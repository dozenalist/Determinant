param(
    [string]$InputDirectory = '.lake/dense-benchmarks',
    [string]$OutputDirectory = '.lake/dense-results',
    [string[]]$Names = @('*'),
    [int]$Repeats = 3,
    [int]$DeadlineSeconds = 600
)

$ErrorActionPreference = 'Stop'
$projectRoot = Split-Path -Parent $PSScriptRoot
Push-Location $projectRoot
try {
    if ($Repeats -lt 1 -or $DeadlineSeconds -lt 1) { throw 'Budgets must be positive.' }
    $manifest = Get-Content -Raw -Encoding UTF8 (Join-Path $InputDirectory 'manifest.json') | ConvertFrom-Json
    New-Item -ItemType Directory -Force -Path $OutputDirectory | Out-Null
    $outputRoot = (Resolve-Path -LiteralPath $OutputDirectory).Path
    $utf8 = New-Object System.Text.UTF8Encoding($false)
    $records = @()
    foreach ($case in $manifest.cases) {
        if (-not @($Names | Where-Object { $case.name -like $_ }).Count) { continue }
        $source = (Resolve-Path -LiteralPath (Join-Path $InputDirectory ($case.name + '.lean'))).Path
        for ($run = 1; $run -le $Repeats; $run++) {
            $stem = Join-Path $outputRoot ($case.name + "-run$run")
            $artifact = $stem + '.olean'
            $startTime = Get-Date
            $timer = [Diagnostics.Stopwatch]::StartNew()
            $argumentText = 'env lean -o "{0}" "{1}"' -f $artifact, $source
            $process = Start-Process -FilePath (Get-Command lake).Source -ArgumentList $argumentText `
                -PassThru -WindowStyle Hidden -RedirectStandardOutput ($stem + '.stdout.log') `
                -RedirectStandardError ($stem + '.stderr.log')
            # Materialize the process handle before polling. Otherwise .NET can lose
            # the exit code after the short-lived elan launcher has already exited.
            $null = $process.Handle
            $peaks = @{}
            $peakCombined = 0L
            $timedOut = $false
            while (-not $process.WaitForExit(100)) {
                # Include all fresh Lake/Lean descendants. Runs are sequential; older editor
                # servers are excluded. Windows reports the lifetime peak for each PID.
                $combined = 0L
                foreach ($child in (Get-Process lean,lake -ErrorAction SilentlyContinue)) {
                    try {
                        if ($child.StartTime -ge $startTime) {
                            $peaks[$child.Id] = [long]$child.PeakWorkingSet64
                            $combined += $child.WorkingSet64
                        }
                    } catch { }
                }
                $peakCombined = [Math]::Max($peakCombined, $combined)
                if ($timer.Elapsed.TotalSeconds -ge $DeadlineSeconds) {
                    & taskkill.exe /PID $process.Id /T /F | Out-Null
                    $timedOut = $true
                    break
                }
            }
            $process.WaitForExit()
            $timer.Stop()
            $log = [IO.File]::ReadAllText($stem + '.stdout.log') + "`n" +
                [IO.File]::ReadAllText($stem + '.stderr.log')
            [IO.File]::WriteAllText($stem + '.log', $log, $utf8)
            $phases = [ordered]@{}
            foreach ($match in [regex]::Matches($log, '\[Determinant.timing\] ([^:\r\n]+): (\d+) ms')) {
                $phases[$match.Groups[1].Value] = [long]$match.Groups[2].Value
            }
            $proofNodes = if ($log -match 'proof nodes: (\d+)') { [long]$Matches[1] } else { $null }
            $metadata = if ($log -match 'metadata: (\{[^\r\n]+\})') {
                $Matches[1] | ConvertFrom-Json
            } else { $null }
            $kernelMs = $null
            $kernelMatch = [regex]::Match($log, '(?m)^\s*type checking ([0-9.]+)(ms|s)\s*$')
            if ($kernelMatch.Success) {
                $kernelMs = [double]::Parse($kernelMatch.Groups[1].Value,
                    [Globalization.CultureInfo]::InvariantCulture)
                if ($kernelMatch.Groups[2].Value -eq 's') { $kernelMs *= 1000 }
            }
            $finalKernelMs = $null
            $individualKernel = [regex]::Matches($log, '(?m)^type checking took ([0-9.]+)(ms|s)\s*$')
            if ($individualKernel.Count) {
                $lastKernel = $individualKernel[$individualKernel.Count - 1]
                $finalKernelMs = [double]::Parse($lastKernel.Groups[1].Value,
                    [Globalization.CultureInfo]::InvariantCulture)
                if ($lastKernel.Groups[2].Value -eq 's') { $finalKernelMs *= 1000 }
            }
            $record = [ordered]@{
                case = $case
                run = $run
                wallSeconds = [Math]::Round($timer.Elapsed.TotalSeconds, 3)
                exitCode = $process.ExitCode
                timedOut = $timedOut
                peakLeanProcessBytes = ($peaks.Values | Measure-Object -Maximum).Maximum
                peakCombinedLeanSampleBytes = $peakCombined
                oleanBytes = if (Test-Path -LiteralPath $artifact) { (Get-Item -LiteralPath $artifact).Length } else { 0 }
                allOleanPartsBytes = (Get-ChildItem -LiteralPath $outputRoot -Filter ($case.name + "-run$run.olean*") | Measure-Object Length -Sum).Sum
                proofNodes = $proofNodes
                sourceBytes = (Get-Item -LiteralPath $source).Length
                axiomReport = if ($log -match "'benchmark' depends on axioms: ([^\r\n]+)") { $Matches[1] } else { $null }
                kernelMs = $kernelMs
                finalDeclarationKernelMs = $finalKernelMs
                phasesMs = $phases
                producer = $metadata
                log = [IO.Path]::GetFileName($stem + '.log')
            }
            $records += $record
            [IO.File]::WriteAllText((Join-Path $outputRoot 'results.json'),
                (ConvertTo-Json -InputObject @($records) -Depth 12), $utf8)
            Write-Output ("{0}, run {1}: {2}s, exit={3}, peak={4:N0} MiB" -f
                $case.name, $run, $record.wallSeconds, $record.exitCode,
                ($record.peakLeanProcessBytes / 1MB))
            if ($record.exitCode -ne 0 -or $timedOut) { throw "Benchmark failed; see $stem.log" }
        }
    }
}
finally { Pop-Location }
