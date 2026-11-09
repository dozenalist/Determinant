param(
    [int[]]$Dimensions = @(10, 50, 100, 128, 200),
    [int]$Repeats = 3,
    [int]$EntryBits = 20,
    [string]$OutputDirectory = '.lake/triangular-benchmarks'
)

$ErrorActionPreference = 'Stop'
$projectRoot = Split-Path -Parent $PSScriptRoot
Push-Location $projectRoot
try {
    if ($Repeats -lt 1 -or $EntryBits -lt 2 -or $EntryBits -gt 4096) {
        throw 'Repeats must be positive; EntryBits must be between 2 and 4096.'
    }
    New-Item -ItemType Directory -Force -Path $OutputDirectory | Out-Null
    $outputRoot = (Resolve-Path -LiteralPath $OutputDirectory).Path
    $records = @()
    $utf8 = New-Object System.Text.UTF8Encoding($false)
    $magnitude = [System.Numerics.BigInteger]::Pow(2, $EntryBits - 1)
    $offsetRange = if ($magnitude -lt 997) { [int]$magnitude } else { 997 }
    foreach ($dimension in $Dimensions) {
        if ($dimension -lt 1) { throw 'Benchmark dimensions must be positive.' }
        $source = Join-Path $outputRoot "Triangular$dimension.lean"
        $artifact = Join-Path $outputRoot "Triangular$dimension.olean"
        $builder = New-Object System.Text.StringBuilder
        [void]$builder.AppendLine('import Determinant')
        [void]$builder.AppendLine('set_option maxRecDepth 100000')
        [void]$builder.AppendLine('set_option maxHeartbeats 0')
        [void]$builder.AppendLine("def benchmarkMatrix : Matrix (Fin $dimension) (Fin $dimension) Int := !![")
        for ($i = 0; $i -lt $dimension; $i++) {
            $row = for ($j = 0; $j -lt $dimension; $j++) {
                if ($j -lt $i) { '0' }
                else {
                    # Deterministic signed entries with exactly EntryBits magnitude bits.
                    $value = $magnitude + (($i * 131 + $j * 17 + 1) % $offsetRange)
                    if (($i + $j) % 2 -eq 1 -or ($i -eq $j -and $i % 2 -eq 1)) {
                        $value = -$value
                    }
                    $value.ToString([Globalization.CultureInfo]::InvariantCulture)
                }
            }
            [void]$builder.Append(($row -join ', '))
            if ($i + 1 -lt $dimension) { [void]$builder.AppendLine(';') }
            else { [void]$builder.AppendLine(']') }
        }
        [void]$builder.AppendLine('theorem benchmark : Ne benchmarkMatrix.det 0 := by')
        [void]$builder.AppendLine('  certify_det_ne_zero_triangular')
        [void]$builder.AppendLine('#print axioms benchmark')
        [IO.File]::WriteAllText($source, $builder.ToString(), $utf8)
        for ($run = 1; $run -le $Repeats; $run++) {
            $timer = [Diagnostics.Stopwatch]::StartNew()
            # Invokes Lean on source every time, including elaboration, kernel checking,
            # and writing a fresh olean. No up-to-date theorem artifact can skip work.
            $diagnostics = & lake env lean -o $artifact $source 2>&1
            $exitCode = $LASTEXITCODE
            $timer.Stop()
            $log = ($diagnostics | Out-String)
            [IO.File]::WriteAllText((Join-Path $outputRoot "Triangular$dimension-run$run.log"),
                $log, $utf8)
            if ($exitCode -ne 0) { throw "Dimension $dimension failed:`n$log" }
            if ($log -match 'sorryAx|ofReduceBool|native_decide|nativeEq|_native') {
                throw "Unexpected axiom in dimension ${dimension}:`n$log"
            }
            $record = [pscustomobject]@{
                Dimension = $dimension
                EntryBits = $EntryBits
                Run = $run
                Seconds = [Math]::Round($timer.Elapsed.TotalSeconds, 3)
                SourceBytes = (Get-Item -LiteralPath $source).Length
                OLeanBytes = (Get-Item -LiteralPath $artifact).Length
                Axioms = $log.Trim()
            }
            $records += $record
            $records | ConvertTo-Json -Depth 4 |
                Set-Content -LiteralPath (Join-Path $outputRoot 'results.json') -Encoding UTF8
            Write-Host ("n={0}, bits={1}, run={2}: {3}s, olean={4} bytes" -f
                $dimension, $EntryBits, $run, $record.Seconds, $record.OLeanBytes)
        }
    }
    $records | Format-Table Dimension, EntryBits, Run, Seconds, SourceBytes, OLeanBytes
}
finally {
    Pop-Location
}
