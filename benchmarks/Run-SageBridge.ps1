param(
    [int]$Repeats = 3,
    [string]$OutputDirectory = '.lake/sage-bridge-benchmarks'
)

$ErrorActionPreference = 'Stop'
$projectRoot = Split-Path -Parent $PSScriptRoot
Push-Location $projectRoot
try {
    if ($Repeats -lt 1) { throw 'Repeats must be positive.' }
    New-Item -ItemType Directory -Force -Path $OutputDirectory | Out-Null
    $outputRoot = (Resolve-Path -LiteralPath $OutputDirectory).Path
    $utf8 = New-Object System.Text.UTF8Encoding($false)
    $source = Join-Path $PSScriptRoot 'SageBridge.lean'
    $records = @()
    for ($run = 1; $run -le $Repeats; $run++) {
        $artifact = Join-Path $outputRoot "SageBridge-$run.olean"
        $timer = [Diagnostics.Stopwatch]::StartNew()
        $output = & lake env lean -o $artifact $source 2>&1
        $exitCode = $LASTEXITCODE
        $timer.Stop()
        [IO.File]::WriteAllLines((Join-Path $outputRoot "run-$run.log"), [string[]]$output, $utf8)
        if ($exitCode -ne 0) { throw "Fresh Sage proof failed on run $run. See its log." }
        $artifactFiles = @(Get-ChildItem -LiteralPath $outputRoot -Filter "SageBridge-$run.olean*")
        $record = [ordered]@{
            run = $run
            wallSeconds = [Math]::Round($timer.Elapsed.TotalSeconds, 3)
            oleanBytes = (Get-Item -LiteralPath $artifact).Length
            allOleanPartsBytes = ($artifactFiles | Measure-Object Length -Sum).Sum
        }
        $records += $record
        Write-Output ($record | ConvertTo-Json -Compress)
    }
    $times = @($records | ForEach-Object { $_.wallSeconds } | Sort-Object)
    $median = if ($times.Count % 2 -eq 1) { $times[[int][Math]::Floor($times.Count / 2)] }
        else { ($times[$times.Count / 2 - 1] + $times[$times.Count / 2]) / 2 }
    $result = [ordered]@{
        dimension = 2
        matrix = @(@('2', '1'), @('2', '2'))
        preferredPrimes = @('2', '3', '5')
        attemptedPrimes = @('2', '3')
        proofMode = 'strict kernel'
        includes = 'Lake/Lean startup, imports, extraction, serialization, producer startup, Sage import and retry/inversion, parsing, proof construction, kernel checking, axiom audit, olean writing'
        excludes = 'dependency build, WSL cold startup, peak memory and internal phase profiling'
        medianSeconds = $median
        worstSeconds = $times[-1]
        records = $records
    }
    [IO.File]::WriteAllText((Join-Path $outputRoot 'results.json'),
        ($result | ConvertTo-Json -Depth 8), $utf8)
}
finally { Pop-Location }
