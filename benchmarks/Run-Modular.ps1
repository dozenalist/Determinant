param(
    [int[]]$Dimensions = @(2, 10, 20),
    [int]$Repeats = 3,
    [ValidateSet('arithmetic', 'kernel', 'upper')]
    [string[]]$Routes = @('arithmetic', 'kernel', 'upper'),
    [string]$OutputDirectory = '.lake/modular-benchmarks'
)

$ErrorActionPreference = 'Stop'
$projectRoot = Split-Path -Parent $PSScriptRoot
Push-Location $projectRoot
try {
    if ($Repeats -lt 1) { throw 'Repeats must be positive.' }
    New-Item -ItemType Directory -Force -Path $OutputDirectory | Out-Null
    $outputRoot = (Resolve-Path -LiteralPath $OutputDirectory).Path
    $utf8 = New-Object System.Text.UTF8Encoding($false)
    $records = @()
    # A = I + J, B = I - (n+1)^(-1) J over ZMod 101.
    # ModPow discovers data only. Lean checks every product; no inversion algorithm is added.
    foreach ($dimension in $Dimensions) {
        if ($dimension -lt 1 -or $dimension -ge 100) {
            throw 'This small-checker comparison supports dimensions 1 through 99.'
        }
        $inverse = [int][System.Numerics.BigInteger]::ModPow($dimension + 1, 99, 101)
        $matrixRows = @()
        $inverseRows = @()
        for ($i = 0; $i -lt $dimension; $i++) {
            $matrixRow = @()
            $inverseRow = @()
            for ($j = 0; $j -lt $dimension; $j++) {
                $diagonal = if ($i -eq $j) { 1 } else { 0 }
                $matrixRow += ($diagonal + 1).ToString()
                $inverseRow += ((101 + $diagonal - $inverse) % 101).ToString()
            }
            $matrixRows += ($matrixRow -join ', ')
            $inverseRows += ('[' + ($inverseRow -join ', ') + ']')
        }
        foreach ($route in $Routes) {
            $kind = if ($route -eq 'upper') { 'unit-upper-product' } else { 'full-inverse' }
            $tactic = if ($route -eq 'kernel') {
                'certify_det_ne_zero_modular_kernel'
            } elseif ($route -eq 'arithmetic') {
                'certify_det_ne_zero_modular_arithmetic'
            } else { 'certify_det_ne_zero_modular' }
            $source = Join-Path $outputRoot "Modular-$route-$dimension.lean"
            $artifact = Join-Path $outputRoot "Modular-$route-$dimension.olean"
            $builder = New-Object System.Text.StringBuilder
            [void]$builder.AppendLine('import Determinant')
            [void]$builder.AppendLine('import Lean.Util.NumObjs')
            [void]$builder.AppendLine('set_option maxRecDepth 100000')
            [void]$builder.AppendLine('set_option maxHeartbeats 0')
            [void]$builder.AppendLine("def benchmarkMatrix : Matrix (Fin $dimension) (Fin $dimension) Int := !![")
            [void]$builder.AppendLine(($matrixRows -join ";`n") + ']')
            [void]$builder.AppendLine('def certificate : Determinant.RawCertificate := {')
            [void]$builder.AppendLine("  dimension := $dimension, modulus := 101, kind := ""$kind"",")
            [void]$builder.AppendLine('  inverse := [' + ($inverseRows -join ', ') + '] }')
            [void]$builder.AppendLine('theorem benchmark : Ne benchmarkMatrix.det 0 := by')
            [void]$builder.AppendLine("  $tactic certificate")
            [void]$builder.AppendLine('#print axioms benchmark')
            [void]$builder.AppendLine('run_cmd do')
            [void]$builder.AppendLine('  for dependency in ' + [char]0x2190 + ' Lean.collectAxioms ``benchmark do')
            [void]$builder.AppendLine('    unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do')
            [void]$builder.AppendLine('      throwError "unexpected axiom {dependency}"')
            [void]$builder.AppendLine('  let some (.thmInfo info) := (' + [char]0x2190 + ' Lean.getEnv).find? ``benchmark')
            [void]$builder.AppendLine('    | throwError "missing benchmark theorem"')
            [void]$builder.AppendLine('  let nodes ' + [char]0x2190 + ' Lean.Expr.numObjs info.value')
            [void]$builder.AppendLine('  Lean.logInfo m!"proof nodes: {nodes}"')
            [IO.File]::WriteAllText($source, $builder.ToString(), $utf8)
            for ($run = 1; $run -le $Repeats; $run++) {
                $timer = [Diagnostics.Stopwatch]::StartNew()
                $diagnostics = & lake env lean -o $artifact $source 2>&1
                $exitCode = $LASTEXITCODE
                $timer.Stop()
                $log = ($diagnostics | Out-String)
                [IO.File]::WriteAllText((Join-Path $outputRoot "Modular-$route-$dimension-run$run.log"),
                    $log, $utf8)
                if ($exitCode -ne 0) { throw "Route $route, dimension $dimension failed:`n$log" }
                if ($log -notmatch 'proof nodes: (\d+)') { throw "Missing proof size in $source" }
                $proofNodes = [long]$Matches[1]
                $record = [pscustomobject]@{
                    Dimension = $dimension
                    Modulus = 101
                    Matrix = 'I + J (2-bit positive entries)'
                    Route = $route
                    Run = $run
                    Seconds = [Math]::Round($timer.Elapsed.TotalSeconds, 3)
                    SourceBytes = (Get-Item -LiteralPath $source).Length
                    OLeanBytes = (Get-Item -LiteralPath $artifact).Length
                    ProofNodes = $proofNodes
                    Axioms = $log.Trim()
                }
                $records += $record
                $records | ConvertTo-Json -Depth 4 |
                    Set-Content -LiteralPath (Join-Path $outputRoot 'results.json') -Encoding UTF8
                Write-Host ("route={0}, n={1}, run={2}: {3}s, olean={4} bytes" -f
                    $route, $dimension, $run, $record.Seconds, $record.OLeanBytes)
            }
        }
    }
    $records | Format-Table Route, Dimension, Run, Seconds, SourceBytes, OLeanBytes
}
finally {
    Pop-Location
}
