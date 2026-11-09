# Windows PowerShell adapter for Lean 4.35's always-quoted process arguments.
# WSL parses its option prefix from the raw command line, so invoke its fixed
# options through PowerShell's native argument handling. No command is evaluated.
param(
    [string]$Distribution = 'SageMath-10.10',
    [string]$Python = '/usr/bin/python3',
    [string]$Script = 'scripts/det_certificate.py'
)

$ErrorActionPreference = 'Continue'
$ProgressPreference = 'SilentlyContinue'
$OutputEncoding = New-Object System.Text.UTF8Encoding($false)
[Console]::OutputEncoding = $OutputEncoding
$request = [Console]::In.ReadToEnd()
$request | & "$env:SystemRoot\System32\wsl.exe" --distribution $Distribution --exec $Python $Script
exit $LASTEXITCODE
