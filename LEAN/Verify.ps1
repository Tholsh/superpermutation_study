#requires -Version 7.0
param(
    [Parameter(Mandatory=$true)][string]$DependencyProject,
    [string]$Lean = 'lean',
    [string]$OutputDirectory = 'build-local',
    [int]$MemoryMB = 6144
)
$ErrorActionPreference = 'Stop'
$taskRoot = $PSScriptRoot
$taskDeps = (Resolve-Path -LiteralPath $DependencyProject).Path
$taskOut = [IO.Path]::GetFullPath((Join-Path $taskRoot $OutputDirectory))
if (Test-Path -LiteralPath $taskOut) { throw 'Use a fresh output directory.' }
$taskLib = Join-Path $taskOut 'lib'
New-Item -ItemType Directory -Path $taskLib -Force | Out-Null
$taskOldPath = $env:LEAN_PATH
$taskPaths = @($taskLib)
# Only third-party dependency objects are borrowed. No Coeff2 or Pantone
# objects from another project are put on the search path.
foreach ($taskPkg in Get-ChildItem -LiteralPath (Join-Path $taskDeps '.lake/packages') -Directory) {
    $taskCandidate = Join-Path $taskPkg.FullName '.lake/build/lib/lean'
    if (Test-Path -LiteralPath $taskCandidate) { $taskPaths += $taskCandidate }
}
if ($taskPaths.Count -lt 2) { throw 'No third-party dependency cache found.' }
$taskRecords = [Collections.Generic.List[object]]::new()
Push-Location $taskRoot
try {
    $taskVersion = (& $Lean --version) -join ' '
    if ($LASTEXITCODE -ne 0 -or $taskVersion -notmatch 'version 4\.31\.0\b') {
        throw "Wrong Lean version: $taskVersion"
    }
    $env:LEAN_PATH = $taskPaths -join [IO.Path]::PathSeparator
    $taskModules = @(Get-Content -LiteralPath 'build-order.txt') + @('PublicClaims', 'AxiomAudit')
    foreach ($taskModule in $taskModules) {
        $taskRelative = $taskModule.Replace('.', '/')
        $taskObject = Join-Path $taskLib ($taskRelative + '.olean')
        New-Item -ItemType Directory -Path (Split-Path -Parent $taskObject) -Force | Out-Null
        $taskLog = Join-Path $taskOut ($taskModule + '.log')
        $taskWatch = [Diagnostics.Stopwatch]::StartNew()
        & $Lean -M $MemoryMB -j 1 -o $taskObject ($taskRelative + '.lean') *> $taskLog
        $taskExit = $LASTEXITCODE
        $taskWatch.Stop()
        $taskText = Get-Content -LiteralPath $taskLog -Raw
        $taskRecords.Add([ordered]@{ module=$taskModule; exit_code=$taskExit;
            seconds=$taskWatch.Elapsed.TotalSeconds; log=[IO.Path]::GetFileName($taskLog) })
        $taskRecords | ConvertTo-Json -Depth 4 | Set-Content -LiteralPath (Join-Path $taskOut 'progress.json')
        if ($taskExit -ne 0 -or $taskText -match '(^|\n)[^\n]*error[(:]') {
            throw "Lean rejected $taskModule; see $taskLog"
        }
        Write-Output "PASS $taskModule ($([Math]::Round($taskWatch.Elapsed.TotalSeconds,2)) s)"
    }
    $taskAudit = Get-Content -LiteralPath (Join-Path $taskOut 'AxiomAudit.log') -Raw
    if ($taskAudit -notmatch 'AXIOM_AUDIT_PASS') { throw 'Missing axiom audit receipt.' }
    [ordered]@{ status='passed'; lean=$taskVersion; modules=$taskModules.Count;
        borrowed_objects='third-party Mathlib dependencies only';
        all_bundled_sources_recompiled=$true;
        axiom_audit=$taskAudit.Trim(); seconds=($taskRecords.seconds | Measure-Object -Sum).Sum
    } | ConvertTo-Json -Depth 4 | Set-Content -LiteralPath (Join-Path $taskOut 'verification.json')
} finally { Pop-Location; $env:LEAN_PATH = $taskOldPath }
