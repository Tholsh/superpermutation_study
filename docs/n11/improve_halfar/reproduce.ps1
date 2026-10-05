# SPDX-License-Identifier: GPL-3.0-or-later
# Copyright (C) 2026 Theo H.

param(
    [string]$Compiler = 'C:\msys64\ucrt64\bin\g++.exe',
    [string]$Python = 'C:\msys64\ucrt64\bin\python.exe'
)

$ErrorActionPreference = 'Stop'
$repoRoot = (Resolve-Path (Join-Path $PSScriptRoot '../../..')).Path
$runId = 'reproduction-' + [guid]::NewGuid().ToString('N')
$reportDir = Join-Path $PSScriptRoot $runId
$workDir = Join-Path ([System.IO.Path]::GetTempPath()) ('course-exchange-' + $runId)
$outputDir = Join-Path $workDir 'output'
$binaryPath = Join-Path $workDir 'course_exchange.exe'
$inputPath = Join-Path $workDir 'halfar-input.txt'
$archivePath = Join-Path $repoRoot 'words/11/superpermutation-11-43930628.txt.xz'
$rowsPath = Join-Path $workDir 'rows.txt'
$rowsArchive = Join-Path $repoRoot 'data/n11/rows.txt.xz'
$circlesPath = Join-Path $repoRoot 'data/n11/circles.txt'
$constructPath = Join-Path $repoRoot 'boundary-spectral-n11-20261004/construct.cpp'
$literalChecker = Join-Path $workDir 'literal_check.exe'
$inversionChecker = Join-Path $workDir 'verify_standalone.exe'
$sortedChecker = Join-Path $workDir 'verify_sorted.exe'
$checkerSources = @(
    (Join-Path $repoRoot 'tools/verification/literal_check.cpp'),
    (Join-Path $repoRoot 'tools/verification/verify_standalone.cpp'),
    (Join-Path $repoRoot 'tools/verification/verify_sorted.cpp')
)

foreach ($required in (@($Compiler, $Python, $archivePath, $rowsArchive, $circlesPath, $constructPath) + $checkerSources)) {
    if (-not (Test-Path -LiteralPath $required)) { throw "Missing required path: $required" }
}

# The historical dependency manifest is preserved; this one pins the local layout.
$dependencies = Get-Content -LiteralPath (Join-Path $PSScriptRoot 'local-dependencies.json') -Raw | ConvertFrom-Json
$usedFiles = @(
    (Join-Path $repoRoot 'search/course_exchange.cpp'),
    (Join-Path $repoRoot 'boundary-spectral-n11-20261004/coupled_cycle_search.cpp'),
    (Join-Path $repoRoot 'boundary-spectral-n11-20261004/phase_cut_spectral.cpp'),
    (Join-Path $repoRoot 'boundary-spectral-n11-20261004/boundary_spectral.cpp'),
    $constructPath, $rowsArchive, $circlesPath
)
foreach ($dependency in $dependencies) {
    $dependencyPath = Join-Path $repoRoot $dependency.Path
    if ((Get-FileHash -Algorithm SHA256 -LiteralPath $dependencyPath).Hash -ne $dependency.Hash) {
        throw "Pinned dependency hash mismatch: $dependencyPath"
    }
}

New-Item -ItemType Directory -Path $reportDir, $workDir | Out-Null
$savedPath = $env:PATH
$started = Get-Date
try {
    $env:PATH = (Split-Path $Compiler -Parent) + ';' + $env:PATH
    @($usedFiles + $checkerSources + @($Compiler, $Python) |
        ForEach-Object { Get-FileHash -Algorithm SHA256 -LiteralPath $_ } |
        Select-Object Path, Hash) | ConvertTo-Json -Depth 3 |
        Set-Content -LiteralPath (Join-Path $reportDir 'inputs-and-tools.json') -Encoding UTF8

    & $Compiler -O3 -std=c++17 $usedFiles[0] -o $binaryPath
    if ($LASTEXITCODE -ne 0) { throw 'C++ build failed' }
    $checkerBinaries = @($literalChecker, $inversionChecker, $sortedChecker)
    for ($checkerIndex = 0; $checkerIndex -lt $checkerSources.Count; ++$checkerIndex) {
        & $Compiler -O3 -std=c++17 $checkerSources[$checkerIndex] -o $checkerBinaries[$checkerIndex]
        if ($LASTEXITCODE -ne 0) { throw "Checker build failed: $($checkerSources[$checkerIndex])" }
    }

    @'
import lzma, pathlib, sys
for archive, target in ((sys.argv[1], sys.argv[2]), (sys.argv[3], sys.argv[4])):
    with lzma.open(archive, 'rb') as source:
        pathlib.Path(target).write_bytes(source.read())
'@ | & $Python - $archivePath $inputPath $rowsArchive $rowsPath
    if ($LASTEXITCODE -ne 0) { throw 'Input extraction failed' }
    if ((Get-FileHash -Algorithm SHA256 -LiteralPath $rowsPath).Hash -ne '99F7F9AAC8F970126A1EB7668CBC5D0E5B6D9F362611F1258C44305EB2A3A015') {
        throw 'Pinned rows hash mismatch'
    }
    $inputHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $inputPath).Hash
    if ($inputHash -ne '784C892B81283ECE13F5B1EF8C49D13B0BCB4D3C1EC49882E5593F034E86B596') {
        throw 'Halfar input hash mismatch'
    }

    & $binaryPath $rowsPath $circlesPath $inputPath $outputDir 2 900 --global-all-phases |
        Tee-Object -FilePath (Join-Path $reportDir 'optimization.log')
    if ($LASTEXITCODE -ne 0) { throw 'Course optimization failed' }
    $candidatePath = Join-Path $outputDir 'global-phase-n11-43930624.txt'
    if (-not (Test-Path -LiteralPath $candidatePath)) { throw 'Expected candidate was not produced' }

    & $literalChecker 11 0123456789A $candidatePath |
        Tee-Object -FilePath (Join-Path $reportDir 'independent-literal.json')
    if ($LASTEXITCODE -ne 0) { throw 'Literal coverage verification failed' }
    & $inversionChecker 11 0123456789A $candidatePath 43930624 |
        Tee-Object -FilePath (Join-Path $reportDir 'independent-inversion.json')
    if ($LASTEXITCODE -ne 0) { throw 'Inversion coverage verification failed' }
    & $sortedChecker 11 0123456789A $candidatePath 43930624 (Join-Path $reportDir 'independent-sorted.json')
    if ($LASTEXITCODE -ne 0) { throw 'Sorted coverage verification failed' }

    $candidateHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $candidatePath).Hash
    if ($candidateHash -ne '0F3B2DCF607AAF3E7985C9DAF2D87C07F8947522490DFEA90B05A90C7FD5AA6B') {
        throw 'Reproduction output hash mismatch'
    }
    foreach ($report in Get-ChildItem -LiteralPath $outputDir -File) {
        if ($report.Extension -in '.json', '.jsonl') {
            Copy-Item -LiteralPath $report.FullName -Destination $reportDir
        }
    }
    [pscustomobject]@{
        success = $true
        started_local = $started.ToString('o')
        completed_local = (Get-Date).ToString('o')
        total_seconds = ((Get-Date) - $started).TotalSeconds
        working_directory = $workDir
        candidate_path = $candidatePath
        input_sha256 = $inputHash.ToLowerInvariant()
        output_sha256 = $candidateHash.ToLowerInvariant()
        output_bytes = (Get-Item -LiteralPath $candidatePath).Length
        mode = '--global-all-phases'
    } | ConvertTo-Json | Set-Content -LiteralPath (Join-Path $reportDir 'run-summary.json') -Encoding UTF8
    Write-Output "Reproduced successfully. Reports: $reportDir"
    Write-Output "Temporary binary and word files: $workDir"
} finally {
    $env:PATH = $savedPath
}
