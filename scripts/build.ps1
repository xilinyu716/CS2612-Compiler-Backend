param(
  [switch]$Clean
)

function Exec($cmd) {
  Write-Host "==> $cmd"
  iex $cmd
  if ($LASTEXITCODE -ne 0) { throw "Command failed: $cmd" }
}

function PathExists($p) { Test-Path -Path $p }

if ($Clean) {
  if (Test-Path build) { Remove-Item -Recurse -Force build }
  if (Test-Path run_tests.exe) { Remove-Item -Force run_tests.exe }
  if (Test-Path demo.exe) { Remove-Item -Force demo.exe }
}

$cmake = Get-Command cmake -ErrorAction SilentlyContinue
if ($cmake) {
  Exec "cmake -S . -B build -DCMAKE_BUILD_TYPE=Release"
  Exec "cmake --build build --config Release"
  $testCandidates = @("build\\run_tests.exe", "build\\Release\\run_tests.exe")
  $demoCandidates = @("build\\demo.exe", "build\\Release\\demo.exe")
  $testExe = $null; foreach ($p in $testCandidates) { if (PathExists $p) { $testExe = $p; break } }
  $demoExe = $null; foreach ($p in $demoCandidates) { if (PathExists $p) { $demoExe = $p; break } }
  if ($testExe) { Exec $testExe } else { Write-Warning "run_tests.exe not found" }
  if ($demoExe) { Exec $demoExe } else { Write-Warning "demo.exe not found" }
  exit 0
}

Write-Host "CMake not found, trying direct compiler invocation"

$gpp = Get-Command g++ -ErrorAction SilentlyContinue
$clangpp = Get-Command clang++ -ErrorAction SilentlyContinue
$cl = Get-Command cl -ErrorAction SilentlyContinue

if ($gpp) {
  Exec "g++ -std=c++17 -O2 tests/test_all.cpp -o run_tests"
  Exec "g++ -std=c++17 -O2 -DBACKEND_MAIN project1.cpp -o demo"
  Exec "./run_tests.exe"
  Exec "./demo.exe"
  exit 0
}
elseif ($clangpp) {
  Exec "clang++ -std=c++17 -O2 tests/test_all.cpp -o run_tests"
  Exec "clang++ -std=c++17 -O2 -DBACKEND_MAIN project1.cpp -o demo"
  Exec "./run_tests.exe"
  Exec "./demo.exe"
  exit 0
}
elseif ($cl) {
  # Visual C++ (requires Developer Command Prompt environment)
  Exec "cl /EHsc tests\\test_all.cpp /Fe:run_tests.exe"
  Exec "cl /EHsc /DBACKEND_MAIN project1.cpp /Fe:demo.exe"
  Exec "./run_tests.exe"
  Exec "./demo.exe"
  exit 0
}
else {
  Write-Error "No C++ compiler found. Please install MSVC (cl), g++, clang++, or CMake."
  exit 1
}

