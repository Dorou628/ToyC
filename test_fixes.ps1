# Test script for the three reported issues

Write-Host "Testing 01_minimal.tc..."
echo 'int main() { return 0; }' | ./_build/default/bin/main.exe
if ($LASTEXITCODE -eq 0) {
    Write-Host "01_minimal.tc: PASSED" -ForegroundColor Green
} else {
    Write-Host "01_minimal.tc: FAILED" -ForegroundColor Red
}

Write-Host "`nTesting 16_complex_syntax.tc..."
Get-Content 16_complex_syntax.tc | ./_build/default/bin/main.exe
if ($LASTEXITCODE -eq 0) {
    Write-Host "16_complex_syntax.tc: PASSED" -ForegroundColor Green
} else {
    Write-Host "16_complex_syntax.tc: FAILED" -ForegroundColor Red
}

Write-Host "`nTesting 18_many_variables.tc..."
Get-Content 18_many_variables.tc | ./_build/default/bin/main.exe
if ($LASTEXITCODE -eq 0) {
    Write-Host "18_many_variables.tc: PASSED" -ForegroundColor Green
} else {
    Write-Host "18_many_variables.tc: FAILED" -ForegroundColor Red
}

Write-Host "`nAll tests completed."