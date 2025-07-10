Write-Host "Testing ToyC compiler..."
Write-Host ""

Write-Host "Test 1: Simple main function"
"int main() { return 42; }" | & "./_build/default/bin/main.exe"
Write-Host ""

Write-Host "Test 2: Function with parameter"
"int test(int x) { return x; } int main() { return test(5); }" | & "./_build/default/bin/main.exe"
Write-Host ""

Write-Host "All tests completed."