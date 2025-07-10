@echo off
echo Testing ToyC compiler...
echo.
echo Test 1: Simple main function
echo int main() { return 42; } | ./_build/default/bin/main.exe
echo.
echo Test 2: Function with parameter
echo int test(int x) { return x; } int main() { return test(5); } | ./_build/default/bin/main.exe
echo.
echo All tests completed.
pause