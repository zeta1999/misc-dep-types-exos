REM "\Program Files (x86)\Microsoft Visual Studio 14.0\VC\vcvarsall.bat" x86_amd64

cmd /c runAndTest.bat
if %errorlevel% neq 0 goto :ERROR

cmd /c runTestFStarDocker.bat
if %errorlevel% neq 0 goto :ERROR

bash -c ./runAndTest.sh
if %errorlevel% neq 0 goto :ERROR

bash -c ./tis.sh
IF EXIST tis.ok (echo SUCCESS) ELSE (echo FAILURE; exit /b 1)
if %errorlevel% neq 0 goto :ERROR

exit /b 0
:ERROR
ECHO FAILURE
exit /b %errorlevel%

echo tests all done

