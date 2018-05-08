del /s /q build-win64
rmdir /s /q build-win64
mkdir build-win64
cd build-win64
cmake .. -G "Visual Studio 14 2015 Win64" 
if %errorlevel% neq 0 goto :ERROR
msbuild /m /target:Clean Project.sln
if %errorlevel% neq 0 goto :ERROR
msbuild /m /target:Build Project.sln
if %errorlevel% neq 0 goto :ERROR
REM .\core-tests\Debug\****.exe
REM if %errorlevel% neq 0 goto :ERROR

cd ..
exit /b 0
:ERROR
exit /b %errorlevel%

