del fstar-exos\OK.txt
docker run -it -v %CD%\fstar-exos:/fstar-exos fstarlang/fstar-emacs /fstar-exos/fstar-docker.sh
IF EXIST fstar-exos\OK.txt (
	echo SUCCESS
	exit /b 0
) ELSE (
	echo FAILURE
	exit /b 1
)

