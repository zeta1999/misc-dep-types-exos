#!/bin/bash
rm tis.ok
pushd tools/tis-interpreter/;./tis-interpreter.sh --cc "-DTIS=1" -main main ../../core-tis-test/main.c > ../../log.txt || exit 1; popd
cat log.txt
if grep -q error log.txt; then
	echo TIS ERROR
	exit 1
fi
echo > tis.ok


