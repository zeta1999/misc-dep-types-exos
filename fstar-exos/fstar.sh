#!/bin/bash
# docker run -it -v c:/Users/esoteric/Documents/ ... _model:/ ... _model fstarlang/fstar-emacs
# optional remove : *.checked.* *.hints
rm -Rvf ml/
rm -v OK.txt
rm -v *.checked.* *.hints *.checked
# --use_hints --record_hints --cache_checked_modules
# --use_hints --record_hints
if fstar.exe --verify_module RBMap rbmap.fst; then echo "success"; else echo "failure"; exit 1; fi
if fstar.exe --verify_module Run run.fst; then echo "success"; else echo "failure"; exit 1; fi

if fstar.exe --codegen OCaml --odir ml run.fst; then echo "success"; else echo "failure"; exit 1; fi

cd ml

if ocamlopt -o Run -I ~/.opam/4.04.2/lib/zarith/ ~/.opam/4.04.2/lib/zarith/zarith.cmxa -I ~/FStar/bin/fstarlib/ ~/FStar/bin/fstarlib/fstarlib.cmxa RBMap.ml Run.ml; then echo "success"; else echo "failure"; exit 1; fi

./Run > run.log
if grep -xq "OK" "run.log"; then echo "run/ok"; else echo "run/failure"; exit 1; fi

cd ..
echo > OK.txt
