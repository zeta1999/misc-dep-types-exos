#!/bin/bash
source /fstar-exos/env.sh
cd /home/FStar/FStar/ulib/ml
make
cd /fstar-exos
./fstar.sh
