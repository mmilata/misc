#!/bin/bash

MEMORY=2000
DEPTH=2000000

if [ $# -lt 1 ]; then
	echo "usage: $0 <ltl_file>"
	exit 1
fi

LTLFILE=$1
BASENAME=`echo $LTLFILE | sed 's/^\([^.]*\)\..*/\1/'`
PROMELAFILE="${BASENAME}.pml"

shift 1

set -x
spin -a -F $LTLFILE $@ $PROMELAFILE || exit 1
cc -DNFAIR=8 -DMEMLIM=$MEMORY -o pan pan.c || exit 1
./pan -a -f -I -m$DEPTH
