#!/bin/bash
if test "$1" == "--no-colour"; then
  runhaskell -cpp -DNOCOLOR -i./tests/driver ./tests/driver/Check.hs $2 $3 $4 $5 $6
else
  runhaskell -cpp -i./tests/driver ./tests/driver/Check.hs $1 $2 $3 $4 $5 $6
fi
