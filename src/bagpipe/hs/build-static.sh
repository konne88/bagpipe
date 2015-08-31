#!/usr/bin/env bash

export LIBRARY_PATH="$HOME/local/lib"

cabal build --ghc-options="-O2 --make -static -optc-static -optl-static -optl-pthread" bagpipe
