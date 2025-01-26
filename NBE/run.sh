#!/bin/bash
rm -rf src/Parser/Syntax/
cd src
bnfc --haskell -d -p Parser --functor --generic -o Parser Parser/grammar/Syntax.cf
sleep 3
alex Parser/Parser/Syntax/Lex.x
happy Parser/Parser/Syntax/Par.y
cd ..
mv src/Parser/Parser/Syntax src/Parser/Syntax
rm -rf src/Parser/Parser
cabal clean
cabal build