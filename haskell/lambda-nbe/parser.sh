#!/bin/bash
rm -rf src/Language/Lambda/Syntax/
bnfc --haskell -d -p Language.Lambda --functor --generic -o src grammar/Lambda/Syntax.cf && \
alex src/Language/Lambda/Syntax/Lex.x && \
happy src/Language/Lambda/Syntax/Par.y && \
stack clean && \
stack build
