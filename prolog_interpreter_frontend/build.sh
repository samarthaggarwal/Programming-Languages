#!/bin/sh
ocamllex ProgLexer.mll && \
ocamllex QueryLexer.mll && \
ocamlyacc ProgParser.mly && \
ocamlyacc QueryParser.mly && \
ocamlc -c Ast.ml && \
ocamlc -c ProgParser.mli && \
ocamlc -c QueryParser.mli && \
ocamlc -c ProgParser.ml && \
ocamlc -c QueryParser.ml && \
ocamlc -c ProgLexer.ml && \
ocamlc -c QueryLexer.ml && \
ocamlc -c Main.ml && \
ocamlmktop -o top Ast.cmo ProgParser.cmo QueryParser.cmo ProgLexer.cmo QueryLexer.cmo Main.cmo