all: build

build: 
	dune build codegen.exe

test: build
	./_build/default/codegen.exe

format:
	for i in *.ml; do ocamlformat --enable-outside-detected-project -i $$i; done

.PHONY: all format test build
