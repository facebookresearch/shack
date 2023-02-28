all: build

build: 
	dune build codegen.exe

test: build
	./_build/default/codegen.exe --file test.lang

format:
	for i in *.ml; do ocamlformat --enable-outside-detected-project -i $$i; done

.PHONY: all format test build

# To regenerate the test file
#./_build/default/codegen.exe  --file test.lang  --output ../theories/generated_example.v
