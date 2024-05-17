.PHONY: build
build:
	dune build

.PHONY: run
run:
	dune exec bin/main.exe

.PHONY: test
test:
	dune runtest
