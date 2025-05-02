hello: amodule.ml bmodule.ml amodule.mli
	ocamlc -c amodule.mli
	ocamlopt -c amodule.ml
	ocamlopt -c bmodule.ml
	ocamlopt -o hello amodule.cmx bmodule.cmx

submod: example.ml use_example.ml
	ocamlopt -c example.ml
	ocamlopt -c use_example.ml
	ocamlopt -o submod example.cmx use_example.cmx

clean:
	rm -rf hello
	rm -rf submod
	rm -rf *.cmx
	rm -rf *.cmi
	rm -rf *.o
