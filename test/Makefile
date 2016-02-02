TESTS := n0 n00 f	n1 p p2 print pf e01 e1 e2 e3 e4 e5 e6 if0 if1 loop1 loop0 loop while while1 looploop rec mr mr0 mwe exn0 exn1 exn2 raise exn3 ex9 # loopexn

.PHONY: run_tests testenv baseenv clean

run_tests:	$(TESTS)
	./test

testenv:
	eval `opam config env --sw=4.02.1+local-git-effects-refactor`

baseenv:
	eval `opam config env --sw=4.02.1`

test: baseenv
	ocamlfind ocamlc -o test -package batteries -package oUnit -linkpkg -g test.ml

$(TESTS): testenv
	ocamlc -o $@ $@.ml
	../compiler/js_of_ocaml --no-runtime ../runtime/runtime.js $@

clean:
	rm -f $(TESTS) $(patsubst %,%.cmo,$(TESTS)) $(patsubst %,%.cmi,$(TESTS)) $(patsubst %,%.js,$(TESTS))
	rm -f test test.cmi test.cmo
