prover_tests:
	emacs src/prover_tests.ml
prover_dependent_type:
	ocamlopt src/prover_dependent_type.ml -o prover_dependent_type
	rm src/*.cmi src/*.cmx src/*.o
prover_notests:
	ocamlopt src/prover_notests.ml -o prover_notests
	rm src/*.cmi src/*.cmx src/*.o

all_prover: prover_notests prover_dependent_type

add.proof:
	cat proof/add.proof | ./prover_notests 
andcomm.proof:
	cat proof/andcomm.proof | ./prover_notests 
app.proof:
	cat proof/app.proof | ./prover_notests 
appid.proof:
	cat proof/appid.proof | ./prover_notests
bool.proof:
	cat proof/bool.proof | ./prover_dependent_type 
comp.proof:
	cat proof/comp.proof | ./prover_notests 
contr.proof:
	cat proof/contr.proof | ./prover_notests 
curry1.proof:
	cat proof/curry1.proof | ./prover_notests 
curry2.proof:
	cat proof/curry2.proof | ./prover_notests 
diag.proof:
	cat proof/diag.proof | ./prover_notests 
dist.proof:
	cat proof/dist.proof | ./prover_notests 
felim.proof:
	cat proof/felim.proof | ./prover_notests 
impdm.proof:
	cat proof/impdm.proof | ./prover_notests 
injl.proof:
	cat proof/injl.proof | ./prover_notests 
injr.proof:
	cat proof/injr.proof | ./prover_notests 
nnef.proof:
	cat proof/nnef.proof | ./prover_notests 
nnem.proof:
	cat proof/nnem.proof | ./prover_notests 
nni.proof:
	cat proof/nni.proof | ./prover_notests 
ntf.proof:
	cat proof/ntf.proof | ./prover_notests 
orcomm.proof:
	cat proof/orcomm.proof | ./prover_notests 
orelim.proof:
	cat proof/orelim.proof | ./prover_notests 
pred.proof:
	cat proof/pred.proof | ./prover_notests 
russel.proof:
	cat proof/russel.proof | ./prover_notests 
s.proof:
	cat proof/s.proof | ./prover_notests 
tintro.proof:
	cat proof/tintro.proof | ./prover_notests 
tstr.proof:
	cat proof/tstr.proof | ./prover_notests

all_proof :
	cat proof/add.proof | ./prover_notests 
	cat proof/andcomm.proof | ./prover_notests 
	cat proof/app.proof | ./prover_notests 
	cat proof/appid.proof | ./prover_notests
	cat proof/bool.proof | ./prover_dependent_type 
	cat proof/comp.proof | ./prover_notests 
	cat proof/contr.proof | ./prover_notests 
	cat proof/curry1.proof | ./prover_notests 
	cat proof/curry2.proof | ./prover_notests 
	cat proof/diag.proof | ./prover_notests 
	cat proof/dist.proof | ./prover_notests 
	cat proof/felim.proof | ./prover_notests 
	cat proof/impdm.proof | ./prover_notests 
	cat proof/injl.proof | ./prover_notests 
	cat proof/injr.proof | ./prover_notests 
	cat proof/nnef.proof | ./prover_notests 
	cat proof/nnem.proof | ./prover_notests 
	cat proof/nni.proof | ./prover_notests 
	cat proof/ntf.proof | ./prover_notests 
	cat proof/orcomm.proof | ./prover_notests 
	cat proof/orelim.proof | ./prover_notests 
	cat proof/pred.proof | ./prover_notests 
	cat proof/russel.proof | ./prover_notests 
	cat proof/s.proof | ./prover_notests 
	cat proof/tintro.proof | ./prover_notests 
	cat proof/tstr.proof | ./prover_notests