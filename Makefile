%.spthy: %.m4
	m4 $< > $@

.PHONY: all
all: odoh.spthy

.PHONY: proofs
proofs:
	tamarin-prover proofs/ODoH_proof.spthy
