%.spthy: %.m4
	m4 $< > $@

.PHONY: all
all: odoh.spthy odoh_fix.spthy

.PHONY: proofs
proofs:
	tamarin-prover proofs/*
