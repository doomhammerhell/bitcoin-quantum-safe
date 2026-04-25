COQC = coqc
COQFLAGS = -Q . BitcoinPQ

SOURCES = SpendPredPQ.v UTXOTransitions.v VarintConcrete.v
OBJECTS = $(SOURCES:.v=.vo)

.PHONY: all clean

all: $(OBJECTS)

%.vo: %.v
	$(COQC) $(COQFLAGS) $<

clean:
	rm -f *.vo *.vok *.vos *.glob .*.aux
