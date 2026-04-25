TLA2TOOLS = tla2tools.jar
SPEC = BitcoinPQ
SPEC_MULTI = BitcoinPQMulti

.PHONY: check check-migration check-multi check-multi-freeze check-all clean

# Check structural invariants (should PASS)
check:
	java -XX:+UseParallelGC -cp $(TLA2TOOLS) tlc2.TLC $(SPEC) -deadlock -workers auto

# Check migration safety (should FAIL — demonstrates the migration dilemma)
check-migration:
	java -XX:+UseParallelGC -cp $(TLA2TOOLS) tlc2.TLC $(SPEC) -config $(SPEC)_Migration.cfg -deadlock -workers auto

# Check multi-input/output model with value conservation (should PASS)
check-multi:
	java -XX:+UseParallelGC -cp $(TLA2TOOLS) tlc2.TLC $(SPEC_MULTI) -deadlock -workers auto

# Check freeze enforcement on multi model (should FAIL — demonstrates freeze dilemma)
check-multi-freeze:
	java -XX:+UseParallelGC -cp $(TLA2TOOLS) tlc2.TLC $(SPEC_MULTI) -config $(SPEC_MULTI)_Freeze.cfg -deadlock -workers auto

# Run all passing checks
check-all: check check-multi

clean:
	rm -rf states/ *.toolbox *_TTrace*.tla
