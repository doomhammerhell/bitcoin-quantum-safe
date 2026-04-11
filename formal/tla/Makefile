TLA2TOOLS = tla2tools.jar
SPEC = BitcoinPQ

.PHONY: check check-migration clean

# Check structural invariants (should PASS)
check:
	java -XX:+UseParallelGC -cp $(TLA2TOOLS) tlc2.TLC $(SPEC) -deadlock -workers auto

# Check migration safety (should FAIL — demonstrates the migration dilemma)
check-migration:
	java -XX:+UseParallelGC -cp $(TLA2TOOLS) tlc2.TLC $(SPEC) -config $(SPEC)_Migration.cfg -deadlock -workers auto

clean:
	rm -rf states/ *.toolbox *_TTrace*.tla
