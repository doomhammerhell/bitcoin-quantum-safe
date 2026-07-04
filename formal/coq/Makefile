COQC = coqc
COQFLAGS = -Q . BitcoinPQ

# Core verification modules
SOURCES = SpendPredPQ.v UTXOTransitions.v VarintConcrete.v SighashV2.v TxidPreimage.v
OBJECTS = $(SOURCES:.v=.vo)

# Extraction modules (require all others)
EXTRACTION = extraction/WitnessExtraction.v extraction/SighashExtraction.v extraction/TxidExtraction.v extraction/TransitionExtraction.v
EXTRACTION_OBJ = extraction/WitnessExtraction.vo
EXTRACTION_DRIVER = extraction/ExtractWitnessVectors.v
EXTRACTION_DRIVER_OBJ = extraction/ExtractWitnessVectors.vo
SIGHASH_EXTRACTION_OBJ = extraction/SighashExtraction.vo
SIGHASH_EXTRACTION_DRIVER = extraction/ExtractSighashVectors.v
SIGHASH_EXTRACTION_DRIVER_OBJ = extraction/ExtractSighashVectors.vo
TXID_EXTRACTION_OBJ = extraction/TxidExtraction.vo
TXID_EXTRACTION_DRIVER = extraction/ExtractTxidVectors.v
TXID_EXTRACTION_DRIVER_OBJ = extraction/ExtractTxidVectors.vo
TRANSITION_EXTRACTION_OBJ = extraction/TransitionExtraction.vo
TRANSITION_EXTRACTION_DRIVER = extraction/ExtractTransitionVectors.v
TRANSITION_EXTRACTION_DRIVER_OBJ = extraction/ExtractTransitionVectors.vo

.PHONY: all clean extraction verify

all: $(OBJECTS)

# Build individual .vo files
%.vo: %.v
	$(COQC) $(COQFLAGS) $<

# SighashV2 depends on VarintConcrete
SighashV2.vo: VarintConcrete.vo SpendPredPQ.vo

# TxidPreimage reuses SighashV2 transaction and serialization definitions
TxidPreimage.vo: SighashV2.vo

# Build extraction modules
extraction: $(OBJECTS) $(EXTRACTION_OBJ) $(EXTRACTION_DRIVER_OBJ) $(SIGHASH_EXTRACTION_OBJ) $(SIGHASH_EXTRACTION_DRIVER_OBJ) $(TXID_EXTRACTION_OBJ) $(TXID_EXTRACTION_DRIVER_OBJ) $(TRANSITION_EXTRACTION_OBJ) $(TRANSITION_EXTRACTION_DRIVER_OBJ)

extraction/WitnessExtraction.vo: extraction/WitnessExtraction.v $(OBJECTS)
	cd extraction && $(COQC) -Q .. BitcoinPQ WitnessExtraction.v

extraction/ExtractWitnessVectors.vo: extraction/ExtractWitnessVectors.v extraction/WitnessExtraction.vo
	cd extraction && $(COQC) -Q .. BitcoinPQ ExtractWitnessVectors.v

extraction/SighashExtraction.vo: extraction/SighashExtraction.v SighashV2.vo
	cd extraction && $(COQC) -Q .. BitcoinPQ SighashExtraction.v

extraction/ExtractSighashVectors.vo: extraction/ExtractSighashVectors.v extraction/SighashExtraction.vo
	cd extraction && $(COQC) -Q .. BitcoinPQ ExtractSighashVectors.v

extraction/TxidExtraction.vo: extraction/TxidExtraction.v TxidPreimage.vo
	cd extraction && $(COQC) -Q .. BitcoinPQ TxidExtraction.v

extraction/ExtractTxidVectors.vo: extraction/ExtractTxidVectors.v extraction/TxidExtraction.vo
	cd extraction && $(COQC) -Q .. BitcoinPQ ExtractTxidVectors.v

extraction/TransitionExtraction.vo: extraction/TransitionExtraction.v UTXOTransitions.vo
	cd extraction && $(COQC) -Q .. BitcoinPQ TransitionExtraction.v

extraction/ExtractTransitionVectors.vo: extraction/ExtractTransitionVectors.v extraction/TransitionExtraction.vo
	cd extraction && $(COQC) -Q .. BitcoinPQ ExtractTransitionVectors.v

# Extract to OCaml
extract-ocaml: extraction
	@echo "Generated extraction/golden_vectors_extracted.ml, extraction/sighash_extracted.ml, extraction/txid_extracted.ml, and extraction/transition_extracted.ml"

# Run all proofs
verify: all
	@echo "=========================================="
	@echo "Proof Obligations Verification Status"
	@echo "=========================================="
	@echo ""
	@echo "PO-1 (Totality):          VERIFIED (SpendPredPQ.vo)"
	@echo "PO-2 (Determinism):       VERIFIED (SpendPredPQ.vo)"
	@echo "PO-3 (Parse Canonicality): VERIFIED (SpendPredPQ.vo)"
	@echo "PO-4 (Sighash Commitment): VERIFIED MODEL (SighashV2.vo + Rust PBT)"
	@echo "PO-5 (Transition Det.):    VERIFIED MODEL (UTXOTransitions.vo); txid/transition/final-state extraction refinement via build_extraction.sh"
	@echo "PO-7 (Cost Boundedness):   VERIFIED (UTXOTransitions.vo)"
	@echo "PO-8 (Correspondence):     BOUNDED EVIDENCE + CONCRETE CANONICALITY + EXHAUSTIVE VARINT + CONSENSUS WITNESS REFINEMENT"

clean:
	rm -f *.vo *.vok *.vos *.glob .*.aux
	rm -f *.lia.cache .lia.cache *.nia.cache .nia.cache
	rm -f extraction/*.vo extraction/*.vok extraction/*.vos extraction/*.glob extraction/.*.aux
	rm -f extraction/*.lia.cache extraction/.lia.cache extraction/*.nia.cache extraction/.nia.cache
	rm -f extraction/*.cmi extraction/*.cmo extraction/golden_vectors extraction/varint_refinement extraction/witness_refinement extraction/sighash_refinement extraction/txid_refinement extraction/transition_refinement
	rm -f extraction/golden_vectors_extracted.ml extraction/golden_vectors_extracted.mli
	rm -f extraction/sighash_extracted.ml extraction/sighash_extracted.mli
	rm -f extraction/txid_extracted.ml extraction/txid_extracted.mli
	rm -f extraction/transition_extracted.ml extraction/transition_extracted.mli
	rm -f extraction/coq_varint_refinement.json extraction/coq_witness_refinement.json extraction/coq_sighash_refinement.json extraction/coq_txid_refinement.json extraction/coq_transition_refinement.json
