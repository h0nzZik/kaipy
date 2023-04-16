
# https://stackoverflow.com/a/64068109/6209703
makeFileDir := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))

TEMP_DIR=${makeFileDir}/.tmp
$(shell mkdir -p ${TEMP_DIR})

.PHONY: default
default: build-imp

IMP_KOMPILED_DIR := ${TEMP_DIR}/build/imp/
IMP_TIMESTAMP := ${IMP_KOMPILED_DIR}/imp-kompiled/timestamp

.PHONY: build-imp
build-imp: ${IMP_TIMESTAMP}

${IMP_TIMESTAMP}: lang/imp/imp.k
	kompile --disable-kore-antileft --emit-json --no-prelude --backend haskell --directory ${IMP_KOMPILED_DIR} $<

.PHONY: run-sum
run-sum: ${IMP_TIMESTAMP}
	krun --definition ${IMP_KOMPILED_DIR}/imp-kompiled/ -cARGS="ListItem(5)" ./lang/imp/sum.imp

IMP_ANALYZER := ${IMP_KOMPILED_DIR}/analyzer.json

${IMP_ANALYZER}: ${IMP_TIMESTAMP}
	kaipy --definition ${IMP_KOMPILED_DIR}/imp-kompiled/ generate-analyzer --analyzer ${IMP_ANALYZER}

.PHONY: test-imp.sum
test-imp.sum: ${IMP_TIMESTAMP} ${IMP_ANALYZER}
	kaipy --definition ${IMP_KOMPILED_DIR}/imp-kompiled/ analyze --analyzer ${IMP_ANALYZER} --input ./lang/imp/sum.imp

.PHONY: clean
clean:
	rm -rf ${TEMP_DIR}