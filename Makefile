default_target: all

.PHONY: update_all clone_all coqutil coq-record-update riscv-coq bedrock2_noex bedrock2_ex LiveVerif_noex LiveVerif_ex PyLevelLang compiler_noex compiler_ex kami processor end2end all clean_coqutil clean_coq-record-update clean_riscv-coq clean_bedrock2 clean_LiveVerif clean_PyLevelLang clean_compiler clean_kami clean_processor clean_end2end clean_manglenames clean install_coqutil install_coq-record-update install_kami install_riscv-coq install_bedrock2 install_bedrock2_ex install_bedrock2_noex install_LiveVerif install_LiveVerif_ex install_LiveVerif_noex install_PyLevelLang install_compiler install_processor install_end2end install

clone_all:
	git submodule update --init --recursive

update_all:
	git submodule update --recursive

REL_PATH_OF_THIS_MAKEFILE:=$(lastword $(MAKEFILE_LIST))
ABS_ROOT_DIR:=$(abspath $(dir $(REL_PATH_OF_THIS_MAKEFILE)))
# use cygpath -m because Coq on Windows cannot handle cygwin paths
ABS_ROOT_DIR:=$(shell cygpath -m '$(ABS_ROOT_DIR)' 2>/dev/null || echo '$(ABS_ROOT_DIR)')

BEDROCK2_DIR ?= $(ABS_ROOT_DIR)/bedrock2/
export BEDROCK2_DIR

bedrock2_noex:
	$(MAKE) -C $(BEDROCK2_DIR) bedrock2_noex

clean_bedrock2:
	$(MAKE) -C $(BEDROCK2_DIR) clean_bedrock2

install_bedrock2_noex:
	$(MAKE) -C $(BEDROCK2_DIR) install_bedrock2_noex

PyLevelLang: bedrock2_noex
	$(MAKE) -C $(ABS_ROOT_DIR)/PyLevelLang

clean_PyLevelLang:
	$(MAKE) -C $(ABS_ROOT_DIR)/PyLevelLang clean

install_PyLevelLang:
	$(MAKE) -C $(ABS_ROOT_DIR)/PyLevelLang install

all: bedrock2_noex PyLevelLang

clean: clean_PyLevelLang

clean_deps: clean_bedrock2

clean_all: clean_deps clean

install: install_bedrock2_noex install_PyLevelLang
