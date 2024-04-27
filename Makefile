default_target: all

.PHONY: update_all clone_all bedrock2_noex fiat2 all clean_bedrock2 clean_fiat2 clean clean_deps clean_all install_bedrock2_noex install_fiat2 install

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
SORTING_DIR ?= $(ABS_ROOT_DIR)/coq-stdlib-edits/

bedrock2_noex:
	$(MAKE) -C $(BEDROCK2_DIR) bedrock2_noex

clean_bedrock2:
	$(MAKE) -C $(BEDROCK2_DIR) clean_bedrock2

install_bedrock2_noex:
	$(MAKE) -C $(BEDROCK2_DIR) install_bedrock2_noex

sorting:
	$(MAKE) -C $(SORTING_DIR)

clean_sorting:
	$(MAKE) -C $(SORTING_DIR) clean

fiat2: bedrock2_noex sorting
	$(MAKE) -C $(ABS_ROOT_DIR)/fiat2

clean_fiat2:
	$(MAKE) -C $(ABS_ROOT_DIR)/fiat2 clean

install_fiat2:
	$(MAKE) -C $(ABS_ROOT_DIR)/fiat2 install

all: bedrock2_noex fiat2

clean: clean_fiat2

clean_deps: clean_bedrock2 clean_sorting

clean_all: clean_deps clean

install: install_bedrock2_noex install_fiat2
