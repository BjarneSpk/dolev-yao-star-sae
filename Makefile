# Build for the SAE model in DY*.
# DY* and Comparse are git submodules in deps/ (git submodule update --init).
# `fstar.exe` must be in PATH (or set FSTAR_EXE).

PROJECT_HOME  ?= .
DY_HOME       ?= $(PROJECT_HOME)/deps/dolev-yao-star-extrinsic
COMPARSE_HOME ?= $(PROJECT_HOME)/deps/comparse
FSTAR_EXE     ?= $(shell which fstar.exe)

DY_SOURCE_DIRS = core lib lib/comparse lib/crypto lib/event lib/hpke lib/label lib/state lib/utils lib/communication
DY_INCLUDE_DIRS = $(addprefix $(DY_HOME)/src/, $(DY_SOURCE_DIRS))
SAE_SOURCE_DIRS = $(PROJECT_HOME)/src

INCLUDE_DIRS = $(SAE_SOURCE_DIRS) $(DY_INCLUDE_DIRS) $(COMPARSE_HOME)/src
FSTAR_INCLUDE_DIRS = $(addprefix --include , $(INCLUDE_DIRS))

ADMIT ?=
MAYBE_ADMIT = $(if $(ADMIT),--admit_smt_queries true)

FSTAR = $(FSTAR_EXE) $(MAYBE_ADMIT)

# Warning 242: inner let-rec not encoded to the solver
# Warning 335: interface admitted without implementation
FSTAR_FLAGS = $(FSTAR_INCLUDE_DIRS) --cache_checked_modules --already_cached '+Prims +FStar' \
  --warn_error '@0..1000' --warn_error '+242-335' --record_hints \
  --hint_dir $(PROJECT_HOME)/hints --cache_dir $(PROJECT_HOME)/cache --odir $(PROJECT_HOME)/obj --cmi \
  --z3version 4.15.3

.PHONY: all clean
all: check

clean:
	rm -rf $(PROJECT_HOME)/hints $(PROJECT_HOME)/obj $(PROJECT_HOME)/cache $(PROJECT_HOME)/.depend

# Dependency analysis (all SAE sources; DY* and Comparse are pulled in transitively)

FSTAR_ROOTS = \
  $(wildcard $(addsuffix /*.fsti,$(SAE_SOURCE_DIRS))) \
  $(wildcard $(addsuffix /*.fst,$(SAE_SOURCE_DIRS)))

ifeq (,$(filter %-in,$(MAKECMDGOALS)))
ifndef MAKE_RESTARTS
$(PROJECT_HOME)/.depend: .FORCE
	$(FSTAR) $(FSTAR_FLAGS) --dep full --extract '-* +DY +Comparse +SAE' $(notdir $(FSTAR_ROOTS)) > $@

.PHONY: .FORCE
.FORCE:
endif
endif

include $(PROJECT_HOME)/.depend

# Verification

$(PROJECT_HOME)/hints $(PROJECT_HOME)/cache $(PROJECT_HOME)/obj:
	mkdir -p $@

%.checked: | $(PROJECT_HOME)/hints $(PROJECT_HOME)/cache $(PROJECT_HOME)/obj
	$(FSTAR) $(FSTAR_FLAGS) $< && touch -c $@

# Editor support (F* IDE / MCP ask for include dirs)
%.fst-in %.fsti-in:
	@echo $(FSTAR_INCLUDE_DIRS)

.PHONY: check
check: $(addsuffix .checked,$(addprefix $(PROJECT_HOME)/cache/,$(notdir $(FSTAR_ROOTS))))

SANITY_FLAGS = $(filter-out --cache_checked_modules --record_hints,$(FSTAR_FLAGS)) --include $(PROJECT_HOME)/sanity
SANITY_LEMMAS = $(shell grep -oE '^val (ok|bad)_[a-z_]+' $(PROJECT_HOME)/sanity/SAE.Group.Sanity.fst | cut -d' ' -f2)

.PHONY: sanity
sanity: $(PROJECT_HOME)/cache/SAE.Group.Labels.fst.checked
	@for l in $(SANITY_LEMMAS); do \
	  if $(FSTAR) $(SANITY_FLAGS) SAE.Group.Sanity.fst --admit_except "SAE.Group.Sanity.$$l" > /dev/null 2>&1; \
	  then r=verifies; else r=fails; fi; \
	  case $$l in ok_*) e=verifies;; *) e=fails;; esac; \
	  if [ $$r = $$e ]; then s=OK; else s=UNEXPECTED; fi; \
	  echo "$$s  $$l $$r (expected: $$e)"; \
	done

# Extraction to OCaml and execution of the honest runs (SAE.Debug)
# `make test` needs OCaml (the version F* was built with), ocamlfind, ocamlbuild and batteries.

.PRECIOUS: $(PROJECT_HOME)/obj/%.ml
$(PROJECT_HOME)/obj/%.ml:
	$(FSTAR) $(FSTAR_FLAGS) $(notdir $(subst .checked,,$<)) --codegen OCaml \
	--extract_module $(basename $(notdir $(subst .checked,,$<)))

.PHONY: extract test
extract: $(ALL_ML_FILES)

# The OCaml library of the F* release binary only links with its own dependency versions.
# Use an F* installed with opam (`opam install fstar.2025.12.15`) for the compilation.
OCAML_FSTAR_EXE ?= $(FSTAR_EXE)

test: extract
	cd $(PROJECT_HOME)/obj; rm -rf _build; $(OCAML_FSTAR_EXE) --ocamlenv ocamlbuild -use-ocamlfind -pkg batteries -pkg fstar.lib SAE_Debug.native
	$(PROJECT_HOME)/obj/SAE_Debug.native
