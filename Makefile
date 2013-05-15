OTT=../tools/ott/bin/ott
COQC=coqc
COQDEP=coqdep

IsaOttTargets=Handlers.thy HandlersEx.thy
CoqOttTargets=Handlers.v HandlersEx.v
CoqSources=HandlersResults.v $(CoqOttTargets)
CoqVoTargets=$(patsubst %.v,%.vo,$(CoqSources))
CoqGlobs=$(patsubst %.v,%.glob,$(CoqSources))

.PHONY: all all-isa clean

all: all-isa-ott all-coq
all-isa-ott: $(IsaOttTargets)
all-coq-ott: $(CoqOttTargets)
all-coq: all-coq-ott $(CoqVoTargets)

clean:
	rm -f \
          $(IsaOttTargets) \
          $(CoqOttTargets) $(CoqVoTargets) $(CoqGlobs) coq.deps

# Fixes some old Isabelle syntax, plus an issue with the substitution function
# generation I don't quite understand
%.thy: %.ott
	$(OTT) $< -o $@
	sed \
          -e 's/types /type_synonym /' \
          -e 's/: set \[\([^]]*\)] @ \[\([^]]*\)]/: set ([\1] @ [\2])/' \
          < $@ > $@.out
	mv $@.out $@
%.v: %.ott
	$(OTT) $< -o $@
%.tex: %.ott
	$(OTT) $< -o $@

%.thy: %.thy.in
	$(OTT) $(filter %.ott,$^) -isa_filter $< $@
%.v: %.v.in
	$(OTT) $(filter %.ott,$^) -coq_filter $< $@

%.vo: %.v
	$(COQC) $<

# Manually say which files should be filtered with which ott rules
HandlersEx.thy: Handlers.ott
HandlersEx.v: Handlers.ott

coq.deps: $(CoqSources) Makefile
	$(COQDEP) -I . $^ > coq.deps

-include coq.deps
