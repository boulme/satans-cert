.PHONY: debug build clean cleanall

SRCD := ../coq_src

OCB:= ocamlbuild -I coq_extracted -I ImpureOracles -lib unix

build: coq_extracted
	$(OCB) SatAnsCert.native

debug: coq_extracted
	$(OCB) -cflag -g -lflag -g SatAnsCert.byte
	OCAMLRUNPARAM=b	./SatAnsCert.byte ${ARGS} || echo

# Auxiliary defs

$(SRCD)/Makefile: $(SRCD)/_CoqProject
	cd $(SRCD); coq_makefile -f _CoqProject -o Makefile

$(SRCD)/SatAnsCert.vo: $(SRCD)/Makefile $(SRCD)/*.v $(SRCD)/Impure/*.v 
	$(MAKE) -C $(SRCD) -j

$(SRCD)/ExtractDirectives.vo coq_extracted: Makefile $(SRCD)/SatAnsCert.vo $(SRCD)/ExtractDirectives.v
	rm -rf coq_extracted && mkdir coq_extracted && cd coq_extracted && coqc  -R ../$(SRCD) "SatansCert" -I ../$(SRCD) ../$(SRCD)/ExtractDirectives.v

clean:
	$(OCB) -clean
	rm -rf coq_extracted *~ *.mli

cleanall: clean
	$(MAKE) -C $(SRCD) cleanall
	rm -rf $(SRCD)/Makefile*
