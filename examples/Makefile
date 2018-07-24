.PHONY: check check_UNSAT check_SAT check_FAIL

BUG:=../bug_examples/test_v3_r8_vr5_c1_s8257.smt2-stp212

check: build check_UNSAT check_SAT check_FAIL

build:
	$(MAKE) -C ../ocaml build

check_UNSAT: build sudoku9-1.cnf sudoku9-1.lrat
	@echo
	../bin/satans-cert sudoku9-1.cnf -l sudoku9-1.lrat

check_SAT: build sudoku9-s1.cnf sudoku9-s1.out
	@echo
	../bin/satans-cert sudoku9-s1.cnf -lazy -s "!" -outfile sudoku9-s1.out

check_FAIL: build $(BUG).cnf $(BUG).lrat
	@echo
	../bin/satans-cert $(BUG).cnf -l $(BUG).lrat 2> /dev/null | grep "Certification failure: Cannot prove Rat !"
	@echo "FAILED AS EXPECTED"
