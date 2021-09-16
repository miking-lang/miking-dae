SRC = $(wildcard *.mc)
EXAMPLES = examples
TESTS = $(SRC:.mc=.test)

test: $(TESTS)

%.test: %.test.exe
	./$<
	@echo ""
	@rm -f $<

%.run: %.run.exe
	@./$<

%.test.exe: %.mc
	mi compile --test $<
	@mv $(basename $(notdir $<)) $@

%.run.exe: %.mc
	@mi compile $<
	@mv $(basename $(notdir $<)) $@

clean:
	rm -f **/*.exe
