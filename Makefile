TOOL_NAME=peadae
BIN_PATH=${HOME}/.local/bin

SRCS := $(shell find . -name "*.mc" -a ! -name "peadae.mc" -a ! -name "ast_gen.mc" -a ! -wholename "./examples/*" ! -wholename "./legacy/*")
TESTS := $(SRCS:.mc=.test)
TESTBINS := $(SRCS:.mc=.test.exe.run)

.PHONY: test test-examples watch-test clean

all: build/${TOOL_NAME}

build/${TOOL_NAME}: ${TOOL_NAME}.exe
	mkdir -p build
	mv ${TOOL_NAME}.exe build/${TOOL_NAME}

test: $(TESTS)

test-compiled: $(TESTBINS)

test-examples:
	$(MAKE) test -C examples

test-all: test test-examples

%.test: %.mc
	mi --test $<
	@echo ""

%.exe.run: %.exe
	./$<
	@echo ""

%.test.exe: %.mc
	mi compile --test --output $@ $<

%.exe: %.mc
	mi compile --output $@ $<

${TOOL_NAME}.exe: $(SRCS)

ast_gen.mc: ast.syn
	mi syn ast.syn ast_gen.mc

watch:
	find . "(" -name "*.mc" -o -name "*.syn" ")" -a ! -name "ast_gen.mc" | entr -rc make test

install: build/${TOOL_NAME}
	cp build/${TOOL_NAME} ${BIN_PATH}

uninstall:
	rm -f ${BIN_PATH}/${TOOL_NAME}

clean:
	rm -rf *.exe build
