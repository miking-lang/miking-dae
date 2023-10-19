TOOL_NAME := peadae
TOOL_PATH := ../../build/${TOOL_NAME}
TOOL_COMPILATION_ARGS := --cse

BUILD_PEAD_COMMAND := ${TOOL_PATH} ${TOOL_COMPILATION_ARGS} --jac-spec-absolute
BUILD_AD_COMMAND := ${TOOL_PATH} ${TOOL_COMPILATION_ARGS} --disable-peval
BUILD_PEAD_RES_COMMAND := ${TOOL_PATH} ${TOOL_COMPILATION_ARGS} --benchmark-res --jac-spec-absolute
BUILD_AD_RES_COMMAND := ${TOOL_PATH} ${TOOL_COMPILATION_ARGS} --benchmark-res --disable-peval
BUILD_PEAD_JAC_COMMAND := ${TOOL_PATH} ${TOOL_COMPILATION_ARGS} --benchmark-jac --jac-spec-absolute
BUILD_AD_JAC_COMMAND := ${TOOL_PATH} ${TOOL_COMPILATION_ARGS} --benchmark-jac --disable-peval

CAUER_10_EXE := cauer_10-ad.exe cauer_10-0.exe cauer_10-1.exe cauer_10-2.exe
CAUER_10_MC := $(CAUER_10_EXE:.exe=.mc)
CAUER_10_RES_EXE := $(CAUER_10_EXE:.exe=.res.exe)
CAUER_10_RES_MC := $(CAUER_10_RES_EXE:.exe=.res.mc)
CAUER_10_JAC_EXE := $(CAUER_10_EXE:.exe=.jac.exe)
CAUER_10_JAC_MC := $(CAUER_10_JAC_EXE:.exe=.jac.mc)

CAUER_100_EXE := cauer_100-ad.exe cauer_100-0.exe cauer_100-1.exe cauer_100-2.exe
CAUER_100_MC := $(CAUER_100_EXE:.exe=.mc)
CAUER_100_RES_EXE := $(CAUER_100_EXE:.exe=.res.exe)
CAUER_100_RES_MC := $(CAUER_100_RES_EXE:.exe=.res.mc)
CAUER_100_JAC_EXE := $(CAUER_100_EXE:.exe=.jac.exe)
CAUER_100_JAC_MC := $(CAUER_100_JAC_EXE:.exe=.jac.mc)

PENDULUM_EXE := pendulum-ad.exe pendulum-0.exe pendulum-1.exe pendulum-2.exe
PENDULUM_MC := $(PENDULUM_EXE:.exe=.mc)
PENDULUM_RES_EXE := $(PENDULUM_EXE:.exe=.res.exe)
PENDULUM_RES_MC := $(PENDULUM_RES_EXE:.exe=.res.mc)
PENDULUM_JAC_EXE := $(PENDULUM_EXE:.exe=.jac.exe)
PENDULUM_JAC_MC := $(PENDULUM_JAC_EXE:.exe=.jac.mc)

FURUTA_EXE := furuta-ad.exe furuta-0.exe furuta-1.exe furuta-2.exe furuta-3.exe furuta-4.exe furuta-5.exe furuta-6.exe furuta-7.exe furuta-8.exe furuta-9.exe furuta-10.exe
FURUTA_MC := $(FURUTA_EXE:.exe=.mc)
FURUTA_RES_EXE := $(FURUTA_EXE:.exe=.res.exe)
FURUTA_RES_MC := $(FURUTA_RES_EXE:.exe=.res.mc)
FURUTA_JAC_EXE := $(FURUTA_EXE:.exe=.jac.exe)
FURUTA_JAC_MC := $(FURUTA_JAC_EXE:.exe=.jac.mc)

SIM_ARGS := --output-only-last --step-size 1 --rtol 1.e-5 --atol 1.e-7

SEED := 0
LABEL := G
RUNS := 100
WARMUP := 3
SLEEP := 5
SEED := 0

# 1: experiment name
# 2: simulation interval
# 3: configurations
# 4: name
define runhyperfine
	hyperfine 'taskset -c 0 ./$(1)-{n}.exe ${SIM_ARGS} --interval $(2)' --parameter-list n $(3) --warmup ${WARMUP} --runs ${RUNS} --export-json ${LABEL}-results-$(4).json
endef

# 1: type
# 2: experiment name
# 3: number of evals
# 4: configurations
# 5: name
define runhyperfineresjac
	hyperfine 'taskset -c 0 ./$(2)-{n}.$(1).exe --seed ${SEED} $(3)' --parameter-list n $(4) --warmup ${WARMUP} --runs ${RUNS} --export-json ${LABEL}-results-$(5)-$(1).json
endef

# 1: experiment name
# 2: simulation interval
# 3: configurations
define runhyperfinewithoutput1
	hyperfine 'taskset -c 0 ./$(1)-{n}.exe ${SIM_ARGS} --interval $(2) --dump-info' --parameter-list n $(3) --runs 1 --warmup 0 --show-output
endef

.PHONY: clean cauer-10 cauer_100 pendulum furuta bench all

all: cauer-10 cauer-100 pendulum furuta

cauer-10: $(CAUER_10_EXE) $(CAUER_10_MC)

cauer-100: $(CAUER_100_EXE) $(CAUER_100_MC)

pendulum: $(PENDULUM_EXE) $(PENDULUM_MC)

furuta: $(FURUTA_EXE) $(FURUTA_MC)

bench: bench-sim bench-res bench-jac

bench-sim: bench-cauer-10-sim bench-cauer-100-sim bench-pendulum-sim bench-furuta-sim

bench-res: bench-cauer-10-res bench-cauer-100-res bench-pendulum-res bench-furuta-res

bench-jac: bench-cauer-10-jac bench-cauer-100-jac bench-pendulum-jac bench-furuta-jac

output-sim: output-cauer-10-sim output-cauer-10-sim output-pendulum-sim output-furuta-sim

res_arg := ad,0

# Cauer 10
test_cauer_arg := 2,2,2,2
test-bench-cauer-10-sim: cauer_10-2.exe
	$(call runhyperfine,cauer_10,10000,$(test_cauer_arg),cauer_10_test)

test-bench-cauer-10-res: $(CAUER_10_RES_EXE)
	$(call runhyperfineresjac,res,cauer_10,106541,$(test_cauer_arg),cauer_10_test)

test-bench-cauer-10-jac: $(CAUER_10_JAC_EXE)
	$(call runhyperfineresjac,jac,cauer_10,2300,$(test_cauer_arg),cauer_10_test)

cauer_arg := ad,0,1,2
# cauer_arg := 2,1,0,ad
bench-cauer-10-sim: $(CAUER_10_EXE)
	$(call runhyperfine,cauer_10,10000,$(cauer_arg),cauer_10)

bench-cauer-10-res: $(CAUER_10_RES_EXE)
	$(call runhyperfineresjac,res,cauer_10,106541,$(cauer_arg),cauer_10)

cauer_jac_arg := 0,1,2
bench-cauer-10-jac: $(CAUER_10_JAC_EXE)
	$(call runhyperfineresjac,jac,cauer_10,2300,$(cauer_arg),cauer_10)

output-cauer-10-sim: $(CAUER_10_EXE)
	$(call runhyperfinewithoutput1,cauer_10,10000,$(cauer_arg))

# Cauer 100
bench-cauer-100-sim: $(CAUER_100_EXE)
	$(call runhyperfine,cauer_100,1000,$(cauer_arg),cauer_100)

bench-cauer-100-res: $(CAUER_100_RES_EXE)
	$(call runhyperfineresjac,res,cauer_100,11493,$(cauer_arg),cauer_100)

bench-cauer-100-jac: $(CAUER_100_JAC_EXE)
	$(call runhyperfineresjac,jac,cauer_100,2900,$(cauer_arg),cauer_100)

output-cauer-100-sim: $(CAUER_100_EXE)
	$(call runhyperfinewithoutput1,cauer_100,1000,$(cauer_arg))

pendulum_arg := ad,0,1,2
bench-pendulum-sim: $(PENDULUM_EXE)
	$(call runhyperfine,pendulum,10000,$(pendulum_arg),pendulum)

bench-pendulum-res: $(PENDULUM_RES_EXE)
	$(call runhyperfineresjac,res,pendulum,231687,$(pendulum_arg),pendulum)

pendulum_jac_arg := 0,1,2,3
bench-pendulum-jac: $(PENDULUM_JAC_EXE)
	$(call runhyperfineresjac,jac,pendulum,9819,$(pendulum_arg),pendulum)

output-pendulum-sim: $(PENDULUM_EXE)
	$(call runhyperfinewithoutput1,pendulum,10000,$(pendulum_arg))

furuta_arg := ad,0,1,2,3,4,5,6,7,8,9,10
bench-furuta-sim: $(FURUTA_EXE)
	$(call runhyperfine,furuta,1000,$(furuta_arg),furuta)

bench-furuta-res: $(FURUTA_RES_EXE)
	$(call runhyperfineresjac,res,furuta,105602,$(furuta_arg),furuta)

furuta_jac_arg := 0,1,2,3,4,5,6,7,8,9,10
bench-furuta-jac: $(FURUTA_JAC_EXE)
	$(call runhyperfineresjac,jac,furuta,4108,$(furuta_arg),furuta)

output-furuta-sim: $(FURUTA_EXE)
	$(call runhyperfinewithoutput1,furuta,1000,$(furuta_arg))

%.exe: %.mc
	mi compile --output $@ $<

%-0.mc: %.dae
	$(BUILD_PEAD_COMMAND) 0 $< > $@

%-1.mc: %.dae
	$(BUILD_PEAD_COMMAND) 1 $< > $@

%-2.mc: %.dae
	$(BUILD_PEAD_COMMAND) 2 $< > $@

%-3.mc: %.dae
	$(BUILD_PEAD_COMMAND) 3 $< > $@

%-4.mc: %.dae
	$(BUILD_PEAD_COMMAND) 4 $< > $@

%-5.mc: %.dae
	$(BUILD_PEAD_COMMAND) 5 $< > $@

%-6.mc: %.dae
	$(BUILD_PEAD_COMMAND) 6 $< > $@

%-7.mc: %.dae
	$(BUILD_PEAD_COMMAND) 7 $< > $@

%-8.mc: %.dae
	$(BUILD_PEAD_COMMAND) 8 $< > $@

%-9.mc: %.dae
	$(BUILD_PEAD_COMMAND) 9 $< > $@

%-10.mc: %.dae
	$(BUILD_PEAD_COMMAND) 10 $< > $@

%-ad.mc: %.dae
	$(BUILD_AD_COMMAND) $< > $@

%-0.res.mc: %.dae
	$(BUILD_PEAD_RES_COMMAND) 0 $< > $@

%-ad.res.mc: %.dae
	$(BUILD_AD_RES_COMMAND) $< > $@

%-0.res.mc: %.dae
	$(BUILD_PEAD_RES_COMMAND) 0 $< > $@

%-1.res.mc: %.dae
	$(BUILD_PEAD_RES_COMMAND) 1 $< > $@

%-2.res.mc: %.dae
	$(BUILD_PEAD_RES_COMMAND) 2 $< > $@

%-3.res.mc: %.dae
	$(BUILD_PEAD_RES_COMMAND) 3 $< > $@

%-4.res.mc: %.dae
	$(BUILD_PEAD_RES_COMMAND) 4 $< > $@

%-5.res.mc: %.dae
	$(BUILD_PEAD_RES_COMMAND) 5 $< > $@

%-6.res.mc: %.dae
	$(BUILD_PEAD_RES_COMMAND) 6 $< > $@

%-7.res.mc: %.dae
	$(BUILD_PEAD_RES_COMMAND) 7 $< > $@

%-8.res.mc: %.dae
	$(BUILD_PEAD_RES_COMMAND) 8 $< > $@

%-9.res.mc: %.dae
	$(BUILD_PEAD_RES_COMMAND) 9 $< > $@

%-10.res.mc: %.dae
	$(BUILD_PEAD_RES_COMMAND) 10 $< > $@

%-ad.jac.mc: %.dae
	$(BUILD_AD_JAC_COMMAND) $< > $@

%-0.jac.mc: %.dae
	$(BUILD_PEAD_JAC_COMMAND) 0 $< > $@

%-1.jac.mc: %.dae
	$(BUILD_PEAD_JAC_COMMAND) 1 $< > $@

%-2.jac.mc: %.dae
	$(BUILD_PEAD_JAC_COMMAND) 2 $< > $@

%-3.jac.mc: %.dae
	$(BUILD_PEAD_JAC_COMMAND) 3 $< > $@

%-4.jac.mc: %.dae
	$(BUILD_PEAD_JAC_COMMAND) 4 $< > $@

%-5.jac.mc: %.dae
	$(BUILD_PEAD_JAC_COMMAND) 5 $< > $@

%-6.jac.mc: %.dae
	$(BUILD_PEAD_JAC_COMMAND) 6 $< > $@

%-7.jac.mc: %.dae
	$(BUILD_PEAD_JAC_COMMAND) 7 $< > $@

%-8.jac.mc: %.dae
	$(BUILD_PEAD_JAC_COMMAND) 8 $< > $@

%-9.jac.mc: %.dae
	$(BUILD_PEAD_JAC_COMMAND) 9 $< > $@

%-10.jac.mc: %.dae
	$(BUILD_PEAD_JAC_COMMAND) 10 $< > $@

# 1: simulation executable
# 2: simulation interval
define cachestatssim
	for i in $(seq ${WARMUP}); do ./$(1) ${SIM_ARGS} --interval $(2); done &&\
	sudo perf stat -dd -r ${RUNS} ./$(1) ${SIM_ARGS} --dump-info --interval $(2)
endef

cauer-100-ad-sim-cache-stats: cauer_100-ad.exe
	$(call cachestatssim,$<,1000)

cauer-100-0-sim-cache-stats: cauer_100-0.exe
	$(call cachestatssim,$<,1000)

cauer-100-1-sim-cache-stats: cauer_100-1.exe
	$(call cachestatssim,$<,1000)

cauer-100-2-sim-cache-stats: cauer_100-2.exe
	$(call cachestatssim,$<,1000)

cauer-10-ad-sim-cache-stats: cauer_10-ad.exe
	$(call cachestatssim,$<,10000)

cauer-10-0-sim-cache-stats: cauer_10-0.exe
	$(call cachestatssim,$<,10000)

# 1: residual/jacobian executable
# 2: evaluations
define cachestatsresjac
	for i in $(seq ${WARMUP}); do ./$(1) --seed ${SEED} $(2); done &&\
	sudo perf stat -dd -r ${RUNS} ./$(1) --seed ${SEED} $(2)
endef

cauer-100-0-jac-cache-stats: cauer_100-0.jac.exe
	$(call cachestatsresjac,$<,2900)

cauer-100-1-jac-cache-stats: cauer_100-1.jac.exe
	$(call cachestatsresjac,$<,2900)

cauer-100-2-jac-cache-stats: cauer_100-2.jac.exe
	$(call cachestatsresjac,$<,2900)

furuta-0-jac-cache-stats: furuta-0.jac.exe
	$(call cachestatsresjac,$<,1000)

furuta-1-jac-cache-stats: furuta-1.jac.exe
	$(call cachestatsresjac,$<,1000)

clean:
	rm -rf *.exe *.mc
