TOOL_NAME=peadae

MODELS_NUMERIC_JAC := harmonic.dae pendulum.dae lrc.dae body.dae pendulum_3d.dae furuta.dae cauer.dae cauer_10.dae cauer_100.dae pendulum_rec.dae

OKS := $(MODELS_NUMERIC_JAC:.dae=-numjac.OK) $(MODELS_NUMERIC_JAC:.dae=-ad.OK) $(MODELS_NUMERIC_JAC:.dae=-0.OK) harmonic-1.OK harmonic-2.OK pendulum-1.OK pendulum-2.OK lrc-1.OK lrc-2.OK lrc-3.OK lrc-4.OK body-1.OK body-2.OK body-3.OK body-4.OK body-5.OK body-6.OK body-7.OK pendulum_3d-1.OK pendulum_3d-2.OK pendulum_3d-3.OK pendulum_3d-4.OK pendulum_3d-5.OK pendulum_3d-7.OK pendulum_3d-8.OK pendulum_3d-9.OK furuta-1.OK furuta-2.OK furuta-3.OK furuta-4.OK furuta-5.OK furuta-6.OK furuta-7.OK furuta-8.OK furuta-9.OK furuta-10.OK cauer-1.OK cauer-2.OK cauer_10-1.OK cauer_10-2.OK cauer_100-1.OK cauer_100-2.OK pendulum_rec-0.OK pendulum_rec-1.OK pendulum_rec-2.OK

EXES := $(OKS:.OK=.exe)
MCS := $(OKS:.OK=.mc)

PEADAE_SPEC := ../build/${TOOL_NAME} --debug --cse --jac-spec-absolute

.PHONY: test clean

test: $(OKS) $(EXES) $(MCS)

%.OK: %.out
	@f=$<; \
	echo -n $$f; \
	if cat $$f $${f%-*}.out.expected | ./compare; then \
		touch $@; \
		echo " OK"; \
	else \
		echo " FAIL"; \
	fi \

%.exe: %.mc
	@mi compile --output $@ $<

%.out: %.exe
	@./$< | tail -n 1 > $@

%.out.expected: %.dae
	../build/${TOOL_NAME} --numeric-jac $< > $<.mc && mi compile --output $<.exe $<.mc && ./$<.exe | tail -n 1 > $@

expected: $(MODELS_NUMERIC_JAC:.dae=.out.expected)

clean:
	rm -rf *.exe *.out *.mc *.OK

%-0-res.mc: %.dae
	@$(PEADAE_SPEC) 0 --benchmark-res $< > $@

%-1-res.mc: %.dae
	@$(PEADAE_SPEC) 1 --benchmark-res $< > $@

%-2-res.mc: %.dae
	@$(PEADAE_SPEC) 2 --benchmark-res $< > $@

%-3-res.mc: %.dae
	@$(PEADAE_SPEC) 3 --benchmark-res $< > $@

%-4-res.mc: %.dae
	@$(PEADAE_SPEC) 4 --benchmark-res $< > $@

%-5-res.mc: %.dae
	@$(PEADAE_SPEC) 5 --benchmark-res $< > $@

%-6-res.mc: %.dae
	@$(PEADAE_SPEC) 6 --benchmark-res $< > $@

%-7-res.mc: %.dae
	@$(PEADAE_SPEC) 7 --benchmark-res $< > $@

%-8-res.mc: %.dae
	@$(PEADAE_SPEC) 8 --benchmark-res $< > $@

%-9-res.mc: %.dae
	@$(PEADAE_SPEC) 9 --benchmark-res $< > $@

%-10-res.mc: %.dae
	@$(PEADAE_SPEC) 10 --benchmark-res $< > $@

%-ad-res.mc: %.dae
	@../build/${TOOL_NAME} --debug --cse --disable-peval --benchmark-res $< > $@

%-0-jac.mc: %.dae
	@$(PEADAE_SPEC) 0 --benchmark-jac $< > $@

%-1-jac.mc: %.dae
	@$(PEADAE_SPEC) 1 --benchmark-jac $< > $@

%-2-jac.mc: %.dae
	@$(PEADAE_SPEC) 2 --benchmark-jac $< > $@

%-3-jac.mc: %.dae
	@$(PEADAE_SPEC) 3 --benchmark-jac $< > $@

%-4-jac.mc: %.dae
	@$(PEADAE_SPEC) 4 --benchmark-jac $< > $@

%-5-jac.mc: %.dae
	@$(PEADAE_SPEC) 5 --benchmark-jac $< > $@

%-6-jac.mc: %.dae
	@$(PEADAE_SPEC) 6 --benchmark-jac $< > $@

%-7-jac.mc: %.dae
	@$(PEADAE_SPEC) 7 --benchmark-jac $< > $@

%-8-jac.mc: %.dae
	@$(PEADAE_SPEC) 8 --benchmark-jac $< > $@

%-9-jac.mc: %.dae
	@$(PEADAE_SPEC) 9 --benchmark-jac $< > $@

%-10-jac.mc: %.dae
	@$(PEADAE_SPEC) 10 --benchmark-jac $< > $@

%-ad-jac.mc: %.dae
	@../build/${TOOL_NAME} --debug --cse --disable-peval --benchmark-jac $< > $@

%-0.mc: %.dae
	@$(PEADAE_SPEC) 0 $< > $@

%-1.mc: %.dae
	@$(PEADAE_SPEC) 1 $< > $@

%-2.mc: %.dae
	@$(PEADAE_SPEC) 2 $< > $@

%-3.mc: %.dae
	@$(PEADAE_SPEC) 3 $< > $@

%-4.mc: %.dae
	@$(PEADAE_SPEC) 4 $< > $@

%-5.mc: %.dae
	@$(PEADAE_SPEC) 5 $< > $@

%-6.mc: %.dae
	@$(PEADAE_SPEC) 6 $< > $@

%-7.mc: %.dae
	@$(PEADAE_SPEC) 7 $< > $@

%-8.mc: %.dae
	@$(PEADAE_SPEC) 8 $< > $@

%-9.mc: %.dae
	@$(PEADAE_SPEC) 9 $< > $@

%-10.mc: %.dae
	@$(PEADAE_SPEC) 10 $< > $@

%-numjac.mc: %.dae
	@../build/${TOOL_NAME} --debug --cse --numeric-jac $< > $@

%-ad.mc: %.dae
	@../build/${TOOL_NAME} --debug --cse --disable-peval $< > $@
