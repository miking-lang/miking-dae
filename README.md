# Miking-DAE
An Automatic Differentiation based Differential Algebraic Equations (DAE) solver that handles high-index DAEs with stabilization.

## Installation

### Step 1
Install the miking compiler with sundials support. See https://github.com/miking-lang/miking.

### Step 2
For simple plotting, install http://www.gnuplot.info/.

## Example
A full working and documented example can be found in [examples/pendulum-actuated-ipm.mc](examples/pendulum-actuated-ipm.mc).

To compile and simulate this model do (assuming the miking compiler `mi` is added to `PATH`)
```
mi compile examples/pendulum-actuated-ipm.mc && ./pendulum-actuated-ipm
```

To also plot the result using gnuplot you instead do
```
mi compile examples/pendulum-actuated-ipm.mc && ./pendulum-actuated-ipm | ./tools/csvplot
```

## Inteface
You can find an interface to the solver based on the Interactive Programmatic Modeling journal article by David Broman here:
[daecore-ipm.mc](daecore-ipm.mc)

## References
The implementation is (although not exclusively) based on the following papers:
- Pryce, J. D. (2001) A Simple Structural Analysis Method for DAEs, https://link.springer.com/article/10.1023/A:1021998624799
- Otter, Martin and Elmqvist, Hilding (2017) Transformation of Differential Algebraic Array Equations to Index One Form, https://elib.dlr.de/117431/
- Broman, David (2021) Interactive Programmatic Modeling, https://dl.acm.org/doi/10.1145/3431387
