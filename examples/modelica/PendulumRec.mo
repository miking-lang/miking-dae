model PendulumRec
  parameter Integer p = 2;
  function Pow
    input Real x;
    input Integer n;
    output Real y;
  algorithm
    if n == 0 then y := 1;
    else y := x * Pow(x, n-1);
    end if;
    annotation(smoothOrder = 100);
  end Pow;
  function L
    input Real x;
    input Integer p;
    output Real y;
  algorithm
    y := 1 + 0.01*Pow(x, p);
    annotation(smoothOrder = 100);
  end L;
  Real t;
  Real x;
  Real vx;
  Real y;
  Real vy;
  Real T;
initial equation
  x = 1;
equation
  der(t) = 1;
  der(vx) = x*T + Pow(vx, p);
  der(vy) = y*T - 1;
  x^2 + y^2 = L(x, p)^2;
  der(x) = vx;
  der(y) = vy;
end PendulumRec;