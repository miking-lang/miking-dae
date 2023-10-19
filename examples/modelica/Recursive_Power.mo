model Recursive_Power
  // constant Integer n = 257;
  parameter Integer n = 3;
  function Pow
    input Integer n;
    input Real x;
    output Real y;
  algorithm
    if n == 0 then
      y := 1;
    else
      y := x * Pow(n - 1, x); 
    end if;
  end Pow;
  Real y;
  Real dy;
equation
  y = Pow(n, time);
  dy = der(y);
end Recursive_Power;