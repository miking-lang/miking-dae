model Recursive_Acc_Power
  // constant Integer n = 257;
  parameter Integer n = 3;
  function Pow
    input Real acc;
    input Integer n;
    input Real x;
    output Real y;
  algorithm
    if n == 0 then
      y := acc;
    else
      y := Pow(acc*x, n - 1, x); 
    end if;
  end Pow;
  Real y;
  Real dy;
equation
  y = Pow(1, n, time);
  dy = der(y);
end Recursive_Acc_Power;