model While_Power
  // constant Integer n = 257;
  parameter Integer n = 3;
  function Pow
    input Integer n;
    input Real x;
    output Real y;
  protected
    Integer i = n;
  algorithm
    y := 1;
    while not i == 0 loop
      y := y * x;
      i := i - 1;
    end while;
  end Pow;
  Real y;
  Real dy;
equation
  y = Pow(n, time);
  dy = der(y);
end While_Power;