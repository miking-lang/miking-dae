model ScopeTest
  Real z;
  function f
    input Real x;
    output Real y;
    algorithm
      y := z;
  end f;
equation
  z + f(1) = 0;
end ScopeTest;