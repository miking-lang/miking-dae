model Pendulum
  Real x;
  Real y;
  Real vx;
  Real vy;
  Real h;
initial equation
  x = 1;
  y = 0;
  der(vy) = -1;
equation
  der(x) = vx;
  der(y) = vy;
  der(vx) = x*h;
  der(vy) = y*h - 1;
  x*x+y*y = 1;  
end Pendulum;