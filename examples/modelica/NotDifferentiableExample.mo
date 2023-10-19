model NotDifferentiableExample
  Real position(start = 0);
  Real velocity;
  
  function ParticlePath
    input Real t;
    input Real amplitude;
    output Real y;
  algorithm
    y := sin(t);
    y := y * amplitude;
    annotation(ModelicaReference.Annotations.Inline = false);
  end ParticlePath;
equation
  velocity = der(position);
  position = ParticlePath(time, 2);
end NotDifferentiableExample;