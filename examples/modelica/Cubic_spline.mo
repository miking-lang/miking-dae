

model Cubic_spline
  import Modelica.Utilities.Streams.*;
  
  constant String dir = Modelica.Utilities.Files.loadResource("modelica://Cubic_spline");
  final parameter String data_file_name = dir + "/cubic_spline_interpolation_data.mat";
  final parameter Integer dimc[2] = readMatrixSize(data_file_name,"c");
  final parameter Integer dimx[2] = readMatrixSize(data_file_name,"x");
  final parameter Integer dimy[2] = readMatrixSize(data_file_name,"y");
  final parameter Real C[4,:] = readRealMatrix(data_file_name,"c",dimc[1],dimc[2]);
  final parameter Real X[1,:] = readRealMatrix(data_file_name,"x",dimx[1],dimx[2]);
  final parameter Real Y[1,:] = readRealMatrix(data_file_name,"y",dimy[1],dimy[2]);
  final parameter Real xdata[:] = X[1,:];
  final parameter Real ydata[:] = Y[1,:];
  function InterpolateF
    input Real C[4,:];
    input Real xdata[:];
    input Real x;
    output Real y;
  protected
    constant Integer n = size(xdata,1);
    Integer i;
  algorithm
    if x < xdata[1] or x > xdata[n] then 
      error("InterpolateF: Input outside domain");
    end if;
    i := 1;
    while i < n and x > xdata[i + 1] loop
      i := i + 1;
    end while;
    if i == n then
      i := i - 1;
    end if;
    y := C[1,i]*(x-xdata[i])^3;
    y := y + C[2,i]*(x-xdata[i])^2;
    y := y + C[3,i]*(x-xdata[i]);
    y := y + C[4,i];
    annotation(ModelicaReference.Annotations.Inline = false);
  end InterpolateF;
  Real u;
  Real du;
  Real d2u;
  Real d3u;
equation
  u = InterpolateF(C,xdata,time);
  du = der(u);
  d2u = der(du);
  d3u = der(d2u);
end Cubic_spline;