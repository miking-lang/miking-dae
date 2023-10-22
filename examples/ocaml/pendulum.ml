open Sundials

let resf _ v v' r =
  let x = v.{0}
  and y = v.{1}
  and x' = v.{2}
  and y' = v.{3}
  and h = v.{4}
  and vx = v.{5}
  and vy = v.{6}
  and x'' = v'.{2}
  and y'' = v'.{3}
  and vx' = v'.{5}
  and vy' = v'.{6}
  in
  (* Differential Aliases *)
  r.{0} <- v'.{0} -. x';
  r.{1} <- v'.{1} -. y';
  (* Equations *)
  r.{2} <- vx' -. x'';
  r.{3} <- vy' -. y'';
  r.{4} <- vx' -. h *. x;
  r.{5} <- vy' -. h *. y +. 1.;
  r.{6} <- x''*.x +. x'*.x' +. y''*.y +. y'*.y'

let vd = RealArray.of_list [1.; 0.; 0.; 0.; 0.; 0.; 0.]
let v  = Nvector_serial.wrap vd
let v' = Nvector_serial.wrap (RealArray.of_list [0.; 0.; 0.; -1.; 0.; 0.; -1.])

let vids = Nvector_serial.make 7 Ida.VarId.differential;;
(Nvector_serial.unwrap vids).{4} <- Ida.VarId.algebraic;;

let m = Matrix.dense 7
let s = Ida.(init (SStolerances (1e-6, 1e-4))
               ~lsolver:Dls.(solver (dense v m))
               ~varid:vids
               resf
               0.0
               v
               v');;

Ida.set_stop_time s 10.0;

Ida.calc_ic_ya_yd' s ~y:v ~y':v' 0.1;;

let rec go (t, r) =
  Printf.printf "% .10e\t% .10e\n" vd.{0} vd.{1};
  match r with
  | Ida.Success -> go (Ida.solve_normal s (t +. 0.05) v v')
  | Ida.StopTimeReached -> ();;

Printf.printf "x\ty\n";
go (0.0, Ida.Success);;
