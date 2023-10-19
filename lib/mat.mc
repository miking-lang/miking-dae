include "tensor.mc"
include "vec.mc"

type Matrix a = Tensor[a]

let matCreate : all a. (Int, Int) -> (Int -> Int -> a) -> Matrix a =
  lam dim. lam f.
    match dim with (n, m) in
    tensorCreateDense [n, m] (lam idx. f (get idx 0) (get idx 1))

let matCreateFloat : (Int, Int) -> (Int -> Int -> Float) -> Matrix Float =
  lam dim. lam f.
    match dim with (n, m) in
    tensorCreateCArrayFloat [n, m] (lam idx. f (get idx 0) (get idx 1))

let matGet : all a. Matrix a -> Int -> Int -> a =
  lam mat. lam i. lam j. tensorGetExn mat [i, j]

let matSet : all a. Matrix a -> Int -> Int -> a -> () =
  lam mat. lam i. lam j. lam v. tensorSetExn mat [i, j] v

let matOfSeq : all a. (Int, Int) -> [a] -> Matrix a =
  lam dim. lam seq.
    match dim with (n, m) in
    tensorOfSeqExn tensorCreateDense [n, m] seq

let matOfSeqFloat : (Int, Int) -> [Float] -> Matrix Float =
  lam dim. lam seq.
    match dim with (n, m) in
    tensorOfSeqExn tensorCreateCArrayFloat [n, m] seq

let matSize : all a. Matrix a -> Int = tensorSize

let matFlatten : all a. Matrix a -> Vector a =
  lam mat. tensorReshapeExn mat [tensorSize mat]

let matDim : all a. Matrix a -> (Int, Int) =
  lam mat.
    let shape = tensorShape mat in
    (get shape 0, get shape 1)

let matTranspose : all a. Matrix a -> Matrix a = lam mat. tensorTransposeExn mat 0 1

let matMapi : all a. all b. (Int -> Int -> a -> b -> b) -> Matrix a -> Matrix b -> () =
  lam f. lam mat. tensorMapiExn (lam idx. f (get idx 0) (get idx 1)) mat

let matMap : all a. all b. (a -> b) -> Matrix a -> Matrix b -> () = tensorMapExn
let matIterRow : all a. (Int -> Vector a -> ()) -> Matrix a -> () = tensorIterSlice

let matIsSquareMatrix : all a. Matrix a -> Bool =
  lam mat. match tensorShape mat with [n, m] then eqi n m else false

let matEq : all a. all b. (a -> b -> Bool) -> Matrix a -> Matrix b -> Bool = tensorEq
let matRow : all a. Matrix a -> Int -> Vector a = lam mat. lam i. tensorSliceExn mat [i]

let matFoldi : all a. all b. (a -> Int -> Int -> b -> a) -> a -> Matrix b -> a =
  lam f. tensorFoldi (lam acc. lam idx. f acc (get idx 0) (get idx 1))

let matToString : all a. (a -> String) -> Matrix a -> String =
  lam eq2str. lam mat.
    let ret = ref "[\n" in
    matIterRow
      (lam. lam r. modref ret (join [deref ret, "  ", vecToString eq2str r, "\n"]))
      mat;
    concat (deref ret) "]"
