include "tensor.mc"
include "vec.mc"

type Matrix a = Tensor[a]

let matCreate : (Int, Int) -> (Int -> Int -> a) -> Matrix a
= lam dim. lam f.
  match dim with (n, m) then
    tensorCreateDense [n, m] (lam idx. f (get idx 0) (get idx 1))
  else never

let matCreateFloat : (Int, Int) -> (Int -> Int -> Float) -> Matrix Float
= lam dim. lam f.
  match dim with (n, m) then
    tensorCreateCArrayFloat [n, m] (lam idx. f (get idx 0) (get idx 1))
  else never

let matGet : Matrix a -> Int -> Int -> a
= lam mat. lam i. lam j. tensorGetExn mat [i, j]

let matSet : Matrix a -> Int -> Int -> a -> ()
= lam mat. lam i. lam j. lam v. tensorSetExn mat [i, j] v

let matOfSeq : (Int, Int) -> [a] -> Matrix a
= lam dim. lam seq.
  match dim with (n, m) then
    tensorOfSeqExn tensorCreateDense [n, m] seq
  else never

let matOfSeqFloat : (Int, Int) -> [Float] -> Matrix Float
= lam dim. lam seq.
  match dim with (n, m) then
    tensorOfSeqExn tensorCreateCArrayFloat [n, m] seq
  else never

let matSize = tensorSize

let matFlatten : Matrix a -> Vector a
= lam mat. tensorReshapeExn mat [tensorSize mat]

let matDim : Matrix a -> (Int, Int)
= lam mat.
  let shape = tensorShape mat in
  (get shape 0, get shape 1)

let matTranspose : Matrix a -> Matrix a
= lam mat. tensorTransposeExn mat 0 1

let matMapi : (Int -> Int -> a -> b -> b) -> Matrix a -> Matrix b -> ()
= lam f. lam mat. tensorMapiExn (lam idx. f (get idx 0) (get idx 1)) mat

let matMap : (a -> b -> b) -> Matrix a -> Matrix b -> () = tensorMapExn

let matIterRow : (Int -> Vector a -> ()) -> Matrix a -> () = tensorIterSlice

let matIsSquareMatrix : Matrix a -> Bool
= lam mat.
  match tensorShape mat with [n, m] then eqi n m else false

let matEq : (a -> b -> Bool) -> Matrix a -> Matrix b -> Bool = tensorEq

let matRow : Matrix a -> Int -> Vector a
= lam mat. lam i. tensorSliceExn mat [i]

let matFoldi : (a -> Int -> Int -> b -> a) -> a -> Matrix b -> a
= lam f. tensorFoldi (lam acc. lam idx. f acc (get idx 0) (get idx 1))
