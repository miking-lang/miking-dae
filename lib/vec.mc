include "tensor.mc"

type Vector a = Tensor[a]

let vecCreate : all a. Int -> (Int -> a) -> Vector a = lam dim. lam f.
  tensorCreateDense [dim] (lam idx. f (head idx))

let vecCreateFloat : Int -> (Int -> Float) -> Vector Float = lam dim. lam f.
  tensorCreateCArrayFloat [dim] (lam idx. f (head idx))

let vecGet : all a. Vector a -> Int -> a = tensorLinearGetExn
let vecSet : all a. Vector a -> Int -> a -> () = tensorLinearSetExn

let vecOfSeq : all a. [a] -> Vector a =
  lam seq. tensorOfSeqExn tensorCreateDense [length seq] seq

let vecOfSeqFloat : [Float] -> Vector Float =
  lam seq. tensorOfSeqExn tensorCreateCArrayFloat [length seq] seq

let vecToSeq : all a. Vector a -> [a] = tensorToSeqExn
let vecLength : all a. Vector a -> Int = tensorSize
let vecMap : all a. all b. (a -> b -> b) -> Vector a ->  Vector b -> () = tensorMapExn
let vecCopy : all a. Vector a -> Vector a = tensorCopy

let vecMax : all a. (a -> a -> Int) -> Vector a -> a
= lam cmp. lam vec.
  optionGetOrElse (lam. error "vecMax: Invalid input") (tensorMax cmp vec)

let vecMapi : all a. (Int -> a -> b -> b) -> Vector a -> Vector b -> ()
= lam f. tensorMapiExn (lam idx. f (head idx))

let vecMapiInplace : all a. (Int -> a -> a) -> Vector a -> ()
= lam f. tensorMapiInplace (lam idx. f (head idx))

let vecMapInplace : all a. (a -> a) -> Vector a -> () = tensorMapInplace
let vecAll : all a. (a -> Bool) -> Vector a -> Bool = tensorAll
let vecEq : all a. all b. (a -> b -> Bool) -> Vector a -> Vector b -> Bool = tensorEq
let vecFilteri : all a. (Int -> a -> Bool) -> Vector a -> [Int] =
  lam p. lam vec. map head (tensorFilteri (lam idx. p (head idx)) vec)

let vecFilter : all a. (a -> Bool) -> Vector a -> [a] = tensorFilter

let vecFoldi : all a. all b. (a -> Int -> b -> a) -> a -> Vector b -> a =
  lam f. tensorFoldliSlice (lam acc. lam i. lam t. f acc i (tensorGetExn t []))

let vecFold : all a. all b. (a -> b -> a) -> a -> Vector b -> a = tensorFold
let vecMapCopy : all a. all b. (a -> b) -> Vector a -> Vector b = tensorMapCopy
let vecCumsimiInplace : Vector Int -> () = tensorCumsumiInplace

let vecSub : all a. Vector a -> Int -> Int -> Vector a = tensorSubExn
let vecIteri : all a. (Int -> a -> ()) -> Vector a -> () =
  lam f. tensorIteri (lam idx. f (head idx))

let vecToString : all a. (a -> String) -> Vector a -> String = tensor2string
let vecBlit : all a. Vector a -> Vector a -> () = tensorBlitExn
