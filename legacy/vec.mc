include "tensor.mc"

type Vector a = Tensor[a]

let vecCreate : Int -> (Int -> a) -> Vector a
= lam dim. lam f.
  tensorCreateDense [dim] (lam idx. f (head idx))

let vecCreateFloat : Int -> (Int -> a) -> Vector Float
= lam dim. lam f.
  tensorCreateCArrayFloat [dim] (lam idx. f (head idx))

let vecGet : Vector a -> Int -> a
= lam vec. lam i. tensorGetExn vec [i]

let vecSet : Vector a -> Int -> a -> ()
= lam vec. lam i. lam v. tensorSetExn vec [i] v

let vecOfSeq : [a] -> Vector a
= lam seq. tensorOfSeqExn tensorCreateDense [length seq] seq

let vecOfSeqFloat : [Float] -> Vector Float
= lam seq. tensorOfSeqExn tensorCreateCArrayFloat [length seq] seq

let vecToSeq : Vector a -> [a] = tensorToSeqExn

let vecLength : Vector a -> Int = tensorSize

let vecMap : (a -> b -> b) -> Vector a -> Vector b -> () = tensorMapExn

let vecCopy : Vector a -> Vector a = tensorCopy

let vecMax : (a -> a -> Int) -> Vector a -> Option a
= lam cmp. lam vec.
  optionGetOrElse (lam. error "vecMax: Invalid input") (tensorMax cmp vec)

let vecMapi : (Int -> a -> b -> b) -> Vector a -> Vector b -> ()
= lam f. tensorMapiExn (lam idx. f (head idx))

let vecMapiInplace : (Int -> a -> a) -> Vector a -> ()
= lam f. tensorMapiInplace (lam idx. f (head idx))

let vecAll : (a -> Bool) -> Vector a -> Bool = tensorAll

let vecEq : (a -> b -> Bool) -> Vector a -> Vector b -> Bool = tensorEq

let vecFilteri : (Int -> a -> Bool) -> Vector a -> [a]
= lam p. lam vec. map head (tensorFilteri p vec)

let vecFilter = tensorFilter

let vecFoldi : (a -> Int -> b -> a) -> a -> Vector b -> a
= lam f. tensorFoldliSlice (lam acc. lam i. lam t. f acc i (tensorGetExn t []))

let vecFold : (a -> b -> a) -> a -> Vector b -> a = tensorFold

let vecMapCopy : (a -> b) -> Vector a -> Vector b = tensorMapCopy

let vecCumsimiInplace : Vector Int -> Int = tensorCumsumiInplace

let vecSub : Vector a -> Int -> Int -> Vector a = tensorSubExn

let vecIteri : (Int -> a -> ()) -> Vector a -> ()
= lam f. tensorIteri (lam idx. f (head idx))

let vecToString : (a -> String) -> Vector a -> String = tensor2string

let vecBlit : Vector a -> Vector a -> () = tensorBlitExn
