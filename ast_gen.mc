include "seq.mc"
include "parser/ll1.mc"
include "parser/breakable.mc"
include "lib/prime-lexer.mc"
lang DAEParseBaseAst
  syn DAEProg =
  syn DAETop =
  syn DAEVar =
  syn DAEEqn =
  syn DAEExpr =
  syn DAEPat =
  syn DAEConst =
  syn DAEType =
  sem smapAccumL_DAEType_DAEType : all a. (a -> DAEType -> (a, DAEType)) -> a -> DAEType -> (a, DAEType)
sem smapAccumL_DAEType_DAEType f acc =
  | x ->
    (acc, x)
  sem smap_DAEType_DAEType : (DAEType -> DAEType) -> DAEType -> DAEType
sem smap_DAEType_DAEType f =
  | x ->
    (smapAccumL_DAEType_DAEType
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEType_DAEType : all a. (a -> DAEType -> a) -> a -> DAEType -> a
sem sfold_DAEType_DAEType f acc =
  | x ->
    (smapAccumL_DAEType_DAEType
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEType_DAEConst : all a. (a -> DAEConst -> (a, DAEConst)) -> a -> DAEType -> (a, DAEType)
sem smapAccumL_DAEType_DAEConst f acc =
  | x ->
    (acc, x)
  sem smap_DAEType_DAEConst : (DAEConst -> DAEConst) -> DAEType -> DAEType
sem smap_DAEType_DAEConst f =
  | x ->
    (smapAccumL_DAEType_DAEConst
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEType_DAEConst : all a. (a -> DAEConst -> a) -> a -> DAEType -> a
sem sfold_DAEType_DAEConst f acc =
  | x ->
    (smapAccumL_DAEType_DAEConst
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEType_DAEPat : all a. (a -> DAEPat -> (a, DAEPat)) -> a -> DAEType -> (a, DAEType)
sem smapAccumL_DAEType_DAEPat f acc =
  | x ->
    (acc, x)
  sem smap_DAEType_DAEPat : (DAEPat -> DAEPat) -> DAEType -> DAEType
sem smap_DAEType_DAEPat f =
  | x ->
    (smapAccumL_DAEType_DAEPat
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEType_DAEPat : all a. (a -> DAEPat -> a) -> a -> DAEType -> a
sem sfold_DAEType_DAEPat f acc =
  | x ->
    (smapAccumL_DAEType_DAEPat
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEType_DAEExpr : all a. (a -> DAEExpr -> (a, DAEExpr)) -> a -> DAEType -> (a, DAEType)
sem smapAccumL_DAEType_DAEExpr f acc =
  | x ->
    (acc, x)
  sem smap_DAEType_DAEExpr : (DAEExpr -> DAEExpr) -> DAEType -> DAEType
sem smap_DAEType_DAEExpr f =
  | x ->
    (smapAccumL_DAEType_DAEExpr
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEType_DAEExpr : all a. (a -> DAEExpr -> a) -> a -> DAEType -> a
sem sfold_DAEType_DAEExpr f acc =
  | x ->
    (smapAccumL_DAEType_DAEExpr
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEType_DAEEqn : all a. (a -> DAEEqn -> (a, DAEEqn)) -> a -> DAEType -> (a, DAEType)
sem smapAccumL_DAEType_DAEEqn f acc =
  | x ->
    (acc, x)
  sem smap_DAEType_DAEEqn : (DAEEqn -> DAEEqn) -> DAEType -> DAEType
sem smap_DAEType_DAEEqn f =
  | x ->
    (smapAccumL_DAEType_DAEEqn
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEType_DAEEqn : all a. (a -> DAEEqn -> a) -> a -> DAEType -> a
sem sfold_DAEType_DAEEqn f acc =
  | x ->
    (smapAccumL_DAEType_DAEEqn
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEType_DAEVar : all a. (a -> DAEVar -> (a, DAEVar)) -> a -> DAEType -> (a, DAEType)
sem smapAccumL_DAEType_DAEVar f acc =
  | x ->
    (acc, x)
  sem smap_DAEType_DAEVar : (DAEVar -> DAEVar) -> DAEType -> DAEType
sem smap_DAEType_DAEVar f =
  | x ->
    (smapAccumL_DAEType_DAEVar
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEType_DAEVar : all a. (a -> DAEVar -> a) -> a -> DAEType -> a
sem sfold_DAEType_DAEVar f acc =
  | x ->
    (smapAccumL_DAEType_DAEVar
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEType_DAETop : all a. (a -> DAETop -> (a, DAETop)) -> a -> DAEType -> (a, DAEType)
sem smapAccumL_DAEType_DAETop f acc =
  | x ->
    (acc, x)
  sem smap_DAEType_DAETop : (DAETop -> DAETop) -> DAEType -> DAEType
sem smap_DAEType_DAETop f =
  | x ->
    (smapAccumL_DAEType_DAETop
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEType_DAETop : all a. (a -> DAETop -> a) -> a -> DAEType -> a
sem sfold_DAEType_DAETop f acc =
  | x ->
    (smapAccumL_DAEType_DAETop
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEType_DAEProg : all a. (a -> DAEProg -> (a, DAEProg)) -> a -> DAEType -> (a, DAEType)
sem smapAccumL_DAEType_DAEProg f acc =
  | x ->
    (acc, x)
  sem smap_DAEType_DAEProg : (DAEProg -> DAEProg) -> DAEType -> DAEType
sem smap_DAEType_DAEProg f =
  | x ->
    (smapAccumL_DAEType_DAEProg
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEType_DAEProg : all a. (a -> DAEProg -> a) -> a -> DAEType -> a
sem sfold_DAEType_DAEProg f acc =
  | x ->
    (smapAccumL_DAEType_DAEProg
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEConst_DAEType : all a. (a -> DAEType -> (a, DAEType)) -> a -> DAEConst -> (a, DAEConst)
sem smapAccumL_DAEConst_DAEType f acc =
  | x ->
    (acc, x)
  sem smap_DAEConst_DAEType : (DAEType -> DAEType) -> DAEConst -> DAEConst
sem smap_DAEConst_DAEType f =
  | x ->
    (smapAccumL_DAEConst_DAEType
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEConst_DAEType : all a. (a -> DAEType -> a) -> a -> DAEConst -> a
sem sfold_DAEConst_DAEType f acc =
  | x ->
    (smapAccumL_DAEConst_DAEType
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEConst_DAEConst : all a. (a -> DAEConst -> (a, DAEConst)) -> a -> DAEConst -> (a, DAEConst)
sem smapAccumL_DAEConst_DAEConst f acc =
  | x ->
    (acc, x)
  sem smap_DAEConst_DAEConst : (DAEConst -> DAEConst) -> DAEConst -> DAEConst
sem smap_DAEConst_DAEConst f =
  | x ->
    (smapAccumL_DAEConst_DAEConst
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEConst_DAEConst : all a. (a -> DAEConst -> a) -> a -> DAEConst -> a
sem sfold_DAEConst_DAEConst f acc =
  | x ->
    (smapAccumL_DAEConst_DAEConst
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEConst_DAEPat : all a. (a -> DAEPat -> (a, DAEPat)) -> a -> DAEConst -> (a, DAEConst)
sem smapAccumL_DAEConst_DAEPat f acc =
  | x ->
    (acc, x)
  sem smap_DAEConst_DAEPat : (DAEPat -> DAEPat) -> DAEConst -> DAEConst
sem smap_DAEConst_DAEPat f =
  | x ->
    (smapAccumL_DAEConst_DAEPat
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEConst_DAEPat : all a. (a -> DAEPat -> a) -> a -> DAEConst -> a
sem sfold_DAEConst_DAEPat f acc =
  | x ->
    (smapAccumL_DAEConst_DAEPat
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEConst_DAEExpr : all a. (a -> DAEExpr -> (a, DAEExpr)) -> a -> DAEConst -> (a, DAEConst)
sem smapAccumL_DAEConst_DAEExpr f acc =
  | x ->
    (acc, x)
  sem smap_DAEConst_DAEExpr : (DAEExpr -> DAEExpr) -> DAEConst -> DAEConst
sem smap_DAEConst_DAEExpr f =
  | x ->
    (smapAccumL_DAEConst_DAEExpr
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEConst_DAEExpr : all a. (a -> DAEExpr -> a) -> a -> DAEConst -> a
sem sfold_DAEConst_DAEExpr f acc =
  | x ->
    (smapAccumL_DAEConst_DAEExpr
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEConst_DAEEqn : all a. (a -> DAEEqn -> (a, DAEEqn)) -> a -> DAEConst -> (a, DAEConst)
sem smapAccumL_DAEConst_DAEEqn f acc =
  | x ->
    (acc, x)
  sem smap_DAEConst_DAEEqn : (DAEEqn -> DAEEqn) -> DAEConst -> DAEConst
sem smap_DAEConst_DAEEqn f =
  | x ->
    (smapAccumL_DAEConst_DAEEqn
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEConst_DAEEqn : all a. (a -> DAEEqn -> a) -> a -> DAEConst -> a
sem sfold_DAEConst_DAEEqn f acc =
  | x ->
    (smapAccumL_DAEConst_DAEEqn
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEConst_DAEVar : all a. (a -> DAEVar -> (a, DAEVar)) -> a -> DAEConst -> (a, DAEConst)
sem smapAccumL_DAEConst_DAEVar f acc =
  | x ->
    (acc, x)
  sem smap_DAEConst_DAEVar : (DAEVar -> DAEVar) -> DAEConst -> DAEConst
sem smap_DAEConst_DAEVar f =
  | x ->
    (smapAccumL_DAEConst_DAEVar
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEConst_DAEVar : all a. (a -> DAEVar -> a) -> a -> DAEConst -> a
sem sfold_DAEConst_DAEVar f acc =
  | x ->
    (smapAccumL_DAEConst_DAEVar
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEConst_DAETop : all a. (a -> DAETop -> (a, DAETop)) -> a -> DAEConst -> (a, DAEConst)
sem smapAccumL_DAEConst_DAETop f acc =
  | x ->
    (acc, x)
  sem smap_DAEConst_DAETop : (DAETop -> DAETop) -> DAEConst -> DAEConst
sem smap_DAEConst_DAETop f =
  | x ->
    (smapAccumL_DAEConst_DAETop
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEConst_DAETop : all a. (a -> DAETop -> a) -> a -> DAEConst -> a
sem sfold_DAEConst_DAETop f acc =
  | x ->
    (smapAccumL_DAEConst_DAETop
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEConst_DAEProg : all a. (a -> DAEProg -> (a, DAEProg)) -> a -> DAEConst -> (a, DAEConst)
sem smapAccumL_DAEConst_DAEProg f acc =
  | x ->
    (acc, x)
  sem smap_DAEConst_DAEProg : (DAEProg -> DAEProg) -> DAEConst -> DAEConst
sem smap_DAEConst_DAEProg f =
  | x ->
    (smapAccumL_DAEConst_DAEProg
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEConst_DAEProg : all a. (a -> DAEProg -> a) -> a -> DAEConst -> a
sem sfold_DAEConst_DAEProg f acc =
  | x ->
    (smapAccumL_DAEConst_DAEProg
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEPat_DAEType : all a. (a -> DAEType -> (a, DAEType)) -> a -> DAEPat -> (a, DAEPat)
sem smapAccumL_DAEPat_DAEType f acc =
  | x ->
    (acc, x)
  sem smap_DAEPat_DAEType : (DAEType -> DAEType) -> DAEPat -> DAEPat
sem smap_DAEPat_DAEType f =
  | x ->
    (smapAccumL_DAEPat_DAEType
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEPat_DAEType : all a. (a -> DAEType -> a) -> a -> DAEPat -> a
sem sfold_DAEPat_DAEType f acc =
  | x ->
    (smapAccumL_DAEPat_DAEType
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEPat_DAEConst : all a. (a -> DAEConst -> (a, DAEConst)) -> a -> DAEPat -> (a, DAEPat)
sem smapAccumL_DAEPat_DAEConst f acc =
  | x ->
    (acc, x)
  sem smap_DAEPat_DAEConst : (DAEConst -> DAEConst) -> DAEPat -> DAEPat
sem smap_DAEPat_DAEConst f =
  | x ->
    (smapAccumL_DAEPat_DAEConst
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEPat_DAEConst : all a. (a -> DAEConst -> a) -> a -> DAEPat -> a
sem sfold_DAEPat_DAEConst f acc =
  | x ->
    (smapAccumL_DAEPat_DAEConst
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEPat_DAEPat : all a. (a -> DAEPat -> (a, DAEPat)) -> a -> DAEPat -> (a, DAEPat)
sem smapAccumL_DAEPat_DAEPat f acc =
  | x ->
    (acc, x)
  sem smap_DAEPat_DAEPat : (DAEPat -> DAEPat) -> DAEPat -> DAEPat
sem smap_DAEPat_DAEPat f =
  | x ->
    (smapAccumL_DAEPat_DAEPat
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEPat_DAEPat : all a. (a -> DAEPat -> a) -> a -> DAEPat -> a
sem sfold_DAEPat_DAEPat f acc =
  | x ->
    (smapAccumL_DAEPat_DAEPat
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEPat_DAEExpr : all a. (a -> DAEExpr -> (a, DAEExpr)) -> a -> DAEPat -> (a, DAEPat)
sem smapAccumL_DAEPat_DAEExpr f acc =
  | x ->
    (acc, x)
  sem smap_DAEPat_DAEExpr : (DAEExpr -> DAEExpr) -> DAEPat -> DAEPat
sem smap_DAEPat_DAEExpr f =
  | x ->
    (smapAccumL_DAEPat_DAEExpr
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEPat_DAEExpr : all a. (a -> DAEExpr -> a) -> a -> DAEPat -> a
sem sfold_DAEPat_DAEExpr f acc =
  | x ->
    (smapAccumL_DAEPat_DAEExpr
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEPat_DAEEqn : all a. (a -> DAEEqn -> (a, DAEEqn)) -> a -> DAEPat -> (a, DAEPat)
sem smapAccumL_DAEPat_DAEEqn f acc =
  | x ->
    (acc, x)
  sem smap_DAEPat_DAEEqn : (DAEEqn -> DAEEqn) -> DAEPat -> DAEPat
sem smap_DAEPat_DAEEqn f =
  | x ->
    (smapAccumL_DAEPat_DAEEqn
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEPat_DAEEqn : all a. (a -> DAEEqn -> a) -> a -> DAEPat -> a
sem sfold_DAEPat_DAEEqn f acc =
  | x ->
    (smapAccumL_DAEPat_DAEEqn
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEPat_DAEVar : all a. (a -> DAEVar -> (a, DAEVar)) -> a -> DAEPat -> (a, DAEPat)
sem smapAccumL_DAEPat_DAEVar f acc =
  | x ->
    (acc, x)
  sem smap_DAEPat_DAEVar : (DAEVar -> DAEVar) -> DAEPat -> DAEPat
sem smap_DAEPat_DAEVar f =
  | x ->
    (smapAccumL_DAEPat_DAEVar
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEPat_DAEVar : all a. (a -> DAEVar -> a) -> a -> DAEPat -> a
sem sfold_DAEPat_DAEVar f acc =
  | x ->
    (smapAccumL_DAEPat_DAEVar
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEPat_DAETop : all a. (a -> DAETop -> (a, DAETop)) -> a -> DAEPat -> (a, DAEPat)
sem smapAccumL_DAEPat_DAETop f acc =
  | x ->
    (acc, x)
  sem smap_DAEPat_DAETop : (DAETop -> DAETop) -> DAEPat -> DAEPat
sem smap_DAEPat_DAETop f =
  | x ->
    (smapAccumL_DAEPat_DAETop
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEPat_DAETop : all a. (a -> DAETop -> a) -> a -> DAEPat -> a
sem sfold_DAEPat_DAETop f acc =
  | x ->
    (smapAccumL_DAEPat_DAETop
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEPat_DAEProg : all a. (a -> DAEProg -> (a, DAEProg)) -> a -> DAEPat -> (a, DAEPat)
sem smapAccumL_DAEPat_DAEProg f acc =
  | x ->
    (acc, x)
  sem smap_DAEPat_DAEProg : (DAEProg -> DAEProg) -> DAEPat -> DAEPat
sem smap_DAEPat_DAEProg f =
  | x ->
    (smapAccumL_DAEPat_DAEProg
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEPat_DAEProg : all a. (a -> DAEProg -> a) -> a -> DAEPat -> a
sem sfold_DAEPat_DAEProg f acc =
  | x ->
    (smapAccumL_DAEPat_DAEProg
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEExpr_DAEType : all a. (a -> DAEType -> (a, DAEType)) -> a -> DAEExpr -> (a, DAEExpr)
sem smapAccumL_DAEExpr_DAEType f acc =
  | x ->
    (acc, x)
  sem smap_DAEExpr_DAEType : (DAEType -> DAEType) -> DAEExpr -> DAEExpr
sem smap_DAEExpr_DAEType f =
  | x ->
    (smapAccumL_DAEExpr_DAEType
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEExpr_DAEType : all a. (a -> DAEType -> a) -> a -> DAEExpr -> a
sem sfold_DAEExpr_DAEType f acc =
  | x ->
    (smapAccumL_DAEExpr_DAEType
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEExpr_DAEConst : all a. (a -> DAEConst -> (a, DAEConst)) -> a -> DAEExpr -> (a, DAEExpr)
sem smapAccumL_DAEExpr_DAEConst f acc =
  | x ->
    (acc, x)
  sem smap_DAEExpr_DAEConst : (DAEConst -> DAEConst) -> DAEExpr -> DAEExpr
sem smap_DAEExpr_DAEConst f =
  | x ->
    (smapAccumL_DAEExpr_DAEConst
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEExpr_DAEConst : all a. (a -> DAEConst -> a) -> a -> DAEExpr -> a
sem sfold_DAEExpr_DAEConst f acc =
  | x ->
    (smapAccumL_DAEExpr_DAEConst
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEExpr_DAEPat : all a. (a -> DAEPat -> (a, DAEPat)) -> a -> DAEExpr -> (a, DAEExpr)
sem smapAccumL_DAEExpr_DAEPat f acc =
  | x ->
    (acc, x)
  sem smap_DAEExpr_DAEPat : (DAEPat -> DAEPat) -> DAEExpr -> DAEExpr
sem smap_DAEExpr_DAEPat f =
  | x ->
    (smapAccumL_DAEExpr_DAEPat
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEExpr_DAEPat : all a. (a -> DAEPat -> a) -> a -> DAEExpr -> a
sem sfold_DAEExpr_DAEPat f acc =
  | x ->
    (smapAccumL_DAEExpr_DAEPat
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEExpr_DAEExpr : all a. (a -> DAEExpr -> (a, DAEExpr)) -> a -> DAEExpr -> (a, DAEExpr)
sem smapAccumL_DAEExpr_DAEExpr f acc =
  | x ->
    (acc, x)
  sem smap_DAEExpr_DAEExpr : (DAEExpr -> DAEExpr) -> DAEExpr -> DAEExpr
sem smap_DAEExpr_DAEExpr f =
  | x ->
    (smapAccumL_DAEExpr_DAEExpr
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEExpr_DAEExpr : all a. (a -> DAEExpr -> a) -> a -> DAEExpr -> a
sem sfold_DAEExpr_DAEExpr f acc =
  | x ->
    (smapAccumL_DAEExpr_DAEExpr
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEExpr_DAEEqn : all a. (a -> DAEEqn -> (a, DAEEqn)) -> a -> DAEExpr -> (a, DAEExpr)
sem smapAccumL_DAEExpr_DAEEqn f acc =
  | x ->
    (acc, x)
  sem smap_DAEExpr_DAEEqn : (DAEEqn -> DAEEqn) -> DAEExpr -> DAEExpr
sem smap_DAEExpr_DAEEqn f =
  | x ->
    (smapAccumL_DAEExpr_DAEEqn
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEExpr_DAEEqn : all a. (a -> DAEEqn -> a) -> a -> DAEExpr -> a
sem sfold_DAEExpr_DAEEqn f acc =
  | x ->
    (smapAccumL_DAEExpr_DAEEqn
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEExpr_DAEVar : all a. (a -> DAEVar -> (a, DAEVar)) -> a -> DAEExpr -> (a, DAEExpr)
sem smapAccumL_DAEExpr_DAEVar f acc =
  | x ->
    (acc, x)
  sem smap_DAEExpr_DAEVar : (DAEVar -> DAEVar) -> DAEExpr -> DAEExpr
sem smap_DAEExpr_DAEVar f =
  | x ->
    (smapAccumL_DAEExpr_DAEVar
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEExpr_DAEVar : all a. (a -> DAEVar -> a) -> a -> DAEExpr -> a
sem sfold_DAEExpr_DAEVar f acc =
  | x ->
    (smapAccumL_DAEExpr_DAEVar
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEExpr_DAETop : all a. (a -> DAETop -> (a, DAETop)) -> a -> DAEExpr -> (a, DAEExpr)
sem smapAccumL_DAEExpr_DAETop f acc =
  | x ->
    (acc, x)
  sem smap_DAEExpr_DAETop : (DAETop -> DAETop) -> DAEExpr -> DAEExpr
sem smap_DAEExpr_DAETop f =
  | x ->
    (smapAccumL_DAEExpr_DAETop
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEExpr_DAETop : all a. (a -> DAETop -> a) -> a -> DAEExpr -> a
sem sfold_DAEExpr_DAETop f acc =
  | x ->
    (smapAccumL_DAEExpr_DAETop
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEExpr_DAEProg : all a. (a -> DAEProg -> (a, DAEProg)) -> a -> DAEExpr -> (a, DAEExpr)
sem smapAccumL_DAEExpr_DAEProg f acc =
  | x ->
    (acc, x)
  sem smap_DAEExpr_DAEProg : (DAEProg -> DAEProg) -> DAEExpr -> DAEExpr
sem smap_DAEExpr_DAEProg f =
  | x ->
    (smapAccumL_DAEExpr_DAEProg
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEExpr_DAEProg : all a. (a -> DAEProg -> a) -> a -> DAEExpr -> a
sem sfold_DAEExpr_DAEProg f acc =
  | x ->
    (smapAccumL_DAEExpr_DAEProg
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEEqn_DAEType : all a. (a -> DAEType -> (a, DAEType)) -> a -> DAEEqn -> (a, DAEEqn)
sem smapAccumL_DAEEqn_DAEType f acc =
  | x ->
    (acc, x)
  sem smap_DAEEqn_DAEType : (DAEType -> DAEType) -> DAEEqn -> DAEEqn
sem smap_DAEEqn_DAEType f =
  | x ->
    (smapAccumL_DAEEqn_DAEType
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEEqn_DAEType : all a. (a -> DAEType -> a) -> a -> DAEEqn -> a
sem sfold_DAEEqn_DAEType f acc =
  | x ->
    (smapAccumL_DAEEqn_DAEType
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEEqn_DAEConst : all a. (a -> DAEConst -> (a, DAEConst)) -> a -> DAEEqn -> (a, DAEEqn)
sem smapAccumL_DAEEqn_DAEConst f acc =
  | x ->
    (acc, x)
  sem smap_DAEEqn_DAEConst : (DAEConst -> DAEConst) -> DAEEqn -> DAEEqn
sem smap_DAEEqn_DAEConst f =
  | x ->
    (smapAccumL_DAEEqn_DAEConst
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEEqn_DAEConst : all a. (a -> DAEConst -> a) -> a -> DAEEqn -> a
sem sfold_DAEEqn_DAEConst f acc =
  | x ->
    (smapAccumL_DAEEqn_DAEConst
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEEqn_DAEPat : all a. (a -> DAEPat -> (a, DAEPat)) -> a -> DAEEqn -> (a, DAEEqn)
sem smapAccumL_DAEEqn_DAEPat f acc =
  | x ->
    (acc, x)
  sem smap_DAEEqn_DAEPat : (DAEPat -> DAEPat) -> DAEEqn -> DAEEqn
sem smap_DAEEqn_DAEPat f =
  | x ->
    (smapAccumL_DAEEqn_DAEPat
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEEqn_DAEPat : all a. (a -> DAEPat -> a) -> a -> DAEEqn -> a
sem sfold_DAEEqn_DAEPat f acc =
  | x ->
    (smapAccumL_DAEEqn_DAEPat
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEEqn_DAEExpr : all a. (a -> DAEExpr -> (a, DAEExpr)) -> a -> DAEEqn -> (a, DAEEqn)
sem smapAccumL_DAEEqn_DAEExpr f acc =
  | x ->
    (acc, x)
  sem smap_DAEEqn_DAEExpr : (DAEExpr -> DAEExpr) -> DAEEqn -> DAEEqn
sem smap_DAEEqn_DAEExpr f =
  | x ->
    (smapAccumL_DAEEqn_DAEExpr
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEEqn_DAEExpr : all a. (a -> DAEExpr -> a) -> a -> DAEEqn -> a
sem sfold_DAEEqn_DAEExpr f acc =
  | x ->
    (smapAccumL_DAEEqn_DAEExpr
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEEqn_DAEEqn : all a. (a -> DAEEqn -> (a, DAEEqn)) -> a -> DAEEqn -> (a, DAEEqn)
sem smapAccumL_DAEEqn_DAEEqn f acc =
  | x ->
    (acc, x)
  sem smap_DAEEqn_DAEEqn : (DAEEqn -> DAEEqn) -> DAEEqn -> DAEEqn
sem smap_DAEEqn_DAEEqn f =
  | x ->
    (smapAccumL_DAEEqn_DAEEqn
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEEqn_DAEEqn : all a. (a -> DAEEqn -> a) -> a -> DAEEqn -> a
sem sfold_DAEEqn_DAEEqn f acc =
  | x ->
    (smapAccumL_DAEEqn_DAEEqn
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEEqn_DAEVar : all a. (a -> DAEVar -> (a, DAEVar)) -> a -> DAEEqn -> (a, DAEEqn)
sem smapAccumL_DAEEqn_DAEVar f acc =
  | x ->
    (acc, x)
  sem smap_DAEEqn_DAEVar : (DAEVar -> DAEVar) -> DAEEqn -> DAEEqn
sem smap_DAEEqn_DAEVar f =
  | x ->
    (smapAccumL_DAEEqn_DAEVar
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEEqn_DAEVar : all a. (a -> DAEVar -> a) -> a -> DAEEqn -> a
sem sfold_DAEEqn_DAEVar f acc =
  | x ->
    (smapAccumL_DAEEqn_DAEVar
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEEqn_DAETop : all a. (a -> DAETop -> (a, DAETop)) -> a -> DAEEqn -> (a, DAEEqn)
sem smapAccumL_DAEEqn_DAETop f acc =
  | x ->
    (acc, x)
  sem smap_DAEEqn_DAETop : (DAETop -> DAETop) -> DAEEqn -> DAEEqn
sem smap_DAEEqn_DAETop f =
  | x ->
    (smapAccumL_DAEEqn_DAETop
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEEqn_DAETop : all a. (a -> DAETop -> a) -> a -> DAEEqn -> a
sem sfold_DAEEqn_DAETop f acc =
  | x ->
    (smapAccumL_DAEEqn_DAETop
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEEqn_DAEProg : all a. (a -> DAEProg -> (a, DAEProg)) -> a -> DAEEqn -> (a, DAEEqn)
sem smapAccumL_DAEEqn_DAEProg f acc =
  | x ->
    (acc, x)
  sem smap_DAEEqn_DAEProg : (DAEProg -> DAEProg) -> DAEEqn -> DAEEqn
sem smap_DAEEqn_DAEProg f =
  | x ->
    (smapAccumL_DAEEqn_DAEProg
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEEqn_DAEProg : all a. (a -> DAEProg -> a) -> a -> DAEEqn -> a
sem sfold_DAEEqn_DAEProg f acc =
  | x ->
    (smapAccumL_DAEEqn_DAEProg
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEVar_DAEType : all a. (a -> DAEType -> (a, DAEType)) -> a -> DAEVar -> (a, DAEVar)
sem smapAccumL_DAEVar_DAEType f acc =
  | x ->
    (acc, x)
  sem smap_DAEVar_DAEType : (DAEType -> DAEType) -> DAEVar -> DAEVar
sem smap_DAEVar_DAEType f =
  | x ->
    (smapAccumL_DAEVar_DAEType
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEVar_DAEType : all a. (a -> DAEType -> a) -> a -> DAEVar -> a
sem sfold_DAEVar_DAEType f acc =
  | x ->
    (smapAccumL_DAEVar_DAEType
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEVar_DAEConst : all a. (a -> DAEConst -> (a, DAEConst)) -> a -> DAEVar -> (a, DAEVar)
sem smapAccumL_DAEVar_DAEConst f acc =
  | x ->
    (acc, x)
  sem smap_DAEVar_DAEConst : (DAEConst -> DAEConst) -> DAEVar -> DAEVar
sem smap_DAEVar_DAEConst f =
  | x ->
    (smapAccumL_DAEVar_DAEConst
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEVar_DAEConst : all a. (a -> DAEConst -> a) -> a -> DAEVar -> a
sem sfold_DAEVar_DAEConst f acc =
  | x ->
    (smapAccumL_DAEVar_DAEConst
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEVar_DAEPat : all a. (a -> DAEPat -> (a, DAEPat)) -> a -> DAEVar -> (a, DAEVar)
sem smapAccumL_DAEVar_DAEPat f acc =
  | x ->
    (acc, x)
  sem smap_DAEVar_DAEPat : (DAEPat -> DAEPat) -> DAEVar -> DAEVar
sem smap_DAEVar_DAEPat f =
  | x ->
    (smapAccumL_DAEVar_DAEPat
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEVar_DAEPat : all a. (a -> DAEPat -> a) -> a -> DAEVar -> a
sem sfold_DAEVar_DAEPat f acc =
  | x ->
    (smapAccumL_DAEVar_DAEPat
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEVar_DAEExpr : all a. (a -> DAEExpr -> (a, DAEExpr)) -> a -> DAEVar -> (a, DAEVar)
sem smapAccumL_DAEVar_DAEExpr f acc =
  | x ->
    (acc, x)
  sem smap_DAEVar_DAEExpr : (DAEExpr -> DAEExpr) -> DAEVar -> DAEVar
sem smap_DAEVar_DAEExpr f =
  | x ->
    (smapAccumL_DAEVar_DAEExpr
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEVar_DAEExpr : all a. (a -> DAEExpr -> a) -> a -> DAEVar -> a
sem sfold_DAEVar_DAEExpr f acc =
  | x ->
    (smapAccumL_DAEVar_DAEExpr
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEVar_DAEEqn : all a. (a -> DAEEqn -> (a, DAEEqn)) -> a -> DAEVar -> (a, DAEVar)
sem smapAccumL_DAEVar_DAEEqn f acc =
  | x ->
    (acc, x)
  sem smap_DAEVar_DAEEqn : (DAEEqn -> DAEEqn) -> DAEVar -> DAEVar
sem smap_DAEVar_DAEEqn f =
  | x ->
    (smapAccumL_DAEVar_DAEEqn
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEVar_DAEEqn : all a. (a -> DAEEqn -> a) -> a -> DAEVar -> a
sem sfold_DAEVar_DAEEqn f acc =
  | x ->
    (smapAccumL_DAEVar_DAEEqn
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEVar_DAEVar : all a. (a -> DAEVar -> (a, DAEVar)) -> a -> DAEVar -> (a, DAEVar)
sem smapAccumL_DAEVar_DAEVar f acc =
  | x ->
    (acc, x)
  sem smap_DAEVar_DAEVar : (DAEVar -> DAEVar) -> DAEVar -> DAEVar
sem smap_DAEVar_DAEVar f =
  | x ->
    (smapAccumL_DAEVar_DAEVar
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEVar_DAEVar : all a. (a -> DAEVar -> a) -> a -> DAEVar -> a
sem sfold_DAEVar_DAEVar f acc =
  | x ->
    (smapAccumL_DAEVar_DAEVar
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEVar_DAETop : all a. (a -> DAETop -> (a, DAETop)) -> a -> DAEVar -> (a, DAEVar)
sem smapAccumL_DAEVar_DAETop f acc =
  | x ->
    (acc, x)
  sem smap_DAEVar_DAETop : (DAETop -> DAETop) -> DAEVar -> DAEVar
sem smap_DAEVar_DAETop f =
  | x ->
    (smapAccumL_DAEVar_DAETop
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEVar_DAETop : all a. (a -> DAETop -> a) -> a -> DAEVar -> a
sem sfold_DAEVar_DAETop f acc =
  | x ->
    (smapAccumL_DAEVar_DAETop
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEVar_DAEProg : all a. (a -> DAEProg -> (a, DAEProg)) -> a -> DAEVar -> (a, DAEVar)
sem smapAccumL_DAEVar_DAEProg f acc =
  | x ->
    (acc, x)
  sem smap_DAEVar_DAEProg : (DAEProg -> DAEProg) -> DAEVar -> DAEVar
sem smap_DAEVar_DAEProg f =
  | x ->
    (smapAccumL_DAEVar_DAEProg
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEVar_DAEProg : all a. (a -> DAEProg -> a) -> a -> DAEVar -> a
sem sfold_DAEVar_DAEProg f acc =
  | x ->
    (smapAccumL_DAEVar_DAEProg
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAETop_DAEType : all a. (a -> DAEType -> (a, DAEType)) -> a -> DAETop -> (a, DAETop)
sem smapAccumL_DAETop_DAEType f acc =
  | x ->
    (acc, x)
  sem smap_DAETop_DAEType : (DAEType -> DAEType) -> DAETop -> DAETop
sem smap_DAETop_DAEType f =
  | x ->
    (smapAccumL_DAETop_DAEType
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAETop_DAEType : all a. (a -> DAEType -> a) -> a -> DAETop -> a
sem sfold_DAETop_DAEType f acc =
  | x ->
    (smapAccumL_DAETop_DAEType
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAETop_DAEConst : all a. (a -> DAEConst -> (a, DAEConst)) -> a -> DAETop -> (a, DAETop)
sem smapAccumL_DAETop_DAEConst f acc =
  | x ->
    (acc, x)
  sem smap_DAETop_DAEConst : (DAEConst -> DAEConst) -> DAETop -> DAETop
sem smap_DAETop_DAEConst f =
  | x ->
    (smapAccumL_DAETop_DAEConst
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAETop_DAEConst : all a. (a -> DAEConst -> a) -> a -> DAETop -> a
sem sfold_DAETop_DAEConst f acc =
  | x ->
    (smapAccumL_DAETop_DAEConst
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAETop_DAEPat : all a. (a -> DAEPat -> (a, DAEPat)) -> a -> DAETop -> (a, DAETop)
sem smapAccumL_DAETop_DAEPat f acc =
  | x ->
    (acc, x)
  sem smap_DAETop_DAEPat : (DAEPat -> DAEPat) -> DAETop -> DAETop
sem smap_DAETop_DAEPat f =
  | x ->
    (smapAccumL_DAETop_DAEPat
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAETop_DAEPat : all a. (a -> DAEPat -> a) -> a -> DAETop -> a
sem sfold_DAETop_DAEPat f acc =
  | x ->
    (smapAccumL_DAETop_DAEPat
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAETop_DAEExpr : all a. (a -> DAEExpr -> (a, DAEExpr)) -> a -> DAETop -> (a, DAETop)
sem smapAccumL_DAETop_DAEExpr f acc =
  | x ->
    (acc, x)
  sem smap_DAETop_DAEExpr : (DAEExpr -> DAEExpr) -> DAETop -> DAETop
sem smap_DAETop_DAEExpr f =
  | x ->
    (smapAccumL_DAETop_DAEExpr
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAETop_DAEExpr : all a. (a -> DAEExpr -> a) -> a -> DAETop -> a
sem sfold_DAETop_DAEExpr f acc =
  | x ->
    (smapAccumL_DAETop_DAEExpr
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAETop_DAEEqn : all a. (a -> DAEEqn -> (a, DAEEqn)) -> a -> DAETop -> (a, DAETop)
sem smapAccumL_DAETop_DAEEqn f acc =
  | x ->
    (acc, x)
  sem smap_DAETop_DAEEqn : (DAEEqn -> DAEEqn) -> DAETop -> DAETop
sem smap_DAETop_DAEEqn f =
  | x ->
    (smapAccumL_DAETop_DAEEqn
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAETop_DAEEqn : all a. (a -> DAEEqn -> a) -> a -> DAETop -> a
sem sfold_DAETop_DAEEqn f acc =
  | x ->
    (smapAccumL_DAETop_DAEEqn
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAETop_DAEVar : all a. (a -> DAEVar -> (a, DAEVar)) -> a -> DAETop -> (a, DAETop)
sem smapAccumL_DAETop_DAEVar f acc =
  | x ->
    (acc, x)
  sem smap_DAETop_DAEVar : (DAEVar -> DAEVar) -> DAETop -> DAETop
sem smap_DAETop_DAEVar f =
  | x ->
    (smapAccumL_DAETop_DAEVar
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAETop_DAEVar : all a. (a -> DAEVar -> a) -> a -> DAETop -> a
sem sfold_DAETop_DAEVar f acc =
  | x ->
    (smapAccumL_DAETop_DAEVar
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAETop_DAETop : all a. (a -> DAETop -> (a, DAETop)) -> a -> DAETop -> (a, DAETop)
sem smapAccumL_DAETop_DAETop f acc =
  | x ->
    (acc, x)
  sem smap_DAETop_DAETop : (DAETop -> DAETop) -> DAETop -> DAETop
sem smap_DAETop_DAETop f =
  | x ->
    (smapAccumL_DAETop_DAETop
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAETop_DAETop : all a. (a -> DAETop -> a) -> a -> DAETop -> a
sem sfold_DAETop_DAETop f acc =
  | x ->
    (smapAccumL_DAETop_DAETop
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAETop_DAEProg : all a. (a -> DAEProg -> (a, DAEProg)) -> a -> DAETop -> (a, DAETop)
sem smapAccumL_DAETop_DAEProg f acc =
  | x ->
    (acc, x)
  sem smap_DAETop_DAEProg : (DAEProg -> DAEProg) -> DAETop -> DAETop
sem smap_DAETop_DAEProg f =
  | x ->
    (smapAccumL_DAETop_DAEProg
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAETop_DAEProg : all a. (a -> DAEProg -> a) -> a -> DAETop -> a
sem sfold_DAETop_DAEProg f acc =
  | x ->
    (smapAccumL_DAETop_DAEProg
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEProg_DAEType : all a. (a -> DAEType -> (a, DAEType)) -> a -> DAEProg -> (a, DAEProg)
sem smapAccumL_DAEProg_DAEType f acc =
  | x ->
    (acc, x)
  sem smap_DAEProg_DAEType : (DAEType -> DAEType) -> DAEProg -> DAEProg
sem smap_DAEProg_DAEType f =
  | x ->
    (smapAccumL_DAEProg_DAEType
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEProg_DAEType : all a. (a -> DAEType -> a) -> a -> DAEProg -> a
sem sfold_DAEProg_DAEType f acc =
  | x ->
    (smapAccumL_DAEProg_DAEType
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEProg_DAEConst : all a. (a -> DAEConst -> (a, DAEConst)) -> a -> DAEProg -> (a, DAEProg)
sem smapAccumL_DAEProg_DAEConst f acc =
  | x ->
    (acc, x)
  sem smap_DAEProg_DAEConst : (DAEConst -> DAEConst) -> DAEProg -> DAEProg
sem smap_DAEProg_DAEConst f =
  | x ->
    (smapAccumL_DAEProg_DAEConst
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEProg_DAEConst : all a. (a -> DAEConst -> a) -> a -> DAEProg -> a
sem sfold_DAEProg_DAEConst f acc =
  | x ->
    (smapAccumL_DAEProg_DAEConst
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEProg_DAEPat : all a. (a -> DAEPat -> (a, DAEPat)) -> a -> DAEProg -> (a, DAEProg)
sem smapAccumL_DAEProg_DAEPat f acc =
  | x ->
    (acc, x)
  sem smap_DAEProg_DAEPat : (DAEPat -> DAEPat) -> DAEProg -> DAEProg
sem smap_DAEProg_DAEPat f =
  | x ->
    (smapAccumL_DAEProg_DAEPat
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEProg_DAEPat : all a. (a -> DAEPat -> a) -> a -> DAEProg -> a
sem sfold_DAEProg_DAEPat f acc =
  | x ->
    (smapAccumL_DAEProg_DAEPat
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEProg_DAEExpr : all a. (a -> DAEExpr -> (a, DAEExpr)) -> a -> DAEProg -> (a, DAEProg)
sem smapAccumL_DAEProg_DAEExpr f acc =
  | x ->
    (acc, x)
  sem smap_DAEProg_DAEExpr : (DAEExpr -> DAEExpr) -> DAEProg -> DAEProg
sem smap_DAEProg_DAEExpr f =
  | x ->
    (smapAccumL_DAEProg_DAEExpr
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEProg_DAEExpr : all a. (a -> DAEExpr -> a) -> a -> DAEProg -> a
sem sfold_DAEProg_DAEExpr f acc =
  | x ->
    (smapAccumL_DAEProg_DAEExpr
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEProg_DAEEqn : all a. (a -> DAEEqn -> (a, DAEEqn)) -> a -> DAEProg -> (a, DAEProg)
sem smapAccumL_DAEProg_DAEEqn f acc =
  | x ->
    (acc, x)
  sem smap_DAEProg_DAEEqn : (DAEEqn -> DAEEqn) -> DAEProg -> DAEProg
sem smap_DAEProg_DAEEqn f =
  | x ->
    (smapAccumL_DAEProg_DAEEqn
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEProg_DAEEqn : all a. (a -> DAEEqn -> a) -> a -> DAEProg -> a
sem sfold_DAEProg_DAEEqn f acc =
  | x ->
    (smapAccumL_DAEProg_DAEEqn
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEProg_DAEVar : all a. (a -> DAEVar -> (a, DAEVar)) -> a -> DAEProg -> (a, DAEProg)
sem smapAccumL_DAEProg_DAEVar f acc =
  | x ->
    (acc, x)
  sem smap_DAEProg_DAEVar : (DAEVar -> DAEVar) -> DAEProg -> DAEProg
sem smap_DAEProg_DAEVar f =
  | x ->
    (smapAccumL_DAEProg_DAEVar
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEProg_DAEVar : all a. (a -> DAEVar -> a) -> a -> DAEProg -> a
sem sfold_DAEProg_DAEVar f acc =
  | x ->
    (smapAccumL_DAEProg_DAEVar
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEProg_DAETop : all a. (a -> DAETop -> (a, DAETop)) -> a -> DAEProg -> (a, DAEProg)
sem smapAccumL_DAEProg_DAETop f acc =
  | x ->
    (acc, x)
  sem smap_DAEProg_DAETop : (DAETop -> DAETop) -> DAEProg -> DAEProg
sem smap_DAEProg_DAETop f =
  | x ->
    (smapAccumL_DAEProg_DAETop
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEProg_DAETop : all a. (a -> DAETop -> a) -> a -> DAEProg -> a
sem sfold_DAEProg_DAETop f acc =
  | x ->
    (smapAccumL_DAEProg_DAETop
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_DAEProg_DAEProg : all a. (a -> DAEProg -> (a, DAEProg)) -> a -> DAEProg -> (a, DAEProg)
sem smapAccumL_DAEProg_DAEProg f acc =
  | x ->
    (acc, x)
  sem smap_DAEProg_DAEProg : (DAEProg -> DAEProg) -> DAEProg -> DAEProg
sem smap_DAEProg_DAEProg f =
  | x ->
    (smapAccumL_DAEProg_DAEProg
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_DAEProg_DAEProg : all a. (a -> DAEProg -> a) -> a -> DAEProg -> a
sem sfold_DAEProg_DAEProg f acc =
  | x ->
    (smapAccumL_DAEProg_DAEProg
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem get_DAEType_info : DAEType -> Info
  sem set_DAEType_info : Info -> DAEType -> DAEType
sem set_DAEType_info val =
  sem mapAccum_DAEType_info : all a. (a -> Info -> (a, Info)) -> a -> DAEType -> (a, DAEType)
sem mapAccum_DAEType_info f acc =
  | target ->
    match
      f
        acc
        (get_DAEType_info
           target)
    with
      (acc, val)
    in
    (acc, set_DAEType_info
        val
        target)
  sem map_DAEType_info : (Info -> Info) -> DAEType -> DAEType
sem map_DAEType_info f =
  | target ->
    set_DAEType_info
      (f
         (get_DAEType_info
            target))
      target
  sem get_DAEConst_info : DAEConst -> Info
  sem set_DAEConst_info : Info -> DAEConst -> DAEConst
sem set_DAEConst_info val =
  sem mapAccum_DAEConst_info : all a. (a -> Info -> (a, Info)) -> a -> DAEConst -> (a, DAEConst)
sem mapAccum_DAEConst_info f acc =
  | target ->
    match
      f
        acc
        (get_DAEConst_info
           target)
    with
      (acc, val)
    in
    (acc, set_DAEConst_info
        val
        target)
  sem map_DAEConst_info : (Info -> Info) -> DAEConst -> DAEConst
sem map_DAEConst_info f =
  | target ->
    set_DAEConst_info
      (f
         (get_DAEConst_info
            target))
      target
  sem get_DAEPat_info : DAEPat -> Info
  sem set_DAEPat_info : Info -> DAEPat -> DAEPat
sem set_DAEPat_info val =
  sem mapAccum_DAEPat_info : all a. (a -> Info -> (a, Info)) -> a -> DAEPat -> (a, DAEPat)
sem mapAccum_DAEPat_info f acc =
  | target ->
    match
      f
        acc
        (get_DAEPat_info
           target)
    with
      (acc, val)
    in
    (acc, set_DAEPat_info
        val
        target)
  sem map_DAEPat_info : (Info -> Info) -> DAEPat -> DAEPat
sem map_DAEPat_info f =
  | target ->
    set_DAEPat_info
      (f
         (get_DAEPat_info
            target))
      target
  sem get_DAEExpr_info : DAEExpr -> Info
  sem set_DAEExpr_info : Info -> DAEExpr -> DAEExpr
sem set_DAEExpr_info val =
  sem mapAccum_DAEExpr_info : all a. (a -> Info -> (a, Info)) -> a -> DAEExpr -> (a, DAEExpr)
sem mapAccum_DAEExpr_info f acc =
  | target ->
    match
      f
        acc
        (get_DAEExpr_info
           target)
    with
      (acc, val)
    in
    (acc, set_DAEExpr_info
        val
        target)
  sem map_DAEExpr_info : (Info -> Info) -> DAEExpr -> DAEExpr
sem map_DAEExpr_info f =
  | target ->
    set_DAEExpr_info
      (f
         (get_DAEExpr_info
            target))
      target
  sem get_DAEEqn_info : DAEEqn -> Info
  sem set_DAEEqn_info : Info -> DAEEqn -> DAEEqn
sem set_DAEEqn_info val =
  sem mapAccum_DAEEqn_info : all a. (a -> Info -> (a, Info)) -> a -> DAEEqn -> (a, DAEEqn)
sem mapAccum_DAEEqn_info f acc =
  | target ->
    match
      f
        acc
        (get_DAEEqn_info
           target)
    with
      (acc, val)
    in
    (acc, set_DAEEqn_info
        val
        target)
  sem map_DAEEqn_info : (Info -> Info) -> DAEEqn -> DAEEqn
sem map_DAEEqn_info f =
  | target ->
    set_DAEEqn_info
      (f
         (get_DAEEqn_info
            target))
      target
  sem get_DAEVar_info : DAEVar -> Info
  sem set_DAEVar_info : Info -> DAEVar -> DAEVar
sem set_DAEVar_info val =
  sem mapAccum_DAEVar_info : all a. (a -> Info -> (a, Info)) -> a -> DAEVar -> (a, DAEVar)
sem mapAccum_DAEVar_info f acc =
  | target ->
    match
      f
        acc
        (get_DAEVar_info
           target)
    with
      (acc, val)
    in
    (acc, set_DAEVar_info
        val
        target)
  sem map_DAEVar_info : (Info -> Info) -> DAEVar -> DAEVar
sem map_DAEVar_info f =
  | target ->
    set_DAEVar_info
      (f
         (get_DAEVar_info
            target))
      target
  sem get_DAETop_info : DAETop -> Info
  sem set_DAETop_info : Info -> DAETop -> DAETop
sem set_DAETop_info val =
  sem mapAccum_DAETop_info : all a. (a -> Info -> (a, Info)) -> a -> DAETop -> (a, DAETop)
sem mapAccum_DAETop_info f acc =
  | target ->
    match
      f
        acc
        (get_DAETop_info
           target)
    with
      (acc, val)
    in
    (acc, set_DAETop_info
        val
        target)
  sem map_DAETop_info : (Info -> Info) -> DAETop -> DAETop
sem map_DAETop_info f =
  | target ->
    set_DAETop_info
      (f
         (get_DAETop_info
            target))
      target
  sem get_DAEProg_info : DAEProg -> Info
  sem set_DAEProg_info : Info -> DAEProg -> DAEProg
sem set_DAEProg_info val =
  sem mapAccum_DAEProg_info : all a. (a -> Info -> (a, Info)) -> a -> DAEProg -> (a, DAEProg)
sem mapAccum_DAEProg_info f acc =
  | target ->
    match
      f
        acc
        (get_DAEProg_info
           target)
    with
      (acc, val)
    in
    (acc, set_DAEProg_info
        val
        target)
  sem map_DAEProg_info : (Info -> Info) -> DAEProg -> DAEProg
sem map_DAEProg_info f =
  | target ->
    set_DAEProg_info
      (f
         (get_DAEProg_info
            target))
      target
end
lang FloatDAETypeAst =
  DAEParseBaseAst
  type FloatDAETypeRecord =
    {info: Info}
  syn DAEType =
  | FloatDAEType FloatDAETypeRecord
  sem get_DAEType_info =
  | FloatDAEType target ->
    target.info
  sem set_DAEType_info val =
  | FloatDAEType target ->
    FloatDAEType
      { target
        with
        info =
          val }
end
lang IntDAETypeAst =
  DAEParseBaseAst
  type IntDAETypeRecord =
    {info: Info}
  syn DAEType =
  | IntDAEType IntDAETypeRecord
  sem get_DAEType_info =
  | IntDAEType target ->
    target.info
  sem set_DAEType_info val =
  | IntDAEType target ->
    IntDAEType
      { target
        with
        info =
          val }
end
lang ArrowDAETypeAst =
  DAEParseBaseAst
  type ArrowDAETypeRecord =
    {info: Info, left: DAEType, right: DAEType}
  syn DAEType =
  | ArrowDAEType ArrowDAETypeRecord
  sem smapAccumL_DAEType_DAEType f acc =
  | ArrowDAEType x ->
    match
      match
        let left =
          x.left
        in
        f
          acc
          left
      with
        (acc, left)
      in
      match
          let right =
            x.right
          in
          f
            acc
            right
        with
          (acc, right)
        in
        (acc, { { x
              with
              left =
                left }
            with
            right =
              right })
    with
      (acc, x)
    in
    (acc, ArrowDAEType
        x)
  sem get_DAEType_info =
  | ArrowDAEType target ->
    target.info
  sem set_DAEType_info val =
  | ArrowDAEType target ->
    ArrowDAEType
      { target
        with
        info =
          val }
end
lang FloatDAEConstAst =
  DAEParseBaseAst
  type FloatDAEConstRecord =
    {val: {i: Info, v: Float}, info: Info}
  syn DAEConst =
  | FloatDAEConst FloatDAEConstRecord
  sem get_DAEConst_info =
  | FloatDAEConst target ->
    target.info
  sem set_DAEConst_info val =
  | FloatDAEConst target ->
    FloatDAEConst
      { target
        with
        info =
          val }
end
lang IntDAEConstAst =
  DAEParseBaseAst
  type IntDAEConstRecord =
    {val: {i: Info, v: Int}, info: Info}
  syn DAEConst =
  | IntDAEConst IntDAEConstRecord
  sem get_DAEConst_info =
  | IntDAEConst target ->
    target.info
  sem set_DAEConst_info val =
  | IntDAEConst target ->
    IntDAEConst
      { target
        with
        info =
          val }
end
lang TrueDAEConstAst =
  DAEParseBaseAst
  type TrueDAEConstRecord =
    {info: Info}
  syn DAEConst =
  | TrueDAEConst TrueDAEConstRecord
  sem get_DAEConst_info =
  | TrueDAEConst target ->
    target.info
  sem set_DAEConst_info val =
  | TrueDAEConst target ->
    TrueDAEConst
      { target
        with
        info =
          val }
end
lang FalseDAEConstAst =
  DAEParseBaseAst
  type FalseDAEConstRecord =
    {info: Info}
  syn DAEConst =
  | FalseDAEConst FalseDAEConstRecord
  sem get_DAEConst_info =
  | FalseDAEConst target ->
    target.info
  sem set_DAEConst_info val =
  | FalseDAEConst target ->
    FalseDAEConst
      { target
        with
        info =
          val }
end
lang PredDAEConstAst =
  DAEParseBaseAst
  type PredDAEConstRecord =
    {info: Info}
  syn DAEConst =
  | PredDAEConst PredDAEConstRecord
  sem get_DAEConst_info =
  | PredDAEConst target ->
    target.info
  sem set_DAEConst_info val =
  | PredDAEConst target ->
    PredDAEConst
      { target
        with
        info =
          val }
end
lang ExpDAEConstAst =
  DAEParseBaseAst
  type ExpDAEConstRecord =
    {info: Info}
  syn DAEConst =
  | ExpDAEConst ExpDAEConstRecord
  sem get_DAEConst_info =
  | ExpDAEConst target ->
    target.info
  sem set_DAEConst_info val =
  | ExpDAEConst target ->
    ExpDAEConst
      { target
        with
        info =
          val }
end
lang SinDAEConstAst =
  DAEParseBaseAst
  type SinDAEConstRecord =
    {info: Info}
  syn DAEConst =
  | SinDAEConst SinDAEConstRecord
  sem get_DAEConst_info =
  | SinDAEConst target ->
    target.info
  sem set_DAEConst_info val =
  | SinDAEConst target ->
    SinDAEConst
      { target
        with
        info =
          val }
end
lang CosDAEConstAst =
  DAEParseBaseAst
  type CosDAEConstRecord =
    {info: Info}
  syn DAEConst =
  | CosDAEConst CosDAEConstRecord
  sem get_DAEConst_info =
  | CosDAEConst target ->
    target.info
  sem set_DAEConst_info val =
  | CosDAEConst target ->
    CosDAEConst
      { target
        with
        info =
          val }
end
lang SqrtDAEConstAst =
  DAEParseBaseAst
  type SqrtDAEConstRecord =
    {info: Info}
  syn DAEConst =
  | SqrtDAEConst SqrtDAEConstRecord
  sem get_DAEConst_info =
  | SqrtDAEConst target ->
    target.info
  sem set_DAEConst_info val =
  | SqrtDAEConst target ->
    SqrtDAEConst
      { target
        with
        info =
          val }
end
lang TupleDAEPatAst =
  DAEParseBaseAst
  type TupleDAEPatRecord =
    {info: Info, names: [{i: Info, v: Name}]}
  syn DAEPat =
  | TupleDAEPat TupleDAEPatRecord
  sem get_DAEPat_info =
  | TupleDAEPat target ->
    target.info
  sem set_DAEPat_info val =
  | TupleDAEPat target ->
    TupleDAEPat
      { target
        with
        info =
          val }
end
lang VarDAEExprAst =
  DAEParseBaseAst
  type VarDAEExprRecord =
    {info: Info, name: {i: Info, v: Name}}
  syn DAEExpr =
  | VarDAEExpr VarDAEExprRecord
  sem get_DAEExpr_info =
  | VarDAEExpr target ->
    target.info
  sem set_DAEExpr_info val =
  | VarDAEExpr target ->
    VarDAEExpr
      { target
        with
        info =
          val }
end
lang AbsDAEExprAst =
  DAEParseBaseAst
  type AbsDAEExprRecord =
    {body: DAEExpr, info: Info, name: {i: Info, v: Name}}
  syn DAEExpr =
  | AbsDAEExpr AbsDAEExprRecord
  sem smapAccumL_DAEExpr_DAEExpr f acc =
  | AbsDAEExpr x ->
    match
      match
        let body =
          x.body
        in
        f
          acc
          body
      with
        (acc, body)
      in
      (acc, { x
          with
          body =
            body })
    with
      (acc, x)
    in
    (acc, AbsDAEExpr
        x)
  sem get_DAEExpr_info =
  | AbsDAEExpr target ->
    target.info
  sem set_DAEExpr_info val =
  | AbsDAEExpr target ->
    AbsDAEExpr
      { target
        with
        info =
          val }
end
lang AppDAEExprAst =
  DAEParseBaseAst
  type AppDAEExprRecord =
    {fn: DAEExpr, arg: DAEExpr, info: Info}
  syn DAEExpr =
  | AppDAEExpr AppDAEExprRecord
  sem smapAccumL_DAEExpr_DAEExpr f acc =
  | AppDAEExpr x ->
    match
      match
        let fn =
          x.fn
        in
        f
          acc
          fn
      with
        (acc, fn)
      in
      match
          let arg =
            x.arg
          in
          f
            acc
            arg
        with
          (acc, arg)
        in
        (acc, { { x
              with
              fn =
                fn }
            with
            arg =
              arg })
    with
      (acc, x)
    in
    (acc, AppDAEExpr
        x)
  sem get_DAEExpr_info =
  | AppDAEExpr target ->
    target.info
  sem set_DAEExpr_info val =
  | AppDAEExpr target ->
    AppDAEExpr
      { target
        with
        info =
          val }
end
lang TupleDAEExprAst =
  DAEParseBaseAst
  type TupleDAEExprRecord =
    {info: Info, exprs: [DAEExpr]}
  syn DAEExpr =
  | TupleDAEExpr TupleDAEExprRecord
  sem smapAccumL_DAEExpr_DAEExpr f acc =
  | TupleDAEExpr x ->
    match
      match
        let exprs =
          x.exprs
        in
        mapAccumL
          (lam acc1.
             lam x1: DAEExpr.
               f
                 acc1
                 x1)
          acc
          exprs
      with
        (acc, exprs)
      in
      (acc, { x
          with
          exprs =
            exprs })
    with
      (acc, x)
    in
    (acc, TupleDAEExpr
        x)
  sem get_DAEExpr_info =
  | TupleDAEExpr target ->
    target.info
  sem set_DAEExpr_info val =
  | TupleDAEExpr target ->
    TupleDAEExpr
      { target
        with
        info =
          val }
end
lang ProjDAEExprAst =
  DAEParseBaseAst
  type ProjDAEExprRecord =
    {expr: DAEExpr, info: Info, label: {i: Info, v: Int}}
  syn DAEExpr =
  | ProjDAEExpr ProjDAEExprRecord
  sem smapAccumL_DAEExpr_DAEExpr f acc =
  | ProjDAEExpr x ->
    match
      match
        let expr =
          x.expr
        in
        f
          acc
          expr
      with
        (acc, expr)
      in
      (acc, { x
          with
          expr =
            expr })
    with
      (acc, x)
    in
    (acc, ProjDAEExpr
        x)
  sem get_DAEExpr_info =
  | ProjDAEExpr target ->
    target.info
  sem set_DAEExpr_info val =
  | ProjDAEExpr target ->
    ProjDAEExpr
      { target
        with
        info =
          val }
end
lang ConstDAEExprAst =
  DAEParseBaseAst
  type ConstDAEExprRecord =
    {val: DAEConst, info: Info}
  syn DAEExpr =
  | ConstDAEExpr ConstDAEExprRecord
  sem smapAccumL_DAEExpr_DAEConst f acc =
  | ConstDAEExpr x ->
    match
      match
        let val1 =
          x.val
        in
        f
          acc
          val1
      with
        (acc, val1)
      in
      (acc, { x
          with
          val =
            val1 })
    with
      (acc, x)
    in
    (acc, ConstDAEExpr
        x)
  sem get_DAEExpr_info =
  | ConstDAEExpr target ->
    target.info
  sem set_DAEExpr_info val =
  | ConstDAEExpr target ->
    ConstDAEExpr
      { target
        with
        info =
          val }
end
lang AddDAEExprAst =
  DAEParseBaseAst
  type AddDAEExprRecord =
    {info: Info, left: DAEExpr, right: DAEExpr}
  syn DAEExpr =
  | AddDAEExpr AddDAEExprRecord
  sem smapAccumL_DAEExpr_DAEExpr f acc =
  | AddDAEExpr x ->
    match
      match
        let left =
          x.left
        in
        f
          acc
          left
      with
        (acc, left)
      in
      match
          let right =
            x.right
          in
          f
            acc
            right
        with
          (acc, right)
        in
        (acc, { { x
              with
              left =
                left }
            with
            right =
              right })
    with
      (acc, x)
    in
    (acc, AddDAEExpr
        x)
  sem get_DAEExpr_info =
  | AddDAEExpr target ->
    target.info
  sem set_DAEExpr_info val =
  | AddDAEExpr target ->
    AddDAEExpr
      { target
        with
        info =
          val }
end
lang SubDAEExprAst =
  DAEParseBaseAst
  type SubDAEExprRecord =
    {info: Info, left: DAEExpr, right: DAEExpr}
  syn DAEExpr =
  | SubDAEExpr SubDAEExprRecord
  sem smapAccumL_DAEExpr_DAEExpr f acc =
  | SubDAEExpr x ->
    match
      match
        let left =
          x.left
        in
        f
          acc
          left
      with
        (acc, left)
      in
      match
          let right =
            x.right
          in
          f
            acc
            right
        with
          (acc, right)
        in
        (acc, { { x
              with
              left =
                left }
            with
            right =
              right })
    with
      (acc, x)
    in
    (acc, SubDAEExpr
        x)
  sem get_DAEExpr_info =
  | SubDAEExpr target ->
    target.info
  sem set_DAEExpr_info val =
  | SubDAEExpr target ->
    SubDAEExpr
      { target
        with
        info =
          val }
end
lang MulDAEExprAst =
  DAEParseBaseAst
  type MulDAEExprRecord =
    {info: Info, left: DAEExpr, right: DAEExpr}
  syn DAEExpr =
  | MulDAEExpr MulDAEExprRecord
  sem smapAccumL_DAEExpr_DAEExpr f acc =
  | MulDAEExpr x ->
    match
      match
        let left =
          x.left
        in
        f
          acc
          left
      with
        (acc, left)
      in
      match
          let right =
            x.right
          in
          f
            acc
            right
        with
          (acc, right)
        in
        (acc, { { x
              with
              left =
                left }
            with
            right =
              right })
    with
      (acc, x)
    in
    (acc, MulDAEExpr
        x)
  sem get_DAEExpr_info =
  | MulDAEExpr target ->
    target.info
  sem set_DAEExpr_info val =
  | MulDAEExpr target ->
    MulDAEExpr
      { target
        with
        info =
          val }
end
lang DivDAEExprAst =
  DAEParseBaseAst
  type DivDAEExprRecord =
    {info: Info, left: DAEExpr, right: DAEExpr}
  syn DAEExpr =
  | DivDAEExpr DivDAEExprRecord
  sem smapAccumL_DAEExpr_DAEExpr f acc =
  | DivDAEExpr x ->
    match
      match
        let left =
          x.left
        in
        f
          acc
          left
      with
        (acc, left)
      in
      match
          let right =
            x.right
          in
          f
            acc
            right
        with
          (acc, right)
        in
        (acc, { { x
              with
              left =
                left }
            with
            right =
              right })
    with
      (acc, x)
    in
    (acc, DivDAEExpr
        x)
  sem get_DAEExpr_info =
  | DivDAEExpr target ->
    target.info
  sem set_DAEExpr_info val =
  | DivDAEExpr target ->
    DivDAEExpr
      { target
        with
        info =
          val }
end
lang LtDAEExprAst =
  DAEParseBaseAst
  type LtDAEExprRecord =
    {info: Info, left: DAEExpr, right: DAEExpr}
  syn DAEExpr =
  | LtDAEExpr LtDAEExprRecord
  sem smapAccumL_DAEExpr_DAEExpr f acc =
  | LtDAEExpr x ->
    match
      match
        let left =
          x.left
        in
        f
          acc
          left
      with
        (acc, left)
      in
      match
          let right =
            x.right
          in
          f
            acc
            right
        with
          (acc, right)
        in
        (acc, { { x
              with
              left =
                left }
            with
            right =
              right })
    with
      (acc, x)
    in
    (acc, LtDAEExpr
        x)
  sem get_DAEExpr_info =
  | LtDAEExpr target ->
    target.info
  sem set_DAEExpr_info val =
  | LtDAEExpr target ->
    LtDAEExpr
      { target
        with
        info =
          val }
end
lang LtfDAEExprAst =
  DAEParseBaseAst
  type LtfDAEExprRecord =
    {info: Info, left: DAEExpr, right: DAEExpr}
  syn DAEExpr =
  | LtfDAEExpr LtfDAEExprRecord
  sem smapAccumL_DAEExpr_DAEExpr f acc =
  | LtfDAEExpr x ->
    match
      match
        let left =
          x.left
        in
        f
          acc
          left
      with
        (acc, left)
      in
      match
          let right =
            x.right
          in
          f
            acc
            right
        with
          (acc, right)
        in
        (acc, { { x
              with
              left =
                left }
            with
            right =
              right })
    with
      (acc, x)
    in
    (acc, LtfDAEExpr
        x)
  sem get_DAEExpr_info =
  | LtfDAEExpr target ->
    target.info
  sem set_DAEExpr_info val =
  | LtfDAEExpr target ->
    LtfDAEExpr
      { target
        with
        info =
          val }
end
lang EqDAEExprAst =
  DAEParseBaseAst
  type EqDAEExprRecord =
    {info: Info, left: DAEExpr, right: DAEExpr}
  syn DAEExpr =
  | EqDAEExpr EqDAEExprRecord
  sem smapAccumL_DAEExpr_DAEExpr f acc =
  | EqDAEExpr x ->
    match
      match
        let left =
          x.left
        in
        f
          acc
          left
      with
        (acc, left)
      in
      match
          let right =
            x.right
          in
          f
            acc
            right
        with
          (acc, right)
        in
        (acc, { { x
              with
              left =
                left }
            with
            right =
              right })
    with
      (acc, x)
    in
    (acc, EqDAEExpr
        x)
  sem get_DAEExpr_info =
  | EqDAEExpr target ->
    target.info
  sem set_DAEExpr_info val =
  | EqDAEExpr target ->
    EqDAEExpr
      { target
        with
        info =
          val }
end
lang NegDAEExprAst =
  DAEParseBaseAst
  type NegDAEExprRecord =
    {info: Info, right: DAEExpr}
  syn DAEExpr =
  | NegDAEExpr NegDAEExprRecord
  sem smapAccumL_DAEExpr_DAEExpr f acc =
  | NegDAEExpr x ->
    match
      match
        let right =
          x.right
        in
        f
          acc
          right
      with
        (acc, right)
      in
      (acc, { x
          with
          right =
            right })
    with
      (acc, x)
    in
    (acc, NegDAEExpr
        x)
  sem get_DAEExpr_info =
  | NegDAEExpr target ->
    target.info
  sem set_DAEExpr_info val =
  | NegDAEExpr target ->
    NegDAEExpr
      { target
        with
        info =
          val }
end
lang MatchInDAEExprAst =
  DAEParseBaseAst
  type MatchInDAEExprRecord =
    {pat: DAEPat, body: DAEExpr, info: Info, target: DAEExpr}
  syn DAEExpr =
  | MatchInDAEExpr MatchInDAEExprRecord
  sem smapAccumL_DAEExpr_DAEPat f acc =
  | MatchInDAEExpr x ->
    match
      match
        let pat =
          x.pat
        in
        f
          acc
          pat
      with
        (acc, pat)
      in
      (acc, { x
          with
          pat =
            pat })
    with
      (acc, x)
    in
    (acc, MatchInDAEExpr
        x)
  sem smapAccumL_DAEExpr_DAEExpr f acc =
  | MatchInDAEExpr x ->
    match
      match
        let body =
          x.body
        in
        f
          acc
          body
      with
        (acc, body)
      in
      match
          let target =
            x.target
          in
          f
            acc
            target
        with
          (acc, target)
        in
        (acc, { { x
              with
              body =
                body }
            with
            target =
              target })
    with
      (acc, x)
    in
    (acc, MatchInDAEExpr
        x)
  sem get_DAEExpr_info =
  | MatchInDAEExpr target ->
    target.info
  sem set_DAEExpr_info val =
  | MatchInDAEExpr target ->
    MatchInDAEExpr
      { target
        with
        info =
          val }
end
lang IfDAEExprAst =
  DAEParseBaseAst
  type IfDAEExprRecord =
    {els: DAEExpr, thn: DAEExpr, info: Info, pred: DAEExpr}
  syn DAEExpr =
  | IfDAEExpr IfDAEExprRecord
  sem smapAccumL_DAEExpr_DAEExpr f acc =
  | IfDAEExpr x ->
    match
      match
        let els =
          x.els
        in
        f
          acc
          els
      with
        (acc, els)
      in
      match
          let thn =
            x.thn
          in
          f
            acc
            thn
        with
          (acc, thn)
        in
        match
            let pred =
              x.pred
            in
            f
              acc
              pred
          with
            (acc, pred)
          in
          (acc, { { { x
                  with
                  els =
                    els }
                with
                thn =
                  thn }
              with
              pred =
                pred })
    with
      (acc, x)
    in
    (acc, IfDAEExpr
        x)
  sem get_DAEExpr_info =
  | IfDAEExpr target ->
    target.info
  sem set_DAEExpr_info val =
  | IfDAEExpr target ->
    IfDAEExpr
      { target
        with
        info =
          val }
end
lang LetDAEExprAst =
  DAEParseBaseAst
  type LetDAEExprRecord =
    {arg: DAEExpr, body: DAEExpr, info: Info, name: {i: Info, v: Name}}
  syn DAEExpr =
  | LetDAEExpr LetDAEExprRecord
  sem smapAccumL_DAEExpr_DAEExpr f acc =
  | LetDAEExpr x ->
    match
      match
        let arg =
          x.arg
        in
        f
          acc
          arg
      with
        (acc, arg)
      in
      match
          let body =
            x.body
          in
          f
            acc
            body
        with
          (acc, body)
        in
        (acc, { { x
              with
              arg =
                arg }
            with
            body =
              body })
    with
      (acc, x)
    in
    (acc, LetDAEExpr
        x)
  sem get_DAEExpr_info =
  | LetDAEExpr target ->
    target.info
  sem set_DAEExpr_info val =
  | LetDAEExpr target ->
    LetDAEExpr
      { target
        with
        info =
          val }
end
lang RecLetDAEExprAst =
  DAEParseBaseAst
  type RecLetDAEExprRecord =
    {arg: DAEExpr, body: DAEExpr, info: Info, name: {i: Info, v: Name}}
  syn DAEExpr =
  | RecLetDAEExpr RecLetDAEExprRecord
  sem smapAccumL_DAEExpr_DAEExpr f acc =
  | RecLetDAEExpr x ->
    match
      match
        let arg =
          x.arg
        in
        f
          acc
          arg
      with
        (acc, arg)
      in
      match
          let body =
            x.body
          in
          f
            acc
            body
        with
          (acc, body)
        in
        (acc, { { x
              with
              arg =
                arg }
            with
            body =
              body })
    with
      (acc, x)
    in
    (acc, RecLetDAEExpr
        x)
  sem get_DAEExpr_info =
  | RecLetDAEExpr target ->
    target.info
  sem set_DAEExpr_info val =
  | RecLetDAEExpr target ->
    RecLetDAEExpr
      { target
        with
        info =
          val }
end
lang PrimDAEExprAst =
  DAEParseBaseAst
  type PrimDAEExprRecord =
    {info: Info, left: DAEExpr}
  syn DAEExpr =
  | PrimDAEExpr PrimDAEExprRecord
  sem smapAccumL_DAEExpr_DAEExpr f acc =
  | PrimDAEExpr x ->
    match
      match
        let left =
          x.left
        in
        f
          acc
          left
      with
        (acc, left)
      in
      (acc, { x
          with
          left =
            left })
    with
      (acc, x)
    in
    (acc, PrimDAEExpr
        x)
  sem get_DAEExpr_info =
  | PrimDAEExpr target ->
    target.info
  sem set_DAEExpr_info val =
  | PrimDAEExpr target ->
    PrimDAEExpr
      { target
        with
        info =
          val }
end
lang EqnDAEEqnAst =
  DAEParseBaseAst
  type EqnDAEEqnRecord =
    {info: Info, left: DAEExpr, right: DAEExpr}
  syn DAEEqn =
  | EqnDAEEqn EqnDAEEqnRecord
  sem smapAccumL_DAEEqn_DAEExpr f acc =
  | EqnDAEEqn x ->
    match
      match
        let left =
          x.left
        in
        f
          acc
          left
      with
        (acc, left)
      in
      match
          let right =
            x.right
          in
          f
            acc
            right
        with
          (acc, right)
        in
        (acc, { { x
              with
              left =
                left }
            with
            right =
              right })
    with
      (acc, x)
    in
    (acc, EqnDAEEqn
        x)
  sem get_DAEEqn_info =
  | EqnDAEEqn target ->
    target.info
  sem set_DAEEqn_info val =
  | EqnDAEEqn target ->
    EqnDAEEqn
      { target
        with
        info =
          val }
end
lang VarsDAEVarAst =
  DAEParseBaseAst
  type VarsDAEVarRecord =
    {ty: DAEType, info: Info, names: [{i: Info, v: Name}]}
  syn DAEVar =
  | VarsDAEVar VarsDAEVarRecord
  sem smapAccumL_DAEVar_DAEType f acc =
  | VarsDAEVar x ->
    match
      match
        let ty =
          x.ty
        in
        f
          acc
          ty
      with
        (acc, ty)
      in
      (acc, { x
          with
          ty =
            ty })
    with
      (acc, x)
    in
    (acc, VarsDAEVar
        x)
  sem get_DAEVar_info =
  | VarsDAEVar target ->
    target.info
  sem set_DAEVar_info val =
  | VarsDAEVar target ->
    VarsDAEVar
      { target
        with
        info =
          val }
end
lang LetDAETopAst =
  DAEParseBaseAst
  type LetDAETopRecord =
    {arg: DAEExpr, info: Info, name: {i: Info, v: Name}}
  syn DAETop =
  | LetDAETop LetDAETopRecord
  sem smapAccumL_DAETop_DAEExpr f acc =
  | LetDAETop x ->
    match
      match
        let arg =
          x.arg
        in
        f
          acc
          arg
      with
        (acc, arg)
      in
      (acc, { x
          with
          arg =
            arg })
    with
      (acc, x)
    in
    (acc, LetDAETop
        x)
  sem get_DAETop_info =
  | LetDAETop target ->
    target.info
  sem set_DAETop_info val =
  | LetDAETop target ->
    LetDAETop
      { target
        with
        info =
          val }
end
lang RecLetDAETopAst =
  DAEParseBaseAst
  type RecLetDAETopRecord =
    {arg: DAEExpr, info: Info, name: {i: Info, v: Name}}
  syn DAETop =
  | RecLetDAETop RecLetDAETopRecord
  sem smapAccumL_DAETop_DAEExpr f acc =
  | RecLetDAETop x ->
    match
      match
        let arg =
          x.arg
        in
        f
          acc
          arg
      with
        (acc, arg)
      in
      (acc, { x
          with
          arg =
            arg })
    with
      (acc, x)
    in
    (acc, RecLetDAETop
        x)
  sem get_DAETop_info =
  | RecLetDAETop target ->
    target.info
  sem set_DAETop_info val =
  | RecLetDAETop target ->
    RecLetDAETop
      { target
        with
        info =
          val }
end
lang ProgDAEProgAst =
  DAEParseBaseAst
  type ProgDAEProgRecord =
    {eqns: [DAEEqn], info: Info, tops: [DAETop], vars: [DAEVar], ieqns: [DAEEqn], output: DAEExpr}
  syn DAEProg =
  | ProgDAEProg ProgDAEProgRecord
  sem smapAccumL_DAEProg_DAEExpr f acc =
  | ProgDAEProg x ->
    match
      match
        let output =
          x.output
        in
        f
          acc
          output
      with
        (acc, output)
      in
      (acc, { x
          with
          output =
            output })
    with
      (acc, x)
    in
    (acc, ProgDAEProg
        x)
  sem smapAccumL_DAEProg_DAEEqn f acc =
  | ProgDAEProg x ->
    match
      match
        let eqns =
          x.eqns
        in
        mapAccumL
          (lam acc1.
             lam x1: DAEEqn.
               f
                 acc1
                 x1)
          acc
          eqns
      with
        (acc, eqns)
      in
      match
          let ieqns =
            x.ieqns
          in
          mapAccumL
            (lam acc2.
               lam x2: DAEEqn.
                 f
                   acc2
                   x2)
            acc
            ieqns
        with
          (acc, ieqns)
        in
        (acc, { { x
              with
              eqns =
                eqns }
            with
            ieqns =
              ieqns })
    with
      (acc, x)
    in
    (acc, ProgDAEProg
        x)
  sem smapAccumL_DAEProg_DAEVar f acc =
  | ProgDAEProg x ->
    match
      match
        let vars =
          x.vars
        in
        mapAccumL
          (lam acc1.
             lam x1: DAEVar.
               f
                 acc1
                 x1)
          acc
          vars
      with
        (acc, vars)
      in
      (acc, { x
          with
          vars =
            vars })
    with
      (acc, x)
    in
    (acc, ProgDAEProg
        x)
  sem smapAccumL_DAEProg_DAETop f acc =
  | ProgDAEProg x ->
    match
      match
        let tops =
          x.tops
        in
        mapAccumL
          (lam acc1.
             lam x1: DAETop.
               f
                 acc1
                 x1)
          acc
          tops
      with
        (acc, tops)
      in
      (acc, { x
          with
          tops =
            tops })
    with
      (acc, x)
    in
    (acc, ProgDAEProg
        x)
  sem get_DAEProg_info =
  | ProgDAEProg target ->
    target.info
  sem set_DAEProg_info val =
  | ProgDAEProg target ->
    ProgDAEProg
      { target
        with
        info =
          val }
end
lang BadDAETypeAst =
  DAEParseBaseAst
  type BadDAETypeRecord =
    {info: Info}
  syn DAEType =
  | BadDAEType BadDAETypeRecord
  sem get_DAEType_info =
  | BadDAEType target ->
    target.info
  sem set_DAEType_info val =
  | BadDAEType target ->
    BadDAEType
      { target
        with
        info =
          val }
end
lang BadDAEConstAst =
  DAEParseBaseAst
  type BadDAEConstRecord =
    {info: Info}
  syn DAEConst =
  | BadDAEConst BadDAEConstRecord
  sem get_DAEConst_info =
  | BadDAEConst target ->
    target.info
  sem set_DAEConst_info val =
  | BadDAEConst target ->
    BadDAEConst
      { target
        with
        info =
          val }
end
lang BadDAEPatAst =
  DAEParseBaseAst
  type BadDAEPatRecord =
    {info: Info}
  syn DAEPat =
  | BadDAEPat BadDAEPatRecord
  sem get_DAEPat_info =
  | BadDAEPat target ->
    target.info
  sem set_DAEPat_info val =
  | BadDAEPat target ->
    BadDAEPat
      { target
        with
        info =
          val }
end
lang BadDAEExprAst =
  DAEParseBaseAst
  type BadDAEExprRecord =
    {info: Info}
  syn DAEExpr =
  | BadDAEExpr BadDAEExprRecord
  sem get_DAEExpr_info =
  | BadDAEExpr target ->
    target.info
  sem set_DAEExpr_info val =
  | BadDAEExpr target ->
    BadDAEExpr
      { target
        with
        info =
          val }
end
lang BadDAEEqnAst =
  DAEParseBaseAst
  type BadDAEEqnRecord =
    {info: Info}
  syn DAEEqn =
  | BadDAEEqn BadDAEEqnRecord
  sem get_DAEEqn_info =
  | BadDAEEqn target ->
    target.info
  sem set_DAEEqn_info val =
  | BadDAEEqn target ->
    BadDAEEqn
      { target
        with
        info =
          val }
end
lang BadDAEVarAst =
  DAEParseBaseAst
  type BadDAEVarRecord =
    {info: Info}
  syn DAEVar =
  | BadDAEVar BadDAEVarRecord
  sem get_DAEVar_info =
  | BadDAEVar target ->
    target.info
  sem set_DAEVar_info val =
  | BadDAEVar target ->
    BadDAEVar
      { target
        with
        info =
          val }
end
lang BadDAETopAst =
  DAEParseBaseAst
  type BadDAETopRecord =
    {info: Info}
  syn DAETop =
  | BadDAETop BadDAETopRecord
  sem get_DAETop_info =
  | BadDAETop target ->
    target.info
  sem set_DAETop_info val =
  | BadDAETop target ->
    BadDAETop
      { target
        with
        info =
          val }
end
lang BadDAEProgAst =
  DAEParseBaseAst
  type BadDAEProgRecord =
    {info: Info}
  syn DAEProg =
  | BadDAEProg BadDAEProgRecord
  sem get_DAEProg_info =
  | BadDAEProg target ->
    target.info
  sem set_DAEProg_info val =
  | BadDAEProg target ->
    BadDAEProg
      { target
        with
        info =
          val }
end
lang DAEParseAst =
  FloatDAETypeAst
  + IntDAETypeAst
  + ArrowDAETypeAst
  + FloatDAEConstAst
  + IntDAEConstAst
  + TrueDAEConstAst
  + FalseDAEConstAst
  + PredDAEConstAst
  + ExpDAEConstAst
  + SinDAEConstAst
  + CosDAEConstAst
  + SqrtDAEConstAst
  + TupleDAEPatAst
  + VarDAEExprAst
  + AbsDAEExprAst
  + AppDAEExprAst
  + TupleDAEExprAst
  + ProjDAEExprAst
  + ConstDAEExprAst
  + AddDAEExprAst
  + SubDAEExprAst
  + MulDAEExprAst
  + DivDAEExprAst
  + LtDAEExprAst
  + LtfDAEExprAst
  + EqDAEExprAst
  + NegDAEExprAst
  + MatchInDAEExprAst
  + IfDAEExprAst
  + LetDAEExprAst
  + RecLetDAEExprAst
  + PrimDAEExprAst
  + EqnDAEEqnAst
  + VarsDAEVarAst
  + LetDAETopAst
  + RecLetDAETopAst
  + ProgDAEProgAst
  + BadDAETypeAst
  + BadDAEConstAst
  + BadDAEPatAst
  + BadDAEExprAst
  + BadDAEEqnAst
  + BadDAEVarAst
  + BadDAETopAst
  + BadDAEProgAst
end
lang DAETypeOpBase =
  DAEParseAst
  syn DAETypeOp lstyle rstyle =
  sem topAllowed_DAETypeOp : all lstyle. all rstyle. DAETypeOp lstyle rstyle -> Bool
sem topAllowed_DAETypeOp =
  | _ ->
    true
  sem leftAllowed_DAETypeOp : all lstyle. all style. all rstyle. {child: DAETypeOp lstyle rstyle, parent: DAETypeOp LOpen style} -> Bool
sem leftAllowed_DAETypeOp =
  | _ ->
    true
  sem rightAllowed_DAETypeOp : all style. all lstyle. all rstyle. {child: DAETypeOp lstyle rstyle, parent: DAETypeOp style ROpen} -> Bool
sem rightAllowed_DAETypeOp =
  | _ ->
    true
  sem groupingsAllowed_DAETypeOp : all lstyle. all rstyle. (DAETypeOp lstyle ROpen, DAETypeOp LOpen rstyle) -> AllowedDirection
sem groupingsAllowed_DAETypeOp =
  | _ ->
    GEither
      {}
  sem parenAllowed_DAETypeOp : all lstyle. all rstyle. DAETypeOp lstyle rstyle -> AllowedDirection
sem parenAllowed_DAETypeOp =
  | _ ->
    GEither
      {}
  sem getInfo_DAETypeOp : all lstyle. all rstyle. DAETypeOp lstyle rstyle -> Info
  sem getTerms_DAETypeOp : all lstyle. all rstyle. DAETypeOp lstyle rstyle -> [Info]
  sem unsplit_DAETypeOp : PermanentNode DAETypeOp -> (Info, DAEType)
end
lang DAEConstOpBase =
  DAEParseAst
  syn DAEConstOp lstyle rstyle =
  sem topAllowed_DAEConstOp : all lstyle. all rstyle. DAEConstOp lstyle rstyle -> Bool
sem topAllowed_DAEConstOp =
  | _ ->
    true
  sem leftAllowed_DAEConstOp : all lstyle. all style. all rstyle. {child: DAEConstOp lstyle rstyle, parent: DAEConstOp LOpen style} -> Bool
sem leftAllowed_DAEConstOp =
  | _ ->
    true
  sem rightAllowed_DAEConstOp : all style. all lstyle. all rstyle. {child: DAEConstOp lstyle rstyle, parent: DAEConstOp style ROpen} -> Bool
sem rightAllowed_DAEConstOp =
  | _ ->
    true
  sem groupingsAllowed_DAEConstOp : all lstyle. all rstyle. (DAEConstOp lstyle ROpen, DAEConstOp LOpen rstyle) -> AllowedDirection
sem groupingsAllowed_DAEConstOp =
  | _ ->
    GEither
      {}
  sem parenAllowed_DAEConstOp : all lstyle. all rstyle. DAEConstOp lstyle rstyle -> AllowedDirection
sem parenAllowed_DAEConstOp =
  | _ ->
    GEither
      {}
  sem getInfo_DAEConstOp : all lstyle. all rstyle. DAEConstOp lstyle rstyle -> Info
  sem getTerms_DAEConstOp : all lstyle. all rstyle. DAEConstOp lstyle rstyle -> [Info]
  sem unsplit_DAEConstOp : PermanentNode DAEConstOp -> (Info, DAEConst)
end
lang DAEPatOpBase =
  DAEParseAst
  syn DAEPatOp lstyle rstyle =
  sem topAllowed_DAEPatOp : all lstyle. all rstyle. DAEPatOp lstyle rstyle -> Bool
sem topAllowed_DAEPatOp =
  | _ ->
    true
  sem leftAllowed_DAEPatOp : all lstyle. all style. all rstyle. {child: DAEPatOp lstyle rstyle, parent: DAEPatOp LOpen style} -> Bool
sem leftAllowed_DAEPatOp =
  | _ ->
    true
  sem rightAllowed_DAEPatOp : all style. all lstyle. all rstyle. {child: DAEPatOp lstyle rstyle, parent: DAEPatOp style ROpen} -> Bool
sem rightAllowed_DAEPatOp =
  | _ ->
    true
  sem groupingsAllowed_DAEPatOp : all lstyle. all rstyle. (DAEPatOp lstyle ROpen, DAEPatOp LOpen rstyle) -> AllowedDirection
sem groupingsAllowed_DAEPatOp =
  | _ ->
    GEither
      {}
  sem parenAllowed_DAEPatOp : all lstyle. all rstyle. DAEPatOp lstyle rstyle -> AllowedDirection
sem parenAllowed_DAEPatOp =
  | _ ->
    GEither
      {}
  sem getInfo_DAEPatOp : all lstyle. all rstyle. DAEPatOp lstyle rstyle -> Info
  sem getTerms_DAEPatOp : all lstyle. all rstyle. DAEPatOp lstyle rstyle -> [Info]
  sem unsplit_DAEPatOp : PermanentNode DAEPatOp -> (Info, DAEPat)
end
lang DAEExprOpBase =
  DAEParseAst
  syn DAEExprOp lstyle rstyle =
  sem topAllowed_DAEExprOp : all lstyle. all rstyle. DAEExprOp lstyle rstyle -> Bool
sem topAllowed_DAEExprOp =
  | _ ->
    true
  sem leftAllowed_DAEExprOp : all lstyle. all style. all rstyle. {child: DAEExprOp lstyle rstyle, parent: DAEExprOp LOpen style} -> Bool
sem leftAllowed_DAEExprOp =
  | _ ->
    true
  sem rightAllowed_DAEExprOp : all style. all lstyle. all rstyle. {child: DAEExprOp lstyle rstyle, parent: DAEExprOp style ROpen} -> Bool
sem rightAllowed_DAEExprOp =
  | _ ->
    true
  sem groupingsAllowed_DAEExprOp : all lstyle. all rstyle. (DAEExprOp lstyle ROpen, DAEExprOp LOpen rstyle) -> AllowedDirection
sem groupingsAllowed_DAEExprOp =
  | _ ->
    GEither
      {}
  sem parenAllowed_DAEExprOp : all lstyle. all rstyle. DAEExprOp lstyle rstyle -> AllowedDirection
sem parenAllowed_DAEExprOp =
  | _ ->
    GEither
      {}
  sem getInfo_DAEExprOp : all lstyle. all rstyle. DAEExprOp lstyle rstyle -> Info
  sem getTerms_DAEExprOp : all lstyle. all rstyle. DAEExprOp lstyle rstyle -> [Info]
  sem unsplit_DAEExprOp : PermanentNode DAEExprOp -> (Info, DAEExpr)
end
lang DAEEqnOpBase =
  DAEParseAst
  syn DAEEqnOp lstyle rstyle =
  sem topAllowed_DAEEqnOp : all lstyle. all rstyle. DAEEqnOp lstyle rstyle -> Bool
sem topAllowed_DAEEqnOp =
  | _ ->
    true
  sem leftAllowed_DAEEqnOp : all lstyle. all style. all rstyle. {child: DAEEqnOp lstyle rstyle, parent: DAEEqnOp LOpen style} -> Bool
sem leftAllowed_DAEEqnOp =
  | _ ->
    true
  sem rightAllowed_DAEEqnOp : all style. all lstyle. all rstyle. {child: DAEEqnOp lstyle rstyle, parent: DAEEqnOp style ROpen} -> Bool
sem rightAllowed_DAEEqnOp =
  | _ ->
    true
  sem groupingsAllowed_DAEEqnOp : all lstyle. all rstyle. (DAEEqnOp lstyle ROpen, DAEEqnOp LOpen rstyle) -> AllowedDirection
sem groupingsAllowed_DAEEqnOp =
  | _ ->
    GEither
      {}
  sem parenAllowed_DAEEqnOp : all lstyle. all rstyle. DAEEqnOp lstyle rstyle -> AllowedDirection
sem parenAllowed_DAEEqnOp =
  | _ ->
    GEither
      {}
  sem getInfo_DAEEqnOp : all lstyle. all rstyle. DAEEqnOp lstyle rstyle -> Info
  sem getTerms_DAEEqnOp : all lstyle. all rstyle. DAEEqnOp lstyle rstyle -> [Info]
  sem unsplit_DAEEqnOp : PermanentNode DAEEqnOp -> (Info, DAEEqn)
end
lang DAEVarOpBase =
  DAEParseAst
  syn DAEVarOp lstyle rstyle =
  sem topAllowed_DAEVarOp : all lstyle. all rstyle. DAEVarOp lstyle rstyle -> Bool
sem topAllowed_DAEVarOp =
  | _ ->
    true
  sem leftAllowed_DAEVarOp : all lstyle. all style. all rstyle. {child: DAEVarOp lstyle rstyle, parent: DAEVarOp LOpen style} -> Bool
sem leftAllowed_DAEVarOp =
  | _ ->
    true
  sem rightAllowed_DAEVarOp : all style. all lstyle. all rstyle. {child: DAEVarOp lstyle rstyle, parent: DAEVarOp style ROpen} -> Bool
sem rightAllowed_DAEVarOp =
  | _ ->
    true
  sem groupingsAllowed_DAEVarOp : all lstyle. all rstyle. (DAEVarOp lstyle ROpen, DAEVarOp LOpen rstyle) -> AllowedDirection
sem groupingsAllowed_DAEVarOp =
  | _ ->
    GEither
      {}
  sem parenAllowed_DAEVarOp : all lstyle. all rstyle. DAEVarOp lstyle rstyle -> AllowedDirection
sem parenAllowed_DAEVarOp =
  | _ ->
    GEither
      {}
  sem getInfo_DAEVarOp : all lstyle. all rstyle. DAEVarOp lstyle rstyle -> Info
  sem getTerms_DAEVarOp : all lstyle. all rstyle. DAEVarOp lstyle rstyle -> [Info]
  sem unsplit_DAEVarOp : PermanentNode DAEVarOp -> (Info, DAEVar)
end
lang DAETopOpBase =
  DAEParseAst
  syn DAETopOp lstyle rstyle =
  sem topAllowed_DAETopOp : all lstyle. all rstyle. DAETopOp lstyle rstyle -> Bool
sem topAllowed_DAETopOp =
  | _ ->
    true
  sem leftAllowed_DAETopOp : all lstyle. all style. all rstyle. {child: DAETopOp lstyle rstyle, parent: DAETopOp LOpen style} -> Bool
sem leftAllowed_DAETopOp =
  | _ ->
    true
  sem rightAllowed_DAETopOp : all style. all lstyle. all rstyle. {child: DAETopOp lstyle rstyle, parent: DAETopOp style ROpen} -> Bool
sem rightAllowed_DAETopOp =
  | _ ->
    true
  sem groupingsAllowed_DAETopOp : all lstyle. all rstyle. (DAETopOp lstyle ROpen, DAETopOp LOpen rstyle) -> AllowedDirection
sem groupingsAllowed_DAETopOp =
  | _ ->
    GEither
      {}
  sem parenAllowed_DAETopOp : all lstyle. all rstyle. DAETopOp lstyle rstyle -> AllowedDirection
sem parenAllowed_DAETopOp =
  | _ ->
    GEither
      {}
  sem getInfo_DAETopOp : all lstyle. all rstyle. DAETopOp lstyle rstyle -> Info
  sem getTerms_DAETopOp : all lstyle. all rstyle. DAETopOp lstyle rstyle -> [Info]
  sem unsplit_DAETopOp : PermanentNode DAETopOp -> (Info, DAETop)
end
lang DAEProgOpBase =
  DAEParseAst
  syn DAEProgOp lstyle rstyle =
  sem topAllowed_DAEProgOp : all lstyle. all rstyle. DAEProgOp lstyle rstyle -> Bool
sem topAllowed_DAEProgOp =
  | _ ->
    true
  sem leftAllowed_DAEProgOp : all lstyle. all style. all rstyle. {child: DAEProgOp lstyle rstyle, parent: DAEProgOp LOpen style} -> Bool
sem leftAllowed_DAEProgOp =
  | _ ->
    true
  sem rightAllowed_DAEProgOp : all style. all lstyle. all rstyle. {child: DAEProgOp lstyle rstyle, parent: DAEProgOp style ROpen} -> Bool
sem rightAllowed_DAEProgOp =
  | _ ->
    true
  sem groupingsAllowed_DAEProgOp : all lstyle. all rstyle. (DAEProgOp lstyle ROpen, DAEProgOp LOpen rstyle) -> AllowedDirection
sem groupingsAllowed_DAEProgOp =
  | _ ->
    GEither
      {}
  sem parenAllowed_DAEProgOp : all lstyle. all rstyle. DAEProgOp lstyle rstyle -> AllowedDirection
sem parenAllowed_DAEProgOp =
  | _ ->
    GEither
      {}
  sem getInfo_DAEProgOp : all lstyle. all rstyle. DAEProgOp lstyle rstyle -> Info
  sem getTerms_DAEProgOp : all lstyle. all rstyle. DAEProgOp lstyle rstyle -> [Info]
  sem unsplit_DAEProgOp : PermanentNode DAEProgOp -> (Info, DAEProg)
end
lang FloatDAETypeOp =
  DAETypeOpBase
  + FloatDAETypeAst
  syn DAETypeOp lstyle rstyle =
  | FloatDAETypeOp {__br_info: Info, __br_terms: [Info]}
  sem getInfo_DAETypeOp =
  | FloatDAETypeOp x ->
    x.__br_info
  sem getTerms_DAETypeOp =
  | FloatDAETypeOp x ->
    x.__br_terms
  sem unsplit_DAETypeOp =
  | AtomP {self = FloatDAETypeOp x} ->
    (x.__br_info, FloatDAEType
      { info =
          x.__br_info })
end
lang IntDAETypeOp =
  DAETypeOpBase
  + IntDAETypeAst
  syn DAETypeOp lstyle rstyle =
  | IntDAETypeOp {__br_info: Info, __br_terms: [Info]}
  sem getInfo_DAETypeOp =
  | IntDAETypeOp x ->
    x.__br_info
  sem getTerms_DAETypeOp =
  | IntDAETypeOp x ->
    x.__br_terms
  sem unsplit_DAETypeOp =
  | AtomP {self = IntDAETypeOp x} ->
    (x.__br_info, IntDAEType
      { info =
          x.__br_info })
end
lang ArrowDAETypeOp =
  DAETypeOpBase
  + ArrowDAETypeAst
  sem groupingsAllowed_DAETypeOp =
  | (ArrowDAETypeOp _, ArrowDAETypeOp _) ->
    GRight
      {}
  syn DAETypeOp lstyle rstyle =
  | ArrowDAETypeOp {__br_info: Info, __br_terms: [Info]}
  sem getInfo_DAETypeOp =
  | ArrowDAETypeOp x ->
    x.__br_info
  sem getTerms_DAETypeOp =
  | ArrowDAETypeOp x ->
    x.__br_terms
  sem unsplit_DAETypeOp =
  | InfixP {self = ArrowDAETypeOp x, leftChildAlts = [ l ] ++ _ ++ "", rightChildAlts = [ r ] ++ _ ++ ""} ->
    match
      (unsplit_DAETypeOp
        l, unsplit_DAETypeOp
        r)
    with
      ((linfo, l), (rinfo, r))
    in
    let info =
        foldl
          mergeInfo
          linfo
          [ x.__br_info,
            rinfo ]
      in
      (info, ArrowDAEType
        { info =
            info,
          left =
            match
              [ l ]
            with
              [ x1 ] ++ _ ++ ""
            in
            x1,
          right =
            match
              [ r ]
            with
              [ x2 ] ++ _ ++ ""
            in
            x2 })
end
lang FloatDAEConstOp =
  DAEConstOpBase
  + FloatDAEConstAst
  syn DAEConstOp lstyle rstyle =
  | FloatDAEConstOp {val: [{i: Info, v: Float}], __br_info: Info, __br_terms: [Info]}
  sem getInfo_DAEConstOp =
  | FloatDAEConstOp x ->
    x.__br_info
  sem getTerms_DAEConstOp =
  | FloatDAEConstOp x ->
    x.__br_terms
  sem unsplit_DAEConstOp =
  | AtomP {self = FloatDAEConstOp x} ->
    (x.__br_info, FloatDAEConst
      { info =
          x.__br_info,
        val =
          match
            x.val
          with
            [ x1 ] ++ _ ++ ""
          in
          x1 })
end
lang IntDAEConstOp =
  DAEConstOpBase
  + IntDAEConstAst
  syn DAEConstOp lstyle rstyle =
  | IntDAEConstOp {val: [{i: Info, v: Int}], __br_info: Info, __br_terms: [Info]}
  sem getInfo_DAEConstOp =
  | IntDAEConstOp x ->
    x.__br_info
  sem getTerms_DAEConstOp =
  | IntDAEConstOp x ->
    x.__br_terms
  sem unsplit_DAEConstOp =
  | AtomP {self = IntDAEConstOp x} ->
    (x.__br_info, IntDAEConst
      { info =
          x.__br_info,
        val =
          match
            x.val
          with
            [ x1 ] ++ _ ++ ""
          in
          x1 })
end
lang TrueDAEConstOp =
  DAEConstOpBase
  + TrueDAEConstAst
  syn DAEConstOp lstyle rstyle =
  | TrueDAEConstOp {__br_info: Info, __br_terms: [Info]}
  sem getInfo_DAEConstOp =
  | TrueDAEConstOp x ->
    x.__br_info
  sem getTerms_DAEConstOp =
  | TrueDAEConstOp x ->
    x.__br_terms
  sem unsplit_DAEConstOp =
  | AtomP {self = TrueDAEConstOp x} ->
    (x.__br_info, TrueDAEConst
      { info =
          x.__br_info })
end
lang FalseDAEConstOp =
  DAEConstOpBase
  + FalseDAEConstAst
  syn DAEConstOp lstyle rstyle =
  | FalseDAEConstOp {__br_info: Info, __br_terms: [Info]}
  sem getInfo_DAEConstOp =
  | FalseDAEConstOp x ->
    x.__br_info
  sem getTerms_DAEConstOp =
  | FalseDAEConstOp x ->
    x.__br_terms
  sem unsplit_DAEConstOp =
  | AtomP {self = FalseDAEConstOp x} ->
    (x.__br_info, FalseDAEConst
      { info =
          x.__br_info })
end
lang PredDAEConstOp =
  DAEConstOpBase
  + PredDAEConstAst
  syn DAEConstOp lstyle rstyle =
  | PredDAEConstOp {__br_info: Info, __br_terms: [Info]}
  sem getInfo_DAEConstOp =
  | PredDAEConstOp x ->
    x.__br_info
  sem getTerms_DAEConstOp =
  | PredDAEConstOp x ->
    x.__br_terms
  sem unsplit_DAEConstOp =
  | AtomP {self = PredDAEConstOp x} ->
    (x.__br_info, PredDAEConst
      { info =
          x.__br_info })
end
lang ExpDAEConstOp =
  DAEConstOpBase
  + ExpDAEConstAst
  syn DAEConstOp lstyle rstyle =
  | ExpDAEConstOp {__br_info: Info, __br_terms: [Info]}
  sem getInfo_DAEConstOp =
  | ExpDAEConstOp x ->
    x.__br_info
  sem getTerms_DAEConstOp =
  | ExpDAEConstOp x ->
    x.__br_terms
  sem unsplit_DAEConstOp =
  | AtomP {self = ExpDAEConstOp x} ->
    (x.__br_info, ExpDAEConst
      { info =
          x.__br_info })
end
lang SinDAEConstOp =
  DAEConstOpBase
  + SinDAEConstAst
  syn DAEConstOp lstyle rstyle =
  | SinDAEConstOp {__br_info: Info, __br_terms: [Info]}
  sem getInfo_DAEConstOp =
  | SinDAEConstOp x ->
    x.__br_info
  sem getTerms_DAEConstOp =
  | SinDAEConstOp x ->
    x.__br_terms
  sem unsplit_DAEConstOp =
  | AtomP {self = SinDAEConstOp x} ->
    (x.__br_info, SinDAEConst
      { info =
          x.__br_info })
end
lang CosDAEConstOp =
  DAEConstOpBase
  + CosDAEConstAst
  syn DAEConstOp lstyle rstyle =
  | CosDAEConstOp {__br_info: Info, __br_terms: [Info]}
  sem getInfo_DAEConstOp =
  | CosDAEConstOp x ->
    x.__br_info
  sem getTerms_DAEConstOp =
  | CosDAEConstOp x ->
    x.__br_terms
  sem unsplit_DAEConstOp =
  | AtomP {self = CosDAEConstOp x} ->
    (x.__br_info, CosDAEConst
      { info =
          x.__br_info })
end
lang SqrtDAEConstOp =
  DAEConstOpBase
  + SqrtDAEConstAst
  syn DAEConstOp lstyle rstyle =
  | SqrtDAEConstOp {__br_info: Info, __br_terms: [Info]}
  sem getInfo_DAEConstOp =
  | SqrtDAEConstOp x ->
    x.__br_info
  sem getTerms_DAEConstOp =
  | SqrtDAEConstOp x ->
    x.__br_terms
  sem unsplit_DAEConstOp =
  | AtomP {self = SqrtDAEConstOp x} ->
    (x.__br_info, SqrtDAEConst
      { info =
          x.__br_info })
end
lang TupleDAEPatOp =
  DAEPatOpBase
  + TupleDAEPatAst
  syn DAEPatOp lstyle rstyle =
  | TupleDAEPatOp {names: [{i: Info, v: Name}], __br_info: Info, __br_terms: [Info]}
  sem getInfo_DAEPatOp =
  | TupleDAEPatOp x ->
    x.__br_info
  sem getTerms_DAEPatOp =
  | TupleDAEPatOp x ->
    x.__br_terms
  sem unsplit_DAEPatOp =
  | AtomP {self = TupleDAEPatOp x} ->
    (x.__br_info, TupleDAEPat
      { info =
          x.__br_info,
        names =
          x.names })
end
lang VarDAEExprOp =
  DAEExprOpBase
  + VarDAEExprAst
  syn DAEExprOp lstyle rstyle =
  | VarDAEExprOp {name: [{i: Info, v: Name}], __br_info: Info, __br_terms: [Info]}
  sem getInfo_DAEExprOp =
  | VarDAEExprOp x ->
    x.__br_info
  sem getTerms_DAEExprOp =
  | VarDAEExprOp x ->
    x.__br_terms
  sem unsplit_DAEExprOp =
  | AtomP {self = VarDAEExprOp x} ->
    (x.__br_info, VarDAEExpr
      { info =
          x.__br_info,
        name =
          match
            x.name
          with
            [ x1 ] ++ _ ++ ""
          in
          x1 })
end
lang AbsDAEExprOp =
  DAEExprOpBase
  + AbsDAEExprAst
  syn DAEExprOp lstyle rstyle =
  | AbsDAEExprOp {name: [{i: Info, v: Name}], __br_info: Info, __br_terms: [Info]}
  sem getInfo_DAEExprOp =
  | AbsDAEExprOp x ->
    x.__br_info
  sem getTerms_DAEExprOp =
  | AbsDAEExprOp x ->
    x.__br_terms
  sem unsplit_DAEExprOp =
  | PrefixP {self = AbsDAEExprOp x, rightChildAlts = [ r ] ++ _ ++ ""} ->
    match
      unsplit_DAEExprOp
        r
    with
      (rinfo, r)
    in
    let info =
        mergeInfo
          x.__br_info
          rinfo
      in
      (info, AbsDAEExpr
        { info =
            info,
          name =
            match
              x.name
            with
              [ x1 ] ++ _ ++ ""
            in
            x1,
          body =
            match
              [ r ]
            with
              [ x2 ] ++ _ ++ ""
            in
            x2 })
end
lang AppDAEExprOp =
  DAEExprOpBase
  + AppDAEExprAst
  sem groupingsAllowed_DAEExprOp =
  | (AppDAEExprOp _, AppDAEExprOp _) ->
    GLeft
      {}
  syn DAEExprOp lstyle rstyle =
  | AppDAEExprOp {__br_info: Info, __br_terms: [Info]}
  sem getInfo_DAEExprOp =
  | AppDAEExprOp x ->
    x.__br_info
  sem getTerms_DAEExprOp =
  | AppDAEExprOp x ->
    x.__br_terms
  sem unsplit_DAEExprOp =
  | InfixP {self = AppDAEExprOp x, leftChildAlts = [ l ] ++ _ ++ "", rightChildAlts = [ r ] ++ _ ++ ""} ->
    match
      (unsplit_DAEExprOp
        l, unsplit_DAEExprOp
        r)
    with
      ((linfo, l), (rinfo, r))
    in
    let info =
        foldl
          mergeInfo
          linfo
          [ x.__br_info,
            rinfo ]
      in
      (info, AppDAEExpr
        { info =
            info,
          arg =
            match
              [ r ]
            with
              [ x1 ] ++ _ ++ ""
            in
            x1,
          fn =
            match
              [ l ]
            with
              [ x2 ] ++ _ ++ ""
            in
            x2 })
end
lang TupleDAEExprOp =
  DAEExprOpBase
  + TupleDAEExprAst
  syn DAEExprOp lstyle rstyle =
  | TupleDAEExprOp {exprs: [DAEExpr], __br_info: Info, __br_terms: [Info]}
  sem getInfo_DAEExprOp =
  | TupleDAEExprOp x ->
    x.__br_info
  sem getTerms_DAEExprOp =
  | TupleDAEExprOp x ->
    x.__br_terms
  sem unsplit_DAEExprOp =
  | AtomP {self = TupleDAEExprOp x} ->
    (x.__br_info, TupleDAEExpr
      { info =
          x.__br_info,
        exprs =
          x.exprs })
end
lang ProjDAEExprOp =
  DAEExprOpBase
  + ProjDAEExprAst
  syn DAEExprOp lstyle rstyle =
  | ProjDAEExprOp {label: [{i: Info, v: Int}], __br_info: Info, __br_terms: [Info]}
  sem getInfo_DAEExprOp =
  | ProjDAEExprOp x ->
    x.__br_info
  sem getTerms_DAEExprOp =
  | ProjDAEExprOp x ->
    x.__br_terms
  sem unsplit_DAEExprOp =
  | PostfixP {self = ProjDAEExprOp x, leftChildAlts = [ l ] ++ _ ++ ""} ->
    match
      unsplit_DAEExprOp
        l
    with
      (linfo, l)
    in
    let info =
        mergeInfo
          linfo
          x.__br_info
      in
      (info, ProjDAEExpr
        { info =
            info,
          label =
            match
              x.label
            with
              [ x1 ] ++ _ ++ ""
            in
            x1,
          expr =
            match
              [ l ]
            with
              [ x2 ] ++ _ ++ ""
            in
            x2 })
end
lang ConstDAEExprOp =
  DAEExprOpBase
  + ConstDAEExprAst
  syn DAEExprOp lstyle rstyle =
  | ConstDAEExprOp {val: [DAEConst], __br_info: Info, __br_terms: [Info]}
  sem getInfo_DAEExprOp =
  | ConstDAEExprOp x ->
    x.__br_info
  sem getTerms_DAEExprOp =
  | ConstDAEExprOp x ->
    x.__br_terms
  sem unsplit_DAEExprOp =
  | AtomP {self = ConstDAEExprOp x} ->
    (x.__br_info, ConstDAEExpr
      { info =
          x.__br_info,
        val =
          match
            x.val
          with
            [ x1 ] ++ _ ++ ""
          in
          x1 })
end
lang AddDAEExprOp =
  DAEExprOpBase
  + AddDAEExprAst
  sem groupingsAllowed_DAEExprOp =
  | (AddDAEExprOp _, AddDAEExprOp _) ->
    GLeft
      {}
  syn DAEExprOp lstyle rstyle =
  | AddDAEExprOp {__br_info: Info, __br_terms: [Info]}
  sem getInfo_DAEExprOp =
  | AddDAEExprOp x ->
    x.__br_info
  sem getTerms_DAEExprOp =
  | AddDAEExprOp x ->
    x.__br_terms
  sem unsplit_DAEExprOp =
  | InfixP {self = AddDAEExprOp x, leftChildAlts = [ l ] ++ _ ++ "", rightChildAlts = [ r ] ++ _ ++ ""} ->
    match
      (unsplit_DAEExprOp
        l, unsplit_DAEExprOp
        r)
    with
      ((linfo, l), (rinfo, r))
    in
    let info =
        foldl
          mergeInfo
          linfo
          [ x.__br_info,
            rinfo ]
      in
      (info, AddDAEExpr
        { info =
            info,
          left =
            match
              [ l ]
            with
              [ x1 ] ++ _ ++ ""
            in
            x1,
          right =
            match
              [ r ]
            with
              [ x2 ] ++ _ ++ ""
            in
            x2 })
end
lang SubDAEExprOp =
  DAEExprOpBase
  + SubDAEExprAst
  sem groupingsAllowed_DAEExprOp =
  | (SubDAEExprOp _, SubDAEExprOp _) ->
    GLeft
      {}
  syn DAEExprOp lstyle rstyle =
  | SubDAEExprOp {__br_info: Info, __br_terms: [Info]}
  sem getInfo_DAEExprOp =
  | SubDAEExprOp x ->
    x.__br_info
  sem getTerms_DAEExprOp =
  | SubDAEExprOp x ->
    x.__br_terms
  sem unsplit_DAEExprOp =
  | InfixP {self = SubDAEExprOp x, leftChildAlts = [ l ] ++ _ ++ "", rightChildAlts = [ r ] ++ _ ++ ""} ->
    match
      (unsplit_DAEExprOp
        l, unsplit_DAEExprOp
        r)
    with
      ((linfo, l), (rinfo, r))
    in
    let info =
        foldl
          mergeInfo
          linfo
          [ x.__br_info,
            rinfo ]
      in
      (info, SubDAEExpr
        { info =
            info,
          left =
            match
              [ l ]
            with
              [ x1 ] ++ _ ++ ""
            in
            x1,
          right =
            match
              [ r ]
            with
              [ x2 ] ++ _ ++ ""
            in
            x2 })
end
lang MulDAEExprOp =
  DAEExprOpBase
  + MulDAEExprAst
  sem groupingsAllowed_DAEExprOp =
  | (MulDAEExprOp _, MulDAEExprOp _) ->
    GLeft
      {}
  syn DAEExprOp lstyle rstyle =
  | MulDAEExprOp {__br_info: Info, __br_terms: [Info]}
  sem getInfo_DAEExprOp =
  | MulDAEExprOp x ->
    x.__br_info
  sem getTerms_DAEExprOp =
  | MulDAEExprOp x ->
    x.__br_terms
  sem unsplit_DAEExprOp =
  | InfixP {self = MulDAEExprOp x, leftChildAlts = [ l ] ++ _ ++ "", rightChildAlts = [ r ] ++ _ ++ ""} ->
    match
      (unsplit_DAEExprOp
        l, unsplit_DAEExprOp
        r)
    with
      ((linfo, l), (rinfo, r))
    in
    let info =
        foldl
          mergeInfo
          linfo
          [ x.__br_info,
            rinfo ]
      in
      (info, MulDAEExpr
        { info =
            info,
          left =
            match
              [ l ]
            with
              [ x1 ] ++ _ ++ ""
            in
            x1,
          right =
            match
              [ r ]
            with
              [ x2 ] ++ _ ++ ""
            in
            x2 })
end
lang DivDAEExprOp =
  DAEExprOpBase
  + DivDAEExprAst
  sem groupingsAllowed_DAEExprOp =
  | (DivDAEExprOp _, DivDAEExprOp _) ->
    GLeft
      {}
  syn DAEExprOp lstyle rstyle =
  | DivDAEExprOp {__br_info: Info, __br_terms: [Info]}
  sem getInfo_DAEExprOp =
  | DivDAEExprOp x ->
    x.__br_info
  sem getTerms_DAEExprOp =
  | DivDAEExprOp x ->
    x.__br_terms
  sem unsplit_DAEExprOp =
  | InfixP {self = DivDAEExprOp x, leftChildAlts = [ l ] ++ _ ++ "", rightChildAlts = [ r ] ++ _ ++ ""} ->
    match
      (unsplit_DAEExprOp
        l, unsplit_DAEExprOp
        r)
    with
      ((linfo, l), (rinfo, r))
    in
    let info =
        foldl
          mergeInfo
          linfo
          [ x.__br_info,
            rinfo ]
      in
      (info, DivDAEExpr
        { info =
            info,
          left =
            match
              [ l ]
            with
              [ x1 ] ++ _ ++ ""
            in
            x1,
          right =
            match
              [ r ]
            with
              [ x2 ] ++ _ ++ ""
            in
            x2 })
end
lang LtDAEExprOp =
  DAEExprOpBase
  + LtDAEExprAst
  sem groupingsAllowed_DAEExprOp =
  | (LtDAEExprOp _, LtDAEExprOp _) ->
    GLeft
      {}
  syn DAEExprOp lstyle rstyle =
  | LtDAEExprOp {__br_info: Info, __br_terms: [Info]}
  sem getInfo_DAEExprOp =
  | LtDAEExprOp x ->
    x.__br_info
  sem getTerms_DAEExprOp =
  | LtDAEExprOp x ->
    x.__br_terms
  sem unsplit_DAEExprOp =
  | InfixP {self = LtDAEExprOp x, leftChildAlts = [ l ] ++ _ ++ "", rightChildAlts = [ r ] ++ _ ++ ""} ->
    match
      (unsplit_DAEExprOp
        l, unsplit_DAEExprOp
        r)
    with
      ((linfo, l), (rinfo, r))
    in
    let info =
        foldl
          mergeInfo
          linfo
          [ x.__br_info,
            rinfo ]
      in
      (info, LtDAEExpr
        { info =
            info,
          left =
            match
              [ l ]
            with
              [ x1 ] ++ _ ++ ""
            in
            x1,
          right =
            match
              [ r ]
            with
              [ x2 ] ++ _ ++ ""
            in
            x2 })
end
lang LtfDAEExprOp =
  DAEExprOpBase
  + LtfDAEExprAst
  sem groupingsAllowed_DAEExprOp =
  | (LtfDAEExprOp _, LtfDAEExprOp _) ->
    GLeft
      {}
  syn DAEExprOp lstyle rstyle =
  | LtfDAEExprOp {__br_info: Info, __br_terms: [Info]}
  sem getInfo_DAEExprOp =
  | LtfDAEExprOp x ->
    x.__br_info
  sem getTerms_DAEExprOp =
  | LtfDAEExprOp x ->
    x.__br_terms
  sem unsplit_DAEExprOp =
  | InfixP {self = LtfDAEExprOp x, leftChildAlts = [ l ] ++ _ ++ "", rightChildAlts = [ r ] ++ _ ++ ""} ->
    match
      (unsplit_DAEExprOp
        l, unsplit_DAEExprOp
        r)
    with
      ((linfo, l), (rinfo, r))
    in
    let info =
        foldl
          mergeInfo
          linfo
          [ x.__br_info,
            rinfo ]
      in
      (info, LtfDAEExpr
        { info =
            info,
          left =
            match
              [ l ]
            with
              [ x1 ] ++ _ ++ ""
            in
            x1,
          right =
            match
              [ r ]
            with
              [ x2 ] ++ _ ++ ""
            in
            x2 })
end
lang EqDAEExprOp =
  DAEExprOpBase
  + EqDAEExprAst
  sem groupingsAllowed_DAEExprOp =
  | (EqDAEExprOp _, EqDAEExprOp _) ->
    GLeft
      {}
  syn DAEExprOp lstyle rstyle =
  | EqDAEExprOp {__br_info: Info, __br_terms: [Info]}
  sem getInfo_DAEExprOp =
  | EqDAEExprOp x ->
    x.__br_info
  sem getTerms_DAEExprOp =
  | EqDAEExprOp x ->
    x.__br_terms
  sem unsplit_DAEExprOp =
  | InfixP {self = EqDAEExprOp x, leftChildAlts = [ l ] ++ _ ++ "", rightChildAlts = [ r ] ++ _ ++ ""} ->
    match
      (unsplit_DAEExprOp
        l, unsplit_DAEExprOp
        r)
    with
      ((linfo, l), (rinfo, r))
    in
    let info =
        foldl
          mergeInfo
          linfo
          [ x.__br_info,
            rinfo ]
      in
      (info, EqDAEExpr
        { info =
            info,
          left =
            match
              [ l ]
            with
              [ x1 ] ++ _ ++ ""
            in
            x1,
          right =
            match
              [ r ]
            with
              [ x2 ] ++ _ ++ ""
            in
            x2 })
end
lang NegDAEExprOp =
  DAEExprOpBase
  + NegDAEExprAst
  syn DAEExprOp lstyle rstyle =
  | NegDAEExprOp {__br_info: Info, __br_terms: [Info]}
  sem getInfo_DAEExprOp =
  | NegDAEExprOp x ->
    x.__br_info
  sem getTerms_DAEExprOp =
  | NegDAEExprOp x ->
    x.__br_terms
  sem unsplit_DAEExprOp =
  | PrefixP {self = NegDAEExprOp x, rightChildAlts = [ r ] ++ _ ++ ""} ->
    match
      unsplit_DAEExprOp
        r
    with
      (rinfo, r)
    in
    let info =
        mergeInfo
          x.__br_info
          rinfo
      in
      (info, NegDAEExpr
        { info =
            info,
          right =
            match
              [ r ]
            with
              [ x1 ] ++ _ ++ ""
            in
            x1 })
end
lang MatchInDAEExprOp =
  DAEExprOpBase
  + MatchInDAEExprAst
  syn DAEExprOp lstyle rstyle =
  | MatchInDAEExprOp {pat: [DAEPat], target: [DAEExpr], __br_info: Info, __br_terms: [Info]}
  sem getInfo_DAEExprOp =
  | MatchInDAEExprOp x ->
    x.__br_info
  sem getTerms_DAEExprOp =
  | MatchInDAEExprOp x ->
    x.__br_terms
  sem unsplit_DAEExprOp =
  | PrefixP {self = MatchInDAEExprOp x, rightChildAlts = [ r ] ++ _ ++ ""} ->
    match
      unsplit_DAEExprOp
        r
    with
      (rinfo, r)
    in
    let info =
        mergeInfo
          x.__br_info
          rinfo
      in
      (info, MatchInDAEExpr
        { info =
            info,
          pat =
            match
              x.pat
            with
              [ x1 ] ++ _ ++ ""
            in
            x1,
          target =
            match
              x.target
            with
              [ x2 ] ++ _ ++ ""
            in
            x2,
          body =
            match
              [ r ]
            with
              [ x3 ] ++ _ ++ ""
            in
            x3 })
end
lang IfDAEExprOp =
  DAEExprOpBase
  + IfDAEExprAst
  syn DAEExprOp lstyle rstyle =
  | IfDAEExprOp {thn: [DAEExpr], pred: [DAEExpr], __br_info: Info, __br_terms: [Info]}
  sem getInfo_DAEExprOp =
  | IfDAEExprOp x ->
    x.__br_info
  sem getTerms_DAEExprOp =
  | IfDAEExprOp x ->
    x.__br_terms
  sem unsplit_DAEExprOp =
  | PrefixP {self = IfDAEExprOp x, rightChildAlts = [ r ] ++ _ ++ ""} ->
    match
      unsplit_DAEExprOp
        r
    with
      (rinfo, r)
    in
    let info =
        mergeInfo
          x.__br_info
          rinfo
      in
      (info, IfDAEExpr
        { info =
            info,
          thn =
            match
              x.thn
            with
              [ x1 ] ++ _ ++ ""
            in
            x1,
          pred =
            match
              x.pred
            with
              [ x2 ] ++ _ ++ ""
            in
            x2,
          els =
            match
              [ r ]
            with
              [ x3 ] ++ _ ++ ""
            in
            x3 })
end
lang LetDAEExprOp =
  DAEExprOpBase
  + LetDAEExprAst
  syn DAEExprOp lstyle rstyle =
  | LetDAEExprOp {arg: [DAEExpr], name: [{i: Info, v: Name}], __br_info: Info, __br_terms: [Info]}
  sem getInfo_DAEExprOp =
  | LetDAEExprOp x ->
    x.__br_info
  sem getTerms_DAEExprOp =
  | LetDAEExprOp x ->
    x.__br_terms
  sem unsplit_DAEExprOp =
  | PrefixP {self = LetDAEExprOp x, rightChildAlts = [ r ] ++ _ ++ ""} ->
    match
      unsplit_DAEExprOp
        r
    with
      (rinfo, r)
    in
    let info =
        mergeInfo
          x.__br_info
          rinfo
      in
      (info, LetDAEExpr
        { info =
            info,
          name =
            match
              x.name
            with
              [ x1 ] ++ _ ++ ""
            in
            x1,
          arg =
            match
              x.arg
            with
              [ x2 ] ++ _ ++ ""
            in
            x2,
          body =
            match
              [ r ]
            with
              [ x3 ] ++ _ ++ ""
            in
            x3 })
end
lang RecLetDAEExprOp =
  DAEExprOpBase
  + RecLetDAEExprAst
  syn DAEExprOp lstyle rstyle =
  | RecLetDAEExprOp {arg: [DAEExpr], name: [{i: Info, v: Name}], __br_info: Info, __br_terms: [Info]}
  sem getInfo_DAEExprOp =
  | RecLetDAEExprOp x ->
    x.__br_info
  sem getTerms_DAEExprOp =
  | RecLetDAEExprOp x ->
    x.__br_terms
  sem unsplit_DAEExprOp =
  | PrefixP {self = RecLetDAEExprOp x, rightChildAlts = [ r ] ++ _ ++ ""} ->
    match
      unsplit_DAEExprOp
        r
    with
      (rinfo, r)
    in
    let info =
        mergeInfo
          x.__br_info
          rinfo
      in
      (info, RecLetDAEExpr
        { info =
            info,
          name =
            match
              x.name
            with
              [ x1 ] ++ _ ++ ""
            in
            x1,
          arg =
            match
              x.arg
            with
              [ x2 ] ++ _ ++ ""
            in
            x2,
          body =
            match
              [ r ]
            with
              [ x3 ] ++ _ ++ ""
            in
            x3 })
end
lang PrimDAEExprOp =
  DAEExprOpBase
  + PrimDAEExprAst
  syn DAEExprOp lstyle rstyle =
  | PrimDAEExprOp {__br_info: Info, __br_terms: [Info]}
  sem getInfo_DAEExprOp =
  | PrimDAEExprOp x ->
    x.__br_info
  sem getTerms_DAEExprOp =
  | PrimDAEExprOp x ->
    x.__br_terms
  sem unsplit_DAEExprOp =
  | PostfixP {self = PrimDAEExprOp x, leftChildAlts = [ l ] ++ _ ++ ""} ->
    match
      unsplit_DAEExprOp
        l
    with
      (linfo, l)
    in
    let info =
        mergeInfo
          linfo
          x.__br_info
      in
      (info, PrimDAEExpr
        { info =
            info,
          left =
            match
              [ l ]
            with
              [ x1 ] ++ _ ++ ""
            in
            x1 })
end
lang EqnDAEEqnOp =
  DAEEqnOpBase
  + EqnDAEEqnAst
  syn DAEEqnOp lstyle rstyle =
  | EqnDAEEqnOp {left: [DAEExpr], right: [DAEExpr], __br_info: Info, __br_terms: [Info]}
  sem getInfo_DAEEqnOp =
  | EqnDAEEqnOp x ->
    x.__br_info
  sem getTerms_DAEEqnOp =
  | EqnDAEEqnOp x ->
    x.__br_terms
  sem unsplit_DAEEqnOp =
  | AtomP {self = EqnDAEEqnOp x} ->
    (x.__br_info, EqnDAEEqn
      { info =
          x.__br_info,
        left =
          match
            x.left
          with
            [ x1 ] ++ _ ++ ""
          in
          x1,
        right =
          match
            x.right
          with
            [ x2 ] ++ _ ++ ""
          in
          x2 })
end
lang VarsDAEVarOp =
  DAEVarOpBase
  + VarsDAEVarAst
  syn DAEVarOp lstyle rstyle =
  | VarsDAEVarOp {ty: [DAEType], names: [{i: Info, v: Name}], __br_info: Info, __br_terms: [Info]}
  sem getInfo_DAEVarOp =
  | VarsDAEVarOp x ->
    x.__br_info
  sem getTerms_DAEVarOp =
  | VarsDAEVarOp x ->
    x.__br_terms
  sem unsplit_DAEVarOp =
  | AtomP {self = VarsDAEVarOp x} ->
    (x.__br_info, VarsDAEVar
      { info =
          x.__br_info,
        names =
          x.names,
        ty =
          match
            x.ty
          with
            [ x1 ] ++ _ ++ ""
          in
          x1 })
end
lang LetDAETopOp =
  DAETopOpBase
  + LetDAETopAst
  syn DAETopOp lstyle rstyle =
  | LetDAETopOp {arg: [DAEExpr], name: [{i: Info, v: Name}], __br_info: Info, __br_terms: [Info]}
  sem getInfo_DAETopOp =
  | LetDAETopOp x ->
    x.__br_info
  sem getTerms_DAETopOp =
  | LetDAETopOp x ->
    x.__br_terms
  sem unsplit_DAETopOp =
  | AtomP {self = LetDAETopOp x} ->
    (x.__br_info, LetDAETop
      { info =
          x.__br_info,
        name =
          match
            x.name
          with
            [ x1 ] ++ _ ++ ""
          in
          x1,
        arg =
          match
            x.arg
          with
            [ x2 ] ++ _ ++ ""
          in
          x2 })
end
lang RecLetDAETopOp =
  DAETopOpBase
  + RecLetDAETopAst
  syn DAETopOp lstyle rstyle =
  | RecLetDAETopOp {arg: [DAEExpr], name: [{i: Info, v: Name}], __br_info: Info, __br_terms: [Info]}
  sem getInfo_DAETopOp =
  | RecLetDAETopOp x ->
    x.__br_info
  sem getTerms_DAETopOp =
  | RecLetDAETopOp x ->
    x.__br_terms
  sem unsplit_DAETopOp =
  | AtomP {self = RecLetDAETopOp x} ->
    (x.__br_info, RecLetDAETop
      { info =
          x.__br_info,
        name =
          match
            x.name
          with
            [ x1 ] ++ _ ++ ""
          in
          x1,
        arg =
          match
            x.arg
          with
            [ x2 ] ++ _ ++ ""
          in
          x2 })
end
lang ProgDAEProgOp =
  DAEProgOpBase
  + ProgDAEProgAst
  syn DAEProgOp lstyle rstyle =
  | ProgDAEProgOp {eqns: [DAEEqn], tops: [DAETop], vars: [DAEVar], ieqns: [DAEEqn], output: [DAEExpr], __br_info: Info, __br_terms: [Info]}
  sem getInfo_DAEProgOp =
  | ProgDAEProgOp x ->
    x.__br_info
  sem getTerms_DAEProgOp =
  | ProgDAEProgOp x ->
    x.__br_terms
  sem unsplit_DAEProgOp =
  | AtomP {self = ProgDAEProgOp x} ->
    (x.__br_info, ProgDAEProg
      { info =
          x.__br_info,
        tops =
          x.tops,
        vars =
          x.vars,
        ieqns =
          x.ieqns,
        eqns =
          x.eqns,
        output =
          match
            x.output
          with
            [ x1 ] ++ _ ++ ""
          in
          x1 })
end
lang DAEExprGrouping =
  DAEExprOpBase
  syn DAEExprOp lstyle rstyle =
  | DAEExprGrouping {inner: DAEExpr, __br_info: Info, __br_terms: [Info]}
  sem getInfo_DAEExprOp =
  | DAEExprGrouping x ->
    x.__br_info
  sem getTerms_DAEExprOp =
  | DAEExprGrouping x ->
    x.__br_terms
  sem unsplit_DAEExprOp =
  | AtomP {self = DAEExprGrouping x} ->
    (x.__br_info, x.inner)
end
lang ParseDAEParse =
  FloatDAETypeOp
  + IntDAETypeOp
  + ArrowDAETypeOp
  + FloatDAEConstOp
  + IntDAEConstOp
  + TrueDAEConstOp
  + FalseDAEConstOp
  + PredDAEConstOp
  + ExpDAEConstOp
  + SinDAEConstOp
  + CosDAEConstOp
  + SqrtDAEConstOp
  + TupleDAEPatOp
  + VarDAEExprOp
  + AbsDAEExprOp
  + AppDAEExprOp
  + TupleDAEExprOp
  + ProjDAEExprOp
  + ConstDAEExprOp
  + AddDAEExprOp
  + SubDAEExprOp
  + MulDAEExprOp
  + DivDAEExprOp
  + LtDAEExprOp
  + LtfDAEExprOp
  + EqDAEExprOp
  + NegDAEExprOp
  + MatchInDAEExprOp
  + IfDAEExprOp
  + LetDAEExprOp
  + RecLetDAEExprOp
  + PrimDAEExprOp
  + EqnDAEEqnOp
  + VarsDAEVarOp
  + LetDAETopOp
  + RecLetDAETopOp
  + ProgDAEProgOp
  + DAEExprGrouping
  + BadDAETypeAst
  + BadDAEConstAst
  + BadDAEPatAst
  + BadDAEExprAst
  + BadDAEEqnAst
  + BadDAEVarAst
  + BadDAETopAst
  + BadDAEProgAst
  + LL1Parser
  + SemiTokenParser
  + UIntTokenParser
  + CommaTokenParser
  + PrimeTokenParser
  + WhitespaceParser
  + LIdentTokenParser
  + LineCommentParser
  + StringTokenParser
  + UFloatTokenParser
  + UIdentTokenParser
  + BracketTokenParser
  + OperatorTokenParser
  + MultilineCommentParser
  
  
  
  sem groupingsAllowed_DAEExprOp =
  | (AbsDAEExprOp _, AppDAEExprOp _) ->
    GRight
      {}
  | (AbsDAEExprOp _, ProjDAEExprOp _) ->
    GRight
      {}
  | (AbsDAEExprOp _, AddDAEExprOp _) ->
    GRight
      {}
  | (AbsDAEExprOp _, SubDAEExprOp _) ->
    GRight
      {}
  | (AbsDAEExprOp _, MulDAEExprOp _) ->
    GRight
      {}
  | (AbsDAEExprOp _, DivDAEExprOp _) ->
    GRight
      {}
  | (AbsDAEExprOp _, LtDAEExprOp _) ->
    GRight
      {}
  | (AbsDAEExprOp _, PrimDAEExprOp _) ->
    GRight
      {}
  | (AppDAEExprOp _, ProjDAEExprOp _) ->
    GRight
      {}
  | (AppDAEExprOp _, AddDAEExprOp _) ->
    GLeft
      {}
  | (AddDAEExprOp _, AppDAEExprOp _) ->
    GRight
      {}
  | (AppDAEExprOp _, SubDAEExprOp _) ->
    GLeft
      {}
  | (SubDAEExprOp _, AppDAEExprOp _) ->
    GRight
      {}
  | (AppDAEExprOp _, MulDAEExprOp _) ->
    GLeft
      {}
  | (MulDAEExprOp _, AppDAEExprOp _) ->
    GRight
      {}
  | (AppDAEExprOp _, DivDAEExprOp _) ->
    GLeft
      {}
  | (DivDAEExprOp _, AppDAEExprOp _) ->
    GRight
      {}
  | (AppDAEExprOp _, LtDAEExprOp _) ->
    GLeft
      {}
  | (LtDAEExprOp _, AppDAEExprOp _) ->
    GRight
      {}
  | (NegDAEExprOp _, AppDAEExprOp _) ->
    GLeft
      {}
  | (IfDAEExprOp _, AppDAEExprOp _) ->
    GRight
      {}
  | (AppDAEExprOp _, PrimDAEExprOp _) ->
    GRight
      {}
  | (AddDAEExprOp _, ProjDAEExprOp _) ->
    GRight
      {}
  | (SubDAEExprOp _, ProjDAEExprOp _) ->
    GRight
      {}
  | (MulDAEExprOp _, ProjDAEExprOp _) ->
    GRight
      {}
  | (DivDAEExprOp _, ProjDAEExprOp _) ->
    GRight
      {}
  | (LtDAEExprOp _, ProjDAEExprOp _) ->
    GRight
      {}
  | (NegDAEExprOp _, ProjDAEExprOp _) ->
    GRight
      {}
  | (IfDAEExprOp _, ProjDAEExprOp _) ->
    GRight
      {}
  | (AddDAEExprOp _, SubDAEExprOp _) ->
    GLeft
      {}
  | (SubDAEExprOp _, AddDAEExprOp _) ->
    GLeft
      {}
  | (AddDAEExprOp _, MulDAEExprOp _) ->
    GRight
      {}
  | (MulDAEExprOp _, AddDAEExprOp _) ->
    GLeft
      {}
  | (AddDAEExprOp _, DivDAEExprOp _) ->
    GRight
      {}
  | (DivDAEExprOp _, AddDAEExprOp _) ->
    GLeft
      {}
  | (AddDAEExprOp _, LtDAEExprOp _) ->
    GLeft
      {}
  | (LtDAEExprOp _, AddDAEExprOp _) ->
    GRight
      {}
  | (NegDAEExprOp _, AddDAEExprOp _) ->
    GLeft
      {}
  | (IfDAEExprOp _, AddDAEExprOp _) ->
    GRight
      {}
  | (AddDAEExprOp _, PrimDAEExprOp _) ->
    GRight
      {}
  | (SubDAEExprOp _, MulDAEExprOp _) ->
    GRight
      {}
  | (MulDAEExprOp _, SubDAEExprOp _) ->
    GLeft
      {}
  | (SubDAEExprOp _, DivDAEExprOp _) ->
    GRight
      {}
  | (DivDAEExprOp _, SubDAEExprOp _) ->
    GLeft
      {}
  | (SubDAEExprOp _, LtDAEExprOp _) ->
    GLeft
      {}
  | (LtDAEExprOp _, SubDAEExprOp _) ->
    GRight
      {}
  | (NegDAEExprOp _, SubDAEExprOp _) ->
    GLeft
      {}
  | (IfDAEExprOp _, SubDAEExprOp _) ->
    GRight
      {}
  | (SubDAEExprOp _, PrimDAEExprOp _) ->
    GRight
      {}
  | (MulDAEExprOp _, DivDAEExprOp _) ->
    GLeft
      {}
  | (DivDAEExprOp _, MulDAEExprOp _) ->
    GLeft
      {}
  | (MulDAEExprOp _, LtDAEExprOp _) ->
    GLeft
      {}
  | (LtDAEExprOp _, MulDAEExprOp _) ->
    GRight
      {}
  | (NegDAEExprOp _, MulDAEExprOp _) ->
    GLeft
      {}
  | (IfDAEExprOp _, MulDAEExprOp _) ->
    GRight
      {}
  | (MulDAEExprOp _, PrimDAEExprOp _) ->
    GRight
      {}
  | (DivDAEExprOp _, LtDAEExprOp _) ->
    GLeft
      {}
  | (LtDAEExprOp _, DivDAEExprOp _) ->
    GRight
      {}
  | (NegDAEExprOp _, DivDAEExprOp _) ->
    GLeft
      {}
  | (IfDAEExprOp _, DivDAEExprOp _) ->
    GRight
      {}
  | (DivDAEExprOp _, PrimDAEExprOp _) ->
    GRight
      {}
  | (NegDAEExprOp _, LtDAEExprOp _) ->
    GLeft
      {}
  | (IfDAEExprOp _, LtDAEExprOp _) ->
    GRight
      {}
  | (LtDAEExprOp _, PrimDAEExprOp _) ->
    GRight
      {}
  | (NegDAEExprOp _, PrimDAEExprOp _) ->
    GRight
      {}
  | (IfDAEExprOp _, PrimDAEExprOp _) ->
    GRight
      {}
  
  
  
  
end
let _table =
  use ParseDAEParse
  in
  let target =
    genParsingTable
      (let #var"DAEType" =
         nameSym
           "DAEType"
       in
       let #var"DAEConst" =
         nameSym
           "DAEConst"
       in
       let #var"DAEPat" =
         nameSym
           "DAEPat"
       in
       let #var"DAEExpr" =
         nameSym
           "DAEExpr"
       in
       let #var"DAEEqn" =
         nameSym
           "DAEEqn"
       in
       let #var"DAEVar" =
         nameSym
           "DAEVar"
       in
       let #var"DAETop" =
         nameSym
           "DAETop"
       in
       let #var"DAEProg" =
         nameSym
           "DAEProg"
       in
       let #var"DAETypePostfix" =
         nameSym
           "DAETypePostfix"
       in
       let #var"DAETypePrefix" =
         nameSym
           "DAETypePrefix"
       in
       let #var"DAETypeInfix" =
         nameSym
           "DAETypeInfix"
       in
       let #var"DAETypeAtom" =
         nameSym
           "DAETypeAtom"
       in
       let #var"DAEConstPostfix" =
         nameSym
           "DAEConstPostfix"
       in
       let #var"DAEConstPrefix" =
         nameSym
           "DAEConstPrefix"
       in
       let #var"DAEConstInfix" =
         nameSym
           "DAEConstInfix"
       in
       let #var"DAEConstAtom" =
         nameSym
           "DAEConstAtom"
       in
       let #var"DAEPatPostfix" =
         nameSym
           "DAEPatPostfix"
       in
       let #var"DAEPatPrefix" =
         nameSym
           "DAEPatPrefix"
       in
       let #var"DAEPatInfix" =
         nameSym
           "DAEPatInfix"
       in
       let #var"DAEPatAtom" =
         nameSym
           "DAEPatAtom"
       in
       let #var"DAEExprPostfix" =
         nameSym
           "DAEExprPostfix"
       in
       let #var"DAEExprPrefix" =
         nameSym
           "DAEExprPrefix"
       in
       let #var"DAEExprInfix" =
         nameSym
           "DAEExprInfix"
       in
       let #var"DAEExprAtom" =
         nameSym
           "DAEExprAtom"
       in
       let #var"DAEEqnPostfix" =
         nameSym
           "DAEEqnPostfix"
       in
       let #var"DAEEqnPrefix" =
         nameSym
           "DAEEqnPrefix"
       in
       let #var"DAEEqnInfix" =
         nameSym
           "DAEEqnInfix"
       in
       let #var"DAEEqnAtom" =
         nameSym
           "DAEEqnAtom"
       in
       let #var"DAEVarPostfix" =
         nameSym
           "DAEVarPostfix"
       in
       let #var"DAEVarPrefix" =
         nameSym
           "DAEVarPrefix"
       in
       let #var"DAEVarInfix" =
         nameSym
           "DAEVarInfix"
       in
       let #var"DAEVarAtom" =
         nameSym
           "DAEVarAtom"
       in
       let #var"DAETopPostfix" =
         nameSym
           "DAETopPostfix"
       in
       let #var"DAETopPrefix" =
         nameSym
           "DAETopPrefix"
       in
       let #var"DAETopInfix" =
         nameSym
           "DAETopInfix"
       in
       let #var"DAETopAtom" =
         nameSym
           "DAETopAtom"
       in
       let #var"DAEProgPostfix" =
         nameSym
           "DAEProgPostfix"
       in
       let #var"DAEProgPrefix" =
         nameSym
           "DAEProgPrefix"
       in
       let #var"DAEProgInfix" =
         nameSym
           "DAEProgInfix"
       in
       let #var"DAEProgAtom" =
         nameSym
           "DAEProgAtom"
       in
       let kleene =
         nameSym
           "kleene"
       in
       let alt =
         nameSym
           "alt"
       in
       let kleene1 =
         nameSym
           "kleene"
       in
       let alt1 =
         nameSym
           "alt"
       in
       let kleene2 =
         nameSym
           "kleene"
       in
       let kleene3 =
         nameSym
           "kleene"
       in
       let kleene4 =
         nameSym
           "kleene"
       in
       let kleene5 =
         nameSym
           "kleene"
       in
       let alt2 =
         nameSym
           "alt"
       in
       let kleene6 =
         nameSym
           "kleene"
       in
       let #var"DAEType_lclosed" =
         nameSym
           "DAEType_lclosed"
       in
       let #var"DAEType_lopen" =
         nameSym
           "DAEType_lopen"
       in
       let #var"DAEConst_lclosed" =
         nameSym
           "DAEConst_lclosed"
       in
       let #var"DAEConst_lopen" =
         nameSym
           "DAEConst_lopen"
       in
       let #var"DAEPat_lclosed" =
         nameSym
           "DAEPat_lclosed"
       in
       let #var"DAEPat_lopen" =
         nameSym
           "DAEPat_lopen"
       in
       let #var"DAEExpr_lclosed" =
         nameSym
           "DAEExpr_lclosed"
       in
       let #var"DAEExpr_lopen" =
         nameSym
           "DAEExpr_lopen"
       in
       let #var"DAEEqn_lclosed" =
         nameSym
           "DAEEqn_lclosed"
       in
       let #var"DAEEqn_lopen" =
         nameSym
           "DAEEqn_lopen"
       in
       let #var"DAEVar_lclosed" =
         nameSym
           "DAEVar_lclosed"
       in
       let #var"DAEVar_lopen" =
         nameSym
           "DAEVar_lopen"
       in
       let #var"DAETop_lclosed" =
         nameSym
           "DAETop_lclosed"
       in
       let #var"DAETop_lopen" =
         nameSym
           "DAETop_lopen"
       in
       let #var"DAEProg_lclosed" =
         nameSym
           "DAEProg_lclosed"
       in
       let #var"DAEProg_lopen" =
         nameSym
           "DAEProg_lopen"
       in
       { start =
           #var"DAEProg",
         productions =
           let config =
             { parenAllowed =
                 #frozen"parenAllowed_DAETypeOp",
               topAllowed =
                 #frozen"topAllowed_DAETypeOp",
               leftAllowed =
                 #frozen"leftAllowed_DAETypeOp",
               rightAllowed =
                 #frozen"rightAllowed_DAETypeOp",
               groupingsAllowed =
                 #frozen"groupingsAllowed_DAETypeOp" }
           in
           let reportConfig =
             { parenAllowed =
                 #frozen"parenAllowed_DAETypeOp",
               topAllowed =
                 #frozen"topAllowed_DAETypeOp",
               terminalInfos =
                 #frozen"getTerms_DAETypeOp",
               getInfo =
                 #frozen"getInfo_DAETypeOp",
               lpar =
                 "(",
               rpar =
                 ")" }
           in
           let addDAETypeOpAtom =
             lam #var"".
               lam x13.
                 lam st.
                   optionMap
                     (breakableAddAtom
                        config
                        x13)
                     st
           in
           let addDAETypeOpInfix =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam x13.
                 lam st.
                   match
                     st
                   with
                     Some st
                   then
                     let st =
                       breakableAddInfix
                         config
                         x13
                         st
                     in
                     (match
                          st
                        with
                          None _
                        then
                          modref
                            p.errors
                            (snoc
                               (deref
                                  p.errors)
                               (getInfo_DAETypeOp
                                 x13, "Invalid input"))
                        else
                          {})
                     ; st
                   else
                     None
                       {}
           in
           let addDAETypeOpPrefix =
             lam #var"".
               lam x13.
                 lam st.
                   optionMap
                     (breakableAddPrefix
                        config
                        x13)
                     st
           in
           let addDAETypeOpPostfix =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam x13.
                 lam st.
                   match
                     st
                   with
                     Some st
                   then
                     let st =
                       breakableAddPostfix
                         config
                         x13
                         st
                     in
                     (match
                          st
                        with
                          None _
                        then
                          modref
                            p.errors
                            (snoc
                               (deref
                                  p.errors)
                               (getInfo_DAETypeOp
                                 x13, "Invalid input"))
                        else
                          {})
                     ; st
                   else
                     None
                       {}
           in
           let finalizeDAETypeOp =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam st.
                 let res57 =
                   optionBind
                     st
                     (lam st.
                        match
                          breakableFinalizeParse
                            config
                            st
                        with
                          Some (tops & ([ top ] ++ _ ++ ""))
                        then
                          let errs =
                            breakableDefaultHighlight
                              reportConfig
                              p.content
                              tops
                          in
                          let res57 =
                            unsplit_DAETypeOp
                              top
                          in
                          match
                            null
                              errs
                          with
                            true
                          then
                            Some
                              res57
                          else
                            (modref
                                 p.errors
                                 (concat
                                    (deref
                                       p.errors)
                                    errs))
                            ; Some
                              (res57.0, BadDAEType
                                { info =
                                    res57.0 })
                        else
                          (modref
                               p.errors
                               (snoc
                                  (deref
                                     p.errors)
                                  (NoInfo
                                    {}, "Unfinished DAEType")))
                          ; None
                            {})
                 in
                 optionGetOr
                   (NoInfo
                     {}, BadDAEType
                     { info =
                         NoInfo
                           {} })
                   res57
           in
           let config1 =
             { parenAllowed =
                 #frozen"parenAllowed_DAEConstOp",
               topAllowed =
                 #frozen"topAllowed_DAEConstOp",
               leftAllowed =
                 #frozen"leftAllowed_DAEConstOp",
               rightAllowed =
                 #frozen"rightAllowed_DAEConstOp",
               groupingsAllowed =
                 #frozen"groupingsAllowed_DAEConstOp" }
           in
           let reportConfig1 =
             { parenAllowed =
                 #frozen"parenAllowed_DAEConstOp",
               topAllowed =
                 #frozen"topAllowed_DAEConstOp",
               terminalInfos =
                 #frozen"getTerms_DAEConstOp",
               getInfo =
                 #frozen"getInfo_DAEConstOp",
               lpar =
                 "(",
               rpar =
                 ")" }
           in
           let addDAEConstOpAtom =
             lam #var"".
               lam x13.
                 lam st.
                   optionMap
                     (breakableAddAtom
                        config1
                        x13)
                     st
           in
           let addDAEConstOpInfix =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam x13.
                 lam st.
                   match
                     st
                   with
                     Some st
                   then
                     let st =
                       breakableAddInfix
                         config1
                         x13
                         st
                     in
                     (match
                          st
                        with
                          None _
                        then
                          modref
                            p.errors
                            (snoc
                               (deref
                                  p.errors)
                               (getInfo_DAEConstOp
                                 x13, "Invalid input"))
                        else
                          {})
                     ; st
                   else
                     None
                       {}
           in
           let addDAEConstOpPrefix =
             lam #var"".
               lam x13.
                 lam st.
                   optionMap
                     (breakableAddPrefix
                        config1
                        x13)
                     st
           in
           let addDAEConstOpPostfix =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam x13.
                 lam st.
                   match
                     st
                   with
                     Some st
                   then
                     let st =
                       breakableAddPostfix
                         config1
                         x13
                         st
                     in
                     (match
                          st
                        with
                          None _
                        then
                          modref
                            p.errors
                            (snoc
                               (deref
                                  p.errors)
                               (getInfo_DAEConstOp
                                 x13, "Invalid input"))
                        else
                          {})
                     ; st
                   else
                     None
                       {}
           in
           let finalizeDAEConstOp =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam st.
                 let res57 =
                   optionBind
                     st
                     (lam st.
                        match
                          breakableFinalizeParse
                            config1
                            st
                        with
                          Some (tops & ([ top ] ++ _ ++ ""))
                        then
                          let errs =
                            breakableDefaultHighlight
                              reportConfig1
                              p.content
                              tops
                          in
                          let res57 =
                            unsplit_DAEConstOp
                              top
                          in
                          match
                            null
                              errs
                          with
                            true
                          then
                            Some
                              res57
                          else
                            (modref
                                 p.errors
                                 (concat
                                    (deref
                                       p.errors)
                                    errs))
                            ; Some
                              (res57.0, BadDAEConst
                                { info =
                                    res57.0 })
                        else
                          (modref
                               p.errors
                               (snoc
                                  (deref
                                     p.errors)
                                  (NoInfo
                                    {}, "Unfinished DAEConst")))
                          ; None
                            {})
                 in
                 optionGetOr
                   (NoInfo
                     {}, BadDAEConst
                     { info =
                         NoInfo
                           {} })
                   res57
           in
           let config2 =
             { parenAllowed =
                 #frozen"parenAllowed_DAEPatOp",
               topAllowed =
                 #frozen"topAllowed_DAEPatOp",
               leftAllowed =
                 #frozen"leftAllowed_DAEPatOp",
               rightAllowed =
                 #frozen"rightAllowed_DAEPatOp",
               groupingsAllowed =
                 #frozen"groupingsAllowed_DAEPatOp" }
           in
           let reportConfig2 =
             { parenAllowed =
                 #frozen"parenAllowed_DAEPatOp",
               topAllowed =
                 #frozen"topAllowed_DAEPatOp",
               terminalInfos =
                 #frozen"getTerms_DAEPatOp",
               getInfo =
                 #frozen"getInfo_DAEPatOp",
               lpar =
                 "(",
               rpar =
                 ")" }
           in
           let addDAEPatOpAtom =
             lam #var"".
               lam x13.
                 lam st.
                   optionMap
                     (breakableAddAtom
                        config2
                        x13)
                     st
           in
           let addDAEPatOpInfix =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam x13.
                 lam st.
                   match
                     st
                   with
                     Some st
                   then
                     let st =
                       breakableAddInfix
                         config2
                         x13
                         st
                     in
                     (match
                          st
                        with
                          None _
                        then
                          modref
                            p.errors
                            (snoc
                               (deref
                                  p.errors)
                               (getInfo_DAEPatOp
                                 x13, "Invalid input"))
                        else
                          {})
                     ; st
                   else
                     None
                       {}
           in
           let addDAEPatOpPrefix =
             lam #var"".
               lam x13.
                 lam st.
                   optionMap
                     (breakableAddPrefix
                        config2
                        x13)
                     st
           in
           let addDAEPatOpPostfix =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam x13.
                 lam st.
                   match
                     st
                   with
                     Some st
                   then
                     let st =
                       breakableAddPostfix
                         config2
                         x13
                         st
                     in
                     (match
                          st
                        with
                          None _
                        then
                          modref
                            p.errors
                            (snoc
                               (deref
                                  p.errors)
                               (getInfo_DAEPatOp
                                 x13, "Invalid input"))
                        else
                          {})
                     ; st
                   else
                     None
                       {}
           in
           let finalizeDAEPatOp =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam st.
                 let res57 =
                   optionBind
                     st
                     (lam st.
                        match
                          breakableFinalizeParse
                            config2
                            st
                        with
                          Some (tops & ([ top ] ++ _ ++ ""))
                        then
                          let errs =
                            breakableDefaultHighlight
                              reportConfig2
                              p.content
                              tops
                          in
                          let res57 =
                            unsplit_DAEPatOp
                              top
                          in
                          match
                            null
                              errs
                          with
                            true
                          then
                            Some
                              res57
                          else
                            (modref
                                 p.errors
                                 (concat
                                    (deref
                                       p.errors)
                                    errs))
                            ; Some
                              (res57.0, BadDAEPat
                                { info =
                                    res57.0 })
                        else
                          (modref
                               p.errors
                               (snoc
                                  (deref
                                     p.errors)
                                  (NoInfo
                                    {}, "Unfinished DAEPat")))
                          ; None
                            {})
                 in
                 optionGetOr
                   (NoInfo
                     {}, BadDAEPat
                     { info =
                         NoInfo
                           {} })
                   res57
           in
           let config3 =
             { parenAllowed =
                 #frozen"parenAllowed_DAEExprOp",
               topAllowed =
                 #frozen"topAllowed_DAEExprOp",
               leftAllowed =
                 #frozen"leftAllowed_DAEExprOp",
               rightAllowed =
                 #frozen"rightAllowed_DAEExprOp",
               groupingsAllowed =
                 #frozen"groupingsAllowed_DAEExprOp" }
           in
           let reportConfig3 =
             { parenAllowed =
                 #frozen"parenAllowed_DAEExprOp",
               topAllowed =
                 #frozen"topAllowed_DAEExprOp",
               terminalInfos =
                 #frozen"getTerms_DAEExprOp",
               getInfo =
                 #frozen"getInfo_DAEExprOp",
               lpar =
                 "(",
               rpar =
                 ")" }
           in
           let addDAEExprOpAtom =
             lam #var"".
               lam x13.
                 lam st.
                   optionMap
                     (breakableAddAtom
                        config3
                        x13)
                     st
           in
           let addDAEExprOpInfix =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam x13.
                 lam st.
                   match
                     st
                   with
                     Some st
                   then
                     let st =
                       breakableAddInfix
                         config3
                         x13
                         st
                     in
                     (match
                          st
                        with
                          None _
                        then
                          modref
                            p.errors
                            (snoc
                               (deref
                                  p.errors)
                               (getInfo_DAEExprOp
                                 x13, "Invalid input"))
                        else
                          {})
                     ; st
                   else
                     None
                       {}
           in
           let addDAEExprOpPrefix =
             lam #var"".
               lam x13.
                 lam st.
                   optionMap
                     (breakableAddPrefix
                        config3
                        x13)
                     st
           in
           let addDAEExprOpPostfix =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam x13.
                 lam st.
                   match
                     st
                   with
                     Some st
                   then
                     let st =
                       breakableAddPostfix
                         config3
                         x13
                         st
                     in
                     (match
                          st
                        with
                          None _
                        then
                          modref
                            p.errors
                            (snoc
                               (deref
                                  p.errors)
                               (getInfo_DAEExprOp
                                 x13, "Invalid input"))
                        else
                          {})
                     ; st
                   else
                     None
                       {}
           in
           let finalizeDAEExprOp =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam st.
                 let res57 =
                   optionBind
                     st
                     (lam st.
                        match
                          breakableFinalizeParse
                            config3
                            st
                        with
                          Some (tops & ([ top ] ++ _ ++ ""))
                        then
                          let errs =
                            breakableDefaultHighlight
                              reportConfig3
                              p.content
                              tops
                          in
                          let res57 =
                            unsplit_DAEExprOp
                              top
                          in
                          match
                            null
                              errs
                          with
                            true
                          then
                            Some
                              res57
                          else
                            (modref
                                 p.errors
                                 (concat
                                    (deref
                                       p.errors)
                                    errs))
                            ; Some
                              (res57.0, BadDAEExpr
                                { info =
                                    res57.0 })
                        else
                          (modref
                               p.errors
                               (snoc
                                  (deref
                                     p.errors)
                                  (NoInfo
                                    {}, "Unfinished DAEExpr")))
                          ; None
                            {})
                 in
                 optionGetOr
                   (NoInfo
                     {}, BadDAEExpr
                     { info =
                         NoInfo
                           {} })
                   res57
           in
           let config4 =
             { parenAllowed =
                 #frozen"parenAllowed_DAEEqnOp",
               topAllowed =
                 #frozen"topAllowed_DAEEqnOp",
               leftAllowed =
                 #frozen"leftAllowed_DAEEqnOp",
               rightAllowed =
                 #frozen"rightAllowed_DAEEqnOp",
               groupingsAllowed =
                 #frozen"groupingsAllowed_DAEEqnOp" }
           in
           let reportConfig4 =
             { parenAllowed =
                 #frozen"parenAllowed_DAEEqnOp",
               topAllowed =
                 #frozen"topAllowed_DAEEqnOp",
               terminalInfos =
                 #frozen"getTerms_DAEEqnOp",
               getInfo =
                 #frozen"getInfo_DAEEqnOp",
               lpar =
                 "(",
               rpar =
                 ")" }
           in
           let addDAEEqnOpAtom =
             lam #var"".
               lam x13.
                 lam st.
                   optionMap
                     (breakableAddAtom
                        config4
                        x13)
                     st
           in
           let addDAEEqnOpInfix =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam x13.
                 lam st.
                   match
                     st
                   with
                     Some st
                   then
                     let st =
                       breakableAddInfix
                         config4
                         x13
                         st
                     in
                     (match
                          st
                        with
                          None _
                        then
                          modref
                            p.errors
                            (snoc
                               (deref
                                  p.errors)
                               (getInfo_DAEEqnOp
                                 x13, "Invalid input"))
                        else
                          {})
                     ; st
                   else
                     None
                       {}
           in
           let addDAEEqnOpPrefix =
             lam #var"".
               lam x13.
                 lam st.
                   optionMap
                     (breakableAddPrefix
                        config4
                        x13)
                     st
           in
           let addDAEEqnOpPostfix =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam x13.
                 lam st.
                   match
                     st
                   with
                     Some st
                   then
                     let st =
                       breakableAddPostfix
                         config4
                         x13
                         st
                     in
                     (match
                          st
                        with
                          None _
                        then
                          modref
                            p.errors
                            (snoc
                               (deref
                                  p.errors)
                               (getInfo_DAEEqnOp
                                 x13, "Invalid input"))
                        else
                          {})
                     ; st
                   else
                     None
                       {}
           in
           let finalizeDAEEqnOp =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam st.
                 let res57 =
                   optionBind
                     st
                     (lam st.
                        match
                          breakableFinalizeParse
                            config4
                            st
                        with
                          Some (tops & ([ top ] ++ _ ++ ""))
                        then
                          let errs =
                            breakableDefaultHighlight
                              reportConfig4
                              p.content
                              tops
                          in
                          let res57 =
                            unsplit_DAEEqnOp
                              top
                          in
                          match
                            null
                              errs
                          with
                            true
                          then
                            Some
                              res57
                          else
                            (modref
                                 p.errors
                                 (concat
                                    (deref
                                       p.errors)
                                    errs))
                            ; Some
                              (res57.0, BadDAEEqn
                                { info =
                                    res57.0 })
                        else
                          (modref
                               p.errors
                               (snoc
                                  (deref
                                     p.errors)
                                  (NoInfo
                                    {}, "Unfinished DAEEqn")))
                          ; None
                            {})
                 in
                 optionGetOr
                   (NoInfo
                     {}, BadDAEEqn
                     { info =
                         NoInfo
                           {} })
                   res57
           in
           let config5 =
             { parenAllowed =
                 #frozen"parenAllowed_DAEVarOp",
               topAllowed =
                 #frozen"topAllowed_DAEVarOp",
               leftAllowed =
                 #frozen"leftAllowed_DAEVarOp",
               rightAllowed =
                 #frozen"rightAllowed_DAEVarOp",
               groupingsAllowed =
                 #frozen"groupingsAllowed_DAEVarOp" }
           in
           let reportConfig5 =
             { parenAllowed =
                 #frozen"parenAllowed_DAEVarOp",
               topAllowed =
                 #frozen"topAllowed_DAEVarOp",
               terminalInfos =
                 #frozen"getTerms_DAEVarOp",
               getInfo =
                 #frozen"getInfo_DAEVarOp",
               lpar =
                 "(",
               rpar =
                 ")" }
           in
           let addDAEVarOpAtom =
             lam #var"".
               lam x13.
                 lam st.
                   optionMap
                     (breakableAddAtom
                        config5
                        x13)
                     st
           in
           let addDAEVarOpInfix =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam x13.
                 lam st.
                   match
                     st
                   with
                     Some st
                   then
                     let st =
                       breakableAddInfix
                         config5
                         x13
                         st
                     in
                     (match
                          st
                        with
                          None _
                        then
                          modref
                            p.errors
                            (snoc
                               (deref
                                  p.errors)
                               (getInfo_DAEVarOp
                                 x13, "Invalid input"))
                        else
                          {})
                     ; st
                   else
                     None
                       {}
           in
           let addDAEVarOpPrefix =
             lam #var"".
               lam x13.
                 lam st.
                   optionMap
                     (breakableAddPrefix
                        config5
                        x13)
                     st
           in
           let addDAEVarOpPostfix =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam x13.
                 lam st.
                   match
                     st
                   with
                     Some st
                   then
                     let st =
                       breakableAddPostfix
                         config5
                         x13
                         st
                     in
                     (match
                          st
                        with
                          None _
                        then
                          modref
                            p.errors
                            (snoc
                               (deref
                                  p.errors)
                               (getInfo_DAEVarOp
                                 x13, "Invalid input"))
                        else
                          {})
                     ; st
                   else
                     None
                       {}
           in
           let finalizeDAEVarOp =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam st.
                 let res57 =
                   optionBind
                     st
                     (lam st.
                        match
                          breakableFinalizeParse
                            config5
                            st
                        with
                          Some (tops & ([ top ] ++ _ ++ ""))
                        then
                          let errs =
                            breakableDefaultHighlight
                              reportConfig5
                              p.content
                              tops
                          in
                          let res57 =
                            unsplit_DAEVarOp
                              top
                          in
                          match
                            null
                              errs
                          with
                            true
                          then
                            Some
                              res57
                          else
                            (modref
                                 p.errors
                                 (concat
                                    (deref
                                       p.errors)
                                    errs))
                            ; Some
                              (res57.0, BadDAEVar
                                { info =
                                    res57.0 })
                        else
                          (modref
                               p.errors
                               (snoc
                                  (deref
                                     p.errors)
                                  (NoInfo
                                    {}, "Unfinished DAEVar")))
                          ; None
                            {})
                 in
                 optionGetOr
                   (NoInfo
                     {}, BadDAEVar
                     { info =
                         NoInfo
                           {} })
                   res57
           in
           let config6 =
             { parenAllowed =
                 #frozen"parenAllowed_DAETopOp",
               topAllowed =
                 #frozen"topAllowed_DAETopOp",
               leftAllowed =
                 #frozen"leftAllowed_DAETopOp",
               rightAllowed =
                 #frozen"rightAllowed_DAETopOp",
               groupingsAllowed =
                 #frozen"groupingsAllowed_DAETopOp" }
           in
           let reportConfig6 =
             { parenAllowed =
                 #frozen"parenAllowed_DAETopOp",
               topAllowed =
                 #frozen"topAllowed_DAETopOp",
               terminalInfos =
                 #frozen"getTerms_DAETopOp",
               getInfo =
                 #frozen"getInfo_DAETopOp",
               lpar =
                 "(",
               rpar =
                 ")" }
           in
           let addDAETopOpAtom =
             lam #var"".
               lam x13.
                 lam st.
                   optionMap
                     (breakableAddAtom
                        config6
                        x13)
                     st
           in
           let addDAETopOpInfix =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam x13.
                 lam st.
                   match
                     st
                   with
                     Some st
                   then
                     let st =
                       breakableAddInfix
                         config6
                         x13
                         st
                     in
                     (match
                          st
                        with
                          None _
                        then
                          modref
                            p.errors
                            (snoc
                               (deref
                                  p.errors)
                               (getInfo_DAETopOp
                                 x13, "Invalid input"))
                        else
                          {})
                     ; st
                   else
                     None
                       {}
           in
           let addDAETopOpPrefix =
             lam #var"".
               lam x13.
                 lam st.
                   optionMap
                     (breakableAddPrefix
                        config6
                        x13)
                     st
           in
           let addDAETopOpPostfix =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam x13.
                 lam st.
                   match
                     st
                   with
                     Some st
                   then
                     let st =
                       breakableAddPostfix
                         config6
                         x13
                         st
                     in
                     (match
                          st
                        with
                          None _
                        then
                          modref
                            p.errors
                            (snoc
                               (deref
                                  p.errors)
                               (getInfo_DAETopOp
                                 x13, "Invalid input"))
                        else
                          {})
                     ; st
                   else
                     None
                       {}
           in
           let finalizeDAETopOp =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam st.
                 let res57 =
                   optionBind
                     st
                     (lam st.
                        match
                          breakableFinalizeParse
                            config6
                            st
                        with
                          Some (tops & ([ top ] ++ _ ++ ""))
                        then
                          let errs =
                            breakableDefaultHighlight
                              reportConfig6
                              p.content
                              tops
                          in
                          let res57 =
                            unsplit_DAETopOp
                              top
                          in
                          match
                            null
                              errs
                          with
                            true
                          then
                            Some
                              res57
                          else
                            (modref
                                 p.errors
                                 (concat
                                    (deref
                                       p.errors)
                                    errs))
                            ; Some
                              (res57.0, BadDAETop
                                { info =
                                    res57.0 })
                        else
                          (modref
                               p.errors
                               (snoc
                                  (deref
                                     p.errors)
                                  (NoInfo
                                    {}, "Unfinished DAETop")))
                          ; None
                            {})
                 in
                 optionGetOr
                   (NoInfo
                     {}, BadDAETop
                     { info =
                         NoInfo
                           {} })
                   res57
           in
           let config7 =
             { parenAllowed =
                 #frozen"parenAllowed_DAEProgOp",
               topAllowed =
                 #frozen"topAllowed_DAEProgOp",
               leftAllowed =
                 #frozen"leftAllowed_DAEProgOp",
               rightAllowed =
                 #frozen"rightAllowed_DAEProgOp",
               groupingsAllowed =
                 #frozen"groupingsAllowed_DAEProgOp" }
           in
           let reportConfig7 =
             { parenAllowed =
                 #frozen"parenAllowed_DAEProgOp",
               topAllowed =
                 #frozen"topAllowed_DAEProgOp",
               terminalInfos =
                 #frozen"getTerms_DAEProgOp",
               getInfo =
                 #frozen"getInfo_DAEProgOp",
               lpar =
                 "(",
               rpar =
                 ")" }
           in
           let addDAEProgOpAtom =
             lam #var"".
               lam x13.
                 lam st.
                   optionMap
                     (breakableAddAtom
                        config7
                        x13)
                     st
           in
           let addDAEProgOpInfix =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam x13.
                 lam st.
                   match
                     st
                   with
                     Some st
                   then
                     let st =
                       breakableAddInfix
                         config7
                         x13
                         st
                     in
                     (match
                          st
                        with
                          None _
                        then
                          modref
                            p.errors
                            (snoc
                               (deref
                                  p.errors)
                               (getInfo_DAEProgOp
                                 x13, "Invalid input"))
                        else
                          {})
                     ; st
                   else
                     None
                       {}
           in
           let addDAEProgOpPrefix =
             lam #var"".
               lam x13.
                 lam st.
                   optionMap
                     (breakableAddPrefix
                        config7
                        x13)
                     st
           in
           let addDAEProgOpPostfix =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam x13.
                 lam st.
                   match
                     st
                   with
                     Some st
                   then
                     let st =
                       breakableAddPostfix
                         config7
                         x13
                         st
                     in
                     (match
                          st
                        with
                          None _
                        then
                          modref
                            p.errors
                            (snoc
                               (deref
                                  p.errors)
                               (getInfo_DAEProgOp
                                 x13, "Invalid input"))
                        else
                          {})
                     ; st
                   else
                     None
                       {}
           in
           let finalizeDAEProgOp =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam st.
                 let res57 =
                   optionBind
                     st
                     (lam st.
                        match
                          breakableFinalizeParse
                            config7
                            st
                        with
                          Some (tops & ([ top ] ++ _ ++ ""))
                        then
                          let errs =
                            breakableDefaultHighlight
                              reportConfig7
                              p.content
                              tops
                          in
                          let res57 =
                            unsplit_DAEProgOp
                              top
                          in
                          match
                            null
                              errs
                          with
                            true
                          then
                            Some
                              res57
                          else
                            (modref
                                 p.errors
                                 (concat
                                    (deref
                                       p.errors)
                                    errs))
                            ; Some
                              (res57.0, BadDAEProg
                                { info =
                                    res57.0 })
                        else
                          (modref
                               p.errors
                               (snoc
                                  (deref
                                     p.errors)
                                  (NoInfo
                                    {}, "Unfinished DAEProg")))
                          ; None
                            {})
                 in
                 optionGetOr
                   (NoInfo
                     {}, BadDAEProg
                     { info =
                         NoInfo
                           {} })
                   res57
           in
           [ { nt =
                 #var"DAETypeAtom",
               label =
                 {},
               rhs =
                 [ litSym
                     "Float" ],
               action =
                 lam state: {errors: Ref [(Info, [Char])], content: String}.
                   lam res.
                     match
                       res
                     with
                       [ LitParsed l ]
                     in
                     asDyn
                         (FloatDAETypeOp
                            { __br_info =
                                l.info,
                              __br_terms =
                                [ l.info ] }) },
             { nt =
                 #var"DAETypeAtom",
               label =
                 {},
               rhs =
                 [ litSym
                     "Int" ],
               action =
                 lam state1: {errors: Ref [(Info, [Char])], content: String}.
                   lam res1.
                     match
                       res1
                     with
                       [ LitParsed l1 ]
                     in
                     asDyn
                         (IntDAETypeOp
                            { __br_info =
                                l1.info,
                              __br_terms =
                                [ l1.info ] }) },
             { nt =
                 #var"DAETypeInfix",
               label =
                 {},
               rhs =
                 [ litSym
                     "->" ],
               action =
                 lam state2: {errors: Ref [(Info, [Char])], content: String}.
                   lam res2.
                     match
                       res2
                     with
                       [ LitParsed l2 ]
                     in
                     asDyn
                         (ArrowDAETypeOp
                            { __br_info =
                                l2.info,
                              __br_terms =
                                [ l2.info ] }) },
             { nt =
                 #var"DAEConstAtom",
               label =
                 {},
               rhs =
                 [ tokSym
                     (FloatRepr
                        {}) ],
               action =
                 lam state3: {errors: Ref [(Info, [Char])], content: String}.
                   lam res3.
                     match
                       res3
                     with
                       [ TokParsed (FloatTok x) ]
                     in
                     asDyn
                         (FloatDAEConstOp
                            { __br_info =
                                x.info,
                              __br_terms =
                                [ x.info ],
                              val =
                                [ { v =
                                      x.val,
                                    i =
                                      x.info } ] }) },
             { nt =
                 #var"DAEConstAtom",
               label =
                 {},
               rhs =
                 [ tokSym
                     (IntRepr
                        {}) ],
               action =
                 lam state4: {errors: Ref [(Info, [Char])], content: String}.
                   lam res4.
                     match
                       res4
                     with
                       [ TokParsed (IntTok x1) ]
                     in
                     asDyn
                         (IntDAEConstOp
                            { __br_info =
                                x1.info,
                              __br_terms =
                                [ x1.info ],
                              val =
                                [ { v =
                                      x1.val,
                                    i =
                                      x1.info } ] }) },
             { nt =
                 #var"DAEConstAtom",
               label =
                 {},
               rhs =
                 [ litSym
                     "true" ],
               action =
                 lam state5: {errors: Ref [(Info, [Char])], content: String}.
                   lam res5.
                     match
                       res5
                     with
                       [ LitParsed l3 ]
                     in
                     asDyn
                         (TrueDAEConstOp
                            { __br_info =
                                l3.info,
                              __br_terms =
                                [ l3.info ] }) },
             { nt =
                 #var"DAEConstAtom",
               label =
                 {},
               rhs =
                 [ litSym
                     "false" ],
               action =
                 lam state6: {errors: Ref [(Info, [Char])], content: String}.
                   lam res6.
                     match
                       res6
                     with
                       [ LitParsed l4 ]
                     in
                     asDyn
                         (FalseDAEConstOp
                            { __br_info =
                                l4.info,
                              __br_terms =
                                [ l4.info ] }) },
             { nt =
                 #var"DAEConstAtom",
               label =
                 {},
               rhs =
                 [ litSym
                     "pred" ],
               action =
                 lam state7: {errors: Ref [(Info, [Char])], content: String}.
                   lam res7.
                     match
                       res7
                     with
                       [ LitParsed l5 ]
                     in
                     asDyn
                         (PredDAEConstOp
                            { __br_info =
                                l5.info,
                              __br_terms =
                                [ l5.info ] }) },
             { nt =
                 #var"DAEConstAtom",
               label =
                 {},
               rhs =
                 [ litSym
                     "exp" ],
               action =
                 lam state8: {errors: Ref [(Info, [Char])], content: String}.
                   lam res8.
                     match
                       res8
                     with
                       [ LitParsed l6 ]
                     in
                     asDyn
                         (ExpDAEConstOp
                            { __br_info =
                                l6.info,
                              __br_terms =
                                [ l6.info ] }) },
             { nt =
                 #var"DAEConstAtom",
               label =
                 {},
               rhs =
                 [ litSym
                     "sin" ],
               action =
                 lam state9: {errors: Ref [(Info, [Char])], content: String}.
                   lam res9.
                     match
                       res9
                     with
                       [ LitParsed l7 ]
                     in
                     asDyn
                         (SinDAEConstOp
                            { __br_info =
                                l7.info,
                              __br_terms =
                                [ l7.info ] }) },
             { nt =
                 #var"DAEConstAtom",
               label =
                 {},
               rhs =
                 [ litSym
                     "cos" ],
               action =
                 lam state10: {errors: Ref [(Info, [Char])], content: String}.
                   lam res10.
                     match
                       res10
                     with
                       [ LitParsed l8 ]
                     in
                     asDyn
                         (CosDAEConstOp
                            { __br_info =
                                l8.info,
                              __br_terms =
                                [ l8.info ] }) },
             { nt =
                 #var"DAEConstAtom",
               label =
                 {},
               rhs =
                 [ litSym
                     "sqrt" ],
               action =
                 lam state11: {errors: Ref [(Info, [Char])], content: String}.
                   lam res11.
                     match
                       res11
                     with
                       [ LitParsed l9 ]
                     in
                     asDyn
                         (SqrtDAEConstOp
                            { __br_info =
                                l9.info,
                              __br_terms =
                                [ l9.info ] }) },
             { nt =
                 kleene,
               label =
                 {},
               rhs =
                 [ litSym
                     ",",
                   tokSym
                     (LIdentRepr
                        {}),
                   ntSym
                     kleene ],
               action =
                 lam state12: {errors: Ref [(Info, [Char])], content: String}.
                   lam res12.
                     match
                       res12
                     with
                       [ LitParsed l10,
                         TokParsed (LIdentTok x2),
                         UserSym val1 ]
                     in
                     let val1: {names: [{i: Info, v: Name}], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val1
                       in
                       asDyn
                         { __br_info =
                             foldl
                               mergeInfo
                               l10.info
                               [ x2.info,
                                 val1.__br_info ],
                           __br_terms =
                             join
                               [ [ l10.info ],
                                 [ x2.info ],
                                 val1.__br_terms ],
                           names =
                             concat
                               [ { v =
                                     nameNoSym
                                       x2.val,
                                   i =
                                     x2.info } ]
                               val1.names } },
             { nt =
                 kleene,
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state13: {errors: Ref [(Info, [Char])], content: String}.
                   lam res13.
                     match
                       res13
                     with
                       ""
                     in
                     asDyn
                         { __br_info =
                             NoInfo
                               {},
                           __br_terms =
                             "",
                           names =
                             "" } },
             { nt =
                 alt,
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state14: {errors: Ref [(Info, [Char])], content: String}.
                   lam res14.
                     match
                       res14
                     with
                       ""
                     in
                     asDyn
                         { __br_info =
                             NoInfo
                               {},
                           __br_terms =
                             "",
                           names =
                             "" } },
             { nt =
                 alt,
               label =
                 {},
               rhs =
                 [ tokSym
                     (LIdentRepr
                        {}),
                   ntSym
                     kleene ],
               action =
                 lam state15: {errors: Ref [(Info, [Char])], content: String}.
                   lam res15.
                     match
                       res15
                     with
                       [ TokParsed (LIdentTok x3),
                         UserSym val1 ]
                     in
                     let val1: {names: [{i: Info, v: Name}], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val1
                       in
                       asDyn
                         { __br_info =
                             mergeInfo
                               x3.info
                               val1.__br_info,
                           __br_terms =
                             concat
                               [ x3.info ]
                               val1.__br_terms,
                           names =
                             concat
                               [ { v =
                                     nameNoSym
                                       x3.val,
                                   i =
                                     x3.info } ]
                               val1.names } },
             { nt =
                 #var"DAEPatAtom",
               label =
                 {},
               rhs =
                 [ litSym
                     "{",
                   ntSym
                     alt,
                   litSym
                     "}" ],
               action =
                 lam state16: {errors: Ref [(Info, [Char])], content: String}.
                   lam res16.
                     match
                       res16
                     with
                       [ LitParsed l11,
                         UserSym val2,
                         LitParsed l12 ]
                     in
                     let val2: {names: [{i: Info, v: Name}], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val2
                       in
                       asDyn
                         (TupleDAEPatOp
                            { __br_info =
                                foldl
                                  mergeInfo
                                  l11.info
                                  [ val2.__br_info,
                                    l12.info ],
                              __br_terms =
                                join
                                  [ [ l11.info ],
                                    val2.__br_terms,
                                    [ l12.info ] ],
                              names =
                                val2.names }) },
             { nt =
                 #var"DAEExprAtom",
               label =
                 {},
               rhs =
                 [ tokSym
                     (LIdentRepr
                        {}) ],
               action =
                 lam state17: {errors: Ref [(Info, [Char])], content: String}.
                   lam res17.
                     match
                       res17
                     with
                       [ TokParsed (LIdentTok x4) ]
                     in
                     asDyn
                         (VarDAEExprOp
                            { __br_info =
                                x4.info,
                              __br_terms =
                                [ x4.info ],
                              name =
                                [ { v =
                                      nameNoSym
                                        x4.val,
                                    i =
                                      x4.info } ] }) },
             { nt =
                 #var"DAEExprPrefix",
               label =
                 {},
               rhs =
                 [ litSym
                     "lam",
                   tokSym
                     (LIdentRepr
                        {}),
                   litSym
                     "." ],
               action =
                 lam state18: {errors: Ref [(Info, [Char])], content: String}.
                   lam res18.
                     match
                       res18
                     with
                       [ LitParsed l13,
                         TokParsed (LIdentTok x5),
                         LitParsed l14 ]
                     in
                     asDyn
                         (AbsDAEExprOp
                            { __br_info =
                                foldl
                                  mergeInfo
                                  l13.info
                                  [ x5.info,
                                    l14.info ],
                              __br_terms =
                                join
                                  [ [ l13.info ],
                                    [ x5.info ],
                                    [ l14.info ] ],
                              name =
                                [ { v =
                                      nameNoSym
                                        x5.val,
                                    i =
                                      x5.info } ] }) },
             { nt =
                 #var"DAEExprInfix",
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state19: {errors: Ref [(Info, [Char])], content: String}.
                   lam res19.
                     match
                       res19
                     with
                       ""
                     in
                     asDyn
                         (AppDAEExprOp
                            { __br_info =
                                NoInfo
                                  {},
                              __br_terms =
                                "" }) },
             { nt =
                 kleene1,
               label =
                 {},
               rhs =
                 [ litSym
                     ",",
                   ntSym
                     #var"DAEExpr",
                   ntSym
                     kleene1 ],
               action =
                 lam state20: {errors: Ref [(Info, [Char])], content: String}.
                   lam res20.
                     match
                       res20
                     with
                       [ LitParsed l15,
                         UserSym ntVal,
                         UserSym val3 ]
                     in
                     let ntVal: (Info, DAEExpr) =
                         fromDyn
                           ntVal
                       in
                       let val3: {exprs: [DAEExpr], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val3
                       in
                       asDyn
                         { __br_info =
                             foldl
                               mergeInfo
                               l15.info
                               [ ntVal.0,
                                 val3.__br_info ],
                           __br_terms =
                             concat
                               [ l15.info ]
                               val3.__br_terms,
                           exprs =
                             concat
                               [ ntVal.1 ]
                               val3.exprs } },
             { nt =
                 kleene1,
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state21: {errors: Ref [(Info, [Char])], content: String}.
                   lam res21.
                     match
                       res21
                     with
                       ""
                     in
                     asDyn
                         { __br_info =
                             NoInfo
                               {},
                           __br_terms =
                             "",
                           exprs =
                             "" } },
             { nt =
                 alt1,
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state22: {errors: Ref [(Info, [Char])], content: String}.
                   lam res22.
                     match
                       res22
                     with
                       ""
                     in
                     asDyn
                         { __br_info =
                             NoInfo
                               {},
                           __br_terms =
                             "",
                           exprs =
                             "" } },
             { nt =
                 alt1,
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"DAEExpr",
                   ntSym
                     kleene1 ],
               action =
                 lam state23: {errors: Ref [(Info, [Char])], content: String}.
                   lam res23.
                     match
                       res23
                     with
                       [ UserSym ntVal1,
                         UserSym val3 ]
                     in
                     let ntVal1: (Info, DAEExpr) =
                         fromDyn
                           ntVal1
                       in
                       let val3: {exprs: [DAEExpr], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val3
                       in
                       asDyn
                         { __br_info =
                             mergeInfo
                               ntVal1.0
                               val3.__br_info,
                           __br_terms =
                             val3.__br_terms,
                           exprs =
                             concat
                               [ ntVal1.1 ]
                               val3.exprs } },
             { nt =
                 #var"DAEExprAtom",
               label =
                 {},
               rhs =
                 [ litSym
                     "{",
                   ntSym
                     alt1,
                   litSym
                     "}" ],
               action =
                 lam state24: {errors: Ref [(Info, [Char])], content: String}.
                   lam res24.
                     match
                       res24
                     with
                       [ LitParsed l16,
                         UserSym val4,
                         LitParsed l17 ]
                     in
                     let val4: {exprs: [DAEExpr], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val4
                       in
                       asDyn
                         (TupleDAEExprOp
                            { __br_info =
                                foldl
                                  mergeInfo
                                  l16.info
                                  [ val4.__br_info,
                                    l17.info ],
                              __br_terms =
                                join
                                  [ [ l16.info ],
                                    val4.__br_terms,
                                    [ l17.info ] ],
                              exprs =
                                val4.exprs }) },
             { nt =
                 #var"DAEExprPostfix",
               label =
                 {},
               rhs =
                 [ litSym
                     ".",
                   tokSym
                     (IntRepr
                        {}) ],
               action =
                 lam state25: {errors: Ref [(Info, [Char])], content: String}.
                   lam res25.
                     match
                       res25
                     with
                       [ LitParsed l18,
                         TokParsed (IntTok x6) ]
                     in
                     asDyn
                         (ProjDAEExprOp
                            { __br_info =
                                mergeInfo
                                  l18.info
                                  x6.info,
                              __br_terms =
                                concat
                                  [ l18.info ]
                                  [ x6.info ],
                              label =
                                [ { v =
                                      x6.val,
                                    i =
                                      x6.info } ] }) },
             { nt =
                 #var"DAEExprAtom",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"DAEConst" ],
               action =
                 lam state26: {errors: Ref [(Info, [Char])], content: String}.
                   lam res26.
                     match
                       res26
                     with
                       [ UserSym ntVal2 ]
                     in
                     let ntVal2: (Info, DAEConst) =
                         fromDyn
                           ntVal2
                       in
                       asDyn
                         (ConstDAEExprOp
                            { __br_info =
                                ntVal2.0,
                              __br_terms =
                                "",
                              val =
                                [ ntVal2.1 ] }) },
             { nt =
                 #var"DAEExprInfix",
               label =
                 {},
               rhs =
                 [ litSym
                     "+" ],
               action =
                 lam state27: {errors: Ref [(Info, [Char])], content: String}.
                   lam res27.
                     match
                       res27
                     with
                       [ LitParsed l19 ]
                     in
                     asDyn
                         (AddDAEExprOp
                            { __br_info =
                                l19.info,
                              __br_terms =
                                [ l19.info ] }) },
             { nt =
                 #var"DAEExprInfix",
               label =
                 {},
               rhs =
                 [ litSym
                     "-" ],
               action =
                 lam state28: {errors: Ref [(Info, [Char])], content: String}.
                   lam res28.
                     match
                       res28
                     with
                       [ LitParsed l20 ]
                     in
                     asDyn
                         (SubDAEExprOp
                            { __br_info =
                                l20.info,
                              __br_terms =
                                [ l20.info ] }) },
             { nt =
                 #var"DAEExprInfix",
               label =
                 {},
               rhs =
                 [ litSym
                     "*" ],
               action =
                 lam state29: {errors: Ref [(Info, [Char])], content: String}.
                   lam res29.
                     match
                       res29
                     with
                       [ LitParsed l21 ]
                     in
                     asDyn
                         (MulDAEExprOp
                            { __br_info =
                                l21.info,
                              __br_terms =
                                [ l21.info ] }) },
             { nt =
                 #var"DAEExprInfix",
               label =
                 {},
               rhs =
                 [ litSym
                     "/" ],
               action =
                 lam state30: {errors: Ref [(Info, [Char])], content: String}.
                   lam res30.
                     match
                       res30
                     with
                       [ LitParsed l22 ]
                     in
                     asDyn
                         (DivDAEExprOp
                            { __br_info =
                                l22.info,
                              __br_terms =
                                [ l22.info ] }) },
             { nt =
                 #var"DAEExprInfix",
               label =
                 {},
               rhs =
                 [ litSym
                     "<" ],
               action =
                 lam state31: {errors: Ref [(Info, [Char])], content: String}.
                   lam res31.
                     match
                       res31
                     with
                       [ LitParsed l23 ]
                     in
                     asDyn
                         (LtDAEExprOp
                            { __br_info =
                                l23.info,
                              __br_terms =
                                [ l23.info ] }) },
             { nt =
                 #var"DAEExprInfix",
               label =
                 {},
               rhs =
                 [ litSym
                     "<." ],
               action =
                 lam state32: {errors: Ref [(Info, [Char])], content: String}.
                   lam res32.
                     match
                       res32
                     with
                       [ LitParsed l24 ]
                     in
                     asDyn
                         (LtfDAEExprOp
                            { __br_info =
                                l24.info,
                              __br_terms =
                                [ l24.info ] }) },
             { nt =
                 #var"DAEExprInfix",
               label =
                 {},
               rhs =
                 [ litSym
                     "==" ],
               action =
                 lam state33: {errors: Ref [(Info, [Char])], content: String}.
                   lam res33.
                     match
                       res33
                     with
                       [ LitParsed l25 ]
                     in
                     asDyn
                         (EqDAEExprOp
                            { __br_info =
                                l25.info,
                              __br_terms =
                                [ l25.info ] }) },
             { nt =
                 #var"DAEExprPrefix",
               label =
                 {},
               rhs =
                 [ litSym
                     "-." ],
               action =
                 lam state34: {errors: Ref [(Info, [Char])], content: String}.
                   lam res34.
                     match
                       res34
                     with
                       [ LitParsed l26 ]
                     in
                     asDyn
                         (NegDAEExprOp
                            { __br_info =
                                l26.info,
                              __br_terms =
                                [ l26.info ] }) },
             { nt =
                 #var"DAEExprPrefix",
               label =
                 {},
               rhs =
                 [ litSym
                     "match",
                   ntSym
                     #var"DAEExpr",
                   litSym
                     "with",
                   ntSym
                     #var"DAEPat",
                   litSym
                     "in" ],
               action =
                 lam state35: {errors: Ref [(Info, [Char])], content: String}.
                   lam res35.
                     match
                       res35
                     with
                       [ LitParsed l27,
                         UserSym ntVal3,
                         LitParsed l28,
                         UserSym ntVal4,
                         LitParsed l29 ]
                     in
                     let ntVal3: (Info, DAEExpr) =
                         fromDyn
                           ntVal3
                       in
                       let ntVal4: (Info, DAEPat) =
                         fromDyn
                           ntVal4
                       in
                       asDyn
                         (MatchInDAEExprOp
                            { __br_info =
                                foldl
                                  mergeInfo
                                  l27.info
                                  [ ntVal3.0,
                                    l28.info,
                                    ntVal4.0,
                                    l29.info ],
                              __br_terms =
                                join
                                  [ [ l27.info ],
                                    [ l28.info ],
                                    [ l29.info ] ],
                              pat =
                                [ ntVal4.1 ],
                              target =
                                [ ntVal3.1 ] }) },
             { nt =
                 #var"DAEExprPrefix",
               label =
                 {},
               rhs =
                 [ litSym
                     "if",
                   ntSym
                     #var"DAEExpr",
                   litSym
                     "then",
                   ntSym
                     #var"DAEExpr",
                   litSym
                     "else" ],
               action =
                 lam state36: {errors: Ref [(Info, [Char])], content: String}.
                   lam res36.
                     match
                       res36
                     with
                       [ LitParsed l30,
                         UserSym ntVal5,
                         LitParsed l31,
                         UserSym ntVal6,
                         LitParsed l32 ]
                     in
                     let ntVal5: (Info, DAEExpr) =
                         fromDyn
                           ntVal5
                       in
                       let ntVal6: (Info, DAEExpr) =
                         fromDyn
                           ntVal6
                       in
                       asDyn
                         (IfDAEExprOp
                            { __br_info =
                                foldl
                                  mergeInfo
                                  l30.info
                                  [ ntVal5.0,
                                    l31.info,
                                    ntVal6.0,
                                    l32.info ],
                              __br_terms =
                                join
                                  [ [ l30.info ],
                                    [ l31.info ],
                                    [ l32.info ] ],
                              thn =
                                [ ntVal6.1 ],
                              pred =
                                [ ntVal5.1 ] }) },
             { nt =
                 #var"DAEExprPrefix",
               label =
                 {},
               rhs =
                 [ litSym
                     "let",
                   tokSym
                     (LIdentRepr
                        {}),
                   litSym
                     "=",
                   ntSym
                     #var"DAEExpr",
                   litSym
                     "in" ],
               action =
                 lam state37: {errors: Ref [(Info, [Char])], content: String}.
                   lam res37.
                     match
                       res37
                     with
                       [ LitParsed l33,
                         TokParsed (LIdentTok x7),
                         LitParsed l34,
                         UserSym ntVal7,
                         LitParsed l35 ]
                     in
                     let ntVal7: (Info, DAEExpr) =
                         fromDyn
                           ntVal7
                       in
                       asDyn
                         (LetDAEExprOp
                            { __br_info =
                                foldl
                                  mergeInfo
                                  l33.info
                                  [ x7.info,
                                    l34.info,
                                    ntVal7.0,
                                    l35.info ],
                              __br_terms =
                                join
                                  [ [ l33.info ],
                                    [ x7.info ],
                                    [ l34.info ],
                                    [ l35.info ] ],
                              name =
                                [ { v =
                                      nameNoSym
                                        x7.val,
                                    i =
                                      x7.info } ],
                              arg =
                                [ ntVal7.1 ] }) },
             { nt =
                 #var"DAEExprPrefix",
               label =
                 {},
               rhs =
                 [ litSym
                     "reclet",
                   tokSym
                     (LIdentRepr
                        {}),
                   litSym
                     "=",
                   ntSym
                     #var"DAEExpr",
                   litSym
                     "in" ],
               action =
                 lam state38: {errors: Ref [(Info, [Char])], content: String}.
                   lam res38.
                     match
                       res38
                     with
                       [ LitParsed l36,
                         TokParsed (LIdentTok x8),
                         LitParsed l37,
                         UserSym ntVal8,
                         LitParsed l38 ]
                     in
                     let ntVal8: (Info, DAEExpr) =
                         fromDyn
                           ntVal8
                       in
                       asDyn
                         (RecLetDAEExprOp
                            { __br_info =
                                foldl
                                  mergeInfo
                                  l36.info
                                  [ x8.info,
                                    l37.info,
                                    ntVal8.0,
                                    l38.info ],
                              __br_terms =
                                join
                                  [ [ l36.info ],
                                    [ x8.info ],
                                    [ l37.info ],
                                    [ l38.info ] ],
                              name =
                                [ { v =
                                      nameNoSym
                                        x8.val,
                                    i =
                                      x8.info } ],
                              arg =
                                [ ntVal8.1 ] }) },
             { nt =
                 #var"DAEExprPostfix",
               label =
                 {},
               rhs =
                 [ litSym
                     "\'" ],
               action =
                 lam state39: {errors: Ref [(Info, [Char])], content: String}.
                   lam res39.
                     match
                       res39
                     with
                       [ LitParsed l39 ]
                     in
                     asDyn
                         (PrimDAEExprOp
                            { __br_info =
                                l39.info,
                              __br_terms =
                                [ l39.info ] }) },
             { nt =
                 #var"DAEEqnAtom",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"DAEExpr",
                   litSym
                     "=",
                   ntSym
                     #var"DAEExpr" ],
               action =
                 lam state40: {errors: Ref [(Info, [Char])], content: String}.
                   lam res40.
                     match
                       res40
                     with
                       [ UserSym ntVal9,
                         LitParsed l40,
                         UserSym ntVal10 ]
                     in
                     let ntVal9: (Info, DAEExpr) =
                         fromDyn
                           ntVal9
                       in
                       let ntVal10: (Info, DAEExpr) =
                         fromDyn
                           ntVal10
                       in
                       asDyn
                         (EqnDAEEqnOp
                            { __br_info =
                                foldl
                                  mergeInfo
                                  ntVal9.0
                                  [ l40.info,
                                    ntVal10.0 ],
                              __br_terms =
                                [ l40.info ],
                              left =
                                [ ntVal9.1 ],
                              right =
                                [ ntVal10.1 ] }) },
             { nt =
                 kleene2,
               label =
                 {},
               rhs =
                 [ litSym
                     ",",
                   tokSym
                     (LIdentRepr
                        {}),
                   ntSym
                     kleene2 ],
               action =
                 lam state41: {errors: Ref [(Info, [Char])], content: String}.
                   lam res41.
                     match
                       res41
                     with
                       [ LitParsed l41,
                         TokParsed (LIdentTok x9),
                         UserSym val5 ]
                     in
                     let val5: {names: [{i: Info, v: Name}], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val5
                       in
                       asDyn
                         { __br_info =
                             foldl
                               mergeInfo
                               l41.info
                               [ x9.info,
                                 val5.__br_info ],
                           __br_terms =
                             join
                               [ [ l41.info ],
                                 [ x9.info ],
                                 val5.__br_terms ],
                           names =
                             concat
                               [ { v =
                                     nameNoSym
                                       x9.val,
                                   i =
                                     x9.info } ]
                               val5.names } },
             { nt =
                 kleene2,
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state42: {errors: Ref [(Info, [Char])], content: String}.
                   lam res42.
                     match
                       res42
                     with
                       ""
                     in
                     asDyn
                         { __br_info =
                             NoInfo
                               {},
                           __br_terms =
                             "",
                           names =
                             "" } },
             { nt =
                 #var"DAEVarAtom",
               label =
                 {},
               rhs =
                 [ tokSym
                     (LIdentRepr
                        {}),
                   ntSym
                     kleene2,
                   litSym
                     ":",
                   ntSym
                     #var"DAEType" ],
               action =
                 lam state43: {errors: Ref [(Info, [Char])], content: String}.
                   lam res43.
                     match
                       res43
                     with
                       [ TokParsed (LIdentTok x10),
                         UserSym val5,
                         LitParsed l42,
                         UserSym ntVal11 ]
                     in
                     let val5: {names: [{i: Info, v: Name}], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val5
                       in
                       let ntVal11: (Info, DAEType) =
                         fromDyn
                           ntVal11
                       in
                       asDyn
                         (VarsDAEVarOp
                            { __br_info =
                                foldl
                                  mergeInfo
                                  x10.info
                                  [ val5.__br_info,
                                    l42.info,
                                    ntVal11.0 ],
                              __br_terms =
                                join
                                  [ [ x10.info ],
                                    val5.__br_terms,
                                    [ l42.info ] ],
                              names =
                                concat
                                  [ { v =
                                        nameNoSym
                                          x10.val,
                                      i =
                                        x10.info } ]
                                  val5.names,
                              ty =
                                [ ntVal11.1 ] }) },
             { nt =
                 #var"DAETopAtom",
               label =
                 {},
               rhs =
                 [ litSym
                     "let",
                   tokSym
                     (LIdentRepr
                        {}),
                   litSym
                     "=",
                   ntSym
                     #var"DAEExpr",
                   litSym
                     "end" ],
               action =
                 lam state44: {errors: Ref [(Info, [Char])], content: String}.
                   lam res44.
                     match
                       res44
                     with
                       [ LitParsed l43,
                         TokParsed (LIdentTok x11),
                         LitParsed l44,
                         UserSym ntVal12,
                         LitParsed l45 ]
                     in
                     let ntVal12: (Info, DAEExpr) =
                         fromDyn
                           ntVal12
                       in
                       asDyn
                         (LetDAETopOp
                            { __br_info =
                                foldl
                                  mergeInfo
                                  l43.info
                                  [ x11.info,
                                    l44.info,
                                    ntVal12.0,
                                    l45.info ],
                              __br_terms =
                                join
                                  [ [ l43.info ],
                                    [ x11.info ],
                                    [ l44.info ],
                                    [ l45.info ] ],
                              name =
                                [ { v =
                                      nameNoSym
                                        x11.val,
                                    i =
                                      x11.info } ],
                              arg =
                                [ ntVal12.1 ] }) },
             { nt =
                 #var"DAETopAtom",
               label =
                 {},
               rhs =
                 [ litSym
                     "reclet",
                   tokSym
                     (LIdentRepr
                        {}),
                   litSym
                     "=",
                   ntSym
                     #var"DAEExpr",
                   litSym
                     "end" ],
               action =
                 lam state45: {errors: Ref [(Info, [Char])], content: String}.
                   lam res45.
                     match
                       res45
                     with
                       [ LitParsed l46,
                         TokParsed (LIdentTok x12),
                         LitParsed l47,
                         UserSym ntVal13,
                         LitParsed l48 ]
                     in
                     let ntVal13: (Info, DAEExpr) =
                         fromDyn
                           ntVal13
                       in
                       asDyn
                         (RecLetDAETopOp
                            { __br_info =
                                foldl
                                  mergeInfo
                                  l46.info
                                  [ x12.info,
                                    l47.info,
                                    ntVal13.0,
                                    l48.info ],
                              __br_terms =
                                join
                                  [ [ l46.info ],
                                    [ x12.info ],
                                    [ l47.info ],
                                    [ l48.info ] ],
                              name =
                                [ { v =
                                      nameNoSym
                                        x12.val,
                                    i =
                                      x12.info } ],
                              arg =
                                [ ntVal13.1 ] }) },
             { nt =
                 kleene3,
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"DAETop",
                   ntSym
                     kleene3 ],
               action =
                 lam state46: {errors: Ref [(Info, [Char])], content: String}.
                   lam res46.
                     match
                       res46
                     with
                       [ UserSym ntVal14,
                         UserSym val6 ]
                     in
                     let ntVal14: (Info, DAETop) =
                         fromDyn
                           ntVal14
                       in
                       let val6: {tops: [DAETop], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val6
                       in
                       asDyn
                         { __br_info =
                             mergeInfo
                               ntVal14.0
                               val6.__br_info,
                           __br_terms =
                             val6.__br_terms,
                           tops =
                             concat
                               [ ntVal14.1 ]
                               val6.tops } },
             { nt =
                 kleene3,
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state47: {errors: Ref [(Info, [Char])], content: String}.
                   lam res47.
                     match
                       res47
                     with
                       ""
                     in
                     asDyn
                         { __br_info =
                             NoInfo
                               {},
                           __br_terms =
                             "",
                           tops =
                             "" } },
             { nt =
                 kleene4,
               label =
                 {},
               rhs =
                 [ litSym
                     ";",
                   ntSym
                     #var"DAEVar",
                   ntSym
                     kleene4 ],
               action =
                 lam state48: {errors: Ref [(Info, [Char])], content: String}.
                   lam res48.
                     match
                       res48
                     with
                       [ LitParsed l49,
                         UserSym ntVal15,
                         UserSym val7 ]
                     in
                     let ntVal15: (Info, DAEVar) =
                         fromDyn
                           ntVal15
                       in
                       let val7: {vars: [DAEVar], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val7
                       in
                       asDyn
                         { __br_info =
                             foldl
                               mergeInfo
                               l49.info
                               [ ntVal15.0,
                                 val7.__br_info ],
                           __br_terms =
                             concat
                               [ l49.info ]
                               val7.__br_terms,
                           vars =
                             concat
                               [ ntVal15.1 ]
                               val7.vars } },
             { nt =
                 kleene4,
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state49: {errors: Ref [(Info, [Char])], content: String}.
                   lam res49.
                     match
                       res49
                     with
                       ""
                     in
                     asDyn
                         { __br_info =
                             NoInfo
                               {},
                           __br_terms =
                             "",
                           vars =
                             "" } },
             { nt =
                 kleene5,
               label =
                 {},
               rhs =
                 [ litSym
                     ";",
                   ntSym
                     #var"DAEEqn",
                   ntSym
                     kleene5 ],
               action =
                 lam state50: {errors: Ref [(Info, [Char])], content: String}.
                   lam res50.
                     match
                       res50
                     with
                       [ LitParsed l50,
                         UserSym ntVal16,
                         UserSym val8 ]
                     in
                     let ntVal16: (Info, DAEEqn) =
                         fromDyn
                           ntVal16
                       in
                       let val8: {ieqns: [DAEEqn], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val8
                       in
                       asDyn
                         { __br_info =
                             foldl
                               mergeInfo
                               l50.info
                               [ ntVal16.0,
                                 val8.__br_info ],
                           __br_terms =
                             concat
                               [ l50.info ]
                               val8.__br_terms,
                           ieqns =
                             concat
                               [ ntVal16.1 ]
                               val8.ieqns } },
             { nt =
                 kleene5,
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state51: {errors: Ref [(Info, [Char])], content: String}.
                   lam res51.
                     match
                       res51
                     with
                       ""
                     in
                     asDyn
                         { __br_info =
                             NoInfo
                               {},
                           __br_terms =
                             "",
                           ieqns =
                             "" } },
             { nt =
                 alt2,
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state52: {errors: Ref [(Info, [Char])], content: String}.
                   lam res52.
                     match
                       res52
                     with
                       ""
                     in
                     asDyn
                         { __br_info =
                             NoInfo
                               {},
                           __br_terms =
                             "",
                           ieqns =
                             "" } },
             { nt =
                 alt2,
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"DAEEqn",
                   ntSym
                     kleene5 ],
               action =
                 lam state53: {errors: Ref [(Info, [Char])], content: String}.
                   lam res53.
                     match
                       res53
                     with
                       [ UserSym ntVal17,
                         UserSym val8 ]
                     in
                     let ntVal17: (Info, DAEEqn) =
                         fromDyn
                           ntVal17
                       in
                       let val8: {ieqns: [DAEEqn], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val8
                       in
                       asDyn
                         { __br_info =
                             mergeInfo
                               ntVal17.0
                               val8.__br_info,
                           __br_terms =
                             val8.__br_terms,
                           ieqns =
                             concat
                               [ ntVal17.1 ]
                               val8.ieqns } },
             { nt =
                 kleene6,
               label =
                 {},
               rhs =
                 [ litSym
                     ";",
                   ntSym
                     #var"DAEEqn",
                   ntSym
                     kleene6 ],
               action =
                 lam state54: {errors: Ref [(Info, [Char])], content: String}.
                   lam res54.
                     match
                       res54
                     with
                       [ LitParsed l51,
                         UserSym ntVal18,
                         UserSym val9 ]
                     in
                     let ntVal18: (Info, DAEEqn) =
                         fromDyn
                           ntVal18
                       in
                       let val9: {eqns: [DAEEqn], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val9
                       in
                       asDyn
                         { __br_info =
                             foldl
                               mergeInfo
                               l51.info
                               [ ntVal18.0,
                                 val9.__br_info ],
                           __br_terms =
                             concat
                               [ l51.info ]
                               val9.__br_terms,
                           eqns =
                             concat
                               [ ntVal18.1 ]
                               val9.eqns } },
             { nt =
                 kleene6,
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state55: {errors: Ref [(Info, [Char])], content: String}.
                   lam res55.
                     match
                       res55
                     with
                       ""
                     in
                     asDyn
                         { __br_info =
                             NoInfo
                               {},
                           __br_terms =
                             "",
                           eqns =
                             "" } },
             { nt =
                 #var"DAEProgAtom",
               label =
                 {},
               rhs =
                 [ ntSym
                     kleene3,
                   litSym
                     "variables",
                   ntSym
                     #var"DAEVar",
                   ntSym
                     kleene4,
                   litSym
                     "init",
                   ntSym
                     alt2,
                   litSym
                     "equations",
                   ntSym
                     #var"DAEEqn",
                   ntSym
                     kleene6,
                   litSym
                     "output",
                   ntSym
                     #var"DAEExpr" ],
               action =
                 lam state56: {errors: Ref [(Info, [Char])], content: String}.
                   lam res56.
                     match
                       res56
                     with
                       [ UserSym val6,
                         LitParsed l52,
                         UserSym ntVal19,
                         UserSym val7,
                         LitParsed l53,
                         UserSym val10,
                         LitParsed l54,
                         UserSym ntVal20,
                         UserSym val9,
                         LitParsed l55,
                         UserSym ntVal21 ]
                     in
                     let val6: {tops: [DAETop], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val6
                       in
                       let ntVal19: (Info, DAEVar) =
                         fromDyn
                           ntVal19
                       in
                       let val7: {vars: [DAEVar], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val7
                       in
                       let val10: {ieqns: [DAEEqn], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val10
                       in
                       let ntVal20: (Info, DAEEqn) =
                         fromDyn
                           ntVal20
                       in
                       let val9: {eqns: [DAEEqn], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val9
                       in
                       let ntVal21: (Info, DAEExpr) =
                         fromDyn
                           ntVal21
                       in
                       asDyn
                         (ProgDAEProgOp
                            { __br_info =
                                foldl
                                  mergeInfo
                                  val6.__br_info
                                  [ l52.info,
                                    ntVal19.0,
                                    val7.__br_info,
                                    l53.info,
                                    val10.__br_info,
                                    l54.info,
                                    ntVal20.0,
                                    val9.__br_info,
                                    l55.info,
                                    ntVal21.0 ],
                              __br_terms =
                                join
                                  [ val6.__br_terms,
                                    [ l52.info ],
                                    val7.__br_terms,
                                    [ l53.info ],
                                    val10.__br_terms,
                                    [ l54.info ],
                                    val9.__br_terms,
                                    [ l55.info ] ],
                              tops =
                                val6.tops,
                              vars =
                                concat
                                  [ ntVal19.1 ]
                                  val7.vars,
                              ieqns =
                                val10.ieqns,
                              eqns =
                                concat
                                  [ ntVal20.1 ]
                                  val9.eqns,
                              output =
                                [ ntVal21.1 ] }) },
             { nt =
                 #var"DAEExprAtom",
               label =
                 {},
               rhs =
                 [ litSym
                     "(",
                   ntSym
                     #var"DAEExpr",
                   litSym
                     ")" ],
               action =
                 lam #var"".
                   lam seq.
                     match
                       seq
                     with
                       [ LitParsed l56,
                         UserSym ntVal22,
                         LitParsed l57 ]
                     in
                     let ntVal22: (Info, DAEExpr) =
                         fromDyn
                           ntVal22
                       in
                       asDyn
                         (DAEExprGrouping
                            { __br_info =
                                foldl
                                  mergeInfo
                                  l56.info
                                  [ ntVal22.0,
                                    l57.info ],
                              __br_terms =
                                [ l56.info,
                                  l57.info ],
                              inner =
                                match
                                  [ ntVal22.1 ]
                                with
                                  [ x13 ]
                                in
                                x13 }) },
             { nt =
                 #var"DAEType",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"DAEType_lclosed" ],
               action =
                 lam #var"".
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym cont ]
                     in
                     fromDyn
                         cont
                         (Some
                            (breakableInitState
                               {})) },
             { nt =
                 #var"DAEType_lclosed",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"DAETypeAtom",
                   ntSym
                     #var"DAEType_lopen" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x13,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addDAETypeOpAtom
                                 p
                                 (fromDyn
                                    x13)
                                 st)) },
             { nt =
                 #var"DAEType_lopen",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"DAETypeInfix",
                   ntSym
                     #var"DAEType_lclosed" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x13,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addDAETypeOpInfix
                                 p
                                 (fromDyn
                                    x13)
                                 st)) },
             { nt =
                 #var"DAEType_lclosed",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"DAETypePrefix",
                   ntSym
                     #var"DAEType_lclosed" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x13,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addDAETypeOpPrefix
                                 p
                                 (fromDyn
                                    x13)
                                 st)) },
             { nt =
                 #var"DAEType_lopen",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"DAETypePostfix",
                   ntSym
                     #var"DAEType_lopen" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x13,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addDAETypeOpPostfix
                                 p
                                 (fromDyn
                                    x13)
                                 st)) },
             { nt =
                 #var"DAEType_lopen",
               label =
                 {},
               rhs =
                 "",
               action =
                 lam p.
                   lam #var"".
                     asDyn
                       (lam st.
                          finalizeDAETypeOp
                            p
                            st) },
             { nt =
                 #var"DAEConst",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"DAEConst_lclosed" ],
               action =
                 lam #var"".
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym cont ]
                     in
                     fromDyn
                         cont
                         (Some
                            (breakableInitState
                               {})) },
             { nt =
                 #var"DAEConst_lclosed",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"DAEConstAtom",
                   ntSym
                     #var"DAEConst_lopen" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x13,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addDAEConstOpAtom
                                 p
                                 (fromDyn
                                    x13)
                                 st)) },
             { nt =
                 #var"DAEConst_lopen",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"DAEConstInfix",
                   ntSym
                     #var"DAEConst_lclosed" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x13,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addDAEConstOpInfix
                                 p
                                 (fromDyn
                                    x13)
                                 st)) },
             { nt =
                 #var"DAEConst_lclosed",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"DAEConstPrefix",
                   ntSym
                     #var"DAEConst_lclosed" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x13,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addDAEConstOpPrefix
                                 p
                                 (fromDyn
                                    x13)
                                 st)) },
             { nt =
                 #var"DAEConst_lopen",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"DAEConstPostfix",
                   ntSym
                     #var"DAEConst_lopen" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x13,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addDAEConstOpPostfix
                                 p
                                 (fromDyn
                                    x13)
                                 st)) },
             { nt =
                 #var"DAEConst_lopen",
               label =
                 {},
               rhs =
                 "",
               action =
                 lam p.
                   lam #var"".
                     asDyn
                       (lam st.
                          finalizeDAEConstOp
                            p
                            st) },
             { nt =
                 #var"DAEPat",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"DAEPat_lclosed" ],
               action =
                 lam #var"".
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym cont ]
                     in
                     fromDyn
                         cont
                         (Some
                            (breakableInitState
                               {})) },
             { nt =
                 #var"DAEPat_lclosed",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"DAEPatAtom",
                   ntSym
                     #var"DAEPat_lopen" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x13,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addDAEPatOpAtom
                                 p
                                 (fromDyn
                                    x13)
                                 st)) },
             { nt =
                 #var"DAEPat_lopen",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"DAEPatInfix",
                   ntSym
                     #var"DAEPat_lclosed" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x13,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addDAEPatOpInfix
                                 p
                                 (fromDyn
                                    x13)
                                 st)) },
             { nt =
                 #var"DAEPat_lclosed",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"DAEPatPrefix",
                   ntSym
                     #var"DAEPat_lclosed" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x13,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addDAEPatOpPrefix
                                 p
                                 (fromDyn
                                    x13)
                                 st)) },
             { nt =
                 #var"DAEPat_lopen",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"DAEPatPostfix",
                   ntSym
                     #var"DAEPat_lopen" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x13,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addDAEPatOpPostfix
                                 p
                                 (fromDyn
                                    x13)
                                 st)) },
             { nt =
                 #var"DAEPat_lopen",
               label =
                 {},
               rhs =
                 "",
               action =
                 lam p.
                   lam #var"".
                     asDyn
                       (lam st.
                          finalizeDAEPatOp
                            p
                            st) },
             { nt =
                 #var"DAEExpr",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"DAEExpr_lclosed" ],
               action =
                 lam #var"".
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym cont ]
                     in
                     fromDyn
                         cont
                         (Some
                            (breakableInitState
                               {})) },
             { nt =
                 #var"DAEExpr_lclosed",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"DAEExprAtom",
                   ntSym
                     #var"DAEExpr_lopen" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x13,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addDAEExprOpAtom
                                 p
                                 (fromDyn
                                    x13)
                                 st)) },
             { nt =
                 #var"DAEExpr_lopen",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"DAEExprInfix",
                   ntSym
                     #var"DAEExpr_lclosed" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x13,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addDAEExprOpInfix
                                 p
                                 (fromDyn
                                    x13)
                                 st)) },
             { nt =
                 #var"DAEExpr_lclosed",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"DAEExprPrefix",
                   ntSym
                     #var"DAEExpr_lclosed" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x13,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addDAEExprOpPrefix
                                 p
                                 (fromDyn
                                    x13)
                                 st)) },
             { nt =
                 #var"DAEExpr_lopen",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"DAEExprPostfix",
                   ntSym
                     #var"DAEExpr_lopen" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x13,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addDAEExprOpPostfix
                                 p
                                 (fromDyn
                                    x13)
                                 st)) },
             { nt =
                 #var"DAEExpr_lopen",
               label =
                 {},
               rhs =
                 "",
               action =
                 lam p.
                   lam #var"".
                     asDyn
                       (lam st.
                          finalizeDAEExprOp
                            p
                            st) },
             { nt =
                 #var"DAEEqn",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"DAEEqn_lclosed" ],
               action =
                 lam #var"".
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym cont ]
                     in
                     fromDyn
                         cont
                         (Some
                            (breakableInitState
                               {})) },
             { nt =
                 #var"DAEEqn_lclosed",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"DAEEqnAtom",
                   ntSym
                     #var"DAEEqn_lopen" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x13,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addDAEEqnOpAtom
                                 p
                                 (fromDyn
                                    x13)
                                 st)) },
             { nt =
                 #var"DAEEqn_lopen",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"DAEEqnInfix",
                   ntSym
                     #var"DAEEqn_lclosed" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x13,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addDAEEqnOpInfix
                                 p
                                 (fromDyn
                                    x13)
                                 st)) },
             { nt =
                 #var"DAEEqn_lclosed",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"DAEEqnPrefix",
                   ntSym
                     #var"DAEEqn_lclosed" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x13,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addDAEEqnOpPrefix
                                 p
                                 (fromDyn
                                    x13)
                                 st)) },
             { nt =
                 #var"DAEEqn_lopen",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"DAEEqnPostfix",
                   ntSym
                     #var"DAEEqn_lopen" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x13,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addDAEEqnOpPostfix
                                 p
                                 (fromDyn
                                    x13)
                                 st)) },
             { nt =
                 #var"DAEEqn_lopen",
               label =
                 {},
               rhs =
                 "",
               action =
                 lam p.
                   lam #var"".
                     asDyn
                       (lam st.
                          finalizeDAEEqnOp
                            p
                            st) },
             { nt =
                 #var"DAEVar",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"DAEVar_lclosed" ],
               action =
                 lam #var"".
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym cont ]
                     in
                     fromDyn
                         cont
                         (Some
                            (breakableInitState
                               {})) },
             { nt =
                 #var"DAEVar_lclosed",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"DAEVarAtom",
                   ntSym
                     #var"DAEVar_lopen" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x13,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addDAEVarOpAtom
                                 p
                                 (fromDyn
                                    x13)
                                 st)) },
             { nt =
                 #var"DAEVar_lopen",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"DAEVarInfix",
                   ntSym
                     #var"DAEVar_lclosed" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x13,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addDAEVarOpInfix
                                 p
                                 (fromDyn
                                    x13)
                                 st)) },
             { nt =
                 #var"DAEVar_lclosed",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"DAEVarPrefix",
                   ntSym
                     #var"DAEVar_lclosed" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x13,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addDAEVarOpPrefix
                                 p
                                 (fromDyn
                                    x13)
                                 st)) },
             { nt =
                 #var"DAEVar_lopen",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"DAEVarPostfix",
                   ntSym
                     #var"DAEVar_lopen" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x13,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addDAEVarOpPostfix
                                 p
                                 (fromDyn
                                    x13)
                                 st)) },
             { nt =
                 #var"DAEVar_lopen",
               label =
                 {},
               rhs =
                 "",
               action =
                 lam p.
                   lam #var"".
                     asDyn
                       (lam st.
                          finalizeDAEVarOp
                            p
                            st) },
             { nt =
                 #var"DAETop",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"DAETop_lclosed" ],
               action =
                 lam #var"".
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym cont ]
                     in
                     fromDyn
                         cont
                         (Some
                            (breakableInitState
                               {})) },
             { nt =
                 #var"DAETop_lclosed",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"DAETopAtom",
                   ntSym
                     #var"DAETop_lopen" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x13,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addDAETopOpAtom
                                 p
                                 (fromDyn
                                    x13)
                                 st)) },
             { nt =
                 #var"DAETop_lopen",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"DAETopInfix",
                   ntSym
                     #var"DAETop_lclosed" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x13,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addDAETopOpInfix
                                 p
                                 (fromDyn
                                    x13)
                                 st)) },
             { nt =
                 #var"DAETop_lclosed",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"DAETopPrefix",
                   ntSym
                     #var"DAETop_lclosed" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x13,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addDAETopOpPrefix
                                 p
                                 (fromDyn
                                    x13)
                                 st)) },
             { nt =
                 #var"DAETop_lopen",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"DAETopPostfix",
                   ntSym
                     #var"DAETop_lopen" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x13,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addDAETopOpPostfix
                                 p
                                 (fromDyn
                                    x13)
                                 st)) },
             { nt =
                 #var"DAETop_lopen",
               label =
                 {},
               rhs =
                 "",
               action =
                 lam p.
                   lam #var"".
                     asDyn
                       (lam st.
                          finalizeDAETopOp
                            p
                            st) },
             { nt =
                 #var"DAEProg",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"DAEProg_lclosed" ],
               action =
                 lam #var"".
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym cont ]
                     in
                     fromDyn
                         cont
                         (Some
                            (breakableInitState
                               {})) },
             { nt =
                 #var"DAEProg_lclosed",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"DAEProgAtom",
                   ntSym
                     #var"DAEProg_lopen" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x13,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addDAEProgOpAtom
                                 p
                                 (fromDyn
                                    x13)
                                 st)) },
             { nt =
                 #var"DAEProg_lopen",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"DAEProgInfix",
                   ntSym
                     #var"DAEProg_lclosed" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x13,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addDAEProgOpInfix
                                 p
                                 (fromDyn
                                    x13)
                                 st)) },
             { nt =
                 #var"DAEProg_lclosed",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"DAEProgPrefix",
                   ntSym
                     #var"DAEProg_lclosed" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x13,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addDAEProgOpPrefix
                                 p
                                 (fromDyn
                                    x13)
                                 st)) },
             { nt =
                 #var"DAEProg_lopen",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"DAEProgPostfix",
                   ntSym
                     #var"DAEProg_lopen" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x13,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addDAEProgOpPostfix
                                 p
                                 (fromDyn
                                    x13)
                                 st)) },
             { nt =
                 #var"DAEProg_lopen",
               label =
                 {},
               rhs =
                 "",
               action =
                 lam p.
                   lam #var"".
                     asDyn
                       (lam st.
                          finalizeDAEProgOp
                            p
                            st) } ] })
  in
  match
    target
  with
    Right table
  in
  table
let parseDAEParse =
  lam filename.
    lam content.
      use ParseDAEParse
      in
      let config8 =
        { errors =
            ref
              "",
          content =
            content }
      in
      let res57 =
        parseWithTable
          _table
          filename
          config8
          content
      in
      let #var"X" =
        (res57, deref
          config8.errors)
      in
      match
        #var"X"
      with
        (Right dyn, "")
      then
        match
          fromDyn
            dyn
        with
          (_, res57)
        in
        Right
            res57
      else
        match
          #var"X"
        with
          (Left err, errors)
        then
          let err =
            ll1DefaultHighlight
              content
              (ll1ToErrorHighlightSpec
                 err)
          in
          Left
            (snoc
               errors
               err)
        else
          match
            #var"X"
          with
            (_, errors)
          in
          Left
              errors
let parseDAEParseExn =
  lam filename.
    lam content.
      let #var"X" =
        parseDAEParse
          filename
          content
      in
      match
        #var"X"
      with
        Left errors
      then
        (for_
             errors
             (lam x13.
                match
                  x13
                with
                  (info, msg)
                in
                printLn
                    (infoErrorString
                       info
                       msg)))
        ; exit
          1
      else
        match
          #var"X"
        with
          Right file
        in
        file
mexpr
{}