open Syntax

type gamvar = string
type gam =
  | GVar of gamvar
  | GPair of gam * gam

type tyvar = string

type ty =
  | TVar of tyvar
  | TInt
  | TBool
  | T0Arrow of ty * ty * delta
  | T0Code of ty * gam
  | T1Arrow of ty * ty
and
  delta =
  | EpsD
  | ConsD of delta * ty

type tyk =
  | TKArrow of (ty * gam) * (ty * gam) * delta (* ty1 * gam := T0Code *)

type tyenv = (tyvar * ty) list
(* constr = list *)

type ge = (ty * ty)

type genv =
  | G of expr * ty

type constr =
  | CModelT0 of genv * ge
  | CModelC of G * ge
