module M =
struct
  exception Error of string

  type sxp =
    | I of int          (* Integer *)
    | A of string       (* Atoms  *)
    | S of string       (* String *)
    | L of sxp list     (* List   *)

  type dom =
    | Bool of bool
    | Int of int | Str of string
    | Fun of int * (dom list -> dom)
    | Undefined
    | Void
    | Empty | Cons of dom ref * dom ref

  type svar = Val of dom code
            | Ref of (dom ref) code
              (* type 'a svar = Val of ('a, dom) code | Ref of ('a, dom ref) code *)
end
