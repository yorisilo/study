let rec fix f x = f (fix f) x;;

let rec fixs f = f (fix f);;

(* let rec fix_ f x = .< fix f x>.;; *)

let rec fix_ f x = .< fix f x>.;;

let fibp = fun f n -> (if n == 0 || n == 1
                       then 1
                       else f (n-1) + f (n-2))

let power = fun x -> fix (fun f n -> if n == 0
                           then 1
                           else x * f (n-1))

let power_ = fun x -> fix (fun f n -> if n == 0
                            then .<1>.
                            else .<.~x * .~(f (n-1))>. )

let gen_power5 x = power_ .<x>. 5

let test = fun x -> power_ .<x>. 8
