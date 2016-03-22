let module M =
struct
  type foo = Foo | Bar of int
end
in let open M in
let x = Foo in match x with Bar z -> z
