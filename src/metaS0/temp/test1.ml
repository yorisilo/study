module Tree =
struct
  type ('a, 'b) t = Empty
                  | Node of ('a, 'b) t * 'a * 'b * ('a, 'b) t

end;;
