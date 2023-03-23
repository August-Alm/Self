namespace Bound

module Bound =

  type Var<'a, 'b> = F of 'a | B of 'b

  let unvar fa fb v =
    match v with
    | F x -> fa x
    | B y -> fb y