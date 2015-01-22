(* Experiment in OCaml, to take advantage of equirecursive types
 *
 * Conclusion:
 * - OCaml seems unsuitable for hosting first-class regular functors.
 *   Cai can't encode the type of `traverse` in OCaml.
 *   See `value traversable`.
 *
 * Advantage:
 * - equirecursive types out of the box
 *
 * Problem:
 * - how to write `cata`?
 *
 * Dependencies:
 * - OCaml
 * - CamlP4
 *
 * Installation on mac:
 * 1. install "homebrew"
 * 2. execute `brew install opam`
 *
 * Execution:
 *   ocaml -rectypes dynlink.cma camlp4r.cma <this-file>
 *)


type termT 'a 'b 'c 'd 'e 'f =
  [ Lit of 'a
  | Var of 'b
  | Abs of ('c * 'd)
  | App of ('e * 'f)
  ] ;

type term = termT int string string term term term;

(* equirecursive types out of the box! *)
value t : term =
  Abs "f"
    (App
      (App
        (Var "f")
        (App (Var "g") (Lit 2)))
      (App (Var "h") (Lit 3)));

(* applicative functors work rather well. *)

module type Type = sig
  type tpe;
end;

module type Map = sig
  type map 'a;
end;

module type Functor = sig
  include Map;
  value map : ('a -> 'b) -> (map 'a -> map 'b);
end;

module type PureCall = sig
  include Map;
  value pure  : 'a -> map 'a;
  value (<*>) : map ('a -> 'b) -> map 'a -> map 'b;
end;

module type Applicative = sig
  include Functor;
  value pure  : 'a -> map 'a;
  value (<*>) : map ('a -> 'b) -> map 'a -> map 'b;
end;

module type PureCall = sig
  include Map;
  value pure  : 'a -> map 'a;
  value (<*>) : map ('a -> 'b) -> map 'a -> map 'b;
end;

module Applicative (PC : PureCall) = struct
  include PC;
  value map f x = pure f <*> x;
end;

module type Traverse = functor (G : Applicative) -> sig
  include Map;
  value traverse : ('a -> G.map 'b) -> map 'a -> G.map (map 'b);
end;

module type Trav = functor (M : Map) -> functor (G : Applicative) -> sig
  value traverse : ('a -> G.map 'b) -> M.map 'a -> G.map (M.map 'b);
end;

module type Traversable = sig
  include Functor;
  module Traverse : functor (G : Applicative) -> sig
    value run : ('a -> G.map 'b) -> (map 'a -> G.map (map 'b));
  end;
end;

module type Traverse = sig
  include Map;
  module Traverse : functor (G : Applicative) -> sig
    value run : ('a -> G.map 'b) -> (map 'a -> G.map (map 'b));
  end;
end;

(*
module type Traversable = functor (G : Applicative) -> sig
  include Functor;
  value traverse : ('a -> G.map 'b) -> map 'a -> G.map (map 'b);
end;
*)

module type Monoid = sig
  include Type;
  value zero : tpe;
  value (+)  : tpe -> tpe -> tpe;
end;

module Applicative = struct

  (* repeat value `id` as submodule.
   * does not work, either.
   * see `value traversable`.
   *)
  module Id = Applicative (struct
    type  map 'a = 'a;
    value pure x = x;
    value (<*>) f x = f x;
  end);


  module Const (M : Monoid) = Applicative (struct
    open M;
    type map 'a = tpe;
    value pure x = zero;
    value (<*>) f x = f + x;
  end);
end;

module Traversable (T : Traverse) = struct
  type map 'a = T.map 'a;
  module Traverse = T.Traverse;

  module TraverseId = Traverse Applicative.Id;

  value map = TraverseId.run;
end;


module TermF = Traversable (struct
  type map 't = termT int string string 't 't 't;

  module Traverse (G : Applicative) = struct
    value run (f : 'a -> G.map 'b) (t : map 'a): G.map (map 'b) =
      let open G in match t with
      [ Lit n   -> pure (fun x -> Lit x) <*> pure n
      | Var x   -> pure (fun x -> Var x) <*> pure x
      | Abs x t -> pure (fun x y -> Abs x y) <*> pure x <*> f t
      | App s t -> pure (fun x y -> App x y) <*> f s <*> f t
      ];
  end;
end);


(* Error: The type abbreviation fixF is cyclic
module Cata (F : Traversable) = struct
  type fixF = F.map fixF;
  value run (algebra : F.map 'a -> 'a) (t : fixF): 'a = raise Not_found;
end;
*)

value rec foldTerm (algebra: TermF.map 'a -> 'a) (t: term): 'a =
  algebra (TermF.map (foldTerm algebra) t);

(* usage example: free variables *)
value fv : (term -> list string) =
  foldTerm (fun x -> match x with
    [ Lit n   -> []
    | Var x   -> [x]
    | Abs x t -> List.filter (fun y -> String.compare x y != 0) t
    | App s t -> List.append s t
    ]
  );
