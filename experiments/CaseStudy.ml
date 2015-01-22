(* Experiment in OCaml, to take advantage of equirecursive types
 *
 * Advantage:
 * - equirecursive types out of the box
 * - polymorphic variants
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


type term =
  [= `Lit of int
  |  `Var of string
  |  `Abs of (string * term)
  |  `App of (term * term)
  ];

(* equirecursive types out of the box! *)
value t : term =
  `Abs "f"
    (`App
      (`App
        (`Var "f")
        (`App (`Var "g") (`Lit 2)))
      (`App (`Var "h") (`Lit 3)));


module type Functor = sig
  type map 'a;
  value fmap : ('a -> 'b) -> (map 'a -> map 'b);
end;

module type Applicative = sig
  include Functor;
  value pure  : 'a -> map 'a;
  value (<*>) : map ('a -> 'b) -> map 'a -> map 'b;
end;

(* applicative functors without the obligation to define `fmap` *)
module type PureCall = sig
  type map 'a;
  value pure  : 'a -> map 'a;
  value (<*>) : map ('a -> 'b) -> map 'a -> map 'b;
end;

(* default implementation of `fmap` in terms of `pure` and `<*>` *)
module Applicative (PC : PureCall) = struct
  include PC;
  value fmap f x = pure f <*> x;
end;

(* Haskell's Data.Monoid *)
module type Monoid = sig
 type tpe;                          (* carrier set *)
 value mempty  : tpe;               (* identity *)
 value mappend : tpe -> tpe -> tpe; (* associative operator *)
end;

(* examples of applicative functors *)
module Applicative = struct
  (* the identity functor is applicative *)
  module Id = Applicative (struct
    type  map 'a    = 'a;
    value pure x    = x;
    value (<*>) f x = f x;
  end);

  (* a constant functor into a monoid is applicative *)
  module Const (M : Monoid) = Applicative (struct
    open M;
    type  map 'a    = tpe;
    value pure x    = mempty;
    value (<*>) f x = mappend f x;
  end);
end;

(* traversable functors distribute over applicative functors
 * in a weak way
 *)
module type Traversable = sig
  include Functor;
  module Traverse : functor (G : Applicative) -> sig
    value run : ('a -> G.map 'b) -> (map 'a -> G.map (map 'b));

    (* witness that traversable functors distribute over
     * applicative functors
     *)
    value seq_a : map (G.map 'a) -> G.map (map 'a);
  end;
end;

(* Traversable with neither fmap nor seq_a *)
module type Traverse = sig
  type map 'a;
  module Traverse : functor (G : Applicative) -> sig
    value run : ('a -> G.map 'b) -> (map 'a -> G.map (map 'b));
  end;
end;

(* default implementations of `fmap` and `seq_a` given `traverse` *)
module Traversable (T : Traverse) = struct
  type map 'a = T.map 'a;

  module Traverse (G : Applicative) = struct
    open G;
    include T.Traverse G;
    value seq_a = run pure;
  end;

  module TraverseId = Traverse Applicative.Id;

  value fmap = TraverseId.run;

  (* PROBLEM: cannot inline the functor application `TraverseId`
   *          into the body of `fmap` and typecheck.
   *)
end;

module TermF = Traversable (struct
  type map 't =
    [= `Lit of int
    |  `Var of string
    |  `Abs of (string * 't)
    |  `App of ('t * 't)
    ];

  (* Traverse.run can be generated from the type constructor TermF.map *)
  module Traverse (G : Applicative) = struct
    value run (f : 'a -> G.map 'b) (t : map 'a): G.map (map 'b) =
      let open G in match t with
      [ `Lit n   -> pure (fun x -> `Lit x) <*> pure n
      | `Var x   -> pure (fun x -> `Var x) <*> pure x
      | `Abs x t -> pure (fun x y -> `Abs x y) <*> pure x <*> f t
      | `App s t -> pure (fun x y -> `App x y) <*> f s <*> f t
      ];
  end;
end);

(* PROBLEM: unable to typecheck `cata` over functors.
 *
 * Error: The type abbreviation fixF is cyclic
 *
module Cata (F : Traversable) = struct
  type fixF = F.map fixF;
  value run (algebra : F.map 'a -> 'a) (t : fixF): 'a = raise Not_found;
end;
*)

(* given an algebra of TermF, compute the corresponding catamorphism
 * a catamorphism is the unique morphism from the initial algebra
 * to the given algebra
 *)
value rec foldTerm (algebra: TermF.map 'a -> 'a) (t: term): 'a =
  algebra (TermF.fmap (foldTerm algebra) t);

(* usage example: free variables *)
value fv : (term -> list string) =
  foldTerm (fun x -> match x with
    [ `Lit n   -> []
    | `Var x   -> [x]
    | `Abs x t -> List.filter (fun y -> String.compare x y != 0) t
    | `App s t -> List.append s t
    ]
  );
