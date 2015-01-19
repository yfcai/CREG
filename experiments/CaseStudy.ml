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
 * Fatal flaws:
 * - no higher-kinded type variables
 * - cannot type `traverse`
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

value applicative (module PC : PureCall) : (module Applicative) =
  (module struct
    include PC;
    value map f x = pure f <*> x;
  end);

module type Traverse = functor (G : Applicative) -> sig
  include Map;
  value traverse : ('a -> G.map 'b) -> map 'a -> G.map (map 'b);
end;

module type Trav = functor (M : Map) -> functor (G : Applicative) -> sig
  value traverse : ('a -> G.map 'b) -> M.map 'a -> G.map (M.map 'b);
end;

module type Traversable = functor (G : Applicative) -> sig
  include Functor;
  value traverse : ('a -> G.map 'b) -> map 'a -> G.map (map 'b);
end;

module type Monoid = sig
  include Type;
  value zero : tpe;
  value (+)  : tpe -> tpe -> tpe;
end;

module Applicative = struct

  value id : (module Applicative) = applicative
    (module struct
      type map 'a = 'a;
      value pure x = x;
      value (<*>) f x = f x;
    end);

  (* repeat value `id` as submodule.
   * does not work, either.
   * see `value traversable`.
   *)
  module Id : Applicative = struct
    type  map 'a = 'a;
    value map f = f;
    value pure x = x;
    value (<*>) f x = f x;
  end;


  value const (module M : Monoid) : (module Applicative) = applicative
    (module struct
      open M;
      type map 'a = tpe;
      value pure x = zero;
      value (<*>) f x = f + x;
    end);
end;

(* first unsuccessful attempt to encode "all traversables are functors" *)
value traversable (module T : Traverse) : (module Traversable) =
  (module functor (G : Applicative) -> struct
    include T G;

    module TId = T Applicative.Id;

    (* cai 13.01.2015:
     * want to call `traverse Applicative.id`,
     * but I couldn't find a well-typed encoding of it.
     *)
    value map = raise Not_found;
  end);

(* 2nd unsuccessful attempt to encode "all traversables are functors" *)
module MkTraversable
  (M : Map)
  (T : functor (G : Applicative) -> sig
         value traverse : ('a -> G.map 'b) -> M.map 'a -> G.map (M.map 'b);
       end) : functor (G : Applicative) -> sig
                type map 'a = M.map 'a;
                value map : ('a -> 'b) -> map 'a -> map 'b;
                value traverse : ('a -> G.map 'b) -> map 'a -> G.map (map 'b);
              end =
  functor (G : Applicative) -> struct
    type map 'a = M.map 'a;

    module TG = T G;
    module TI = T Applicative.Id;

    value traverse = TG.traverse;

    value map f x = raise Not_found;
      (* TI.traverse f x *)
      (* signature mismatch: `Applicative.Id.map 'b` is not reduced to `'b` *)
  end;
