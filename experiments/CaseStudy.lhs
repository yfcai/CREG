> {-# LANGUAGE LiberalTypeSynonyms, RankNTypes #-}
> import Data.List

User writes:

  data Term = Unit
            | Var String
            | Abs String Term
            | App Term Term

System generates:

> data TermT a b c d e = Unit
>                      | Var a
>                      | Abs b c
>                      | App d e
>
> -- want to generate
> --
> --   type TermF t = TermT String String t t t
> --   type Term = Fix TermF
> --
> -- but have to generate TermS to work around GHC forbidding partially
> -- applied type synonyms
>
> data TermS a b = Roll {
>   unroll :: TermT a b (TermS a b) (TermS a b) (TermS a b)
> }
>
> type Term = TermS String String
>
> -- not sure what this class is
> data Mo w t = Mo
>   { ret  :: forall a. a -> w a
>   , bind :: forall b. w (t -> b) -> t -> w b
>   }
>
> class Data t where
>   gfoldl :: Mo w r -> t -> w t

[TODO: Haskell too restrictive. Do this in Scala.]


User writes:

  mapVar = fmapOf (\t -> Term { var = Var t })

System generates:

> type VarF v = TermS v String
>
> mapVar :: (a -> b) -> VarF a -> VarF b
> mapVar f t =
>   let
>     recurse = mapVar f
>   in
>     Roll $ case unroll t of
>       Unit -> Unit
>       Var x -> Var (f x)
>       Abs x t -> Abs x (recurse t)
>       App s t -> App (recurse s) (recurse t)

User writes:

> -- list of all free variables
> --freevars :: Term -> [String]
> --freevars t = nub (collect (mapVar singleton t))
> --  where
> --    singleton x = [x]
> --    -- collect free names, retain duplicates
> --    collect t = undefined
>
> newtype FV t = FV [String]
>



