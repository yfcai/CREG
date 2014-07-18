// [failed] experiment in expressing the idea of endofunctor with expoinents in scala
// Every applicative functor's domain is a category with exponentials.
// If subcategories with exponentials were expressible, then
// we don't have to restrict the domain of applicative functors to the entire scala category.
// Sadly they weren't, and we must.

import language.higherKinds

trait FunctorsOverSubcategories {
  trait Functor {
    type Domain
    type Map[+ Obj <: Domain]
    type Range = Map[Domain]

    def fmap[A <: Domain, B <: Domain](f: A => B, mA: Map[A]): Map[B]
  }

  trait Endofunctor extends Functor {
    type Domain
    type Map[+ Obj <: Domain] <: Domain
  }

  trait FunctorOverCatWithExponents extends Functor {
    // i. e., for all A, B <: Domain we have (A => B) <: Domain
    // failed due to "illegal cyclic reference involving type Domain"
    // type Domain >: (Nothing => Domain)
  }
}
