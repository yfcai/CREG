package creg

import language.higherKinds

// much as I would like to make `Fix` path-dependent
// on some functor, we need the type param `F` for
// coercion. If there are too many levels of nested
// path-dependent types then scalac will gice up and
// refuese to tell us anything.
sealed trait Fix[+F[+_]] { def unroll: F[Fix[F]] }

sealed case class Roll[+F[+_]](unroll: F[Fix[F]]) extends Fix[F]

object Fix {
  // dummy class to help scalac figure out the expected result type
  // of an implicit conversion. it is less straightforward than
  // expected. here we use the collection.breakOut + CanBuildFrom
  // pattern.
  //
  // covariance of type parameter is not option.
  class TypeWitness[+T]
  object TypeWitness extends TypeWitness[Nothing] {
    implicit def get[T]: TypeWitness[T] = this
  }

  // marker of variants and records
  // beware: because records extends variants, they will
  // be marked as variants, too.
  //
  // if x is a subtype of both Record and Variant, then it is a record
  // if x is a subtype of Variant, then it is a variant
  // if x is a subtype of neither, then it is not a datatype
  trait RecordOrVariant
  trait Variant extends RecordOrVariant
  trait Record  extends RecordOrVariant
}
