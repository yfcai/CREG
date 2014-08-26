package nominal
package lib

import language.higherKinds

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
  object TypeWitness {
    implicit def spawn[T]: TypeWitness[T] = new TypeWitness
  }
}
