package nominal
package lib

import language.higherKinds

sealed trait Fix[+F[+_]] { def unroll: F[Fix[F]] }

sealed case class Roll[+F[+_]](unroll: F[Fix[F]]) extends Fix[F]
