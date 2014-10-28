package nominal
package lib

import scala.util.hashing.MurmurHash3
import Fix.Record

object Tuple { tuple =>
  //@tupledata def t2[a1, a2] = T2(_1 = a1, _2 = a2)
  //@tupledata def t3[a1, a2, a3] = T3(_1 = a1, _2 = a2, _3 = a3)
  //@tupledata def t4[a1, a2, a3, a4] = T4(_1 = a1, _2 = a2, _3 = a3, _4 = a4)
  // ..etc.

  final case class _2[+A, +B](_1: A, _2: B) extends Record
  final case class _3[+A, +B, +C](_1: A, _2: B, _3: C) extends Record
  final case class _4[+A, +B, +C, +D](_1: A, _2: B, _3: C, d: D) extends Record

  // would be nice if we could say `Tuple2.extend(...)`
  object _2 extends Traversable.EndofunctorTrait2 {
    type Map[+A, +B] = _2[A, B]

    def traverse[A, B, C, D](G: Applicative)(f: A => G.Map[C], g: B => G.Map[D]):
        Map[A, B] => G.Map[Map[C, D]] = {
      case tuple._2(x, y) =>
        G.call(G.call(
          G.pure[C => D => _2[C, D]](x => y => _2(x, y)),
          f(x)),
          g(y))
    }
  }

  object _3 extends Traversable.EndofunctorTrait3 {
    type Map[+A, +B, +C] = _3[A, B, C]
    def traverse[A, B, C, D, E, F](G: Applicative)
      (f: A => G.Map[D], g: B => G.Map[E], h: C => G.Map[F]):
        Map[A, B, C] => G.Map[Map[D, E, F]] = {
      case tuple._3(x, y, z) =>
        G.call(G.call(G.call(
          G.pure[D => E => F => _3[D, E, F]](x => y => z => _3(x, y, z)),
          f(x)),
          g(y)),
          h(z))
    }
  }

  object _4 extends Traversable.EndofunctorTrait4 {
    type Map[+A, +B, +C, +D] = _4[A, B, C, D]
    def traverse[A, B, C, D, W, X, Y, Z](G: Applicative)
      (f: A => G.Map[W], g: B => G.Map[X], h: C => G.Map[Y], k: D => G.Map[Z]):
        Map[A, B, C, D] => G.Map[Map[W, X, Y, Z]] = {
      case tuple._4(w, x, y, z) =>
        G.call(G.call(G.call(G.call(
          G.pure[W => X => Y => Z => _4[W, X, Y, Z]](w => x => y => z => _4(w, x, y, z)),
          f(w)),
          g(x)),
          h(y)),
          k(z))
    }
  }

  // mimics case class methods
  trait CaseClass extends Serializable {
    val get: Any

    override def toString: String = s"${getClass.getSimpleName}$get"

    override def hashCode: Int =
      MurmurHash3.mix(getClass.hashCode, get.hashCode)

    override def equals(that: Any) = that match {
      case that: CaseClass =>
        this.getClass == that.getClass & this.get == that.get

      case _ =>
        false
    }
  }
}
