package creg
package lib

import language.higherKinds

trait Functor {
  type Map[+A]
  def fmap[A, B](f: A => B): Map[A] => Map[B]
}
