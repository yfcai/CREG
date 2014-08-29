/** Cargo code from:
  * http://stackoverflow.com/a/16826132/3968633
  *
  * "boxing is supposed to be invisible, plus or minus".
  * I don't know if this case is plus or minus.
  *                                         ---som-snytt
  */
package nominal.util

import reflect._

object ClassTagForPrimitives {
  implicit class ClassTagWithPrimitiveUnderConsideration[A](t: ClassTag[A]) extends ClassTag[A] {
    override def runtimeClass = t.runtimeClass

    def safeCast(x: Any): Option[A] = (
      if (t.runtimeClass.isPrimitive) {
        val ok = x match {
          case _: java.lang.Integer   => runtimeClass == java.lang.Integer.TYPE
              //case _: java.lang.Double    => runtimeClass == java.lang.Double.TYPE
          case _: java.lang.Double    => t == ClassTag.Double  // equivalent
          case _: java.lang.Long      => runtimeClass == java.lang.Long.TYPE
          case _: java.lang.Character => runtimeClass == java.lang.Character.TYPE
          case _: java.lang.Float     => runtimeClass == java.lang.Float.TYPE
          case _: java.lang.Byte      => runtimeClass == java.lang.Byte.TYPE
          case _: java.lang.Short     => runtimeClass == java.lang.Short.TYPE
          case _: java.lang.Boolean   => runtimeClass == java.lang.Boolean.TYPE
          case _: Unit                => runtimeClass == java.lang.Void.TYPE
          case _ => false // super.unapply(x).isDefined
        }
        if (ok) Some(x.asInstanceOf[A]) else None
      } else if (x == null) {  // let them collect nulls, for example
        if (t == ClassTag.Null) Some(null.asInstanceOf[A]) else None
      } else super.unapply(x)
    )
  }
}
