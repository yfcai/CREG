package nominal
package util

import scala.reflect.macros.blackbox.Context

trait Paths {
  // location of the Fix[_[_]] trait
  def getFix(c: Context) = {
    import c.universe._
    tq"_root_.nominal.lib.Fix"
  }

  def getRoll(c: Context) = c parse "_root_.nominal.lib.Roll"

  def getVariant(c: Context) = {
    import c.universe._
    tq"_root_.nominal.lib.Fix.Variant"
  }

  def getRecord(c: Context) = {
    import c.universe._
    tq"_root_.nominal.lib.Fix.Record"
  }

  def getTraversableEndofunctor(c: Context, n: Int): c.Tree = {
    import c.universe._
    val q"new $traversableN" =
      c parse "new " + traversableEndofunctorTrait + (if (n == 1) "" else n.toString)
    traversableN
  }

  def getApplicative(c: Context): c.Tree = {
    import c.universe._
    tq"_root_.nominal.lib.Applicative"
  }

  def traversableEndofunctorTrait: String = "_root_.nominal.lib.Traversable.EndofunctorTrait"

  def mappingOnObjects: String = "Map"

  def getFunctorMapOnObjects(c: Context)(applicative: c.TermName): c.Tree = {
    import c.universe._
    tq"$applicative.Map"
  }

  def getThisMapOnObjects(c: Context): c.Tree = {
    import c.universe._
    tq"this.Map"
  }

  def identityFunctorLocationString: String = "_root_.nominal.lib.Applicative.Identity"

  def applicativeEndofunctor(c: Context)(f: c.TypeName): c.Tree = {
    import c.universe._
    val q"??? : $tpe" = q"??? : _root_.nominal.lib.Applicative.Endofunctor[$f]"
    tpe
  }
}
