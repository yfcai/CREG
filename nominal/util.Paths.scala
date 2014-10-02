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

  def getTraversableEndofunctor(c: Context, n: Int): c.Tree =
    getSomeTraversableTrait(c, n, traversableEndofunctorTrait)

  def getBoundedTraversable(c: Context, n: Int): c.Tree =
    getSomeTraversableTrait(c, n, boundedTraversableTrait)

  private[this]
  def getSomeTraversableTrait(c: Context, n: Int, traitName: String): c.Tree = {
    import c.universe._
    val q"??? : $traversableN" =
      c parse "??? : " + traitName + (if (n == 1) "" else n.toString)
    traversableN
  }

  def getApplicative(c: Context): c.Tree = {
    import c.universe._
    tq"_root_.nominal.lib.Applicative"
  }

  def traversableEndofunctorTrait: String = "_root_.nominal.lib.Traversable.EndofunctorTrait"
  def boundedTraversableTrait: String = "_root_.nominal.lib.Traversable"

  def mappingOnObjects: String = "Map"

  def getPure(c: Context)(applicative: c.TermName): c.Tree = {
    import c.universe._
    q"$applicative.pure"
  }

  def getFunctorMapOnObjects(c: Context)(applicative: c.TermName): c.Tree = {
    import c.universe._
    tq"$applicative.Map"
  }

  def getThisMapOnObjects(c: Context): c.Tree = {
    import c.universe._
    tq"this.Map"
  }

  def getMapOnObjects(c: Context): c.Tree = {
    import c.universe._
    tq"Map"
  }

  def getFunctorCat(c: Context, i: Int, n: Int)(functor: c.TermName): c.Tree = {
    import c.universe._
    tq"$functor.${typeNameCat(c, i, n)}"
  }

  def getThisCat(c: Context, i: Int, n: Int): c.Tree = {
    import c.universe._
    tq"this.${typeNameCat(c, i, n)}"
  }

  def typeNameCat(c: Context, i: Int, n: Int): c.TypeName = {
    import c.universe._
    TypeName("Cat" + (if (n == 1) "" else (i + 1).toString))
  }

  def identityFunctorLocationString: String = "_root_.nominal.lib.Applicative.Identity"

  def applicativeEndofunctor(c: Context)(f: c.TypeName): c.Tree = {
    import c.universe._
    val q"??? : $tpe" = q"??? : _root_.nominal.lib.Applicative.Endofunctor[$f]"
    tpe
  }

  def getAnyType(c: Context): c.Tree = {
    import c.universe._
    tq"_root_.scala.Any"
  }

  def nothingType: String = "_root_.scala.Nothing"
  def anyType: String = "_root_.scala.Any"

}
