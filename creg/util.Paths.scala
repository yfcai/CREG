package creg
package util

import scala.reflect.macros.blackbox.Context
import compiler.DatatypeRepresentation.Many

private[creg]
trait Paths {
  def getIdentity(c: Context): c.Tree = {
    import c.universe._
    q"_root_.scala.Predef.identity"
  }

  // location of the Fix[_[_]] trait
  def getFix(c: Context) = {
    import c.universe._
    tq"_root_.creg.lib.fix.Fix"
  }

  def getFixWithoutRoot: String = "creg.lib.fix.Fix"

  def getRoll(c: Context) = c parse "_root_.creg.Roll"

  def getRecordOrVariant(c: Context): c.Tree = {
    import c.universe._
    tq"_root_.creg.lib.fix.Fix.RecordOrVariant"
  }

  def getVariant(c: Context) = {
    import c.universe._
    tq"_root_.creg.lib.fix.Fix.Variant"
  }

  def getRecord(c: Context) = {
    import c.universe._
    tq"_root_.creg.lib.fix.Fix.Record"
  }

  def getTraversableEndofunctor(c: Context, n: Int): c.Tree =
    getSomeTraversableBoundedTrait(c, n, traversableEndofunctorTrait)

  def getTraversableEndofunctorOf(c: Context, n: Int): c.Tree =
    getSomeTraversableBoundedTrait(c, n, traversableEndofunctorOf)

  def getTraversableBounded(c: Context, n: Int): c.Tree =
    getSomeTraversableBoundedTrait(c, n, boundedTraversableBoundedTrait)

  private[this]
  def getSomeTraversableBoundedTrait(c: Context, n: Int, traitName: String): c.Tree = {
    import c.universe._
    val q"??? : $traversableN" =
      c parse "??? : " + traitName + (if (n == 1) "" else n.toString)
    traversableN
  }

  def getApplicative(c: Context): c.Tree = {
    import c.universe._
    tq"_root_.creg.Applicative"
  }

  def traversableEndofunctorTrait: String = "_root_.creg.lib.traversable.Traversable"
  def traversableEndofunctorOf: String = "_root_.creg.lib.traversable.TraversableBounded.EndofunctorOf"
  def boundedTraversableBoundedTrait: String = "_root_.creg.lib.traversable.TraversableBounded"

  def mappingOnObjects: String = "Map"

  def getPure(c: Context)(applicative: c.TermName): c.Tree = {
    import c.universe._
    q"$applicative.pure"
  }

  def getFunctorMapOnObjects(c: Context)(applicative: c.TermName): c.Tree = {
    import c.universe._
    tq"$applicative.Map"
  }

  def getTreeMapOnObjects(c: Context)(applicative: c.Tree): c.Tree = {
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

  def getFunctorCat(c: Context, i: Int)(functor: c.TermName): c.Tree = {
    import c.universe._
    tq"$functor.${typeNameCat(c, i)}"
  }

  def getTreeCat(c: Context, i: Int)(functor: c.Tree): c.Tree = {
    import c.universe._
    tq"$functor.${typeNameCat(c, i)}"
  }

  def getThisCat(c: Context, i: Int): c.Tree = {
    import c.universe._
    tq"this.${typeNameCat(c, i)}"
  }

  def typeNameCat(c: Context, i: Int): c.TypeName = {
    import c.universe._
    TypeName("Cat" + i)
  }

  def typeNameRange(c: Context): c.TypeName = c.universe.TypeName("Range")

  def identityFunctorLocationString: String = "_root_.creg.Applicative.Identity"

  def applicativeEndofunctor(c: Context)(f: c.TypeName): c.Tree = {
    import c.universe._
    val q"??? : $tpe" = q"??? : _root_.creg.Applicative.Endofunctor[$f]"
    tpe
  }

  def getAnyType(c: Context): c.Tree = {
    import c.universe._
    tq"_root_.scala.Any"
  }

  def getNothingType(c: Context): c.Tree = {
    import c.universe._
    tq"_root_.scala.Nothing"
  }

  def nothingType: String = "_root_.scala.Nothing"
  def anyType: String = "_root_.scala.Any"

  def scalaLanguageFeatureImports(c: Context): Many[c.Tree] = {
    import c.universe._
    Many(
      q"import _root_.scala.language.higherKinds",
      q"import _root_.scala.language.implicitConversions")
  }

  def getImplicitly(c: Context)(typeTree: c.Tree): c.Tree = {
    import c.universe._
    q"_root_.scala.Predef.implicitly[$typeTree]"
  }
}
