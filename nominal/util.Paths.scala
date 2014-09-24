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
}
