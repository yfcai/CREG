import scala.reflect.macros.blackbox.Context

import DatatypeRepresentation._

trait UniverseConstruction {

  def meaning(c: Context)(rep: Datatype): c.Type = ???

  def representation(c: Context)(tpe: c.Type): Datatype = {
    Scala("Int") // stub
  }
}

object UniverseConstruction {
  object Tests {
    // stub
  }
}
