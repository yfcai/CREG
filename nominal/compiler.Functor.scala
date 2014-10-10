/**
 * decl := params => body
 *
 * params := typevar
 *         | (typevar, typevar, ..., typevar)
 *
 * body := typevar
 *       | Fix(typevar => body)
 *       | scala-functor(body, body, ..., body)
 *       | scala-constant
 */

package nominal
package compiler

object Functor {
  type Code = String
  type Name = DatatypeRepresentation.Name
  type Many[T] = DatatypeRepresentation.Many[T]
  val Many = DatatypeRepresentation.Many

  case class Decl(name: Name, params: Many[Name], body: Body)

  sealed trait Body
  case class TypeVar(name: Name) extends Body
  case class FixedPoint(param: Name, body: Body) extends Body
  case class Application(functor: Code, args: Many[Body]) extends Body
}
