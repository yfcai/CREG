import org.scalatest._
import nominal.functors._
import nominal.lib._

import scala.language.experimental.macros

class CoercionSpec extends FlatSpec with Coercion {
  @datatype trait List[A] {
    Nil
    Cons(head = A, tail = List[A])
  }

  def listF[A] = {
    @functor val listF = L => List { Cons(A, L) }
    listF
  }

  type ILF[+X] = ListF[Int, X]
  type ILT = ListT[Nil, Cons[Int, List[Int]]]

  // representation of type
  def rep[T](implicit tag: reflect.runtime.universe.TypeTag[T]): String = tag.tpe.toString

  // instantiate dummy object to test typer
  def absurd[T]: T = null.asInstanceOf[T]

  "Coercion" should "know the source and destination types" in {
    val info = collection.mutable.Map.empty[String, String]
    val x0: List[Int] = coerceContextInfo(Nil, info)
    assert(info == Map("expected" -> rep[List[Int]], "actual" -> rep[Nil.type]))

    info.clear
    val x1: Boolean = coerceContextInfo(5, info)
    assert(info == Map("expected" -> rep[Boolean], "actual" -> rep[Int]))
  }

  val nilOfInt: List[Int] = coerce(Nil)
  val consOfInt: List[Int] = coerce( Cons(5, nilOfInt) )

  it should "auto-roll at top level" in {
    assert(nilOfInt == Roll[ILF](Nil))
    assert(consOfInt == Roll[ILF](Cons(5, nilOfInt)))
  }

  it should "auto-unroll at top level" in {
    val nil: ILT = coerce(nilOfInt)
    assert(nil == Nil)

    val cons: ILT = coerce(consOfInt)
    assert(cons == Cons(5, nilOfInt))
  }

  // curried ListF
  private[this] type ListC[+X] = { type λ[+Y] = ListF[X, Y] }

  private[this] type ListF2[+X] = ListF[X, X]

  // μX. ListF[X, X]
  private[this] type MuX = Fix[ListF2]

  // μY. ListF[μX. ListF[X, X], Y]
  private[this] type MuY = Fix[ListC[MuX]#λ]

  it should "tell whether types are compatible at runtime" in {
    // MuX and MuY are compatible at runtime.
    // but this does not compile:
    //   val x0: MuX = absurd[MuY]

    // these do:
    val x1: MuX = coerce(absurd[MuY])
    val x2: MuY = coerce(absurd[MuX])

    // unfortunately, can't verify failure because
    // the `coerce` macro can't be used inside
    // nominal.util.EvalScala.evalScala.
    //
    // these fail with bad error messages.
    // error messages are bad because scalac discards
    // the first error message, discards the expected
    // return type it infers, and calls `coerce` again
    // with expected type = Nothing.
    //
    //   val x3: List[Int] = coerce(absurd[MuY])
    //   val x4: MuY = coerce(absurd[ILT])
  }

  it should "roll variants into fixed points" in {
    val ints: ILT = coerce(Cons(3, Nil))

    // compilation success means auto-roll at top level
    val intList: List[Int] = coerce(ints)

    // compilation success means auto-roll at nested level
    val list2: List[List[Int]] = coerce(Cons(ints, Cons(ints, Cons(ints, Nil))))
    val list3: List[List[List[Int]]] = coerce(Cons(Cons(ints, Nil), Nil))

    val list4: ListF[List[Int], List[List[Int]]] = coerce(Cons(Cons(3, Nil), Nil))

    val list5: ListF[Cons[Int, Nil], Nil] = Cons(Cons(3, Nil), Nil)
    val list6: ListF[List[Int], List[List[Int]]] = coerce(list5)

    def ana[A, T](seed: T)(coalgebra: T => ListF[A, T]): List[A] =
      coerce( listF[A](coalgebra(seed)) map (x => ana(x)(coalgebra)) )
  }

  it should "unroll fixed points as appropriate" in {
    val intList: List[Int] = coerce(Cons(3, Nil))
    val ints: ILT = coerce(intList)
  }
}
