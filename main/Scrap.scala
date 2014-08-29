/** Console demo script for:
  *
  * Lämmel, Jones.
  * Scrap your boilerplate: a practical design pattern for generic programming.
  */

import language.higherKinds
import nominal.functors._
import nominal.lib._
import nominal.lib.Traversable.{Endofunctor => Functor, _}
import nominal.util.ClassTagForPrimitives._

import reflect.{ClassTag, classTag}

object Scrap {
  @datatype trait List[A]    { Nil ; Cons(head = A, tail = List) }

  @datatype trait Company    { C(List[Department]) }
  @datatype trait Dept[SubU] { D(Name, Manager, subunits = List[SubU]) }
  @datatype trait SubU[Dept] { PU(Employee) ; DU(Dept) }
  @datatype trait Employee   { E(Person, Salary) }
  @datatype trait Person     { P(Name, Address) }
  @datatype trait Salary     { S(Float) }

  type Department = Fix[deptF.Map]
  type SubUnit    = SubU[Department]
  type Manager    = Employee
  type Name       = String
  type Address    = String

  val deptF = {
    @functor val deptF = Department => Dept {
      // BUG: does not work if we write D(Name, Manager, List { ... }) instead.
      D(subunits = List { Cons(head = SubU { DU(Department) }) })
    }
    deptF
  }

  val ralf   = E(P("Ralf",   "Amsterdam"), S(8000))
  val joost  = E(P("Joost",  "Amsterdam"), S(1000))
  val marlow = E(P("Marlow", "Cambridge"), S(2000))
  val blair  = E(P("Blair",  "London"),    S(100000))

  val genCom: Company = coerce(
    C(Cons(
      D("Research", ralf, Cons(PU(joost), Cons(PU(marlow), Nil))), Cons(
        D("Strategy", blair, Nil),
        Nil)))
  )

  trait SpecialCase[W[_]] {
    def apply[A](x: A): W[A]
  }

  trait Transform {
    def apply[A](x: A): A
  }

  trait Query[R] {
    def apply[A](x: A): Option[R]
  }

  def safeCast[T: ClassTag](x: Any): Option[T] = classTag[T].safeCast(x)

  def mkT[T: ClassTag](f: T => T): Transform = new Transform {
    def apply[A](x: A): A =
      safeCast[T](x) match {
        case Some(x) => f(x).asInstanceOf[A]
        case None => x
      }
  }

  def mkQ[T: ClassTag, R](default: R, query: T => R): Query[R] = new Query[R] {
    def apply[A](x: A): Option[R] =
      safeCast[T](x) map query
  }

  trait Data[T] {
    // precondition: T =:= Map[X] forSome X
    // is it possible to express that as a Scala type?
    val functor: Traversable { type Map[+X] }

    def gfoldl[W[+_]](apl: Applicative.Endofunctor[W])(sp: SpecialCase[W]): T => W[T] =
      data => {
        functor(
          data.asInstanceOf[functor.Map[functor.Cat]]
        ).traverse(sp.apply)(apl)
      }.asInstanceOf[W[T]]

    type ID[+X] = Applicative.Identity[X]

    def gmapT(tr: Transform): T => T =
      gfoldl[ID](Applicative.Identity)(new SpecialCase[ID] { def apply[A](x: A): A = tr(x) })

    type Const[A] = { type λ[+X] = A }

    def gmapQ[R](query: Query[R]): T => Seq[R] =
      gfoldl[Const[Seq[R]]#λ](Applicative.Const(Seq.empty, _ ++ _))(
        new SpecialCase[Const[Seq[R]]#λ] {
          def apply[A](x: A): Seq[R] = query(x).toSeq
        })
  }

  implicit class GenericOps[T](data: T)(implicit gen: Data[T]) {
    def gmapT(tr: Transform): T = gen.gmapT(tr)(data)
    def gmapQ[R](query: Query[R]): Seq[R] = gen.gmapQ(query)(data)
    def gfoldl[W[+_]](apl: Applicative.Endofunctor[W])(sp: SpecialCase[W]): W[T] = gen.gfoldl(apl)(sp)(data)

    // this version of `everywhere` is wrong and usually does nothing.
    // TODO FIXME introduce type class constraints into transformations and queries
    // so that this can be fixed.
    def everywhere(tr: Transform)(implicit tag: ClassTag[T]): T = tr(data gmapT mkT[T](_ everywhere tr))
  }

  trait DataWithConstantFunctor[T] extends Data[T] {
    val functor = {
      @functor val constantFunctor = F => T
      constantFunctor
    }
  }

  implicit object dataString extends DataWithConstantFunctor[String]
  implicit object dataFloat  extends DataWithConstantFunctor[Float]

  implicit object dataSalary extends Data[Salary] {
    val functor = {
      @functor val fun = X => Salary { S(X) }
      fun
    }
  }

  implicit object dataPerson extends Data[Person] {
    val functor = {
      @functor val fun = X => Person { P(X, X) }
      fun
    }
  }

  implicit object dataEmployee extends Data[Employee] {
    val functor = {
      @functor val fun = X => Employee { E(X, X) }
      fun
    }
  }

  implicit object dataSubunit extends Data[SubUnit] {
    val functor = {
      @functor val fun = X => SubUnit { PU(X) ; DU(X) }
      fun
    }
  }

  // this one could be useful somewhere else...
  def rollDataInstance[F[+_]](gen: Data[F[Fix[F]]]): Data[Fix[F]] = new Data[Fix[F]] {
    val rollFunctor = new Traversable {
      type Cat = F[Fix[F]]  // basically, the input can only be F[Fix[F]]
      type Map[+X] = Fix[F] // not entirely satisfactory...

      def traverse[H[+_]: Applicative.Endofunctor, A <: Cat, B <: Cat](f: A => H[B], mA: Map[A]): H[Map[B]] = {
        val apl = implicitly[Applicative.Endofunctor[H]] ; import apl._
        call(
          pure[F[Fix[F]] => Fix[F]](x => Roll[F](x)),
          f(mA.unroll.asInstanceOf[A]).asInstanceOf[H[F[Fix[F]]]])
      }
    }

    val functor = Traversable.compose(
      rollFunctor.asInstanceOf[Functor[ID]],
      gen.functor.asInstanceOf[Functor[ID]]) // fool the type system
  }

  implicit def dataList[A]: Data[List[A]] =
    rollDataInstance[({ type λ[+X] = ListF[A, X] })#λ](
      new Data[ListF[A, List[A]]] {
        val functor = {
          @functor val fun = X => List { Cons(X, X) }
          fun
        }
      }
    )

  //implicit val dataDepartment: Data[Department] =
    //???


  //implicit object dataDepartment: Data[Department] {
  //}

}

import Scrap._
