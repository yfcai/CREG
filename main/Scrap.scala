/** Console demo script for:
  *
  * Lämmel, Jones.
  * Scrap your boilerplate: a practical design pattern for generic programming.
  *
  * Show examples first, implementations later.
  */

import language.higherKinds
import nominal.functors._
import nominal.lib._
import nominal.lib.Traversable.{Endofunctor => Functor, _}

import reflect.runtime.universe.TypeTag

object Scrap {

  // =========== //
  // DECLARATION //
  // =========== //

  @datatype trait List[A]    { Nil ; Cons(head = A, tail = List[A]) }

  @datatype trait Company    { C(List[Department]) }
  @datatype trait Dept[SubU] { D(name = Name, manager = Manager, subunits = List[SubU]) }
  @datatype trait SubU[Dept] { PU(Employee) ; DU(Dept) }
  @datatype trait Employee   { E(Person, Salary) }
  @datatype trait Person     { P(Name, Address) }
  @datatype trait Salary     { S(Double) }

  type Department = Fix[deptF.Map]
  type SubUnit    = SubU[Department]
  type Manager    = Employee
  type Name       = String
  type Address    = String

  val deptF = {
    @functor val deptF = department => Dept {
      // BUG: does not work if we write D(Name, Manager, List { ... }) instead.
      D(subunits = List { Cons(head = SubU { DU(department) }) })
    }
    deptF
  }

  // ============== //
  // IMPLEMENTATION //
  // ============== //

  trait SpecialCase[W[_]] {
    def apply[A: Data](x: A): W[A]
  }

  // forall a. Data a => a -> a
  trait Transform {
    def apply[A: Data](x: A): A
  }

  // forall a. Data a => a -> R
  trait Query[R] {
    def apply[A: Data](x: A): R
  }

  // CAVEAT:
  // due to limitation of runtime.universe.TypeTag,
  // `safeCast` only works when used in the same class
  // where type `T` is declared.
  def safeCast[A: Data, T: TypeTag](x: A): Option[T] = {
    val tpeA = implicitly[Data[A]].typeTag.tpe.dealias
    val tpeT = implicitly[TypeTag[T]].tpe.dealias
    if (tpeA <:< tpeT)
      Some(x.asInstanceOf[T])
    else
      None
  }

  def mkT[T: TypeTag](f: T => T): Transform = new Transform {
    def apply[A: Data](x: A): A =
      safeCast[A, T](x) match {
        case Some(x) => f(x).asInstanceOf[A]
        case None => x
      }
  }

  def mkQ[T: TypeTag, R](default: R, query: T => R): Query[R] = new Query[R] {
    def apply[A: Data](x: A): R =
      safeCast[A, T](x) map query getOrElse default
  }

  abstract class Data[T: TypeTag] {
    val typeTag: TypeTag[T] = implicitly

    def gfoldl[W[+_]](apl: Applicative.Endofunctor[W])(sp: SpecialCase[W]): T => W[T]

    type ID[+X] = Applicative.Identity[X]

    def gmapT(tr: Transform): T => T =
      gfoldl[ID](Applicative.Identity)(new SpecialCase[ID] { def apply[A: Data](x: A): A = tr(x) })

    type Const[A] = { type λ[+X] = A }

    def gmapQ[R](query: Query[R]): T => Seq[R] =
      gfoldl[Const[Seq[R]]#λ](Applicative.Const(Seq.empty, _ ++ _))(
        new SpecialCase[Const[Seq[R]]#λ] {
          def apply[A: Data](x: A): Seq[R] = Seq(query(x))
        })
  }

  implicit class GenericOps[A](data: A)(implicit gen: Data[A]) {
    def gmapT(tr: Transform): A = gen.gmapT(tr)(data)
    def gmapQ[R](query: Query[R]): Seq[R] = gen.gmapQ(query)(data)
    def gfoldl[W[+_]](apl: Applicative.Endofunctor[W])(sp: SpecialCase[W]): W[A] = gen.gfoldl(apl)(sp)(data)

    def everywhere(f: Transform): A =
      f(gmapT(new Transform {
        def apply[B: Data](x: B): B = x everywhere f
      }))

    def everything[R](combine: (R, R) => R, query: Query[R]): R = {
      query(data) +: gmapQ(
        new Query[R] {
          def apply[A: Data](x: A): R = x.everything(combine, query)
        }
      ) reduce combine
    }
  }

  implicit object nothingData extends DataWithConstantFunctor[Nothing]

  class DataWithConstantFunctor[T: TypeTag] extends Data[T] {
    val functor = {
      @functor val constantFunctor = _ => T
      constantFunctor
    }

    def gfoldl[W[+_]](apl: Applicative.Endofunctor[W])(sp: SpecialCase[W]): T => W[T] =
      data => functor(data).traverse(sp[Nothing])(apl)
  }

  implicit object stringData extends DataWithConstantFunctor[String]
  implicit object floatData  extends DataWithConstantFunctor[Double]

  implicit object salaryData extends Data[Salary] {
    val functor = {
      @functor val fun = amount => Salary { S(amount) }
      fun
    }

    def gfoldl[W[+_]](apl: Applicative.Endofunctor[W])(sp: SpecialCase[W]): Salary => W[Salary] =
      salary => functor(salary).traverse(sp[Double])(apl)
  }

  implicit object personData extends Data[Person] {
    val functor = {
      @functor val fun = (name, address) => Person { P(name, address) }
      fun
    }

    def gfoldl[W[+_]](apl: Applicative.Endofunctor[W])(sp: SpecialCase[W]): Person => W[Person] =
      person => functor(person).traverse(sp[Name], sp[Address])(apl)
  }

  implicit object dataEmployee extends Data[Employee] {
    val functor = {
      @functor val fun = (person, salary) => Employee { E(person, salary) }
      fun
    }

    def gfoldl[W[+_]](apl: Applicative.Endofunctor[W])(sp: SpecialCase[W]): Employee => W[Employee] =
      employee => functor(employee).traverse(sp[Person], sp[Salary])(apl)
  }

  // needs: Data[Department]
  implicit def subunitData(implicit genDept: Data[Department]): Data[SubUnit] = new Data[SubUnit] {
    val functor = {
      @functor val fun = (person, department) => SubUnit { PU(person) ; DU(department) }
      fun
    }

    def gfoldl[W[+_]](apl: Applicative.Endofunctor[W])(sp: SpecialCase[W]): SubUnit => W[SubUnit] =
      subunit => functor(subunit).traverse(sp[Employee], sp[Department])(apl)
  }

  implicit def listData[A](implicit genA: Data[A]): Data[List[A]] = {
    implicit val tagA = genA.typeTag
    implicit val tagL = implicitly[TypeTag[List[A]]]

    new Data[List[A]] {
      val functor = {
        @functor val fun = (x, xs) => List[A] { Cons(x, xs) }
        fun
      }

      implicit val genList: Data[List[A]] = this

      def gfoldl[W[+_]](apl: Applicative.Endofunctor[W])(sp: SpecialCase[W]): List[A] => W[List[A]] =
        xs => apl.roll[({ type λ[+X] = functor.Map[A, X] })#λ] {
          functor(xs.unroll).traverse(sp[A], sp[List[A]])(apl)
        }
    }
  }

  implicit object departmentData extends Data[Department] {
    val functor = {
      @functor val fun = (name, manager, subunit) => Department { D(name, manager, subunit) }
      fun
    }

    def gfoldl[W[+_]](apl: Applicative.Endofunctor[W])(sp: SpecialCase[W]): Department => W[Department] =
      dept => apl.roll[deptF.Map] {
        functor(dept.unroll).traverse(sp[Name], sp[Manager], sp[List[SubUnit]])(apl)
      }
  }

  implicit object companyData extends Data[Company] {
    val functor = {
      @functor val fun = depts => Company { C(depts) }
      fun
    }

    def gfoldl[W[+_]](apl: Applicative.Endofunctor[W])(sp: SpecialCase[W]): Company => W[Company] =
      company => functor(company).traverse(sp[List[Department]])(apl)
  }

  // ===== //
  // USAGE //
  // ===== //

  def concat[A](xs: List[A], ys: List[A]): List[A] = {
    @functor val listF = rec => ListF[A, rec]
    new Foldable[listF.Map](xs)(listF).fold[List[A]] {
      case Nil  => ys
      case cons => coerce(cons)
    }
  }

  def concatMap[A, B](f: A => List[B], xs: List[A]): List[B] = {
    @functor val list = x => List[x]
    list(list(xs) map f) reduce (coerce(Nil), concat)
  }

  val ralf   = E(P("Ralf",   "Amsterdam"), S(8000))
  val joost  = E(P("Joost",  "Amsterdam"), S(1000))
  val marlow = E(P("Marlow", "Cambridge"), S(2000))
  val blair  = E(P("Blair",  "London"),    S(100000))

  val genCom: Company = coerce(
    C(
      Cons(D("Research", ralf,
        Cons(PU(joost), Cons(PU(marlow), Nil))),
      Cons(D("Strategy", blair, Nil),
    Nil)))
  )

  val overmanaged: Company = coerce(
    C(
      Cons(D("management", blair,
        Cons(DU(D("mid-level management", ralf,
          Cons(DU(D("junior management", joost,
            Cons(PU(marlow), Nil))), Nil))), Nil)), Nil))
  )

  // EXAMPLE: increase salary

  def increase(rate: Double, company: Company): Company =
    company everywhere mkT[Double](_ * (1.0f + rate))

  // increase(0.1, genCom)

  // EXAMPLE: flatten departments

  def flatten(com: Company): Company = com everywhere mkT[Department](flatD)

  def flatD: Department => Department = _.unroll match {
    case D(n, m, us) =>
      val unwrap: SubUnit => List[SubUnit] = _ match {
        case du @ DU(dept) => dept.unroll match {
          case D(d2, m, us) => coerce(Cons(PU(m), us))
        }

        case pu @ PU(_) => coerce(Cons(pu, Nil))
      }

      coerce(D(n, m, concatMap(unwrap, us)))
  }

  // EXAMPLE: get department names

  def deptNames(com: Company): List[Name] =
    com.everything[List[Name]](
      concat,
      mkQ[Department, List[Name]](
        coerce(Nil),
        _.unroll match {
          case D(name, _, _) => coerce(Cons(name, Nil))
        })
    )

  // deptNames(genCom)
  // deptNames(overmanaged)
  // deptNames(flatten(genCom))
  // deptNames(flatten(overmanaged))
}

import Scrap._
