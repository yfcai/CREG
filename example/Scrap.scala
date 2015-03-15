/** Console demo script for:
  *
  * Lämmel, Peyton Jones.
  * Scrap your boilerplate: a practical design pattern for generic programming.
  *
  * Show examples first, implementations later.
  */

package creg.example

import language.higherKinds
import creg.functors._
import creg.lib._

import reflect.runtime.universe.{TypeTag, typeTag}

object Scrap extends Scrap {
  // =========== //
  // DECLARATION //
  // =========== //

  // Re-declare lists as a datatype so as to benefit from coercion
  // and to be able to write the pattern functor
  @data def List[A] = Fix(list =>
    ListT {
      Nil
      Cons(head = A, tail = list)
    })

  // define an implicit functor for lists so that it's easier to write other datatypes
  // maybe these functors should be generated?
  @functor implicit def List[A] = Fix(list => ListT { Nil ; Cons(head = A, tail = list) })

  @data def Company  = C(depts = List apply Dept)

  @data def Dept     = Fix(dept => D(
    name = Name,
    manager = Manager,
    subunits = List apply SubunitT {
      PU(employee = Employee)
      DU(dept = dept)
    }
  ))

  @data def Subunit  = SubunitT { PU(employee = Employee) ; DU(dept = Dept) }
  @data def Employee = E(person = Person, salary = Salary)
  @data def Person   = P(name = Name, address = Address)
  @data def Salary   = S(get = Int)

  type Manager       = Employee
  type Name          = String
  type Address       = String


  // ===== //
  // USAGE //
  // ===== //

  def listF[A] = {
    @functor def fun[list] = ListT { Nil ; Cons(head = A, tail = list) }
    fun
  }

  implicit class listIsFoldable[A](xs: List[A])
      extends Foldable[({ type λ[+list] = ListF[A, list] })#λ](xs)(listF[A])

  def concat[A](xs: List[A], ys: List[A]): List[A] =
    xs.fold[List[A]] {
      case Nil  => ys
      case cons => coerce(cons)
    }

  val elemF: Traversable { type Map[+A] = List[A] } = List
  // elemF is defined because a bit confusing to write List(xs).

  def concatMap[A, B](f: A => List[B], xs: List[A]): List[B] =
    elemF(xs).mapReduce(f)(coerce(Nil), concat)

  val ralf   = E(P("Ralf",   "Amsterdam"), S(8000))
  val joost  = E(P("Joost",  "Amsterdam"), S(1000))
  val marlow = E(P("Marlow", "Cambridge"), S(2000))
  val blair  = E(P("Blair",  "London"),    S(100000))

  val genCom: Company = coerce {
    C(Cons(D("Research", ralf,
      Cons(PU(joost), Cons(PU(marlow), Nil))),
      Cons(D("Strategy", blair, Nil),
        Nil)))
  }

  val overmanaged: Company = coerce {
    C(Cons(D("management", blair,
      Cons(DU(D("mid-level management", ralf,
        Cons(DU(D("junior management", joost,
          Cons(PU(marlow), Nil))), Nil))), Nil)), Nil))
  }

  // EXAMPLE: increase salary

  def increase(percentage: Int, company: Company): Company =
    company everywhere mkT[Int](_ * (100 + percentage) / 100)

  // will not show `increase1` as example, because
  // the implementation of `Scrap.everywhere` is
  // ugly for technical reasons.
  def increase1(percentage: Int): Company => Company =
    everywhere(mkT[Int](_ * (100 + percentage) / 100))

  @functor def salaryOfEmployeeF[amount] =
    E(person = Person, salary = S(amount = amount))

  @functor def salaryF[amount] =
    C(depts = List apply {
      Fix(dept => D(
        name = Name,
        manager = salaryOfEmployeeF apply amount,
        subunits = List apply SubunitT {
          PU(employee = salaryOfEmployeeF apply amount)
          DU(dept = dept)
        }
      ))
    })

  def increase2(percentage: Int, company: Company): Company =
    salaryF(company).map(_ * (100 + percentage) / 100)

  // EXAMPLE: flatten departments

  def flatten(com: Company): Company = com everywhere mkT[Dept](flatD)

  def flatD: Dept => Dept = _.unroll match {
    case D(n, m, us) =>
      val unwrap: Subunit => List[Subunit] = _ match {
        case du @ DU(dept) => dept.unroll match {
          case D(d2, m, us) => coerce(Cons(PU(m), us))
        }

        case pu @ PU(_) => coerce(Cons(pu, Nil))
      }

      coerce {
        D(n, m, concatMap(unwrap, us))
      }
  }

  // pattern functor of departments
  @functor def deptF[dept] =
    D(name = Name,
      manager = Manager,
      subunits = List apply SubunitT {
        PU(employee = Employee)
        DU(dept = dept)
      })

  implicit class deptIsFoldable(d: Dept) extends Foldable[deptF.Map](d)(deptF)

  def flatten2(com: Company): Company = {
    // focus on departments, flatten their structures,
    // then plug them back into the company
    val zoomToDept = C compose elemF

    zoomToDept(com).map (_.fold[Dept] {
      case D(name, manager, subunits) => coerce {
        D(name = name,
          manager = manager,
          subunits = concatMap[Subunit, Subunit]({
            case PU(person) =>
              coerce { Cons(PU(person), Nil) }

            case DU(dept) =>
              coerce { Cons(PU(manager), dept.unroll.subunits) }
          }, subunits))
      }: Dept
    })
  }

  // EXAMPLE: get department names

  def deptNames(com: Company): List[Name] =
    com.everything[List[Name]](
      concat,
      mkQ[Dept, List[Name]](
        coerce(Nil),
        dept => coerce { Cons(dept.unroll.name, Nil) }
      )
    )

  @functor def deptNameF[name] =
    C(dept = List apply Fix(dept =>
      D(name = name,
        manager = Manager,
        subunits = List apply SubunitT {
          PU(employee= Employee)
          DU(dept = dept)
        })
    ))

  def deptNames2(com: Company): List[Name] = {
    deptNameF(com).mapReduce[List[Name]](name => coerce { Cons(name, Nil) })(coerce(Nil), concat)
  }

  // deptNames(genCom)
  // deptNames(overmanaged)
  // deptNames(flatten(genCom))
  // deptNames(flatten(overmanaged))
}

trait Scrap {
  this: Scrap.type =>

  // ============== //
  // IMPLEMENTATION //
  // ============== //

  // SpecialCase is not a supertype of Transform and Query
  // due to technical reasons. If we change the type of
  // SpecialCase.apply to resemble Transform.apply, then
  // we run into "Unable to convert functio with dependent
  // type to function value". If we change the type of
  // Transform.apply to resemble SpecialCase.apply, then
  // we have to call a transformation like this:
  //
  //   tr(implicitly)(x)
  //
  // because the implicit argument of the transformation
  // would come before the explicit argument.

  trait SpecialCase[W[_]] {
    def apply[A: Data]: A => W[A]
  }

  // forall a. Data a => a -> a
  trait Transform extends SpecialCase[Applicative.Identity] {
    def apply[A: Data](x: A): A
    def apply[A: Data]: A => A = x => this.apply(x)(implicitly)
  }

  // forall a. Data a => a -> R
  trait Query[R] extends SpecialCase[Applicative.Const[R]#λ] {
    queryTrait =>
    def apply[A: Data](x: A): R
    def apply[A: Data]: A => R = x => this.apply(x)(implicitly)
    def lift: Query[Seq[R]] = new Query[Seq[R]] {
      def apply[A: Data](x: A): Seq[R] = Seq(queryTrait(x))
    }
  }

  object DataToTypeTag {
    implicit def dataToTypeTag[A: Data]: TypeTag[A] =
      implicitly[Data[A]].typeTag
  }

  // CAVEAT:
  // due to limitation of runtime.universe.TypeTag,
  // `safeCast` only works for *static* datatypes,
  // namely those declared inside an object, not a trait.
  def safeCast[A: TypeTag, T: TypeTag](x: A): Option[T] = {
    val tpeA = implicitly[TypeTag[A]].tpe.dealias
    val tpeT = implicitly[TypeTag[T]].tpe.dealias
    if (tpeA <:< tpeT)
      Some(x.asInstanceOf[T])
    else
      None
  }

  def mkT[T: TypeTag](f: T => T): Transform = new Transform {
    def apply[A: Data](x: A): A = {
      import DataToTypeTag._
      safeCast[T => T, A => A](f) match {
        case Some(f) => f(x)
        case None => x
      }
    }
  }

  def mkQ[T: TypeTag, R](default: R, query: T => R): Query[R] = new Query[R] {
    def apply[A: Data](x: A): R = {
      import DataToTypeTag._
      safeCast[A, T](x) map query getOrElse default
    }
  }

  abstract class Data[T](implicit val typeTag: TypeTag[T]) {

    def gfoldl(apl: Applicative)(sp: SpecialCase[apl.Map]): T => apl.Map[T]

    type ID[+X] = Applicative.Identity[X]

    def gmapT(tr: Transform): T => T =
      gfoldl(Applicative.Identity)(tr)

    type Const[A] = { type λ[+X] = A }

    def gmapQ[R](query: Query[R]): T => Seq[R] =
      gfoldl(Applicative.Const[Seq[R]](Seq.empty, _ ++ _))(query.lift)
  }

  def everywhere[A: Data](f: Transform): A => A =
    x => {
      val dataInstance = implicitly[Data[A]]

      f(dataInstance.gmapT(
        new Transform {
          def apply[B: Data](y: B): B = everywhere[B](f)(implicitly)(y) // ugly
        })(x))
    }

  implicit class GenericOps[A](data: A)(implicit gen: Data[A]) {
    def gmapT(tr: Transform): A = gen.gmapT(tr)(data)
    def gmapQ[R](query: Query[R]): Seq[R] = gen.gmapQ(query)(data)
    def gfoldl(apl: Applicative)(sp: SpecialCase[apl.Map]): apl.Map[A] = gen.gfoldl(apl)(sp)(data)

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

  class DataWithConstantFunctor[T: TypeTag] extends Data[T] {
    @functor def fun[X] = T

    def gfoldl(apl: Applicative)(sp: SpecialCase[apl.Map]): T => apl.Map[T] =
      data => fun(data).traverse(apl)(sp[Nothing])
  }

  implicit val nothingData: Data[Nothing] = new DataWithConstantFunctor[Nothing]
  implicit val stringData: Data[String] = new DataWithConstantFunctor[String]
  implicit val intData: Data[Int] = new DataWithConstantFunctor[Int]

  implicit val salaryData: Data[Salary] = new Data[Salary] {
    @functor def fun[amount] = S(get = amount)

    def gfoldl(apl: Applicative)(sp: SpecialCase[apl.Map]): Salary => apl.Map[Salary] =
      fun.traverse(apl)(sp[Int])
  }

  implicit val personData: Data[Person] = new Data[Person] {
    @functor def fun[name, address] = P(name = name, address = address)

    def gfoldl(apl: Applicative)(sp: SpecialCase[apl.Map]): Person => apl.Map[Person] =
      person => fun(person).traverse(apl)(sp[Name], sp[Address])
  }

  implicit val dataEmployee: Data[Employee] = new Data[Employee] {
    @functor def fun[person, salary] = E(person = person, salary = salary)

    def gfoldl(apl: Applicative)(sp: SpecialCase[apl.Map]): Employee => apl.Map[Employee] =
      employee => fun(employee).traverse(apl)(sp[Person], sp[Salary])
  }

  implicit val subunitData: Data[Subunit] = new Data[Subunit] {
    @functor def fun[employee, dept] = SubunitT { PU(employee = employee) ; DU(dept = dept) }

    def gfoldl(apl: Applicative)(sp: SpecialCase[apl.Map]): Subunit => apl.Map[Subunit] =
      subunit => fun(subunit).traverse(apl)(sp[Employee], sp[Dept])
  }

  implicit def listData[A](implicit genA: Data[A]): Data[List[A]] = {
    import genA.typeTag

    new Data[List[A]] {
      @functor def fun[head, tail] = ListT { Nil ; Cons(head = head, tail = tail) }

      implicit def genList: Data[List[A]] = this

      def gfoldl(apl: Applicative)(sp: SpecialCase[apl.Map]): List[A] => apl.Map[List[A]] =
        xs =>
      apl.roll[({ type λ[+X] = fun.Map[A, X] })#λ] {
          fun(
            xs.unroll
          ).traverse(apl)(
            sp[A],
            sp[List[A]])
        }
    }
  }

  implicit val deptData: Data[Dept] = new Data[Dept] {
    @functor def fun[name, manager, subunits] =
      D(name = name, manager = manager, subunits = subunits)

    // We cannot write
    //
    //   @functor def fun2[name, manager, subunits] =
    //     Fix(dept => D(name = name, manager = manager, subunits = subunits))
    //
    // because the range of `fun2` consists of fixed points of constant functors,
    // and Scalac can't figure out that one of those constant functors have the
    // same fixed point as `DeptF`.

    def gfoldl(apl: Applicative)(sp: SpecialCase[apl.Map]): Dept => apl.Map[Dept] =
      dept => apl.roll[DeptF] {
        fun(dept.unroll).traverse(apl)(sp[Name], sp[Manager], sp[List[Subunit]])
      }
  }

  implicit val companyData: Data[Company] = new Data[Company] {
    @functor def fun[depts] = C(depts = depts)

    def gfoldl(apl: Applicative)(sp: SpecialCase[apl.Map]): Company => apl.Map[Company] =
      company => fun(company).traverse(apl)(sp[List[Dept]])
  }

}

import Scrap._
