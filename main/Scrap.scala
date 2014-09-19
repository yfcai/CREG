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

import reflect.runtime.universe.TypeTag

object Scrap {

  // =========== //
  // DECLARATION //
  // =========== //

  @datatype trait List[A]    { Nil ; Cons(head = A, tail = List[A]) }

  @datatype trait Company    { C(List[Department]) }
  @datatype trait Dept[SubU] { D(name = Name, manager = Manager, subunits = List[SubU]) }
  @datatype trait SubU[Dept] { PU(Employee) ; DU(Dept) }
  @datatype trait Employee   { E(Person, salary = Salary) }
  @datatype trait Person     { P(Name, Address) }
  @datatype trait Salary     { S(Long) }

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

  object List {
    def apply[A](xs: A*): List[A] =
      if (xs.isEmpty)
        coerce(Nil)
      else
        coerce(Cons(xs.head, apply(xs.tail: _*)))
  }

  trait SpecialCase[W[_]] {
    def apply[A: Data]: A => W[A]
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

    def gfoldl(apl: Applicative)(sp: SpecialCase[apl.Map]): T => apl.Map[T]

    type ID[+X] = Applicative.Identity[X]

    def gmapT(tr: Transform): T => T =
      gfoldl(Applicative.Identity)(new SpecialCase[ID] { def apply[A: Data] = tr[A] })

    type Const[A] = { type λ[+X] = A }

    def gmapQ[R](query: Query[R]): T => Seq[R] =
      gfoldl(Applicative.Const[Seq[R]](Seq.empty, _ ++ _))(
        new SpecialCase[Const[Seq[R]]#λ] {
          def apply[A: Data]: A => Seq[R] = x => Seq(query(x))
        })
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

  implicit object nothingData extends DataWithConstantFunctor[Nothing]

  class DataWithConstantFunctor[T: TypeTag] extends Data[T] {
    val functor = {
      @functor val constantFunctor = _ => T
      constantFunctor
    }

    def gfoldl(apl: Applicative)(sp: SpecialCase[apl.Map]): T => apl.Map[T] =
      data => functor(data).traverse(apl)(sp[Nothing])
  }

  implicit object stringData extends DataWithConstantFunctor[String]
  implicit object floatData  extends DataWithConstantFunctor[Long]

  implicit object salaryData extends Data[Salary] {
    val functor = {
      @functor val fun = amount => Salary { S(amount) }
      fun
    }

    def gfoldl(apl: Applicative)(sp: SpecialCase[apl.Map]): Salary => apl.Map[Salary] =
      salary => functor(salary).traverse(apl)(sp[Long])
  }

  implicit object personData extends Data[Person] {
    val functor = {
      @functor val fun = (name, address) => Person { P(name, address) }
      fun
    }

    def gfoldl(apl: Applicative)(sp: SpecialCase[apl.Map]): Person => apl.Map[Person] =
      person => functor(person).traverse(apl)(sp[Name], sp[Address])
  }

  implicit object dataEmployee extends Data[Employee] {
    val functor = {
      @functor val fun = (person, salary) => Employee { E(person, salary) }
      fun
    }

    def gfoldl(apl: Applicative)(sp: SpecialCase[apl.Map]): Employee => apl.Map[Employee] =
      employee => functor(employee).traverse(apl)(sp[Person], sp[Salary])
  }

  // needs: Data[Department]
  implicit def subunitData(implicit genDept: Data[Department]): Data[SubUnit] = new Data[SubUnit] {
    val functor = {
      @functor val fun = (person, department) => SubUnit { PU(person) ; DU(department) }
      fun
    }

    def gfoldl(apl: Applicative)(sp: SpecialCase[apl.Map]): SubUnit => apl.Map[SubUnit] =
      subunit => functor(subunit).traverse(apl)(sp[Employee], sp[Department])
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

      def gfoldl(apl: Applicative)(sp: SpecialCase[apl.Map]): List[A] => apl.Map[List[A]] =
        xs => apl.roll[({ type λ[+X] = functor.Map[A, X] })#λ] {
          functor(xs.unroll).traverse(apl)(sp[A], sp[List[A]])
        }
    }
  }

  implicit object departmentData extends Data[Department] {
    val functor = {
      @functor val fun = (name, manager, subunit) => Department { D(name, manager, subunit) }
      fun
    }

    def gfoldl(apl: Applicative)(sp: SpecialCase[apl.Map]): Department => apl.Map[Department] =
      dept => apl.roll[deptF.Map] {
        functor(dept.unroll).traverse(apl)(sp[Name], sp[Manager], sp[List[SubUnit]])
      }
  }

  implicit object companyData extends Data[Company] {
    val functor = {
      @functor val fun = depts => Company { C(depts) }
      fun
    }

    def gfoldl(apl: Applicative)(sp: SpecialCase[apl.Map]): Company => apl.Map[Company] =
      company => functor(company).traverse(apl)(sp[List[Department]])
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
    list(xs).mapReduce(f)(coerce(Nil), concat)
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

  def increase(percentage: Long, company: Company): Company =
    company everywhere mkT[Long](_ * (100 + percentage) / 100)

  val employeeF = {
    @functor val employeeF = employee => Company {
      C(List {
        Cons(head = Department {
          D(
            manager = employee,
            subunits = List { Cons(head = SubUnit {
              DU(Department)
              PU(employee)
            }) }
          )
        })
      })
    }
    employeeF
  }

  val salaryF = {
    // salaryF is written as a composite with employeeF instead of a stand-alone functor
    // because a bug makes the latter impossible (05.09.2014).
    @functor val salaryOfEmployee = amount => Employee { E(salary = Salary { S(amount) }) }
    employeeF compose salaryOfEmployee
  }

  def increase2(percentage: Long, company: Company): Company =
    salaryF(company).map[Long](_ * (100 + percentage) / 100)

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

  def flatten2(com: Company): Company = {
    @functor val dcom = dept => Company { C(List { Cons(head = dept) }) }

    @functor val each = subunit => List[subunit]

    implicit class deptIsFoldable(d: Department) extends Foldable[deptF.Map](d)(deptF)

    dcom(com).map(_.fold[Department] {
      case D(name, manager, subunits) => coerce {
        D(name     = name,
          manager  = manager,
          subunits = concatMap[SubUnit, SubUnit]({
            case PU(person) => List(PU(person))
            case DU(dept) => dept.unroll match {
              case D(_, manager, subunits) => concat(List(PU(manager)), subunits)
            }
          }, subunits))
      }
    })
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

  def deptNames2(com: Company): List[Name] = {
    @functor val deptNameF = name => Company { C(List { Cons(head = Department { D(name = name) }) }) }
    deptNameF(com).mapReduce(name => List(name))(coerce(Nil), concat)
  }

  // deptNames(genCom)
  // deptNames(overmanaged)
  // deptNames(flatten(genCom))
  // deptNames(flatten(overmanaged))
}

import Scrap._
