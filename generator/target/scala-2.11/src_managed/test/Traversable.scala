package creg
package lib
package traversable

import language.higherKinds

trait Index {
  type Traversable = traversable.Traversable
  type Traversable2 = traversable.Traversable2
  type Traversable3 = traversable.Traversable3
  type Traversable4 = traversable.Traversable4
  type Traversable5 = traversable.Traversable5
  type Traversable6 = traversable.Traversable6
  type Traversable7 = traversable.Traversable7
  type Traversable8 = traversable.Traversable8
  type Traversable9 = traversable.Traversable9
  type Traversable10 = traversable.Traversable10
  type Traversable11 = traversable.Traversable11
  type Traversable12 = traversable.Traversable12
  type Traversable13 = traversable.Traversable13
  type Traversable14 = traversable.Traversable14
  type Traversable15 = traversable.Traversable15
  type Traversable16 = traversable.Traversable16
  type Traversable17 = traversable.Traversable17
  type Traversable18 = traversable.Traversable18
  type Traversable19 = traversable.Traversable19
  type Traversable20 = traversable.Traversable20
  type Traversable21 = traversable.Traversable21
  type Traversable22 = traversable.Traversable22
}

trait Traversable0 {
  type Map >: this.type
  type Range = Map
  def traverse(G: applicative.Applicative)(): Map => G.Map[Map] = G pure _
}

trait Traversable extends functor.Functor with TraversableBounded {  thisFunctor =>
  type Cat0 = Any
  type Map[+A]

  def compose(that: Traversable) =
    new Traversable {
      type Map[+A] = thisFunctor.Map[that.Map[A]]
      def traverse[A, B](G: applicative.Applicative)(f: A => G.Map[B]):
          this.Map[A] => G.Map[this.Map[B]] =
        thisFunctor.traverse[that.Map[A], that.Map[B]](G)(that.traverse(G)(f))
    }
}

trait TraversableBounded {
  type Cat0
  type Map[+A <: Cat0]
  type Range = Map[Cat0]
  def traverse[A <: Cat0,B <: Cat0](_G : applicative.Applicative)(a : A => _G.Map[B]): Map[A] => _G.Map[Map[B]]
  def fmap[A <: Cat0,B <: Cat0](a : A => B): Map[A] => Map[B] = traverse[A,B](applicative.Applicative.Identity)(a)
  def apply[A <: Cat0](_m : Map[A]): View[A] = new View(_m)
  def mapReduce[A <: Cat0, B <: Cat0](f: A => B)(
    default: B, combine: (B, B) => B):
      Map[A] => B =
    traverse[A, B](applicative.Applicative.Const(default, combine))(f)

  def crush[A <: Cat0](z: A, op: (A, A) => A): Map[A] => A = mapReduce(identity[A])(z, op)

  def toList[A <: Cat0]: Map[A] => List[A] =
    traverse(applicative.Applicative.FreeMonoid[A])((x: A) => List(x))

  def fromList[A <: Cat0](children: List[A]): Map[A] => Map[A] =
    t => {
      import Monad.State._
      evalState(
        traverse(stateMonad[List[A]])({
          (oldChild: A) => for {
            children <- readState
            _        <- writeState(children.tail)
          }
          yield children.head
        })(t),
        children
      )
    }

  class View[A <: Cat0](_m : Map[A]) {
    def traverse[B <: Cat0](_G : applicative.Applicative)(a : A => _G.Map[B]):
        _G.Map[Map[B]] =
      TraversableBounded.this.traverse(_G)(a)(_m)
    def map[B <: Cat0](a : A => B): Map[B] =
      TraversableBounded.this.fmap(a)(_m)
      // McBride & Paterson's reduce
    def reduce(monoidId: A, monoidOp: (A, A) => A): A =
      mapReduce(identity)(monoidId, monoidOp)

    def mapReduce[B <: Cat0](f: A => B)(monoidId: B, monoidOp: (B, B) => B): B =
      traverse(applicative.Applicative.Const(monoidId, monoidOp))(f)}
}

trait Traversable2 extends functor.Functor2 with TraversableBounded2 {
  type Cat0 = Any;type Cat1 = Any
  type Map[+A,+B]
}

trait TraversableBounded2 {
  type Cat0;type Cat1
  type Map[+A <: Cat0,+B <: Cat1]
  type Range = Map[Cat0,Cat1]
  def traverse[A <: Cat0,C <: Cat1,B <: Cat0,D <: Cat1](_G : applicative.Applicative)(a : A => _G.Map[B],b : C => _G.Map[D]): Map[A,C] => _G.Map[Map[B,D]]
  def fmap[A <: Cat0,C <: Cat1,B <: Cat0,D <: Cat1](a : A => B,b : C => D): Map[A,C] => Map[B,D] = traverse[A,C,B,D](applicative.Applicative.Identity)(a,b)
  def apply[A <: Cat0,C <: Cat1](_m : Map[A,C]): View[A,C] = new View(_m)
  
  class View[A <: Cat0,C <: Cat1](_m : Map[A,C]) {
    def traverse[B <: Cat0,D <: Cat1](_G : applicative.Applicative)(a : A => _G.Map[B],b : C => _G.Map[D]):
        _G.Map[Map[B,D]] =
      TraversableBounded2.this.traverse(_G)(a,b)(_m)
    def map[B <: Cat0,D <: Cat1](a : A => B,b : C => D): Map[B,D] =
      TraversableBounded2.this.fmap(a,b)(_m)
  }
}

trait Traversable3 extends functor.Functor3 with TraversableBounded3 {
  type Cat0 = Any;type Cat1 = Any;type Cat2 = Any
  type Map[+A,+B,+C]
}

trait TraversableBounded3 {
  type Cat0;type Cat1;type Cat2
  type Map[+A <: Cat0,+B <: Cat1,+C <: Cat2]
  type Range = Map[Cat0,Cat1,Cat2]
  def traverse[A <: Cat0,C <: Cat1,E <: Cat2,B <: Cat0,D <: Cat1,F <: Cat2](_G : applicative.Applicative)(a : A => _G.Map[B],b : C => _G.Map[D],c : E => _G.Map[F]): Map[A,C,E] => _G.Map[Map[B,D,F]]
  def fmap[A <: Cat0,C <: Cat1,E <: Cat2,B <: Cat0,D <: Cat1,F <: Cat2](a : A => B,b : C => D,c : E => F): Map[A,C,E] => Map[B,D,F] = traverse[A,C,E,B,D,F](applicative.Applicative.Identity)(a,b,c)
  def apply[A <: Cat0,C <: Cat1,E <: Cat2](_m : Map[A,C,E]): View[A,C,E] = new View(_m)
  
  class View[A <: Cat0,C <: Cat1,E <: Cat2](_m : Map[A,C,E]) {
    def traverse[B <: Cat0,D <: Cat1,F <: Cat2](_G : applicative.Applicative)(a : A => _G.Map[B],b : C => _G.Map[D],c : E => _G.Map[F]):
        _G.Map[Map[B,D,F]] =
      TraversableBounded3.this.traverse(_G)(a,b,c)(_m)
    def map[B <: Cat0,D <: Cat1,F <: Cat2](a : A => B,b : C => D,c : E => F): Map[B,D,F] =
      TraversableBounded3.this.fmap(a,b,c)(_m)
  }
}

trait Traversable4 extends functor.Functor4 with TraversableBounded4 {
  type Cat0 = Any;type Cat1 = Any;type Cat2 = Any;type Cat3 = Any
  type Map[+A,+B,+C,+D]
}

trait TraversableBounded4 {
  type Cat0;type Cat1;type Cat2;type Cat3
  type Map[+A <: Cat0,+B <: Cat1,+C <: Cat2,+D <: Cat3]
  type Range = Map[Cat0,Cat1,Cat2,Cat3]
  def traverse[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3](_G : applicative.Applicative)(a : A => _G.Map[B],b : C => _G.Map[D],c : E => _G.Map[F],d : G => _G.Map[H]): Map[A,C,E,G] => _G.Map[Map[B,D,F,H]]
  def fmap[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3](a : A => B,b : C => D,c : E => F,d : G => H): Map[A,C,E,G] => Map[B,D,F,H] = traverse[A,C,E,G,B,D,F,H](applicative.Applicative.Identity)(a,b,c,d)
  def apply[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3](_m : Map[A,C,E,G]): View[A,C,E,G] = new View(_m)
  
  class View[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3](_m : Map[A,C,E,G]) {
    def traverse[B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3](_G : applicative.Applicative)(a : A => _G.Map[B],b : C => _G.Map[D],c : E => _G.Map[F],d : G => _G.Map[H]):
        _G.Map[Map[B,D,F,H]] =
      TraversableBounded4.this.traverse(_G)(a,b,c,d)(_m)
    def map[B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3](a : A => B,b : C => D,c : E => F,d : G => H): Map[B,D,F,H] =
      TraversableBounded4.this.fmap(a,b,c,d)(_m)
  }
}

trait Traversable5 extends functor.Functor5 with TraversableBounded5 {
  type Cat0 = Any;type Cat1 = Any;type Cat2 = Any;type Cat3 = Any;type Cat4 = Any
  type Map[+A,+B,+C,+D,+E]
}

trait TraversableBounded5 {
  type Cat0;type Cat1;type Cat2;type Cat3;type Cat4
  type Map[+A <: Cat0,+B <: Cat1,+C <: Cat2,+D <: Cat3,+E <: Cat4]
  type Range = Map[Cat0,Cat1,Cat2,Cat3,Cat4]
  def traverse[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4](_G : applicative.Applicative)(a : A => _G.Map[B],b : C => _G.Map[D],c : E => _G.Map[F],d : G => _G.Map[H],e : I => _G.Map[J]): Map[A,C,E,G,I] => _G.Map[Map[B,D,F,H,J]]
  def fmap[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J): Map[A,C,E,G,I] => Map[B,D,F,H,J] = traverse[A,C,E,G,I,B,D,F,H,J](applicative.Applicative.Identity)(a,b,c,d,e)
  def apply[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4](_m : Map[A,C,E,G,I]): View[A,C,E,G,I] = new View(_m)
  
  class View[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4](_m : Map[A,C,E,G,I]) {
    def traverse[B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4](_G : applicative.Applicative)(a : A => _G.Map[B],b : C => _G.Map[D],c : E => _G.Map[F],d : G => _G.Map[H],e : I => _G.Map[J]):
        _G.Map[Map[B,D,F,H,J]] =
      TraversableBounded5.this.traverse(_G)(a,b,c,d,e)(_m)
    def map[B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J): Map[B,D,F,H,J] =
      TraversableBounded5.this.fmap(a,b,c,d,e)(_m)
  }
}

trait Traversable6 extends functor.Functor6 with TraversableBounded6 {
  type Cat0 = Any;type Cat1 = Any;type Cat2 = Any;type Cat3 = Any;type Cat4 = Any;type Cat5 = Any
  type Map[+A,+B,+C,+D,+E,+F]
}

trait TraversableBounded6 {
  type Cat0;type Cat1;type Cat2;type Cat3;type Cat4;type Cat5
  type Map[+A <: Cat0,+B <: Cat1,+C <: Cat2,+D <: Cat3,+E <: Cat4,+F <: Cat5]
  type Range = Map[Cat0,Cat1,Cat2,Cat3,Cat4,Cat5]
  def traverse[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5](_G : applicative.Applicative)(a : A => _G.Map[B],b : C => _G.Map[D],c : E => _G.Map[F],d : G => _G.Map[H],e : I => _G.Map[J],f : K => _G.Map[L]): Map[A,C,E,G,I,K] => _G.Map[Map[B,D,F,H,J,L]]
  def fmap[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L): Map[A,C,E,G,I,K] => Map[B,D,F,H,J,L] = traverse[A,C,E,G,I,K,B,D,F,H,J,L](applicative.Applicative.Identity)(a,b,c,d,e,f)
  def apply[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5](_m : Map[A,C,E,G,I,K]): View[A,C,E,G,I,K] = new View(_m)
  
  class View[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5](_m : Map[A,C,E,G,I,K]) {
    def traverse[B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5](_G : applicative.Applicative)(a : A => _G.Map[B],b : C => _G.Map[D],c : E => _G.Map[F],d : G => _G.Map[H],e : I => _G.Map[J],f : K => _G.Map[L]):
        _G.Map[Map[B,D,F,H,J,L]] =
      TraversableBounded6.this.traverse(_G)(a,b,c,d,e,f)(_m)
    def map[B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L): Map[B,D,F,H,J,L] =
      TraversableBounded6.this.fmap(a,b,c,d,e,f)(_m)
  }
}

trait Traversable7 extends functor.Functor7 with TraversableBounded7 {
  type Cat0 = Any;type Cat1 = Any;type Cat2 = Any;type Cat3 = Any;type Cat4 = Any;type Cat5 = Any;type Cat6 = Any
  type Map[+A,+B,+C,+D,+E,+F,+G]
}

trait TraversableBounded7 {
  type Cat0;type Cat1;type Cat2;type Cat3;type Cat4;type Cat5;type Cat6
  type Map[+A <: Cat0,+B <: Cat1,+C <: Cat2,+D <: Cat3,+E <: Cat4,+F <: Cat5,+G <: Cat6]
  type Range = Map[Cat0,Cat1,Cat2,Cat3,Cat4,Cat5,Cat6]
  def traverse[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6](_G : applicative.Applicative)(a : A => _G.Map[B],b : C => _G.Map[D],c : E => _G.Map[F],d : G => _G.Map[H],e : I => _G.Map[J],f : K => _G.Map[L],g : M => _G.Map[N]): Map[A,C,E,G,I,K,M] => _G.Map[Map[B,D,F,H,J,L,N]]
  def fmap[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N): Map[A,C,E,G,I,K,M] => Map[B,D,F,H,J,L,N] = traverse[A,C,E,G,I,K,M,B,D,F,H,J,L,N](applicative.Applicative.Identity)(a,b,c,d,e,f,g)
  def apply[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6](_m : Map[A,C,E,G,I,K,M]): View[A,C,E,G,I,K,M] = new View(_m)
  
  class View[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6](_m : Map[A,C,E,G,I,K,M]) {
    def traverse[B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6](_G : applicative.Applicative)(a : A => _G.Map[B],b : C => _G.Map[D],c : E => _G.Map[F],d : G => _G.Map[H],e : I => _G.Map[J],f : K => _G.Map[L],g : M => _G.Map[N]):
        _G.Map[Map[B,D,F,H,J,L,N]] =
      TraversableBounded7.this.traverse(_G)(a,b,c,d,e,f,g)(_m)
    def map[B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N): Map[B,D,F,H,J,L,N] =
      TraversableBounded7.this.fmap(a,b,c,d,e,f,g)(_m)
  }
}

trait Traversable8 extends functor.Functor8 with TraversableBounded8 {
  type Cat0 = Any;type Cat1 = Any;type Cat2 = Any;type Cat3 = Any;type Cat4 = Any;type Cat5 = Any;type Cat6 = Any;type Cat7 = Any
  type Map[+A,+B,+C,+D,+E,+F,+G,+H]
}

trait TraversableBounded8 {
  type Cat0;type Cat1;type Cat2;type Cat3;type Cat4;type Cat5;type Cat6;type Cat7
  type Map[+A <: Cat0,+B <: Cat1,+C <: Cat2,+D <: Cat3,+E <: Cat4,+F <: Cat5,+G <: Cat6,+H <: Cat7]
  type Range = Map[Cat0,Cat1,Cat2,Cat3,Cat4,Cat5,Cat6,Cat7]
  def traverse[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7](_G : applicative.Applicative)(a : A => _G.Map[B],b : C => _G.Map[D],c : E => _G.Map[F],d : G => _G.Map[H],e : I => _G.Map[J],f : K => _G.Map[L],g : M => _G.Map[N],h : O => _G.Map[P]): Map[A,C,E,G,I,K,M,O] => _G.Map[Map[B,D,F,H,J,L,N,P]]
  def fmap[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N,h : O => P): Map[A,C,E,G,I,K,M,O] => Map[B,D,F,H,J,L,N,P] = traverse[A,C,E,G,I,K,M,O,B,D,F,H,J,L,N,P](applicative.Applicative.Identity)(a,b,c,d,e,f,g,h)
  def apply[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7](_m : Map[A,C,E,G,I,K,M,O]): View[A,C,E,G,I,K,M,O] = new View(_m)
  
  class View[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7](_m : Map[A,C,E,G,I,K,M,O]) {
    def traverse[B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7](_G : applicative.Applicative)(a : A => _G.Map[B],b : C => _G.Map[D],c : E => _G.Map[F],d : G => _G.Map[H],e : I => _G.Map[J],f : K => _G.Map[L],g : M => _G.Map[N],h : O => _G.Map[P]):
        _G.Map[Map[B,D,F,H,J,L,N,P]] =
      TraversableBounded8.this.traverse(_G)(a,b,c,d,e,f,g,h)(_m)
    def map[B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N,h : O => P): Map[B,D,F,H,J,L,N,P] =
      TraversableBounded8.this.fmap(a,b,c,d,e,f,g,h)(_m)
  }
}

trait Traversable9 extends functor.Functor9 with TraversableBounded9 {
  type Cat0 = Any;type Cat1 = Any;type Cat2 = Any;type Cat3 = Any;type Cat4 = Any;type Cat5 = Any;type Cat6 = Any;type Cat7 = Any;type Cat8 = Any
  type Map[+A,+B,+C,+D,+E,+F,+G,+H,+I]
}

trait TraversableBounded9 {
  type Cat0;type Cat1;type Cat2;type Cat3;type Cat4;type Cat5;type Cat6;type Cat7;type Cat8
  type Map[+A <: Cat0,+B <: Cat1,+C <: Cat2,+D <: Cat3,+E <: Cat4,+F <: Cat5,+G <: Cat6,+H <: Cat7,+I <: Cat8]
  type Range = Map[Cat0,Cat1,Cat2,Cat3,Cat4,Cat5,Cat6,Cat7,Cat8]
  def traverse[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8](_G : applicative.Applicative)(a : A => _G.Map[B],b : C => _G.Map[D],c : E => _G.Map[F],d : G => _G.Map[H],e : I => _G.Map[J],f : K => _G.Map[L],g : M => _G.Map[N],h : O => _G.Map[P],i : Q => _G.Map[R]): Map[A,C,E,G,I,K,M,O,Q] => _G.Map[Map[B,D,F,H,J,L,N,P,R]]
  def fmap[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N,h : O => P,i : Q => R): Map[A,C,E,G,I,K,M,O,Q] => Map[B,D,F,H,J,L,N,P,R] = traverse[A,C,E,G,I,K,M,O,Q,B,D,F,H,J,L,N,P,R](applicative.Applicative.Identity)(a,b,c,d,e,f,g,h,i)
  def apply[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8](_m : Map[A,C,E,G,I,K,M,O,Q]): View[A,C,E,G,I,K,M,O,Q] = new View(_m)
  
  class View[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8](_m : Map[A,C,E,G,I,K,M,O,Q]) {
    def traverse[B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8](_G : applicative.Applicative)(a : A => _G.Map[B],b : C => _G.Map[D],c : E => _G.Map[F],d : G => _G.Map[H],e : I => _G.Map[J],f : K => _G.Map[L],g : M => _G.Map[N],h : O => _G.Map[P],i : Q => _G.Map[R]):
        _G.Map[Map[B,D,F,H,J,L,N,P,R]] =
      TraversableBounded9.this.traverse(_G)(a,b,c,d,e,f,g,h,i)(_m)
    def map[B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N,h : O => P,i : Q => R): Map[B,D,F,H,J,L,N,P,R] =
      TraversableBounded9.this.fmap(a,b,c,d,e,f,g,h,i)(_m)
  }
}

trait Traversable10 extends functor.Functor10 with TraversableBounded10 {
  type Cat0 = Any;type Cat1 = Any;type Cat2 = Any;type Cat3 = Any;type Cat4 = Any;type Cat5 = Any;type Cat6 = Any;type Cat7 = Any;type Cat8 = Any;type Cat9 = Any
  type Map[+A,+B,+C,+D,+E,+F,+G,+H,+I,+J]
}

trait TraversableBounded10 {
  type Cat0;type Cat1;type Cat2;type Cat3;type Cat4;type Cat5;type Cat6;type Cat7;type Cat8;type Cat9
  type Map[+A <: Cat0,+B <: Cat1,+C <: Cat2,+D <: Cat3,+E <: Cat4,+F <: Cat5,+G <: Cat6,+H <: Cat7,+I <: Cat8,+J <: Cat9]
  type Range = Map[Cat0,Cat1,Cat2,Cat3,Cat4,Cat5,Cat6,Cat7,Cat8,Cat9]
  def traverse[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9](_G : applicative.Applicative)(a : A => _G.Map[B],b : C => _G.Map[D],c : E => _G.Map[F],d : G => _G.Map[H],e : I => _G.Map[J],f : K => _G.Map[L],g : M => _G.Map[N],h : O => _G.Map[P],i : Q => _G.Map[R],j : S => _G.Map[T]): Map[A,C,E,G,I,K,M,O,Q,S] => _G.Map[Map[B,D,F,H,J,L,N,P,R,T]]
  def fmap[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N,h : O => P,i : Q => R,j : S => T): Map[A,C,E,G,I,K,M,O,Q,S] => Map[B,D,F,H,J,L,N,P,R,T] = traverse[A,C,E,G,I,K,M,O,Q,S,B,D,F,H,J,L,N,P,R,T](applicative.Applicative.Identity)(a,b,c,d,e,f,g,h,i,j)
  def apply[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9](_m : Map[A,C,E,G,I,K,M,O,Q,S]): View[A,C,E,G,I,K,M,O,Q,S] = new View(_m)
  
  class View[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9](_m : Map[A,C,E,G,I,K,M,O,Q,S]) {
    def traverse[B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9](_G : applicative.Applicative)(a : A => _G.Map[B],b : C => _G.Map[D],c : E => _G.Map[F],d : G => _G.Map[H],e : I => _G.Map[J],f : K => _G.Map[L],g : M => _G.Map[N],h : O => _G.Map[P],i : Q => _G.Map[R],j : S => _G.Map[T]):
        _G.Map[Map[B,D,F,H,J,L,N,P,R,T]] =
      TraversableBounded10.this.traverse(_G)(a,b,c,d,e,f,g,h,i,j)(_m)
    def map[B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N,h : O => P,i : Q => R,j : S => T): Map[B,D,F,H,J,L,N,P,R,T] =
      TraversableBounded10.this.fmap(a,b,c,d,e,f,g,h,i,j)(_m)
  }
}

trait Traversable11 extends functor.Functor11 with TraversableBounded11 {
  type Cat0 = Any;type Cat1 = Any;type Cat2 = Any;type Cat3 = Any;type Cat4 = Any;type Cat5 = Any;type Cat6 = Any;type Cat7 = Any;type Cat8 = Any;type Cat9 = Any;type Cat10 = Any
  type Map[+A,+B,+C,+D,+E,+F,+G,+H,+I,+J,+K]
}

trait TraversableBounded11 {
  type Cat0;type Cat1;type Cat2;type Cat3;type Cat4;type Cat5;type Cat6;type Cat7;type Cat8;type Cat9;type Cat10
  type Map[+A <: Cat0,+B <: Cat1,+C <: Cat2,+D <: Cat3,+E <: Cat4,+F <: Cat5,+G <: Cat6,+H <: Cat7,+I <: Cat8,+J <: Cat9,+K <: Cat10]
  type Range = Map[Cat0,Cat1,Cat2,Cat3,Cat4,Cat5,Cat6,Cat7,Cat8,Cat9,Cat10]
  def traverse[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10,B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10](_G : applicative.Applicative)(a : A => _G.Map[B],b : C => _G.Map[D],c : E => _G.Map[F],d : G => _G.Map[H],e : I => _G.Map[J],f : K => _G.Map[L],g : M => _G.Map[N],h : O => _G.Map[P],i : Q => _G.Map[R],j : S => _G.Map[T],k : U => _G.Map[V]): Map[A,C,E,G,I,K,M,O,Q,S,U] => _G.Map[Map[B,D,F,H,J,L,N,P,R,T,V]]
  def fmap[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10,B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N,h : O => P,i : Q => R,j : S => T,k : U => V): Map[A,C,E,G,I,K,M,O,Q,S,U] => Map[B,D,F,H,J,L,N,P,R,T,V] = traverse[A,C,E,G,I,K,M,O,Q,S,U,B,D,F,H,J,L,N,P,R,T,V](applicative.Applicative.Identity)(a,b,c,d,e,f,g,h,i,j,k)
  def apply[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10](_m : Map[A,C,E,G,I,K,M,O,Q,S,U]): View[A,C,E,G,I,K,M,O,Q,S,U] = new View(_m)
  
  class View[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10](_m : Map[A,C,E,G,I,K,M,O,Q,S,U]) {
    def traverse[B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10](_G : applicative.Applicative)(a : A => _G.Map[B],b : C => _G.Map[D],c : E => _G.Map[F],d : G => _G.Map[H],e : I => _G.Map[J],f : K => _G.Map[L],g : M => _G.Map[N],h : O => _G.Map[P],i : Q => _G.Map[R],j : S => _G.Map[T],k : U => _G.Map[V]):
        _G.Map[Map[B,D,F,H,J,L,N,P,R,T,V]] =
      TraversableBounded11.this.traverse(_G)(a,b,c,d,e,f,g,h,i,j,k)(_m)
    def map[B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N,h : O => P,i : Q => R,j : S => T,k : U => V): Map[B,D,F,H,J,L,N,P,R,T,V] =
      TraversableBounded11.this.fmap(a,b,c,d,e,f,g,h,i,j,k)(_m)
  }
}

trait Traversable12 extends functor.Functor12 with TraversableBounded12 {
  type Cat0 = Any;type Cat1 = Any;type Cat2 = Any;type Cat3 = Any;type Cat4 = Any;type Cat5 = Any;type Cat6 = Any;type Cat7 = Any;type Cat8 = Any;type Cat9 = Any;type Cat10 = Any;type Cat11 = Any
  type Map[+A,+B,+C,+D,+E,+F,+G,+H,+I,+J,+K,+L]
}

trait TraversableBounded12 {
  type Cat0;type Cat1;type Cat2;type Cat3;type Cat4;type Cat5;type Cat6;type Cat7;type Cat8;type Cat9;type Cat10;type Cat11
  type Map[+A <: Cat0,+B <: Cat1,+C <: Cat2,+D <: Cat3,+E <: Cat4,+F <: Cat5,+G <: Cat6,+H <: Cat7,+I <: Cat8,+J <: Cat9,+K <: Cat10,+L <: Cat11]
  type Range = Map[Cat0,Cat1,Cat2,Cat3,Cat4,Cat5,Cat6,Cat7,Cat8,Cat9,Cat10,Cat11]
  def traverse[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10,W <: Cat11,B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10,X <: Cat11](_G : applicative.Applicative)(a : A => _G.Map[B],b : C => _G.Map[D],c : E => _G.Map[F],d : G => _G.Map[H],e : I => _G.Map[J],f : K => _G.Map[L],g : M => _G.Map[N],h : O => _G.Map[P],i : Q => _G.Map[R],j : S => _G.Map[T],k : U => _G.Map[V],l : W => _G.Map[X]): Map[A,C,E,G,I,K,M,O,Q,S,U,W] => _G.Map[Map[B,D,F,H,J,L,N,P,R,T,V,X]]
  def fmap[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10,W <: Cat11,B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10,X <: Cat11](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N,h : O => P,i : Q => R,j : S => T,k : U => V,l : W => X): Map[A,C,E,G,I,K,M,O,Q,S,U,W] => Map[B,D,F,H,J,L,N,P,R,T,V,X] = traverse[A,C,E,G,I,K,M,O,Q,S,U,W,B,D,F,H,J,L,N,P,R,T,V,X](applicative.Applicative.Identity)(a,b,c,d,e,f,g,h,i,j,k,l)
  def apply[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10,W <: Cat11](_m : Map[A,C,E,G,I,K,M,O,Q,S,U,W]): View[A,C,E,G,I,K,M,O,Q,S,U,W] = new View(_m)
  
  class View[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10,W <: Cat11](_m : Map[A,C,E,G,I,K,M,O,Q,S,U,W]) {
    def traverse[B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10,X <: Cat11](_G : applicative.Applicative)(a : A => _G.Map[B],b : C => _G.Map[D],c : E => _G.Map[F],d : G => _G.Map[H],e : I => _G.Map[J],f : K => _G.Map[L],g : M => _G.Map[N],h : O => _G.Map[P],i : Q => _G.Map[R],j : S => _G.Map[T],k : U => _G.Map[V],l : W => _G.Map[X]):
        _G.Map[Map[B,D,F,H,J,L,N,P,R,T,V,X]] =
      TraversableBounded12.this.traverse(_G)(a,b,c,d,e,f,g,h,i,j,k,l)(_m)
    def map[B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10,X <: Cat11](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N,h : O => P,i : Q => R,j : S => T,k : U => V,l : W => X): Map[B,D,F,H,J,L,N,P,R,T,V,X] =
      TraversableBounded12.this.fmap(a,b,c,d,e,f,g,h,i,j,k,l)(_m)
  }
}

trait Traversable13 extends functor.Functor13 with TraversableBounded13 {
  type Cat0 = Any;type Cat1 = Any;type Cat2 = Any;type Cat3 = Any;type Cat4 = Any;type Cat5 = Any;type Cat6 = Any;type Cat7 = Any;type Cat8 = Any;type Cat9 = Any;type Cat10 = Any;type Cat11 = Any;type Cat12 = Any
  type Map[+A,+B,+C,+D,+E,+F,+G,+H,+I,+J,+K,+L,+M]
}

trait TraversableBounded13 {
  type Cat0;type Cat1;type Cat2;type Cat3;type Cat4;type Cat5;type Cat6;type Cat7;type Cat8;type Cat9;type Cat10;type Cat11;type Cat12
  type Map[+A <: Cat0,+B <: Cat1,+C <: Cat2,+D <: Cat3,+E <: Cat4,+F <: Cat5,+G <: Cat6,+H <: Cat7,+I <: Cat8,+J <: Cat9,+K <: Cat10,+L <: Cat11,+M <: Cat12]
  type Range = Map[Cat0,Cat1,Cat2,Cat3,Cat4,Cat5,Cat6,Cat7,Cat8,Cat9,Cat10,Cat11,Cat12]
  def traverse[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10,W <: Cat11,Y <: Cat12,B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10,X <: Cat11,Z <: Cat12](_G : applicative.Applicative)(a : A => _G.Map[B],b : C => _G.Map[D],c : E => _G.Map[F],d : G => _G.Map[H],e : I => _G.Map[J],f : K => _G.Map[L],g : M => _G.Map[N],h : O => _G.Map[P],i : Q => _G.Map[R],j : S => _G.Map[T],k : U => _G.Map[V],l : W => _G.Map[X],m : Y => _G.Map[Z]): Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y] => _G.Map[Map[B,D,F,H,J,L,N,P,R,T,V,X,Z]]
  def fmap[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10,W <: Cat11,Y <: Cat12,B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10,X <: Cat11,Z <: Cat12](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N,h : O => P,i : Q => R,j : S => T,k : U => V,l : W => X,m : Y => Z): Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y] => Map[B,D,F,H,J,L,N,P,R,T,V,X,Z] = traverse[A,C,E,G,I,K,M,O,Q,S,U,W,Y,B,D,F,H,J,L,N,P,R,T,V,X,Z](applicative.Applicative.Identity)(a,b,c,d,e,f,g,h,i,j,k,l,m)
  def apply[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10,W <: Cat11,Y <: Cat12](_m : Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y]): View[A,C,E,G,I,K,M,O,Q,S,U,W,Y] = new View(_m)
  
  class View[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10,W <: Cat11,Y <: Cat12](_m : Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y]) {
    def traverse[B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10,X <: Cat11,Z <: Cat12](_G : applicative.Applicative)(a : A => _G.Map[B],b : C => _G.Map[D],c : E => _G.Map[F],d : G => _G.Map[H],e : I => _G.Map[J],f : K => _G.Map[L],g : M => _G.Map[N],h : O => _G.Map[P],i : Q => _G.Map[R],j : S => _G.Map[T],k : U => _G.Map[V],l : W => _G.Map[X],m : Y => _G.Map[Z]):
        _G.Map[Map[B,D,F,H,J,L,N,P,R,T,V,X,Z]] =
      TraversableBounded13.this.traverse(_G)(a,b,c,d,e,f,g,h,i,j,k,l,m)(_m)
    def map[B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10,X <: Cat11,Z <: Cat12](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N,h : O => P,i : Q => R,j : S => T,k : U => V,l : W => X,m : Y => Z): Map[B,D,F,H,J,L,N,P,R,T,V,X,Z] =
      TraversableBounded13.this.fmap(a,b,c,d,e,f,g,h,i,j,k,l,m)(_m)
  }
}

trait Traversable14 extends functor.Functor14 with TraversableBounded14 {
  type Cat0 = Any;type Cat1 = Any;type Cat2 = Any;type Cat3 = Any;type Cat4 = Any;type Cat5 = Any;type Cat6 = Any;type Cat7 = Any;type Cat8 = Any;type Cat9 = Any;type Cat10 = Any;type Cat11 = Any;type Cat12 = Any;type Cat13 = Any
  type Map[+A,+B,+C,+D,+E,+F,+G,+H,+I,+J,+K,+L,+M,+N]
}

trait TraversableBounded14 {
  type Cat0;type Cat1;type Cat2;type Cat3;type Cat4;type Cat5;type Cat6;type Cat7;type Cat8;type Cat9;type Cat10;type Cat11;type Cat12;type Cat13
  type Map[+A <: Cat0,+B <: Cat1,+C <: Cat2,+D <: Cat3,+E <: Cat4,+F <: Cat5,+G <: Cat6,+H <: Cat7,+I <: Cat8,+J <: Cat9,+K <: Cat10,+L <: Cat11,+M <: Cat12,+N <: Cat13]
  type Range = Map[Cat0,Cat1,Cat2,Cat3,Cat4,Cat5,Cat6,Cat7,Cat8,Cat9,Cat10,Cat11,Cat12,Cat13]
  def traverse[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10,W <: Cat11,Y <: Cat12,BA <: Cat13,B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10,X <: Cat11,Z <: Cat12,BB <: Cat13](_G : applicative.Applicative)(a : A => _G.Map[B],b : C => _G.Map[D],c : E => _G.Map[F],d : G => _G.Map[H],e : I => _G.Map[J],f : K => _G.Map[L],g : M => _G.Map[N],h : O => _G.Map[P],i : Q => _G.Map[R],j : S => _G.Map[T],k : U => _G.Map[V],l : W => _G.Map[X],m : Y => _G.Map[Z],n : BA => _G.Map[BB]): Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA] => _G.Map[Map[B,D,F,H,J,L,N,P,R,T,V,X,Z,BB]]
  def fmap[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10,W <: Cat11,Y <: Cat12,BA <: Cat13,B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10,X <: Cat11,Z <: Cat12,BB <: Cat13](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N,h : O => P,i : Q => R,j : S => T,k : U => V,l : W => X,m : Y => Z,n : BA => BB): Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA] => Map[B,D,F,H,J,L,N,P,R,T,V,X,Z,BB] = traverse[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,B,D,F,H,J,L,N,P,R,T,V,X,Z,BB](applicative.Applicative.Identity)(a,b,c,d,e,f,g,h,i,j,k,l,m,n)
  def apply[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10,W <: Cat11,Y <: Cat12,BA <: Cat13](_m : Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA]): View[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA] = new View(_m)
  
  class View[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10,W <: Cat11,Y <: Cat12,BA <: Cat13](_m : Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA]) {
    def traverse[B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10,X <: Cat11,Z <: Cat12,BB <: Cat13](_G : applicative.Applicative)(a : A => _G.Map[B],b : C => _G.Map[D],c : E => _G.Map[F],d : G => _G.Map[H],e : I => _G.Map[J],f : K => _G.Map[L],g : M => _G.Map[N],h : O => _G.Map[P],i : Q => _G.Map[R],j : S => _G.Map[T],k : U => _G.Map[V],l : W => _G.Map[X],m : Y => _G.Map[Z],n : BA => _G.Map[BB]):
        _G.Map[Map[B,D,F,H,J,L,N,P,R,T,V,X,Z,BB]] =
      TraversableBounded14.this.traverse(_G)(a,b,c,d,e,f,g,h,i,j,k,l,m,n)(_m)
    def map[B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10,X <: Cat11,Z <: Cat12,BB <: Cat13](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N,h : O => P,i : Q => R,j : S => T,k : U => V,l : W => X,m : Y => Z,n : BA => BB): Map[B,D,F,H,J,L,N,P,R,T,V,X,Z,BB] =
      TraversableBounded14.this.fmap(a,b,c,d,e,f,g,h,i,j,k,l,m,n)(_m)
  }
}

trait Traversable15 extends functor.Functor15 with TraversableBounded15 {
  type Cat0 = Any;type Cat1 = Any;type Cat2 = Any;type Cat3 = Any;type Cat4 = Any;type Cat5 = Any;type Cat6 = Any;type Cat7 = Any;type Cat8 = Any;type Cat9 = Any;type Cat10 = Any;type Cat11 = Any;type Cat12 = Any;type Cat13 = Any;type Cat14 = Any
  type Map[+A,+B,+C,+D,+E,+F,+G,+H,+I,+J,+K,+L,+M,+N,+O]
}

trait TraversableBounded15 {
  type Cat0;type Cat1;type Cat2;type Cat3;type Cat4;type Cat5;type Cat6;type Cat7;type Cat8;type Cat9;type Cat10;type Cat11;type Cat12;type Cat13;type Cat14
  type Map[+A <: Cat0,+B <: Cat1,+C <: Cat2,+D <: Cat3,+E <: Cat4,+F <: Cat5,+G <: Cat6,+H <: Cat7,+I <: Cat8,+J <: Cat9,+K <: Cat10,+L <: Cat11,+M <: Cat12,+N <: Cat13,+O <: Cat14]
  type Range = Map[Cat0,Cat1,Cat2,Cat3,Cat4,Cat5,Cat6,Cat7,Cat8,Cat9,Cat10,Cat11,Cat12,Cat13,Cat14]
  def traverse[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10,W <: Cat11,Y <: Cat12,BA <: Cat13,BC <: Cat14,B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10,X <: Cat11,Z <: Cat12,BB <: Cat13,BD <: Cat14](_G : applicative.Applicative)(a : A => _G.Map[B],b : C => _G.Map[D],c : E => _G.Map[F],d : G => _G.Map[H],e : I => _G.Map[J],f : K => _G.Map[L],g : M => _G.Map[N],h : O => _G.Map[P],i : Q => _G.Map[R],j : S => _G.Map[T],k : U => _G.Map[V],l : W => _G.Map[X],m : Y => _G.Map[Z],n : BA => _G.Map[BB],o : BC => _G.Map[BD]): Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC] => _G.Map[Map[B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD]]
  def fmap[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10,W <: Cat11,Y <: Cat12,BA <: Cat13,BC <: Cat14,B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10,X <: Cat11,Z <: Cat12,BB <: Cat13,BD <: Cat14](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N,h : O => P,i : Q => R,j : S => T,k : U => V,l : W => X,m : Y => Z,n : BA => BB,o : BC => BD): Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC] => Map[B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD] = traverse[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD](applicative.Applicative.Identity)(a,b,c,d,e,f,g,h,i,j,k,l,m,n,o)
  def apply[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10,W <: Cat11,Y <: Cat12,BA <: Cat13,BC <: Cat14](_m : Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC]): View[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC] = new View(_m)
  
  class View[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10,W <: Cat11,Y <: Cat12,BA <: Cat13,BC <: Cat14](_m : Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC]) {
    def traverse[B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10,X <: Cat11,Z <: Cat12,BB <: Cat13,BD <: Cat14](_G : applicative.Applicative)(a : A => _G.Map[B],b : C => _G.Map[D],c : E => _G.Map[F],d : G => _G.Map[H],e : I => _G.Map[J],f : K => _G.Map[L],g : M => _G.Map[N],h : O => _G.Map[P],i : Q => _G.Map[R],j : S => _G.Map[T],k : U => _G.Map[V],l : W => _G.Map[X],m : Y => _G.Map[Z],n : BA => _G.Map[BB],o : BC => _G.Map[BD]):
        _G.Map[Map[B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD]] =
      TraversableBounded15.this.traverse(_G)(a,b,c,d,e,f,g,h,i,j,k,l,m,n,o)(_m)
    def map[B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10,X <: Cat11,Z <: Cat12,BB <: Cat13,BD <: Cat14](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N,h : O => P,i : Q => R,j : S => T,k : U => V,l : W => X,m : Y => Z,n : BA => BB,o : BC => BD): Map[B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD] =
      TraversableBounded15.this.fmap(a,b,c,d,e,f,g,h,i,j,k,l,m,n,o)(_m)
  }
}

trait Traversable16 extends functor.Functor16 with TraversableBounded16 {
  type Cat0 = Any;type Cat1 = Any;type Cat2 = Any;type Cat3 = Any;type Cat4 = Any;type Cat5 = Any;type Cat6 = Any;type Cat7 = Any;type Cat8 = Any;type Cat9 = Any;type Cat10 = Any;type Cat11 = Any;type Cat12 = Any;type Cat13 = Any;type Cat14 = Any;type Cat15 = Any
  type Map[+A,+B,+C,+D,+E,+F,+G,+H,+I,+J,+K,+L,+M,+N,+O,+P]
}

trait TraversableBounded16 {
  type Cat0;type Cat1;type Cat2;type Cat3;type Cat4;type Cat5;type Cat6;type Cat7;type Cat8;type Cat9;type Cat10;type Cat11;type Cat12;type Cat13;type Cat14;type Cat15
  type Map[+A <: Cat0,+B <: Cat1,+C <: Cat2,+D <: Cat3,+E <: Cat4,+F <: Cat5,+G <: Cat6,+H <: Cat7,+I <: Cat8,+J <: Cat9,+K <: Cat10,+L <: Cat11,+M <: Cat12,+N <: Cat13,+O <: Cat14,+P <: Cat15]
  type Range = Map[Cat0,Cat1,Cat2,Cat3,Cat4,Cat5,Cat6,Cat7,Cat8,Cat9,Cat10,Cat11,Cat12,Cat13,Cat14,Cat15]
  def traverse[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10,W <: Cat11,Y <: Cat12,BA <: Cat13,BC <: Cat14,BE <: Cat15,B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10,X <: Cat11,Z <: Cat12,BB <: Cat13,BD <: Cat14,BF <: Cat15](_G : applicative.Applicative)(a : A => _G.Map[B],b : C => _G.Map[D],c : E => _G.Map[F],d : G => _G.Map[H],e : I => _G.Map[J],f : K => _G.Map[L],g : M => _G.Map[N],h : O => _G.Map[P],i : Q => _G.Map[R],j : S => _G.Map[T],k : U => _G.Map[V],l : W => _G.Map[X],m : Y => _G.Map[Z],n : BA => _G.Map[BB],o : BC => _G.Map[BD],p : BE => _G.Map[BF]): Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE] => _G.Map[Map[B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF]]
  def fmap[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10,W <: Cat11,Y <: Cat12,BA <: Cat13,BC <: Cat14,BE <: Cat15,B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10,X <: Cat11,Z <: Cat12,BB <: Cat13,BD <: Cat14,BF <: Cat15](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N,h : O => P,i : Q => R,j : S => T,k : U => V,l : W => X,m : Y => Z,n : BA => BB,o : BC => BD,p : BE => BF): Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE] => Map[B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF] = traverse[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF](applicative.Applicative.Identity)(a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p)
  def apply[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10,W <: Cat11,Y <: Cat12,BA <: Cat13,BC <: Cat14,BE <: Cat15](_m : Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE]): View[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE] = new View(_m)
  
  class View[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10,W <: Cat11,Y <: Cat12,BA <: Cat13,BC <: Cat14,BE <: Cat15](_m : Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE]) {
    def traverse[B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10,X <: Cat11,Z <: Cat12,BB <: Cat13,BD <: Cat14,BF <: Cat15](_G : applicative.Applicative)(a : A => _G.Map[B],b : C => _G.Map[D],c : E => _G.Map[F],d : G => _G.Map[H],e : I => _G.Map[J],f : K => _G.Map[L],g : M => _G.Map[N],h : O => _G.Map[P],i : Q => _G.Map[R],j : S => _G.Map[T],k : U => _G.Map[V],l : W => _G.Map[X],m : Y => _G.Map[Z],n : BA => _G.Map[BB],o : BC => _G.Map[BD],p : BE => _G.Map[BF]):
        _G.Map[Map[B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF]] =
      TraversableBounded16.this.traverse(_G)(a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p)(_m)
    def map[B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10,X <: Cat11,Z <: Cat12,BB <: Cat13,BD <: Cat14,BF <: Cat15](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N,h : O => P,i : Q => R,j : S => T,k : U => V,l : W => X,m : Y => Z,n : BA => BB,o : BC => BD,p : BE => BF): Map[B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF] =
      TraversableBounded16.this.fmap(a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p)(_m)
  }
}

trait Traversable17 extends functor.Functor17 with TraversableBounded17 {
  type Cat0 = Any;type Cat1 = Any;type Cat2 = Any;type Cat3 = Any;type Cat4 = Any;type Cat5 = Any;type Cat6 = Any;type Cat7 = Any;type Cat8 = Any;type Cat9 = Any;type Cat10 = Any;type Cat11 = Any;type Cat12 = Any;type Cat13 = Any;type Cat14 = Any;type Cat15 = Any;type Cat16 = Any
  type Map[+A,+B,+C,+D,+E,+F,+G,+H,+I,+J,+K,+L,+M,+N,+O,+P,+Q]
}

trait TraversableBounded17 {
  type Cat0;type Cat1;type Cat2;type Cat3;type Cat4;type Cat5;type Cat6;type Cat7;type Cat8;type Cat9;type Cat10;type Cat11;type Cat12;type Cat13;type Cat14;type Cat15;type Cat16
  type Map[+A <: Cat0,+B <: Cat1,+C <: Cat2,+D <: Cat3,+E <: Cat4,+F <: Cat5,+G <: Cat6,+H <: Cat7,+I <: Cat8,+J <: Cat9,+K <: Cat10,+L <: Cat11,+M <: Cat12,+N <: Cat13,+O <: Cat14,+P <: Cat15,+Q <: Cat16]
  type Range = Map[Cat0,Cat1,Cat2,Cat3,Cat4,Cat5,Cat6,Cat7,Cat8,Cat9,Cat10,Cat11,Cat12,Cat13,Cat14,Cat15,Cat16]
  def traverse[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10,W <: Cat11,Y <: Cat12,BA <: Cat13,BC <: Cat14,BE <: Cat15,BG <: Cat16,B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10,X <: Cat11,Z <: Cat12,BB <: Cat13,BD <: Cat14,BF <: Cat15,BH <: Cat16](_G : applicative.Applicative)(a : A => _G.Map[B],b : C => _G.Map[D],c : E => _G.Map[F],d : G => _G.Map[H],e : I => _G.Map[J],f : K => _G.Map[L],g : M => _G.Map[N],h : O => _G.Map[P],i : Q => _G.Map[R],j : S => _G.Map[T],k : U => _G.Map[V],l : W => _G.Map[X],m : Y => _G.Map[Z],n : BA => _G.Map[BB],o : BC => _G.Map[BD],p : BE => _G.Map[BF],q : BG => _G.Map[BH]): Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG] => _G.Map[Map[B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF,BH]]
  def fmap[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10,W <: Cat11,Y <: Cat12,BA <: Cat13,BC <: Cat14,BE <: Cat15,BG <: Cat16,B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10,X <: Cat11,Z <: Cat12,BB <: Cat13,BD <: Cat14,BF <: Cat15,BH <: Cat16](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N,h : O => P,i : Q => R,j : S => T,k : U => V,l : W => X,m : Y => Z,n : BA => BB,o : BC => BD,p : BE => BF,q : BG => BH): Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG] => Map[B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF,BH] = traverse[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG,B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF,BH](applicative.Applicative.Identity)(a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q)
  def apply[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10,W <: Cat11,Y <: Cat12,BA <: Cat13,BC <: Cat14,BE <: Cat15,BG <: Cat16](_m : Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG]): View[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG] = new View(_m)
  
  class View[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10,W <: Cat11,Y <: Cat12,BA <: Cat13,BC <: Cat14,BE <: Cat15,BG <: Cat16](_m : Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG]) {
    def traverse[B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10,X <: Cat11,Z <: Cat12,BB <: Cat13,BD <: Cat14,BF <: Cat15,BH <: Cat16](_G : applicative.Applicative)(a : A => _G.Map[B],b : C => _G.Map[D],c : E => _G.Map[F],d : G => _G.Map[H],e : I => _G.Map[J],f : K => _G.Map[L],g : M => _G.Map[N],h : O => _G.Map[P],i : Q => _G.Map[R],j : S => _G.Map[T],k : U => _G.Map[V],l : W => _G.Map[X],m : Y => _G.Map[Z],n : BA => _G.Map[BB],o : BC => _G.Map[BD],p : BE => _G.Map[BF],q : BG => _G.Map[BH]):
        _G.Map[Map[B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF,BH]] =
      TraversableBounded17.this.traverse(_G)(a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q)(_m)
    def map[B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10,X <: Cat11,Z <: Cat12,BB <: Cat13,BD <: Cat14,BF <: Cat15,BH <: Cat16](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N,h : O => P,i : Q => R,j : S => T,k : U => V,l : W => X,m : Y => Z,n : BA => BB,o : BC => BD,p : BE => BF,q : BG => BH): Map[B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF,BH] =
      TraversableBounded17.this.fmap(a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q)(_m)
  }
}

trait Traversable18 extends functor.Functor18 with TraversableBounded18 {
  type Cat0 = Any;type Cat1 = Any;type Cat2 = Any;type Cat3 = Any;type Cat4 = Any;type Cat5 = Any;type Cat6 = Any;type Cat7 = Any;type Cat8 = Any;type Cat9 = Any;type Cat10 = Any;type Cat11 = Any;type Cat12 = Any;type Cat13 = Any;type Cat14 = Any;type Cat15 = Any;type Cat16 = Any;type Cat17 = Any
  type Map[+A,+B,+C,+D,+E,+F,+G,+H,+I,+J,+K,+L,+M,+N,+O,+P,+Q,+R]
}

trait TraversableBounded18 {
  type Cat0;type Cat1;type Cat2;type Cat3;type Cat4;type Cat5;type Cat6;type Cat7;type Cat8;type Cat9;type Cat10;type Cat11;type Cat12;type Cat13;type Cat14;type Cat15;type Cat16;type Cat17
  type Map[+A <: Cat0,+B <: Cat1,+C <: Cat2,+D <: Cat3,+E <: Cat4,+F <: Cat5,+G <: Cat6,+H <: Cat7,+I <: Cat8,+J <: Cat9,+K <: Cat10,+L <: Cat11,+M <: Cat12,+N <: Cat13,+O <: Cat14,+P <: Cat15,+Q <: Cat16,+R <: Cat17]
  type Range = Map[Cat0,Cat1,Cat2,Cat3,Cat4,Cat5,Cat6,Cat7,Cat8,Cat9,Cat10,Cat11,Cat12,Cat13,Cat14,Cat15,Cat16,Cat17]
  def traverse[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10,W <: Cat11,Y <: Cat12,BA <: Cat13,BC <: Cat14,BE <: Cat15,BG <: Cat16,BI <: Cat17,B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10,X <: Cat11,Z <: Cat12,BB <: Cat13,BD <: Cat14,BF <: Cat15,BH <: Cat16,BJ <: Cat17](_G : applicative.Applicative)(a : A => _G.Map[B],b : C => _G.Map[D],c : E => _G.Map[F],d : G => _G.Map[H],e : I => _G.Map[J],f : K => _G.Map[L],g : M => _G.Map[N],h : O => _G.Map[P],i : Q => _G.Map[R],j : S => _G.Map[T],k : U => _G.Map[V],l : W => _G.Map[X],m : Y => _G.Map[Z],n : BA => _G.Map[BB],o : BC => _G.Map[BD],p : BE => _G.Map[BF],q : BG => _G.Map[BH],r : BI => _G.Map[BJ]): Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG,BI] => _G.Map[Map[B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF,BH,BJ]]
  def fmap[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10,W <: Cat11,Y <: Cat12,BA <: Cat13,BC <: Cat14,BE <: Cat15,BG <: Cat16,BI <: Cat17,B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10,X <: Cat11,Z <: Cat12,BB <: Cat13,BD <: Cat14,BF <: Cat15,BH <: Cat16,BJ <: Cat17](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N,h : O => P,i : Q => R,j : S => T,k : U => V,l : W => X,m : Y => Z,n : BA => BB,o : BC => BD,p : BE => BF,q : BG => BH,r : BI => BJ): Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG,BI] => Map[B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF,BH,BJ] = traverse[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG,BI,B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF,BH,BJ](applicative.Applicative.Identity)(a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r)
  def apply[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10,W <: Cat11,Y <: Cat12,BA <: Cat13,BC <: Cat14,BE <: Cat15,BG <: Cat16,BI <: Cat17](_m : Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG,BI]): View[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG,BI] = new View(_m)
  
  class View[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10,W <: Cat11,Y <: Cat12,BA <: Cat13,BC <: Cat14,BE <: Cat15,BG <: Cat16,BI <: Cat17](_m : Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG,BI]) {
    def traverse[B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10,X <: Cat11,Z <: Cat12,BB <: Cat13,BD <: Cat14,BF <: Cat15,BH <: Cat16,BJ <: Cat17](_G : applicative.Applicative)(a : A => _G.Map[B],b : C => _G.Map[D],c : E => _G.Map[F],d : G => _G.Map[H],e : I => _G.Map[J],f : K => _G.Map[L],g : M => _G.Map[N],h : O => _G.Map[P],i : Q => _G.Map[R],j : S => _G.Map[T],k : U => _G.Map[V],l : W => _G.Map[X],m : Y => _G.Map[Z],n : BA => _G.Map[BB],o : BC => _G.Map[BD],p : BE => _G.Map[BF],q : BG => _G.Map[BH],r : BI => _G.Map[BJ]):
        _G.Map[Map[B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF,BH,BJ]] =
      TraversableBounded18.this.traverse(_G)(a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r)(_m)
    def map[B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10,X <: Cat11,Z <: Cat12,BB <: Cat13,BD <: Cat14,BF <: Cat15,BH <: Cat16,BJ <: Cat17](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N,h : O => P,i : Q => R,j : S => T,k : U => V,l : W => X,m : Y => Z,n : BA => BB,o : BC => BD,p : BE => BF,q : BG => BH,r : BI => BJ): Map[B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF,BH,BJ] =
      TraversableBounded18.this.fmap(a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r)(_m)
  }
}

trait Traversable19 extends functor.Functor19 with TraversableBounded19 {
  type Cat0 = Any;type Cat1 = Any;type Cat2 = Any;type Cat3 = Any;type Cat4 = Any;type Cat5 = Any;type Cat6 = Any;type Cat7 = Any;type Cat8 = Any;type Cat9 = Any;type Cat10 = Any;type Cat11 = Any;type Cat12 = Any;type Cat13 = Any;type Cat14 = Any;type Cat15 = Any;type Cat16 = Any;type Cat17 = Any;type Cat18 = Any
  type Map[+A,+B,+C,+D,+E,+F,+G,+H,+I,+J,+K,+L,+M,+N,+O,+P,+Q,+R,+S]
}

trait TraversableBounded19 {
  type Cat0;type Cat1;type Cat2;type Cat3;type Cat4;type Cat5;type Cat6;type Cat7;type Cat8;type Cat9;type Cat10;type Cat11;type Cat12;type Cat13;type Cat14;type Cat15;type Cat16;type Cat17;type Cat18
  type Map[+A <: Cat0,+B <: Cat1,+C <: Cat2,+D <: Cat3,+E <: Cat4,+F <: Cat5,+G <: Cat6,+H <: Cat7,+I <: Cat8,+J <: Cat9,+K <: Cat10,+L <: Cat11,+M <: Cat12,+N <: Cat13,+O <: Cat14,+P <: Cat15,+Q <: Cat16,+R <: Cat17,+S <: Cat18]
  type Range = Map[Cat0,Cat1,Cat2,Cat3,Cat4,Cat5,Cat6,Cat7,Cat8,Cat9,Cat10,Cat11,Cat12,Cat13,Cat14,Cat15,Cat16,Cat17,Cat18]
  def traverse[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10,W <: Cat11,Y <: Cat12,BA <: Cat13,BC <: Cat14,BE <: Cat15,BG <: Cat16,BI <: Cat17,BK <: Cat18,B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10,X <: Cat11,Z <: Cat12,BB <: Cat13,BD <: Cat14,BF <: Cat15,BH <: Cat16,BJ <: Cat17,BL <: Cat18](_G : applicative.Applicative)(a : A => _G.Map[B],b : C => _G.Map[D],c : E => _G.Map[F],d : G => _G.Map[H],e : I => _G.Map[J],f : K => _G.Map[L],g : M => _G.Map[N],h : O => _G.Map[P],i : Q => _G.Map[R],j : S => _G.Map[T],k : U => _G.Map[V],l : W => _G.Map[X],m : Y => _G.Map[Z],n : BA => _G.Map[BB],o : BC => _G.Map[BD],p : BE => _G.Map[BF],q : BG => _G.Map[BH],r : BI => _G.Map[BJ],s : BK => _G.Map[BL]): Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG,BI,BK] => _G.Map[Map[B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF,BH,BJ,BL]]
  def fmap[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10,W <: Cat11,Y <: Cat12,BA <: Cat13,BC <: Cat14,BE <: Cat15,BG <: Cat16,BI <: Cat17,BK <: Cat18,B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10,X <: Cat11,Z <: Cat12,BB <: Cat13,BD <: Cat14,BF <: Cat15,BH <: Cat16,BJ <: Cat17,BL <: Cat18](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N,h : O => P,i : Q => R,j : S => T,k : U => V,l : W => X,m : Y => Z,n : BA => BB,o : BC => BD,p : BE => BF,q : BG => BH,r : BI => BJ,s : BK => BL): Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG,BI,BK] => Map[B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF,BH,BJ,BL] = traverse[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG,BI,BK,B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF,BH,BJ,BL](applicative.Applicative.Identity)(a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s)
  def apply[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10,W <: Cat11,Y <: Cat12,BA <: Cat13,BC <: Cat14,BE <: Cat15,BG <: Cat16,BI <: Cat17,BK <: Cat18](_m : Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG,BI,BK]): View[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG,BI,BK] = new View(_m)
  
  class View[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10,W <: Cat11,Y <: Cat12,BA <: Cat13,BC <: Cat14,BE <: Cat15,BG <: Cat16,BI <: Cat17,BK <: Cat18](_m : Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG,BI,BK]) {
    def traverse[B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10,X <: Cat11,Z <: Cat12,BB <: Cat13,BD <: Cat14,BF <: Cat15,BH <: Cat16,BJ <: Cat17,BL <: Cat18](_G : applicative.Applicative)(a : A => _G.Map[B],b : C => _G.Map[D],c : E => _G.Map[F],d : G => _G.Map[H],e : I => _G.Map[J],f : K => _G.Map[L],g : M => _G.Map[N],h : O => _G.Map[P],i : Q => _G.Map[R],j : S => _G.Map[T],k : U => _G.Map[V],l : W => _G.Map[X],m : Y => _G.Map[Z],n : BA => _G.Map[BB],o : BC => _G.Map[BD],p : BE => _G.Map[BF],q : BG => _G.Map[BH],r : BI => _G.Map[BJ],s : BK => _G.Map[BL]):
        _G.Map[Map[B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF,BH,BJ,BL]] =
      TraversableBounded19.this.traverse(_G)(a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s)(_m)
    def map[B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10,X <: Cat11,Z <: Cat12,BB <: Cat13,BD <: Cat14,BF <: Cat15,BH <: Cat16,BJ <: Cat17,BL <: Cat18](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N,h : O => P,i : Q => R,j : S => T,k : U => V,l : W => X,m : Y => Z,n : BA => BB,o : BC => BD,p : BE => BF,q : BG => BH,r : BI => BJ,s : BK => BL): Map[B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF,BH,BJ,BL] =
      TraversableBounded19.this.fmap(a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s)(_m)
  }
}

trait Traversable20 extends functor.Functor20 with TraversableBounded20 {
  type Cat0 = Any;type Cat1 = Any;type Cat2 = Any;type Cat3 = Any;type Cat4 = Any;type Cat5 = Any;type Cat6 = Any;type Cat7 = Any;type Cat8 = Any;type Cat9 = Any;type Cat10 = Any;type Cat11 = Any;type Cat12 = Any;type Cat13 = Any;type Cat14 = Any;type Cat15 = Any;type Cat16 = Any;type Cat17 = Any;type Cat18 = Any;type Cat19 = Any
  type Map[+A,+B,+C,+D,+E,+F,+G,+H,+I,+J,+K,+L,+M,+N,+O,+P,+Q,+R,+S,+T]
}

trait TraversableBounded20 {
  type Cat0;type Cat1;type Cat2;type Cat3;type Cat4;type Cat5;type Cat6;type Cat7;type Cat8;type Cat9;type Cat10;type Cat11;type Cat12;type Cat13;type Cat14;type Cat15;type Cat16;type Cat17;type Cat18;type Cat19
  type Map[+A <: Cat0,+B <: Cat1,+C <: Cat2,+D <: Cat3,+E <: Cat4,+F <: Cat5,+G <: Cat6,+H <: Cat7,+I <: Cat8,+J <: Cat9,+K <: Cat10,+L <: Cat11,+M <: Cat12,+N <: Cat13,+O <: Cat14,+P <: Cat15,+Q <: Cat16,+R <: Cat17,+S <: Cat18,+T <: Cat19]
  type Range = Map[Cat0,Cat1,Cat2,Cat3,Cat4,Cat5,Cat6,Cat7,Cat8,Cat9,Cat10,Cat11,Cat12,Cat13,Cat14,Cat15,Cat16,Cat17,Cat18,Cat19]
  def traverse[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10,W <: Cat11,Y <: Cat12,BA <: Cat13,BC <: Cat14,BE <: Cat15,BG <: Cat16,BI <: Cat17,BK <: Cat18,BM <: Cat19,B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10,X <: Cat11,Z <: Cat12,BB <: Cat13,BD <: Cat14,BF <: Cat15,BH <: Cat16,BJ <: Cat17,BL <: Cat18,BN <: Cat19](_G : applicative.Applicative)(a : A => _G.Map[B],b : C => _G.Map[D],c : E => _G.Map[F],d : G => _G.Map[H],e : I => _G.Map[J],f : K => _G.Map[L],g : M => _G.Map[N],h : O => _G.Map[P],i : Q => _G.Map[R],j : S => _G.Map[T],k : U => _G.Map[V],l : W => _G.Map[X],m : Y => _G.Map[Z],n : BA => _G.Map[BB],o : BC => _G.Map[BD],p : BE => _G.Map[BF],q : BG => _G.Map[BH],r : BI => _G.Map[BJ],s : BK => _G.Map[BL],t : BM => _G.Map[BN]): Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG,BI,BK,BM] => _G.Map[Map[B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF,BH,BJ,BL,BN]]
  def fmap[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10,W <: Cat11,Y <: Cat12,BA <: Cat13,BC <: Cat14,BE <: Cat15,BG <: Cat16,BI <: Cat17,BK <: Cat18,BM <: Cat19,B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10,X <: Cat11,Z <: Cat12,BB <: Cat13,BD <: Cat14,BF <: Cat15,BH <: Cat16,BJ <: Cat17,BL <: Cat18,BN <: Cat19](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N,h : O => P,i : Q => R,j : S => T,k : U => V,l : W => X,m : Y => Z,n : BA => BB,o : BC => BD,p : BE => BF,q : BG => BH,r : BI => BJ,s : BK => BL,t : BM => BN): Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG,BI,BK,BM] => Map[B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF,BH,BJ,BL,BN] = traverse[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG,BI,BK,BM,B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF,BH,BJ,BL,BN](applicative.Applicative.Identity)(a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t)
  def apply[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10,W <: Cat11,Y <: Cat12,BA <: Cat13,BC <: Cat14,BE <: Cat15,BG <: Cat16,BI <: Cat17,BK <: Cat18,BM <: Cat19](_m : Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG,BI,BK,BM]): View[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG,BI,BK,BM] = new View(_m)
  
  class View[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10,W <: Cat11,Y <: Cat12,BA <: Cat13,BC <: Cat14,BE <: Cat15,BG <: Cat16,BI <: Cat17,BK <: Cat18,BM <: Cat19](_m : Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG,BI,BK,BM]) {
    def traverse[B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10,X <: Cat11,Z <: Cat12,BB <: Cat13,BD <: Cat14,BF <: Cat15,BH <: Cat16,BJ <: Cat17,BL <: Cat18,BN <: Cat19](_G : applicative.Applicative)(a : A => _G.Map[B],b : C => _G.Map[D],c : E => _G.Map[F],d : G => _G.Map[H],e : I => _G.Map[J],f : K => _G.Map[L],g : M => _G.Map[N],h : O => _G.Map[P],i : Q => _G.Map[R],j : S => _G.Map[T],k : U => _G.Map[V],l : W => _G.Map[X],m : Y => _G.Map[Z],n : BA => _G.Map[BB],o : BC => _G.Map[BD],p : BE => _G.Map[BF],q : BG => _G.Map[BH],r : BI => _G.Map[BJ],s : BK => _G.Map[BL],t : BM => _G.Map[BN]):
        _G.Map[Map[B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF,BH,BJ,BL,BN]] =
      TraversableBounded20.this.traverse(_G)(a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t)(_m)
    def map[B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10,X <: Cat11,Z <: Cat12,BB <: Cat13,BD <: Cat14,BF <: Cat15,BH <: Cat16,BJ <: Cat17,BL <: Cat18,BN <: Cat19](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N,h : O => P,i : Q => R,j : S => T,k : U => V,l : W => X,m : Y => Z,n : BA => BB,o : BC => BD,p : BE => BF,q : BG => BH,r : BI => BJ,s : BK => BL,t : BM => BN): Map[B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF,BH,BJ,BL,BN] =
      TraversableBounded20.this.fmap(a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t)(_m)
  }
}

trait Traversable21 extends functor.Functor21 with TraversableBounded21 {
  type Cat0 = Any;type Cat1 = Any;type Cat2 = Any;type Cat3 = Any;type Cat4 = Any;type Cat5 = Any;type Cat6 = Any;type Cat7 = Any;type Cat8 = Any;type Cat9 = Any;type Cat10 = Any;type Cat11 = Any;type Cat12 = Any;type Cat13 = Any;type Cat14 = Any;type Cat15 = Any;type Cat16 = Any;type Cat17 = Any;type Cat18 = Any;type Cat19 = Any;type Cat20 = Any
  type Map[+A,+B,+C,+D,+E,+F,+G,+H,+I,+J,+K,+L,+M,+N,+O,+P,+Q,+R,+S,+T,+U]
}

trait TraversableBounded21 {
  type Cat0;type Cat1;type Cat2;type Cat3;type Cat4;type Cat5;type Cat6;type Cat7;type Cat8;type Cat9;type Cat10;type Cat11;type Cat12;type Cat13;type Cat14;type Cat15;type Cat16;type Cat17;type Cat18;type Cat19;type Cat20
  type Map[+A <: Cat0,+B <: Cat1,+C <: Cat2,+D <: Cat3,+E <: Cat4,+F <: Cat5,+G <: Cat6,+H <: Cat7,+I <: Cat8,+J <: Cat9,+K <: Cat10,+L <: Cat11,+M <: Cat12,+N <: Cat13,+O <: Cat14,+P <: Cat15,+Q <: Cat16,+R <: Cat17,+S <: Cat18,+T <: Cat19,+U <: Cat20]
  type Range = Map[Cat0,Cat1,Cat2,Cat3,Cat4,Cat5,Cat6,Cat7,Cat8,Cat9,Cat10,Cat11,Cat12,Cat13,Cat14,Cat15,Cat16,Cat17,Cat18,Cat19,Cat20]
  def traverse[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10,W <: Cat11,Y <: Cat12,BA <: Cat13,BC <: Cat14,BE <: Cat15,BG <: Cat16,BI <: Cat17,BK <: Cat18,BM <: Cat19,BO <: Cat20,B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10,X <: Cat11,Z <: Cat12,BB <: Cat13,BD <: Cat14,BF <: Cat15,BH <: Cat16,BJ <: Cat17,BL <: Cat18,BN <: Cat19,BP <: Cat20](_G : applicative.Applicative)(a : A => _G.Map[B],b : C => _G.Map[D],c : E => _G.Map[F],d : G => _G.Map[H],e : I => _G.Map[J],f : K => _G.Map[L],g : M => _G.Map[N],h : O => _G.Map[P],i : Q => _G.Map[R],j : S => _G.Map[T],k : U => _G.Map[V],l : W => _G.Map[X],m : Y => _G.Map[Z],n : BA => _G.Map[BB],o : BC => _G.Map[BD],p : BE => _G.Map[BF],q : BG => _G.Map[BH],r : BI => _G.Map[BJ],s : BK => _G.Map[BL],t : BM => _G.Map[BN],u : BO => _G.Map[BP]): Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG,BI,BK,BM,BO] => _G.Map[Map[B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF,BH,BJ,BL,BN,BP]]
  def fmap[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10,W <: Cat11,Y <: Cat12,BA <: Cat13,BC <: Cat14,BE <: Cat15,BG <: Cat16,BI <: Cat17,BK <: Cat18,BM <: Cat19,BO <: Cat20,B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10,X <: Cat11,Z <: Cat12,BB <: Cat13,BD <: Cat14,BF <: Cat15,BH <: Cat16,BJ <: Cat17,BL <: Cat18,BN <: Cat19,BP <: Cat20](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N,h : O => P,i : Q => R,j : S => T,k : U => V,l : W => X,m : Y => Z,n : BA => BB,o : BC => BD,p : BE => BF,q : BG => BH,r : BI => BJ,s : BK => BL,t : BM => BN,u : BO => BP): Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG,BI,BK,BM,BO] => Map[B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF,BH,BJ,BL,BN,BP] = traverse[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG,BI,BK,BM,BO,B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF,BH,BJ,BL,BN,BP](applicative.Applicative.Identity)(a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u)
  def apply[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10,W <: Cat11,Y <: Cat12,BA <: Cat13,BC <: Cat14,BE <: Cat15,BG <: Cat16,BI <: Cat17,BK <: Cat18,BM <: Cat19,BO <: Cat20](_m : Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG,BI,BK,BM,BO]): View[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG,BI,BK,BM,BO] = new View(_m)
  
  class View[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10,W <: Cat11,Y <: Cat12,BA <: Cat13,BC <: Cat14,BE <: Cat15,BG <: Cat16,BI <: Cat17,BK <: Cat18,BM <: Cat19,BO <: Cat20](_m : Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG,BI,BK,BM,BO]) {
    def traverse[B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10,X <: Cat11,Z <: Cat12,BB <: Cat13,BD <: Cat14,BF <: Cat15,BH <: Cat16,BJ <: Cat17,BL <: Cat18,BN <: Cat19,BP <: Cat20](_G : applicative.Applicative)(a : A => _G.Map[B],b : C => _G.Map[D],c : E => _G.Map[F],d : G => _G.Map[H],e : I => _G.Map[J],f : K => _G.Map[L],g : M => _G.Map[N],h : O => _G.Map[P],i : Q => _G.Map[R],j : S => _G.Map[T],k : U => _G.Map[V],l : W => _G.Map[X],m : Y => _G.Map[Z],n : BA => _G.Map[BB],o : BC => _G.Map[BD],p : BE => _G.Map[BF],q : BG => _G.Map[BH],r : BI => _G.Map[BJ],s : BK => _G.Map[BL],t : BM => _G.Map[BN],u : BO => _G.Map[BP]):
        _G.Map[Map[B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF,BH,BJ,BL,BN,BP]] =
      TraversableBounded21.this.traverse(_G)(a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u)(_m)
    def map[B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10,X <: Cat11,Z <: Cat12,BB <: Cat13,BD <: Cat14,BF <: Cat15,BH <: Cat16,BJ <: Cat17,BL <: Cat18,BN <: Cat19,BP <: Cat20](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N,h : O => P,i : Q => R,j : S => T,k : U => V,l : W => X,m : Y => Z,n : BA => BB,o : BC => BD,p : BE => BF,q : BG => BH,r : BI => BJ,s : BK => BL,t : BM => BN,u : BO => BP): Map[B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF,BH,BJ,BL,BN,BP] =
      TraversableBounded21.this.fmap(a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u)(_m)
  }
}

trait Traversable22 extends functor.Functor22 with TraversableBounded22 {
  type Cat0 = Any;type Cat1 = Any;type Cat2 = Any;type Cat3 = Any;type Cat4 = Any;type Cat5 = Any;type Cat6 = Any;type Cat7 = Any;type Cat8 = Any;type Cat9 = Any;type Cat10 = Any;type Cat11 = Any;type Cat12 = Any;type Cat13 = Any;type Cat14 = Any;type Cat15 = Any;type Cat16 = Any;type Cat17 = Any;type Cat18 = Any;type Cat19 = Any;type Cat20 = Any;type Cat21 = Any
  type Map[+A,+B,+C,+D,+E,+F,+G,+H,+I,+J,+K,+L,+M,+N,+O,+P,+Q,+R,+S,+T,+U,+V]
}

trait TraversableBounded22 {
  type Cat0;type Cat1;type Cat2;type Cat3;type Cat4;type Cat5;type Cat6;type Cat7;type Cat8;type Cat9;type Cat10;type Cat11;type Cat12;type Cat13;type Cat14;type Cat15;type Cat16;type Cat17;type Cat18;type Cat19;type Cat20;type Cat21
  type Map[+A <: Cat0,+B <: Cat1,+C <: Cat2,+D <: Cat3,+E <: Cat4,+F <: Cat5,+G <: Cat6,+H <: Cat7,+I <: Cat8,+J <: Cat9,+K <: Cat10,+L <: Cat11,+M <: Cat12,+N <: Cat13,+O <: Cat14,+P <: Cat15,+Q <: Cat16,+R <: Cat17,+S <: Cat18,+T <: Cat19,+U <: Cat20,+V <: Cat21]
  type Range = Map[Cat0,Cat1,Cat2,Cat3,Cat4,Cat5,Cat6,Cat7,Cat8,Cat9,Cat10,Cat11,Cat12,Cat13,Cat14,Cat15,Cat16,Cat17,Cat18,Cat19,Cat20,Cat21]
  def traverse[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10,W <: Cat11,Y <: Cat12,BA <: Cat13,BC <: Cat14,BE <: Cat15,BG <: Cat16,BI <: Cat17,BK <: Cat18,BM <: Cat19,BO <: Cat20,BQ <: Cat21,B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10,X <: Cat11,Z <: Cat12,BB <: Cat13,BD <: Cat14,BF <: Cat15,BH <: Cat16,BJ <: Cat17,BL <: Cat18,BN <: Cat19,BP <: Cat20,BR <: Cat21](_G : applicative.Applicative)(a : A => _G.Map[B],b : C => _G.Map[D],c : E => _G.Map[F],d : G => _G.Map[H],e : I => _G.Map[J],f : K => _G.Map[L],g : M => _G.Map[N],h : O => _G.Map[P],i : Q => _G.Map[R],j : S => _G.Map[T],k : U => _G.Map[V],l : W => _G.Map[X],m : Y => _G.Map[Z],n : BA => _G.Map[BB],o : BC => _G.Map[BD],p : BE => _G.Map[BF],q : BG => _G.Map[BH],r : BI => _G.Map[BJ],s : BK => _G.Map[BL],t : BM => _G.Map[BN],u : BO => _G.Map[BP],v : BQ => _G.Map[BR]): Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG,BI,BK,BM,BO,BQ] => _G.Map[Map[B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF,BH,BJ,BL,BN,BP,BR]]
  def fmap[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10,W <: Cat11,Y <: Cat12,BA <: Cat13,BC <: Cat14,BE <: Cat15,BG <: Cat16,BI <: Cat17,BK <: Cat18,BM <: Cat19,BO <: Cat20,BQ <: Cat21,B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10,X <: Cat11,Z <: Cat12,BB <: Cat13,BD <: Cat14,BF <: Cat15,BH <: Cat16,BJ <: Cat17,BL <: Cat18,BN <: Cat19,BP <: Cat20,BR <: Cat21](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N,h : O => P,i : Q => R,j : S => T,k : U => V,l : W => X,m : Y => Z,n : BA => BB,o : BC => BD,p : BE => BF,q : BG => BH,r : BI => BJ,s : BK => BL,t : BM => BN,u : BO => BP,v : BQ => BR): Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG,BI,BK,BM,BO,BQ] => Map[B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF,BH,BJ,BL,BN,BP,BR] = traverse[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG,BI,BK,BM,BO,BQ,B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF,BH,BJ,BL,BN,BP,BR](applicative.Applicative.Identity)(a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v)
  def apply[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10,W <: Cat11,Y <: Cat12,BA <: Cat13,BC <: Cat14,BE <: Cat15,BG <: Cat16,BI <: Cat17,BK <: Cat18,BM <: Cat19,BO <: Cat20,BQ <: Cat21](_m : Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG,BI,BK,BM,BO,BQ]): View[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG,BI,BK,BM,BO,BQ] = new View(_m)
  
  class View[A <: Cat0,C <: Cat1,E <: Cat2,G <: Cat3,I <: Cat4,K <: Cat5,M <: Cat6,O <: Cat7,Q <: Cat8,S <: Cat9,U <: Cat10,W <: Cat11,Y <: Cat12,BA <: Cat13,BC <: Cat14,BE <: Cat15,BG <: Cat16,BI <: Cat17,BK <: Cat18,BM <: Cat19,BO <: Cat20,BQ <: Cat21](_m : Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG,BI,BK,BM,BO,BQ]) {
    def traverse[B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10,X <: Cat11,Z <: Cat12,BB <: Cat13,BD <: Cat14,BF <: Cat15,BH <: Cat16,BJ <: Cat17,BL <: Cat18,BN <: Cat19,BP <: Cat20,BR <: Cat21](_G : applicative.Applicative)(a : A => _G.Map[B],b : C => _G.Map[D],c : E => _G.Map[F],d : G => _G.Map[H],e : I => _G.Map[J],f : K => _G.Map[L],g : M => _G.Map[N],h : O => _G.Map[P],i : Q => _G.Map[R],j : S => _G.Map[T],k : U => _G.Map[V],l : W => _G.Map[X],m : Y => _G.Map[Z],n : BA => _G.Map[BB],o : BC => _G.Map[BD],p : BE => _G.Map[BF],q : BG => _G.Map[BH],r : BI => _G.Map[BJ],s : BK => _G.Map[BL],t : BM => _G.Map[BN],u : BO => _G.Map[BP],v : BQ => _G.Map[BR]):
        _G.Map[Map[B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF,BH,BJ,BL,BN,BP,BR]] =
      TraversableBounded22.this.traverse(_G)(a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v)(_m)
    def map[B <: Cat0,D <: Cat1,F <: Cat2,H <: Cat3,J <: Cat4,L <: Cat5,N <: Cat6,P <: Cat7,R <: Cat8,T <: Cat9,V <: Cat10,X <: Cat11,Z <: Cat12,BB <: Cat13,BD <: Cat14,BF <: Cat15,BH <: Cat16,BJ <: Cat17,BL <: Cat18,BN <: Cat19,BP <: Cat20,BR <: Cat21](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N,h : O => P,i : Q => R,j : S => T,k : U => V,l : W => X,m : Y => Z,n : BA => BB,o : BC => BD,p : BE => BF,q : BG => BH,r : BI => BJ,s : BK => BL,t : BM => BN,u : BO => BP,v : BQ => BR): Map[B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF,BH,BJ,BL,BN,BP,BR] =
      TraversableBounded22.this.fmap(a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v)(_m)
  }
}

