package creg
package lib
import language.higherKinds

trait Functor {
  type Map[+A]
  def fmap[A,B](a : A => B): Map[A] => Map[B]
}

trait Functor2 {
  type Map[+A,+B]
  def fmap[A,C,B,D](a : A => B,b : C => D): Map[A,C] => Map[B,D]
}

trait Functor3 {
  type Map[+A,+B,+C]
  def fmap[A,C,E,B,D,F](a : A => B,b : C => D,c : E => F): Map[A,C,E] => Map[B,D,F]
}

trait Functor4 {
  type Map[+A,+B,+C,+D]
  def fmap[A,C,E,G,B,D,F,H](a : A => B,b : C => D,c : E => F,d : G => H): Map[A,C,E,G] => Map[B,D,F,H]
}

trait Functor5 {
  type Map[+A,+B,+C,+D,+E]
  def fmap[A,C,E,G,I,B,D,F,H,J](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J): Map[A,C,E,G,I] => Map[B,D,F,H,J]
}

trait Functor6 {
  type Map[+A,+B,+C,+D,+E,+F]
  def fmap[A,C,E,G,I,K,B,D,F,H,J,L](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L): Map[A,C,E,G,I,K] => Map[B,D,F,H,J,L]
}

trait Functor7 {
  type Map[+A,+B,+C,+D,+E,+F,+G]
  def fmap[A,C,E,G,I,K,M,B,D,F,H,J,L,N](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N): Map[A,C,E,G,I,K,M] => Map[B,D,F,H,J,L,N]
}

trait Functor8 {
  type Map[+A,+B,+C,+D,+E,+F,+G,+H]
  def fmap[A,C,E,G,I,K,M,O,B,D,F,H,J,L,N,P](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N,h : O => P): Map[A,C,E,G,I,K,M,O] => Map[B,D,F,H,J,L,N,P]
}

trait Functor9 {
  type Map[+A,+B,+C,+D,+E,+F,+G,+H,+I]
  def fmap[A,C,E,G,I,K,M,O,Q,B,D,F,H,J,L,N,P,R](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N,h : O => P,i : Q => R): Map[A,C,E,G,I,K,M,O,Q] => Map[B,D,F,H,J,L,N,P,R]
}

trait Functor10 {
  type Map[+A,+B,+C,+D,+E,+F,+G,+H,+I,+J]
  def fmap[A,C,E,G,I,K,M,O,Q,S,B,D,F,H,J,L,N,P,R,T](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N,h : O => P,i : Q => R,j : S => T): Map[A,C,E,G,I,K,M,O,Q,S] => Map[B,D,F,H,J,L,N,P,R,T]
}

trait Functor11 {
  type Map[+A,+B,+C,+D,+E,+F,+G,+H,+I,+J,+K]
  def fmap[A,C,E,G,I,K,M,O,Q,S,U,B,D,F,H,J,L,N,P,R,T,V](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N,h : O => P,i : Q => R,j : S => T,k : U => V): Map[A,C,E,G,I,K,M,O,Q,S,U] => Map[B,D,F,H,J,L,N,P,R,T,V]
}

trait Functor12 {
  type Map[+A,+B,+C,+D,+E,+F,+G,+H,+I,+J,+K,+L]
  def fmap[A,C,E,G,I,K,M,O,Q,S,U,W,B,D,F,H,J,L,N,P,R,T,V,X](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N,h : O => P,i : Q => R,j : S => T,k : U => V,l : W => X): Map[A,C,E,G,I,K,M,O,Q,S,U,W] => Map[B,D,F,H,J,L,N,P,R,T,V,X]
}

trait Functor13 {
  type Map[+A,+B,+C,+D,+E,+F,+G,+H,+I,+J,+K,+L,+M]
  def fmap[A,C,E,G,I,K,M,O,Q,S,U,W,Y,B,D,F,H,J,L,N,P,R,T,V,X,Z](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N,h : O => P,i : Q => R,j : S => T,k : U => V,l : W => X,m : Y => Z): Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y] => Map[B,D,F,H,J,L,N,P,R,T,V,X,Z]
}

trait Functor14 {
  type Map[+A,+B,+C,+D,+E,+F,+G,+H,+I,+J,+K,+L,+M,+N]
  def fmap[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,B,D,F,H,J,L,N,P,R,T,V,X,Z,BB](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N,h : O => P,i : Q => R,j : S => T,k : U => V,l : W => X,m : Y => Z,n : BA => BB): Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA] => Map[B,D,F,H,J,L,N,P,R,T,V,X,Z,BB]
}

trait Functor15 {
  type Map[+A,+B,+C,+D,+E,+F,+G,+H,+I,+J,+K,+L,+M,+N,+O]
  def fmap[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N,h : O => P,i : Q => R,j : S => T,k : U => V,l : W => X,m : Y => Z,n : BA => BB,o : BC => BD): Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC] => Map[B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD]
}

trait Functor16 {
  type Map[+A,+B,+C,+D,+E,+F,+G,+H,+I,+J,+K,+L,+M,+N,+O,+P]
  def fmap[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N,h : O => P,i : Q => R,j : S => T,k : U => V,l : W => X,m : Y => Z,n : BA => BB,o : BC => BD,p : BE => BF): Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE] => Map[B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF]
}

trait Functor17 {
  type Map[+A,+B,+C,+D,+E,+F,+G,+H,+I,+J,+K,+L,+M,+N,+O,+P,+Q]
  def fmap[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG,B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF,BH](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N,h : O => P,i : Q => R,j : S => T,k : U => V,l : W => X,m : Y => Z,n : BA => BB,o : BC => BD,p : BE => BF,q : BG => BH): Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG] => Map[B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF,BH]
}

trait Functor18 {
  type Map[+A,+B,+C,+D,+E,+F,+G,+H,+I,+J,+K,+L,+M,+N,+O,+P,+Q,+R]
  def fmap[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG,BI,B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF,BH,BJ](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N,h : O => P,i : Q => R,j : S => T,k : U => V,l : W => X,m : Y => Z,n : BA => BB,o : BC => BD,p : BE => BF,q : BG => BH,r : BI => BJ): Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG,BI] => Map[B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF,BH,BJ]
}

trait Functor19 {
  type Map[+A,+B,+C,+D,+E,+F,+G,+H,+I,+J,+K,+L,+M,+N,+O,+P,+Q,+R,+S]
  def fmap[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG,BI,BK,B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF,BH,BJ,BL](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N,h : O => P,i : Q => R,j : S => T,k : U => V,l : W => X,m : Y => Z,n : BA => BB,o : BC => BD,p : BE => BF,q : BG => BH,r : BI => BJ,s : BK => BL): Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG,BI,BK] => Map[B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF,BH,BJ,BL]
}

trait Functor20 {
  type Map[+A,+B,+C,+D,+E,+F,+G,+H,+I,+J,+K,+L,+M,+N,+O,+P,+Q,+R,+S,+T]
  def fmap[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG,BI,BK,BM,B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF,BH,BJ,BL,BN](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N,h : O => P,i : Q => R,j : S => T,k : U => V,l : W => X,m : Y => Z,n : BA => BB,o : BC => BD,p : BE => BF,q : BG => BH,r : BI => BJ,s : BK => BL,t : BM => BN): Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG,BI,BK,BM] => Map[B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF,BH,BJ,BL,BN]
}

trait Functor21 {
  type Map[+A,+B,+C,+D,+E,+F,+G,+H,+I,+J,+K,+L,+M,+N,+O,+P,+Q,+R,+S,+T,+U]
  def fmap[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG,BI,BK,BM,BO,B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF,BH,BJ,BL,BN,BP](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N,h : O => P,i : Q => R,j : S => T,k : U => V,l : W => X,m : Y => Z,n : BA => BB,o : BC => BD,p : BE => BF,q : BG => BH,r : BI => BJ,s : BK => BL,t : BM => BN,u : BO => BP): Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG,BI,BK,BM,BO] => Map[B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF,BH,BJ,BL,BN,BP]
}

trait Functor22 {
  type Map[+A,+B,+C,+D,+E,+F,+G,+H,+I,+J,+K,+L,+M,+N,+O,+P,+Q,+R,+S,+T,+U,+V]
  def fmap[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG,BI,BK,BM,BO,BQ,B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF,BH,BJ,BL,BN,BP,BR](a : A => B,b : C => D,c : E => F,d : G => H,e : I => J,f : K => L,g : M => N,h : O => P,i : Q => R,j : S => T,k : U => V,l : W => X,m : Y => Z,n : BA => BB,o : BC => BD,p : BE => BF,q : BG => BH,r : BI => BJ,s : BK => BL,t : BM => BN,u : BO => BP,v : BQ => BR): Map[A,C,E,G,I,K,M,O,Q,S,U,W,Y,BA,BC,BE,BG,BI,BK,BM,BO,BQ] => Map[B,D,F,H,J,L,N,P,R,T,V,X,Z,BB,BD,BF,BH,BJ,BL,BN,BP,BR]
}

