/** Encoding mutually recursive datatypes as mu-types */

import nominal.functors._
import nominal.lib._

object Mutual {
  // tree+forest: easy.
  @data def TREE[A, B] = TreeT { Empty ; Node(label = A, children = B) }
  @data def FOREST[A, B] = ForestT { Nil ; Cons(head = A, tail = B) }

  @functor def TreeF[T, F] = TreeT { Empty ; Node(label = Int, children = F) }
  @functor def ForestF[T, F] = ForestT { Nil ; Cons(head = T, tail = F) }

  @synonym def Tree = Fix(tree => TreeF apply (
    tree, Fix(forest => ForestF apply (tree, forest) ))
  )

  @synonym def Forest = Fix(forest => ForestF apply (
    Fix(tree => TreeF apply (tree, forest)), forest
  ))

  // each type depends on the other two.
  @data def AX[A,B,C] = AT { NA ; RA(_1 = A, _2 = B, _3 = C) }
  @data def BX[A,B,C] = BT { NB ; RB(_1 = A, _2 = B, _3 = C) }
  @data def CX[A,B,C] = CT { NC ; RC(_1 = A, _2 = B, _3 = C) }

  @functor def AXF[A,B,C] = RA(_1 = A, _2 = B, _3 = C)
  @functor def BXF[A,B,C] = RB(_1 = A, _2 = B, _3 = C)
  @functor def CXF[A,B,C] = RC(_1 = A, _2 = B, _3 = C)

  @synonym def A = Fix(a => Fix(b => Fix(c => AT {
    NA
    RA(_1 = a, _2 = BXF apply (a, b, c), _3 = CXF apply (a, b, c))
  })))

  @synonym def B = Fix(d => Fix(e => Fix(f => BT {
    NB
    RB(_1 = AXF apply (d, e, f), _2 = e, _3 = CXF apply (d, e, f))
  })))

  @synonym def C = Fix(g => Fix(h => Fix(i => CT {
    NC
    RC(_1 = AXF apply (g, h, i), _2 = BXF apply (g, h, i), _3 = i)
  })))

  // BUG: coerce fails

  //val a0: A = coerce { NA }
  //val b0: B = coerce { NB }
  //val c0: C = coerce { NC }

  //val a1: A = coerce { RA(a0, b0, c0) }
  //val b1: B = coerce { RB(a0, b0, c0) }
  //val c1: C = coerce { RC(a0, b0, c0) }
}
