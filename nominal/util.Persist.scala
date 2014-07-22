package nominal
package util

// cross-stage persistance
//
// based on:
// http://stackoverflow.com/a/8887244

import java.io._
import org.apache.commons.codec.binary.Base64
import scala.reflect.macros.blackbox.Context

trait Persist {
  def persist(c: Context)(obj: Serializable): c.Tree = {
    import c.universe._
    val bo = new ByteArrayOutputStream
    val so = new ObjectOutputStream(bo)
    so writeObject obj
    so.flush
    // without base64 encoding, get java.io.StreamCorruptedException due to UTF-8 encoding
    val string = Base64 encodeBase64 bo.toByteArray
    val stringExpr = c.Expr[String](q"$string")
    reify({
      import java.io._
      import org.apache.commons.codec.binary.Base64
      val b = Base64 decodeBase64 stringExpr.splice
      val bi = new ByteArrayInputStream(b)
      val si = new ObjectInputStream(bi)
      si.readObject
    }).tree
  }
}
