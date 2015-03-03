package creg
package util

// cross-stage persistance
//
// based on:
// http://stackoverflow.com/a/8887244

import java.io._
import org.apache.commons.codec.binary.Base64
import scala.reflect.macros.blackbox.Context
import scala.reflect.runtime.universe.{ TypeTag => Tag }

trait Persist {
  def persist[T <: Serializable : Tag](c: Context)(obj: T): c.Tree = {
    import c.universe._
    val bo = new ByteArrayOutputStream
    val so = new ObjectOutputStream(bo)
    val q"??? : $tpe" = c parse s"??? : ${implicitly[Tag[T]].tpe}"
    so writeObject obj
    so.flush
    // without base64 encoding, get java.io.StreamCorruptedException due to UTF-8 encoding
    val string = Base64 encodeBase64 bo.toByteArray
    q"""{
      import java.io._
      import org.apache.commons.codec.binary.Base64
      val b = Base64 decodeBase64 $string
      val bi = new ByteArrayInputStream(b)
      val si = new ObjectInputStream(bi)
      si.readObject.asInstanceOf[$tpe]
    }"""
  }
}
