package fos

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input._

/** This object implements a parser and evaluator for the
 *  untyped lambda calculus found in Chapter 5 of
 *  the TAPL book.
 */
object Untyped extends StandardTokenParsers {
  lexical.delimiters ++= List("(", ")", "\\", ".")
  import lexical.Identifier

  /** t ::= x
          | '\' x '.' t
          | t t
          | '(' t ')'
   */
  def term: Parser[Term] =
    rep1(singleTerm) ^^ {case termlist => processTermList(termlist.reverse)}
  def singleTerm: Parser[Term] =
  ( ident ^^ {case e => Var(e)} |
    ("\\" ~> ident) ~ ("." ~> term) ^^ {case vr ~ t => Abs(vr, t)} |
    "(" ~> term <~ ")"
    )
  def processTermList(tl: List[Term]): Term = {
    if (tl.tail.isEmpty) tl.head
    else App(processTermList(tl.tail), tl.head)
  }

  /** <p>
   *    Alpha conversion: term <code>t</code> should be a lambda abstraction
   *    <code>\x. t</code>.
   *  </p>
   *  <p>
   *    All free occurences of <code>x</code> inside term <code>t/code>
   *    will be renamed to a unique name.
   *  </p>
   *
   *  @param t the given lambda abstraction.
   *  @return  the transformed term with bound variables renamed.
   */
  var randomnum = 100
  def alpha(t: Term): Term =
    t match {
      case Abs(v, t0) => randomnum += 1; Abs(v + randomnum.toString, processTerm(t0, v))
      case _ => t
    }
    def processTerm(t: Term, v: String): Term = {
      t match {
        case App(t1, t2) => App(processTerm(t1, v), processTerm(t2, v))
        case Abs(vr, t0) if (vr != v) => Abs(vr, processTerm(t0, v))
        case Abs(vr, t0) if (vr == v) => t
        case Var(vr) if (vr == v) => Var(vr + randomnum.toString)
        case _ => t
      }
    }

  /** Straight forward substitution method
   *  (see definition 5.3.5 in TAPL book).
   *  [x -> s]t
   *
   *  @param t the term in which we perform substitution
   *  @param x the variable name
   *  @param s the term we replace x with
   *  @return  ...
   */
  def subst(t: Term, x: String, s: Term): Term =
    t match {
      case Var(vr) if (vr == x) => s
      case Var(vr) if (vr != x) => t
      case Abs(vr, t0) if (vr == x) => t
      case Abs(vr, t0) if (vr != x && !(FV(s).exists((v: String) => v == vr))) => Abs(vr, subst(t0, x, s))
      case Abs(vr, t0) if (vr != x && FV(s).exists((v: String) => v == vr)) => subst(alpha(t), x, s)
      case App(t1, t2) => App(subst(t1, x, s), subst(t2, x, s))
      case _ => t
    }
    //Free Variable test
  def FV(t: Term): List[String] =
    t match {
      case Var(vr) => List(vr)
      case Abs(vr, t0) => FV(t0).filter((v: String) => v != vr)
      case App(t1, t2) => FV(t1):::FV(t2)
    }

  /** Term 't' does not match any reduction rule. */
  case class NoReductionPossible(t: Term) extends Exception(t.toString)

  /** Normal order (leftmost, outermost redex first).
   *
   * example: let id = (\x. x) ==> (\x. x) ((\x. x) (\z. (\x. x) z))
   *   id (id (\z. id z))
   *   => id (\z. id z)
   *   => \z. id z
   *   => \z. z
   *
   *  in (e1 e2), 
   *  @param t the initial term
   *  @return  the reduced term
   */
  def reduceNormalOrder(t: Term): Term =
    t match {
      case App(Abs(vr, t0), t1) => subst(t0, vr, t1)
      case App(t1, t2) if(reduces(t1))=> App(reduceNormalOrder(t1), t2)
      case App(Var(vr), t1) => App(Var(vr), reduceNormalOrder(t1))
      case Abs(vr, t0) => Abs(vr, reduceNormalOrder(t0))
      case _ => throw new NoReductionPossible(t)
    }
  def reduces(t: Term) : Boolean =
  	t match {
  		case Abs(vr, t0) => false
  		case Var(vr) => false
  		case _ => t != reduceNormalOrder(t)
  	}

    // let id = (\x. x) ===>
    // id (id (\z. id z))
    // => (id (\z. id z))
    // => (\z. id z)
    // 
    // in (e1 e2), if e1 is a value, we evaluate e2 until it is a value(if it can be), 
    // else, we evaluate e1 until it is a value(if it can be),
    // then we do the beta reduction.
    // 
  /** Call by value reducer. */
  def reduceCallByValue(t: Term): Term =
    t match {
      case App(Abs(vr, t0), t1) if(reducesToValue(t1) && !isValue(t1)) => App(Abs(vr, t0), reduceCallByValue(t1))
      case App(t1, t2) if(reducesToValue(t1) && !isValue(t1)) => App(reduceCallByValue(t1), t2)
      case App(Abs(vr, t0), t1) if(isValue(t1)) => subst(t0, vr, t1)
      case _ => throw new NoReductionPossible(t)
    }
  def reducesToValue(t: Term): Boolean =
    t match {
      case Abs(vr, t0) => true
      case Var(vr) => false
      case _ => reducesToValue(reduceCallByValue(t))
    }
  def isValue(t: Term): Boolean =
    t match {
      case Abs(vr, t0) => true
      case _ => false
    }

  /** Returns a stream of terms, each being one step of reduction.
   *
   *  @param t      the initial term
   *  @param reduce the method that reduces a term by one step.
   *  @return       the stream of terms representing the big reduction.
   */
  def path(t: Term, reduce: Term => Term): Stream[Term] =
    try {
      var t1 = reduce(t)
      Stream.cons(t, path(t1, reduce))
    } catch {
      case NoReductionPossible(_) =>
        Stream.cons(t, Stream.empty)
    }

  def main(args: Array[String]): Unit = {
    val stdin = new java.io.BufferedReader(new java.io.InputStreamReader(System.in))
    val tokens = new lexical.Scanner(stdin.readLine())
    phrase(term)(tokens) match {
      case Success(trees, _) =>
        println("normal order: ")
        for (t <- path(trees, reduceNormalOrder))
          println(t)
        println("call-by-value: ")
        for (t <- path(trees, reduceCallByValue))
          println(t)

      case e =>
        println(e)
    }
  }
}
