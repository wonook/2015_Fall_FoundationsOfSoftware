package fos

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input._

/** This object implements a parser and evaluator for the NB
 *  language of booleans and numbers found in Chapter 3 of
 *  the TAPL book.
 */
object Arithmetic extends StandardTokenParsers {
  lexical.reserved ++= List("true", "false", "0", "if", "then", "else", "succ", "pred", "iszero")

  import lexical.NumericLit

  /** term ::= 'true'
             | 'false'
             | 'if' term 'then' term 'else' term
             | '0'
             | 'succ' term
             | 'pred' term
             | 'iszero' term
   */
  def term: Parser[Term] =
    ( "true" ^^ (t => True) |
      "false" ^^ (t => False) |
      ("if" ~> term) ~ ("then" ~> term) ~ ("else" ~> term) ^^ {case t1 ~ t2 ~ t3 => If(t1, t2, t3)} |
      numericValue |
      "succ" ~> term ^^ {case t => Succ(t)} |
      "pred" ~> term ^^ {case t => Pred(t)} |
      "iszero" ~> term ^^ {case t => IsZero(t)}
      )

  def numericValue: Parser[Term] =
    ( numericLit ^^ {case n => transformNv(n.toInt) } |
      "succ" ~> numericValue ^^ {case n => Succ(n)}
      )

  def transformNv(n: Int): Term = {
    n match {
      case 0 => Zero
      case t if t != 0 => Succ(transformNv(t - 1))
    }
  }

  case class NoReductionPossible(t: Term) extends Exception(t.toString)

  /** Return a list of at most n terms, each being one step of reduction. */
  def path(t: Term, n: Int = 64): List[Term] =
    if (n <= 0) Nil
    else
      t :: {
        try {
          path(reduce(t), n - 1)
        } catch {
          case NoReductionPossible(t1) =>
            Nil
        }
      }

  /** Perform one step of reduction, when possible.
   *  If reduction is not possible NoReductionPossible exception
   *  with corresponding irreducible term should be thrown.
   */
  def reduce(t: Term): Term = {
    t match {
      case If(True, t1, t2) => t1
      case If(False, t1, t2) => t2
      case IsZero(Zero) => True
      case IsZero(Succ(nv)) if (isNv(nv)) => False
      case Pred(Zero) => Zero
      case Pred(Succ(nv)) if (isNv(nv)) => nv
      case If(t1, t2, t3) => val v = reduce(t1); If(v, t2, t3)
      case IsZero(t) => val v = reduce(t); IsZero(v)
      case Pred(t) => val v = reduce(t); Pred(v)
      case Succ(t) => val v = reduce(t); Succ(v)
      case _ => throw NoReductionPossible(t)
    }
  }

  def isNv(nv: Term): Boolean = {
    nv match {
      case Zero => true
      case Succ(t) => isNv(t)
      case _ => false
    }
  }

  case class TermIsStuck(t: Term) extends Exception(t.toString)

  /** Perform big step evaluation (result is always a value.)
   *  If evaluation is not possible TermIsStuck exception with
   *  corresponding inner irreducible term should be thrown.
   */
  def eval(t: Term): Term = {
    t match {
      case v if (isV(v)) => v
      case If(t1, t2, t3) => eval(t1) match {
        case True if isV(eval(t2)) => eval(t2)
        case False if isV(eval(t3)) => eval(t3)
        case _ => throw TermIsStuck(If(eval(t1), t2, t3))
      }
      case Succ(t1) if isNv(eval(t1)) => Succ(eval(t1))
      case Pred(t1) => eval(t1) match {
        case Zero => Zero
        case Succ(nv) if (isNv(nv)) => nv
        case _ => throw TermIsStuck(Pred(eval(t1)))
      }
      case IsZero(t1) => eval(t1) match {
        case Zero => True
        case Succ(nv) if (isNv(nv)) => False
        case _ => throw TermIsStuck(IsZero(eval(t1)))
      }
      case _ => throw TermIsStuck(t)
    }
  }

  def isV(v: Term): Boolean = {
    v match {
      case True => true
      case False => true
      case a if isNv(a) => true
      case _ => false
    }
  }

  def main(args: Array[String]): Unit = {
    val stdin = new java.io.BufferedReader(new java.io.InputStreamReader(System.in))
    val tokens = new lexical.Scanner(stdin.readLine())
    phrase(term)(tokens) match {
      case Success(trees, _) =>
        for (t <- path(trees))
          println(t)
        try {
          print("Big step: ")
          println(eval(trees))
        } catch {
          case TermIsStuck(t) => println("Stuck term: " + t)
        }
      case e =>
        println(e)
    }
  }
}
