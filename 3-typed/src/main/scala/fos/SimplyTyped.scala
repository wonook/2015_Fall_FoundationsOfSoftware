package fos

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input._

/** This object implements a parser and evaluator for the
 *  simply typed lambda calculus found in Chapter 9 of
 *  the TAPL book.
 */
object SimplyTyped extends StandardTokenParsers {
  lexical.delimiters ++= List("(", ")", "\\", ".", ":", "=", "->", "{", "}", ",", "*")
  lexical.reserved   ++= List("Bool", "Nat", "true", "false", "if", "then", "else", "succ",
                              "pred", "iszero", "let", "in", "fst", "snd")

  /** Term     ::= SimpleTerm { SimpleTerm }
   */
  def Term: Parser[Term] =
    rep1(simpleTerm) ^^ {case termlist => processTermList(termlist.reverse)}
  def processTermList(tl: List[Term]): Term = {
    if (tl.tail.isEmpty) tl.head
    else App(processTermList(tl.tail), tl.head)
  }

  def simpleTerm: Parser[Term] = 
  ( valueTerm |
    funcTerm |
    letTerm |
    pairTerm
    )

  // Bool and Nat
  /** valueTerm ::=
   *   "true" |
   *   "false" |
   *   "if" Term "then" Term "else" Term
   *   number |
   *   "succ" Term
   *   "pred" Term
   *   "iszero" Term
   */
  def valueTerm: Parser[Term] =
  ( "true" ^^ (t => True()) |
    "false" ^^ (t => False()) |
    ("if" ~> Term) ~ ("then" ~> Term) ~ ("else" ~> Term) ^^ {case t1 ~ t2 ~ t3 => If(t1, t2, t3)} |
    numericValue |
    "succ" ~> Term ^^ {case t => Succ(t)} |
    "pred" ~> Term ^^ {case t => Pred(t)} |
    "iszero" ~> Term ^^ {case t => IsZero(t)}
    )
  def numericValue: Parser[Term] =
  ( numericLit ^^ {case n => transformNv(n.toInt) } |
    "succ" ~> numericValue ^^ {case n => Succ(n)}
    )
  def transformNv(n: Int): Term = {
    n match {
      case 0 => Zero()
      case t if t != 0 => Succ(transformNv(t - 1))
    }
  }

  // function types
  /** funcTerm ::=
   *   ident (variable) |
   *   "\\" ident ":" Type "." Term
   *   "(" Term ")"
   */
  def funcTerm: Parser[Term] =
  ( ident ^^ {case e => Var(e)} |
    ("\\" ~> ident) ~ (":" ~> Type) ~ ("." ~> Term) ^^ {case vr ~ tp ~ t => Abs(vr, tp, t)} |
    "(" ~> Term <~ ")"
    )

  // let type
  /** letTerm ::=
   *   "let" Term ":" Type "=" Term "in" Term
   */
  def letTerm: Parser[Term] =
  ( ("let" ~> Term) ~ (":" ~> Type) ~ ("=" ~> Term) ~ ("in" ~> Term) ^^ {case x ~ tp ~ t1 ~ t2 => App(Abs(x, tp, t2), t1)}
    )

  // pair type
  /** pairTerm ::=
   *   "{" Term "," Term "}" |
   *   "fst" Term
   *   "snd" Term
   */
  def pairTerm: Parser[Term] =
  ( ("{" ~> Term) ~ ("," ~> Term <~ "}") ^^ {case t1 ~ t2 => TermPair(t1, t2)} |
    "fst" ~> Term ^^ {case t => First(t)} |
    "snd" ~> Term ^^ {case t => Second(t)}
    )


  /** Thrown when no reduction rule applies to the given term. */
  case class NoRuleApplies(t: Term) extends Exception(t.toString)

  /** Print an error message, together with the position where it occured. */
  case class TypeError(t: Term, msg: String) extends Exception(msg) {
    override def toString =
      msg + "\n" + t
  }

  /** The context is a list of variable names paired with their type. */
  type Context = List[(String, Type)]

  /** Call by value reducer. */
  def reduce(t: Term): Term =
    ???


  /** Returns the type of the given term <code>t</code>.
   *
   *  @param ctx the initial context
   *  @param t   the given term
   *  @return    the computed type
   */
  def typeof(ctx: Context, t: Term): Type =
    ???


  /** Returns a stream of terms, each being one step of reduction.
   *
   *  @param t      the initial term
   *  @param reduce the evaluation strategy used for reduction.
   *  @return       the stream of terms representing the big reduction.
   */
  def path(t: Term, reduce: Term => Term): Stream[Term] =
    try {
      var t1 = reduce(t)
      Stream.cons(t, path(t1, reduce))
    } catch {
      case NoRuleApplies(_) =>
        Stream.cons(t, Stream.empty)
    }

  def main(args: Array[String]): Unit = {
    val stdin = new java.io.BufferedReader(new java.io.InputStreamReader(System.in))
    val tokens = new lexical.Scanner(stdin.readLine())
    phrase(Term)(tokens) match {
      case Success(trees, _) =>
        try {
          println("typed: " + typeof(Nil, trees))
          for (t <- path(trees, reduce))
            println(t)
        } catch {
          case tperror: Exception => println(tperror.toString)
        }
      case e =>
        println(e)
    }
  }
}
