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
    ("\\" ~> ident) ~ (":" ~> Type) ~ ("." ~> Term) ^^ {case (vr: String) ~ (tp: Type) ~ (t: Term) => Abs(vr, tp, t)} |
    "(" ~> Term <~ ")"
    )

  // let type
  /** letTerm ::=
   *   "let" Term ":" Type "=" Term "in" Term
   */
  def letTerm: Parser[Term] =
  ( ("let" ~> ident) ~ (":" ~> Type) ~ ("=" ~> Term) ~ ("in" ~> Term) ^^ {case (x: String) ~ (tp: Type) ~ (t1: Term) ~ (t2: Term) => App(Abs(x, tp, t2), t1)}
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
////////////////////////////TERMS FINISHED//////////////////////////

  def Type: Parser[Type] = 
  ( "Bool" ^^ (t => TypeBool) |
    "Nat" ^^ (t => TypeNat) |
    (Type <~ "->") ~ Type ^^ {case t1 ~ t2 => TypeFun(t1, t2)} |
    (Type <~ "*") ~ Type ^^ {case t1 ~ t2 => TypePair(t1, t2)} |
    "(" ~> Type <~ ")"
    )
////////////////////////////TYPES FINISHED//////////////////////////

  /** Thrown when no reduction rule applies to the given term. */
  case class NoRuleApplies(t: Term) extends Exception(t.toString)

  /** Print an error message, together with the position where it occured. */
  case class TypeError(t: Term, msg: String) extends Exception(msg) {
    override def toString =
      msg + "\n" + t
  }

  /** The context is a list of variable names paired with their type. */
  type Context = List[(String, Type)]


///////////////////////////COPIED FROM MY ASSGN2////////////////////
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
      case Abs(v, tp, t0) => randomnum += 1; Abs(v + randomnum.toString, tp, processTerm(t0, v))
      case _ => t
    }
  def processTerm(t: Term, v: String): Term = {
    t match {
      case Succ(t0) => Succ(processTerm(t0, v))
      case Pred(t0) => Pred(processTerm(t0, v))
      case IsZero(t0) => IsZero(processTerm(t0, v))
      case If(con, t1, t2) => If(processTerm(con, v), processTerm(t1, v), processTerm(t2, v))

      case Var(vr) if (vr == v) => Var(vr + randomnum.toString)
      case Abs(vr, tp, t0) if (vr != v) => Abs(vr, tp, processTerm(t0, v))
      case Abs(vr, tp, t0) if (vr == v) => t
      case App(t1, t2) => App(processTerm(t1, v), processTerm(t2, v))

      case TermPair(t1, t2) => TermPair(processTerm(t1, v), processTerm(t2, v))
      case First(t0) => First(processTerm(t0, v))
      case Second(t0) => Second(processTerm(t0, v))

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
      case Succ(t0) => Succ(subst(t0, x, s))
      case Pred(t0) => Pred(subst(t0, x, s))
      case IsZero(t0) => IsZero(subst(t0, x, s))
      case If(con, t1, t2) => If(subst(con, x, s), subst(t1, x, s), subst(t2, x, s))

      case Var(vr) if (vr == x) => s
      case Var(vr) if (vr != x) => t
      case Abs(vr, tp, t0) if (vr == x) => t
      case Abs(vr, tp, t0) if (vr != x && !(FV(s).exists((v: String) => v == vr))) => Abs(vr, tp, subst(t0, x, s))
      case Abs(vr, tp, t0) if (vr != x && FV(s).exists((v: String) => v == vr)) => subst(alpha(t), x, s)
      case App(t1, t2) => App(subst(t1, x, s), subst(t2, x, s))

      case TermPair(t1, t2) => TermPair(subst(t1, x, s), subst(t2, x, s))
      case First(t0) => First(subst(t0, x, s))
      case Second(t0) => Second(subst(t0, x, s))

      case _ => t
    }
    //Free Variable test
  def FV(t: Term): List[String] =
    t match {
      case True() => List()
      case False() => List()
      case Zero() => List()

      case Succ(t0) => FV(t0)
      case Pred(t0) => FV(t0)
      case IsZero(t0) => FV(t0)
      case If(con, t1, t2) => FV(con):::FV(t1):::FV(t2)

      case Var(vr) => List(vr)
      case Abs(vr, tp, t0) => FV(t0).filter((v: String) => v != vr)
      case App(t1, t2) => FV(t1):::FV(t2)

      case TermPair(t1, t2) => FV(t1):::FV(t2)
      case First(t0) => FV(t0)
      case Second(t0) => FV(t0)
    }
////////////////////////////////////////////////////////////////////

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
  def reduce(t: Term): Term =
    t match {
      //Computational Rules
      case If(True(), t1, t2) => t1
      case If(False(), t1, t2) => t2
      case IsZero(Zero()) => True()
      case IsZero(Succ(nv)) => False()
      case Pred(Zero()) => Zero()
      case Pred(Succ(nv)) => nv
      case App(Abs(vr, tp, t0), t1) if(isValue(t1)) => subst(t0, vr, t1)

      // Congruence Rules
      case If(con, t1, t2) => If(reduce(con), t1, t2)
      case IsZero(t0) => IsZero(reduce(t0))
      case Pred(t0) => Pred(reduce(t0))
      case Succ(t0) => Succ(reduce(t0))
      case App(t1, t2) if(isValue(t1) && !isValue(t2)) => App(t1, reduce(t2))
      case App(t1, t2) if(!isValue(t1)) => App(reduce(t1), t2)

      // New evaluation rules
      case First(TermPair(t1, t2)) => t1
      case Second(TermPair(t1, t2)) => t2
      case First(t0) => First(reduce(t0))
      case Second(t0) => Second(reduce(t0))
      case TermPair(t1, t2) if(!isValue(t1)) => TermPair(reduce(t1), t2)
      case TermPair(t1, t2) if(!isValue(t2)) => TermPair(t1, reduce(t2))

      case _ => throw new NoRuleApplies(t)
    }
  def isValue(t: Term): Boolean =
    t match {
      case True() => true
      case False() => true
      case Zero() => true
      case Succ(t0) => isValue(t0)
      case Pred(t0) => isValue(t0)
      case Abs(vr, tp, t0) => true
      case TermPair(t1, t2) => true
      case _ => false
    }
  // def isValue(t: Term): Boolean =
  //   t match {
  //     case Abs(vr, t0) => true
  //     case _ => false
  //   }

  /** Returns the type of the given term <code>t</code>.
   *
   *  @param ctx the initial context
   *  @param t   the given term
   *  @return    the computed type
   */
  def typeof(ctx: Context, t: Term): Type =
    t match {
      case True() => TypeBool
      case False() => TypeBool
      case Zero() => TypeNat

      case Succ(t0) if(typeof(ctx, t0) == TypeNat) => TypeNat
      case Pred(t0) if(typeof(ctx, t0) == TypeNat) => TypeNat
      case IsZero(t0) if(typeof(ctx, t0) == TypeNat) => TypeBool
      case If(cond, t1, t2) if(typeof(ctx, cond) == TypeBool && typeof(ctx, t1) == typeof(ctx, t2)) => typeof(ctx, t1)

      case Var(vr) if(ctx.toMap.contains(vr)) => ctx.toMap.apply(vr)
      case Abs(vr, tp, t0) => typeof((vr, tp)::ctx, t0) match {
        case (tp2: Type) => TypeFun(tp, tp2)
      }
      case App(t1, t2) => (typeof(ctx, t1), typeof(ctx, t2)) match {
        case (TypeFun(tp1, tp2), (tp3: Type)) if(tp1 == tp3) => tp2
        case (TypeFun(tp1, tp2), (tp3: Type)) if(tp1 != tp3) => throw new TypeError(t, "Applying wrong type to a function")
        case _ => throw new TypeError(t, "Applying something to that's not a function")
      }

      case TermPair(t1, t2) => TypePair(typeof(ctx, t1), typeof(ctx, t2))
      case First(t0) => typeof(ctx, t0) match {
        case TypePair(tp1, tp2) => tp1
        case _ => throw new TypeError(t, "First of not a Pair")
      }
      case Second(t0) => typeof(ctx, t0) match {
        case TypePair(tp1, tp2) => tp2
        case _ => throw new TypeError(t, "Second of not a Pair")
      }

      case _ => throw new TypeError(t, "Not recognized type")
    }


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
