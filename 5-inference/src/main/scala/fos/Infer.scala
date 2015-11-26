package fos

object Infer {
  case class TypeScheme(params: List[TypeVar], tp: Type)
  type Env = List[(String, TypeScheme)]
  type Constraint = (Type, Type)

  case class TypeError(msg: String) extends Exception(msg)

  def collect(env: Env, t: Term): (Type, List[Constraint]) = {
		println(env + ", " + t)
		t match {
			case True() => (BoolType, Nil)
			case False() => (BoolType, Nil)
			case Zero() => (NatType, Nil)

			case Succ(t1) => collect(env, t1) match {
				case (tp, constlst) => (NatType, (tp, NatType)::constlst)
				case _ => throw TypeError("expected NatType")
			}
			case Pred(t1) => collect(env, t1) match {
				case (tp, constlst) => (NatType, (tp, NatType)::constlst)
				case _ => throw TypeError("expected NatType")
			}
			case IsZero(t1) => collect(env, t1) match {
				case (tp, constlst) => (BoolType, (tp, NatType)::constlst)
				case _ => throw TypeError("expected NatType")
			}
			case If(cond, t1, t2) =>
				val ccond = collect(env, cond)
				val ct1 = collect(env, t1)
				val ct2 = collect(env, t2)
				(ct1._1, (ccond._1, BoolType)::(ct1._1, ct2._1)::ct2._2:::ct1._2:::ccond._2)

			case Var(name) =>
				val tscheme = varexists(env, name)
				if(tscheme == null) throw TypeError("use of unknown variable " + name)
				else (tscheme.tp, Nil)
			case Abs(str, tp, t1) => tp match {
				case EmptyTypeTree() =>
					val freshtype = TypeVar(freshtypename)
					val ct1 = collect((str, TypeScheme(Nil, freshtype))::env, t1)
					(FunType(freshtype, ct1._1), ct1._2)
				case _ =>
					val ct1 = collect((str, TypeScheme(Nil, tp.tpe))::env, t1)
					(FunType(tp.tpe, ct1._1), ct1._2)
			}
			case App(t1, t2) =>
				val ct1 = collect(env, t1)
				val ct2 = collect(env, t2)
				val freshtype = TypeVar(freshtypename)
				(freshtype, (ct1._1, FunType(ct2._1, freshtype))::ct1._2:::ct2._2)

			// let x: T = t1 in t2 => (λx:T. t2) t1
			// Let(str, tp, v, t1) => App(Abs(str, tp, t1), v)
			case Let(str, tp, v, t1) =>
				// collect(env, App(Abs(str, tp, t1), v))
				???
		}
	}

  def varexists(env: Env, name: String): TypeScheme = env match {
  	case Nil => null
  	case (stt, tpschm)::tl => if(stt == name) tpschm else varexists(tl, name)
  }

  var uniquenum = 0

  def freshtypename = {
  	uniquenum += 1
  	"x" + uniquenum.toString
  }

  def unify(c: List[Constraint]): Type => Type = {
    def unifyIter(c: List[Constraint], map: Map[TypeVar, Type]): Type => Type = {

      def substitute(t: Type, map: Map[TypeVar, Type]): Type = {
        t match {
          case NatType => NatType
          case BoolType => BoolType
          case FunType(t1, t2) => FunType(substitute(t1, map), substitute(t2, map))
          case e @ TypeVar(name) => if(map.isDefinedAt(e)) map.apply(e) else e
        }
      }

      def typevarinType(tp: Type): List[TypeVar] = tp match {
        case a @ TypeVar(name) => List(a)
        case FunType(t1, t2) => typevarinType(t1) ::: typevarinType(t2)
        case _ => Nil
      }

      def substConstraints(c: Constraint, extend: Map[TypeVar, Type]): Constraint = c match {
        case (c1: TypeVar, c2: TypeVar) =>
          val r1 = if(extend.isDefinedAt(c1)) extend.apply(c1) else c1
          val r2 = if(extend.isDefinedAt(c2)) extend.apply(c2) else c2
          (r1, r2)
        case (c1: TypeVar, c2) =>
          val r1 = if(extend.isDefinedAt(c1)) extend.apply(c1) else c1
          (r1, c2)
        case (c1, c2: TypeVar) =>
          val r2 = if(extend.isDefinedAt(c2)) extend.apply(c2) else c2
          (c1, r2)
        case _ => c
      }

      if(c.isEmpty) sub => substitute(sub, map)
      else c.head match {
        case (NatType, NatType) => unifyIter(c.tail, map)
        case (BoolType, BoolType) => unifyIter(c.tail, map)
        case (TypeVar(n1), TypeVar(n2)) if(n1 == n2) => unifyIter(c.tail, map)
        case (t1 @ TypeVar(name), t2) if(!typevarinType(t2).exists(_.name == name)) =>
          val extend = Map((t1 -> t2))
          unifyIter(c.tail.map(substConstraints(_, extend)), extend++map)
        case (t1, t2 @ TypeVar(name)) if(!typevarinType(t1).exists(_.name == name)) =>
          val extend = Map((t2 -> t1))
          unifyIter(c.tail.map(substConstraints(_, extend)), extend++map)
        case (FunType(a1, a2), FunType(b1, b2)) => unifyIter((a1, b1)::(a2, b2)::c.tail, map)
        case (t1, t2) => throw TypeError("Could not unify: " + t1  + " with " + t2)
      }
    }
    unifyIter(c, Map())
  }
}
