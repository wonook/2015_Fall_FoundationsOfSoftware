package fos

object Infer {
  case class TypeScheme(params: List[TypeVar], tp: Type)
  type Env = List[(String, TypeScheme)]
  type Constraint = (Type, Type)

  case class TypeError(msg: String) extends Exception(msg)

  def collect(env: Env, t: Term): (Type, List[Constraint]) = {
//    println("collect: " + env + "|t: " + t)
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
				else {
          val ret = if(tscheme.params.exists((p) => typevarinType(tscheme.tp).exists(_ == p))) TypeVar(freshtypename) else tscheme.tp
          (ret, Nil)
        }
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

			// let x: T = v in t1 => (λx:T. t1) v
			// Let(str, tp, v, t1) => App(Abs(str, tp, t1), v)
			case Let(str, tp, v, t1) =>
				// collect(env, App(Abs(str, tp, t1), v))
				val (ctp, cc) = collect(env, v)
        val sub = unify(cc)
        val typed = sub(ctp)

        val newEnvTypes = env.map((e) => (e._1, TypeScheme(e._2.params, sub(e._2.tp))))
        val generalizedTypes = typevarinType(typed).filter((e) => newEnvTypes.forall((e1) => !typevarinType(e1._2.tp).exists(_.name == e.name)))
        val newEnv = (str, TypeScheme(generalizedTypes, typed))::newEnvTypes
        collect(newEnv, t1)
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

  def typevarinType(tp: Type): List[TypeVar] = tp match {
    case a @ TypeVar(name) => List(a)
    case FunType(t1, t2) => (typevarinType(t1) ::: typevarinType(t2)).distinct
    case _ => Nil
  }

  def unify(c: List[Constraint]): Type => Type = {
    def unifyIter(c: List[Constraint], map: Map[TypeVar, Type]): Type => Type = {

      def substitute(t: Type, map: Map[TypeVar, Type]): Type = {
//        println("|||substitute: " + t)
        t match {
          case NatType => NatType
          case BoolType => BoolType
          case FunType(t1, t2) => FunType(substitute(t1, map), substitute(t2, map))
          case e @ TypeVar(name) => if(map.isDefinedAt(e)) map.apply(e) else e
        }
      }

      def updateType(extend: Map[TypeVar, Type], tp: Type): Type = {
        tp match {
          case (tv @ TypeVar(name)) =>
            if(extend.isDefinedAt(tv)) extend.apply(tv) else tv
          case (FunType(t1, t2)) =>
            FunType(updateType(extend, t1), updateType(extend, t2))
          case _ => tp
        }
      }

//      println("||unify: " + c + " ||map: " + map.toList)
      if(c.isEmpty) sub => substitute(sub, map)
      else c.head match {
        case (NatType, NatType) => unifyIter(c.tail, map)
        case (BoolType, BoolType) => unifyIter(c.tail, map)
        case (TypeVar(n1), TypeVar(n2)) if(n1 == n2) => unifyIter(c.tail, map)
        case (t1 @ TypeVar(name), t2) if(!typevarinType(t2).exists(_.name == name)) =>
          val extend = Map((t1, t2))
          val newMap = map.map((e) => (e._1, updateType(extend, e._2)))
          unifyIter(c.tail.map((e) => (updateType(extend, e._1), updateType(extend, e._2))), extend++newMap)
        case (t1, t2 @ TypeVar(name)) if(!typevarinType(t1).exists(_.name == name)) =>
          val extend = Map((t2, t1))
          val newMap = map.map((e) => (e._1, updateType(extend, e._2)))
          unifyIter(c.tail.map((e) => (updateType(extend, e._1), updateType(extend, e._2))), extend++newMap)
        case (FunType(a1, a2), FunType(b1, b2)) => unifyIter((a1, b1)::(a2, b2)::c.tail, map)
        case (t1, t2) => throw TypeError("Could not unify: " + t1  + " with " + t2)
      }
    }
    unifyIter(c, Map())
  }
}
