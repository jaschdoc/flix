/*
 * Copyright 2018 Magnus Madsen, Anna Krogh, Patrick Lundvig, Christian Bonde
 * Copyright 2025 Jakob Schneider Villumsen
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package ca.uwaterloo.flix.language.phase.optimizer

import ca.uwaterloo.flix.api.Flix
import ca.uwaterloo.flix.language.ast.MonoAst.{Expr, FormalParam, Occur, Pattern}
import ca.uwaterloo.flix.language.ast.SemanticOp.{BoolOp, CharOp, Float32Op, Float64Op, Int16Op, Int32Op, Int64Op, Int8Op, StringOp}
import ca.uwaterloo.flix.language.ast.shared.Constant
import ca.uwaterloo.flix.language.ast.{AtomicOp, MonoAst, SourceLocation, Symbol, Type}
import ca.uwaterloo.flix.util.{InternalCompilerException, ParOps}

import java.util.concurrent.ConcurrentHashMap
import scala.annotation.tailrec
import scala.jdk.CollectionConverters.ConcurrentMapHasAsScala

/**
  * Rewrites the body of each def using, using the following transformations:
  *   - Copy Propagation:
  * {{{
  *     let x = 1;
  *     f(x)
  * }}}
  *     becomes
  * {{{
  *     let x = 1;
  *     f(1)
  * }}}
  *   - Dead Code Elimination
  * {{{
  *     let x = 1;
  *     f(1)
  * }}}
  *     becomes
  * {{{
  *     f(1)
  * }}}
  *   - Inline Expansion
  * {{{
  *     f(1)
  * }}}
  *     becomes (where the definition of `f` is `x + 2`)
  * {{{
  *     (x -> x + 2)(1)
  * }}}
  *   - Beta Reduction
  * {{{
  *     (x -> x + 2)(1)
  * }}}
  *     becomes
  * {{{
  *     let x = 1;
  *     x + 2
  * }}}
  */
object Inliner {

  /** Performs inlining on the given AST `root`. */
  def run(root: MonoAst.Root)(implicit flix: Flix): (MonoAst.Root, Set[Symbol.DefnSym]) = {
    val sctx: SharedContext = SharedContext.mk()
    val defs = ParOps.parMapValues(root.defs)(visitDef(_)(sctx, root, flix))
    val newDelta = sctx.changed.asScala.keys.toSet
    (root.copy(defs = defs), newDelta)
  }

  /** Performs inlining on the body of `def0`. */
  private def visitDef(def0: MonoAst.Def)(implicit sctx: SharedContext, root: MonoAst.Root, flix: Flix): MonoAst.Def = def0 match {
    case MonoAst.Def(sym, spec, exp, loc) =>
      val e = visitExp(exp, LocalContext.Empty)(sym, sctx, root, flix)
      MonoAst.Def(sym, spec, e, loc)
  }

  /**
    * Performs inlining on the expression `exp0`.
    *
    * To avoid duplicating variable names, [[visitExp]] unconditionally
    * assigns new names to all variables.
    * When a binder is visited, it replaces it with a fresh variable and adds
    * it to the variable substitution `varSubst` in th LocalContext `ctx0`.
    * When a variable is visited, it replaces the old variable with the fresh one.
    * Top-level function parameters are not substituted unless inlined, in which case
    * the parameters are let-bound and added to the variable substitution.
    *
    * Within `ctx0` [[visitExp]] also maintains an 'expression substitution' `subst` mapping symbols
    * to expressions ([[SubstRange]]) which it uses unconditionally replace some variable occurrences (see below).
    * It also maintains a set of in-scope variables `inScopeVars` mapping symbols to [[BoundKind]], i.e.,
    * information on how a variable is bound. This is used to consider inlining at a variable occurrence.
    * If a let-bound variable has been visited and is not in `subst`, then it must always be in `inScopeVars`.
    * Importantly, only fresh variables are mapped in both `subst` and `inScopeVars`, so when a variable
    * is encountered, `varSubst` must always be applied first to obtain the corresponding fresh variable.
    *
    * When [[visitExp]] encounters a variable `x` it first applies the substitution `varSubst` to
    * obtain the fresh variable. If it is not in the substitution then the variable is a function parameter
    * occurrence bound by the defining function with symbol `sym0`.
    * If it obtains `x'` from the substitution, it does the following three things:
    *   1. If `x'` is in the expression substitution `subst` it replaces the variable with
    *      the expression, recursively calling [[visitExp]] with the substitution from the definition site
    *      if it is a [[SubstRange.SuspendedExpr]].
    *      This means that [[visitExp]] previously decided to unconditionally inline the let-binding
    *   1. If it is a [[SubstRange.DoneExpr]] then it decided to do copy-propagation of that binding (see below).
    *      It then recursively visits the expression using the empty substitution since the current substitution
    *      is invalid in that scope.
    *   1. If `x'` is not in the expression substitution, it must be in the set of in-scope variable
    *      definitions and considers it for inlining if its definition is pure.
    *
    * When [[visitExp]] encounters a let-binding `let sym = e1; e2` it considers four cases
    * (note that it always refreshes `sym` to `sym'` as mentioned above):
    *   1. If the binding is dead and pure, it drops the binding and returns `visitExp(e2)`.
    *   1. If the binding is dead and impure, it rewrites the binding to a statement.
    *   1. If the binding occurs once and is pure, it adds the unvisited `e1` to the substitution `subst`,
    *      drops the binding and unconditionally inlines it at the occurrence of `sym`.
    *   1. If the binding occurs more than once, it first visits `e1` and considers the following:
    *      (a) If the visited `e1` is trivial and pure, it removes the let-binding and unconditionally inlines
    *      the visited `e1` at every occurrence of `sym`. This corresponds to copy-propagation.
    *      (b) If the visited `e1` is nontrivial, it keeps the let-binding, adds the visited `e1` to the set
    *      of in-scope variable definitions and considers it for inlining at every occurrence.
    */
  private def visitExp(exp0: Expr, ctx0: LocalContext)(implicit sym0: Symbol.DefnSym, sctx: SharedContext, root: MonoAst.Root, flix: Flix): Expr = exp0 match {
    case Expr.Cst(cst, tpe, loc) =>
      Expr.Cst(cst, tpe, loc)

    case Expr.Var(sym, tpe, loc) =>
      // Replace with fresh variable if it is not a parameter
      ctx0.varSubst.get(sym) match {
        case None => // Function parameter occurrence
          Expr.Var(sym, tpe, loc)

        case Some(freshVarSym) =>
          // Check for unconditional inlining / copy-propagation
          ctx0.subst.get(freshVarSym) match {
            case Some(SubstRange.SuspendedExpr(exp, subst)) =>
              // Unconditional inline of variable that occurs once.
              // Use the expression substitution from the definition site.
              sctx.changed.putIfAbsent(sym0, ())
              visitExp(exp, ctx0.withSubst(subst))

            case Some(SubstRange.DoneExpr(exp)) =>
              // Copy-propagation of visited expr.
              // Use the empty expression substitution since this has already been visited
              // and the context might indicate that if exp is a var, it should be inlined again.
              sctx.changed.putIfAbsent(sym0, ())
              visitExp(exp, ctx0.withSubst(Map.empty))

            case None =>
              // It was not unconditionally inlined, so consider inlining at this occurrence site
              useSiteInline(freshVarSym, ctx0) match {
                case Some(exp) =>
                  sctx.changed.putIfAbsent(sym0, ())
                  visitExp(exp, ctx0.withSubst(Map.empty))

                case None =>
                  Expr.Var(freshVarSym, tpe, loc)
              }
          }
      }

    case Expr.Lambda(fparam, exp, tpe, loc) =>
      val (fp, varSubst1) = freshFormalParam(fparam)
      val ctx = ctx0.addVarSubsts(varSubst1).addInScopeVar(fp.sym, BoundKind.ParameterOrPattern)
      val e = visitExp(exp, ctx)
      Expr.Lambda(fp, e, tpe, loc)

    case Expr.ApplyAtomic(op, exps, tpe, eff, loc) =>
      val es = exps.map(visitExp(_, ctx0))
      if (es.forall(isCst)) {
        constantFold(op, es, loc) match {
          case Some(exp) =>
            sctx.changed.putIfAbsent(sym0, ())
            exp

          case None =>
            Expr.ApplyAtomic(op, es, tpe, eff, loc)
        }
      } else {
        Expr.ApplyAtomic(op, es, tpe, eff, loc)
      }

    case Expr.ApplyClo(exp1, exp2, tpe, eff, loc) =>
      val appCtx = ExprContext.AppCtx(exp2, ctx0.subst, ctx0.exprCtx)
      val ctx1 = ctx0.addExprCtx(appCtx)
      visitExp(exp1, ctx1) match {
        case Expr.Lambda(fparam, e1, _, _) =>
          sctx.changed.putIfAbsent(sym0, ())
          val e2 = visitExp(exp2, ctx0)
          bindArgs(e1, List(fparam), List(e2), loc, ctx0)

        case e1 =>
          val e2 = visitExp(exp2, ctx0)
          Expr.ApplyClo(e1, e2, tpe, eff, loc)
      }

    case Expr.ApplyDef(sym, exps, itpe, tpe, eff, loc) =>
      val es = exps.map(visitExp(_, ctx0))
      if (shouldInlineDef(root.defs(sym), es, ctx0)) {
        sctx.changed.putIfAbsent(sym0, ())
        val defn = root.defs(sym)
        val ctx = ctx0.withSubst(Map.empty).enableInliningMode
        bindArgs(defn.exp, defn.spec.fparams, es, loc, ctx)
      } else {
        val es = exps.map(visitExp(_, ctx0))
        Expr.ApplyDef(sym, es, itpe, tpe, eff, loc)
      }

    case Expr.ApplyLocalDef(sym, exps, tpe, eff, loc) =>
      // Refresh the symbol
      val sym1 = ctx0.varSubst.getOrElse(sym, sym)
      // Check if it was unconditionally inlined
      ctx0.subst.get(sym1) match {
        case Some(SubstRange.SuspendedExpr(Expr.LocalDef(_, fparams, exp, _, _, _, _, _), subst)) =>
          val es = exps.map(visitExp(_, ctx0))
          bindArgs(exp, fparams, es, loc, ctx0.withSubst(subst))

        case None | Some(_) =>
          // It was not unconditionally inlined, so return same expr with visited subexpressions
          val es = exps.map(visitExp(_, ctx0))
          Expr.ApplyLocalDef(sym1, es, tpe, eff, loc)
      }


    case Expr.Let(sym, exp1, exp2, tpe, eff, occur, loc) => (occur, exp1.eff) match {
      case (Occur.Dead, Type.Pure) =>
        // Eliminate dead binder
        sctx.changed.putIfAbsent(sym0, ())
        visitExp(exp2, ctx0)

      case (Occur.Dead, _) =>
        // Rewrite to Stm to preserve effect
        sctx.changed.putIfAbsent(sym0, ())
        val e1 = visitExp(exp1, ctx0)
        val e2 = visitExp(exp2, ctx0)
        Expr.Stm(e1, e2, tpe, eff, loc)

      case (Occur.Once, Type.Pure) =>
        // Unconditionally inline
        sctx.changed.putIfAbsent(sym0, ())
        val freshVarSym = Symbol.freshVarSym(sym)
        val ctx = ctx0.addVarSubst(sym, freshVarSym)
          .addSubst(freshVarSym, SubstRange.SuspendedExpr(exp1, ctx0.subst))
        visitExp(exp2, ctx)

      case _ =>
        // Simplify and maybe do copy-propagation
        val e1 = visitExp(exp1, ctx0.withEmptyExprCtx)
        if (isSimple(e1) && exp1.eff == Type.Pure) {
          // Do copy propagation and drop let-binding
          sctx.changed.putIfAbsent(sym0, ())
          val freshVarSym = Symbol.freshVarSym(sym)
          val ctx = ctx0.addVarSubst(sym, freshVarSym).addSubst(freshVarSym, SubstRange.DoneExpr(e1))
          visitExp(exp2, ctx)
        } else {
          // Keep let-binding, add binding freshVarSym -> e1 to the set of in-scope
          // variables and consider inlining at each occurrence.
          val freshVarSym = Symbol.freshVarSym(sym)
          val ctx = ctx0.addVarSubst(sym, freshVarSym).addInScopeVar(freshVarSym, BoundKind.LetBound(e1, occur))
          val e2 = visitExp(exp2, ctx)
          Expr.Let(freshVarSym, e1, e2, tpe, eff, occur, loc)
        }
    }

    case Expr.LocalDef(sym, fparams, exp1, exp2, tpe, eff, occur, loc) => occur match {
      case Occur.Dead =>
        // A function declaration is always pure so we do not care about the effect of exp1
        sctx.changed.putIfAbsent(sym0, ())
        visitExp(exp2, ctx0)

      case Occur.Once =>
        // It occurs exactly once in exp2, otherwise it would be OnceInLocalDef,
        // so unconditionally inline
        sctx.changed.putIfAbsent(sym0, ())
        val freshVarSym = Symbol.freshVarSym(sym)
        val exp = Expr.LocalDef(freshVarSym, fparams, exp1, exp2, tpe, eff, occur, loc)
        val ctx = ctx0.addVarSubst(sym, freshVarSym)
          .addSubst(freshVarSym, SubstRange.SuspendedExpr(exp, ctx0.subst))
        visitExp(exp2, ctx)

      case _ =>
        val freshVarSym = Symbol.freshVarSym(sym)
        val ctx1 = ctx0.addVarSubst(sym, freshVarSym)
        val e2 = visitExp(exp2, ctx1)
        val (fps, varSubsts) = fparams.map(freshFormalParam).unzip
        val ctx2 = ctx1.addVarSubsts(varSubsts)
          .addInScopeVar(sym, BoundKind.ParameterOrPattern)
          .addInScopeVars(fps.map(fp => fp.sym -> BoundKind.ParameterOrPattern))
          .withEmptyExprCtx
        val e1 = visitExp(exp1, ctx2)
        Expr.LocalDef(freshVarSym, fps, e1, e2, tpe, eff, occur, loc)
    }

    case Expr.Scope(sym, rvar, exp, tpe, eff, loc) =>
      val freshVarSym = Symbol.freshVarSym(sym)
      val ctx = ctx0.addVarSubst(sym, freshVarSym).addInScopeVar(freshVarSym, BoundKind.ParameterOrPattern)
      val e = visitExp(exp, ctx)
      Expr.Scope(freshVarSym, rvar, e, tpe, eff, loc)

    case Expr.IfThenElse(exp1, exp2, exp3, tpe, eff, loc) =>
      val e1 = visitExp(exp1, ctx0.withEmptyExprCtx)
      e1 match {
        case Expr.Cst(Constant.Bool(true), _, _) =>
          sctx.changed.putIfAbsent(sym0, ())
          visitExp(exp2, ctx0)
        case Expr.Cst(Constant.Bool(false), _, _) =>
          sctx.changed.putIfAbsent(sym0, ())
          visitExp(exp3, ctx0)
        case _ =>
          val e2 = visitExp(exp2, ctx0)
          val e3 = visitExp(exp3, ctx0)
          Expr.IfThenElse(e1, e2, e3, tpe, eff, loc)
      }

    case Expr.Stm(exp1, exp2, tpe, eff, loc) => exp1.eff match {
      case Type.Pure =>
        // Exp1 has no side effect and is unused
        sctx.changed.putIfAbsent(sym0, ())
        visitExp(exp2, ctx0)

      case _ =>
        val e1 = visitExp(exp1, ctx0)
        val e2 = visitExp(exp2, ctx0)
        Expr.Stm(e1, e2, tpe, eff, loc)
    }

    case Expr.Discard(exp, eff, loc) =>
      val e = visitExp(exp, ctx0)
      Expr.Discard(e, eff, loc)

    case Expr.Match(exp, rules, tpe, eff, loc) =>
      val matchCtx = ExprContext.MatchCtx(rules, ctx0.subst, ctx0.exprCtx)
      val ctx = ctx0.addExprCtx(matchCtx)
      val e = visitExp(exp, ctx)
      if (isLiteral(e)) {
        tryDeforestation(e, rules, tpe, eff, loc, ctx0)
      } else {
        val rs = rules.map(visitMatchRule(_, ctx0))
        Expr.Match(e, rs, tpe, eff, loc)
      }

    case Expr.VectorLit(exps, tpe, eff, loc) =>
      val es = exps.map(visitExp(_, ctx0))
      Expr.VectorLit(es, tpe, eff, loc)

    case Expr.VectorLoad(exp1, exp2, tpe, eff, loc) =>
      val e1 = visitExp(exp1, ctx0)
      val e2 = visitExp(exp2, ctx0)
      Expr.VectorLoad(e1, e2, tpe, eff, loc)

    case Expr.VectorLength(exp, loc) =>
      val e = visitExp(exp, ctx0)
      Expr.VectorLength(e, loc)

    case Expr.Ascribe(exp, tpe, eff, loc) =>
      val e = visitExp(exp, ctx0)
      Expr.Ascribe(e, tpe, eff, loc)

    case Expr.Cast(exp, tpe, eff, loc) =>
      val e = visitExp(exp, ctx0)
      Expr.Cast(e, tpe, eff, loc)

    case Expr.TryCatch(exp, rules, tpe, eff, loc) =>
      val e = visitExp(exp, ctx0)
      val rs = rules.map(visitCatchRule(_, ctx0))
      Expr.TryCatch(e, rs, tpe, eff, loc)

    case Expr.RunWith(exp, effUse, rules, tpe, eff, loc) =>
      val rs = rules.map(visitHandlerRule(_, ctx0))
      val e = visitExp(exp, ctx0)
      Expr.RunWith(e, effUse, rs, tpe, eff, loc)

    case Expr.Do(op, exps, tpe, eff, loc) =>
      val es = exps.map(visitExp(_, ctx0))
      Expr.Do(op, es, tpe, eff, loc)

    case Expr.NewObject(name, clazz, tpe, eff, methods0, loc) =>
      val methods = methods0.map(visitJvmMethod(_, ctx0))
      Expr.NewObject(name, clazz, tpe, eff, methods, loc)
  }

  /** Applies `op` to `exps` if possible. */
  private def constantFold(op: AtomicOp, exps: List[Expr], loc0: SourceLocation): Option[Expr] = op match {
    case AtomicOp.Closure(_) => None
    case AtomicOp.Region => None
    case AtomicOp.Is(_) => None
    case AtomicOp.Tag(_) => None
    case AtomicOp.Untag(_, _) => None
    case AtomicOp.Index(_) => None
    case AtomicOp.Tuple => None
    case AtomicOp.RecordSelect(_) => None
    case AtomicOp.RecordExtend(_) => None
    case AtomicOp.RecordRestrict(_) => None
    case AtomicOp.ExtensibleIs(_) => None
    case AtomicOp.ExtensibleTag(_) => None
    case AtomicOp.ExtensibleUntag(_) => None
    case AtomicOp.ArrayLit => None
    case AtomicOp.ArrayNew => None
    case AtomicOp.ArrayLoad => None
    case AtomicOp.ArrayStore => None
    case AtomicOp.ArrayLength => None
    case AtomicOp.StructNew(_, _) => None
    case AtomicOp.StructGet(_) => None
    case AtomicOp.StructPut(_) => None
    case AtomicOp.InstanceOf(_) => None
    case AtomicOp.Cast => None
    case AtomicOp.Unbox => None
    case AtomicOp.Box => None
    case AtomicOp.InvokeConstructor(_) => None
    case AtomicOp.InvokeMethod(_) => None
    case AtomicOp.InvokeStaticMethod(_) => None
    case AtomicOp.GetField(_) => None
    case AtomicOp.PutField(_) => None
    case AtomicOp.GetStaticField(_) => None
    case AtomicOp.PutStaticField(_) => None
    case AtomicOp.Throw => None
    case AtomicOp.Spawn => None
    case AtomicOp.Lazy => None
    case AtomicOp.Force => None
    case AtomicOp.HoleError(_) => None
    case AtomicOp.MatchError => None
    case AtomicOp.CastError(_, _) => None
    case AtomicOp.Unary(sop) => sop match {
      case BoolOp.Not =>
        val List(Expr.Cst(Constant.Bool(bool), tpe, loc)) = exps
        Some(Expr.Cst(Constant.Bool(!bool), tpe, loc))

      case Float32Op.Neg =>
        val List(Expr.Cst(Constant.Float32(float), tpe, loc)) = exps
        Some(Expr.Cst(Constant.Float32(-float), tpe, loc))

      case Float64Op.Neg =>
        val List(Expr.Cst(Constant.Float64(float), tpe, loc)) = exps
        Some(Expr.Cst(Constant.Float64(-float), tpe, loc))

      case Int8Op.Neg =>
        val List(Expr.Cst(Constant.Int8(int), tpe, loc)) = exps
        Some(Expr.Cst(Constant.Int8((-int).toByte), tpe, loc))

      case Int8Op.Not =>
        val List(Expr.Cst(Constant.Int8(int), tpe, loc)) = exps
        Some(Expr.Cst(Constant.Int8((~int).toByte), tpe, loc))

      case Int16Op.Neg =>
        val List(Expr.Cst(Constant.Int16(int), tpe, loc)) = exps
        Some(Expr.Cst(Constant.Int16((-int).toShort), tpe, loc))

      case Int16Op.Not =>
        val List(Expr.Cst(Constant.Int16(int), tpe, loc)) = exps
        Some(Expr.Cst(Constant.Int16((~int).toShort), tpe, loc))

      case Int32Op.Neg =>
        val List(Expr.Cst(Constant.Int32(int), tpe, loc)) = exps
        Some(Expr.Cst(Constant.Int32(-int), tpe, loc))

      case Int32Op.Not =>
        val List(Expr.Cst(Constant.Int32(int), tpe, loc)) = exps
        Some(Expr.Cst(Constant.Int32(~int), tpe, loc))

      case Int64Op.Neg =>
        val List(Expr.Cst(Constant.Int64(int), tpe, loc)) = exps
        Some(Expr.Cst(Constant.Int64(-int), tpe, loc))

      case Int64Op.Not =>
        val List(Expr.Cst(Constant.Int64(int), tpe, loc)) = exps
        Some(Expr.Cst(Constant.Int64(~int), tpe, loc))
    }

    case AtomicOp.Binary(sop) => sop match {
      case BoolOp.And =>
        val List(Expr.Cst(Constant.Bool(left), _, _), Expr.Cst(Constant.Bool(right), _, _)) = exps
        Some(Expr.Cst(Constant.Bool(left && right), Type.Bool, loc0))

      case BoolOp.Or =>
        val List(Expr.Cst(Constant.Bool(left), _, _), Expr.Cst(Constant.Bool(right), _, _)) = exps
        Some(Expr.Cst(Constant.Bool(left || right), Type.Bool, loc0))

      case BoolOp.Eq =>
        val List(Expr.Cst(Constant.Bool(left), _, _), Expr.Cst(Constant.Bool(right), _, _)) = exps
        Some(Expr.Cst(Constant.Bool(left == right), Type.Bool, loc0))

      case BoolOp.Neq =>
        val List(Expr.Cst(Constant.Bool(left), _, _), Expr.Cst(Constant.Bool(right), _, _)) = exps
        Some(Expr.Cst(Constant.Bool(left != right), Type.Bool, loc0))

      case CharOp.Eq =>
        val List(Expr.Cst(Constant.Char(left), _, _), Expr.Cst(Constant.Char(right), _, _)) = exps
        Some(Expr.Cst(Constant.Bool(left == right), Type.Bool, loc0))

      case CharOp.Neq =>
        val List(Expr.Cst(Constant.Char(left), _, _), Expr.Cst(Constant.Char(right), _, _)) = exps
        Some(Expr.Cst(Constant.Bool(left != right), Type.Bool, loc0))

      case CharOp.Lt =>
        val List(Expr.Cst(Constant.Char(left), _, _), Expr.Cst(Constant.Char(right), _, _)) = exps
        Some(Expr.Cst(Constant.Bool(left < right), Type.Bool, loc0))

      case CharOp.Le =>
        val List(Expr.Cst(Constant.Char(left), _, _), Expr.Cst(Constant.Char(right), _, _)) = exps
        Some(Expr.Cst(Constant.Bool(left <= right), Type.Bool, loc0))

      case CharOp.Gt =>
        val List(Expr.Cst(Constant.Char(left), _, _), Expr.Cst(Constant.Char(right), _, _)) = exps
        Some(Expr.Cst(Constant.Bool(left > right), Type.Bool, loc0))

      case CharOp.Ge =>
        val List(Expr.Cst(Constant.Char(left), _, _), Expr.Cst(Constant.Char(right), _, _)) = exps
        Some(Expr.Cst(Constant.Bool(left >= right), Type.Bool, loc0))

      case Float32Op.Add =>
        val List(Expr.Cst(Constant.Float32(left), tpe, _), Expr.Cst(Constant.Float32(right), _, _)) = exps
        Some(Expr.Cst(Constant.Float32(left + right), tpe, loc0))

      case Float32Op.Sub =>
        val List(Expr.Cst(Constant.Float32(left), tpe, _), Expr.Cst(Constant.Float32(right), _, _)) = exps
        Some(Expr.Cst(Constant.Float32(left - right), tpe, loc0))

      case Float32Op.Mul =>
        val List(Expr.Cst(Constant.Float32(left), tpe, _), Expr.Cst(Constant.Float32(right), _, _)) = exps
        Some(Expr.Cst(Constant.Float32(left * right), tpe, loc0))

      case Float32Op.Div =>
        val List(Expr.Cst(Constant.Float32(left), tpe, _), Expr.Cst(Constant.Float32(right), _, _)) = exps
        Some(Expr.Cst(Constant.Float32(left / right), tpe, loc0))

      case Float32Op.Exp =>
        val List(Expr.Cst(Constant.Float32(left), tpe, _), Expr.Cst(Constant.Float32(right), _, _)) = exps
        Some(Expr.Cst(Constant.Float32(Math.pow(left, right).toFloat), tpe, loc0))

      case Float32Op.Eq =>
        val List(Expr.Cst(Constant.Float32(left), _, _), Expr.Cst(Constant.Float32(right), _, _)) = exps
        Some(Expr.Cst(Constant.Bool(left == right), Type.Bool, loc0))

      case Float32Op.Neq =>
        val List(Expr.Cst(Constant.Float32(left), _, _), Expr.Cst(Constant.Float32(right), _, _)) = exps
        Some(Expr.Cst(Constant.Bool(left != right), Type.Bool, loc0))

      case Float32Op.Lt =>
        val List(Expr.Cst(Constant.Float32(left), _, _), Expr.Cst(Constant.Float32(right), _, _)) = exps
        Some(Expr.Cst(Constant.Bool(left < right), Type.Bool, loc0))

      case Float32Op.Le =>
        val List(Expr.Cst(Constant.Float32(left), _, _), Expr.Cst(Constant.Float32(right), _, _)) = exps
        Some(Expr.Cst(Constant.Bool(left <= right), Type.Bool, loc0))

      case Float32Op.Gt =>
        val List(Expr.Cst(Constant.Float32(left), _, _), Expr.Cst(Constant.Float32(right), _, _)) = exps
        Some(Expr.Cst(Constant.Bool(left > right), Type.Bool, loc0))

      case Float32Op.Ge =>
        val List(Expr.Cst(Constant.Float32(left), _, _), Expr.Cst(Constant.Float32(right), _, _)) = exps
        Some(Expr.Cst(Constant.Bool(left >= right), Type.Bool, loc0))

      case Float64Op.Add =>
        val List(Expr.Cst(Constant.Float64(left), tpe, _), Expr.Cst(Constant.Float64(right), _, _)) = exps
        Some(Expr.Cst(Constant.Float64(left + right), tpe, loc0))

      case Float64Op.Sub =>
        val List(Expr.Cst(Constant.Float64(left), tpe, _), Expr.Cst(Constant.Float64(right), _, _)) = exps
        Some(Expr.Cst(Constant.Float64(left - right), tpe, loc0))

      case Float64Op.Mul =>
        val List(Expr.Cst(Constant.Float64(left), tpe, _), Expr.Cst(Constant.Float64(right), _, _)) = exps
        Some(Expr.Cst(Constant.Float64(left * right), tpe, loc0))

      case Float64Op.Div =>
        val List(Expr.Cst(Constant.Float64(left), tpe, _), Expr.Cst(Constant.Float64(right), _, _)) = exps
        Some(Expr.Cst(Constant.Float64(left / right), tpe, loc0))

      case Float64Op.Exp =>
        val List(Expr.Cst(Constant.Float64(left), tpe, _), Expr.Cst(Constant.Float64(right), _, _)) = exps
        Some(Expr.Cst(Constant.Float64(Math.pow(left, right)), tpe, loc0))

      case Float64Op.Eq =>
        val List(Expr.Cst(Constant.Float64(left), _, _), Expr.Cst(Constant.Float64(right), _, _)) = exps
        Some(Expr.Cst(Constant.Bool(left == right), Type.Bool, loc0))

      case Float64Op.Neq =>
        val List(Expr.Cst(Constant.Float64(left), _, _), Expr.Cst(Constant.Float64(right), _, _)) = exps
        Some(Expr.Cst(Constant.Bool(left != right), Type.Bool, loc0))

      case Float64Op.Lt =>
        val List(Expr.Cst(Constant.Float64(left), _, _), Expr.Cst(Constant.Float64(right), _, _)) = exps
        Some(Expr.Cst(Constant.Bool(left < right), Type.Bool, loc0))

      case Float64Op.Le =>
        val List(Expr.Cst(Constant.Float64(left), _, _), Expr.Cst(Constant.Float64(right), _, _)) = exps
        Some(Expr.Cst(Constant.Bool(left <= right), Type.Bool, loc0))

      case Float64Op.Gt =>
        val List(Expr.Cst(Constant.Float64(left), _, _), Expr.Cst(Constant.Float64(right), _, _)) = exps
        Some(Expr.Cst(Constant.Bool(left > right), Type.Bool, loc0))

      case Float64Op.Ge =>
        val List(Expr.Cst(Constant.Float64(left), _, _), Expr.Cst(Constant.Float64(right), _, _)) = exps
        Some(Expr.Cst(Constant.Bool(left >= right), Type.Bool, loc0))

      case Int8Op.Add =>
        val List(Expr.Cst(Constant.Int8(left), tpe, _), Expr.Cst(Constant.Int8(right), _, _)) = exps
        Some(Expr.Cst(Constant.Int8((left + right).toByte), tpe, loc0))

      case Int8Op.Sub =>
        val List(Expr.Cst(Constant.Int8(left), tpe, _), Expr.Cst(Constant.Int8(right), _, _)) = exps
        Some(Expr.Cst(Constant.Int8((left - right).toByte), tpe, loc0))

      case Int8Op.Mul =>
        val List(Expr.Cst(Constant.Int8(left), tpe, _), Expr.Cst(Constant.Int8(right), _, _)) = exps
        Some(Expr.Cst(Constant.Int8((left * right).toByte), tpe, loc0))

      case Int8Op.Div =>
        val List(Expr.Cst(Constant.Int8(left), tpe, _), Expr.Cst(Constant.Int8(right), _, _)) = exps
        Some(Expr.Cst(Constant.Int8((left / right).toByte), tpe, loc0))
      case Int8Op.Rem =>
        val List(Expr.Cst(Constant.Int8(left), tpe, _), Expr.Cst(Constant.Int8(right), _, _)) = exps
        Some(Expr.Cst(Constant.Int8((left % right).toByte), tpe, loc0))

      case Int8Op.Exp =>
        val List(Expr.Cst(Constant.Int8(left), tpe, _), Expr.Cst(Constant.Int8(right), _, _)) = exps
        Some(Expr.Cst(Constant.Int8(Math.pow(left, right).toByte), tpe, loc0))

      case Int8Op.And =>
        val List(Expr.Cst(Constant.Int8(left), tpe, _), Expr.Cst(Constant.Int8(right), _, _)) = exps
        Some(Expr.Cst(Constant.Int8((left & right).toByte), tpe, loc0))

      case Int8Op.Or =>
        val List(Expr.Cst(Constant.Int8(left), tpe, _), Expr.Cst(Constant.Int8(right), _, _)) = exps
        Some(Expr.Cst(Constant.Int8((left | right).toByte), tpe, loc0))

      case Int8Op.Xor =>
        val List(Expr.Cst(Constant.Int8(left), tpe, _), Expr.Cst(Constant.Int8(right), _, _)) = exps
        Some(Expr.Cst(Constant.Int8((left ^ right).toByte), tpe, loc0))

      case Int8Op.Shl =>
        val List(Expr.Cst(Constant.Int8(left), tpe, _), Expr.Cst(Constant.Int32(right), _, _)) = exps
        Some(Expr.Cst(Constant.Int8((left << right).toByte), tpe, loc0))

      case Int8Op.Shr =>
        val List(Expr.Cst(Constant.Int8(left), tpe, _), Expr.Cst(Constant.Int32(right), _, _)) = exps
        Some(Expr.Cst(Constant.Int8((left >> right).toByte), tpe, loc0))

      case Int8Op.Eq =>
        val List(Expr.Cst(Constant.Int8(left), _, _), Expr.Cst(Constant.Int8(right), _, _)) = exps
        Some(Expr.Cst(Constant.Bool(left == right), Type.Bool, loc0))

      case Int8Op.Neq =>
        val List(Expr.Cst(Constant.Int8(left), _, _), Expr.Cst(Constant.Int8(right), _, _)) = exps
        Some(Expr.Cst(Constant.Bool(left != right), Type.Bool, loc0))

      case Int8Op.Lt =>
        val List(Expr.Cst(Constant.Int8(left), _, _), Expr.Cst(Constant.Int8(right), _, _)) = exps
        Some(Expr.Cst(Constant.Bool(left < right), Type.Bool, loc0))

      case Int8Op.Le =>
        val List(Expr.Cst(Constant.Int8(left), _, _), Expr.Cst(Constant.Int8(right), _, _)) = exps
        Some(Expr.Cst(Constant.Bool(left <= right), Type.Bool, loc0))

      case Int8Op.Gt =>
        val List(Expr.Cst(Constant.Int8(left), _, _), Expr.Cst(Constant.Int8(right), _, _)) = exps
        Some(Expr.Cst(Constant.Bool(left > right), Type.Bool, loc0))

      case Int8Op.Ge =>
        val List(Expr.Cst(Constant.Int8(left), _, _), Expr.Cst(Constant.Int8(right), _, _)) = exps
        Some(Expr.Cst(Constant.Bool(left >= right), Type.Bool, loc0))

      case Int16Op.Add =>
        val List(Expr.Cst(Constant.Int16(left), tpe, _), Expr.Cst(Constant.Int16(right), _, _)) = exps
        Some(Expr.Cst(Constant.Int16((left + right).toShort), tpe, loc0))

      case Int16Op.Sub =>
        val List(Expr.Cst(Constant.Int16(left), tpe, _), Expr.Cst(Constant.Int16(right), _, _)) = exps
        Some(Expr.Cst(Constant.Int16((left - right).toShort), tpe, loc0))

      case Int16Op.Mul =>
        val List(Expr.Cst(Constant.Int16(left), tpe, _), Expr.Cst(Constant.Int16(right), _, _)) = exps
        Some(Expr.Cst(Constant.Int16((left * right).toShort), tpe, loc0))

      case Int16Op.Div =>
        val List(Expr.Cst(Constant.Int16(left), tpe, _), Expr.Cst(Constant.Int16(right), _, _)) = exps
        Some(Expr.Cst(Constant.Int16((left / right).toShort), tpe, loc0))
      case Int16Op.Rem =>
        val List(Expr.Cst(Constant.Int16(left), tpe, _), Expr.Cst(Constant.Int16(right), _, _)) = exps
        Some(Expr.Cst(Constant.Int16((left % right).toShort), tpe, loc0))

      case Int16Op.Exp =>
        val List(Expr.Cst(Constant.Int16(left), tpe, _), Expr.Cst(Constant.Int16(right), _, _)) = exps
        Some(Expr.Cst(Constant.Int16(Math.pow(left, right).toShort), tpe, loc0))

      case Int16Op.And =>
        val List(Expr.Cst(Constant.Int16(left), tpe, _), Expr.Cst(Constant.Int16(right), _, _)) = exps
        Some(Expr.Cst(Constant.Int16((left & right).toShort), tpe, loc0))

      case Int16Op.Or =>
        val List(Expr.Cst(Constant.Int16(left), tpe, _), Expr.Cst(Constant.Int16(right), _, _)) = exps
        Some(Expr.Cst(Constant.Int16((left | right).toShort), tpe, loc0))

      case Int16Op.Xor =>
        val List(Expr.Cst(Constant.Int16(left), tpe, _), Expr.Cst(Constant.Int16(right), _, _)) = exps
        Some(Expr.Cst(Constant.Int16((left ^ right).toShort), tpe, loc0))

      case Int16Op.Shl =>
        val List(Expr.Cst(Constant.Int16(left), tpe, _), Expr.Cst(Constant.Int32(right), _, _)) = exps
        Some(Expr.Cst(Constant.Int16((left << right).toShort), tpe, loc0))

      case Int16Op.Shr =>
        val List(Expr.Cst(Constant.Int16(left), tpe, _), Expr.Cst(Constant.Int32(right), _, _)) = exps
        Some(Expr.Cst(Constant.Int16((left >> right).toShort), tpe, loc0))

      case Int16Op.Eq =>
        val List(Expr.Cst(Constant.Int16(left), _, _), Expr.Cst(Constant.Int16(right), _, _)) = exps
        Some(Expr.Cst(Constant.Bool(left == right), Type.Bool, loc0))

      case Int16Op.Neq =>
        val List(Expr.Cst(Constant.Int16(left), _, _), Expr.Cst(Constant.Int16(right), _, _)) = exps
        Some(Expr.Cst(Constant.Bool(left != right), Type.Bool, loc0))

      case Int16Op.Lt =>
        val List(Expr.Cst(Constant.Int16(left), _, _), Expr.Cst(Constant.Int16(right), _, _)) = exps
        Some(Expr.Cst(Constant.Bool(left < right), Type.Bool, loc0))

      case Int16Op.Le =>
        val List(Expr.Cst(Constant.Int16(left), _, _), Expr.Cst(Constant.Int16(right), _, _)) = exps
        Some(Expr.Cst(Constant.Bool(left <= right), Type.Bool, loc0))

      case Int16Op.Gt =>
        val List(Expr.Cst(Constant.Int16(left), _, _), Expr.Cst(Constant.Int16(right), _, _)) = exps
        Some(Expr.Cst(Constant.Bool(left > right), Type.Bool, loc0))

      case Int16Op.Ge =>
        val List(Expr.Cst(Constant.Int16(left), _, _), Expr.Cst(Constant.Int16(right), _, _)) = exps
        Some(Expr.Cst(Constant.Bool(left >= right), Type.Bool, loc0))

      case Int32Op.Add =>
        val List(Expr.Cst(Constant.Int32(left), tpe, _), Expr.Cst(Constant.Int32(right), _, _)) = exps
        Some(Expr.Cst(Constant.Int32(left + right), tpe, loc0))

      case Int32Op.Sub =>
        val List(Expr.Cst(Constant.Int32(left), tpe, _), Expr.Cst(Constant.Int32(right), _, _)) = exps
        Some(Expr.Cst(Constant.Int32(left - right), tpe, loc0))

      case Int32Op.Mul =>
        val List(Expr.Cst(Constant.Int32(left), tpe, _), Expr.Cst(Constant.Int32(right), _, _)) = exps
        Some(Expr.Cst(Constant.Int32(left * right), tpe, loc0))

      case Int32Op.Div =>
        val List(Expr.Cst(Constant.Int32(left), tpe, _), Expr.Cst(Constant.Int32(right), _, _)) = exps
        Some(Expr.Cst(Constant.Int32(left / right), tpe, loc0))

      case Int32Op.Rem =>
        val List(Expr.Cst(Constant.Int32(left), tpe, _), Expr.Cst(Constant.Int32(right), _, _)) = exps
        Some(Expr.Cst(Constant.Int32(left % right), tpe, loc0))

      case Int32Op.Exp =>
        val List(Expr.Cst(Constant.Int32(left), tpe, _), Expr.Cst(Constant.Int32(right), _, _)) = exps
        Some(Expr.Cst(Constant.Int32(Math.pow(left, right).toInt), tpe, loc0))

      case Int32Op.And =>
        val List(Expr.Cst(Constant.Int32(left), tpe, _), Expr.Cst(Constant.Int32(right), _, _)) = exps
        Some(Expr.Cst(Constant.Int32(left & right), tpe, loc0))

      case Int32Op.Or =>
        val List(Expr.Cst(Constant.Int32(left), tpe, _), Expr.Cst(Constant.Int32(right), _, _)) = exps
        Some(Expr.Cst(Constant.Int32(left | right), tpe, loc0))

      case Int32Op.Xor =>
        val List(Expr.Cst(Constant.Int32(left), tpe, _), Expr.Cst(Constant.Int32(right), _, _)) = exps
        Some(Expr.Cst(Constant.Int32(left ^ right), tpe, loc0))

      case Int32Op.Shl =>
        val List(Expr.Cst(Constant.Int32(left), tpe, _), Expr.Cst(Constant.Int32(right), _, _)) = exps
        Some(Expr.Cst(Constant.Int32(left << right), tpe, loc0))

      case Int32Op.Shr =>
        val List(Expr.Cst(Constant.Int32(left), tpe, _), Expr.Cst(Constant.Int32(right), _, _)) = exps
        Some(Expr.Cst(Constant.Int32(left >> right), tpe, loc0))

      case Int32Op.Eq =>
        val List(Expr.Cst(Constant.Int32(left), _, _), Expr.Cst(Constant.Int32(right), _, _)) = exps
        Some(Expr.Cst(Constant.Bool(left == right), Type.Bool, loc0))

      case Int32Op.Neq =>
        val List(Expr.Cst(Constant.Int32(left), _, _), Expr.Cst(Constant.Int32(right), _, _)) = exps
        Some(Expr.Cst(Constant.Bool(left != right), Type.Bool, loc0))

      case Int32Op.Lt =>
        val List(Expr.Cst(Constant.Int32(left), _, _), Expr.Cst(Constant.Int32(right), _, _)) = exps
        Some(Expr.Cst(Constant.Bool(left < right), Type.Bool, loc0))

      case Int32Op.Le =>
        val List(Expr.Cst(Constant.Int32(left), _, _), Expr.Cst(Constant.Int32(right), _, _)) = exps
        Some(Expr.Cst(Constant.Bool(left <= right), Type.Bool, loc0))

      case Int32Op.Gt =>
        val List(Expr.Cst(Constant.Int32(left), _, _), Expr.Cst(Constant.Int32(right), _, _)) = exps
        Some(Expr.Cst(Constant.Bool(left > right), Type.Bool, loc0))

      case Int32Op.Ge =>
        val List(Expr.Cst(Constant.Int32(left), _, _), Expr.Cst(Constant.Int32(right), _, _)) = exps
        Some(Expr.Cst(Constant.Bool(left >= right), Type.Bool, loc0))

      case Int64Op.Add =>
        val List(Expr.Cst(Constant.Int64(left), tpe, _), Expr.Cst(Constant.Int64(right), _, _)) = exps
        Some(Expr.Cst(Constant.Int64(left + right), tpe, loc0))

      case Int64Op.Sub =>
        val List(Expr.Cst(Constant.Int64(left), tpe, _), Expr.Cst(Constant.Int64(right), _, _)) = exps
        Some(Expr.Cst(Constant.Int64(left - right), tpe, loc0))

      case Int64Op.Mul =>
        val List(Expr.Cst(Constant.Int64(left), tpe, _), Expr.Cst(Constant.Int64(right), _, _)) = exps
        Some(Expr.Cst(Constant.Int64(left * right), tpe, loc0))

      case Int64Op.Div =>
        val List(Expr.Cst(Constant.Int64(left), tpe, _), Expr.Cst(Constant.Int64(right), _, _)) = exps
        Some(Expr.Cst(Constant.Int64(left / right), tpe, loc0))

      case Int64Op.Rem =>
        val List(Expr.Cst(Constant.Int64(left), tpe, _), Expr.Cst(Constant.Int64(right), _, _)) = exps
        Some(Expr.Cst(Constant.Int64(left % right), tpe, loc0))

      case Int64Op.Exp =>
        val List(Expr.Cst(Constant.Int64(left), tpe, _), Expr.Cst(Constant.Int64(right), _, _)) = exps
        Some(Expr.Cst(Constant.Int64(Math.pow(left.toDouble, right.toDouble).toLong), tpe, loc0))

      case Int64Op.And =>
        val List(Expr.Cst(Constant.Int64(left), tpe, _), Expr.Cst(Constant.Int64(right), _, _)) = exps
        Some(Expr.Cst(Constant.Int64(left & right), tpe, loc0))

      case Int64Op.Or =>
        val List(Expr.Cst(Constant.Int64(left), tpe, _), Expr.Cst(Constant.Int64(right), _, _)) = exps
        Some(Expr.Cst(Constant.Int64(left | right), tpe, loc0))

      case Int64Op.Xor =>
        val List(Expr.Cst(Constant.Int64(left), tpe, _), Expr.Cst(Constant.Int64(right), _, _)) = exps
        Some(Expr.Cst(Constant.Int64(left ^ right), tpe, loc0))

      case Int64Op.Shl =>
        val List(Expr.Cst(Constant.Int64(left), tpe, _), Expr.Cst(Constant.Int32(right), _, _)) = exps
        Some(Expr.Cst(Constant.Int64(left << right), tpe, loc0))

      case Int64Op.Shr =>
        val List(Expr.Cst(Constant.Int64(left), tpe, _), Expr.Cst(Constant.Int32(right), _, _)) = exps
        Some(Expr.Cst(Constant.Int64(left >> right), tpe, loc0))

      case Int64Op.Eq =>
        val List(Expr.Cst(Constant.Int64(left), _, _), Expr.Cst(Constant.Int64(right), _, _)) = exps
        Some(Expr.Cst(Constant.Bool(left == right), Type.Bool, loc0))

      case Int64Op.Neq =>
        val List(Expr.Cst(Constant.Int64(left), _, _), Expr.Cst(Constant.Int64(right), _, _)) = exps
        Some(Expr.Cst(Constant.Bool(left != right), Type.Bool, loc0))

      case Int64Op.Lt =>
        val List(Expr.Cst(Constant.Int64(left), _, _), Expr.Cst(Constant.Int64(right), _, _)) = exps
        Some(Expr.Cst(Constant.Bool(left < right), Type.Bool, loc0))

      case Int64Op.Le =>
        val List(Expr.Cst(Constant.Int64(left), _, _), Expr.Cst(Constant.Int64(right), _, _)) = exps
        Some(Expr.Cst(Constant.Bool(left <= right), Type.Bool, loc0))

      case Int64Op.Gt =>
        val List(Expr.Cst(Constant.Int64(left), _, _), Expr.Cst(Constant.Int64(right), _, _)) = exps
        Some(Expr.Cst(Constant.Bool(left > right), Type.Bool, loc0))

      case Int64Op.Ge =>
        val List(Expr.Cst(Constant.Int64(left), _, _), Expr.Cst(Constant.Int64(right), _, _)) = exps
        Some(Expr.Cst(Constant.Bool(left >= right), Type.Bool, loc0))

      case StringOp.Concat =>
        val List(Expr.Cst(Constant.Str(left), tpe, _), Expr.Cst(Constant.Str(right), _, _)) = exps
        Some(Expr.Cst(Constant.Str(left + right), tpe, loc0))
    }
  }

  /**
    * Returns a pattern with fresh variables and a substitution mapping the old variables the fresh variables.
    *
    * If a variable is unused it is rewritten to a wildcard pattern.
    */
  private def visitPattern(pat0: Pattern)(implicit flix: Flix): (Pattern, Map[Symbol.VarSym, Symbol.VarSym]) = pat0 match {
    case Pattern.Wild(tpe, loc) =>
      (Pattern.Wild(tpe, loc), Map.empty)

    case Pattern.Var(sym, tpe, occur, loc) => occur match {
      case Occur.Unknown => throw InternalCompilerException("unexpected unknown occurrence information", loc)

      case Occur.Dead =>
        (Pattern.Wild(tpe, loc), Map.empty)

      case Occur.Once
           | Occur.OnceInLambda
           | Occur.OnceInLocalDef
           | Occur.ManyBranch
           | Occur.Many =>
        val freshVarSym = Symbol.freshVarSym(sym)
        (Pattern.Var(freshVarSym, tpe, occur, loc), Map(sym -> freshVarSym))
    }

    case Pattern.Cst(cst, tpe, loc) =>
      (Pattern.Cst(cst, tpe, loc), Map.empty)

    case Pattern.Tag(sym, pats, tpe, loc) =>
      val (ps, varSubsts) = pats.map(visitPattern).unzip
      val varSubst = varSubsts.foldLeft(Map.empty[Symbol.VarSym, Symbol.VarSym])(_ ++ _)
      (Pattern.Tag(sym, ps, tpe, loc), varSubst)

    case Pattern.Tuple(pats, tpe, loc) =>
      val (ps, varSubsts) = pats.map(visitPattern).unzip
      val varSubst = varSubsts.foldLeft(Map.empty[Symbol.VarSym, Symbol.VarSym])(_ ++ _)
      (Pattern.Tuple(ps, tpe, loc), varSubst)

    case Pattern.Record(pats, pat, tpe, loc) =>
      val (ps, varSubsts) = pats.map(visitRecordLabelPattern).unzip
      val (p, varSubst1) = visitPattern(pat)
      val varSubst2 = varSubsts.foldLeft(varSubst1)(_ ++ _)
      (Pattern.Record(ps, p, tpe, loc), varSubst2)
  }

  private def visitRecordLabelPattern(pat0: Pattern.Record.RecordLabelPattern)(implicit flix: Flix): (Pattern.Record.RecordLabelPattern, Map[Symbol.VarSym, Symbol.VarSym]) = pat0 match {
    case Pattern.Record.RecordLabelPattern(label, pat, tpe, loc) =>
      val (p, subst) = visitPattern(pat)
      (Pattern.Record.RecordLabelPattern(label, p, tpe, loc), subst)
  }

  /** Returns a formal param with a fresh symbol and a substitution mapping the old variable the fresh variable. */
  private def freshFormalParam(fp0: MonoAst.FormalParam)(implicit flix: Flix): (MonoAst.FormalParam, Map[Symbol.VarSym, Symbol.VarSym]) = fp0 match {
    case MonoAst.FormalParam(sym, mod, tpe, src, occur, loc) =>
      val freshVarSym = Symbol.freshVarSym(sym)
      val varSubst = Map(sym -> freshVarSym)
      (MonoAst.FormalParam(freshVarSym, mod, tpe, src, occur, loc), varSubst)
  }

  def visitMatchRule(rule: MonoAst.MatchRule, ctx0: LocalContext)(implicit sym0: Symbol.DefnSym, sctx: SharedContext, root: MonoAst.Root, flix: Flix): MonoAst.MatchRule = rule match {
    case MonoAst.MatchRule(pat, guard, exp1) =>
      val (p, varSubst1) = visitPattern(pat)
      val ctx = ctx0.addVarSubsts(varSubst1).addInScopeVars(varSubst1.values.map(sym => sym -> BoundKind.ParameterOrPattern))
      val g = guard.map(visitExp(_, ctx))
      val e1 = visitExp(exp1, ctx)
      MonoAst.MatchRule(p, g, e1)
  }

  def visitCatchRule(rule: MonoAst.CatchRule, ctx0: LocalContext)(implicit sym0: Symbol.DefnSym, sctx: SharedContext, root: MonoAst.Root, flix: Flix): MonoAst.CatchRule = rule match {
    case MonoAst.CatchRule(sym, clazz, exp1) =>
      val freshVarSym = Symbol.freshVarSym(sym)
      val ctx = ctx0.addVarSubst(sym, freshVarSym).addInScopeVar(freshVarSym, BoundKind.ParameterOrPattern)
      val e1 = visitExp(exp1, ctx)
      MonoAst.CatchRule(freshVarSym, clazz, e1)
  }

  def visitHandlerRule(rule: MonoAst.HandlerRule, ctx0: LocalContext)(implicit sym0: Symbol.DefnSym, sctx: SharedContext, root: MonoAst.Root, flix: Flix): MonoAst.HandlerRule = rule match {
    case MonoAst.HandlerRule(op, fparams, exp1) =>
      val (fps, varSubsts) = fparams.map(freshFormalParam).unzip
      val ctx = ctx0.addVarSubsts(varSubsts).addInScopeVars(fps.map(fp => fp.sym -> BoundKind.ParameterOrPattern))
      val e1 = visitExp(exp1, ctx)
      MonoAst.HandlerRule(op, fps, e1)
  }

  def visitJvmMethod(method: MonoAst.JvmMethod, ctx0: LocalContext)(implicit sym0: Symbol.DefnSym, sctx: SharedContext, root: MonoAst.Root, flix: Flix): MonoAst.JvmMethod = method match {
    case MonoAst.JvmMethod(ident, fparams, exp, retTpe, eff1, loc1) =>
      val (fps, varSubsts) = fparams.map(freshFormalParam).unzip
      val ctx = ctx0.addVarSubsts(varSubsts).addInScopeVars(fps.map(fp => fp.sym -> BoundKind.ParameterOrPattern))
      val e = visitExp(exp, ctx)
      MonoAst.JvmMethod(ident, fps, e, retTpe, eff1, loc1)
  }

  /**
    * Performs beta-reduction, binding `exps` as let-bindings.
    *
    * It is the responsibility of the caller to first visit `exps` and provide a substitution from the definition site
    * of `exp`. The caller must not visit `exp`.
    *
    * [[bindArgs]] creates a series of let-bindings
    * {{{
    *   let sym1 = exp1;
    *   // ...
    *   let symn = expn;
    *   exp
    * }}}
    * where `symi` is the symbol of the i-th formal parameter and `exp` is the body of the function.
    *
    * Lastly, it visits the top-most let-binding, thus possibly removing the bindings.
    */
  private def bindArgs(exp: Expr, fparams: List[FormalParam], exps: List[Expr], loc: SourceLocation, ctx0: LocalContext)(implicit sym0: Symbol.DefnSym, sctx: SharedContext, root: MonoAst.Root, flix: Flix): Expr = {
    val letBindings = fparams.zip(exps).foldRight(exp) {
      case ((fparam, arg), acc) =>
        val eff = Type.mkUnion(arg.eff, acc.eff, loc)
        Expr.Let(fparam.sym, arg, acc, acc.tpe, eff, fparam.occur, loc)
    }
    visitExp(letBindings, ctx0.withEmptyExprCtx)
  }

  /**
    * Returns `true` if the `exp` should be inlined at the calling occurrence site
    * for a variable that has occurrence information [[Occur.Many]].
    */
  private def shouldInlineMulti(exp: Expr, ctx0: LocalContext)(implicit root: MonoAst.Root): Boolean = {
    noSizeIncrease(exp, ctx0) || (someBenefit(exp, ctx0) && (isTrivial(exp) || smallEnough(exp, ctx0)))
  }

  /**
    * Returns true if `exp0` is a lambda and the size of its definition is less than or equal to
    * the size of the call.
    */
  private def noSizeIncrease(exp0: Expr, ctx0: LocalContext)(implicit root: MonoAst.Root): Boolean = exp0 match {
    case Expr.Lambda(_, exp, _, _) =>
      val bodySize = size(exp)
      val args = collectLambdaArgs(exp0, ctx0.exprCtx, ctx0)
      val callSize = args.map(_._1).map(size).sum
      bodySize <= callSize

    case _ => false
  }

  private def someBenefit(exp0: Expr, ctx0: LocalContext): Boolean = exp0 match {
    case Expr.Lambda(_, _, _, _) =>
      argsAreReducible(exp0, ctx0.exprCtx, ctx0) || isFullyApplied(exp0, ctx0.exprCtx)

    case Expr.ApplyAtomic(AtomicOp.Tag(_), _, _, _, _) => ctx0.exprCtx match {
      case ExprContext.MatchCtx(_, _, _) => true
      case _ => false
    }
    case Expr.ApplyAtomic(AtomicOp.Tuple, _, _, _, _) => ctx0.exprCtx match {
      case ExprContext.MatchCtx(_, _, _) => true
      case _ => false
    }

    case _ => false
  }

  private def smallEnough(exp0: Expr, ctx0: LocalContext): Boolean = exp0 match {
    case Expr.Lambda(_, exp, _, _) =>
      val bodySize = size(exp)
      val args = collectLambdaArgs(exp, ctx0.exprCtx, ctx0)
      val callSize = args.map(_._1).map(size).sum
      val argDiscount = computeArgDiscount(args.map { case (_, bk, ctx) => (bk, ctx) })
      val resultDiscount = computeResultDiscount(exp)
      val keenness = 1.5
      val threshold = 8
      bodySize - callSize - (argDiscount * keenness + resultDiscount * keenness) <= threshold

    case _ => false
  }

  @tailrec
  private def argsAreReducible(exp0: Expr, exprCtx: ExprContext, ctx0: LocalContext): Boolean = (exp0, exprCtx) match {
    case (Expr.Lambda(_, body, _, _), ExprContext.AppCtx(arg, _, ctx)) =>
      !isTrivial(arg) || letBoundVariable(arg, ctx0) || argsAreReducible(body, ctx, ctx0)
    case _ => false
  }

  private def letBoundVariable(expr: MonoAst.Expr, ctx0: LocalContext): Boolean = expr match {
    case Expr.Var(sym, _, _) => ctx0.varSubst.get(sym) match {
      case Some(freshSym) => ctx0.inScopeVars.get(freshSym) match {
        case Some(BoundKind.ParameterOrPattern) => false
        case Some(BoundKind.LetBound(_, _)) => true
        case None => false
      }
      case None => false
    }
    case _ => false
  }

  @tailrec
  private def isFullyApplied(exp0: Expr, exprCtx: ExprContext): Boolean = (exp0, exprCtx) match {
    case (Expr.Lambda(_, exp, _, _), ExprContext.AppCtx(_, _, ctx)) => isFullyApplied(exp, ctx)
    case (Expr.Lambda(_, _, _, _), _) => false
    case _ => true
  }

  private def computeArgDiscount(args: List[(BoundKind, ExprContext)]): Int = args.map {
    case (BoundKind.LetBound(_, _), ExprContext.AppCtx(_, _, _)) => 1
    case (BoundKind.LetBound(_, _), ExprContext.MatchCtx(_, _, _)) => 1
    case _ => 0
  }.sum

  private def computeResultDiscount(exp: Expr): Int = {
    val res = resultExp(exp)
    if (isTrivial(res) || isLambda(res)) 1 else 0
  }

  /**
    * Returns a tuple of the arg expression, its BoundKind ([[BoundKind.ParameterOrPattern]] if not applicable) and its own context.
    */
  private def collectLambdaArgs(exp0: Expr, ectx0: ExprContext, ctx0: LocalContext): List[(Expr, BoundKind, ExprContext)] = (exp0, ectx0) match {
    case (Expr.Lambda(_, body, _, _), ExprContext.AppCtx(exp@Expr.Var(sym, _, _), _, ctx)) =>
      (exp, getEvaluationState(sym, ctx0), ctx) :: collectLambdaArgs(body, ctx, ctx0)
    case (Expr.Lambda(_, body, _, _), ExprContext.AppCtx(exp, _, ctx)) =>
      (exp, BoundKind.ParameterOrPattern, ctx) :: collectLambdaArgs(body, ctx, ctx0)
    case _ => Nil
  }

  /** Returns the [[BoundKind]] for `sym`. The symbol must be in scope, otherwise an exception is thrown. */
  private def getEvaluationState(sym: Symbol.VarSym, ctx0: LocalContext): BoundKind = ctx0.varSubst.get(sym) match {
    case Some(freshSym) => ctx0.inScopeVars.getOrElse(freshSym, BoundKind.ParameterOrPattern)
    case None => BoundKind.ParameterOrPattern
  }

  /**
    * Returns the number of subexpressions in `exp0` including itself.
    */
  private def size(exp0: Expr): Int = exp0 match {
    case Expr.Cst(_, _, _) => 1
    case Expr.Var(_, _, _) => 1
    case Expr.Lambda(_, exp, _, _) => size(exp) + 1
    case Expr.ApplyAtomic(_, exps, _, _, _) => exps.map(size).sum + 1
    case Expr.ApplyClo(exp1, exp2, _, _, _) => size(exp1) + size(exp2) + 3
    case Expr.ApplyDef(_, exps, _, _, _, _) => exps.map(size).sum + 3
    case Expr.ApplyLocalDef(_, exps, _, _, _) => exps.map(size).sum + 3
    case Expr.Let(_, exp1, exp2, _, _, _, _) => size(exp1) + size(exp2) + 1
    case Expr.LocalDef(_, _, exp1, exp2, _, _, _, _) => size(exp1) + size(exp2) + 1
    case Expr.Scope(_, _, exp, _, _, _) => size(exp) + 1
    case Expr.IfThenElse(exp1, exp2, exp3, _, _, _) => size(exp1) + size(exp2) + size(exp3) + 1
    case Expr.Stm(exp1, exp2, _, _, _) => size(exp1) + size(exp2) + 1
    case Expr.Discard(exp, _, _) => size(exp) + 1
    case Expr.Match(exp, rules, _, _, _) => size(exp) + rules.map(_.exp).map(size).sum + 1
    case Expr.VectorLit(exps, _, _, _) => exps.map(size).sum
    case Expr.VectorLoad(exp1, exp2, _, _, _) => size(exp1) + size(exp2) + 1
    case Expr.VectorLength(exp, _) => size(exp) + 1
    case Expr.Ascribe(exp, _, _, _) => size(exp) + 1
    case Expr.Cast(exp, _, _, _) => size(exp) + 1
    case Expr.TryCatch(exp, rules, _, _, _) => size(exp) + rules.map(_.exp).map(size).sum + 1
    case Expr.RunWith(exp, _, rules, _, _, _) => size(exp) + rules.map(_.exp).map(size).sum + 1
    case Expr.Do(_, exps, _, _, _) => exps.map(size).sum + 1
    case Expr.NewObject(_, _, _, _, methods, _) => methods.map(_.exp).map(size).sum + 1
  }

  @tailrec
  private def resultExp(exp0: Expr): Expr = exp0 match {
    case Expr.Let(_, _, exp2, _, _, _, _) => resultExp(exp2)
    case Expr.LocalDef(_, _, _, exp2, _, _, _, _) => resultExp(exp2)
    case Expr.Scope(_, _, exp, _, _, _) => resultExp(exp)
    case Expr.Stm(_, exp2, _, _, _) => resultExp(exp2)
    case Expr.Ascribe(exp, _, _, _) => resultExp(exp)
    case Expr.Cast(exp, _, _, _) => resultExp(exp)
    case exp => exp
  }

  /**
    *
    * Returns `true` if
    *   - the local context shows that we are not currently inlining and
    *   - `defn` does not refer to itself and
    *   - it is either a higher-order function with a known lambda as argument or
    *   - it is a direct call with simple arguments to another function or
    *   - the body is simple.
    *
    * It is the responsibility of the caller to visit `exps` first.
    *
    * @param defn the definition of the function.
    * @param exps the arguments to the function.
    * @param ctx0 the local context.
    */
  private def shouldInlineDef(defn: MonoAst.Def, exps: List[Expr], ctx0: LocalContext): Boolean = {
    !ctx0.currentlyInlining && !defn.spec.defContext.isSelfRef &&
      (isSingleCall(defn.exp) || isSimple(defn.exp) || hasKnownLambda(exps))
  }

  /**
    * Returns `true` if there exists [[Expr.Lambda]] in `exps`.
    */
  private def hasKnownLambda(exps: List[Expr]): Boolean = {
    exps.exists(isLambda)
  }

  /**
    * Returns a [[Some]] with the definition of `sym` if it is let-bound and the [[shouldInlineVar]] predicate holds.
    * The caller should visit the expression with an empty `subst`, i.e., `visitExp(exp, ctx0.withSubst(Map.empty))`.
    *
    * Returns [[None]] otherwise.
    *
    * Throws an error if `sym` is not in scope. This also implies that it is the responsibility of the caller
    * to replace any symbol occurrence with the corresponding fresh symbol in the variable substitution.
    */
  private def useSiteInline(sym: Symbol.VarSym, ctx0: LocalContext)(implicit root: MonoAst.Root): Option[Expr] = {
    ctx0.inScopeVars.get(sym) match {
      case Some(BoundKind.LetBound(exp, occur)) if shouldInlineVar(sym, exp, occur, ctx0) =>
        Some(exp)

      case Some(_) =>
        None

      case None =>
        throw InternalCompilerException(s"unexpected evaluated var not in scope $sym", sym.loc)
    }
  }

  /**
    * Returns `true` if `exp` is pure and should be inlined at the occurrence of `sym`.
    *
    * A lambda should be inlined if it has occurrence information [[Occur.OnceInLambda]] or [[Occur.OnceInLocalDef]].
    */
  private def shouldInlineVar(sym: Symbol.VarSym, exp: Expr, occur: Occur, ctx0: LocalContext)(implicit root: MonoAst.Root): Boolean = (occur, exp.eff) match {
    case (Occur.Dead, _) => throw InternalCompilerException(s"unexpected call site inline of dead variable $sym", exp.loc)
    case (Occur.Once, Type.Pure) => throw InternalCompilerException(s"unexpected call site inline of pre-inlined variable $sym", exp.loc)
    case (Occur.OnceInLambda, Type.Pure) => (isTrivial(exp) || isLambda(exp)) && someBenefit(exp, ctx0)
    case (Occur.OnceInLocalDef, Type.Pure) => (isTrivial(exp) || isLambda(exp)) && someBenefit(exp, ctx0)
    case (Occur.ManyBranch, Type.Pure) => shouldInlineMulti(exp, ctx0)
    case (Occur.Many, Type.Pure) => (isTrivial(exp) || isLambda(exp)) && shouldInlineMulti(exp, ctx0)
    case _ => false // Impure so do not move expression
  }

  /** Returns `true` if `exp` is [[Expr.Cst]] and the constant is not a [[Constant.Regex]]. */
  private def isCst(exp: Expr): Boolean = exp match {
    case Expr.Cst(Constant.Regex(_), _, _) => false
    case Expr.Cst(_, _, _) => true
    case _ => false
  }

  /** Returns `true` if `exp` is [[Expr.Lambda]]. */
  def isLambda(exp: MonoAst.Expr): Boolean = exp match {
    case Expr.Lambda(_, _, _, _) => true
    case _ => false
  }

  /**
    * Returns `true` if `exp0` is considered a trivial expression.
    *
    * A trivial expression is one of the following:
    *   - [[Expr.Var]]
    *   - Any expression where [[isCst]] holds.
    *
    * A pure and trivial expression can always be inlined even without duplicating work.
    */
  private def isTrivial(exp0: Expr): Boolean = exp0 match {
    case Expr.Var(_, _, _) => true
    case exp => isCst(exp)
  }

  /**
    * Returns `true` if `exp0` is considered a literal.
    *
    * A simple expression is one of the following:
    *   - [[Expr.Lambda]]
    *   - [[Expr.ApplyAtomic]] with [[AtomicOp.Unary]] where for all operands [[isCst]] holds.
    *   - [[Expr.ApplyAtomic]] with [[AtomicOp.Binary]] where for all operands [[isCst]] holds.
    *   - [[Expr.ApplyAtomic]] with [[AtomicOp.Tuple]] where for all subexpressions either [[isCst]] or [[isLiteral]] holds.
    *   - [[Expr.ApplyAtomic]] with [[AtomicOp.Tag]] where for all subexpressions either [[isCst]] or [[isLiteral]] holds.
    *   - Any expression where [[isCst]] holds.
    *
    * A simple expression can be reduced by beta reduction, constant folding or deforestation.
    */
  private def isLiteral(exp0: Expr): Boolean = exp0 match {
    case Expr.Lambda(_, _, _, _) => true
    case Expr.ApplyAtomic(AtomicOp.Unary(_), exps, _, _, _) => exps.forall(isCst)
    case Expr.ApplyAtomic(AtomicOp.Binary(_), exps, _, _, _) => exps.forall(isCst)
    case Expr.ApplyAtomic(AtomicOp.Tuple, exps, _, _, _) => exps.forall(e => isCst(e) || isLiteral(e))
    case Expr.ApplyAtomic(AtomicOp.Tag(_), exps, _, _, _) => exps.forall(e => isCst(e) || isLiteral(e))
    case exp => isCst(exp)
  }

  /**
    * Returns `true` if `exp0` is considered simple.
    *
    * A simple expression is one of the following:
    *   - [[Expr.Lambda]]
    *   - [[Expr.ApplyAtomic]] with [[AtomicOp.Unary]] where for all operands [[isTrivial]] holds.
    *   - [[Expr.ApplyAtomic]] with [[AtomicOp.Binary]] where for all operands [[isTrivial]] holds.
    *   - [[Expr.ApplyAtomic]] with [[AtomicOp.Tuple]] where for all subexpressions either [[isTrivial]] or [[isSimple]] holds.
    *   - [[Expr.ApplyAtomic]] with [[AtomicOp.Tag]] where for all subexpressions either [[isTrivial]] or [[isSimple]] holds.
    *   - Any expression where [[isTrivial]] holds.
    *
    * A simple expression can be reduced by beta reduction, constant folding or deforestation.
    */
  private def isSimple(exp0: Expr): Boolean = exp0 match {
    case Expr.Lambda(_, _, _, _) => true
    case Expr.ApplyAtomic(AtomicOp.Unary(_), exps, _, _, _) => exps.forall(isTrivial)
    case Expr.ApplyAtomic(AtomicOp.Binary(_), exps, _, _, _) => exps.forall(isTrivial)
    case Expr.ApplyAtomic(AtomicOp.Tuple, exps, _, _, _) => exps.forall(e => isTrivial(e) || isSimple(e))
    case Expr.ApplyAtomic(AtomicOp.Tag(_), exps, _, _, _) => exps.forall(e => isTrivial(e) || isSimple(e))
    case Expr.Cast(exp, _, _, _) => isSimple(exp)
    case Expr.Ascribe(exp, _, _, _) => isSimple(exp)
    case exp => isTrivial(exp)
  }

  /**
    * Returns `true` if `exp0` is a single call expression.
    *
    * A single call is expression is one of the following:
    *   - [[Expr.ApplyClo]] where [[isSimple]] holds for all subexpressions.
    *   - [[Expr.ApplyDef]] where [[isSimple]] holds for all subexpressions.
    *   - [[Expr.LocalDef]] where the following expression is [[Expr.ApplyLocalDef]] and
    *     [[isSimple]] holds for all subexpressions of the latter.
    *   - [[Expr.ApplyAtomic]] with [[AtomicOp.InvokeMethod]] where for all subexpressions [[isSimple]] holds.
    *   - [[Expr.ApplyAtomic]] with [[AtomicOp.InvokeConstructor]] where for all subexpressions [[isSimple]] holds.
    *   - [[Expr.ApplyAtomic]] with [[AtomicOp.InvokeStaticMethod]] where for all subexpressions [[isSimple]] holds.
    *   - [[Expr.Cast]] where [[isSingleCall]] holds for the subexpression.
    *
    * This captures functions that simply forward to another function with possibly additional simple arguments.
    * Inlining such a function reduces code size.
    */
  @tailrec
  private def isSingleCall(exp0: Expr): Boolean = exp0 match {
    case Expr.ApplyClo(exp1, exp2, _, _, _) => isSimple(exp1) && isSimple(exp2)
    case Expr.ApplyDef(_, exps, _, _, _, _) => exps.forall(isSimple)
    case Expr.LocalDef(_, _, _, Expr.ApplyLocalDef(_, exps, _, _, _), _, _, _, _) => exps.forall(isSimple)
    case Expr.ApplyAtomic(AtomicOp.InvokeMethod(_), exps, _, _, _) => exps.forall(isSimple)
    case Expr.ApplyAtomic(AtomicOp.InvokeConstructor(_), exps, _, _, _) => exps.forall(isSimple)
    case Expr.ApplyAtomic(AtomicOp.InvokeStaticMethod(_), exps, _, _, _) => exps.forall(isSimple)
    case Expr.Cast(exp, _, _, _) => isSingleCall(exp)
    case _ => false
  }

  /**
    * Tries to unify exp with each rule in `rules`.
    * If exp successfully unifies with a rule, each variable in the pattern is let-bound from left to right
    * and assigned to the expression that was unified with.
    *
    * In some cases, unification may completely abort:
    *   - If there is a non-trivial guard since the value of the guard cannot be determined.
    *   - If there is a constant pattern and a non-constant expression in the scrutinee in that subterm since the value cannot be determined without constant folding.
    *
    * `exp` must be visited before calling [[tryDeforestation]]. `rules` must NOT be visited before calling [[tryDeforestation]].
    */
  private def tryDeforestation(exp: Expr, rules: List[MonoAst.MatchRule], tpe: Type, eff: Type, loc: SourceLocation, ctx0: LocalContext)(implicit sym0: Symbol.DefnSym, sctx: SharedContext, root: MonoAst.Root, flix: Flix): Expr = {
    unifyFirstRule(exp, rules) match {
      case None =>
        val rs = rules.map(visitMatchRule(_, ctx0))
        Expr.Match(exp, rs, tpe, eff, loc)

      case Some((bindings, rule)) =>
        sctx.changed.putIfAbsent(sym0, ())
        val letExp = bindings.foldRight(rule.exp) {
          case ((sym, BoundKind.LetBound(e, occur)), acc) =>
            val eff = Type.mkUnion(e.eff, acc.eff, loc)
            Expr.Let(sym, e, acc, acc.tpe, eff, occur, e.loc)
        }
        visitExp(letExp, ctx0.withEmptyExprCtx)
    }
  }

  /**
    * Attempts to unify `exp` with each rule in `rules` from left to right and returns
    * the first successful rule along with each unified variable and expression pair.
    *
    * If unification failed or aborted then [[None]] is returned.
    */
  @tailrec
  private def unifyFirstRule(exp: Expr, rules: List[MonoAst.MatchRule])(implicit flix: Flix): Option[(List[(Symbol.VarSym, BoundKind.LetBound)], MonoAst.MatchRule)] = rules match {
    case Nil =>
      None

    case r :: rs => r.guard match {
      case Some(Expr.Cst(Constant.Bool(false), _, _)) =>
        unifyFirstRule(exp, rs)

      case None | Some(Expr.Cst(Constant.Bool(true), _, _)) => unifyPattern(exp, r.pat) match {
        case UnificationResult.Abort =>
          None

        case UnificationResult.Failure =>
          unifyFirstRule(exp, rs)

        case UnificationResult.Success(bindings) =>
          Some((bindings, r))
      }

      case Some(_) =>
        None
    }
  }

  /**
    * Attempts to unify `exp0` with `pat0`.
    *
    * Returns [[UnificationResult.Abort]] to signal that no further attempts at unification should be made.
    * This can happen when `pat0` is a constant and `exp0` is not yet fully reduced.
    *
    */
  private def unifyPattern(exp0: Expr, pat0: Pattern)(implicit flix: Flix): UnificationResult = (exp0, pat0) match {
    case (Expr.Cast(exp, _, _, _), _) =>
      unifyPattern(exp, pat0)

    case (Expr.Ascribe(exp, _, _, _), _) =>
      unifyPattern(exp, pat0)

    case (_, Pattern.Wild(_, _)) =>
      UnificationResult.SuccessEmpty

    case (exp, Pattern.Var(sym, _, occur, _)) =>
      UnificationResult.Success(List(sym -> BoundKind.LetBound(exp, occur)))

    case (Expr.Cst(cst1, _, _), Pattern.Cst(cst2, _, _)) =>
      if (cst1 == cst2) {
        UnificationResult.SuccessEmpty
      } else {
        UnificationResult.Failure
      }

    case (_, Pattern.Cst(_, _, _)) =>
      UnificationResult.Abort

    case (Expr.ApplyAtomic(AtomicOp.Tag(sym1), exps, _, _, _), Pattern.Tag(sym2, pats, _, _)) =>
      if (sym1 == sym2.sym) {
        exps.zip(pats).map { case (e, p) => unifyPattern(e, p) }
          .foldLeft(UnificationResult.SuccessEmpty)(UnificationResult.combine)
      } else {
        UnificationResult.Failure
      }

    case (Expr.ApplyAtomic(AtomicOp.Tuple, exps, _, _, _), Pattern.Tuple(pats, _, _)) =>
      exps.zip(pats).map { case (e, p) => unifyPattern(e, p) }
        .foldLeft(UnificationResult.SuccessEmpty)(UnificationResult.combine)

    case (Expr.Cst(Constant.RecordEmpty, _, _), Pattern.Record(Nil, Pattern.Cst(Constant.RecordEmpty, _, _), _, _)) =>
      UnificationResult.SuccessEmpty

    case _ =>
      UnificationResult.Failure
  }

  /** Represents the range of a substitution from variables to expressions. */
  sealed private trait SubstRange

  private object SubstRange {

    /**
      * An expression that will be inlined but is not yet visited.
      * We must capture the substitution from its definition site to ensure
      * we substitute the variables the inliner may have previously decided
      * to inline.
      */
    case class SuspendedExpr(exp: MonoAst.Expr, subst: Map[Symbol.VarSym, SubstRange]) extends SubstRange

    /** An expression that will be inlined but has already been visited. */
    case class DoneExpr(exp: MonoAst.Expr) extends SubstRange

  }

  /** Contains information on a variable's definition. */
  private sealed trait BoundKind

  private object BoundKind {

    /** Variable is bound by either a parameter or a pattern. Its value is unknown. */
    object ParameterOrPattern extends BoundKind

    /** The right-hand side of a let-bound variable along with its occurrence information. */
    case class LetBound(expr: MonoAst.Expr, occur: Occur) extends BoundKind

  }

  /** Represents the compile-time evaluation state and is used like a stack. */
  private sealed trait ExprContext

  private object ExprContext {

    /** The empty evaluation context. */
    case object Empty extends ExprContext

    /** Function application context. */
    case class AppCtx(expr: Expr, subst: Map[Symbol.VarSym, SubstRange], ctx: ExprContext) extends ExprContext

    /** Match-case expression context. */
    case class MatchCtx(rules: List[MonoAst.MatchRule], subst: Map[Symbol.VarSym, SubstRange], ctx: ExprContext) extends ExprContext

  }

  /**
    * A wrapper class for all the different inlining environments.
    *
    * @param varSubst          a substitution on variables to variables.
    * @param subst             a substitution on variables to expressions.
    * @param inScopeVars       a set of variables considered to be in scope.
    * @param exprCtx           a compile-time evaluation context.
    * @param currentlyInlining a flag denoting whether the current traversal is part of an inline-expansion process.
    */
  private case class LocalContext(varSubst: Map[Symbol.VarSym, Symbol.VarSym], subst: Map[Symbol.VarSym, SubstRange], inScopeVars: Map[Symbol.VarSym, BoundKind], exprCtx: ExprContext, currentlyInlining: Boolean) {

    /** Returns a [[LocalContext]] where [[exprCtx]] has been overwritten with [[ExprContext.Empty]]. */
    def withEmptyExprCtx: LocalContext = {
      this.copy(exprCtx = ExprContext.Empty)
    }

    /**
      * Returns a [[LocalContext]] where [[exprCtx]] has been overwritten with `ctx`.
      * Thus, it is the caller's responsibility to save the current expression context.
      */
    def addExprCtx(ctx: ExprContext): LocalContext = {
      this.copy(exprCtx = ctx)
    }

    /** Returns a [[LocalContext]] with the mapping `old -> fresh` added to [[varSubst]]. */
    def addVarSubst(old: Symbol.VarSym, fresh: Symbol.VarSym): LocalContext = {
      this.copy(varSubst = this.varSubst + (old -> fresh))
    }

    /** Returns a [[LocalContext]] with the mappings of `mappings` added to [[varSubst]]. */
    def addVarSubsts(mappings: Map[Symbol.VarSym, Symbol.VarSym]): LocalContext = {
      this.copy(varSubst = this.varSubst ++ mappings)
    }

    /** Returns a [[LocalContext]] with the mappings of `mappings` added to [[varSubst]]. */
    def addVarSubsts(mappings: List[Map[Symbol.VarSym, Symbol.VarSym]]): LocalContext = {
      this.copy(varSubst = mappings.foldLeft(this.varSubst)(_ ++ _))
    }

    /** Returns a [[LocalContext]] with the mapping `sym -> substExpr` added to [[subst]]. */
    def addSubst(sym: Symbol.VarSym, substExpr: SubstRange): LocalContext = {
      this.copy(subst = this.subst + (sym -> substExpr))
    }

    /** Returns a [[LocalContext]] with [[subst]] overwritten by `newSubst`. */
    def withSubst(newSubst: Map[Symbol.VarSym, SubstRange]): LocalContext = {
      this.copy(subst = newSubst)
    }

    /** Returns a [[LocalContext]] with the mapping `sym -> boundKind` added to [[inScopeVars]]. */
    def addInScopeVar(sym: Symbol.VarSym, boundKind: BoundKind): LocalContext = {
      this.copy(inScopeVars = this.inScopeVars + (sym -> boundKind))
    }

    /** Returns a [[LocalContext]] with the mappings of `mappings` added to [[inScopeVars]]. */
    def addInScopeVars(mappings: Iterable[(Symbol.VarSym, BoundKind)]): LocalContext = {
      this.copy(inScopeVars = this.inScopeVars ++ mappings)
    }

    /** Returns a [[LocalContext]] where [[currentlyInlining]] is set to `true`. */
    def enableInliningMode: LocalContext = {
      this.copy(currentlyInlining = true)
    }
  }

  /** Represents the result of unifying the scrutinee of a [[Expr.Match]] expression with a pattern. */
  private sealed trait UnificationResult

  private object UnificationResult {

    val SuccessEmpty: UnificationResult = UnificationResult.Success(List.empty)

    /**
      * Represents an unrecoverable failure.
      * The caller should then no longer attempt any further unification with the expression.
      */
    case object Abort extends UnificationResult

    /**
      * Represents a "normal" unification failure.
      * The caller may attempt to unify the expression with another pattern.
      */
    case object Failure extends UnificationResult

    /**
      * Represents a successful unification.
      *
      * @param bindings contains the unified variable and expression pairs that should be let-bound.
      */
    case class Success(bindings: List[(Symbol.VarSym, BoundKind.LetBound)]) extends UnificationResult

    /**
      * Combines `ur1` and `ur2`.
      *
      * If either is [[UnificationResult.Abort]] then [[UnificationResult.Abort]] is returned.
      * Then if either is [[UnificationResult.Failure]] then [[UnificationResult.Failure]] is returned.
      * If both `ur1` and `ur2` are [[UnificationResult.Success]] then their lists are combined.
      *
      */
    def combine(ur1: UnificationResult, ur2: UnificationResult): UnificationResult = (ur1, ur2) match {
      case (UnificationResult.Abort, _) =>
        UnificationResult.Abort

      case (_, UnificationResult.Abort) =>
        UnificationResult.Abort

      case (UnificationResult.Failure, _) =>
        UnificationResult.Failure

      case (_, UnificationResult.Failure) =>
        UnificationResult.Failure

      case (UnificationResult.Success(bindings1), UnificationResult.Success(bindings2)) =>
        UnificationResult.Success(bindings1 ::: bindings2)
    }
  }

  private object LocalContext {

    /** Returns the empty context with `currentlyInlining` set to `false`. */
    val Empty: LocalContext = LocalContext(Map.empty, Map.empty, Map.empty, ExprContext.Empty, currentlyInlining = false)

  }

  private object SharedContext {

    /** Returns a fresh [[SharedContext]]. */
    def mk(): SharedContext = new SharedContext(new ConcurrentHashMap())

  }

  /**
    * A globally shared thread-safe context.
    *
    * @param changed the set of symbols of changed functions.
    */
  private case class SharedContext(changed: ConcurrentHashMap[Symbol.DefnSym, Unit])

}
