mod Talpin.Data {

pub enum Constraint(Set[(EVar, Effect)]) with Coerce

instance ToString[Constraint] {
    pub def toString(k: Constraint): String = Constraint.toString(k)
}


instance Add[Constraint] {
    pub def add(k1: Constraint, k2: Constraint): Constraint = Constraint.combine(k1, k2)
}

mod Constraint {
    use Talpin.Data.Effect
    use Talpin.Data.FreeVarSet
    use Talpin.Data.EVar

    pub def empty(): Constraint =
        Constraint(Set.empty())

    pub def isEmpty(k: Constraint): Bool =
        k |> coerce |> Set.isEmpty

    pub def coerce(k: Constraint): Set[(EVar, Effect)] = {
        let Constraint(s) = k;
        s
    }

    pub def constraint(upperBound: {upperBound = EVar}, ef: Effect): Constraint =
        Constraint(Set.singleton((upperBound#upperBound, ef)))

    pub def combine(k1: Constraint, k2: Constraint): Constraint =
        Set.union(coerce(k1), coerce(k2)) |> Constraint

    pub def fv(k: Constraint): FreeVarSet = {
        k |> coerce |> Set.foldLeft(acc -> match (z, ef) -> FreeVarSet.singleEVar(z) + Effect.fv(ef) + acc, FreeVarSet.empty())
    }

    pub def simplify(k: Constraint): Constraint = {
        k |> coerce |> Set.map(match (x, ef) -> (x, Effect.simplify(ef))) |> Constraint
    }

    pub def toString(k: Constraint): String = {
        let inner = toStrings(k) |> List.join(", ");
        "{${inner}}"
    }

    pub def toStrings(k: Constraint): List[String] =
        k |> coerce |> Set.toList |> List.map(match (x, y) -> "${x} ⊒ ${y}")

}

}
mod Talpin.Data {

pub enum Effect with Eq, Order {
    case Empty
    case Init(Reg)
    case Read(Reg)
    case Write(Reg)
    case Union(Effect, Effect)
    case Var(EVar)

    case Eff(String)
}

instance ToString[Effect] {
    pub def toString(ef: Effect): String = Effect.toString(ef)
}

instance Add[Effect] {
    pub def add(ef1: Effect, ef2: Effect): Effect = Effect.Union(ef1, ef2)
}

mod Effect {
    use Talpin.Data.FreeVarSet
    use Talpin.Data.Reg

    use Functor.map
    use Option.getWithDefault

    pub def toString(effect: Effect): String = match effect {
        case Empty => "Ø"
        case Init(p) => "init(${p})"
        case Read(p) => "read(${p})"
        case Write(p) => "write(${p})"
        case Union(p, p1) => "${toString(p)} ∪ ${toString(p1)}"
        case Var(z) => "${z}"

        case Eff(ef) => ef
    }

    pub def union(l: i): Effect \ Iterable.Aef[i] with Iterable[i] where Iterable.Elm[i] ~ Effect = region local {
        // TODO: don't materialize
        l |> Iterable.iterator(local) |> Iterator.toList |> List.toNel |> map(Nel.reduceLeft(Union)) |> getWithDefault(Empty)
    }

    pub def fv(effect: Effect): FreeVarSet = match effect {
        case Empty => FreeVarSet.empty()
        case Init(p) => Reg.fv(p)
        case Read(p) => Reg.fv(p)
        case Write(p) => Reg.fv(p)
        case Union(ef, ef1) => fv(ef) + fv(ef1)
        case Var(x) => FreeVarSet.singleEVar(x)

        case Eff(_) => FreeVarSet.empty()
    }

    pub def simplify(effect: Effect): Effect = region local {
        let workList = MutPriorityQueue.empty(local);
        MutPriorityQueue.enqueue(effect, workList);

        let seen = MutSet.empty(local);
        def loop() = match MutPriorityQueue.dequeue(workList) {
            case Some(ef) =>
                match ef {
                    case Empty => ()
                    case Init(_) => seen |> MutSet.add(ef)
                    case Read(_) => seen |> MutSet.add(ef)
                    case Write(_) => seen |> MutSet.add(ef)
                    case Union(e, e1) =>
                        MutPriorityQueue.enqueue(e, workList);
                        MutPriorityQueue.enqueue(e1, workList)
                    case Var(_) => seen |> MutSet.add(ef)

                    case Eff(_) => seen |> MutSet.add(ef)
                };
                loop()
            case None => ()
        };
        loop();
        union(seen)
    }

    pub def remove(toRemove: {toRemove = Effect}, effect: Effect): Effect = match effect {
        case Empty => Empty
        case Init(p) => if (toRemove#toRemove == Init(p)) Empty else Init(p)
        case Read(p) => if (toRemove#toRemove == Read(p)) Empty else Read(p)
        case Write(p) => if (toRemove#toRemove == Write(p)) Empty else Write(p)
        case Union(ef, ef1) => Union(remove(toRemove, ef), remove(toRemove, ef1))
        case Var(x) => if (toRemove#toRemove == Var(x)) Empty else Var(x)

        case Eff(s) => if (toRemove#toRemove == Eff(s)) Empty else Eff(s)
    }

}

}
mod Talpin.Data {
    use Coerce.coerce

pub enum Env(Map[Id, Value])

instance Indexable[Env] {
    type Idx = Id
    type Elm = Value
    type Aef = KeyNotFound

    pub def get(env: Env, id: Id): Value \ KeyNotFound = Env.lookup(id, env)
}

instance Coerce[Env] {
    type Out = Map[Id, Value]

    pub def coerce(env: Env): Map[Id, Value] = Env.coerce(env)
}


mod Env {
    use Talpin.Data.Id
    use Talpin.Data.Value

    pub def empty(): Env =
        Env(Map.empty())

    pub def lookupOpt(id: Id, env: Env): Option[Value] =
        env |> coerce |> Map.get(id)

    pub def lookup(id: Id, env: Env): Value \ KeyNotFound =
        match lookupOpt(id, env) {
            case None => KeyNotFound.keyNotFound("key not found: ${id}")
            case Some(v) => v
        }

    pub def coerce(env: Env): Map[Id, Value] =
        match env { case Env(m) => m }

    pub def coerceMap(f: Map[Id, Value] -> Map[Id, Value] \ ef, env: Env): Env \ ef =
        env |> coerce |> f |> Env

    pub def unbind(id: Id, env: Env): Env =
        env |> coerceMap(Map.remove(id))

    pub def bind(id: Id, v: Value, env: Env): Env =
        env |> coerceMap(Map.insert(id, v))

}

}
mod Talpin.Data {
    use Coerce.coerce

    pub enum EVar(String) with Eq, Coerce, Order

    instance ToString[EVar] {
        pub def toString(x: EVar): String = EVar.toString(x)
    }

    mod EVar {
        pub def toString(x: EVar): String = coerce(x)
    }

}
mod Talpin.Data {

pub enum Exp {
    /// x
    case Var(String)
    /// (e e')
    case App(Exp, Exp)
    /// (lambda (x) e)
    case Abs(String, Exp)
    /// (rec (f x) e)
    case Rec(String, String, Exp)
    /// (let (x e) e')
    case Let(String, Exp, Exp)
    /// (new e)
    case New(Exp)
    /// (get e)
    case Get(Exp)
    /// (set e e')
    case Set(Exp, Exp)

    case BoolCst(Bool)
    case If(Exp, Exp, Exp)
    case IntCst(Int32)
    case Add(Exp, Exp)
    case Sub(Exp, Exp)
    case Eq(Exp, Exp)

    case Do(String)
    case Run(Exp, String)
}

instance ToString[Exp] {
    pub def toString(e: Exp): String = Exp.toString(e)
}

mod Exp {

    pub def expansive(exp: Exp): Bool = match exp {
        case Rec(_, _, _) => false
        case Var(_) => false
        case Abs(_, _) => false

        case New(_) => true
        case Get(_) => true
        case Set(_, _) => true
        case App(_, _) => true

        case Let(_, e, e1) => expansive(e) or expansive(e1)

        case BoolCst(_) => false
        case IntCst(_) => false

        case If(_, _, _) => true
        case Add(_, _) => true
        case Sub(_, _) => true
        case Eq(_, _) => true

        case Do(_) => true
        case Run(_, _) => true
    }


    pub def toString(exp: Exp): String = match exp {
        case Var(x) => "${x}"
        case App(e, e1) => "(${e} ${e1})"
        case Abs(x, e) => "(lambda (${x}) ${e})"
        case Rec(f, x, e) => "(rec (${f} ${x}) ${e})"
        case Let(x, e, e1) => "(let (${x} ${e}) ${e1})"
        case New(e) => "(new ${e})"
        case Get(e) => "(get ${e})"
        case Set(e, e1) => "(set ${e} ${e1})"

        case BoolCst(b) => "${b}"
        case If(e, e1, e2) => "(if ${e} ${e1} ${e2})"
        case IntCst(i) => "${i}"
        case Add(e, e1) => "(+ ${e} ${e1})"
        case Sub(e, e1) => "(- ${e} ${e1})"
        case Eq(e, e1) => "(== ${e} ${e1})"

        case Do(e) => "(do ${e})"
        case Run(e, ef) => "(run ${e} ${ef})"
    }

}

}
mod Talpin.Data {

pub enum FreeVarSet {
    case Sets(Set[TVar], Set[RVar], Set[EVar])
    case Empty
}

instance Add[FreeVarSet] {
    pub def add(fv: FreeVarSet, fv1: FreeVarSet): FreeVarSet = FreeVarSet.union(fv, fv1)
}

instance Sub[FreeVarSet] {
    pub def sub(fv: FreeVarSet, fv1: FreeVarSet): FreeVarSet = FreeVarSet.difference(fv, fv1)
}

instance Coerce[FreeVarSet] {
    type Out = {tVars = Set[TVar], rVars = Set[RVar], eVars = Set[EVar]}

    pub def coerce(fv: FreeVarSet): {tVars = Set[TVar], rVars = Set[RVar], eVars = Set[EVar]} = FreeVarSet.coerce(fv)
}


mod FreeVarSet {
    use Talpin.Data.TVar
    use Talpin.Data.RVar
    use Talpin.Data.EVar
    pub def empty(): FreeVarSet =
        Empty

    pub def coerce(fv: FreeVarSet): {tVars = Set[TVar], rVars = Set[RVar], eVars = Set[EVar]} = match fv {
        case Sets(t, r, e) => {tVars = t, rVars = r, eVars = e}
        case Empty => {tVars = Set.empty(), rVars = Set.empty(), eVars = Set.empty()}
    }

    pub def singleTVar(x: TVar): FreeVarSet =
        Sets(Set#{x}, Set.empty(), Set.empty())

    pub def containsTVar(x: TVar, fv: FreeVarSet): Bool = match fv {
        case Sets(t, _, _) => Set.memberOf(x, t)
        case Empty => false
    }

    pub def removeTVars(s: Set[TVar], fv: FreeVarSet): FreeVarSet = match fv {
        case Sets(t, r, e) => Sets(Set.difference(t, s), r, e)
        case Empty => Empty
    }

    pub def singleRVar(x: RVar): FreeVarSet =
        Sets(Set.empty(), Set#{x}, Set.empty())

    pub def containsRVar(x: RVar, fv: FreeVarSet): Bool = match fv {
        case Sets(_, r, _) => Set.memberOf(x, r)
        case Empty => false
    }

    pub def removeRVars(s: Set[RVar], fv: FreeVarSet): FreeVarSet = match fv {
        case Sets(t, r, e) => Sets(t, Set.difference(r, s), e)
        case Empty => Empty
    }

    pub def singleEVar(x: EVar): FreeVarSet =
        Sets(Set.empty(), Set.empty(), Set#{x})

    pub def containsEVar(x: EVar, fv: FreeVarSet): Bool = match fv {
        case Sets(_, _, e) => Set.memberOf(x, e)
        case Empty => false
    }

    pub def removeEVars(s: Set[EVar], fv: FreeVarSet): FreeVarSet = match fv {
        case Sets(t, r, e) => Sets(t, r, Set.difference(e, s))
        case Empty => Empty
    }

    pub def union(fv: FreeVarSet, fv1: FreeVarSet): FreeVarSet = match (fv, fv1) {
        case (Sets(t, r, e), Sets(t1, r1, e1)) =>
            Sets(t `Set.union` t1, r `Set.union` r1, e `Set.union` e1)
        case (Sets(_, _, _), Empty) => fv
        case (Empty, Sets(_, _, _)) => fv1
        case (Empty, Empty) => Empty
    }

    pub def difference(fv: FreeVarSet, fv1: FreeVarSet): FreeVarSet = match (fv, fv1) {
        case (Sets(t, r, e), Sets(t1, r1, e1)) =>
            Sets(t `Set.difference` t1, r `Set.difference` r1, e `Set.difference` e1)
        case (Sets(_, _, _), Empty) => fv
        case (Empty, _) => Empty
    }

}

}
mod Talpin.Data {

pub type alias Id = String

}
mod Talpin.Data {

pub type alias RefLoc = Int32

}
mod Talpin.Data {

// Region is already used in Flix
pub enum Reg with Eq, Order {
    case RegConst(Int32)
    case RegVar(RVar)
}

instance ToString[Reg] {
    pub def toString(p: Reg): String = Reg.toString(p)
}

mod Reg {
    use Talpin.Data.FreeVarSet

    pub def toString(p: Reg): String = match p {
        case RegConst(i) => "cst#${i}"
        case RegVar(x) => "${x}"
    }

    pub def fv(p: Reg): FreeVarSet = match p {
        case RegConst(_) => FreeVarSet.empty()
        case RegVar(x) => FreeVarSet.singleRVar(x)
    }

}

}
mod Talpin.Data {

pub enum RuntimeEffect with Eq, Order, ToString {
    case Init(RefLoc)
    case Read(RefLoc)
    case Write(RefLoc)

    case Eff(String)
}

}
mod Talpin.Data {
    use Coerce.coerce

    pub enum RVar(String) with Eq, Coerce, Order

    instance ToString[RVar] {
        pub def toString(x: RVar): String = RVar.toString(x)
    }

    mod RVar {
        pub def toString(x: RVar): String = coerce(x)
    }

}
mod Talpin.Data {

pub type alias Store = Map[RefLoc, Value]

mod Store {
    use Add.add
    use Functor.map
    use Option.getWithDefault

    use Talpin.Data.RefLoc
    use Talpin.Data.Value

    pub def store(l: RefLoc, v: Value, s: Store): Store =
        Map.insert(l, v, s)

    pub def newLoc(s: Store): RefLoc =
        s |> Map.maximumKey |> map(fst) |> getWithDefault(-1) |> add(1)

    pub def remove(l: RefLoc, s: Store): Store =
        Map.remove(l, s)

    pub def empty(): Store =
        Map.empty()

}

}
mod Talpin.Data {

pub enum Subst(Map[TVar, Type], Map[RVar, Reg], Map[EVar, Effect])

instance ToString[Subst] {
    pub def toString(subst: Subst): String = Subst.toString(subst)
}

trait SubstApp[t] {
    type Out: Type
    pub def app(s: Subst, x: t): SubstApp.Out[t]
}

instance SubstApp[TVar] {
    type Out = Type
    pub def app(s: Subst, x: TVar): Type = Subst.appTVar(s, x)
}

instance SubstApp[RVar] {
    type Out = Reg
    pub def app(s: Subst, x: RVar): Reg = Subst.appRVar(s, x)
}

instance SubstApp[EVar] {
    type Out = Effect
    pub def app(s: Subst, x: EVar): Effect = Subst.appEVar(s, x)
}

instance SubstApp[Reg] {
    type Out = Reg
    pub def app(s: Subst, x: Reg): Reg = Subst.appReg(s, x)
}

instance SubstApp[Type] {
    type Out = Type
    pub def app(s: Subst, x: Type): Type = Subst.appType(s, x)
}

instance SubstApp[Effect] {
    type Out = Effect
    pub def app(s: Subst, x: Effect): Effect = Subst.appEffect(s, x)
}

instance SubstApp[Constraint] {
    type Out = Constraint
    pub def app(s: Subst, x: Constraint): Constraint = Subst.appConstraint(s, x)
}

instance SubstApp[TyScheme] {
    type Out = TyScheme
    pub def app(s: Subst, x: TyScheme): TyScheme = Subst.appTyScheme(s, x)
}

instance SubstApp[Map[k, v]] with SubstApp[v] {
    type Out = Map[k, SubstApp.Out[v]]
    pub def app(s: Subst, x: Map[k, v]): Map[k, SubstApp.Out[v]] =
        Map.map(SubstApp.app(s), x)
}

trait SubstBind[t] {
    type Value: Type
    pub def bind(k: t, v: SubstBind.Value[t], s: Subst): Subst
}

instance SubstBind[TVar] {
    type Value = Type
    pub def bind(x: TVar, t: Type, s: Subst): Subst = Subst.bindTVar(x, t, s)
}

instance SubstBind[RVar] {
    type Value = Reg
    pub def bind(x: RVar, p: Reg, s: Subst): Subst = Subst.bindRVar(x, p, s)
}

instance SubstBind[EVar] {
    type Value = Effect
    pub def bind(x: EVar, effect: Effect, s: Subst): Subst = Subst.bindEVar(x, effect, s)
}

mod SubstBind {
    use Talpin.Data.Subst
    use Talpin.Data.SubstBind

    pub def bindAll(l: List[(k, v)], s: Subst): Subst with SubstBind[k] where SubstBind.Value[k] ~ v =
        (s, l) ||> List.foldLeft(acc -> match (x, t) -> SubstBind.bind(x, t, acc))
}

mod Subst {
    use Option.getWithDefault

    use Talpin.Data.Type
    use Talpin.Data.Reg
    use Talpin.Data.Effect
    use Talpin.Data.TyScheme
    use Talpin.Data.TyEnv
    use Talpin.Data.Constraint
    use Talpin.Data.TVar
    use Talpin.Data.RVar
    use Talpin.Data.EVar
    use Talpin.Data.SubstApp.app

    pub def empty(): Subst =
        Subst(Map.empty(), Map.empty(), Map.empty())

    pub def isEmpty(s: Subst): Bool = {
        let Subst(t, r, e) = s;
        Map.isEmpty(t) and Map.isEmpty(r) and Map.isEmpty(e)
    }

    pub def singleTVar(x: TVar, t: Type): Subst =
        empty() |> bindTVar(x, t)

    pub def singleRVar(x: RVar, t: Reg): Subst =
        empty() |> bindRVar(x, t)

    pub def singleEVar(x: EVar, t: Effect): Subst =
        empty() |> bindEVar(x, t)

    pub def id(): Subst =
        empty()

    pub def compose(inner: {inner = Subst}, outer: Subst): Subst = {
        if (isEmpty(inner#inner)) outer
        else if (isEmpty(outer)) inner#inner
        else {
            let Subst(tInner, rInner, eInner) = inner#inner;
            let tMap = tInner |> Map.map(appType(outer));
            let rMap = rInner |> Map.map(appReg(outer));
            let eMap = eInner |> Map.map(appEffect(outer));

            let Subst(tOuter, rOuter, eOuter) = outer;
            // Note that Map.union is left-biased.
            let tMap1 = Map.union(tMap, tOuter);
            let rMap1 = Map.union(rMap, rOuter);
            let eMap1 = Map.union(eMap, eOuter);
            Subst(tMap1, rMap1, eMap1)
        }
    }

    pub def bindTVar(x: TVar, t: Type, subst: Subst): Subst = {
        let Subst(tMap, rMap, eMap) = subst;
        Subst(tMap |> Map.insert(x, t), rMap, eMap)
    }

    pub def bindTVarAll(l: List[(TVar, Type)], subst: Subst): Subst =
        (subst, l) ||> List.foldLeft(acc -> match (x, t) -> bindTVar(x, t, acc))

    pub def unbindTVar(x: TVar, subst: Subst): Subst = {
        let Subst(tMap, rMap, eMap) = subst;
        Subst(tMap |> Map.remove(x), rMap, eMap)
    }

    pub def appTVar(subst: Subst, x: TVar): Type = {
        let Subst(tMap, _, _) = subst;
        Map.get(x, tMap) |> Option.getWithDefault(Type.Var(x))
    }

    pub def bindRVar(x: RVar, p: Reg, subst: Subst): Subst = {
        let Subst(tMap, rMap, eMap) = subst;
        Subst(tMap, rMap |> Map.insert(x, p), eMap)
    }

    pub def bindRVarAll(l: List[(RVar, Reg)], subst: Subst): Subst =
        (subst, l) ||> List.foldLeft(acc -> match (x, t) -> bindRVar(x, t, acc))

    pub def unbindRVar(x: RVar, subst: Subst): Subst = {
        let Subst(tMap, rMap, eMap) = subst;
        Subst(tMap, rMap |> Map.remove(x), eMap)
    }

    pub def appRVar(subst: Subst, x: RVar): Reg = {
        let Subst(_, rMap, _) = subst;
        Map.get(x, rMap) |> Option.getWithDefault(Reg.RegVar(x))
    }

    pub def bindEVar(x: EVar, ef: Effect, subst: Subst): Subst = {
        let Subst(tMap, rMap, eMap) = subst;
        Subst(tMap, rMap, eMap |> Map.insert(x, ef))
    }

    pub def bindEVarAll(l: List[(EVar, Effect)], subst: Subst): Subst =
        (subst, l) ||> List.foldLeft(acc -> match (x, t) -> bindEVar(x, t, acc))

    pub def unbindEVar(x: EVar, subst: Subst): Subst = {
        let Subst(tMap, rMap, eMap) = subst;
        Subst(tMap, rMap, eMap |> Map.remove(x))
    }

    pub def appEVar(subst: Subst, x: EVar): Effect = {
        let Subst(_, _, eMap) = subst;
        Map.get(x, eMap) |> Option.getWithDefault(Effect.Var(x))
    }

    pub def appEVarDirect(subst: Subst, x: EVar): Option[Effect] = {
        let Subst(_, _, eMap) = subst;
        Map.get(x, eMap)
    }

    pub def appType(subst: Subst, tpe: Type): Type = match tpe {
        case Type.Unitt => Type.Unitt
        case Type.Var(x) => app(subst, x)
        case Type.Ref(p, t) => Type.Ref(app(subst, p), app(subst, t))
        case Type.Arrow(t, ef, t1) => Type.Arrow(app(subst, t), app(subst, ef), app(subst, t1))

        case Type.Bool => Type.Bool
        case Type.Int => Type.Int
    }

    pub def appReg(subst: Subst, p: Reg): Reg = match p {
        case Reg.RegConst(_) => p
        case Reg.RegVar(x) => app(subst, x)
    }

    pub def appEffect(subst: Subst, effect: Effect): Effect = match effect {
        case Effect.Empty => Effect.Empty
        case Effect.Init(p) => Effect.Init(app(subst, p))
        case Effect.Read(p) => Effect.Read(app(subst, p))
        case Effect.Write(p) => Effect.Write(app(subst, p))
        case Effect.Union(ef, ef1) => app(subst, ef) + app(subst, ef1)
        case Effect.Var(x) => app(subst, x)

        case Effect.Eff(_) => effect
    }

    pub def appTyEnv(subst: Subst, env: TyEnv): TyEnv =
        TyEnv.map(appTyScheme(subst), env)

    pub def appTyScheme(subst: Subst, scheme: TyScheme): TyScheme = region local {
        let {tVars, rVars, eVars, tpe = t, k} = coerce(scheme);
        let acc = Ref.fresh(local, subst);
        tVars |> Set.forEach(x -> acc |> Ref.transform(unbindTVar(x)));
        rVars |> Set.forEach(x -> acc |> Ref.transform(unbindRVar(x)));
        eVars |> Set.forEach(x -> acc |> Ref.transform(unbindEVar(x)));
        let t1 = app(Ref.get(acc), t);
        let k1 = app(Ref.get(acc), k);
        TyScheme.TyScheme({tpe = t1, k = k1 | coerce(scheme)})
    }

    pub def appConstraint(subst: Subst, k: Constraint): Constraint = {
        k |> coerce |> Set.map(match (x, ef) -> {
            match app(subst, x) {
                case Effect.Var(x1) => (x1, appEffect(subst)(ef))
                case other => bug!(other |> ToString.toString) // paper says it should only be inferred variables, so unreachable
            }
        }) |> Constraint.Constraint
    }

    pub def toString(subst: Subst): String = {
        let inner = toStrings(subst) |> List.join(", ");
        "[${inner}]"
    }

    pub def toStrings(subst: Subst): List[String] = region local {
        let Subst(ts, rs, efs) = subst;
        let tIt = ts |> Map.iterator(local) |> Iterator.map(match (x, t) -> "${x} -> ${t}");
        let rIt = rs |> Map.iterator(local) |> Iterator.map(match (x, r) -> "${x} -> ${r}");
        let eIt = efs |> Map.iterator(local) |> Iterator.map(match (x, ef) -> "${x} -> ${ef}");
        (tIt `Iterator.append` rIt `Iterator.append` eIt) |> Iterator.toList
    }

    pub def simplify(subst: Subst): Subst = {
        let Subst(ts, rs, efs) = subst;
        Subst(ts |> Map.map(Type.simplify), rs, efs |> Map.map(Effect.simplify))
    }

}

}
mod Talpin.Data {

pub enum Trace(Set[RuntimeEffect]) with ToString

instance Coerce[Trace] {
    type Out = Set[RuntimeEffect]

    pub def coerce(f: Trace): Set[RuntimeEffect] = Trace.coerce(f)
}

instance Add[Trace] {
    pub def add(f1: Trace, f2: Trace): Trace = Trace.union(f1, f2)
}

mod Trace {
    use Talpin.Data.RuntimeEffect

    pub def empty(): Trace = Set.empty() |> Trace

    pub def singleton(ef: RuntimeEffect): Trace =
        ef |> Set.singleton |> Trace

    pub def insert(ef: RuntimeEffect, f: Trace): Trace =
        f |> coerceMap(Set.insert(ef))

    pub def union(f1: Trace, f2: Trace): Trace =
        Set.union(f1 |> coerce, f2 |> coerce) |> Trace

    pub def coerce(f: Trace): Set[RuntimeEffect] =
        match f { case Trace(s) => s }

    pub def coerceMap(g: Set[RuntimeEffect] -> Set[RuntimeEffect] \ ef, f: Trace): Trace \ ef =
        f |> coerce |> g |> Trace

    pub def remove(ef: RuntimeEffect, f: Trace): Trace = {
        f |> coerceMap(Set.remove(ef))
    }

}

}
mod Talpin.Data {
    use Coerce.coerce

    pub enum TVar(String) with Eq, Coerce, Order

    instance ToString[TVar] {
        pub def toString(x: TVar): String = TVar.toString(x)
    }

    mod TVar {
        pub def toString(x: TVar): String = coerce(x)
    }

}
mod Talpin.Data {

pub type alias TyEnv = Map[Id, TyScheme]

mod TyEnv {
    use Talpin.Data.TyScheme
    use Talpin.Data.Id
    use Talpin.Data.Constraint
    use Talpin.Data.Type
    use Talpin.Data.FreeVarSet

    use Coerce.coerce

    pub def empty(): TyEnv =
        Map.empty()

    pub def map(f: TyScheme -> TyScheme \ ef, env: TyEnv): TyEnv \ ef =
        Map.map(f, env)

    pub def bindType(x: Id, t: Type, env: TyEnv): TyEnv =
        Map.insert(x, TyScheme.fromType(t), env)

    pub def bind(x: Id, s: TyScheme, env: TyEnv): TyEnv =
        Map.insert(x, s, env)

    pub def unbind(x: Id, env: TyEnv): TyEnv =
        Map.remove(x, env)

    pub def fv(env: TyEnv): FreeVarSet =
        (FreeVarSet.empty(), env) ||> Map.foldLeft(acc -> s -> acc + TyScheme.fv(s))

}

}
mod Talpin.Data {

pub enum Type {
    case Unitt
    case Var(TVar)
    case Ref(Reg, Type)
    case Arrow(Type, Effect, Type)

    case Bool
    case Int
}

instance ToString[Type] {
    pub def toString(t: Type): String = Type.toString(t)
}

mod Type {
    use Talpin.Data.Effect
    use Talpin.Data.FreeVarSet
    use Talpin.Data.Reg

    pub def toString(tpe: Type): String = match tpe {
        case Unitt => "unit"
        case Var(x) => "${x}"
        case Ref(p, t) => "ref_${p}(${toString(t)})"
        case Arrow(Arrow(it, ief, it1), Effect.Empty, t1) => "(${toString(Arrow(it, ief, it1))}) -> ${toString(t1)}"
        case Arrow(t, Effect.Empty, t1) => "${toString(t)} -> ${toString(t1)}"
        case Arrow(Arrow(it, ief, it1), ef, t1) => "(${toString(Arrow(it, ief, it1))}) ->[${ef}] ${toString(t1)}"
        case Arrow(t, ef, t1) => "${toString(t)} ->[${ef}] ${toString(t1)}"

        case Bool => "boolean"
        case Int => "integer"
    }

    pub def fv(tpe: Type): FreeVarSet = match tpe {
        case Unitt => FreeVarSet.empty()
        case Var(x) => FreeVarSet.singleTVar(x)
        case Ref(p, t) => Reg.fv(p) + fv(t)
        case Arrow(t, ef, t1) => fv(t) + Effect.fv(ef) + fv(t1)

        case Bool => FreeVarSet.empty()
        case Int => FreeVarSet.empty()
    }

    pub def simplify(tpe: Type): Type = match tpe {
        case Unitt => Unitt
        case Var(_) => tpe
        case Ref(p, t) => Ref(p, simplify(t))
        case Arrow(t, ef, t1) => Arrow(simplify(t), Effect.simplify(ef), simplify(t1))

        case Bool => Bool
        case Int => Int
    }

}

}
mod Talpin.Data {

pub enum TyScheme({
    tVars = Set[TVar],
    rVars = Set[RVar],
    eVars = Set[EVar],
    tpe = Type,
    k = Constraint
}) with Coerce

instance ToString[TyScheme] {
    pub def toString(x: TyScheme): String = TyScheme.toString(x)
}

mod TyScheme {
    use Coerce.coerce
    use Talpin.Data.Type
    use Talpin.Data.Constraint
    use Talpin.Data.FreeVarSet
    use Talpin.Data.TyScheme.TyScheme

    pub def fromType(t: Type): TyScheme = TyScheme({
        tVars = Set.empty(),
        rVars = Set.empty(),
        eVars = Set.empty(),
        tpe = t,
        k = Constraint.empty()
    })

    pub def genType(t: Type, k: Constraint, fv: FreeVarSet): TyScheme ={
        let {tVars, rVars, eVars} = coerce(fv);
        TyScheme({tVars = tVars, rVars = rVars, eVars = eVars, tpe = t, k = k})
    }

    pub def fv(s: TyScheme): FreeVarSet = {
        let {tVars, rVars, eVars, tpe, k} = coerce(s);
        (Type.fv(tpe) + Constraint.fv(k))
        |> FreeVarSet.removeTVars(tVars)
        |> FreeVarSet.removeRVars(rVars)
        |> FreeVarSet.removeEVars(eVars)
    }

    pub def isEmpty(s: TyScheme): Bool = {
        let {tVars, rVars, eVars, tpe = _, k} = coerce(s);
        Set.isEmpty(tVars) and Set.isEmpty(rVars) and Set.isEmpty(eVars) and Constraint.isEmpty(k)
    }

    pub def toString(s: TyScheme): String = {
        if (isEmpty(s)) coerce(s)#tpe |> ToString.toString
        else {
            let {tVars, rVars, eVars, tpe, k} = coerce(s);
            let vars = List.map(ToString.toString, Set.toList(tVars)) `List.append` List.map(ToString.toString, Set.toList(rVars)) `List.append` List.map(ToString.toString, Set.toList(eVars));
            "∀${vars |> List.join(", ")}.    ${tpe}    with ${k}"
        }
    }

    pub def simplify(s: TyScheme): TyScheme = {
        let {tVars, rVars, eVars, tpe, k} = coerce(s);
        TyScheme({tVars = tVars, rVars = rVars, eVars = eVars, tpe = tpe |> Type.simplify, k = k |> Constraint.simplify})
    }

}

}
mod Talpin.Data {

pub enum Value {
    case U
    case Ref(RefLoc)
    case Closure(Id, Exp, Unit -> Env)

    case BoolVal(Bool)
    case IntVal(Int32)
}

instance ToString[Value] {
    pub def toString(v: Value): String = Value.toString(v)
}


mod Value {
    use Talpin.Data.Id
    use Talpin.Data.Exp
    use Talpin.Data.Env
    use Talpin.Data.RefLoc

    pub def getRef(v: Value): RefLoc \ Abort = match v {
        case Ref(l) => l
        case other => Abort.abort("'${other}' is not a ref.")
    }

    pub def getClosure(v: Value): (Id, Exp, Env) \ Abort = match v {
        case Closure(x, e, env) => (x, e, env())
        case other => Abort.abort("'${other}' is not a closure.")
    }

    pub def getBool(v: Value): Bool \ Abort = match v {
        case BoolVal(b) => b
        case other => Abort.abort("'${other}' is not a bool.")
    }

    pub def getInt(v: Value): Int32 \ Abort = match v {
        case IntVal(i) => i
        case other => Abort.abort("'${other}' is not an int.")
    }

    pub def toString(v: Value): String = match v {
        case U => "u"
        case Ref(loc) => "loc_${loc}"
        case Closure(x, e, _env) => "<${x}, ${e}, _>"
        case BoolVal(b) => "${b}"
        case IntVal(i) => "${i}"
    }

}

}
mod Talpin.Examples {
    use Talpin.BigStep.eval
    use Talpin.Data.Constraint
    use Talpin.Data.Effect
    use Talpin.Data.Env
    use Talpin.Data.Exp
    use Talpin.Data.Store
    use Talpin.Data.Trace
    use Talpin.Data.TyEnv
    use Talpin.Data.Type
    use Talpin.Data.Value
    use Talpin.EffectSolver
    use Talpin.FreshName
    use Talpin.Parsing.Parser.parse
    use Talpin.Reconstruction.reconstruct
    use Util.Util.runAll

    pub def exp01(): Exp \ IO = runAll(() -> parse(" ( (  lambda  (  x  )  (  new   x  )  )  (  lambda ( q )  q ) ) "))

    pub def runExp01(): (Value, Trace, Store) \ IO = runAll(() -> {
        eval(Store.empty(), Env.empty(), exp01())
    })

    pub def exp02(): Exp \ IO = runAll(() -> parse(List.join(" ", List#{
        "(let (mul (lambda (x) (lambda (y)",
            "(let (sum (new 0))",
            "(let (inner (rec (loop n)",
                "(if (== n 0) (get sum)",
                    "(let (tmpA (set sum (+ (get sum) y)))",
                    "(loop (- n 1))",
                    ")",
                ")))",
            "(inner x)",
            "))",
        ")))",
        "((mul 6) 8)",
        ")"
    })))

    pub def runExp02(): (Value, Trace, Store) \ IO = runAll(() -> {
        eval(Store.empty(), Env.empty(), exp02())
    })

    pub def exp03(): Exp \ IO = runAll(() -> parse(List.join(" ", List#{
        "(lambda (initial)",
            "(let (counter (new initial))",
                "(lambda (inc)",
                    "(begin (set counter (+ (get counter) inc))",
                            "(get counter)))))"
    })))

    pub def runExp03(): (Value, Trace, Store) \ IO = runAll(() -> {
        eval(Store.empty(), Env.empty(), exp03())
    })

    pub def inferExp03(): (Type, Effect) \ IO = runAll(() -> {
        let (_, t, ef) = reconstruct(exp03()) |> EffectSolver.solvFull;
        (t, ef)
    })

}
mod Talpin.Parsing.FlixParser {
    use Talpin.Data.Exp
    use Util.StringCursor
    use Util.StringCursor.peekChar
    use Util.StringCursor.nthChar
    use Util.StringCursor.remaining
    use Util.StringCursor.eat
    use Util.StringCursor.at
    use Util.StringCursor.take
    use Util.StringCursor.dropWhile
    use Util.StringCursor.dropWhile!

    pub def parse(s: String): Exp \ Abort = region local {
        let sc = StringCursor.mk(local, '&', s);
        let e = parseExp(sc, canSemi = true);
        whiteSpace(sc);
        expect("&", "parse", sc);
        e
    }

    def parseExp(sc: StringCursor[r], canSemi: {canSemi = Bool}): Exp \ r + Abort = {
        let e0 = parseExpSimp(sc);
        def loop(e) = {
            if (eat("(", sc)) {
                let e1 = parseExp(sc, canSemi = true);
                whiteSpace(sc);
                expect(")", "parseExp", sc);
                loop(Exp.App(e, e1))
            } else {
                whiteSpace(sc);
                if (at(";", sc) and canSemi#canSemi) {
                    expect(";", "parseExp", sc);
                    let e1 = parseExp(sc, canSemi);
                    loop(Exp.Let("_", e, e1))
                } else if (eat("+", sc)) {
                    let e1 = parseExp(sc, canSemi);
                    loop(Exp.Add(e, e1))
                } else if (eat("-", sc)) {
                    let e1 = parseExp(sc, canSemi);
                    loop(Exp.Sub(e, e1))
                } else if (eat("==", sc)) {
                    let e1 = parseExp(sc, canSemi);
                    loop(Exp.Eq(e, e1))
                } else e
            }
        };
        loop(e0)
    }

    def parseExpSimp(sc: StringCursor[r]): Exp \ r + Abort = {
        def ept(s, h) = expect(s, "parseExpSimp:${h#inner}", sc);
        def ws!(h) = whiteSpace!("parseExpSimp:${h}", sc);
        whiteSpace(sc);
        if (eat("(", sc)) { // (e)
            let e = parseExp(sc, canSemi = true);
            whiteSpace(sc);
            ept(")", inner = "paren");
            e
        } else if (eat("\\", sc)) { // \x -> e
            let x = parseName(sc);
            whiteSpace(sc);
            ept("->", inner = "lambda");
            let e = parseExp(sc, canSemi = false);
            Exp.Abs(x, e)
        } else if (eat("rec", sc)) { // rec f \x -> e
            ws!("rec");
            let f = parseName(sc);
            whiteSpace(sc);
            ept("\\", inner = "rec");
            let x = parseName(sc);
            whiteSpace(sc);
            ept("->", inner = "rec");
            let e = parseExp(sc, canSemi = false);
            Exp.Rec(f, x, e)
        } else if (eat("let", sc)) { // let x = e; e1
            ws!("let");
            let x = parseName(sc);
            whiteSpace(sc);
            ept("=", inner = "let");
            let e = parseExp(sc, canSemi = false);
            whiteSpace(sc);
            ept(";", inner = "let");
            let e1 = parseExp(sc, canSemi = true);
            Exp.Let(x, e, e1)
        } else if (eat("new", sc)) { // new(e)
            ept("(", inner = "new");
            let e = parseExp(sc, canSemi = true);
            whiteSpace(sc);
            ept(")", inner = "new");
            Exp.New(e)
        } else if (eat("get", sc)) { // get(e)
            ept("(", inner = "get");
            let e = parseExp(sc, canSemi = true);
            whiteSpace(sc);
            ept(")", inner = "get");
            Exp.Get(e)
        } else if (eat("set", sc)) { // set(e, e1)
            ept("(", inner = "set");
            let e = parseExp(sc, canSemi = true);
            whiteSpace(sc);
            ept(",", inner = "set");
            let e1 = parseExp(sc, canSemi = true);
            whiteSpace(sc);
            ept(")", inner = "set");
            Exp.Set(e, e1)
        } else if (eat("if", sc)) { // if (e) e1 else e2
            whiteSpace(sc);
            ept("(", inner = "if");
            let e = parseExp(sc, canSemi = true);
            whiteSpace(sc);
            ept(")", inner = "if");
            let e1 = parseExp(sc, canSemi = true);
            whiteSpace(sc);
            ept("else", inner = "if");
            ws!("if");
            let e2 = parseExp(sc, canSemi = false);
            Exp.If(e, e1, e2)
        } else if (eat("do", sc)) { // do Effect
            ws!("do");
            let ef = parseName(sc);
            Exp.Do(ef)
        } else if (eat("run", sc)) { // run e Effect
            ws!("run");
            let e = parseExp(sc, canSemi = false);
            whiteSpace(sc);
            let ef = parseName(sc);
            Exp.Run(e, ef)
        } else if (eat("true", sc)) Exp.BoolCst(true)
        else if (eat("false", sc)) Exp.BoolCst(false)
        else if (Char.isDigit(peekChar(sc))) parseInt(sc)
        else if (Char.isLetter(peekChar(sc))) parseVar(sc)
        else err("expression", "parseExpSimp", sc)
    }

    def parseInt(sc: StringCursor[r]): Exp \ r + Abort = {
        def loop(i) = {
            if (nthChar(i, sc) |> Char.isDigit) loop(i+1)
            else i
        };
        let chars = loop(0);
        if (chars == 0) err("digit", "parseInt", sc) else ();
        match take(chars, sc) |> Int32.fromString {
            case Some(i) => Exp.IntCst(i)
            case None => ?unreachable // unreachable
        }
    }

    /// ALWAYS CONSUMES
    def parseVar(sc: StringCursor[r]): Exp \ r + Abort =
        Exp.Var(parseName(sc))

    /// ALWAYS CONSUMES
    def parseName(sc: StringCursor[r]): String \ r + Abort = {
        def loop(first, i) = {
            let c = nthChar(i, sc);
            if (Char.isLetter(c) or c == '_' or (not first#first and Char.isDigit(c))) loop(first = false, i+1)
            else i
        };
        let chars = loop(first = true, 0);
        if (chars == 0) err("letter", "parseName", sc)
        else take(chars, sc)
    }

    def expect(s: String, rule: String, sc: StringCursor[r]): Unit \ r + Abort = {
        if (eat(s, sc)) ()
        else err("'${s}'", rule, sc)
    }

    def whiteSpace(sc: StringCursor[r]): Unit \ r =
        dropWhile(Char.isWhitespace, sc)

    def whiteSpace!(rule: String, sc: StringCursor[r]): Unit \ r + Abort =
        if (dropWhile!(Char.isWhitespace, sc)) ()
        else {
            err("whitespace", rule, sc)
        }

    def err(expected: String, rule: String, sc: StringCursor[r]): a \ r + Abort =
        Abort.abort("(${rule}) expected ${expected} in: '${remaining(sc)}'")

}
mod Talpin.Parsing.Parser {
    use Talpin.Data.Exp
    use Util.StringCursor
    use Util.StringCursor.peekChar
    use Util.StringCursor.nthChar
    use Util.StringCursor.remaining
    use Util.StringCursor.eat
    use Util.StringCursor.take
    use Util.StringCursor.dropWhile
    use Util.StringCursor.dropWhile!

    pub def parse(s: String): Exp \ Abort = region local {
        match String.stripPrefix(substr = "flix:", s) {
            case Some(input) =>
                Talpin.Parsing.FlixParser.parse(input)
            case None =>
                let sc = StringCursor.mk(local, '&', s);
                let e = parseExp(sc);
                whiteSpace(sc);
                expect("&", "parse", sc);
                e
        }
    }

    def parseExp(sc: StringCursor[r]): Exp \ r + Abort = {
        whiteSpace(sc);
        let c = peekChar(sc);
        if (c == '(') parseParenExp(sc)
        else if (eat("true", sc)) Exp.BoolCst(true)
        else if (eat("false", sc)) Exp.BoolCst(false)
        else if (Char.isDigit(c)) parseInt(sc)
        else if (Char.isLetter(c)) parseVar(sc)
        else err("expression or '('", "parseExp", sc)
    }

    /// ALWAYS CONSUMES
    def parseParenExp(sc: StringCursor[r]): Exp \ r + Abort = {
        def ept(s) = expect(s, "parseParenExp", sc);
        def ws!() = whiteSpace!("parseParenExp", sc);
        ept("(");
        whiteSpace(sc);
        if (sc |> eat("lambda")) {
            whiteSpace(sc);
            ept("(");
            whiteSpace(sc);
            let x = parseName(sc);
            whiteSpace(sc);
            ept(")");
            whiteSpace(sc);
            let e = parseExp(sc);
            whiteSpace(sc);
            ept(")");
            Exp.Abs(x, e)
        } else if (sc |> eat("rec")) {
            whiteSpace(sc);
            ept("(");
            whiteSpace(sc);
            let f = parseName(sc);
            whiteSpace(sc);
            let x = parseName(sc);
            whiteSpace(sc);
            ept(")");
            whiteSpace(sc);
            let e = parseExp(sc);
            whiteSpace(sc);
            ept(")");
            Exp.Rec(f, x, e)
        } else if (sc |> eat("let")) {
            whiteSpace(sc);
            ept("(");
            whiteSpace(sc);
            let x = parseName(sc);
            whiteSpace(sc);
            let e = parseExp(sc);
            whiteSpace(sc);
            ept(")");
            whiteSpace(sc);
            let e1 = parseExp(sc);
            whiteSpace(sc);
            ept(")");
            Exp.Let(x, e, e1)
        } else if (sc |> eat("new")) {
            ws!();
            let e = parseExp(sc);
            whiteSpace(sc);
            ept(")");
            Exp.New(e)
        } else if (sc |> eat("get")) {
            ws!();
            let e = parseExp(sc);
            whiteSpace(sc);
            ept(")");
            Exp.Get(e)
        } else if (sc |> eat("set")) {
            ws!();
            let e = parseExp(sc);
            whiteSpace(sc);
            let e1 = parseExp(sc);
            whiteSpace(sc);
            ept(")");
            Exp.Set(e, e1)
        } else if (sc |> eat("begin")) {
            ws!();
            let e = parseExp(sc);
            whiteSpace(sc);
            let e1 = parseExp(sc);
            whiteSpace(sc);
            ept(")");
            Exp.Let("_", e, e1)
        } else if (sc |> eat("if")) {
            ws!();
            let e = parseExp(sc);
            whiteSpace(sc);
            let e1 = parseExp(sc);
            whiteSpace(sc);
            let e2 = parseExp(sc);
            whiteSpace(sc);
            ept(")");
            Exp.If(e, e1, e2)
        } else if (sc |> eat("+")) {
            whiteSpace(sc);
            let e = parseExp(sc);
            whiteSpace(sc);
            let e1 = parseExp(sc);
            whiteSpace(sc);
            ept(")");
            Exp.Add(e, e1)
        } else if (sc |> eat("-")) {
            whiteSpace(sc);
            let e = parseExp(sc);
            whiteSpace(sc);
            let e1 = parseExp(sc);
            whiteSpace(sc);
            ept(")");
            Exp.Sub(e, e1)
        } else if (sc |> eat("==")) {
            let e = parseExp(sc);
            let e1 = parseExp(sc);
            whiteSpace(sc);
            ept(")");
            Exp.Eq(e, e1)
        } else if (sc |> eat("do")) {
            ws!();
            let ef = parseName(sc);
            whiteSpace(sc);
            ept(")");
            Exp.Do(ef)
        } else if (sc |> eat("run")) {
            ws!();
            let e = parseExp(sc);
            whiteSpace(sc);
            let ef = parseName(sc);
            whiteSpace(sc);
            ept(")");
            Exp.Run(e, ef)
        } else {
            whiteSpace(sc);
            let e = parseExp(sc);
            whiteSpace(sc);
            let e1 = parseExp(sc);
            whiteSpace(sc);
            ept(")");
            Exp.App(e, e1)
        }
    }

    def expect(s: String, rule: String, sc: StringCursor[r]): Unit \ r + Abort = {
        if (eat(s, sc)) ()
        else err("'${s}'", rule, sc)
    }

    /// ALWAYS CONSUMES
    def parseVar(sc: StringCursor[r]): Exp \ r + Abort =
        Exp.Var(parseName(sc))

    def parseInt(sc: StringCursor[r]): Exp \ r + Abort = {
        def loop(i) = {
            if (nthChar(i, sc) |> Char.isDigit) loop(i+1)
            else i
        };
        let chars = loop(0);
        if (chars == 0) err("digit", "parseInt", sc) else ();
        match take(chars, sc) |> Int32.fromString {
            case Some(i) => Exp.IntCst(i)
            case None => ?unreachable // unreachable
        }
    }

    /// ALWAYS CONSUMES
    def parseName(sc: StringCursor[r]): String \ r + Abort = {
        def loop(first, i) = {
            let c = nthChar(i, sc);
            if (Char.isLetter(c) or c == '_' or (not first#first and Char.isDigit(c))) loop(first = false, i+1)
            else i
        };
        let chars = loop(first = true, 0);
        if (chars == 0) err("letter", "parseName", sc)
        else take(chars, sc)
    }

    def whiteSpace(sc: StringCursor[r]): Unit \ r =
        dropWhile(Char.isWhitespace, sc)

    def whiteSpace!(rule: String, sc: StringCursor[r]): Unit \ r + Abort =
        if (dropWhile!(Char.isWhitespace, sc)) ()
        else {
            err("whitespace", rule, sc)
        }

    def err(expected: String, rule: String, sc: StringCursor[r]): a \ r + Abort =
        Abort.abort("(${rule}) expected ${expected} in: '${remaining(sc)}'")

}
mod Talpin.BigStep {
    use Talpin.Data.Env
    use Talpin.Data.Env.{bind, unbind}
    use Talpin.Data.Exp
    use Talpin.Data.Id
    use Talpin.Data.Store
    use Talpin.Data.Trace
    use Talpin.Data.Trace.insert
    use Talpin.Data.Value
    use Talpin.Data.Store.{newLoc, remove, store}
    use Talpin.Data.RuntimeEffect.{Init, Read, Write, Eff}
    use Talpin.Data.Value.{Closure, Ref, U, BoolVal, IntVal}

    pub def eval(s: Store, env: Env, exp: Exp): (Value, Trace, Store) \ {Abort, KeyNotFound} = match exp {
        case Exp.Var(x) =>
            (env[x], Trace.empty(), s)
        case Exp.Abs(x, e) =>
            let env1 = unbind(x, env);
            (Closure(x, e, () -> env1), Trace.empty(), s)
        case Exp.Rec(f, x, e) =>
            let env1 = env |> unbind(f) |> unbind(x);
            def c() = Closure(x, e, () -> env1 |> bind(f, c()));
            (c(), Trace.empty(), s)
        case Exp.App(e, e1) =>
            evalApp(s, env, e, e1)
        case Exp.Let(x, e, e1) =>
            evalLet(s, env, x, e, e1)
        case Exp.New(e) =>
            evalNew(s, env, e)
        case Exp.Get(e) =>
            evalGet(s, env, e)
        case Exp.Set(e, e1) =>
            evalSet(s, env, e, e1)

        case Exp.BoolCst(b) =>
            (BoolVal(b), Trace.empty(), s)
        case Exp.If(e, e1, e2) =>
            evalIf(s, env, e, e1, e2)
        case Exp.IntCst(b) =>
            (IntVal(b), Trace.empty(), s)
        case Exp.Add(e, e1) =>
            evalIntOp(s, env, e, e1, Add.add)
        case Exp.Sub(e, e1) =>
            evalIntOp(s, env, e, e1, Sub.sub)
        case Exp.Eq(e, e1) =>
            evalEq(s, env, e, e1)

        case Exp.Do(ef) =>
            (U, Trace.singleton(Eff(ef)), s)
        case Exp.Run(e, ef) =>
            let (v, f, s1) = eval(s, env, e);
            (v, f |> Trace.remove(Eff(ef)), s1)
    }

    def evalApp(s0: Store, env: Env, e: Exp, e1: Exp): (Value, Trace, Store) \ {Abort, KeyNotFound} = {
        let (vTemp, f, s) = eval(s0, env, e);
        let (x, e11, env1) = vTemp |> Value.getClosure;
        let (v1, f1, s1) = eval(s, env, e1);
        let (v11, f11, s11) = eval(s1, env1 |> bind(x, v1), e11);
        (v11, f + f1 + f11, s11)
    }

    def evalLet(s0: Store, env: Env, x: Id, e: Exp, e1: Exp): (Value, Trace, Store) \ {Abort, KeyNotFound} = {
        let (v, f, s) = eval(s0, env, e);
        let env1 = if (x == "_") env else env |> unbind(x) |> bind(x, v);
        let (v1, f1, s1) = eval(s, env1, e1);
        (v1, f + f1, s1)
    }

    def evalNew(s0: Store, env: Env, e: Exp): (Value, Trace, Store) \ {Abort, KeyNotFound} = {
        let (v, f, s) = eval(s0, env, e);
        let l = newLoc(s);
        (Ref(l), f |> insert(Init(l)), s |> store(l, v))
    }

    def evalGet(s0: Store, env: Env, e: Exp): (Value, Trace, Store) \ {Abort, KeyNotFound} = {
        let (vTemp, f, s) = eval(s0, env, e);
        let l = Value.getRef(vTemp);
        (s[l], f |> insert(Read(l)), s)
    }

    def evalSet(s0: Store, env: Env, e: Exp, e1: Exp): (Value, Trace, Store) \ {Abort, KeyNotFound} = {
        let (vTemp, f, s) = eval(s0, env, e);
        let l = Value.getRef(vTemp);
        let (v, f1, s1) = eval(s, env, e1);
        (U, (f + f1) |> insert(Write(l)), s1 |> remove(l) |> store(l, v))
    }

    def evalIf(s0: Store, env: Env, e: Exp, e1: Exp, e2: Exp): (Value, Trace, Store) \ {Abort, KeyNotFound} = {
        let (vTemp, f, s) = eval(s0, env, e);
        match Value.getBool(vTemp) {
            case true =>
                let (v, f1, s1) = eval(s, env, e1);
                (v, f + f1, s1)
            case false =>
                let (v, f1, s1) = eval(s, env, e2);
                (v, f + f1, s1)
        }
    }

    def evalIntOp(s0: Store, env: Env, e: Exp, e1: Exp, op: (Int32, Int32) -> Int32): (Value, Trace, Store) \ {Abort, KeyNotFound} = {
        let (vTemp, f, s) = eval(s0, env, e);
        let v = Value.getInt(vTemp);
        let (v1Temp, f1, s1) = eval(s, env, e1);
        let v1 = Value.getInt(v1Temp);
        (IntVal(op(v, v1)), f + f1, s1)
    }

    def evalEq(s0: Store, env: Env, e: Exp, e1: Exp): (Value, Trace, Store) \ {Abort, KeyNotFound} = {
        let (v, f, s) = eval(s0, env, e);
        let (v1, f1, s1) = eval(s, env, e1);
        let resB = match (v, v1) {
            case (IntVal(i1), IntVal(i2)) => i1 == i2
            case (BoolVal(b1), BoolVal(b2)) => b1 == b2
            case _ => Abort.abort("'${v}' and '${v1}' cannot be compared with eq")
        };
        (BoolVal(resB), f + f1, s1)
    }

}
mod Talpin.EffectSolver {
    use Talpin.Data.Constraint
    use Talpin.Data.Type
    use Talpin.Data.Effect
    use Talpin.Data.Subst

    use Eq.eq

    pub def solv(k: Constraint): Subst =
        k |> collapse |> min

    pub def solvFull(p: (Subst, Type, Effect, Constraint)): (Subst, Type, Effect) = {
        let (s, t, ef, k) = p;
        let s1 = solv(k);
        (Subst.compose(inner = s, s1), Subst.appType(s1)(t), Subst.appEffect(s1)(ef))
    }

    def collapse(k: Constraint): Constraint = {
        k |> coerce |> Set.toList |> List.groupBy(x -> y -> fst(x) == fst(y)) |> List.map(
            group ->
                match group {
                    case Nil => ?unreachable
                    case (evar, _) :: xs =>
                        (evar, group |> List.map(snd) |> List.foldLeft(Effect.Union, Effect.Empty))
                }
        ) |> List.toSet |> Constraint.Constraint
    }

    def min(k: Constraint): Subst = {
        match Set.minimum(coerce(k)) {
            case None => Subst.id()
            case Some((z, ef)) =>
                let k1 = Set.remove((z, ef), coerce(k)) |> Constraint.Constraint;
                let my = min(k1);
                Subst.singleEVar(z, Subst.appEffect(my)(ef) |> Effect.remove(toRemove = Effect.Var(z))) |> Subst.compose(inner = my)
        }
    }

}
mod Talpin {

pub eff FreshName {
    def get(): Int32
}

mod FreshName {
    use Add.add

    pub def handleWithState(f: a -> b \ ef): a -> b \ ef - FreshName =
        x -> runWithState(() -> f(x))

    pub def runWithState(f: Unit -> b \ ef): b \ ef - FreshName = region local {
        let counter = Ref.fresh(local, -1);
        def next() = {
            counter |> Ref.transform(add(1));
            Ref.get(counter)
        };
        run f() with handler FreshName {
            def get(k) = k(next())
        }
    }

}
}
mod Talpin.Reconstruction {
    use Talpin.Data.Constraint
    use Talpin.Data.Constraint.constraint
    use Talpin.Data.Effect
    use Talpin.Data.Exp
    use Talpin.Data.Exp.expansive
    use Talpin.Data.FreeVarSet
    use Talpin.Data.Reg
    use Talpin.Data.Subst
    use Talpin.Data.SubstApp.app
    use Talpin.Data.SubstBind.bindAll
    use Talpin.Data.Subst.compose
    use Talpin.Data.TyEnv
    use Talpin.Data.Type
    use Talpin.Data.TyScheme
    use Talpin.Data.TVar
    use Talpin.Data.TVar.TVar
    use Talpin.Data.RVar
    use Talpin.Data.RVar.RVar
    use Talpin.Data.EVar
    use Talpin.Data.EVar.EVar
    use Talpin.Reconstruction
    use Talpin.EffectSolver
    use Talpin.Data.Subst
    use Talpin.FreshName
    use Util.Util.init
    use Util.Util

    use Functor.map
    use Foldable.toList
    use ToString.toString

    pub type alias Info = {
        exp = Exp,
        tpe = Type,
        effect = Effect,
        binders = Vector[(String, TyScheme)],
        preEffTpe = Type,
        preEffEffect = Effect,
        constraints = Constraint,
        preEffSubst = Subst,
        preEffBinders = Vector[(String, TyScheme)],
        solvedSubst = Subst
    }

    mod Info {
        use Functor.map
        use Talpin.Data.Constraint
        use Talpin.Data.Subst

        pub def toStrings(i: Info): List[String] = region local {
            use ToString.toString;
            let {
                exp,
                tpe,
                effect,
                binders,
                preEffTpe,
                preEffEffect,
                constraints,
                preEffSubst,
                preEffBinders,
                solvedSubst
            } = i;
            let l = MutList.empty(local);
            def add(title, content, start, end) = l |> MutList.push(Some((title, content, start, end)));
            def addOne(title, content) = l |> MutList.push(Some((title, List#{content}, "", "")));
            def addEmpty() = l |> MutList.push(None);
            addOne("Exp", exp |> toString);
            addOne("Type", tpe |> toString);
            addOne("Effect", effect |> toString);
            add("Binders", binders |> map(match (x, sigma) -> "${x}: ${sigma}") |> Vector.toList, "{", "}");
            addEmpty();
            addOne("(PreEff) Tpe", preEffTpe |> toString);
            addOne("(PreEff) Effect", preEffEffect |> toString);
            add("(PreEff) Constraints", constraints |> Constraint.toStrings, "{", "}");
            add("(PreEff) Subst", preEffSubst |> Subst.toStrings, "[", "]");
            add("(PreEff) Binders", preEffBinders |> map(match (x, sigma) -> "${x}: ${sigma}") |> Vector.toList, "{", "}");
            addEmpty();
            add("(Solved) Subst", solvedSubst |> Subst.toStrings, "[", "]");

            let maxFirst = l |> MutList.map(local, Option.map(match (x, _, _, _) -> String.length(x)) >> Option.getWithDefault(0)) |> MutList.maximum |> Option.getWithDefault(0);
            let indent = String.repeat(maxFirst+6, " ");
            l |> MutList.toList |> List.flatMap(line -> match line {
                case None => List#{""}
                case Some((title, content, start, end)) =>
                    let paddedTitle = String.padRight(maxFirst+2, '.', title);
                    match content {
                        case Nil => List#{"${paddedTitle}: ${start}${end}"}
                        case one :: Nil => List#{"${paddedTitle}: ${start}${one}${end}"}
                        case many => "${paddedTitle}: ${start}" :: map(String.concat(indent), many) ::: List#{String.concat(String.padLeft(maxFirst+2, ' ', ""), "  ${end}")}
                    }
            })
        }
    }

    pub def reconstructInfo(exp: Exp): Info \ {Abort, KeyNotFound} = {
        let ((s, t, ef, k), binders) = run Reconstruction.reconstruct(exp) with FreshName.runWithState with Reconstruction.BinderTypes.runWithList;
        let s1 = EffectSolver.solv(k);
        let finalSubst = s1 |> compose(inner = s);
        {
            exp = exp,
            tpe = app(s1)(t) |> Type.simplify,
            effect = app(s1)(ef) |> Effect.simplify,
            binders = binders |> Vector.map(match (x, xt) -> (x, app(finalSubst)(xt) |> TyScheme.simplify)),

            preEffTpe = t,
            preEffEffect = ef,
            constraints = k,
            preEffSubst = s,
            preEffBinders = binders |> Vector.map(match (x, xt) -> (x, app(s)(xt) |> TyScheme.simplify)),

            solvedSubst = finalSubst |> Subst.simplify
        }
    }

    pub eff BinderTypes {
        def typed(x: String, t: TyScheme): Unit
    }

    mod BinderTypes {
        use Talpin.Data.Type
        use Talpin.Data.TyScheme

        pub def handleWithNothing(f: a -> b \ ef): a -> b \ ef - BinderTypes =
            x -> runWithNothing(() -> f(x))

        pub def runWithNothing(f: Unit -> b \ ef): b \ ef - BinderTypes =
            run f() with handler BinderTypes { def typed(_x, _t, k) = k() }

        pub def handleWithList(f: a -> b \ ef): a -> (b, Vector[(String, TyScheme)]) \ ef - BinderTypes =
            x -> runWithList(() -> f(x))

        pub def runWithList(f: Unit -> b \ ef): (b, Vector[(String, TyScheme)]) \ ef - BinderTypes =
            region local {
                let types = MutList.empty(local);
                run {
                    (f(), MutList.toVector(types))
                } with handler BinderTypes {
                    def typed(x, t, k) = {
                        MutList.push((x, t), types);
                        k()
                    }
                }
            }
    }

    pub def reconstruct(exp: Exp): (Subst, Type, Effect, Constraint) \ {Abort, BinderTypes, FreshName, KeyNotFound} = {
        let (s, t, ef, k) = recon(TyEnv.empty(), exp);
        (s, Type.simplify(t), Effect.simplify(ef), Constraint.simplify(k))
    }

    def recon(tEnv: TyEnv, exp: Exp): (Subst, Type, Effect, Constraint) \ {Abort, BinderTypes, FreshName, KeyNotFound} = match exp {
        case Exp.Var(x) => reconVar(tEnv, x)
        case Exp.Let(x, e, e1) => reconLet(tEnv, x, e, e1)
        case Exp.Abs(x, e) => reconAbs(tEnv, x, e)
        case Exp.Rec(f, x, e) => reconRec(tEnv, f, x, e)
        case Exp.App(e, e1) => reconApp(tEnv, e, e1)
        case Exp.New(e) => reconNew(tEnv, e)
        case Exp.Get(e) => reconGet(tEnv, e)
        case Exp.Set(e, e1) => reconSet(tEnv, e, e1)

        case Exp.BoolCst(_) => (Subst.id(), Type.Bool, Effect.Empty, Constraint.empty())
        case Exp.If(e, e1, e11) => reconIf(tEnv, e, e1, e11)
        case Exp.IntCst(_) => (Subst.id(), Type.Int, Effect.Empty, Constraint.empty())
        case Exp.Add(e, e1) => reconIntOp(tEnv, e, e1)
        case Exp.Sub(e, e1) => reconIntOp(tEnv, e, e1)
        case Exp.Eq(e, e1) => reconEq(tEnv, e, e1)

        case Exp.Do(ef) => reconDo(tEnv, ef)
        case Exp.Run(e, ef) => reconRun(tEnv, e, ef)
    }

    def reconVar(tEnv: TyEnv, x: String): (Subst, Type, Effect, Constraint) \ {FreshName, KeyNotFound} = {
        let {tVars = tVars0, rVars = rVars0, eVars = eVars0, tpe = t, k} = coerce(tEnv[x]);
        let tVars = tVars0 |> toList |> map(tx -> (tx, Type.Var(freshTVar())));
        let rVars = rVars0 |> toList |> map(tx -> (tx, Reg.RegVar(freshRVar())));
        let eVars = eVars0 |> toList |> map(tx -> (tx, Effect.Var(freshEVar())));
        let s = Subst.empty() |> bindAll(tVars) |> bindAll(rVars) |> bindAll(eVars);
        (Subst.id(), app(s)(t), Effect.Empty, app(s)(k))
    }

    def reconLet(tEnv: TyEnv, x: String, e: Exp, e1: Exp): (Subst, Type, Effect, Constraint) \ {Abort, BinderTypes, FreshName, KeyNotFound} = {
        let (s, t, ef, k) = recon(tEnv, e);
        // don't need to generalize for _xyz let-binders
        if (not expansive(e) and not String.startsWith(prefix = "_", x)) {
            let vs = Type.fv(t) + Constraint.fv(k) - TyEnv.fv(tEnv);
            let scheme = TyScheme.genType(t, k, vs);
            BinderTypes.typed(x, scheme);
            let tEnv1 = app(s)(tEnv |> TyEnv.unbind(x)) |> TyEnv.bind(x, scheme);
            let (s1, t1, ef1, k1) = recon(tEnv1, e1);
            (s1 |> compose(inner = s), t1, ef1, k1)
        } else {
            BinderTypes.typed(x, TyScheme.fromType(t));
            let tEnv1 = app(s)(tEnv |> TyEnv.unbind(x)) |> TyEnv.bindType(x, t);
            let (s1, t1, ef1, k1) = recon(tEnv1, e1);
            (s1 |> compose(inner = s), t1, app(s1)(ef) + ef1, app(s1)(k) + k1)
        }
    }

    def reconAbs(tEnv: TyEnv, x: String, e: Exp): (Subst, Type, Effect, Constraint) \ {Abort, BinderTypes, FreshName, KeyNotFound} = {
        let a = Type.Var(freshTVar());
        let (s, t, ef, k) = recon(tEnv |> TyEnv.unbind(x) |> TyEnv.bindType(x, a), e);
        let zName = freshEVar();
        let z = Effect.Var(zName);
        BinderTypes.typed(x, TyScheme.fromType(a));
        (s, Type.Arrow(app(s)(a), z, t), Effect.Empty, k + constraint(upperBound = zName, ef))
    }

    def reconRec(tEnv: TyEnv, f: String, x: String, e: Exp): (Subst, Type, Effect, Constraint) \ {Abort, BinderTypes, FreshName, KeyNotFound} = {
        let a = Type.Var(freshTVar());
        let a1 = Type.Var(freshTVar());
        let zName = freshEVar();
        let z = Effect.Var(zName);
        // PAPER ERROR: x here is written as n twice
        let tEnv1 = tEnv |> TyEnv.unbind(f) |> TyEnv.unbind(x) |> TyEnv.bindType(f, Type.Arrow(a, z, a1)) |> TyEnv.bindType(x, a);
        let (s, t, ef, k) = recon(tEnv1, e);
        let s1 = unify(app(s)(a1), t);
        let comp = s1 |> compose(inner = s);
        let zSubst = match app(s, zName) {
            case Effect.Var(zName1) => zName1
            case other => bug!(other |> toString)
        };
        // PAPER ERROR: effect should be the variable, not the effect
        (comp, app(comp)(Type.Arrow(a, z, a1)), Effect.Empty, app(s1)(k + constraint(upperBound = zSubst, ef)))
    }


    def reconApp(tEnv: TyEnv, e: Exp, e1: Exp): (Subst, Type, Effect, Constraint) \ {Abort, BinderTypes, FreshName, KeyNotFound} = {
        let (s, t,  ef, k) = recon(tEnv, e);
        let (s1, t1, ef1, k1) = recon(tEnv, e1);
        let a = Type.Var(freshTVar());
        let z = Effect.Var(freshEVar());
        let s11 = unify(app(s1)(t), Type.Arrow(t1, z, a));
        let ef11 = app(s11)(app(s1)(ef) + ef1 + z);
        (s11 |> compose(inner = s1 |> compose(inner = s)), app(s11)(a), ef11, app(s11)(app(s1)(k) + k1))
    }

    def reconNew(tEnv: TyEnv, e: Exp): (Subst, Type, Effect, Constraint) \ {Abort, BinderTypes, FreshName, KeyNotFound} = {
        let r = Reg.RegVar(freshRVar());
        let (s, t, ef, k) = recon(tEnv, e);
        (s, Type.Ref(r, t), ef + Effect.Init(r), k)
    }

    def reconGet(tEnv: TyEnv, e: Exp): (Subst, Type, Effect, Constraint) \ {Abort, BinderTypes, FreshName, KeyNotFound} = {
        let (s, t, ef, k) = recon(tEnv, e);
        let a = Type.Var(freshTVar());
        let r = Reg.RegVar(freshRVar());
        let s1 = unify(Type.Ref(r, a), t);
        (s1 |> compose(inner = s), app(s1)(a), ef + Effect.Read(app(s1)(r)), app(s1)(k))
    }

    def reconSet(tEnv: TyEnv, e: Exp, e1: Exp): (Subst, Type, Effect, Constraint) \ {Abort, BinderTypes, FreshName, KeyNotFound} = {
        let (s, t, ef, k) = recon(tEnv, e);
        let (s1, t1, ef1, k1) = recon(tEnv, e1);
        let r = Reg.RegVar(freshRVar());
        let s11 = unify(Type.Ref(r, t1), app(s1)(t));
        let ef11 = app(s11)(app(s1)(ef) + ef1 + Effect.Write(r));
        (s11 |> compose(inner = s1 |> compose(inner = s)), Type.Unitt, ef11, app(s11)(app(s1)(k) + k1))
    }

    def reconIf(tEnv: TyEnv, e: Exp, e1: Exp, e11: Exp): (Subst, Type, Effect, Constraint) \ {Abort, BinderTypes, FreshName, KeyNotFound} = {
        let (s, t, ef, k) = recon(tEnv, e);
        let s1 = unify(t, Type.Bool);
        let (s11, t1, ef1, k1) = recon(tEnv, e1);
        let (s111, t11, ef11, k11) = recon(tEnv, e11);
        let s1111 = unify(app(s111)(t1), t11);
        let comp1And11 = s11 |> compose(inner = s1);
        let comp111And1111 = s1111 |> compose(inner = s111);
        let comp1Through1111 = comp111And1111 |> compose(inner = comp1And11);
        let ef111 = app(comp1Through1111)(ef) + app(comp111And1111)(ef1) + app(s1111)(ef11);
        (comp1Through1111 |> compose(inner = s), app(s1111)(t11), ef111, app(comp1Through1111)(k) + app(comp111And1111)(k1) + app(s1111)(k11))
    }

    def reconIntOp(tEnv: TyEnv, e: Exp, e1: Exp): (Subst, Type, Effect, Constraint) \ {Abort, BinderTypes, FreshName, KeyNotFound} = {
        let (s, t, ef, k) = recon(tEnv, e);
        let (s1, t1, ef1, k1) = recon(tEnv, e1);
        let s11 = unify(app(s1)(t), Type.Int);
        let s111 = unify(app(s11)(t1), Type.Int);
        let comp11And111 = s111 |> compose(inner = s11);
        let comp1And11And111 = comp11And111 |> compose(inner = s1);
        let ef11 = app(comp1And11And111)(ef) + app(comp11And111)(ef1);
        (comp1And11And111 |> compose(inner = s), Type.Int, ef11, app(comp1And11And111)(k) + app(comp11And111)(k1))
    }

    def reconEq(tEnv: TyEnv, e: Exp, e1: Exp): (Subst, Type, Effect, Constraint) \ {Abort, BinderTypes, FreshName, KeyNotFound} = {
        let (s, t, ef, k) = recon(tEnv, e);
        let (s1, t1, ef1, k1) = recon(tEnv, e1);
        let s11 = unify(app(s1)(t), Type.Int);
        let s111 = unify(app(s11)(t1), Type.Int);
        let comp = s111 |> compose(inner = s11);
        let comp1 = comp |> compose(inner = s1);
        let ef11 = app(comp1)(ef) + app(comp)(ef1);
        (comp1 |> compose(inner = s), Type.Bool, ef11, app(comp1)(k) + app(comp)(k1))
    }

    def reconDo(_tEnv: TyEnv, ef: String): (Subst, Type, Effect, Constraint) =
        (Subst.id(), Type.Unitt, Effect.Eff(ef), Constraint.empty())

    def reconRun(tEnv: TyEnv, e: Exp, effect: String): (Subst, Type, Effect, Constraint) \ {Abort, BinderTypes, FreshName, KeyNotFound} = {
        let (s, t, _ef, k) = recon(tEnv, e);
        let qName = freshEVar();
        let _q = Effect.Var(qName);
        let z = Effect.Var(freshEVar());
        let _union = z + Effect.Eff(effect);
        (s, t, z, k + Abort.abort("run not implemented"))
    }

    def unify(tpe: Type, tpe1: Type): Subst \ Abort = match (tpe, tpe1) {
        case (Type.Unitt, Type.Unitt) => Subst.id()
        case (Type.Var(x), Type.Var(_)) => Subst.singleTVar(x, tpe1)
        case (Type.Var(x), t) if not FreeVarSet.containsTVar(x, Type.fv(t)) => Subst.singleTVar(x, t)
        case (t, Type.Var(x)) if not FreeVarSet.containsTVar(x, Type.fv(t)) => Subst.singleTVar(x, t)
        case (Type.Arrow(ti, Effect.Var(z), tf), Type.Arrow(ti1, Effect.Var(z1), tf1)) =>
            let s = Subst.singleEVar(z, Effect.Var(z1));
            let s1 = unify(app(s)(ti), app(s)(ti1));
            let comp = s1 |> compose(inner = s);
            let s11 = unify(app(comp)(tf), app(comp)(tf1));
            s11 |> compose(inner = comp)
        case (Type.Ref(Reg.RegVar(r), t), Type.Ref(Reg.RegVar(r1), t1)) =>
            let s = Subst.singleRVar(r, Reg.RegVar(r1));
            let s1 = unify(app(s)(t), app(s)(t1));
            s1 |> compose(inner = s)

        case (Type.Bool, Type.Bool) => Subst.id()
        case (Type.Int, Type.Int) => Subst.id()

        case (t, t1) => Abort.abort("${t} !~ ${t1}")
    }

    def freshTVar(): TVar \ FreshName = TVar("t${FreshName.get()}")

    def freshRVar(): RVar \ FreshName = RVar("r${FreshName.get()}")

    def freshEVar(): EVar \ FreshName = EVar("e${FreshName.get()}")

}
mod Talpin.Repl {
    use Talpin.Parsing.Parser
    use Talpin.Reconstruction
    use Talpin.Data.Type
    use Talpin.Data.Constraint
    use Talpin.Data.TyScheme
    use Talpin.Data.Subst
    use Talpin.FreshName
    use Talpin.EffectSolver
    use Talpin.Data.Effect
    use Util.Util

    pub def main(): Unit \ IO = run {
        println("-- REPL READY (':exit' to exit) --");
        println("Write a single line expression and I will type it");
        println("(Start with 'flix:' to use flix-ish syntax)");
        loop()
    } with Console.runWithIO

    def loop(): Unit \ IO + Console = {
        let input = Console.readln();
        if (input == ":exit" or input == ":quit" or input == ":q")
            ()
        else {
            typeInput(input);
            loop()
        }
    }

    def typeInput(input: String): Unit \ IO = {
        run {
            let p = Parser.parse(input);
            let info = run Reconstruction.reconstructInfo(p) with FreshName.runWithState;
            info |> Reconstruction.Info.toStrings |> List.forEach(println)
        } with handler Abort {
            def abort(msg, _k) = println("Err: ${msg}")
        } with handler KeyNotFound {
            def keyNotFound(msg, _k) = println("Err: ${msg}")
        }
    }

}
mod Talpin.RunFile {
    use Talpin.FreshName
    use Talpin.Reconstruction
    use Talpin.EffectSolver
    use Talpin.Data.Subst
    use Util.Util

    pub def checkFileArg(): Result[String, Unit] \ {Sys, IO} =
        run {
            match Environment.getArgs() {
                case path :: Nil => checkFile(path)
                case _ => println("expects one path argument")
            }
        }
        with Environment.runWithIO
        with Util.fileReadRunWithAbort
        with Abort.runWithResult

    pub def checkFile(path: String): Unit \ IO =
        run checkFileEff(path)
        with Util.fileReadRunWithAbort
        with handler Abort {
            def abort(m, _k) = println(m)
        }

    pub def checkFileEff(path: String): Unit \ IO + Abort + FileRead = {
        if (FileRead.isReadable(path)) {
            let input = FileRead.read(path);
            let p =
                run Talpin.Parsing.Parser.parse(input)
                with handler Abort {
                    def abort(m, _k) = Abort.abort("Parsing Error: ${m}")
                };
            let info =
                run Reconstruction.reconstructInfo(p)
                with FreshName.runWithState
                with handler Abort {
                    def abort(m, _k) = Abort.abort("Typer Error: ${m}")
                } with handler KeyNotFound {
                    def keyNotFound(msg, _k) = Abort.abort("Typer Error: ${msg}")
                };
            info |> Reconstruction.Info.toStrings |> List.forEach(println)

        } else {
            println("cannot find ${path}")
        }
    }

}
mod Util {

pub struct StringCursor[r] {
    mut p: Int32,
    s: String,
    eof: Char
}

mod StringCursor {
    use ToString.toString

    pub def mk(rc: Region[r], eof: Char, s: String): StringCursor[r] \ r =
        new StringCursor @ rc {p = 0, s = s, eof = eof}

    pub def peekChar(sc: StringCursor[r]): Char \ r =
        nthChar(0, sc)

    pub def nthChar(n: Int32, sc: StringCursor[r]): Char \ r = {
        if (inBounds(sc->p + n, sc)) String.charAt(sc->p + n, sc->s)
        else sc->eof
    }

    pub def remaining(sc: StringCursor[r]): String \ r = {
        if (inBounds(sc->p, sc)) String.slice(start = sc->p, end = String.length(sc->s), sc->s)
        else ""
    }

    pub def peek(n: Int32, sc: StringCursor[r]): String \ r = {
        let available = inBounds(sc->p + n - 1, sc);
        if (available) String.slice(start = sc->p, end = sc->p + n, sc->s)
        else String.slice(start = sc->p, end = String.length(sc->s), sc->s) + toString(sc->eof)
    }

    pub def take(n: Int32, sc: StringCursor[r]): String \ r = {
        let res = peek(n, sc);
        sc->p = sc->p + n;
        res
    }

    pub def eat(s: String, sc: StringCursor[r]): Bool \ r = {
        let len = String.length(s);
        if (peek(len, sc) == s) {
            take(len, sc);
            true
        } else {
            false
        }
    }

    pub def at(s: String, sc: StringCursor[r]): Bool \ r = {
        let len = String.length(s);
        if (peek(len, sc) == s) {
            true
        } else {
            false
        }
    }

    pub def dropWhile(f: Char -> Bool \ ef, sc: StringCursor[r]): Unit \ ef + r = {
        let c = peekChar(sc);
        if (c != sc->eof and f(c)) {
            discard take(1, sc);
            dropWhile(f, sc)
        } else ()
    }

    pub def dropWhile!(f: Char -> Bool \ ef, sc: StringCursor[r]): Bool \ ef + r = {
        let c = peekChar(sc);
        if (c != sc->eof and f(c)) {
            discard take(1, sc);
            dropWhile(f, sc);
            true
        } else false
    }

    pub def hasPrefix(s: String, sc: StringCursor[r]): Bool \ r = {
        peek(String.length(s), sc) == s
    }

    def inBounds(idx: Int32, sc: StringCursor[r]): Bool =
        idx < String.length(sc->s)

}

}
mod Util.Util {
    import java.lang.System

    pub def abortRunWithCrash(f: Unit -> b \ ef): b \ ef - Abort + IO =
        run f() with handler Abort {
            def abort(m, _k) = {
                System.err.println(m);
                ?abortCrash
            }
        }

    pub def keyNotFoundRunWithAbort(f: Unit -> b \ ef): b \ ef - KeyNotFound + Abort =
        run f() with handler KeyNotFound {
            def keyNotFound(m, _k) = Abort.abort(m)
        }

    pub def runAll(f: Unit -> t \ ef): t \ ef - Abort - KeyNotFound - Talpin.FreshName - Talpin.Reconstruction.BinderTypes + IO =
        run f()
        with Talpin.FreshName.runWithState
        with Talpin.Reconstruction.BinderTypes.runWithNothing
        with keyNotFoundRunWithAbort
        with abortRunWithCrash

    pub def init(f: Unit -> t \ ef, n: Int32): List[t] \ ef = {
        def loop(count, acc) = {
            if (count <= 0) List.reverse(acc)
            else loop(count - 1, f() :: acc)
        };
        loop(n, Nil)
    }

    pub def fileReadRunWithAbort(f: Unit -> b \ ef): b \ ef - FileRead + {Abort, IO} =
        match FileRead.runWithIO(f) {
            case Ok(v) => v
            case Err(_ioError) => Abort.abort("IoError")
        }
}

pub def runBenchmark(): Unit \ IO = {
    Talpin.Examples.runExp02() |> blackhole
}
