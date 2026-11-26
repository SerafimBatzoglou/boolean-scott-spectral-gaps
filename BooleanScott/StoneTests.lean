module
public import BooleanScott.PacketScott

/-! Bookkeeping for compiling predicates on finite clopen tuples into the
pure Boolean hierarchy. The semantic quantifiers range over all compact
Stone spaces with countably many clopens. -/
@[expose] public section
namespace BooleanScott
open TopologicalSpace Ordinal
open scoped Ordinal

abbrev StonePredicate (n : ℕ) := (X : Type) → [TopologicalSpace X] → (Fin n → Clopens X) → Prop

def StoneDef {n : ℕ} (p : Polarity) (α : Ordinal.{0}) (R : StonePredicate n) := ∃ φ : Formula n,
  AtLevel p α φ ∧ ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ZeroDimensionalSpace X] [Countable (Clopens X)] (v : Fin n → Clopens X),
    φ.Holds (BoolOps.ofAlgebra (Clopens X)) v ↔ R X v

def FiniteTest {n : ℕ} (R : StonePredicate n) := ∃ k : ℕ, 0 < k ∧ StoneDef .pi (k : Ordinal.{0}) R

theorem StoneDef.congr {n p α} {R S : StonePredicate n} (h : StoneDef p α R)
    (eq : ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] [ZeroDimensionalSpace X]
      [Countable (Clopens X)] (v : Fin n → Clopens X), R X v ↔ S X v) : StoneDef p α S := by
  obtain ⟨φ,hφ,t⟩ := h
  exact ⟨φ,hφ,fun X _ _ _ _ _ v => (t X v).trans (eq X v)⟩

theorem StoneDef.raise {n p α β} {R : StonePredicate n} (h : StoneDef p α R) (le : α ≤ β) : StoneDef p β R := by
  obtain ⟨φ,hφ,t⟩ := h
  exact ⟨φ,hφ.liftLevel le,t⟩

theorem StoneDef.neg {n p α} {R : StonePredicate n} (h : StoneDef p α R) :
    StoneDef p.flip α (fun X _ v => ¬ R X v) := by
  obtain ⟨φ,hφ,t⟩ := h
  exact ⟨φ.negate,hφ.negate,fun X _ _ _ _ _ v => (φ.holds_negate _ _).trans (not_congr (t X v))⟩

theorem StoneDef.asSigma {n α} {R : StonePredicate n} (h : StoneDef .pi α R) : StoneDef .sigma (α+1) R := by
  obtain ⟨φ,lev,t⟩ := h
  let f (_ : Unit) := φ
  exact ⟨disjoinPi f,disjoinPi_level (fun _ => lev),fun X _ _ _ _ _ v => (holds_disjoinPi f _ v).trans
    (Iff.trans ⟨fun ⟨_,h⟩ => h,fun h => ⟨(),h⟩⟩ (t X v))⟩

theorem StoneDef.asPi {n α} {R : StonePredicate n} (h : StoneDef .sigma α R) : StoneDef .pi (α+1) R := by
  obtain ⟨φ,lev,t⟩ := h
  obtain ⟨ψ,hψ,truth⟩ := sigma_as_pi lev
  exact ⟨ψ,hψ,fun X _ _ _ _ _ v => (truth _ _ _).trans (t X v)⟩

theorem StoneDef.and {n α} {R S : StonePredicate n} (h : StoneDef .pi α R) (g : StoneDef .pi α S)
    (pos : 0 < α) : StoneDef .pi α (fun X _ v => R X v ∧ S X v) := by
  obtain ⟨φ,hφ,t⟩ := h
  obtain ⟨ψ,hψ,s⟩ := g
  obtain ⟨χ,hχ,c⟩ := pi_pair hφ hψ pos
  exact ⟨χ,hχ,fun X _ _ _ _ _ v => (c _ _ _).trans (and_congr (t X v) (s X v))⟩

theorem StoneDef.or {n α} {R S : StonePredicate n} (h : StoneDef .sigma α R) (g : StoneDef .sigma α S)
    (pos : 0 < α) : StoneDef .sigma α (fun X _ v => R X v ∨ S X v) := by
  obtain ⟨φ,hφ,t⟩ := h
  obtain ⟨ψ,hψ,s⟩ := g
  obtain ⟨χ,hχ,c⟩ := sigma_or hφ hψ pos
  exact ⟨χ,hχ,fun X _ _ _ _ _ v => (c _ _ _).trans (or_congr (t X v) (s X v))⟩

theorem StoneDef.substitute {m n p α} {R : StonePredicate n} (h : StoneDef p α R) (ρ : Fin n → Term m) :
    StoneDef p α (fun X _ v => R X (fun i => (ρ i).eval (BoolOps.ofAlgebra _) v)) := by
  obtain ⟨φ,hφ,t⟩ := h
  exact ⟨φ.substitute ρ,hφ.substitute _,fun X _ _ _ _ _ v => (φ.holds_substitute ρ _ v).trans (t X _)⟩

theorem StoneDef.someClopen {n α} {R : StonePredicate (1+n)} (h : StoneDef .pi α R) :
    StoneDef .sigma (α+1) (fun X _ v => ∃ U : Clopens X, R X (Fin.append (fun _ : Fin 1 => U) v)) := by
  obtain ⟨φ,hφ,t⟩ := h
  refine ⟨.sigma (fun _ => 1) (fun _ => φ),.sigma (fun _ => α) (fun _ => lt_add_one _) (fun _ => hφ),
    fun X _ _ _ _ _ v => ?_⟩
  constructor
  · rintro ⟨_,u,hu⟩
    have eq : (fun _ => u 0) = u := funext (fun i => congrArg u (Subsingleton.elim 0 i))
    exact ⟨u 0,eq.symm ▸ (t X _).mp hu⟩
  · rintro ⟨U,hU⟩
    exact ⟨0,fun _ => U,(t X _).mpr hU⟩

theorem StoneDef.everyClopen {n α} {R : StonePredicate (1+n)} (h : StoneDef .sigma α R) :
    StoneDef .pi (α+1) (fun X _ v => ∀ U : Clopens X, R X (Fin.append (fun _ : Fin 1 => U) v)) := by
  obtain ⟨φ,hφ,t⟩ := h
  refine ⟨.pi (fun _ => 1) (fun _ => φ),.pi (fun _ => α) (fun _ => lt_add_one _) (fun _ => hφ),
    fun X _ _ _ _ _ v => ?_⟩
  constructor
  · intro every U
    exact (t X _).mp (every 0 _)
  · intro every _ u
    have eq : (fun _ => u 0) = u := funext (fun i => congrArg u (Subsingleton.elim 0 i))
    exact (t X _).mpr (eq ▸ every (u 0))

theorem StoneDef.allOf {I : Type} [Countable I] {n α} {R : I → StonePredicate n} (pos : 0 < α)
    (h : ∀ i, StoneDef .pi α (R i)) : StoneDef .pi α (fun X _ v => ∀ i, R i X v) := by
  choose φ lev t using h
  obtain ⟨ψ,hψ,s⟩ := pi_conjunction φ lev pos
  exact ⟨ψ,hψ,fun X _ _ _ _ _ v => (s _ _ _).trans (forall_congr' (fun i => t i X v))⟩

theorem StoneDef.anyOf {I : Type} [Countable I] [Nonempty I] {n α} {R : I → StonePredicate n}
    (h : ∀ i, StoneDef .pi α (R i)) : StoneDef .sigma (α+1) (fun X _ v => ∃ i, R i X v) := by
  choose φ lev t using h
  exact ⟨disjoinPi φ,disjoinPi_level lev,fun X _ _ _ _ _ v =>
    (holds_disjoinPi φ _ _).trans (exists_congr fun i => t i X v)⟩

theorem FiniteTest.congr {n} {R S : StonePredicate n} (h : FiniteTest R)
    (eq : ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] [ZeroDimensionalSpace X]
      [Countable (Clopens X)] (v : Fin n → Clopens X), R X v ↔ S X v) : FiniteTest S := by
  obtain ⟨k,pos,lev⟩ := h
  exact ⟨k,pos,lev.congr eq⟩

theorem FiniteTest.neg {n} {R : StonePredicate n} (h : FiniteTest R) : FiniteTest (fun X _ v => ¬ R X v) := by
  obtain ⟨k,pos,lev⟩ := h
  exact ⟨k+1,by omega,by simpa using lev.neg.asPi⟩

theorem FiniteTest.and {n} {R S : StonePredicate n} (h : FiniteTest R) (g : FiniteTest S) :
    FiniteTest (fun X _ v => R X v ∧ S X v) := by
  obtain ⟨a,pa,ha⟩ := h
  obtain ⟨b,_,hb⟩ := g
  have pos : 0 < max a b := pa.trans_le (Nat.le_max_left ..)
  exact ⟨_,pos,(ha.raise (by exact_mod_cast Nat.le_max_left a b)).and
    (hb.raise (by exact_mod_cast Nat.le_max_right a b)) (by exact_mod_cast pos)⟩

theorem FiniteTest.substitute {m n} {R : StonePredicate n} (h : FiniteTest R) (ρ : Fin n → Term m) :
    FiniteTest (fun X _ v => R X (fun i => (ρ i).eval (BoolOps.ofAlgebra _) v)) := by
  obtain ⟨k,pos,lev⟩ := h
  exact ⟨k,pos,lev.substitute ρ⟩

theorem FiniteTest.piOmega {n} {R : StonePredicate n} (h : FiniteTest R) : StoneDef .pi ω R := by
  obtain ⟨k,_,lev⟩ := h
  exact lev.raise (natCast_lt_omega0 k).le

end BooleanScott
