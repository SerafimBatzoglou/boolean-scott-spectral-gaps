module
public import BooleanScott.PacketClassification
public import BooleanScott.MarkerDerivatives
public import BooleanScott.ScottClauses

/-! Pure finite-level incidence formulas for the derivative counts. Removing
a closed locus can be tested inside a single clopen neighborhood, even if
the difference itself is not closed. -/
@[expose] public section
namespace BooleanScott
open Set TopologicalSpace Ordinal

theorem sigma_as_pi {n : ℕ} {φ : Formula n} {α : Ordinal.{0}} (h : AtLevel .sigma α φ) :
    ∃ ψ : Formula n, AtLevel .pi (α+1) ψ ∧ ∀ (B : Type) (M : BoolOps B) (v : Fin n → B),
      ψ.Holds M v ↔ φ.Holds M v := by
  let f (_ : Unit) := φ.negate
  refine ⟨(disjoinPi f).negate,(disjoinPi_level (fun _ : Unit => h.negate)).negate,fun B M v => ?_⟩
  simp [Formula.holds_negate,holds_disjoinPi,f]

theorem pi_pair {n : ℕ} {α : Ordinal.{0}} {φ ψ : Formula n} (hφ : AtLevel .pi α φ)
    (hψ : AtLevel .pi α ψ) (pos : 0 < α) :
    ∃ θ : Formula n, AtLevel .pi α θ ∧ ∀ (B : Type) (M : BoolOps B) (v : Fin n → B),
      θ.Holds M v ↔ φ.Holds M v ∧ ψ.Holds M v := by
  let f (b : Bool) := if b then φ else ψ
  have hf (b : Bool) : AtLevel .pi α (f b) := by cases b <;> first | exact hφ | exact hψ
  obtain ⟨θ,hθ,t⟩ := pi_conjunction f hf pos
  exact ⟨θ,hθ,fun B M v => (t B M v).trans ⟨fun h => ⟨h true,h false⟩,
    fun ⟨l,r⟩ b => by cases b <;> assumption⟩⟩

theorem below_formula {φ : Formula 1} {α : Ordinal.{0}} (lev : AtLevel .pi α φ) (pos : 0 < α) :
    ∃ ψ : Formula 1, AtLevel .pi (α+1+1) ψ ∧ ∀ (B : Type) [BooleanAlgebra B] (c : B),
      ψ.Holds (BoolOps.ofAlgebra B) (fun _ => c) ↔ ∃ u ≤ c, φ.Holds (BoolOps.ofAlgebra B) (fun _ => u) := by
  obtain ⟨χ,hχ,t⟩ := threshold_formula lev pos 1
  obtain ⟨ψ,hψ,s⟩ := sigma_as_pi hχ
  refine ⟨ψ,hψ,fun B _ c => ((s B _ _).trans (t B c)).trans ?_⟩
  constructor
  · rintro ⟨u,hu,_⟩
    exact ⟨u 0,hu 0⟩
  · rintro ⟨u,le,hu⟩
    exact ⟨fun _ => u,fun _ => ⟨le,hu⟩,fun i j ne => (ne (Subsingleton.elim i j)).elim⟩

def FiniteHit (P : LocalLocus) : Prop := ∃ (k : ℕ) (φ : Formula 1), 0 < k ∧
  AtLevel .pi (k : Ordinal.{0}) φ ∧ ∀ (X : Type) [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [ZeroDimensionalSpace X], Detects φ (P.points X)

theorem full_finiteHit : FiniteHit fullLocus := by
  let φ : Formula 1 := .qf (.neg (.eq (.var 0) .zero))
  refine ⟨1,φ,by decide,.qf _ _ _,fun X _ _ _ _ C => ?_⟩
  change C ≠ ⊥ ↔ ((C : Set X) ∩ univ).Nonempty
  rw [inter_univ,nonempty_iff_ne_empty]
  exact not_congr SetLike.coe_injective.eq_iff.symm

theorem finiteHit_stages {P : LocalLocus} (h : FiniteHit P) (k : ℕ) : FiniteHit (P.stage k) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    obtain ⟨n,φ,pos,lev,truth⟩ := ih
    obtain ⟨ψ,hψ,t⟩ := derivative_formula lev (by exact_mod_cast pos)
    refine ⟨n+2,ψ,by omega,by simpa using hψ,fun X _ _ _ _ => ?_⟩
    change Detects ψ (derivatives (k+1) _)
    rw [derivatives_succ]
    exact t X _ (truth X)

def LocalLocus.difference (P Q : LocalLocus) : LocalLocus where
  points X _ := P.points X \ Q.points X
  restricts e := by rw [preimage_sdiff,P.restricts e,Q.restricts e]

def LocalLocus.closedHull (P : LocalLocus) : LocalLocus where
  points X _ := closure (P.points X)
  restricts e := by rw [e.isOpenMap.preimage_closure_eq_closure_preimage e.continuous,P.restricts e]

theorem finiteHit_hull {P : LocalLocus} (h : FiniteHit P) : FiniteHit P.closedHull := by
  obtain ⟨k,φ,pos,lev,t⟩ := h
  refine ⟨k,φ,pos,lev,fun X _ _ _ _ C => (t X C).trans ?_⟩
  change _ ↔ ((C : Set X) ∩ closure (P.points X)).Nonempty
  rw [inter_comm (C : Set X) (P.points X),inter_comm (C : Set X) (closure _),
    closure_inter_open_nonempty_iff C.isClopen.isOpen]

theorem finiteHit_difference {P Q : LocalLocus} (hp : FiniteHit P) (hq : FiniteHit Q)
    (closed : ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] [ZeroDimensionalSpace X],
      IsClosed (Q.points X)) : FiniteHit (P.difference Q) := by
  obtain ⟨a,φ,ha,lev,t⟩ := hp
  obtain ⟨b,ψ,_,hψ,s⟩ := hq
  obtain ⟨η,hη,tt⟩ := sigma_as_pi hψ.negate
  let m := max a (b+1)
  have l : AtLevel .pi (m : Ordinal.{0}) φ := lev.liftLevel (by exact_mod_cast Nat.le_max_left a (b+1))
  have r : AtLevel .pi (m : Ordinal.{0}) η := hη.liftLevel (by exact_mod_cast Nat.le_max_right a (b+1))
  have pos : 0 < m := ha.trans_le (Nat.le_max_left ..)
  obtain ⟨ζ,hζ,z⟩ := pi_pair l r (by exact_mod_cast pos)
  obtain ⟨θ,hθ,th⟩ := below_formula hζ (by exact_mod_cast pos)
  refine ⟨m+1+1,θ,by omega,by simpa using hθ,fun X _ _ _ _ C => ?_⟩
  rw [th]
  have meaning (U : Clopens X) : ζ.Holds (BoolOps.ofAlgebra (Clopens X)) (fun _ => U) ↔
      ((U : Set X) ∩ P.points X).Nonempty ∧ ¬ ((U : Set X) ∩ Q.points X).Nonempty := by
    rw [z,tt,Formula.holds_negate,t X U,s X U]
  constructor
  · rintro ⟨U,le,hU⟩
    obtain ⟨⟨x,hx,px⟩,no⟩ := (meaning U).mp hU
    exact ⟨x,le hx,px,fun qx => no ⟨x,hx,qx⟩⟩
  · rintro ⟨x,hx,px,nq⟩
    obtain ⟨V,hV,xv,sub⟩ := exists_isClopen_mem_of_isOpen (C.isClopen.isOpen.inter (closed X).isOpen_compl) ⟨hx,nq⟩
    let U : Clopens X := ⟨V,hV⟩
    refine ⟨U,fun _ hv => (sub hv).1,(meaning U).mpr ⟨⟨x,xv,px⟩,?_⟩⟩
    rintro ⟨y,hy,qy⟩
    exact (sub hy).2 qy

theorem isolatedClosure_finiteHit : FiniteHit isolatedClosureLocus := by
  have h := finiteHit_hull (finiteHit_difference full_finiteHit (finiteHit_stages full_finiteHit 1)
    (fun X _ _ _ _ => isClosed_derivedSet (univ : Set X)))
  obtain ⟨k,φ,pos,lev,t⟩ := h
  refine ⟨k,φ,pos,lev,fun X _ _ _ _ => ?_⟩
  simpa only [LocalLocus.closedHull,LocalLocus.difference,fullLocus,LocalLocus.stage,
    derivatives,Function.iterate_one,← compl_eq_univ_sdiff,isolatedClosureLocus,scatteredLocus,isolatedPoints] using t X

end BooleanScott
