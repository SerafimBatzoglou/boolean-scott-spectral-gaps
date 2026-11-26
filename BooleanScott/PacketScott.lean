module
public import BooleanScott.FiniteLoci
public import BooleanScott.SignTerms
public import BooleanScott.OrbitScott

/-! A finite family of uniformly finite-level point incidence predicates
gives a finite-level Scott sentence if its counts classify clopen fragments.
The bound is uniform over tuple arities and thresholds. The mixed packets
satisfy the criterion with two kinds of Cantor–Bendixson derivative. -/
@[expose] public section
namespace BooleanScott
open Set TopologicalSpace Ordinal

theorem count_thresholds {P : LocalLocus} (hyp : FiniteHit P) : ∃ k : ℕ, ∀ h : ℕ,
    ∃ φ : Formula 1, AtLevel .sigma (k : Ordinal.{0}) φ ∧ ∀ (X : Type) [TopologicalSpace X]
      [CompactSpace X] [T2Space X] [ZeroDimensionalSpace X] (C : Clopens X),
      φ.Holds (BoolOps.ofAlgebra (Clopens X)) (fun _ => C) ↔ (h : ℕ∞) ≤ P.count (spaceType C) := by
  obtain ⟨a,ψ,pos,lev,det⟩ := hyp
  refine ⟨a+1,fun h => ?_⟩
  obtain ⟨φ,hφ,t⟩ := threshold_formula lev (by exact_mod_cast pos) h
  refine ⟨φ,by simpa using hφ,fun X _ _ _ _ C => ?_⟩
  rw [t,count_clopen_marks (det X),P.count_clopen,le_encard_iff_exists_fin_injective]
  exact ⟨fun ⟨f,hf⟩ => ⟨f,hf,f.injective⟩,fun ⟨f,hf,inj⟩ => ⟨⟨f,inj⟩,hf⟩⟩

/-- Signed tests at a uniform level identify a reference tuple by the
truth values of a countable family of existential tests. -/
theorem truth_profile {A I : Type} [Countable I] (M : BoolOps A) {n : ℕ} (v : Fin n → A)
    {α : Ordinal.{0}} (f : I → Formula n) (levels : ∀ i, AtLevel .sigma α (f i)) :
    ∃ θ : Formula n, AtLevel .pi (α+1) θ ∧ ∀ w,
      θ.Holds M w ↔ ∀ i, ((f i).Holds M v ↔ (f i).Holds M w) := by
  classical
  choose positive hp tp using fun i => sigma_as_pi (levels i)
  let g i := if (f i).Holds M v then positive i else (f i).negate
  have hg i : AtLevel .pi (α+1) (g i) := by
    dsimp only [g]
    split
    · exact hp i
    · exact (levels i).negate.liftLevel (lt_add_one _).le
  obtain ⟨θ,hθ,t⟩ := pi_conjunction g hg (by positivity)
  refine ⟨θ,hθ,fun w => (t A M w).trans (forall_congr' (fun i => ?_))⟩
  by_cases h : (f i).Holds M v <;> simp [g,h,tp,Formula.holds_negate]

theorem scott_of_finite_counts {I X : Type} [Fintype I] [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [ZeroDimensionalSpace X] [Countable (Clopens X)] (P : I → LocalLocus)
    (definable : ∀ i, FiniteHit (P i))
    (classifies : ∀ C E : Clopens X, (∀ i, (P i).count (spaceType C) = (P i).count (spaceType E)) →
      Nonempty (C ≃ₜ E)) :
    ∃ (k : ℕ) (σ : Formula 0), AtLevel .pi (k : Ordinal.{0}) σ ∧
      ∀ (B : Type) [Countable B] [BooleanAlgebra B], Models (BoolOps.ofAlgebra B) σ ↔
        Nonempty (Clopens X ≃o B) := by
  classical
  let M := BoolOps.ofAlgebra (Clopens X)
  choose r t using fun i => count_thresholds (definable i)
  choose φ hφ truth using t
  let K := Finset.univ.sup r
  have bound (i : I) : r i ≤ K := Finset.le_sup (Finset.mem_univ i)
  let test (n : ℕ) (q : I × Pattern n × ℕ) := (φ q.1 q.2.2).substitute (fun _ => signTerm q.2.1)
  have level (n : ℕ) (q : I × Pattern n × ℕ) : AtLevel .sigma (K : Ordinal.{0}) (test n q) :=
    ((hφ q.1 q.2.2).substitute _).liftLevel (by exact_mod_cast bound q.1)
  have eval (n : ℕ) (q : I × Pattern n × ℕ) (w : Fin n → Clopens X) :
      (test n q).Holds M w ↔ (q.2.2 : ℕ∞) ≤ (P q.1).count (spaceType (signCell w q.2.1)) := by
    dsimp only [test]
    rw [Formula.holds_substitute]
    simp only [M,signTerm_eval]
    exact truth q.1 q.2.2 X _
  choose D lev spec using fun n (v : Fin n → Clopens X) => truth_profile M v (test n) (level n)
  have orbit : DefinesOrbits (fun {n} v => D n v) := by
    intro n v w
    constructor
    · intro hw
      have eq := (spec n v w).mp hw
      apply clopen_tuple_of_signs
      intro p
      apply classifies
      intro i
      apply ENat.eq_of_forall_natCast_le_iff
      intro h
      let q : I × Pattern n × ℕ := (i,p,h)
      exact (eval n q v).symm.trans ((eq q).trans (eval n q w))
    · rintro ⟨e,he⟩
      apply (spec n v w).mpr
      intro q
      let g := OpsIso.ofOrder e
      have same : g.toEquiv ∘ v = w := funext he
      exact same ▸ (level n q).transfer (g.bf K v)
  obtain ⟨σ,hσ,model⟩ := chartScott_of_orbits (fun {n} v => D n v) (fun {n} v => lev n v) orbit
  exact ⟨K+1+2,σ,by simpa using hσ,model⟩

/-- Every mixed packet has an actual finite-level pure Scott sentence.
The finite rank may grow with d. Countable competitors range over all
Boolean algebras, including the trivial algebra. -/
theorem mixed_finite_scott (d : ℕ) :
    ∃ (k : ℕ) (σ : Formula 0), AtLevel .pi (k : Ordinal.{0}) σ ∧
      ∀ (B : Type) [Countable B] [BooleanAlgebra B], Models (BoolOps.ofAlgebra B) σ ↔
        Nonempty (Clopens (Mixed d) ≃o B) := by
  obtain ⟨ht,hz,hc⟩ := mixed_stone d
  let P : Option (Fin (d+2)) → LocalLocus
    | none => ordinaryStage (d+1)
    | some k => scatteredStage k
  apply scott_of_finite_counts P
  · intro i
    cases i with
    | none => exact finiteHit_stages full_finiteHit _
    | some k => exact finiteHit_stages isolatedClosure_finiteHit _
  · intro C E same
    exact mixed_clopens_determined d C E (fun k hk => same (some ⟨k,by omega⟩)) (same none)

end BooleanScott
