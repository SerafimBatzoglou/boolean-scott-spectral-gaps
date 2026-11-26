module
public import BooleanScott.Flow
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! A concrete Baire-parametrized family of trees whose branchless parameters
are not analytic. The proof diagonalizes against continuous enumerations of
those parameters. This avoids importing a boundedness theorem for tree ranks. -/
@[expose] public section
namespace BooleanScott
open Descriptive MeasureTheory Set Filter Topology

abbrev Baire := ℕ → ℕ

@[simp] theorem initialSeg_length (a : Baire) (n : ℕ) : (initialSeg a n).length = n := by
  induction n <;> simp_all [initialSeg]

theorem initialSeg_take (a : Baire) {m n : ℕ} (h : m ≤ n) :
    (initialSeg a n).take m = initialSeg a m := by
  induction n with
  | zero =>
    have hm : m = 0 := by omega
    subst m
    rfl
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hl
    · simp
    · rw [initialSeg, List.take_append_of_le_length (by simpa using Nat.le_of_lt_succ hl)]
      exact ih (by omega)

theorem initialSeg_coord {a b : Baire} {n : ℕ} (h : initialSeg a n = initialSeg b n)
    {i : ℕ} (hi : i < n) : a i = b i := by
  induction n with
  | zero => omega
  | succ n ih =>
    change initialSeg a n ++ [a n] = initialSeg b n ++ [b n] at h
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hi) with rfl | hl
    · exact (List.cons.inj (List.append_inj_right' h rfl)).1
    · exact ih (List.append_inj_left' h rfl) hl

/-- A tree of candidate witnesses at input x, read from the code c. -/
def sectionTree (c x : Baire) : tree ℕ where
  val := {s | ∀ m ≤ s.length, c (Encodable.encode (initialSeg x m, s.take m)) ≠ 0}
  property := by
    intro s i h m hm
    have hh := h m (by simp; omega : m ≤ (s ++ [i]).length)
    simpa only [List.take_append_of_le_length hm] using hh

theorem branch_section_iff (c x : Baire) : HasBranch (sectionTree c x) ↔
    ∃ y : Baire, ∀ n, c (Encodable.encode (initialSeg x n, initialSeg y n)) ≠ 0 := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, fun n => ?_⟩
    simpa only [initialSeg_take y le_rfl] using hy n n (by simp)
  · rintro ⟨y, hy⟩
    refine ⟨y, fun n m hm => ?_⟩
    rw [initialSeg_take y (by simpa using hm)]
    exact hy m

/-- Every continuous image of Baire space is the ill-founded section of one code. -/
theorem range_as_sections (f : Baire → Baire) (hf : Continuous f) :
    ∃ c, ∀ x, HasBranch (sectionTree c x) ↔ x ∈ range f := by
  classical
  let c (k : ℕ) : ℕ := if ∃ (n : ℕ) (z : Baire),
      Encodable.encode (initialSeg (f z) n, initialSeg z n) = k then 1 else 0
  refine ⟨c, fun x => ?_⟩
  rw [branch_section_iff]
  constructor
  · rintro ⟨y, hy⟩
    have witness (n : ℕ) : ∃ z, initialSeg (f z) n = initialSeg x n ∧
        initialSeg z n = initialSeg y n := by
      have h := hy n
      simp only [c, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at h
      obtain ⟨m,z,hz⟩ := h
      have hp := Encodable.encode_injective hz
      have hm : m = n := by simpa using congrArg List.length (congrArg Prod.snd hp)
      subst m
      exact ⟨z, congrArg Prod.fst hp, congrArg Prod.snd hp⟩
    choose z hfx hzy using witness
    have convergence (u : ℕ → Baire) (v : Baire) (hu : ∀ n, initialSeg (u n) n = initialSeg v n) :
        Tendsto u atTop (𝓝 v) := by
      apply tendsto_pi_nhds.mpr
      intro i
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop i] with n hn
      exact (initialSeg_coord (hu n) hn).symm
    exact ⟨y, tendsto_nhds_unique (hf.continuousAt.tendsto.comp (convergence z y hzy))
      (convergence (f ∘ z) x hfx)⟩
  · rintro ⟨y,rfl⟩
    refine ⟨y, fun n => ?_⟩
    simp [c]
    exact ⟨n,y,rfl,rfl⟩

def diagonalTree (c : Baire) : tree ℕ := sectionTree c c

theorem branchless_not_analytic : ¬ AnalyticSet {c : Baire | ¬ HasBranch (diagonalTree c)} := by
  intro h
  obtain ⟨P, top, pol, f, hf, hr⟩ := analyticSet_iff_exists_polishSpace_range.mp h
  have hz : (fun _ : ℕ => 0) ∈ {c : Baire | ¬ HasBranch (diagonalTree c)} := by
    intro hb
    obtain ⟨y, hy⟩ := (branch_section_iff _ _).mp hb
    exact hy 0 rfl
  rw [← hr] at hz
  obtain ⟨p, _⟩ := hz
  let : Nonempty P := ⟨p⟩
  obtain ⟨g, hg, hsurj⟩ := PolishSpace.exists_nat_nat_continuous_surjective P
  obtain ⟨c,hc⟩ := range_as_sections (f ∘ g) (hf.comp hg)
  have flip := hc c
  rw [hsurj.range_comp, hr] at flip
  change HasBranch (diagonalTree c) ↔ ¬ HasBranch (diagonalTree c) at flip
  have hn : ¬ HasBranch (diagonalTree c) := fun hb => (flip.mp hb) hb
  exact hn (flip.mpr hn)

/-- The projection step for the all-model argument. Guard and comparison
failure must both be Borel. Absorption excludes every branched parameter. -/
theorem escape_comparison {M : Type*} [MeasurableSpace M] [StandardBorelSpace M]
    (guard failure : Set (Baire × M)) (hg : MeasurableSet guard)
    (hf : MeasurableSet failure)
    (sound : ∀ c x, (c,x) ∈ guard → (c,x) ∈ failure → ¬ HasBranch (diagonalTree c)) :
    ∃ c, ¬ HasBranch (diagonalTree c) ∧ ∀ x, (c,x) ∈ guard → (c,x) ∉ failure := by
  classical
  by_contra! h
  apply branchless_not_analytic
  have heq : Prod.fst '' (guard ∩ failure) = {c | ¬ HasBranch (diagonalTree c)} := by
    ext c
    constructor
    · rintro ⟨⟨p,x⟩, ⟨hg',hf'⟩,rfl⟩
      exact sound p x hg' hf'
    · intro hn
      obtain ⟨x,hg',hf'⟩ := h c hn
      exact ⟨(c,x),⟨hg',hf'⟩,rfl⟩
  rw [← heq]
  exact (hg.inter hf).analyticSet_image measurable_fst

end BooleanScott
