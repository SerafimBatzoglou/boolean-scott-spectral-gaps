module
public import BooleanScott.BranchBlocks

/-! Disjoint branch blocks whose entire clopen sites converge to the common
vertex limit. Future branch vertices stay free at every finite stage. -/
@[expose] public section
namespace BooleanScott
open Set Filter Topology TopologicalSpace Descriptive
open scoped Classical OnePoint

variable {T : tree ℕ} {X : Type} [TopologicalSpace X]

def ConvergingSites (t : X) (V : ℕ → Clopens X) := ∀ C : Clopens X, t ∈ C → ∀ᶠ n in atTop, V n ≤ C

theorem window_schedule [Countable (Clopens X)] (t : X) (z : ℕ → X)
    (tends : ∀ C : Clopens X, t ∈ C → ∀ᶠ n in atTop, z n ∈ C) :
    ∃ U : ℕ → Clopens X, (∀ n, t ∈ U n) ∧ (∀ n, z n ∈ U n) ∧ ConvergingSites t U := by
  classical
  obtain ⟨cover,onto⟩ := exists_surjective_nat (Clopens X)
  let window (n : ℕ) (x : X) := (Finset.range n).inf (fun i => if x ∈ cover i then cover i else ⊤)
  have hit (n : ℕ) (x : X) : x ∈ window n x := by
    induction n with
    | zero => exact Set.mem_univ _
    | succ n ih =>
      dsimp only [window]
      rw [Finset.range_add_one,Finset.inf_insert]
      exact ⟨by split <;> first | assumption | trivial,ih⟩
  have sub {k n : ℕ} (lt : k<n) {x : X} (hx : x ∈ cover k) : window n x ≤ cover k := by
    have h := Finset.inf_le (f := fun i => if x ∈ cover i then cover i else ⊤) (Finset.mem_range.mpr lt)
    rwa [ite_eq_left hx] at h
  refine ⟨fun n => window n t ⊔ window n (z n),fun n => Or.inl (hit n _),fun n => Or.inr (hit n _),?_⟩
  intro C hc
  obtain ⟨k,rfl⟩ := onto C
  filter_upwards [eventually_gt_atTop k,tends _ hc] with n large inside
  exact sup_le (sub large hc) (sub large inside)

structure BranchStage (G : GuardData T X) (t : X) (path : ℕ → Vertex) (n : ℕ) where
  used : Clopens X
  misses : t ∉ used
  free (k : ℕ) : n ≤ k → G.vertex (path k) ∉ used

variable [CompactSpace X] [T2Space X] (G : GuardData T X)

theorem GuardData.convergent_blocks [Countable (Clopens X)] {t : X} (ht : t ∈ derivedSet (range G.vertex))
    (path : ℕ → Vertex) (inj : Function.Injective path) (a b : ℕ → ℕ)
    (inTag : ∀ n, a n ∈ sectorTags T (path n)) (outTag : ∀ n, b n ∈ sectorTags T (path n)) :
    ∃ P : ∀ n, BranchBlock G t (path n) (a n) (b n),
      Pairwise (fun i j => Disjoint ((P i).site : Set X) ((P j).site : Set X)) ∧ ConvergingSites t (fun n => (P n).site) := by
  classical
  have tends (C : Clopens X) (inside : t ∈ C) : ∀ᶠ n in atTop, G.vertex (path n) ∈ C := by
    rcases G.finite_or_cofinite C with fin|fin
    · exact (G.finite_site_misses_limit ht C fin inside).elim
    · have few := fin.preimage inj.injOn
      rw [← Nat.cofinite_eq_atTop]
      exact mem_of_superset few.compl_mem_cofinite (fun _ h => Classical.not_not.mp h)
  obtain ⟨U,tU,vU,limits⟩ := window_schedule t (fun n => G.vertex (path n)) tends
  let Stage := BranchStage G t path
  have pick (n : ℕ) (s : Stage n) := G.allocate_block ht (path n) (inTag n) (outTag n) (U n \ s.used)
    ⟨tU n,s.misses⟩ ⟨vU n,s.free n le_rfl⟩
  let block (n : ℕ) (s : Stage n) := (pick n s).choose
  have inside (n : ℕ) (s : Stage n) : (block n s).site ≤ U n \ s.used := (pick n s).choose_spec
  let advance (n : ℕ) (s : Stage n) : Stage (n+1) :=
    ⟨s.used ⊔ (block n s).site,fun h => h.elim s.misses (block n s).limit_out,fun k hk h =>
      h.elim (s.free k (Nat.le_of_succ_le hk)) (fun atSite =>
        (Nat.ne_of_gt hk) (inj ((block n s).only (path k) atSite)))⟩
  let stages : (n : ℕ) → Stage n := Nat.rec ⟨⊥,id,fun _ _ => id⟩ advance
  let P (n : ℕ) := block n (stages n)
  have grows (n : ℕ) : (stages n).used ≤ (stages (n+1)).used := le_sup_left
  have monotone : Monotone (fun n => (stages n).used) := monotone_nat_of_le_succ grows
  have dis {i j : ℕ} (lt : i<j) : Disjoint ((P i).site : Set X) ((P j).site : Set X) := by
    have old : (P i).site ≤ (stages j).used := (show (P i).site ≤ (stages (i+1)).used from le_sup_right).trans (monotone lt)
    exact Set.disjoint_left.mpr (fun _ hi hj => (inside j (stages j) hj).2 (old hi))
  refine ⟨P,fun _ _ ne => (lt_or_gt_of_ne ne).elim dis (fun lt => (dis lt).symm),?_⟩
  intro C hc
  exact (limits C hc).mono (fun n h => (inside n (stages n)).trans (sdiff_le.trans h))

end BooleanScott
