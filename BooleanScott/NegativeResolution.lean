module
public import BooleanScott.BranchGluing

/-! Unconditional conclusion for the pure Boolean language. The branch
homeomorphism is built in every guarded model and is composed with the
verified Scott, Borel, and diagonal arguments. -/
@[expose] public section
namespace BooleanScott
open Set TopologicalSpace Descriptive

theorem guarded_branch_implies_absorption {T : tree ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [ZeroDimensionalSpace X] [Countable (Clopens X)] (G : GuardData T X) (branch : HasBranch T) :
    Nonempty ((X ⊕ RootRow) ≃ₜ X) := by
  classical
  obtain ⟨s,hs⟩ := branch
  let path := initialSeg s
  have inj : Function.Injective path := fun i j h => by simpa [path] using congrArg List.length h
  let out (n : ℕ) := tagNumber (.inr (path n,s n))
  let incoming : ℕ → ℕ := Nat.rec (tagNumber (.inl [])) (fun n _ => out n)
  have edge (n : ℕ) : path n ++ [s n] ∈ T := hs (n+1)
  have outTag (n : ℕ) : out n ∈ sectorTags T (path n) :=
    (tagNumber_mem_sector ..).mpr (by simp [tagSupport,edge])
  have inTag (n : ℕ) : incoming n ∈ sectorTags T (path n) := by
    cases n with
    | zero => exact (tagNumber_mem_sector ..).mpr (Finset.mem_singleton_self _)
    | succ n =>
      apply (tagNumber_mem_sector T (path (n+1)) (.inr (path n,s n))).mpr
      simp [tagSupport,edge,show path (n+1)=path n ++ [s n] from rfl]
  obtain ⟨t,ht,_⟩ := G.vertex_limit
  obtain ⟨P,pair,limits⟩ := G.convergent_blocks ht path inj incoming out inTag outTag
  let W (n : ℕ) := TopCat.of (P n).site
  let A (n : ℕ) := TopCat.of (P n).base
  let B (n : ℕ) := TopCat.of (P n).row
  have form (n : ℕ) : spaceType (W n) = spaceType (A n) + spaceType (B n) :=
    clopen_sup_type _ _ (P n).apart
  have exchange (n : ℕ) : spaceType (A n) + spaceType (shiftFamily (TopCat.of RootRow) B n) =
      spaceType (A n) + spaceType (B n) := by
    change _ = spaceType (A n) + spaceType (P n).row
    rw [(P n).row_type]
    cases n with
    | zero => exact (P 0).exchange
    | succ n =>
      change spaceType (A (n+1)) + spaceType (P n).row = _
      rw [(P n).row_type]
      exact (P (n+1)).exchange
  let := (row_stone (tagNumber (.inl [])) 0).1
  exact block_sum_absorption t (fun n => (P n).site) pair (fun n => (P n).limit_out) limits
    (ray_absorption (TopCat.of RootRow) W A B form exchange)

theorem guarded_absorption_iff_branch {T : tree ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [ZeroDimensionalSpace X] [Countable (Clopens X)] (G : GuardData T X) :
    Nonempty ((X ⊕ RootRow) ≃ₜ X) ↔ HasBranch T :=
  ⟨fun ⟨f⟩ => guarded_absorption_implies_branch G f,guarded_branch_implies_absorption G⟩

/-- For each countable ordinal bound there is a satisfiable pure Boolean
Π_(ω+4) sentence with no countable model of robust Scott rank at most that bound. -/
theorem negativeResolution : NegativeResolution :=
  negativeResolution_of_branch_realization (fun _ _ _ _ _ _ _ G => guarded_branch_implies_absorption G)

end BooleanScott
