module
public import BooleanScott.Diagonal

/-! The retained-edge predicate for the specific diagonal family is clopen.
Its finite set of relevant coordinates can depend on the parameter. -/
@[expose] public section
namespace BooleanScott
open Set Filter Topology

private theorem locally_fixed_eval (c : Baire) (i : ℕ) : ∀ᶠ d in 𝓝 c, d i = c i :=
  (continuous_apply i).continuousAt (isOpen_discrete ({c i} : Set ℕ) |>.mem_nhds rfl)

private theorem locally_fixed_prefix (c : Baire) (n : ℕ) :
    ∀ᶠ d in 𝓝 c, initialSeg d n = initialSeg c n := by
  induction n with
  | zero => exact Eventually.of_forall (fun _ => rfl)
  | succ n ih =>
    filter_upwards [ih, locally_fixed_eval c n] with d hd hi
    simp only [initialSeg,hd,hi]

theorem clopen_tree_membership (s : List ℕ) : IsClopen {c : Baire | s ∈ diagonalTree c} := by
  have stable (c : Baire) : ∀ᶠ d in 𝓝 c, (s ∈ diagonalTree d ↔ s ∈ diagonalTree c) := by
    let idx (d : Baire) (m : ℕ) := Encodable.encode (initialSeg d m, s.take m)
    have test (m : ℕ) : ∀ᶠ d in 𝓝 c, d (idx d m) = c (idx c m) := by
      filter_upwards [locally_fixed_prefix c m, locally_fixed_eval c (idx c m)] with d hp he
      simpa only [idx,hp] using he
    let F := Finset.range (s.length+1)
    have allTests := (eventually_all_finite F.finite_toSet).mpr (fun m _ => test m)
    filter_upwards [allTests] with d hd
    have same (m : ℕ) (hm : m ≤ s.length) : d (idx d m) = c (idx c m) :=
      hd m (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
    change (∀ m ≤ s.length, d (idx d m) ≠ 0) ↔ (∀ m ≤ s.length, c (idx c m) ≠ 0)
    exact ⟨fun H m hm => same m hm ▸ H m hm,fun H m hm => (same m hm).symm ▸ H m hm⟩
  constructor
  · apply isOpen_compl_iff.mp
    apply isOpen_iff_mem_nhds.mpr
    intro c hc
    filter_upwards [stable c] with d hd using fun h => hc (hd.mp h)
  · apply isOpen_iff_mem_nhds.mpr
    intro c hc
    filter_upwards [stable c] with d hd using hd.mpr hc

end BooleanScott
