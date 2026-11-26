module
public import BooleanScott.CompactArrays
public import Mathlib.Order.Filter.AtTopBot.Finite

/-! Eventual ledger counts in arbitrary clopen fragments missing the vertex.
Individual rows may have different first columns and different convergence times. -/
@[expose] public section
namespace BooleanScott
open Set Filter Topology
open scoped OnePoint

/-- Picking one point per distinct packet gives a sequence converging to the
row root. It does not matter where in the packet the point was picked. -/
theorem packetMarkers_tendsto {E : Type} {P : E → Type} [∀ e, TopologicalSpace (P e)]
    (q : ℕ ↪ E) (x : ∀ j, P (q j)) :
    Tendsto (fun j => OnePoint.some (Sigma.mk (q j) (x j))) atTop (𝓝 ∞) := by
  intro U hU
  obtain ⟨F,hF⟩ := cofinite_components_of_nhds hU
  have he : ∀ᶠ j : ℕ in atTop, q j ∉ F :=
    by
    rw [← Nat.cofinite_eq_atTop]
    exact q.injective.tendsto_cofinite F.finite_toSet.compl_mem_cofinite
  change ∀ᶠ j : ℕ in atTop, OnePoint.some (Sigma.mk (q j) (x j)) ∈ U
  filter_upwards [he] with j hj using hF _ hj _

variable {I : Type} {X : I → Type} [∀ i, TopologicalSpace (X i)] [∀ i, CompactSpace (X i)]

/-- Each eligible row has one designated private marker in a column. Only
the eligible rows contribute. Values of m elsewhere have no effect. -/
def markedRows (m : ∀ i, ℕ → X i) (eligible : I → ℕ → Prop)
    (C : Set (OnePoint (Σ i, X i))) (j : ℕ) : Set I :=
  {i | eligible i j ∧ OnePoint.some (Sigma.mk i (m i j)) ∈ C}

def rootRows (r : ∀ i, X i) (C : Set (OnePoint (Σ i, X i))) : Set I :=
  {i | OnePoint.some (Sigma.mk i (r i)) ∈ C}

/-- For a compact clopen missing the vertex, all sufficiently large columns
identify *exactly* the row indices of the retained roots. A fragment need not
be a union of whole packets or whole rows. -/
theorem fragment_markedRows {m : ∀ i, ℕ → X i} {r : ∀ i, X i} {eligible : I → ℕ → Prop}
    (conv : ∀ i, Tendsto (m i) atTop (𝓝 (r i)))
    (tail : ∀ i, ∀ᶠ j in atTop, eligible i j)
    {C : Set (OnePoint (Σ i, X i))} (hc : IsClopen C) (away : ∞ ∉ C) :
    (rootRows r C).Finite ∧ ∀ᶠ j in atTop, markedRows m eligible C j = rootRows r C := by
  classical
  obtain ⟨localClopen,F,outside⟩ := (clopen_array_iff C).mp hc
  have never (i : I) (hi : i ∉ F) (x : X i) : OnePoint.some (Sigma.mk i x) ∉ C :=
    fun hx => away ((outside i hi x).mp hx)
  refine ⟨F.finite_toSet.subset (fun i hi => by
    by_contra h; exact never i h (r i) hi), ?_⟩
  have within (i : I) : ∀ᶠ j in atTop, i ∈ markedRows m eligible C j ↔ i ∈ rootRows r C := by
    let S : Set (X i) := {x | OnePoint.some (Sigma.mk i x) ∈ C}
    by_cases h : r i ∈ S
    · have hm := conv i ((localClopen i).isOpen.mem_nhds h)
      filter_upwards [hm,tail i] with j hj he
      exact iff_of_true ⟨he,hj⟩ h
    · have hm := conv i ((localClopen i).compl.isOpen.mem_nhds h)
      filter_upwards [hm] with j hj
      exact iff_of_false (fun z => hj z.2) h
  have uniform := (eventually_all_finite F.finite_toSet).mpr (fun i _ => within i)
  filter_upwards [uniform] with j hj
  ext i
  by_cases h : i ∈ F
  · exact hj i h
  · exact iff_of_false (fun z => never i h _ z.2) (never i h _)

end BooleanScott
