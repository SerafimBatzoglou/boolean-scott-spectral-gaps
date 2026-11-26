module
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Tactic

/-! Equal finite ledger columns have a matching that fixes every common row.
Thus a row present on both sides eventually has only finitely many exceptional
columns, simultaneously for a bijection and its inverse. -/
@[expose] public section
namespace BooleanScott
open Filter

theorem matchColumn {I : Type*} (s t : Finset I) (h : s.card = t.card) :
    ∃ e : s ≃ t, ∀ x : s, x.val ∈ t → (e x).val = x.val := by
  classical
  let moved : (s \ t : Finset I) ≃ (t \ s : Finset I) :=
    Finset.equivOfCardEq (Finset.card_sdiff_comm h)
  let f (x : s) : t := if hx : x.val ∈ t then ⟨x.val,hx⟩ else
    let y := moved ⟨x.val,Finset.mem_sdiff.mpr ⟨x.property,hx⟩⟩
    ⟨y.val,(Finset.mem_sdiff.mp y.property).1⟩
  let g (y : t) : s := if hy : y.val ∈ s then ⟨y.val,hy⟩ else
    let x := moved.symm ⟨y.val,Finset.mem_sdiff.mpr ⟨y.property,hy⟩⟩
    ⟨x.val,(Finset.mem_sdiff.mp x.property).1⟩
  have gf (x : s) : g (f x) = x := by
    by_cases hx : x.val ∈ t
    · apply Subtype.ext
      simp [f,g,hx,x.property]
    · let a : (s \ t : Finset I) := ⟨x.val,Finset.mem_sdiff.mpr ⟨x.property,hx⟩⟩
      have hn := (Finset.mem_sdiff.mp (moved a).property).2
      apply Subtype.ext
      simpa only [f, g, dite_eq_right hx, a, dite_eq_right hn] using
        congrArg Subtype.val (moved.symm_apply_apply a)
  have fg (y : t) : f (g y) = y := by
    by_cases hy : y.val ∈ s
    · apply Subtype.ext
      simp [f,g,hy,y.property]
    · let b : (t \ s : Finset I) := ⟨y.val,Finset.mem_sdiff.mpr ⟨y.property,hy⟩⟩
      have hn := (Finset.mem_sdiff.mp (moved.symm b).property).2
      apply Subtype.ext
      simpa only [f, g, dite_eq_right hy, b, dite_eq_right hn] using
        congrArg Subtype.val (moved.apply_symm_apply b)
  exact ⟨⟨f,g,gf,fg⟩,fun x hx => by change (f x).val = _; simp [f,hx]⟩

/-- After pairing rows by tag, a column is the finite set of row indices
containing its ledger packet. All off-row departures and arrivals are
confined to an initial finite segment that can depend on the row. -/
theorem protectedTransport {I : Type*} (s t : ℕ → Finset I)
    (count : ∀ j, (s j).card = (t j).card)
    (src : ∀ i, ∀ᶠ j in atTop, i ∈ s j)
    (dst : ∀ i, ∀ᶠ j in atTop, i ∈ t j) :
    ∃ e : ∀ j, s j ≃ t j, ∀ i, ∃ k : ℕ, ∀ j ≥ k,
      (∀ x : s j, x.val = i → (e j x).val = i) ∧
      (∀ y : t j, y.val = i → ((e j).symm y).val = i) := by
  classical
  choose e fixed using fun j => matchColumn (s j) (t j) (count j)
  refine ⟨e,fun i => ?_⟩
  obtain ⟨k,hk⟩ := eventually_atTop.mp ((src i).and (dst i))
  refine ⟨k,fun j hj => ?_⟩
  obtain ⟨hs,ht⟩ := hk j hj
  constructor
  · rintro x rfl
    exact fixed j x ht
  · intro y hy
    let x : s j := ⟨i,hs⟩
    have hxy : e j x = y := Subtype.ext ((fixed j x ht).trans hy.symm)
    rw [← hxy, Equiv.symm_apply_apply]

end BooleanScott
