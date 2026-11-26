module
public import BooleanScott.VertexSectors

/-! A finite signed census on the integer labels of the actual charts gives
a descending branch. The argument uses signs on retained edges, including
the case of an infinitely branching vertex with finite current support. -/
@[expose] public section
namespace BooleanScott
open Descriptive

structure TagCurrents (T : tree ℕ) where
  diff : Vertex → ℕ →₀ ℤ
  incident (v : Vertex) (e : ℕ) : diff v e ≠ 0 → e ∈ sectorTags T v
  private_zero (v : Vertex) : diff v (tagNumber (.inl v)) = 0
  opposite (v : Vertex) (i : ℕ) : v++[i] ∈ T →
    diff v (tagNumber (.inr (v,i))) + diff (v++[i]) (tagNumber (.inr (v,i))) = 0
  divergence (v : Vertex) : rootTotal (diff v) = if v=[] then 1 else 0

theorem TagCurrents.positive_edge {T : tree ℕ} (F : TagCurrents T) {v : Vertex} {e : ℕ} (pos : 0 < F.diff v e) :
    ∃ (w : Vertex) (i : ℕ), e=tagNumber (.inr (w,i)) ∧ w++[i] ∈ T ∧ (v=w ∨ v=w++[i]) := by
  classical
  obtain ⟨t,eq,h⟩ := F.incident v e pos.ne'
  subst e
  cases t with
  | inl w =>
    have same : v=w := Finset.mem_singleton.mp h
    subst w
    exact ((F.private_zero v).not_gt pos).elim
  | inr p =>
    obtain ⟨w,i⟩ := p
    by_cases edge : w++[i] ∈ T
    · exact ⟨w,i,rfl,edge,by simpa [tagSupport,edge] using h⟩
    · simp [tagSupport,edge] at h

theorem TagCurrents.positive_root {T : tree ℕ} (F : TagCurrents T) :
    ∃ i : ℕ, 0 < F.diff [] (tagNumber (.inr ([],i))) := by
  have pos : ∃ e, 0 < F.diff [] e := by
    by_contra! no
    have bound : ∑ e ∈ (F.diff []).support, (F.diff []) e ≤ 0 := Finset.sum_nonpos (fun e _ => no e)
    have h := F.divergence []
    change ∑ e ∈ (F.diff []).support, (F.diff []) e = _ at h
    simp only [ite_true] at h
    omega
  obtain ⟨e,he⟩ := pos
  obtain ⟨w,i,rfl,_,h|h⟩ := F.positive_edge he
  · subst w; exact ⟨i,he⟩
  · simp at h

theorem TagCurrents.retained_outgoing {T : tree ℕ} (F : TagCurrents T) (v : Vertex) (i : ℕ)
    (pos : 0 < F.diff v (tagNumber (.inr (v,i)))) : v++[i] ∈ T := by
  have h := (tagNumber_mem_sector T v (.inr (v,i))).mp (F.incident v _ pos.ne')
  by_contra absent
  simp [tagSupport,absent] at h

theorem TagCurrents.continue_edge {T : tree ℕ} (F : TagCurrents T) (v : Vertex) (i : ℕ)
    (pos : 0 < F.diff v (tagNumber (.inr (v,i)))) :
    ∃ j, 0 < F.diff (v++[i]) (tagNumber (.inr (v++[i],j))) := by
  classical
  let w := v++[i]
  let e := tagNumber (.inr (v,i))
  have opp := F.opposite v i (F.retained_outgoing v i pos)
  have neg : F.diff w e < 0 := by dsimp [w,e]; omega
  have pos' : ∃ a, 0 < F.diff w a := by
    by_contra! no
    have mem : e ∈ (F.diff w).support := Finsupp.mem_support_iff.mpr neg.ne
    have bound := Finset.sum_nonpos (s := (F.diff w).support.erase e) (fun a _ => no a)
    have div := F.divergence w
    change ∑ a ∈ (F.diff w).support, (F.diff w) a = _ at div
    rw [ite_eq_right (show w ≠ [] by simp [w])] at div
    have eq := Finset.sum_erase_add (f := fun a => F.diff w a) _ mem
    omega
  obtain ⟨a,ha⟩ := pos'
  obtain ⟨u,j,rfl,_,left|right⟩ := F.positive_edge ha
  · subst u; exact ⟨j,ha⟩
  · have ends : v=u ∧ i=j := by simpa [w,and_comm] using congrArg List.reverse right
    obtain ⟨rfl,rfl⟩ := ends
    exact (neg.not_gt ha).elim

theorem TagCurrents.hasBranch {T : tree ℕ} (F : TagCurrents T) : HasBranch T := by
  classical
  let next (v : Vertex) := if h : ∃ i, 0 < F.diff v (tagNumber (.inr (v,i))) then h.choose else 0
  have step (v : Vertex) (h : ∃ i, 0 < F.diff v (tagNumber (.inr (v,i)))) :
      0 < F.diff v (tagNumber (.inr (v,next v))) := by simp only [next,dite_eq_left h]; exact h.choose_spec
  let node : ℕ → Vertex := Nat.rec [] fun _ w => w++[next w]
  have outgoing (n : ℕ) : 0 < F.diff (node n) (tagNumber (.inr (node n,next (node n)))) := by
    induction n with
    | zero => exact step [] F.positive_root
    | succ n ih => exact step _ (F.continue_edge _ _ ih)
  let a (n : ℕ) := next (node n)
  have path (n : ℕ) : initialSeg a n = node n := by
    induction n with
    | zero => rfl
    | succ n ih => rw [initialSeg,ih]
  exact ⟨a,fun n => path n ▸ T.prop (F.retained_outgoing _ _ (outgoing n))⟩

end BooleanScott
