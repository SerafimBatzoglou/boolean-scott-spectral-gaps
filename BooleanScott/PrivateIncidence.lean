module
public import BooleanScott.FiniteLoci
public import BooleanScott.SignTerms

/-! Two compact closed point sets that miss one another in a clopen can be
separated there by one more clopen. This yields finite-level incidence for
intersection of closed loci and hence for the private marks themselves. -/
@[expose] public section
namespace BooleanScott
open Set TopologicalSpace Ordinal

theorem compact_clopen_between {X : Type} [TopologicalSpace X] [ZeroDimensionalSpace X] {S U : Set X}
    (hs : IsCompact S) (hu : IsOpen U) (sub : S ⊆ U) :
    ∃ V : Clopens X, S ⊆ V ∧ (V : Set X) ⊆ U := by
  classical
  choose V hV memV subV using fun x : S => exists_isClopen_mem_of_isOpen hu (sub x.property)
  obtain ⟨F,hF⟩ := hs.elim_finite_subcover V (fun x => (hV x).isOpen)
    (fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,memV _⟩)
  exact ⟨⟨_,isClopen_biUnion_finset (fun x (_ : x ∈ F) => hV x)⟩,hF,
    iUnion₂_subset fun x _ => subV x⟩

theorem clopen_hits_intersection {X : Type} [TopologicalSpace X] [CompactSpace X] [ZeroDimensionalSpace X]
    (C : Clopens X) {P Q : Set X} (hp : IsClosed P) (hq : IsClosed Q) :
    ((C : Set X) ∩ (P ∩ Q)).Nonempty ↔ ∀ U : Clopens X,
      (((C ⊓ Uᶜ : Clopens X) : Set X) ∩ P).Nonempty ∨ (((C ⊓ U : Clopens X) : Set X) ∩ Q).Nonempty := by
  classical
  constructor
  · rintro ⟨x,hc,hp,hq⟩ U
    by_cases hx : x ∈ U
    · exact Or.inr ⟨x,⟨hc,hx⟩,hq⟩
    · exact Or.inl ⟨x,⟨hc,hx⟩,hp⟩
  · intro every
    by_contra empty
    have sub : (C : Set X) ∩ P ⊆ Qᶜ := fun x ⟨cx,px⟩ qx => empty ⟨x,cx,px,qx⟩
    obtain ⟨U,left,right⟩ := compact_clopen_between (C.isClopen.isClosed.inter hp).isCompact hq.isOpen_compl sub
    obtain ⟨x,⟨cx,nu⟩,px⟩ | ⟨x,⟨_,ux⟩,qx⟩ := every U
    · exact nu (left ⟨cx,px⟩)
    · exact right ux qx

def LocalLocus.intersect (P Q : LocalLocus) : LocalLocus where
  points X _ := P.points X ∩ Q.points X
  restricts e := by rw [preimage_inter,P.restricts e,Q.restricts e]

def ClosedLocus (P : LocalLocus) := ∀ (X : Type) [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [ZeroDimensionalSpace X], IsClosed (P.points X)

theorem closed_stage {P : LocalLocus} (closed : ClosedLocus P) (k : ℕ) : ClosedLocus (P.stage k) := by
  intro X _ _ _ _
  cases k with
  | zero => exact closed X
  | succ k =>
    change IsClosed (derivatives (k+1) (P.points X))
    rw [derivatives_succ]
    exact isClosed_derivedSet _

theorem finiteHit_closed_intersection {P Q : LocalLocus} (hp : FiniteHit P) (hq : FiniteHit Q)
    (cp : ClosedLocus P) (cq : ClosedLocus Q) : FiniteHit (P.intersect Q) := by
  obtain ⟨a,φ,_,lev,t⟩ := hp
  obtain ⟨b,ψ,_,lev',s⟩ := hq
  let m := max a b
  let slot : Term (1+1) := .var (Fin.castAdd 1 (0 : Fin 1))
  let parent : Term (1+1) := .var (Fin.natAdd 1 (0 : Fin 1))
  let f := φ.substitute (fun _ => .meet parent (.compl slot))
  let g := ψ.substitute (fun _ => .meet parent slot)
  have l : AtLevel .pi (m : Ordinal.{0}) f := (lev.substitute _).liftLevel (by exact_mod_cast Nat.le_max_left a b)
  have r : AtLevel .pi (m : Ordinal.{0}) g := (lev'.substitute _).liftLevel (by exact_mod_cast Nat.le_max_right a b)
  let branch (i : Bool) := if i then f else g
  have hb (i : Bool) : AtLevel .pi (m : Ordinal.{0}) (branch i) := by cases i <;> first | exact l | exact r
  let χ := disjoinPi branch
  let θ : Formula 1 := .pi (fun _ => 1) (fun _ => χ)
  have lθ : AtLevel .pi ((m : Ordinal.{0})+1+1) θ :=
    .pi (fun _ => (m : Ordinal.{0})+1) (fun _ => lt_add_one _) (fun _ => disjoinPi_level hb)
  refine ⟨m+1+1,θ,by omega,by simpa using lθ,fun X _ _ _ _ C => ?_⟩
  let M := BoolOps.ofAlgebra (Clopens X)
  have meaning (w : Fin 1 → Clopens X) : χ.Holds M (Fin.append w (fun _ => C)) ↔
      (((C ⊓ (w 0)ᶜ : Clopens X) : Set X) ∩ P.points X).Nonempty ∨
      (((C ⊓ w 0 : Clopens X) : Set X) ∩ Q.points X).Nonempty := by
    apply (holds_disjoinPi branch M _).trans
    have left : f.Holds M (Fin.append w (fun _ => C)) ↔ _ :=
      (φ.holds_substitute _ M _).trans (by simpa only [Term.eval,BoolOps.ofAlgebra,M,slot,parent,Fin.append_left,Fin.append_right] using t X (C ⊓ (w 0)ᶜ))
    have right : g.Holds M (Fin.append w (fun _ => C)) ↔ _ :=
      (ψ.holds_substitute _ M _).trans (by simpa only [Term.eval,BoolOps.ofAlgebra,M,slot,parent,Fin.append_left,Fin.append_right] using s X (C ⊓ w 0))
    constructor
    · rintro ⟨i,hi⟩
      cases i
      · exact Or.inr (right.mp hi)
      · exact Or.inl (left.mp hi)
    · rintro (h|h)
      · exact ⟨true,left.mpr h⟩
      · exact ⟨false,right.mpr h⟩
  apply Iff.trans _ (clopen_hits_intersection C (cp X) (cq X)).symm
  exact ⟨fun h U => (meaning (fun _ => U)).mp (h 0 _),fun h _ w => (meaning w).mpr (h (w 0))⟩

theorem private_finiteHit (j : ℕ) : FiniteHit (privateLocus j) := by
  let D := isolatedClosureLocus
  have cd : ClosedLocus D := fun X _ _ _ _ => isClosed_closure
  let O := (fullLocus.difference D).closedHull
  have ho : FiniteHit O := finiteHit_hull (finiteHit_difference full_finiteHit isolatedClosure_finiteHit cd)
  have co : ClosedLocus O := fun X _ _ _ _ => isClosed_closure
  let B := D.intersect O
  have hb : FiniteHit B := finiteHit_closed_intersection isolatedClosure_finiteHit ho cd co
  have cb : ClosedLocus B := fun X _ _ _ _ => (cd X).inter (co X)
  have pair := finiteHit_closed_intersection hb (finiteHit_stages isolatedClosure_finiteHit (j+1)) cb (closed_stage cd _)
  have h := finiteHit_difference pair (finiteHit_stages isolatedClosure_finiteHit (j+2)) (closed_stage cd _)
  obtain ⟨k,φ,pos,lev,t⟩ := h
  refine ⟨k,φ,pos,lev,fun X _ _ _ _ => ?_⟩
  have eq : (((B.intersect (D.stage (j+1))).difference (D.stage (j+2))).points X) = privateMark X j := by
    ext x
    simp only [LocalLocus.difference,LocalLocus.intersect,LocalLocus.closedHull,LocalLocus.stage,B,D,O,
      fullLocus,isolatedClosureLocus,← compl_eq_univ_sdiff,privateMark,mixedBoundary,mem_inter_iff,mem_sdiff]
    tauto
  change Detects φ (privateMark X j)
  rw [← eq]
  exact t X

end BooleanScott
