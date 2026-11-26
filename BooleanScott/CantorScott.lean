module
public import BooleanScott.AtomlessMatching
public import BooleanScott.PacketStone
public import BooleanScott.Coding
public import BooleanScott.ClopenIntervals

/-! An actual finite-level Scott sentence for the countable clopen algebra
of Cantor space. It asserts nontriviality and the existence of a proper
nonzero subelement of each nonzero element. -/
@[expose] public section
namespace BooleanScott
open Set Topology TopologicalSpace

def hasProperParts (B : Type) [BooleanAlgebra B] : Prop :=
  (⊥ : B) ≠ ⊤ ∧ ∀ a : B, a ≠ ⊥ → ∃ b, b ≤ a ∧ b ≠ ⊥ ∧ b ≠ a

def splitQF : QF (1+(1+0)) :=
  let a : Term (1+(1+0)) := .var (Fin.natAdd 1 (0 : Fin 1))
  let b : Term (1+(1+0)) := .var (Fin.castAdd 1 (0 : Fin 1))
  let proper : QF _ := .and (.eq (.meet b a) b) (.and (.neg (.eq b .zero)) (.neg (.eq b a)))
  .and (.neg (.eq .zero .one)) (.neg (.and (.neg (.eq a .zero)) (.neg proper)))

def cantorSentence : Formula 0 :=
  .pi (fun _ => 1) (fun _ => .sigma (fun _ => 1) (fun _ => .qf splitQF))

theorem cantorSentence_level : AtLevel .pi 2 cantorSentence :=
  .pi (fun _ => 1) (fun _ => by norm_num) (fun _ =>
    .sigma (fun _ => 0) (fun _ => by norm_num) (fun _ => .qf _ _ _))

theorem cantorSentence_models (B : Type) [BooleanAlgebra B] :
    Models (BoolOps.ofAlgebra B) cantorSentence ↔ hasProperParts B := by
  classical
  have matrix (u v : Fin 1 → B) :
      splitQF.Holds (BoolOps.ofAlgebra B) (Fin.append u (Fin.append v Fin.elim0)) ↔
        (⊥ : B) ≠ ⊤ ∧ (v 0 ≠ ⊥ → u 0 ≤ v 0 ∧ u 0 ≠ ⊥ ∧ u 0 ≠ v 0) := by
    simp only [splitQF,QF.Holds,Term.eval,Fin.append_left,Fin.append_right,BoolOps.ofAlgebra,inf_eq_left]
    tauto
  constructor
  · intro h
    obtain ⟨_,u,hu⟩ := h 0 (fun _ => ⊥)
    refine ⟨((matrix u _).mp hu).1,fun a ha => ?_⟩
    obtain ⟨_,v,hv⟩ := h 0 (fun _ => a)
    exact ⟨v 0,((matrix v _).mp hv).2 ha⟩
  · rintro ⟨ht,part⟩ _ v
    by_cases h : v 0 = ⊥
    · exact ⟨0,fun _ => ⊥,(matrix _ v).mpr ⟨ht,fun ne => (ne h).elim⟩⟩
    · obtain ⟨b,hb⟩ := part _ h
      exact ⟨0,fun _ => b,(matrix _ v).mpr ⟨ht,fun _ => hb⟩⟩

private theorem nonempty_iff_ne_bot {X : Type} [TopologicalSpace X] (C : Clopens X) :
    (C : Set X).Nonempty ↔ C ≠ ⊥ := by
  rw [Set.nonempty_iff_ne_empty]
  change ((C : Set X) ≠ ((⊥ : Clopens X) : Set X)) ↔ _
  exact not_congr SetLike.coe_injective.eq_iff

theorem properParts_clopens_iff (X : Type) [TopologicalSpace X] :
    hasProperParts (Clopens X) ↔ Nonempty X ∧ SplitsClopens X := by
  classical
  constructor
  · rintro ⟨nt,part⟩
    have top := (nonempty_iff_ne_bot (⊤ : Clopens X)).mpr nt.symm
    refine ⟨⟨top.choose⟩,fun C hc => ?_⟩
    obtain ⟨D,le,pos,neq⟩ := part C ((nonempty_iff_ne_bot C).mp hc)
    obtain ⟨x,hx⟩ := (nonempty_iff_ne_bot D).mpr pos
    have outside : ¬ (C : Set X) ⊆ D := fun sub => neq (le_antisymm le sub)
    obtain ⟨y,hy,hn⟩ := Set.not_subset.mp outside
    exact ⟨D,⟨x,le hx,hx⟩,⟨y,hy,hn⟩⟩
  · rintro ⟨⟨x⟩,split⟩
    refine ⟨((nonempty_iff_ne_bot (⊤ : Clopens X)).mp ⟨x,trivial⟩).symm,fun a h => ?_⟩
    obtain ⟨D,⟨u,hu,hd⟩,⟨v,hv,hn⟩⟩ := split a ((nonempty_iff_ne_bot a).mpr h)
    refine ⟨a ⊓ D,inf_le_left,(nonempty_iff_ne_bot _).mp ⟨u,hu,hd⟩,?_⟩
    intro eq
    have hm : v ∈ a ⊓ D := by rw [eq]; exact hv
    exact hn hm.2

theorem splits_of_no_isolated (X : Type) [TopologicalSpace X] [T1Space X] [ZeroDimensionalSpace X]
    (none : isolatedPoints X = ∅) : SplitsClopens X := by
  intro C hC
  obtain ⟨x,hx⟩ := hC
  have acc : x ∈ derivedSet (univ : Set X) := by
    by_contra hn
    exact (Set.ext_iff.mp none x).mp hn
  obtain ⟨y,⟨hy,_⟩,hne⟩ := (accPt_iff_nhds.mp acc) C (C.isClopen.isOpen.mem_nhds hx)
  obtain ⟨U,hU,ux,sub⟩ := exists_isClopen_mem_of_isOpen (isOpen_compl_singleton (x := y)) hne.symm
  exact ⟨⟨U,hU⟩,⟨x,hx,ux⟩,⟨y,hy,fun uy => sub uy rfl⟩⟩

theorem cantorScott (B : Type) [Countable B] [BooleanAlgebra B] :
    Models (BoolOps.ofAlgebra B) cantorSentence ↔ Nonempty (Clopens CantorBits ≃o B) := by
  let := cantor_countable_clopens
  have reference : Models (BoolOps.ofAlgebra (Clopens CantorBits)) cantorSentence :=
    (cantorSentence_models _).mpr ((properParts_clopens_iff _).mpr
      ⟨inferInstance,splits_of_no_isolated CantorBits cantor_no_isolated⟩)
  constructor
  · intro m
    let e := stoneRepresentation B
    have h := (OpsIso.models cantorSentence_level (OpsIso.ofOrder e)).mp m
    obtain ⟨hne,sp⟩ := (properParts_clopens_iff (StoneModel B)).mp ((cantorSentence_models _).mp h)
    let := hne
    let := e.surjective.countable
    obtain ⟨f⟩ := splitting_clopens_iso (splits_of_no_isolated CantorBits cantor_no_isolated) sp
    exact ⟨f.trans e.symm⟩
  · rintro ⟨e⟩
    exact (OpsIso.models cantorSentence_level (OpsIso.ofOrder e)).mp reference

theorem cantor_nonempty_clopen (C : Clopens CantorBits) (nonempty : (C : Set CantorBits).Nonempty) :
    Nonempty (C ≃ₜ CantorBits) := by
  let := cantor_countable_clopens
  let := (clopenRestriction C).surjective.countable
  let : Nonempty C := nonempty.to_subtype
  let := clopen_compactSpace C
  have none : isolatedPoints C = ∅ := by
    exact (local_isolated C.isClopen.isOpen.isOpenEmbedding_subtypeVal).symm.trans (by rw [cantor_no_isolated,preimage_empty])
  obtain ⟨e⟩ := (cantorScott (Clopens C)).mp ((cantorSentence_models _).mpr
    ((properParts_clopens_iff _).mpr ⟨inferInstance,splits_of_no_isolated C none⟩))
  exact ⟨homeomorphOfClopens e.symm⟩

end BooleanScott
