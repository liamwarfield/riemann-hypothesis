module

public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.AdmFourteen

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.ExistsIsotypicDecomposition
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.Joints Formalism.MainNotions.LemmaBAlt

theorem span_inter_eq_span_image {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] (hinj : Function.Injective (algebraMap O Kf))
    {σ X : Type} (bO : X → MvPolynomial σ O) (bK : X → MvPolynomial σ Kf)
    (hmap : ∀ x, MvPolynomial.map (algebraMap O Kf) (bO x) = bK x) (hLI : LinearIndependent Kf bK)
    (Y : Submodule Kf (MvPolynomial σ Kf)) (A : Set X)
    (hY : Submodule.span Kf (Set.range bK) ⊓ Y = Submodule.span Kf (bK '' A)) :
    {f | f ∈ Submodule.span O (Set.range bO) ∧ MvPolynomial.map (algebraMap O Kf) f ∈ Y} =
      (Submodule.span O (bO '' A) : Set _) := by
  classical
  have hmaplc : ∀ c : X →₀ O, MvPolynomial.map (algebraMap O Kf) (Finsupp.linearCombination O bO c) =
      Finsupp.linearCombination Kf bK (c.mapRange (algebraMap O Kf) (map_zero _)) := by
    intro c
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply,
      Finsupp.sum_mapRange_index (by intro i; exact zero_smul _ _), Finsupp.sum, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, hmap, ← MvPolynomial.smul_eq_C_mul]
  ext G
  constructor
  · rintro ⟨hG, hGY⟩
    obtain ⟨c, rfl⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hG
    change (c.sum fun x a => a • bO x) ∈ Submodule.span O (bO '' A)
    refine Submodule.sum_mem _ fun x hx => Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, ?_, rfl⟩)
    have h1 : MvPolynomial.map (algebraMap O Kf) (Finsupp.linearCombination O bO c) ∈
        Submodule.span Kf (bK '' A) := by
      rw [← hY]
      refine ⟨?_, hGY⟩
      rw [hmaplc]
      exact Finsupp.mem_span_range_iff_exists_finsupp.2 ⟨_, rfl⟩
    obtain ⟨l, hl, hle⟩ := (Finsupp.mem_span_image_iff_linearCombination Kf).1 h1
    rw [hmaplc] at hle
    have hlc := hLI hle
    have hxl : x ∈ l.support := by
      rw [hlc, Finsupp.mem_support_iff, Finsupp.mapRange_apply]
      intro h0
      exact (Finsupp.mem_support_iff.1 hx) (hinj (by rw [h0, map_zero]))
    exact (Finsupp.mem_supported Kf l).1 hl hxl
  · intro hG
    change G ∈ Submodule.span O (bO '' A) at hG
    induction hG using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      refine ⟨Submodule.subset_span ⟨x, rfl⟩, ?_⟩
      rw [hmap]
      have : bK x ∈ Submodule.span Kf (Set.range bK) ⊓ Y := by
        rw [hY]
        exact Submodule.subset_span ⟨x, hx, rfl⟩
      exact this.2
    | zero => exact ⟨Submodule.zero_mem _, by rw [map_zero]; exact Submodule.zero_mem _⟩
    | add x y _ _ hx hy =>
      exact ⟨Submodule.add_mem _ hx.1 hy.1, by rw [map_add (f := _)]; exact Submodule.add_mem _ hx.2 hy.2⟩
    | smul a x _ hx =>
      exact ⟨Submodule.smul_mem _ _ hx.1, by
        rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
        exact Submodule.smul_mem _ _ hx.2⟩

abbrev GLWeightLabels (N r K : ℕ) : Fin (N + 1) ⊕ Fin (N + 1) → Type
  | .inl _ => Fin r → ℤ
  | .inr _ => Fin K → ℤ

structure ExternalProductHyps : Prop where
  p16 : ExternalProductBasis
  e1 : GlOperatorsFormRepresentation
  e2 : IsotypicZeroOfNonDominant
  e3 : ProjectorsPreserveMultidegree
  e5a : ProjectorsCommuteNested
  e5b : ProjectorsCommuteDisjoint
  lowPl : RestLowPl
  lowTan : RestLowTan
  sum : RestJointSum

section

variable (D : Formalism.BasicNotions.D7) (H : ExternalProductHyps) {F : Type} [Field F] [CharZero F] {N : ℕ} (r K : ℕ) (LL : Letters (Fin N))
  (B : Fin N → ℕ)

include D H in
theorem exists_decSys_isoSub_glOpsE_of_injective {m k : ℕ} (S : Set (Fin N)) (e : Fin m → Fin k) (he : Function.Injective e) :
    ∃ pr : (Fin m → ℤ) → Module.End F (MvPolynomial (Fin N × Fin k) F), DecSys (isoSub (glOpsE F LL S e)) pr :=
  isoDecomp (glOpsE F LL S e) D (weight_condition_from_integral_form D) (H.e1 F N m k LL S e he)

abbrev EPl (F : Type) [Field F] {N : ℕ} (r K : ℕ) (LL : Letters (Fin N)) (i : Fin (N + 1)) :
    GLOps r F (MvPolynomial (Fin N × Fin (r + K)) F) := glOpsE F LL {j | j.val < i.val} (Fin.castAdd K)

abbrev ETan (F : Type) [Field F] {N : ℕ} (r K : ℕ) (LL : Letters (Fin N)) (i : Fin (N + 1)) :
    GLOps K F (MvPolynomial (Fin N × Fin (r + K)) F) := glOpsE F LL {j | j.val < i.val} (Fin.natAdd r)

def prPl (i : Fin (N + 1)) : (Fin r → ℤ) → Module.End F (MvPolynomial (Fin N × Fin (r + K)) F) :=
  Classical.choose (exists_decSys_isoSub_glOpsE_of_injective (F := F) D H LL {j | j.val < i.val} (Fin.castAdd K) (Fin.castAdd_injective r K))

def prTan (i : Fin (N + 1)) : (Fin K → ℤ) → Module.End F (MvPolynomial (Fin N × Fin (r + K)) F) :=
  Classical.choose (exists_decSys_isoSub_glOpsE_of_injective (F := F) D H LL {j | j.val < i.val} (Fin.natAdd r) (Fin.natAdd_injective K r))

theorem prPl_sys (i : Fin (N + 1)) : DecSys (isoSub (EPl F r K LL i)) (prPl D H r K LL i) :=
  Classical.choose_spec (exists_decSys_isoSub_glOpsE_of_injective (F := F) D H LL {j | j.val < i.val} (Fin.castAdd K) (Fin.castAdd_injective r K))

theorem prTan_sys (i : Fin (N + 1)) : DecSys (isoSub (ETan F r K LL i)) (prTan D H r K LL i) :=
  Classical.choose_spec (exists_decSys_isoSub_glOpsE_of_injective (F := F) D H LL {j | j.val < i.val} (Fin.natAdd r) (Fin.natAdd_injective K r))

theorem initialSegments_nested (i j : Fin (N + 1)) :
    ({l : Fin N | l.val < i.val} ⊆ {l : Fin N | l.val < j.val}) ∨
      ({l : Fin N | l.val < j.val} ⊆ {l : Fin N | l.val < i.val}) := by
  rcases le_total i j with h | h
  · exact Or.inl fun l (hl : l.val < i.val) => lt_of_lt_of_le hl h
  · exact Or.inr fun l (hl : l.val < j.val) => lt_of_lt_of_le hl h

theorem fin_castAdd_ne_natAdd (a : Fin r) (b : Fin K) : Fin.castAdd K a ≠ Fin.natAdd r b := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at this
  omega

def externalProductJointData : JointData F (MvPolynomial (Fin N × Fin (r + K)) F) (Fin (N + 1) ⊕ Fin (N + 1)) (GLWeightLabels N r K)
    (PIdx r K LL B) where
  le := fun s => match s with
    | .inl _ => DomLE
    | .inr _ => DomLE
  dom := fun s => match s with
    | .inl _ => Dominant
    | .inr _ => Dominant
  le_refl := fun s => match s with
    | .inl _ => fun a => dominance_refl a
    | .inr _ => fun a => dominance_refl a
  le_trans := fun s => match s with
    | .inl _ => fun _ _ _ h1 h2 => dominance_trans h1 h2
    | .inr _ => fun _ _ _ h1 h2 => dominance_trans h1 h2
  le_antisymm := fun s => match s with
    | .inl _ => fun _ _ h1 h2 => dominance_antisymm h1 h2
    | .inr _ => fun _ _ h1 h2 => dominance_antisymm h1 h2
  W := fun s => match s with
    | .inl i => isoSub (EPl F r K LL i)
    | .inr i => isoSub (ETan F r K LL i)
  e := fun s => match s with
    | .inl i => prPl D H r K LL i
    | .inr i => prTan D H r K LL i
  sys := fun s => match s with
    | .inl i => prPl_sys D H r K LL i
    | .inr i => prTan_sys D H r K LL i
  comm := fun s t => match s, t with
    | .inl i, .inl j => fun a b => H.e5a F N r (r + K) LL _ _ _ (Fin.castAdd_injective r K) (initialSegments_nested i j) _ _
        (prPl_sys D H r K LL i) (prPl_sys D H r K LL j) a b
    | .inr i, .inr j => fun a b => H.e5a F N K (r + K) LL _ _ _ (Fin.natAdd_injective K r) (initialSegments_nested i j) _ _
        (prTan_sys D H r K LL i) (prTan_sys D H r K LL j) a b
    | .inl i, .inr j => fun a b => H.e5b F N r K (r + K) LL _ _ _ _ (Fin.castAdd_injective r K)
        (Fin.natAdd_injective K r) (fin_castAdd_ne_natAdd r K) _ _ (prPl_sys D H r K LL i) (prTan_sys D H r K LL j) a b
    | .inr i, .inl j => fun a b => (H.e5b F N r K (r + K) LL _ _ _ _ (Fin.castAdd_injective r K)
        (Fin.natAdd_injective K r) (fin_castAdd_ne_natAdd r K) _ _ (prPl_sys D H r K LL j) (prTan_sys D H r K LL i) b a).symm
  bot := fun s => match s with
    | .inl i => fun a h => H.e2 F N r (r + K) LL _ _ (Fin.castAdd_injective r K) a h
    | .inr i => fun a h => H.e2 F N K (r + K) LL _ _ (Fin.natAdd_injective K r) a h
  Pl := Pol F (r + K) B
  stab := fun s => match s with
    | .inl i => fun a x hx => H.e3 F N r (r + K) LL _ _ (Fin.castAdd_injective r K) _ (prPl_sys D H r K LL i) B a x hx
    | .inr i => fun a x hx => H.e3 F N K (r + K) LL _ _ (Fin.natAdd_injective K r) _ (prTan_sys D H r K LL i) B a x hx
  b := pvec F r K LL B
  P := fun x s => match s with
    | .inl i => x.1.1.1 i
    | .inr i => x.1.2.1 i
  Pdom := fun x s => match s with
    | .inl i => by
        obtain ⟨_, _, _, ⟨P1, h1⟩, _⟩ := x.2.1
        exact h1 ▸ P1.dom i
    | .inr i => by
        obtain ⟨_, _, _, _, ⟨P2, h2⟩⟩ := x.2.1
        exact h2 ▸ P2.dom i
  li := (H.p16 F N r K LL B).1
  span := (H.p16 F N r K LL B).2
  low := fun s => match s with
    | .inl i => fun pi h1 h2 => H.lowPl F N r K LL B i pi ⟨h1, h2⟩
    | .inr i => fun pi h1 h2 => H.lowTan F N r K LL B i pi ⟨h1, h2⟩

end

end Formalism.MainNotions.G.ColumnFamilies
end
end

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.Joints Formalism.MainNotions.LemmaBAlt

theorem externalProduct_index_finite (H : ExternalProductHyps) {N : ℕ} (r K : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) :
    Finite (PIdx r K LL B) := by
  have := standardPath_index_finite N (r + K) LL B
  refine LinearIndependent.finite_of_le_span_finite _ (H.p16 ℚ N r K LL B).1 (Set.range (wd LL B ℚ)) ?_
  rw [span_words_eq_polynomials, ← (H.p16 ℚ N r K LL B).2]
  exact Submodule.subset_span

theorem span_inf_iSup_externalProduct (D : Formalism.BasicNotions.D7) (H : ExternalProductHyps) (F : Type) [Field F] [CharZero F] {N : ℕ} (r K : ℕ)
    (LL : Letters (Fin N)) (B : Fin N → ℕ) (pi' : Fin (N + 1) → Set (Fin r → ℤ))
    (pi'' : Fin (N + 1) → Set (Fin K → ℤ)) (h' : ∀ i, DomLowerSet (pi' i)) (h'' : ∀ i, DomLowerSet (pi'' i)) :
    Submodule.span F (Set.range (pvec F r K LL B)) ⊓
        (⨆ q ∈ {q : (Fin (N + 1) → Fin r → ℤ) × (Fin (N + 1) → Fin K → ℤ) | ∀ i, q.1 i ∈ pi' i ∧ q.2 i ∈ pi'' i},
          jointType F LL q.1 q.2) =
      Submodule.span F (pvec F r K LL B '' {x | ∀ i, x.1.1.1 i ∈ pi' i ∧ x.1.2.1 i ∈ pi'' i}) := by
  have := externalProduct_index_finite H r K LL B
  let pi : ∀ s, Set (GLWeightLabels N r K s) := fun s => match s with
    | .inl i => pi' i
    | .inr i => pi'' i
  have key := H.sum F _ (Fin (N + 1) ⊕ Fin (N + 1)) (GLWeightLabels N r K) (PIdx r K LL B) (externalProductJointData D H r K LL B) pi
    (fun s => match s with
      | .inl i => (h' i).1
      | .inr i => (h'' i).1)
    (fun s => match s with
      | .inl i => (h' i).2
      | .inr i => (h'' i).2)
  have hsup : (⨆ q ∈ {q : ∀ s, GLWeightLabels N r K s | ∀ s, q s ∈ pi s}, ⨅ s, (externalProductJointData (F := F) D H r K LL B).W s (q s)) =
      ⨆ q ∈ {q : (Fin (N + 1) → Fin r → ℤ) × (Fin (N + 1) → Fin K → ℤ) | ∀ i, q.1 i ∈ pi' i ∧ q.2 i ∈ pi'' i},
          jointType F LL q.1 q.2 := by
    apply le_antisymm
    · refine iSup₂_le fun q hq => ?_
      refine le_iSup₂_of_le (f := fun (q : (Fin (N + 1) → Fin r → ℤ) × (Fin (N + 1) → Fin K → ℤ))
          (_ : q ∈ {q : (Fin (N + 1) → Fin r → ℤ) × (Fin (N + 1) → Fin K → ℤ) |
            ∀ i, q.1 i ∈ pi' i ∧ q.2 i ∈ pi'' i}) => jointType F LL q.1 q.2)
        (fun i => q (.inl i), fun i => q (.inr i)) (fun i => ⟨hq (.inl i), hq (.inr i)⟩) ?_
      exact le_iInf fun i => le_inf (iInf_le (fun s => (externalProductJointData (F := F) D H r K LL B).W s (q s)) (Sum.inl i))
        (iInf_le (fun s => (externalProductJointData (F := F) D H r K LL B).W s (q s)) (Sum.inr i))
    · refine iSup₂_le fun q hq => ?_
      refine le_iSup₂_of_le (f := fun (q : ∀ s, GLWeightLabels N r K s) (_ : q ∈ {q : ∀ s, GLWeightLabels N r K s | ∀ s, q s ∈ pi s}) =>
          ⨅ s, (externalProductJointData (F := F) D H r K LL B).W s (q s))
        (fun s => match s with
          | .inl i => q.1 i
          | .inr i => q.2 i)
        (fun s => match s with
          | .inl i => (hq i).1
          | .inr i => (hq i).2) ?_
      exact le_iInf fun s => match s with
        | .inl i => (iInf_le _ i).trans inf_le_left
        | .inr i => (iInf_le _ i).trans inf_le_right
  have hset : {x | ∀ s, (externalProductJointData (F := F) D H r K LL B).P x s ∈ pi s} =
      {x : PIdx r K LL B | ∀ i, x.1.1.1 i ∈ pi' i ∧ x.1.2.1 i ∈ pi'' i} := by
    ext x
    constructor
    · intro h i
      exact ⟨h (.inl i), h (.inr i)⟩
    · intro h s
      match s with
      | .inl i => exact (h i).1
      | .inr i => exact (h i).2
  rw [(H.p16 F N r K LL B).2, ← hsup, ← hset]
  exact key

theorem map_externalProduct_vector {O Kf : Type} [CommRing O] [CommRing Kf] (φ : O →+* Kf) {N : ℕ} (r K : ℕ) (LL : Letters (Fin N))
    (B : Fin N → ℕ) (x : PIdx r K LL B) : MvPolynomial.map φ (pvec O r K LL B x) = pvec Kf r K LL B x := by
  unfold pvec PsiPl PsiTan
  rw [map_mul, MvPolynomial.map_rename, MvPolynomial.map_rename, map_Psi', map_Psi']

theorem admissible_externalProduct_of_hyps (D : Formalism.BasicNotions.D7) (H : ExternalProductHyps) : PairedPathIndependence D := by
  intro O _ _ _ _ N r K _ _ LL B
  have hP := H.p16 O N r K LL B
  refine ⟨⟨hP.1, ?_⟩, ?_⟩
  · rw [← hP.2]
    congr 1
    ext G
    constructor
    · rintro ⟨nu, ka, I', I'', h1, h2, h3, rfl⟩
      exact ⟨⟨((nu, I'), (ka, I'')), h1, h2, h3⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x.1.1.1, x.1.2.1, x.1.1.2, x.1.2.2, x.2.1, x.2.2.1, x.2.2.2, rfl⟩
  · intro pi' pi'' h' h''
    have hint := span_inter_eq_span_image (IsFractionRing.injective O (KK O)) (pvec O r K LL B) (pvec (KK O) r K LL B)
      (map_externalProduct_vector (algebraMap O (KK O)) r K LL B) (H.p16 (KK O) N r K LL B).1 _ _
      (span_inf_iSup_externalProduct D H (KK O) r K LL B pi' pi'' h' h'')
    rw [hP.2] at hint
    rw [hint]
    congr 2
    ext G
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.1.1.1, x.1.2.1, x.1.1.2, x.1.2.2, x.2.1, hx, x.2.2.1, x.2.2.2, rfl⟩
    · rintro ⟨nu, ka, I', I'', h1, hx, h2, h3, rfl⟩
      exact ⟨⟨((nu, I'), (ka, I'')), h1, h2, h3⟩, hx, rfl⟩

end Formalism.MainNotions.G.ColumnFamilies
