module

public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrameLats
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClassNumberLeAbsDiscrOfFinrankEqTwo

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SameBlockAppend
open ValuativeRel MeasureTheory ComplexConjugate Formalism.MainNotions.S.Loc
open scoped ComplexOrder

namespace GlobalTheory.SgLoc.PtAlg

variable {E : Type} [CommRing E]

theorem ptEntryL_append (bs : List (Eˣ × ℕ+)) (t : Eˣ) (s : ℕ+) :
    ∀ (m : ℕ), (bs.map (fun b => (b.2 : ℕ))).sum = m → ∀ a b : ℕ,
      ptEntryL (bs ++ [(t, s)]) a b =
        if a < m ∧ b < m then ptEntryL bs a b
        else if m ≤ a ∧ m ≤ b ∧ a + b + 1 = 2 * m + s then (t : E) else 0 := by
  induction bs with
  | nil =>
    intro m hm a b
    simp only [List.map_nil, List.sum_nil] at hm
    subst hm
    simp only [List.nil_append, ptEntryL]
    split_ifs <;> first | rfl | omega
  | cons hd bs ih =>
    obtain ⟨t', s'⟩ := hd
    intro m hm a b
    simp only [List.map_cons, List.sum_cons] at hm
    simp only [List.cons_append, ptEntryL]
    rw [ih _ rfl]
    split_ifs <;> first | rfl | omega

theorem mat_snoc {m : ℕ} (h : Pt E m) (t : Eˣ) (s : ℕ+) (a b : Fin (m + s)) :
    (h.snoc t s).mat a b =
      if hab : (a : ℕ) < m ∧ (b : ℕ) < m then h.mat ⟨a, hab.1⟩ ⟨b, hab.2⟩
      else if m ≤ (a : ℕ) ∧ m ≤ (b : ℕ) ∧ (a : ℕ) + b + 1 = 2 * m + s then (t : E) else 0 := by
  show ptEntryL (h.blocks ++ [(t, s)]) a b = _
  rw [ptEntryL_append h.blocks t s m h.size]
  split_ifs <;> rfl

theorem det_snoc_eq {m : ℕ} (h : Pt E m) (t : Eˣ) (s : ℕ+) :
    (h.snoc t s).mat.det =
      h.mat.det * (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s)) : ℤˣ) : ℤ) *
        (t : E) ^ (s : ℕ)) := by
  have key : Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm (h.snoc t s).mat =
      Matrix.fromBlocks h.mat 0 0
        ((t : E) • (Fin.revPerm : Equiv.Perm (Fin s)).permMatrix E) := by
    ext (i | i) (j | j) <;>
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, mat_snoc,
        finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.val_castAdd, Fin.val_natAdd,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂, Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul] <;>
      have hi := i.isLt <;> have hj := j.isLt
    · rw [dite_eq_left ⟨hi, hj⟩]
    · rw [dite_eq_right (by omega), ite_eq_right (by omega)]
    · rw [dite_eq_right (by omega), ite_eq_right (by omega)]
    · rw [dite_eq_right (by omega)]
      simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
        Option.mem_def, Option.some.injEq, Fin.revPerm_apply]
      by_cases hij : Fin.rev i = j
      · rw [ite_eq_left (by rw [← hij, Fin.val_rev]; omega), ite_eq_left hij, mul_one]
      · rw [ite_eq_right (fun hc => hij (Fin.ext (by rw [Fin.val_rev]; omega))),
          ite_eq_right hij, mul_zero]
  have hdet := congrArg Matrix.det key
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_smul,
    Matrix.det_permutation, Fintype.card_fin] at hdet
  rw [hdet]
  ring

theorem det_snoc {m : ℕ} (h : Pt E m) (t : Eˣ) (s : ℕ+) :
    (h.snoc t s).mat.det = h.mat.det * (t : E) ^ (s : ℕ) ∨
      (h.snoc t s).mat.det = -(h.mat.det * (t : E) ^ (s : ℕ)) := by
  rw [det_snoc_eq]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s))) with h1 | h1
  · left
    rw [h1]
    simp
  · right
    rw [h1]
    simp

private theorem isUnit_det_of_mem_UH_Hpk (bs : List (Eˣ × ℕ+)) :
    ∀ (n : ℕ) (hn : (bs.map (fun b => (b.2 : ℕ))).sum = n),
      IsUnit (Pt.mat (⟨bs, hn⟩ : Pt E n)).det := by
  induction bs using List.reverseRecOn with
  | nil =>
    intro n hn
    have hn' : n = 0 := by rw [← hn]; simp
    subst hn'
    simp
  | append_singleton bs x ih =>
    obtain ⟨t, s⟩ := x
    intro n hn
    have hn' : n = (bs.map (fun b => (b.2 : ℕ))).sum + s := by rw [← hn]; simp
    subst hn'
    have hu := ih _ rfl
    change IsUnit (Pt.snoc (⟨bs, rfl⟩ : Pt E _) t s).mat.det
    rcases det_snoc (⟨bs, rfl⟩ : Pt E _) t s with h1 | h1
    · rw [h1]
      exact hu.mul ((Units.isUnit t).pow _)
    · rw [h1]
      exact (hu.mul ((Units.isUnit t).pow _)).neg

theorem isUnit_det {m : ℕ} (h : Pt E m) : IsUnit h.mat.det := by
  exact isUnit_det_of_mem_UH_Hpk h.blocks m h.size

end GlobalTheory.SgLoc.PtAlg

namespace GlobalTheory.SgLoc

end GlobalTheory.SgLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndexMeasureIntegralEqOfFineSubgroup
open GlobalTheory.IdxInt
open scoped Pointwise Classical

namespace GlobalTheory.IdxInt

open Function in
private lemma quotientEquivProdOfLE_apply_fst {W : Type} [AddCommGroup W] {C B : AddSubgroup W} (h : C ≤ B)
    (c : W ⧸ C) : ((AddSubgroup.quotientEquivProdOfLE h) c).1 = ((Quotient.out c : W) : W ⧸ B) := by
  conv_lhs => rw [← QuotientAddGroup.out_eq' c]
  rfl

open Function in
private lemma finsum_prod_fst_eq_card_mul {X Y : Type} [Finite Y] (g : X → ℂ) (hg : (support g).Finite) :
    ∑ᶠ p : X × Y, g p.1 = (Nat.card Y : ℂ) * ∑ᶠ x, g x := by
  have := Fintype.ofFinite Y
  rw [finsum_eq_sum_of_support_subset (s := hg.toFinset ×ˢ Finset.univ),
    finsum_eq_sum_of_support_subset (s := hg.toFinset), Finset.sum_product, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun x _ => ?_
    show ∑ _y : Y, g x = _
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  · intro x hx
    simpa using hx
  · intro p hp
    simpa using hp

open Function in
private lemma support_quotient_out_finite_of_image_finite {W : Type} [AddCommGroup W] {B : AddSubgroup W} (φ : W → ℂ)
    (hφ : ((fun w : W => (w : W ⧸ B)) '' support φ).Finite) :
    (support fun c : W ⧸ B => φ (Quotient.out c)).Finite := by
  refine hφ.subset fun c hc => ⟨Quotient.out c, hc, QuotientAddGroup.out_eq' c⟩

open Function in
private lemma finsum_quotient_out_eq_relIndex_mul_of_le {W : Type} [AddCommGroup W] {C B : AddSubgroup W} (hCB : C ≤ B)
    (hidx : C.relIndex B ≠ 0) (φ : W → ℂ) (hinv : ∀ w b : W, b ∈ B → φ (w + b) = φ w)
    (hφ : ((fun w : W => (w : W ⧸ B)) '' support φ).Finite) :
    ∑ᶠ c : W ⧸ C, φ (Quotient.out c) = (C.relIndex B : ℂ) * ∑ᶠ c : W ⧸ B, φ (Quotient.out c) := by
  have hfin : Finite (B ⧸ C.addSubgroupOf B) := Nat.finite_of_card_ne_zero hidx
  have hcls : ∀ c : W ⧸ C, φ (Quotient.out c) =
      φ (Quotient.out ((AddSubgroup.quotientEquivProdOfLE hCB) c).1) := by
    intro c
    rw [quotientEquivProdOfLE_apply_fst]
    obtain ⟨b, hb⟩ : ∃ b ∈ B, Quotient.out ((Quotient.out c : W) : W ⧸ B) = Quotient.out c + b := by
      refine ⟨-(Quotient.out c) + Quotient.out ((Quotient.out c : W) : W ⧸ B), ?_, by abel⟩
      exact QuotientAddGroup.leftRel_apply.mp (Quotient.exact' (QuotientAddGroup.out_eq' _).symm)
    rw [hb.2, hinv _ _ hb.1]
  rw [finsum_congr hcls, finsum_comp_equiv (AddSubgroup.quotientEquivProdOfLE hCB)
      (f := fun p => φ (Quotient.out p.1)), finsum_prod_fst_eq_card_mul _ (support_quotient_out_finite_of_image_finite φ hφ)]
  rfl

open Function in
private lemma finsum_out_div_relIndex_eq_of_le {W : Type} [AddCommGroup W] {A B C : AddSubgroup W}
    {φ : W → ℂ} (hB : _root_.GlobalTheory.IdxInt.Fine A φ B) (hCB : C ≤ B) (hC : C.relIndex A ≠ 0) :
    (∑ᶠ c : W ⧸ C, φ (Quotient.out c)) / (C.relIndex A : ℂ) =
      (∑ᶠ c : W ⧸ B, φ (Quotient.out c)) / (B.relIndex A : ℂ) := by
  obtain ⟨hBA, -, hinv, hsupp⟩ := hB
  have hidx : C.relIndex B ≠ 0 := by
    rw [← AddSubgroup.relIndex_mul_relIndex C B A hCB hBA] at hC
    exact left_ne_zero_of_mul hC
  rw [finsum_quotient_out_eq_relIndex_mul_of_le hCB hidx φ hinv hsupp, ← AddSubgroup.relIndex_mul_relIndex C B A hCB hBA,
    Nat.cast_mul, mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr hidx)]

open Function in
theorem _root_.GlobalTheory.IdxInt.cint_eq_of_fine : ∀ {W : Type} [AddCommGroup W] (A B : AddSubgroup W) (φ : W → ℂ),
    _root_.GlobalTheory.IdxInt.Fine A φ B → _root_.GlobalTheory.IdxInt.cint A φ = (∑ᶠ c : W ⧸ B, φ c.out) / (B.relIndex A : ℂ) := by
  intro W _ A B φ hB
  have h : _root_.GlobalTheory.IdxInt.Nice A φ := ⟨B, hB⟩
  unfold _root_.GlobalTheory.IdxInt.cint
  rw [dite_eq_left h]
  have hB0 := h.choose_spec
  have hidx : (B ⊓ h.choose).relIndex A ≠ 0 := AddSubgroup.relIndex_inf_ne_zero hB.2.1 hB0.2.1
  rw [← finsum_out_div_relIndex_eq_of_le hB0 inf_le_right hidx, finsum_out_div_relIndex_eq_of_le hB inf_le_left hidx]

end GlobalTheory.IdxInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilIntegrationFormulaOrbit
open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.WeilOrbit

theorem measurableEmbedding_of_sigmaCompact {Y X : Type} [TopologicalSpace Y] [T2Space Y]
    [SigmaCompactSpace Y] [MeasurableSpace Y] [BorelSpace Y] [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] {φ : Y → X} (hc : Continuous φ)
    (hi : Function.Injective φ) : MeasurableEmbedding φ := by
  refine ⟨hi, hc.measurable, fun s hs => ?_⟩
  have h : φ '' s = ⋃ n, (fun y : compactCovering Y n => φ y) '' (Subtype.val ⁻¹' s) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨n, hn⟩ := exists_mem_compactCovering y
      exact ⟨n, ⟨y, hn⟩, hy, rfl⟩
    · rintro ⟨n, y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
  rw [h]
  refine MeasurableSet.iUnion fun n => ?_
  haveI : CompactSpace (compactCovering Y n) :=
    isCompact_iff_compactSpace.mp (isCompact_compactCovering Y n)
  have hce : Topology.IsClosedEmbedding (fun y : compactCovering Y n => φ y) :=
    (hc.comp continuous_subtype_val).isClosedEmbedding (hi.comp Subtype.val_injective)
  exact hce.measurableEmbedding.measurableSet_image.mpr (measurable_subtype_coe hs)

theorem exists_compact_cover {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] (H : Subgroup G) {C : Set (G ⧸ H)} (hC : IsCompact C) :
    ∃ K : Set G, IsCompact K ∧ C ⊆ (QuotientGroup.mk : G → G ⧸ H) '' K := by
  refine hC.induction_on (p := fun C => ∃ K : Set G, IsCompact K ∧
    C ⊆ (QuotientGroup.mk : G → G ⧸ H) '' K) ⟨∅, isCompact_empty, by simp⟩ ?_ ?_ ?_
  · rintro s t hst ⟨K, hK, h⟩
    exact ⟨K, hK, hst.trans h⟩
  · rintro s t ⟨K, hK, h⟩ ⟨L, hL, h'⟩
    exact ⟨K ∪ L, hK.union hL, by rw [Set.image_union]; exact Set.union_subset_union h h'⟩
  · intro q _
    induction q using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨K, hK, hg⟩ := exists_compact_mem_nhds g
      exact ⟨_, mem_nhdsWithin_of_mem_nhds (QuotientGroup.isOpenMap_coe.image_mem_nhds hg),
        K, hK, subset_rfl⟩

def orbitMap (G : Type) {X : Type} [Group G] [MulAction G X] (x0 : X) :
    G ⧸ MulAction.stabilizer G x0 → X :=
  MulAction.ofQuotientStabilizer G x0

theorem orbitMap_mk {G X : Type} [Group G] [MulAction G X] (x0 : X) (g : G) :
    orbitMap G x0 (g : G ⧸ MulAction.stabilizer G x0) = g • x0 := rfl

theorem orbitMap_injective {G X : Type} [Group G] [MulAction G X] (x0 : X) :
    Function.Injective (orbitMap G x0) :=
  MulAction.injective_ofQuotientStabilizer G x0

theorem weil_formula : ∀ (G X : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [MulAction G X] [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (x0 : X), Continuous (fun p : G × X => p.1 • p.2) → ∀ (μ : Measure G), μ.IsHaarMeasure → ∀ (ν : Measure X), ν {y | ¬ ∃ g : G, g • x0 = y} = 0 → (∀ (g : G) (s : Set X), MeasurableSet s → ν ((fun y => g • y) ⁻¹' s) = ν s) → (∀ K : Set G, IsCompact K → ν ((fun g => g • x0) '' K) < ⊤) → ν ≠ 0 → ∃ μ' : Measure (MulAction.stabilizer G x0), μ'.IsHaarMeasure ∧ ∀ f : G → ℝ≥0∞, Measurable f → ∀ s : X → G, (∀ y, (∃ g : G, g • x0 = y) → s y • x0 = y) → ∫⁻ g, f g ∂μ = ∫⁻ y, ∫⁻ h', f (s y * (h' : G)) ∂μ' ∂ν := by
  intro G X _ _ _ _ _ _ _ _ _ _ _ _ _ _ x0 hcont μ hμ ν hν0 hinv hfin hne
  set H := MulAction.stabilizer G x0 with hHdef
  have hc0 : Continuous (fun g : G => g • x0) :=
    hcont.comp (continuous_id.prodMk continuous_const)
  have hH : IsClosed (H : Set G) := isClosed_eq hc0 continuous_const
  haveI := hH
  letI : MeasurableSpace (G ⧸ H) := borel _
  haveI : BorelSpace (G ⧸ H) := ⟨rfl⟩
  haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SigmaCompactSpace (G ⧸ H) := inferInstance
  let φ : G ⧸ H → X := orbitMap G x0
  have hφc : Continuous φ := (QuotientGroup.isQuotientMap_mk H).continuous_iff.mpr hc0
  have hφ : MeasurableEmbedding φ :=
    measurableEmbedding_of_sigmaCompact hφc (orbitMap_injective x0)
  have hrange : Set.range φ = {y | ∃ g : G, g • x0 = y} := by
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      induction q using QuotientGroup.induction_on with
      | H g => exact ⟨g, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨(g : G ⧸ H), rfl⟩
  have hae : ∀ᵐ y ∂ν, y ∈ Set.range φ := by
    rw [hrange]
    exact hν0
  have hmap : (ν.comap φ).map φ = ν := by
    rw [hφ.map_comap, Measure.restrict_eq_self_of_ae_mem hae]
  have hrad : GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.IsInvariantRadon H (ν.comap φ) := by
    refine ⟨fun h0 => hne ?_, ⟨fun C hC => ?_⟩, ⟨fun g s hs => ?_⟩⟩
    · rw [← hmap, h0, Measure.map_zero]
    · obtain ⟨K, hK, hCK⟩ := exists_compact_cover H hC
      rw [hφ.comap_apply]
      refine (measure_mono ?_).trans_lt (hfin K hK)
      rintro _ ⟨q, hq, rfl⟩
      obtain ⟨g, hg, rfl⟩ := hCK hq
      exact ⟨g, hg, rfl⟩
    · rw [hφ.comap_apply, hφ.comap_apply, ← hinv g (φ '' s) (hφ.measurableSet_image.mpr hs)]
      congr 1
      have heq : ∀ (a : G) (q : G ⧸ H), φ (a • q) = a • φ q := by
        intro a q
        induction q using QuotientGroup.induction_on with
        | H b => exact mul_smul a b x0
      ext y
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact ⟨g • q, hq, heq g q⟩
      · rintro ⟨q, hq, h⟩
        refine ⟨g⁻¹ • q, by simpa using hq, ?_⟩
        rw [heq, h, inv_smul_smul]
  let ν0 : Measure H := Measure.haar
  obtain ⟨dg, ⟨hdg, hq⟩, -⟩ :=
    GlobalTheory.QuotientHaar.existsUnique_haar_of_invariantRadon G H hH ν0 _ hrad
  let c := Measure.haarScalarFactor μ dg
  have hc : μ = c • dg := Measure.isMulLeftInvariant_eq_smul μ dg
  have hcpos : c ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure μ dg).ne'
  refine ⟨c • ν0, Measure.IsHaarMeasure.nnreal_smul ν0 hcpos, fun f hf s hs => ?_⟩
  have h1 : ∫⁻ y, ∫⁻ h' : H, f (s y * (h' : G)) ∂ν0 ∂ν = ∫⁻ g, f g ∂dg := by
    rw [(hq f hf).2]
    conv_lhs => rw [← hmap]
    rw [hφ.lintegral_map]
    refine lintegral_congr fun q => ?_
    rw [← GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.fibreIntegral_mk H ν0 f]
    congr 1
    apply orbitMap_injective x0
    rw [orbitMap_mk]
    exact hs _ (by
      have : φ q ∈ Set.range φ := ⟨q, rfl⟩
      rwa [hrange] at this)
  rw [hc]
  simp only [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
  rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, h1]

end GlobalTheory.WeilOrbit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndexMeasureIntegralTransportAndChange
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndexMeasureIntegralTransportAndChange
noncomputable section
open GlobalTheory.IdxInt
open scoped Pointwise Classical

namespace GlobalTheory.IdxInt.Transport

variable {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W']

private lemma apply_out_mk_eq_of_invariant {B : AddSubgroup W} {φ : W → ℂ}
    (hφ : ∀ w b, b ∈ B → φ (w + b) = φ w) (y : W) :
    φ (Quotient.out (QuotientAddGroup.mk y : W ⧸ B)) = φ y := by
  have h : (QuotientAddGroup.mk (Quotient.out (QuotientAddGroup.mk y : W ⧸ B)) : W ⧸ B) =
      QuotientAddGroup.mk y := Quotient.out_eq _
  rw [QuotientAddGroup.eq] at h
  have := hφ (Quotient.out (QuotientAddGroup.mk y : W ⧸ B)) _ h
  rw [add_neg_cancel_left] at this
  exact this.symm

private lemma Fine_map_addEquiv_and_finsum_eq (e : W ≃+ W') {A B : AddSubgroup W}
    {φ : W' → ℂ} (hB : _root_.GlobalTheory.IdxInt.Fine A (fun w => φ (e w)) B) :
    _root_.GlobalTheory.IdxInt.Fine (A.map e.toAddMonoidHom) φ (B.map e.toAddMonoidHom) ∧
      (∑ᶠ c : W' ⧸ B.map e.toAddMonoidHom, φ (Quotient.out c)) =
        ∑ᶠ c : W ⧸ B, φ (e (Quotient.out c)) := by
  obtain ⟨hBA, hBi, hφ, hsupp⟩ := hB
  have hφ' : ∀ w b, b ∈ B.map e.toAddMonoidHom → φ (w + b) = φ w := by
    rintro w _ ⟨b, hb, rfl⟩
    have := hφ (e.symm w) b hb
    simpa using this
  let q : W ⧸ B ≃+ W' ⧸ B.map e.toAddMonoidHom := QuotientAddGroup.congr _ _ e rfl
  have hq : ∀ y : W, q (QuotientAddGroup.mk y) = QuotientAddGroup.mk (e y) := fun _ => rfl
  refine ⟨⟨AddSubgroup.map_mono hBA, ?_, hφ', ?_⟩, ?_⟩
  · rw [AddSubgroup.relIndex_map_map_of_injective _ _ e.injective]
    exact hBi
  · refine (hsupp.image q).subset ?_
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨QuotientAddGroup.mk (e.symm y), ⟨e.symm y, by simpa using hy, rfl⟩, ?_⟩
    rw [hq, AddEquiv.apply_symm_apply]
  · rw [← finsum_comp_equiv q.toEquiv]
    refine finsum_congr fun c => ?_
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective c
    change φ (Quotient.out (q (QuotientAddGroup.mk y))) = _
    rw [hq, apply_out_mk_eq_of_invariant hφ', apply_out_mk_eq_of_invariant (φ := fun w => φ (e w)) hφ]

private lemma map_symm_map_addEquiv (e : W ≃+ W') (A : AddSubgroup W) :
    (A.map e.toAddMonoidHom).map e.symm.toAddMonoidHom = A := by
  ext x
  simp

private lemma Fine_of_le_and_finsum_eq_relIndex_mul {A B C : AddSubgroup W} {φ : W → ℂ}
    (hB : _root_.GlobalTheory.IdxInt.Fine A φ B) (hCB : C ≤ B) (hC : C.relIndex B ≠ 0) :
    _root_.GlobalTheory.IdxInt.Fine A φ C ∧
      (∑ᶠ c : W ⧸ C, φ (Quotient.out c)) =
        (C.relIndex B : ℂ) * ∑ᶠ c : W ⧸ B, φ (Quotient.out c) := by
  obtain ⟨hBA, hBi, hφ, hsupp⟩ := hB
  haveI : Finite (B ⧸ C.addSubgroupOf B) := Nat.finite_of_card_ne_zero hC
  let e := AddSubgroup.quotientEquivProdOfLE hCB
  have he : ∀ y : W, (e (QuotientAddGroup.mk y)).1 = QuotientAddGroup.mk y := fun _ => rfl
  have hφC : ∀ w b, b ∈ C → φ (w + b) = φ w := fun w b hb => hφ w b (hCB hb)
  have hcomp : ∀ x : W ⧸ C, φ (Quotient.out x) = φ (Quotient.out (e x).1) := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
    rw [he, apply_out_mk_eq_of_invariant hφC, apply_out_mk_eq_of_invariant hφ]
  set T : Set (W ⧸ B) := (fun w : W => (w : W ⧸ B)) '' Function.support φ with hT
  have hgT : Function.support (fun c : W ⧸ B => φ (Quotient.out c)) ⊆ T := by
    intro c hc
    refine ⟨Quotient.out c, hc, ?_⟩
    exact Quotient.out_eq c
  refine ⟨⟨hCB.trans hBA, ?_, hφC, ?_⟩, ?_⟩
  · rw [← AddSubgroup.relIndex_mul_relIndex C B A hCB hBA]
    exact mul_ne_zero hC hBi
  · refine ((hsupp.prod (Set.finite_univ (α := B ⧸ C.addSubgroupOf B))).preimage
      e.injective.injOn).subset ?_
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨?_, Set.mem_univ _⟩
    rw [he]
    exact ⟨y, hy, rfl⟩
  · rw [finsum_congr hcomp,
      finsum_comp_equiv e (f := fun p : (W ⧸ B) × (B ⧸ C.addSubgroupOf B) => φ (Quotient.out p.1))]
    rw [finsum_curry _ ?_]
    · haveI := Fintype.ofFinite (B ⧸ C.addSubgroupOf B)
      simp only [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [mul_finsum]
      congr 1
      funext a
      rw [AddSubgroup.relIndex, AddSubgroup.index, Nat.card_eq_fintype_card]
    · exact (hsupp.prod (Set.finite_univ (α := B ⧸ C.addSubgroupOf B))).subset
        fun p hp => ⟨hgT hp, Set.mem_univ _⟩

private lemma finsum_out_div_relIndex_eq_inf_of_fine {A B₁ B₂ : AddSubgroup W} {φ : W → ℂ}
    (h₁ : _root_.GlobalTheory.IdxInt.Fine A φ B₁) (h₂ : _root_.GlobalTheory.IdxInt.Fine A φ B₂) :
    (∑ᶠ c : W ⧸ B₁, φ (Quotient.out c)) / (B₁.relIndex A : ℂ) =
      (∑ᶠ c : W ⧸ (B₁ ⊓ B₂), φ (Quotient.out c)) / ((B₁ ⊓ B₂).relIndex A : ℂ) := by
  have hle : B₁ ⊓ B₂ ≤ B₁ := inf_le_left
  have hprod := AddSubgroup.relIndex_mul_relIndex (B₁ ⊓ B₂) B₁ A hle h₁.1
  have hA : (B₁ ⊓ B₂).relIndex A ≠ 0 := AddSubgroup.relIndex_inf_ne_zero h₁.2.1 h₂.2.1
  have hi : (B₁ ⊓ B₂).relIndex B₁ ≠ 0 := by
    rw [← hprod] at hA
    exact left_ne_zero_of_mul hA
  rw [(Fine_of_le_and_finsum_eq_relIndex_mul h₁ hle hi).2, ← hprod, Nat.cast_mul,
    mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr hi)]

private lemma cint_eq_finsum_div_relIndex_of_fine {A B : AddSubgroup W} {φ : W → ℂ}
    (hB : _root_.GlobalTheory.IdxInt.Fine A φ B) :
    _root_.GlobalTheory.IdxInt.cint A φ = (∑ᶠ c : W ⧸ B, φ (Quotient.out c)) / (B.relIndex A : ℂ) := by
  have hnice : _root_.GlobalTheory.IdxInt.Nice A φ := ⟨B, hB⟩
  unfold _root_.GlobalTheory.IdxInt.cint
  rw [dite_eq_left hnice, finsum_out_div_relIndex_eq_inf_of_fine hnice.choose_spec hB,
    finsum_out_div_relIndex_eq_inf_of_fine hB hnice.choose_spec, inf_comm]

private lemma Fine_inf_of_relIndex_ne_zero {A A' B : AddSubgroup W} {φ : W → ℂ}
    (hB : _root_.GlobalTheory.IdxInt.Fine A φ B) (h₂ : A'.relIndex A ≠ 0) (h₁ : A.relIndex A' ≠ 0) :
    _root_.GlobalTheory.IdxInt.Fine A φ (B ⊓ A') ∧ _root_.GlobalTheory.IdxInt.Fine A' φ (B ⊓ A') := by
  have hBA : B ≤ A := hB.1
  have hCA : (B ⊓ A').relIndex A ≠ 0 := AddSubgroup.relIndex_inf_ne_zero hB.2.1 h₂
  have hi : (B ⊓ A').relIndex B ≠ 0 := by
    have h := hCA
    rw [← AddSubgroup.relIndex_mul_relIndex (B ⊓ A') B A inf_le_left hBA] at h
    exact left_ne_zero_of_mul h
  have hfine := (Fine_of_le_and_finsum_eq_relIndex_mul hB inf_le_left hi).1
  refine ⟨hfine, inf_le_right, ?_, hfine.2.2⟩
  have hCD : B ⊓ A' ≤ A ⊓ A' := inf_le_inf_right A' hBA
  have hD : (B ⊓ A').relIndex (A ⊓ A') ≠ 0 := by
    have h := hCA
    rw [← AddSubgroup.relIndex_mul_relIndex (B ⊓ A') (A ⊓ A') A hCD inf_le_left] at h
    exact left_ne_zero_of_mul h
  rw [← AddSubgroup.relIndex_mul_relIndex (B ⊓ A') (A ⊓ A') A' hCD inf_le_right,
    AddSubgroup.inf_relIndex_right]
  exact mul_ne_zero hD h₁

theorem _root_.GlobalTheory.IdxInt.Transport.cint_map_and_change : ∀ {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W'], (∀ (e : W ≃+ W') (A : AddSubgroup W) (φ : W' → ℂ), (_root_.GlobalTheory.IdxInt.Nice (A.map e.toAddMonoidHom) φ ↔ _root_.GlobalTheory.IdxInt.Nice A (fun w => φ (e w))) ∧ _root_.GlobalTheory.IdxInt.cint (A.map e.toAddMonoidHom) φ = _root_.GlobalTheory.IdxInt.cint A (fun w => φ (e w))) ∧ ∀ (A A' : AddSubgroup W) (φ : W → ℂ), A.relIndex A' ≠ 0 → A'.relIndex A ≠ 0 → (_root_.GlobalTheory.IdxInt.Nice A φ ↔ _root_.GlobalTheory.IdxInt.Nice A' φ) ∧ _root_.GlobalTheory.IdxInt.cint A' φ * (A.relIndex A' : ℂ) = _root_.GlobalTheory.IdxInt.cint A φ * (A'.relIndex A : ℂ) := by
  intro W _ W' _
  refine ⟨fun e A φ => ?_, fun A A' φ h₁ h₂ => ?_⟩
  · have hiff : _root_.GlobalTheory.IdxInt.Nice (A.map e.toAddMonoidHom) φ ↔
        _root_.GlobalTheory.IdxInt.Nice A (fun w => φ (e w)) := by
      constructor
      · rintro ⟨B', hB'⟩
        have hB'' : _root_.GlobalTheory.IdxInt.Fine (A.map e.toAddMonoidHom)
            (fun w => (fun w => φ (e w)) (e.symm w)) B' := by simpa using hB'
        have h := (Fine_map_addEquiv_and_finsum_eq e.symm (φ := fun w => φ (e w)) hB'').1
        rw [map_symm_map_addEquiv] at h
        exact ⟨_, h⟩
      · rintro ⟨B, hB⟩
        exact ⟨_, (Fine_map_addEquiv_and_finsum_eq e hB).1⟩
    refine ⟨hiff, ?_⟩
    by_cases hN : _root_.GlobalTheory.IdxInt.Nice A (fun w => φ (e w))
    · obtain ⟨B, hB⟩ := hN
      rw [cint_eq_finsum_div_relIndex_of_fine hB, cint_eq_finsum_div_relIndex_of_fine (Fine_map_addEquiv_and_finsum_eq e hB).1,
        (Fine_map_addEquiv_and_finsum_eq e hB).2, AddSubgroup.relIndex_map_map_of_injective _ _ e.injective]
    · unfold _root_.GlobalTheory.IdxInt.cint
      rw [dite_eq_right hN, dite_eq_right (hiff.not.mpr hN)]
  · have hiff : _root_.GlobalTheory.IdxInt.Nice A φ ↔ _root_.GlobalTheory.IdxInt.Nice A' φ := by
      constructor
      · rintro ⟨B, hB⟩
        exact ⟨_, (Fine_inf_of_relIndex_ne_zero hB h₂ h₁).2⟩
      · rintro ⟨B, hB⟩
        exact ⟨_, (Fine_inf_of_relIndex_ne_zero hB h₁ h₂).2⟩
    refine ⟨hiff, ?_⟩
    by_cases hN : _root_.GlobalTheory.IdxInt.Nice A φ
    · obtain ⟨B, hB⟩ := hN
      have hC := Fine_inf_of_relIndex_ne_zero hB h₂ h₁
      have hCD : B ⊓ A' ≤ A ⊓ A' := inf_le_inf_right A' hB.1
      have hD : (B ⊓ A').relIndex (A ⊓ A') ≠ 0 := by
        have h := hC.1.2.1
        rw [← AddSubgroup.relIndex_mul_relIndex (B ⊓ A') (A ⊓ A') A hCD inf_le_left] at h
        exact left_ne_zero_of_mul h
      rw [cint_eq_finsum_div_relIndex_of_fine hC.1, cint_eq_finsum_div_relIndex_of_fine hC.2,
        ← AddSubgroup.relIndex_mul_relIndex (B ⊓ A') (A ⊓ A') A' hCD inf_le_right,
        ← AddSubgroup.relIndex_mul_relIndex (B ⊓ A') (A ⊓ A') A hCD inf_le_left,
        AddSubgroup.inf_relIndex_right, AddSubgroup.inf_relIndex_left]
      have hD' : ((B ⊓ A').relIndex (A ⊓ A') : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hD
      have h₁' : (A.relIndex A' : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr h₁
      have h₂' : (A'.relIndex A : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr h₂
      push_cast
      field_simp
    · unfold _root_.GlobalTheory.IdxInt.cint
      rw [dite_eq_right hN, dite_eq_right (hiff.not.mp hN)]
      simp

end GlobalTheory.IdxInt.Transport
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndexMeasureIntegralTransportAndChangeStatement
open GlobalTheory.IdxInt
open scoped Pointwise Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indexMeasureIntegral_transport_and_change : ∀ {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W'], (∀ (e : W ≃+ W') (A : AddSubgroup W) (φ : W' → ℂ), (Nice (A.map e.toAddMonoidHom) φ ↔ Nice A (fun w => φ (e w))) ∧ cint (A.map e.toAddMonoidHom) φ = cint A (fun w => φ (e w))) ∧ ∀ (A A' : AddSubgroup W) (φ : W → ℂ), A.relIndex A' ≠ 0 → A'.relIndex A ≠ 0 → (Nice A φ ↔ Nice A' φ) ∧ cint A' φ * (A.relIndex A' : ℂ) = cint A φ * (A'.relIndex A : ℂ) := by
  first | exact @GlobalTheory.IdxInt.Transport.cint_map_and_change | exact GlobalTheory.IdxInt.Transport.cint_map_and_change | (intros; apply GlobalTheory.IdxInt.Transport.cint_map_and_change <;> assumption)
end
end
