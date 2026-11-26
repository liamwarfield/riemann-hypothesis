module

public import GroundTheory.LocalFields.LocalFourier
public import GroundTheory.LocalFields.ExtensionsOfDegree
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MExistsNatSmulMem
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.FirstLemmaN

@[expose] public section

section -- merged from GroundTheory.LocalFields.LocalFourierExistence
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel Topology Filter
open scoped WithZero Pointwise

section RatCircle

def ratAddCircleToReal : AddCircle (1 : ℚ) →+ AddCircle (1 : ℝ) :=
  QuotientAddGroup.map _ _ (Rat.castHom ℝ : ℚ →+* ℝ).toAddMonoidHom
    (AddSubgroup.zmultiples_le_of_mem (by
      rw [AddSubgroup.mem_comap]
      simp))

theorem ratAddCircleToReal_coe (q : ℚ) :
    ratAddCircleToReal (q : AddCircle (1 : ℚ)) = ((q : ℝ) : AddCircle (1 : ℝ)) := rfl

theorem ratAddCircleToReal_injective : Function.Injective ratAddCircleToReal := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using QuotientAddGroup.induction_on with
  | H q =>
    rw [ratAddCircleToReal_coe, AddCircle.coe_eq_zero_iff] at hx
    obtain ⟨n, hn⟩ := hx
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_zmultiples_iff]
    refine ⟨n, ?_⟩
    have : ((n : ℚ) : ℝ) = (q : ℝ) := by simpa using hn
    simpa using (Rat.cast_injective this)

def ratCircleChar : AddChar (AddCircle (1 : ℚ)) Circle :=
  (AddCircle.toCircle_addChar (T := 1)).compAddMonoidHom ratAddCircleToReal

theorem ratCircleChar_injective : Function.Injective ratCircleChar :=
  (AddCircle.injective_toCircle one_ne_zero).comp ratAddCircleToReal_injective

theorem ratCircleChar_eq_one_iff {x : AddCircle (1 : ℚ)} : ratCircleChar x = 1 ↔ x = 0 := by
  constructor
  · intro h
    apply ratCircleChar_injective
    rw [h, AddChar.map_zero_eq_one]
  · rintro rfl
    exact AddChar.map_zero_eq_one _

end RatCircle

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Existence

theorem exists_mem_valBall_neg_one_notMem_valBall_zero :
    ∃ x : K, x ∈ valBall K (-1) ∧ x ∉ valBall K 0 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have h0 : (ϖ : K) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hi : (ϖ : K)⁻¹ ≠ 0 := inv_ne_zero h0
  refine ⟨(ϖ : K)⁻¹, ?_, ?_⟩
  · rw [mem_valBall_iff_le_ord hi, ord_inv h0, ord_uniformizer hϖ]
  · rw [mem_valBall_iff_le_ord hi, ord_inv h0, ord_uniformizer hϖ]
    omega

theorem continuous_of_isTrivialOn {χ : AddChar K Circle} {n : ℤ} (h : IsTrivialOn χ n) :
    Continuous χ := by
  have hlc : IsLocallyConstant χ := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨{z | z - x ∈ valBall K n},
      (isOpen_valBall n).preimage (continuous_id.sub continuous_const), by simp, fun z hz => ?_⟩
    have e : x + (z - x) = z := by abel
    rw [← e, AddChar.map_add_eq_mul, h _ hz, mul_one]
  exact hlc.continuous

theorem exists_addChar_isTrivialOn_zero_not_isTrivialOn_neg_one :
    ∃ ψ : AddChar K Circle, IsTrivialOn ψ 0 ∧ ¬ IsTrivialOn ψ (-1) := by
  obtain ⟨x, hx1, hx0⟩ := exists_mem_valBall_neg_one_notMem_valBall_zero (K := K)
  let π : K →+ K ⧸ valBall K 0 := QuotientAddGroup.mk' (valBall K 0)
  have hπx : π x ≠ 0 := by
    rwa [Ne, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hπx
  let ψ : AddChar K Circle :=
    ratCircleChar.compAddMonoidHom ((c : K ⧸ valBall K 0 →+ AddCircle (1 : ℚ)).comp π)
  have hψ : ∀ y, ψ y = ratCircleChar (c (π y)) := fun _ => rfl
  refine ⟨ψ, fun y hy => ?_, fun h => ?_⟩
  · have : π y = 0 := by
      rwa [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    rw [hψ, this, map_zero, AddChar.map_zero_eq_one]
  · exact hc (ratCircleChar_eq_one_iff.mp ((hψ x).symm.trans (h x hx1)))

theorem exists_addChar_addCharConductor_eq_zero :
    ∃ ψ : AddChar K Circle, Continuous ψ ∧ ψ ≠ 1 ∧ addCharConductor ψ = 0 := by
  obtain ⟨ψ, h0, h1⟩ := exists_addChar_isTrivialOn_zero_not_isTrivialOn_neg_one (K := K)
  have hc : Continuous ψ := continuous_of_isTrivialOn h0
  have hne : ψ ≠ 1 := by
    rintro rfl
    exact h1 fun _ _ => AddChar.one_apply _
  refine ⟨ψ, hc, hne, le_antisymm ((isTrivialOn_iff hc hne 0).mp h0) ?_⟩
  by_contra hlt
  exact h1 ((isTrivialOn_iff hc hne (-1)).mpr (by omega))

theorem exists_addChar_continuous_ne_one :
    ∃ ψ : AddChar K Circle, Continuous ψ ∧ ψ ≠ 1 := by
  obtain ⟨ψ, hc, hne, -⟩ := exists_addChar_addCharConductor_eq_zero (K := K)
  exact ⟨ψ, hc, hne⟩

end Existence

end GroundTheory.LocalField
end
end

section -- merged from GroundTheory.LocalFields.LubinTateTowerMaps
noncomputable section

open IntermediateField

namespace GroundTheory.LocalField

open ValuativeRel

section Restrict

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

def restrictAutFun {E F : IntermediateField K Ω} (h : F ≤ E) [Normal K F] (σ : E ≃ₐ[K] E) :
    F ≃ₐ[K] F :=
  AlgHom.restrictNormal' ((E.val.comp (σ : E →ₐ[K] E)).comp (inclusion h)) F

theorem restrictAutFun_apply {E F : IntermediateField K Ω} (h : F ≤ E) [Normal K F]
    (σ : E ≃ₐ[K] E) (x : F) : ((restrictAutFun h σ x : F) : Ω) = σ ⟨x, h x.2⟩ := by
  have := AlgHom.restrictNormal_commutes ((E.val.comp (σ : E →ₐ[K] E)).comp (inclusion h)) F x
  simp only [restrictAutFun, AlgHom.restrictNormal', AlgEquiv.coe_ofBijective]
  exact this

def restrictAut {E F : IntermediateField K Ω} (h : F ≤ E) [Normal K F] :
    (E ≃ₐ[K] E) →* (F ≃ₐ[K] F) where
  toFun := restrictAutFun h
  map_one' := AlgEquiv.ext fun x => Subtype.ext (by rw [restrictAutFun_apply]; rfl)
  map_mul' σ τ := AlgEquiv.ext fun x => Subtype.ext (by
    rw [AlgEquiv.mul_apply, restrictAutFun_apply, restrictAutFun_apply]
    have : (⟨(restrictAutFun h τ x : Ω), h (restrictAutFun h τ x).2⟩ : E) = τ ⟨x, h x.2⟩ :=
      Subtype.ext (restrictAutFun_apply h τ x)
    rw [this]
    rfl)

theorem restrictAut_apply {E F : IntermediateField K Ω} (h : F ≤ E) [Normal K F]
    (σ : E ≃ₐ[K] E) (x : F) : ((restrictAut h σ x : F) : Ω) = σ ⟨x, h x.2⟩ :=
  restrictAutFun_apply h σ x

theorem restrictAut_self {E : IntermediateField K Ω} [Normal K E] (σ : E ≃ₐ[K] E) :
    restrictAut le_rfl σ = σ :=
  AlgEquiv.ext fun x => Subtype.ext (by rw [restrictAut_apply])

theorem algEquiv_ext_of_restrictAut {ι : Type*} {F : ι → IntermediateField K Ω}
    [∀ n, Normal K (F n)] {E : IntermediateField K Ω} (hle : ∀ n, F n ≤ E)
    (hE : ∀ x ∈ E, ∃ n, x ∈ F n) {σ σ' : E ≃ₐ[K] E}
    (h : ∀ n, restrictAut (hle n) σ = restrictAut (hle n) σ') : σ = σ' := by
  refine AlgEquiv.ext fun x => Subtype.ext ?_
  obtain ⟨n, hn⟩ := hE x x.2
  have := congrArg (fun τ : F n ≃ₐ[K] F n => ((τ ⟨x, hn⟩ : F n) : Ω)) (h n)
  simp only [restrictAut_apply] at this
  exact this

theorem exists_algEquiv_of_compatible {F : ℕ → IntermediateField K Ω} (hF : Monotone F)
    [∀ n, Normal K (F n)] {E : IntermediateField K Ω} [Algebra.IsAlgebraic K E]
    (hle : ∀ n, F n ≤ E) (hE : ∀ x ∈ E, ∃ n, x ∈ F n) (τ : ∀ n, F n ≃ₐ[K] F n)
    (hτ : ∀ m n (h : m ≤ n), restrictAut (hF h) (τ n) = τ m) :
    ∃ σ : E ≃ₐ[K] E, ∀ n, restrictAut (hle n) σ = τ n := by
  have hτ' : ∀ i j (x : Ω) (hi : x ∈ F i) (hj : x ∈ F j),
      ((τ i ⟨x, hi⟩ : F i) : Ω) = ((τ j ⟨x, hj⟩ : F j) : Ω) := by
    intro i j x hi hj
    rcases le_total i j with h | h
    · rw [← hτ i j h, restrictAut_apply]
    · rw [← hτ j i h, restrictAut_apply]
  let S : ℕ → Subalgebra K Ω := fun n => (F n).toSubalgebra
  have hS : Monotone S := fun _ _ h => hF h
  let f : ∀ n, S n →ₐ[K] Ω := fun n => (F n).val.comp (τ n : F n →ₐ[K] F n)
  have hf : ∀ (i j : ℕ) (h : S i ≤ S j), f i = (f j).comp (Subalgebra.inclusion h) := by
    intro i j h
    ext x
    exact hτ' i j x x.2 (h x.2)
  have hT : E.toSubalgebra ≤ iSup S := fun x hx => by
    obtain ⟨n, hn⟩ := hE x hx
    exact (le_iSup S n) hn
  let g := Subalgebra.iSupLift S hS.directed_le f hf E.toSubalgebra hT
  have hg : ∀ (x : E) (n : ℕ) (hn : (x : Ω) ∈ F n), g x = ((τ n ⟨x, hn⟩ : F n) : Ω) :=
    fun x n hn => Subalgebra.iSupLift_of_mem (K := S) x hn
  have hgE : ∀ x : E, g x ∈ E := fun x => by
    obtain ⟨n, hn⟩ := hE x x.2
    rw [hg x n hn]
    exact hle n (τ n ⟨x, hn⟩).2
  let g' : E →ₐ[K] E := g.codRestrict E.toSubalgebra hgE
  refine ⟨AlgEquiv.ofBijective g' (Algebra.IsAlgebraic.algHom_bijective _), fun n => ?_⟩
  refine AlgEquiv.ext fun x => Subtype.ext ?_
  rw [restrictAut_apply, AlgEquiv.ofBijective_apply]
  exact hg ⟨x, hle n x.2⟩ n x.2

end Restrict

namespace FormalGroup

section Reduce

variable {K : Type*} [Field K] [ValuativeRel K]

def unitsReduce (π : 𝒪[K]) {m n : ℕ} (h : m ≤ n) :
    (𝒪[K] ⧸ Ideal.span {π ^ n})ˣ →* (𝒪[K] ⧸ Ideal.span {π ^ m})ˣ :=
  Units.map (Ideal.Quotient.factor
    (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π h))).toMonoidHom

theorem coe_unitsReduce (π : 𝒪[K]) {m n : ℕ} (h : m ≤ n) (u : (𝒪[K] ⧸ Ideal.span {π ^ n})ˣ)
    (a : 𝒪[K]) (ha : Ideal.Quotient.mk _ a = (u : 𝒪[K] ⧸ Ideal.span {π ^ n})) :
    (unitsReduce π h u : 𝒪[K] ⧸ Ideal.span {π ^ m}) = Ideal.Quotient.mk _ a := by
  rw [unitsReduce, Units.coe_map, ← ha]
  exact Ideal.Quotient.factor_mk _ a

def unitsMk (π : 𝒪[K]) (n : ℕ) : 𝒪[K]ˣ →* (𝒪[K] ⧸ Ideal.span {π ^ n})ˣ :=
  Units.map (Ideal.Quotient.mk (Ideal.span {π ^ n})).toMonoidHom

theorem coe_unitsMk (π : 𝒪[K]) (n : ℕ) (u : 𝒪[K]ˣ) :
    (unitsMk π n u : 𝒪[K] ⧸ Ideal.span {π ^ n}) = Ideal.Quotient.mk _ (u : 𝒪[K]) := rfl

theorem unitsReduce_unitsMk (π : 𝒪[K]) {m n : ℕ} (h : m ≤ n) (u : 𝒪[K]ˣ) :
    unitsReduce π h (unitsMk π n u) = unitsMk π m u :=
  Units.ext (coe_unitsReduce π h _ _ rfl)

end Reduce

section Char

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]
variable {π : 𝒪[K]} (hπ : Irreducible π) {f g : PowerSeries 𝒪[K]}

variable [IsSepClosed Ω]

open Polynomial in
local instance normal_lubinTateField (hf : IsLubinTateSeries π f) (n : ℕ) :
    Normal K (lubinTateField Ω hπ hf n) := by
  have hq := one_lt_card_residueField' K
  have hlt : IsLubinTateSeries π (ltPoly π : PowerSeries 𝒪[K]) := {
    constantCoeff_eq_zero := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, ltPoly]
      simp [coeff_X_pow, show 0 ≠ Nat.card 𝓀[K] by omega]
    coeff_one := by
      rw [Polynomial.coeff_coe, ltPoly]
      simp [coeff_X_pow, hq.ne]
    dvd_coeff_sub := fun k => by
      rw [coeff_ltPoly_sub, coeff_C_mul_X]
      split_ifs
      · exact dvd_rfl
      · exact dvd_zero π }
  have hpow (x : IdealPoint Ω (lubinTateFormalGroup hπ hlt)) :
      (π ^ n • x).val = aeval x.val ((ltPolyIter π n).map (algebraMap 𝒪[K] K)) := by
    have := t2Space_of_isValuativeTopology Ω
    induction n with
    | zero => simp [ltPolyIter_zero]
    | succ n ih =>
      rw [pow_succ', mul_smul, lubinTate_uniformizer_smul_val hlt, psEval_polynomial, ih,
        ltPolyIter_succ, Polynomial.map_comp, aeval_comp]
  let p := (ltPolyIter π n).map (algebraMap 𝒪[K] K)
  have hsep : p.Separable := separable_ltPolyIter hπ n
  have htorsion (x : IdealPoint Ω (lubinTateFormalGroup hπ hlt)) :
      x ∈ lubinTateTorsion Ω hlt n ↔ aeval x.val ((ltPolyIter π n).map (algebraMap 𝒪[K] K)) = 0 := by
    rw [mem_lubinTateTorsion, ← hpow]
    exact ⟨fun h => by rw [h]; rfl, fun h => IdealPoint.ext h⟩
  have hroots : IdealPoint.val '' (lubinTateTorsion Ω (hπ := hπ) hlt n :
      Set (IdealPoint Ω (lubinTateFormalGroup hπ hlt))) = p.rootSet Ω := by
    ext z
    rw [mem_rootSet_of_ne hsep.ne_zero]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (htorsion x).mp hx
    · intro hz
      let x : IdealPoint Ω (lubinTateFormalGroup hπ hlt) :=
        IdealPoint.mk z (valuation_lt_one_of_aeval_ltPolyIter_eq_zero hπ n hz)
      exact ⟨x, (htorsion x).mpr hz, rfl⟩
  rw [lubinTateField_eq hπ hf hlt, lubinTateField, hroots]
  have := adjoin_rootSet_isSplittingField (IsSepClosed.splits_codomain p hsep) (L := Ω)
  exact Normal.of_isSplittingField p

def lubinTateChar (hf : IsLubinTateSeries π f) (n : ℕ) {E : IntermediateField K Ω}
    (hE : lubinTateField Ω hπ hf n ≤ E) : (E ≃ₐ[K] E) →* (𝒪[K] ⧸ Ideal.span {π ^ n})ˣ :=
  (lubinTateGalEquiv hπ hf n).toMonoidHom.comp (restrictAut hE)

theorem lubinTateChar_spec (hf : IsLubinTateSeries π f) {n : ℕ} {E : IntermediateField K Ω}
    (hE : lubinTateField Ω hπ hf n ≤ E) (σ : E ≃ₐ[K] E)
    {x : IdealPoint Ω (lubinTateFormalGroup hπ hf)} (hx : x ∈ lubinTateTorsion Ω hf n) (a : 𝒪[K])
    (ha : Ideal.Quotient.mk _ a = (lubinTateChar hπ hf n hE σ : 𝒪[K] ⧸ Ideal.span {π ^ n})) :
    ((σ ⟨x.val, hE (val_mem_lubinTateField hπ hf hx)⟩ : E) : Ω) = (a • x).val :=
  (restrictAut_apply hE σ ⟨x.val, val_mem_lubinTateField hπ hf hx⟩).symm.trans
    (lubinTateGalEquiv_spec hf n (restrictAut hE σ) x hx a ha)

theorem lubinTateChar_eq_of_apply (hf : IsLubinTateSeries π f) {n : ℕ} {E : IntermediateField K Ω}
    (hE : lubinTateField Ω hπ hf n ≤ E) (σ : E ≃ₐ[K] E) (a : 𝒪[K])
    (h : ∀ (x) (hx : x ∈ lubinTateTorsion Ω (hπ := hπ) hf n),
      ((σ ⟨x.val, hE (val_mem_lubinTateField hπ hf hx)⟩ : E) : Ω) = (a • x).val) :
    (lubinTateChar hπ hf n hE σ : 𝒪[K] ⧸ Ideal.span {π ^ n}) = Ideal.Quotient.mk _ a := by
  obtain ⟨l, hl, hann, -⟩ := exists_generator_lubinTateTorsion (Ω := Ω) (hπ := hπ) hf n
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective
    (lubinTateChar hπ hf n hE σ : 𝒪[K] ⧸ Ideal.span {π ^ n})
  have h1 := lubinTateChar_spec hπ hf hE σ hl b hb
  rw [h l hl] at h1
  have h2 : b • l = a • l := (IdealPoint.ext h1).symm
  rw [← hb, Ideal.Quotient.eq, ← hann, sub_smul, sub_eq_zero]
  exact h2

theorem lubinTateChar_reduce (hf : IsLubinTateSeries π f) {m n : ℕ} (hmn : m ≤ n)
    {E : IntermediateField K Ω} (hE : lubinTateField Ω hπ hf n ≤ E) (σ : E ≃ₐ[K] E) :
    lubinTateChar hπ hf m ((lubinTateField_mono hπ hf hmn).trans hE) σ =
      unitsReduce π hmn (lubinTateChar hπ hf n hE σ) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    (lubinTateChar hπ hf n hE σ : 𝒪[K] ⧸ Ideal.span {π ^ n})
  apply Units.ext
  rw [coe_unitsReduce π hmn _ a ha, lubinTateChar_eq_of_apply hπ hf _ σ a]
  intro x hx
  exact lubinTateChar_spec hπ hf hE σ (lubinTateTorsion_mono hπ hf hmn hx) a ha

theorem lubinTateGalEquiv_restrictAut (hf : IsLubinTateSeries π f) {m n : ℕ} (hmn : m ≤ n)
    (σ : lubinTateField Ω hπ hf n ≃ₐ[K] lubinTateField Ω hπ hf n) :
    lubinTateGalEquiv hπ hf m (restrictAut (lubinTateField_mono hπ hf hmn) σ) =
      unitsReduce π hmn (lubinTateGalEquiv hπ hf n σ) := by
  have := lubinTateChar_reduce hπ hf hmn le_rfl σ
  simp only [lubinTateChar, MonoidHom.coe_comp, Function.comp_apply, restrictAut_self] at this
  exact this

end Char

end FormalGroup

end GroundTheory.LocalField
end
end

section -- merged from GroundTheory.LocalFields.LowerIndexQuotient
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel IsLocalRing IsDiscreteValuationRing Polynomial

theorem addVal_prod {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {ι : Type*}
    (s : Finset ι) (f : ι → R) : addVal R (∏ i ∈ s, f i) = ∑ i ∈ s, addVal R (f i) :=
  _root_.Bl.general_b_fact'''''''.goal1 s f

section Restrict

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (M : IntermediateField K L)

theorem restrictNormalHom_restrictScalars [Normal K M] (τ : L ≃ₐ[M] L) :
    AlgEquiv.restrictNormalHom M (τ.restrictScalars K) = 1 := by
  rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker, ← range_restrictScalarsHom M]
  exact ⟨τ, rfl⟩

theorem exists_eq_mul_restrictScalars_of_restrictNormalHom_eq [Normal K M] {σ ρ : L ≃ₐ[K] L}
    (h : AlgEquiv.restrictNormalHom M ρ = AlgEquiv.restrictNormalHom M σ) :
    ∃ τ : L ≃ₐ[M] L, σ * τ.restrictScalars K = ρ := by
  have hker : σ⁻¹ * ρ ∈ (AlgEquiv.restrictNormalHom M).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  rw [IntermediateField.restrictNormalHom_ker, ← range_restrictScalarsHom M] at hker
  obtain ⟨τ, hτ⟩ := hker
  refine ⟨τ, ?_⟩
  rw [← AlgEquiv.restrictScalarsHom_apply, hτ, mul_inv_cancel_left]

end Restrict

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

section

variable (M : IntermediateField K L)

section
variable [IsGalois K L]

theorem ramificationIndex_mul_lowerIndex_restrictNormalHom [Normal K M] (σ : L ≃ₐ[K] L) :
    ((_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation M))) : ℕ∞) * lowerIndex K M (AlgEquiv.restrictNormalHom M σ) =
      ∑ τ : L ≃ₐ[M] L, lowerIndex K L (σ * τ.restrictScalars K) :=
  by apply _root_.UpperTheory.Reformulated.B.RamificationLowerIndex.ramificationIndex_mul_lowerIndex_restrictNormalHom <;> assumption
end

theorem exists_lowerIndex_mul_eq_min (σ : L ≃ₐ[K] L) :
    ∃ τ₀ : L ≃ₐ[M] L,
      (∀ τ : L ≃ₐ[M] L, lowerIndex K L (σ * τ.restrictScalars K) ≤
        lowerIndex K L (σ * τ₀.restrictScalars K)) ∧
      ∀ τ : L ≃ₐ[M] L, lowerIndex K L (σ * τ₀.restrictScalars K * τ.restrictScalars K) =
        min (lowerIndex M L τ) (lowerIndex K L (σ * τ₀.restrictScalars K)) := by
  obtain ⟨τ₀, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun τ : L ≃ₐ[M] L ↦ lowerIndex K L (σ * τ.restrictScalars K)) Finset.univ_nonempty
  refine ⟨τ₀, fun τ ↦ hmax τ (Finset.mem_univ _), fun τ ↦ ?_⟩
  set σ₀ := σ * τ₀.restrictScalars K with hσ₀
  rw [← lowerIndex_restrictScalars (K := K)]
  rcases lt_or_ge (lowerIndex K L (τ.restrictScalars K)) (lowerIndex K L σ₀) with h | h
  · rw [lowerIndex_mul_of_lt h, min_eq_left h.le]
  · rw [min_eq_right h]
    refine le_antisymm ?_ ((min_eq_left h).symm.le.trans (min_le_lowerIndex_mul _ _))
    have hm : (τ₀ * τ).restrictScalars K = τ₀.restrictScalars K * τ.restrictScalars K :=
      AlgEquiv.ext fun _ ↦ rfl
    have := hmax (τ₀ * τ) (Finset.mem_univ _)
    rwa [hm, ← mul_assoc] at this

end

end GroundTheory.LocalField
end
end

section -- merged from GroundTheory.LocalFields.LocalZetaShell
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Order

variable (K) in
theorem exists_units_ord_eq_one : ∃ π : Kˣ, ord (π : K) = 1 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have h0 : (ϖ : K) ≠ 0 := by exact_mod_cast hϖ.ne_zero
  exact ⟨Units.mk0 _ h0, by rw [Units.val_mk0]; exact ord_uniformizer hϖ⟩


variable (K) in
def unifUnit : Kˣ := (exists_units_ord_eq_one K).choose

theorem ord_unifUnit : ord (unifUnit K : K) = 1 := (exists_units_ord_eq_one K).choose_spec

theorem ord_units_mul (u v : Kˣ) : ord ((u * v : Kˣ) : K) = ord (u : K) + ord (v : K) := by
  rw [Units.val_mul, ord_mul u.ne_zero v.ne_zero]

theorem ord_units_zpow (u : Kˣ) (k : ℤ) : ord ((u ^ k : Kˣ) : K) = k * ord (u : K) := by
  rw [Units.val_zpow_eq_zpow_val]
  simp [ord, map_zpow₀, WithZero.log_zpow]

theorem ord_units_inv (u : Kˣ) : ord ((u⁻¹ : Kˣ) : K) = -ord (u : K) := by
  rw [Units.val_inv_eq_inv_val, ord_inv u.ne_zero]

theorem ord_unifUnit_zpow (k : ℤ) : ord ((unifUnit K ^ k : Kˣ) : K) = k := by
  rw [ord_units_zpow, ord_unifUnit, mul_one]

theorem valuation_eq_one_iff_ord_eq_zero {x : K} (hx : x ≠ 0) :
    valuation K x = 1 ↔ ord x = 0 := by
  have h0 := mem_valBall_iff_le_ord (n := 0) hx
  have h1 := mem_valBall_iff_le_ord (n := 1) hx
  rw [mem_valBall_zero_iff, Valuation.mem_integer_iff] at h0
  rw [mem_valBall_one_iff] at h1
  constructor
  · intro h
    have a := h0.mp h.le
    have b : ¬ 1 ≤ ord x := fun hb => (h1.mpr hb).ne h
    omega
  · intro h
    refine le_antisymm (h0.mpr h.ge) (not_lt.mp fun hl => ?_)
    have := h1.mp hl
    omega

theorem mem_unitFiltrationUnits_zero_iff_ord {u : Kˣ} :
    u ∈ unitFiltrationUnits K 0 ↔ ord (u : K) = 0 := by
  rw [mem_unitFiltrationUnits_zero_iff, valuation_eq_one_iff_ord_eq_zero u.ne_zero]

end Order

section Shell


variable (K) in
def ordShell (k : ℤ) : Set Kˣ := {u | ord (u : K) = k}

theorem mem_ordShell {k : ℤ} {u : Kˣ} : u ∈ ordShell K k ↔ ord (u : K) = k := Iff.rfl

theorem ordShell_zero : ordShell K 0 = (unitFiltrationUnits K 0 : Set Kˣ) := by
  ext u
  rw [SetLike.mem_coe, mem_unitFiltrationUnits_zero_iff_ord]
  rfl

theorem mul_mem_ordShell_iff (v : Kˣ) {k : ℤ} {u : Kˣ} :
    v * u ∈ ordShell K (ord (v : K) + k) ↔ u ∈ ordShell K k := by
  simp only [mem_ordShell, ord_units_mul]
  omega

theorem pairwise_disjoint_ordShell : Pairwise (Function.onFun Disjoint (ordShell K)) := by
  intro i j hij
  exact Set.disjoint_left.mpr fun u hi hj => hij (hi.symm.trans hj)

theorem iUnion_ordShell : ⋃ k, ordShell K k = Set.univ :=
  Set.eq_univ_of_forall fun _ => Set.mem_iUnion.mpr ⟨_, rfl⟩

end Shell

section Measure

variable [MeasurableSpace K] [BorelSpace K]

theorem measurable_units_val : Measurable (Units.val : Kˣ → K) :=
  measurableEmbedding_units_val.measurable

instance instMeasurableMul₂UnitsLocalField : MeasurableMul₂ Kˣ where
  measurable_mul := by
    rw [← measurableEmbedding_units_val.measurable_comp_iff]
    have : (Units.val ∘ fun p : Kˣ × Kˣ => p.1 * p.2) = fun p => (p.1 : K) * (p.2 : K) := by
      funext p
      simp
    rw [this]
    exact (measurable_units_val.comp measurable_fst).mul (measurable_units_val.comp measurable_snd)

instance instBorelSpaceUnitsLocalField : BorelSpace Kˣ := by
  refine ⟨?_⟩
  calc (Units.instMeasurableSpace : MeasurableSpace Kˣ) = MeasurableSpace.comap Units.val (borel K) := by
        rw [← BorelSpace.measurable_eq]
        rfl
    _ = borel Kˣ := by
        rw [(Units.isEmbedding_val₀ (G₀ := K)).isInducing.eq_induced, borel_comap]

theorem measurableSet_ordShell (k : ℤ) : MeasurableSet (ordShell K k) := by
  have : ordShell K k = Units.val ⁻¹' ((valBall K k : Set K) \ valBall K (k + 1)) := by
    ext u
    simp only [mem_ordShell, Set.mem_preimage, Set.mem_sdiff, SetLike.mem_coe,
      mem_valBall_iff_le_ord u.ne_zero]
    omega
  rw [this]
  exact ((measurableSet_valBall k).diff (measurableSet_valBall (k + 1))).preimage
    measurable_units_val

theorem multHaar_ordShell (k : ℤ) : multHaar K (ordShell K k) = 1 := by
  have h : (fun u => unifUnit K ^ k * u) ⁻¹' ordShell K k = ordShell K 0 := by
    ext u
    have := mul_mem_ordShell_iff (K := K) (unifUnit K ^ k) (k := 0) (u := u)
    rwa [ord_unifUnit_zpow, add_zero] at this
  rw [← measure_preimage_mul (multHaar K) (unifUnit K ^ k), h, ordShell_zero,
    multHaar_unitFiltrationUnits_zero]

instance instSigmaFiniteMultHaar : SigmaFinite (multHaar K) := by
  refine Measure.sigmaFinite_of_countable (S := Set.range (ordShell K)) (Set.countable_range _) ?_ ?_
  · rintro _ ⟨k, rfl⟩
    rw [multHaar_ordShell]
    exact ENNReal.one_lt_top
  · rw [Set.sUnion_range, iUnion_ordShell]

theorem lintegral_multHaar_eq_tsum (g : Kˣ → ℝ≥0∞) :
    ∫⁻ u, g u ∂multHaar K = ∑' k : ℤ, ∫⁻ u in ordShell K k, g u ∂multHaar K := by
  rw [← lintegral_iUnion measurableSet_ordShell pairwise_disjoint_ordShell, iUnion_ordShell,
    Measure.restrict_univ]

theorem lintegral_multHaar_le_tsum (g : Kˣ → ℝ≥0∞) (a : ℤ → ℝ≥0∞)
    (h : ∀ u, g u ≤ a (ord (u : K))) : ∫⁻ u, g u ∂multHaar K ≤ ∑' k, a k := by
  rw [lintegral_multHaar_eq_tsum]
  refine ENNReal.tsum_le_tsum fun k => ?_
  calc ∫⁻ u in ordShell K k, g u ∂multHaar K ≤ ∫⁻ _ in ordShell K k, a k ∂multHaar K :=
        setLIntegral_mono' (measurableSet_ordShell k) fun u hu => (h u).trans_eq (by rw [hu])
    _ = a k := by rw [setLIntegral_const, multHaar_ordShell, mul_one]

theorem hasSum_setIntegral_ordShell {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Kˣ → E} (hF : Integrable F (multHaar K)) :
    HasSum (fun k : ℤ => ∫ u in ordShell K k, F u ∂multHaar K) (∫ u, F u ∂multHaar K) := by
  have := hasSum_integral_iUnion (μ := multHaar K) (measurableSet_ordShell (K := K))
    (pairwise_disjoint_ordShell (K := K)) (by rw [iUnion_ordShell]; exact hF.integrableOn)
  rwa [iUnion_ordShell, Measure.restrict_univ] at this

theorem setIntegral_ordShell_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Kˣ → E) (v : Kˣ) (k : ℤ) :
    ∫ u in ordShell K (ord (v : K) + k), F u ∂multHaar K =
      ∫ u in ordShell K k, F (v * u) ∂multHaar K := by
  rw [← integral_indicator (measurableSet_ordShell _), ← integral_indicator (measurableSet_ordShell _),
    ← integral_mul_left_eq_self _ v]
  congr 1
  funext u
  by_cases hu : u ∈ ordShell K k
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem ((mul_mem_ordShell_iff v).mpr hu)]
  · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem (mt (mul_mem_ordShell_iff v).mp hu)]


omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [MeasurableSpace K]
  [BorelSpace K] in
theorem integral_eq_zero_of_mul_eq {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (F : G → ℂ) (v : G) {a : ℂ} (ha : a ≠ 1)
    (hF : ∀ u, F (v * u) = a * F u) : ∫ u, F u ∂μ = 0 := by
  refine eq_zero_of_eq_mul_of_ne_one ha ?_
  calc ∫ u, F u ∂μ = ∫ u, F (v * u) ∂μ := (integral_mul_left_eq_self F v).symm
    _ = ∫ u, a * F u ∂μ := by simp only [hF]
    _ = a * ∫ u, F u ∂μ := integral_const_mul a _

theorem setIntegral_ordShell_eq_zero (F : Kˣ → ℂ) {v : Kˣ} (hv : ord (v : K) = 0) {a : ℂ}
    (ha : a ≠ 1) (k : ℤ) (hF : ∀ u ∈ ordShell K k, F (v * u) = a * F u) :
    ∫ u in ordShell K k, F u ∂multHaar K = 0 := by
  rw [← integral_indicator (measurableSet_ordShell k)]
  refine integral_eq_zero_of_mul_eq _ _ v ha fun u => ?_
  have hiff : v * u ∈ ordShell K k ↔ u ∈ ordShell K k := by
    have := mul_mem_ordShell_iff (K := K) v (k := k) (u := u)
    rwa [hv, zero_add] at this
  by_cases hu : u ∈ ordShell K k
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem (hiff.mpr hu), hF u hu]
  · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem (mt hiff.mp hu), mul_zero]

end Measure

section Power

theorem residueCard_pos_real : (0 : ℝ) < residueCard K := by
  exact_mod_cast zero_lt_one.trans one_lt_residueCard

theorem residueCard_ne_zero_complex : (residueCard K : ℂ) ≠ 0 := by
  exact_mod_cast residueCard_ne_zero

theorem modulus_cpow_eq_zpow (u : Kˣ) (s : ℂ) :
    ((modulus (u : K) : ℝ) : ℂ) ^ s = ((residueCard K : ℂ) ^ (-s)) ^ ord (u : K) := by
  have hq := residueCard_pos_real (K := K)
  rw [modulus_of_ne_zero u.ne_zero, NNReal.coe_zpow, NNReal.coe_natCast]
  have hpos : (0 : ℝ) < (residueCard K : ℝ) ^ (-ord (u : K)) := zpow_pos hq _
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'),
    Complex.cpow_def_of_ne_zero residueCard_ne_zero_complex, ← Complex.exp_int_mul,
    ← Complex.ofReal_log hpos.le, Real.log_zpow, ← Complex.ofReal_natCast,
    ← Complex.ofReal_log hq.le]
  push_cast
  ring_nf

theorem norm_qpow (s : ℂ) : ‖(residueCard K : ℂ) ^ (-s)‖ = (residueCard K : ℝ) ^ (-s.re) := by
  rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos residueCard_pos_real,
    Complex.neg_re]

theorem qpow_ne_zero (s : ℂ) : (residueCard K : ℂ) ^ (-s) ≠ 0 := by
  rw [Complex.cpow_def_of_ne_zero residueCard_ne_zero_complex]
  exact Complex.exp_ne_zero _

end Power

end GroundTheory.LocalField
end
end
