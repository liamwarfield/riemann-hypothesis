module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumNormSqLeOfRootOfUnityAddCharCombination
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumNormSqLeOfRootOfUnityAddCharCombination
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.ParsevalRootsOfUnity

theorem isIntegral_of_pow_eq_one {R : Type} [CommRing R] (z : R) (m : ℕ) (hm : 0 < m)
    (h : z ^ m = 1) : IsIntegral ℤ z :=
  ⟨Polynomial.X ^ m - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hm.ne', by simp [h]⟩

theorem mem_Qbar_of_pow_eq_one (z : ℂ) (m : ℕ) (hm : 0 < m) (h : z ^ m = 1) : z ∈ Qbar := by
  rw [mem_algebraicClosure_iff]
  exact ((isIntegral_of_pow_eq_one z m hm h).tower_top (A := ℚ)).isAlgebraic

theorem norm_eq_one_of_pow_eq_one' (z : ℂ) (m : ℕ) (hm : 0 < m) (h : z ^ m = 1) : ‖z‖ = 1 :=
  (pow_eq_one_iff_of_nonneg (norm_nonneg z) hm.ne').1 (by rw [← norm_pow, h, norm_one])

theorem exists_integral_coeffs_sum_norm_sq_le_of_rootOfUnity : ∀ {ι Q : Type} [Fintype ι] [Fintype Q] [AddCommGroup Q] (N k : ℕ) (c : ι → ℂ) (χ : ι → AddChar Q ℂ), 0 < N → (∀ i, ∃ m : ℕ, 0 < m ∧ c i ^ m = 1) → Function.Injective χ → Fintype.card Q = N ^ k → Fintype.card ι ≤ N ^ k → ∃ r : Q → Qbar, (∀ q, (r q : ℂ) = ((N : ℂ) ^ k)⁻¹ * ∑ i, c i * χ i q) ∧ (∀ q, IsIntegral ℤ ((N : Qbar) ^ k * r q)) ∧ ∀ ρ : Qbar →+* ℂ, (∑ q, ‖ρ (r q)‖) ^ 2 ≤ (N : ℝ) ^ k := by
  intro ι Q _ _ _ N k c χ hN hc hχ hQ hι
  classical
  choose m hm hcm using hc
  have hQpos : 0 < Fintype.card Q := Fintype.card_pos
  have hχq : ∀ i q, χ i q ^ Fintype.card Q = 1 := fun i q => by
    rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero, AddChar.map_zero_eq_one]
  let cq : ι → Qbar := fun i => ⟨c i, mem_Qbar_of_pow_eq_one _ _ (hm i) (hcm i)⟩
  let xq : ι → Q → Qbar := fun i q => ⟨χ i q, mem_Qbar_of_pow_eq_one _ _ hQpos (hχq i q)⟩
  have hNQ : (N : Qbar) ≠ 0 := by exact_mod_cast hN.ne'
  let r : Q → Qbar := fun q => ((N : Qbar) ^ k)⁻¹ * ∑ i, cq i * xq i q
  refine ⟨r, ?_, ?_, ?_⟩
  · intro q
    simp [r, cq, xq]
  · intro q
    have : (N : Qbar) ^ k * r q = ∑ i, cq i * xq i q := by
      simp only [r]
      rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hNQ), one_mul]
    rw [this]
    refine IsIntegral.sum _ fun i _ => IsIntegral.mul ?_ ?_
    · exact isIntegral_of_pow_eq_one _ (m i) (hm i) (Subtype.ext (by simpa [cq] using hcm i))
    · exact isIntegral_of_pow_eq_one _ _ hQpos (Subtype.ext (by simpa [xq] using hχq i q))
  · intro ρ
    let χ' : ι → AddChar Q Qbar := fun i =>
      { toFun := xq i
        map_zero_eq_one' := Subtype.ext (by simp [xq])
        map_add_eq_mul' := fun a b => Subtype.ext (by simp [xq, AddChar.map_add_eq_mul]) }
    let ψ : ι → AddChar Q ℂ := fun i => (ρ : Qbar →* ℂ).compAddChar (χ' i)
    have hψ : ∀ i q, ψ i q = ρ (xq i q) := fun i q => rfl
    let a : ι → ℂ := fun i => ρ (cq i)
    have ha : ∀ i, a i * (starRingEnd ℂ) (a i) = 1 := by
      intro i
      have h1 : a i ^ m i = 1 := by
        simp only [a]
        rw [← map_pow]
        have : cq i ^ m i = 1 := Subtype.ext (by simpa [cq] using hcm i)
        rw [this, map_one]
      rw [Complex.mul_conj', norm_eq_one_of_pow_eq_one' _ _ (hm i) h1]
      simp
    have hinj : Function.Injective ψ := by
      intro i j hij
      apply hχ
      ext q
      have h1 : ρ (xq i q) = ρ (xq j q) := by rw [← hψ, ← hψ, hij]
      have h2 := congrArg Subtype.val (ρ.injective h1)
      simpa [xq] using h2
    have horth : ∀ i j, ∑ q, ψ i q * (starRingEnd ℂ) (ψ j q) = if i = j then (Fintype.card Q : ℂ) else 0 := by
      intro i j
      have : ∀ q, ψ i q * (starRingEnd ℂ) (ψ j q) = (ψ i - ψ j) q := fun q => by
        rw [AddChar.sub_apply, AddChar.map_neg_eq_conj]
      simp_rw [this]
      rw [AddChar.sum_eq_ite]
      by_cases h : i = j
      · simp [h]
      · have : ψ i - ψ j ≠ 0 := fun h' => h (hinj (sub_eq_zero.1 h'))
        simp [h, this]
    let f : Q → ℂ := fun q => ∑ i, a i * ψ i q
    have hpars : ∑ q, ‖f q‖ ^ 2 = (Fintype.card Q : ℝ) * Fintype.card ι := by
      apply Complex.ofReal_injective
      push_cast
      simp_rw [← Complex.mul_conj']
      calc ∑ q, f q * (starRingEnd ℂ) (f q)
          = ∑ q, ∑ i, ∑ j, (a i * (starRingEnd ℂ) (a j)) * (ψ i q * (starRingEnd ℂ) (ψ j q)) := by
            refine Finset.sum_congr rfl fun q _ => ?_
            set_option synthInstance.maxHeartbeats 100000 in
              simp only [f, map_sum, map_mul, Finset.sum_mul_sum]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            ring
        _ = ∑ i, ∑ j, (a i * (starRingEnd ℂ) (a j)) * ∑ q, (ψ i q * (starRingEnd ℂ) (ψ j q)) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_comm]
            simp [Finset.mul_sum]
        _ = ∑ i, (Fintype.card Q : ℂ) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            simp [horth, ha]
        _ = (Fintype.card Q : ℂ) * Fintype.card ι := by
            simp [mul_comm]
    have hCS : (∑ q, ‖f q‖) ^ 2 ≤ (Fintype.card Q : ℝ) * ∑ q, ‖f q‖ ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset Q)) (f := fun q => ‖f q‖)
      simpa using this
    have hρr : ∀ q, ‖ρ (r q)‖ = ((N : ℝ) ^ k)⁻¹ * ‖f q‖ := by
      intro q
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [r, map_mul, map_inv₀, map_pow, map_natCast, map_sum, norm_mul, norm_inv,
        norm_pow, Complex.norm_natCast, f, a, hψ]
    simp_rw [hρr]
    rw [← Finset.mul_sum, mul_pow]
    have hNk : (0 : ℝ) < (N : ℝ) ^ k := by positivity
    have hQr : (Fintype.card Q : ℝ) = (N : ℝ) ^ k := by exact_mod_cast hQ
    have hιr : (Fintype.card ι : ℝ) ≤ (N : ℝ) ^ k := by exact_mod_cast hι
    calc (((N : ℝ) ^ k)⁻¹) ^ 2 * (∑ q, ‖f q‖) ^ 2
        ≤ (((N : ℝ) ^ k)⁻¹) ^ 2 * ((Fintype.card Q : ℝ) * ((Fintype.card Q : ℝ) * (Fintype.card ι : ℝ))) := by
          gcongr
          rw [← hpars]; exact hCS
      _ = (Fintype.card ι : ℝ) := by
          rw [hQr]; field_simp
      _ ≤ (N : ℝ) ^ k := hιr

end GlobalTheory.ParsevalRootsOfUnity
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumNormSqLeOfRootOfUnityAddCharCombinationStatement
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_norm_sq_le_of_rootOfUnity_addChar_combination : ∀ {ι Q : Type} [Fintype ι] [Fintype Q] [AddCommGroup Q] (N k : ℕ) (c : ι → ℂ) (χ : ι → AddChar Q ℂ), 0 < N → (∀ i, ∃ m : ℕ, 0 < m ∧ c i ^ m = 1) → Function.Injective χ → Fintype.card Q = N ^ k → Fintype.card ι ≤ N ^ k → ∃ r : Q → Qbar, (∀ q, (r q : ℂ) = ((N : ℂ) ^ k)⁻¹ * ∑ i, c i * χ i q) ∧ (∀ q, IsIntegral ℤ ((N : Qbar) ^ k * r q)) ∧ ∀ ρ : Qbar →+* ℂ, (∑ q, ‖ρ (r q)‖) ^ 2 ≤ (N : ℝ) ^ k := by
  first | exact @GlobalTheory.ParsevalRootsOfUnity.exists_integral_coeffs_sum_norm_sq_le_of_rootOfUnity | exact GlobalTheory.ParsevalRootsOfUnity.exists_integral_coeffs_sum_norm_sq_le_of_rootOfUnity | (intros; apply GlobalTheory.ParsevalRootsOfUnity.exists_integral_coeffs_sum_norm_sq_le_of_rootOfUnity <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarFundamentalDomainConjugateUnitaryAdeli
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarFundamentalDomainConjugateUnitaryAdeli
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.HaarConj

variable {D : D7}

theorem isFundamentalDomain_image {G H : Type} [Group G] [Group H] [MeasurableSpace G] [MeasurableSpace H]
    (φ : G ≃* H) (hc : Measurable φ) (hc' : Measurable φ.symm) (Γ : Subgroup G) (Γ' : Subgroup H)
    (hQ : ∀ g, g ∈ Γ ↔ φ g ∈ Γ') (μ : Measure G) (𝓕 : Set G) (h : IsFundamentalDomain Γ 𝓕 μ) :
    IsFundamentalDomain Γ' (φ '' 𝓕) (μ.map φ) := by
  let ψ : G ≃ᵐ H := ⟨φ.toEquiv, hc, hc'⟩
  have hψ : MeasurePreserving ψ μ (μ.map φ) := ⟨ψ.measurable, rfl⟩
  have e : φ '' 𝓕 = φ.symm ⁻¹' 𝓕 := φ.toEquiv.image_eq_preimage_symm 𝓕
  rw [e]
  exact h.preimage_of_equiv (f := φ.symm) (MeasurePreserving.symm ψ hψ).quasiMeasurePreserving
    (e := fun γ => ⟨φ γ, (hQ γ).1 γ.2⟩)
    ⟨fun a b hab => Subtype.ext (φ.injective (congrArg Subtype.val hab)),
      fun b => ⟨⟨φ.symm b, (hQ _).2 (by simp)⟩, Subtype.ext (by simp)⟩⟩
    fun γ y => by
      show φ.symm (φ γ * y) = γ * φ.symm y
      rw [map_mul, φ.symm_apply_apply]

theorem cA_incA (e : D.host.E) : cA D (incA D e) = incA D (D.sp.cm.sig e) := by
  simp [cA, sigR, incA, inclR, Algebra.TensorProduct.map_tmul]

theorem incA_inj : Function.Injective (incA D) :=
  Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (R := 𝓞 D.host.F) (K := D.host.F))

def conjInv (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hc : c ≠ 0)
    (h : J = c • V.gram) (u : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) : GA D V :=
  ⟨GeneralLinearGroup.map (cA D) u.1, by
    have hu : u.1.1ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J * u.1.1.map (cA D) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J := u.2
    have e : (u.1.1.map (cA D)).map (cA D) = u.1.1 := Matrix.ext fun _ _ => cA_cA _
    show Formalism.UG.cT (cA D) (u.1.1.map (cA D)) * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM V.gram * u.1.1.map (cA D)
      = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM V.gram
    rw [Formalism.UG.cT, e]
    generalize u.1.1 = M at hu ⊢
    rw [h, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul, Matrix.mul_smul, Matrix.smul_mul] at hu
    have k : incA D c⁻¹ * incA D c = 1 := by rw [← map_mul, inv_mul_cancel₀ hc, map_one]
    have := congrArg (incA D c⁻¹ • ·) hu
    simpa only [smul_smul, k, one_smul] using this⟩

def conjE (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hc : c ≠ 0)
    (h : J = c • V.gram) : GA D V ≃* GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J where
  toFun := conjU V c h
  invFun := conjInv V c hc h
  left_inv g := Subtype.ext (Units.ext (Matrix.ext fun _ _ => cA_cA _))
  right_inv u := Subtype.ext (Units.ext (Matrix.ext fun _ _ => cA_cA _))
  map_mul' a b := Subtype.ext (by
    show GeneralLinearGroup.map (cA D) (matHom V (a * b)) = GeneralLinearGroup.map (cA D) (matHom V a) *
      GeneralLinearGroup.map (cA D) (matHom V b)
    rw [map_mul, map_mul])

theorem continuous_conjInv (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hc : c ≠ 0)
    (h : J = c • V.gram) : Continuous (conjInv V c hc h) := by
  have h1 : Continuous (fun u : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J => u.1) := continuous_subtype_val
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact (Units.continuous_val.comp h1).matrix_map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conj D)
  · exact (Units.continuous_coe_inv.comp h1).matrix_map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conj D)

theorem mem_ratU_iff (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hc : c ≠ 0)
    (h : J = c • V.gram) (g : GA D V) :
    g ∈ GQ V ↔ conjE V c hc h g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig J := by
  have hg : Formalism.UG.cT (cA D) g.1.1 * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM V.gram * g.1.1 = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM V.gram := g.2
  constructor
  · intro hq
    obtain ⟨x, -, hx⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hq)
    refine Subgroup.mem_subgroupOf.2 ⟨GeneralLinearGroup.map (D.sp.cm.sig : D.host.E →+* D.host.E) x, ?_⟩
    refine Units.ext (Matrix.ext fun i j => ?_)
    have := congrArg (fun y : GL (Fin V.rank) (AE D) => y.1 i j) hx
    show incA D (D.sp.cm.sig (x.1 i j)) = cA D (g.1.1 i j)
    rw [← this, ← cA_incA]
    rfl
  · intro hq
    obtain ⟨w, hw⟩ := Subgroup.mem_subgroupOf.1 hq
    have hw' : ∀ i j, incA D (w.1 i j) = cA D (g.1.1 i j) := fun i j =>
      congrArg (fun y : GL (Fin V.rank) (AE D) => y.1 i j) hw
    have hx : ∀ i j, incA D (D.sp.cm.sig (w.1 i j)) = g.1.1 i j := fun i j => by
      rw [← cA_incA, hw', cA_cA]
    let x := GeneralLinearGroup.map (D.sp.cm.sig : D.host.E →+* D.host.E) w
    have hxm : x.1.map (incA D) = g.1.1 := Matrix.ext fun i j => hx i j
    refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨x, ?_, Units.ext (Matrix.ext fun i j => hx i j)⟩)
    show Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) x.1 * V.gram * x.1 = V.gram
    have key : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) x.1 * V.gram * x.1).map (incA D) =
        V.gram.map (incA D) := by
      rw [Matrix.map_mul, Matrix.map_mul, hxm]
      have e1 : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) x.1).map (incA D) = Formalism.UG.cT (cA D) g.1.1 := by
        rw [← hxm]
        ext i j
        simp only [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply]
        exact (cA_incA _).symm
      rw [e1]
      exact hg
    exact Matrix.ext fun i j => incA_inj (congrFun (congrFun key i) j)

theorem haarConj : ∀ {D : D7} (V : HSp D) (c : D.host.E), c ≠ 0 → ∀ {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (hJ : J = c • V.gram)
    (ν : Measure (GA D V)) (fd : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) fd ν →
    ∃ dom : Set (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J), (ν.map (conjU V c hJ)).IsHaarMeasure ∧
      IsFundamentalDomain (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig J) dom (ν.map (conjU V c hJ)) := by
  intro D V c hc J hJ ν fd hν hfd
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have : BorelSpace (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) := ⟨rfl⟩
  have c1 : Continuous (conjE V c hc hJ) := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conjU V c hJ
  have c2 : Continuous (conjE V c hc hJ).symm := continuous_conjInv V c hc hJ
  exact ⟨conjE V c hc hJ '' fd, MulEquiv.isHaarMeasure_map ν (conjE V c hc hJ) c1 c2,
    isFundamentalDomain_image (conjE V c hc hJ) c1.measurable c2.measurable (GQ V) _ (mem_ratU_iff V c hc hJ) ν fd hfd⟩

end GlobalTheory.HaarConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarFundamentalDomainConjugateUnitaryAdeliStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_haar_fundamentalDomain_conjugateUnitaryAdelicIso : ∀ {D : D7} (V : HSp D) (c : D.host.E), c ≠ 0 → ∀ {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (hJ : J = c • V.gram)
    (ν : Measure (GA D V)) (fd : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) fd ν →
    ∃ dom : Set (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J), (ν.map (conjU V c hJ)).IsHaarMeasure ∧
      IsFundamentalDomain (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig J) dom (ν.map (conjU V c hJ)) := by
  first | exact @GlobalTheory.HaarConj.haarConj | exact GlobalTheory.HaarConj.haarConj | (intros; apply GlobalTheory.HaarConj.haarConj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLatticeStableIffConjIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLatticeStableIffConjIntegral
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

noncomputable section

namespace GlobalTheory.InertUnitOrb.LatStable

theorem mulVec_int_iff {E : Type} [Field E] [NumberField E] {n : ℕ} (w : Pl E)
    (M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) :
    (∀ v : Fin n → w.adicCompletion E, (∀ i, Valued.v (v i) ≤ 1) → ∀ i, Valued.v ((M *ᵥ v) i) ≤ 1) ↔
      ∀ i j, Valued.v (M i j) ≤ 1 := by
  have hmem : ∀ x : w.adicCompletion E, Valued.v x ≤ 1 ↔ x ∈ Formalism.UG.Ov E w := fun x =>
    (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 E) (K := E) (v := w)).symm
  constructor
  · intro h i j
    have := h (Pi.single j 1) (fun k => by
      by_cases hk : k = j
      · subst hk; simp
      · simp [Pi.single_apply, hk]) i
    simpa [Matrix.mulVec_single] using this
  · intro h v hv i
    rw [hmem]
    simp only [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ ((hmem _).1 (h i k)) ((hmem _).1 (hv k))

theorem mem_KGL_of_int {E : Type} [Field E] [NumberField E] {n : ℕ} (w : Pl E) (M : GLw n w)
    (h1 : ∀ i j, Valued.v ((M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ 1)
    (h2 : ∀ i j, Valued.v (((M⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ 1) :
    M ∈ GlobalTheory.LFun.KGL w (n := n) := by
  have hmem : ∀ x : w.adicCompletion E, Valued.v x ≤ 1 ↔ x ∈ Formalism.UG.Ov E w := fun x =>
    (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 E) (K := E) (v := w)).symm
  let N : Matrix (Fin n) (Fin n) (Formalism.UG.Ov E w) := fun i j => ⟨_, (hmem _).1 (h1 i j)⟩
  let N' : Matrix (Fin n) (Fin n) (Formalism.UG.Ov E w) := fun i j => ⟨_, (hmem _).1 (h2 i j)⟩
  have hinj : Function.Injective ((Formalism.UG.Ov E w).subtype.mapMatrix :
      Matrix (Fin n) (Fin n) (Formalism.UG.Ov E w) →+* Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
    intro a b hab
    exact Matrix.ext fun i j => Subtype.ext (congrFun (congrFun hab i) j)
  have hN : (Formalism.UG.Ov E w).subtype.mapMatrix N = (M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
    ext i j; rfl
  have hN' : (Formalism.UG.Ov E w).subtype.mapMatrix N' = ((M⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
    ext i j; rfl
  refine ⟨⟨N, N', hinj ?_, hinj ?_⟩, ?_⟩
  · rw [map_mul, hN, hN', map_one]; exact M.mul_inv
  · rw [map_mul, hN, hN', map_one]; exact M.inv_mul
  · apply Units.ext
    simp only [Formalism.UG.bc, Units.coe_map, MonoidHom.coe_coe]
    exact hN

end GlobalTheory.InertUnitOrb.LatStable

namespace GlobalTheory.InertUnitOrb.LatStable

theorem mem_KGL_of_unitary {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) {n : ℕ} (w : Pl E)
    (hw : ¬ IsSplitAt w) (M : GLw n w) (hM : M ∈ UL n w)
    (h1 : ∀ i j, Valued.v ((M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ 1) :
    M ∈ GlobalTheory.LFun.KGL w (n := n) := by
  have hcj := (GlobalTheory.ConjAtPlace.main E hU w).2.2.1
  rw [UL, if_neg hw] at hM
  have hM' : Formalism.UG.cT (cj w) (M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * 1 *
      (M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = 1 := hM
  have hinv : ((M⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      Formalism.UG.cT (cj w) (M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
    have := congrArg (· * ((M⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E))) hM'
    simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv] at this
    exact this.symm
  refine mem_KGL_of_int w M h1 fun i j => ?_
  rw [hinv]
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
  rw [hcj]
  exact h1 j i

theorem e_mulVec {K F : Type} [Field K] [Field F] (e : K ≃+* F) {n : ℕ} (Q : Matrix (Fin n) (Fin n) F)
    (u : Fin n → K) (i : Fin n) : e ((Q.map e.symm *ᵥ u) i) = (Q *ᵥ fun j => e (u j)) i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

end GlobalTheory.InertUnitOrb.LatStable

namespace GlobalTheory.InertUnitOrb.LatStable

theorem unitLat_stable_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (γ : UL n w), (∀ y, ψ (B.g * y) = ((((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ y) → ∀ q : UL n w, ((∀ y ∈ unitLat e B ψ q, B.g * y ∈ unitLat e B ψ q) ↔ q⁻¹ * γ * q ∈ KL n w) := by
  intro E _ _ _ hU w hw K e _ hint n B ψ γ hg q
  let ψ' : B.A → Fin n → w.adicCompletion E := fun y i => e (ψ y i)
  have hsurj : Function.Surjective ψ' := fun u => ⟨ψ.symm fun i => e.symm (u i), by funext i; simp [ψ']⟩
  set Qi := (((q⁻¹ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hQi
  set Qm := (((q : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hQm
  set Gm := (((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hGm
  set Mm := (((q⁻¹ * γ * q : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hMm'
  have hMm : Mm = Qi * Gm * Qm := rfl
  have hQiQm : Qi * Qm = 1 := by
    rw [hQi, hQm, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
  have hQmQi : Qm * Qi = 1 := by
    rw [hQi, hQm, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]; rfl
  have hmemL : ∀ y, y ∈ unitLat e B ψ q ↔ ∀ i, Valued.v ((Qi *ᵥ ψ' y) i) ≤ 1 := by
    intro y
    show (∀ i, ((Qi.map e.symm) *ᵥ ψ y) i ∈ (algebraMap K.O K.E).range) ↔ _
    refine forall_congr' fun i => ?_
    rw [hint, e_mulVec]
  have hgψ : ∀ y, ψ' (B.g * y) = Gm *ᵥ ψ' y := by
    intro y; funext i
    simp only [ψ']
    rw [hg, e_mulVec]
  have hstab : (∀ y ∈ unitLat e B ψ q, B.g * y ∈ unitLat e B ψ q) ↔
      ∀ v : Fin n → w.adicCompletion E, (∀ i, Valued.v (v i) ≤ 1) → ∀ i, Valued.v ((Mm *ᵥ v) i) ≤ 1 := by
    constructor
    · intro hst v hv
      obtain ⟨y, hy⟩ := hsurj (Qm *ᵥ v)
      have hyL : y ∈ unitLat e B ψ q := (hmemL y).2 (by rw [hy, Matrix.mulVec_mulVec, hQiQm, Matrix.one_mulVec]; exact hv)
      have := (hmemL _).1 (hst y hyL)
      rw [hgψ, hy, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at this
      rw [hMm]; exact this
    · intro h y hy
      rw [hmemL] at hy ⊢
      rw [hgψ]
      have key : Qi *ᵥ (Gm *ᵥ ψ' y) = Mm *ᵥ (Qi *ᵥ ψ' y) := by
        simp only [hMm, Matrix.mulVec_mulVec, Matrix.mul_assoc, hQmQi, Matrix.mul_one]
      rw [key]
      exact h _ hy
  rw [hstab, mulVec_int_iff, KL, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    exact mem_KGL_of_unitary hU w hw _ (q⁻¹ * γ * q).2 h
  · rintro ⟨N, hN⟩ i j
    have hmem : ∀ x : w.adicCompletion E, Valued.v x ≤ 1 ↔ x ∈ Formalism.UG.Ov E w := fun x =>
      (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 E) (K := E) (v := w)).symm
    rw [hmem, hMm', ← hN]
    exact ((N : Matrix (Fin n) (Fin n) (Formalism.UG.Ov E w)) i j).2

end GlobalTheory.InertUnitOrb.LatStable
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLatticeStableIffConjIntegralStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitLattice_stable_iff_conj_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (γ : UL n w), (∀ y, ψ (B.g * y) = ((((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ y) → ∀ q : UL n w, ((∀ y ∈ unitLat e B ψ q, B.g * y ∈ unitLat e B ψ q) ↔ q⁻¹ * γ * q ∈ KL n w) := by
  first | exact @GlobalTheory.InertUnitOrb.LatStable.unitLat_stable_iff | exact GlobalTheory.InertUnitOrb.LatStable.unitLat_stable_iff | (intros; apply GlobalTheory.InertUnitOrb.LatStable.unitLat_stable_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarEqOfWeilPairingEqPrincipalCMTriple
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarEqOfWeilPairingEqPrincipalCMTriple
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

noncomputable section

namespace GlobalTheory.TwistScalarUnique

def coordMul {E : Type} [Field E] {g : ℕ} (ty : Fin g → (E →+* ℂ)) (s : E) : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) where
  toFun z k := ty k s * z k
  map_add' z w := by funext k; simp [mul_add]
  map_smul' c z := by funext k; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem cmHost_sqrtNegDisc_re_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) : H.rt0.re = 0 := by
  have h2 := congrArg Complex.re H.sqrt_neg_disc_sq
  have h3 := congrArg Complex.im H.sqrt_neg_disc_sq
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
    Complex.natCast_im] at h2 h3
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  by_contra hne
  have him : H.rt0.im = 0 := by
    have : H.rt0.re * H.rt0.im = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left hne
  rw [him] at h2
  nlinarith [mul_self_nonneg H.rt0.re]

theorem exists_embedding {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    (∃ τ : E →+* ℂ, τ (H.rt : E) = H.rt0) ∧ ∃ τ : E →+* ℂ, τ (H.rt : E) ≠ H.rt0 := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := ⟨(IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom⟩
  have hre := cmHost_sqrtNegDisc_re_eq_zero H
  have hd : (H.d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 H.d_prime.ne_zero
  have hr0 : H.rt0 ≠ 0 := fun h0 => hd (by have := H.sqrt_neg_disc_sq; rw [h0] at this; linear_combination this)
  have hne : H.rt0 ≠ -H.rt0 := fun h => hr0 (by linear_combination h / 2)
  have hconj : starRingEnd ℂ H.rt0 = -H.rt0 := by apply Complex.ext <;> simp [hre]
  have h1 : τ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
    have := congrArg (fun a : 𝓞 E => τ (a : E)) H.rt_sq
    rw [H.sqrt_neg_disc_sq]; simpa using this
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · refine ⟨⟨τ, h⟩, (starRingEnd ℂ).comp τ, ?_⟩
    show starRingEnd ℂ (τ (H.rt : E)) ≠ H.rt0
    rw [h, hconj]; exact fun e => hne e.symm
  · refine ⟨⟨(starRingEnd ℂ).comp τ, ?_⟩, τ, ?_⟩
    · show starRingEnd ℂ (τ (H.rt : E)) = H.rt0
      rw [h, map_neg, hconj, neg_neg]
    · rw [h]; exact fun e => hne e.symm

theorem nonempty_of_isTypeFn {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {p q g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (hty : IsTypeFn H p q ty) (hpq : p + q = 1) : Nonempty (Fin g) := by
  obtain ⟨⟨τ₁, h₁⟩, τ₂, h₂⟩ := exists_embedding H
  rcases Nat.add_eq_one_iff.1 hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have h := (hty τ₂).2 h₂
    obtain ⟨⟨i, -⟩⟩ : Nonempty {i // ty i = τ₂} := (Nat.card_pos_iff.1 (by rw [h]; norm_num)).1
    exact ⟨i⟩
  · have h := (hty τ₁).1 h₁
    obtain ⟨⟨i, -⟩⟩ : Nonempty {i // ty i = τ₁} := (Nat.card_pos_iff.1 (by rw [h]; norm_num)).1
    exact ⟨i⟩

theorem eq_of_weilEq_complex {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (A : PAT H (Sp ℂ))
    {p q : ℕ} (hpq : p + q = 1)
    (hdet : ∀ τ : 𝓞 E →+* ℂ, (τ H.rt = H.rt0 → LieMult A.t.act (𝟙 (Sp ℂ)) τ p) ∧
      (τ H.rt ≠ H.rt0 → LieMult A.t.act (𝟙 (Sp ℂ)) τ q)) (s s' : 𝓞 E)
    (h : WeilEq A.t.PP.L (A.t.act.act s) (𝟙 _) A.t.PP.L (A.t.act.act s') (𝟙 _) (𝟙 (Sp ℂ))) : s = s' := by
  have hT : ThetaUnifAV := thetaUnifAV_all
  have hL : Out.Laws := abelianSchemeLaws_all.1
  obtain ⟨g, ty, hty⟩ := AllClasses.exists_isTypeFn H p q
  obtain ⟨u, HA, χA, -, hA, -⟩ := PureType.exists_isThetaUnif hT A.pol
  obtain ⟨D, Pe, F, -, -, -, -, -, hact⟩ := PureTriple.exists_datum_period hT hL A hty hdet u hA
  let G : 𝓞 E → (Fin A.pol.g → ℂ) →ₗ[ℂ] (Fin A.pol.g → ℂ) := fun s =>
    F.toLinearMap ∘ₗ coordMul ty (s : E) ∘ₗ F.symm.toLinearMap
  have hG : ∀ s z, u.ex (G s z) = u.ex z ≫ A.t.act.act s := fun s z => by
    have e := hact s (F.symm z)
    rw [F.apply_symm_apply] at e
    exact e
  have key := (weilEq_iff_hermForm_eq hT hL A.pol A.pol A.pol A.pol u u u u HA HA χA χA hA hA
    (A.t.act.act s) (𝟙 _) (A.t.act.act s') (𝟙 _) (G s) LinearMap.id (G s') LinearMap.id (hG s)
    (fun _ => (Category.comp_id _).symm) (hG s') (fun _ => (Category.comp_id _).symm)).1 h
  have hGeq : ∀ z, G s z = G s' z := by
    intro z
    by_contra hne
    have hpos := hA.2.1 (G s z - G s' z) (sub_ne_zero.2 hne)
    have e := key z (G s z - G s' z)
    simp only [hermForm, LinearMap.id_apply] at e
    rw [sub_dotProduct, e, sub_self] at hpos
    simp at hpos
  obtain ⟨k⟩ := nonempty_of_isTypeFn H hty hpq
  have e1 := hGeq (F fun _ => 1)
  simp only [G, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at e1
  have e2 := congrFun (F.injective e1) k
  have e3 : ty k (s : E) = ty k (s' : E) := by simpa [coordMul] using e2
  exact RingOfIntegers.ext ((ty k).injective e3)

theorem eq_of_weilEq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
    [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (A : PAT H (Sp (𝓞 K))), ρ ^ 2 = -(H.d : 𝓞 K) →
    HasType H A.t.act ρ 1 0 → ∀ s s' : 𝓞 E,
    WeilEq A.t.PP.L (A.t.act.act s) (𝟙 _) A.t.PP.L (A.t.act.act s') (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
    s = s' := by
  intro E _ _ _ H K _ _ ρ σ₁ A hρ hA s s' h
  have hβi : Function.Injective (σ₁.comp (algebraMap (𝓞 K) K)) :=
    σ₁.injective.comp (IsFractionRing.injective (𝓞 K) K)
  obtain ⟨⟨A', mA, -⟩, hA2⟩ := GlobalTheory.LamT.pat_pullback E H (𝓞 K) ℂ (σ₁.comp (algebraMap (𝓞 K) K)) A
  obtain ⟨-, -, wA, hwA⟩ := hA2 A' mA inferInstance
  have hlie : ∀ (τ : 𝓞 E →+* ℂ) (n : ℕ), LieMult A'.t.act (𝟙 (Sp ℂ)) τ n ↔
      LieMult A.t.act (spMap (σ₁.comp (algebraMap (𝓞 K) K))) τ n := fun τ n => by
    have := GlobalTheory.lieMult_iff_of_isGrpPullback mA.cart A'.t.act A.t.act mA.act (𝟙 (Sp ℂ)) τ n
    rwa [Category.id_comp] at this
  have hweil : WeilEq A'.t.PP.L (A'.t.act.act s) (𝟙 _) A'.t.PP.L (A'.t.act.act s') (𝟙 _) (𝟙 (Sp ℂ)) := by
    refine (GlobalTheory.PairingFibre.weilEq_iff (f₂ := 𝟙 _) (g₂ := 𝟙 _) (f₂' := 𝟙 _) (g₂' := 𝟙 _) mA.cart mA.cart
      mA.cart mA.cart A.t.PP.isLB A.t.PP.isLB A'.t.PP.isLB A'.t.PP.isLB ⟨wA, hwA.1⟩ ⟨wA, hwA.1⟩ (mA.act s)
      (by simp) (mA.act s') (by simp) (𝟙 (Sp ℂ))).2 ?_
    rwa [Category.id_comp]
  have hT := hA ℂ (σ₁.comp (algebraMap (𝓞 K) K)) hβi
  have hd0 : (H.d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 H.d_prime.ne_zero
  have hr0 : H.rt0 ≠ 0 := fun h0 => hd0 (by have := H.sqrt_neg_disc_sq; rw [h0] at this; linear_combination this)
  have hsq : ∀ x : ℂ, x ^ 2 = -(H.d : ℂ) → x = H.rt0 ∨ x = -H.rt0 := fun x hx =>
    sq_eq_sq_iff_eq_or_eq_neg.1 (hx.trans H.sqrt_neg_disc_sq.symm)
  have hβρ : (σ₁.comp (algebraMap (𝓞 K) K)) ρ ^ 2 = -(H.d : ℂ) := by
    rw [← map_pow, hρ]; simp
  have hτ : ∀ τ : 𝓞 E →+* ℂ, τ H.rt ^ 2 = -(H.d : ℂ) := fun τ => by
    rw [← map_pow, H.rt_sq]; simp
  have hne : H.rt0 ≠ -H.rt0 := fun h => hr0 (by linear_combination h / 2)
  rcases hsq _ hβρ with hc | hc
  · refine eq_of_weilEq_complex H A' (p := 1) (q := 0) rfl (fun τ => ⟨fun ht => ?_, fun ht => ?_⟩) s s' hweil
    · exact (hlie τ 1).2 ((hT τ).1 (ht.trans hc.symm))
    · exact (hlie τ 0).2 ((hT τ).2 (fun h => ht (h.trans hc)))
  · refine eq_of_weilEq_complex H A' (p := 0) (q := 1) rfl (fun τ => ⟨fun ht => ?_, fun ht => ?_⟩) s s' hweil
    · exact (hlie τ 0).2 ((hT τ).2 (fun h => hne (ht.symm.trans (h.trans hc))))
    · rcases hsq _ (hτ τ) with h | h
      · exact absurd h ht
      · exact (hlie τ 1).2 ((hT τ).1 (h.trans hc.symm))

end GlobalTheory.TwistScalarUnique
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarEqOfWeilPairingEqPrincipalCMTripleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalar_eq_of_weilPairing_eq_principalCMTriple : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
    [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (A : PAT H (Sp (𝓞 K))), ρ ^ 2 = -(H.d : 𝓞 K) →
    HasType H A.t.act ρ 1 0 → ∀ s s' : 𝓞 E,
    WeilEq A.t.PP.L (A.t.act.act s) (𝟙 _) A.t.PP.L (A.t.act.act s') (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
    s = s' := by
  first | exact @GlobalTheory.TwistScalarUnique.eq_of_weilEq | exact GlobalTheory.TwistScalarUnique.eq_of_weilEq | (intros; apply GlobalTheory.TwistScalarUnique.eq_of_weilEq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongOneInvMulIff
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.CongReps

variable (D : D7) (𝔪 : Ideal (𝓞 D.host.E))


variable {D 𝔪} in
theorem mul_mem_hatId {t x : AE D} (ht : t ∈ OhE D) (hx : x ∈ hatId D 𝔪) : t * x ∈ hatId D 𝔪 := by
  unfold hatId at hx ⊢
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨b, hb, t * s, mul_mem ht hs, by ring⟩
  | zero => rw [mul_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
  | neg y _ hy => rw [mul_neg]; exact neg_mem hy


variable {D 𝔪} in
theorem inc_sub_mem {r r' : 𝓞 D.host.E} (h : r - r' ∈ 𝔪) :
    inc D (r : D.host.E) - inc D (r' : D.host.E) ∈ hatId D 𝔪 :=
  AddSubgroup.subset_closure ⟨r - r', h, 1, one_mem _, by push_cast; rw [map_sub, mul_one]⟩


variable {D 𝔪} in
theorem exists_rep (h𝔪 : 𝔪 ≠ ⊥) {s : AE D} (hs : s ∈ OhE D) :
    ∃ r : 𝓞 D.host.E, s - inc D (r : D.host.E) ∈ hatId D 𝔪 := by
  have hn : 0 < Ideal.absNorm 𝔪 := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 h𝔪)
  obtain ⟨r, hr, w, hw, e⟩ := GlobalTheory.HeckeVal.exists_approx D _ hn s hs
  refine ⟨⟨r, hr⟩, AddSubgroup.subset_closure ⟨(Ideal.absNorm 𝔪 : 𝓞 D.host.E), Ideal.absNorm_mem 𝔪, w, hw, ?_⟩⟩
  rw [e]
  change inc D r + (Ideal.absNorm 𝔪 : AE D) * w - inc D r = inc D (((Ideal.absNorm 𝔪 : ℕ) : 𝓞 D.host.E) : D.host.E) * w
  simp

def congRel (N : ℕ) : Setoid {k : GA D N // k ∈ intG D N} where
  r k k' := ∀ i j, ((k.1 : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j -
    ((k'.1 : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ hatId D 𝔪
  iseqv := by
    refine ⟨fun k i j => by rw [sub_self]; exact zero_mem _, fun h i j => by rw [← neg_sub]; exact neg_mem (h i j),
      fun h h' i j => ?_⟩
    have := add_mem (h i j) (h' i j)
    rwa [sub_add_sub_cancel] at this


variable {D 𝔪} in
theorem congOne_inv_mul_iff {N : ℕ} {r : GA D N} (hr : r ∈ intG D N) (k : GA D N) :
    CongOne D 𝔪 (r⁻¹ * k) ↔ ∀ i j, ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j -
      ((r : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ hatId D 𝔪 := by
  have hI := (mem_intG r).1 hr
  set Rm : Matrix (Fin N) (Fin N) (AE D) := ((r : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))
  set Ri : Matrix (Fin N) (Fin N) (AE D) := (((r : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))
  set K : Matrix (Fin N) (Fin N) (AE D) := ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))
  have e0 : (((r⁻¹ * k : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) = Ri * K := by
    simp [Rm, Ri, K]
  have e1 : Ri * K - 1 = Ri * (K - Rm) := by
    rw [Matrix.mul_sub]
    congr 1
    exact (Units.inv_mul (r : GL (Fin N) (AE D))).symm
  have e2 : K - Rm = Rm * (Ri * K - 1) := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, Matrix.mul_one]
    congr 1
    rw [show Rm * Ri = 1 from Units.mul_inv (r : GL (Fin N) (AE D)), Matrix.one_mul]
  unfold CongOne
  rw [e0]
  constructor
  · intro h i j
    rw [← Matrix.sub_apply, e2, Matrix.mul_apply]
    exact sum_mem fun l _ => mul_mem_hatId (hI i l).1 (h l j)
  · intro h i j
    rw [e1, Matrix.mul_apply]
    exact sum_mem fun l _ => mul_mem_hatId (hI i l).2 (by rw [Matrix.sub_apply]; exact h l j)


open Classical in
def red (x : AE D) : 𝓞 D.host.E ⧸ 𝔪 :=
  if h : ∃ r : 𝓞 D.host.E, x - inc D (r : D.host.E) ∈ hatId D 𝔪 then Ideal.Quotient.mk 𝔪 h.choose else 0


variable {D 𝔪} in
theorem sub_mem_of_red_eq (h𝔪 : 𝔪 ≠ ⊥) {x y : AE D} (hx : x ∈ OhE D) (hy : y ∈ OhE D) (h : red D 𝔪 x = red D 𝔪 y) :
    x - y ∈ hatId D 𝔪 := by
  have ex := exists_rep h𝔪 hx
  have ey := exists_rep h𝔪 hy
  unfold red at h
  rw [dite_eq_left ex, dite_eq_left ey, Ideal.Quotient.eq] at h
  have := add_mem (sub_mem ex.choose_spec ey.choose_spec) (inc_sub_mem h)
  convert this using 1
  ring

theorem finite_congRel (h𝔪 : 𝔪 ≠ ⊥) (N : ℕ) : Finite (Quotient (congRel D 𝔪 N)) := by
  haveI : Finite (𝓞 D.host.E ⧸ 𝔪) := Ideal.finiteQuotientOfFreeOfNeBot 𝔪 h𝔪
  let φ : {k : GA D N // k ∈ intG D N} → Fin N → Fin N → 𝓞 D.host.E ⧸ 𝔪 := fun k i j =>
    red D 𝔪 (((k.1 : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j)
  let g : {q // ∃ k, φ k = q} → Quotient (congRel D 𝔪 N) := fun q => Quotient.mk _ q.2.choose
  refine Finite.of_surjective g fun c => ?_
  induction c using Quotient.inductionOn with
  | h k =>
    refine ⟨⟨φ k, k, rfl⟩, Quotient.sound fun i j => ?_⟩
    have hq : φ (⟨φ k, k, rfl⟩ : {q // ∃ k, φ k = q}).2.choose = φ k := (⟨φ k, k, rfl⟩ : {q // ∃ k, φ k = q}).2.choose_spec
    set k' := (⟨φ k, k, rfl⟩ : {q // ∃ k, φ k = q}).2.choose
    exact sub_mem_of_red_eq h𝔪 (((mem_intG k'.1).1 k'.2) i j).1 (((mem_intG k.1).1 k.2) i j).1
      (congrFun (congrFun hq i) j)

theorem exists_reps : ∀ (D : D7) (N : ℕ) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∃ R : Finset (GA D N),
    (∀ r ∈ R, r ∈ intG D N) ∧ ∀ k ∈ intG D N, ∃! r, r ∈ R ∧ CongOne D 𝔪 (r⁻¹ * k) := by
  intro D N 𝔪 h𝔪
  haveI := finite_congRel D 𝔪 h𝔪 N
  haveI : Fintype (Quotient (congRel D 𝔪 N)) := Fintype.ofFinite _
  classical
  refine ⟨Finset.univ.image fun c : Quotient (congRel D 𝔪 N) => c.out.1, ?_, ?_⟩
  · intro r hr
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hr
    exact c.out.2
  · intro k hk
    let c := Quotient.mk (congRel D 𝔪 N) ⟨k, hk⟩
    refine ⟨c.out.1, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ c), ?_⟩, ?_⟩
    · rw [congOne_inv_mul_iff c.out.2]
      have := Quotient.exact (Quotient.out_eq c)
      intro i j
      have h := (congRel D 𝔪 N).iseqv.symm this i j
      exact h
    · rintro r ⟨hr, hc⟩
      obtain ⟨c', -, rfl⟩ := Finset.mem_image.1 hr
      rw [congOne_inv_mul_iff c'.out.2] at hc
      have h1 : (congRel D 𝔪 N) c'.out ⟨k, hk⟩ := (congRel D 𝔪 N).iseqv.symm hc
      have h3 : c' = c := by
        rw [← Quotient.out_eq c']
        exact Quotient.sound h1
      rw [h3]

end GlobalTheory.CongReps

end
end
