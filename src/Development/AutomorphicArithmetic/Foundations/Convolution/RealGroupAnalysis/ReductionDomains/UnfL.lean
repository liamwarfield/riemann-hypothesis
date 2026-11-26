module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.KkCpt
public import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.GJGlobalModulus
public import GroundTheory.AutomorphicForms.GL2Classical.GrowthReduction

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.UnfL
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.CosetSum
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.cosetSum :
    ∀ (F : Type) [Field F] [NumberField F] (M₀ : Meas F) (σ) (β u : G1 F → ℝ≥0∞), M.RowSec (F := F) σ → M.NWt β → Measurable u → (∀ (ξ : F) g, u (nU (rt ξ) * g) = u g) → ∫⁻ g, u g * β g ∂M₀.μ = ∫⁻ g in M₀.D, ∑' r, u (ratS F (σ r) * g) ∂M₀.μ := by
  intro F _ _ M₀ σ β u hσ hβ hu hinv
  have hc := (UpperTheory.ConvolutionTheory.R2.M.rowCosets F).2 σ hσ
  haveI := M₀.haar
  let e : ({r : Fin 2 → F // r ≠ 0} × F) → Gam F := fun p =>
    ⟨nU (rt p.2) * ratS F (σ p.1), (Gam F).mul_mem (M.nU_rt_mem _) ⟨_, rfl⟩⟩
  have he : Function.Bijective e := by
    constructor
    · intro p q h
      obtain ⟨p0, _, hp⟩ := hc (e p)
      exact (hp p rfl).trans (hp q (congrArg Subtype.val h)).symm
    · intro γ
      obtain ⟨p, hp, _⟩ := hc γ
      exact ⟨p, Subtype.ext hp.symm⟩
  have key : ∀ g : G1 F, ∑' γ : Gam F, u (γ • g) * β (γ • g) = ∑' r, u (ratS F (σ r) * g) := by
    intro g
    rw [← (Equiv.ofBijective e he).tsum_eq, ENNReal.tsum_prod']
    refine tsum_congr fun r => ?_
    have h1 : ∀ ξ : F, u ((Equiv.ofBijective e he (r, ξ)) • g) * β ((Equiv.ofBijective e he (r, ξ)) • g)
        = u (ratS F (σ r) * g) * β (nU (rt ξ) * (ratS F (σ r) * g)) := by
      intro ξ
      have h2 : (Equiv.ofBijective e he (r, ξ)) • g = nU (rt ξ) * (ratS F (σ r) * g) := by
        change (nU (rt ξ) * ratS F (σ r)) * g = _
        rw [mul_assoc]
      rw [h2, hinv]
    simp_rw [h1]
    rw [ENNReal.tsum_mul_left, hβ.2, mul_one]
  have hmeas : ∀ γ : Gam F, Measurable fun g : G1 F => u (γ • g) * β (γ • g) := fun γ =>
    (hu.mul hβ.1).comp (measurable_const_smul γ)
  rw [M₀.fund.lintegral_eq_tsum'', ← lintegral_tsum fun γ => (hmeas γ).aemeasurable]
  exact lintegral_congr key
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.OneVar
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

private theorem oneVar {F : Type} [Field F] [NumberField F] (f w : A F → ℝ≥0∞) (hf : Measurable f) (hw : Measurable w)
    (hinv : ∀ (ξ : F) b, f (rt ξ + b) = f b) (hsum : ∀ b, ∑' ξ : F, w (rt ξ + b) = 1) :
    ∫⁻ b, f b * w b ∂(adeleMeasure F) = ∫⁻ b in fundamentalSet F, f b ∂(adeleMeasure F) := by
  have hD := isAddFundamentalDomain_fundamentalSet F
  let φ : F → AdeleRing.principalSubgroup (𝓞 F) F := fun ξ => ⟨rt ξ, ξ, rfl⟩
  have hφ : Function.Bijective φ := by
    constructor
    · intro x y h
      exact AdeleRing.algebraMap_injective (𝓞 F) F (congrArg Subtype.val h)
    · rintro ⟨_, ξ, rfl⟩
      exact ⟨ξ, rfl⟩
  haveI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  haveI : Countable (AdeleRing.principalSubgroup (𝓞 F) F) := hφ.2.countable
  rw [hD.lintegral_eq_tsum'' (fun b => f b * w b), ← lintegral_tsum]
  · refine lintegral_congr fun x => ?_
    rw [← (Equiv.ofBijective φ hφ).tsum_eq]
    have h1 : ∀ ξ : F, f ((Equiv.ofBijective φ hφ ξ) +ᵥ x) * w ((Equiv.ofBijective φ hφ ξ) +ᵥ x) = f x * w (rt ξ + x) := by
      intro ξ
      change f (rt ξ + x) * w (rt ξ + x) = _
      rw [hinv]
    simp only [h1]
    rw [ENNReal.tsum_mul_left, hsum, mul_one]
  · intro γ
    exact ((hf.mul hw).comp (measurable_const_add (γ : A F))).aemeasurable

theorem UpperTheory.ConvolutionTheory.R2.M.wtInt :
    ∀ (F : Type) [Field F] [NumberField F] (M₀ : Meas F) (β u : G1 F → ℝ≥0∞), M.NWt β → Measurable u → (∀ (ξ : F) g, u (nU (rt ξ) * g) = u g) → ∫⁻ g, u g * β g ∂M₀.μ = M.J0 M₀ fun g => ∫⁻ b in fundamentalSet F, u (nU b * g) ∂(adeleMeasure F) := by
  intro F _ _ M₀ β u hβ hu hinv
  haveI := M₀.prob
  have hnU : Measurable (nU : A F → G1 F) := M.continuous_nU.measurable
  have hmD : Measurable (mD : IdeleGroup F → G1 F) := M.continuous_mD.measurable
  have hy : Measurable fun p : IdeleGroup F × G1 F => mD p.1 * p.2 :=
    (hmD.comp measurable_fst).mul measurable_snd
  have hI : Measurable fun p : IdeleGroup F × G1 F =>
      ∫⁻ b in fundamentalSet F, u (nU b * (mD p.1 * p.2)) ∂(adeleMeasure F) :=
    Measurable.lintegral_prod_right' (ν := (adeleMeasure F).restrict (fundamentalSet F))
      (f := fun q : (IdeleGroup F × G1 F) × A F => u (nU q.2 * (mD q.1.1 * q.1.2)))
      (hu.comp ((hnU.comp measurable_snd).mul (hy.comp measurable_fst)))
  have hJ : Measurable fun p : IdeleGroup F × G1 F =>
      M.wt p.1 * ∫⁻ b in fundamentalSet F, u (nU b * (mD p.1 * p.2)) ∂(adeleMeasure F) :=
    (M.measurable_wt.comp measurable_fst).mul hI
  rw [M₀.iwasawa (fun g => u g * β g) (hu.mul hβ.1), M.J0, Meas.ν, lintegral_prod_symm _ hJ.aemeasurable]
  refine lintegral_congr fun k => lintegral_congr fun a => ?_
  have hsh : ∀ (ξ : F) (b : A F) (y : G1 F), nU (rt ξ + b) * y = nU (rt ξ) * (nU b * y) := by
    intro ξ b y
    rw [M.nU_add, mul_assoc]
  have hmy : ∀ v : G1 F → ℝ≥0∞, Measurable v → Measurable fun b : A F => v (nU b * (mD a * k)) :=
    fun v hv => hv.comp (hnU.mul_const _)
  have key := oneVar (fun b => u (nU b * (mD a * k))) (fun b => β (nU b * (mD a * k)))
    (hmy u hu) (hmy β hβ.1) (fun ξ b => by simp only [hsh, hinv])
    (fun b => by simp only [hsh]; exact hβ.2 _)
  simp only [mul_assoc (nU _) (mD a) k]
  rw [lintegral_mul_const (f := fun b => u (nU b * (mD a * k)) * β (nU b * (mD a * k))) _
    ((hmy u hu).mul (hmy β hβ.1)), key, mul_comm]
  rfl
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.unfL :
    ∀ (F : Type) [Field F] [NumberField F] (M₀ : Meas F) (σ) (u : G1 F → ℝ≥0∞), M.RowSec (F := F) σ → Measurable u → (∀ (ξ : F) g, u (nU (rt ξ) * g) = u g) → ∫⁻ g in M₀.D, ∑' r, u (ratS F (σ r) * g) ∂M₀.μ = M.J0 M₀ fun g => ∫⁻ b in fundamentalSet F, u (nU b * g) ∂(adeleMeasure F) := by
  intro F _ _ M₀ σ u hσ hu hinv
  obtain ⟨β, hβ⟩ := M.wtEx F
  exact (M.cosetSum F M₀ σ β u hσ hβ hu hinv).symm.trans (M.wtInt F M₀ β u hβ hu hinv)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.LintegralUnipotentQuotientRightInvariant
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.lintegral_unipotent_quotient_right_invariant :
    ∀ (F : Type) [Field F] [NumberField F] (M₀ : Meas F) (u : G1 F → ℝ≥0∞), Measurable u → (∀ b g, u (nU b * g) = u g) → ∀ g₀, (M.J0 M₀ fun g => u (g * g₀)) = M.J0 M₀ u := by
  intro F _ _ M₀ u hu hinv g₀
  obtain ⟨β, hβ⟩ := UpperTheory.ConvolutionTheory.R2.M.wtEx F
  haveI := M₀.right
  have hone := UpperTheory.ConvolutionTheory.R2.M.wtOne F β hβ
  have hm : ∀ h : G1 F, Measurable fun g : G1 F => g * h := fun h => measurable_mul_const h
  have h1 := UpperTheory.ConvolutionTheory.R2.M.wtA F M₀ β (fun g => u (g * g₀)) 1 hβ.1 hone (hu.comp (hm g₀))
    (fun b g => by rw [mul_assoc, hinv])
  have h2 := UpperTheory.ConvolutionTheory.R2.M.wtA F M₀ (fun g => β (g * g₀⁻¹)) u 1 (hβ.1.comp (hm g₀⁻¹))
    (fun g => by simpa only [mul_assoc] using hone (g * g₀⁻¹)) hu hinv
  have h3 := lintegral_mul_right_eq_self (μ := M₀.μ) (fun g => u g * β (g * g₀⁻¹)) g₀
  simp only [mul_inv_cancel_right] at h3
  rw [one_mul] at h1 h2
  rw [← h1, ← h2, h3]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.FromGL
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.InfNorm
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

namespace UpperTheory.ConvolutionTheory.R2.M

variable {F : Type} [Field F] [NumberField F]

private theorem int_det {R : Type*} [CommRing R] (S : Subring R) {m : Matrix (Fin 2) (Fin 2) R}
    (h : ∀ i j, m i j ∈ S) : m.det ∈ S := by
  rw [Matrix.det_fin_two]
  exact S.sub_mem (S.mul_mem (h 0 0) (h 1 1)) (S.mul_mem (h 0 1) (h 1 0))

private theorem fin_int {k : GL (Fin 2) (A F)} (hk : k ∈ Reduction.maxCompact (K := F) (n := 2))
    (v : HeightOneSpectrum (𝓞 F)) :
    (((Matrix.GeneralLinearGroup.det k : (A F)ˣ) : A F)).2 v ∈
      (ValuativeRel.valuation (v.adicCompletion F)).integer := by
  have h := ((GLnLocal.mem_integralGL_iff _ _).1 (hk.2 v)).1
  have e := GL2Classical.det_finAt_eq v k
  have e' : (((Matrix.GeneralLinearGroup.det k : (A F)ˣ) : A F)).2 v =
      ((Reduction.finAt v k : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det := e
  rw [e']
  exact int_det _ h

private theorem inf_norm {k : GL (Fin 2) (A F)} (hk : k ∈ Reduction.maxCompact (K := F) (n := 2))
    (w : InfinitePlace F) : ‖(((Matrix.GeneralLinearGroup.det k : (A F)ˣ) : A F)).1 w‖ = 1 := by
  have e := GL2Classical.det_infAt_eq w k
  have e' : (((Matrix.GeneralLinearGroup.det k : (A F)ˣ) : A F)).1 w =
      ((Reduction.infAt w k : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion).det := e
  rw [e']
  exact Reduction.norm_det_infAt_of_mem_maxCompact hk w

private theorem dM_mem (t : (A F)ˣ) (h1 : ∀ w : InfinitePlace F, ‖((t : A F)).1 w‖ = 1)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 F), ((t : A F)).2 v ∈
      (ValuativeRel.valuation (v.adicCompletion F)).integer)
    (h3 : ∀ v : HeightOneSpectrum (𝓞 F), (((t⁻¹ : (A F)ˣ) : A F)).2 v ∈
      (ValuativeRel.valuation (v.adicCompletion F)).integer) :
    dM t ∈ Reduction.maxCompact (K := F) (n := 2) := by
  refine ⟨fun w => ?_, fun v => ?_⟩
  · intro y
    have key : Reduction.euclidNorm (y ᵥ* ((Reduction.infAt w (dM t) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion)) ^ 2 = Reduction.euclidNorm y ^ 2 := by
      rw [Reduction.euclidNorm_sq, Reduction.euclidNorm_sq, Fin.sum_univ_two, Fin.sum_univ_two]
      have a0 : (y ᵥ* ((Reduction.infAt w (dM t) : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion)) 0 = y 0 := by
        simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, dM]
        exact Or.inr rfl
      have a1 : (y ᵥ* ((Reduction.infAt w (dM t) : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion)) 1 = y 1 * ((t : A F)).1 w := by
        simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, dM]
        exact Or.inr rfl
      rw [a0, a1, norm_mul, h1 w, mul_one]
    exact (sq_eq_sq₀ (Reduction.euclidNorm_nonneg _) (Reduction.euclidNorm_nonneg _)).1 key
  · rw [GLnLocal.mem_integralGL_iff, ← Reduction.finAt_inv]
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · fin_cases i <;> fin_cases j <;> simp [dM, h2 v] <;> change (0 : v.adicCompletion F) ∈ _ <;> exact Subring.zero_mem _
    · fin_cases i <;> fin_cases j <;> simp [dM, h3 v] <;> change (0 : v.adicCompletion F) ∈ _ <;> exact Subring.zero_mem _

end UpperTheory.ConvolutionTheory.R2.M

theorem UpperTheory.ConvolutionTheory.R2.M.detK :
    ∀ (F : Type) [Field F] [NumberField F], ∀ k ∈ Reduction.maxCompact (K := F) (n := 2), dM (Matrix.GeneralLinearGroup.det k) ∈ Reduction.maxCompact (K := F) (n := 2) ∧ ab (Matrix.GeneralLinearGroup.det k) = 1 := by
  intro F _ _ k hk
  refine ⟨dM_mem _ (inf_norm hk) (fin_int hk) fun v => ?_, ?_⟩
  · have := fin_int (inv_mem hk) v
    rwa [map_inv] at this
  · have := GJGlobal.Modulus.ideleModule_det_of_mem_maxCompact' hk
    simp [ab, this]
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.fromGL :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ∀ (g : G1 F), ∀ b ∈ Reduction.adelicBorel (K := F) (n := 2), ∀ k ∈ Reduction.maxCompact (K := F) (n := 2), gl g = b * k → ∃ (x : A F) (a : (A F)ˣ), ∃ k' ∈ KK F, g = nU x * mD a * k' ∧ (a : A F) = (b : Matrix (Fin 2) (Fin 2) (A F)) 0 0 ∧ Reduction.adeleAbs ((b : Matrix (Fin 2) (Fin 2) (A F)) 1 1) = (ab a)⁻¹ := by
  intro F _ _ _ g b hb k hk hg
  obtain ⟨hdk, hab⟩ := M.detK F k hk
  set t := Matrix.GeneralLinearGroup.det k with ht
  have hk' : (dM t)⁻¹ * k ∈ Reduction.maxCompact (K := F) (n := 2) := mul_mem (inv_mem hdk) hk
  have hd : Matrix.GeneralLinearGroup.det (dM t) = t := by
    refine Units.ext ?_
    simp [dM, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  have hdet : Matrix.GeneralLinearGroup.det ((dM t)⁻¹ * k) = 1 := by
    rw [map_mul, map_inv, hd, ← ht, inv_mul_cancel]
  let s : G1 F := ⟨((dM t)⁻¹ * k).val, by
    have h1 := congrArg Units.val hdet
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using h1⟩
  have hs : gl s = (dM t)⁻¹ * k := Units.ext rfl
  have hsK : s ∈ KK F := by
    rw [(M.kkCpt F).1]
    show gl s ∈ Reduction.maxCompact (K := F) (n := 2)
    rw [hs]
    exact hk'
  have hc : gl (g * s⁻¹) = b * dM t := by
    have hm : ∀ x y : G1 F, gl (x * y) = gl x * gl y := fun x y => map_mul _ x y
    have h1 : gl (g * s⁻¹) = gl g * (gl s)⁻¹ := by
      rw [hm, eq_inv_of_mul_eq_one_left (a := gl s⁻¹) (b := gl s) (by rw [← hm, inv_mul_cancel]; exact map_one _)]
    rw [h1, hs, hg]
    group
  have hv : (g * s⁻¹).1 = (b : Matrix (Fin 2) (Fin 2) (A F)) * (dM t).val :=
    congrArg Units.val hc
  have hlow : (b : Matrix (Fin 2) (Fin 2) (A F)) 1 0 = 0 :=
    (Reduction.mem_adelicBorel.1 hb) (show (0 : Fin 2) < 1 by decide)
  have e00 : (g * s⁻¹).1 0 0 = (b : Matrix (Fin 2) (Fin 2) (A F)) 0 0 := by
    rw [hv]; simp [dM, Matrix.mul_apply, Fin.sum_univ_two]
  have e01 : (g * s⁻¹).1 0 1 = (b : Matrix (Fin 2) (Fin 2) (A F)) 0 1 * (t : A F) := by
    rw [hv]; simp [dM, Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : (g * s⁻¹).1 1 0 = 0 := by
    rw [hv]; simp [dM, Matrix.mul_apply, Fin.sum_univ_two, hlow]
  have e11 : (g * s⁻¹).1 1 1 = (b : Matrix (Fin 2) (Fin 2) (A F)) 1 1 * (t : A F) := by
    rw [hv]; simp [dM, Matrix.mul_apply, Fin.sum_univ_two]
  have hdet2 : (b : Matrix (Fin 2) (Fin 2) (A F)) 0 0 * ((b : Matrix (Fin 2) (Fin 2) (A F)) 1 1 * (t : A F)) = 1 := by
    have h1 := (g * s⁻¹).det_coe
    rw [Matrix.det_fin_two, e00, e01, e10, e11, mul_zero, sub_zero] at h1
    exact h1
  let a : (A F)ˣ := (Reduction.isUnit_apply_self_of_mem_adelicBorel hb 0).unit
  have ha : (a : A F) = (b : Matrix (Fin 2) (Fin 2) (A F)) 0 0 := IsUnit.unit_spec _
  have hinv : ((a⁻¹ : (A F)ˣ) : A F) = (b : Matrix (Fin 2) (Fin 2) (A F)) 1 1 * (t : A F) :=
    Units.inv_eq_of_mul_eq_one_right (by rw [ha]; exact hdet2)
  have hh : g * s⁻¹ = nU ((b : Matrix (Fin 2) (Fin 2) (A F)) 0 1 * (t : A F) * (a : A F)) * mD a := by
    refine Subtype.ext ?_
    rw [M.val_mul (nU _) (mD a)]
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [nU, mD, Matrix.mul_apply, Fin.sum_univ_two, ha] using e00
    · simpa [nU, mD, Matrix.mul_apply, Fin.sum_univ_two, mul_assoc] using e01
    · simpa [nU, mD, Matrix.mul_apply, Fin.sum_univ_two] using e10
    · simpa [nU, mD, Matrix.mul_apply, Fin.sum_univ_two, hinv] using e11
  refine ⟨(b : Matrix (Fin 2) (Fin 2) (A F)) 0 1 * (t : A F) * (a : A F), a, s, hsK, ?_, ha, ?_⟩
  · rw [← hh, inv_mul_cancel_right]
  · have hb11 : (b : Matrix (Fin 2) (Fin 2) (A F)) 1 1 = ((a⁻¹ * t⁻¹ : (A F)ˣ) : A F) := by
      rw [Units.val_mul, hinv, mul_assoc, Units.mul_inv, mul_one]
    rw [hb11, Reduction.adeleAbs_units]
    show ab (a⁻¹ * t⁻¹) = _
    rw [M.ab_mul, M.ab_inv, M.ab_inv, hab, inv_one, mul_one]
end
