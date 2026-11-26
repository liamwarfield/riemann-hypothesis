module

public import GroundTheory.AutomorphicForms.GL2.GJFEDefs

@[expose] public section

section -- merged from GroundTheory.AutomorphicForms.GL2.GJFEInducedChar
section -- merged from GroundTheory.AutomorphicForms.GL2.GJFEInducedInv
noncomputable section

namespace GroundTheory.Automorphic

namespace Measures

namespace LinearChart

open MeasureTheory Measure Set
open scoped NNReal ENNReal Pointwise

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] {ι : Type*} [Fintype ι]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  (C : LinearChart F ι G) (μ₀ : Measure (ι → F)) [μ₀.IsAddHaarMeasure]

theorem map_mul_right_haar_modular (h : G) :
    map (· * h) (C.haar μ₀) = modularCharacter h • C.haar μ₀ := by
  rw [C.map_mul_right_haar μ₀ h, C.modularCharacter_eq h]


include C in
theorem continuous_modularCharacter : Continuous (modularCharacter : G → ℝ≥0) := by
  have : (modularCharacter : G → ℝ≥0) = fun g => C.leftModulus g * (C.rightModulus g)⁻¹ := by
    funext g
    rw [C.modularCharacter_eq, div_eq_mul_inv]
  rw [this]
  exact C.continuous_leftModulus.mul
    (C.continuous_rightModulus.inv₀ fun g => (C.rightModulus_pos g).ne')

include C in
theorem measurable_modularCharacter :
    Measurable fun g : G => ((modularCharacter g : ℝ≥0) : ℝ≥0∞) :=
  (ENNReal.continuous_coe.comp (continuous_modularCharacter C)).measurable

theorem lintegral_mul_right_haar (h : G) {f : G → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f (x * h) ∂C.haar μ₀ = modularCharacter h * ∫⁻ x, f x ∂C.haar μ₀ := by
  rw [← lintegral_map hf (measurable_mul_const h), C.map_mul_right_haar_modular,
    lintegral_smul_measure]
  rfl


include C in
theorem modularCharacter_eq_one_of_mem {V : OpenSubgroup G} (hV : IsCompact (V : Set G)) {v : G}
    (hv : v ∈ V) : modularCharacter v = 1 := by
  obtain ⟨h1, h2⟩ := C.modulus_eq_one_of_mem hV hv
  rw [C.modularCharacter_eq, h1, h2, div_one]

variable [SecondCountableTopology G]

theorem map_inv_withDensity_haar :
    map (·⁻¹) ((C.haar μ₀).withDensity fun x => (modularCharacter x : ℝ≥0∞)) = C.haar μ₀ := by
  set μ := C.haar μ₀ with hμ
  set Δ : G → ℝ≥0∞ := fun x => (modularCharacter x : ℝ≥0∞) with hΔ
  have hΔm : Measurable Δ := (measurable_modularCharacter C)
  set ν := map (·⁻¹) (μ.withDensity Δ) with hνdef
  have hν : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂ν = ∫⁻ x, f x⁻¹ * Δ x ∂μ := by
    intro f hf
    rw [hνdef, lintegral_map hf measurable_inv]
    have := lintegral_withDensity_eq_lintegral_mul μ hΔm (hf.comp measurable_inv)
    simp only [Function.comp_def, Pi.mul_apply] at this
    rw [this]
    congr 1
    funext x
    ring

  have hleft : ∀ g : G, ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ x, f (g * x) ∂ν = ∫⁻ x, f x ∂ν := by
    intro g f hf
    rw [hν (fun x => f (g * x)) (hf.comp (measurable_const_mul g)), hν f hf]
    set L : G → ℝ≥0∞ := fun y => f y⁻¹ * Δ y with hLdef
    have hL : Measurable L := (hf.comp measurable_inv).mul hΔm
    have key : (fun x => f (g * x⁻¹) * Δ x) =
        fun x => (modularCharacter g : ℝ≥0∞) * L (x * g⁻¹) := by
      funext x
      have h1 : (x * g⁻¹)⁻¹ = g * x⁻¹ := by group
      have h2 : Δ x = (modularCharacter (x * g⁻¹) : ℝ≥0∞) * modularCharacter g := by
        rw [hΔ, ← ENNReal.coe_mul, ← map_mul, inv_mul_cancel_right]
      simp only [hLdef, h1, h2]
      ring
    show ∫⁻ x, f (g * x⁻¹) * Δ x ∂μ = ∫⁻ x, L x ∂μ
    rw [key, lintegral_const_mul (f := fun x => L (x * g⁻¹)) _ (hL.comp (measurable_mul_const _)),
      C.lintegral_mul_right_haar μ₀ g⁻¹ hL, ← mul_assoc, ← ENNReal.coe_mul, ← map_mul,
      mul_inv_cancel, map_one, ENNReal.coe_one, one_mul]
  have hinv : ν.IsMulLeftInvariant := ⟨fun g => by
    ext s hs
    rw [map_apply (measurable_const_mul g) hs, ← lintegral_indicator_one hs,
      ← lintegral_indicator_one (measurable_const_mul g hs)]
    exact hleft g (s.indicator 1) (measurable_one.indicator hs)⟩
  have hfin : IsFiniteMeasureOnCompacts ν := ⟨fun K hK => by
    rw [hνdef, map_apply measurable_inv hK.isClosed.measurableSet,
      withDensity_apply _ (measurable_inv hK.isClosed.measurableSet)]
    have hK' : IsCompact ((·⁻¹) ⁻¹' K : Set G) := by
      rw [Set.inv_preimage]
      exact hK.inv
    exact setLIntegral_lt_top_of_isCompact (hK'.measure_lt_top).ne hK'
      (continuous_modularCharacter C)⟩
  have hsmul := isMulLeftInvariant_eq_smul ν μ
  obtain ⟨V, hV⟩ := exists_compactOpenSubgroup (G := G)
  have hVm : MeasurableSet (V : Set G) := V.isOpen.measurableSet
  have hVinv : ((·⁻¹) ⁻¹' (V : Set G) : Set G) = V := by
    ext x
    simp
  have hνV : ν V = μ V := by
    rw [hνdef, map_apply measurable_inv hVm, withDensity_apply _ (measurable_inv hVm), hVinv]
    rw [setLIntegral_congr_fun hVm (g := fun _ => (1 : ℝ≥0∞)) fun x hx => by
      simp [hΔ, modularCharacter_eq_one_of_mem C hV hx]]
    simp
  have hμV0 : μ V ≠ 0 := V.isOpen.measure_ne_zero μ ⟨1, V.one_mem⟩
  have hμVt : μ V ≠ ∞ := hV.measure_lt_top.ne
  have hc : haarScalarFactor ν μ = 1 := by
    have := congrArg (fun m : Measure G => m V) hsmul
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at this
    rw [hνV] at this
    have h1 : (haarScalarFactor ν μ : ℝ≥0∞) * μ V = 1 * μ V := by rw [one_mul, ← this]
    exact_mod_cast (ENNReal.mul_left_inj hμV0 hμVt).1 h1
  rw [hsmul, hc, one_smul]

theorem lintegral_inv_haar {f : G → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x⁻¹ ∂C.haar μ₀ = ∫⁻ x, (modularCharacter x : ℝ≥0∞) * f x ∂C.haar μ₀ := by
  conv_lhs => rw [← C.map_inv_withDensity_haar μ₀]
  have h1 := lintegral_map (μ := (C.haar μ₀).withDensity fun x => (modularCharacter x : ℝ≥0∞))
    (f := fun x => f x⁻¹) (hf.comp measurable_inv) measurable_inv
  have h2 := lintegral_withDensity_eq_lintegral_mul (C.haar μ₀) (measurable_modularCharacter C) hf
  simp only [inv_inv] at h1
  rw [h1, h2]
  rfl

theorem integral_inv_haar {f : G → ℂ} (hf : Continuous f) :
    ∫ x, f x⁻¹ ∂C.haar μ₀ = ∫ x, (modularCharacter x : ℂ) * f x ∂C.haar μ₀ := by
  conv_lhs => rw [← C.map_inv_withDensity_haar μ₀]
  have h1 := integral_map (μ := (C.haar μ₀).withDensity fun x => (modularCharacter x : ℝ≥0∞))
    (φ := fun x : G => x⁻¹) (f := fun x => f x⁻¹) measurable_inv.aemeasurable
    (hf.comp continuous_inv).aestronglyMeasurable
  simp only [inv_inv] at h1
  rw [h1, integral_withDensity_eq_integral_smul (continuous_modularCharacter C).measurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [NNReal.smul_def, Complex.real_smul]

end LinearChart

end Measures

end GroundTheory.Automorphic
end
end

noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Matrix GLnLocal Parabolic Measures MeasureTheory
open scoped NNReal

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}


omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
  [BorelSpace F] in
theorem det_eq_prod_of_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : (ι → F) ≃ₗ[F] (ι → F)) (c : ι → F) (h : ∀ x s, L x s = c s * x s) :
    (LinearEquiv.det L : F) = ∏ s, c s := by
  rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix']
  have : LinearMap.toMatrix' (L : (ι → F) →ₗ[F] (ι → F)) = Matrix.diagonal c := by
    ext s t
    rw [LinearMap.toMatrix'_apply, LinearEquiv.coe_coe, h, Matrix.diagonal_apply, Pi.single_apply]
    split_ifs <;> simp
  rw [this, Matrix.det_diagonal]


omit [MeasurableSpace F] [BorelSpace F] in
theorem modulus_prod {ι : Type*} (s : Finset ι) (f : ι → F) :
    LocalField.modulus (∏ i ∈ s, f i) = ∏ i ∈ s, LocalField.modulus (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [LocalField.modulus_one]
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.prod_insert hi, LocalField.modulus_mul, ih]

theorem distribHaarChar_pi_eq_modulus {ι : Type*} [Fintype ι] [DecidableEq ι] (L : (ι → F) ≃ₗ[F] (ι → F)) :
    (distribHaarChar (ι → F) L : ℝ≥0) = LocalField.modulus (LinearEquiv.det L : F) := by
  rw [distribHaarChar_pi_eq, GroundTheory.LocalField.distribHaarChar_eq_modulus]


variable (β) in
abbrev leviDiag (μ : Fin n → ℤ) : levi F n β := ⟨Cartan.diagPow F n μ, diagPow_mem_levi μ⟩

theorem leviChart_leftModulus_diag (μ : Fin n → ℤ) :
    (leviChart β).leftModulus (leviDiag (F := F) β μ) =
      ∏ s : LeviIndex n β, LocalField.modulus ((uniformizer F : F) ^ μ s.1.1) := by
  classical
  rw [LinearChart.leftModulus, distribHaarChar_pi_eq_modulus,
    det_eq_prod_of_apply _ (fun s => (uniformizer F : F) ^ μ s.1.1), modulus_prod]
  intro x s
  show (((Cartan.diagPow F n μ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      (((leviCoord F n β).symm x : lieLevi F n β) : Matrix (Fin n) (Fin n) F)) s.1.1 s.1.2 = _
  rw [Cartan.coe_diagPow, Matrix.diagonal_mul]
  congr 1
  simp [leviCoord, s.2]

theorem parabolicChart_leftModulus_diag (μ : Fin n → ℤ) :
    (parabolicChart F n β).leftModulus (leviIncl (leviDiag (F := F) β μ)) =
      ∏ s : ParabolicIndex n β, LocalField.modulus ((uniformizer F : F) ^ μ s.1.1) := by
  classical
  rw [LinearChart.leftModulus, distribHaarChar_pi_eq_modulus,
    det_eq_prod_of_apply _ (fun s => (uniformizer F : F) ^ μ s.1.1), modulus_prod]
  intro x s
  show (((Cartan.diagPow F n μ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      (((parabolicCoord F n β).symm x : lieParabolic F n β) : Matrix (Fin n) (Fin n) F)) s.1.1 s.1.2 = _
  rw [Cartan.coe_diagPow, Matrix.diagonal_mul]
  congr 1
  simp [parabolicCoord, s.2]

theorem localField_modulus_eq_modulus {x : F} (hx : x ≠ 0) :
    LocalField.modulus x = Measures.modulus x := by
  rw [show x = ((Units.mk0 x hx : Fˣ) : F) from rfl, Measures.modulus_units,
    GroundTheory.LocalField.distribHaarChar_eq_modulus]

theorem modularCharacter_leviDiag (μ : Fin n → ℤ) :
    Measure.modularCharacter (leviIncl (leviDiag (F := F) β μ)) =
      ∏ s : {ij : Fin n × Fin n // β ij.1 < β ij.2},
        LocalField.modulus ((uniformizer F : F) ^ μ s.1.1) /
          LocalField.modulus ((uniformizer F : F) ^ μ s.1.2) := by
  have hϖ : (uniformizer F : F) ≠ 0 := Cartan.uniformizer_ne_zero F
  rw [modularCharacter_blockUpper_of_mem_borel' _ (diagPow_mem_borel μ)]
  refine Finset.prod_congr rfl fun s _ => ?_
  simp only [leviIncl_coe, Cartan.coe_diagPow, Matrix.diagonal_apply_eq]
  rw [localField_modulus_eq_modulus (zpow_ne_zero _ hϖ),
    localField_modulus_eq_modulus (zpow_ne_zero _ hϖ)]

omit [MeasurableSpace F] [BorelSpace F] in
theorem modulus_det_diagPow (μ : Fin n → ℤ) :
    LocalField.modulus ((Cartan.diagPow F n μ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det =
      ∏ i, LocalField.modulus ((uniformizer F : F) ^ μ i) := by
  rw [Cartan.coe_diagPow, Matrix.det_diagonal, modulus_prod]


omit [MeasurableSpace F] [BorelSpace F] in
theorem prod_leviIndex_eq (f : Fin n → ℝ≥0) :
    ∏ s : LeviIndex n β, f s.1.1 = ∏ i, f i ^ blockSize β (blockOf β i) := by
  classical
  rw [← Finset.prod_subtype (Finset.univ.filter fun ij : Fin n × Fin n => β ij.1 = β ij.2)
    (by simp) (fun ij => f ij.1), Finset.prod_filter, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_filter]
  simp only [Finset.prod_const]
  congr 1
  rw [blockSize, Fintype.card_subtype]
  congr 1
  ext j
  simp [blockOf, Set.rangeFactorization, Subtype.ext_iff, eq_comm]

omit [MeasurableSpace F] [BorelSpace F] in
theorem leviModulus_diag (μ : Fin n → ℤ) :
    leviModulus β (leviDiag (F := F) β μ) =
      ∏ s : LeviIndex n β, LocalField.modulus ((uniformizer F : F) ^ μ s.1.1) := by
  classical
  have hblock : ∀ a, ((leviBlock F (leviDiag (F := F) β μ) a : GL (Fiber β a) F) :
      Matrix (Fiber β a) (Fiber β a) F).det = ∏ i : Fiber β a, (uniformizer F : F) ^ μ i.1 := by
    intro a
    rw [coe_leviBlock]
    have : blocks β F ((Cartan.diagPow F n μ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a =
        Matrix.diagonal fun i : Fiber β a => (uniformizer F : F) ^ μ i.1 := by
      ext i j
      simp only [blocks, Cartan.coe_diagPow, Matrix.diagonal_apply, Subtype.ext_iff]
    rw [this, Matrix.det_diagonal]
  rw [leviModulus, prod_leviIndex_eq (β := β) fun i => LocalField.modulus ((uniformizer F : F) ^ μ i)]
  simp_rw [hblock, modulus_prod, ← Finset.prod_pow]
  rw [← Fintype.prod_fiberwise (blockOf β) fun i =>
    LocalField.modulus ((uniformizer F : F) ^ μ i) ^ blockSize β (blockOf β i)]
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun i _ => ?_
  rw [i.2]

omit [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] in
theorem prod_subtype_eq_ite {M : Type*} [CommMonoid M] (P : Fin n × Fin n → Prop) [DecidablePred P]
    (g : Fin n × Fin n → M) :
    ∏ s : {ij : Fin n × Fin n // P ij}, g s.1 = ∏ ij, if P ij then g ij else 1 := by
  rw [← Finset.prod_filter]
  exact (Finset.prod_subtype (Finset.univ.filter P) (by simp) g).symm


omit [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] in
theorem prod_identity (t : Fin n → ℝ≥0) (ht : ∀ i, t i ≠ 0) :
    ((∏ s : LeviIndex n β, t s.1.1) / ∏ s : ParabolicIndex n β, t s.1.1) ^ 2 *
      (∏ s : {ij : Fin n × Fin n // β ij.1 < β ij.2}, t s.1.1 / t s.1.2) * (∏ i, t i) ^ n =
      ∏ s : LeviIndex n β, t s.1.1 := by
  classical
  set A := ∏ ij : Fin n × Fin n, if β ij.1 = β ij.2 then t ij.1 else 1 with hAdef
  set U := ∏ ij : Fin n × Fin n, if β ij.1 < β ij.2 then t ij.1 else 1 with hUdef
  set L := ∏ ij : Fin n × Fin n, if β ij.2 < β ij.1 then t ij.1 else 1 with hLdef
  have hA : ∏ s : LeviIndex n β, t s.1.1 = A :=
    prod_subtype_eq_ite (fun ij : Fin n × Fin n => β ij.1 = β ij.2) fun ij => t ij.1
  have hP : ∏ s : ParabolicIndex n β, t s.1.1 = A * U := by
    rw [prod_subtype_eq_ite (fun ij : Fin n × Fin n => ¬ β ij.2 < β ij.1) fun ij => t ij.1,
      hAdef, hUdef, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun ij _ => ?_
    rcases lt_trichotomy (β ij.1) (β ij.2) with h | h | h
    · simp [h, h.ne, not_lt.2 h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.2 h.le]
  have hU : ∏ s : {ij : Fin n × Fin n // β ij.1 < β ij.2}, t s.1.1 / t s.1.2 = U / L := by
    rw [prod_subtype_eq_ite (fun ij : Fin n × Fin n => β ij.1 < β ij.2) fun ij => t ij.1 / t ij.2]
    have hswap : L = ∏ ij : Fin n × Fin n, if β ij.1 < β ij.2 then t ij.2 else 1 :=
      Fintype.prod_equiv (Equiv.prodComm (Fin n) (Fin n)) _ _ fun ij => rfl
    rw [hswap, hUdef, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun ij _ => ?_
    split_ifs <;> simp
  have hall : (∏ i, t i) ^ n = A * U * L := by
    have : (∏ i, t i) ^ n = ∏ ij : Fin n × Fin n, t ij.1 := by
      rw [Fintype.prod_prod_type, ← Finset.prod_pow]
      simp
    rw [this, hAdef, hUdef, hLdef, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun ij _ => ?_
    rcases lt_trichotomy (β ij.1) (β ij.2) with h | h | h
    · simp [h, h.ne, not_lt.2 h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.2 h.le]
  have hne : ∀ P : Fin n × Fin n → Prop, ∀ [DecidablePred P],
      (∏ ij : Fin n × Fin n, if P ij then t ij.1 else 1) ≠ 0 := fun P _ =>
    Finset.prod_ne_zero_iff.2 fun ij _ => by split_ifs <;> simp [ht]
  have hA0 : A ≠ 0 := hne _
  have hU0 : U ≠ 0 := hne _
  have hL0 : L ≠ 0 := hne _
  rw [hA, hP, hU, hall]
  field_simp


variable (β) in
def leviAbsDet : levi F n β →* ℝ≥0 where
  toFun m := LocalField.modulus (((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det)
  map_one' := by simp [LocalField.modulus_one]
  map_mul' m m' := by simp [Matrix.det_mul, LocalField.modulus_mul]

omit [MeasurableSpace F] [BorelSpace F] in
theorem leviAbsDet_apply (m : levi F n β) :
    leviAbsDet β m = LocalField.modulus (((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det) :=
  rfl


variable (β) in
def leviModulusHom : levi F n β →* ℝ≥0 where
  toFun := leviModulus β
  map_one' := by
    simp only [leviModulus]
    refine Finset.prod_eq_one fun a _ => ?_
    rw [coe_leviBlock, OneMemClass.coe_one, Units.val_one, blocks_one, Matrix.det_one,
      LocalField.modulus_one, one_pow]
  map_mul' m m' := by
    simp only [leviModulus, leviBlock_mul, Units.val_mul, Matrix.det_mul, LocalField.modulus_mul,
      mul_pow, Finset.prod_mul_distrib]

omit [MeasurableSpace F] [BorelSpace F] in
theorem leviModulusHom_apply (m : levi F n β) : leviModulusHom β m = leviModulus β m := rfl


omit [MeasurableSpace F] [BorelSpace F] in
theorem modulus_eq_one_of_ord {x : F} (hx : x ≠ 0) (h : LocalField.ord x = 0) :
    LocalField.modulus x = 1 :=
  LocalField.modulus_eq_one_iff.2 ⟨hx, h⟩

omit [MeasurableSpace F] [BorelSpace F] in
theorem leviAbsDet_of_mem_integralGL {k : levi F n β}
    (hk : (k : GL (Fin n) F) ∈ integralGL F n) : leviAbsDet β k = 1 :=
  modulus_eq_one_of_ord (det_ne_zero _) (ordDet_of_mem_integralGL hk)

omit [MeasurableSpace F] [BorelSpace F] in
theorem leviModulus_of_mem_integralGL {k : levi F n β}
    (hk : (k : GL (Fin n) F) ∈ integralGL F n) : leviModulus β k = 1 := by
  refine Finset.prod_eq_one fun a _ => ?_
  rw [modulus_eq_one_of_ord (det_ne_zero_of_GL _) (blockOrd_of_mem_integralGL a hk), one_pow]

omit [MeasurableSpace F] [BorelSpace F] in
theorem leviRatio_of_mem_integralGL {k : levi F n β}
    (hk : (k : GL (Fin n) F) ∈ integralGL F n) : leviRatio β k = 1 :=
  eq_one_of_mem_compact (leviRatio β) continuous_leviRatio (isCompact_leviIntegral (F := F))
    (Subgroup.mem_subgroupOf.2 hk)


omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in
theorem hom_cartan (f : levi F n β →* ℝ≥0)
    (hf : ∀ k : levi F n β, (k : GL (Fin n) F) ∈ integralGL F n → f k = 1) {k₁ k₂ : levi F n β}
    (h₁ : (k₁ : GL (Fin n) F) ∈ integralGL F n) (h₂ : (k₂ : GL (Fin n) F) ∈ integralGL F n)
    (d : levi F n β) : f (k₁ * d * k₂) = f d := by
  rw [map_mul, map_mul, hf k₁ h₁, hf k₂ h₂, one_mul, mul_one]

theorem leviRatio_sq_mul_modular_mul_det (m : levi F n β) :
    leviRatio β m ^ 2 * Measure.modularCharacter (leviIncl m) * leviAbsDet β m ^ n =
      leviModulus β m := by
  obtain ⟨μ, k₁, hk₁, k₂, hk₂, hm⟩ := exists_eq_mul_diagPow_mul_levi m.2
  have e : m = ⟨k₁, hk₁.1⟩ * leviDiag (F := F) β μ * ⟨k₂, hk₂.1⟩ := Subtype.ext hm
  have h1 := hom_cartan (leviRatio β) (fun k hk => leviRatio_of_mem_integralGL hk) (k₁ := ⟨k₁, hk₁.1⟩)
    (k₂ := ⟨k₂, hk₂.1⟩) hk₁.2 hk₂.2 (leviDiag (F := F) β μ)
  have h2 := hom_cartan (Measure.modularCharacter.comp leviIncl)
    (fun k hk => modularCharacter_eq_one_of_mem_integralGL _ hk) (k₁ := ⟨k₁, hk₁.1⟩)
    (k₂ := ⟨k₂, hk₂.1⟩) hk₁.2 hk₂.2 (leviDiag (F := F) β μ)
  have h3 := hom_cartan (leviAbsDet β) (fun k hk => leviAbsDet_of_mem_integralGL hk) (k₁ := ⟨k₁, hk₁.1⟩)
    (k₂ := ⟨k₂, hk₂.1⟩) hk₁.2 hk₂.2 (leviDiag (F := F) β μ)
  have h4 := hom_cartan (leviModulusHom β) (fun k hk => leviModulus_of_mem_integralGL hk)
    (k₁ := ⟨k₁, hk₁.1⟩) (k₂ := ⟨k₂, hk₂.1⟩) hk₁.2 hk₂.2 (leviDiag (F := F) β μ)
  simp only [MonoidHom.coe_comp, Function.comp_apply, leviModulusHom_apply] at h2 h4
  rw [e, h1, h2, h3, h4, leviRatio_apply, leviChart_leftModulus_diag,
    parabolicChart_leftModulus_diag, modularCharacter_leviDiag, leviAbsDet_apply,
    modulus_det_diagPow, leviModulus_diag]
  exact prod_identity (fun i => LocalField.modulus ((uniformizer F : F) ^ μ i)) fun i =>
    LocalField.modulus_ne_zero (zpow_ne_zero _ (Cartan.uniformizer_ne_zero F))

end GodementJacquet

end GroundTheory.Automorphic
end
end

noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Matrix GLnLocal Parabolic Measures MeasureTheory GJMatrix
open scoped NNReal
open ValuativeRel

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}

def matrixTensor (g : Fin n × Fin n → F → ℂ) (X : Matrix (Fin n) (Fin n) F) : ℂ :=
  ∏ ij : Fin n × Fin n, g ij (X ij.1 ij.2)

omit [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem matrixTensor_norm (g : Fin n × Fin n → F → ℂ) (X : Matrix (Fin n) (Fin n) F) :
    matrixTensor (fun ij x => ((‖g ij x‖ : ℝ) : ℂ)) X = ((‖matrixTensor g X‖ : ℝ) : ℂ) := by
  simp [matrixTensor, norm_prod]

theorem mem_span_matrixTensor {Φ : Matrix (Fin n) (Fin n) F → ℂ} (hΦ : IsSchwartzBruhat Φ) :
    Φ ∈ Submodule.span ℂ (Set.range fun p : ℤ × (Fin n × Fin n → F) =>
      matrixTensor fun ij => cosetInd (LocalField.valBall F p.1) (p.2 ij)) := by
  have h := (isSchwartzBruhat_iff_comp_symm Φ).1 hΦ
  rw [localSchwartzBruhatPi_eq_span] at h
  let L : ((Fin n × Fin n → F) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin n) F → ℂ) :=
    LinearMap.funLeft ℂ ℂ (matrixCoordHomeomorph (Fin n) F)
  have hm := Submodule.mem_map_of_mem (f := L) h
  rw [Submodule.map_span, ← Set.range_comp] at hm
  have e1 : L (Φ ∘ (matrixCoordHomeomorph (Fin n) F).symm) = Φ := by
    funext X
    simp [L, LinearMap.funLeft_apply]
  have e2 : (⇑L ∘ fun p : ℤ × (Fin n × Fin n → F) =>
      localTensor fun i => cosetInd (LocalField.valBall F p.1) (p.2 i)) =
      fun p => matrixTensor fun ij => cosetInd (LocalField.valBall F p.1) (p.2 ij) := by
    funext p X
    rfl
  rw [e1, e2] at hm
  exact hm

section Unip

variable [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle)


variable (β) in
def unipMeasure : Measure (UnipotentIndex n β → F) :=
  Measure.pi fun _ => LocalField.selfDualMeasure ψ

instance : (unipMeasure β ψ).IsAddHaarMeasure := by
  unfold unipMeasure
  infer_instance


variable (β) in
def tensorConst (g : Fin n × Fin n → F → ℂ) : ℂ :=
  (∏ s : UnipotentIndex n β,
    LocalField.localFourier (LocalField.selfDualMeasure ψ) ψ (g s.1) 0) *
      ∏ ij : Fin n × Fin n, if β ij.2 < β ij.1 then g ij 0 else 1


omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
  [BorelSpace F] in
theorem prod_not_unip_eq {X : Matrix (Fin n) (Fin n) F} (hX : ∀ i j, β i ≠ β j → X i j = 0)
    (g : Fin n × Fin n → F → ℂ) :
    ∏ s : {ij : Fin n × Fin n // ¬ β ij.1 < β ij.2}, g s.1 (X s.1.1 s.1.2) =
      leviTensor β (fun s => g s.1) X * ∏ ij : Fin n × Fin n, if β ij.2 < β ij.1 then g ij 0 else 1 := by
  classical
  rw [prod_subtype_eq_ite (fun ij : Fin n × Fin n => ¬ β ij.1 < β ij.2) fun ij => g ij (X ij.1 ij.2),
    leviTensor, prod_subtype_eq_ite (fun ij : Fin n × Fin n => β ij.1 = β ij.2)
      fun ij => g ij (X ij.1 ij.2), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun ij _ => ?_
  rcases lt_trichotomy (β ij.1) (β ij.2) with h | h | h
  · simp [h, h.ne, not_lt.2 h.le]
  · simp [h]
  · simp [h, h.ne', not_lt.2 h.le, hX ij.1 ij.2 h.ne']

theorem integral_matrixTensor_add_unip (g : Fin n × Fin n → F → ℂ)
    {X : Matrix (Fin n) (Fin n) F} (hX : ∀ i j, β i ≠ β j → X i j = 0) :
    ∫ u, matrixTensor g (X + unipMatrix F u) ∂unipMeasure β ψ =
      tensorConst β ψ g * leviTensor β (fun s => g s.1) X := by
  classical
  have hsplit : ∀ u : UnipotentIndex n β → F, matrixTensor g (X + unipMatrix F u) =
      (∏ s : {ij : Fin n × Fin n // ¬ β ij.1 < β ij.2}, g s.1 (X s.1.1 s.1.2)) *
        ∏ s : UnipotentIndex n β, g s.1 (u s) := by
    intro u
    rw [matrixTensor, ← Fintype.prod_subtype_mul_prod_subtype
      (fun ij : Fin n × Fin n => β ij.1 < β ij.2), mul_comm]
    congr 1
    · refine Finset.prod_congr rfl fun s _ => ?_
      rw [Matrix.add_apply, unipMatrix_apply_of_not_lt u s.2, add_zero]
    · refine Finset.prod_congr rfl fun s _ => ?_
      rw [Matrix.add_apply, hX _ _ (ne_of_lt s.2), zero_add, unipMatrix_apply_of_lt u s.2]
  simp_rw [hsplit]
  rw [integral_const_mul, unipMeasure,
    integral_fintype_prod_eq_prod (f := fun (s : UnipotentIndex n β) x => g s.1 x),
    prod_not_unip_eq hX, tensorConst]
  have h0 : ∀ s : UnipotentIndex n β, ∫ x, g s.1 x ∂LocalField.selfDualMeasure ψ =
      LocalField.localFourier (LocalField.selfDualMeasure ψ) ψ (g s.1) 0 := by
    intro s
    simp [LocalField.localFourier]
  simp_rw [h0]
  ring

theorem localMatrixFourier_matrixTensor (g : Fin n × Fin n → F → ℂ) (Y : Matrix (Fin n) (Fin n) F) :
    localMatrixFourier ψ (matrixTensor g) Y = ∏ ij : Fin n × Fin n,
      LocalField.localFourier (LocalField.selfDualMeasure ψ) ψ (g ij) (Y ij.2 ij.1) := by
  rw [localMatrixFourier_eq]
  have : matrixTensor g ∘ (matrixCoordHomeomorph (Fin n) F).symm = localTensor g := by
    funext x
    rfl
  rw [this, localFourierPi_localTensor]
  rfl

theorem localMatrixFourier_matrixTensor_eq (g : Fin n × Fin n → F → ℂ) :
    localMatrixFourier ψ (matrixTensor g) = matrixTensor fun ij =>
      LocalField.localFourier (LocalField.selfDualMeasure ψ) ψ (g ij.swap) := by
  funext Z
  rw [localMatrixFourier_matrixTensor, matrixTensor]
  exact Fintype.prod_equiv (Equiv.prodComm _ _) _ _ fun ij => rfl


omit [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] in
theorem leviTensor_swap_eq (h : Fin n × Fin n → F → ℂ) (Y : Matrix (Fin n) (Fin n) F) :
    leviTensor β (fun s => h s.1.swap) Y = ∏ s : LeviIndex n β, h s.1 (Y s.1.2 s.1.1) := by
  rw [leviTensor]
  let e : LeviIndex n β ≃ LeviIndex n β :=
    { toFun := fun s => ⟨s.1.swap, s.2.symm⟩
      invFun := fun s => ⟨s.1.swap, s.2.symm⟩
      left_inv := fun s => rfl
      right_inv := fun s => rfl }
  exact Fintype.prod_equiv e _ _ fun s => rfl

theorem leviTensor_swap_eq_hat (g : Fin n × Fin n → F → ℂ) (Y : Matrix (Fin n) (Fin n) F) :
    leviTensor β (fun s => LocalField.localFourier (LocalField.selfDualMeasure ψ) ψ (g s.1.swap)) Y =
      leviTensorHat β ψ (fun s => g s.1) Y :=
  leviTensor_swap_eq (fun ij => LocalField.localFourier (LocalField.selfDualMeasure ψ) ψ (g ij)) Y

theorem integral_norm_matrixTensor_add_unip (g : Fin n × Fin n → F → ℂ)
    {X : Matrix (Fin n) (Fin n) F} (hX : ∀ i j, β i ≠ β j → X i j = 0) :
    ∫ u, ‖matrixTensor g (X + unipMatrix F u)‖ ∂unipMeasure β ψ =
      ‖tensorConst β ψ (fun ij x => ((‖g ij x‖ : ℝ) : ℂ))‖ * ‖leviTensor β (fun s => g s.1) X‖ := by
  have h := integral_matrixTensor_add_unip ψ (fun ij x => ((‖g ij x‖ : ℝ) : ℂ)) hX
  simp_rw [matrixTensor_norm] at h
  rw [integral_complex_ofReal] at h
  have h2 := congrArg (‖·‖) h
  simp only [Complex.norm_real, norm_mul] at h2
  rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)] at h2
  rw [h2]
  congr 1
  simp [leviTensor, norm_prod]


variable {ψ} in
theorem integral_norm_fourier_matrixTensor_add_unip (g : Fin n × Fin n → F → ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Y : Matrix (Fin n) (Fin n) F}, (∀ i j, β i ≠ β j → Y i j = 0) →
      ∫ u, ‖localMatrixFourier ψ (matrixTensor g) (Y + unipMatrix F u)‖ ∂unipMeasure β ψ =
        C * ‖leviTensorHat β ψ (fun s => g s.1) Y‖ := by
  set g' : Fin n × Fin n → F → ℂ := fun ij =>
    LocalField.localFourier (LocalField.selfDualMeasure ψ) ψ (g ij.swap)
  refine ⟨‖tensorConst β ψ (fun ij x => ((‖g' ij x‖ : ℝ) : ℂ))‖, norm_nonneg _, fun hY => ?_⟩
  rw [localMatrixFourier_matrixTensor_eq, integral_norm_matrixTensor_add_unip ψ g' hY,
    leviTensor_swap_eq_hat]


variable {ψ} in
theorem integral_fourier_matrixTensor_add_unip (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    {g : Fin n × Fin n → F → ℂ} (hg : ∀ ij, g ij ∈ LocalField.schwartzBruhat F)
    {Y : Matrix (Fin n) (Fin n) F} (hY : ∀ i j, β i ≠ β j → Y i j = 0) :
    ∫ u, localMatrixFourier ψ (matrixTensor g) (Y + unipMatrix F u) ∂unipMeasure β ψ =
      tensorConst β ψ g * leviTensorHat β ψ (fun s => g s.1) Y := by
  classical
  set gh : Fin n × Fin n → F → ℂ := fun ij =>
    LocalField.localFourier (LocalField.selfDualMeasure ψ) ψ (g ij) with hgh
  set g' : Fin n × Fin n → F → ℂ := fun ij => gh ij.swap with hg'
  have hT : ∀ Z, localMatrixFourier ψ (matrixTensor g) Z = matrixTensor g' Z := by
    intro Z
    rw [localMatrixFourier_matrixTensor, matrixTensor]
    exact Fintype.prod_equiv (Equiv.prodComm _ _) _ _ fun ij => rfl
  simp_rw [hT]
  rw [integral_matrixTensor_add_unip ψ g' hY]
  congr 1
  · have hinv : ∀ ij : Fin n × Fin n,
        LocalField.localFourier (LocalField.selfDualMeasure ψ) ψ (g' ij) 0 = g ij.swap 0 := by
      intro ij
      rw [hg', hgh]
      simp only
      rw [LocalField.localFourier_localFourier_selfDual hψ hψ1 (hg _), neg_zero]
    rw [tensorConst, tensorConst]
    simp_rw [hinv]
    rw [mul_comm]
    congr 1
    · rw [prod_subtype_eq_ite (fun ij : Fin n × Fin n => β ij.1 < β ij.2) fun ij => gh ij 0]
      exact Fintype.prod_equiv (Equiv.prodComm _ _) _ _ fun ij => rfl
    · rw [prod_subtype_eq_ite (fun ij : Fin n × Fin n => β ij.1 < β ij.2)
        fun ij => g ij.swap 0]
      exact (Fintype.prod_equiv (Equiv.prodComm _ _) _ _ fun ij => rfl).symm
  · rw [leviTensor, leviTensorHat]
    let e : LeviIndex n β ≃ LeviIndex n β :=
      { toFun := fun s => ⟨s.1.swap, s.2.symm⟩
        invFun := fun s => ⟨s.1.swap, s.2.symm⟩
        left_inv := fun s => rfl
        right_inv := fun s => rfl }
    exact Fintype.prod_equiv e _ _ fun s => rfl

end Unip

section Translate

variable [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle)


omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in
theorem mul_mem_integer_iff {y : GL (Fin n) F} (hy : y ∈ integralGL F n)
    (X : Matrix (Fin n) (Fin n) F) :
    (∀ i j, (X * (y : Matrix (Fin n) (Fin n) F)) i j ∈ 𝒪[F]) ↔ ∀ i j, X i j ∈ 𝒪[F] := by
  obtain ⟨h₁, h₂⟩ := (mem_integralGL_iff F n).1 hy
  have key : ∀ (A B : Matrix (Fin n) (Fin n) F), (∀ i j, A i j ∈ 𝒪[F]) → (∀ i j, B i j ∈ 𝒪[F]) →
      ∀ i j, (A * B) i j ∈ 𝒪[F] := fun A B hA hB i j => by
    rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (hB k j)
  refine ⟨fun h i j => ?_, fun h => key _ _ h h₁⟩
  have := key _ _ h h₂ i j
  rwa [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one] at this

def mulRightEquiv (y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F ≃ₜ+ Matrix (Fin n) (Fin n) F where
  toFun X := X * (y : Matrix (Fin n) (Fin n) F)
  invFun X := X * ((y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  left_inv X := by simp [Matrix.mul_assoc]
  right_inv X := by simp [Matrix.mul_assoc]
  map_add' X Y := Matrix.add_mul X Y _
  continuous_toFun := continuous_id.matrix_mul continuous_const
  continuous_invFun := continuous_id.matrix_mul continuous_const

omit [MeasurableSpace F] [BorelSpace F] in
theorem mulRightEquiv_apply (y : GL (Fin n) F) (X : Matrix (Fin n) (Fin n) F) :
    mulRightEquiv y X = X * (y : Matrix (Fin n) (Fin n) F) := rfl

theorem measurePreserving_mul_right {y : GL (Fin n) F} (hy : y ∈ integralGL F n) :
    MeasurePreserving (mulRightEquiv y)
      (matrixMeasure (LocalField.selfDualMeasure ψ)) (matrixMeasure (LocalField.selfDualMeasure ψ)) := by
  set μ : Measure (Matrix (Fin n) (Fin n) F) := matrixMeasure (LocalField.selfDualMeasure ψ) with hμ
  have hH : (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n =>
      LocalField.selfDualMeasure ψ : Measure (Fin n → Fin n → F)).IsAddHaarMeasure := by
    have : (Measure.pi fun _ : Fin n => LocalField.selfDualMeasure ψ).IsAddHaarMeasure :=
      inferInstance
    infer_instance
  have : μ.IsAddHaarMeasure := hH
  set e := mulRightEquiv y
  have hmap : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  have hsmul := Measure.isAddLeftInvariant_eq_smul (μ.map e) μ
  set B : Set (Matrix (Fin n) (Fin n) F) :=
    Set.univ.pi fun _ => Set.univ.pi fun _ => (LocalField.valBall F 0 : Set F) with hB
  have hBo : IsOpen B := isOpen_set_pi Set.finite_univ fun _ _ =>
    isOpen_set_pi Set.finite_univ fun _ _ => LocalField.isOpen_valBall 0
  have hBc : IsCompact B := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
    LocalField.isCompact_valBall 0
  have hmemB : ∀ X, X ∈ B ↔ ∀ i j, X i j ∈ 𝒪[F] := by
    intro X
    rw [hB]
    constructor
    · intro h i j
      exact LocalField.mem_valBall_zero_iff.1 (h i (Set.mem_univ _) j (Set.mem_univ _))
    · intro h i _ j _
      exact LocalField.mem_valBall_zero_iff.2 (h i j)
  have hpre : e ⁻¹' B = B := by
    ext X
    rw [Set.mem_preimage, hmemB, hmemB]
    exact mul_mem_integer_iff hy X
  have h0 : μ B ≠ 0 := hBo.measure_ne_zero μ ⟨0, fun _ _ _ _ => by simp [zero_mem]⟩
  have ht : μ B ≠ ⊤ := hBc.measure_lt_top.ne
  have hc : Measure.addHaarScalarFactor (μ.map e) μ = 1 := by
    have h1 := congrArg (fun m : Measure (Matrix (Fin n) (Fin n) F) => m B) hsmul
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h1
    have hme : Measurable e := e.continuous.measurable
    rw [Measure.map_apply hme hBo.measurableSet, hpre] at h1
    have h2 : (Measure.addHaarScalarFactor (μ.map e) μ : ENNReal) * μ B = 1 * μ B := by
      rw [one_mul, ← h1]
    exact_mod_cast (ENNReal.mul_left_inj h0 ht).1 h2
  refine ⟨e.continuous.measurable, ?_⟩
  rw [hsmul, hc, one_smul]

theorem localMatrixFourier_mul_right (Φ : Matrix (Fin n) (Fin n) F → ℂ) {y : GL (Fin n) F}
    (hy : y ∈ integralGL F n) (Z : Matrix (Fin n) (Fin n) F) :
    localMatrixFourier ψ (fun X => Φ (X * (y : Matrix (Fin n) (Fin n) F))) Z =
      localMatrixFourier ψ Φ (((y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * Z) := by
  have hm := measurePreserving_mul_right ψ hy
  have he : MeasurableEmbedding (mulRightEquiv y) :=
    (mulRightEquiv y).toHomeomorph.measurableEmbedding
  rw [localMatrixFourier, localMatrixFourier]
  have key : ∀ X : Matrix (Fin n) (Fin n) F,
      Φ (X * (y : Matrix (Fin n) (Fin n) F)) * (ψ (Matrix.trace (X * Z)) : ℂ) =
        (fun W => Φ W * (ψ (Matrix.trace (W * (((y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * Z))) :
          ℂ)) (mulRightEquiv y X) := by
    intro X
    simp only [mulRightEquiv_apply]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (y : Matrix (Fin n) (Fin n) F), ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.one_mul]
  simp_rw [key]
  exact hm.integral_comp he (fun W => Φ W *
    (ψ (Matrix.trace (W * (((y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * Z))) : ℂ))

end Translate

end GodementJacquet

end GroundTheory.Automorphic
