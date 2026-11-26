module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DetMulRCReal

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.NormInvSqrtTwoSq
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PjCong
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.MpOfIsomProd
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Matrix ComplexConjugate

section Iso

variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

theorem mp_of_isom (f : E →ₗ[ℝ] F) (hn : ∀ x, ‖f x‖ = ‖x‖) (hs : Function.Surjective f) :
    MeasurePreserving f volume volume := by
  have hinj : Function.Injective f := by
    intro a b hab
    have h0 : ‖a - b‖ = 0 := by rw [← hn, map_sub, hab, sub_self, norm_zero]
    exact sub_eq_zero.mp (norm_eq_zero.mp h0)
  let e : E ≃ₗ[ℝ] F := LinearEquiv.ofBijective f ⟨hinj, hs⟩
  let g : E ≃ₗᵢ[ℝ] F := { e with norm_map' := hn }
  exact g.measurePreserving

variable {U V : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U] [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem mp_of_isom_prod (f : U × V →ₗ[ℝ] F) (hn : ∀ a b, ‖f (a, b)‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2)
    (hs : Function.Surjective f) : MeasurePreserving f volume volume := by
  let L : WithLp 2 (U × V) ≃ₗ[ℝ] U × V := WithLp.linearEquiv 2 ℝ (U × V)
  have h1 : MeasurePreserving (f.comp L.toLinearMap) volume volume := by
    apply mp_of_isom
    · intro t
      have h := hn (L t).1 (L t).2
      have h2 := WithLp.prod_norm_sq_eq_of_L2 t
      have e : (L t) = ((L t).1, (L t).2) := rfl
      rw [← e] at h
      have h3 : ‖f (L t)‖ ^ 2 = ‖t‖ ^ 2 := by rw [h, h2]; rfl
      exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h3
    · exact hs.comp L.surjective
  have h2 := WithLp.volume_preserving_toLp U V
  have h3 : (⇑(f.comp L.toLinearMap) ∘ WithLp.toLp 2) = ⇑f := by
    funext x
    rfl
  have h4 := h1.comp h2
  rwa [h3] at h4

end Iso

def reimL {n m : ℕ} : Matrix (Fin n) (Fin m) ℂ →ₗ[ℝ] EuclideanSpace ℝ (Fin n × Fin m × Bool) where
  toFun := reim
  map_add' Y Z := by
    ext p
    rcases p with ⟨i, j, s⟩
    cases s <;> simp [reim]
  map_smul' c Y := by
    ext p
    rcases p with ⟨i, j, s⟩
    cases s <;> simp [reim]

theorem reimL_apply {n m : ℕ} (Y : Matrix (Fin n) (Fin m) ℂ) : reimL Y = reim Y := rfl

theorem norm_reim_sq {n m : ℕ} (Y : Matrix (Fin n) (Fin m) ℂ) :
    ‖reim Y‖ ^ 2 = ∑ i, ∑ j, ‖Y i j‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  simp only [reim, Fintype.sum_prod_type, Fintype.sum_bool]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

theorem reim_surj {n m : ℕ} (y : EuclideanSpace ℝ (Fin n × Fin m × Bool)) :
    ∃ Y : Matrix (Fin n) (Fin m) ℂ, reim Y = y := by
  refine ⟨Matrix.of fun i j => ⟨y.ofLp (i, j, true), y.ofLp (i, j, false)⟩, ?_⟩
  ext p
  rcases p with ⟨i, j, s⟩
  cases s <;> simp [reim]

theorem herm_cross {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ) (hA : Aᴴ = A) (hB : Bᴴ = B) :
    (∑ i, ∑ j, A i j * conj (B i j)).im = 0 := by
  have hA' : ∀ i j, A j i = conj (A i j) := fun i j => by
    simpa [Matrix.conjTranspose_apply] using (congrFun (congrFun hA j) i).symm
  have hB' : ∀ i j, B j i = conj (B i j) := fun i j => by
    simpa [Matrix.conjTranspose_apply] using (congrFun (congrFun hB j) i).symm
  have hc : conj (∑ i, ∑ j, A i j * conj (B i j)) = ∑ i, ∑ j, A i j * conj (B i j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, Complex.conj_conj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hA' j i, hB' j i, Complex.conj_conj]
  exact Complex.conj_eq_iff_im.mp hc

theorem herm_pyth {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ) (hA : Aᴴ = A) (hB : Bᴴ = B) :
    ∑ i, ∑ j, ‖(Complex.I • A + B) i j‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 + ∑ i, ∑ j, ‖B i j‖ ^ 2 := by
  have key : ∀ i j, ‖(Complex.I • A + B) i j‖ ^ 2 =
      ‖A i j‖ ^ 2 + ‖B i j‖ ^ 2 - 2 * (A i j * conj (B i j)).im := by
    intro i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.sq_norm,
      Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
    ring
  have h0 := herm_cross A B hA hB
  simp only [Complex.im_sum] at h0
  simp only [key, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, h0]
  ring

def psiLp {m : ℕ} {η : Type} [Fintype η] (H : EuclideanSpace ℝ η →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ) :
    EuclideanSpace ℝ η × EuclideanSpace ℝ η →ₗ[ℝ] EuclideanSpace ℝ (Fin m × Fin m × Bool) where
  toFun z := reimL (Complex.I • H z.1 + H z.2)
  map_add' a b := by
    show reimL (Complex.I • H (a + b).1 + H (a + b).2) =
      reimL (Complex.I • H a.1 + H a.2) + reimL (Complex.I • H b.1 + H b.2)
    rw [← map_add (f := _)]
    congr 1
    simp only [Prod.fst_add, Prod.snd_add, map_add (f := _), smul_add]
    abel
  map_smul' c z := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, RingHom.id_apply]
    rw [smul_comm Complex.I c, ← smul_add, map_smul]

theorem psiLp_apply {m : ℕ} {η : Type} [Fintype η] (H : EuclideanSpace ℝ η →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ)
    (z : EuclideanSpace ℝ η × EuclideanSpace ℝ η) : psiLp H z = reim (Complex.I • H z.1 + H z.2) := rfl

theorem psi_mp {m : ℕ} {η : Type} [Fintype η] (H : EuclideanSpace ℝ η →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ)
    (hH : ∀ t, (H t)ᴴ = H t) (hn : ∀ t, ∑ i, ∑ j, ‖H t i j‖ ^ 2 = ‖t‖ ^ 2)
    (hs : ∀ M : Matrix (Fin m) (Fin m) ℂ, Mᴴ = M → ∃ t, H t = M) :
    MeasurePreserving (psiLp H) volume volume := by
  apply mp_of_isom_prod
  · intro a b
    rw [psiLp_apply, norm_reim_sq, herm_pyth _ _ (hH a) (hH b), hn a, hn b]
  · intro y
    obtain ⟨Y, rfl⟩ := reim_surj y
    set A : Matrix (Fin m) (Fin m) ℂ := (-(Complex.I / 2)) • (Y - Yᴴ) with hAdef
    set B : Matrix (Fin m) (Fin m) ℂ := (1 / 2 : ℂ) • (Y + Yᴴ) with hBdef
    have hA : Aᴴ = A := by
      rw [hAdef, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
        Matrix.conjTranspose_conjTranspose]
      ext i j
      simp [Complex.ext_iff]
      constructor <;> ring
    have hB : Bᴴ = B := by
      rw [hBdef, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
        Matrix.conjTranspose_conjTranspose]
      ext i j
      simp [Complex.ext_iff]
      constructor <;> ring
    obtain ⟨s, hsA⟩ := hs A hA
    obtain ⟨t, htB⟩ := hs B hB
    refine ⟨(s, t), ?_⟩
    rw [psiLp_apply]
    congr 1
    simp only [hsA, htB]
    ext i j
    simp [hAdef, hBdef, Complex.ext_iff]
    constructor <;> ring

end PI.AprimeInfW
end
end

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Matrix

def liftL {Z E X : Type} [AddCommGroup Z] [Module ℝ Z] [AddCommGroup E] [Module ℝ E] [AddCommGroup X]
    [Module ℝ X] (L : E →ₗ[ℝ] X) (hL : Function.Injective L) (Ξ : Z →ₗ[ℝ] X) (h : ∀ z, ∃ x, L x = Ξ z) :
    Z →ₗ[ℝ] E :=
  (LinearEquiv.ofInjective L hL).symm.toLinearMap ∘ₗ
    Ξ.codRestrict (LinearMap.range L) (fun z => by obtain ⟨x, hx⟩ := h z; exact ⟨x, hx⟩)

theorem liftL_spec {Z E X : Type} [AddCommGroup Z] [Module ℝ Z] [AddCommGroup E] [Module ℝ E] [AddCommGroup X]
    [Module ℝ X] (L : E →ₗ[ℝ] X) (hL : Function.Injective L) (Ξ : Z →ₗ[ℝ] X) (h : ∀ z, ∃ x, L x = Ξ z) (z : Z) :
    L (liftL L hL Ξ h z) = Ξ z := by
  have key := (LinearEquiv.ofInjective L hL).apply_symm_apply
    (Ξ.codRestrict (LinearMap.range L) (fun z => by obtain ⟨x, hx⟩ := h z; exact ⟨x, hx⟩) z)
  exact congrArg Subtype.val key

theorem inj_of_frob {ι p q : Type} [Fintype ι] [Fintype p] [Fintype q]
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] Matrix p q ℂ) (hn : ∀ t, ∑ i, ∑ j, ‖L t i j‖ ^ 2 = ‖t‖ ^ 2) :
    Function.Injective L := by
  refine (injective_iff_map_eq_zero L).mpr ?_
  intro t ht
  have h := hn t
  rw [ht] at h
  simp only [Matrix.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero] at h
  have h2 : ‖t‖ ^ 2 = 0 := h.symm
  exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h2)

def congL {m : ℕ} (B : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ where
  toFun M := Bᴴ * M * B
  map_add' _ _ := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c M := by simp

theorem congL_herm {m : ℕ} (B M : Matrix (Fin m) (Fin m) ℂ) (hM : Mᴴ = M) : (congL B M)ᴴ = congL B M := by
  show (Bᴴ * M * B)ᴴ = Bᴴ * M * B
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hM,
    Matrix.mul_assoc]

def congH {m : ℕ} {η : Type} [Fintype η] (H : EuclideanSpace ℝ η →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ)
    (hH : ∀ t, (H t)ᴴ = H t) (hn : ∀ t, ∑ i, ∑ j, ‖H t i j‖ ^ 2 = ‖t‖ ^ 2)
    (hs : ∀ M : Matrix (Fin m) (Fin m) ℂ, Mᴴ = M → ∃ t, H t = M) (B : Matrix (Fin m) (Fin m) ℂ) :
    EuclideanSpace ℝ η →ₗ[ℝ] EuclideanSpace ℝ η :=
  liftL H (inj_of_frob H hn) (congL B ∘ₗ H) (fun s => hs _ (congL_herm B _ (hH s)))

theorem congH_spec {m : ℕ} {η : Type} [Fintype η] (H : EuclideanSpace ℝ η →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ)
    (hH : ∀ t, (H t)ᴴ = H t) (hn : ∀ t, ∑ i, ∑ j, ‖H t i j‖ ^ 2 = ‖t‖ ^ 2)
    (hs : ∀ M : Matrix (Fin m) (Fin m) ℂ, Mᴴ = M → ∃ t, H t = M) (B : Matrix (Fin m) (Fin m) ℂ) (s) :
    H (congH H hH hn hs B s) = Bᴴ * H s * B := by
  unfold congH
  exact liftL_spec _ _ _ _ s

theorem cong_factor {m : ℕ} {η : Type} [Fintype η] (H : EuclideanSpace ℝ η →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ)
    (hH : ∀ t, (H t)ᴴ = H t) (hn : ∀ t, ∑ i, ∑ j, ‖H t i j‖ ^ 2 = ‖t‖ ^ 2)
    (hs : ∀ M : Matrix (Fin m) (Fin m) ℂ, Mᴴ = M → ∃ t, H t = M) (B : Matrix (Fin m) (Fin m) ℂ)
    (hB : B.det ≠ 0) :
    (volume : Measure (EuclideanSpace ℝ η)).map (congH H hH hn hs B) =
      ENNReal.ofReal (Complex.normSq B.det ^ m)⁻¹ • volume := by
  set C := congH H hH hn hs B with hCdef
  have hspec : ∀ s, H (C s) = Bᴴ * H s * B := congH_spec H hH hn hs B
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.2 hB
  have hBh : IsUnit Bᴴ.det := by
    rw [Matrix.det_conjTranspose]; exact isUnit_iff_ne_zero.2 (star_ne_zero.2 hB)
  have canc : ∀ X : Matrix (Fin m) (Fin m) ℂ, (Bᴴ)⁻¹ * (Bᴴ * X * B) * B⁻¹ = X := by
    intro X
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hBu, Matrix.mul_one, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hBh, Matrix.one_mul]
  have hinjC : Function.Injective C := by
    intro a b hab
    apply inj_of_frob H hn
    have h1 := congrArg H hab
    rw [hspec, hspec] at h1
    rw [← canc (H a), h1, canc]
  have hdet : LinearMap.det C ≠ 0 := fun h =>
    (LinearMap.det_eq_zero_iff_ker_ne_bot.1 h) (LinearMap.ker_eq_bot.2 hinjC)
  have hC := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
    (μ := (volume : Measure (EuclideanSpace ℝ η))) hdet
  set c := ENNReal.ofReal |(LinearMap.det C)⁻¹| with hc

  set mR : EuclideanSpace ℝ (Fin m × Fin m × Bool) →ₗ[ℝ] EuclideanSpace ℝ (Fin m × Fin m × Bool) :=
    (reimE (r := m) (m := m)).toLinearMap ∘ₗ ((mulRC (r := m) B).restrictScalars ℝ) ∘ₗ
      (reimE (r := m) (m := m)).symm.toLinearMap with hmR
  set mL : EuclideanSpace ℝ (Fin m × Fin m × Bool) →ₗ[ℝ] EuclideanSpace ℝ (Fin m × Fin m × Bool) :=
    (reimE (r := m) (m := m)).toLinearMap ∘ₗ ((mulLC (c := m) Bᴴ).restrictScalars ℝ) ∘ₗ
      (reimE (r := m) (m := m)).symm.toLinearMap with hmL
  have hmRf : (mR : _ → _) = fun y => reim (Matrix.of ((reimE (r := m) (m := m)).symm y) * B) := by
    funext y
    simp only [hmR, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearMap.coe_restrictScalars]
    rw [mulRC_apply]
    rfl
  have hmLf : (mL : _ → _) = fun y => reim (Bᴴ * Matrix.of ((reimE (r := m) (m := m)).symm y)) := by
    funext y
    simp only [hmL, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearMap.coe_restrictScalars]
    rw [mulLC_apply]
    rfl
  have hR : (volume : Measure (EuclideanSpace ℝ (Fin m × Fin m × Bool))).map mR =
      ENNReal.ofReal (Complex.normSq B.det ^ m)⁻¹ • volume := by
    rw [hmRf]; exact map_mulR B hB
  have hL : (volume : Measure (EuclideanSpace ℝ (Fin m × Fin m × Bool))).map mL =
      ENNReal.ofReal (Complex.normSq B.det ^ m)⁻¹ • volume := by
    rw [hmLf, map_mulL Bᴴ (by rw [Matrix.det_conjTranspose]; exact star_ne_zero.2 hB), Matrix.det_conjTranspose,
      Complex.star_def, Complex.normSq_conj]
  have key : ∀ z : EuclideanSpace ℝ η × EuclideanSpace ℝ η, psiLp H (Prod.map C C z) = mL (mR (psiLp H z)) := by
    intro z
    rw [hmLf, hmRf]
    simp only [psiLp_apply, Prod.map_fst, Prod.map_snd, hspec]
    have e1 : ∀ M : Matrix (Fin m) (Fin m) ℂ, (reimE (r := m) (m := m)).symm (reim M) = M :=
      fun M => (reimE (r := m) (m := m)).symm_apply_apply M
    rw [e1, e1]
    congr 1
    show _ = Bᴴ * ((Complex.I • H z.1 + H z.2) * B)
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  have hmC : Measurable C := C.continuous_of_finiteDimensional.measurable
  have hmP := psi_mp H hH hn hs
  have hmRm : Measurable mR := mR.continuous_of_finiteDimensional.measurable
  have hmLm : Measurable mL := mL.continuous_of_finiteDimensional.measurable
  have lhs : (volume : Measure (EuclideanSpace ℝ η × EuclideanSpace ℝ η)).map (psiLp H ∘ Prod.map C C) =
      (c * c) • volume := by
    rw [← Measure.map_map hmP.measurable (hmC.prodMap hmC), Measure.volume_eq_prod,
      ← Measure.map_prod_map _ _ hmC hmC, hC, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
      Measure.map_smul, ← Measure.volume_eq_prod, hmP.map_eq]
    exact hmP.measurable.aemeasurable
  have rhs : (volume : Measure (EuclideanSpace ℝ η × EuclideanSpace ℝ η)).map (psiLp H ∘ Prod.map C C) =
      (ENNReal.ofReal (Complex.normSq B.det ^ m)⁻¹ * ENNReal.ofReal (Complex.normSq B.det ^ m)⁻¹) • volume := by
    have : (psiLp H ∘ Prod.map C C) = mL ∘ mR ∘ psiLp H := funext key
    rw [this, ← Measure.map_map hmLm (hmRm.comp hmP.measurable), ← Measure.map_map hmRm hmP.measurable,
      hmP.map_eq, hR, Measure.map_smul, hL, smul_smul]
    exact hmLm.aemeasurable
  have hball := lhs.symm.trans rhs
  have hv := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin m × Fin m × Bool)) => μ (Metric.ball 0 1)) hball
  simp only [Measure.smul_apply, smul_eq_mul] at hv
  have hpos : (volume : Measure (EuclideanSpace ℝ (Fin m × Fin m × Bool))) (Metric.ball 0 1) ≠ 0 :=
    (Metric.measure_ball_pos _ _ one_pos).ne'
  have hfin : (volume : Measure (EuclideanSpace ℝ (Fin m × Fin m × Bool))) (Metric.ball 0 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have hcc := (ENNReal.mul_left_inj hpos hfin).1 hv
  have q0 : 0 ≤ (Complex.normSq B.det ^ m)⁻¹ := inv_nonneg.2 (pow_nonneg (Complex.normSq_nonneg _) _)
  rw [hc, ← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_mul q0,
    ENNReal.ofReal_eq_ofReal_iff (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (mul_nonneg q0 q0),
    mul_self_inj (abs_nonneg _) q0] at hcc
  rw [hC, hc, hcc]
end PI.AprimeInfW
end
end

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Matrix

def sgn {n : ℕ} (ε : Fin n → Bool) (i : Fin n) : ℂ := if ε i then 1 else -1

theorem sgn_mul_self {n : ℕ} (ε : Fin n → Bool) (i : Fin n) : sgn ε i * sgn ε i = 1 := by
  unfold sgn
  split_ifs <;> norm_num

theorem star_sgn {n : ℕ} (ε : Fin n → Bool) (i : Fin n) : star (sgn ε i) = sgn ε i := by
  unfold sgn
  split_ifs <;> simp

theorem star_I' : star Complex.I = -Complex.I := Complex.conj_I

theorem norm_sgn {n : ℕ} (ε : Fin n → Bool) (i : Fin n) : ‖sgn ε i‖ = 1 := by
  unfold sgn
  split_ifs <;> simp

theorem lie_apply {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (Mᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * M) i j = star (M j i) * sgn ε j + sgn ε i * M i j := by
  simp only [Matrix.add_apply, Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.conjTranspose_apply, sgn]

def cpx {k m : ℕ} (u : EuclideanSpace ℝ (Fin k × Fin m × Bool)) (a : Fin k) (b : Fin m) : ℂ :=
  ⟨u (a, b, true), u (a, b, false)⟩

theorem cpx_add {k m : ℕ} (u v : EuclideanSpace ℝ (Fin k × Fin m × Bool)) (a b) :
    cpx (u + v) a b = cpx u a b + cpx v a b := by
  apply Complex.ext <;> simp [cpx]

theorem cpx_smul {k m : ℕ} (c : ℝ) (u : EuclideanSpace ℝ (Fin k × Fin m × Bool)) (a b) :
    cpx (c • u) a b = (c : ℂ) * cpx u a b := by
  apply Complex.ext <;> simp [cpx]

theorem cpx_eq {k m : ℕ} (u : EuclideanSpace ℝ (Fin k × Fin m × Bool)) :
    Matrix.of (cpx u) = Matrix.of ((reimE (r := k) (m := m)).symm u) := rfl

theorem cpx_reim {k m : ℕ} (Y : Matrix (Fin k) (Fin m) ℂ) (a b) : cpx (reim Y) a b = Y a b := by
  apply Complex.ext <;> simp [cpx, reim]

theorem norm_cpx_sq {k m : ℕ} (u : EuclideanSpace ℝ (Fin k × Fin m × Bool)) :
    ‖u‖ ^ 2 = ∑ a, ∑ b, ‖cpx u a b‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Fintype.sum_bool, Complex.sq_norm, Complex.normSq_apply]
  simp [cpx, Real.norm_eq_abs, sq]

def r2 : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

theorem inv_sqrt_two_mul : r2 * (Real.sqrt 2 : ℂ) = 1 := by
  rw [r2, ← Complex.ofReal_mul, inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr two_pos), Complex.ofReal_one]

theorem norm_inv_sqrt_two_sq : ‖r2‖ ^ 2 = 1 / 2 := by
  rw [r2, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt (by norm_num)]
  norm_num

variable {n k m : ℕ} (ε : Fin n → Bool) (S : Finset (Fin n)) (eS : Fin k ≃ {i // i ∈ S})
  (eU : Fin m ≃ {i // i ∉ S}) {η : Type} [Fintype η] (H : EuclideanSpace ℝ η →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ)

def xiF (z : EuclideanSpace ℝ (Fin k × Fin m × Bool) × EuclideanSpace ℝ η) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j =>
    if hi : i ∈ S then (if hj : j ∈ S then 0 else r2 * cpx z.1 (eS.symm ⟨i, hi⟩) (eU.symm ⟨j, hj⟩))
    else (if hj : j ∈ S then -(sgn ε i * sgn ε j) * star (r2 * cpx z.1 (eS.symm ⟨j, hj⟩) (eU.symm ⟨i, hi⟩))
      else sgn ε i * Complex.I * H z.2 (eU.symm ⟨i, hi⟩) (eU.symm ⟨j, hj⟩))

def xiL : EuclideanSpace ℝ (Fin k × Fin m × Bool) × EuclideanSpace ℝ η →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := xiF ε S eS eU H
  map_add' a b := by
    ext i j
    simp only [xiF, Matrix.add_apply]
    split_ifs <;> (try simp [cpx_add]) <;> ring
  map_smul' c z := by
    ext i j
    simp only [xiF, Matrix.smul_apply, RingHom.id_apply]
    split_ifs <;> (try simp [cpx_smul, Complex.real_smul, Complex.conj_ofReal]) <;> ring

theorem xi_SS (z) (a b : Fin k) : xiF ε S eS eU H z (eS a) (eS b) = 0 := by
  simp [xiF, (eS a).2, (eS b).2]

theorem xi_SU (z) (a : Fin k) (b : Fin m) : xiF ε S eS eU H z (eS a) (eU b) = r2 * cpx z.1 a b := by
  simp [xiF, (eS a).2, (eU b).2]

theorem xi_US (z) (a : Fin m) (b : Fin k) :
    xiF ε S eS eU H z (eU a) (eS b) = -(sgn ε (eU a) * sgn ε (eS b)) * star (r2 * cpx z.1 b a) := by
  simp [xiF, (eU a).2, (eS b).2]

theorem xi_UU (z) (a b : Fin m) : xiF ε S eS eU H z (eU a) (eU b) = sgn ε (eU a) * Complex.I * H z.2 a b := by
  simp [xiF, (eU a).2, (eU b).2]

theorem sum_split {M : Type} [AddCommMonoid M] (f : Fin n → M) : ∑ i, f i = ∑ a, f (eS a) + ∑ a, f (eU a) := by
  have h : ∑ i, f i = ∑ x : ↥S, f ↑x + ∑ x : {i // i ∉ S}, f ↑x := by
    convert (Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ S) f).symm
  exact h.trans (congrArg₂ (· + ·) (eS.sum_comp (fun x => f x)).symm (eU.sum_comp (fun x => f x)).symm)

theorem xi_norm (hn : ∀ t, ∑ i, ∑ j, ‖H t i j‖ ^ 2 = ‖t‖ ^ 2) (z) :
    ∑ i, ∑ j, ‖xiF ε S eS eU H z i j‖ ^ 2 = ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 := by
  simp only [sum_split S eS eU, xi_SS, xi_SU, xi_US, xi_UU, norm_zero, norm_mul, norm_neg, norm_star,
    norm_sgn, Complex.norm_I, mul_pow, norm_inv_sqrt_two_sq, one_mul, mul_one]
  rw [norm_cpx_sq z.1, ← hn z.2]
  have hc : ∑ x : Fin m, ∑ y : Fin k, ‖cpx z.1 y x‖ ^ 2 = ∑ y : Fin k, ∑ x : Fin m, ‖cpx z.1 y x‖ ^ 2 :=
    Finset.sum_comm
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero, zero_add,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hc]
  ring

theorem xi_mem (hH : ∀ t, (H t)ᴴ = H t) (z) :
    (xiF ε S eS eU H z)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * xiF ε S eS eU H z = 0 ∧
      ∀ i ∈ S, ∀ j ∈ S, xiF ε S eS eU H z i j = 0 := by
  refine ⟨?_, fun i hi j hj => by simp [xiF, hi, hj]⟩
  have hHe : ∀ a b, star (H z.2 b a) = H z.2 a b := fun a b => by
    have h := congrFun (congrFun (hH z.2) a) b
    rwa [Matrix.conjTranspose_apply] at h
  ext i j
  rw [lie_apply, Matrix.zero_apply]
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
  · simp [xiF, hi, hj]
  · simp only [xiF, dif_pos hi, dif_neg hj, star_mul', star_neg, star_star, star_sgn]
    linear_combination (-(sgn ε i) * (r2 * cpx z.1 (eS.symm ⟨i, hi⟩) (eU.symm ⟨j, hj⟩))) * sgn_mul_self ε j
  · simp only [xiF, dif_pos hj, dif_neg hi, star_mul']
    linear_combination (-(sgn ε j) * (star r2 * star (cpx z.1 (eS.symm ⟨j, hj⟩) (eU.symm ⟨i, hi⟩)))) * sgn_mul_self ε i
  · simp only [xiF, dif_neg hi, dif_neg hj, star_mul', star_sgn, star_I', hHe]
    linear_combination (Complex.I * (H z.2 (eU.symm ⟨i, hi⟩) (eU.symm ⟨j, hj⟩))) * sgn_mul_self ε i - (Complex.I * (H z.2 (eU.symm ⟨i, hi⟩) (eU.symm ⟨j, hj⟩))) * sgn_mul_self ε j

theorem xi_onto (hs : ∀ M : Matrix (Fin m) (Fin m) ℂ, Mᴴ = M → ∃ t, H t = M) (ξ : Matrix (Fin n) (Fin n) ℂ)
    (h1 : ξᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * ξ = 0) (h2 : ∀ i ∈ S, ∀ j ∈ S, ξ i j = 0) :
    ∃ z, xiF ε S eS eU H z = ξ := by
  have hξ : ∀ i j, star (ξ j i) * sgn ε j + sgn ε i * ξ i j = 0 := fun i j => by
    have h := congrFun (congrFun h1 i) j
    rwa [lie_apply, Matrix.zero_apply] at h
  let u : EuclideanSpace ℝ (Fin k × Fin m × Bool) :=
    reim (Matrix.of fun a b => (Real.sqrt 2 : ℂ) * ξ (eS a) (eU b))
  let M : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun a b => -Complex.I * sgn ε (eU a) * ξ (eU a) (eU b)
  have hM : Mᴴ = M := by
    ext a b
    simp only [M, Matrix.conjTranspose_apply, Matrix.of_apply, star_mul', star_neg, star_I', star_sgn]
    linear_combination Complex.I * hξ (eU a) (eU b)
  obtain ⟨t, ht⟩ := hs M hM
  have e2 : ∀ w : ℂ, r2 * ((Real.sqrt 2 : ℂ) * w) = w := fun w => by rw [← mul_assoc, inv_sqrt_two_mul, one_mul]
  refine ⟨(u, t), ?_⟩
  ext i j
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
  · simp [xiF, hi, hj, h2 i hi j hj]
  · simp only [xiF, dif_pos hi, dif_neg hj, u, cpx_reim, Matrix.of_apply, Equiv.apply_symm_apply, e2]
  · simp only [xiF, dif_neg hi, dif_pos hj, u, cpx_reim, Matrix.of_apply, Equiv.apply_symm_apply, e2]
    linear_combination (-(sgn ε i)) * hξ i j + ξ i j * sgn_mul_self ε i
  · simp only [xiF, dif_neg hi, dif_neg hj, ht, M, Matrix.of_apply, Equiv.apply_symm_apply]
    linear_combination (-(sgn ε i) ^ 2 * ξ i j) * Complex.I_sq + ξ i j * sgn_mul_self ε i

theorem dom_exists {ι : Type} [Fintype ι] (L : EuclideanSpace ℝ ι →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ)
    (hL : ∀ x, (L x)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * L x = 0 ∧ ∀ i ∈ S, ∀ j ∈ S, L x i j = 0)
    (hnL : ∀ x, ∑ i, ∑ j, ‖L x i j‖ ^ 2 = ‖x‖ ^ 2)
    (hLs : ∀ M : Matrix (Fin n) (Fin n) ℂ, Mᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * M = 0 →
      (∀ i ∈ S, ∀ j ∈ S, M i j = 0) → ∃ x, L x = M)
    (hH : ∀ t, (H t)ᴴ = H t) (hnH : ∀ t, ∑ i, ∑ j, ‖H t i j‖ ^ 2 = ‖t‖ ^ 2)
    (hsH : ∀ M : Matrix (Fin m) (Fin m) ℂ, Mᴴ = M → ∃ t, H t = M) :
    ∃ Λ : EuclideanSpace ℝ (Fin k × Fin m × Bool) × EuclideanSpace ℝ η →ₗ[ℝ] EuclideanSpace ℝ ι,
      MeasurePreserving Λ volume volume ∧ ∀ z, L (Λ z) = xiF ε S eS eU H z := by
  have hxi : ∀ z, ∃ x, L x = xiL ε S eS eU H z := fun z =>
    hLs _ (xi_mem ε S eS eU H hH z).1 (xi_mem ε S eS eU H hH z).2
  let Λ := liftL L (inj_of_frob L hnL) (xiL ε S eS eU H) hxi
  have hΛ : ∀ z, L (Λ z) = xiF ε S eS eU H z := fun z => liftL_spec L (inj_of_frob L hnL) _ hxi z
  refine ⟨Λ, mp_of_isom_prod Λ (fun a b => ?_) ?_, hΛ⟩
  · rw [← hnL, hΛ]
    exact xi_norm ε S eS eU H hnH (a, b)
  · intro x
    obtain ⟨z, hz⟩ := xi_onto ε S eS eU H hsH (L x) (hL x).1 (hL x).2
    exact ⟨z, inj_of_frob L hnL ((hΛ z).trans hz)⟩

end PI.AprimeInfW
end
end

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Matrix

variable {n k m : ℕ} (S : Finset (Fin n)) (eS : Fin k ≃ {i // i ∈ S}) (eU : Fin m ≃ {i // i ∉ S})

def rowsM (X : Matrix (Fin k) (Fin m) ℂ) (Y : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin n) (Fin m) ℂ :=
  fun i j => if hi : i ∈ S then X (eS.symm ⟨i, hi⟩) j else Y (eU.symm ⟨i, hi⟩) j

theorem rowsM_S (X Y) (a : Fin k) (j) : rowsM S eS eU X Y (eS a) j = X a j := by
  simp [rowsM]

theorem rowsM_U (X Y) (a : Fin m) (j) : rowsM S eS eU X Y (eU a) j = Y a j := by
  simp [rowsM, (eU a).2]

theorem rows_ext {p : Type} (X Y : Matrix (Fin n) p ℂ) (h1 : ∀ a j, X (eS a) j = Y (eS a) j)
    (h2 : ∀ a j, X (eU a) j = Y (eU a) j) : X = Y := by
  ext i j
  by_cases hi : i ∈ S
  · simpa using h1 (eS.symm ⟨i, hi⟩) j
  · simpa using h2 (eU.symm ⟨i, hi⟩) j

theorem of_cpx_reim {a b : ℕ} (X : Matrix (Fin a) (Fin b) ℂ) : Matrix.of (cpx (reim X)) = X := by
  ext a b
  simp [cpx_reim]

def rsL : EuclideanSpace ℝ (Fin k × Fin m × Bool) × EuclideanSpace ℝ (Fin m × Fin m × Bool) →ₗ[ℝ]
    EuclideanSpace ℝ (Fin n × Fin m × Bool) where
  toFun z := reim (rowsM S eS eU (Matrix.of (cpx z.1)) (Matrix.of (cpx z.2)))
  map_add' a b := by
    ext p
    rcases p with ⟨i, j, c⟩
    by_cases hi : i ∈ S <;> cases c <;> simp [reim, rowsM, hi, cpx]
  map_smul' r z := by
    ext p
    rcases p with ⟨i, j, c⟩
    by_cases hi : i ∈ S <;> cases c <;> simp [reim, rowsM, hi, cpx]

theorem rsL_apply (z) : rsL S eS eU z = reim (rowsM S eS eU (Matrix.of (cpx z.1)) (Matrix.of (cpx z.2))) := rfl

theorem rs_mp : MeasurePreserving (rsL S eS eU) volume volume := by
  apply mp_of_isom_prod
  · intro a b
    rw [rsL_apply, norm_reim_sq, sum_split S eS eU, norm_cpx_sq a, norm_cpx_sq b]
    simp [rowsM_S, rowsM_U]
  · intro y
    obtain ⟨Y, rfl⟩ := reim_surj y
    refine ⟨(reim (Matrix.of fun a j => Y (eS a) j), reim (Matrix.of fun a j => Y (eU a) j)), ?_⟩
    rw [rsL_apply, of_cpx_reim, of_cpx_reim]
    congr 1
    apply rows_ext S eS eU
    · intro a j
      rw [rowsM_S]
      rfl
    · intro a j
      rw [rowsM_U]
      rfl

end PI.AprimeInfW
