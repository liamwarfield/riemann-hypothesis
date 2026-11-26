module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceCmbMulCmbStar
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

noncomputable section

namespace GlobalTheory.IwConst.Adapted

variable {n a b c e : ℕ}

theorem trace_cmb_mul_cmb {E : Fin a → Matrix (Fin n) (Fin n) ℂ} {F : Fin b → Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ i k, (E i * F k).trace = 0) (x : Fin a → ℝ) (y : Fin b → ℝ) : (cmb E x * cmb F y).trace = 0 := by
  simp [cmb, Finset.sum_mul, Finset.mul_sum, Matrix.trace_sum, h]

theorem trace_cmb_mul_cmb_star {E : Fin a → Matrix (Fin n) (Fin n) ℂ} {F : Fin b → Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ i k, (E i * (F k)ᴴ).trace = 0) (x : Fin a → ℝ) (y : Fin b → ℝ) : (cmb E x * (cmb F y)ᴴ).trace = 0 := by
  simp [cmb, Matrix.conjTranspose_sum, Finset.sum_mul, Finset.mul_sum, Matrix.trace_sum, h]

theorem trace_star_star (X Y : Matrix (Fin n) (Fin n) ℂ) (h : (X * Y).trace = 0) : (Xᴴ * Yᴴ).trace = 0 := by
  rw [← Matrix.conjTranspose_mul, Matrix.trace_conjTranspose, Matrix.trace_mul_comm, h, star_zero]

theorem hs_neg_star (X : Matrix (Fin n) (Fin n) ℂ) : Formalism.REAL.hs (-Xᴴ) = Formalism.REAL.hs X := by
  rw [← nrm_sq, ← nrm_sq, nrm_neg, nrm_conjTranspose]

theorem hs_three {EN : Fin a → Matrix (Fin n) (Fin n) ℂ} {EM : Fin b → Matrix (Fin n) (Fin n) ℂ}
    (hN : IsON EN) (hM : IsON EM) (h1 : ∀ i k, (EN i * (EM k)ᴴ).trace = 0) (h2 : ∀ i k, (EN i * EM k).trace = 0)
    (h3 : ∀ i k, (EN i * EN k).trace = 0) (x u : Fin a → ℝ) (y : Fin b → ℝ) :
    Formalism.REAL.hs (cmb EN x + cmb EM y + -(cmb EN u)ᴴ) = ∑ i, x i ^ 2 + ∑ i, y i ^ 2 + ∑ i, u i ^ 2 := by
  have e2 : (cmb EM y * cmb EN u).trace = 0 := by
    rw [Matrix.trace_mul_comm]; exact trace_cmb_mul_cmb h2 u y
  rw [hs_add, hs_add, hs_neg_star, hs_cmb hN, hs_cmb hM, hs_cmb hN, trace_cmb_mul_cmb_star h1]
  simp [Matrix.add_mul, trace_cmb_mul_cmb h3, e2]

def cmbL (E : Fin a → Matrix (Fin n) (Fin n) ℂ) : (Fin a → ℝ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := cmb E
  map_add' := cmb_add E
  map_smul' := cmb_smul E

def crdL (E : Fin a → Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (Fin a → ℝ) where
  toFun := crd E
  map_add' := crd_add E
  map_smul' := crd_smul E

def adp (EN : Fin a → Matrix (Fin n) (Fin n) ℂ) (EL : Fin e → Matrix (Fin n) (Fin n) ℂ) :
    ((Fin a → ℝ) × (Fin e → ℝ)) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun v := cmb EN ((Real.sqrt 2)⁻¹ • v.1) - (cmb EN ((Real.sqrt 2)⁻¹ • v.1))ᴴ + cmb EL v.2
  map_add' v w := by
    simp only [Prod.fst_add, Prod.snd_add, smul_add, cmb_add, Matrix.conjTranspose_add]; abel
  map_smul' r v := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_comm (Real.sqrt 2)⁻¹ r, cmb_smul EN r, cmb_smul EL r,
      Matrix.conjTranspose_smul, star_trivial, RingHom.id_apply, smul_add, smul_sub]

theorem cmb_mem_of {E : Fin a → Matrix (Fin n) (Fin n) ℂ} {S : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)}
    (h : ∀ i, E i ∈ S) (x : Fin a → ℝ) : cmb E x ∈ S :=
  Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h i)

theorem cmb_sub_star_mem {E : Fin a → Matrix (Fin n) (Fin n) ℂ} {S : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)}
    (h : ∀ i, E i - (E i)ᴴ ∈ S) (x : Fin a → ℝ) : cmb E x - (cmb E x)ᴴ ∈ S := by
  have : cmb E x - (cmb E x)ᴴ = cmb (fun i => E i - (E i)ᴴ) x := by
    simp [cmb, Matrix.conjTranspose_sum, smul_sub, Finset.sum_sub_distrib]
  rw [this]; exact cmb_mem_of h x

theorem sum_sq_half (w : Fin a → ℝ) : ∑ i, ((Real.sqrt 2)⁻¹ • w) i ^ 2 = ∑ i, w i ^ 2 / 2 := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_pow, inv_pow, Real.sq_sqrt (by norm_num)]
  ring

theorem exists_adapted (n : ℕ) (dN dM dK dL : ℕ) (EN : Fin dN → Matrix (Fin n) (Fin n) ℂ)
    (EM : Fin dM → Matrix (Fin n) (Fin n) ℂ) (EK : Fin dK → Matrix (Fin n) (Fin n) ℂ)
    (EL : Fin dL → Matrix (Fin n) (Fin n) ℂ) (hN : IsON EN) (hM : IsON EM) (hK : IsON EK) (hL : IsON EL)
    (hR : LieRel EN EM EK EL) (hd : dK = dN + dL) :
    ∃ (Q : (Fin dK → ℝ) →ₗ[ℝ] (Fin dN → ℝ) × (Fin dL → ℝ)) (ι : (Fin dL → ℝ) →ₗ[ℝ] (Fin dM → ℝ)),
      (∀ z, ∑ i, (Q z).1 i ^ 2 + ∑ i, (Q z).2 i ^ 2 = ∑ i, z i ^ 2) ∧
      ∀ x y z, Formalism.REAL.hs (cmb EN x + cmb EM y + cmb EK z) =
        ∑ i, (x i + (Q z).1 i / Real.sqrt 2) ^ 2 + ∑ i, (y i + ι (Q z).2 i) ^ 2 + ∑ i, (Q z).1 i ^ 2 / 2 ∧
        crd EL (cmb EK z) = (Q z).2 := by
  obtain ⟨h1, h2, h3, h4, h5, -, h7⟩ := hR
  have hι : ∀ t, cmb EM (crd EM (cmb EL t)) = cmb EL t := fun t => cmb_crd hM (cmb_mem_of h4 t)
  have hmem : ∀ v, adp EN EL v ∈ Submodule.span ℝ (Set.range EK) := fun v =>
    Submodule.add_mem _ (cmb_sub_star_mem h7 _) (cmb_mem_of h5 _)
  have hsum : ∀ x y v, Formalism.REAL.hs (cmb EN x + cmb EM y + adp EN EL v) =
      ∑ i, (x i + v.1 i / Real.sqrt 2) ^ 2 + ∑ i, (y i + crd EM (cmb EL v.2) i) ^ 2 + ∑ i, v.1 i ^ 2 / 2 := by
    intro x y v
    have e : cmb EN x + cmb EM y + adp EN EL v = cmb EN (x + (Real.sqrt 2)⁻¹ • v.1) +
        cmb EM (y + crd EM (cmb EL v.2)) + -(cmb EN ((Real.sqrt 2)⁻¹ • v.1))ᴴ := by
      rw [cmb_add, cmb_add, hι]
      simp only [adp, LinearMap.coe_mk, AddHom.coe_mk]
      abel
    rw [e, hs_three hN hM h1 h2 h3, sum_sq_half]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]
  have hhs : ∀ v, Formalism.REAL.hs (adp EN EL v) = ∑ i, v.1 i ^ 2 + ∑ i, v.2 i ^ 2 := by
    intro v
    have e : adp EN EL v = cmb EN ((Real.sqrt 2)⁻¹ • v.1) +
        cmb EM (crd EM (cmb EL v.2)) + -(cmb EN ((Real.sqrt 2)⁻¹ • v.1))ᴴ := by
      rw [hι]
      simp only [adp, LinearMap.coe_mk, AddHom.coe_mk]
      abel
    rw [e, hs_three hN hM h1 h2 h3, sum_sq_half, ← hs_cmb hM, hι, hs_cmb hL, ← Finset.sum_div]
    ring
  let T : ((Fin dN → ℝ) × (Fin dL → ℝ)) →ₗ[ℝ] (Fin dK → ℝ) := (crdL EK).comp (adp EN EL)
  have hT : ∀ v, cmb EK (T v) = adp EN EL v := fun v => cmb_crd hK (hmem v)
  have hinj : Function.Injective T := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro v hv
    have h := hhs v
    rw [← hT, hv, hs_cmb hK] at h
    simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero] at h
    have p1 : 0 ≤ ∑ i, v.1 i ^ 2 := by positivity
    have p2 : 0 ≤ ∑ i, v.2 i ^ 2 := by positivity
    have q1 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (v.1 i)).1
      (show ∑ i, v.1 i ^ 2 = 0 by linarith)
    have q2 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (v.2 i)).1
      (show ∑ i, v.2 i ^ 2 = 0 by linarith)
    ext i
    · exact pow_eq_zero_iff two_ne_zero |>.1 (q1 i (Finset.mem_univ i))
    · exact pow_eq_zero_iff two_ne_zero |>.1 (q2 i (Finset.mem_univ i))
  have hdim : Module.finrank ℝ ((Fin dN → ℝ) × (Fin dL → ℝ)) = Module.finrank ℝ (Fin dK → ℝ) := by
    simp [hd]
  let U := LinearMap.linearEquivOfInjective T hinj hdim
  have hU : ∀ z, cmb EK z = adp EN EL (U.symm z) := by
    intro z
    rw [← hT]
    congr 1
    exact (U.apply_symm_apply z).symm
  refine ⟨U.symm.toLinearMap, (crdL EM).comp (cmbL EL), fun z => ?_, fun x y z => ⟨?_, ?_⟩⟩
  · rw [← hs_cmb hK z, hU, hhs]; rfl
  · rw [hU, hsum]; rfl
  · rw [hU]
    change crd EL (_ - _ + _) = (U.symm z).2
    rw [crd_add, crd_cmb hL, add_eq_right]
    funext i
    simp only [crd, Pi.zero_apply]
    rw [← cmb_crd hM (h4 i), Matrix.sub_mul, Matrix.trace_sub, trace_cmb_mul_cmb_star h1,
      trace_star_star _ _ (trace_cmb_mul_cmb h2 _ _)]
    simp

end GlobalTheory.IwConst.Adapted
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingOfSumSqEq
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst

theorem measurePreserving_of_sum_sq_eq : ∀ (k a b : ℕ), k = a + b → ∀ Q : (Fin k → ℝ) →ₗ[ℝ] (Fin a → ℝ) × (Fin b → ℝ), (∀ z, ∑ i, (Q z).1 i ^ 2 + ∑ i, (Q z).2 i ^ 2 = ∑ i, z i ^ 2) → MeasurePreserving Q volume volume := by
  intro k a b hk Q hQ
  let L : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin a ⊕ Fin b) :=
    (WithLp.linearEquiv 2 ℝ (Fin a ⊕ Fin b → ℝ)).symm.toLinearMap ∘ₗ
      (LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin b) ℝ ℝ).symm.toLinearMap ∘ₗ Q ∘ₗ
      (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).toLinearMap
  have hL : ∀ z, ‖L z‖ = ‖z‖ := by
    intro z
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    simp only [Real.norm_eq_abs, sq_abs, Fintype.sum_sum_type]
    rw [← hQ z.ofLp]
    rfl
  let Li : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a ⊕ Fin b) := ⟨L, hL⟩
  have hd : Module.finrank ℝ (EuclideanSpace ℝ (Fin k))
      = Module.finrank ℝ (EuclideanSpace ℝ (Fin a ⊕ Fin b)) := by
    simp [hk]
  have h1 := (Li.toLinearIsometryEquiv hd).measurePreserving
  have h2 := PiLp.volume_preserving_toLp (Fin k)
  have h3 := PiLp.volume_preserving_ofLp (Fin a ⊕ Fin b)
  have h4 := volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin a ⊕ Fin b => ℝ)
  have h := h4.comp (h3.comp (h1.comp h2))
  exact h

end GlobalTheory.IwConst
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumeShearedBalls
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

noncomputable section

namespace GlobalTheory.IwConst.Shear

theorem vol_ball_type (κ : Type) [Fintype κ] (d : ℕ) (h : Fintype.card κ = d) :
    volume {x : κ → ℝ | ∑ i, x i ^ 2 ≤ 1} = ballVol d := by
  classical
  let e : κ ≃ Fin d := Fintype.equivFinOfCardEq h
  have h1 := (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e).measurePreserving
  have h2 := PiLp.volume_preserving_toLp κ
  have h3 := (h1.comp h2).measure_preimage
    (s := Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) measurableSet_closedBall.nullMeasurableSet
  unfold ballVol
  rw [← Measure.addHaar_unitClosedBall_eq_addHaar_unitBall, ← h3]
  congr 1
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Function.comp_apply, mem_closedBall_zero_iff,
    LinearIsometryEquiv.norm_map, EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs, Real.sqrt_le_one]

theorem vol_ball_three (a b : ℕ) :
    volume {p : ((Fin a → ℝ) × (Fin b → ℝ)) × (Fin a → ℝ) |
      ∑ i, p.1.1 i ^ 2 + ∑ i, p.1.2 i ^ 2 + ∑ i, p.2 i ^ 2 ≤ 1} = ballVol (2 * a + b) := by
  rw [← vol_ball_type ((Fin a ⊕ Fin b) ⊕ Fin a) (2 * a + b) (by simp; ring)]
  have h1 := volume_measurePreserving_sumPiEquivProdPi (fun _ : (Fin a ⊕ Fin b) ⊕ Fin a => ℝ)
  have h2 := volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin a ⊕ Fin b => ℝ)
  have h3 := (h2.prod (MeasurePreserving.id (volume : Measure (Fin a → ℝ)))).comp h1
  have hm : MeasurableSet {p : ((Fin a → ℝ) × (Fin b → ℝ)) × (Fin a → ℝ) |
      ∑ i, p.1.1 i ^ 2 + ∑ i, p.1.2 i ^ 2 + ∑ i, p.2 i ^ 2 ≤ 1} :=
    measurableSet_le (by fun_prop) measurable_const
  have h4 := h3.measure_preimage hm.nullMeasurableSet
  rw [Measure.volume_eq_prod, ← h4]
  congr 1
  ext x
  simp [Fintype.sum_sum_type, MeasurableEquiv.sumPiEquivProdPi]

theorem vol_scale (a : ℕ) (q : ℝ) :
    volume {w : Fin a → ℝ | q + ∑ i, w i ^ 2 / 2 ≤ 1} =
      ENNReal.ofReal ((2 : ℝ) ^ ((a : ℝ) / 2)) * volume {w : Fin a → ℝ | q + ∑ i, w i ^ 2 ≤ 1} := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have h := Measure.addHaar_preimage_smul (volume : Measure (Fin a → ℝ)) (r := (Real.sqrt 2)⁻¹)
    (inv_ne_zero h2.ne') {w : Fin a → ℝ | q + ∑ i, w i ^ 2 ≤ 1}
  have e1 : |(((Real.sqrt 2)⁻¹) ^ Module.finrank ℝ (Fin a → ℝ))⁻¹| = (2 : ℝ) ^ ((a : ℝ) / 2) := by
    rw [Module.finrank_fin_fun, inv_pow, inv_inv, abs_of_pos (pow_pos h2 _), Real.sqrt_eq_rpow,
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1; ring
  rw [e1] at h
  rw [← h]
  congr 1
  ext w
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Pi.smul_apply, smul_eq_mul, mul_pow, inv_pow,
    Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  simp only [div_eq_inv_mul]

theorem vol_ell_three (a b : ℕ) :
    volume {p : ((Fin a → ℝ) × (Fin b → ℝ)) × (Fin a → ℝ) |
      ∑ i, p.1.1 i ^ 2 + ∑ i, p.1.2 i ^ 2 + ∑ i, p.2 i ^ 2 / 2 ≤ 1} =
      ENNReal.ofReal ((2 : ℝ) ^ ((a : ℝ) / 2)) * ballVol (2 * a + b) := by
  rw [← vol_ball_three]
  have hm : MeasurableSet {p : ((Fin a → ℝ) × (Fin b → ℝ)) × (Fin a → ℝ) |
      ∑ i, p.1.1 i ^ 2 + ∑ i, p.1.2 i ^ 2 + ∑ i, p.2 i ^ 2 ≤ 1} :=
    measurableSet_le (by fun_prop) measurable_const
  have hm' : MeasurableSet {p : ((Fin a → ℝ) × (Fin b → ℝ)) × (Fin a → ℝ) |
      ∑ i, p.1.1 i ^ 2 + ∑ i, p.1.2 i ^ 2 + ∑ i, p.2 i ^ 2 / 2 ≤ 1} :=
    measurableSet_le (by fun_prop) measurable_const
  rw [Measure.volume_eq_prod, Measure.prod_apply hm, Measure.prod_apply hm',
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun x => ?_
  exact vol_scale a (∑ i, x.1 i ^ 2 + ∑ i, x.2 i ^ 2)

theorem vol_shear {G Z : Type} [MeasurableSpace G] [AddCommGroup G] [MeasurableAdd₂ G] [MeasurableSpace Z]
    (μ : Measure G) [μ.IsAddRightInvariant] [SFinite μ] (ν : Measure Z) [SFinite ν] (f : Z → G)
    (hf : Measurable f) (s : Set (G × Z)) (hs : MeasurableSet s) :
    (μ.prod ν) {p | (p.1 + f p.2, p.2) ∈ s} = (μ.prod ν) s := by
  have hm : MeasurableSet {p : G × Z | (p.1 + f p.2, p.2) ∈ s} :=
    (show Measurable fun p : G × Z => (p.1 + f p.2, p.2) by fun_prop) hs
  rw [Measure.prod_apply_symm hm, Measure.prod_apply_symm hs]
  refine lintegral_congr fun z => ?_
  exact measure_preimage_add_right μ (f z) ((fun x => (x, z)) ⁻¹' s)

theorem volume_sheared_balls (a b c : ℕ) (ι : (Fin c → ℝ) →ₗ[ℝ] (Fin b → ℝ)) :
    volume {v : (Fin a → ℝ) × (Fin b → ℝ) × ((Fin a → ℝ) × (Fin c → ℝ)) |
      ∑ i, (v.1 i + v.2.2.1 i / Real.sqrt 2) ^ 2 + ∑ i, (v.2.1 i + ι v.2.2.2 i) ^ 2 +
        ∑ i, v.2.2.1 i ^ 2 / 2 ≤ 1 ∧ ∑ i, v.2.2.2 i ^ 2 ≤ 1} =
      ENNReal.ofReal ((2 : ℝ) ^ ((a : ℝ) / 2)) * ballVol (2 * a + b) * ballVol c := by
  have hι : Continuous ι := ι.continuous_of_finiteDimensional
  have hS : MeasurableSet {v : (Fin a → ℝ) × (Fin b → ℝ) × ((Fin a → ℝ) × (Fin c → ℝ)) |
      ∑ i, (v.1 i + v.2.2.1 i / Real.sqrt 2) ^ 2 + ∑ i, (v.2.1 i + ι v.2.2.2 i) ^ 2 +
        ∑ i, v.2.2.1 i ^ 2 / 2 ≤ 1 ∧ ∑ i, v.2.2.2 i ^ 2 ≤ 1} := by
    rw [Set.setOf_and]
    exact ((isClosed_le (by fun_prop) continuous_const).inter
      (isClosed_le (by fun_prop) continuous_const)).measurableSet
  have hs : MeasurableSet {v : ((Fin a → ℝ) × (Fin b → ℝ)) × ((Fin a → ℝ) × (Fin c → ℝ)) |
      ∑ i, v.1.1 i ^ 2 + ∑ i, v.1.2 i ^ 2 + ∑ i, v.2.1 i ^ 2 / 2 ≤ 1 ∧ ∑ i, v.2.2 i ^ 2 ≤ 1} := by
    rw [Set.setOf_and]
    exact ((isClosed_le (by fun_prop) continuous_const).inter
      (isClosed_le (by fun_prop) continuous_const)).measurableSet
  have h1 := (volume_preserving_prodAssoc (α₁ := Fin a → ℝ) (β₁ := Fin b → ℝ)
    (γ₁ := (Fin a → ℝ) × (Fin c → ℝ))).measure_preimage hS.nullMeasurableSet
  have h2 := vol_shear ((volume : Measure (Fin a → ℝ)).prod (volume : Measure (Fin b → ℝ)))
    (volume : Measure ((Fin a → ℝ) × (Fin c → ℝ)))
    (fun z => ((fun i => z.1 i / Real.sqrt 2), ι z.2)) (Continuous.measurable (by fun_prop)) _ hs
  have h3 := (volume_preserving_prodAssoc (α₁ := (Fin a → ℝ) × (Fin b → ℝ)) (β₁ := Fin a → ℝ)
    (γ₁ := Fin c → ℝ)).measure_preimage hs.nullMeasurableSet
  rw [← h1]
  refine (h2.trans h3.symm).trans ?_
  rw [← vol_ell_three, ← vol_ball_type (Fin c) c (Fintype.card_fin c), ← Measure.prod_prod]
  rfl

end GlobalTheory.IwConst.Shear
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaGaugeDefiniteAndUnitBodyVolume
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst

theorem gau_definite_and_volume : ∀ (n : ℕ), ∀ (dN dM dK dL : ℕ) (EN : Fin dN → Matrix (Fin n) (Fin n) ℂ) (EM : Fin dM → Matrix (Fin n) (Fin n) ℂ) (EK : Fin dK → Matrix (Fin n) (Fin n) ℂ) (EL : Fin dL → Matrix (Fin n) (Fin n) ℂ), IsON EN → IsON EM → IsON EK → IsON EL → LieRel EN EM EK EL → dK = dN + dL → (∀ v, gau EN EM EK EL v = 0 → v = 0) ∧ volume {v | gau EN EM EK EL v ≤ 1} = ENNReal.ofReal ((2 : ℝ) ^ ((dN : ℝ) / 2)) * ballVol (2 * dN + dM) * ballVol dL := by
  intro n dN dM dK dL EN EM EK EL hN hM hK hL hR hd
  obtain ⟨Q, ι, hQ, hh⟩ := GlobalTheory.IwConst.Adapted.exists_adapted n dN dM dK dL EN EM EK EL hN hM hK hL hR hd
  have sq0 : ∀ {d : ℕ} (f : Fin d → ℝ), ∑ i, f i ^ 2 ≤ 0 → f = 0 := by
    intro d f hf
    funext i
    have h0 : ∑ i, f i ^ 2 = 0 := le_antisymm hf (by positivity)
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (f i))).1 h0 i (Finset.mem_univ i)
    simpa using this
  constructor
  · rintro ⟨x, y, z⟩ hv
    obtain ⟨h1, h2⟩ := hh x y z
    have a1 : nrm (cmb EN x + cmb EM y + cmb EK z) ≤ 0 := (le_max_left _ _).trans hv.le
    have a2 : len (crd EL (cmb EK z)) ≤ 0 := (le_max_right _ _).trans hv.le
    have b1 : Formalism.REAL.hs (cmb EN x + cmb EM y + cmb EK z) = 0 := by
      rw [← nrm_sq, le_antisymm a1 (nrm_nonneg _)]; simp
    have b2 : ∑ i, (Q z).2 i ^ 2 = 0 := by
      rw [← h2, ← len_sq, le_antisymm a2 (len_nonneg _)]; simp
    rw [b1] at h1
    have p1 : 0 ≤ ∑ i, (x i + (Q z).1 i / Real.sqrt 2) ^ 2 := by positivity
    have p2 : 0 ≤ ∑ i, (y i + ι (Q z).2 i) ^ 2 := by positivity
    have p3 : 0 ≤ ∑ i, (Q z).1 i ^ 2 := by positivity
    rw [← Finset.sum_div] at h1
    have hz : z = 0 := sq0 z (by rw [← hQ z]; linarith)
    subst hz
    have hx : x = 0 := sq0 x (by
      simp only [map_zero, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, zero_div, add_zero, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero] at h1 p1 p2
      linarith)
    have hy : y = 0 := sq0 y (by
      simp only [map_zero, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, zero_div, add_zero, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero] at h1 p1 p2
      linarith)
    subst hx hy
    rfl
  · have hmp := GlobalTheory.IwConst.measurePreserving_of_sum_sq_eq dK dN dL hd Q hQ
    have hmp2 : MeasurePreserving (Prod.map id (Prod.map id Q) :
        (Fin dN → ℝ) × (Fin dM → ℝ) × (Fin dK → ℝ) →
          (Fin dN → ℝ) × (Fin dM → ℝ) × ((Fin dN → ℝ) × (Fin dL → ℝ))) volume volume :=
      (MeasurePreserving.id _).prod ((MeasurePreserving.id _).prod hmp)
    rw [← GlobalTheory.IwConst.Shear.volume_sheared_balls dN dM dL ι, ← hmp2.measure_preimage]
    · congr 1
      ext ⟨x, y, z⟩
      obtain ⟨h1, h2⟩ := hh x y z
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Prod.map, id, gau, max_le_iff, nrm, len,
        Real.sqrt_le_one, h1, h2]
    · refine (IsClosed.measurableSet ?_).nullMeasurableSet
      have hι : Continuous ι := ι.continuous_of_finiteDimensional
      refine IsClosed.and (isClosed_le ?_ continuous_const) (isClosed_le ?_ continuous_const)
      · fun_prop
      · fun_prop

end GlobalTheory.IwConst
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaGaugeDefiniteAndUnitBodyVolumeStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawaGauge_definite_and_unitBody_volume : ∀ (n : ℕ), ∀ (dN dM dK dL : ℕ) (EN : Fin dN → Matrix (Fin n) (Fin n) ℂ) (EM : Fin dM → Matrix (Fin n) (Fin n) ℂ) (EK : Fin dK → Matrix (Fin n) (Fin n) ℂ) (EL : Fin dL → Matrix (Fin n) (Fin n) ℂ), IsON EN → IsON EM → IsON EK → IsON EL → LieRel EN EM EK EL → dK = dN + dL → (∀ v, gau EN EM EK EL v = 0 → v = 0) ∧ volume {v | gau EN EM EK EL v ≤ 1} = ENNReal.ofReal ((2 : ℝ) ^ ((dN : ℝ) / 2)) * ballVol (2 * dN + dM) * ballVol dL := by
  first | exact @GlobalTheory.IwConst.gau_definite_and_volume | exact GlobalTheory.IwConst.gau_definite_and_volume | (intros; apply GlobalTheory.IwConst.gau_definite_and_volume <;> assumption)
end
