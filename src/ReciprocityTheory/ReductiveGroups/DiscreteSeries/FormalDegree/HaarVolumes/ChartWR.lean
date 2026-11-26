module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.TriDens
public import Lemmata.CurryModusPonens.CurryMp

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.ChartWRB
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.ChartWRA
noncomputable section

open Finset Matrix MeasureTheory Set

namespace ReciprocityTheory.ChartRestriction.DS

namespace ChartWRAux

theorem mp_curry (ι κ : Type*) [Fintype ι] [Fintype κ] :
    MeasurePreserving (Function.curry : (ι × κ → ℂ) → ι → κ → ℂ) volume volume := by
  first | exact Bl.CurryModusPonens.goal1 .. | (apply Bl.CurryModusPonens.goal1 <;> assumption) | (intros; apply Bl.CurryModusPonens.goal1 <;> assumption)

theorem mp_perm4 {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] (μa : Measure α) (μb : Measure β) (μc : Measure γ) (μd : Measure δ)
    [SigmaFinite μa] [SigmaFinite μb] [SigmaFinite μc] [SigmaFinite μd] :
    MeasurePreserving (fun p : (α × β) × (γ × δ) => ((p.2.1, p.1.1), (p.1.2, p.2.2)))
      ((μa.prod μb).prod (μc.prod μd)) ((μc.prod μa).prod (μb.prod μd)) := by
  have h1 := measurePreserving_prodAssoc μa μb (μc.prod μd)
  have h2 := (MeasurePreserving.id μa).prod
    ((measurePreserving_prodAssoc μb μc μd).symm _)
  have h3 := (MeasurePreserving.id μa).prod
    (((Measure.measurePreserving_swap (μ := μb) (ν := μc))).prod (MeasurePreserving.id μd))
  have h4 := (MeasurePreserving.id μa).prod (measurePreserving_prodAssoc μc μb μd)
  have h5 := (measurePreserving_prodAssoc μa μc (μb.prod μd)).symm _
  have h6 := (Measure.measurePreserving_swap (μ := μa) (ν := μc)).prod (MeasurePreserving.id (μb.prod μd))
  have h := h6.comp (h5.comp (h4.comp (h3.comp (h2.comp h1))))
  convert h using 1
  funext p
  rfl

abbrev Lo (N : ℕ) : Type := {ab : Fin N × Fin N // ab.2 < ab.1}

abbrev Up (N : ℕ) : Type := {ab : Fin N × Fin N // ab.1 < ab.2}

variable {N : ℕ}

local instance volTri : (volume : Measure (TriCo N)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _

def idx (N : ℕ) : Fin N ⊕ (Lo N ⊕ Up N) ≃ Fin N × Fin N where
  toFun i := match i with
    | Sum.inl a => (a, a)
    | Sum.inr (Sum.inl ab) => ab.1
    | Sum.inr (Sum.inr ab) => ab.1
  invFun ab := if h : ab.1 = ab.2 then Sum.inl ab.1 else if h' : ab.2 < ab.1 then Sum.inr (Sum.inl ⟨ab, h'⟩)
    else Sum.inr (Sum.inr ⟨ab, lt_of_le_of_ne (not_lt.1 h') h⟩)
  left_inv := by
    rintro (a | ⟨ab, h⟩ | ⟨ab, h⟩)
    · simp
    · simp [h.ne', h]
    · simp [h.ne, not_lt.2 h.le]
  right_inv := by
    rintro ⟨a, b⟩
    dsimp only
    split_ifs with h h'
    · simp [h]
    · rfl
    · rfl

def rho (p : UCo N × TriCo N) : Fin N → Fin N → ℂ := fun a b =>
  if a = b then ((p.2.1 a : ℝ) : ℂ) + ((p.1.1 a : ℝ) : ℂ) * Complex.I
  else if h : b < a then p.1.2 ⟨(a, b), h⟩ else if h' : a < b then p.2.2 ⟨(a, b), h'⟩ else 0

def e2 (q : (Fin N → ℝ) × (Fin N → ℝ)) : Fin N → ℂ := fun a => ⟨q.1 a, q.2 a⟩

theorem measurePreserving_second_reorder : MeasurePreserving (e2 (N := N)) volume volume := by
  have h1 := (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin N)).symm _
  have h2 := volume_preserving_pi (fun _ : Fin N => (Complex.volume_preserving_equiv_real_prod).symm _)
  exact h2.comp h1

def rho0 (p : UCo N × TriCo N) : Fin N → Fin N → ℂ :=
  Function.curry (MeasurableEquiv.piCongrLeft (fun _ : Fin N × Fin N => ℂ) (idx N)
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin N ⊕ (Lo N ⊕ Up N) => ℂ)).symm
      (e2 (p.2.1, p.1.1), (MeasurableEquiv.sumPiEquivProdPi (fun _ : Lo N ⊕ Up N => ℂ)).symm (p.1.2, p.2.2))))

theorem measurePreserving_rho_reorder : MeasurePreserving (rho0 (N := N)) volume volume := by
  have h1 := mp_perm4 (volume : Measure (Fin N → ℝ)) (volume : Measure (Lo N → ℂ))
    (volume : Measure (Fin N → ℝ)) (volume : Measure (Up N → ℂ))
  have h2 := (measurePreserving_second_reorder (N := N)).prod (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Lo N ⊕ Up N => ℂ))
  have h3 := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin N ⊕ (Lo N ⊕ Up N) => ℂ)
  have h4 := volume_measurePreserving_piCongrLeft (fun _ : Fin N × Fin N => ℂ) (idx N)
  have h5 := mp_curry (Fin N) (Fin N)
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

theorem rho_reorder_eq_rho : rho0 (N := N) = rho := by
  funext p a b
  have key : ∀ i, rho0 p (idx N i).1 (idx N i).2 =
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin N ⊕ (Lo N ⊕ Up N) => ℂ)).symm
        (e2 (p.2.1, p.1.1), (MeasurableEquiv.sumPiEquivProdPi (fun _ : Lo N ⊕ Up N => ℂ)).symm (p.1.2, p.2.2)) i :=
    fun i => MeasurableEquiv.piCongrLeft_apply_apply (idx N) (β := fun _ => ℂ) _ i
  rcases lt_trichotomy a b with h | rfl | h
  · have k := key (Sum.inr (Sum.inr ⟨(a, b), h⟩))
    simp only [rho, h.ne, not_lt.2 h.le, h, if_false, dif_neg, dif_pos, not_false_eq_true]
    exact k
  · have k := key (Sum.inl a)
    simp only [rho, if_true]
    refine k.trans ?_
    apply Complex.ext <;> simp <;> rfl
  · have k := key (Sum.inr (Sum.inl ⟨(a, b), h⟩))
    simp only [rho, h.ne', h, if_false, dif_pos]
    exact k

theorem mp_rho : MeasurePreserving (rho (N := N)) volume volume := by
  rw [← rho_reorder_eq_rho]; exact measurePreserving_rho_reorder

def sh (p : UCo N × TriCo N) : UCo N × TriCo N :=
  (p.1, (p.2.1, fun ab => p.2.2 ab - star (p.1.2 ⟨(ab.1.2, ab.1.1), ab.2⟩)))

theorem mp_sh : MeasurePreserving (sh (N := N)) volume volume := by
  have hc : Continuous (fun q : UCo N × TriCo N =>
      ((0 : Fin N → ℝ), fun ab : Up N => -star (q.1.2 ⟨(ab.1.2, ab.1.1), ab.2⟩)) + q.2) := by
    refine (continuous_const.prodMk (continuous_pi fun ab => ?_)).add continuous_snd
    exact ((continuous_apply _).comp (continuous_snd.comp continuous_fst)).star.neg
  have h := (MeasurePreserving.id (volume : Measure (UCo N))).skew_product
    (g := fun x (t : TriCo N) => ((0 : Fin N → ℝ), fun ab : Up N => -star (x.2 ⟨(ab.1.2, ab.1.1), ab.2⟩)) + t)
    (μc := (volume : Measure (TriCo N))) (μd := (volume : Measure (TriCo N)))
    hc.measurable (Filter.Eventually.of_forall fun x => map_add_left_eq_self (volume : Measure (TriCo N)) _)
  have e : sh (N := N) = fun p => (id p.1,
      ((0 : Fin N → ℝ), fun ab : Up N => -star (p.1.2 ⟨(ab.1.2, ab.1.1), ab.2⟩)) + p.2) := by
    funext p
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · simp [sh]
    · funext ab
      simp [sh, sub_eq_add_neg, add_comm]
  rw [e]; exact h

def lam (p : UCo N × TriCo N) : Fin N → Fin N → ℂ := Matrix.of.symm (skMat p.1 + upMat p.2)

theorem lam_eq : lam (N := N) = rho ∘ sh := by
  funext p a b
  simp only [lam, Function.comp_apply, rho, sh, Matrix.of_symm_apply, Matrix.add_apply, skMat, upMat]
  rcases lt_trichotomy a b with h | rfl | h
  · simp [h.ne, not_lt.2 h.le, h]; ring
  · simp; ring
  · simp [h.ne', h, not_lt.2 h.le]

theorem mp_lam : MeasurePreserving (lam (N := N)) volume volume := by
  rw [lam_eq]; exact mp_rho.comp mp_sh

def lamInv (Z : Fin N → Fin N → ℂ) : UCo N × TriCo N :=
  ((fun a => (Z a a).im, fun ab => Z ab.1.1 ab.1.2),
   (fun a => (Z a a).re, fun ab => Z ab.1.1 ab.1.2 + star (Z ab.1.2 ab.1.1)))

theorem lamInv_lam (p : UCo N × TriCo N) : lamInv (lam p) = p := by
  obtain ⟨⟨x1, x2⟩, ⟨t1, t2⟩⟩ := p
  simp only [lamInv, lam, Matrix.of_symm_apply, Matrix.add_apply, skMat, upMat]
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
  · funext a; simp
  · funext ab; obtain ⟨⟨a, b⟩, h⟩ := ab; simp [h.ne', h, not_lt.2 h.le]
  · funext a; simp
  · funext ab; obtain ⟨⟨a, b⟩, h⟩ := ab; simp [h.ne, h.ne', h, not_lt.2 h.le]

theorem lam_lamInv (Z : Fin N → Fin N → ℂ) : lam (lamInv Z) = Z := by
  funext a b
  simp only [lamInv, lam, Matrix.of_symm_apply, Matrix.add_apply, skMat, upMat]
  rcases lt_trichotomy a b with h | rfl | h
  · simp [h.ne, not_lt.2 h.le, h]
  · apply Complex.ext <;> simp
  · simp [h.ne', h, not_lt.2 h.le]

def lamL : (UCo N × TriCo N) →ₗ[ℝ] (Fin N → Fin N → ℂ) where
  toFun := lam
  map_add' p q := by
    funext a b
    simp only [lam, Matrix.of_symm_apply, Matrix.add_apply, skMat, upMat, Prod.fst_add, Prod.snd_add,
      Pi.add_apply]
    split_ifs <;> (try simp [star_add]) <;> (try ring)
  map_smul' c p := by
    funext a b
    simp only [lam, Matrix.of_symm_apply, Matrix.add_apply, skMat, upMat, Prod.smul_fst, Prod.smul_snd,
      Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> (try simp [Complex.real_smul]) <;> (try ring)

def lamE : (UCo N × TriCo N) ≃L[ℝ] (Fin N → Fin N → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { lamL with invFun := lamInv, left_inv := lamInv_lam, right_inv := lam_lamInv }

theorem lamE_apply (p : UCo N × TriCo N) : lamE p = lam p := rfl

end ChartWRAux

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset Matrix MeasureTheory Set

namespace ReciprocityTheory.ChartRestriction.DS

namespace ChartWRAux

variable {N : ℕ}

def skML : (UCo N × TriCo N) →ₗ[ℝ] Matrix (Fin N) (Fin N) ℂ where
  toFun p := skMat p.1
  map_add' p q := by
    ext a b
    simp only [skMat, Prod.fst_add, Pi.add_apply, Matrix.add_apply]
    split_ifs <;> (try simp [star_add]) <;> (try ring)
  map_smul' c p := by
    ext a b
    simp only [skMat, Prod.smul_fst, Pi.smul_apply, RingHom.id_apply, Matrix.smul_apply]
    split_ifs <;> (try simp [Complex.real_smul]) <;> (try ring)

def upML : (UCo N × TriCo N) →ₗ[ℝ] Matrix (Fin N) (Fin N) ℂ where
  toFun p := upMat p.2
  map_add' p q := by
    ext a b
    simp only [upMat, Prod.snd_add, Pi.add_apply, Matrix.add_apply]
    split_ifs <;> (try simp) <;> (try ring)
  map_smul' c p := by
    ext a b
    simp only [upMat, Prod.smul_snd, Pi.smul_apply, RingHom.id_apply, Matrix.smul_apply]
    split_ifs <;> (try simp [Complex.real_smul]) <;> (try ring)

section Deriv

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem chartWR_strict :
    HasStrictFDerivAt (chartWR (N := N))
      ((lamE : (UCo N × TriCo N) ≃L[ℝ] (Fin N → Fin N → ℂ)) : (UCo N × TriCo N) →L[ℝ] (Fin N → Fin N → ℂ)) 0 := by
  let skL : (UCo N × TriCo N) →L[ℝ] Matrix (Fin N) (Fin N) ℂ := LinearMap.toContinuousLinearMap skML
  let upL : (UCo N × TriCo N) →L[ℝ] Matrix (Fin N) (Fin N) ℂ := LinearMap.toContinuousLinearMap upML
  let ofL : Matrix (Fin N) (Fin N) ℂ →L[ℝ] (Fin N → Fin N → ℂ) :=
    LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).symm.toLinearMap
  have hsk0 : skL 0 = 0 := map_zero _
  have hup0 : upL 0 = 0 := map_zero _
  have h1 : HasStrictFDerivAt (fun p : UCo N × TriCo N => NormedSpace.exp (skL p))
      ((1 : Matrix (Fin N) (Fin N) ℂ →L[ℝ] Matrix (Fin N) (Fin N) ℂ).comp skL) 0 := by
    have he := hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := Matrix (Fin N) (Fin N) ℂ)
    rw [← hsk0] at he
    exact he.comp 0 skL.hasStrictFDerivAt
  have h2 : HasStrictFDerivAt (fun p : UCo N × TriCo N => 1 + upL p) upL 0 :=
    upL.hasStrictFDerivAt.const_add 1
  have h3 := h1.mul' h2
  have h4 := ofL.hasStrictFDerivAt.comp 0 h3
  have hF : (fun x => ofL (((fun p => NormedSpace.exp (skL p)) * fun p => 1 + upL p) x)) = chartWR := by
    funext p; rfl
  have hD : ofL.comp (NormedSpace.exp (skL 0) • upL + MulOpposite.op (1 + upL 0) •
      (1 : Matrix (Fin N) (Fin N) ℂ →L[ℝ] Matrix (Fin N) (Fin N) ℂ).comp skL) =
      ((lamE : (UCo N × TriCo N) ≃L[ℝ] (Fin N → Fin N → ℂ)) : (UCo N × TriCo N) →L[ℝ] (Fin N → Fin N → ℂ)) := by
    refine ContinuousLinearMap.ext fun p => ?_
    rw [hsk0, hup0, NormedSpace.exp_zero]
    simp
    exact (add_comm _ _).trans rfl
  rw [hF] at h4
  exact h4.congr_fderiv hD

end Deriv

end ChartWRAux

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset Matrix MeasureTheory Set Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

open ChartWRAux in
theorem chartWR_vol (η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, ∀ (B : Set (UCo N)) (E : Set (TriCo N)), MeasurableSet B → MeasurableSet E →
      (∀ x ∈ B, ‖x‖ < δ) → (∀ t ∈ E, ‖t‖ < δ) →
      volume (chartWR '' (B ×ˢ E)) ≤ ENNReal.ofReal (1 + η) * (volume B * volume E) ∧
        ENNReal.ofReal (1 - η) * (volume B * volume E) ≤ volume (chartWR '' (B ×ˢ E)) := by
  have : (volume : Measure (Fin N → Fin N → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  let L : (UCo N × TriCo N) →L[ℝ] (Fin N → Fin N → ℂ) := (lamE : (UCo N × TriCo N) ≃L[ℝ] _)
  let g : (Fin N → Fin N → ℂ) → (Fin N → Fin N → ℂ) := fun z => chartWR (lamE.symm z)
  have hg : HasStrictFDerivAt g (ContinuousLinearMap.id ℝ (Fin N → Fin N → ℂ)) 0 := by
    have hc : HasStrictFDerivAt (chartWR (N := N)) L (lamE.symm 0) := by
      rw [map_zero]; exact chartWR_strict
    have h := hc.comp (0 : Fin N → Fin N → ℂ)
      ((lamE.symm : (Fin N → Fin N → ℂ) ≃L[ℝ] (UCo N × TriCo N)) :
        (Fin N → Fin N → ℂ) →L[ℝ] (UCo N × TriCo N)).hasStrictFDerivAt
    rwa [ContinuousLinearEquiv.coe_comp_coe_symm] at h
  have hdet : ENNReal.ofReal |(ContinuousLinearMap.id ℝ (Fin N → Fin N → ℂ)).det| = 1 := by
    simp [ContinuousLinearMap.det, ContinuousLinearMap.coe_id]
  have ev1 := addHaar_image_le_mul_of_det_lt (μ := (volume : Measure (Fin N → Fin N → ℂ)))
    (ContinuousLinearMap.id ℝ (Fin N → Fin N → ℂ)) (m := (1 + η).toNNReal) (by
      rw [hdet]; exact_mod_cast (show (1 : ℝ) < (1 + η).toNNReal by
        rw [Real.coe_toNNReal _ (by linarith)]; linarith))
  have ev2 : ∀ᶠ δ in 𝓝[>] (0 : NNReal), ∀ (s : Set (Fin N → Fin N → ℂ)) (f : (Fin N → Fin N → ℂ) → (Fin N → Fin N → ℂ)),
      ApproximatesLinearOn f (ContinuousLinearMap.id ℝ (Fin N → Fin N → ℂ)) s δ →
        ENNReal.ofReal (1 - η) * volume s ≤ volume (f '' s) := by
    rcases lt_or_ge η 1 with h1 | h1
    · have := mul_le_addHaar_image_of_lt_det (μ := (volume : Measure (Fin N → Fin N → ℂ)))
        (ContinuousLinearMap.id ℝ (Fin N → Fin N → ℂ)) (m := (1 - η).toNNReal) (by
          rw [hdet]; exact_mod_cast (show ((1 - η).toNNReal : ℝ) < 1 by
            rw [Real.coe_toNNReal _ (by linarith)]; linarith))
      exact this
    · refine Filter.Eventually.of_forall fun δ s f _ => ?_
      rw [ENNReal.ofReal_of_nonpos (by linarith), zero_mul]; exact bot_le
  obtain ⟨c, ⟨hc1, hc2⟩, hcpos⟩ := ((ev1.and ev2).and self_mem_nhdsWithin).exists
  obtain ⟨s, hs, hap⟩ := hg.approximates_deriv_on_nhds (Or.inr hcpos)
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.1 hs
  have hL0 : 0 ≤ ‖L‖ := norm_nonneg _
  refine ⟨r / (‖L‖ + 1), by positivity, fun B E hB hE hBδ hEδ => ?_⟩
  have hLr : ‖L‖ * (r / (‖L‖ + 1)) < r := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
  have hball : (lamE : (UCo N × TriCo N) ≃L[ℝ] (Fin N → Fin N → ℂ)) '' (B ×ˢ E) ⊆ s := by
    rintro _ ⟨p, hp, rfl⟩
    apply hrs
    rw [Metric.mem_ball, dist_zero_right]
    have hp' : ‖p‖ < r / (‖L‖ + 1) := by
      rw [Prod.norm_def]; exact max_lt (hBδ _ hp.1) (hEδ _ hp.2)
    calc ‖lamE p‖ = ‖L p‖ := rfl
      _ ≤ ‖L‖ * ‖p‖ := L.le_opNorm p
      _ ≤ ‖L‖ * (r / (‖L‖ + 1)) := mul_le_mul_of_nonneg_left hp'.le hL0
      _ < r := hLr
  have hap' := hap.mono_set hball
  have himg : chartWR '' (B ×ˢ E) = g '' ((lamE : (UCo N × TriCo N) ≃L[ℝ] _) '' (B ×ˢ E)) := by
    rw [Set.image_image]
    refine Set.image_congr fun p _ => ?_
    simp [g]
  have hmp : MeasurePreserving (lamE : (UCo N × TriCo N) ≃L[ℝ] (Fin N → Fin N → ℂ)) volume volume := by
    have e : (⇑(lamE : (UCo N × TriCo N) ≃L[ℝ] (Fin N → Fin N → ℂ))) = lam := funext lamE_apply
    rw [e]; exact mp_lam
  have hme : MeasurableEmbedding (lamE : (UCo N × TriCo N) ≃L[ℝ] (Fin N → Fin N → ℂ)) :=
    lamE.toHomeomorph.measurableEmbedding
  have hvol : volume ((lamE : (UCo N × TriCo N) ≃L[ℝ] _) '' (B ×ˢ E)) = volume B * volume E := by
    calc volume ((lamE : (UCo N × TriCo N) ≃L[ℝ] _) '' (B ×ˢ E))
        = (Measure.map lamE volume) ((lamE : (UCo N × TriCo N) ≃L[ℝ] _) '' (B ×ˢ E)) := by
          rw [hmp.map_eq]
      _ = volume (lamE ⁻¹' ((lamE : (UCo N × TriCo N) ≃L[ℝ] _) '' (B ×ˢ E))) := hme.map_apply _ _
      _ = volume (B ×ˢ E) := by rw [Set.preimage_image_eq _ lamE.injective]
      _ = volume B * volume E := Measure.prod_prod _ _
  rw [himg]
  refine ⟨?_, ?_⟩
  · have := hc1 _ g hap'
    rw [hvol] at this
    exact this
  · have := hc2 _ g hap'
    rw [hvol] at this
    exact this

end ReciprocityTheory.ChartRestriction.DS
