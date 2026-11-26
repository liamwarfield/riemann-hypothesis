module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StSInt
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvGroup

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBePosB
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBePosA
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.BesselPositivity

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1

variable {k r : ℕ}

def sP (p : Mt k r × Mt k r) : Mat k r := Matrix.of p.2 * Matrix.of p.1

def SS (z : Fin (2 * r + k + 1) → ℂ) : Set (Mt k r × Mt k r) :=
  {p | (Matrix.of p.1 : Mat k r) ∈ UWset k r z ∧ (Matrix.of p.2 : Mat k r) ∈ Nset k r}

def Lq (q p : Mt k r × Mt k r) : Mt k r × Mt k r :=
  (lmulM (Matrix.of q.1) p.1, lmulM (Matrix.of q.2) (conjM (Matrix.of q.1) p.2))

def Sh (p : Mt k r × Mt k r) : Mt k r × Mt k r := (p.1, conjM (Matrix.of p.1)⁻¹ (invM p.2))

def Iv (p : Mt k r × Mt k r) : Mt k r × Mt k r := (invM (Sh p).1, (Sh p).2)

def Tm (p : Mt k r × (Mt k r × Mt k r)) : Mt k r × (Mt k r × Mt k r) :=
  (mulM (p.1, mulM (p.2.2, p.2.1)), p.2)

theorem bp_sf {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) : SigmaFinite μ := by
  have : IsFiniteMeasureOnCompacts μ := ⟨h.finite_compact⟩
  infer_instance

theorem bp_ae_mem {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) :
    ∀ᵐ x ∂μ, (Matrix.of x : Mat k r) ∈ U := by
  rw [ae_iff]; exact h.conc

theorem bp_ae_prod_and {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {ν : Measure β} [SFinite μ] [SFinite ν] {P : α → Prop} {Q : β → Prop} (hP : ∀ᵐ x ∂μ, P x)
    (hQ : ∀ᵐ y ∂ν, Q y) : ∀ᵐ p ∂(μ.prod ν), P p.1 ∧ Q p.2 :=
  (Measure.quasiMeasurePreserving_fst.ae hP).and (Measure.quasiMeasurePreserving_snd.ae hQ)

theorem bp_meas_inv : Measurable (invM (k := k) (r := r)) := by
  have hc : Continuous (fun g : Mt k r => (Matrix.of g : Mat k r)) := continuous_id
  have h1 : Measurable (fun g : Mt k r => ((Matrix.of g : Mat k r).det)⁻¹) :=
    (hc.matrix_det).measurable.inv
  have h2 : Continuous (fun g : Mt k r => Matrix.of.symm (Matrix.of g : Mat k r).adjugate) :=
    hc.matrix_adjugate
  have h3 : Measurable (fun g : Mt k r =>
      ((Matrix.of g : Mat k r).det)⁻¹ • Matrix.of.symm (Matrix.of g : Mat k r).adjugate) :=
    h1.smul h2.measurable
  convert h3 using 1
  funext g
  change (Matrix.of g : Mat k r)⁻¹ =
    (Matrix.of g : Mat k r).det⁻¹ • (Matrix.of g : Mat k r).adjugate
  rw [Matrix.inv_def, Ring.inverse_eq_inv']

theorem bp_cont_mul : Continuous (mulM (k := k) (r := r)) := by
  unfold mulM
  exact (continuous_fst (X := Mt k r) (Y := Mt k r)).matrix_mul continuous_snd

theorem bp_cont_gN : Continuous (fun g : Mat k r => gN g) := by
  unfold gN; fun_prop

theorem det_unit_G {g : Mat k r} (hg : g ∈ GV k r) : IsUnit g.det :=
  Matrix.isUnit_det_of_left_inverse (ConjugateNormInequalities.UH_left_inv k r hg)

theorem inv_mul_G {g : Mat k r} (hg : g ∈ GV k r) : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g (det_unit_G hg)

theorem mul_inv_G {g : Mat k r} (hg : g ∈ GV k r) : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g (det_unit_G hg)

theorem sP_mem {z : Fin (2 * r + k + 1) → ℂ} (hCG : ClosedG) {p : Mt k r × Mt k r} (hp : p ∈ SS z) :
    sP p ∈ GV k r :=
  (hCG k r).mul_mem _ hp.2.1 _ hp.1.1

theorem sP_Lq {z : Fin (2 * r + k + 1) → ℂ} {q : Mt k r × Mt k r} (hq : q ∈ SS z) (p : Mt k r × Mt k r) :
    sP (Lq q p) = sP q * sP p := by
  have h1 := inv_mul_G hq.1.1
  show (Matrix.of q.2 : Mat k r) * ((Matrix.of q.1 : Mat k r) * Matrix.of p.2 * (Matrix.of q.1 : Mat k r)⁻¹) *
      ((Matrix.of q.1 : Mat k r) * Matrix.of p.1) = Matrix.of q.2 * Matrix.of q.1 * (Matrix.of p.2 * Matrix.of p.1)
  simp only [mul_assoc]
  rw [← mul_assoc ((Matrix.of q.1 : Mat k r)⁻¹), h1, one_mul]

theorem sP_Iv {z : Fin (2 * r + k + 1) → ℂ} {p : Mt k r × Mt k r} (hp : p ∈ SS z) : sP (Iv p) = (sP p)⁻¹ := by
  have hu := det_unit_G hp.1.1
  have h1 := mul_inv_G hp.1.1
  show (Matrix.of p.1 : Mat k r)⁻¹ * (Matrix.of p.2 : Mat k r)⁻¹ * ((Matrix.of p.1 : Mat k r)⁻¹)⁻¹ *
      (Matrix.of p.1 : Mat k r)⁻¹ = ((Matrix.of p.2 : Mat k r) * Matrix.of p.1)⁻¹
  rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu, mul_assoc, h1, mul_one]

theorem meas_lmul (a : Mat k r) : Measurable (lmulM (k := k) (r := r) a) := by
  apply Continuous.measurable
  show Continuous fun x : Mat k r => a * x
  exact continuous_const.matrix_mul continuous_id

theorem meas_conj (a : Mat k r) : Measurable (conjM (k := k) (r := r) a) := by
  apply Continuous.measurable
  show Continuous fun x : Mat k r => a * x * a⁻¹
  exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem meas_rmul (a : Mat k r) : Measurable (rmulF a : Mt k r → Mt k r) := by
  apply Continuous.measurable
  show Continuous fun x : Mat k r => x * a
  exact continuous_id.matrix_mul continuous_const

theorem meas_sP : Measurable (fun p : Mt k r × Mt k r => mulM (p.2, p.1)) :=
  bp_cont_mul.measurable.comp (measurable_snd.prodMk measurable_fst)

theorem cont_sP : Continuous (fun p : Mt k r × Mt k r => (sP p : Mat k r)) := by
  unfold sP; exact (continuous_snd (X := Mt k r) (Y := Mt k r)).matrix_mul continuous_fst

theorem meas_Sh : Measurable (Sh (k := k) (r := r)) := by
  refine measurable_fst.prodMk ?_
  change Measurable fun p : Mt k r × Mt k r => mulM (mulM (invM p.1, invM p.2), invM (invM p.1))
  exact bp_cont_mul.measurable.comp ((bp_cont_mul.measurable.comp
    ((bp_meas_inv.comp measurable_fst).prodMk (bp_meas_inv.comp measurable_snd))).prodMk
    (bp_meas_inv.comp (bp_meas_inv.comp measurable_fst)))

theorem meas_Tm : Measurable (Tm (k := k) (r := r)) :=
  (bp_cont_mul.measurable.comp (measurable_fst.prodMk (meas_sP.comp measurable_snd))).prodMk measurable_snd

theorem isClosed_SS (hCW : ClosedW) (hCN : ClosedN) (z : Fin (2 * r + k + 1) → ℂ) :
    IsClosed (SS (k := k) (r := r) z) :=
  ((hCW k r z).closed.preimage continuous_fst).inter ((hCN k r).closed.preimage continuous_snd)

theorem aesm_of_contOn {α E : Type*} [TopologicalSpace α] [SecondCountableTopology α] [MeasurableSpace α]
    [OpensMeasurableSpace α] [TopologicalSpace E] [TopologicalSpace.PseudoMetrizableSpace E] {μ : Measure α}
    {f : α → E} {s : Set α} (hs : IsClosed s) (hf : ContinuousOn f s) (h : ∀ᵐ x ∂μ, x ∈ s) :
    AEStronglyMeasurable f μ := by
  have := hf.aestronglyMeasurable (μ := μ) hs.measurableSet
  rwa [Measure.restrict_eq_self_of_ae_mem h] at this

section meas

variable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (D : RealPlaceData k r Wp Wp)

theorem ae_SS : ∀ᵐ p ∂(D.μW.prod D.μN), p ∈ SS D.z := by
  have := bp_sf D.haarW
  have := bp_sf D.haarN
  exact bp_ae_prod_and (bp_ae_mem D.haarW) (bp_ae_mem D.haarN)

theorem mp_Lq (hCI : ConjInv D) {q : Mt k r × Mt k r} (hq : q ∈ SS D.z) :
    MeasurePreserving (Lq q) (D.μW.prod D.μN) (D.μW.prod D.μN) := by
  have := bp_sf D.haarW
  have := bp_sf D.haarN
  have h1 : MeasurePreserving (lmulM (k := k) (r := r) (Matrix.of q.1)) D.μW D.μW :=
    ⟨meas_lmul _, D.haarW.left _ hq.1⟩
  have h2 : MeasurePreserving (conjM (k := k) (r := r) (Matrix.of q.1)) D.μN D.μN :=
    ⟨meas_conj _, hCI _ (Or.inl hq.1)⟩
  have h3 : MeasurePreserving (lmulM (k := k) (r := r) (Matrix.of q.2)) D.μN D.μN :=
    ⟨meas_lmul _, D.haarN.left _ hq.2⟩
  exact h1.prod (h3.comp h2)

theorem mp_Sh (hCI : ConjInv D) (hInv : HaarInv) (hCW : ClosedW) (hCN : ClosedN) :
    MeasurePreserving (Sh (k := k) (r := r)) (D.μW.prod D.μN) (D.μW.prod D.μN) := by
  have := bp_sf D.haarW
  have := bp_sf D.haarN
  refine ⟨meas_Sh, ?_⟩
  ext s hs
  rw [Measure.map_apply meas_Sh hs, Measure.prod_apply (meas_Sh hs), Measure.prod_apply hs]
  refine lintegral_congr_ae ?_
  filter_upwards [bp_ae_mem D.haarW] with h hh
  have hi : (Matrix.of h : Mat k r)⁻¹ ∈ UWset k r D.z := (hCW k r D.z).inv_mem _ hh
  have hm : Measurable fun n : Mt k r => conjM (Matrix.of h : Mat k r)⁻¹ (invM n) :=
    (meas_conj _).comp bp_meas_inv
  have e : Prod.mk h ⁻¹' (Sh ⁻¹' s) = (fun n : Mt k r => conjM (Matrix.of h : Mat k r)⁻¹ (invM n)) ⁻¹'
      (Prod.mk h ⁻¹' s) := rfl
  have hmap : D.μN.map (fun n : Mt k r => conjM (Matrix.of h : Mat k r)⁻¹ (invM n)) = D.μN := by
    have e2 : (fun n : Mt k r => conjM (Matrix.of h : Mat k r)⁻¹ (invM n)) =
        conjM (Matrix.of h : Mat k r)⁻¹ ∘ invM := rfl
    rw [e2, ← Measure.map_map (meas_conj _) bp_meas_inv, hInv k r _ _ (hCN k r) D.haarN]
    exact hCI _ (Or.inl hi)
  rw [e, ← Measure.map_apply hm (measurable_prodMk_left hs), hmap]

theorem mp_Iv (hCI : ConjInv D) (hInv : HaarInv) (hCW : ClosedW) (hCN : ClosedN) :
    MeasurePreserving (Iv (k := k) (r := r)) (D.μW.prod D.μN) (D.μW.prod D.μN) := by
  have := bp_sf D.haarW
  have := bp_sf D.haarN
  have h1 : MeasurePreserving (invM (k := k) (r := r)) D.μW D.μW :=
    ⟨bp_meas_inv, hInv k r _ _ (hCW k r D.z) D.haarW⟩
  exact (h1.prod (MeasurePreserving.id D.μN)).comp (mp_Sh D hCI hInv hCW hCN)

theorem mp_Tm (hCG : ClosedG) :
    MeasurePreserving (Tm (k := k) (r := r)) (D.μG.prod (D.μW.prod D.μN)) (D.μG.prod (D.μW.prod D.μN)) := by
  have := bp_sf D.haarW
  have := bp_sf D.haarN
  have := bp_sf D.haarG
  refine ⟨meas_Tm, ?_⟩
  ext s hs
  rw [Measure.map_apply meas_Tm hs, Measure.prod_apply_symm (meas_Tm hs), Measure.prod_apply_symm hs]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_SS D] with q hq
  have e : (fun x : Mt k r => (x, q)) ⁻¹' (Tm ⁻¹' s) = rmulF (sP q) ⁻¹' ((fun x : Mt k r => (x, q)) ⁻¹' s) := rfl
  rw [e, ← Measure.map_apply (meas_rmul _) (measurable_prodMk_right hs), D.haarG.right _ (sP_mem hCG hq)]

end meas

section pi

variable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (D : RealPlaceData k r Wp Wp)

def PiO (p : Mt k r × Mt k r) : Wp →L[ℂ] Wp := psiD D (Matrix.of p.2) • D.π (Matrix.of p.1)

theorem norm_psiD (m : Mat k r) : ‖psiD D m‖ = 1 := by
  unfold psiD psi; exact Complex.norm_exp_I_mul_ofReal _

theorem psiD_mul (hEA : EllAdd) {m m' : Mat k r} (hm : m ∈ Nset k r) (hm' : m' ∈ Nset k r) :
    psiD D (m * m') = psiD D m * psiD D m' := by
  unfold psiD psi
  rw [hEA k r D.z D.z_mem m hm m' hm', mul_add, Complex.add_re, Complex.ofReal_add, mul_add, Complex.exp_add]

theorem psiD_conj (hUN : UWNormal) {h m : Mat k r} (hh : h ∈ UWset k r D.z) (hm : m ∈ Nset k r) :
    psiD D (h * m * h⁻¹) = psiD D m := by
  unfold psiD psi; rw [(hUN k r D.z D.z_mem h hh m hm).2]

theorem inner_pi {h : Mat k r} (hh : h ∈ UWset k r D.z) (a b : Wp) : ⟪D.π h a, D.π h b⟫_ℂ = ⟪a, b⟫_ℂ :=
  LinearIsometry.inner_map_map ⟨(D.π h).toLinearMap, fun v => D.π_unitary h hh v⟩ a b

theorem inner_PiO {q : Mt k r × Mt k r} (hq : q ∈ SS D.z) (a b : Wp) : ⟪PiO D q a, PiO D q b⟫_ℂ = ⟪a, b⟫_ℂ := by
  simp only [PiO, ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right, inner_pi D hq.1]
  have h2 : psiD D (Matrix.of q.2) * starRingEnd ℂ (psiD D (Matrix.of q.2)) = 1 := by
    rw [RCLike.mul_conj, norm_psiD]; simp
  rw [← mul_assoc, h2, one_mul]

theorem norm_PiO {q : Mt k r × Mt k r} (hq : q ∈ SS D.z) (a : Wp) : ‖PiO D q a‖ = ‖a‖ := by
  simp only [PiO, ContinuousLinearMap.smul_apply, norm_smul, norm_psiD, D.π_unitary _ hq.1, one_mul]

theorem PiO_Lq (hEA : EllAdd) (hUN : UWNormal) {q p : Mt k r × Mt k r} (hq : q ∈ SS D.z) (hp : p ∈ SS D.z)
    (a : Wp) : PiO D (Lq q p) a = PiO D q (PiO D p a) := by
  have h1 : (Matrix.of q.1 : Mat k r) * Matrix.of p.2 * (Matrix.of q.1 : Mat k r)⁻¹ ∈ Nset k r :=
    (hUN k r D.z D.z_mem _ hq.1 _ hp.2).1
  have e1 : psiD D (Matrix.of (Lq q p).2) = psiD D (Matrix.of q.2) * psiD D (Matrix.of p.2) := by
    show psiD D ((Matrix.of q.2 : Mat k r) * ((Matrix.of q.1 : Mat k r) * Matrix.of p.2 * (Matrix.of q.1 : Mat k r)⁻¹)) = _
    rw [psiD_mul D hEA hq.2 h1, psiD_conj D hUN hq.1 hp.2]
  have e2 : D.π (Matrix.of (Lq q p).1) = (D.π (Matrix.of q.1)).comp (D.π (Matrix.of p.1)) :=
    D.π_rep.2 _ hq.1 _ hp.1
  simp only [PiO, ContinuousLinearMap.smul_apply, e1, e2, ContinuousLinearMap.comp_apply, map_smul, smul_smul]
  rw [mul_comm]

theorem cont_ell (z : Fin (2 * r + k + 1) → ℂ) : Continuous (ell k r z) := by
  unfold ell
  refine continuous_finsetSum _ fun a _ => ?_
  by_cases h : a.val + 1 < r
  · simp only [h, dif_pos]
    fun_prop
  · simp only [h, dif_neg, not_false_eq_true, mulVec, dotProduct]
    fun_prop

theorem cont_psiD : Continuous (psiD D) := by
  unfold psiD psi
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp (continuous_const.mul (cont_ell _)))))

theorem contOn_PiO (a : Wp) : ContinuousOn (fun p : Mt k r × Mt k r => PiO D p a) (SS D.z) := by
  have h1 : ContinuousOn (fun p : Mt k r × Mt k r => D.π (Matrix.of p.1) a) (SS D.z) := by
    have h0 : ContinuousOn (fun m : Mat k r => D.π m a) (UWset k r D.z) :=
      D.π_cont.clm_apply continuousOn_const
    exact h0.comp continuous_fst.continuousOn fun p hp => hp.1
  have h2 : Continuous fun p : Mt k r × Mt k r => psiD D (Matrix.of p.2) := (cont_psiD D).comp continuous_snd
  exact h2.continuousOn.smul h1

end pi

end ReciprocityTheory.ChartRestriction.DS.Mult1.BesselPositivity
end
end

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.BesselPositivity

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1

variable {k r : ℕ}

def cc (k r : ℕ) : ℝ := max (gN (Hpk k r) ^ 2) 1

theorem cc_pos : 0 < cc k r := by
  unfold cc
  exact lt_max_of_lt_right one_pos

theorem AB_pos : 0 < AB k r := by
  unfold AB
  positivity

theorem le_cc {x : Mat k r} (hx : x ∈ GV k r) (t : Mat k r) : gN t ≤ cc k r * (gN x * gN (x * t)) :=
  (ConjugateNormInequalities.gN_le_mul hx t).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (mul_nonneg (ConjugateNormInequalities.gN_nonneg _) (ConjugateNormInequalities.gN_nonneg _)))

theorem rpow_shift (hGL : GNLower) {x t : Mat k r} (hx : x ∈ GV k r) (ht : t ∈ GV k r) {e : ℝ} (he : 0 ≤ e) :
    gN (x * t) ^ (-e) ≤ (cc k r * gN x) ^ e * gN t ^ (-e) := by
  have ht1 := hGL k r t ht
  have hx1 := hGL k r x hx
  have hle := le_cc hx t
  have hpos : 0 < cc k r * gN x := mul_pos cc_pos (by linarith)
  have h1 : gN t / (cc k r * gN x) ≤ gN (x * t) := by
    rw [div_le_iff₀ hpos]
    linarith [show cc k r * (gN x * gN (x * t)) = gN (x * t) * (cc k r * gN x) by ring]
  have h2 := Real.rpow_le_rpow_of_nonpos (div_pos (by linarith) hpos) h1 (by linarith : -e ≤ 0)
  rw [Real.div_rpow (by linarith) hpos.le, Real.rpow_neg hpos.le, div_inv_eq_mul] at h2
  linarith [mul_comm (gN t ^ (-e)) ((cc k r * gN x) ^ e)]

theorem pair_bd (hGL : GNLower) {x t : Mat k r} (hx : x ∈ GV k r) (ht : t ∈ GV k r) (hxt : x * t ∈ GV k r)
    {a : ℝ} (ha : 0 ≤ a) :
    gN (x * t) ^ (-a) * gN x ^ (-a) ≤ (cc k r)⁻¹ ^ (-(a / 2)) * (gN t ^ (-(a / 2)) * gN x ^ (-(a / 2))) := by
  have key := ConjugateNormInequalities.real_key (hGL k r _ hxt) (hGL k r x hx) (lt_of_lt_of_le one_pos (hGL k r t ht)) cc_pos
    (by linarith : 0 ≤ a / 2) (by linarith : a / 2 ≤ a) (le_cc hx t)
  have e : a - a / 2 = a / 2 := by ring
  rw [e, Real.mul_rpow (ConjugateNormInequalities.gN_nonneg _) (inv_nonneg.2 cc_pos.le)] at key
  linarith [key, show gN t ^ (-(a / 2)) * (cc k r)⁻¹ ^ (-(a / 2)) * gN x ^ (-(a / 2)) =
    (cc k r)⁻¹ ^ (-(a / 2)) * (gN t ^ (-(a / 2)) * gN x ^ (-(a / 2))) by ring]

theorem cont_gNt : Continuous (fun g : Mt k r => gN (Matrix.of g : Mat k r)) := by
  unfold gN
  simp only [Matrix.of_apply]
  fun_prop

variable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  (D : RealPlaceData k r Wp Wp)

structure Hyp : Prop where
  cw : ClosedW
  cn : ClosedN
  cg : ClosedG
  gl : GNLower
  gi : GNIntSharp
  ci : ConjInv D
  hinv : HaarInv
  ea : EllAdd
  un : UWNormal
  sint : ∀ b : ℝ, AB k r ≤ b → Integrable (fun p : Mt k r × Mt k r => gN (sP p) ^ (-b)) (D.μW.prod D.μN)

structure Coef (c : Mat k r → ℂ) (C a : ℝ) : Prop where
  cont : ContinuousOn c (GV k r)
  C0 : 0 ≤ C
  a0 : 2 * AB k r ≤ a
  bd : ∀ y ∈ GV k r, ‖c y‖ ≤ C * gN y ^ (-a)

theorem intG (hGI : GNIntSharp) {e : ℝ} (he : AB k r ≤ e) :
    Integrable (fun g : Mt k r => gN (Matrix.of g : Mat k r) ^ (-e)) D.μG := by
  refine ⟨(cont_gNt.measurable.pow_const _).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun g => Real.rpow_nonneg (ConjugateNormInequalities.gN_nonneg _) _)]
  exact hGI k r D.μG e D.haarG he

def Kf (ξ : Wp) (p : Mt k r × Mt k r) : ℂ := star ⟪ξ, PiO D p ξ⟫_ℂ

def Aq (c : Mat k r → ℂ) (ξ : Wp) (x : Mat k r) : ℂ := ∫ p, c (x * sP p) * Kf D ξ p ∂(D.μW.prod D.μN)

def phi (c : Mat k r → ℂ) (ξ : Wp) (x : Mat k r) : ℂ := star (c x) * Aq D c ξ x

def Bv (c : Mat k r → ℂ) (ξ : Wp) (x : Mat k r) : Wp :=
  ∫ p, star (c (x * sP p)) • PiO D p ξ ∂(D.μW.prod D.μN)

def rho (x : Mat k r) : ℝ := gN x ^ (-AB k r)

def Den (x : Mat k r) : ℝ := ∫ q, rho (x * sP q) ∂(D.μW.prod D.μN)

def bet (x : Mat k r) : ℝ := rho x / Den D x

def GS (z : Fin (2 * r + k + 1) → ℂ) : Set (Mt k r × (Mt k r × Mt k r)) :=
  {w | (Matrix.of w.1 : Mat k r) ∈ GV k r ∧ w.2 ∈ SS z}

theorem isClosed_GS (H : Hyp D) : IsClosed (GS (k := k) (r := r) D.z) :=
  ((H.cg k r).closed.preimage continuous_fst).inter ((isClosed_SS H.cw H.cn D.z).preimage continuous_snd)

theorem ae_GS : ∀ᵐ w ∂(D.μG.prod (D.μW.prod D.μN)), w ∈ GS D.z := by
  have := bp_sf D.haarG
  have := bp_sf D.haarW
  have := bp_sf D.haarN
  exact bp_ae_prod_and (bp_ae_mem D.haarG) (ae_SS D)

theorem mulS_mem (H : Hyp D) {x : Mat k r} (hx : x ∈ GV k r) {p : Mt k r × Mt k r} (hp : p ∈ SS D.z) :
    x * sP p ∈ GV k r :=
  (H.cg k r).mul_mem _ hx _ (sP_mem H.cg hp)

theorem norm_Kf {p : Mt k r × Mt k r} (hp : p ∈ SS D.z) (ξ : Wp) : ‖Kf D ξ p‖ ≤ ‖ξ‖ ^ 2 := by
  unfold Kf
  rw [norm_star]
  calc ‖⟪ξ, PiO D p ξ⟫_ℂ‖ ≤ ‖ξ‖ * ‖PiO D p ξ‖ := norm_inner_le_norm _ _
    _ = ‖ξ‖ ^ 2 := by rw [norm_PiO D hp]; ring

theorem contOn_Kf (ξ : Wp) : ContinuousOn (Kf D ξ) (SS D.z) :=
  continuous_star.comp_continuousOn (continuousOn_const.inner (contOn_PiO D ξ))

theorem contOn_cGS (H : Hyp D) {c : Mat k r → ℂ} {C a : ℝ} (hc : Coef c C a) :
    ContinuousOn (fun w : Mt k r × (Mt k r × Mt k r) => c (Matrix.of w.1 * sP w.2)) (GS D.z) :=
  hc.cont.comp ((continuous_fst (X := Mt k r) (Y := Mt k r × Mt k r)).matrix_mul
    (cont_sP.comp continuous_snd)).continuousOn fun w hw => mulS_mem D H hw.1 hw.2

theorem pt_bd (H : Hyp D) {c : Mat k r → ℂ} {C a : ℝ} (hc : Coef c C a) (ξ : Wp) {g : Mat k r}
    (hg : g ∈ GV k r) {p : Mt k r × Mt k r} (hp : p ∈ SS D.z) :
    ‖c (g * sP p)‖ * ‖c g‖ * ‖Kf D ξ p‖ ≤
      (C ^ 2 * ‖ξ‖ ^ 2 * (cc k r)⁻¹ ^ (-(a / 2))) * (gN g ^ (-(a / 2)) * gN (sP p) ^ (-(a / 2))) := by
  have ha : 0 ≤ a := by linarith [hc.a0, AB_pos (k := k) (r := r)]
  have hs := sP_mem H.cg hp
  have hgs := mulS_mem D H hg hp
  have b1 := hc.bd _ hgs
  have b2 := hc.bd _ hg
  have b3 := norm_Kf D hp ξ
  have b4 := pair_bd H.gl hg hs hgs ha
  have hA : 0 ≤ C * gN (g * sP p) ^ (-a) := mul_nonneg hc.C0 (Real.rpow_nonneg (ConjugateNormInequalities.gN_nonneg _) _)
  have hB : 0 ≤ C * gN g ^ (-a) := mul_nonneg hc.C0 (Real.rpow_nonneg (ConjugateNormInequalities.gN_nonneg _) _)
  calc ‖c (g * sP p)‖ * ‖c g‖ * ‖Kf D ξ p‖
      ≤ (C * gN (g * sP p) ^ (-a)) * (C * gN g ^ (-a)) * ‖ξ‖ ^ 2 :=
        mul_le_mul (mul_le_mul b1 b2 (norm_nonneg _) hA) b3 (norm_nonneg _) (mul_nonneg hA hB)
    _ = C ^ 2 * ‖ξ‖ ^ 2 * (gN (g * sP p) ^ (-a) * gN g ^ (-a)) := by ring
    _ ≤ C ^ 2 * ‖ξ‖ ^ 2 * ((cc k r)⁻¹ ^ (-(a / 2)) * (gN (sP p) ^ (-(a / 2)) * gN g ^ (-(a / 2)))) :=
        mul_le_mul_of_nonneg_left b4 (by positivity)
    _ = _ := by ring

theorem intF (H : Hyp D) {c : Mat k r → ℂ} {C a : ℝ} (hc : Coef c C a) (ξ : Wp) :
    Integrable (fun w : Mt k r × (Mt k r × Mt k r) =>
      c (Matrix.of w.1 * sP w.2) * star (c (Matrix.of w.1)) * Kf D ξ w.2) (D.μG.prod (D.μW.prod D.μN)) := by
  have := bp_sf D.haarG
  have := bp_sf D.haarW
  have := bp_sf D.haarN
  have ha2 : AB k r ≤ a / 2 := by linarith [hc.a0]
  have hM : Integrable (fun w : Mt k r × (Mt k r × Mt k r) => (C ^ 2 * ‖ξ‖ ^ 2 * (cc k r)⁻¹ ^ (-(a / 2))) *
      (gN (Matrix.of w.1 : Mat k r) ^ (-(a / 2)) * gN (sP w.2) ^ (-(a / 2)))) (D.μG.prod (D.μW.prod D.μN)) :=
    ((intG D H.gi ha2).mul_prod (H.sint _ ha2)).const_mul _
  refine hM.mono' ?_ ?_
  · refine aesm_of_contOn (isClosed_GS D H) ?_ (ae_GS D)
    exact ((contOn_cGS D H hc).mul (continuous_star.comp_continuousOn
      (hc.cont.comp continuous_fst.continuousOn fun w hw => hw.1))).mul
      ((contOn_Kf D ξ).comp continuous_snd.continuousOn fun w hw => hw.2)
  · filter_upwards [ae_GS D] with w hw
    rw [norm_mul, norm_mul, norm_star]
    exact pt_bd D H hc ξ hw.1 hw.2

theorem fubini1 (H : Hyp D) {c : Mat k r → ℂ} {C a : ℝ} (hc : Coef c C a) (ξ : Wp) :
    ∫ p, (∫ g, c (Matrix.of g * sP p) * star (c (Matrix.of g)) ∂D.μG) * Kf D ξ p ∂(D.μW.prod D.μN) =
      ∫ g, phi D c ξ (Matrix.of g) ∂D.μG := by
  have := bp_sf D.haarG
  have := bp_sf D.haarW
  have := bp_sf D.haarN
  have hF := intF D H hc ξ
  calc _ = ∫ p, ∫ g, c (Matrix.of g * sP p) * star (c (Matrix.of g)) * Kf D ξ p ∂D.μG ∂(D.μW.prod D.μN) := by
          congr 1; funext p; rw [integral_mul_const]
    _ = ∫ g, ∫ p, c (Matrix.of g * sP p) * star (c (Matrix.of g)) * Kf D ξ p ∂(D.μW.prod D.μN) ∂D.μG :=
          integral_integral_swap hF.swap
    _ = _ := by
          congr 1; funext g; unfold phi Aq; rw [← integral_const_mul]; congr 1; funext p; ring

theorem intB (H : Hyp D) {c : Mat k r → ℂ} {C a : ℝ} (hc : Coef c C a) (ξ : Wp) {x : Mat k r}
    (hx : x ∈ GV k r) : Integrable (fun p => star (c (x * sP p)) • PiO D p ξ) (D.μW.prod D.μN) := by
  have ha : 0 ≤ a := by linarith [hc.a0, AB_pos (k := k) (r := r)]
  have haB : AB k r ≤ a := by linarith [hc.a0, AB_pos (k := k) (r := r)]
  refine ((H.sint a haB).const_mul (C * (cc k r * gN x) ^ a * ‖ξ‖)).mono' ?_ ?_
  · refine aesm_of_contOn (isClosed_SS H.cw H.cn D.z) ?_ (ae_SS D)
    exact (continuous_star.comp_continuousOn (hc.cont.comp (continuous_const.matrix_mul cont_sP).continuousOn
      fun p hp => mulS_mem D H hx hp)).smul (contOn_PiO D ξ)
  · filter_upwards [ae_SS D] with p hp
    rw [norm_smul, norm_star, norm_PiO D hp]
    have b1 := hc.bd _ (mulS_mem D H hx hp)
    have b2 := rpow_shift H.gl hx (sP_mem H.cg hp) ha
    calc ‖c (x * sP p)‖ * ‖ξ‖ ≤ C * gN (x * sP p) ^ (-a) * ‖ξ‖ := mul_le_mul_of_nonneg_right b1 (norm_nonneg _)
      _ ≤ C * ((cc k r * gN x) ^ a * gN (sP p) ^ (-a)) * ‖ξ‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left b2 hc.C0) (norm_nonneg _)
      _ = C * (cc k r * gN x) ^ a * ‖ξ‖ * gN (sP p) ^ (-a) := by ring

theorem inner_Bv (H : Hyp D) {c : Mat k r → ℂ} {C a : ℝ} (hc : Coef c C a) (ξ : Wp) {x : Mat k r}
    (hx : x ∈ GV k r) {q : Mt k r × Mt k r} (hq : q ∈ SS D.z) :
    ⟪PiO D q ξ, Bv D c ξ x⟫_ℂ = star (Aq D c ξ (x * sP q)) := by
  have := bp_sf D.haarW
  have := bp_sf D.haarN
  have hmp := mp_Lq D H.ci hq
  have hfi := intB D H hc ξ hx
  have hg_m : AEStronglyMeasurable (fun p => star (c (x * sP p)) * ⟪PiO D q ξ, PiO D p ξ⟫_ℂ)
      (D.μW.prod D.μN) := by
    refine aesm_of_contOn (isClosed_SS H.cw H.cn D.z) ?_ (ae_SS D)
    exact (continuous_star.comp_continuousOn (hc.cont.comp (continuous_const.matrix_mul cont_sP).continuousOn
      fun p hp => mulS_mem D H hx hp)).mul (continuousOn_const.inner (contOn_PiO D ξ))
  have e1 : ⟪PiO D q ξ, Bv D c ξ x⟫_ℂ =
      ∫ p, star (c (x * sP p)) * ⟪PiO D q ξ, PiO D p ξ⟫_ℂ ∂(D.μW.prod D.μN) := by
    rw [Bv, ← integral_inner hfi]
    congr 1; funext p; rw [inner_smul_right]
  have e2 := integral_map (μ := D.μW.prod D.μN) hmp.measurable.aemeasurable
    (f := fun p => star (c (x * sP p)) * ⟪PiO D q ξ, PiO D p ξ⟫_ℂ) (by rw [hmp.map_eq]; exact hg_m)
  rw [hmp.map_eq] at e2
  rw [e1, e2, Aq, ← starRingEnd_apply, ← integral_conj]
  refine integral_congr_ae ?_
  filter_upwards [ae_SS D] with p hp
  simp only [Kf]
  rw [sP_Lq hq, PiO_Lq D H.ea H.un hq hp, inner_PiO D hq, ← mul_assoc x (sP q) (sP p), map_mul,
    starRingEnd_apply, starRingEnd_apply, star_star]

theorem fold_sq (H : Hyp D) {c : Mat k r → ℂ} {C a : ℝ} (hc : Coef c C a) (ξ : Wp) {x : Mat k r}
    (hx : x ∈ GV k r) : ∫ q, phi D c ξ (x * sP q) ∂(D.μW.prod D.μN) = ((‖Bv D c ξ x‖ ^ 2 : ℝ) : ℂ) := by
  have hfi := intB D H hc ξ hx
  have h1 : ∫ q, ⟪Bv D c ξ x, star (c (x * sP q)) • PiO D q ξ⟫_ℂ ∂(D.μW.prod D.μN) =
      ⟪Bv D c ξ x, Bv D c ξ x⟫_ℂ := integral_inner hfi _
  have eB : ⟪Bv D c ξ x, Bv D c ξ x⟫_ℂ = ∫ q, phi D c ξ (x * sP q) ∂(D.μW.prod D.μN) := by
    rw [← h1]
    refine integral_congr_ae ?_
    filter_upwards [ae_SS D] with q hq
    rw [inner_smul_right, ← inner_conj_symm, inner_Bv D H hc ξ hx hq, phi, starRingEnd_apply, star_star]
  rw [← eB, inner_self_eq_norm_sq_to_K]
  norm_cast

theorem meas_rhoS (x : Mat k r) : Measurable (fun q : Mt k r × Mt k r => rho (x * sP q)) :=
  (bp_cont_gN.comp (continuous_const.matrix_mul cont_sP)).measurable.pow_const _

theorem meas_Den : Measurable (fun y : Mt k r => Den D (Matrix.of y)) := by
  have := bp_sf D.haarW
  have := bp_sf D.haarN
  have h : StronglyMeasurable (fun w : Mt k r × (Mt k r × Mt k r) => rho (Matrix.of w.1 * sP w.2)) :=
    ((bp_cont_gN.comp ((continuous_fst (X := Mt k r) (Y := Mt k r × Mt k r)).matrix_mul
      (cont_sP.comp continuous_snd))).measurable.pow_const _).stronglyMeasurable
  exact (h.integral_prod_right' (ν := D.μW.prod D.μN)).measurable

theorem meas_bet : Measurable (fun y : Mt k r => bet D (Matrix.of y)) :=
  (cont_gNt.measurable.pow_const _).div (meas_Den D)

theorem meas_betS (x : Mat k r) : Measurable (fun q : Mt k r × Mt k r => bet D (x * sP q)) :=
  (meas_bet D).comp (bp_cont_mul.measurable.comp (measurable_const.prodMk meas_sP))

theorem meas_bet_inv : Measurable (fun w : Mt k r × (Mt k r × Mt k r) => bet D (Matrix.of w.1 * (sP w.2)⁻¹)) :=
  (meas_bet D).comp (bp_cont_mul.measurable.comp (measurable_fst.prodMk (bp_meas_inv.comp (meas_sP.comp measurable_snd))))

theorem intRho (H : Hyp D) {x : Mat k r} (hx : x ∈ GV k r) :
    Integrable (fun q => rho (x * sP q)) (D.μW.prod D.μN) := by
  refine ((H.sint (AB k r) le_rfl).const_mul ((cc k r * gN x) ^ AB k r)).mono'
    (meas_rhoS x).aestronglyMeasurable ?_
  filter_upwards [ae_SS D] with p hp
  rw [rho, Real.norm_of_nonneg (Real.rpow_nonneg (ConjugateNormInequalities.gN_nonneg _) _)]
  exact rpow_shift H.gl hx (sP_mem H.cg hp) AB_pos.le

theorem Den_pos (H : Hyp D) {x : Mat k r} (hx : x ∈ GV k r) : 0 < Den D x := by
  have := bp_sf D.haarW
  have := bp_sf D.haarN
  unfold Den
  rw [integral_pos_iff_support_of_nonneg_ae (f := fun q => rho (x * sP q))
    (Filter.Eventually.of_forall fun q => Real.rpow_nonneg (ConjugateNormInequalities.gN_nonneg _) _) (intRho D H hx)]
  have hsub : SS D.z ⊆ Function.support (fun q => rho (x * sP q)) := fun q hq =>
    (Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (H.gl k r _ (mulS_mem D H hx hq))) _).ne'
  have hne : (D.μW.prod D.μN) Set.univ ≠ 0 := by
    rw [← Set.univ_prod_univ, Measure.prod_prod]
    exact mul_ne_zero (Measure.measure_univ_ne_zero.2 D.haarW.ne_zero) (Measure.measure_univ_ne_zero.2 D.haarN.ne_zero)
  have hc0 : (D.μW.prod D.μN) (SS D.z)ᶜ = 0 := ae_iff.1 (ae_SS D)
  have h1 : (D.μW.prod D.μN) Set.univ ≤ (D.μW.prod D.μN) (SS D.z) + (D.μW.prod D.μN) (SS D.z)ᶜ := by
    rw [← Set.union_compl_self (SS D.z)]; exact measure_union_le _ _
  rw [hc0, add_zero] at h1
  exact lt_of_lt_of_le (lt_of_lt_of_le (pos_iff_ne_zero.2 hne) h1) (measure_mono hsub)

theorem Den_nonneg (x : Mat k r) : 0 ≤ Den D x := by
  unfold Den rho gN
  exact integral_nonneg fun q => Real.rpow_nonneg (Real.sqrt_nonneg _) _

theorem bet_nonneg (x : Mat k r) : 0 ≤ bet D x := by
  unfold bet
  exact div_nonneg (by unfold rho gN; exact Real.rpow_nonneg (Real.sqrt_nonneg _) _) (Den_nonneg D x)

theorem norm_bet (x : Mat k r) : ‖(bet D x : ℂ)‖ = bet D x := by
  rw [Complex.norm_real, Real.norm_of_nonneg (bet_nonneg D x)]

theorem Den_inv (H : Hyp D) (x : Mat k r) {q₀ : Mt k r × Mt k r} (hq : q₀ ∈ SS D.z) :
    Den D (x * sP q₀) = Den D x := by
  have hmp := mp_Lq D H.ci hq
  have e := integral_map (μ := D.μW.prod D.μN) hmp.measurable.aemeasurable
    (f := fun q => rho (x * sP q)) (meas_rhoS x).aestronglyMeasurable
  rw [hmp.map_eq] at e
  unfold Den
  rw [e]
  congr 1; funext q; rw [sP_Lq hq, mul_assoc]

theorem intBet (H : Hyp D) {x : Mat k r} (hx : x ∈ GV k r) :
    Integrable (fun q => bet D (x * sP q)) (D.μW.prod D.μN) :=
  ((intRho D H hx).div_const (Den D x)).congr (by
    filter_upwards [ae_SS D] with q hq
    simp only [bet]; rw [Den_inv D H x hq])

theorem intBinv (H : Hyp D) {x : Mat k r} (hx : x ∈ GV k r) :
    Integrable (fun q => bet D (x * (sP q)⁻¹)) (D.μW.prod D.μN) :=
  ((mp_Iv D H.ci H.hinv H.cw H.cn).integrable_comp_of_integrable (intBet D H hx)).congr (by
    filter_upwards [ae_SS D] with q hq
    simp only [Function.comp]; rw [sP_Iv hq])

theorem norm1 (H : Hyp D) {x : Mat k r} (hx : x ∈ GV k r) :
    ∫ q, bet D (x * (sP q)⁻¹) ∂(D.μW.prod D.μN) = 1 := by
  have hmp := mp_Iv D H.ci H.hinv H.cw H.cn
  have e := integral_map (μ := D.μW.prod D.μN) hmp.measurable.aemeasurable
    (f := fun q => bet D (x * sP q)) (meas_betS D x).aestronglyMeasurable
  rw [hmp.map_eq] at e
  calc ∫ q, bet D (x * (sP q)⁻¹) ∂(D.μW.prod D.μN) = ∫ q, bet D (x * sP (Iv q)) ∂(D.μW.prod D.μN) :=
        integral_congr_ae (by filter_upwards [ae_SS D] with q hq; rw [sP_Iv hq])
    _ = ∫ q, bet D (x * sP q) ∂(D.μW.prod D.μN) := e.symm
    _ = ∫ q, rho (x * sP q) / Den D x ∂(D.μW.prod D.μN) :=
        integral_congr_ae (by filter_upwards [ae_SS D] with q hq; simp only [bet]; rw [Den_inv D H x hq])
    _ = 1 := by rw [integral_div]; exact div_self (Den_pos D H hx).ne'

theorem fold (H : Hyp D) {φ : Mat k r → ℂ} (hφ : Integrable (fun g : Mt k r => φ (Matrix.of g)) D.μG) :
    ∫ g, φ (Matrix.of g) ∂D.μG =
      ∫ g, (bet D (Matrix.of g) : ℂ) * ∫ q, φ (Matrix.of g * sP q) ∂(D.μW.prod D.μN) ∂D.μG := by
  have := bp_sf D.haarG
  have := bp_sf D.haarW
  have := bp_sf D.haarN
  set Φ : Mt k r × (Mt k r × Mt k r) → ℂ :=
    fun w => φ (Matrix.of w.1) * (bet D (Matrix.of w.1 * (sP w.2)⁻¹) : ℂ) with hΦ_def
  have hΦm : AEStronglyMeasurable Φ (D.μG.prod (D.μW.prod D.μN)) :=
    (hφ.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).mul
      (Complex.measurable_ofReal.comp (meas_bet_inv D)).aestronglyMeasurable
  have hΦ : Integrable Φ (D.μG.prod (D.μW.prod D.μN)) := by
    rw [integrable_prod_iff hΦm]
    constructor
    · filter_upwards [bp_ae_mem D.haarG] with g hg
      simp only [hΦ_def]
      exact (Integrable.ofReal (𝕜 := ℂ) (intBinv D H hg)).const_mul (φ (Matrix.of g))
    · refine hφ.norm.congr ?_
      filter_upwards [bp_ae_mem D.haarG] with g hg
      simp only [hΦ_def, norm_mul, norm_bet]
      rw [integral_const_mul, norm1 D H hg, mul_one]
  have hmp := mp_Tm D H.cg
  have hT : Integrable (Φ ∘ Tm) (D.μG.prod (D.μW.prod D.μN)) := hmp.integrable_comp_of_integrable hΦ
  have eT := integral_map (μ := D.μG.prod (D.μW.prod D.μN)) hmp.measurable.aemeasurable (f := Φ)
    (by rw [hmp.map_eq]; exact hΦm)
  rw [hmp.map_eq] at eT
  calc ∫ g, φ (Matrix.of g) ∂D.μG = ∫ g, ∫ q, Φ (g, q) ∂(D.μW.prod D.μN) ∂D.μG := by
        refine integral_congr_ae ?_
        filter_upwards [bp_ae_mem D.haarG] with g hg
        simp only [hΦ_def]
        rw [integral_const_mul, integral_complex_ofReal, norm1 D H hg, Complex.ofReal_one, mul_one]
    _ = ∫ w, Φ w ∂(D.μG.prod (D.μW.prod D.μN)) := (integral_prod Φ hΦ).symm
    _ = ∫ w, (Φ ∘ Tm) w ∂(D.μG.prod (D.μW.prod D.μN)) := eT
    _ = ∫ g, ∫ q, (Φ ∘ Tm) (g, q) ∂(D.μW.prod D.μN) ∂D.μG := integral_prod _ hT
    _ = _ := by
        refine integral_congr_ae ?_
        filter_upwards [bp_ae_mem D.haarG] with g hg
        rw [← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards [ae_SS D] with q hq
        show φ (Matrix.of g * sP q) * (bet D (Matrix.of g * sP q * (sP q)⁻¹) : ℂ) =
          (bet D (Matrix.of g) : ℂ) * φ (Matrix.of g * sP q)
        rw [mul_assoc (Matrix.of g : Mat k r), mul_inv_G (sP_mem H.cg hq), mul_one, mul_comm]

theorem intPhi (H : Hyp D) {c : Mat k r → ℂ} {C a : ℝ} (hc : Coef c C a) (ξ : Wp) :
    Integrable (fun g : Mt k r => phi D c ξ (Matrix.of g)) D.μG := by
  have := bp_sf D.haarG
  have := bp_sf D.haarW
  have := bp_sf D.haarN
  have ha2 : AB k r ≤ a / 2 := by linarith [hc.a0]
  set K : ℝ := C ^ 2 * ‖ξ‖ ^ 2 * (cc k r)⁻¹ ^ (-(a / 2)) with hK
  set I : ℝ := ∫ p, gN (sP p) ^ (-(a / 2)) ∂(D.μW.prod D.μN) with hI
  have hAm : AEStronglyMeasurable (fun g : Mt k r => Aq D c ξ (Matrix.of g)) D.μG :=
    (aesm_of_contOn (isClosed_GS D H) ((contOn_cGS D H hc).mul
      ((contOn_Kf D ξ).comp continuous_snd.continuousOn fun w hw => hw.2)) (ae_GS D)).integral_prod_right'
  have hof : Continuous (fun g : Mt k r => (Matrix.of g : Mat k r)) := continuous_id
  have hGc : IsClosed {g : Mt k r | (Matrix.of g : Mat k r) ∈ GV k r} := (H.cg k r).closed.preimage hof
  have hcm : AEStronglyMeasurable (fun g : Mt k r => star (c (Matrix.of g))) D.μG :=
    aesm_of_contOn (α := Mt k r) hGc
      (continuous_star.comp_continuousOn (hc.cont.comp hof.continuousOn fun g hg => hg))
      (bp_ae_mem D.haarG)
  refine ((intG D H.gi ha2).const_mul (K * I)).mono' (hcm.mul hAm) ?_
  filter_upwards [bp_ae_mem D.haarG] with g hg
  have hSi := H.sint _ ha2
  unfold phi Aq
  rw [norm_mul, norm_star]
  calc ‖c (Matrix.of g)‖ * ‖∫ p, c (Matrix.of g * sP p) * Kf D ξ p ∂(D.μW.prod D.μN)‖
      ≤ ‖c (Matrix.of g)‖ * ∫ p, ‖c (Matrix.of g * sP p) * Kf D ξ p‖ ∂(D.μW.prod D.μN) :=
        mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)
    _ = ∫ p, ‖c (Matrix.of g)‖ * ‖c (Matrix.of g * sP p) * Kf D ξ p‖ ∂(D.μW.prod D.μN) :=
        (integral_const_mul _ _).symm
    _ ≤ ∫ p, (K * gN (Matrix.of g : Mat k r) ^ (-(a / 2))) * gN (sP p) ^ (-(a / 2)) ∂(D.μW.prod D.μN) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => by positivity)
          (hSi.const_mul _) ?_
        filter_upwards [ae_SS D] with p hp
        have := pt_bd D H hc ξ hg hp
        rw [norm_mul]
        calc ‖c (Matrix.of g)‖ * (‖c (Matrix.of g * sP p)‖ * ‖Kf D ξ p‖)
            = ‖c (Matrix.of g * sP p)‖ * ‖c (Matrix.of g)‖ * ‖Kf D ξ p‖ := by ring
          _ ≤ _ := this
          _ = _ := by rw [hK]; ring
    _ = K * I * gN (Matrix.of g : Mat k r) ^ (-(a / 2)) := by rw [integral_const_mul, hI]; ring

theorem phi_eq (H : Hyp D) {c : Mat k r → ℂ} {C a : ℝ} (hc : Coef c C a) (ξ : Wp) :
    ∫ g, phi D c ξ (Matrix.of g) ∂D.μG =
      ((∫ g, bet D (Matrix.of g) * ‖Bv D c ξ (Matrix.of g)‖ ^ 2 ∂D.μG : ℝ) : ℂ) := by
  rw [fold D H (intPhi D H hc ξ), ← integral_complex_ofReal]
  refine integral_congr_ae ?_
  filter_upwards [bp_ae_mem D.haarG] with g hg
  rw [fold_sq D H hc ξ hg, Complex.ofReal_mul]

end ReciprocityTheory.ChartRestriction.DS.Mult1.BesselPositivity
end
end

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem bePos_hyp (h : UnitaryGroupStructuralFacts) {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] (D : RealPlaceData k r Wp Wp) (hD : IsDiag D) : BesselPositivity.Hyp D := by
  have hS := stSInt h
  obtain ⟨h1, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h16, h17, -⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, a13, -, a15, a16, -, a18, -, a20, a21, a22, -, -, -, -, -⟩ := h1
  exact ⟨a22, a21, a20, a16, a15, a13 k r Wp Wp D, a18, h17, h16, fun b hb => hS k r Wp D hD b hb⟩

private theorem two_mul_AB_le_aM (k r : ℕ) : 2 * AB k r ≤ aM k r := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  simp only [AB, aM, nR]
  push_cast
  nlinarith [mul_nonneg hk hr, mul_nonneg (mul_nonneg hk hr) hr, mul_nonneg (mul_nonneg hk hk) hr,
    mul_nonneg (mul_nonneg hr hr) hr, mul_nonneg (mul_nonneg hk hk) hk, mul_nonneg hr hr, mul_nonneg hk hk]

private theorem exists_bessel_coef_of_mem_Vfl {k r : ℕ} (X : SigData k r) (haM : aM k r ≤ X.a) {u : X.Hs}
    (hu : u ∈ Vfl X) : ∃ C : ℝ, BesselPositivity.Coef (mc X u X.w) C X.a := by
  obtain ⟨C, hC⟩ := hu
  refine ⟨max C 0, ⟨?_, le_max_right _ _, (two_mul_AB_le_aM k r).trans haM, ?_⟩⟩
  ·
    have h1 := X.rep.2.2 u
    exact (continuous_const.inner continuous_id).comp_continuousOn h1
  · intro y hy
    have ht : 0 ≤ gN y ^ (-X.a) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
    exact (hC y hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ht)

private lemma inner_apply_right_inverse_eq_inner_of_isometry {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (T S : E →L[ℂ] E)
    (hT : ∀ v, ‖T v‖ = ‖v‖) (hTS : T.comp S = 1) (x : E) : ⟪x, S x⟫_ℂ = ⟪T x, x⟫_ℂ := by
  let L : E →ₗᵢ[ℂ] E := ⟨T.toLinearMap, hT⟩
  have h1 : ⟪T x, T (S x)⟫_ℂ = ⟪x, S x⟫_ℂ := L.inner_map_map x (S x)
  have h2 : T (S x) = x := by
    have := congrArg (fun F : E →L[ℂ] E => F x) hTS
    simpa using this
  rw [h2] at h1
  exact h1.symm

theorem bePos_inner_eq {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] (D : RealPlaceData k r Wp Wp) (X : SigData k r) (H : BesselPositivity.Hyp D)
    {d : ℝ} (hd : IsFdegG D X d) {u : X.Hs} {C a : ℝ} (hc : BesselPositivity.Coef (mc X u X.w) C a) (ξ : Wp)
    (hI : Integrable (beInt D X u u) (D.μW.prod D.μN)) :
    ⟪ξ, beOp D X u u ξ⟫_ℂ = (d : ℂ) * ∫ g, BesselPositivity.phi D (mc X u X.w) ξ (Matrix.of g) ∂D.μG := by
  obtain ⟨hd0, hdS⟩ := hd
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
  have hA : ⟪ξ, beOp D X u u ξ⟫_ℂ = ∫ p, ⟪ξ, beInt D X u u p ξ⟫_ℂ ∂(D.μW.prod D.μN) := by
    unfold beOp
    rw [ContinuousLinearMap.integral_apply hI, integral_inner (hI.apply_continuousLinearMap ξ)]
  have hGae : ∀ᵐ g ∂D.μG, Matrix.of g ∈ GV k r := by
    first
    | exact ae_iff.2 D.haarG.conc
    | exact measure_mono_null (fun a ha => ha) D.haarG.conc
  rw [hA, ← BesselPositivity.fubini1 D H hc ξ, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [BesselPositivity.ae_SS (D := D)] with p hp
  have hs : BesselPositivity.sP p ∈ GV k r := BesselPositivity.sP_mem H.cg hp

  have hSch : ∫ g, mc X u X.w (Matrix.of g * BesselPositivity.sP p) * star (mc X u X.w (Matrix.of g)) ∂D.μG =
      mc X u u (BesselPositivity.sP p) / d := by
    have hc1 : ∀ᵐ g ∂D.μG, mc X u X.w (Matrix.of g * BesselPositivity.sP p) * star (mc X u X.w (Matrix.of g)) =
        mc X (X.σ (BesselPositivity.sP p) u) X.w (Matrix.of g) * star (mc X u X.w (Matrix.of g)) := by
      filter_upwards [hGae] with g hg
      simp only [mc, X.rep.1.2 _ hg _ hs, ContinuousLinearMap.comp_apply]
    rw [integral_congr_ae hc1, ((hdS (X.σ (BesselPositivity.sP p) u) X.w u X.w).2)]
    simp only [mc, inner_self_eq_norm_sq_to_K, X.w_norm]
    simp
  rw [hSch]
  have ha := hp.1
  have hinv := inner_apply_right_inverse_eq_inner_of_isometry (D.π (Matrix.of p.1)) (D.π (Matrix.of p.1)⁻¹) (D.π_unitary _ ha) (by
    rw [← D.π_rep.2 _ ha _ ((H.cw k r D.z).inv_mem _ ha), Matrix.mul_nonsing_inv _ ((H.cw k r D.z).unit _ ha),
      D.π_rep.1]) ξ
  have hc2 : star ⟪ξ, D.π (Matrix.of p.1) ξ⟫_ℂ = ⟪D.π (Matrix.of p.1) ξ, ξ⟫_ℂ := inner_conj_symm _ _
  simp only [beInt, BesselPositivity.Kf, BesselPositivity.PiO, BesselPositivity.sP, inner_smul_right, ContinuousLinearMap.smul_apply,
    inner_smul_right, star_mul', hinv, hc2]
  field_simp

theorem bePos_identity (h : UnitaryGroupStructuralFacts) {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hD : IsDiag D) (haM : aM k r ≤ X.a)
    {d : ℝ} (hd : IsFdegG D X d) {u : X.Hs} (hu : u ∈ Vfl X) (ξ : Wp)
    (hI : Integrable (beInt D X u u) (D.μW.prod D.μN)) :
    ⟪ξ, beOp D X u u ξ⟫_ℂ =
      (d : ℂ) * ((∫ g, BesselPositivity.bet D (Matrix.of g) * ‖BesselPositivity.Bv D (mc X u X.w) ξ (Matrix.of g)‖ ^ 2 ∂D.μG : ℝ) : ℂ) := by
  obtain ⟨C, hc⟩ := exists_bessel_coef_of_mem_Vfl X haM hu
  have H := bePos_hyp h D hD
  rw [bePos_inner_eq D X H hd hc ξ hI, BesselPositivity.phi_eq D H hc ξ]

theorem stBePos (h : UnitaryGroupStructuralFacts) : StBePos := by
  intro k r Wp _ _ _ D X hD hX ha u hu ξ
  obtain ⟨d, hd⟩ := stSchurG k r Wp D X hD hX
  by_cases hI : Integrable (beInt D X u u) (D.μW.prod D.μN)
  swap
  · have h0 : beOp D X u u = 0 := integral_undef hI
    rw [h0]
    simp
  rw [bePos_identity h D X hD ha hd hu ξ hI]
  have h0 : 0 ≤ ∫ g, BesselPositivity.bet D (Matrix.of g) * ‖BesselPositivity.Bv D (mc X u X.w) ξ (Matrix.of g)‖ ^ 2 ∂D.μG :=
    integral_nonneg fun g => mul_nonneg (BesselPositivity.bet_nonneg (D := D) _) (sq_nonneg _)
  rw [← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_nonneg hd.1.le h0

end ReciprocityTheory.ChartRestriction.DS.Mult1
