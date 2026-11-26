module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.TheoremMOf
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBePos
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JHaarSF
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JSmooth
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvCC
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.WeightedL1OfL2
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JMixed
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.XiExistsOfIn

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JSchurW
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace SchurWAux

theorem fdeg_eq_finrank {G : Type*} [MeasurableSpace G] (μ : Measure G) [IsProbabilityMeasure μ]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [Nontrivial H]
    (ρ : G → (H →L[ℂ] H)) (hiso : ∀ g v, ‖ρ g v‖ = ‖v‖) (d : ℝ) (hd : 0 < d)
    (h : ∀ v w v' w' : H, Integrable (fun g => ⟪w, ρ g v⟫_ℂ * star ⟪w', ρ g v'⟫_ℂ) μ ∧
      ∫ g, ⟪w, ρ g v⟫_ℂ * star ⟪w', ρ g v'⟫_ℂ ∂μ = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)) :
    (d : ℂ) = (Module.finrank ℂ H : ℂ) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  set b := stdOrthonormalBasis ℂ H
  have hpt : ∀ g, ∑ i, ⟪b i, ρ g v⟫_ℂ * star ⟪b i, ρ g v⟫_ℂ = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    intro g
    have e1 : ∀ i, ⟪b i, ρ g v⟫_ℂ * star ⟪b i, ρ g v⟫_ℂ = ⟪ρ g v, b i⟫_ℂ * ⟪b i, ρ g v⟫_ℂ := by
      intro i
      rw [mul_comm]
      congr 1
      exact inner_conj_symm _ _
    simp_rw [e1]
    rw [b.sum_inner_mul_inner, inner_self_eq_norm_sq_to_K, hiso]
    push_cast
    rfl
  have hbi : ∀ i, ⟪b i, b i⟫_ℂ = 1 := by
    intro i
    rw [inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]
    simp
  have hL : ∫ g, ∑ i, ⟪b i, ρ g v⟫_ℂ * star ⟪b i, ρ g v⟫_ℂ ∂μ = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    simp_rw [hpt]
    simp
  rw [MeasureTheory.integral_finsetSum _ (fun i _ => (h v (b i) v (b i)).1)] at hL
  have e2 : ∀ i, ∫ g, ⟪b i, ρ g v⟫_ℂ * star ⟪b i, ρ g v⟫_ℂ ∂μ = ((‖v‖ ^ 2 : ℝ) : ℂ) / (d : ℂ) := by
    intro i
    rw [(h v (b i) v (b i)).2, hbi, mul_one, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  simp_rw [e2] at hL
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hL
  have hv2 : ((‖v‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have : 0 < ‖v‖ := norm_pos_iff.mpr hv
    exact_mod_cast (pow_pos this 2).ne'
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [mul_div_assoc', div_eq_iff hd'] at hL
  exact (mul_right_cancel₀ hv2 (by rw [hL]; ring)).symm

end SchurWAux

theorem stSchurW (h : UnitaryGroupStructuralFacts) : StSchurW := by
  obtain ⟨hB2, -⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hCpt, -, -, -, hHI, -, -, -, hCW, -⟩ := hB2
  intro k r Wp _ _ _ D hD v w v' w'
  rcases subsingleton_or_nontrivial Wp with hW | hW
  · rw [Subsingleton.elim w 0]
    simp
  have hU : IsClosedSubgroup (UWset k r D.z) := hCW k r D.z
  have hμ := D.haarW
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  let μ : Measure (MatrixSubsetMeasurability.SG hU) := MatrixSubsetMeasurability.nu hU D.μW
  have : μ.IsMulLeftInvariant := MatrixSubsetMeasurability.nu_left hμ
  have : μ.IsInvInvariant := MatrixSubsetMeasurability.nu_inv hHI hμ
  have hE := MatrixSubsetMeasurability.me_val hU
  have hcpt : IsCompact (Set.univ : Set (MatrixSubsetMeasurability.SG hU)) := by
    have hind : Topology.IsInducing (fun g : MatrixSubsetMeasurability.SG hU => g.1) := Topology.IsInducing.subtypeVal
    have hr : Set.range (fun g : MatrixSubsetMeasurability.SG hU => g.1) = {x : Mt k r | (Matrix.of x : Mat k r) ∈ UWset k r D.z} :=
      Subtype.range_coe_subtype
    rw [hind.isCompact_iff, Set.image_univ, hr]
    exact hCpt k r D.z D.z_mem D.T_pos
  have hν1 : μ Set.univ = 1 := by
    have e : ((MatrixSubsetMeasurability.nu hU D.μW).map (fun g : MatrixSubsetMeasurability.SG hU => g.1)) Set.univ = D.μW Set.univ := by
      rw [MatrixSubsetMeasurability.map_nu hμ]
    rw [Measure.map_apply hE.measurable MeasurableSet.univ, Set.preimage_univ] at e
    exact e.trans hD.mass
  have : IsProbabilityMeasure μ := ⟨hν1⟩
  have : μ.IsOpenPosMeasure :=
    isOpenPosMeasure_of_mulLeftInvariant_of_compact _ hcpt (by rw [hν1]; exact one_ne_zero)
  let ρ : MatrixSubsetMeasurability.SG hU → (Wp →L[ℂ] Wp) := fun g => D.π (MatrixSubsetMeasurability.mat g)
  have h1 : ρ 1 = 1 := D.π_rep.1
  have hρm : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b) := fun a b => D.π_rep.2 _ a.2 _ b.2
  have hiso : ∀ g v, ‖ρ g v‖ = ‖v‖ := fun g v => D.π_unitary _ g.2 v
  have hcont : ∀ v, Continuous fun g => ρ g v := fun v =>
    (D.π_cont.comp_continuous MatrixSubsetMeasurability.continuous_mat MatrixSubsetMeasurability.mat_mem).clm_apply continuous_const
  have hsq : ∀ v w : Wp, MemLp (fun g => ⟪w, ρ g v⟫_ℂ) 2 μ := by
    intro v w
    refine MemLp.of_bound (continuous_const.inner (hcont v)).aestronglyMeasurable (‖w‖ * ‖v‖)
      (ae_of_all _ fun g => ?_)
    exact (norm_inner_le_norm _ _).trans (le_of_eq (by rw [hiso]))
  have hirr : ∀ S : Submodule ℂ Wp, IsClosed (S : Set Wp) → (∀ g, ∀ v ∈ S, ρ g v ∈ S) → S = ⊥ ∨ S = ⊤ :=
    fun S hS hst => hD.irr S hS fun g hg v hv => hst (MatrixSubsetMeasurability.mk hU g hg) v hv
  have hSq : Formalism.MainNotions.BridgeCSchur.SqRep μ ρ := ⟨h1, hρm, hiso, hcont, hsq⟩
  obtain ⟨d, hd, hrel⟩ := Formalism.MainNotions.BridgeCSchur.schur_orth hSq hirr
  have hdn := SchurWAux.fdeg_eq_finrank μ ρ hiso d hd hrel
  rw [← MatrixSubsetMeasurability.map_nu (hU := hU) hμ, hE.integral_map, ← hdn]
  exact (hrel v w v' w').2

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBeEquiv
namespace ReciprocityTheory.ChartRestriction.DS.Mult1

theorem stBeEquiv (h : UnitaryGroupStructuralFacts) : StBeEquiv := by
  intro k r Wp _ _ _ D X _ _ u u' hI h0 hh0 m hm
  exact ⟨BeEquiv.beOp_left D X (BeEquiv.beFacts_of h D) u u' hI hh0 hm,
    BeEquiv.beOp_right D X (BeEquiv.beFacts_of h D) u u' hI hh0 hm⟩

end ReciprocityTheory.ChartRestriction.DS.Mult1
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBeHerm
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.BesselHermitian

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1

variable {k r : ℕ}

def SSh (z : Fin (2 * r + k + 1) → ℂ) : Set (Mt k r × Mt k r) :=
  {p | (Matrix.of p.1 : Mat k r) ∈ UWset k r z ∧ (Matrix.of p.2 : Mat k r) ∈ Nset k r}

def Shh (p : Mt k r × Mt k r) : Mt k r × Mt k r := (p.1, conjM (Matrix.of p.1)⁻¹ (invM p.2))

def Ivh (p : Mt k r × Mt k r) : Mt k r × Mt k r := (invM (Shh p).1, (Shh p).2)

theorem bh_sf {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) : SigmaFinite μ := by
  have : IsFiniteMeasureOnCompacts μ := ⟨h.finite_compact⟩
  infer_instance

theorem bh_ae_mem {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) :
    ∀ᵐ x ∂μ, (Matrix.of x : Mat k r) ∈ U := by
  rw [ae_iff]; exact h.conc

theorem bh_ae_prod_and {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {ν : Measure β} [SFinite μ] [SFinite ν] {P : α → Prop} {Q : β → Prop} (hP : ∀ᵐ x ∂μ, P x)
    (hQ : ∀ᵐ y ∂ν, Q y) : ∀ᵐ p ∂(μ.prod ν), P p.1 ∧ Q p.2 :=
  (Measure.quasiMeasurePreserving_fst.ae hP).and (Measure.quasiMeasurePreserving_snd.ae hQ)

theorem bh_meas_inv : Measurable (invM (k := k) (r := r)) := by
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
  change Matrix.of.symm ((Matrix.of g : Mat k r)⁻¹) = _
  rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rfl

theorem bh_cont_mul : Continuous (mulM (k := k) (r := r)) := by
  unfold mulM
  exact (continuous_fst (X := Mt k r) (Y := Mt k r)).matrix_mul continuous_snd

theorem bh_meas_conj (a : Mat k r) : Measurable (conjM (k := k) (r := r) a) := by
  apply Continuous.measurable
  show Continuous fun x : Mat k r => a * x * a⁻¹
  exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem bh_meas_Shh : Measurable (Shh (k := k) (r := r)) := by
  refine measurable_fst.prodMk ?_
  change Measurable fun p : Mt k r × Mt k r => mulM (mulM (invM p.1, invM p.2), invM (invM p.1))
  exact bh_cont_mul.measurable.comp ((bh_cont_mul.measurable.comp
    ((bh_meas_inv.comp measurable_fst).prodMk (bh_meas_inv.comp measurable_snd))).prodMk
    (bh_meas_inv.comp (bh_meas_inv.comp measurable_fst)))

section meas

variable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (D : RealPlaceData k r Wp Wp)

theorem ae_SSh : ∀ᵐ p ∂(D.μW.prod D.μN), p ∈ SSh D.z := by
  have := bh_sf D.haarW
  have := bh_sf D.haarN
  exact bh_ae_prod_and (bh_ae_mem D.haarW) (bh_ae_mem D.haarN)

theorem mp_Shh (hCI : ConjInv D) (hInv : HaarInv) (hCW : ClosedW) (hCN : ClosedN) :
    MeasurePreserving (Shh (k := k) (r := r)) (D.μW.prod D.μN) (D.μW.prod D.μN) := by
  have := bh_sf D.haarW
  have := bh_sf D.haarN
  refine ⟨bh_meas_Shh, ?_⟩
  ext s hs
  rw [Measure.map_apply bh_meas_Shh hs, Measure.prod_apply (bh_meas_Shh hs), Measure.prod_apply hs]
  refine lintegral_congr_ae ?_
  filter_upwards [bh_ae_mem D.haarW] with h hh
  have hi : (Matrix.of h : Mat k r)⁻¹ ∈ UWset k r D.z := (hCW k r D.z).inv_mem _ hh
  have hm : Measurable fun n : Mt k r => conjM (Matrix.of h : Mat k r)⁻¹ (invM n) :=
    (bh_meas_conj _).comp bh_meas_inv
  have e : Prod.mk h ⁻¹' (Shh ⁻¹' s) = (fun n : Mt k r => conjM (Matrix.of h : Mat k r)⁻¹ (invM n)) ⁻¹'
      (Prod.mk h ⁻¹' s) := rfl
  have hmap : D.μN.map (fun n : Mt k r => conjM (Matrix.of h : Mat k r)⁻¹ (invM n)) = D.μN := by
    have e2 : (fun n : Mt k r => conjM (Matrix.of h : Mat k r)⁻¹ (invM n)) =
        conjM (Matrix.of h : Mat k r)⁻¹ ∘ invM := rfl
    rw [e2, ← Measure.map_map (bh_meas_conj _) bh_meas_inv, hInv k r _ _ (hCN k r) D.haarN]
    exact hCI _ (Or.inl hi)
  rw [e, ← Measure.map_apply hm (measurable_prodMk_left hs), hmap]

theorem mp_Ivh (hCI : ConjInv D) (hInv : HaarInv) (hCW : ClosedW) (hCN : ClosedN) :
    MeasurePreserving (Ivh (k := k) (r := r)) (D.μW.prod D.μN) (D.μW.prod D.μN) := by
  have := bh_sf D.haarW
  have := bh_sf D.haarN
  have h1 : MeasurePreserving (invM (k := k) (r := r)) D.μW D.μW :=
    ⟨bh_meas_inv, hInv k r _ _ (hCW k r D.z) D.haarW⟩
  exact (h1.prod (MeasurePreserving.id D.μN)).comp (mp_Shh D hCI hInv hCW hCN)

end meas

section key

variable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
  (D : RealPlaceData k r Wp Wp) (X : SigData k r)

theorem inner_move_sig (hCG : ClosedG) {g : Mat k r} (hg : g ∈ GV k r) (a b : X.Hs) :
    ⟪X.σ g a, b⟫_ℂ = ⟪a, X.σ g⁻¹ b⟫_ℂ := by
  have hgi : g⁻¹ ∈ GV k r := (hCG k r).inv_mem _ hg
  have hgg : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g ((hCG k r).unit _ hg)
  let e : X.Hs →ₗᵢ[ℂ] X.Hs := ⟨(X.σ g).toLinearMap, fun v => X.rep.2.1 g hg v⟩
  have hb : X.σ g (X.σ g⁻¹ b) = b := by
    have := X.rep.1.2 g hg g⁻¹ hgi
    rw [hgg, X.rep.1.1] at this
    have h2 := congrArg (fun L : X.Hs →L[ℂ] X.Hs => L b) this
    simpa using h2.symm
  calc ⟪X.σ g a, b⟫_ℂ = ⟪e a, e (X.σ g⁻¹ b)⟫_ℂ := by
        simp only [e]; exact congrArg _ hb.symm
    _ = ⟪a, X.σ g⁻¹ b⟫_ℂ := e.inner_map_map a _

theorem inner_move_pi (hCW : ClosedW) {h : Mat k r} (hh : h ∈ UWset k r D.z) (a b : Wp) :
    ⟪D.π h a, b⟫_ℂ = ⟪a, D.π h⁻¹ b⟫_ℂ := by
  have hhi : h⁻¹ ∈ UWset k r D.z := (hCW k r D.z).inv_mem _ hh
  have hhh : h * h⁻¹ = 1 := Matrix.mul_nonsing_inv h ((hCW k r D.z).unit _ hh)
  let e : Wp →ₗᵢ[ℂ] Wp := ⟨(D.π h).toLinearMap, fun v => D.π_unitary h hh v⟩
  have hb : D.π h (D.π h⁻¹ b) = b := by
    have := D.π_rep.2 h hh h⁻¹ hhi
    rw [hhh, D.π_rep.1] at this
    have h2 := congrArg (fun L : Wp →L[ℂ] Wp => L b) this
    simpa using h2.symm
  calc ⟪D.π h a, b⟫_ℂ = ⟪e a, e (D.π h⁻¹ b)⟫_ℂ := by
        simp only [e]; exact congrArg _ hb.symm
    _ = ⟪a, D.π h⁻¹ b⟫_ℂ := e.inner_map_map a _

theorem psiD_conj' (hUN : UWNormal) {h m : Mat k r} (hh : h ∈ UWset k r D.z) (hm : m ∈ Nset k r) :
    psiD D (h * m * h⁻¹) = psiD D m := by
  unfold psiD psi; rw [(hUN k r D.z D.z_mem h hh m hm).2]

theorem psiD_inv' (hEA : EllAdd) (hCN : ClosedN) {m : Mat k r} (hm : m ∈ Nset k r) :
    psiD D m⁻¹ = star (psiD D m) := by
  have hmi : m⁻¹ ∈ Nset k r := (hCN k r).inv_mem _ hm
  have h1 : (1 : Mat k r) ∈ Nset k r := (hCN k r).one_mem
  have hm1 : m⁻¹ * m = 1 := Matrix.nonsing_inv_mul m ((hCN k r).unit _ hm)
  have e0 : ell k r D.z 1 = 0 := by
    have := hEA k r D.z D.z_mem 1 h1 1 h1
    rw [Matrix.one_mul] at this
    linear_combination -this
  have e1 : ell k r D.z m⁻¹ = -ell k r D.z m := by
    have := hEA k r D.z D.z_mem m⁻¹ hmi m hm
    rw [hm1, e0] at this
    linear_combination -this
  unfold psiD psi
  rw [e1, Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]
  congr 1
  rw [mul_neg, Complex.neg_re, Complex.ofReal_neg]
  ring

theorem key (hCG : ClosedG) (hCW : ClosedW) (hCN : ClosedN) (hUN : UWNormal) (hEA : EllAdd)
    (u u' : X.Hs) {p : Mt k r × Mt k r} (hp : p ∈ SSh D.z) :
    beInt D X u' u (Ivh p) = ContinuousLinearMap.adjoint (beInt D X u u' p) := by
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  obtain ⟨hH, hN⟩ := hp
  have eH : (Matrix.of (Ivh p).1 : Mat k r) = (Matrix.of p.1 : Mat k r)⁻¹ := rfl
  have eN : (Matrix.of (Ivh p).2 : Mat k r) =
      (Matrix.of p.1 : Mat k r)⁻¹ * (Matrix.of p.2 : Mat k r)⁻¹ * ((Matrix.of p.1 : Mat k r)⁻¹)⁻¹ := rfl
  simp only [beInt, eH, eN]
  generalize (Matrix.of p.1 : Mat k r) = H at hH ⊢
  generalize (Matrix.of p.2 : Mat k r) = N at hN ⊢
  have hHu : IsUnit H.det := (hCW k r D.z).unit _ hH
  have hHi : H⁻¹ ∈ UWset k r D.z := (hCW k r D.z).inv_mem _ hH
  have hNi : N⁻¹ ∈ Nset k r := (hCN k r).inv_mem _ hN
  have hHH : H⁻¹⁻¹ = H := Matrix.nonsing_inv_nonsing_inv H hHu
  have hNH : N * H ∈ GV k r := (hCG k r).mul_mem _ hN.1 _ hH.1
  have hs : H⁻¹ * N⁻¹ * H⁻¹⁻¹ * H⁻¹ = (N * H)⁻¹ := by
    rw [hHH, Matrix.mul_assoc, Matrix.mul_nonsing_inv H hHu, Matrix.mul_one, Matrix.mul_inv_rev]
  have hps : psiD D (H⁻¹ * N⁻¹ * H⁻¹⁻¹) = star (psiD D N) := by
    rw [psiD_conj' D hUN hHi hNi, psiD_inv' D hEA hCN hN]
  have hmc : starRingEnd ℂ (mc X u' u (N * H)⁻¹) = mc X u u' (N * H) := by
    unfold mc
    rw [inner_conj_symm, inner_move_sig X hCG ((hCG k r).inv_mem _ hNH),
      Matrix.nonsing_inv_nonsing_inv _ ((hCG k r).unit _ hNH)]
  rw [hs, hps, hHH]
  simp only [ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right, star_star]
  rw [inner_move_pi D hCW hH x y, map_mul, hmc]
  rfl

end key

section main

variable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
  (D : RealPlaceData k r Wp Wp) (X : SigData k r)

theorem inner_int {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → Wp →L[ℂ] Wp}
    (hf : Integrable f μ) (a b : Wp) : ⟪a, (∫ p, f p ∂μ) b⟫_ℂ = ∫ p, ⟪a, f p b⟫_ℂ ∂μ := by
  have := ((innerSL ℂ a).comp (ContinuousLinearMap.apply ℂ Wp b)).integral_comp_comm hf
  simpa [innerSL_apply_apply] using this.symm

theorem int_adj {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → Wp →L[ℂ] Wp}
    (hf : Integrable f μ) : Integrable (fun p => ContinuousLinearMap.adjoint (f p)) μ :=
  hf.congr' ((ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := Wp) (F := Wp)).continuous.comp_aestronglyMeasurable
    hf.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun _ => ((ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := Wp) (F := Wp)).norm_map _).symm)

theorem int_swap (hCI : ConjInv D) (hInv : HaarInv) (hCG : ClosedG) (hCW : ClosedW) (hCN : ClosedN)
    (hUN : UWNormal) (hEA : EllAdd) (u u' : X.Hs) (hI : Integrable (beInt D X u u') (D.μW.prod D.μN)) :
    Integrable (beInt D X u' u) (D.μW.prod D.μN) := by
  have hmp := mp_Ivh D hCI hInv hCW hCN
  have h1 : Integrable (beInt D X u u' ∘ Ivh) (D.μW.prod D.μN) := by
    apply Integrable.comp_measurable _ hmp.measurable
    rw [hmp.map_eq]; exact hI
  refine (int_adj h1).congr ?_
  filter_upwards [ae_SSh D] with p hp
  show ContinuousLinearMap.adjoint (beInt D X u u' (Ivh p)) = beInt D X u' u p
  rw [key D X hCG hCW hCN hUN hEA u' u hp, ContinuousLinearMap.adjoint_adjoint]

theorem herm_main (hCI : ConjInv D) (hInv : HaarInv) (hCG : ClosedG) (hCW : ClosedW) (hCN : ClosedN)
    (hUN : UWNormal) (hEA : EllAdd) (u u' : X.Hs) (η ξ : Wp) :
    ⟪ξ, beOp D X u u' η⟫_ℂ = ⟪beOp D X u' u ξ, η⟫_ℂ := by
  unfold beOp
  by_cases hI : Integrable (beInt D X u u') (D.μW.prod D.μN)
  · have hJ := int_swap D X hCI hInv hCG hCW hCN hUN hEA u u' hI
    have hmp := mp_Ivh D hCI hInv hCW hCN
    have hA := int_adj hI
    have e1 : ∫ p, beInt D X u' u p ∂(D.μW.prod D.μN) =
        ∫ p, ContinuousLinearMap.adjoint (beInt D X u u' p) ∂(D.μW.prod D.μN) := by
      have e2 : ∫ p, beInt D X u' u p ∂(D.μW.prod D.μN) = ∫ p, beInt D X u' u (Ivh p) ∂(D.μW.prod D.μN) := by
        conv_lhs => rw [← hmp.map_eq]
        exact integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hJ.aestronglyMeasurable)
      rw [e2]
      refine integral_congr_ae ?_
      filter_upwards [ae_SSh D] with p hp
      exact key D X hCG hCW hCN hUN hEA u u' hp
    rw [e1]
    calc ⟪ξ, (∫ p, beInt D X u u' p ∂(D.μW.prod D.μN)) η⟫_ℂ
        = ∫ p, ⟪ξ, beInt D X u u' p η⟫_ℂ ∂(D.μW.prod D.μN) := inner_int hI ξ η
      _ = starRingEnd ℂ (starRingEnd ℂ (∫ p, ⟪ξ, beInt D X u u' p η⟫_ℂ ∂(D.μW.prod D.μN))) :=
          (Complex.conj_conj _).symm
      _ = starRingEnd ℂ (∫ p, starRingEnd ℂ ⟪ξ, beInt D X u u' p η⟫_ℂ ∂(D.μW.prod D.μN)) := by
          rw [integral_conj]
      _ = starRingEnd ℂ (∫ p, ⟪η, ContinuousLinearMap.adjoint (beInt D X u u' p) ξ⟫_ℂ ∂(D.μW.prod D.μN)) := by
          congr 1
          refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
          show starRingEnd ℂ ⟪ξ, beInt D X u u' p η⟫_ℂ = ⟪η, ContinuousLinearMap.adjoint (beInt D X u u' p) ξ⟫_ℂ
          rw [ContinuousLinearMap.adjoint_inner_right, inner_conj_symm]
      _ = starRingEnd ℂ ⟪η, (∫ p, ContinuousLinearMap.adjoint (beInt D X u u' p) ∂(D.μW.prod D.μN)) ξ⟫_ℂ := by
          rw [inner_int hA η ξ]
      _ = _ := inner_conj_symm _ _
  · have hJ : ¬ Integrable (beInt D X u' u) (D.μW.prod D.μN) := fun h =>
      hI (int_swap D X hCI hInv hCG hCW hCN hUN hEA u' u h)
    rw [integral_undef hI, integral_undef hJ]
    simp

end main

end ReciprocityTheory.ChartRestriction.DS.Mult1.BesselHermitian

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem stBeHerm (h : UnitaryGroupStructuralFacts) : StBeHerm := by
  intro k r Wp _ _ _ D X _ _ u _ u' _ η ξ
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  obtain ⟨hB2, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hUN, hEA, -⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hCIA, -, -, -, -, hInv, -, hCG, hCN, hCW, -⟩ := hB2
  exact BesselHermitian.herm_main D X (hCIA k r Wp Wp D) hInv hCG hCW hCN hUN hEA u u' η ξ

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBetaInf
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBetaInfA
noncomputable section

open MeasureTheory Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.BetaInfA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem ccle_five_four {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {F : Mat k r → E} {c : ℝ}
    (h : CCle A 5 F c) : CCle A 4 F c := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, fun u v hu hv hl g hg => h2 u v hu hv (by omega) g hg⟩
  intro g₀ hg₀
  obtain ⟨U, f', hU, hg, hf, he⟩ := h1 g₀ hg₀
  exact ⟨U, f', hU, hg, hf.of_le (by exact_mod_cast (by norm_num : (4 : ℕ) ≤ 5)), he⟩

theorem inCC_five_four {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {F : Mat k r → E}
    (h : InCC A 5 F) : InCC A 4 F := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, ccle_five_four hc⟩

theorem continuous_lam (z : Fin (2 * r + k + 1) → ℂ) :
    Continuous fun n : Mt k r => lam k r z (Matrix.of n) := by
  unfold Formalism.FourierDecayAlt.B.lam Formalism.QuantumDeterminants.ell
  refine Complex.continuous_re.comp (continuous_const.mul (continuous_finsetSum _ fun a _ => ?_))
  split_ifs
  · exact (continuous_apply _).comp (continuous_apply _)
  · simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    fun_prop

theorem continuous_xiTau_prod (D : RealPlaceData k r Wp Wq) :
    Continuous fun x : (ℝ × ℝ) × SS k r => xiTau D x.1 x.2 := by
  have h1 := continuous_lam (k := k) (r := r) D.z
  have h2 := continuous_lam (k := k) (r := r) D.z'
  unfold Formalism.FourierDecayAlt.B.xiTau
  refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp ?_))
  exact ((continuous_fst.comp continuous_fst).mul
      (h1.comp (continuous_snd.comp (continuous_fst.comp continuous_snd)))).sub
    ((continuous_snd.comp continuous_fst).mul
      (h2.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))))

theorem norm_xiTau (D : RealPlaceData k r Wp Wq) (τ : ℝ × ℝ) (p : SS k r) : ‖xiTau D τ p‖ = 1 := by
  unfold Formalism.FourierDecayAlt.B.xiTau
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

theorem continuous_cf (D : RealPlaceData k r Wp Wq) {P : SS k r → ℂ} (hP : Integrable P D.μSS) :
    Continuous fun τ : ℝ × ℝ => ∫ p, xiTau D τ p * P p ∂D.μSS := by
  refine continuous_of_dominated (bound := fun p => ‖P p‖) (fun τ => ?_) (fun τ => ?_) hP.norm ?_
  · exact ((continuous_xiTau_prod D).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable.mul
      hP.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun p => by simp only [norm_mul, norm_xiTau, one_mul, le_refl]
  · exact Filter.Eventually.of_forall fun p =>
      ((continuous_xiTau_prod D).comp (continuous_id.prodMk continuous_const)).mul continuous_const

theorem integrable_test {w : ℝ → ℝ} (hw : IsTest w) : Integrable (fun x => (w x : ℂ)) volume := (hw.1.continuous.integrable_of_hasCompactSupport hw.2.1).ofReal

theorem integrable_test2 {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) :
    Integrable (fun τ : ℝ × ℝ => ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ)) volume := by
  have h := MeasureTheory.Integrable.mul_prod (integrable_test h₁) (integrable_test h₂)
  rw [Measure.volume_eq_prod]
  push_cast
  exact h

theorem inner_om (w₁ w₂ : ℝ → ℝ) (a b : ℝ) :
    ∫ τ : ℝ × ℝ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((τ.1 * a - τ.2 * b : ℝ) : ℂ)) = om w₁ a * om w₂ (-b) := by
  have e : ∀ τ : ℝ × ℝ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) *
      Complex.exp (Complex.I * ((τ.1 * a - τ.2 * b : ℝ) : ℂ)) =
      ((w₁ τ.1 : ℂ) * Complex.exp (Complex.I * ((τ.1 * a : ℝ) : ℂ))) *
        ((w₂ τ.2 : ℂ) * Complex.exp (Complex.I * ((τ.2 * -b : ℝ) : ℂ))) := by
    intro τ
    push_cast
    rw [show Complex.I * ((τ.1 : ℂ) * a - τ.2 * b) =
      Complex.I * (τ.1 * a) + Complex.I * (τ.2 * -b) by ring, Complex.exp_add]
    ring
  rw [Measure.volume_eq_prod, integral_congr_ae (Filter.Eventually.of_forall e)]
  exact MeasureTheory.integral_prod_mul
    (fun x : ℝ => (w₁ x : ℂ) * Complex.exp (Complex.I * ((x * a : ℝ) : ℂ)))
    (fun y : ℝ => (w₂ y : ℂ) * Complex.exp (Complex.I * ((y * -b : ℝ) : ℂ)))

theorem sigmaFinite_haarOn {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) :
    SigmaFinite μ := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
  infer_instance

theorem sigmaFinite_SS (D : RealPlaceData k r Wp Wq) : SigmaFinite D.μSS := by
  haveI := sigmaFinite_haarOn D.haarW
  haveI := sigmaFinite_haarOn D.haarN
  haveI := sigmaFinite_haarOn D.haarW'
  unfold RealPlaceData.μSS
  infer_instance

theorem fubini_cf (D : RealPlaceData k r Wp Wq) {P : SS k r → ℂ} (hP : Integrable P D.μSS)
    {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) :
    ∫ τ : ℝ × ℝ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * ∫ p, xiTau D τ p * P p ∂D.μSS =
      ∫ p, om w₁ (lam k r D.z (Matrix.of p.1.2)) * om w₂ (-lam k r D.z' (Matrix.of p.2.2)) * P p ∂D.μSS := by
  haveI := sigmaFinite_SS D
  have hint : Integrable (fun x : (ℝ × ℝ) × SS k r =>
      ((w₁ x.1.1 * w₂ x.1.2 : ℝ) : ℂ) * (xiTau D x.1 x.2 * P x.2)) (volume.prod D.μSS) := by
    refine (MeasureTheory.Integrable.mul_prod (integrable_test2 h₁ h₂) hP).mono ?_ ?_
    · haveI : OpensMeasurableSpace ((ℝ × ℝ) × SS k r) := Prod.opensMeasurableSpace
      exact (integrable_test2 h₁ h₂).aestronglyMeasurable.comp_fst.mul
        ((continuous_xiTau_prod D).aestronglyMeasurable.mul hP.aestronglyMeasurable.comp_snd)
    · exact Filter.Eventually.of_forall fun x => by simp only [norm_mul, norm_xiTau, one_mul, le_refl]
  simp_rw [← integral_const_mul]
  rw [integral_integral_swap (f := fun τ p => ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * (xiTau D τ p * P p)) hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  have e : ∀ τ : ℝ × ℝ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * (xiTau D τ p * P p) =
      (((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * Complex.exp (Complex.I *
        ((τ.1 * lam k r D.z (Matrix.of p.1.2) - τ.2 * lam k r D.z' (Matrix.of p.2.2) : ℝ) : ℂ))) * P p :=
    fun τ => by unfold Formalism.FourierDecayAlt.B.xiTau; ring
  simp only [e]
  rw [integral_mul_const, inner_om]

theorem isOpen_Quad : IsOpen Quad := isOpen_Ioi.prod isOpen_Ioi

theorem integrable_test_mul {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) {f : ℝ × ℝ → ℂ}
    (hf : ContinuousOn f Quad) : Integrable (fun τ : ℝ × ℝ => ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * f τ) volume := by
  have hK : IsCompact (tsupport w₁ ×ˢ tsupport w₂) := h₁.2.1.prod h₂.2.1
  have hKQ : tsupport w₁ ×ˢ tsupport w₂ ⊆ Quad := Set.prod_mono h₁.2.2 h₂.2.2
  have hc : ContinuousOn (fun τ : ℝ × ℝ => ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * f τ)
      (tsupport w₁ ×ˢ tsupport w₂) := by
    refine ContinuousOn.mul ?_ (hf.mono hKQ)
    exact (Complex.continuous_ofReal.comp ((h₁.1.continuous.comp continuous_fst).mul
      (h₂.1.continuous.comp continuous_snd))).continuousOn
  refine MeasureTheory.IntegrableOn.integrable_of_forall_notMem_eq_zero
    (hc.integrableOn_compact (μ := volume) hK) ?_
  intro τ hτ
  rw [Set.mem_prod, not_and_or] at hτ
  rcases hτ with h | h
  · simp [image_eq_zero_of_notMem_tsupport h]
  · simp [image_eq_zero_of_notMem_tsupport h]

theorem betaInf_eq_of (D : RealPlaceData k r Wp Wq) [FiniteDimensional ℂ Wq] (A : ℝ) (hAe : AeFromTests)
    (hRB : RegBound D A) (hRA : RegAverage D A) {F F' : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : InCC A 4 F) (hF' : InCC A 4 F') (hP : Integrable (Ph D F F') D.μSS) :
    betaInf D F F' = ∫ p, xiTau D (1, 1) p * Ph D F F' p ∂D.μSS := by
  obtain ⟨-, hcont, -⟩ := hRB
  have hc1 : ContinuousOn (fun τ => betaInfTau D τ F F') Quad := hcont F F' hF hF'
  have hc2 : ContinuousOn (fun τ : ℝ × ℝ => ∫ p, xiTau D τ p * Ph D F F' p ∂D.μSS) Quad :=
    (continuous_cf D hP).continuousOn
  have hae := hAe (fun _ => 0)
    (fun τ => betaInfTau D τ F F' - ∫ p, xiTau D τ p * Ph D F F' p ∂D.μSS)
    aemeasurable_const (hc1.sub hc2) (fun w₁ w₂ h₁ h₂ _ _ => by
      refine ⟨by simp, ?_⟩
      simp only [mul_zero, MeasureTheory.lintegral_zero, ENNReal.toReal_zero, Complex.ofReal_zero]
      simp_rw [mul_sub]
      rw [integral_sub (integrable_test_mul h₁ h₂ hc1) (integrable_test_mul h₁ h₂ hc2),
        (hRA F F' hF hF' w₁ w₂ h₁ h₂).2, fubini_cf D hP h₁ h₂, sub_self])
  have h0 : (fun τ => betaInfTau D τ F F' - ∫ p, xiTau D τ p * Ph D F F' p ∂D.μSS)
      =ᵐ[volume.restrict Quad] fun _ => 0 := by
    filter_upwards [hae] with τ hτ
    simpa using hτ.2.symm
  have heq := Measure.eqOn_open_of_ae_eq h0 isOpen_Quad (hc1.sub hc2) continuousOn_const
  have h11 : ((1 : ℝ), (1 : ℝ)) ∈ Quad := by
    unfold Quad
    exact ⟨by norm_num, by norm_num⟩
  show betaInfTau D (1, 1) F F' = _
  exact sub_eq_zero.mp (heq h11)

end ReciprocityTheory.ChartRestriction.DS.Mult1.BetaInfA
end
end

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem stBetaInf (h : UnitaryGroupStructuralFacts) : StBetaInf := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hRB, hRA, -, hAe, hDJ⟩ := h
  have hDJ' : DilJacAll := by first | exact hDJ | exact hDJ.1
  intro k r Wp Wq _ _ _ _ _ _ D A hXi hA F F' hF hF' hP
  obtain ⟨Ξ, hCB, hXI⟩ := hXi k r Wp Wq D A hA
  exact BetaInfA.betaInf_eq_of D A hAe (hRB k r Wp Wq D Ξ A hA hCB hXI)
    (hRA k r Wp Wq D Ξ A hA hCB hXI (hDJ' k r Wp Wq D)) (BetaInfA.inCC_five_four hF)
    (BetaInfA.inCC_five_four hF') hP

end ReciprocityTheory.ChartRestriction.DS.Mult1
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JFrame
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JFrameA
noncomputable section

open Matrix
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

def frameMat (k : ℕ) (u : Fin (k + 1) → ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ := fun i j =>
  if i = Fin.last k then
    (if j = Fin.last k then u (Fin.last k)
      else u (Fin.last k) * (((‖u (Fin.last k)‖)⁻¹ : ℝ) : ℂ) * star (u j))
  else if j = Fin.last k then u i
  else (if i = j then 1 else 0) + u i * star (u j) * (((1 + ‖u (Fin.last k)‖)⁻¹ : ℝ) : ℂ)

theorem frameMat_col (k : ℕ) (u : Fin (k + 1) → ℂ) (i : Fin (k + 1)) :
    frameMat k u i (Fin.last k) = u i := by
  by_cases h : i = Fin.last k
  · subst h; simp [frameMat]
  · simp [frameMat, h]

theorem frameMat_star_mul_self (t : ℂ) : star t * t = ((‖t‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.conj_mul']
  push_cast
  ring

section
variable (k : ℕ) (u : Fin (k + 1) → ℂ)

theorem frameMat_cc (x i : Fin k) : frameMat k u x.castSucc i.castSucc =
    (if x = i then 1 else 0) + u x.castSucc * star (u i.castSucc) * (((1 + ‖u (Fin.last k)‖)⁻¹ : ℝ) : ℂ) := by
  simp [frameMat, (Fin.castSucc_lt_last x).ne, (Fin.castSucc_lt_last i).ne, Fin.castSucc_inj]

theorem frameMat_lc (i : Fin k) : frameMat k u (Fin.last k) i.castSucc =
    u (Fin.last k) * (((‖u (Fin.last k)‖)⁻¹ : ℝ) : ℂ) * star (u i.castSucc) := by
  simp [frameMat, (Fin.castSucc_lt_last i).ne]

theorem frameMat_cl (x : Fin k) : frameMat k u x.castSucc (Fin.last k) = u x.castSucc := by
  simp [frameMat, (Fin.castSucc_lt_last x).ne]

theorem frameMat_ll : frameMat k u (Fin.last k) (Fin.last k) = u (Fin.last k) := by
  simp [frameMat]

end

theorem frameMat_star_ofReal (x : ℝ) : star ((x : ℝ) : ℂ) = (x : ℂ) := by
  rw [Complex.star_def, Complex.conj_ofReal]

theorem frameMat_unitary (k : ℕ) (u : Fin (k + 1) → ℂ)
    (hu : ∑ l : Fin k, star (u l.castSucc) * u l.castSucc = star (u (Fin.last k)) * u (Fin.last k) - 1) :
    (frameMat k u)ᴴ * Hb k * frameMat k u = Hb k := by
  set t := u (Fin.last k) with ht
  set n : ℝ := ‖t‖ with hn
  set c : ℝ := (1 + n)⁻¹ with hc
  set m : ℝ := n⁻¹ with hm
  have ht2 : star t * t = (n : ℂ) ^ 2 := by rw [frameMat_star_mul_self]; push_cast; rfl
  have hreal : (∑ l : Fin k, ‖u l.castSucc‖ ^ 2 : ℝ) = n ^ 2 - 1 := by
    have h1 := hu
    simp only [frameMat_star_mul_self] at h1
    exact_mod_cast h1
  have hn1 : 1 ≤ n ^ 2 := by
    have : 0 ≤ (∑ l : Fin k, ‖u l.castSucc‖ ^ 2 : ℝ) := Finset.sum_nonneg (fun _ _ => by positivity)
    linarith
  have hnpos : 0 < n := by
    have : 0 ≤ n := norm_nonneg _
    rcases this.eq_or_lt with h | h
    · rw [← h] at hn1; norm_num at hn1
    · exact h
  have key : (2 : ℂ) * (c : ℂ) + ((n : ℂ) ^ 2 - 1) * (c : ℂ) ^ 2 - (n : ℂ) ^ 2 * (m : ℂ) ^ 2 = 0 := by
    have : (2 * c + (n ^ 2 - 1) * c ^ 2 - n ^ 2 * m ^ 2 : ℝ) = 0 := by
      rw [hc, hm]; field_simp; ring
    exact_mod_cast this
  have key2 : (1 : ℂ) + ((n : ℂ) ^ 2 - 1) * (c : ℂ) - (n : ℂ) ^ 2 * (m : ℂ) = 0 := by
    have : (1 + (n ^ 2 - 1) * c - n ^ 2 * m : ℝ) = 0 := by
      rw [hc, hm]; field_simp; ring
    exact_mod_cast this
  have hne : ∀ x : Fin k, (Fin.last k = x.castSucc) = False :=
    fun x => eq_false (fun h => Fin.castSucc_ne_last x h.symm)
  have hne' : ∀ x : Fin k, (x.castSucc = Fin.last k) = False :=
    fun x => eq_false (Fin.castSucc_ne_last x)
  ext i j
  rw [Matrix.mul_apply]
  simp only [Hb, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Fin.sum_univ_castSucc]
  cases i using Fin.lastCases with
  | last =>
    cases j using Fin.lastCases with
    | last =>
      simp only [frameMat_ll, frameMat_cl, Matrix.diagonal_apply, hne', if_true, if_false, mul_one]
      rw [hu]; ring
    | cast j =>
      simp only [frameMat_ll, frameMat_cl, frameMat_lc, frameMat_cc, Matrix.diagonal_apply, hne, hne', if_true, if_false, mul_one,
        ← ht, ← hn, ← hc, ← hm]
      have hpt : ∀ x : Fin k, star (u x.castSucc) * ((if x = j then (1 : ℂ) else 0) +
          u x.castSucc * star (u j.castSucc) * (c : ℂ)) =
          (if x = j then star (u j.castSucc) else 0) + star (u x.castSucc) * u x.castSucc *
            (star (u j.castSucc) * (c : ℂ)) := by
        intro x; split_ifs with h <;> [subst h; skip] <;> ring
      rw [Finset.sum_congr rfl (fun x _ => hpt x)]
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, ← Finset.sum_mul, hu,
        star_mul, frameMat_star_ofReal, star_star]
      linear_combination (star (u j.castSucc)) * key2 +
        (star (u j.castSucc) * (c : ℂ) - star (u j.castSucc) * (m : ℂ)) * ht2
  | cast i =>
    cases j using Fin.lastCases with
    | last =>
      simp only [frameMat_ll, frameMat_cl, frameMat_lc, frameMat_cc, Matrix.diagonal_apply, hne, hne', if_true, if_false, mul_one,
        ← ht, ← hn, ← hc, ← hm]
      have hpt : ∀ x : Fin k, star ((if x = i then (1 : ℂ) else 0) +
          u x.castSucc * star (u i.castSucc) * (c : ℂ)) * u x.castSucc =
          (if x = i then u i.castSucc else 0) + star (u x.castSucc) * u x.castSucc *
            (u i.castSucc * (c : ℂ)) := by
        intro x; split_ifs with h <;> [subst h; skip] <;> simp only [star_add, star_mul, frameMat_star_ofReal, star_star,
          star_one, star_zero] <;> ring
      rw [Finset.sum_congr rfl (fun x _ => hpt x)]
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, ← Finset.sum_mul, hu,
        star_mul, frameMat_star_ofReal, star_star]
      linear_combination (u i.castSucc) * key2 +
        (u i.castSucc * (c : ℂ) - u i.castSucc * (m : ℂ)) * ht2
    | cast j =>
      simp only [frameMat_ll, frameMat_cl, frameMat_lc, frameMat_cc, Matrix.diagonal_apply, hne, hne', if_true, if_false, mul_one,
        Fin.castSucc_inj, ← ht, ← hn, ← hc, ← hm]
      have hpt : ∀ x : Fin k, star ((if x = i then (1 : ℂ) else 0) +
          u x.castSucc * star (u i.castSucc) * (c : ℂ)) * ((if x = j then (1 : ℂ) else 0) +
          u x.castSucc * star (u j.castSucc) * (c : ℂ)) =
          (if x = i then (if i = j then 1 else 0) + u i.castSucc * star (u j.castSucc) * (c : ℂ) else 0) +
          (if x = j then star (u j.castSucc) * u i.castSucc * (c : ℂ) else 0) +
          star (u x.castSucc) * u x.castSucc * (u i.castSucc * star (u j.castSucc) * (c : ℂ) ^ 2) := by
        intro x; split_ifs <;> subst_vars <;> first
          | exact (‹¬ _ = _› rfl).elim
          | (simp only [star_add, star_mul, frameMat_star_ofReal, star_star, star_one, star_zero]; ring)
      rw [Finset.sum_congr rfl (fun x _ => hpt x)]
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, ← Finset.sum_mul, hu,
        star_mul, frameMat_star_ofReal, star_star]
      linear_combination (u i.castSucc * star (u j.castSucc)) * key +
        (u i.castSucc * star (u j.castSucc) * (c : ℂ) ^ 2 - u i.castSucc * star (u j.castSucc) * (m : ℂ) ^ 2) * ht2

def frameCoef (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if r ≤ i.val ∧ i.val ≤ r + k then (if i.val = r + k then -1 else 1) else 0

theorem frame_wI_val (k r : ℕ) (j : Fin (k + 1)) : (wI k r j).val = r + j.val := rfl

theorem frame_Hpk_mul (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j * z j = if j = i then frameCoef k r i * z i else 0 := by
  by_cases hij : j = i
  · subst hij
    rw [if_pos rfl]
    by_cases hj : j.val < r ∨ r + k < j.val
    · rw [hz j hj, mul_zero, mul_zero]
    · congr 1
      unfold Hpk frameCoef
      split_ifs <;> first | rfl | (exfalso; omega) | simp_all
  · rw [if_neg hij]
    by_cases hj : j.val < r ∨ r + k < j.val
    · rw [hz j hj, mul_zero]
    · have hv : j.val ≠ i.val := fun h => hij (Fin.ext h)
      unfold Hpk
      split_ifs <;> first | (exfalso; omega) | simp_all | simp

theorem frame_herm (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) :
    herm (Hpk k r) z z = ∑ l : Fin k, star (z (wI k r l.castSucc)) * z (wI k r l.castSucc) -
      star (z (wI k r (Fin.last k))) * z (wI k r (Fin.last k)) := by
  have hrow : ∀ i, (Hpk k r *ᵥ z) i = frameCoef k r i * z i := by
    intro i
    show ∑ j, Hpk k r i j * z j = _
    rw [Finset.sum_congr rfl (fun j _ => frame_Hpk_mul k r z hz i j)]
    simp
  show ∑ i, star (z i) * (Hpk k r *ᵥ z) i = _
  simp only [hrow]
  have hinj : Function.Injective (wI k r) := by
    intro a b h
    have h' := congrArg Fin.val h
    rw [frame_wI_val, frame_wI_val] at h'
    exact Fin.ext (by omega)
  have hsub : ∑ i, star (z i) * (frameCoef k r i * z i) =
      ∑ i ∈ Finset.univ.image (wI k r), star (z i) * (frameCoef k r i * z i) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    have hn : ¬ (r ≤ i.val ∧ i.val ≤ r + k) := by
      rintro ⟨h1, h2⟩
      exact hi (Finset.mem_image.2 ⟨⟨i.val - r, by omega⟩, Finset.mem_univ _,
        Fin.ext (by rw [frame_wI_val]; simp; omega)⟩)
    simp [frameCoef, hn]
  have hc1 : ∀ l : Fin k, frameCoef k r (wI k r l.castSucc) = 1 := by
    intro l
    have hl := l.isLt
    have h1 : r ≤ r + (l : ℕ) ∧ r + (l : ℕ) ≤ r + k := by omega
    have h3 : (l : ℕ) ≠ k := by omega
    simp [frameCoef, frame_wI_val, h1, h3]
  have hc2 : frameCoef k r (wI k r (Fin.last k)) = -1 := by
    simp [frameCoef, frame_wI_val]
  rw [hsub, Finset.sum_image (fun a _ b _ h => hinj h), Fin.sum_univ_castSucc]
  simp only [hc1, hc2, one_mul, neg_one_mul, mul_neg, sub_eq_add_neg]

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem stFrame : StFrame := by
  intro k r z _hk hz hT
  set T := Tz k r z with hTdef
  set s : ℝ := (Real.sqrt T)⁻¹ with hs

  have hTeq : T = ‖z (wI k r (Fin.last k))‖ ^ 2 - ∑ l : Fin k, ‖z (wI k r l.castSucc)‖ ^ 2 := by
    have h := frame_herm k r z hz
    simp only [frameMat_star_mul_self] at h
    rw [hTdef, Tz, h, ← Complex.ofReal_sum, ← Complex.ofReal_sub, Complex.ofReal_re]
    ring
  have hsT : s ^ 2 * T = 1 := by
    rw [hs, inv_pow, Real.sq_sqrt hT.le, inv_mul_cancel₀ hT.ne']
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  refine ⟨frameMat k (fun j => (s : ℂ) * z (wI k r j)), ?_⟩
  unfold IsZFrame
  constructor
  · apply frameMat_unitary
    simp only [frameMat_star_mul_self]
    have key : ∑ l : Fin k, ‖(s : ℂ) * z (wI k r l.castSucc)‖ ^ 2 =
        ‖(s : ℂ) * z (wI k r (Fin.last k))‖ ^ 2 - 1 := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0, mul_pow,
        ← Finset.mul_sum]
      linear_combination (-1 : ℝ) * hsT + s ^ 2 * hTeq
    rw [← Complex.ofReal_sum, key, Complex.ofReal_sub, Complex.ofReal_one]
  · have hlast : (wI k r (Fin.last k)).val = r + k := by simp [frame_wI_val]
    funext i
    simp only [bvec, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Pi.smul_apply, smul_eq_mul]
    unfold embWb
    by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
    · rw [dite_eq_left ⟨hi, by omega, by omega⟩]
      rw [show ∀ p, (⟨(wI k r (Fin.last k)).val - r, p⟩ : Fin (k + 1)) = Fin.last k from
        fun p => Fin.ext (by simp only [Fin.val_last]; omega)]
      rw [frameMat_col]
      rw [show ∀ p, wI k r (⟨i.val - r, p⟩ : Fin (k + 1)) = i from
        fun p => Fin.ext (by rw [frame_wI_val]; show r + (i.val - r) = i.val; omega)]
    · rw [dite_eq_right (fun h => hi h.1)]
      have hne : ¬ (i = wI k r (Fin.last k) ∧ ¬ (r ≤ i.val ∧ i.val ≤ r + k)) := by
        rintro ⟨rfl, h⟩
        exact h ⟨by omega, by omega⟩
      rw [if_neg hne, hz i (by omega), mul_zero]

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JRankOne
namespace ReciprocityTheory.ChartRestriction.DS.Mult1

theorem rankOneMinors : RankOneMinors := by
  intro X κ hherm hpos hmin
  by_cases h : ∃ x0, κ x0 x0 ≠ 0
  · obtain ⟨x0, hx0⟩ := h
    have him : (κ x0 x0).im = 0 := by
      have h1 := congrArg Complex.im (hherm x0 x0)
      simp [Complex.star_def] at h1
      linarith
    have hk0 : κ x0 x0 = (((κ x0 x0).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
    have hr : 0 < (κ x0 x0).re := by
      rcases (hpos x0).lt_or_eq with h | h
      · exact h
      · exact (hx0 (by rw [hk0, ← h]; simp)).elim
    generalize (κ x0 x0).re = r at hk0 hr
    refine ⟨fun x => κ x x0 / (Real.sqrt r : ℂ), fun x y => ?_⟩
    show κ x y = κ x x0 / (Real.sqrt r : ℂ) * star (κ y x0 / (Real.sqrt r : ℂ))
    have hs : (Real.sqrt r : ℂ) * (Real.sqrt r : ℂ) = (r : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hr.le]
    have hst : star (κ y x0 / (Real.sqrt r : ℂ)) = κ x0 y / (Real.sqrt r : ℂ) := by
      rw [star_div₀, ← hherm x0 y]
      congr 1
      exact Complex.conj_ofReal _
    rw [hst, div_mul_div_comm, hs, ← hk0, hmin x x0 x0 y, mul_div_assoc, div_self hx0, mul_one]
  · push_neg at h
    refine ⟨fun _ => 0, fun x y => ?_⟩
    simp only [zero_mul]
    have h1 := hmin x y y x
    rw [h x, zero_mul, hherm y x] at h1
    have e : κ x y * star (κ x y) = (Complex.normSq (κ x y) : ℂ) := Complex.mul_conj _
    rw [e] at h1
    exact Complex.normSq_eq_zero.mp (by exact_mod_cast h1)

end ReciprocityTheory.ChartRestriction.DS.Mult1
end

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

theorem thmM_of_xi (h : UnitaryGroupStructuralFacts) (hXi : Formalism.FourierDecayAlt.B.XiExists) : ThmM :=
  theoremM_of h hXi (stBeHerm h) (stBePos h) (stSchurW h) (stSInt h) stSchurG (stPairs h) (stBeConv h) (stBeEquiv h)
    (stRepro h) (stSmooth h) stFrame (stInvGroup h) stInvChar stInvCC (stReps h) (stTransM h) (stSym h) (stSymBeta h)
    (stBetaInf h) (stDichoG h) (stDichoW h) (stMixed h) rankOneMinors

theorem thmM : ThmM := thmM_of_xi multiplicity_one_hypotheses_hold ReciprocityTheory.ChartRestriction.DS.Xi.xiExists

end ReciprocityTheory.ChartRestriction.DS.Mult1
