module

public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.FiniteInfinitePlaceProduct

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.AdmissibleVectors
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace AdmissibleVectors

set_option synthInstance.maxHeartbeats 400000

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {k : ℕ}

omit [_root_.NumberField.IsTotallyComplex E] in
theorem map_wd (μ : Measure (GA E k)) [μ.IsHaarMeasure] (β : GA E k → ℝ≥0∞) (t : GA E k) :
    Measure.map (MeasurableEquiv.mulLeft t⁻¹) (μ.withDensity β) = μ.withDensity fun g => β (t * g) := by
  ext s hs
  rw [Measure.map_apply (MeasurableEquiv.mulLeft t⁻¹).measurable hs,
    withDensity_apply _ ((MeasurableEquiv.mulLeft t⁻¹).measurable hs), withDensity_apply _ hs,
    ← lintegral_indicator ((MeasurableEquiv.mulLeft t⁻¹).measurable hs), ← lintegral_indicator hs]
  rw [← lintegral_mul_left_eq_self (μ := μ) _ t]
  congr 1
  funext x
  by_cases hx : x ∈ s <;> simp [hx]

end AdmissibleVectors

open AdmissibleVectors in
set_option synthInstance.maxHeartbeats 400000 in
theorem sum_wt_mul_massS_le_inv_pow_mul_total_mass : Q1 → Q2 → N2 → N3 → C1 := by
  intro _ hQ2 hN2 hN3 E _ _ _ k μ _ hk β hβ w l Φ hΦ hΦu hint
  set t := fl k w (Iwasawa.torusPow (w.adicCompletion E) k l) with ht
  obtain ⟨hsf, hinv, -⟩ := (hN3 E k).1 0 (by omega)
  have := hsf
  obtain ⟨hUU, -⟩ := (hN3 E k).2.2.2 hk
  have hq0 : (Ideal.absNorm w.asIdeal : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  set c : ℝ≥0∞ := ENNReal.ofReal ((Ideal.absNorm w.asIdeal : ℝ) ^ rhoPair l) with hc
  have hcpos : 0 < (Ideal.absNorm w.asIdeal : ℝ) ^ rhoPair l :=
    zpow_pos (lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hq0)) _
  have hc0 : c ≠ 0 := by rw [hc]; exact (ENNReal.ofReal_pos.2 hcpos).ne'
  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hβ0m : Measurable fun g => β (t * g) := hβ.1.comp (measurable_const_mul t)
  set β' : GA E k → ℝ≥0∞ := fun g => c⁻¹ * β (t * g) with hβ'
  have hβ'm : Measurable β' := hβ0m.const_mul _
  have hwt : IsWt (nuP E k 0) β' := by
    refine ⟨hβ'm, fun g => ?_⟩
    simp only [hβ']
    rw [lintegral_const_mul c⁻¹ (f := fun h => β (t * (h * g))) (hβ0m.comp (measurable_mul_const g))]
    have := hN2 E k w l (fun h => β (h * (t * g))) (hβ.1.comp (measurable_mul_const _))
    rw [← ht] at this
    simp only [mul_assoc, inv_mul_cancel_left] at this
    rw [this, hβ.2 (t * g), mul_one, ENNReal.inv_mul_cancel hc0 hctop]

  have hH : ∀ᵐ h ∂nuP E k 0, h ∈ {h : GA E k | UU 0 (t * h * t⁻¹)} := by
    set A := {h : GA E k | ¬ UU 0 h}
    have hA : nuP E k 0 A = 0 := ae_iff.1 hUU
    set S := toMeasurable (nuP E k 0) A
    have hS : MeasurableSet S := measurableSet_toMeasurable _ _
    have hS0 : nuP E k 0 S = 0 := by rw [measure_toMeasurable]; exact hA
    have hcm : Measurable fun h : GA E k => t * h * t⁻¹ := (measurable_const_mul t).mul_const _
    have := hN2 E k w l (S.indicator 1) (measurable_one.indicator hS)
    rw [lintegral_indicator_one hS, hS0, mul_zero] at this
    have h2 := (lintegral_eq_zero_iff ((measurable_one.indicator hS).comp hcm)).1 this
    filter_upwards [h2] with h hh
    by_contra hn
    have : t * h * t⁻¹ ∈ S := subset_toMeasurable _ _ hn
    simp [Set.indicator_of_mem this] at hh
  have hone : ∀ g, ∫⁻ r, ∫⁻ h, β (r⁻¹ * h * g) ∂nuP E k 0 ∂Measure.dirac (1 : GA E k) = 1 := fun g => by
    rw [lintegral_dirac]; simpa using hβ.2 g
  have hΦ'm : Measurable fun g => Φ (t * g) := hΦ.comp (measurable_const_mul t)
  have hΦ'H : ∀ h ∈ {h : GA E k | UU 0 (t * h * t⁻¹)}, ∀ g, Φ (t * (h * g)) = Φ (t * g) := by
    intro h hh g
    have := hΦu _ hh (t * g)
    simpa [mul_assoc] using this
  have hmap := map_wd μ β t
  have hsm : μ.withDensity (fun g => β (t * g)) = c • μ.withDensity β' := by
    rw [← withDensity_smul _ hβ'm]
    congr 1
    funext g
    simp [hβ', ← mul_assoc, ENNReal.mul_inv_cancel hc0 hctop]
  have hint0 : Integrable (fun g => Φ (t * g)) (μ.withDensity fun g => β (t * g)) := by
    rw [← hmap, integrable_map_equiv]
    simpa [Function.comp_def] using hint
  have hint' : Integrable (fun g => Φ (t * g)) (μ.withDensity β') := by
    have h1 : μ.withDensity β' = c⁻¹ • μ.withDensity (fun g => β (t * g)) := by
      rw [hsm, smul_smul, ENNReal.inv_mul_cancel hc0 hctop, one_smul]
    rw [h1]
    exact hint0.smul_measure (ENNReal.inv_ne_top.2 hc0)
  have hQ := hQ2 (GA E k) μ (nuP E k 0) (Measure.dirac 1) _ β' β hinv hH hwt hβ.1 hone
    (fun g => Φ (t * g)) hΦ'm hΦ'H hint'
  simp only [integral_dirac, one_mul] at hQ
  refine ⟨hQ.1, ?_⟩
  have e1 : ∫ g, Φ g ∂μ.withDensity β = ∫ g, Φ (t * g) ∂μ.withDensity fun g => β (t * g) := by
    rw [← hmap, integral_map_equiv]
    simp [MeasurableEquiv.coe_mulLeft]
  rw [e1, hsm, integral_smul_measure, hQ.2, hc, ENNReal.toReal_ofReal hcpos.le, Complex.real_smul]
  push_cast
  rfl

end PositivityTheory.AdelicQuotientData

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.LApply
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace PKY

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

def I (ν : Measure (GA E k)) [IsFiniteMeasure ν] : XB E k →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ g, f g ∂ν
      map_add' := fun f f' => integral_add (f.integrable ν) (f'.integrable ν)
      map_smul' := fun c f => integral_smul c (fun g => f g) }
    (ν.real Set.univ) (fun f => f.norm_integral_le_mul_norm ν)

def L (ν : Measure (GA E k)) [IsFiniteMeasure ν] (φ' : XB E k) (h : GA E k) : XB E k →L[ℂ] ℂ :=
  (I ν).comp (((ContinuousLinearMap.mul ℂ (XB E k)).flip (star φ')).comp (Rt E k h))

theorem L_apply (ν : Measure (GA E k)) [IsFiniteMeasure ν] (φ' x : XB E k) (h : GA E k) :
    L ν φ' h x = ∫ g, x (g * h) * conj (φ' g) ∂ν := by
  first
    | rfl
    | (simp only [L, I, ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.flip_apply,
        ContinuousLinearMap.mul_apply', LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk,
        BoundedContinuousFunction.mul_apply, BoundedContinuousFunction.star_apply]
       rfl)

end PKY

theorem ky_of : W0 → KY := by
  intro hW E _ _ _ k μ _ hk β hβ φ'
  have hfin : (μ.withDensity β) (band E k) < ⊤ := (hW E k μ hk).2 β hβ
  haveI hνf : IsFiniteMeasure ((μ.withDensity β).restrict (band E k)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  have hLR : ∀ (h a : GlobalTheory.CuspRep.GA E k) (x : PositivityTheory.jumpWindows.XB E k),
      PKY.L ((μ.withDensity β).restrict (band E k)) φ' h (PositivityTheory.jumpWindows.Rt E k a x) =
        PKY.L ((μ.withDensity β).restrict (band E k)) φ' (h * a) x := by
    intro h a x
    show PKY.I _ (((ContinuousLinearMap.mul ℂ (PositivityTheory.jumpWindows.XB E k)).flip (star φ'))
        (PositivityTheory.jumpWindows.Rt E k h (PositivityTheory.jumpWindows.Rt E k a x))) =
      PKY.I _ (((ContinuousLinearMap.mul ℂ (PositivityTheory.jumpWindows.XB E k)).flip (star φ')) (PositivityTheory.jumpWindows.Rt E k (h * a) x))
    rw [map_mul]
    rfl
  let Y : Submodule ℂ (PositivityTheory.jumpWindows.XB E k) :=
    { carrier := {x | (∀ (t : ℝ) (g : GlobalTheory.CuspRep.GA E k), x (GlobalTheory.UnitaryBC.splitCentre E k t * g) = x g) ∧
          ∀ h, PKY.L ((μ.withDensity β).restrict (band E k)) φ' h x = 0}
      add_mem' := by
        rintro x x' ⟨hx1, hx2⟩ ⟨hx1', hx2'⟩
        refine ⟨fun t g => ?_, fun h => ?_⟩
        · show x (GlobalTheory.UnitaryBC.splitCentre E k t * g) + x' (GlobalTheory.UnitaryBC.splitCentre E k t * g) = x g + x' g
          rw [hx1, hx1']
        · rw [map_add (f := _), hx2, hx2', add_zero]
      zero_mem' := ⟨fun t g => rfl, fun h => map_zero _⟩
      smul_mem' := by
        rintro c x ⟨hx1, hx2⟩
        refine ⟨fun t g => ?_, fun h => ?_⟩
        · show c • x (GlobalTheory.UnitaryBC.splitCentre E k t * g) = c • x g
          rw [hx1]
        · rw [map_smul, hx2, smul_zero] }
  have hmemL : ∀ x, x ∈ Y ↔ (∀ (t : ℝ) (g : GlobalTheory.CuspRep.GA E k), x (GlobalTheory.UnitaryBC.splitCentre E k t * g) = x g) ∧
      ∀ h, PKY.L ((μ.withDensity β).restrict (band E k)) φ' h x = 0 := fun x => Iff.rfl
  have hc : IsClosed (Y : Set (PositivityTheory.jumpWindows.XB E k)) := by
    have hset : (Y : Set (PositivityTheory.jumpWindows.XB E k)) =
        (⋂ (t : ℝ), ⋂ (g : GlobalTheory.CuspRep.GA E k),
          {x : PositivityTheory.jumpWindows.XB E k | x (GlobalTheory.UnitaryBC.splitCentre E k t * g) = x g}) ∩
        ⋂ h, {x : PositivityTheory.jumpWindows.XB E k | PKY.L ((μ.withDensity β).restrict (band E k)) φ' h x = 0} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
      exact hmemL x
    rw [hset]
    exact (isClosed_iInter fun t => isClosed_iInter fun g =>
        isClosed_eq (BoundedContinuousFunction.evalCLM ℂ (GlobalTheory.UnitaryBC.splitCentre E k t * g)).continuous
          (BoundedContinuousFunction.evalCLM ℂ g).continuous).inter
      (isClosed_iInter fun h => isClosed_eq (PKY.L _ φ' h).continuous continuous_const)
  refine ⟨Y, hc, ?_, ?_, ?_⟩
  · intro a x hx
    obtain ⟨hx1, hx2⟩ := (hmemL x).mp hx
    refine (hmemL _).mpr ⟨fun t g => ?_, fun h => ?_⟩
    · show x (GlobalTheory.UnitaryBC.splitCentre E k t * g * a) = x (g * a)
      rw [mul_assoc, hx1]
    · rw [hLR]
      exact hx2 _
  · intro x
    rw [hmemL]
    exact and_congr Iff.rfl (forall_congr' fun h => by rw [PKY.L_apply])
  · intro φ hφ ψ S U η s hcut
    have hφ2 := ((hmemL φ).mp hφ).2
    let F : (Fin k → GlobalTheory.CuspRep.Ad E) → PositivityTheory.jumpWindows.XB E k := fun y => (η y : ℂ) • PositivityTheory.jumpWindows.Rt E k (s y)⁻¹ φ
    have hFc : Continuous F := hcut.contV
    have hFs : HasCompactSupport F := by
      have h1 : HasCompactSupport (fun y => (η y : ℂ)) :=
        hcut.cpt.comp_left (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero
      exact h1.smul_right (f' := fun y => PositivityTheory.jumpWindows.Rt E k (s y)⁻¹ φ)
    have hFi : Integrable F (GroundTheory.Automorphic.FourierWhittaker.vecMeasure E (Fin k)) :=
      hFc.integrable_of_hasCompactSupport hFs
    have hpt : ∀ g : GlobalTheory.CuspRep.GA E k,
        (∫ y, (η y : ℂ) * φ (g * (s y)⁻¹) ∂GroundTheory.Automorphic.FourierWhittaker.vecMeasure E (Fin k)) =
          (∫ y, F y ∂GroundTheory.Automorphic.FourierWhittaker.vecMeasure E (Fin k)) (g * 1) := by
      intro g
      rw [mul_one]
      exact (BoundedContinuousFunction.evalCLM ℂ g).integral_comp_comm hFi
    simp_rw [hpt]
    rw [← PKY.L_apply, ← ContinuousLinearMap.integral_comp_comm _ hFi]
    have hz : ∀ y, PKY.L ((μ.withDensity β).restrict (band E k)) φ' 1 (F y) = 0 := fun y => by
      show PKY.L _ φ' 1 ((η y : ℂ) • PositivityTheory.jumpWindows.Rt E k (s y)⁻¹ φ) = 0
      rw [map_smul, hLR, one_mul, hφ2, smul_zero]
    simp only [hz, integral_zero]

end PositivityTheory.AdelicQuotientData

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ThetaDecayingFunction
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace ThetaDecayingFunction

theorem key {x C1 D : ℝ} {a k : ℕ} (ha : a ≠ 0) (hx : 0 < x) (hC : 0 < C1) (hD : 0 < D) :
    ((D ^ ((k : ℝ)⁻¹) * (x / C1) ^ ((a : ℝ)⁻¹)) ^ a)⁻¹ * x = C1 * D ^ (-(a : ℝ) / k) := by
  rw [mul_pow, ← Real.rpow_mul_natCast hD.le, Real.rpow_inv_natCast_pow (div_nonneg hx.le hC.le) ha,
    show -(a : ℝ) / k = -((k : ℝ)⁻¹ * a) by ring, Real.rpow_neg hD.le]
  have : 0 < D ^ ((k : ℝ)⁻¹ * a) := Real.rpow_pos_of_pos hD _
  field_simp

theorem le_height {x C1 D h : ℝ} {a k : ℕ} (ha : a ≠ 0) (hx : 0 < x) (hC : 0 < C1) (hD : 0 < D)
    (ht : 0 < h / D ^ ((k : ℝ)⁻¹)) (hb : x ≤ C1 * (h / D ^ ((k : ℝ)⁻¹)) ^ a) :
    D ^ ((k : ℝ)⁻¹) * (x / C1) ^ ((a : ℝ)⁻¹) ≤ h := by
  have hDk : 0 < D ^ ((k : ℝ)⁻¹) := Real.rpow_pos_of_pos hD _
  have h1 : (x / C1) ^ ((a : ℝ)⁻¹) ≤ h / D ^ ((k : ℝ)⁻¹) := by
    rw [← pow_le_pow_iff_left₀ (Real.rpow_nonneg (div_nonneg hx.le hC.le) _) ht.le ha,
      Real.rpow_inv_natCast_pow (div_nonneg hx.le hC.le) ha, div_le_iff₀' hC]
    exact hb
  calc _ ≤ D ^ ((k : ℝ)⁻¹) * (h / D ^ ((k : ℝ)⁻¹)) := mul_le_mul_of_nonneg_left h1 hDk.le
    _ = h := by field_simp

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {k : ℕ}

theorem part1 (hD : D0) (hH : H0) (hG : ThetaSeriesBound) (hk : 1 ≤ k) (φ : GA E k → ℂ) (hφ : Dec φ)
    (Cf : Set (Fin k → Af E)) (hCf : IsCompact Cf) (a : ℕ) (hka : k ≤ a) :
    ∃ (M : ℕ) (C : ℝ), ∀ g : GA E k, (∑' ξ : {ξ : Fin k → E // ξ ≠ 0}, ENNReal.ofReal (Cf.indicator
      (fun _ => ((1 + ‖fun i => pInf E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val) i)‖) ^ M)⁻¹)
      fun i => pFin E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val) i))) * ‖φ g‖ₑ ≤
        ENNReal.ofReal (C * Dt g ^ (-(a : ℝ) / k)) := by
  obtain ⟨M, C, hMC⟩ := hG E k Cf hCf a hka
  obtain ⟨C1, hC1⟩ := hφ a
  refine ⟨M, C * C1, fun g => ?_⟩
  have hDg : 0 < Dt g := (hD E k).1 g
  by_cases h0 : φ g = 0
  · simp [h0]
  have hx : 0 < ‖φ g‖ := norm_pos_iff.2 h0
  have hne : (fun _ : Fin k => (1 : E)) ≠ 0 := by
    intro h
    have := congrFun h ⟨0, hk⟩
    simp at this
  have hC1p : 0 < C1 := by
    have h1 := hC1 g _ hne
    have h2 := (hH E k).1 g _ hne
    by_contra hc
    replace hc := not_lt.1 hc
    have : C1 * ht g (fun _ => 1) ^ a ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc (pow_nonneg h2.le _)
    linarith
  have ha : a ≠ 0 := by omega
  have hr : 0 < Dt g ^ ((k : ℝ)⁻¹) * (‖φ g‖ / C1) ^ ((a : ℝ)⁻¹) :=
    mul_pos (Real.rpow_pos_of_pos hDg _) (Real.rpow_pos_of_pos (div_pos hx hC1p) _)
  have hbound := hMC g _ hr fun ξ hξ => le_height ha hx hC1p hDg ((hH E k).1 g ξ hξ) (hC1 g ξ hξ)
  calc _ ≤ ENNReal.ofReal (C * ((Dt g ^ ((k : ℝ)⁻¹) * (‖φ g‖ / C1) ^ ((a : ℝ)⁻¹)) ^ a)⁻¹) * ‖φ g‖ₑ := by
        gcongr
    _ = ENNReal.ofReal (C * ((Dt g ^ ((k : ℝ)⁻¹) * (‖φ g‖ / C1) ^ ((a : ℝ)⁻¹)) ^ a)⁻¹ * ‖φ g‖) := by
        rw [ENNReal.ofReal_mul' (norm_nonneg _), ofReal_norm]
    _ = _ := by rw [mul_assoc, key ha hx hC1p hDg, mul_assoc]

theorem ind_le {C₀ : Set (Fin k → Ad E)} {R : ℝ} (hR : ∀ y ∈ C₀, ‖fun i => pInf E (y i)‖ ≤ R) (M : ℕ)
    (y : Fin k → Ad E) :
    C₀.indicator (fun _ => (1 : ℝ≥0∞)) y ≤ ENNReal.ofReal ((1 + max R 0) ^ M) *
      ENNReal.ofReal (((fun y : Fin k → Ad E => fun i => pFin E (y i)) '' C₀).indicator
        (fun _ => ((1 + ‖fun i => pInf E (y i)‖) ^ M)⁻¹) fun i => pFin E (y i)) := by
  by_cases hy : y ∈ C₀
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (Set.mem_image_of_mem _ hy),
      ← ENNReal.ofReal_mul (by positivity), ENNReal.one_le_ofReal, ← div_eq_mul_inv,
      one_le_div (by positivity)]
    exact pow_le_pow_left₀ (by positivity) (by linarith [hR y hy, le_max_left R 0]) M
  · rw [Set.indicator_of_notMem hy]
    exact bot_le

theorem part2 (hD : D0) (hN : N0) (hH : H0) (hG : ThetaSeriesBound) (hk : 1 ≤ k) (φ : GA E k → ℂ) (hφ : Dec φ)
    (C₀ : Set (Fin k → Ad E)) (hC₀ : IsCompact C₀) (a : ℕ) (hka : k ≤ a) :
    ∃ C : ℝ, ∀ g : GA E k,
      (∑' ξ : RowT E k k, C₀.indicator (fun _ => (1 : ℝ≥0∞)) (lastRow (ratGL E k (gam ξ) * g))) * ‖φ g‖ₑ ≤
        ENNReal.ofReal (C * Dt g ^ (-(a : ℝ) / k)) := by
  have hcF : Continuous fun y : Fin k → Ad E => fun i => pFin E (y i) :=
    continuous_pi fun i => (GlobalTheory.CuspRep.ContAut.continuous_pFin E).comp (continuous_apply i)
  have hcI : Continuous fun y : Fin k → Ad E => fun i => pInf E (y i) :=
    continuous_pi fun i => (GlobalTheory.CuspRep.ContAut.continuous_pInf E).comp (continuous_apply i)
  obtain ⟨R, hR⟩ := hC₀.exists_bound_of_continuousOn hcI.continuousOn
  obtain ⟨M, C', hC'⟩ := part1 hD hH hG hk φ hφ _ (hC₀.image hcF) a hka
  obtain ⟨-, -, -, -, -, -, -, -, -, hlast⟩ := hN E k k hk le_rfl
  let e : {ξ : Fin k → E // ξ ≠ 0} ≃ RowT E k k :=
    { toFun := fun ξ => ⟨ξ.1, ξ.2, fun i hi => absurd i.2 (by omega)⟩
      invFun := fun ξ => ⟨ξ.1, ξ.2.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hK : (0 : ℝ) ≤ (1 + max R 0) ^ M := by positivity
  refine ⟨(1 + max R 0) ^ M * C', fun g => ?_⟩
  rw [← e.tsum_eq]
  calc _ = (∑' ξ : {ξ : Fin k → E // ξ ≠ 0}, C₀.indicator (fun _ => (1 : ℝ≥0∞))
          ((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val)) * ‖φ g‖ₑ := by
        congr 1
        exact tsum_congr fun ξ => by rw [hlast]; rfl
    _ ≤ (∑' ξ : {ξ : Fin k → E // ξ ≠ 0}, ENNReal.ofReal ((1 + max R 0) ^ M) * ENNReal.ofReal (
          ((fun y : Fin k → Ad E => fun i => pFin E (y i)) '' C₀).indicator
          (fun _ => ((1 + ‖fun i => pInf E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val) i)‖) ^ M)⁻¹)
          fun i => pFin E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val) i))) * ‖φ g‖ₑ :=
        by
        gcongr with ξ
        exact ind_le hR M _
    _ = ENNReal.ofReal ((1 + max R 0) ^ M) * ((∑' ξ : {ξ : Fin k → E // ξ ≠ 0}, ENNReal.ofReal (
          ((fun y : Fin k → Ad E => fun i => pFin E (y i)) '' C₀).indicator
          (fun _ => ((1 + ‖fun i => pInf E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val) i)‖) ^ M)⁻¹)
          fun i => pFin E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val) i))) * ‖φ g‖ₑ) := by
        rw [ENNReal.tsum_mul_left, mul_assoc]
    _ ≤ ENNReal.ofReal ((1 + max R 0) ^ M) * ENNReal.ofReal (C' * Dt g ^ (-(a : ℝ) / k)) :=
        by
        gcongr
        exact hC' g
    _ = _ := by rw [← ENNReal.ofReal_mul hK, mul_assoc]

end ThetaDecayingFunction

theorem theta_decaying_of_bound : D0 → N0 → H0 → ThetaSeriesBound → ThetaDecaying := by
  intro hD hN hH hG E _ _ _ k hk φ hφ
  exact ⟨fun Cf hCf a hka => ThetaDecayingFunction.part1 hD hH hG hk φ hφ Cf hCf a hka,
    fun C₀ hC₀ a hka => ThetaDecayingFunction.part2 hD hN hH hG hk φ hφ C₀ hC₀ a hka⟩

end PositivityTheory.AdelicQuotientData

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.SphericalIntegralStep
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace SphericalFunctionIntegral

open Formalism.UG GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.LFun Formalism.L2.Host

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem le_one (w : Pl E) (x : w.adicCompletion E) :
    ValuativeRel.valuation (w.adicCompletion E) x ≤ 1 ↔ Valued.v x ≤ 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation _) Valued.v).le_one_iff_le_one

theorem mem_Ov (w : Pl E) {x : w.adicCompletion E} (h : x ∈ (ValuativeRel.valuation (w.adicCompletion E)).integer) :
    x ∈ Ov E w :=
  (le_one w x).1 ((Valuation.mem_integer_iff _ _).1 h)

theorem int_KGL (w : Pl E) {x : GL (Fin k) (w.adicCompletion E)}
    (hx : x ∈ GLnLocal.integralGL (w.adicCompletion E) k) : x ∈ KGL w (n := k) := by
  obtain ⟨h1, h2⟩ := (GLnLocal.mem_integralGL_iff _ _).1 hx
  have hi : Function.Injective fun A : Matrix (Fin k) (Fin k) (Ov E w) => A.map (Ov E w).subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, mem_Ov w (h1 i j)⟩, Matrix.of fun i j => ⟨(x⁻¹ : GL (Fin k) (w.adicCompletion E)).1 i j, mem_Ov w (h2 i j)⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.inv_mul

theorem fix {w : Pl E} {B : Multiset ℂˣ} {φ : XB E k} (h : SatFn w B φ) {x : GL (Fin k) (w.adicCompletion E)}
    (hx : x ∈ GLnLocal.integralGL (w.adicCompletion E) k) : Rt E k (fl k w x) φ = φ := by
  rcases h with rfl | h
  · exact map_zero _
  · exact GlobalTheory.LGrp.mem_fixed.1 h.2.1 x (int_KGL w hx)

variable [_root_.NumberField.IsTotallyComplex E]

theorem step (hG : jumpWindows.G0) (S : Finset (Pl E)) (φ : XB E k) (g κ : GA E k)
    (hfix : ∀ w, w ∉ S → ∀ x ∈ GLnLocal.integralGL (w.adicCompletion E) k, Rt E k (fl k w x) φ = φ)
    (hinf : cInf κ = 1) (hS : ∀ w ∈ S, cLoc w κ = 1)
    (hint : ∀ w, cLoc w κ ∈ GLnLocal.integralGL (w.adicCompletion E) k) (T : Finset (Pl E)) :
    ∃ h : GA E k, φ (g * h) = φ g ∧ cInf h = cInf κ ∧ (∀ w, (w ∈ S ∨ w ∈ T) → cLoc w h = cLoc w κ) ∧
      (∀ w, w ∉ S → w ∉ T → cLoc w h = 1) := by
  classical
  obtain ⟨-, -, h3, h4, h5, -⟩ := hG E k
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨1, by rw [mul_one], by rw [map_one, hinf], fun w hw => ?_, fun w _ _ => map_one _⟩
    rcases hw with hw | hw
    · rw [map_one, hS w hw]
    · simp at hw
  | insert w T hwT ih =>
    obtain ⟨h, hf0, hi, hl, ho⟩ := ih
    by_cases hwS : w ∈ S
    · refine ⟨h, hf0, hi, fun v hv => ?_, fun v hv hv' => ho v hv fun h' => hv' (Finset.mem_insert_of_mem h')⟩
      rcases hv with hv | hv
      · exact hl v (Or.inl hv)
      · rcases Finset.mem_insert.1 hv with rfl | hv
        · exact hl v (Or.inl hwS)
        · exact hl v (Or.inr hv)
    · refine ⟨h * fl k w (cLoc w κ), ?_, ?_, fun v hv => ?_, fun v hv hv' => ?_⟩
      · have e := congrArg (fun ψ : XB E k => ψ (g * h)) (hfix w hwS _ (hint w))
        simp only [Rt_apply] at e
        rw [← mul_assoc, e, hf0]
      · rw [map_mul, h3, mul_one, hi]
      · rw [map_mul]
        by_cases hvw : v = w
        · subst hvw
          rw [h4, ho v hwS hwT, one_mul]
        · rw [h5 _ _ _ hvw, mul_one]
          rcases hv with hv | hv
          · exact hl v (Or.inl hv)
          · exact hl v (Or.inr ((Finset.mem_insert.1 hv).resolve_left hvw))
      · have hvw : v ≠ w := fun e => hv' (e ▸ Finset.mem_insert_self w T)
        rw [map_mul, h5 _ _ _ hvw, mul_one]
        exact ho v hv fun h' => hv' (Finset.mem_insert_of_mem h')


open jumpWindows.GeneralLinearEntryConvergence in
theorem sph (hG : jumpWindows.G0) (S : Finset (Pl E)) (φ : XB E k)
    (hfix : ∀ w, w ∉ S → ∀ x ∈ GLnLocal.integralGL (w.adicCompletion E) k, Rt E k (fl k w x) φ = φ) :
    SphOff S (φ : GA E k → ℂ) := by
  intro g κ hinf hS hint
  choose H hH using step hG S φ g κ hfix hinf hS hint
  have hT : Tendsto H atTop (𝓝 κ) := by
    refine tendsto_gl κ H (tendsto_entry S κ H (fun T => (hH T).2.1) (fun T => (hH T).2.2.1)
      (fun T => (hH T).2.2.2)) (tendsto_entry S κ⁻¹ (fun T => (H T)⁻¹) (fun T => ?_) (fun T w hw => ?_)
      (fun T w hw hw' => ?_))
    · rw [map_inv, map_inv, (hH T).2.1]
    · rw [map_inv, map_inv, (hH T).2.2.1 w hw]
    · rw [map_inv, (hH T).2.2.2 w hw hw', inv_one]
  have hc : Continuous fun x : GA E k => φ (g * x) := φ.continuous.comp (continuous_const.mul continuous_id)
  have h1 := (hc.tendsto κ).comp hT
  have h2 : Tendsto ((fun x : GA E k => φ (g * x)) ∘ H) atTop (𝓝 (φ g)) := by
    have e : (fun x : GA E k => φ (g * x)) ∘ H = fun _ => φ g := funext fun T => (hH T).1
    rw [e]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique h1 h2

end SphericalFunctionIntegral

theorem spherical_function_of : jumpWindows.G0 → jumpWindows.G5 → C0 → K7 → K8 := by
  intro hG0 hG5 hC0 hK7 E _ _ _ k ψ hψ S hcond α φ hgood hsat
  obtain ⟨-, hrt, -, hreg⟩ := hG5 E k ψ hψ
  have hfix : ∀ w, w ∉ S → ∀ x ∈ GLnLocal.integralGL (w.adicCompletion E) k, Rt E k (fl k w x) φ = φ :=
    fun w hw x hx => SphericalFunctionIntegral.fix (hsat ⟨w, hw⟩) hx
  have hφ := SphericalFunctionIntegral.sph hG0 S φ hfix
  have hcont := (hreg φ hgood).1
  refine ⟨hφ, fun g κ hinf hS hint => ?_, fun g hg => ⟨fun g₀ hi hS hIn h0 => ?_, fun w hw => ?_⟩⟩
  · have e : Rt E k κ φ = φ := by
      ext x
      simp only [Rt_apply]
      exact hφ x κ hinf hS hint
    rw [← hrt, e]
  · refine hg (jumpWindows.convergence_entries_general_linear hG0 E k S (Wh ψ φ) hcont (fun w hw h hh h0 u => ?_) g g₀ hi hS hIn h0)
    obtain ⟨χ, -, -, hK⟩ := hK7 E k ψ hψ w (hcond w hw)
    rw [hK (α ⟨w, hw⟩) φ hgood (hsat ⟨w, hw⟩) h hh u, h0, zero_mul]
  · obtain ⟨χ, -, -, hK⟩ := hK7 E k ψ hψ w (hcond w hw)
    obtain ⟨g', hg', e, -, -⟩ := (hC0 E k S).2.2.2.2.2.2 w g
    have h1 := hK (α ⟨w, hw⟩) φ hgood (hsat ⟨w, hw⟩) g' hg' (cLoc w g)
    rw [← e] at h1
    rw [h1] at hg
    have h2 := right_ne_zero_of_mul hg
    by_contra hA
    apply h2
    rw [sphericalWhittaker, if_neg hA]

end PositivityTheory.AdelicQuotientData

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.HeightDropSingle
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace HeightDropSingle

open scoped NumberField.AdeleRing

theorem euclid_drop {F : Type*} [NormedField F] {n : ℕ} (p : Fin (n + 1)) (z : Fin (n + 1) → F)
    (hz : z p = 0) : euclidNorm z = euclidNorm (fun j => z (p.succAbove j)) := by
  simp only [euclidNorm]
  rw [Fin.sum_univ_succAbove _ p, hz]
  simp

theorem sup_drop {F : Type*} [NormedField F] {n : ℕ} (p : Fin (n + 1)) (z : Fin (n + 1) → F)
    (hz : z p = 0) : ‖z‖ = ‖fun j => z (p.succAbove j)‖ := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    rcases Fin.eq_self_or_eq_succAbove p i with rfl | ⟨j, rfl⟩
    · rw [hz, norm_zero]; exact norm_nonneg _
    · exact norm_le_pi_norm (fun j => z (p.succAbove j)) j
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => norm_le_pi_norm z _

theorem adelicNorm_drop {K : Type*} [Field K] [NumberField K] {n : ℕ} (p : Fin (n + 1))
    (y : Fin (n + 1) → 𝔸[K]) (hy : y p = 0) :
    adelicNorm y = adelicNorm (fun j => y (p.succAbove j)) := by
  unfold adelicNorm
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [euclid_drop p (infComp w y) (by show (y p).1 w = 0; rw [hy]; rfl)]
    rfl
  · refine finprod_congr fun v => ?_
    rw [sup_drop p (finComp v y) (by show (y p).2 v = 0; rw [hy]; rfl)]
    rfl

theorem height_single {K : Type*} [Field K] [NumberField K] {n : ℕ} (x : GL (Fin n) 𝔸[K]) (i : Fin n)
    (hx : x.val i = Pi.single i 1) : Reduction.height x (Pi.single i (1 : K)) = 1 := by
  unfold Reduction.height
  have : ratVec (Pi.single i (1 : K)) ᵥ* (x : Matrix (Fin n) (Fin n) 𝔸[K]) = x.val i := by
    ext c
    simp [ratVec, vecMul, dotProduct, Pi.single_apply]
  rw [this, hx, adelicNorm_single_one]

end HeightDropSingle

theorem short_rows_embedding_of : D0 → MinkowskiBoundAlt → K1 → CornerEmbedding → ShortRowsEmbedding := by
  intro hD hG hK1 hK5e E _ _ _ m k hk hkm ι hι
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨C, hC⟩ := hG E n (by omega)
  have hDm := hD E (n + 1)
  have hDk := hD E k
  have hDι : ∀ g, Dt (ι g) = Dt g := ((hK5e E (n + 1) k hkm.le).2 ι hι).2.2.2.1
  have hK := (hK1 E (n + 1) (by omega)).2.2.1
  refine ⟨C, fun g u => ⟨fun hu => ?_, fun hu => ?_⟩⟩
  · obtain ⟨x, hx⟩ : ∃ x, x = u * ι g := ⟨_, rfl⟩
    rw [← hx]
    have hDx : Dt x = Dt g := by rw [hx, hDm.2.1, hDm.2.2.2.2.1 0 u hu, hDι, one_mul]
    have hrow : x.val (Fin.last n) = Pi.single (Fin.last n) 1 := by
      ext c
      rw [hx, Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single (Fin.last n)]
      · rw [hu.2.1, one_mul, hι g]
        have hk' : ¬ ((Fin.last n : ℕ) < k ∧ (c : ℕ) < k) := by simp; omega
        simp only [embM, Matrix.of_apply, dif_neg hk', Matrix.one_apply, Pi.single_apply, eq_comm]
      · intro j _ hj
        rw [hu.1 _ _ (lt_of_le_of_ne (Fin.le_last j) hj), zero_mul]
      · simp
    have hpos := hDk.1 g
    refine (hK x (Pi.single (Fin.last n) 1) fun h => by simpa using congrFun h (Fin.last n)).trans (le_of_eq ?_)
    unfold ht
    rw [HeightDropSingle.height_single x _ hrow, hDx, Real.rpow_neg hpos.le, one_div]
  · obtain ⟨x, hx⟩ : ∃ x, x = u * ι g := ⟨_, rfl⟩
    rw [← hx]
    have hDx : Dt x = Dt g := by rw [hx, hDm.2.1, hDm.2.2.2.2.1 (k + 1) u hu, hDι, one_mul]
    set p : Fin (n + 1) := ⟨k, hkm⟩ with hp
    have hcol : ∀ i, x.val i p = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) (Ad E)) i p := by
      intro i
      rw [hx, Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single p]
      · rw [hι g]
        have hk' : ¬ ((p : ℕ) < k ∧ (p : ℕ) < k) := by simp [p]
        simp only [embM, Matrix.of_apply, dif_neg hk', Matrix.one_apply_eq, mul_one]
        exact hu.2.2 i p (by simp [p])
      · intro j _ hj
        rw [hι g]
        have hk' : ¬ ((j : ℕ) < k ∧ (p : ℕ) < k) := by simp [p]
        simp only [embM, Matrix.of_apply, dif_neg hk', Matrix.one_apply_ne hj, mul_zero]
      · simp
    set M' : Matrix (Fin n) (Fin n) (Ad E) := x.val.submatrix p.succAbove p.succAbove with hM'
    have hdet : M'.det = x.val.det := by
      rw [Matrix.det_succ_column x.val p, Finset.sum_eq_single p]
      · rw [hcol, Matrix.one_apply_eq, mul_one, Even.neg_one_pow ⟨(p : ℕ), rfl⟩, one_mul]
      · intro i _ hi
        rw [hcol, Matrix.one_apply_ne hi, mul_zero, zero_mul]
      · simp
    have hunit : IsUnit M'.det := by
      rw [hdet]; exact (Matrix.GeneralLinearGroup.det x).isUnit
    let g' : GA E n := M'.nonsingInvUnit hunit
    have hDg' : Dt g' = Dt x := by
      have : GeneralLinearGroup.det g' = GeneralLinearGroup.det x := Units.ext hdet
      unfold Dt; rw [this]
    obtain ⟨ξ', hξ'0, hξ'⟩ := hC g'
    let ξ : Fin (n + 1) → E := p.insertNth 0 ξ'
    have hξ0 : ξ ≠ 0 := by
      intro h; apply hξ'0; ext j
      simpa [ξ] using congrFun h (p.succAbove j)
    have hht : Reduction.height x ξ = Reduction.height g' ξ' := by
      unfold Reduction.height
      rw [HeightDropSingle.adelicNorm_drop p]
      · congr 1
        ext c
        simp only [vecMul, dotProduct]
        rw [Fin.sum_univ_succAbove _ p]
        simp [ξ, ratVec, g', M']
        rfl
      · simp only [vecMul, dotProduct]
        rw [Fin.sum_univ_succAbove _ p]
        simp [ξ, ratVec, hcol, Matrix.one_apply_ne (Fin.succAbove_ne p _)]
    have hpos := hDk.1 g
    refine (hK x ξ hξ0).trans ?_
    unfold ht at hξ' ⊢
    rw [hht, hDx]
    rw [hDg', hDx] at hξ'
    have h1 : Reduction.height g' ξ' ≤ C * Dt g ^ ((n : ℝ)⁻¹) :=
      (div_le_iff₀ (Real.rpow_pos_of_pos hpos _)).1 hξ'
    rw [div_le_iff₀ (Real.rpow_pos_of_pos hpos _)]
    calc Reduction.height g' ξ' ≤ C * Dt g ^ ((n : ℝ)⁻¹) := h1
      _ = C * Dt g ^ ((((n + 1 : ℕ) : ℝ) - 1)⁻¹ - ((n + 1 : ℕ) : ℝ)⁻¹) * Dt g ^ (((n + 1 : ℕ) : ℝ)⁻¹) := by
        rw [mul_assoc, ← Real.rpow_add hpos]
        congr 2
        push_cast
        ring

end PositivityTheory.AdelicQuotientData

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.QuadraticTransferReal
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace QuadraticTransferReal

theorem swap3 {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ρ : Measure β) (ν : Measure γ) [SFinite μ] [SFinite ρ] [SFinite ν]
    (F : α → β → γ → ℝ≥0∞) (hF : Measurable fun p : α × β × γ => F p.1 p.2.1 p.2.2) :
    ∫⁻ g, ∫⁻ r, ∫⁻ h, F g r h ∂ν ∂ρ ∂μ = ∫⁻ r, ∫⁻ h, ∫⁻ g, F g r h ∂μ ∂ν ∂ρ := by
  have h1 : Measurable fun q : α × β => ∫⁻ h, F q.1 q.2 h ∂ν := by
    have : Measurable fun p : (α × β) × γ => F p.1.1 p.1.2 p.2 :=
      hF.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
    exact this.lintegral_prod_right'
  rw [lintegral_lintegral_swap (f := fun g r => ∫⁻ h, F g r h ∂ν) h1.aemeasurable]
  refine lintegral_congr fun r => ?_
  have h2 : Measurable fun q : α × γ => F q.1 r q.2 :=
    hF.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
  exact lintegral_lintegral_swap (f := fun g h => F g r h) h2.aemeasurable

section
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem q1' (μ : Measure G) [μ.IsHaarMeasure] (ν ρ : Measure G) [SFinite ν] [SFinite ρ] (H : Set G)
    (β β₁ : G → ℝ≥0∞) (hinv : Measure.map (fun h => h⁻¹) ν = ν) (hH : ∀ᵐ h ∂ν, h ∈ H)
    (hβ : IsWt ν β) (hβ₁ : Measurable β₁) (h1 : ∀ g, ∫⁻ r, ∫⁻ h, β₁ (r⁻¹ * h * g) ∂ν ∂ρ = 1)
    (Φ : G → ℝ≥0∞) (hΦ : Measurable Φ) (hΦH : ∀ h ∈ H, ∀ g, Φ (h * g) = Φ g) :
    ∫⁻ g, Φ g ∂μ.withDensity β = ∫⁻ g, ∫⁻ r, Φ (r * g) ∂ρ ∂μ.withDensity β₁ := by
  have hβm := hβ.1
  have hm : Measurable fun p : G × G × G => β p.1 * Φ p.1 * β₁ (p.2.1⁻¹ * p.2.2 * p.1) := by fun_prop
  have hm' : Measurable fun p : G × G × G => β₁ p.1 * (Φ (p.2.1 * p.1) * β (p.2.2⁻¹ * p.2.1 * p.1)) := by
    fun_prop
  have hint : ∀ x, ∫⁻ h, β (h⁻¹ * x) ∂ν = 1 := by
    intro x
    have := lintegral_map (f := fun h => β (h * x)) (g := fun h : G => h⁻¹) (μ := ν)
      (hβm.comp (measurable_mul_const x)) measurable_inv
    rw [hinv, hβ.2 x] at this
    exact this.symm
  have hR : Measurable fun g => ∫⁻ r, Φ (r * g) ∂ρ := by
    have : Measurable fun p : G × G => Φ (p.2 * p.1) := hΦ.comp (measurable_snd.mul measurable_fst)
    exact this.lintegral_prod_right'
  rw [lintegral_withDensity_eq_lintegral_mul _ hβm hΦ, lintegral_withDensity_eq_lintegral_mul _ hβ₁ hR]
  calc ∫⁻ g, (β * Φ) g ∂μ
      = ∫⁻ g, ∫⁻ r, ∫⁻ h, β g * Φ g * β₁ (r⁻¹ * h * g) ∂ν ∂ρ ∂μ := by
        refine lintegral_congr fun g => ?_
        have hr : Measurable fun r => ∫⁻ h, β₁ (r⁻¹ * h * g) ∂ν := by
          have : Measurable fun p : G × G => β₁ (p.1⁻¹ * p.2 * g) := by fun_prop
          exact this.lintegral_prod_right'
        have e : ∀ r, ∫⁻ h, β g * Φ g * β₁ (r⁻¹ * h * g) ∂ν = β g * Φ g * ∫⁻ h, β₁ (r⁻¹ * h * g) ∂ν := by
          intro r
          exact lintegral_const_mul _ (by fun_prop)
        simp only [e, Pi.mul_apply]
        rw [lintegral_const_mul _ hr, h1 g, mul_one]
    _ = ∫⁻ r, ∫⁻ h, ∫⁻ g, β g * Φ g * β₁ (r⁻¹ * h * g) ∂μ ∂ν ∂ρ :=
        swap3 μ ρ ν (fun g r h => β g * Φ g * β₁ (r⁻¹ * h * g)) hm
    _ = ∫⁻ r, ∫⁻ h, ∫⁻ g, β₁ g * (Φ (r * g) * β (h⁻¹ * r * g)) ∂μ ∂ν ∂ρ := by
        refine lintegral_congr fun r => lintegral_congr_ae ?_
        filter_upwards [hH] with h hh
        rw [← lintegral_mul_left_eq_self _ (h⁻¹ * r)]
        refine lintegral_congr fun g => ?_
        have e1 : r⁻¹ * h * (h⁻¹ * r * g) = g := by group
        have e2 : Φ (h⁻¹ * r * g) = Φ (r * g) := by
          have := hΦH h hh (h⁻¹ * (r * g))
          rw [mul_inv_cancel_left] at this
          rw [mul_assoc]
          exact this.symm
        simp only [e1, e2]
        ring
    _ = ∫⁻ g, ∫⁻ r, ∫⁻ h, β₁ g * (Φ (r * g) * β (h⁻¹ * r * g)) ∂ν ∂ρ ∂μ :=
        (swap3 μ ρ ν (fun g r h => β₁ g * (Φ (r * g) * β (h⁻¹ * r * g))) hm').symm
    _ = ∫⁻ g, (β₁ * fun g => ∫⁻ r, Φ (r * g) ∂ρ) g ∂μ := by
        refine lintegral_congr fun g => ?_
        have e : ∀ r, ∫⁻ h, β₁ g * (Φ (r * g) * β (h⁻¹ * r * g)) ∂ν = β₁ g * Φ (r * g) := by
          intro r
          simp_rw [← mul_assoc (β₁ g)]
          rw [lintegral_const_mul _ (by fun_prop)]
          simp_rw [mul_assoc _ r g]
          rw [hint, mul_one]
        simp only [e, Pi.mul_apply]
        exact lintegral_const_mul _ (hΦ.comp (measurable_mul_const g))

end

theorem real_transfer {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (A : Measure X)
    (B : Measure Y) (m : Y → X) (F : X → ℝ) (hi : Integrable F A) (hiB : Integrable (fun y => F (m y)) B)
    (h₁ : ∫⁻ x, ENNReal.ofReal (F x) ∂A = ∫⁻ y, ENNReal.ofReal (F (m y)) ∂B)
    (h₂ : ∫⁻ x, ENNReal.ofReal (-F x) ∂A = ∫⁻ y, ENNReal.ofReal (-F (m y)) ∂B) :
    ∫ x, F x ∂A = ∫ y, F (m y) ∂B := by
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hiB, h₁, h₂]

theorem transfer {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (A : Measure X)
    (B : Measure Y) (m : Y → X) (hm : Measurable m) (Φ : X → ℂ) (hΦ : Measurable Φ) (P : (X → ℝ≥0∞) → Prop)
    (hP : ∀ f, Measurable f → P f → ∫⁻ x, f x ∂A = ∫⁻ y, f (m y) ∂B)
    (hn : P fun x => ‖Φ x‖ₑ) (hr₁ : P fun x => ENNReal.ofReal (Φ x).re)
    (hr₂ : P fun x => ENNReal.ofReal (-(Φ x).re)) (hi₁ : P fun x => ENNReal.ofReal (Φ x).im)
    (hi₂ : P fun x => ENNReal.ofReal (-(Φ x).im)) (hi : Integrable Φ A) :
    Integrable (fun y => Φ (m y)) B ∧ ∫ x, Φ x ∂A = ∫ y, Φ (m y) ∂B := by
  have hiB : Integrable (fun y => Φ (m y)) B := by
    refine ⟨(hΦ.comp hm).aestronglyMeasurable, ?_⟩
    have := hP _ (by fun_prop) hn
    rw [HasFiniteIntegral, ← this]
    exact hi.2
  refine ⟨hiB, ?_⟩
  apply Complex.ext
  · have a1 := integral_re hi
    have a2 := integral_re hiB
    simp only [RCLike.re_to_complex] at a1 a2
    rw [← a1, ← a2]
    exact real_transfer A B m (fun x => (Φ x).re) hi.re hiB.re
      (hP _ (by fun_prop) hr₁) (hP _ (by fun_prop) hr₂)
  · have a1 := integral_im hi
    have a2 := integral_im hiB
    simp only [RCLike.im_to_complex] at a1 a2
    rw [← a1, ← a2]
    exact real_transfer A B m (fun x => (Φ x).im) hi.im hiB.im
      (hP _ (by fun_prop) hi₁) (hP _ (by fun_prop) hi₂)

end QuadraticTransferReal

theorem closedSubgroup_cutoff_exists : Q2 := by
  intro G _ _ _ _ _ _ _ μ _ ν ρ _ _ H β β₁ hinv hH hβ hβ₁ h1 Φ hΦ hΦH hi
  have hm : Measurable fun p : G × G => p.2 * p.1 := measurable_snd.mul measurable_fst
  have key := QuadraticTransferReal.transfer (μ.withDensity β) ((μ.withDensity β₁).prod ρ) (fun p : G × G => p.2 * p.1) hm Φ hΦ
    (fun f => ∀ h ∈ H, ∀ g, f (h * g) = f g)
    (fun f hf hfH => by
      rw [QuadraticTransferReal.q1' μ ν ρ H β β₁ hinv hH hβ hβ₁ h1 f hf hfH, lintegral_prod (fun p : G × G => f (p.2 * p.1)) (hf.comp hm).aemeasurable])
    (fun h hh g => by simp only [hΦH h hh]) (fun h hh g => by simp only [hΦH h hh])
    (fun h hh g => by simp only [hΦH h hh]) (fun h hh g => by simp only [hΦH h hh])
    (fun h hh g => by simp only [hΦH h hh]) hi
  obtain ⟨hiB, he⟩ := key
  refine ⟨hiB.integral_prod_left, ?_⟩
  rw [he, integral_prod _ hiB]

end PositivityTheory.AdelicQuotientData

end
end
