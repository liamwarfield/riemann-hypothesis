module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivedActionDiscreteSeriesProperties
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HaarUniquenessConjugation
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumericalFamilyShapeGaps
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.MaximalCompactIsCompact
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesParameterUnique
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.IsUnitDetOfMemGV
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormFactor

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HaarEqSmul
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselDegree

open Formalism.FourierDecayAlt.P.HaarUniquenessConjugation

theorem isDS_iff {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool)
    (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    PI.UpqRep.IsDS ε lam σ ↔ Formalism.MainNotions.S.IsDS ε lam σ := Iff.rfl

theorem haar_eq_smul {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Mx k r} (hP : IsUnit P.det)
    (hH : Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r) (ν : Measure (Formalism.QuantumDeterminants.Mt k r))
    (hν : PI.BesselPeriodGGP.IsHaarOn (GG k r) ν) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ ν = c • (Formalism.REAL.muG ε).map (phi ε P) := by
  have hE := Formalism.REAL.isClosedEmbeddingMatrix
  have hC := Formalism.QuantumDeterminants.uHConj
  obtain ⟨hσ, h0, hconc, hleft⟩ := hν
  have hm := phi_measurable (ε := ε) hE hP
  have hce := phi_closedEmbedding (ε := ε) hE hP
  have hme : MeasurableEmbedding (phi ε P) := hce.measurableEmbedding
  have hr := phi_range hE hC hP hH
  have h2 : (ν.comap (phi ε P)).map (phi ε P) = ν := by
    rw [hme.map_comap]
    refine Measure.restrict_eq_self_of_ae_mem ?_
    rw [ae_iff, hr]
    exact hconc
  have hsf : SigmaFinite (ν.comap (phi ε P)) :=
    SigmaFinite.of_map _ hm.aemeasurable (by rw [h2]; exact hσ)
  have hinv : (ν.comap (phi ε P)).IsMulLeftInvariant := ⟨fun u => by
    ext s hs
    rw [Measure.map_apply (measurable_const_mul u) hs, hme.comap_apply, hme.comap_apply]
    have hu : Matrix.of (phi ε P u) ∈ GG k r := (phi_range_iff hE hC hP hH _).1 ⟨u, rfl⟩
    have h1 := hleft _ hu
    have hs' : MeasurableSet (phi ε P '' s) := hme.measurableSet_image.2 hs
    conv_rhs => rw [← h1, Measure.map_apply (lmul_cont _).measurable hs']
    congr 1
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨u * w, hw, (lmul_phi hP u w).symm⟩
    · rintro ⟨v, hv, hx⟩
      refine ⟨u⁻¹ * v, by simpa using hv, ?_⟩
      have h2 : Formalism.QuantumDeterminants.lmulM (phi ε P u⁻¹) (Formalism.QuantumDeterminants.lmulM (phi ε P u) x) = x := by
        have h3 : (Matrix.of (phi ε P u⁻¹) : Mx k r) * Matrix.of (phi ε P u) = 1 := by
          have := lmul_phi hP u⁻¹ u
          rw [inv_mul_cancel] at this
          refine Eq.trans this ?_
          show P⁻¹ * (1 : Mx k r) * P = 1
          rw [Matrix.mul_one, Matrix.nonsing_inv_mul P hP]
        show (Matrix.of (phi ε P u⁻¹) : Mx k r) * (Matrix.of (phi ε P u) * Matrix.of x) = Matrix.of x
        rw [← Matrix.mul_assoc, h3, Matrix.one_mul]
      rw [← lmul_phi hP, hx]; exact h2⟩
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts (Formalism.REAL.UJ ε)) := inferInstance
  have e1 := Measure.haarMeasure_unique (ν.comap (phi ε P)) K
  have e2 := Measure.haarMeasure_unique (Formalism.REAL.muG ε) K
  have hb0 : Formalism.REAL.muG ε K ≠ 0 := (Measure.measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
  have hbt : Formalism.REAL.muG ε K ≠ ∞ := K.isCompact.measure_lt_top.ne
  set a := (ν.comap (phi ε P)) K with ha
  set b := Formalism.REAL.muG ε K with hb
  have e3 : ν.comap (phi ε P) = (a / b) • Formalism.REAL.muG ε := by
    rw [e1, e2, smul_smul, ENNReal.div_mul_cancel hb0 hbt]
  have hc0 : a / b ≠ 0 := by
    intro h
    rw [h, zero_smul] at e3
    rw [e3, Measure.map_zero] at h2
    exact h0 h2.symm
  have hct : a / b ≠ ∞ := by
    intro h
    have hz : ∀ i, Formalism.REAL.muG ε (spanningSets (ν.comap (phi ε P)) i) = 0 := by
      intro i
      have h4 := measure_spanningSets_lt_top (ν.comap (phi ε P)) i
      have h5 : (ν.comap (phi ε P)) (spanningSets (ν.comap (phi ε P)) i) =
          ∞ * Formalism.REAL.muG ε (spanningSets (ν.comap (phi ε P)) i) := by
        have := congrArg (fun m : Measure (Formalism.REAL.UJ ε) => m (spanningSets (ν.comap (phi ε P)) i)) e3
        simpa only [h, Measure.smul_apply, smul_eq_mul] using this
      by_contra hne
      rw [h5, ENNReal.top_mul hne] at h4
      exact lt_irrefl _ h4
    have h6 := measure_iUnion_null hz
    rw [iUnion_spanningSets] at h6
    exact hb0 (measure_mono_null (Set.subset_univ _) h6)
  refine ⟨a / b, hc0, hct, ?_⟩
  rw [← Measure.map_smul, ← e3, h2]
  exact hm.aemeasurable

theorem schur_fdeg : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (μG : Measure (Formalism.QuantumDeterminants.Mt k r)), PI.BesselPeriodGGP.IsHaarOn (GG k r) μG → ∃ c : ℝ, 0 < c ∧ ∀ (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH μG R.σ w = c * Formalism.QuantumDeterminants.fdegHC mu) ∧ ∀ v w v' w' : R.H, Integrable (fun x : Formalism.QuantumDeterminants.Mt k r => ⟪w, R.σ (Matrix.of x) v⟫_ℂ * star ⟪w', R.σ (Matrix.of x) v'⟫_ℂ) μG ∧ ∫ x, ⟪w, R.σ (Matrix.of x) v⟫_ℂ * star ⟪w', R.σ (Matrix.of x) v'⟫_ℂ ∂μG = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / ((c * Formalism.QuantumDeterminants.fdegHC mu : ℝ) : ℂ) := by
  intro hy k r ε μG hμ
  have hHC : GlobalTheory.FormalDegree.HarishChandra := hy.2.2.2.2.2.2
  by_cases hQ : ∃ Q, PI.UpqRep.IsCayleyU k r ε Q
  swap
  · refine ⟨1, one_pos, fun mu R hR => absurd ?_ hQ⟩
    obtain ⟨Q, hQ, -⟩ := hR.2
    exact ⟨Q, hQ⟩
  obtain ⟨Q, hQ⟩ := hQ
  have hP : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ.1.1
  have hH : Qᴴ * Formalism.REAL.Jm ε * Q = Formalism.QuantumDeterminants.Hpk k r := hQ.1.2
  obtain ⟨a, ha0, hat, ha⟩ := haar_eq_smul hP hH μG hμ
  obtain ⟨c, hc, hF⟩ := hHC.chamber _ ε
  have hapos : 0 < a.toReal := ENNReal.toReal_pos ha0 hat
  have hme : MeasurableEmbedding (phi ε Q) :=
    (phi_closedEmbedding (ε := ε) Formalism.REAL.isClosedEmbeddingMatrix hP).measurableEmbedding
  refine ⟨c / a.toReal, div_pos hc hapos, fun mu R hR => ?_⟩
  have hDS := (isDS_iff _ _ _).1 ((GlobalTheory.CayleyChoice.cayley_exists_and_any k r).2 ε mu R hR Q hQ)
  obtain ⟨hd, hS⟩ := hF mu hR.1 R.H _ hDS
  have hd' : 0 < c / a.toReal * Formalism.QuantumDeterminants.fdegHC mu := by
    rw [div_mul_eq_mul_div]; exact div_pos hd hapos
  have key : ∀ v w v' w' : R.H, Integrable (fun x : Formalism.QuantumDeterminants.Mt k r => ⟪w, R.σ (Matrix.of x) v⟫_ℂ * star ⟪w', R.σ (Matrix.of x) v'⟫_ℂ) μG ∧ ∫ x, ⟪w, R.σ (Matrix.of x) v⟫_ℂ * star ⟪w', R.σ (Matrix.of x) v'⟫_ℂ ∂μG = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / ((c / a.toReal * Formalism.QuantumDeterminants.fdegHC mu : ℝ) : ℂ) := by
    intro v w v' w'
    obtain ⟨h1, h2⟩ := hS v w v' w'
    rw [ha]
    constructor
    · refine Integrable.smul_measure ?_ hat
      rw [hme.integrable_map_iff]
      exact h1
    · rw [integral_smul_measure, hme.integral_map]
      have h3 : ∫ g, ⟪w, R.σ (Matrix.of (phi ε Q g)) v⟫_ℂ * star ⟪w', R.σ (Matrix.of (phi ε Q g)) v'⟫_ℂ
          ∂(Formalism.REAL.muG ε) = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / ((c * Formalism.QuantumDeterminants.fdegHC mu : ℝ) : ℂ) := h2
      rw [h3, div_mul_eq_mul_div, Complex.ofReal_div, div_div_eq_mul_div, Complex.real_smul]
      ring
  exact ⟨fun w hw => Formalism.FourierDecayAlt.P.DDSmoothness.fdeg_eq hd' key hw, key⟩

end GlobalTheory.BesselDegree
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSubgroupParameterMeasurePreserving
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSubgroupParameterMeasurePreserving
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SParamMeas

open Formalism.QuantumDeterminants

variable {k r : ℕ}

noncomputable def conjInvM (a : B.Mat k r) (x : Mt k r) : Mt k r := a⁻¹ * Matrix.of x * a

theorem meas_mul {α : Type*} [MeasurableSpace α] {f g : α → Mt k r} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => Formalism.FourierDecayAlt.P.B7.mulM (f x) (g x)) :=
  Formalism.FourierDecayAlt.P.B7.continuous_mulM.measurable.comp (hf.prodMk hg)

theorem meas_inv {α : Type*} [MeasurableSpace α] {f : α → Mt k r} (hf : Measurable f) :
    Measurable (fun x => Formalism.FourierDecayAlt.P.B7.invM (f x)) :=
  Formalism.FourierDecayAlt.P.B7.measurable_invM.comp hf

theorem mp_lmul {U : Set (B.Mat k r)} {μ : Measure (Mt k r)} (h : B.IsHaarOn U μ) {a : B.Mat k r} (ha : a ∈ U) :
    MeasurePreserving (lmulM a) μ μ :=
  ⟨meas_mul (f := fun _ => a) measurable_const measurable_id, h.left a ha⟩

theorem mp_rmul {U : Set (B.Mat k r)} {μ : Measure (Mt k r)} (h : B.IsHaarOn U μ) {a : B.Mat k r} (ha : a ∈ U) :
    MeasurePreserving (B.rmulF a) μ μ :=
  ⟨meas_mul (g := fun _ => a) measurable_id measurable_const, h.right a ha⟩

theorem mp_inv {U : Set (B.Mat k r)} {μ : Measure (Mt k r)} (hU : B2.IsClosedSubgroup U) (h : B.IsHaarOn U μ) :
    MeasurePreserving (B2.invM (k := k) (r := r)) μ μ :=
  ⟨Formalism.FourierDecayAlt.P.B7.measurable_invM, Formalism.FourierDecayAlt.P.haar_measure_inversion k r U μ hU h⟩

theorem mp_conj {z : Fin (2 * r + k + 1) → ℂ} {μ : Measure (Mt k r)} (hz : inWb k r z) (hT : 0 < Tz k r z)
    (h : B.IsHaarOn (Nset k r) μ) {a : B.Mat k r} (ha : a ∈ UWset k r z) :
    MeasurePreserving (conjM a) μ μ :=
  ⟨meas_mul (g := fun _ => (a⁻¹ : B.Mat k r)) (meas_mul (f := fun _ => a) measurable_const measurable_id)
    measurable_const, Formalism.FourierDecayAlt.P.b2_conjInvRaw_proof k r z μ hz hT h a ha⟩

theorem mp_conj_inv {z : Fin (2 * r + k + 1) → ℂ} {μ : Measure (Mt k r)} (hz : inWb k r z) (hT : 0 < Tz k r z)
    (h : B.IsHaarOn (Nset k r) μ) {a : B.Mat k r} (ha : a ∈ UWset k r z) :
    MeasurePreserving (conjInvM a) μ μ := by
  have hW := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z
  have := mp_conj hz hT h (hW.inv_mem a ha)
  have e : conjM (a⁻¹) = conjInvM a := by
    funext x
    unfold conjM conjInvM
    rw [Matrix.nonsing_inv_nonsing_inv _ (hW.unit a ha)]
  rwa [e] at this

end GlobalTheory.SParamMeas

open GlobalTheory.SParamMeas in
theorem GlobalTheory.sParam_measurePreserving : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)), 1 ≤ k → Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW → PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN → (∀ h₀ ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ n₀ ∈ Formalism.QuantumDeterminants.Nset k r, MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => (Matrix.of p.1 * h₀ : Mx k r) i j), (fun i j => (h₀⁻¹ * Matrix.of p.2 * h₀ * n₀ : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN) ∧ MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => (h₀ * Matrix.of p.1 : Mx k r) i j), (fun i j => ((Matrix.of p.1)⁻¹ * n₀ * Matrix.of p.1 * Matrix.of p.2 : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN)) ∧ MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => ((Matrix.of p.1)⁻¹ : Mx k r) i j), (fun i j => (Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹ : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN) ∧ MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => (Matrix.of p.1 : Mx k r) i j), (fun i j => (Matrix.of p.1 * Matrix.of p.2 * (Matrix.of p.1)⁻¹ : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN) ∧ MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => (Matrix.of p.1 : Mx k r) i j), (fun i j => ((Matrix.of p.1)⁻¹ * Matrix.of p.2 * Matrix.of p.1 : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN) ∧ MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => ((Matrix.of p.1)⁻¹ : Mx k r) i j), (fun i j => ((Matrix.of p.2)⁻¹ : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN) ∧ ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r := by
  intro k r z μW μN hk hz hT hW0 hN0
  have hW : B.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW := ((GlobalTheory.HaarNotions.isHaarOn_iff_groups k r μW).2.2 z hz hT hk).1 hW0
  have hN : B.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN := (GlobalTheory.HaarNotions.isHaarOn_iff_groups k r μN).2.1.1 hN0
  have := hW0.1
  have := hN0.1
  have cW := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z
  have cN := Formalism.FourierDecayAlt.P.unipotent_radical_closed k r
  have aW := Formalism.FourierDecayAlt.P.B7.ae_mem hW
  have aN := Formalism.FourierDecayAlt.P.B7.ae_mem hN
  have m1 : Measurable (Prod.fst : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r → _) := measurable_fst
  have m2 : Measurable (Prod.snd : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r → _) := measurable_snd
  refine ⟨fun h₀ hh n₀ hn => ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact (mp_rmul hW hh).prod ((mp_rmul hN hn).comp (mp_conj_inv hz hT hN hh))
  · have m3 : Measurable (fun _ : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of.symm n₀ : Formalism.QuantumDeterminants.Mt k r)) :=
      measurable_const
    refine (mp_lmul hW hh).skew_product
      (g := fun (a x : Formalism.QuantumDeterminants.Mt k r) => Formalism.QuantumDeterminants.lmulM ((Matrix.of a)⁻¹ * n₀ * Matrix.of a) x)
      (meas_mul (meas_mul (meas_mul (meas_inv m1) m3) m1) m2) ?_
    filter_upwards [aW] with a ha
    refine hN.left _ ?_
    have := (Formalism.QuantumDeterminants.unitary_weyl_normal_holds k r z hz _ (cW.inv_mem _ ha) n₀ hn).1
    rwa [Matrix.nonsing_inv_nonsing_inv _ (cW.unit _ ha)] at this
  · refine (mp_inv cW hW).skew_product
      (g := fun (a x : Formalism.QuantumDeterminants.Mt k r) => Formalism.QuantumDeterminants.conjM (Matrix.of a) (B2.invM x))
      (meas_mul (meas_mul m1 (meas_inv m2)) (meas_inv m1)) ?_
    filter_upwards [aW] with a ha
    exact ((mp_conj hz hT hN ha).comp (mp_inv cN hN)).map_eq
  · refine (MeasurePreserving.id μW).skew_product
      (g := fun (a x : Formalism.QuantumDeterminants.Mt k r) => Formalism.QuantumDeterminants.conjM (Matrix.of a) x)
      (meas_mul (meas_mul m1 m2) (meas_inv m1)) ?_
    filter_upwards [aW] with a ha
    exact (mp_conj hz hT hN ha).map_eq
  · refine (MeasurePreserving.id μW).skew_product
      (g := fun (a x : Formalism.QuantumDeterminants.Mt k r) =>
        conjInvM (Matrix.of a) x)
      (meas_mul (meas_mul (meas_inv m1) m2) m1) ?_
    filter_upwards [aW] with a ha
    exact (mp_conj_inv hz hT hN ha).map_eq
  · exact (mp_inv cW hW).prod (mp_inv cN hN)
  · exact (Measure.quasiMeasurePreserving_fst.ae aW).and (Measure.quasiMeasurePreserving_snd.ae aN)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSubgroupParameterMeasurePreservingStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselSubgroup_parameter_measurePreserving : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)), 1 ≤ k → Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW → PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN → (∀ h₀ ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ n₀ ∈ Formalism.QuantumDeterminants.Nset k r, MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => (Matrix.of p.1 * h₀ : Mx k r) i j), (fun i j => (h₀⁻¹ * Matrix.of p.2 * h₀ * n₀ : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN) ∧ MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => (h₀ * Matrix.of p.1 : Mx k r) i j), (fun i j => ((Matrix.of p.1)⁻¹ * n₀ * Matrix.of p.1 * Matrix.of p.2 : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN)) ∧ MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => ((Matrix.of p.1)⁻¹ : Mx k r) i j), (fun i j => (Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹ : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN) ∧ MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => (Matrix.of p.1 : Mx k r) i j), (fun i j => (Matrix.of p.1 * Matrix.of p.2 * (Matrix.of p.1)⁻¹ : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN) ∧ MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => (Matrix.of p.1 : Mx k r) i j), (fun i j => ((Matrix.of p.1)⁻¹ * Matrix.of p.2 * Matrix.of p.1 : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN) ∧ MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => ((Matrix.of p.1)⁻¹ : Mx k r) i j), (fun i j => ((Matrix.of p.2)⁻¹ : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN) ∧ ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r := by
  first | exact @GlobalTheory.sParam_measurePreserving | exact GlobalTheory.sParam_measurePreserving | (intros; apply GlobalTheory.sParam_measurePreserving <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGroupMatGroupUnimodular
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGroupMatGroupUnimodular
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem unitaryGroup_matGroup_unimodular : ∀ (k r : ℕ), PI.IsMatGroup (GG k r) ∧
    ∀ μG : Measure (Formalism.QuantumDeterminants.Mt k r), PI.BesselPeriodGGP.IsHaarOn (GG k r) μG →
      PI.IsHaarOnM (GG k r) μG ∧ PI.IsRightInvM (GG k r) μG := by
  intro k r
  have hG : PI.IsMatGroup (GG k r) := PI.QuotSetU.UnitaryGroupMassFormula.unitary_hermitian_group k r
  refine ⟨hG, fun μG hμ => ?_⟩
  have hμ' : PI.IsHaarOnM (GG k r) μG := hμ
  refine ⟨hμ', ?_⟩
  obtain ⟨μ, h1, h2, -⟩ := GlobalTheory.SgInf.exists_unimod_GG (k := k) (r := r)
  have h1' : PI.IsHaarOnM (GG k r) μ := h1
  obtain ⟨c, -, -, hc⟩ := (GlobalTheory.T.matGroupHaar_unique_finite_compact_openPos _ (GG k r) μ hG h1').1 μG hμ'
  intro s hs
  have h3 : μ.map (PI.rmulQ s) = μ := h2 s hs
  rw [hc, Measure.map_smul, h3]
  apply Measurable.aemeasurable
  apply Continuous.measurable
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [PI.rmulQ, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGroupMatGroupUnimodularStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMatGroup_GG_and_haar_right_invariant : ∀ (k r : ℕ), PI.IsMatGroup (GG k r) ∧ ∀ μG : Measure (Formalism.QuantumDeterminants.Mt k r), PI.BesselPeriodGGP.IsHaarOn (GG k r) μG → PI.IsHaarOnM (GG k r) μG ∧ PI.IsRightInvM (GG k r) μG := by
  first | exact @GlobalTheory.unitaryGroup_matGroup_unimodular | exact GlobalTheory.unitaryGroup_matGroup_unimodular | (intros; apply GlobalTheory.unitaryGroup_matGroup_unimodular <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsFRepExteriorPowerStandardRep
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsFRepExteriorPowerStandardRep
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.WedgeFRep

theorem entry_le_hs {k r : ℕ} (g : Mx k r) (i j : Fin (2 * r + k + 1)) : ‖g i j‖ ≤ B.gN g := by
  unfold B.gN
  apply Real.le_sqrt_of_sq_le
  rw [← Complex.normSq_eq_norm_sq]
  calc Complex.normSq (g i j) ≤ ∑ j', Complex.normSq (g i j') :=
        Finset.single_le_sum (f := fun j' => Complex.normSq (g i j'))
          (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
    _ ≤ _ := Finset.single_le_sum (f := fun i' => ∑ j', Complex.normSq (g i' j'))
          (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)

theorem isFRep_cmp (k r l : ℕ) :
    IsFRep (k := k) (r := r) (cmp l) (cmp l (Formalism.QuantumDeterminants.Hpk k r)) l := by
  have hm : ∀ g h : Mx k r, cmp l (g * h) = cmp l g * cmp l h := fun g h => (GlobalTheory.T.compoundMatrix_cauchyBinet_properties _ l g h).1
  have hc : ∀ g : Mx k r, cmp l gᴴ = (cmp l g)ᴴ := fun g => (GlobalTheory.T.compoundMatrix_cauchyBinet_properties _ l g g).2.1
  have h1 : cmp l (1 : Mx k r) = 1 := (GlobalTheory.T.compoundMatrix_cauchyBinet_properties _ l 1 1).2.2.1
  refine ⟨?_, ?_, h1, fun g _ h _ => hm g h, ?_, ?_, ⟨(l.factorial : ℝ), ?_⟩, ?_⟩
  · rw [← hc, PI.StabPairsW.hpk_conjTranspose]
  · rw [← hm, PI.StabPairsW.hpk_mul_self, h1]
  · intro g hg
    have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
    rw [← hc, ← hm, ← hm, hg']
  · intro I J
    apply Continuous.continuousOn
    unfold BranchingSupport.cmp
    exact (continuous_id.matrix_submatrix _ _).matrix_det
  · intro g _ I J
    have := Matrix.det_le (A := g.submatrix (I.1.orderEmbOfFin I.2) (J.1.orderEmbOfFin J.2))
      (abv := IsAbsoluteValue.toAbsoluteValue (norm : ℂ → ℝ)) (x := B.gN g) (fun i j => entry_le_hs g _ _)
    rw [Fintype.card_fin, nsmul_eq_mul] at this
    exact this
  · intro g _ hu
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hu ⊢
    rw [← hc, ← hm, hu, h1]

end GlobalTheory.WedgeFRep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsFRepExteriorPowerStandardRepStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFRep_exteriorPower_standardRep : ∀ (k r : ℕ) (l : ℕ), IsFRep (k := k) (r := r) (cmp l) (cmp l (Formalism.QuantumDeterminants.Hpk k r)) l := by
  first | exact @GlobalTheory.WedgeFRep.isFRep_cmp | exact GlobalTheory.WedgeFRep.isFRep_cmp | (intros; apply GlobalTheory.WedgeFRep.isFRep_cmp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FixesWedgeAndForm
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.FlagFix

open Formalism.QuantumDeterminants

theorem wedge_eq_of_mul {n l : ℕ} (f f' : Fin l → Fin n → ℂ) (U : Matrix (Fin l) (Fin l) ℂ)
    (hU0 : ∀ c a, a < c → U c a = 0) (hU1 : ∀ c, U c c = 1)
    (h : ∀ i a, f' a i = ∑ c, f c i * U c a) : wedge f' = wedge f := by
  have dU : U.det = 1 := by
    have ht : U.IsUpperTriangular := fun i j hij => hU0 i j hij
    rw [det_of_isUpperTriangular ht]
    exact Finset.prod_eq_one (fun i _ => hU1 i)
  funext I
  have e : (Matrix.of fun a b : Fin l => f' b (I.1.orderEmbOfFin I.2 a)) =
      (Matrix.of fun a b : Fin l => f b (I.1.orderEmbOfFin I.2 a)) * U := by
    ext a b
    simp only [Matrix.of_apply, Matrix.mul_apply, h]
  simp only [wedge]
  rw [e, det_mul, dU, mul_one]

theorem flat_eq (k r : ℕ) (f : Fin (2 * r + k + 1) → ℂ) : flat k r f = star f ᵥ* Hpk k r := by
  funext c
  simp only [flat, herm]
  rw [dotProduct_mulVec, dotProduct_single, mul_one]

theorem dual_fix (k r : ℕ) (f : Fin (2 * r + k + 1) → ℂ)
    (s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hs : sᴴ * Hpk k r * s = Hpk k r)
    (hf : s *ᵥ f = f) : dualM s *ᵥ flat k r f = flat k r f := by
  have h2 : Hpk k r * Hpk k r = 1 := (hermitian_pos_facts_hold k r).2.1
  have hl : (Hpk k r * sᴴ * Hpk k r) * s = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc sᴴ, hs, h2]
  rw [flat_eq, dualM, mulVec_transpose, Matrix.inv_eq_left_inv hl, vecMul_vecMul,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul, ← vecMul_vecMul, ← star_mulVec, hf]

theorem fixes_wedge_and_form : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z →
    ∀ s ∈ Formalism.QuantumDeterminants.Sset k r z,
      cmp (r + 1) s *ᵥ (wedge (Formalism.QuantumDeterminants.fvec k r z)) = (wedge (Formalism.QuantumDeterminants.fvec k r z)) ∧
      dualM s *ᵥ (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) = (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) := by
  intro k r z hz s hs
  obtain ⟨U, hU0, hU1, hF⟩ := S_F hz hs
  have key : ∀ i a, (s *ᵥ fvec k r z a) i = ∑ c, fvec k r z c i * U c a := by
    intro i a
    have := congrFun (congrFun hF i) a
    simpa [Matrix.mul_apply, Fm, mulVec, dotProduct] using this
  refine ⟨?_, dual_fix k r _ s (Sset_UH hs) ?_⟩
  · rw [(GlobalTheory.T.compoundMatrix_cauchyBinet_properties _ (r + 1) s s).2.2.2]
    exact wedge_eq_of_mul _ _ U hU0 hU1 key
  · funext i
    rw [key, Finset.sum_eq_single 0, hU1, mul_one]
    · intro c _ hc
      rw [hU0 c 0 (Fin.pos_of_ne_zero hc), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h

end GlobalTheory.FlagFix
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsFiniteFlatTorsionOfIsGt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

namespace ExtensionTorsion

open KernelNoTorsion

variable {S : Scheme.{0}} {T G B : Over S} [GrpObj T] [GrpObj G] [GrpObj B]

noncomputable def torsionHom (q : G ⟶ B) [IsMonHom q] (N : ℕ) : torsion G N ⟶ torsion B N :=
  torsionLift (torsion.ι G N ≫ q) (by rw [← MonObj.pow_comp, torsionι_pow, MonObj.one_comp])

theorem torsionHom_ι (q : G ⟶ B) [IsMonHom q] (N : ℕ) :
    torsionHom q N ≫ torsion.ι B N = torsion.ι G N ≫ q :=
  torsionLift_ι _ _

theorem exists_isPullback_mulN [IsCommMonObj G] (i : T ⟶ G) (q : G ⟶ B) [IsMonHom i] [IsMonHom q]
    (hk : IsPullback i (toUnit _) q (η : 𝟙_ _ ⟶ B)) (N : ℕ)
    {P Q : Over S} {a : P ⟶ G} {b : P ⟶ torsion B N} (hP : IsPullback a b q (torsion.ι B N))
    {s : Q ⟶ P} {r : Q ⟶ torsion G N} (hQ : IsPullback s r b (torsionHom q N)) :
    ∃ (c : P ⟶ T) (t : Q ⟶ T), IsPullback s t c (mulN T N) := by
  have inj : ∀ {W : Over S} {x y : W ⟶ T}, x ≫ i = y ≫ i → x = y := fun h =>
    hk.hom_ext h (toUnit_unique _ _)
  have ex : ∀ {W : Over S} (x : W ⟶ G), x ≫ q = 1 → ∃ y : W ⟶ T, y ≫ i = x := fun x h =>
    ⟨hk.lift x (toUnit _) (by rw [h, Hom.one_def]), hk.lift_fst _ _ _⟩
  have hiq : i ≫ q = 1 := by rw [hk.w, Hom.one_def]
  have hpow : ∀ {W : Over S} (x : W ⟶ torsion G N), (x ≫ torsion.ι G N) ^ N = 1 := fun x => by
    rw [← MonObj.comp_pow, torsionι_pow, MonObj.comp_one]
  obtain ⟨c, hc⟩ := ex (a ^ N) (by
    rw [MonObj.pow_comp, hP.w, ← MonObj.comp_pow, torsionι_pow, MonObj.comp_one])
  have hsr : s ≫ a ≫ q = r ≫ torsion.ι G N ≫ q := by
    rw [hP.w, ← Category.assoc, hQ.w, Category.assoc, torsionHom_ι]
  obtain ⟨t, ht⟩ := ex ((s ≫ a) / (r ≫ torsion.ι G N)) (by
    rw [GrpObj.div_comp, Category.assoc, Category.assoc, hsr, div_self'])
  refine ⟨c, t, ⟨?_⟩, ⟨PullbackCone.isLimitAux' _ fun W => ?_⟩⟩
  · apply inj
    rw [comp_mulN, MonObj.pow_comp, ht, div_pow, hpow, div_one, Category.assoc, hc,
      MonObj.comp_pow]
  · have hW : W.fst ≫ c = W.snd ^ N := by rw [W.condition, comp_mulN]
    have hg : ((W.fst ≫ a) / (W.snd ≫ i)) ^ N = 1 := by
      rw [div_pow, ← MonObj.pow_comp _ _ i, ← hW, Category.assoc, hc, MonObj.comp_pow, div_self']
    have hl : W.fst ≫ b = torsionLift _ hg ≫ torsionHom q N := by
      apply torsion_hom_ext
      rw [Category.assoc, Category.assoc, torsionHom_ι, ← Category.assoc (torsionLift _ hg),
        torsionLift_ι, GrpObj.div_comp, Category.assoc, Category.assoc, hiq, MonObj.comp_one,
        div_one, hP.w]
    refine ⟨hQ.lift W.fst _ hl, hQ.lift_fst _ _ _, ?_, ?_⟩
    · apply inj
      change (_ ≫ t) ≫ i = _
      rw [Category.assoc, ht, GrpObj.comp_div, ← Category.assoc, ← Category.assoc, hQ.lift_fst,
        hQ.lift_snd, torsionLift_ι, div_div_cancel]
    · intro (m : W.pt ⟶ Q) (h1 : m ≫ s = W.fst) (h2 : m ≫ t = W.snd)
      change m = _
      refine hQ.hom_ext (by rw [hQ.lift_fst, h1]) ?_
      apply torsion_hom_ext
      rw [hQ.lift_snd, torsionLift_ι, ← h1, ← h2, Category.assoc, Category.assoc, Category.assoc,
        ht, GrpObj.comp_div, div_div_cancel]

theorem torsionHom_of_mulN (Pr : MorphismProperty Scheme.{0}) [Pr.IsStableUnderBaseChange]
    [Pr.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)]
    [IsCommMonObj G] (i : T ⟶ G) (q : G ⟶ B) [IsMonHom i] [IsMonHom q]
    [Surjective q.left] [Flat q.left] [QuasiCompact q.left]
    (hk : IsPullback i (toUnit _) q (η : 𝟙_ _ ⟶ B)) (N : ℕ) (h : Pr (mulN T N).left) :
    Pr (torsionHom q N).left := by
  have hP := IsPullback.of_hasPullback q (torsion.ι B N)
  have hQ := IsPullback.of_hasPullback (pullback.snd q (torsion.ι B N)) (torsionHom q N)
  obtain ⟨c, t, H⟩ := exists_isPullback_mulN i q hk N hP hQ
  have hP' := hP.map (Over.forget S)
  refine MorphismProperty.of_isPullback_of_descendsAlong (P := Pr)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (hQ.map (Over.forget S)) ⟨⟨?_, ?_⟩, ?_⟩ ?_
  · exact MorphismProperty.of_isPullback (P := @Surjective) hP' ‹_›
  · exact MorphismProperty.of_isPullback (P := @Flat) hP' ‹_›
  · exact MorphismProperty.of_isPullback (P := @QuasiCompact) hP' ‹_›
  · exact MorphismProperty.of_isPullback (P := Pr) (H.map (Over.forget S)).flip h

end ExtensionTorsion

open ExtensionTorsion in
theorem isFinite_flat_torsion_of_isGt :
    ∀ (S : Scheme.{0}) (E : SplitExt S) (G : Over S) [GrpObj G] [IsCommMonObj G], E.IsGt G → ∀ N : ℕ, 1 ≤ N → IsFinite (torsion E.B N).hom → Flat (torsion E.B N).hom → IsFinite (torsion G N).hom ∧ Flat (torsion G N).hom := by
  rintro S E G _ _ ⟨D⟩ N hN h1 h2
  have := D.q_hom
  have := D.i_hom
  have := D.q_flat
  have := D.q_surjective
  have := D.q_affine
  have := E.free
  have := E.finite
  have hN' : N ≠ 0 := by omega
  have hf : IsFinite (mulN (splitTorus S E.X) N).left := Diag.isFinite_mulN S E.X hN'
  have hl : Flat (mulN (splitTorus S E.X) N).left := Diag.flat_mulN S E.X hN'
  have := flat_descendsAlong_fpqc
  have := isAffineHom_descendsAlong_fpqc.{0}
  have a1 : Flat (torsionHom D.q N).left :=
    torsionHom_of_mulN @Flat D.i D.q D.isKernel N hl
  have a2 : IsAffineHom (torsionHom D.q N).left :=
    torsionHom_of_mulN @IsAffineHom D.i D.q D.isKernel N inferInstance
  have a3 : UniversallyClosed (torsionHom D.q N).left :=
    torsionHom_of_mulN @UniversallyClosed D.i D.q D.isKernel N inferInstance
  have a4 : LocallyOfFiniteType (torsionHom D.q N).left :=
    torsionHom_of_mulN @LocallyOfFiniteType D.i D.q D.isKernel N inferInstance
  have a5 : IsFinite (torsionHom D.q N).left :=
    (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr
      ⟨IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨a3, a2⟩, a4⟩
  rw [← Over.w (torsionHom D.q N)]
  exact ⟨inferInstance, inferInstance⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothMapsClosure
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothMapsClosure
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SmMapAct

open PI.UpqRep

variable {k r : ℕ}

def SemiBd (R : Rep k r) (f : R.H → ℝ) : Prop :=
  ∃ (C : ℝ) (Ws : List (List (Mx k r))), 0 ≤ C ∧ (∀ w ∈ Ws, ∀ X ∈ w, InLieHpk k r X) ∧
    ∀ v ∈ R.sm, f v ≤ C * (Ws.map fun w => ‖dsigW (k := k) (r := r) R.σ w v‖).sum

theorem sum_norm_nonneg (R : Rep k r) (Ws : List (List (Mx k r))) (v : R.H) :
    0 ≤ (Ws.map fun w => ‖dsigW (k := k) (r := r) R.σ w v‖).sum := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hx
  exact norm_nonneg _

theorem semiBd_of_cw {Wp : Type} [NormedAddCommGroup Wp] (R : Rep k r) {B : R.H → Wp}
    (h : PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ B) : SemiBd R (fun v => ‖B v‖) := by
  obtain ⟨C, Ws, h1, h2⟩ := h
  exact ⟨max C 0, Ws, le_max_right _ _, h1, fun v hv => (h2 v hv).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (sum_norm_nonneg R Ws v))⟩

theorem cw_of_semiBd {Wp : Type} [NormedAddCommGroup Wp] (R : Rep k r) {B : R.H → Wp} {f : R.H → ℝ}
    (h : SemiBd R f) (hle : ∀ v ∈ R.sm, ‖B v‖ ≤ f v) :
    PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ B := by
  obtain ⟨C, Ws, _, h1, h2⟩ := h
  exact ⟨C, Ws, h1, fun v hv => (hle v hv).trans (h2 v hv)⟩

theorem SemiBd.add {R : Rep k r} {f g : R.H → ℝ} (hf : SemiBd R f) (hg : SemiBd R g) :
    SemiBd R (fun v => f v + g v) := by
  obtain ⟨C, Ws, h0, h1, h2⟩ := hf
  obtain ⟨C', Ws', h0', h1', h2'⟩ := hg
  refine ⟨C + C', Ws ++ Ws', add_nonneg h0 h0', ?_, fun v hv => ?_⟩
  · intro w hw
    rcases List.mem_append.mp hw with h | h
    · exact h1 w h
    · exact h1' w h
  · have a := h2 v hv
    have b := h2' v hv
    have c := sum_norm_nonneg R Ws v
    have d := sum_norm_nonneg R Ws' v
    rw [List.map_append, List.sum_append]
    nlinarith [mul_nonneg h0 d, mul_nonneg h0' c]

theorem SemiBd.mul {R : Rep k r} {f : R.H → ℝ} (hf : SemiBd R f) {a : ℝ} (ha : 0 ≤ a) :
    SemiBd R (fun v => a * f v) := by
  obtain ⟨C, Ws, h0, h1, h2⟩ := hf
  refine ⟨a * C, Ws, mul_nonneg ha h0, h1, fun v hv => ?_⟩
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (h2 v hv) ha

theorem semiBd_sum {R R' : Rep k r} {T : R.H → R'.H} (hT : SmMap R R' T) (Ws : List (List (Mx k r)))
    (hWs : ∀ w ∈ Ws, ∀ X ∈ w, InLieHpk k r X) :
    SemiBd R (fun v => (Ws.map fun w => ‖dsigW (k := k) (r := r) R'.σ w (T v)‖).sum) := by
  induction Ws with
  | nil => exact ⟨0, [], le_rfl, by simp, fun v _ => by simp⟩
  | cons w Ws ih =>
    have h1 := semiBd_of_cw R (hT.cont w (hWs w List.mem_cons_self))
    have h2 := ih (fun w' hw' => hWs w' (List.mem_cons_of_mem _ hw'))
    simpa only [List.map_cons, List.sum_cons] using h1.add h2

theorem cw_comp {Wp : Type} [NormedAddCommGroup Wp] {R R' : Rep k r} {T : R.H → R'.H} {Bm : R'.H → Wp}
    (hT : SmMap R R' T) (hB : PI.BesselMapUniq.IsCWCont (k := k) (r := r) R'.σ Bm) :
    PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ (fun v => Bm (T v)) := by
  obtain ⟨C, Ws, h0, h1, h2⟩ := semiBd_of_cw R' hB
  exact cw_of_semiBd R ((semiBd_sum hT Ws h1).mul h0) (fun v hv => h2 _ (hT.mem v hv))

theorem smMap_comp {R R' R'' : Rep k r} {T : R.H → R'.H} {T' : R'.H → R''.H}
    (hT : SmMap R R' T) (hT' : SmMap R' R'' T') : SmMap R R'' (fun v => T' (T v)) := by
  refine ⟨fun v hv => hT'.mem _ (hT.mem v hv), ?_, ?_, ?_⟩
  · intro v hv w hw
    rw [hT.add v hv w hw, hT'.add _ (hT.mem v hv) _ (hT.mem w hw)]
  · intro a v hv
    rw [hT.smul a v hv, hT'.smul a _ (hT.mem v hv)]
  · intro W hW
    exact cw_comp (Bm := fun v => dsigW (k := k) (r := r) R''.σ W (T' v)) hT (hT'.cont W hW)

section DS

variable {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {R : Rep k r}

theorem dsigW_mem (hK : PI.KFinSmooth) (hR : R.IsDS ε mu) (W : List (Mx k r))
    (hW : ∀ X ∈ W, InLieHpk k r X) {v : R.H} (hv : v ∈ R.sm) :
    dsigW (k := k) (r := r) R.σ W v ∈ R.sm := by
  induction W with
  | nil => exact hv
  | cons X W ih =>
    exact ((GlobalTheory.T.derivedAction_discreteSeries_properties hK k r ε mu R hR X (hW X List.mem_cons_self)).1 _
      (ih (fun Y hY => hW Y (List.mem_cons_of_mem _ hY)))).1

theorem dsig_lin (hK : PI.KFinSmooth) (hR : R.IsDS ε mu) {X : Mx k r} (hX : InLieHpk k r X) (a : ℂ)
    {v w : R.H} (hv : v ∈ R.sm) (hw : w ∈ R.sm) :
    dsig (k := k) (r := r) R.σ X (a • v + w) =
      a • dsig (k := k) (r := r) R.σ X v + dsig (k := k) (r := r) R.σ X w := by
  have h := (GlobalTheory.T.derivedAction_discreteSeries_properties hK k r ε mu R hR X hX).1
  have h1 := ((h v hv).2.const_smul a).add (h w hw).2
  refine HasDerivAt.deriv ?_
  convert h1 using 1
  funext t
  simp only [Pi.add_apply, Pi.smul_apply, map_add, map_smul]

theorem dsigW_lin (hK : PI.KFinSmooth) (hR : R.IsDS ε mu) (W : List (Mx k r))
    (hW : ∀ X ∈ W, InLieHpk k r X) (a : ℂ) {v w : R.H} (hv : v ∈ R.sm) (hw : w ∈ R.sm) :
    dsigW (k := k) (r := r) R.σ W (a • v + w) =
      a • dsigW (k := k) (r := r) R.σ W v + dsigW (k := k) (r := r) R.σ W w := by
  induction W with
  | nil => rfl
  | cons X W ih =>
    have hW' : ∀ Y ∈ W, InLieHpk k r Y := fun Y hY => hW Y (List.mem_cons_of_mem _ hY)
    show dsig R.σ X (dsigW R.σ W (a • v + w)) = _
    rw [ih hW']
    exact dsig_lin hK hR (hW X List.mem_cons_self) a (dsigW_mem hK hR W hW' hv) (dsigW_mem hK hR W hW' hw)

theorem inLie_conj {g X : Mx k r} (hg : g ∈ GG k r) (hX : InLieHpk k r X) : InLieHpk k r (g⁻¹ * X * g) := by
  obtain ⟨hu, hi, -⟩ := PI.UnitaryGroupMassFormula.CapelliEig.unitary_Hecke_group k r g hg
  have hdet : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det _).mp hu
  have h1 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hX' : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  have e1 : Hpk k r * g⁻¹ = gᴴ * Hpk k r := by
    calc Hpk k r * g⁻¹ = gᴴ * Hpk k r * g * g⁻¹ := by rw [hg']
      _ = gᴴ * Hpk k r := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  have e2 : (g⁻¹)ᴴ * Hpk k r = Hpk k r * g := by
    calc (g⁻¹)ᴴ * Hpk k r = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) := by rw [hg']
      _ = (g * g⁻¹)ᴴ * Hpk k r * g := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Hpk k r * g := by rw [h1, Matrix.conjTranspose_one, Matrix.one_mul]
  show (g⁻¹ * X * g)ᴴ * Hpk k r + Hpk k r * (g⁻¹ * X * g) = 0
  calc (g⁻¹ * X * g)ᴴ * Hpk k r + Hpk k r * (g⁻¹ * X * g)
      = gᴴ * Xᴴ * ((g⁻¹)ᴴ * Hpk k r) + (Hpk k r * g⁻¹) * X * g := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = gᴴ * (Xᴴ * Hpk k r + Hpk k r * X) * g := by
        rw [e1, e2]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hX', Matrix.mul_zero, Matrix.zero_mul]

theorem norm_sigma (hR : R.IsDS ε mu) {g : Mx k r} (hg : g ∈ GG k r) (v : R.H) : ‖R.σ g v‖ = ‖v‖ := by
  obtain ⟨P₀, ⟨⟨hunit, hcay⟩, _⟩, hds⟩ := hR.2
  have hdet : IsUnit P₀.det := (Matrix.isUnit_iff_isUnit_det _).mp hunit
  have hPQ : P₀ * P₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hQP : P₀⁻¹ * P₀ = 1 := Matrix.nonsing_inv_mul _ hdet
  have hH : Formalism.QuantumDeterminants.Hpk k r = P₀ᴴ * Formalism.REAL.Jm ε * P₀ := hcay.symm
  have hx' : Formalism.REAL.inUJ ε (P₀ * g * P₀⁻¹) := Formalism.QuantumDeterminants.ioh_inUJ ε _ P₀ P₀⁻¹ g hPQ hH hg
  have hm := hds.2.2.1.2.1 (P₀ * g * P₀⁻¹) hx' v
  have e2 : P₀⁻¹ * (P₀ * g * P₀⁻¹) * P₀ = g := by
    calc P₀⁻¹ * (P₀ * g * P₀⁻¹) * P₀ = (P₀⁻¹ * P₀) * g * (P₀⁻¹ * P₀) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [hQP, Matrix.one_mul, Matrix.mul_one]
  simp only [e2] at hm
  exact hm

theorem dsigW_sigma (hK : PI.KFinSmooth) (hR : R.IsDS ε mu) {g : Mx k r} (hg : g ∈ GG k r) (W : List (Mx k r))
    (hW : ∀ X ∈ W, InLieHpk k r X) {v : R.H} (hv : v ∈ R.sm) :
    dsigW (k := k) (r := r) R.σ W (R.σ g v) =
      R.σ g (dsigW (k := k) (r := r) R.σ (W.map fun X => g⁻¹ * X * g) v) := by
  induction W with
  | nil => rfl
  | cons X W ih =>
    have hW' : ∀ Y ∈ W, InLieHpk k r Y := fun Y hY => hW Y (List.mem_cons_of_mem _ hY)
    have hW'' : ∀ Y ∈ W.map (fun X => g⁻¹ * X * g), InLieHpk k r Y := by
      intro Y hY
      obtain ⟨Z, hZ, rfl⟩ := List.mem_map.mp hY
      exact inLie_conj hg (hW' Z hZ)
    have hdet : IsUnit g.det :=
      (Matrix.isUnit_iff_isUnit_det _).mp (PI.UnitaryGroupMassFormula.CapelliEig.unitary_Hecke_group k r g hg).1
    have h1 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
    have e : g * (g⁻¹ * X * g) * g⁻¹ = X := by
      calc g * (g⁻¹ * X * g) * g⁻¹ = (g * g⁻¹) * X * (g * g⁻¹) := by simp only [Matrix.mul_assoc]
        _ = X := by rw [h1, Matrix.one_mul, Matrix.mul_one]
    have h := (GlobalTheory.T.derivedAction_discreteSeries_properties hK k r ε mu R hR _ (inLie_conj hg (hW X List.mem_cons_self))).2.1 _
      (dsigW_mem hK hR _ hW'' hv) g hg
    rw [e] at h
    show dsig R.σ X (dsigW R.σ W (R.σ g v)) = R.σ g (dsig R.σ (g⁻¹ * X * g) _)
    rw [ih hW', h]

theorem smMap_sigma (hK : PI.KFinSmooth) (hR : R.IsDS ε mu) {g : Mx k r} (hg : g ∈ GG k r) :
    SmMap R R (fun v => R.σ g v) := by
  refine ⟨?_, fun v _ w _ => map_add (R.σ g) v w, fun a v _ => map_smul (R.σ g) a v, ?_⟩
  · intro v hv
    exact PI.UnitaryGroupMassFormula.CapelliEig.smooth_right_action k r ε mu R.H R.σ hR.2 v hv g hg
  · intro W hW
    refine ⟨1, [W.map fun X => g⁻¹ * X * g], ?_, fun v hv => ?_⟩
    · intro w hw Y hY
      rw [List.mem_singleton.mp hw] at hY
      obtain ⟨Z, hZ, rfl⟩ := List.mem_map.mp hY
      exact inLie_conj hg (hW Z hZ)
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul]
      rw [dsigW_sigma hK hR hg W hW hv, norm_sigma hR hg]

theorem smMap_lin (hK : PI.KFinSmooth) {R₀ : Rep k r} (hR : R.IsDS ε mu) {T T' : R₀.H → R.H} (a : ℂ)
    (hT : SmMap R₀ R T) (hT' : SmMap R₀ R T') : SmMap R₀ R (fun v => a • T v + T' v) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv
    exact Formalism.FourierDecayAlt.P.DDSmoothness.smooth_add
      (Formalism.FourierDecayAlt.P.DDSmoothness.smooth_smul a (hT.mem v hv)) (hT'.mem v hv)
  · intro v hv w hw
    rw [hT.add v hv w hw, hT'.add v hv w hw, smul_add]
    abel
  · intro b v hv
    rw [hT.smul b v hv, hT'.smul b v hv, smul_add, smul_comm]
  · intro W hW
    refine cw_of_semiBd R₀ (((semiBd_of_cw R₀ (hT.cont W hW)).mul (norm_nonneg a)).add
      (semiBd_of_cw R₀ (hT'.cont W hW))) (fun v hv => ?_)
    rw [dsigW_lin hK hR W hW a (hT.mem v hv) (hT'.mem v hv)]
    exact (norm_add_le _ _).trans (by rw [norm_smul])

end DS

theorem smMap_act : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (mu' mu'' : Fin (2 * r + k + 1) → ℝ) (R R' R'' : Rep k r), R.IsDS ε mu → R'.IsDS ε mu' → R''.IsDS ε mu'' → (∀ g ∈ GG k r, SmMap R R (fun v => R.σ g v)) ∧ (∀ (T : R.H → R'.H) (T' : R'.H → R''.H), SmMap R R' T → SmMap R' R'' T' → SmMap R R'' (fun v => T' (T v))) ∧ (∀ (T T' : R.H → R'.H) (a : ℂ), SmMap R R' T → SmMap R R' T' → SmMap R R' (fun v => a • T v + T' v)) ∧ ∀ (Wp : Type) [NormedAddCommGroup Wp] (T : R.H → R'.H) (Bm : R'.H → Wp), SmMap R R' T → PI.BesselMapUniq.IsCWCont (k := k) (r := r) R'.σ Bm → PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ (fun v => Bm (T v)) := by
  intro hK k r ε mu mu' mu'' R R' R'' hR hR' _
  exact ⟨fun g hg => smMap_sigma hK hR hg, fun T T' hT hT' => smMap_comp hT hT',
    fun T T' a hT hT' => smMap_lin hK hR' a hT hT', fun Wp _ T Bm hT hB => cw_comp hT hB⟩

end GlobalTheory.SmMapAct
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothMapsClosureStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_maps_closure : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (mu' mu'' : Fin (2 * r + k + 1) → ℝ) (R R' R'' : Rep k r), R.IsDS ε mu → R'.IsDS ε mu' → R''.IsDS ε mu'' → (∀ g ∈ GG k r, SmMap R R (fun v => R.σ g v)) ∧ (∀ (T : R.H → R'.H) (T' : R'.H → R''.H), SmMap R R' T → SmMap R' R'' T' → SmMap R R'' (fun v => T' (T v))) ∧ (∀ (T T' : R.H → R'.H) (a : ℂ), SmMap R R' T → SmMap R R' T' → SmMap R R' (fun v => a • T v + T' v)) ∧ ∀ (Wp : Type) [NormedAddCommGroup Wp] (T : R.H → R'.H) (Bm : R'.H → Wp), SmMap R R' T → PI.BesselMapUniq.IsCWCont (k := k) (r := r) R'.σ Bm → PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ (fun v => Bm (T v)) := by
  first | exact @GlobalTheory.SmMapAct.smMap_act | exact GlobalTheory.SmMapAct.smMap_act | (intros; apply GlobalTheory.SmMapAct.smMap_act <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.GrowthUnitaryGroupRpowNegIntegrable
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.GrowthUnitaryGroupRpowNegIntegrable
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem _root_.GlobalTheory.gN_rpow_neg_integrable_haar : _root_.Formalism.FourierDecayAlt.ThreeDimData.GrowthG := by
  unfold _root_.Formalism.FourierDecayAlt.ThreeDimData.GrowthG
  intro k r μG A hμ hA
  have hW : _root_.Formalism.FourierDecayAlt.B.IsHaarOn (_root_.Formalism.FourierDecayAlt.B.GV k r) μG :=
    (_root_.GlobalTheory.HaarNotions.isHaarOn_iff_groups k r μG).1.1 hμ
  have hvol := _root_.Formalism.FourierDecayAlt.P.norm_ball_volume_sharp
  unfold _root_.Formalism.FourierDecayAlt.B2.VolSharp at hvol
  obtain ⟨C, hC⟩ := hvol k r μG hW
  have hU : ∀ᵐ x ∂μG, Matrix.of x ∈ _root_.Formalism.QuantumDeterminants.UH (_root_.Formalism.QuantumDeterminants.Hpk k r) := by
    unfold _root_.PI.BesselPeriodGGP.IsHaarOn at hμ
    exact ae_iff.2 hμ.2.2.1
  set N : _root_.Formalism.QuantumDeterminants.Mt k r → ℝ := fun x ↦ _root_.Formalism.FourierDecayAlt.B.gN (Matrix.of x) with hNdef
  have hNcont : Continuous N := by
    simp only [hNdef]
    unfold _root_.Formalism.FourierDecayAlt.B.gN
    fun_prop
  have hNm : Measurable N := hNcont.measurable
  have h1 : ∀ᵐ x ∂μG, 1 ≤ N x := hU.mono fun x hx ↦ _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hx
  have hd0 : (0:ℝ) ≤ 2 * ((k:ℝ) + r) * (r + 1) := by positivity
  have hAd : 2 * ((k:ℝ) + r) * (r + 1) < A := by
    have : _root_.Formalism.FourierDecayAlt.ThreeDimData.AG k r = 4 * ((k:ℝ) + r) * (r + 1) := by unfold _root_.Formalism.FourierDecayAlt.ThreeDimData.AG; ring
    rw [this] at hA
    linarith
  set d : ℝ := 2 * ((k:ℝ) + r) * (r + 1) with hd
  set C' : ℝ := max C 0 with hC'
  set q : ℝ := (2:ℝ) ^ (d - A) with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hS : ∀ n : ℕ, MeasurableSet {x | N x ≤ (2:ℝ) ^ (n + 1)} := fun n ↦
    measurableSet_le hNm measurable_const
  have hvolS : ∀ n : ℕ, μG {x | N x ≤ (2:ℝ) ^ (n + 1)}
      ≤ ENNReal.ofReal (C' * ((2:ℝ) ^ (n + 1)) ^ d) := by
    intro n
    refine (hC _ (one_le_pow₀ one_le_two)).trans (ENNReal.ofReal_le_ofReal ?_)
    gcongr
    exact le_max_left _ _
  have hkey : ∀ n : ℕ, ((2:ℝ) ^ n) ^ (-A) * (C' * ((2:ℝ) ^ (n + 1)) ^ d)
      = C' * 2 ^ d * q ^ n := by
    intro n
    rw [← Real.rpow_natCast_mul (by norm_num), ← Real.rpow_natCast_mul (by norm_num), hq,
      ← Real.rpow_mul_natCast (by norm_num)]
    have e : (2:ℝ) ^ ((n:ℝ) * -A) * (2:ℝ) ^ (((n + 1 : ℕ) : ℝ) * d)
        = 2 ^ d * 2 ^ ((d - A) * n) := by
      rw [← Real.rpow_add two_pos, ← Real.rpow_add two_pos]
      congr 1
      push_cast
      ring
    calc ((2:ℝ) ^ ((n:ℝ) * -A)) * (C' * (2:ℝ) ^ (((n + 1 : ℕ) : ℝ) * d))
        = C' * ((2:ℝ) ^ ((n:ℝ) * -A) * (2:ℝ) ^ (((n + 1 : ℕ) : ℝ) * d)) := by ring
      _ = C' * 2 ^ d * 2 ^ ((d - A) * n) := by rw [e]; ring
  have hsum : Summable fun n : ℕ ↦ C' * 2 ^ d * q ^ n :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hpt : ∀ᵐ x ∂μG, ENNReal.ofReal (N x ^ (-A)) ≤ ∑' n : ℕ,
      {y | N y ≤ (2:ℝ) ^ (n + 1)}.indicator (fun _ ↦ ENNReal.ofReal (((2:ℝ) ^ n) ^ (-A))) x := by
    filter_upwards [h1] with x hx
    obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hx one_lt_two
    refine le_trans ?_ (ENNReal.le_tsum n)
    rw [Set.indicator_of_mem (show x ∈ {y | N y ≤ (2:ℝ) ^ (n + 1)} from hn2.le)]
    exact ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_nonpos (by positivity) hn1 (by linarith))
  refine ⟨(hNm.pow_const _).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  calc ∫⁻ x, ‖_root_.Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (-A)‖ₑ ∂μG
      = ∫⁻ x, ENNReal.ofReal (N x ^ (-A)) ∂μG := by
        refine lintegral_congr fun x ↦ ?_
        rw [Real.enorm_eq_ofReal
          (Real.rpow_nonneg (by unfold _root_.Formalism.FourierDecayAlt.B.gN; exact Real.sqrt_nonneg _) _)]
    _ ≤ ∫⁻ x, ∑' n : ℕ, {y | N y ≤ (2:ℝ) ^ (n + 1)}.indicator
          (fun _ ↦ ENNReal.ofReal (((2:ℝ) ^ n) ^ (-A))) x ∂μG := lintegral_mono_ae hpt
    _ = ∑' n : ℕ, ENNReal.ofReal (((2:ℝ) ^ n) ^ (-A)) * μG {y | N y ≤ (2:ℝ) ^ (n + 1)} := by
        rw [lintegral_tsum fun n ↦ (measurable_const.indicator (hS n)).aemeasurable]
        exact tsum_congr fun n ↦ lintegral_indicator_const (hS n) _
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (C' * 2 ^ d * q ^ n) := by
        refine ENNReal.tsum_le_tsum fun n ↦ ?_
        rw [← hkey n, ENNReal.ofReal_mul (by positivity)]
        gcongr
        exact hvolS n
    _ = ENNReal.ofReal (∑' n : ℕ, C' * 2 ^ d * q ^ n) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun n ↦ by positivity) hsum).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.GrowthUnitaryGroupRpowNegIntegrableStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.growth_unitaryGroup_rpow_neg_integrable : Formalism.FourierDecayAlt.ThreeDimData.GrowthG := by
  first | exact @GlobalTheory.gN_rpow_neg_integrable_haar | exact GlobalTheory.gN_rpow_neg_integrable_haar | (intros; apply GlobalTheory.gN_rpow_neg_integrable_haar <;> assumption)
end
end
