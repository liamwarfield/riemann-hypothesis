module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.Groups
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvGroup

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.HaarMap
noncomputable section

open MeasureTheory Matrix Topology
open scoped InnerProductSpace ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open Formalism.QuantumDeterminants

namespace ConjugationHaarMap

variable {k r : ℕ}

theorem conj_closedEmb (P : Mat k r) (hP : IsUnit P.det) :
    IsClosedEmbedding (fun x : Mat k r => ((P⁻¹ * x * P : Mat k r) : Mt k r)) := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hP
  have hc1 : Continuous (fun x : Mat k r => ((P⁻¹ * x * P : Mat k r) : Mt k r)) :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have hc2 : Continuous (fun y : Mt k r => ((P * (show Mat k r from y) * P⁻¹ : Mat k r) : Mat k r)) :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  let e : Mat k r ≃ Mt k r :=
    { toFun := fun x => ((P⁻¹ * x * P : Mat k r) : Mt k r)
      invFun := fun y => ((P * (show Mat k r from y) * P⁻¹ : Mat k r) : Mat k r)
      left_inv := fun x => by
        show P * (P⁻¹ * x * P) * P⁻¹ = x
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]
      right_inv := fun y => by
        show P⁻¹ * (P * (show Mat k r from y) * P⁻¹) * P = (show Mat k r from y)
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one] }
  exact (Homeomorph.mk e hc1 hc2).isClosedEmbedding

private theorem det_unit_of_inUJ_lemma {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : Formalism.REAL.inUJ ε M) : IsUnit M.det := by
  have hJ : (Formalism.REAL.Jm ε).det ≠ 0 := by
    unfold Formalism.REAL.Jm
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun a _ => by split_ifs <;> norm_num)
  rw [isUnit_iff_ne_zero]
  intro h0
  have h := congrArg Matrix.det (show Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε from hM)
  rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at h
  exact hJ h.symm

theorem phi_closedEmb (ε : Fin (2 * r + k + 1) → Bool) (P : Mat k r) (hP : IsUnit P.det) :
    IsClosedEmbedding
      (fun g : Formalism.REAL.UJ ε => ((P⁻¹ * Formalism.MainNotions.S.umat g * P : Mat k r) : Mt k r)) := by
  have hinvc : ContinuousOn (fun A : Mat k r => A⁻¹) {A : Mat k r | IsUnit A} := by
    have he : (fun A : Mat k r => A⁻¹) = fun A => (A.det)⁻¹ • A.adjugate := by
      funext A
      simp only [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [he]
    have hid : Continuous fun A : Mat k r => A := continuous_id
    exact (ContinuousOn.inv₀ hid.matrix_det.continuousOn
      (fun A hA => ((Matrix.isUnit_iff_isUnit_det A).mp hA).ne_zero)).smul hid.matrix_adjugate.continuousOn
  have hval : IsEmbedding (Units.val : (Mat k r)ˣ → Mat k r) :=
    Units.isEmbedding_val_mk' hinvc (fun u => (Matrix.coe_units_inv u).symm)
  have hU : IsClosedEmbedding (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat g) := by
    refine ⟨hval.comp IsEmbedding.subtypeVal, ?_⟩
    have hr : Set.range (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat g) =
        {M : Mat k r | Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε} := by
      ext M
      constructor
      · rintro ⟨g, rfl⟩
        exact g.2
      · intro hM
        exact ⟨⟨M.nonsingInvUnit (det_unit_of_inUJ_lemma ε M hM), hM⟩, rfl⟩
    rw [hr]
    exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
      continuous_id) continuous_const
  exact (conj_closedEmb P hP).comp hU

theorem phi_mem (ε : Fin (2 * r + k + 1) → Bool) (P : Mat k r) (hC : Formalism.MainNotions.S.IsCayley k r ε P)
    (g : Mat k r) (hg : Formalism.REAL.inUJ ε g) : P⁻¹ * g * P ∈ UH (Hpk k r) := by
  obtain ⟨hPu, hPJ⟩ := hC
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  have h2 : (P⁻¹)ᴴ * Pᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  have hg' : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  show (P⁻¹ * g * P)ᴴ * Hpk k r * (P⁻¹ * g * P) = Hpk k r
  rw [← hPJ]
  calc (P⁻¹ * g * P)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * (P⁻¹ * g * P)
      = Pᴴ * ((gᴴ * ((P⁻¹)ᴴ * Pᴴ) * Formalism.REAL.Jm ε * (P * P⁻¹) * g)) * P := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Pᴴ * Formalism.REAL.Jm ε * P := by
        rw [h1, h2, Matrix.mul_one, Matrix.mul_one, hg', Matrix.mul_assoc]

theorem conj_mem (ε : Fin (2 * r + k + 1) → Bool) (P : Mat k r) (hC : Formalism.MainNotions.S.IsCayley k r ε P)
    (s : Mat k r) (hs : s ∈ UH (Hpk k r)) : Formalism.REAL.inUJ ε (P * s * P⁻¹) := by
  obtain ⟨hPu, hPJ⟩ := hC
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  have h2 : (P⁻¹)ᴴ * Pᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  have hs' : sᴴ * Hpk k r * s = Hpk k r := hs
  show (P * s * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * s * P⁻¹) = Formalism.REAL.Jm ε
  calc (P * s * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * s * P⁻¹)
      = (P⁻¹)ᴴ * (sᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * s) * P⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P⁻¹ := by rw [hPJ, hs']
    _ = ((P⁻¹)ᴴ * Pᴴ) * Formalism.REAL.Jm ε * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

end ConjugationHaarMap

theorem haarMap : HaarMapStatement := by
  intro k r ε P hC
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hC.1
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hd
  have h2' : ∀ X : Mat k r, P⁻¹ * (P * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  let φ : Formalism.REAL.UJ ε → Mt k r := fun g => ((P⁻¹ * Formalism.MainNotions.S.umat g * P : Mat k r) : Mt k r)
  have hφ : IsClosedEmbedding φ := ConjugationHaarMap.phi_closedEmb ε P hd
  have hme : MeasurableEmbedding φ := hφ.measurableEmbedding
  show Formalism.MainNotions.S.IsHaarOn (UH (Hpk k r)) ((Measure.haar : Measure (Formalism.REAL.UJ ε)).map φ)
  unfold Formalism.MainNotions.S.IsHaarOn
  refine ⟨hme.sigmaFinite_map, ?_, ?_, ?_⟩
  · rw [Ne, Measure.map_eq_zero_iff hme.measurable.aemeasurable]
    exact Measure.measure_univ_pos.mp (isOpen_univ.measure_pos _ Set.univ_nonempty)
  · rw [hme.map_apply]
    have hE : φ ⁻¹' {x : Mt k r | Matrix.of x ∉ UH (Hpk k r)} = ∅ := by
      refine Set.subset_empty_iff.mp ?_
      intro g hg
      exact absurd (ConjugationHaarMap.phi_mem ε P hC (Formalism.MainNotions.S.umat g) g.2) hg
    rw [hE, measure_empty]
  · intro s hs
    have hsJ := ConjugationHaarMap.conj_mem ε P hC s hs
    let g₀ : Formalism.REAL.UJ ε := ⟨(P * s * P⁻¹).nonsingInvUnit (ConjugationHaarMap.det_unit_of_inUJ_lemma ε _ hsJ), hsJ⟩
    have hcl : Continuous (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) s) := continuous_const.matrix_mul continuous_id
    have hcomp : Formalism.QuantumDeterminants.lmulM s ∘ φ = φ ∘ (fun g => g₀ * g) := by
      funext g
      show s * (P⁻¹ * Formalism.MainNotions.S.umat g * P) = P⁻¹ * ((P * s * P⁻¹) * Formalism.MainNotions.S.umat g) * P
      simp only [Matrix.mul_assoc, h2']
    rw [Measure.map_map hcl.measurable hme.measurable, hcomp,
      ← Measure.map_map hme.measurable (continuous_const_mul g₀).measurable, map_mul_left_eq_self]

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.HaarUniq
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS.Mult1

theorem haarUniq2 : HaarUniq2Statement := by
  intro k r U μ ν hU hμ hν
  haveI : Fact (Formalism.FourierDecayAlt.B2.IsClosedSubgroup U) := ⟨hU⟩
  obtain ⟨hμs, hμ0, hμc, hμl⟩ := hμ
  obtain ⟨hνs, hν0, hνc, hνl⟩ := hν
  have hμc' : μ (HaarSigmaFiniteUniqueness.Aset U)ᶜ = 0 := hμc
  have hνc' : ν (HaarSigmaFiniteUniqueness.Aset U)ᶜ = 0 := hνc
  haveI := hμs
  haveI := hνs
  haveI := HaarSigmaFiniteUniqueness.sigmaFinite_comap (U := U) μ
  haveI := HaarSigmaFiniteUniqueness.sigmaFinite_comap (U := U) ν
  haveI := HaarSigmaFiniteUniqueness.isMulLeftInvariant_comap μ hμc' hμl
  haveI := HaarSigmaFiniteUniqueness.isMulLeftInvariant_comap ν hνc' hνl
  have hμ0' : μ.comap (Subtype.val : HaarSigmaFiniteUniqueness.Aset U → Formalism.QuantumDeterminants.Mt k r) ≠ 0 := by
    intro h
    apply hμ0
    rw [← HaarSigmaFiniteUniqueness.map_comap_val μ hμc', h, Measure.map_zero]
  have hν0' : ν.comap (Subtype.val : HaarSigmaFiniteUniqueness.Aset U → Formalism.QuantumDeterminants.Mt k r) ≠ 0 := by
    intro h
    apply hν0
    rw [← HaarSigmaFiniteUniqueness.map_comap_val ν hνc', h, Measure.map_zero]
  obtain ⟨c, hc, hcE⟩ := HaarSigmaFiniteUniqueness.eq_smul_of_sigmaFinite _ _ hν0' hμ0'
  refine ⟨c, pos_iff_ne_zero.mpr hc, ?_⟩
  have hval : AEMeasurable (Subtype.val : HaarSigmaFiniteUniqueness.Aset U → Formalism.QuantumDeterminants.Mt k r)
      (μ.comap (Subtype.val : HaarSigmaFiniteUniqueness.Aset U → Formalism.QuantumDeterminants.Mt k r)) :=
    (HaarSigmaFiniteUniqueness.mEmb (U := U)).measurable.aemeasurable
  rw [← HaarSigmaFiniteUniqueness.map_comap_val ν hνc', hcE, Measure.map_smul _ hval,
    HaarSigmaFiniteUniqueness.map_comap_val μ hμc']

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Lap

namespace SchurBAux

open Formalism.QuantumDeterminants

theorem conj_cancel {k r : ℕ} {P : Mat k r} (hd : IsUnit P.det) (g : Mat k r) :
    P⁻¹ * (P * g * P⁻¹) * P = g := by
  simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd, Matrix.nonsing_inv_mul _ hd,
    Matrix.mul_one]

theorem conj_cancel' {k r : ℕ} {P : Mat k r} (hd : IsUnit P.det) (g : Mat k r) :
    P * (P⁻¹ * g * P) * P⁻¹ = g := by
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd, Matrix.mul_nonsing_inv _ hd,
    Matrix.mul_one]

theorem conj_mul {k r : ℕ} {P : Mat k r} (hd : IsUnit P.det) (a b : Mat k r) :
    P * (a * b) * P⁻¹ = (P * a * P⁻¹) * (P * b * P⁻¹) := by
  simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd]

theorem conj_inUJ {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P)
    {a : Mat k r} (ha : a ∈ UH (Hpk k r)) : Formalism.REAL.inUJ ε (P * a * P⁻¹) := by
  obtain ⟨hPu, hPe⟩ := hP
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hq1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  have hq2 : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hq1, Matrix.conjTranspose_one]
  show (P * a * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * a * P⁻¹) = Formalism.REAL.Jm ε
  calc (P * a * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * a * P⁻¹)
      = (P⁻¹)ᴴ * (aᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * a) * P⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P⁻¹ := by rw [hPe, ha']
    _ = ((P⁻¹)ᴴ * Pᴴ) * Formalism.REAL.Jm ε * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [hq1, hq2, Matrix.one_mul, Matrix.mul_one]

theorem cont_conj {k r : ℕ} (A B : Mat k r) :
    Continuous (fun x : Mt k r => ((A * Matrix.of x * B : Mat k r) : Mt k r)) := by
  exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem measEmb {k r : ℕ} (ε : Fin (2 * r + k + 1) → Bool) {P : Mat k r} (hd : IsUnit P.det) :
    MeasurableEmbedding (α := Formalism.REAL.UJ ε) (β := Mt k r) (fun g => ((P⁻¹ * Formalism.MainNotions.S.umat g * P : Mat k r) : Mt k r)) := by
  let e : Mt k r ≃ₜ Mt k r :=
    { toFun := fun x => ((P⁻¹ * Matrix.of x * P : Mat k r) : Mt k r)
      invFun := fun x => ((P * Matrix.of x * P⁻¹ : Mat k r) : Mt k r)
      left_inv := fun x => conj_cancel' hd (Matrix.of x)
      right_inv := fun x => conj_cancel hd (Matrix.of x)
      continuous_toFun := cont_conj _ _
      continuous_invFun := cont_conj _ _ }
  have h1 : Topology.IsClosedEmbedding (fun g : Formalism.REAL.UJ ε => (Formalism.MainNotions.S.umat g : Mt k r)) :=
    (Formalism.REAL.isClosedEmbeddingMatrix _ ε).1
  exact (e.isClosedEmbedding.comp h1).measurableEmbedding

end SchurBAux

open Formalism.QuantumDeterminants SchurBAux

theorem schurB : SchurBStatement := by
  intro k r ε lam H _ _ _ σ μG hDSH hH
  obtain ⟨P, ⟨hCay, _⟩, hDS⟩ := hDSH
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hCay.1
  obtain ⟨σ', hσ'⟩ : ∃ σ' : Mat k r → (H →L[ℂ] H), σ' = fun g => σ (P⁻¹ * g * P) := ⟨_, rfl⟩
  rw [← hσ'] at hDS
  have hrep : ∀ g, σ g = σ' (P * g * P⁻¹) := by
    intro g; rw [hσ']; exact (congrArg σ (conj_cancel hd g)).symm
  have uj : ∀ a ∈ UH (Hpk k r), P * a * P⁻¹ ∈ Formalism.MainNotions.S.UJset ε := fun a ha => conj_inUJ hCay ha
  obtain ⟨⟨h1, hmul⟩, hiso, hcont⟩ := hDS.2.2.1
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · rw [hrep, Matrix.mul_one, Matrix.mul_nonsing_inv _ hd]; exact h1
  · intro a ha b hb
    rw [hrep (a * b), hrep a, hrep b, conj_mul hd]
    exact hmul _ (uj a ha) _ (uj b hb)
  · intro g hg v
    rw [hrep]; exact hiso _ (uj g hg) v
  · intro v
    have hc : Continuous (fun g : Mat k r => P * g * P⁻¹) :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    refine ((hcont v).comp hc.continuousOn (fun g hg => uj g hg)).congr ?_
    intro g _
    show σ g v = σ' (P * g * P⁻¹) v
    rw [← hrep]
  · obtain ⟨d, hd0, hF⟩ := Formalism.MainNotions.BridgeCSchur.fdeg_of_DS lam σ' hDS
    have hmap := haarMap k r ε P hCay
    obtain ⟨c, hc, hμ⟩ := haarUniq2 k r _ _ μG (closedSubgroups k r 0).1 hmap hH
    have hemb := measEmb ε hd
    refine ⟨d / (c : ℝ), div_pos hd0 (by exact_mod_cast hc), fun v w v' w' => ?_⟩
    subst hσ'
    have hint := (hF v w v' w').1
    have hval := (hF v w v' w').2
    rw [hμ]
    refine ⟨((hemb.integrable_map_iff (g := fun x : Mt k r => ⟪w, σ (Matrix.of x) v⟫_ℂ * star ⟪w', σ (Matrix.of x) v'⟫_ℂ)).mpr hint).smul_measure_nnreal, ?_⟩
    calc _ = c • (⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)) := by
          rw [integral_smul_nnreal_measure, hemb.integral_map]; exact congrArg (c • ·) hval
      _ = _ := by
          rw [NNReal.smul_def, Complex.real_smul]; push_cast; rw [div_div_eq_mul_div]; ring

end ReciprocityTheory.ChartRestriction.DS.Lap
