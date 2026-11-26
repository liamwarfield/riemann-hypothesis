module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.PsiDatumStatement
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.ContinuousBlkWConj
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.HpkMulVecMulVec
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HermitianMeasures.JSIntFin

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SmoothMatrixMaps.ContinuousSecondMatrix
noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

namespace CurveContinuity

open Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem frob_eq_frobenius {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    frob g = @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm g := by
  rw [@Matrix.frobenius_norm_def, frob, Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Real.rpow_two]

theorem frob_mul_le {n : ℕ} (a b : Matrix (Fin n) (Fin n) ℂ) : frob (a * b) ≤ frob a * frob b := by
  rw [frob_eq_frobenius, frob_eq_frobenius, frob_eq_frobenius]
  exact @Matrix.frobenius_norm_mul _ _ _ _ _ _ _ _ a b

theorem frob_nonneg {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ frob g := Real.sqrt_nonneg _

theorem frob_cont {n : ℕ} : Continuous (fun g : Matrix (Fin n) (Fin n) ℂ => frob g) := by
  unfold frob
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => ((continuous_id.matrix_elem i j).norm).pow 2)

theorem gN_eq_frob {k r : ℕ} (g : Mat k r) : Formalism.FourierDecayAlt.B.gN g = frob g := by
  unfold Formalism.FourierDecayAlt.B.gN frob
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.normSq_eq_norm_sq]

theorem smooth_contOn {n : ℕ} {ε : Fin n → Bool} {f : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hf : Formalism.REAL.SmoothOnG ε f) : ContinuousOn f (UJset ε) := by
  intro g hg
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  have hFc : ContinuousAt F g := hF.continuousOn.continuousAt (hU.mem_nhds hgU)
  refine (hFc.continuousWithinAt (s := UJset ε)).congr_of_eventuallyEq ?_ (hfF g hgU hg)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hU.mem_nhds hgU)] with y hy hyU
  exact hfF y hyU hy

theorem exp_shift {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (t u : ℝ) :
    NormedSpace.exp ((u : ℂ) • X) =
      NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp (((u - t : ℝ) : ℂ) • X) := by
  rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _), ← add_smul]
  congr 2
  push_cast
  ring_nf

theorem hasDeriv_curve {n : ℕ} {ε : Fin n → Bool} {f : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hf : Formalism.REAL.SmoothOnG ε f) {g X : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g)
    (hX : Formalism.REAL.inG ε X) :
    HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (Formalism.REAL.Rd X f g) 0 := by
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  have hγ := Formalism.REAL.hasDerivAt_mul_exp_smul_zero g X
  have hγ0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by simp [NormedSpace.exp_zero]
  have hFd : DifferentiableAt ℝ F g :=
    (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)
  have hcomp : HasDerivAt (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X)))
      (fderiv ℝ F g (g * X)) 0 :=
    hFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  have hev : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0]
      (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) := by
    have hmem : ∀ᶠ t : ℝ in 𝓝 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ U :=
      hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hgU)
    filter_upwards [hmem] with t ht
    exact hfF _ ht (Formalism.REAL.indefinite_unitary_mul_mem ε hg (Formalism.REAL.exp_indefinite_unitary_holds _ ε X hX t))
  rw [Formalism.REAL.right_derivative_extends _ ε f F U g X hU hgU hg hF hfF hX]
  exact hcomp.congr_of_eventuallyEq hev

theorem hasDeriv_curve_at {n : ℕ} {ε : Fin n → Bool} {f : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hf : Formalism.REAL.SmoothOnG ε f) {g X : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g)
    (hX : Formalism.REAL.inG ε X) (t : ℝ) :
    HasDerivAt (fun u : ℝ => f (g * NormedSpace.exp ((u : ℂ) • X)))
      (Formalism.REAL.Rd X f (g * NormedSpace.exp ((t : ℂ) • X))) t := by
  have hg' : Formalism.REAL.inUJ ε (g * NormedSpace.exp ((t : ℂ) • X)) :=
    Formalism.REAL.indefinite_unitary_mul_mem ε hg (Formalism.REAL.exp_indefinite_unitary_holds _ ε X hX t)
  have h0 := hasDeriv_curve hf hg' hX
  have h1 : HasDerivAt (fun s : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp ((s : ℂ) • X)))
      (Formalism.REAL.Rd X f (g * NormedSpace.exp ((t : ℂ) • X))) (t - t) := by
    rw [sub_self]; exact h0
  have h2 := h1.comp_sub_const t t
  refine h2.congr_of_eventuallyEq (Eventually.of_forall fun u => ?_)
  simp only
  rw [Matrix.mul_assoc, ← exp_shift X t u]

theorem curve_cont {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) := by
  refine continuous_iff_continuousAt.2 fun t => ?_
  have h1 : HasDerivAt (fun u : ℝ => NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp ((u : ℂ) • X))
      (NormedSpace.exp ((t : ℂ) • X) * X) (t - t) := by
    rw [sub_self]; exact Formalism.REAL.hasDerivAt_mul_exp_smul_zero _ X
  refine ((h1.comp_sub_const t t).continuousAt).congr (Eventually.of_forall fun u => ?_)
  simp only
  rw [← exp_shift X t u]

theorem rd_smul {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (g : Matrix (Fin n) (Fin n) ℂ)
    (s : ℝ) : Formalism.REAL.Rd ((s : ℂ) • X) f g = (s : ℂ) * Formalism.REAL.Rd X f g := by
  unfold Formalism.REAL.Rd
  have h : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • ((s : ℂ) • X)))) =
      (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) ∘ (fun t => s * t) := by
    funext t
    simp only [Function.comp, smul_smul]
    congr 3
    push_cast; ring_nf
  rw [h]
  have := deriv_comp_mul_left s (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) 0
  simp only [mul_zero] at this
  rw [show ((fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) ∘ fun t => s * t) =
    (fun x => (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (s * x)) from rfl, this,
    Complex.real_smul]

theorem frob_pos {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (hg : g ≠ 0) : 0 < frob g := by
  obtain ⟨i, j, hij⟩ : ∃ i j, g i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hg (Matrix.ext h)
  unfold frob
  apply Real.sqrt_pos.2
  calc (0 : ℝ) < ‖g i j‖ ^ 2 := pow_pos (norm_pos_iff.2 hij) 2
    _ ≤ ∑ j', ‖g i j'‖ ^ 2 :=
        Finset.single_le_sum (f := fun j' => ‖g i j'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ‖g i' j'‖ ^ 2 :=
        Finset.single_le_sum (f := fun i' => ∑ j', ‖g i' j'‖ ^ 2) (fun _ _ => by positivity)
          (Finset.mem_univ i)

theorem ne_zero_of_inUJ {n : ℕ} (hn : 0 < n) {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : Formalism.REAL.inUJ ε g) : g ≠ 0 := by
  rintro rfl
  unfold Formalism.REAL.inUJ at hg
  have h := congrFun (congrFun hg ⟨0, hn⟩) ⟨0, hn⟩
  simp only [Matrix.mul_zero, Matrix.zero_apply, Formalism.REAL.Jm, Matrix.diagonal_apply_eq] at h
  split_ifs at h <;> norm_num at h

theorem one_mem_UH (k r : ℕ) : (1 : Mat k r) ∈ UH (Hpk k r) := by
  show (1 : Mat k r)ᴴ * Hpk k r * 1 = Hpk k r
  simp

theorem uh_mul' {k r : ℕ} {a b : Mat k r} (ha : a ∈ UH (Hpk k r)) (hb : b ∈ UH (Hpk k r)) :
    a * b ∈ UH (Hpk k r) := by
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  calc (a * b)ᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

theorem inUJ_conj {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P)
    {a : Mat k r} (ha : a ∈ UH (Hpk k r)) : Formalism.REAL.inUJ ε (P * a * P⁻¹) := by
  obtain ⟨hPu, hPe⟩ := hP
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  unfold Formalism.REAL.inUJ
  calc (P * a * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * a * P⁻¹)
      = (P⁻¹)ᴴ * (aᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * a) * P⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P⁻¹ := by rw [hPe, ha']
    _ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [h1]; simp

theorem one_inUJ {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by
  unfold Formalism.REAL.inUJ; simp

section Int

variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Mt k r)}

theorem ae_supp (hW : Formalism.MainNotions.S.IsHaarOn (UWset k r z) μW) (hN : Formalism.MainNotions.S.IsHaarOn (Nset k r) μN) :
    ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r := by
  have : SigmaFinite μW := hW.1
  have : SigmaFinite μN := hN.1
  have hWae : ∀ᵐ y ∂μW, Matrix.of y ∈ UWset k r z := by
    rw [ae_iff]; simpa using hW.2.2.1
  have hNae : ∀ᵐ y ∂μN, Matrix.of y ∈ Nset k r := by
    rw [ae_iff]; simpa using hN.2.2.1
  exact (Measure.quasiMeasurePreserving_fst.ae hWae).and (Measure.quasiMeasurePreserving_snd.ae hNae)

def suppA (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Set (Mt k r × Mt k r) :=
  {p | Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r}

theorem continuous_first_matrix : Continuous (fun p : Mt k r × Mt k r => (Matrix.of p.1 : Mat k r)) := continuous_fst

theorem continuous_second_matrix : Continuous (fun p : Mt k r × Mt k r => (Matrix.of p.2 : Mat k r)) := continuous_snd

theorem suppA_closed : IsClosed (suppA k r z) :=
  IsClosed.inter (IsClosed.preimage continuous_first_matrix (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z).closed)
    (IsClosed.preimage continuous_second_matrix (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r).closed)

theorem cont_gp (P x : Mat k r) :
    Continuous (fun p : Mt k r × Mt k r => P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) :=
  (continuous_const.matrix_mul ((continuous_first_matrix.matrix_mul continuous_second_matrix).matrix_mul continuous_const)).matrix_mul
    continuous_const

theorem psiGen_cont (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) :
    Continuous (Formalism.MainNotions.S.psiGen k r z c) := by
  have hell : ∀ a, Continuous fun g : Mat k r => Formalism.MainNotions.S.ellA k r z g a := by
    intro a
    unfold Formalism.MainNotions.S.ellA
    split_ifs
    · exact continuous_id.matrix_elem _ _
    · simp only [Matrix.mulVec, dotProduct]
      exact continuous_finsetSum _ fun j _ => (continuous_id.matrix_elem _ _).mul continuous_const
  unfold Formalism.MainNotions.S.psiGen
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp (continuous_finsetSum _ fun a _ => continuous_const.mul (hell a)))))

variable {u : Fin k → ℝ} {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp]
  {c : Fin r → ℂ} {π : Mat k r → (Vp →L[ℂ] Vp)}

theorem chi_norm (hB : IsBData z c u π μW μN) {h : Mat k r} (hh : h ∈ UWset k r z) (m : Mat k r) (ξ : Vp) :
    ‖chiInv (Formalism.MainNotions.S.psiGen k r z c) π h m ξ‖ = ‖ξ‖ := by
  obtain ⟨hz, hT, hc, hπ, hW, hN⟩ := hB
  have hU := hcTypeW_uRep k r z u Vp π hz hT hπ
  unfold chiInv Formalism.MainNotions.S.psiGen
  rw [norm_smul, norm_star, Complex.norm_exp_I_mul_ofReal, one_mul,
    hU.2.1 _ ((Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z).inv_mem _ hh)]

theorem aesm_int {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P)
    (hB : IsBData z c u π μW μN) {x : Mat k r} (hx : x ∈ UH (Hpk k r)) (ξ : Vp)
    (G : Mat k r → ℂ) (hG : ContinuousOn G (UJset ε)) (e : Mat k r) (he : Formalism.REAL.inUJ ε e) :
    AEStronglyMeasurable (fun p : Mt k r × Mt k r => G (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹ * e) •
      chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of p.1) (Matrix.of p.2) ξ) (μW.prod μN) := by
  obtain ⟨hz, hT, hc, hπ, hW, hN⟩ := hB
  have hU := hcTypeW_uRep k r z u Vp π hz hT hπ
  have hWc := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z
  have hs : ∀ᵐ p ∂(μW.prod μN), p ∈ suppA k r z := ae_supp hW hN
  rw [← Measure.restrict_eq_self_of_ae_mem hs]
  refine ContinuousOn.aestronglyMeasurable ?_ suppA_closed.measurableSet
  refine ContinuousOn.smul ?_ ?_
  · refine hG.comp ((cont_gp P x).matrix_mul continuous_const).continuousOn ?_
    intro p hp
    exact Formalism.REAL.indefinite_unitary_mul_mem ε (inUJ_conj hP (uh_mul' (uh_mul' hp.1.1 hp.2.1) hx)) he
  · unfold chiInv
    refine ContinuousOn.smul ((continuous_star.comp ((psiGen_cont z c).comp continuous_second_matrix)).continuousOn) ?_
    have hinv : ContinuousOn (fun p : Mt k r × Mt k r => (Matrix.of p.1 : Mat k r)⁻¹) (suppA k r z) := by
      intro p hp
      have hdet : IsUnit (Matrix.of p.1 : Mat k r).det := hWc.unit _ hp.1
      refine ContinuousAt.continuousWithinAt ?_
      refine (continuousAt_matrix_inv _ ?_).comp continuous_first_matrix.continuousAt
      rw [← hdet.unit_spec]
      exact NormedRing.inverse_continuousAt hdet.unit
    exact (hU.2.2 ξ).comp hinv (fun p hp => hWc.inv_mem _ hp.1)

theorem bS_nonneg : 0 ≤ S0.bS k r := by unfold S0.bS S0.nS; positivity

theorem int_bound {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P)
    (hB : IsBData z c u π μW μN) {x : Mat k r} (hx : x ∈ UH (Hpk k r)) (a : ℝ) (hb : S0.bS k r < a - 1) :
    Integrable (fun p : Mt k r × Mt k r => frob (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) ^ (1 - a))
      (μW.prod μN) := by
  obtain ⟨hz, hT, hc, hπ, hW, hN⟩ := hB
  have hIS := S0.IntS.intS_of_sIntFin (Mult1.S0.sIntFin Mult1.multiplicity_one_hypotheses_hold)
  have hI := hIS k r z μW μN hz hT hW hN 1 (one_mem_UH k r) x hx (a - 1) hb
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.1
  set K := frob P⁻¹ * frob P with hKdef
  have hK : ∀ g : Mat k r, frob g ≤ K * frob (P * g * P⁻¹) := by
    intro g
    have hg : P⁻¹ * (P * g * P⁻¹) * P = g := by
      simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.nonsing_inv_mul_cancel_left _ _ hd]
    calc frob g = frob (P⁻¹ * (P * g * P⁻¹) * P) := by rw [hg]
      _ ≤ frob P⁻¹ * frob (P * g * P⁻¹) * frob P :=
          (frob_mul_le _ _).trans (mul_le_mul_of_nonneg_right (frob_mul_le _ _) (frob_nonneg _))
      _ = K * frob (P * g * P⁻¹) := by rw [hKdef]; ring_nf
  have ha1 : 1 ≤ a := by linarith [bS_nonneg (k := k) (r := r)]
  refine Integrable.mono' (hI.const_mul (K ^ (a - 1))) ?_ ?_
  · exact ((frob_cont.comp (cont_gp P x)).measurable.pow_const _).aestronglyMeasurable
  · filter_upwards [ae_supp hW hN] with p hp
    have hgU : Matrix.of p.1 * Matrix.of p.2 * x ∈ UH (Hpk k r) := uh_mul' (uh_mul' hp.1.1 hp.2.1) hx
    have hJ := inUJ_conj hP hgU
    have hn : 0 < 2 * r + k + 1 := by omega
    have hG0 : 0 < frob (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) := frob_pos _ (ne_zero_of_inUJ hn hJ)
    have hg0 : 0 < frob (Matrix.of p.1 * Matrix.of p.2 * x) := by
      refine frob_pos _ ?_
      intro h
      apply ne_zero_of_inUJ hn hJ
      rw [h]; simp
    have hKg := hK (Matrix.of p.1 * Matrix.of p.2 * x)
    have hK0 : 0 < K := by
      by_contra hle
      push Not at hle
      have : K * frob (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hle hG0.le
      linarith
    have hle : frob (Matrix.of p.1 * Matrix.of p.2 * x) / K ≤
        frob (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) := by
      rw [div_le_iff₀ hK0]; linarith
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hG0.le _)]
    calc frob (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) ^ (1 - a)
        ≤ (frob (Matrix.of p.1 * Matrix.of p.2 * x) / K) ^ (1 - a) :=
          Real.rpow_le_rpow_of_nonpos (div_pos hg0 hK0) hle (by linarith)
      _ = K ^ (a - 1) * Formalism.FourierDecayAlt.B.gN ((1 : Mat k r)⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * x)) ^ (-(a - 1)) := by
          rw [inv_one, Matrix.one_mul, gN_eq_frob, Real.div_rpow hg0.le hK0.le, neg_sub, div_eq_mul_inv,
            ← Real.rpow_neg hK0.le, neg_sub, mul_comm]

end Int

end CurveContinuity

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

namespace CurveContinuity

open Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Der

variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Mt k r)}
variable {u : Fin k → ℝ} {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp]
  {c : Fin r → ℂ} {π : Mat k r → (Vp →L[ℂ] Vp)}

theorem int_of_bound {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P)
    (hB : IsBData z c u π μW μN) {x : Mat k r} (hx : x ∈ UH (Hpk k r)) (ξ : Vp) (a : ℝ)
    (hb : S0.bS k r < a - 1) (G : Mat k r → ℂ) (hG : ContinuousOn G (UJset ε)) (CG : ℝ)
    (hCG : ∀ g ∈ UJset ε, ‖G g‖ ≤ CG * frob g ^ (1 - a)) :
    Integrable (fun p : Mt k r × Mt k r => G (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) •
      chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of p.1) (Matrix.of p.2) ξ) (μW.prod μN) := by
  have hm := aesm_int hP hB hx ξ G hG 1 (one_inUJ ε)
  simp only [Matrix.mul_one] at hm
  refine Integrable.mono' ((int_bound hP hB hx a hb).const_mul (|CG| * ‖ξ‖)) hm ?_
  filter_upwards [ae_supp hB.2.2.2.2.1 hB.2.2.2.2.2] with p hp
  rw [norm_smul, chi_norm hB hp.1]
  have hJ := inUJ_conj hP (uh_mul' (uh_mul' hp.1.1 hp.2.1) hx)
  have h1 := hCG _ hJ
  set y := frob (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) ^ (1 - a) with hy
  have h2 : 0 ≤ y := Real.rpow_nonneg (frob_nonneg _) _
  have h3 : CG * y ≤ |CG| * y := mul_le_mul_of_nonneg_right (le_abs_self CG) h2
  calc ‖G (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹)‖ * ‖ξ‖ ≤ (|CG| * y) * ‖ξ‖ :=
        mul_le_mul_of_nonneg_right (h1.trans h3) (norm_nonneg _)
    _ = |CG| * ‖ξ‖ * y := by ring_nf

theorem deriv_int {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P)
    (hB : IsBData z c u π μW μN) {x : Mat k r} (hx : x ∈ UH (Hpk k r)) (ξ : Vp) (a : ℝ)
    (hb : S0.bS k r < a - 1) (F : Mat k r → ℂ) (hF : Formalism.REAL.SmoothOnG ε F) (C0 : ℝ)
    (hC0 : ∀ g ∈ UJset ε, ‖F g‖ ≤ C0 * frob g ^ (1 - a))
    (X : Mat k r) (hX : Formalism.REAL.inG ε X) (CX : ℝ)
    (hCX : ∀ g ∈ UJset ε, ‖Formalism.REAL.Rd X F g‖ ≤ CX * frob g ^ (1 - a)) :
    Integrable (fun p : Mt k r × Mt k r => Formalism.REAL.Rd X F (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) •
        chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of p.1) (Matrix.of p.2) ξ) (μW.prod μN) ∧
    HasDerivAt (fun t : ℝ => ∫ p : Mt k r × Mt k r,
        F (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹ * NormedSpace.exp ((t : ℂ) • X)) •
          chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of p.1) (Matrix.of p.2) ξ ∂(μW.prod μN))
      (∫ p : Mt k r × Mt k r, Formalism.REAL.Rd X F (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) •
        chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of p.1) (Matrix.of p.2) ξ ∂(μW.prod μN)) 0 := by
  have hFc := smooth_contOn hF
  have hRc := smooth_contOn (Formalism.REAL.rdSmooth _ ε F X hF hX)
  have h0 : ∀ g : Mat k r, g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := fun g => by
    simp [NormedSpace.exp_zero]
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℝ) 1).exists_bound_of_continuousOn
    ((frob_cont.comp ((curve_cont X).comp (continuous_const.sub continuous_id))).continuousOn
      (s := Metric.closedBall (0 : ℝ) 1))
  set M' := max M 1 with hM'def
  have hM' : ∀ t ∈ Metric.ball (0 : ℝ) 1, frob (NormedSpace.exp ((((0 : ℝ) - t : ℝ) : ℂ) • X)) ≤ M' := by
    intro t ht
    have := hM t (Metric.ball_subset_closedBall ht)
    simp only [Function.comp] at this
    rw [Real.norm_of_nonneg (frob_nonneg _)] at this
    exact this.trans (le_max_left _ _)
  have hM'0 : 0 < M' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have ha1 : 1 ≤ a := by linarith [bS_nonneg (k := k) (r := r)]
  have hn : 0 < 2 * r + k + 1 := by omega
  have hsupp := ae_supp hB.2.2.2.2.1 hB.2.2.2.2.2
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μW.prod μN) (x₀ := (0 : ℝ))
    (F := fun (t : ℝ) (p : Mt k r × Mt k r) =>
      F (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹ * NormedSpace.exp ((t : ℂ) • X)) •
        chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of p.1) (Matrix.of p.2) ξ)
    (F' := fun (t : ℝ) (p : Mt k r × Mt k r) =>
      Formalism.REAL.Rd X F (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹ * NormedSpace.exp ((t : ℂ) • X)) •
        chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of p.1) (Matrix.of p.2) ξ)
    (bound := fun p => (|CX| * ‖ξ‖ * M' ^ (a - 1)) * frob (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) ^ (1 - a))
    (Metric.ball_mem_nhds (0 : ℝ) one_pos)
    (Eventually.of_forall fun t => aesm_int hP hB hx ξ F hFc _ (Formalism.REAL.exp_indefinite_unitary_holds _ ε X hX t))
    (by simp only [h0]; exact int_of_bound hP hB hx ξ a hb F hFc C0 hC0)
    (aesm_int hP hB hx ξ _ hRc _ (Formalism.REAL.exp_indefinite_unitary_holds _ ε X hX 0))
    ?_ ((int_bound hP hB hx a hb).const_mul _) ?_
  · simp only [h0] at key
    exact key
  · filter_upwards [hsupp] with p hp t ht
    set g := P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹ with hg
    have hJ : Formalism.REAL.inUJ ε g := inUJ_conj hP (uh_mul' (uh_mul' hp.1.1 hp.2.1) hx)
    have hJt : Formalism.REAL.inUJ ε (g * NormedSpace.exp ((t : ℂ) • X)) :=
      Formalism.REAL.indefinite_unitary_mul_mem ε hJ (Formalism.REAL.exp_indefinite_unitary_holds _ ε X hX t)
    rw [norm_smul, chi_norm hB hp.1]
    have hg0 : 0 < frob g := frob_pos _ (ne_zero_of_inUJ hn hJ)
    have hprod : g * NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp ((((0 : ℝ) - t : ℝ) : ℂ) • X) = g := by
      rw [Matrix.mul_assoc, ← exp_shift X t 0]
      simp [NormedSpace.exp_zero]
    have hle0 : frob g ≤ frob (g * NormedSpace.exp ((t : ℂ) • X)) * M' := by
      calc frob g = frob (g * NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp ((((0 : ℝ) - t : ℝ) : ℂ) • X)) := by
            rw [hprod]
        _ ≤ frob (g * NormedSpace.exp ((t : ℂ) • X)) * frob (NormedSpace.exp ((((0 : ℝ) - t : ℝ) : ℂ) • X)) :=
            frob_mul_le _ _
        _ ≤ frob (g * NormedSpace.exp ((t : ℂ) • X)) * M' :=
            mul_le_mul_of_nonneg_left (hM' t ht) (frob_nonneg _)
    have hle : frob g / M' ≤ frob (g * NormedSpace.exp ((t : ℂ) • X)) := by
      rw [div_le_iff₀ hM'0]; exact hle0
    have hpow : frob (g * NormedSpace.exp ((t : ℂ) • X)) ^ (1 - a) ≤ M' ^ (a - 1) * frob g ^ (1 - a) := by
      calc frob (g * NormedSpace.exp ((t : ℂ) • X)) ^ (1 - a) ≤ (frob g / M') ^ (1 - a) :=
            Real.rpow_le_rpow_of_nonpos (div_pos hg0 hM'0) hle (by linarith)
        _ = M' ^ (a - 1) * frob g ^ (1 - a) := by
            rw [Real.div_rpow hg0.le hM'0.le, div_eq_mul_inv, ← Real.rpow_neg hM'0.le, neg_sub, mul_comm]
    have h1 := hCX _ hJt
    set y := frob (g * NormedSpace.exp ((t : ℂ) • X)) ^ (1 - a) with hy
    have h2 : 0 ≤ y := Real.rpow_nonneg (frob_nonneg _) _
    have h3 : CX * y ≤ |CX| * y := mul_le_mul_of_nonneg_right (le_abs_self CX) h2
    have h4 : |CX| * y ≤ |CX| * (M' ^ (a - 1) * frob g ^ (1 - a)) :=
      mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
    calc ‖Formalism.REAL.Rd X F (g * NormedSpace.exp ((t : ℂ) • X))‖ * ‖ξ‖
        ≤ (|CX| * (M' ^ (a - 1) * frob g ^ (1 - a))) * ‖ξ‖ :=
          mul_le_mul_of_nonneg_right ((h1.trans h3).trans h4) (norm_nonneg _)
      _ = |CX| * ‖ξ‖ * M' ^ (a - 1) * frob g ^ (1 - a) := by ring_nf
  · filter_upwards [hsupp] with p hp t _
    have hJ : Formalism.REAL.inUJ ε (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) :=
      inUJ_conj hP (uh_mul' (uh_mul' hp.1.1 hp.2.1) hx)
    exact (hasDeriv_curve_at hF hJ hX t).smul_const _

end Der

def sg {n : ℕ} (ε : Fin n → Bool) (a b : Fin n) : ℝ := (if ε a then 1 else -1) * (if ε b then 1 else -1)

theorem sg_sq {n : ℕ} (ε : Fin n → Bool) (a b : Fin n) : ((sg ε a b : ℝ) : ℂ) * (sg ε a b : ℂ) = 1 := by
  unfold sg; split_ifs <;> push_cast <;> ring_nf

theorem sg_comm {n : ℕ} (ε : Fin n → Bool) (a b : Fin n) : sg ε b a = sg ε a b := by
  unfold sg; ring_nf

theorem sg_norm {n : ℕ} (ε : Fin n → Bool) (a b : Fin n) : ‖((sg ε a b : ℝ) : ℂ)‖ = 1 := by
  unfold sg; split_ifs <;> simp

theorem jsj {n : ℕ} (ε : Fin n → Bool) (a b : Fin n) :
    Formalism.REAL.Jm ε * (Matrix.single a b (1 : ℂ))ᴴ * Formalism.REAL.Jm ε = ((sg ε a b : ℝ) : ℂ) • Matrix.single b a 1 := by
  ext i j
  unfold Formalism.REAL.Jm
  rw [Matrix.conjTranspose_single, star_one, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply,
    smul_eq_mul]
  by_cases h : b = i ∧ a = j
  · obtain ⟨rfl, rfl⟩ := h
    rw [Matrix.single_apply_same]
    unfold sg
    split_ifs <;> push_cast <;> ring_nf
  · simp only [Matrix.single_apply, if_neg h, mul_zero, zero_mul]

theorem cpart1_rel {n : ℕ} (ε : Fin n → Bool) (a b : Fin n) :
    Formalism.REAL.cpart1 ε (Matrix.single b a 1) = ((-sg ε a b : ℝ) : ℂ) • Formalism.REAL.cpart1 ε (Matrix.single a b 1) := by
  unfold Formalism.REAL.cpart1
  rw [jsj ε b a, jsj ε a b, sg_comm]
  have hs := sg_sq ε a b
  ext i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  push_cast
  linear_combination (-(1 / 2) * (Matrix.single b a (1 : ℂ) i j)) * hs

theorem cpart2_rel {n : ℕ} (ε : Fin n → Bool) (a b : Fin n) :
    Formalism.REAL.cpart2 ε (Matrix.single b a 1) = ((sg ε a b : ℝ) : ℂ) • Formalism.REAL.cpart2 ε (Matrix.single a b 1) := by
  unfold Formalism.REAL.cpart2
  rw [jsj ε b a, jsj ε a b, sg_comm]
  have hs := sg_sq ε a b
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  linear_combination (-(1 / (2 * Complex.I)) * (Matrix.single b a (1 : ℂ) i j)) * hs

theorem rd_bounds {n : ℕ} (ε : Fin n → Bool) (a b : Fin n) (F : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (g : Matrix (Fin n) (Fin n) ℂ) :
    ‖Formalism.REAL.Rd (Formalism.REAL.cpart1 ε (Matrix.single a b 1)) F g‖ ≤
              (‖Formalism.REAL.Eab ε a b F g‖ + ‖Formalism.REAL.Eab ε b a F g‖) / 2 ∧
      ‖Formalism.REAL.Rd (Formalism.REAL.cpart2 ε (Matrix.single a b 1)) F g‖ ≤
        (‖Formalism.REAL.Eab ε a b F g‖ + ‖Formalism.REAL.Eab ε b a F g‖) / 2 := by
  set R1 := Formalism.REAL.Rd (Formalism.REAL.cpart1 ε (Matrix.single a b 1)) F g
  set R2 := Formalism.REAL.Rd (Formalism.REAL.cpart2 ε (Matrix.single a b 1)) F g
  set s : ℂ := ((sg ε a b : ℝ) : ℂ) with hsdef
  have hs := sg_sq ε a b
  have hE1 : Formalism.REAL.Eab ε a b F g = R1 + Complex.I * R2 := rfl
  have hE2 : Formalism.REAL.Eab ε b a F g = -s * R1 + Complex.I * (s * R2) := by
    show Formalism.REAL.Rd (Formalism.REAL.cpart1 ε (Matrix.single b a 1)) F g +
      Complex.I * Formalism.REAL.Rd (Formalism.REAL.cpart2 ε (Matrix.single b a 1)) F g = _
    rw [cpart1_rel, cpart2_rel, rd_smul, rd_smul]
    simp only [R1, R2, s]
    push_cast
    ring
  have hR1 : 2 * R1 = Formalism.REAL.Eab ε a b F g - s * Formalism.REAL.Eab ε b a F g := by
    rw [hE1, hE2]; linear_combination (Complex.I * R2 - R1) * hs
  have hR2 : (2 * Complex.I) * R2 = Formalism.REAL.Eab ε a b F g + s * Formalism.REAL.Eab ε b a F g := by
    rw [hE1, hE2]; linear_combination (R1 - Complex.I * R2) * hs
  have hsn : ‖s‖ = 1 := sg_norm ε a b
  constructor
  · have h := congrArg norm hR1
    rw [norm_mul, Complex.norm_ofNat] at h
    have := norm_sub_le (Formalism.REAL.Eab ε a b F g) (s * Formalism.REAL.Eab ε b a F g)
    rw [norm_mul, hsn, one_mul] at this
    linarith
  · have h := congrArg norm hR2
    rw [norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one] at h
    have := norm_add_le (Formalism.REAL.Eab ε a b F g) (s * Formalism.REAL.Eab ε b a F g)
    rw [norm_mul, hsn, one_mul] at this
    linarith

theorem per_gap {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {h : ℝ} (hgap : StepGap ε r h) :
    S0.bS k r < aExp ε h - 1 := by
  have h2 := hgap.2
  have hq0 : ((S7.q0 ε : ℕ) : ℝ) = (min (pOf ε) (qOf ε) : ℝ) := by unfold S7.q0; norm_cast
  have hB0 : S0.bS k r = 2 * (r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := rfl
  have hle : 2 * (r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 ≤
      max (2 * ((2 * r + k + 1 : ℕ) : ℝ) * (min (pOf ε) (qOf ε) : ℝ)) (2 * (r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2) :=
    le_max_right _ _
  have h0 : 0 ≤ 2 * (r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  unfold aExp
  rw [hq0, hB0]
  linarith

end CurveContinuity

open CurveContinuity in
theorem per_spec : PerStatement := by
  intro k r ε u h z c Vp _ _ _ π μW μN P hP hB _ _ hgap
  have hb := per_gap hgap
  refine ⟨fun F C hFc hFb x hx ξ => int_of_bound hP hB hx ξ (aExp ε h) hb F hFc C hFb, ?_⟩
  intro F hF hW a b x hx ξ
  obtain ⟨C0, hC0⟩ := hW []
  obtain ⟨C1, hC1⟩ := hW [(a, b)]
  obtain ⟨C2, hC2⟩ := hW [(b, a)]
  have hC1' : ∀ g ∈ UJset ε, ‖Formalism.REAL.Eab ε a b F g‖ ≤ C1 * frob g ^ (1 - aExp ε h) := hC1
  have hC2' : ∀ g ∈ UJset ε, ‖Formalism.REAL.Eab ε b a F g‖ ≤ C2 * frob g ^ (1 - aExp ε h) := hC2
  have hC0' : ∀ g ∈ UJset ε, ‖F g‖ ≤ C0 * frob g ^ (1 - aExp ε h) := hC0
  have hcm := Formalism.REAL.cpartMem _ ε (Matrix.single a b 1)
  have hR : ∀ i : Fin 2, ∀ g ∈ UJset ε,
      ‖Formalism.REAL.Rd ((if i = 0 then Formalism.REAL.cpart1 else Formalism.REAL.cpart2) ε (Matrix.single a b 1)) F g‖ ≤
        ((C1 + C2) / 2) * frob g ^ (1 - aExp ε h) := by
    intro i g hg
    have hrb := rd_bounds ε a b F g
    have h1 := hC1' g hg
    have h2 := hC2' g hg
    have : (‖Formalism.REAL.Eab ε a b F g‖ + ‖Formalism.REAL.Eab ε b a F g‖) / 2 ≤ ((C1 + C2) / 2) * frob g ^ (1 - aExp ε h) := by
      linarith
    fin_cases i
    · exact hrb.1.trans this
    · exact hrb.2.trans this
  obtain ⟨hi1, hd1⟩ := deriv_int hP hB hx ξ (aExp ε h) hb F hF C0 hC0' _ hcm.1 _ (hR 0)
  obtain ⟨hi2, hd2⟩ := deriv_int hP hB hx ξ (aExp ε h) hb F hF C0 hC0' _ hcm.2.1 _ (hR 1)
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.1
  have hΦ : ∀ (X : Mat k r) (t : ℝ),
      per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π F ξ (P⁻¹ * (P * x * P⁻¹ * NormedSpace.exp ((t : ℂ) • X)) * P) =
        ∫ p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r,
          F (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹ * NormedSpace.exp ((t : ℂ) • X)) •
            chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of p.1) (Matrix.of p.2) ξ ∂(μW.prod μN) := by
    intro X t
    unfold per sInt
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only
    congr 2
    simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd, Matrix.mul_nonsing_inv _ hd]
  show (∫ p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r,
      (Formalism.REAL.Rd (Formalism.REAL.cpart1 ε (Matrix.single a b 1)) F (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) +
        Complex.I * Formalism.REAL.Rd (Formalism.REAL.cpart2 ε (Matrix.single a b 1)) F
          (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹)) •
        chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of p.1) (Matrix.of p.2) ξ ∂(μW.prod μN)) =
    deriv (fun t : ℝ => per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π F ξ
        (P⁻¹ * (P * x * P⁻¹ * NormedSpace.exp ((t : ℂ) • Formalism.REAL.cpart1 ε (Matrix.single a b 1))) * P)) 0 +
      Complex.I • deriv (fun t : ℝ => per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π F ξ
        (P⁻¹ * (P * x * P⁻¹ * NormedSpace.exp ((t : ℂ) • Formalism.REAL.cpart2 ε (Matrix.single a b 1))) * P)) 0
  simp only [hΦ]
  rw [hd1.deriv, hd2.deriv, ← integral_smul, ← integral_add hi1 ?hI2]
  · refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [add_smul, mul_smul]
  · exact hi2.smul Complex.I

end ReciprocityTheory.ChartRestriction.DS.Lap
