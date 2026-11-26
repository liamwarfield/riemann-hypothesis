module

public import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfSt

@[expose] public section

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfK
noncomputable section

open Formalism.IndefR.Datum Matrix
open scoped ComplexOrder

namespace Formalism.IndefR.Tow.SobPf

variable {n : ℕ}

theorem quad_smul (A : Matrix (Fin n) (Fin n) ℂ) (r : ℝ) (x : Fin n → ℂ) :
    (star ((r : ℂ) • x) ⬝ᵥ A *ᵥ ((r : ℂ) • x)) = (r : ℂ) ^ 2 * (star x ⬝ᵥ A *ᵥ x) := by

  have h1 : star ((r : ℂ) • x) = (r : ℂ) • star x := by
    rw [star_smul]; simp
  rw [h1, Matrix.mulVec_smul]
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

theorem continuous_quad (A : Matrix (Fin n) (Fin n) ℂ) :
    Continuous fun x : Fin n → ℂ => (star x ⬝ᵥ A *ᵥ x).re := by
  have h : Continuous fun x : Fin n → ℂ => star x ⬝ᵥ A *ᵥ x := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
    fun_prop
  exact Complex.continuous_re.comp h

theorem posDef_lower (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) :
    ∃ c > (0 : ℝ), ∀ x : Fin n → ℂ, c * ‖x‖ ^ 2 ≤ (star x ⬝ᵥ A *ᵥ x).re := by

  have sph : ∀ x : Fin n → ℂ, x ≠ 0 →
      ((‖x‖⁻¹ : ℝ) : ℂ) • x ∈ Metric.sphere (0 : Fin n → ℂ) 1 ∧
        x = ((‖x‖ : ℝ) : ℂ) • (((‖x‖⁻¹ : ℝ) : ℂ) • x) := by
    intro x hx
    have hnx : 0 < ‖x‖ := norm_pos_iff.2 hx
    refine ⟨?_, ?_⟩
    · rw [mem_sphere_zero_iff_norm, norm_smul]
      simp [hnx.ne']
    · rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hnx.ne', Complex.ofReal_one, one_smul]
  by_cases hS : (Metric.sphere (0 : Fin n → ℂ) 1).Nonempty
  · obtain ⟨x0, hx0, hmin⟩ := (isCompact_sphere (0 : Fin n → ℂ) 1).exists_isMinOn hS
      (continuous_quad A).continuousOn
    have hx0ne : x0 ≠ 0 := by
      intro h
      rw [h, mem_sphere_zero_iff_norm, norm_zero] at hx0
      exact zero_ne_one hx0
    refine ⟨(star x0 ⬝ᵥ A *ᵥ x0).re, ?_, ?_⟩
    · have h := hA.dotProduct_mulVec_pos hx0ne
      have h2 := (Complex.lt_def.1 h).1
      simpa using h2
    · intro x
      by_cases hx : x = 0
      · subst hx; simp
      · obtain ⟨hu, hxu⟩ := sph x hx
        set u : Fin n → ℂ := ((‖x‖⁻¹ : ℝ) : ℂ) • x with hu_def
        have key : (star x ⬝ᵥ A *ᵥ x) = ((‖x‖ : ℝ) : ℂ) ^ 2 * (star u ⬝ᵥ A *ᵥ u) := by
          conv_lhs => rw [hxu]
          exact quad_smul A ‖x‖ u
        have hre : (star x ⬝ᵥ A *ᵥ x).re = ‖x‖ ^ 2 * (star u ⬝ᵥ A *ᵥ u).re := by
          rw [key, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
        have hle : (star x0 ⬝ᵥ A *ᵥ x0).re ≤ (star u ⬝ᵥ A *ᵥ u).re := isMinOn_iff.1 hmin u hu
        rw [hre, mul_comm]
        exact mul_le_mul_of_nonneg_left hle (sq_nonneg _)
  · refine ⟨1, one_pos, fun x => ?_⟩
    by_cases hx : x = 0
    · subst hx; simp
    · exact absurd ⟨_, (sph x hx).1⟩ hS

theorem KAt_pres {G s k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ KAt G s) : kᴴ * (G * s) * k = G * s := by

  have hk' : k ∈ Formalism.QuantumDeterminants.UH G ∧ k * s = s * k := hk
  have h1 : kᴴ * G * k = G := hk'.1
  calc kᴴ * (G * s) * k = kᴴ * G * (s * k) := by simp only [Matrix.mul_assoc]
    _ = kᴴ * G * (k * s) := by rw [hk'.2]
    _ = (kᴴ * G * k) * s := by simp only [Matrix.mul_assoc]
    _ = G * s := by rw [h1]

theorem isClosed_KAt (G s : Matrix (Fin n) (Fin n) ℂ) : IsClosed (KAt G s) := by

  have e : KAt G s = {g | gᴴ * G * g = G} ∩ {g | g * s = s * g} := Set.ext fun _ => Iff.rfl
  rw [e]
  refine IsClosed.inter (isClosed_eq ?_ continuous_const) (isClosed_eq ?_ ?_)
  · exact (continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id
  · exact continuous_id.matrix_mul continuous_const
  · exact continuous_const.matrix_mul continuous_id

theorem isCompact_KAt {G s : Matrix (Fin n) (Fin n) ℂ} (hs : IsCartanInv G s) : IsCompact (KAt G s) := by
  obtain ⟨-, -, hP⟩ := hs
  obtain ⟨c, hc, hcP⟩ := posDef_lower (G * s) hP
  have hvec : ∀ k ∈ KAt G s, ∀ x : Fin n → ℂ,
      ‖k *ᵥ x‖ ^ 2 ≤ (star x ⬝ᵥ (G * s) *ᵥ x).re / c := by
    intro k hk x
    have hpres : kᴴ * ((G * s) * k) = G * s := by
      rw [← Matrix.mul_assoc]; exact KAt_pres hk
    have h2 : star (k *ᵥ x) ⬝ᵥ (G * s) *ᵥ (k *ᵥ x) = star x ⬝ᵥ (G * s) *ᵥ x := by
      rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
        hpres, ← Matrix.dotProduct_mulVec]
    have h1 := hcP (k *ᵥ x)
    rw [h2] at h1
    rw [le_div_iff₀ hc, mul_comm]
    exact h1
  refine IsCompact.of_isClosed_subset (isCompact_univ_pi fun i => isCompact_univ_pi fun j =>
    isCompact_closedBall (0 : ℂ)
      (Real.sqrt ((star (Pi.single j 1 : Fin n → ℂ) ⬝ᵥ (G * s) *ᵥ (Pi.single j 1 : Fin n → ℂ)).re / c)))
    (isClosed_KAt G s) ?_
  intro k hk
  refine Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j => ?_
  rw [mem_closedBall_zero_iff]
  have hcomp : (k *ᵥ (Pi.single j 1 : Fin n → ℂ)) i = k i j := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hle : ‖k i j‖ ≤ ‖k *ᵥ (Pi.single j 1 : Fin n → ℂ)‖ := by
    rw [← hcomp]; exact norm_le_pi_norm _ i
  have hsq : ‖k i j‖ ^ 2 ≤ (star (Pi.single j 1 : Fin n → ℂ) ⬝ᵥ (G * s) *ᵥ (Pi.single j 1 : Fin n → ℂ)).re / c :=
    le_trans (pow_le_pow_left₀ (norm_nonneg _) hle 2) (hvec k hk _)
  calc ‖k i j‖ = |‖k i j‖| := (abs_norm _).symm
    _ ≤ _ := Real.abs_le_sqrt hsq

end Formalism.IndefR.Tow.SobPf

end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfAs
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Mult
  MeasureTheory Matrix Filter Topology

namespace Formalism.IndefR.Tow.SobPf

theorem oneProd_zero {n d : ℕ} (Y : Fin d → Matrix (Fin n) (Fin n) ℂ) : oneProd Y 0 = 1 := by
  simp [oneProd]

theorem continuity_of_sobolev_chart (h4 : SobChart) (h5 : FoldCont) : Cont1 := by
  intro n H _ _ G s π hs hπ w hw l hl ε hε
  obtain ⟨d, Y, hY, hch⟩ := h4 G s hs
  have hc := h5 G π hπ w hw l hl d Y hY
  have h0 : dL π l (π (oneProd Y 0) w) = dL π l w := by
    rw [oneProd_zero, hπ.1, ContinuousLinearMap.one_apply]
  obtain ⟨η, hη, hηc⟩ := Metric.continuous_iff.1 hc 0 ε hε
  obtain ⟨δ, hδ, hδc⟩ := hch η hη
  refine ⟨δ, hδ, fun g hg hgd => ?_⟩
  obtain ⟨t, ht, rfl⟩ := hδc g hg hgd
  have htn : dist t 0 < η := by
    rw [dist_zero_right]
    exact (pi_norm_lt_iff hη).2 fun i => by rw [Real.norm_eq_abs]; exact ht i
  have h1 := hηc t htn
  beta_reduce at h1
  rw [dist_eq_norm, h0] at h1
  exact h1

theorem one_mem_KAt {n : ℕ} (G s : Matrix (Fin n) (Fin n) ℂ) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ KAt G s := by
  simp [KAt, Formalism.QuantumDeterminants.UH]

theorem continuous_evP {n : ℕ} (q : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ) :
    Continuous (evP q) := by
  unfold evP
  refine (MvPolynomial.continuous_eval q).comp (continuous_pi fun s => ?_)
  rcases s with ⟨i, j⟩ | ⟨i, j⟩
  · simp only [Sum.elim_inl]
    exact (continuous_apply j).comp (continuous_apply i)
  · simp only [Sum.elim_inr]
    exact Complex.continuous_conj.comp ((continuous_apply j).comp (continuous_apply i))

theorem exists_delta_list {α : Type*} (S : List α) (P : α → ℝ → Prop)
    (hP : ∀ a ∈ S, ∃ δ > (0 : ℝ), ∀ δ', 0 < δ' → δ' ≤ δ → P a δ') :
    ∃ δ > (0 : ℝ), ∀ a ∈ S, ∀ δ', 0 < δ' → δ' ≤ δ → P a δ' := by
  induction S with
  | nil => exact ⟨1, one_pos, fun a ha => by simp at ha⟩
  | cons a S ih =>
    obtain ⟨δ1, h1, hδ1⟩ := hP a (by simp)
    obtain ⟨δ2, h2, hδ2⟩ := ih fun b hb => hP b (by simp [hb])
    refine ⟨min δ1 δ2, lt_min h1 h2, fun b hb δ' hδ' hle => ?_⟩
    rcases List.mem_cons.1 hb with rfl | hb
    · exact hδ1 δ' hδ' (hle.trans (min_le_left _ _))
    · exact hδ2 b hb δ' hδ' (hle.trans (min_le_right _ _))

theorem exists_bound_list {α β : Type*} (S : List α) (A : Set β) (f : α → β → ℝ)
    (h : ∀ a ∈ S, ∃ B : ℝ, ∀ b ∈ A, f a b ≤ B) : ∃ B : ℝ, 0 ≤ B ∧ ∀ a ∈ S, ∀ b ∈ A, f a b ≤ B := by
  induction S with
  | nil => exact ⟨0, le_rfl, fun a ha => by simp at ha⟩
  | cons a S ih =>
    obtain ⟨B1, hB1⟩ := h a (by simp)
    obtain ⟨B2, _, hB2⟩ := ih fun c hc => h c (by simp [hc])
    refine ⟨max (max B1 B2) 0, le_max_right _ _, fun c hc b hb => ?_⟩
    rcases List.mem_cons.1 hc with rfl | hc
    · exact (hB1 b hb).trans ((le_max_left _ _).trans (le_max_left _ _))
    · exact (hB2 c hc b hb).trans ((le_max_right _ _).trans (le_max_left _ _))

theorem sobApprox_of (h8a : HaarExists) (h8b : PolyKernel) (h8c : AvgSmooth) (h8d : AvgKFin) (h6 : Cont1)
    (h8e : FoldBddK) : SobApprox := by
  intro n H _ _ _ G s π hs hπ w hw S hS ε hε
  obtain ⟨μ, hμ⟩ := h8a G s hs
  have hμ' := hμ
  obtain ⟨-, hae, -, -⟩ := hμ'
  have hπ1 : π 1 = 1 := hπ.1
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨δ, hδ, hδS⟩ := exists_delta_list S
    (fun l δ' => ∀ g ∈ Formalism.QuantumDeterminants.UH G, (∀ i j, ‖g i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ < δ') →
      ‖dL π l (π g w) - dL π l w‖ < ε / 2)
    (fun l hl => by
      obtain ⟨δ₀, hδ₀, h⟩ := h6 G s π hs hπ w hw l (hS l hl) (ε / 2) hε2
      exact ⟨δ₀, hδ₀, fun δ' _ hδ' g hg hgd => h g hg (fun i j => lt_of_lt_of_le (hgd i j) hδ')⟩)
  obtain ⟨B, hB0, hB⟩ := exists_bound_list S (KAt G s) (fun l k => ‖dL π l (π k w)‖)
    (fun l hl => h8e G s π hs hπ w hw l (hS l hl))
  set U : Set (Fin n → Fin n → ℂ) := {k | ∀ i j, ‖k i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ < δ} with hU
  have hUo : IsOpen U := by
    rw [hU]
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_lt (by fun_prop) continuous_const
  have hU1 : U ∈ 𝓝 (Matrix.of.symm (1 : Matrix (Fin n) (Fin n) ℂ)) := by
    refine hUo.mem_nhds fun i j => ?_
    simpa using hδ
  set η : ℝ := ε / (4 * (B + 1)) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨q, hqi, hq1, hqn, hqU⟩ := h8b G s hs μ hμ U hU1 η hη0
  have hec : Continuous (evP q) := continuous_evP q
  obtain ⟨hsm, hfold⟩ := h8c G s π hs hπ μ hμ (evP q) hec w hw
  refine ⟨∫ k, evP q k • π (Matrix.of k) w ∂μ, hsm, h8d G s π hs hπ μ hμ q w, fun l hl => ?_⟩
  obtain ⟨hint, hcomm⟩ := hfold l (hS l hl)
  have hw1 : dL π l w = ∫ k, evP q k • dL π l w ∂μ := by
    rw [integral_smul_const, hq1, one_smul]
  rw [hcomm, hw1, ← integral_sub hint (hqi.smul_const _)]
  have hD : ∀ᵐ k ∂μ, ‖evP q k • dL π l (π (Matrix.of k) w) - evP q k • dL π l w‖ ≤
      ‖evP q k‖ * (ε / 2) + Uᶜ.indicator (fun k => ‖evP q k‖ * (2 * B)) k := by
    filter_upwards [hae] with k hk
    rw [← smul_sub, norm_smul]
    by_cases hkU : k ∈ U
    · rw [Set.indicator_of_notMem (Set.notMem_compl_iff.2 hkU), add_zero]
      have hlt : ‖dL π l (π (Matrix.of k) w) - dL π l w‖ < ε / 2 :=
        hδS l hl δ hδ le_rfl (Matrix.of k) hk.1 hkU
      exact mul_le_mul_of_nonneg_left hlt.le (norm_nonneg _)
    · rw [Set.indicator_of_mem hkU]
      have h1 : ‖dL π l (π (Matrix.of k) w)‖ ≤ B := hB l hl (Matrix.of k) hk
      have h2 : ‖dL π l w‖ ≤ B := by
        have h := hB l hl 1 (one_mem_KAt G s)
        simp only [hπ1, one_apply_eq_self] at h
        exact h
      have h3 : ‖dL π l (π (Matrix.of k) w) - dL π l w‖ ≤ 2 * B := by
        calc _ ≤ ‖dL π l (π (Matrix.of k) w)‖ + ‖dL π l w‖ := norm_sub_le _ _
          _ ≤ 2 * B := by linarith
      have h4 : 0 ≤ ‖evP q k‖ * (ε / 2) := by positivity
      calc ‖evP q k‖ * ‖dL π l (π (Matrix.of k) w) - dL π l w‖ ≤ ‖evP q k‖ * (2 * B) :=
            mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
        _ ≤ _ := by linarith
  have hmeasU : MeasurableSet Uᶜ := hUo.measurableSet.compl
  have hA : Integrable (fun k => ‖evP q k‖ * (ε / 2)) μ := hqi.norm.mul_const _
  have hC : Integrable (Uᶜ.indicator (fun k => ‖evP q k‖ * (2 * B))) μ :=
    (hqi.norm.mul_const _).indicator hmeasU
  have hsub : Integrable (fun k => evP q k • dL π l (π (Matrix.of k) w) - evP q k • dL π l w) μ :=
    hint.sub (hqi.smul_const _)
  have hηB : η * (2 * B) < ε / 2 := by
    rw [hη, div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  calc ‖∫ k, (evP q k • dL π l (π (Matrix.of k) w) - evP q k • dL π l w) ∂μ‖
      ≤ ∫ k, ‖evP q k • dL π l (π (Matrix.of k) w) - evP q k • dL π l w‖ ∂μ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ k, (‖evP q k‖ * (ε / 2) + Uᶜ.indicator (fun k => ‖evP q k‖ * (2 * B)) k) ∂μ :=
        integral_mono_ae hsub.norm (hA.add hC) hD
    _ = (∫ k, ‖evP q k‖ ∂μ) * (ε / 2) + (∫ k in Uᶜ, ‖evP q k‖ ∂μ) * (2 * B) := by
        rw [integral_add hA hC, integral_indicator hmeasU, integral_mul_const, integral_mul_const]
    _ ≤ 1 * (ε / 2) + η * (2 * B) :=
        add_le_add (mul_le_mul_of_nonneg_right hqn hε2.le)
          (mul_le_mul_of_nonneg_right hqU.le (by linarith))
    _ < ε := by linarith

end Formalism.IndefR.Tow.SobPf

end
end
