module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.WeightedA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Weighted

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.WeightedB
noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool}

theorem wd_rreg_adj (g : Formalism.REAL.UJ ε) (a b : L2 ε) :
    inner ℂ (rreg ε (Formalism.MainNotions.S.umat g) a) b = inner ℂ a (rreg ε (Formalism.MainNotions.S.umat g⁻¹) b) := by
  have hinv : rreg ε (Formalism.MainNotions.S.umat g) (rreg ε (Formalism.MainNotions.S.umat g⁻¹) b) = b := by
    rw [← ContinuousLinearMap.comp_apply, ← (rreg_isURepOn ε).1.2 _ g.2 _ (g⁻¹).2]
    show rreg ε (Formalism.MainNotions.S.umat (g * g⁻¹)) b = b
    rw [mul_inv_cancel, show Formalism.MainNotions.S.umat (1 : Formalism.REAL.UJ ε) = 1 from rfl, (rreg_isURepOn ε).1.1]
    rfl
  let Lk : L2 ε →ₗᵢ[ℂ] L2 ε :=
    ⟨(rreg ε (Formalism.MainNotions.S.umat g)).toLinearMap, fun z => (rreg_isURepOn ε).2.1 _ g.2 z⟩
  conv_lhs => rw [← hinv]
  exact Lk.inner_map_map a _

theorem wd_hs_inv (g : Formalism.REAL.UJ ε) : S7.hs (Formalism.MainNotions.S.umat g⁻¹) = S7.hs (Formalism.MainNotions.S.umat g) := by
  rw [arb_umat_inv, arbSharp_apply]
  unfold S7.hs Formalism.REAL.Jm
  have e : ∀ i j, ‖(Matrix.diagonal (fun a => if ε a = true then (1 : ℂ) else -1) * (Formalism.MainNotions.S.umat g)ᴴ *
      Matrix.diagonal (fun a => if ε a = true then (1 : ℂ) else -1)) i j‖ = ‖Formalism.MainNotions.S.umat g j i‖ := by
    intro i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, norm_mul, norm_mul, norm_star]
    have h1 : ∀ a, ‖(if ε a = true then (1 : ℂ) else -1)‖ = 1 := fun a => by split_ifs <;> simp
    rw [h1, h1, one_mul, mul_one]
  simp only [e]
  exact Finset.sum_comm

theorem wdF_add (f f' : Matrix (Fin n) (Fin n) ℂ → ℂ) : wdF ε (f + f') = wdF ε f + wdF ε f' := by
  funext g; simp [wdF, mul_add]

theorem wdF_smul (c : ℂ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) : wdF ε (c • f) = c • wdF ε f := by
  funext g; simp only [wdF, Pi.smul_apply, smul_eq_mul]; ring

theorem wdF_zero : wdF ε (0 : Matrix (Fin n) (Fin n) ℂ → ℂ) = 0 := by
  funext g; simp [wdF]

variable {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}
  {v₀ : T.V}

theorem wd_key (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) (i : Fin n) (w : L2 ε)
    (hw : ∀ x ∈ datumV ε Ψ v₀, MemLp (wdF ε (wdCoef ε w x)) 2 (Formalism.REAL.muG ε)) :
    ∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), MemLp (wdF ε (wdCoef ε w v)) 2 (Formalism.REAL.muG ε) := _root_.ReciprocityTheory.ChartRestriction.DS.G2.wd_key hP hv₀ i w hw

theorem wd_psi_memLp (hP : IsPsiFor ε lam T Ψ)
    (hΨw : ∀ μ : Measure (S7.UJ ε), μ.IsHaarMeasure →
      Integrable (fun g : S7.UJ ε => ‖Ψ (S7.toM g)‖ ^ 2 * S7.hs (S7.toM g) ^ ((2 : ℝ) / 2)) μ) :
    MemLp (wdF ε (fun g => ((‖Ψ g‖ : ℝ) : ℂ))) 2 (Formalism.REAL.muG ε) := by
  have hI := integrable_muG_of_haar ε (fun g => ‖Ψ g‖ ^ 2 * S7.hs g ^ ((2 : ℝ) / 2)) hΨw
  have hΨm : AEStronglyMeasurable (fun g : Formalism.REAL.UJ ε => Ψ (Formalism.MainNotions.S.umat g)) (Formalism.REAL.muG ε) :=
    ((ffa_continuousOn hP.2.2.1).comp_continuous (continuous_umatA ε) (fun g => g.2)).aestronglyMeasurable
  have hm : AEStronglyMeasurable (wdF ε (fun g => ((‖Ψ g‖ : ℝ) : ℂ))) (Formalism.REAL.muG ε) := by
    unfold wdF
    exact ((Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
      (wd_hs_cont.comp (continuous_umatA ε)))).aestronglyMeasurable).mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hΨm.norm)
  rw [memLp_two_iff_integrable_sq_norm hm]
  refine hI.congr (Filter.Eventually.of_forall fun g => ?_)
  simp only
  rw [wd_norm_sq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one, mul_comm]

theorem wd_datum_datum (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (hΨw : ∀ μ : Measure (S7.UJ ε), μ.IsHaarMeasure →
      Integrable (fun g : S7.UJ ε => ‖Ψ (S7.toM g)‖ ^ 2 * S7.hs (S7.toM g) ^ ((2 : ℝ) / 2)) μ)
    (x' : smD ε (rreg ε)) (hx' : x' ∈ datumV ε Ψ v₀) (x : smD ε (rreg ε)) (hx : x ∈ datumV ε Ψ v₀) :
    MemLp (wdF ε (wdCoef ε (x' : L2 ε) x)) 2 (Formalism.REAL.muG ε) := by
  obtain ⟨u', hu'⟩ := (mem_datumV_iff hP v₀ x').1 hx'
  obtain ⟨u, hu⟩ := (mem_datumV_iff hP v₀ x).1 hx
  have hG := wd_psi_memLp hP hΨw
  have hm : AEStronglyMeasurable (wdF ε (wdCoef ε (x' : L2 ε) x)) (Formalism.REAL.muG ε) := by
    unfold wdF
    exact ((Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
      (wd_hs_cont.comp (continuous_umatA ε)))).mul (wdCoef_cont _ _)).aestronglyMeasurable
  refine hG.of_le_mul (c := ‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 * ‖u'‖ * ‖u‖) hm (Filter.Eventually.of_forall fun g => ?_)
  simp only [wdF, wdCoef_apply, hu', hu]
  have h3 : 0 ≤ ‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 := by positivity
  rw [formulaF hgap hP hv₀ g.2 u u']
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_norm, abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg h3]
  have h1 : ‖inner ℂ u' (Ψ (Formalism.MainNotions.S.umat g) u)‖ ≤ ‖u'‖ * (‖Ψ (Formalism.MainNotions.S.umat g)‖ * ‖u‖) :=
    (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ((Ψ _).le_opNorm u) (norm_nonneg _))
  have h2 : 0 ≤ Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) := Real.sqrt_nonneg _
  calc Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) * (‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 * ‖inner ℂ u' (Ψ (Formalism.MainNotions.S.umat g) u)‖)
      ≤ Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) * (‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 * (‖u'‖ * (‖Ψ (Formalism.MainNotions.S.umat g)‖ * ‖u‖))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 h3) h2
    _ = _ := by ring

theorem wd_gen_datum (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (hΨw : ∀ μ : Measure (S7.UJ ε), μ.IsHaarMeasure →
      Integrable (fun g : S7.UJ ε => ‖Ψ (S7.toM g)‖ ^ 2 * S7.hs (S7.toM g) ^ ((2 : ℝ) / 2)) μ)
    (i : Fin n) (w : smD ε (rreg ε)) (hw : w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀))
    (x : smD ε (rreg ε)) (hx : x ∈ datumV ε Ψ v₀) :
    MemLp (wdF ε (wdCoef ε (w : L2 ε) x)) 2 (Formalism.REAL.muG ε) := by
  have h := wd_key hP hv₀ i (x : L2 ε) (fun y hy => wd_datum_datum hgap hP hv₀ hΨw x hx y hy) w hw
  have hinv := (h.comp_measurePreserving (Measure.measurePreserving_inv (Formalism.REAL.muG ε))).star
  have e : star (wdF ε (wdCoef ε (x : L2 ε) w) ∘ Inv.inv) = wdF ε (wdCoef ε (w : L2 ε) x) := by
    funext g
    simp only [Pi.star_apply, Function.comp_apply, wdF, wdCoef_apply, star_mul', RCLike.star_def,
      Complex.conj_ofReal]
    rw [wd_hs_inv, inner_conj_symm, wd_rreg_adj, inv_inv]
  rw [e] at hinv
  exact hinv

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

open MeasureTheory

theorem weighted_datum {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V} (hgap : StdGap ε lam)
    (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (hΨw : ∀ μ : Measure (S7.UJ ε), μ.IsHaarMeasure →
      Integrable (fun g : S7.UJ ε => ‖Ψ (S7.toM g)‖ ^ 2 * S7.hs (S7.toM g) ^ ((2 : ℝ) / 2)) μ) :
    ∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      MemLp (fun g : Formalism.REAL.UJ ε =>
        ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
          inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε)))
        2 (Formalism.REAL.muG ε) := by
  intro v hv w hw
  show MemLp (wdF ε (wdCoef ε ((w : smD ε (rreg ε)) : L2 ε) v)) 2 (Formalism.REAL.muG ε)
  rcases isEmpty_or_nonempty (Fin n) with hn | hne
  · have e : wdF ε (wdCoef ε ((w : smD ε (rreg ε)) : L2 ε) v) = 0 := by
      funext g
      simp [wdF, S7.hs]
    rw [e]
    exact MemLp.zero
  · obtain ⟨i⟩ := hne
    exact wd_key hP hv₀ i (w : L2 ε) (fun x hx => wd_gen_datum hgap hP hv₀ hΨw i w hw x hx) v hv

end ReciprocityTheory.ChartRestriction.DS
