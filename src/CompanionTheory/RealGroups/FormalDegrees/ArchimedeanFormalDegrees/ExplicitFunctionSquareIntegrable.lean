module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.FormalDegreeG2.FdCons
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.CoverExistsOf
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.HcFormalDegreeOfDiscreteSeriesFormalDegree
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureThird
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNonnegTestFunctionNearOne
public import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.FormalDegreeFormula.CoefPow

@[expose] public section

section -- merged from CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.DegreeNormalization.DegPsi
noncomputable section

open Finset MeasureTheory Matrix
open scoped InnerProductSpace

namespace CompanionTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS

theorem degPsi : DegPsi := by
  intro n ε V _ _ _ Ψ H _ _ σ j C d m hC hj hΨ hd
  set b := stdOrthonormalBasis ℂ V with hb
  obtain ⟨hd0, hS⟩ := hd
  have hb1 : ∀ i, ⟪b i, b i⟫_ℂ = 1 := fun i => by
    rw [inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]; simp
  have key : ∀ i l, Integrable (fun g : Formalism.REAL.UJ ε => ‖⟪b l, Ψ (Formalism.MainNotions.S.umat g) (b i)⟫_ℂ‖ ^ 2) m ∧
      ∫ g, ‖⟪b l, Ψ (Formalism.MainNotions.S.umat g) (b i)⟫_ℂ‖ ^ 2 ∂m = 1 / d := by
    intro i l
    obtain ⟨hi, he⟩ := hS (j (b i)) (j (b l)) (j (b i)) (j (b l))
    have hpt : ∀ g : Formalism.REAL.UJ ε, Formalism.MainNotions.S.coefOn σ (j (b i)) (j (b l)) g * star (Formalism.MainNotions.S.coefOn σ (j (b i)) (j (b l)) g) =
        ((C ^ 2 * ‖⟪b l, Ψ (Formalism.MainNotions.S.umat g) (b i)⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
      intro g
      rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      simp only [Formalism.MainNotions.S.coefOn]
      rw [hΨ g (b i) (b l), norm_mul, Complex.norm_real, Real.norm_of_nonneg hC.le]
      push_cast; ring
    simp_rw [hpt] at hi he
    rw [integral_complex_ofReal, hj, hj, hb1, hb1] at he
    have he' : ∫ g, C ^ 2 * ‖⟪b l, Ψ (Formalism.MainNotions.S.umat g) (b i)⟫_ℂ‖ ^ 2 ∂m = C * C / d := by
      apply Complex.ofReal_injective
      rw [he]; push_cast; ring
    have hi' : Integrable (fun g : Formalism.REAL.UJ ε => C ^ 2 * ‖⟪b l, Ψ (Formalism.MainNotions.S.umat g) (b i)⟫_ℂ‖ ^ 2) m := by
      refine hi.re.congr (ae_of_all _ fun g => ?_)
      simp only
      exact RCLike.ofReal_re _
    have hC2 : C ^ 2 ≠ 0 := pow_ne_zero 2 hC.ne'
    refine ⟨?_, ?_⟩
    · refine (hi'.const_mul (C ^ 2)⁻¹).congr (ae_of_all _ fun g => ?_)
      simp only
      field_simp
    · rw [integral_const_mul] at he'
      have hd' : d ≠ 0 := hd0.ne'
      field_simp at he' ⊢
      nlinarith [he']
  have hexp : ∀ g : Formalism.REAL.UJ ε, hsOp (Ψ (Formalism.MainNotions.S.umat g)) =
      ∑ i, ∑ l, ‖⟪b l, Ψ (Formalism.MainNotions.S.umat g) (b i)⟫_ℂ‖ ^ 2 := by
    intro g
    unfold hsOp
    exact sum_congr rfl fun i _ => (b.sum_sq_norm_inner_right _).symm
  have hint : Integrable (fun g : Formalism.REAL.UJ ε => hsOp (Ψ (Formalism.MainNotions.S.umat g))) m := by
    simp_rw [hexp]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun l _ => (key i l).1
  have hval : ∫ g, hsOp (Ψ (Formalism.MainNotions.S.umat g)) ∂m = (Module.finrank ℂ V : ℝ) ^ 2 / d := by
    simp_rw [hexp]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun l _ => (key i l).1)]
    rw [sum_congr rfl fun i _ => integral_finsetSum _ fun l _ => (key i l).1]
    rw [sum_congr rfl fun i _ => sum_congr rfl fun l _ => (key i l).2]
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun g => by unfold hsOp; positivity), hval]

end CompanionTheory.RgFd
end
end

section -- merged from CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.PositiveConjugation.PhiMul
noncomputable section

open Finset Matrix
open scoped ComplexOrder

namespace CompanionTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem posDef_conj_toMK {ε : Fin n → Bool} (k : KG ε) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) :
    (toMK k⁻¹ * x * toMK k).PosDef := by
  rw [toMK_inv]
  refine hx.conjTranspose_mul_mul_same ?_
  intro a b hab
  have h := congrArg (fun y => (toMK k)ᴴ.mulVec y) hab
  simpa only [Matrix.mulVec_mulVec, (toMK_facts k).1, Matrix.one_mulVec] using h

theorem muNext_add_smul (μ D : Fin n → ℤ) (t : ℤ) (i : Fin n) :
    muNext (μ + t • D) i = muNext μ i + t * muNext D i := by
  unfold muNext
  split_ifs <;> simp

theorem phiM_add_smul (μ D : Fin n → ℤ) (t : ℕ) {y : Matrix (Fin n) (Fin n) ℂ} (hy : y ∈ OmegaSet n) :
    PhiM (μ + (t : ℤ) • D) y = PhiM μ y * PhiM D y ^ t := by
  unfold PhiM
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h0 : lead ((i : ℕ) + 1) y ≠ 0 := hy i
  rw [muNext_add_smul, ← zpow_natCast, ← _root_.zpow_mul, ← zpow_add₀ h0]
  congr 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem phiMul : PhiMul := by
  intro n ε μ t x hx k
  have hy := posDef_conj_toMK k hx
  have h1 := phiM_posDef μ hy
  have h2 := phiM_posDef (Dz n) hy
  refine ⟨h1.1, ?_⟩
  unfold phiK
  rw [phiM_add_smul μ (Dz n) t (posSet_subset_omega hy)]
  have e1 : PhiM μ (toMK k⁻¹ * x * toMK k) = ((PhiM μ (toMK k⁻¹ * x * toMK k)).re : ℂ) :=
    Complex.ext (by simp) (by simp [h1.2])
  have e2 : PhiM (Dz n) (toMK k⁻¹ * x * toMK k) = ((PhiM (Dz n) (toMK k⁻¹ * x * toMK k)).re : ℂ) :=
    Complex.ext (by simp) (by simp [h2.2])
  rw [e1, e2, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
  simp only [Complex.ofReal_re]

end CompanionTheory.RgFd
end
end

section -- merged from CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.DegreeNormalization.GapNorm
noncomputable section

open Finset MeasureTheory Matrix
open scoped InnerProductSpace

namespace CompanionTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

theorem gapNorm_of (hD : DegPsi) : GapNorm := by
  intro n ε hp hq
  refine ⟨G2.thrS ε + 2, fun lam hlam hgap T μ hμ => ?_⟩
  have hh : G2.thrS ε + 1 < G2.thrS ε + 2 := by linarith
  have hq0 := G2.one_le_q0_of_p_q_pos hp hq
  have h8 := G2.fdc_eight hh
  have hP : IsPsiFor ε lam T (PsiM T μ) := (S7.isPsiFor_psiM ε lam _ T μ hlam hμ hgap hq0 h8).1
  have hgap' := G2.fdc_stdGap hlam hgap hh
  have hw := G2.fdc_w_ne T
  have hDS := G2.isDS_sigLam hgap' hP hw
  have : CompleteSpace (Hlam ε (PsiM T μ) T.w) := hDS.1
  have : Nontrivial (Hlam ε (PsiM T μ) T.w) := hDS.2.1
  obtain ⟨d, hd⟩ := G2.fdcGood_of_isDS hDS
  obtain ⟨x, hx⟩ := exists_ne (0 : Hlam ε (PsiM T μ) T.w)
  have hΨ : ∀ μ' : Fin n → ℝ, IsHCParam μ' → GapAtLeast ε μ' (G2.thrS ε + 2) →
      ∃ (T' : KType ε (lowK ε μ')) (Ψ : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)), IsPsiFor ε μ' T' Ψ := by
    intro μ' hμ' hg'
    obtain ⟨T'⟩ := HW.kType_exists ε μ' hμ'
    obtain ⟨m', -, hP'⟩ := G2.fdc_model hp hq hμ' hg' hh T'
    exact ⟨T', _, hP'⟩
  have hdeg := G2.fdCons_cd hp hq hlam hgap hh hΨ hDS hx
  rw [fdegOf_of_isFdeg' hd hx] at hdeg
  subst hdeg
  set C : ℝ := ‖uniformisationL2 ε (PsiM T μ) T.w T.w‖ ^ 2 with hC
  have hC0 : 0 < C := by
    have := G2.datumEmbedding_highest_ne_zero hgap' hP hw
    positivity
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := umat_mem_UJset ε 1
  refine hD n ε T.V (PsiM T μ) (Hlam ε (PsiM T μ) T.w) (sigLam ε (PsiM T μ) T.w)
    (fun v => ⟨uniformisationL2 ε (PsiM T μ) T.w v, datumEmbedding_mem_Hlam hP v⟩) C (dimVlam lam) (muCD ε) hC0 (fun v v' => ?_) (fun g v v' => ?_) hd
  · have e := G2.formulaF_sigLam hgap' hP hw h1 v v'
    rw [hP.2.1] at e
    simp only [ContinuousLinearMap.one_apply] at e
    rw [← e, (G2.sigLam_isURepOn hgap' hP hw).1.1]
    rfl
  · exact G2.formulaF_sigLam hgap' hP hw (umat_mem_UJset ε g) v v'

end CompanionTheory.RgFd
end
end

section -- merged from CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.FormalDegreeFormula.CKContinuous
noncomputable section

open Finset MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace CompanionTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.HW

variable {n : ℕ}

theorem cK_continuous {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) : Continuous (cK T) :=
  (continuous_const.inner ((CompactHaarProbability.cont_op T).clm_apply continuous_const)).norm

theorem op_norm {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k : KG ε) (v : T.V) : ‖T.op k v‖ = ‖v‖ := by
  have h : T.op k⁻¹ * T.op k = 1 := CompactHaarProbability.op_inv_mul T k
  have hs : star (T.op k) * T.op k = 1 := Unitary.star_mul_self_of_mem (T.τ k).prop
  have h2 : ‖T.op k v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [← @inner_self_eq_norm_sq ℂ, ← @inner_self_eq_norm_sq ℂ]
    congr 1
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
      ← ContinuousLinearMap.mul_apply, hs, ContinuousLinearMap.one_apply]
  have := h
  nlinarith [norm_nonneg (T.op k v), norm_nonneg v, sq_nonneg (‖T.op k v‖ - ‖v‖), sq_nonneg (‖T.op k v‖ + ‖v‖)]

theorem cK_le_one {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k : KG ε) : cK T k ≤ 1 := by
  unfold cK
  calc ‖⟪T.w, T.op k T.w⟫_ℂ‖ ≤ ‖T.w‖ * ‖T.op k T.w‖ := norm_inner_le_norm _ _
    _ = 1 := by rw [op_norm, T.w_norm, one_mul]

abbrev CPair (ε : Fin n → Bool) : Type := {p : Fin n × Fin n // p.1 < p.2 ∧ ε p.1 = ε p.2}

theorem prod_cpair (ε : Fin n → Bool) (f : Fin n → Fin n → ℝ) :
    ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b ∧ ε a = ε b), f a b = ∏ p : CPair ε, f p.1.1 p.1.2 := by
  have e1 : ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b ∧ ε a = ε b), f a b =
      ∏ x ∈ univ.filter (fun x : Fin n × Fin n => x.1 < x.2 ∧ ε x.1 = ε x.2), f x.1 x.2 := by
    rw [Finset.prod_filter, Fintype.prod_prod_type]
    simp_rw [Finset.prod_filter]
  rw [e1, ← Finset.prod_subtype (univ.filter (fun x : Fin n × Fin n => x.1 < x.2 ∧ ε x.1 = ε x.2))
    (fun x => by simp) (fun x : Fin n × Fin n => f x.1 x.2)]

theorem kNull_of (hW : MomW) (hP : CoefPow) : KNull := by
  intro n ε lam hl T TD
  classical
  haveI : CompactSpace (KG ε) := compactSpace_KG ε
  set F : ℝ := (∏ i ∈ range (pOf ε), (i.factorial : ℝ)) * ∏ i ∈ range (qOf ε), (i.factorial : ℝ) with hF
  have hFpos : 0 < F := by positivity
  let α : CPair ε → ℝ := fun p => lam p.1.1 - lam p.1.2 + (nab ε p.1.1 p.1.2 : ℝ)
  let β : CPair ε → ℝ := fun p => ((p.1.2 : ℕ) : ℝ) - ((p.1.1 : ℕ) : ℝ)
  have hα : ∀ p, 0 < α p := fun p => by
    have := hl.1 p.2.1
    have : (0 : ℝ) ≤ nab ε p.1.1 p.1.2 := Nat.cast_nonneg _
    simp only [α]; linarith
  have hβ : ∀ p, 0 ≤ β p := fun p => by
    have : ((p.1.1 : ℕ) : ℝ) < ((p.1.2 : ℕ) : ℝ) := by exact_mod_cast p.2.1
    simp only [β]; linarith

  have hmom : ∀ t : ℕ, ∫⁻ k, ENNReal.ofReal (cK T k ^ 2) * ENNReal.ofReal ((cK TD k ^ 2) ^ t) ∂(dk ε) =
      ENNReal.ofReal (F / ∏ p, (α p + t * β p)) := by
    intro t
    obtain ⟨Tt⟩ := kType_exists ε (lamT lam t) (isHCParam_lamT hl t)
    have e : ∀ k, ENNReal.ofReal (cK T k ^ 2) * ENNReal.ofReal ((cK TD k ^ 2) ^ t) = ENNReal.ofReal (cK Tt k ^ 2) := by
      intro k
      rw [← ENNReal.ofReal_mul (sq_nonneg _), hP n ε lam hl T TD t Tt k]
      ring_nf
    simp_rw [e]
    have hint : Integrable (fun k => cK Tt k ^ 2) (dk ε) :=
      ((cK_continuous Tt).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun k => sq_nonneg _)]
    congr 1
    have hs := kschur_coef Tt Tt.w Tt.w
    rw [Tt.w_norm] at hs
    have h7 := lemma7 Tt
    have hd : (0 : ℝ) < Module.finrank ℂ Tt.V := by
      have : Nontrivial Tt.V := ⟨⟨Tt.w, 0, fun h => by have := Tt.w_norm; rw [h, norm_zero] at this; exact zero_ne_one this⟩⟩
      exact_mod_cast Module.finrank_pos
    have hI : ∫ k, cK Tt k ^ 2 ∂(dk ε) = (Module.finrank ℂ Tt.V : ℝ)⁻¹ := by
      unfold cK
      field_simp
      linarith
    rw [hI, h7, prod_cpair ε (fun a b => lamT lam t a - lamT lam t b + (nab ε a b : ℝ))]
    have e2 : ∀ p : CPair ε, lamT lam t p.1.1 - lamT lam t p.1.2 + (nab ε p.1.1 p.1.2 : ℝ) = α p + t * β p := by
      intro p
      simp only [lamT_apply, Dvec, α, β]
      ring
    simp_rw [e2]
    rw [inv_div]
  have h0 := hmom 0
  simp only [pow_zero, ENNReal.ofReal_one, mul_one, Nat.cast_zero, zero_mul, add_zero] at h0
  have hpos := hW (KG ε) (dk ε) (fun k => ENNReal.ofReal (cK T k ^ 2)) (fun k => cK TD k ^ 2) (CPair ε) α β F 0
    ((cK_continuous T).pow 2).measurable.ennreal_ofReal ((cK_continuous TD).pow 2).measurable
    (fun k => ⟨sq_nonneg _, by have h1 := cK_le_one TD k; have h2 : 0 ≤ cK TD k := norm_nonneg _; nlinarith⟩) hα hβ hFpos.le
    (fun t _ => hmom t)
  set s : Set (KG ε) := {k | 0 < cK TD k ^ 2} with hs
  have hsm : MeasurableSet s := measurableSet_lt measurable_const ((cK_continuous TD).pow 2).measurable
  have hsum := lintegral_add_compl (fun k => ENNReal.ofReal (cK T k ^ 2)) (μ := dk ε) hsm
  rw [hpos, h0] at hsum
  have hz : ∫⁻ k in sᶜ, ENNReal.ofReal (cK T k ^ 2) ∂(dk ε) = 0 := by
    have hne : ENNReal.ofReal (F / ∏ p, α p) ≠ ⊤ := ENNReal.ofReal_ne_top
    calc _ = ENNReal.ofReal (F / ∏ p, α p) + (∫⁻ k in sᶜ, ENNReal.ofReal (cK T k ^ 2) ∂(dk ε)) -
          ENNReal.ofReal (F / ∏ p, α p) := by rw [ENNReal.add_sub_cancel_left hne]
      _ = 0 := by rw [hsum, tsub_self]
  have hmeas : Measurable fun k => ENNReal.ofReal (cK T k ^ 2) := by
    exact ((cK_continuous T).pow 2).measurable.ennreal_ofReal
  replace hz := (lintegral_eq_zero_iff hmeas).1 hz
  rw [Filter.EventuallyEq, ae_restrict_iff' hsm.compl] at hz
  apply hz.mono
  intro k hk h0k
  have hk' := hk (by simp [hs, h0k])
  simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hk'
  nlinarith [sq_nonneg (cK T k), norm_nonneg (⟪T.w, T.op k T.w⟫_ℂ)]

end CompanionTheory.RgFd
end
end

section -- merged from CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.PositiveConjugation.PhiCont
noncomputable section

open Finset Matrix
open scoped ComplexOrder

namespace CompanionTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem continuous_pP (ε : Fin n → Bool) : Continuous fun g : UJ ε => pP (toM g) := by
  have h : Continuous fun g : UJ ε => PolarDecomposition.polar_L (toM g) :=
    (lcA_polarL_continuousOn ε).comp_continuous (continuous_toM ε) (fun g => g.2)
  exact continuous_matrix_exp_alt.comp h

theorem pP_posDef {ε : Fin n → Bool} (g : UJ ε) : (pP (toM g)).PosDef :=
  exp_noncompactPart_posDef (PolarDecomposition.polar_L_inP (ε := ε) g.2)

theorem phiCont : PhiCont := by
  intro n ε μ
  have hY : Continuous fun z : UJ ε × KG ε => toMK z.2⁻¹ * pP (toM z.1) * toMK z.2 :=
    ((Ps1.continuous_toMK_inv.comp continuous_snd).matrix_mul ((continuous_pP ε).comp continuous_fst)).matrix_mul
      (Ps1.continuous_toMK'.comp continuous_snd)
  refine continuous_iff_continuousAt.2 fun z => ?_
  have hpd := posDef_conj_toMK z.2 (pP_posDef z.1)
  have hΩ : toMK z.2⁻¹ * pP (toM z.1) * toMK z.2 ∈ OmegaSet n := posSet_subset_omega hpd
  have hc : ContinuousAt (PhiM μ) (toMK z.2⁻¹ * pP (toM z.1) * toMK z.2) :=
    ((phiM_differentiableOn μ).continuousOn).continuousAt (isOpen_omega.mem_nhds hΩ)
  show ContinuousAt (fun z : UJ ε × KG ε => (PhiM μ (toMK z.2⁻¹ * pP (toM z.1) * toMK z.2)).re) z
  exact Complex.continuous_re.continuousAt.comp
    (hc.comp (f := fun z : UJ ε × KG ε => toMK z.2⁻¹ * pP (toM z.1) * toMK z.2) hY.continuousAt)

end CompanionTheory.RgFd
end
end

section -- merged from CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.SignDefiniteness.ExplicitFunctionSquareIntegrable
noncomputable section

open Finset MeasureTheory Matrix
open scoped InnerProductSpace

namespace CompanionTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem pl_opNorm_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (A : V →L[ℂ] V) : ‖A‖ ^ 2 ≤ (Module.finrank ℂ V : ℝ) * hsOp A := by
  set b := stdOrthonormalBasis ℂ V
  have h1 : ‖A‖ ≤ ∑ i, ‖A (b i)‖ := by
    refine A.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun v => ?_
    conv_lhs => rw [← b.sum_repr' v]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [map_smul, norm_smul, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    calc ‖⟪b i, v⟫_ℂ‖ ≤ ‖b i‖ * ‖v‖ := norm_inner_le_norm _ _
      _ = ‖v‖ := by rw [b.orthonormal.1 i, one_mul]
  have h2 : (∑ i, ‖A (b i)‖) ^ 2 ≤ (Finset.univ.card : ℝ) * ∑ i, ‖A (b i)‖ ^ 2 := sq_sum_le_card_mul_sum_sq
  have hc : (Finset.univ : Finset (Fin (Module.finrank ℂ V))).card = Module.finrank ℂ V := by simp
  calc ‖A‖ ^ 2 ≤ (∑ i, ‖A (b i)‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := by rw [hc] at h2; exact h2

theorem square_integrable_of_norm : PsiNorm → CompanionTheory.RgDs.ExplicitFunctionSquareIntegrable := by
  intro hN n ε lam T μ hl hμ ν hν
  have hfin := hN n ε lam hl T μ hμ
  let f : UJ ε → (T.V →L[ℂ] T.V) := fun g => PsiM T μ (toM g)
  have hcont : Continuous f :=
    (psiM_continuousOn T μ hμ).comp_continuous (continuous_toM ε) (fun g => g.2)
  have hmCD : MemLp f 2 (muCD ε) := by
    refine (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).2 ⟨(hcont.norm.pow 2).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    have hle : ∀ g : Formalism.REAL.UJ ε, ‖‖f g‖ ^ 2‖ₑ ≤
        ENNReal.ofReal (Module.finrank ℂ T.V : ℝ) * ENNReal.ofReal (hsOp (PsiM T μ (Formalism.MainNotions.S.umat g))) := by
      intro g
      rw [← ENNReal.ofReal_mul (Nat.cast_nonneg _), Real.eNorm_eq_ofReal (by positivity)]
      exact ENNReal.ofReal_le_ofReal (pl_opNorm_le _)
    calc ∫⁻ g, ‖‖f g‖ ^ 2‖ₑ ∂(muCD ε) ≤ ∫⁻ g : Formalism.REAL.UJ ε, ENNReal.ofReal (Module.finrank ℂ T.V : ℝ) *
          ENNReal.ofReal (hsOp (PsiM T μ (Formalism.MainNotions.S.umat g))) ∂(muCD ε) := lintegral_mono hle
      _ = ENNReal.ofReal (Module.finrank ℂ T.V : ℝ) *
          ∫⁻ g : Formalism.REAL.UJ ε, ENNReal.ofReal (hsOp (PsiM T μ (Formalism.MainNotions.S.umat g))) ∂(muCD ε) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ < ⊤ := by rw [hfin]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  haveI hH : (show Measure (UJ ε) from muCD ε).IsHaarMeasure := muCD_isHaar ε
  have heq := Measure.isMulLeftInvariant_eq_smul ν (show Measure (UJ ε) from muCD ε)
  rw [heq]
  exact hmCD.smul_measure ENNReal.coe_ne_top

end CompanionTheory.RgFd
end
end

section -- merged from CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.SignDefiniteness.NormDef
noncomputable section

open Finset MeasureTheory Matrix
open scoped InnerProductSpace

namespace CompanionTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem nd_const_sign {ε : Fin n → Bool} (hq : q0 ε = 0) : ∃ s : Bool, ∀ a, ε a = s := by
  unfold q0 at hq
  rcases Nat.min_eq_zero_iff.1 hq with h | h
  · refine ⟨false, fun a => ?_⟩
    unfold pOf at h
    have := Finset.filter_eq_empty_iff.1 (Finset.card_eq_zero.1 h) (Finset.mem_univ a)
    simpa using this
  · refine ⟨true, fun a => ?_⟩
    unfold qOf at h
    have := Finset.filter_eq_empty_iff.1 (Finset.card_eq_zero.1 h) (Finset.mem_univ a)
    simpa using this

theorem nd_Jm {ε : Fin n → Bool} {s : Bool} (hs : ∀ a, ε a = s) :
    Jm ε = (if s then (1 : ℂ) else -1) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [Jm, hs]
  · simp [Jm, h]

theorem nd_mem_Kset {ε : Fin n → Bool} (hq : q0 ε = 0) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    g ∈ Kset ε := by
  obtain ⟨s, hs⟩ := nd_const_sign hq
  set c : ℂ := if s then 1 else -1 with hc
  have hc0 : c ≠ 0 := by simp only [hc]; split_ifs <;> norm_num
  have hJ := nd_Jm hs
  rw [← hc] at hJ
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  rw [hJ, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul] at hg'
  have hu : gᴴ * g = 1 := smul_right_injective _ hc0 hg'
  refine ⟨Matrix.mem_unitaryGroup_iff'.2 (by rw [star_eq_conjTranspose]; exact hu), ?_⟩
  rw [hJ, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

theorem nd_hsOp_op {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k : KG ε) :
    hsOp (T.op k) = (Module.finrank ℂ T.V : ℝ) := by
  have hn : ∀ v : T.V, ‖T.op k v‖ = ‖v‖ := by
    intro v
    have hU := (T.τ k).2
    have h1 : star (T.op k) * T.op k = 1 := hU.1
    have h2 : ⟪T.op k v, T.op k v⟫_ℂ = ⟪v, v⟫_ℂ := by
      rw [← ContinuousLinearMap.adjoint_inner_right, ← mul_apply_eq_comp,
        ← ContinuousLinearMap.star_eq_adjoint, h1, one_apply_eq_self]
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h2
    have h3 : ‖T.op k v‖ ^ 2 = ‖v‖ ^ 2 := by exact_mod_cast h2
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h3
  unfold hsOp
  simp only [hn, (stdOrthonormalBasis ℂ T.V).orthonormal.1, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

theorem nd_psiM_K {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (μ : Fin n → ℤ) (k : KG ε) :
    PsiM T μ (toMK k) = T.op k := by
  have h1 : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by simp [inUJ]
  have e := psiM_equiv T μ k 1 h1
  rw [show toMK (1 : KG ε) = 1 from rfl, Matrix.mul_one, Matrix.mul_one, psiM_one] at e
  rw [e]
  simp [KType.op, map_one]

theorem nd_pev_zero {ε : Fin n → Bool} {s : Bool} (hs : ∀ a, ε a = s) (z : PCoord ε → ℂ) : pev z = 0 := by
  have h0 : pmat z = 0 := by
    ext a b
    simp [pmat, hs]
  exact (pmat_isHermitian z).eigenvalues_eq_zero_iff.2 h0

theorem nd_jac_one {ε : Fin n → Bool} {s : Bool} (hs : ∀ a, ε a = s) (z : PCoord ε → ℂ) : Jac z = 1 := by
  unfold Jac
  refine Finset.prod_eq_one fun a _ => Finset.prod_eq_one fun b _ => ?_
  rw [nd_pev_zero hs z]
  simp [shc]

theorem nd_isEmpty {ε : Fin n → Bool} {s : Bool} (hs : ∀ a, ε a = s) : IsEmpty (PCoord ε) :=
  ⟨fun ab => ab.2.2 (by rw [hs, hs])⟩

theorem nd_counts {ε : Fin n → Bool} (hq : q0 ε = 0) :
    (pOf ε = n ∧ qOf ε = 0) ∨ (pOf ε = 0 ∧ qOf ε = n) := by
  obtain ⟨s, hs⟩ := nd_const_sign hq
  cases s
  · right
    refine ⟨?_, ?_⟩
    · unfold pOf; simp [hs]
    · unfold qOf; simp [hs]
  · left
    refine ⟨?_, ?_⟩
    · unfold pOf; simp [hs]
    · unfold qOf; simp [hs]

theorem nd_cPQ {ε : Fin n → Bool} (hq : q0 ε = 0) : cPQ ε = 1 := by
  unfold cPQ
  have hpos : 0 < ∏ i ∈ range n, (i.factorial : ℝ) :=
    Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i
  rcases nd_counts hq with ⟨hp, hq'⟩ | ⟨hp, hq'⟩ <;> rw [hp, hq'] <;> simp [hpos.ne']

theorem nd_muCD_univ {ε : Fin n → Bool} (hq : q0 ε = 0) : muCD ε Set.univ = 1 := by
  obtain ⟨s, hs⟩ := nd_const_sign hq
  have := nd_isEmpty hs
  have h := lintegral_muCD ε (fun _ => 1) measurable_const
  simp only [lintegral_one] at h
  rw [h, nd_cPQ hq, ENNReal.ofReal_one, one_mul]
  have hz : ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (Jac z) = 1 := by
    simp only [nd_jac_one hs, ENNReal.ofReal_one, lintegral_one]
    rw [MeasureTheory.volume_pi, Measure.pi_of_empty]
    simp
  simp only [one_mul, hz]
  rw [lintegral_one]
  exact (CompactHaarProbability.dk_isProb ε).measure_univ

theorem nd_finrank {ε : Fin n → Bool} (hq : q0 ε = 0) {lam : Fin n → ℝ} (hl : StrictAnti lam)
    (T : KType ε (lowK ε lam)) : (Module.finrank ℂ T.V : ℝ) = dimVlam lam := by
  obtain ⟨s, hs⟩ := nd_const_sign hq
  rw [lemma7 T, dimVlam, prod_pairs_eq_factorial]
  have hden : (∏ i ∈ range (pOf ε), (i.factorial : ℝ)) * ∏ i ∈ range (qOf ε), (i.factorial : ℝ) =
      ∏ i ∈ range n, (i.factorial : ℝ) := by
    rcases nd_counts hq with ⟨hp, hq'⟩ | ⟨hp, hq'⟩ <;> rw [hp, hq'] <;> simp
  rw [hden]
  congr 1
  refine Finset.prod_congr rfl fun a _ => ?_
  have hf : (univ.filter fun b : Fin n => a < b ∧ ε a = ε b) = univ.filter fun b : Fin n => a < b := by
    ext b; simp [hs]
  rw [hf]
  refine Finset.prod_congr rfl fun b hb => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
  have hn : nab ε a b = 0 := by
    unfold nab
    simp [hs]
  rw [hn, Nat.cast_zero, add_zero, abs_of_pos (sub_pos.2 (hl hb))]

theorem normDef : NormDef := by
  intro n ε hq lam hl T μ hμ
  have hK : ∀ g : Formalism.REAL.UJ ε, hsOp (PsiM T μ (Formalism.MainNotions.S.umat g)) = (Module.finrank ℂ T.V : ℝ) := by
    intro g
    have hg : inUJ ε (Formalism.MainNotions.S.umat g) := by
      have h := g.2
      unfold inUJ Jm
      exact h
    obtain ⟨u, hu⟩ := exists_toMK (nd_mem_Kset hq hg)
    rw [← hu, nd_psiM_K, nd_hsOp_op]
  simp only [hK, lintegral_const, nd_muCD_univ hq, mul_one]
  rw [← nd_finrank hq hl.1 T]
  congr 1
  have hpos : (0 : ℝ) < Module.finrank ℂ T.V := by
    have : Nontrivial T.V := ⟨⟨T.w, 0, fun h => by simpa [h] using T.w_norm⟩⟩
    exact_mod_cast Module.finrank_pos
  field_simp

end CompanionTheory.RgFd
end
end

section -- merged from CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.PositiveConjugation.HsOpOpMul
noncomputable section

open Finset Matrix

namespace CompanionTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem polar_pP {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    ∃ k : KG ε, g = toMK k * pP g := by
  obtain ⟨u, hu⟩ := exists_toMK (PolarDecomposition.polar_k_mem hg)
  refine ⟨u, ?_⟩
  rw [hu, pP, Matrix.mul_assoc, PolarDecomposition.polar_exp_neg_mul, Matrix.mul_one]

theorem hsOp_op_mul {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k : KG ε) (A : T.V →L[ℂ] T.V) :
    hsOp (T.op k * A) = hsOp A := by
  unfold hsOp
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.mul_apply, KType_norm_op_apply]

theorem hsPol : HsPol := by
  intro n ε g hg
  refine ⟨⟨PolarDecomposition.polar_L g, PolarDecomposition.polar_L_inP hg, rfl⟩, fun Λ T μ => ?_⟩
  obtain ⟨k, hk⟩ := polar_pP hg
  have hL := PolarDecomposition.polar_L_inP hg
  have hex : ∃ (k' : KG ε) (X' : Matrix (Fin n) (Fin n) ℂ), inP ε X' ∧ g = toMK k' * NormedSpace.exp X' :=
    ⟨k, PolarDecomposition.polar_L g, hL, hk⟩
  unfold PsiM
  rw [dite_eq_left hex]
  obtain ⟨hP, hEq⟩ := hex.choose_spec.choose_spec
  have hEq' : toMK k * NormedSpace.exp (PolarDecomposition.polar_L g) = toMK hex.choose * NormedSpace.exp hex.choose_spec.choose :=
    hk.symm.trans hEq
  obtain ⟨-, h2⟩ := polar_unique hL hP hEq'
  rw [hsOp_op_mul, ← h2]
  rfl

end CompanionTheory.RgFd
end
end

section -- merged from CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.PositiveConjugation.DzSubMuNextNonneg
noncomputable section

open Finset Matrix
open scoped ComplexOrder

namespace CompanionTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem inP_entry_zero {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) {a b : Fin n}
    (h : ε a = ε b) : X a b = 0 := by
  have h1 := congrFun (congrFun hX.2 a) b
  simp only [Matrix.mul_apply, Matrix.neg_apply, Jm, Matrix.diagonal_apply, mul_ite, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true] at h1
  rw [h] at h1
  split_ifs at h1 with hb
  · have : (2 : ℂ) * X a b = 0 := by linear_combination h1
    simpa using this
  · have : (2 : ℂ) * X a b = 0 := by linear_combination -h1
    simpa using this

theorem exists_pmat {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) :
    ∃ z : PCoord ε → ℂ, pmat z = X := by
  refine ⟨fun ab => X ab.1.1 ab.1.2, ?_⟩
  have hH := isHermitian_of_mem_noncompactPart' hX
  ext a b
  simp only [pmat]
  by_cases h1 : b < a ∧ ε a ≠ ε b
  · rw [dite_eq_left h1]
  · rw [dite_eq_right h1]
    by_cases h2 : a < b ∧ ε b ≠ ε a
    · rw [dite_eq_left h2]
      have := congrFun (congrFun hH a) b
      simp only [Matrix.conjTranspose_apply] at this
      exact this
    · rw [dite_eq_right h2]
      by_cases he : ε a = ε b
      · exact (inP_entry_zero hX he).symm
      · have hab : a = b := by
          by_contra hne
          rcases lt_or_gt_of_ne hne with h | h
          · exact h2 ⟨h, Ne.symm he⟩
          · exact h1 ⟨h, he⟩
        subst hab
        exact absurd rfl he

theorem one_le_lead_exp {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) (i : ℕ) (hi : i ≤ n) :
    1 ≤ (lead i (NormedSpace.exp X)).re := by
  obtain ⟨z, rfl⟩ := exists_pmat hX
  have h0 := fi_nonneg z i
  have hp := (lead_posDef (exp_noncompactPart_posDef hX) i hi).1
  unfold Fi at h0
  have e : Del (NormedSpace.exp (pmat z)) i = lead i (NormedSpace.exp (pmat z)) := rfl
  rw [e] at h0
  exact (Real.log_nonneg_iff hp).1 h0

theorem dz_sub_muNext_nonneg (i : Fin n) : 0 ≤ Dz n i - muNext (Dz n) i := by
  unfold muNext Dz
  split_ifs with h
  · simp only
    omega
  · have : (i : ℕ) + 1 = n := by omega
    omega

theorem phiLe : PhiLe := by
  intro n ε X hX k
  obtain ⟨hP, hE⟩ := inP_conj k⁻¹ hX
  rw [inv_inv] at hP hE
  unfold phiK
  rw [← hE]
  set Y := toMK k⁻¹ * X * toMK k with hY
  have hpd := exp_noncompactPart_posDef hP
  have hr : ∀ i : Fin n, lead ((i : ℕ) + 1) (NormedSpace.exp Y) = ((lead ((i : ℕ) + 1) (NormedSpace.exp Y)).re : ℂ) :=
    fun i => Complex.ext (by simp) (by simp [(lead_posDef hpd _ i.isLt).2])
  have hphi : PhiM (Dz n) (NormedSpace.exp Y) =
      ((∏ i : Fin n, (lead ((i : ℕ) + 1) (NormedSpace.exp Y)).re ^ (-(Dz n i - muNext (Dz n) i)) : ℝ) : ℂ) := by
    unfold PhiM
    rw [Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hr i, Complex.ofReal_zpow, Complex.ofReal_re]
  rw [hphi, Complex.ofReal_re]
  refine Finset.prod_le_one₀ (fun i _ => zpow_nonneg (zero_le_one.trans (one_le_lead_exp hP _ i.isLt)) _) fun i _ => ?_
  exact zpow_le_one_of_nonpos₀ (one_le_lead_exp hP _ i.isLt) (neg_nonpos.2 (dz_sub_muNext_nonneg i))

end CompanionTheory.RgFd
end
end

section -- merged from CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.MomentRecursion.MomStep
open MeasureTheory Set

namespace CompanionTheory.RgFd

theorem mom_step {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {ν : Measure Ω} {ν' : Measure Ω'} {V : Ω → ℝ}
    {V' : Ω' → ℝ} (hV : Measurable V) (hV' : Measurable V') (h0 : ∀ x, 0 ≤ V x ∧ V x ≤ 1) (h0' : ∀ y, 0 ≤ V' y ∧ V' y ≤ 1)
    (he : ∀ j : ℕ, 1 ≤ j → ∫⁻ x, ENNReal.ofReal (V x ^ j) ∂ν = ∫⁻ y, ENNReal.ofReal (V' y ^ j) ∂ν')
    (hf : ∀ j : ℕ, 1 ≤ j → ∫⁻ x, ENNReal.ofReal (V x ^ j) ∂ν ≠ ⊤) (M : ℕ) : ∀ j : ℕ, 1 ≤ j →
    ∫⁻ x, ENNReal.ofReal (V x ^ j * (1 - V x) ^ M) ∂ν = ∫⁻ y, ENNReal.ofReal (V' y ^ j * (1 - V' y) ^ M) ∂ν' := by
  have split : ∀ {A : Type} [MeasurableSpace A] (m : Measure A) (W : A → ℝ), Measurable W → (∀ x, 0 ≤ W x ∧ W x ≤ 1) →
      ∀ j M : ℕ, ∫⁻ x, ENNReal.ofReal (W x ^ j * (1 - W x) ^ M) ∂m =
        ∫⁻ x, ENNReal.ofReal (W x ^ j * (1 - W x) ^ (M + 1)) ∂m + ∫⁻ x, ENNReal.ofReal (W x ^ (j + 1) * (1 - W x) ^ M) ∂m := by
    intro A _ m W hW h j M
    rw [← lintegral_add_left (by fun_prop)]
    refine lintegral_congr fun x => ?_
    have a := (h x).1
    have b := sub_nonneg.2 (h x).2
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1; ring
  induction M with
  | zero => simpa using he
  | succ M ih =>
    intro j hj
    have fin : ∫⁻ x, ENNReal.ofReal (V x ^ (j + 1) * (1 - V x) ^ M) ∂ν ≠ ⊤ := by
      refine ne_top_of_le_ne_top (hf (j + 1) (by omega)) (lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_)
      have a := (h0 x).1
      exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (sub_nonneg.2 (h0 x).2) (by linarith))
    have e := ih j hj
    rw [split ν V hV h0 j M, split ν' V' hV' h0' j M, ← ih (j + 1) (by omega)] at e
    exact (ENNReal.add_left_inj fin).1 e

theorem mom_sum {A : Type} [MeasurableSpace A] (m : Measure A) {W : A → ℝ} (hW : Measurable W) (h : ∀ x, 0 ≤ W x ∧ W x ≤ 1) :
    m {x | 0 < W x} = ∑' M : ℕ, ∫⁻ x, ENNReal.ofReal (W x ^ 1 * (1 - W x) ^ M) ∂m := by
  rw [← lintegral_tsum fun M => (by fun_prop : Measurable fun x => ENNReal.ofReal (W x ^ 1 * (1 - W x) ^ M)).aemeasurable,
    ← lintegral_indicator_one (measurableSet_lt measurable_const hW)]
  refine lintegral_congr fun x => ?_
  have a := (h x).1
  have b := sub_nonneg.2 (h x).2
  by_cases hx : 0 < W x
  · have hs : HasSum (fun M : ℕ => W x ^ 1 * (1 - W x) ^ M) (W x ^ 1 * (1 - (1 - W x))⁻¹) :=
      (hasSum_geometric_of_lt_one b (by linarith)).mul_left _
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun M => by positivity) hs.summable, hs.tsum_eq,
      indicator_of_mem (show x ∈ {x | 0 < W x} from hx)]
    simp [mul_inv_cancel₀ hx.ne']
  · rw [indicator_of_notMem (show x ∉ {x | 0 < W x} from hx), show W x = 0 from le_antisymm (not_lt.1 hx) a]
    simp

theorem momA : MomA := by
  intro Ω Ω' _ _ ν ν' U U' t0 hU hU' h h' ht he hf
  have p : ∀ {A : Type} (W : A → ℝ), (∀ x, 0 ≤ W x ∧ W x ≤ 1) → {x | 0 < W x} = {x | 0 < W x ^ t0} := fun W h => by
    ext x
    show 0 < W x ↔ 0 < W x ^ t0
    exact ⟨fun a => pow_pos a _, fun a => (h x).1.lt_of_ne fun b => by
      rw [← b, zero_pow (by omega)] at a; exact lt_irrefl _ a⟩
  have q : ∀ {A : Type} (W : A → ℝ), (∀ x, 0 ≤ W x ∧ W x ≤ 1) → ∀ x, 0 ≤ W x ^ t0 ∧ W x ^ t0 ≤ 1 := fun W h x =>
    ⟨pow_nonneg (h x).1 _, pow_le_one₀ (h x).1 (h x).2⟩
  rw [p U h, p U' h', mom_sum ν (hU.pow_const t0) (q U h), mom_sum ν' (hU'.pow_const t0) (q U' h')]
  refine tsum_congr fun M => mom_step (hU.pow_const t0) (hU'.pow_const t0) (q U h) (q U' h') (fun j hj => ?_)
    (fun j hj => ?_) M 1 le_rfl
  · simpa only [← pow_mul, mul_comm t0] using he j hj
  · simpa only [← pow_mul, mul_comm t0] using hf j hj

theorem momB : MomB := by
  intro I _ α β c hα hβ hc
  refine ⟨(Measure.pi fun _ : I => (volume : Measure ℝ).restrict (Ioi 0)).withDensity
    fun y => ENNReal.ofReal (c * ∏ i, Real.exp (-α i * |y i|)), fun y => ∏ i, Real.exp (-β i * |y i|), by fun_prop,
    fun y => ⟨Finset.prod_pos fun i _ => Real.exp_pos _, Finset.prod_le_one₀ (fun i _ => (Real.exp_pos _).le) fun i _ =>
      Real.exp_le_one_iff.2 (by have := hβ i; have := abs_nonneg (y i); nlinarith)⟩, fun t => ?_⟩
  have hp : ∀ i, 0 < α i + t * β i := fun i => by have := hα i; have := hβ i; positivity
  have e1 : ∀ i, EqOn (fun x : ℝ => Real.exp (-(α i + t * β i) * |x|)) (fun x => Real.exp (-(α i + t * β i) * x)) (Ioi 0) :=
    fun i x hx => by simp only [abs_of_pos (show (0 : ℝ) < x from hx)]
  have hi : ∀ i, Integrable (fun x : ℝ => Real.exp (-(α i + t * β i) * |x|)) (volume.restrict (Ioi 0)) := fun i =>
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos (hp i)) 0).congr_fun (e1 i).symm measurableSet_Ioi
  have hv : ∀ i, ∫ x in Ioi (0 : ℝ), Real.exp (-(α i + t * β i) * |x|) = (α i + t * β i)⁻¹ := fun i => by
    rw [setIntegral_congr_fun measurableSet_Ioi (e1 i), integral_exp_mul_Ioi (neg_neg_of_pos (hp i))]
    rw [mul_zero, Real.exp_zero, neg_div_neg_eq, one_div]
  rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  have e2 : ∀ y : I → ℝ, ((fun y : I → ℝ => ENNReal.ofReal (c * ∏ i, Real.exp (-α i * |y i|))) *
      fun y : I → ℝ => ENNReal.ofReal ((∏ i, Real.exp (-β i * |y i|)) ^ t)) y =
      ENNReal.ofReal (c * ∏ i, Real.exp (-(α i + t * β i) * |y i|)) := fun y => by
    rw [Pi.mul_apply, ← ENNReal.ofReal_mul (by positivity), mul_assoc, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    congr 2
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  rw [lintegral_congr e2, ← ofReal_integral_eq_lintegral_ofReal ((Integrable.fintype_prod hi).const_mul c)
    (.of_forall fun y => by positivity), integral_const_mul,
    integral_fintype_prod_eq_prod (f := fun i (x : ℝ) => Real.exp (-(α i + t * β i) * |x|))]
  simp only [hv, Finset.prod_inv_distrib, div_eq_mul_inv]

theorem momW_of : MomA → MomB → MomW := by
  intro hA hB Ω _ P h U I _ α β c t0 hh hU h01 hα hβ hc hm
  obtain ⟨ν', U', m', p', e'⟩ := hB I α β c hα hβ hc
  have e : ∀ j : ℕ, 1 ≤ j → ∫⁻ x, ENNReal.ofReal (U x ^ (j * (t0 + 1))) ∂(P.withDensity h) =
      ENNReal.ofReal (c / ∏ i, (α i + (j * (t0 + 1) : ℕ) * β i)) := fun j hj => by
    rw [lintegral_withDensity_eq_lintegral_mul _ hh (by fun_prop)]
    exact hm _ (by nlinarith)
  have r := hA Ω _ (P.withDensity h) ν' U U' (t0 + 1) hU m' h01 (fun y => ⟨(p' y).1.le, (p' y).2⟩) (by omega)
    (fun j hj => (e j hj).trans (e' _).symm) fun j hj => by rw [e j hj]; exact ENNReal.ofReal_ne_top
  rw [withDensity_apply _ (measurableSet_lt measurable_const hU)] at r
  rw [r, show {y | 0 < U' y} = univ from eq_univ_of_forall fun y => (p' y).1]
  simpa using e' 0

theorem momW : MomW := momW_of momA momB

end CompanionTheory.RgFd
end

section -- merged from CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.NormIndOfSteps
noncomputable section

namespace CompanionTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS CompanionTheory.RgDs

theorem hsInt : HsInt := GlobalTheory.CompanionTheory.RgFd.hsInt GlobalTheory.CompanionTheory.HsPsProof.hsPs hsPol phiMul phiCont

theorem psiNorm_of (hI : NormInd) : PsiNorm := by
  intro n ε lam hl
  by_cases h : S7.q0 ε = 0
  · exact normDef n ε h lam hl
  · have h1 : 1 ≤ min (pOf ε) (qOf ε) := Nat.one_le_iff_ne_zero.2 h
    exact hI n ε (h1.trans (min_le_left _ _)) (h1.trans (min_le_right _ _)) lam hl

theorem normInd_of_steps (hP : CoefPow)
    (h : MomW → CoefPow → KNull → HsPol → PhiMul → PhiLe → PhiCont → HsInt → GapNorm → NormInd) : NormInd :=
  h momW hP (kNull_of momW hP) hsPol phiMul phiLe phiCont hsInt (gapNorm_of degPsi)

end CompanionTheory.RgFd
end
end

namespace CompanionTheory.RgFd

open CompanionTheory.RgDs

theorem psiNorm : PsiNorm := psiNorm_of (normInd_of_steps coefPow GlobalTheory.CompanionTheory.RgFdNorm.norm_induction_of_estimates)

theorem explicit_function_square_integrable : ExplicitFunctionSquareIntegrable := square_integrable_of_norm psiNorm

end CompanionTheory.RgFd
