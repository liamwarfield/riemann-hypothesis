module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HasSumSectionValueArcFramedPoint
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolArcEqFlowOrbit
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AbelianPartSectionNormSqEqThetaData
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HermFormSumSmul
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReadingLinearIndependentAndInjective
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaL2FamilyUniformCompare
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FreqRealNonnegIntegral
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantArcEigenbasisFlatBaseChange

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFrBor
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open Formalism.L2.Pj hiding Unf GoodEmb relab toC perFr laU
open scoped LaurentSeries Matrix

namespace GlobalTheory.ValNorm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem exists_idx (hσ : GoodEmb c σ) (X : Data E r) (hr : r = Dw.p + Dw.q) (hp0 : X.p0 = Dw.q)
    (hty : ∀ τ : E →+* ℂ, τ ∈ X.Ψ ↔ τ (H.rt : E) = H.rt0) {g : ℕ}
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) :
    ∃ idx : Fin g ≃ X.Ψ × Fin r, (∀ j,
      (X.p0 ≤ ((idx j).2 : ℕ) ∧ (idx j).1.1 = relab c σ (e j).1 ∧ ((idx j).2 : ℕ) = X.p0 + (e j).2) ∨
      (((idx j).2 : ℕ) < X.p0 ∧ conjEmb (idx j).1.1 = relab c σ (e j).1 ∧
        ((idx j).2 : ℕ) = X.p0 - 1 - (e j).2 ∧ ((e j).2 : ℕ) < X.p0)) ∧
      ∀ (x : Frame X.Ψ r) (v : Fin r → E) j, perFr X x v (relab c σ (e j).1) (e j).2 =
        if ((idx j).2 : ℕ) < X.p0 then
          hermC (idx j).1.1 X.Gm (col (mat x (idx j).1) (idx j).2) (Data.emb (idx j).1.1 v)
        else ((mat x (idx j).1)⁻¹ *ᵥ Data.emb (idx j).1.1 v) (idx j).2 := by
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := fun τ =>
    ComplexEmbedding.involutive_conjugate E τ
  obtain ⟨f, hf⟩ := GlobalTheory.FrameUnif.exists_letter_equiv X.Ψ X.cmType Dw.p Dw.q r hr (relab c σ) hbij Dw.mult
    (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))])
    (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])
  obtain ⟨idx, hi⟩ : ∃ idx : Fin g ≃ X.Ψ × Fin r, ∀ j,
      (relab c σ (e j).1 ∈ X.Ψ ∧ (idx j).1.1 = relab c σ (e j).1 ∧ ((idx j).2 : ℕ) = Dw.q + (e j).2) ∨
      (relab c σ (e j).1 ∉ X.Ψ ∧ (idx j).1.1 = ComplexEmbedding.conjugate (relab c σ (e j).1) ∧
        ((idx j).2 : ℕ) = Dw.q - 1 - (e j).2 ∧ ((e j).2 : ℕ) < Dw.q) := ⟨e.trans f, fun j => hf (e j)⟩
  rw [← hp0] at hi
  refine ⟨idx, fun j => ?_, fun x v j => ?_⟩
  · rcases hi j with ⟨a, b, c'⟩ | ⟨a, b, c', d⟩
    · exact Or.inl ⟨by omega, b, c'⟩
    · exact Or.inr ⟨by omega, by rw [b]; exact hcc _, c', d⟩
  · have h := hi j
    generalize idx j = t at h ⊢
    obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
    dsimp only at h ⊢
    rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
    · rw [if_neg (by omega)]
      unfold perFr
      rw [dite_eq_left a, dite_eq_left hn]
    · rw [if_pos (by omega)]
      unfold perFr
      rw [dite_eq_right a, dite_eq_left (show conjEmb (relab c σ (e j).1) ∈ X.Ψ from hτ), dite_eq_left hn]
      rfl

theorem exists_move (hσ : GoodEmb c σ) (U : Unf Xo c σ r) (k : U.Comp) (hr : r = Dw.p + Dw.q)
    (hp0 : (U.X k).p0 = Dw.q) (hty : ∀ τ : E →+* ℂ, τ ∈ (U.X k).Ψ ↔ τ (H.rt : E) = H.rt0) {g : ℕ}
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (x b : Frame (U.X k).Ψ r) (hb : b ∈ Bor (U.X k).Ψ r) :
    ∃ h₀ : Matrix (Fin g) (Fin g) ℂ,
      (∀ v : Fin r → E, (fun j => perFr (U.X k) (rmul x b) v (relab c σ (e j).1) (e j).2) =
        h₀ *ᵥ fun j => perFr (U.X k) x v (relab c σ (e j).1) (e j).2) ∧
      (∀ j j', h₀⁻¹ j j' ≠ 0 → (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2) ∧
      ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ),
        ∏ j, h₀⁻¹ j j ^ (a ((e j).1, (e j).2) + n / 2) = bchar (laU U a n k) b := by
  obtain ⟨idx, hi, hper⟩ := exists_idx hσ (U.X k) hr hp0 hty e
  obtain ⟨hbij, -, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  have hinj : ∀ j j', (e j).1 = (e j').1 → ((e j).2 : ℕ) = (e j').2 → j = j' := by
    intro j j' h1 h2
    apply e.injective
    refine Sigma.ext h1 ((Fin.heq_ext_iff (by rw [h1])).2 h2)
  have hs : ∀ j j', PerBor.moveMat (U.X k).p0 idx b j j' ≠ 0 →
      (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2 := by
    intro j j' hne
    obtain ⟨h1, h2⟩ := PerBor.moveMat_support _ idx hb j j' hne
    rcases hi j with ⟨a1, b1, c1⟩ | ⟨a1, b1, c1, d1⟩
    · rw [if_neg (by omega)] at h2
      rcases hi j' with ⟨a2, b2, c2⟩ | ⟨a2, b2, c2, d2⟩
      · exact ⟨hbij.1 (by rw [← b1, ← b2, h1]), by omega⟩
      · omega
    · rw [if_pos a1] at h2
      rcases hi j' with ⟨a2, b2, c2⟩ | ⟨a2, b2, c2, d2⟩
      · omega
      · exact ⟨hbij.1 (by rw [← b1, ← b2, h1]), by omega⟩
  have hdet := PerBor.det_of_support _ _ hinj _ hs
  have hdiag := PerBor.moveMat_diag (U.X k).p0 idx hb
  have hbne : ∀ τ i, b τ i i ≠ 0 := fun τ i => PerMove.bor_diag_ne hb τ i
  have hu : IsUnit (PerBor.moveMat (U.X k).p0 idx b).det := by
    rw [hdet, isUnit_iff_ne_zero]
    refine Finset.prod_ne_zero_iff.2 fun j _ => ?_
    rw [hdiag]
    split_ifs
    · exact hbne _ _
    · exact inv_ne_zero (hbne _ _)
  refine ⟨PerBor.moveMat (U.X k).p0 idx b, fun v => ?_, PerBor.inv_support _ _ _ hu hs, fun a n => ?_⟩
  · exact PerBor.moveMat_mulVec _ idx hb (U.X k).Gm x v _ _ (fun j => hper _ _ j) (fun j => hper _ _ j)
  · unfold bchar
    refine Eq.trans ?_ (Fintype.prod_prod_type'
      (fun (τ : (U.X k).Ψ) (i : Fin r) => b τ i i ^ laU U a n k τ i))
    rw [← idx.prod_comp]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [PerBor.inv_diag _ _ hinj _ hu hs, hdiag]
    have hinv := Function.leftInverse_invFun hbij.1 (e j).1
    unfold laU
    rcases hi j with ⟨a1, b1, c1⟩ | ⟨a1, b1, c1, d1⟩
    · rw [if_neg (by omega), if_pos a1, b1, hinv,
        show ((idx j).2 : ℕ) - (U.X k).p0 = (e j).2 by omega, inv_inv, ← zpow_natCast]
      congr 1
    · rw [if_pos a1, if_neg (by omega), b1, hinv,
        show (U.X k).p0 - 1 - ((idx j).2 : ℕ) = (e j).2 by omega, inv_pow, ← zpow_natCast, ← zpow_neg]
      congr 1
      push_cast
      ring

theorem exists_frBor (hσ : GoodEmb c σ) (U : Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (hr : r = Dw.p + Dw.q)
    (hp0 : (U.X k).p0 = Dw.q) (hty : ∀ τ : E →+* ℂ, τ ∈ (U.X k).Ψ ↔ τ (H.rt : E) = H.rt0)
    (x : (U.X k).dom) (b : Frame (U.X k).Ψ r) (hb : b ∈ Bor (U.X k).Ψ r) (h : rmul x.1 b ∈ (U.X k).dom) :
    ∃ (t : Ix Dw → (CAt σ)ˣ) (G : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ)),
      FrBor t (U.un k x) (U.un k ⟨_, h⟩) ∧ FrChg G (t none : CAt σ) (U.un k x) (U.un k ⟨_, h⟩) ∧
      ∀ a n, toC (wchar (ex Dw a n) t) * bchar (laU U 0 n k) b =
        toC (t none : CAt σ) ^ n * bchar (laU U a n k) b := by
  obtain ⟨h₀, hP, htri, hw⟩ := exists_move hσ U k hr hp0 hty Uw.e x.1 b hb
  have hp := Uw.period k x
  have hp' := Uw.period k ⟨_, h⟩
  obtain ⟨hdet, hu, hex⟩ := GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E H Dw l Xo _ _ _ Uw.F (Uw.ik k)
    (Uw.Pm k x) (Uw.Pm k ⟨_, h⟩) (LinearEquiv.refl _ _) h₀ hp hp' (fun _ _ => rfl) (fun a _ => ⟨0, by simp⟩)
    (fun a => ⟨0, by simp⟩) (fun a => by
      have e1 : Uw.Pm k x a = _ := funext (Uw.Pm_eq k x a)
      have e2 : Uw.Pm k ⟨_, h⟩ a = _ := funext (Uw.Pm_eq k ⟨_, h⟩ a)
      rw [LinearEquiv.refl_apply, e1, e2]
      exact hP _)
  obtain ⟨hy1, hy2⟩ := Uw.lie k x
  obtain ⟨hy1', hy2'⟩ := Uw.lie k ⟨_, h⟩
  have hxx : (U.un k ⟨_, h⟩).x = (U.un k x).x := hy1'.trans (hu.symm.trans hy1.symm)
  have hder : ∀ τ i, IsDerivAt0 (fun z => (Uw.F.ex (Uw.ik k) (Uw.Pm k x) z).left)
      (h₀⁻¹ *ᵥ Pi.single (Uw.e.symm ⟨τ, i⟩) 1) ((U.un k ⟨_, h⟩).u τ i) := by
    intro τ i
    refine (GlobalTheory.ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ _ _ Uw.F (Uw.ik k) (Uw.Pm k x) hp (Uw.ik k)
      (Uw.Pm k ⟨_, h⟩) (Matrix.mulVecLin h₀) hp' hex _ _).2 ?_
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
    exact hy2' τ i
  obtain ⟨G, t₀, -, hG⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c (CAt σ) _ _).1 hxx
  have hinv : (h₀⁻¹).det ≠ 0 := (Matrix.isUnit_nonsing_inv_det h₀ hdet).ne_zero
  have hdiag := GlobalTheory.NormUnBor.diag_ne_zero Uw.e h₀⁻¹ hinv htri
  let d : Fin Uw.g → (CAt σ)ˣ := fun j => (Units.mk0 (h₀⁻¹ j j) (hdiag j) : ℂˣ)
  let t : Ix Dw → (CAt σ)ˣ := fun o => Option.elim o t₀ (fun p => d (Uw.e.symm p))
  refine ⟨t, G, ⟨hxx, fun τ i => ⟨fun i' => (h₀⁻¹ (Uw.e.symm ⟨τ, i'⟩) (Uw.e.symm ⟨τ, i⟩) : ℂ), rfl, ?_, ?_⟩, ?_⟩,
    hG, ?_⟩
  · intro j hj
    by_contra hne
    have := (htri _ _ hne).2
    rw [Uw.e.apply_symm_apply, Uw.e.apply_symm_apply] at this
    exact absurd hj (not_lt.2 this)
  · rw [hy1]
    refine (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ _ _ Uw.F _ _ hp _ _ _ (hy2 τ) _ _).2 ?_
    rw [GlobalTheory.NormUnBor.col_eq_sum Uw.e h₀⁻¹ htri]
    exact hder τ i
  · obtain ⟨pm, h1, h2, h3⟩ := hG.2.2
    refine ⟨pm, h1, ?_, h3⟩
    rw [h2]
    simp [spMap]
  · intro a n
    rw [← hw a n, ← hw 0 n]
    show (∏ o : Ix Dw, toC ((t o : (CAt σ)ˣ) : CAt σ) ^ ex Dw a n o) * _ = _
    rw [Fintype.prod_option, mul_assoc]
    congr 1
    rw [← Equiv.prod_comp Uw.e, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    show h₀⁻¹ (Uw.e.symm (Uw.e j)) (Uw.e.symm (Uw.e j)) ^ a ((Uw.e j).1, (Uw.e j).2) * _ = _
    rw [Uw.e.symm_apply_apply, ← pow_add, Pi.zero_apply, zero_add]

theorem exists_unit (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    ∃ b ∈ Bor X.Ψ r, rmul x b ∈ X.dom ∧ ∀ τ i, ‖dmin X.Gm (rmul x b) τ i‖ = 1 := by
  obtain ⟨_, b, hb, hg, rfl⟩ :=
    (GlobalTheory.UnitFrames.frame_mul_triangular_orthonormal E r X.p0 X.Ψ X.Gm X.Gm_herm).1 x hx
  refine ⟨b, hb, ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.dom_rmul X hx hb, fun τ i => ?_⟩
  unfold dmin lminor
  rw [hg, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, norm_prod]
  refine Finset.prod_eq_one fun a _ => ?_
  simp only [Function.comp_apply, sgn]
  split_ifs <;> simp

end GlobalTheory.ValNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CoeffEqZeroOfHasSumZero
namespace GlobalTheory.LaurentFJ

open Complex ReciprocityTheory.ChartRestriction.G.FD

noncomputable section

theorem coeff_eq_zero_of_hasSum_zero (d : ℤ → ℂ)
    (h : ∀ t : ℝ, HasSum (fun k : ℤ => d k * cexp (2 * Real.pi * I * t) ^ k) 0) (j : ℤ) :
    d j = 0 := by
  have hs : Summable fun k => ‖d k‖ := by
    have := (h 0).summable
    simp only [ofReal_zero, mul_zero, Complex.exp_zero, one_zpow, mul_one] at this
    exact summable_norm_iff.mpr this
  have hpow : ∀ (k : ℤ) (t : ℝ), cexp (2 * Real.pi * I * t) ^ k * cexp (2 * Real.pi * I * t) ^ (-j)
      = cexp ((2 * Real.pi * I * ((k - j : ℤ) : ℂ)) * t) := by
    intro k t
    rw [← Complex.exp_int_mul, ← Complex.exp_int_mul, ← Complex.exp_add]
    congr 1; push_cast; ring
  have hI := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := MeasureTheory.volume)
    (a := 0) (b := 1) (f := fun _ : ℝ => (0 : ℂ))
    (F := fun (k : ℤ) (t : ℝ) => d k * cexp ((2 * Real.pi * I * ((k - j : ℤ) : ℂ)) * t))
    (fun k _ => ‖d k‖)
    (fun k => (by fun_prop : Continuous fun t : ℝ =>
      d k * cexp ((2 * Real.pi * I * ((k - j : ℤ) : ℂ)) * t)).aestronglyMeasurable)
    (fun k => MeasureTheory.ae_of_all _ fun t _ => by
      have : (2 * Real.pi * I * ((k - j : ℤ) : ℂ)) * t =
          ((2 * Real.pi * ((k - j : ℤ) : ℝ) * t : ℝ) : ℂ) * I := by push_cast; ring
      rw [norm_mul, this, Complex.norm_exp_ofReal_mul_I, mul_one])
    (MeasureTheory.ae_of_all _ fun t _ => hs) intervalIntegrable_const
    (MeasureTheory.ae_of_all _ fun t _ => by
      have := (h t).mul_right (cexp (2 * Real.pi * I * t) ^ (-j))
      simp only [zero_mul, mul_assoc (d _), hpow] at this
      exact this)
  have hval : ∀ k : ℤ, (∫ t in (0 : ℝ)..1,
      d k * cexp ((2 * Real.pi * I * ((k - j : ℤ) : ℂ)) * t)) = if k = j then d j else 0 := by
    intro k
    split_ifs with hk
    · subst hk; simp
    · have hc : (2 * Real.pi * I * ((k - j : ℤ) : ℂ)) ≠ 0 := by
        refine mul_ne_zero Complex.two_pi_I_ne_zero ?_
        exact_mod_cast sub_ne_zero.mpr hk
      rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex hc]
      have : cexp (2 * Real.pi * I * ((k - j : ℤ) : ℂ)) = 1 := by
        rw [mul_comm]; exact Complex.exp_int_mul_two_pi_mul_I _
      simp only [ofReal_one, mul_one, ofReal_zero, mul_zero, Complex.exp_zero, this]
      simp
  simp only [hval, intervalIntegral.integral_zero] at hI
  exact (hasSum_ite_eq j (d j)).unique hI

theorem hasSum_fiber_of_hasSum_line {ι : Type*} (c : ι → ℂ) (n : ι → ℤ) (a : ℤ → ℂ) (y : ℝ)
    (f : ℝ → ℂ)
    (ha : ∀ t : ℝ, HasSum (fun k : ℤ => a k * cexp (2 * Real.pi * I * (t + y * I)) ^ k) (f t))
    (hc : ∀ t : ℝ, HasSum (fun i => c i * cexp (2 * Real.pi * I * (t + y * I)) ^ n i) (f t))
    (j : ℤ) : HasSum (fun i : {i // n i = j} => c i) (a j) := by
  have hsum : ∀ k : ℤ, Summable fun i : {i // n i = k} => c i := by
    intro k
    have h1 := ((hc 0).summable.subtype fun i => n i = k).mul_right
      (cexp (2 * Real.pi * I * ((0 : ℝ) + y * I)) ^ (-k))
    refine h1.congr fun i => ?_
    have hi : n i = k := i.2
    simp only [Function.comp_apply, hi]
    rw [mul_assoc, ← zpow_add₀ (Complex.exp_ne_zero _)]
    simp
  have hb : ∀ t : ℝ, HasSum (fun k : ℤ => (∑' i : {i // n i = k}, c i) *
      cexp (2 * Real.pi * I * (t + y * I)) ^ k) (f t) := by
    intro t
    have h1 := (Equiv.sigmaFiberEquiv n).hasSum_iff.mpr (hc t)
    refine h1.sigma fun k => ?_
    have := (hsum k).hasSum.mul_right (cexp (2 * Real.pi * I * (t + y * I)) ^ k)
    refine this.congr_fun fun i => ?_
    simp only [Function.comp_apply, Equiv.sigmaFiberEquiv, Equiv.coe_fn_mk, i.2]
  have hz := coeff_eq_zero_of_hasSum_zero
    (fun k => (a k - ∑' i : {i // n i = k}, c i) * cexp (2 * Real.pi * I * (y * I)) ^ k)
    (fun t => by
      have := (ha t).sub (hb t)
      rw [sub_self] at this
      refine this.congr_fun fun k => ?_
      rw [mul_add, Complex.exp_add, mul_zpow]; ring) j
  have hz' : a j = ∑' i : {i // n i = j}, c i :=
    sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (zpow_ne_zero _ (Complex.exp_ne_zero _)))
  rw [hz']
  exact (hsum j).hasSum

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}

theorem flow_mem_dom_of_im_nonneg (X : Data E r) {ξ : Fin r → E} (hξ : X.IsIso ξ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) (s : X.Ψ → ℂ) (hs : ∀ τ, 0 ≤ (s τ).im) :
    X.flow ξ s x ∈ X.dom := by
  have hiv : X.IsIsoV fun τ => Data.emb τ.1 ξ := by
    intro τ
    refine ⟨?_, ?_⟩
    · have key : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = τ.1 (herm X.Gm ξ ξ) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [hermC, herm, Data.emb, map_sum, map_mul, cc,
          NumberField.IsCMField.complexEmbedding_complexConj]
      change hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0
      rw [key, hξ.2.1, map_zero]
    · intro h0
      apply hξ.2.2
      funext a
      have := congrFun h0 a
      simpa [Data.emb] using this
  refine (flowDomainCriterion_holds r X _ hiv x hx s).1.2 fun τ => ?_
  have ht : 0 < X.ttV (fun τ => Data.emb τ.1 ξ) x τ :=
    one_div_pos.mpr (mul_pos (MajorantFamilyNorms.c_pos X τ) (X.maj_pos hx τ (hiv τ).2))
  have := div_nonneg (hs τ) ht.le
  linarith

theorem hasSum_fj_of_line (X : Data E r) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ}
    (hP : X.IsSec la P) {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (sb : X.Ψ → ℝ)
    (hint : ∀ ν : X.Ψ → ℝ, X.fj la ξ ν P x ≠ 0 → ∃ k : ℤ, 2 * ∑ τ, ν τ * sb τ = k)
    (κ u₁ : ℂ) (a : ℤ → ℂ) (y : ℝ)
    (hdom : ∀ w : ℂ, w.im = y → X.flow ξ (fun τ => w * sb τ) x ∈ X.dom)
    (ha : ∀ w : ℂ, w.im = y → HasSum (fun n : ℤ => a n * (u₁ * cexp (2 * Real.pi * I * w)) ^ n)
      (κ * P (X.flow ξ (fun τ => w * sb τ) x))) (j : ℤ) :
    HasSum (fun ν : {ν : X.Ψ → ℝ // 2 * ∑ τ, ν τ * sb τ = j} => κ * X.fj la ξ ν P x)
      (a j * u₁ ^ j) := by
  classical
  set n : (X.Ψ → ℝ) → ℤ := fun ν => ⌊2 * ∑ τ, ν τ * sb τ⌋ with hn
  have hnν : ∀ ν, X.fj la ξ ν P x ≠ 0 → 2 * ∑ τ, ν τ * sb τ = n ν := by
    intro ν hν
    obtain ⟨k, hk⟩ := hint ν hν
    simp only [hn, hk, Int.floor_intCast]
  have him : ∀ t : ℝ, ((t : ℂ) + y * I).im = y := fun t => by simp
  have H := hasSum_fiber_of_hasSum_line (fun ν => κ * X.fj la ξ ν P x) n
    (fun k => a k * u₁ ^ k) y (fun t => κ * P (X.flow ξ (fun τ => ((t : ℂ) + y * I) * sb τ) x))
    (fun t => by
      convert ha _ (him t) using 2 with k
      rw [mul_zpow, mul_assoc])
    (fun t => by
      have := (m3bExp_holds r X la P hP ξ hξ x hx _ (hdom _ (him t))).mul_left κ
      refine this.congr_fun fun ν => ?_
      rw [mul_assoc]
      by_cases hν : X.fj la ξ ν P x = 0
      · simp [hν]
      · congr 2
        rw [← Complex.exp_int_mul]
        congr 1
        have h2 : ((n ν : ℤ) : ℂ) = 2 * ∑ τ, (ν τ : ℂ) * sb τ := by
          have := congrArg (fun z : ℝ => (z : ℂ)) (hnν ν hν)
          push_cast at this
          exact this.symm
        have h3 : ∑ τ, (ν τ : ℂ) * (((t : ℂ) + y * I) * sb τ) =
            ((t : ℂ) + y * I) * ∑ τ, (ν τ : ℂ) * sb τ := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun τ _ => by ring
        rw [h2, h3]; ring) j
  have e1 := (hasSum_subtype_iff_indicator (s := {ν | n ν = j})
    (f := fun ν => κ * X.fj la ξ ν P x)).mp H
  refine (hasSum_subtype_iff_indicator (s := {ν : X.Ψ → ℝ | 2 * ∑ τ, ν τ * sb τ = j})
    (f := fun ν => κ * X.fj la ξ ν P x)).mpr ?_
  convert e1 using 1
  funext ν
  by_cases hν : X.fj la ξ ν P x = 0
  · simp [Set.indicator_apply, hν]
  · have : (2 * ∑ τ, ν τ * sb τ = j) ↔ n ν = j := by
      rw [hnν ν hν]; exact Int.cast_inj
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, this]

theorem hasSum_fj (X : Data E r) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ}
    (hP : X.IsSec la P) {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (sb : X.Ψ → ℝ) (hsb : ∀ τ, 0 ≤ sb τ)
    (hint : ∀ ν : X.Ψ → ℝ, X.fj la ξ ν P x ≠ 0 → ∃ k : ℤ, 2 * ∑ τ, ν τ * sb τ = k)
    (κ u₁ : ℂ) (a : ℤ → ℂ) (T : ℝ)
    (ha : ∀ w : ℂ, T < w.im → HasSum (fun n : ℤ => a n * (u₁ * cexp (2 * Real.pi * I * w)) ^ n)
      (κ * P (X.flow ξ (fun τ => w * sb τ) x))) (j : ℤ) :
    HasSum (fun ν : {ν : X.Ψ → ℝ // 2 * ∑ τ, ν τ * sb τ = j} => κ * X.fj la ξ ν P x)
      (a j * u₁ ^ j) := by
  refine hasSum_fj_of_line X hP hξ hx sb hint κ u₁ a (max T 0 + 1) (fun w hw => ?_)
    (fun w hw => ha w (by rw [hw]; linarith [le_max_left T 0])) j
  refine flow_mem_dom_of_im_nonneg X hξ hx _ fun τ => ?_
  simp only [mul_im, ofReal_re, ofReal_im, mul_zero, zero_add, hw]
  exact mul_nonneg (by linarith [le_max_right T 0]) (hsb τ)

theorem coeff_mul_zpow_eq_mul_fj (X : Data E r) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ}
    (hP : X.IsSec la P) {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (sb : X.Ψ → ℝ) (hsb : ∀ τ, 0 ≤ sb τ) (ν₀ : X.Ψ → ℝ) (j : ℤ)
    (hj : 2 * ∑ τ, ν₀ τ * sb τ = j)
    (huniq : ∀ ν : X.Ψ → ℝ, X.fj la ξ ν P x ≠ 0 → 2 * ∑ τ, ν τ * sb τ = j → ν = ν₀)
    (hint : ∀ ν : X.Ψ → ℝ, X.fj la ξ ν P x ≠ 0 → ∃ k : ℤ, 2 * ∑ τ, ν τ * sb τ = k)
    (κ u₁ : ℂ) (a : ℤ → ℂ) (T : ℝ)
    (ha : ∀ w : ℂ, T < w.im → HasSum (fun n : ℤ => a n * (u₁ * cexp (2 * Real.pi * I * w)) ^ n)
      (κ * P (X.flow ξ (fun τ => w * sb τ) x))) :
    a j * u₁ ^ j = κ * X.fj la ξ ν₀ P x := by
  refine (hasSum_fj X hP hξ hx sb hsb hint κ u₁ a T ha j).unique ?_
  refine hasSum_single (f := fun ν : {ν : X.Ψ → ℝ // 2 * ∑ τ, ν τ * sb τ = j} =>
    κ * X.fj la ξ ν P x) ⟨ν₀, hj⟩ fun ν hν => ?_
  by_cases h0 : X.fj la ξ ν P x = 0
  · simp [h0]
  · exact absurd (Subtype.ext (huniq ν h0 ν.2)) hν

end

end GlobalTheory.LaurentFJ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstRatioOfNormEq
open Complex

namespace GlobalTheory

theorem exists_const_ratio_of_norm_eq :
    ∀ (I : Type) (T K : ℝ) (f g : I → ℂ → ℂ) (c : ℂ → ℂ), 0 < K →
      (∀ i, DifferentiableOn ℂ (f i) {w | T < w.im} ∧ DifferentiableOn ℂ (g i) {w | T < w.im}) →
      (∀ i w, T < w.im → f i w = c w * g i w ∧ ‖f i w‖ = K * ‖g i w‖) →
      ∃ κ : ℂ, ‖κ‖ = K ∧ ∀ i w, T < w.im → f i w = κ * g i w := by
  intro I T K f g c hK hd h
  by_cases h0 : ∀ i w, T < w.im → g i w = 0
  · refine ⟨K, by simp [abs_of_pos hK], fun i w hw => ?_⟩
    rw [(h i w hw).1, h0 i w hw]; simp
  push_neg at h0
  obtain ⟨i₀, w₀, hw₀, hg₀⟩ := h0
  have hU : IsOpen {w : ℂ | T < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hUc : IsPreconnected {w : ℂ | T < w.im} := (convex_halfSpace_im_gt T).isPreconnected
  have hca : ContinuousAt (g i₀) w₀ :=
    (hd i₀).2.continuousOn.continuousAt (hU.mem_nhds hw₀)
  have hev : ∀ᶠ w in nhds w₀, T < w.im ∧ g i₀ w ≠ 0 :=
    (hU.eventually_mem hw₀).and (hca.eventually_ne hg₀)
  obtain ⟨r, hr, hB⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hsub : Metric.ball w₀ r ⊆ {w : ℂ | T < w.im} := fun w hw => (hB w hw).1
  have hcq : ∀ w ∈ Metric.ball w₀ r, c w = f i₀ w / g i₀ w := fun w hw => by
    rw [(h i₀ w (hB w hw).1).1, mul_div_cancel_right₀ _ (hB w hw).2]
  have hcd : DifferentiableOn ℂ c (Metric.ball w₀ r) :=
    (((hd i₀).1.mono hsub).div ((hd i₀).2.mono hsub) fun w hw => (hB w hw).2).congr hcq
  have hcn : ∀ w ∈ Metric.ball w₀ r, ‖c w‖ = K := fun w hw => by
    rw [hcq w hw, norm_div, (h i₀ w (hB w hw).1).2,
      mul_div_cancel_right₀ _ (norm_ne_zero_iff.2 (hB w hw).2)]
  have hm : w₀ ∈ Metric.ball w₀ r := Metric.mem_ball_self hr
  have hconst := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
    (convex_ball w₀ r).isPreconnected Metric.isOpen_ball hcd hm
    (fun w hw => by
      show ‖c w‖ ≤ ‖c w₀‖
      rw [hcn w hw, hcn w₀ hm])
  refine ⟨c w₀, hcn w₀ hm, fun i w hw => ?_⟩
  have ha : AnalyticOnNhd ℂ (f i) {w : ℂ | T < w.im} := (hd i).1.analyticOnNhd hU
  have hb : AnalyticOnNhd ℂ (fun w => c w₀ * g i w) {w : ℂ | T < w.im} :=
    ((hd i).2.const_mul (c w₀)).analyticOnNhd hU
  have he : f i =ᶠ[nhds w₀] fun w => c w₀ * g i w := by
    filter_upwards [Metric.ball_mem_nhds w₀ hr] with z hz
    rw [(h i z (hB z hz).1).1, hconst hz]
    rfl
  exact ha.eqOn_of_preconnected_of_eventuallyEq hb hUc hw₀ he hw

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LaurentCoeffSectionValueArcEqFourierJacobi
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open Formalism.L2.Pj hiding Unf GoodEmb relab toC perFr laU
open scoped LaurentSeries

namespace GlobalTheory.ArcCoeff

theorem norm_eTwoPi_zpow (w : ℂ) (m : ℤ) : ‖eTwoPi w ^ m‖ = Real.exp (-(2 * Real.pi * m) * w.im) := by
  unfold eTwoPi
  rw [← Complex.exp_int_mul, Complex.norm_exp]
  congr 1
  simp
  ring

theorem differentiableOn_of_hasSum (a : ℤ → ℂ) (T : ℝ) (f : ℂ → ℂ)
    (h : ∀ w : ℂ, T < w.im → HasSum (fun m : ℤ => a m * eTwoPi w ^ m) (f w)) :
    DifferentiableOn ℂ f {w | T < w.im} := by
  intro w₀ hw₀
  have hw₀' : T < w₀.im := hw₀
  set y₁ : ℝ := (T + w₀.im) / 2 with hy₁
  set y₂ : ℝ := w₀.im + 1 with hy₂
  have hs : ∀ y : ℝ, T < y → Summable fun m : ℤ => ‖a m‖ * Real.exp (-(2 * Real.pi * m) * y) := fun y hy => by
    have := (h (y * Complex.I) (by simpa using hy)).summable.norm
    simpa only [norm_mul, norm_eTwoPi_zpow, Complex.mul_I_im, Complex.ofReal_re] using this
  have hO : IsOpen {w : ℂ | y₁ < w.im ∧ w.im < y₂} :=
    (isOpen_lt continuous_const Complex.continuous_im).inter (isOpen_lt Complex.continuous_im continuous_const)
  have hd : DifferentiableOn ℂ (fun w => ∑' m : ℤ, a m * eTwoPi w ^ m) {w : ℂ | y₁ < w.im ∧ w.im < y₂} := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      ((hs y₁ (by linarith)).add (hs y₂ (by linarith))) (fun m => ?_) hO (fun m w hw => ?_)
    · have : (fun w => a m * eTwoPi w ^ m) = fun w => a m * Complex.exp (m * (2 * Real.pi * Complex.I * w)) := by
        funext w
        rw [Complex.exp_int_mul]
        rfl
      rw [this]
      fun_prop
    · rw [norm_mul, norm_eTwoPi_zpow, ← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rcases le_total 0 (2 * Real.pi * m) with hm | hm
      · exact le_add_of_le_of_nonneg (Real.exp_le_exp.2 (by nlinarith [hw.1])) (Real.exp_pos _).le
      · exact le_add_of_nonneg_of_le (Real.exp_pos _).le (Real.exp_le_exp.2 (by nlinarith [hw.2]))
  have hm : {w : ℂ | y₁ < w.im ∧ w.im < y₂} ∈ nhds w₀ := hO.mem_nhds ⟨by linarith, by linarith⟩
  refine ((hd.differentiableAt hm).congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [hm] with w hw
  exact (h w (by linarith [hw.1])).tsum_eq.symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem two_sum_eq_trace (X : Data E r) {ν s : E} (hν : cc ν = ν) (hs : cc s = s) :
    2 * ∑ τ : X.Ψ, (τ.1 ν).re * (τ.1 s).re = ((Algebra.trace ℚ E (ν * s) : ℚ) : ℝ) := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_ratCast, X.trace_eq_Psi]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [map_mul, RealEmbeddingCharacters.emb_real hs, RealEmbeddingCharacters.emb_real hν, map_mul, Complex.conj_ofReal, Complex.conj_ofReal,
    Complex.ofReal_re, Complex.ofReal_re]
  ring

theorem coeff_eq_of_betaAt (X : Data E r) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (hP : X.IsBddSec la P)
    {ξ' : Fin r → E} (hξ : X.IsIso ξ') {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    {M : Type} [AddCommGroup M] [Module (𝓞 E) M] (ξ : Module.Dual ℤ M) (N : ℕ) (be : LinearMap.BilinForm ℤ M)
    (hbe : ∀ y z, (N : ℤ) ∣ be y z) {ν₀ sE : E} {jj : ℤ} (hβ : BetaAt ξ N be ν₀ jj) (hs : IsBePar ξ be sE)
    (hpos : ∀ τ : X.Ψ, 0 < (τ.1 sE).re) (hT : TransvIn X N la)
    (hlev : ∀ s : E, LevelPar ξ N s → ∀ v ∈ X.Λ, ∃ u ∈ X.Λ,
      (transvMat X.Gm ξ' (s * X.κ0)).mulVec v - v = (N : E) • u)
    (κ w₁ : ℂ) (a : ℤ → ℂ) (T : ℝ)
    (ha : ∀ w : ℂ, T < w.im → HasSum (fun m : ℤ => a m * eTwoPi w ^ m)
      (κ * P (X.flow ξ' (fun τ => (w - w₁) * ((τ.1 sE).re : ℂ)) x))) :
    a jj * eTwoPi w₁ ^ jj = κ * X.fj la ξ' (fun τ => (τ.1 ν₀).re) P x := by
  obtain ⟨hν₀, hβ⟩ := hβ
  obtain ⟨htr, huq⟩ := hβ sE hs
  have hsL : LevelPar ξ N sE := ⟨hs.1, fun y z => by
    obtain ⟨m, hm⟩ := hbe y z
    exact ⟨m, by rw [hs.2, hm]; push_cast; rfl⟩⟩
  have hfr : ∀ ν : X.Ψ → ℝ, X.fj la ξ' ν P x ≠ 0 → ∃ ν₁ : E, cc ν₁ = ν₁ ∧ (ν = fun τ => (τ.1 ν₁).re) ∧
      (∀ τ : E →+* ℂ, 0 ≤ (τ ν₁).re) ∧ ∀ s, LevelPar ξ N s → ∃ m : ℤ, Algebra.trace ℚ E (ν₁ * s) = m := by
    intro ν hν
    obtain ⟨ν₁, h1, h2, h3, h4⟩ := GlobalTheory.FjFreq.freq_real_nonneg_integral E r X la P hP ξ' hξ ν x hx hν
    exact ⟨ν₁, h1, funext h2, h3, fun s hs' => h4 s hs'.1 (hT ξ' hξ s hs'.1 (hlev s hs'))⟩
  refine GlobalTheory.LaurentFJ.coeff_mul_zpow_eq_mul_fj X hP.1 hξ hx (fun τ => (τ.1 sE).re) (fun τ => (hpos τ).le) _ jj
    ?_ (fun ν hν hj => ?_) (fun ν hν => ?_) κ _ a (T - w₁.im) (fun w hw => ?_)
  · rw [two_sum_eq_trace X hν₀ hs.1, htr, Rat.cast_intCast]
  · obtain ⟨ν₁, h1, rfl, h3, h4⟩ := hfr ν hν
    rw [two_sum_eq_trace X h1 hs.1] at hj
    rw [huq ν₁ h1 h3 h4 (by exact_mod_cast hj)]
  · obtain ⟨ν₁, h1, rfl, -, h4⟩ := hfr ν hν
    obtain ⟨m, hm⟩ := h4 sE hsL
    exact ⟨m, by rw [two_sum_eq_trace X h1 hs.1, hm, Rat.cast_intCast]⟩
  · have := ha (w₁ + w) (by rw [Complex.add_im]; linarith)
    simp only [add_sub_cancel_left, eTwoPi, mul_add, Complex.exp_add] at this
    exact this

theorem frChg_of_anLie {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (i : Fin Fu.n)
    (Pm : (Fu.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (Fu.Di i) ty Pm) (y y' : FrPt Xo c (CAt σ))
    (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin g → ℂ)) (h : AnLie Fu i Pm y z) (h' : AnLie Fu i Pm y' z) :
    ∃ s, FrChg (fun _ => 1) s y y' := by
  have hx : y'.x = y.x := h'.1.trans h.1.symm
  obtain ⟨G, s, -, hG⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c (CAt σ) y y').1 hx
  obtain ⟨-, hder, -⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ _ _ Fu i _ hP
  refine ⟨s, hx, fun τ k => ?_, hG.2.2⟩
  rw [(hder _).unique (h'.2 τ k) (h.2 τ k)]
  exact (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c (CAt σ) y y y).1.2.1 τ k

theorem evR_eq_and_norm (hL : Out.Laws) (hL2 : Out.Laws2) (U : Unf Xo c σ r) (Uw : UnfWit U)
    (hEv : GlobalTheory.Reg.EvLaws Xo c) (hσ : GoodEmb c σ) (hU : IsUnf U) (k : U.Comp) (x : (U.X k).dom)
    (y : FrPt Xo c (CAt σ)) (s : CAt σ) (v : ℝ) (hchg : FrChg (fun _ => 1) s (U.un k x) y)
    (i : Fin Uw.F.n) (Pm : (Uw.F.Di i).La →+ (Fin Uw.g → ℂ)) (hPm : IsPeriod (Uw.F.Di i) (fun j => relab c σ (Uw.e j).1) Pm)
    (hy : y.x = Uw.F.u i Pm) (hv : IsThetaL2NormSquared Uw.F i Pm y v) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (F : Rul Xo c)
    (hD : Dom a n) (hF : F ∈ sec Xo c a n) :
    toC (evR Xo c F y) = toC s ^ n * rdU U F k x.1 ∧
      ‖toC (evR Xo c F y)‖ = v ^ ((n : ℝ) / 2) * ‖rdU U F k x.1‖ * (U.X k).nfac (laU U 0 n k) x.1 := by
  obtain ⟨hr, hty, -, -, hsec, -⟩ := hU
  haveI : IsDomain (CAt σ) := inferInstanceAs (IsDomain ℂ)
  haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  obtain ⟨b, hb, h, hun⟩ := GlobalTheory.ValNorm.exists_unit (U.X k) x.2
  obtain ⟨t, G, hbor, hG, hw⟩ := GlobalTheory.ValNorm.exists_frBor hσ U Uw k hr (hty k).1 (hty k).2 x b hb h
  obtain ⟨G', a₀, -, hG'⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c (CAt σ) y (U.un k ⟨_, h⟩)).1
    (hG.1.trans hchg.1.symm)
  have hts : (t none : CAt σ) = a₀ * s :=
    ((GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c (CAt σ) _ _).2 _ _ _ _ hG
      ((GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c (CAt σ) _ _ _).2 _ _ _ _ hchg hG')).2
  obtain ⟨hv0, hv1⟩ := GlobalTheory.T.theta_l2_family_uniform_compare hL hL2 E H Dw l Xo c σ _ _ Uw.F _ _ _ _ y _ G' _ v 1 hPm
    (Uw.period k ⟨_, h⟩) hy (Uw.lie k ⟨_, h⟩).1 hG' hv (Uw.norm k ⟨_, h⟩ hun)
  obtain ⟨hB, hS⟩ := (GlobalTheory.T.framedPoint_eval_natural_weight_scaling E H Dw l Xo c hEv a n F hF (CAt σ)).2 inferInstance
  have hrd : ∀ z : (U.X k).dom, rdU U F k z.1 = toC (evR Xo c F (U.un k z)) := fun z => dif_pos z.2
  have e1 : toC (evR Xo c F y) = toC s ^ n * rdU U F k x.1 := by
    rw [hrd]; exact hS s _ _ hchg
  have e2 : toC (wchar (ex Dw a n) t) * rdU U F k x.1 = bchar (laU U a n k) b * rdU U F k x.1 := by
    rw [← (hsec a n hD F hF k).2.1 x.1 x.2 b hb, hrd x]
    exact ((hrd ⟨_, h⟩).trans (hB t _ _ hbor)).symm
  have e3 : (U.X k).nfac (laU U 0 n k) x.1 = ‖bchar (laU U 0 n k) b‖ := by
    rw [← GlobalTheory.NormFactor.norm_bchar_mul_nfac_rmul (U.X k) _ x.2 hb]
    unfold Data.nfac
    simp only [norm_div, hun, div_one, Real.one_rpow, Finset.prod_const_one, mul_one]
  refine ⟨e1, ?_⟩
  rw [e1, e3]
  by_cases hP : rdU U F k x.1 = 0
  · simp [hP]
  have e4 := hw a n
  rw [mul_right_cancel₀ hP e2, mul_comm] at e4
  have e5 := mul_right_cancel₀ (ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.bchar_ne (U.X k) _ hb) e4
  have e6 : toC (t none : CAt σ) = toC (a₀ : CAt σ) * toC s := hts
  have e7 : v ^ ((n : ℝ) / 2) * ‖toC (a₀ : CAt σ)‖ ^ n = 1 := by
    obtain ⟨m, rfl⟩ := hD.2
    have hv1' : 1 = ‖toC (a₀ : CAt σ)‖ ^ 2 * v := hv1
    rw [show (((m + m : ℕ) : ℝ) / 2) = (m : ℝ) by push_cast; ring, Real.rpow_natCast, ← two_mul, pow_mul,
      ← mul_pow, mul_comm, ← hv1', one_pow]
  rw [e5, e6, norm_mul, norm_pow, norm_pow, norm_mul, mul_pow]
  linear_combination (-(‖toC s‖ ^ n * ‖rdU U F k x.1‖)) * e7

theorem tau_col_const [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] {O : Type} [CommRing O]
    {β : O →+* c.F} {Y : Model Xo c β} {a : ArcIn Dw l β ℂ (σ.comp β)} {χ : Sp (PowerSeries ℂ) ⟶ Y.X} {W : Wit Y a χ}
    {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty}
    (Ha : HolArc Y σ a χ W Fu) {th : a.D₀.P.L.Sec} (Θ : ThetaDat Ha th) (w w' : ℂ) (j k : Fin g) (hk : k ∉ Θ.S) :
    Θ.τ w j k = Θ.τ w' j k := by
  obtain ⟨nn, h1, -, -, h4, -⟩ := GlobalTheory.ArcQ.holArc_nilpotent E H Dw l Xo c σ O β Y a χ W g ty Fu Ha
  have hy : Ha.y (Θ.bas (Pi.single (.inr k) 1)) = 0 := (Θ.ker _).2 fun k' hk' =>
    Pi.single_eq_of_ne (fun h => hk (by rwa [← Sum.inr_injective h])) _
  have hN : Ha.N (Θ.bas (Pi.single (.inr k) 1)) = 0 := by rw [h1, h4 _ hy, map_zero]
  have e := (Θ.per w k).2
  rw [Ha.Pw_eq, hN, smul_zero, ← smul_zero w', ← hN, ← Ha.Pw_eq, (Θ.per w' k).2] at e
  simpa using (congrFun e j).symm

theorem coeff_evR_eq_fj : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) [Algebra c.F ℂ⸨X⸩] (th : a.D₀.P.L.Sec) (ξ : Module.Dual ℤ a.D₀.X) (ν₀ : E) (jj : ℤ) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), GlobalTheory.Reg.EvLaws Xo c → GoodEmb c σ → IsUnf U → (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp β) → Mono (spMap β) → PushInvertible Y.t.G Y.t.PP.L → ThNZ th → Module.finrank (𝓞 E) a.D₀.X = 1 → ξ ≠ 0 → BetaAt ξ l.M' a.be ν₀ jj → Dom a' n → (∀ k, TransvIn (U.X k) l.M' (laU U a' n k)) → ∀ w₁ : ℂ, Ha.T < w₁.im → ∃ (k : U.Comp) (ξ' : Fin r → E) (sE : E) (C : ℝ), (U.X k).IsIso ξ' ∧ IsBePar ξ a.be sE ∧ (∀ τ : (U.X k).Ψ, 0 < (τ.1 sE).re) ∧ (∀ (N : ℕ) (s : E), LevelPar ξ N s → ∀ v ∈ (U.X k).Λ, ∃ u ∈ (U.X k).Λ, (transvMat (U.X k).Gm ξ' (s * (U.X k).κ0)).mulVec v - v = (N : E) • u) ∧ 0 < C ∧ (∀ v, Arch.IsThNormAt a.D₀.P a.D₀.rig th (RingHom.id ℂ) v → C ≤ v * Real.sqrt |((NumberField.discr E : ℤ) : ℝ)|) ∧ ∀ (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR ℂ)) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)) (y : FrPt Xo c ℂ⸨X⸩), IsArcFr W e th (HahnSeries.ofPowerSeries ℤ ℂ) y → (∀ τ i, AnVec Ha (e τ i) (z τ i)) → ∃ (x : (U.X k).dom) (κ : ℂ), ∃ (L : (Fin Uw.g → ℂ) ≃ₗ[ℂ] (Fin Uw.g → ℂ)) (γ : (Uw.F.Di Ha.i).La ≃ₗ[𝓞 E] (Uw.F.Di (Uw.ik k)).La), (∀ v, Uw.Pm k x (γ v) = L (Ha.Pw w₁ v)) ∧ (∀ v v', (Uw.F.Di (Uw.ik k)).EF (γ v) (γ v') = (Uw.F.Di Ha.i).EF v v') ∧ (∀ τ i, L (z τ i) = Pi.single (Uw.e.symm ⟨τ, i⟩) 1) ∧ (∃ t, (∀ v', -(Uw.F.Di Ha.i).EF t v' = ξ (Ha.y v')) ∧ (Uw.φ k (γ t) : Fin r → E) = ξ') ∧ ‖κ‖ = (C * ∏ τ, ((U.X k).tt ξ' x.1 τ)⁻¹) ^ ((n : ℝ) / 2) * (U.X k).nfac (laU U 0 n k) x.1 ∧ ∀ F ∈ sec Xo c a' n, (U.X k).IsBddSec (laU U a' n k) (rdU U F k) → (evR Xo c F y).coeff jj * eTwoPi w₁ ^ jj = κ * (U.X k).fj (laU U a' n k) ξ' (fun τ => (τ.1 ν₀).re) (rdU U F k) x.1 := by
  intro hL hL2 E _ _ _ H Dw l Xo c σ r U Uw _ _ O _ β Y a χ W Ha _ th ξ ν₀ jj a' n hEv hσ hU halg hχ hmono hpush hth
    hrk hξ0 hβ hD hTr w₁ hw₁
  obtain ⟨Θ⟩ := GlobalTheory.ArcTheta.nonempty_thetaDat hL hL2 E H Dw l Xo c σ O β Y a χ W _ _ Uw.F Ha
    ((GlobalTheory.Relab.relab_good E H l c σ hσ).2.2.2 Dw Uw.g Uw.e) th hth
  obtain ⟨k, ξ', sE, hiso, hbe, hpos, hlev, hdict⟩ :=
    GlobalTheory.ArcFlow.holArc_eq_flow_orbit hL hL2 E H Dw l Xo c σ r U Uw O β Y a χ W Ha hσ hU hrk ξ hξ0 w₁ hw₁
  obtain ⟨C₀, hC₀, hC₀', hcov⟩ := GlobalTheory.LatticeCovolumeL2.det_im_eq_covol E H Dw l Xo c σ r U Uw O β Y a χ W Ha th Θ k ξ' hσ hU hiso hrk
  set B : ℝ := ‖Θ.κ‖ ^ 2 * (Real.sqrt (2 ^ (Uw.g - Θ.S.card) * ((((Θ.τ w₁).map Complex.im).submatrix
    (fun k : {k // k ∉ Θ.S} => k.1) (fun k : {k // k ∉ Θ.S} => k.1)).det)))⁻¹ with hBdef
  have hB : 0 < B := by
    have h1 := ((Θ.pos w₁ hw₁).2.submatrix (e := fun k : {k // k ∉ Θ.S} => k.1) Subtype.val_injective).det_pos
    have h2 := norm_pos_iff.2 Θ.κ_ne
    positivity
  refine ⟨k, ξ', sE, B * C₀, hiso, hbe, hpos, hlev, mul_pos hB hC₀, fun v hv => ?_, fun e z y hy hz => ?_⟩
  · rw [GlobalTheory.T.abelianPart_sectionNormSq_eq_thetaData hL hL2 E H Dw l Xo c σ O β Y a χ W _ _ Uw.F Ha th Θ w₁ v hw₁ hv]
    exact mul_le_mul_of_nonneg_left hC₀' hB.le
  have hzt := GlobalTheory.T.arc_letter_analyticVectors_independent_blockType hL hL2 E H Dw l Xo c σ r U Uw O β Y a χ W Ha y e th z hσ halg (GlobalTheory.ThetaShiftProofs.mono_j Y hmono) hy hz
  obtain ⟨x, hx, L, γ, hEF, hLz, ⟨t, ht, htξ⟩, hflow⟩ := hdict z hzt
  obtain ⟨T', hT'⟩ := GlobalTheory.T.hasSum_sectionValue_arc_framedPoint hL hL2 E H Dw l Xo c σ O β Y a χ W _ _ Uw.F Ha y e th Θ z hEv halg hχ hmono hpush hth hy hz
  set K : ℝ := (B * C₀ * ∏ τ, ((U.X k).tt ξ' x τ)⁻¹) ^ ((n : ℝ) / 2) * (U.X k).nfac (laU U 0 n k) x with hKdef
  have htt : ∀ x' ∈ (U.X k).dom, 0 < ∏ τ, ((U.X k).tt ξ' x' τ)⁻¹ := fun x' hx' =>
    Finset.prod_pos fun τ _ => inv_pos.2 (GlobalTheory.FjCauchy.tt_pos _ hiso hx' τ)
  have hK : 0 < K := mul_pos (Real.rpow_pos_of_pos (mul_pos (mul_pos hB hC₀) (htt x hx)) _)
    (MinimumGrowthBounds.nfac_pos _ _ hx)
  let fl : ℂ → Frame (U.X k).Ψ r := fun w => (U.X k).flow ξ' (fun τ => (w - w₁) * ((τ.1 sE).re : ℂ)) x
  have key : ∀ w : ℂ, ∃ cw : ℂ, max Ha.T T' < w.im → ∀ F ∈ sec Xo c a' n,
      HasSum (fun m : ℤ => (evR Xo c F y).coeff m * eTwoPi w ^ m) (cw * rdU U F k (fl w)) ∧
        ‖cw * rdU U F k (fl w)‖ = K * ‖rdU U F k (fl w)‖ := by
    intro w
    by_cases hw : max Ha.T T' < w.im
    swap
    · exact ⟨0, fun h => absurd h hw⟩
    obtain ⟨hw1, hw2⟩ := max_lt_iff.1 hw
    obtain ⟨hxw, hPm, hlie⟩ := hflow w hw1
    obtain ⟨yw, hyw, -⟩ := GlobalTheory.ArcQ.AnFrEx.existsUnique_anFr hL hL2 E H Dw l Xo c σ r U Uw O β Y a χ W Ha th Θ z hσ hzt w hw1
    obtain ⟨s, hs⟩ := frChg_of_anLie Uw.F Ha.i _ (Ha.period w hw1) _ _ z hlie hyw.1
    have hv := GlobalTheory.ThetaSquareIntegrable.theta_l2_of_analytic_generator E H Dw l Xo c σ O β Y a χ W _ _ Uw.F Ha th Θ w yw hw1 hyw.1.1 hyw.2
    have hoff : (((Θ.τ w).map Complex.im).submatrix (fun k : {k // k ∉ Θ.S} => k.1) (fun k : {k // k ∉ Θ.S} => k.1)) =
        (((Θ.τ w₁).map Complex.im).submatrix (fun k : {k // k ∉ Θ.S} => k.1) (fun k : {k // k ∉ Θ.S} => k.1)) := by
      ext i j
      exact congrArg Complex.im (tau_col_const Ha Θ w w₁ i.1 j.1 j.2)
    rw [hcov w ⟨_, hxw⟩ L γ hw1 hPm hEF ⟨t, fun v' hv' => by
      have := ht v'
      rwa [hv', map_zero, neg_eq_zero] at this, htξ⟩, hoff, ← mul_assoc, ← mul_assoc, ← hBdef] at hv
    refine ⟨toC s ^ n, fun _ F hF => ?_⟩
    obtain ⟨e1, e2⟩ := evR_eq_and_norm hL hL2 U Uw hEv hσ hU k ⟨_, hxw⟩ yw s _ hs Ha.i _ (Ha.period w hw1) hyw.1.1 hv
      a' n F hD hF
    have hsum : HasSum (fun m => (evR Xo c F y).coeff m * eTwoPi w ^ m) (toC (evR Xo c F yw)) :=
      hT' w hw2 yw hyw a' n F hF
    rw [e1] at hsum e2
    refine ⟨hsum, e2.trans ?_⟩
    have hn := GlobalTheory.ArcQ.nfac_parallel_flow E H Dw l Xo c σ r U k n ξ' hD.2 hiso x hx _ hxw
    rw [hKdef, Real.mul_rpow (mul_pos hB hC₀).le (htt _ hxw).le, Real.mul_rpow (mul_pos hB hC₀).le (htt _ hx).le]
    dsimp only [fl]
    linear_combination ((B * C₀) ^ ((n : ℝ) / 2) * ‖rdU U F k (fl w)‖) * hn
  choose cw hcw using key
  have hfl : Differentiable ℂ fl := (FlowMeanContinuity.flow_differentiable (U.X k) ξ' x).comp (by fun_prop)
  obtain ⟨κ, hκ, hκ'⟩ := GlobalTheory.exists_const_ratio_of_norm_eq {F // F ∈ sec Xo c a' n} (max Ha.T T') K
    (fun F w => cw w * rdU U F.1 k (fl w)) (fun F w => rdU U F.1 k (fl w)) cw hK
    (fun F => ⟨differentiableOn_of_hasSum _ _ _ fun w hw => (hcw w hw F.1 F.2).1,
      (hU.2.2.2.2.1 a' n hD F.1 F.2 k).1.comp hfl.differentiableOn
        fun w hw => (hflow w (max_lt_iff.1 hw).1).1⟩)
    (fun F w hw => ⟨rfl, (hcw w hw F.1 F.2).2⟩)
  refine ⟨⟨x, hx⟩, κ, L, γ, fun v => ?_, hEF, hLz, ⟨t, ht, htξ⟩, hκ, fun F hF hbdd => ?_⟩
  · obtain ⟨h1, h2, -⟩ := hflow w₁ hw₁
    rw [← h2 v]
    congr 3
    simp only [sub_self, zero_mul]
    exact (EmbeddingHermitianPairs.flow_zero _ _ _).symm
  · refine coeff_eq_of_betaAt (U.X k) hbdd hiso hx ξ l.M' a.be
      (fun y z => (dvd_mul_left _ 2).trans (a.be_dvd y z)) hβ hbe hpos (hTr k) (hlev _) κ w₁ _ (max Ha.T T')
      fun w hw => ?_
    exact hκ' ⟨F, hF⟩ w hw ▸ (hcw w hw F hF).1

end GlobalTheory.ArcCoeff
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LaurentCoeffSectionValueArcEqFourierJacobiStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open Formalism.L2.Pj hiding Unf GoodEmb relab toC perFr laU
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurentCoeff_sectionValue_arc_eq_fourierJacobi : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) [Algebra c.F ℂ⸨X⸩] (th : a.D₀.P.L.Sec) (ξ : Module.Dual ℤ a.D₀.X) (ν₀ : E) (jj : ℤ) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), GlobalTheory.Reg.EvLaws Xo c → GoodEmb c σ → IsUnf U → (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp β) → Mono (spMap β) → PushInvertible Y.t.G Y.t.PP.L → ThNZ th → Module.finrank (𝓞 E) a.D₀.X = 1 → ξ ≠ 0 → BetaAt ξ l.M' a.be ν₀ jj → Dom a' n → (∀ k, TransvIn (U.X k) l.M' (laU U a' n k)) → ∀ w₁ : ℂ, Ha.T < w₁.im → ∃ (k : U.Comp) (ξ' : Fin r → E) (sE : E) (C : ℝ), (U.X k).IsIso ξ' ∧ IsBePar ξ a.be sE ∧ (∀ τ : (U.X k).Ψ, 0 < (τ.1 sE).re) ∧ (∀ (N : ℕ) (s : E), LevelPar ξ N s → ∀ v ∈ (U.X k).Λ, ∃ u ∈ (U.X k).Λ, (transvMat (U.X k).Gm ξ' (s * (U.X k).κ0)).mulVec v - v = (N : E) • u) ∧ 0 < C ∧ (∀ v, Arch.IsThNormAt a.D₀.P a.D₀.rig th (RingHom.id ℂ) v → C ≤ v * Real.sqrt |((NumberField.discr E : ℤ) : ℝ)|) ∧ ∀ (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR ℂ)) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)) (y : FrPt Xo c ℂ⸨X⸩), IsArcFr W e th (HahnSeries.ofPowerSeries ℤ ℂ) y → (∀ τ i, AnVec Ha (e τ i) (z τ i)) → ∃ (x : (U.X k).dom) (κ : ℂ), ∃ (L : (Fin Uw.g → ℂ) ≃ₗ[ℂ] (Fin Uw.g → ℂ)) (γ : (Uw.F.Di Ha.i).La ≃ₗ[𝓞 E] (Uw.F.Di (Uw.ik k)).La), (∀ v, Uw.Pm k x (γ v) = L (Ha.Pw w₁ v)) ∧ (∀ v v', (Uw.F.Di (Uw.ik k)).EF (γ v) (γ v') = (Uw.F.Di Ha.i).EF v v') ∧ (∀ τ i, L (z τ i) = Pi.single (Uw.e.symm ⟨τ, i⟩) 1) ∧ (∃ t, (∀ v', -(Uw.F.Di Ha.i).EF t v' = ξ (Ha.y v')) ∧ (Uw.φ k (γ t) : Fin r → E) = ξ') ∧ ‖κ‖ = (C * ∏ τ, ((U.X k).tt ξ' x.1 τ)⁻¹) ^ ((n : ℝ) / 2) * (U.X k).nfac (laU U 0 n k) x.1 ∧ ∀ F ∈ sec Xo c a' n, (U.X k).IsBddSec (laU U a' n k) (rdU U F k) → (evR Xo c F y).coeff jj * eTwoPi w₁ ^ jj = κ * (U.X k).fj (laU U a' n k) ξ' (fun τ => (τ.1 ν₀).re) (rdU U F k) x.1 := by
  first | exact @GlobalTheory.ArcCoeff.coeff_evR_eq_fj | exact GlobalTheory.ArcCoeff.coeff_evR_eq_fj | (intros; apply GlobalTheory.ArcCoeff.coeff_evR_eq_fj <;> assumption)
end
