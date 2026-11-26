module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultiplierPowerUnitConstant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledStabilizerWeilOperatorTransportsLatticeEi

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFactorFlatLineEqGramOrthonormalFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousNormFactorFlatLineOrthonormalFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousNormFactorFlatLineOrthonormalFrame
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OrthoFlatFac

theorem sum_wtOf_flatWt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) (τ : Psi H) :
    (∑ ρ : E →+* ℂ, ∑ i : Fin (Dw.mult ρ), (((wtOf Dw (flatWt Dw τ) 0).1 (ρ, i) : ℤ) : ℝ)) = (Dw.q : ℝ) - Dw.p := by
  classical
  have key : ∀ ρ : E →+* ℂ, ∑ i : Fin (Dw.mult ρ), (((wtOf Dw (flatWt Dw τ) 0).1 (ρ, i) : ℤ) : ℝ) =
      (if ρ = conjEmb τ.1 then (Dw.q : ℝ) else 0) - if ρ = τ.1 then (Dw.p : ℝ) else 0 := fun ρ => by
    by_cases h : ρ (H.rt : E) = H.rt0
    · have hm : Dw.mult ρ = Dw.p := if_pos h
      have h1 : ρ ≠ conjEmb τ.1 := fun e => conj_not_mem τ (e ▸ h)
      have h2 : ∀ i : Fin (Dw.mult ρ), (wtOf Dw (flatWt Dw τ) 0).1 (ρ, i) = if ρ = τ.1 then -1 else 0 := fun i =>
        (wtOf_big (flatWt Dw τ) 0 ⟨ρ, h⟩ i (hm ▸ i.2)).trans (by simp [flatWt, parWt, Subtype.ext_iff])
      simp only [h2]
      split_ifs <;> simp_all
    · have hm : Dw.mult ρ = Dw.q := if_neg h
      have h1 : ρ ≠ τ.1 := fun e => h (e ▸ τ.2)
      have h2 : ∀ i : Fin (Dw.mult ρ), (wtOf Dw (flatWt Dw τ) 0).1 (ρ, i) = if ρ = conjEmb τ.1 then 1 else 0 :=
        fun i => by
          have := wtOf_small (flatWt Dw τ) 0 ⟨_, conj_mem h⟩ i (hm ▸ i.2)
          simp only [Formalism.L2.Pj.conjEmb_conjEmb] at this
          rw [this]
          by_cases e : ρ = conjEmb τ.1
          · simp [flatWt, parWt, e, Formalism.L2.Pj.conjEmb_conjEmb]
          · have : conjEmb ρ ≠ τ.1 := fun e' => e (by rw [← e', Formalism.L2.Pj.conjEmb_conjEmb])
            simp [flatWt, parWt, Subtype.ext_iff, e, this]
      simp only [h2]
      split_ifs <;> simp_all
  simp only [key, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem homFac_flatWt_ortho : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (x : ℝ)
    (τ : Psi H) (k : U.Comp) (w : (U.X k).dom), (U.X k).IsOrtho w.1 →
    GlobalTheory.CompHS.homFac U x (flatWt Dw τ) k w = Real.exp (((Dw.p : ℝ) - Dw.q) / 2 * Real.log (2 * Real.pi * x)) := by
  intro E _ _ _ H Dw l Xo c σ r U x τ k w ho
  rw [GlobalTheory.CompHS.homFac, GlobalTheory.OrbitNfac.nfac_ortho _ ho, mul_one, lieFacZ, sum_wtOf_flatWt]
  congr 1
  ring

end GlobalTheory.OrthoFlatFac
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousNormFactorFlatLineOrthonormalFrameStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneousNormFactor_flatLine_orthonormalFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (x : ℝ) (τ : Psi H) (k : U.Comp) (w : (U.X k).dom), (U.X k).IsOrtho w.1 → GlobalTheory.CompHS.homFac U x (flatWt Dw τ) k w = Real.exp (((Dw.p : ℝ) - Dw.q) / 2 * Real.log (2 * Real.pi * x)) := by
  first | exact @GlobalTheory.OrthoFlatFac.homFac_flatWt_ortho | exact GlobalTheory.OrthoFlatFac.homFac_flatWt_ortho | (intros; apply GlobalTheory.OrthoFlatFac.homFac_flatWt_ortho <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameGramDetEqUniformizationHermForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameGramDetEqUniformizationHermForm
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.LieGram

theorem form_eq_hermForm {K : Type} [Field K] {n g m : ℕ} (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin n → K)) (σ : K →+* ℂ)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (Wc : Fin n → Fin g → ℂ)
    (hform : ∀ i j, h.form σ (Pi.single i 1) (Pi.single j 1) = Real.pi * hermForm Hm (Wc j) (Wc i))
    (v : Fin m → Fin n → K) (i j : Fin m) :
    h.form σ (v i) (v j) = Real.pi * hermForm Hm (∑ k, σ (v j k) • Wc k) (∑ k, σ (v i k) • Wc k) := by
  have hsum : ∀ a : Fin n → K, a = ∑ k, a k • Pi.single k (1 : K) := fun a => by
    ext t; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hsum (v i), hsum (v j)]
  rw [GlobalTheory.HermFamFrame.form_sum_left]
  simp_rw [GlobalTheory.HermFamFrame.form_sum_right, hform]
  simp only [hermForm, Matrix.mulVec_sum, Matrix.mulVec_smul, star_sum, star_smul, dotProduct_sum,
    sum_dotProduct, smul_dotProduct, dotProduct_smul, Finset.mul_sum, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Complex.star_def]
  ring

theorem gram_det_re_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ (ρ : E →+* ℂ) (v : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ v → ∀ (σ : K →+* ℂ), GoodEmb c (σ.comp (algebraMap c.F K)) → ∀ (φ : K →ₐ[c.F] CAt (σ.comp (algebraMap c.F K))), (∀ a, toC (φ a) = σ a) → ∀ (z : FrPt Xo c (CAt (σ.comp (algebraMap c.F K)))), FrMap φ y z → ∀ (k : (U (σ.comp (algebraMap c.F K))).Comp) (w : ((U (σ.comp (algebraMap c.F K))).X k).dom) (W : ReciprocityTheory.ChartRestriction.G.PullbackSections.UnfAt (U (σ.comp (algebraMap c.F K))) k w) (Wu : ReciprocityTheory.ChartRestriction.G.PullbackSections.UnitAt W), z.x = ((U (σ.comp (algebraMap c.F K))).un k w).x → ∀ (C : Fin (Dw.mult ρ) → Fin (Dw.mult ρ) → CAt (σ.comp (algebraMap c.F K))), (∀ i, IsCombAt ((U (σ.comp (algebraMap c.F K))).un k w).x (((U (σ.comp (algebraMap c.F K))).un k w).u ρ) (C i) (z.u ρ i)) → (h.gram σ v).det.re = (Matrix.of fun i j : Fin (Dw.mult ρ) => (Real.pi : ℂ) * hermForm Wu.Hm (∑ l, toC (C j l) • Pi.single (W.e.symm ⟨ρ, l⟩) (1 : ℂ)) (∑ l, toC (C i l) • Pi.single (W.e.symm ⟨ρ, l⟩) (1 : ℂ))).det.re := by
  intro E _ _ _ H Dw l Xo c r U x hL K _ _ _ y B t₀ m1 m2 F h hH ρ v hv σ hσ φ hφ z hz k w W Wu hzx C hC
  obtain ⟨Q, ψ, v', u, Hm, χ, Wc, hfib, hAH, hvec, hform⟩ := hH σ
  obtain ⟨T, m, u', χ', hA', hw'⟩ := GlobalTheory.T.exists_fibre_uniformisation_appellHumbert_unit E H Dw l Xo c r _ _ hL.pos k w W Wu ρ z hzx C hC
  obtain ⟨f, hf, hLB, hq⟩ := GlobalTheory.T.complex_fibre_iso_universal_group_framed_point E H Dw l Xo c K y B t₀ m1 m2 F ρ v hv σ φ hφ z hz Q ψ v' hfib (fun i => (hvec i).1) T m
  choose w' hw'1 hw'2 using hw'
  have htan : ∀ i, IsTangent (v' i) := fun i => GlobalTheory.IsVecOver.isTangent hfib.2.1 (hvec i).1 (F.basis.1 i)
  obtain ⟨Lm, hL1, hL2⟩ := GlobalTheory.T.exists_linear_lift_preserving_appellHumbert_form Q T.pol W.g u Hm χ u' Wu.Hm χ' hAH hA' f hf hLB F.P₀.g v' Wc
    (fun i => ⟨htan i, (hvec i).2⟩) (Dw.mult ρ) (fun i k => σ (v i k)) w' _ hw'2
    (fun i q hq' => hq i q hq' (w' i) (hw'1 i))
  congr 2
  ext i j
  simp only [ReciprocityTheory.GeometryOfNumbersTheory.HermFam.gram, Matrix.of_apply]
  rw [form_eq_hermForm h σ Hm Wc hform v i j, ← hL1, hL2, hL2]

end GlobalTheory.LieGram
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameGramDetEqUniformizationHermFormStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_gram_det_eq_uniformization_hermForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ (ρ : E →+* ℂ) (v : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ v → ∀ (σ : K →+* ℂ), GoodEmb c (σ.comp (algebraMap c.F K)) → ∀ (φ : K →ₐ[c.F] CAt (σ.comp (algebraMap c.F K))), (∀ a, toC (φ a) = σ a) → ∀ (z : FrPt Xo c (CAt (σ.comp (algebraMap c.F K)))), FrMap φ y z → ∀ (k : (U (σ.comp (algebraMap c.F K))).Comp) (w : ((U (σ.comp (algebraMap c.F K))).X k).dom) (W : ReciprocityTheory.ChartRestriction.G.PullbackSections.UnfAt (U (σ.comp (algebraMap c.F K))) k w) (Wu : ReciprocityTheory.ChartRestriction.G.PullbackSections.UnitAt W), z.x = ((U (σ.comp (algebraMap c.F K))).un k w).x → ∀ (C : Fin (Dw.mult ρ) → Fin (Dw.mult ρ) → CAt (σ.comp (algebraMap c.F K))), (∀ i, IsCombAt ((U (σ.comp (algebraMap c.F K))).un k w).x (((U (σ.comp (algebraMap c.F K))).un k w).u ρ) (C i) (z.u ρ i)) → (h.gram σ v).det.re = (Matrix.of fun i j : Fin (Dw.mult ρ) => (Real.pi : ℂ) * hermForm Wu.Hm (∑ l, toC (C j l) • Pi.single (W.e.symm ⟨ρ, l⟩) (1 : ℂ)) (∑ l, toC (C i l) • Pi.single (W.e.symm ⟨ρ, l⟩) (1 : ℂ))).det.re := by
  first | exact @GlobalTheory.LieGram.gram_det_re_eq | exact GlobalTheory.LieGram.gram_det_re_eq | (intros; apply GlobalTheory.LieGram.gram_det_re_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDiagonalTorusCharacterFlatLineWeight
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDiagonalTorusCharacterFlatLineWeight
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS.FlatDiag

theorem norm_diagChar_flatWt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (σ : c.F →+* ℂ) (τ : Psi H) (t : Ix Dw → (CAt σ)ˣ), ‖GlobalTheory.CompHS.diagChar (exOf Dw (flatWt Dw τ) 0) t‖ = (∏ j : Fin (Dw.mult (conjEmb τ.1)), ‖toC ((t (some ⟨conjEmb τ.1, j⟩) : CAt σ))‖) / ∏ i : Fin (Dw.mult τ.1), ‖toC ((t (some ⟨τ.1, i⟩) : CAt σ))‖ := by
  classical
  intro E _ _ _ H Dw l c σ τ t
  set e := exOf Dw (flatWt Dw τ) 0 with he_def
  have hne : τ.1 ≠ conjEmb τ.1 := fun h => conj_not_mem τ (h ▸ τ.2)
  have hE : ∀ (ρ : E →+* ℂ) (i : Fin (Dw.mult ρ)),
      e (some ⟨ρ, i⟩) = if ρ = τ.1 then -1 else if ρ = conjEmb τ.1 then 1 else 0 := by
    intro ρ i
    obtain ⟨n, hi⟩ := i
    simp only [he_def, exOf, exZ, wtOf, flatWt, parWt, Datum.mult] at hi ⊢
    by_cases h : ρ (H.rt : E) = H.rt0
    · rw [if_pos h] at hi
      rw [dite_eq_left h, dite_eq_left hi]
      have h2 : ρ ≠ conjEmb τ.1 := fun e => conj_not_mem τ (e ▸ h)
      by_cases h1 : ρ = τ.1
      · subst h1
        simp
      · have h3 : (⟨ρ, h⟩ : Psi H) ≠ τ := fun e => h1 (congrArg Subtype.val e)
        simp [h1, h2, h3]
    · rw [if_neg h] at hi
      rw [dite_eq_right h]
      have h1 : ρ ≠ τ.1 := fun e => h (e ▸ τ.2)
      by_cases h' : conjEmb ρ (H.rt : E) = H.rt0
      · rw [dite_eq_left h', dite_eq_left hi]
        by_cases h2 : ρ = conjEmb τ.1
        · have h3 : (⟨conjEmb ρ, h'⟩ : Psi H) = τ := Subtype.ext (show conjEmb ρ = τ.1 by rw [h2, AllWt.conjEmb_conjEmb])
          rw [if_pos h3, if_neg h1, if_pos h2]
          norm_num
        · have h3 : (⟨conjEmb ρ, h'⟩ : Psi H) ≠ τ := fun e => h2 (by
            rw [← congrArg Subtype.val e, AllWt.conjEmb_conjEmb])
          rw [if_neg h3, if_neg h1, if_neg h2]
          norm_num
      · rw [dite_eq_right h']
        have h2 : ρ ≠ conjEmb τ.1 := fun e => h' (by rw [e, AllWt.conjEmb_conjEmb]; exact τ.2)
        simp [h1, h2]
  have e0 : e none = 0 := by simp [he_def, exOf, exZ, wtOf_snd]
  let f : (CAt σ)ˣ →* ℂˣ := Units.map (MonoidHom.id ℂ)
  have hf : ∀ u : (CAt σ)ˣ, ((f u : ℂˣ) : ℂ) = toC (u : CAt σ) := fun _ => rfl
  have e₁ : GlobalTheory.CompHS.diagChar e t = ((∏ ix, f (t ix) ^ e ix : ℂˣ) : ℂ) := by
    have : (∏ ix, f (t ix) ^ e ix) = f (∏ ix, t ix ^ e ix) := by simp only [map_prod, map_zpow]
    rw [this, hf]
    rfl
  let g : (E →+* ℂ) → ℝ := fun ρ => ∏ i : Fin (Dw.mult ρ), ‖toC ((t (some ⟨ρ, i⟩) : CAt σ))‖ ^ e (some ⟨ρ, i⟩)
  have e₂ : ‖GlobalTheory.CompHS.diagChar e t‖ = ∏ ρ, g ρ := by
    rw [e₁, Units.coe_prod, norm_prod, Fintype.prod_option, e0, zpow_zero, Units.val_one, norm_one, one_mul,
      Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun ρ _ => Finset.prod_congr rfl fun i _ => ?_
    rw [Units.val_zpow_eq_zpow_val, norm_zpow, hf]
  have e₃ : ∏ ρ, g ρ = g τ.1 * g (conjEmb τ.1) := by
    rw [← Finset.prod_pair hne]
    refine (Finset.prod_subset (Finset.subset_univ _) fun ρ _ hρ => ?_).symm
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hρ
    exact Finset.prod_eq_one fun i _ => by rw [hE, if_neg hρ.1, if_neg hρ.2, zpow_zero]
  have gτ : g τ.1 = (∏ i : Fin (Dw.mult τ.1), ‖toC ((t (some ⟨τ.1, i⟩) : CAt σ))‖)⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [hE, if_pos rfl, zpow_neg_one]
  have gc : g (conjEmb τ.1) = ∏ j : Fin (Dw.mult (conjEmb τ.1)), ‖toC ((t (some ⟨conjEmb τ.1, j⟩) : CAt σ))‖ :=
    Finset.prod_congr rfl fun i _ => by rw [hE, if_neg hne.symm, if_pos rfl, zpow_one]
  rw [e₂, e₃, gτ, gc, div_eq_mul_inv, mul_comm]

end GlobalTheory.CompHS.FlatDiag
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDiagonalTorusCharacterFlatLineWeightStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_diagonalTorusCharacter_flatLineWeight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (σ : c.F →+* ℂ) (τ : Psi H) (t : Ix Dw → (CAt σ)ˣ), ‖GlobalTheory.CompHS.diagChar (exOf Dw (flatWt Dw τ) 0) t‖ = (∏ j : Fin (Dw.mult (conjEmb τ.1)), ‖toC ((t (some ⟨conjEmb τ.1, j⟩) : CAt σ))‖) / ∏ i : Fin (Dw.mult τ.1), ‖toC ((t (some ⟨τ.1, i⟩) : CAt σ))‖ := by
  first | exact @GlobalTheory.CompHS.FlatDiag.norm_diagChar_flatWt | exact GlobalTheory.CompHS.FlatDiag.norm_diagChar_flatWt | (intros; apply GlobalTheory.CompHS.FlatDiag.norm_diagChar_flatWt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetGramLowerTriangularCoordVecRe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetGramLowerTriangularCoordVecRe
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
open scoped Matrix

theorem GlobalTheory.det_gram_lowerTriangular_coordVec_re : ∀ (g m : ℕ) (f : Fin m → Fin g), Function.Injective f → ∀ (a : ℝ) (C : Fin m → Fin m → ℂ), (∀ i j : Fin m, i < j → C i j = 0) → (Matrix.of fun i j : Fin m => (Real.pi : ℂ) * hermForm ((a : ℂ) • (1 : Matrix (Fin g) (Fin g) ℂ)) (∑ l, C j l • Pi.single (f l) (1 : ℂ)) (∑ l, C i l • Pi.single (f l) (1 : ℂ))).det.re = (Real.pi * a) ^ m * ∏ i, ‖C i i‖ ^ 2 := by
  intro g m f hf a C hC
  classical
  set A : Matrix (Fin m) (Fin m) ℂ := Matrix.of C with hA
  set P : Matrix (Fin m) (Fin g) ℂ := Matrix.of fun l k => (Pi.single (f l) (1:ℂ) : Fin g → ℂ) k with hP
  have hX : ∀ i, (∑ l, C i l • Pi.single (f l) (1:ℂ)) = fun k => (A * P) i k := by
    intro i; ext k; simp [Matrix.mul_apply, hP, hA, Finset.sum_apply]
  have hPP : P * Pᴴ = 1 := by
    ext l l'
    simp only [Matrix.mul_apply, hP, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
    simp [Pi.single_apply, hf.eq_iff, eq_comm]
  have hH : ∀ u v : Fin g → ℂ, hermForm ((a : ℂ) • (1 : Matrix (Fin g) (Fin g) ℂ)) u v = (a:ℂ) * (u ⬝ᵥ star v) := by
    intro u v
    rw [hermForm, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
  have hE : (Matrix.of fun i j : Fin m => (Real.pi : ℂ) * hermForm ((a : ℂ) • (1 : Matrix (Fin g) (Fin g) ℂ)) (∑ l, C j l • Pi.single (f l) (1 : ℂ)) (∑ l, C i l • Pi.single (f l) (1 : ℂ))) = ((Real.pi : ℂ) * a) • (A * Aᴴ)ᵀ := by
    ext i j
    rw [Matrix.of_apply, hX, hX, hH]
    have : (fun k => (A * P) j k) ⬝ᵥ star (fun k => (A * P) i k) = ((A * P) * (A * P)ᴴ) j i := by
      rw [Matrix.mul_apply]; simp only [dotProduct, Matrix.conjTranspose_apply, Pi.star_apply]
    rw [this, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc P, hPP, Matrix.one_mul]
    rw [Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul]; ring
  have hlow : A.BlockTriangular OrderDual.toDual := by
    intro i j hij
    exact hC i j hij
  rw [hE, Matrix.det_smul, Matrix.det_transpose, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_of_lowerTriangular A hlow]
  have : (∏ i, A i i) * star (∏ i, A i i) = ((∏ i, ‖C i i‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    simp [hA, Finset.prod_pow, norm_prod]
  rw [this, Fintype.card_fin]
  rw [show ((Real.pi : ℂ) * a) ^ m = (((Real.pi * a) ^ m : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_mul, Complex.ofReal_re]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetGramLowerTriangularCoordVecReStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_gram_lowerTriangular_re_eq_pi_mul_pow : ∀ (g m : ℕ) (f : Fin m → Fin g), Function.Injective f → ∀ (a : ℝ) (C : Fin m → Fin m → ℂ), (∀ i j : Fin m, i < j → C i j = 0) → (Matrix.of fun i j : Fin m => (Real.pi : ℂ) * hermForm ((a : ℂ) • (1 : Matrix (Fin g) (Fin g) ℂ)) (∑ l, C j l • Pi.single (f l) (1 : ℂ)) (∑ l, C i l • Pi.single (f l) (1 : ℂ))).det.re = (Real.pi * a) ^ m * ∏ i, ‖C i i‖ ^ 2 := by
  first | exact @GlobalTheory.det_gram_lowerTriangular_coordVec_re | exact GlobalTheory.det_gram_lowerTriangular_coordVec_re | (intros; apply GlobalTheory.det_gram_lowerTriangular_coordVec_re <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFactorFlatLineEqGramOrthonormalFrame
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

noncomputable section

namespace GlobalTheory.PtDegOrtho

theorem homFac_eq_gram_ortho : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (τ : Psi H) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ (u : Fin (Dw.mult τ.1) → Fin F.P₀.g → K) (u' : Fin (Dw.mult (conjEmb τ.1)) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F τ.1 u → GlobalTheory.PtDeg.FrameCoord y m1 m2 F (conjEmb τ.1) u' → ∀ (σ : K →+* ℂ), GoodEmb c (σ.comp (algebraMap c.F K)) → ∀ (φ : K →ₐ[c.F] CAt (σ.comp (algebraMap c.F K))), (∀ a, toC (φ a) = σ a) → ∀ (z : FrPt Xo c (CAt (σ.comp (algebraMap c.F K)))), FrMap φ y z → ∀ (k : (U (σ.comp (algebraMap c.F K))).Comp) (w : ((U (σ.comp (algebraMap c.F K))).X k).dom) (t : Ix Dw → (CAt (σ.comp (algebraMap c.F K)))ˣ), ((U (σ.comp (algebraMap c.F K))).X k).IsOrtho w.1 → FrBor t ((U (σ.comp (algebraMap c.F K))).un k w) z → GlobalTheory.CompHS.homFac (U (σ.comp (algebraMap c.F K))) x (flatWt Dw τ) k w = ‖GlobalTheory.CompHS.diagChar (exOf Dw (flatWt Dw τ) 0) t‖ * Real.sqrt (h.gram σ u).det.re / Real.sqrt (h.gram σ u').det.re := by
  intro E _ _ _ H Dw l Xo c r U x hL τ K _ _ _ y B t₀ m1 m2 F h hh u u' hu hu' σ hσ φ hφ z hz k w t hort hbor
  have hU := hL.unf _ hσ
  obtain ⟨W⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.nonempty_unfAt hU k w
  obtain ⟨Wu⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.nonempty_unitAt W (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.dmin_ortho _ hort)
  have hHm := GlobalTheory.OrthoHerm.hm_eq_smul_one E H Dw l Xo c _ r (U _) x hσ hU k w W Wu (hL.xi _ hσ k) hort
  obtain ⟨hzx, hcomb, -⟩ := hbor
  choose C hCi hCup hCc using hcomb
  have hp : Dw.mult τ.1 = Dw.p := by unfold Datum.mult; rw [if_pos τ.2]
  have hq : Dw.mult (conjEmb τ.1) = Dw.q := by unfold Datum.mult; rw [if_neg (conj_not_mem τ)]

  have hx : 0 < x := by
    have hne : Nonempty (Σ ρ : E →+* ℂ, Fin (Dw.mult ρ)) := by
      rcases Nat.eq_zero_or_pos Dw.p with h0 | h0
      · have hq1 : 0 < Dw.q := by have := hL.pos; omega
        exact ⟨⟨conjEmb τ.1, ⟨0, hq ▸ hq1⟩⟩⟩
      · exact ⟨⟨τ.1, ⟨0, hp ▸ h0⟩⟩⟩
    obtain ⟨j0⟩ := hne
    have h1 := Wu.pos (Pi.single (W.e.symm j0) 1) (by simp)
    rw [hHm] at h1
    have h2 : hermForm (((2 * x : ℝ) : ℂ) • (1 : Matrix (Fin W.g) (Fin W.g) ℂ)) (Pi.single (W.e.symm j0) 1)
        (Pi.single (W.e.symm j0) 1) = ((2 * x : ℝ) : ℂ) := by
      simp [hermForm, Matrix.smul_mulVec, dotProduct, Pi.single_apply]
    rw [h2, Complex.ofReal_re] at h1
    linarith
  have key : ∀ (ρ : E →+* ℂ) (v : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ v →
      (h.gram σ v).det.re = (2 * Real.pi * x) ^ (Dw.mult ρ) *
        (∏ i : Fin (Dw.mult ρ), ‖toC ((t (some ⟨ρ, i⟩) : CAt (σ.comp (algebraMap c.F K))))‖) ^ 2 := by
    intro ρ v hv
    rw [GlobalTheory.T.frame_gram_det_eq_uniformization_hermForm E H Dw l Xo c r U x hL K y B t₀ m1 m2 F h hh ρ v hv σ hσ φ hφ z hz k w W Wu hzx (C ρ) (hCc ρ), hHm,
      GlobalTheory.T.det_gram_lowerTriangular_re_eq_pi_mul_pow W.g (Dw.mult ρ) (fun l => W.e.symm ⟨ρ, l⟩) (fun a b e => by simpa using e) (2 * x)
        (fun i j => toC (C ρ i j)) (fun i j hij => by simp only [hCup ρ i j hij]; rfl), ← Finset.prod_pow]
    simp only [hCi]
    congr 1
    ring
  rw [GlobalTheory.T.homogeneousNormFactor_flatLine_orthonormalFrame E H Dw l Xo c _ r (U _) x τ k w hort, GlobalTheory.T.norm_diagonalTorusCharacter_flatLineWeight E H Dw l c _ τ t, key _ u hu, key _ u' hu']
  have e1 : (2 * Real.pi * x) ^ (Dw.mult τ.1) = (2 * Real.pi * x) ^ Dw.p := by rw [hp]
  have e2 : (2 * Real.pi * x) ^ (Dw.mult (conjEmb τ.1)) = (2 * Real.pi * x) ^ Dw.q := by rw [hq]
  rw [e1, e2]
  have hpos : ∀ ρ : E →+* ℂ, 0 < ∏ i : Fin (Dw.mult ρ), ‖toC ((t (some ⟨ρ, i⟩) : CAt (σ.comp (algebraMap c.F K))))‖ :=
    fun ρ => Finset.prod_pos fun i _ => norm_pos_iff.2 (Units.ne_zero (M₀ := ℂ) _)
  have hP := hpos τ.1
  have hP' := hpos (conjEmb τ.1)
  generalize ∏ i : Fin (Dw.mult τ.1), ‖toC ((t (some ⟨τ.1, i⟩) : CAt (σ.comp (algebraMap c.F K))))‖ = P at *
  generalize ∏ i : Fin (Dw.mult (conjEmb τ.1)), ‖toC ((t (some ⟨conjEmb τ.1, i⟩) : CAt (σ.comp (algebraMap c.F K))))‖ = P' at *
  have ha : 0 < 2 * Real.pi * x := by positivity
  have hs : ∀ n : ℕ, Real.sqrt ((2 * Real.pi * x) ^ n) = Real.exp ((n : ℝ) / 2 * Real.log (2 * Real.pi * x)) := by
    intro n
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ha.le, Real.rpow_def_of_pos ha]
    congr 1
    ring
  rw [Real.sqrt_mul (pow_nonneg ha.le _), Real.sqrt_mul (pow_nonneg ha.le _), Real.sqrt_sq hP.le, Real.sqrt_sq hP'.le,
    hs, hs]
  have hq2 : Real.exp (((Dw.p : ℝ) - Dw.q) / 2 * Real.log (2 * Real.pi * x)) * Real.exp ((Dw.q : ℝ) / 2 * Real.log (2 * Real.pi * x)) =
      Real.exp ((Dw.p : ℝ) / 2 * Real.log (2 * Real.pi * x)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [← hq2]
  field_simp

end GlobalTheory.PtDegOrtho
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFactorFlatLineEqGramOrthonormalFrameStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normFactor_flatLine_eq_gram_orthonormal_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (τ : Psi H) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ (u : Fin (Dw.mult τ.1) → Fin F.P₀.g → K) (u' : Fin (Dw.mult (conjEmb τ.1)) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F τ.1 u → GlobalTheory.PtDeg.FrameCoord y m1 m2 F (conjEmb τ.1) u' → ∀ (σ : K →+* ℂ), GoodEmb c (σ.comp (algebraMap c.F K)) → ∀ (φ : K →ₐ[c.F] CAt (σ.comp (algebraMap c.F K))), (∀ a, toC (φ a) = σ a) → ∀ (z : FrPt Xo c (CAt (σ.comp (algebraMap c.F K)))), FrMap φ y z → ∀ (k : (U (σ.comp (algebraMap c.F K))).Comp) (w : ((U (σ.comp (algebraMap c.F K))).X k).dom) (t : Ix Dw → (CAt (σ.comp (algebraMap c.F K)))ˣ), ((U (σ.comp (algebraMap c.F K))).X k).IsOrtho w.1 → FrBor t ((U (σ.comp (algebraMap c.F K))).un k w) z → GlobalTheory.CompHS.homFac (U (σ.comp (algebraMap c.F K))) x (flatWt Dw τ) k w = ‖GlobalTheory.CompHS.diagChar (exOf Dw (flatWt Dw τ) 0) t‖ * Real.sqrt (h.gram σ u).det.re / Real.sqrt (h.gram σ u').det.re := by
  first | exact @GlobalTheory.PtDegOrtho.homFac_eq_gram_ortho | exact GlobalTheory.PtDegOrtho.homFac_eq_gram_ortho | (intros; apply GlobalTheory.PtDegOrtho.homFac_eq_gram_ortho <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieAlgebraMetricConjEmbeddingEqConj
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieAlgebraMetricConjEmbeddingEqConj
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.ArchMetricCompare

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CM.LieMetricConj

variable {K : Type} [Field K]

theorem form_conj_of_single {g : ℕ} (h : HermFam K (Fin g → K)) (s : K →+* ℂ)
    (e : ∀ i j, h.form ((starRingEnd ℂ).comp s) (Pi.single i 1) (Pi.single j 1) =
      starRingEnd ℂ (h.form s (Pi.single i 1) (Pi.single j 1)))
    (a b : Fin g → K) : h.form ((starRingEnd ℂ).comp s) a b = starRingEnd ℂ (h.form s a b) := by
  have key : ∀ t : K →+* ℂ, h.form t a b =
      ∑ j, t (b j) * starRingEnd ℂ (∑ i, t (a i) * h.form t (Pi.single j 1) (Pi.single i 1)) := by
    intro t
    rw [LieMetric.form_sum_right h t a b]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← h.conj_symm t (Pi.single j 1) a, LieMetric.form_sum_right h t (Pi.single j 1) a]
  rw [key ((starRingEnd ℂ).comp s), key s]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, RingHom.comp_apply, e, Complex.conj_conj]

end GlobalTheory.CM.LieMetricConj

namespace GlobalTheory.CM.LieMetricConj

open GlobalTheory.ConjUnif

variable {K : Type} [Field K] [NumberField K]

theorem conj_conj_comp (s : K →+* ℂ) : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp s) = s :=
  RingHom.ext fun x => by simp

theorem single_conj (hU : ThetaUnifAV) {P : Out.PolAV (Sp (𝓞 K))} (F : GenFib P) (h : HermFam K (Fin F.P₀.g → K))
    (H : F.IsHerm h) (s : K →+* ℂ) (i j : Fin F.P₀.g) :
    h.form ((starRingEnd ℂ).comp s) (Pi.single i 1) (Pi.single j 1) =
      starRingEnd ℂ (h.form s (Pi.single i 1) (Pi.single j 1)) := by
  obtain ⟨Q, ψ, v, u, Hm, χ, W, a, b, c, d⟩ := H s
  obtain ⟨Q', ψ', v', u', Hm', χ', W', a', b', c', d'⟩ := H ((starRingEnd ℂ).comp s)
  obtain ⟨A'', _, ψc, hc⟩ : ∃ (A'' : Over (Sp ℂ)) (_ : GrpObj A'') (ψc : A''.left ⟶ Q'.A.left),
      IsGrpPullback A'' Q'.A cj ψc :=
    ⟨_, _, _, isGrpPullback_pullback Q'.A cj⟩
  let Q'' : Out.PolAV (Sp ℂ) := pullPol Q' hc
  have hQ : IsPolFibre (starRingEnd ℂ) Q' Q'' ψc := ⟨rfl, hc, ⟨idIso _, idIso_isGen (pull_isLB Q'.isLB ψc)⟩⟩
  have a'' : IsPolFibre s F.P₀ Q'' (ψc ≫ ψ') := by
    rw [← conj_conj_comp s]
    exact PolFibre.comp a' hQ
  choose v'' hv'' using fun k => (existsUnique_isVecOver hc.1 (v' k)).exists
  have ht : ∀ k, IsTangent (v' k) := fun k => (c' k).1.isTangent a'.2.1 (F.basis.1 k)
  have c'' : ∀ k, IsVecOver s (ψc ≫ ψ') (F.v k) (v'' k) ∧ (conjPull hc u').IsDiff (star (W' k)) (v'' k) := by
    intro k
    refine ⟨?_, cj_isDiff hc (pullId u') (ht k) (hv'' k) (c' k).2⟩
    rw [← conj_conj_comp s]
    exact (PolFibre.vec_iff a'.2.1.1 hc.1.w (c' k).1).1 (hv'' k)
  have e := LieMetric.hermForm_eq hU a a'' b (conjPull_isAH hc u' b') F.basis.1 c c'' j i
  rw [d, d', e]
  unfold hermForm
  rw [map_mul, Complex.conj_ofReal, star_star]
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    simp [dotProduct, Matrix.mulVec, map_sum, Complex.star_def]

theorem form_conj : ∀ (K : Type) [Field K] [NumberField K] (P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp (𝓞 K)))
    (F : GlobalTheory.CM.GenFib P) (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ (σ : K →+* ℂ)
    (a b : Fin F.P₀.g → K), h.form ((starRingEnd ℂ).comp σ) a b = starRingEnd ℂ (h.form σ a b) :=
  fun _ _ _ _ F h H σ a b => form_conj_of_single h σ (single_conj thetaUnifAV_all F h H σ) a b

end GlobalTheory.CM.LieMetricConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieAlgebraMetricConjEmbeddingEqConjStatement
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieAlgebraMetric_conjEmbedding_eq_conj : ∀ (K : Type) [Field K] [NumberField K] (P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp (𝓞 K))) (F : GlobalTheory.CM.GenFib P) (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ (σ : K →+* ℂ) (a b : Fin F.P₀.g → K), h.form ((starRingEnd ℂ).comp σ) a b = starRingEnd ℂ (h.form σ a b) := by
  first | exact @GlobalTheory.CM.LieMetricConj.form_conj | exact GlobalTheory.CM.LieMetricConj.form_conj | (intros; apply GlobalTheory.CM.LieMetricConj.form_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstLengthFlatSectionEqFrameNormComplexEmbeddin
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

noncomputable section

namespace GlobalTheory.PtDegArch

theorem good_case (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (hL : Laws U x) (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (hy : LiesOn Z y) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin F.P₀.g → K)) (hh : F.IsHerm h) (u : Fin (Dw.mult τ.1) → Fin F.P₀.g → K) (u' : Fin (Dw.mult (conjEmb τ.1)) → Fin F.P₀.g → K) (hu : GlobalTheory.PtDeg.FrameCoord y m1 m2 F τ.1 u) (hu' : GlobalTheory.PtDeg.FrameCoord y m1 m2 F (conjEmb τ.1) u') (σ : K →+* ℂ) (hσ : GoodEmb c (σ.comp (algebraMap c.F K))) :
    s.cInf (σ.comp (algebraMap c.F K)) = ‖σ (evR Xo c s.sig y)‖ * Real.sqrt (h.gram σ u).det.re / Real.sqrt (h.gram σ u').det.re := by
  set σ₀ := σ.comp (algebraMap c.F K) with hσ₀
  let φ : K →ₐ[c.F] CAt σ₀ := { σ with commutes' := fun a => rfl }
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c K (CAt σ₀) φ y
  obtain ⟨k, w, t, ho, hb⟩ := GlobalTheory.LamT.exists_ortho_frBor E H Dw l Xo c σ₀ r (U σ₀) (hL.unf σ₀ hσ) z
  have hon : (⟨k, w.1⟩ : Σ k, Frame ((U σ₀).X k).Ψ r) ∈ framesOn (U σ₀) Z :=
    ⟨w.2, liesOn_frBor hb (liesOn_frMap hz hy)⟩
  have hgood : goodOf c σ₀ = σ₀ := if_pos hσ
  have hinf := s.norm_inf σ₀
  rw [hgood] at hinf
  have h1 : homN (U σ₀) x (wtOf Dw (flatWt Dw τ) 0) s.sig ⟨k, w.1⟩ = s.cInf σ₀ := by
    have : homN (U σ₀) x (wtOf Dw (flatWt Dw τ) 0) s.sig ⟨k, w.1⟩ ∈
        homN (U σ₀) x (wtOf Dw (flatWt Dw τ) 0) s.sig '' framesOn (U σ₀) Z := ⟨_, hon, rfl⟩
    rw [hinf] at this
    exact this
  rw [GlobalTheory.CompHS.homN_eq_homFac] at h1
  have h2 := GlobalTheory.evR_frBor_of_mem_secZ GlobalTheory.lawsFieldsSeparately.2.1 Xo c _ s.sig_mem (CAt σ₀) t _ _ hb
  have h3 := GlobalTheory.FrameEval.evR_frMap_of_isReduced E H Dw l Xo c s.sig s.sig_mem.1 φ y z hz
  have h4 := GlobalTheory.T.normFactor_flatLine_eq_gram_orthonormal_frame E H Dw l Xo c r U x hL τ K y B t₀ m1 m2 F h hh u u' hu hu' σ hσ φ (fun _ => rfl) z hz k w t ho hb
  rw [← h1, h4]
  have h5 : ‖σ (evR Xo c s.sig y)‖ = ‖GlobalTheory.CompHS.diagChar (exOf Dw (flatWt Dw τ) 0) t‖ * ‖toC (evR Xo c s.sig ((U σ₀).un k w))‖ := by
    rw [← norm_mul]
    show ‖toC (φ (evR Xo c s.sig y))‖ = _
    rw [← h3, h2]
    rfl
  rw [h5]
  ring

theorem cInf_eq_frame_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K), LiesOn Z y → ∀ (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ (u : Fin (Dw.mult τ.1) → Fin F.P₀.g → K) (u' : Fin (Dw.mult (conjEmb τ.1)) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F τ.1 u → GlobalTheory.PtDeg.FrameCoord y m1 m2 F (conjEmb τ.1) u' → ∀ σ : K →+* ℂ, s.cInf (σ.comp (algebraMap c.F K)) = ‖σ (evR Xo c s.sig y)‖ * Real.sqrt (h.gram σ u).det.re / Real.sqrt (h.gram σ u').det.re := by
  intro E _ _ _ H Dw l Xo c r U x hL Z τ s K _ _ _ y hy B t₀ m1 m2 F h hh u u' hu hu' σ
  by_cases hσ : GoodEmb c (σ.comp (algebraMap c.F K))
  · exact good_case E H Dw l Xo c r U x hL Z τ s K y hy B t₀ m1 m2 F h hh u u' hu hu' σ hσ
  · set σ' := (starRingEnd ℂ).comp σ
    have e0 : σ'.comp (algebraMap c.F K) = (starRingEnd ℂ).comp (σ.comp (algebraMap c.F K)) := RingHom.comp_assoc _ _ _
    have hσ' : GoodEmb c (σ'.comp (algebraMap c.F K)) := by
      have := goodEmb_goodOf c (σ.comp (algebraMap c.F K))
      rw [goodOf, if_neg hσ] at this
      rw [e0]; exact this
    have hg := good_case E H Dw l Xo c r U x hL Z τ s K y hy B t₀ m1 m2 F h hh u u' hu hu' σ' hσ'
    have hc : s.cInf (σ'.comp (algebraMap c.F K)) = s.cInf (σ.comp (algebraMap c.F K)) := by
      have i1 := s.norm_inf (σ.comp (algebraMap c.F K))
      have i2 := s.norm_inf (σ'.comp (algebraMap c.F K))
      rw [e0, Formalism.L2.Pj.goodOf_conj, i1] at i2
      exact (Set.singleton_eq_singleton_iff.1 i2).symm
    have hgr : ∀ {n : ℕ} (v : Fin n → Fin F.P₀.g → K), (h.gram σ' v).det.re = (h.gram σ v).det.re := fun v => by
      have : h.gram σ' v = (h.gram σ v).map (starRingEnd ℂ) := by
        ext i j
        simp only [ReciprocityTheory.GeometryOfNumbersTheory.HermFam.gram, Matrix.of_apply, Matrix.map_apply]
        exact GlobalTheory.T.lieAlgebraMetric_conjEmbedding_eq_conj K B.pol F h hh σ (v i) (v j)
      rw [this]
      change ((starRingEnd ℂ).mapMatrix (h.gram σ v)).det.re = _
      rw [← RingHom.map_det, Complex.conj_re]
    rw [← hc, hg, hgr, hgr]
    simp only [σ', RingHom.comp_apply, Complex.norm_conj]

end GlobalTheory.PtDegArch
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstLengthFlatSectionEqFrameNormComplexEmbeddinStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constLengthFlatSection_eq_frameNorm_complexEmbedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K), LiesOn Z y → ∀ (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ (u : Fin (Dw.mult τ.1) → Fin F.P₀.g → K) (u' : Fin (Dw.mult (conjEmb τ.1)) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F τ.1 u → GlobalTheory.PtDeg.FrameCoord y m1 m2 F (conjEmb τ.1) u' → ∀ σ : K →+* ℂ, s.cInf (σ.comp (algebraMap c.F K)) = ‖σ (evR Xo c s.sig y)‖ * Real.sqrt (h.gram σ u).det.re / Real.sqrt (h.gram σ u').det.re := by
  first | exact @GlobalTheory.PtDegArch.cInf_eq_frame_norm | exact GlobalTheory.PtDegArch.cInf_eq_frame_norm | (intros; apply GlobalTheory.PtDegArch.cInf_eq_frame_norm <;> assumption)
end
