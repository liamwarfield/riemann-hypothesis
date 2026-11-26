module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRiemannFormPeriodChartGenericFibre

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricEqConstMulRiemannFormOnExpChart
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDiagonalRiemannFormOrthonormalFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDiagonalRiemannFormOrthonormalFrame
open AlgebraicGeometry CategoryTheory Limits MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ArcQ GlobalTheory.FrameNormLie GlobalTheory.HodgeSmooth
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

section EigenvectorOrthogonality

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ProjVar.Var GlobalTheory.ShFam.Pad
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ArcQ GlobalTheory.FrameNormLie GlobalTheory.ShFam
open scoped ComplexOrder

namespace GlobalTheory.HodgeSmooth.EigOrth

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}


open Classical in
def riemConst (U : Formalism.L2.PjFree.Unf Xo c σ r) (k : U.Comp) (τ : E →+* ℂ) : ℝ :=
  2 * ((if Formalism.L2.PjFree.relab c σ τ ∈ (U.X k).Ψ then Formalism.L2.PjFree.relab c σ τ
    else ComplexEmbedding.conjugate (Formalism.L2.PjFree.relab c σ τ)) (-(U.X k).ξ0)).im

theorem exists_diag_im {U : Formalism.L2.PjFree.Unf Xo c σ r} (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) (W : UnfWit U) (k : U.Comp) (x : (U.X k).dom) (hx : IsOrth (U.X k) x.1) :
    ∃ D : Fin W.g → ℂ, (∀ τ (j : Fin (Dw.mult τ)), D (W.e.symm ⟨τ, j⟩) = ((riemConst U k τ : ℝ) : ℂ)) ∧
      ∀ v w, (hermForm (diagonal D) (W.Pm k x v) (W.Pm k x w)).im = (W.F.Di (W.ik k)).EF v w := by
  classical
  obtain ⟨hp0, hty⟩ := hU.2.1 k
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨f, hf⟩ := FrameUnif.exists_letter_equiv (U.X k).Ψ (U.X k).cmType Dw.p Dw.q r hU.1
    (Formalism.L2.PjFree.relab c σ) hbij Dw.mult
    (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))])
    (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])
  rw [← hp0] at hf
  have hper (v) : W.Pm k x v = perVec (U.X k) (W.e.trans f) x.1 (W.φ k v : Fin r → E) := funext fun j => by
    rw [W.Pm_eq, perVec, Equiv.trans_apply]
    have h := hf (W.e j)
    generalize f (W.e j) = t at h ⊢
    obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
    dsimp only at h ⊢
    rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
    · rw [if_neg (by omega), Formalism.L2.PjFree.perFr, dite_eq_left a, dite_eq_left hn]
    · rw [if_pos (by omega), Formalism.L2.PjFree.perFr, dite_eq_right a,
        dite_eq_left (show conjEmb (Formalism.L2.PjFree.relab c σ (W.e j).1) ∈ (U.X k).Ψ from hτ), dite_eq_left hn]
      rfl
  refine ⟨diagXi (U.X k) (W.e.trans f), fun τ j => ?_, fun v w => ?_⟩
  · rw [diagXi, Equiv.trans_apply, Equiv.apply_symm_apply]
    rcases hf ⟨τ, j⟩ with ⟨a, h1, -⟩ | ⟨a, h1, -, -⟩
    · rw [h1]
      simp only [riemConst, if_pos a]
    · rw [h1]
      simp only [riemConst, if_neg a]
  · rw [hper, hper, im_diag_ortho _ _ _ hx, ← W.iso]
    simp

theorem riemConst_pos {U : Formalism.L2.PjFree.Unf Xo c σ r} (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) (W : UnfWit U) (k : U.Comp) (x : (U.X k).dom) (hx : IsOrth (U.X k) x.1)
    (τ : E →+* ℂ) (hτ : 0 < Dw.mult τ) : 0 < riemConst U k τ := by
  classical
  obtain ⟨D, hD, him⟩ := exists_diag_im hσ hU W k x hx
  obtain ⟨-, -, -, hspan, Hm₀, -, hpos, hHm₀⟩ := W.period k x
  have e := UnitDet.eq_of_im_hermForm_eq _ hspan (diagonal D) Hm₀ (by
    rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩
    rw [him, hHm₀])
  set j := W.e.symm ⟨τ, ⟨0, hτ⟩⟩
  have h := hpos (Pi.single j 1) (by simp)
  rw [← e] at h
  have h2 : hermForm (diagonal D) (Pi.single j 1) (Pi.single j 1) = D j := by
    simp [hermForm]
  rw [h2, hD] at h
  simpa using h

end GlobalTheory.HodgeSmooth.EigOrth

end EigenvectorOrthogonality


open GlobalTheory.HodgeSmooth.EigOrth in
theorem GlobalTheory.HodgeSmooth.exists_diag_riem_orth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (W : UnfWit U), ∃ d : U.Comp → (E →+* ℂ) → ℝ, (∀ (k : U.Comp) (x : (U.X k).dom), IsOrth (U.X k) x.1 → ∀ τ : E →+* ℂ, 0 < Dw.mult τ → 0 < d k τ) ∧ ∀ (k : U.Comp) (x : (U.X k).dom), IsOrth (U.X k) x.1 → ∀ (i : Fin W.F.n) (P : (W.F.Di i).La →+ (Fin W.g → ℂ)), IsPeriod (W.F.Di i) (fun j => Formalism.L2.PjFree.relab c σ (W.e j).1) P → ∀ (Hm : Matrix (Fin W.g) (Fin W.g) ℂ), (∀ v w, (hermForm Hm (P v) (P w)).im = (W.F.Di i).EF v w) → W.F.u i P = (U.un k x).x → ∀ (τ τ' : E →+* ℂ) (zz : Fin (Dw.mult τ) → (Fin W.g → ℂ)) (zz' : Fin (Dw.mult τ') → (Fin W.g → ℂ)) (uu : Fin (Dw.mult τ) → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (uu' : Fin (Dw.mult τ') → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) (T' : Matrix (Fin (Dw.mult τ')) (Fin (Dw.mult τ')) ℂ), (∀ b, IsDerivAt0 (fun w => (W.F.ex i P w).left) (zz b) (uu b)) → (∀ b, IsDerivAt0 (fun w => (W.F.ex i P w).left) (zz' b) (uu' b)) → (∀ b, IsCombAt (U.un k x).x ((U.un k x).u τ) (show Fin (Dw.mult τ) → CAt σ from fun b' => T b' b) (uu b)) → (∀ b, IsCombAt (U.un k x).x ((U.un k x).u τ') (show Fin (Dw.mult τ') → CAt σ from fun b' => T' b' b) (uu' b)) → (of fun b b' => hermForm Hm (zz b') (zz b)) = ((d k τ : ℝ) : ℂ) • (Tᴴ * T) ∧ (τ' ≠ τ → ∀ b b', hermForm Hm (zz' b') (zz b) = 0) := by
  classical
  intro E _ _ _ H Dw l Xo c σ r U hσ hU W
  refine ⟨fun k τ => riemConst U k τ, fun k x hx τ hτ => riemConst_pos hσ hU W k x hx τ hτ, ?_⟩
  intro k x hx i P hP Hm hH hPu τ τ' zz zz' uu uu' T T' hder hder' hT hT'
  obtain ⟨D, hD, him⟩ := exists_diag_im hσ hU W k x hx
  have p := W.period k x
  obtain ⟨hPx, hv⟩ := W.lie k x
  obtain ⟨h, gam, hex, hh, hiso, -⟩ := familyUnif_exp_unique E H Dw l Xo _ _ _ W.F i (W.ik k) P _ hP p
    (by rw [← hPx]; exact hPu)
  set A := LinearMap.toMatrix' h.toLinearMap with hA
  have hAv : ∀ z, A *ᵥ z = h z := fun z => by rw [hA, LinearMap.toMatrix'_mulVec]; rfl
  have hcol : ∀ (τ : E →+* ℂ) (zz : Fin (Dw.mult τ) → (Fin W.g → ℂ))
      (uu : Fin (Dw.mult τ) → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left))
      (T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ),
      (∀ b, IsDerivAt0 (fun w => (W.F.ex i P w).left) (zz b) (uu b)) →
      (∀ b, IsCombAt (U.un k x).x ((U.un k x).u τ) (show Fin (Dw.mult τ) → CAt σ from fun b' => T b' b) (uu b)) →
      ∀ b, A *ᵥ zz b = ∑ j, T j b • (Pi.single (W.e.symm ⟨τ, j⟩) 1 : Fin W.g → ℂ) := by
    intro τ zz uu T hder hT b
    have d1 := (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ _ _ W.F _ _ p _ ((U.un k x).u τ) _ (hv τ) _
      (uu b)).1 (hPx ▸ hT b)
    have d2 := (ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ _ _ W.F _ P hP _ _ h.toLinearMap p hex _ _).1 (hder b)
    have tn := isDerivAt0_ex_isTanAt E H Dw l Xo _ _ _ W.F _ _ p
    rw [hAv]
    exact (tn.2.2 _ (tn.1 _ _ d2)).unique d2 d1
  have key := UnitDet.eq_of_im_hermForm_eq _ hP.2.2.2.1
    (Aᵀ * (diagonal D * A.map (starRingEnd ℂ))) Hm (by
      rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩
      rw [← UnitDet.hermForm_mulVec, hAv, hAv, ← hh, ← hh, him, hiso, hH])
  refine ⟨?_, fun hne b b' => ?_⟩
  · have hsupp : ∀ b, diagonal D *ᵥ star (∑ j, T j b • (Pi.single (W.e.symm ⟨τ, j⟩) 1 : Fin W.g → ℂ)) =
        (((riemConst U k τ : ℝ) : ℂ) • (1 : Matrix (Fin W.g) (Fin W.g) ℂ)) *ᵥ
          star (∑ j, T j b • (Pi.single (W.e.symm ⟨τ, j⟩) 1 : Fin W.g → ℂ)) := by
      intro b
      simp only [smul_mulVec, Matrix.one_mulVec]
      funext p'
      rw [mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
      by_cases hp : ∃ j, W.e.symm ⟨τ, j⟩ = p'
      · obtain ⟨j, rfl⟩ := hp
        rw [hD τ j]
      · push_neg at hp
        have : (∑ j, T j b • (Pi.single (W.e.symm ⟨τ, j⟩) 1 : Fin W.g → ℂ)) p' = 0 := by
          rw [Finset.sum_apply]
          exact Finset.sum_eq_zero fun j _ => by rw [Pi.smul_apply, Pi.single_eq_of_ne (hp j).symm, smul_zero]
        simp [Pi.star_apply, this]
    ext b b'
    rw [of_apply, ← key, ← UnitDet.hermForm_mulVec, hcol τ zz uu T hder hT, hcol τ zz uu T hder hT, hermForm,
      hsupp, ← hermForm]
    beta_reduce
    generalize ((riemConst U k τ : ℝ) : ℂ) = dd
    clear hsupp key hcol hAv hiso hh hex him hD hT hder hH hPu hT' hder'
    have hi : ∀ j j' : Fin (Dw.mult τ), W.e.symm ⟨τ, j⟩ = W.e.symm ⟨τ, j'⟩ ↔ j = j' := fun j j' => by simp
    simp [hermForm, smul_mulVec, sum_dotProduct, dotProduct_sum, star_sum, Pi.single_apply, hi, mul_apply, mul_comm]
    left
    simp [Matrix.mul_apply, mul_comm]
  · rw [← key, ← UnitDet.hermForm_mulVec, hcol τ' zz' uu' T' hder' hT', hcol τ zz uu T hder hT]
    simp only [hermForm, dotProduct, mulVec_diagonal, Pi.star_apply]
    refine Finset.sum_eq_zero fun q _ => ?_
    by_cases hq : ∃ j, W.e.symm ⟨τ', j⟩ = q
    · obtain ⟨j, rfl⟩ := hq
      have : (∑ j'', T j'' b • (Pi.single (W.e.symm ⟨τ, j''⟩) 1 : Fin W.g → ℂ)) (W.e.symm ⟨τ', j⟩) = 0 := by
        rw [Finset.sum_apply]
        refine Finset.sum_eq_zero fun j'' _ => ?_
        rw [Pi.smul_apply, Pi.single_eq_of_ne, smul_zero]
        intro he
        exact hne (congrArg Sigma.fst (W.e.symm.injective he))
      rw [this]
      simp
    · push_neg at hq
      have : (∑ j, T' j b' • (Pi.single (W.e.symm ⟨τ', j⟩) 1 : Fin W.g → ℂ)) q = 0 := by
        rw [Finset.sum_apply]
        exact Finset.sum_eq_zero fun j _ => by rw [Pi.smul_apply, Pi.single_eq_of_ne (hq j).symm, smul_zero]
      rw [this]
      simp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDiagonalRiemannFormOrthonormalFrameStatement
open AlgebraicGeometry CategoryTheory Limits MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ArcQ GlobalTheory.FrameNormLie GlobalTheory.HodgeSmooth
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_diagonal_riemannForm_orthonormalFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (W : UnfWit U), ∃ d : U.Comp → (E →+* ℂ) → ℝ, (∀ (k : U.Comp) (x : (U.X k).dom), IsOrth (U.X k) x.1 → ∀ τ : E →+* ℂ, 0 < Dw.mult τ → 0 < d k τ) ∧ ∀ (k : U.Comp) (x : (U.X k).dom), IsOrth (U.X k) x.1 → ∀ (i : Fin W.F.n) (P : (W.F.Di i).La →+ (Fin W.g → ℂ)), IsPeriod (W.F.Di i) (fun j => Formalism.L2.PjFree.relab c σ (W.e j).1) P → ∀ (Hm : Matrix (Fin W.g) (Fin W.g) ℂ), (∀ v w, (hermForm Hm (P v) (P w)).im = (W.F.Di i).EF v w) → W.F.u i P = (U.un k x).x → ∀ (τ τ' : E →+* ℂ) (zz : Fin (Dw.mult τ) → (Fin W.g → ℂ)) (zz' : Fin (Dw.mult τ') → (Fin W.g → ℂ)) (uu : Fin (Dw.mult τ) → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (uu' : Fin (Dw.mult τ') → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) (T' : Matrix (Fin (Dw.mult τ')) (Fin (Dw.mult τ')) ℂ), (∀ b, IsDerivAt0 (fun w => (W.F.ex i P w).left) (zz b) (uu b)) → (∀ b, IsDerivAt0 (fun w => (W.F.ex i P w).left) (zz' b) (uu' b)) → (∀ b, IsCombAt (U.un k x).x ((U.un k x).u τ) (show Fin (Dw.mult τ) → CAt σ from fun b' => T b' b) (uu b)) → (∀ b, IsCombAt (U.un k x).x ((U.un k x).u τ') (show Fin (Dw.mult τ') → CAt σ from fun b' => T' b' b) (uu' b)) → (of fun b b' => hermForm Hm (zz b') (zz b)) = ((d k τ : ℝ) : ℂ) • (Tᴴ * T) ∧ (τ' ≠ τ → ∀ b b', hermForm Hm (zz' b') (zz b) = 0) := by
  first | exact @GlobalTheory.HodgeSmooth.exists_diag_riem_orth | exact GlobalTheory.HodgeSmooth.exists_diag_riem_orth | (intros; apply GlobalTheory.HodgeSmooth.exists_diag_riem_orth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrthonormalFramesSameComponentNearChart
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrthonormalFramesSameComponentNearChart
open AlgebraicGeometry CategoryTheory Limits MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ArcQ GlobalTheory.FrameNormLie GlobalTheory.HodgeSmooth
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

theorem GlobalTheory.HodgeSmooth.chart_comp_locconst : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → 1 ≤ r → ∀ (n : ℕ) (ch : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr Z) σ) (Fin n → ℂ)), IsHolTo ch.target (fun z => (ch.symm z).1) → ∀ (k₀ : U.Comp) (x₀ : (U.X k₀).dom), cxPt Z (U.un k₀ x₀) ∈ ch.source → ∃ B : Set (Fin n → ℂ), IsOpen B ∧ ch (cxPt Z (U.un k₀ x₀)) ∈ B ∧ ∀ z ∈ B, ∀ (k : U.Comp) (x : (U.X k).dom), cxPt Z (U.un k x) = ch.symm z → k = k₀ := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ r U hσ hU h1 n ch hsy k₀ x₀ hy₀
  obtain ⟨W, hinj⟩ := GlobalTheory.HodgeSmooth.exists_unfWit_inj hσ hU h1
  have := Z.jQ_open
  have hB₀ := (hsy Z.jQ.opensRange 0).1
  set B₀ := {b ∈ ch.target | ⊤ ≤ (ch.symm b).1 ⁻¹ᵁ Z.jQ.opensRange} with hB₀def
  set y₀ := U.un k₀ x₀ with hy₀def
  have hb₀ : ch (cxPt Z y₀) ∈ B₀ := by
    refine ⟨ch.map_source hy₀, ?_⟩
    rw [ch.left_inv hy₀]
    intro s _
    exact ⟨GlobalTheory.AllWt.ptF (S := Formalism.L2.Pj.CAt σ) y₀ s, (Scheme.Hom.comp_apply (GlobalTheory.AllWt.ptF (S := Formalism.L2.Pj.CAt σ) y₀) Z.jQ s).symm⟩
  have : Nonempty (Sp ℂ ⟶ Xo.XF c) := ⟨GlobalTheory.AllWt.ptF (S := Formalism.L2.Pj.CAt σ) y₀⟩
  have hw : ∀ b ∈ B₀, ∃ w : Sp ℂ ⟶ Xo.XF c, w ≫ Z.jQ = (ch.symm b).1 := fun b hb =>
    ⟨IsOpenImmersion.lift Z.jQ _ (by rintro _ ⟨s, rfl⟩; exact hb.2 (Set.mem_univ s)), IsOpenImmersion.lift_fac _ _ _⟩
  choose! w hw using hw
  have hwh : IsHolTo B₀ w := GlobalTheory.TrueCx.TorHolo.isHolTo_of_openImmersion Z.jQ
    (GlobalTheory.LocLift.isHolTo_congr (GlobalTheory.LocLift.isHolTo_mono hsy hB₀ fun b hb => hb.1) hw)
  have hyh := ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp hwh (pullback.fst _ _)
  have hsnd : ∀ b ∈ B₀, w b ≫ pullback.snd _ _ = spMap σ := fun b hb => by
    rw [← Z.jQ_over, ← Category.assoc, hw b hb]
    exact (ch.symm b).2
  obtain ⟨B, i, P, hB, hbB, hsub, hP, hu⟩ := W.F.lift n B₀ (fun x => w x ≫ pullback.fst _ _) hB₀
    (fun x hx => by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hsnd _ hx, ← Spec.map_comp]
      rfl) hyh _ hb₀
  have hik : ∀ z ∈ B, ∀ (k : U.Comp) (x : (U.X k).dom), cxPt Z (U.un k x) = ch.symm z → W.ik k = i := by
    intro z hz k x hkx
    have h1' : w z = GlobalTheory.AllWt.ptF (S := Formalism.L2.Pj.CAt σ) (U.un k x) :=
      (cancel_mono Z.jQ).1 ((hw z (hsub hz)).trans (congrArg Subtype.val hkx.symm))
    have h2 : W.F.u i (P z) = (U.un k x).x := by
      rw [hu z hz, h1']
      exact GlobalTheory.ShFam.ptF_fst _
    exact W.F.disj _ _ _ _ (W.period k x) (hP.1 z hz) ((W.lie k x).1.symm.trans h2.symm)
  have hk₀ : W.ik k₀ = i := hik _ hbB k₀ x₀ (by rw [ch.left_inv hy₀])
  exact ⟨B, hB, hbB, fun z hz k x hkx => hinj ((hik z hz k x hkx).trans hk₀.symm)⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrthonormalFramesSameComponentNearChartStatement
open AlgebraicGeometry CategoryTheory Limits MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ArcQ GlobalTheory.FrameNormLie GlobalTheory.HodgeSmooth
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthonormalFrames_same_component_near_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → 1 ≤ r → ∀ (n : ℕ) (ch : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr Z) σ) (Fin n → ℂ)), IsHolTo ch.target (fun z => (ch.symm z).1) → ∀ (k₀ : U.Comp) (x₀ : (U.X k₀).dom), cxPt Z (U.un k₀ x₀) ∈ ch.source → ∃ B : Set (Fin n → ℂ), IsOpen B ∧ ch (cxPt Z (U.un k₀ x₀)) ∈ B ∧ ∀ z ∈ B, ∀ (k : U.Comp) (x : (U.X k).dom), cxPt Z (U.un k x) = ch.symm z → k = k₀ := by
  first | exact @GlobalTheory.HodgeSmooth.chart_comp_locconst | exact GlobalTheory.HodgeSmooth.chart_comp_locconst | (intros; apply GlobalTheory.HodgeSmooth.chart_comp_locconst <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPreconnectedPolydiscFirstCoordsNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPreconnectedPolydiscFirstCoordsNeZero
open Set

namespace GlobalTheory

theorem punctured_unit_disc_eq_exp_image :
    Metric.ball (0:ℂ) 1 \ {0} = Complex.exp '' {z : ℂ | z.re < 0} := by
  ext w
  constructor
  · rintro ⟨hb, h0⟩
    have h0' : w ≠ 0 := h0
    refine ⟨Complex.log w, ?_, Complex.exp_log h0'⟩
    rw [Set.mem_setOf_eq, Complex.log_re]
    rw [Metric.mem_ball, dist_zero_right] at hb
    exact Real.log_neg (norm_pos_iff.mpr h0') hb
  · rintro ⟨z, hz, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, Complex.norm_exp]
      exact Real.exp_lt_one_iff.mpr hz
    · exact Complex.exp_ne_zero z

theorem isPreconnected_punctured_unit_disc :
    IsPreconnected (Metric.ball (0:ℂ) 1 \ {0}) := by
  rw [punctured_unit_disc_eq_exp_image]
  exact (convex_halfSpace_re_lt 0).isPreconnected.image _ Complex.continuous_exp.continuousOn

theorem isPreconnected_polydisc_first_coords_ne_zero :
    ∀ (n a : ℕ) (ha : a ≤ n), _root_.IsPreconnected {z : Fin n → ℂ | z ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ ∀ i : Fin a, z (Fin.castLE ha i) ≠ 0} := by
  intro n a ha
  have hS : {z : Fin n → ℂ | z ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ ∀ i : Fin a, z (Fin.castLE ha i) ≠ 0}
      = Set.pi univ (fun k : Fin n => if (k:ℕ) < a then Metric.ball (0:ℂ) 1 \ {0} else Metric.ball (0:ℂ) 1) := by
    ext z
    rw [ball_pi _ one_pos]
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies, Pi.zero_apply]
    constructor
    · rintro ⟨hb, hne⟩ k
      split_ifs with hk
      · exact ⟨hb k, fun h => hne ⟨k, hk⟩ (by simpa using h)⟩
      · exact hb k
    · intro h
      refine ⟨fun k => ?_, fun i => ?_⟩
      · have := h k
        split_ifs at this
        · exact this.1
        · exact this
      · have := h (Fin.castLE ha i)
        rw [if_pos (by simp)] at this
        exact this.2
  rw [hS]
  apply isPreconnected_univ_pi
  intro k
  split_ifs
  · exact isPreconnected_punctured_unit_disc
  · exact (convex_ball (0:ℂ) 1).isPreconnected

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPreconnectedPolydiscFirstCoordsNeZeroStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPreconnected_ball_inter_coords_ne_zero : ∀ (n a : ℕ) (ha : a ≤ n), _root_.IsPreconnected {z : Fin n → ℂ | z ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ ∀ i : Fin a, z (Fin.castLE ha i) ≠ 0} := by
  first | exact @GlobalTheory.isPreconnected_polydisc_first_coords_ne_zero | exact GlobalTheory.isPreconnected_polydisc_first_coords_ne_zero | (intros; apply GlobalTheory.isPreconnected_polydisc_first_coords_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricEqConstMulRiemannFormOnExpChart
open AlgebraicGeometry CategoryTheory Limits MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ArcQ GlobalTheory.FrameNormLie GlobalTheory.HodgeSmooth
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HodgeChart

theorem hodgeMet_eq_riem_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (n a : ℕ) (ha : a ≤ n) (g : ℕ) (ch₀ : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr T.Z) σ) (Fin n → ℂ)) (ex : ExpMaps T.Z σ g), IsExpChart ch₀ ex → Fintype.card ((Σ τ : E →+* ℂ, Fin (Dw.mult τ))) = g → (∀ x ∈ ch₀.source, Inner x ↔ ∀ i : Fin a, ch₀ x (Fin.castLE ha i) ≠ 0) → ∃ κ : (E →+* ℂ) → ℝ, (∀ τ, 0 < κ τ) ∧ ∀ x ∈ ch₀.source, Inner x → ∀ Hm : Matrix (Fin g) (Fin g) ℂ, ((Hm).IsHermitian ∧ (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm (Hm) u u).re) ∧ (∀ v w : Fin g → ℂ, ex x v = 1 → ex x w = 1 → ∃ m : ℤ, (hermForm (Hm) v w).im = m) ∧ ∀ (k : ℕ) (v w : Fin g → ℂ) (ζ : ℂˣ), 0 < k → ex x v = 1 → ex x w = 1 → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm (Hm) v w).im : ℂ) / k) → GlobalTheory.UU.CubWeil T.Z.t.cub k (ex x ((k : ℂ)⁻¹ • v)) (ex x ((k : ℂ)⁻¹ • w)) (unitOn ζ)) → ∀ (f : EigFrame T.Z σ (x.1 ≫ genι T.Z)) (W : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → Fin g → ℂ), Dirs ⟨x, f⟩ (fun w => (ex x w).left) W → (∀ τ, (hodgeMet T.Z U).gram x f τ = ((κ τ : ℝ) : ℂ) • Matrix.of fun b b' => hermForm Hm (W ⟨τ, b'⟩) (W ⟨τ, b⟩)) ∧ ∀ p q : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), p.1 ≠ q.1 → hermForm Hm (W p) (W q) = 0 := by
  intro E _ _ _ H Dw l Xo c O _ β Y T σ U hσ hU n a ha g ch₀ ex hEC _ hIn
  classical
  obtain ⟨htarget, -, hsymmHol, hadd, hjoint, htan⟩ := hEC
  have hsrc : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ch₀.symm z ∈ ch₀.source := fun z hz =>
    ch₀.map_target (by rw [htarget]; exact hz)
  set Ω : Set (Fin n → ℂ) := {z | z ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ ∀ i : Fin a, z (Fin.castLE ha i) ≠ 0} with hΩ
  have hinΩ : ∀ x ∈ ch₀.source, Inner x → ch₀ x ∈ Ω := fun x hx hI =>
    ⟨by rw [← htarget]; exact ch₀.map_source hx, (hIn x hx).1 hI⟩
  have hΩin : ∀ z ∈ Ω, Inner (ch₀.symm z) := fun z hz =>
    (hIn _ (hsrc z hz.1)).2 (by rw [ch₀.right_inv (by rw [htarget]; exact hz.1)]; exact hz.2)
  by_cases h1 : 1 ≤ Dw.p + Dw.q
  swap
  · have hm : ∀ τ : E →+* ℂ, Dw.mult τ = 0 := fun τ => by unfold Datum.mult; split_ifs <;> omega
    refine ⟨fun _ => 1, fun _ => one_pos, fun x _ _ Hm _ f Wd _ => ⟨fun τ => ?_, fun p q _ => ?_⟩⟩
    · ext i
      have h0 := hm τ
      have h2 := i.2
      omega
    · have h0 := hm p.1
      have h2 := p.2.2
      omega
  set U' := unfFam U σ with hU'def
  have hU' : Formalism.L2.PjFree.IsUnf U' := by rw [hU'def, unfFam_self]; exact hU
  obtain ⟨W, hinj⟩ := exists_unfWit_inj hσ hU' h1
  obtain ⟨d, hdpos, hd⟩ := GlobalTheory.T.exists_diagonal_riemannForm_orthonormalFrame E H Dw l Xo c σ _ U' hσ hU' W
  have hreach : ∀ z ∈ Ω, ∃ (k : U'.Comp) (x : (U'.X k).dom), IsOrth (U'.X k) x.1 ∧
      cxPt T.Z (U'.un k x) = ch₀.symm z :=
    fun z hz => exists_orth (Z := T.Z) hσ hU' (hΩin z hz)
  by_cases hne : Ω.Nonempty
  swap
  · exact ⟨fun _ => 1, fun _ => one_pos, fun x hx hI => absurd ⟨ch₀ x, hinΩ x hx hI⟩ hne⟩
  obtain ⟨z₁, hz₁⟩ := hne
  have hreach' : ∀ z, ∃ k : U'.Comp, z ∈ Ω → ∃ x : (U'.X k).dom, IsOrth (U'.X k) x.1 ∧
      cxPt T.Z (U'.un k x) = ch₀.symm z := fun z => by
    by_cases h : z ∈ Ω
    · obtain ⟨k, x, hx⟩ := hreach z h
      exact ⟨k, fun _ => ⟨x, hx⟩⟩
    · exact ⟨(hreach z₁ hz₁).choose, fun h' => absurd h' h⟩
  choose comp hcomp using hreach'
  letI : TopologicalSpace U'.Comp := ⊥
  haveI : DiscreteTopology U'.Comp := ⟨rfl⟩
  have hcont : ContinuousOn comp Ω := by
    intro z hz
    obtain ⟨x₀, -, hx₀⟩ := hcomp z hz
    have hs0 : cxPt T.Z (U'.un (comp z) x₀) ∈ ch₀.source := by rw [hx₀]; exact hsrc z hz.1
    obtain ⟨B, hBo, hzB, hB⟩ := GlobalTheory.T.orthonormalFrames_same_component_near_chart E H Dw l Xo c O β T.Z σ _ U' hσ hU' h1 n ch₀ hsymmHol (comp z) x₀ hs0
    rw [hx₀, ch₀.right_inv (by rw [htarget]; exact hz.1)] at hzB
    refine tendsto_nhds_of_eventually_eq ?_
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (hBo.mem_nhds hzB)] with w hw hwB
    obtain ⟨x, -, hx⟩ := hcomp w hw
    exact hB w hwB _ x hx
  have hconst : ∀ z ∈ Ω, comp z = comp z₁ := fun z hz =>
    (GlobalTheory.T.isPreconnected_ball_inter_coords_ne_zero n a ha).constant hcont hz hz₁
  refine ⟨fun τ => if 0 < d (comp z₁) τ then 2 * Real.pi / d (comp z₁) τ else 1, fun τ => ?_, ?_⟩
  · dsimp only
    split_ifs with h
    · exact div_pos Real.two_pi_pos h
    · exact one_pos
  intro x hx hI Hm hHm f Wd hW
  have hz := hinΩ x hx hI
  obtain ⟨x', hx'o, hx'⟩ := hcomp _ hz
  rw [ch₀.left_inv hx] at hx'
  have hk := hconst _ hz
  have hExpAt : IsExpAt T.Z.t (x.1 ≫ genι T.Z) (ex x) := ⟨hadd x hx, (htan x hx).1, (htan x hx).2⟩
  have hslice : IsHolTo Set.univ (fun w => (ex x w).left) := by
    have hmem : ch₀ x ∈ ch₀.target := ch₀.map_source hx
    have := GlobalTheory.HolPeriods.isHolTo_comp (φ := fun w : Fin g → ℂ => (ch₀ x, w)) hjoint isOpen_univ
      ((differentiableOn_const (ch₀ x)).prodMk differentiableOn_id) fun w _ => Set.mk_mem_prod hmem (Set.mem_univ w)
    dsimp only at this
    rw [ch₀.left_inv hx] at this
    exact this
  obtain ⟨hg, ho⟩ := GlobalTheory.T.hodgeMetric_frame_eq_riemannForm_at_interior_point E H Dw l Xo c O β T.Z σ U hσ hU W hinj d hdpos hd g x (ex x) hI hExpAt hslice _ x' hx'o hx'
    Hm hHm.2.2.1 hHm.2.2.2 f Wd hW
  refine ⟨fun τ => ?_, ho⟩
  rw [hg τ]
  by_cases hm : Dw.mult τ = 0
  · ext i
    have h2 := i.2
    omega
  · have hpos := hdpos _ x' hx'o τ (Nat.pos_of_ne_zero hm)
    have e : d (comp (ch₀ x)) τ = d (comp z₁) τ := by rw [hk]
    rw [e] at hpos ⊢
    simp only [if_pos hpos]

end GlobalTheory.HodgeChart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricEqConstMulRiemannFormOnExpChartStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeMetric_eq_const_mul_riemannForm_on_expChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (n a : ℕ) (ha : a ≤ n) (g : ℕ) (ch₀ : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr T.Z) σ) (Fin n → ℂ)) (ex : ExpMaps T.Z σ g), IsExpChart ch₀ ex → Fintype.card ((Σ τ : E →+* ℂ, Fin (Dw.mult τ))) = g → (∀ x ∈ ch₀.source, Inner x ↔ ∀ i : Fin a, ch₀ x (Fin.castLE ha i) ≠ 0) → ∃ κ : (E →+* ℂ) → ℝ, (∀ τ, 0 < κ τ) ∧ ∀ x ∈ ch₀.source, Inner x → ∀ Hm : Matrix (Fin g) (Fin g) ℂ, ((Hm).IsHermitian ∧ (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm (Hm) u u).re) ∧ (∀ v w : Fin g → ℂ, ex x v = 1 → ex x w = 1 → ∃ m : ℤ, (hermForm (Hm) v w).im = m) ∧ ∀ (k : ℕ) (v w : Fin g → ℂ) (ζ : ℂˣ), 0 < k → ex x v = 1 → ex x w = 1 → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm (Hm) v w).im : ℂ) / k) → GlobalTheory.UU.CubWeil T.Z.t.cub k (ex x ((k : ℂ)⁻¹ • v)) (ex x ((k : ℂ)⁻¹ • w)) (unitOn ζ)) → ∀ (f : EigFrame T.Z σ (x.1 ≫ genι T.Z)) (W : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → Fin g → ℂ), Dirs ⟨x, f⟩ (fun w => (ex x w).left) W → (∀ τ, (hodgeMet T.Z U).gram x f τ = ((κ τ : ℝ) : ℂ) • Matrix.of fun b b' => hermForm Hm (W ⟨τ, b'⟩) (W ⟨τ, b⟩)) ∧ ∀ p q : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), p.1 ≠ q.1 → hermForm Hm (W p) (W q) = 0 := by
  first | exact @GlobalTheory.HodgeChart.hodgeMet_eq_riem_chart | exact GlobalTheory.HodgeChart.hodgeMet_eq_riem_chart | (intros; apply GlobalTheory.HodgeChart.hodgeMet_eq_riem_chart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPeriodChartHodgeMetricGenericFibre
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.PerChart

theorem exists_periodChart_hodge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ x₀ : GlobalTheory.CxPts (genStr T.Z) σ, ∃ (n a : ℕ) (ha : a ≤ n) (g rk : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (ch₀ : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr T.Z) σ) (Fin n → ℂ)) (ex : ExpMaps T.Z σ g) (κ : (E →+* ℂ) → ℝ), GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk τ₀ B ∧ IsExpChart ch₀ ex ∧ x₀ ∈ ch₀.source ∧ ch₀ x₀ = 0 ∧ Fintype.card ((Σ τ : E →+* ℂ, Fin (Dw.mult τ))) = g ∧ (∀ τ, 0 < κ τ) ∧ (∀ x ∈ ch₀.source, Inner x ↔ ∀ i : Fin a, ch₀ x (Fin.castLE ha i) ≠ 0) ∧ ∀ x ∈ ch₀.source, Inner x → ∀ (f : EigFrame T.Z σ (x.1 ≫ genι T.Z)) (W : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → Fin g → ℂ), Dirs ⟨x, f⟩ (fun w => (ex x w).left) W → (∀ τ, (hodgeMet T.Z U).gram x f τ = ((κ τ : ℝ) : ℂ) • Matrix.of fun b b' => hermForm (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch₀ x))⁻¹ (W ⟨τ, b'⟩) (W ⟨τ, b⟩)) ∧ ∀ p q : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), p.1 ≠ q.1 → hermForm (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch₀ x))⁻¹ (W p) (W q) = 0 := by
  intro E _ _ _ H Dw l Xo c O _ β Y T σ U hσ hU x₀
  obtain ⟨n, a, ha, g, rk, τ₀, B, ch₀, ex, d, hP, hE, hx₀, h0, hcard, hd, hInner, hR⟩ :=
    GlobalTheory.T.exists_riemannForm_periodChart_genericFibre E H Dw l Xo c O β Y T σ U hσ hU x₀
  obtain ⟨κ, hκ, hM⟩ := GlobalTheory.T.hodgeMetric_eq_const_mul_riemannForm_on_expChart E H Dw l Xo c O β Y T σ U hσ hU n a ha g ch₀ ex hE hcard hInner
  refine ⟨n, a, ha, g, rk, τ₀, B, ch₀, ex, fun τ => κ τ * d, hP, hE, hx₀, h0, hcard,
    fun τ => mul_pos (hκ τ) hd, hInner, ?_⟩
  intro x hx hin f W hW
  obtain ⟨h1, h2⟩ := hM x hx hin _ (hR x hx hin) f W hW
  have hs : ∀ (M : Matrix (Fin g) (Fin g) ℂ) (v w : Fin g → ℂ),
      hermForm (((d : ℝ) : ℂ) • M) v w = ((d : ℝ) : ℂ) * hermForm M v w := by
    intro M v w
    simp [hermForm, Matrix.smul_mulVec, dotProduct_smul]
  refine ⟨fun τ => ?_, fun p q hpq => ?_⟩
  · rw [h1 τ]
    ext b b'
    simp only [Matrix.smul_apply, Matrix.of_apply, hs, smul_eq_mul]
    push_cast
    ring
  · have := h2 p q hpq
    rw [hs] at this
    exact (mul_eq_zero.1 this).resolve_left (by exact_mod_cast hd.ne')

end GlobalTheory.ShFam.Hor.PerChart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPeriodChartHodgeMetricGenericFibreStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_periodChart_hodgeMetric_genericFibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ x₀ : GlobalTheory.CxPts (genStr T.Z) σ, ∃ (n a : ℕ) (ha : a ≤ n) (g rk : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (ch₀ : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr T.Z) σ) (Fin n → ℂ)) (ex : ExpMaps T.Z σ g) (κ : (E →+* ℂ) → ℝ), GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk τ₀ B ∧ IsExpChart ch₀ ex ∧ x₀ ∈ ch₀.source ∧ ch₀ x₀ = 0 ∧ Fintype.card ((Σ τ : E →+* ℂ, Fin (Dw.mult τ))) = g ∧ (∀ τ, 0 < κ τ) ∧ (∀ x ∈ ch₀.source, Inner x ↔ ∀ i : Fin a, ch₀ x (Fin.castLE ha i) ≠ 0) ∧ ∀ x ∈ ch₀.source, Inner x → ∀ (f : EigFrame T.Z σ (x.1 ≫ genι T.Z)) (W : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → Fin g → ℂ), Dirs ⟨x, f⟩ (fun w => (ex x w).left) W → (∀ τ, (hodgeMet T.Z U).gram x f τ = ((κ τ : ℝ) : ℂ) • Matrix.of fun b b' => hermForm (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch₀ x))⁻¹ (W ⟨τ, b'⟩) (W ⟨τ, b⟩)) ∧ ∀ p q : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), p.1 ≠ q.1 → hermForm (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch₀ x))⁻¹ (W p) (W q) = 0 := by
  first | exact @GlobalTheory.ShFam.Hor.PerChart.exists_periodChart_hodge | exact GlobalTheory.ShFam.Hor.PerChart.exists_periodChart_hodge | (intros; apply GlobalTheory.ShFam.Hor.PerChart.exists_periodChart_hodge <;> assumption)
end
