module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ActLevFullLevelGroupFramedPoints
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FramesDifferByIsometryAndTriangularOfPeriods
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicValueConnectionIntegralChart
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TranslateThetaFrameGermEqUnitMulBoxProduct
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIntegralChartIntegralFramedPoint
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.NuAlgLeOfCharts
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsEqConstMulOfForallExistsNormEqStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelActionMemCuspForms
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsRationalIsometryOfTraceIsometryStatement
open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_isometry_of_trace_isometry : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r), (∀ τ : E →+* ℂ, ‖τ X.ξ0‖ = ‖τ X'.ξ0‖) → ∀ (gam : X.Λ ≃ₗ[𝓞 E] X'.Λ), (∀ u v : X.Λ, Algebra.trace ℚ E (-X'.ξ0 * herm X'.Gm (gam u : Fin r → E) (gam v : Fin r → E)) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (u : Fin r → E) (v : Fin r → E))) → ∃ (a : GL (Fin r) E) (ε : E), (ε = 1 ∨ ε = -1) ∧ X'.ξ0 = ε * X.ξ0 ∧ (∀ v : X.Λ, (a : Matrix (Fin r) (Fin r) E) *ᵥ (v : Fin r → E) = (gam v : Fin r → E)) ∧ (∀ v, v ∈ X.Λ ↔ (a : Matrix (Fin r) (Fin r) E) *ᵥ v ∈ X'.Λ) ∧ ∀ u v, herm X'.Gm ((a : Matrix (Fin r) (Fin r) E) *ᵥ u) ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) = ε * herm X.Gm u v := by
  first | exact @GlobalTheory.TraceIsometry.exists_gl_of_trace_isometry | exact GlobalTheory.TraceIsometry.exists_gl_of_trace_isometry | (intros; apply GlobalTheory.TraceIsometry.exists_gl_of_trace_isometry <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelActionMemCuspForms
namespace GlobalTheory.LevelCusp

section Free

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
  {U : Formalism.L2.PjFree.Unf Xo c σ r}

theorem exists_match (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) (hr : 1 ≤ r)
    (hxi : ∀ k k' (τ : E →+* ℂ), ‖τ (U.X k).ξ0‖ = ‖τ (U.X k').ξ0‖)
    {ρ : Xo.X ⟶ Xo.X} {ν : SABMap Xo.univ.t Xo.univ.t ρ} {k k' : U.Comp} {x : (U.X k).dom} {x' : (U.X k').dom}
    {y' : FrPt Xo c (CAt σ)} {t : Ix Dw → (CAt σ)ˣ} (hm : FrMove ρ ν (U.un k x) y') (hb : FrBor t (U.un k' x') y')
    (hx : IsUnitFr (U.X k) x.1) (hx' : IsUnitFr (U.X k') x'.1) :
    ∃ (a : GL (Fin r) E) (h : IsMatch (U.X k) (U.X k') a), ∃ b ∈ Bor (U.X k').Ψ r,
      x'.1 = rmul (lact a (castFr h.psi x.1)) b ∧ (∀ τ i, ‖b τ i i‖ = 1) ∧ ∀ j, cabs (t j : CAt σ) = 1 := by
  obtain ⟨gam, A, htr, hA0, hA, hAt⟩ := GlobalTheory.T.exists_isometry_triangular_periods_of_framePointMove E H Dw l Xo c σ r U hσ hU ρ ν k k' x x' y' t hm hb
  have hgen := GlobalTheory.T.abs_generatorRatio_eq_one_of_unitFrame_move E H Dw l Xo c σ r U hσ hU ρ ν k k' x x' y' t hm hb hx hx'
  obtain ⟨a, ε, hε, hξ, hav, hlat, hiso⟩ := GlobalTheory.T.exists_rational_isometry_of_trace_isometry E r (U.X k) (U.X k') (hxi k k') gam htr
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨hrr, hty, -⟩ := hU
  have hΨ : (U.X k).Ψ = (U.X k').Ψ := Finset.ext fun τ => ((hty k).2 τ).trans ((hty k').2 τ).symm
  have hp : (U.X k).p0 = (U.X k').p0 := (hty k).1.trans (hty k').1.symm
  let e := Equiv.ofBijective _ hbij
  have he : ∀ τ, Formalism.L2.PjFree.relab c σ (e.symm τ) = τ := e.apply_symm_apply
  have m1 : ∀ τ ∈ (U.X k).Ψ, Dw.mult (e.symm τ) = r - (U.X k).p0 := fun τ hτ => by
    unfold Datum.mult
    rw [if_pos ((hrt _).1 (by rw [he]; exact ((hty k).2 τ).1 hτ)), (hty k).1]
    omega
  have m2 : ∀ τ ∉ (U.X k).Ψ, Dw.mult (e.symm τ) = (U.X k).p0 := fun τ hτ => by
    unfold Datum.mult
    rw [if_neg (fun h => hτ (((hty k).2 τ).2 (by rw [← he τ]; exact (hrt _).2 h))), (hty k).1]
  have hrel : ∀ τ, ∀ i < Dw.mult (e.symm τ), ∀ v ∈ (U.X k).Λ,
      Formalism.L2.PjFree.perFr (U.X k') x'.1 ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i =
        ∑ j ∈ Finset.range (Dw.mult (e.symm τ)), A (e.symm τ) i j * Formalism.L2.PjFree.perFr (U.X k) x.1 v τ j :=
    fun τ i hi v hv => by
      have := hA (e.symm τ) i hi ⟨v, hv⟩
      rwa [he, ← hav] at this
  rcases hε with rfl | rfl
  · have h : IsMatch (U.X k) (U.X k') a :=
      ⟨hΨ, hp, by rw [hξ, one_mul], fun u v => by rw [hiso, one_mul], hlat⟩
    obtain ⟨b, hb, hxb, hu⟩ := GlobalTheory.T.frames_differ_by_isometry_and_triangular_of_periods E r _ _ a h (fun τ => Dw.mult (e.symm τ)) m1 m2 x.1 x.2 x'.1 x'.2
      (fun τ => A (e.symm τ)) (fun τ => hA0 _) hrel
    obtain ⟨h1, h2⟩ := hu hx hx'
    refine ⟨a, h, b, hb, hxb, h1, fun j => ?_⟩
    rcases j with _ | ⟨τ, i⟩
    · exact hgen
    · have := h2 (e τ) i (by rw [e.symm_apply_apply]; exact i.2)
      rw [e.symm_apply_apply, hAt] at this
      exact this
  · exact (GlobalTheory.T.not_antiIsometry_of_triangular_related_periods E r _ _ hΨ hp hr a hiso (fun τ => Dw.mult (e.symm τ)) m1 m2 x.1 x.2 x'.1 x'.2
      (fun τ => A (e.symm τ)) (fun τ => hA0 _) hrel).elim

theorem laU_match {k k' : U.Comp} {a : GL (Fin r) E} (h : IsMatch (U.X k) (U.X k') a)
    (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (τ : (U.X k').Ψ) (i : Fin r) :
    Formalism.L2.PjFree.laU U w n k' τ i = Formalism.L2.PjFree.laU U w n k ⟨τ.1, h.mem τ⟩ i := by
  unfold Formalism.L2.PjFree.laU
  rw [h.p0]

theorem rdU_mem_SS (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) (hr : 1 ≤ r)
    (hxi : ∀ k k' (τ : E →+* ℂ), ‖τ (U.X k).ξ0‖ = ‖τ (U.X k').ξ0‖) {w : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hD : Dom w n)
    {f g : Rul Xo c} (hf : f ∈ sec Xo c w n) (hg : g ∈ sec Xo c w n)
    (hfc : ∀ k, Formalism.L2.PjFree.rdU U f k ∈ (U.X k).SS (Formalism.L2.PjFree.laU U w n k))
    (hmv : ∀ y : FrPt Xo c (CAt σ), ∃ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (y' : FrPt Xo c (CAt σ)),
      FrMove ρ ν y y' ∧ evR Xo c g y = evR Xo c f y') (k : U.Comp) :
    Formalism.L2.PjFree.rdU U g k ∈ (U.X k).SS (Formalism.L2.PjFree.laU U w n k) := by
  have hsec := hU.2.2.2.2.1 w n hD g hg k
  obtain ⟨hun1, hun2⟩ := GlobalTheory.FrameNorm.exists_unitFr_frBor E H Dw l Xo c σ r U hσ hU
  obtain ⟨⟨k', a, h⟩, c₀, hc⟩ := GlobalTheory.T.exists_eq_const_mul_of_forall_exists_norm_eq' (Frame (U.X k).Ψ r)
    (Σ k' : U.Comp, {a : GL (Fin r) E // IsMatch (U.X k) (U.X k') a}) (U.X k).dom (FourierCoefficientDomain.isOpen_dom _)
    (GlobalTheory.frames_isConnected E r (U.X k)).isPreconnected (GlobalTheory.frames_isConnected E r (U.X k)).nonempty
    (Formalism.L2.PjFree.rdU U g k) (fun i x => Formalism.L2.PjFree.rdU U f i.1 (lact i.2.1 (castFr i.2.2.psi x))) hsec.1
    (fun i => (hfc i.1).1.1.1.comp ((GlobalTheory.Dict.Extend.differentiable_lact i.2.1).comp
      (GlobalTheory.Dict.Pull.cast_diff i.2.2.psi)).differentiableOn fun x hx => i.2.2.mem_dom hx)
    (fun x hx => by
      obtain ⟨x₀, hx₀, ⟨b₀, hb₀, e₀⟩, -⟩ := hun1 k ⟨x, hx⟩
      obtain ⟨ρ, ν, y', hm, hv⟩ := hmv (U.un k x₀)
      obtain ⟨k', x', t, hx', hb⟩ := hun2 y'
      obtain ⟨a, h, b, hbB, hxb, hb1, ht⟩ := exists_match hσ hU hr hxi hm hb hx₀ hx'
      refine ⟨⟨k', a, h⟩, ?_⟩
      have hQ := (hfc k').1.1
      have v1 : Formalism.L2.PjFree.rdU U g k x₀.1 = Formalism.L2.PjFree.toC (evR Xo c g (U.un k x₀)) := dif_pos x₀.2
      have v2 : Formalism.L2.PjFree.rdU U f k' x'.1 = Formalism.L2.PjFree.toC (evR Xo c f (U.un k' x')) := dif_pos x'.2
      have v3 := (GlobalTheory.Frames.algebraic_laws GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c).2.2.2.2.2.2 (CAt σ)
        (inferInstanceAs (IsReduced ℂ)) w n f hf t _ y' hb
      have v4 : ‖Formalism.L2.PjFree.toC (wchar (ex Dw w n) t : CAt σ)‖ = 1 := by
        have : Formalism.L2.PjFree.toC (wchar (ex Dw w n) t : CAt σ) =
          ∏ j, Formalism.L2.PjFree.toC (t j : CAt σ) ^ ex Dw w n j := rfl
        rw [this, norm_prod]
        exact Finset.prod_eq_one fun j _ => by
          rw [norm_pow, show ‖Formalism.L2.PjFree.toC (t j : CAt σ)‖ = 1 from ht j, one_pow]
      have v5 : ‖Formalism.L2.PjFree.rdU U g k x₀.1‖ = ‖Formalism.L2.PjFree.rdU U f k' x'.1‖ := by
        rw [v1, v2, hv, v3]
        exact (norm_mul (Formalism.L2.PjFree.toC (wchar (ex Dw w n) t : CAt σ)) _).trans (by rw [v4, one_mul]; rfl)
      have v6 : ‖bchar (Formalism.L2.PjFree.laU U w n k') b‖ = 1 := by
        unfold bchar
        simp only [norm_prod, norm_zpow, hb1, one_zpow, Finset.prod_const_one]
      rw [hxb, hQ.2.1 _ (h.mem_dom x₀.2) b hbB, norm_mul, v6, one_mul, e₀, hsec.2.1 x hx b₀ hb₀,
        GlobalTheory.Dict.Pull.cast_rmul, GlobalTheory.Dict.Extend.lact_rmul,
        hQ.2.1 _ (h.mem_dom hx) _ (GlobalTheory.Dict.Pull.cast_bor h.psi hb₀),
        GlobalTheory.Dict.Pull.cast_bchar h.psi (laU_match h w n), norm_mul, norm_mul] at v5
      exact mul_left_cancel₀ (norm_ne_zero_iff.2 (AR.Up.OntoE.bchar_ne _ _ hb₀)) v5)
  exact GlobalTheory.T.mem_cuspForms_of_multiple_rational_isometry_move E r _ _ a h _ _ (laU_match h w n) _ _ c₀ hsec (hfc k') hc

end Free

end GlobalTheory.LevelCusp

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

theorem GlobalTheory.LevelCusp.actLev_mem_cuspA : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (γ : LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l), ∀ f ∈ T.cuspA j (wtA w) w.n, actLev (Xo := T.Q.Xo j) T.Q.c (levFull (T.Q.Dw j) T.Q.l) γ f ∈ T.cuspA j (wtA w) w.n := by
  intro D T h j hj w γ f hf
  have hp := h.pins
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
    rw [(hp.2.2.2 j hj).1, (hp.2.2.2 j hj).2.1]
    have := hj.1; have := hj.2; have := D.R.m_add_three_le_k
    simp only [Ranks.sigW]; omega
  have hL := GlobalTheory.T.actLev_full_level_group_framedPoints D T.Q j hpq hp.2.1.2
  obtain ⟨hs, hc⟩ := (mem_cusp _ _ _ _ _ _).1 hf
  have hg : actLev (Xo := T.Q.Xo j) T.Q.c (levFull (T.Q.Dw j) T.Q.l) γ f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n :=
    actL_mem _ _ _ _ hL.total hL.nat hL.bor _ γ hs
  refine (mem_cusp _ _ _ _ _ _).2 ⟨hg, fun σ hσ => holCusp_mem_holSub _ _ fun k => ?_⟩
  have hU := h.unf j hj σ hσ
  refine GlobalTheory.LevelCusp.rdU_mem_SS (U := Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hσ hU (hU.1 ▸ hpq)
    (fun k k' τ => (h.xiAbs j hj σ hσ k τ).trans (h.xiAbs j hj σ hσ k' τ).symm) (dom_wtA w) hs hg
    (fun k => GlobalTheory.CuspSecFin.mem_SS_of_mem_holSub _ _ (hc σ hσ) k) (fun y => ?_) k
  obtain ⟨ρ, ν, -, -, hm⟩ := mvPt_spec hL.total γ y
  exact ⟨ρ, ν, _, hm, evalAt_actL hL (h.evalWD j hj) frMap_trans_id γ hs.1 y⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelActionMemCuspFormsStatement
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelAction_mem_cuspForms : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (γ : LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l), ∀ f ∈ T.cuspA j (wtA w) w.n, actLev (Xo := T.Q.Xo j) T.Q.c (levFull (T.Q.Dw j) T.Q.l) γ f ∈ T.cuspA j (wtA w) w.n := by
  first | exact @GlobalTheory.LevelCusp.actLev_mem_cuspA | exact GlobalTheory.LevelCusp.actLev_mem_cuspA | (intros; apply GlobalTheory.LevelCusp.actLev_mem_cuspA <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicValueTranslateEqUnitMulNormaliserThetaVa
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PtTie

theorem addVal_eq_zero_of_pow_eq_one {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) (u : F) (m : ℕ) (hm : 0 < m)
    (hu : u ^ m = 1) : v u = 0 := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne'] at hu
    exact zero_ne_one hu
  have h1 : m • v u = 0 := by rw [← AddValuation.map_pow, hu, AddValuation.map_one]
  have ht : v u ≠ ⊤ := by rwa [Ne, AddValuation.top_iff]
  lift v u to ℚ using ht with q hq
  have h3 : m • q = 0 := by exact_mod_cast h1
  rw [nsmul_eq_mul] at h3
  rcases mul_eq_zero.mp h3 with h | h
  · exact absurd h (by exact_mod_cast hm.ne')
  · rw [h]; rfl

theorem addVal_prod_eq_zero {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {K : Type} (s : Finset K) (u : K → F)
    (hu : ∀ i, v (u i) = 0) : v (∏ i ∈ s, u i) = 0 := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  rw [Finset.prod_insert ha, AddValuation.map_mul, hu, ih, add_zero]

theorem boxSer_smul {k : Type} [CommRing k] {n d : ℕ} (u : Fin n → k) (f : Fin n → PS k 1 d) :
    boxSer (fun i => u i • f i) = (∏ i, u i) • boxSer f := by
  simp only [boxSer, map_smul]
  simp only [Algebra.smul_def, Finset.prod_mul_distrib, map_prod]


set_option maxHeartbeats 1600000 in
theorem harmonicValue_translate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso → y.IsAlg → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (n : ℕ) (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr))) (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U) [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)), (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) → (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) → ∀ (α : 𝓞 E) (N : ℕ), N = l.M → α * star α = (N : 𝓞 E) → l.Mb = Ideal.span {star α} → ∀ (θ : Fam D'.toPre F 1) (θα : Fam D'.toPre F (1 * N)), ThFrame D' ϖ F θ → PullAl D' F oD' α 1 N θ θα → ∀ (p : QkPt D'.toPre F (1 * N)) (w : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p.g.b) (DegPre.lineε (1 * N)))) (ζ : F) (x : TFK (R := T.V) F ⟶ A'.A) (t₀ t : Fam D'.toPre F (1 * N)) (q : ℕ) (e : 1 * N = q) (σ' : U'.toUnifPre.SecGF F q) (h : PS F n (chD C.ch)), w.IsGen → ζ ≠ 0 → FinOrd D' F (1 * N) p w ζ → QkToAkU U'.toUnifPre F (1 * N) p x → PhiRel D'.toPre F (1 * N) p w θα t₀ → Fam.IsSmul D'.toPre F ζ t₀ t → U'.toUnifPre.ExpandsG F q σ' (PowGerm.famCast (Dp := D'.toPre) (F := F) e t) → IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F q σ' h → (∀ k, x ≫ pA.pr k ≫ P.oA.act (star α) = 1) → letI := io.toAlgebra; ∃ (xx : Fin n → Dw.La) (u : F), v u = 0 ∧ ∀ (a : ((E →+* ℂ) × ℕ → ℕ)) (Pp : MvPolynomial (LtN Dw n) c.F), Pp ∈ harmA c a n → ∀ f, IsThRule Xo c nab xx Pp f → nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 q h (fun ℓ : LtN Dw n => ℓ.2.2) (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i)) (MvPolynomial.map ((algebraMap T.Fr F).comp io) Pp) = u * algebraMap T.Fr F (io (nrm Dw c a α) * evI y f) := by
  intro E _ _ _ H Dw l Xo c nab hnab T io y C hFT P hTors hAlg ϖ hϖ Q hQ F _ _ _ _ _ _ v hv n D' A' G' _ _ pD pA pG
    U' PU _ oD' hxe hoD α N hN hα hMb θ θα hθ hθα p w ζ x t₀ t q e σ' h hw hζ hFin hQk hPhi hSm hExp hGerm hx
  letI := H.starRing
  letI := io.toAlgebra
  subst hN
  obtain rfl : q = l.M := by rw [← e, Nat.one_mul]
  have hodd : Odd l.M := l.odd
  have h1 : 1 ≤ l.M := le_trans (by norm_num) l.three_le

  obtain ⟨τ, hτG, hτEL, hτT⟩ := frame1St_holds E H T.V C.I.G P (chD C.ch) C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT
    C.xT C.eT C.wPT C.15 C.17 C.18
  have hUJ : IsUnivJ C.I.G.G (Fin 1 × Fin (chD C.ch)) C.xT := GlobalTheory.T.universal_statement E H Dw l Xo c T io y C
  have hAG := GlobalTheory.GermBasic.main T.V _ _ _ P.U _ C.xT hUJ τ hτG F l.M

  letI : Algebra c.F F := ((algebraMap T.Fr F).comp io).toAlgebra
  let φ : T.Fr →ₐ[c.F] F := { algebraMap T.Fr F with commutes' := fun _ => rfl }
  obtain ⟨yF, hyF⟩ := GlobalTheory.FramedBaseChange.exists_frMap GlobalTheory.firstFiveLaws.1 E H Dw l Xo c T.Fr F φ y.1

  obtain ⟨θ₁, θα₁, hθ₁, hθα₁, hcol⟩ := GlobalTheory.OneColTranslate.oneColumn_translate E H Dw l Xo c T io y.1 C.I P ϖ hϖ F φ rfl
    yF hyF α l.M hodd hα

  obtain ⟨u₀, p₁, w₁, ζ₁, r₀, r, σ₁, f, hu₀, hhf, hcols⟩ := GlobalTheory.ColumnSplit.main E H Dw l Xo c T io y C hFT P hTors hAlg
    ϖ hϖ Q hQ F v hv n D' A' G' pD pA pG U' PU oD' hxe hoD τ hτG hτEL α l.M h1 hα θ₁ θα₁ hθ₁ hθα₁ θ θα hθ hθα p w ζ x t₀
    t l.M e σ' h hw hζ hFin hQk hPhi hSm hExp hGerm
  have hall := fun i => hcol (p₁ i) (w₁ i) (ζ₁ i) (x ≫ pA.pr i) (r₀ i) (r i) (σ₁ i) (hcols i).1 (hcols i).2.1
    (hcols i).2.2.1 ((Category.assoc _ _ _).trans (hx i)) (hcols i).2.2.2.1 (hcols i).2.2.2.2.1 (hcols i).2.2.2.2.2.1
  choose U B HH S0 hU hB hTP hTie hσ using hall

  have hex : ∀ i, ∃ g, GermA P.U.toUnifPre C.xT τ F l.M (S0 i) g := fun i => hAG.2.2 (hτT hFT) (S0 i)
  choose f' hf' using hex
  have hff : ∀ i, f i = U i • f' i := by
    intro i
    have hlin := hAG.2.1 1 (fun _ => U i) (fun _ => S0 i) (fun _ => f' i) (σ₁ i) (fun _ => hf' i)
      (by intro jj; rw [Fin.sum_univ_one]; exact hσ i jj)
    have := hAG.1 (σ₁ i) _ _ (hcols i).2.2.2.2.2.2 hlin
    rw [Fin.sum_univ_one] at this
    exact this
  have hh2 : h = (u₀ * ∏ i, U i) • boxSer f' := by
    rw [hhf, show f = fun i => U i • f' i from funext hff, boxSer_smul, smul_smul]
  have hv0 : v (u₀ * ∏ i, U i) = 0 := by
    rw [AddValuation.map_mul, hu₀, zero_add]
    refine addVal_prod_eq_zero v Finset.univ U (fun i => ?_)
    obtain ⟨m, hm, hum⟩ := hU i
    exact addVal_eq_zero_of_pow_eq_one v (U i) m hm hum

  have hT := GlobalTheory.harmonic_value_of_tied_sections E H Dw l Xo c nab hnab T io y C P τ hτG hτEL F φ rfl yF hyF l.M n S0
    HH f' hTie hf'
  obtain ⟨xx, Fs, hFs, hA⟩ := GlobalTheory.AlphaForm.alphaForm_at_point E H Dw l Xo c nab hnab F yF α hα hMb n B HH hB hTP
  refine ⟨xx, u₀ * ∏ i, U i, hv0, ?_⟩
  intro a Pp hP fth hth
  have h9918 := GlobalTheory.PtTie.evI_eq_thExpr_ext E H Dw l Xo c nab hnab T io y F φ rfl yF hyF a n xx Pp hP Fs hFs fth hth
  have key : ∀ (g : PS F n (chD C.ch)) (s : F),
      nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 l.M (s • g) (fun ℓ : LtN Dw n => ℓ.2.2)
        (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i))
        (MvPolynomial.map ((algebraMap T.Fr F).comp io) Pp) =
      s * nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 l.M g (fun ℓ : LtN Dw n => ℓ.2.2)
        (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i))
        (MvPolynomial.map ((algebraMap T.Fr F).comp io) Pp) := by
    intro g s
    have := (GlobalTheory.PowGerm.nabJet _ _ _ C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 l.M n (LtN Dw n)
      (fun ℓ : LtN Dw n => ℓ.2.2) (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i))).2.1
      (MvPolynomial.map ((algebraMap T.Fr F).comp io) Pp) (Fin 1) (fun _ => s) (fun _ => g)
    simp only [Fin.sum_univ_one] at this
    exact this
  have hT' := hT a Pp hP
  rw [hA a Pp hP] at hT'
  rw [hh2, key, map_mul, h9918]
  exact congrArg (fun z => (u₀ * ∏ i, U i) * z) hT'.symm

end GlobalTheory.PtTie
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevActMemMlat
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.FormTies

theorem fromTest_mvPt {K : Type} [Field K] {ιB : Type}
    {pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type}
    {mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
      (S →ₐ[K] T) → pts S → pts T → Prop}
    {borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ιB → Sˣ) → pts S → pts S → Prop}
    {G : Type} [Group G] {actR : ∀ {S : Type} [CommRing S] [Algebra K S], G → pts S → pts S → Prop}
    (hL : ActLaws pts mapR borR actR) (g : G) {S : Type} [CommRing S] [Algebra K S] {y : pts S}
    (hy : FromTest pts mapR y) : FromTest pts mapR (mvPt pts actR g y) := by
  obtain ⟨p, φ, z, hz⟩ := hy
  exact ⟨p, φ, _, hL.nat g _ S φ z _ y _ hz (mvPt_spec hL.total g z) (mvPt_spec hL.total g y)⟩

theorem levAct_mem_Mlat : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (P : Type) (ℓ : P → (LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l)) (act : P → (recB h.toLawsCore).Cusp j w → (recB h.toLawsCore).Cusp j w), IsLevAct T h j w ℓ act → ∀ g, ∀ F ∈ (recB h.toLawsCore).Mlat j w, act g F ∈ (recB h.toLawsCore).Mlat j w := by
  intro D T h j hj w P ℓ act hact g F hF
  have hp := h.pins
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
    rw [(hp.2.2.2 j hj).1, (hp.2.2.2 j hj).2.1]
    have := hj.1; have := hj.2; have := D.R.m_add_three_le_k
    simp only [Ranks.sigW]; omega
  have hL := GlobalTheory.T.actLev_full_level_group_framedPoints D T.Q j hpq hp.2.1.2
  have hc : (F.1 : T.R j) ∈ T.C j w := cutR_le T.C j w F.2
  have hnat := ((mem_cusp _ _ _ _ _ _).1 hc).1.1
  rintro la _ ⟨⟨q, S, io, e, ho, y, hy, η, hη, rfl⟩, rfl⟩
  let := io.toAlgebra
  have hmv := mvPt_spec hL.total (ℓ g) y.1
  let y' : IntFr (T.Q.Xo j) T.Q.c S io :=
    ⟨_, fromTest_mvPt hL (ℓ g) y.2.1, GlobalTheory.T.integral_framedPoint_of_level_move _ _ _ _ _ _ (levFull (T.Q.Dw j) T.Q.l (ℓ g)) S io y.1 _ hmv y.2.2⟩
  have h0 : 0 ≤ nval S.V e (evI y' F.1) := hF la _ ⟨PtV.mk la ho y' hy () trivial, rfl⟩
  have e1 : evI y (act g F).1 = evI y' F.1 := by
    rw [hact g F]
    exact evalAt_actL hL (h.evalWD j hj) frMap_trans_id (ℓ g) hnat y.1
  show 0 ≤ nval S.V e (evI y (act g F).1)
  rw [e1]
  exact h0

end GlobalTheory.FormTies
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnscaledWeightDepthFiniteBoundedAboveCharts
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnscaledWeightDepthFiniteBoundedAboveCharts
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

namespace GlobalTheory.DepthBd

section Gen
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]

theorem nuW_eq_zero (hE : IntChartEx Xo c) (hS : ChartSaturated Xo c) (la : HeightOneSpectrum (𝓞 c.F)) (k : ℕ)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (ha : DomW Dw a) (hn : Fintype.card (Lt1 Dw) ≤ n)
    (hl : Formalism.L2.Pj.DF Dw a < resCharOf la) : nuW Xo c la k a n = 0 := by
  refine max_eq_left ?_
  refine iSup_le fun T => iSup_le fun io => iSup_le fun e => iSup_le fun ho => iSup_le fun y => iSup_le fun hy => ?_
  obtain ⟨C⟩ := hE T io y hy
  letI := io.toAlgebra
  exact (iInf_le _ C).trans ((crude_inf C.ch.B C.ch.h C.ch.gauge H.w0 k C.ch.uvec (satDir_of hS C) a n ha hn ho).2 hl)

theorem nuLocC_le_nuW (hI : ChartIndep Xo c) (la : HeightOneSpectrum (𝓞 c.F)) (k : ℕ)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (ho : OverLa la T.V io e)
    (z : IntFr Xo c T io) (hz : z.IsAlg) (C : IntegralChartA3 Xo c T io z) :
    nuLocC C e k a n ≤ nuW Xo c la k a n := by
  have h1 : nuLocC C e k a n ≤ nuLoc z e k a n := le_iInf fun C' => (hI T io z C C' e k a n).le
  refine h1.trans (le_trans ?_ (le_max_right _ _))
  unfold nuSup
  exact le_iSup_of_le T (le_iSup_of_le io (le_iSup_of_le e (le_iSup_of_le ho (le_iSup_of_le z
    (le_iSup_of_le hz le_rfl)))))
end Gen

theorem ereal_unit {x : EReal} {r d q : ℝ} (hr : 0 < r) (hd : 0 ≤ d) (hq : 0 < q) (h0 : 0 ≤ x)
    (h1 : x ≤ max 0 ((r * d / q : ℝ) : EReal)) :
    x = ((r * (x.toReal / r) : ℝ) : EReal) ∧ 0 ≤ x.toReal / r ∧ x.toReal / r ≤ d / q := by
  have hb : (0 : ℝ) ≤ r * d / q := by positivity
  rw [max_eq_right (by exact_mod_cast hb)] at h1
  have ht : x ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) h1
  have hb' : x ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) h0
  lift x to ℝ using ⟨ht, hb'⟩
  have h0' : 0 ≤ x := by exact_mod_cast h0
  have h1' : x ≤ r * d / q := by exact_mod_cast h1
  rw [EReal.toReal_coe]
  refine ⟨by rw [mul_div_cancel₀ _ hr.ne'], by positivity, ?_⟩
  rw [div_le_iff₀ hr]
  calc x ≤ r * d / q := h1'
    _ = d / q * r := by ring

theorem nuWt_bounds : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j), 2 * D.R.f * D.R.r ≤ w.n → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)), letI := T.Q.H.starRing; nuW (T.Q.Xo j) T.Q.c la T.Q.l.M (wtA w) w.n = (((ramOverZ la : ℝ) * nuWt T w la : ℝ) : EReal) ∧ 0 ≤ nuWt T w la ∧ nuWt T w la ≤ (WeightAlgebra.DF w : ℝ) / ((resCharOf la : ℝ) - 1) ∧ (WeightAlgebra.DF w < resCharOf la → nuWt T w la = 0) ∧ ∀ (T' : CDVR) (io : T.Q.c.F →+* T'.Fr) (e : ℕ), OverLa la T'.V io e → ∀ z : IntFr (T.Q.Xo j) T.Q.c T' io, z.IsAlg → ∀ C : IntegralChartA3 (T.Q.Xo j) T.Q.c T' io z, nuLocC C e T.Q.l.M (wtA w) w.n ≤ (((ramOverZ la : ℝ) * nuWt T w la : ℝ) : EReal) := by
  intro D T h j hj w hn la
  letI := T.Q.H.starRing
  have hst : ∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a := fun _ => rfl
  obtain ⟨hDF, hdom, -, -, hcard, -⟩ := GlobalTheory.WeightOnDatum.weight_on_datum D T.toCore h.pins j hj w
  have hE : IntChartEx (T.Q.Xo j) T.Q.c :=
    (GlobalTheory.IntChartExists.intChart_exists _ _ _ _ (T.Q.Xo j) T.Q.c).2.1 hst
  have hI : ChartIndep (T.Q.Xo j) T.Q.c := GlobalTheory.ChartCmp.chartIndep_holds _ _ _ _ (T.Q.Xo j) T.Q.c hst
  have hS : ChartSaturated (T.Q.Xo j) T.Q.c := SaturatedCharts.saturation_charts_holds _ _
  have hn' := hcard.trans hn
  have hr : (0 : ℝ) < (ramOverZ la : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (GlobalTheory.GoodDepth.ramOverZ_ne_zero' la)
  have hq : (0 : ℝ) < (resCharOf la : ℝ) - 1 := by
    have : (1 : ℝ) < resCharOf la := by exact_mod_cast (Crude.resCharOf_prime la).one_lt
    linarith
  have hle := nuW_le_crude hE hS la T.Q.l.M (wtA w) w.n hdom hn'
  rw [hDF] at hle
  obtain ⟨a1, a2, a3⟩ := ereal_unit hr (Nat.cast_nonneg (WeightAlgebra.DF w)) hq (le_max_left _ _) hle
  refine ⟨a1, a2, a3, fun hl => ?_, fun T' io e ho z hz C => ?_⟩
  · unfold nuWt
    rw [nuW_eq_zero hE hS la T.Q.l.M (wtA w) w.n hdom hn' (hDF ▸ hl)]
    simp
  · exact (nuLocC_le_nuW hI la T.Q.l.M (wtA w) w.n T' io e ho z hz C).trans a1.le

end GlobalTheory.DepthBd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnscaledWeightDepthFiniteBoundedAboveChartsStatement
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unscaledWeightDepth_finite_bounded_above_charts : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j), 2 * D.R.f * D.R.r ≤ w.n → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)), letI := T.Q.H.starRing; nuW (T.Q.Xo j) T.Q.c la T.Q.l.M (wtA w) w.n = (((ramOverZ la : ℝ) * nuWt T w la : ℝ) : EReal) ∧ 0 ≤ nuWt T w la ∧ nuWt T w la ≤ (WeightAlgebra.DF w : ℝ) / ((resCharOf la : ℝ) - 1) ∧ (WeightAlgebra.DF w < resCharOf la → nuWt T w la = 0) ∧ ∀ (T' : CDVR) (io : T.Q.c.F →+* T'.Fr) (e : ℕ), OverLa la T'.V io e → ∀ z : IntFr (T.Q.Xo j) T.Q.c T' io, z.IsAlg → ∀ C : IntegralChartA3 (T.Q.Xo j) T.Q.c T' io z, nuLocC C e T.Q.l.M (wtA w) w.n ≤ (((ramOverZ la : ℝ) * nuWt T w la : ℝ) : EReal) := by
  first | exact @GlobalTheory.DepthBd.nuWt_bounds | exact GlobalTheory.DepthBd.nuWt_bounds | (intros; apply GlobalTheory.DepthBd.nuWt_bounds <;> assumption)
end
end
