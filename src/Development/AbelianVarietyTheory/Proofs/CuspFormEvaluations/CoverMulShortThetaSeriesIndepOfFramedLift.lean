module

public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsQuotEquiv
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsLevMoveOfFrOver
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaValueExistsUniqueNaturalOfLaws

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CoverMulShortThetaSeriesIndepOfFramedLift
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CoverMulShortThetaSeriesIndepOfFramedLift
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShortLiftInvariance

theorem shortValAt_smul {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (nab : NabV Xo c) {n : ℕ}
    (w w' : (Fin n → LevQ Dw l) → c.F) (t : c.F) (hw : ∀ q, w' q = t * w q)
    (Λ : GenLat E n) (β : c.F) (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S)
    (h : ShortValAt Xo c nab w Λ β N P y v) :
    ShortValAt Xo c nab w' Λ β N P y (algebraMap c.F S t * v) := by
  obtain ⟨S', i1, i2, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨S', i1, i2, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, ?_⟩
  rw [map_mul, AlgHom.commutes, h7]
  simp only [hw, map_mul, _root_.mul_assoc]
  by_cases hf : Finite (Fin n → LevQ Dw l)
  · have := Fintype.ofFinite (Fin n → LevQ Dw l)
    simp only [finsum_eq_sum_of_fintype]
    rw [← Finset.mul_sum]
    ring
  · have := not_finite_iff_infinite.mp hf
    simp [Nat.card_eq_zero_of_infinite]

theorem cover_product_indep_of_lift : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), @ToroidalLevelCompatibility E _ _ _ H Dw → d.IsLev → d.l₂.A = l.A → ∀ [StarRing (𝓞 E)], IsNab d.Xo₂ d.c₂ d.nab₂ → (∃ ph ψ x₀, d.PhiPin ph ψ x₀ ∧ d.PsiTie ψ) → ∀ (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt d.l₂.M → Λ.LevOK N d.l₂.M → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) d.c₂.F), P ∈ HHa Dw.mult n d.c₂.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (x0 : Fin n → Dw.La) (β : d.c₂.F), ∀ (r' : d.Xo₂.X ⟶ Xo.X) (m' : SABMap d.Xo₂.univ.t Xo.univ.t r'), DeltaDat.EtaOK { d with r := r', m := m' } → ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k], (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) → ∀ (y : FrPt Xo c k) (y₂ y₂' : FrPt d.Xo₂ d.c₂ k), FrOver d y₂ y → FrOver { d with r := r', m := m' } y₂' y → ∀ v v', ShortValAt d.Xo₂ d.c₂ d.nab₂ (d.w x0) Λ β N P y₂ v → ShortValAt d.Xo₂ d.c₂ d.nab₂ (d.w x0) Λ β N P y₂' v' → evR d.Xo₂ d.c₂ d.cδ y₂ * v = evR d.Xo₂ d.c₂ d.cδ y₂' * v' := by
  intro hL hC E _ _ _ H Dw l Xo c n d hN1 hLev hA _ hNab hex Λ N hU hT hO a P hP x0 β r' m' hE k _ _ _ _ hk y y₂ y₂' hF hF' v v' hv hv'
  obtain ⟨ph, ψ, x₀, hph, hpsi⟩ := hex
  obtain ⟨hDvd, hM, hcop, hMb, hI, hEta, -, -, -⟩ := hLev
  obtain ⟨g, ρ, ν, hg, hρ, hmv, hfm⟩ :=
    GlobalTheory.exists_levMove_of_frOver hL E H Dw l Xo c n d hN1 hDvd hM hEta r' m' hE k hk y y₂ y₂' hF hF'
  obtain ⟨kI, σq, hk1, hk2, hk3⟩ :=
    GlobalTheory.DatumInverseCharacter.datum_inv_char E H Dw l Xo c n d hM hcop hMb hI hDvd ph ψ x₀ hph g hg
  have hx : y₂'.x = y₂.x ≫ ρ.hom := by
    unfold FrMove at hfm
    exact hfm.1
  have hmod : ∀ a : Dw.La, Dw.ModN d.l₂.A ((g.f d.l₂.A) a - a) := by
    intro a
    rw [hA]
    unfold Sim.InGam at hg
    exact hg.2.2 a
  unfold DeltaDat.PsiTie at hpsi
  have hev := hpsi kI g ρ hg hmod hρ hk1 k y₂ y₂' hx
  have h1 := GlobalTheory.T.shortThetaValue_under_levelMove hL hC E H Dw d.l₂ d.Xo₂ d.c₂ _ hNab k ρ.hom ν (g.f d.l₂.M) (g.f d.l₂.A)
    y₂ y₂' hmv hfm σq hk2 n a P hP (d.w x0) Λ β N v' hv'
  have hw : ∀ q, d.w x0 q = d.eF ↑(ψ kI) * d.w x0 (fun b => σq.symm (q b)) := by
    intro q
    rw [hk3, ← _root_.mul_assoc, ← map_mul, Units.mul_inv, map_one, _root_.one_mul]
  have h2 := shortValAt_smul d.Xo₂ d.c₂ _ _ (d.w x0) (d.eF ↑(ψ kI)) hw Λ β N P y₂ v' h1
  have hu := (GlobalTheory.T.shortThetaValue_existsUnique_natural_of_laws hL hC E H Dw d.l₂ d.Xo₂ d.c₂ _ hNab n Λ N hU hT hO a P hP (d.w x0) β).1 k y₂
  rw [hu.unique hv h2, hev]
  ring

end GlobalTheory.ShortLiftInvariance
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CoverMulShortThetaSeriesIndepOfFramedLiftStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cover_mul_shortThetaSeries_indep_of_framed_lift : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), @ToroidalLevelCompatibility E _ _ _ H Dw → d.IsLev → d.l₂.A = l.A → ∀ [StarRing (𝓞 E)], IsNab d.Xo₂ d.c₂ d.nab₂ → (∃ ph ψ x₀, d.PhiPin ph ψ x₀ ∧ d.PsiTie ψ) → ∀ (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt d.l₂.M → Λ.LevOK N d.l₂.M → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) d.c₂.F), P ∈ HHa Dw.mult n d.c₂.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (x0 : Fin n → Dw.La) (β : d.c₂.F), ∀ (r' : d.Xo₂.X ⟶ Xo.X) (m' : SABMap d.Xo₂.univ.t Xo.univ.t r'), DeltaDat.EtaOK { d with r := r', m := m' } → ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k], (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) → ∀ (y : FrPt Xo c k) (y₂ y₂' : FrPt d.Xo₂ d.c₂ k), FrOver d y₂ y → FrOver { d with r := r', m := m' } y₂' y → ∀ v v', ShortValAt d.Xo₂ d.c₂ d.nab₂ (d.w x0) Λ β N P y₂ v → ShortValAt d.Xo₂ d.c₂ d.nab₂ (d.w x0) Λ β N P y₂' v' → evR d.Xo₂ d.c₂ d.cδ y₂ * v = evR d.Xo₂ d.c₂ d.cδ y₂' * v' := by
  first | exact @GlobalTheory.ShortLiftInvariance.cover_product_indep_of_lift | exact GlobalTheory.ShortLiftInvariance.cover_product_indep_of_lift | (intros; apply GlobalTheory.ShortLiftInvariance.cover_product_indep_of_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CuspFormHalfSupAtOrthonormalFrameFirstMin
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FirstMinimumBoundAtHalfSupremumCuspForm
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FirstMinimumBoundAtHalfSupremumCuspForm
noncomputable section

namespace GlobalTheory.RunIn

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

theorem firstMin_at_halfMax : ∀ (D : D7) (T : Top D) (_h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ f ∈ T.C j w, ∀ (k : (T.U j σ).Comp), ∀ z0 ∈ ((T.U j σ).X k).dom, (∀ x ∈ ((T.U j σ).X k).dom, ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) x ≤ 2 * ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) z0) → 0 < ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) z0 → 0 < ((T.U j σ).X k).firstMinimumSq z0 ∧ Real.log (1 / ((T.U j σ).X k).firstMinimumSq z0) ≤ 80 * large₂.sc.L := by
  intro D T hL hG large₂ j hj w hP hL2 hr σ hσ f hf k z0 hz0 hmax hpos

  have hr1 : 1 ≤ D.R.r := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    unfold Formalism.BasicNotions.Ranks.r
    omega

  have hSS : ∀ Q ∈ Formalism.L2.Pj.holSub (T.U j σ).X (laU (T.U j σ) (wtA w) w.n), ∀ c,
      Q c ∈ ((T.U j σ).X c).SS (laU (T.U j σ) (wtA w) w.n c) := by
    intro Q hQ
    unfold Formalism.L2.Pj.holSub at hQ
    induction hQ using Submodule.span_induction with
    | mem x hx => intro c; exact hx c
    | zero =>
      intro c
      exact ⟨ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.bdd_zero _ _,
        fun ξ _ x _ => ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.fj_zero _ _ _ _ _⟩
    | add x y _ _ hx hy =>
      intro c
      obtain ⟨hx1, hx2⟩ := hx c
      obtain ⟨hy1, hy2⟩ := hy c
      refine ⟨ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.bdd_add _ hx1 hy1, fun ξ hξ x' hx' => ?_⟩
      rw [Pi.add_apply, ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.fj_add _ hx1 hy1 hξ hx', hx2 ξ hξ x' hx',
        hy2 ξ hξ x' hx', add_zero]
    | smul a x _ hx =>
      intro c
      obtain ⟨hx1, hx2⟩ := hx c
      refine ⟨ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.bdd_smul _ a hx1, fun ξ hξ x' hx' => ?_⟩
      rw [Pi.smul_apply, ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.fj_smul, hx2 ξ hξ x' hx', mul_zero]
  have hcusp : (rdU (T.U j σ)) f ∈ Formalism.L2.Pj.holSub (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) := by
    unfold Formalism.L2.Pj.Core.C at hf
    exact ((Formalism.L2.Pj.mem_cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA w) w.n f).1 hf).2 σ hσ
  have hPk := hSS _ hcusp k
  obtain ⟨e, M, wg, hM1, hMlog, hwg, _hwglog, hfwlog, hk⟩ :=
    GlobalTheory.T.exists_rankOne_cuspData_log_bounds D T hL hG large₂ j hj w hP hL2 hr σ hσ
  obtain ⟨hspread, hflow, _hla, hNA, _hNC, _hg, hk0⟩ := hk k

  have hmb := ReciprocityTheory.ChartRestriction.G.FD.maxBound_holds D.R.r (e k).toX (laU (T.U j σ) (wtA w) w.n k)
    ((rdU (T.U j σ)) f k) M wg hPk (by linarith) hspread hwg hflow z0 hz0 hmax hpos
  have hk0pos : 0 < (e k).k0 := (e k).minWeight_pos
  have hk0le : (e k).k0 ≤ 2 := (e k).k0_le
  have hNApos : (0 : ℝ) < (e k).NA := by exact_mod_cast (e k).NA_pos
  have hMpos : 0 < M := by linarith
  have hfw : (0 : ℝ) < (fdeg D.host.E : ℝ) * wg + 2 := by positivity
  have hε : 0 < ReciprocityTheory.ChartRestriction.G.FD.epStar M (fdeg D.host.E) wg (e k).k0 := by
    unfold ReciprocityTheory.ChartRestriction.G.FD.epStar
    apply lt_min one_pos
    apply div_pos Real.pi_pos
    have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    positivity

  have hc : ∀ τ : ((T.U j σ).X k).Ψ, ((T.U j σ).X k).c τ = (e k).k0 := by
    intro τ
    unfold ReciprocityTheory.ChartRestriction.G.FD.Data.c
    rw [(e k).ξ0_abs τ]
    ring

  have hbpos : 0 < (e k).k0 * ReciprocityTheory.ChartRestriction.G.FD.epStar M (fdeg D.host.E) wg (e k).k0 / ((e k).NA : ℝ) ^ 2 :=
    div_pos (mul_pos hk0pos hε) (pow_pos hNApos 2)
  have hlow : (e k).k0 * ReciprocityTheory.ChartRestriction.G.FD.epStar M (fdeg D.host.E) wg (e k).k0 / ((e k).NA : ℝ) ^ 2 ≤
      ((T.U j σ).X k).firstMinimumSq z0 := by
    unfold ReciprocityTheory.ChartRestriction.G.FD.Data.firstMinimumSq
    apply le_csInf
    · by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      have h0 : ∀ v ∈ ((T.U j σ).X k).Λ, v = 0 := by
        intro v hv
        by_contra hv0
        have hin : (∑ τ, ((T.U j σ).X k).c τ * ((T.U j σ).X k).maj z0 τ (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v)) ∈
            {t | ∃ v ∈ ((T.U j σ).X k).Λ, v ≠ 0 ∧
              t = ∑ τ, ((T.U j σ).X k).c τ * ((T.U j σ).X k).maj z0 τ (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v)} :=
          ⟨v, hv, hv0, rfl⟩
        rw [hemp] at hin
        exact hin
      have hbot : Submodule.span D.host.E (((T.U j σ).X k).Λ : Set (Fin D.R.r → D.host.E)) = ⊥ :=
        Submodule.span_eq_bot.mpr h0
      rw [((T.U j σ).X k).Λ_span] at hbot
      have hmem : (Pi.single (⟨0, hr1⟩ : Fin D.R.r) (1 : D.host.E)) ∈
          (⊤ : Submodule D.host.E (Fin D.R.r → D.host.E)) := Submodule.mem_top
      rw [hbot, Submodule.mem_bot] at hmem
      have h01 := congrFun hmem ⟨0, hr1⟩
      simp at h01
    · rintro t ⟨v, hv, hv0, rfl⟩
      have hNAv : ((e k).NA : D.host.E) • v ∈ (e k).L' := (e k).NA_sub v hv
      have hNAv0 : ((e k).NA : D.host.E) • v ≠ 0 := by
        refine smul_ne_zero ?_ hv0
        exact_mod_cast (e k).NA_pos.ne'
      obtain ⟨τ0, hτ0⟩ := hmb _ hNAv hNAv0
      have hτ0' : ReciprocityTheory.ChartRestriction.G.FD.epStar M (fdeg D.host.E) wg (e k).k0 ≤
          ((T.U j σ).X k).maj z0 τ0 (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ0.1 (((e k).NA : D.host.E) • v)) := hτ0
      have hemb : ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ0.1 (((e k).NA : D.host.E) • v) =
          (Complex.ofReal ((e k).NA : ℝ)) • ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ0.1 v := by
        funext a
        simp [ReciprocityTheory.ChartRestriction.G.FD.Data.emb]
      rw [hemb, ReciprocityTheory.ChartRestriction.G.FD.FlowMajorantFlags.maj_smul _ hz0 τ0 ((e k).NA : ℝ) (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ0.1 v)] at hτ0'
      have hsum := Finset.single_le_sum
        (f := fun τ => ((T.U j σ).X k).c τ * ((T.U j σ).X k).maj z0 τ (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v))
        (fun τ _ => mul_nonneg (by rw [hc τ]; exact hk0pos.le)
          (ReciprocityTheory.ChartRestriction.G.FD.FlagSpanBounds.maj_nonneg _ hz0 τ _)) (Finset.mem_univ τ0)
      simp only [hc τ0] at hsum
      have hstep : (e k).k0 * ReciprocityTheory.ChartRestriction.G.FD.epStar M (fdeg D.host.E) wg (e k).k0 / ((e k).NA : ℝ) ^ 2 ≤
          (e k).k0 * ((T.U j σ).X k).maj z0 τ0 (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ0.1 v) := by
        rw [mul_div_assoc]
        apply mul_le_mul_of_nonneg_left _ hk0pos.le
        rw [div_le_iff₀ (pow_pos hNApos 2)]
        linarith
      exact le_trans hstep hsum
  have hla1 : 0 < ((T.U j σ).X k).firstMinimumSq z0 := lt_of_lt_of_le hbpos hlow
  refine ⟨hla1, ?_⟩

  have h1 : Real.log (1 / ((T.U j σ).X k).firstMinimumSq z0) ≤
      Real.log (1 / ((e k).k0 * ReciprocityTheory.ChartRestriction.G.FD.epStar M (fdeg D.host.E) wg (e k).k0 / ((e k).NA : ℝ) ^ 2)) :=
    Real.log_le_log (one_div_pos.mpr hla1) (one_div_le_one_div_of_le hbpos hlow)
  have hlog2 : Real.log 2 ≤ large₂.sc.L := by
    have := Real.log_two_lt_d9
    linarith
  have hε' := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfLam1Row.neg_log_epStar M (fdeg D.host.E) wg (e k).k0 hMpos hfw hk0pos hk0le
  have hε2 : -Real.log (ReciprocityTheory.ChartRestriction.G.FD.epStar M (fdeg D.host.E) wg (e k).k0) ≤ 36 * large₂.sc.L := by
    refine hε'.trans (max_le (by linarith) ?_)
    linarith
  have h1b : Real.log (1 / ((e k).k0 * ReciprocityTheory.ChartRestriction.G.FD.epStar M (fdeg D.host.E) wg (e k).k0 / ((e k).NA : ℝ) ^ 2)) =
      2 * Real.log ((e k).NA : ℝ) + Real.log (1 / (e k).k0) -
        Real.log (ReciprocityTheory.ChartRestriction.G.FD.epStar M (fdeg D.host.E) wg (e k).k0) := by
    rw [one_div_div, Real.log_div (pow_pos hNApos 2).ne' (mul_pos hk0pos hε).ne', Real.log_pow,
      Real.log_mul hk0pos.ne' hε.ne', one_div, Real.log_inv]
    push_cast
    ring
  rw [h1b] at h1
  linarith

end GlobalTheory.RunIn
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FirstMinimumBoundAtHalfSupremumCuspFormStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstMinimum_bound_at_halfSupremum_cuspForm : ∀ (D : D7) (T : Top D) (_h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ f ∈ T.C j w, ∀ (k : (T.U j σ).Comp), ∀ z0 ∈ ((T.U j σ).X k).dom, (∀ x ∈ ((T.U j σ).X k).dom, ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) x ≤ 2 * ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) z0) → 0 < ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) z0 → 0 < ((T.U j σ).X k).firstMinimumSq z0 ∧ Real.log (1 / ((T.U j σ).X k).firstMinimumSq z0) ≤ 80 * large₂.sc.L := by
  first | exact @GlobalTheory.RunIn.firstMin_at_halfMax | exact GlobalTheory.RunIn.firstMin_at_halfMax | (intros; apply GlobalTheory.RunIn.firstMin_at_halfMax <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CuspFormHalfSupAtOrthonormalFrameFirstMin
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.RunIn

theorem half_sup_at_ortho_frame : ∀ (D : D7) (T : Top D) (_h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → LastPos (T.Q.Dw j) (wtA w) → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ f ∈ T.C j w, 0 < supN (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f) → ∃ (k : (T.U j σ).Comp) (xf : ((T.U j σ).X k).dom), (∀ τ' i', ‖dmin ((T.U j σ).X k).Gm xf.1 τ' i'‖ = 1) ∧ ((T.U j σ).X k).IsOrtho xf.1 ∧ supN (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f) ≤ 2 * ‖toC (evR (T.Q.Xo j) T.Q.c f ((T.U j σ).un k xf))‖ ∧ 0 < ((T.U j σ).X k).firstMinimumSq xf.1 ∧ Real.log (1 / ((T.U j σ).X k).firstMinimumSq xf.1) ≤ 80 * large₂.sc.L := by
  intro D T hL hG large₂ j hj w hrows hL2 hn hlast σ hσ f hf hsup
  have hfs : f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n := Formalism.L2.Pj.cusp_le_sec _ _ _ _ _ hf
  have hRS := (hL.unf j hj σ hσ).2.2.2.2.1 (wtA w) w.n (dom_wtA w) f hfs
  unfold Formalism.L2.Pj.supN at hsup ⊢
  have hStop : Formalism.L2.Pj.supE (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f) ≠ ⊤ := by
    intro h
    rw [h] at hsup
    simp at hsup
  have hSpos : 0 < Formalism.L2.Pj.supE (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f) :=
    (ENNReal.toReal_pos_iff.mp hsup).1
  have hhalf := ENNReal.half_lt_self hSpos.ne' hStop
  have hhalf' := hhalf
  unfold Formalism.L2.Pj.supE at hhalf'
  obtain ⟨⟨k, x, hx⟩, hp⟩ := lt_iSup_iff.mp hhalf'
  have hB := (hRS k).2.1
  have hb := ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf_mem ((T.U j σ).X k) hx
  have hy := ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain.rmul_mem_dom ((T.U j σ).X k) hx hb
  have ho := ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ortho_bOf ((T.U j σ).X k) hx
  have hpn := ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.pnorm_rmul ((T.U j σ).X k) (laU (T.U j σ) (wtA w) w.n k)
    (rdU (T.U j σ) f k) hB x hx _ hb
  have hu1 : ∀ τ i, ‖dmin ((T.U j σ).X k).Gm
      (rmul x (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf ((T.U j σ).X k) x)) τ i‖ = 1 :=
    fun τ i => ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.dmin_ortho ((T.U j σ).X k) ho τ i
  have hpu := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.pnorm_unit ((T.U j σ).X k)
    (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) hu1
  have hrd := Formalism.L2.Pj.rdU_mem (T.U j σ) f k hy
  have hlt := (ENNReal.toReal_lt_toReal (ENNReal.div_ne_top hStop two_ne_zero)
    ENNReal.ofReal_ne_top).mpr hp
  rw [ENNReal.toReal_div, ENNReal.toReal_ofReal'] at hlt
  have hlt' : (Formalism.L2.Pj.supE (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f)).toReal / 2 <
      max (((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) x) 0 := by
    simpa using hlt
  have hm : 0 < ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) x := by
    rcases lt_max_iff.mp (lt_trans (half_pos hsup) hlt') with h | h
    · exact h
    · exact absurd h (lt_irrefl 0)
  rw [max_eq_left hm.le] at hlt'
  have hle : ∀ z ∈ ((T.U j σ).X k).dom,
      ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) z ≤
        (Formalism.L2.Pj.supE (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f)).toReal := by
    intro z hz
    have h1 : ENNReal.ofReal (((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) z) ≤
        Formalism.L2.Pj.supE (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f) := by
      unfold Formalism.L2.Pj.supE
      exact le_iSup_of_le (⟨k, ⟨z, hz⟩⟩ : Formalism.L2.Pj.FPt (T.U j σ).X) le_rfl
    exact (ENNReal.ofReal_le_iff_le_toReal hStop).mp h1
  refine ⟨k, ⟨_, hy⟩, hu1, ho, ?_, ?_⟩
  · rw [← hrd, ← hpu, hpn]
    linarith
  · exact GlobalTheory.T.firstMinimum_bound_at_halfSupremum_cuspForm D T hL hG large₂ j hj w hrows hL2 hn σ hσ f hf k _ hy
      (fun z hz => by rw [hpn]; linarith [hle z hz]) (by rw [hpn]; exact hm)

end GlobalTheory.RunIn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CuspFormHalfSupAtOrthonormalFrameFirstMinStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_halfSup_at_orthonormalFrame_firstMin : ∀ (D : D7) (T : Top D) (_h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → LastPos (T.Q.Dw j) (wtA w) → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ f ∈ T.C j w, 0 < supN (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f) → ∃ (k : (T.U j σ).Comp) (xf : ((T.U j σ).X k).dom), (∀ τ' i', ‖dmin ((T.U j σ).X k).Gm xf.1 τ' i'‖ = 1) ∧ ((T.U j σ).X k).IsOrtho xf.1 ∧ supN (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f) ≤ 2 * ‖toC (evR (T.Q.Xo j) T.Q.c f ((T.U j σ).un k xf))‖ ∧ 0 < ((T.U j σ).X k).firstMinimumSq xf.1 ∧ Real.log (1 / ((T.U j σ).X k).firstMinimumSq xf.1) ≤ 80 * large₂.sc.L := by
  first | exact @GlobalTheory.RunIn.half_sup_at_ortho_frame | exact GlobalTheory.RunIn.half_sup_at_ortho_frame | (intros; apply GlobalTheory.RunIn.half_sup_at_ortho_frame <;> assumption)
end
end
