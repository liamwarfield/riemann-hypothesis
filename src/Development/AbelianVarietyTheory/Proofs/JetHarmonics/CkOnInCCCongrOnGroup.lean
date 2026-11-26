module

public import Formalism.HermitianCurvature.StatementJF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExistsTruncatedIntegralChart
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.VVAlgebraMapNonnegDvr

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CkOnInCCCongrOnGroup
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

private theorem exp_real_smul_mem_UJset_of_inG {n : ℕ} (H X : Matrix (Fin n) (Fin n) ℂ) (hX : X.conjTranspose * H + H * X = 0)
    (t : ℝ) : (NormedSpace.exp ((t : ℂ) • X)).conjTranspose * H * NormedSpace.exp ((t : ℂ) • X) = H := by
  set Y : Matrix (Fin n) (Fin n) ℂ := (t : ℂ) • X with hYdef
  have hHX : H * X = -(X.conjTranspose * H) := eq_neg_of_add_eq_zero_right hX
  have hY : SemiconjBy H Y (-Y.conjTranspose) := by
    show H * Y = -Y.conjTranspose * H
    rw [hYdef, Matrix.mul_smul, hHX, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
      Matrix.neg_mul, Matrix.smul_mul, smul_neg]
  have key : NormedSpace.exp (-(-Y.conjTranspose)) * H * NormedSpace.exp Y = H := by
    letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
    letI : NormedSpace ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedSpace
    letI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℂ _
    exact hY.exp_neg_mul_mul_exp_eq_self
  rwa [neg_neg, Matrix.exp_conjTranspose] at key

private theorem mul_mem_UH_Hpk' {k r : ℕ} {g h : B.Mat k r} (hg : g ∈ B.GV k r) (hh : h ∈ B.GV k r) :
    g * h ∈ B.GV k r := by
  have hg' : g.conjTranspose * Hpk k r * g = Hpk k r := hg
  have hh' : h.conjTranspose * Hpk k r * h = Hpk k r := hh
  show (g * h).conjTranspose * Hpk k r * (g * h) = Hpk k r
  rw [Matrix.conjTranspose_mul, show h.conjTranspose * g.conjTranspose * Hpk k r * (g * h) = h.conjTranspose * (g.conjTranspose * Hpk k r * g) * h by
    simp only [Matrix.mul_assoc], hg', hh']

private theorem exp_smul_mem_UJset' {k r : ℕ} {X : B.Mat k r} (hX : B.inLie k r X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ B.GV k r :=
  exp_real_smul_mem_UJset_of_inG (Hpk k r) X hX t

private theorem rdV_congr_on_GV {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {X : B.Mat k r} (hX : B.inLie k r X) {f f' : B.Mat k r → E}
    (h : ∀ g ∈ B.GV k r, f g = f' g) : ∀ g ∈ B.GV k r, RdV X f g = RdV X f' g := by
  intro g hg
  simp only [RdV]
  congr 1
  funext t
  exact h _ (mul_mem_UH_Hpk' hg (exp_smul_mem_UJset' hX t))

private theorem ldV_congr_on_GV {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {X : B.Mat k r} (hX : B.inLie k r X) {f f' : B.Mat k r → E}
    (h : ∀ g ∈ B.GV k r, f g = f' g) : ∀ g ∈ B.GV k r, B.LdV X f g = B.LdV X f' g := by
  intro g hg
  simp only [B.LdV]
  congr 1
  funext t
  have hneg : -((t : ℂ) • X) = ((-t : ℝ) : ℂ) • X := by rw [Complex.ofReal_neg, neg_smul]
  rw [hneg]
  exact h _ (mul_mem_UH_Hpk' (exp_smul_mem_UJset' hX (-t)) hg)

private theorem rw_congr_on_GV {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (v : List (B.Mat k r)) (hv : ∀ X ∈ v, B.inLie k r X) {f f' : B.Mat k r → E}
    (h : ∀ g ∈ B.GV k r, f g = f' g) : ∀ g ∈ B.GV k r, B.Rw v f g = B.Rw v f' g := by
  induction v with
  | nil => exact h
  | cons X v ih =>
    exact rdV_congr_on_GV (hv X List.mem_cons_self) (ih fun Y hY => hv Y (List.mem_cons_of_mem X hY))

private theorem dLR_congr_on_GV {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (u v : List (B.Mat k r)) (hu : ∀ X ∈ u, B.inLie k r X) (hv : ∀ X ∈ v, B.inLie k r X)
    {f f' : B.Mat k r → E} (h : ∀ g ∈ B.GV k r, f g = f' g) :
    ∀ g ∈ B.GV k r, B.dLR u v f g = B.dLR u v f' g := by
  induction u with
  | nil => exact rw_congr_on_GV v hv h
  | cons X u ih =>
    exact ldV_congr_on_GV (hu X List.mem_cons_self) (ih fun Y hY => hu Y (List.mem_cons_of_mem X hY))

theorem ckOn_inCC_congr_on_group : ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (A : ℝ) (F F' : B.Mat k r → E), (∀ g ∈ B.GV k r, F g = F' g) → (B.CkOn ⊤ (B.GV k r) F → B.CkOn ⊤ (B.GV k r) F') ∧ ∀ m : ℕ, B.InCC A m F → B.InCC A m F' := by
  intro k r E _ _ A F F' h
  have hck : ∀ m : ℕ∞, B.CkOn m (B.GV k r) F → B.CkOn m (B.GV k r) F' := by
    intro m hF g₀ hg₀
    obtain ⟨U, f', hU, hg₀U, hf', hfU⟩ := hF g₀ hg₀
    exact ⟨U, f', hU, hg₀U, hf', fun g hgU hgG => (h g hgG).symm.trans (hfU g hgU hgG)⟩
  refine ⟨hck ⊤, fun m hF => ?_⟩
  unfold B.InCC B.CCle at hF ⊢
  obtain ⟨c, hc1, hc2⟩ := hF
  refine ⟨c, hck _ hc1, fun u v hu hv hlen g hg => ?_⟩
  rw [← dLR_congr_on_GV u v (fun X hX => (hu X hX).1) (fun X hX => (hv X hX).1) h g hg]
  exact hc2 u v hu hv hlen g hg

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntChartFrTrunc
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IntChartTrunc

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.L2.Pj.SaturatedCharts (toT prodPts_of_combAt combAt_of_prodPts chartTan_of tanAt_of isTan_iff' fst_comp_jetTan)

attribute [local instance] Over.cartesianMonoidalCategory


set_option maxHeartbeats 1000000 in
open ReciprocityTheory.ChartRestriction.G.Chart (tcoord) in
theorem exists_intChart_frTrunc : IntChartStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ChartTransportSt Xo c → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), ∃ C : IntegralChartA3 Xo c T io y, FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT := by
  intro hIC E _ _ _ H Dw l Xo c _ hstar hTr T io y
  have I : IntData Xo c T io y.1 := Classical.choice (by
    obtain ⟨G, t', m1, m2, ⟨ub, h1, h2, h3, h4⟩, θ, h5, w1, w2, σ, s1, θ2, r1, r2, a1, a2, p, g⟩ := y.2.2
    exact ⟨⟨G, t', m1, m2, ub, h1, h2, h3, h4, θ, h5, w1, w2, σ, s1, θ2, r1, r2, a1, a2, p, g⟩⟩)

  have hp1 : IsProper I.t'.G.hom := by
    have := Xo.univ.proper
    rw [← I.m1.cart.1.isoPullback_hom_snd]
    infer_instance
  have hprop : IsProper ((Over.pullback (spMap (algebraMap T.V (FractionRing T.V)))).obj I.G.G).hom := by
    show IsProper (pullback.snd I.G.G.hom (spMap (algebraMap T.V T.Fr)))
    rw [← I.m2.cart.1.isoPullback_inv_snd]
    infer_instance

  have hsm : Smooth I.G.G.hom := I.G.semi.smooth
  obtain ⟨n, x, hx⟩ := ReciprocityTheory.ChartRestriction.G.Chart.univChartLoc (R := T.V) I.G.G
  let v : Fin n → (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := T.V) (DualNumber T.V) ⟶ I.G.G) := fun i =>
    ReciprocityTheory.ChartRestriction.G.Chart.tvec (x := x) (Pi.single i 1)
  let tg : Fin n → (Sp (DualNumber T.V) ⟶ I.G.G.left) := fun i => (v i).left
  have htgo : ∀ i, tg i ≫ I.G.G.hom = spMap (algebraMap T.V (DualNumber T.V)) := fun i => Over.w (v i)
  have htgt : ∀ i, ReciprocityTheory.ChartRestriction.G.Chart.IsTan (toT I.G (tg i) (htgo i)) := fun i =>
    ReciprocityTheory.ChartRestriction.G.Chart.isTan_tvec hx _
  have htgc : ∀ i, tcoord hx _ (htgt i) = Pi.single i 1 := fun i => ReciprocityTheory.ChartRestriction.G.Chart.tcoord_tvec hx _
  have htan : ∀ i, IsTanAtG I.G (𝟙 (Sp T.V)) (tg i) := fun i => tanAt_of I.G _ (htgo i) (htgt i)
  let e0 := Fintype.equivFin (Fin n)

  have hcombR : ∀ (a : Fin (Fintype.card (Fin n)) → T.V) (w : Sp (DualNumber T.V) ⟶ I.G.G.left)
      (hw : w ≫ I.G.G.hom = spMap (algebraMap T.V (DualNumber T.V))),
      IsCombAtG I.G (𝟙 (Sp T.V)) (fun j => tg (e0.symm j)) a w ↔
        ∃ h : ReciprocityTheory.ChartRestriction.G.Chart.IsTan (toT I.G w hw), tcoord hx _ h = fun i => a (e0 i) := by
    intro a w hw
    rw [combAt_iff I.G hx (fun j => tg (e0.symm j)) (fun j => htgo _) (fun j => htgt _) a w hw]
    have hs : ∑ j, a j • tcoord hx _ (htgt (e0.symm j)) = fun i => a (e0 i) := by
      simp only [htgc]
      rw [← Equiv.sum_comp e0 (fun j => a j • (Pi.single (e0.symm j) (1 : T.V) : Fin n → T.V))]
      simp only [Equiv.symm_apply_apply]
      funext i
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hs]
  have hwo : ∀ w, IsTanAtG I.G (𝟙 (Sp T.V)) w → w ≫ I.G.G.hom = spMap (algebraMap T.V (DualNumber T.V)) :=
    fun w hw => hw.1.trans (Category.comp_id _)
  have hbasR : ∀ w, IsTanAtG I.G (𝟙 (Sp T.V)) w →
      ∃! a : Fin (Fintype.card (Fin n)) → T.V, IsCombAtG I.G (𝟙 (Sp T.V)) (fun j => tg (e0.symm j)) a w := by
    intro w hw
    have ht := chartTan_of I.G w hw
    refine ⟨fun j => tcoord hx _ ht (e0.symm j), (hcombR _ w (hwo w hw)).2 ⟨ht, ?_⟩, fun a ha => ?_⟩
    · funext i
      simp only [Equiv.symm_apply_apply]
    · obtain ⟨h', hh'⟩ := (hcombR a w (hwo w hw)).1 ha
      funext j
      have := congrFun hh' (e0.symm j)
      simp only [Equiv.apply_symm_apply] at this
      rw [← this]
  have hbas : ∀ w, IsTanAtG I.G (𝟙 (Sp T.V)) w →
      ∃! a : Fin n → T.V, IsCombAtG I.G (𝟙 (Sp T.V)) (m := Fintype.card (Fin n))
        (fun i => tg (e0.symm i)) (fun i => a (e0.symm i)) w := by
    intro w hw
    obtain ⟨a, ha, hu⟩ := hbasR w hw
    refine ⟨fun i => a (e0 i), by simpa only [Equiv.apply_symm_apply] using ha, fun b hb => ?_⟩
    have := hu _ hb
    funext i
    rw [← this]
    simp only [Equiv.symm_apply_apply]

  obtain ⟨d, B, uvec, xT, eT, wPT, hd, hu, hch, hfr, hpr, htr, hrig, -⟩ :=
    hIC E H T.V inferInstance I.G hprop tg htan hbas hstar
  subst hd
  let tgT : Fin (Fintype.card (Fin n)) → (Sp (DualNumber T.V) ⟶ I.G.G.left) := fun j => tg (e0.symm j)
  have chartT : IsChartG I.G (𝟙 (Sp T.V)) (Fintype.card (Fin n)) B.G.F B.A.act tgT
      (fun j => Pi.single j (1 : T.V)) xT := by
    have h0 := isChartG_reindex I.G (𝟙 (Sp T.V)) _ B.G.F B.A.act tg uvec xT hch e0.symm
    have hue : (fun ℓ => uvec (e0.symm ℓ)) = fun j => Pi.single j (1 : T.V) := by
      funext ℓ j
      rw [hu, Equiv.apply_symm_apply, Pi.single_apply]
      simp only [Fin.val_inj, eq_comm]
    rw [hue] at h0
    exact h0
  have tgBasis : (∀ j, IsTanAtG I.G (𝟙 (Sp T.V)) (tgT j)) ∧
      ∀ w, IsTanAtG I.G (𝟙 (Sp T.V)) w → ∃! a : Fin (Fintype.card (Fin n)) → T.V,
        IsCombAtG I.G (𝟙 (Sp T.V)) tgT a w := ⟨fun j => htan _, hbasR⟩

  have hDo : ∀ j, (homAt (𝟙 (Sp T.V)) (jetTan ((0 : Fin 1), j) :
      Jet T.V (Fin 1 × Fin (Fintype.card (Fin n))) (0 + 1) →ₐ[T.V] DualNumber T.V) ≫ xT 1).left ≫ I.G.G.hom =
        spMap (algebraMap T.V (DualNumber T.V)) := fun j =>
    (Over.w (homAt (𝟙 (Sp T.V)) (jetTan ((0 : Fin 1), j) :
      Jet T.V (Fin 1 × Fin (Fintype.card (Fin n))) (0 + 1) →ₐ[T.V] DualNumber T.V) ≫ xT 1)).trans
      (Category.comp_id _)
  have hDt := fun j => dir_tan I.G xT chartT.zero j (hDo j)
  have hDc : ∀ j, tcoord hx _ (hDt j) = tcoord hx _ (htgt (e0.symm j)) := by
    intro j
    obtain ⟨h, hh⟩ := (combAt_iff I.G hx _ hDo hDt (Pi.single j 1) (tgT j) (htgo _)).1 (chartT.tan j)
    rw [ReciprocityTheory.ChartRestriction.G.Chart.tcoord_congr hx rfl (htgt _) h, hh]
    simp [Pi.single_apply]

  have hubo : ∀ ℓ : Lt1 Dw, (I.ub ℓ.1 ℓ.2).left ≫ I.G.G.hom = spMap (algebraMap T.V (DualNumber T.V)) :=
    fun ℓ => Over.w _
  have hubt : ∀ ℓ : Lt1 Dw, ReciprocityTheory.ChartRestriction.G.Chart.IsTan (toT I.G _ (hubo ℓ)) := fun ℓ =>
    (isTan_iff' I.G _).1 (I.tan ℓ.1 ℓ.2)
  let uvecT : Lt1 Dw → Fin (Fintype.card (Fin n)) → T.V := fun ℓ j => tcoord hx _ (hubt ℓ) (e0.symm j)
  have dirT : ∀ ℓ : Lt1 Dw, IsCombAtG I.G (𝟙 (Sp T.V))
      (fun j : Fin (Fintype.card (Fin n)) => (homAt (𝟙 (Sp T.V))
        (jetTan ((0 : Fin 1), j) : Jet T.V (Fin 1 × Fin (Fintype.card (Fin n))) (0 + 1) →ₐ[T.V] DualNumber T.V) ≫
          xT 1).left) (uvecT ℓ) (I.ub ℓ.1 ℓ.2).left := by
    intro ℓ
    refine (combAt_iff I.G hx _ hDo hDt (uvecT ℓ) _ (hubo ℓ)).2 ⟨hubt ℓ, ?_⟩
    simp only [hDc, htgc, uvecT]
    rw [← Equiv.sum_comp e0 (fun j => tcoord hx _ (hubt ℓ) (e0.symm j) •
      (Pi.single (e0.symm j) (1 : T.V) : Fin n → T.V))]
    simp only [Equiv.symm_apply_apply]
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  obtain ⟨B', uvec', x', e', wP', h', hch', hfr', hpr', hg', hr', hgen⟩ :=
    hTr hstar T io y I _ B tgT uvecT xT eT wPT tgBasis chartT dirT hfr hpr htr hrig
  letI := io.toAlgebra
  exact ⟨⟨⟨_, B', uvec', x', e', wP', h', hch', hfr', hpr', hg', hr'⟩, I, B.G.F, B.A.act, B.ph1, B.ph2, B.sy, B.ad,
    uvecT, tgT, xT, eT, wPT, tgBasis, chartT, dirT, hfr, hpr, hgen⟩, htr⟩

end GlobalTheory.IntChartTrunc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCombinationIntegers
set_option autoImplicit false

open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory.ThetaLeast


open MvPowerSeries ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.QuadDeriv GlobalTheory.GaugeBaseChange in
theorem nabValN_algebraMap (S S' : Type) [CommRing S] [Algebra ℚ S] [CommRing S'] [Algebra ℚ S'] [Algebra S S']
    (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB S d O) (h : PS S 2 d)
    (hc : MvPowerSeries.constantCoeff h = 0) (w0 : O) (m n : ℕ) (f : PS S n d) (κ : Type) [Fintype κ]
    (cp : κ → Fin n) (u : κ → Fin d → S) (P : MvPolynomial κ S) :
    nabValN B S' (MvPowerSeries.map (algebraMap S S') h) w0 m (MvPowerSeries.map (algebraMap S S') f) cp
      (fun l j => algebraMap S S' (u l j)) (MvPolynomial.map (algebraMap S S') P) =
      algebraMap S S' (nabValN B S h w0 m f cp u P) := by
  set ψ := algebraMap S S' with hψ
  have eF : (fun i => MvPowerSeries.map ψ (B.FK S i)) = B.FK S' := by
    funext i
    change MvPowerSeries.map ψ (MvPowerSeries.map (algebraMap S S) (B.G.F i)) =
      MvPowerSeries.map (algebraMap S S') (B.G.F i)
    ext e
    simp [coeff_map, hψ]
  have eA : mapP ψ (B.actK S w0) = B.actK S' w0 := by
    funext i
    change MvPowerSeries.map ψ (MvPowerSeries.map (algebraMap S S) (B.A.act w0 i)) =
      MvPowerSeries.map (algebraMap S S') (B.A.act w0 i)
    ext e
    simp [coeff_map, hψ]
  have gC : GP (comp1 (B.actK S w0) (pt S (n := 1) d 0)) := gp_comp1 _ _ (gp_actK B w0) (gp_pt 0)
  have cL : constantCoeff (B.hL S h w0) = 0 := gt_const_ev _ (pair_points_zero_constant (gp_pt 0) gC) h hc
  have eL : MvPowerSeries.map ψ (B.hL S h w0) = B.hL S' (MvPowerSeries.map ψ h) w0 := by
    unfold FB.hL
    rw [map_ev_two _ _ _ (gp_pt _) gC, baseChange_comp1 _ _ _ (gp_pt _), eA, baseChange_pt]
  have g1 : ∀ (b : Fin n) (j : Fin 1), GP ((![pt S d b] : Fin 1 → Pt S n d) j) := by
    intro b j
    fin_cases j
    exact gp_pt b
  have cb : ∀ b : Fin n, constantCoeff (ev (n := n) ![pt S d b] (B.hL S h w0)) = 0 :=
    fun b => gt_const_ev _ (g1 b) _ cL
  have eb : ∀ b : Fin n, MvPowerSeries.map ψ (ev (n := n) ![pt S d b] (B.hL S h w0)) =
      ev (n := n) ![pt S' d b] (B.hL S' (MvPowerSeries.map ψ h) w0) := by
    intro b
    rw [map_ev ψ _ (g1 b), eL]
    congr 1
    funext j
    fin_cases j
    exact baseChange_pt ψ b
  unfold nabValN
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← MvPowerSeries.constantCoeff_map, ← GlobalTheory.dpolyN_map, eF, map_mul,
    map_expS _ _ (by
      rw [MvPowerSeries.smul_eq_C_mul, map_mul, map_sum, Finset.sum_eq_zero fun b _ => cb b, mul_zero]),
    MvPowerSeries.smul_eq_C_mul, MvPowerSeries.smul_eq_C_mul, map_mul, map_C, map_natCast ψ, map_sum,
    Finset.sum_congr rfl fun b _ => eb b]

theorem smul_mem_HHa {Ty : Type} {r : Ty → ℕ} {n : ℕ} {k : Type} [Field k] {cc : Ty → Ty} {isX : Ty → Prop}
    {a : Ty → ℕ → ℕ} (s : k) {P : MvPolynomial (Letter Ty r n) k} (hP : P ∈ HHa r n k cc isX a) :
    s • P ∈ HHa r n k cc isX a :=
  ⟨Submodule.smul_mem _ s hP.1, fun σ i i' hi t => by rw [map_smul, hP.2.1 σ i i' hi t],
    fun m hm => hP.2.2 m (MvPolynomial.support_smul hm)⟩

theorem exists_lift_integers (K : Type) [Field K] [NumberField K] (V L : Type) [CommRing V] [IsDomain V]
    [IsIntegrallyClosed V] [Field L] [Algebra V L] [IsFractionRing V L] (io : K →+* L) :
    ∃ φ : 𝓞 K →+* V, ∀ x : 𝓞 K, algebraMap V L (φ x) = io (x : K) := by
  have h : ∀ x : 𝓞 K, ∃ z : V, algebraMap V L z = io (x : K) := fun x =>
    IsIntegrallyClosed.algebraMap_eq_of_integral
      (IsIntegral.tower_top (R := ℤ) (map_isIntegral_int io x.isIntegral_coe))
  choose g hg using h
  have inj := IsFractionRing.injective V L
  refine ⟨⟨⟨⟨g, inj ?_⟩, fun x y => inj ?_⟩, inj ?_, fun x y => inj ?_⟩, hg⟩ <;> simp [hg]

theorem exists_combination_integers (K : Type) [Field K] [NumberField K] (T : CDVR) (io : K →+* T.Fr)
    (Ty : Type) (r : Ty → ℕ) (n : ℕ) (cc : Ty → Ty) (isX : Ty → Prop) (a : Ty → ℕ → ℕ)
    (P : MvPolynomial (Letter Ty r n) T.Fr) (hP : P ∈ HaO r n T.Fr (algebraMap T.V T.Fr).range cc isX a) :
    ∃ (s : ℕ) (c : Fin s → T.V) (Q : Fin s → MvPolynomial (Letter Ty r n) K),
      (∀ j, Q j ∈ HaO r n K (integralClosure ℤ K).toSubring cc isX a) ∧
      P = ∑ j, algebraMap T.V T.Fr (c j) • MvPolynomial.map io (Q j) := by
  classical
  obtain ⟨φ, hφ⟩ := exists_lift_integers K T.V T.Fr io
  let p : Ideal (𝓞 K) := (IsLocalRing.maximalIdeal T.V).comap φ
  haveI hp : p.IsPrime := Ideal.comap_isPrime _ _
  have hS : p.primeCompl ≤ nonZeroDivisors (𝓞 K) := p.primeCompl_le_nonZeroDivisors
  let V := Localization.subalgebra.ofField K p.primeCompl hS
  haveI : IsLocalRing V := IsLocalization.AtPrime.isLocalRing V p
  haveI : IsDedekindDomain V := IsLocalization.isDedekindDomain (𝓞 K) hS V
  haveI : IsPrincipalIdealRing V :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain V).out 3 1).1 ‹IsDedekindDomain V›
  have hu : ∀ s : p.primeCompl, IsUnit (φ s) := fun s => by
    by_contra hn
    exact s.2 ((IsLocalRing.mem_maximalIdeal _).2 hn)
  have hV : ∀ x : V, io (algebraMap V K x) ∈ (algebraMap T.V T.Fr).range := by
    rintro ⟨x, a, s, hs, rfl⟩
    obtain ⟨u, hu'⟩ := hu ⟨s, hs⟩
    refine ⟨φ a * (u⁻¹ : T.Vˣ), ?_⟩
    change _ = io (algebraMap _ K a * (algebraMap _ K s)⁻¹)
    rw [map_mul, map_mul, map_inv₀, map_units_inv, hu', hφ, hφ]
  obtain ⟨s, c, Q, hc, hQ, hsum⟩ := GlobalTheory.exists_integral_combination_of_mem_HaO Ty r n V K T.Fr io _ hV cc isX a P hP
  have hden : ∀ j, ∃ b : p.primeCompl, ∀ m, (((b : 𝓞 K) : K) • Q j).coeff m ∈ (integralClosure ℤ K).toSubring := by
    intro j
    choose g hg using (hQ j).2
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples p.primeCompl (Q j).support g
    refine ⟨b, fun m => ?_⟩
    by_cases hm : m ∈ (Q j).support
    · obtain ⟨z, hz⟩ := hb m hm
      have : (((b : 𝓞 K) : K) • Q j).coeff m = (z : K) := by
        rw [MvPolynomial.coeff_smul, ← hg m]
        have := congrArg (algebraMap V K) hz
        rw [← IsScalarTower.algebraMap_apply, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply] at this
        exact this.symm
      rw [this]
      exact z.isIntegral_coe
    · rw [MvPolynomial.coeff_smul, MvPolynomial.notMem_support_iff.1 hm, smul_zero]
      exact Subring.zero_mem _
  choose b hb using hden
  choose c' hc' using hc
  choose u hu' using hu
  refine ⟨s, fun j => c' j * ((u (b j))⁻¹ : T.Vˣ), fun j => ((b j : 𝓞 K) : K) • Q j,
    fun j => ⟨smul_mem_HHa _ (hQ j).1, hb j⟩, ?_⟩
  rw [hsum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h0 : io ((b j : 𝓞 K) : K) ≠ 0 := by
    rw [← hφ, ← hu']
    exact ((u (b j)).isUnit.map _).ne_zero
  beta_reduce
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul (MvPolynomial.map io), MvPolynomial.map_C, ← mul_assoc,
    ← map_mul, map_mul (algebraMap T.V T.Fr), map_units_inv, hu', hφ, hc', mul_assoc, inv_mul_cancel₀ h0, mul_one]

theorem totalDegree_le_DF {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    (T : CDVR) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {P : MvPolynomial (LtN Dw n) T.Fr} (hP : P ∈ FFV (Dw := Dw) T a n) :
    P.totalDegree ≤ DF Dw a := by
  have key : ∀ m ∈ P.support, (m.sum fun _ e => e) = DF Dw a := by
    intro m hm
    rw [Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma, DF]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => hP.1.2.2 m hm τ i
  exact Finset.sup_le fun m' hm' => (key m' hm').le

theorem val_algebraMap_nonneg (T : CDVR) {F : Type} [Field F] [Algebra T.Fr F] (v : AddValuation F (WithTop ℚ))
    (hv : ∀ x : T.Fr, x ≠ 0 → v (algebraMap T.Fr F x) = (((vV T.V x : ℤ) : ℚ) : WithTop ℚ)) (x : T.V) :
    0 ≤ v (algebraMap T.Fr F (algebraMap T.V T.Fr x)) := by
  by_cases hx : algebraMap T.V T.Fr x = 0
  · rw [hx, map_zero, AddValuation.map_zero]; exact le_top
  · rw [hv _ hx]
    exact_mod_cast GlobalTheory.vV_algebraMap_nonneg_dvr T x

theorem nval_le_of_val (T : CDVR) {F : Type} [Field F] [Algebra T.Fr F] (v : AddValuation F (WithTop ℚ))
    (hv : ∀ x : T.Fr, x ≠ 0 → v (algebraMap T.Fr F x) = (((vV T.V x : ℤ) : ℚ) : WithTop ℚ))
    {x z : T.Fr} (hx : x ≠ 0) {ε : F} (hε : 0 ≤ v ε) {ρ : ℚ} (hρ : v (ε * algebraMap T.Fr F z) = (ρ : WithTop ℚ))
    {δ : ℝ} (hle : (ρ : ℝ) ≤ ((vV T.V x : ℤ) : ℚ) + δ) (e : ℕ) :
    nval T.V e z ≤ nval T.V e x + ((δ / e : ℝ) : EReal) := by
  have hz : z ≠ 0 := by
    rintro rfl
    rw [map_zero, mul_zero, AddValuation.map_zero] at hρ
    exact WithTop.top_ne_coe hρ
  rw [AddValuation.map_mul, hv z hz] at hρ
  have h1 : (((vV T.V z : ℤ) : ℚ) : WithTop ℚ) ≤ (ρ : WithTop ℚ) := hρ ▸ le_add_of_nonneg_left hε
  have h2 : ((vV T.V z : ℤ) : ℚ) ≤ ρ := WithTop.coe_le_coe.1 h1
  have h3 : ((vV T.V z : ℤ) : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast h2
  rw [nval_of_ne hz, nval_of_ne hx, ← EReal.coe_add, EReal.coe_le_coe_iff, ← add_div]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg e)
  rw [Rat.cast_intCast] at hle
  linarith

theorem le_iInf_add_coe {ι : Sort*} {X : EReal} {g : ι → EReal} {δ : ℝ} (h : ∀ i, X ≤ g i + (δ : EReal)) :
    X ≤ (⨅ i, g i) + (δ : EReal) := by
  rw [← EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot δ)) (Or.inl (EReal.coe_ne_top δ))]
  exact le_iInf fun i =>
    (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot δ)) (Or.inl (EReal.coe_ne_top δ))).2 (h i)

end GlobalTheory.ThetaLeast
end
