module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedTorsionPointTorusExtensionEqOfLiesOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCompletionEqLatticeVectorAddNsmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetVacuumEqConstMulPeriodScaledJet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyMumfordClassBilinear
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmplePrincipalPolarisationEveryFibreOfGenerat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralPullbackGenericallyFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupIsogenyHeightEqDualSameDegree
public import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFlatFinrank
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFlatFinrank
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem isogeny_flat_finrank : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), IsIsogeny f →
    A.dim = B.dim ∧ Flat f.hom.left ∧ 0 < deg f ∧ ∀ y : B.X.left, f.hom.left.finrank y = deg f := by
  intro K _ A B f hf
  obtain ⟨hfin, hsurj⟩ := hf
  have hd := GlobalTheory.T.abelianVariety_dim_le_of_finite_and_of_surjective K A B f
  have hdim : A.dim = B.dim := le_antisymm (hd.1 hfin) (hd.2 hsurj)
  have hflat : Flat f.hom.left := by
    have hAg := A.smooth
    have hBg : SmoothOfRelativeDimension A.dim B.X.hom := hdim ▸ B.smooth
    have h := GlobalTheory.IsogenyQuasiInverse.flat_fibre A.X B.X A.dim A.ab B.ab hAg hBg f.hom K (𝟙 _)
    have e' : f.hom.left = ((Over.pullbackId (X := Sp K)).inv.app A.X).left ≫
        ((Over.pullback (𝟙 (Sp K))).map f.hom).left ≫
          ((Over.pullbackId (X := Sp K)).hom.app B.X).left := by
      rw [← Over.comp_left, ← Over.comp_left]
      simp
    have i1 : IsIso ((Over.pullbackId (X := Sp K)).inv.app A.X).left :=
      (Over.forget (Sp K)).map_isIso ((Over.pullbackId (X := Sp K)).inv.app A.X)
    have i2 : IsIso ((Over.pullbackId (X := Sp K)).hom.app B.X).left :=
      (Over.forget (Sp K)).map_isIso ((Over.pullbackId (X := Sp K)).hom.app B.X)
    rw [e']
    exact Flat.comp _ _
  obtain ⟨hBint, hBnoeth, -⟩ := GlobalTheory.T.abelianVariety_isIntegral_noetherian_compact K B
  have hdeg : deg f = f.hom.left.finrank B.origin := if_pos ⟨hfin, hsurj⟩
  have hconst : ∀ y : B.X.left, f.hom.left.finrank y = deg f := by
    intro y
    rw [hdeg]
    exact (Scheme.Hom.isLocallyConstant_finrank f.hom.left).apply_eq_of_preconnectedSpace y B.origin
  refine ⟨hdim, hflat, ?_, hconst⟩
  have h1 := (Scheme.Hom.one_le_finrank_iff_surjective f.hom.left).mpr hsurj B.origin
  rw [hdeg]
  exact h1

end GlobalTheory.AV.AbVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFlatFinrankStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dim_eq_flat_finrank_eq_deg_of_isIsogeny : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), IsIsogeny f → A.dim = B.dim ∧ Flat f.hom.left ∧ 0 < deg f ∧ ∀ y : B.X.left, f.hom.left.finrank y = deg f := by
  first | exact @GlobalTheory.AV.AbVar.isogeny_flat_finrank | exact GlobalTheory.AV.AbVar.isogeny_flat_finrank | (intros; apply GlobalTheory.AV.AbVar.isogeny_flat_finrank <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacEqJets
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetsOriginOppositeSignVacuumConjPeriod
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetsOriginOppositeSignVacuumConjPeriod
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FunObj.FockChi

theorem fockIn_chi_zero : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (δ t0 : ℂ), Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (Formalism.MainNotions.TaylorLogMetric.lamOf D D.host.ccK δ) t0 → ∀ i : ℕ, i + 1 ≤ D.R.m → ∀ e0 : Formalism.MainNotions.TaylorLogMetric.VC D (G.pS (.chi i D.R.m : Pair T)).rank (G.pT (.chi i D.R.m : Pair T)).rank → ℂ, Formalism.MainNotions.StandardLatticesGL3.oddE0 D D.host.ccK δ t0 _ _ e0 → ∀ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart (.chi i D.R.m)) (G.onT W.cart (.chi i D.R.m)) (N.latS (.chi i D.R.m) : Set _) (N.latT (.chi i D.R.m) : Set _) f → ∃ c : ℂˣ, ∀ k : FVar D (G.pT (.chi i D.R.m : Pair T)).rank (G.pS (.chi i D.R.m : Pair T)).rank →₀ ℕ, GlobalTheory.FunObj.fockIn W N.frC (.chi i D.R.m) f (MvPolynomial.monomial k 1) 0 = c * starRingEnd ℂ ((k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) e0) := by
  intro D T L sc G W U N δ t0 hc hδ ht i hi e0 he f hf
  have hcf := GlobalTheory.T.isVacuum_conj_of_negHermitianSpace _ _ _ _ _ _ _ _ f hf
  obtain ⟨c, hc'⟩ := GlobalTheory.T.fockJets_unitVacuum_eq_unit_mul_periodJets W.ψ W.θ (G.V (.grid (i + 1) D.R.m)) (G.V (.grid i D.R.m)) (W.cart (.grid (i + 1) D.R.m)) (W.cart (.grid i D.R.m))
    (N.fr _) (N.fr _) (N.fr_on _ ⟨hi, rfl⟩) (N.fr_on _ ⟨by omega, rfl⟩)
    (W.cart_is _ ⟨hi, le_rfl⟩) (W.cart_is _ ⟨by omega, le_rfl⟩) δ t0 hc hδ ht e0 he _ hcf
  refine ⟨Units.map (starRingEnd ℂ).toMonoidHom c, fun k => ?_⟩
  have h2 := GlobalTheory.T.fockVector_negHermitianSpace_conj_monomial W.ψ W.θ (G.V (.grid (i + 1) D.R.m)) (G.V (.grid i D.R.m)) (W.cart (.grid (i + 1) D.R.m)) (W.cart (.grid i D.R.m))
    (N.frC (.grid (i + 1) D.R.m)) (N.frC (.grid i D.R.m)) f hf.1 hf.2.inf k 0
  have e1 : N.frC (.grid (i + 1) D.R.m) = fun τ => (N.fr (.grid (i + 1) D.R.m)).1.map (tauE D τ) := rfl
  have e2 : N.frC (.grid i D.R.m) = fun τ => (N.fr (.grid i D.R.m)).1.map (tauE D τ) := rfl
  show pureTensorO _ _ _ _ _ _ _ _ f _ 0 = _
  rw [h2, e1, e2, hc' k, map_mul]
  rfl

end GlobalTheory.FunObj.FockChi
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetsOriginOppositeSignVacuumConjPeriodStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockJets_origin_oppositeSignVacuum_conjPeriod : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (δ t0 : ℂ), Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (Formalism.MainNotions.TaylorLogMetric.lamOf D D.host.ccK δ) t0 → ∀ i : ℕ, i + 1 ≤ D.R.m → ∀ e0 : Formalism.MainNotions.TaylorLogMetric.VC D (G.pS (.chi i D.R.m : Pair T)).rank (G.pT (.chi i D.R.m : Pair T)).rank → ℂ, Formalism.MainNotions.StandardLatticesGL3.oddE0 D D.host.ccK δ t0 _ _ e0 → ∀ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart (.chi i D.R.m)) (G.onT W.cart (.chi i D.R.m)) (N.latS (.chi i D.R.m) : Set _) (N.latT (.chi i D.R.m) : Set _) f → ∃ c : ℂˣ, ∀ k : FVar D (G.pT (.chi i D.R.m : Pair T)).rank (G.pS (.chi i D.R.m : Pair T)).rank →₀ ℕ, GlobalTheory.FunObj.fockIn W N.frC (.chi i D.R.m) f (MvPolynomial.monomial k 1) 0 = c * starRingEnd ℂ ((k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) e0) := by
  first | exact @GlobalTheory.FunObj.FockChi.fockIn_chi_zero | exact GlobalTheory.FunObj.FockChi.fockIn_chi_zero | (intros; apply GlobalTheory.FunObj.FockChi.fockIn_chi_zero <;> assumption)
end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker

namespace GlobalTheory.FunObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_delta (D : D7) : ∃ δ : ℂ, Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ ∧ δ ≠ 0 := by
  obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_pow_nat_eq (Formalism.MainNotions.TaylorLogMetric.discr (Formalism.MainNotions.TaylorLogMetric.lamOf D D.host.ccK 1)) (n := 12) (by norm_num)
  refine ⟨δ, ⟨Formalism.MainNotions.GlobalTheoryTheory.jnt_ccK_curve D, hδ⟩, ?_⟩
  rintro rfl
  obtain ⟨L, hL⟩ := GlobalTheory.CurveLattice.exists_periodPair_one D D.host.ccK_ne_bot
  exact GlobalTheory.CurveLattice.discr_ne_zero _ L hL (by rw [← hδ]; simp)

theorem period_ne_zero {D : D7} {δ : ℂ} (hδ : δ ≠ 0) (τ : D.what₂.Tau) : period δ τ ≠ 0 := by
  refine div_ne_zero hδ (Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 ?_))
  have : 0 < ‖tauE D τ D.host.xi0‖ := norm_pos_iff.2 ((_root_.map_ne_zero _).2 cmHost_imaginaryGenerator_ne_zero)
  positivity

theorem rank_grid_zero {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : ChiGrid.GridData L sc) (k : ℕ) (hk : k ≤ D.R.m) :
    (G.V (.grid 0 k)).rank = D.R.r + k * D.R.t := by
  have key : (columnBlock L k).sp.rank = D.R.r + k * D.R.t := by
    rcases hk.eq_or_lt with rfl | hk
    · rw [colY_m]; exact D.sp.X'_rank
    · rw [colY_lt L hk]
      exact (D.sp.Y_rank _ (min_le_right _ _)).trans (by rw [min_eq_left hk.le]; rfl)
  exact key

theorem rank_node {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : ChiGrid.GridData L sc) {X : Node}
    (h : X.InRange D.R.m) (h0 : ∀ j, X ≠ .grid 0 j) : (G.V X).rank = X.rank D := (G.isV h h0).rank

theorem even_rank_mul : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : ChiGrid.GridData L sc) (p : Pair T),
    DefPair D.R.m p → Even ((G.pS p).rank * (G.pT p).rank) := by
  intro D T L sc G p hp
  cases p with
  | chi i j =>
    obtain ⟨hi, rfl⟩ := hp
    have h1 : (G.pS (.chi i D.R.m)).rank = rankV D (i + 1) D.R.m :=
      rank_node G (X := .grid (i + 1) D.R.m) ⟨hi, le_rfl⟩ (fun j h => by cases h)
    have h2 : (G.pT (.chi i D.R.m)).rank = rankV D i D.R.m := by
      rcases i with _ | i
      · show (G.V (.grid 0 D.R.m)).rank = _
        rw [rank_grid_zero G _ le_rfl]; simp [rankV]
      · exact rank_node G (X := .grid (i + 1) D.R.m) ⟨by omega, le_rfl⟩ (fun j h => by cases h)
    rw [h1, h2]
    have hs : Odd (sLen D) := odd_sLen D
    have e : rankV D (i + 1) D.R.m = rankV D i D.R.m + sLen D := by simp only [rankV]; ring
    by_cases he : Even (rankV D i D.R.m)
    · exact he.mul_left _
    · refine Even.mul_right ?_ _
      rw [e, Nat.even_add]
      exact ⟨fun h => absurd h he, fun h => absurd h (Nat.not_even_iff_odd.2 hs)⟩
  | mu t i j => exact absurd hp id
  | core i => exact absurd hp id
  | top t j =>
    have h1 : (G.pS (.top t j)).rank = rankX D j :=
      rank_node G (X := .top j) (show j ≤ D.R.m by simp only [DefPair] at hp; omega) (fun j h => by cases h)
    rw [h1]
    exact (even_rankX D j).mul_right _

theorem fock_vac_eq_jets : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : ChiGrid.GridData L sc} (W : G.Weil)
    {U : Set T} (N : Std G U) (δ t0 : ℂ), Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 →
    Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (Formalism.MainNotions.TaylorLogMetric.lamOf D D.host.ccK δ) t0 → ∀ p : Pair T, DefPair D.R.m p →
    ∀ e0 : Formalism.MainNotions.TaylorLogMetric.VC D (G.pS p).rank (G.pT p).rank → ℂ, Formalism.MainNotions.StandardLatticesGL3.oddE0 D D.host.ccK δ t0 _ _ e0 →
    ∀ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart p) (G.onT W.cart p) (N.latS p : Set _) (N.latT p : Set _) f →
    ∃ c : ℂˣ, ∀ k : FVar D (G.pT p).rank (G.pS p).rank →₀ ℕ,
      fockIn W N.frC p f (monomial k 1) 0 =
        c * opp p ((k.prod fun v n => period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (monomial k 1) e0) := by
  intro D T L sc G W U N δ t0 hc hδ ht0 p hp e0 he0 f hf
  cases p with
  | chi i j =>
    obtain ⟨hi, rfl⟩ := hp
    exact GlobalTheory.T.fockJets_origin_oppositeSignVacuum_conjPeriod W N δ t0 hc hδ ht0 i hi e0 he0 f hf
  | mu t i j => exact absurd hp id
  | core i => exact absurd hp id
  | top t j => exact GlobalTheory.T.fockJet_vacuum_eq_const_mul_periodScaledJet W N δ t0 hc hδ ht0 t j hp e0 he0 f hf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : ChiGrid.GridData L sc} (W : G.Weil)


open Classical in
theorem normal_nonempty : ∀ μ0, L.Is μ0 → ∀ (U : Set T) (N : Std G U), Nonempty (Normal W N) := by
  intro μ0 _ U N
  have hodd := GlobalTheory.Vacuum.exists_vacuum D
  obtain ⟨δ, hc, hδ⟩ := exists_delta D
  obtain ⟨t0, ht0⟩ := (GlobalTheory.TwoTorsionPt.exists_point D D.host.ccK δ hc).1
  let e0 : ∀ p : Pair T, Formalism.MainNotions.TaylorLogMetric.VC D (G.pS p).rank (G.pT p).rank → ℂ := fun p =>
    if h : Even ((G.pS p).rank * (G.pT p).rank) then Classical.choose (hodd D.host.ccK δ hc t0 ht0 _ _ h) else 0
  have e0_is : ∀ p, DefPair D.R.m p → Formalism.MainNotions.StandardLatticesGL3.oddE0 D D.host.ccK δ t0 _ _ (e0 p) := fun p hp => by
    have h := even_rank_mul G p hp
    simp only [e0, dif_pos h]
    exact (Classical.choose_spec (hodd D.host.ccK δ hc t0 ht0 _ _ h)).1
  let vac : ∀ p : Pair T, WO (G.pS p) (G.pT p) → ℂ := fun p =>
    if h : ∃ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart p) (G.onT W.cart p) (N.latS p : Set _) (N.latT p : Set _) f
    then Classical.choose h else 0
  have vac_is : ∀ p, DefPair D.R.m p →
      IsVacO W.ψ W.θ _ _ (G.cartS W.cart p) (G.onT W.cart p) (N.latS p : Set _) (N.latT p : Set _) (vac p) := fun p hp => by
    have h := GlobalTheory.T.exists_unitVacuum_standardLattices_definitePair W N p hp
    simp only [vac, dif_pos h]
    exact Classical.choose_spec h
  let c0 : Pair T → ℂˣ := fun p =>
    if h : ∃ c : ℂˣ, ∀ k : FVar D (G.pT p).rank (G.pS p).rank →₀ ℕ,
      fockIn W N.frC p (vac p) (monomial k 1) 0 =
        c * opp p ((k.prod fun v n => period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (monomial k 1) (e0 p))
    then Classical.choose h else 1
  have kernelNorm_constant_spec : ∀ p, DefPair D.R.m p → ∀ k : FVar D (G.pT p).rank (G.pS p).rank →₀ ℕ,
      fockIn W N.frC p (vac p) (monomial k 1) 0 =
        c0 p * opp p ((k.prod fun v n => period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (monomial k 1) (e0 p)) := by
    intro p hp k
    have h := fock_vac_eq_jets W N δ t0 hc hδ ht0 p hp (e0 p) (e0_is p hp) (vac p) (vac_is p hp)
    simp only [c0, dif_pos h]
    exact Classical.choose_spec h k
  exact ⟨⟨δ, hc, t0, ht0, e0, e0_is, vac, vac_is, c0, kernelNorm_constant_spec, fun t t' j => ⟨rfl, rfl, rfl⟩⟩⟩

theorem Normal.period_ne_zero {U : Set T} {N : Std G U} (Z : Normal W N) (τ : D.what₂.Tau) : period Z.δ τ ≠ 0 := by
  refine GlobalTheory.FunObj.period_ne_zero ?_ τ
  rintro h
  obtain ⟨L, hL⟩ := GlobalTheory.CurveLattice.exists_periodPair_one D D.host.ccK_ne_bot
  have e : Z.δ ^ 12 = Formalism.MainNotions.TaylorLogMetric.discr (Formalism.MainNotions.TaylorLogMetric.lamOf D D.host.ccK 1) := Z.crv.2
  rw [h] at e
  exact GlobalTheory.CurveLattice.discr_ne_zero _ L hL (by rw [← e]; simp)

end GlobalTheory.FunObj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFormsCalculusHolomorphicAtlas
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelDbarLeibnizEvenFormMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelDbarLeibnizEvenFormMul
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

namespace GlobalTheory.CxForm.HolAtlas

theorem del_dbar_even_mul (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (w : A.Pt → Ev n) (β : A.Fld)
    (hw : A.IsForm (GlobalTheory.LineForm.fld A w)) (hβ : A.IsForm β) :
    A.del (GlobalTheory.LineForm.fld A w * β) = A.del (GlobalTheory.LineForm.fld A w) * β + GlobalTheory.LineForm.fld A w * A.del β ∧
    A.dbar (GlobalTheory.LineForm.fld A w * β) = A.dbar (GlobalTheory.LineForm.fld A w) * β + GlobalTheory.LineForm.fld A w * A.dbar β := by
  have hloc : ∀ i, A.loc (GlobalTheory.LineForm.fld A w * β) i =
      fun v => A.loc (GlobalTheory.LineForm.fld A w) i v * A.loc β i v := by
    intro i
    funext v
    unfold HolAtlas.loc
    split_ifs
    · rfl
    · simp
  have hd : ∀ α : A.Fld, A.IsForm α → ∀ (x : A.Pt) (S),
      DifferentiableAt ℝ (fun v => (bas n).repr (A.loc α x.1.1 v) S) x.crd := fun α hα x S =>
    ((hα.smooth x.1.1 S).contDiffAt ((A.e x.1.1).open_target.mem_nhds (x.ch.map_source x.2))).differentiableAt (by simp)
  have key := fun x : A.Pt => GlobalTheory.T.delOperatorAt_dbarOperatorAt_leibniz_of_commute n (A.loc (GlobalTheory.LineForm.fld A w) x.1.1) (A.loc β x.1.1) x.crd
    (GlobalTheory.LineForm.fld A w x) (hd _ hw x) (hd _ hβ x)
  have hc : ∀ (x : A.Pt) (b : Alt n), b * A.loc (GlobalTheory.LineForm.fld A w) x.1.1 x.crd = GlobalTheory.LineForm.fld A w x * b := by
    intro x b
    rw [A.loc_crd]
    exact Subalgebra.mem_center_iff.1 (w x).2 b
  constructor
  · funext x
    have := (key x).1 fun a => hc x _
    rw [A.loc_crd β x] at this
    simp only [HolAtlas.del, Pi.add_apply, Pi.mul_apply, hloc]
    exact this
  · funext x
    have := (key x).2 fun a => hc x _
    rw [A.loc_crd β x] at this
    simp only [HolAtlas.dbar, Pi.add_apply, Pi.mul_apply, hloc]
    exact this

end GlobalTheory.CxForm.HolAtlas
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelDbarLeibnizEvenFormMulStatement
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.del_dbar_leibniz_evenForm_mul : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (w : A.Pt → Ev n) (β : A.Fld),
    A.IsForm (GlobalTheory.LineForm.fld A w) → A.IsForm β →
    A.del (GlobalTheory.LineForm.fld A w * β) = A.del (GlobalTheory.LineForm.fld A w) * β + GlobalTheory.LineForm.fld A w * A.del β ∧
    A.dbar (GlobalTheory.LineForm.fld A w * β) = A.dbar (GlobalTheory.LineForm.fld A w) * β + GlobalTheory.LineForm.fld A w * A.dbar β := by
  first | exact @GlobalTheory.CxForm.HolAtlas.del_dbar_even_mul | exact GlobalTheory.CxForm.HolAtlas.del_dbar_even_mul | (intros; apply GlobalTheory.CxForm.HolAtlas.del_dbar_even_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFormsCalculusHolomorphicAtlas
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

namespace GlobalTheory

theorem formCalculus : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n),
    A.IsForm 1 ∧ (∀ (c : ℂ) (α β : A.Fld), A.IsForm α → A.IsForm β → A.IsForm (α + β) ∧ A.IsForm (α * β) ∧ A.IsForm (c • α) ∧
      A.IsForm (A.del α) ∧ A.IsForm (A.dbar α) ∧ A.del (α + β) = A.del α + A.del β ∧ A.dbar (α + β) = A.dbar α + A.dbar β ∧
      A.del (c • α) = c • A.del α ∧ A.dbar (c • α) = c • A.dbar α) ∧
    (∀ (w : A.Pt → Ev n) (β : A.Fld), A.IsForm (fld A w) → A.IsForm β →
      A.del (fld A w * β) = A.del (fld A w) * β + fld A w * A.del β ∧ A.dbar (fld A w * β) = A.dbar (fld A w) * β + fld A w * A.dbar β) ∧
    (∀ (ι : Type) (w : ι → A.Pt → Ev n) (P : MvPolynomial ι ℝ), (∀ i, A.IsForm (fld A (w i))) → A.IsForm (evalF A w P) ∧
      ((∀ i, A.del (fld A (w i)) = 0) → A.del (evalF A w P) = 0) ∧ ((∀ i, A.dbar (fld A (w i)) = 0) → A.dbar (evalF A w P) = 0)) ∧
    ∀ (M' : Type) [TopologicalSpace M'] (n' : ℕ) (A' : HolAtlas M' n') (f : M' → M), A.IsHolo A' f →
      A.pullback A' f 1 = 1 ∧ ∀ (c : ℂ) (α β : A.Fld), A.pullback A' f (α + β) = A.pullback A' f α + A.pullback A' f β ∧
        A.pullback A' f (α * β) = A.pullback A' f α * A.pullback A' f β ∧ A.pullback A' f (c • α) = c • A.pullback A' f α ∧
        (A.IsForm α → A'.IsForm (A.pullback A' f α) ∧ A'.del (A.pullback A' f α) = A.pullback A' f (A.del α) ∧
          A'.dbar (A.pullback A' f α) = A.pullback A' f (A.dbar α)) := by
  intro M _ n A
  refine ⟨(GlobalTheory.T.isForm_one_add_mul_smul M n A).1, fun c α β hα hβ => ?_, fun w β hw hβ => GlobalTheory.T.del_dbar_leibniz_evenForm_mul M n A w β hw hβ, fun ι w P hw => ?_,
    fun M' _ n' A' f hf => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := (GlobalTheory.T.isForm_one_add_mul_smul M n A).2 c α β hα hβ
    obtain ⟨d1, d2⟩ := GlobalTheory.T.holAtlas_isForm_del_dbar_smooth M n A α hα
    obtain ⟨e1, e2, e3, e4⟩ := (GlobalTheory.T.del_dbar_additive_complexLinear_one M n A).2 c α β hα hβ
    exact ⟨h1, h2, h3, d1, d2, e1, e2, e3, e4⟩
  · induction P using MvPolynomial.induction_on with
    | C r =>
      have e : evalF A w (C r) = ((r : ℂ) • (1 : A.Fld)) := by
        funext x
        simp [evalF, fld, Algebra.algebraMap_eq_smul_one]
        first | rfl | exact Subalgebra.coe_smul _ _ _ | (rw [SetLike.val_smul]; simp) | simp [Subalgebra.coe_algebraMap]
      have h1 := (GlobalTheory.T.isForm_one_add_mul_smul M n A).1
      have hf := ((GlobalTheory.T.isForm_one_add_mul_smul M n A).2 (r : ℂ) 1 1 h1 h1).2.2
      obtain ⟨⟨z1, z2⟩, hl⟩ := GlobalTheory.T.del_dbar_additive_complexLinear_one M n A
      obtain ⟨-, -, s1, s2⟩ := hl (r : ℂ) 1 1 h1 h1
      rw [e]
      exact ⟨hf, fun _ => by rw [s1, z1, smul_zero], fun _ => by rw [s2, z2, smul_zero]⟩
    | add p q hp hq =>
      have e : evalF A w (p + q) = evalF A w p + evalF A w q := by
        funext x
        simp [evalF, fld]
      obtain ⟨hp1, hp2, hp3⟩ := hp
      obtain ⟨hq1, hq2, hq3⟩ := hq
      obtain ⟨a1, -, -⟩ := (GlobalTheory.T.isForm_one_add_mul_smul M n A).2 1 _ _ hp1 hq1
      obtain ⟨l1, l2, -, -⟩ := (GlobalTheory.T.del_dbar_additive_complexLinear_one M n A).2 1 _ _ hp1 hq1
      rw [e]
      exact ⟨a1, fun h => by rw [l1, hp2 h, hq2 h, add_zero], fun h => by rw [l2, hp3 h, hq3 h, add_zero]⟩
    | mul_X p i hp =>
      have e : evalF A w (p * X i) = evalF A w p * fld A (w i) := by
        funext x
        simp [evalF, fld]
      obtain ⟨hp1, hp2, hp3⟩ := hp
      obtain ⟨-, a2, -⟩ := (GlobalTheory.T.isForm_one_add_mul_smul M n A).2 1 _ _ hp1 (hw i)
      obtain ⟨b1, b2⟩ := GlobalTheory.T.del_dbar_leibniz_evenForm_mul M n A (fun x => aeval (fun i => w i x) (p.map (algebraMap ℝ ℂ))) (fld A (w i)) hp1 (hw i)
      rw [e]
      refine ⟨a2, fun h => ?_, fun h => ?_⟩
      · change A.del (fld A _ * fld A (w i)) = 0
        rw [b1]
        change A.del (evalF A w p) * _ + _ = 0
        rw [hp2 h, h i, zero_mul, mul_zero, add_zero]
      · change A.dbar (fld A _ * fld A (w i)) = 0
        rw [b2]
        change A.dbar (evalF A w p) * _ + _ = 0
        rw [hp3 h, h i, zero_mul, mul_zero, add_zero]
  · refine ⟨funext fun x => map_one _, fun c α β => ⟨funext fun x => map_add _ _ _, funext fun x => map_mul _ _ _,
      funext fun x => map_smul (pull _) c _, fun hα => ?_⟩⟩
    obtain ⟨d1, d2⟩ := GlobalTheory.T.holAtlas_isForm_del_dbar_smooth M n A α hα
    exact ⟨GlobalTheory.T.holAtlas_isForm_pullback_holomorphic M M' n n' A A' f α hf hα, GlobalTheory.T.del_dbar_comm_pullback_of_smooth_del_dbar M M' n n' A A' f α hf hα d1 d2⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFormsCalculusHolomorphicAtlasStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothForms_calculus_holomorphicAtlas : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n),
    A.IsForm 1 ∧ (∀ (c : ℂ) (α β : A.Fld), A.IsForm α → A.IsForm β → A.IsForm (α + β) ∧ A.IsForm (α * β) ∧ A.IsForm (c • α) ∧
      A.IsForm (A.del α) ∧ A.IsForm (A.dbar α) ∧ A.del (α + β) = A.del α + A.del β ∧ A.dbar (α + β) = A.dbar α + A.dbar β ∧
      A.del (c • α) = c • A.del α ∧ A.dbar (c • α) = c • A.dbar α) ∧
    (∀ (w : A.Pt → Ev n) (β : A.Fld), A.IsForm (fld A w) → A.IsForm β →
      A.del (fld A w * β) = A.del (fld A w) * β + fld A w * A.del β ∧ A.dbar (fld A w * β) = A.dbar (fld A w) * β + fld A w * A.dbar β) ∧
    (∀ (ι : Type) (w : ι → A.Pt → Ev n) (P : MvPolynomial ι ℝ), (∀ i, A.IsForm (fld A (w i))) → A.IsForm (evalF A w P) ∧
      ((∀ i, A.del (fld A (w i)) = 0) → A.del (evalF A w P) = 0) ∧ ((∀ i, A.dbar (fld A (w i)) = 0) → A.dbar (evalF A w P) = 0)) ∧
    ∀ (M' : Type) [TopologicalSpace M'] (n' : ℕ) (A' : HolAtlas M' n') (f : M' → M), A.IsHolo A' f →
      A.pullback A' f 1 = 1 ∧ ∀ (c : ℂ) (α β : A.Fld), A.pullback A' f (α + β) = A.pullback A' f α + A.pullback A' f β ∧
        A.pullback A' f (α * β) = A.pullback A' f α * A.pullback A' f β ∧ A.pullback A' f (c • α) = c • A.pullback A' f α ∧
        (A.IsForm α → A'.IsForm (A.pullback A' f α) ∧ A'.del (A.pullback A' f α) = A.pullback A' f (A.del α) ∧
          A'.dbar (A.pullback A' f α) = A.pullback A' f (A.dbar α)) := by
  first | exact @GlobalTheory.formCalculus | exact GlobalTheory.formCalculus | (intros; apply GlobalTheory.formCalculus <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedPDivGroupFormalLawCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedPDivGroupFormalLawCoordinates
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.LawCoord

theorem evA_X {k : Type} [CommRing k] {σ : Type} [Finite σ] {A : Type} [CommRing A] [Algebra k A]
    (x : σ → A) (hx : ∀ i, IsNilpotent (x i)) (i : σ) : evA k x hx (X i) = x i := by
  have ha : HasSubst (fun i => (C (x i) : MvPowerSeries Empty A)) :=
    hasSubst_of_constantCoeff_nilpotent fun i => by simpa using hx i
  change constantCoeff (substAlgHom (R := k) ha (X i : MvPowerSeries σ k)) = x i
  rw [substAlgHom_apply, subst_X ha]
  simp

theorem main : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d),
    (∃ μ, c.IsLawOf μ) ∧ ∀ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), c.IsLawOf μ →
      (∀ i, constantCoeff (μ i) = 0) ∧ ∀ n f, c.ev₂ n (subst μ f) = Coalgebra.comul (R := k) (c.ev n f) ∧
        c.ev₂ n (cob1 μ f) = cobOne k (G.A n) (c.ev n f) := by
  intro p k _ d G c
  refine ⟨?_, fun μ hμ => ?_⟩
  · have h := fun i => ((GlobalTheory.T.chart_square_coordinates_present_levels p k d G c).2 (fun n => Coalgebra.comul (R := k) (c.x n i))
      (fun n => by rw [pullTwo_comul]; exact congrArg _ (c.res n i))).exists
    choose μ hμ using h
    exact ⟨μ, fun n i => hμ i n⟩
  have hconst : ∀ i, constantCoeff (μ i) = 0 := by
    intro i
    have h := (GlobalTheory.T.connectedChart_evalSquare_variables_swap_constant p k d G c 0).2.2.2 (μ i)
    rw [← h, hμ 0 i]
    have key : ∀ t : G.A 0 ⊗[k] G.A 0, Algebra.TensorProduct.lift (Bialgebra.counitAlgHom k (G.A 0))
        (Bialgebra.counitAlgHom k (G.A 0)) (fun _ _ => Commute.all _ _) t =
        Coalgebra.counit (R := k) (TensorProduct.lid k (G.A 0)
          (LinearMap.rTensor (G.A 0) (Coalgebra.counit (R := k) (A := G.A 0)) t)) := by
      intro t
      induction t with
      | tmul a b => simp [Algebra.TensorProduct.lift_tmul, Bialgebra.counitAlgHom_apply]
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
    rw [key, Coalgebra.rTensor_counit_comul, TensorProduct.lid_tmul, one_smul]
    exact c.aug 0 i
  refine ⟨hconst, fun n f => ?_⟩
  have hs : c.ev₂ n (subst μ f) = Coalgebra.comul (R := k) (c.ev n f) := by
    have hy : ∀ i, IsNilpotent (Coalgebra.comul (R := k) (c.x n i)) := fun i =>
      (c.nil n i).map (Bialgebra.comulAlgHom k (G.A n))
    have h1 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d) (G.A n ⊗[k] G.A n)).1 (Fin d ⊕ Fin d) (c.ev₂ n)
      (fun t => by rw [Chart.ev₂, evA_X]; exact c.nil₂ n t) μ hconst _ hy (fun i => hμ n i) f
    have h2 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d) (G.A n)).2 (G.A n ⊗[k] G.A n)
      (Bialgebra.comulAlgHom k (G.A n)) (c.x n) (c.nil n) _ hy (fun i => rfl) f
    rw [h1, ← h2]
    rfl
  refine ⟨hs, ?_⟩
  have he := GlobalTheory.T.connectedChart_evalSquare_variables_swap_constant p k d G c n
  rw [cob1, map_sub, map_sub, hs, he.1, he.2.1, cobOne_apply]

end GlobalTheory.LawCoord
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedPDivGroupFormalLawCoordinatesStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.connectedPDivGroup_formalLaw_coordinates : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), (∃ μ, c.IsLawOf μ) ∧ ∀ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), c.IsLawOf μ → (∀ i, constantCoeff (μ i) = 0) ∧ ∀ n f, c.ev₂ n (subst μ f) = Coalgebra.comul (R := k) (c.ev n f) ∧ c.ev₂ n (cob1 μ f) = cobOne k (G.A n) (c.ev n f) := by
  first | exact @GlobalTheory.LawCoord.main | exact GlobalTheory.LawCoord.main | (intros; apply GlobalTheory.LawCoord.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularNonvanishingLocusSectionProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularNonvanishingLocusSectionProperties
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp.NVRules

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem unitAt_zpow {x : X} {f : X.functionField} (h : UnitAt x f) (n : ℤ) : UnitAt x (f ^ n) := by
  have hm : Units.mk0 f h.ne_zero ∈ unitsAt x := by
    change UnitAt x ((Units.mk0 f h.ne_zero : X.functionFieldˣ) : X.functionField)
    rwa [Units.val_mk0]
  have := zpow_mem hm n
  change UnitAt x (((Units.mk0 f h.ne_zero ^ n : X.functionFieldˣ)) : X.functionField) at this
  rwa [Units.val_zpow_eq_zpow_val, Units.val_mk0] at this

theorem regAt_pow {x : X} {f : X.functionField} (h : RegAt x f) (n : ℕ) : RegAt x (f ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact (unitAt_one x).regAt
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem unitAt_of_pow {x : X} {f : X.functionField} (hf : RegAt x f) {n : ℕ} (hn : 1 ≤ n)
    (h : UnitAt x (f ^ n)) : UnitAt x f := by
  have hne : f ≠ 0 := fun e => h.ne_zero (by rw [e, zero_pow (by omega)])
  refine (unitAt_iff hne).2 ⟨hf, ?_⟩
  have e : f⁻¹ = f ^ (n - 1) * (f ^ n)⁻¹ := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hne), one_mul]
  rw [e]
  exact (regAt_pow hf _).mul h.inv.regAt

theorem unitAt_pow_iff {x : X} {f : X.functionField} (hf : RegAt x f) {n : ℕ} (hn : 1 ≤ n) :
    UnitAt x (f ^ n) ↔ UnitAt x f :=
  ⟨unitAt_of_pow hf hn, fun h => by simpa using unitAt_zpow h (n : ℤ)⟩

theorem unitAt_ratio {L : LB X} {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r) {x : X} {i j : L.ι}
    (hi : x ∈ L.U i) (hj : x ∈ L.U j) : UnitAt x ((r i : X.functionField) / r j) := by
  have h := gen_mem (memInf hi hj)
  rw [hr i j h, mul_div_cancel_right₀ _ (Units.ne_zero _)]
  exact unitAt_fnOf (memInf hi hj) h (L.g i j)

theorem loc_eq_mul (P : Pair p) (a b : ℤ) (f : X.functionField) (i i' : P.L.B.ι) (j j' : P.A.B.ι) :
    P.loc a b f i j = P.loc a b f i' j' *
      (((P.r i : X.functionField) / P.r i') ^ a * ((P.r' j : X.functionField) / P.r' j') ^ b) := by
  have h1 : ((P.r i' : X.functionField)) ^ a ≠ 0 := zpow_ne_zero _ (Units.ne_zero _)
  have h2 : ((P.r' j' : X.functionField)) ^ b ≠ 0 := zpow_ne_zero _ (Units.ne_zero _)
  simp only [Pair.loc, div_zpow]
  field_simp

theorem unitAt_loc_of (P : Pair p) (a b : ℤ) (f : X.functionField) {x : X} {i i' : P.L.B.ι} {j j' : P.A.B.ι}
    (hi : x ∈ P.L.B.U i) (hi' : x ∈ P.L.B.U i') (hj : x ∈ P.A.B.U j) (hj' : x ∈ P.A.B.U j')
    (h : UnitAt x (P.loc a b f i' j')) : UnitAt x (P.loc a b f i j) := by
  rw [loc_eq_mul P a b f i i' j j']
  exact h.mul ((unitAt_zpow (unitAt_ratio P.hr hi hi') a).mul (unitAt_zpow (unitAt_ratio P.hr' hj hj') b))

theorem mem_NV_iff (P : Pair p) (a b : ℤ) (f : X.functionField) {x : X} {i : P.L.B.ι} {j : P.A.B.ι}
    (hi : x ∈ P.L.B.U i) (hj : x ∈ P.A.B.U j) : x ∈ NV P a b f ↔ UnitAt x (P.loc a b f i j) :=
  ⟨fun h => h i j hi hj, fun h _ _ hi' hj' => unitAt_loc_of P a b f hi' hi hj' hj h⟩

theorem div_eq_loc_div (P : Pair p) (a b : ℤ) (f g : X.functionField) (i : P.L.B.ι) (j : P.A.B.ι) :
    f / g = P.loc a b f i j / P.loc a b g i j := by
  have h1 : ((P.r i : X.functionField)) ^ a ≠ 0 := zpow_ne_zero _ (Units.ne_zero _)
  have h2 : ((P.r' j : X.functionField)) ^ b ≠ 0 := zpow_ne_zero _ (Units.ne_zero _)
  simp only [Pair.loc]
  rw [mul_assoc f, mul_assoc g, mul_div_mul_right _ _ (mul_ne_zero h1 h2)]

theorem loc_pow (P : Pair p) (a b : ℤ) (g : X.functionField) (n : ℕ) (i : P.L.B.ι) (j : P.A.B.ι) :
    P.loc (n * a) (n * b) (g ^ n) i j = P.loc a b g i j ^ n := by
  simp only [Pair.loc, mul_pow]
  rw [mul_comm (n : ℤ) a, mul_comm (n : ℤ) b, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]

end GlobalTheory.HSAmp.NVRules


open GlobalTheory.HSAmp.NVRules in
theorem GlobalTheory.HSAmp.nv_rules : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (g : X.functionField), g ∈ P.H a b → IsOpen (NV P a b g) ∧ (genericPoint X ∈ NV P a b g ↔ g ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → NV P (n * a) (n * b) (g ^ n) = NV P a b g) ∧ (∀ f ∈ P.H a b, ∀ z ∈ NV P a b g, RegAt z (f / g) ∧ (z ∈ NV P a b f ↔ UnitAt z (f / g))) ∧ ∀ f ∈ P.H a b, ∀ (σ : k →+* ℂ) (y : CxPts p σ), under y ∈ NV P a b g → P.nu a b σ y f = ‖ratVal (f / g) y‖ * P.nu a b σ y g ∧ 0 < P.nu a b σ y g := by
  intro k _ X _ p P a b g hg
  have cL := fun x : X => ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart P.L.isLB x
  have cA := fun x : X => ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart P.A.isLB x
  have h4 : ∀ f ∈ P.H a b, ∀ z ∈ NV P a b g, RegAt z (f / g) ∧ (z ∈ NV P a b f ↔ UnitAt z (f / g)) := by
    intro f hf z hz
    obtain ⟨i, hi⟩ := cL z
    obtain ⟨j, hj⟩ := cA z
    have hu := (mem_NV_iff P a b g hi hj).1 hz
    rw [div_eq_loc_div P a b f g i j, mem_NV_iff P a b f hi hj]
    refine ⟨(hf z i j hi hj).mul hu.inv.regAt, fun h => h.mul hu.inv, fun h => ?_⟩
    have := h.mul hu
    rwa [div_mul_cancel₀ _ hu.ne_zero] at this
  refine ⟨?_, ?_, ?_, h4, ?_⟩
  · refine isOpen_iff_forall_mem_open.2 fun x hx => ?_
    obtain ⟨i, hi⟩ := cL x
    obtain ⟨j, hj⟩ := cA x
    obtain ⟨V, hV, hVu⟩ := ((mem_NV_iff P a b g hi hj).1 hx).exists_nhds
    refine ⟨((V ⊓ P.L.B.U i ⊓ P.A.B.U j : X.Opens) : Set X), fun y hy => ?_, Opens.isOpen _, ⟨⟨hV, hi⟩, hj⟩⟩
    obtain ⟨⟨hyV, hyi⟩, hyj⟩ := hy
    exact (mem_NV_iff P a b g hyi hyj).2 (hVu y hyV)
  · obtain ⟨i, hi⟩ := cL (genericPoint X)
    obtain ⟨j, hj⟩ := cA (genericPoint X)
    rw [mem_NV_iff P a b g hi hj]
    refine ⟨fun h e => h.ne_zero (by rw [e]; simp [Pair.loc]), fun h => unitAt_genericPoint ?_⟩
    simp only [Pair.loc]
    exact mul_ne_zero (mul_ne_zero h (zpow_ne_zero _ (Units.ne_zero _))) (zpow_ne_zero _ (Units.ne_zero _))
  · intro n hn
    ext x
    obtain ⟨i, hi⟩ := cL x
    obtain ⟨j, hj⟩ := cA x
    rw [mem_NV_iff P _ _ _ hi hj, mem_NV_iff P a b g hi hj, loc_pow]
    exact unitAt_pow_iff (hg x i j hi hj) hn
  · intro f hf σ y hy
    have hi := mem_ptsIn.1 (mem_pick (P.L.φ σ).isLB y)
    have hj := mem_ptsIn.1 (mem_pick (P.A.φ σ).isLB y)
    have hu := (mem_NV_iff P a b g hi hj).1 hy
    have hq := (h4 f hf _ hy).1
    have e : P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y) =
        f / g * P.loc a b g (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y) := by
      rw [div_eq_loc_div P a b f g (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y), div_mul_cancel₀ _ hu.ne_zero]
    refine ⟨?_, ?_⟩
    · rw [Pair.nu, Pair.nu, e, ratVal_mul hq hu.regAt, norm_mul, mul_assoc]
    · rw [Pair.nu]
      exact mul_pos (norm_pos_iff.2 (ratVal_ne_zero hu)) (Real.exp_pos _)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularNonvanishingLocusSectionPropertiesStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularNonvanishingLocusSection_properties : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (g : X.functionField), g ∈ P.H a b → IsOpen (NV P a b g) ∧ (genericPoint X ∈ NV P a b g ↔ g ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → NV P (n * a) (n * b) (g ^ n) = NV P a b g) ∧ (∀ f ∈ P.H a b, ∀ z ∈ NV P a b g, RegAt z (f / g) ∧ (z ∈ NV P a b f ↔ UnitAt z (f / g))) ∧ ∀ f ∈ P.H a b, ∀ (σ : k →+* ℂ) (y : CxPts p σ), under y ∈ NV P a b g → P.nu a b σ y f = ‖ratVal (f / g) y‖ * P.nu a b σ y g ∧ 0 < P.nu a b σ y g := by
  first | exact @GlobalTheory.HSAmp.nv_rules | exact GlobalTheory.HSAmp.nv_rules | (intros; apply GlobalTheory.HSAmp.nv_rules <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationBaseChangeOfKernelInGeneratingOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationBaseChangeOfKernelInGeneratingOpen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem unif_baseChange_of_psiUnitOn : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'], AdmBase R' (maximalIdeal R') → ∀ φ : R →+* R', IsLocalHom φ → ∀ W : (Sp R).Opens, (∀ y, PsiUnitOn D.toPre y W) → spMap φ (genericPoint (Sp R')) ∈ W → ∀ (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf φ)).obj G), IsMonHom bc.hom → ∃ (D' : DegData R' (maximalIdeal R')) (A' : PolAV (Sp (FractionRing R'))) (hD : IsPullDeg φ D.toPre D'.toPre) (U' : Unif (maximalIdeal R') D' A' G'), IsPullUnif φ hD bc U U' := by
  intro R _ _ _ hR D A G _ _ hG U R' _ _ _ hR' φ hφl W hψ hgen G' _ _ bc mbc
  obtain ⟨hL, -, -, h4, -⟩ := GlobalTheory.firstFiveLaws
  have aR := hR.1
  have hI : (maximalIdeal R).map φ ≤ maximalIdeal R' :=
    Ideal.map_le_iff_le_comap.2 fun a ha => (map_mem_nonunits_iff φ a).2 ha
  let x : Sp (FractionRing R') ⟶ Sp R := jK R' ≫ specOf φ
  have hxW : Set.range x ⊆ (W : Set (Sp R)) := by
    rintro _ ⟨z, rfl⟩
    have hz : (jK R').base z = genericPoint (Sp R') := by
      rw [genericPoint_eq_bot_of_affine]
      apply PrimeSpectrum.ext
      show Ideal.comap (algebraMap R' (FractionRing R')) z.asIdeal = ⊥
      haveI := z.isPrime
      rw [Ideal.eq_bot_of_prime z.asIdeal]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R' (FractionRing R'))
    show (specOf φ).base ((jK R').base z) ∈ W
    rw [hz]
    exact hgen
  obtain ⟨hamp, hkt⟩ := GlobalTheory.T.relAmple_principal_polarisation_every_fibre_of_generate R hR D A G hG U W hψ (FractionRing R') x hxW
  have hBs := IsSemiAbelian.pullback x G hG
  have hab : IsAbelianScheme ((Over.pullback x).obj G) :=
    ⟨hBs.comm, hBs.smooth, GlobalTheory.ZH.isProper_hom_of_relAmple hamp, hBs.geomConnected⟩
  have hpbG := isGrpPullback_pullback G x
  haveI := mbc
  have hbc : IsGrpPullback G' G (specOf φ) (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) :=
    ((isGrpPullback_of_iso bc).comp (isGrpPullback_pullback G (specOf φ))).congr (Category.id_comp _) rfl
  have hgK := (isGrpPullback_pullback G' (jK R')).comp hbc
  obtain ⟨eA, meA, heA⟩ := grpPullback_iso hgK hpbG

  have := hG.smooth
  have := hG.geomConnected
  have : ConnectedSpace (Sp R) := inferInstanceAs (ConnectedSpace (PrimeSpectrum R))
  have : ConnectedSpace G.left := GeometricallyConnected.connectedSpace G.hom G.hom.isOpenMap
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected G.hom (Classical.arbitrary _)
  have hgA := GlobalTheory.ThetaBaseChange.grp_generic U.toUnifPre
  have dA : d = A.g := H1.dim_unique _ ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hgA.1 hd)
    A.smoothDim (eSec A.A (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R)))
  have hdB : SmoothOfRelativeDimension A.g ((Over.pullback x).obj G).hom :=
    dA ▸ (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hpbG.1 hd
  let A' : PolAV (Sp (FractionRing R')) :=
    { A := (Over.pullback x).obj G
      isAb := hab
      g := A.g
      smoothDim := hdB
      L := U.LG.L.pull (pullback.fst G.hom x)
      isLB := pull_isLB U.LG.isLB _
      rigid := GlobalTheory.PolBaseChange.rigidified_pull hpbG ⟨U.LG.rig, U.LG.rigGen⟩
      sym := GlobalTheory.PolBaseChange.sym_pull hpbG (GlobalTheory.WtPoint.sym_of_cp (GlobalTheory.ValueForm.modelCP U.toUnifPre hL.globalFns))
      ample := hamp
      ktriv := hkt }
  have wA : ∃ wA : LB.Iso (A'.L.pull eA.hom.left)
      (U.LG.L.pull (pullback.fst G'.hom (jK R') ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ))), wA.IsGen := by
    rw [← heA]
    exact ⟨GlobalTheory.Proof.TautologicalModel.taut U.LG.L _ _, GlobalTheory.Proof.TautologicalModel.taut_isGen U.LG.isLB _ _⟩
  have he := GlobalTheory.PolBaseChange.eSec_comm hbc
  let L' : RigLB G' := ⟨U.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom (specOf φ)),
    rigPullOf (G' := G') (G := G) (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) (specOf φ) he U.LG.L U.LG.rig,
    pull_isLB U.LG.isLB _,
    GlobalTheory.Proof.TautologicalModel.rigPullOf_isGen (G' := G') (G := G) (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) (specOf φ) he
      U.LG.L U.LG.rig U.LG.rigGen⟩
  obtain ⟨wL, gL, rL⟩ := GlobalTheory.Unif.RigidifyIso.exists_rigidified_iso _ _ (specOf φ) G G' _ he U.LG L'
    (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB U.LG.isLB _))
  have hWne : (W : Set (Sp R)).Nonempty := ⟨_, hgen⟩
  obtain ⟨D', hD, U', -, -, hP⟩ := h4.unifBaseChange R R' _ _ aR hR' φ hI D A G hG U W
    (GlobalTheory.PelCoordPull.nonempty_psiOn D.toPre W hWne hψ) hgen G' bc mbc A' rfl eA meA wA L' wL he gL rL
  exact ⟨D', A', hD, U', hP⟩

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationBaseChangeOfKernelInGeneratingOpenStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_baseChange_of_kernel_in_generating_open : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'], AdmBase R' (maximalIdeal R') → ∀ φ : R →+* R', IsLocalHom φ → ∀ W : (Sp R).Opens, (∀ y, PsiUnitOn D.toPre y W) → spMap φ (genericPoint (Sp R')) ∈ W → ∀ (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf φ)).obj G), IsMonHom bc.hom → ∃ (D' : DegData R' (maximalIdeal R')) (A' : PolAV (Sp (FractionRing R'))) (hD : IsPullDeg φ D.toPre D'.toPre) (U' : Unif (maximalIdeal R') D' A' G'), IsPullUnif φ hD bc U U' := by
  first | exact @GlobalTheory.Mum.unif_baseChange_of_psiUnitOn | exact GlobalTheory.Mum.unif_baseChange_of_psiUnitOn | (intros; apply GlobalTheory.Mum.unif_baseChange_of_psiUnitOn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNormSectionIntegrableMixedChernProjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNormSectionIntegrableMixedChernProjective
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
namespace GlobalTheory.Mix

theorem logSec_intg_proj : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (D : ℕ), IsProjOver p → topologicalKrullDim X = (D : ℕ) → ∀ (L : Fin D → MLine p σ) (M : MLine p σ) (s : M.B.Sec), genericPoint X ∈ nonzeroLocus s → Intg L (M.logSec s) := by
  intro hP F _ X _ _ p σ D hproj hdim L M s hs
  haveI : CharZero F := RingHom.charZero σ
  obtain ⟨Y, hY, π, hsm, hprojY, hdimY, hgen, hdeg, -⟩ :=
    GlobalTheory.T.exists_logResolution_projective_of_principalisation hP F X p D hproj hdim ⊥ (fun h => h)
  haveI : Smooth (π ≫ p) := SmoothOfRelativeDimension.smooth D (π ≫ p)
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (π ≫ p)
  obtain ⟨s', hz, hn, -⟩ := GlobalTheory.T.exists_pullback_section_zeros_norm_multiplicities F X Y p (π ≫ p) σ π rfl M s
  have hs' : genericPoint Y ∈ nonzeroLocus s' := by
    rw [hz]; show π (genericPoint Y) ∈ nonzeroLocus s; rw [hgen]; exact hs
  have hsmooth := GlobalTheory.T.integrable_logNormSection_mixedChernForms F Y (π ≫ p) σ D hprojY hsm (fun i => (L i).pull π rfl) (M.pull π rfl) s' hs'
  have hmeas := (GlobalTheory.Mix.SecNorm.logSec_basic F X p σ M s).1
  have hpush := (GlobalTheory.T.mixedIntegral_pullback_genericallyFinite F X Y p (π ≫ p) σ D hproj hdim hprojY π rfl hgen (by rw [hdeg]; exact one_ne_zero) L (M.logSec s) hmeas).1
  refine hpush.1 ?_
  have hfun : (fun y => M.logSec s (ptMap π rfl σ y)) = (M.pull π rfl).logSec s' := by
    funext y; simp only [MLine.logSec]; rw [hn y]
  rw [hfun]; exact hsmooth

end GlobalTheory.Mix
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNormSectionIntegrableMixedChernProjectiveStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_norm_section_integrable_mixedChern_projective : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (D : ℕ), IsProjOver p → topologicalKrullDim X = (D : ℕ) → ∀ (L : Fin D → MLine p σ) (M : MLine p σ) (s : M.B.Sec), genericPoint X ∈ nonzeroLocus s → Intg L (M.logSec s) := by
  first | exact @GlobalTheory.Mix.logSec_intg_proj | exact GlobalTheory.Mix.logSec_intg_proj | (intros; apply GlobalTheory.Mix.logSec_intg_proj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilOverOfClauses
noncomputable section

section WeilOver

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChiGrid.WeilOver

open GlobalTheory.LatVac GlobalTheory.PlaceDatum GlobalTheory.PlaceModel Formalism.IndefR.Mult

variable {D : D7}

theorem exists_weil_over_of_clauses (hW : GlobalTheory.Published.WeilRepresentationUnitaryPair) {Γ : Type} [Group Γ] [Fintype Γ]
    {Pl0 T : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hlev : R.toLevCh.Is A.μ0) (hch : R.IsChain) (hmod : R.IsModels)
    (sc : Consts) (G : GridData R.toLevCh sc) : ∃ W : G.Weil, W.Over R := by
  have hψ := (hch.ωX A.μ0).std
  obtain ⟨W, hWψ⟩ := GlobalTheory.T.exists_weilRepresentation_vacuum_cosetVectors_grid hW D T R.toLevCh A.μ0 hlev sc G R.ψ hψ
  obtain ⟨e, he, -⟩ := W.cosVec_is
  have lt : ∀ j, j < D.R.m → G.V (.grid 0 j) = Yc D j := fun j h => congrArg LSp.sp (colY_lt R.toLevCh h)
  have top : G.V (.grid 0 D.R.m) = D.sp.X' := congrArg LSp.sp (colY_m R.toLevCh)
  have h1 : ∀ X : Node, ∃ s B, (X.InRange D.R.m → IsMaj (G.V X) s B) ∧
      (∀ j, j < D.R.m → X = .grid 0 j → HEq s (cart (R.MY j)) ∧ HEq B (onb (R.MY j))) ∧
      (X = .grid 0 D.R.m → HEq s (cart R.MX) ∧ HEq B (onb R.MX)) := fun X => by
    by_cases h : ∃ j, j < D.R.m ∧ X = .grid 0 j
    · obtain ⟨j, hj, rfl⟩ := h
      obtain ⟨s, B, a, b⟩ := exists_maj_heq (lt j hj) (R.MY j)
      refine ⟨s, B, fun _ => a, fun k _ hk => ?_, fun hk => ?_⟩
      · cases hk; exact b
      · exact absurd (Node.grid.inj hk).2 hj.ne
    by_cases h' : X = .grid 0 D.R.m
    · subst h'
      obtain ⟨s, B, a, b⟩ := exists_maj_heq top R.MX
      exact ⟨s, B, fun _ => a, fun k hk e => absurd ⟨k, hk, e⟩ h, fun _ => b⟩
    exact ⟨W.cart X, W.onb X, fun hX τ => ⟨W.cart_is X hX τ, W.onb_is X hX τ⟩, fun k hk e => absurd ⟨k, hk, e⟩ h,
      fun e => absurd e h'⟩
  have h2 : ∀ p : Pair T, ∃ ω, (p.InRange D.R.m → IsWeilDatumO R.ψ (G.pS p) (G.pT p) (G.chrS p) (G.chrT p) ω) ∧
      (∀ t k, k + 1 < D.R.m → p = .mu t 0 k → HEq ω (R.ωY t k)) ∧
      (∀ t k, k + 1 = D.R.m → p = .mu t 0 k → HEq ω (R.ωX t)) := fun p => by
    by_cases h : ∃ t k, k + 1 < D.R.m ∧ p = .mu t 0 k
    · obtain ⟨t, k, hk, rfl⟩ := h
      have := hch.ωY t k hk
      rw [← G.chr_mu_zero t hk.le] at this
      obtain ⟨ω, a, b⟩ := exists_om_heq (lt k (by omega)) (lt (k + 1) hk) this
      refine ⟨ω, fun _ => a, fun t' k' _ e => ?_, fun t' k' hk' e => ?_⟩
      · cases e; exact b
      · cases e; omega
    by_cases h' : ∃ t k, k + 1 = D.R.m ∧ p = .mu t 0 k
    · obtain ⟨t, k, hk, rfl⟩ := h'
      have e0 := G.chr_mu_zero t hk.le
      rw [hk] at e0
      have := hch.ωX t
      rw [← e0] at this
      obtain ⟨ω, a, b⟩ := exists_om_heq (S' := G.V (.grid 0 k)) (T' := G.V (.grid 0 (k + 1)))
        ((lt k (by omega)).trans (congrArg (Yc D) (by omega))) (hk ▸ top) this
      refine ⟨ω, fun _ => a, fun t' k' hk' e => ?_, fun t' k' _ e => ?_⟩
      · cases e; omega
      · cases e; exact b
    exact ⟨W.om p, fun hp => hWψ ▸ W.om_is p hp, fun t k hk e => absurd ⟨t, k, hk, e⟩ h,
      fun t k hk e => absurd ⟨t, k, hk, e⟩ h'⟩
  choose s B hs sY sX using h1
  choose om hom oY oX using h2
  obtain ⟨W', a1, a2, a3, a4, a5⟩ := exists_weil G (fun i hi => by
    have : (G.node (.grid i 0)).IsV (rankV D i 0) ((D.R.m - 0) / 2) := by
      cases i with
      | zero => exact GlobalTheory.T.gridFirstColumnSpace_rank_signature_selfDual D T R.toLevCh A.μ0 hlev 0 hi
      | succ i => exact G.sp.V_is (i + 1) 0 (by omega) hi (Nat.zero_le _)
    exact ⟨this.sigOK, this.sd⟩) he hψ hmod.inf s B hs om hom
  exact ⟨W', a1, a2, fun j hj => a3 ▸ (sY _ j hj rfl).1, a3 ▸ (sX _ rfl).1, fun j hj => a4 ▸ (sY _ j hj rfl).2,
    a4 ▸ (sX _ rfl).2, fun t k hk => a5 ▸ oY _ t k hk rfl, fun t k hk => a5 ▸ oX _ t k hk rfl⟩

end GlobalTheory.ChiGrid.WeilOver

end WeilOver

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx

namespace GlobalTheory.BigTop.Fun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

end GlobalTheory.BigTop.Fun

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticVarietyGenericFibre
set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.Published
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier

namespace GlobalTheory.FibreProj

variable {k : Type} [CommRing k] {B Y : Scheme.{0}} [IsIntegral B] {q : B ⟶ Sp k} {p : Y ⟶ Sp k} {d : ℕ}

theorem isProper_of_isArithVar {D : ℕ} (h : IsArithVar p D) : IsProper p := by
  obtain ⟨N, j, _, hj⟩ := h.isProjOver
  have := isProper_str k N
  exact hj ▸ inferInstance



end GlobalTheory.FibreProj
end
end
