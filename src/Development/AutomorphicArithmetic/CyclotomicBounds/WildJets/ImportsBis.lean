module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactPairRealAverageFockEqJetOperator
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnArrowKernelRealEqDetCharMulFockKernel

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.AttExp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.Chain.StepVac in
private theorem mu_exp' {D : D7} {T : Type} {L : LevCh D T} {μ₀ : T} (hL : L.Is μ₀) (t : T) (j : ℕ) (hj : j < D.R.m)
    (τ : D.what₂.Tau) : HasInfExp D (L.mu t (j + 1)) τ (-(D.hc τ).e ⟨j, hj⟩) := by
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  have h0 := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hL.mu0 ⟨j, hj⟩) (hasInfQ_tau (L.C.isMu0 ⟨j, hj⟩).inf) τ
  obtain ⟨θ, hθ⟩ : ∃ θ, IsInfFam (D := D) θ := by
    obtain ⟨_, _, hθ, _⟩ := h0
    exact hθ
  have := hasInfExp_mul h0 (hasInfExp_of_order hθ (hL.xi t) hn ho τ)
  rw [add_zero, Formalism.L2.Host.eExp, Equiv.symm_apply_apply] at this
  exact this

private theorem att_exp' {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {μ0 : T} (hL : L.Is μ0)
    {i : ℕ} (hi : i < D.R.m) (n : ℕ) (τ : D.what₂.Tau) :
    HasInfExp D (Formalism.IndefR.Lift.attChr (G.ch.chi (D.R.m - i)) L.eta n) τ
      ((cen D sc.cGap τ (D.R.m - i) : ℚ) - if Odd n then 1 / 2 else 0) := by
  have hm1 : 1 ≤ D.R.m - i := by omega
  have hm2 : D.R.m - i ≤ D.R.m := by omega
  have h0 : HasInfExp D (G.ch.chi (D.R.m - i)) τ (cen D sc.cGap τ (D.R.m - i) : ℚ) :=
    GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ (fun τ => (cen D sc.cGap τ (D.R.m - i) : ℚ)) (G.ch.chi_eq _ hm1 hm2)
      ⟨fun τ => 2 * cen D sc.cGap τ (D.R.m - i), fun τ => by push_cast; ring, G.ch.inf _ hm1 hm2⟩ τ
  unfold Formalism.IndefR.Lift.attChr
  split_ifs
  · rw [sub_eq_add_neg]
    exact GlobalTheory.Chain.StepVac.hasInfExp_mul h0 (GlobalTheory.Chain.StepVac.hasInfExp_inv (GlobalTheory.SquareExps.eta_exp hL τ))
  · simpa using h0

theorem UpperTheory.WildA.expEx :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ p : GlobalTheory.ChiGrid.Pair T, DefPair D.R.m p → ∃ (a b : D.what₂.Tau → ℚ) (e₁ e₂ : D.what₂.Tau → ℤ),
      (∀ τ, HasInfExp D (G.chrS p) τ (a τ)) ∧ (∀ τ, HasInfExp D (G.chrT p) τ (b τ)) ∧
      (∀ τ, (e₁ τ : ℚ) = a τ + GlobalTheory.FockReal.sgnP p * (G.pS p).rank / 2) ∧ ∀ τ, (e₂ τ : ℚ) = -(b τ + GlobalTheory.FockReal.sgnP p * (G.pT p).rank / 2) := by
  intro D T L sc G μ₀ hL p hp
  have half : ∀ (c : ℤ) (n : ℕ), ∃ e : ℤ, (e : ℚ) = ((c : ℚ) - if Odd n then 1 / 2 else 0) + (-1) * (n : ℚ) / 2 := by
    intro c n
    rcases Nat.even_or_odd n with h | h
    · obtain ⟨k, hk⟩ := id h
      refine ⟨c - k, ?_⟩
      simp only [Nat.not_odd_iff_even.2 h, ite_false]; rw [hk]; push_cast; ring
    · obtain ⟨k, hk⟩ := id h
      refine ⟨c - k - 1, ?_⟩
      simp only [h, ite_true]; rw [hk]; push_cast; ring
  cases p with
  | mu t i j => exact hp.elim
  | core i => exact hp.elim
  | top t j =>
    have hj : j < D.R.m := hp
    have hr0 : Even (G.V (.top j)).rank := by rw [GlobalTheory.FunObj.rank_top G (j := j) (by omega)]; exact even_rankX D j
    have hr1 : Even (G.V (.top (j + 1))).rank := by
      rw [GlobalTheory.FunObj.rank_top G (j := j + 1) (by omega)]; exact even_rankX D (j + 1)
    have hS : G.chrS (.top t j) = L.mu t (j + 1) := by
      simp only [GridData.chrS, Formalism.IndefR.Lift.attChr, GridData.chr, GridData.pS, Nat.not_odd_iff_even.2 hr0, ite_false]
    have hT : G.chrT (.top t j) = L.mu t (j + 1) := by
      simp only [GridData.chrT, Formalism.IndefR.Lift.attChr, GridData.chr, GridData.pT, Nat.not_odd_iff_even.2 hr1, ite_false]
    have hce : ∀ τ, (((num D sc.cGap τ).e (j + 1) : ℤ) : ℚ) = (D.hc τ).e ⟨j, hj⟩ := fun τ =>
      GlobalTheory.SignedHC.GridData.extend_cast 1 (D.hc τ).e_int ⟨j, hj⟩
    obtain ⟨k0, hk0⟩ := hr0
    obtain ⟨k1, hk1⟩ := hr1
    refine ⟨fun τ => -((D.hc τ).e ⟨j, hj⟩ : ℚ), fun τ => -((D.hc τ).e ⟨j, hj⟩ : ℚ),
      fun τ => -(num D sc.cGap τ).e (j + 1) + k0, fun τ => (num D sc.cGap τ).e (j + 1) - k1,
      fun τ => ?_, fun τ => ?_, fun τ => ?_, fun τ => ?_⟩
    · rw [hS]; exact mu_exp' hL t j hj τ
    · rw [hT]; exact mu_exp' hL t j hj τ
    · simp only [GlobalTheory.FockReal.sgnP, one_mul, hk0, ← hce]; push_cast; ring
    · simp only [GlobalTheory.FockReal.sgnP, one_mul, hk1, ← hce]; push_cast; ring
  | chi i j =>
    have hi : i < D.R.m := hp.1
    choose e he using half
    refine ⟨_, _, fun τ => e (cen D sc.cGap τ (D.R.m - i)) (G.pS (.chi i j : Pair T)).rank,
      fun τ => -e (cen D sc.cGap τ (D.R.m - i)) (G.pT (.chi i j : Pair T)).rank,
      fun τ => att_exp' G hL hi _ τ, fun τ => att_exp' G hL hi _ τ, fun τ => ?_, fun τ => ?_⟩
    · exact he _ _
    · rw [Int.cast_neg, he]; rfl
end

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.RatReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem UpperTheory.WildA.ratReal :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) (fr : ∀ X : Node, GL (Fin (G.V X).rank) D.host.E) (X : Node) (r : FinPt G X)
      (U : Matrix.unitaryGroup (Fin (G.V X).rank) D.host.E), GlobalTheory.RatMoveJets.RatCoord _ (fr X) r U →
      ∃ γ ∈ GQ (G.V X), ∃ k ∈ GinfC (G.V X), (∀ x : FinPt G X, ((r * x : FinPt G X) : GA D (G.V X)) = γ * ((x : GA D (G.V X)) * k)) ∧
        GlobalTheory.DefStep.realAct W.θ fr X k⁻¹ = rhoVr (tauE D) (wt G X) (Unitary.toUnits U) := by
  intro D T L sc G W fr X r U h
  obtain ⟨γ, hγ, hf, hm⟩ := h
  have hk : γ⁻¹ * (r : GA D (G.V X)) ∈ GinfC (G.V X) := by
    show finHom (G.V X) (γ⁻¹ * (r : GA D (G.V X))) = 1
    rw [map_mul, map_inv, hf, inv_mul_cancel]
  refine ⟨γ, hγ, γ⁻¹ * (r : GA D (G.V X)), hk, fun x => ?_, ?_⟩
  · have hc := GlobalTheory.AdelicSplit.commute_GinfC_GfC (G.V X) hk x.2
    rw [← hc, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
    rfl
  · have hrat : Bridge.IsRatMat (G.V X) ⟨γ, hγ⟩ (fr X * Unitary.toUnits U * (fr X)⁻¹) := Units.ext hm
    have hin : GlobalTheory.DefStep.realIn W.θ fr X γ = embGL (tauE D) (Unitary.toUnits U) := by
      funext τ
      have h1 := GlobalTheory.CoefModel.realGL_rat W.θ_is (G.V X) ⟨γ, hγ⟩ _ hrat τ
      have h2 : GlobalTheory.DefStep.realIn W.θ fr X γ τ = (GlobalTheory.DefStep.frGL fr X τ)⁻¹ *
          GlobalTheory.CoefModel.realGL W.θ (G.V X) γ τ * GlobalTheory.DefStep.frGL fr X τ := by
        simp [GlobalTheory.DefStep.realIn]
      rw [h2, h1, map_mul, map_mul, map_inv, GlobalTheory.DefStep.frGL]
      show _ = Formalism.UG.bc (tauE D τ) (Unitary.toUnits U)
      group
    rw [_root_.mul_inv_rev, inv_inv, map_mul,
      GlobalTheory.DefStep.realAct_fin W.θ fr X (inv_mem r.2), one_mul, GlobalTheory.DefStep.realAct, MonoidHom.comp_apply,
      MonoidHom.comp_apply, hin]
    rfl
end

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.MoveTop
section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.RealTop
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MvPolynomial Formalism.L2.Ker in
private theorem jetMap_smul' {ι : Type} [Fintype ι] {a b : ℕ} (c : ℂ) (J : (DVar ι a b →₀ ℕ) → ℂ) (n : ι → ℕ) (P : Pol ℂ ι a) :
    jetMap (fun m => c * J m) n P = c • jetMap J n P := by
  have h : jetLin (fun m => c * J m) = c • jetLin J := by
    refine (basisMonomials _ ℂ).ext fun m => ?_
    rw [coe_basisMonomials]
    simp only [LinearMap.smul_apply]
    rw [GlobalTheory.KerT.RatLaw.jetLin_monomial, GlobalTheory.KerT.RatLaw.jetLin_monomial, smul_monomial, smul_eq_mul]
  simp only [jetMap, LinearMap.comp_apply, h, LinearMap.smul_apply]

open MvPolynomial Formalism.L2.Ker in
private theorem jetMap_substF {ι : Type} [Fintype ι] {a b : ℕ} (c : ℂ) (ℓ : MvPolynomial (DVar ι a b) ℂ →ₗ[ℂ] ℂ)
    (g : ι → Matrix (Fin a) (Fin a) ℂ) (h : ι → Matrix (Fin b) (Fin b) ℂ) (n : ι → ℕ) (P : Pol ℂ ι a) :
    jetMap (fun m => c * ℓ (GlobalTheory.CompactHowe.substF h (fun τ => (g τ)ᵀ) (monomial m 1))) n P =
      (c * ∏ τ, (g τ).det ^ n τ) • GlobalTheory.KJInf.lft h (jetMap (fun m => ℓ (monomial m 1)) n (GlobalTheory.KJInf.lft g P)) := by
  have e1 : GlobalTheory.KerT.RatLaw.tabFn (fun m => ℓ (monomial m 1)) = ℓ := by
    refine (basisMonomials _ ℂ).ext fun m => ?_
    rw [coe_basisMonomials]
    exact GlobalTheory.KerT.RatLaw.tabFn_monomial _ m
  have e2 : GlobalTheory.CompactHowe.substF h (fun τ => (g τ)ᵀ) = aeval (GlobalTheory.KerT.RatLaw.subst g h) := by
    refine algHom_ext fun v => ?_
    simp only [GlobalTheory.CompactHowe.substF_X, aeval_X, Matrix.transpose_apply]
  rw [jetMap_smul', GlobalTheory.KerT.RatLaw.jetMap_subst (J := fun m => ℓ (monomial m 1)) g h (fun m => by rw [e1, e2]), mul_smul]
  rfl

open GlobalTheory.ColKer GlobalTheory.RowHoweAvg in
theorem UpperTheory.WildA.realTop :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil} {U₀ : Set T} (N : Std G U₀) {μ₀ : T}, L.Is μ₀ → ∀ (t : T) (j : ℕ), j + 1 ≤ D.R.m →
      ∀ (a b : D.what₂.Tau → ℚ), (∀ τ, HasInfExp D (G.chrS (GlobalTheory.ChiGrid.Pair.top t j)) τ (a τ)) → (∀ τ, HasInfExp D (G.chrT (GlobalTheory.ChiGrid.Pair.top t j)) τ (b τ)) →
      ∀ (e₁ e₂ : D.what₂.Tau → ℤ), (∀ τ, (e₁ τ : ℚ) = a τ + GlobalTheory.FockReal.sgnP (GlobalTheory.ChiGrid.Pair.top t j) * (G.pS (GlobalTheory.ChiGrid.Pair.top t j)).rank / 2) →
        (∀ τ, (e₂ τ : ℚ) = -(b τ + GlobalTheory.FockReal.sgnP (GlobalTheory.ChiGrid.Pair.top t j) * (G.pT (GlobalTheory.ChiGrid.Pair.top t j)).rank / 2)) →
      ∀ (ℓ : PolF D (G.pT (GlobalTheory.ChiGrid.Pair.top t j)).rank (G.pS (GlobalTheory.ChiGrid.Pair.top t j)).rank →ₗ[ℂ] ℂ) (k : GA D (G.V ((GlobalTheory.ChiGrid.Pair.top t j)).small)), k ∈ GinfC (G.V ((GlobalTheory.ChiGrid.Pair.top t j)).small) →
      ∀ k' : GA D (G.V ((GlobalTheory.ChiGrid.Pair.top t j)).big), k' ∈ GinfC (G.V ((GlobalTheory.ChiGrid.Pair.top t j)).big) →
        Formalism.L2.Ker.jetOp (wt G ((GlobalTheory.ChiGrid.Pair.top t j)).small) (wt G ((GlobalTheory.ChiGrid.Pair.top t j)).big) (fun m => GlobalTheory.FockReal.realChar W (GlobalTheory.ChiGrid.Pair.top t j) e₁ e₂ k k' *
                  ℓ (GlobalTheory.FockReal.realSubst W N.frC (GlobalTheory.ChiGrid.Pair.top t j) k k' (MvPolynomial.monomial (m.mapDomain (fvar G (GlobalTheory.ChiGrid.Pair.top t j))) 1))) (nuEnd G (GlobalTheory.ChiGrid.Pair.top t j)) =
          GlobalTheory.DefStep.realAct W.θ N.fr ((GlobalTheory.ChiGrid.Pair.top t j)).big k'⁻¹ ∘ₗ
            Formalism.L2.Ker.jetOp (wt G ((GlobalTheory.ChiGrid.Pair.top t j)).small) (wt G ((GlobalTheory.ChiGrid.Pair.top t j)).big) (fun m => ℓ (MvPolynomial.monomial (m.mapDomain (fvar G (GlobalTheory.ChiGrid.Pair.top t j))) 1)) (nuEnd G (GlobalTheory.ChiGrid.Pair.top t j)) ∘ₗ
            GlobalTheory.DefStep.realAct W.θ N.fr ((GlobalTheory.ChiGrid.Pair.top t j)).small k := by
  intro D T L sc G W U₀ N μ₀ hL t j hj a b ha hb e₁ e₂ he₁ he₂ ℓ k _ k' _
  have hp : DefPair D.R.m (Pair.top t j) := hj
  have hj' : j < D.R.m := hj
  have hJ := (wtOK_of_defPair G _ hp).2
  have hr0 : Even (G.V (.top j)).rank := by rw [rank_top G (j := j) (by omega)]; exact rankX_even D j
  have hr1 : Even (G.V (.top (j + 1))).rank := by rw [rank_top G (j := j + 1) (by omega)]; exact rankX_even D (j + 1)
  have hS : G.chrS (.top t j) = L.mu t (j + 1) := by
    simp only [GridData.chrS, Formalism.IndefR.Lift.attChr, GridData.chr, GridData.pS, Nat.not_odd_iff_even.2 hr0, if_false]
  have hT : G.chrT (.top t j) = L.mu t (j + 1) := by
    simp only [GridData.chrT, Formalism.IndefR.Lift.attChr, GridData.chr, GridData.pT, Nat.not_odd_iff_even.2 hr1, if_false]
  have h1 : ∀ τ, e₁ τ = (wt G (.top (j + 1)) τ).detShift := fun τ => by
    have ea := GlobalTheory.Mem.HeckeExp.hasInfExp_unique (hS ▸ ha τ) (mu_exp hL t j hj' τ)
    have := (detShift_top G t j hj' τ).1
    have h : (e₁ τ : ℚ) = ((wt G (.top (j + 1)) τ).detShift : ℤ) := by
      rw [he₁, this, ea]; simp only [GlobalTheory.FockReal.sgnP, one_mul]
    exact_mod_cast h
  have h2 : ∀ τ, e₂ τ = (nuEnd G (.top t j) τ : ℤ) - (wt G (.top j) τ).detShift := fun τ => by
    have eb := GlobalTheory.Mem.HeckeExp.hasInfExp_unique (hT ▸ hb τ) (mu_exp hL t j hj' τ)
    have := (detShift_top G t j hj' τ).2
    have h : (e₂ τ : ℚ) = (((nuEnd G (.top t j) τ : ℤ) - (wt G (.top j) τ).detShift : ℤ) : ℚ) := by
      rw [he₂, this, eb]; simp only [GlobalTheory.FockReal.sgnP, one_mul]
    exact_mod_cast h
  have hinv : GlobalTheory.SeeSaw.inB W.θ (G.V (.top j)) (N.frC (.top j)) k⁻¹ =
      fun τ => (GlobalTheory.SeeSaw.inB W.θ (G.V (.top j)) (N.frC (.top j)) k τ)⁻¹ := by
    funext τ
    rw [← realIn_coe, ← realIn_coe, map_inv, Pi.inv_apply, Matrix.coe_units_inv]
  have hne : ∀ τ, (compAt W.θ τ (Formalism.L2.Theta.mt (G.V (.top j)) k)).det ≠ 0 := fun τ => by
    rw [← det_inB W.θ N, ← realIn_coe]
    exact (Matrix.isUnits_det_units _).ne_zero
  have hdi : ∀ τ, (compAt W.θ τ (Formalism.L2.Theta.mt (G.V (.top j)) k⁻¹)).det =
      (compAt W.θ τ (Formalism.L2.Theta.mt (G.V (.top j)) k)).det⁻¹ := fun τ => by
    rw [← det_inB W.θ N, ← det_inB W.θ N, hinv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  have hm : ∀ m : Formalism.L2.Ker.DVar D.what₂.Tau (G.V (Pair.top t j).small).rank (G.V (Pair.top t j).big).rank →₀ ℕ,
      Finsupp.mapDomain (fvar G (Pair.top t j)) m = m := fun m => Finsupp.mapDomain_id
  have hs : GlobalTheory.FockReal.realSubst W N.frC (Pair.top t j) k k' =
      GlobalTheory.CompactHowe.substF (GlobalTheory.SeeSaw.inB W.θ (G.V (.top (j + 1))) (N.frC (.top (j + 1))) k')
        (fun τ => (GlobalTheory.SeeSaw.inB W.θ (G.V (.top j)) (N.frC (.top j)) k⁻¹ τ)ᵀ) := by
    rw [hinv]
    rfl
  refine LinearMap.ext fun v => Subtype.ext ?_
  have e0 := realAct_inv_coe W.θ N (.top j) k⁻¹ v
  rw [inv_inv] at e0
  simp only [hm, hs, LinearMap.comp_apply]
  rw [jetOp_coe hJ, realAct_inv_coe, jetOp_coe hJ]
  refine (jetMap_substF _ ℓ _ _ _ _).trans ?_
  erw [e0]
  rw [map_smul, map_smul, smul_smul]
  congr 1
  simp only [GlobalTheory.FockReal.realChar, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [det_inB, hdi, h1, h2]
  show (compAt W.θ τ (Formalism.L2.Theta.mt (G.V (.top j)) k)).det ^ _ * _ * _ = _
  rw [zpow_sub₀ (hne τ), zpow_natCast, inv_pow, _root_.inv_zpow]
  have := pow_ne_zero (nuEnd G (.top t j) τ) (hne τ)
  field_simp
  try rfl
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem UpperTheory.WildA.moveTop :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil} {U₀ : Set T} {N : Std G U₀} (Z : Normal W N) {μ₀ : T}, L.Is μ₀ → ∀ (t t' : T) (j : ℕ), j + 1 ≤ D.R.m →
      ∀ (d : FinDatum G t (GlobalTheory.ChiGrid.Pair.top t' j)) (x r : FinPt G ((GlobalTheory.ChiGrid.Pair.top t' j)).small) (y r' : FinPt G ((GlobalTheory.ChiGrid.Pair.top t' j)).big)
        (U : Matrix.unitaryGroup (Fin (G.V ((GlobalTheory.ChiGrid.Pair.top t' j)).small).rank) D.host.E) (U' : Matrix.unitaryGroup (Fin (G.V ((GlobalTheory.ChiGrid.Pair.top t' j)).big).rank) D.host.E),
        GlobalTheory.RatMoveJets.RatCoord _ (N.fr ((GlobalTheory.ChiGrid.Pair.top t' j)).small) r U → GlobalTheory.RatMoveJets.RatCoord _ (N.fr ((GlobalTheory.ChiGrid.Pair.top t' j)).big) r' U' →
        Z.kkMap 1 d (r * x) (r' * y) ∘ₗ rhoVr (tauE D) (wt G ((GlobalTheory.ChiGrid.Pair.top t' j)).small) (Unitary.toUnits U) =
          rhoVr (tauE D) (wt G ((GlobalTheory.ChiGrid.Pair.top t' j)).big) (Unitary.toUnits U') ∘ₗ Z.kkMap 1 d x y := by
  intro D T L sc G W U₀ N Z μ₀ hL t t' j hj d x r y r' U U' hU hU'
  have hp : DefPair D.R.m (GlobalTheory.ChiGrid.Pair.top t' j : GlobalTheory.ChiGrid.Pair T) := hj
  have hω := W.om_is (GlobalTheory.ChiGrid.Pair.top t' j) hj
  obtain ⟨a, b, e₁, e₂, ha, hb, he₁, he₂⟩ := UpperTheory.WildA.expEx (G := G) hL _ hp
  obtain ⟨γ, hγ, k, hk, hrk, hρ⟩ := UpperTheory.WildA.ratReal W N.fr _ r U hU
  obtain ⟨γ', hγ', k', hk', hrk', hρ'⟩ := UpperTheory.WildA.ratReal W N.fr _ r' U' hU'
  obtain ⟨h1, h2⟩ := GlobalTheory.T.gridFiniteDatumVector_theta_fockVacuum W Z hp d (Z.hasVec_of_defPair hL hp d)
  have hB : ∀ X, DefNode D.R.m X → ∀ τ, (N.frC X τ)ᴴ * gramAt D (G.V X) τ * N.frC X τ = 1 := fun X hX τ =>
    GlobalTheory.FockJetOrigin.frame_map τ (N.fr_on X hX)
  have hF : ∀ Q, IsThetaFunO W.ψ _ _ (fockIn W N.frC (GlobalTheory.ChiGrid.Pair.top t' j) (Z.vec d) Q) := fun Q =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ h1 Q
  have haut : ∀ Q g h, W.ker (GlobalTheory.ChiGrid.Pair.top t' j) (fockIn W N.frC (GlobalTheory.ChiGrid.Pair.top t' j) (Z.vec d) Q) (γ * g) (γ' * h) =
      W.ker (GlobalTheory.ChiGrid.Pair.top t' j) (fockIn W N.frC (GlobalTheory.ChiGrid.Pair.top t' j) (Z.vec d) Q) g h := by
    intro Q g h
    show thetaKO (W.om (.top t' j)) (γ * g) (γ' * h) _ = thetaKO (W.om (.top t' j)) g h _
    have e : ((γ * g, γ' * h) : GA D (G.V (.top j)) × GA D (G.V (.top (j + 1)))) = (γ, γ') * (g, h) := rfl
    unfold thetaKO
    rw [e, map_mul]
    exact hω.om_aut γ hγ γ' hγ' _ (hω.om_pres _ _ (hF Q))
  let ℓ : PolF D (G.pT (GlobalTheory.ChiGrid.Pair.top t' j)).rank (G.pS (GlobalTheory.ChiGrid.Pair.top t' j)).rank →ₗ[ℂ] ℂ :=
    { toFun := fun Q => kerFin W (GlobalTheory.ChiGrid.Pair.top t' j) (fockIn W N.frC (GlobalTheory.ChiGrid.Pair.top t' j) (Z.vec d) Q)
        (x * N.u _) (y * N.u _)
      map_add' := fun P Q => by
        simp only [kerFin, GridData.Weil.ker, thetaKO, map_add (f := _), Pi.add_apply]
      map_smul' := fun c Q => by
        simp only [kerFin, GridData.Weil.ker, thetaKO, map_smul, Pi.smul_apply, RingHom.id_apply] }
  have key := UpperTheory.WildA.realTop (W := W) N hL t' j hj a b ha hb e₁ e₂ he₁ he₂ ℓ k hk k' hk'
  have tab : jetTab W N.frC (GlobalTheory.ChiGrid.Pair.top t' j) (Z.vec d) (r * x * N.u _) (r' * y * N.u _) =
      fun m => GlobalTheory.FockReal.realChar W (GlobalTheory.ChiGrid.Pair.top t' j) e₁ e₂ k k' *
        ℓ (GlobalTheory.FockReal.realSubst W N.frC (GlobalTheory.ChiGrid.Pair.top t' j) k k'
          (MvPolynomial.monomial (m.mapDomain (fvar G (GlobalTheory.ChiGrid.Pair.top t' j))) 1)) := by
    funext m
    rw [jetTab, kerFin, mul_assoc r, mul_assoc r', hrk, hrk', haut]
    exact GlobalTheory.FockReal.ker_fockIn_real hL W N.frC hp hB a b ha hb e₁ e₂ he₁ he₂ _ h1 h2 k hk k' hk' _ _ _
  have hid : GlobalTheory.DefStep.realAct W.θ N.fr (GlobalTheory.ChiGrid.Pair.top t' j : GlobalTheory.ChiGrid.Pair T).small k ∘ₗ
      GlobalTheory.DefStep.realAct W.θ N.fr (GlobalTheory.ChiGrid.Pair.top t' j : GlobalTheory.ChiGrid.Pair T).small k⁻¹ = LinearMap.id := by
    rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [← hρ, ← hρ', Normal.kkMap, Normal.kkMap, fockComp, fockComp, tab, key, LinearMap.smul_comp, LinearMap.comp_smul,
    LinearMap.comp_assoc, LinearMap.comp_assoc, hid, LinearMap.comp_id]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.MoveRow
section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.RealRow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.KJInf Formalism.L2.Ker MvPolynomial in
private theorem jet_smul_subst {ι : Type} [Fintype ι] {a b : ℕ} (c : ℂ) (ℓ : FP ι a b →ₗ[ℂ] ℂ)
    (g : ι → Matrix (Fin a) (Fin a) ℂ) (h : ι → Matrix (Fin b) (Fin b) ℂ) (n : ι → ℕ) (P : PY ι a) :
    jetMap (fun m => c * ℓ (mvZ g h (monomial m 1))) n P =
      (c * ∏ τ, (g τ).det ^ n τ) • lft h (jetMap (fun m => ℓ (monomial m 1)) n (lft g P)) := by
  have h1 : ∀ (J : (DVar ι a b →₀ ℕ) → ℂ) Q, jetLin (fun m => c * J m) Q = c • jetLin J Q := fun J Q => by
    refine LinearMap.congr_fun (f := jetLin (fun m => c * J m)) (g := c • jetLin J) ((basisMonomials _ ℂ).ext fun m => ?_) Q
    rw [coe_basisMonomials]
    simp only [LinearMap.smul_apply, GlobalTheory.KerT.RatLaw.jetLin_monomial, smul_monomial, smul_eq_mul]
  have h2 : ∀ (J : (DVar ι a b →₀ ℕ) → ℂ), jetMap (fun m => c * J m) n P = c • jetMap J n P := fun J => by
    simp only [jetMap, LinearMap.comp_apply, h1]
  have h3 : GlobalTheory.KerT.RatLaw.tabFn (fun m => ℓ (monomial m 1)) = ℓ := by
    refine (basisMonomials _ ℂ).ext fun m => ?_
    rw [coe_basisMonomials]
    exact GlobalTheory.KerT.RatLaw.tabFn_monomial _ m
  rw [h2, GlobalTheory.KerT.RatLaw.jetMap_subst (J := fun m => ℓ (monomial m 1)) g h (fun m => by rw [h3]; rfl), smul_smul]
  rfl

open GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.RowHoweAvg GlobalTheory.FockReal GlobalTheory.DefStep MvPolynomial in
theorem UpperTheory.WildA.realRow :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil} {U₀ : Set T} (N : Std G U₀) {μ₀ : T}, L.Is μ₀ → ∀ (i : ℕ), i + 1 ≤ D.R.m →
      ∀ (a b : D.what₂.Tau → ℚ), (∀ τ, HasInfExp D (G.chrS (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)) τ (a τ)) → (∀ τ, HasInfExp D (G.chrT (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)) τ (b τ)) →
      ∀ (e₁ e₂ : D.what₂.Tau → ℤ), (∀ τ, (e₁ τ : ℚ) = a τ + GlobalTheory.FockReal.sgnP (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T) * (G.pS (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).rank / 2) →
        (∀ τ, (e₂ τ : ℚ) = -(b τ + GlobalTheory.FockReal.sgnP (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T) * (G.pT (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).rank / 2)) →
      ∀ (ℓ : PolF D (G.pT (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).rank (G.pS (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).rank →ₗ[ℂ] ℂ) (k : GA D (G.V ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).small)), k ∈ GinfC (G.V ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).small) →
      ∀ k' : GA D (G.V ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).big), k' ∈ GinfC (G.V ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).big) →
        Formalism.L2.Ker.jetOp (wt G ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).small) (wt G ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).big) (fun m => GlobalTheory.FockReal.realChar W (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T) e₁ e₂ k k' *
                  ℓ (GlobalTheory.FockReal.realSubst W N.frC (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T) k k' (MvPolynomial.monomial (m.mapDomain (fvar G (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T))) 1))) (nuEnd G (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)) =
          GlobalTheory.DefStep.realAct W.θ N.fr ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).big k'⁻¹ ∘ₗ
            Formalism.L2.Ker.jetOp (wt G ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).small) (wt G ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).big) (fun m => ℓ (MvPolynomial.monomial (m.mapDomain (fvar G (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T))) 1)) (nuEnd G (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)) ∘ₗ
            GlobalTheory.DefStep.realAct W.θ N.fr ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).small k := by
  intro D T L sc G W U N μ0 hL i hi a b ha hb e₁ e₂ he₁ he₂ ℓ k hk k' hk'
  have hi' : i < D.R.m := hi
  have hp : DefPair D.R.m (.chi i D.R.m : Pair T) := ⟨hi', rfl⟩
  have hn := DefPair.nodes hp
  have hX := GlobalTheory.SeeSaw.ontoUni_inB D W.θ (G.V (.grid i D.R.m)) (N.frC _) W.θ_is (GlobalTheory.RealType.frC_on N hn.1)
  have hY := GlobalTheory.SeeSaw.ontoUni_inB D W.θ (G.V (.grid (i + 1) D.R.m)) (N.frC _) W.θ_is (GlobalTheory.RealType.frC_on N hn.2)
  have hJ := (wtOK_of_defPair G _ hp).2
  have hm := fun τ => exps_match G hL hi' τ (ha τ) (hb τ) (he₁ τ) (he₂ τ)
  let f : D.what₂.Tau × Fin (G.V (.grid (i + 1) D.R.m)).rank × Fin (G.V (.grid i D.R.m)).rank →
      D.what₂.Tau × Fin (G.V (.grid i D.R.m)).rank × Fin (G.V (.grid (i + 1) D.R.m)).rank := fun k => (k.1, k.2.2, k.2.1)
  let ℓ' : FP D.what₂.Tau (G.V (.grid i D.R.m)).rank (G.V (.grid (i + 1) D.R.m)).rank →ₗ[ℂ] ℂ := ℓ ∘ₗ (rename f).toLinearMap
  have hJ' : (fun m => ℓ (MvPolynomial.monomial (m.mapDomain (fvar G (.chi i D.R.m : Pair T))) 1)) =
      fun m => ℓ' (monomial m 1) := by
    funext m
    simp only [ℓ', LinearMap.comp_apply, AlgHom.toLinearMap_apply, rename_monomial]
    rfl
  have hinv : ∀ τ, (inB W.θ _ (N.frC (.grid i D.R.m)) k τ)⁻¹ = inB W.θ _ (N.frC (.grid i D.R.m)) k⁻¹ τ := fun τ =>
    GlobalTheory.KJAvg.ontoUni_inv hX ⟨k, hk⟩ τ
  have e : ∀ P, realSubst W N.frC (.chi i D.R.m) k k' (rename f P) =
      rename f (mvZ (inB W.θ _ (N.frC (.grid i D.R.m)) k⁻¹) (inB W.θ _ (N.frC (.grid (i + 1) D.R.m)) k') P) := fun P => by
    rw [← funext hinv, ← substF_rename]
    have e1 := fun τ => (map_conj_of_unitary (hX.uni ⟨k, hk⟩ τ)).1
    have e2 := fun τ => (map_conj_of_unitary (hY.uni ⟨k', hk'⟩ τ)).2
    exact congrArg₂ (fun x y => GlobalTheory.CompactHowe.substF x y (rename f P)) (funext e1) (funext e2)
  have hJ2 : (fun m => realChar W (.chi i D.R.m) e₁ e₂ k k' *
      ℓ (realSubst W N.frC (.chi i D.R.m) k k' (MvPolynomial.monomial (m.mapDomain (fvar G (.chi i D.R.m : Pair T))) 1))) =
      fun m => realChar W (.chi i D.R.m) e₁ e₂ k k' * ℓ' (mvZ (inB W.θ _ (N.frC (.grid i D.R.m)) k⁻¹)
        (inB W.θ _ (N.frC (.grid (i + 1) D.R.m)) k') (monomial m 1)) := by
    funext m
    have := e (monomial m 1)
    rw [rename_monomial] at this
    exact congrArg (fun x => realChar W (.chi i D.R.m) e₁ e₂ k k' * ℓ x) this
  have hne : ∀ τ, (inB W.θ _ (N.frC (.grid i D.R.m)) k τ).det ≠ 0 := fun τ =>
    (Matrix.UnitaryGroup.det_isUnit ⟨_, hX.uni ⟨k, hk⟩ τ⟩).ne_zero
  have hsc : realChar W (.chi i D.R.m) e₁ e₂ k k' *
      ∏ τ, (inB W.θ _ (N.frC (.grid i D.R.m)) k⁻¹ τ).det ^ nuEnd G (.chi i D.R.m : Pair T) τ =
      (∏ τ, (compAt W.θ τ (Formalism.L2.Theta.mt (G.V (.grid (i + 1) D.R.m)) k')).det ^ (wt G (.grid (i + 1) D.R.m) τ).detShift) *
      ∏ τ, (compAt W.θ τ (Formalism.L2.Theta.mt (G.V (.grid i D.R.m)) k⁻¹)).det ^ (wt G (.grid i D.R.m) τ).detShift := by
    simp only [realChar, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have h1 := hne τ
    rw [← det_inB W.θ N (.grid i D.R.m) k⁻¹, ← hinv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', ← zpow_natCast,
      ← (hm τ).2, ← (hm τ).1, zpow_add₀ (inv_ne_zero h1), _root_.inv_zpow _ (e₁ τ), mul_assoc, det_inB]
    rw [det_inB] at h1
    exact congrArg₂ (· * ·) rfl (mul_inv_cancel_left₀ (zpow_ne_zero _ h1) _)
  have key : ∀ v : VV ℂ (wt G (.grid i D.R.m)),
      Formalism.L2.Ker.jetOp (wt G (.grid i D.R.m)) (wt G (.grid (i + 1) D.R.m))
        (fun m => realChar W (.chi i D.R.m) e₁ e₂ k k' * ℓ' (mvZ (inB W.θ _ (N.frC (.grid i D.R.m)) k⁻¹)
        (inB W.θ _ (N.frC (.grid (i + 1) D.R.m)) k') (monomial m 1))) (nuEnd G (.chi i D.R.m : Pair T)) v =
      realAct W.θ N.fr (.grid (i + 1) D.R.m) k'⁻¹ (Formalism.L2.Ker.jetOp (wt G (.grid i D.R.m)) (wt G (.grid (i + 1) D.R.m))
        (fun m => ℓ' (monomial m 1)) (nuEnd G (.chi i D.R.m : Pair T)) (realAct W.θ N.fr (.grid i D.R.m) k v)) := fun v => by
    have hk1 := realAct_inv_coe W.θ N (.grid i D.R.m) k⁻¹ v
    rw [inv_inv] at hk1
    refine Subtype.ext ?_
    rw [realAct_inv_coe, jetOp_coe hJ, jetOp_coe hJ, hk1, jet_smul_subst, map_smul, map_smul, smul_smul, hsc]
  rw [hJ', hJ2]
  exact LinearMap.ext key
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem frC_on' {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {U₀ : Set T}
    (N : Std G U₀) (X : Node) (hX : DefNode D.R.m X) (τ : D.what₂.Tau) :
    (N.frC X τ)ᴴ * gramAt D (G.V X) τ * N.frC X τ = 1 := by
  show (N.frC X τ)ᴴ * (G.V X).gram.map (tauE D τ) * N.frC X τ = 1
  have h := congrArg (·.map (tauE D τ)) (N.fr_on X hX)
  simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h
  rw [← h, Std.frC]
  congr 2
  ext a b
  exact (D.sp.cm.cmUnram.2.1 (tauE D τ) _).symm

private noncomputable def kerLin {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc}
    (W : G.Weil) (B : VertexFrames G) (p : GlobalTheory.ChiGrid.Pair T) (f : WO (G.pS p) (G.pT p) → ℂ)
    (g : GA D (G.V p.small)) (h : GA D (G.V p.big)) : PolF D (G.pT p).rank (G.pS p).rank →ₗ[ℂ] ℂ :=
  LinearMap.proj (0 : WO (G.pS p) (G.pT p)) ∘ₗ W.om p (G.toPair p g h) ∘ₗ fockIn W B p f

private theorem kerLin_apply {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc}
    (W : G.Weil) (B : VertexFrames G) (p : GlobalTheory.ChiGrid.Pair T) (f : WO (G.pS p) (G.pT p) → ℂ)
    (g : GA D (G.V p.small)) (h : GA D (G.V p.big)) (Q : PolF D (G.pT p).rank (G.pS p).rank) :
    kerLin W B p f g h Q = W.ker p (fockIn W B p f Q) g h := rfl

private theorem negGA_GQ {D : D7} (V : HSp D) {γ : GA D V} (hγ : γ ∈ GQ V) : negGA V γ ∈ GQ (negSp V) := by
  obtain ⟨x, hx, e⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hγ)
  refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨x, ?_, e⟩)
  have hx' : Formalism.UG.cT _ (x : Matrix _ _ _) * V.gram * (x : Matrix _ _ _) = V.gram := hx
  show Formalism.UG.cT _ (x : Matrix _ _ _) * (-V.gram) * (x : Matrix _ _ _) = -V.gram
  rw [Matrix.mul_neg, Matrix.neg_mul, hx']

private theorem ker_rat {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc}
    (W : G.Weil) (p : GlobalTheory.ChiGrid.Pair T) (hp : p.InRange D.R.m) (f : WO (G.pS p) (G.pT p) → ℂ)
    (hf : IsThetaFunO W.ψ (G.pS p) (G.pT p) f) (γ : GA D (G.V p.small)) (hγ : γ ∈ GQ (G.V p.small))
    (γ' : GA D (G.V p.big)) (hγ' : γ' ∈ GQ (G.V p.big)) (g : GA D (G.V p.small)) (h : GA D (G.V p.big)) :
    W.ker p f (γ * g) (γ' * h) = W.ker p f g h := by
  have hw := W.om_is p hp
  have h12 : (G.toPair p γ γ').1 ∈ GQ (G.pS p) ∧ (G.toPair p γ γ').2 ∈ GQ (G.pT p) := by
    cases p with
    | chi i j => exact ⟨negGA_GQ _ hγ', hγ⟩
    | mu t i j => exact ⟨hγ, hγ'⟩
    | core i => exact ⟨negGA_GQ _ hγ', hγ⟩
    | top t j => exact ⟨hγ, hγ'⟩
  rw [GlobalTheory.FockReal.ker_mul]
  exact hw.om_aut _ h12.1 _ h12.2 _ (hw.om_pres (G.toPair p g h) f hf)

theorem UpperTheory.WildA.moveRow :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil} {U₀ : Set T} {N : Std G U₀} (Z : Normal W N) {μ₀ : T}, L.Is μ₀ → ∀ (t : T) (i : ℕ), i + 1 ≤ D.R.m →
      ∀ (d : FinDatum G t (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)) (x r : FinPt G ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).small) (y r' : FinPt G ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).big)
        (U : Matrix.unitaryGroup (Fin (G.V ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).small).rank) D.host.E) (U' : Matrix.unitaryGroup (Fin (G.V ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).big).rank) D.host.E),
        GlobalTheory.RatMoveJets.RatCoord _ (N.fr ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).small) r U → GlobalTheory.RatMoveJets.RatCoord _ (N.fr ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).big) r' U' →
        Z.kkMap 1 d (r * x) (r' * y) ∘ₗ rhoVr (tauE D) (wt G ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).small) (Unitary.toUnits U) =
          rhoVr (tauE D) (wt G ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).big) (Unitary.toUnits U') ∘ₗ Z.kkMap 1 d x y := by
  intro D T L sc G W U₀ N Z μ₀ hL t i hi d x r y r' U U' hU hU'
  have hp : DefPair D.R.m (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T) := ⟨by omega, rfl⟩
  have hR : (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T).InRange D.R.m := ⟨by omega, le_rfl⟩
  obtain ⟨a, b, e₁, e₂, ha, hb, he₁, he₂⟩ := UpperTheory.WildA.expEx (G := G) hL _ hp
  obtain ⟨γ, hγ, k, hk, hm, hρ⟩ := UpperTheory.WildA.ratReal W N.fr _ r U hU
  obtain ⟨γ', hγ', k', hk', hm', hρ'⟩ := UpperTheory.WildA.ratReal W N.fr _ r' U' hU'
  obtain ⟨hth, hvac⟩ := GlobalTheory.T.gridFiniteDatumVector_theta_fockVacuum W Z hp d (Z.hasVec_of_defPair hL hp d)
  have hrow := UpperTheory.WildA.realRow (W := W) N hL i hi a b ha hb e₁ e₂ he₁ he₂
    (kerLin W N.frC _ (Z.vec d) ((x * N.u _ : FinPt G _) : GA D _) ((y * N.u _ : FinPt G _) : GA D _)) k hk k' hk'
  have htab : jetTab W N.frC _ (Z.vec d) (r * x * N.u _) (r' * y * N.u _) = fun m =>
      GlobalTheory.FockReal.realChar W (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T) e₁ e₂ k k' *
        kerLin W N.frC _ (Z.vec d) ((x * N.u _ : FinPt G _) : GA D _) ((y * N.u _ : FinPt G _) : GA D _)
          (GlobalTheory.FockReal.realSubst W N.frC (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T) k k'
            (MvPolynomial.monomial (m.mapDomain (fvar G (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T))) 1)) := by
    funext m
    rw [jetTab, kerFin, mul_assoc r, mul_assoc r', hm, hm', kerLin_apply,
      ker_rat W _ hR (fockIn W N.frC _ (Z.vec d) _)
        (GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ hth _) γ hγ γ' hγ']
    exact GlobalTheory.FockReal.ker_fockIn_real hL W N.frC hp (frC_on' N) a b ha hb e₁ e₂ he₁ he₂ _ hth hvac k hk k' hk' _ _ _
  have h1 : GlobalTheory.DefStep.realAct W.θ N.fr _ k ∘ₗ GlobalTheory.DefStep.realAct W.θ N.fr _ k⁻¹ = LinearMap.id := by
    rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl
  rw [Normal.kkMap, Normal.kkMap, fockComp, fockComp, htab, hrow, ← hρ, ← hρ', LinearMap.smul_comp, LinearMap.comp_smul,
    LinearMap.comp_assoc, LinearMap.comp_assoc, h1, LinearMap.comp_id]
  rfl
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem UpperTheory.WildA.move :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil} {U₀ : Set T} {N : Std G U₀} (Z : Normal W N) {μ₀ : T}, L.Is μ₀ → ∀ (t : T) (p : GlobalTheory.ChiGrid.Pair T), DefPair D.R.m p →
      ∀ (d : FinDatum G t p) (x r : FinPt G (p).small) (y r' : FinPt G (p).big)
        (U : Matrix.unitaryGroup (Fin (G.V (p).small).rank) D.host.E) (U' : Matrix.unitaryGroup (Fin (G.V (p).big).rank) D.host.E),
        GlobalTheory.RatMoveJets.RatCoord _ (N.fr (p).small) r U → GlobalTheory.RatMoveJets.RatCoord _ (N.fr (p).big) r' U' →
        Z.kkMap 1 d (r * x) (r' * y) ∘ₗ rhoVr (tauE D) (wt G (p).small) (Unitary.toUnits U) =
          rhoVr (tauE D) (wt G (p).big) (Unitary.toUnits U') ∘ₗ Z.kkMap 1 d x y := by
  intro D T L sc G W U₀ N Z μ₀ hL t p hp
  cases p with
  | chi i j =>
    obtain ⟨hi, hj⟩ := hp
    subst hj
    exact UpperTheory.WildA.moveRow Z hL t i (by omega)
  | mu t' i j => exact hp.elim
  | core i => exact hp.elim
  | top t' j => exact UpperTheory.WildA.moveTop Z hL t t' j hp
