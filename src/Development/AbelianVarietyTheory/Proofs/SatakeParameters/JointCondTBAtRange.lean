module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneCharpolyTwistSpecial
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecUniqueOfLaws
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsWeilGroupRestrictExtension
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiLocalGlobalDual
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAdjoinSplitHeckeGeneratorsDualsSpherical
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormEqOfSplitFactor

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointCondTBAtRange
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JumpWindowBlockExponentConditionOfJumpWindow
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JumpWindowBlockExponentConditionOfJumpWindow
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.BlockWindow

theorem jointTB_of_jumpWindow : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (h₁ : ℕ), D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → D.R.t ≤ h₁ → GlobalTheory.BlockWindow.JumpWindow D i r π h₁ → GlobalTheory.BlockWindow.JointTB D HW F i r π h₁ h₁ (GlobalTheory.HubLoc.cBnum (D.nd.l i) h₁ D.R.t (4 * D.R.n * D.R.nV)) := by
  intro D HW F i r π h₁ hsm hq hd ht hJ
  have h2 : D.nd.l i ≠ 2 := fun e => hsm (e ▸ D.host.toHostRaw.two_mem_small)
  refine ⟨h2, fun w hw => ?_⟩
  obtain ⟨hK0, hK1, -⟩ := GlobalTheory.HubLoc.localField_unramified D i hsm hq hd w hw
  have hKur : (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i) := by
    rw [← hK0]; exact inf_le_right
  refine ⟨GlobalTheory.BridgeInertia.inertEq D i w hw, hK1, fun CL h hs Y hc hY => ?_⟩
  have hs1 : (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 CL hs).W.s = 1 :=
    (HW (D.nd.l i)).W_s _ 1 _ hs
  have hell : LocalSituation.ell (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 CL hs) = D.nd.l i :=
    (D.loc (D.nd.l i)).PD_p _
  haveI : CharZero (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 CL hs).Qp :=
    inferInstanceAs (CharZero ℚ_[D.nd.l i])
  haveI : FiniteDimensional (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 CL hs).Qp
      (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 CL hs).K := (D.nbr i w hw).Kw.2
  have hcard : Nat.card (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥CL.1) =
      Module.finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1 :=
    GlobalTheory.HubLoc.card_emb _ _ fun τ x => h ((D.nbr i w hw).LL_split τ x)
  have hdeg := GlobalTheory.bridge_finrank_le D i w hw
  obtain ⟨hv1, hv2⟩ := GlobalTheory.HubLoc.padicValNat_finrank_Ks (D.nd.l i) (D.nbr i w hw).Kw
  have hgK : LocalSituation.gK (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 CL hs) = 0 := by
    unfold LocalSituation.gK
    rw [hs1, hell]
    exact hv2 hKur
  have hvd : ∀ m : ℕ, 0 < m → LocalSituation.vdegMs (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 CL hs) m = m - 1 := by
    intro m hm
    unfold LocalSituation.vdegMs
    rw [hs1, hell]
    exact hv1 m hm
  have key := GlobalTheory.T.jumpWindow_and_blockExponent_of_embeddings (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 CL hs) Y h₁ D.R.nV (4 * D.R.n) D.R.t
    hs1 hcard hdeg hgK (hvd _ (by unfold LocalSituation.mN; omega)) ht (fun τ => by
      obtain ⟨U, hU1, hU2, hU3⟩ := hJ w hw CL h τ
      exact ⟨U, hU1, hU2, fun a ha => hU3 a (hY τ a ha)⟩)
  refine ⟨key.1, fun e he => (key.2 e he).trans (le_of_eq ?_)⟩
  rw [hell]

end GlobalTheory.BlockWindow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JumpWindowBlockExponentConditionOfJumpWindowStatement
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jumpWindowBlockExponentCondition_of_jumpWindow : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (h₁ : ℕ), D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → D.R.t ≤ h₁ → GlobalTheory.BlockWindow.JumpWindow D i r π h₁ → GlobalTheory.BlockWindow.JointTB D HW F i r π h₁ h₁ (GlobalTheory.HubLoc.cBnum (D.nd.l i) h₁ D.R.t (4 * D.R.n * D.R.nV)) := by
  first | exact @GlobalTheory.BlockWindow.jointTB_of_jumpWindow | exact GlobalTheory.BlockWindow.jointTB_of_jumpWindow | (intros; apply GlobalTheory.BlockWindow.jointTB_of_jumpWindow <;> assumption)
end
end

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.BlockWindow

theorem jointTB_iff_jointCond (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (M0 h0 cB : ℕ) :
    JointTB D HW F i r π M0 h0 cB ↔ JointConditionTameBound D HW F i r π M0 h0 cB := by
  constructor
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun w hw => ?_⟩
    obtain ⟨a, b, c⟩ := h w hw
    exact ⟨a, b, fun C hs Y hc hY => c C.LL C.le hs Y hc hY⟩
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun w hw => ?_⟩
    obtain ⟨a, b, c⟩ := h w hw
    exact ⟨a, b, fun CL hL hs Y hc hY => c ⟨CL, hL⟩ hs Y hc hY⟩

theorem jointCond_TB_at_range (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (large₂ : SizeData₂ D)
    (hJ : AdmissibleParameterJ.JumpConditions large₂) (hA : EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (cB : ℕ)
    (h2 : D.nd.l i ∉ D.host.small) (hq : D.nd.l i ≠ D.host.q) (hd : D.nd.l i ≠ D.host.d) (hG : GoodR D.nd i r)
    (hc : GlobalTheory.HubLoc.cBnum (D.nd.l i) ⌊2 * large₂.sc.b⌋₊ D.R.t (4 * D.R.n * D.R.nV) ≤ cB) :
    ∃ M0 h0 : ℕ, JointConditionTameBound D HW F i r π M0 h0 cB := by
  obtain ⟨ht, hW⟩ := GlobalTheory.T.hodgeTateJumpWindow_of_jumpSets D large₂ hJ hA
  have hT := GlobalTheory.T.jumpWindowBlockExponentCondition_of_jumpWindow D HW F i r π ⌊2 * large₂.sc.b⌋₊ h2 hq hd ht (hW i r hG π)
  exact ⟨_, _, (jointTB_iff_jointCond D HW F i r π _ _ _).1 (hT.mono hc)⟩

end GlobalTheory.BlockWindow

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FockVectorsChainIsVacuumOffThetaLevels
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FockVectorsChainIsVacuumOffThetaLevels
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacGood

variable {D : D7}

theorem infPart_latO {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} {u : WO S T}
    (hu : u ∈ latO S T LS LT fun _ => True) : u.map (infPart D) = 0 := by
  ext i j
  rw [Matrix.map_apply, Matrix.zero_apply]
  unfold latO at hu
  refine AddSubgroup.closure_induction (p := fun u _ => infPart D (u i j) = 0) ?_ ?_ ?_ ?_ hu
  · rintro w ⟨α, -, -, a, -, s, -, t, -, rfl⟩
    rw [Matrix.of_apply]
    exact (show infPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)) =
      (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) from rfl).trans (TensorProduct.zero_tmul _ _)
  · simp
  · intro x y _ _ hx hy; rw [Matrix.add_apply, RingHom.map_add (f := _), hx, hy, add_zero]
  · intro x _ hx; rw [Matrix.neg_apply, RingHom.map_neg, hx, neg_zero]

theorem prime_idem_absorb (S : HSp D) {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : AE D} (h : IsPrimeIdem P e f) :
    f * e = e := by
  have hff := ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents S).2.2.1 P e f h).1
  rcases h with ⟨he, hf⟩ | ⟨hf, -, -⟩
  · rw [hf, add_mul, he.1.1, mul_comm (cA D e) e, he.1.2.1, add_zero]
  · subst hf; exact hff

theorem prime_idem_absorb_conj (S : HSp D) {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : AE D} (h : IsPrimeIdem P e f) :
    f * cA D e = cA D e := by
  have hcf := ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents S).2.2.1 P e f h).2.1
  have := congrArg (cA D) (prime_idem_absorb S h)
  rwa [map_mul, hcf] at this

theorem half_absorb (S : HSp D) {T : HSp D} {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : AE D} (h : IsPrimeIdem P e f)
    {u : WO S T} (hu : IsHalf e u ∨ IsHalf (cA D e) u) (i : Fin T.rank) (j : Fin S.rank) : f * u i j = u i j := by
  rcases hu with hu | hu
  · rw [← hu i j, ← mul_assoc, prime_idem_absorb S h]
  · rw [← hu i j, ← mul_assoc, prime_idem_absorb_conj S h]

theorem idemSum_mul_zero (S : HSp D) {E0 : AE D} {Q : Finset (Pl D.host.E)} (hE : IsIdemSum E0 Q)
    {P : HeightOneSpectrum (𝓞 D.host.E)} (hQ : ∀ PP ∈ Q, PP ≠ P ∧ ¬ Lev.IsConjPl PP P)
    {e f : AE D} (hP : IsPrimeIdem P e f) (x : AE D) (hx : f * x = x) : E0 * x = 0 ∧ cA D E0 * x = 0 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := hE
  have hI := GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents S
  have key : ∀ PP ∈ Q, es PP * x = 0 ∧ cA D (es PP) * x = 0 := by
    intro PP hPP
    have hPPi : IsPrimeIdem PP (es PP) (es PP + cA D (es PP)) := Or.inl ⟨hes PP hPP, rfl⟩
    have h4 := (hI.2.2.1 PP _ _ hPPi).2.2.2.2 P e f hP
    have hff : (es PP + cA D (es PP)) * f = 0 := by
      rcases h4 with h | ⟨-, h | h⟩
      · exact h
      · exact absurd h.symm (hQ PP hPP).1
      · exact absurd h (hQ PP hPP).2
    have ha := prime_idem_absorb S hPPi
    have hb := prime_idem_absorb_conj S hPPi
    constructor
    · calc es PP * x = ((es PP + cA D (es PP)) * es PP) * (f * x) := by rw [ha, hx]
        _ = es PP * (((es PP + cA D (es PP)) * f) * x) := by ring
        _ = 0 := by rw [hff]; ring
    · calc cA D (es PP) * x = ((es PP + cA D (es PP)) * cA D (es PP)) * (f * x) := by rw [hb, hx]
        _ = cA D (es PP) * (((es PP + cA D (es PP)) * f) * x) := by ring
        _ = 0 := by rw [hff]; ring
  constructor
  · rw [Finset.sum_mul]; exact Finset.sum_eq_zero fun PP h => (key PP h).1
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum, Finset.sum_mul]; exact Finset.sum_eq_zero fun PP h => (key PP h).2

theorem vac_of_frames {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)} {NS NT : ℕ}
    (hS : IsSDFrame S βS ΛS NS) (hT : IsSDFrame T βT ΛT NT) {P : Pl D.host.E}
    (hNS : ((NS : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) (hNT : ((NT : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    {f₀ : WO S T → ℂ} (hv : IsVacO ψ θ S T sS sT ΛS ΛT f₀) : IsVacAt ψ S T P f₀ := by
  obtain ⟨cS, hS⟩ := hS
  obtain ⟨cT, hT⟩ := hT
  refine GlobalTheory.T.isLocalVacuum_of_isLatticeVacuum_coprime_level ψ S T βS βT ΛS ΛT (NS ^ cS) (NT ^ cT) hS hT P ?_ f₀ hv.2.theta hv.2.lat
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]
  intro h
  rcases P.isPrime.mem_or_mem h with h | h
  · exact hNS (P.isPrime.mem_of_pow_mem _ h)
  · exact hNT (P.isPrime.mem_of_pow_mem _ h)

theorem vac_pt {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} {P : Pl D.host.E}
    {f₀ Φ f : WO S T → ℂ} {E1 : AE D} {Λ : AddSubgroup (WO S T)}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hv : IsVacAt ψ S T P f₀) (ht : IsThetaAt ψ (symplO S T) (heisO ψ S T) E1 Λ 1 f₀ Φ f)
    (hE : ∀ e' f', IsPrimeIdem P e' f' → ∀ x : AE D, f' * x = x → E1 * x = 0 ∧ cA D E1 * x = 0)
    (hth : ∀ φ, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f φ)) :
    ∀ φ, IsVacAt ψ S T P (pureTensorO ψ θ S T sS sT BS BT f φ) := by
  intro φ
  refine ⟨hth φ, fun e' f' hP u hu hh => ?_⟩
  refine GlobalTheory.T.heisenbergOriented_finite_fixes_fockPolynomialVectors ψ θ S T hθ sS sT BS BT f hth u (infPart_latO hu) ?_ φ
  exact GlobalTheory.T.heisenbergOperator_fix_thetaDatum_away_splitPlaces ψ S T E1 Λ 1 f₀ Φ f ht u (fun i j => hE e' f' hP _ (half_absorb S hP hh i j))
    (hv.2 e' f' hP u hu hh)

theorem fock_vacua_good : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F →
    ∀ t P, Good R t P → (∀ k, k + 1 < D.R.m → ∀ φ, IsVacAt R.ψ _ _ P (R.ptY t k φ)) ∧ (∀ φ, IsVacAt R.ψ _ _ P (R.ptX t φ)) ∧
      ∀ i φ, IsVacAt R.ψ _ _ P (R.ptP i t φ) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC t P hG
  classical
  have hN := ((GlobalTheory.T.theta_lift_levels_good_primes_properties R F hC.lev).2.1 t P hG).1
  have hθ : IsInfFam R.θ := hC.models.inf
  have h1 : ((1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [Nat.cast_one]; exact fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have hm := D.R.two_le_m
  refine ⟨fun k hk => ?_, ?_, fun i => ?_⟩
  · obtain ⟨hvac, e, he, ht⟩ := hC.chain.vY t k hk
    have hv := vac_of_frames (hC.lev.βY k (by omega)) (hC.lev.βY (k + 1) hk) hN hN hvac
    exact vac_pt hθ hv ht (fun e' f' hP x hx => idemSum_mul_zero (Yc D k) he (fun PP h => hG PP (Finset.mem_union.1 h)) hP x hx) (hC.chain.ptY t k hk)
  · obtain ⟨hvac, e, he, ht⟩ := hC.chain.vX t
    have hv := vac_of_frames (hC.lev.βY (D.R.m - 1) (by omega)) hC.lev.βX hN h1 hvac
    exact vac_pt hθ hv ht (fun e' f' hP x hx => idemSum_mul_zero (Yc D (D.R.m - 1)) he (fun PP h => hG PP (Finset.mem_union.1 h)) hP x hx) (hC.chain.ptX t)
  · obtain ⟨hvac, e, he, ht⟩ := hC.thP.vP i t
    have hv := vac_of_frames (hC.lev.βV i) (hC.lev.βW i) h1 h1 hvac
    refine vac_pt hθ hv ht (fun e' f' hP x hx => ?_) (hC.thP.pt_theta i t)
    obtain ⟨a, b⟩ := idemSum_mul_zero (Vc D i) he (fun PP h => hG PP (Finset.mem_union.1 h)) hP x hx
    exact ⟨b, by rw [cA_cA]; exact a⟩

end GlobalTheory.VacGood

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FockVectorsChainIsVacuumOffThetaLevelsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVectors_chain_isVacuum_off_thetaLevels : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → ∀ t P, Good R t P → (∀ k, k + 1 < D.R.m → ∀ φ, IsVacAt R.ψ _ _ P (R.ptY t k φ)) ∧ (∀ φ, IsVacAt R.ψ _ _ P (R.ptX t φ)) ∧ ∀ i φ, IsVacAt R.ψ _ _ P (R.ptP i t φ) := by
  first | exact @GlobalTheory.VacGood.fock_vacua_good | exact GlobalTheory.VacGood.fock_vacua_good | (intros; apply GlobalTheory.VacGood.fock_vacua_good <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalGlobalOfGelfandKazhdan
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalGlobalOfGelfandKazhdan
open NumberField GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory

theorem galoisRepOfPolarizedCuspidal_iff_pair : GlobalTheory.Published.GelfandKazhdanDual →
    (GlobalTheory.Published.CaraianiLocalGlobalDual → GlobalTheory.Published.CaraianiLocalGlobal) ∧
    (GlobalTheory.Published.GaloisRepOfPolarizedPair → GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) := by
  intro hGK
  refine ⟨fun hC => ?_, fun hP => ?_⟩
  · intro E Ω _ _ _ _ _ _ l _ ι a ha π hcsd hcoh
    have hd : DualIsConj π :=
      (dualIsConjBy_one π).1 (GlobalTheory.T.cuspContragredientIsCMConjTwist_of_paired_invTranspose E a π 1 (hGK E a _) ((GlobalTheory.GalOfCusp.isConjDualBy_one π).2 hcsd))
    exact hC E Ω l ι a ha π hd hcoh
  · intro E Ω _ _ _ _ _ _ l _ ι a ha π χ hr hpol
    exact hP E Ω l ι a ha π χ hr
      ⟨hpol.sign, GlobalTheory.T.cuspContragredientIsCMConjTwist_of_paired_invTranspose E a π (GlobalTheory.GalOfCusp.compNorm E χ) (hGK E a _) hpol.dual⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalGlobalOfGelfandKazhdanStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_global_of_gelfand_kazhdan : GlobalTheory.Published.GelfandKazhdanDual → (GlobalTheory.Published.CaraianiLocalGlobalDual → GlobalTheory.Published.CaraianiLocalGlobal) ∧ (GlobalTheory.Published.GaloisRepOfPolarizedPair → GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) := by
  first | exact @GlobalTheory.galoisRepOfPolarizedCuspidal_iff_pair | exact GlobalTheory.galoisRepOfPolarizedCuspidal_iff_pair | (intros; apply GlobalTheory.galoisRepOfPolarizedCuspidal_iff_pair <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatchedSphericalPairsCommuteCompositeLift
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatchedSphericalPairsCommuteCompositeLift
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3.SysE


set_option maxHeartbeats 1000000 in
theorem matched_commute : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → SchurAll R → ∀ SF, IsSF R SF → ∀ t P, Good R t P → ∀ cX c0, MatchE R t P cX c0 → ∀ hX, IsOpsX R t hX → (∀ h, IsOpsE R h → ∀ y, R.Th t (hX P cX y) = h P c0 (R.Th t y)) ∧ ∀ c, ∀ w ∈ EEc R SF c, hX P cX (LinearMap.adjoint (R.Th t) w) = evC (Yc D 0) P (fun d => c P (dualLab d)) c0 • LinearMap.adjoint (R.Th t) w := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hS SF hSF t P hg cX c0 hM hX hXo
  have gd := GlobalTheory.GoodPrimes.good_primes R F hC.lev
  have hg0 : Good R A.μ0 P := (gd.2.1 t P hg).2.2
  have injE : Function.Injective R.HE.e := hC.models.HE.1
  have injX : Function.Injective (R.HX t).e := (hC.models.HX t).1

  have part1 : ∀ h, IsOpsE R h → ∀ y, R.Th t (hX P cX y) = h P c0 (R.Th t y) := by
    intro h hh y
    apply injE
    exact (hM y (hX P cX y) (hXo P hg cX y)).trans (hh P hg0 c0 (R.Th t y)).symm
  refine ⟨part1, ?_⟩
  intro c w hw
  have h01 := GlobalTheory.T.exists_sphericalOperators_rows_normal_eigenspaces R F hC hS SF hSF
  rcases h01 with ⟨h0, h0o, h0n, -, h0e, -⟩
  have hX01 := (GlobalTheory.T.realization_family_normal_operators R F hC.lev hC.fam hC.models).1 t
  rcases hX01 with ⟨hX0, hX0o, hX0n⟩
  have eqX : hX P cX = hX0 P cX := by
    ext x
    apply injX
    exact (hXo P hg cX x).trans (hX0o P hg cX x).symm
  have eX : LinearMap.adjoint (hX0 P cX) = hX0 P (dualC (Finsupp.mapRange star (star_zero ℂ) cX)) := hX0n.2 P hg cX
  have cX' : Commute (hX0 P cX) (hX0 P (dualC (Finsupp.mapRange star (star_zero ℂ) cX))) := hX0n.1 P P hg hg _ _
  have nX0 : Commute (hX0 P cX) (LinearMap.adjoint (hX0 P cX)) :=
    @Eq.subst (Module.End ℂ (R.HX t).H) (fun B => Commute (hX0 P cX) B) _ _ eX.symm cX'
  have nX : Commute (hX P cX) (LinearMap.adjoint (hX P cX)) :=
    @Eq.subst (Module.End ℂ (R.HX t).H) (fun B => Commute B (LinearMap.adjoint B)) _ _ eqX.symm nX0
  have eE : LinearMap.adjoint (h0 P c0) = h0 P (dualC (Finsupp.mapRange star (star_zero ℂ) c0)) := h0n.2 P hg0 c0
  have cE : Commute (h0 P c0) (h0 P (dualC (Finsupp.mapRange star (star_zero ℂ) c0))) := h0n.1 P P hg0 hg0 _ _
  have nE : Commute (h0 P c0) (LinearMap.adjoint (h0 P c0)) :=
    @Eq.subst (Module.End ℂ R.HE.H) (fun B => Commute (h0 P c0) B) _ _ eE.symm cE
  exact GlobalTheory.T.eigenvector_adjoint_intertwiner_normal_operators (R.Th t) (fun _ : Unit => hX P cX) (fun _ : Unit => h0 P c0)
    (fun _ u => part1 h0 h0o u) (fun _ => nX) (fun _ => nE) () _ w (h0e c P hg0 c0 w hw)

end GlobalTheory.Hk3.SysE
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatchedSphericalPairsCommuteCompositeLiftStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matched_spherical_pairs_commute_composite_lift : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → SchurAll R → ∀ SF, IsSF R SF → ∀ t P, Good R t P → ∀ cX c0, MatchE R t P cX c0 → ∀ hX, IsOpsX R t hX → (∀ h, IsOpsE R h → ∀ y, R.Th t (hX P cX y) = h P c0 (R.Th t y)) ∧ ∀ c, ∀ w ∈ EEc R SF c, hX P cX (LinearMap.adjoint (R.Th t) w) = evC (Yc D 0) P (fun d => c P (dualLab d)) c0 • LinearMap.adjoint (R.Th t) w := by
  first | exact @GlobalTheory.Hk3.SysE.matched_commute | exact GlobalTheory.Hk3.SysE.matched_commute | (intros; apply GlobalTheory.Hk3.SysE.matched_commute <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightCocharacterEqOfGoodPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCommonEigenvalueOfMemAdjoin
namespace GlobalTheory.CommonEigenvalueAdjoin

theorem exists_common_eigenvalue_of_mem_adjoin {M : Type} [AddCommGroup M] [Module ℂ M]
    (s : Set (Module.End ℂ M)) (u u' : M)
    (h : ∀ x ∈ s, ∃ l : ℂ, x u = l • u ∧ x u' = l • u') :
    ∀ a ∈ Algebra.adjoin ℂ s, ∃ l : ℂ, a u = l • u ∧ a u' = l • u' := by
  intro a ha
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact h x hx
  | algebraMap r => exact ⟨r, by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨l, h1, h2⟩ := hx
    obtain ⟨m, h3, h4⟩ := hy
    exact ⟨l + m, by rw [LinearMap.add_apply, h1, h3, add_smul],
      by rw [LinearMap.add_apply, h2, h4, add_smul]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨l, h1, h2⟩ := hx
    obtain ⟨m, h3, h4⟩ := hy
    exact ⟨m * l, by rw [Module.End.mul_apply, h3, map_smul, h1, smul_smul],
      by rw [Module.End.mul_apply, h4, map_smul, h2, smul_smul]⟩

end GlobalTheory.CommonEigenvalueAdjoin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightCocharacterEqOfGoodPlaces
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3.LabDet

theorem adjoin_common {M : Type} [AddCommGroup M] [Module ℂ M] (s : Set (Module.End ℂ M)) (u u' : M)
    (h : ∀ x ∈ s, ∃ l : ℂ, x u = l • u ∧ x u' = l • u') :
    ∀ a ∈ Algebra.adjoin ℂ s, ∃ l : ℂ, a u = l • u ∧ a u' = l • u' := by
  first
  | exact @_root_.GlobalTheory.CommonEigenvalueAdjoin.exists_common_eigenvalue_of_mem_adjoin
  | exact _root_.GlobalTheory.CommonEigenvalueAdjoin.exists_common_eigenvalue_of_mem_adjoin
  | (apply _root_.GlobalTheory.CommonEigenvalueAdjoin.exists_common_eigenvalue_of_mem_adjoin <;> assumption)
  | (intros; apply _root_.GlobalTheory.CommonEigenvalueAdjoin.exists_common_eigenvalue_of_mem_adjoin <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CommonEigenvalueAdjoin.exists_common_eigenvalue_of_mem_adjoin <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CommonEigenvalueAdjoin.exists_common_eigenvalue_of_mem_adjoin ..)

variable {D : D7}

theorem opOf_single {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (P : Pl D.host.E)
    (d : List ℤ) : opOf π P (Finsupp.single d 1) = ∑ γ ∈ rep V P d, π γ := by
  unfold opOf
  rw [Finsupp.sum_single_index (by simp), one_smul]

theorem opOf_single_of_not {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (P : Pl D.host.E)
    (d : List ℤ) (h : ¬ IsLab V P d) : opOf π P (Finsupp.single d 1) = 0 := by
  rw [opOf_single]
  unfold rep
  rw [dite_eq_right h, Finset.sum_empty]

theorem sphOp_rep {V : HSp D} {P : Pl D.host.E} {d : List ℤ} (h : IsLab V P d) : SphOp V P d (rep V P d) := by
  unfold rep
  rw [dite_eq_left h]
  exact h.choose_spec

theorem eq_of_split {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (P : Pl D.host.E)
    (hP : conjPl P ≠ P) (u u' : M) (hu : u ≠ 0) (hu' : u' ≠ 0) (fu : ∀ k ∈ hyp V P, π k u = u) (fu' : ∀ k ∈ hyp V P, π k u' = u')
    (a a' b b' : List ℤ → ℂ)
    (ha : ∀ d, IsLab V P d → opOf π P (Finsupp.single d 1) u = a d • u)
    (ha' : ∀ d, IsLab V P d → opOf π P (Finsupp.single d 1) u' = a' d • u')
    (hb : ∀ d, IsLab V (conjPl P) d → opOf π (conjPl P) (Finsupp.single d 1) u = b d • u)
    (hb' : ∀ d, IsLab V (conjPl P) d → opOf π (conjPl P) (Finsupp.single d 1) u' = b' d • u')
    (ea : ∀ k, k ≤ V.rank → a (splitLab V.rank k) = a' (splitLab V.rank k))
    (eb : ∀ k, k ≤ V.rank → b (splitLab V.rank k) = b' (splitLab V.rank k)) :
    ∀ d, IsLab V P d → a d = a' d := by
  intro d hd
  obtain ⟨x, hx, hxe⟩ := GlobalTheory.T.exists_adjoin_splitHeckeGenerators_duals_spherical V P hP M π d
  obtain ⟨l, h1, h2⟩ := adjoin_common _ u u' (by
    rintro y ⟨k, hk, rfl | rfl⟩
    · by_cases hl : IsLab V P (splitLab V.rank k)
      · exact ⟨_, ha _ hl, by rw [ha' _ hl, ea k hk]⟩
      · exact ⟨0, by simp [opOf_single_of_not π P _ hl], by simp [opOf_single_of_not π P _ hl]⟩
    · have hc := (GlobalTheory.T.sphericalHecke_conjPlace_eq_dualLabel V P).2.2 (Finsupp.single (splitLab V.rank k) 1) M π
      have hd : dualC (Finsupp.single (splitLab V.rank k) 1) = Finsupp.single (dualLab (splitLab V.rank k)) 1 := by
        unfold dualC
        rw [Finsupp.mapDomain_single]
      rw [hd] at hc
      rw [← hc u fu, ← hc u' fu']
      by_cases hl : IsLab V (conjPl P) (splitLab V.rank k)
      · exact ⟨_, hb _ hl, by rw [hb' _ hl, eb k hk]⟩
      · exact ⟨0, by simp [opOf_single_of_not π _ _ hl], by simp [opOf_single_of_not π _ _ hl]⟩) x hx
  rw [hxe u fu, ha d hd] at h1
  rw [hxe u' fu', ha' d hd] at h2
  rw [smul_left_injective ℂ hu h1, smul_left_injective ℂ hu' h2]

def rLin (V : HSp D) (g : GA D V) : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) where
  toFun F := fun h => F (h * g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rRep {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) : GA D V →* Module.End ℂ (MMap M) where
  toFun g := postOn M (rLin V g)
  map_one' := by
    ext U v h
    show U v (h * 1) = U v h
    rw [mul_one]
  map_mul' g g' := by
    ext U v h
    show U v (h * (g * g')) = U v (h * g * g')
    rw [mul_assoc]

theorem rRep_apply {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (g : GA D V) (U : MMap M) (v : M.Vec) (h : GA D V) :
    rRep M g U v h = U v (h * g) := rfl

theorem sum_rRep {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (B : Finset (GA D V)) :
    ∑ γ ∈ B, rRep M γ = heckeOn M B := by
  ext U v h
  rw [LinearMap.sum_apply, MultilinearMap.sum_apply, Finset.sum_apply]
  rfl

theorem mult_lev {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (U : MMap M) (hU : U ∈ Mult θ M J χ) (k : GA D V) (hk : k ∈ J)
    (h1 : χ k = 1) : rRep M k U = U := by
  induction hU using Submodule.span_induction with
  | mem x hx =>
    ext v h
    rw [rRep_apply, hx.lev v k hk h, h1, one_mul]
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
  | smul a x _ hx => rw [map_smul, hx]

theorem mem_partFull {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (c : Pl D.host.E → List ℤ → ℂ) (U : MMap M) :
    U ∈ partFull θ M J χ Sb c ↔ U ∈ Mult θ M J χ ∧ ∀ P d B, Hecke₂ V J χ Sb P d B → heckeOn M B U = c P d • U := by
  unfold partFull
  simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

theorem part_eq_of_labels : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → ∀ SF, IsSF R SF → ∀ i (c c' : Pl D.host.E → List ℤ → ℂ), Wcc R SF i c ≠ ⊥ → Wcc R SF i c' ≠ ⊥ → (∀ P, Good R A.μ0 P → conjPl P ≠ P → ∀ k, k ≤ (Wc D i).rank → c P (splitLab (Wc D i).rank k) = c' P (splitLab (Wc D i).rank k)) → (∀ P d, Good R A.μ0 P → conjPl P = P → IsLab (Wc D i) P d → c P d = c' P d) → Wcc R SF i c = Wcc R SF i c' := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC SF hSF i c c' hc hc' hs hi
  obtain ⟨hQ, hgood, hoff, -⟩ := GlobalTheory.T.theta_lift_levels_good_primes_properties R F hC.lev
  obtain ⟨n, hβ⟩ := hC.lev.βW i
  have hlev := fun (P : Pl D.host.E) (hP : Good R A.μ0 P) =>
    GlobalTheory.T.level_operators_at_prime_off_level_datum (Wc D i) (R.βW i) (R.ΛW i) (1 ^ n) (R.datWp i R.triv) hβ P
      (by rw [one_pow, Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top)
      (by
        intro PP hPP
        refine hP PP (hPP.imp id ?_)
        intro h
        exact absurd h (Finset.notMem_empty _))
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  obtain ⟨x', hx', hx0'⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc'
  have inj : Function.Injective (R.HW i (sg0 D A)).e := (hC.models.HW i (sg0 D A)).1
  have hu : (R.HW i (sg0 D A)).e x ≠ 0 := fun h => hx0 (inj (by rw [h, map_zero]))
  have hu' : (R.HW i (sg0 D A)).e x' ≠ 0 := fun h => hx0' (inj (by rw [h, map_zero]))
  have hp := (mem_partFull _ _ _ _ _ _ _).1 (Submodule.mem_inf.1 (Submodule.mem_comap.1 hx)).2
  have hp' := (mem_partFull _ _ _ _ _ _ _).1 (Submodule.mem_inf.1 (Submodule.mem_comap.1 hx')).2
  have key : ∀ P, Good R A.μ0 P → ∀ d, IsLab (Wc D i) P d → c P d = c' P d := by
    intro P hP
    by_cases hcP : conjPl P = P
    · exact fun d hd => hi P d hP hcP hd
    · have hP' : Good R A.μ0 (conjPl P) := (hgood _ P hP).2.1
      have hcc : conjPl (conjPl P) = P := ValuationRepresentative.conjPl_conjPl P
      refine eq_of_split (rRep (R.MW i (sg0 D A))) P hcP _ _ hu hu' ?_ ?_ (c P) (c' P) (c (conjPl P)) (c' (conjPl P)) ?_ ?_ ?_ ?_
        (hs P hP hcP) (hs _ hP' (by rw [hcc]; exact fun h => hcP h.symm))
      · exact fun k hk => mult_lev _ _ _ _ _ hp.1 k ((hlev P hP).1 k hk).1 ((hlev P hP).1 k hk).2
      · exact fun k hk => mult_lev _ _ _ _ _ hp'.1 k ((hlev P hP).1 k hk).1 ((hlev P hP).1 k hk).2
      · intro d hd
        rw [opOf_single, sum_rRep]
        exact hp.2 _ _ _ (((hlev P hP).2.1 SF d _).2 ⟨(hoff SF hSF P).2 hP, sphOp_rep hd⟩)
      · intro d hd
        rw [opOf_single, sum_rRep]
        exact hp'.2 _ _ _ (((hlev P hP).2.1 SF d _).2 ⟨(hoff SF hSF P).2 hP, sphOp_rep hd⟩)
      · intro d hd
        rw [opOf_single, sum_rRep]
        exact hp.2 _ _ _ (((hlev _ hP').2.1 SF d _).2 ⟨(hoff SF hSF _).2 hP', sphOp_rep hd⟩)
      · intro d hd
        rw [opOf_single, sum_rRep]
        exact hp'.2 _ _ _ (((hlev _ hP').2.1 SF d _).2 ⟨(hoff SF hSF _).2 hP', sphOp_rep hd⟩)
  have key2 : ∀ P d B, Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) SF P d B →
      c P d = c' P d := by
    intro P d B hB
    have hP : Good R A.μ0 P := by
      obtain ⟨_, _, _, _, ho, _⟩ := hB
      exact (hoff SF hSF P).1 ho
    exact key P hP d ⟨B, (((hlev P hP).2.1 SF d B).1 hB).2⟩
  unfold Wcc
  congr 2
  ext U
  rw [mem_partFull, mem_partFull]
  refine and_congr_right fun _ => forall_congr' fun P => forall_congr' fun d => forall_congr' fun B => imp_congr_right fun hB => ?_
  rw [key2 P d B hB]

end GlobalTheory.Hk3.LabDet

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightCocharacterEqOfGoodPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_cocharacter_eq_of_good_places : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → ∀ SF, IsSF R SF → ∀ i (c c' : Pl D.host.E → List ℤ → ℂ), Wcc R SF i c ≠ ⊥ → Wcc R SF i c' ≠ ⊥ → (∀ P, Good R A.μ0 P → conjPl P ≠ P → ∀ k, k ≤ (Wc D i).rank → c P (splitLab (Wc D i).rank k) = c' P (splitLab (Wc D i).rank k)) → (∀ P d, Good R A.μ0 P → conjPl P = P → IsLab (Wc D i) P d → c P d = c' P d) → Wcc R SF i c = Wcc R SF i c' := by
  first | exact @GlobalTheory.Hk3.LabDet.part_eq_of_labels | exact GlobalTheory.Hk3.LabDet.part_eq_of_labels | (intros; apply GlobalTheory.Hk3.LabDet.part_eq_of_labels <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaIntertwinesMatchedOperators
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaIntertwinesMatchedOperators
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SysW


set_option maxHeartbeats 1000000 in
theorem matched_operators_theta_intertwine : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → SchurAll R → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ SF, IsSF R SF → ∀ i t P, Good R t P → ∀ cV cW, MatchW R i t P cV cW → ∀ hV, IsOpsV R i t hV → (∀ h, IsOpsW R i h → ∀ y, R.thG i t (hV P cV y) = h P cW (R.thG i t y)) ∧ ∀ c, ∀ w ∈ Wcc R SF i c, hV P cV (LinearMap.adjoint (R.thG i t) w) = evC (Wc D i) P (c P) cW • LinearMap.adjoint (R.thG i t) w := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hS hX SF hSF i t P hP cV cW hM hV hhV
  have hP0 : Good R A.μ0 P := ((GlobalTheory.GoodPrimes.good_primes R F hC.lev).2.1 t P hP).2.2
  have hWinj : Function.Injective (R.HW i (sg0 D A)).e := (hC.models.HW i (sg0 D A)).1
  have key : ∀ h, IsOpsW R i h → ∀ y, R.thG i t (hV P cV y) = h P cW (R.thG i t y) := by
    intro h hh y
    have h1 := hM y (hV P cV y) (hhV P hP cV y)
    have h2 := hh P hP0 cW (R.thG i t y)
    exact hWinj (h1.trans h2.symm)
  refine ⟨key, ?_⟩
  intro c w hw
  have XW := GlobalTheory.T.sphericalOperators_forms_on_rank_space_normal R F hC hS hX SF hSF i
  obtain ⟨hW, hWo, hWn, -, -, -, hWe, -⟩ := XW
  have XV := (GlobalTheory.T.realization_family_normal_operators R F hC.lev hC.fam hC.models).2 i t
  obtain ⟨hV', hV'o, hV'n⟩ := XV
  have hVinj : Function.Injective (R.HV i t).e := (hC.models.HV i t).1
  have heq : ∀ c, hV P c = hV' P c := fun c => LinearMap.ext fun x => hVinj (by rw [hhV P hP, hV'o P hP])
  have nV' : Commute (hV' P cV) (LinearMap.adjoint (hV' P cV)) :=
    Eq.mpr (congrArg (Commute (hV' P cV)) (hV'n.2 P hP cV)) (hV'n.1 P P hP hP _ _)
  have nV : Commute (hV P cV) (LinearMap.adjoint (hV P cV)) :=
    Eq.mpr (congrArg (fun L => Commute L (LinearMap.adjoint L)) (heq cV)) nV'
  have nW : Commute (hW P cW) (LinearMap.adjoint (hW P cW)) :=
    Eq.mpr (congrArg (Commute (hW P cW)) (hWn.2 P hP0 cW)) (hWn.1 P P hP0 hP0 _ _)
  exact GlobalTheory.T.eigenvector_adjoint_intertwiner_normal_operators (R.thG i t) (fun _ : Unit => hV P cV) (fun _ : Unit => hW P cW) (fun _ u => key hW hWo u)
    (fun _ => nV) (fun _ => nW) () _ w (hWe c P hP0 cW w hw)

end GlobalTheory.SysW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaIntertwinesMatchedOperatorsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_intertwines_matched_operators : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → SchurAll R → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ SF, IsSF R SF → ∀ i t P, Good R t P → ∀ cV cW, MatchW R i t P cV cW → ∀ hV, IsOpsV R i t hV → (∀ h, IsOpsW R i h → ∀ y, R.thG i t (hV P cV y) = h P cW (R.thG i t y)) ∧ ∀ c, ∀ w ∈ Wcc R SF i c, hV P cV (LinearMap.adjoint (R.thG i t) w) = evC (Wc D i) P (c P) cW • LinearMap.adjoint (R.thG i t) w := by
  first | exact @GlobalTheory.SysW.matched_operators_theta_intertwine | exact GlobalTheory.SysW.matched_operators_theta_intertwine | (intros; apply GlobalTheory.SysW.matched_operators_theta_intertwine <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeOperatorsRowsLiftsRationalAdjointClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeOperatorsRationalAdjointClosedOfWeakChar
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LiftsOpMatMem
open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitHeckeCore

open Formalism.DivisionValues Formalism.IndefR Formalism.L2.Theta GlobalTheory.HeckeRational GlobalTheory.SplitHeckeAdj

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem rows_opMat_mem (R : RealDat D A Ks) (hf : R.IsFam) (t i a b) :
    (A.fam.R t).opMat i a b ∈ Formalism.DivisionValues.cmMax D.what₂.LL := by
  obtain ⟨P, k⟩ := i
  show LinearMap.toMatrix (A.MtildeCSD t).basis (A.MtildeCSD t).basis (A.heckeR t (P, k)) a b ∈ _
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [(hf.degR t P).1]
    exact toMatrix_one_mem _ _ _ _
  rcases le_or_gt k D.sp.X'.rank with hk' | hk'
  · exact rows_dcOp_mem_cmMax R hf.tie t _ _ ((R.B.R t).hecke.op_eq (P, k) ⟨hk, hk'⟩) a b
  · rw [(hf.degR t P).2 k hk', map_zero]
    exact Subfield.zero_mem _

theorem lifts_opMat_mem (R : RealDat D A Ks) (hf : R.IsFam) (j t i a b) :
    (A.fam.L j t).opMat i a b ∈ Formalism.DivisionValues.cmMax D.what₂.LL := by
  obtain ⟨P, k⟩ := i
  show LinearMap.toMatrix (A.MtCSD j t).basis (A.MtCSD j t).basis (A.heckeL j t (P, k)) a b ∈ _
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [(hf.degL j t P).1]
    exact toMatrix_one_mem _ _ _ _
  rcases le_or_gt k (Vc D j).rank with hk' | hk'
  · exact lifts_dcOp_mem_cmMax R hf.tie j t _ _ ((R.B.L j t).hecke.op_eq (P, k) ⟨hk, hk'⟩) a b
  · rw [(hf.degL j t P).2 k hk', map_zero]
    exact Subfield.zero_mem _

theorem hecke_okH_comm : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (_F : Face D A), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → (∀ t, (A.fam.R t).OkH ∧ Formalism.L2.Col.PairComm (A.fam.R t).op) ∧ ∀ j t, (A.fam.L j t).OkH ∧ Formalism.L2.Col.PairComm (A.fam.L j t).op := by
  intro D G _ _ Pl0 T A Ks _ _ _ R _ hl hf hm
  obtain ⟨gramR, c0R, c0L, tie⟩ := hf.tie
  have honto : ∀ t PP, Bridge.SplitOff PP ((R.Sb : Set (Pl D.host.E)) ∪ (R.Q t : Set (Pl D.host.E))) → ∃ P, R.pl P = PP :=
    fun t PP hP => hf.pl_onto PP (splitOff_mono Set.subset_union_left hP)
  have hS : ∀ t PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → PP ∈ (R.Sb : Set (Pl D.host.E)) ∪ (R.Q t : Set (Pl D.host.E)) :=
    fun t PP hP => hP.elim (fun h1 => Or.inl (hf.Sb h1)) Or.inr
  refine ⟨fun t => ?_, fun j t => ?_⟩
  · obtain ⟨c, hc⟩ := hl.βX
    rw [one_pow] at hc
    have h := side_adj_comm D.sp.X' R.βX R.ΛX (R.datXt t) hc R.pl (A.ok t) _ (tie.ok t) (honto t) (hS t)
      R.cX.coef.ρ (fun γ => hm.cX.2.1 γ) D.what₂.embLL (A.MtildeCSD t) (R.B.R t).pres (A.heckeR t)
      (R.B.R t).hecke (hf.degR t)
    exact ⟨⟨rows_opMat_mem R hf t, h.1⟩, h.2⟩
  · obtain ⟨c, hc⟩ := hl.βV j
    rw [one_pow] at hc
    have h := side_adj_comm (Vc D j) (R.βV j) (R.ΛV j) (R.datVt j t) hc R.pl (A.ok t) _ (tie.ok t) (honto t) (hS t)
      (R.cV j).coef.ρ (fun γ => (hm.cV j).2.1 γ) D.what₂.embLL (A.MtCSD j t) (R.B.L j t).pres (A.heckeL j t)
      (R.B.L j t).hecke (hf.degL j t)
    exact ⟨⟨lifts_opMat_mem R hf j t, h.1⟩, h.2⟩

end GlobalTheory.SplitHeckeCore

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Hk3

theorem hecke_operators_rational_adjoint_closed_of_weak_char : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → (∀ t, (A3.A.fam.R t).OkH) ∧ ∀ j t, (A3.A.fam.L j t).OkH := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hC
  have h := GlobalTheory.SplitHeckeCore.hecke_okH_comm R.toRealDat F.lv2 hC.base.lev hC.base.fam hC.base.models
  exact ⟨fun t => (h.1 t).1, fun j t => (h.2 j t).1⟩

end GlobalTheory.Hk3

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeOperatorsRowsLiftsRationalAdjointClosed
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.InertOkH

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem csum_zero_left {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) (g : S.Cl → S.V) : S.csum 0 g = 0 := by
  simp [CSD.csum]

theorem csum_zero_right {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) (f : S.Cl → S.V) : S.csum f 0 = 0 := by
  simp [CSD.csum]


set_option maxHeartbeats 4000000 in
theorem inertHeckeOperators_rows_rational_adjointClosed (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hW : R.WeakCharacterisation F) (hJ : InertJunk A3) (t : T) :
    (A3.rowI t).InertRationalAdjoint := by
  obtain ⟨tie⟩ := hW.inert.hR t
  have hrk : D.sp.X'.rank = A3.A.r + D.R.m * A3.A.t := R.toRealDat.B.rankR
  have hpl := (GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hW).2.2.1 t
  have key := GlobalTheory.T.inertHeckeOperators_rows_rational_selfAdjoint_labels R.toRealDat F.lv2 hW.base.lev hW.base.fam hW.base.models t (A3.okI t × List ℕ)
    (fun i => R.plI i.1) (fun i => Formalism.IndefR.Links.labIn D.sp.X'.rank i.2) (A3.heckeRI t)
    (fun i => Formalism.L2.Col.InertTypeOk D.sp.X'.rank i.2)
    (fun i hi => ⟨(hpl i.1 i.1.2).1, (hpl i.1 i.1.2).2,
      ((GlobalTheory.T.selfDual_antitone_list_iff_inertPrimeHeckeExponents D.sp.X'.rank (Formalism.IndefR.Links.labIn D.sp.X'.rank i.2)).mpr ⟨i.2, hi.2.2, hi.1, hi.2.1, rfl⟩).2.1⟩) tie
  have hop : ∀ k : A3.okI t × List ℕ, A3.heckeRI t k = 0 ∨
      ∃ s', Formalism.L2.Col.InertTypeOk D.sp.X'.rank s' ∧ A3.heckeRI t k = A3.heckeRI t (k.1, s') := by
    rintro ⟨Q, s⟩
    rcases hJ.R t Q s with h | ⟨s', hs', h⟩
    · exact Or.inl h
    · exact Or.inr ⟨s', hrk ▸ hs', h⟩
  refine ⟨fun k a b => ?_, fun k => ⟨k, fun f g => ?_⟩⟩
  · show LinearMap.toMatrix (A3.A.MtildeCSD t).basis (A3.A.MtildeCSD t).basis (A3.heckeRI t k) a b ∈ cmMax D.what₂.LL
    rcases hop k with h | ⟨s', hs', h⟩
    · rw [h]
      simp only [map_zero]
      exact zero_mem _
    · rw [h]
      exact (key (k.1, s') hs').1 a b
  · rcases hop k with h | ⟨s', hs', h⟩
    · have h0 : (A3.rowI t).opI k = 0 := h
      rw [h0]
      simp only [LinearMap.zero_apply, ZeroMemClass.coe_zero, csum_zero_left, csum_zero_right]
    · have h1 : (A3.rowI t).opI k = A3.heckeRI t (k.1, s') := h
      rw [h1]
      exact (key (k.1, s') hs').2.1 f g


set_option maxHeartbeats 4000000 in
theorem inertHeckeOperators_lifts_rational_adjointClosed (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hW : R.WeakCharacterisation F) (hJ : InertJunk A3) (j : Fin D.R.m) (t : T) :
    (A3.liftI j t).InertRationalAdjoint := by
  obtain ⟨tie⟩ := hW.inert.hL j t
  have hrk : (Vc D j).rank = A3.A.r + A3.A.t := R.toRealDat.B.rankL j
  have hpl := (GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hW).2.2.1 t
  have key := GlobalTheory.T.inertHeckeOperators_lifts_rational_selfAdjoint_labels R.toRealDat F.lv2 hW.base.lev hW.base.fam hW.base.models j t (A3.okI t × List ℕ)
    (fun i => R.plI i.1) (fun i => Formalism.IndefR.Links.labIn (Vc D j).rank i.2) (A3.heckeLI j t)
    (fun i => Formalism.L2.Col.InertTypeOk (Vc D j).rank i.2)
    (fun i hi => ⟨(hpl i.1 i.1.2).1, (hpl i.1 i.1.2).2,
      ((GlobalTheory.T.selfDual_antitone_list_iff_inertPrimeHeckeExponents (Vc D j).rank (Formalism.IndefR.Links.labIn (Vc D j).rank i.2)).mpr ⟨i.2, hi.2.2, hi.1, hi.2.1, rfl⟩).2.1⟩) tie
  have hop : ∀ k : A3.okI t × List ℕ, A3.heckeLI j t k = 0 ∨
      ∃ s', Formalism.L2.Col.InertTypeOk (Vc D j).rank s' ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, s') := by
    rintro ⟨Q, s⟩
    rcases hJ.L j t Q s with h | ⟨s', hs', h⟩
    · exact Or.inl h
    · exact Or.inr ⟨s', hrk ▸ hs', h⟩
  refine ⟨fun k a b => ?_, fun k => ⟨k, fun f g => ?_⟩⟩
  · show LinearMap.toMatrix (A3.A.MtCSD j t).basis (A3.A.MtCSD j t).basis (A3.heckeLI j t k) a b ∈ cmMax D.what₂.LL
    rcases hop k with h | ⟨s', hs', h⟩
    · rw [h]
      simp only [map_zero]
      exact zero_mem _
    · rw [h]
      exact (key (k.1, s') hs').1 a b
  · rcases hop k with h | ⟨s', hs', h⟩
    · have h0 : (A3.liftI j t).opI k = 0 := h
      rw [h0]
      simp only [LinearMap.zero_apply, ZeroMemClass.coe_zero, csum_zero_left, csum_zero_right]
    · have h1 : (A3.liftI j t).opI k = A3.heckeLI j t (k.1, s') := h
      rw [h1]
      exact (key (k.1, s') hs').2.1 f g

theorem heckeOperators_rows_lifts_rational_adjointClosed : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → InertJunk A3 → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) ∧ (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hW hJ
  have h2 := hecke_operators_rational_adjoint_closed_of_weak_char R F hW
  exact ⟨fun t => ⟨h2.1 t, inertHeckeOperators_rows_rational_adjointClosed R F hW hJ t⟩, fun j t => ⟨h2.2 j t, inertHeckeOperators_lifts_rational_adjointClosed R F hW hJ j t⟩⟩

end GlobalTheory.InertOkH

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeOperatorsRowsLiftsRationalAdjointClosedStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.okH_inertRationalAdjoint_of_weakCharacterisation_inertJunk : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → InertJunk A3 → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) ∧ (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) := by
  first | exact @GlobalTheory.InertOkH.heckeOperators_rows_lifts_rational_adjointClosed | exact GlobalTheory.InertOkH.heckeOperators_rows_lifts_rational_adjointClosed | (intros; apply GlobalTheory.InertOkH.heckeOperators_rows_lifts_rational_adjointClosed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimeBadPrimesLevelsHypotheses
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.MomT
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recSeam HostTie AnTie badS)
open GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation (StdOver)

noncomputable section

namespace GlobalTheory.DatumJets

def SplitSet {X : Fields} (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (ϖ : 𝓞 X.E) (p : ℕ) : Prop :=
  X.Ok ∧ A.LaHyp a b S ∧ A.AA ≠ ⊥ ∧ A.ESmooth a b ∧ p.Prime ∧ ϖ * X.conjO ϖ = (p : 𝓞 X.E) ∧ IsCoprime ϖ (X.conjO ϖ) ∧
    ∀ P : HeightOneSpectrum (𝓞 X.E), ϖ ∈ P.asIdeal → P ∈ S

def TranslateInt {X : Fields} (A : Amb X) {a b : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (π : X.E) (κ : ℂ) (e : DVar X.Tau a b →₀ ℕ) : Prop :=
  ∀ (s : HomE X.E a b) (n : ℕ), Nat.Coprime n p → ((n : X.E) * π) • s ∈ per A N N' →
    GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions.IntAt lam (κ * jetC A.cD (Wx A s (A.e a b N N')) e)

def PlaceAbove : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (p : ℕ) [Fact p.Prime] (w : HeightOneSpectrum (𝓞 K)),
    (p : 𝓞 K) ∈ w.asIdeal →
    ∃ lam : TaylorLogMetric.Qbar →+* ℂ_[p], ∀ k : K, GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions.IntAt lam (σ k) ↔ w.valuation K k ≤ 1

def TypePrimeBadPrimesLevelsHypotheses : Prop :=
  ∀ (D : D7) (EX : ErrX D) (sel : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E)) (δ : ℂ)
    (B : Base D D.host.ccK δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ), HostTie EX → IsSel (recFields D) sel →
    ∀ (i : Fin 2) (u : (recPrimes EX).Word) (mu : Tup (recFields D).F (recFields D).E (recFields D).K (badS D))
      (cst : LocCst (recFields D) (rowSG (recPrimes EX) sel mu)), cst.Ok →
    ∀ a b : ℕ, (ambOf (recSeam D) B χ cD).LaHyp a b ∅ → (ambOf (recSeam D) B χ cD).ESmooth a b →
      SplitSet (ambOf (recSeam D) B χ cD) a b (Sall sel mu u) ((recFields D).conjO ((recPrimes EX).piG i))
        ((recPrimes EX).g i) ∧
      0 < cAof sel mu cst ∧ 0 < cBof sel mu cst u ∧ (recPrimes EX).g i ∣ cBof sel mu cst u

end GlobalTheory.DatumJets
end
end
