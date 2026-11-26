module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesBaseTwistedUniversalRational
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniversalSeriesCoefficientsIntegralCoreForms

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniversalSeriesCoeffBoundedInSupOfTwistSeriesSid
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XiIntComb
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesIntegralCoreSupLatticeCombination
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupLatticeCombOfBaseInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.DictionaryCast
open Formalism.IndefR.FWT _root_.Formalism.L2.Pj
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw}

theorem evW_smul (YS : NX.NExpRealS Rl cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
    (j : Fin D.R.m) (a : D.what₂.LL) (x : S.WL ((j : ℕ) + 1)) :
    evW YS v₀ j (a • x) = sg0 D A3.A a • evW YS v₀ j x := by
  simp only [evW, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [LinearEquiv.map_smul, LinearMap.map_smulₛₗ, map_smul]
  rfl

theorem castDict_sum_smul' {V W : HSp D} (e : V = W) {m : ℕ} (a : Fin m → ℂ) (ψ : Fin m → GA D V → ℂ) (g : GA D W) :
    castDict e (∑ i, a i • ψ i) g = ∑ i, a i * castDict e (ψ i) g := by
  subst e
  simp [castDict, Finset.sum_apply]

theorem castDict_phiJ' {T : CoreJ D} {j : ℕ} {W : HSp D} {σ : T.Q.c.F →+* ℂ} (hσ : σ = T.σ₀) (h1 : T.V j σ = W)
    (h2 : T.V j T.σ₀ = W) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) (g : GA D W) :
    (h1 ▸ T.phiJ j σ a f : GA D W → ℂ) g = castDict h2 (T.phiJ j T.σ₀ a f) g := by
  subst hσ
  subst h1
  rfl

end GlobalTheory.DictionaryCast

theorem GlobalTheory.XiIntCore.supLattice_comb_of_baseInt : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (j : Fin D.R.m) (b : Bool) (hV : X.core.V ((j : ℕ) + 1) X.core.σ₀ = Wc D j) (la : HeightOneSpectrum (𝓞 X.core.Q.c.F)), (∀ x : X.core.Q.c.F, FinitePlace.mk la x ≤ 1 ↔ ∃ o : D.ntw.O i, Y.Z.ρ.eO i b o = X.core.σ₀ x) → ∀ (n : ℕ) (o : Fin n → D.ntw.O i) (ψ : Fin n → (GA D (X.core.V ((j : ℕ) + 1) X.core.σ₀) → ℂ)), (∀ k, ψ k ∈ GlobalTheory.CoverRead.baseInt X.core ((j : ℕ) + 1) X.core.σ₀ (Formalism.L2.Pj.wtA (X.geo.κ j)) (X.geo.κ j).n {la}) → ∃ (n' : ℕ) (o' : Fin n' → D.ntw.O i) (m : Fin n' → NX.FmK Y.S ((j : ℕ) + 1)), (∀ k, Subtype.val (m k) ∈ (Y.S.A ((j : ℕ) + 1)).MK) ∧ FWT.castDict hV (∑ k, Y.Z.ρ.eO i b (o k) • ψ k) = ∑ k, Y.Z.ρ.eO i b (o' k) • evW Y.YS X.geo.v₀ j (Subtype.val (m k)) := by
  intro hA hR hI D X E Y hF hP i hi j b hV la hla n o ψ hψ
  have hev : X.geo.fw.Evaluates := X.geo.fw.evaluates_of_lUnif X.unif
  have hσ : FWT.res X.core (sg0 D X.A3.A) = X.core.σ₀ := by
    rw [show sg0 D X.A3.A = D.what₂.embLL from sgAt_mk _ X.R.hv0]
    exact FWT.res_embLL X.core X.geo.fw.alg_eq X.geo.fw.laws.pins.2.2.1
  have hV' : X.core.V ((j : ℕ) + 1) (FWT.res X.core (sg0 D X.A3.A)) = Wc D j := by rw [hσ]; exact hV
  have hlast : (X.geo.κ j).LastPos := fun τ k hk => by
    rw [(X.geo.fw.kap j τ).1 k]; exact GlobalTheory.LiftWeight.kapTop_lastPos D j τ k hk
  have hinR : Formalism.L2.Pj.InR D ((j : ℕ) + 1) := ⟨Nat.le_add_left _ _, j.2⟩
  have key : ∀ k, ∃ (o'' : D.ntw.O i) (m : NX.FmK Y.S ((j : ℕ) + 1)), Subtype.val m ∈ (Y.S.A ((j : ℕ) + 1)).MK ∧
      FWT.castDict hV (ψ k) = Y.Z.ρ.eO i b o'' • evW Y.YS X.geo.v₀ j (Subtype.val m) := by
    intro k
    obtain ⟨f, ⟨hsec, hhol, hint⟩, hfk⟩ := hψ k
    have hcu := GlobalTheory.CuspAllEmb.mem_cuspA_of_rdU_mem_holSub0 D X.core X.geo.fw.laws _ hinR (X.geo.κ j) hlast f hsec hhol
    let fc : FWT.Cu X.core X.geo.κ j := ⟨f, hcu⟩
    have hball : ∀ y : (X.R.FW j).Pt la, (X.R.FW j).nrm la y (X.geo.fw.e j fc) ≤ 1 := fun y => by
      rw [X.geo.fw.nrm_eq]
      exact (X.core.nrmM_le_one_iff _ la _ _).2 (hint la rfl _ (X.geo.fw.pt j la y).2)
    obtain ⟨s, hs, hsM⟩ := GlobalTheory.supLattice_localisation_of_unitBall _ _ _ _ _ (X.R.FW j) (X.integral j).2.1.2 la _ hball
    set w := X.geo.fw.e j fc with hw
    have hx₀ : evW Y.YS X.geo.v₀ j ((Y.YS.fi j).e.symm (w : Fin (X.R.nW j) → D.what₂.LL)) =
        FWT.phiC X.core hV' (Formalism.L2.Pj.wtA (X.geo.κ j)) f := by
      refine Eq.trans ?_ (hev j (sg0 D X.A3.A) (by rw [hσ]; exact X.core.toCore.good_σ₀) hV' fc)
      simp only [evW, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [LinearEquiv.apply_symm_apply]
      rfl
    have hsm : s • (w : Fin (X.R.nW j) → D.what₂.LL) =
        algebraMap X.core.Q.c.F D.what₂.LL (s : X.core.Q.c.F) • (w : Fin (X.R.nW j) → D.what₂.LL) := by
      rw [algebraMap_smul]
      exact (algebraMap_smul X.core.Q.c.F s _).symm
    let m : NX.FmK Y.S ((j : ℕ) + 1) := ⟨(Y.YS.fi j).e.symm (s • (w : Fin (X.R.nW j) → D.what₂.LL)),
      ((Y.YS.fi j).wk _).2 (by rw [LinearEquiv.apply_symm_apply]; exact hsM.fst)⟩
    have hmK : Subtype.val m ∈ (Y.S.A ((j : ℕ) + 1)).MK :=
      ((Y.YS.fi j).mkK _).2 (by rw [LinearEquiv.apply_symm_apply]; exact hsM)
    have hsσ : sg0 D X.A3.A (algebraMap X.core.Q.c.F D.what₂.LL (s : X.core.Q.c.F)) = X.core.σ₀ (s : X.core.Q.c.F) :=
      congrArg (fun τ : X.core.Q.c.F →+* ℂ => τ (s : X.core.Q.c.F)) hσ
    have hevm : evW Y.YS X.geo.v₀ j (Subtype.val m) =
        X.core.σ₀ (s : X.core.Q.c.F) • evW Y.YS X.geo.v₀ j ((Y.YS.fi j).e.symm (w : Fin (X.R.nW j) → D.what₂.LL)) := by
      change evW Y.YS X.geo.v₀ j ((Y.YS.fi j).e.symm (s • (w : Fin (X.R.nW j) → D.what₂.LL))) = _
      rw [hsm, LinearEquiv.map_smul, GlobalTheory.DictionaryCast.evW_smul, hsσ]
    have hs0 : (s : X.core.Q.c.F) ≠ 0 := fun h => hs (by
      rw [show s = 0 from RingOfIntegers.coe_eq_zero_iff.1 h]; exact la.asIdeal.zero_mem)
    have hinv : FinitePlace.mk la ((s : X.core.Q.c.F)⁻¹) ≤ 1 := by
      rw [map_inv₀, FinitePlace.mk_apply, (FinitePlace.norm_eq_one_iff_notMem X.core.Q.c.F la s).mpr hs, inv_one]
    obtain ⟨o'', ho''⟩ := (hla _).1 hinv
    refine ⟨o'', m, hmK, ?_⟩
    have hc : FWT.castDict hV (ψ k) = FWT.phiC X.core hV' (Formalism.L2.Pj.wtA (X.geo.κ j)) f := by
      rw [← hfk]
      funext g
      exact (GlobalTheory.DictionaryCast.castDict_phiJ' hσ hV' hV _ _ g).symm
    rw [hc, ← hx₀, hevm, ho'', smul_smul, map_inv₀, inv_mul_cancel₀ ((map_ne_zero _).2 hs0), one_smul]
  choose o'' m hm he using key
  refine ⟨n, fun k => o k * o'' k, m, hm, ?_⟩
  funext g
  rw [GlobalTheory.DictionaryCast.castDict_sum_smul', Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [he k]
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesIntegralCoreSupLatticeCombination
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

theorem GlobalTheory.XiIntCore.xi_int_core : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (j : Fin D.R.m) b s h, Y.Z.ρ.IsDatum i j b s h 0 → ∃ u : ℂ, u ≠ 0 ∧ ∀ P ∈ (Y.Z.ρ.B i j b).valSpace, ∀ F : VV ↥D.LL0 (Y.Z.ρ.B i j b).w.lam, harmFn (Wc D j).rank (Y.Z.ρ.B i j b).w (Y.Z.ρ.B i j b).F.BS P = coefFn (Formalism.L2.Host.embLL0 D) (Y.Z.ρ.B i j b).w.lam (F : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank) → ∃ c : ℕ, ∀ Q M, InRange D.ntw i Q → (∀ v ∈ Q, ((normProd s : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) → ∀ a, ∃ (n : ℕ) (o : Fin n → D.ntw.O i) (m : Fin n → NX.FmK Y.S ((j : ℕ) + 1)), (∀ k, Subtype.val (m k) ∈ (Y.S.A ((j : ℕ) + 1)).MK) ∧ (((D.ntw.l i : ℕ) : ℂ) ^ c * u) • Y.Z.ρ.xi i j b D.nexp Q M h P a = ∑ k, Y.Z.ρ.eO i b (o k) • evW Y.YS X.geo.v₀ j (Subtype.val (m k)) := by
  intro hAR hSR hSI D X E Y hF hFP i hi j b s h hd
  obtain ⟨u, hu, hA⟩ := GlobalTheory.T.universal_series_coefficients_integral_core_forms hAR hSR hSI D X E Y hF hFP hF.split i hi j b s h hd
  refine ⟨u, hu, fun P hP F hPF => ?_⟩
  obtain ⟨c, hc⟩ := hA P hP F hPF
  refine ⟨c, fun Q M hQ hs a => ?_⟩
  obtain ⟨la, hla, n, o, ψ, hψ, he⟩ := hc Q M hQ hs a (X.geo.fw.laws.spaceW _ ⟨Nat.le_add_left _ _, j.2⟩ _ X.core.toCore.good_σ₀)
  obtain ⟨n', o', m, hm, he'⟩ := GlobalTheory.XiIntCore.supLattice_comb_of_baseInt hAR hSR hSI D X E Y hF hFP i hi j b _ la hla n o ψ hψ
  exact ⟨n', o', m, hm, he.trans he'⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesIntegralCoreSupLatticeCombinationStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeries_integral_core_supLattice_combination : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (j : Fin D.R.m) b s h, Y.Z.ρ.IsDatum i j b s h 0 → ∃ u : ℂ, u ≠ 0 ∧ ∀ P ∈ (Y.Z.ρ.B i j b).valSpace, ∀ F : VV ↥D.LL0 (Y.Z.ρ.B i j b).w.lam, harmFn (Wc D j).rank (Y.Z.ρ.B i j b).w (Y.Z.ρ.B i j b).F.BS P = coefFn (Formalism.L2.Host.embLL0 D) (Y.Z.ρ.B i j b).w.lam (F : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank) → ∃ c : ℕ, ∀ Q M, InRange D.ntw i Q → (∀ v ∈ Q, ((normProd s : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) → ∀ a, ∃ (n : ℕ) (o : Fin n → D.ntw.O i) (m : Fin n → NX.FmK Y.S ((j : ℕ) + 1)), (∀ k, Subtype.val (m k) ∈ (Y.S.A ((j : ℕ) + 1)).MK) ∧ (((D.ntw.l i : ℕ) : ℂ) ^ c * u) • Y.Z.ρ.xi i j b D.nexp Q M h P a = ∑ k, Y.Z.ρ.eO i b (o k) • evW Y.YS X.geo.v₀ j (Subtype.val (m k)) := by
  first | exact @GlobalTheory.XiIntCore.xi_int_core | exact GlobalTheory.XiIntCore.xi_int_core | (intros; apply GlobalTheory.XiIntCore.xi_int_core <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarmonicPolysReachSmallFieldCoefficientFunctions
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarmonicPolysReachSmallFieldCoefficientFunctions
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IntExpOnto

theorem exists_harm_complex {D : D7} (m n : ℕ) (w : GlobalTheory.ExportSeries.Weight D n) (B : GLR D n) (hw : w.Good) (hm : ∀ τ, w.p τ + w.q τ ≤ m)
    (F : Pol ℂ D.what₂.Tau n) (hF : F ∈ VV ℂ w.lam) :
    ∃ P ∈ harm m w B, harmFn m w B P = coefFn (RingHom.id ℂ) w.lam F := by
  obtain ⟨s, hs⟩ := GlobalTheory.ExportSeries.DeltaExtremal.harmFn_delta D m n w B hw hm
  have hs0 : ((s : ℤ) : ℂ) ≠ 0 := by exact_mod_cast s.ne_zero
  have key : ∀ u : GLR D n, harmFn m w B (fockGL m w B u (w.delta m)) =
      ((s : ℤ) : ℂ) • Onto.coefLin w.lam (actP w.lam (invTrK (u * B)) (ten fun τ => extremal ℂ n (w.lam τ))) := fun u => by
    funext x
    rw [harmFn_fockGL, hs, Pi.smul_apply, smul_eq_mul]
    congr 1
    change _ = coefFn _ _ _ _
    rw [Onto.coefFn_actP, _root_.mul_inv_rev, mul_assoc]
  have hle : (VV ℂ w.lam).map (Onto.coefLin w.lam) ≤ (harm m w B).map (harmFn m w B) := by
    rw [GlobalTheory.OrbitSpan.VV_eq_span_orbit, harm, Submodule.map_span, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    have h2 := key (invTrK g * B⁻¹)
    rw [inv_mul_cancel_right, Onto.invTrK_invTrK] at h2
    refine (Submodule.smul_mem_iff _ hs0).1 ?_
    beta_reduce
    rw [← h2]
    exact Submodule.subset_span ⟨_, ⟨_, rfl⟩, rfl⟩
  exact hle ⟨F, hF, rfl⟩

theorem exists_harm {D : D7} (m n : ℕ) (w : GlobalTheory.ExportSeries.Weight D n) (B : GLR D n) (hw : w.Good) (hm : ∀ τ, w.p τ + w.q τ ≤ m)
    {K : Type} [Field K] [CharZero K] (σ : K →+* ℂ) (F : VV K w.lam) :
    ∃ P ∈ harm m w B, harmFn m w B P = coefFn σ w.lam (F : Pol K D.what₂.Tau n) := by
  obtain ⟨P, hP, e⟩ := exists_harm_complex m n w B hw hm (MvPolynomial.map σ F.1) (GlobalTheory.Proof.TensorMapDescent.map_mem_VV _ _ _ F.2)
  refine ⟨P, hP, e.trans (funext fun x => ?_)⟩
  rw [coefFn, coefFn, MvPolynomial.eval₂Hom_map_hom, RingHom.id_comp]

theorem onto : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (j : Fin D.R.m) b (F : VV ↥D.LL0 (Y.Z.ρ.B i j b).w.lam), ∃ P ∈ (Y.Z.ρ.B i j b).valSpace, harmFn (Wc D j).rank (Y.Z.ρ.B i j b).w (Y.Z.ρ.B i j b).F.BS P = coefFn (Formalism.L2.Host.embLL0 D) (Y.Z.ρ.B i j b).w.lam (F : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank) := by
  intro _ _ _ D X E Y _ _ i _ j b F
  have hB := Y.Z.good.base i j b
  refine exists_harm _ _ _ _ hB.wt (fun τ => ?_) _ F
  have h1 := hB.sig τ
  have h2 := Formalism.BasicNotions.sig_sum _ hB.sigOK (tauE D τ)
  rw [← h1] at h2
  exact h2.le

end GlobalTheory.IntExpOnto
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarmonicPolysReachSmallFieldCoefficientFunctionsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonic_polys_reach_small_field_coefficient_functions : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (j : Fin D.R.m) b (F : VV ↥D.LL0 (Y.Z.ρ.B i j b).w.lam), ∃ P ∈ (Y.Z.ρ.B i j b).valSpace, harmFn (Wc D j).rank (Y.Z.ρ.B i j b).w (Y.Z.ρ.B i j b).F.BS P = coefFn (Formalism.L2.Host.embLL0 D) (Y.Z.ρ.B i j b).w.lam (F : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank) := by
  first | exact @GlobalTheory.IntExpOnto.onto | exact GlobalTheory.IntExpOnto.onto | (intros; apply GlobalTheory.IntExpOnto.onto <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.XiIntComb

variable {D : D7} {X : RealSide D} {E : IntegralHeckeForms.XD D}

def Good (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (s : Finset (Pl D.host.E)) (h : GA D (Vc D j)) (u : ℂ)
    (P : PolF D (Wc D j).rank (Vc D j).rank) : Prop :=
  ∃ c : ℕ, ∀ Q M, InRange D.ntw i Q → (∀ v ∈ Q, ((normProd s : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) → ∀ a,
    ∃ (n : ℕ) (o : Fin n → D.ntw.O i) (m : Fin n → NX.FmK Y.S ((j : ℕ) + 1)), (∀ k, Subtype.val (m k) ∈ (Y.S.A ((j : ℕ) + 1)).MK) ∧
      (((D.ntw.l i : ℕ) : ℂ) ^ c * u) • Y.Z.ρ.xi i j b D.nexp Q M h P a =
        ∑ k, Y.Z.ρ.eO i b (o k) • evW Y.YS X.geo.v₀ j (Subtype.val (m k))

variable (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (s : Finset (Pl D.host.E)) (h : GA D (Vc D j)) (u : ℂ)

theorem xi_eq_lin (Q : Finset (Pl D.host.E)) (M : ℕ) (P : PolF D (Wc D j).rank (Vc D j).rank) (a) :
    Y.Z.ρ.xi i j b D.nexp Q M h P a = xiLin Y.Z.ρ D.nexp i j b Q M h a P := rfl

theorem good_zero : Good Y i j b s h u 0 := by
  refine ⟨0, fun Q M _ _ a => ⟨0, Fin.elim0, Fin.elim0, fun k => k.elim0, ?_⟩⟩
  rw [xi_eq_lin, map_zero, smul_zero, Finset.univ_eq_empty, Finset.sum_empty]

theorem good_smul {P : PolF D (Wc D j).rank (Vc D j).rank} (hP : Good Y i j b s h u P) (o : D.ntw.O i) :
    Good Y i j b s h u (Y.Z.ρ.eO i b o • P) := by
  obtain ⟨c, hc⟩ := hP
  refine ⟨c, fun Q M hQ hs a => ?_⟩
  obtain ⟨n, o', m, hm, he⟩ := hc Q M hQ hs a
  refine ⟨n, fun k => o * o' k, m, hm, ?_⟩
  rw [xi_eq_lin, map_smul, smul_comm, ← xi_eq_lin, he, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_smul, map_mul]

theorem good_add {P P' : PolF D (Wc D j).rank (Vc D j).rank} (hP : Good Y i j b s h u P) (hP' : Good Y i j b s h u P') :
    Good Y i j b s h u (P + P') := by
  obtain ⟨c, hc⟩ := hP
  obtain ⟨c', hc'⟩ := hP'
  refine ⟨c + c', fun Q M hQ hs a => ?_⟩
  obtain ⟨n, o, m, hm, he⟩ := hc Q M hQ hs a
  obtain ⟨n', o', m', hm', he'⟩ := hc' Q M hQ hs a
  have hl : Y.Z.ρ.eO i b ((D.ntw.l i : ℕ) : D.ntw.O i) = ((D.ntw.l i : ℕ) : ℂ) := map_natCast _ _
  refine ⟨n + n', Fin.append (fun k => ((D.ntw.l i : ℕ) : D.ntw.O i) ^ c' * o k)
    (fun k => ((D.ntw.l i : ℕ) : D.ntw.O i) ^ c * o' k), Fin.append m m', fun k => ?_, ?_⟩
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) k
    · rw [Fin.append_left]; exact hm k
    · rw [Fin.append_right]; exact hm' k
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [xi_eq_lin, map_add (f := _), smul_add, ← xi_eq_lin, ← xi_eq_lin]
    congr 1
    · rw [show (((D.ntw.l i : ℕ) : ℂ) ^ (c + c') * u) = ((D.ntw.l i : ℕ) : ℂ) ^ c' * (((D.ntw.l i : ℕ) : ℂ) ^ c * u) by ring,
        mul_smul, he, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_smul, map_mul, map_pow, hl]
    · rw [show (((D.ntw.l i : ℕ) : ℂ) ^ (c + c') * u) = ((D.ntw.l i : ℕ) : ℂ) ^ c * (((D.ntw.l i : ℕ) : ℂ) ^ c' * u) by ring,
        mul_smul, he', Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_smul, map_mul, map_pow, hl]

end GlobalTheory.XiIntComb

open GlobalTheory.XiIntComb in
theorem GlobalTheory.XiIntComb.xi_int_comb : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (j : Fin D.R.m) b s h P, Y.Z.ρ.IsDatum i j b s h P → ∃ (u : ℂ) (c : ℕ), u ≠ 0 ∧ ∀ Q M, InRange D.ntw i Q → (∀ v ∈ Q, ((normProd s : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) → ∀ a, ∃ (n : ℕ) (o : Fin n → D.ntw.O i) (m : Fin n → NX.FmK Y.S ((j : ℕ) + 1)), (∀ k, Subtype.val (m k) ∈ (Y.S.A ((j : ℕ) + 1)).MK) ∧ (((D.ntw.l i : ℕ) : ℂ) ^ c * u) • Y.Z.ρ.xi i j b D.nexp Q M h P a = ∑ k, Y.Z.ρ.eO i b (o k) • evW Y.YS X.geo.v₀ j (Subtype.val (m k)) := by
  intro hAR hSR hSI D X E Y hF hFP i hi j b s h P hd
  obtain ⟨u, hu0, hgen⟩ := GlobalTheory.T.thetaSeries_integral_core_supLattice_combination hAR hSR hSI D X E Y hF hFP i hi j b s h ⟨hd.split, hd.off, hd.fin, hd.supp, zero_mem _⟩
  have hB := Y.Z.good.base i j b
  have hm : ∀ τ, (Y.Z.ρ.B i j b).w.p τ + (Y.Z.ρ.B i j b).w.q τ ≤ (Wc D j).rank := fun τ => by
    have h1 := hB.sig τ
    have h2 := Formalism.BasicNotions.sig_sum _ hB.sigOK (tauE D τ)
    rw [← h1] at h2
    exact h2.le
  have hinj := GlobalTheory.T.harmonic_polynomial_eq_zero_of_function D _ _ _ (Y.Z.ρ.B i j b).F.BS hB.wt hm
  have key : ∀ φ ∈ coefLatFn (Formalism.L2.Host.embLL0 D) (labLL0 D) (Y.Z.ρ.eO i b).range (Y.Z.ρ.B i j b).w.lam
      ((Y.Z.ρ.B i j b).latAt (finPt _ h)), ∃ P' ∈ (Y.Z.ρ.B i j b).valSpace,
        harmFn (Wc D j).rank (Y.Z.ρ.B i j b).w (Y.Z.ρ.B i j b).F.BS P' = φ ∧ Good Y i j b s h u P' := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem _ h1 =>
      obtain ⟨F, -, rfl⟩ := h1
      obtain ⟨P', h2, h3⟩ := GlobalTheory.T.harmonic_polys_reach_small_field_coefficient_functions hAR hSR hSI D X E Y hF hFP i hi j b F
      exact ⟨P', h2, h3, hgen P' h2 F h3⟩
    | zero => exact ⟨0, zero_mem _, map_zero _, good_zero Y i j b s h u⟩
    | add _ _ _ _ h1 h2 =>
      obtain ⟨P₁, a1, rfl, g1⟩ := h1
      obtain ⟨P₂, a2, rfl, g2⟩ := h2
      exact ⟨P₁ + P₂, add_mem a1 a2, map_add _ _ _, good_add Y i j b s h u g1 g2⟩
    | smul c _ _ h1 =>
      obtain ⟨P₁, a1, rfl, g1⟩ := h1
      obtain ⟨_, o, rfl⟩ := c
      exact ⟨Y.Z.ρ.eO i b o • P₁, Submodule.smul_mem _ _ a1, map_smul _ _ _, good_smul Y i j b s h u g1 o⟩
  obtain ⟨P', h1, h2, ⟨c, hc⟩⟩ := key _ hd.mem.2
  obtain rfl : P = P' := sub_eq_zero.1 (hinj (P - P') (sub_mem hd.mem.1 h1) (by rw [map_sub, h2]; exact sub_self _))
  exact ⟨u, c, hu0, hc⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniversalSeriesCoeffBoundedInSupOfTwistSeriesSid
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
noncomputable section
namespace GlobalTheory.XiBound

theorem exists_pow_mul_mem {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] {l : O} (hl : l ∈ IsLocalRing.maximalIdeal O) (z : K) :
    ∃ (n : ℕ) (o : O), algebraMap O K o = algebraMap O K (l ^ n) * z := by
  by_cases h0 : l = 0
  · exact ⟨1, 0, by simp [h0]⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨⟨a, d⟩, hz⟩ := IsLocalization.surj (nonZeroDivisors O) z
  have hd : (d : O) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  obtain ⟨k, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hϖ
  obtain ⟨e, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
  have he : e ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hw
    exact (IsLocalRing.mem_maximalIdeal _).1 hl (hw ▸ w.isUnit)
  have hdvd : (d : O) ∣ l ^ k := by
    rw [hv, hw, mul_pow, ← pow_mul]
    exact mul_dvd_mul (Units.isUnit v).dvd (pow_dvd_pow ϖ (Nat.le_mul_of_pos_left k (Nat.pos_of_ne_zero he)))
  obtain ⟨t, ht⟩ := hdvd
  refine ⟨k, a * t, ?_⟩
  simp only at hz
  rw [ht, map_mul, map_mul, ← hz]
  ring

theorem main : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) → XiBdd Y.Z.rd := by
  intro hA hR hI D X E Y hF hP i hi j b s h P hd
  classical
  obtain ⟨u, c, hu, hK⟩ := GlobalTheory.XiIntComb.xi_int_comb hA hR hI D X E Y hF hP i hi j b s h P hd
  have hν : Y.Z.ν i j b ≠ 0 := (Y.Z.scalar i j b).ne
  have hFa : Faithful (Y.Z.rd i j b) :=
    realRd_faithful D X.Γ X.Pl0 X.I0 X.T X.A3 _ X.R X.cG Y.S Y.YS X.geo.v₀ Y.Z.ρ Y.Z.good i j b (Y.Z.ν i j b)
      hν X.unif X.char.models.HW (Y.Z.vec j) ((GlobalTheory.T.rational_datum_small_field_form_hecke_scalar_unit D X E Y).1 _ (Nat.le_add_left _ _) j.2)
  have hinj := hFa.injective
  set lam : ℂ := (Y.Z.ν i j b)⁻¹ * (((D.ntw.l i : ℕ) : ℂ) ^ c * u) with hlam

  have step : ∀ Q M, InRange D.ntw i Q → (∀ v ∈ Q, ((normProd s : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) → ∀ a x,
      Y.Z.rd i j b x = Y.Z.ρ.xi i j b D.nexp Q M h P a →
      ∃ x' ∈ D.nexp.Bsup i ((j : ℕ) + 1) b, Y.Z.rd i j b x' = lam • Y.Z.rd i j b x := by
    intro Q M hQ hs a x hx
    obtain ⟨n, o, m, hm, he⟩ := hK Q M hQ hs a
    let y : NX.Fm Y.S i ((j : ℕ) + 1) b :=
      ∑ k, ((show NX.KB Y.S i b from algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (o k)) • ((1 : NX.KB Y.S i b) ⊗ₜ[Y.S.Ks] m k) :
        NX.KB Y.S i b ⊗[Y.S.Ks] NX.FmK Y.S ((j : ℕ) + 1))
    have hy : y ∈ NX.Bsup Y.S i ((j : ℕ) + 1) b := by
      refine Submodule.sum_mem _ fun k _ => ?_
      exact (NX.Bsup Y.S i ((j : ℕ) + 1) b).smul_mem (o k) (Submodule.subset_span ⟨m k, hm k, rfl⟩)
    have hey : evK Y.YS X.geo.v₀ Y.Z.good i j b y = ∑ k, Y.Z.ρ.eO i b (o k) • evW Y.YS X.geo.v₀ j (Subtype.val (m k)) := by
      refine (map_sum (evK Y.YS X.geo.v₀ Y.Z.good i j b) (fun k => ((show NX.KB Y.S i b from algebraMap (D.ntw.O i)
        (FractionRing (D.ntw.O i)) (o k)) • ((1 : NX.KB Y.S i b) ⊗ₜ[Y.S.Ks] m k) : NX.KB Y.S i b ⊗[Y.S.Ks] NX.FmK Y.S ((j : ℕ) + 1)))
        Finset.univ).trans (Finset.sum_congr rfl fun k _ => ?_)
      rw [TensorProduct.smul_tmul', evK_tmul, smul_eq_mul, mul_one]
      rfl
    let x' := (Y.YS.eF i _ b (Nat.le_add_left _ _) j.2).symm y
    refine ⟨x', (Y.sup i _ b (Nat.le_add_left _ _) j.2 x').2 (by simp only [x', LinearEquiv.apply_symm_apply]; exact hy), ?_⟩
    change (Y.Z.ν i j b)⁻¹ • evK Y.YS X.geo.v₀ Y.Z.good i j b (Y.YS.eF i _ b (Nat.le_add_left _ _) j.2 x') = _
    rw [show Y.YS.eF i _ b (Nat.le_add_left _ _) j.2 x' = y from LinearEquiv.apply_symm_apply _ _, hey, ← he, hx, hlam,
      smul_smul]
  by_cases hex : ∃ μ : FractionRing (D.ntw.O i), Y.Z.ρ.e i b μ = lam
  · obtain ⟨μ, hμ⟩ := hex
    obtain ⟨N, o, ho⟩ := exists_pow_mul_mem (K := FractionRing (D.ntw.O i)) (D.ntw.O_l i) μ⁻¹
    refine ⟨N, fun Q M hQ hs a x hx => ?_⟩
    obtain ⟨x', hx'B, hx'⟩ := step Q M hQ hs a x hx
    have hμx : x' = μ • x := hinj (by rw [hx', map_smulₛₗ, hμ])
    by_cases hμ0 : μ = 0
    · exfalso
      rw [hμ0, map_zero, hlam] at hμ
      have hl : ((D.ntw.l i : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (D.ntw.lPrime i).out.ne_zero
      exact mul_ne_zero (inv_ne_zero hν) (mul_ne_zero (pow_ne_zero _ hl) hu) hμ.symm
    have : ((D.ntw.l i : D.ntw.O i) ^ N) • x = o • x' := by
      rw [hμx, ← algebraMap_smul (FractionRing (D.ntw.O i)) o, ← algebraMap_smul (FractionRing (D.ntw.O i)) ((D.ntw.l i : D.ntw.O i) ^ N),
        smul_smul, ho, mul_assoc, inv_mul_cancel₀ hμ0, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ hx'B
  · refine ⟨0, fun Q M hQ hs a x hx => ?_⟩
    obtain ⟨x', -, hx'⟩ := step Q M hQ hs a x hx
    by_cases h0 : Y.Z.rd i j b x = 0
    · rw [hinj (h0.trans (map_zero _).symm), smul_zero]
      exact Submodule.zero_mem _
    · exact absurd (hFa.mem_range_of_smul h0 ⟨x, rfl⟩ ⟨x', hx'⟩) hex

end GlobalTheory.XiBound
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniversalSeriesCoeffBoundedInSupOfTwistSeriesSidStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universalSeriesCoeff_boundedInSup_of_twistSeriesSideData : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) → XiBdd Y.Z.rd := by
  first | exact @GlobalTheory.XiBound.main | exact GlobalTheory.XiBound.main | (intros; apply GlobalTheory.XiBound.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalThetaSeriesOfTwistSeriesSideData
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalThetaSeriesOfTwistSeriesSideData
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatBundles

theorem ratHyp {D : D7} (X : RealSide D) {E : IntegralHeckeForms.XD D} (Y : SerSide X E) (hF : FieldOk X)
    (hP : ∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) {i : D.ntw.Tw} (hi : D.ntw.NonzeroIndexPlace i)
    (j : Fin D.R.m) : GlobalTheory.BigOn.Exp.RatHyp X.core X.R X.F.lv2 X.geo.κ X.geo.v₀ X.geo.O i j (X.space_eq j) :=
  have hC := X.char
  { size := X.size
    host := X.host
    std := X.std j
    laws := X.geo.fw.laws
    core := ⟨hC.lev, hC.grp, hC.fam, hC.models, hC.chain, hC.thP⟩
    unif := X.unif
    fw := ⟨X.geo.fw⟩
    tieIn := ⟨X.geo.fw.laws, X.geo.fw.alg_eq, X.geo.fw.kap, X.geo.fw.hv₀, X.geo.fw.chiR, X.geo.fw.x0⟩
    io := GlobalTheory.IoExtremal.ioExt D _ _ _ _ _ X.R.toRealDat hC.lev hC.fam hC.models hC.thP
    guard := X.guard
    fin := X.finT
    pins := X.geo.pins j
    phase := by
      convert X.geo.phase j X.unif using 2
      rename_i k
      rw [X.phs k]
      simp
    frame := hP j _
    galois := hF.galois
    small := ⟨hF.vals, hF.ray, hF.roots⟩
    inUse := hi
    low := Y.low i }

theorem levelOf {D : D7} {X : RealSide D} {E : IntegralHeckeForms.XD D} (Y : SerSide X E) : Y.Z.ρ.LevelOf D.nexp :=
  ⟨fun i j b => (Y.Z.tie i j b).U_eq, fun i j b => (Y.Z.tie i j b).psiU_eq⟩

theorem rat_of_split (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hS : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat) {D : D7} (X : RealSide D) {E : IntegralHeckeForms.XD D}
    (Y : SerSide X E) (hF : FieldOk X) (hsp : D.host.cls D.host.pde = .splitK ∧ D.host.cls D.host.pde' = .splitK)
    (hP : ∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) {i : D.ntw.Tw} (hi : D.ntw.NonzeroIndexPlace i)
    (j : Fin D.R.m) (b : Bool) : RatRow Y.YS X.geo.v₀ Y.Z.good i j b :=
  GlobalTheory.T.thetaSeries_base_twisted_universal_rational hA hA.rayClassFieldSt (GlobalTheory.SerStd.seriesRatS_of hS) D X.Γ X.Pl0 X.I0 X.T X.A3 X.core X.R X.cG Y.S Y.YS
    X.F.lv2 X.geo.κ X.geo.v₀ X.geo.O Y.Z.ρ Y.Z.good i j b (X.space_eq j) Y.Z.pin (levelOf Y) hsp (ratHyp X Y hF hP hi j)

theorem rat_bundles : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j b, RatRow Y.YS X.geo.v₀ Y.Z.good i j b :=
  fun hA hS _ X _ Y hF hP _ hi j b => rat_of_split hA hS X Y hF hF.split hP hi j b

end GlobalTheory.RatBundles
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalThetaSeriesOfTwistSeriesSideDataStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_thetaSeries_of_twistSeriesSideData : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j b, RatRow Y.YS X.geo.v₀ Y.Z.good i j b := by
  first | exact @GlobalTheory.RatBundles.rat_bundles | exact GlobalTheory.RatBundles.rat_bundles | (intros; apply GlobalTheory.RatBundles.rat_bundles <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsScalarMove
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharacterisationTransferMovedReadings
set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.Unframe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def rhoEquiv {K M G : Type} [Field K] [AddCommGroup M] [Module K M] [Group G] (ρ : G →* (M →ₗ[K] M)) (g : G) : M ≃ₗ[K] M :=
  LinearEquiv.ofLinearMap (ρ g) (ρ g⁻¹) (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)

theorem rho_rho {K M G : Type} [Field K] [AddCommGroup M] [Module K M] [Group G] (ρ : G →* (M →ₗ[K] M)) (g g' : G) (x : M) :
    ρ g (ρ g' x) = ρ (g * g') x := by rw [map_mul]; rfl

theorem rho_inv {K M G : Type} [Field K] [AddCommGroup M] [Module K M] [Group G] (ρ : G →* (M →ₗ[K] M)) (g : G) (x : M) :
    ρ g (ρ g⁻¹ x) = x := by rw [rho_rho, mul_inv_cancel, map_one]; rfl

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  (Rl : RealDat3 D A3 Ks) (w : Fin D.R.m → (D.what₂.LL →+* ℂ) → Γ)

abbrev realDatMovedReadingsKeepScalars : RealDat3 D A3 Ks := ⟨moveR Rl.toRealDat w, Rl.plI, Rl.SF, Rl.phs, Rl.lam3⟩

variable (kap : ℝ) (lam : type_of% Rl.lam3)

abbrev fullHeckeRealDatMovedReadings : RealDat3 D A3 Ks := (realDatMovedReadingsKeepScalars Rl w).updS kap lam

variable {Rl w kap lam}


set_option maxHeartbeats 4000000 in
theorem heckeCharacterisation_transfer_movedReadings {F : Face3 D A3} (h : Rl.Char3 F) (hs : (fullHeckeRealDatMovedReadings Rl w kap lam).IsScal F) : (fullHeckeRealDatMovedReadings Rl w kap lam).Char3 F := by
  obtain ⟨h1, h2, h5, hi, h6, h7, h8, f1, f2, f3, -, ht, hp, ha⟩ := h
  refine ⟨h1, ⟨h2.1, h2.2, h2.3, h2.4, h2.5⟩, ?_, ⟨hi.1, hi.2, hi.3, hi.4, hi.5⟩, ?_, ?_, ?_, f1, f2, f3, hs,
    ⟨ht.1, ht.2, ht.3, ht.4, ht.5⟩, fun i => ⟨(hp i).1, fun hc x => ?_⟩, ha⟩
  · exact ⟨h5.1, h5.2, h5.3, h5.4, h5.5, h5.6, h5.7, h5.8⟩
  · exact ⟨h6.1, h6.2, h6.3, h6.4, h6.5, h6.6, h6.7, h6.8, h6.9, h6.10, h6.11, h6.12, h6.13, h6.14, h6.15, h6.16, h6.17,
      h6.18, h6.19, h6.20, h6.21⟩
  · exact ⟨h7.1, h7.2, h7.3, h7.4, h7.5, h7.6, h7.7, h7.8, h7.9, h7.10, h7.11⟩
  · exact ⟨h8.1, h8.2, h8.3, h8.4, h8.5, h8.6, h8.7⟩
  · obtain ⟨c, hc1, hc2⟩ := hc
    obtain ⟨y, hy⟩ := (hp i).2 ⟨c, hc1, fun x => (hc2 x).elim fun y hy => ⟨(Rl.FW i).ρ (w i (sg0 D A3.A)) y, hy⟩⟩ x
    exact ⟨(Rl.FW i).ρ (w i (sg0 D A3.A))⁻¹ y, (congrArg ((Rl.FW i).j (sg0 D A3.A)) (rho_inv _ _ y)).trans hy⟩

variable {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) (w)

abbrev moveS : NX.RatDat D.ntw :=
  { S with
    A := fun n => moveForms (S.A n) fun σ =>
      (YS.fi (NX.idxOf D n)).eG.symm (w (NX.idxOf D n) σ * (w (NX.idxOf D n) (sg0 D A3.A))⁻¹) }

variable {w} (kap lam) (hw : ∀ i σ, w i σ ∈ Subgroup.center Γ) (hst : ∀ i, (Rl.FW i).MKStable)

def moveIso (i : Fin D.R.m) : NX.FormsIso ((moveS w YS).A ((i : ℕ) + 1)) ((fullHeckeRealDatMovedReadings Rl w kap lam).FW i) where
  eK := (YS.fi i).eK
  eK_LL := (YS.fi i).eK_LL
  e := (YS.fi i).e.trans (rhoEquiv (Rl.FW i).ρ (w i (sg0 D A3.A))⁻¹)
  eG := (YS.fi i).eG
  eW := (YS.fi i).eW
  wk x := ((YS.fi i).wk x).trans ⟨(hst i _ _).1, fun h => by
    rw [← rho_inv (Rl.FW i).ρ (w i (sg0 D A3.A)) ((YS.fi i).e x)]
    exact (hst i _ _).1 h⟩
  mkK x := ((YS.fi i).mkK x).trans ⟨(hst i _ _).2, fun h => by
    rw [← rho_inv (Rl.FW i).ρ (w i (sg0 D A3.A)) ((YS.fi i).e x)]
    exact (hst i _ _).2 h⟩
  rho g x := by
    change (Rl.FW i).ρ (w i (sg0 D A3.A))⁻¹ ((YS.fi i).e ((S.A _).ρ g x)) =
      (Rl.FW i).ρ ((YS.fi i).eG g) ((Rl.FW i).ρ (w i (sg0 D A3.A))⁻¹ ((YS.fi i).e x))
    rw [(YS.fi i).rho, rho_rho, rho_rho, Subgroup.mem_center_iff.1 (inv_mem (hw i _))]
  chi := (YS.fi i).chi
  j σ x := by
    change (Rl.FW i).j σ ((Rl.FW i).ρ (w i σ) ((Rl.FW i).ρ (w i (sg0 D A3.A))⁻¹ ((YS.fi i).e x))) =
      (YS.fi i).eW σ ((S.A _).j σ ((S.A _).ρ ((YS.fi (NX.idxOf D ((i : ℕ) + 1))).eG.symm
        (w (NX.idxOf D ((i : ℕ) + 1)) σ * (w (NX.idxOf D ((i : ℕ) + 1)) (sg0 D A3.A))⁻¹)) x))
    rw [NX.idxOf_succ, ← (YS.fi i).j, (YS.fi i).rho, MulEquiv.apply_symm_apply, rho_rho]

def moveYS : NX.NExpRealS (fullHeckeRealDatMovedReadings Rl w kap lam) cG (moveS w YS) where
  fi := moveIso kap lam YS hw hst
  geq := YS.geq
  rho := YS.rho
  chi := YS.chi
  eF := YS.eF
  bsup := YS.bsup
  act := YS.act

theorem j_moveYS (i : Fin D.R.m) (x : S.WL ((i : ℕ) + 1)) :
    ((fullHeckeRealDatMovedReadings Rl w kap lam).FW i).j (sg0 D A3.A) (((moveYS kap lam YS hw hst).fi i).e x) =
      (Rl.FW i).j (sg0 D A3.A) ((YS.fi i).e x) :=
  congrArg ((Rl.FW i).j (sg0 D A3.A)) (rho_inv _ _ _)

def moveH (H : NX.NExpRealH Rl cG S YS) : NX.NExpRealH (fullHeckeRealDatMovedReadings Rl w kap lam) cG (moveS w YS) (moveYS kap lam YS hw hst) where
  hL := H.hL
  hs := H.hs
  cHk := H.cHk
  cHk_zero := H.cHk_zero
  cHk_unit := H.cHk_unit
  cHk_pow := H.cHk_pow
  hkEq := H.hkEq

theorem reads_move {hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)} (h : GlobalTheory.ExportPin.Reads Rl cG S YS hL) :
    GlobalTheory.ExportPin.Reads (fullHeckeRealDatMovedReadings Rl w kap lam) cG (moveS w YS) (moveYS kap lam YS hw hst) hL := by
  intro i k P h1 h2 h3 α R h4 h5 x
  rw [j_moveYS, j_moveYS]
  exact h i k P h1 h2 h3 α R h4 h5 x

variable (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)

theorem realRd_move {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (ν : ℂ) :
    realRd (moveYS kap lam YS hw hst) v₀ hρ i j b ν = realRd YS v₀ hρ i j b ν := by
  have key : ∀ x : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1),
      evK (moveYS kap lam YS hw hst) v₀ hρ i j b x = evK YS v₀ hρ i j b x := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => exact (map_zero _).trans (map_zero _).symm
    | add x y hx hy => exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)
    | tmul a f =>
      exact congrArg (fun y => ρ.e i b a • (Rl.HW j (sg0 D A3.A)).e y (v₀ j _)) (j_moveYS kap lam YS hw hst j (Subtype.val f))
  exact LinearMap.ext fun f => congrArg (ν⁻¹ • ·) (key _)

theorem ratRow_move {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) :
    RatRow (moveYS kap lam YS hw hst) v₀ hρ i j b ↔ RatRow YS v₀ hρ i j b :=
  exists_congr fun ν => and_congr Iff.rfl (by rw [realRd_move])

variable {YS v₀}

theorem rd_move (Z : ExportTie YS v₀) :
    (fun i j b => realRd (moveYS kap lam YS hw hst) v₀ Z.good i j b (Z.ν i j b) : Rds D.nexp Z.ρ) = Z.rd :=
  funext fun i => funext fun j => funext fun b => realRd_move kap lam YS hw hst v₀ Z.good i j b _

end GlobalTheory.Unframe

end
end

set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.Unframe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {w : Fin D.R.m → (D.what₂.LL →+* ℂ) → Γ} (kap : ℝ) (lam : type_of% Rl.lam3)
  {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} {YS : NX.NExpRealS Rl cG S}
  (hw : ∀ i σ, w i σ ∈ Subgroup.center Γ) (hst : ∀ i, (Rl.FW i).MKStable)
  {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}

theorem pin_move {ρ : Setup D.ntw} (h : RealPin Rl cG ρ) : RealPin (fullHeckeRealDatMovedReadings Rl w kap lam) cG ρ :=
  ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11, h.12, h.13, h.14, h.15, h.16, h.17, h.18⟩

theorem isNorm_move {j : Fin D.R.m} (B : Base (Vc D j) (Wc D j)) (ν : ℂ) :
    IsNorm (fullHeckeRealDatMovedReadings Rl w kap lam) v₀ B ν ↔ IsNorm Rl v₀ B ν := Iff.rfl

theorem vec_move {j : Fin D.R.m} (h : FWT.IsChosenExtremalVector Rl.toRealDat j (sg0 D A3.A) (v₀ j _)) :
    FWT.IsChosenExtremalVector (fullHeckeRealDatMovedReadings Rl w kap lam).toRealDat j (sg0 D A3.A) (v₀ j _) := h

theorem isScalar_move {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) {ν : ℂ}
    (h : IsScalar YS v₀ hρ i j b ν) : IsScalar (Rl := fullHeckeRealDatMovedReadings Rl w kap lam) (cG := cG) (S := moveS w YS) (moveYS kap lam YS hw hst) v₀ hρ i j b ν :=
  ⟨h.ne, fun h' => (isNorm_move kap lam _ _).2 (h.norm (h'.imp fun _ => (isNorm_move kap lam _ _).1)), fun h' =>
    (congrArg (Rat hρ) (realRd_move kap lam YS hw hst v₀ hρ i j b ν)).mpr
      (h.rat ((ratRow_move kap lam YS hw hst v₀ hρ i j b).1 h'))⟩

def moveZ (Z : ExportTie YS v₀) : ExportTie (Rl := fullHeckeRealDatMovedReadings Rl w kap lam) (cG := cG) (S := moveS w YS) (moveYS kap lam YS hw hst) v₀ where
  ρ := Z.ρ
  good := Z.good
  pin := pin_move kap lam Z.pin
  vec := fun j => vec_move kap lam (Z.vec j)
  ν := Z.ν
  scalar := fun i j b => isScalar_move kap lam hw hst Z.good i j b (Z.scalar i j b)
  tie := cast (congrArg (Comparison₂ Z.good (Y := D.nexp)) (rd_move kap lam hw hst Z).symm) Z.tie
  hecke := fun i j b => (congrArg HeckeTie (realRd_move kap lam YS hw hst v₀ Z.good i j b _)).mpr (Z.hecke i j b)
  univ := Z.univ

end GlobalTheory.Unframe

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesRationalityAndCoefficientBound
set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.Unframe

open GlobalTheory.TwInputs GlobalTheory.RealGeo _root_.Formalism.L2.Pj Formalism.IndefR.FWT

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}


set_option maxHeartbeats 8000000 in
theorem exists_framed (hP : GlobalTheory.Published.CuspRapidDecay) (X : RealSide D) {E : IntegralHeckeForms.XD D} (Y : SerSide X E) (hF : FieldOk X) :
    ∃ (X' : RealSide D) (Y' : SerSide X' E), FieldOk X' ∧
      (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X'.core X'.R.toRealDat j X'.core.σ₀ hV) ∧
      (∀ i j b, RatRow Y'.YS X'.geo.v₀ Y'.Z.good i j b → RatRow Y.YS X.geo.v₀ Y.Z.good i j b) ∧
      (XiBdd Y'.Z.rd → XiBdd Y.Z.rd) := by
  have hC : GlobalTheory.Core5 X.R.toRealDat X.F.lv2 := ⟨X.char.lev, X.char.grp, X.char.fam, X.char.models, X.char.thP⟩
  obtain ⟨c', w, hw, hfr, B, hB⟩ := exists_framed_half hP X.size hC X.geo X.unif X.inGeo
  obtain ⟨kap, lam, hs⟩ := scalars_exist (F := X.F) (realDatMovedReadingsKeepScalars X.R w)
  have hch : (fullHeckeRealDatMovedReadings X.R w kap lam).Char3 X.F := heckeCharacterisation_transfer_movedReadings X.char hs
  obtain ⟨B', -, hB', -⟩ := @geoHalf_upd D X.Γ _ _ X.Pl0 X.T X.A3.A (setCE X.core c') X.alg (moveR X.R.toRealDat w) _ kap X.R.lam
    X.R.err0 B
  obtain ⟨κ, v₀, fw, bar, O, pins, rho, eqa, ct, phase⟩ := B'
  obtain rfl : v₀ = X.geo.v₀ := (eq_of_heq hB').trans hB
  let g : @GeoHalf D X.Γ _ _ X.Pl0 X.T X.A3.A (setCE X.core c') X.alg (fullHeckeRealDatMovedReadings X.R w kap lam).toRealDat fun _ => 1 :=
    @GeoHalf.mk D X.Γ _ _ X.Pl0 X.T X.A3.A (setCE X.core c') X.alg (fullHeckeRealDatMovedReadings X.R w kap lam).toRealDat _
      κ X.geo.v₀ fw bar O pins rho eqa ct phase
  have hpb : X.core.pb = X.R.C.P.pb :=
    GlobalTheory.CoverHalf.primes_eq_of_halfIs X.core.toCore X.R.toRealDat X.geo.fw.laws.toLawsM hC.lev
      ((X.geo.pins ⟨0, by have := D.R.two_le_m; omega⟩).2.tuple ()).half
  obtain ⟨hI, hU, hInt⟩ := @GlobalTheory.RealGeoIn.inGeo_and_lUnif_and_lIntegral hP D X.Γ _ _ X.Pl0 X.T X.A3.A (setCE X.core c') X.alg
    (fullHeckeRealDatMovedReadings X.R w kap lam).toRealDat _ g
    ⟨hch.lev, hch.grp.red_R, hch.grp.red_L, hch.grp.record, hch.fam, hch.models, hch.chain, hch.thP⟩ hch.grp.chiW hpb X.size
  have hst : ∀ i, (X.R.FW i).MKStable := fun i => (X.integral i).2.2
  let X' : RealSide D := @RealSide.mk D X.Γ X.grp X.fin X.Pl0 X.I0 X.T X.A3 (setCE X.core c') X.alg (fullHeckeRealDatMovedReadings X.R w kap lam) X.F X.cG g
    hch X.phs X.guard X.valKs X.idem hU hInt hI X.finT X.host X.std X.size
  let Y' : SerSide X' E :=
    { S := moveS w Y.YS
      YS := moveYS kap lam Y.YS hw hst
      sup := Y.sup
      H := moveH kap lam Y.YS hw hst Y.H
      reads := reads_move kap lam Y.YS hw hst Y.reads
      del := Y.del
      Z := moveZ kap lam hw hst Y.Z
      U_eq := Y.U_eq
      psi_eq := Y.psi_eq
      low := Y.low
      Sb := Y.Sb
      B_range := Y.B_range
      hk_emb := Y.hk_emb
      hk_split := Y.hk_split
      off := Y.off
      all := Y.all }
  refine ⟨X', Y', ⟨hF.galois, hF.star, hF.vals, hF.ray, hF.roots, hF.split⟩, hfr,
    fun i j b => (ratRow_move kap lam Y.YS hw hst X.geo.v₀ Y.Z.good i j b).1, fun h => ?_⟩
  rw [← rd_move kap lam hw hst Y.Z]
  exact h

end GlobalTheory.Unframe

section

open GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf

theorem GlobalTheory.Unframe.rat_and_xiBdd : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ i, D.ntw.NonzeroIndexPlace i → ∀ j b, RatRow Y.YS X.geo.v₀ Y.Z.good i j b) ∧ XiBdd Y.Z.rd := by
  intro hP hA hR hS D X E Y hF
  obtain ⟨X', Y', hF', hfr, h1, h2⟩ := GlobalTheory.Unframe.exists_framed hP X Y hF
  exact ⟨fun i hi j b => h1 i j b (GlobalTheory.T.exists_rational_thetaSeries_of_twistSeriesSideData hA hR D X' E Y' hF' hfr i hi j b), h2 (GlobalTheory.T.universalSeriesCoeff_boundedInSup_of_twistSeriesSideData hA hR hS D X' E Y' hF' hfr)⟩

end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesRationalityAndCoefficientBoundStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeries_rationality_and_coefficientBound : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ i, D.ntw.NonzeroIndexPlace i → ∀ j b, RatRow Y.YS X.geo.v₀ Y.Z.good i j b) ∧ XiBdd Y.Z.rd := by
  first | exact @GlobalTheory.Unframe.rat_and_xiBdd | exact GlobalTheory.Unframe.rat_and_xiBdd | (intros; apply GlobalTheory.Unframe.rat_and_xiBdd <;> assumption)
end
