module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNonzeroLocalScalars
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftTopScalar

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NonzeroScalarsRootsOfUnity
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section

namespace GlobalTheory.StepVacForm

section Gen

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem theta_comb (hψ : IsStdChar D ψ (-1)) {c : WO S T →₀ ℂ} (hc : IsFinComb c) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (comb ψ S T c f) :=
  Finset.sum_induction _ (IsThetaFunO ψ S T) (fun _ _ => GlobalTheory.OrientedHeis.theta_add) GlobalTheory.OrientedHeis.theta_zero
    fun u hu => GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.FinTranslate.isThetaFunO_heisO hψ.1.1 hψ.1.2.1 hf (hc u hu))

theorem comb_smul (c : WO S T →₀ ℂ) (a : ℂ) (f : WO S T → ℂ) :
    comb ψ S T c (a • f) = a • comb ψ S T c f := by
  funext w
  simp only [GlobalTheory.FrComb.comb_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem vac_mono {LS : GlobalTheory.FinPl.Lat S} {LT : GlobalTheory.FinPl.Lat T} (P : GlobalTheory.FinPl.Pl D → Prop) {f : WO S T → ℂ}
    (h : GlobalTheory.FinPl.Vac ψ S T LS LT (fun _ => True) f) : GlobalTheory.FinPl.Vac ψ S T LS LT P f := by
  have hle : latO S T (LS : Set _) (LT : Set _) P ≤ latO S T (LS : Set _) (LT : Set _) fun _ => True :=
    AddSubgroup.closure_mono fun w ⟨α, hα, _, hw⟩ => ⟨α, hα, fun _ h => absurd trivial h, hw⟩
  exact ⟨h.1, fun u hu => h.2.1 u (hle hu), fun e he u hu hh => h.2.2 e he u (hle hu) hh⟩

theorem real_fock {χS χT : (AE D)ˣ →* Circle} {om : Om S T} (hθ : IsInfFam θ) (hW : IsWeilDatumO ψ S T χS χT om) (sS sT BS BT)
    {e : WO S T →₀ ℂ} (he : IsFinComb e) {f₀ : WO S T → ℂ} (hf₀ : IsThetaFunO ψ S T f₀) (P) {a : GA D S} (ha : a ∈ GinfC S)
    {a' : GA D T} (ha' : a' ∈ GinfC T) :
    om (a, a') (pureTensorO ψ θ S T sS sT BS BT (comb ψ S T e f₀) P) =
      comb ψ S T e (om (a, a') (pureTensorO ψ θ S T sS sT BS BT f₀ P)) := by
  have h1 : om (1, 1) (comb ψ S T e f₀) = (1 : ℂ) • comb ψ S T e f₀ := by
    rw [one_smul, show ((1, 1) : GA D S × GA D T) = 1 from rfl, map_one, Module.End.one_apply]
  have := (GlobalTheory.FockComb.om_pureTensorO_comb D ψ θ S T χS χT om hθ hW sS sT BS BT e f₀ _ 1 he hf₀ (theta_comb hW.std he hf₀)
    1 (one_mem _) 1 (one_mem _) h1 P a ha a' ha').1
  rwa [mul_one, mul_one, one_smul] at this

theorem step {χS χT : (AE D)ˣ →* Circle} {om : Om S T} (hθ : IsInfFam θ) (hW : IsWeilDatumO ψ S T χS χT om) (sS sT BS BT)
    {P Q : GlobalTheory.FinPl.Pl D → Prop} (hd : ∀ p, P p → ¬ Q p) {LS : GlobalTheory.FinPl.Lat S} {LT : GlobalTheory.FinPl.Lat T} {vac : WO S T → ℂ}
    (hv : GlobalTheory.FinPl.Vac ψ S T LS LT (fun _ => True) vac) {dG dQ eG eQ : WO S T →₀ ℂ} (hdG : GlobalTheory.FinPl.CombAt P dG)
    (hdQ : GlobalTheory.FinPl.CombAt Q dQ) (heG : GlobalTheory.FinPl.CombAt P eG) (heQ : GlobalTheory.FinPl.CombAt Q eQ)
    {b : GA D S} (hb : b ∈ GfC S) {b' : GA D T} (hb' : b' ∈ GfC T) {a : GA D S} (ha : a ∈ GinfC S)
    {a' : GA D T} (ha' : a' ∈ GinfC T)
    (hQ : ∀ g, GlobalTheory.FinPl.Vac ψ S T LS LT Q g → om (b, b') (comb ψ S T dQ g) = comb ψ S T eQ (om (b, b') g))
    (Pol) {c : ℂ} {Ψ : WO S T → ℂ}
    (hG : IsThetaFunO ψ S T (comb ψ S T dG (pureTensorO ψ θ S T sS sT BS BT vac Pol)) →
      om (a * b, a' * b') (comb ψ S T dG (pureTensorO ψ θ S T sS sT BS BT vac Pol)) = c • comb ψ S T eG Ψ) :
    om (a * b, a' * b') (pureTensorO ψ θ S T sS sT BS BT (comb ψ S T dQ (comb ψ S T dG vac)) Pol) =
      c • comb ψ S T eG (comb ψ S T eQ Ψ) := by
  have hψ : IsStdChar D ψ (-1) := hW.std
  have hPQ := GlobalTheory.DisjComb.main D ψ hψ S T P Q hd
  have hQP := GlobalTheory.DisjComb.main D ψ hψ S T Q P (fun p h h' => hd p h' h)
  have fG : IsFinComb dG := (hPQ.2.1 dG hdG).1
  have fQ : IsFinComb dQ := (hQP.2.1 dQ hdQ).1
  have h1 : om (1, 1) (comb ψ S T dG vac) = (1 : ℂ) • comb ψ S T dG vac := by
    rw [one_smul, show ((1, 1) : GA D S × GA D T) = 1 from rfl, map_one, Module.End.one_apply]
  have hvac := fun a ha a' ha' => (GlobalTheory.FockComb.om_pureTensorO_comb D ψ θ S T χS χT om hθ hW sS sT BS BT dG vac _ 1 fG hv.1
    (theta_comb hψ fG hv.1) 1 (one_mem _) 1 (one_mem _) h1 Pol a ha a' ha').2 LS LT hv
  have hth : IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT vac Pol) := by
    have := (hvac 1 (one_mem _) 1 (one_mem _)).1
    rwa [show ((1, 1) : GA D S × GA D T) = 1 from rfl, map_one, Module.End.one_apply] at this
  have hg := (hPQ.2.1 dG hdG).2 LS LT _ (vac_mono Q (hvac a ha a' ha'))
  have e1 : ((a * b, a' * b') : GA D S × GA D T) = (b, b') * (a, a') := by
    rw [Formalism.IndefR.Eqv.Act.comm_inf_fin ha hb, Formalism.IndefR.Eqv.Act.comm_inf_fin ha' hb']
    rfl
  have hG' := hG (theta_comb hψ fG hth)
  rw [e1, map_mul, Module.End.mul_apply, GlobalTheory.FrComb.om_comb hW ha ha' fG hth] at hG'
  rw [e1, map_mul, Module.End.mul_apply, real_fock hθ hW sS sT BS BT fQ (theta_comb hψ fG hv.1) Pol ha ha',
    real_fock hθ hW sS sT BS BT fG hv.1 Pol ha ha', hQ _ hg, hG', comb_smul, hPQ.1 eG eQ heG heQ]

end Gen

theorem under_ne {D : D7} {T : Type} (L : LevCh D T) {μ0 : T} (hL : L.Is μ0) (t : T) {PP PP' : Pl D.host.E} (h : PP ∈ L.Pg)
    (h' : PP' ∈ L.Q t) : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') := by
  intro e
  obtain ⟨i, hi⟩ := (hL.Pg PP).1 h
  obtain ⟨⟨q, hq, hcard, -, hqg⟩, -⟩ := hL.Q_pl t PP' h'
  have hg : ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    have h0 := L.C.P.pb_over i
    rw [← hi] at h0
    have h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g i : ℕ) : 𝓞 D.host.K) ∈ PP.asIdeal := h0
    rwa [map_natCast] at h2
  have hq' : (q : 𝓞 D.host.E) ∈ PP'.asIdeal := by
    have h1 : Nat.card (kP PP') • (1 : kP PP') = 0 := card_nsmul_eq_zero'
    rw [hcard, nsmul_one] at h1
    exact Ideal.Quotient.eq_zero_iff_mem.1 ((map_natCast _ q).trans h1)
  have hqF : (q : 𝓞 D.host.F) ∈ ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP')).asIdeal := by
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) q ∈ PP'.asIdeal
    rwa [map_natCast]
  rw [← e] at hqF
  have hqP : (q : 𝓞 D.host.E) ∈ PP.asIdeal := by
    have h2 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) q ∈ PP.asIdeal := hqF
    rwa [map_natCast] at h2
  obtain ⟨a, b, hab⟩ : IsCoprime ((D.host.g i : ℕ) : 𝓞 D.host.E) q :=
    Nat.Coprime.cast ((Nat.coprime_primes (D.host.g_prime i) hq).2 fun h => hqg i h.symm)
  exact PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ PP.asIdeal.add_mem (PP.asIdeal.mul_mem_left _ hg) (PP.asIdeal.mul_mem_left _ hqP)))

end GlobalTheory.StepVacForm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChainTopThetaLift
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BaseChain

theorem setIntegral_smul_measure_complex {H : Type*} [MeasurableSpace H] (c : ENNReal) (ν : Measure H) (s : Set H) (f : H → ℂ) :
    ∫ y in s, f y ∂(c • ν) = c.toReal • ∫ y in s, f y ∂ν := by
  rw [Measure.restrict_smul, integral_smul_measure]

end GlobalTheory.BaseChain

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftTheoremBPublishedHypothesesStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCarries
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.ThmBFromScal

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem eEp3_eq (R : RealDat3 D A3 Ks)
    (hU : ∀ p c c', R.Carries p c → R.Carries p c' → R.EEc c = R.EEc c' ∧ ∀ i, R.Wc' i c = R.Wc' i c')
    {p : A3.fam3.base3.Ix} {c : Pl D.host.E → List ℤ → ℂ} (hc : R.Carries p c) :
    R.EEp3 p = R.EEc c ∧ ∀ i, R.Wp3 i p = R.Wc' i c := by
  refine ⟨le_antisymm (iSup₂_le fun c' hc' => ((hU p c c' hc hc').1).symm.le) (le_iSup₂ (f := fun c' (_ : R.Carries p c') => R.EEc c') c hc),
    fun i => le_antisymm (iSup₂_le fun c' hc' => (((hU p c c' hc hc').2 i)).symm.le)
      (le_iSup₂ (f := fun c' (_ : R.Carries p c') => R.Wc' i c') c hc)⟩

theorem exists_carries (R : RealDat3 D A3 Ks) {p : A3.fam3.base3.Ix} (h : R.EEp3 p ≠ ⊥) :
    ∃ c, R.Carries p c := by
  by_contra hn
  push_neg at hn
  apply h
  unfold RealDat3.EEp3
  exact iSup₂_eq_bot.2 fun c hc => absurd hc (hn c)

theorem wc_eq (R : RealDat3 D A3 Ks) (i : Fin D.R.m) (c : Pl D.host.E → List ℤ → ℂ) :
    R.Wc' i c = GlobalTheory.Hk3.Wcc R.toRealDat R.SF i c := rfl

theorem ec_eq (R : RealDat3 D A3 Ks) (c : Pl D.host.E → List ℤ → ℂ) :
    R.EEc c = GlobalTheory.Hk3.EEc R.toRealDat R.SF c := rfl

end GlobalTheory.ThmBFromScal

namespace GlobalTheory.ThmBFromScal

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem act_on_part (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F)
    {lam : Fin D.R.m → T → GlobalTheory.LiftRows.Eig D → ℝ} {κ : ℝ}
    (hW : ∀ i t c, ∀ x ∈ GlobalTheory.Hk3.Wcc R.toRealDat R.SF i c,
      R.thG i t (LinearMap.adjoint (R.thG i t) x) = ((lam i t c : ℝ) : ℂ) • x)
    (hE : ∀ t c, ∀ x ∈ GlobalTheory.Hk3.EEc R.toRealDat R.SF c,
      R.Th t (LinearMap.adjoint (R.Th t) x) = ((κ * ∏ i, lam i t c : ℝ) : ℂ) • x)
    (hM : GlobalTheory.LiftRows.MatchUp R.toRealDat R.SF)
    (hU : ∀ p c c', R.Carries p c → R.Carries p c' → R.EEc c = R.EEc c' ∧ ∀ i, R.Wc' i c = R.Wc' i c')
    {p : A3.fam3.base3.Ix} {c : Pl D.host.E → List ℤ → ℂ} (hc : R.Carries p c) (t : T) :
    (∀ i, R.lam3 i t p A3.A.v0 = lam i t c) ∧
      ∀ x ∈ R.EEp3 p, R.Th t (LinearMap.adjoint (R.Th t) x) =
        ((κ * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN t j p : ℝ) : ℂ) • x := by
  have hEp := (eEp3_eq R hU hc).1
  have hWp := (eEp3_eq R hU hc).2
  have hl : ∀ i, R.lam3 i t p A3.A.v0 = lam i t c := by
    intro i
    refine hC.scal.lam0 i t p (lam i t c) ?_ ?_
    · rw [hWp i, wc_eq]
      exact hM c (by rw [← ec_eq]; exact hc.1) i
    · intro x hx
      rw [hWp i, wc_eq] at hx
      exact hW i t c x hx
  refine ⟨hl, fun x hx => ?_⟩
  rw [hEp] at hx
  rw [hE t c x hx, RealDat3.prod_lamN (R := R) t p]
  simp only [hl]

theorem pThmB {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ} :
    A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → GlobalTheory.LiftRows.Scal R.toRealDat R.SF →
    GlobalTheory.LiftRows.MatchUp R.toRealDat R.SF →
    (∀ p c c', R.Carries p c → R.Carries p c' → R.EEc c = R.EEc c' ∧ ∀ i, R.Wc' i c = R.Wc' i c') → R.PThmB := by
  intro _ hC _ hS hM hU
  classical
  unfold GlobalTheory.LiftRows.Scal at hS
  obtain ⟨lam, κ, hκ, hlpos, hW, hE⟩ := hS

  have hK : Lift.IsKap D.R.m (fun t => R.Th t ∘ₗ LinearMap.adjoint (R.Th t)) R.EEp3 R.lamN κ := by
    intro t p x hx
    rw [LinearMap.comp_apply]
    by_cases h0 : R.EEp3 p = ⊥
    · rw [h0, Submodule.mem_bot] at hx
      subst hx
      simp
    · exact (act_on_part R F hC hW hE hM hU (exists_carries R h0).choose_spec t).2 x hx
  by_cases hex : ∃ (_ : T) (p : A3.fam3.base3.Ix), R.EEp3 p ≠ ⊥
  · obtain ⟨t, p, hp⟩ := hex
    have hc := (exists_carries R hp).choose_spec
    have hl := (act_on_part R F hC hW hE hM hU hc t).1
    have hk : R.kap = κ := by
      refine hC.scal.kap κ hK ⟨t, p, hp, ?_⟩
      rw [RealDat3.prod_lamN (R := R) t p, Finset.prod_congr rfl fun i _ => hl i]
      exact (Finset.prod_pos fun i _ => hlpos i t _).ne'
    intro t' p' x hx
    exact (hK t' p' x hx).trans (by rw [hk])
  · push_neg at hex
    intro t p x hx
    rw [hex t p, Submodule.mem_bot] at hx
    subst hx
    simp

end GlobalTheory.ThmBFromScal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftSecondHypotheses
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

namespace GlobalTheory.PThmBShort

theorem pThmB_short : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilSiegelFormulaUnitary → (∀ D' : Formalism.BasicNotions.D7, GlobalTheory.Core.Rk.SW.HeckeFormNS D') → GlobalTheory.Published.SiegelEisensteinContinuation → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → HostHyp D → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → D.host.ccK = ⊤ → FWT.QGuard R.toRealDat → GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes R.toRealDat → GlobalTheory.TrCopy.TRLev R.toRealDat F.lv2 R.SF → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → R.PThmB := by
  intro hDS hHCF hHCM hCW hCusp hHowe hWS hSWc hSEc hUD hBZ
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hCh hEx hHost hLed hcc hQ hGT hTR hHk
  have hGiven := GlobalTheory.GivenOfTop.given_of_top R F hOk hCh hEx hHost hLed hcc hQ hGT
  obtain ⟨-, hSF, -, -⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hCh hEx
  have hFix := GlobalTheory.FixAllGood.fixAll_of_good R F hCh hEx
  obtain ⟨hScal, hMatch, hInj, -⟩ :=
    GlobalTheory.T.thetaLift_scalarIdentity_matching_adjointInjective hDS hHCF hHCM hCW hCusp hHowe hWS hSWc hSEc hUD hBZ R.toRealDat F.lv2 hGiven hcc
      hCh.allPl hFix R.SF hSF hTR
  exact GlobalTheory.ThmBFromScal.pThmB R F hOk hCh hEx hScal hMatch
    (GlobalTheory.CarriesOne.parts_eq_of_carries hHowe hCusp R F hOk hCh hEx hHk hInj)

end GlobalTheory.PThmBShort
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_theoremB_publishedHypotheses : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilSiegelFormulaUnitary → (∀ D' : Formalism.BasicNotions.D7, GlobalTheory.Core.Rk.SW.HeckeFormNS D') → GlobalTheory.Published.SiegelEisensteinContinuation → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → HostHyp D → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → D.host.ccK = ⊤ → FWT.QGuard R.toRealDat → GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes R.toRealDat → GlobalTheory.TrCopy.TRLev R.toRealDat F.lv2 R.SF → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → R.PThmB := by
  first | exact @GlobalTheory.PThmBShort.pThmB_short | exact GlobalTheory.PThmBShort.pThmB_short | (intros; apply GlobalTheory.PThmBShort.pThmB_short <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftPositiveScalarsBasePlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftPositiveScalarsBasePlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

namespace GlobalTheory.PosScalBase

theorem pos_scal_base : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilSiegelFormulaUnitary → (∀ D' : Formalism.BasicNotions.D7, GlobalTheory.Core.Rk.SW.HeckeFormNS D') → GlobalTheory.Published.SiegelEisensteinContinuation → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → HostHyp D → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → D.host.ccK = ⊤ → FWT.QGuard R.toRealDat → GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes R.toRealDat → GlobalTheory.TrCopy.TRLev R.toRealDat F.lv2 R.SF → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → R.PGEquiv F → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) := by
  intro hDS hHCF hHCM hCW hCusp hHowe hWS hSWc hSEC hUD hBZ D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hCh hEx hHost hPar hcc hQG hGT hTR hHk hPG hPos
  have hGiven := GlobalTheory.GivenOfTop.given_of_top R F hOk hCh hEx hHost hPar hcc hQG hGT
  have hcore := GlobalTheory.CoreOfWeak.core_of_weak R F hCh hEx
  have hfix := GlobalTheory.FixAllGood.fixAll_of_good R F hCh hEx
  obtain ⟨hScal, hMatch, hUp, -⟩ :=
    GlobalTheory.T.thetaLift_scalarIdentity_matching_adjointInjective hDS hHCF hHCM hCW hCusp hHowe hWS hSWc hSEC hUD hBZ R.toRealDat F.lv2 hGiven hcc hCh.allPl hfix R.SF hcore.2.1 hTR
  have hCar := GlobalTheory.CarriesOne.parts_eq_of_carries hHowe hCusp R F hOk hCh hEx hHk hUp
  have hNe := GlobalTheory.RowsPartNe.exists_rowPart_ne_bot_positiveDimension hHowe hCusp R F hOk hCh hEx hHk hPG hPos
  exact GlobalTheory.PosAtBase.pos_at_base R F hOk hCh hEx hScal hMatch hCar hNe

end GlobalTheory.PosScalBase
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftPositiveScalarsBasePlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_positiveScalars_basePlace : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilSiegelFormulaUnitary → (∀ D' : Formalism.BasicNotions.D7, GlobalTheory.Core.Rk.SW.HeckeFormNS D') → GlobalTheory.Published.SiegelEisensteinContinuation → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → HostHyp D → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → D.host.ccK = ⊤ → FWT.QGuard R.toRealDat → GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes R.toRealDat → GlobalTheory.TrCopy.TRLev R.toRealDat F.lv2 R.SF → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → R.PGEquiv F → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) := by
  first | exact @GlobalTheory.PosScalBase.pos_scal_base | exact GlobalTheory.PosScalBase.pos_scal_base | (intros; apply GlobalTheory.PosScalBase.pos_scal_base <;> assumption)
end
end
