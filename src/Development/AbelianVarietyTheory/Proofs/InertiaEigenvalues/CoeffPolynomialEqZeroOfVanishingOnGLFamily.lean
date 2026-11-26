module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixCoefficientVacuaUnramifiedPlace
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsClassSystem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsCentAtScalar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanOneParameterFamilyContinuous

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffPolynomialEqZeroOfVanishingOnGLFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffPolynomialEqZeroOfVanishingOnGLFamily
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open Formalism.IndefR.Links
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ExportSeries

open MvPolynomial Matrix

theorem eq_zero_of_coefFn_id_eq_zero (D : D7) (n : ℕ) (lam : D.what₂.Tau → DomWeight n) (F : Formalism.L2.DIV.Pol ℂ D.what₂.Tau n)
    (hF : ∀ x : GLR D n, coefFn (RingHom.id ℂ) lam F x = 0) : F = 0 := by
  classical
  set d : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ :=
    ∏ τ, (Matrix.of fun a b => (X (τ, a, b) : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ)).det with hd
  have hev : ∀ v : D.what₂.Tau × Fin n × Fin n → ℂ, eval v d = ∏ τ, (Matrix.of fun a b => v (τ, a, b)).det := by
    intro v
    rw [hd, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [RingHom.map_det]
    congr 1
    ext a b
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.of_apply, eval_X]
  have hd0 : d ≠ 0 := by
    intro h
    have := hev (fun w => (1 : Matrix (Fin n) (Fin n) ℂ) w.2.1 w.2.2)
    rw [h, map_zero] at this
    have h1 : ∀ τ : D.what₂.Tau, (Matrix.of fun a b => (1 : Matrix (Fin n) (Fin n) ℂ) a b).det = 1 := by
      intro τ
      have : (Matrix.of fun a b => (1 : Matrix (Fin n) (Fin n) ℂ) a b) = 1 := by ext a b; rfl
      rw [this, det_one]
    rw [Finset.prod_eq_one fun τ _ => h1 τ] at this
    exact zero_ne_one this
  have hFd : F * d = 0 := by
    apply MvPolynomial.funext
    intro v
    rw [map_mul, map_zero, hev]
    by_cases h : ∏ τ, (Matrix.of fun a b => v (τ, a, b)).det = 0
    · rw [h, mul_zero]
    · have hτ : ∀ τ, (Matrix.of fun a b => v (τ, a, b)).det ≠ 0 := fun τ hτ =>
        h (Finset.prod_eq_zero (Finset.mem_univ τ) hτ)
      let x : GLR D n := fun τ => GeneralLinearGroup.mkOfDetNeZero _ (hτ τ)
      have hx := hF x
      rw [coefFn] at hx
      have hu : ((detFam (fun τ => (lam τ).detShift) x : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
      have h2 := (mul_eq_zero.mp hx).resolve_left hu
      have h3 : (fun w : D.what₂.Tau × Fin n × Fin n => (x w.1).val w.2.1 w.2.2) = v := by
        funext w
        rfl
      rw [h3] at h2
      have h4 : eval v F = 0 := by
        rw [← h2]
        rfl
      rw [h4, zero_mul]
  exact (mul_eq_zero.mp hFd).resolve_right hd0

end GlobalTheory.ExportSeries
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffPolynomialEqZeroOfVanishingOnGLFamilyStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open Formalism.IndefR.Links
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeffPolynomial_eq_zero_of_vanishing_on_GLFamily : ∀ (D : D7) (n : ℕ) (lam : D.what₂.Tau → DomWeight n) (F : Formalism.L2.DIV.Pol ℂ D.what₂.Tau n), (∀ x : GLR D n, coefFn (RingHom.id ℂ) lam F x = 0) → F = 0 := by
  first | exact @GlobalTheory.ExportSeries.eq_zero_of_coefFn_id_eq_zero | exact GlobalTheory.ExportSeries.eq_zero_of_coefFn_id_eq_zero | (intros; apply GlobalTheory.ExportSeries.eq_zero_of_coefFn_id_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDatumCharactersUnramifiedOffLevels
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDatumCharactersUnramifiedOffLevels
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.GoodModUnr

open GlobalTheory.IdemSupport

variable {D : D7}

theorem unrAt_of_unrPl {w : HeightOneSpectrum (𝓞 D.host.E)} {χ : (AE D)ˣ →* Circle} (h : GlobalTheory.Hk3.UnrPl w χ) :
    GlobalTheory.LFun.UnrAt χ w := by
  intro u hu
  have hΦ : Comp D (GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E) := by
    obtain ⟨a, b, c, d, e⟩ := (GlobalTheory.LFun.EulerTie.comp_finComp (F := D.host.F) (E := D.host.E))
    exact ⟨a, b, c, d, e⟩
  obtain ⟨e, f, hp⟩ := exists_isPrimeIdem hΦ w
  have hd := (of_isPrimeIdem hΦ hp).1
  have hee : e * e = e := delta_idem hΦ hd
  have hfe : f * e = e := by
    rcases hp with ⟨hi, rfl⟩ | ⟨rfl, -, -⟩
    · have ho : e * cA D e = 0 := hi.1.2.1
      linear_combination hee + ho
    · exact hee
  obtain ⟨h1, h2⟩ := (GlobalTheory.LFun.EulerTie.isUnitAt_iff w u).1 hu
  have hg : e * ((GlobalTheory.LFun.locIdele D.host.F w u : (AE D)ˣ) : AE D) + (1 - e) =
      ((GlobalTheory.LFun.locIdele D.host.F w u : (AE D)ˣ) : AE D) :=
    GlobalTheory.LFun.EulerTie.glue_eq_locIdele hd (GlobalTheory.LFun.EulerTie.finComp_locIdele_self w u)
  have hx : f * (((GlobalTheory.LFun.locIdele D.host.F w u : (AE D)ˣ) : AE D) - 1) =
      ((GlobalTheory.LFun.locIdele D.host.F w u : (AE D)ˣ) : AE D) - 1 := by
    linear_combination (((GlobalTheory.LFun.locIdele D.host.F w u : (AE D)ˣ) : AE D) - 1) * hfe + (1 - f) * hg
  have i1 := (GlobalTheory.LFun.EulerTie.locIdele_int_iff (F := D.host.F) w u).2 h1
  have i2 := (GlobalTheory.LFun.EulerTie.locIdele_int_iff (F := D.host.F) w u⁻¹).2 h2
  rw [map_inv] at i2
  have := h e f hp _ hx i1 i2
  exact (congrArg Circle.toUnits this).trans (map_one _)

theorem good_of_ne {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (t : T) {v : HeightOneSpectrum (𝓞 D.host.F)}
    {f : AE D} (hf : IsFinIdem D v f) (hv : ∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f', IsPrimeIdem P e f' → f' ≠ f)
    {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w.under (𝓞 D.host.F) = v) : GlobalTheory.Hk3.Good R t w := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  intro PP hPP
  have key : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v := by
    intro hu
    obtain ⟨e, f', hp⟩ := exists_isPrimeIdem hΦ PP
    obtain ⟨-, ε, hε, hf'⟩ := of_isPrimeIdem hΦ hp
    obtain ⟨ε', hε', rfl⟩ := hf
    rw [hu] at hε
    exact hv PP hPP e f' hp (by rw [hf', placeIdem_unique hε hε'])
  refine ⟨fun h => key (h ▸ hw), fun h => key ?_⟩
  rw [← hw, (isConjPl_iff PP w).1 h, under_cP]

theorem chrTh_unrAt : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ (i : Fin D.R.m) (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : AE D), IsFinIdem D v f → (∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f', IsPrimeIdem P e f' → f' ≠ f) → ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt (Formalism.IndefR.Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).1 w ∧ GlobalTheory.LFun.UnrAt (Formalism.IndefR.Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2 w := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL i t v f hf hv w hw
  obtain ⟨he, hm⟩ := GlobalTheory.UnrOffLevels.unrPl_of_good R F hL.lev t w (good_of_ne R t hf hv hw)
  have a := unrAt_of_unrPl (hm ((i : ℕ) + 1) (by omega) (by have := i.isLt; omega))
  have b := unrAt_of_unrPl he
  exact ⟨a, a.mul b.inv⟩

end GlobalTheory.GoodModUnr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDatumCharactersUnramifiedOffLevelsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDatumCharacters_unramified_offLevels : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ (i : Fin D.R.m) (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : AE D), IsFinIdem D v f → (∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f', IsPrimeIdem P e f' → f' ≠ f) → ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt (Formalism.IndefR.Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).1 w ∧ GlobalTheory.LFun.UnrAt (Formalism.IndefR.Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2 w := by
  first | exact @GlobalTheory.GoodModUnr.chrTh_unrAt | exact GlobalTheory.GoodModUnr.chrTh_unrAt | (intros; apply GlobalTheory.GoodModUnr.chrTh_unrAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemThPsiOfMemSpan
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries
open Formalism.IndefR.Links
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Ser

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

open Classical in
def specXi (ρ : Setup X) (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ)
    (Q : Finset (Pl D.host.E)) (M : ℕ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ) (h : GA D (Vc D j))
    (P : PolF D (Wc D j).rank (Vc D j).rank) : GA D (Wc D j) → ℂ :=
  ∑ a, ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) a)) : X.Ok i k) • ρ.xi i j b Y Q M h P a

theorem exists_mem_thPsi_of_mem_span {ρ : Setup X} {hρ : ρ.Good} {Y : NExp D.R D.host D.what₂ D.LL0 N X} {i : X.Tw}
    {j : Fin D.R.m} {b : Bool} {rd : Rd ρ Y i j b} (T : CellTie hρ Y rd) (hR : RatTwist hρ rd) {k : ℕ}
    {Q : Finset (Pl D.host.E)} {ψ : G D.host.E N.Om →* (X.Ok i k)ˣ} (hψ : TwOK i k Q ψ) (hQ : ClsQ (D := D) Q)
    (d : Y.Dat i ((j : ℕ) + 1) b) {f : GA D (Wc D j) → ℂ}
    (hf : f ∈ Submodule.span (ρ.eOk i b k).range (ρ.gens i j b k Q ψ (T.cls d) (T.coef d))) :
    ∃ z ∈ Formalism.MainNotions.IntegralHeckeForms.ThPsi Y i ((j : ℕ) + 1) b k Q ψ {d}, rdK rd hρ k z = f := by
  induction hf using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨z, hz⟩ := hR k Q ψ hψ hQ _ _ _ (T.dat d) hs
    refine ⟨z, Submodule.subset_span ?_, hz⟩
    exact Set.mem_biUnion (Set.mem_singleton d) ((T.thPsi_iff k Q ψ hψ d z).2 (hz ▸ hs))
  | zero => exact ⟨0, zero_mem _, map_zero _⟩
  | add f g _ _ hf hg =>
    obtain ⟨z, hz, rfl⟩ := hf
    obtain ⟨z', hz', rfl⟩ := hg
    exact ⟨z + z', add_mem hz hz', map_add _ _ _⟩
  | smul c f _ hf =>
    obtain ⟨z, hz, rfl⟩ := hf
    obtain ⟨c', hc'⟩ := c.2
    refine ⟨c' • z, Submodule.smul_mem _ _ hz, ?_⟩
    rw [map_smulₛₗ]
    change ρ.eOk i b k c' • rdK rd hρ k z = (c : ℂ) • rdK rd hρ k z
    rw [hc']

end Ser

end GlobalTheory.SeriesTie

namespace GlobalTheory.SeriesTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section SpecLoc

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

open Classical in
def specLoc (ρ : Setup X) (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ)
    (Q : Finset (Pl D.host.E)) (M : ℕ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ)
    (PP : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M))) (y : Matrix (Fin (Wc D j).rank) (Fin (Vc D j).rank) (kP PP.1)) : ℂ :=
  ∑ c : ZMod (X.l i ^ M), ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) (Pi.single PP c))) : X.Ok i k) *
    ((Base.univFam (univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc) (ρ.β j) PP.1 c y : ℚ) : ℂ)

def specSer (ρ : Setup X) (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ)
    (Q : Finset (Pl D.host.E)) (M : ℕ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ) (h : GA D (Vc D j))
    (P : PolF D (Wc D j).rank (Vc D j).rank) : GA D (Wc D j) → ℂ :=
  twistBy (Wc D j) (ρ.tw i b k Q (χ.comp (Y.delU i Q M))).chi
    (series (ρ.B i j b).F (ρ.om i j b 1) ((ρ.B i j b).vecAt (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) (specLoc ρ Y i j b k Q M χ)) h P)

end SpecLoc

end GlobalTheory.SeriesTie

namespace GlobalTheory.SeriesTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Ser2

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

open Classical in
theorem rdK_specU_grpSum {ρ : Setup X} (hρ : ρ.Good) {Y : NExp D.R D.host D.what₂ D.LL0 N X} {i : X.Tw}
    {j : Fin D.R.m} {b : Bool} (rd : Rd ρ Y i j b) (k : ℕ) (Q : Finset (Pl D.host.E)) (M : ℕ)
    (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ)
    (x : (↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) → ZMod (X.l i ^ M)) → Y.Fm i ((j : ℕ) + 1) b) :
    rdK rd hρ k (Formalism.MainNotions.IntegralHeckeForms.specU Y i ((j : ℕ) + 1) b Q M k χ (grpSum Y (ρ.ch i) Q M x)) =
      ∑ a, ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) a)) : X.Ok i k) • rd (x a) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [grpSum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Formalism.MainNotions.IntegralHeckeForms.specU, LinearMap.coe_comp, Function.comp_apply, LinearMap.lTensor_tmul,
    LinearEquiv.coe_coe, TensorProduct.comm_tmul, AlgHom.toLinearMap_apply, AddMonoidAlgebra.lift_single, one_smul,
    MonoidHom.coe_comp, Units.coeHom_apply]
  rw [rdK_tmul]

end Ser2

end GlobalTheory.SeriesTie
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockTargetGlActionCompactPreservesJointHarmonics
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockTargetGlActionCompactPreservesJointHarmonics
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.CompactHarm

open MvPolynomial

theorem pd_comm {σ : Type*} (i j : σ) (f : MvPolynomial σ ℂ) :
    pderiv i (pderiv j f) = pderiv j (pderiv i f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p k hp =>
    have h : ∀ a b : σ, pderiv a (pderiv b (X k : MvPolynomial σ ℂ)) = 0 := by
      intro a b
      rw [pderiv_X]
      by_cases hk : k = b
      · subst hk; simp
      · simp [Pi.single_eq_of_ne hk]
    simp only [Derivation.leibniz, map_add (f := _), smul_eq_mul, hp, h]
    ring

theorem pd_X_mul {σ : Type*} [DecidableEq σ] (x u : σ) (Q : MvPolynomial σ ℂ) :
    pderiv x (X u * Q) = (if u = x then Q else 0) + X u * pderiv x Q := by
  rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul]
  by_cases h : u = x
  · subst h; simp only [Pi.single_eq_same, mul_one, if_true]; ring
  · simp only [Pi.single_apply, h, if_false, mul_zero, add_zero, zero_add]

theorem dd_X_mul {σ : Type*} [DecidableEq σ] (x y u : σ) (R : MvPolynomial σ ℂ) :
    pderiv x (pderiv y (X u * R)) = (if u = y then pderiv x R else 0) + (if u = x then pderiv y R else 0) +
      X u * pderiv x (pderiv y R) := by
  rw [pd_X_mul, map_add (f := _), pd_X_mul]
  split_ifs <;> (try simp only [map_zero]) <;> ring

theorem gen {σ : Type*} [DecidableEq σ] {n : ℕ} (x y u w : Fin n → σ) (P : MvPolynomial σ ℂ)
    (hxy : ∑ j, pderiv (x j) (pderiv (y j) P) = 0)
    (hA1 : ∑ j, ∑ k, (if u k = y j then pderiv (x j) (pderiv (w k) P) else 0) = 0)
    (hA2 : ∑ j, ∑ k, (if u k = x j then pderiv (y j) (pderiv (w k) P) else 0) = 0) :
    ∑ j, pderiv (x j) (pderiv (y j) (∑ k, X (u k) * pderiv (w k) P)) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, dd_X_mul]
  simp only [Finset.sum_add_distrib]
  rw [hA1, hA2, zero_add, zero_add, Finset.sum_comm]
  have : ∀ k, ∑ j, X (u k) * pderiv (x j) (pderiv (y j) (pderiv (w k) P)) = 0 := by
    intro k
    rw [← Finset.mul_sum]
    simp only [pd_comm (y _) (w k), pd_comm (x _) (w k)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, hxy, map_zero, mul_zero]
  simp [this]

end GlobalTheory.CompactHarm

namespace GlobalTheory.CompactHarm

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

theorem fockT_single {D : D7} {m n : ℕ} (τ : D.what₂.Tau) (ε' : Fin m → Bool) (i l : Fin m) (Q : PolF D m n) :
    fockT τ (fun _ : Fin n => true) ε' (Matrix.single i l (1 : ℂ)) Q =
      ∑ j, (raiO τ (fun _ : Fin n => true) ε' i j * lowO τ (fun _ : Fin n => true) ε' l j) Q +
        (if i = l then ((n : ℂ) / 2) • Q else 0) := by
  classical
  unfold fockT
  rw [Finset.sum_eq_single i, Finset.sum_eq_single l]
  · simp only [Matrix.single_apply_same, one_smul, LinearMap.sum_apply, LinearMap.add_apply, Finset.sum_add_distrib]
    congr 1
    split_ifs with h
    · simp only [LinearMap.smul_apply, Module.End.one_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        smul_smul]
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
      congr 1
      ring
    · simp
  · intro k _ hk; simp [Matrix.single_apply, Ne.symm hk]
  · simp
  · intro k _ hk
    rw [Finset.sum_eq_zero]
    intro l' _
    simp [Matrix.single_apply, Ne.symm hk]
  · simp

theorem low_eq {D : D7} {m n : ℕ} (τ : D.what₂.Tau) (ε' : Fin m → Bool) (i l : Fin m) (hi : ε' i = false)
    (hl : ε' l = true) (Q : PolF D m n) :
    fockT τ (fun _ : Fin n => true) ε' (Matrix.single i l (1 : ℂ)) Q =
      -∑ j, pderiv (τ, i, j) (pderiv (τ, l, j) Q) := by
  have hil : i ≠ l := fun e => by rw [e, hl] at hi; exact Bool.noConfusion hi
  rw [fockT_single, if_neg hil, add_zero, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [raiO, lowO, sgn, hi, hl]

theorem up_eq {D : D7} {m n : ℕ} (τ : D.what₂.Tau) (ε' : Fin m → Bool) (a b : Fin m) (ha : ε' a = true)
    (hb : ε' b = true) (Q : PolF D m n) :
    fockT τ (fun _ : Fin n => true) ε' (Matrix.single a b (1 : ℂ)) Q =
      ∑ j, X (τ, a, j) * pderiv (τ, b, j) Q + (if a = b then ((n : ℂ) / 2) • Q else 0) := by
  rw [fockT_single]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [raiO, lowO, sgn, ha, hb]

theorem dn_eq {D : D7} {m n : ℕ} (τ : D.what₂.Tau) (ε' : Fin m → Bool) (a b : Fin m) (ha : ε' a = false)
    (hb : ε' b = false) (Q : PolF D m n) :
    fockT τ (fun _ : Fin n => true) ε' (Matrix.single a b (1 : ℂ)) Q =
      -∑ j, pderiv (τ, a, j) (X (τ, b, j) * Q) + (if a = b then ((n : ℂ) / 2) • Q else 0) := by
  rw [fockT_single, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [raiO, lowO, sgn, ha, hb]

end GlobalTheory.CompactHarm

namespace GlobalTheory.CompactHarm

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

theorem fockT_compact_harm : ∀ (D : D7) (n m : ℕ) (p : D.what₂.Tau → ℕ) (P : PolF D m n), (∀ (τ' : D.what₂.Tau) (i l : Fin m), p τ' ≤ (i : ℕ) → (l : ℕ) < p τ' → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ' (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ')) (Matrix.single i l (1 : ℂ)) (P) = 0) → ∀ (τ : D.what₂.Tau) (a b : Fin m), ((a : ℕ) < p τ ↔ (b : ℕ) < p τ) → ∀ (τ' : D.what₂.Tau) (i l : Fin m), p τ' ≤ (i : ℕ) → (l : ℕ) < p τ' → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ' (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ')) (Matrix.single i l (1 : ℂ)) (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) (Matrix.single a b (1 : ℂ)) P) = 0 := by
  classical
  intro D n m p P hP τ a b hab τ' i l hi hl
  have hL : ∀ (σ : D.what₂.Tau) (i l : Fin m), p σ ≤ (i : ℕ) → (l : ℕ) < p σ →
      ∑ j, pderiv (σ, i, j) (pderiv (σ, l, j) P) = 0 := by
    intro σ i l hi hl
    have := hP σ i l hi hl
    rw [low_eq σ _ i l (by simpa using hi) (by simpa using hl)] at this
    exact neg_eq_zero.1 this
  rw [low_eq τ' _ i l (by simpa using hi) (by simpa using hl), neg_eq_zero]
  let Lop : PolF D m n →ₗ[ℂ] PolF D m n :=
    ∑ j, (pderiv (τ', i, j)).toLinearMap ∘ₗ (pderiv (τ', l, j)).toLinearMap
  have hLop : ∀ Q, Lop Q = ∑ j, pderiv (τ', i, j) (pderiv (τ', l, j) Q) := by
    intro Q; simp [Lop, LinearMap.sum_apply]
  have hP0 : Lop P = 0 := by rw [hLop]; exact hL τ' i l hi hl
  have hite : ∀ (c : Prop) [Decidable c] (z : ℂ), Lop (if c then z • P else 0) = 0 := by
    intro c _ z; split_ifs <;> simp [hP0]
  rw [← hLop]
  by_cases ha : (a : ℕ) < p τ
  · have hb : (b : ℕ) < p τ := hab.1 ha
    rw [up_eq τ _ a b (by simpa using ha) (by simpa using hb), map_add (f := _), hite, add_zero, hLop]
    refine gen (fun j => (τ', i, j)) (fun j => (τ', l, j)) (fun k => (τ, a, k)) (fun k => (τ, b, k)) P
      (hL τ' i l hi hl) ?_ ?_
    · by_cases h : τ = τ' ∧ a = l
      · obtain ⟨rfl, rfl⟩ := h
        simp only [Prod.mk.injEq, true_and, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
        exact hL τ i b hi hb
      · refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => if_neg ?_
        intro e; simp only [Prod.mk.injEq] at e; exact h ⟨e.1, e.2.1⟩
    · refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => if_neg ?_
      intro e; simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl, -⟩ := e; omega
  · have hb : ¬ (b : ℕ) < p τ := fun h => ha (hab.2 h)
    rw [dn_eq τ _ a b (by simpa using ha) (by simpa using hb)]
    have e : ∑ k, pderiv (τ, a, k) (X (τ, b, k) * P) =
        (∑ k, if ((τ, b, k) : FVar D m n) = (τ, a, k) then P else 0) + ∑ k, X (τ, b, k) * pderiv (τ, a, k) P := by
      simp only [pd_X_mul, Finset.sum_add_distrib]
    have hS1 : Lop (∑ k, if ((τ, b, k) : FVar D m n) = (τ, a, k) then P else 0) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      split_ifs <;> simp [hP0]
    rw [e, map_add (f := _), map_neg, map_add (f := _), hS1, zero_add, hite, add_zero, neg_eq_zero, hLop]
    refine gen (fun j => (τ', i, j)) (fun j => (τ', l, j)) (fun k => (τ, b, k)) (fun k => (τ, a, k)) P
      (hL τ' i l hi hl) ?_ ?_
    · refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => if_neg ?_
      intro e; simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl, -⟩ := e; omega
    · by_cases h : τ = τ' ∧ b = i
      · obtain ⟨rfl, rfl⟩ := h
        simp only [Prod.mk.injEq, true_and, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
        simp only [pd_comm (τ, l, _) (τ, a, _)]
        exact hL τ a l (not_lt.1 ha) hl
      · refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => if_neg ?_
        intro e; simp only [Prod.mk.injEq] at e; exact h ⟨e.1, e.2.1⟩

end GlobalTheory.CompactHarm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockTargetGlActionCompactPreservesJointHarmonicsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockTargetGlAction_compact_preserves_jointHarmonics : ∀ (D : D7) (n m : ℕ) (p : D.what₂.Tau → ℕ) (P : PolF D m n), (∀ (τ' : D.what₂.Tau) (i l : Fin m), p τ' ≤ (i : ℕ) → (l : ℕ) < p τ' → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ' (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ')) (Matrix.single i l (1 : ℂ)) (P) = 0) → ∀ (τ : D.what₂.Tau) (a b : Fin m), ((a : ℕ) < p τ ↔ (b : ℕ) < p τ) → ∀ (τ' : D.what₂.Tau) (i l : Fin m), p τ' ≤ (i : ℕ) → (l : ℕ) < p τ' → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ' (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ')) (Matrix.single i l (1 : ℂ)) (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) (Matrix.single a b (1 : ℂ)) P) = 0 := by
  first | exact @GlobalTheory.CompactHarm.fockT_compact_harm | exact GlobalTheory.CompactHarm.fockT_compact_harm | (intros; apply GlobalTheory.CompactHarm.fockT_compact_harm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockPolynomialSubstitutionCommuteTargetGlAction
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockPolynomialSubstitutionCommuteTargetGlAction
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.ExportSeries GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes

noncomputable section
open MvPolynomial

namespace GlobalTheory.FockSubstComm

variable {D : D7} {m n : ℕ}

def rowMat (p : D.what₂.Tau → ℕ) (g : GLR D n) (τ : D.what₂.Tau) (i : Fin m) : Matrix (Fin n) (Fin n) ℂ :=
  if (i : ℕ) < p τ then ((g τ)⁻¹).val else ((g τ).val)ᵀ

theorem fockSubst_X (p : D.what₂.Tau → ℕ) (g : GLR D n) (v : FVar D m n) :
    fockSubst p g (X v) = ∑ b, C (rowMat p g v.1 v.2.1 v.2.2 b) * X (v.1, v.2.1, b) := by
  rw [fockSubst, aeval_X, rowMat]
  split_ifs <;> simp

open Classical in
theorem pderiv_fockSubst_X (p : D.what₂.Tau → ℕ) (g : GLR D n) (τ : D.what₂.Tau) (i : Fin m) (b : Fin n)
    (u : FVar D m n) :
    pderiv (τ, i, b) (fockSubst p g (X u)) = if u.1 = τ ∧ u.2.1 = i then C (rowMat p g τ i u.2.2 b) else 0 := by
  rw [fockSubst_X]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Derivation.leibniz, pderiv_C, smul_zero, add_zero, pderiv_X, smul_eq_mul]
  split_ifs with h
  · obtain ⟨h1, h2⟩ := h
    subst h1; subst h2
    rw [Finset.sum_eq_single b]
    · simp [Pi.single_apply]
    · intro c _ hc; simp [Pi.single_apply, Prod.ext_iff, hc]
    · simp
  · refine Finset.sum_eq_zero fun c _ => ?_
    have : (u.1, u.2.1, c) ≠ (τ, i, b) := by
      intro e; simp [Prod.ext_iff] at e; exact h ⟨e.1, e.2.1⟩
    simp [Pi.single_apply, this]

theorem chain_X (p : D.what₂.Tau → ℕ) (g : GLR D n) (τ : D.what₂.Tau) (i : Fin m) (c : Fin n)
    (C' : Matrix (Fin n) (Fin n) ℂ) (hC : rowMat p g τ i * C' = 1) (u : FVar D m n) :
    fockSubst p g (pderiv (τ, i, c) (X u)) = ∑ b, C' b c • pderiv (τ, i, b) (fockSubst p g (X u)) := by
  classical
  simp only [pderiv_fockSubst_X]
  rw [pderiv_X]
  by_cases h : u.1 = τ ∧ u.2.1 = i
  · simp only [if_pos h]
    have e : (∑ b, C' b c • C (rowMat p g τ i u.2.2 b) : PolF D m n) = C ((rowMat p g τ i * C') u.2.2 c) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Matrix.mul_apply, map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [smul_eq_C_mul, ← map_mul, mul_comm]
    rw [e, hC]
    obtain ⟨u1, u2, u3⟩ := u
    obtain ⟨h1, h2⟩ := h
    simp only at h1 h2
    subst h1; subst h2
    by_cases h3 : u3 = c
    · subst h3; simp
    · have : ((u1, u2, u3) : FVar D m n) ≠ (u1, u2, c) := by simp [h3]
      simp [Pi.single_apply, this, Matrix.one_apply, h3]
  · simp only [if_neg h, smul_zero, Finset.sum_const_zero]
    have : u ≠ (τ, i, c) := by
      rintro rfl; exact h ⟨rfl, rfl⟩
    simp [Pi.single_apply, this]

theorem chain (p : D.what₂.Tau → ℕ) (g : GLR D n) (τ : D.what₂.Tau) (i : Fin m) (c : Fin n)
    (C' : Matrix (Fin n) (Fin n) ℂ) (hC : rowMat p g τ i * C' = 1) (P : PolF D m n) :
    fockSubst p g (pderiv (τ, i, c) P) = ∑ b, C' b c • pderiv (τ, i, b) (fockSubst p g P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [pderiv_C]
  | add P Q hP hQ =>
    simp only [map_add (f := _), hP, hQ, smul_add, Finset.sum_add_distrib]
  | mul_X P u ih =>
    simp only [Derivation.leibniz, smul_eq_mul, map_add (f := _), map_mul, smul_add, Finset.sum_add_distrib]
    rw [ih, chain_X p g τ i c C' hC u, Finset.mul_sum, Finset.mul_sum]
    simp only [mul_smul_comm]

theorem rai_comm (p : D.what₂.Tau → ℕ) (g : GLR D n) (τ : D.what₂.Tau) (i : Fin m) (c : Fin n) :
    (fockSubst p g).toLinearMap * raiO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) i c =
      ∑ b, ((g τ)⁻¹).val c b • (raiO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) i b *
        (fockSubst p g).toLinearMap) := by
  refine LinearMap.ext fun P => ?_
  by_cases h : (i : ℕ) < p τ
  · simp only [raiO, sgn, h, decide_true, if_true, one_smul, Module.End.mul_apply, AlgHom.toLinearMap_apply,
      LinearMap.mulLeft_apply, map_mul, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]
    rw [fockSubst_X, Finset.sum_mul]
    dsimp only
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [rowMat, h, smul_eq_C_mul, mul_assoc]
  · have hC : rowMat p g τ i * (((g τ)⁻¹).val)ᵀ = 1 := by
      rw [rowMat, if_neg h, ← Matrix.transpose_mul]
      simp
    simp only [raiO, sgn, h, decide_false, if_true, one_smul, Module.End.mul_apply, AlgHom.toLinearMap_apply,
      LinearMap.neg_apply, map_neg, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply,
      Derivation.coeFn_coe, Bool.false_eq_true, if_false]
    rw [chain p g τ i c _ hC, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [smul_neg]

theorem low_comm (p : D.what₂.Tau → ℕ) (g : GLR D n) (τ : D.what₂.Tau) (l : Fin m) (c : Fin n) :
    (fockSubst p g).toLinearMap * lowO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) l c =
      ∑ b, (g τ).val b c • (lowO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) l b *
        (fockSubst p g).toLinearMap) := by
  refine LinearMap.ext fun P => ?_
  by_cases h : (l : ℕ) < p τ
  · have hC : rowMat p g τ l * (g τ).val = 1 := by
      rw [rowMat, if_pos h]
      simp
    simp only [lowO, sgn, h, decide_true, if_true, one_smul, Module.End.mul_apply, AlgHom.toLinearMap_apply,
      LinearMap.sum_apply, LinearMap.smul_apply, Derivation.coeFn_coe]
    rw [chain p g τ l c _ hC]
  · simp only [lowO, sgn, h, decide_false, if_true, one_smul, Module.End.mul_apply, AlgHom.toLinearMap_apply,
      LinearMap.mulLeft_apply, map_mul, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply,
      Bool.false_eq_true, if_false]
    rw [fockSubst_X, Finset.sum_mul]
    dsimp only
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [rowMat, h, smul_eq_C_mul, mul_assoc]

theorem pair_comm (p : D.what₂.Tau → ℕ) (g : GLR D n) (τ : D.what₂.Tau) (i l : Fin m) :
    Commute (fockSubst p g).toLinearMap
      (∑ j, raiO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) i j *
        lowO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) l j) := by
  set σ := (fockSubst p g).toLinearMap
  set R := raiO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) i
  set L := lowO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) l
  have hR : ∀ c, σ * R c = ∑ b, ((g τ)⁻¹).val c b • (R b * σ) := rai_comm p g τ i
  have hL : ∀ c, σ * L c = ∑ b, (g τ).val b c • (L b * σ) := low_comm p g τ l
  have hGG : ∀ c b, ∑ j, (g τ).val c j * ((g τ)⁻¹).val j b = (1 : Matrix (Fin n) (Fin n) ℂ) c b := by
    intro c b
    rw [← Matrix.mul_apply]
    simp
  unfold Commute SemiconjBy
  calc σ * ∑ j, R j * L j
      = ∑ j, ∑ b, ∑ c, (((g τ)⁻¹).val j b * (g τ).val c j) • (R b * L c * σ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← mul_assoc, hR, Finset.sum_mul]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [smul_mul_assoc, mul_assoc, hL, Finset.mul_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [mul_smul_comm, smul_smul, ← mul_assoc]
    _ = ∑ b, ∑ c, (∑ j, (g τ).val c j * ((g τ)⁻¹).val j b) • (R b * L c * σ) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_smul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_comm]
    _ = (∑ j, R j * L j) * σ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun b _ => ?_
        simp only [hGG, Matrix.one_apply, ite_smul, one_smul, zero_smul]
        rw [Finset.sum_ite_eq']
        simp

theorem fockSubst_fockT (D : D7) (m n : ℕ) (p : D.what₂.Tau → ℕ) (g : GLR D n) (τ : D.what₂.Tau)
    (Y : Matrix (Fin m) (Fin m) ℂ) (P : PolF D m n) :
    fockSubst p g (fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) Y P) =
      fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) Y (fockSubst p g P) := by
  have hc : Commute (fockSubst p g).toLinearMap
      (fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) Y) := by
    unfold fockT
    refine Commute.sum_right _ _ _ fun i _ => Commute.sum_right _ _ _ fun l _ => Commute.smul_right ?_ _
    rw [Finset.sum_add_distrib]
    refine Commute.add_right (pair_comm p g τ i l) (Commute.sum_right _ _ _ fun j _ => ?_)
    split_ifs
    · exact Commute.smul_right (Commute.one_right _) _
    · exact Commute.zero_right _
  have := LinearMap.congr_fun hc.eq P
  simpa only [Module.End.mul_apply, AlgHom.toLinearMap_apply] using this

end GlobalTheory.FockSubstComm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockPolynomialSubstitutionCommuteTargetGlActionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.ExportSeries GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockPolynomialSubstitution_commute_targetGlAction : ∀ (D : D7) (m n : ℕ) (p : D.what₂.Tau → ℕ) (g : GLR D n) (τ : D.what₂.Tau) (Y : Matrix (Fin m) (Fin m) ℂ) (P : PolF D m n), fockSubst p g (fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) Y P) = fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) Y (fockSubst p g P) := by
  first | exact @GlobalTheory.FockSubstComm.fockSubst_fockT | exact GlobalTheory.FockSubstComm.fockSubst_fockT | (intros; apply GlobalTheory.FockSubstComm.fockSubst_fockT <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalPreimageOfSupportedAtPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalPreimageOfSupportedAtPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift

theorem suppF_finIdem_mem_range : ∀ (D : D7) (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : AE D), IsFinIdem D v f → ∀ k : GA D V, SuppF V f k → ∃ a : GlobalTheory.FinZeta.Gv V v, GlobalTheory.FinZeta.embV V v a = k := by
  intro D V v f hf k hk
  obtain ⟨ε, hε, rfl⟩ := hf
  obtain ⟨a, ha⟩ := (GlobalTheory.AdelicU.Supp.suppF_iff_mem_range V hε k).1 hk
  exact ⟨a, ha⟩

end GlobalTheory.RawLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalPreimageOfSupportedAtPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_preimage_of_supportedAtPlace : ∀ (D : D7) (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : AE D), IsFinIdem D v f → ∀ k : GA D V, SuppF V f k → ∃ a : GlobalTheory.FinZeta.Gv V v, GlobalTheory.FinZeta.embV V v a = k := by
  first | exact @GlobalTheory.RawLift.suppF_finIdem_mem_range | exact GlobalTheory.RawLift.suppF_finIdem_mem_range | (intros; apply GlobalTheory.RawLift.suppF_finIdem_mem_range <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypePlacesMemPlacesOverGenerators
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypePlacesMemPlacesOverGenerators
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypePlacesOver

theorem mem_placesOver : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (F3 : Face3 D A3), Rl.Char3 F3 → ∀ P ∈ Rl.Pg, ∃ k, P ∈ placesOver D.host.E (D.host.g k) := by
  intro D Γ _ _ Pl0 I0 T A3 Ks _ _ _ Rl F3 hC P hP
  obtain ⟨k, hk⟩ := (hC.lev.Pg P).1 hP
  refine ⟨k, ?_⟩
  have h1 := Rl.C.P.pb_over k
  rw [← hk] at h1
  have h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) (D.host.g k : ℕ) ∈ P.asIdeal := h1
  simpa [placesOver] using h2

end GlobalTheory.TypePlacesOver
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypePlacesMemPlacesOverGeneratorsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typePlaces_mem_placesOver_generators : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (F3 : Face3 D A3), Rl.Char3 F3 → ∀ P ∈ Rl.Pg, ∃ k, P ∈ placesOver D.host.E (D.host.g k) := by
  first | exact @GlobalTheory.TypePlacesOver.mem_placesOver | exact GlobalTheory.TypePlacesOver.mem_placesOver | (intros; apply GlobalTheory.TypePlacesOver.mem_placesOver <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointFrameIntegralIffPartsConjHalf
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointFrameIntegralIffPartsConjHalf
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.ConjHalfSplitInt

theorem frMapAdj_int_iff : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (Pg Q : Finset (Pl D.host.E)) (eg eQ : AE D), IsIdemSum eg Pg → IsIdemSum eQ Q → Disjoint Pg Q → IsIdemSum (eg + eQ) (Pg ∪ Q) → ∀ x : WO S T, IsHalf (cA D (eg + eQ)) x → (IsIntM (frMapAdj S T βS βT x) ↔ IsIntM (frMapAdj S T βS βT (cA D eg • x)) ∧ IsIntM (frMapAdj S T βS βT (cA D eQ • x))) := by
  intro D S T βS βT Pg Q eg eQ hg hQ _ _ x hx
  have hx' : cA D (eg + eQ) • x = x := (GlobalTheory.ExportSeries.RestrictHalfModel.isHalf_iff' _ _).1 hx
  have hsplit : x = cA D eg • x + cA D eQ • x := by rw [← add_smul, ← map_add (f := _), hx']
  have hA : ∀ e : AE D, frMapAdj S T βS βT (cA D e • x) = toEAf D e • frMapAdj S T βS βT x := fun e => by
    rw [GlobalTheory.RedHalfDrop.frMapAdj_smul_eq, Formalism.L2.Theta.cA_cA]
  have hint : ∀ (e : AE D) (P : Finset (Pl D.host.E)), IsIdemSum e P →
      toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun e P h => by
    rw [← GlobalTheory.ExportSeries.idem_eq h]
    unfold GlobalTheory.ExportSeries.idem
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact sum_mem fun PP hPP => GlobalTheory.RedHalfDrop.int_idemAt ⟨e, h⟩ hPP
  constructor
  · intro h
    rw [hA, hA]
    exact ⟨fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact mul_mem (hint _ _ hg) (h i j),
      fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact mul_mem (hint _ _ hQ) (h i j)⟩
  · rintro ⟨h1, h2⟩
    rw [hsplit, GlobalTheory.PlaceVec.frMapAdj_add]
    intro i j
    rw [Matrix.add_apply]
    exact add_mem (h1 i j) (h2 i j)

end GlobalTheory.ConjHalfSplitInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointFrameIntegralIffPartsConjHalfStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjointFrame_integral_iff_parts_conj_half : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (Pg Q : Finset (Pl D.host.E)) (eg eQ : AE D), IsIdemSum eg Pg → IsIdemSum eQ Q → Disjoint Pg Q → IsIdemSum (eg + eQ) (Pg ∪ Q) → ∀ x : WO S T, IsHalf (cA D (eg + eQ)) x → (IsIntM (frMapAdj S T βS βT x) ↔ IsIntM (frMapAdj S T βS βT (cA D eg • x)) ∧ IsIntM (frMapAdj S T βS βT (cA D eQ • x))) := by
  first | exact @GlobalTheory.ConjHalfSplitInt.frMapAdj_int_iff | exact GlobalTheory.ConjHalfSplitInt.frMapAdj_int_iff | (intros; apply GlobalTheory.ConjHalfSplitInt.frMapAdj_int_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionAdjointFrameConjHalfTwoParts
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionAdjointFrameConjHalfTwoParts
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.TwoStepRed

theorem redM_part_eq {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (EAf D))
    (βT : GL (Fin T.rank) (EAf D)) (P R : Finset (Pl D.host.E)) (e f : AE D)
    (hP : IsIdemSum e P) (hR : IsIdemSum f R) (hd : Disjoint P R) (x : WO S T)
    (hx : IsHalf (cA D (e + f)) x) (hN : IsIntM (frMapAdj S T βS βT x)) :
    ∀ PP ∈ P, redM PP (frMapAdj S T βS βT (cA D e • x)) = redM PP (frMapAdj S T βS βT x) := by
  intro PP hPP
  have hsplit : x = cA D e • x + cA D f • x := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [← add_mul, ← map_add (f := _), hx i j]
  have h1 : frMapAdj S T βS βT x
      = frMapAdj S T βS βT (cA D e • x) + toEAf D f • frMapAdj S T βS βT x := by
    conv_lhs => rw [hsplit]
    rw [GlobalTheory.PlaceVec.frMapAdj_add, GlobalTheory.RedHalfDrop.frMapAdj_smul_eq βS βT (cA D f) x, cA_cA]
  have hc : toEAf D f ∈ Formalism.L2.Herm.intAf (↥D.host.F) D.host.E := by
    rw [← GlobalTheory.ExportSeries.idem_eq hR]
    unfold GlobalTheory.ExportSeries.idem
    set_option synthInstance.maxHeartbeats 100000 in
      rw [show (toEAf D) (∑ Q ∈ R, GlobalTheory.ExportSeries.idemAt Q) = ∑ Q ∈ R, (toEAf D) (GlobalTheory.ExportSeries.idemAt Q) from
      map_sum (toEAf D).toAddMonoidHom _ _]
    exact sum_mem (fun Q hQ => GlobalTheory.RedHalfDrop.int_idemAt ⟨f, hR⟩ hQ)
  rw [eq_sub_of_add_eq h1.symm]
  exact GlobalTheory.RedHalfDrop.redM_sub_smul PP hN hc
    (GlobalTheory.AdjRedOff.resS_idemSum_eq_zero hR hc (fun h => Finset.disjoint_left.mp hd hPP h))

theorem redM_twoStep : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (Pg Q : Finset (Pl D.host.E)) (eg eQ : AE D), IsIdemSum eg Pg → IsIdemSum eQ Q → Disjoint Pg Q → IsIdemSum (eg + eQ) (Pg ∪ Q) → ∀ x : WO S T, IsHalf (cA D (eg + eQ)) x → IsIntM (frMapAdj S T βS βT x) → (∀ PP ∈ Pg, redM PP (frMapAdj S T βS βT (cA D eg • x)) = redM PP (frMapAdj S T βS βT x)) ∧ (∀ PP ∈ Q, redM PP (frMapAdj S T βS βT (cA D eQ • x)) = redM PP (frMapAdj S T βS βT x)) := by
  intro D S T βS βT Pg Q eg eQ hg hQ hd _ x hx hN
  exact ⟨redM_part_eq S T βS βT Pg Q eg eQ hg hQ hd x hx hN,
    redM_part_eq S T βS βT Q Pg eQ eg hQ hg hd.symm x (by rwa [add_comm]) hN⟩

end GlobalTheory.TwoStepRed
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionAdjointFrameConjHalfTwoPartsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_adjointFrame_conj_half_two_parts : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (Pg Q : Finset (Pl D.host.E)) (eg eQ : AE D), IsIdemSum eg Pg → IsIdemSum eQ Q → Disjoint Pg Q → IsIdemSum (eg + eQ) (Pg ∪ Q) → ∀ x : WO S T, IsHalf (cA D (eg + eQ)) x → IsIntM (frMapAdj S T βS βT x) → (∀ PP ∈ Pg, redM PP (frMapAdj S T βS βT (cA D eg • x)) = redM PP (frMapAdj S T βS βT x)) ∧ (∀ PP ∈ Q, redM PP (frMapAdj S T βS βT (cA D eQ • x)) = redM PP (frMapAdj S T βS βT x)) := by
  first | exact @GlobalTheory.TwoStepRed.redM_twoStep | exact GlobalTheory.TwoStepRed.redM_twoStep | (intros; apply GlobalTheory.TwoStepRed.redM_twoStep <;> assumption)
end
end
