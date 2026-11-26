module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.BaseIntSet
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsOfHyp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUniformizerTorusTranslateUnipotentQuoti
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLettersHarmMemHHa
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictionLineOperatorSum

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.LevelSeries

variable {D : D7}

def trSp (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (f₀ : WO V W → ℂ) (e : AE D) (M : ℕ) (O : Subring ℂ) :
    Submodule O (WO V W → ℂ) :=
  Submodule.span O {f | ∃ y : WO V W, IsHalf e y ∧ M • y ∈ latO V W ΛV ΛW (fun _ => True) ∧ f = heisO ψ V W y f₀}

abbrev stdF (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D)
    (sW BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f : WO V W → ℂ) :
    MvPolynomial (FVar D W.rank V.rank) ℂ →ₗ[ℂ] (WO V W → ℂ) :=
  pureTensorO ψ θ V W (fun _ => 1) sW (fun _ => 1) BW f

def OneAt (V : HSp D) (l : ℕ) (h : GA D V) : Prop :=
  ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε → ((l : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal →
    ∀ a b, algebraMap (AF D.host.F) (AE D) ε * (Formalism.L2.Theta.mt V h - 1) a b = 0

def ChiData (χW : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (b : ℕ) : Prop :=
  ChrEq χW χ ∧ (∀ Q : HeightOneSpectrum (𝓞 D.host.E), ((b : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal → χ.UnrAt Q) ∧
    ∀ Q : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.IdemSupport.cP Q ≠ Q → ∀ k, χ.resFin (Q.under (𝓞 D.host.F)) k = 1

def ValRing {k : Type} [Field k] [NumberField k] (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) (O : Subring ℂ) : Prop :=
  ∀ x : k, la.valuation k x ≤ 1 → σ x ∈ O

def locRing {k : Type} [Field k] [NumberField k] (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) : Subring ℂ :=
  (la.valuation k).integer.map σ

theorem valRing_locRing {k : Type} [Field k] [NumberField k] (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) :
    ValRing σ la (locRing σ la) := fun x hx => ⟨x, hx, rfl⟩

theorem valRing_range {k : Type} [Field k] [NumberField k] (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) :
    ValRing σ la σ.range := fun x _ => ⟨x, rfl⟩

def ConjIn (D : D7) {k : Type} [Field k] (σ : k →+* ℂ) : Prop := ∀ (τ : D.host.E →+* ℂ) (a : D.host.E), ∃ x, σ x = τ a

def DenomAt {E : Type} [Field E] {n : ℕ} (l c : ℕ) (γ : GL (Fin n) E) : Prop :=
  ∃ m : ℕ, Nat.Coprime m l ∧ ∀ a b, IsIntegral ℤ (((m * l ^ c : ℕ) : E) * γ.val a b) ∧
    IsIntegral ℤ (((m * l ^ c : ℕ) : E) * γ⁻¹.val a b)

theorem oneAt_one (V : HSp D) (l : ℕ) : OneAt V l 1 := fun _ _ _ _ a b => by
  have h1 : Formalism.L2.Theta.mt V 1 = 1 := by unfold Formalism.L2.Theta.mt; rw [map_one]; rfl
  rw [h1, sub_self]
  simp

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m)
  (hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i)

def BaseCc (ph : ℂ) : Prop :=
  CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) T.σ₀) (castDict hV (T.dict ((i : ℕ) + 1) T.σ₀))
    (castDict hV (T.mu ((i : ℕ) + 1) T.σ₀)) (T.x₀ ((i : ℕ) + 1) T.σ₀) (R.ωP i A.μ0) (R.vacP i)
    fun k => ph * T.cE ((i : ℕ) + 1) T.σ₀ k

def CovCc (ph : ℂ) (C : Cover T ((i : ℕ) + 1) T.σ₀) : Prop :=
  CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) C.U₂ (castDict hV C.dict₂)
    (castDict hV (T.mu ((i : ℕ) + 1) T.σ₀)) (T.x₀ ((i : ℕ) + 1) T.σ₀) (R.ωP i A.μ0) (R.vacP i)
    fun k => ph * C.cc₂ k

end GlobalTheory.LevelSeries

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActOfMemGfC
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries GlobalTheory.ConjTwist
open Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoefActIo

variable {D : D7}

section Gen

variable {S T : HSp D}

theorem om_fock_of_vac {B : Base S T} {ψ : Twist D Circle} {ω : PairRep S T} (hB : B.Good) (hψ : ψ.Good)
    (hω : B.IsWeil ψ.chi ω) {f : WO S T → ℂ} (hf : IsThetaFunO B.F.ψ S T f)
    (hv : ∀ τ, IsFockVacAt (heisO B.F.ψ S T) B.F.θ τ (cplxO 1 (B.F.sT τ)) f) {u : GA D S} (hu : u ∈ GinfC S)
    (P : PolF D T.rank S.rank) : ω (u, 1) (B.F.fock f P) = B.F.fock f (B.act u P) := by
  have hθ := hB.frame.vac.2.inf
  have hBS := fun τ => GlobalTheory.RealFockAction.onb_posDef (hB.frame.onbS τ)
  have one : ∀ τ, compAt B.F.θ τ (Formalism.L2.Theta.mt T 1) = 1 := fun τ => GlobalTheory.PointAtPlaceHom.infMat_one T _
  have eu : ∀ τ, (inBasis B.F.BS (realGL B.F.θ S u) τ).val =
      (B.F.BS τ).val⁻¹ * compAt B.F.θ τ (Formalism.L2.Theta.mt S u) * (B.F.BS τ).val := fun τ => by
    rw [← Matrix.coe_units_inv]
    rfl
  have hle : ∀ τ, B.w.p τ ≤ T.rank := fun τ => by
    obtain ⟨e, -⟩ := hB.sigOK (tauE D τ)
    rw [← hB.sig τ] at e
    have := Fintype.card_congr e
    simp only [Fintype.card_fin, Fintype.card_sum] at this
    omega
  unfold Frame.fock
  rw [(GlobalTheory.OrientedHeis.om_pureTensorO D _ _ S T _ _ ω hω hθ (fun _ => 1) (fun _ => 1) (fun τ => (B.F.BS τ).val)
    (fun τ => (B.F.BS τ).val * (inBasis B.F.BS (realGL B.F.θ S u) τ).val) B.F.sT B.F.sT B.F.BT B.F.BT u 1
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) (fun τ => by rw [one, one_mul, mul_one])
    (fun τ => by rw [eu, ← Matrix.coe_units_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul])
    (fun τ => by rw [one, one_mul]) _ hf P).2, GlobalTheory.RealFockAction.om_vac hB hψ hω hf hv hu,
    GlobalTheory.FiniteFock.pureTensorO_smul,
    GlobalTheory.RealFockAction.pureTensorO_subst (p := B.w.p) hB.frame.vac.1 hθ
      (fun τ => GlobalTheory.FockBasis.isCartanInv_one (hBS τ)) hB.frame.cartT
      (fun τ => (GlobalTheory.RealFockAction.onb_laws (by have := hB.frame.onbT τ; rwa [← hB.sig τ] at this) (hle τ)).1) _ _
      (fun τ => by rw [eu]; exact GlobalTheory.RealFockAction.conj_unitary (hBS τ) (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ S u τ)) hf,
    Base.act, MonoidHom.comp_apply, fockGL_apply, LinearMap.map_smul]

theorem act_of_mem_GfC (B : Base S T) {k : GA D S} (hk : k ∈ GfC S) : B.act k = 1 := by
  have e : realGL B.F.θ S k = 1 := by
    funext τ
    change (Formalism.UG.bc (B.F.θ τ)) (infHom S k) = 1
    rw [show infHom S k = 1 from hk, map_one]
  rw [Base.act, MonoidHom.comp_apply, e, map_one]

end Gen

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} {i : Fin D.R.m}

theorem thetaVector_laws (hC : GlobalTheory.Hk3.Core R F) (t : T0) :
    IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) ∧
      (∀ ρ, IsFockVacAt (heisO R.ψ (Vc D i) (Wc D i)) R.θ ρ (cplxO 1 (cart (R.MW i (sg0 D A)) ρ)) (R.vP i t)) ∧
      Function.Injective (R.ptP i t) := by
  have hP := hC.thP
  have hM := hC.models
  have hf : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have h := hP.pt_theta i t 1
    have e : R.ptP i t 1 = R.vP i t := by
      unfold RealDat.ptP pureTensorO pureTensorL
      rw [show (1 : PolF D (Wc D i).rank (Vc D i).rank) = MvPolynomial.basisMonomials _ ℂ 0 from rfl,
        Module.Basis.constr_basis]
      simp [opPow]
    rwa [e] at h
  have hv := GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hP.vP i t) hf
  have hne : R.vP i t ≠ 0 :=
    GlobalTheory.AdTh.VecNe.thPVec_ne_zero (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βV i))
      (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βW i))
      ((D.sp.W_rank _ (Nat.le_add_left _ _) i.2).trans_le (r_le_V i)) (hP.vP i t)
  exact ⟨hf, hv, GlobalTheory.FockIndep.pureTensorO_injective D R.ψ R.θ _ _ _ (R.MW i (sg0 D A)) (R.BV i) _
    (hP.ωP i t).std hM.inf (fun τ => GlobalTheory.OneMapRef.VecP.isCartanInv_one_of_onb (hM.BV i τ)) (hM.BV i) hf hne hv⟩

theorem act_ioP_inf (hC : GlobalTheory.Hk3.Core R F) {B : Base (Vc D i) (Wc D i)} (hB : B.Good) (h : BaseOf R i B)
    {ψ : Twist D Circle} (hψ : ψ.Good) {t : T0} (ht : IsTupOf R B ψ t) :
    ∀ u ∈ GinfC (Vc D i), ∀ x w, B.act u (R.ioP i x w) = R.ioP i x ((R.cV i).ρ u w) := by
  intro u hu x w
  obtain ⟨hf, hv, hinj⟩ := thetaVector_laws (i := i) hC t
  have hω := h.isWeil hC.thP.ωP ht
  have hpt : ∀ P, R.ptP i t P = B.F.fock (R.vP i t) P := fun P => by rw [h.fock_eq]; rfl
  have hf' : IsThetaFunO B.F.ψ (Vc D i) (Wc D i) (R.vP i t) := by rw [h.ψ]; exact hf
  have hv' : ∀ τ, IsFockVacAt (heisO B.F.ψ (Vc D i) (Wc D i)) B.F.θ τ (cplxO 1 (B.F.sT τ)) (R.vP i t) := by
    rw [h.ψ, h.θ, h.sT]; exact hv
  apply hinj
  rw [hpt, hpt, ← om_fock_of_vac hB hψ hω hf' hv' hu, ← hpt, ← hpt]
  exact (hC.thP.ioP i t).1 u hu x w

theorem act_ioP (hC : GlobalTheory.Hk3.Core R F) {B : Base (Vc D i) (Wc D i)} (hB : B.Good) (h : BaseOf R i B)
    {ψ : Twist D Circle} (hψ : ψ.Good) {t : T0} (ht : IsTupOf R B ψ t) :
    (∀ u ∈ GinfC (Vc D i), ∀ x w, B.act u (R.ioP i x w) = R.ioP i x ((R.cV i).ρ u w)) ∧
      ∀ (u : GA D (Vc D i)) x w, B.act u (R.ioP i x w) = R.ioP i x ((R.cV i).ρ u w) := by
  refine ⟨act_ioP_inf hC hB h hψ ht, fun u x w => ?_⟩
  have e := GlobalTheory.AutMult.toInf_mul_toFin u
  set a := GlobalTheory.AutMult.toInf (Vc D i) u
  set k := GlobalTheory.AutMult.toFin (Vc D i) u
  rw [← e, map_mul, map_mul, act_of_mem_GfC B k.2, (hC.models.cV i).1 _ k.2, mul_one, mul_one]
  exact act_ioP_inf hC hB h hψ ht _ a.2 x w

end GlobalTheory.CoefActIo

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CellLintegral
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumUnfoldingOfComplexInvariantIntegrable
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumUnfoldingOfComplexInvariantIntegrable
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

namespace GlobalTheory.UnfoldCplx

variable {α ι : Type} [MeasurableSpace α] [Countable ι]

theorem integrable_comp {μ : Measure α} {𝓕 A : Set α} {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {T : ι → α → α} (hT : ∀ i, Measurable (T i)) {H : Set (α → α)}
    (hU : ∀ f : α → ℝ≥0∞, Measurable f → (∀ h ∈ H, ∀ x, f (h x) = f x) →
      ∫⁻ x in 𝓕, f x ∂μ = ∑' i, ENNReal.ofReal (c i) * ∫⁻ x in A, f (T i x) ∂μ)
    {B : α → ℂ} (hB : Measurable B) (hBi : Integrable B (μ.restrict 𝓕))
    (hH : ∀ h ∈ H, ∀ x, B (h x) = B x) (i : ι) :
    Integrable (fun x => B (T i x)) (μ.restrict A) := by
  refine ⟨(hB.comp (hT i)).aestronglyMeasurable, ?_⟩
  have h1 := hU (fun x => ‖B x‖ₑ) hB.enorm (fun h hh x => by simp [hH h hh x])
  have hfin : ∫⁻ x in 𝓕, ‖B x‖ₑ ∂μ < ∞ := hBi.2
  have hle : ENNReal.ofReal (c i) * ∫⁻ x in A, ‖B (T i x)‖ₑ ∂μ ≤ ∫⁻ x in 𝓕, ‖B x‖ₑ ∂μ := by
    rw [h1]; exact ENNReal.le_tsum (f := fun i => ENNReal.ofReal (c i) * ∫⁻ x in A, ‖B (T i x)‖ₑ ∂μ) i
  have hne : ENNReal.ofReal (c i) ≠ 0 := by simpa using hc i
  show ∫⁻ x in A, ‖B (T i x)‖ₑ ∂μ < ∞
  by_contra hh
  rw [not_lt, top_le_iff] at hh
  rw [hh, ENNReal.mul_top hne] at hle
  exact absurd (lt_of_le_of_lt hle hfin) (lt_irrefl _)

theorem hasSum_nonneg {μ : Measure α} {𝓕 A : Set α} {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {T : ι → α → α} (hT : ∀ i, Measurable (T i)) {H : Set (α → α)}
    (hU : ∀ f : α → ℝ≥0∞, Measurable f → (∀ h ∈ H, ∀ x, f (h x) = f x) →
      ∫⁻ x in 𝓕, f x ∂μ = ∑' i, ENNReal.ofReal (c i) * ∫⁻ x in A, f (T i x) ∂μ)
    {g : α → ℝ} (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) (hgi : Integrable g (μ.restrict 𝓕))
    (hH : ∀ h ∈ H, ∀ x, g (h x) = g x) :
    HasSum (fun i => c i * ∫ x in A, g (T i x) ∂μ) (∫ x in 𝓕, g x ∂μ) := by
  have h1 := hU (fun x => ENNReal.ofReal (g x)) hg.ennreal_ofReal (fun h hh x => by simp [hH h hh x])
  have hfin : ∫⁻ x in 𝓕, ENNReal.ofReal (g x) ∂μ ≠ ∞ := (hgi.lintegral_lt_top).ne
  set F : ι → ℝ≥0∞ := fun i => ENNReal.ofReal (c i) * ∫⁻ x in A, ENNReal.ofReal (g (T i x)) ∂μ with hF
  have hsum : ∑' i, F i ≠ ∞ := by rw [← h1]; exact hfin
  have hFi : ∀ i, F i ≠ ∞ := ENNReal.ne_top_of_tsum_ne_top hsum
  have key := ENNReal.hasSum_toReal hsum
  rw [← ENNReal.tsum_toReal_eq hFi, ← h1, ← integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall hg0) hg.aestronglyMeasurable] at key
  convert key using 1
  funext i
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun x => hg0 _))
    (hg.comp (hT i)).aestronglyMeasurable]
  simp [F, ENNReal.toReal_mul, (hc i).le]

theorem hasSum_real {μ : Measure α} {𝓕 A : Set α} {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {T : ι → α → α} (hT : ∀ i, Measurable (T i)) {H : Set (α → α)}
    (hU : ∀ f : α → ℝ≥0∞, Measurable f → (∀ h ∈ H, ∀ x, f (h x) = f x) →
      ∫⁻ x in 𝓕, f x ∂μ = ∑' i, ENNReal.ofReal (c i) * ∫⁻ x in A, f (T i x) ∂μ)
    {g : α → ℝ} (hg : Measurable g) (hgi : Integrable g (μ.restrict 𝓕))
    (hgA : ∀ i, Integrable (fun x => g (T i x)) (μ.restrict A))
    (hH : ∀ h ∈ H, ∀ x, g (h x) = g x) :
    HasSum (fun i => c i * ∫ x in A, g (T i x) ∂μ) (∫ x in 𝓕, g x ∂μ) := by
  have hp := hasSum_nonneg hc hT hU (g := fun x => max (g x) 0) (hg.max measurable_const)
    (fun x => le_max_right _ _) hgi.pos_part (fun h hh x => by simp only [hH h hh x])
  have hn := hasSum_nonneg hc hT hU (g := fun x => max (-g x) 0) (hg.neg.max measurable_const)
    (fun x => le_max_right _ _) hgi.neg_part (fun h hh x => by simp only [hH h hh x])
  have hsplit : ∀ y : ℝ, max y 0 - max (-y) 0 = y := fun y => by
    rcases le_total y 0 with h | h
    · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]; ring
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]; ring
  have e1 : ∫ x in 𝓕, g x ∂μ = (∫ x in 𝓕, max (g x) 0 ∂μ) - ∫ x in 𝓕, max (-g x) 0 ∂μ := by
    rw [← integral_sub hgi.pos_part hgi.neg_part]; simp only [hsplit]
  have hf : (fun i => c i * ∫ x in A, g (T i x) ∂μ) = fun i =>
      c i * (∫ x in A, max (g (T i x)) 0 ∂μ) - c i * ∫ x in A, max (-g (T i x)) 0 ∂μ := by
    funext i
    rw [← mul_sub, ← integral_sub (hgA i).pos_part (hgA i).neg_part]; simp only [hsplit]
  rw [e1, hf]
  exact hp.sub hn

theorem hasSum_complex : ∀ {α ι : Type} [MeasurableSpace α] [Countable ι] (μ : Measure α) (𝓕 A : Set α) (c : ι → ℝ), (∀ i, 0 < c i) →
    ∀ (T : ι → α → α), (∀ i, Measurable (T i)) → ∀ (H : Set (α → α)),
    (∀ f : α → ℝ≥0∞, Measurable f → (∀ h ∈ H, ∀ x, f (h x) = f x) →
      ∫⁻ x in 𝓕, f x ∂μ = ∑' i, ENNReal.ofReal (c i) * ∫⁻ x in A, f (T i x) ∂μ) →
    ∀ B : α → ℂ, Measurable B → Integrable B (μ.restrict 𝓕) → (∀ h ∈ H, ∀ x, B (h x) = B x) →
      (∀ i, Integrable (fun x => B (T i x)) (μ.restrict A)) ∧
        HasSum (fun i => (c i : ℂ) * ∫ x in A, B (T i x) ∂μ) (∫ x in 𝓕, B x ∂μ) := by
  intro α ι _ _ μ 𝓕 A c hc T hT H hU B hB hBi hH
  have hBA := integrable_comp hc hT hU hB hBi hH
  refine ⟨hBA, ?_⟩
  rw [Complex.hasSum_iff]
  constructor
  · have := hasSum_real hc hT hU (g := fun x => (B x).re) (Complex.measurable_re.comp hB) hBi.re
      (fun i => (hBA i).re) (fun h hh x => by simp only [hH h hh x])
    have e2 : ∫ x in 𝓕, (B x).re ∂μ = (∫ x in 𝓕, B x ∂μ).re := integral_re hBi
    have hf : (fun i => c i * ∫ x in A, (B (T i x)).re ∂μ) =
        fun i => ((c i : ℂ) * ∫ x in A, B (T i x) ∂μ).re := by
      funext i
      rw [Complex.re_ofReal_mul]; congr 1; exact integral_re (hBA i)
    rw [e2, hf] at this
    exact this
  · have := hasSum_real hc hT hU (g := fun x => (B x).im) (Complex.measurable_im.comp hB) hBi.im
      (fun i => (hBA i).im) (fun h hh x => by simp only [hH h hh x])
    have e2 : ∫ x in 𝓕, (B x).im ∂μ = (∫ x in 𝓕, B x ∂μ).im := integral_im hBi
    have hf : (fun i => c i * ∫ x in A, (B (T i x)).im ∂μ) =
        fun i => ((c i : ℂ) * ∫ x in A, B (T i x) ∂μ).im := by
      funext i
      rw [Complex.im_ofReal_mul]; congr 1; exact integral_im (hBA i)
    rw [e2, hf] at this
    exact this

end GlobalTheory.UnfoldCplx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumUnfoldingOfComplexInvariantIntegrableStatement
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_unfolding_of_complex_invariant_integrable : ∀ {α ι : Type} [MeasurableSpace α] [Countable ι] (μ : Measure α) (𝓕 A : Set α) (c : ι → ℝ), (∀ i, 0 < c i) →
    ∀ (T : ι → α → α), (∀ i, Measurable (T i)) → ∀ (H : Set (α → α)),
    (∀ f : α → ℝ≥0∞, Measurable f → (∀ h ∈ H, ∀ x, f (h x) = f x) →
      ∫⁻ x in 𝓕, f x ∂μ = ∑' i, ENNReal.ofReal (c i) * ∫⁻ x in A, f (T i x) ∂μ) →
    ∀ B : α → ℂ, Measurable B → Integrable B (μ.restrict 𝓕) → (∀ h ∈ H, ∀ x, B (h x) = B x) →
      (∀ i, Integrable (fun x => B (T i x)) (μ.restrict A)) ∧
        HasSum (fun i => (c i : ℂ) * ∫ x in A, B (T i x) ∂μ) (∫ x in 𝓕, B x ∂μ) := by
  first | exact @GlobalTheory.UnfoldCplx.hasSum_complex | exact GlobalTheory.UnfoldCplx.hasSum_complex | (intros; apply GlobalTheory.UnfoldCplx.hasSum_complex <;> assumption)
end
end

noncomputable section
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CellDec
variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem cell_lintegral [MeasurableSpace (GA E n)] [BorelSpace (GA E n)] (μ : Measure (GA E n)) [μ.IsHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 E))) (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ)
    (hϖ : ∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) (𝓕 : Set (GA E n)) (h𝓕 : IsFundamentalDomain (NE E n) 𝓕 μ)
    (B : GA E n → ℝ≥0∞) (hB : Measurable B) (hinv : ∀ u ∈ NA E n, ∀ g, B (u * g) = B g) :
    ∫⁻ g in 𝓕, B g ∂μ =
      ∑' l : abelian₂ E n S, ENNReal.ofReal (dinv n l.1) * ∫⁻ g in 𝓕 ∩ C0 E n S, B (tl n ϖ l.1 * g) ∂μ := by
  have hC : MeasurableSet (C0 E n S) := (GlobalTheory.T.isOpen_C0 E n S).measurableSet
  let cellS : abelian₂ E n S → Set (GA E n) := fun l => {g | (tl n ϖ l.1)⁻¹ * g ∈ C0 E n S}
  have hmeas : ∀ l, MeasurableSet (cellS l) := fun l =>
    ((GlobalTheory.T.isOpen_C0 E n S).preimage (continuous_const.mul continuous_id)).measurableSet
  have hpart : ∀ g, ∑' l : abelian₂ E n S, (cellS l).indicator B g = B g := by
    intro g
    obtain ⟨l0, hl0S, hl0⟩ := GlobalTheory.T.exists_tl_inv_mul_mem_C0_off_finset E n S ϖ hϖ g
    have hz : ∀ l : abelian₂ E n S, l ≠ (⟨l0, hl0S⟩ : abelian₂ E n S) → (cellS l).indicator B g = 0 := fun l hl =>
      Set.indicator_of_notMem (show g ∉ cellS l from fun hg => hl (Subtype.ext (GlobalTheory.T.adelic_iwasawa_cells_disjoint_off_finset E n S ϖ hϖ l.1 l0 g l.2 hl0S hg hl0))) B
    rw [tsum_eq_single _ hz]
    exact Set.indicator_of_mem (show g ∈ cellS ⟨l0, hl0S⟩ from hl0) _
  calc ∫⁻ g in 𝓕, B g ∂μ = ∫⁻ g in 𝓕, ∑' l, (cellS l).indicator B g ∂μ := by simp_rw [hpart]
    _ = ∑' l, ∫⁻ g in 𝓕, (cellS l).indicator B g ∂μ :=
        lintegral_tsum fun l => (hB.indicator (hmeas l)).aemeasurable
    _ = _ := tsum_congr fun l => ?_
  let t := tl n ϖ l.1
  let F : GA E n → ℝ≥0∞ := (C0 E n S).indicator fun h => B (t * h)
  have e : (cellS l).indicator B = fun g => F (t⁻¹ * g) := by
    funext g
    show (cellS l).indicator B g = (C0 E n S).indicator (fun h => B (t * h)) (t⁻¹ * g)
    by_cases hg : t⁻¹ * g ∈ C0 E n S
    · rw [Set.indicator_of_mem (show g ∈ cellS l from hg), Set.indicator_of_mem hg, mul_inv_cancel_left]
    · rw [Set.indicator_of_notMem (show g ∉ cellS l from hg), Set.indicator_of_notMem hg]
  have hF : Measurable F := (hB.comp (measurable_const_mul t)).indicator hC
  have hFinv : ∀ u ∈ NA E n, ∀ g, F (u * g) = F g := by
    intro u hu g
    show (C0 E n S).indicator (fun h => B (t * h)) (u * g) = (C0 E n S).indicator (fun h => B (t * h)) g
    by_cases hg : g ∈ C0 E n S
    · rw [Set.indicator_of_mem (adelicUnitriangular_mul_mem_unipotentTimesIntegral hu hg), Set.indicator_of_mem hg]
      change B (t * (u * g)) = B (t * g)
      rw [show t * (u * g) = (t * u * t⁻¹) * (t * g) by group]
      exact hinv _ (tl_conj_mem ϖ l.1 hu) _
    · have : u * g ∉ C0 E n S := fun h => hg (by simpa using adelicUnitriangular_mul_mem_unipotentTimesIntegral (inv_mem hu) h)
      rw [Set.indicator_of_notMem this, Set.indicator_of_notMem hg]
  rw [e, GlobalTheory.T.lintegral_uniformizerTorus_translate_unipotentQuotient E n μ ϖ hϖ l.1 𝓕 h𝓕 F hF hFinv]
  congr 1
  rw [lintegral_indicator hC, Measure.restrict_restrict hC, Set.inter_comm]

theorem cell_integral [MeasurableSpace (GA E n)] [BorelSpace (GA E n)] (μ : Measure (GA E n)) [μ.IsHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 E))) (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ)
    (hϖ : ∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) (𝓕 : Set (GA E n)) (h𝓕 : IsFundamentalDomain (NE E n) 𝓕 μ)
    (B : GA E n → ℂ) (hB : Measurable B) (hBi : Integrable B (μ.restrict 𝓕))
    (hinv : ∀ u ∈ NA E n, ∀ g, B (u * g) = B g) :
    (∀ l : abelian₂ E n S, Integrable (fun g => B (tl n ϖ l.1 * g)) (μ.restrict (𝓕 ∩ C0 E n S))) ∧
      HasSum (fun l : abelian₂ E n S => (dinv n l.1 : ℂ) * ∫ g in 𝓕 ∩ C0 E n S, B (tl n ϖ l.1 * g) ∂μ)
        (∫ g in 𝓕, B g ∂μ) := by
  have hpos : ∀ l : abelian₂ E n S, 0 < dinv n l.1 := fun l =>
    Finset.prod_pos fun v _ => zpow_pos (by exact_mod_cast (GlobalTheory.LFun.qV_ne_zero v).bot_lt) _
  exact GlobalTheory.T.hasSum_unfolding_of_complex_invariant_integrable μ 𝓕 (𝓕 ∩ C0 E n S) (fun l : abelian₂ E n S => dinv n l.1) hpos (fun l g => tl n ϖ l.1 * g)
    (fun l => measurable_const_mul _) ((fun u : GA E n => fun g => u * g) '' (NA E n : Set (GA E n)))
    (fun f hf hfi => cell_lintegral μ S ϖ hϖ 𝓕 h𝓕 f hf fun u hu g => hfi _ ⟨u, hu, rfl⟩ g)
    B hB hBi (by rintro _ ⟨u, hu, rfl⟩ x; exact hinv u hu x)

end GlobalTheory.CellDec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientMapUniqueBijectiveComplexExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientMapUniqueBijectiveComplexExtension
noncomputable section

namespace GlobalTheory.CoefExtC

section General

open Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.AdTh.CoefExt

variable {K : Type} [Field K] {σ : K →+* ℂ} {I : Type} [Fintype I] {n : ℕ} {lam : I → DomWeight n}
  {W : Type} [AddCommGroup W] [Module ℂ W]

theorem exists_ext (c' : VV K lam →ₛₗ[σ] W) (hs : Submodule.span ℂ (Set.range c') = ⊤)
    (hli : LinearIndependent ℂ fun j => c' (bVV K lam j)) :
    ∃ c : VV ℂ lam →ₗ[ℂ] W, (∀ v, c (up σ lam v) = c' v) ∧ Function.Bijective c ∧
      ∀ d : VV ℂ lam →ₗ[ℂ] W, (∀ v, d (up σ lam v) = c' v) → d = c := by
  classical
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range fun j => up σ lam (bVV K lam j)) := by
    intro v _
    obtain ⟨a, rfl⟩ := exists_coord σ lam v
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hcard : Fintype.card (VVIdx lam) = Module.finrank ℂ (VV ℂ lam) := (Module.finrank_eq_card_basis (bVV ℂ lam)).symm
  let b : Module.Basis (VVIdx lam) ℂ (VV ℂ lam) := basisOfTopLeSpanOfCardEqFinrank _ hsp hcard
  have hb : ∀ j, b j = up σ lam (bVV K lam j) := fun j => congrFun (coe_basisOfTopLeSpanOfCardEqFinrank _ hsp hcard) j
  have hsw : ⊤ ≤ Submodule.span ℂ (Set.range fun j => c' (bVV K lam j)) := by
    rw [← hs, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← (bVV K lam).sum_repr v, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  let w : Module.Basis (VVIdx lam) ℂ W := Module.Basis.mk hli hsw
  have hc : ∀ j, (b.equiv w (Equiv.refl _)) (up σ lam (bVV K lam j)) = c' (bVV K lam j) := by
    intro j
    rw [← hb, Module.Basis.equiv_apply]
    exact Module.Basis.mk_apply hli hsw j
  refine ⟨(b.equiv w (Equiv.refl _)).toLinearMap, fun v => ?_, (b.equiv w (Equiv.refl _)).bijective, fun d hd => ?_⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [← (bVV K lam).sum_repr v, up_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, map_smulₛₗ, LinearEquiv.coe_coe, hc]
  · refine b.ext fun j => ?_
    rw [hb, hd, LinearEquiv.coe_coe, hc]

theorem li_basis (c' : VV K lam →ₛₗ[σ] W)
    (h : ∀ (m : ℕ) (b : Fin m → VV K lam), LinearIndependent K b → LinearIndependent ℂ fun j => c' (b j)) :
    LinearIndependent ℂ fun j => c' (bVV K lam j) := by
  let e := Fintype.equivFin (VVIdx lam)
  have h1 := h _ (bVV K lam ∘ e.symm) ((bVV K lam).linearIndependent.comp _ e.symm.injective)
  have h2 := h1.comp e e.injective
  simpa [Function.comp_def] using h2

end General

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical


set_option maxHeartbeats 800000 in
theorem exists_extC_bijective_unique : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∃ c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W, ExtC R i (inC M.c') M.c0' c ∧ Function.Bijective c ∧ ∀ c', ExtC R i (inC M.c') M.c0' c' → c' = c := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ _ _ i Tp tup O hP
  obtain ⟨gramR, c0R, c0L, hT, hc⟩ := hP.lift.c0
  have hE : ∀ v, O.c0' (GlobalTheory.AdTh.CoefExt.up O.jL (lamV D i) v) = c0L i v := by
    intro v
    obtain ⟨w, hw, h⟩ := hc v
    rw [show GlobalTheory.AdTh.CoefExt.up O.jL (lamV D i) v = w from Subtype.ext hw.symm]
    exact h
  obtain ⟨-, h2, h3⟩ := hT.mapL i
  obtain ⟨c, h4, h5, h6⟩ := exists_ext (W := (R.cV i).W) O.c0' (GlobalTheory.AdTh.CoefExt.span_top (W := (R.cV i).W) hE h3)
    (li_basis (W := (R.cV i).W) O.c0' fun m b hb => GlobalTheory.AdTh.CoefExt.linearIndependent (W := (R.cV i).W) hE h2 b hb)
  refine ⟨c, fun v v' hv => ?_, h5, fun d hd => h6 d fun v => hd v _ rfl⟩
  rw [show v' = GlobalTheory.AdTh.CoefExt.up (inC O.c') (lamV D i) v from Subtype.ext hv]
  exact h4 v

end GlobalTheory.CoefExtC

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientMapUniqueBijectiveComplexExtensionStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficientMap_unique_bijective_complex_extension : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∃ c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W, ExtC R i (inC M.c') M.c0' c ∧ Function.Bijective c ∧ ∀ c', ExtC R i (inC M.c') M.c0' c' → c' = c := by
  first | exact @GlobalTheory.CoefExtC.exists_extC_bijective_unique | exact GlobalTheory.CoefExtC.exists_extC_bijective_unique | (intros; apply GlobalTheory.CoefExtC.exists_extC_bijective_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCartanInvOneOfOnb
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.RawLift.VecNonzero

theorem thetaInner_self_ne_zero {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (hψ : IsStdChar D ψ (-1))
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (h0 : f ≠ 0) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hμ : IsCovolOne (ratL T S) μ 𝓕) : thetaIP μ 𝓕 f f ≠ 0 := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨-, c, hc⟩ := GlobalTheory.exists_normalise_meanSquare_of_cocompact (WO S T) (ratL T S) K hK hKc f hf.cont h0
    (by
      rintro _ ⟨γ, rfl⟩ w
      exact (congrArg norm (hf.quasi γ w)).trans (by rw [norm_mul, hψ.1.2.1, one_mul]))
  have h1 := hc μ 𝓕 hμ.1 hμ.2.1 hμ.2.2
  have e1 : thetaIP μ 𝓕 f f = ((∫ w in 𝓕, ‖f w‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    unfold thetaIP
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [Complex.star_def, Complex.conj_mul']
    push_cast
    rfl
  intro h
  rw [e1, Complex.ofReal_eq_zero] at h
  simp only [norm_mul, mul_pow] at h1
  rw [integral_const_mul, h, mul_zero] at h1
  exact zero_ne_one h1

end GlobalTheory.RawLift.VecNonzero

namespace GlobalTheory.RawLift

open GlobalTheory.RawLift.VecNonzero


open scoped ComplexOrder in
theorem isCartanInv_one_of_onb {k : ℕ} {Gm B : Matrix (Fin k) (Fin k) ℂ} (h : IsONBasis Gm 1 B k) : IsCartanInv Gm 1 := by
  obtain ⟨ε, hε, hG, -⟩ := h
  have e1 : ∀ a, (ε a : ℂ) = 1 := fun a => by
    rcases hε a with h | h
    · simp [h.1]
    · exact absurd a.2 (not_lt.2 h.2)
  have hB : Bᴴ * Gm * B = 1 := by
    rw [hG]
    simp only [e1, Matrix.diagonal_one]
  have hu : IsUnit B.det := Matrix.isUnit_det_of_left_inverse hB
  have h1 := Matrix.mul_nonsing_inv B hu
  have h2 : Gm = (B⁻¹)ᴴ * B⁻¹ := by
    have h3 : (B⁻¹)ᴴ * (Bᴴ * Gm * B) * B⁻¹ = (B⁻¹)ᴴ * B⁻¹ := by rw [hB, Matrix.mul_one]
    have h4 : (B⁻¹)ᴴ * Bᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
    rw [← h3]
    simp only [Matrix.mul_assoc, h1, Matrix.mul_one]
    rw [← Matrix.mul_assoc, h4, Matrix.one_mul]
  refine ⟨Matrix.mul_one _, by simp, ?_⟩
  rw [Matrix.mul_one, h2]
  exact Matrix.PosDef.conjTranspose_mul_self _
    (Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (by
      rw [Matrix.det_nonsing_inv]; exact hu.ringInverse)))

theorem vecNe : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i t, VecNe R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hF i t μ 𝓕 hμ
  have hW := hL.thP.ωP i t
  have hth : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have := hL.thP.pt_theta i t 1
    unfold RealDat.ptP pureTensorO at this
    rwa [GlobalTheory.AdTh.VecFock.pureTensorL_one] at this
  have hv0 : R.vP i t ≠ 0 := GlobalTheory.AdTh.VecNe.thPVec_ne_zero
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.lev.βV i))
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.lev.βW i))
    ((D.sp.W_rank _ (Nat.le_add_left _ _) i.2).trans_le (r_le_V i)) (hL.thP.vP i t)
  refine ⟨thetaInner_self_ne_zero hW.std hth hv0 hμ, ?_⟩
  obtain ⟨-, -, v, w, hv1, -, hio⟩ := hL.thP.ioP i t
  have hvac := GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ (fun _ => 1) _ _ _ _ _ _ _ _ _ _ (hL.thP.vP i t) hth
  have hinj := GlobalTheory.FockVecInj.pureTensorO_injective D R.ψ R.θ (Vc D i) (Wc D i) hW.std hL.models.inf (fun _ => 1) (R.BV i)
    (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) (fun _ => (Vc D i).rank) (fun τ => ((Wc D i).sig (tauE D τ)).1)
    (fun τ => isCartanInv_one_of_onb (hL.models.BV i τ)) (GlobalTheory.AdTh.VecFock.isCartanInv_cart _) (hL.models.BV i)
    (fun τ => GlobalTheory.AdTh.VecFock.isONBasis_onb _ τ _ (hL.models.order i τ)) (D.sp.V_sig _) (D.sp.W_sig _) _ hth hvac hv0
  refine ⟨fun ρ => v ρ, w, hv1, ?_⟩
  have hj : jointVec R i t (fun ρ => v ρ) w = R.ptP i t (RealDat.Delta i) := by
    unfold jointVec
    rw [hio]
  rw [hj]
  refine thetaInner_self_ne_zero hW.std (hL.thP.pt_theta i t _) (fun h => ?_) hμ
  refine GlobalTheory.AdTh.IoExtPf.Delta_ne i (hinj ?_)
  exact h.trans (map_zero (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i)
    (onb (R.MW i (sg0 D A))) (R.vP i t))).symm

end GlobalTheory.RawLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateTuplesConjugateResidueLevels
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateTuplesConjugateResidueLevels
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.ConjRes

section General

variable {D : D7}

theorem locK_conj {c c' : (AE D)ˣ →* Circle} {χ χ' : Formalism.L2.Host.HChar D.host.E} (h : ChrEq c χ) (h' : ChrEq c' χ')
    (τ : ℂ ≃+* ℂ) (hc : ∀ x, ((c' x : Circle) : ℂ) = τ ((c x : Circle) : ℂ)) (P : Pl D.host.E) (k : D.host.Eˣ) :
    ((χ'.locK P k : ℂˣ) : ℂ) = τ ((χ.locK P k : ℂˣ) : ℂ) := by
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  rw [← h.2 P e he k _ (Formalism.L2.JoinChr.locU_val he.1 k), ← h'.2 P e he k _ (Formalism.L2.JoinChr.locU_val he.1 k), hc]

theorem exists_lift (P : Pl D.host.E) (u : (kP P)ˣ) :
    ∃ (a : 𝓞 D.host.E) (k : D.host.Eˣ), (k : D.host.E) = a ∧ (u : kP P) = Ideal.Quotient.mk _ a := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := P.asIdeal) (u : kP P)
  have : Nontrivial (kP P) := Ideal.Quotient.nontrivial_iff.2 P.isPrime.ne_top
  have h0 : (a : D.host.E) ≠ 0 := by
    intro h
    have : a = 0 := by exact_mod_cast h
    rw [this, map_zero] at ha
    exact u.ne_zero ha.symm
  exact ⟨a, Units.mk0 _ h0, rfl, ha.symm⟩

theorem unrAt_of_isRes_one {χ : Formalism.L2.Host.HChar D.host.E} {P : Pl D.host.E} (h : IsRes χ P 1) : χ.UnrAt P := by
  have key : ∀ (a : 𝓞 D.host.E) (k : D.host.Eˣ), (k : D.host.E) = a → a ∉ P.asIdeal → χ.locK P k = 1 := by
    intro a k hk ha
    have := P.isMaximal
    have hu : IsUnit (Ideal.Quotient.mk P.asIdeal a) := by
      let _ := Ideal.Quotient.field P.asIdeal
      exact (Ne.isUnit (fun h0 => ha (Ideal.Quotient.eq_zero_iff_mem.1 h0)))
    exact (h a k hu.unit hk rfl).symm
  refine GlobalTheory.EtaConjType.unrAt_of_locK χ P fun u hu => ?_
  obtain ⟨n, ⟨d, hd⟩, hnd⟩ := P.exists_primeCompl_mul_eq_of_integer (u : D.host.E) hu.le
  have hd' : d ∉ P.asIdeal := hd
  have hd0 : (d : D.host.E) ≠ 0 := by
    intro h0
    have : d = 0 := by exact_mod_cast h0
    exact hd' (this ▸ P.asIdeal.zero_mem)
  have hn : n ∉ P.asIdeal := by
    rw [← P.valuation_eq_one_iff_notMem (K := D.host.E), ← hnd, map_mul, hu, one_mul]
    exact (P.valuation_eq_one_iff_notMem (K := D.host.E)).2 hd'
  have e1 := key d (Units.mk0 _ hd0) rfl hd'
  have e2 := key n (u * Units.mk0 _ hd0) hnd hn
  rwa [map_mul, e1, mul_one] at e2

theorem levFn_conj {n : ℕ} (β : GL (Fin n) (Lev.EAf D)) {r : ℕ} (hr : r ≤ n) (t : ℕ) (Pg : Finset (Pl D.host.E))
    {Q Q' : Finset (Pl D.host.E)} (hQ : Q' = Q) (τ : ℂ ≃+* ℂ) (χ ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (hχ : ∀ PP ∈ Pg, ∀ x, τ ((χ PP x : ℂˣ) : ℂ) = ((χ PP x : ℂˣ) : ℂ))
    (hξ : ∀ PP ∈ Q, ∀ x, ((ξ' PP x : ℂˣ) : ℂ) = τ ((ξ PP x : ℂˣ) : ℂ)) (x) :
    ((levFn β ⟨r, hr, t, 1, Pg, Q', LevelP.triv Pg r ℂ, fun _ PP => (χ PP)⁻¹, ξ'⟩ x : ℂˣ) : ℂ) =
      τ ((levFn β ⟨r, hr, t, 1, Pg, Q, LevelP.triv Pg r ℂ, fun _ PP => (χ PP)⁻¹, ξ⟩ x : ℂˣ) : ℂ) := by
  subst hQ
  have h1 : ∀ y, ext1 (LevelP.triv Pg r ℂ).H (LevelP.triv Pg r ℂ).chi y = 1 := fun y => Lev.subgroupCharExtension_one_apply _ _
  unfold levFn
  simp only [h1, one_mul, Units.val_mul, Units.coe_prod, map_mul, map_prod]
  congr 1
  · refine Finset.prod_congr rfl fun PP hP => Finset.prod_congr rfl fun c _ => ?_
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, hχ PP hP]
  · exact Finset.prod_congr rfl fun PP hP => hξ PP hP _

theorem lev_congr (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) {r : ℕ} (hr : r ≤ V.rank) (t : ℕ) (Pg : Finset (Pl D.host.E))
    {Q Q' : Finset (Pl D.host.E)} (hQ : Q' = Q) (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) :
    (levEnv V β ⟨r, hr, t, 1, Pg, Q', P, χ, ξ'⟩).J = (levEnv V β ⟨r, hr, t, 1, Pg, Q, P, χ, ξ⟩).J := by
  subst hQ
  rfl

theorem levEnv_chi (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (k : Bridge.Gf V)
    (hk : k ∈ (levEnv V β L).J) :
    (levEnv V β L).χ ⟨k, hk⟩ = levFn β (Lev.flag1L L) (Formalism.UG.bc (Lev.swapAE D) k.1) := rfl

theorem principalLevel_definite_datum_flag_eq {T0 : Type} (L : LevCh D T0) (i : Fin D.R.m) (t : T0) :
    Lev.flag1L (L.datVt i t) = ⟨D.R.r, r_le_V i, D.R.t, 1, L.Pg, L.Q t, LevelP.triv L.Pg D.R.r ℂ,
      fun _ PP => (L.chi ((i : ℕ) + 1) PP)⁻¹, L.xiR t⟩ := rfl

theorem datVt_eq {T0 : Type} (L : LevCh D T0) (i : Fin D.R.m) (t : T0) :
    L.datVt i t = ⟨D.R.r, r_le_V i, D.R.t, 1, L.Pg, L.Q t, (LevelP.triv L.Pg D.R.r ℂ).conj,
      fun _ PP => (L.chi ((i : ℕ) + 1) PP)⁻¹, L.xiR t⟩ := rfl

theorem lev_datVt {T0 : Type} (L : LevCh D T0) (i : Fin D.R.m) {t t' : T0} (h : L.Q t' = L.Q t) :
    (levEnv (Vc D i) (L.βV i) (L.datVt i t')).J = (levEnv (Vc D i) (L.βV i) (L.datVt i t)).J := by
  rw [datVt_eq, datVt_eq]
  exact lev_congr (Vc D i) (L.βV i) (r_le_V i) D.R.t L.Pg h _ _ (L.xiR t) (L.xiR t')

end General


set_option maxHeartbeats 1000000 in
theorem conj_res : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → ∀ (τ : ℂ ≃+* ℂ) (t t' : T0), ConjTup R τ t t' → (∀ PP ∈ R.Q t, ∀ x, ((R.xiR t' PP x : ℂˣ) : ℂ) = τ ((R.xiR t PP x : ℂˣ) : ℂ)) ∧ (∀ PP ∈ R.Q t, R.xiR t PP ≠ 1) ∧ (∀ P, (((R.xiH t').val P : ℂˣ) : ℂ) = τ (((R.xiH t).val P : ℂˣ) : ℂ)) ∧ ∀ i : Fin D.R.m, FixBase T R i τ → levJ R i t' = levJ R i t ∧ ∀ k (hk : k ∈ levJ R i t) (hk' : k ∈ levJ R i t'), (((levEnv (Vc D i) (R.βV i) (R.datVt i t')).χ ⟨k, hk'⟩ : ℂˣ) : ℂ) = τ (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ ⟨k, hk⟩ : ℂˣ) : ℂ) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC τ t t' hct
  have hL := hC.lev
  have hloc := locK_conj (hL.xi t) (hL.xi t') τ hct.2
  have h1 : ∀ PP ∈ R.Q t, ∀ x, ((R.xiR t' PP x : ℂˣ) : ℂ) = τ ((R.xiR t PP x : ℂˣ) : ℂ) := by
    intro PP hP x
    obtain ⟨a, k, hk, hx⟩ := exists_lift PP x
    rw [hL.xiR t PP hP a k x hk hx, hL.xiR t' PP (hct.1 ▸ hP) a k x hk hx]
    exact hloc PP k
  refine ⟨h1, fun PP hP h => ?_, fun P => hloc P _, fun i hτ => ⟨?_, fun k hk hk' => ?_⟩⟩
  · exact (hL.Q_ram t PP).2 (Or.inl hP) (unrAt_of_isRes_one (h ▸ hL.xiR t PP hP))
  · exact lev_datVt R.toLevCh i hct.1
  · rw [levEnv_chi, levEnv_chi, principalLevel_definite_datum_flag_eq, principalLevel_definite_datum_flag_eq]
    exact levFn_conj (R.βV i) (r_le_V i) D.R.t R.Pg hct.1 τ (R.chi ((i : ℕ) + 1)) (R.xiR t) (R.xiR t') hτ.chi h1 _

end GlobalTheory.ConjRes
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateTuplesConjugateResidueLevelsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_tuples_conjugate_residue_levels : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → ∀ (τ : ℂ ≃+* ℂ) (t t' : T0), ConjTup R τ t t' → (∀ PP ∈ R.Q t, ∀ x, ((R.xiR t' PP x : ℂˣ) : ℂ) = τ ((R.xiR t PP x : ℂˣ) : ℂ)) ∧ (∀ PP ∈ R.Q t, R.xiR t PP ≠ 1) ∧ (∀ P, (((R.xiH t').val P : ℂˣ) : ℂ) = τ (((R.xiH t).val P : ℂˣ) : ℂ)) ∧ ∀ i : Fin D.R.m, FixBase T R i τ → levJ R i t' = levJ R i t ∧ ∀ k (hk : k ∈ levJ R i t) (hk' : k ∈ levJ R i t'), (((levEnv (Vc D i) (R.βV i) (R.datVt i t')).χ ⟨k, hk'⟩ : ℂˣ) : ℂ) = τ (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ ⟨k, hk⟩ : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.ConjRes.conj_res | exact GlobalTheory.ConjRes.conj_res | (intros; apply GlobalTheory.ConjRes.conj_res <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenWeight
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.PtExt


set_option maxHeartbeats 1000000 in
theorem main : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big₀ big₁ : D.what₂.places.Pl → Finset ℂ) (L₀ L₁ : LocAll (lay0 D)), Built A M C tp.tup big₀ L₀ → Built A M C tp.tup big₁ L₁ → ∀ i₁ : L₁.lay.fixZ.nd.Loc, ∃ i₀ : L₀.lay.fixZ.nd.Loc, L₀.lay.fixZ.nd.w i₀ = L₁.lay.fixZ.nd.w i₁ ∧ L₀.lay.fixZ.nd.j i₀ = L₁.lay.fixZ.nd.j i₁ ∧ ∃ e : L₁.lay.fixZ.nd.X i₁ ≃ L₀.lay.fixZ.nd.X i₀, ∀ (v : PlE D.host) (k : ℕ) (x : L₁.lay.fixZ.nd.X i₁), SplitOut L₁.lay.fixZ.nd i₁ v → 1 ≤ k → k ≤ D.R.nV → iotaO L₁.lay.fixZ.nd L₁.lay.fixZ.naut i₁ ((L₁.lay.fixZ.nd.hT i₁ v k : L₁.lay.fixZ.nd.X i₁ → L₁.lay.fixZ.nd.O i₁) x) = iotaO L₀.lay.fixZ.nd L₀.lay.fixZ.naut i₀ ((L₀.lay.fixZ.nd.hT i₀ v k : L₀.lay.fixZ.nd.X i₀ → L₀.lay.fixZ.nd.O i₀) (e x)) := by
  intro hstd D cf jE A low Pq S hL eig θ Bs M C tp hch hmt hstar hexp hspl hcheb big₀ big₁ L₀ L₁ hB₀ hB₁ i₁
  have onto : ∀ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), Built A M C tp.tup big L →
      ∀ (j : ℕ) (w : D.what₂.places.Pl) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), D.what₂.muAt w ≠ D.what₂.mu0 →
      ∀ c ∈ EigSet (M (D.what₂.muTw w) j h1 h2) (D.what₂.places.resChar w) (C.Q w),
        ∃ i ∈ L.X.nd.locs j w, ∃ x : L.X.nd.X i, sys L i x = c := by
    intro big L hB j w h1 h2 htw c hc
    obtain ⟨i, hi, x, hx⟩ := GlobalTheory.T.side_eigen_frobenius hstd D cf jE A low Pq S hL eig θ Bs M C tp hch hmt hstar hexp hspl hcheb big L hB j w h1 h2 htw c hc
    refine ⟨i, hi, x, funext fun v => funext fun k => ?_⟩
    by_cases hg : GenAt D (D.what₂.places.resChar w) (C.Q w) v k
    · rw [sys_of_genAt hB hi x hg, hx v k hg]
    · rw [sys_of_not_genAt hB hi x hg, hc.1 v k hg]
  have cong : ∀ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), Built A M C tp.tup big L →
      ∀ (j : ℕ) (w : D.what₂.places.Pl) (i i' : L.X.nd.Loc), i ∈ L.X.nd.locs j w → i' ∈ L.X.nd.locs j w →
      ∀ (x : L.X.nd.X i) (x' : L.X.nd.X i'),
        (i = i' ↔ ∀ v k, sys L i x v k - sys L i' x' v k ∈ (A.pl.plB w).nonunits) := by
    intro big L hB j w i i' hi hi' x x'
    rw [GlobalTheory.T.locations_distinguished_by_generics D cf jE A M C tp.tup big L hB j w i i' hi hi' x x']
    constructor
    · intro h v k
      by_cases hg : GenAt D (D.what₂.places.resChar w) (C.Q w) v k
      · rw [sys_of_genAt hB hi x hg, sys_of_genAt hB hi' x' hg]; exact h v k hg
      · rw [sys_of_not_genAt hB hi x hg, sys_of_not_genAt hB hi' x' hg, sub_zero]; exact zero_mem _
    · intro h v k hg
      rw [← sys_of_genAt hB hi x hg, ← sys_of_genAt hB hi' x' hg]; exact h v k
  have h1 := (L₁.X.nd.j_range i₁).1
  have h2 := (L₁.X.nd.j_range i₁).2
  have hi₁ : i₁ ∈ L₁.X.nd.locs (L₁.X.nd.j i₁) (L₁.X.nd.w i₁) := (L₁.X.nd.locs_mem _ _ i₁).2 ⟨rfl, rfl⟩
  have htw : D.what₂.muAt (L₁.X.nd.w i₁) ≠ D.what₂.mu0 := L₁.X.nd.w_tw i₁
  obtain ⟨x₁⟩ := L₁.X.nd.neX i₁
  obtain ⟨i₀, hi₀, y₀, hy₀⟩ := onto big₀ L₀ hB₀ _ _ h1 h2 htw _ (sys_mem hB₁ h1 h2 hi₁ x₁)
  have fwd : ∀ x : L₁.X.nd.X i₁, ∃ y : L₀.X.nd.X i₀, sys L₀ i₀ y = sys L₁ i₁ x := by
    intro x
    obtain ⟨i', hi', y', hy'⟩ := onto big₀ L₀ hB₀ _ _ h1 h2 htw _ (sys_mem hB₁ h1 h2 hi₁ x)
    have hc : i' = i₀ := by
      rw [cong big₀ L₀ hB₀ _ _ i' i₀ hi' hi₀ y' y₀, hy', hy₀]
      exact (cong big₁ L₁ hB₁ _ _ i₁ i₁ hi₁ hi₁ x x₁).1 rfl
    subst hc
    exact ⟨y', hy'⟩
  choose f hf using fwd
  have finj : Function.Injective f := fun x x' h => sys_inj L₁ i₁ (by rw [← hf x, ← hf x', h])
  have fsurj : Function.Surjective f := by
    intro y
    obtain ⟨i', hi', x', hx'⟩ := onto big₁ L₁ hB₁ _ _ h1 h2 htw _ (sys_mem hB₀ h1 h2 hi₀ y)
    have hc : i' = i₁ := by
      rw [cong big₁ L₁ hB₁ _ _ i' i₁ hi' hi₁ x' x₁, hx', ← hy₀]
      exact (cong big₀ L₀ hB₀ _ _ i₀ i₀ hi₀ hi₀ y y₀).1 rfl
    subst hc
    exact ⟨x', sys_inj L₀ i₀ (by rw [hf x', hx'])⟩
  have hw₀ : L₀.X.nd.w i₀ = L₁.X.nd.w i₁ := ((L₀.X.nd.locs_mem _ _ i₀).1 hi₀).2
  have hj₀ : L₀.X.nd.j i₀ = L₁.X.nd.j i₁ := ((L₀.X.nd.locs_mem _ _ i₀).1 hi₀).1
  refine ⟨i₀, hw₀, hj₀, Equiv.ofBijective f ⟨finj, fsurj⟩, fun v k x hv k1 k2 => ?_⟩
  have hg := (splitOut_iff_genAt hB₁ hi₁ v k).1 ⟨hv, k1, k2⟩
  have e := congrFun (congrFun (hf x) v) k
  rw [sys_of_genAt hB₀ hi₀ _ hg] at e
  exact (sys_of_genAt hB₁ hi₁ x hg).symm.trans e.symm

end GlobalTheory.PtExt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffSpaceLevelFixesFockVectors
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffSpaceLevelFixesFockVectors
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift.LevelFix

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem isLiftFiniteGroup_one_of_mem_coeffSpaceLevel (R : RealDat D A Ks) (i : Fin D.R.m) (k : GA D (Wc D i)) (hk : k ∈ levW R i) :
    IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) 1 k := by
  refine ⟨hk.1, hk.2.1, ?_⟩
  have h2 := hk.2.2
  have e : (R.datWp i R.triv).P.H = ⊥ := rfl
  rw [e] at h2
  exact Subgroup.mem_bot.1 h2

theorem realDatum_identity_lifts_identity (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) :
    IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) 1 1 :=
  ⟨Subgroup.one_mem _, by rw [map_one]; exact Subgroup.one_mem _, by rw [map_one]; exact rTup_one⟩

theorem levChi_flag_one (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) :
    levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) 1 = 1 := by
  have := (levChar D.sp.cm (Vc D i).gram (R.βV i) (flagL (R.datVt i t))).map_one
  unfold levChi
  rw [map_one]
  exact congrArg Units.val this

theorem levW_fix_vP (R : RealDat D A Ks) (F : Face D A) (h : Laws R F) (i : Fin D.R.m) (t : T)
    (k : GA D (Wc D i)) (hk : k ∈ levW R i) : R.ωP i t (1, k) (R.vP i t) = R.vP i t := by
  have e := GlobalTheory.T.weilAction_liftPair_stepVector_invLevelChar R h.lev h.models.inf h.thP.ωP h.thP.vP i t 1 1 k (realDatum_identity_lifts_identity R i t)
    (isLiftFiniteGroup_one_of_mem_coeffSpaceLevel R i k hk)
  rw [e, levChi_flag_one R i t, inv_one, one_smul]

theorem levFix : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    Laws R F → R.FullP → ∀ i t, LevFix R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F h _ i t k hk P
  have hv : R.ωP i t (1, k) (R.vP i t) = (1 : ℂ) • R.vP i t := by
    rw [one_smul]; exact levW_fix_vP R F h i t k hk
  have := GlobalTheory.FiniteFock.om_pureTensorO_of_finite R.ψ R.θ (Vc D i) (Wc D i) _ _ (R.ωP i t) h.models.inf
    (h.thP.ωP i t) _ _ _ _ _ (h.thP.pt_theta i t) 1 (Subgroup.one_mem _) k hk.1 1 hv P
  exact this.trans (one_smul ℂ _)

end GlobalTheory.RawLift.LevelFix

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffSpaceLevelFixesFockVectorsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeffSpaceLevel_fixes_fockVectors : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i t, LevFix R i t := by
  first | exact @GlobalTheory.RawLift.LevelFix.levFix | exact GlobalTheory.RawLift.LevelFix.levFix | (intros; apply GlobalTheory.RawLift.LevelFix.levFix <;> assumption)
end
end
