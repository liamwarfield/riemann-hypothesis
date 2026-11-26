module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsScaleOfChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KeepSideBMtVPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardThetaLiftPreservesGood
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypePlacesIsSplitNonconjugateOfAdmissible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesFourth
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverFramedPointOverMovedBaseFrame
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormGenEqOneOfFrOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionPullbackExistsUnique
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIneOfUnit
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SignAtBasePlaceEqEmbedding
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftVanishesSingleCoefficientOfKernelKills

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapVVSymmMapVV
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ExportSeries GlobalTheory.ConjTwist

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoefLatConj

open MvPolynomial GlobalTheory.SeriesTie.Scale

variable {D : D7} {n : ℕ}

def polLat {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ)
    (lam : D.what₂.Tau → DomWeight n) (M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Submodule O (VV ℂ lam) :=
  Submodule.span O {y | ∃ F ∈ nabAtr emb lam M, y = GlobalTheory.CoefModel.mapVV σ lam F}

theorem coefLatFn_eq {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K))
    (O : Subring ℂ) (lam : D.what₂.Tau → DomWeight n) (M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) :
    coefLatFn σ emb O lam M = (polLat σ emb O lam M).map ((coefLin lam).restrictScalars O) := by
  unfold coefLatFn polLat
  rw [Submodule.map_span]
  congr 1
  ext φ
  constructor
  · rintro ⟨F, hF, rfl⟩
    exact ⟨_, ⟨F, hF, rfl⟩, coefFn_map σ lam _⟩
  · rintro ⟨_, ⟨F, hF, rfl⟩, rfl⟩
    exact ⟨F, hF, coefFn_map σ lam _⟩

theorem polLat_conj {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ} {emb : D.what₂.Tau → (D.host.E →+* K)}
    {O O' : Subring ℂ} {lam : D.what₂.Tau → DomWeight n} {M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (τ : ℂ ≃+* ℂ)
    (hτ : ∀ a : K, τ (σ a) = σ a) (hO : ∀ a ∈ O, τ a ∈ O') {y : VV ℂ lam} (hy : y ∈ polLat σ emb O lam M) :
    GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) lam y ∈ polLat σ emb O' lam M := by
  induction hy using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨F, hF, rfl⟩ := h
    refine Submodule.subset_span ⟨F, hF, Subtype.ext ?_⟩
    change MvPolynomial.map (τ : ℂ →+* ℂ) (MvPolynomial.map σ F.1) = MvPolynomial.map σ F.1
    rw [MvPolynomial.map_map, show (τ : ℂ →+* ℂ).comp σ = σ from RingHom.ext hτ]
  | zero => rw [map_zero]; exact zero_mem _
  | add _ _ _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
  | smul a y _ h1 =>
    have e : GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) lam (a • y) = (⟨τ a, hO a a.2⟩ : O') • GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) lam y := by
      rw [Subring.smul_def, Subring.smul_def, map_smulₛₗ]
      rfl
    rw [e]
    exact Submodule.smul_mem _ _ h1

theorem mapVV_symm_mapVV (lam : D.what₂.Tau → DomWeight n) (τ : ℂ ≃+* ℂ) (y : VV ℂ lam) :
    GlobalTheory.CoefModel.mapVV (τ.symm : ℂ →+* ℂ) lam (GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) lam y) = y := by
  refine Subtype.ext ?_
  change MvPolynomial.map (τ.symm : ℂ →+* ℂ) (MvPolynomial.map (τ : ℂ →+* ℂ) y.1) = y.1
  rw [MvPolynomial.map_map]
  have : (τ.symm : ℂ →+* ℂ).comp (τ : ℂ →+* ℂ) = RingHom.id ℂ := RingHom.ext fun a => τ.symm_apply_apply a
  rw [this, MvPolynomial.map_id]

section Base

variable {i : Fin D.R.m} {B : Base (Vc D i) (Wc D i)}

theorem pq_le (hB : B.Good) (τ : D.what₂.Tau) : B.w.p τ + B.w.q τ ≤ (Wc D i).rank := by
  obtain ⟨e, -⟩ := hB.sigOK (tauE D τ)
  rw [← hB.sig τ] at e
  have := Fintype.card_congr e
  simp only [Fintype.card_fin, Fintype.card_sum] at this
  omega

variable (Φ : VsV D i ℂ →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) {κ : ℂ}

theorem mem_coefLat_iff (hlam : B.w.lam = lamV D i) (hval : ∀ x, Φ x ∈ B.valSpace)
    (hκ : ∀ x : VsV D i ℂ, harmFn (Wc D i).rank B.w B.F.BS (Φ x) =
      κ • coefFn (RingHom.id ℂ) (lamV D i) (x : Pol ℂ D.what₂.Tau (Vc D i).rank))
    {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ)
    (h : Bridge.Gf (Vc D i)) (x : VsV D i ℂ) :
    Φ x ∈ B.coefLat σ emb O h ↔ κ • x ∈ polLat σ emb O (lamV D i) (B.latAt h) := by
  show Φ x ∈ harmLat σ emb O _ B.w B.F.BS (B.latAt h) ↔ _
  rw [mem_harmLat, hlam, coefLatFn_eq, Submodule.mem_map]
  constructor
  · rintro ⟨-, y, hy, he⟩
    have e : coefLin (lamV D i) y = coefLin (lamV D i) (κ • x) := by
      rw [map_smul]
      exact he.trans (hκ x)
    exact coefLin_injective _ e ▸ hy
  · intro hx
    refine ⟨hval x, κ • x, hx, ?_⟩
    change coefLin (lamV D i) (κ • x) = _
    rw [map_smul, hκ]
    rfl

theorem existsUnique_eq (hB : B.Good) (hlam : B.w.lam = lamV D i) (hκ0 : κ ≠ 0) (hval : ∀ x, Φ x ∈ B.valSpace)
    (hκ : ∀ x : VsV D i ℂ, harmFn (Wc D i).rank B.w B.F.BS (Φ x) =
      κ • coefFn (RingHom.id ℂ) (lamV D i) (x : Pol ℂ D.what₂.Tau (Vc D i).rank)) :
    ∀ P ∈ B.valSpace, ∃! x : VsV D i ℂ, P = Φ x := by
  intro P hP
  have h1 : harmFn (Wc D i).rank B.w B.F.BS P ∈ (harm (Wc D i).rank B.w B.F.BS).map (harmFn (Wc D i).rank B.w B.F.BS) :=
    Submodule.mem_map_of_mem hP
  rw [GlobalTheory.T.fockHarmonicValueSpace_map_eq_dualWeylModuleFunctions D _ _ B.w B.F.BS hB.wt (pq_le hB), hlam] at h1
  have hs : Submodule.span ℂ {φ | ∃ F : VV ℂ (lamV D i), φ = coefFn (RingHom.id ℂ) (lamV D i) (F : Pol ℂ D.what₂.Tau (Vc D i).rank)}
      ≤ LinearMap.range (coefLin (lamV D i)) :=
    Submodule.span_le.2 (by rintro _ ⟨F, rfl⟩; exact ⟨F, rfl⟩)
  obtain ⟨y, hy⟩ := hs h1
  have hy' : coefLin (lamV D i) y = harmFn (Wc D i).rank B.w B.F.BS P := hy
  have hv : ∀ x, harmFn (Wc D i).rank B.w B.F.BS (Φ x) = κ • coefLin (lamV D i) x := hκ
  refine ⟨κ⁻¹ • y, ?_, fun x hx => ?_⟩
  · have e : harmFn (Wc D i).rank B.w B.F.BS (Φ (κ⁻¹ • y) - P) = 0 := by
      rw [map_sub, hv, map_smul, smul_smul, mul_inv_cancel₀ hκ0, one_smul, hy', sub_self]
    exact (sub_eq_zero.1 (GlobalTheory.T.harmonic_polynomial_eq_zero_of_function D _ _ B.w B.F.BS hB.wt (pq_le hB) _ (sub_mem (hval _) hP) e)).symm
  · refine coefLin_injective (lamV D i) ?_
    have e := hv x
    rw [← hx, ← hy'] at e
    rw [map_smul, e, smul_smul, inv_mul_cancel₀ hκ0, one_smul]

theorem conj_mem_iff (hlam : B.w.lam = lamV D i) (hκ0 : κ ≠ 0) (hval : ∀ x, Φ x ∈ B.valSpace)
    (hκ : ∀ x : VsV D i ℂ, harmFn (Wc D i).rank B.w B.F.BS (Φ x) =
      κ • coefFn (RingHom.id ℂ) (lamV D i) (x : Pol ℂ D.what₂.Tau (Vc D i).rank))
    {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ)
    (τ : ℂ ≃+* ℂ) (hτ : ∀ a : K, τ (σ a) = σ a) (h : Bridge.Gf (Vc D i)) {x x' : VsV D i ℂ} (hx : ConjVec i τ x x') :
    Φ x ∈ B.coefLat σ emb O h ↔ Φ ((τ κ / κ) • x') ∈ B.coefLat σ emb (O.map (τ : ℂ →+* ℂ)) h := by
  rw [mem_coefLat_iff Φ hlam hval hκ, mem_coefLat_iff Φ hlam hval hκ]
  have hx' : x' = GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D i) x := Subtype.ext hx
  have e : κ • ((τ κ / κ) • x') = GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D i) (κ • x) := by
    rw [smul_smul, mul_div_cancel₀ _ hκ0, map_smulₛₗ, hx']
    rfl
  rw [e]
  constructor
  · exact polLat_conj τ hτ fun a ha => Subring.mem_map.2 ⟨a, ha, rfl⟩
  · intro h'
    have hτ' : ∀ a : K, τ.symm (σ a) = σ a := fun a => by rw [τ.symm_apply_eq, hτ]
    have := polLat_conj τ.symm hτ' (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := Subring.mem_map.1 ha
      simpa using hb) h'
    rwa [mapVV_symm_mapVV] at this

theorem coefLat_eq_span (hB : B.Good) (hlam : B.w.lam = lamV D i) (hκ0 : κ ≠ 0) (hval : ∀ x, Φ x ∈ B.valSpace)
    (hκ : ∀ x : VsV D i ℂ, harmFn (Wc D i).rank B.w B.F.BS (Φ x) =
      κ • coefFn (RingHom.id ℂ) (lamV D i) (x : Pol ℂ D.what₂.Tau (Vc D i).rank))
    {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ)
    (h : Bridge.Gf (Vc D i)) :
    B.coefLat σ emb O h = Submodule.span O
      {P | ∃ F ∈ nabAtr emb (lamV D i) (B.latAt h), P = Φ (κ⁻¹ • GlobalTheory.CoefModel.mapVV σ (lamV D i) F)} := by
  let Ψ : VsV D i ℂ →ₗ[O] PolF D (Wc D i).rank (Vc D i).rank := (Φ ∘ₗ (κ⁻¹ • LinearMap.id)).restrictScalars O
  have hΨ : ∀ y, Ψ y = Φ (κ⁻¹ • y) := fun _ => rfl
  have e : B.coefLat σ emb O h = (polLat σ emb O (lamV D i) (B.latAt h)).map Ψ := by
    ext P
    constructor
    · intro hP
      obtain ⟨x, rfl, -⟩ := existsUnique_eq Φ hB hlam hκ0 hval hκ P (Submodule.mem_inf.1 hP).1
      refine ⟨κ • x, (mem_coefLat_iff Φ hlam hval hκ σ emb O h x).1 hP, ?_⟩
      rw [hΨ, smul_smul, inv_mul_cancel₀ hκ0, one_smul]
    · rintro ⟨y, hy, rfl⟩
      rw [hΨ, mem_coefLat_iff Φ hlam hval hκ, smul_smul, mul_inv_cancel₀ hκ0, one_smul]
      exact hy
  rw [e, polLat, Submodule.map_span]
  congr 1
  ext P
  constructor
  · rintro ⟨_, ⟨F, hF, rfl⟩, rfl⟩
    exact ⟨F, hF, rfl⟩
  · rintro ⟨F, hF, rfl⟩
    exact ⟨_, ⟨F, hF, rfl⟩, rfl⟩

end Base

end GlobalTheory.CoefLatConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodFormsSpannedByThetaSeriesOfClassSums
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodFormsSpannedByThetaSeriesOfClassSums
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 10000000

namespace GlobalTheory.BaseClassSum

variable {D : D7} {S T : HSp D}

theorem series_move {B : Base S T} (hB : B.Good) (hS : S.SigOK) {t : Twist D Circle} (ht : t.Good) (hQ : B.admitted t.Q)
    {ω : PairRep S T} (hω : B.IsWeil t.chi ω) {h h' : GA D S} (hh : h ∈ GfC S) (hh' : h' ∈ GfC S) (γ : GQ S) (k : B.levJ t)
    (e : finPt S h = Bridge.ratF S γ * finPt S h' * (k : Bridge.Gf S)) (P : PolF D T.rank S.rank) :
    series B.F ω (B.vecFlat t) h P =
      ((B.levLam t k : ℂˣ) : ℂ)⁻¹ • series B.F ω (B.vecFlat t) h' (B.act ((γ⁻¹ : GQ S) : GA D S) P) := by
  obtain ⟨hsplit, hcomm, htriv, -, -⟩ := GlobalTheory.UnitarySplit.real_finite_split D S
  obtain ⟨x, hx⟩ := (k : Bridge.Gf S).2
  obtain ⟨kk, hkk, -, -, -, hfk⟩ := GlobalTheory.LiftUnfold.exists_fin_mul_real S x
  have hkk' : finPt S kk = (k : Bridge.Gf S) := hfk.trans (Subtype.ext hx)
  obtain ⟨ga, hga, gf, hgf, hγ⟩ := hsplit (γ : GA D S)
  have hfγ : Bridge.ratF S γ = finPt S gf := by
    change finPt S (γ : GA D S) = _
    rw [hγ]
    dsimp only [finPt]
    rw [map_mul]
    have : (finHom S).rangeRestrict ga = 1 := Subtype.ext (MonoidHom.mem_ker.1 hga)
    rw [this, one_mul]
  have eh : h = (γ : GA D S) * h' * ga⁻¹ * kk := by
    have eg : gf = (γ : GA D S) * ga⁻¹ := by
      rw [hγ, hcomm ga hga gf hgf, mul_inv_cancel_right]
    have e1 : h = gf * h' * kk := by
      set y := (gf * h' * kk)⁻¹ * h with hy
      have hyf : y ∈ GfC S := mul_mem (inv_mem (mul_mem (mul_mem hgf hh') hkk)) hh
      have hyi : y ∈ GinfC S := by
        have : finPt S y = 1 := by
          rw [hy]
          dsimp only [finPt] at hkk' hfγ e ⊢
          rw [map_mul, map_inv, map_mul, map_mul, hkk', ← hfγ]
          change _ * ((finHom S).rangeRestrict h) = 1
          rw [e]
          exact inv_mul_cancel _
        exact MonoidHom.mem_ker.2 (congrArg Subtype.val this)
      have := htriv y hyi hyf
      rw [hy, inv_mul_eq_one] at this
      exact this.symm
    rw [e1, eg, mul_assoc (γ : GA D S) ga⁻¹ h', hcomm ga⁻¹ (inv_mem hga) h' hh', ← mul_assoc]
  have hact : B.act ((γ⁻¹ : GQ S) : GA D S) = B.act ga⁻¹ := by
    have hr : GlobalTheory.ExportSeries.realGL B.F.θ S gf = 1 := by
      funext τ
      show Formalism.UG.bc (B.F.θ τ) (infHom S gf) = 1
      rw [MonoidHom.mem_ker.1 hgf, map_one]
    rw [Base.act, MonoidHom.comp_apply, MonoidHom.comp_apply, Subgroup.coe_inv, hγ, _root_.mul_inv_rev, map_mul, map_inv _ gf, hr,
      inv_one, one_mul]
  have hJ : finPt S kk ∈ B.levJ t := hkk' ▸ k.2
  have hθf : ∀ P, IsThetaFunO B.F.ψ S T (B.F.fock (B.vecFlat t) P) := Base.isThetaFunO_fock_vecAt hB hQ _
  have hk : ω (kk, 1) (B.F.fock (B.vecFlat t) P) = ((B.levLam t k : ℂˣ) : ℂ)⁻¹ • B.F.fock (B.vecFlat t) P := by
    have h1 := GlobalTheory.ExportSeries.DualType.dual_type_fock hB hS ht hQ hω hkk hJ P
    have e2 : ((B.levLam t ⟨_, hJ⟩ : ℂˣ) : ℂ) = ((B.levLam t k : ℂˣ) : ℂ) :=
      congrArg (fun z : B.levJ t => ((B.levLam t z : ℂˣ) : ℂ)) (Subtype.ext hkk')
    rw [← e2]
    exact h1
  have ha : ω (ga⁻¹, 1) (B.F.fock (B.vecFlat t) P) = B.F.fock (B.vecFlat t) (B.act ga⁻¹ P) :=
    GlobalTheory.RealFockAction.om_fock_vecAt D S T B t ω t.Q _ hB ht hQ hω ga⁻¹ (inv_mem hga) P
  have ep : ∀ g : GA D T, (((γ : GA D S) * h' * ga⁻¹ * kk, g) : GA D S × GA D T) =
      ((γ : GA D S), 1) * ((h', g) * ((ga⁻¹, 1) * (kk, 1))) := fun g => by
    ext <;> simp [mul_assoc]
  have key : ∀ g : GA D T, ω (h, g) (B.F.fock (B.vecFlat t) P) 0 =
      ((B.levLam t k : ℂˣ) : ℂ)⁻¹ * ω (h', g) (B.F.fock (B.vecFlat t) (B.act ga⁻¹ P)) 0 := fun g => by
    rw [eh, ep g, map_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply, hk, map_smul, ha,
      map_smul, map_smul, Pi.smul_apply, hω.om_aut _ γ.2 1 (one_mem _) _ (hω.om_pres _ _ (hθf _)), smul_eq_mul]
  refine funext fun g => ?_
  rw [Pi.smul_apply, smul_eq_mul, hact]
  exact key g

theorem series_triv (ρ : Setup D.ntw) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (h : GA D (Vc D j))
    (P : PolF D (Wc D j).rank (Vc D j).rank) :
    series (ρ.B i j b).F (ρ.om i j b (ρ.tw i b 0 ∅ 1).chi) ((ρ.B i j b).vecFlat (ρ.tw i b 0 ∅ 1)) h P = ρ.theta i j b h P := by
  have key : ∀ t : Twist D Circle, t.Q = ∅ → t.chi = 1 →
      series (ρ.B i j b).F (ρ.om i j b t.chi) ((ρ.B i j b).vecFlat t) h P = ρ.theta i j b h P := by
    rintro ⟨_, _, r⟩ rfl rfl
    show series _ _ ((ρ.B i j b).vecAt ∅ _) h P = series _ _ (ρ.B i j b).vecBase h P
    rw [Base.vecAt_empty]
  exact key _ (half_empty _) (charOf_one _ _)

theorem term_mem_span {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    {F : Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank} (hF : F ∈ (ρ.B i j b).formsC (ρ.tw i b 0 ∅ 1))
    {h : GA D (Vc D j)} (hh : h ∈ GfC (Vc D j)) :
    series (ρ.B i j b).F (ρ.om i j b (ρ.tw i b 0 ∅ 1).chi) ((ρ.B i j b).vecFlat (ρ.tw i b 0 ∅ 1)) h (F (finPt _ h)) ∈
      Submodule.span ℂ {f | ∃ s h P, ρ.IsDatum i j b s h P ∧ f = ρ.theta i j b h P} := by
  obtain ⟨hg, ha, -⟩ := GlobalTheory.TwistGood.tw_good D _ D.ntw ρ hρ i j b 0 ∅ 1 (twOK_one i 0)
  have hB := hρ.base i j b
  have hω := hρ.weil i j b _ hg
  obtain ⟨γ, s, h', k, hs, hoff, hh', hsupp, e⟩ := GlobalTheory.RankReps.exists_rep_split_levJ D ρ hρ i j b h hh
  have hlaw := ((ρ.B i j b).mem_formsC.1 hF).2 γ (finPt _ h') k
  have hval : F (finPt _ h') ∈ (ρ.B i j b).valSpace := ((ρ.B i j b).mem_formsC.1 hF).1 _
  have hinv : ((ρ.B i j b).act ((γ⁻¹ : GQ (Vc D j)) : GA D (Vc D j))) ((ρ.B i j b).act (γ : GA D (Vc D j)) (F (finPt _ h'))) =
      F (finPt _ h') := by
    rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [e, hlaw, LinearMap.map_smul, series_move hB (D.sp.V_sig _) hg ha hω hh hh' γ k e, hinv, smul_smul,
    mul_inv_cancel₀ (Units.ne_zero _), one_smul, series_triv]

  have hspan : F (finPt _ h') ∈ Submodule.span ℂ (ρ.lat i j b (ρ.eO i b).range h' : Set (PolF D (Wc D j).rank (Vc D j).rank)) := by
    have hm : ∀ τ, (ρ.B i j b).w.p τ + (ρ.B i j b).w.q τ ≤ (Wc D j).rank := fun τ => by
      have h1 := hB.sig τ
      have h2 := Formalism.BasicNotions.sig_sum _ hB.sigOK (tauE D τ)
      rw [← h1] at h2
      exact h2.le
    have h2 := (GlobalTheory.ExportSeries.HarmLattice.harmLat_fg_span D (Wc D j).rank (Vc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS _ (Formalism.L2.Host.embLL0 D) (labLL0 D)
      (ρ.eO i b).range ((ρ.B i j b).latAt (finPt _ h')) hB.wt hm (hρ.isCoefRing i b)
      (GlobalTheory.LatFull.latAt_isFullLattice D ρ hρ i j b h')).2
    have h3 : (ρ.lat i j b (ρ.eO i b).range h' : Set (PolF D (Wc D j).rank (Vc D j).rank)) =
        (harmLat (Formalism.L2.Host.embLL0 D) (labLL0 D) (ρ.eO i b).range (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS
          ((ρ.B i j b).latAt (finPt _ h')) : Set (PolF D (Wc D j).rank (Vc D j).rank)) := rfl
    rw [h3, h2]
    exact hval
  have hmap := Submodule.mem_map_of_mem (f := (ρ.B i j b).theta (ρ.om i j b 1) h') hspan
  rw [Submodule.map_span] at hmap
  refine Submodule.span_mono ?_ hmap
  rintro _ ⟨P, hP, rfl⟩
  exact ⟨s, h', P, ⟨hs, hoff, hh', hsupp, hP⟩, rfl⟩

theorem sum_mem_span {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    {F : Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank}
    (hF : F ∈ Submodule.span ℂ (ρ.mt i j b 0 ∅ 1 : Set (Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank))) :
    ρ.sum i j b 0 ∅ 1 F ∈ Submodule.span ℂ {f | ∃ s h P, ρ.IsDatum i j b s h P ∧ f = ρ.theta i j b h P} := by
  obtain ⟨hg, ha, -⟩ := GlobalTheory.TwistGood.tw_good D _ D.ntw ρ hρ i j b 0 ∅ 1 (twOK_one i 0)
  have hc := hρ.classes i j b _ hg ha
  induction hF using Submodule.span_induction with
  | mem F hF =>
    have hF' := ((ρ.B i j b).mem_mtLat _ _ _).1 hF
    rw [Setup.sum, Base.classSum_apply]
    exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (term_mem_span hρ i j b hF'.1 (hc.fin c))
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

end GlobalTheory.BaseClassSum

namespace GlobalTheory.TwInputs

theorem spanGood_of_sumOnto : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), ∀ i, SumOnto rd i → SpanGood rd i := by
  intro D ρ hρ rd i hS j b x hx
  obtain ⟨F, hF, e⟩ := hS j b x hx
  rw [e]
  exact GlobalTheory.BaseClassSum.sum_mem_span hρ i j b hF

end GlobalTheory.TwInputs
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodFormsSpannedByThetaSeriesOfClassSumsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodForms_spanned_by_thetaSeries_of_classSums : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), ∀ i, SumOnto rd i → SpanGood rd i := by
  first | exact @GlobalTheory.TwInputs.spanGood_of_sumOnto | exact GlobalTheory.TwInputs.spanGood_of_sumOnto | (intros; apply GlobalTheory.TwInputs.spanGood_of_sumOnto <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCoverComponentReadingsUnitModulusScalar
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCoverComponentReadingsUnitModulusScalar
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.CoverFrameMod

open CategoryTheory

section Weight

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem wchar_gen {S : Type} [CommRing S] (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (u : Sˣ) :
    wchar (ex Dw a n) (fun i : Ix Dw => Option.elim i u (fun _ => 1)) = (u : S) ^ n := by
  unfold wchar
  rw [Fintype.prod_option]
  simp [ex]

end Weight

variable {D : D7} {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ}

def midEmb (C : Cover T j σ) : C.c'.F →+* ℂ := C.σ₂.comp (C.d.eF : C.c'.F →+* C.d.c₂.F)


set_option maxHeartbeats 1600000 in
theorem exists_scalar (C : Cover T j σ) (hσ : C.σ₂.comp C.inc = σ) (y : FrPt (T.Q.Xo j) T.Q.c (CAt σ))
    (y₂ : FrPt C.d.Xo₂ C.d.c₂ (CAt C.σ₂))
    (hx : (y₂.x : Sp ℂ ⟶ C.d.Xo₂.X) ≫ C.d.r = (y.x : Sp ℂ ⟶ (T.Q.Xo j).X))
    (hu : ∀ τ i, (y₂.u τ i : Sp (DualNumber ℂ) ⟶ C.d.Xo₂.univ.t.G.left) ≫ C.d.m.φ =
      (y.u τ i : Sp (DualNumber ℂ) ⟶ (T.Q.Xo j).univ.t.G.left)) :
    ∃ t : ℂ, t ≠ 0 ∧
      (∀ (σ' : KA T.Q.l →+* ℂ) (σ₂' : KA C.d.l₂ →+* ℂ) (g : ℕ) (ty ty₂ : Fin g → (D.host.E →+* ℂ))
        (F : FamilyUnif (T.Q.Xo j) σ' ty) (F₂ : FamilyUnif C.d.Xo₂ σ₂' ty₂) (i : Fin F.n)
        (i₂ : Fin F₂.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (P₂ : (F₂.Di i₂).La →+ (Fin g → ℂ)),
        IsPeriod (F.Di i) ty P → IsPeriod (F₂.Di i₂) ty₂ P₂ → y.x = F.u i P →
        y₂.x = F₂.u i₂ P₂ → GlobalTheory.GeoLevel.NormPin F i P y → GlobalTheory.GeoLevel.NormPin F₂ i₂ P₂ y₂ → ‖t‖ = 1) ∧
      ∀ (n : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ), ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ f₂ : Rul C.d.Xo₂ C.d.c₂,
        C.IsPull f f₂ → toC (evR C.d.Xo₂ C.d.c₂ f₂ y₂) = t ^ n * toC (evR (T.Q.Xo j) T.Q.c f y) := by
  letI a₂ : Algebra C.d.c₂.F (CAt (midEmb C)) := RingHom.toAlgebra (R := C.d.c₂.F) (S := CAt (midEmb C)) C.σ₂
  letI a₀ : Algebra T.Q.c.F (CAt (midEmb C)) := RingHom.toAlgebra (R := T.Q.c.F) (S := CAt (midEmb C)) σ
  have hov : AlgOver T.Q.c C.c' C.hle (CAt (midEmb C)) := fun a => DFunLike.congr_fun hσ a
  have hc : ∀ a : C.c'.F, algebraMap C.d.c₂.F (CAt (midEmb C)) (C.d.eF a) = algebraMap C.c'.F (CAt (midEmb C)) a :=
    fun _ => rfl
  let y₀ : FrPt (T.Q.Xo j) T.Q.c (CAt (midEmb C)) := y
  let z : FrPt (T.Q.Xo j) C.c' (CAt (midEmb C)) := FrPt.ext C.hle hov y₀
  let w : FrPt C.d.Xo₂ C.d.c₂ (CAt (midEmb C)) := y₂
  obtain ⟨y', hy'⟩ := GlobalTheory.CoverSec.exists_frOver_below C.d hc w
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (T.Q.Xo j).s) hx).trans z.x_over))
  obtain ⟨t₀, ht⟩ := GlobalTheory.GeoLevel.exists_frBor_gen z y' (hy'.1.symm.trans hx)
    (funext fun τ => funext fun i => (hy'.2.1 τ i).symm.trans (hu τ i))
  refine ⟨toC (t₀ : CAt (midEmb C)), Units.ne_zero (M₀ := ℂ) t₀, ?_, fun n a f hf f₂ hp => ?_⟩
  · intro σ' σ₂' g ty ty₂ F F₂ i i₂ P P₂ p p₂ e e₂ N N₂
    exact norm_gen_eq_one_of_frOver C.d F₂ F i₂ i P₂ P y₂ z y' _ p₂ p e₂ e N₂ N hy' ht
  · have h1 := @hp (CAt (midEmb C)) (inferInstanceAs (Field ℂ)) a₀
      (inferInstanceAs (Algebra C.c'.F (CAt (midEmb C)))) a₂ hov hc w y' hy'
    have hb : FrBor (fun i => Option.elim i t₀ (fun _ => 1)) y₀ (y'.res C.hle hov) := ht
    have h2 := (GlobalTheory.Frames.algebraic_laws GlobalTheory.lawsFieldsSeparately.2.1 _ _ _ _ (T.Q.Xo j) T.Q.c).2.2.2.2.2.2
      (CAt (midEmb C)) (inferInstanceAs (IsReduced ℂ)) a n f hf _ _ _ hb
    rw [wchar_gen] at h2
    exact h1.trans h2


set_option maxHeartbeats 1600000 in
theorem comp_over_comp_norm : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ k₂ : C.U₂.Comp, ∃ (k : (T.U j σ).Comp) (γ : GL (Fin D.R.r) D.host.E), (((T.U j σ).X k).Λ : Set (Fin D.R.r → D.host.E)) = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec '' ((C.U₂.X k₂).Λ : Set _) ∧ (∀ v w, herm ((T.U j σ).X k).Gm ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm (C.U₂.X k₂).Gm v w) ∧ (∀ h, (C.dict₂ h).1 = k₂ → (T.dict j σ h).1 = k) ∧ ∀ (x : Frame (C.U₂.X k₂).Ψ D.R.r) (x' : Frame ((T.U j σ).X k).Ψ D.R.r), x ∈ (C.U₂.X k₂).dom → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X k₂).Ψ) (h₁ : τ ∈ ((T.U j σ).X k).Ψ), mat x' ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩) → x' ∈ ((T.U j σ).X k).dom ∧ ∃ t : ℂ, t ≠ 0 ∧ ((∀ τ i, ‖dmin (C.U₂.X k₂).Gm x τ i‖ = 1) → ‖t‖ = 1) ∧ ∀ n : ℕ, ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ), Dom a n → ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ → rdU C.U₂ f₂ k₂ x = t ^ n * rdU (T.U j σ) f k x' := by
  intro D T hT j hj σ hσ C hC k₂
  obtain ⟨h₀, rfl⟩ := GlobalTheory.CoverOnto.exists_dict₂_comp D T hT j hj σ hσ C hC k₂
  obtain ⟨γ, hΛ, hiso, hfr⟩ := GlobalTheory.CoverFrameMove.frames_differ D T hT j hj σ hσ C hC h₀
  refine ⟨(T.dict j σ h₀).1, γ, hΛ, hiso, fun h hh => GlobalTheory.CoverRead.CompIndep.comp_eq_of_cover D T hT j hj σ hσ C hC h h₀ hh,
    fun x x' hx hxx' => ?_⟩
  have hU := hT.unf j hj σ hσ
  have hU₂ := hC.2.2.2.1
  have hΨ : ∀ τ, τ ∈ ((T.U j σ).X (T.dict j σ h₀).1).Ψ ↔ τ ∈ (C.U₂.X (C.dict₂ h₀).1).Ψ :=
    fun τ => ((hU.2.1 _).2 τ).trans ((hU₂.2.1 _).2 τ).symm
  have hx' : x' ∈ ((T.U j σ).X (T.dict j σ h₀).1).dom :=
    GlobalTheory.FrameDom.mem_dom_of_isometry _ _ _ _ γ ((hU.2.1 _).1.trans (hU₂.2.1 _).1.symm) hΨ hiso x x' hx hxx'
  obtain ⟨o₁, o₂⟩ := GlobalTheory.T.coverFramedPoint_over_moved_base_frame D T hT j hj σ hσ C hC h₀ γ hΛ hiso hfr x x' hx hx' hxx'
  obtain ⟨t, ht, hn, hr⟩ := exists_scalar C hC.2.2.1 _ _ o₁ o₂
  refine ⟨hx', t, ht, fun hd => ?_, fun n a _ f hf f₂ _ hp => ?_⟩
  · have hd' : ∀ τ i, ‖dmin ((T.U j σ).X (T.dict j σ h₀).1).Gm x' τ i‖ = 1 := by
      rintro ⟨τ, h₁⟩ i
      rw [← hd ⟨τ, (hΨ τ).1 h₁⟩ i]
      unfold dmin
      rw [hxx' τ ((hΨ τ).1 h₁) h₁, GlobalTheory.FrameDom.gram_mul _ _ _ hiso τ]
    obtain ⟨g, e, F, ik, φ, -, hP⟩ := hU.2.2.2.2.2
    obtain ⟨g₂, e₂, F₂, ik₂, φ₂, -, hP₂⟩ := hU₂.2.2.2.2.2
    obtain rfl : g₂ = g := Fin.equiv_iff_eq.1 ⟨e₂.trans e.symm⟩
    obtain ⟨P, -, p, u, -, N⟩ := hP _ ⟨x', hx'⟩
    obtain ⟨P₂, -, p₂, u₂, -, N₂⟩ := hP₂ _ ⟨x, hx⟩
    exact hn _ _ _ _ _ F F₂ _ _ P P₂ p p₂ u u₂ (N hd') (N₂ hd)
  · have e : rdU (T.U j σ) f (T.dict j σ h₀).1 x' =
        toC (evR (T.Q.Xo j) T.Q.c f ((T.U j σ).un (T.dict j σ h₀).1 ⟨x', hx'⟩)) := dif_pos hx'
    rw [e]
    exact (dif_pos hx).trans (hr n a f hf f₂ hp)

end GlobalTheory.CoverFrameMod
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCoverComponentReadingsUnitModulusScalarStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCover_component_readings_unit_modulus_scalar : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ k₂ : C.U₂.Comp, ∃ (k : (T.U j σ).Comp) (γ : GL (Fin D.R.r) D.host.E), (((T.U j σ).X k).Λ : Set (Fin D.R.r → D.host.E)) = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec '' ((C.U₂.X k₂).Λ : Set _) ∧ (∀ v w, herm ((T.U j σ).X k).Gm ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm (C.U₂.X k₂).Gm v w) ∧ (∀ h, (C.dict₂ h).1 = k₂ → (T.dict j σ h).1 = k) ∧ ∀ (x : Frame (C.U₂.X k₂).Ψ D.R.r) (x' : Frame ((T.U j σ).X k).Ψ D.R.r), x ∈ (C.U₂.X k₂).dom → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X k₂).Ψ) (h₁ : τ ∈ ((T.U j σ).X k).Ψ), mat x' ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩) → x' ∈ ((T.U j σ).X k).dom ∧ ∃ t : ℂ, t ≠ 0 ∧ ((∀ τ i, ‖dmin (C.U₂.X k₂).Gm x τ i‖ = 1) → ‖t‖ = 1) ∧ ∀ n : ℕ, ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ), Dom a n → ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ → rdU C.U₂ f₂ k₂ x = t ^ n * rdU (T.U j σ) f k x' := by
  first | exact @GlobalTheory.CoverFrameMod.comp_over_comp_norm | exact GlobalTheory.CoverFrameMod.comp_over_comp_norm | (intros; apply GlobalTheory.CoverFrameMod.comp_over_comp_norm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCharactersTypePlacesEqLocalComponents
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCharactersTypePlacesEqLocalComponents
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem GlobalTheory.TwInputs.tau_eq_locK : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), ValLL0 D cf → ∀ τ : ℕ → ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (ZMod (D.host.g kv.1))ˣ →* (↥D.LL0)ˣ, (∀ i j b kv x, 1 ≤ j → j ≤ D.R.m → ((Bs.exp.tauG i j b kv x : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) = sideEmb D.ntw i b ((τ j kv x : (↥D.LL0)ˣ) : ↥D.LL0)) → ∀ (j : Fin D.R.m) (kv : Σ k : Fin 2, D.nd.PlG k) (x : (ZMod (D.host.g kv.1))ˣ) (u : 𝓞 D.host.E) (hu : (u : D.host.E) ≠ 0), (((x : ZMod (D.host.g kv.1)).val : 𝓞 D.host.E) - u) ∈ (NX.pG D kv).asIdeal → embLL0 D ((τ (j.1 + 1) kv x : (↥D.LL0)ˣ) : ↥D.LL0) = (((cf.mu0 j).locK (NX.pG D kv) (Units.mk0 (u : D.host.E) hu) : ℂˣ) : ℂ) := by
  intro hGAR D cf Rw low Pq S hL eig θ Bs hV τ hτ j kv x u hu0 hxu0
  obtain ⟨k, v⟩ := kv
  have hgp : (D.host.g k).Prime := D.host.g_prime k
  haveI : Fact (D.host.g k).Prime := ⟨hgp⟩
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨p, hpg, hp⟩ := Nat.exists_infinite_primes (D.host.g k + 1)
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨w, hw⟩⟩ := Formalism.BasicNotions.Examples₂.PlOver.plNe D p
  obtain ⟨i, hi, -⟩ := Bs.cover w
  have hk : D.ntw.l i ≠ D.host.g k := by rw [hi, hw]; omega
  obtain ⟨art, ha⟩ := hGAR D.host.E D.nd.Om
  obtain ⟨ρ⟩ := GlobalTheory.Triple.Reading.nonempty (X := D.ntw) i true
  obtain ⟨n, hn⟩ := GlobalTheory.TwChiGal.firstTwistCharacter_eq_ladic_heckeCharacter D cf Bs.chiD Bs.chi Bs.eta_eq Bs.ringSpec_normalisedCharacter_eq Bs.del_eq hV art ha i true ρ j
  have hl := GlobalTheory.Triple.Model.notMem_l (X := D.ntw) hk v
  have hgw : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := D.naut.plGw_over k v
  have hspl := GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) hgp (D.nd.g_split k) (D.naut.plGw k v) hgw
  have hN : normV (D.naut.plGw k v) = D.host.g k := by
    rw [← hspl.1, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  have hg2 := hgp.two_le
  have hAw : IsPlaceOver (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v) := D.nd.plOm.2 _
  have hu : u ∉ (D.naut.plGw k v).asIdeal := by
    intro h
    have h1 : (((x : ZMod (D.host.g k)).val : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := by
      have := (D.naut.plGw k v).asIdeal.add_mem hxu0 h
      rwa [sub_add_cancel] at this
    obtain ⟨a, c, hac⟩ : IsCoprime (((x : ZMod (D.host.g k)).val : ℕ) : 𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.E) :=
      (ZMod.val_coe_unit_coprime x).cast
    apply (D.naut.plGw k v).isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hac]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ hgw)
  haveI : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq
    (algebraMap D.host.E D.nd.Om (((D.host.g k : ℕ) : 𝓞 D.host.E) : D.host.E))
    (show 0 < normV (D.naut.plGw k v) - 1 by omega)
  have hxu : IsUnitAt (D.naut.plGw k v) (atFin (D.naut.plGw k v) (Units.mk0 (u : D.host.E) hu0)) := by
    show Valued.v (((u : D.host.E) : (D.naut.plGw k v).adicCompletion D.host.E)) = 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem _).2 hu
  obtain ⟨σ, hσI, hσart, hσval⟩ := GlobalTheory.TameRecip.exists_ine_of_unit hGAR D.host.E D.nd.Om art ha
    (D.naut.plGw k v) _ hAw _ hgw hspl.2.1 π hπ (atFin (D.naut.plGw k v) (Units.mk0 (u : D.host.E) hu0)) u hxu
    (by simp [atFin])
  have hTR : NX.TameRep (D.naut.plGw k v) 1 σ u :=
    ⟨_, hAw, hσI, _, π, hgw, hspl.2.1, hπ, by simpa using hσval⟩
  have e1 := hn.loc (Or.inl hl) hσart.symm
  obtain ⟨h1, -, h3, -, h5⟩ := GlobalTheory.GalChar.inertialOrderFifteenChar_auxiliaryPrime_spec (GlobalTheory.Triple.hframe cf) (l := D.ntw.l i)
  have hdel : (cf.delAt (D.ntw.l i)).UnrAt (D.naut.plGw k v) :=
    h5.unr _ (GlobalTheory.GalChar.notMem_of_ne (D.host.g_prime k) h1 (h3 k).symm (D.naut.plGw_over k v))
  have hloc (a b : HChar D.host.E) (v : HeightOneSpectrum (𝓞 D.host.E))
      (x : (v.adicCompletion D.host.E)ˣ) : (a * b).loc v x = a.loc v x * b.loc v x := rfl
  rw [GlobalTheory.Triple.blockChar, GlobalTheory.GalChar.block_loc (cf.isEta.unr _) hxu, GlobalTheory.Triple.muBase, hloc,
    hdel _ hxu, mul_one] at e1
  have hm : ((normV (D.naut.plGw k v) - 1 : ℕ) : 𝓞 D.host.E) ∉ (D.naut.plGw k v).asIdeal := by
    rw [hN]
    intro h
    apply (D.naut.plGw k v).isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have := (D.naut.plGw k v).asIdeal.sub_mem hgw h
    rwa [Nat.cast_sub (by omega), Nat.cast_one, sub_sub_cancel] at this
  have hex : ∃ s : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om, NX.TameRep (D.naut.plGw k v) 1 s u := ⟨σ, hTR⟩
  have e2 : NX.tameVal (D.ntw.chi1 i (j.1 + 1) true) (D.naut.plGw k v) 1 u = D.ntw.chi1 i (j.1 + 1) true σ := by
    unfold NX.tameVal
    rw [dite_eq_left hex]
    refine GlobalTheory.T.tameChar_eq_of_tameRep_congr (D.naut.plGw k v) (D.ntw.twistBaseCoefficientRing_isAdic i) _ (D.ntw.twistCharacterFamily_continuous i (j.1 + 1) true) (by omega) hm
      (fun A hA s hs => ?_) _ _ u u hex.choose_spec hTR (by rw [sub_self]; exact zero_mem _)
    rw [hN]
    exact D.ntw.twistCharacterFamily_tame i (j.1 + 1) true k _ hgw hl A hA s hs
  have e3 := Bs.exp.tau_galois_first_character i (j.1 + 1) true ⟨k, v⟩ x u (by omega) (by omega) hl hxu0
  rw [hτ i (j.1 + 1) true ⟨k, v⟩ x (by omega) (by omega), Bs.exp.sgnG_one, Bs.exp.sgnT_one, one_mul] at e3
  have e4 : GlobalTheory.Triple.embSide D.ntw i true ((τ (j.1 + 1) ⟨k, v⟩ x : (↥D.LL0)ˣ) : ↥D.LL0) =
      algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) ((D.ntw.chi1 i (j.1 + 1) true σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) := by
    apply (IsFractionRing.map (A := D.ntw.O0 i) (B := D.ntw.O i) (K := FractionRing (D.ntw.O0 i))
      (L := FractionRing (D.ntw.O i)) (D.ntw.O_inj i)).injective
    rw [← e2]
    refine e3.trans ?_
    simp only [IsFractionRing.map, IsLocalization.map_eq]
    rfl
  rw [← ρ.read, e4]
  exact e1

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCharactersTypePlacesEqLocalComponentsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCharacters_typePlaces_eq_local_components : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), ValLL0 D cf → ∀ τ : ℕ → ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (ZMod (D.host.g kv.1))ˣ →* (↥D.LL0)ˣ, (∀ i j b kv x, 1 ≤ j → j ≤ D.R.m → ((Bs.exp.tauG i j b kv x : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) = sideEmb D.ntw i b ((τ j kv x : (↥D.LL0)ˣ) : ↥D.LL0)) → ∀ (j : Fin D.R.m) (kv : Σ k : Fin 2, D.nd.PlG k) (x : (ZMod (D.host.g kv.1))ˣ) (u : 𝓞 D.host.E) (hu : (u : D.host.E) ≠ 0), (((x : ZMod (D.host.g kv.1)).val : 𝓞 D.host.E) - u) ∈ (NX.pG D kv).asIdeal → embLL0 D ((τ (j.1 + 1) kv x : (↥D.LL0)ˣ) : ↥D.LL0) = (((cf.mu0 j).locK (NX.pG D kv) (Units.mk0 (u : D.host.E) hu) : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.TwInputs.tau_eq_locK | exact GlobalTheory.TwInputs.tau_eq_locK | (intros; apply GlobalTheory.TwInputs.tau_eq_locK <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StarMulSelfOfPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.CoefUniq

open GlobalTheory.CoefModel

theorem schur_scalar : ∀ (D : D7) (V : HSp D) (θ : InfFam D) (c : CoefA V) (lam : D.what₂.Tau → DomWeight V.rank)
    (c0 c0' : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.coef.W), IsInfFam θ → c.Is →
    Bridge.CoefMapTie V c.coef c0 (rhoVr (labLL D) lam) → Bridge.CoefMapTie V c.coef c0' (rhoVr (labLL D) lam) →
    ∃ ζ : ℂ, ∀ F, c0' F = ζ • c0 F := by
  intro D V θ c lam c0 c0' hθ hc ht ht'
  obtain ⟨E, hE, hEρ⟩ := GlobalTheory.CoefReal.exists_real_model V θ c lam c0 hθ hc ht
  obtain ⟨E', hE', hEρ'⟩ := GlobalTheory.CoefReal.exists_real_model V θ c lam c0' hθ hc ht'
  let ψ : Module.End ℂ c.W := E'.toLinearMap ∘ₗ E.symm.toLinearMap
  have hψ : ∀ u ∈ GinfC V, ∀ w, ψ (c.ρ u w) = c.ρ u (ψ w) := fun u hu w => by
    obtain ⟨v, rfl⟩ := E.surjective w
    change E' (E.symm (c.ρ u (E v))) = c.ρ u (E' (E.symm (E v)))
    rw [hEρ u hu, E.symm_apply_apply, E.symm_apply_apply, hEρ' u hu]
  haveI := hc.2.2.2.1
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue ψ
  have hU := GlobalTheory.GenRealSchur.irr_real c hc (Module.End.eigenspace ψ μ) fun u hu => by
    rintro _ ⟨w, hw, rfl⟩
    have hw' : ψ w = μ • w := Module.End.mem_eigenspace_iff.1 hw
    exact Module.End.mem_eigenspace_iff.2 (by rw [hψ u hu, hw', map_smul])
  rcases hU with h0 | h0
  · exact absurd h0 hμ
  refine ⟨μ, fun F => ?_⟩
  have h1 : E (mapVV D.what₂.embLL lam F) ∈ Module.End.eigenspace ψ μ := h0 ▸ Submodule.mem_top
  rw [Module.End.mem_eigenspace_iff] at h1
  rw [← hE, ← hE']
  exact (congrArg E' (E.symm_apply_apply _)).symm.trans h1

theorem scalar_of_basis : ∀ {K V W ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]
    [Fintype ι] [Nonempty ι] (σ : K →+* ℂ) (b : Module.Basis ι K V) (c : V →ₛₗ[σ] W),
    LinearIndependent ℂ (fun i => c (b i)) → ∀ (φ : V →ₗ[K] V) (ζ : ℂ), (∀ v, c (φ v) = ζ • c v) →
    ∃ a : K, σ a = ζ ∧ ∀ v, φ v = a • v := by
  intro K V W ι _ _ _ _ _ _ _ σ b c hli φ ζ hφ
  classical
  have key : ∀ i k, σ (b.repr (φ (b i)) k) = if k = i then ζ else 0 := by
    intro i
    have e1 : c (φ (b i)) = ∑ k, σ (b.repr (φ (b i)) k) • c (b k) := by
      conv_lhs => rw [← b.sum_repr (φ (b i))]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [LinearMap.map_smulₛₗ]
    have e2 : ∑ k, (if k = i then ζ else 0) • c (b k) = ζ • c (b i) := by
      simp [ite_smul]
    have h1 : ∑ k, (σ (b.repr (φ (b i)) k) - if k = i then ζ else 0) • c (b k) = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, ← e1, e2, hφ, sub_self]
    intro k
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli _ h1 k)
  obtain ⟨i0⟩ := ‹Nonempty ι›
  set a := b.repr (φ (b i0)) i0 with ha
  have hd : ∀ i, b.repr (φ (b i)) i = a := fun i => σ.injective (by rw [key, key, if_pos rfl, if_pos rfl])
  have ho : ∀ i k, k ≠ i → b.repr (φ (b i)) k = 0 := fun i k hk => σ.injective (by rw [key, if_neg hk, map_zero])
  have hb : ∀ i, φ (b i) = a • b i := by
    intro i
    refine b.repr.injective (Finsupp.ext fun k => ?_)
    rw [map_smul, Finsupp.smul_apply, b.repr_self, Finsupp.single_apply, smul_eq_mul]
    by_cases hk : i = k
    · subst hk
      rw [if_pos rfl, mul_one, hd]
    · rw [if_neg hk, mul_zero, ho i k (Ne.symm hk)]
  have hφa : φ = a • LinearMap.id := b.ext fun i => by rw [hb i]; rfl
  refine ⟨a, (key i0 i0).trans (if_pos rfl), fun v => ?_⟩
  rw [hφa]
  rfl

theorem pow_eq_one_of_cmMax {K : Type} [Field K] [NumberField K] [StarRing K] {a : K} (hm : a ∈ Formalism.DivisionValues.cmMax K)
    (hs : star a * a = 1) (hi : IsIntegral ℤ a) : ∃ n : ℕ, n ≠ 0 ∧ a ^ n = 1 := by
  obtain ⟨n, hn, h⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one K ℂ hi (fun φ => by
    have h1 := congrArg φ hs
    rw [map_mul, map_one, show φ (star a) = starRingEnd ℂ (φ a) from hm φ, Complex.conj_mul'] at h1
    have h2 : ‖φ a‖ ^ 2 = 1 := by exact_mod_cast h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2)
  exact ⟨n, hn.ne', h⟩

theorem mem_of_coords {K V ι : Type} [Field K] [AddCommGroup V] [Module K V] (K0 : Subfield K) (b : Module.Basis ι K V)
    {y : V} (a : K) (hy : y ≠ 0) (h1 : ∀ k, b.repr (a • y) k ∈ K0) (h2 : ∀ k, b.repr y k ∈ K0) : a ∈ K0 := by
  obtain ⟨k, hk⟩ : ∃ k, b.repr y k ≠ 0 := by
    by_contra hc
    exact hy (b.repr.injective (Finsupp.ext fun k => by simpa using not_not.1 (fun h => hc ⟨k, h⟩)))
  have e1 : a = b.repr (a • y) k * (b.repr y k)⁻¹ := by
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, mul_inv_cancel_right₀ hk]
  rw [e1]
  exact K0.mul_mem (h1 k) (K0.inv_mem (h2 k))

theorem star_mul_self_of_pair {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    (pair : V →ₗ⋆[K] V →ₗ[K] K) (a : K) {y : V} (hy : pair y y ≠ 0) (h : pair (a • y) (a • y) = pair y y) :
    star a * a = 1 := by
  have e1 : pair (a • y) (a • y) = star a * a * pair y y := by
    rw [map_smul, LinearMap.map_smulₛₗ₂, smul_eq_mul, smul_eq_mul, starRingEnd_apply]
    ring
  rw [e1] at h
  exact mul_right_cancel₀ hy (h.trans (one_mul _).symm)

theorem pair_ne_zero {K V W : Type} [Field K] [AddCommGroup V] [Module K V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (σ : K →+* ℂ) (coef : V →ₛₗ[σ] W) (hinj : Function.Injective coef) (q : V → V → K)
    (hq : ∀ x x', inner ℂ (coef x) (coef x') = σ (q x x')) {x : V} (hx : x ≠ 0) : q x x ≠ 0 := fun h0 => by
  have h1 := hq x x
  rw [h0, map_zero] at h1
  exact hx (hinj ((inner_self_eq_zero.1 h1).trans (map_zero coef).symm))

theorem isIntegral_of_keeps {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (L : Submodule (𝓞 K) V) (hne : L ≠ ⊥) (hfg : L.FG) (a : K) (h : ∀ n ∈ L, a • n ∈ L) :
    IsIntegral ℤ a := by
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 (isIntegral_of_smul_mem_submodule L hne hfg a h)
  rw [← hy]
  exact NumberField.RingOfIntegers.isIntegral_coe y

theorem isFullLattice_hLat {D : D7} (V : HSp D) (g : Bridge.Gf V) :
    Submodule.IsFullLattice D.host.E (Bridge.hLat V g) := by
  obtain ⟨-, -, hfg, hsp, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  obtain ⟨Λ, hΛ, h1, h2, -⟩ := GlobalTheory.AdLat.exists_lattice_latOf
    D.host.F D.host.E V.rank (GlobalTheory.Member.latC V) g.1 hfg hsp
  rw [SetLike.coe_injective ((GlobalTheory.RepsCompare.coe_hLat V g).trans hΛ.symm)]
  letI : Submodule.IsLattice D.host.E Λ := Submodule.IsLattice.of_fg D.host.E h1
  exact ⟨h2⟩

theorem exists_root_of_unity : ∀ (D : D7) (X : RealSide D) (c c₂ : ∀ j : Fin D.R.m, VV D.what₂.LL (FWT.lamV D j) →ₛₗ[D.what₂.embLL] (X.R.cV j).W), IsCoef X c → IsCoef X c₂ → ∀ j, ∃ (ζ : ℂ) (n : ℕ), n ≠ 0 ∧ ζ ^ n = 1 ∧ ∀ F, c₂ j F = ζ • c j F := by
  intro D X c c₂ hc hc₂ j
  obtain ⟨g, c0R, h⟩ := hc
  obtain ⟨g₂, c0R₂, h₂⟩ := hc₂
  obtain ⟨ζ, hζ⟩ := schur_scalar D (Vc D j) X.R.θ (X.R.cV j) (FWT.lamV D j) (c j) (c₂ j) X.char.models.inf
    (X.char.models.cV j) (h.mapL j) (h₂.mapL j)
  rcases subsingleton_or_nontrivial (VV D.what₂.LL (FWT.lamV D j)) with hs | hs
  · refine ⟨1, 1, one_ne_zero, one_pow _, fun F => ?_⟩
    rw [Subsingleton.elim F 0, map_zero, map_zero, smul_zero]
  obtain ⟨e, hrat, hco, hpa, hnab, -⟩ := h.coefL j X.A3.A.μ0
  obtain ⟨e₂, hrat₂, hco₂, hpa₂, hnab₂, -⟩ := h₂.coefL j X.A3.A.μ0

  have hφ : ∀ v, c j ((e₂.symm.trans e) v) = ζ • c j v := fun v =>
    (hco (e₂.symm v)).symm.trans ((hco₂ _).trans ((congrArg (c₂ j) (e₂.apply_symm_apply v)).trans (hζ v)))
  haveI : Nonempty _ := (bVV D.what₂.LL (FWT.lamV D j)).index_nonempty
  obtain ⟨a, hζa, ha⟩ := scalar_of_basis D.what₂.embLL (bVV D.what₂.LL (FWT.lamV D j)) (c j) (h.mapL j).2.1
    (e₂.symm.trans e).toLinearMap ζ hφ
  have hea : ∀ x, e x = a • e₂ x := fun x =>
    (congrArg e (e₂.symm_apply_apply x)).symm.trans (ha (e₂ x))
  haveI := e.toEquiv.nontrivial
  obtain ⟨i0⟩ := (X.A3.A.MtCSD j X.A3.A.μ0).bV.index_nonempty
  have hx0 := (X.A3.A.MtCSD j X.A3.A.μ0).bV.ne_zero i0
  have hy0 : e₂ ((X.A3.A.MtCSD j X.A3.A.μ0).bV i0) ≠ 0 := fun h0 => hx0 (e₂.injective (h0.trans (map_zero e₂).symm))
  have hm : a ∈ Formalism.DivisionValues.cmMax D.what₂.LL :=
    mem_of_coords _ (bVV D.what₂.LL (FWT.lamV D j)) a hy0 (fun k => hea _ ▸ hrat i0 k) (hrat₂ i0)
  have hs : star a * a = 1 := by
    have hinj := GlobalTheory.GalLift.rescale_inj _ D.what₂.embLL _ (X.R.B.L j X.A3.A.μ0).pres.coef_li
    have hp0 := pair_ne_zero D.what₂.embLL _ hinj _ (X.R.B.L j X.A3.A.μ0).pres.coef_pair hx0
    refine star_mul_self_of_pair _ a ((hpa₂ _ _).trans_ne hp0) ?_
    rw [← hea, hpa, hpa₂]
  have hi : IsIntegral ℤ a := by
    obtain ⟨cl, -⟩ := ((X.R.B.L j X.A3.A.μ0).pres.reps 1).exists
    have hL := nabAtr_isLattice (labLL D) (FWT.lamV D j) _
      (isFullLattice_hLat (Vc D j) ((X.R.B.L j X.A3.A.μ0).pres.y cl))
    refine isIntegral_of_keeps _ (fun h0 => ?_) hL.fg a (fun n hn => ?_)
    · let M := fun τ => dualFr (tauLat (labLL D) τ (Bridge.hLat (Vc D j) ((X.R.B.L j X.A3.A.μ0).pres.y cl)))
      have hM : ∀ τ, Submodule.IsFullLattice D.what₂.LL (M τ) := fun τ =>
        dualFr_tauLat_isLattice (labLL D) τ _
          (isFullLattice_hLat (Vc D j) ((X.R.B.L j X.A3.A.μ0).pres.y cl))
      obtain ⟨d, hd, -, hd2⟩ := nb_global (nb_comm_nab (FWT.lamV D j)) M hM
      have hd' : algebraMap (𝓞 D.what₂.LL) D.what₂.LL d ≠ 0 := by
        rwa [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
      have h1 : Submodule.span D.what₂.LL (nabAtr (labLL D) (FWT.lamV D j) (Bridge.hLat (Vc D j) ((X.R.B.L j X.A3.A.μ0).pres.y cl)) : Set (VV D.what₂.LL (FWT.lamV D j))) = ⊤ := by
        apply Submodule.map_injective_of_injective (f := (VV D.what₂.LL (FWT.lamV D j)).subtype) (VV D.what₂.LL (FWT.lamV D j)).injective_subtype
        rw [Submodule.map_top, Submodule.range_subtype, Submodule.map_span]
        apply le_antisymm
        · rw [Submodule.span_le]
          rintro _ ⟨x, -, rfl⟩
          exact x.2
        · refine le_trans (le_of_eq (nb_VV_eq_bid (FWT.lamV D j))) ?_
          rw [Submodule.span_le]
          intro P hP
          have hP1 : P ∈ nabStd D.what₂.LL (FWT.lamV D j) := by
            rw [nb_nabStd_eq]
            exact Submodule.subset_span hP
          have hP2 := hd2 P hP1
          have hP3 : d • P ∈ VV D.what₂.LL (FWT.lamV D j) := nb_le_VV (nb_comm_nab (FWT.lamV D j)) M hM _ hP2
          have hP4 : d • P ∈ Submodule.span D.what₂.LL ((VV D.what₂.LL (FWT.lamV D j)).subtype ''
              (nabAtr (labLL D) (FWT.lamV D j) (Bridge.hLat (Vc D j) ((X.R.B.L j X.A3.A.μ0).pres.y cl)) : Set (VV D.what₂.LL (FWT.lamV D j)))) :=
            Submodule.subset_span ⟨⟨d • P, hP3⟩, hP2, rfl⟩
          have := Submodule.smul_mem _ (algebraMap (𝓞 D.what₂.LL) D.what₂.LL d)⁻¹ hP4
          rwa [nb_osmul, smul_smul, inv_mul_cancel₀ hd', one_smul] at this
      rw [h0, Submodule.bot_coe, Submodule.span_zero_singleton] at h1
      exact bot_ne_top h1
    · rw [← hnab₂ cl] at hn
      obtain ⟨m, hm, rfl⟩ := hn
      rw [← hnab cl]
      exact ⟨m, hm, hea m⟩
  obtain ⟨n, hn, han⟩ := pow_eq_one_of_cmMax hm hs hi
  exact ⟨ζ, n, hn, by rw [← hζa, ← map_pow, han, map_one], hζ⟩

end GlobalTheory.CoefUniq

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThFEqIntegral
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.LiftClassSum

theorem exists_low (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (j : Fin D.R.m) :
    ∃ u : ∀ ρ, lowT (X.R.MW j (sg0 D X.A3.A)) ρ, (fun ρ => (u ρ : ↥((X.R.MW j (sg0 D X.A3.A)).sm ρ))) = X.geo.v₀ j (sg0 D X.A3.A) := by
  have h := (Y.Z.vec j).1
  exact ⟨fun ρ => ⟨X.geo.v₀ j _ ρ, (h ρ).2.1⟩, rfl⟩


open Classical in
theorem sum_eq_classSum_ωP (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (t : X.T) (hxi : X.R.xi t = (Y.Z.ρ.B i j b).de.chi) (hQ : X.R.Q t = (Y.Z.ρ.B i j b).de.Q) :
    Y.Z.ρ.sum i j b 0 ∅ 1 = (Y.Z.ρ.B i j b).classSum (X.R.ωP j t) (Y.Z.ρ.tw i b 0 ∅ 1) (Y.Z.ρ.rep i j b (Y.Z.ρ.tw i b 0 ∅ 1)) := by
  have hB : GlobalTheory.ConjTwist.BaseOf X.R.toRealDat j (Y.Z.ρ.B i j b) :=
    GlobalTheory.PinBase.baseOf_of_pin D X Y.Z.ρ Y.Z.good Y.Z.pin i j b
  have hG : (Y.Z.ρ.B i j b).Good := Y.Z.good.base i j b
  have htup : GlobalTheory.ConjTwist.IsTupOf X.R.toRealDat (Y.Z.ρ.B i j b) (Twist.triv Circle ∅) t := by
    classical
    exact
      ⟨by rw [hxi]; exact (mul_one _).symm, by rw [hQ]; exact (Finset.union_empty _).symm⟩
  have h1 : IsWeilDatumO X.R.toRealDat.ψ (Vc D j) (Wc D j) (Lift.chrTh (X.R.toRealDat.toLevCh.mu t) X.R.toRealDat.eta ((j : ℕ) + 1)).1
      (Lift.chrTh (X.R.toRealDat.toLevCh.mu t) X.R.toRealDat.eta ((j : ℕ) + 1)).2 (Y.Z.ρ.om i j b 1) := by
    have := Y.Z.good.weil_base i j b
    rw [Base.IsWeil, show (1 : (AE D)ˣ →* Circle) = (Twist.triv Circle ∅ : Twist D Circle).chi from rfl,
      hB.mu_mul htup, hB.ψ, hB.eta] at this
    exact this
  have hu := (GlobalTheory.SplitChange.change_of_splitting D X.R.toRealDat.ψ (Vc D j) (Wc D j) (X.R.toRealDat.toLevCh.mu t) X.R.toRealDat.eta (Y.Z.ρ.B i j b).mu0
    ((j : ℕ) + 1) (X.R.ωP j t) (X.char.thP.ωP j t) hG.hecke hG.real).2.2 _ h1
  have key : ∀ τ : Twist D Circle, τ.Q = ∅ → τ.chi = 1 → ∀ (h : GA D (Vc D j)) (P : PolF D (Wc D j).rank (Vc D j).rank),
      series (Y.Z.ρ.B i j b).F (Y.Z.ρ.om i j b τ.chi) ((Y.Z.ρ.B i j b).vecFlat τ) h P =
        series (Y.Z.ρ.B i j b).F (X.R.ωP j t) ((Y.Z.ρ.B i j b).vecFlat τ) h P := by
    rintro ⟨Q0, c0, r0⟩ hq hc h P
    dsimp only at hq hc
    subst hq hc
    funext g
    rw [series_apply, series_apply]
    have ht := Base.isThetaFunO_fock_vecAt hG (Base.admissible_empty_of_good hG) (fun _ _ => (1 : ℂ)) P
    rw [hB.ψ] at ht
    exact congrFun (hu (h, g) _ ht) 0
  apply LinearMap.ext
  intro F
  rw [Setup.sum, Base.classSum_apply, Base.classSum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [key _ (half_empty _) (charOf_one _ _)]

end GlobalTheory.LiftClassSum

end
end
