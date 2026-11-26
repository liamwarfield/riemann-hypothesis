module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulOriginSec
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.KernelPolarisationTrivialOfSectionsVanishZero
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsHomOfLinearScalingHermForm
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqZeroOfSumEmbeddingSmul
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HolomorphicUniformizationTangentUnimodularRiemann
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.OneMulConjFracOneEqInvDifferent
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.OriginLineBundlePolarisation
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.OriginLineBundlePolarisation
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw

namespace GlobalTheory.WeierstrassCurve

theorem appLE_top_eq_zero_iff {X T : Scheme.{0}} (t : T ⟶ X) {U : X.Opens} (h : ⊤ ≤ t ⁻¹ᵁ U)
    (a : Γ(X, U)) : (t.appLE U ⊤ h).hom a = 0 ↔ (t.app U).hom a = 0 := by
  have e : (t.appLE U ⊤ h).hom a = resG _ h ((t.app U).hom a) := rfl
  rw [e]
  refine ⟨fun h0 => ?_, fun h0 => by rw [h0, map_zero]⟩
  have := congrArg (resG _ (le_top : t ⁻¹ᵁ U ≤ ⊤)) h0
  rwa [Cartier.resG_resG, Cartier.resG_self, map_zero] at this

theorem appLE_originSec_eq_zero_iff {R : Type} [CommRing R] (W : WeierstrassCurve R) {T : Scheme.{0}}
    (t : T ⟶ scheme W) (i : (originLB W).ι) (h : ⊤ ≤ t ⁻¹ᵁ (originLB W).U i) :
    (t.appLE ((originLB W).U i) ⊤ h).hom ((originSec W).f i) = 0 ↔ t = t ≫ toSpec W ≫ zero W := by
  rw [appLE_top_eq_zero_iff]
  constructor
  · intro h0
    rcases i with _ | _
    · have h1 : (1 : Γ(T, t ⁻¹ᵁ coordOpen W 2)) = 0 := (map_one _).symm.trans h0
      have hT : IsEmpty T := ⟨fun p => by
        have := congrArg (T.presheaf.germ (t ⁻¹ᵁ coordOpen W 2) p (h (Set.mem_univ p))).hom h1
        rw [map_one, map_zero] at this
        exact absurd this one_ne_zero⟩
      refine (eq_comp_zero_iff W t).2 ⟨fun p _ => (hT.false p).elim, Cartier.ext_germ fun p _ => (hT.false p).elim⟩
    · exact (eq_comp_zero_iff W t).2 ⟨h, h0⟩
  · intro e
    have h0 := (secPull_originSec_eq_zero_iff W t).2 e (fun _ => i)
    have := congrArg (resG T (Cartier.pull_U (originLB W) t (fun _ => i)).ge) h0
    rw [map_zero] at this
    exact ((Cartier.resG_resG _ _ _).trans (Cartier.resG_self _ _)).symm.trans this

theorem appLE_sec_pull_originLB_eq_zero {R : Type} [CommRing R] (W : WeierstrassCurve R)
    {R' : Type} [CommRing R'] {f : Sp R' ⟶ Sp R} {Y : Scheme.{0}} {φ : Y ⟶ scheme W} {q : Y ⟶ Sp R'}
    (H : IsPullback φ q (toSpec W) f) (s : ((originLB W).pull φ).Sec) {T : Scheme.{0}} (t : T ⟶ Y)
    (j : ((originLB W).pull φ).ι) (h : ⊤ ≤ t ⁻¹ᵁ ((originLB W).pull φ).U j)
    (e : t ≫ φ = t ≫ φ ≫ toSpec W ≫ zero W) :
    (t.appLE (((originLB W).pull φ).U j) ⊤ h).hom (s.f j) = 0 := by
  obtain ⟨c, hc, -⟩ := existsUnique_eq_appLE_mul_secPull W H s
  have h' : ⊤ ≤ (t ≫ φ) ⁻¹ᵁ (originLB W).U (j ⟨⟩) :=
    fun p hp => (Cartier.pull_U (originLB W) φ j).le (h hp)
  have h0 := (appLE_originSec_eq_zero_iff W (t ≫ φ) (j ⟨⟩) h').2 (e.trans (Category.assoc _ _ _).symm)
  have h1 : (t.appLE (((originLB W).pull φ).U j) ⊤ h).hom
      ((Cartier.secPull (originSec W) φ).f j) = 0 := by
    refine Eq.trans ?_ h0
    have := Scheme.Hom.appLE_comp_appLE t φ ((originLB W).U (j ⟨⟩)) _ ⊤
      (Cartier.pull_U (originLB W) φ j).le h
    exact congrArg (fun g => g.hom ((originSec W).f (j ⟨⟩))) this
  rw [hc j, map_mul, h1, mul_zero]

theorem originLB_polarisation (R : Type) [CommRing R] (W : WeierstrassCurve R) [GrpObj (schemeOver W)]
    (_hc : IsCommMonObj (schemeOver W)) (he : η[schemeOver W].left = zero W) :
    Out.Rigidified (schemeOver W) (originLB W) ∧ Out.Sym (schemeOver W) (originLB W) ∧
      Out.RelAmple (schemeOver W) (originLB W) ∧ Out.KTriv (schemeOver W) (originLB W) := by
  have he' : eSec (schemeOver W) = zero W := he
  have hz : ∀ (T : Scheme.{0}) (t : T ⟶ (schemeOver W).left) (i : (originLB W).ι)
      (h : ⊤ ≤ t ⁻¹ᵁ (originLB W).U i),
      (t.appLE ((originLB W).U i) ⊤ h).hom ((originSec W).f i) = 0 ↔
        t = t ≫ (schemeOver W).hom ≫ eSec (schemeOver W) := fun T t i h => by
    rw [he']
    exact appLE_originSec_eq_zero_iff W t i h
  refine ⟨?_, ?_, relAmple_originLB W, ?_⟩
  · unfold Out.Rigidified
    rw [he']
    exact ⟨_, isGen_one_pull_zero W⟩
  · exact GlobalTheory.T.symmetric_lineBundle_of_regular_section _ (schemeOver W) (originLB W) (originSec W) (originLB_isLB W)
      (fun i V h => ((isRegularSec_originSec W i).resG h).mem) hz
  · refine GlobalTheory.T.kernelPolarisation_trivial_of_sections_vanish_zero _ (schemeOver W) (originLB W) (originSec W) (originLB_isLB W) hz ?_
    intro R' _ f Y φ q H s T t j h e
    rw [he'] at e
    exact appLE_sec_pull_originLB_eq_zero W H s t j h e

end GlobalTheory.WeierstrassCurve
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.OriginLineBundlePolarisationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.originLineBundle_polarisation : ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R) [GrpObj (schemeOver W)], IsCommMonObj (schemeOver W) → η[schemeOver W].left = zero W → Out.Rigidified (schemeOver W) (originLB W) ∧ Out.Sym (schemeOver W) (originLB W) ∧ Out.RelAmple (schemeOver W) (originLB W) ∧ Out.KTriv (schemeOver W) (originLB W) := by
  first | exact @GlobalTheory.WeierstrassCurve.originLB_polarisation | exact GlobalTheory.WeierstrassCurve.originLB_polarisation | (intros; apply GlobalTheory.WeierstrassCurve.originLB_polarisation <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MultiplierIffExistsHom
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory.EllipticHom

theorem exists_coord {g : ℕ} (hg : g = 1) {w : Fin g → ℂ} (hw : w ≠ 0) :
    ∃ c : (Fin g → ℂ) →ₗ[ℂ] ℂ, (∀ x, c x • w = x) ∧ c w = 1 := by
  subst hg
  have hw0 : w 0 ≠ 0 := fun h => hw (funext fun i => by rw [Subsingleton.elim i 0, h]; rfl)
  refine ⟨(w 0)⁻¹ • LinearMap.proj 0, fun x => ?_, by simp [hw0]⟩
  funext i
  rw [Subsingleton.elim i 0]
  simp only [LinearMap.smul_apply, LinearMap.proj_apply, Pi.smul_apply, smul_eq_mul]
  field_simp

theorem exists_index {L L' : PeriodPair} {α : ℂ} (h : ∀ z ∈ L.lattice, α * z ∈ L'.lattice) :
    ∃ n : ℕ, Complex.normSq α * |(L.ω₁ * starRingEnd ℂ L.ω₂).im| = n * |(L'.ω₁ * starRingEnd ℂ L'.ω₂).im| := by
  obtain ⟨p, q, h1⟩ := PeriodPair.mem_lattice.1 (h _ L.ω₁_mem_lattice)
  obtain ⟨r, s, h2⟩ := PeriodPair.mem_lattice.1 (h _ L.ω₂_mem_lattice)
  refine ⟨(p * s - q * r).natAbs, ?_⟩
  have e : Complex.normSq α * (L.ω₁ * starRingEnd ℂ L.ω₂).im =
      ((p * s - q * r : ℤ) : ℝ) * (L'.ω₁ * starRingEnd ℂ L'.ω₂).im := by
    have e1 : Complex.normSq α * (L.ω₁ * starRingEnd ℂ L.ω₂).im = ((α * L.ω₁) * starRingEnd ℂ (α * L.ω₂)).im := by
      simp [Complex.normSq_apply]
      ring
    rw [e1, ← h1, ← h2]
    simp
    ring
  rw [Nat.cast_natAbs, Int.cast_abs, ← abs_mul, ← e, abs_mul, abs_of_nonneg (Complex.normSq_nonneg α)]

theorem covolume_ne_zero (L : PeriodPair) : (L.ω₁ * starRingEnd ℂ L.ω₂).im ≠ 0 := by
  intro h
  have hi := LinearIndependent.pair_iff.1 L.indep
  simp at h
  have h1 := hi L.ω₂.re (-L.ω₁.re) (by
    apply Complex.ext <;> simp <;> linarith)
  have h2 := hi L.ω₂.im (-L.ω₁.im) (by
    apply Complex.ext <;> simp <;> linarith)
  have h3 := hi 0 1 (by
    apply Complex.ext <;> simp [h1.1, h2.1])
  exact one_ne_zero h3.2

theorem multiplier_iff_exists_hom : ThetaUnifAV → Out.PolBaseChangeSt → ∀ (R : Type) [CommRing R] (P Q : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A) (t : epsR R ⟶ Q.A) (s : R →+* ℂ) (L L' : PeriodPair) (α : ℂ), P.g = 1 → Q.g = 1 → IsTangent v → IsTangent t → (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s P P' φ' → IsVecOver s φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ L.lattice ↔ z • w' ∈ u'.Λ) → (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ Q.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s Q P' φ' → IsVecOver s φ' t v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ L'.lattice ↔ z • w' ∈ u'.Λ) → ((∀ z ∈ L.lattice, α * z ∈ L'.lattice) ↔ (∀ (P₁ Q₁ : Out.PolAV (Sp ℂ)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ Q.A.left) (v₁ : epsR ℂ ⟶ P₁.A) (t₁ : epsR ℂ ⟶ Q₁.A), IsPolFibre s P P₁ φ₁ → IsPolFibre s Q Q₁ ψ₁ → IsVecOver s φ₁ v v₁ → IsVecOver s ψ₁ t t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![α] ![t₁] (v₁ ≫ f₁))) := by
  intro hU hB R _ P Q v t s L L' α hP hQ hv ht hL hL'
  constructor
  · intro hα P₁ Q₁ φ₁ ψ₁ v₁ t₁ hφ hψ hv₁ ht₁
    obtain ⟨rig, hrig⟩ := P₁.rigid
    obtain ⟨rig', hrig'⟩ := Q₁.rigid
    obtain ⟨u, Hm, χ, Ef, hA, -, hd, -, -, hθ, hE, hEb, -⟩ := hU P₁ rig hrig
    obtain ⟨u', Hm', χ', Ef', hA', -, hd', he', -, hθ', hE', hEb', -⟩ := hU Q₁ rig' hrig'
    have tv := hv₁.isTangent hφ.2.1 hv
    have tt := ht₁.isTangent hψ.2.1 ht
    obtain ⟨w, hw, -⟩ := hd v₁ tv
    obtain ⟨w', hw', -⟩ := hd' t₁ tt
    obtain ⟨w0, hΛ⟩ := hL P₁ φ₁ v₁ u w hφ hv₁ hw
    obtain ⟨w0', hΛ'⟩ := hL' Q₁ ψ₁ t₁ u' w' hψ ht₁ hw'
    have g1 : P₁.g = 1 := hφ.1.trans hP
    have g2 : Q₁.g = 1 := hψ.1.trans hQ
    have hH := hermForm_principal_dim_one _ u.Λ w L Hm Ef g1 w0 hΛ hA.1 (hA.2.1 w w0) hE hEb
    have hH' := hermForm_principal_dim_one _ u'.Λ w' L' Hm' Ef' g2 w0' hΛ' hA'.1 (hA'.2.1 w' w0') hE' hEb'
    obtain ⟨c, hc, hc1⟩ := exists_coord g1 w0
    obtain ⟨n, hn⟩ := exists_index hα
    let F : (Fin P₁.g → ℂ) →ₗ[ℂ] (Fin Q₁.g → ℂ) := (α • c).smulRight w'
    have hF : ∀ x, F x = (α * c x) • w' := fun x => rfl
    obtain ⟨f, hf, hFf⟩ := exists_hom_of_linear_scaling_hermForm P₁ Q₁ u u' Hm χ Hm' χ' hA hA'
      (fun k => (hθ k).2) (fun k => (hθ' k).1) F n
      (fun l hl => by
        rw [hF, ← hΛ']
        exact hα _ ((hΛ _).2 (by rwa [hc])))
      (fun x y => by
        have e := hH (c x) (c y)
        rw [hc, hc] at e
        have a1 : ((|(L.ω₁ * starRingEnd ℂ L.ω₂).im| : ℝ) : ℂ) ≠ 0 := by
          exact_mod_cast abs_ne_zero.2 (covolume_ne_zero L)
        have a2 : ((|(L'.ω₁ * starRingEnd ℂ L'.ω₂).im| : ℝ) : ℂ) ≠ 0 := by
          exact_mod_cast abs_ne_zero.2 (covolume_ne_zero L')
        have hn' := congrArg (fun r : ℝ => (r : ℂ)) hn
        simp only [Complex.ofReal_mul, Complex.ofReal_natCast, ← Complex.mul_conj] at hn'
        rw [hF, hF, hH', e, map_mul, ← mul_div_assoc, div_eq_div_iff a2 a1]
        linear_combination (c x * starRingEnd ℂ (c y)) * hn')
    refine ⟨f, hf, ?_⟩
    have h1 := HomLinear.isDiff_comp u u' f F hFf tv hw
    rw [hF, hc1, _root_.mul_one] at h1
    have hx := (LieMultiple.isLieComb_one_iff_comp α t₁ _).2 rfl
    have hxt : IsTangent (Chart.spMap (Chart.scaleD α) ≫ t₁) :=
      (Chart.isTan_iff _).1 (Chart.isTan_scale α ((Chart.isTan_iff _).2 tt))
    have := (he' (α • w')).unique ⟨HomLinear.isTangent_comp f tv, h1⟩
      ⟨hxt, CMNormIdentity.isDiff_of_isLieComb u' hw' α hx⟩
    rw [this]
    exact hx
  · intro h z hz
    obtain ⟨P₁, φ₁, hφ⟩ := exists_isPolFibre hB s P
    obtain ⟨Q₁, ψ₁, hψ⟩ := exists_isPolFibre hB s Q
    obtain ⟨v₁, hv₁, -⟩ := existsUnique_isVecOver hφ.2.1.1 v
    obtain ⟨t₁, ht₁, -⟩ := existsUnique_isVecOver hψ.2.1.1 t
    obtain ⟨f, hf, hl⟩ := h P₁ Q₁ φ₁ ψ₁ v₁ t₁ hφ hψ hv₁ ht₁
    obtain ⟨rig, hrig⟩ := P₁.rigid
    obtain ⟨rig', hrig'⟩ := Q₁.rigid
    obtain ⟨u, -, -, -, -, -, hd, -⟩ := hU P₁ rig hrig
    obtain ⟨u', -, -, -, -, -, hd', he', -⟩ := hU Q₁ rig' hrig'
    have tv := hv₁.isTangent hφ.2.1 hv
    have tt := ht₁.isTangent hψ.2.1 ht
    obtain ⟨w, hw, -⟩ := hd v₁ tv
    obtain ⟨w', hw', -⟩ := hd' t₁ tt
    obtain ⟨-, hΛ⟩ := hL P₁ φ₁ v₁ u w hφ hv₁ hw
    obtain ⟨-, hΛ'⟩ := hL' Q₁ ψ₁ t₁ u' w' hψ ht₁ hw'
    obtain ⟨F, -, hF, hT, -⟩ := HomLinear.exists_linear_of_isMonHom P₁.A Q₁.A P₁.isAb Q₁.isAb P₁.L Q₁.L _ _ u u'
      hd' he' f hf
    obtain ⟨tf, df⟩ := hT w v₁ tv hw
    have e : F w = α • w' := (hd' _ tf).unique df (CMNormIdentity.isDiff_of_isLieComb u' hw' α hl)
    have := hF _ ((hΛ z).1 hz)
    rw [map_smul, e, smul_smul, _root_.mul_comm] at this
    exact (hΛ' _).2 this

end GlobalTheory.EllipticHom
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTorsionGeneratorsRational
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

namespace GlobalTheory.TorsionGenerators

variable {R : Type} [CommRing R]

theorem exists_fibre (hL : Out.Laws) (P : Out.PolAV (Sp R)) [IsCommMonObj P.A] {k : Type} [CommRing k] (t : R →+* k) :
    ∃ (P' : Out.PolAV (Sp k)) (φ : P'.A.left ⟶ P.A.left)
      (β : (𝟙_ (Over (Sp k)) ⟶ P'.A) ≃* (Over.mk (spMap t) ⟶ P.A)), IsPolFibre t P P' φ ∧
      (∀ x, (β x).left = x.left ≫ φ) ∧ ∀ (n : ℤ) x y (c : Γ(Sp k, ⊤)ˣ),
        Out.WeilIs P'.A P'.L n x y c → Out.WeilIs P.A P.L n (β x) (β y) c := by
  obtain ⟨P', φ, h⟩ := exists_isPolFibre hL.polBaseChange t P
  obtain ⟨β, hβ⟩ := UnifPoint.exists_pointEquiv h.2.1
  refine ⟨P', φ, β, h, hβ, fun n x y c H => ?_⟩
  have H' := (weilIs_grpPullback_of_comm _ _ P.A P'.A _ φ P.L P'.L P.isLB P'.isLB h.2.1 (LBIso.symm h.2.2) _ n x y
    (pushPt h.2.1.1.w x) (pushPt h.2.1.1.w y) c rfl rfl).1 H
  exact UnifPoint.weilIs_congr (Category.id_comp _) (hβ x).symm (hβ y).symm H'

theorem exists_weilIs (hL : Out.Laws) (P : Out.PolAV (Sp R)) [IsCommMonObj P.A] {k : Type} [Field k]
    (t : R →+* k) {n : ℕ} {x y : Over.mk (spMap t) ⟶ P.A} (hx : x ^ n = 1) (hy : y ^ n = 1) :
    ∃ u : kˣ, Out.WeilIs P.A P.L n x y (unitOn u) := by
  obtain ⟨P', φ, β, h, -, H⟩ := exists_fibre hL P t
  obtain ⟨x, rfl⟩ := β.surjective x
  obtain ⟨y, rfl⟩ := β.surjective y
  rw [← map_pow, MulEquiv.map_eq_one_iff] at hx hy
  obtain ⟨c, hc, -⟩ := (hL.weil _ P' n _).1 x y hx hy
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.toMonoidHom c, ?_⟩
  have e : unitOn (Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.toMonoidHom c) = c :=
    Units.ext (CommRingCat.inv_hom_apply (Scheme.ΓSpecIso (CommRingCat.of k)) c.val)
  rw [e]
  exact H n x y c hc

theorem unitOn_injective {k : Type} [CommRing k] : Function.Injective (unitOn (R := k)) := fun a b h =>
  Units.ext ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).1 (congrArg Units.val h))

section Ext

variable {K k : Type} [Field K] [Field k] {t : R →+* K} {t' : R →+* k} {β : K →+* k}

def extPt (e : β.comp t = t') : Over.mk (spMap t') ⟶ Over.mk (spMap t) :=
  Over.homMk (spMap β) ((spMap_comp_spMap _ _).trans (congrArg spMap e))

theorem extPt_injective (e : β.comp t = t') {A : Over (Sp R)} {x y : Over.mk (spMap t) ⟶ A}
    (h : extPt e ≫ x = extPt e ≫ y) : x = y := by
  have : Epi (extPt e).left := TorsionSeparable.epi_specMap β
  have : Epi (extPt e) := Over.epi_of_epi_left _
  exact (cancel_epi _).1 h

theorem weilIs_extPt (hL : Out.Laws) (P : Out.PolAV (Sp R)) (e : β.comp t = t') {n : ℤ}
    {x y : Over.mk (spMap t) ⟶ P.A} {u : Kˣ} (H : Out.WeilIs P.A P.L n x y (unitOn u)) :
    Out.WeilIs P.A P.L n (extPt e ≫ x) (extPt e ≫ y) (unitOn (Units.map β.toMonoidHom u)) := by
  have H' := CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB (extPt e) H
  have e' : Units.map (extPt e).left.appTop.hom.toMonoidHom (unitOn u) = unitOn (Units.map β.toMonoidHom u) :=
    Units.ext (congrArg (fun q => q.hom u.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm
  rwa [e'] at H'

end Ext

section System

variable {O : Type} [CommRing O] (P : Out.PolAV (Sp R)) (a : OAct O P.A) (tr : O → ℤ)

variable {P a tr} {K k : Type} [Field K] [Field k] {t : R →+* K} {t' : R →+* k} {β : K →+* k}

theorem extPt_eq_one_iff (e : β.comp t = t') {x : Over.mk (spMap t) ⟶ P.A} : extPt e ≫ x = 1 ↔ x = 1 :=
  ⟨fun h => extPt_injective e (h.trans (comp_one _).symm), fun h => by rw [h, comp_one]⟩

theorem unitsMap_injective (β : K →+* k) : Function.Injective (Units.map β.toMonoidHom) :=
  Units.map_injective β.injective

end System

theorem exists_finite_coordinates {Ω : Type} [Field Ω] {X : Scheme.{0}} (p : X ⟶ Sp R) [LocallyOfFiniteType p]
    (t : R →+* Ω) (x : Sp Ω ⟶ X) (hx : x ≫ p = spMap t) :
    ∃ s : Set Ω, s.Finite ∧ ∀ (B : Type) [CommRing B] (io : B →+* Ω), Function.Injective io → (∀ c, t c ∈ io.range) →
      (∀ y ∈ s, y ∈ io.range) → ∃ b : Sp B ⟶ X, spMap io ≫ b = x := by
  obtain ⟨A, i, _, q, ht⟩ : ∃ (A : CommRingCat.{0}) (i : Spec A ⟶ X) (_ : IsOpenImmersion i)
      (t : Spec A), i t = x (IsLocalRing.closedPoint Ω) := by
    obtain ⟨n, t, ht⟩ := X.affineCover.exists_eq (x (IsLocalRing.closedPoint Ω))
    exact ⟨_, X.affineCover.f n, X.affineCover.map_prop n, t, ht⟩
  have hr : Set.range x ⊆ Set.range i := by
    rintro _ ⟨u, rfl⟩
    exact ⟨q, ht.trans (congrArg x (Subsingleton.elim _ _))⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift i x hr)
  have hφa : Spec.map φ ≫ i = x := by rw [hφ, IsOpenImmersion.lift_fac]
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (i ≫ p)
  have h₂ : LocallyOfFiniteType (Spec.map ψ) := by rw [hψ]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h₂
  have hc : ψ ≫ φ = CommRingCat.ofHom t := by
    rw [← Spec.map_inj, Spec.map_comp, hψ, ← Category.assoc, hφa, hx]
  let : Algebra R A := ψ.hom.toAlgebra
  have : Algebra.FiniteType R A := h₂
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := A)
  refine ⟨φ.hom '' (s : Set A), s.finite_toSet.image _, fun B _ io hio h1 h2 => ?_⟩
  have hmem : ∀ y, φ.hom y ∈ io.range := by
    intro y
    have hy : y ∈ Algebra.adjoin R (s : Set A) := by simp [hs]
    induction hy using Algebra.adjoin_induction with
    | mem y hy => exact h2 _ ⟨y, hy, rfl⟩
    | algebraMap c => exact (congr($hc c) : φ.hom (algebraMap R A c) = t c) ▸ h1 c
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz
  let e : B ≃+* io.range := RingEquiv.ofBijective io.rangeRestrict
    ⟨fun a b h => hio (congrArg Subtype.val h), io.rangeRestrict_surjective⟩
  refine ⟨Spec.map (CommRingCat.ofHom (e.symm.toRingHom.comp (φ.hom.codRestrict io.range hmem))) ≫ i, ?_⟩
  rw [← hφa, ← Spec.map_comp_assoc]
  congr 2
  ext y
  exact congrArg Subtype.val (e.apply_symm_apply ⟨φ.hom y, hmem y⟩)

end GlobalTheory.TorsionGenerators

namespace GlobalTheory

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DetCondTensorDefinite
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

namespace GlobalTheory.TensorDet

section Algebra

noncomputable def rightAction (k O O' M : Type) [CommRing k] [CommRing O] [CommRing O'] [Algebra O k] [Algebra O O']
    [AddCommGroup M] [Module O M] [Module O' M] [IsScalarTower O O' M] : O' →+* Module.End k (k ⊗[O] M) :=
  (Module.End.baseChangeHom O k M).toRingHom.comp (Algebra.lsmul O O M : O' →ₐ[O] Module.End O M).toRingHom

variable {k O O' M : Type} [CommRing k] [CommRing O] [CommRing O'] [Algebra O k] [Algebra O O']
    [AddCommGroup M] [Module O M] [Module O' M] [IsScalarTower O O' M]

theorem rightAction_apply (a : O') :
    rightAction k O O' M a = LinearMap.baseChange k (Algebra.lsmul O O M a : M →ₗ[O] M) := rfl

theorem rightAction_tmul (a : O') (c : k) (m : M) : rightAction k O O' M a (c ⊗ₜ m) = c ⊗ₜ (a • m) := rfl

theorem nonempty_eigenSub_equiv [Algebra O' k] [IsScalarTower O O' k] {I : Type} {σ : I → O' →+* k}
    (h : EigenSplit.IsSplitting σ) (i : I) (hi : σ i = algebraMap O' k) :
    Nonempty (EigenSplit.eigenSub (rightAction k O O' M) (σ i) ≃ₗ[k] k ⊗[O'] M) := by
  classical
  let ρ := rightAction k O O' M
  let π : k ⊗[O] M →ₗ[k] k ⊗[O'] M := ((TensorProduct.mk O' k M 1).restrictScalars O).liftBaseChange k
  have hπ : ∀ m, π (1 ⊗ₜ m) = 1 ⊗ₜ m := fun m => by simp [π]
  let ρ' : O' →+* Module.End k (k ⊗[O'] M) := (algebraMap k _).comp (σ i)
  have he : EigenSplit.IsEquivariant ρ ρ' π := fun a x => by
    have : π ∘ₗ ρ a = ρ' a ∘ₗ π := by
      ext m
      simp only [TensorProduct.AlgebraTensorModule.curry_apply,
        TensorProduct.curry_apply, LinearMap.comp_apply, LinearMap.coe_restrictScalars, ρ, rightAction_tmul, hπ]
      simp [ρ', hi]
    exact congr($this x)
  let g : M →ₗ[O'] k ⊗[O] M :=
    { toFun := fun m => EigenSplit.proj h ρ i (1 ⊗ₜ m)
      map_add' := fun m n => by rw [TensorProduct.tmul_add, map_add (f := _)]
      map_smul' := fun a m => by
        rw [← rightAction_tmul, ← (EigenSplit.isEquivariant_action ρ a).proj h,
          EigenSplit.mem_eigenSub.1 (EigenSplit.proj_mem h ρ i _), hi, algebraMap_smul]
        rfl }
  let s : k ⊗[O'] M →ₗ[k] k ⊗[O] M := g.liftBaseChange k
  have h1 : s ∘ₗ π = EigenSplit.proj h ρ i := by
    ext m
    simp [hπ, s, g]
  have h2 : ∀ x, π (EigenSplit.proj h ρ i x) = π x := fun x => by
    rw [he.proj h]
    exact EigenSplit.proj_of_mem h (EigenSplit.mem_eigenSub.2 fun a => rfl)
  have h3 : π ∘ₗ s = LinearMap.id := by
    ext m
    simp [s, g, h2, hπ]
  refine ⟨LinearEquiv.ofBijective (π ∘ₗ Submodule.subtype _) ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_,
    fun y => ⟨EigenSplit.projTo h ρ i (s y), (h2 _).trans congr($h3 y)⟩⟩⟩
  refine Subtype.ext ((EigenSplit.proj_of_mem h x.2).symm.trans ?_)
  rw [← h1]
  exact (congrArg s hx).trans (map_zero s)

end Algebra

theorem injective_of_charZero {E k : Type} [Field E] [NumberField E] [Field k] [CharZero k] (τ : 𝓞 E →+* k) :
    Function.Injective τ := by
  rw [RingHom.injective_iff_ker_eq_bot, ← Ideal.absNorm_eq_zero_iff]
  simpa using RingHom.mem_ker.1 (Ideal.absNorm_mem (RingHom.ker τ))

theorem finrank_eigenSub {E k O M : Type} [Field E] [NumberField E] [Field k] [IsAlgClosed k] [CharZero k]
    [CommRing O] [Algebra O k] [Algebra O (𝓞 E)] [AddCommGroup M] [Module O M] [Module (𝓞 E) M]
    [IsScalarTower O (𝓞 E) M] (τ : 𝓞 E →+* k) (hτ : τ.comp (algebraMap O (𝓞 E)) = algebraMap O k) :
    Module.finrank k (EigenSplit.eigenSub (rightAction k O (𝓞 E) M) τ) = Module.finrank (𝓞 E) M := by
  have hs : EigenSplit.IsSplitting fun φ : E →+* k => φ.comp (algebraMap (𝓞 E) E) := by
    classical
    obtain ⟨b⟩ := EigenSplit.nonempty_basis (E := E) (NumberField.Embeddings.card E k)
    exact EigenSplit.isSplitting_of_isUnit_discr b (EigenSplit.det_sq_eq_discr_of_field Function.injective_id b)
      (by simpa using NumberField.discr_ne_zero E)
  have hi := injective_of_charZero τ
  let _ := τ.toAlgebra
  have : IsScalarTower O (𝓞 E) k := IsScalarTower.of_algebraMap_eq' hτ.symm
  have : FaithfulSMul (𝓞 E) k := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
  have e : (IsFractionRing.lift hi : E →+* k).comp (algebraMap (𝓞 E) E) = τ :=
    RingHom.ext fun a => IsFractionRing.lift_algebraMap hi a
  obtain ⟨f⟩ := nonempty_eigenSub_equiv (O := O) (M := M) hs (IsFractionRing.lift hi) e
  rw [← (TensorProduct.isBaseChange (𝓞 E) M k).finrank_eq, ← f.finrank_eq, e]

theorem lieMult_of_param {k O V : Type} [Field k] [CommRing O] [AddCommGroup V] [Module k V] [Module.Finite k V]
    {A : Over (Sp k)} [GrpObj A] (act : OAct O A) (ρ : O →+* Module.End k V) (Φ : V → (epsR k ⟶ A))
    (inj : Function.Injective Φ) (tan : ∀ x, IsTangent x ↔ x ∈ Set.range Φ) (add : ∀ y z, Φ (y + z) = Φ y * Φ z)
    (smul : ∀ (c : k) y, IsLieComb ![c] ![Φ y] (Φ (c • y))) (eqv : ∀ a y, Φ (ρ a y) = Φ y ≫ act.act a)
    (τ : O →+* k) {n : ℕ} (hn : Module.finrank k (EigenSplit.eigenSub ρ τ) = n) :
    LieMult act (𝟙 (Sp k)) τ n := by
  have sm : ∀ (c : k) y x, x.left = spMap (epsScaleR c) ≫ (Φ y).left ↔ x = Φ (c • y) := fun c y x => by
    rw [← (LieMultiple.isLieComb_one_iff _ _ _).1 (smul c y)]
    exact ⟨fun h => Over.OverMorphism.ext h, fun h => by rw [h]⟩
  let F : Multiplicative V →* (epsR k ⟶ A) := MonoidHom.mk' (fun y => Φ y.toAdd) (fun y z => add _ _)
  have pr : ∀ (n : ℕ) (y : Fin n → V), (List.ofFn fun i => Φ (y i)).prod = Φ (∑ i, y i) := fun n y => by
    have := map_list_prod F (List.ofFn fun i => Multiplicative.ofAdd (y i))
    rw [List.map_ofFn, List.prod_ofFn, ← ofAdd_sum] at this
    exact this.symm
  let B := Module.finBasisOfFinrankEq k _ hn
  let j : epsPt (𝟙 (Sp k)) ≅ epsR k := Over.isoMk (Iso.refl _) (by simp)
  let e : (epsPt (𝟙 (Sp k)) ⟶ A) ≃* (epsR k ⟶ A) :=
    MulEquiv.ofBijective (preHom j.inv) (j.symm.homCongr (Iso.refl A)).symm.bijective
  have he : ∀ w, (e w).left = w.left := fun w => Category.id_comp _
  have he' : ∀ w, (e.symm w).left = w.left := fun w => by rw [← he, e.apply_symm_apply]
  have one : (1 : Over.mk (𝟙 (Sp k)) ⟶ A).left = η[A].left := Category.id_comp _
  have mem : ∀ y, y ∈ EigenSplit.eigenSub ρ τ ↔
      ∀ a, (Φ y ≫ act.act a).left = spMap (epsScaleR (τ a)) ≫ (Φ y).left := fun y => by
    rw [EigenSplit.mem_eigenSub]
    exact forall_congr' fun a => by rw [sm, ← eqv, inj.eq_iff]
  refine LiePull.basis_transport e.symm (Q := IsLieEigen act (𝟙 _) τ)
    (R' := fun c u v => u.left = spMap (epsScale c) ≫ v.left)
    (R := fun c u v => u.left = spMap (epsScaleR c) ≫ v.left)
    (P := fun w => IsTangent w ∧ ∀ a, (w ≫ act.act a).left = spMap (epsScaleR (τ a)) ≫ w.left)
    (fun w => and_congr (by rw [IsTangent, he', one]) (forall_congr' fun a => by
      rw [Over.comp_left, Over.comp_left, he']
      rfl))
    (fun c u v => by rw [he', he']; rfl) n
    ⟨fun i => Φ (B i), fun i => ⟨(tan _).2 ⟨_, rfl⟩, (mem _).1 (B i).2⟩, ?_⟩
  rintro w ⟨hw, hw'⟩
  obtain ⟨y, rfl⟩ := (tan w).1 hw
  let y' : EigenSplit.eigenSub ρ τ := ⟨y, (mem y).2 hw'⟩
  refine (existsUnique_congr fun d => ?_).1 (existsUnique_eq' (a' := B.equivFun y'))
  have e₁ : B.equivFun y' = d ↔ y = ∑ i, d i • (B i : V) := by
    rw [← LinearEquiv.eq_symm_apply, Module.Basis.equivFun_symm_apply, Subtype.ext_iff]
    simp [y']
  rw [e₁, ← inj.eq_iff, ← pr]
  constructor
  · exact fun h => ⟨_, fun i => (sm _ _ _).2 rfl, h⟩
  · rintro ⟨u, hu, h⟩
    rw [h, show u = fun i => Φ (d i • (B i : V)) from funext fun i => (sm _ _ _).1 (hu i)]

end GlobalTheory.TensorDet
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HomDerivDescendsToNumberField
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory

namespace HomDerivDescent

variable {R R' : Type} [CommRing R] [CommRing R']

theorem isLieComb_one_iff {G : Over (Sp R)} [GrpObj G] (a : R) (t w : epsR R ⟶ G) :
    IsLieComb ![a] ![t] w ↔ w.left = spMap (epsScaleR a) ≫ t.left := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa using hu 0
  · intro h
    refine ⟨![w], fun i => ?_, by simp⟩
    fin_cases i
    exact h

theorem epsScaleR_comp_dualMapR (g : R →+* R') (a : R) :
    (epsScaleR (g a)).comp (Chart.dualMapR g) = (Chart.dualMapR g).comp (epsScaleR a) := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [Chart.dualMapR, epsScaleR, mul_comm]

theorem isLieComb_pull {g : R →+* R'} {G H : Over (Sp R)} {G' H' : Over (Sp R')} [GrpObj H] [GrpObj H']
    {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (hψ : IsPullback ψ H'.hom H.hom (spMap g))
    {v : epsR R ⟶ G} {t : epsR R ⟶ H} {v' : epsR R' ⟶ G'} {t' : epsR R' ⟶ H'}
    (hv : IsVecOver g φ v v') (ht : IsVecOver g ψ t t') {f : G ⟶ H} {f' : G' ⟶ H'}
    (hf : f'.left ≫ ψ = φ ≫ f.left) {a : R} (h : IsLieComb ![a] ![t] (v ≫ f)) :
    IsLieComb ![g a] ![t'] (v' ≫ f') := by
  rw [isLieComb_one_iff] at h ⊢
  unfold IsVecOver at hv ht
  refine hψ.hom_ext ?_ ?_
  · rw [Over.comp_left] at h ⊢
    rw [Category.assoc, hf, ← Category.assoc, hv, Category.assoc, h, Category.assoc, ht, ← Category.assoc,
      ← Category.assoc]
    congr 1
    exact (spMap_comp_spMap _ _).trans
      ((congrArg spMap (epsScaleR_comp_dualMapR g a).symm).trans (spMap_comp_spMap _ _).symm)
  · rw [Over.w, Category.assoc, Over.w]
    refine Eq.trans ?_ (spMap_comp_spMap _ _).symm
    change spMap _ = _
    congr 1
    ext x <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]

theorem exists_descent (hT : ThetaUnifAV) (hB : Out.PolBaseChangeSt) (k : IntermediateField ℚ ℂ)
    [FiniteDimensional ℚ k] (P Q : Out.PolAV (Sp k)) {Pc Qc : Out.PolAV (Sp ℂ)} {φc : Pc.A.left ⟶ P.A.left}
    {ψc : Qc.A.left ⟶ Q.A.left} (hP : IsPolFibre (algebraMap k ℂ) P Pc φc) (hQ : IsPolFibre (algebraMap k ℂ) Q Qc ψc)
    (fc : Pc.A ⟶ Qc.A) [IsMonHom fc] :
    ∃ (K : IntermediateField k ℂ) (P₁ Q₁ : Out.PolAV (Sp K)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ Q.A.left)
      (m : Pc.A.left ⟶ P₁.A.left) (n : Qc.A.left ⟶ Q₁.A.left) (f₁ : P₁.A ⟶ Q₁.A), FiniteDimensional k K ∧
      IsPolFibre (algebraMap k K) P P₁ φ₁ ∧ IsPolFibre (algebraMap k K) Q Q₁ ψ₁ ∧
      IsPolFibre (algebraMap K ℂ) P₁ Pc m ∧ IsPolFibre (algebraMap K ℂ) Q₁ Qc n ∧ m ≫ φ₁ = φc ∧ n ≫ ψ₁ = ψc ∧
      IsMonHom f₁ ∧ fc.left ≫ n = m ≫ f₁.left := by
  obtain ⟨e, he, he'⟩ := grpPullback_iso hP.2.1 (isGrpPullback_pullback P.A _)
  obtain ⟨d, hd, hd'⟩ := grpPullback_iso hQ.2.1 (isGrpPullback_pullback Q.A _)
  obtain ⟨K, f, j, hK, hf, j₁, j₂, j₃⟩ := hom_descends_to_numberField hT hB k P Q (e.inv ≫ fc ≫ d.hom) inferInstance
  obtain ⟨P₁, φ₁, hP₁⟩ := exists_isPolFibre hB (algebraMap k K) P
  obtain ⟨Q₁, ψ₁, hQ₁⟩ := exists_isPolFibre hB (algebraMap k K) Q
  obtain ⟨m, hm, hm'⟩ := PolFibre.cancel (g := algebraMap K ℂ) hP₁ hP
  obtain ⟨n, hn, hn'⟩ := PolFibre.cancel (g := algebraMap K ℂ) hQ₁ hQ
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso hP₁.2.1 (isGrpPullback_pullback P.A _)
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso (isGrpPullback_pullback Q.A _) hQ₁.2.1
  refine ⟨K, P₁, Q₁, φ₁, ψ₁, m, n, a.hom ≫ f ≫ b.hom, hK, hP₁, hQ₁, hm, hn, hm', hn', inferInstance, ?_⟩
  have key : m ≫ a.hom.left = e.hom.left ≫ j := by
    apply pullback.hom_ext
    · exact ((Category.assoc _ _ _).trans ((congrArg (m ≫ ·) ha').trans hm')).trans
        ((Category.assoc _ _ _).trans ((congrArg (e.hom.left ≫ ·) j₁).trans he')).symm
    · exact ((Category.assoc _ _ _).trans ((congrArg (m ≫ ·) (Over.w a.hom)).trans hm.2.1.1.w)).trans
        ((Category.assoc _ _ _).trans ((congrArg (e.hom.left ≫ ·) j₂).trans ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ _) (Over.w e.hom))))).symm
  refine hQ₁.2.1.1.hom_ext ?_ ?_
  · have r : e.hom.left ≫ (e.inv ≫ fc ≫ d.hom).left = fc.left ≫ d.hom.left := by
      rw [← Over.comp_left, e.hom_inv_id_assoc, Over.comp_left]
    rw [Category.assoc, hn', Over.comp_left, Over.comp_left]
    simp only [Category.assoc]
    rw [hb', ← Category.assoc, key, Category.assoc, ← hd', ← Category.assoc, ← r, Category.assoc]
    exact congrArg (e.hom.left ≫ ·) j₃.symm
  · rw [Category.assoc, Category.assoc, Over.w, hn.2.1.1.w, hm.2.1.1.w, ← Category.assoc, Over.w]

end HomDerivDescent

open HomDerivDescent in
theorem hom_deriv_descends_to_numberField : ThetaUnifAV → Out.PolBaseChangeSt → ∀ (R : Type) [CommRing R] (P Q : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A) (t : epsR R ⟶ Q.A) (k : IntermediateField ℚ ℂ) (ρ : R →+* k) (α : ℂ), FiniteDimensional ℚ k → IsTangent v → (∀ (R' : Type) [CommRing R'] (f' : R →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ Q.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' Q P' φ' → IsVecOver f' φ' t v' → IsLieBasis ![v']) → (∀ (P₁ Q₁ : Out.PolAV (Sp ℂ)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ Q.A.left) (v₁ : epsR ℂ ⟶ P₁.A) (t₁ : epsR ℂ ⟶ Q₁.A), IsPolFibre ((algebraMap k ℂ).comp ρ) P P₁ φ₁ → IsPolFibre ((algebraMap k ℂ).comp ρ) Q Q₁ ψ₁ → IsVecOver ((algebraMap k ℂ).comp ρ) φ₁ v v₁ → IsVecOver ((algebraMap k ℂ).comp ρ) ψ₁ t t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![α] ![t₁] (v₁ ≫ f₁)) → ∃ (K₁ : IntermediateField ℚ ℂ) (hk : k ≤ K₁) (a : K₁), FiniteDimensional ℚ K₁ ∧ (a : ℂ) = α ∧ (∀ (P₁ Q₁ : Out.PolAV (Sp K₁)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ Q.A.left) (v₁ : epsR K₁ ⟶ P₁.A) (t₁ : epsR K₁ ⟶ Q₁.A), IsPolFibre ((IntermediateField.inclusion hk).toRingHom.comp ρ) P P₁ φ₁ → IsPolFibre ((IntermediateField.inclusion hk).toRingHom.comp ρ) Q Q₁ ψ₁ → IsVecOver ((IntermediateField.inclusion hk).toRingHom.comp ρ) φ₁ v v₁ → IsVecOver ((IntermediateField.inclusion hk).toRingHom.comp ρ) ψ₁ t t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![a] ![t₁] (v₁ ≫ f₁)) := by
  intro hT hB R _ P Q v t k ρ α hk hv hbas hhom
  obtain ⟨Pk, φk, hPk⟩ := exists_isPolFibre hB ρ P
  obtain ⟨Qk, ψk, hQk⟩ := exists_isPolFibre hB ρ Q
  obtain ⟨Pc, φc, hPc⟩ := exists_isPolFibre hB (algebraMap k ℂ) Pk
  obtain ⟨Qc, ψc, hQc⟩ := exists_isPolFibre hB (algebraMap k ℂ) Qk
  have hPc' := PolFibre.comp hPk hPc
  have hQc' := PolFibre.comp hQk hQc
  obtain ⟨vc, hvc, -⟩ := existsUnique_isVecOver hPc'.2.1.1 v
  obtain ⟨tc, htc, -⟩ := existsUnique_isVecOver hQc'.2.1.1 t
  obtain ⟨fc, hfc, hα⟩ := hhom Pc Qc _ _ vc tc hPc' hQc' hvc htc
  obtain ⟨K, P₀, Q₀, φ₀, ψ₀, m, n, f₀, hK, hP₀, hQ₀, hm, hn, em, en, hf₀, ef⟩ :=
    exists_descent hT hB k Pk Qk hPc hQc fc
  have hP₀' := PolFibre.comp hPk hP₀
  have hQ₀' := PolFibre.comp hQk hQ₀
  obtain ⟨v₀, hv₀, -⟩ := existsUnique_isVecOver hP₀'.2.1.1 v
  obtain ⟨t₀, ht₀, -⟩ := existsUnique_isVecOver hQ₀'.2.1.1 t
  obtain ⟨c, hc, -⟩ := (hbas _ _ _ _ _ hQ₀' ht₀).2 (v₀ ≫ f₀)
    (HomDescent.isTangent_comp f₀ (hv₀.isTangent hP₀'.2.1 hv))
  obtain ⟨a, rfl⟩ : ∃ a, c = ![a] := ⟨c 0, by ext i; fin_cases i; rfl⟩
  have hv' : IsVecOver (algebraMap K ℂ) m v₀ vc :=
    (PolFibre.vec_iff hP₀'.2.1.1 hm.2.1.1.w hv₀).2 (by rw [← Category.assoc, em]; exact hvc)
  have ht' : IsVecOver (algebraMap K ℂ) n t₀ tc :=
    (PolFibre.vec_iff hQ₀'.2.1.1 hn.2.1.1.w ht₀).2 (by rw [← Category.assoc, en]; exact htc)
  have hα' := isLieComb_pull hn.2.1.1 hv' ht' ef hc
  have haα : algebraMap K ℂ a = α := congrFun (((hbas _ _ _ _ _ hQc' htc).2 (vc ≫ fc)
    (HomDescent.isTangent_comp fc (hvc.isTangent hPc'.2.1 hv))).unique hα' hα) 0
  have main : ∀ (P₁ Q₁ : Out.PolAV (Sp K)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ Q.A.left)
      (v₁ : epsR K ⟶ P₁.A) (t₁ : epsR K ⟶ Q₁.A), IsPolFibre ((algebraMap k K).comp ρ) P P₁ φ₁ →
      IsPolFibre ((algebraMap k K).comp ρ) Q Q₁ ψ₁ → IsVecOver ((algebraMap k K).comp ρ) φ₁ v v₁ →
      IsVecOver ((algebraMap k K).comp ρ) ψ₁ t t₁ →
      ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![a] ![t₁] (v₁ ≫ f₁) := by
    intro P₁ Q₁ φ₁ ψ₁ v₁ t₁ hP₁ hQ₁ hv₁ ht₁
    obtain ⟨p, hp, rfl⟩ := PolFibre.cancel (g := RingHom.id K) hP₀' hP₁
    obtain ⟨q, hq, rfl⟩ := PolFibre.cancel (g := RingHom.id K) hQ₀' hQ₁
    obtain ⟨f₁, hf₁, e₁⟩ := HomDescent.exists_isMonHom_pull hp.2.1 hq.2.1 f₀
    exact ⟨f₁, hf₁, isLieComb_pull hq.2.1.1 ((PolFibre.vec_iff hP₀'.2.1.1 hp.2.1.1.w hv₀).2 hv₁)
      ((PolFibre.vec_iff hQ₀'.2.1.1 hq.2.1.1.w ht₀).2 ht₁) e₁ hc⟩
  have : IsScalarTower ℚ k K := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have hfin : FiniteDimensional ℚ K := Module.Finite.trans k K
  exact ⟨K.restrictScalars ℚ, fun x hx => K.algebraMap_mem ⟨x, hx⟩, a, hfin, haα, main⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HomDerivativeClosure
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory.HomDerivative

theorem isLieComb_inv {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {v x : epsR R ⟶ G} {a : R}
    (hv : IsTangent v) (hx : IsLieComb ![a] ![v] x) : IsLieComb ![-a] ![v] x⁻¹ := by
  obtain ⟨y, hy⟩ : ∃ y, IsLieComb ![-a] ![v] y :=
    ⟨_, (GlobalTheory.LieMultiple.isLieComb_one_iff_comp (-a) v _).2 rfl⟩
  have hsum := (GlobalTheory.LieMultiple.lieMultiple_calculus R G G v x y a (-a)).2.1 hv hx hy
  have hone := (GlobalTheory.LieMultiple.lieMultiple_calculus R G G v x y a (-a)).2.2.2.2.2 hv
  rw [add_neg_cancel] at hsum
  have hxy : x * y = 1 :=
    ((GlobalTheory.LieMultiple.isLieComb_one_iff_comp 0 v _).1 hsum).trans
      ((GlobalTheory.LieMultiple.isLieComb_one_iff_comp 0 v _).1 hone).symm
  rw [← eq_inv_of_mul_eq_one_right hxy]
  exact hy

theorem hom_derivative_closure : Out.PolBaseChangeSt → ∀ (R : Type) [CommRing R] (P Q : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A) (t : epsR R ⟶ Q.A) (R₁ : Type) [CommRing R₁] (ρ : R →+* R₁) (S : Set R₁), IsTangent t → (∀ a ∈ S, (∀ (P₁ Q₁ : Out.PolAV (Sp R₁)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ Q.A.left) (v₁ : epsR R₁ ⟶ P₁.A) (t₁ : epsR R₁ ⟶ Q₁.A), IsPolFibre ρ P P₁ φ₁ → IsPolFibre ρ Q Q₁ ψ₁ → IsVecOver ρ φ₁ v v₁ → IsVecOver ρ ψ₁ t t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![a] ![t₁] (v₁ ≫ f₁))) → ∀ a ∈ AddSubgroup.closure S, (∀ (P₁ Q₁ : Out.PolAV (Sp R₁)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ Q.A.left) (v₁ : epsR R₁ ⟶ P₁.A) (t₁ : epsR R₁ ⟶ Q₁.A), IsPolFibre ρ P P₁ φ₁ → IsPolFibre ρ Q Q₁ ψ₁ → IsVecOver ρ φ₁ v v₁ → IsVecOver ρ ψ₁ t t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![a] ![t₁] (v₁ ≫ f₁)) := by
  intro _ R _ P Q v t R₁ _ ρ S ht hS a ha
  induction ha using AddSubgroup.closure_induction with
  | mem a h => exact hS a h
  | zero =>
    intro P₁ Q₁ φ₁ ψ₁ v₁ t₁ hP hQ hv ht₁
    have hT : IsTangent t₁ := IsVecOver.isTangent hQ.2.1 ht₁ ht
    refine ⟨toUnit _ ≫ η, inferInstance, ?_⟩
    have h1 : v₁ ≫ toUnit P₁.A ≫ η[Q₁.A] = 1 := by
      rw [← Category.assoc, CartesianMonoidalCategory.toUnit_unique (v₁ ≫ toUnit _) (toUnit _)]
      rfl
    rw [h1]
    exact (GlobalTheory.LieMultiple.lieMultiple_calculus R₁ Q₁.A Q₁.A t₁ t₁ t₁ 0 0).2.2.2.2.2 hT
  | add a b _ _ iha ihb =>
    intro P₁ Q₁ φ₁ ψ₁ v₁ t₁ hP hQ hv ht₁
    have hT : IsTangent t₁ := IsVecOver.isTangent hQ.2.1 ht₁ ht
    obtain ⟨f, hf, hfa⟩ := iha P₁ Q₁ φ₁ ψ₁ v₁ t₁ hP hQ hv ht₁
    obtain ⟨g, hg, hgb⟩ := ihb P₁ Q₁ φ₁ ψ₁ v₁ t₁ hP hQ hv ht₁
    refine ⟨lift f g ≫ μ, inferInstance, ?_⟩
    change IsLieComb _ _ (v₁ ≫ (f * g))
    rw [MonObj.comp_mul]
    exact (GlobalTheory.LieMultiple.lieMultiple_calculus R₁ Q₁.A Q₁.A t₁ (v₁ ≫ f) (v₁ ≫ g) a b).2.1 hT hfa hgb
  | neg a _ iha =>
    intro P₁ Q₁ φ₁ ψ₁ v₁ t₁ hP hQ hv ht₁
    have hT : IsTangent t₁ := IsVecOver.isTangent hQ.2.1 ht₁ ht
    obtain ⟨f, hf, hfa⟩ := iha P₁ Q₁ φ₁ ψ₁ v₁ t₁ hP hQ hv ht₁
    refine ⟨f⁻¹, inferInstance, ?_⟩
    rw [GrpObj.comp_inv]
    exact isLieComb_inv hT hfa

end GlobalTheory.HomDerivative
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.KTrivOfUnimodular
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

namespace GlobalTheory.HermTensorKernel

open GlobalTheory.CechPic

section Local

variable {Y Y' B : Scheme.{0}}

def LocZero (π : Y ⟶ B) (c : Pic Y) : Prop :=
  ∀ p : B, ∃ V : B.Opens, p ∈ V ∧ ∀ (Z : Scheme.{0}) (f : Z ⟶ Y), (∀ z, π (f z) ∈ V) → pull f c = 0

theorem LocZero.add {π : Y ⟶ B} {c d : Pic Y} (hc : LocZero π c) (hd : LocZero π d) : LocZero π (c + d) := by
  intro p
  obtain ⟨V, hV, H⟩ := hc p
  obtain ⟨V', hV', H'⟩ := hd p
  refine ⟨V ⊓ V', ⟨hV, hV'⟩, fun Z f hf => ?_⟩
  rw [map_add (f := _), H Z f fun z => (hf z).1, H' Z f fun z => (hf z).2, add_zero]

theorem LocZero.pull {π : Y ⟶ B} {c : Pic Y} (hc : LocZero π c) (k : Y' ⟶ Y) :
    LocZero (k ≫ π) (pull k c) := by
  intro p
  obtain ⟨V, hV, H⟩ := hc p
  exact ⟨V, hV, fun Z f hf => (pull_comp f k c).symm.trans (H Z (f ≫ k) hf)⟩

theorem locZero_base (π : Y ⟶ B) (d : Pic B) : LocZero π (pull π d) := by
  obtain ⟨D, hD, rfl⟩ := cls_surj d
  intro p
  obtain ⟨i, hi⟩ := exists_chart hD p
  refine ⟨D.U i, hi, fun Z f hf => (pull_comp f π _).symm.trans ?_⟩
  exact (cls_eq_zero_iff (pull_isLB hD (f ≫ π))).2
    (BoxKernel.gen_of_chart (pull_isLB hD _) (fun _ => i) fun z => mem_pull.2 (hf z))

theorem locZero_iff (π : Y ⟶ B) {M : LB Y} (hM : M.IsLB) :
    (∀ p : B, ∃ V : B.Opens, p ∈ V ∧ ∃ c : LB.Gen (M.pull (π ⁻¹ᵁ V).ι), c.IsGen) ↔ LocZero π (cls M hM) := by
  refine forall_congr' fun p => exists_congr fun V => and_congr_right fun _ => ?_
  rw [← cls_eq_zero_iff (pull_isLB hM _), cls_pull hM]
  refine ⟨fun H Z f hf => ?_, fun H => H _ _ fun z => z.2⟩
  have hr : Set.range f ⊆ Set.range (π ⁻¹ᵁ V).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hf z
  rw [← IsOpenImmersion.lift_fac (π ⁻¹ᵁ V).ι f hr, pull_comp, H, map_zero]

end Local

section Group

variable {S : Scheme.{0}} {A T : Over S} [GrpObj A]

theorem translDiff_iff {L : LB A.left} (hL : L.IsLB) (x : T ⟶ A) :
    (∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
      ∃ c : LB.Gen ((Out.translDiff A L x).pull ((fst T A).left ⁻¹ᵁ V).ι), c.IsGen) ↔
      LocZero (fst T A).left (lam (cls L hL) (fst T A ≫ x) (snd T A)) := by
  have hD : (Out.translDiff A L x).IsLB := LB.isLB_linComb hL _ _
  rw [locZero_iff _ hD]
  have e : lam (cls L hL) (fst T A ≫ x) (snd T A) = cls _ hD +
      pull (fst T A).left (pull (1 : T ⟶ A).left (cls L hL) - pull x.left (cls L hL)) := by
    have e₁ : cls _ hD = pull ((fst T A ≫ x) * snd T A).left (cls L hL) - pull (snd T A).left (cls L hL) := by
      refine (cls_linComb hL _ _ hD).trans ?_
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, ← sub_eq_add_neg]
      rfl
    rw [e₁, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_one, lam]
    abel
  refine ⟨fun H => e ▸ H.add (locZero_base _ _), fun H => ?_⟩
  have := H.add (locZero_base _ (-(pull (1 : T ⟶ A).left (cls L hL) - pull x.left (cls L hL))))
  rwa [e, map_neg, add_neg_cancel_right] at this

end Group

end GlobalTheory.HermTensorKernel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIsHomFamilyBaseChange
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

namespace PureType

section Grp

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {B G : Over S} {B' G' : Over S'}
  {β : B'.left ⟶ B.left} {π : G'.left ⟶ G.left}

set_option autoImplicit false in
theorem _root_.GlobalTheory.PureType.exists_hom_over (hβ : β ≫ B.hom = B'.hom ≫ f)
    (hπ : IsPullback π G'.hom G.hom f) (φ : B ⟶ G) :
    ∃ φ' : B' ⟶ G', φ'.left ≫ π = β ≫ φ.left := by
  refine ⟨Over.homMk (hπ.lift (β ≫ φ.left) B'.hom ?_) (hπ.lift_snd _ _ _), ?_⟩
  · rw [Category.assoc, Over.w φ, hβ]
  · exact hπ.lift_fst _ _ _

set_option autoImplicit false in
theorem _root_.GlobalTheory.PureType.eq_of_comp_eq (hπ : IsPullback π G'.hom G.hom f) {T : Over S'}
    {x y : T ⟶ G'} (h : x.left ≫ π = y.left ≫ π) : x = y :=
  Over.OverMorphism.ext (hπ.hom_ext h (by simp))

variable [GrpObj B] [GrpObj G] [GrpObj B'] [GrpObj G']

set_option autoImplicit false in
theorem _root_.GlobalTheory.PureType.isMonHom_over (hβ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback B' B f β) (hπ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G f π) {φ : B ⟶ G}
    [IsMonHom φ] {φ' : B' ⟶ G'} (h : φ'.left ≫ π = β ≫ φ.left) : IsMonHom φ' := by
  have key : ∀ (T : Over S') (x y : T ⟶ B'), (x * y) ≫ φ' = (x ≫ φ') * (y ≫ φ') := by
    intro T x y
    have hw : ∀ z : T ⟶ B', (z.left ≫ β) ≫ B.hom = (Over.mk (T.hom ≫ f)).hom := by
      intro z
      rw [Category.assoc, hβ.1.w, ← Category.assoc, Over.w z]
      rfl
    let x₀ : Over.mk (T.hom ≫ f) ⟶ B := Over.homMk (x.left ≫ β) (hw x)
    let y₀ : Over.mk (T.hom ≫ f) ⟶ B := Over.homMk (y.left ≫ β) (hw y)
    have h₁ := hβ.2 T x y x₀ y₀ rfl rfl
    have h₂ := hπ.2 T (x ≫ φ') (y ≫ φ') (x₀ ≫ φ) (y₀ ≫ φ) (by simp [x₀, h]) (by simp [y₀, h])
    apply _root_.GlobalTheory.PureType.eq_of_comp_eq hπ.1
    rw [← h₂, ← MonObj.mul_comp]
    simp only [Over.comp_left, h₁, Category.assoc, h]
  have one : ∀ (T : Over S'), (1 : T ⟶ B') ≫ φ' = 1 := by
    intro T
    have := key T 1 1
    rw [_root_.mul_one] at this
    exact mul_left_cancel (a := (1 : T ⟶ B') ≫ φ') (by rw [_root_.mul_one]; exact this.symm)
  constructor
  · simpa [Hom.one_def] using one (𝟙_ _)
  · have := key (B' ⊗ B') (fst B' B') (snd B' B')
    simpa [Hom.mul_def] using this

end Grp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

end PureType

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HolomorphicUniformisationTangentUnimodularRiemanStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane
theorem _root_.GlobalTheory.T.holomorphicUniformisation_tangent_unimodular_riemannForm : ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g), (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) ∧ ∀ (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ), u.IsAH Hm χ → ∃ Ef : LinearMap.BilinForm ℤ u.Λ, (∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧ Function.Bijective Ef := by
  first | exact @GlobalTheory.AnyUnif.tangent_and_unimodular | exact GlobalTheory.AnyUnif.tangent_and_unimodular | (intros; apply GlobalTheory.AnyUnif.tangent_and_unimodular <;> assumption)
end
