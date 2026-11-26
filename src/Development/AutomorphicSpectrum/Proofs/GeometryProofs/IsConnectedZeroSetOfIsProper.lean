module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ZariskiSplit
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalFunctions
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsAbPartBaseChange
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteBaseChange

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsConnectedZeroSetOfIsProper
section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ZeroSetSpecialFibreConnected
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.SpecialFibreConnected

theorem mem_range_of_isIntegral {O Ω : Type} [CommRing O] [IsDomain O] [IsIntegrallyClosed O] [Field Ω]
    [Algebra O Ω] (hinj : Function.Injective (algebraMap O Ω)) (hc : ConstClosed O Ω) (a : Ω)
    (ha : IsIntegral O a) : ∃ o : O, algebraMap O Ω o = a := by
  obtain ⟨x, y, hy, e⟩ := hc a ha.isAlgebraic
  let ι : FractionRing O →ₐ[O] Ω :=
    { IsFractionRing.lift (K := FractionRing O) hinj with
      commutes' := fun o => IsFractionRing.lift_algebraMap hinj o }
  have hy' : algebraMap O Ω y ≠ 0 := fun h => hy (hinj (by rw [h, map_zero]))
  have e' : ι (algebraMap O (FractionRing O) x / algebraMap O (FractionRing O) y) = a := by
    rw [map_div₀, ι.commutes, ι.commutes, ← e, mul_div_cancel_right₀ _ hy']
  have hi : IsIntegral O (algebraMap O (FractionRing O) x / algebraMap O (FractionRing O) y) := by
    rw [← isIntegral_algHom_iff ι ι.toRingHom.injective, e']
    exact ha
  obtain ⟨o, ho⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  exact ⟨o, by rw [← e', ← ho, ι.commutes]⟩

theorem appTop_injective {Z : Scheme.{0}} [IsReduced Z] {Ω : Type} [Field Ω]
    (η : Spec (CommRingCat.of Ω) ⟶ Z) (h : ∀ q : Z, η (IsLocalRing.closedPoint Ω) ⤳ q) :
    Function.Injective η.appTop.hom := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro t ht
  rw [← basicOpen_eq_bot_iff, eq_bot_iff]
  intro q hq
  have h1 : η (IsLocalRing.closedPoint Ω) ∈ Z.basicOpen t :=
    (h q).mem_open (Z.basicOpen t).isOpen hq
  have h2 : IsLocalRing.closedPoint Ω ∈ η ⁻¹ᵁ Z.basicOpen t := h1
  rw [Scheme.preimage_basicOpen_top] at h2
  have h3 : η.appTop t = 0 := ht
  rw [h3, Scheme.basicOpen_zero] at h2
  exact h2.elim

theorem bijective_const {Z : Scheme.{0}} [IsReduced Z] {Ω : Type} [Field Ω]
    (η : Spec (CommRingCat.of Ω) ⟶ Z) (h : ∀ q : Z, η (IsLocalRing.closedPoint Ω) ⤳ q)
    {O : Type} [CommRing O] [IsDomain O] [IsIntegrallyClosed O] [Algebra O Ω]
    (f : Z ⟶ Spec (CommRingCat.of O)) [IsProper f] (hinj : Function.Injective (algebraMap O Ω))
    (hf : η ≫ f = Spec.map (CommRingCat.ofHom (algebraMap O Ω))) (hc : ConstClosed O Ω) :
    Function.Bijective (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom) := by
  let ψ : O →+* Γ(Z, ⊤) := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom
  let φ : Γ(Z, ⊤) →+* Ω := (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom.comp η.appTop.hom
  have hφ : Function.Injective φ :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom).1.comp (appTop_injective η h)
  have hcomp : φ.comp ψ = algebraMap O Ω := by
    have : (Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ f.appTop ≫ η.appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom = CommRingCat.ofHom (algebraMap O Ω) := by
      rw [← Scheme.Hom.comp_appTop_assoc, hf, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    exact congrArg (fun q => q.hom) this
  have hψ : ψ.IsIntegral :=
    RingHom.IsIntegral.trans _ _
      (RingHom.isIntegral_of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of O)).inv).2)
      (isIntegral_appTop_of_universallyClosed f)
  refine ⟨fun a b hab => hinj ?_, fun t => ?_⟩
  · rw [← hcomp]
    exact congrArg φ hab
  · have hi : IsIntegral O (φ t) := by
      obtain ⟨p, hp, e⟩ := hψ t
      refine ⟨p, hp, ?_⟩
      rw [← hcomp, ← Polynomial.hom_eval₂, e, map_zero]
    obtain ⟨o, ho⟩ := mem_range_of_isIntegral hinj hc _ hi
    refine ⟨o, hφ ?_⟩
    rw [← ho, ← hcomp]
    rfl


attribute [local instance] GroundTheory.Arith.SchemeCoh.algebraOfOver in
open GroundTheory.Arith.SchemeCoh in
theorem isConnected_closed {Z : Scheme.{0}} {O : Type} [CommRing O] [IsNoetherianRing O] [IsLocalRing O]
    (f : Z ⟶ Spec (CommRingCat.of O)) [IsProper f]
    (h : Function.Bijective (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom)) :
    _root_.IsConnected (f ⁻¹' {IsLocalRing.closedPoint O}) := by
  letI : Z.Over (Spec (.of O)) := ⟨f⟩
  have : IsProper (Z ↘ Spec (.of O)) := (inferInstance : IsProper f)
  exact isConnected_closedFibre_of_surj (A := O) (X := Z) h
    (fun x hx => formalFunctions_mem_range (IsLocalRing.maximalIdeal O) (isCoherent_unit Z) 0 hx 0)

end PositivityTheory.Xgn.SpecialFibreConnected

open PositivityTheory.Xgn.SpecialFibreConnected in
theorem PositivityTheory.Xgn.zero_set_special_fibre_connected : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O), Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → IsCptGen ξ → ConstClosed O Ω → _root_.IsConnected (zeroSet ξ (algebraMap O Ω ϖ)) := by
  intro X Ω _ ξ O _ _ _ _ s _ ϖ hϖ hinj hs hg hc
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  obtain ⟨U, hU, hcl, hint⟩ := cpt_open_integral X Ω ξ hg
  have hrange : Set.range ξ ⊆ Set.range U.ι := by
    rintro _ ⟨z, rfl⟩
    have hz : z = IsLocalRing.closedPoint Ω := Subsingleton.elim (α := PrimeSpectrum Ω) _ _
    rw [Scheme.Opens.range_ι, hz]
    exact (hU _).2 specializes_rfl
  let η : Spec (CommRingCat.of Ω) ⟶ U.toScheme := IsOpenImmersion.lift U.ι ξ hrange
  have hη : η ≫ U.ι = ξ := IsOpenImmersion.lift_fac _ _ _
  haveI : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion _ (by rwa [Scheme.Opens.range_ι])
  have hsp : ∀ q : U.toScheme, η (IsLocalRing.closedPoint Ω) ⤳ q := fun q => by
    rw [← U.ι.isOpenEmbedding.isInducing.specializes_iff]
    have e : U.ι (η (IsLocalRing.closedPoint Ω)) = genPt ξ :=
      congrArg (fun g : Spec (CommRingCat.of Ω) ⟶ X => g (IsLocalRing.closedPoint Ω)) hη
    exact e ▸ (hU _).1 q.2
  have hb := bijective_const η hsp (U.ι ≫ s) hinj (by rw [← Category.assoc, hη, hs]) hc
  have hconn := (isConnected_closed (U.ι ≫ s) hb).image U.ι U.ι.continuous.continuousOn
  have hm : ∀ P : PrimeSpectrum O, ϖ ∈ P.asIdeal ↔ P = IsLocalRing.closedPoint O := fun P => by
    have hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
    constructor
    · intro h
      apply PrimeSpectrum.ext
      refine ((IsLocalRing.maximalIdeal.isMaximal O).eq_of_le P.isPrime.ne_top ?_).symm
      rw [hmax, Ideal.span_singleton_le_iff_mem]
      exact h
    · rintro rfl
      change ϖ ∈ IsLocalRing.maximalIdeal O
      rw [hmax]
      exact Ideal.mem_span_singleton_self ϖ
  have key : ∀ (q : X) (h : genPt ξ ⤳ q),
      ¬ unitAt ξ ⟨q, h⟩ (algebraMap O Ω ϖ) ↔ s q = IsLocalRing.closedPoint O := fun q h => by
    rw [(ConstReg.regular_const X Ω ξ O s hs ⟨q, h⟩ ϖ).2 hg, not_not]
    exact hm _
  convert hconn using 1
  ext q
  constructor
  · rintro ⟨h, hq⟩
    refine ⟨⟨q, (hU q).2 h⟩, ?_, rfl⟩
    exact (key q h).1 hq
  · rintro ⟨z, hz, rfl⟩
    exact ⟨(hU _).1 z.2, (key _ _).2 hz⟩
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsConnectedZeroSetOfIsProper
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem isConnected_zeroSet_of_isProper : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O), Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → IsCptGen ξ → ConstClosed O Ω → _root_.IsConnected (zeroSet ξ (algebraMap O Ω ϖ)) :=
  @PositivityTheory.Xgn.zero_set_special_fibre_connected

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsConnectedZeroSetOfIsProperStatement
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isConnected_zeroSet_uniformizer : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O), Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → IsCptGen ξ → ConstClosed O Ω → _root_.IsConnected (zeroSet ξ (algebraMap O Ω ϖ)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.isConnected_zeroSet_of_isProper | exact GlobalTheory.CompanionTheory.Ar.Flat.isConnected_zeroSet_of_isProper | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.isConnected_zeroSet_of_isProper <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicAtlasCoordCompat
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicAtlasCoordCompat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ImmBlock

theorem aeval_mul_of_isHomogeneous {σ R : Type*} [Fintype σ] [CommRing R] {alg : Algebra ℤ R}
    {F : MvPolynomial σ ℤ} {n : ℕ}
    (hF : F.IsHomogeneous n) (a : σ → R) (t : R) :
    MvPolynomial.aeval (fun i => a i * t) F = MvPolynomial.aeval a F * t ^ n := by
  classical
  simp only [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i, d i = n := by
    have h := hF (MvPolynomial.mem_support_iff.1 hd)
    have h2 : Finsupp.degree d = n := by
      rw [Finsupp.degree_eq_weight_one]
      exact h
    rw [← h2, Finsupp.degree_apply]
    exact (Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by simpa using hi)).symm
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg, _root_.mul_assoc]

theorem aeval_ringHom {σ A B : Type*} [CommRing A] [CommRing B] {algA : Algebra ℤ A} {algB : Algebra ℤ B}
    (φ : A →+* B) (a : σ → A) (P : MvPolynomial σ ℤ) :
    MvPolynomial.aeval (fun i => φ (a i)) P = φ (MvPolynomial.aeval a P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp only [MvPolynomial.aeval_C, eq_intCast, map_intCast]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, MvPolynomial.aeval_X]

theorem differentiable_aeval {σ κ : Type*} [Fintype κ] (g : σ → κ) (P : MvPolynomial σ ℤ) :
    Differentiable ℂ (fun u : κ → ℂ => MvPolynomial.aeval (fun i => u (g i)) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using differentiable_const _
  | add p q hp hq =>
    simp only [map_add (f := _)]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.aeval_X]
    exact hp.mul (differentiable_apply _)

theorem form_mem {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]
    (y : (Σ k, J k) → Ω) (k₀ k : K) (n : ℕ) (F G : MvPolynomial (J k₀) ℤ) (hF : F.IsHomogeneous n)
    (hG : G.IsHomogeneous n) (c d : J k)
    (h : MvPolynomial.aeval (fun i : J k₀ => y ⟨k₀, i⟩) F * y ⟨k, c⟩ =
      MvPolynomial.aeval (fun i : J k₀ => y ⟨k₀, i⟩) G * y ⟨k, d⟩) :
    MvPolynomial.rename (Sigma.mk k₀) F * MvPolynomial.X ⟨k, c⟩ -
      MvPolynomial.rename (Sigma.mk k₀) G * MvPolynomial.X ⟨k, d⟩ ∈ mCoordIdeal y := by
  have hh := congrArg (MvPolynomial.C : Ω → MvPolynomial K Ω) h
  simp only [map_mul] at hh
  rw [mCoordIdeal, RingHom.mem_ker]
  simp only [mConeMap, map_sub, map_mul, MvPolynomial.aeval_rename, MvPolynomial.aeval_X, Function.comp_def]
  rw [aeval_mul_of_isHomogeneous hF (fun i : J k₀ => (MvPolynomial.C (y ⟨k₀, i⟩) : MvPolynomial K Ω)) (MvPolynomial.X k₀),
    aeval_mul_of_isHomogeneous hG (fun i : J k₀ => (MvPolynomial.C (y ⟨k₀, i⟩) : MvPolynomial K Ω)) (MvPolynomial.X k₀),
    aeval_ringHom MvPolynomial.C (fun i : J k₀ => y ⟨k₀, i⟩) F,
    aeval_ringHom MvPolynomial.C (fun i : J k₀ => y ⟨k₀, i⟩) G]
  linear_combination (MvPolynomial.X k₀ ^ n * MvPolynomial.X k) * hh

theorem differentiableAt_quot {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {a b : E → ℂ} {v : E}
    (ha : DifferentiableAt ℂ a v) (hb : DifferentiableAt ℂ b v) (h : b v ≠ 0) :
    DifferentiableAt ℂ (fun w => a w / b w) v := by
  simp only [div_eq_mul_inv]
  exact ha.mul (hb.inv h)

theorem ker_bot_of_factor {E F₁ F₂ : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F₁]
    [NormedSpace ℂ F₁] [NormedAddCommGroup F₂] [NormedSpace ℂ F₂] {f : E → F₁} {a : E → F₂} {Ψ : F₁ → F₂} {v₀ : E}
    (hf : DifferentiableAt ℂ f v₀) (hΨ : DifferentiableAt ℂ Ψ (f v₀)) (h : a =ᶠ[nhds v₀] Ψ ∘ f)
    (hk : (fderiv ℂ a v₀).ker = ⊥) : (fderiv ℂ f v₀).ker = ⊥ := by
  rw [h.fderiv_eq, fderiv_comp v₀ hΨ hf] at hk
  rw [eq_bot_iff]
  intro u hu
  have hu' : fderiv ℂ f v₀ u = 0 := hu
  have : u ∈ ((fderiv ℂ Ψ (f v₀)).comp (fderiv ℂ f v₀)).ker := by
    change (fderiv ℂ Ψ (f v₀)) (fderiv ℂ f v₀ u) = 0
    rw [hu', map_zero]
  rwa [hk] at this

theorem immersion_block : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (k₀ : K), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → EmbedsGeneric ξ (fun i : J k₀ => y ⟨k₀, i⟩) → ∀ (e : ℕ) (M : Type) [TopologicalSpace M] (A : ReciprocityTheory.AnForm.M.FinHolAtlas e M) (U : M → Set M) (lam : M → M → (Σ k, J k) → ℂ), Cmp.IsEmbedded A (mCoordIdeal y) U lam → ∀ (κ : Type) [Fintype κ] (ix : κ ≃ J k₀) (x : M) (p : κ), lam x x ⟨k₀, ix p⟩ ≠ 0 → ∀ j, x ∈ (A.chart j).source → DifferentiableAt ℂ (fun (v : Fin e → ℂ) (i : κ) => lam x ((A.chart j).symm v) ⟨k₀, ix i⟩ / lam x ((A.chart j).symm v) ⟨k₀, ix p⟩) (A.chart j x) ∧ (fderiv ℂ (fun (v : Fin e → ℂ) (i : κ) => lam x ((A.chart j).symm v) ⟨k₀, ix i⟩ / lam x ((A.chart j).symm v) ⟨k₀, ix p⟩) (A.chart j x)).ker = ⊥ := by
  intro X Ω _ _ ξ K _ J _ y k₀ hTie hEmb e M _ A U lam hE κ _ ix x p hp j hj
  classical
  have hev : ∀ (z : (Σ k, J k) → ℂ) (f : MRing J),
      MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) f) = MvPolynomial.aeval z f := fun z f => by
    rw [MvPolynomial.eval_map, MvPolynomial.aeval_def]
    congr 1
  set G : (Fin e → ℂ) → (Σ k, J k) → ℂ := fun v => lam x ((A.chart j).symm v) with hGdef
  set v₀ : Fin e → ℂ := A.chart j x with hv₀
  have hG0 : G v₀ = lam x x := by
    simp only [hGdef, hv₀]
    rw [(A.chart j).left_inv hj]
  have hS : v₀ ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U x := by
    refine ⟨(A.chart j).map_source hj, ?_⟩
    change (A.chart j).symm (A.chart j x) ∈ U x
    rw [(A.chart j).left_inv hj]
    exact hE.mem_U x
  have hSo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U x) :=
    (A.chart j).isOpen_inter_preimage_symm (hE.isOpen x)
  have hAn : ∀ q, DifferentiableAt ℂ (fun v => G v q) v₀ := fun q =>
    (hE.holo x q j v₀ hS).differentiableAt
  have hCo : ∀ q, ContinuousAt (fun v => G v q) v₀ := fun q => (hAn q).continuousAt
  have hw : lam x x ∈ mcPts (mCoordIdeal y) := hE.mem x x (hE.mem_U x)
  have hwpts : lam x x ∈ Small.ptsOver ℂ (mCoordIdeal y) :=
    ⟨hw.1, fun f hf => by rw [← hev]; exact hw.2 f hf⟩
  choose r hr using hw.1
  set p' : (k : K) → J k := Function.update r k₀ (ix p) with hp'def
  have hp'0 : p' k₀ = ix p := by simp [hp'def]
  have hp' : ∀ k, lam x x ⟨k, p' k⟩ ≠ 0 := by
    intro k
    by_cases h : k = k₀
    · subst h
      rw [hp'0]
      exact hp
    · rw [hp'def, Function.update_of_ne h]
      exact hr k
  have hblk := fun k => GlobalTheory.T.small_points_coord_ratio_bound X Ω ξ K J y k₀ hTie hEmb ℂ (lam x x) hwpts (ix p) k (p' k) hp (hp' k)
  choose n F hFh hFr hFn using hblk

  set f : (Fin e → ℂ) → κ → ℂ := fun v i => G v ⟨k₀, ix i⟩ / G v ⟨k₀, ix p⟩ with hfdef
  have ht0 : G v₀ ⟨k₀, ix p⟩ ≠ 0 := by rw [hG0]; exact hp
  have hfd : DifferentiableAt ℂ f v₀ :=
    by
    refine differentiableAt_pi.2 fun i => ?_
    have h := differentiableAt_quot (hAn ⟨k₀, ix i⟩) (hAn ⟨k₀, ix p⟩) ht0
    exact h

  set ev : MvPolynomial (J k₀) ℤ → (κ → ℂ) → ℂ :=
    fun P u => MvPolynomial.aeval (fun i' : J k₀ => u (ix.symm i')) P with hevdef
  have hevd : ∀ P, Differentiable ℂ (ev P) := fun P => differentiable_aeval (fun i' => ix.symm i') P
  have hscale : ∀ v k (d : J k), ev (F k d) (f v) =
      MvPolynomial.aeval (fun i' : J k₀ => G v ⟨k₀, i'⟩) (F k d) * ((G v ⟨k₀, ix p⟩)⁻¹) ^ n k := by
    intro v k d
    rw [← aeval_mul_of_isHomogeneous (hFh k d)]
    simp only [hevdef, hfdef, Equiv.apply_symm_apply, div_eq_mul_inv]
  have hden0 : ∀ k, ev (F k (p' k)) (f v₀) ≠ 0 := by
    intro k
    rw [hscale, hG0]
    exact mul_ne_zero (hFn k) (pow_ne_zero _ (inv_ne_zero hp))
  set Ψ : (κ → ℂ) → (Σ k, J k) → ℂ := fun u q => ev (F q.1 q.2) u / ev (F q.1 (p' q.1)) u with hΨdef
  have hΨd : DifferentiableAt ℂ Ψ (f v₀) :=
    by
    refine differentiableAt_pi.2 fun q => ?_
    have h := differentiableAt_quot (hevd (F q.1 q.2) (f v₀)) (hevd (F q.1 (p' q.1)) (f v₀)) (hden0 q.1)
    exact h

  have e1 : ∀ᶠ v in nhds v₀, G v ∈ mcPts (mCoordIdeal y) := by
    filter_upwards [hSo.mem_nhds hS] with v hv
    exact hE.mem x _ hv.2
  have e2 : ∀ᶠ v in nhds v₀, ∀ k, G v ⟨k, p' k⟩ ≠ 0 :=
    Filter.eventually_all.2 fun k =>
      (hCo ⟨k, p' k⟩).eventually_ne (by rw [hG0]; exact hp' k)
  have e3 : ∀ᶠ v in nhds v₀, ∀ k, ev (F k (p' k)) (f v) ≠ 0 :=
    Filter.eventually_all.2 fun k =>
      (((hevd _).continuous.continuousAt).comp hfd.continuousAt).eventually_ne (hden0 k)
  have e4 : ∀ᶠ v in nhds v₀, G v ⟨k₀, ix p⟩ ≠ 0 := (hCo _).eventually_ne ht0
  have hfac : (fun v => affCoord p' (G v)) =ᶠ[nhds v₀] Ψ ∘ f := by
    filter_upwards [e1, e2, e3, e4] with v h1 h2 h3 h4
    funext q
    obtain ⟨k, d⟩ := q
    have hmem := form_mem y k₀ k (n k) (F k d) (F k (p' k)) (hFh k d) (hFh k (p' k)) (p' k) d (hFr k d)
    have h0 := h1.2 _ hmem
    rw [hev] at h0
    simp only [map_sub, map_mul, MvPolynomial.aeval_rename, MvPolynomial.aeval_X, Function.comp_def] at h0
    have hrel : ev (F k d) (f v) * G v ⟨k, p' k⟩ = ev (F k (p' k)) (f v) * G v ⟨k, d⟩ := by
      rw [hscale, hscale]
      linear_combination ((G v ⟨k₀, ix p⟩)⁻¹) ^ n k * h0
    change G v ⟨k, d⟩ / G v ⟨k, p' k⟩ = ev (F k d) (f v) / ev (F k (p' k)) (f v)
    rw [div_eq_div_iff (h2 k) (h3 k)]
    linear_combination -hrel
  have hk : (fderiv ℂ (fun v => affCoord p' (G v)) v₀).ker = ⊥ :=
    hE.immersion x p' hp' j hj
  exact ⟨hfd, ker_bot_of_factor hfd hΨd hfac hk⟩

end GlobalTheory.CompanionTheory.Ar.ImmBlock
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicAtlasCoordCompatStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_atlas_coord_compat : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (k₀ : K), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → EmbedsGeneric ξ (fun i : J k₀ => y ⟨k₀, i⟩) → ∀ (e : ℕ) (M : Type) [TopologicalSpace M] (A : ReciprocityTheory.AnForm.M.FinHolAtlas e M) (U : M → Set M) (lam : M → M → (Σ k, J k) → ℂ), Cmp.IsEmbedded A (mCoordIdeal y) U lam → ∀ (κ : Type) [Fintype κ] (ix : κ ≃ J k₀) (x : M) (p : κ), lam x x ⟨k₀, ix p⟩ ≠ 0 → ∀ j, x ∈ (A.chart j).source → DifferentiableAt ℂ (fun (v : Fin e → ℂ) (i : κ) => lam x ((A.chart j).symm v) ⟨k₀, ix i⟩ / lam x ((A.chart j).symm v) ⟨k₀, ix p⟩) (A.chart j x) ∧ (fderiv ℂ (fun (v : Fin e → ℂ) (i : κ) => lam x ((A.chart j).symm v) ⟨k₀, ix i⟩ / lam x ((A.chart j).symm v) ⟨k₀, ix p⟩) (A.chart j x)).ker = ⊥ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ImmBlock.immersion_block | exact GlobalTheory.CompanionTheory.Ar.ImmBlock.immersion_block | (intros; apply GlobalTheory.CompanionTheory.Ar.ImmBlock.immersion_block <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.OrthogonalMetricHermitianBundle
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtEigen
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagFib

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar


open LieTangent in
theorem valAt_eigen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L : Type) [Field L] (zL : Sp L ⟶ 𝔐.X) (h : genPt 𝔐.ξ ⤳ centre zL) (g₀ : c.F →+* 𝔐.X.presheaf.stalk (centre zL)), (genMap 𝔐.ξ ⟨centre zL, h⟩).comp g₀ = 𝔐.cst → ∀ (s : CMType H ⊕ CMType H) (e : 𝔐.Li) (v : epsAt zL ⟶ 𝔐.t.G) (a : 𝓞 E), e ∈ 𝔐.Vgen s → 𝔐.M.ValAt zL e v → (v ≫ 𝔐.t.act.act a).left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.epsMul ((Scheme.stalkClosedPointTo zL).hom (g₀ (labelEmb c s a))))) ≫ v.left := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J y 𝔐 L _ zL h g₀ hg s e v a he hv
  obtain ⟨h', v₀, hext, rfl⟩ := (𝔐.M.valAt_iff zL e v).1 hv
  have hgen : genMap 𝔐.ξ ⟨centre zL, h⟩ (g₀ (labelEmb c s a)) = 𝔐.emb s a :=
    DFunLike.congr_fun hg (labelEmb c s a)
  have hρ : 𝔐.ρ a e = 𝔐.emb s a • e := by
    have h1 : e ∈ LinearMap.ker (𝔐.ρ a - 𝔐.emb s a • LinearMap.id) :=
      (Submodule.mem_iInf _).1 he a
    rw [LinearMap.mem_ker] at h1
    simpa [sub_eq_zero] using h1
  have hext' := (𝔐.M.extends_iff _ _ _).1 hext
  have h1 : 𝔐.M.Extends ⟨centre zL, h⟩ (𝔐.emb s a • e) (v₀ ≫ 𝔐.t.act.act a) := by
    rw [LieModel.extends_iff]
    refine ⟨?_, ?_⟩
    · rw [isTanAt_iff, ← Category.assoc, (isTanAt_iff _).1 hext'.1]
      haveI := 𝔐.t.act.hom a
      exact one_comp _
    · rw [← hρ, 𝔐.act a e, hext'.2, Category.assoc]
  have h2 := hext.smul (g₀ (labelEmb c s a))
  rw [hgen] at h2
  have key := h1.unique (𝔐.tie.gen.inj _) h2
  have e1 : epsBase _ (spec_centre zL) ≫ v₀ ≫ 𝔐.t.act.act a =
      epsScale zL ((Scheme.stalkClosedPointTo zL).hom (g₀ (labelEmb c s a))) ≫ epsBase _ (spec_centre zL) ≫ v₀ := by
    rw [key, ← Category.assoc, base_scale, Category.assoc]
    rfl
  exact congrArg (fun q => q.left) ((Category.assoc _ _ _).trans e1)

end GlobalTheory.CompanionTheory.Ar.FlagFib
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.OrthogonalMetricHermitianBundle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagFib.FibOrth

open GroundTheory.Heights₂.Heights LieTangent

section Form

variable {L : Type} [Field L]

theorem one_tmul_smul (σ : L →+* ℂ) {V : Type} [AddCommGroup V] [Module (𝓞 L) V] (r : 𝓞 L) (x : V) :
    (1 : ComplexAt σ) ⊗ₜ[𝓞 L] (r • x) = (σ (r : L)) • ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) := by
  rw [tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
  congr 1

variable [NumberField L]

theorem core_span {R V F : Type} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup F] [Module ℂ F]
    (C : InnerProductSpace.Core ℂ F) (f : V →+ F) (φ : R → ℂ) (hs : ∀ r x, f (r • x) = φ r • f x) (A A' : Set V)
    (h : ∀ x ∈ A, ∀ x' ∈ A', C.inner (f x) (f x') = 0) :
    ∀ x ∈ Submodule.span R A, ∀ x' ∈ Submodule.span R A', C.inner (f x) (f x') = 0 := by
  let c : PreInnerProductSpace.Core ℂ F := C.toCore
  intro x hx x' hx'
  induction hx using Submodule.span_induction with
  | mem a ha =>
    induction hx' using Submodule.span_induction with
    | mem b hb => exact h a ha b hb
    | zero => rw [map_zero]; exact InnerProductSpace.Core.inner_zero_right _
    | add u v _ _ hu hv =>
      rw [map_add (f := _)]
      exact (InnerProductSpace.Core.inner_add_right _ _ _).trans (by rw [show _ = _ from hu, show _ = _ from hv, add_zero])
    | smul r u _ hu =>
      rw [hs]
      exact (InnerProductSpace.Core.inner_smul_right _ _).trans (by rw [show _ = _ from hu, mul_zero])
  | zero => rw [map_zero]; exact InnerProductSpace.Core.inner_zero_left _
  | add u v _ _ hu hv =>
    rw [map_add (f := _)]
    exact (InnerProductSpace.Core.inner_add_left _ _ _).trans (by rw [show _ = _ from hu, show _ = _ from hv, add_zero])
  | smul r u _ hu =>
    rw [hs]
    exact (InnerProductSpace.Core.inner_smul_left _ _).trans (by rw [show _ = _ from hu, mul_zero])

theorem orth_sat (B : HermitianBundle.{0} L) (σ : L →+* ℂ) (A A' : Set B.carrier)
    (h : ∀ x ∈ A, ∀ x' ∈ A',
      (B.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x') = 0)
    (x x' : B.carrier) (a a' : 𝓞 L) (ha : a ≠ 0) (ha' : a' ≠ 0) (hx : a • x ∈ Submodule.span (𝓞 L) A)
    (hx' : a' • x' ∈ Submodule.span (𝓞 L) A') :
    (B.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x') = 0 := by
  let f : B.carrier →+ Fibre σ B.carrier :=
    { toFun := fun x => (1 : ComplexAt σ) ⊗ₜ[𝓞 L] x
      map_zero' := TensorProduct.tmul_zero _ _
      map_add' := fun x y => TensorProduct.tmul_add _ _ _ }
  have key := core_span (B.metric.form σ) f (fun r : 𝓞 L => σ (r : L)) (fun r x => one_tmul_smul σ r x) A A' h _ hx _ hx'
  let c : PreInnerProductSpace.Core ℂ (Fibre σ B.carrier) := (B.metric.form σ).toCore
  have ne : ∀ b : 𝓞 L, b ≠ 0 → σ (b : L) ≠ 0 := fun b hb =>
    (map_ne_zero σ).2 (by simpa using hb)
  have e : (B.metric.form σ).inner (f (a • x)) (f (a' • x')) =
      (starRingEnd ℂ) (σ (a : L)) * (σ (a' : L) * (B.metric.form σ).inner (f x) (f x')) := by
    rw [show f (a • x) = σ (a : L) • f x from one_tmul_smul σ a x,
      show f (a' • x') = σ (a' : L) • f x' from one_tmul_smul σ a' x']
    exact (InnerProductSpace.Core.inner_smul_left _ _).trans
      (congrArg _ (InnerProductSpace.Core.inner_smul_right _ _))
  rw [e] at key
  have h1 : (starRingEnd ℂ) (σ (a : L)) ≠ 0 := (map_ne_zero _).2 (ne a ha)
  exact (mul_eq_zero.1 ((mul_eq_zero.1 key).resolve_left h1)).resolve_left (ne a' ha')

end Form

section Eigen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K]
  {J : K → Type} {y : (Σ k, J k) → Ω}

theorem isLieEigen_of_gen (𝔐 : HodgeCpt Y S y) {L : Type} [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ 𝔐.X)
    (hp : genPt 𝔐.ξ ⤳ centre (spMap (algebraMap (𝓞 L) L) ≫ z))
    (g₀ : c.F →+* 𝔐.X.presheaf.stalk (centre (spMap (algebraMap (𝓞 L) L) ≫ z)))
    (hg : (genMap 𝔐.ξ ⟨_, hp⟩).comp g₀ = 𝔐.cst) (s : CMType H ⊕ CMType H) (U : Submodule Ω 𝔐.Li) (hU : U ≤ 𝔐.Vgen s)
    (σ : L →+* ℂ) {V : Type} [AddCommGroup V] [Module (𝓞 L) V] (MB : LieModel 𝔐.t.G z V) (x : V)
    (hx : x ∈ subGens 𝔐.M U z MB)
    (w : epsAt (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) ⟶ 𝔐.t.G)
    (hw : (w.left ≫ (𝟙 𝔐.t.G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt x).left)) :
    IsLieEigen 𝔐.t.act (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z)
      ((σ.comp ((Scheme.stalkClosedPointTo (spMap (algebraMap (𝓞 L) L) ≫ z)).hom.comp g₀)).comp (labelEmb c s)) w := by
  obtain ⟨e, he, v, hval, hl⟩ := hx
  have hσ : spMap σ ≫ spMap (algebraMap (𝓞 L) L) ≫ z = spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z := by
    rw [← Category.assoc]
    exact congrArg (· ≫ z) (spec_comp _ _)
  have hd : GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L)) = (GlobalTheory.CompanionTheory.Ar.dualMap σ).comp (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) := by
    refine RingHom.ext fun a => ?_
    ext <;> simp
  have hw' : w = epsBase σ hσ ≫ v := by
    refine (left_eq_iff σ hσ w v).1 ?_
    have h1 : w.left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt x).left := by
      simpa [LieModel.Lifts] using hw
    have h2 : v.left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt x).left := by
      simpa [LieModel.Lifts] using hl
    rw [h1, h2, hd, ← Category.assoc]
    exact congrArg (· ≫ (MB.pt x).left) (spec_comp _ _).symm
  subst hw'
  refine ⟨isTanAt_base σ hσ hval.isTanAt, fun a => ?_⟩
  have ev := GlobalTheory.CompanionTheory.Ar.FlagFib.valAt_eigen E H D l Xo c Y S Ω K J y 𝔐 L _ hp g₀ hg s e v a (hU he) hval
  have e1 : ((epsBase σ hσ ≫ v) ≫ 𝔐.t.act.act a).left =
      Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap σ)) ≫ (v ≫ 𝔐.t.act.act a).left := rfl
  rw [e1, ev, ← Category.assoc, spec_dual_eps, Category.assoc]
  rfl

end Eigen

theorem orthAt_subFib : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (h : LieMetric 𝔐.M y), h.Orth 𝔐.t.act → ∀ (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ 𝔐.X) (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel 𝔐.t.G z B.carrier), IsFibre (fun z v w c => c = h.ip z v w) z B MB → ∀ (s s' : CMType H ⊕ CMType H), s ≠ s' → ∀ U U' : Submodule Ω 𝔐.Li, U ≤ 𝔐.Vgen s → U' ≤ 𝔐.Vgen s' → OrthAt B (FlagFib.subFib 𝔐.M U z MB) (FlagFib.subFib 𝔐.M U' z MB) := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J y 𝔐 h hO L _ _ z B MB hF s s' hss U U' hU hU' σ x hx x' hx'
  have hp : genPt 𝔐.ξ ⤳ centre (spMap (algebraMap (𝓞 L) L) ≫ z) := 𝔐.all _
  obtain ⟨g₀, hg⟩ := GlobalTheory.CompanionTheory.Ar.Flat.KonstReg.exists_const_stalk E H D l Xo c Y S Ω K J y 𝔐 ⟨_, hp⟩
    (fun n hn => isUnit_natCast_stalk 𝔐.X L _ n hn)
  classical
  let : Fintype (CMType H) := Fintype.ofFinite _
  let ι₀ : c.F →+* ℂ := σ.comp ((Scheme.stalkClosedPointTo (spMap (algebraMap (𝓞 L) L) ≫ z)).hom.comp g₀)
  have hinj := (GlobalTheory.CompanionTheory.Ar.LabelCount.labels_injective_card E H l c ℂ ι₀).1
  have hne : ι₀.comp (labelEmb c s) ≠ ι₀.comp (labelEmb c s') := fun e => hss (hinj e)
  obtain ⟨a, ha, hax⟩ := hx
  obtain ⟨a', ha', hax'⟩ := hx'
  refine orth_sat B σ _ _ ?_ x x' a a' ha ha' hax hax'
  intro u hu u' hu'
  let w := epsBase (σ.comp (algebraMap (𝓞 L) L)) rfl ≫ MB.pt u
  let w' := epsBase (σ.comp (algebraMap (𝓞 L) L)) rfl ≫ MB.pt u'
  have hl : (w.left ≫ (𝟙 𝔐.t.G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt u).left) := Category.comp_id _
  have hl' : (w'.left ≫ (𝟙 𝔐.t.G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt u').left) := Category.comp_id _
  have e1 := isLieEigen_of_gen 𝔐 z hp g₀ hg s U hU σ MB u hu w hl
  have e2 := isLieEigen_of_gen 𝔐 z hp g₀ hg s' U' hU' σ MB u' hu' w' hl'
  exact (hF σ u u' w w' hl hl').trans (hO _ _ _ w w' hne e1 e2)

end GlobalTheory.CompanionTheory.Ar.FlagFib.FibOrth
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.OrthogonalMetricHermitianBundleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonal_metric_hermitian_bundle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (h : LieMetric 𝔐.M y), h.Orth 𝔐.t.act → ∀ (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ 𝔐.X) (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel 𝔐.t.G z B.carrier), IsFibre (fun z v w c => c = h.ip z v w) z B MB → ∀ (s s' : CMType H ⊕ CMType H), s ≠ s' → ∀ U U' : Submodule Ω 𝔐.Li, U ≤ 𝔐.Vgen s → U' ≤ 𝔐.Vgen s' → OrthAt B (FlagFib.subFib 𝔐.M U z MB) (FlagFib.subFib 𝔐.M U' z MB) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagFib.FibOrth.orthAt_subFib | exact GlobalTheory.CompanionTheory.Ar.FlagFib.FibOrth.orthAt_subFib | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagFib.FibOrth.orthAt_subFib <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KillsOverOfAdicCompletion
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SpecialMapFinite
@[reducible] noncomputable def UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.Sp :
    (R : Type) → [CommRing R] → AlgebraicGeometry.Scheme :=
    fun (R : Type) [CommRing R] ↦ AlgebraicGeometry.Spec (CommRingCat.of R)

@[reducible] noncomputable def UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.spMap :
    {R R' : Type} →
      [inst : CommRing R] → [inst_1 : CommRing R'] → (R →+* R') → (UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.Sp R' ⟶ UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.Sp R) :=
    fun {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') ↦ AlgebraicGeometry.Spec.map (CommRingCat.ofHom f)

theorem UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.main :
    ∀ {A : Type} [inst : CommRing A] {Y Z : AlgebraicGeometry.Scheme} {f g : UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.Sp A ⟶ Y} (s : Y ⟶ Z)
      [AlgebraicGeometry.IsSeparated s],
      CategoryTheory.CategoryStruct.comp f s = CategoryTheory.CategoryStruct.comp g s →
        ∀ {N : Type} (I : N → Ideal A),
          (∀ (x : A), (∀ (n : N), x ∈ I n) → x = (0 : A)) →
            (∀ (n : N),
                CategoryTheory.CategoryStruct.comp (UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.spMap (Ideal.Quotient.mk (I n))) f =
                  CategoryTheory.CategoryStruct.comp (UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.spMap (Ideal.Quotient.mk (I n))) g) →
              f = g := by
  open AlgebraicGeometry CategoryTheory CategoryTheory.Limits in
  intro A _ Y Z f g s _ h N I hI hn
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g h.symm
  have : IsSeparated Y'.hom := ‹_›
  have : IsAffine X'.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))
  have hcl : IsClosedImmersion (equalizer.ι f' g').left := inferInstance
  obtain ⟨haff, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine (equalizer.ι f' g').left
  have hfac : ∀ n, ∃ l : UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.Sp (A ⧸ I n) ⟶ (equalizer f' g').left,
      l ≫ (equalizer.ι f' g').left = UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.spMap (Ideal.Quotient.mk (I n)) := by
    intro n
    let T' : Over Z := Over.mk (UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.spMap (Ideal.Quotient.mk (I n)) ≫ f ≫ s)
    let ι' : T' ⟶ X' := Over.homMk (UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.spMap (Ideal.Quotient.mk (I n)))
    have hc : ι' ≫ f' = ι' ≫ g' := by
      ext1
      exact hn n
    refine ⟨(equalizer.lift ι' hc).left, ?_⟩
    rw [← Over.comp_left, equalizer.lift_ι]
    rfl
  have hinj : Function.Injective (equalizer.ι f' g').left.appTop := by
    refine (injective_iff_map_eq_zero (equalizer.ι f' g').left.appTop.hom).mpr fun y hy ↦ ?_
    obtain ⟨a, rfl⟩ : ∃ a, (Scheme.ΓSpecIso (CommRingCat.of A)).inv a = y :=
      ⟨(Scheme.ΓSpecIso (CommRingCat.of A)).hom y, by simp⟩
    have ha : a = 0 := by
      refine hI a fun n ↦ ?_
      obtain ⟨l, hl⟩ := hfac n
      have h1 : (UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.spMap (Ideal.Quotient.mk (I n))).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) = 0 := by
        rw [← hl, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
        erw [hy]
        exact map_zero _
      have h2 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (I n)))
      have h3 : (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ I n))).inv (Ideal.Quotient.mk (I n) a) = 0 := by
        have h4 := congr($h2 a)
        simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom] at h4
        exact h4.trans h1
      have h5 := congr((Scheme.ΓSpecIso (CommRingCat.of (A ⧸ I n))).hom $h3)
      simp only [map_zero] at h5
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simpa using h5
    simp [ha]
  have hiso : IsIso (equalizer.ι f' g').left.appTop := by
    exact (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj, hsurj⟩
  have hE : IsIso (equalizer.ι f' g').left :=
    (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme)
      (arrowIsoSpecΓOfIsAffine (equalizer.ι f' g').left)).mpr
      (inferInstanceAs (IsIso (Spec.map (equalizer.ι f' g').left.appTop)))
  rw [← cancel_epi (equalizer.ι f' g').left]
  exact congr($(equalizer.condition f' g').left)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EqZeroOfMemMapPow
open Matrix Filter Topology
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.KrullGroupAlg

theorem coeff_mem_of_mem_map {R M : Type} [CommRing R] [AddCommGroup M] (I : Ideal R)
    (x : AddMonoidAlgebra R M) (hx : x ∈ Ideal.map (algebraMap R (AddMonoidAlgebra R M)) I)
    (φ : AddMonoidAlgebra R M →ₗ[R] R) : φ x ∈ I := by
  have hx' : x ∈ Submodule.span (AddMonoidAlgebra R M) (algebraMap R (AddMonoidAlgebra R M) '' I) := hx
  clear hx
  revert φ
  induction hx' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, rfl⟩ := hy
    intro φ
    rw [Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul]
    exact I.mul_mem_right _ ha
  | zero =>
    intro φ
    rw [map_zero]
    exact I.zero_mem
  | add y z _ _ hy hz =>
    intro φ
    rw [map_add (f := _)]
    exact I.add_mem (hy φ) (hz φ)
  | smul r y _ hy =>
    intro φ
    have := hy (φ ∘ₗ LinearMap.mulLeft R r)
    simpa [smul_eq_mul] using this

theorem eq_zero_of_mem_map_pow : ∀ (R M : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup M] (x : AddMonoidAlgebra R M), (∀ n : ℕ, x ∈ Ideal.map (algebraMap R (AddMonoidAlgebra R M)) (IsLocalRing.maximalIdeal R ^ n)) → x = 0 := by
  intro R M _ _ _ _ x hx
  ext m
  have hm : (Finsupp.lapply m ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap) x ∈ ⨅ n : ℕ, IsLocalRing.maximalIdeal R ^ n :=
    Ideal.mem_iInf.2 fun n =>
      coeff_mem_of_mem_map _ x (hx n) (Finsupp.lapply m ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap)
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal R).ne_top,
    Ideal.mem_bot] at hm
  simpa using hm

end GlobalTheory.CompanionTheory.KrullGroupAlg
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KillsOverOfAdicCompletion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.KillsAdic

theorem ext_of_quotients {A : Type} [CommRing A] {Y Z : Scheme.{0}} {f g : Sp A ⟶ Y} (s : Y ⟶ Z) [IsSeparated s]
    (h : f ≫ s = g ≫ s) {N : Type} (I : N → Ideal A) (hI : ∀ x : A, (∀ n, x ∈ I n) → x = 0)
    (hU : ∀ n, spMap (Ideal.Quotient.mk (I n)) ≫ f = spMap (Ideal.Quotient.mk (I n)) ≫ g) : f = g :=
  _root_.UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.main s h I hI hU

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem charVal_comp {A A' : Type} [CommRing A] [CommRing A'] {a : Sp A ⟶ S} {a' : Sp A' ⟶ S} (h : A →+* A')
    (e : spMap h ≫ a = a') (t : Over.mk a ⟶ splitTorus S X) (χ : X) :
    charVal ((Over.homMk (spMap h) e : Over.mk a' ⟶ Over.mk a) ≫ t) χ = h (charVal t χ) := by
  subst e
  exact (GlobalTheory.T.charVal_multiplicative S X A a).2.2.2.2.2 A' h t _ (by simp) χ

theorem exists_factor {M : Type} [CommMonoid M] (Y : AddSubgroup X) (f : X → M) (h0 : f 0 = 1)
    (hadd : ∀ x y, f (x + y) = f x * f y) (hY : ∀ y ∈ Y, f y = 1) :
    ∃ v : Multiplicative (X ⧸ Y) →* M, ∀ χ : X, v (Multiplicative.ofAdd (χ : X ⧸ Y)) = f χ := by
  have key : ∀ x x' : X, (x : X ⧸ Y) = x' → f x = f x' := by
    intro x x' e
    have hm : -x + x' ∈ Y := QuotientAddGroup.eq.1 e
    have : x' = x + (-x + x') := by abel
    rw [this, hadd, hY _ hm, _root_.mul_one]
  refine ⟨{ toFun := fun q => f (Quotient.out (Multiplicative.toAdd q))
            map_one' := ?_
            map_mul' := ?_ }, fun χ => ?_⟩
  · rw [← h0]
    exact key _ _ (by simp)
  · intro p q
    rw [← hadd]
    exact key _ _ (by simp)
  · exact key _ _ (by simp)

theorem comp_one_over {T T' M : Over S} [GrpObj M] (f : T' ⟶ T) : f ≫ (1 : T ⟶ M) = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (f ≫ toUnit T) (toUnit T')]

theorem universal_one {G : Over S} [GrpObj G] [IsSeparated G.hom] (u : splitTorus S X ⟶ G) (Y : AddSubgroup X)
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (b : Sp R ⟶ S)
    (hk : ∀ n : ℕ, KillsOver u Y (spMap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))) ≫ b))
    (t₀ : Over.mk (spMap (algebraMap R (AddMonoidAlgebra R (X ⧸ Y))) ≫ b) ⟶ splitTorus S X)
    (ht₀ : ∀ χ : X, charVal t₀ χ = AddMonoidAlgebra.single (χ : X ⧸ Y) 1) : t₀ ≫ u = 1 := by
  let c := algebraMap R (AddMonoidAlgebra R (X ⧸ Y))
  let I : ℕ → Ideal (AddMonoidAlgebra R (X ⧸ Y)) := fun n =>
    Ideal.map c (IsLocalRing.maximalIdeal R ^ (n + 1))
  have hI : ∀ x, (∀ n, x ∈ I n) → x = 0 := fun x hx =>
    GlobalTheory.CompanionTheory.KrullGroupAlg.eq_zero_of_mem_map_pow R (X ⧸ Y) x fun n =>
      Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ n)) (hx n)
  refine Over.OverMorphism.ext (ext_of_quotients G.hom ?_ I hI fun n => ?_)
  · rw [Over.w, Over.w]
  · let J := IsLocalRing.maximalIdeal R ^ (n + 1)
    let gn : R ⧸ J →+* AddMonoidAlgebra R (X ⧸ Y) ⧸ I n :=
      Ideal.quotientMap (I n) c Ideal.le_comap_map
    have e : spMap (Ideal.Quotient.mk (I n)) ≫ spMap c ≫ b = spMap gn ≫ spMap (Ideal.Quotient.mk J) ≫ b := by
      rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
      rfl
    let m : Over.mk (spMap gn ≫ spMap (Ideal.Quotient.mk J) ≫ b) ⟶ Over.mk (spMap c ≫ b) :=
      Over.homMk (spMap (Ideal.Quotient.mk (I n))) e
    have hone := hk n _ gn (m ≫ t₀) (fun y hy => by
      rw [charVal_comp, ht₀, (QuotientAddGroup.eq_zero_iff y).2 hy]
      exact map_one _)
    have h4 : m ≫ (t₀ ≫ u) = m ≫ (1 : Over.mk (spMap c ≫ b) ⟶ G) := by
      exact (Category.assoc m t₀ u).symm.trans (hone.trans (comp_one_over m).symm)
    exact congrArg (fun w => w.left) h4

theorem killsOver_of_forall_pow : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsSeparated G.hom] (X : Type) [AddCommGroup X] (u : splitTorus S X ⟶ G) (Y : AddSubgroup X) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (b : Sp R ⟶ S), (∀ n : ℕ, KillsOver u Y (spMap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))) ≫ b)) → KillsOver u Y b := by
  intro S G _ _ X _ u Y R _ _ _ b hk A _ g t ht
  let c := algebraMap R (AddMonoidAlgebra R (X ⧸ Y))
  let w₀ : Multiplicative X →* AddMonoidAlgebra R (X ⧸ Y) :=
    (AddMonoidAlgebra.of R (X ⧸ Y)).comp (AddMonoidHom.toMultiplicative (QuotientAddGroup.mk' Y))
  obtain ⟨t₀, ht₀⟩ := (GlobalTheory.T.charVal_multiplicative S X _ (spMap c ≫ b)).2.2.2.2.1 w₀
  have ht₀' : ∀ χ : X, charVal t₀ χ = AddMonoidAlgebra.single (χ : X ⧸ Y) 1 := fun χ => ht₀ χ
  have hone := universal_one u Y b hk t₀ ht₀'
  have hpts := (GlobalTheory.T.charVal_multiplicative S X A (spMap g ≫ b))
  obtain ⟨v, hv⟩ := exists_factor Y (charVal t) (hpts.2.2.2.1 t).1 (hpts.2.2.2.1 t).2 ht
  let h : AddMonoidAlgebra R (X ⧸ Y) →+* A :=
    AddMonoidAlgebra.liftNCRingHom g v (fun _ _ => Commute.all _ _)
  have hc : h.comp c = g := by
    ext r
    simp [h, c]
  have e : spMap h ≫ spMap c ≫ b = spMap g ≫ b := by
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hc]
  let m : Over.mk (spMap g ≫ b) ⟶ Over.mk (spMap c ≫ b) := Over.homMk (spMap h) e
  have htm : t = m ≫ t₀ := hpts.1 _ _ fun χ => by
    rw [charVal_comp, ht₀']
    simp [h, AddMonoidAlgebra.liftNCRingHom_single, hv]
  rw [htm, Category.assoc, hone, comp_one_over]

end GlobalTheory.CompanionTheory.Ar.KillsAdic
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KillsOverOfAdicCompletionStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.killsOver_of_adic_completion : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsSeparated G.hom] (X : Type) [AddCommGroup X] (u : splitTorus S X ⟶ G) (Y : AddSubgroup X) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (b : Sp R ⟶ S), (∀ n : ℕ, KillsOver u Y (spMap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))) ≫ b)) → KillsOver u Y b := by
  first | exact @GlobalTheory.CompanionTheory.Ar.KillsAdic.killsOver_of_forall_pow | exact GlobalTheory.CompanionTheory.Ar.KillsAdic.killsOver_of_forall_pow | (intros; apply GlobalTheory.CompanionTheory.Ar.KillsAdic.killsOver_of_forall_pow <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelBaseChangeSpan
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelBaseChangeSpan
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.LieSpan

theorem span_range_pullback : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom] (R R' : Type) [CommRing R] [CommRing R'] (c : R →+* R') (x : Spec (CommRingCat.of R) ⟶ S) (E E' : Type) [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R' E'] (M : LieModel G x E) (M' : LieModel G (Spec.map (CommRingCat.ofHom c) ≫ x) E') (j : E → E'), (∀ e, (M'.pt (j e)).left = Spec.map (CommRingCat.ofHom (dualMap c)) ≫ (M.pt e).left) → Submodule.span R' (Set.range j) = ⊤ := by
  intro S G _ _ R R' _ _ c x E E' _ _ _ _ M M' j hj
  letI : Algebra R R' := c.toAlgebra
  letI : Module R E' := Module.compHom E' c
  haveI : IsScalarTower R R' E' :=
    ⟨fun r r' e => by
      show (c r * r') • e = c r • (r' • e)
      exact mul_smul _ _ _⟩
  let h : GlobalTheory.CompanionTheory.Ar.epsAt (Spec.map (CommRingCat.ofHom c) ≫ x) ⟶ GlobalTheory.CompanionTheory.Ar.epsAt x :=
    Over.homMk (Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap c))) (by
      show Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap c)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x =
        Spec.map (CommRingCat.ofHom (algebraMap R' (DualNumber R'))) ≫
          Spec.map (CommRingCat.ofHom c) ≫ x
      rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
      congr 2
      ext r <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl, CommRingCat.hom_comp,
        CommRingCat.hom_ofHom])
  have hl : h.left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap c)) := rfl
  have hpt : ∀ e, M'.pt (j e) = h ≫ M.pt e := fun e =>
    Over.OverMorphism.ext (by rw [Over.comp_left, hl]; exact hj e)
  have hadd : ∀ a b, j (a + b) = j a + j b := by
    intro a b
    apply M'.inj
    rw [M'.add, hpt, hpt, hpt, M.add, MonObj.comp_mul]
  have hsmul : ∀ (r : R) (e : E), j (r • e) = c r • j e := by
    intro r e
    apply M'.inj
    apply Over.OverMorphism.ext
    rw [M'.smul, hpt, hpt, Over.comp_left, Over.comp_left, M.smul, hl,
      ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 2
    ext a <;>
      simp [GlobalTheory.CompanionTheory.Ar.dualMap, GlobalTheory.CompanionTheory.Ar.epsMul, smul_eq_mul, TrivSqZeroExt.algebraMap_eq_inl, CommRingCat.hom_comp,
        CommRingCat.hom_ofHom]
  let β : E →ₗ[R] E' :=
    { toFun := j, map_add' := hadd, map_smul' := fun r e => hsmul r e }
  obtain ⟨-, -, hbc⟩ := GlobalTheory.CompanionTheory.Ar.LieProj.lie_finite_projective_baseChange S G R x E M
  have hb : IsBaseChange R' β := hbc R' E' M' β (fun e => hj e)
  rw [eq_top_iff]
  rintro y -
  obtain ⟨t, rfl⟩ := hb.equiv.surjective y
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul s e =>
    rw [hb.equiv_tmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e, rfl⟩)
  | add a b ha hb' =>
    rw [map_add (f := _)]
    exact Submodule.add_mem _ ha hb'

end GlobalTheory.CompanionTheory.Ar.LieSpan
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelBaseChangeSpanStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_base_change_span : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom] (R R' : Type) [CommRing R] [CommRing R'] (c : R →+* R') (x : Spec (CommRingCat.of R) ⟶ S) (E E' : Type) [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R' E'] (M : LieModel G x E) (M' : LieModel G (Spec.map (CommRingCat.ofHom c) ≫ x) E') (j : E → E'), (∀ e, (M'.pt (j e)).left = Spec.map (CommRingCat.ofHom (dualMap c)) ≫ (M.pt e).left) → Submodule.span R' (Set.range j) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieSpan.span_range_pullback | exact GlobalTheory.CompanionTheory.Ar.LieSpan.span_range_pullback | (intros; apply GlobalTheory.CompanionTheory.Ar.LieSpan.span_range_pullback <;> assumption)
end
end
