module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryFourierSystemTraitsChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermSystemFourOfGaloisClassSums
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermSystemIndexZeroCoefficientApprox
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedBlowupFiniteNormalCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkElementsApproxLeadingTermQuotients
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartDescendsOfThetaTermsRatios
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTermCoefficientSqEqMonomialSubfield
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareApproxValuesAtPointOfElements
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSupportingTupleSmoothConeCmField

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryFourierSystemTraitsFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryFourierSystemTraitsFamily
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep

namespace GlobalTheory.USep


set_option maxHeartbeats 1000000 in
theorem exists_system_with_traits_and_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (φ : InvFun (𝓞 E)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Cm : GlobalTheory.UChart.MonoFam Xo c φ V), GlobalTheory.Mum.Base V → ∀ ξ : Sp V ⟶ pullback C.z (spMap C.b), Cm.y ≫ C.iF = jK V ≫ ξ → ∀ n : ℕ, n.Prime → Odd n → ∀ j₀ : ℕ, ∃ (j : ℕ) (M : Scheme.{0}) (_ : IsIntegral M) (g : M ⟶ C.Z) (z₁ : M) (ζ : Sp (M.presheaf.stalk z₁) ⟶ pullback C.z (spMap C.b)) (Φ : VSys (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) !![(1 : ℤ)] ((n ^ j) ^ 2) (M.presheaf.stalk z₁)) (y : Φ.Y) (ρ : V →+* Φ.V y) (e : Φ.X y ≃ₗ[𝓞 E] Cm.P.D.toPre.X) (h : Fin (Φ.m y) ≃ Fin Cm.m) (U : M.Opens), (U : Set M).Nonempty ∧ j₀ ≤ j ∧ IsCov C g z₁ ζ ∧ GlobalTheory.GSep.HasTraitsOn ζ Φ.pre U ∧ IsMember ζ Φ Cm ξ y ρ e h := by
  intro E _ _ _ H Dw hpq l Xo c C φ V _ _ _ Cm hV ξ hξ n hn hodd j₀
  obtain ⟨j, X₁, π, z₁, ζ, hdom, U, Φ, y, ρ, e, h, c₀, hj, hcov, hU, hT, hM, hunit, hm1, hE, hCS⟩ :=
    GlobalTheory.T.exists_unitary_fourier_system_traits_chart E H Dw hpq l Xo c C φ V Cm hV ξ hξ n hn hodd (max j₀ 1)
  obtain ⟨-, -, hIC, -⟩ := GlobalTheory.T.modelStalk_normal_noetherian_fractionRing X₁ z₁
  have hj1 : 1 ≤ j := le_trans (le_max_right _ _) hj
  have hN : 3 ≤ (n ^ j) ^ 2 := by
    have h3 : 3 ≤ n := by
      rcases hodd with ⟨k, hk⟩
      have := hn.two_le
      omega
    have h2 : 3 ≤ n ^ j := le_trans h3 (Nat.le_self_pow (by omega) n)
    nlinarith
  have hLam : Φ.abelian₂ := GlobalTheory.T.fourierTermSystem_lam_of_exact_class_sums (𝓞 E) _ _ 1 _ _ Φ ((n ^ j) ^ 2) (by norm_num) hN hE
  have hFour : Φ.Four ((n ^ j) ^ 2) := GlobalTheory.T.fourierTermSystem_four_of_galois_class_sums (𝓞 E) _ _ 1 _ _ Φ ((n ^ j) ^ 2) hCS
  let v : ∀ y', (Φ.V y')ˣ := fun y' => (hunit y').unit⁻¹
  have happ : ∀ e' : ℕ, ∃ a : X₁.M.Z.presheaf.stalk z₁, ∀ y', Φ.ev y' a - ((v y')⁻¹ : (Φ.V y')ˣ) ∈
      (maximalIdeal (X₁.M.Z.presheaf.stalk z₁) ^ e').map (Φ.ev y') := by
    intro e'
    obtain ⟨a, ha⟩ := GlobalTheory.T.fourierTermSystem_indexZero_coefficient_approx (𝓞 E) _ _ 1 _ _ Φ ((n ^ j) ^ 2) hN hE hLam hFour
      (fun y₁ y₂ h₁ h₂ => (hm1 y₁ h₁).trans (hm1 y₂ h₂).symm) c₀ e'
    refine ⟨a, fun y' => ?_⟩
    simpa [v] using ha y'
  have hFour' : (Φ.rescale v).Four ((n ^ j) ^ 2) := GlobalTheory.T.fourierTermSystem_four_rescale_approximated_units (𝓞 E) _ _ 1 _ _ Φ ((n ^ j) ^ 2) hFour v happ
  have hLam' : (Φ.rescale v).abelian₂ := hLam
  refine ⟨j, X₁.M.Z, inferInstance, π, z₁, ζ, (Φ.rescale v).toVSys ((n ^ j) ^ 2) hLam' hFour', y, ρ, e, h, U, hU,
    le_trans (le_max_left _ _) hj, hcov, hT, ?_⟩
  obtain ⟨h1, h2, h3, h4, D, p, hT0⟩ := hM
  refine ⟨h1, h2, h3, h4, D, p, ?_⟩
  have h0 : Φ.term y (fun _ => e.symm 0) c₀ * ((v y : (Φ.V y)ˣ) : Φ.V y) = 1 := by
    have hz : (fun _ : Fin 1 => e.symm 0) = 0 := by
      funext a; simp
    rw [hz]
    simp [VPre.term, mono, qW, v]
  have := GlobalTheory.T.isThetaTerms_of_mul_index_zero_term_eq_one (Φ.V y) D ((n ^ j) ^ 2) _ Φ.Q p.xe.symm
    (fun mu c => Φ.term y (fun _ => e.symm mu) c) (v y) c₀ hT0 h0
  refine cast (congrArg (fun T => GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) p.xe.symm T) ?_) this
  funext mu c
  show Φ.u y (fun _ => e.symm mu) c * mono !![(1 : ℤ)] (Φ.t y) (Φ.δ y) (fun _ => e.symm mu) * ((v y : (Φ.V y)ˣ) : Φ.V y) =
    Φ.u y (fun _ => e.symm mu) c * ((v y : (Φ.V y)ˣ) : Φ.V y) * mono !![(1 : ℤ)] (Φ.t y) (Φ.δ y) (fun _ => e.symm mu)
  exact mul_right_comm _ _ _

end GlobalTheory.USep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryFourierSystemTraitsFamilyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_fourier_system_traits_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (φ : InvFun (𝓞 E)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Cm : GlobalTheory.UChart.MonoFam Xo c φ V), GlobalTheory.Mum.Base V → ∀ ξ : Sp V ⟶ pullback C.z (spMap C.b), Cm.y ≫ C.iF = jK V ≫ ξ → ∀ n : ℕ, n.Prime → Odd n → ∀ j₀ : ℕ, ∃ (j : ℕ) (M : Scheme.{0}) (_ : IsIntegral M) (g : M ⟶ C.Z) (z₁ : M) (ζ : Sp (M.presheaf.stalk z₁) ⟶ pullback C.z (spMap C.b)) (Φ : VSys (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) !![(1 : ℤ)] ((n ^ j) ^ 2) (M.presheaf.stalk z₁)) (y : Φ.Y) (ρ : V →+* Φ.V y) (e : Φ.X y ≃ₗ[𝓞 E] Cm.P.D.toPre.X) (h : Fin (Φ.m y) ≃ Fin Cm.m) (U : M.Opens), (U : Set M).Nonempty ∧ j₀ ≤ j ∧ IsCov C g z₁ ζ ∧ GlobalTheory.GSep.HasTraitsOn ζ Φ.pre U ∧ IsMember ζ Φ Cm ξ y ρ e h := by
  first | exact @GlobalTheory.USep.exists_system_with_traits_and_family | exact GlobalTheory.USep.exists_system_with_traits_and_family | (intros; apply GlobalTheory.USep.exists_system_with_traits_and_family <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApproximatingElementsNormalCoverUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSystemOfOrderGeAlongTraits
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMapEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

namespace GlobalTheory.USepTrait

theorem sp_comp {R S U : Type} [CommRing R] [CommRing S] [CommRing U] (f : R →+* S) (g : S →+* U) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem comap_map_eq {R S : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing S] [IsDomain S]
    [IsLocalRing S] (f : R →+* S) (hf : Function.Injective f) [IsLocalHom f] (I : Ideal R) :
    (I.map f).comap f = I := by
  letI := f.toAlgebra
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective _ _).2 hf
  have : IsLocalHom (algebraMap R S) := ‹IsLocalHom f›
  have : Module.Flat R S := inferInstance
  have : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact Ideal.comap_map_eq_self_of_faithfullyFlat (B := S) I

end GlobalTheory.USepTrait
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSystemOfOrderGeAlongTraits
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep
open GlobalTheory

noncomputable section

namespace GlobalTheory.USepStrait

theorem range_jK_spMap_subset_of_injective (V R : Type) [CommRing V] [IsDomain V] [CommRing R] [IsDomain R] (ρ : V →+* R)
    (hρ : Function.Injective ρ) (X : Scheme.{0}) (χ : Sp V ⟶ X) : Set.range (jK R ≫ spMap ρ ≫ χ) ⊆ Set.range (jK V ≫ χ) := by
  intro x ⟨p, hp⟩
  let q : Sp (FractionRing V) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V))
  have key : (spMap ρ) ((jK R) p) = (jK V) q := by
    apply PrimeSpectrum.ext
    change Ideal.comap ρ (Ideal.comap (algebraMap R (FractionRing R)) p.asIdeal) =
      Ideal.comap (algebraMap V (FractionRing V)) ⊥
    haveI : p.asIdeal.IsPrime := PrimeSpectrum.isPrime p
    rw [Ideal.eq_bot_of_prime p.asIdeal, Ideal.comap_comap,
      Ideal.comap_bot_of_injective _ (IsFractionRing.injective V (FractionRing V)),
      Ideal.comap_bot_of_injective _ (by rw [RingHom.coe_comp]; exact (IsFractionRing.injective R (FractionRing R)).comp hρ)]
  refine ⟨q, ?_⟩
  rw [← hp]
  change χ ((jK V) q) = χ ((spMap ρ) ((jK R) p))
  rw [key]

theorem mem_of_ordGe_on : UTraitExtSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (φ : InvFun (𝓞 E)) (d : ℕ) (J : C.Z.IdealSheafData), UValOn Xo c C.i φ J d → ∀ (M : Scheme.{0}) (z₁ : M) (U : M.Opens) (ζ : Sp (M.presheaf.stalk z₁) ⟶ pullback C.z (spMap C.b)) (N₁ : ℕ) (Φ : VSys (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) !![(1 : ℤ)] N₁ (M.presheaf.stalk z₁)), GlobalTheory.GSep.HasTraitsOn ζ Φ.pre U → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (ev' : M.presheaf.stalk z₁ →+* V), IsLocalHom ev' → Set.range (jK V ≫ spMap ev' ≫ M.fromSpecStalk z₁) ⊆ (U : Set M) → ∀ y' : Sp (FractionRing V) ⟶ Xo.XF c, y' ≫ C.iF = spMap ((algebraMap V (FractionRing V)).comp ev') ≫ ζ → ∀ (D e : ℕ) (f : M.presheaf.stalk z₁), Φ.OrdGe φ (D * (2 * d)) e f → ev' f ∈ idlAlong J (spMap ev' ≫ ζ ≫ pullback.fst C.z (spMap C.b)) ^ D ⊔ ((maximalIdeal (M.presheaf.stalk z₁)).map ev') ^ e := by
  intro hExt E _ _ _ H Dw l Xo c C φ d J hval M z₁ U ζ N₁ Φ hT V _ _ _ _ hV ev' hev' hU y' hy' D e f hf
  have hB : GlobalTheory.Mum.Base V := ⟨⟨inferInstance, inferInstance, inferInstance, hV⟩, inferInstance⟩
  obtain ⟨T, fx, fK, hfi, hfl, -, hfK, hTy⟩ := hExt E H Dw l Xo c V hB inferInstance y'
  haveI : IsDiscreteValuationRing T.V := T.cdvr.1
  let evT := fx.comp ev'
  haveI : IsLocalHom evT := RingHom.isLocalHom_comp fx ev'
  have hring : (algebraMap T.V (FractionRing T.V)).comp evT = fK.comp ((algebraMap V (FractionRing V)).comp ev') :=
    RingHom.ext fun a => (hfK (ev' a)).symm
  have hsq : jK T.V ≫ spMap evT ≫ ζ = T.y ≫ C.iF := by
    rw [hTy, Category.assoc, hy', ← Category.assoc, GlobalTheory.USepTrait.sp_comp, ← Category.assoc, GlobalTheory.USepTrait.sp_comp, hring]
  have hrange : Set.range (jK T.V ≫ spMap evT ≫ M.fromSpecStalk z₁) ⊆ (U : Set M) := by
    have e1 : jK T.V ≫ spMap evT ≫ M.fromSpecStalk z₁ = jK T.V ≫ spMap fx ≫ spMap ev' ≫ M.fromSpecStalk z₁ := by
      rw [← GlobalTheory.USepTrait.sp_comp ev' fx, Category.assoc]
    rw [e1]
    exact (range_jK_spMap_subset_of_injective V T.V fx hfi M (spMap ev' ≫ M.fromSpecStalk z₁)).trans
      (by simpa only [Category.assoc] using hU)
  have hT' := hT T evT inferInstance hsq hrange
  change ∃ (y : Φ.Y) (f : T.V →+* Φ.V y) (e : Φ.X y ≃ₗ[𝓞 E] T.P.D.toPre.X), Φ.m y = 1 ∧ IsPrincipalIdealRing (Φ.V y) ∧
      Function.Injective f ∧ IsLocalHom f ∧ f.comp evT = Φ.ev y ∧
      ∀ k, Φ.t y k ^ 2 = f T.ϖ ∧ ∀ a b, Φ.δ y k a b = T.be (e a) (e b) at hT'
  obtain ⟨y2, f₂, eq, hm, hP, hf₂i, hf₂l, hf₂c, ht⟩ := hT'
  obtain ⟨tK, m1, m2⟩ := T.gen
  have hyχ : T.y ≫ C.i = jK T.V ≫ (spMap evT ≫ ζ ≫ pullback.fst C.z (spMap C.b)) := by
    show T.y ≫ C.iF ≫ pullback.fst _ _ = _
    rw [← Category.assoc, ← hsq]
    simp only [Category.assoc]
  obtain ⟨n, hn, hid⟩ := hval T.V T.cdvr T.ϖ T.irr _ T.y hyχ T.t tK m1 m2 T.P T.be T.lev T.mono
  have hid' : (idlAlong J (spMap ev' ≫ ζ ≫ pullback.fst C.z (spMap C.b))).map fx = Ideal.span {T.ϖ ^ n} := by
    rw [← GlobalTheory.TraitOrder.idlAlong_comp, ← hid, ← Category.assoc, GlobalTheory.USepTrait.sp_comp]
  have hm0 : 0 < Φ.m y2 := by omega
  let k : Fin (Φ.m y2) := ⟨0, hm0⟩
  have hδ : Φ.δ y2 k = pull eq.toLinearMap T.be := LinearMap.ext₂ fun a b => (ht k).2 a b
  have hev : φ.evalZ (Φ.δ y2 k) = φ.evalZ T.be := by
    rw [hδ]; exact evalZ_pull φ eq.surjective T.be
  have hb : ((D * (2 * n) : ℕ) : ℝ) = ((D * (2 * d) : ℕ) : ℝ) * φ.evalZ (Φ.δ y2 k) := by
    rw [hev]; push_cast; rw [hn]; ring
  have hmem := hf.mem y2 hP hm k (D * (2 * n)) hb
  have htp : Φ.t y2 k ^ (D * (2 * n)) = f₂ (T.ϖ ^ (n * D)) := by
    rw [show D * (2 * n) = 2 * (n * D) by ring, pow_mul, (ht k).1, map_pow]
  haveI := hf₂l
  have hK : (Ideal.span {T.ϖ ^ (n * D)} ⊔ ((maximalIdeal (M.presheaf.stalk z₁)).map evT) ^ e).map f₂ =
      Ideal.span {Φ.t y2 k ^ (D * (2 * n))} ⊔ ((maximalIdeal (M.presheaf.stalk z₁)).map (Φ.ev y2)) ^ e := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, Ideal.map_pow, Ideal.map_map, hf₂c, htp]
  have h1 : evT f ∈ Ideal.span {T.ϖ ^ (n * D)} ⊔ ((maximalIdeal (M.presheaf.stalk z₁)).map evT) ^ e := by
    rw [← GlobalTheory.USepTrait.comap_map_eq f₂ hf₂i (Ideal.span {T.ϖ ^ (n * D)} ⊔ ((maximalIdeal (M.presheaf.stalk z₁)).map evT) ^ e)]
    rw [Ideal.mem_comap]
    rw [hK, ← RingHom.comp_apply, hf₂c]
    exact hmem
  haveI := hfl
  have hK' : ((idlAlong J (spMap ev' ≫ ζ ≫ pullback.fst C.z (spMap C.b))) ^ D ⊔
      ((maximalIdeal (M.presheaf.stalk z₁)).map ev') ^ e).map fx =
      Ideal.span {T.ϖ ^ (n * D)} ⊔ ((maximalIdeal (M.presheaf.stalk z₁)).map evT) ^ e := by
    rw [Ideal.map_sup, Ideal.map_pow, hid', Ideal.span_singleton_pow, ← pow_mul, Ideal.map_pow, Ideal.map_map]
  rw [← GlobalTheory.USepTrait.comap_map_eq fx hfi (_ ^ D ⊔ _), hK']
  exact h1

end GlobalTheory.USepStrait
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSystemOfOrderGeAlongTraitsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_system_of_order_ge_along_traits : UTraitExtSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (φ : InvFun (𝓞 E)) (d : ℕ) (J : C.Z.IdealSheafData), UValOn Xo c C.i φ J d → ∀ (M : Scheme.{0}) (z₁ : M) (U : M.Opens) (ζ : Sp (M.presheaf.stalk z₁) ⟶ pullback C.z (spMap C.b)) (N₁ : ℕ) (Φ : VSys (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) !![(1 : ℤ)] N₁ (M.presheaf.stalk z₁)), GlobalTheory.GSep.HasTraitsOn ζ Φ.pre U → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (ev' : M.presheaf.stalk z₁ →+* V), IsLocalHom ev' → Set.range (jK V ≫ spMap ev' ≫ M.fromSpecStalk z₁) ⊆ (U : Set M) → ∀ y' : Sp (FractionRing V) ⟶ Xo.XF c, y' ≫ C.iF = spMap ((algebraMap V (FractionRing V)).comp ev') ≫ ζ → ∀ (D e : ℕ) (f : M.presheaf.stalk z₁), Φ.OrdGe φ (D * (2 * d)) e f → ev' f ∈ idlAlong J (spMap ev' ≫ ζ ≫ pullback.fst C.z (spMap C.b)) ^ D ⊔ ((maximalIdeal (M.presheaf.stalk z₁)).map ev') ^ e := by
  first | exact @GlobalTheory.USepStrait.mem_of_ordGe_on | exact GlobalTheory.USepStrait.mem_of_ordGe_on | (intros; apply GlobalTheory.USepStrait.mem_of_ordGe_on <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkValueClosedPointDefinedOverSubfield
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkValueClosedPointDefinedOverSubfield
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

namespace GlobalTheory.USep

theorem stalkClosedPointTo_comp_stalkMap_spec (X : Scheme.{0}) {R W : Type} [CommRing R] [IsLocalRing R]
    [CommRing W] [IsLocalRing W] (ξ : Sp R ⟶ X) (g : R →+* W)
    (hs : (spMap g ≫ ξ) (closedPoint W) ⤳ ξ (closedPoint R)) (a : X.presheaf.stalk (ξ (closedPoint R))) :
    (Scheme.stalkClosedPointTo (spMap g ≫ ξ)).hom ((X.presheaf.stalkSpecializes hs).hom a) =
      g ((Scheme.stalkClosedPointTo ξ).hom a) := by
  have key : X.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo (spMap g ≫ ξ) =
      Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom g := by
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk (ξ (closedPoint R))), Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.Spec_stalkClosedPointTo_fromSpecStalk,
      Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  exact congrArg (fun q => q.hom a) key

theorem bijective_stalkSpecializes_of_eq {X : Scheme.{0}} {x y : X} (h : x ⤳ y) (e : x = y) :
    Function.Bijective (X.presheaf.stalkSpecializes h).hom := by
  subst e
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  exact Function.bijective_id

theorem isLocalHom_stalkSpecializes_of_eq {X : Scheme.{0}} {x y : X} (h : x ⤳ y) (e : x = y) :
    IsLocalHom (X.presheaf.stalkSpecializes h).hom := by
  subst e
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  exact ⟨fun a ha => ha⟩

theorem stalkClosedPointTo_mem_subfield_of_definedOver {X : Scheme.{0}} {K : Type} [Field K] (k₀ : Subfield K) (Q : Sp K ⟶ X)
    (hQ : GlobalTheory.UChart.DefOver k₀ Q) (b : X.presheaf.stalk (Q (closedPoint K))) :
    (Scheme.stalkClosedPointTo Q).hom b ∈ k₀ := by
  obtain ⟨P₀, rfl⟩ := hQ
  have e : (spMap k₀.subtype ≫ P₀) (closedPoint K) = P₀ (closedPoint k₀) := by
    change P₀ ((spMap k₀.subtype) (closedPoint K)) = _
    congr 1
    exact Subsingleton.elim _ _
  have hs : (spMap k₀.subtype ≫ P₀) (closedPoint K) ⤳ P₀ (closedPoint k₀) := e ▸ specializes_refl _
  obtain ⟨a, rfl⟩ := (bijective_stalkSpecializes_of_eq hs e).2 b
  rw [stalkClosedPointTo_comp_stalkMap_spec X P₀ k₀.subtype hs a]
  exact SetLike.coe_mem _

theorem stalkVal_closedPoint : ∀ (X : Scheme.{0}) (R : Type) [CommRing R] [IsLocalRing R] (ξ₁ : Sp R ⟶ X) (K : Type) [Field K] (ev₁ : R →+* K) (k₀ : Subfield K), (∀ p, (spMap ev₁ ≫ ξ₁) p = ξ₁ (closedPoint R)) → GlobalTheory.UChart.DefOver k₀ (spMap ev₁ ≫ ξ₁) → ∀ h ∈ (Scheme.stalkClosedPointTo ξ₁).hom.range, ev₁ h ∈ k₀ ∧ (h ∈ maximalIdeal R → ev₁ h = 0) := by
  intro X R _ _ ξ₁ K _ ev₁ k₀ hpt hdef h hh
  obtain ⟨a, rfl⟩ := hh
  have e := hpt (closedPoint K)
  have hs : (spMap ev₁ ≫ ξ₁) (closedPoint K) ⤳ ξ₁ (closedPoint R) := e ▸ specializes_refl _
  have hv := stalkClosedPointTo_comp_stalkMap_spec X ξ₁ ev₁ hs a
  refine ⟨?_, fun hm => ?_⟩
  · rw [← hv]
    exact stalkClosedPointTo_mem_subfield_of_definedOver k₀ _ hdef _
  · by_contra hne
    have hl := isLocalHom_stalkSpecializes_of_eq hs e
    have hu : IsUnit ((Scheme.stalkClosedPointTo (spMap ev₁ ≫ ξ₁)).hom
        ((X.presheaf.stalkSpecializes hs).hom a)) := by
      rw [hv]; exact Ne.isUnit hne
    have ha : IsUnit a := isUnit_of_map_unit _ _ (isUnit_of_map_unit _ _ hu)
    exact (mem_maximalIdeal _).1 hm (ha.map _)

end GlobalTheory.USep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkValueClosedPointDefinedOverSubfieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stalkValue_closedPoint_definedOver_subfield : ∀ (X : Scheme.{0}) (R : Type) [CommRing R] [IsLocalRing R] (ξ₁ : Sp R ⟶ X) (K : Type) [Field K] (ev₁ : R →+* K) (k₀ : Subfield K), (∀ p, (spMap ev₁ ≫ ξ₁) p = ξ₁ (closedPoint R)) → GlobalTheory.UChart.DefOver k₀ (spMap ev₁ ≫ ξ₁) → ∀ h ∈ (Scheme.stalkClosedPointTo ξ₁).hom.range, ev₁ h ∈ k₀ ∧ (h ∈ maximalIdeal R → ev₁ h = 0) := by
  first | exact @GlobalTheory.USep.stalkVal_closedPoint | exact GlobalTheory.USep.stalkVal_closedPoint | (intros; apply GlobalTheory.USep.stalkVal_closedPoint <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCorrectionProperNormalCoverPowerLocalEquat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCorrectionProperNormalCoverPowerLocalEquat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

namespace GlobalTheory.CorrCover

theorem exists_corr : ∀ (Z M S₁ : Scheme.{0}) [IsIntegral M] [IsIntegral S₁] (sM : M ⟶ Sp ℤ) (p₁ : S₁ ⟶ M) (g : M ⟶ Z) (J : Z.IdealSheafData), LocallyOfFiniteType sM → QuasiCompact sM → Flat (p₁ ≫ sM) → Geo.Tor.IsNormalScheme S₁ → IsProper p₁ → IsDominant p₁ → FinalTheorems.EffCartier (J.comap (p₁ ≫ g)) → ∀ (U₁ : S₁.Opens), (U₁ : Set S₁).Nonempty → ∀ (z₁ : M) (R : Type) [CommRing R] [IsLocalRing R] (ev : M.presheaf.stalk z₁ →+* R), IsLocalHom ev → ∀ ξ₁ : Sp R ⟶ S₁, ξ₁ ≫ p₁ = spMap ev ≫ M.fromSpecStalk z₁ → ∃ g₀ : R, idlAlong (J.comap (p₁ ≫ g)) ξ₁ = Ideal.span {g₀} ∧ ∀ D e : ℕ, ∃ e' : ℕ, ∀ f : M.presheaf.stalk z₁, (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (ξ' : Sp V ⟶ S₁) (ev' : M.presheaf.stalk z₁ →+* V), IsLocalHom ev' → spMap ev' ≫ M.fromSpecStalk z₁ = ξ' ≫ p₁ → Set.range (jK V ≫ ξ') ⊆ (U₁ : Set S₁) → ev' f ∈ idlAlong (J.comap (p₁ ≫ g)) ξ' ^ D ⊔ ((maximalIdeal (M.presheaf.stalk z₁)).map ev') ^ e') → ∃ h ∈ (Scheme.stalkClosedPointTo ξ₁).hom.range, ev f - h * g₀ ^ D ∈ maximalIdeal R ^ e := by
  intro Z M S₁ _ _ sM p₁ g J h1 h2 h3 hN h5 h6 hEC U₁ hU z₁ R _ _ ev hev ξ₁ hξ
  haveI := h1; haveI := h2; haveI := h3; haveI := h5; haveI := h6; haveI := hev
  set I := J.comap (p₁ ≫ g) with hIdef
  set x₁ := ξ₁ (closedPoint R)
  set ψ := (Scheme.stalkClosedPointTo ξ₁).hom
  obtain ⟨W, f₀, hx, -, hI⟩ := hEC x₁
  have st : ∀ k : ℕ, FinalTheorems.stalkId (I ^ k) x₁ = Ideal.span {(S₁.presheaf.germ _ x₁ hx).hom f₀ ^ k} := fun k => by
    rw [ReciprocityTheory.AnForm.R.ds_stalkId_eq_map _ W x₁ hx, Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, hI,
      Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton, map_pow]
  refine ⟨ψ ((S₁.presheaf.germ _ x₁ hx).hom f₀), ?_, ?_⟩
  · have := st 1
    rw [pow_one, pow_one] at this
    rw [idlAlong, this, Ideal.map_span, Set.image_singleton]
  intro D e
  obtain ⟨E, hE⟩ := EffCartierData.exists_idealSheaf_eq (CoverElements.effCartier_pow hEC D)
  obtain ⟨e', he'⟩ := GlobalTheory.T.exists_correction_approximate_ideal_sections M S₁ sM p₁ hN U₁ hU E z₁ e
  refine ⟨e', fun f hf => ?_⟩
  have hm := he' f (fun V _ _ _ _ hc ξ' ev' hl hc' hr => by
    rw [hE, TorRef.idlAlong_pow]
    exact hf V hc ξ' ev' hl hc' hr)
  obtain ⟨f₁, hf₁, r, hr, rfl⟩ := Submodule.mem_sup.1 hm
  obtain ⟨u, hu, hψ⟩ := CoverElements.exists_stalk_of_map p₁ E.idealSheaf ξ₁ ev hξ hf₁
  rw [hE, st D] at hu
  obtain ⟨h', rfl⟩ := Ideal.mem_span_singleton'.1 hu
  refine ⟨ψ h', ⟨h', rfl⟩, ?_⟩
  have hmR : (maximalIdeal (M.presheaf.stalk z₁)).map ev ≤ maximalIdeal R :=
    Ideal.map_le_iff_le_comap.2 fun x hx => (IsLocalRing.mem_maximalIdeal _).2 fun hu => hx (isUnit_of_map_unit ev x hu)
  have : ev r ∈ maximalIdeal R ^ e :=
    Ideal.pow_right_mono hmR e (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem ev hr)
  rw [map_add (f := _), ← hψ, map_mul, map_pow]
  convert this using 1
  exact add_sub_cancel_left _ _

end GlobalTheory.CorrCover
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCorrectionProperNormalCoverPowerLocalEquatStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_correction_properNormalCover_powerLocalEquation : ∀ (Z M S₁ : Scheme.{0}) [IsIntegral M] [IsIntegral S₁] (sM : M ⟶ Sp ℤ) (p₁ : S₁ ⟶ M) (g : M ⟶ Z) (J : Z.IdealSheafData), LocallyOfFiniteType sM → QuasiCompact sM → Flat (p₁ ≫ sM) → Geo.Tor.IsNormalScheme S₁ → IsProper p₁ → IsDominant p₁ → FinalTheorems.EffCartier (J.comap (p₁ ≫ g)) → ∀ (U₁ : S₁.Opens), (U₁ : Set S₁).Nonempty → ∀ (z₁ : M) (R : Type) [CommRing R] [IsLocalRing R] (ev : M.presheaf.stalk z₁ →+* R), IsLocalHom ev → ∀ ξ₁ : Sp R ⟶ S₁, ξ₁ ≫ p₁ = spMap ev ≫ M.fromSpecStalk z₁ → ∃ g₀ : R, idlAlong (J.comap (p₁ ≫ g)) ξ₁ = Ideal.span {g₀} ∧ ∀ D e : ℕ, ∃ e' : ℕ, ∀ f : M.presheaf.stalk z₁, (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (ξ' : Sp V ⟶ S₁) (ev' : M.presheaf.stalk z₁ →+* V), IsLocalHom ev' → spMap ev' ≫ M.fromSpecStalk z₁ = ξ' ≫ p₁ → Set.range (jK V ≫ ξ') ⊆ (U₁ : Set S₁) → ev' f ∈ idlAlong (J.comap (p₁ ≫ g)) ξ' ^ D ⊔ ((maximalIdeal (M.presheaf.stalk z₁)).map ev') ^ e') → ∃ h ∈ (Scheme.stalkClosedPointTo ξ₁).hom.range, ev f - h * g₀ ^ D ∈ maximalIdeal R ^ e := by
  first | exact @GlobalTheory.CorrCover.exists_corr | exact GlobalTheory.CorrCover.exists_corr | (intros; apply GlobalTheory.CorrCover.exists_corr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInjectiveRingHomIsLocalHomAndExtend
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsFurtherLast
namespace GlobalTheory.ValuationExtensionExistence

theorem exists_extension {V R K : Type} [CommRing V] [CommRing R] [IsDomain R] [Field K]
    [IsAlgClosed K] [Algebra V R] [Algebra.IsIntegral V R] [FaithfulSMul V R] (ev : V →+* K) :
    ∃ ev₁ : R →+* K, ev₁.comp (algebraMap V R) = ev := by
  classical

  have : (RingHom.ker ev).IsPrime := RingHom.ker_isPrime ev
  obtain ⟨Q, -, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := R) (RingHom.ker ev) ⊥ (by
    rw [(show Ideal.under _ ⊥ = ⊥ from Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective V R))]
    exact bot_le)
  have := hQ
  have : Q.LiesOver (RingHom.ker ev) := ⟨hQp.symm⟩

  let : Algebra (V ⧸ RingHom.ker ev) K := (RingHom.kerLift ev).toAlgebra
  have : Module.IsTorsionFree (V ⧸ RingHom.ker ev) K :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (RingHom.kerLift_injective ev)
  have : Module.IsTorsionFree (V ⧸ RingHom.ker ev) (R ⧸ Q) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (FaithfulSMul.algebraMap_injective _ _)
  have : Algebra.IsIntegral (V ⧸ RingHom.ker ev) (R ⧸ Q) :=
    Ideal.Quotient.algebra_isIntegral_of_liesOver Q (RingHom.ker ev)
  have : Algebra.IsAlgebraic (V ⧸ RingHom.ker ev) (R ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  let f : R ⧸ Q →ₐ[V ⧸ RingHom.ker ev] K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨(f : R ⧸ Q →+* K).comp (Ideal.Quotient.mk Q), ?_⟩
  ext v
  have h := f.commutes (Ideal.Quotient.mk (RingHom.ker ev) v)
  rw [Ideal.Quotient.algebraMap_mk_of_liesOver] at h
  exact h.trans (RingHom.kerLift_mk ev v)

theorem main : ∀ (V R K : Type) [inst : CommRing V] [IsDomain V] [IsLocalRing V]
    [inst_3 : CommRing R] [IsDomain R] [IsLocalRing R] [inst_6 : Field K] [IsAlgClosed K]
    (ρ : V →+* R), Function.Injective (⇑ρ : V → R) → RingHom.Finite ρ →
      IsLocalHom ρ ∧ ∀ (ev : V →+* K), ∃ (ev₁ : R →+* K), RingHom.comp ev₁ ρ = ev := by
  intro V R K _ _ _ _ _ _ _ _ ρ hinj hfin
  have hint : ρ.IsIntegral := hfin.to_isIntegral
  refine ⟨?_, fun ev => ?_⟩
  · refine ((IsLocalRing.local_hom_tfae ρ).out 5 1).mp ?_
    exact IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' ρ hint _)
  · let := ρ.toAlgebra
    have : Algebra.IsIntegral V R := ⟨hint⟩
    have : FaithfulSMul V R := (faithfulSMul_iff_algebraMap_injective V R).2 hinj
    exact exists_extension ev

end GlobalTheory.ValuationExtensionExistence
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInjectiveRingHomIsLocalHomAndExtend
open IsLocalRing

namespace GlobalTheory

theorem finite_injective_localHom_and_extend (V R K : Type) [CommRing V] [IsDomain V] [IsLocalRing V]
    [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [IsAlgClosed K] (ρ : V →+* R) :
    Function.Injective ρ → ρ.Finite → IsLocalHom ρ ∧ ∀ ev : V →+* K, ∃ ev₁ : R →+* K, ev₁.comp ρ = ev := by
  first
  | exact @_root_.GlobalTheory.ValuationExtensionExistence.main
  | exact _root_.GlobalTheory.ValuationExtensionExistence.main
  | (apply _root_.GlobalTheory.ValuationExtensionExistence.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ValuationExtensionExistence.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ValuationExtensionExistence.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ValuationExtensionExistence.main ..)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInjectiveRingHomIsLocalHomAndExtendStatement
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_injective_ringHom_isLocalHom_and_extend : ∀ (V R K : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [IsAlgClosed K] (ρ : V →+* R), Function.Injective ρ → ρ.Finite → IsLocalHom ρ ∧ ∀ ev : V →+* K, ∃ ev₁ : R →+* K, ev₁.comp ρ = ev := by
  first | exact @GlobalTheory.finite_injective_localHom_and_extend | exact GlobalTheory.finite_injective_localHom_and_extend | (intros; apply GlobalTheory.finite_injective_localHom_and_extend <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApproximatingElementsNormalCoverUnitary
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

noncomputable section

namespace GlobalTheory.USep

theorem range_jK_spMap_subset : ∀ (V R : Type) [CommRing V] [IsDomain V] [CommRing R] [IsDomain R] (ρ : V →+* R), Function.Injective ρ → ∀ (X : Scheme.{0}) (χ : Sp V ⟶ X), Set.range (jK R ≫ spMap ρ ≫ χ) ⊆ Set.range (jK V ≫ χ) := by
  intro V R _ _ _ _ ρ hρ X χ x ⟨p, hp⟩
  let q : Sp (FractionRing V) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V))
  have key : (spMap ρ) ((jK R) p) = (jK V) q := by
    apply PrimeSpectrum.ext
    change Ideal.comap ρ (Ideal.comap (algebraMap R (FractionRing R)) p.asIdeal) =
      Ideal.comap (algebraMap V (FractionRing V)) ⊥
    haveI : p.asIdeal.IsPrime := PrimeSpectrum.isPrime p
    rw [Ideal.eq_bot_of_prime p.asIdeal, Ideal.comap_comap,
      Ideal.comap_bot_of_injective _ (IsFractionRing.injective V (FractionRing V)),
      Ideal.comap_bot_of_injective _ (by rw [RingHom.coe_comp]; exact (IsFractionRing.injective R (FractionRing R)).comp hρ)]
  refine ⟨q, ?_⟩
  rw [← hp]
  change χ ((jK V) q) = χ ((spMap ρ) ((jK R) p))
  rw [key]

theorem exists_elements_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (φ : InvFun (𝓞 E)), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (d : ℕ) (J : C.Z.IdealSheafData), (∀ x ∈ J.support, x ∉ Set.range C.i) → UValOn Xo c C.i φ J d → ∀ (S : Scheme.{0}) (π : S ⟶ pullback C.z (spMap C.b)), IsNormBl π (J.comap (pullback.fst C.z (spMap C.b))) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Cm : GlobalTheory.UChart.MonoFam Xo c φ V), GlobalTheory.Mum.Base V → ∀ ξ : Sp V ⟶ S, Cm.y ≫ C.iF = jK V ≫ ξ ≫ π → ∀ (N₁ : ℕ) (M : Scheme.{0}) [IsIntegral M] (g : M ⟶ C.Z) (z₁ : M) (ζ : Sp (M.presheaf.stalk z₁) ⟶ pullback C.z (spMap C.b)) (Φ : VSys (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) !![(1 : ℤ)] N₁ (M.presheaf.stalk z₁)) (y : Φ.Y) (ρ : V →+* Φ.V y) (e : Φ.X y ≃ₗ[𝓞 E] Cm.P.D.toPre.X) (h : Fin (Φ.m y) ≃ Fin Cm.m) (U : M.Opens), (U : Set M).Nonempty → IsCov C g z₁ ζ → GlobalTheory.GSep.HasTraitsOn ζ Φ.pre U → IsMember ζ Φ Cm (ξ ≫ π) y ρ e h → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ p, (spMap ev ≫ ξ) p = ξ (closedPoint V)) → GlobalTheory.UChart.DefOver k₀ (spMap ev ≫ ξ) → ∀ ga : Fin (Φ.m y) → LinearMap.BilinForm ℤ (Φ.X y), (∀ k a b, ga k a b = Cm.δ (h k) (e a) (e b)) → ∃ ev₁ : Φ.V y →+* K, ev₁.comp ρ = ev ∧ GlobalTheory.Poinc.Sep.Elements Φ y φ (2 * d) ga ev₁ k₀ := by
  intro E _ _ _ H Dw hpq l Xo c C φ hφ d J hJ hV S π hπ V _ _ _ Cm hB ξ hξ N₁ M _ g z₁ ζ Φ y ρ e h U hUne hcov htr hmem K _ _ ev k₀ hk₀ hpt hdef ga hga
  obtain ⟨hρi, hρf, hζ, hst, -⟩ := hmem
  obtain ⟨hρl, hext⟩ := GlobalTheory.T.finite_injective_ringHom_isLocalHom_and_extend V (Φ.V y) K ρ hρi hρf
  obtain ⟨ev₁, hev₁⟩ := hext ev
  have hcov' := hcov
  obtain ⟨-, -, hζg, -⟩ := hcov'
  obtain ⟨S₁, hS₁, p₁, sM, U₁, hft, hqc, hfl, hnorm, hprop, hdom, hcart, hU₁, hlift, hxi⟩ :=
    GlobalTheory.T.exists_normalisedBlowup_finite_normal_cover E H Dw hpq l Xo c C J hJ S π hπ M g z₁ ζ hcov
  haveI := hS₁
  haveI : IsIntegrallyClosed (Φ.V y) := (Φ.cn y).2.1
  have hζ' : (spMap ρ ≫ ξ) ≫ π = spMap (Φ.ev y) ≫ ζ := by rw [hζ, Category.assoc]
  have hgen : Set.range (jK (Φ.V y) ≫ (spMap ρ ≫ ξ) ≫ π) ⊆ Set.range C.iF := by
    intro x hx
    obtain ⟨p, hp⟩ := range_jK_spMap_subset V (Φ.V y) ρ hρi _ (ξ ≫ π) (by simpa only [Category.assoc] using hx)
    simp only [Category.assoc] at hp
    rw [← hξ, Scheme.Hom.comp_apply] at hp
    exact ⟨_, hp⟩
  obtain ⟨ξ₁, hξ₁p, hξ₁⟩ := hxi (Φ.V y) (spMap ρ ≫ ξ) (Φ.ev y) hζ' hgen
  have hcomp : spMap ev₁ ≫ spMap ρ = spMap ev := by
    rw [← hev₁, spMap, spMap, spMap, ← Spec.map_comp]; rfl
  have hpt' : ∀ p, (spMap ev₁ ≫ (spMap ρ ≫ ξ)) p = (spMap ρ ≫ ξ) (closedPoint (Φ.V y)) := by
    intro p
    rw [← Category.assoc, hcomp, hpt]
    change _ = ξ ((spMap ρ) (closedPoint (Φ.V y)))
    rw [spMap, Spec_closedPoint]
  have hdef' : GlobalTheory.UChart.DefOver k₀ (spMap ev₁ ≫ (spMap ρ ≫ ξ)) := by rwa [← Category.assoc, hcomp]
  obtain ⟨hpt₁, hdef₁⟩ := hξ₁ K ev₁ k₀ hk₀ hpt' hdef'
  obtain ⟨b', hb', hid⟩ := GlobalTheory.T.idealAlong_monomialFamily_eq_span_monomial E H Dw hpq l Xo c C φ hφ d J hJ hV S π hπ V Cm hB ξ hξ
  have hU₂ : ((U₁ ⊓ p₁ ⁻¹ᵁ U : S₁.Opens) : Set S₁).Nonempty := by
    have h1 : ((p₁ ⁻¹ᵁ U : S₁.Opens) : Set S₁).Nonempty := by
      obtain ⟨s, hs⟩ := (p₁.denseRange).exists_mem_open U.isOpen hUne
      exact ⟨s, hs⟩
    exact nonempty_preirreducible_inter U₁.isOpen (p₁ ⁻¹ᵁ U).isOpen hU₁ h1
  obtain ⟨g₀, hg₀, happ⟩ := GlobalTheory.T.exists_correction_properNormalCover_powerLocalEquation C.Z M S₁ sM p₁ g J hft hqc hfl hnorm hprop hdom hcart (U₁ ⊓ p₁ ⁻¹ᵁ U) hU₂ z₁ (Φ.V y) (Φ.ev y)
    (Φ.ev_loc y) ξ₁ hξ₁p
  have hpath : ξ₁ ≫ p₁ ≫ g = spMap ρ ≫ (ξ ≫ π ≫ pullback.fst C.z (spMap C.b)) := by
    rw [← Category.assoc, hξ₁p, Category.assoc, ← hζg, ← Category.assoc, hζ]
    simp only [Category.assoc]
  have hkey : Ideal.span {g₀} = Ideal.span {∏ k, Φ.t y k ^ (2 * b' (h k))} := by
    rw [← hg₀, GlobalTheory.TorRef.idlAlong_comap, hpath, GlobalTheory.TraitOrder.idlAlong_comp, hid, Ideal.map_span,
      Set.image_singleton, map_prod]
    congr 2
    exact (Equiv.prod_comp h _).symm.trans (Finset.prod_congr rfl fun j _ => by
      rw [map_pow, ← (hst j).1, ← pow_mul])
  have hδ : ∀ k, Φ.δ y k = GlobalTheory.PolFan.pull e.toLinearMap ((l.M' : ℤ) • Cm.δ (h k)) :=
    fun k => LinearMap.ext₂ fun a b => by rw [(hst k).2 a b]; rfl
  have hev : ∀ k, φ.evalZ (Φ.δ y k) = φ.evalZ ((l.M' : ℤ) • Cm.δ (h k)) := fun k => by
    rw [hδ k, evalZ_pull φ (r := e.toLinearMap) e.surjective]
  have hbdd : BddAct (H.bar : 𝓞 E → 𝓞 E) := (GlobalTheory.Poinc.bddAct_int_and_cm).2 E H
  have hM : 1 ≤ l.M' := GlobalTheory.LevelExist.M'_pos l
  have hδga : ∀ i, Φ.δ y i = ((l.M' : ℕ) : ℤ) • ga i := fun i => LinearMap.ext₂ fun a b => by
    rw [(hst i).2 a b]; simp [hga]
  refine ⟨ev₁, hev₁, (Scheme.stalkClosedPointTo ξ₁).hom.range, g₀, fun k => 2 * b' (h k),
    fun x hx => GlobalTheory.T.stalkValue_closedPoint_definedOver_subfield S₁ (Φ.V y) ξ₁ K ev₁ k₀ hpt₁ hdef₁ x hx, fun k => ?_,
    Ideal.span_singleton_eq_span_singleton.1 hkey, ?_⟩
  · push_cast
    rw [hev k, hb' (h k)]
    ring
  intro D l' a hdom c' e'
  obtain ⟨e₁, he₁⟩ := happ D e'
  obtain ⟨f, hord, hlead⟩ := GlobalTheory.T.exists_approximate_series_leading_term_fourierSystem (𝓞 E) (H.bar : 𝓞 E → 𝓞 E) hbdd (min Dw.p Dw.q) φ hφ 1 !![(1 : ℤ)] Φ.posW N₁ _ Φ y ga
    l.M' hM hδga (D * (2 * d)) l' a hdom c' (max e' e₁)
  have hord' : Φ.OrdGe φ (D * (2 * d)) e₁ f := fun y' hP hm i =>
    (sup_le_sup_left (α := Ideal (Φ.V y')) (Ideal.pow_le_pow_right (le_max_right e' e₁)) _) (hord y' hP hm i)
  obtain ⟨x, hx, hxe⟩ := he₁ f (by
    intro V' _ _ _ _ hc ξ' ev' hl hcomm hU
    have hj : jK V' ≫ spMap ev' = spMap ((algebraMap V' (FractionRing V')).comp ev') := by
      simp only [jK, spMap, ← Spec.map_comp]; rfl
    obtain ⟨y', hy'⟩ := hlift (FractionRing V') (jK V' ≫ ξ') ((algebraMap V' (FractionRing V')).comp ev')
      (by rw [Category.assoc, ← hcomm, ← Category.assoc, hj]) (fun x hx => (hU hx).1)
    have hUM : Set.range (jK V' ≫ spMap ev' ≫ M.fromSpecStalk z₁) ⊆ (U : Set M) := by
      rw [hcomm]
      rintro _ ⟨q, rfl⟩
      have := (hU ⟨q, rfl⟩).2
      rw [Scheme.Hom.comp_apply]
      exact this
    have htr' := GlobalTheory.T.mem_system_of_order_ge_along_traits GlobalTheory.T.exists_unitaryTrait_through_moduliGenericPoint E H Dw l Xo c C φ d J hV M z₁ U ζ N₁ Φ htr V' hc ev' hl hUM y' hy' D e₁ f hord'
    have hpath' : ξ' ≫ p₁ ≫ g = spMap ev' ≫ ζ ≫ pullback.fst C.z (spMap C.b) := by
      rw [hζg, ← Category.assoc (spMap ev'), hcomm, Category.assoc]
    rwa [GlobalTheory.TorRef.idlAlong_comap, hpath'])
  refine ⟨x, hx, ?_⟩
  have h1 : Φ.ev y f - Φ.coefT y a c' * Φ.monoT y a ∈
      Ideal.span {Φ.monoT y a} * Ideal.span (Set.range (Φ.t y)) ⊔ maximalIdeal (Φ.V y) ^ e' :=
    (sup_le_sup_left (α := Ideal (Φ.V y)) (Ideal.pow_le_pow_right (le_max_left e' e₁)) _) hlead
  have h2 : Φ.ev y f - x * g₀ ^ D ∈
      Ideal.span {Φ.monoT y a} * Ideal.span (Set.range (Φ.t y)) ⊔ maximalIdeal (Φ.V y) ^ e' :=
    Ideal.mem_sup_right hxe
  have h3 := Ideal.sub_mem _ h1 h2
  convert h3 using 1
  ring

end GlobalTheory.USep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApproximatingElementsNormalCoverUnitaryStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_approximating_elements_normalCover_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (φ : InvFun (𝓞 E)), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (d : ℕ) (J : C.Z.IdealSheafData), (∀ x ∈ J.support, x ∉ Set.range C.i) → UValOn Xo c C.i φ J d → ∀ (S : Scheme.{0}) (π : S ⟶ pullback C.z (spMap C.b)), IsNormBl π (J.comap (pullback.fst C.z (spMap C.b))) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Cm : GlobalTheory.UChart.MonoFam Xo c φ V), GlobalTheory.Mum.Base V → ∀ ξ : Sp V ⟶ S, Cm.y ≫ C.iF = jK V ≫ ξ ≫ π → ∀ (N₁ : ℕ) (M : Scheme.{0}) [IsIntegral M] (g : M ⟶ C.Z) (z₁ : M) (ζ : Sp (M.presheaf.stalk z₁) ⟶ pullback C.z (spMap C.b)) (Φ : VSys (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) !![(1 : ℤ)] N₁ (M.presheaf.stalk z₁)) (y : Φ.Y) (ρ : V →+* Φ.V y) (e : Φ.X y ≃ₗ[𝓞 E] Cm.P.D.toPre.X) (h : Fin (Φ.m y) ≃ Fin Cm.m) (U : M.Opens), (U : Set M).Nonempty → IsCov C g z₁ ζ → GlobalTheory.GSep.HasTraitsOn ζ Φ.pre U → IsMember ζ Φ Cm (ξ ≫ π) y ρ e h → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ p, (spMap ev ≫ ξ) p = ξ (closedPoint V)) → GlobalTheory.UChart.DefOver k₀ (spMap ev ≫ ξ) → ∀ ga : Fin (Φ.m y) → LinearMap.BilinForm ℤ (Φ.X y), (∀ k a b, ga k a b = Cm.δ (h k) (e a) (e b)) → ∃ ev₁ : Φ.V y →+* K, ev₁.comp ρ = ev ∧ GlobalTheory.Poinc.Sep.Elements Φ y φ (2 * d) ga ev₁ k₀ := by
  first | exact @GlobalTheory.USep.exists_elements_cover | exact GlobalTheory.USep.exists_elements_cover | (intros; apply GlobalTheory.USep.exists_elements_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendsAbelianPartOfIsPullDeg
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendsAbelianPartOfIsPullDeg
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

noncomputable section

namespace GlobalTheory.USep

def chartPullCompOf {X Y Y' : Scheme.{0}} (L : LB X) (g : Y ⟶ X) (h : Y' ⟶ Y) (k : Y' ⟶ X) (e : h ≫ g = k) :
    ChartPull (L.pull k) (L.pull g) h where
  idx J := J
  le J y hy := by
    subst e
    exact mem_pull.2 (by simpa using mem_pull.1 hy)
  g y J J' hj hj' := by
    subst e
    have hj₁ : h y ∈ (L.pull g).U J := mem_pull.2 (by simpa using mem_pull.1 hj)
    have hj₁' : h y ∈ (L.pull g).U J' := mem_pull.2 (by simpa using mem_pull.1 hj')
    refine (gm_pull_g L (h ≫ g) (𝟙 _) y J J' hj hj').trans ?_
    refine Eq.trans ?_ (gm_pull_g L g h y J J' hj₁ hj₁').symm
    rw [Category.id_comp]

theorem spMap_comp_ringHom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, ← Spec.map_comp]

theorem descAt_of_isPullDeg : ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] (ρ : V →+* V₁)
    (Q : DegPre V) (D : DegPre V₁), IsPullDeg ρ Q D → D.P.g = Q.P.g ∧ ∀ (K : Type) [Field K] (ev : V₁ →+* K)
    (k₀ : Subfield K), DescAt D ev k₀ → DescAt Q (ev.comp ρ) k₀ := by
  intro V V₁ _ _ _ _ ρ Q D p
  have gp := pull_grp p
  refine ⟨H1.dim_unique _ D.P.smoothDim
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback gp.1 Q.P.smoothDim)
    (eSec D.P.A (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V₁)), ?_⟩
  intro K _ ev k₀ hd
  obtain ⟨B₀, i₁, i₂, M₀, c₀, B', i₃, π₁, π₀, w, c', hab, hM, h₁, h₀, hw, hc⟩ := hd
  have hL : LBIso (Q.P.L.pull (π₁ ≫ (p.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf ρ)))) (M₀.pull π₀) :=
    LBIso.trans (pull_isLB Q.P.isLB _) (pull_isLB D.P.isLB _) (pull_isLB hM _)
      (LBIso.chartPull (chartPullCompOf Q.P.L _ π₁ _ rfl) (chartPullPull D.P.L π₁)
        (LBIso.symm ⟨p.w, p.w_gen⟩)) ⟨w, hw⟩
  obtain ⟨w', hw'⟩ := hL
  refine ⟨B₀, i₁, i₂, M₀, fun a => c₀ (p.xe.symm a), B', i₃, π₁ ≫ (p.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf ρ)),
    π₀, w', fun a => c' (p.xe.symm a), hab, hM, ?_, h₀, hw', fun a => ⟨(hc _).1, ?_, (hc _).2.2⟩⟩
  · exact (h₁.comp gp).congr (spMap_comp_ringHom ρ ev).symm rfl
  · have e₁ := (hc (p.xe.symm a)).2.1
    have e₂ := p.c_pr (p.xe.symm a)
    rw [AddEquiv.apply_symm_apply] at e₂
    rw [← Category.assoc, e₁, Category.assoc, e₂, ← Category.assoc, spMap_comp_ringHom]

end GlobalTheory.USep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendsAbelianPartOfIsPullDegStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descendsAbelianPart_of_isPullDeg : ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] (ρ : V →+* V₁) (Q : DegPre V) (D : DegPre V₁), IsPullDeg ρ Q D → D.P.g = Q.P.g ∧ ∀ (K : Type) [Field K] (ev : V₁ →+* K) (k₀ : Subfield K), DescAt D ev k₀ → DescAt Q (ev.comp ρ) k₀ := by
  first | exact @GlobalTheory.USep.descAt_of_isPullDeg | exact GlobalTheory.USep.descAt_of_isPullDeg | (intros; apply GlobalTheory.USep.descAt_of_isPullDeg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparationNormalizedBlowupUnitaryCompactificatio
noncomputable section
namespace GlobalTheory.USep.Alg

theorem mem_of_zpow_mem {K : Type} [Field K] (k₀ : Subfield K) (hk : IsAlgClosed k₀) {x : K} (hx : x ≠ 0) {m : ℤ}
    (hm : m ≠ 0) (h : x ^ m ∈ k₀) : x ∈ k₀ := by
  have hn : ∃ n : ℕ, 0 < n ∧ x ^ n ∈ k₀ := by
    rcases lt_or_gt_of_ne hm with hm | hm
    · refine ⟨m.natAbs, by omega, ?_⟩
      have : x ^ m = (x ^ m.natAbs)⁻¹ := by
        rw [← zpow_natCast, ← zpow_neg]; congr 1; omega
      rw [this] at h
      simpa using k₀.inv_mem h
    · refine ⟨m.natAbs, by omega, ?_⟩
      have : x ^ m = x ^ m.natAbs := by rw [← zpow_natCast]; congr 1; omega
      rwa [this] at h
  obtain ⟨n, hn, h⟩ := hn
  letI : Algebra k₀ K := k₀.subtype.toAlgebra
  have hi : IsIntegral k₀ x := by
    refine ⟨Polynomial.X ^ n - Polynomial.C ⟨x ^ n, h⟩, Polynomial.monic_X_pow_sub_C _ hn.ne', ?_⟩
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
    exact sub_eq_zero.2 rfl
  have h1 : (minpoly k₀ x).natDegree = 1 := by
    have := IsAlgClosed.degree_eq_one_of_irreducible k₀ (minpoly.irreducible hi)
    exact Polynomial.natDegree_eq_of_degree_eq_some this
  obtain ⟨y, hy⟩ := (minpoly.natDegree_eq_one_iff).1 h1
  rw [← hy]
  exact y.2

theorem exists_extend_smul {L : Type} [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L] (N : Submodule ℤ L)
    (F : N →ₗ[ℤ] ℤ) : ∃ n : ℤ, n ≠ 0 ∧ ∃ g : L →ₗ[ℤ] ℤ, ∀ x : N, g x = n * F x := by
  classical
  obtain ⟨r, S⟩ := N.smithNormalForm (Module.Free.chooseBasis ℤ L)
  have ha : ∀ i, S.a i ≠ 0 := fun i h0 => S.bN.ne_zero i (Subtype.ext (by rw [S.snf, h0, zero_smul]; rfl))
  set P : ℤ := ∏ i, S.a i
  have hdiv : ∀ i, S.a i ∣ P := fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  refine ⟨P, Finset.prod_ne_zero_iff.2 fun i _ => ha i, ∑ i, (P / S.a i * F (S.bN i)) • S.bM.coord (S.f i), ?_⟩
  have key : ∀ i, (∑ k, (P / S.a k * F (S.bN k)) • S.bM.coord (S.f k)) (S.bN i) = P * F (S.bN i) := by
    intro i
    rw [LinearMap.sum_apply, S.snf, Finset.sum_eq_single i]
    · simp only [LinearMap.smul_apply, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
        Finsupp.single_eq_same, smul_eq_mul, mul_one]
      rw [← mul_assoc, mul_comm (S.a i), Int.ediv_mul_cancel (hdiv i)]
    · intro k _ hk
      simp only [LinearMap.smul_apply, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, smul_eq_mul]
      rw [Finsupp.single_eq_of_ne (S.f.injective.ne hk)]
      simp
    · simp
  intro x
  have : ((∑ k, (P / S.a k * F (S.bN k)) • S.bM.coord (S.f k)).comp N.subtype) = P • F :=
    S.bN.ext fun i => by rw [LinearMap.comp_apply, LinearMap.smul_apply, Submodule.subtype_apply, key]; rfl
  exact LinearMap.congr_fun this x

end GlobalTheory.USep.Alg

namespace GlobalTheory.USep.Alg

theorem zpow_sum_units {G ι : Type} [CommGroup G] (a : G) (s : Finset ι) (f : ι → ℤ) :
    a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.prod_insert hx, zpow_add, ih]

end GlobalTheory.USep.Alg

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical


open GlobalTheory.USep in
theorem GlobalTheory.USep.sepB_of_normBl : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (d : ℕ) (J : C.Z.IdealSheafData), 1 ≤ d → (∀ x ∈ J.support, x ∉ Set.range C.i) → UValOn Xo c C.i φ J d → ∀ (S : Scheme.{0}) (π : S ⟶ pullback C.z (spMap C.b)) (j : Xo.XF c ⟶ S), GlobalTheory.Poinc.IsNormBl π (J.comap (pullback.fst C.z (spMap C.b))) → IsProper π → j ≫ π = C.iF → IsOpenImmersion j → π ⁻¹' Set.range C.iF = Set.range j → GlobalTheory.UChart.SepB Xo c φ j := by
  intro E _ _ _ H Dw hpq φ hpol hnsi l Xo c C d J hd hJ hval S π j hbl hprop hjπ hj hpre
  intro V _ _ _ Cm hV ξ hξ N s ε τ₀ h1 h2 h3 hτ K _ _ ev k₀ hk hc hdef
  have hξ' : Cm.y ≫ C.iF = jK V ≫ ξ ≫ π := by rw [← hjπ, ← Category.assoc, hξ, Category.assoc]
  obtain ⟨j₀, hdesc⟩ := GlobalTheory.T.abelianPart_descends_of_thetaTerms_ratios Cm.P.D.toPre.P.g 3 Nat.prime_three (by decide)
  obtain ⟨jj, M, _, g, z₁, ζ, Φ, y, ρ, e, h, U, hUne, hjj, hcov, htr, hmem⟩ :=
    GlobalTheory.T.exists_unitary_fourier_system_traits_family E H Dw hpq l Xo c C φ V Cm hV (ξ ≫ π) hξ' 3 Nat.prime_three (by decide) (max j₀ 1)
  let ga : Fin (Φ.m y) → LinearMap.BilinForm ℤ (Φ.X y) := fun k => GlobalTheory.PolFan.pull e.toLinearMap (Cm.δ (h k))
  obtain ⟨ev₁, hev₁, hEl⟩ := GlobalTheory.T.exists_approximating_elements_normalCover_unitary E H Dw hpq l Xo c C φ hpol d J hJ hval S π hbl V Cm hV ξ hξ' _ M g z₁ ζ Φ y ρ e h U hUne
    hcov htr hmem K ev k₀ hk hc hdef ga (fun k a b => rfl)
  obtain ⟨d₀, hd₀, hsup⟩ : ∃ d₀, 1 ≤ d₀ ∧ HasSupports (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) φ d₀ :=
    exists_hasSupports (𝓞 E) H.bar (min Dw.p Dw.q) φ hpol fun X _ _ _ _ hX r γ hγ =>
      GlobalTheory.T.exists_supportingTuple_smoothCone_cmField E H φ X (hpol X hX) r γ hγ
  have hM' : 1 ≤ l.M' := Nat.one_le_iff_ne_zero.2 (Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne')
  have hmem4 := hmem.2.2.2.1
  have hδ : ∀ k, Φ.δ y k = (l.M' : ℤ) • ga k := fun k => LinearMap.ext₂ fun a b => by
    rw [(hmem4 k).2 a b]; rfl
  have hN3 : 3 ≤ (3 ^ jj) ^ 2 := by
    have : 3 ≤ 3 ^ jj := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ jj := Nat.pow_le_pow_right (by norm_num) (le_of_max_le_right hjj)
    nlinarith
  obtain ⟨V1, V2, V3⟩ := GlobalTheory.T.poincareApprox_values_at_point_of_elements (𝓞 E) (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) φ hpol hnsi d₀ (2 * d) hd₀ (by omega) hsup 0
    !![(1 : ℤ)] Φ.posW _ hN3 _ Φ y ga l.M' hM' ((Cm.cone.pull_equiv e).reindex h) hδ K ev₁ k₀ hEl
  have hρinj : Function.Injective ρ := hmem.1
  obtain ⟨-, -, -, -, D, p, hth⟩ := hmem
  have hU : ∀ m : ℕ, m ≠ 0 → IsUnit (m : Φ.V y) := fun m hm => by
    have := (IsUnit.mk0 (m : c.F) (Nat.cast_ne_zero.2 hm)).map (ρ.comp Cm.b)
    rwa [map_natCast] at this
  have hmo : ∀ mu : Cm.P.D.toPre.X, mono !![(1 : ℤ)] (Φ.t y) (Φ.δ y) (fun _ => e.symm mu) ≠ 0 ∧
      ∃ cc, IsUnit (Φ.u y (fun _ => e.symm mu) cc) := fun mu =>
    ⟨Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (Φ.t_mem y i).2, Φ.u_unit y _⟩
  obtain ⟨hg, htr'⟩ := GlobalTheory.T.descendsAbelianPart_of_isPullDeg V (Φ.V y) ρ Cm.P.D.toPre D p
  refine (sepAtB_iff _ _ _ _ _).2 ⟨fun i => ?_, ?_, ?_⟩
  · rw [h1 i, ← hev₁, RingHom.comp_apply]
    have := (hmem4 (h.symm i)).1
    rw [Equiv.apply_symm_apply] at this
    rw [← this, map_pow, V1, zero_pow two_ne_zero]
  · have hD := hdesc jj (le_of_max_le_left hjj) (Φ.V y) (Φ.cn y) hU D hg Cm.P.D.toPre.X Φ.Q p.xe.symm
      (fun mu cc => Φ.u y (fun _ => e.symm mu) cc) (fun mu => mono !![(1 : ℤ)] (Φ.t y) (Φ.δ y) (fun _ => e.symm mu))
      hmo hth K ev₁ k₀ hk (fun mu cc cc' hu => V2 _ cc cc' hu)
    have := htr' K ev₁ k₀ hD
    rwa [hev₁] at this
  · intro W₀ _ ιb hFB hkb i
    let P : LinearMap.BilinForm ℤ Cm.P.D.toPre.X → LinearMap.BilinForm ℤ D.X :=
      fun β => β.compl₁₂ p.xe.toAddMonoidHom.toIntLinearMap p.xe.toAddMonoidHom.toIntLinearMap
    let ε₁ : Fin Cm.m ⊕ Fin N → LinearMap.BilinForm ℤ D.X :=
      fun x => P ((l.M' : ℤ) • (ε x : LinearMap.BilinForm ℤ Cm.P.D.toPre.X))
    obtain ⟨τ₁, hT1, hF1⟩ := GlobalTheory.T.periodsInCoordinates_fromBase_pullDeg V (Φ.V y) ρ hρinj Cm.P.D.toPre D p τ₀ (Cm.m + N)
      (fun k => s (finSumFinEquiv.symm k))
      (fun k => (l.M' : ℤ) • (ε (finSumFinEquiv.symm k) : LinearMap.BilinForm ℤ Cm.P.D.toPre.X))
      (fun k => ε₁ (finSumFinEquiv.symm k)) (fun k a b => rfl) hτ W₀ ιb hFB
    have hPE : D.PsiEven := GlobalTheory.PsiEvenPull.psiEven_pull GlobalTheory.globalFns_holds _ _ ρ _ _ p Cm.P.D.psi_even
    have hTB : D.TauBimult := GlobalTheory.tauBimult_of_isPullDeg GlobalTheory.globalFns_holds _ _ ρ _ _ p Cm.P.D.tau_bimult
    have hε₁ : ∀ x mu, ε₁ x (p.xe.symm mu) (p.xe.symm mu) = (l.M' : ℤ) * (ε x : LinearMap.BilinForm ℤ _) mu mu := by
      intro x mu; simp [ε₁, P]
    have hmo2 : ∀ mu, algebraMap (Φ.V y) (FractionRing (Φ.V y)) (mono !![(1 : ℤ)] (Φ.t y) (Φ.δ y) (fun _ => e.symm mu)) ^ 2
        = ∏ k, algebraMap (Φ.V y) (FractionRing (Φ.V y)) (ρ (s (.inl k))) ^ ε₁ (.inl k) (p.xe.symm mu) (p.xe.symm mu) := by
      intro mu
      have hq : ∀ k', (qW !![(1 : ℤ)] (Φ.δ y k') fun _ => e.symm mu) = (l.M' : ℤ) * Cm.δ (h k') mu mu := fun k' => by
        simp [qW, (hmem4 k').2]
      have hnn : ∀ k, 0 ≤ (l.M' : ℤ) * Cm.δ k mu mu := fun k => mul_nonneg (by positivity) (Cm.cone.nonneg k mu)
      simp only [mono, hq, hε₁, h2, h1]
      calc (algebraMap (Φ.V y) (FractionRing (Φ.V y)) (∏ k', Φ.t y k' ^ ((l.M' : ℤ) * Cm.δ (h k') mu mu).toNat)) ^ 2
          = ∏ k', algebraMap (Φ.V y) (FractionRing (Φ.V y)) (ρ (Cm.s (h k'))) ^ ((l.M' : ℤ) * Cm.δ (h k') mu mu).toNat := by
            rw [map_prod, ← Finset.prod_pow]
            refine Finset.prod_congr rfl fun k' _ => ?_
            rw [← (hmem4 k').1, map_pow (algebraMap (Φ.V y) (FractionRing (Φ.V y))) (Φ.t y k') 2]
            rw [map_pow (algebraMap (Φ.V y) (FractionRing (Φ.V y))) (Φ.t y k')]
            exact pow_right_comm (M := FractionRing (Φ.V y)) _ _ _
        _ = ∏ k, algebraMap (Φ.V y) (FractionRing (Φ.V y)) (ρ (Cm.s k)) ^ ((l.M' : ℤ) * Cm.δ k mu mu).toNat :=
            Fintype.prod_equiv h _ _ (fun _ => rfl)
        _ = _ := Finset.prod_congr rfl fun k _ => by rw [← zpow_natCast, Int.toNat_of_nonneg (hnn k)]
    have hcoef := GlobalTheory.T.thetaTerm_coefficient_sq_eq_monomial_subfield ((3 ^ jj) ^ 2) (by omega) (Φ.V y) (Φ.cn y) hU D hPE hTB Cm.P.D.toPre.X Φ.Q p.xe.symm
      (fun mu cc => Φ.u y (fun _ => e.symm mu) cc) (fun mu => mono !![(1 : ℤ)] (Φ.t y) (Φ.δ y) (fun _ => e.symm mu))
      hmo hth K ev₁ k₀ hk τ₁ Cm.m N (fun x => ρ (s x)) ε₁ (fun k => (h3 k).map ρ) hT1 hmo2 W₀ (ρ.comp ιb) hF1
      (fun a => by rw [RingHom.comp_apply, ← RingHom.comp_apply ev₁, hev₁]; exact hkb a)
    have hxne : ∀ k, ev (s (.inr k)) ≠ 0 := fun k => ((h3 k).map ev).ne_zero
    let Uk : Fin N → Kˣ := fun k => Units.mk0 (ev (s (.inr k))) (hxne k)
    have hc1 : ∀ (x : Φ.X y) cc, ∃ r ∈ k₀, ev₁ (Φ.u y (fun _ => x) cc) ^ 2 =
        r * ((∏ k, Uk k ^ ((l.M' : ℤ) * (ε (.inr k) : LinearMap.BilinForm ℤ _) (e x) (e x)) : Kˣ) : K) := by
      intro x cc
      obtain ⟨r, hr, hre⟩ := hcoef (e x) cc
      refine ⟨r, hr, ?_⟩
      simp only [LinearEquiv.symm_apply_apply] at hre
      rw [hre, Units.coe_prod]
      congr 1
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [hε₁, Units.val_zpow_eq_zpow_val, ← RingHom.comp_apply ev₁ ρ, hev₁]
      rfl
    let β' : Fin N → LinearMap.BilinForm ℤ (Φ.X y) := fun k => pull e.toLinearMap (ε (.inr k))
    have hβ' : ∀ k, β' k ∈ balForms (H.bar : 𝓞 E → 𝓞 E) (Φ.X y) := fun k => pull_mem _ (ε (.inr k)).2
    have hlin1 : ∀ {l₀ : ℕ} (a : Fin l₀ × Fin 1 → Φ.X y) (k : Fin N),
        lin !![(1 : ℤ)] a (β' k) = ∑ i', (ε (.inr k) : LinearMap.BilinForm ℤ _) (e (a (i', 0))) (e (a (i', 0))) := by
      intro l₀ a k
      simp [lin, qW, β']
    have hT : ∀ {l₀ : ℕ} (a : Fin l₀ × Fin 1 → Φ.X y) (cs : Fin l₀ → Φ.Q), ∃ R ∈ k₀,
        ev₁ (Φ.coefT y a cs) ^ 2 = R * ((∏ k, Uk k ^ ((l.M' : ℤ) * lin !![(1 : ℤ)] a (β' k)) : Kˣ) : K) := by
      intro l₀ a cs
      choose r hr hre using fun i' => hc1 (a (i', 0)) (cs i')
      refine ⟨∏ i', r i', prod_mem fun i' _ => hr i', ?_⟩
      have ha : ∀ i', (fun v => a (i', v)) = fun _ => a (i', 0) := fun i' => funext fun v => by
        rw [Subsingleton.elim v 0]
      simp only [VSys.coefT, map_prod, ← Finset.prod_pow, ha, hre, Finset.prod_mul_distrib, hlin1, Finset.mul_sum]
      congr 1
      rw [← Units.coe_prod, Finset.prod_comm]
      congr 1
      exact Finset.prod_congr rfl fun k _ => (GlobalTheory.USep.Alg.zpow_sum_units _ _ _).symm
    let F : balForms (H.bar : 𝓞 E → 𝓞 E) (Φ.X y) →ₗ[ℤ] ℤ :=
      (ε.coord (.inr i)).comp (pullBalEquiv (H.bar : 𝓞 E → 𝓞 E) e).symm.toLinearMap
    obtain ⟨n, hn, lam, hlam⟩ := GlobalTheory.USep.Alg.exists_extend_smul (balForms (H.bar : 𝓞 E → 𝓞 E) (Φ.X y)) F
    have hF : ∀ β : balForms (H.bar : 𝓞 E → 𝓞 E) Cm.P.D.toPre.X,
        F ⟨pull e.toLinearMap β, pull_mem _ β.2⟩ = ε.coord (.inr i) β := by
      intro β
      have : (⟨pull e.toLinearMap β, pull_mem _ β.2⟩ : balForms (H.bar : 𝓞 E → 𝓞 E) (Φ.X y)) =
        pullBalEquiv (H.bar : 𝓞 E → 𝓞 E) e β := rfl
      simp only [F, LinearMap.comp_apply, LinearEquiv.coe_coe, this, LinearEquiv.symm_apply_apply]
    have hlam0 : ∀ k, lam (Φ.δ y k) = 0 := by
      intro k
      have e1 : Φ.δ y k = pull e.toLinearMap (((l.M' : ℤ) • ε (.inl (h k)) : balForms (H.bar : 𝓞 E → 𝓞 E) _) :
          LinearMap.BilinForm ℤ _) := LinearMap.ext₂ fun a b => by
        rw [(hmem4 k).2 a b]
        simp [h2]
      have e2 := hlam ⟨pull e.toLinearMap ((l.M' : ℤ) • ε (.inl (h k)) : balForms (H.bar : 𝓞 E → 𝓞 E) _),
        pull_mem _ ((l.M' : ℤ) • ε (.inl (h k))).2⟩
      rw [hF] at e2
      rw [e1, e2, map_zsmul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, if_neg (by simp)]
      simp
    obtain ⟨l₁, l₂, MM, a, a', c₁, c₂, hMM, hu₁, hu₂, hlin, r, hr, hre⟩ := V3 lam hlam0
    obtain ⟨R₁, hR₁, hR₁e⟩ := hT a c₁
    obtain ⟨R₂, hR₂, hR₂e⟩ := hT a' c₂
    have hlam1 : ∀ k, lam (β' k) = n * if i = k then 1 else 0 := by
      intro k
      have e2 := hlam ⟨β' k, hβ' k⟩
      rw [hF (ε (.inr k))] at e2
      rw [e2, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
      by_cases hik : i = k
      · subst hik; simp
      · simp [hik, Ne.symm hik]
    have hG : ((∏ k, Uk k ^ ((l.M' : ℤ) * lin !![(1 : ℤ)] a (β' k)) : Kˣ) : K) =
        ((Uk i ^ ((l.M' : ℤ) * (MM * n)) : Kˣ) : K) * ((∏ k, Uk k ^ ((l.M' : ℤ) * lin !![(1 : ℤ)] a' (β' k)) : Kˣ) : K) := by
      rw [← Units.val_mul]
      congr 1
      have : ∀ k, (l.M' : ℤ) * lin !![(1 : ℤ)] a (β' k) =
          (l.M' : ℤ) * (MM * (n * if i = k then 1 else 0)) + (l.M' : ℤ) * lin !![(1 : ℤ)] a' (β' k) := fun k => by
        rw [← hlam1, ← hlin _ (hβ' k)]; ring
      simp only [this, zpow_add, Finset.prod_mul_distrib]
      congr 1
      rw [Finset.prod_eq_single i (fun k _ hk => by rw [if_neg (Ne.symm hk)]; simp) (by simp)]
      simp
    have hne : ev₁ (Φ.coefT y a c₁) ^ 2 ≠ 0 := pow_ne_zero _ (hu₁.map ev₁).ne_zero
    have hR₁ne : R₁ ≠ 0 := fun h0 => hne (by rw [hR₁e, h0, zero_mul])
    have key : ((Uk i ^ ((l.M' : ℤ) * (MM * n)) : Kˣ) : K) = r ^ 2 * R₂ / R₁ := by
      have h5 : R₁ * (((Uk i ^ ((l.M' : ℤ) * (MM * n)) : Kˣ) : K) *
          ((∏ k, Uk k ^ ((l.M' : ℤ) * lin !![(1 : ℤ)] a' (β' k)) : Kˣ) : K)) =
          r ^ 2 * (R₂ * ((∏ k, Uk k ^ ((l.M' : ℤ) * lin !![(1 : ℤ)] a' (β' k)) : Kˣ) : K)) := by
        rw [← hG, ← hR₁e, ← hR₂e, hre, mul_pow]
      rw [eq_div_iff hR₁ne]
      have hP : ((∏ k, Uk k ^ ((l.M' : ℤ) * lin !![(1 : ℤ)] a' (β' k)) : Kˣ) : K) ≠ 0 := Units.ne_zero _
      apply mul_right_cancel₀ hP
      linear_combination h5
    have hmem' : ev (s (.inr i)) ^ ((l.M' : ℤ) * (MM * n)) ∈ k₀ := by
      have : ev (s (.inr i)) ^ ((l.M' : ℤ) * (MM * n)) = ((Uk i ^ ((l.M' : ℤ) * (MM * n)) : Kˣ) : K) := by
        rw [Units.val_zpow_eq_zpow_val]; rfl
      rw [this, key]
      exact div_mem (mul_mem (pow_mem hr 2) hR₂) hR₁
    refine GlobalTheory.USep.Alg.mem_of_zpow_mem k₀ hk (hxne i) ?_ hmem'
    have : (l.M' : ℤ) ≠ 0 := by exact_mod_cast (show l.M' ≠ 0 by omega)
    exact mul_ne_zero this (mul_ne_zero (by exact_mod_cast (show MM ≠ 0 by omega)) hn)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparationNormalizedBlowupUnitaryCompactificatioStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.separation_normalizedBlowup_unitaryCompactification : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (d : ℕ) (J : C.Z.IdealSheafData), 1 ≤ d → (∀ x ∈ J.support, x ∉ Set.range C.i) → UValOn Xo c C.i φ J d → ∀ (S : Scheme.{0}) (π : S ⟶ pullback C.z (spMap C.b)) (j : Xo.XF c ⟶ S), GlobalTheory.Poinc.IsNormBl π (J.comap (pullback.fst C.z (spMap C.b))) → IsProper π → j ≫ π = C.iF → IsOpenImmersion j → π ⁻¹' Set.range C.iF = Set.range j → GlobalTheory.UChart.SepB Xo c φ j) := by
  first | exact @GlobalTheory.USep.sepB_of_normBl | exact GlobalTheory.USep.sepB_of_normBl | (intros; apply GlobalTheory.USep.sepB_of_normBl <;> assumption)
end
