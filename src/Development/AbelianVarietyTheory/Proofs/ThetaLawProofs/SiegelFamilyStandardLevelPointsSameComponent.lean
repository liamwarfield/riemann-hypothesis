module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BijectiveTensorOmegaStd
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SiegelFamilyNearbyPeriodsSameComponent

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsPeriodLevelOfSiegelPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsPeriodLevelOfSiegelPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.SiegelObject

open GlobalTheory.TensorSiegel

theorem exists_lattice_form {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (hs : τ.IsSymm)
    (hp : (τ.map Complex.im).PosDef) :
    ∃ (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (Ef : LinearMap.BilinForm ℤ Λ),
      DiscreteTopology Λ ∧ Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ ∧ Hm.IsHermitian ∧
      (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
      (∀ a b : Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧ Function.Bijective Ef ∧
      (∀ z, z ∈ Λ ↔ ∃ a, z = per τ a) ∧
      ∀ a b, (hermForm Hm (per τ a) (per τ b)).im = omegaStd a b := by
  let σ : Fin 1 × Fin g ≃ Fin g := Equiv.uniqueProd _ _
  let G : Matrix (Fin 1) (Fin 1) ℤ := 1
  have hG : (G.map (Int.cast : ℤ → ℝ)).PosDef := by
    rw [show G.map (Int.cast : ℤ → ℝ) = 1 from Matrix.map_one _ Int.cast_zero Int.cast_one]
    exact Matrix.PosDef.one
  have hper : ∀ x : Fin 1 → (Fin g ⊕ Fin g → ℤ), period σ τ x = per τ (x 0) := fun x => by
    funext i
    exact period_apply σ τ x 0 i
  have hsum : ∀ x y : Fin 1 → (Fin g ⊕ Fin g → ℤ),
      ∑ u, ∑ v, G u v * omegaStd (x u) (y v) = omegaStd (x 0) (y 0) := fun x y => by simp [G]
  let EF : LinearMap.BilinForm ℤ (Fin 1 → (Fin g ⊕ Fin g → ℤ)) :=
    LinearMap.mk₂ ℤ (fun x y => omegaStd (x 0) (y 0))
      (fun x x' y => by
        simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring)
      (fun c x y => by
        simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring)
      (fun x y y' => by
        simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring)
      (fun c x y => by
        simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring)
  have hEF : Function.Bijective EF :=
    bijective_tensor_omegaStd G (by simp [G]) EF fun x y => (hsum x y).symm
  obtain ⟨h1, h2, h3⟩ := period_isLattice σ hp
  have him := im_formMatrix_period σ G hs hp
  let Q := (period σ τ).toIntLinearMap
  let e := LinearEquiv.ofInjective Q h1
  refine ⟨LinearMap.range Q, formMatrix σ (G.map (Int.cast : ℤ → ℝ)) τ,
    e.symm.dualMap.toLinearMap ∘ₗ EF ∘ₗ e.symm.toLinearMap, h2, h3, formMatrix_isHermitian σ hG hp,
    fun z hz => formMatrix_pos σ hG hp hz, fun a b => ?_,
    e.symm.dualMap.bijective.comp (hEF.comp e.symm.bijective), fun z => ?_, fun a b => ?_⟩
  · obtain ⟨x, rfl⟩ := e.surjective a
    obtain ⟨y, rfl⟩ := e.surjective b
    refine Eq.trans ?_ (him x y).symm
    rw [hsum]
    simp [EF]
  · exact ⟨fun ⟨x, hx⟩ => ⟨x 0, hx.symm.trans (hper x)⟩, fun ⟨a, ha⟩ => ⟨fun _ => a, (hper _).trans ha.symm⟩⟩
  · have := him (fun _ => a) (fun _ => b)
    rwa [hsum, hper, hper] at this

theorem exists_perLev_of_siegel : ThetaUnifAV → GlobalTheory.TorusAlgebraic → ∀ (g k : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ.IsSymm → (τ.map Complex.im).PosDef → ∃ (P : Out.PolAV (Sp ℂ)) (lev : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)), PerLev P τ k lev := by
  intro hU _ g k τ hs hp
  obtain ⟨Λ, Hm, Ef, h1, h2, h3, h4, h5, h6, hΛ, hω⟩ := exists_lattice_form τ hs hp
  obtain ⟨P, u, χ, hg, rfl, hAH, -⟩ := GlobalTheory.principalTorus_algebraic g Λ Hm Ef h1 h2 h3 h4 h5 h6
  obtain ⟨E', hE', -, -, -, -, hW⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH hU P g u Hm χ hAH
  refine ⟨P, fun a => u.ex ((k : ℂ)⁻¹ • per τ a), hg, hs, hp, u, hΛ, fun n a b c hn hc => ?_, fun _ => rfl⟩
  refine hW n ⟨per τ a, (hΛ _).2 ⟨a, rfl⟩⟩ ⟨per τ b, (hΛ _).2 ⟨b, rfl⟩⟩ c hn ?_
  have h : E' ⟨per τ a, (hΛ _).2 ⟨a, rfl⟩⟩ ⟨per τ b, (hΛ _).2 ⟨b, rfl⟩⟩ = omegaStd a b := by
    have h' := hE' ⟨per τ a, (hΛ _).2 ⟨a, rfl⟩⟩ ⟨per τ b, (hΛ _).2 ⟨b, rfl⟩⟩
    rw [Subtype.coe_mk, Subtype.coe_mk, hω] at h'
    exact Int.cast_injective h'
  rw [h, hc]

end GlobalTheory.SiegelObject
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsPeriodLevelOfSiegelPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_periodLevel_of_siegel_point : ThetaUnifAV → GlobalTheory.TorusAlgebraic → ∀ (g k : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ.IsSymm → (τ.map Complex.im).PosDef → ∃ (P : Out.PolAV (Sp ℂ)) (lev : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)), PerLev P τ k lev := by
  first | exact @GlobalTheory.SiegelObject.exists_perLev_of_siegel | exact GlobalTheory.SiegelObject.exists_perLev_of_siegel | (intros; apply GlobalTheory.SiegelObject.exists_perLev_of_siegel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SiegelFamilyStandardLevelPointsSameComponent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.SiegelConnected

theorem convex_siegel (h : ℕ) :
    Convex ℝ {τ : Matrix (Fin h) (Fin h) ℂ | τ.IsSymm ∧ (τ.map Complex.im).PosDef} := by
  rintro x ⟨hx, hx'⟩ y ⟨hy, hy'⟩ a b ha hb hab
  refine ⟨(hx.smul a).add (hy.smul b), ?_⟩
  have e : (a • x + b • y).map Complex.im = a • x.map Complex.im + b • y.map Complex.im := by
    ext i j
    simp
  rw [e]
  rcases ha.eq_or_lt with rfl | ha'
  · have : b = 1 := by simpa using hab
    subst this
    simpa using hy'
  · exact (hx'.smul ha').add_posSemidef (hy'.posSemidef.smul hb)

variable {o : Type} [CommRing o] {S : Scheme.{0}} {s : S ⟶ Sp o} {σ : o →+* ℂ}

theorem sameComp_symm {p q : Sp ℂ ⟶ S} (h : SameComp s σ p q) : SameComp s σ q p := by
  obtain ⟨hp, hq, H⟩ := h
  refine ⟨hq, hp, fun z => ?_⟩
  rw [← connectedComponent_eq (H z)]
  exact mem_connectedComponent

theorem sameComp_trans {p q r : Sp ℂ ⟶ S} (h : SameComp s σ p q) (h' : SameComp s σ q r) :
    SameComp s σ p r := by
  obtain ⟨hp, hq, H⟩ := h
  obtain ⟨hq', hr, H'⟩ := h'
  refine ⟨hp, hr, fun z => ?_⟩
  rw [connectedComponent_eq (H' z)]
  exact H z

theorem mem_siegel_of_ptAt {h k : ℕ} {ζ : o} {c : SiegPre h k ζ s} {p : Sp ℂ ⟶ S}
    {τ : Matrix (Fin h) (Fin h) ℂ} (H : PtAt c p τ) : τ.IsSymm ∧ (τ.map Complex.im).PosDef := by
  obtain ⟨P, lev, φ, hP, -⟩ := H
  exact ⟨hP.2.1, hP.2.2.1⟩

theorem sameComp_of_ptAt : Out.Laws → Out.Laws2 → ThetaUnifAV → GlobalTheory.TorusAlgebraic → ∀ (h k : ℕ) (K : Type) [Field K] (ζ : K) (σ : K →+* ℂ) (F : SFam h k ζ), 1 ≤ h → 3 ≤ k → Odd k → σ ζ = Complex.exp (-(2 * Real.pi * Complex.I) / k) → ∀ (τ τ' : Matrix (Fin h) (Fin h) ℂ) (p q : Sp ℂ ⟶ F.X), p ≫ F.s = spMap σ → q ≫ F.s = spMap σ → PtAt F.univ p τ → PtAt F.univ q τ' → SameComp F.s σ p q := by
  intro hL hL2 hT hA h k K _ ζ σ F hh hk hodd hζ τ τ' p q hp hq hpτ hqτ
  have hopen := GlobalTheory.T.siegelFamily_nearbyPeriods_same_component hL hL2 hT h k K ζ σ F hh hk hodd hζ
  have hex : ∀ t : Matrix (Fin h) (Fin h) ℂ, t.IsSymm ∧ (t.map Complex.im).PosDef →
      ∃ r : Sp ℂ ⟶ F.X, r ≫ F.s = spMap σ ∧ PtAt F.univ r t := by
    rintro t ⟨ht, ht'⟩
    obtain ⟨P, lev, hP⟩ := GlobalTheory.T.exists_periodLevel_of_siegel_point hT hA h k t ht ht'
    obtain ⟨r, φ, hr, hsq, hlev⟩ := GlobalTheory.KeyFam.exists_point_of_perLev hL h k K ζ σ F hh hk hodd hζ P t lev hP
    exact ⟨r, hr, P, lev, φ, hP, hsq, hlev⟩
  have key := (convex_siegel h).isPreconnected.induction₂'
    (fun t t' => ∀ r : Sp ℂ ⟶ F.X, r ≫ F.s = spMap σ → PtAt F.univ r t →
      ∃ r' : Sp ℂ ⟶ F.X, r' ≫ F.s = spMap σ ∧ PtAt F.univ r' t' ∧ SameComp F.s σ r r')
    (by
      intro x hx
      obtain ⟨r₀, hr₀, hr₀x⟩ := hex x hx
      obtain ⟨N, hN, HN⟩ := hopen x r₀ hr₀ hr₀x
      filter_upwards [mem_nhdsWithin_of_mem_nhds hN, self_mem_nhdsWithin] with y hyN hy
      refine ⟨fun r hr hrx => ?_, fun r hr hry => ⟨r₀, hr₀, hr₀x, HN y hyN r hr hry⟩⟩
      obtain ⟨r', hr', hr'y⟩ := hex y hy
      exact ⟨r', hr', hr'y, sameComp_trans (HN x (mem_of_mem_nhds hN) r hr hrx)
        (sameComp_symm (HN y hyN r' hr' hr'y))⟩)
    (by
      intro x y z _ _ _ hxy hyz r hr hrx
      obtain ⟨r', hr', hr'y, h₁⟩ := hxy r hr hrx
      obtain ⟨r'', hr'', hr''z, h₂⟩ := hyz r' hr' hr'y
      exact ⟨r'', hr'', hr''z, sameComp_trans h₁ h₂⟩)
    (mem_siegel_of_ptAt hpτ) (mem_siegel_of_ptAt hqτ)
  obtain ⟨q', hq', hq'τ, h₁⟩ := key p hp hpτ
  obtain ⟨N, hN, HN⟩ := hopen τ' q hq hqτ
  exact sameComp_trans h₁ (HN τ' (mem_of_mem_nhds hN) q' hq' hq'τ)

end GlobalTheory.SiegelConnected
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SiegelFamilyStandardLevelPointsSameComponentStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelFamily_standard_level_points_same_component : Out.Laws → Out.Laws2 → ThetaUnifAV → GlobalTheory.TorusAlgebraic → ∀ (h k : ℕ) (K : Type) [Field K] (ζ : K) (σ : K →+* ℂ) (F : SFam h k ζ), 1 ≤ h → 3 ≤ k → Odd k → σ ζ = Complex.exp (-(2 * Real.pi * Complex.I) / k) → ∀ (τ τ' : Matrix (Fin h) (Fin h) ℂ) (p q : Sp ℂ ⟶ F.X), p ≫ F.s = spMap σ → q ≫ F.s = spMap σ → PtAt F.univ p τ → PtAt F.univ q τ' → SameComp F.s σ p q := by
  first | exact @GlobalTheory.SiegelConnected.sameComp_of_ptAt | exact GlobalTheory.SiegelConnected.sameComp_of_ptAt | (intros; apply GlobalTheory.SiegelConnected.sameComp_of_ptAt <;> assumption)
end
