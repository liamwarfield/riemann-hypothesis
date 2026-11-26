module

public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ToZIsArFunIff
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.WZIsCInfStatement

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ArchIntToZEq
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ArchIntToZEq
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem archInt_toZ : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (D : ℕ), IsArithVar p D → ∀ (N M : HermLB p) (hN : ∀ τ, (wZ N t τ).IsCInf) (hM : ∀ τ, (wZ M t τ).IsCInf) (e : ℕ) (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r), ((toZ N t hN).ArchIntegrable (toZ M t hM) e hr ↔ N.ArchIntegrable M e hr) ∧ (N.ArchIntegrable M e hr → (toZ N t hN).archInt (toZ M t hM) e hr = N.archInt M e hr) := by
  intro k _ X _ p t D hX N M hN hM e r hr
  have W := fun τ : ℤ →+* ℂ => GlobalTheory.T.archIntegrable_iff_over_integers k X p t τ D hX N M (wZ N t τ) (wZ M t τ)
    (wOver_wZ N t τ) (wOver_wZ M t τ) (hN τ) e r hr
  let τ₀ : ℤ →+* ℂ := Int.castRingHom ℂ
  have hu : ∀ τ : ℤ →+* ℂ, τ = τ₀ := fun τ => Subsingleton.elim _ _
  refine ⟨⟨fun h => (W τ₀).1.1 (h τ₀), fun h τ => (W τ).1.2 h⟩, fun h => ?_⟩
  haveI : Unique (ℤ →+* ℂ) := ⟨⟨τ₀⟩, hu⟩
  unfold HermLB.archInt
  rw [finsum_unique]
  exact (W default).2 h

end GlobalTheory.CompanionTheory.Ar.BaseZ
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ArchIntToZEqStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archInt_toZ_eq : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (D : ℕ), IsArithVar p D → ∀ (N M : HermLB p) (hN : ∀ τ, (wZ N t τ).IsCInf) (hM : ∀ τ, (wZ M t τ).IsCInf) (e : ℕ) (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r), ((toZ N t hN).ArchIntegrable (toZ M t hM) e hr ↔ N.ArchIntegrable M e hr) ∧ (N.ArchIntegrable M e hr → (toZ N t hN).archInt (toZ M t hM) e hr = N.archInt M e hr) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BaseZ.archInt_toZ | exact GlobalTheory.CompanionTheory.Ar.BaseZ.archInt_toZ | (intros; apply GlobalTheory.CompanionTheory.Ar.BaseZ.archInt_toZ <;> assumption)
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem arMix_of_base_int : (∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℤ) (D : ℕ), IsArithVar p D → ∀ (ι : Type) [Fintype ι] (M : HermLB p) (L : ι → HermLB p) (Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ), IsArFun (fun o : Option ι => o.elim M L) D Φ → ∀ (n : ι → ℤ) (h : X → ℝ), (comb L n).IsArithHeight h → ∀ (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r), (comb L n).ArchIntegrable M D hr ∧ Φ (MvPolynomial.X none * MvPolynomial.rename some (lin fun i => (n i : ℝ)) ^ D) = ∑ᶠ z, ((M.div hr).mult z : ℝ) * h z - (comb L n).archInt M D hr) → GlobalTheory.Published.ArMix := by
  intro H k _ X _ _ p D hX ι _ M L Φ hΦ n h hh r hr
  haveI := hX.finite
  let t : X ⟶ Sp ℤ := p ≫ spMap (Int.castRingHom k)
  have hX' : IsArithVar t D := isArithVar_int k X p t D hX
  have Hc : ∀ (N : HermLB p) (τ : ℤ →+* ℂ), (wZ N t τ).IsCInf := fun N τ => GlobalTheory.T.wZ_isCInf' k X p t N τ
  have hΦ' : IsArFun (fun o : Option ι => o.elim (toZ M t (Hc M)) fun i => toZ (L i) t (Hc (L i))) D Φ := by
    have e := (GlobalTheory.T.toZ_isArFun_iff k X p t D hX (Option ι) (fun o : Option ι => o.elim M L)
      (fun o => Hc _) Φ).2 hΦ
    convert e using 2 with o
    cases o <;> rfl
  have iso : (toZ (comb L n) t (Hc _)).Isometric (comb (fun i => toZ (L i) t (Hc (L i))) n) :=
    (GlobalTheory.T.toZ_pow_comb_isometric k X p t Hc).2 ι L n
  have hh' : (comb (fun i => toZ (L i) t (Hc (L i))) n).IsArithHeight h :=
    iso.isArithHeight hX' ((GlobalTheory.T.toZ_isArithHeight_iff k X p t D hX (comb L n) (Hc _) h).2 hh)
  obtain ⟨h₁, h₂⟩ := H X t D hX' ι (toZ M t (Hc M)) (fun i => toZ (L i) t (Hc (L i))) Φ hΦ' n h hh' r hr
  have hA : (toZ (comb L n) t (Hc _)).ArchIntegrable (toZ M t (Hc M)) D hr := fun τ => by
    rw [iso.chernIntegrableOn_eq]
    exact h₁ τ
  have hI : (comb (fun i => toZ (L i) t (Hc (L i))) n).archInt (toZ M t (Hc M)) D hr =
      (toZ (comb L n) t (Hc _)).archInt (toZ M t (Hc M)) D hr := by
    simp only [HermLB.archInt, iso.chernInt_eq]
  obtain ⟨e₁, e₂⟩ := GlobalTheory.T.archInt_toZ_eq k X p t D hX (comb L n) M (Hc _) (Hc _) D r hr
  have hB := e₁.1 hA
  refine ⟨hB, h₂.trans ?_⟩
  rw [hI, e₂ hB]
  rfl

end GlobalTheory.CompanionTheory.Ar.BaseZ
