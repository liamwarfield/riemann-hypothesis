module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsArithVarInt
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.WZIsCInf
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ToZIsArithHeightIff
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.WZIsCInfStatement

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ToZIsArFunIff
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ToZIsArFunIff
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem isArFun_toZ_iff : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (D : ℕ),
    IsArithVar p D → ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p) (hL : ∀ i τ, (wZ (L i) t τ).IsCInf)
    (Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ), IsArFun (fun i => toZ (L i) t (hL i)) D Φ ↔ IsArFun L D Φ := by
  intro k _ X _ p t D hX ι _ L hL Φ
  have : Module.Finite ℤ k := hX.finite
  have H : ∀ (M : HermLB p) (τ : ℤ →+* ℂ), (wZ M t τ).IsCInf := fun M τ => GlobalTheory.T.wZ_isCInf' k X p t M τ
  have hZ : IsArithVar t D := isArithVar_int k X p t D hX
  have key : ∀ (n : ι → ℤ) (a : ℝ),
      (comb (fun i => toZ (L i) t (hL i)) n).IsSelfInter a ↔ (comb L n).IsSelfInter a := by
    intro n a
    have e : (toZ (comb L n) t (H _)).Isometric (comb (fun i => toZ (L i) t (hL i)) n) :=
      (GlobalTheory.T.toZ_pow_comb_isometric k X p t H).2 ι L n
    constructor
    · intro h₀
      obtain ⟨h, h₁, h₂⟩ := e.symm.isSelfInter hZ h₀
      exact ⟨h, (GlobalTheory.T.toZ_isArithHeight_iff k X p t D hX (comb L n) (H _) h).1 h₁, h₂⟩
    · rintro ⟨h, h₁, h₂⟩
      exact e.isSelfInter hZ ⟨h, (GlobalTheory.T.toZ_isArithHeight_iff k X p t D hX (comb L n) (H _) h).2 h₁, h₂⟩
  exact ⟨fun h => ⟨fun n => (key n _).1 (h.1 n), h.2⟩, fun h => ⟨fun n => (key n _).2 (h.1 n), h.2⟩⟩

end GlobalTheory.CompanionTheory.Ar.BaseZ
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ToZIsArFunIffStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toZ_isArFun_iff : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (D : ℕ), IsArithVar p D → ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p) (hL : ∀ i τ, (wZ (L i) t τ).IsCInf) (Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ), IsArFun (fun i => toZ (L i) t (hL i)) D Φ ↔ IsArFun L D Φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BaseZ.isArFun_toZ_iff | exact GlobalTheory.CompanionTheory.Ar.BaseZ.isArFun_toZ_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.BaseZ.isArFun_toZ_iff <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HeightProjectionOfInt
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ToZPullIsometric
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ToZPullIsometric
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem isometric_toZ_pull : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (t : X ⟶ Sp ℤ) (t' : Y ⟶ Sp ℤ) (π : Y ⟶ X) (hπ : π ≫ p = q) (hπ' : π ≫ t = t') (L : HermLB p) (hL : ∀ τ, (wZ L t τ).IsCInf) (hL' : ∀ τ, (wZ (L.pull π hπ) t' τ).IsCInf), (toZ (L.pull π hπ) t' hL').Isometric ((toZ L t hL).pull π hπ') := by
  intro k _ X Y p q t t' π hπ hπ' L hL hL'
  refine HermLB.isometric_of_eqOn fun τ a y _ => ?_
  have key : ∀ (σ σ' : k →+* ℂ) (_ : σ = σ') (z : CxPts p σ) (z' : CxPts p σ'), z.1 = z'.1 →
      (L.φ σ).φ (a PUnit.unit) z = (L.φ σ').φ (a PUnit.unit) z' := by
    rintro σ _ rfl z z' h
    rw [Subtype.ext h]
  refine (Weight.pull_φ (wZ L t τ) π hπ' a y).trans (Eq.trans ?_ (Weight.pull_φ (L.φ (emb q y)) π hπ a (unsheet q y)).symm)
  refine key _ _ ?_ _ _ rfl
  have e : (PtsOver.map π hπ' _ y).1 ≫ p = y.1 ≫ q := by
    rw [← hπ]
    exact Category.assoc _ _ _
  show (Spec.preimage ((PtsOver.map π hπ' _ y).1 ≫ p)).hom = (Spec.preimage (y.1 ≫ q)).hom
  rw [e]

end GlobalTheory.CompanionTheory.Ar.BaseZ
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ToZPullIsometricStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toZ_pull_isometric : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (t : X ⟶ Sp ℤ) (t' : Y ⟶ Sp ℤ) (π : Y ⟶ X) (hπ : π ≫ p = q) (hπ' : π ≫ t = t') (L : HermLB p) (hL : ∀ τ, (wZ L t τ).IsCInf) (hL' : ∀ τ, (wZ (L.pull π hπ) t' τ).IsCInf), (toZ (L.pull π hπ) t' hL').Isometric ((toZ L t hL).pull π hπ') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BaseZ.isometric_toZ_pull | exact GlobalTheory.CompanionTheory.Ar.BaseZ.isometric_toZ_pull | (intros; apply GlobalTheory.CompanionTheory.Ar.BaseZ.isometric_toZ_pull <;> assumption)
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem heightProjection_of_int : (∀ (X Y : Scheme.{0}) [IsIntegral Y] (p : X ⟶ Sp ℤ) (q : Y ⟶ Sp ℤ) (D e : ℕ), IsArithVar p D → IsArithVar q e → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), topologicalKrullDim (closure ({π (genericPoint Y)} : Set X)) = (e + 1 : ℕ) → π.residueDegree (genericPoint Y) ≠ 0 → ∀ (L : HermLB p) (h : X → ℝ), L.IsArithHeight h → (L.pull π hπ).IsSelfInter ((π.residueDegree (genericPoint Y) : ℝ) * h (π (genericPoint Y)))) → GlobalTheory.Published.HeightProjection := by
  intro H k _ X Y _ p q D e hp hq π hπ hdim hdeg L h hL
  haveI : Module.Finite ℤ k := hp.finite
  have hc : ∀ τ : ℤ →+* ℂ, (wZ L (p ≫ spMap (Int.castRingHom k)) τ).IsCInf :=
    GlobalTheory.T.wZ_isCInf' k X p (p ≫ spMap (Int.castRingHom k)) L
  have hc' : ∀ τ : ℤ →+* ℂ,
      (wZ (L.pull π hπ) (π ≫ p ≫ spMap (Int.castRingHom k)) τ).IsCInf :=
    GlobalTheory.T.wZ_isCInf' k Y q (π ≫ p ≫ spMap (Int.castRingHom k)) (L.pull π hπ)
  have htX : GlobalTheory.IsArithVar (p ≫ spMap (Int.castRingHom k)) D :=
    isArithVar_int k X p _ D hp
  have htY : GlobalTheory.IsArithVar (π ≫ p ≫ spMap (Int.castRingHom k)) e :=
    isArithVar_int k Y q _ e hq
  have hLZ : (toZ L (p ≫ spMap (Int.castRingHom k)) hc).IsArithHeight h :=
    (GlobalTheory.T.toZ_isArithHeight_iff k X p _ D hp L hc h).mpr hL
  have key := H X Y (p ≫ spMap (Int.castRingHom k)) (π ≫ p ≫ spMap (Int.castRingHom k)) D e
    htX htY π rfl hdim hdeg (toZ L (p ≫ spMap (Int.castRingHom k)) hc) h hLZ
  have iso := GlobalTheory.T.toZ_pull_isometric k X Y p q (p ≫ spMap (Int.castRingHom k))
    (π ≫ p ≫ spMap (Int.castRingHom k)) π hπ rfl L hc hc'
  obtain ⟨h', hh', hv⟩ := GlobalTheory.HermLB.Isometric.isSelfInter htY iso.symm key
  exact ⟨h', (GlobalTheory.T.toZ_isArithHeight_iff k Y q _ e hq (L.pull π hπ) hc' h').mp hh', hv⟩

end GlobalTheory.CompanionTheory.Ar.BaseZ
end
