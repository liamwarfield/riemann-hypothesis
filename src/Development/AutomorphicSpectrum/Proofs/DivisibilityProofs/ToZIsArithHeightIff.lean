module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ArchIntegrableIffOverIntegers

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SumLogNormEqSumEmbeddings
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SumLogNormEqSumEmbeddings
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

def sheetEquiv {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) :
    (Σ σ : k →+* ℂ, CxPts p σ) ≃ CxPts t τ where
  toFun s := sheet t τ s.2
  invFun y := ⟨emb p y, unsheet p y⟩
  left_inv := by
    rintro ⟨σ, y⟩
    have key : ∀ (σ' : k →+* ℂ) (_ : σ' = σ) (y' : CxPts p σ'), y'.1 = y.1 →
        (⟨σ', y'⟩ : Σ σ : k →+* ℂ, CxPts p σ) = ⟨σ, y⟩ := by
      rintro σ' rfl y' h
      rw [Subtype.ext h]
    exact key _ (emb_sheet t τ y) _ rfl
  right_inv y := sheet_unsheet p y

theorem finite_sigma_cxPts {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    (hX : IsArithVar p 0) : Finite (Σ σ : k →+* ℂ, CxPts p σ) := by
  have : Finite (X.residueField (genericPoint X) →+* ℂ) := by
    by_cases h : Nonempty (X.residueField (genericPoint X) →+* ℂ)
    · obtain ⟨f⟩ := h
      have := SmallSecHeight.numberField hX f.charZero
      infer_instance
    · have := not_nonempty_iff.1 h
      infer_instance
  exact .of_equiv _ (SmallSecHeight.ptsEquiv hX).symm

theorem sum_logNorm_curve : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ), IsArithVar p 0 → ∀ (M : HermLB p) (ν : Weight t τ M.B), WOver M.φ ν → ∀ (r : M.B.ι → X.functionFieldˣ), IsRatSec M.B r → ∑ᶠ y : CxPts t τ, logNorm ν r y = ∑ᶠ σ : k →+* ℂ, ∑ᶠ y : CxPts p σ, logNorm (M.φ σ) r y := by
  intro k _ X _ p t τ hX M ν hν r hr
  have hfin := finite_sigma_cxPts hX
  have (σ : k →+* ℂ) : Finite (CxPts p σ) := .of_injective _ (sigma_mk_injective (i := σ))
  have := hX.finite_emb
  have := Fintype.ofFinite (k →+* ℂ)
  have (σ : k →+* ℂ) := Fintype.ofFinite (CxPts p σ)
  have h₁ (σ : k →+* ℂ) (y : CxPts p σ) : logNorm ν r (sheet t τ y) = logNorm (M.φ σ) r y :=
    GlobalTheory.T.logNorm_sheet_eq k X p t τ M.B M.φ ν hν r hr σ y (mem_offSupp.2 (by
      rw [hX.under_eq_genericPoint]
      exact CartierDiv.genericPoint_notMem_supp _))
  rw [← finsum_comp_equiv (sheetEquiv p t τ)]
  simp only [finsum_eq_sum_of_fintype]
  rw [Fintype.sum_sigma]
  exact Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun y _ => h₁ σ y

end GlobalTheory.CompanionTheory.Ar.BaseZ
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SumLogNormEqSumEmbeddingsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_logNorm_eq_sum_embeddings : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ), IsArithVar p 0 → ∀ (M : HermLB p) (ν : Weight t τ M.B), WOver M.φ ν → ∀ (r : M.B.ι → X.functionFieldˣ), IsRatSec M.B r → ∑ᶠ y : CxPts t τ, logNorm ν r y = ∑ᶠ σ : k →+* ℂ, ∑ᶠ y : CxPts p σ, logNorm (M.φ σ) r y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BaseZ.sum_logNorm_curve | exact GlobalTheory.CompanionTheory.Ar.BaseZ.sum_logNorm_curve | (intros; apply GlobalTheory.CompanionTheory.Ar.BaseZ.sum_logNorm_curve <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.WOverRestrPow
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem WOver.pow {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {t : X ⟶ Sp ℤ} {τ : ℤ →+* ℂ}
    {B : LB X} {φ : ∀ σ : k →+* ℂ, Weight p σ B} {ψ : Weight t τ B} (h : WOver φ ψ) (m : ℕ) :
    WOver (fun σ => (φ σ).pow m) (ψ.pow m) := by
  intro σ j y hy
  refine (ψ.zpow_φ _ j _).trans (Eq.trans ?_ ((φ σ).zpow_φ _ j y).symm)
  exact congrArg _ (h σ _ y (mem_pow_iff.1 hy))

theorem WOver.restr {k : Type} [CommRing k] {X Z : Scheme.{0}} {p : X ⟶ Sp k} {t : X ⟶ Sp ℤ} {τ : ℤ →+* ℂ}
    {B : LB X} {φ : ∀ σ : k →+* ℂ, Weight p σ B} {ψ : Weight t τ B} (h : WOver φ ψ) (i : Z ⟶ X) :
    WOver (p := i ≫ p) (t := i ≫ t) (fun σ => (φ σ).pull i rfl) (ψ.pull i rfl) := by
  intro σ j y hy
  have hm : PtsOver.map i rfl _ y ∈ ptsIn p σ (B.U (j PUnit.unit)) :=
    mem_of_mem_linComb (m := fun _ => PtsOver.map i rfl _ y) (fun _ => rfl) hy PUnit.unit
  refine (ψ.pull_φ i rfl j _).trans (Eq.trans ?_ ((φ σ).pull_φ i rfl j y).symm)
  exact h σ _ _ hm

theorem wOver_restr_pow : ∀ (k : Type) [CommRing k] (X Z : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (i : Z ⟶ X) (L : HermLB p) (hL : ∀ τ, (wZ L t τ).IsCInf) (τ : ℤ →+* ℂ), WOver (L.restr i).φ (((toZ L t hL).restr i).φ τ) ∧ ∀ m : ℕ, WOver ((L.restr i).pow m).φ ((((toZ L t hL).restr i).pow m).φ τ) := by
  intro k _ X Z p t i L hL τ
  have h : WOver (L.restr i).φ (((toZ L t hL).restr i).φ τ) := (wOver_wZ L t τ).restr i
  exact ⟨h, fun m => h.pow m⟩

end GlobalTheory.CompanionTheory.Ar.BaseZ
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ToZIsArithHeightIff
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem curveDeg_toZ {k : Type} [CommRing k] {X Z : Scheme.{0}} {p : X ⟶ Sp k} (t : X ⟶ Sp ℤ) {D : ℕ}
    (hX : IsArithVar p D) (L : HermLB p) (hL : ∀ τ, (wZ L t τ).IsCInf) (i : Z ⟶ X) [IsClosedImmersion i]
    [IsIntegral Z] [IsLocallyNoetherian Z] (hc : CharZero Γ(Z, ⊤)) (hd : topologicalKrullDim Z = 1)
    (r : (L.restr i).B.ι → Z.functionFieldˣ) (hr : IsRatSec (L.restr i).B r) :
    HermLB.curveDeg ((toZ L t hL).restr i) (r := r) hr = HermLB.curveDeg (L.restr i) hr := by
  have hv : IsArithVar (i ≫ p) 0 := hX.of_isClosedImmersion i hc (by simpa using hd)
  have e := GlobalTheory.T.sum_logNorm_eq_sum_embeddings k Z (i ≫ p) (i ≫ t) (Int.castRingHom ℂ) hv (L.restr i)
    (((toZ L t hL).restr i).φ (Int.castRingHom ℂ))
    (wOver_restr_pow k X Z p t i L hL _).1 r hr
  unfold HermLB.curveDeg
  refine congrArg (_ - ·) ?_
  rw [finsum_eq_single _ (Int.castRingHom ℂ) fun τ h => absurd (RingHom.ext_int _ _) h]
  exact e

theorem arch_toZ {k : Type} [CommRing k] {X Z : Scheme.{0}} {p : X ⟶ Sp k} (t : X ⟶ Sp ℤ) {D : ℕ}
    (hX : IsArithVar p D) (L : HermLB p) (hL : ∀ τ, (wZ L t τ).IsCInf) (i : Z ⟶ X) [IsClosedImmersion i]
    [IsIntegral Z] (hc : CharZero Γ(Z, ⊤)) (e : ℕ) (hd : topologicalKrullDim Z = (e + 1 : ℕ)) (m : ℕ)
    (r : ((L.restr i).pow m).B.ι → Z.functionFieldˣ) (hr : IsRatSec ((L.restr i).pow m).B r) :
    (HermLB.ArchIntegrable ((toZ L t hL).restr i) ((toZ L t hL).restr i |>.pow m) (r := r) e hr ↔
      HermLB.ArchIntegrable (L.restr i) ((L.restr i).pow m) e hr) ∧
    (HermLB.ArchIntegrable (L.restr i) ((L.restr i).pow m) e hr →
      HermLB.archInt ((toZ L t hL).restr i) ((toZ L t hL).restr i |>.pow m) (r := r) e hr =
        HermLB.archInt (L.restr i) ((L.restr i).pow m) e hr) := by
  have hv : IsArithVar (i ≫ p) e := hX.of_isClosedImmersion i hc hd
  have hw := wOver_restr_pow k X Z p t i L hL (Int.castRingHom ℂ)
  obtain ⟨e₁, e₂⟩ := GlobalTheory.T.archIntegrable_iff_over_integers k Z (i ≫ p) (i ≫ t) (Int.castRingHom ℂ) e hv (L.restr i)
    ((L.restr i).pow m) (((toZ L t hL).restr i).φ (Int.castRingHom ℂ))
    ((((toZ L t hL).restr i).pow m).φ (Int.castRingHom ℂ)) hw.1 (hw.2 m)
    (((toZ L t hL).restr i).cInf _) e r hr
  have hτ (τ : ℤ →+* ℂ) : τ = Int.castRingHom ℂ := RingHom.ext_int _ _
  refine ⟨⟨fun H => e₁.1 (H _), fun H τ => ?_⟩, fun H => ?_⟩
  · rw [hτ τ]
    exact e₁.2 H
  · unfold HermLB.archInt
    rw [finsum_eq_single _ (Int.castRingHom ℂ) fun τ h => absurd (hτ τ) h]
    exact e₂ H

theorem isArithHeight_toZ_iff : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (D : ℕ), IsArithVar p D → ∀ (L : HermLB p) (hL : ∀ τ, (wZ L t τ).IsCInf) (h : X → ℝ), (toZ L t hL).IsArithHeight h ↔ L.IsArithHeight h := by
  intro k _ X p t D hX L hL h
  refine ⟨fun H => ⟨H.vertical, ?_, ?_⟩, fun H => ⟨H.vertical, ?_, ?_⟩⟩
  · intro Z i _ _ _ hc hd r hr
    exact (H.point Z i hc hd r hr).trans (curveDeg_toZ t hX L hL i hc hd r hr)
  · intro Z i _ _ _ hc e he hd m r hr
    obtain ⟨e₁, e₂⟩ := arch_toZ t hX L hL i hc e hd m r hr
    obtain ⟨h₁, h₂⟩ := H.recursion Z i hc e he hd m r hr
    have h₃ := e₁.1 h₁
    exact ⟨h₃, h₂.trans (congrArg (_ - ·) (e₂ h₃))⟩
  · intro Z i _ _ _ hc hd r hr
    exact (H.point Z i hc hd r hr).trans (curveDeg_toZ t hX L hL i hc hd r hr).symm
  · intro Z i _ _ _ hc e he hd m r hr
    obtain ⟨e₁, e₂⟩ := arch_toZ t hX L hL i hc e hd m r hr
    obtain ⟨h₁, h₂⟩ := H.recursion Z i hc e he hd m r hr
    exact ⟨e₁.2 h₁, h₂.trans (congrArg (_ - ·) (e₂ h₁).symm)⟩

end GlobalTheory.CompanionTheory.Ar.BaseZ
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ToZIsArithHeightIffStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toZ_isArithHeight_iff : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (D : ℕ), IsArithVar p D → ∀ (L : HermLB p) (hL : ∀ τ, (wZ L t τ).IsCInf) (h : X → ℝ), (toZ L t hL).IsArithHeight h ↔ L.IsArithHeight h := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BaseZ.isArithHeight_toZ_iff | exact GlobalTheory.CompanionTheory.Ar.BaseZ.isArithHeight_toZ_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.BaseZ.isArithHeight_toZ_iff <;> assumption)
end
