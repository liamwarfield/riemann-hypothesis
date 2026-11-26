module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegerUnitSplitPlaceConjugatePrime
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormEqXModMonicOfAdicCompleteInvolution
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormEqXModMonicOfAdicCompleteInvolution
open Polynomial

namespace GlobalTheory.InertNorm

theorem isAdicComplete_map_of_finite {O : Type} [CommRing O] [IsNoetherianRing O] (I : Ideal O)
    [IsAdicComplete I O] (R : Type) [CommRing R] [Algebra O R] [Module.Finite O R] :
    IsAdicComplete (I.map (algebraMap O R)) R := by
  rw [IsAdicComplete.map_algebraMap_iff]
  have : IsHausdorff I R := IsHausdorff.of_le_jacobson I R (IsAdicComplete.le_jacobson I)
  have : IsPrecomplete I R := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isPrecomplete_finite_module I R
  exact ⟨⟩

theorem finite_quotient_map_of_finite {O : Type} [CommRing O] (I : Ideal O) [Finite (O ⧸ I)]
    (R : Type) [CommRing R] [Algebra O R] [Module.Finite O R] :
    Finite (R ⧸ I.map (algebraMap O R)) := by
  have : Module.Finite O (R ⧸ I.map (algebraMap O R)) := inferInstance
  have : Module.Finite (O ⧸ I) (R ⧸ I.map (algebraMap O R)) :=
    Module.Finite.of_restrictScalars_finite O (O ⧸ I) _
  exact Module.finite_of_finite (O ⧸ I)

theorem exists_dvd_mul_map_sub_X : ∀ (O : Type) [CommRing O] [IsNoetherianRing O] (I : Ideal O) [IsAdicComplete I O] [Finite (O ⧸ I)] (c : O →+* O), (∀ x, c (c x) = x) → (∀ x ∈ I, c x ∈ I) → (∃ ω, IsUnit (ω - c ω)) → ∀ f : Polynomial O, f.Monic → f.map c = f → IsUnit (f.coeff 0) → ∃ p : Polynomial O, f ∣ p * p.map c - Polynomial.X := by
  intro O _ _ I _ _ c hcc hcI hω f hf hfc hf0
  have : Module.Finite O (AdjoinRoot f) := (AdjoinRoot.powerBasis' hf).finite
  let J : Ideal (AdjoinRoot f) := I.map (algebraMap O (AdjoinRoot f))
  have : IsAdicComplete J (AdjoinRoot f) := isAdicComplete_map_of_finite I (AdjoinRoot f)
  have : Finite (AdjoinRoot f ⧸ J) := finite_quotient_map_of_finite I (AdjoinRoot f)

  have hev : f.eval₂ ((AdjoinRoot.of f).comp c) (AdjoinRoot.root f) = 0 := by
    rw [← Polynomial.eval₂_map, hfc, AdjoinRoot.eval₂_root]
  let c' : AdjoinRoot f →+* AdjoinRoot f :=
    AdjoinRoot.lift ((AdjoinRoot.of f).comp c) (AdjoinRoot.root f) hev
  have hc'mk : ∀ p : Polynomial O, c' (AdjoinRoot.mk f p) = AdjoinRoot.mk f (p.map c) := by
    intro p
    simp only [c', AdjoinRoot.lift_mk]
    rw [← Polynomial.eval₂_map, ← AdjoinRoot.aeval_eq, Polynomial.aeval_def, AdjoinRoot.algebraMap_eq]
  have hc'of : ∀ x : O, c' (algebraMap O (AdjoinRoot f) x) = algebraMap O (AdjoinRoot f) (c x) := by
    intro x
    simp only [AdjoinRoot.algebraMap_eq, c', AdjoinRoot.lift_of, RingHom.comp_apply]
  have hcomp : c.comp c = RingHom.id O := RingHom.ext hcc
  have hinv : ∀ y, c' (c' y) = y := by
    intro y
    induction y using AdjoinRoot.induction_on with
    | ih p => rw [hc'mk, hc'mk, Polynomial.map_map, hcomp, Polynomial.map_id]
  have hJ : ∀ y ∈ J, c' y ∈ J := by
    have : J ≤ J.comap c' := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      simp only [Ideal.mem_comap, hc'of]
      exact Ideal.mem_map_of_mem _ (hcI x hx)
    exact fun y hy => this hy
  have hω' : ∃ ω, IsUnit (ω - c' ω) := by
    obtain ⟨ω, hu⟩ := hω
    refine ⟨algebraMap O (AdjoinRoot f) ω, ?_⟩
    rw [hc'of, ← map_sub]
    exact hu.map _
  have hroot : c' (AdjoinRoot.root f) = AdjoinRoot.root f := AdjoinRoot.lift_root _

  have hunit : IsUnit (AdjoinRoot.root f) := by
    have h0 : (f - Polynomial.C (f.coeff 0)).coeff 0 = 0 := by simp
    obtain ⟨q, hq⟩ := Polynomial.X_dvd_iff.mpr h0
    have hm : AdjoinRoot.root f * AdjoinRoot.mk f q = -AdjoinRoot.of f (f.coeff 0) := by
      have := congrArg (AdjoinRoot.mk f) hq
      rw [map_sub, AdjoinRoot.mk_self, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C, zero_sub] at this
      exact this.symm
    exact isUnit_of_mul_isUnit_left (hm ▸ (hf0.map (AdjoinRoot.of f)).neg)
  obtain ⟨x, hx⟩ := GlobalTheory.T.exists_norm_eq_fixed_unit_henselian (AdjoinRoot f) J c' hinv hJ hω' (AdjoinRoot.root f) hroot hunit
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  refine ⟨p, ?_⟩
  rw [← AdjoinRoot.mk_eq_zero, map_sub, map_mul, ← hc'mk, hx, AdjoinRoot.mk_X, sub_self]

end GlobalTheory.InertNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormEqXModMonicOfAdicCompleteInvolutionStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_norm_eq_X_mod_monic_of_adicComplete_involution : ∀ (O : Type) [CommRing O] [IsNoetherianRing O] (I : Ideal O) [IsAdicComplete I O] [Finite (O ⧸ I)] (c : O →+* O), (∀ x, c (c x) = x) → (∀ x ∈ I, c x ∈ I) → (∃ ω, IsUnit (ω - c ω)) → ∀ f : Polynomial O, f.Monic → f.map c = f → IsUnit (f.coeff 0) → ∃ p : Polynomial O, f ∣ p * p.map c - Polynomial.X := by
  first | exact @GlobalTheory.InertNorm.exists_dvd_mul_map_sub_X | exact GlobalTheory.InertNorm.exists_dvd_mul_map_sub_X | (intros; apply GlobalTheory.InertNorm.exists_dvd_mul_map_sub_X <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIndEtaleOverEtaleOfIsIndEtale
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIndEtaleOverEtaleOfIsIndEtale
open scoped TensorProduct

namespace GlobalTheory.IndEtaleCancel

theorem isIndEtale_of_etale_of_isIndEtale : ∀ (A W O : Type) [CommRing A] [CommRing W]
    [CommRing O] [Algebra A W] [Algebra A O] [Algebra W O] [IsScalarTower A W O]
    [Algebra.Etale A W], GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap A O) →
      GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap W O) := by
  intro A W O _ _ _ _ _ _ _ _ h
  have hT : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap W (W ⊗[A] O)) :=
    GlobalTheory.isIndEtale_tensorProduct_left A O W h
  obtain ⟨t, ht1, ht2⟩ :=
    (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := A) (S := W)).1 inferInstance
  let g : W →ₐ[A] O := IsScalarTower.toAlgHom A W O
  let μ : W ⊗[A] O →ₐ[W] O := Algebra.TensorProduct.lift (Algebra.ofId W O) (AlgHom.id A O)
    (fun _ _ => Commute.all _ _)
  have hμ : ∀ w o, μ (w ⊗ₜ o) = algebraMap W O w * o := fun w o => by simp [μ]
  let e : W ⊗[A] O := Algebra.TensorProduct.map (AlgHom.id A W) g t
  have he1 : ∀ s : W, ((1 : W) ⊗ₜ[A] (algebraMap W O s) - s ⊗ₜ[A] (1 : O)) * e = 0 := by
    intro s
    have := congrArg (Algebra.TensorProduct.map (AlgHom.id A W) g) (ht1 s)
    simpa [map_mul, map_sub, e, g] using this
  have hμe : μ e = 1 := by
    have H : (μ.restrictScalars A).comp (Algebra.TensorProduct.map (AlgHom.id A W) g) =
        g.comp (Algebra.TensorProduct.lmul' A) := by
      apply Algebra.TensorProduct.ext'
      intro a b
      simp [μ, g, Algebra.TensorProduct.lmul'_apply_tmul, IsScalarTower.algebraMap_apply A W O]
    have := DFunLike.congr_fun H t
    simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars'] at this
    rw [show μ e = _ from this, ht2, map_one]
  have hkey : ∀ x : W ⊗[A] O, e * x = e * ((1 : W) ⊗ₜ[A] μ x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul w o =>
      rw [hμ]
      have h1 : (w ⊗ₜ[A] o : W ⊗[A] O) = (w ⊗ₜ[A] (1 : O)) * ((1 : W) ⊗ₜ[A] o) := by simp
      have h2 : ((1 : W) ⊗ₜ[A] (algebraMap W O w * o) : W ⊗[A] O) =
          ((1 : W) ⊗ₜ[A] algebraMap W O w) * ((1 : W) ⊗ₜ[A] o) := by simp
      linear_combination e * h1 - e * h2 - ((1 : W) ⊗ₜ[A] o) * he1 w
    | add x y hx hy => rw [mul_add, hx, hy, map_add (f := _), TensorProduct.tmul_add, mul_add]
  have hidem : IsIdempotentElem e := by
    show e * e = e
    rw [hkey e, hμe, Algebra.TensorProduct.one_def.symm, mul_one]
  letI : Algebra (W ⊗[A] O) O := μ.toRingHom.toAlgebra
  have hmap : ∀ x, algebraMap (W ⊗[A] O) O x = μ x := fun _ => rfl
  haveI : IsScalarTower W (W ⊗[A] O) O :=
    IsScalarTower.of_algebraMap_eq (fun w => by rw [hmap, μ.commutes])
  haveI : IsLocalization.Away e O := by
    refine IsLocalization.away_of_isIdempotentElem_of_mul hidem (fun x y => ?_) ?_
    · rw [hmap, hmap]
      constructor
      · intro hxy; rw [hkey x, hkey y, hxy]
      · intro hxy
        have hx : μ (e * x) = μ x := by rw [map_mul, hμe, one_mul]
        have hy : μ (e * y) = μ y := by rw [map_mul, hμe, one_mul]
        rw [← hx, ← hy, hxy]
    · intro o
      exact ⟨(1 : W) ⊗ₜ o, by rw [hmap, hμ, map_one, one_mul]⟩
  exact GlobalTheory.IndEtaleLoc.isIndEtale_of_isLocalization W (W ⊗[A] O) O (Submonoid.powers e) hT

end GlobalTheory.IndEtaleCancel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIndEtaleOverEtaleOfIsIndEtaleStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIndEtale_over_etale_of_isIndEtale : ∀ (A W O : Type) [CommRing A] [CommRing W] [CommRing O] [Algebra A W] [Algebra A O] [Algebra W O] [IsScalarTower A W O] [Algebra.Etale A W], GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap A O) → GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap W O) := by
  first | (exact @GlobalTheory.IndEtaleCancel.isIndEtale_of_etale_of_isIndEtale) | (exact GlobalTheory.IndEtaleCancel.isIndEtale_of_etale_of_isIndEtale) | (intros; apply GlobalTheory.IndEtaleCancel.isIndEtale_of_etale_of_isIndEtale  <;> assumption)
end
end
