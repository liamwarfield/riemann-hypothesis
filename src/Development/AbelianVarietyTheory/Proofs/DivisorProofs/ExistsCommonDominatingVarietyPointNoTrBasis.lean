module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsLocEqOfIsLocComp

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalModelAtComplexPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalModelAtComplexPoint
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair

theorem exists_locModel_at_point :
    ∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.EssFiniteType ℂ A] (ε : A →ₐ[ℂ] ℂ),
      ∃ T : Subring (FractionRing A), IsLocModel (algebraMap ℂ (FractionRing A)) T ∧
        RatRes (algebraMap ℂ (FractionRing A)) T ∧
        ∀ a : A, algebraMap A (FractionRing A) a ∈ T ∧
          (ε a = 0 → NonUnit T (algebraMap A (FractionRing A) a)) := by
  intro A _ _ _ _ ε
  let K := FractionRing A
  let P : Ideal A := RingHom.ker (ε : A →+* ℂ)
  haveI : P.IsPrime := RingHom.ker_isPrime _
  have hle : P.primeCompl ≤ nonZeroDivisors A := P.primeCompl_le_nonZeroDivisors
  let B : Subalgebra A K := Localization.subalgebra.ofField K P.primeCompl hle
  haveI hB : IsLocalization P.primeCompl B := Localization.subalgebra.isLocalization_ofField K _ hle
  let b : A →+* B := algebraMap A B
  have hu : ∀ y : P.primeCompl, IsUnit ((ε : A →+* ℂ) y) := fun y => by
    refine isUnit_iff_ne_zero.2 fun h => y.2 ?_
    exact RingHom.mem_ker.2 h
  let ψ : B →+* ℂ := IsLocalization.lift hu
  have hψ : ∀ x, ψ (b x) = ε x := IsLocalization.lift_eq hu
  have hcK : ∀ z : ℂ, algebraMap ℂ K z = algebraMap A K (algebraMap ℂ A z) :=
    fun z => IsScalarTower.algebraMap_apply ℂ A K z
  have hc : ∀ z : ℂ, algebraMap ℂ K z ∈ B.toSubring := fun z => by
    rw [hcK]; exact B.algebraMap_mem _
  have hψc : ∀ z : ℂ, ψ ⟨algebraMap ℂ K z, hc z⟩ = z := fun z => by
    have : (⟨algebraMap ℂ K z, hc z⟩ : B) = b (algebraMap ℂ A z) := Subtype.ext (hcK z)
    rw [this, hψ]; exact ε.commutes z
  have key : ∀ x : B, ψ x = 0 → NonUnit B.toSubring (x : K) := fun x hx => by
    refine (nonUnit_iff (R := B.toSubring) x).2 fun h => ?_
    have := h.map ψ
    rw [hx] at this
    exact not_isUnit_zero this
  refine ⟨B.toSubring, ⟨hc, IsLocalization.AtPrime.isLocalRing B P, ?_, ?_⟩, ?_, fun a => ?_⟩
  · have e : (algebraMap ℂ K).codRestrict B.toSubring hc = b.comp (algebraMap ℂ A) := by
      ext z; exact hcK z
    rw [e]
    refine RingHom.EssFiniteType.comp ?_ ?_
    · exact RingHom.essFiniteType_algebraMap.2 (inferInstance : Algebra.EssFiniteType ℂ A)
    · exact (RingHom.essFiniteType_algebraMap (R := A) (S := B)).2
        (Algebra.EssFiniteType.of_isLocalization B P.primeCompl)
  · intro f
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := A) f
    have hy' : algebraMap A K y ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
    exact ⟨_, B.algebraMap_mem x, _, B.algebraMap_mem y, hy', div_mul_cancel₀ _ hy'⟩
  · intro r hr
    refine ⟨ψ ⟨r, hr⟩, key (⟨r, hr⟩ - ⟨algebraMap ℂ K (ψ ⟨r, hr⟩), hc _⟩) ?_⟩
    rw [ψ.map_sub, hψc, sub_self]
  · refine ⟨B.algebraMap_mem a, fun ha => key (b a) ?_⟩
    rw [hψ, ha]

end GlobalTheory.FieldPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalModelAtComplexPointStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localModel_at_complexPoint : ∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.EssFiniteType ℂ A] (ε : A →ₐ[ℂ] ℂ),
  ∃ T : Subring (FractionRing A), IsLocModel (algebraMap ℂ (FractionRing A)) T ∧
    RatRes (algebraMap ℂ (FractionRing A)) T ∧
    ∀ a : A, algebraMap A (FractionRing A) a ∈ T ∧ (ε a = 0 → NonUnit T (algebraMap A (FractionRing A) a)) := by
  first | exact @GlobalTheory.FieldPair.exists_locModel_at_point | exact GlobalTheory.FieldPair.exists_locModel_at_point | (intros; apply GlobalTheory.FieldPair.exists_locModel_at_point <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsResidueToComplexOfRationalResidue
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsResidueToComplexOfRationalResidue
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.FieldPair

theorem exists_residue_complex : ∀ {K : Type} [Field K] [Algebra ℂ K] (R : Subring K) (h : IsLocModel (algebraMap ℂ K) R),
  RatRes (algebraMap ℂ K) R →
  ∃ ε : R →+* ℂ, (∀ a : ℂ, ε ⟨algebraMap ℂ K a, h.const_mem a⟩ = a) ∧ ∀ r : R, ε r = 0 ↔ NonUnit R (r : K) := by
  intro K _ _ R h hr
  haveI := h.isLocalRing
  let c0 : ℂ →+* R := (algebraMap ℂ K).codRestrict R h.const_mem
  let φ : ℂ →+* IsLocalRing.ResidueField R := (IsLocalRing.residue R).comp c0
  have hφ : Function.Bijective φ := by
    refine ⟨φ.injective, fun y => ?_⟩
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨a, ha⟩ := hr r r.2
    refine ⟨a, ?_⟩
    have hn : NonUnit R ((r - c0 a : R) : K) := by simpa [c0] using ha
    have hm : r - c0 a ∈ IsLocalRing.maximalIdeal R :=
      (IsLocalRing.mem_maximalIdeal _).2 ((nonUnit_iff (R := R) (r - c0 a)).1 hn)
    have := (IsLocalRing.residue_eq_zero_iff (r - c0 a)).2 hm
    rw [map_sub, sub_eq_zero] at this
    exact this.symm
  let e := RingEquiv.ofBijective φ hφ
  refine ⟨e.symm.toRingHom.comp (IsLocalRing.residue R), fun a => ?_, fun r => ?_⟩
  · show e.symm (φ a) = a
    exact e.symm_apply_apply a
  · rw [nonUnit_iff (R := R) r, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      map_eq_zero_iff _ e.symm.injective, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff]

end GlobalTheory.FieldPair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsResidueToComplexOfRationalResidueStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_residue_to_complex_of_rationalResidue : ∀ {K : Type} [Field K] [Algebra ℂ K] (R : Subring K) (h : IsLocModel (algebraMap ℂ K) R),
  RatRes (algebraMap ℂ K) R →
  ∃ ε : R →+* ℂ, (∀ a : ℂ, ε ⟨algebraMap ℂ K a, h.const_mem a⟩ = a) ∧ ∀ r : R, ε r = 0 ↔ NonUnit R (r : K) := by
  first | exact @GlobalTheory.FieldPair.exists_residue_complex | exact GlobalTheory.FieldPair.exists_residue_complex | (intros; apply GlobalTheory.FieldPair.exists_residue_complex <;> assumption)
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CommonPoint

theorem isFractionRing_of_isLocModel {K : Type} [Field K] [Algebra ℂ K] {R : Subring K}
    (h : IsLocModel (algebraMap ℂ K) R) : IsFractionRing R K :=
  IsFractionRing.of_field R K fun f => by
    obtain ⟨a, ha, b, hb, hb0, e⟩ := h.frac f
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, (eq_div_iff hb0).2 e⟩

theorem exists_residue {K : Type} [Field K] [Algebra ℂ K] (R : Subring K)
    (h : IsLocModel (algebraMap ℂ K) R) (h' : RatRes (algebraMap ℂ K) R) :
    letI : Algebra ℂ R := ((algebraMap ℂ K).codRestrict R h.const_mem).toAlgebra
    ∃ ε : R →ₐ[ℂ] ℂ, ∀ r : R, ε r = 0 ↔ NonUnit R (r : K) := by
  letI : Algebra ℂ R := ((algebraMap ℂ K).codRestrict R h.const_mem).toAlgebra
  obtain ⟨ε, h1, h2⟩ := GlobalTheory.T.exists_residue_to_complex_of_rationalResidue R h h'
  exact ⟨⟨ε, h1⟩, h2⟩

theorem pair_step : ∀ {K L : Type} [Field K] [Field L] [Algebra ℂ K] [Algebra ℂ L] (R : Subring K) (S : Subring L),
  IsLocModel (algebraMap ℂ K) R → RatRes (algebraMap ℂ K) R →
  IsLocModel (algebraMap ℂ L) S → RatRes (algebraMap ℂ L) S →
  ∃ (M : Type) (_ : Field M) (_ : Algebra ℂ M) (ρ : K →ₐ[ℂ] M) (σ : L →ₐ[ℂ] M) (T : Subring M),
    IsLocModel (algebraMap ℂ M) T ∧ RatRes (algebraMap ℂ M) T ∧
    Dominates ρ.toRingHom T R ∧ Dominates σ.toRingHom T S := by
  intro K L _ _ _ _ R S hR hR' hS hS'
  letI : Algebra ℂ R := ((algebraMap ℂ K).codRestrict R hR.const_mem).toAlgebra
  letI : Algebra ℂ S := ((algebraMap ℂ L).codRestrict S hS.const_mem).toAlgebra
  haveI : IsScalarTower ℂ R K := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower ℂ S L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.EssFiniteType ℂ R := hR.essFiniteType
  haveI : Algebra.EssFiniteType ℂ S := hS.essFiniteType
  haveI := isFractionRing_of_isLocModel hR
  haveI := isFractionRing_of_isLocModel hS
  obtain ⟨εR, hεR⟩ := exists_residue R hR hR'
  obtain ⟨εS, hεS⟩ := exists_residue S hS hS'
  let iR : R →ₐ[ℂ] K := IsScalarTower.toAlgHom ℂ R K
  let iS : S →ₐ[ℂ] L := IsScalarTower.toAlgHom ℂ S L
  have hinj : Function.Injective (Algebra.TensorProduct.map iR iS) := by
    have e : (Algebra.TensorProduct.map iR iS).toLinearMap =
        (iR.toLinearMap.rTensor L).comp (iS.toLinearMap.lTensor R) := by
      ext x y; simp
    have h1 : Function.Injective (iS.toLinearMap.lTensor R) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
    have h2 : Function.Injective (iR.toLinearMap.rTensor L) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective
    intro x y hxy
    have ex := LinearMap.congr_fun e x
    have ey := LinearMap.congr_fun e y
    exact h1 (h2 (ex.symm.trans (hxy.trans ey)))
  haveI : IsDomain (K ⊗[ℂ] L) := GlobalTheory.TensorFields.isDomain_tensor_complex K L
  haveI : IsDomain (R ⊗[ℂ] S) := hinj.isDomain _
  haveI : Algebra.EssFiniteType S (S ⊗[ℂ] R) := Algebra.EssFiniteType.baseChange ℂ R S
  haveI : Algebra.EssFiniteType ℂ (S ⊗[ℂ] R) := Algebra.EssFiniteType.comp ℂ S (S ⊗[ℂ] R)
  haveI : Algebra.EssFiniteType ℂ (R ⊗[ℂ] S) :=
    Algebra.EssFiniteType.of_surjective (Algebra.TensorProduct.comm ℂ S R).toAlgHom
      (Algebra.TensorProduct.comm ℂ S R).surjective
  let ε : R ⊗[ℂ] S →ₐ[ℂ] ℂ := Algebra.TensorProduct.lift εR εS fun _ _ => Commute.all _ _
  obtain ⟨T, hT, hT', hTa⟩ := GlobalTheory.T.exists_localModel_at_complexPoint (R ⊗[ℂ] S) ε
  let M := FractionRing (R ⊗[ℂ] S)
  let j : R ⊗[ℂ] S →ₐ[ℂ] M := IsScalarTower.toAlgHom ℂ _ M
  have hj : Function.Injective j := IsFractionRing.injective (R ⊗[ℂ] S) M
  have hl : Function.Injective (j.comp Algebra.TensorProduct.includeLeft) := by
    rw [AlgHom.coe_comp]
    exact hj.comp (Algebra.TensorProduct.includeLeft_injective (S := ℂ) (algebraMap ℂ S).injective)
  have hr : Function.Injective (j.comp Algebra.TensorProduct.includeRight) := by
    rw [AlgHom.coe_comp]
    exact hj.comp (Algebra.TensorProduct.includeRight_injective (algebraMap ℂ R).injective)
  obtain ⟨ρ, hρ⟩ : ∃ ρ : K →ₐ[ℂ] M, ∀ r : R, ρ (r : K) = j (r ⊗ₜ 1) :=
    ⟨IsFractionRing.liftAlgHom hl, fun r => (IsFractionRing.liftAlgHom_apply hl _).trans
      (IsFractionRing.lift_algebraMap hl r)⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : L →ₐ[ℂ] M, ∀ s : S, σ (s : L) = j (1 ⊗ₜ s) :=
    ⟨IsFractionRing.liftAlgHom hr, fun s => (IsFractionRing.liftAlgHom_apply hr _).trans
      (IsFractionRing.lift_algebraMap hr s)⟩
  refine ⟨M, inferInstance, inferInstance, ρ, σ, T, hT, hT', fun f hf => ?_, fun f hf => ?_⟩
  · have e : ρ.toRingHom f = algebraMap _ M ((⟨f, hf⟩ : R) ⊗ₜ[ℂ] (1 : S)) := hρ ⟨f, hf⟩
    rw [e]
    refine ⟨(hTa _).1, fun hn => (hTa _).2 ?_⟩
    have h0 : εR ⟨f, hf⟩ = 0 := (hεR ⟨f, hf⟩).2 hn
    simp [ε, h0]
  · have e : σ.toRingHom f = algebraMap _ M ((1 : R) ⊗ₜ[ℂ] (⟨f, hf⟩ : S)) := hσ ⟨f, hf⟩
    rw [e]
    refine ⟨(hTa _).1, fun hn => (hTa _).2 ?_⟩
    have h0 : εS ⟨f, hf⟩ = 0 := (hεS ⟨f, hf⟩).2 hn
    simp [ε, h0]

theorem trBasis_of_isLocModel {κ : Type} [Field κ] [Algebra ℂ κ] {O : Subring κ}
    (h : IsLocModel (algebraMap ℂ κ) O) : ∃ (k : ℕ) (z : Fin k → κ), TrBasis (algebraMap ℂ κ) z := by
  letI : Algebra ℂ O := ((algebraMap ℂ κ).codRestrict O h.const_mem).toAlgebra
  haveI : Algebra.EssFiniteType ℂ O := h.essFiniteType
  haveI : IsScalarTower ℂ O κ := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsFractionRing O κ := IsFractionRing.of_field O κ (fun f => by
    obtain ⟨a, ha, b, hb, hb0, e⟩ := h.frac f
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, (eq_div_iff hb0).2 e⟩)
  haveI : Algebra.EssFiniteType O κ := Algebra.EssFiniteType.of_isLocalization κ (nonZeroDivisors O)
  haveI : Algebra.EssFiniteType ℂ κ := Algebra.EssFiniteType.comp ℂ O κ
  obtain ⟨s, hs⟩ := exists_finset_isTranscendenceBasis ℂ κ
  refine ⟨s.card, fun i => (s.equivFin.symm i : κ), ?_⟩
  have e : (algebraMap ℂ κ).toAlgebra = (inferInstance : Algebra ℂ κ) :=
    Algebra.algebra_ext _ _ fun _ => rfl
  unfold TrBasis
  rw [e]
  exact hs.comp_equiv s.equivFin.symm

theorem exists_common_dominating_varietyPoint_noTrBasis {κ : Type} [Field κ] [Algebra ℂ κ] (c : ℕ) : ∀ (O : Fin c → Subring κ),
    (∀ i, IsLocModel (algebraMap ℂ κ) (O i) ∧ RatRes (algebraMap ℂ κ) (O i)) →
    ∃ (κ' : Type) (_ : Field κ') (_ : Algebra ℂ κ') (ρ : Fin c → (κ →ₐ[ℂ] κ')) (O' : Subring κ'),
      IsLocModel (algebraMap ℂ κ') O' ∧ RatRes (algebraMap ℂ κ') O' ∧
      ∀ i, Dominates (ρ i).toRingHom O' (O i) := by
  induction c with
  | zero =>
    intro O _
    exact ⟨ℂ, inferInstance, inferInstance, Fin.elim0, ⊤, isLocModel_self, ratRes_self,
      fun i => i.elim0⟩
  | succ c ih =>
    intro O hO
    obtain ⟨κ'', _, _, ρ'', O'', h1, h2, h3⟩ := ih (fun i => O (Fin.castSucc i)) (fun i => hO _)
    obtain ⟨M, _, _, ρ', σ, T, g1, g2, g3, g4⟩ :=
      pair_step O'' (O (Fin.last c)) h1 h2 (hO _).1 (hO _).2
    refine ⟨M, inferInstance, inferInstance, Fin.lastCases σ (fun j => ρ'.comp (ρ'' j)), T, g1, g2,
      fun i => ?_⟩
    induction i using Fin.lastCases with
    | last => simpa only [Fin.lastCases_last] using g4
    | cast j =>
      simp only [Fin.lastCases_castSucc]
      exact (h3 j).trans g3

theorem exists_common_field : ∀ {κ : Type} [Field κ] [Algebra ℂ κ] (c : ℕ) (O : Fin c → Subring κ),
  (∀ i, IsLocModel (algebraMap ℂ κ) (O i) ∧ RatRes (algebraMap ℂ κ) (O i)) → (∃ (k : ℕ) (z : Fin k → κ), TrBasis (algebraMap ℂ κ) z) →
  ∃ (κ' : Type) (_ : Field κ') (_ : Algebra ℂ κ') (ρ : Fin c → (κ →ₐ[ℂ] κ')) (O' : Subring κ'),
    IsLocModel (algebraMap ℂ κ') O' ∧ RatRes (algebraMap ℂ κ') O' ∧ (∀ i, Dominates (ρ i).toRingHom O' (O i)) ∧
    ∃ (k' : ℕ) (z' : Fin k' → κ'), TrBasis (algebraMap ℂ κ') z' := by
  intro κ _ _ c O hO _
  obtain ⟨κ', _, _, ρ, O', h1, h2, h3⟩ := exists_common_dominating_varietyPoint_noTrBasis c O hO
  exact ⟨κ', inferInstance, inferInstance, ρ, O', h1, h2, h3, trBasis_of_isLocModel h1⟩

end GlobalTheory.CommonPoint
