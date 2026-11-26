module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimLocalizationGraphIdealMinimalPrime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltAlongPlaceNeighboursRingEquiv

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFreeGeneratorTopFormsTensorLocalizationOrd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFreeGeneratorTopFormsTensorLocalizationOrd
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GraphLocal

variable {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ']
  [Algebra (K ⊗[ℂ] κ') L]

theorem isLocalization_locAt {A : Subalgebra ℂ K} (𝔭 : Ideal (tens (κ' := κ') A)) [𝔭.IsPrime]
    (hinj : Function.Injective (algebraMap (K ⊗[ℂ] κ') L)) :
    letI := (toQ (L := L) 𝔭).toAlgebra
    IsLocalization 𝔭.primeCompl (locAt (L := L) 𝔭) := by
  letI := (toQ (L := L) 𝔭).toAlgebra
  refine ⟨fun s => isUnit_toQ 𝔭 hinj s.2, fun x => ?_, fun {a b} h => ⟨1, ?_⟩⟩
  · obtain ⟨a, s, hs, e⟩ := exists_mul_toQ 𝔭 x
    exact ⟨(a, ⟨s, hs⟩), e⟩
  · have : a = b := Subtype.ext (hinj (congrArg Subtype.val h))
    rw [this]

theorem formallyEtale_toQ {A : Subalgebra ℂ K} (𝔭 : Ideal (tens (κ' := κ') A)) [𝔭.IsPrime]
    (hinj : Function.Injective (algebraMap (K ⊗[ℂ] κ') L)) : (toQ (L := L) 𝔭).FormallyEtale := by
  letI := (toQ (L := L) 𝔭).toAlgebra
  haveI := isLocalization_locAt (L := L) 𝔭 hinj
  exact Algebra.FormallyEtale.of_isLocalization 𝔭.primeCompl

end GlobalTheory.GraphLocal

namespace GlobalTheory.GraphLocal

variable {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ']
  [Algebra ℂ L] [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L]

theorem isFreeGen_locAt {n k' : ℕ} (τ' : Fin k' → κ') (E : Place (algebraMap ℂ K))
    (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime]
    (hc : ∀ a, algebraMap ℂ L a ∈ locAt (L := L) 𝔭)
    (hinj : Function.Injective (algebraMap (K ⊗[ℂ] κ') L))
    (hτ : TrBasis (algebraMap ℂ κ') τ') (z : Fin n → E.ring)
    (b : Module.Basis (Fin n) E.ring (Omega E.const)) (hb : ∀ i, b i = dFun E.const (z i)) :
    IsFreeGen (locAt (L := L) 𝔭) (dForm ((algebraMap ℂ L).codRestrict (locAt (L := L) 𝔭) hc)
      (Fin.append (fun i => toQ 𝔭 ⟨1 ⊗ₜ τ' i, tmul_mem (one_mem _) _⟩)
        (fun i => toQ 𝔭 ⟨(z i : K) ⊗ₜ 1, tmul_mem (z i).2 1⟩))) := by
  letI : Algebra ℂ E.ring := E.const.toAlgebra
  let f : E.ring ≃ₐ[ℂ] placeAlg E :=
    { toFun := fun a => ⟨a.1, a.2⟩
      invFun := fun a => ⟨a.1, a.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  let θ : E.ring ⊗[ℂ] κ' ≃ₐ[ℂ] tens (κ' := κ') (placeAlg E) :=
    (Algebra.TensorProduct.congr f AlgEquiv.refl).trans (tensEquiv (placeAlg E))
  have hθ (a : E.ring) (c : κ') : (θ (a ⊗ₜ c) : K ⊗[ℂ] κ') = (a : K) ⊗ₜ c := rfl
  have hθe : (θ : E.ring ⊗[ℂ] κ' →+* tens (κ' := κ') (placeAlg E)).FormallyEtale := by
    letI := (θ : E.ring ⊗[ℂ] κ' →+* tens (κ' := κ') (placeAlg E)).toAlgebra
    exact Algebra.FormallyEtale.of_equiv
      (AlgEquiv.ofBijective (Algebra.ofId (E.ring ⊗[ℂ] κ') (tens (κ' := κ') (placeAlg E)))
        θ.bijective)
  let ψ : E.ring ⊗[ℂ] κ' →+* locAt (L := L) 𝔭 :=
    (toQ (L := L) 𝔭).comp (θ : E.ring ⊗[ℂ] κ' →+* tens (κ' := κ') (placeAlg E))
  have hψ : ψ.FormallyEtale := RingHom.FormallyEtale.comp hθe (formallyEtale_toQ 𝔭 hinj)
  let ρ : E.ring →+* locAt (L := L) 𝔭 := ψ.comp Algebra.TensorProduct.includeLeftRingHom
  have hg := formallyEtale_mvPolynomial_eval₂_tensor (R := E.ring) τ'
    (GlobalTheory.DiagLoc.formallyEtale_eval₂Hom_of_trBasis (algebraMap ℂ κ') hτ)
  have hφ : (MvPolynomial.eval₂Hom ρ (fun i => toQ (L := L) 𝔭 ⟨1 ⊗ₜ τ' i, tmul_mem (one_mem _) _⟩)).FormallyEtale := by
    convert RingHom.FormallyEtale.comp hg hψ using 1
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [ρ]
    · intro i
      simp only [MvPolynomial.eval₂Hom_X', RingHom.comp_apply]
      rfl
  have hρ : ρ.comp E.const = (algebraMap ℂ L).codRestrict (locAt (L := L) 𝔭) hc := by
    ext a
    change algebraMap (K ⊗[ℂ] κ') L (algebraMap ℂ K a ⊗ₜ[ℂ] (1 : κ')) = algebraMap ℂ L a
    rw [← Algebra.TensorProduct.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have := GlobalTheory.TopFrameEt.isFreeGen_dForm_of_formallyEtale_mvPolynomial E.const
    ((algebraMap ℂ L).codRestrict (locAt (L := L) 𝔭) hc) ρ hρ z b hb
    (fun i => toQ (L := L) 𝔭 ⟨1 ⊗ₜ τ' i, tmul_mem (one_mem _) _⟩) hφ
  exact this

end GlobalTheory.GraphLocal

namespace GlobalTheory.GraphLocal

variable {K : Type} [Field K] [Algebra ℂ K]

theorem exists_unit_mul_zpow (E : Place (algebraMap ℂ K)) {t : E.ring} (ht : Irreducible t)
    {f : K} (hf : f ≠ 0) : ∃ u : E.ring, IsUnit u ∧ f = (u : K) * (t : K) ^ E.ord f := by
  have ht0 : (t : K) ≠ 0 := fun h => ht.ne_zero (Subtype.ext h)
  set v : K := f * (t : K) ^ (-E.ord f) with hv
  have hv0 : v ≠ 0 := mul_ne_zero hf (zpow_ne_zero _ ht0)
  have hvo : E.ord v = 0 := by
    rw [hv, E.ord_mul hf (zpow_ne_zero _ ht0), E.ord_zpow, E.ord_irreducible ht]
    ring
  obtain ⟨h1, h2⟩ := (E.ord_eq_zero_iff hv0).1 hvo
  refine ⟨⟨v, h1⟩, IsUnit.of_mul_eq_one (⟨v⁻¹, h2⟩ : E.ring) (Subtype.ext (mul_inv_cancel₀ hv0)), ?_⟩
  change f = v * _
  rw [hv, mul_assoc, ← zpow_add₀ ht0, neg_add_cancel, zpow_zero, mul_one]

end GlobalTheory.GraphLocal

namespace GlobalTheory.GraphLocal

theorem exists_matrix_dFun {K : Type} [Field K] (c₀ : ℂ →+* K) {n : ℕ} (E : Place (c₀)) (z : Fin n → E.ring)
    (b : Module.Basis (Fin n) E.ring (Omega E.const)) (hb : ∀ i, b i = dFun E.const (z i))
    (x : Fin n → K) (hx : TrBasis (c₀) x) :
    ∃ c : Matrix (Fin n) (Fin n) K,
      (∀ i, dFun (c₀) (x i) = ∑ j, c i j • (dFun (c₀) (z j : K) : Omega (c₀))) ∧
      c.det ≠ 0 ∧ (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (dForm (c₀) x) = E.ord c.det := by
  obtain ⟨b', hb'⟩ : ∃ b' : Module.Basis (Fin n) K (Omega (c₀)),
      ∀ j, b' j = dFun (c₀) (z j : K) := by
    letI := E.const.toAlgebra
    letI := (c₀).toAlgebra
    haveI : IsScalarTower ℂ E.ring K := IsScalarTower.of_algebraMap_eq' rfl
    refine ⟨fracKaehlerBasis K b, fun j => ?_⟩
    simp only [fracKaehlerBasis_apply, hb, dFun, KaehlerDifferential.map_D]
    rfl
  let c : Matrix (Fin n) (Fin n) K := fun i j => b'.repr (dFun (c₀) (x i)) j
  have hc : ∀ i, dFun (c₀) (x i) = ∑ j, c i j • dFun (c₀) (z j : K) :=
    fun i => by
      simp_rw [← hb']
      exact (b'.sum_repr _).symm
  have hω := isFreeGen_dForm z b hb
  have hdet : dForm (c₀) x = c.det • E.toRat n (dForm E.const z) := by
    have hz : E.toRat n (dForm E.const z) = dForm c₀ (fun j => (z j : K)) :=
      formMap_dForm _ _ z
    rw [dForm_eq_det_smul x (fun j => (z j : K)) c hc, hz]
  have hc0 : c.det ≠ 0 := by
    intro h0
    have hfree := isFreeGen_dForm_of_trBasis (c₀) hx
    rw [hdet, h0, zero_smul] at hfree
    exact one_ne_zero (hfree.1 (a₁ := 1) (a₂ := 0) (by simp))
  exact ⟨c, hc, hc0, by rw [hdet]; exact E.formOrd_smul_toRat hω hc0⟩

end GlobalTheory.GraphLocal

namespace GlobalTheory.GraphLocal

theorem dForm_append_eq_det_smul {k A : Type*} [CommRing k] [CommRing A] (α : k →+* A)
    {r n : ℕ} (a : Fin r → A) (f w : Fin n → A) (c : Matrix (Fin n) (Fin n) A)
    (h : ∀ i, dFun α (f i) = ∑ j, c i j • dFun α (w j)) :
    dForm α (Fin.append a f) = c.det • dForm α (Fin.append a w) := by
  let M : Matrix (Fin (r + n)) (Fin (r + n)) A :=
    (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) A) 0 0 c).submatrix finSumFinEquiv.symm
      finSumFinEquiv.symm
  have hM : M.det = c.det := by
    simp [M, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
  rw [← hM]
  refine dForm_eq_det_smul _ _ M fun i => ?_
  rw [Fin.sum_univ_add]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp [M, Fin.append_left, Fin.append_right, Matrix.one_apply]
  · simp [M, Fin.append_left, Fin.append_right, h]

end GlobalTheory.GraphLocal

namespace GlobalTheory.GraphLocal

theorem exists_isFreeGen_locAt_formOrd : ∀ {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ'] [Algebra ℂ L]
    [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (n k' : ℕ) (x : Fin n → K) (τ' : Fin k' → κ') (E : Place (algebraMap ℂ K))
    (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime] (t : E.ring)
    (hc : ∀ a, algebraMap ℂ L a ∈ locAt (L := L) 𝔭),
  TrBasis (algebraMap ℂ K) x → TrBasis (algebraMap ℂ κ') τ' →
  (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') → Irreducible t →
  ∃ (y : Fin (k' + n) → locAt (L := L) 𝔭) (q : locAt (L := L) 𝔭),
    IsFreeGen (locAt (L := L) 𝔭) (dForm ((algebraMap ℂ L).codRestrict (locAt (L := L) 𝔭) hc) y) ∧
    IsUnit q ∧
    dForm (algebraMap ℂ L) (Fin.append (fun i => algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ τ' i))
        (fun i => algebraMap (K ⊗[ℂ] κ') L (x i ⊗ₜ 1))) =
      ((q : L) * (algebraMap (K ⊗[ℂ] κ') L ((t : K) ⊗ₜ 1)) ^ (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (dForm (algebraMap ℂ K) x)) •
        dForm (algebraMap ℂ L) (fun i => (y i : L)) := by
  intro K κ' L _ _ _ _ _ _ _ _ _ n k' x τ' E 𝔭 _ t hc hx hτ _ ht
  have hinj : Function.Injective (algebraMap (K ⊗[ℂ] κ') L) := IsFractionRing.injective _ _
  obtain ⟨z, b, hb⟩ : ∃ (z : Fin n → E.ring) (b : Module.Basis (Fin n) E.ring (Omega E.const)),
      ∀ i, b i = dFun E.const (z i) := by
    letI := E.const.toAlgebra
    letI := (algebraMap ℂ K).toAlgebra
    haveI : IsScalarTower ℂ E.ring K := IsScalarTower.of_algebraMap_eq' rfl
    haveI : Algebra.EssFiniteType ℂ E.ring := E.essFiniteType
    haveI := formallySmooth_of_isRegularLocalRing_of_perfectField ℂ E.ring
    obtain ⟨m, z, b, -, hb⟩ := exists_basis_kaehler_uniformiser ℂ ht
    have h1 := trdeg_eq_of_basis_kaehler ℂ K b
    have h2 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hx
    rw [h1, Cardinal.mk_fin] at h2
    obtain rfl : n = m + 1 := by exact_mod_cast h2
    exact ⟨z, b, hb⟩
  obtain ⟨c, hcx, hc0, hord⟩ := exists_matrix_dFun (algebraMap ℂ K) E z b hb x hx
  obtain ⟨u, hu, hfu⟩ := exists_unit_mul_zpow E ht hc0
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  let j : K →+* L := (algebraMap (K ⊗[ℂ] κ') L).comp Algebra.TensorProduct.includeLeftRingHom
  have hj : j.comp (algebraMap ℂ K) = algebraMap ℂ L := by
    ext a
    change algebraMap (K ⊗[ℂ] κ') L (algebraMap ℂ K a ⊗ₜ[ℂ] (1 : κ')) = algebraMap ℂ L a
    rw [← Algebra.TensorProduct.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  let y : Fin (k' + n) → locAt (L := L) 𝔭 :=
    Fin.append (fun i => toQ 𝔭 ⟨1 ⊗ₜ τ' i, tmul_mem (one_mem _) _⟩)
      (fun i => toQ 𝔭 ⟨(z i : K) ⊗ₜ 1, tmul_mem (z i).2 1⟩)
  have hy : (fun i => (y i : L)) = Fin.append (fun i => algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ τ' i))
      (fun i => j (z i : K)) := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp [y, Fin.append_left]
    · simp [y, Fin.append_right, j]
  refine ⟨y, toQ 𝔭 ⟨(u : K) ⊗ₜ 1, tmul_mem u.2 1⟩, isFreeGen_locAt τ' E 𝔭 hc hinj hτ z b hb,
    IsUnit.of_mul_eq_one (toQ 𝔭 ⟨(v : K) ⊗ₜ 1, tmul_mem v.2 1⟩) ?_, ?_⟩
  · rw [← map_mul, ← map_one (toQ (L := L) 𝔭)]
    congr 1
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, Subalgebra.coe_one, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rw [← Subring.coe_mul, hv]
    rfl
  · rw [hy, hord]
    refine (dForm_append_eq_det_smul (algebraMap ℂ L)
      (fun i => algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ τ' i)) (fun i => j (x i)) (fun i => j (z i : K))
      (c.map j) fun i => ?_).trans ?_
    letI := (algebraMap ℂ K).toAlgebra
    letI := (algebraMap ℂ L).toAlgebra
    letI := j.toAlgebra
    haveI : IsScalarTower ℂ K L := IsScalarTower.of_algebraMap_eq' hj.symm
    have e := congrArg (KaehlerDifferential.map ℂ ℂ K L) (hcx i)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at e
    simp only [map_smul, KaehlerDifferential.map_D] at e
    simp only [Matrix.map_apply]
    rw [show dFun (algebraMap ℂ L) (j (x i)) = KaehlerDifferential.D ℂ L (algebraMap K L (x i)) from rfl, e]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← algebraMap_smul L (c i l)]
    rfl
    congr 1
    rw [show (c.map j).det = j c.det from (RingHom.map_det j c).symm]
    generalize E.ord c.det = a at hfu ⊢
    rw [hfu, map_mul, map_zpow₀]
    rfl

end GlobalTheory.GraphLocal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFreeGeneratorTopFormsTensorLocalizationOrdStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_freeGenerator_topForms_tensorLocalization_order : ∀ {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ'] [Algebra ℂ L]
    [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (n k' : ℕ) (x : Fin n → K) (τ' : Fin k' → κ') (E : Place (algebraMap ℂ K))
    (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime] (t : E.ring)
    (hc : ∀ a, algebraMap ℂ L a ∈ locAt (L := L) 𝔭),
  TrBasis (algebraMap ℂ K) x → TrBasis (algebraMap ℂ κ') τ' →
  (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') → Irreducible t →
  ∃ (y : Fin (k' + n) → locAt (L := L) 𝔭) (q : locAt (L := L) 𝔭),
    IsFreeGen (locAt (L := L) 𝔭) (dForm ((algebraMap ℂ L).codRestrict (locAt (L := L) 𝔭) hc) y) ∧
    IsUnit q ∧
    dForm (algebraMap ℂ L) (Fin.append (fun i => algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ τ' i))
        (fun i => algebraMap (K ⊗[ℂ] κ') L (x i ⊗ₜ 1))) =
      ((q : L) * (algebraMap (K ⊗[ℂ] κ') L ((t : K) ⊗ₜ 1)) ^ (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (dForm (algebraMap ℂ K) x)) •
        dForm (algebraMap ℂ L) (fun i => (y i : L)) := by
  first | exact @GlobalTheory.GraphLocal.exists_isFreeGen_locAt_formOrd | exact GlobalTheory.GraphLocal.exists_isFreeGen_locAt_formOrd | (intros; apply GlobalTheory.GraphLocal.exists_isFreeGen_locAt_formOrd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceGraphIdealTensorNeTop
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceGraphIdealTensorNeTop
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GraphLocal

open GlobalTheory.FieldPair

theorem ne_zero_of_ord_pos {K : Type} [Field K] [Algebra ℂ K] (E : Place (algebraMap ℂ K)) {e : K}
    (he : 0 < E.ord e) : e ≠ 0 := by
  rintro rfl
  simp [Place.ord] at he

theorem graphIdeal_ne_top_of_hom {K κ κ' F : Type} [Field K] [Field κ] [Field κ'] [Field F]
    [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ']
    (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ') (E : Place (algebraMap ℂ K))
    (h1 : ∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a)
    (h2 : ∀ a, algebraMap ℂ K a ∈ R) (h4 : E.Contains R)
    (α : E.ring →+* F) (β : κ' →+* F) (hα : ∀ r : R, α ⟨r, h4 _ r.2⟩ = β (ρ (π r)))
    (hpos : ∀ x : E.ring, 0 < E.ord (x : K) → α x = 0) :
    graphIdeal (κ' := κ') E R π ρ ≠ ⊤ := by
  letI : Algebra ℂ F := (β.comp (algebraMap ℂ κ')).toAlgebra
  let j : placeAlg E →+* E.ring :=
    { toFun := fun x => ⟨x.1, x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  let α' : placeAlg E →ₐ[ℂ] F :=
    { α.comp j with
      commutes' := fun a => by
        have := hα ⟨algebraMap ℂ K a, h2 a⟩
        rw [h1, ρ.commutes] at this
        exact this }
  let β' : κ' →ₐ[ℂ] F := { β with commutes' := fun _ => rfl }
  let Φ := Algebra.TensorProduct.lift α' β' (fun _ _ => Commute.all _ _)
  let Ψ : tens (κ' := κ') (placeAlg E) →+* F :=
    (Φ.comp (tensEquiv (κ' := κ') (placeAlg E)).symm.toAlgHom).toRingHom
  have hΨ : ∀ w, Ψ (tensEquiv (placeAlg E) w) = Φ w := fun w => by
    simp [Ψ]
  intro htop
  have hle : graphIdeal (κ' := κ') E R π ρ ≤ RingHom.ker Ψ := by
    rw [graphIdeal, Ideal.span_le]
    rintro b (⟨e, he, hb⟩ | ⟨a, hb⟩)
    · have hmem : e ∈ E.ring := (E.ord_nonneg_iff (ne_zero_of_ord_pos E he)).1 he.le
      have hb' : b = tensEquiv (κ' := κ') (placeAlg E) (⟨e, hmem⟩ ⊗ₜ 1) :=
        Subtype.ext (by rw [hb]; rfl)
      rw [SetLike.mem_coe, RingHom.mem_ker, hb', hΨ]
      simp only [Φ, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
      exact hpos ⟨e, hmem⟩ he
    · have hb' : b = tensEquiv (κ' := κ') (placeAlg E)
          (⟨a, h4 _ a.2⟩ ⊗ₜ 1 - 1 ⊗ₜ ρ (π a)) :=
        Subtype.ext (by rw [hb, coe_tensEquiv, map_sub]; rfl)
      rw [SetLike.mem_coe, RingHom.mem_ker, hb', hΨ]
      simp only [Φ, map_sub, Algebra.TensorProduct.lift_tmul, map_one, mul_one, one_mul]
      rw [sub_eq_zero]
      exact hα a
  have h1mem : (1 : tens (κ' := κ') (placeAlg E)) ∈ graphIdeal (κ' := κ') E R π ρ :=
    htop ▸ Submodule.mem_top
  exact one_ne_zero ((RingHom.mem_ker).1 (hle h1mem) |>.symm.trans (map_one Ψ)).symm

end GlobalTheory.GraphLocal

namespace GlobalTheory.GraphLocal

open GlobalTheory.FieldPair

theorem graphIdeal_ne_top : ∀ {K κ κ' : Type} [Field K] [Field κ] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ']
    (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ') (E : Place (algebraMap ℂ K)),
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ a, algebraMap ℂ K a ∈ R) → (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  E.Contains R → (∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) →
  graphIdeal (κ' := κ') E R π ρ ≠ ⊤ := by
  intro K κ κ' _ _ _ _ _ _ R π ρ E h1 h2 h3 h4 h5
  let kE := IsLocalRing.ResidueField E.ring
  let inc : R →+* E.ring := R.subtype.codRestrict E.ring (fun r => h4 _ r.2)
  let g : R →+* kE := (IsLocalRing.residue E.ring).comp inc
  have hnu : ∀ x : E.ring, (x : K) ≠ 0 →
      (0 < E.ord x ↔ x ∈ IsLocalRing.maximalIdeal E.ring) := by
    intro x hx
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    constructor
    · intro hpos hu
      have := E.ord_eq_zero hu
      omega
    · intro hnu'
      have h0 : 0 ≤ E.ord x := (E.ord_nonneg_iff hx).2 x.2
      rcases h0.lt_or_eq with h | h
      · exact h
      · exfalso
        apply hnu'
        have hinv : (x : K)⁻¹ ∈ E.ring :=
          (E.ord_nonneg_iff (inv_ne_zero hx)).1 (by rw [E.ord_inv, ← h]; simp)
        exact IsUnit.of_mul_eq_one (b := ⟨_, hinv⟩) (Subtype.ext (mul_inv_cancel₀ hx))
  have hker : ∀ r : R, π r = 0 ↔ g r = 0 := by
    intro r
    by_cases hr : (r : K) = 0
    · have : r = 0 := Subtype.ext hr
      subst this
      simp
    · rw [h5 r hr, show g r = IsLocalRing.residue E.ring (inc r) from rfl,
        IsLocalRing.residue_eq_zero_iff]
      exact hnu (inc r) hr
  have hsurj : Function.Surjective π.rangeRestrict := π.rangeRestrict_surjective
  let φ₀ : π.range →+* kE := π.rangeRestrict.liftOfSurjective hsurj
    ⟨g, fun r hr => by
      rw [RingHom.mem_ker] at hr ⊢
      exact (hker r).1 (congrArg Subtype.val hr)⟩
  have hφ₀ : ∀ r, φ₀ (π.rangeRestrict r) = g r := fun r =>
    RingHom.liftOfSurjective_comp_apply _ hsurj _ r
  have hinj : Function.Injective φ₀ := (injective_iff_map_eq_zero φ₀).2 fun s hs => by
    obtain ⟨r, rfl⟩ := hsurj s
    rw [hφ₀] at hs
    exact Subtype.ext ((hker r).2 hs)
  haveI : IsFractionRing π.range κ := IsFractionRing.of_field π.range κ fun z => by
    obtain ⟨a, b, hb, e⟩ := h3 z
    refine ⟨π.rangeRestrict a, π.rangeRestrict b, ?_⟩
    show z = π a / π b
    rw [eq_div_iff hb, e]
  let ι : κ →+* kE := IsFractionRing.lift hinj
  have hι : ∀ r, ι (π r) = g r := fun r => by
    rw [← hφ₀]
    exact IsFractionRing.lift_algebraMap hinj (π.rangeRestrict r)
  letI : Algebra κ kE := ι.toAlgebra
  letI : Algebra κ κ' := ρ.toRingHom.toAlgebra
  haveI : Nontrivial (kE ⊗[κ] κ') :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain κ kE κ'
      ι.injective ρ.toRingHom.injective
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (kE ⊗[κ] κ')
  letI : Field (kE ⊗[κ] κ' ⧸ M) := Ideal.Quotient.field M
  let q := Ideal.Quotient.mk M
  let α : E.ring →+* (kE ⊗[κ] κ' ⧸ M) :=
    q.comp (Algebra.TensorProduct.includeLeftRingHom.comp (IsLocalRing.residue E.ring))
  let β : κ' →+* (kE ⊗[κ] κ' ⧸ M) :=
    q.comp (Algebra.TensorProduct.includeRight (R := κ) (A := kE)).toRingHom
  refine graphIdeal_ne_top_of_hom R π ρ E h1 h2 h4 α β (fun r => ?_) (fun x hx => ?_)
  · show q (IsLocalRing.residue E.ring (inc r) ⊗ₜ 1) = q (1 ⊗ₜ ρ (π r))
    congr 1
    rw [show IsLocalRing.residue E.ring (inc r) = g r from rfl, ← hι,
      show ι (π r) = π r • (1 : kE) by rw [Algebra.smul_def, mul_one]; rfl,
      TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    rfl
  · show q (IsLocalRing.residue E.ring x ⊗ₜ 1) = 0
    rw [(IsLocalRing.residue_eq_zero_iff x).2 ((hnu x (ne_zero_of_ord_pos E hx)).1 hx),
      TensorProduct.zero_tmul, map_zero]

end GlobalTheory.GraphLocal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceGraphIdealTensorNeTopStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placeGraphIdealTensor_ne_top : ∀ {K κ κ' : Type} [Field K] [Field κ] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ']
    (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ') (E : Place (algebraMap ℂ K)),
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ a, algebraMap ℂ K a ∈ R) → (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  E.Contains R → (∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) →
  graphIdeal (κ' := κ') E R π ρ ≠ ⊤ := by
  first | exact @GlobalTheory.GraphLocal.graphIdeal_ne_top | exact GlobalTheory.GraphLocal.graphIdeal_ne_top | (intros; apply GlobalTheory.GraphLocal.graphIdeal_ne_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsUnitMulZpowUniformiserTmul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsUnitMulZpowUniformiserTmul
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GraphLocal

theorem exists_isUnit_mul_zpow_tmul :
    ∀ {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ'] [Algebra (K ⊗[ℂ] κ') L]
    (E : Place (algebraMap ℂ K)) (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime] (t : E.ring),
  Function.Injective (algebraMap (K ⊗[ℂ] κ') L) → Irreducible t →
  ∀ g : K, g ≠ 0 → ∃ q : locAt (L := L) 𝔭, IsUnit q ∧
    algebraMap (K ⊗[ℂ] κ') L (g ⊗ₜ 1) = q * (algebraMap (K ⊗[ℂ] κ') L ((t : K) ⊗ₜ 1)) ^ E.ord g := by
  intro K κ' L _ _ _ _ _ _ E 𝔭 _ t _ ht g hg
  set n := E.ord g
  have ht0 : (t : K) ≠ 0 := fun h => ht.ne_zero (Subtype.ext h)
  set u : K := g * (t : K) ^ (-n) with hu_def
  have hu0 : u ≠ 0 := mul_ne_zero hg (zpow_ne_zero _ ht0)
  have hord : E.ord u = 0 := by
    rw [hu_def, E.ord_mul hg (zpow_ne_zero _ ht0), E.ord_zpow, E.ord_irreducible ht]
    ring
  have hu : u ∈ E.ring := (E.ord_nonneg_iff hu0).1 hord.ge
  have hui : u⁻¹ ∈ E.ring := (E.ord_nonneg_iff (inv_ne_zero hu0)).1 (by rw [E.ord_inv, hord]; simp)
  let b : tens (κ' := κ') (placeAlg E) := ⟨u ⊗ₜ 1, tmul_mem (mem_placeAlg.2 hu) 1⟩
  let b' : tens (κ' := κ') (placeAlg E) := ⟨u⁻¹ ⊗ₜ 1, tmul_mem (mem_placeAlg.2 hui) 1⟩
  have hbb : b * b' = 1 := by
    apply Subtype.ext
    change (u ⊗ₜ[ℂ] (1 : κ')) * (u⁻¹ ⊗ₜ 1) = 1
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ hu0, one_mul]
    rfl
  refine ⟨toQ (L := L) 𝔭 b, (IsUnit.of_mul_eq_one (b := b') hbb).map _, ?_⟩
  let φ : K →+* L := (algebraMap (K ⊗[ℂ] κ') L).comp Algebra.TensorProduct.includeLeftRingHom
  have hφ (x : K) : φ x = algebraMap (K ⊗[ℂ] κ') L (x ⊗ₜ 1) := rfl
  have hg' : g = u * (t : K) ^ n := by
    rw [hu_def, mul_assoc, ← zpow_add₀ ht0, neg_add_cancel, zpow_zero, mul_one]
  rw [coe_toQ, ← hφ, ← hφ, ← hφ, ← map_zpow₀, ← map_mul, ← hg']

end GlobalTheory.GraphLocal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsUnitMulZpowUniformiserTmulStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isUnit_mul_zpow_uniformiser_tmul : ∀ {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ'] [Algebra (K ⊗[ℂ] κ') L]
    (E : Place (algebraMap ℂ K)) (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime] (t : E.ring),
  Function.Injective (algebraMap (K ⊗[ℂ] κ') L) → Irreducible t →
  ∀ g : K, g ≠ 0 → ∃ q : locAt (L := L) 𝔭, IsUnit q ∧
    algebraMap (K ⊗[ℂ] κ') L (g ⊗ₜ 1) = q * (algebraMap (K ⊗[ℂ] κ') L ((t : K) ⊗ₜ 1)) ^ E.ord g := by
  first | exact @GlobalTheory.GraphLocal.exists_isUnit_mul_zpow_tmul | exact GlobalTheory.GraphLocal.exists_isUnit_mul_zpow_tmul | (intros; apply GlobalTheory.GraphLocal.exists_isUnit_mul_zpow_tmul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GraphJetsMemPowSupUniformiser
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GraphJetsMemPowSupUniformiser
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GraphLocal

theorem ker_productMap_le_span {κ κ' : Type} [Field κ] [Field κ'] [Algebra ℂ κ] [Algebra ℂ κ']
    (ρ : κ →ₐ[ℂ] κ') :
    RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ')) ≤
      Ideal.span {x | ∃ f : κ, x = f ⊗ₜ[ℂ] (1 : κ') - 1 ⊗ₜ ρ f} := by
  have key : ∀ x : κ ⊗[ℂ] κ',
      x - 1 ⊗ₜ Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ') x ∈
        Ideal.span {x | ∃ f : κ, x = f ⊗ₜ[ℂ] (1 : κ') - 1 ⊗ₜ ρ f} := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul f g =>
      have e : f ⊗ₜ[ℂ] g - 1 ⊗ₜ Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ') (f ⊗ₜ g) =
          (f ⊗ₜ[ℂ] (1 : κ') - 1 ⊗ₜ ρ f) * (1 ⊗ₜ g) := by
        simp [Algebra.TensorProduct.productMap_apply_tmul, sub_mul,
          Algebra.TensorProduct.tmul_mul_tmul]
      rw [e]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨f, rfl⟩)
    | add x y hx hy =>
      have e : x + y - 1 ⊗ₜ Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ') (x + y) =
          (x - 1 ⊗ₜ Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ') x) +
            (y - 1 ⊗ₜ Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ') y) := by
        rw [map_add (f := _), TensorProduct.tmul_add]
        abel
      rw [e]
      exact add_mem hx hy
  intro x hx
  have h := key x
  rwa [RingHom.mem_ker.1 hx, TensorProduct.tmul_zero, sub_zero] at h


set_option maxHeartbeats 1000000 in
theorem jets_mem_pow_sup : ∀ {K κ κ' : Type} [Field K] [Field κ] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ']
    (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ') (E : Place (algebraMap ℂ K))
    (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime] (t : E.ring),
  graphIdeal E R π ρ ≤ 𝔭 → Irreducible t →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ a, algebraMap ℂ K a ∈ R) → (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  E.Contains R → (∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) →
  ∀ (M l : ℕ) (a : Fin l → R) (b : Fin l → κ') (w : tens (κ' := κ') (placeAlg E)),
    (w : K ⊗[ℂ] κ') = ∑ i, (a i : K) ⊗ₜ b i →
    ∑ i, π (a i) ⊗ₜ[ℂ] b i ∈ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ^ M →
    w ∈ 𝔭 ^ M ⊔ Ideal.span {⟨(t : K) ⊗ₜ 1, tmul_mem t.2 1⟩} := by

  intro K κ κ' _ _ _ _ _ _ R π ρ E 𝔭 _ t hle ht hπC hC hfrac hR hord M l a b w hw hx
  let T := tens (κ' := κ') (placeAlg E)
  let I : Ideal T := 𝔭 ^ M ⊔ Ideal.span {⟨(t : K) ⊗ₜ 1, tmul_mem t.2 1⟩}
  let q : T →ₐ[ℂ] T ⧸ I := Ideal.Quotient.mkₐ ℂ I
  have hq0 : ∀ y : T, q y = 0 ↔ y ∈ I := fun y => by
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
  let jL : placeAlg E →ₐ[ℂ] T :=
    (tensEquiv (κ' := κ') (placeAlg E)).toAlgHom.comp Algebra.TensorProduct.includeLeft
  let jR : κ' →ₐ[ℂ] T :=
    (tensEquiv (κ' := κ') (placeAlg E)).toAlgHom.comp Algebra.TensorProduct.includeRight
  have hjL : ∀ e, (jL e : K ⊗[ℂ] κ') = (e : K) ⊗ₜ 1 := fun e => by
    simp [jL, tensMap]
  have hjR : ∀ c, (jR c : K ⊗[ℂ] κ') = 1 ⊗ₜ c := fun c => by
    simp [jR, tensMap]
  let ι : R →+* placeAlg E :=
    { toFun := fun r => ⟨r, hR _ r.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hι : ∀ r : R, ((ι r : placeAlg E) : K) = r := fun _ => rfl

  have hg : ∀ r : R, jL (ι r) - jR (ρ (π r)) ∈ 𝔭 := fun r => by
    have e : ((jL (ι r) - jR (ρ (π r)) : T) : K ⊗[ℂ] κ') = (r : K) ⊗ₜ 1 - 1 ⊗ₜ ρ (π r) := by
      rw [Subalgebra.coe_sub, hjL (ι r), hjR (ρ (π r))]
      rfl
    exact hle (Ideal.subset_span (Or.inr ⟨r, e⟩))

  have hk : ∀ r : R, π r = 0 → q (jL (ι r)) = 0 := by
    intro r hr
    rw [hq0]
    apply Ideal.mem_sup_right
    by_cases h0 : (r : K) = 0
    · have e : jL (ι r) = 0 := Subtype.ext (by simp [hjL, hι, h0])
      rw [e]
      exact zero_mem _
    have hpos := (hord r h0).1 hr
    have hnu : ¬ IsUnit (⟨r, hR _ r.2⟩ : E.ring) := fun hu => by
      have h1 := E.ord_eq_zero hu
      simp only at h1
      omega
    have hm : (⟨r, hR _ r.2⟩ : E.ring) ∈ Ideal.span {t} := by
      rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer t).1 ht]
      exact hnu
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 hm
    rw [Ideal.mem_span_singleton']
    refine ⟨jL ⟨u, u.2⟩, Subtype.ext ?_⟩
    have hu' : (u : K) * t = r := congrArg Subtype.val hu
    simp only [Subalgebra.coe_mul, hjL, hι, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hu']

  have hu : ∀ r : R, π r ≠ 0 → IsUnit (q (jL (ι r))) := by
    intro r hr
    have hρ : IsUnit (q (jR (ρ (π r)))) :=
      ((isUnit_iff_ne_zero.2 ((map_ne_zero ρ).2 hr)).map jR).map q
    have hn : IsNilpotent (q (jL (ι r) - jR (ρ (π r)))) :=
      ⟨M, by rw [← map_pow, hq0]; exact Ideal.mem_sup_left (Ideal.pow_mem_pow (hg r) M)⟩
    have h := IsNilpotent.isUnit_add_left_of_commute hn hρ (Commute.all _ _)
    rwa [map_sub, add_sub_cancel] at h

  let φ : R →+* T ⧸ I := (q : T →+* T ⧸ I).comp ((jL : placeAlg E →+* T).comp ι)
  have hφ : ∀ r, φ r = q (jL (ι r)) := fun _ => rfl
  have hker : RingHom.ker π.rangeRestrict ≤ RingHom.ker φ := fun r hr => by
    rw [RingHom.mem_ker] at hr ⊢
    exact hk r (congrArg Subtype.val hr)
  let ψ : π.range →+* T ⧸ I :=
    π.rangeRestrict.liftOfRightInverse (Function.surjInv π.rangeRestrict_surjective)
      (Function.rightInverse_surjInv _) ⟨φ, hker⟩
  have hψ : ∀ r, ψ (π.rangeRestrict r) = q (jL (ι r)) := fun r =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ r
  haveI : IsFractionRing π.range κ := by
    refine ⟨fun y => ?_, fun z => ?_, fun {x y} h => ⟨1, by simpa using Subtype.ext h⟩⟩
    · refine isUnit_iff_ne_zero.2 fun h => nonZeroDivisors.coe_ne_zero y (Subtype.ext h)
    · obtain ⟨c, d, hd, e⟩ := hfrac z
      exact ⟨(π.rangeRestrict c, ⟨π.rangeRestrict d, mem_nonZeroDivisors_of_ne_zero
        fun h => hd (congrArg Subtype.val h)⟩), e⟩
  have hunit : ∀ y : nonZeroDivisors π.range, IsUnit (ψ y) := by
    rintro ⟨⟨v, d, rfl⟩, hy⟩
    have hd : π d ≠ 0 := fun h => nonZeroDivisors.coe_ne_zero ⟨_, hy⟩ (Subtype.ext h)
    exact (hψ d).symm ▸ hu d hd
  let θ₀ : κ →+* T ⧸ I := IsLocalization.lift (M := nonZeroDivisors π.range) hunit
  have hθ₀ : ∀ r, θ₀ (π r) = q (jL (ι r)) := fun r =>
    (IsLocalization.lift_eq (M := nonZeroDivisors π.range) hunit (π.rangeRestrict r)).trans (hψ r)

  let θ₀A : κ →ₐ[ℂ] T ⧸ I :=
    { θ₀ with
      commutes' := fun c => by
        have e1 : algebraMap ℂ κ c = π ⟨algebraMap ℂ K c, hC c⟩ := (hπC c (hC c)).symm
        have e2 : ι ⟨algebraMap ℂ K c, hC c⟩ = algebraMap ℂ (placeAlg E) c := Subtype.ext rfl
        change θ₀ (algebraMap ℂ κ c) = _
        rw [e1, hθ₀, e2, AlgHom.commutes, AlgHom.commutes] }
  let θ : κ ⊗[ℂ] κ' →ₐ[ℂ] T ⧸ I := Algebra.TensorProduct.productMap θ₀A (q.comp jR)
  have hθt : ∀ f c, θ (f ⊗ₜ c) = θ₀ f * q (jR c) := fun f c =>
    Algebra.TensorProduct.productMap_apply_tmul _ _ _ _

  have hwx : θ (∑ i, π (a i) ⊗ₜ[ℂ] b i) = q w := by
    have ew : w = ∑ i, jL (ι (a i)) * jR (b i) := by
      apply Subtype.ext
      rw [hw]
      simp only [AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul, hjL, hjR, hι,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [ew, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hθt, hθ₀, map_mul]

  have hgen : Ideal.map θ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ≤
      Ideal.map q 𝔭 := by
    refine (Ideal.map_mono (ker_productMap_le_span ρ)).trans ?_
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨f, rfl⟩, rfl⟩
    obtain ⟨c, d, hd, e⟩ := hfrac f
    have hfd : θ₀ f * q (jL (ι d)) = q (jL (ι c)) := by rw [← hθ₀, ← hθ₀, ← map_mul, e]
    set u := θ (f ⊗ₜ 1 - 1 ⊗ₜ ρ f) with hu_def
    have hu1 : u = θ₀ f - q (jR (ρ f)) := by
      rw [hu_def, map_sub, hθt, hθt]
      simp only [map_one, mul_one, one_mul]
    have h2 : u * q (jL (ι d)) =
        q (jL (ι c) - jR (ρ (π c))) - q (jR (ρ f)) * q (jL (ι d) - jR (ρ (π d))) := by
      rw [hu1, sub_mul, hfd, ← e, map_mul ρ, map_mul jR, map_sub q (jL (ι c)), map_sub q (jL (ι d)),
        map_mul q]
      rw [mul_sub, sub_sub_sub_cancel_right]
    have h3 : u * q (jL (ι d)) ∈ Ideal.map q 𝔭 := by
      rw [h2]
      exact sub_mem (Ideal.mem_map_of_mem q (hg c))
        (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem q (hg d)))
    obtain ⟨v, hv⟩ := (hu d hd).exists_right_inv
    have h4 : u = u * q (jL (ι d)) * v := by rw [mul_assoc, hv, mul_one]
    rw [SetLike.mem_coe, h4]
    exact Ideal.mul_mem_right _ _ h3
  have hbot : Ideal.map q 𝔭 ^ M = ⊥ := by
    rw [← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker]
    intro y hy
    rw [RingHom.mem_ker]
    exact (hq0 y).2 (Ideal.mem_sup_left hy)
  have h1 := Ideal.mem_map_of_mem θ hx
  rw [Ideal.map_pow] at h1
  have h2 := Ideal.pow_right_mono hgen M h1
  rw [hbot, Ideal.mem_bot] at h2
  exact (hq0 w).1 (hwx.symm.trans h2)

end GlobalTheory.GraphLocal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GraphJetsMemPowSupUniformiserStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graphJets_mem_pow_sup_uniformiser : ∀ {K κ κ' : Type} [Field K] [Field κ] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ']
    (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ') (E : Place (algebraMap ℂ K))
    (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime] (t : E.ring),
  graphIdeal E R π ρ ≤ 𝔭 → Irreducible t →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ a, algebraMap ℂ K a ∈ R) → (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  E.Contains R → (∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) →
  ∀ (M l : ℕ) (a : Fin l → R) (b : Fin l → κ') (w : tens (κ' := κ') (placeAlg E)),
    (w : K ⊗[ℂ] κ') = ∑ i, (a i : K) ⊗ₜ b i →
    ∑ i, π (a i) ⊗ₜ[ℂ] b i ∈ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ^ M →
    w ∈ 𝔭 ^ M ⊔ Ideal.span {⟨(t : K) ⊗ₜ 1, tmul_mem t.2 1⟩} := by
  first | exact @GlobalTheory.GraphLocal.jets_mem_pow_sup | exact GlobalTheory.GraphLocal.jets_mem_pow_sup | (intros; apply GlobalTheory.GraphLocal.jets_mem_pow_sup <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTmulNotMemPrimeOfGraphImageNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTmulNotMemPrimeOfGraphImageNeZero
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

namespace GlobalTheory.GraphLocal

theorem sum_notMem_of_ne_zero : ∀ {K κ κ' : Type} [Field K] [Field κ] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ']
    (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ') (E : Place (algebraMap ℂ K))
    (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime],
  graphIdeal E R π ρ ≤ 𝔭 → E.Contains R →
  ∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ') (w : tens (κ' := κ') (placeAlg E)),
    (w : K ⊗[ℂ] κ') = ∑ i, (a i : K) ⊗ₜ b i → ∑ i, ρ (π (a i)) * b i ≠ 0 → w ∉ 𝔭 := by
  intro K κ κ' _ _ _ _ _ _ R π ρ E 𝔭 _ hle hR l a b w hw hc
  let g : Fin l → tens (κ' := κ') (placeAlg E) := fun i =>
    ⟨(a i : K) ⊗ₜ 1 - 1 ⊗ₜ ρ (π (a i)),
      sub_mem (tmul_mem (hR _ (a i).2) 1) (tmul_mem (one_mem (placeAlg E)) _)⟩
  let bb : Fin l → tens (κ' := κ') (placeAlg E) := fun i =>
    ⟨1 ⊗ₜ b i, tmul_mem (one_mem (placeAlg E)) _⟩
  let u : tens (κ' := κ') (placeAlg E) :=
    ⟨1 ⊗ₜ (∑ i, ρ (π (a i)) * b i), tmul_mem (one_mem (placeAlg E)) _⟩
  let v : tens (κ' := κ') (placeAlg E) :=
    ⟨1 ⊗ₜ (∑ i, ρ (π (a i)) * b i)⁻¹, tmul_mem (one_mem (placeAlg E)) _⟩
  have hg : ∀ i, g i ∈ graphIdeal E R π ρ := fun i => Ideal.subset_span (Or.inr ⟨a i, rfl⟩)
  have hsum : w - u = ∑ i, g i * bb i := by
    apply Subtype.ext
    rw [Subalgebra.coe_sub, hw, AddSubmonoidClass.coe_finsetSum]
    simp only [g, bb, u, Subalgebra.coe_mul, sub_mul, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, mul_one, Finset.sum_sub_distrib, TensorProduct.tmul_sum]
  have huv : u * v = 1 := by
    apply Subtype.ext
    simp only [u, v, Subalgebra.coe_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      mul_inv_cancel₀ hc, Subalgebra.coe_one, Algebra.TensorProduct.one_def]
  have hu : u ∉ 𝔭 := fun h => one_notMem 𝔭 (huv ▸ 𝔭.mul_mem_right v h)
  intro hwp
  have hd : w - u ∈ 𝔭 :=
    hle (hsum ▸ Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (hg i))
  exact hu (by simpa using 𝔭.sub_mem hwp hd)

end GlobalTheory.GraphLocal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTmulNotMemPrimeOfGraphImageNeZeroStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_tmul_notMem_prime_of_graph_image_ne_zero : ∀ {K κ κ' : Type} [Field K] [Field κ] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ']
    (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ') (E : Place (algebraMap ℂ K))
    (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime],
  graphIdeal E R π ρ ≤ 𝔭 → E.Contains R →
  ∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ') (w : tens (κ' := κ') (placeAlg E)),
    (w : K ⊗[ℂ] κ') = ∑ i, (a i : K) ⊗ₜ b i → ∑ i, ρ (π (a i)) * b i ≠ 0 → w ∉ 𝔭 := by
  first | exact @GlobalTheory.GraphLocal.sum_notMem_of_ne_zero | exact GlobalTheory.GraphLocal.sum_notMem_of_ne_zero | (intros; apply GlobalTheory.GraphLocal.sum_notMem_of_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularLocalModelGraphOfPlace
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

set_option autoImplicit false

theorem GlobalTheory.GraphLocal.exists_locModel_graph : ∀ {K κ κ' L : Type} [Field K] [Field κ] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ'] [Algebra ℂ L]
    [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (n k k' : ℕ) (x : Fin n → K) (τ' : Fin k' → κ') (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ'),
  TrBasis (algebraMap ℂ K) x → TrBasis (algebraMap ℂ κ') τ' → (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') → (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ a, algebraMap ℂ K a ∈ R) →
  (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  ∀ (E : Place (algebraMap ℂ K)), E.Contains R → (∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) →
  ∃ (Q : Subring L) (hQ : IsLocModel (algebraMap ℂ L) Q), letI := hQ.isLocalRing; ∃ z : Fin (k + 1) → Q,
    IsLocalRing.maximalIdeal Q = Ideal.span (Set.range z) ∧ ringKrullDim Q = k + 1 ∧
    (∀ e ∈ E.ring, algebraMap (K ⊗[ℂ] κ') L (e ⊗ₜ 1) ∈ Q) ∧
    (∀ g : K, g ≠ 0 → ∃ q : Q, IsUnit q ∧ algebraMap (K ⊗[ℂ] κ') L (g ⊗ₜ 1) = q * (z 0 : L) ^ E.ord g) ∧
    (∀ b : κ', b ≠ 0 → ∃ q : Q, IsUnit q ∧ (q : L) = algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ b)) ∧
    (∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ'), ∑ i, ρ (π (a i)) * b i ≠ 0 →
      ∃ q : Q, IsUnit q ∧ (q : L) = (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b) ∧
    (∀ (M l : ℕ) (a : Fin l → R) (b : Fin l → κ'), ∑ i, π (a i) ⊗ₜ[ℂ] b i ∈ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ^ M →
      ∃ q : Q, (q : L) = (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b ∧ q ∈ IsLocalRing.maximalIdeal Q ^ M ⊔ Ideal.span {z 0}) ∧
    ∃ (y : Fin (k' + n) → Q) (q : Q), IsFreeGen Q (dForm ((algebraMap ℂ L).codRestrict Q hQ.const_mem) y) ∧ IsUnit q ∧
      dForm (algebraMap ℂ L) (Fin.append (fun i => algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ τ' i))
        (fun i => algebraMap (K ⊗[ℂ] κ') L (x i ⊗ₜ 1))) =
        ((q : L) * (z 0 : L) ^ E.formOrd (dForm (algebraMap ℂ K) x)) • dForm (algebraMap ℂ L) (fun i => (y i : L)) := by
  intro K κ κ' L _ _ _ _ _ _ _ _ _ _ _ n k k' x τ' R π ρ hx hτ hO' hz hcompat hC hfrac E hER hcentre
  have hinj : Function.Injective (algebraMap (K ⊗[ℂ] κ') L) := IsFractionRing.injective _ _
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible E.ring
  obtain ⟨zR, hzR⟩ := GlobalTheory.T.exists_trBasis_in_image_of_fractionField k R π hfrac hz
  obtain ⟨𝔭, h𝔭⟩ := Ideal.nonempty_minimalPrimes (GlobalTheory.T.placeGraphIdealTensor_ne_top (κ' := κ') R π ρ E hcompat hC hfrac hER hcentre)
  haveI : 𝔭.IsPrime := h𝔭.1.1
  have hle : graphIdeal E R π ρ ≤ 𝔭 := h𝔭.1.2
  have hQ : IsLocModel (algebraMap ℂ L) (locAt (L := L) 𝔭) := GlobalTheory.T.isLocalRingOfVarietyPoint_localization_placeTensor E 𝔭 hO'
  letI := hQ.isLocalRing
  have hmax := GlobalTheory.T.graphIdeal_localization_maximalIdeal_eq_span (L := L) k R π ρ E hER t zR 𝔭 hO' hcompat hC hfrac hcentre ht hzR h𝔭
  have hdim := GlobalTheory.T.ringKrullDim_localization_graphIdeal_minimalPrime (L := L) k R π ρ E 𝔭 hO' hcompat hC hfrac hER hcentre hz h𝔭
  have hz0 : ((toQ (L := L) 𝔭 (gens E R π ρ hER t zR 0) : locAt (L := L) 𝔭) : L) =
      algebraMap (K ⊗[ℂ] κ') L ((t : K) ⊗ₜ 1) := by
    simp [gens]
  refine ⟨locAt (L := L) 𝔭, hQ, fun i => toQ 𝔭 (gens E R π ρ hER t zR i), hmax, hdim, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    exact (toQ (L := L) 𝔭 ⟨e ⊗ₜ 1, tmul_mem (A := placeAlg E) he 1⟩).2
  · intro g hg
    rw [hz0]
    exact GlobalTheory.T.exists_isUnit_mul_zpow_uniformiser_tmul E 𝔭 t hinj ht g hg
  · intro b hb
    refine ⟨toQ 𝔭 ⟨1 ⊗ₜ b, tmul_mem (one_mem (placeAlg E)) b⟩, isUnit_toQ 𝔭 hinj ?_, rfl⟩
    intro h
    apply one_notMem 𝔭
    have h2 := 𝔭.mul_mem_right ⟨(1 : K) ⊗ₜ b⁻¹, tmul_mem (one_mem (placeAlg E)) b⁻¹⟩ h
    convert h2 using 1
    apply Subtype.ext
    simp [Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ hb, Algebra.TensorProduct.one_def]
  · intro l a b hs
    have hw : ∑ i, (a i : K) ⊗ₜ[ℂ] b i ∈ tens (κ' := κ') (placeAlg E) :=
      Subalgebra.sum_mem _ fun i _ => tmul_mem (hER _ (a i).2) (b i)
    refine ⟨toQ 𝔭 ⟨_, hw⟩, isUnit_toQ 𝔭 hinj (GlobalTheory.T.sum_tmul_notMem_prime_of_graph_image_ne_zero R π ρ E 𝔭 hle hER l a b ⟨_, hw⟩ rfl hs), ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum]
  · intro M l a b hJ
    have hw : ∑ i, (a i : K) ⊗ₜ[ℂ] b i ∈ tens (κ' := κ') (placeAlg E) :=
      Subalgebra.sum_mem _ fun i _ => tmul_mem (hER _ (a i).2) (b i)
    refine ⟨toQ 𝔭 ⟨_, hw⟩, by simp [map_sum], ?_⟩
    have h1 := GlobalTheory.T.graphJets_mem_pow_sup_uniformiser R π ρ E 𝔭 t hle ht hcompat hC hfrac hER hcentre M l a b ⟨_, hw⟩ rfl hJ
    have h2 := Ideal.mem_map_of_mem (toQ (L := L) 𝔭) h1
    rw [Ideal.map_sup, Ideal.map_pow, Ideal.map_span, Set.image_singleton] at h2
    have h3 : Ideal.map (toQ (L := L) 𝔭) 𝔭 ^ M ⊔ Ideal.span {toQ (L := L) 𝔭 ⟨(t : K) ⊗ₜ 1, tmul_mem t.2 1⟩} ≤
        IsLocalRing.maximalIdeal (locAt (L := L) 𝔭) ^ M ⊔
          Ideal.span {toQ (L := L) 𝔭 (gens E R π ρ hER t zR 0)} :=
      sup_le_sup (Ideal.pow_right_mono (map_le_maximalIdeal 𝔭 hinj) M) le_rfl
    exact h3 h2
  · obtain ⟨y, q, hy, hq, e⟩ := GlobalTheory.T.exists_freeGenerator_topForms_tensorLocalization_order n k' x τ' E 𝔭 t hQ.const_mem hx hτ hO' ht
    refine ⟨y, q, hy, hq, ?_⟩
    rw [hz0]
    exact e
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularLocalModelGraphOfPlaceStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_regular_localModel_graph_of_place : ∀ {K κ κ' L : Type} [Field K] [Field κ] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ'] [Algebra ℂ L]
    [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (n k k' : ℕ) (x : Fin n → K) (τ' : Fin k' → κ') (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ'),
  TrBasis (algebraMap ℂ K) x → TrBasis (algebraMap ℂ κ') τ' → (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') → (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ a, algebraMap ℂ K a ∈ R) →
  (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  ∀ (E : Place (algebraMap ℂ K)), E.Contains R → (∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) →
  ∃ (Q : Subring L) (hQ : IsLocModel (algebraMap ℂ L) Q), letI := hQ.isLocalRing; ∃ z : Fin (k + 1) → Q,
    IsLocalRing.maximalIdeal Q = Ideal.span (Set.range z) ∧ ringKrullDim Q = k + 1 ∧
    (∀ e ∈ E.ring, algebraMap (K ⊗[ℂ] κ') L (e ⊗ₜ 1) ∈ Q) ∧
    (∀ g : K, g ≠ 0 → ∃ q : Q, IsUnit q ∧ algebraMap (K ⊗[ℂ] κ') L (g ⊗ₜ 1) = q * (z 0 : L) ^ E.ord g) ∧
    (∀ b : κ', b ≠ 0 → ∃ q : Q, IsUnit q ∧ (q : L) = algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ b)) ∧
    (∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ'), ∑ i, ρ (π (a i)) * b i ≠ 0 →
      ∃ q : Q, IsUnit q ∧ (q : L) = (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b) ∧
    (∀ (M l : ℕ) (a : Fin l → R) (b : Fin l → κ'), ∑ i, π (a i) ⊗ₜ[ℂ] b i ∈ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ^ M →
      ∃ q : Q, (q : L) = (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b ∧ q ∈ IsLocalRing.maximalIdeal Q ^ M ⊔ Ideal.span {z 0}) ∧
    ∃ (y : Fin (k' + n) → Q) (q : Q), IsFreeGen Q (dForm ((algebraMap ℂ L).codRestrict Q hQ.const_mem) y) ∧ IsUnit q ∧
      dForm (algebraMap ℂ L) (Fin.append (fun i => algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ τ' i))
        (fun i => algebraMap (K ⊗[ℂ] κ') L (x i ⊗ₜ 1))) =
        ((q : L) * (z 0 : L) ^ E.formOrd (dForm (algebraMap ℂ K) x)) • dForm (algebraMap ℂ L) (fun i => (y i : L)) := by
  first | exact @GlobalTheory.GraphLocal.exists_locModel_graph | exact GlobalTheory.GraphLocal.exists_locModel_graph | (intros; apply GlobalTheory.GraphLocal.exists_locModel_graph <;> assumption)
end
