module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIntegralPivotDecomposition
namespace GlobalTheory

open Matrix

theorem exists_pivot_entry {L : Type} [Field L] (W : ValuationSubring L) {n : ℕ}
    (w : Fin n → L) (hw : w ≠ 0) : ∃ k, w k ≠ 0 ∧ ∀ i, w i / w k ∈ W := by
  obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
    by_contra h
    exact hw (funext fun i => by_contra fun hi => h ⟨i, hi⟩)
  obtain ⟨k, -, hk⟩ :=
    Finset.exists_max_image Finset.univ (fun i => W.valuation (w i)) ⟨j, Finset.mem_univ j⟩
  have hwk : w k ≠ 0 := by
    intro h0
    have hle := hk j (Finset.mem_univ j)
    rw [h0, map_zero] at hle
    exact hj ((Valuation.zero_iff _).1 (le_antisymm hle zero_le))
  refine ⟨k, hwk, fun i => ?_⟩
  rw [← W.valuation_le_one_iff, map_div₀]
  exact div_le_one_of_le₀ (hk i (Finset.mem_univ i)) zero_le

private theorem exists_pivot_unipotent_mul_triangular {L : Type} [Field L] (W : ValuationSubring L) {n : ℕ} :
    ∀ (r : ℕ) (g : Matrix (Fin n) (Fin r) L), LinearIndependent L g.transpose →
      ∃ (ι : Fin r ↪ Fin n) (u : Matrix (Fin n) (Fin r) L) (b : Matrix (Fin r) (Fin r) L),
        (∀ i j, u i j ∈ W) ∧ (∀ i j : Fin r, i < j → u (ι i) j = 0) ∧
        (∀ i : Fin r, u (ι i) i = 1) ∧ b.BlockTriangular id ∧ (∀ i, b i i ≠ 0) ∧ g = u * b := by
  intro r
  induction r with
  | zero =>
    intro g _
    refine ⟨⟨Fin.elim0, fun a => Fin.elim0 a⟩, 0, 0, fun _ j => Fin.elim0 j, fun i => Fin.elim0 i,
      fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_⟩
    ext _ j
    exact Fin.elim0 j
  | succ r ih =>
    intro g hg
    let cols' : Fin r → Fin n → L := fun i a => g a i.castSucc
    let g' : Matrix (Fin n) (Fin r) L := Matrix.of fun a i => cols' i a
    let x : Fin n → L := fun a => g a (Fin.last r)
    have hsplit : (Fin.snoc cols' x : Fin (r + 1) → Fin n → L) = fun i a => g a i := by
      funext i a
      cases i using Fin.lastCases with
      | last => simp [x]
      | cast i => simp [cols']
    have hg2 : LinearIndependent L (Fin.snoc cols' x : Fin (r + 1) → Fin n → L) := by
      rw [hsplit]
      exact hg
    rw [linearIndependent_finSnoc] at hg2
    obtain ⟨hg'ind, hxspan⟩ := hg2
    obtain ⟨ι', u', b', hu'W, hu'zero, hu'one, hb'tri, hb'diag, hgub⟩ := ih g' hg'ind
    have hb'det : IsUnit b'.det := by
      rw [Matrix.det_of_isUpperTriangular hb'tri]
      exact (Finset.prod_ne_zero_iff.2 fun i _ => hb'diag i).isUnit
    let M : Matrix (Fin r) (Fin r) L := Matrix.of fun l i => u' (ι' l) i
    have hMtri : M.BlockTriangular OrderDual.toDual := by
      intro l i hli
      simpa [M] using hu'zero l i (OrderDual.toDual_lt_toDual.1 hli)
    have hMdet : IsUnit M.det := by
      rw [Matrix.det_of_isLowerTriangular M hMtri]
      simp [M, hu'one]
    let c : Fin r → L := M⁻¹ *ᵥ (fun l => x (ι' l))
    let v : Fin n → L := x - u' *ᵥ c
    have hvpiv : ∀ l, v (ι' l) = 0 := by
      intro l
      have h1 : (u' *ᵥ c) (ι' l) = (M *ᵥ c) l := rfl
      have h2 : M *ᵥ c = fun l => x (ι' l) := by
        simp only [c]
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hMdet, Matrix.one_mulVec]
      show x (ι' l) - (u' *ᵥ c) (ι' l) = 0
      rw [h1, h2, sub_self]
    have hv0 : v ≠ 0 := by
      intro h0
      apply hxspan
      have hxv : x - u' *ᵥ c = 0 := h0
      have hu' : u' = g' * b'⁻¹ := by
        rw [hgub]
        exact (Matrix.mul_nonsing_inv_cancel_right (B := u') (h := hb'det)).symm
      have hxe : x = g' *ᵥ (b'⁻¹ *ᵥ c) := by
        rw [Matrix.mulVec_mulVec, ← hu']
        exact sub_eq_zero.1 hxv
      have hmem := LinearMap.mem_range_self g'.mulVecLin (b'⁻¹ *ᵥ c)
      rw [Matrix.range_mulVecLin] at hmem
      rw [hxe]
      exact hmem
    obtain ⟨k, hvk, hkW⟩ := exists_pivot_entry W v hv0
    have hk : ∀ l, ι' l ≠ k := fun l hl => hvk (hl ▸ hvpiv l)
    let ιf : Fin (r + 1) → Fin n := Fin.lastCases (motive := fun _ => Fin n) k (fun i => ι' i)
    have hιf : Function.Injective ιf := by
      intro i j hij
      cases i using Fin.lastCases with
      | last =>
        cases j using Fin.lastCases with
        | last => rfl
        | cast j =>
          simp only [ιf, Fin.lastCases_last, Fin.lastCases_castSucc] at hij
          exact absurd hij.symm (hk j)
      | cast i =>
        cases j using Fin.lastCases with
        | last =>
          simp only [ιf, Fin.lastCases_last, Fin.lastCases_castSucc] at hij
          exact absurd hij (hk i)
        | cast j =>
          simp only [ιf, Fin.lastCases_castSucc] at hij
          rw [ι'.injective hij]
    let u : Matrix (Fin n) (Fin (r + 1)) L :=
      Matrix.of fun a => Fin.snoc (α := fun _ => L) (u' a) (v a / v k)
    let b : Matrix (Fin (r + 1)) (Fin (r + 1)) L := Matrix.of fun i j =>
      Fin.lastCases (motive := fun _ => L)
        (Fin.lastCases (motive := fun _ => L) (v k) (fun i' => c i') i)
        (fun j' => Fin.lastCases (motive := fun _ => L) 0 (fun i' => b' i' j') i) j
    refine ⟨⟨ιf, hιf⟩, u, b, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a j
      cases j using Fin.lastCases with
      | last => simpa [u] using hkW a
      | cast j => simpa [u] using hu'W a j
    · intro i j hij
      cases i using Fin.lastCases with
      | last => exact absurd hij (not_lt.2 (Fin.le_last j))
      | cast i =>
        cases j using Fin.lastCases with
        | last =>
          simp only [u, ιf, Function.Embedding.coeFn_mk, Matrix.of_apply, Fin.lastCases_castSucc,
            Fin.snoc_last]
          rw [hvpiv i, zero_div]
        | cast j =>
          simp only [u, ιf, Function.Embedding.coeFn_mk, Matrix.of_apply, Fin.lastCases_castSucc,
            Fin.snoc_castSucc]
          exact hu'zero i j (Fin.castSucc_lt_castSucc_iff.1 hij)
    · intro i
      cases i using Fin.lastCases with
      | last =>
        simp only [u, ιf, Function.Embedding.coeFn_mk, Matrix.of_apply, Fin.lastCases_last,
          Fin.snoc_last]
        exact div_self hvk
      | cast i =>
        simp only [u, ιf, Function.Embedding.coeFn_mk, Matrix.of_apply, Fin.lastCases_castSucc,
          Fin.snoc_castSucc]
        exact hu'one i
    · intro i j hji
      cases i using Fin.lastCases with
      | last =>
        cases j using Fin.lastCases with
        | last => exact absurd hji (lt_irrefl _)
        | cast j => simp [b]
      | cast i =>
        cases j using Fin.lastCases with
        | last => exact absurd hji (not_lt.2 (Fin.le_last _))
        | cast j =>
          simp only [b, Matrix.of_apply, Fin.lastCases_castSucc]
          exact hb'tri (Fin.castSucc_lt_castSucc_iff.1 hji)
    · intro i
      cases i using Fin.lastCases with
      | last => simpa [b] using hvk
      | cast i => simpa [b] using hb'diag i
    · ext a j
      rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
      cases j using Fin.lastCases with
      | last =>
        simp only [u, b, Matrix.of_apply, Fin.snoc_castSucc, Fin.snoc_last, Fin.lastCases_last,
          Fin.lastCases_castSucc]
        rw [div_mul_cancel₀ _ hvk]
        show x a = _ + (x a - (u' *ᵥ c) a)
        simp only [Matrix.mulVec, dotProduct]
        ring
      | cast j =>
        simp only [u, b, Matrix.of_apply, Fin.snoc_castSucc, Fin.lastCases_last,
          Fin.lastCases_castSucc, mul_zero, add_zero]
        have hentry := congrFun (congrFun hgub a) j
        simpa [g', cols', Matrix.mul_apply] using hentry

theorem exists_integral_pivot_decomposition :
    ∀ (L : Type) [Field L] (W : ValuationSubring L) (n r : ℕ) (g : Matrix (Fin n) (Fin r) L),
      LinearIndependent L g.transpose →
      ∃ (ι : Fin r ↪ Fin n) (u : Matrix (Fin n) (Fin r) L) (b : Matrix (Fin r) (Fin r) L),
        (∀ i j, u i j ∈ W) ∧ (∀ i j : Fin r, i < j → u (ι i) j = 0) ∧
        (∀ i : Fin r, u (ι i) i = 1) ∧ b.BlockTriangular id ∧ (∀ i, b i i ≠ 0) ∧ g = u * b := by
  intro L _ W n r g hg
  exact exists_pivot_unipotent_mul_triangular W r g hg

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIsOpenImmersionIsStandardSmoothOfRelativeD
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory

theorem residueField_fg_trdeg_of_isStandardSmoothOfRelativeDimension {K B : Type} [Field K]
    [CommRing B] [Algebra K B] (d : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension d K B]
    (p : Ideal B) [p.IsPrime] (hp : ∀ q : Ideal B, q.IsPrime → q ≤ p → q = p) :
    Algebra.EssFiniteType K p.ResidueField ∧ Algebra.trdeg K p.ResidueField = d := by
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial d K B
  letI : Algebra (MvPolynomial (Fin d) K) B := g.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin d) K) B := hg
  haveI : IsScalarTower K (MvPolynomial (Fin d) K) B :=
    IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  haveI : Algebra.FiniteType K B := .trans (S := MvPolynomial (Fin d) K) inferInstance inferInstance
  refine ⟨.comp K B _, ?_⟩
  obtain ⟨q, hqp, hq, hqo⟩ := Ideal.exists_ideal_le_liesOver_of_le
    (p := (⊥ : Ideal (MvPolynomial (Fin d) K))) (q := p.under (MvPolynomial (Fin d) K)) p bot_le
  obtain rfl := hp q hq hqp
  haveI : FaithfulSMul (MvPolynomial (Fin d) K) q.ResidueField := by
    rw [faithfulSMul_iff_algebraMap_injective, injective_iff_map_eq_zero]
    intro a ha
    rw [IsScalarTower.algebraMap_apply _ B, Ideal.algebraMap_residueField_eq_zero] at ha
    have : a ∈ q.under (MvPolynomial (Fin d) K) := ha
    rwa [← hqo.over] at this
  haveI : Algebra.IsAlgebraic (MvPolynomial (Fin d) K) q.ResidueField := by
    let := Localization.AtPrime.algebraOfLiesOver (⊥ : Ideal (MvPolynomial (Fin d) K)) q
    have : Module.Finite (⊥ : Ideal (MvPolynomial (Fin d) K)).ResidueField q.ResidueField :=
      inferInstance
    have : Algebra.IsAlgebraic (MvPolynomial (Fin d) K)
        (⊥ : Ideal (MvPolynomial (Fin d) K)).ResidueField :=
      IsLocalization.isAlgebraic _ (nonZeroDivisors (MvPolynomial (Fin d) K))
    exact Algebra.IsAlgebraic.trans _ (⊥ : Ideal (MvPolynomial (Fin d) K)).ResidueField _
  rw [← trdeg_add_eq K (MvPolynomial (Fin d) K), MvPolynomial.trdeg_of_isDomain, trdeg_eq_zero]
  simp

theorem exists_isOpenImmersion_isStandardSmoothOfRelativeDimension {K : Type} [Field K]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K)) (d : ℕ)
    (hf : SmoothOfRelativeDimension d f) (x : X) :
    ∃ (B : CommRingCat.{0}) (φ : CommRingCat.of K ⟶ B) (j : Spec B ⟶ X) (_ : IsOpenImmersion j)
      (y : Spec B), j y = x ∧ j ≫ f = Spec.map φ ∧
        φ.hom.IsStandardSmoothOfRelativeDimension d := by
  obtain ⟨A, j, hj, ⟨y, rfl⟩, -⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (x := x) (U := ⊤) trivial
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (j ≫ f)
  have h : SmoothOfRelativeDimension (0 + d) (j ≫ f) := inferInstance
  rw [zero_add, ← hφ] at h
  obtain ⟨s, hs, h'⟩ := (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension d)).1 h
  obtain ⟨t, ht, hty⟩ : ∃ t ∈ s, t ∉ y.asIdeal := by
    by_contra hne
    push Not at hne
    exact y.isPrime.ne_top (top_le_iff.mp (hs ▸ Ideal.span_le.mpr hne))
  obtain ⟨z, hz⟩ : y ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away t))) := by
    rw [PrimeSpectrum.localization_away_comap_range _ t]
    exact hty
  refine ⟨.of (Localization.Away t), φ ≫ CommRingCat.ofHom (algebraMap A (Localization.Away t)),
    Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away t))) ≫ j, inferInstance, z,
    ?_, ?_, h' t ht⟩
  · rw [← hz]; rfl
  · rw [Category.assoc, ← hφ, Spec.map_comp]

theorem residueField_fg_trdeg_of_smoothOfRelativeDimension {K : Type} [Field K]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K)) (d : ℕ)
    (hf : SmoothOfRelativeDimension d f) (x : X) (hx : ∀ y : X, y ⤳ x → y = x) :
    letI : Algebra K (X.residueField x) :=
      (Spec.preimage (X.fromSpecResidueField x ≫ f)).hom.toAlgebra
    (⊤ : IntermediateField K (X.residueField x)).FG ∧ Algebra.trdeg K (X.residueField x) = d := by
  obtain ⟨B, φ, j, hj, y, rfl, hjf, hφ⟩ :=
    exists_isOpenImmersion_isStandardSmoothOfRelativeDimension f d hf x
  letI : Algebra K (X.residueField (j y)) :=
    (Spec.preimage (X.fromSpecResidueField (j y) ≫ f)).hom.toAlgebra
  letI : Algebra K B := φ.hom.toAlgebra
  haveI : y.asIdeal.IsPrime := y.isPrime
  haveI : Algebra.IsStandardSmoothOfRelativeDimension d K B := hφ
  obtain ⟨h1, h2⟩ := residueField_fg_trdeg_of_isStandardSmoothOfRelativeDimension (K := K) d
    y.asIdeal (fun q hq hqy => by
      have hs : (⟨q, hq⟩ : PrimeSpectrum B) ⤳ y := (PrimeSpectrum.le_iff_specializes _ _).mp hqy
      have := j.isOpenEmbedding.injective (hx _ (hs.map j.continuous))
      exact congrArg PrimeSpectrum.asIdeal this)
  let e : X.residueField (j y) ≅ CommRingCat.of y.asIdeal.ResidueField :=
    asIso (j.residueFieldMap y) ≪≫ Scheme.Spec.residueFieldIso B y
  have he : Spec.preimage (X.fromSpecResidueField (j y) ≫ f) ≫ e.hom =
      φ ≫ CommRingCat.ofHom (algebraMap B y.asIdeal.ResidueField) := by
    rw [← Spec.map_inj, ← cancel_epi (Spec.map (Scheme.Spec.residueFieldIso B y).inv)]
    simp only [e, Iso.trans_hom, asIso_hom, Spec.map_comp, Spec.map_preimage, Category.assoc,
      Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField_assoc,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc, hjf]
    rw [← Spec.map_comp_assoc, Iso.hom_inv_id, Spec.map_id, Category.id_comp]
  let e' : X.residueField (j y) ≃ₐ[K] y.asIdeal.ResidueField :=
    { e.commRingCatIsoToRingEquiv with
      commutes' := fun a => congr($(he).hom a) }
  refine ⟨IntermediateField.fg_top_iff.mpr ?_, ?_⟩
  · exact Algebra.EssFiniteType.of_surjective e'.symm.toAlgHom e'.symm.surjective
  · rw [e'.trdeg_eq, h2]

theorem residueField_genericPoint_fg_trdeg_of_smoothOfRelativeDimension :
    ∀ (K : Type) [Field K] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K)) (d : ℕ), SmoothOfRelativeDimension d f → ∀ (Z : Set X) (hZ : Z ∈ irreducibleComponents X), letI : Algebra K (X.residueField (hZ.1 : IsIrreducible Z).genericPoint) := (Spec.preimage (X.fromSpecResidueField (hZ.1 : IsIrreducible Z).genericPoint ≫ f)).hom.toAlgebra; (⊤ : IntermediateField K (X.residueField (hZ.1 : IsIrreducible Z).genericPoint)).FG ∧ Algebra.trdeg K (X.residueField (hZ.1 : IsIrreducible Z).genericPoint) = d := by
  intro K _ X f d hf Z hZ
  refine residueField_fg_trdeg_of_smoothOfRelativeDimension f d hf _ fun y hy => ?_
  have hg := (hZ.1 : IsIrreducible Z).isGenericPoint_genericPoint
    (isClosed_of_mem_irreducibleComponents Z hZ)
  have h1 : Z ⊆ closure {y} := by
    rw [← hg.def]
    exact specializes_iff_closure_subset.mp hy
  have h2 : closure {y} ⊆ Z := hZ.2 isIrreducible_singleton.closure h1
  exact (hy.antisymm (hg.specializes (h2 (subset_closure rfl)))).eq

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsLowerMulUpperOfLeadingMinors
namespace GlobalTheory

open Matrix

section Cell
variable {R : Type} [CommRing R]

theorem det_eq_one_of_lower_unitriangular {r : ℕ} (l : Matrix (Fin r) (Fin r) R)
    (h0 : ∀ i j : Fin r, i < j → l i j = 0) (h1 : ∀ i, l i i = 1) : l.det = 1 := by
  rw [Matrix.det_of_lowerTriangular l (fun i j h => h0 i j h)]
  simp [h1]

theorem exists_lower_mul_upper_of_leading_minors (r : ℕ) (h : Matrix (Fin r) (Fin r) R)
    (hm : ∀ k (hk : k ≤ r), IsUnit (h.submatrix (Fin.castLE hk) (Fin.castLE hk)).det) :
    ∃ l b : Matrix (Fin r) (Fin r) R, (∀ i j : Fin r, i < j → l i j = 0) ∧ (∀ i, l i i = 1) ∧
      b.BlockTriangular id ∧ h = l * b := by
  induction r with
  | zero => exact ⟨1, 1, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, Subsingleton.elim _ _⟩
  | succ r ih =>
    obtain ⟨L, B, hL0, hL1, hB, hA⟩ := ih (h.submatrix Fin.castSucc Fin.castSucc)
      (fun k hk => hm k (hk.trans (Nat.le_succ r)))
    have hLd : L.det = 1 := det_eq_one_of_lower_unitriangular L hL0 hL1
    have hAu : IsUnit (h.submatrix Fin.castSucc Fin.castSucc).det := hm r (Nat.le_succ r)
    have hBu : IsUnit B.det := by
      rw [hA, Matrix.det_mul, hLd, one_mul] at hAu; exact hAu
    have hLu : IsUnit L.det := by rw [hLd]; exact isUnit_one
    set x : Fin r → R := (fun j => h (Fin.last r) j.castSucc) ᵥ* B⁻¹ with hx
    set y : Fin r → R := L⁻¹ *ᵥ (fun i => h i.castSucc (Fin.last r)) with hy
    have hxB : x ᵥ* B = fun j => h (Fin.last r) j.castSucc := by
      rw [hx, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hBu, Matrix.vecMul_one]
    have hLy : L *ᵥ y = fun i => h i.castSucc (Fin.last r) := by
      rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hLu, Matrix.one_mulVec]
    refine ⟨Matrix.of fun i j => Fin.lastCases (motive := fun _ => R)
        (Fin.lastCases (motive := fun _ => R) 1 x j)
        (fun i => Fin.lastCases (motive := fun _ => R) 0 (L i) j) i,
      Matrix.of fun i j => Fin.lastCases (motive := fun _ => R)
        (Fin.lastCases (motive := fun _ => R) (h (Fin.last r) (Fin.last r) - x ⬝ᵥ y) (fun _ => 0) j)
        (fun i => Fin.lastCases (motive := fun _ => R) (y i) (B i) j) i, ?_, ?_, ?_, ?_⟩
    · intro i j hij
      induction i using Fin.lastCases with
      | last => exact absurd hij (not_lt.2 (Fin.le_last j))
      | cast i =>
        induction j using Fin.lastCases with
        | last => simp
        | cast j => simpa using hL0 i j (by simpa using hij)
    · intro i
      induction i using Fin.lastCases with
      | last => simp
      | cast i => simpa using hL1 i
    · intro i j hij
      induction j using Fin.lastCases with
      | last => exact absurd hij (not_lt.2 (Fin.le_last i))
      | cast j =>
        induction i using Fin.lastCases with
        | last => simp
        | cast i => simpa using hB (i := i) (j := j) (by simpa using hij)
    · ext i j
      rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => simp [dotProduct]
        | cast j => simpa [Matrix.vecMul, dotProduct] using (congrFun hxB j).symm
      | cast i =>
        induction j using Fin.lastCases with
        | last => simpa [Matrix.mulVec, dotProduct] using (congrFun hLy i).symm
        | cast j => simpa [Matrix.mul_apply] using congrFun (congrFun hA i) j

theorem eq_one_of_lower_unitriangular_eq_mul {r : ℕ} (l l' c : Matrix (Fin r) (Fin r) R)
    (h0 : ∀ i j : Fin r, i < j → l i j = 0) (h1 : ∀ i, l i i = 1)
    (h0' : ∀ i j : Fin r, i < j → l' i j = 0) (h1' : ∀ i, l' i i = 1)
    (hc : c.BlockTriangular id) (h : l = l' * c) : c = 1 := by
  have key : ∀ i : Fin r, ∀ j, c i j = (1 : Matrix (Fin r) (Fin r) R) i j := by
    intro i
    induction i using WellFoundedLT.induction with
    | ind i ih =>
      intro j
      rcases lt_or_ge j i with hji | hij
      · rw [hc hji, Matrix.one_apply_ne hji.ne']
      · have e : l i j = c i j := by
          rw [h, Matrix.mul_apply, Finset.sum_eq_single i, h1', one_mul]
          · intro k _ hk
            rcases lt_or_gt_of_ne hk with hk | hk
            · rw [ih k hk, Matrix.one_apply_ne (hk.trans_le hij).ne, mul_zero]
            · rw [h0' i k hk, zero_mul]
          · simp
        rw [← e]
        rcases hij.eq_or_lt with rfl | hij
        · simp [h1]
        · rw [h0 i j hij, Matrix.one_apply_ne hij.ne]
  ext i j
  exact key i j

theorem isUnit_det_of_upper_of_isUnit_diag {r : ℕ} (b : Matrix (Fin r) (Fin r) R)
    (hb : b.BlockTriangular id) (hu : ∀ i, IsUnit (b i i)) : IsUnit b.det := by
  rw [Matrix.det_of_upperTriangular hb]
  exact IsUnit.prod_iff.2 fun i _ => hu i

end Cell

theorem cell_coordinates_exists_unique :
    ∀ (R : Type) [CommRing R] (n r : ℕ) (ι : Fin r ↪ Fin n) (g : Matrix (Fin n) (Fin r) R), ((∀ k (hk : k ≤ r), IsUnit (g.submatrix (fun i : Fin k => ι (Fin.castLE hk i)) (Fin.castLE hk)).det) ↔ ∃ (u : Matrix (Fin n) (Fin r) R) (b : Matrix (Fin r) (Fin r) R), (∀ i j : Fin r, i < j → u (ι i) j = 0) ∧ (∀ i : Fin r, u (ι i) i = 1) ∧ b.BlockTriangular id ∧ (∀ i, IsUnit (b i i)) ∧ g = u * b) ∧ ∀ (u u' : Matrix (Fin n) (Fin r) R) (b b' : Matrix (Fin r) (Fin r) R), (∀ i j : Fin r, i < j → u (ι i) j = 0) ∧ (∀ i : Fin r, u (ι i) i = 1) → (∀ i j : Fin r, i < j → u' (ι i) j = 0) ∧ (∀ i : Fin r, u' (ι i) i = 1) → b.BlockTriangular id → b'.BlockTriangular id → (∀ i, IsUnit (b i i)) → u * b = u' * b' → u = u' ∧ b = b' := by
  intro R _ n r ι g
  refine ⟨⟨fun hm => ?_, ?_⟩, ?_⟩
  · obtain ⟨l, b, hl0, hl1, hb, hh⟩ :=
      exists_lower_mul_upper_of_leading_minors r (g.submatrix ι id) hm
    have hbu : IsUnit b.det := by
      have h1 : IsUnit (g.submatrix ι id).det := hm r le_rfl
      rwa [hh, Matrix.det_mul, det_eq_one_of_lower_unitriangular l hl0 hl1, one_mul] at h1
    have hu : ∀ i j, (g * b⁻¹) (ι i) j = l i j := by
      intro i j
      have : l = g.submatrix ι id * b⁻¹ := by
        rw [hh, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hbu, Matrix.mul_one]
      rw [this]; simp [Matrix.mul_apply]
    refine ⟨g * b⁻¹, b, fun i j hij => by rw [hu, hl0 i j hij], fun i => by rw [hu, hl1], hb, ?_, ?_⟩
    · intro i
      rw [Matrix.det_of_upperTriangular hb] at hbu
      exact IsUnit.prod_iff.1 hbu i (Finset.mem_univ _)
    · rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hbu, Matrix.mul_one]
  · rintro ⟨u, b, hu0, hu1, hb, hbu, rfl⟩ k hk
    have e : (u * b).submatrix (fun i : Fin k => ι (Fin.castLE hk i)) (Fin.castLE hk) =
        u.submatrix (fun i : Fin k => ι (Fin.castLE hk i)) (Fin.castLE hk) *
          b.submatrix (Fin.castLE hk) (Fin.castLE hk) := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.mul_apply]
      symm
      refine Fintype.sum_of_injective (Fin.castLE hk) (Fin.castLE_injective hk) _ _ ?_ (fun _ => rfl)
      intro m hm
      have hkm : k ≤ m.val := by
        by_contra hlt
        exact hm ⟨⟨m.val, not_le.1 hlt⟩, rfl⟩
      have : Fin.castLE hk j < m := by
        rw [Fin.lt_def]; exact lt_of_lt_of_le j.2 hkm
      have h0 : b m (Fin.castLE hk j) = 0 := hb this
      rw [h0, mul_zero]
    rw [e, Matrix.det_mul, det_eq_one_of_lower_unitriangular, one_mul]
    · exact isUnit_det_of_upper_of_isUnit_diag _ (fun i j hij => hb hij) (fun i => hbu _)
    · intro i j hij; exact hu0 _ _ hij
    · intro i; exact hu1 _
  · rintro u u' b b' ⟨hu0, hu1⟩ ⟨hu0', hu1'⟩ hb hb' hbu h
    have hd := isUnit_det_of_upper_of_isUnit_diag b hb hbu
    have hu : u = u' * (b' * b⁻¹) := by
      rw [← Matrix.mul_assoc, ← h, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
    have hbi : b⁻¹.BlockTriangular id := by
      let _ := Matrix.invertibleOfIsUnitDet b hd
      exact Matrix.blockTriangular_inv_of_blockTriangular hb
    have hc : b' * b⁻¹ = 1 := by
      refine eq_one_of_lower_unitriangular_eq_mul (u.submatrix ι id) (u'.submatrix ι id) _
        hu0 hu1 hu0' hu1' (hb'.mul hbi) ?_
      ext i j
      rw [Matrix.submatrix_apply, hu]; simp [Matrix.mul_apply]
    refine ⟨by rw [hu, hc, Matrix.mul_one], ?_⟩
    calc b = b' * b⁻¹ * b := by rw [hc, Matrix.one_mul]
      _ = b' := by rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.mul_one]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.AdjoinRatiosOfSpanEqTop
namespace GlobalTheory

theorem adjoin_ratios_of_span_eq_top :
    ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (R : Subalgebra K Ω) (m : ℕ) (w : Fin m → R) (k : Fin m), Ideal.span (Set.range w) = ⊤ → (w k : Ω) ≠ 0 → ∀ R' : Subalgebra K Ω, R' = Algebra.adjoin K ((R : Set Ω) ∪ Set.range fun i => (w i : Ω) / (w k : Ω)) → ∃ h : R ≤ R', (w k : Ω)⁻¹ ∈ R' ∧ (Algebra.Smooth K R → Algebra.Smooth K R') ∧ ∀ (L : Type) [Field L] [Algebra K L] (ψ : R →ₐ[K] L), ψ (w k) ≠ 0 → ∃ ψ' : R' →ₐ[K] L, ψ'.comp (Subalgebra.inclusion h) = ψ ∧ ∀ i (hi : (w i : Ω) / (w k : Ω) ∈ R'), ψ' ⟨_, hi⟩ = ψ (w i) / ψ (w k) := by
  intro K Ω _ _ _ R m w k hspan hk R' hR'
  have h : R ≤ R' := by
    rw [hR']; intro x hx; exact Algebra.subset_adjoin (Or.inl hx)
  have hrat : ∀ i, (w i : Ω) / (w k : Ω) ∈ R' := by
    intro i; rw [hR']; exact Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩)
  have hinv : (w k : Ω)⁻¹ ∈ R' := by
    have h1 : (1 : R) ∈ Ideal.span (Set.range w) := by rw [hspan]; trivial
    obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.1 h1
    have h2 : ∑ i, (a i : Ω) * (w i : Ω) = 1 := by
      have := congrArg (fun x : R => (x : Ω)) ha
      simpa using this
    have h3 : (w k : Ω)⁻¹ = ∑ i, (a i : Ω) * ((w i : Ω) / (w k : Ω)) := by
      simp only [← mul_div_assoc, ← Finset.sum_div, h2, one_div]
    rw [h3]
    exact R'.sum_mem fun i _ => R'.mul_mem (h (a i).2) (hrat i)
  letI : Algebra R R' := (Subalgebra.inclusion h).toRingHom.toAlgebra
  haveI : IsScalarTower K R R' := IsScalarTower.of_algebraMap_eq fun x => rfl
  have halg : ∀ x : R, ((algebraMap R R' x : R') : Ω) = x := fun x => rfl
  have hsurj : ∀ z : Ω, z ∈ R' → ∃ (n : ℕ) (a : R), z * (w k : Ω) ^ n = a := by
    intro z hz
    rw [hR'] at hz
    induction hz using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with hx | ⟨i, rfl⟩
      · exact ⟨0, ⟨x, hx⟩, by simp⟩
      · exact ⟨1, w i, by field_simp⟩
    | algebraMap r => exact ⟨0, algebraMap K R r, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨n, a, ha⟩ := hx
      obtain ⟨n', b, hb⟩ := hy
      refine ⟨n + n', a * w k ^ n' + b * w k ^ n, ?_⟩
      push_cast
      rw [← ha, ← hb]; ring
    | mul x y _ _ hx hy =>
      obtain ⟨n, a, ha⟩ := hx
      obtain ⟨n', b, hb⟩ := hy
      refine ⟨n + n', a * b, ?_⟩
      push_cast
      rw [← ha, ← hb]; ring
  haveI hloc : IsLocalization.Away (w k) R' := by
    refine IsLocalization.Away.mk (w k) ?_ ?_ ?_
    · refine IsUnit.of_mul_eq_one ⟨_, hinv⟩ ?_
      apply Subtype.ext
      simp [halg, hk]
    · intro s
      obtain ⟨n, a, ha⟩ := hsurj s s.2
      refine ⟨n, a, Subtype.ext ?_⟩
      simpa [halg] using ha
    · intro a b hab
      refine ⟨0, ?_⟩
      have : (a : Ω) = b := by rw [← halg a, ← halg b, hab]
      rw [Subtype.ext this]
  refine ⟨h, hinv, fun hs => ?_, fun L _ _ ψ hψ => ?_⟩
  · haveI : Algebra.Smooth R R' := Algebra.Smooth.of_isLocalization_Away (w k)
    exact Algebra.Smooth.comp K R R'
  · have hu : IsUnit ((ψ : R →+* L) (w k)) := isUnit_iff_ne_zero.2 hψ
    let φ : R' →+* L := IsLocalization.Away.lift (w k) hu
    have hφ : ∀ x : R, φ (algebraMap R R' x) = ψ x := fun x =>
      IsLocalization.Away.lift_eq (w k) hu x
    refine ⟨{ φ with commutes' := fun r => ?_ }, ?_, fun i hi => ?_⟩
    · change φ (algebraMap K R' r) = _
      rw [IsScalarTower.algebraMap_apply K R R', hφ, AlgHom.commutes]
    · ext x; exact hφ x
    · change φ ⟨_, hi⟩ = _
      rw [eq_div_iff hψ, ← hφ, ← hφ, ← map_mul]
      congr 1
      apply Subtype.ext
      simp [halg, hk]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsIntegralCoeffZeroMulOfAevalInv
namespace GlobalTheory

open Polynomial

theorem _root_.GlobalTheory.isIntegral_mul_of_bounded_at_points :
    ∀ (O O' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [IsAdicComplete (IsLocalRing.maximalIdeal O') O'] [CharZero O'] [Algebra O O'] [IsLocalHom (algebraMap O O')], Function.Injective (algebraMap O O') → (∀ (B : Type) [CommRing B] [IsDomain B] [Algebra O B] [Algebra.FiniteType O B], Function.Injective (algebraMap O B) → ∀ I : Ideal B, I ≠ ⊤ → Ideal.map (algebraMap O B) (IsLocalRing.maximalIdeal O) ≤ I → ∀ e : B, e ≠ 0 → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Algebra O' V) (_ : Module.Finite O' V) (φ : B →+* V), φ.comp (algebraMap O B) = (algebraMap O' V).comp (algebraMap O O') ∧ φ e ≠ 0 ∧ ∀ x ∈ I, φ x ∈ IsLocalRing.maximalIdeal V) → ∀ (A Ω : Type) [CommRing A] [IsDomain A] [Algebra O A] [Algebra.FiniteType O A] [Field Ω] [Algebra A Ω] [IsFractionRing A Ω], Function.Injective (algebraMap O A) → ∀ (e : A), e ≠ 0 → ∀ f : Ω, (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra O' V] [Module.Finite O' V] (φ : A →+* V), φ.comp (algebraMap O A) = (algebraMap O' V).comp (algebraMap O O') → φ e ≠ 0 → ∀ a b : A, f * algebraMap A Ω b = algebraMap A Ω a → φ b ≠ 0 → φ b ∣ φ a) → ∃ s : A, s - 1 ∈ Ideal.map (algebraMap O A) (IsLocalRing.maximalIdeal O) ∧ IsIntegral A (algebraMap A Ω s * f) := by
  intro O O' _ _ _ _ _ _ _ _ _ _ _ hpts A Ω _ _ _ _ _ _ _ hOA e he f hf
  by_cases hf0 : f = 0
  · exact ⟨1, by simp, by simp [hf0, isIntegral_zero]⟩
  obtain ⟨d, c, hc, hdc⟩ := IsFractionRing.div_surjective (A := A) f
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hinj : Function.Injective (algebraMap A Ω) := IsFractionRing.injective A Ω
  have hcΩ : algebraMap A Ω c ≠ 0 := (map_ne_zero_iff _ hinj).2 hc0
  have hfc : f * algebraMap A Ω c = algebraMap A Ω d := by rw [← hdc, div_mul_cancel₀ _ hcΩ]
  set g : Ω := f⁻¹ with hg
  have hgf : g * f = 1 := inv_mul_cancel₀ hf0
  have hgd : g * algebraMap A Ω d = algebraMap A Ω c := by
    rw [← hfc, ← mul_assoc, hgf, one_mul]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hπm : π ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hπ.not_isUnit
  let B := Algebra.adjoin A ({g} : Set Ω)
  letI : Algebra O B := ((algebraMap A B).comp (algebraMap O A)).toAlgebra
  haveI : IsScalarTower O A B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.FiniteType A B :=
    ⟨(Subalgebra.fg_top B).2 (by simpa using Subalgebra.fg_adjoin_finset (R := A) {g})⟩
  haveI : Algebra.FiniteType O B := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  have hOB : Function.Injective (algebraMap O B) := by
    intro x y hxy
    exact hOA (hinj (congrArg Subtype.val hxy))
  let gB : B := ⟨g, Algebra.self_mem_adjoin_singleton A g⟩
  let I : Ideal B := Ideal.span ({gB, algebraMap O B π} : Set B)
  have hI : I = ⊤ := by
    by_contra hI
    have hmI : Ideal.map (algebraMap O B) (IsLocalRing.maximalIdeal O) ≤ I := by
      rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, Ideal.span_le,
        Set.singleton_subset_iff]
      exact Ideal.subset_span (by simp)
    have hec : algebraMap A B (e * c) ≠ 0 := by
      intro h
      exact mul_ne_zero he hc0 (hinj (by simpa using congrArg Subtype.val h))
    obtain ⟨V, _, _, _, _, _, φ, hφ, hφe, hφI⟩ := hpts B hOB I hI hmI _ hec
    let ψ : A →+* V := φ.comp (algebraMap A B)
    have hψ : ψ.comp (algebraMap O A) = (algebraMap O' V).comp (algebraMap O O') := hφ
    have hψec : ψ e * ψ c ≠ 0 := by
      simpa [ψ, map_mul] using hφe
    have hψc : ψ c ≠ 0 := right_ne_zero_of_mul hψec
    obtain ⟨t, ht⟩ := hf V ψ hψ (left_ne_zero_of_mul hψec) d c hfc hψc
    have hmem : φ gB ∈ IsLocalRing.maximalIdeal V := hφI gB (Ideal.subset_span (by simp))
    have h1 : φ gB * ψ d = ψ c := by
      simp only [ψ, RingHom.comp_apply, ← map_mul]
      congr 1
      exact Subtype.ext hgd
    have hu : IsUnit (φ gB) := by
      refine IsUnit.of_mul_eq_one t ?_
      have h2 : ψ c * (φ gB * t) = ψ c * 1 := by linear_combination (-φ gB) * ht + h1
      exact mul_left_cancel₀ hψc h2
    exact ((IsLocalRing.mem_maximalIdeal _).1 hmem) hu
  have hone : (1 : B) ∈ I := hI ▸ Submodule.mem_top
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 hone
  have hpoly : ∀ x : B, ∃ p : A[X], aeval g p = (x : Ω) := by
    intro x
    have hx : (x : Ω) ∈ Algebra.adjoin A ({g} : Set Ω) := x.2
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hx
    exact (AlgHom.mem_range _).1 hx
  obtain ⟨p, hp⟩ := hpoly a
  obtain ⟨r, hr⟩ := hpoly b
  have hΩ : (a : Ω) * g + (b : Ω) * algebraMap A Ω (algebraMap O A π) = 1 :=
    congrArg Subtype.val hab
  let H : A[X] := 1 - X * p - C (algebraMap O A π) * r
  have hH : aeval g H = 0 := by
    simp only [H, map_sub, map_one, map_mul, aeval_X, aeval_C, hp, hr]
    linear_combination -hΩ
  letI : Invertible g := invertibleOfNonzero (inv_ne_zero hf0)
  have hrev : aeval f (reverse H) = 0 := by
    have key := eval₂_reverse_mul_pow (algebraMap A Ω) g H
    have hinv : ⅟g = f := by rw [invOf_eq_inv, hg, inv_inv]
    rw [hinv, ← aeval_def, ← aeval_def, hH] at key
    exact (mul_eq_zero.1 key).resolve_right (pow_ne_zero _ (inv_ne_zero hf0))
  have hint := isIntegral_leadingCoeff_smul (reverse H) f hrev
  have hcoeff : H.coeff 0 = 1 - algebraMap O A π * r.coeff 0 := by simp [H]
  refine ⟨H.coeff 0, ?_, ?_⟩
  · rw [hcoeff, sub_sub_cancel_left]
    exact (Ideal.neg_mem_iff _).2 (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hπm))
  · by_cases h0 : H.coeff 0 = 0
    · rw [h0, map_zero, zero_mul]
      exact isIntegral_zero
    · have hlead : (reverse H).leadingCoeff = H.coeff 0 := by
        rw [reverse_leadingCoeff, trailingCoeff, natTrailingDegree_eq_zero.2 (Or.inr h0)]
      rw [← hlead, ← Algebra.smul_def]
      exact hint

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIsMaximalTensorProductOfIsLocalHom
open TensorProduct

namespace GlobalTheory

theorem flat_of_injective_algebraMap_of_isDomain (O A : Type*) [CommRing O] [IsDomain O]
    [IsPrincipalIdealRing O] [CommRing A] [IsDomain A] [Algebra O A]
    (h : Function.Injective (algebraMap O A)) : Module.Flat O A := by
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  rintro m ⟨⟨r, hr⟩, hm⟩
  rw [Submodule.mem_bot]
  have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
  have hmul : algebraMap O A r * m = 0 := by rw [← Algebra.smul_def]; exact hm
  exact (mul_eq_zero.mp hmul).resolve_left ((map_ne_zero_iff _ h).mpr hr0)

theorem one_tmul_mem_nonZeroDivisors_of_flat (O A B : Type*) [CommRing O] [CommRing A]
    [CommRing B] [IsDomain B] [Algebra O A] [Algebra O B] [Module.Flat O A] {b : B} (hb : b ≠ 0) :
    ((1 : A) ⊗ₜ[O] b) ∈ nonZeroDivisors (A ⊗[O] B) := by
  have hinj : Function.Injective (LinearMap.lTensor A (LinearMap.mulRight O b)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (mul_left_injective₀ hb)
  have key : ∀ x : A ⊗[O] B, LinearMap.lTensor A (LinearMap.mulRight O b) x = x * (1 ⊗ₜ[O] b) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a c => simp [Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => rw [map_add (f := _), hx, hy, add_mul]
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  exact hinj (by rw [key, map_zero, hx])

theorem tmul_one_mem_nonZeroDivisors_of_flat (O A B : Type*) [CommRing O] [CommRing A]
    [CommRing B] [IsDomain A] [Algebra O A] [Algebra O B] [Module.Flat O B] {a : A} (ha : a ≠ 0) :
    (a ⊗ₜ[O] (1 : B)) ∈ nonZeroDivisors (A ⊗[O] B) := by
  have hinj : Function.Injective (LinearMap.rTensor B (LinearMap.mulRight O a)) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (mul_left_injective₀ ha)
  have key : ∀ x : A ⊗[O] B, LinearMap.rTensor B (LinearMap.mulRight O a) x = x * (a ⊗ₜ[O] (1 : B)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c d => simp [Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => rw [map_add (f := _), hx, hy, add_mul]
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  exact hinj (by rw [key, map_zero, hx])

theorem exists_isMaximal_tensorProduct_of_isLocalHom (O O' B : Type*) [CommRing O] [IsLocalRing O]
    [CommRing O'] [IsLocalRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')]
    [CommRing B] [Algebra O B] (I : Ideal B) (hI : I ≠ ⊤)
    (hm : Ideal.map (algebraMap O B) (IsLocalRing.maximalIdeal O) ≤ I) :
    ∃ M : Ideal (O' ⊗[O] B), M.IsMaximal ∧
      (∀ a ∈ IsLocalRing.maximalIdeal O', a ⊗ₜ[O] (1 : B) ∈ M) ∧
      ∀ b ∈ I, (1 : O') ⊗ₜ[O] b ∈ M := by
  obtain ⟨N, hN, hIN⟩ := Ideal.exists_le_maximal I hI
  have hle : IsLocalRing.maximalIdeal O ≤ N.comap (algebraMap O B) :=
    Ideal.map_le_iff_le_comap.mp (hm.trans hIN)
  letI : Algebra (IsLocalRing.ResidueField O) (B ⧸ N) :=
    Ideal.Quotient.algebraQuotientOfLEComap hle
  haveI : IsScalarTower O (IsLocalRing.ResidueField O) (B ⧸ N) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Nontrivial (IsLocalRing.ResidueField O' ⊗[IsLocalRing.ResidueField O] (B ⧸ N)) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain _ _ _
      (RingHom.injective (algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O'))) (RingHom.injective (algebraMap (IsLocalRing.ResidueField O) (B ⧸ N)))
  let f : O' →ₐ[O] IsLocalRing.ResidueField O' ⊗[IsLocalRing.ResidueField O] (B ⧸ N) :=
    (Algebra.TensorProduct.includeLeft).comp (IsScalarTower.toAlgHom O O' (IsLocalRing.ResidueField O'))
  let g : B →ₐ[O] IsLocalRing.ResidueField O' ⊗[IsLocalRing.ResidueField O] (B ⧸ N) :=
    ((Algebra.TensorProduct.includeRight).restrictScalars O).comp (IsScalarTower.toAlgHom O B (B ⧸ N))
  let ψ := Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)
  obtain ⟨M, hM, hkM⟩ := Ideal.exists_le_maximal (RingHom.ker ψ.toRingHom) (RingHom.ker_ne_top _)
  refine ⟨M, hM, fun a ha => hkM ?_, fun b hb => hkM ?_⟩
  · rw [RingHom.mem_ker]
    have h0 : IsLocalRing.residue O' a = 0 :=
      (IsLocalRing.residue_eq_zero_iff a).mpr ha
    simp [ψ, f, g, Algebra.TensorProduct.lift_tmul, h0]
  · rw [RingHom.mem_ker]
    have h0 : Ideal.Quotient.mk N b = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (hIN hb)
    simp [ψ, f, g, Algebra.TensorProduct.lift_tmul, h0]

theorem exists_integral_point_of_complete_case :
    (∀ (O B : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [CharZero O] [CommRing B] [IsDomain B] [Algebra O B] [Algebra.FiniteType O B] [Module.Flat O B] (M : Ideal B), M.IsMaximal → Ideal.map (algebraMap O B) (IsLocalRing.maximalIdeal O) ≤ M → ∀ e : B, e ≠ 0 → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Algebra O V) (_ : Module.Finite O V) (φ : B →ₐ[O] V), φ e ≠ 0 ∧ ∀ x ∈ M, φ x ∈ IsLocalRing.maximalIdeal V) → ∀ (O O' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [IsAdicComplete (IsLocalRing.maximalIdeal O') O'] [CharZero O'] [Algebra O O'] [IsLocalHom (algebraMap O O')], Function.Injective (algebraMap O O') → ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra O B] [Algebra.FiniteType O B], Function.Injective (algebraMap O B) → ∀ I : Ideal B, I ≠ ⊤ → Ideal.map (algebraMap O B) (IsLocalRing.maximalIdeal O) ≤ I → ∀ e : B, e ≠ 0 → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Algebra O' V) (_ : Module.Finite O' V) (φ : B →+* V), φ.comp (algebraMap O B) = (algebraMap O' V).comp (algebraMap O O') ∧ φ e ≠ 0 ∧ ∀ x ∈ I, φ x ∈ IsLocalRing.maximalIdeal V := by
  intro H O O' _ _ _ _ _ _ _ _ _ _ hOO' B _ _ _ _ hOB I hI hmI e he
  haveI : Module.Flat O O' := flat_of_injective_algebraMap_of_isDomain O O' hOO'
  haveI : Module.Flat O B := flat_of_injective_algebraMap_of_isDomain O B hOB
  obtain ⟨M, hM, hM1, hM2⟩ := exists_isMaximal_tensorProduct_of_isLocalHom O O' B I hI hmI
  obtain ⟨P, hPmin, hPM⟩ := Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal (O' ⊗[O] B)) ≤ M)
  haveI : P.IsPrime := hPmin.isPrime
  haveI : IsDomain (O' ⊗[O] B ⧸ P) := Ideal.Quotient.isDomain P
  have hinj : Function.Injective (algebraMap O' (O' ⊗[O] B ⧸ P)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra ha0
    have ha' : Ideal.Quotient.mk P (a ⊗ₜ[O] (1 : B)) = 0 := ha
    exact notMem_nonZeroDivisors_of_mem_mem_minimalPrimes (Ideal.Quotient.eq_zero_iff_mem.mp ha')
      hPmin (tmul_one_mem_nonZeroDivisors_of_flat O O' B ha0)
  haveI : Module.Flat O' (O' ⊗[O] B ⧸ P) := flat_of_injective_algebraMap_of_isDomain _ _ hinj
  haveI : Algebra.FiniteType O' (O' ⊗[O] B ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ O' P)
      (Ideal.Quotient.mkₐ_surjective O' P)
  have hM' : (M.map (Ideal.Quotient.mk P)).IsMaximal := by
    refine (Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective hM).resolve_left ?_
    intro htop
    have h1 : (1 : O' ⊗[O] B ⧸ P) ∈ M.map (Ideal.Quotient.mk P) := by rw [htop]; exact Submodule.mem_top
    obtain ⟨m, hm, hm1⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp h1
    have hmP : m - 1 ∈ P := Ideal.Quotient.eq.mp (by rw [hm1, map_one])
    exact hM.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using M.sub_mem hm (hPM hmP)))
  have hmap : Ideal.map (algebraMap O' (O' ⊗[O] B ⧸ P)) (IsLocalRing.maximalIdeal O') ≤
      M.map (Ideal.Quotient.mk P) :=
    Ideal.map_le_iff_le_comap.mpr fun a ha => Ideal.mem_map_of_mem (Ideal.Quotient.mk P) (hM1 a ha)
  have he' : Ideal.Quotient.mk P ((1 : O') ⊗ₜ[O] e) ≠ 0 := by
    intro h0
    exact notMem_nonZeroDivisors_of_mem_mem_minimalPrimes (Ideal.Quotient.eq_zero_iff_mem.mp h0)
      hPmin (one_tmul_mem_nonZeroDivisors_of_flat O O' B he)
  obtain ⟨V, i₁, i₂, i₃, i₄, i₅, φ, hφe, hφM⟩ :=
    H O' (O' ⊗[O] B ⧸ P) (M.map (Ideal.Quotient.mk P)) hM' hmap _ he'
  refine ⟨V, i₁, i₂, i₃, i₄, i₅,
    φ.toRingHom.comp ((Ideal.Quotient.mk P).comp
      (Algebra.TensorProduct.includeRight : B →ₐ[O] O' ⊗[O] B).toRingHom), ?_, hφe, ?_⟩
  · ext o
    have h1 : (Algebra.TensorProduct.includeRight : B →ₐ[O] O' ⊗[O] B) (algebraMap O B o) =
        algebraMap O' (O' ⊗[O] B) (algebraMap O O' o) := by
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply O O' (O' ⊗[O] B)]
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, h1]
    exact φ.commutes _
  · intro x hx
    exact hφM _ (Ideal.mem_map_of_mem (Ideal.Quotient.mk P) (hM2 x hx))

end GlobalTheory
end
