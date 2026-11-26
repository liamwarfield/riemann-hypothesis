module

public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.PolyChartSmoothFractionLift
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsRatioFormsAtPoints

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFlagCellChartOverFramedAffineOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFlagCoordinatesCellChangeBirational
section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFlagCoordinatesCellChangeBirational
namespace GlobalTheory.Reg.CellChange

open Matrix

theorem exists_algEquiv_of_generates {κ ι : Type} [Field κ] [Finite ι] (y : ι → FractionRing (MvPolynomial ι κ))
    (hy : ∀ v, algebraMap (MvPolynomial ι κ) (FractionRing (MvPolynomial ι κ)) (MvPolynomial.X v) ∈
      IntermediateField.adjoin κ (Set.range y)) :
    ∃ e : FractionRing (MvPolynomial ι κ) ≃ₐ[κ] FractionRing (MvPolynomial ι κ),
      ∀ v, e (algebraMap (MvPolynomial ι κ) _ (MvPolynomial.X v)) = y v := by
  have htop : IntermediateField.adjoin κ (Set.range y) = ⊤ := by
    have hp : ∀ p : MvPolynomial ι κ, algebraMap (MvPolynomial ι κ) (FractionRing (MvPolynomial ι κ)) p ∈
        IntermediateField.adjoin κ (Set.range y) := by
      intro p
      induction p using MvPolynomial.induction_on with
      | C a =>
        rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
        exact IntermediateField.algebraMap_mem _ a
      | add p q hp hq => rw [map_add]; exact add_mem hp hq
      | mul_X p v hp => rw [map_mul]; exact mul_mem hp (hy v)
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial ι κ) x
    exact div_mem (hp a) (hp b)
  have hX : AlgebraicIndependent κ (fun v : ι =>
      algebraMap (MvPolynomial ι κ) (FractionRing (MvPolynomial ι κ)) (MvPolynomial.X v)) :=
    (MvPolynomial.algebraicIndependent_X ι κ).map'
      (f := IsScalarTower.toAlgHom κ (MvPolynomial ι κ) (FractionRing (MvPolynomial ι κ)))
      (IsFractionRing.injective _ _)
  have halg : Algebra.IsAlgebraic (Algebra.adjoin κ (Set.range y)) (FractionRing (MvPolynomial ι κ)) := by
    rw [← IntermediateField.isAlgebraic_adjoin_iff_top, htop]
    exact ⟨fun x => isAlgebraic_algebraMap (⟨x, trivial⟩ : (⊤ : IntermediateField κ _))⟩
  have hind : AlgebraicIndependent κ y :=
    (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite κ y hX.cardinalMk_le_trdeg).1
  have hinj : Function.Injective (MvPolynomial.aeval y : MvPolynomial ι κ →ₐ[κ] _) :=
    algebraicIndependent_iff_injective_aeval.1 hind
  let f : FractionRing (MvPolynomial ι κ) →ₐ[κ] FractionRing (MvPolynomial ι κ) :=
    IsFractionRing.liftAlgHom hinj
  have hf : ∀ v, f (algebraMap (MvPolynomial ι κ) _ (MvPolynomial.X v)) = y v := by
    intro v
    simp [f]
  have hs : Function.Surjective f := by
    have : IntermediateField.adjoin κ (Set.range y) ≤ f.fieldRange := by
      rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨v, rfl⟩
      exact ⟨_, hf v⟩
    intro x
    exact this (htop ▸ IntermediateField.mem_top)
  exact ⟨AlgEquiv.ofBijective f ⟨f.injective, hs⟩, hf⟩

theorem minors_iff {R : Type} [CommRing R] {n : ℕ} (g : Matrix (Fin n) (Fin n) R) :
    (∀ k (hk : k ≤ n), IsUnit (g.submatrix (Fin.castLE hk) (Fin.castLE hk)).det) ↔
      ∃ u b : Matrix (Fin n) (Fin n) R, (∀ i j : Fin n, i < j → u i j = 0) ∧ (∀ i, u i i = 1) ∧
        b.BlockTriangular id ∧ (∀ i, IsUnit (b i i)) ∧ g = u * b :=
  (GlobalTheory.cell_coordinates_exists_unique R n n (Function.Embedding.refl _) g).1

theorem upper_inv {R : Type} [CommRing R] {n : ℕ} (b : Matrix (Fin n) (Fin n) R) (hb : b.BlockTriangular id)
    (hu : ∀ i, IsUnit (b i i)) : b⁻¹.BlockTriangular id ∧ (∀ i, IsUnit (b⁻¹ i i)) ∧ b * b⁻¹ = 1 := by
  have hd := GlobalTheory.isUnit_det_of_upper_of_isUnit_diag b hb hu
  have hbi : b⁻¹.BlockTriangular id := by
    let _ := Matrix.invertibleOfIsUnitDet b hd
    exact Matrix.blockTriangular_inv_of_blockTriangular hb
  refine ⟨hbi, fun i => ?_, Matrix.mul_nonsing_inv _ hd⟩
  have h1 : IsUnit b⁻¹.det := Matrix.isUnit_nonsing_inv_det _ hd
  rw [Matrix.det_of_isUpperTriangular hbi] at h1
  exact IsUnit.prod_iff.1 h1 i (Finset.mem_univ _)

theorem upper_mul_diag {R : Type} [CommRing R] {n : ℕ} (b c : Matrix (Fin n) (Fin n) R) (hb : b.BlockTriangular id)
    (hu : ∀ i, IsUnit (b i i)) (hc : c.BlockTriangular id) (hv : ∀ i, IsUnit (c i i)) (i : Fin n) :
    IsUnit ((b * c) i i) := by
  have h1 : IsUnit (b * c).det := by
    rw [Matrix.det_mul]
    exact (GlobalTheory.isUnit_det_of_upper_of_isUnit_diag b hb hu).mul (GlobalTheory.isUnit_det_of_upper_of_isUnit_diag c hc hv)
  rw [Matrix.det_of_isUpperTriangular (hb.mul hc)] at h1
  exact IsUnit.prod_iff.1 h1 i (Finset.mem_univ _)

theorem lower_mem_range {F K : Type} [Field F] [Field K] (φ : F →+* K) {n : ℕ} (M : Matrix (Fin n) (Fin n) F)
    (l b : Matrix (Fin n) (Fin n) K) (h0 : ∀ i j : Fin n, i < j → l i j = 0) (h1 : ∀ i, l i i = 1)
    (hb : b.BlockTriangular id) (hu : ∀ i, IsUnit (b i i)) (h : M.map φ = l * b) (i j : Fin n) :
    ∃ x, φ x = l i j := by
  have hm := (minors_iff (M.map φ)).2 ⟨l, b, h0, h1, hb, hu, h⟩
  obtain ⟨u, c, hu0, hu1, hc, hcu, hM⟩ := (minors_iff M).1 (fun k hk => by
    have h2 := hm k hk
    rw [Matrix.submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h2
    rw [isUnit_iff_ne_zero] at h2 ⊢
    intro h3
    exact h2 (by rw [h3, map_zero]))
  have := (GlobalTheory.cell_coordinates_exists_unique K n n (Function.Embedding.refl _) l).2 l (u.map φ) b (c.map φ)
    ⟨h0, h1⟩ ⟨fun i j hij => by simpa using hu0 i j hij, fun i => by simp [hu1 i]⟩ hb
    (hc.map φ) hu (by rw [← h, hM, Matrix.map_mul])
  exact ⟨u i j, by rw [this.1]; rfl⟩

theorem exists_lower_minors {κ : Type} [Field κ] {n : ℕ} (A : Matrix (Fin n) (Fin n) κ) (hA : IsUnit A.det) :
    ∃ l : Matrix (Fin n) (Fin n) (RatFunc κ), (∀ i j : Fin n, i < j → l i j = 0) ∧ (∀ i, l i i = 1) ∧
      ∀ k (hk : k ≤ n), IsUnit ((A.map (algebraMap κ (RatFunc κ)) * l).submatrix
        (Fin.castLE hk) (Fin.castLE hk)).det := by
  have key : ∀ M : Matrix (Fin n) (Fin n) (Polynomial κ),
      (∀ k (hk : k ≤ n), (M.submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0) →
      ∀ k (hk : k ≤ n), IsUnit ((M.map (algebraMap _ (RatFunc κ))).submatrix
        (Fin.castLE hk) (Fin.castLE hk)).det := by
    intro M hM k hk
    rw [Matrix.submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det, isUnit_iff_ne_zero]
    exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (hM k hk)
  obtain ⟨l, b, h0, h1, hb, hu, h⟩ := (minors_iff _).1 (key (Matrix.charmatrix (-A⁻¹)) (fun k hk => by
    have : (Matrix.charmatrix (-A⁻¹)).submatrix (Fin.castLE hk) (Fin.castLE hk) =
        Matrix.charmatrix ((-A⁻¹).submatrix (Fin.castLE hk) (Fin.castLE hk)) := by
      ext i j : 2
      simp [Matrix.charmatrix_apply, Matrix.diagonal_apply]
    rw [this]
    exact (Matrix.charpoly_monic _).ne_zero))
  obtain ⟨u, c, hu0, hu1, hc, hcu, h'⟩ := (minors_iff _).1
    (key (1 + (Polynomial.X : Polynomial κ) • A.map Polynomial.C) (fun k hk h2 => by
      have h3 := congrArg (Polynomial.evalRingHom (0 : κ)) h2
      rw [RingHom.map_det, map_zero] at h3
      have : (Polynomial.evalRingHom (0 : κ)).mapMatrix ((1 + (Polynomial.X : Polynomial κ) •
          A.map Polynomial.C).submatrix (Fin.castLE hk) (Fin.castLE hk)) = 1 := by
        ext i j
        simp [Matrix.one_apply, apply_ite]
      rw [this, Matrix.det_one] at h3
      exact one_ne_zero h3))
  obtain ⟨hbi, hbu, hbb⟩ := upper_inv b hb hu
  refine ⟨l, h0, h1, (minors_iff _).2 ⟨u, c * b⁻¹, hu0, hu1, hc.mul hbi, upper_mul_diag _ _ hc hcu hbi hbu, ?_⟩⟩
  have e1 : A.map Polynomial.C * Matrix.charmatrix (-A⁻¹) = 1 + (Polynomial.X : Polynomial κ) • A.map Polynomial.C := by
    rw [Matrix.charmatrix, Matrix.mul_sub, map_neg, Matrix.mul_neg, RingHom.mapMatrix_apply, ← Matrix.map_mul,
      Matrix.mul_nonsing_inv _ hA, sub_neg_eq_add, add_comm, Matrix.map_one _ (map_zero _) (map_one _)]
    congr 1
    ext i j : 2
    rw [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul, mul_comm]
  have e2 : A.map (algebraMap κ (RatFunc κ)) = (A.map Polynomial.C).map (algebraMap _ (RatFunc κ)) := by
    ext i j
    exact IsScalarTower.algebraMap_apply κ (Polynomial κ) (RatFunc κ) (A i j)
  rw [← Matrix.mul_assoc, ← h', ← e1, Matrix.map_mul, h, ← e2, Matrix.mul_assoc, Matrix.mul_assoc, hbb,
    Matrix.mul_one]

section Low
variable {T S S' : Type} [CommRing S] [CommRing S'] {r : T → ℕ}

theorem lowM_upper (x : (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) → S) (τ : T) (i j : Fin (r τ))
    (h : i < j) : lowM x τ i j = 0 := by
  simp [lowM, h.not_gt, h.ne']

theorem lowM_diag (x : (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) → S) (τ : T) (i : Fin (r τ)) :
    lowM x τ i i = 1 := by
  simp [lowM]

theorem lowM_entry (x : (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) → S)
    (v : Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) : lowM x v.1 v.2.1.2 v.2.1.1 = x v := by
  obtain ⟨τ, ⟨i, j⟩, h⟩ := v
  exact dite_eq_left h

theorem lowM_map (f : S →+* S') (x : (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) → S) (τ : T) :
    (lowM x τ).map f = lowM (fun v => f (x v)) τ := by
  ext i j
  simp only [lowM, Matrix.map_apply]
  split_ifs <;> simp

theorem lowM_of_lower (l : ∀ τ, Matrix (Fin (r τ)) (Fin (r τ)) S) (τ : T)
    (h0 : ∀ i j, i < j → l τ i j = 0) (h1 : ∀ i, l τ i i = 1) :
    lowM (fun v : (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) => l v.1 v.2.1.2 v.2.1.1) τ = l τ := by
  ext i j
  simp only [lowM]
  split_ifs with h h'
  · rfl
  · rw [h', h1]
  · exact (h0 i j (lt_of_le_of_ne (not_lt.1 h) (Ne.symm h'))).symm

end Low

theorem generic_minors {κ T : Type} [Field κ] {r : T → ℕ} (A : ∀ τ, Matrix (Fin (r τ)) (Fin (r τ)) κ)
    (hA : ∀ τ, IsUnit (A τ).det) (τ : T) (k : ℕ) (hk : k ≤ r τ) :
    (((A τ).map (algebraMap κ (MvPolynomial (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) κ)) *
      lowM MvPolynomial.X τ).submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0 := by
  choose l h0 h1 hm using fun τ => exists_lower_minors (A τ) (hA τ)
  intro h
  let φ : MvPolynomial (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) κ →ₐ[κ] RatFunc κ :=
    MvPolynomial.aeval (fun v => l v.1 v.2.1.2 v.2.1.1)
  have h2 := congrArg φ.toRingHom h
  rw [RingHom.map_det, map_zero, RingHom.mapMatrix_apply, ← Matrix.submatrix_map, Matrix.map_mul, lowM_map] at h2
  apply (hm τ k hk).ne_zero
  rw [← h2, ← lowM_of_lower l τ (h0 τ) (h1 τ)]
  congr 3
  · ext i j
    exact (φ.commutes _).symm
  · congr 1
    funext v
    simp [φ]

end GlobalTheory.Reg.CellChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem GlobalTheory.Reg.cell_change_birational :
    ∀ (κ T : Type) [Field κ] [Infinite κ] [Finite T] (r : T → ℕ) (G : ∀ τ, Matrix (Fin (r τ)) (Fin (r τ)) κ) (σ : ∀ τ, Equiv.Perm (Fin (r τ))), (∀ τ, IsUnit (G τ).det) → ∃ (e : FractionRing (MvPolynomial (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) κ) ≃ₐ[κ] FractionRing (MvPolynomial (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) κ)) (b : ∀ τ, Matrix (Fin (r τ)) (Fin (r τ)) (FractionRing (MvPolynomial (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) κ))), (∀ τ, (b τ).BlockTriangular id ∧ ∀ i, b τ i i ≠ 0) ∧ ∀ τ, (G τ).map (algebraMap κ _) * lowM (fun v => algebraMap (MvPolynomial _ κ) _ (MvPolynomial.X v)) τ = (lowM (fun v => e (algebraMap (MvPolynomial _ κ) _ (MvPolynomial.X v))) τ).submatrix (σ τ).symm id * b τ := by
  intro κ T _ _ _ r G σ hG
  let P := MvPolynomial (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) κ
  let K := FractionRing P
  let A : ∀ τ, Matrix (Fin (r τ)) (Fin (r τ)) κ := fun τ => (G τ).submatrix (σ τ) id
  have hA : ∀ τ, IsUnit (A τ).det := fun τ => by
    simp only [A]
    rw [Matrix.det_permute]
    exact (((Equiv.Perm.sign (σ τ)).isUnit).map (Int.castRingHom κ)).mul (hG τ)
  have hdec := fun τ => (CellChange.minors_iff ((A τ).map (algebraMap κ K) *
      lowM (fun v => algebraMap P K (MvPolynomial.X v)) τ)).1 (fun k hk => by
    have h := (map_ne_zero_iff (algebraMap P K) (IsFractionRing.injective _ _)).2
      (CellChange.generic_minors A hA τ k hk)
    rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.submatrix_map, Matrix.map_mul, CellChange.lowM_map,
      Matrix.map_map] at h
    exact isUnit_iff_ne_zero.2 h)
  choose l b h0 h1 hb hu h using hdec
  obtain ⟨e, he⟩ := CellChange.exists_algEquiv_of_generates
    (fun v : (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) => l v.1 v.2.1.2 v.2.1.1) (fun v => by
      set y : (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) → K := fun v => l v.1 v.2.1.2 v.2.1.1 with hy
      let F := IntermediateField.adjoin κ (Set.range y)
      obtain ⟨hbi, hbu, hbb⟩ := CellChange.upper_inv _ (hb v.1) (hu v.1)
      obtain ⟨x, hx⟩ := CellChange.lower_mem_range (algebraMap F K)
        ((A v.1)⁻¹.map (algebraMap κ F) * lowM (fun w => (⟨y w, IntermediateField.subset_adjoin _ _ ⟨w, rfl⟩⟩ : F)) v.1)
        (lowM (fun v => algebraMap P K (MvPolynomial.X v)) v.1) (b v.1)⁻¹
        (CellChange.lowM_upper _ _) (CellChange.lowM_diag _ _) hbi hbu (by
          rw [Matrix.map_mul, CellChange.lowM_map, Matrix.map_map]
          change (A v.1)⁻¹.map (algebraMap κ K) * lowM y v.1 = _
          rw [hy, CellChange.lowM_of_lower l v.1 (h0 _) (h1 _), ← Matrix.mul_one (l v.1), ← hbb,
            ← Matrix.mul_assoc (l v.1), ← h, Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul,
            Matrix.nonsing_inv_mul _ (hA _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul])
        v.2.1.2 v.2.1.1
      rw [CellChange.lowM_entry] at hx
      have hx' : (x : K) ∈ F := x.2
      exact hx ▸ hx')
  refine ⟨e, b, fun τ => ⟨hb τ, fun i => (hu τ i).ne_zero⟩, fun τ => ?_⟩
  simp only [he]
  rw [CellChange.lowM_of_lower l τ (h0 τ) (h1 τ)]
  ext i j
  have := congrFun (congrFun (h τ) ((σ τ).symm i)) j
  simpa [A, Matrix.mul_apply] using this
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFlagCoordinatesCellChangeBirationalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flagCoordinates_cellChange_birational : ∀ (κ T : Type) [Field κ] [Infinite κ] [Finite T] (r : T → ℕ) (G : ∀ τ, Matrix (Fin (r τ)) (Fin (r τ)) κ) (σ : ∀ τ, Equiv.Perm (Fin (r τ))), (∀ τ, IsUnit (G τ).det) → ∃ (e : FractionRing (MvPolynomial (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) κ) ≃ₐ[κ] FractionRing (MvPolynomial (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) κ)) (b : ∀ τ, Matrix (Fin (r τ)) (Fin (r τ)) (FractionRing (MvPolynomial (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) κ))), (∀ τ, (b τ).BlockTriangular id ∧ ∀ i, b τ i i ≠ 0) ∧ ∀ τ, (G τ).map (algebraMap κ _) * lowM (fun v => algebraMap (MvPolynomial _ κ) _ (MvPolynomial.X v)) τ = (lowM (fun v => e (algebraMap (MvPolynomial _ κ) _ (MvPolynomial.X v))) τ).submatrix (σ τ).symm id * b τ := by
  first | exact @GlobalTheory.Reg.cell_change_birational | exact GlobalTheory.Reg.cell_change_birational | (intros; apply GlobalTheory.Reg.cell_change_birational <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFlagCellChartOverFramedAffineOpen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg.CellChart

theorem spMap_inj {A S : Type} [CommRing A] [CommRing S] {f g : A →+* S} (h : spMap f = spMap g) : f = g := by
  have := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom this

theorem exists_spMap {A S : Type} [CommRing A] [CommRing S] (m : Sp S ⟶ Sp A) : ∃ f : A →+* S, spMap f = m :=
  ⟨(Spec.preimage m).hom, Spec.map_preimage m⟩

theorem exists_algHom_fac {K A S : Type} [CommRing K] [CommRing A] [Algebra K A] [CommRing S] [Algebra K S]
    {X : Scheme.{0}} (s : X ⟶ Sp K) (j : Sp A ⟶ X) [IsOpenImmersion j] (hj : j ≫ s = spMap (algebraMap K A))
    (W : Sp S ⟶ X) (hW : W ≫ s = spMap (algebraMap K S)) (hr : Set.range W ⊆ Set.range j) :
    ∃ f : A →ₐ[K] S, spMap f.toRingHom ≫ j = W := by
  obtain ⟨f, hf⟩ := exists_spMap (IsOpenImmersion.lift j W hr)
  have h1 : spMap f ≫ j = W := by rw [hf, IsOpenImmersion.lift_fac]
  have h2 : f.comp (algebraMap K A) = algebraMap K S := by
    apply spMap_inj
    rw [← spMap_comp_ring, ← hj, ← Category.assoc, h1, hW]
  exact ⟨{ f with commutes' := fun a => DFunLike.congr_fun h2 a }, h1⟩

theorem exists_away_fac {K A S L : Type} [CommRing K] [CommRing A] [Algebra K A] [CommRing S] [Algebra K S] [Field L]
    {X : Scheme.{0}} (s : X ⟶ Sp K) (j : Sp A ⟶ X) [IsOpenImmersion j] (hj : j ≫ s = spMap (algebraMap K A))
    (W : Sp S ⟶ X) (hW : W ≫ s = spMap (algebraMap K S)) (χ : S →+* L) (f : A →+* L)
    (h : spMap χ ≫ W = spMap f ≫ j) :
    ∃ g : S, χ g ≠ 0 ∧ ∃ f₁ : A →ₐ[K] Localization.Away g,
      spMap f₁.toRingHom ≫ j = spMap (algebraMap S (Localization.Away g)) ≫ W := by
  let p : PrimeSpectrum S := PrimeSpectrum.comap χ ⟨⊥, Ideal.isPrime_bot⟩
  have hp : p ∈ (W ⁻¹ᵁ j.opensRange : (Sp S).Opens) := by
    have e := congrArg (fun m : Sp L ⟶ X => m (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum L)) h
    simp only [Scheme.Hom.comp_apply] at e
    exact ⟨_, e.symm⟩
  obtain ⟨_, ⟨g, rfl⟩, hg, hle⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    hp (W ⁻¹ᵁ j.opensRange).isOpen
  refine ⟨g, fun h0 => hg (show χ g ∈ (⊥ : Ideal L) from h0), ?_⟩
  refine exists_algHom_fac s j hj _ ?_ ?_
  · rw [Category.assoc, hW, spMap_comp_ring, ← IsScalarTower.algebraMap_eq]
  · rintro _ ⟨q, rfl⟩
    rw [Scheme.Hom.comp_apply]
    refine hle (a := PrimeSpectrum.comap (algebraMap S (Localization.Away g)) q) ?_
    intro hq
    exact q.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hq (IsLocalization.Away.algebraMap_isUnit g))

theorem closure_range_mem {A : Type} [CommRing A] [IsDomain A] {X : Scheme.{0}} (j : Sp A ⟶ X) [IsOpenImmersion j] :
    closure (Set.range j) ∈ irreducibleComponents X := by
  have hi : IsIrreducible (Set.range j) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ j.continuous.continuousOn
  refine ⟨hi.closure, fun t ht hle => ?_⟩
  have ho : IsOpen (Set.range j) := j.isOpenEmbedding.isOpen_range
  have hne : (t ∩ Set.range j).Nonempty := by
    obtain ⟨x, hx⟩ := hi.nonempty
    exact ⟨x, hle (subset_closure hx), hx⟩
  exact (subset_closure_inter_of_isPreirreducible_of_isOpen ht.isPreirreducible ho hne).trans
    (closure_mono Set.inter_subset_right)

theorem exists_residue_embed {A : Type} [CommRing A] [IsDomain A] {X : Scheme.{0}} (j : Sp A ⟶ X)
    (x : X) (hx : IsGenericPoint x (closure (Set.range j))) :
    Set.range (X.fromSpecResidueField x) ⊆ Set.range j ∧ ∃ β : X.residueField x ⟶ CommRingCat.of (FractionRing A),
      Spec.map β ≫ X.fromSpecResidueField x = spMap (algebraMap A (FractionRing A)) ≫ j := by
  let m : Sp (FractionRing A) ⟶ X := spMap (algebraMap A (FractionRing A)) ≫ j
  have h0 : IsGenericPoint (j (⊥ : PrimeSpectrum A)) (closure (Set.range j)) := by
    have := (genericPoint_spec (Sp A)).image j.continuous
    rw [genericPoint_eq_bot_of_affine (CommRingCat.of A), Set.image_univ] at this
    exact this
  have h1 : x = m (IsLocalRing.closedPoint (FractionRing A)) := by
    refine (hx.eq h0).trans (Eq.trans (congrArg j ?_) (Scheme.Hom.comp_apply _ _ _).symm)
    apply PrimeSpectrum.ext
    show (⊥ : Ideal A) = Ideal.comap (algebraMap A (FractionRing A)) (IsLocalRing.maximalIdeal _)
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.comap_bot_of_injective _ (IsFractionRing.injective A _)]
  refine ⟨(Scheme.range_fromSpecResidueField x).le.trans ?_, ?_⟩
  · rintro _ rfl
    exact ⟨_, (hx.eq h0).symm⟩
  · subst h1
    exact ⟨_, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField _ X m⟩

theorem exists_generic {K A κ : Type} [CommRing K] [CommRing A] [IsDomain A] [Algebra K A] [Field κ] [Algebra K κ]
    {X : Scheme.{0}} (s : X ⟶ Sp K) (j : Sp A ⟶ X) [IsOpenImmersion j] (hj : j ≫ s = spMap (algebraMap K A))
    (m : Sp κ ⟶ X) (hs : m ≫ s = spMap (algebraMap K κ)) (hr : Set.range m ⊆ Set.range j)
    (β : κ →+* FractionRing A) (hβ : spMap β ≫ m = spMap (algebraMap A (FractionRing A)) ≫ j) :
    ∃ f : A →ₐ[K] κ, spMap f.toRingHom ≫ j = m ∧ Function.Injective f ∧
      ∀ y : κ, ∃ a b : A, b ≠ 0 ∧ y * f b = f a := by
  obtain ⟨f, hf⟩ := exists_algHom_fac s j hj m hs hr
  have h2 : β.comp f.toRingHom = algebraMap A (FractionRing A) := by
    apply spMap_inj
    rw [← cancel_mono j, ← spMap_comp_ring, Category.assoc, hf, hβ]
  have h3 : ∀ a, β (f a) = algebraMap A (FractionRing A) a := fun a => DFunLike.congr_fun h2 a
  refine ⟨f, hf, fun a b hab => IsFractionRing.injective A (FractionRing A) (by rw [← h3, ← h3, hab]), fun y => ?_⟩
  obtain ⟨a, b, hb, e⟩ := IsFractionRing.div_surjective (A := A) (β y)
  refine ⟨a, b, nonZeroDivisors.ne_zero hb, β.injective ?_⟩
  rw [map_mul, h3, h3, ← e, div_mul_cancel₀ _ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb)]

theorem exists_poly_embed {K κ A V : Type} [Field K] [Field κ] [Algebra K κ] [CommRing A] [Algebra K A] [Finite V]
    (f : A →ₐ[K] κ) (hf : Function.Injective f) (hfr : ∀ y : κ, ∃ a b : A, b ≠ 0 ∧ y * f b = f a)
    (e : FractionRing (MvPolynomial V κ) ≃ₐ[κ] FractionRing (MvPolynomial V κ)) :
    ∃ θ : MvPolynomial V A →ₐ[K] FractionRing (MvPolynomial V κ), Function.Injective θ ∧
      (∀ a, θ (MvPolynomial.C a) = algebraMap κ _ (f a)) ∧
      (∀ v, θ (MvPolynomial.X v) = e (algebraMap (MvPolynomial V κ) _ (MvPolynomial.X v))) ∧
      ∀ x, ∃ a ∈ θ.range, ∃ b ∈ θ.range, b ≠ 0 ∧ x * b = a := by
  let θ₀ : MvPolynomial V A →ₐ[K] FractionRing (MvPolynomial V κ) :=
    (polyChartHom V f.range).comp (MvPolynomial.mapAlgHom f.rangeRestrict)
  have hs : Function.Surjective (MvPolynomial.mapAlgHom (σ := V) f.rangeRestrict) :=
    MvPolynomial.map_surjective _ f.rangeRestrict_surjective
  have hi : Function.Injective (MvPolynomial.mapAlgHom (σ := V) f.rangeRestrict) :=
    MvPolynomial.map_injective _ fun a b h => hf (congrArg Subtype.val h)
  refine ⟨(e.toAlgHom.restrictScalars K).comp θ₀, e.injective.comp ((polyChartHom_injective V _).comp hi),
    fun a => ?_, fun v => ?_, fun x => ?_⟩
  · show e (polyChartHom V f.range (MvPolynomial.map _ (MvPolynomial.C a))) = _
    rw [MvPolynomial.map_C, polyChartHom_C, e.commutes]
    rfl
  · show e (polyChartHom V f.range (MvPolynomial.map _ (MvPolynomial.X v))) = _
    rw [MvPolynomial.map_X, polyChartHom_X]
  · obtain ⟨_, ⟨p, rfl⟩, _, ⟨q, rfl⟩, hq, hx⟩ :=
      (polyChart_smooth_fraction_lift K κ V f.range _ (polyChartHom_range V f.range)).2.1 (fun y => by
        obtain ⟨a, b, hb, hy⟩ := hfr y
        exact ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, fun h0 => hb (hf (h0.trans (map_zero f).symm)), hy⟩) (e.symm x)
    obtain ⟨p, rfl⟩ := hs p
    obtain ⟨q, rfl⟩ := hs q
    refine ⟨_, ⟨p, rfl⟩, _, ⟨q, rfl⟩, fun h0 => hq (e.injective (h0.trans (map_zero e).symm)), ?_⟩
    have := congrArg e hx
    rw [map_mul, e.apply_symm_apply] at this
    exact this

section Cells

variable {T S : Type} [CommRing S] {r : T → ℕ}

noncomputable def cellM (σ : ∀ τ, Equiv.Perm (Fin (r τ)))
    (x : (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) → S) (τ : T) : Matrix (Fin (r τ)) (Fin (r τ)) S :=
  (lowM x τ).submatrix (σ τ).symm id

variable (σ : ∀ τ, Equiv.Perm (Fin (r τ))) (x : (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) → S)

theorem lowM_zero (τ : T) (i j : Fin (r τ)) (h : i < j) : lowM x τ i j = 0 := by
  simp [lowM, h.not_gt, h.ne']

theorem lowM_diag (τ : T) (i : Fin (r τ)) : lowM x τ i i = 1 := by
  simp [lowM]

theorem cellM_apply (τ : T) (i j : Fin (r τ)) : cellM σ x τ (σ τ i) j = lowM x τ i j := by
  simp [cellM]

theorem cellM_shape (τ : T) : (∀ i j : Fin (r τ), i < j → cellM σ x τ ((σ τ).toEmbedding i) j = 0) ∧
    ∀ i : Fin (r τ), cellM σ x τ ((σ τ).toEmbedding i) i = 1 :=
  ⟨fun i j h => (cellM_apply σ x τ i j).trans (lowM_zero x τ i j h),
    fun i => (cellM_apply σ x τ i i).trans (lowM_diag x τ i)⟩

theorem isUnit_det_cellM (τ : T) : IsUnit (cellM σ x τ).det := by
  rw [cellM, Matrix.det_permute, det_eq_one_of_lower_unitriangular _ (lowM_zero x τ) (lowM_diag x τ), _root_.mul_one]
  exact ((Equiv.Perm.sign (σ τ).symm).isUnit).map (Int.castRingHom S)

theorem cellM_map {S' F : Type} [CommRing S'] [FunLike F S S'] [RingHomClass F S S'] (φ : F) (τ : T) :
    (cellM σ x τ).map φ = cellM σ (fun v => φ (x v)) τ := by
  ext i j
  simp only [cellM, lowM, Matrix.map_apply, Matrix.submatrix_apply]
  split_ifs <;> simp

theorem cellM_unique (x' : (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) → S)
    (b : ∀ τ, Matrix (Fin (r τ)) (Fin (r τ)) S) (hb : ∀ τ, (b τ).BlockTriangular id ∧ ∀ i, IsUnit (b τ i i))
    (h : ∀ τ, cellM σ x τ * b τ = cellM σ x' τ) : x = x' := by
  funext ⟨τ, ⟨i, j⟩, hij⟩
  have e := ((cell_coordinates_exists_unique S _ _ (σ τ).toEmbedding (b τ)).2 _ _ (b τ) 1 (cellM_shape σ x τ)
    (cellM_shape σ x' τ) (hb τ).1 Matrix.blockTriangular_one (hb τ).2 (by rw [h, Matrix.mul_one])).1
  have e' := congrFun (congrFun e (σ τ j)) i
  rw [cellM_apply, cellM_apply] at e'
  have hij' : i < j := hij
  simpa [lowM, hij'] using e'

noncomputable def minor (g : ∀ τ, Matrix (Fin (r τ)) (Fin (r τ)) S) (k : Σ τ : T, Fin (r τ + 1)) : S :=
  ((g k.1).submatrix (fun i : Fin k.2 => (σ k.1).toEmbedding (Fin.castLE (Nat.lt_succ_iff.1 k.2.2) i))
    (Fin.castLE (Nat.lt_succ_iff.1 k.2.2))).det

theorem minor_map {S' F : Type} [CommRing S'] [FunLike F S S'] [RingHomClass F S S'] (φ : F)
    (g : ∀ τ, Matrix (Fin (r τ)) (Fin (r τ)) S) (k : Σ τ : T, Fin (r τ + 1)) :
    minor σ (fun τ => (g τ).map φ) k = φ (minor σ g k) :=
  ((φ : S →+* S').map_det _).symm

theorem minor_iff (g : ∀ τ, Matrix (Fin (r τ)) (Fin (r τ)) S) :
    (∀ k, IsUnit (minor σ g k)) ↔ ∃ (x : (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) → S)
      (b : ∀ τ, Matrix (Fin (r τ)) (Fin (r τ)) S), (∀ τ, (b τ).BlockTriangular id ∧ ∀ i, IsUnit (b τ i i)) ∧
      ∀ τ, g τ = cellM σ x τ * b τ := by
  constructor
  · intro h
    choose u b h0 h1 hb hu hg using fun τ => (cell_coordinates_exists_unique S _ _ (σ τ).toEmbedding (g τ)).1.1
      fun k hk => h ⟨τ, ⟨k, Nat.lt_succ_iff.2 hk⟩⟩
    refine ⟨fun v => u v.1 (σ v.1 v.2.1.2) v.2.1.1, b, fun τ => ⟨hb τ, hu τ⟩, fun τ => ?_⟩
    rw [hg τ]
    congr 1
    ext i j
    obtain ⟨i, rfl⟩ := (σ τ).surjective i
    rw [cellM_apply]
    rcases lt_trichotomy i j with hij | rfl | hij
    · rw [lowM_zero _ _ _ _ hij]; exact h0 τ i j hij
    · rw [lowM_diag]; exact h1 τ i
    · simp [lowM, hij]
  · rintro ⟨x, b, hb, hg⟩ ⟨τ, k⟩
    exact (cell_coordinates_exists_unique S _ _ (σ τ).toEmbedding (g τ)).1.2
      ⟨_, _, (cellM_shape σ x τ).1, (cellM_shape σ x τ).2, (hb τ).1, (hb τ).2, hg τ⟩ k _

end Cells

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem reframe_unique {S : Type} [CommRing S] [Algebra c.F S]
    {g g' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S} {y y' : FrPt Xo c S}
    (h : Reframe g y y') (h' : Reframe g' y y') (τ : E →+* ℂ) : g τ = g' τ := by
  ext j i
  exact congrFun ((y.basis τ (y'.u τ i) (h.1 ▸ y'.tan τ i) (y'.eig τ i)).unique (h.2 τ i) (h'.2 τ i)) j

theorem reframe_cancel {S : Type} [CommRing S] [Algebra c.F S]
    {g b : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S} {y y' y'' : FrPt Xo c S}
    (hg : ∀ τ, IsUnit (g τ).det) (h : Reframe g y y') (h' : Reframe (fun τ => g τ * b τ) y y'') :
    Reframe b y' y'' := by
  obtain ⟨b', ⟨_, hb'⟩, _⟩ := (GlobalTheory.T.isTriangularReframe_exists_and_unique E H Dw l Xo c S y').2 y'' (h'.1.trans h.1.symm)
  have e := reframe_unique ((GlobalTheory.T.triangularReframe_comp_baseChange_borel E H Dw l Xo c S).1 _ _ _ _ _ h hb') h'
  have : b' = b := funext fun τ => ((Matrix.isUnit_iff_isUnit_det _).2 (hg τ)).mul_left_cancel (e τ)
  exact this ▸ hb'

theorem algHom_eq_of_point {A S : Type} [CommRing A] [Algebra c.F A] [CommRing S] [Algebra c.F S]
    (j : Sp A ⟶ Xo.XF c) [IsOpenImmersion j] (hj : j ≫ pullback.snd _ _ = spMap (algebraMap c.F A))
    (f f' : A →ₐ[c.F] S)
    (h : spMap f.toRingHom ≫ j ≫ pullback.fst _ _ = spMap f'.toRingHom ≫ j ≫ pullback.fst _ _) : f = f' := by
  apply AlgHom.coe_ringHom_injective
  apply spMap_inj
  rw [← cancel_mono j]
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc]
    exact h
  · rw [Category.assoc, Category.assoc, hj, spMap_comp_ring, spMap_comp_ring, f.comp_algebraMap, f'.comp_algebraMap]

section Poly

variable (bc : FrBC Xo c) {A : Type} [CommRing A] [Algebra c.F A] {yA : FrPt Xo c A}
  (σ : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) {R : Type} [CommRing R] [Algebra c.F R]
  (q : MvPolynomial (FlagVar Dw) A ≃ₐ[c.F] R) {y₀ y : FrPt Xo c R}

noncomputable def cst : A →ₐ[c.F] R :=
  q.toAlgHom.comp (IsScalarTower.toAlgHom c.F A (MvPolynomial (FlagVar Dw) A))

theorem reframe_pt (h₀ : FrMap (cst q) yA y₀) (hy : Reframe (cellM σ fun v => q (MvPolynomial.X v)) y₀ y)
    {S : Type} [CommRing S] [Algebra c.F S] {ψ : R →ₐ[c.F] S} {z₀ z : FrPt Xo c S}
    (hz₀ : FrMap (ψ.comp (cst q)) yA z₀) (hz : FrMap ψ y z) :
    Reframe (cellM σ fun v => ψ (q (MvPolynomial.X v))) z₀ z := by
  have := (GlobalTheory.T.triangularReframe_comp_baseChange_borel E H Dw l Xo c R).2.1 S ψ _ _ _ _ _ hy (frMap_cancel _ _ _ _ _ _ _ _ h₀ hz₀) hz
  simpa only [cellM_map] using this

include bc in
theorem catches (h₀ : FrMap (cst q) yA y₀) (hy : Reframe (cellM σ fun v => q (MvPolynomial.X v)) y₀ y)
    {S : Type} [CommRing S] [Algebra c.F S] (f : A →ₐ[c.F] S) (z₀ w : FrPt Xo c S) (x : FlagVar Dw → S)
    (b : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (hz₀ : FrMap f yA z₀)
    (hb : ∀ τ, (b τ).BlockTriangular id ∧ ∀ i, IsUnit (b τ i i)) (hw : Reframe (fun τ => cellM σ x τ * b τ) z₀ w) :
    ∃ (ψ : R →ₐ[c.F] S) (z : FrPt Xo c S) (t' : Ix Dw → Sˣ), FrMap ψ y z ∧ FrBor t' z w := by
  let ψ : R →ₐ[c.F] S := (MvPolynomial.aevalTower f x).comp q.symm.toAlgHom
  have h1 : ψ.comp (cst q) = f := by
    ext a
    simp [ψ, cst]
  have h2 : (fun v => ψ (q (MvPolynomial.X v))) = x := by
    funext v
    simp [ψ]
  obtain ⟨z, hz⟩ := bc _ _ ψ y
  have h3 := reframe_pt σ q h₀ hy (h1 ▸ hz₀) hz
  rw [h2] at h3
  obtain ⟨t, ht⟩ := ((GlobalTheory.T.triangularReframe_comp_baseChange_borel E H Dw l Xo c S).2.2 z w).2 ⟨b, hb, reframe_cancel (isUnit_det_cellM σ x) h3 hw⟩
  exact ⟨ψ, z, t, hz, ht⟩

variable {j : Sp A ⟶ Xo.XF c} [IsOpenImmersion j] (hj : j ≫ pullback.snd _ _ = spMap (algebraMap c.F A))
  (hA : yA.x = j ≫ pullback.fst _ _)

include hA in
theorem point_eq (h₀ : FrMap (cst q) yA y₀) (hy : Reframe (cellM σ fun v => q (MvPolynomial.X v)) y₀ y)
    {S : Type} [CommRing S] [Algebra c.F S] {ψ : R →ₐ[c.F] S} {z : FrPt Xo c S} (hz : FrMap ψ y z) :
    z.x = spMap (ψ.comp (cst q)).toRingHom ≫ j ≫ pullback.fst _ _ := by
  rw [hz.1, hy.1, h₀.1, hA, spMap_algHom_comp, Category.assoc]

include bc hj hA in
theorem mono_chart (h₀ : FrMap (cst q) yA y₀) (hy : Reframe (cellM σ fun v => q (MvPolynomial.X v)) y₀ y)
    {S : Type} [CommRing S] [Algebra c.F S] (ψ ψ' : R →ₐ[c.F] S) (z z' : FrPt Xo c S) (t : Ix Dw → Sˣ)
    (hz : FrMap ψ y z) (hz' : FrMap ψ' y z') (ht : FrBor t z z') : ψ = ψ' := by
  have h1 : ψ.comp (cst q) = ψ'.comp (cst q) :=
    algHom_eq_of_point j hj _ _ (by rw [← point_eq σ q hA h₀ hy hz, ← point_eq σ q hA h₀ hy hz', ht.1])
  obtain ⟨z₀, hz₀⟩ := bc _ _ (ψ.comp (cst q)) yA
  obtain ⟨b, hb, hbz⟩ := ((GlobalTheory.T.triangularReframe_comp_baseChange_borel E H Dw l Xo c S).2.2 z z').1 ⟨t, ht⟩
  have h2 := cellM_unique σ _ _ b hb (reframe_unique
    ((GlobalTheory.T.triangularReframe_comp_baseChange_borel E H Dw l Xo c S).1 _ _ _ _ _ (reframe_pt σ q h₀ hy hz₀ hz) hbz)
    (reframe_pt σ q h₀ hy (h1 ▸ hz₀) hz'))
  have h3 : ψ.comp q.toAlgHom = ψ'.comp q.toAlgHom :=
    MvPolynomial.algHom_ext' h1 fun v => congrFun h2 v
  ext a
  obtain ⟨p, rfl⟩ := q.surjective a
  exact DFunLike.congr_fun h3 p

include bc hj hA in
theorem open_chart (h₀ : FrMap (cst q) yA y₀) (hy : Reframe (cellM σ fun v => q (MvPolynomial.X v)) y₀ y)
    (S L : Type) [CommRing S] [Algebra c.F S] [Field L] [Algebra c.F L] (χ : S →ₐ[c.F] L) (w : FrPt Xo c S)
    (wL : FrPt Xo c L) (hw : FrMap χ w wL)
    (hc : ∃ (ψ : R →ₐ[c.F] L) (z : FrPt Xo c L) (t' : Ix Dw → Lˣ), FrMap ψ y z ∧ FrBor t' z wL) :
    ∃ g : S, χ g ≠ 0 ∧ ∀ (S' : Type) [CommRing S'] [Algebra c.F S'] (lam : S →ₐ[c.F] S'), IsUnit (lam g) →
      ∀ w' : FrPt Xo c S', FrMap lam w w' →
        ∃ (ψ : R →ₐ[c.F] S') (z : FrPt Xo c S') (t' : Ix Dw → S'ˣ), FrMap ψ y z ∧ FrBor t' z w' := by
  obtain ⟨ψ, z, t, hz, ht⟩ := hc
  let W : Sp S ⟶ Xo.XF c := pullback.lift w.x (spMap (algebraMap c.F S)) (by
    rw [w.x_over, spMap_comp_ring]; rfl)
  have hW1 : W ≫ pullback.fst _ _ = w.x := pullback.lift_fst _ _ _
  have hW2 : W ≫ pullback.snd _ _ = spMap (algebraMap c.F S) := pullback.lift_snd _ _ _
  have hL : wL.x = spMap (ψ.comp (cst q)).toRingHom ≫ j ≫ pullback.fst _ _ := by
    rw [ht.1, point_eq σ q hA h₀ hy hz]
  obtain ⟨g₁, hg₁, f₁, hf₁⟩ := exists_away_fac (pullback.snd _ _) j hj W hW2 χ.toRingHom (ψ.comp (cst q)).toRingHom (by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hW1, ← hL, hw.1]
    · rw [Category.assoc, Category.assoc, hW2, hj, spMap_comp_ring, spMap_comp_ring]
      exact congrArg spMap (χ.comp_algebraMap.trans (ψ.comp (cst q)).comp_algebraMap.symm))
  let S₁ := Localization.Away g₁
  let i₁ : S →ₐ[c.F] S₁ := IsScalarTower.toAlgHom c.F S S₁
  have ext : ∀ (S' : Type) [CommRing S'] [Algebra c.F S'] (lam : S →ₐ[c.F] S'), IsUnit (lam g₁) →
      ∃ ν : S₁ →ₐ[c.F] S', ν.comp i₁ = lam := fun S' _ _ lam hu =>
    ⟨IsLocalization.liftAlgHom (M := Submonoid.powers g₁) (f := lam) (by
      rintro ⟨_, n, rfl⟩
      simpa using hu.pow n), by ext a; simp [i₁]⟩
  obtain ⟨w₁, hw₁⟩ := bc _ _ i₁ w
  obtain ⟨z₁, hz₁⟩ := bc _ _ f₁ yA
  have hx₁ : w₁.x = z₁.x := by
    rw [hw₁.1, hz₁.1, hA, ← Category.assoc, hf₁, Category.assoc, hW1]; rfl
  obtain ⟨G, ⟨_, hG⟩, _⟩ := (GlobalTheory.T.isTriangularReframe_exists_and_unique E H Dw l Xo c S₁ z₁).2 w₁ hx₁
  have base : ∀ (S' : Type) [CommRing S'] [Algebra c.F S'] (ν : S₁ →ₐ[c.F] S') (z' w' : FrPt Xo c S'),
      FrMap (ν.comp f₁) yA z' → FrMap (ν.comp i₁) w w' → Reframe (fun τ => (G τ).map ν) z' w' :=
    fun S' _ _ ν z' w' h1 h2 => (GlobalTheory.T.triangularReframe_comp_baseChange_borel E H Dw l Xo c S₁).2.1 S' ν _ _ _ _ _ hG
      (frMap_cancel _ _ _ _ _ _ _ _ hz₁ h1) (frMap_cancel _ _ _ _ _ _ _ _ hw₁ h2)
  obtain ⟨χ₁, hχ₁⟩ := ext L χ (IsUnit.mk0 _ hg₁)
  obtain ⟨z₀, hz₀⟩ := bc _ _ (χ₁.comp f₁) yA
  have hGL := base L χ₁ z₀ wL hz₀ (hχ₁ ▸ hw)
  have he : χ₁.comp f₁ = ψ.comp (cst q) :=
    algHom_eq_of_point j hj _ _ (by rw [← hL, hGL.1, hz₀.1, hA])
  obtain ⟨b, hb, hbz⟩ := ((GlobalTheory.T.triangularReframe_comp_baseChange_borel E H Dw l Xo c L).2.2 z wL).1 ⟨t, ht⟩
  have hmin := (minor_iff σ _).2 ⟨_, b, hb, reframe_unique hGL
    ((GlobalTheory.T.triangularReframe_comp_baseChange_borel E H Dw l Xo c L).1 _ _ _ _ _ (reframe_pt σ q h₀ hy (he ▸ hz₀) hz) hbz)⟩
  obtain ⟨n, g₂, hg₂⟩ := IsLocalization.Away.surj g₁ (∏ k, minor σ G k)
  have hval : ∀ (S' : Type) [CommRing S'] [Algebra c.F S'] (ν : S₁ →ₐ[c.F] S'),
      (ν.comp i₁) g₂ = (∏ k, minor σ (fun τ => (G τ).map ν) k) * (ν.comp i₁) g₁ ^ n := by
    intro S' _ _ ν
    have := congrArg ν hg₂
    rw [map_mul, map_prod, map_pow] at this
    simp only [minor_map]
    exact this.symm
  refine ⟨g₁ * g₂, ?_, fun S' _ _ lam hu w' hw' => ?_⟩
  · rw [map_mul]
    refine mul_ne_zero hg₁ ?_
    rw [← hχ₁, hval, hχ₁]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => (hmin k).ne_zero) (pow_ne_zero _ hg₁)
  · rw [map_mul] at hu
    obtain ⟨ν, hν⟩ := ext S' lam (isUnit_of_mul_isUnit_left hu)
    have hu2 := isUnit_of_mul_isUnit_right hu
    rw [← hν, hval] at hu2
    obtain ⟨x, b', hb', hx⟩ := (minor_iff σ (fun τ => (G τ).map ν)).1 fun k =>
      IsUnit.prod_iff.1 (isUnit_of_mul_isUnit_left hu2) k (Finset.mem_univ _)
    obtain ⟨z', hz'⟩ := bc _ _ (ν.comp f₁) yA
    have hr := base S' ν z' w' hz' (hν ▸ hw')
    rw [funext hx] at hr
    exact catches bc σ q h₀ hy _ z' w' x b' hz' hb' hr

end Poly

end GlobalTheory.Reg.CellChart

namespace GlobalTheory.Reg


open CellChart in
attribute [local instance 1100] Subalgebra.algebra in
attribute [local instance 100] IntermediateField.instAlgebraSubtypeMem in
theorem exists_fChart_cell : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), FrBC Xo c → ∀ (h : GenFrEx Xo c) (A : Type) [CommRing A] [IsDomain A] [Algebra c.F A] (j : Sp A ⟶ Xo.XF c) (yA : FrPt Xo c A), IsOpenImmersion j → j ≫ pullback.snd _ _ = spMap (algebraMap c.F A) → Algebra.Smooth c.F A → yA.x = j ≫ pullback.fst _ _ → ∀ σ : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ)), ∃ C : FChart h, ∀ (L : Type) [Field L] [Algebra c.F L] (f : A →ₐ[c.F] L) (z₀ y : FrPt Xo c L) (x : FlagVar Dw → L) (b : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) L), FrMap f yA z₀ → (∀ τ, (b τ).BlockTriangular id ∧ ∀ i, b τ i i ≠ 0) → Reframe (fun τ => (lowM x τ).submatrix (σ τ).symm id * b τ) z₀ y → ∃ (ψ : C.R →ₐ[c.F] L) (z : FrPt Xo c L) (t' : Ix Dw → Lˣ), FrMap ψ C.y z ∧ FrBor t' z y := by
  intro E _ _ _ H Dw l Xo c bc h A _ _ _ j yA hjo hj hsm hA σ
  let Z : Comp Xo c := ⟨_, closure_range_mem j⟩
  obtain ⟨hr, β, hβ⟩ := exists_residue_embed j (genPt Z)
    ((Z.2.1 : IsIrreducible (Z : Set (Xo.XF c))).isGenericPoint_genericPoint isClosed_closure)
  obtain ⟨f, hf, hfi, hfr⟩ := exists_generic (K := c.F) (κ := kap Z) (pullback.snd _ _) j hj (genSp Z)
    (Spec.map_preimage (genSp Z ≫ strK)).symm hr β.hom hβ
  haveI : Infinite (kap Z) := Infinite.of_injective _ (algebraMap c.F (kap Z)).injective
  obtain ⟨hgx, y₀, hy₀, hgu⟩ := isGenFr_genFr h Z
  obtain ⟨zκ, hzκ⟩ := bc _ _ f yA
  obtain ⟨G, ⟨hGu, hG⟩, _⟩ := (GlobalTheory.T.isTriangularReframe_exists_and_unique E H Dw l Xo c _ zκ).2 y₀ (by
    rw [hy₀, hzκ.1, hA, ← Category.assoc, hf]; rfl)
  obtain ⟨e, b, hb, he⟩ := GlobalTheory.T.exists_flagCoordinates_cellChange_birational (kap Z) (E →+* ℂ) Dw.mult G σ hGu
  obtain ⟨θ, hθ, hθC, hθX, hθf⟩ := exists_poly_embed (V := FlagVar Dw) f hfi hfr e
  let q : MvPolynomial (FlagVar Dw) A ≃ₐ[c.F] θ.range := AlgEquiv.ofInjective θ hθ
  obtain ⟨u₀, hu₀⟩ := bc _ _ (cst q) yA
  obtain ⟨u, hu⟩ := (GlobalTheory.T.isTriangularReframe_exists_and_unique E H Dw l Xo c _ u₀).1 _ (isUnit_det_cellM σ fun v => q (MvPolynomial.X v))
  obtain ⟨yg, hyg⟩ := bc _ _ θ.range.val u
  let k : kap Z →ₐ[c.F] Om Z := IsScalarTower.toAlgHom c.F (kap Z) (Om Z)
  obtain ⟨zΩ, hzΩ⟩ := bc _ _ k zκ
  obtain ⟨yΩ, hyΩ⟩ := bc _ _ k y₀
  have h1 := (GlobalTheory.T.triangularReframe_comp_baseChange_borel E H Dw l Xo c _).2.1 _ k _ _ _ _ _ hG hzΩ hyΩ
  have hx : (genFr h Z).x = yΩ.x := by rw [hgx, hyΩ.1, hy₀]; rfl
  have h2 : Reframe (lowM fun v => algebraMap (MvPolynomial (FlagVar Dw) (kap Z)) (Om Z) (MvPolynomial.X v)) yΩ
      (genFr h Z) := by
    refine ⟨hx, fun τ i => ?_⟩
    have := hgu τ i
    rw [hx] at this
    rw [funext (hyΩ.2.1 τ)]
    exact this
  have h3 := (GlobalTheory.T.triangularReframe_comp_baseChange_borel E H Dw l Xo c _).1 _ _ _ _ _ h1 h2
  have hc : θ.range.val.comp (cst q) = k.comp f := AlgHom.ext hθC
  have h4 := reframe_pt σ q hu₀ hu (hc ▸ frMap_trans _ _ _ _ _ _ _ _ hzκ hzΩ) hyg
  have hX : (fun v => θ.range.val (q (MvPolynomial.X v))) =
      fun v => e (algebraMap (MvPolynomial (FlagVar Dw) (kap Z)) (Om Z) (MvPolynomial.X v)) := funext hθX
  rw [hX] at h4
  have h5 : Reframe b yg (genFr h Z) := reframe_cancel (isUnit_det_cellM σ _) h4 (by
    have := funext he
    exact this ▸ h3)
  obtain ⟨t, ht⟩ := ((GlobalTheory.T.triangularReframe_comp_baseChange_borel E H Dw l Xo c _).2.2 _ _).2
    ⟨b, fun τ => ⟨(hb τ).1, fun i => IsUnit.mk0 _ ((hb τ).2 i)⟩, h5⟩
  have hsm' : Algebra.Smooth c.F θ.range := by
    have : Algebra.Smooth A (MvPolynomial (FlagVar Dw) A) := ⟨inferInstance, inferInstance⟩
    have : Algebra.Smooth c.F (MvPolynomial (FlagVar Dw) A) := Algebra.Smooth.comp c.F A _
    exact Algebra.Smooth.of_equiv q
  refine ⟨⟨Z, θ.range, hsm', hθf, u, yg, t⁻¹, hyg, (GlobalTheory.T.frameBorel_groupoid_properties E H Dw l Xo c _).2.2.1 _ _ _ ht,
    fun L _ _ => mono_chart bc σ q hj hA hu₀ hu, open_chart bc σ q hj hA hu₀ hu⟩, ?_⟩
  intro L _ _ f' z₀ y x b' hz₀ hb' hr
  exact catches bc σ q hu₀ hu f' z₀ y x b' hz₀ (fun τ => ⟨(hb' τ).1, fun i => IsUnit.mk0 _ ((hb' τ).2 i)⟩) hr

end GlobalTheory.Reg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFlagCellChartOverFramedAffineOpenStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
attribute [local instance 1100] Subalgebra.algebra in
attribute [local instance 100] IntermediateField.instAlgebraSubtypeMem in
theorem _root_.GlobalTheory.T.exists_flagCellChart_over_framedAffineOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), FrBC Xo c → ∀ (h : GenFrEx Xo c) (A : Type) [CommRing A] [IsDomain A] [Algebra c.F A] (j : Sp A ⟶ Xo.XF c) (yA : FrPt Xo c A), IsOpenImmersion j → j ≫ pullback.snd _ _ = spMap (algebraMap c.F A) → Algebra.Smooth c.F A → yA.x = j ≫ pullback.fst _ _ → ∀ σ : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ)), ∃ C : FChart h, ∀ (L : Type) [Field L] [Algebra c.F L] (f : A →ₐ[c.F] L) (z₀ y : FrPt Xo c L) (x : FlagVar Dw → L) (b : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) L), FrMap f yA z₀ → (∀ τ, (b τ).BlockTriangular id ∧ ∀ i, b τ i i ≠ 0) → Reframe (fun τ => (lowM x τ).submatrix (σ τ).symm id * b τ) z₀ y → ∃ (ψ : C.R →ₐ[c.F] L) (z : FrPt Xo c L) (t' : Ix Dw → Lˣ), FrMap ψ C.y z ∧ FrBor t' z y := by
  first | exact @GlobalTheory.Reg.exists_fChart_cell | exact GlobalTheory.Reg.exists_fChart_cell | (intros; apply GlobalTheory.Reg.exists_fChart_cell <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.FlagChartsCoverFramedFieldPoints
noncomputable section

namespace GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem exists_perm_lower_upper {L : Type} [Field L] {n : ℕ} (g : Matrix (Fin n) (Fin n) L) (hg : IsUnit g.det) :
    ∃ (σ : Equiv.Perm (Fin n)) (u b : Matrix (Fin n) (Fin n) L),
      (∀ i j : Fin n, i < j → u (σ i) j = 0) ∧ (∀ i, u (σ i) i = 1) ∧
      (b.BlockTriangular id ∧ ∀ i, b i i ≠ 0) ∧ g = u * b := by
  have hli : LinearIndependent L g.transpose :=
    Matrix.linearIndependent_cols_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det g).mpr hg)
  obtain ⟨m, u, b, -, h0, h1, hb, hd, e⟩ := GlobalTheory.exists_integral_pivot_decomposition L ⊤ n n g hli
  exact ⟨Equiv.ofBijective m (Finite.injective_iff_bijective.mp m.injective), u, b, h0, h1, ⟨hb, hd⟩, e⟩

theorem exists_algHom_of_mem_range {K A L : Type} [Field K] [CommRing A] [Algebra K A] [Field L] [Algebra K L]
    {X : Scheme.{0}} (s : X ⟶ Sp K) (j : Sp A ⟶ X) [IsOpenImmersion j] (hj : j ≫ s = spMap (algebraMap K A))
    (q : Sp L ⟶ X) (hq : q ≫ s = spMap (algebraMap K L))
    (hp : q (IsLocalRing.closedPoint L) ∈ Set.range j) :
    ∃ f : A →ₐ[K] L, spMap f.toRingHom ≫ j = q := by
  have hr : Set.range q ⊆ Set.range j := by
    rintro _ ⟨a, rfl⟩
    have : a = IsLocalRing.closedPoint L := Subsingleton.elim (α := PrimeSpectrum L) _ _
    rw [this]
    exact hp
  let φ : CommRingCat.of A ⟶ CommRingCat.of L := Spec.preimage (IsOpenImmersion.lift j q hr)
  have hφ : Spec.map φ ≫ j = q := by
    rw [Spec.map_preimage, IsOpenImmersion.lift_fac]
  have hc : CommRingCat.ofHom (algebraMap K A) ≫ φ = CommRingCat.ofHom (algebraMap K L) := by
    apply Spec.map_injective
    rw [Spec.map_comp]
    show Spec.map φ ≫ spMap (algebraMap K A) = spMap (algebraMap K L)
    rw [← hj, ← Category.assoc, hφ, hq]
  exact ⟨{ φ.hom with commutes' := fun a => congrArg (fun t => t.hom a) hc }, hφ⟩

theorem atlas : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), FrBC Xo c → ∀ h : GenFrEx Xo c, Atlas h := by
  intro hS E _ _ _ H Dw l Xo c hBC h L _ _ y
  have hcond : y.x ≫ Xo.s =
      spMap (algebraMap c.F L) ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [y.x_over, spMap_comp_ring]
    rfl
  let q : Sp L ⟶ Xo.XF c := pullback.lift y.x (spMap (algebraMap c.F L)) hcond
  obtain ⟨A, _, _, _, j, yA, hj, hp, hjs, hsm, hyA⟩ :=
    GlobalTheory.T.exists_integral_smooth_chart_frame_moduli hS E H Dw l Xo c (q (IsLocalRing.closedPoint L))
  obtain ⟨f, hf⟩ := exists_algHom_of_mem_range (pullback.snd _ _) j hjs q (pullback.lift_snd _ _ _) hp
  obtain ⟨z₀, hz₀⟩ := hBC A L f yA
  have hx : y.x = z₀.x := by
    rw [hz₀.1, hyA, ← Category.assoc, hf]
    exact (pullback.lift_fst _ _ _).symm
  obtain ⟨g, ⟨hgu, hg⟩, -⟩ := (GlobalTheory.T.isTriangularReframe_exists_and_unique E H Dw l Xo c L z₀).2 y hx
  choose σ u b h0 h1 hb e using fun τ => exists_perm_lower_upper (g τ) (hgu τ)
  obtain ⟨C, hC⟩ := GlobalTheory.T.exists_flagCellChart_over_framedAffineOpen E H Dw l Xo c hBC h A j yA hj hjs hsm hyA σ
  let x : FlagVar Dw → L := fun v => u v.1 (σ v.1 v.2.1.2) v.2.1.1
  have hu : ∀ τ, (lowM x τ).submatrix (σ τ).symm id = u τ := by
    intro τ
    ext i k
    obtain ⟨i, rfl⟩ := (σ τ).surjective i
    simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply, id, lowM]
    split_ifs with h₁ h₂
    · rfl
    · rw [h₂, h1]
    · exact (h0 τ i k (lt_of_le_of_ne (not_lt.mp h₁) (Ne.symm h₂))).symm
  refine ⟨C, hC L f z₀ y x b hz₀ hb ?_⟩
  have : (fun τ => (lowM x τ).submatrix (σ τ).symm id * b τ) = g := funext fun τ => by rw [hu τ, ← e τ]
  rw [this]
  exact hg

end GlobalTheory.Reg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.FlagChartsCoverFramedFieldPointsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagCharts_cover_framed_fieldPoints : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), FrBC Xo c → ∀ h : GenFrEx Xo c, Atlas h := by
  first | exact @GlobalTheory.Reg.atlas | exact GlobalTheory.Reg.atlas | (intros; apply GlobalTheory.Reg.atlas <;> assumption)
end
