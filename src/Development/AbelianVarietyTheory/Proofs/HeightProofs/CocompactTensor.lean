module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsNhdsZeroPrincipalEqZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdelicMatrixLattice

section Tensor

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

theorem exists_coords : ∃ (n : ℕ) (e : R ⊗[F] E ≃ₜ (Fin n → R)) (b : E ≃ₗ[F] (Fin n → F)),
    (∀ x y, e (x + y) = e x + e y) ∧ ∀ x i, e (inclR R x) i = algebraMap F R (b x i) := by
  have : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  let e := (Algebra.TensorProduct.basis R (Module.finBasis F E)).equivFun
  refine ⟨Module.finrank F E, { e.toEquiv with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap },
    (Module.finBasis F E).equivFun, fun x y => e.map_add x y, fun x i => ?_⟩
  change (Algebra.TensorProduct.basis R (Module.finBasis F E)).repr ((1 : R) ⊗ₜ[F] x) i = _
  rw [Algebra.TensorProduct.basis_repr_tmul]
  simp

theorem discrete_tensor (h : ∃ U ∈ nhds (0 : R), ∀ x : F, algebraMap F R x ∈ U → x = 0) :
    ∃ U ∈ nhds (0 : R ⊗[F] E), ∀ x : E, inclR R x ∈ U → x = 0 := by
  obtain ⟨U, hU, hx⟩ := h
  obtain ⟨n, e, b, hadd, hb⟩ := exists_coords (F := F) (E := E) R
  have h0 : e 0 = 0 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_add.1 this
  refine ⟨e ⁻¹' (Set.univ.pi fun _ => U), ?_, fun x hxU => ?_⟩
  · refine e.continuous.continuousAt.preimage_mem_nhds ?_
    rw [h0]
    exact set_pi_mem_nhds Set.finite_univ fun _ _ => hU
  · refine b.injective ?_
    rw [map_zero]
    funext i
    refine hx _ ?_
    rw [← hb]
    exact hxU i (Set.mem_univ i)

theorem cocompact_tensor
    (h : ∃ K : Set R, IsCompact K ∧ ∀ a : R, ∃ x : F, a - algebraMap F R x ∈ K) :
    ∃ K : Set (R ⊗[F] E), IsCompact K ∧ ∀ a : R ⊗[F] E, ∃ x : E, inclR R x + a ∈ K := by
  obtain ⟨K, hK, hx⟩ := h
  obtain ⟨n, e, b, hadd, hb⟩ := exists_coords (F := F) (E := E) R
  refine ⟨e ⁻¹' (Set.univ.pi fun _ => K), e.isCompact_preimage.2 (isCompact_univ_pi fun _ => hK),
    fun a => ?_⟩
  choose c hc using hx
  refine ⟨b.symm fun i => - c (e a i), fun i _ => ?_⟩
  rw [hadd, Pi.add_apply, hb, b.apply_symm_apply, map_neg, neg_add_eq_sub]
  exact hc _

end Tensor

theorem lattice : ∀ (D : D7) (V W : HSp D), IsTopologicalAddGroup (WA V W) ∧ LocallyCompactSpace (WA V W) ∧ SecondCountableTopology (WA V W) ∧ T2Space (WA V W) ∧ DiscreteTopology (ratL V W) ∧ ∃ K : Set (WA V W), IsCompact K ∧ ∀ x : WA V W, ∃ γ ∈ ratL V W, γ + x ∈ K := by
  intro D V W
  have : LocallyCompactSpace (AF D.host.F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele _
  have : SecondCountableTopology (AF D.host.F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele _
  have : T2Space (AF D.host.F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField _
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E)
    (AF D.host.F)
  have : LocallyCompactSpace (AE D) := e.isClosedEmbedding.locallyCompactSpace
  have : SecondCountableTopology (AE D) := e.secondCountableTopology
  have : T2Space (AE D) := e.isEmbedding.t2Space
  have hg : IsTopologicalAddGroup (WA V W) :=
    inferInstanceAs (IsTopologicalAddGroup (Fin V.rank → Fin W.rank → AE D))
  refine ⟨hg, inferInstanceAs (LocallyCompactSpace (Fin V.rank → Fin W.rank → AE D)),
    inferInstanceAs (SecondCountableTopology (Fin V.rank → Fin W.rank → AE D)),
    inferInstanceAs (T2Space (Fin V.rank → Fin W.rank → AE D)), ?_, ?_⟩
  · obtain ⟨U, hU, hx⟩ := discrete_tensor (F := D.host.F) (E := D.host.E) (AF D.host.F)
      (GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero D.host.F)
    have hN : (Set.univ.pi fun _ : Fin V.rank => Set.univ.pi fun _ : Fin W.rank => U) ∈
        nhds (0 : WA V W) :=
      set_pi_mem_nhds Set.finite_univ fun _ _ => set_pi_mem_nhds Set.finite_univ fun _ _ => hU
    refine discreteTopology_of_isOpen_singleton_zero ?_
    rw [isOpen_singleton_iff_nhds_eq_pure]
    refine le_antisymm (Filter.le_pure_iff.2 ?_) (pure_le_nhds _)
    have hc : ContinuousAt (fun x : ratL V W => (x : WA V W)) 0 :=
      continuous_subtype_val.continuousAt
    refine Filter.mem_of_superset (hc.preimage_mem_nhds hN) ?_
    rintro ⟨_, y, rfl⟩ hy
    have hy0 : y = 0 := by
      funext i j
      exact hx _ (hy i (Set.mem_univ i) j (Set.mem_univ j))
    subst hy0
    exact Subtype.ext (map_zero _)
  · obtain ⟨K, hK, hx⟩ := cocompact_tensor (F := D.host.F) (E := D.host.E) (AF D.host.F)
      (GlobalTheory.AdeleCocompact.exists_compact_adele D.host.F)
    choose c hc using hx
    refine ⟨Set.univ.pi fun _ : Fin V.rank => Set.univ.pi fun _ : Fin W.rank => K,
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK, fun x => ?_⟩
    exact ⟨_, ⟨Matrix.of fun i j => c (x i j), rfl⟩, fun i _ j _ => hc (x i j)⟩

end GlobalTheory.AdelicMatrixLattice
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryLieGeneratorsRep
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryLieGeneratorsRep
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.UnitaryLieComplexification

open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies

variable {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ}

noncomputable def cj (J Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := -(J⁻¹ * Zᴴ * J)

theorem cj_add (Z W : Matrix (Fin n) (Fin n) ℂ) : cj J (Z + W) = cj J Z + cj J W := by
  simp only [cj, conjTranspose_add, mul_add, add_mul, neg_add]

theorem cj_sub (Z W : Matrix (Fin n) (Fin n) ℂ) : cj J (Z - W) = cj J Z - cj J W := by
  simp only [cj, conjTranspose_sub, mul_sub, sub_mul]
  abel

theorem cj_smul (c : ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) : cj J (c • Z) = star c • cj J Z := by
  simp only [cj, conjTranspose_smul, mul_smul_comm, smul_mul_assoc, smul_neg]

theorem cj_cj (hJ : Jᴴ = J) (hu : IsUnit J.det) (Z : Matrix (Fin n) (Fin n) ℂ) : cj J (cj J Z) = Z := by
  simp only [cj, conjTranspose_neg, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, hJ,
    mul_neg, neg_mul, neg_neg, Matrix.mul_assoc, Matrix.nonsing_inv_mul J hu, Matrix.mul_one]
  rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul J hu, Matrix.one_mul]

theorem mem_iff_cj (hu : IsUnit J.det) (X : Matrix (Fin n) (Fin n) ℂ) : X ∈ lieU J ↔ cj J X = X := by
  change Xᴴ * J + J * X = 0 ↔ _
  constructor
  · intro h
    rw [cj, Matrix.mul_assoc, eq_neg_of_add_eq_zero_left h, mul_neg, neg_neg, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul J hu, Matrix.one_mul]
  · intro h
    have : J * X = -(Xᴴ * J) := by
      conv_lhs => rw [← h]
      rw [cj, mul_neg, Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv J hu, Matrix.one_mul]
    rw [this, add_neg_cancel]

noncomputable def rePart (hJ : Jᴴ = J) (hu : IsUnit J.det) (Z : Matrix (Fin n) (Fin n) ℂ) : lieU J :=
  ⟨(1 / 2 : ℂ) • (Z + cj J Z), by
    rw [mem_iff_cj hu, cj_smul, cj_add, cj_cj hJ hu, add_comm]
    simp⟩

noncomputable def imPart (hJ : Jᴴ = J) (hu : IsUnit J.det) (Z : Matrix (Fin n) (Fin n) ℂ) : lieU J :=
  ⟨(1 / (2 * Complex.I) : ℂ) • (Z - cj J Z), by
    rw [mem_iff_cj hu, cj_smul, cj_sub, cj_cj hJ hu, ← neg_sub Z, smul_neg, ← neg_smul]
    congr 1
    simp⟩

theorem re_add_im (hJ : Jᴴ = J) (hu : IsUnit J.det) (Z : Matrix (Fin n) (Fin n) ℂ) :
    (rePart hJ hu Z).1 + Complex.I • (imPart hJ hu Z).1 = Z := by
  have h : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by field_simp
  simp only [rePart, imPart, smul_smul, h]
  module

theorem cj_mk (hu : IsUnit J.det) (X Y : lieU J) :
    cj J (X.1 + Complex.I • Y.1) = X.1 - Complex.I • Y.1 := by
  rw [cj_add, cj_smul, (mem_iff_cj hu _).1 X.2, (mem_iff_cj hu _).1 Y.2]
  simp [sub_eq_add_neg]

theorem rePart_mk (hJ : Jᴴ = J) (hu : IsUnit J.det) (X Y : lieU J) :
    rePart hJ hu (X.1 + Complex.I • Y.1) = X := by
  apply Subtype.ext
  simp only [rePart, cj_mk hu]
  module

theorem imPart_mk (hJ : Jᴴ = J) (hu : IsUnit J.det) (X Y : lieU J) :
    imPart hJ hu (X.1 + Complex.I • Y.1) = Y := by
  apply Subtype.ext
  simp only [imPart, cj_mk hu]
  have h : (1 / (2 * Complex.I)) * (2 * Complex.I) = 1 := by field_simp
  have h2 : X.1 + Complex.I • Y.1 - (X.1 - Complex.I • Y.1) = (2 * Complex.I) • Y.1 := by module
  rw [h2, smul_smul, h, one_smul]

theorem exists_mk (hJ : Jᴴ = J) (hu : IsUnit J.det) (Z : Matrix (Fin n) (Fin n) ℂ) :
    ∃ X Y : lieU J, Z = X.1 + Complex.I • Y.1 := ⟨_, _, (re_add_im hJ hu Z).symm⟩

theorem exists_extension (hJ : Jᴴ = J) (hu : IsUnit J.det) {A : Type} [Ring A] [Algebra ℂ A] (ρ : lieU J → A)
    (hadd : ∀ X Y, ρ (X + Y) = ρ X + ρ Y) (hsm : ∀ (c : ℝ) X, ρ (c • X) = (c : ℂ) • ρ X)
    (hlie : ∀ X Y Z : lieU J, Z.1 = X.1 * Y.1 - Y.1 * X.1 → ρ Z = ρ X * ρ Y - ρ Y * ρ X) :
    ∃ R : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A,
      (∀ Z, R Z = ρ (rePart hJ hu Z) + Complex.I • ρ (imPart hJ hu Z)) ∧ (∀ X : lieU J, R X.1 = ρ X) ∧
      ∀ Z W, R (Z * W - W * Z) = R Z * R W - R W * R Z := by
  have hsub : ∀ X Y, ρ (X - Y) = ρ X - ρ Y := by
    intro X Y
    have := hadd (X - Y) Y
    rw [sub_add_cancel] at this
    rw [this, add_sub_cancel_right]
  have h0 : ρ 0 = 0 := by
    have := hsub 0 0
    rwa [sub_self, sub_self] at this
  let r : Matrix (Fin n) (Fin n) ℂ → A := fun Z => ρ (rePart hJ hu Z) + Complex.I • ρ (imPart hJ hu Z)
  have key : ∀ X Y : lieU J, r (X.1 + Complex.I • Y.1) = ρ X + Complex.I • ρ Y := by
    intro X Y
    simp only [r, rePart_mk, imPart_mk]
  have hII : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] (m : M), Complex.I • Complex.I • m = -m := by
    intro M _ _ m
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  have hbr : ∀ X Y : lieU J, ρ ⁅X, Y⁆ = ρ X * ρ Y - ρ Y * ρ X := fun X Y => hlie X Y _ rfl
  have hbc : ∀ X Y : lieU J, (⁅X, Y⁆ : lieU J).1 = X.1 * Y.1 - Y.1 * X.1 := fun X Y => rfl
  refine ⟨{ toFun := r, map_add' := ?_, map_smul' := ?_ }, fun Z => rfl, ?_, ?_⟩
  · intro Z W
    obtain ⟨X, Y, rfl⟩ := exists_mk hJ hu Z
    obtain ⟨X', Y', rfl⟩ := exists_mk hJ hu W
    have : X.1 + Complex.I • Y.1 + (X'.1 + Complex.I • Y'.1) = (X + X').1 + Complex.I • (Y + Y').1 := by
      change _ = (X.1 + X'.1) + Complex.I • (Y.1 + Y'.1)
      module
    rw [this, key, key, key, hadd, hadd]
    module
  · intro c Z
    obtain ⟨X, Y, rfl⟩ := exists_mk hJ hu Z
    have hc : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := (Complex.re_add_im c).symm
    generalize c.re = a at hc
    generalize c.im = b at hc
    subst hc
    have : ((a : ℂ) + (b : ℂ) * Complex.I) • (X.1 + Complex.I • Y.1) =
        (a • X - b • Y).1 + Complex.I • (b • X + a • Y).1 := by
      change _ = ((a : ℂ) • X.1 - (b : ℂ) • Y.1) + Complex.I • ((b : ℂ) • X.1 + (a : ℂ) • Y.1)
      simp only [add_smul, smul_add, mul_smul, hII]
      module
    rw [this, key, key, hsub, hadd, hsm, hsm, hsm, hsm]
    simp only [RingHom.id_apply, add_smul, smul_add, mul_smul, hII]
    module
  · intro X
    have := key X 0
    simpa [h0] using this
  · intro Z W
    obtain ⟨X, Y, rfl⟩ := exists_mk hJ hu Z
    obtain ⟨X', Y', rfl⟩ := exists_mk hJ hu W
    have : (X.1 + Complex.I • Y.1) * (X'.1 + Complex.I • Y'.1) - (X'.1 + Complex.I • Y'.1) * (X.1 + Complex.I • Y.1) =
        (⁅X, X'⁆ - ⁅Y, Y'⁆ : lieU J).1 + Complex.I • (⁅X, Y'⁆ + ⁅Y, X'⁆ : lieU J).1 := by
      change _ = ((X.1 * X'.1 - X'.1 * X.1) - (Y.1 * Y'.1 - Y'.1 * Y.1)) +
        Complex.I • ((X.1 * Y'.1 - Y'.1 * X.1) + (Y.1 * X'.1 - X'.1 * Y.1))
      simp only [add_mul, mul_add, mul_smul_comm, smul_mul_assoc, smul_add, hII]
      module
    change r _ = r _ * r _ - r _ * r _
    rw [this, key, key, key, hsub, hadd, hbr, hbr, hbr, hbr]
    simp only [add_mul, mul_add, mul_smul_comm, smul_mul_assoc, smul_add, hII]
    module

theorem glRel_and_span : ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) ℂ), Jᴴ = J → IsUnit J.det → ∃ P Q : Fin n → Fin n → GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J, (∀ a b, (P a b).1 = (1 / 2 : ℂ) • (Matrix.single a b 1 + -(J⁻¹ * (Matrix.single a b (1 : ℂ))ᴴ * J)) ∧ (Q a b).1 = (1 / (2 * Complex.I)) • (Matrix.single a b 1 - -(J⁻¹ * (Matrix.single a b (1 : ℂ))ᴴ * J))) ∧ ∀ (A : Type) [Ring A] [Algebra ℂ A] (ρ : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J → A), (∀ X Y, ρ (X + Y) = ρ X + ρ Y) → (∀ (c : ℝ) X, ρ (c • X) = (c : ℂ) • ρ X) → (∀ X Y Z : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J, Z.1 = X.1 * Y.1 - Y.1 * X.1 → ρ Z = ρ X * ρ Y - ρ Y * ρ X) → Formalism.REAL.GlRel (fun a b => ρ (P a b) + Complex.I • ρ (Q a b)) ∧ ∀ X, ρ X ∈ Submodule.span ℂ (Set.range fun p : Fin n × Fin n => ρ (P p.1 p.2) + Complex.I • ρ (Q p.1 p.2)) := by
  intro n J hJ hu
  refine ⟨fun a b => rePart hJ hu (Matrix.single a b 1), fun a b => imPart hJ hu (Matrix.single a b 1),
    fun a b => ⟨rfl, rfl⟩, ?_⟩
  intro A _ _ ρ hadd hsm hlie
  obtain ⟨R, hR, hX, hc⟩ := exists_extension hJ hu ρ hadd hsm hlie
  simp only [← hR]
  constructor
  · intro a b c d
    simp only
    rw [← hc, map_sub]
    congr 1
    · split_ifs with h
      · subst h; rw [Matrix.single_mul_single_same, one_mul]
      · rw [Matrix.single_mul_single_of_ne (h := h), map_zero]
    · split_ifs with h
      · subst h; rw [Matrix.single_mul_single_same, one_mul]
      · rw [Matrix.single_mul_single_of_ne (h := h), map_zero]
  · intro X
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hX, Matrix.matrix_eq_sum_single X.1, map_sum]
    refine Submodule.sum_mem _ fun a _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Submodule.sum_mem _ fun b _ => ?_
    have : Matrix.single a b (X.1 a b) = X.1 a b • Matrix.single a b (1 : ℂ) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [this, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(a, b), rfl⟩)

end GlobalTheory.UnitaryLieComplexification
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryLieGeneratorsRepStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_lie_generators_rep : ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) ℂ), Jᴴ = J → IsUnit J.det → ∃ P Q : Fin n → Fin n → GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J, (∀ a b, (P a b).1 = (1 / 2 : ℂ) • (Matrix.single a b 1 + -(J⁻¹ * (Matrix.single a b (1 : ℂ))ᴴ * J)) ∧ (Q a b).1 = (1 / (2 * Complex.I)) • (Matrix.single a b 1 - -(J⁻¹ * (Matrix.single a b (1 : ℂ))ᴴ * J))) ∧ ∀ (A : Type) [Ring A] [Algebra ℂ A] (ρ : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J → A), (∀ X Y, ρ (X + Y) = ρ X + ρ Y) → (∀ (c : ℝ) X, ρ (c • X) = (c : ℂ) • ρ X) → (∀ X Y Z : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J, Z.1 = X.1 * Y.1 - Y.1 * X.1 → ρ Z = ρ X * ρ Y - ρ Y * ρ X) → Formalism.REAL.GlRel (fun a b => ρ (P a b) + Complex.I • ρ (Q a b)) ∧ ∀ X, ρ X ∈ Submodule.span ℂ (Set.range fun p : Fin n × Fin n => ρ (P p.1 p.2) + Complex.I • ρ (Q p.1 p.2)) := by
  first | exact @GlobalTheory.UnitaryLieComplexification.glRel_and_span | exact GlobalTheory.UnitaryLieComplexification.glRel_and_span | (intros; apply GlobalTheory.UnitaryLieComplexification.glRel_and_span <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryAdelicHeightCosetLeNormInfPow
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryAdelicHeightCosetLeNormInfPow
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.SmoothForms.HeightCoset

open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies

theorem opNorm_le_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A‖ ≤ ∑ i, ∑ j, ‖A i j‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  refine (Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => norm_nonneg _).trans ?_
  gcongr
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have : (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A x) i = ∑ j, A i j * x j := rfl
  rw [this, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul]
  gcongr
  exact PiLp.norm_apply_le x j

variable {D : D7}

theorem infMat_mul' (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (V : HSp D) (g h : GA D V) :
    infMat D.sp.cm.sig V.gram θ (g * h) = infMat D.sp.cm.sig V.gram θ g * infMat D.sp.cm.sig V.gram θ h := by
  have : HA.mat (AF D.host.F) D.sp.cm.sig V.gram (g * h) =
    HA.mat (AF D.host.F) D.sp.cm.sig V.gram g * HA.mat (AF D.host.F) D.sp.cm.sig V.gram h := rfl
  simp only [infMat, this, Units.val_mul]
  rw [Matrix.map_mul, Matrix.map_mul]

theorem infMat_one' (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (V : HSp D) :
    infMat D.sp.cm.sig V.gram θ (1 : GA D V) = 1 := by
  have : HA.mat (AF D.host.F) D.sp.cm.sig V.gram (1 : GA D V) = 1 := rfl
  simp only [infMat, this, Units.val_one]
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]

theorem finMat_eq (V : HSp D) (g : GA D V) : finMat D.sp.cm.sig V.gram g = (finHom V g).1 := rfl

theorem finHt_mul (V : HSp D) (x g : GA D V) (hg : g ∈ GinfC V) (v) : finHt V v (x * g) = finHt V v x := by
  have h0 : finHom V g = 1 := hg
  have h1 : finMat D.sp.cm.sig V.gram (x * g) = finMat D.sp.cm.sig V.gram x := by
    rw [finMat_eq, finMat_eq, map_mul, h0, mul_one]
  have h2 : finMat D.sp.cm.sig V.gram (x * g)⁻¹ = finMat D.sp.cm.sig V.gram x⁻¹ := by
    rw [finMat_eq, finMat_eq, map_inv, map_inv, map_mul, h0, mul_one]
  simp only [finHt, finNorm, h1, h2]

variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)

theorem infNorm_mul_le (τ : D.what₂.Tau) (x g : GA D V) :
    infNorm θ V τ (x * g) ≤ infNorm θ V τ x * infNorm θ V τ g := by
  unfold infNorm
  rw [infMat_mul', map_mul]
  exact nnnorm_mul_le _ _

theorem infHt_mul_le (τ : D.what₂.Tau) (x g : GA D V) :
    infHt θ V τ (x * g) ≤ infHt θ V τ x * infHt θ V τ g := by
  refine max_le (one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _)) (max_le ?_ ?_)
  · refine (infNorm_mul_le θ V τ x g).trans (mul_le_mul' ?_ ?_) <;>
      exact le_max_of_le_right (le_max_left _ _)
  · rw [_root_.mul_inv_rev, mul_comm (infHt θ V τ x)]
    refine (infNorm_mul_le θ V τ g⁻¹ x⁻¹).trans (mul_le_mul' ?_ ?_) <;>
      exact le_max_of_le_right (le_max_right _ _)

theorem infNorm_le_normInf (τ : D.what₂.Tau) (g : GA D V) :
    (infNorm θ V τ g : ℝ) ≤ normInf θ V g ∧ (infNorm θ V τ g⁻¹ : ℝ) ≤ normInf θ V g := by
  have h : ∑ i, ∑ j, (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖)
      ≤ normInf θ V g :=
    Finset.single_le_sum (f := fun τ => ∑ i, ∑ j,
      (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖))
      (fun _ _ => by positivity) (Finset.mem_univ τ)
  constructor
  · refine (opNorm_le_sum _).trans (le_trans ?_ h)
    gcongr
    exact le_add_of_nonneg_right (norm_nonneg _)
  · refine (opNorm_le_sum _).trans (le_trans ?_ h)
    gcongr
    exact le_add_of_nonneg_left (norm_nonneg _)

theorem infHt_le_normInf (hV : 0 < V.rank) (τ : D.what₂.Tau) (g : GA D V) :
    (infHt θ V τ g : ℝ) ≤ normInf θ V g := by
  obtain ⟨h1, h2⟩ := infNorm_le_normInf θ V τ g
  haveI : Nonempty (Fin V.rank) := ⟨⟨0, hV⟩⟩
  have h3 : infNorm θ V τ 1 = 1 := by
    unfold infNorm
    rw [infMat_one', map_one]
    exact nnnorm_one
  have h4 : (1 : ℝ) ≤ infNorm θ V τ g * infNorm θ V τ g⁻¹ := by
    have := infNorm_mul_le θ V τ g g⁻¹
    rw [mul_inv_cancel, h3] at this
    exact_mod_cast this
  have h5 : 1 ≤ normInf θ V g := by
    by_contra hc
    push_neg at hc
    have a0 := (infNorm θ V τ g).coe_nonneg
    have b0 := (infNorm θ V τ g⁻¹).coe_nonneg
    nlinarith
  unfold infHt
  push_cast
  exact max_le h5 (max_le h1 h2)

theorem infHt_rank_zero (hV : V.rank = 0) (τ : D.what₂.Tau) (g : GA D V) : infHt θ V τ g = 1 := by
  haveI : IsEmpty (Fin V.rank) := by rw [hV]; infer_instance
  have h : ∀ g, infNorm θ V τ g ≤ 1 := fun g => by
    have := opNorm_le_sum (infMat D.sp.cm.sig V.gram (θ τ) g)
    rw [Finset.univ_eq_empty, Finset.sum_empty] at this
    exact_mod_cast this.trans zero_le_one
  exact max_eq_left (max_le (h g) (h g⁻¹))

theorem height_mul_le (x g : GA D V) (hg : g ∈ GinfC V) :
    height θ V (x * g) ≤ height θ V x * ∏ τ, infHt θ V τ g := by
  unfold height
  simp only [finHt_mul V x g hg]
  rw [mul_right_comm, ← Finset.prod_mul_distrib]
  gcongr with τ
  exact infHt_mul_le θ V τ x g

theorem height_le_normInf_pow (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) :
    ∃ M : ℕ, ∀ x : GA D V, ∃ C : ℝ, ∀ g ∈ GinfC V,
      (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V (x * g) : ℝ) ≤ C * normInf θ V g ^ M := by
  rcases Nat.eq_zero_or_pos V.rank with hV | hV
  · refine ⟨0, fun x => ⟨height θ V x, fun g hg => ?_⟩⟩
    have := height_mul_le θ V x g hg
    simp only [infHt_rank_zero θ V hV, Finset.prod_const_one] at this
    rw [pow_zero]
    exact_mod_cast this
  · refine ⟨Fintype.card D.what₂.Tau, fun x => ⟨height θ V x, fun g hg => ?_⟩⟩
    have : (height θ V (x * g) : ℝ) ≤ height θ V x * ∏ τ, (infHt θ V τ g : ℝ) := by
      exact_mod_cast height_mul_le θ V x g hg
    refine this.trans ?_
    gcongr
    rw [← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun _ _ => NNReal.coe_nonneg _) fun τ _ => infHt_le_normInf θ V hV τ g

end GlobalTheory.SmoothForms.HeightCoset

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryAdelicHeightCosetLeNormInfPowStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAdelicHeight_coset_le_normInf_pow : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D), ∃ M : ℕ, ∀ x : GA D V, ∃ C : ℝ, ∀ g ∈ GinfC V, (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V (x * g) : ℝ) ≤ C * normInf θ V g ^ M := by
  first | exact @GlobalTheory.SmoothForms.HeightCoset.height_le_normInf_pow | exact GlobalTheory.SmoothForms.HeightCoset.height_le_normInf_pow | (intros; apply GlobalTheory.SmoothForms.HeightCoset.height_le_normInf_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.NormInfSubmultiplicativeLeAdelicHeight
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.NormInfSubmultiplicativeLeAdelicHeight
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.SmoothForms.NormInf

theorem entrySum_mul_le {n : Type} [Fintype n] (A B : Matrix n n ℂ) :
    ∑ i, ∑ j, ‖(A * B) i j‖ ≤ (∑ i, ∑ j, ‖A i j‖) * ∑ i, ∑ j, ‖B i j‖ := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  calc ∑ j, ‖(A * B) i j‖ ≤ ∑ j, ∑ k, ‖A i k‖ * ‖B k j‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [Matrix.mul_apply]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => norm_mul_le _ _)
    _ = ∑ k, ‖A i k‖ * ∑ j, ‖B k j‖ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
    _ ≤ _ := by
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact Finset.single_le_sum (f := fun k => ∑ j, ‖B k j‖)
          (fun k _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ k)

theorem norm_entry_le_opNorm {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (i j : n) :
    ‖A i j‖ ≤ ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A‖ := by
  have h := (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A).le_opNorm (EuclideanSpace.single j (1 : ℂ))
  have h1 : ‖(EuclideanSpace.single j (1 : ℂ) : EuclideanSpace ℂ n)‖ = 1 := by simp
  rw [h1, mul_one] at h
  refine le_trans ?_ h
  refine le_trans (le_of_eq ?_) (PiLp.norm_apply_le _ i)
  congr 1
  change _ = (A *ᵥ Pi.single j 1) i
  simp

theorem sum_mul_add_le {ι : Type} [Fintype ι] (a b c d : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hc : ∀ i, 0 ≤ c i) (hd : ∀ i, 0 ≤ d i) :
    ∑ i, (a i * c i + d i * b i) ≤ (∑ i, (a i + b i)) * ∑ i, (c i + d i) := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h : c i + d i ≤ ∑ i, (c i + d i) :=
    Finset.single_le_sum (f := fun i => c i + d i) (fun i _ => add_nonneg (hc i) (hd i)) (Finset.mem_univ i)
  refine le_trans ?_ (mul_le_mul_of_nonneg_left h (add_nonneg (ha i) (hb i)))
  nlinarith [mul_nonneg (ha i) (hd i), mul_nonneg (hb i) (hc i)]

theorem infMat_mul' {D : D7} (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (V : HSp D) (g h : GA D V) :
    infMat D.sp.cm.sig V.gram θ (g * h) = infMat D.sp.cm.sig V.gram θ g * infMat D.sp.cm.sig V.gram θ h := by
  have : HA.mat (AF D.host.F) D.sp.cm.sig V.gram (g * h) =
    HA.mat (AF D.host.F) D.sp.cm.sig V.gram g * HA.mat (AF D.host.F) D.sp.cm.sig V.gram h := rfl
  simp only [infMat, this, Units.val_mul]
  rw [Matrix.map_mul, Matrix.map_mul]

theorem infHt_le_height {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (τ : D.what₂.Tau) (g : GA D V) : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infHt θ V τ g ≤ GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height
  refine le_trans ?_ (le_mul_of_one_le_right' (one_le_finprod' fun _ => le_max_left _ _))
  exact Finset.single_le_prod' (f := fun τ => GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infHt θ V τ g)
    (fun _ _ => le_max_left _ _) (Finset.mem_univ τ)

end GlobalTheory.SmoothForms.NormInf

namespace GlobalTheory.SmoothForms


open NormInf in
theorem normInf_mul_le_and_le_height :
    ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D),
      (∀ g h : GA D V, normInf θ V (g * h) ≤ normInf θ V g * normInf θ V h) ∧
        ∃ C : ℝ, ∀ g : GA D V, normInf θ V g ≤ C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g : ℝ) := by
  intro D θ V
  refine ⟨fun g h => ?_, ⟨∑ _τ : D.what₂.Tau, ∑ _i : Fin V.rank, ∑ _j : Fin V.rank, (2 : ℝ), fun g => ?_⟩⟩
  · unfold normInf
    simp only [Finset.sum_add_distrib (s := (Finset.univ : Finset (Fin V.rank)))]
    have hn : ∀ (x : GA D V) τ, 0 ≤ ∑ i, ∑ j, ‖infMat D.sp.cm.sig V.gram (θ τ) x i j‖ := fun x τ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
    refine le_trans ?_ (sum_mul_add_le _ _ _ _ (hn g) (hn g⁻¹) (hn h) (hn h⁻¹))
    refine Finset.sum_le_sum fun τ _ => ?_
    rw [_root_.mul_inv_rev, infMat_mul', infMat_mul']
    exact add_le_add (entrySum_mul_le _ _) (entrySum_mul_le _ _)
  · unfold normInf
    simp only [Finset.sum_mul]
    refine Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have h0 := infHt_le_height θ V τ g
    have h1 : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infNorm θ V τ g ≤ GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g :=
      ((le_max_left _ _).trans (le_max_right _ _)).trans h0
    have h2 : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infNorm θ V τ g⁻¹ ≤ GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g :=
      ((le_max_right _ _).trans (le_max_right _ _)).trans h0
    have h3 := (norm_entry_le_opNorm (infMat D.sp.cm.sig V.gram (θ τ) g) i j).trans (NNReal.coe_le_coe.2 h1)
    have h4 := (norm_entry_le_opNorm (infMat D.sp.cm.sig V.gram (θ τ) g⁻¹) i j).trans (NNReal.coe_le_coe.2 h2)
    linarith

end GlobalTheory.SmoothForms
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.NormInfSubmultiplicativeLeAdelicHeightStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normInf_submultiplicative_le_adelicHeight : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D), (∀ g h : GA D V, normInf θ V (g * h) ≤ normInf θ V g * normInf θ V h) ∧ ∃ C : ℝ, ∀ g : GA D V, normInf θ V g ≤ C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g : ℝ) := by
  first | exact @GlobalTheory.SmoothForms.normInf_mul_le_and_le_height | exact GlobalTheory.SmoothForms.normInf_mul_le_and_le_height | (intros; apply GlobalTheory.SmoothForms.normInf_mul_le_and_le_height <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFiniteCosetsAdelicUnitaryBoundedDenominato
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFiniteCosetsAdelicUnitaryBoundedDenominato
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.SmoothForms.Cover

open NumberField IsDedekindDomain Topology

theorem exists_finset_of_compact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H : Subgroup G) (U : Subgroup H) (hU : IsOpen (U : Set H)) (K : Set G) (hK : IsCompact K)
    (Ω : Set H) (hΩ : ∀ k ∈ Ω, (k : G) ∈ K) :
    ∃ S : Finset H, (∀ x ∈ S, x ∈ Ω) ∧ ∀ k ∈ Ω, ∃ x ∈ S, x⁻¹ * k ∈ U := by
  classical
  obtain ⟨W, hW, hWU⟩ := isOpen_induced_iff.1 hU
  have h1 : (1 : G) ∈ W := by
    have : (1 : H) ∈ (U : Set H) := U.one_mem
    rw [← hWU] at this
    exact this
  have hc : Continuous fun p : G × G => p.1⁻¹ * p.2 := by fun_prop
  have h2 : (fun p : G × G => p.1⁻¹ * p.2) ⁻¹' W ∈ 𝓝 ((1, 1) : G × G) :=
    (hW.preimage hc).mem_nhds (by simpa using h1)
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.1 h2
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun x => (fun y => x⁻¹ * y) ⁻¹' (A ∩ B)) (fun x _ => by
    have : Continuous fun y : G => x⁻¹ * y := by fun_prop
    exact this.continuousAt.preimage_mem_nhds (by simpa using ⟨hA, hB⟩))
  have hch : ∀ x : G, (∃ s ∈ Ω, x⁻¹ * (s : G) ∈ A ∩ B) → ∃ s ∈ Ω, x⁻¹ * (s : G) ∈ A ∩ B := fun _ h => h
  choose f hf hf' using hch
  refine ⟨(t.filter fun x => ∃ s ∈ Ω, x⁻¹ * (s : G) ∈ A ∩ B).attach.image
    fun x => f x.1 (by have h := x.2; rw [Finset.mem_filter] at h; exact h.2), ?_, ?_⟩
  · intro x hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hx
    exact hf _ _
  · intro k hk
    obtain ⟨x, hx, hxk⟩ := Set.mem_iUnion₂.1 (ht (hΩ k hk))
    have hex : ∃ s ∈ Ω, x⁻¹ * (s : G) ∈ A ∩ B := ⟨k, hk, hxk⟩
    refine ⟨f x hex, Finset.mem_image.2 ⟨⟨x, Finset.mem_filter.2 ⟨hx, hex⟩⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
    have h3 := hAB (Set.mk_mem_prod (hf' x hex).1 hxk.2)
    have h4 : (x⁻¹ * (f x hex : G))⁻¹ * (x⁻¹ * (k : G)) = (((f x hex)⁻¹ * k : H) : G) := by
      push_cast; group
    change _ ∈ (U : Set H)
    rw [← hWU]
    change _ ∈ W
    rw [← h4]
    exact h3

theorem isCompact_GL {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] {n : ℕ}
    (C : Fin n → Fin n → Set A) (hC : ∀ i j, IsCompact (C i j)) :
    IsCompact {g : GL (Fin n) A | ∀ i j, g.1 i j ∈ C i j ∧ (g⁻¹).1 i j ∈ C i j} := by
  have h1 : IsCompact {m : Matrix (Fin n) (Fin n) A | ∀ i j, m i j ∈ C i j} :=
    isCompact_pi_infinite fun i => isCompact_pi_infinite (hC i)
  have h2 := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) A)).isCompact_preimage
    (h1.prod (h1.image MulOpposite.continuous_op))
  convert h2 using 1
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod, Set.mem_image,
    MulOpposite.op_inj, exists_eq_right, forall_and]

theorem exists_compact_denom (D : D7) (d : ℕ) (hd : 0 < d) :
    ∃ C : Set (Af D.host.F ⊗[D.host.F] D.host.E), IsCompact C ∧ ∀ y, d • y ∈ intAE D → y ∈ C := by
  classical
  haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (Af D.host.F) _
  let b := RingOfIntegers.basis D.host.E
  let O : AddSubgroup (Af D.host.F) :=
    { carrier := {a | ∀ v, a v ∈ v.adicCompletionIntegers D.host.F}
      zero_mem' := fun v => zero_mem _
      add_mem' := fun ha hb v => add_mem (ha v) (hb v)
      neg_mem' := fun ha v => neg_mem (ha v) }
  let φ : (Module.Free.ChooseBasisIndex ℤ (𝓞 D.host.E) → Af D.host.F) →+
      Af D.host.F ⊗[D.host.F] D.host.E :=
    { toFun := fun a => ∑ i, a i • ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b i : D.host.E))
      map_zero' := by simp
      map_add' := fun x y => by simp [add_smul, Finset.sum_add_distrib] }
  have hφ : Continuous φ :=
    continuous_finsetSum _ fun i _ => (continuous_apply i).fun_smul continuous_const
  have hle : intAE D ≤ (AddSubgroup.pi Set.univ fun _ => O).map φ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro y ⟨a, ha, x, rfl⟩
    refine ⟨fun i => b.repr x i • a, fun i _ => zsmul_mem (show a ∈ O from ha) _, ?_⟩
    change ∑ i, (b.repr x i • a) • ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b i : D.host.E)) = _
    conv_rhs => rw [← b.sum_repr x]
    change _ = a ⊗ₜ[D.host.F] (algebraMap (𝓞 D.host.E) D.host.E _)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, smul_assoc, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    exact (map_zsmul (TensorProduct.mk D.host.F (Af D.host.F) D.host.E a) _ _).symm
  have hO : IsCompact (Set.pi Set.univ fun _ : Module.Free.ChooseBasisIndex ℤ (𝓞 D.host.E) =>
      (O : Set (Af D.host.F))) :=
    isCompact_univ_pi fun _ => GlobalTheory.AdeleCocompact.isCompact_integral D.host.F
  let c : Af D.host.F := algebraMap D.host.F (Af D.host.F) (d : D.host.F)⁻¹
  have hcs : Continuous fun y : Af D.host.F ⊗[D.host.F] D.host.E => c • y :=
    (continuous_const (y := c)).fun_smul continuous_id
  refine ⟨(fun y => c • y) '' (φ '' _), (hO.image hφ).image hcs, fun y hy => ?_⟩
  refine ⟨d • y, hle hy, ?_⟩
  have : (d : D.host.F) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  change c • d • y = y
  rw [← Nat.cast_smul_eq_nsmul (Af D.host.F), smul_smul,
    ← map_natCast (algebraMap D.host.F (Af D.host.F)) d, ← map_mul, inv_mul_cancel₀ this, map_one, one_smul]

theorem exists_finset_cover : ∀ (D : D7) (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → ∀ d : ℕ, 0 < d → ∃ S : Finset (GA D V), ∀ k ∈ GfC V, BddDen V d k → ∃ x ∈ S, x⁻¹ * k ∈ U ∧ x⁻¹ * k ∈ GfC V := by
  intro D V U hU d hd
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (AF D.host.F)
  haveI : T2Space (AE D) := e0.isEmbedding.t2Space
  obtain ⟨C, hC, hCd⟩ := exists_compact_denom D d hd
  obtain ⟨e, he, -, hc⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  let C' : Fin V.rank → Fin V.rank → Set (AE D) := fun i j =>
    e.symm '' ({(1 : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) i j} ×ˢ C)
  have hC' : ∀ i j, IsCompact (C' i j) := fun i j => (isCompact_singleton.prod hC).image hc
  have key : ∀ k ∈ GfC V, (∀ i j, d • finMat D.sp.cm.sig V.gram k i j ∈ intAE D) →
      ∀ i j, (matHom V k).1 i j ∈ C' i j := by
    intro k hk h i j
    refine ⟨e ((matHom V k).1 i j), ⟨?_, ?_⟩, e.symm_apply_apply _⟩
    · rw [(he _).1]
      have h1 : (infHom V k).1 i j = _ := congrArg (fun g => g.1 i j) (MonoidHom.mem_ker.1 hk)
      exact h1
    · rw [(he _).2]
      exact hCd _ (h i j)
  obtain ⟨S, hS, hS'⟩ := exists_finset_of_compact (HR (AF D.host.F) D.sp.cm.sig V.gram) U hU _
    (isCompact_GL C' hC') {k : GA D V | k ∈ GfC V ∧ BddDen V d k} (fun k hk i j =>
      ⟨key k hk.1 (fun i j => (hk.2 i j).1) i j, key k⁻¹ (inv_mem hk.1) (fun i j => (hk.2 i j).2) i j⟩)
  refine ⟨S, fun k hk hb => ?_⟩
  obtain ⟨x, hx, hxk⟩ := hS' k ⟨hk, hb⟩
  exact ⟨x, hx, hxk, mul_mem (inv_mem (hS x hx).1) hk⟩

end GlobalTheory.SmoothForms.Cover
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFiniteCosetsAdelicUnitaryBoundedDenominatoStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_cosets_adelicUnitary_bounded_denominator : ∀ (D : D7) (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → ∀ d : ℕ, 0 < d → ∃ S : Finset (GA D V), ∀ k ∈ GfC V, BddDen V d k → ∃ x ∈ S, x⁻¹ * k ∈ U ∧ x⁻¹ * k ∈ GfC V := by
  first | exact @GlobalTheory.SmoothForms.Cover.exists_finset_cover | exact GlobalTheory.SmoothForms.Cover.exists_finset_cover | (intros; apply GlobalTheory.SmoothForms.Cover.exists_finset_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsEnvelopingAlgHomUnitaryLieAlgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsEnvelopingAlgHomUnitaryLieAlgebra
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

namespace GlobalTheory.EnvelopingExtension

theorem exists_algHom_of_real (L : Type) [LieRing L] [LieAlgebra ℝ L] (A : Type) [Ring A] [Algebra ℂ A] (ρ : L → A)
    (hadd : ∀ X Y, ρ (X + Y) = ρ X + ρ Y) (hsmul : ∀ (c : ℝ) X, ρ (c • X) = (c : ℂ) • ρ X)
    (hbr : ∀ X Y, ρ ⁅X, Y⁆ = ρ X * ρ Y - ρ Y * ρ X) :
    ∃ π : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L) →ₐ[ℂ] A,
      ∀ X, π (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)) = ρ X := by
  let f : L →ₗ[ℝ] A :=
    { toFun := ρ
      map_add' := hadd
      map_smul' := fun c X => by
        rw [hsmul]
        exact Complex.coe_smul c (ρ X) }
  let F : ℂ ⊗[ℝ] L →ₗ[ℂ] A := f.liftBaseChange ℂ
  have hF : ∀ (a : ℂ) (x : L), F (a ⊗ₜ x) = a • ρ x := fun a x => by
    simp [F, f, LinearMap.liftBaseChange_tmul]
  have hlie : ∀ u v : ℂ ⊗[ℝ] L, F ⁅u, v⁆ = ⁅F u, F v⁆ := by
    intro u v
    induction u using TensorProduct.induction_on with
    | zero => simp
    | add u₁ u₂ h₁ h₂ => rw [add_lie, map_add (f := _), h₁, h₂, map_add (f := _), add_lie]
    | tmul a x =>
      induction v using TensorProduct.induction_on with
      | zero => simp
      | add v₁ v₂ h₁ h₂ => rw [lie_add, map_add (f := _), h₁, h₂, map_add (f := _), lie_add]
      | tmul b y =>
        rw [LieAlgebra.ExtendScalars.bracket_tmul, hF, hF, hF, hbr, Ring.lie_def,
          smul_mul_smul_comm, smul_mul_smul_comm, mul_comm b a, smul_sub]
  let G : ℂ ⊗[ℝ] L →ₗ⁅ℂ⁆ A := { F with map_lie' := fun {u v} => hlie u v }
  refine ⟨UniversalEnvelopingAlgebra.lift ℂ G, fun X => ?_⟩
  rw [UniversalEnvelopingAlgebra.lift_ι_apply]
  change F ((1 : ℂ) ⊗ₜ X) = ρ X
  rw [hF, one_smul]

theorem exists_algHom_unitary : ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) ℂ) (A : Type) [Ring A] [Algebra ℂ A] (ρ : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J → A), (∀ X Y, ρ (X + Y) = ρ X + ρ Y) → (∀ (c : ℝ) X, ρ (c • X) = (c : ℂ) • ρ X) → (∀ X Y Z : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J, Z.1 = X.1 * Y.1 - Y.1 * X.1 → ρ Z = ρ X * ρ Y - ρ Y * ρ X) → ∃ π : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J) →ₐ[ℂ] A, ∀ X, π (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)) = ρ X := by
  intro n J A _ _ ρ hadd hsmul hbr
  exact exists_algHom_of_real _ A ρ hadd hsmul fun X Y => hbr X Y ⁅X, Y⁆ (by
    rw [LieSubalgebra.coe_bracket, Ring.lie_def])

end GlobalTheory.EnvelopingExtension

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsEnvelopingAlgHomUnitaryLieAlgebraStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_envelopingAlgHom_unitaryLieAlgebra : ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) ℂ) (A : Type) [Ring A] [Algebra ℂ A] (ρ : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J → A), (∀ X Y, ρ (X + Y) = ρ X + ρ Y) → (∀ (c : ℝ) X, ρ (c • X) = (c : ℂ) • ρ X) → (∀ X Y Z : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J, Z.1 = X.1 * Y.1 - Y.1 * X.1 → ρ Z = ρ X * ρ Y - ρ Y * ρ X) → ∃ π : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J) →ₐ[ℂ] A, ∀ X, π (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)) = ρ X := by
  first | exact @GlobalTheory.EnvelopingExtension.exists_algHom_unitary | exact GlobalTheory.EnvelopingExtension.exists_algHom_unitary | (intros; apply GlobalTheory.EnvelopingExtension.exists_algHom_unitary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.EnvelopingMapSurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.EnvelopingMapSurjective
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.EnvWords

theorem mem_span_words (L : Type) [LieRing L] [LieAlgebra ℝ L] (u : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L)) :
    u ∈ Submodule.span ℂ (Set.range fun l : List L =>
      (l.map fun X => UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)).prod) := by
  have hs : Function.Surjective (UniversalEnvelopingAlgebra.mkAlgHom ℂ (ℂ ⊗[ℝ] L)) :=
    fun u => Quotient.exists_rep u
  obtain ⟨t, rfl⟩ := hs u
  induction t using TensorAlgebra.induction with
  | algebraMap r =>
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[], rfl⟩)
  | ι x =>
    change UniversalEnvelopingAlgebra.ι ℂ x ∈ _
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | tmul z X =>
      have h : z ⊗ₜ[ℝ] X = z • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h, map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[X], by simp⟩)
    | add x y hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | mul a b ha hb =>
    rw [map_mul]
    have h := Submodule.mul_mem_mul ha hb
    rw [Submodule.span_mul_span] at h
    refine Submodule.span_mono ?_ h
    rintro _ ⟨_, ⟨l, rfl⟩, _, ⟨m, rfl⟩, rfl⟩
    exact ⟨l ++ m, by simp only [List.map_append, List.prod_append]⟩
  | add a b ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb

theorem envOf_surjective : ∀ (D : D7) (V : HSp D) (τ : D.what₂.Tau),
    Function.Surjective (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.envOf V τ) := by
  intro D V τ u
  exact (Finsupp.mem_span_range_iff_exists_finsupp).1 (mem_span_words (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt V τ) u)

end GlobalTheory.EnvWords
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.EnvelopingMapSurjectiveStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.enveloping_map_surjective : ∀ (D : D7) (V : HSp D) (τ : D.what₂.Tau), Function.Surjective (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.envOf V τ) := by
  first | exact @GlobalTheory.EnvWords.envOf_surjective | exact GlobalTheory.EnvWords.envOf_surjective | (intros; apply GlobalTheory.EnvWords.envOf_surjective <;> assumption)
end
end
