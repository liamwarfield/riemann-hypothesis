module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyFiniteBaseChangeFilteredColimit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyZmodTorsorGaloisProductMapBijectiveCol

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveEventuallyFilteredColimitAlgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialSystemEventuallySolvableColimit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialSystemEventuallySolvableColimit
open CategoryTheory Limits TensorProduct

namespace GlobalTheory.TorsorColim

theorem poly_eventually_solvable :
    ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (j : J) (σ ι : Type) [Finite σ] [Finite ι] (p : ι → MvPolynomial σ (F.obj j)) (x : σ → c.pt),
    (∀ i, MvPolynomial.eval₂ (c.ι.app j).hom x (p i) = 0) →
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k), ∃ y : σ → F.obj k,
      ∀ i, MvPolynomial.eval₂ (F.map (f₀ ≫ f)).hom y (p i) = 0 := by
  classical
  intro J _ _ F c hc j σ ι _ _ p x hx
  haveI := Fintype.ofFinite σ
  haveI := Fintype.ofFinite ι
  have hc' := isColimitOfPreserves (forget _) hc

  choose jx x' hx' using fun s : σ => Types.jointly_surjective_of_isColimit hc' (x s)
  obtain ⟨K, hK⟩ := IsFiltered.sup_objs_exists (insert j (Finset.univ.image jx))
  obtain ⟨h⟩ := hK (Finset.mem_insert_self j _)
  have hm : ∀ s, Nonempty (jx s ⟶ K) := fun s =>
    hK (Finset.mem_insert_of_mem (Finset.mem_image_of_mem jx (Finset.mem_univ s)))
  let u : σ → F.obj K := fun s => (F.map (hm s).some).hom (x' s)
  have hu : ∀ s, (c.ι.app K).hom (u s) = x s := by
    intro s
    have h2 := congr(($(c.w (hm s).some)).hom (x' s))
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h2
    rw [h2]
    exact hx' s

  have hz : ∀ i, (c.ι.app K).hom (MvPolynomial.eval₂ (F.map h).hom u (p i)) = 0 := by
    intro i
    rw [MvPolynomial.eval₂_comp_left]
    have e1 : (c.ι.app K).hom.comp (F.map h).hom = (c.ι.app j).hom := by
      rw [← CommRingCat.hom_comp, c.w h]
    have e2 : ⇑(c.ι.app K).hom ∘ u = x := funext hu
    rw [e1, e2]; exact hx i

  have one : ∀ i, ∃ (k₀ : J) (f₀ : K ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      (F.map (f₀ ≫ f)).hom (MvPolynomial.eval₂ (F.map h).hom u (p i)) = 0 := by
    intro i
    have h0 : (c.ι.app K).hom (MvPolynomial.eval₂ (F.map h).hom u (p i)) = (c.ι.app K).hom 0 := by
      rw [hz i, map_zero]
    obtain ⟨k₀, f₀, e⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc' _ 0).1 (by exact h0)
    refine ⟨k₀, f₀, fun k f => ?_⟩
    have e' : (F.map f₀).hom (MvPolynomial.eval₂ (F.map h).hom u (p i)) = 0 := by simpa using e
    rw [Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply, e', map_zero]

  have all : ∀ S : Finset ι, ∃ (k₀ : J) (f₀ : K ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      ∀ i ∈ S, (F.map (f₀ ≫ f)).hom (MvPolynomial.eval₂ (F.map h).hom u (p i)) = 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨K, 𝟙 K, fun _ _ i hi => absurd hi (Finset.notMem_empty i)⟩
    | insert a S _ ih =>
      obtain ⟨k₀, f₀, hh⟩ := eventually_and
        (fun k (g : K ⟶ k) => (F.map g).hom (MvPolynomial.eval₂ (F.map h).hom u (p a)) = 0)
        (fun k (g : K ⟶ k) => ∀ i ∈ S, (F.map g).hom (MvPolynomial.eval₂ (F.map h).hom u (p i)) = 0)
        (one a) ih
      refine ⟨k₀, f₀, fun k f i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact (hh k f).1
      · exact (hh k f).2 i hi
  obtain ⟨k₀, f₀, h0⟩ := all Finset.univ
  refine ⟨k₀, h ≫ f₀, fun k f => ⟨fun s => (F.map (f₀ ≫ f)).hom (u s), fun i => ?_⟩⟩
  have := h0 k f i (Finset.mem_univ i)
  rw [MvPolynomial.eval₂_comp_left, ← CommRingCat.hom_comp, ← Functor.map_comp] at this
  rw [Category.assoc]
  exact this

end GlobalTheory.TorsorColim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialSystemEventuallySolvableColimitStatement
open CategoryTheory Limits TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_system_eventually_solvable_colimit : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (j : J) (σ ι : Type) [Finite σ] [Finite ι] (p : ι → MvPolynomial σ (F.obj j)) (x : σ → c.pt),
    (∀ i, MvPolynomial.eval₂ (c.ι.app j).hom x (p i) = 0) →
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k), ∃ y : σ → F.obj k,
      ∀ i, MvPolynomial.eval₂ (F.map (f₀ ≫ f)).hom y (p i) = 0 := by
  first | (exact @GlobalTheory.TorsorColim.poly_eventually_solvable) | (exact GlobalTheory.TorsorColim.poly_eventually_solvable) | (intros; apply GlobalTheory.TorsorColim.poly_eventually_solvable  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPresentationMatrixOfProjectiveBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPresentationMatrixOfProjectiveBaseChange
open CategoryTheory Limits TensorProduct

namespace GlobalTheory

theorem projective_baseChange_presentation_matrix : ∀ (R B M : Type) [CommRing R] [CommRing B] [Algebra R B] [AddCommGroup M]
    [Module R M] (n m : ℕ) (π : (Fin n → R) →ₗ[R] M), Function.Surjective π →
    ∀ (r : Fin m → Fin n → R), Submodule.span R (Set.range r) = LinearMap.ker π →
    Module.Projective B (B ⊗[R] M) →
    ∃ (v : Fin n → Fin n → B) (w : Fin n → Fin m → B),
    (∀ b l, ∑ a, algebraMap R B (r b a) * v a l = 0) ∧
    (∀ a l, v a l = (if a = l then 1 else 0) + ∑ b, w a b * algebraMap R B (r b l)) := by
  intro R B M _ _ _ _ _ n m π hπ r hr hP
  let e := TensorProduct.piScalarRight R B B (Fin n)
  let πB : (Fin n → B) →ₗ[B] B ⊗[R] M := (π.baseChange B) ∘ₗ e.symm.toLinearMap
  have hπB : Function.Surjective πB := (LinearMap.lTensor_surjective B hπ).comp e.symm.surjective
  obtain ⟨i, hi⟩ := Module.projective_lifting_property πB LinearMap.id hπB
  let v : Fin n → Fin n → B := fun a => i ((1 : B) ⊗ₜ[R] π (Pi.single a 1))
  let f : (Fin m → R) →ₗ[R] (Fin n → R) := Fintype.linearCombination R r
  have hex : Function.Exact f π := by
    rw [LinearMap.exact_iff, Fintype.range_linearCombination, hr]
  have hexB := lTensor_exact B hex hπ
  let N : Submodule B (Fin n → B) := Submodule.span B (Set.range fun b l => algebraMap R B (r b l))
  have hker : ∀ y, πB y = 0 → y ∈ N := by
    intro y hy
    have h0 : (π.lTensor B) (e.symm y) = 0 := by
      have := hy
      simp only [πB, LinearMap.comp_apply, LinearEquiv.coe_coe] at this
      rwa [LinearMap.baseChange_eq_ltensor] at this
    obtain ⟨z, hz⟩ := (hexB _).1 h0
    have hy' : y = e (f.lTensor B z) := by rw [hz, LinearEquiv.apply_symm_apply]
    rw [hy']
    clear hz hy' h0 hy
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x c =>
        have : e ((f.lTensor B) (x ⊗ₜ c)) = ∑ b, (x * algebraMap R B (c b)) • (fun l => algebraMap R B (r b l)) := by
          ext l
          simp [e, f, Fintype.linearCombination_apply, Finset.sum_apply, Algebra.smul_def, Finset.mul_sum,
            Finset.sum_mul, mul_comm, mul_left_comm]
        rw [this]
        exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
    | add a b ha hb => rw [map_add (f := _), map_add (f := _)]; exact N.add_mem ha hb
  have hπv : ∀ a, πB (v a - Pi.single a 1) = 0 := by
    intro a
    have h1 : πB (v a) = (1 : B) ⊗ₜ[R] π (Pi.single a 1) := LinearMap.congr_fun hi _
    have h2 : e.symm (Pi.single a 1) = (1 : B) ⊗ₜ[R] (Pi.single a 1 : Fin n → R) := by
      rw [LinearEquiv.symm_apply_eq]
      ext l
      simp [e, Pi.single_apply]
    rw [map_sub, h1]
    simp [πB, h2]
  choose w hw using fun a => (Submodule.mem_span_range_iff_exists_fun B).1 (hker _ (hπv a))
  refine ⟨v, w, fun b l => ?_, fun a l => ?_⟩
  · have hrb : π (r b) = 0 := by
      have : r b ∈ LinearMap.ker π := hr ▸ Submodule.subset_span ⟨b, rfl⟩
      exact this
    have hsum : (1 : B) ⊗ₜ[R] π (r b) = ∑ a, algebraMap R B (r b a) • ((1 : B) ⊗ₜ[R] π (Pi.single a 1)) := by
      conv_lhs => rw [← Finset.univ_sum_single (r b)]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, TensorProduct.tmul_sum, algebraMap_smul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← TensorProduct.tmul_smul, ← map_smul]
      congr 2
      ext j
      simp [Pi.single_apply]
    have h1 : ∑ a, algebraMap R B (r b a) • v a = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [v, ← map_smul, ← map_sum, ← hsum, hrb, TensorProduct.tmul_zero, map_zero]
    have := congrFun h1 l
    simpa [Finset.sum_apply, Algebra.smul_def] using this
  · have := congrFun (hw a) l
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.single_apply] at this
    rw [this]
    simp [eq_comm]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPresentationMatrixOfProjectiveBaseChangeStatement
open CategoryTheory Limits TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_presentation_matrix_of_projective_baseChange : ∀ (R B M : Type) [CommRing R] [CommRing B] [Algebra R B] [AddCommGroup M]
    [Module R M] (n m : ℕ) (π : (Fin n → R) →ₗ[R] M), Function.Surjective π →
    ∀ (r : Fin m → Fin n → R), Submodule.span R (Set.range r) = LinearMap.ker π →
    Module.Projective B (B ⊗[R] M) →
    ∃ (v : Fin n → Fin n → B) (w : Fin n → Fin m → B),
    (∀ b l, ∑ a, algebraMap R B (r b a) * v a l = 0) ∧
    (∀ a l, v a l = (if a = l then 1 else 0) + ∑ b, w a b * algebraMap R B (r b l)) := by
  first | (exact @GlobalTheory.projective_baseChange_presentation_matrix) | (exact GlobalTheory.projective_baseChange_presentation_matrix) | (intros; apply GlobalTheory.projective_baseChange_presentation_matrix <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBaseChangeOfPresentationMatrixSplit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBaseChangeOfPresentationMatrixSplit
open CategoryTheory Limits TensorProduct

namespace GlobalTheory

theorem projective_baseChange_of_presentation_split
    (R B M : Type) [CommRing R] [CommRing B] [Algebra R B] [AddCommGroup M]
    [Module R M] (n m : ℕ) (π : (Fin n → R) →ₗ[R] M) (hπ : Function.Surjective π)
    (r : Fin m → Fin n → R) (hr : Submodule.span R (Set.range r) = LinearMap.ker π)
    (v : Fin n → Fin n → B) (w : Fin n → Fin m → B)
    (hv : ∀ b l, ∑ a, algebraMap R B (r b a) * v a l = 0)
    (hvw : ∀ a l, v a l = (if a = l then 1 else 0) + ∑ b, w a b * algebraMap R B (r b l)) :
    Module.Projective B (B ⊗[R] M) := by
  classical

  let φ : (Fin n → R) →ₗ[R] (Fin n → B) := ∑ a, (LinearMap.proj a).smulRight (v a)
  have hφ : ∀ x l, φ x l = ∑ a, algebraMap R B (x a) * v a l := by
    intro x l
    simp [φ, Finset.sum_apply, Algebra.smul_def]
  have hker : LinearMap.ker π ≤ LinearMap.ker φ := by
    rw [← hr, Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker]
    funext l
    rw [hφ]
    simpa using hv b l
  let ψ : M →ₗ[R] (Fin n → B) :=
    (LinearMap.ker π).liftQ φ hker ∘ₗ (π.quotKerEquivOfSurjective hπ).symm.toLinearMap
  have hψ : ∀ x, ψ (π x) = φ x := by
    intro x
    have : (π.quotKerEquivOfSurjective hπ).symm (π x) = Submodule.Quotient.mk x := by
      rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
    simp [ψ, this]
  let i : B ⊗[R] M →ₗ[B] (Fin n → B) := ψ.liftBaseChange B
  let s : (Fin n → B) →ₗ[B] B ⊗[R] M :=
    ∑ l, (LinearMap.proj l).smulRight ((1 : B) ⊗ₜ[R] π (Pi.single l 1))
  have hs : ∀ y, s y = ∑ l, y l • ((1 : B) ⊗ₜ[R] π (Pi.single l 1)) := by
    intro y; simp [s]
  have hsr : ∀ b, ∑ l, algebraMap R B (r b l) • ((1 : B) ⊗ₜ[R] π (Pi.single l 1)) = 0 := by
    intro b
    have h0 : π (r b) = 0 := by
      rw [← LinearMap.mem_ker, ← hr]; exact Submodule.subset_span ⟨b, rfl⟩
    have : ∑ l, algebraMap R B (r b l) • ((1 : B) ⊗ₜ[R] π (Pi.single l 1))
        = (1 : B) ⊗ₜ[R] π (r b) := by
      conv_rhs => rw [show r b = ∑ l, r b l • Pi.single l (1 : R) by
        ext j; simp [Finset.sum_apply, Pi.single_apply]]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, tmul_sum, algebraMap_smul, tmul_smul]
    rw [this, h0, tmul_zero]
  have hsv : ∀ a, s (v a) = (1 : B) ⊗ₜ[R] π (Pi.single a 1) := by
    intro a
    rw [hs]
    simp_rw [hvw a, add_smul, Finset.sum_add_distrib, Finset.sum_smul]
    rw [Finset.sum_comm]
    have : ∀ b, ∑ l, (w a b * algebraMap R B (r b l)) • ((1 : B) ⊗ₜ[R] π (Pi.single l 1)) = 0 := by
      intro b
      simp_rw [mul_smul, ← Finset.smul_sum, hsr, smul_zero]
    simp [this, ite_smul]
  have hsi : s ∘ₗ i = LinearMap.id := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro x y
    obtain ⟨z, rfl⟩ := hπ y
    simp only [LinearMap.comp_apply, LinearMap.id_apply, i, LinearMap.liftBaseChange_tmul, map_smul]
    have hz : φ z = ∑ a, z a • v a := by
      funext l; rw [hφ]; simp [Finset.sum_apply, Algebra.smul_def]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hψ, hz, map_sum]
    simp_rw [LinearMap.map_smul_of_tower, hsv]
    conv_rhs => rw [show z = ∑ a, z a • Pi.single a (1 : R) by
        ext j; simp [Finset.sum_apply, Pi.single_apply]]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, tmul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_comm, TensorProduct.smul_tmul', smul_eq_mul, mul_one, map_smul, TensorProduct.tmul_smul]
  exact Module.Projective.of_split i s hsi

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBaseChangeOfPresentationMatrixSplitStatement
open CategoryTheory Limits TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_baseChange_of_presentation_matrix_split : ∀ (R B M : Type) [CommRing R] [CommRing B] [Algebra R B] [AddCommGroup M]
    [Module R M] (n m : ℕ) (π : (Fin n → R) →ₗ[R] M), Function.Surjective π →
    ∀ (r : Fin m → Fin n → R), Submodule.span R (Set.range r) = LinearMap.ker π →
    ∀ (v : Fin n → Fin n → B) (w : Fin n → Fin m → B),
    (∀ b l, ∑ a, algebraMap R B (r b a) * v a l = 0) →
    (∀ a l, v a l = (if a = l then 1 else 0) + ∑ b, w a b * algebraMap R B (r b l)) →
    Module.Projective B (B ⊗[R] M) := by
  first | (exact @GlobalTheory.projective_baseChange_of_presentation_split) | (exact GlobalTheory.projective_baseChange_of_presentation_split) | (intros; apply GlobalTheory.projective_baseChange_of_presentation_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveEventuallyFilteredColimitAlgebra
open CategoryTheory Limits TensorProduct

noncomputable section

namespace GlobalTheory.ProjColim

noncomputable def sysPoly {R : Type} [CommRing R] (n m : ℕ) (r : Fin m → Fin n → R) :
    (Fin m × Fin n) ⊕ (Fin n × Fin n) → MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin m)) R
  | .inl (b, l) => ∑ a, MvPolynomial.C (r b a) * MvPolynomial.X (.inl (a, l))
  | .inr (a, l) => MvPolynomial.X (.inl (a, l)) - (if a = l then 1 else 0) -
      ∑ b, MvPolynomial.X (.inr (a, b)) * MvPolynomial.C (r b l)

theorem eval₂_sysPoly_eq_zero_iff {R B : Type} [CommRing R] [CommRing B] (φ : R →+* B) (n m : ℕ)
    (r : Fin m → Fin n → R) (x : (Fin n × Fin n) ⊕ (Fin n × Fin m) → B) :
    (∀ i, MvPolynomial.eval₂ φ x (sysPoly n m r i) = 0) ↔
      (∀ b l, ∑ a, φ (r b a) * x (.inl (a, l)) = 0) ∧
      (∀ a l, x (.inl (a, l)) = (if a = l then 1 else 0) + ∑ b, x (.inr (a, b)) * φ (r b l)) := by
  have key : ∀ a l, MvPolynomial.eval₂ φ x (sysPoly n m r (.inr (a, l))) =
      x (.inl (a, l)) - ((if a = l then 1 else 0) + ∑ b, x (.inr (a, b)) * φ (r b l)) := by
    intro a l
    by_cases h : a = l <;> simp [sysPoly, MvPolynomial.eval₂_sum, h, sub_sub]
  constructor
  · intro h
    refine ⟨fun b l => ?_, fun a l => ?_⟩
    · simpa [sysPoly, MvPolynomial.eval₂_sum] using h (.inl (b, l))
    · have := h (.inr (a, l))
      rw [key] at this
      exact sub_eq_zero.mp this
  · rintro ⟨h1, h2⟩ (⟨b, l⟩ | ⟨a, l⟩)
    · simpa [sysPoly, MvPolynomial.eval₂_sum] using h1 b l
    · rw [key, sub_eq_zero]
      exact h2 a l

theorem projective_eventually_of_finitePresentation : ∀ (J : Type) [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{0}) (c : Cocone F), IsColimit c → ∀ (j : J) (M : Type) [AddCommGroup M]
    [Module (F.obj j) M] [Module.FinitePresentation (F.obj j) M],
    (letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
      Module.Projective c.pt (c.pt ⊗[F.obj j] M)) →
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      letI : Algebra (F.obj j) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra;
      Module.Projective (F.obj k) (F.obj k ⊗[F.obj j] M) := by
  intro J _ _ F c hc j M _ _ _ hproj
  obtain ⟨n, K, e, hK⟩ := Module.FinitePresentation.exists_fin (F.obj j) M
  obtain ⟨m, r, hr⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hK
  let π : (Fin n → F.obj j) →ₗ[F.obj j] M := e.symm.toLinearMap ∘ₗ K.mkQ
  have hπ : Function.Surjective π := e.symm.surjective.comp K.mkQ_surjective
  have hker : Submodule.span (F.obj j) (Set.range r) = LinearMap.ker π := by
    rw [hr, LinearMap.ker_comp, LinearEquiv.ker]
    exact (Submodule.ker_mkQ K).symm
  letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
  obtain ⟨v, w, h1, h2⟩ := GlobalTheory.T.exists_presentation_matrix_of_projective_baseChange (F.obj j) c.pt M n m π hπ r hker hproj
  obtain ⟨k₀, f₀, hk⟩ := GlobalTheory.T.polynomial_system_eventually_solvable_colimit J F c hc j _ _ (sysPoly n m r)
    (Sum.elim (fun p => v p.1 p.2) (fun p => w p.1 p.2))
    ((eval₂_sysPoly_eq_zero_iff _ n m r _).mpr ⟨h1, h2⟩)
  refine ⟨k₀, f₀, fun k f => ?_⟩
  letI : Algebra (F.obj j) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra
  obtain ⟨y, hy⟩ := hk k f
  obtain ⟨h1', h2'⟩ := (eval₂_sysPoly_eq_zero_iff _ n m r y).mp hy
  exact GlobalTheory.T.projective_baseChange_of_presentation_matrix_split (F.obj j) (F.obj k) M n m π hπ r hker (fun a l => y (.inl (a, l)))
    (fun a b => y (.inr (a, b))) h1' h2'

theorem projective_eventually : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (j : J) (A : Type) [CommRing A] [Algebra (F.obj j) A]
    [Algebra.FinitePresentation (F.obj j) A],
    (letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
      Module.Finite c.pt (c.pt ⊗[F.obj j] A) ∧ Module.Projective c.pt (c.pt ⊗[F.obj j] A)) →
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      letI : Algebra (F.obj j) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra;
      Module.Projective (F.obj k) (F.obj k ⊗[F.obj j] A) := by
  intro J _ _ F c hc j A _ _ _ hfp
  obtain ⟨hfin, hproj⟩ := hfp
  letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
  obtain ⟨k₁, g₁, hk₁⟩ := GlobalTheory.T.eventually_finite_baseChange_filtered_colimit J F c hc j A hfin
  letI : Algebra (F.obj j) (F.obj k₁) := (F.map (g₁ ≫ 𝟙 k₁)).hom.toAlgebra
  haveI : Module.Finite (F.obj k₁) (F.obj k₁ ⊗[F.obj j] A) := hk₁ k₁ (𝟙 k₁)
  haveI : Module.FinitePresentation (F.obj k₁) (F.obj k₁ ⊗[F.obj j] A) :=
    Module.FinitePresentation.of_finite_of_finitePresentation _ _
  letI : Algebra (F.obj k₁) c.pt := (c.ι.app k₁).hom.toAlgebra
  haveI : IsScalarTower (F.obj j) (F.obj k₁) c.pt := IsScalarTower.of_algebraMap_eq (fun x => by
    change (c.ι.app j).hom x = (c.ι.app k₁).hom ((F.map (g₁ ≫ 𝟙 k₁)).hom x)
    rw [← c.w (g₁ ≫ 𝟙 k₁)]; rfl)
  haveI : Module.Projective c.pt (c.pt ⊗[F.obj j] A) := hproj
  have hproj₁ : Module.Projective c.pt (c.pt ⊗[F.obj k₁] (F.obj k₁ ⊗[F.obj j] A)) :=
    Module.Projective.of_equiv
      (TensorProduct.AlgebraTensorModule.cancelBaseChange (F.obj j) (F.obj k₁) c.pt c.pt A).symm
  obtain ⟨k₀, g₀, hk₀⟩ :=
    projective_eventually_of_finitePresentation J F c hc k₁ (F.obj k₁ ⊗[F.obj j] A) hproj₁
  refine ⟨k₀, (g₁ ≫ 𝟙 k₁) ≫ g₀, fun k f => ?_⟩
  letI : Algebra (F.obj k₁) (F.obj k) := (F.map (g₀ ≫ f)).hom.toAlgebra
  haveI : Module.Projective (F.obj k) (F.obj k ⊗[F.obj k₁] (F.obj k₁ ⊗[F.obj j] A)) := hk₀ k f
  letI : Algebra (F.obj j) (F.obj k) := (F.map (((g₁ ≫ 𝟙 k₁) ≫ g₀) ≫ f)).hom.toAlgebra
  haveI : IsScalarTower (F.obj j) (F.obj k₁) (F.obj k) := IsScalarTower.of_algebraMap_eq (fun x => by
    change (F.map (((g₁ ≫ 𝟙 k₁) ≫ g₀) ≫ f)).hom x = (F.map (g₀ ≫ f)).hom ((F.map (g₁ ≫ 𝟙 k₁)).hom x)
    rw [Category.assoc, F.map_comp (g₁ ≫ 𝟙 k₁)]; rfl)
  exact Module.Projective.of_equiv
    (TensorProduct.AlgebraTensorModule.cancelBaseChange (F.obj j) (F.obj k₁) (F.obj k) (F.obj k) A)

end GlobalTheory.ProjColim
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveEventuallyFilteredColimitAlgebraStatement
open CategoryTheory Limits TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_eventually_filteredColimit_algebra : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (j : J) (A : Type) [CommRing A] [Algebra (F.obj j) A]
    [Algebra.FinitePresentation (F.obj j) A],
    (letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
      Module.Finite c.pt (c.pt ⊗[F.obj j] A) ∧ Module.Projective c.pt (c.pt ⊗[F.obj j] A)) →
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      letI : Algebra (F.obj j) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra;
      Module.Projective (F.obj k) (F.obj k ⊗[F.obj j] A) := by
  first | (exact @GlobalTheory.ProjColim.projective_eventually) | (exact GlobalTheory.ProjColim.projective_eventually) | (intros; apply GlobalTheory.ProjColim.projective_eventually  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLateSplitOfFilteredColimit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLateSplitOfFilteredColimit
open CategoryTheory Limits TensorProduct GlobalTheory.FiniteColim MvPolynomial

noncomputable section
namespace GlobalTheory.SplitColim

variable {J : Type} [SmallCategory J] [IsFiltered J] {F : J ⥤ CommRingCat.{0}} {c : Cocone F}

theorem eventually_map_eq_zero (hc : IsColimit c) {k : J} (x : F.obj k)
    (hx : (c.ι.app k).hom x = 0) :
    ∃ (k₀ : J) (f₀ : k ⟶ k₀), ∀ (k' : J) (f : k₀ ⟶ k'), (F.map (f₀ ≫ f)).hom x = 0 := by
  have hc' := isColimitOfPreserves (forget _) hc
  have h0 : (c.ι.app k).hom x = (c.ι.app k).hom 0 := by rw [hx, map_zero]
  obtain ⟨k₀, f₀, e⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc' x 0).1 (by exact h0)
  refine ⟨k₀, f₀, fun k' f => ?_⟩
  have e' : (F.map f₀).hom x = 0 := by simpa using e
  rw [Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply, e', map_zero]

theorem eventually_map_eq_zero_finite (hc : IsColimit c) {k : J} {κ : Type} [Fintype κ]
    (x : κ → F.obj k) (hx : ∀ i, (c.ι.app k).hom (x i) = 0) :
    ∃ (k₀ : J) (f₀ : k ⟶ k₀), ∀ (k' : J) (f : k₀ ⟶ k') (i : κ), (F.map (f₀ ≫ f)).hom (x i) = 0 := by
  classical
  suffices H : ∀ S : Finset κ, ∃ (k₀ : J) (f₀ : k ⟶ k₀), ∀ (k' : J) (f : k₀ ⟶ k'),
      ∀ i ∈ S, (F.map (f₀ ≫ f)).hom (x i) = 0 by
    obtain ⟨k₀, f₀, h⟩ := H Finset.univ
    exact ⟨k₀, f₀, fun k' f i => h k' f i (Finset.mem_univ i)⟩
  intro S
  induction S using Finset.induction_on with
  | empty => exact ⟨k, 𝟙 k, fun _ _ i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert a S _ ih =>
    obtain ⟨k₀, f₀, h⟩ := GlobalTheory.TorsorColim.eventually_and
      (fun k' (g : k ⟶ k') => (F.map g).hom (x a) = 0)
      (fun k' (g : k ⟶ k') => ∀ i ∈ S, (F.map g).hom (x i) = 0)
      (eventually_map_eq_zero hc (x a) (hx a)) ih
    refine ⟨k₀, f₀, fun k' f i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact (h k' f).1
    · exact (h k' f).2 i hi

theorem exists_stage_rep (hc : IsColimit c) (k₁ : J) {ι : Type} [Finite ι] (t : ι → c.pt) :
    ∃ (K : J) (h : k₁ ⟶ K) (u : ι → F.obj K), ∀ i, (c.ι.app K).hom (u i) = t i := by
  classical
  have hc' := isColimitOfPreserves (forget _) hc
  choose jx x hx using fun i : ι => Types.jointly_surjective_of_isColimit hc' (t i)
  haveI := Fintype.ofFinite ι
  obtain ⟨K, hK⟩ := IsFiltered.sup_objs_exists (insert k₁ (Finset.univ.image jx))
  obtain ⟨h⟩ := hK (Finset.mem_insert_self k₁ _)
  have hm : ∀ i, Nonempty (jx i ⟶ K) := fun i =>
    hK (Finset.mem_insert_of_mem (Finset.mem_image_of_mem jx (Finset.mem_univ i)))
  refine ⟨K, h, fun i => (F.map (hm i).some).hom (x i), fun i => ?_⟩
  have h1 := hx i
  have h2 := congr(($(c.w (hm i).some)).hom (x i))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h2
  rw [h2]
  exact h1

end GlobalTheory.SplitColim

namespace GlobalTheory.SplitColim

variable {J : Type} [SmallCategory J] [IsFiltered J] {F : J ⥤ CommRingCat.{0}} {c : Cocone F}

theorem exists_late_solution (hc : IsColimit c) (k₁ : J) {ι κ : Type} [Finite ι] [Fintype κ]
    (P : κ → MvPolynomial ι (F.obj k₁)) (t : ι → c.pt)
    (ht : ∀ i, MvPolynomial.eval₂ (c.ι.app k₁).hom t (P i) = 0) :
    ∃ (k₀ : J) (f₀ : k₁ ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k), ∃ u : ι → F.obj k,
      ∀ i, MvPolynomial.eval₂ (F.map (f₀ ≫ f)).hom u (P i) = 0 := by
  obtain ⟨K, h, u, hu⟩ := exists_stage_rep hc k₁ t
  have hx : ∀ i, (c.ι.app K).hom (MvPolynomial.eval₂ (F.map h).hom u (P i)) = 0 := by
    intro i
    rw [MvPolynomial.eval₂_comp_left]
    have e1 : (c.ι.app K).hom.comp (F.map h).hom = (c.ι.app k₁).hom := by
      rw [← CommRingCat.hom_comp, c.w h]
    have e2 : ⇑(c.ι.app K).hom ∘ u = t := funext hu
    rw [e1, e2]; exact ht i
  obtain ⟨k₀, f₀, h0⟩ := eventually_map_eq_zero_finite hc _ hx
  refine ⟨k₀, h ≫ f₀, fun k f => ⟨fun a => (F.map (f₀ ≫ f)).hom (u a), fun i => ?_⟩⟩
  have := h0 k f i
  rw [MvPolynomial.eval₂_comp_left, ← CommRingCat.hom_comp, ← Functor.map_comp] at this
  rw [Category.assoc]
  exact this

theorem exists_late_linear (hc : IsColimit c) (k₁ : J) (M : Type) [AddCommGroup M]
    [Module (F.obj k₁) M] [Module.FinitePresentation (F.obj k₁) M] (m : M) :
    letI : Algebra (F.obj k₁) c.pt := (c.ι.app k₁).hom.toAlgebra
    ∀ σ : M →ₗ[F.obj k₁] c.pt, σ m = 1 →
    ∃ (k₀ : J) (f₀ : k₁ ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      letI : Algebra (F.obj k₁) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra
      ∃ σk : M →ₗ[F.obj k₁] F.obj k, σk m = 1 := by
  letI : Algebra (F.obj k₁) c.pt := (c.ι.app k₁).hom.toAlgebra
  intro σ hσ
  classical
  obtain ⟨s, hs, K, hK⟩ := Module.FinitePresentation.out (R := F.obj k₁) (M := M)
  set π := Finsupp.linearCombination (F.obj k₁) (Subtype.val : s → M) with hπdef
  have hπ : Function.Surjective π := by
    rw [← LinearMap.range_eq_top, hπdef, Finsupp.range_linearCombination, Subtype.range_coe_subtype]
    simpa using hs
  obtain ⟨e, he⟩ := hπ m
  have hπapp : ∀ {T : Type} [AddCommGroup T] [Module (F.obj k₁) T] (g : M →ₗ[F.obj k₁] T)
      (v : s →₀ F.obj k₁), g (π v) = ∑ x, v x • g x := by
    intro T _ _ g v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hπdef, Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (fun i => by simp), map_sum]
    simp
  let lin : (s →₀ F.obj k₁) → MvPolynomial s (F.obj k₁) :=
    fun v => ∑ x, MvPolynomial.C (v x) * MvPolynomial.X x
  have evlin : ∀ {T : Type} [CommRing T] (φ : F.obj k₁ →+* T) (u : s → T) (v : s →₀ F.obj k₁),
      MvPolynomial.eval₂ φ u (lin v) = ∑ x, φ (v x) * u x := by
    intro T _ φ u v; simp [lin, MvPolynomial.eval₂_sum]
  let P : Option K → MvPolynomial s (F.obj k₁) := fun o => o.elim (lin e - 1) (fun v => lin v.1)
  have hKker : ∀ v ∈ K, π v = 0 := fun v hv => by
    have : v ∈ Submodule.span (F.obj k₁) (K : Set (s →₀ F.obj k₁)) := Submodule.subset_span hv
    rw [hK] at this
    exact this
  obtain ⟨k₀, f₀, hsol⟩ := exists_late_solution hc k₁ P (fun x => σ x) (by
    intro o
    cases o with
    | none =>
      change MvPolynomial.eval₂ _ _ (lin e - 1) = 0
      rw [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_one, evlin, sub_eq_zero, ← hσ, ← he, hπapp σ e]
      rfl
    | some v =>
      change MvPolynomial.eval₂ _ _ (lin v.1) = 0
      rw [evlin]
      have := hπapp σ v.1
      rw [hKker v.1 v.2, map_zero] at this
      rw [this]
      rfl)
  refine ⟨k₀, f₀, fun k f => ?_⟩
  letI : Algebra (F.obj k₁) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra
  obtain ⟨u, hu⟩ := hsol k f
  let φ := Finsupp.linearCombination (F.obj k₁) u
  have hφ : ∀ v : s →₀ F.obj k₁, φ v = MvPolynomial.eval₂ (F.map (f₀ ≫ f)).hom u (lin v) := by
    intro v
    rw [evlin, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    · rfl
    · intro i; simp
  have hle : LinearMap.ker π ≤ LinearMap.ker φ := by
    rw [← hK, Submodule.span_le]
    intro v hv
    simp only [SetLike.mem_coe, LinearMap.mem_ker]
    rw [hφ]
    exact hu (some ⟨v, hv⟩)
  refine ⟨((LinearMap.ker π).liftQ φ hle).comp
    (π.quotKerEquivOfSurjective hπ).symm.toLinearMap, ?_⟩
  have hq : (π.quotKerEquivOfSurjective hπ).symm m = Submodule.Quotient.mk e := by
    rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk, he]
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, hq, Submodule.liftQ_apply, hφ]
  have := hu none
  change MvPolynomial.eval₂ _ _ (lin e - 1) = 0 at this
  rw [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_one, sub_eq_zero] at this
  exact this

end GlobalTheory.SplitColim

namespace GlobalTheory.SplitColim

theorem exists_late_split_of_isColimit :
    ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (j : J) (A : Type) [CommRing A] [Algebra (F.obj j) A]
    [Algebra.FinitePresentation (F.obj j) A],
    (letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
      Module.Finite c.pt (c.pt ⊗[F.obj j] A) ∧
        ∃ τ : (c.pt ⊗[F.obj j] A) →ₗ[c.pt] c.pt, τ 1 = 1) →
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      letI : Algebra (F.obj j) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra;
      ∃ τ : (F.obj k ⊗[F.obj j] A) →ₗ[F.obj k] F.obj k, τ 1 = 1 := by
  intro J _ _ F c hc j A _ _ hfp h
  letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
  obtain ⟨hfin, τ, hτ⟩ := h
  have hbase : ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      letI : Algebra (F.obj j) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra;
      Module.Finite (F.obj k) (F.obj k ⊗[F.obj j] A) := by
    classical
    obtain ⟨n, φ, hφ, hfg⟩ := hfp.out
    obtain ⟨s, hs⟩ := hfg
    let rel : s → MvPolynomial (Fin n) (F.obj j) := fun x => x
    have hker : RingHom.ker φ = Ideal.span (Set.range rel) := by
      have : Set.range rel = (s : Set (MvPolynomial (Fin n) (F.obj j))) := by
        ext x; simp [rel]
      rw [this, hs]
      rfl
    letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
    haveI : Algebra.IsIntegral c.pt (c.pt ⊗[F.obj j] A) := Algebra.IsIntegral.of_finite _ _
    have hint : ∀ i, IsIntegral c.pt (bcPres (S := c.pt) φ (X i)) :=
      fun i => Algebra.IsIntegral.isIntegral _
    choose p hpm hp0 using hint
    have hcomb : ∀ i, ∃ G : s → MvPolynomial (Fin n) c.pt,
        ∑ l, G l * MvPolynomial.map (algebraMap (F.obj j) c.pt) (rel l) =
          Polynomial.aeval (X i : MvPolynomial (Fin n) c.pt) (p i) := by
      intro i
      refine exists_comb_of_bcPres_eq_zero φ hφ rel hker _ ?_
      rw [← Polynomial.aeval_algHom_apply, Polynomial.aeval_def]
      exact hp0 i
    choose G hG using hcomb
    let T : Finset c.pt := Finset.univ.biUnion (fun i => (p i).support.image (p i).coeff) ∪
      Finset.univ.biUnion (fun i => Finset.univ.biUnion (fun l => (G i l).coeffs))
    obtain ⟨k₁, f₁, hk₁⟩ := exists_stage_range hc j T
    have hlp : ∀ i, ∃ q : Polynomial (F.obj k₁), q.map (c.ι.app k₁).hom = p i ∧ q.Monic := by
      intro i
      have hl : p i ∈ Polynomial.lifts (c.ι.app k₁).hom := by
        rw [Polynomial.lifts_iff_coeff_lifts]
        intro m
        by_cases hm : m ∈ (p i).support
        · exact hk₁ _ (Finset.mem_union_left _ (Finset.mem_biUnion.2
            ⟨i, Finset.mem_univ _, Finset.mem_image_of_mem _ hm⟩))
        · rw [Polynomial.notMem_support_iff.1 hm]; exact ⟨0, map_zero _⟩
      obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (hpm i)
      exact ⟨q, hq, hqm⟩
    choose q hq hqm using hlp
    have hlG : ∀ i l, ∃ H, MvPolynomial.map (c.ι.app k₁).hom H = G i l := by
      intro i l
      have : G i l ∈ Set.range (MvPolynomial.map (σ := Fin n) (c.ι.app k₁).hom) := by
        rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
        intro y hy
        exact hk₁ _ (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _,
          Finset.mem_biUnion.2 ⟨l, Finset.mem_univ _, hy⟩⟩))
      exact this
    choose H hH using hlG
    let E : Fin n → MvPolynomial (Fin n) (F.obj k₁) := fun i =>
      Polynomial.aeval (X i) (q i) - ∑ l, H i l * MvPolynomial.map (F.map f₁).hom (rel l)
    have hE : ∀ i, MvPolynomial.map (c.ι.app k₁).hom (E i) = 0 := by
      intro i
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [E, map_sub, map_sum, map_mul, map_aeval_X, hq, hH, MvPolynomial.map_map]
      rw [← CommRingCat.hom_comp, c.w f₁, sub_eq_zero, ← hG i]
      rfl
    let U : Finset (F.obj k₁) := Finset.univ.biUnion (fun i => (E i).coeffs)
    obtain ⟨k₂, g₂, hg₂⟩ := exists_stage_zero hc U (by
      intro x hx
      obtain ⟨i, -, hx⟩ := Finset.mem_biUnion.1 hx
      obtain ⟨m, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.1 hx
      have := congrArg (AddMonoidAlgebra.coeff · m) (hE i)
      rwa [MvPolynomial.coeff_map, MvPolynomial.coeff_zero] at this)
    have hE2 : ∀ i, MvPolynomial.map (F.map g₂).hom (E i) = 0 := by
      intro i
      ext m
      rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero]
      by_cases hm : m ∈ (E i).support
      · exact hg₂ _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _,
          MvPolynomial.coeff_mem_coeffs _ (MvPolynomial.mem_support_iff.1 hm)⟩)
      · simp [MvPolynomial.notMem_support_iff.1 hm]
    refine ⟨k₂, f₁ ≫ g₂, fun k f => ?_⟩
    letI : Algebra (F.obj j) (F.obj k) := (F.map ((f₁ ≫ g₂) ≫ f)).hom.toAlgebra
    have hrel : ∀ l, φ (rel l) = 0 := fun l =>
      (RingHom.mem_ker).1 (hker ▸ Ideal.subset_span ⟨l, rfl⟩ : rel l ∈ RingHom.ker φ)
    refine finite_of_relations φ hφ rel hrel (fun i => (q i).map (F.map (g₂ ≫ f)).hom)
      (fun i => (hqm i).map _) (fun i l => MvPolynomial.map (F.map (g₂ ≫ f)).hom (H i l)) (fun i => ?_)
    have halg : algebraMap (F.obj j) (F.obj k) = (F.map (g₂ ≫ f)).hom.comp (F.map f₁).hom := by
      change (F.map ((f₁ ≫ g₂) ≫ f)).hom = _
      rw [Category.assoc, Functor.map_comp, CommRingCat.hom_comp]
    have h3 : MvPolynomial.map (F.map (g₂ ≫ f)).hom (E i) = 0 := by
      rw [Functor.map_comp, CommRingCat.hom_comp, ← MvPolynomial.map_map, hE2, map_zero]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [E, map_sub, map_sum, map_mul, map_aeval_X, MvPolynomial.map_map, sub_eq_zero] at h3
    rw [halg]
    exact h3
  obtain ⟨k₁, f₁, hk₁⟩ := hbase
  have hfin₁ := hk₁ k₁ (𝟙 k₁)
  rw [Category.comp_id] at hfin₁
  letI : Algebra (F.obj j) (F.obj k₁) := (F.map f₁).hom.toAlgebra
  letI : Algebra (F.obj k₁) c.pt := (c.ι.app k₁).hom.toAlgebra
  haveI : IsScalarTower (F.obj j) (F.obj k₁) c.pt := IsScalarTower.of_algebraMap_eq (fun x => by
    change (c.ι.app j).hom x = (c.ι.app k₁).hom ((F.map f₁).hom x)
    rw [← c.w f₁]; rfl)
  haveI : Module.Finite (F.obj k₁) (F.obj k₁ ⊗[F.obj j] A) := hfin₁
  haveI : Module.FinitePresentation (F.obj k₁) (F.obj k₁ ⊗[F.obj j] A) :=
    (Module.FinitePresentation.iff_finitePresentation_of_finite _ _).2 inferInstance
  let g : A →ₗ[F.obj j] c.pt :=
    (τ.restrictScalars (F.obj j)).comp (TensorProduct.mk (F.obj j) c.pt A 1)
  let σ : (F.obj k₁ ⊗[F.obj j] A) →ₗ[F.obj k₁] c.pt := LinearMap.liftBaseChange (F.obj k₁) g
  have hσ : σ 1 = 1 := by
    rw [Algebra.TensorProduct.one_def, LinearMap.liftBaseChange_tmul, one_smul]
    change τ (1 ⊗ₜ 1) = 1
    rw [← Algebra.TensorProduct.one_def]; exact hτ
  obtain ⟨k₀, f₀, hk₀⟩ := exists_late_linear hc k₁ _ (1 : F.obj k₁ ⊗[F.obj j] A) σ hσ
  refine ⟨k₀, f₁ ≫ f₀, fun k f => ?_⟩
  letI : Algebra (F.obj j) (F.obj k) := (F.map ((f₁ ≫ f₀) ≫ f)).hom.toAlgebra
  letI : Algebra (F.obj k₁) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra
  haveI : IsScalarTower (F.obj j) (F.obj k₁) (F.obj k) := IsScalarTower.of_algebraMap_eq (fun x => by
    change (F.map ((f₁ ≫ f₀) ≫ f)).hom x = (F.map (f₀ ≫ f)).hom ((F.map f₁).hom x)
    rw [Category.assoc, Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply])
  obtain ⟨σk, hσk⟩ := hk₀ k f
  refine ⟨LinearMap.liftBaseChange (F.obj k)
    ((σk.restrictScalars (F.obj j)).comp (TensorProduct.mk (F.obj j) (F.obj k₁) A 1)), ?_⟩
  rw [Algebra.TensorProduct.one_def, LinearMap.liftBaseChange_tmul, one_smul]
  change σk (1 ⊗ₜ 1) = 1
  rw [← Algebra.TensorProduct.one_def]; exact hσk

end GlobalTheory.SplitColim
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLateSplitOfFilteredColimitStatement
open CategoryTheory Limits TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_late_split_of_filteredColimit : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (j : J) (A : Type) [CommRing A] [Algebra (F.obj j) A]
    [Algebra.FinitePresentation (F.obj j) A],
    (letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
      Module.Finite c.pt (c.pt ⊗[F.obj j] A) ∧
        ∃ τ : (c.pt ⊗[F.obj j] A) →ₗ[c.pt] c.pt, τ 1 = 1) →
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      letI : Algebra (F.obj j) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra;
      ∃ τ : (F.obj k ⊗[F.obj j] A) →ₗ[F.obj k] F.obj k, τ 1 = 1 := by
  first | (exact @GlobalTheory.SplitColim.exists_late_split_of_isColimit) | (exact GlobalTheory.SplitColim.exists_late_split_of_isColimit) | (intros; apply GlobalTheory.SplitColim.exists_late_split_of_isColimit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePresentationModelOfIsColimitStatement
open CategoryTheory Limits TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finitePresentation_descent_of_isColimit : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (D : Type) [CommRing D] [Algebra c.pt D], Algebra.FinitePresentation c.pt D →
    ∃ (j : J) (A : Type) (_ : CommRing A) (_ : Algebra (F.obj j) A)
      (_ : Algebra.FinitePresentation (F.obj j) A),
      letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
      Nonempty (c.pt ⊗[F.obj j] A ≃ₐ[c.pt] D) := by
  intro J _ _ F c hc D _ _ hD
  classical
  have hc' := isColimitOfPreserves (forget _) hc
  let P := Algebra.Presentation.ofFinitePresentation c.pt D
  obtain ⟨j, hj⟩ : ∃ j, P.coeffs ⊆ Set.range (c.ι.app j).hom := by
    have hfin := P.finite_coeffs
    choose jx x hx using fun y : c.pt ↦ Types.jointly_surjective_of_isColimit hc' y
    obtain ⟨j, hj⟩ := IsFiltered.sup_objs_exists (hfin.toFinset.image jx)
    refine ⟨j, fun y hy ↦ ?_⟩
    obtain ⟨f⟩ := hj (Finset.mem_image_of_mem jx (hfin.mem_toFinset.mpr hy))
    refine ⟨F.map f (x y), ?_⟩
    have hw := congr(($(c.w f)).hom (x y))
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hw
    rw [hw]
    exact hx y
  let : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
  let : Algebra (F.obj j) D := ((algebraMap c.pt D).comp (c.ι.app j).hom).toAlgebra
  have : IsScalarTower (F.obj j) c.pt D := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  have : P.HasCoeffs (F.obj j) := ⟨hj⟩
  exact ⟨j, P.ModelOfHasCoeffs (F.obj j), inferInstance, inferInstance, inferInstance,
    ⟨P.tensorModelOfHasCoeffsEquiv (F.obj j)⟩⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearSplittingUnitFaithfullyFlat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearSplittingUnitFaithfullyFlat
open CategoryTheory Limits TensorProduct

namespace GlobalTheory

theorem unit_splits_of_projective_faithfullyFlat :
    ∀ (R D : Type) [CommRing R] [CommRing D] [Algebra R D], Module.Finite R D →
    Module.Projective R D → Module.FaithfullyFlat R D → ∃ τ : D →ₗ[R] R, τ 1 = 1 := by
  intro R D _ _ _ _ hP hF
  obtain ⟨s, hs⟩ := Module.projective_def'.mp hP
  let ev : (D →ₗ[R] R) →ₗ[R] R :=
    { toFun := fun τ => τ 1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  by_cases hI : LinearMap.range ev = ⊤
  · obtain ⟨τ, hτ⟩ := LinearMap.mem_range.mp (hI ▸ Submodule.mem_top : (1 : R) ∈ LinearMap.range ev)
    exact ⟨τ, hτ⟩
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal (LinearMap.range ev) hI
  exfalso
  have hcoord : ∀ x : D, s 1 x ∈ m := fun x =>
    hIm (LinearMap.mem_range.mpr ⟨Finsupp.lapply x ∘ₗ s, rfl⟩)
  have h1 : (1 : D) ∈ m • (⊤ : Submodule R D) := by
    have : Finsupp.linearCombination R id (s 1) = (1 : D) := LinearMap.congr_fun hs 1
    rw [← this, Finsupp.linearCombination_apply]
    exact Submodule.sum_mem _ fun x _ => Submodule.smul_mem_smul (hcoord x) Submodule.mem_top
  have hmul : ∀ d : D, ∀ y ∈ m • (⊤ : Submodule R D), d * y ∈ m • (⊤ : Submodule R D) := by
    intro d y hy
    refine Submodule.smul_induction_on hy ?_ ?_
    · intro r hr n _
      rw [mul_smul_comm]; exact Submodule.smul_mem_smul hr Submodule.mem_top
    · intro x z hx hz
      rw [mul_add]; exact Submodule.add_mem _ hx hz
  apply Module.FaithfullyFlat.submodule_ne_top (M := D) hm
  rw [eq_top_iff]
  intro d _
  simpa using hmul d 1 h1

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearSplittingUnitFaithfullyFlatStatement
open CategoryTheory Limits TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_splitting_unit_faithfullyFlat : ∀ (R D : Type) [CommRing R] [CommRing D] [Algebra R D], Module.Finite R D →
    Module.Projective R D → Module.FaithfullyFlat R D → ∃ τ : D →ₗ[R] R, τ 1 = 1 := by
  first | (exact @GlobalTheory.unit_splits_of_projective_faithfullyFlat) | (exact GlobalTheory.unit_splits_of_projective_faithfullyFlat) | (intros; apply GlobalTheory.unit_splits_of_projective_faithfullyFlat  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZmodTorsorModelOfFilteredColimit
open CategoryTheory Limits TensorProduct

namespace GlobalTheory.TorsorColim

theorem faithfullyFlat_of_split : ∀ (R D : Type) [CommRing R] [CommRing D] [Algebra R D], Module.Projective R D →
    (∃ τ : D →ₗ[R] R, τ 1 = 1) → Module.FaithfullyFlat R D := by
  intro R D _ _ _ hP ⟨τ, hτ⟩
  haveI : Module.Flat R D := inferInstance
  refine ⟨fun m hm h => ?_⟩
  have h1 : (1 : D) ∈ m • (⊤ : Submodule R D) := by rw [h]; exact Submodule.mem_top
  have h2 : ∀ x ∈ m • (⊤ : Submodule R D), τ x ∈ m := by
    intro x hx
    refine Submodule.smul_induction_on hx (fun r hr d _ => ?_) (fun x y hx hy => ?_)
    · rw [map_smul, smul_eq_mul]; exact m.mul_mem_right _ hr
    · rw [map_add (f := _)]; exact m.add_mem hx hy
  have := h2 1 h1
  rw [hτ] at this
  exact hm.ne_top ((Ideal.eq_top_iff_one m).2 this)

theorem isZModTorsor_of_algEquiv : ∀ (R D D' : Type) [CommRing R] [CommRing D] [CommRing D'] [Algebra R D] [Algebra R D'] (q : ℕ)
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[R] D)) (act' : Multiplicative (ZMod q) →* (D' ≃ₐ[R] D'))
    (e : D ≃ₐ[R] D'), (∀ (g : Multiplicative (ZMod q)) (x : D), e (act g x) = act' g (e x)) →
    GlobalTheory.LocAcyc.IsZModTorsor R D q act → GlobalTheory.LocAcyc.IsZModTorsor R D' q act' := by
  intro R D D' _ _ _ _ _ q act act' e he hD
  obtain ⟨h1, h2, h3, h4⟩ := hD
  have el : D ≃ₗ[R] D' := e.toLinearEquiv
  refine ⟨Module.Finite.equiv el, Module.Projective.of_equiv el, ?_, ?_⟩
  · exact Module.FaithfullyFlat.of_linearEquiv R D el.symm
  · let eT : D ⊗[R] D ≃ₐ[R] D' ⊗[R] D' := Algebra.TensorProduct.congr e e
    let eP : (Multiplicative (ZMod q) → D) ≃ₐ[R] (Multiplicative (ZMod q) → D') :=
      AlgEquiv.piCongrRight (fun _ => e)
    have key : ∀ x, GlobalTheory.TorsorColim.prodMapOf R D' q act' (eT x) = eP (GlobalTheory.TorsorColim.prodMapOf R D q act x) := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        funext g
        simp [eT, eP, he]
      | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]
    have hb : Function.Bijective (GlobalTheory.TorsorColim.prodMapOf R D q act) := h4
    have : ⇑(GlobalTheory.TorsorColim.prodMapOf R D' q act') = eP ∘ (GlobalTheory.TorsorColim.prodMapOf R D q act) ∘ eT.symm := by
      funext y
      simp only [Function.comp_apply]
      rw [← key, AlgEquiv.apply_symm_apply]
    change Function.Bijective (GlobalTheory.TorsorColim.prodMapOf R D' q act')
    rw [this]
    exact eP.bijective.comp (hb.comp eT.symm.bijective)

theorem exists_torsor_model_of_isColimit : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (q : ℕ), 0 < q → ∀ (D : Type) [CommRing D] [Algebra c.pt D]
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[c.pt] D)), GlobalTheory.LocAcyc.IsZModTorsor c.pt D q act →
    ∃ (j : J), letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
    ∃ (Dj : Type) (_ : CommRing Dj) (_ : Algebra (F.obj j) Dj)
      (actj : Multiplicative (ZMod q) →* (Dj ≃ₐ[F.obj j] Dj)),
      GlobalTheory.LocAcyc.IsZModTorsor (F.obj j) Dj q actj ∧
      Nonempty (TensorProduct (F.obj j) c.pt Dj ≃ₐ[c.pt] D) := by
  intro J _ _ F c hc q hq D _ _ act hD
  haveI : Module.Finite c.pt D := hD.1
  haveI : Module.Projective c.pt D := hD.2.1
  haveI : Module.FinitePresentation c.pt D := Module.finitePresentation_of_projective c.pt D
  obtain ⟨j, A, _, _, _, he0⟩ := GlobalTheory.T.exists_finitePresentation_descent_of_isColimit J F c hc D inferInstance
  obtain ⟨k, B, _, _, _, actB, e, he⟩ := GlobalTheory.T.exists_zmod_action_model_of_isColimit_filtered J F c hc q hq j A D act he0
  letI : Algebra (F.obj k) c.pt := (c.ι.app k).hom.toAlgebra
  have hT : GlobalTheory.LocAcyc.IsZModTorsor c.pt (c.pt ⊗[F.obj k] B) q
      (GlobalTheory.TorsorColim.bcAct c.pt actB) := by
    refine GlobalTheory.TorsorColim.isZModTorsor_of_algEquiv c.pt D _ q act _ e.symm (fun g y => ?_) hD
    apply e.injective
    rw [he, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  have h1 := GlobalTheory.T.eventually_finite_baseChange_filtered_colimit J F c hc k B hT.1
  have h2 := GlobalTheory.T.projective_eventually_filteredColimit_algebra J F c hc k B ⟨hT.1, hT.2.1⟩
  have h3 := GlobalTheory.T.exists_late_split_of_filteredColimit J F c hc k B ⟨hT.1, GlobalTheory.T.exists_linear_splitting_unit_faithfullyFlat _ _ hT.1 hT.2.1 hT.2.2.1⟩
  have h4 := GlobalTheory.T.eventually_zmodTorsorGaloisProductMap_bijective_colimit J F c hc q hq k B actB hT
  have h34 := GlobalTheory.TorsorColim.eventually_and (fun (m : J) (h : k ⟶ m) => letI : Algebra (F.obj k) (F.obj m) := (F.map h).hom.toAlgebra; ∃ τ : (F.obj m ⊗[F.obj k] B) →ₗ[F.obj m] F.obj m, τ 1 = 1) (fun (m : J) (h : k ⟶ m) => letI : Algebra (F.obj k) (F.obj m) := (F.map h).hom.toAlgebra; Function.Bijective (GlobalTheory.TorsorColim.prodMapOf (F.obj m) (F.obj m ⊗[F.obj k] B) q (GlobalTheory.TorsorColim.bcAct (F.obj m) actB))) h3 h4
  have h234 := GlobalTheory.TorsorColim.eventually_and (fun (m : J) (h : k ⟶ m) => letI : Algebra (F.obj k) (F.obj m) := (F.map h).hom.toAlgebra; Module.Projective (F.obj m) (F.obj m ⊗[F.obj k] B)) (fun (m : J) (h : k ⟶ m) => letI : Algebra (F.obj k) (F.obj m) := (F.map h).hom.toAlgebra; (∃ τ : (F.obj m ⊗[F.obj k] B) →ₗ[F.obj m] F.obj m, τ 1 = 1) ∧ Function.Bijective (GlobalTheory.TorsorColim.prodMapOf (F.obj m) (F.obj m ⊗[F.obj k] B) q (GlobalTheory.TorsorColim.bcAct (F.obj m) actB))) h2 h34
  obtain ⟨m, f₀, hm⟩ := GlobalTheory.TorsorColim.eventually_and (fun (m : J) (h : k ⟶ m) => letI : Algebra (F.obj k) (F.obj m) := (F.map h).hom.toAlgebra; Module.Finite (F.obj m) (F.obj m ⊗[F.obj k] B)) (fun (m : J) (h : k ⟶ m) => letI : Algebra (F.obj k) (F.obj m) := (F.map h).hom.toAlgebra; Module.Projective (F.obj m) (F.obj m ⊗[F.obj k] B) ∧ (∃ τ : (F.obj m ⊗[F.obj k] B) →ₗ[F.obj m] F.obj m, τ 1 = 1) ∧ Function.Bijective (GlobalTheory.TorsorColim.prodMapOf (F.obj m) (F.obj m ⊗[F.obj k] B) q (GlobalTheory.TorsorColim.bcAct (F.obj m) actB))) h1 h234
  obtain ⟨i1, i2, ⟨τ, hτ⟩, i4⟩ := hm m (𝟙 m)
  refine ⟨m, ?_⟩
  letI : Algebra (F.obj k) (F.obj m) := (F.map (f₀ ≫ 𝟙 m)).hom.toAlgebra
  letI : Algebra (F.obj m) c.pt := (c.ι.app m).hom.toAlgebra
  haveI : IsScalarTower (F.obj k) (F.obj m) c.pt := IsScalarTower.of_algebraMap_eq (fun x => by
    change (c.ι.app k).hom x = (c.ι.app m).hom ((F.map (f₀ ≫ 𝟙 m)).hom x)
    rw [← c.w (f₀ ≫ 𝟙 m)]
    rfl)
  exact ⟨F.obj m ⊗[F.obj k] B, inferInstance, inferInstance, GlobalTheory.TorsorColim.bcAct (F.obj m) actB,
    ⟨i1, i2, GlobalTheory.TorsorColim.faithfullyFlat_of_split _ _ i2 ⟨τ, hτ⟩, i4⟩,
    ⟨(Algebra.TensorProduct.cancelBaseChange (F.obj k) (F.obj m) c.pt c.pt B).trans e⟩⟩

end GlobalTheory.TorsorColim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZmodTorsorModelOfFilteredColimitStatement
open CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_zmodTorsor_model_of_filtered_colimit : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (q : ℕ), 0 < q → ∀ (D : Type) [CommRing D] [Algebra c.pt D]
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[c.pt] D)), GlobalTheory.LocAcyc.IsZModTorsor c.pt D q act →
    ∃ (j : J), letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
    ∃ (Dj : Type) (_ : CommRing Dj) (_ : Algebra (F.obj j) Dj)
      (actj : Multiplicative (ZMod q) →* (Dj ≃ₐ[F.obj j] Dj)),
      GlobalTheory.LocAcyc.IsZModTorsor (F.obj j) Dj q actj ∧
      Nonempty (TensorProduct (F.obj j) c.pt Dj ≃ₐ[c.pt] D) := by
  first | (exact @GlobalTheory.TorsorColim.exists_torsor_model_of_isColimit) | (exact GlobalTheory.TorsorColim.exists_torsor_model_of_isColimit) | (intros; apply GlobalTheory.TorsorColim.exists_torsor_model_of_isColimit  <;> assumption)
end
