module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.GlNegOp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.MsetSep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.InfinitesimalCharacterPullback.HasInfCharPullSub

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.DualIff
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

namespace UpperTheory.V.AlgRepEndIrreducible.QuantumDeterminantDual

private theorem map_qdet {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) {n : ℕ}
    (X : Fin n → Fin n → A) (u : ℂ) : f (Formalism.REAL.qdet X u) = Formalism.REAL.qdet (fun i j => f (X i j)) u := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, Formalism.REAL.Tm, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn,
    Function.comp_def, map_add, apply_ite f, AlgHom.commutes, map_zero]

private theorem qdet_negT {d n : ℕ} (X : Fin n → Fin n → Matrix (Fin d) (Fin d) ℂ) (h : Formalism.REAL.GlRel X) (u : ℂ) :
    Formalism.REAL.qdet (fun i j => -(X i j)ᵀ) (u + ((n : ℂ) - 1) / 2) =
      (-1 : ℂ) ^ n • (Formalism.REAL.qdet X (-u + ((n : ℂ) - 1) / 2))ᵀ := by
  have h1 := map_qdet (Matrix.transposeAlgEquiv (Fin d) ℂ ℂ).toAlgHom (fun i j => -(X i j)ᵀ) (u + ((n : ℂ) - 1) / 2)
  have h2 := (glNegOp _ n X h).2 (u + ((n : ℂ) - 1) / 2)
  have e : (fun i j => (Matrix.transposeAlgEquiv (Fin d) ℂ ℂ).toAlgHom (-(X i j)ᵀ)) =
      fun i j => -MulOpposite.op (X i j) := by
    funext i j
    simp
  have e' : (n : ℂ) - 1 - (u + ((n : ℂ) - 1) / 2) = -u + ((n : ℂ) - 1) / 2 := by ring
  rw [e, h2, e'] at h1
  have h3 : (Formalism.REAL.qdet (fun i j => -(X i j)ᵀ) (u + ((n : ℂ) - 1) / 2))ᵀ =
      (-1 : ℂ) ^ n • Formalism.REAL.qdet X (-u + ((n : ℂ) - 1) / 2) := MulOpposite.op_injective h1
  rw [← Matrix.transpose_smul, ← h3, Matrix.transpose_transpose]

private theorem prod_neg (m : Multiset ℂ) (u : ℂ) :
    ((m.map Neg.neg).map (-u + ·)).prod = (-1) ^ Multiset.card m * (m.map (u + ·)).prod := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, ih]
    ring

end UpperTheory.V.AlgRepEndIrreducible.QuantumDeterminantDual

theorem UpperTheory.V.AlgRepEndIrreducible.dualIff :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (τ : E →+* ℂ) (m : Multiset ℂ),
      UpperTheory.V.Af.AlgInfChar Ξ τ (m.map Neg.neg) ↔ GlobalTheory.WignerGL.HasDualInfChar Ξ τ m := by
  intro E _ _ _ a Ξ τ m
  have hR : Formalism.REAL.GlRel (eL Ξ.dmat τ) := (eLRel E a _ Ξ.dmat (GlobalTheory.AlgInfChar.dmat_bracket Ξ)).1 τ
  have hd : GlobalTheory.WignerGL.dualE Ξ τ = fun i j => -(eL Ξ.dmat τ i j)ᵀ := by
    funext i j
    exact dualE_eq Ξ τ i j
  have hs : (-1 : ℂ) ^ a * (-1 : ℂ) ^ a = 1 := by rw [← mul_pow]; simp
  change (Multiset.card (m.map Neg.neg) = a ∧ ∀ u : ℂ, Formalism.REAL.qdet (eL Ξ.dmat τ) (u + ((a : ℂ) - 1) / 2) =
    ((m.map Neg.neg).map (u + ·)).prod • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ)) ↔ _
  unfold GlobalTheory.WignerGL.HasDualInfChar
  rw [Multiset.card_map, hd]
  refine and_congr_right fun hm => ⟨fun h u => ?_, fun h u => ?_⟩
  · rw [QuantumDeterminantDual.qdet_negT _ hR, h, QuantumDeterminantDual.prod_neg, hm, Matrix.transpose_smul, Matrix.transpose_one, smul_smul,
      ← mul_assoc, hs, one_mul]
  · have h1 := congrArg (fun M => (-1 : ℂ) ^ a • Mᵀ) (h (-u))
    have h2 := QuantumDeterminantDual.prod_neg m (-u)
    simp only [QuantumDeterminantDual.qdet_negT _ hR, Matrix.transpose_smul, Matrix.transpose_transpose, Matrix.transpose_one,
      smul_smul, hs, one_smul, neg_neg] at h1
    rw [neg_neg, hm] at h2
    rw [h1, h2]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.LieDecomp
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private theorem scalarDecomp {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : Type} [AddCommGroup N]
    [Module ℂ N] [Module ℝ N] [IsScalarTower ℝ ℂ N] (l : Cinf E →ₗ[ℝ] N) (x : Cinf E) :
    l x = ∑ τ : E →+* ℂ, coord τ x • ((1 / 2 : ℂ) • (l (atEmb τ 1) - Complex.I • l (atEmb τ Complex.I))) := by
  classical
  have e : x = ∑ w : InfinitePlace E, atEmb w.embedding (x w) := by
    conv_lhs => rw [← Finset.univ_sum_single x]
    refine Finset.sum_congr rfl fun w _ => ?_
    unfold atEmb
    rw [if_pos (by rw [InfinitePlace.mk_embedding])]
    congr 1 <;> simp
  rw [← Finset.sum_fiberwise Finset.univ InfinitePlace.mk]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [e, map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := fun h =>
    InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)
      (InfinitePlace.isReal_iff.2 (ComplexEmbedding.isReal_iff.2 h.symm))
  have hf : (Finset.univ.filter fun τ : E →+* ℂ => InfinitePlace.mk τ = w) =
      {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      have h' : InfinitePlace.mk w.embedding = InfinitePlace.mk τ := by rw [InfinitePlace.mk_embedding, h]
      exact (InfinitePlace.mk_eq_iff.1 h').imp Eq.symm Eq.symm
    · rintro (rfl | rfl)
      · exact InfinitePlace.mk_embedding w
      · rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
  have e' : atEmb w.embedding (-Complex.I) = -atEmb w.embedding Complex.I := by
    rw [atEmb_eq]; simp
  rw [hf, Finset.sum_pair hne, UpperTheory.V.FieldIso.coord_conj, UpperTheory.V.FieldIso.coord_embedding, atEmb_eq _ (x w),
    map_add, map_smul, map_smul, ← algebraMap_smul ℂ (x w).re, ← algebraMap_smul ℂ (x w).im]
  simp only [atEmb_conj, map_one, Complex.conj_I, e', map_neg]
  have h1 : algebraMap ℝ ℂ (x w).re = (x w + starRingEnd ℂ (x w)) / 2 := by
    rw [Complex.add_conj]; simp
  have h2 : algebraMap ℝ ℂ (x w).im = -(x w - starRingEnd ℂ (x w)) * Complex.I / 2 := by
    rw [Complex.sub_conj]; push_cast
    change ((x w).im : ℂ) = _
    linear_combination ((x w).im : ℂ) * Complex.I_mul_I
  rw [h1, h2]
  match_scalars <;> ring

theorem UpperTheory.V.AlgRepEndIrreducible.lieDecomp :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (N : Type) [AddCommGroup N] [Module ℂ N] [Module ℝ N] [IsScalarTower ℝ ℂ N] (L : Lie E a →ₗ[ℝ] N) (X : Matrix (Fin a) (Fin a) (Cinf E)),
      L (toL X) = ∑ τ : E →+* ℂ, hol τ L (X.map (coord τ)) := by
  intro E _ _ _ a N _ _ _ _ L X
  let L' : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] N := L
  change L' X = _
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, hol_apply, Matrix.map_apply]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact scalarDecomp (L' ∘ₗ Matrix.singleLinearMap ℝ i j) (X i j)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.ExpGen
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private theorem exp_map_eval {ι : Type} [Fintype ι] {a : ℕ} (X : Matrix (Fin a) (Fin a) (ι → ℂ)) (w : ι) :
    (NormedSpace.exp X).map (fun x => x w) = NormedSpace.exp (X.map fun x => x w) := by
  open scoped Matrix.Norms.Operator in
  exact NormedSpace.map_exp ((Pi.evalRingHom (fun _ : ι => ℂ) w).mapMatrix (m := Fin a))
    (Continuous.matrix_map continuous_id (continuous_apply w)) X

private theorem gen_pi {ι : Type} [Fintype ι] {a : ℕ} (H : Submonoid (Matrix (Fin a) (Fin a) (ι → ℂ)))
    (hH : ∀ X, NormedSpace.exp X ∈ H) (y : Matrix (Fin a) (Fin a) (ι → ℂ)) (hy : IsUnit y) : y ∈ H := by
  classical
  let e : Matrix (Fin a) (Fin a) (ι → ℂ) ≃+* (ι → Matrix (Fin a) (Fin a) ℂ) :=
    Matrix.piRingEquiv (β := fun _ : ι => ℂ)
  have he : ∀ X w, e X w = X.map (fun x => x w) := fun _ _ => rfl
  let H' : Submonoid (ι → Matrix (Fin a) (Fin a) ℂ) := H.comap (e.symm : _ →* _)
  have h1 : ∀ (w : ι) (g : Matrix (Fin a) (Fin a) ℂ), g.det ≠ 0 → Pi.mulSingle w g ∈ H' := by
    intro w g hg
    refine UpperTheory.V.AlgRepEndIrreducible.expGenC a (H'.comap (MonoidHom.mulSingle (fun _ : ι => Matrix (Fin a) (Fin a) ℂ) w)) ?_ g hg
    intro X
    change e.symm (Pi.mulSingle w (NormedSpace.exp X)) ∈ H
    have : e.symm (Pi.mulSingle w (NormedSpace.exp X)) = NormedSpace.exp (e.symm (Pi.single w X)) := by
      rw [RingEquiv.symm_apply_eq]
      funext v
      rw [he, exp_map_eval, ← he, RingEquiv.apply_symm_apply]
      by_cases hv : v = w
      · subst hv
        simp
      · simp [hv]
    rw [this]
    exact hH _
  have h2 : ∀ w, (e y w).det ≠ 0 := by
    intro w
    have : IsUnit (e y w) := (hy.map e).map (Pi.evalRingHom (fun _ : ι => Matrix (Fin a) (Fin a) ℂ) w)
    exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero
  have h3 : ∀ s : Finset ι, s.piecewise (e y) 1 ∈ H' := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using H'.one_mem
    | insert w s hw ih =>
      have : (insert w s).piecewise (e y) 1 = Pi.mulSingle w (e y w) * s.piecewise (e y) 1 := by
        funext v
        by_cases hv : v = w
        · subst hv
          simp [Finset.piecewise, hw]
        · simp [Finset.piecewise, hv]
      rw [this]
      exact H'.mul_mem (h1 w _ (h2 w)) ih
  have h4 := h3 Finset.univ
  rw [Finset.piecewise_univ] at h4
  have h5 : e.symm (e y) ∈ H := h4
  simpa using h5

theorem UpperTheory.V.AlgRepEndIrreducible.expGen :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (H : Submonoid (GL (Fin a) (Cinf E))),
      (∀ (X : Matrix (Fin a) (Fin a) (Cinf E)) (y : GL (Fin a) (Cinf E)), y.val = NormedSpace.exp X → y ∈ H) → ∀ y, y ∈ H := by
  intro E _ _ _ a H hH y
  have h : y.val ∈ H.map (Units.coeHom _) := by
    refine gen_pi (ι := InfinitePlace E) (H.map (Units.coeHom _)) ?_ y.val y.isUnit
    intro X
    obtain ⟨u, hu⟩ := Matrix.isUnit_exp X
    exact ⟨u, hH X u hu, hu⟩
  obtain ⟨u, hu, h'⟩ := h
  have : u = y := Units.ext h'
  exact this ▸ hu
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.InfAbs
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private theorem multi_cont {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {q : ℕ}
    (μ : (Fin q → V) →ₘₗ[ℝ] ℂ) : Continuous μ := by
  let b := Module.finBasis ℝ V
  have e : (μ : (Fin q → V) → ℂ) = fun x => ∑ r : Fin q → Fin (Module.finrank ℝ V),
      (∏ i, b.coord (r i) (x i)) • μ fun i => b (r i) := by
    funext x
    have h : x = fun i => ∑ j, b.coord j (x i) • b j := funext fun i => (b.sum_repr (x i)).symm
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [h, μ.map_sum]
    simp only [μ.map_smul_univ, RingHom.id_apply]
  rw [e]
  refine continuous_finsetSum _ fun r _ => Continuous.fun_smul ?_ continuous_const
  exact continuous_finsetProd _ fun i _ =>
    (b.coord (r i)).continuous_of_finiteDimensional.comp (continuous_apply i)

private theorem multi_deriv {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {q : ℕ}
    (μ : (Fin q → V) →ₘₗ[ℝ] ℂ) (c : ℝ → Fin q → V) (c' : Fin q → V)
    (hc : ∀ i, HasDerivAt (fun t => c t i) (c' i) 0) :
    HasDerivAt (fun t => μ (c t)) (∑ i, μ (Function.update (c 0) i (c' i))) 0 := by
  let ν : ContinuousMultilinearMap ℝ (fun _ : Fin q => V) ℂ := ⟨μ, multi_cont μ⟩
  have h := (ν.hasFDerivAt (c 0)).comp_hasDerivAt (0 : ℝ) (hasDerivAt_pi.2 hc)
  rw [ContinuousMultilinearMap.linearDeriv_apply] at h
  exact h

private theorem hp_herm {E : Type} [Field E] {a : ℕ} (Y : Herm E a) : hp (toL Y.1) = Y := by
  apply Subtype.ext
  have h : star Y.1 = Y.1 := Y.2
  rw [hp_val, h, ← two_smul ℝ, smul_smul]
  norm_num

private theorem conj_deriv {E : Type} [Field E] [NumberField E] {a : ℕ} (k : ℝ → Kinf E a)
    (Z : Matrix (Fin a) (Fin a) (Cinf E)) (hZ : star Z = -Z) (h0 : k 0 = 1)
    (hk : HasDerivAt (fun t => toL (k t).1) (toL Z) 0) (Y : Matrix (Fin a) (Fin a) (Cinf E)) :
    HasDerivAt (fun t => toL ((k t).1 * Y * star (k t).1)) (toL (Z * Y - Y * Z)) 0 := by
  open scoped Matrix.Norms.Operator in
  have h1 : HasDerivAt (fun t => (k t).1) Z 0 := hk
  open scoped Matrix.Norms.Operator in
  have h2 : HasDerivAt (fun t => star (k t).1) (star Z) 0 :=
    (hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => (hasDerivAt_pi.1 (hasDerivAt_pi.1 hk j) i).star :
      HasDerivAt (fun t => toL (star (k t).1)) (toL (star Z)) 0)
  open scoped Matrix.Norms.Operator in
  have h := (h1.mul_const Y).mul h2
  simp only [h0, hZ, OneMemClass.coe_one, star_one, mul_one, one_mul, mul_neg, ← sub_eq_add_neg] at h
  exact h

theorem UpperTheory.V.AlgRepEndIrreducible.infAbs :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] (κ : Kinf E a → Module.End ℂ M) (L : Lie E a →ₗ[ℝ] Module.End ℂ M),
      SepDer κ L → ∀ (q : ℕ) (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M), IsCochain κ ω → InfEq L ω := by
  intro E _ _ _ a M _ _ _ _ κ L hS q ω hω Z hZ Y
  obtain ⟨k, h0, hk⟩ := kCurve E a Z hZ
  rw [← sub_eq_zero]
  by_contra hne
  obtain ⟨l, hl, hd⟩ := hS k Z h0 hk _ hne
  apply hl
  let μ : (Fin q → Lie E a) →ₘₗ[ℝ] ℂ :=
    (l.restrictScalars ℝ).compMultilinearMap (ω.toMultilinearMap.compLinearMap fun _ => hp)
  have hμ : ∀ X : Fin q → Herm E a, μ (fun i => toL (X i).1) = l (ω X) := fun X => by
    change l (ω fun i => hp (toL (X i).1)) = _
    simp only [hp_herm]
  have h1 := multi_deriv μ (fun t i => toL (adHerm (k t) (Y i)).1) (fun i => toL (brH Z hZ (Y i)).1)
    (fun i => conj_deriv k Z hZ h0 hk (Y i).1)
  have h2 : ∀ t, μ (fun i => toL (adHerm (k t) (Y i)).1) = l (κ (k t) (ω Y)) := fun t => by
    rw [hμ, hω]
  simp only [h2] at h1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, (hd (ω Y)).unique h1, map_sum, sub_eq_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hμ]
  congr 1
  funext j
  by_cases h : j = i
  · subst h; simp only [Function.update_self]
  · simp only [Function.update_of_ne h, h0, adHerm, OneMemClass.coe_one, star_one, mul_one, one_mul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.HolMul
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private theorem atEmb_add' {E : Type} [Field E] (τ : E →+* ℂ) (z w : ℂ) :
    atEmb τ (z + w) = atEmb τ z + atEmb τ w := by
  rw [atEmb_eq τ (z + w), atEmb_eq τ z, atEmb_eq τ w, Complex.add_re, Complex.add_im, add_smul, add_smul]
  abel

private noncomputable def atEmbHom {E : Type} [Field E] (τ : E →+* ℂ) : ℂ →+ Cinf E :=
  AddMonoidHom.mk' (atEmb τ) (atEmb_add' τ)

private theorem mul_atEmb_map {E : Type} [Field E] {a : ℕ} (τ : E →+* ℂ)
    (p : Matrix (Fin a) (Fin a) (Cinf E)) (x : Matrix (Fin a) (Fin a) ℂ) :
    p * x.map (atEmb τ) = (p.map (coord τ) * x).map (atEmb τ) := by
  ext1 i j
  simp only [Matrix.mul_apply, Matrix.map_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [show atEmb τ (∑ k, coord τ (p i k) * x k j) = ∑ k, atEmb τ (coord τ (p i k) * x k j) from
    map_sum (atEmbHom τ) _ _]
  exact Finset.sum_congr rfl fun k _ => GlobalTheory.CapAdInv.mul_atEmb _ _ _

private theorem atEmb_map_mul {E : Type} [Field E] {a : ℕ} (τ : E →+* ℂ)
    (p : Matrix (Fin a) (Fin a) (Cinf E)) (x : Matrix (Fin a) (Fin a) ℂ) :
    x.map (atEmb τ) * p = (x * p.map (coord τ)).map (atEmb τ) := by
  ext1 i j
  simp only [Matrix.mul_apply, Matrix.map_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [show atEmb τ (∑ k, x i k * coord τ (p k j)) = ∑ k, atEmb τ (x i k * coord τ (p k j)) from
    map_sum (atEmbHom τ) _ _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm, mul_comm (x i k)]
  exact GlobalTheory.CapAdInv.mul_atEmb _ _ _

private theorem atEmb_map_sub {E : Type} [Field E] {a : ℕ} (τ : E →+* ℂ)
    (x y : Matrix (Fin a) (Fin a) ℂ) :
    (x - y).map (atEmb τ) = x.map (atEmb τ) - y.map (atEmb τ) := by
  ext1 i j
  simp only [Matrix.sub_apply, Matrix.map_apply]
  exact map_sub (atEmbHom τ) _ _

theorem UpperTheory.V.AlgRepEndIrreducible.holMul :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (N : Type) [AddCommGroup N] [Module ℂ N] [Module ℝ N] [IsScalarTower ℝ ℂ N] (τ : E →+* ℂ) (L L' : Lie E a →ₗ[ℝ] N),
      (∀ p q : Matrix (Fin a) (Fin a) (Cinf E), (∀ X, L' (toL X) = L (toL (p * X * q))) →
        ∀ x, hol τ L' x = hol τ L (p.map (coord τ) * x * q.map (coord τ))) ∧
      ∀ Y : Matrix (Fin a) (Fin a) (Cinf E), (∀ X, L' (toL X) = L (toL (Y * X - X * Y))) →
        ∀ x, hol τ L' x = hol τ L (Y.map (coord τ) * x - x * Y.map (coord τ)) := by
  intro E _ _ _ a N _ _ _ _ τ L L'
  refine ⟨fun p q h x => ?_, fun Y h x => ?_⟩
  · rw [holEq, holEq, h, h, mul_atEmb_map, atEmb_map_mul, mul_atEmb_map, atEmb_map_mul, Matrix.mul_smul, Matrix.smul_mul]
  · rw [holEq, holEq, h, h, mul_atEmb_map, atEmb_map_mul, mul_atEmb_map, atEmb_map_mul, Matrix.mul_smul, Matrix.smul_mul,
      ← atEmb_map_sub, ← atEmb_map_sub, ← smul_sub]
end
