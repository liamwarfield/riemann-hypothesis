module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankJointEigenspaceAddConjEqMul
public import Development.AutomorphicArithmetic.RealSpanData.RealData

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceRestrictScalarsField
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.QTrace

set_option autoImplicit false in
private lemma trace_restrictScalars_rat {F W : Type} [Field F] [NumberField F] [AddCommGroup W]
    [Module F W] [Module ℚ W] [IsScalarTower ℚ F W] [FiniteDimensional F W] (f : W →ₗ[F] W) :
    LinearMap.trace ℚ W (f.restrictScalars ℚ) = Algebra.trace ℚ F (LinearMap.trace F W f) := by
  classical
  let b := Module.finBasis ℚ F
  let d := Module.finBasis F W
  set_option synthInstance.maxHeartbeats 100000 in
    rw [LinearMap.trace_eq_matrix_trace ℚ (b.smulTower d), LinearMap.trace_eq_matrix_trace F d,
    Matrix.trace, Matrix.trace, map_sum, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [LinearMap.toMatrix_apply, Module.Basis.smulTower_apply, Module.Basis.smulTower_repr,
    Algebra.leftMulMatrix_eq_repr_mul, mul_comm]

set_option autoImplicit false in
private lemma trace_mulLeft_matrix (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) :
    LinearMap.trace ℂ (Matrix (Fin n) (Fin n) ℂ) (LinearMap.mulLeft ℂ M) = n * M.trace := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Matrix.stdBasis ℂ (Fin n) (Fin n))]
  simp only [Matrix.trace, LinearMap.toMatrix_apply, Matrix.diag, Fintype.sum_prod_type]
  have key : ∀ i j, (Matrix.stdBasis ℂ (Fin n) (Fin n)).repr
      (LinearMap.mulLeft ℂ M (Matrix.stdBasis ℂ (Fin n) (Fin n) (i, j))) (i, j) = M i i := by
    intro i j
    rw [Matrix.stdBasis_eq_single]
    simp [Matrix.stdBasis]
  simp only [key]
  simp [Finset.sum_const, Finset.card_univ, Finset.mul_sum]

set_option autoImplicit false in
private lemma embedding_trace_mulLeft_eq_mul_trace {F A : Type} [Field F] [Ring A] [Algebra F A]
    [FiniteDimensional F A] [Algebra.IsCentral F A] [IsSimpleRing A] (n : ℕ)
    (hn : Module.finrank F A = n ^ 2) (σ : F →+* ℂ) (φ : A →+* Matrix (Fin n) (Fin n) ℂ)
    (hφ : ∀ x : F, φ (algebraMap F A x) = Matrix.scalar (Fin n) (σ x)) (c : A) :
    σ (LinearMap.trace F A (LinearMap.mulLeft F c)) = n * (φ c).trace := by
  letI : Algebra F ℂ := σ.toAlgebra
  have hn0 : n ≠ 0 := by
    rintro rfl
    have : 0 < Module.finrank F A := Module.finrank_pos
    simp [hn] at this
  haveI : NeZero n := ⟨hn0⟩
  let φF : A →ₐ[F] Matrix (Fin n) (Fin n) ℂ :=
    { φ with commutes' := fun x => (hφ x).trans rfl }
  let ι : ℂ →ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ := Algebra.ofId ℂ _
  let G : TensorProduct F ℂ A →ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    Algebra.TensorProduct.lift ι φF (fun z a => Algebra.commute_algebraMap_left z _)
  let H : TensorProduct F A ℂ →ₐ[F] Matrix (Fin n) (Fin n) ℂ :=
    Algebra.TensorProduct.lift φF (ι.restrictScalars F)
      (fun a z => (Algebra.commute_algebraMap_left z _).symm)
  have hH : Function.Injective H := by
    rw [← TwoSidedIdeal.ker_eq_bot]
    by_contra hne
    obtain ⟨b, hb, hmem⟩ := _root_.GroundTheory.Brauer.exists_one_tmul_mem_of_ne_bot _ hne
    rw [TwoSidedIdeal.mem_ker] at hmem
    have : algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) b = 0 := by
      have h1 : H (1 ⊗ₜ[F] b) = φF 1 * (ι.restrictScalars F) b :=
        Algebra.TensorProduct.lift_tmul _ _ _ _ _
      rw [h1, map_one, one_mul] at hmem
      exact hmem
    exact hb ((algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ)).injective (this.trans (map_zero _).symm))
  have hGH : ∀ x, G x = H (TensorProduct.comm F ℂ A x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul z a =>
      rw [TensorProduct.comm_tmul]
      simp only [G, H, Algebra.TensorProduct.lift_tmul, AlgHom.restrictScalars_apply, ι, Algebra.ofId_apply]
      exact Algebra.commutes z _
    | add x y hx hy => simp [map_add (f := _), hx, hy]
  have hG : Function.Injective G := by
    intro x y hxy
    rw [hGH, hGH] at hxy
    exact (TensorProduct.comm F ℂ A).injective (hH hxy)
  have hdim : Module.finrank ℂ (TensorProduct F ℂ A) = Module.finrank ℂ (Matrix (Fin n) (Fin n) ℂ) := by
    rw [_root_.GroundTheory.Brauer.finrank_baseChange_eq, hn, Module.finrank_matrix]
    simp [sq]
  haveI : FiniteDimensional ℂ (TensorProduct F ℂ A) :=
    Module.finite_of_finrank_pos (by rw [hdim]; simp [Module.finrank_matrix, Nat.pos_of_ne_zero hn0])
  let e : TensorProduct F ℂ A ≃ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    LinearEquiv.ofBijective G.toLinearMap
      ⟨hG, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hG⟩
  have hconj : e.conj ((LinearMap.mulLeft F c).baseChange ℂ) = LinearMap.mulLeft ℂ (φ c) := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    show G _ = φ c * G x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul z a =>
      rw [LinearMap.baseChange_tmul]
      simp only [G, Algebra.TensorProduct.lift_tmul, ι, Algebra.ofId_apply, LinearMap.mulLeft_apply]
      show algebraMap ℂ _ z * φ (c * a) = φ c * (algebraMap ℂ _ z * φ a)
      rw [map_mul, ← mul_assoc, ← mul_assoc, Algebra.commutes z (φ c)]
    | add x y hx hy => simp [map_add (f := _), hx, hy, mul_add]
  rw [← trace_mulLeft_matrix, ← hconj, LinearMap.trace_conj', LinearMap.trace_baseChange]
  rfl

set_option autoImplicit false in
private lemma trace_pi_comp_proj {N : Type} [AddCommGroup N] [Module ℚ N] [FiniteDimensional ℚ N] (m : ℕ)
    (f : N →ₗ[ℚ] N) :
    LinearMap.trace ℚ (Fin m → N) (LinearMap.pi fun i => f ∘ₗ LinearMap.proj i) =
      m * LinearMap.trace ℚ N f := by
  let e := TensorProduct.piScalarRight ℚ ℚ N (Fin m)
  have h : e.symm.conj (LinearMap.pi fun i => f ∘ₗ LinearMap.proj i) = TensorProduct.map f LinearMap.id := by
    apply TensorProduct.ext'
    intro x y
    have hx : (LinearMap.pi fun i => f ∘ₗ LinearMap.proj i) (e (x ⊗ₜ y)) = e (f x ⊗ₜ y) := by
      ext i
      simp [e, TensorProduct.piScalarRight_apply]
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_symm, hx,
      LinearEquiv.symm_apply_apply, TensorProduct.map_tmul, LinearMap.id_apply]
  rw [← LinearMap.trace_conj' _ e.symm, h, LinearMap.trace_tensorProduct', LinearMap.trace_id]
  simp [mul_comm]

set_option autoImplicit false in
private lemma trace_and_finrank_of_linearEquiv_pi {A M S : Type} [Ring A] [Algebra ℚ A] [AddCommGroup M]
    [Module A M] [Module ℚ M] [IsScalarTower ℚ A M] [AddCommGroup S] [Module A S] [Module ℚ S]
    [IsScalarTower ℚ A S] [FiniteDimensional ℚ S] (k : ℕ) (e : M ≃ₗ[A] (Fin k → S)) (c : A) :
    LinearMap.trace ℚ M (DistribSMul.toLinearMap ℚ M c) =
        k * LinearMap.trace ℚ S (DistribSMul.toLinearMap ℚ S c) ∧
      Module.finrank ℚ M = k * Module.finrank ℚ S := by
  let e' : M ≃ₗ[ℚ] (Fin k → S) := e.restrictScalars ℚ
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.trace_conj' _ e', ← trace_pi_comp_proj]
    congr 1
    refine LinearMap.ext fun v => funext fun x => ?_
    show e (c • e.symm v) x = c • v x
    rw [map_smul, LinearEquiv.apply_symm_apply]
    rfl
  · rw [e'.finrank_eq, Module.finrank_pi_fintype]
    simp

set_option autoImplicit false in
private lemma trace_mul_finrank_eq_finrank_mul_trace {A M : Type} [Ring A] [Algebra ℚ A] [FiniteDimensional ℚ A]
    [IsSimpleRing A] [AddCommGroup M] [Module A M] [Module ℚ M] [IsScalarTower ℚ A M]
    [FiniteDimensional ℚ M] (c : A) :
    LinearMap.trace ℚ M (DistribSMul.toLinearMap ℚ M c) * Module.finrank ℚ A =
      Module.finrank ℚ M * LinearMap.trace ℚ A (DistribSMul.toLinearMap ℚ A c) := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite ℚ A
  haveI : IsSemisimpleRing A := (IsSimpleRing.isSemisimpleRing_iff_isArtinianRing (R := A)).mpr inferInstance
  haveI : Module.Finite A M := Module.Finite.of_restrictScalars_finite ℚ A M
  obtain ⟨S, hS⟩ := IsSemisimpleModule.exists_simple_submodule A (A × M)
  have hP : IsIsotypicOfType A (A × M) S := IsSimpleRing.isIsotypic A (A × M) S
  have hA : IsIsotypicOfType A A S := by
    refine (LinearEquiv.isIsotypicOfType_iff
      (LinearEquiv.ofInjective (LinearMap.inl A A M) LinearMap.inl_injective)).mpr ?_
    refine isIsotypicOfType_submodule_iff.mpr ?_
    intro m _ _
    exact hP m
  have hM : IsIsotypicOfType A M S := by
    refine (LinearEquiv.isIsotypicOfType_iff
      (LinearEquiv.ofInjective (LinearMap.inr A A M) LinearMap.inr_injective)).mpr ?_
    refine isIsotypicOfType_submodule_iff.mpr ?_
    intro m _ _
    exact hP m
  haveI : FiniteDimensional ℚ S :=
    Module.Finite.of_injective ((S.subtype).restrictScalars ℚ) S.injective_subtype
  obtain ⟨k, ⟨eA⟩⟩ := hA.linearEquiv_fun
  obtain ⟨m, ⟨eM⟩⟩ := hM.linearEquiv_fun
  obtain ⟨hA1, hA2⟩ := trace_and_finrank_of_linearEquiv_pi k eA c
  obtain ⟨hM1, hM2⟩ := trace_and_finrank_of_linearEquiv_pi m eM c
  rw [hA1, hA2, hM1, hM2]
  push_cast
  ring


set_option autoImplicit false in
theorem _root_.GlobalTheory.QTrace.q_trace : ∀ {F A V : Type} [Field F] [NumberField F] [Ring A] [Algebra F A] [FiniteDimensional F A] [Algebra.IsCentral F A]
    [IsSimpleRing A] [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (n : ℕ), Module.finrank F A = n ^ 2 →
    ∀ (ρ : A →+* Module.End ℚ V) (ψ : (F →+* ℂ) → (A →+* Matrix (Fin n) (Fin n) ℂ)),
    (∀ σ (x : F), ψ σ (algebraMap F A x) = Matrix.scalar (Fin n) (σ x)) → ∀ c : A,
    ((n * Module.finrank ℚ F : ℕ) : ℂ) * ((LinearMap.trace ℚ V (ρ c) : ℚ) : ℂ) =
      (Module.finrank ℚ V : ℂ) * ∑ σ, Matrix.trace (ψ σ c) := by
  intro F A V _ _ _ _ _ _ _ _ _ _ n hn ρ ψ hψ c
  have hn0 : n ≠ 0 := by
    rintro rfl
    have : 0 < Module.finrank F A := Module.finrank_pos
    simp [hn] at this
  letI : Algebra ℚ A := RingHom.toAlgebra' ((algebraMap F A).comp (algebraMap ℚ F))
    (fun q x => Algebra.commutes _ x)
  haveI : IsScalarTower ℚ F A := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : FiniteDimensional ℚ A := Module.Finite.trans F A
  letI : Module A V := Module.compHom V ρ
  have hρq : ∀ q : ℚ, ρ (algebraMap ℚ A q) = algebraMap ℚ (Module.End ℚ V) q := fun q =>
    congrArg (fun f : ℚ →+* Module.End ℚ V => f q)
      (RingHom.ext_rat (ρ.comp (algebraMap ℚ A)) (algebraMap ℚ (Module.End ℚ V)))
  haveI : IsScalarTower ℚ A V := ⟨fun q a v => by
    show ρ (q • a) v = q • ρ a v
    rw [Algebra.smul_def, map_mul, Module.End.mul_apply, hρq, Module.algebraMap_end_apply]⟩
  have hV : LinearMap.trace ℚ V (DistribSMul.toLinearMap ℚ V c) = LinearMap.trace ℚ V (ρ c) := rfl
  have hA : LinearMap.trace ℚ A (DistribSMul.toLinearMap ℚ A c) =
      Algebra.trace ℚ F (LinearMap.trace F A (LinearMap.mulLeft F c)) := by
    rw [← trace_restrictScalars_rat]
    rfl
  have hsum : (algebraMap ℚ ℂ (Algebra.trace ℚ F (LinearMap.trace F A (LinearMap.mulLeft F c)))) =
      n * ∑ σ, Matrix.trace (ψ σ c) := by
    rw [trace_eq_sum_embeddings ℂ, Finset.mul_sum]
    refine (Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ).symm _ _ fun τ => ?_)
    exact embedding_trace_mulLeft_eq_mul_trace n hn _ (ψ _) (hψ _) c
  have hdim : Module.finrank ℚ A = Module.finrank ℚ F * n ^ 2 := by
    rw [← hn, Module.finrank_mul_finrank]
  have key := trace_mul_finrank_eq_finrank_mul_trace (A := A) (M := V) c
  rw [hV, hA, hdim] at key
  have key' := congrArg (fun t : ℚ => (t : ℂ)) key
  simp only [Rat.cast_mul, Rat.cast_natCast] at key'
  have hsum' : ((Algebra.trace ℚ F (LinearMap.trace F A (LinearMap.mulLeft F c)) : ℚ) : ℂ) =
      n * ∑ σ, Matrix.trace (ψ σ c) := hsum
  rw [hsum'] at key'
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  apply mul_left_cancel₀ hnC
  push_cast at key' ⊢
  linear_combination key'

end GlobalTheory.QTrace
end
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.TraceActionEqSumPlaces
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix
open IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct Classical ComplexOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKCx GlobalTheory.PELU
attribute [local instance] Over.cartesianMonoidalCategory
open UpperTheory.ComplexUniformization

private def psiE {p : ℕ} [Fact p.Prime] (G : HTGroup p) (σ : G.F →+* ℂ) : G.C →+* Matrix (Fin G.n) (Fin G.n) ℂ :=
  if (InfinitePlace.mk σ).embedding = σ then G.psi (InfinitePlace.mk σ)
  else ((starRingEnd ℂ).mapMatrix).comp (G.psi (InfinitePlace.mk σ))

private theorem psiE_F {p : ℕ} [Fact p.Prime] (G : HTGroup p) (σ : G.F →+* ℂ) (x : G.F) :
    psiE G σ (algebraMap G.F G.C x) = Matrix.scalar (Fin G.n) (σ x) := by
  unfold psiE
  split_ifs with h
  · rw [G.psi_F, h]
  · have h2 : (InfinitePlace.mk σ).embedding = ComplexEmbedding.conjugate σ :=
      (InfinitePlace.embedding_mk_eq σ).resolve_left h
    rw [RingHom.comp_apply, G.psi_F, h2]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, Matrix.diagonal_apply, hij, ComplexEmbedding.conjugate_coe_eq]

private theorem sum_psiE {p : ℕ} [Fact p.Prime] (G : HTGroup p) (c : G.C) :
    ∑ σ : G.F →+* ℂ, Matrix.trace (psiE G σ c) =
      ∑ v : InfinitePlace G.F, ((2 * (Matrix.trace (G.psi v c)).re : ℝ) : ℂ) := by
  rw [← Finset.sum_fiberwise Finset.univ (fun σ : G.F →+* ℂ => InfinitePlace.mk σ)]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hne : ComplexEmbedding.conjugate v.embedding ≠ v.embedding := fun h =>
    (InfinitePlace.isComplex_iff.1 (IsTotallyComplex.isComplex v)) h
  have hf : (Finset.univ.filter fun σ : G.F →+* ℂ => InfinitePlace.mk σ = v) =
      {v.embedding, ComplexEmbedding.conjugate v.embedding} := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro rfl
      rcases InfinitePlace.embedding_mk_eq σ with h | h
      · exact Or.inl h.symm
      · refine Or.inr ?_
        rw [h]
        exact (star_star σ).symm
    · rintro (rfl | rfl)
      · exact InfinitePlace.mk_embedding v
      · rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
  rw [hf, Finset.sum_pair hne.symm]
  have h1 : psiE G v.embedding = G.psi v := by
    unfold psiE
    rw [InfinitePlace.mk_embedding, if_pos rfl]
  have h2 : psiE G (ComplexEmbedding.conjugate v.embedding) = ((starRingEnd ℂ).mapMatrix).comp (G.psi v) := by
    unfold psiE
    rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding, if_neg hne.symm]
  rw [h1, h2, RingHom.comp_apply]
  have h3 : Matrix.trace (((starRingEnd ℂ).mapMatrix) (G.psi v c)) = (starRingEnd ℂ) (Matrix.trace (G.psi v c)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.trace, map_sum]
  rw [h3, Complex.add_conj]

private theorem trace_rep {p : ℕ} [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (c : G.C) :
    ((LinearMap.trace ℚ (VQ D) (L.rep c) : ℚ) : ℝ) =
      2 * (D.m : ℝ) * ∑ v : InfinitePlace G.F, (Matrix.trace (G.psi v c)).re := by
  have h3 : Module.finrank ℚ G.F = Module.finrank ℚ D.F :=
    (AlgEquiv.ofRingEquiv (f := L.e) (fun r => by simp)).toLinearEquiv.finrank_eq.symm
  have h4 : Module.finrank ℚ (VQ D) = D.m * G.n * Module.finrank ℚ G.F := by
    haveI := D.freeLa
    rw [h3, L.n_eq, ← D.rankLa]
    exact Module.finrank_baseChange
  haveI : FiniteDimensional ℚ (VQ D) := by
    haveI := D.finLa
    infer_instance
  have hq := GlobalTheory.QTrace.q_trace (F := G.F) (A := G.C) (V := VQ D) G.n G.rankC L.rep.toRingHom (psiE G) (psiE_F G) c
  rw [sum_psiE, h4] at hq
  have hn : (G.n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 G.n_pos.ne'
  have hd : ((Module.finrank ℚ G.F : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  push_cast at hq
  have hq' : ((LinearMap.trace ℚ (VQ D) (L.rep c) : ℚ) : ℂ) =
      (D.m : ℂ) * ∑ v : InfinitePlace G.F, ((2 * (Matrix.trace (G.psi v c)).re : ℝ) : ℂ) := by
    have : (G.n : ℂ) * (Module.finrank ℚ G.F : ℂ) ≠ 0 := mul_ne_zero hn hd
    apply mul_left_cancel₀ this
    push_cast
    linear_combination hq
  have : (((LinearMap.trace ℚ (VQ D) (L.rep c) : ℚ) : ℝ) : ℂ) =
      ((2 * (D.m : ℝ) * ∑ v : InfinitePlace G.F, (Matrix.trace (G.psi v c)).re : ℝ) : ℂ) := by
    push_cast at hq' ⊢
    rw [hq', Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    ring
  exact_mod_cast this

theorem UpperTheory.trace_action_eq_sum_places :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (x : ℝ ⊗[ℚ] G.C), LinearMap.trace ℝ (ℝ ⊗[ℚ] VQ D) (actOn L.rep ℝ x) = 2 * (D.m : ℝ) * ∑ v : InfinitePlace G.F, (Matrix.trace (G.psiR v x)).re := by
  intro p _ D G L x
  haveI : FiniteDimensional ℚ (VQ D) := by
    haveI := D.finLa
    infer_instance
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add (f := _), Matrix.trace_add, Complex.add_re, Finset.sum_add_distrib, hx, hy, mul_add]
  | tmul r c =>
    have h1 : actOn L.rep ℝ (r ⊗ₜ[ℚ] c) = r • (L.rep c).baseChange ℝ := by
      rw [Algebra.smul_def]
      exact Algebra.TensorProduct.lift_tmul _ _ _ r c
    rw [h1, map_smul, LinearMap.trace_baseChange, smul_eq_mul]
    have h2 : (algebraMap ℚ ℝ) (LinearMap.trace ℚ (VQ D) (L.rep c)) = ((LinearMap.trace ℚ (VQ D) (L.rep c) : ℚ) : ℝ) := rfl
    rw [h2, trace_rep]
    simp only [HTGroup.psiR_tmul, Matrix.trace_smul, Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, ← Finset.mul_sum]
    ring
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix
open IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct Classical ComplexOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKCx GlobalTheory.PELU
attribute [local instance] Over.cartesianMonoidalCategory
open UpperTheory.ComplexUniformization

private theorem jt_sum_emb {F : Type} [Field F] [NumberField F] [IsCMField F] (g : (F →+* ℂ) → ℂ) :
    ∑ σ : F →+* ℂ, g σ = ∑ w : InfinitePlace F,
      (g w.embedding + g (ComplexEmbedding.conjugate w.embedding)) := by
  rw [← Finset.sum_fiberwise Finset.univ (fun σ : F →+* ℂ => InfinitePlace.mk σ) g]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := by
    intro h
    have hc : w.IsComplex := IsTotallyComplex.isComplex w
    exact (InfinitePlace.isComplex_iff.mp hc) (ComplexEmbedding.isReal_iff.mpr h.symm)
  have hf : (Finset.univ.filter fun σ : F →+* ℂ => InfinitePlace.mk σ = w) =
      {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro rfl
      rcases InfinitePlace.embedding_mk_eq σ with h | h
      · exact Or.inl h.symm
      · right; rw [h]; simp
    · rintro (rfl | rfl)
      · exact InfinitePlace.mk_embedding w
      · rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
  rw [hf, Finset.sum_pair hne]

private theorem jt_indep {E F : Type} [Field E] [NumberField E] [Field F] [NumberField F] [IsCMField F]
    (e : E ≃+* F) (a : (E →+* ℂ) → ℂ) (t : InfinitePlace F → ℂ)
    (h : ∀ c : 𝓞 E, ∑ σ : E →+* ℂ, a σ * σ (c : E) =
      ∑ w : InfinitePlace F, (t w * w.embedding (e c) +
        (starRingEnd ℂ) (t w) * (starRingEnd ℂ) (w.embedding (e c))))
    (w : InfinitePlace F) : a (w.embedding.comp (e : E →+* F)) = t w := by
  let r : (F →+* ℂ) ≃ (E →+* ℂ) :=
    { toFun := fun σ => σ.comp (e : E →+* F)
      invFun := fun σ => σ.comp (e.symm : F →+* E)
      left_inv := fun σ => by ext x; simp
      right_inv := fun σ => by ext x; simp }
  let B : (F →+* ℂ) → ℂ := fun σ =>
    if σ = (InfinitePlace.mk σ).embedding then t (InfinitePlace.mk σ)
    else (starRingEnd ℂ) (t (InfinitePlace.mk σ))
  have hB1 : ∀ w : InfinitePlace F, B w.embedding = t w := by
    intro w; simp [B, InfinitePlace.mk_embedding]
  have hB2 : ∀ w : InfinitePlace F, B (ComplexEmbedding.conjugate w.embedding) = (starRingEnd ℂ) (t w) := by
    intro w
    have hne : ComplexEmbedding.conjugate w.embedding ≠ w.embedding := by
      intro h
      have hc : w.IsComplex := IsTotallyComplex.isComplex w
      exact (InfinitePlace.isComplex_iff.mp hc) (ComplexEmbedding.isReal_iff.mpr h)
    simp only [B, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
    rw [if_neg hne]
  have key : ∀ c : 𝓞 E, ∑ σ : E →+* ℂ, (a σ - B (r.symm σ)) * σ (c : E) = 0 := by
    intro c
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [h c, sub_eq_zero, ← Equiv.sum_comp r (fun σ => B (r.symm σ) * σ (c : E))]
    have := jt_sum_emb (fun σ : F →+* ℂ => B σ * σ (e c))
    simp only [Equiv.symm_apply_apply]
    have hr : ∑ σ : F →+* ℂ, B σ * (r σ) (c : E) = ∑ σ : F →+* ℂ, B σ * σ (e c) :=
      Finset.sum_congr rfl fun _ _ => rfl
    rw [hr, this]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [hB1, hB2, ComplexEmbedding.conjugate_coe_eq]
  have h0 := GlobalTheory.UPel.HT.LieType.DimSum.coeff_eq_zero_of_sum_embeddings _ key (r w.embedding)
  simp only [Equiv.symm_apply_apply, hB1] at h0
  exact sub_eq_zero.mp h0

private theorem jt_ne {p : ℕ} [Fact p.Prime] (D : Datum p) : (starRingEnd ℂ) D.ρc ≠ D.ρc := by
  intro h
  have him : D.ρc.im = 0 := Complex.conj_eq_iff_im.mp h
  have hre : D.ρc = (D.ρc.re : ℂ) := by
    apply Complex.ext <;> simp [him]
  have h0 := D.ρc_root
  rw [hre] at h0
  have h1 : D.ρc.re ^ 2 - (D.tr : ℝ) * D.ρc.re + (D.nm : ℝ) = 0 := by exact_mod_cast h0
  have h2 : ((D.tr ^ 2 - 4 * D.nm : ℤ) : ℝ) < 0 := by exact_mod_cast D.disc_neg
  push_cast at h2
  nlinarith [sq_nonneg (2 * D.ρc.re - (D.tr : ℝ))]

private theorem jt_root {p : ℕ} [Fact p.Prime] (D : Datum p) (τ : D.F →+* ℂ) :
    τ (D.ω : D.F) = D.ρc ∨ τ (D.ω : D.F) = (starRingEnd ℂ) D.ρc := by
  have hω : (D.ω : 𝓞 D.F) ^ 2 - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
    rw [← D.tr_eq, ← D.nm_eq]; ring
  have hz : (τ (D.ω : D.F)) ^ 2 - (D.tr : ℂ) * τ (D.ω : D.F) + (D.nm : ℂ) = 0 := by
    have := congrArg (fun x : 𝓞 D.F => τ (x : D.F)) hω
    simpa using this
  have hρ := D.ρc_root
  have hc : ((starRingEnd ℂ) D.ρc) ^ 2 - (D.tr : ℂ) * (starRingEnd ℂ) D.ρc + (D.nm : ℂ) = 0 := by
    have := congrArg (starRingEnd ℂ) hρ
    simpa using this
  have hsum : (starRingEnd ℂ) D.ρc + D.ρc - (D.tr : ℂ) = 0 := by
    have : ((starRingEnd ℂ) D.ρc - D.ρc) * ((starRingEnd ℂ) D.ρc + D.ρc - (D.tr : ℂ)) = 0 := by
      linear_combination hc - hρ
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (jt_ne D))
  have : (τ (D.ω : D.F) - D.ρc) * (τ (D.ω : D.F) - (starRingEnd ℂ) D.ρc) = 0 := by
    linear_combination hz - τ (D.ω : D.F) * hsum + D.ρc * hsum - hρ
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

private theorem jt_S {p : ℕ} [Fact p.Prime] (D : Datum p) (c : 𝓞 D.F) :
    (∑ τ ∈ Finset.univ.filter (fun τ : D.F →+* ℂ => τ (D.ω : D.F) ≠ D.ρc), (D.n : ℂ) * τ (c : D.F)) -
      (starRingEnd ℂ) (∑ τ ∈ Finset.univ.filter (fun τ : D.F →+* ℂ => τ (D.ω : D.F) ≠ D.ρc),
        (D.n : ℂ) * τ (c : D.F)) =
    ∑ τ : D.F →+* ℂ, (D.n : ℂ) * (if τ (D.ω : D.F) ≠ D.ρc then 1 else -1) * τ (c : D.F) := by
  have hc : (starRingEnd ℂ) (∑ τ ∈ Finset.univ.filter (fun τ : D.F →+* ℂ => τ (D.ω : D.F) ≠ D.ρc),
        (D.n : ℂ) * τ (c : D.F)) =
      ∑ τ ∈ Finset.univ.filter (fun τ : D.F →+* ℂ => ¬ τ (D.ω : D.F) ≠ D.ρc), (D.n : ℂ) * τ (c : D.F) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_nbij' (fun σ => (starRingEnd ℂ).comp σ) (fun σ => (starRingEnd ℂ).comp σ) ?_ ?_ ?_ ?_ ?_
    · intro σ hσ
      have hσ' : σ (D.ω : D.F) ≠ D.ρc := (Finset.mem_filter.mp hσ).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rcases jt_root D σ with h | h
      · exact absurd h hσ'
      · simp [h]
    · intro σ hσ
      have hσ' : ¬ σ (D.ω : D.F) ≠ D.ρc := (Finset.mem_filter.mp hσ).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have h : σ (D.ω : D.F) = D.ρc := not_not.mp hσ'
      simpa [h] using jt_ne D
    · intro σ _; ext x; simp
    · intro σ _; ext x; simp
    · intro σ _; simp
  rw [hc, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun τ : D.F →+* ℂ => τ (D.ω : D.F) ≠ D.ρc)
    (fun τ => (D.n : ℂ) * (if τ (D.ω : D.F) ≠ D.ρc then 1 else -1) * τ (c : D.F)),
    sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun τ h => ?_
    rw [if_pos (Finset.mem_filter.mp h).2]; ring
  · refine Finset.sum_congr rfl fun τ h => ?_
    rw [if_neg (Finset.mem_filter.mp h).2]; ring

private theorem jt_lhs {p : ℕ} [Fact p.Prime] (D : Datum p) (τ₁ : D.F →+* ℂ) (c : 𝓞 D.F) :
    ∑ σ : D.F →+* ℂ, (Complex.I * (D.m : ℂ) * ((if σ = τ₁ then 2 else 0) -
        (if σ = (starRingEnd ℂ).comp τ₁ then 2 else 0) +
        (D.n : ℂ) * (if σ (D.ω : D.F) ≠ D.ρc then 1 else -1))) * σ (c : D.F) =
      Complex.I * ((D.m : ℂ) * (τ₁ (c : D.F) +
        ∑ τ ∈ Finset.univ.filter (fun τ : D.F →+* ℂ => τ (D.ω : D.F) ≠ D.ρc), (D.n : ℂ) * τ (c : D.F) -
        (starRingEnd ℂ) (τ₁ (c : D.F)))) +
      (starRingEnd ℂ) (Complex.I * ((D.m : ℂ) * (τ₁ (c : D.F) +
        ∑ τ ∈ Finset.univ.filter (fun τ : D.F →+* ℂ => τ (D.ω : D.F) ≠ D.ρc), (D.n : ℂ) * τ (c : D.F) -
        (starRingEnd ℂ) (τ₁ (c : D.F))))) := by
  have hS := jt_S D c
  have e1 : ∑ σ : D.F →+* ℂ, (if σ = τ₁ then (2 : ℂ) else 0) * σ (c : D.F) = 2 * τ₁ (c : D.F) := by
    simp [ite_mul]
  have e2 : ∑ σ : D.F →+* ℂ, (if σ = (starRingEnd ℂ).comp τ₁ then (2 : ℂ) else 0) * σ (c : D.F) =
      2 * (starRingEnd ℂ) (τ₁ (c : D.F)) := by
    simp [ite_mul]
  have e0 : ∑ σ : D.F →+* ℂ, (Complex.I * (D.m : ℂ) * ((if σ = τ₁ then 2 else 0) -
        (if σ = (starRingEnd ℂ).comp τ₁ then 2 else 0) +
        (D.n : ℂ) * (if σ (D.ω : D.F) ≠ D.ρc then 1 else -1))) * σ (c : D.F) =
      Complex.I * (D.m : ℂ) * (∑ σ : D.F →+* ℂ, (if σ = τ₁ then (2 : ℂ) else 0) * σ (c : D.F) -
        ∑ σ : D.F →+* ℂ, (if σ = (starRingEnd ℂ).comp τ₁ then (2 : ℂ) else 0) * σ (c : D.F) +
        ∑ σ : D.F →+* ℂ, (D.n : ℂ) * (if σ (D.ω : D.F) ≠ D.ρc then 1 else -1) * σ (c : D.F)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    ring
  rw [e0, e1, e2, ← hS]
  simp only [map_mul, map_add (f := _), map_sub, Complex.conj_I, Complex.conj_natCast, Complex.conj_conj]
  ring

private theorem jt_actOn {C V : Type} [Ring C] [Algebra ℚ C] [AddCommGroup V] [Module ℚ V]
    (rep : C →ₐ[ℚ] Module.End ℚ V) (x : C) :
    actOn rep ℝ ((1 : ℝ) ⊗ₜ[ℚ] x) = (rep x).baseChange ℝ := by
  unfold actOn
  erw [Algebra.TensorProduct.lift_tmul]
  simp only [map_one, _root_.one_mul]
  rfl

private theorem jt_psi {p : ℕ} [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (x : G.F)
    (J : ℝ ⊗[ℚ] G.C) :
    Matrix.trace (G.psiR v (J * ((1 : ℝ) ⊗ₜ[ℚ] algebraMap G.F G.C x))) =
      Matrix.trace (G.psiR v J) * v.embedding x := by
  have h : G.psiR v ((1 : ℝ) ⊗ₜ[ℚ] algebraMap G.F G.C x) = Matrix.scalar (Fin G.n) (v.embedding x) := by
    unfold HTGroup.psiR
    erw [Algebra.TensorProduct.lift_tmul]
    simp only [map_one, _root_.one_mul]
    exact G.psi_F v x
  rw [map_mul, h]
  simp [Matrix.trace, Matrix.scalar_apply, Matrix.mul_diagonal, Finset.sum_mul]

private theorem jt_real {p : ℕ} [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G)
    (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (Φ : (ℝ ⊗[ℚ] VQ D) ≃ₗ[ℝ] (Fin D.g → ℂ))
    (Jc : ℝ ⊗[ℚ] G.C) (h1 : ∀ (b : D.O) u, Φ ((actQ D b).baseChange ℝ u) = ρ b *ᵥ Φ u)
    (h2 : ∀ u, Φ (actOn L.rep ℝ Jc u) = Complex.I • Φ u) (c : 𝓞 D.F) :
    LinearMap.trace ℝ (ℝ ⊗[ℚ] VQ D)
        (actOn L.rep ℝ (Jc * ((1 : ℝ) ⊗ₜ[ℚ] algebraMap G.F G.C (L.e c)))) =
      2 * (Complex.I * (ρ (algebraMap (𝓞 D.F) D.O c)).trace).re := by
  have hX : Φ.conj (actOn L.rep ℝ (Jc * ((1 : ℝ) ⊗ₜ[ℚ] algebraMap G.F G.C (L.e c)))) =
      (Matrix.toLin' (Complex.I • ρ (algebraMap (𝓞 D.F) D.O c))).restrictScalars ℝ := by
    apply LinearMap.ext
    intro y
    rw [LinearEquiv.conj_apply]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, map_mul, Module.End.mul_apply, jt_actOn,
      L.rep_F, h2, h1, LinearEquiv.apply_symm_apply, LinearMap.restrictScalars_apply,
      Matrix.toLin'_apply, Matrix.smul_mulVec]
  rw [← LinearMap.trace_conj' _ Φ, hX, GlobalTheory.UPel.HT.LieType.DimSum.trace_real_restrict, Matrix.trace_smul,
    smul_eq_mul]

theorem UpperTheory.trace_complex_structure_places :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (v : InfinitePlace G.F), D.a = 1 → TypeAt D ρ → sigPosH (G.gram_herm v) = 1 → ∀ (Φ : (ℝ ⊗[ℚ] VQ D) ≃ₗ[ℝ] (Fin D.g → ℂ)) (Jc : ℝ ⊗[ℚ] G.C), Jc * Jc = -1 → (∀ (b : D.O) u, Φ ((actQ D b).baseChange ℝ u) = ρ b *ᵥ Φ u) → (∀ u, Φ (actOn L.rep ℝ Jc u) = Complex.I • Φ u) → ∀ v' : InfinitePlace G.F, Matrix.trace (G.psiR v' Jc) = (if v'.embedding (L.e D.ω) = D.ρc then Complex.I else -Complex.I) * (2 * (if v' = v then 1 else 0) - (G.n : ℂ)) := by
  intro p _ D G L ρ v ha hT hv Φ Jc _ h1 h2 v'
  have hm : (D.m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr D.m_pos.ne'
  have hn : (G.n : ℂ) = (D.n : ℂ) := by rw [L.n_eq]
  let i0 : Fin D.a := ⟨0, by omega⟩
  have hsum : ∀ f : Fin D.a → ℂ, ∑ i, f i = f i0 := fun f =>
    Fintype.sum_eq_single i0 (fun j hj => absurd (Fin.ext (by simp only [i0]; omega)) hj)
  obtain ⟨i, hi⟩ := (L.sig v).mp hv
  have hii : i = i0 := Fin.ext (by simp only [i0]; omega)
  rw [hii] at hi
  obtain ⟨τ₁, hτ₁⟩ : ∃ τ₁ : D.F →+* ℂ, τ₁ = D.tau i0 := ⟨_, rfl⟩
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀ : G.F →+* ℂ, σ₀ = G.iotaC.comp (L.s i0) := ⟨_, rfl⟩
  rw [← hσ₀] at hi
  have hσ : σ₀.comp (L.e : D.F →+* G.F) = τ₁ := by
    ext x
    rw [hσ₀, hτ₁]
    exact L.s_C i0 x
  have hτω : τ₁ (D.ω : D.F) = D.ρc := by rw [hτ₁]; exact D.tau_ω i0

  have hmain := jt_indep L.e
    (fun σ : D.F →+* ℂ => Complex.I * (D.m : ℂ) * ((if σ = τ₁ then 2 else 0) -
        (if σ = (starRingEnd ℂ).comp τ₁ then 2 else 0) +
        (D.n : ℂ) * (if σ (D.ω : D.F) ≠ D.ρc then 1 else -1)))
    (fun w => (D.m : ℂ) * Matrix.trace (G.psiR w Jc)) (fun c => by
      have h484 := UpperTheory.trace_action_eq_sum_places p D G L (Jc * ((1 : ℝ) ⊗ₜ[ℚ] algebraMap G.F G.C (L.e c)))
      rw [jt_real D G L ρ Φ Jc h1 h2 c] at h484
      simp only [jt_psi] at h484
      have hTc := hT c
      rw [hsum, hsum, ← hτ₁] at hTc
      rw [hTc] at h484
      rw [jt_lhs D τ₁ c, Complex.add_conj, h484]
      have hw : ∀ w : InfinitePlace G.F, (D.m : ℂ) * Matrix.trace (G.psiR w Jc) * w.embedding (L.e c) +
          (starRingEnd ℂ) ((D.m : ℂ) * Matrix.trace (G.psiR w Jc)) *
            (starRingEnd ℂ) (w.embedding (L.e c)) =
          ((2 * (D.m : ℝ) * (Matrix.trace (G.psiR w Jc) * w.embedding (L.e c)).re : ℝ) : ℂ) := by
        intro w
        have hre : ((D.m : ℂ) * (Matrix.trace (G.psiR w Jc) * w.embedding (L.e c))).re =
            (D.m : ℝ) * (Matrix.trace (G.psiR w Jc) * w.embedding (L.e c)).re := by
          simp [Complex.mul_re]
        rw [← map_mul, Complex.add_conj, mul_assoc (D.m : ℂ), hre]
        push_cast
        ring
      simp only [hw]
      push_cast
      rw [Finset.mul_sum]) v'
  obtain ⟨σ', hσ'⟩ : ∃ σ' : D.F →+* ℂ, σ' = v'.embedding.comp (L.e : D.F →+* G.F) := ⟨_, rfl⟩
  rw [← hσ'] at hmain
  have hσω : σ' (D.ω : D.F) = v'.embedding (L.e D.ω) := by rw [hσ']; rfl
  rw [← hσω, hn]
  have hdiv : Matrix.trace (G.psiR v' Jc) = Complex.I * ((if σ' = τ₁ then 2 else 0) -
      (if σ' = (starRingEnd ℂ).comp τ₁ then 2 else 0) +
      (D.n : ℂ) * (if σ' (D.ω : D.F) ≠ D.ρc then 1 else -1)) := by
    apply mul_left_cancel₀ hm
    rw [← hmain]
    ring
  have hcj : ∀ f g : G.F →+* ℂ, f.comp (L.e : D.F →+* G.F) = g.comp (L.e : D.F →+* G.F) → f = g := by
    intro f g h
    ext y
    have := RingHom.congr_fun h (L.e.symm y)
    simpa using this
  have hconj : ((ComplexEmbedding.conjugate σ₀).comp (L.e : D.F →+* G.F)) = (starRingEnd ℂ).comp τ₁ := by
    rw [← hσ]
    ext x
    simp [ComplexEmbedding.conjugate_coe_eq]
  have hvv : v' = v ↔ σ' = τ₁ ∨ σ' = (starRingEnd ℂ).comp τ₁ := by
    constructor
    · intro h
      rcases InfinitePlace.embedding_mk_eq σ₀ with h3 | h3
      · left
        rw [hσ', h, hi, h3, hσ]
      · right
        rw [hσ', h, hi, h3, hconj]
    · rintro (h | h)
      · rw [hi, ← hcj v'.embedding σ₀ (by rw [← hσ', h, hσ]), InfinitePlace.mk_embedding]
      · rw [hi, ← InfinitePlace.mk_conjugate_eq σ₀,
          ← hcj v'.embedding (ComplexEmbedding.conjugate σ₀) (by rw [← hσ', h, hconj]),
          InfinitePlace.mk_embedding]
  by_cases hε : σ' (D.ω : D.F) = D.ρc
  · have h2' : σ' ≠ (starRingEnd ℂ).comp τ₁ := by
      intro h
      have h3 : σ' (D.ω : D.F) = (starRingEnd ℂ) D.ρc := by rw [h, RingHom.comp_apply, hτω]
      exact jt_ne D (h3.symm.trans hε)
    by_cases hw : v' = v
    · have h1' : σ' = τ₁ := (hvv.mp hw).resolve_right h2'
      rw [hdiv, if_pos h1', if_neg h2', if_pos hε, if_pos hw, if_neg (not_not.mpr hε)]
      ring
    · have h1' : σ' ≠ τ₁ := fun h => hw (hvv.mpr (Or.inl h))
      rw [hdiv, if_neg h1', if_neg h2', if_pos hε, if_neg hw, if_neg (not_not.mpr hε)]
      ring
  · have h1' : σ' ≠ τ₁ := fun h => hε (by rw [h, hτω])
    by_cases hw : v' = v
    · have h2' : σ' = (starRingEnd ℂ).comp τ₁ := (hvv.mp hw).resolve_left h1'
      rw [hdiv, if_neg h1', if_pos h2', if_neg hε, if_pos hw, if_pos hε]
      ring
    · have h2' : σ' ≠ (starRingEnd ℂ).comp τ₁ := fun h => hw (hvv.mpr (Or.inr h))
      rw [hdiv, if_neg h1', if_neg h2', if_neg hε, if_neg hw, if_pos hε]
      ring
