module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorAutomorphicDerivatives
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalTermIntegralExpression
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeSublatticePullbackAlongEmbedding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalNormOutsideFiniteSet

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraceFormOfTwistedNormCharpoly
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraceFormOfTwistedNormCharpoly
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.TwTraceForm

theorem phi_transpose (a : ℕ) (L : Type) [Field L] :
    (GlobalTheory.Tw.Phi a L)ᵀ = (-1 : L) ^ (a - 1) • GlobalTheory.Tw.Phi a L :=
  (GlobalTheory.antidiag_twisted_norm L (RingEquiv.refl L) (fun _ => rfl) a (GlobalTheory.Tw.Phi a L) (by
    ext i j
    simp only [GlobalTheory.Tw.Phi, Matrix.of_apply]
    have : ((i : ℕ) + (j : ℕ) + 1 = a) ↔ j = i.rev := by
      rw [Fin.ext_iff, Fin.val_rev]; omega
    simp only [this])).1

theorem phi_map (a : ℕ) (L : Type) [Field L] (c : L →+* L) :
    (GlobalTheory.Tw.Phi a L).map c = GlobalTheory.Tw.Phi a L := by
  ext i j
  simp only [GlobalTheory.Tw.Phi, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

theorem phi_transpose_mul (a : ℕ) (L : Type) [Field L] :
    (GlobalTheory.Tw.Phi a L)ᵀ * GlobalTheory.Tw.Phi a L = 1 :=
  mul_eq_one_comm.1 (GlobalTheory.CuspRep.Phi_mul_transpose a L)

theorem gram_eq (a : ℕ) (L : Type) [Field L] (δ : GL (Fin a) L) :
    ((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ = ((δ⁻¹ : GL (Fin a) L).val)ᵀ * GlobalTheory.Tw.Phi a L := by
  have h : (δ.val * GlobalTheory.Tw.Phi a L)⁻¹ = (GlobalTheory.Tw.Phi a L)ᵀ * (δ⁻¹ : GL (Fin a) L).val := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (δ⁻¹ : GL (Fin a) L).val, Units.inv_mul, Matrix.one_mul,
      phi_transpose_mul]
  rw [h, Matrix.transpose_mul, Matrix.transpose_transpose]

theorem gram_mul_transpose (a : ℕ) (L : Type) [Field L] (δ : GL (Fin a) L) :
    ((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ * (δ.val * GlobalTheory.Tw.Phi a L)ᵀ = 1 := by
  rw [gram_eq, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (GlobalTheory.Tw.Phi a L),
    GlobalTheory.CuspRep.Phi_mul_transpose, Matrix.one_mul, ← Matrix.transpose_mul, Units.mul_inv,
    Matrix.transpose_one]

theorem gram_norm (a : ℕ) (L : Type) [Field L] (c : L →+* L) (δ : GL (Fin a) L) :
    (((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ)ᵀ * (δ * thetaGL a c δ).val
      = (-1 : L) ^ (a - 1) • (((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ).map c := by
  have hθ : (thetaGL a c δ).val
      = GlobalTheory.Tw.Phi a L * (((δ⁻¹ : GL (Fin a) L).val).map c)ᵀ * (GlobalTheory.Tw.Phi a L)ᵀ := rfl
  rw [gram_eq, Units.val_mul, hθ, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.map_mul, Matrix.transpose_map, phi_map]
  set Φ := GlobalTheory.Tw.Phi a L
  set Di := (δ⁻¹ : GL (Fin a) L).val
  set X := (Di.map c)ᵀ
  calc Φᵀ * Di * (δ.val * (Φ * X * Φᵀ))
      = Φᵀ * (Di * δ.val) * Φ * X * Φᵀ := by
        simp only [Matrix.mul_assoc]
    _ = X * Φᵀ := by
        rw [Units.inv_mul, Matrix.mul_one, phi_transpose_mul, Matrix.one_mul]
    _ = (-1 : L) ^ (a - 1) • (X * Φ) := by
        rw [phi_transpose, Matrix.mul_smul]

theorem form_asym {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] (σ : k ≃+* k)
    (hσ : ∀ x, σ (σ x) = x) (S N : Matrix n n k) (ε : k) (h : S.map σ = ε • (Sᵀ * N))
    (u v : n → k) :
    σ (v ⬝ᵥ S *ᵥ (fun j => σ (u j))) = (ε • N *ᵥ u) ⬝ᵥ S *ᵥ (fun j => σ (v j)) := by
  have h1 : σ (v ⬝ᵥ S *ᵥ (fun j => σ (u j))) = (fun j => σ (v j)) ⬝ᵥ S.map σ *ᵥ u := by
    rw [show σ (v ⬝ᵥ S *ᵥ (fun j => σ (u j))) = (σ : k →+* k) (v ⬝ᵥ S *ᵥ (fun j => σ (u j))) from rfl,
      RingHom.map_dotProduct]
    congr 1
    funext i
    rw [Function.comp_apply, RingHom.map_mulVec]
    congr 1
    funext j
    simp [hσ]
  rw [h1, h, Matrix.smul_mulVec, dotProduct_smul, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, smul_dotProduct, dotProduct_comm, smul_eq_mul]

end GlobalTheory.TwTraceForm

namespace GlobalTheory.TwTraceForm

theorem exists_trace_form : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (L : Type) [Field L] (e : K.E ≃+* L) (c : L →+* L), (∀ x, e (K.c x) = c (e x)) → (∀ x, c (c x) = x) → B.g * B.σ B.g = 1 → ∀ (a : ℕ) (Q : L[X]), B.P = Q.map e.symm.toRingHom → Q.Separable → Q.natDegree = a → ∀ δ : GL (Fin a) L, (δ * thetaGL a c δ).val.charpoly = Q → ∃ β : B.Aˣ, B.σ (β : B.A) = β * ((-1) ^ (a - 1) * B.g) ∧ ∃ b : Module.Basis (Fin a) K.E B.A, ((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ = (Matrix.of fun i j => e (B.herm β (b i) (b j))) := by
  intro K B L _ e c hec hcc hg a Q hBP hQs hQd δ hδ
  classical
  let f : L →+* K.E := e.symm.toRingHom
  have hf : ∀ x, f (c x) = K.c (f x) := by
    intro x
    apply e.injective
    show e (e.symm (c x)) = e (K.c (e.symm x))
    rw [hec, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  set G := ((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ with hG
  set N := (δ * thetaGL a c δ).val with hN
  set S := G.map f with hS
  set N' := N.map f with hN'
  set ε : K.E := (-1) ^ (a - 1) with hε
  have hεε : ε * ε = 1 := by rw [hε, ← mul_pow]; simp
  have hkey : Sᵀ * N' = ε • S.map K.c := by
    have h0 := congrArg f.mapMatrix (gram_norm a L c δ)
    rw [map_mul] at h0
    simp only [RingHom.mapMatrix_apply] at h0
    rw [Matrix.transpose_map] at h0
    change Sᵀ * N' = _ at h0
    rw [h0]
    ext i j
    simp [f, hf, hε, Matrix.map_apply, Matrix.smul_apply]
    exact hf _
  have hSc : S.map K.c = ε • (Sᵀ * N') := by rw [hkey, smul_smul, hεε, one_smul]
  set Y := ((δ.val * GlobalTheory.Tw.Phi a L)ᵀ).map f with hY
  have hSY : S * Y = 1 := by
    have h0 := congrArg f.mapMatrix (gram_mul_transpose a L δ)
    rw [map_mul, map_one] at h0
    exact h0
  have hsep : (LinearMap.mulLeft K.E B.g).charpoly.Separable := by
    show B.P.Separable
    rw [hBP]; exact hQs.map
  have hchar : (LinearMap.mulLeft K.E B.g).charpoly = (Matrix.toLin' N').charpoly := by
    rw [Matrix.charpoly_toLin', hN', Matrix.charpoly_map, hδ]
    exact hBP
  obtain ⟨ψ, hψ⟩ := GlobalTheory.UnitLemma.PairClass.exists_intertwine K.E B.A (Fin a → K.E)
    (LinearMap.mulLeft K.E B.g) (Matrix.toLin' N') hsep hchar
  have hψ' : ∀ y, ψ (B.g * y) = N' *ᵥ ψ y := fun y => by simpa using hψ y
  have hc1 : ∀ j : Fin a, (fun k => K.c ((Pi.single j (1 : K.E) : Fin a → K.E) k)) = (Pi.single j 1 : Fin a → K.E) := by
    intro j
    funext k
    by_cases h : k = j
    · subst h; simp
    · simp [h]
  let s : B.A → B.A → K.E := fun y z => ψ y ⬝ᵥ S *ᵥ (fun j => K.c (ψ z j))
  have hadd : ∀ x y z, s (x + y) z = s x z + s y z := by
    intro x y z
    simp only [s, map_add (f := _), add_dotProduct]
  have hlin : ∀ (r : K.E) x z, s (r • x) z = r * s x z := by
    intro r x z
    simp only [s, map_smul, smul_dotProduct, smul_eq_mul]
  have hnd : ∀ y, (∀ z, s y z = 0) → y = 0 := by
    intro y hy
    have hv : ψ y ᵥ* S = 0 := by
      funext j
      have h1 := hy (ψ.symm (Pi.single j 1))
      simp only [s, LinearEquiv.apply_symm_apply] at h1
      rw [hc1 j, Matrix.dotProduct_mulVec, dotProduct_single, mul_one] at h1
      exact h1
    have h2 : ψ y = 0 := by
      rw [← Matrix.vecMul_one (ψ y), ← hSY, ← Matrix.vecMul_vecMul, hv, Matrix.zero_vecMul]
    exact ψ.injective (by rw [h2, map_zero])
  have hsym : ∀ y z, K.c (s z y) = s ((-1 : B.A) ^ (a - 1) * B.g * y) z := by
    intro y z
    have hψε : ψ ((-1 : B.A) ^ (a - 1) * B.g * y) = ε • N' *ᵥ ψ y := by
      have h1 : (-1 : B.A) ^ (a - 1) = algebraMap K.E B.A ε := by simp [hε]
      rw [h1, mul_assoc, ← Algebra.smul_def, map_smul, hψ']
    simp only [s]
    rw [hψε]
    exact form_asym K.c K.c_c S N' ε hSc (ψ y) (ψ z)
  obtain ⟨β, hβ, hs⟩ := (GlobalTheory.SesqAsym.sesq_asym K B hg hsep ((-1) ^ (a - 1))
    (neg_one_pow_eq_or B.A (a - 1))).2 s hadd hlin hnd hsym
  refine ⟨β, hβ, (Pi.basisFun K.E (Fin a)).map ψ.symm, ?_⟩
  ext i j
  simp only [Matrix.of_apply, Module.Basis.map_apply, Pi.basisFun_apply]
  rw [← hs]
  simp only [s, LinearEquiv.apply_symm_apply]
  rw [hc1 j, Matrix.mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply, hS, Matrix.map_apply]
  exact (e.apply_symm_apply _).symm

end GlobalTheory.TwTraceForm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraceFormOfTwistedNormCharpolyStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_traceForm_of_twistedNorm_charpoly : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (L : Type) [Field L] (e : K.E ≃+* L) (c : L →+* L), (∀ x, e (K.c x) = c (e x)) → (∀ x, c (c x) = x) → B.g * B.σ B.g = 1 → ∀ (a : ℕ) (Q : L[X]), B.P = Q.map e.symm.toRingHom → Q.Separable → Q.natDegree = a → ∀ δ : GL (Fin a) L, (δ * thetaGL a c δ).val.charpoly = Q → ∃ β : B.Aˣ, B.σ (β : B.A) = β * ((-1) ^ (a - 1) * B.g) ∧ ∃ b : Module.Basis (Fin a) K.E B.A, ((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ = (Matrix.of fun i j => e (B.herm β (b i) (b j))) := by
  first | exact @GlobalTheory.TwTraceForm.exists_trace_form | exact GlobalTheory.TwTraceForm.exists_trace_form | (intros; apply GlobalTheory.TwTraceForm.exists_trace_form <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixCharpolyPreservingHermitianFormCM
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixCharpolyPreservingHermitianFormCM
open NumberField IsDedekindDomain Matrix Polynomial Filter Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.GlobHerm

theorem vandermonde_diag_herm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (l : Fin n → ℂ) (hl : Function.Injective l)
    (h1 : ∀ k, ‖l k‖ = 1) (hVA : vandermonde l * A = diagonal l * vandermonde l) :
    A.det ≠ 0 ∧ (Matrix.of fun i j : Fin n => trace (A⁻¹ ^ (i : ℕ) * A ^ (j : ℕ))) = (vandermonde l)ᴴ * vandermonde l ∧
      ((vandermonde l)ᴴ * vandermonde l).det ≠ 0 ∧
      Aᴴ * ((vandermonde l)ᴴ * vandermonde l) * A = (vandermonde l)ᴴ * vandermonde l := by
  set V := vandermonde l with hV
  have hl0 : ∀ k, l k ≠ 0 := fun k h => by simpa [h] using h1 k
  have hVd : V.det ≠ 0 := det_vandermonde_ne_zero_iff.2 hl
  have hconj : ∀ k, starRingEnd ℂ (l k) = (l k)⁻¹ := by
    intro k
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, h1 k]; simp
  have hAd : A.det ≠ 0 := by
    have := congrArg Matrix.det hVA
    rw [det_mul, det_mul, det_diagonal, mul_comm] at this
    have h2 : A.det = ∏ k, l k := mul_right_cancel₀ hVd this
    rw [h2]; exact Finset.prod_ne_zero_iff.2 fun k _ => hl0 k
  set D' := diagonal fun k => (l k)⁻¹
  have hDD : D' * diagonal l = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext k; exact inv_mul_cancel₀ (hl0 k)
  have hAinv : A * A⁻¹ = 1 := mul_nonsing_inv A (isUnit_iff_ne_zero.2 hAd)
  have hVAi : V * A⁻¹ = D' * V := by
    calc V * A⁻¹ = D' * diagonal l * V * A⁻¹ := by rw [hDD, one_mul]
      _ = D' * (V * A) * A⁻¹ := by rw [hVA, mul_assoc D']
      _ = D' * V := by rw [mul_assoc, mul_assoc, hAinv, mul_one]
  have hpow : ∀ j : ℕ, V * A ^ j = diagonal l ^ j * V := by
    intro j; induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, hVA, ← mul_assoc, ← pow_succ]
  have hpowi : ∀ j : ℕ, V * A⁻¹ ^ j = D' ^ j * V := by
    intro j; induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, hVAi, ← mul_assoc, ← pow_succ]
  have hVinv : V⁻¹ * V = 1 := nonsing_inv_mul V (isUnit_iff_ne_zero.2 hVd)
  have hVinv' : V * V⁻¹ = 1 := mul_nonsing_inv V (isUnit_iff_ne_zero.2 hVd)
  refine ⟨hAd, ?_, ?_, ?_⟩
  · ext i j
    have hM : V * (A⁻¹ ^ (i : ℕ) * A ^ (j : ℕ)) = (D' ^ (i : ℕ) * diagonal l ^ (j : ℕ)) * V := by
      rw [← mul_assoc, hpowi, mul_assoc, hpow, ← mul_assoc]
    have htr : trace (A⁻¹ ^ (i : ℕ) * A ^ (j : ℕ)) = trace (D' ^ (i : ℕ) * diagonal l ^ (j : ℕ)) := by
      calc trace (A⁻¹ ^ (i : ℕ) * A ^ (j : ℕ)) = trace (V⁻¹ * (V * (A⁻¹ ^ (i : ℕ) * A ^ (j : ℕ)))) := by
            rw [← mul_assoc, hVinv, one_mul]
        _ = trace (V⁻¹ * ((D' ^ (i : ℕ) * diagonal l ^ (j : ℕ)) * V)) := by rw [hM]
        _ = trace (D' ^ (i : ℕ) * diagonal l ^ (j : ℕ)) := by
            rw [trace_mul_comm, mul_assoc, hVinv', mul_one]
    rw [of_apply, htr, diagonal_pow, diagonal_pow, diagonal_mul_diagonal, trace_diagonal, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [V, D', vandermonde_apply, conjTranspose_apply, hconj, inv_pow]
  · rw [det_mul, det_conjTranspose]
    exact mul_ne_zero (by simpa using hVd) hVd
  · calc Aᴴ * (Vᴴ * V) * A = (V * A)ᴴ * (V * A) := by
          rw [conjTranspose_mul]; simp only [mul_assoc]
      _ = Vᴴ * ((diagonal l)ᴴ * diagonal l) * V := by
          rw [hVA, conjTranspose_mul]; simp only [mul_assoc]
      _ = Vᴴ * V := by
          rw [diagonal_conjTranspose, diagonal_mul_diagonal]
          have : (diagonal fun k => star (l k) * l k) = 1 := by
            rw [← diagonal_one]; congr 1; funext k
            show starRingEnd ℂ (l k) * l k = 1
            rw [hconj, inv_mul_cancel₀ (hl0 k)]
          simp only [Pi.star_apply] at this ⊢
          rw [this, mul_one]

end GlobalTheory.GlobHerm

namespace GlobalTheory.GlobHerm

theorem exists_mat_herm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : E[X]), P ∈ Ell E n →
    ∃ C H : Matrix (Fin n) (Fin n) E, C.charpoly = P ∧ C.det ≠ 0 ∧ H.det ≠ 0 ∧
      cT (IsCMField.complexConj E).toRingEquiv.toRingHom H = H ∧
      cT (IsCMField.complexConj E).toRingEquiv.toRingHom C * H * C = H := by
  intro E _ _ _ n P hP
  obtain ⟨hmon, hdeg, hsep, hroot⟩ := hP
  subst hdeg
  have hP0 : P ≠ 0 := hmon.ne_zero
  let pb := AdjoinRoot.powerBasis hP0
  let Cm : Matrix (Fin P.natDegree) (Fin P.natDegree) E := Algebra.leftMulMatrix pb.basis pb.gen
  let H : Matrix (Fin P.natDegree) (Fin P.natDegree) E :=
    Matrix.of fun i j => trace (Cm⁻¹ ^ (i : ℕ) * Cm ^ (j : ℕ))
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hτc : ∀ x, τ ((IsCMField.complexConj E).toRingEquiv.toRingHom x) = starRingEnd ℂ (τ x) :=
    fun x => IsCMField.complexEmbedding_complexConj E τ x
  have hQsep : (P.map τ).Separable := hsep.map
  have hQcard : (P.map τ).roots.card = P.natDegree := by
    rw [splits_iff_card_roots.1 (IsAlgClosed.splits _), natDegree_map]
  have hs : (P.map τ).roots.toFinset.card = P.natDegree := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hQsep), hQcard]
  let e : (P.map τ).roots.toFinset ≃ Fin P.natDegree := Fintype.equivFinOfCardEq (by simp [hs])
  let l : Fin P.natDegree → ℂ := fun k => (e.symm k : ℂ)
  have hl : Function.Injective l := Subtype.val_injective.comp e.symm.injective
  have hlr : ∀ k, eval₂ τ (l k) P = 0 := by
    intro k
    have := (e.symm k).2
    rw [Multiset.mem_toFinset, mem_roots hQsep.ne_zero, IsRoot, eval_map] at this
    exact this
  have h1 : ∀ k, ‖l k‖ = 1 := fun k => hroot τ _ (Multiset.mem_toFinset.1 (e.symm k).2)
  have hrep : ∀ k (x : AdjoinRoot P),
      ∑ i : Fin pb.dim, l k ^ (i : ℕ) * τ (pb.basis.repr x i) = AdjoinRoot.lift τ (l k) (hlr k) x := by
    intro k x
    conv_rhs => rw [← pb.basis.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, map_mul, PowerBasis.coe_basis]
    simp only [pb, AdjoinRoot.powerBasis_gen, map_pow, AdjoinRoot.lift_root, AdjoinRoot.algebraMap_eq,
      AdjoinRoot.lift_of]
    ring
  have hVA : vandermonde l * Cm.map τ = diagonal l * vandermonde l := by
    ext k j
    rw [Matrix.mul_apply, diagonal_mul, vandermonde_apply]
    show ∑ i : Fin pb.dim, l k ^ (i : ℕ) * τ (Algebra.leftMulMatrix pb.basis pb.gen i j) = l k * l k ^ (j : ℕ)
    have hC : ∀ i : Fin pb.dim, Algebra.leftMulMatrix pb.basis pb.gen i j = pb.basis.repr (pb.gen * pb.basis j) i :=
      fun i => Algebra.leftMulMatrix_eq_repr_mul _ _ _ _
    rw [Finset.sum_congr rfl fun i _ => by rw [hC i], hrep k]
    simp only [pb, PowerBasis.coe_basis, AdjoinRoot.powerBasis_gen]
    rw [← pow_succ', map_pow, AdjoinRoot.lift_root, pow_succ']
  obtain ⟨hAd, hH, hHd, hpres⟩ := GlobalTheory.GlobHerm.vandermonde_diag_herm (Cm.map τ) l hl h1 hVA
  have hinv : (Cm.map τ)⁻¹ = Cm⁻¹.map τ := by
    apply inv_eq_left_inv
    have hCd : Cm.det ≠ 0 := by
      intro h; apply hAd
      have := RingHom.map_det τ Cm
      rw [h, map_zero] at this
      exact this.symm
    rw [← Matrix.map_mul, nonsing_inv_mul Cm (isUnit_iff_ne_zero.2 hCd), Matrix.map_one _ (map_zero τ) (map_one τ)]
  have hHm : H.map τ = (vandermonde l)ᴴ * vandermonde l := by
    rw [← hH]
    ext i j
    simp only [map_apply, of_apply, H]
    rw [AddMonoidHom.map_trace τ, hinv]
    congr 1
    change τ.mapMatrix _ = _
    rw [map_mul, map_pow, map_pow]
    rfl
  have hinj : Function.Injective (fun M : Matrix (Fin P.natDegree) (Fin P.natDegree) E => M.map τ) :=
    Matrix.map_injective τ.injective
  have hcT : ∀ M : Matrix (Fin P.natDegree) (Fin P.natDegree) E,
      (cT (IsCMField.complexConj E).toRingEquiv.toRingHom M).map τ = (M.map τ)ᴴ := by
    intro M; ext i j
    simp only [cT, map_apply, transpose_apply, conjTranspose_apply, hτc]
    rfl
  refine ⟨Cm, H, ?_, ?_, ?_, ?_, ?_⟩
  · refine (charpoly_leftMulMatrix pb).trans ?_
    rw [AdjoinRoot.powerBasis_gen, AdjoinRoot.minpoly_root hP0, hmon.leadingCoeff, inv_one,
      Polynomial.C_1, mul_one]
  · intro h; apply hAd
    have := RingHom.map_det τ Cm
    rw [h, map_zero] at this
    exact this.symm
  · intro h; apply hHd
    have := RingHom.map_det τ H
    rw [h, map_zero] at this
    rw [← hHm]; exact this.symm
  · apply hinj
    simp only
    rw [hcT, hHm, conjTranspose_mul, conjTranspose_conjTranspose]
  · apply hinj
    simp only
    rw [Matrix.map_mul, Matrix.map_mul, hcT, hHm, hpres]
end GlobalTheory.GlobHerm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixCharpolyPreservingHermitianFormCMStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter Formalism.UG GlobalTheory.BCT
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_matrix_charpoly_preserving_hermitian_form_CM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : E[X]), P ∈ Ell E n → ∃ C H : Matrix (Fin n) (Fin n) E, C.charpoly = P ∧ C.det ≠ 0 ∧ H.det ≠ 0 ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom H = H ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom C * H * C = H := by
  first | exact @GlobalTheory.GlobHerm.exists_mat_herm | exact GlobalTheory.GlobHerm.exists_mat_herm | (intros; apply GlobalTheory.GlobHerm.exists_mat_herm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SobolevBoundForSmoothVectors
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SobolevBoundForSmoothVectors
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SobolevGrowth

theorem lintegral_le_of_count {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G)
    [μ.IsMulLeftInvariant] (Γ : Subgroup G) [Countable Γ] {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    {A : Set G} (hA : MeasurableSet A) {h : G → ℝ≥0∞} (hm : Measurable h) (hinv : ∀ γ ∈ Γ, ∀ g, h (γ * g) = h g)
    (M : ℝ) (hM : ∀ y, {γ : G | γ ∈ Γ ∧ γ * y ∈ A}.Finite ∧ (({γ : G | γ ∈ Γ ∧ γ * y ∈ A}.ncard : ℕ) : ℝ) ≤ M) :
    ∫⁻ x in A, h x ∂μ ≤ ENNReal.ofReal M * ∫⁻ x in 𝓕, h x ∂μ := by
  classical
  rw [← lintegral_indicator hA, h𝓕.lintegral_eq_tsum'' (A.indicator h), ← lintegral_tsum, ← lintegral_const_mul _ hm]
  · refine lintegral_mono fun y => ?_
    obtain ⟨hfin, hle⟩ := hM y
    have hfin' : {γ : Γ | (γ : G) * y ∈ A}.Finite := by
      refine Set.Finite.of_finite_image (f := Subtype.val) (hfin.subset ?_) Subtype.val_injective.injOn
      rintro _ ⟨γ, hγ, rfl⟩
      exact ⟨γ.2, hγ⟩
    have hcard : hfin'.toFinset.card = {γ : G | γ ∈ Γ ∧ γ * y ∈ A}.ncard := by
      rw [← Set.ncard_eq_toFinset_card _ hfin', ← Set.ncard_image_of_injective _ Subtype.val_injective]
      congr 1
      ext g
      constructor
      · rintro ⟨γ, hγ, rfl⟩
        exact ⟨γ.2, hγ⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨g, h1⟩, h2, rfl⟩
    rw [tsum_eq_sum (s := hfin'.toFinset)]
    · have : ∀ γ ∈ hfin'.toFinset, A.indicator h (γ • y) = h y := by
        intro γ hγ
        have h1 : (γ : G) * y ∈ A := by simpa using hγ
        change A.indicator h ((γ : G) * y) = h y
        rw [Set.indicator_of_mem h1, hinv _ γ.2]
      rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, hcard]
      gcongr
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal hle
    · intro γ hγ
      have h1 : (γ : G) * y ∉ A := by simpa using hγ
      change A.indicator h ((γ : G) * y) = 0
      exact Set.indicator_of_notMem h1 _
  · intro γ
    exact ((hm.indicator hA).comp (measurable_const_mul (γ : G))).aemeasurable

theorem lintegral_enorm_sq {Q : Type} [MeasurableSpace Q] (ν : Measure Q) (F : Lp ℂ 2 ν) :
    ∫⁻ x, ‖F x‖ₑ ^ 2 ∂ν = ENNReal.ofReal (‖F‖ ^ 2) := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := F) (μ := ν) (p := 2) (by norm_num) (Lp.stronglyMeasurable F).aestronglyMeasurable
  rw [ENNReal.ofReal_pow (norm_nonneg _), Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top F)]
  simp only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_ofNat] at h
  exact h.symm

theorem sum_sq_le {α : Type} (S : List α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    (S.map fun a => f a ^ 2).sum ≤ (S.map f).sum ^ 2 := by
  induction S with
  | nil => simp
  | cons a S ih =>
    have : 0 ≤ (S.map f).sum := List.sum_nonneg (by simpa using fun a _ => hf a)
    simp only [List.map_cons, List.sum_cons]
    nlinarith [hf a, mul_nonneg (hf a) this]

theorem integral_le_of_count {G Q : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSpace Q] (μ : Measure G) [μ.IsMulLeftInvariant]
    (Γ : Subgroup G) [Countable Γ] {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (π : G → Q) (hmk : Measurable π)
    (hπ : ∀ γ ∈ Γ, ∀ g, π (γ * g) = π g) {Ω : Set G} (hΩ : IsCompact Ω) (z : G) (M : ℝ)
    (hM : ∀ y, {γ : G | γ ∈ Γ ∧ ∃ o ∈ Ω, γ * y = z * o}.Finite ∧
      (({γ : G | γ ∈ Γ ∧ ∃ o ∈ Ω, γ * y = z * o}.ncard : ℕ) : ℝ) ≤ M)
    (F : Lp ℂ 2 ((μ.restrict 𝓕).map π)) (φ : G → ℂ) (hφ : Continuous φ) (hr : ∀ᵐ x ∂μ, F (π x) = φ x) :
    ∫ x in Ω, ‖φ (z * x)‖ ^ 2 ∂μ ≤ M ^ 2 * ‖F‖ ^ 2 := by
  have hFm : Measurable fun x => ‖F x‖ₑ ^ 2 := (Lp.stronglyMeasurable F).measurable.eNorm.pow_const 2
  have hA : IsCompact ((fun o => z * o) '' Ω) := hΩ.image (continuous_const_mul z)
  have key := lintegral_le_of_count μ Γ h𝓕 hA.measurableSet (hFm.comp hmk)
    (fun γ hγ g => by simp only [Function.comp, hπ γ hγ g]) (M ^ 2) (fun y => by
      have e : {γ : G | γ ∈ Γ ∧ γ * y ∈ (fun o => z * o) '' Ω} = {γ : G | γ ∈ Γ ∧ ∃ o ∈ Ω, γ * y = z * o} :=
        Set.ext fun γ => and_congr_right fun _ => exists_congr fun _ => and_congr_right fun _ => eq_comm
      rw [e]
      refine ⟨(hM y).1, ?_⟩
      have h1 := (hM y).2
      generalize Set.ncard _ = n at h1
      have h2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast Nat.le_self_pow (by norm_num) n
      exact h2.trans (pow_le_pow_left₀ (Nat.cast_nonneg n) h1 2))
  have e1 : ∫⁻ x in 𝓕, ((fun x => ‖F x‖ₑ ^ 2) ∘ π) x ∂μ = ENNReal.ofReal (‖F‖ ^ 2) := by
    rw [← lintegral_enorm_sq]
    exact (lintegral_map hFm hmk).symm
  have e2 : ∫⁻ x in (fun o => z * o) '' Ω, ((fun x => ‖F x‖ₑ ^ 2) ∘ π) x ∂μ =
      ∫⁻ x in Ω, ‖φ (z * x)‖ₑ ^ 2 ∂μ := by
    rw [((measurePreserving_mul_left μ z).setLIntegral_comp_emb (measurableEmbedding_mulLeft z)
      (fun x => ‖φ x‖ₑ ^ 2) Ω)]
    refine lintegral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [hr] with x hx
    simp only [Function.comp, hx]
  rw [e1, e2, ← ENNReal.ofReal_mul (sq_nonneg _)] at key
  have hc : Continuous fun x => ‖φ (z * x)‖ ^ 2 := (hφ.comp (continuous_const_mul z)).norm.pow 2
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => sq_nonneg _) hc.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) (le_of_eq_of_le ?_ key)
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem le_of_sums {α : Type} (S : List α) (I f : α → ℝ) (a C₁ C₂ n : ℝ) (N : ℕ) (hn : 0 ≤ n)
    (hI : ∀ l, 0 ≤ I l) (hf : ∀ l, 0 ≤ f l) (h1 : a ^ 2 ≤ C₁ * (S.map I).sum)
    (h2 : ∀ l ∈ S, I l ≤ (C₂ * n ^ N) ^ 2 * f l ^ 2) : a ≤ √|C₁| * |C₂| * n ^ N * (S.map f).sum := by
  have h2' : (S.map I).sum ≤ (S.map fun l => (C₂ * n ^ N) ^ 2 * f l ^ 2).sum := List.sum_le_sum h2
  rw [List.sum_map_mul_left] at h2'
  have h3 := sum_sq_le S f hf
  have h0 : 0 ≤ (S.map I).sum := List.sum_nonneg (by simpa using fun a _ => hI a)
  have hT : 0 ≤ (S.map f).sum := List.sum_nonneg (by simpa using fun a _ => hf a)
  refine le_of_sq_le_sq ?_ (by positivity)
  have e : (√|C₁| * |C₂| * n ^ N * (S.map f).sum) ^ 2 = |C₁| * ((C₂ * n ^ N) ^ 2 * (S.map f).sum ^ 2) := by
    rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (abs_nonneg _), sq_abs]
    ring
  rw [e]
  refine h1.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) h0).trans ?_)
  exact mul_le_mul_of_nonneg_left (h2'.trans (mul_le_mul_of_nonneg_left h3 (sq_nonneg _))) (abs_nonneg _)

variable {D : D7}

theorem integral_le_adelic (V : HSp D) {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} (hp : FinPair V μ 𝓕)
    {Ω : Set (GA D V)} (hΩ : IsCompact Ω) (z : GA D V) (M : ℝ)
    (hM : ∀ y, {γ : GA D V | γ ∈ GQ V ∧ ∃ o ∈ Ω, γ * y = z * o}.Finite ∧
      (({γ : GA D V | γ ∈ GQ V ∧ ∃ o ∈ Ω, γ * y = z * o}.ncard : ℕ) : ℝ) ≤ M)
    (F : Lp ℂ 2 (nuQ V μ 𝓕)) (φ : GA D V → ℂ) (hφ : Continuous φ) (hr : Repr V μ 𝓕 F φ) :
    ∫ x in Ω, ‖φ (z * x)‖ ^ 2 ∂μ ≤ M ^ 2 * ‖F‖ ^ 2 := by
  obtain ⟨-, -, _, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have := hp.haar
  exact integral_le_of_count μ (GQ V) hp.fd (autMk V) measurable_quotient_mk''
    (fun γ hγ g => Quotient.sound (QuotientGroup.rightRel_apply.2 (by
      rw [_root_.mul_inv_rev, mul_inv_cancel_left]
      exact (GQ V).inv_mem hγ))) hΩ z M hM F φ hφ hr

theorem level_of_repr (V : HSp D) {μ : Measure (GA D V)} {𝓕 : Set (GA D V)}
    {ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))} (hp : FinPair V μ 𝓕) (hρ : IsReg V μ 𝓕 ρ)
    {F : Lp ℂ 2 (nuQ V μ 𝓕)} {ψ : GA D V → ℂ} (hψ : Continuous ψ) (hr : Repr V μ 𝓕 F ψ) {k : GA D V} (hk : ρ k F = F)
    (g : GA D V) : ψ (g * k) = ψ g := by
  obtain ⟨-, -, -, -, _, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨-, huniq, -, htr, -⟩ := GlobalTheory.T.bounded_automorphic_has_representative D V μ 𝓕 ρ hp hρ
  have h1 := htr F ψ k hr
  rw [hk] at h1
  exact congrFun (huniq F (rTr V k ψ) ψ (hψ.comp (continuous_mul_const k)) hψ h1 hr) g

theorem normInf_nonneg (θ : InfFam D) (V : HSp D) (g : GA D V) : 0 ≤ normInf θ V g := by
  unfold normInf
  positivity

theorem pointwise_growth : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))), FinPair V μ 𝓕 → IsReg V μ 𝓕 ρ → ∀ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) → ∃ (N : ℕ) (S : List (List (D.what₂.Tau × Mt V.rank))), (∀ l ∈ S, ∀ p ∈ l, p.2 ∈ lieAt V p.1) ∧ ∀ x, ∃ C : ℝ, ∀ F ψ, IsSmoothVector' θ V ρ F → (∀ k ∈ U, k ∈ GfC V → ρ k F = F) → Continuous ψ → Repr V μ 𝓕 F ψ → ∀ u ∈ GinfC V, ‖ψ (x * u)‖ ≤ C * normInf θ V u ^ N * (S.map fun l => ‖l.foldr (dL2 θ V ρ) F‖).sum := by
  intro D θ V hθ μ 𝓕 ρ hp hρ U hU
  obtain ⟨S, Ω, C₁, hS, hΩ, hsob⟩ := GlobalTheory.T.local_sobolev_inequality_adelic_unitary D θ V hθ U hU μ hp.haar
  have hcount := GlobalTheory.T.ncard_rationalPoints_translatedCompact_le_pow D θ V hθ Ω hΩ
  refine hcount.elim fun N hN => ?_
  refine ⟨N, S, hS, fun x => ?_⟩
  refine (hN x).elim fun C₂ hC₂ => ?_
  refine ⟨√|C₁| * |C₂|, fun F ψ hF hlev hψ hr u hu => ?_⟩
  obtain ⟨ψ', hr', haut, hsm, hder⟩ := GlobalTheory.T.smooth_vector_automorphic_derivatives D θ V hθ μ 𝓕 ρ hp hρ U hU F hF hlev
  have e : ψ' = ψ := (GlobalTheory.T.bounded_automorphic_has_representative D V μ 𝓕 ρ hp hρ).2.1 F ψ' ψ haut.cont hψ hr' hr
  subst e
  have h1 := hsob ψ' hψ (fun k hk hk' => level_of_repr V hp hρ hψ hr (hlev k hk hk')) (fun l hl => (hder l hl).1) hsm (x * u)
  have h2 := fun l hl => integral_le_adelic V hp hΩ (x * u) _ (hC₂ u hu) _ _ (hder l (hS l hl)).1 (hder l (hS l hl)).2
  have h3 := le_of_sums S
    (fun l => ∫ o in Ω, ‖(l.foldr (fun p f => Rder θ V p.1 p.2 f) ψ') (x * u * o)‖ ^ 2 ∂μ)
    (fun l => ‖l.foldr (dL2 θ V ρ) F‖) ‖ψ' (x * u)‖ C₁ C₂ (normInf θ V u) N (normInf_nonneg θ V u)
    (fun _ => integral_nonneg fun _ => sq_nonneg _) (fun _ => norm_nonneg _) h1 h2
  exact h3

end GlobalTheory.SobolevGrowth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SobolevBoundForSmoothVectorsStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sobolev_bound_for_smooth_vectors : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))), FinPair V μ 𝓕 → IsReg V μ 𝓕 ρ → ∀ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) → ∃ (N : ℕ) (S : List (List (D.what₂.Tau × Mt V.rank))), (∀ l ∈ S, ∀ p ∈ l, p.2 ∈ lieAt V p.1) ∧ ∀ x, ∃ C : ℝ, ∀ F ψ, IsSmoothVector' θ V ρ F → (∀ k ∈ U, k ∈ GfC V → ρ k F = F) → Continuous ψ → Repr V μ 𝓕 F ψ → ∀ u ∈ GinfC V, ‖ψ (x * u)‖ ≤ C * normInf θ V u ^ N * (S.map fun l => ‖l.foldr (dL2 θ V ρ) F‖).sum := by
  first | exact @GlobalTheory.SobolevGrowth.pointwise_growth | exact GlobalTheory.SobolevGrowth.pointwise_growth | (intros; apply GlobalTheory.SobolevGrowth.pointwise_growth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullSumRegroup
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjByCarryingUnitMemPositiveSimilitudeFormGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjByCarryingUnitMemPositiveSimilitudeFormGroup
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory

theorem pair_conj_mem_grp : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (B y : G.Cˣ) (s : ℚ), 0 < s → 0 < ((P.c : ℚˣ) : ℚ) → (P.β : G.C) = algebraMap ℚ G.C s * (y * B * sh G y) → ((y⁻¹ * P.γ * y, P.c) : G.Cˣ × ℚˣ) ∈ grp G B := by
  intro p _ G P B y s hs hc hβ
  refine ⟨?_, hc⟩
  change ((y⁻¹ * P.γ * y : G.Cˣ) : G.C) * B * sh G ((y⁻¹ * P.γ * y : G.Cˣ) : G.C) = algebraMap ℚ G.C (P.c : ℚ) * B
  have hmul : ∀ a b : G.C, sh G (a * b) = sh G b * sh G a := by
    intro a b; simp only [sh, map_mul, MulOpposite.unop_mul]
  have e : sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := by
    rw [← hmul, Units.inv_mul]; simp [sh]
  have hs0 : s ≠ 0 := hs.ne'
  have hβ' : (P.β : G.C) = s • ((y : G.C) * B * sh G y) := by rw [hβ, Algebra.smul_def]
  have hY : (y : G.C) * B * sh G y = s⁻¹ • (P.β : G.C) := by
    rw [hβ', smul_smul, inv_mul_cancel₀ hs0, one_smul]
  have hsim : (P.γ : G.C) * P.β * sh G P.γ = (P.c : ℚ) • (P.β : G.C) := by
    rw [P.sim, Algebra.smul_def]
  rw [Units.val_mul, Units.val_mul, hmul, hmul, ← Algebra.smul_def]
  calc ((y⁻¹ : G.Cˣ) : G.C) * P.γ * y * B * (sh G y * (sh G P.γ * sh G ((y⁻¹ : G.Cˣ) : G.C)))
      = ((y⁻¹ : G.Cˣ) : G.C) * (P.γ * ((y : G.C) * B * sh G y) * sh G P.γ) * sh G ((y⁻¹ : G.Cˣ) : G.C) := by
        simp only [mul_assoc]
    _ = s⁻¹ • (((y⁻¹ : G.Cˣ) : G.C) * ((P.γ : G.C) * P.β * sh G P.γ) * sh G ((y⁻¹ : G.Cˣ) : G.C)) := by
        rw [hY]; simp only [mul_smul_comm, smul_mul_assoc]
    _ = (s⁻¹ * (P.c : ℚ)) • (((y⁻¹ : G.Cˣ) : G.C) * (P.β : G.C) * sh G ((y⁻¹ : G.Cˣ) : G.C)) := by
        rw [hsim, mul_smul]; simp only [mul_smul_comm, smul_mul_assoc]
    _ = (s⁻¹ * (P.c : ℚ) * s) • ((((y⁻¹ : G.Cˣ) : G.C) * y) * B * (sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C))) := by
        rw [hβ', mul_smul (s⁻¹ * (P.c : ℚ)) s]; simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]
    _ = (P.c : ℚ) • (B : G.C) := by
        rw [Units.inv_mul, e, one_mul, mul_one, mul_comm (s⁻¹) _, mul_assoc, inv_mul_cancel₀ hs0, mul_one]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjByCarryingUnitMemPositiveSimilitudeFormGroupStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_by_carrying_unit_mem_positiveSimilitudeFormGroup : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (B y : G.Cˣ) (s : ℚ), 0 < s → 0 < ((P.c : ℚˣ) : ℚ) → (P.β : G.C) = algebraMap ℚ G.C s * (y * B * sh G y) → ((y⁻¹ * P.γ * y, P.c) : G.Cˣ × ℚˣ) ∈ grp G B := by
  first | (exact @GlobalTheory.pair_conj_mem_grp) | (exact GlobalTheory.pair_conj_mem_grp) | (intros; apply GlobalTheory.pair_conj_mem_grp  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelOfConjInGroupOfCommonForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelOfConjInGroupOfCommonForm
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.RelConj

theorem rel_of_conj_in_form : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P P' : Pair G) (B y y' g : G.Cˣ) (s s' sg : ℚ), 0 < s → 0 < s' → 0 < sg → (P.β : G.C) = algebraMap ℚ G.C s * (y * B * sh G y) → (P'.β : G.C) = algebraMap ℚ G.C s' * (y' * B * sh G y') → (g : G.C) * B * sh G g = algebraMap ℚ G.C sg * B → g * (y⁻¹ * P.γ * y) * g⁻¹ = y'⁻¹ * P'.γ * y' → P.Rel P' := by
  intro p _ G P P' B y y' g s s' sg hs hs' hsg hβ hβ' hg hγ
  have shm : ∀ a b : G.C, sh G (a * b) = sh G b * sh G a := fun a b => by simp [sh]
  have hyi : ((y⁻¹ : G.Cˣ) : G.C) * y = 1 := Units.inv_mul y
  have hshy : sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := by
    rw [← shm, hyi]; simp [sh]
  have key : ((y' * g * y⁻¹ : G.Cˣ) : G.C) * P.β * sh G ((y' * g * y⁻¹ : G.Cˣ) : G.C) =
      algebraMap ℚ G.C (s * sg) * (y' * B * sh G y') := by
    rw [hβ, Units.val_mul, Units.val_mul, shm, shm, ← Algebra.smul_def]
    calc (y' : G.C) * g * ((y⁻¹ : G.Cˣ) : G.C) * (s • ((y : G.C) * B * sh G y)) *
          (sh G ((y⁻¹ : G.Cˣ) : G.C) * (sh G g * sh G y'))
        = s • ((y' : G.C) * (g * (((y⁻¹ : G.Cˣ) : G.C) * y) * B * (sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C)) * sh G g) * sh G y') := by
          simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]
      _ = s • ((y' : G.C) * ((g : G.C) * B * sh G g) * sh G y') := by
          rw [hyi, hshy, mul_one, mul_one]
      _ = s • (sg • ((y' : G.C) * B * sh G y')) := by
          rw [hg, ← Algebra.smul_def, mul_smul_comm, smul_mul_assoc]
      _ = _ := by rw [smul_smul, Algebra.smul_def]
  refine ⟨y' * g * y⁻¹, s' / (s * sg), div_pos hs' (mul_pos hs hsg), ?_, ?_⟩
  · rw [key, ← mul_assoc, ← map_mul, div_mul_cancel₀ _ (mul_pos hs hsg).ne', hβ']
  · have e : P'.γ = y' * (y'⁻¹ * P'.γ * y') * y'⁻¹ := by group
    rw [e, ← hγ]; group

end GlobalTheory.RelConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelOfConjInGroupOfCommonFormStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rel_of_conj_in_group_of_common_form : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P P' : Pair G) (B y y' g : G.Cˣ) (s s' sg : ℚ), 0 < s → 0 < s' → 0 < sg → (P.β : G.C) = algebraMap ℚ G.C s * (y * B * sh G y) → (P'.β : G.C) = algebraMap ℚ G.C s' * (y' * B * sh G y') → (g : G.C) * B * sh G g = algebraMap ℚ G.C sg * B → g * (y⁻¹ * P.γ * y) * g⁻¹ = y'⁻¹ * P'.γ * y' → P.Rel P' := by
  first | (exact @GlobalTheory.RelConj.rel_of_conj_in_form) | (exact GlobalTheory.RelConj.rel_of_conj_in_form) | (intros; apply GlobalTheory.RelConj.rel_of_conj_in_form  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjOfRelSimilitudePairsSameForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjOfRelSimilitudePairsSameForm
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.ConjR

variable {p : ℕ} [Fact p.Prime]

theorem sh_mul' (G : HTGroup p) (a b : G.C) : sh G (a * b) = sh G b * sh G a := by
  simp only [sh, map_mul, MulOpposite.unop_mul]

theorem sh_unit_mul_inv (G : HTGroup p) (y : G.Cˣ) : sh G (y : G.C) * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := by
  rw [← sh_mul', Units.inv_mul]; simp [sh]

theorem conj_of_rel (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P P' : Pair G) (B y y' : G.Cˣ) (s s' : ℚ)
    (hs : 0 < s) (hs' : 0 < s')
    (hP : (P.β : G.C) = algebraMap ℚ G.C s * (y * B * sh G y))
    (hP' : (P'.β : G.C) = algebraMap ℚ G.C s' * (y' * B * sh G y')) (hR : P.Rel P') :
    ∃ (g : G.Cˣ) (sg : ℚ), 0 < sg ∧ (g : G.C) * B * sh G g = algebraMap ℚ G.C sg * B ∧
      g * (y⁻¹ * P.γ * y) * g⁻¹ = y'⁻¹ * P'.γ * y' := by
  obtain ⟨z, sr, hsr, hβ, hγ⟩ := hR
  refine ⟨y'⁻¹ * z * y, s' / (s * sr), div_pos hs' (mul_pos hs hsr), ?_, ?_⟩
  · rw [← Algebra.smul_def] at hP hP' hβ ⊢
    set a : G.Cˣ := y'⁻¹
    have E : s' • ((y' : G.C) * B * sh G y') = (sr * s) • ((z : G.C) * (y * B * sh G y) * sh G z) := by
      rw [← hP', hβ, hP, mul_smul, mul_smul_comm, smul_mul_assoc]
    have E2 := congrArg (fun X => (a : G.C) * X * sh G a) E
    have ha1 : (a : G.C) * y' = 1 := Units.inv_mul y'
    have ha2 : sh G (y' : G.C) * sh G a = 1 := sh_unit_mul_inv G y'
    have L : (a : G.C) * (s' • ((y' : G.C) * B * sh G y')) * sh G a = s' • (B : G.C) := by
      rw [mul_smul_comm, smul_mul_assoc]
      congr 1
      calc (a : G.C) * ((y' : G.C) * B * sh G y') * sh G a = ((a : G.C) * y') * B * (sh G y' * sh G a) := by
            simp only [mul_assoc]
        _ = _ := by rw [ha1, ha2, one_mul, mul_one]
    have R : (a : G.C) * ((sr * s) • ((z : G.C) * (y * B * sh G y) * sh G z)) * sh G a =
        (sr * s) • (((a * z * y : G.Cˣ) : G.C) * B * sh G ((a * z * y : G.Cˣ) : G.C)) := by
      rw [mul_smul_comm, smul_mul_assoc]
      congr 1
      simp only [Units.val_mul, sh_mul', mul_assoc]
    rw [L, R] at E2
    have hne : (sr * s) ≠ 0 := (mul_pos hsr hs).ne'
    rw [show s' / (s * sr) = (sr * s)⁻¹ * s' by rw [div_eq_inv_mul, mul_comm s sr], mul_smul, E2, smul_smul,
      inv_mul_cancel₀ hne, one_smul]
  · rw [hγ]; group
end GlobalTheory.LKCx.ConjR
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjOfRelSimilitudePairsSameFormStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_of_rel_similitude_pairs_same_form : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P P' : Pair G) (B y y' : G.Cˣ) (s s' : ℚ), 0 < s → 0 < s' → (P.β : G.C) = algebraMap ℚ G.C s * (y * B * sh G y) → (P'.β : G.C) = algebraMap ℚ G.C s' * (y' * B * sh G y') → P.Rel P' → ∃ (g : G.Cˣ) (sg : ℚ), 0 < sg ∧ (g : G.C) * B * sh G g = algebraMap ℚ G.C sg * B ∧ g * (y⁻¹ * P.γ * y) * g⁻¹ = y'⁻¹ * P'.γ * y' := by
  first | (exact @GlobalTheory.LKCx.ConjR.conj_of_rel) | (exact GlobalTheory.LKCx.ConjR.conj_of_rel) | (intros; apply GlobalTheory.LKCx.ConjR.conj_of_rel  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumRegroupFibreBij
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumRegroupFibreBij
namespace GlobalTheory

theorem finsum_regroup_fibre_bij {α ι : Type} {κ : ι → Type} (U : α → ℂ)
    (W : (i : ι) → κ i → ℂ) (π : α → ι) (Φ : (i : ι) → α → κ i)
    (hU : (Function.support U).Finite)
    (hval : ∀ a, U a ≠ 0 → W (π a) (Φ (π a) a) = U a)
    (hinj : ∀ a a', U a ≠ 0 → U a' ≠ 0 → π a' = π a → Φ (π a) a = Φ (π a) a' → a = a')
    (hsurj : ∀ i c, W i c ≠ 0 → ∃ a, π a = i ∧ U a ≠ 0 ∧ Φ i a = c) :
    ∑ᶠ a, U a = ∑ᶠ i, ∑ᶠ c, W i c := by
  classical
  set S : Finset α := hU.toFinset with hS
  have hmem : ∀ a, a ∈ S ↔ U a ≠ 0 := fun a => by simp [hS]
  have hin : ∀ i, ∑ᶠ c, W i c = ∑ a ∈ S.filter (fun a => π a = i), U a := by
    intro i
    have h1 : Function.support (W i) ⊆
        ((S.filter (fun a => π a = i)).image (Φ i) : Finset (κ i)) := by
      intro c hc
      obtain ⟨a, ha, hUa, hac⟩ := hsurj i c hc
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_filter]
      exact ⟨a, ⟨(hmem a).2 hUa, ha⟩, hac⟩
    rw [finsum_eq_sum_of_support_subset _ h1, Finset.sum_image]
    · refine Finset.sum_congr rfl fun a ha => ?_
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.1 ha
      subst ha2
      exact hval a ((hmem a).1 ha1)
    · intro a ha a' ha' h
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.1 ha
      obtain ⟨ha1', ha2'⟩ := Finset.mem_filter.1 ha'
      subst ha2
      exact hinj a a' ((hmem a).1 ha1) ((hmem a').1 ha1') ha2' h
  simp only [hin]
  have h2 : Function.support (fun i => ∑ a ∈ S.filter (fun a => π a = i), U a) ⊆
      (S.image π : Finset ι) := by
    intro i hi
    obtain ⟨a, ha, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
    obtain ⟨ha1, ha2⟩ := Finset.mem_filter.1 ha
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
    exact ⟨a, ha1, ha2⟩
  rw [finsum_eq_sum_of_support_subset _ h2, finsum_eq_sum U hU,
    Finset.sum_fiberwise_of_maps_to (fun a ha => Finset.mem_image_of_mem π ha)]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumRegroupFibreBijStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_eq_finsum_finsum_of_fibre_bij : ∀ {α ι : Type} {κ : ι → Type} (U : α → ℂ) (W : (i : ι) → κ i → ℂ) (π : α → ι) (Φ : (i : ι) → α → κ i), (Function.support U).Finite → (∀ a, U a ≠ 0 → W (π a) (Φ (π a) a) = U a) → (∀ a a', U a ≠ 0 → U a' ≠ 0 → π a' = π a → Φ (π a) a = Φ (π a) a' → a = a') → (∀ i c, W i c ≠ 0 → ∃ a, π a = i ∧ U a ≠ 0 ∧ Φ i a = c) → ∑ᶠ a, U a = ∑ᶠ i, ∑ᶠ c, W i c := by
  first | (exact @GlobalTheory.finsum_regroup_fibre_bij) | (exact GlobalTheory.finsum_regroup_fibre_bij) | (intros; apply GlobalTheory.finsum_regroup_fibre_bij  <;> assumption)
end
end

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.Regroup

variable {p : ℕ} [Fact p.Prime]

def formOf {G : HTGroup p} (P : Pair G) : Form G := ⟨P.β, P.sym, P.trivAf, P.trivR⟩

def ofGrp {G : HTGroup p} (F : Form G) (r : grp G F.β)
    (h : (minpoly G.F (((r : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n ∧
      (minpoly G.F (((r : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable) : Pair G :=
  ⟨F.β, (r : G.Cˣ × ℚˣ).1, (r : G.Cˣ × ℚˣ).2, F.sym, r.2.1, h, F.trivAf, F.trivR⟩

def phi {G : HTGroup p} (q : FCls G) (Q : Cls G) : ConjClasses (grp G (Quot.out q).β) :=
  if h : ∃ y : G.Cˣ, (∃ s : ℚ, 0 < s ∧
      ((Quot.out Q).β : G.C) = algebraMap ℚ G.C s * (y * (Quot.out q).β * sh G y)) ∧
      ((y⁻¹ * (Quot.out Q).γ * y, (Quot.out Q).c) : G.Cˣ × ℚˣ) ∈ grp G (Quot.out q).β
  then ConjClasses.mk ⟨_, h.choose_spec.2⟩ else ConjClasses.mk 1

theorem phi_spec {G : HTGroup p} (q : FCls G) (Q : Cls G) (y : G.Cˣ) (s : ℚ) (hs : 0 < s)
    (hβ : ((Quot.out Q).β : G.C) = algebraMap ℚ G.C s * (y * (Quot.out q).β * sh G y))
    (hm : ((y⁻¹ * (Quot.out Q).γ * y, (Quot.out Q).c) : G.Cˣ × ℚˣ) ∈ grp G (Quot.out q).β) :
    ∃ y₁ : G.Cˣ, ∃ s₁ : ℚ, 0 < s₁ ∧
      ((Quot.out Q).β : G.C) = algebraMap ℚ G.C s₁ * (y₁ * (Quot.out q).β * sh G y₁) ∧
      ∃ hm₁ : ((y₁⁻¹ * (Quot.out Q).γ * y₁, (Quot.out Q).c) : G.Cˣ × ℚˣ) ∈ grp G (Quot.out q).β,
        phi q Q = ConjClasses.mk ⟨_, hm₁⟩ := by
  have h : ∃ y : G.Cˣ, (∃ s : ℚ, 0 < s ∧
      ((Quot.out Q).β : G.C) = algebraMap ℚ G.C s * (y * (Quot.out q).β * sh G y)) ∧
      ((y⁻¹ * (Quot.out Q).γ * y, (Quot.out Q).c) : G.Cˣ × ℚˣ) ∈ grp G (Quot.out q).β := ⟨y, ⟨s, hs, hβ⟩, hm⟩
  obtain ⟨⟨s₁, hs₁, hβ₁⟩, hm₁⟩ := h.choose_spec
  exact ⟨h.choose, s₁, hs₁, hβ₁, hm₁, by rw [phi, dite_eq_left h]⟩

end GlobalTheory.LKCx.Regroup
end
end
