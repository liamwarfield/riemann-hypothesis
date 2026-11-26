module

public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RowHighestLeSpanColWordComplex
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.TraceHermNondegenerate
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantTheorems.TBIdemDen

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.FormPerpVectorMemOfIntegral
open scoped BigOperators Nat

namespace GlobalTheory

section Covector

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]

def pairingMatrix (ε : ι → Module.Dual R M) (e' : ι → M) : Matrix ι ι R :=
  Matrix.of fun a' a => ε a (e' a')

def perpVector (ε : ι → Module.Dual R M) (e' : ι → M) (g : M) : M :=
  (pairingMatrix ε e').det • g
    - ∑ a, ∑ a', ((pairingMatrix ε e').adjugate a a' * ε a g) • e' a'

section Integral

variable {A : Type*} [CommRing A] [Algebra A R]

end Integral

end Covector

section Size

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

private theorem seminorm_sum_le {G κ : Type*} [AddCommGroup G] (ν : AddGroupSeminorm G)
    (s : Finset κ) (x : κ → G) {C : ℝ} (hx : ∀ k ∈ s, ν (x k) ≤ C) :
    ν (∑ k ∈ s, x k) ≤ s.card * C := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.card_insert_of_notMem hk]
    have h1 := map_add_le_add ν (x k) (∑ k ∈ s, x k)
    have h2 := hx k (Finset.mem_insert_self _ _)
    have h3 := ih fun j hj => hx j (Finset.mem_insert_of_mem hj)
    push_cast
    linarith

private theorem ringSeminorm_prod_le {κ : Type*} (ν : RingSeminorm R) (h1 : ν 1 ≤ 1)
    (s : Finset κ) (x : κ → R) {C : ℝ} (hx : ∀ k ∈ s, ν (x k) ≤ C) :
    ν (∏ k ∈ s, x k) ≤ C ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h1
  | insert k s hk ih =>
    rw [Finset.prod_insert hk, Finset.card_insert_of_notMem hk, pow_succ']
    have h2 := hx k (Finset.mem_insert_self _ _)
    have h3 := ih fun j hj => hx j (Finset.mem_insert_of_mem hj)
    exact (map_mul_le_mul ν _ _).trans
      (mul_le_mul h2 h3 (apply_nonneg ν _) ((apply_nonneg ν _).trans h2))

theorem ringSeminorm_det_le {ι : Type*} [Fintype ι] [DecidableEq ι] (ν : RingSeminorm R)
    (h1 : ν 1 ≤ 1) (H : Matrix ι ι R) {C : ℝ} (hH : ∀ i j, ν (H i j) ≤ C) :
    ν H.det ≤ (Fintype.card ι)! * C ^ Fintype.card ι := by
  rw [Matrix.det_apply]
  have := seminorm_sum_le ν.toAddGroupSeminorm Finset.univ
    (fun σ : Equiv.Perm ι => Equiv.Perm.sign σ • ∏ i, H (σ i) i) (C := C ^ Fintype.card ι) (by
      intro σ _
      have h := ringSeminorm_prod_le ν h1 Finset.univ (fun i => H (σ i) i) fun i _ => hH _ _
      rw [Finset.card_univ] at h
      change ν _ ≤ _
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
      · rw [hs, one_smul]; exact h
      · rw [hs, Units.neg_smul, one_smul, map_neg_eq_map]; exact h)
  rwa [Finset.card_univ, Fintype.card_perm] at this

theorem ringSeminorm_adjugate_le {n : ℕ} (ν : RingSeminorm R) (h1 : ν 1 ≤ 1)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) R) {C : ℝ} (hH : ∀ i j, ν (H i j) ≤ C)
    (i j : Fin (n + 1)) : ν (H.adjugate i j) ≤ n ! * C ^ n := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  have h := ringSeminorm_det_le ν h1 (H.submatrix j.succAbove i.succAbove) (C := C)
    fun _ _ => hH _ _
  rw [Fintype.card_fin] at h
  rcases neg_one_pow_eq_or R ((j : ℕ) + i) with hs | hs
  · rw [hs, one_mul]; exact h
  · rw [hs, neg_one_mul, map_neg_eq_map]; exact h

theorem seminorm_perpVector_le {p : ℕ} (ν : RingSeminorm R) (h1 : ν 1 ≤ 1)
    (μ : AddGroupSeminorm M) (hsmul : ∀ (x : R) (v : M), μ (x • v) ≤ ν x * μ v)
    (ε : Fin p → Module.Dual R M) (e' : Fin p → M) (g : M) {C r : ℝ}
    (he : ∀ a a', ν (ε a (e' a')) ≤ C) (hg : ∀ a, ν (ε a g) ≤ C)
    (he' : ∀ a, μ (e' a) ≤ r) (hgr : μ g ≤ r) :
    μ (perpVector ε e' g) ≤ (p + 1)! * C ^ p * r := by
  have hdet := ringSeminorm_det_le ν h1 (pairingMatrix ε e') (C := C) fun i j => he j i
  rw [Fintype.card_fin] at hdet
  have hA : μ ((pairingMatrix ε e').det • g) ≤ p ! * C ^ p * r :=
    (hsmul _ _).trans (mul_le_mul hdet hgr (apply_nonneg μ _) ((apply_nonneg ν _).trans hdet))
  have hB : μ (∑ a, ∑ a', ((pairingMatrix ε e').adjugate a a' * ε a g) • e' a')
      ≤ p * (p ! * C ^ p * r) := by
    cases p with
    | zero => simp
    | succ n =>
      have h := seminorm_sum_le μ Finset.univ
        (fun a => ∑ a', ((pairingMatrix ε e').adjugate a a' * ε a g) • e' a')
        (C := ((n + 1 : ℕ) : ℝ) * (n ! * C ^ n * C * r)) (by
          intro a _
          have h' := seminorm_sum_le μ Finset.univ
            (fun a' => ((pairingMatrix ε e').adjugate a a' * ε a g) • e' a')
            (C := n ! * C ^ n * C * r) (by
              intro a' _
              have hadj := ringSeminorm_adjugate_le ν h1 (pairingMatrix ε e') (C := C)
                (fun i j => he j i) a a'
              have hm : ν ((pairingMatrix ε e').adjugate a a' * ε a g) ≤ n ! * C ^ n * C :=
                (map_mul_le_mul ν _ _).trans
                  (mul_le_mul hadj (hg a) (apply_nonneg ν _) ((apply_nonneg ν _).trans hadj))
              exact (hsmul _ _).trans
                (mul_le_mul hm (he' a') (apply_nonneg μ _) ((apply_nonneg ν _).trans hm)))
          rwa [Finset.card_univ, Fintype.card_fin] at h')
      rw [Finset.card_univ, Fintype.card_fin] at h
      refine h.trans (le_of_eq ?_)
      rw [Nat.factorial_succ]; push_cast; ring
  have hsub := map_sub_le_add μ ((pairingMatrix ε e').det • g)
    (∑ a, ∑ a', ((pairingMatrix ε e').adjugate a a' * ε a g) • e' a')
  rw [perpVector, Nat.factorial_succ]
  push_cast
  linarith

end Size

section Degree

open MvPolynomial

variable {S τ : Type*} [CommRing S]

end Degree

section Form

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
  {σ : R →+* R}

end Form

section InnerProduct

variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℂ V]

end InnerProduct

section Places

variable {R M T : Type*} [CommRing R] [StarRing R] [AddCommGroup M] [Module R M]

end Places

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SpanGridPerpVecEqOrbitSpanOfLe
open MvPolynomial Matrix NumberField
open ReciprocityTheory.ChartRestriction.G.TB (perpVec hMat)
open ReciprocityTheory.ChartRestriction.G.FD (cc)

namespace GlobalTheory.Harm

section Perp

variable {R S : Type} [CommRing R] [CommRing S] {p n : ℕ}

variable (R n) in
def dotPairing (R : Type) [CommRing R] (n : ℕ) : (Fin n → R) →ₗ[R] ((Fin n → R) → R) where
  toFun x y := x ⬝ᵥ y
  map_add' x x' := funext fun y => add_dotProduct x x' y
  map_smul' r x := funext fun y => smul_dotProduct r x y

@[simp] theorem dotPairing_apply (x y : Fin n → R) : dotPairing R n x y = x ⬝ᵥ y := rfl

theorem map_perpVec_apply (f : R →+* S) (h : (Fin n → R) →ₗ[R] ((Fin n → R) → R))
    (h' : (Fin n → S) →ₗ[S] ((Fin n → S) → S)) (e e' : Fin p → Fin n → R) (g : Fin n → R)
    (ε ε' : Fin p → Fin n → S) (γ : Fin n → S) (he' : ∀ a k, f (e' a k) = ε' a k)
    (hg : ∀ k, f (g k) = γ k) (hM : ∀ a' a, f (h (e' a') (e a)) = h' (ε' a') (ε a))
    (hge : ∀ a, f (h g (e a)) = h' γ (ε a)) (k : Fin n) :
    f (perpVec h e e' g k) = perpVec h' ε ε' γ k := by
  have hm : f.mapMatrix (hMat h e e') = hMat h' ε ε' := by
    ext a' a; exact hM a' a
  have hadj (a a') : f ((hMat h e e').adjugate a a') = (hMat h' ε ε').adjugate a a' := by
    rw [← hm, ← RingHom.map_adjugate]; rfl
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [perpVec, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, map_sub, map_mul,
    map_sum, RingHom.map_det, hm, hadj, hg, hge, he']

theorem map_perpVec_dotPairing (f : R →+* S) (ε ε' : Fin p → Fin n → R) (γ : Fin n → R) :
    f ∘ perpVec (dotPairing R n) ε ε' γ =
      perpVec (dotPairing S n) (fun a => f ∘ ε a) (fun a => f ∘ ε' a) (f ∘ γ) :=
  funext fun k => map_perpVec_apply f _ _ _ _ _ _ _ _ (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => by simp [dotProduct]) (fun _ => by simp [dotProduct]) k

theorem adjugate_isHomogeneous {σ : Type*} (M : Matrix (Fin p) (Fin p) (MvPolynomial σ R)) (d : ℕ)
    (hM : ∀ a b, (M a b).IsHomogeneous d) (a b : Fin p) :
    (M.adjugate a b).IsHomogeneous ((p - 1) * d) := by
  rw [adjugate_apply]
  have := det_isWeightedHomogeneous (1 : σ → ℕ) (M.updateRow b (Pi.single a 1))
    (fun i => if i = b then 0 else d) (fun i j => by
      by_cases hi : i = b
      · subst hi
        rw [updateRow_self, if_pos rfl, Pi.single_apply]
        split_ifs
        · exact isWeightedHomogeneous_one _ _
        · exact isWeightedHomogeneous_zero _ _ _
      · rw [updateRow_ne hi, if_neg hi]; exact hM i j)
  change IsWeightedHomogeneous 1 _ _
  convert this using 1
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, Finset.filter_ne',
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin, smul_eq_mul]

theorem perpVec_dotPairing_isHomogeneous {σ : Type} (ε ε' : Fin p → Fin n → MvPolynomial σ R)
    (γ : Fin n → MvPolynomial σ R) (hε : ∀ a k, (ε a k).IsHomogeneous 1)
    (hε' : ∀ a k, (ε' a k).IsHomogeneous 1) (hγ : ∀ k, (γ k).IsHomogeneous 1) (k : Fin n) :
    (perpVec (dotPairing _ n) ε ε' γ k).IsHomogeneous (2 * p + 1) := by
  have hM (a' a) : (hMat (dotPairing _ n) ε ε' a' a).IsHomogeneous 2 :=
    show (∑ k, ε' a' k * ε a k).IsHomogeneous 2 from
      IsHomogeneous.sum _ _ _ fun k _ => (hε' a' k).mul (hε a k)
  have hge (a) : (dotPairing _ n γ (ε a)).IsHomogeneous 2 :=
    IsHomogeneous.sum _ _ _ fun k _ => (hγ k).mul (hε a k)
  have hdet : (hMat (dotPairing _ n) ε ε').det.IsHomogeneous (2 * p) := by
    have := det_isWeightedHomogeneous (1 : σ → ℕ) _ (fun _ => 2) hM
    simpa [mul_comm, IsHomogeneous] using this
  simp only [perpVec, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  refine (hdet.mul (hγ k)).sub (IsHomogeneous.sum _ _ _ fun a _ => IsHomogeneous.sum _ _ _
    fun a' _ => ?_)
  have := ((adjugate_isHomogeneous _ 2 hM a a').mul (hge a)).mul (hε' a' k)
  have hp := a.pos
  rwa [show (p - 1) * 2 + 2 + 1 = 2 * p + 1 by omega] at this

end Perp

section Param

variable {K : Type*} [CommRing K] {σ ω T κ : Type*} {p q : ℕ}

noncomputable def swapVars : MvPolynomial ω (MvPolynomial σ K) →+* MvPolynomial σ (MvPolynomial ω K) :=
  eval₂Hom (MvPolynomial.map C) fun v => C (X v)

theorem eval_swapVars (x : σ → K) (F : MvPolynomial ω (MvPolynomial σ K)) :
    eval (fun i => C (x i)) (swapVars F) = MvPolynomial.map (eval x) F := by
  have : (eval fun i => (C (x i) : MvPolynomial ω K)).comp swapVars = MvPolynomial.map (eval x) := by
    ext1
    · ext1
      · ext1 r; simp [swapVars]
      · simp [swapVars]
    · simp [swapVars]
  exact DFunLike.congr_fun this F

variable [Fintype κ]

theorem swapVars_rowForm_isHomogeneous (t : T) (r : Fin p ⊕ Fin q) (u : κ → MvPolynomial σ K)
    {d : ℕ} (hu : ∀ k, (u k).IsHomogeneous d) : (swapVars (rowForm t r u)).IsHomogeneous d := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [rowForm_apply, map_sum]
  refine IsHomogeneous.sum _ _ _ fun k _ => ?_
  simp only [swapVars, map_mul, eval₂Hom_C, eval₂Hom_X']
  simpa using ((hu k).map C).mul (isHomogeneous_C σ (X (t, r, k) : Poly K T p q κ))

theorem swapVars_minorProd_isHomogeneous [Fintype T] (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (ε : T → Fin p → κ → MvPolynomial σ K) (φ : T → Fin q → κ → MvPolynomial σ K) {d d' : ℕ}
    (hε : ∀ t a k, (ε t a k).IsHomogeneous d) (hφ : ∀ t b k, (φ t b k).IsHomogeneous d') :
    (swapVars (minorProd c c' ε φ)).IsHomogeneous
      (∑ t, (d * partSize (c t) + d' * partSize (c' t))) := by
  simp only [minorProd, map_prod, map_mul, map_pow]
  refine IsHomogeneous.prod _ _ _ fun t _ => IsHomogeneous.mul ?_ ?_
  · rw [partSize, Finset.mul_sum]
    refine IsHomogeneous.prod _ _ _ fun i _ => ?_
    rw [← mul_assoc]
    refine IsHomogeneous.pow ?_ _
    rw [xMinor, RingHom.map_det]
    have := det_isWeightedHomogeneous (1 : σ → ℕ) (swapVars.mapMatrix (Matrix.of
      fun a b : Fin (i.val + 1) => (xForm t (lead i a) (ε t (lead i b)) : Poly _ T p q κ)))
      (fun _ => d) fun a b => swapVars_rowForm_isHomogeneous t _ _ (hε t _)
    simpa [mul_comm, IsHomogeneous] using this
  · rw [partSize, Finset.mul_sum]
    refine IsHomogeneous.prod _ _ _ fun i _ => ?_
    rw [← mul_assoc]
    refine IsHomogeneous.pow ?_ _
    rw [yMinor, RingHom.map_det]
    have := det_isWeightedHomogeneous (1 : σ → ℕ) (swapVars.mapMatrix (Matrix.of
      fun a b : Fin (i.val + 1) => (yForm t (lead i a) (φ t (lead i b)) : Poly _ T p q κ)))
      (fun _ => d') fun a b => swapVars_rowForm_isHomogeneous t _ _ (hφ t _)
    simpa [mul_comm, IsHomogeneous] using this

end Param

section Field

variable {R S : Type} [CommRing R] [CommRing S] {T : Type*} [Fintype T] {ι : Type} [Fintype ι]
  {p q n : ℕ}

noncomputable def coordProd (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ) (w w' : T → ι → Fin n → R)
    (x : (Fin p ⊕ Fin p ⊕ Fin q) × ι → R) : Poly R T p q (Fin n) :=
  minorProd c c' (fun t a k => ∑ i, x (Sum.inl a, i) * w' t i k)
    fun t b => perpVec (dotPairing R n) (fun a k => ∑ i, x (Sum.inl a, i) * w' t i k)
      (fun a k => ∑ i, x (Sum.inr (Sum.inl a), i) * w t i k)
      fun k => ∑ i, x (Sum.inr (Sum.inr b), i) * w t i k

theorem map_coordProd (f : R →+* S) (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (w w' : T → ι → Fin n → R) (x : (Fin p ⊕ Fin p ⊕ Fin q) × ι → R) :
    MvPolynomial.map f (coordProd c c' w w' x) =
      coordProd c c' (fun t i k => f (w t i k)) (fun t i k => f (w' t i k)) fun j => f (x j) := by
  simp only [coordProd, map_minorProd, map_perpVec_dotPairing]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Function.comp_def, map_sum, map_mul]

variable {K : Type} [Field K]

theorem coordProd_mem_orbitSpan (hpq : p + q ≤ n) (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (w w' : T → ι → Fin n → K) (x : (Fin p ⊕ Fin p ⊕ Fin q) × ι → K) :
    coordProd c c' w w' x ∈ orbitSpan K hpq c c' :=
  minorProd_mem_orbitSpan hpq c c' fun _ a _ => by
    rw [dotProduct_comm]; exact perpendicular_vector_exists K _ p (dotPairing K n) _ _ _ a

theorem span_range_coordProd (hpq : p + q ≤ n) (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (w w' : T → ι → Fin n → K)
    (hw : ∀ y y' : T → Fin n → K, ∃ x : ι → K,
      (∀ t k, ∑ i, x i * w t i k = y t k) ∧ ∀ t k, ∑ i, x i * w' t i k = y' t k) :
    Submodule.span K (Set.range (coordProd c c' w w')) = orbitSpan K hpq c c' := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact coordProd_mem_orbitSpan hpq c c' w w' x
  rw [orbitSpan_eq_span_linearIndependent]
  refine Submodule.span_mono ?_
  rintro _ ⟨ε, φ, hε, -, hperp, rfl⟩
  choose ε' hε' using fun t a => surjective_mulVecLin_of (hε t) (Pi.single a 1)
  choose x₁ _ hx₁ using fun a => hw 0 fun t => ε t a
  choose x₂ hx₂ _ using fun a => hw (fun t => ε' t a) 0
  choose x₃ hx₃ _ using fun b => hw (fun t => φ t b) 0
  refine ⟨fun j => Sum.elim x₁ (Sum.elim x₂ x₃) j.1 j.2, ?_⟩
  simp only [coordProd, Sum.elim_inl, Sum.elim_inr, hx₁, hx₂, hx₃]
  congr 1
  funext t b
  have hM : hMat (dotPairing K n) (ε t) (ε' t) = 1 := by
    ext a' a
    have := congrFun (hε' t a') a
    rw [one_eq_pi_single, ← this]
    exact dotProduct_comm (ε' t a') (ε t a)
  have := perpendicular_vector_perp K _ p (dotPairing K n) (ε t) (ε' t) (φ t b) fun a => by
    rw [dotPairing_apply, dotProduct_comm]; exact hperp t a b
  rw [hM, det_one, one_smul] at this
  exact this

theorem span_grid_coordProd [CharZero K] (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (w w' : T → ι → Fin n → K) {dg : ℕ} (hdg : (2 * p + 1) * typeDegree c c' ≤ dg) :
    Submodule.span K ((fun x : (Fin p ⊕ Fin p ⊕ Fin q) × ι → ℕ =>
      coordProd c c' w w' fun j => (x j : K)) '' {x | ∀ j, x j ≤ dg}) =
      Submodule.span K (Set.range (coordProd c c' w w')) := by
  let F : MvPolynomial ((Fin p ⊕ Fin p ⊕ Fin q) × ι) (Poly K T p q (Fin n)) :=
    swapVars (coordProd c c' (fun t i k => C (w t i k)) (fun t i k => C (w' t i k)) X)
  have hlin (r : Fin p ⊕ Fin p ⊕ Fin q) (u : ι → K) :
      (∑ i, X (r, i) * C (u i) : MvPolynomial _ K).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun i _ => (isHomogeneous_X K (r, i)).mul (isHomogeneous_C _ (u i))
  have hF : F.IsHomogeneous _ := swapVars_minorProd_isHomogeneous c c' _ _ (d := 1)
    (d' := 2 * p + 1) (fun t a k => hlin _ _) fun t b k =>
      perpVec_dotPairing_isHomogeneous _ _ _ (fun a k => hlin _ _) (fun a k => hlin _ _)
        (fun k => hlin _ _) k
  have hdeg : F.totalDegree ≤ dg := by
    refine hF.totalDegree_le.trans (le_trans ?_ hdg)
    rw [typeDegree, Finset.mul_sum]
    refine Finset.sum_le_sum fun t _ => ?_
    rw [mul_add]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) _
  have hev (x : (Fin p ⊕ Fin p ⊕ Fin q) × ι → K) :
      eval (fun j => C (x j)) F = coordProd c c' w w' x := by
    rw [eval_swapVars, map_coordProd]; simp only [eval_C, eval_X]
  have := span_grid_eval_eq_span_range (A := K) (K := K) dg F
    fun j => (degreeOf_le_totalDegree F j).trans hdeg
  simp only [Algebra.algebraMap_self, RingHom.id_apply, algebraMap_eq, hev] at this
  rw [← this]
  congr 2
  funext x
  rw [← hev]; simp only [map_natCast]

end Field

section Embeddings

theorem exists_sum_mul_embedding_eq {E K J κ ι : Type*} [Field E] [CharZero E] [Field K]
    [Finite J] [Finite κ] [Fintype ι] (σ : J → E →+* K) (hσ : Function.Injective σ)
    (v : ι → κ → E) (hv : Submodule.span ℚ (Set.range v) = ⊤) (y : J → κ → K) :
    ∃ x : ι → K, ∀ j k, ∑ i, x i * σ j (v i k) = y j k := by
  classical
  have := Fintype.ofFinite J
  have := Fintype.ofFinite κ
  let u : (κ → E) → J × κ → K := fun z s => σ s.1 (z s.2)
  let U : Submodule K (J × κ → K) := Submodule.span K (Set.range fun i => u (v i))
  have hU (z : κ → E) : u z ∈ U := by
    have hz : z ∈ Submodule.span ℚ (Set.range v) := hv ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z hz => obtain ⟨i, rfl⟩ := hz; exact Submodule.subset_span ⟨i, rfl⟩
    | zero => convert U.zero_mem; ext s; simp [u]
    | add z z' _ _ h h' => convert U.add_mem h h'; ext s; simp [u]
    | smul r z _ h => convert U.smul_mem (r : K) h; ext s; simp [u, Rat.smul_def]
  have hind : LinearIndependent K fun j => (σ j : E → K) :=
    (linearIndependent_monoidHom E K).comp (fun j => (σ j : E →* K)) fun j j' e =>
      hσ (RingHom.ext fun a => DFunLike.congr_fun e a)
  have hy : (fun s : J × κ => y s.1 s.2) ∈ U := by
    rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff U]
    intro l hl
    have h0 (j k) : l (Pi.single (j, k) 1) = 0 := by
      refine Fintype.linearIndependent_iff.1 hind (fun j => l (Pi.single (j, k) 1)) ?_ j
      funext a
      have h1 := (Submodule.mem_dualAnnihilator l).1 hl _ (hU (Pi.single k a))
      have h2 : u (Pi.single k a) = ∑ j, σ j a • Pi.single (j, k) 1 := by
        ext ⟨j', k'⟩
        by_cases hk : k' = k <;> simp [u, Finset.sum_apply, Pi.single_apply, hk]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [h2, map_sum] at h1
      simpa [mul_comm] using h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.univ_sum_single (fun s : J × κ => y s.1 s.2), map_sum]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [← mul_one (y s.1 s.2), ← smul_eq_mul, Pi.single_smul', map_smul, h0, smul_zero]
  obtain ⟨x, hx⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hy
  exact ⟨x, fun j k => by simpa [u] using congrFun hx (j, k)⟩

end Embeddings

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {K : Type} [Field K] [CharZero K]
  {T : Type*} [Fintype T] {ι : Type} [Fintype ι] {p q n : ℕ}

theorem span_grid_perpVec_eq_orbitSpan_of_le (τ : T → E →+* K)
    (hτ : Function.Injective fun s : T × Bool => fun x : E => τ s.1 (if s.2 then cc x else x))
    (hpq : p + q ≤ n) (h : (Fin n → E) →ₗ[E] ((Fin n → E) → E))
    (hh : ∀ x y, h x y = ∑ k, x k * cc (y k)) (v : ι → Fin n → E)
    (hv : Submodule.span ℚ (Set.range v) = ⊤) (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ) {dg : ℕ}
    (hdg : (2 * p + 1) * typeDegree c c' ≤ dg) :
    Submodule.span K {P | ∃ (A A' : Fin p → ι → ℕ) (B : Fin q → ι → ℕ),
      (∀ a i, A a i ≤ dg) ∧ (∀ a i, A' a i ≤ dg) ∧ (∀ b i, B b i ≤ dg) ∧
      P = minorProd c c' (fun t a k => τ t (cc ((∑ i, (A a i : E) • v i) k)))
        fun t b k => τ t (perpVec h (fun a => ∑ i, (A a i : E) • v i)
          (fun a => ∑ i, (A' a i : E) • v i) (∑ i, (B b i : E) • v i) k)} =
      orbitSpan K hpq c c' := by
  let γ : E →+* E := (IsCMField.complexConj E : E ≃ₐ[_] E)
  have hγ (x) : cc x = γ x := rfl
  let σ : T × Bool → E →+* K := fun s => if s.2 then (τ s.1).comp γ else τ s.1
  have hσ : Function.Injective σ := fun s s' e => hτ (funext fun x => by
    have := DFunLike.congr_fun e x
    obtain ⟨t, _ | _⟩ := s <;> obtain ⟨t', _ | _⟩ := s' <;> exact this)
  rw [← span_range_coordProd hpq c c' (fun t i k => τ t (v i k)) (fun t i k => τ t (γ (v i k)))
    fun y y' => by
      obtain ⟨x, hx⟩ := exists_sum_mul_embedding_eq σ hσ v hv fun s => if s.2 then y' s.1 else y s.1
      exact ⟨x, fun t => hx (t, false), fun t => hx (t, true)⟩,
    ← span_grid_coordProd c c' _ _ hdg]
  have key (A A' : Fin p → ι → ℕ) (B : Fin q → ι → ℕ) :
      minorProd c c' (fun t a k => τ t (cc ((∑ i, (A a i : E) • v i) k)))
        (fun t b k => τ t (perpVec h (fun a => ∑ i, (A a i : E) • v i)
          (fun a => ∑ i, (A' a i : E) • v i) (∑ i, (B b i : E) • v i) k)) =
      coordProd c c' (fun t i k => τ t (v i k)) (fun t i k => τ t (γ (v i k)))
        fun j => ((Sum.elim A (Sum.elim A' B) j.1 j.2 : ℕ) : K) := by
    rw [coordProd]
    congr 1
    · funext t a k
      simp [hγ]
    · funext t b k
      refine map_perpVec_apply _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ k
      all_goals intros; simp [hγ, hh, dotProduct]
  congr 1
  ext P
  constructor
  · rintro ⟨A, A', B, hA, hA', hB, rfl⟩
    refine ⟨fun j => Sum.elim A (Sum.elim A' B) j.1 j.2, ?_, (key A A' B).symm⟩
    rintro ⟨a | a | b, i⟩
    exacts [hA a i, hA' a i, hB b i]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨fun a i => x (Sum.inl a, i), fun a i => x (Sum.inr (Sum.inl a), i),
      fun b i => x (Sum.inr (Sum.inr b), i), fun _ _ => hx _, fun _ _ => hx _, fun _ _ => hx _, ?_⟩
    rw [key]
    congr 1
    funext j
    obtain ⟨a | a | b, i⟩ := j <;> rfl

theorem span_grid_perpVec_eq_orbitSpan (τ : T → E →+* K)
    (hτ : Function.Injective fun s : T × Bool => fun x : E => τ s.1 (if s.2 then cc x else x))
    (hpq : p + q ≤ n) (h : (Fin n → E) →ₗ[E] ((Fin n → E) → E))
    (hh : ∀ x y, h x y = ∑ k, x k * cc (y k)) (v : ι → Fin n → E)
    (hv : Submodule.span ℚ (Set.range v) = ⊤) (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ) {dg : ℕ}
    (hdg : (2 * (p + q) + 1) * typeDegree c c' ≤ dg) :
    Submodule.span K {P | ∃ (A A' : Fin p → ι → ℕ) (B : Fin q → ι → ℕ),
      (∀ a i, A a i ≤ dg) ∧ (∀ a i, A' a i ≤ dg) ∧ (∀ b i, B b i ≤ dg) ∧
      P = minorProd c c' (fun t a k => τ t (cc ((∑ i, (A a i : E) • v i) k)))
        fun t b k => τ t (perpVec h (fun a => ∑ i, (A a i : E) • v i)
          (fun a => ∑ i, (A' a i : E) • v i) (∑ i, (B b i : E) • v i) k)} =
      orbitSpan K hpq c c' :=
  span_grid_perpVec_eq_orbitSpan_of_le τ hτ hpq h hh v hv c c'
    ((Nat.mul_le_mul_right _ (by omega)).trans hdg)

end CM

end GlobalTheory.Harm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.L1NormRowBlockLeadingMinorProductLe
open scoped BigOperators
open NumberField

namespace GlobalTheory.GridSize

open GlobalTheory.Harm GlobalTheory.MvPoly

section Minor

variable {T : Type*} {p q n : ℕ}

theorem l1Norm_rowBlockLinearForm_le (t : T) (r : Fin p ⊕ Fin q) (v : Fin n → ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hv : ∑ k, ‖v k‖ ^ 2 ≤ R ^ 2) : l1Norm (rowForm t r v) ≤ √(n : ℝ) * R := by
  rw [rowForm_apply]
  refine (l1Norm_linearForm_le (fun k => (t, r, k)) v).trans ?_
  rw [Fintype.card_fin]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_iff.mpr ⟨hR, hv⟩) (Real.sqrt_nonneg _)

theorem l1Norm_det_le_of_entry_bound {σ : Type*} {i N : ℕ} (hi : i ≤ N)
    (M : Matrix (Fin i) (Fin i) (MvPolynomial σ ℂ)) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ a b, l1Norm (M a b) ≤ B) : l1Norm M.det ≤ (N * B) ^ i := by
  refine (l1Norm_det_le_pow M h).trans ?_
  rw [Fintype.card_fin]
  have : (i : ℝ) ≤ N := by exact_mod_cast hi
  gcongr

theorem l1Norm_rowBlockLeadingMinorProduct_le [Fintype T] (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (ε : T → Fin p → Fin n → ℂ) (φ : T → Fin q → Fin n → ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hε : ∀ t a, ∑ k, ‖ε t a k‖ ^ 2 ≤ R ^ 2) (hφ : ∀ t b, ∑ k, ‖φ t b k‖ ^ 2 ≤ R ^ 2)
    {N : ℕ} (hp : p ≤ N) (hq : q ≤ N) :
    l1Norm (minorProd c c' ε φ) ≤ (N * √(n : ℝ) * R) ^ typeDegree c c' := by
  have hB : 0 ≤ √(n : ℝ) * R := by positivity
  rw [minorProd, typeDegree, ← Finset.prod_pow_eq_pow_sum, mul_assoc]
  refine (l1Norm_prod_le _ _).trans (Finset.prod_le_prod₀ (fun _ _ => l1Norm_nonneg _) fun t _ => ?_)
  rw [pow_add]
  refine (l1Norm_mul_le _ _).trans (mul_le_mul ?_ ?_ (l1Norm_nonneg _) (by positivity))
  · refine (l1Norm_prod_pow_le _ _ _ (fun i => (N * (√(n : ℝ) * R)) ^ (i.val + 1))
      fun i _ => ?_).trans_eq ?_
    · exact l1Norm_det_le_of_entry_bound (by have := i.isLt; omega) _ hB
        fun a b => l1Norm_rowBlockLinearForm_le _ _ _ hR (hε _ _)
    · simp only [← pow_mul, Finset.prod_pow_eq_pow_sum, partSize]
  · refine (l1Norm_prod_pow_le _ _ _ (fun i => (N * (√(n : ℝ) * R)) ^ (i.val + 1))
      fun i _ => ?_).trans_eq ?_
    · exact l1Norm_det_le_of_entry_bound (by have := i.isLt; omega) _ hB
        fun a b => l1Norm_rowBlockLinearForm_le _ _ _ hR (hφ _ _)
    · simp only [← pow_mul, Finset.prod_pow_eq_pow_sum, partSize]

end Minor

section Length

variable {E : Type*} [CommRing E] {κ : Type*} [Fintype κ]

noncomputable def embSeminorm (τ : E →+* ℂ) : RingSeminorm E where
  toFun x := ‖τ x‖
  map_zero' := by simp
  add_le' x y := by rw [map_add (f := _)]; exact norm_add_le _ _
  neg' x := by simp
  mul_le' x y := by simp

noncomputable def embVec (τ : E →+* ℂ) : (κ → E) →+ EuclideanSpace ℂ κ where
  toFun v := WithLp.toLp 2 fun k => τ (v k)
  map_zero' := by ext k; simp
  map_add' v w := by ext k; simp

omit [Fintype κ] in
theorem embVec_smul (τ : E →+* ℂ) (x : E) (v : κ → E) : embVec τ (x • v) = τ x • embVec τ v := by
  ext k; simp [embVec, Pi.smul_apply]

noncomputable def embLength (τ : E →+* ℂ) : AddGroupSeminorm (κ → E) where
  toFun v := ‖embVec τ v‖
  map_zero' := by simp
  add_le' x y := by rw [map_add (f := _)]; exact norm_add_le _ _
  neg' x := by simp

theorem embLength_apply (τ : E →+* ℂ) (v : κ → E) : embLength τ v = ‖embVec τ v‖ := rfl

theorem embLength_sq (τ : E →+* ℂ) (v : κ → E) : embLength τ v ^ 2 = ∑ k, ‖τ (v k)‖ ^ 2 := by
  rw [embLength_apply, EuclideanSpace.norm_sq_eq]; rfl

theorem embLength_smul (τ : E →+* ℂ) (x : E) (v : κ → E) :
    embLength τ (x • v) = ‖τ x‖ * embLength τ v := by
  rw [embLength_apply, embVec_smul, norm_smul, embLength_apply]

theorem embLength_le_abs (τ : E →+* ℂ) {v : κ → E} {R : ℝ} (h : ∑ k, ‖τ (v k)‖ ^ 2 ≤ R ^ 2) :
    embLength τ v ≤ |R| :=
  (le_abs_self _).trans (sq_le_sq.mp (by rwa [embLength_sq]))

theorem sum_sq_le_of_embLength_le (τ : E →+* ℂ) {v : κ → E} {R : ℝ} (h : embLength τ v ≤ |R|) :
    ∑ k, ‖τ (v k)‖ ^ 2 ≤ R ^ 2 := by
  rw [← embLength_sq, ← sq_abs R]
  exact pow_le_pow_left₀ (apply_nonneg _ _) h 2

theorem norm_emb_sum_mul_le (τ : E →+* ℂ) (s : E → E) (hs : ∀ x, ‖τ (s x)‖ = ‖τ x‖)
    (x y : κ → E) : ‖τ (∑ k, x k * s (y k))‖ ≤ embLength τ x * embLength τ y := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine (norm_sum_le _ _).trans ?_
  simp only [map_mul, norm_mul, hs]
  refine (le_abs_self _).trans (abs_le_of_sq_le_sq ?_
    (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)))
  rw [mul_pow, embLength_sq, embLength_sq]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

theorem sum_sq_combination_le (τ : E →+* ℂ) {ι : Type*} [Fintype ι] (v : ι → κ → E) {ρ : ℝ}
    (hv : ∀ i, ∑ k, ‖τ (v i k)‖ ^ 2 ≤ ρ ^ 2) (A : ι → ℕ) {d : ℕ} (hA : ∀ i, A i ≤ d) :
    ∑ k, ‖τ ((∑ i, (A i : E) • v i) k)‖ ^ 2 ≤ ((Fintype.card ι : ℝ) * d * ρ) ^ 2 := by
  apply sum_sq_le_of_embLength_le
  set_option synthInstance.maxHeartbeats 100000 in
    rw [embLength_apply, map_sum, abs_mul, abs_mul, Nat.abs_cast, Nat.abs_cast, mul_assoc,
    ← nsmul_eq_mul, ← Finset.card_univ]
  refine (norm_sum_le _ _).trans (Finset.sum_le_card_nsmul _ _ _ fun i _ => ?_)
  rw [← embLength_apply, embLength_smul, map_natCast, Complex.norm_natCast]
  exact mul_le_mul (by exact_mod_cast hA i) (embLength_le_abs τ (hv i)) (apply_nonneg _ _)
    (Nat.cast_nonneg _)

end Length

section Perp

open ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.FD

theorem perpVec_eq_perpVector {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {p : ℕ}
    (h : V →ₗ[R] (V → R)) (e e' : Fin p → V) (g : V) :
    perpVec h e e' g = perpVector (fun a => (LinearMap.proj (e a)).comp h) e' g := rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {p n : ℕ}

theorem sum_sq_perpVec_le (τ : E →+* ℂ) (h : (Fin n → E) →ₗ[E] ((Fin n → E) → E))
    (hh : ∀ x y, h x y = ∑ k, x k * cc (y k)) (e e' : Fin p → Fin n → E) (g : Fin n → E) {R : ℝ}
    (he : ∀ a, ∑ k, ‖τ (e a k)‖ ^ 2 ≤ R ^ 2) (he' : ∀ a, ∑ k, ‖τ (e' a k)‖ ^ 2 ≤ R ^ 2)
    (hg : ∑ k, ‖τ (g k)‖ ^ 2 ≤ R ^ 2) :
    ∑ k, ‖τ (perpVec h e e' g k)‖ ^ 2 ≤ (((p + 1).factorial : ℝ) * R ^ (2 * p + 1)) ^ 2 := by
  have hs : ∀ x, ‖τ (cc x)‖ = ‖τ x‖ := fun x => by
    rw [cc, IsCMField.complexEmbedding_complexConj, Complex.norm_conj]
  have key : ∀ u v, embLength τ u ≤ |R| → embLength τ v ≤ |R| → ‖τ (h u v)‖ ≤ |R| ^ 2 :=
    fun u v hu hv => by
      rw [hh, sq]
      exact (norm_emb_sum_mul_le τ cc hs u v).trans
        (mul_le_mul hu hv (apply_nonneg _ _) (abs_nonneg _))
  apply sum_sq_le_of_embLength_le
  rw [perpVec_eq_perpVector, abs_mul, Nat.abs_cast, abs_pow, pow_succ, pow_mul, ← mul_assoc]
  exact seminorm_perpVector_le (embSeminorm τ) (by change ‖τ 1‖ ≤ 1; simp) (embLength τ)
    (fun x v => (embLength_smul τ x v).le) _ e' g
    (fun a a' => key _ _ (embLength_le_abs τ (he' a')) (embLength_le_abs τ (he a)))
    (fun a => key _ _ (embLength_le_abs τ hg) (embLength_le_abs τ (he a)))
    (fun a => embLength_le_abs τ (he' a)) (embLength_le_abs τ hg)

end Perp

end GlobalTheory.GridSize
end

open NumberField ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.TB (perpVec)

namespace GlobalTheory.Harm

open GlobalTheory.MvPoly GlobalTheory.GridSize

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

variable (E n) in
noncomputable def conjVec : (Fin n → E) →ₛₗ[((IsCMField.ringOfIntegersComplexConj E).toRingEquiv :
    𝓞 E →+* 𝓞 E)] (Fin n → E) where
  toFun v k := cc (v k)
  map_add' v w := funext fun k => map_add (IsCMField.complexConj E) (v k) (w k)
  map_smul' a v := funext fun k => map_mul (IsCMField.complexConj E) (a : E) (v k)

@[simp] theorem conjVec_apply (v : Fin n → E) (k : Fin n) : conjVec E n v k = cc (v k) := rfl

@[simp] theorem _root_.GlobalTheory.Harm.conjVec_conjVec (v : Fin n → E) :
    _root_.GlobalTheory.Harm.conjVec E n (_root_.GlobalTheory.Harm.conjVec E n v) = v := by
  funext k
  exact _root_.GlobalTheory.TraceDualMin.cc_cc (v k)

theorem _root_.GlobalTheory.Harm.herm_conjVec (v w : Fin n → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 (_root_.GlobalTheory.Harm.conjVec E n v) (_root_.GlobalTheory.Harm.conjVec E n w)
      = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 w v := by
  simp only [_root_.GlobalTheory.DualFamily.herm_one_eq, _root_.GlobalTheory.Harm.conjVec_apply,
    _root_.GlobalTheory.TraceDualMin.cc_cc]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

noncomputable def conjLattice (Λ : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E) (Fin n → E) :=
  Λ.map (conjVec E n)

variable {Λ : Submodule (𝓞 E) (Fin n → E)}

theorem _root_.GlobalTheory.Harm.mem_conjLattice {v : Fin n → E} :
    v ∈ _root_.GlobalTheory.Harm.conjLattice Λ ↔ _root_.GlobalTheory.Harm.conjVec E n v ∈ Λ := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [_root_.GlobalTheory.Harm.conjVec_conjVec]
    exact hw
  · intro hv
    exact ⟨_, hv, _root_.GlobalTheory.Harm.conjVec_conjVec v⟩

theorem _root_.GlobalTheory.Harm.conjLattice_selfDual (hfg : Λ.FG)
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y)) → x ∈ Λ) :
    (_root_.GlobalTheory.Harm.conjLattice Λ).FG ∧
      (∀ x ∈ _root_.GlobalTheory.Harm.conjLattice Λ, ∀ y ∈ _root_.GlobalTheory.Harm.conjLattice Λ, IsIntegral ℤ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y)) ∧
      ∀ x, (∀ y ∈ _root_.GlobalTheory.Harm.conjLattice Λ, IsIntegral ℤ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y)) →
        x ∈ _root_.GlobalTheory.Harm.conjLattice Λ := by
  refine ⟨hfg.map _, ?_, ?_⟩
  · intro x hx y hy
    rw [_root_.GlobalTheory.Harm.mem_conjLattice] at hx hy
    have h := hint _ hy _ hx
    rwa [_root_.GlobalTheory.Harm.herm_conjVec] at h
  · intro x hx
    rw [_root_.GlobalTheory.Harm.mem_conjLattice]
    refine hdual _ fun y hy => ?_
    have hy' : _root_.GlobalTheory.Harm.conjVec E n y ∈ _root_.GlobalTheory.Harm.conjLattice Λ := by
      rw [_root_.GlobalTheory.Harm.mem_conjLattice, _root_.GlobalTheory.Harm.conjVec_conjVec]
      exact hy
    have h := _root_.GlobalTheory.TraceDualMin.isIntegral_cc (hx _ hy')
    rw [← _root_.GlobalTheory.DualFamily.herm_one_symm] at h
    have h2 := _root_.GlobalTheory.Harm.herm_conjVec (E := E) x (_root_.GlobalTheory.Harm.conjVec E n y)
    rw [_root_.GlobalTheory.Harm.conjVec_conjVec] at h2
    rw [h2]
    exact h

omit [IsCMField E] in
theorem _root_.GlobalTheory.Harm.one_le_rdE : 1 ≤ _root_.ReciprocityTheory.ChartRestriction.G.FD.rdE E := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.rdE _root_.ReciprocityTheory.ChartRestriction.G.FD.dE
  apply Real.one_le_rpow _ (by positivity)
  have h : (discr E : ℝ) ≠ 0 := by exact_mod_cast discr_ne_zero E
  have h' : (1 : ℝ) ≤ |((discr E : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs (discr_ne_zero E)
  exact_mod_cast h'

theorem _root_.GlobalTheory.Harm.one_le_fdeg : 1 ≤ _root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E := by
  have h := _root_.GlobalTheory.ShortVectors.finrank_eq (E := E)
  have hpos : 0 < Module.finrank ℚ E := Module.finrank_pos
  omega

theorem _root_.GlobalTheory.Harm.one_le_add_of_one_le_typeDegree {T : Type*} [Fintype T] {p q : ℕ}
    {c : T → Fin p → ℕ} {c' : T → Fin q → ℕ} (ha : 1 ≤ _root_.GlobalTheory.Harm.typeDegree c c') :
    1 ≤ p + q := by
  by_contra hpq
  obtain ⟨rfl, rfl⟩ : p = 0 ∧ q = 0 := by omega
  simp [_root_.GlobalTheory.Harm.typeDegree, _root_.GlobalTheory.Harm.partSize] at ha

variable (E n) in
noncomputable def hermPairing : (Fin n → E) →ₗ[E] ((Fin n → E) → E) where
  toFun x y := herm 1 x y
  map_add' x x' := funext fun y => by simp [herm_one_eq_sum, add_mul, Finset.sum_add_distrib]
  map_smul' r x := funext fun y => TraceDualMin.herm_smul_left r x y

theorem _root_.GlobalTheory.Harm.perpVec_hermPairing_mem
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y)) {p : ℕ}
    {e e' : Fin p → Fin n → E} {g : Fin n → E} (he : ∀ a, e a ∈ Λ) (he' : ∀ a, e' a ∈ Λ)
    (hg : g ∈ Λ) : _root_.ReciprocityTheory.ChartRestriction.G.TB.perpVec (_root_.GlobalTheory.Harm.hermPairing E n) e e' g ∈ Λ := by
  classical
  unfold _root_.ReciprocityTheory.ChartRestriction.G.TB.perpVec
  set M := _root_.ReciprocityTheory.ChartRestriction.G.TB.hMat (_root_.GlobalTheory.Harm.hermPairing E n) e e' with hM
  have hMint : ∀ i j, IsIntegral ℤ (M i j) := fun i j => hint _ (he' i) _ (he j)
  let Mo : Matrix (Fin p) (Fin p) (𝓞 E) := fun i j => ⟨M i j, hMint i j⟩
  have hMo : M = (algebraMap (𝓞 E) E).mapMatrix Mo := by ext i j; rfl
  have key : ∀ (c : 𝓞 E) (x : Fin n → E), x ∈ Λ → ((c : E) • x) ∈ Λ :=
    fun c x hx => Λ.smul_mem c hx
  apply Λ.sub_mem
  · rw [hMo, ← RingHom.map_det]
    exact key _ _ hg
  · refine Λ.sum_mem fun a _ => Λ.sum_mem fun a' _ => ?_
    have hga : IsIntegral ℤ (_root_.GlobalTheory.Harm.hermPairing E n g (e a)) := hint _ hg _ (he a)
    rw [hMo, ← RingHom.map_adjugate]
    have hc : (algebraMap (𝓞 E) E).mapMatrix Mo.adjugate a a'
        * _root_.GlobalTheory.Harm.hermPairing E n g (e a)
        = ((Mo.adjugate a a' * ⟨_, hga⟩ : 𝓞 E) : E) := by
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
      rfl
    rw [hc]
    exact key _ _ (he' a')

end GlobalTheory.Harm
