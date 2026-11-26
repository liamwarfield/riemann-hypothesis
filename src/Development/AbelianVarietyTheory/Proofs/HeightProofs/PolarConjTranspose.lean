module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CommuteGelfandInvariantMatrixUnitsOfGlRel
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.PermutationWordGelfandPolynomialModShorter

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CommutantLiftModStableSelfAdjoint
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CommutantLiftModStableSelfAdjoint
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

namespace GlobalTheory

theorem matrix_exists_sub_mem_trace_orthogonal {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : Submodule ℂ (Matrix ι ι ℂ)) (M : Matrix ι ι ℂ) :
    ∃ M₀ : Matrix ι ι ℂ, M - M₀ ∈ N ∧ ∀ n ∈ N, (nᴴ * M₀).trace = 0 := by
  let e : Matrix ι ι ℂ →ₗ[ℂ] EuclideanSpace ℂ (ι × ι) :=
    { toFun := fun A => WithLp.toLp 2 (fun p : ι × ι => A p.1 p.2)
      map_add' := fun A B => rfl
      map_smul' := fun c A => rfl }
  have hin : ∀ A B : Matrix ι ι ℂ, inner ℂ (e A) (e B) = (Aᴴ * B).trace := by
    intro A B
    simp only [e, LinearMap.coe_mk, AddHom.coe_mk, PiLp.inner_apply, Matrix.trace,
      Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [mul_comm]
    rfl
  obtain ⟨y, hy, z, hz, h⟩ := (N.map e).exists_add_mem_mem_orthogonal (e M)
  obtain ⟨y', hy', rfl⟩ := hy
  refine ⟨M - y', by simpa using hy', fun n hn => ?_⟩
  rw [← hin, map_sub, h, add_sub_cancel_left]
  exact (Submodule.mem_orthogonal _ _).1 hz _ ⟨n, hn, rfl⟩

theorem matrix_commutant_lift_mod_stable :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S : Set (Matrix ι ι ℂ))
      (N : Submodule ℂ (Matrix ι ι ℂ)), (∀ x ∈ S, xᴴ ∈ S) →
      (∀ x ∈ S, ∀ y ∈ N, x * y - y * x ∈ N) → ∀ M : Matrix ι ι ℂ,
      (∀ x ∈ S, x * M - M * x ∈ N) →
      ∃ M₀ : Matrix ι ι ℂ, M - M₀ ∈ N ∧ ∀ x ∈ S, x * M₀ = M₀ * x := by
  intro ι _ _ S N hS hN M hM
  obtain ⟨M₀, h1, h2⟩ := matrix_exists_sub_mem_trace_orthogonal N M
  refine ⟨M₀, h1, fun x hx => ?_⟩
  have hw : x * M₀ - M₀ * x ∈ N := by
    have := N.sub_mem (hM x hx) (hN x hx _ h1)
    convert this using 1
    noncomm_ring
  set w := x * M₀ - M₀ * x with hwdef
  have h3 := h2 _ (hN _ (hS x hx) w hw)
  have h4 : (wᴴ * w).trace = 0 := by
    rw [← h3]
    have : (wᴴ * (M₀ * x)).trace = (x * wᴴ * M₀).trace := by
      rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
    conv_lhs => rw [hwdef, Matrix.mul_sub, ← hwdef]
    rw [Matrix.trace_sub, this]
    simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.sub_mul, Matrix.mul_assoc]
  open scoped ComplexOrder in
  exact sub_eq_zero.1 (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.1 h4)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CommutantLiftModStableSelfAdjointStatement
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutant_lift_mod_stable_selfAdjoint : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S : Set (Matrix ι ι ℂ)) (N : Submodule ℂ (Matrix ι ι ℂ)), (∀ x ∈ S, xᴴ ∈ S) → (∀ x ∈ S, ∀ y ∈ N, x * y - y * x ∈ N) → ∀ M : Matrix ι ι ℂ, (∀ x ∈ S, x * M - M * x ∈ N) → ∃ M₀ : Matrix ι ι ℂ, M - M₀ ∈ N ∧ ∀ x ∈ S, x * M₀ = M₀ * x := by
  first | exact @GlobalTheory.matrix_commutant_lift_mod_stable | exact GlobalTheory.matrix_commutant_lift_mod_stable | (intros; apply GlobalTheory.matrix_commutant_lift_mod_stable <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.MemAdjoinGlActionOfCommuteTensorPerm
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.MemAdjoinGlActionOfCommuteTensorPerm
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

noncomputable section

namespace GlobalTheory.SymmTensor

variable {n d : ℕ}

def tens (X : Fin d → Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ :=
  Matrix.of fun I K => ∏ p, X p (I p) (K p)

def sym (X : Fin d → Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ :=
  ∑ π : Equiv.Perm (Fin d), tens (X ∘ π)

theorem tens_mul (X Y : Fin d → Matrix (Fin n) (Fin n) ℂ) : tens X * tens Y = tens (X * Y) := by
  ext I K
  simp only [tens, Matrix.mul_apply, Matrix.of_apply, Pi.mul_apply, ← Finset.prod_mul_distrib]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

theorem tens_one : tens (1 : Fin d → Matrix (Fin n) (Fin n) ℂ) = 1 := by
  ext I K
  simp only [tens, Matrix.of_apply, Pi.one_apply, Matrix.one_apply]
  rw [Finset.prod_ite_zero]
  simp [funext_iff]

theorem tens_single_apply (p : Fin d) (Y : Matrix (Fin n) (Fin n) ℂ) (I K : Fin d → Fin n) :
    tens (Pi.mulSingle p Y) I K = if ∀ q, q ≠ p → I q = K q then Y (I p) (K p) else 0 := by
  simp only [tens, Matrix.of_apply]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ p), Pi.mulSingle_eq_same]
  have : ∀ q ∈ Finset.univ.erase p, (Pi.mulSingle p Y : Fin d → Matrix (Fin n) (Fin n) ℂ) q (I q) (K q)
      = if I q = K q then 1 else 0 := fun q hq => by
    rw [Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hq), Matrix.one_apply]
  rw [Finset.prod_congr rfl this, Finset.prod_ite_zero]
  simp

theorem sum_tens_single (Y : Matrix (Fin n) (Fin n) ℂ) :
    ∑ p : Fin d, tens (Pi.mulSingle p Y) = ∑ a, ∑ b, Y a b • polar n d a b := by
  ext I K
  simp only [Matrix.sum_apply, tens_single_apply, polar, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul,
    Finset.mul_sum]
  symm
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h : ∀ q, q ≠ p → I q = K q
  · simp [eq_true h, ite_and]
  · simp [eq_false h]

theorem sym_comp (X : Fin d → Matrix (Fin n) (Fin n) ℂ) (σ : Equiv.Perm (Fin d)) : sym (X ∘ σ) = sym X :=
  Fintype.sum_equiv (Equiv.mulLeft σ) _ _ fun _ => rfl

theorem sym_mul (X : Fin d → Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin n) (Fin n) ℂ) :
    sym X * ∑ p : Fin d, tens (Pi.mulSingle p Y) = ∑ i : Fin d, sym (X * Pi.mulSingle i Y) := by
  simp only [sym, Finset.sum_mul, Finset.mul_sum, tens_mul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun π _ => Fintype.sum_equiv π _ _ fun p => ?_
  congr 1
  funext q
  by_cases h : q = p
  · subst h; simp
  · have : π q ≠ π p := fun e => h (π.injective e)
    simp [h, this]

theorem sym_mem (X : Fin d → Matrix (Fin n) (Fin n) ℂ) :
    sym X ∈ Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => polar n d p.1 p.2) := by
  set A := Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => polar n d p.1 p.2)
  suffices H : ∀ s : Finset (Fin d), ∀ X : Fin d → Matrix (Fin n) (Fin n) ℂ, (∀ i ∉ s, X i = 1) → sym X ∈ A from
    H Finset.univ X (by simp)
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro X hX
    obtain rfl : X = 1 := funext fun i => hX i (by simp)
    refine A.sum_mem fun π _ => ?_
    rw [show (1 : Fin d → Matrix (Fin n) (Fin n) ℂ) ∘ π = 1 from rfl, tens_one]
    exact A.one_mem
  | insert j s hj ih =>
    intro X hX
    set Z := Function.update X j 1 with hZ
    have hZ1 : ∀ i ∉ s, Z i = 1 := fun i hi => by
      by_cases h : i = j
      · subst h; simp [hZ]
      · rw [hZ, Function.update_of_ne h]; exact hX i (by simp [h, hi])
    have hP : ∑ p : Fin d, tens (Pi.mulSingle p (X j)) ∈ A := by
      rw [sum_tens_single]
      exact A.sum_mem fun a _ => A.sum_mem fun b _ => A.smul_mem (Algebra.subset_adjoin ⟨(a, b), rfl⟩) _
    have h1 := A.mul_mem (ih Z hZ1) hP
    rw [sym_mul, ← Finset.sum_add_sum_compl s] at h1
    have h2 : ∑ i ∈ s, sym (Z * Pi.mulSingle i (X j)) ∈ A := A.sum_mem fun i hi => ih _ fun k hk => by
      have : k ≠ i := fun e => hk (e ▸ hi)
      simp [hZ1 k hk, this]
    have h3 := A.sub_mem h1 h2
    have h4 : ∀ i ∈ sᶜ, sym (Z * Pi.mulSingle i (X j)) = sym X := fun i hi => by
      have hi : i ∉ s := by simpa using hi
      rw [← sym_comp X (Equiv.swap i j)]
      congr 1
      funext k
      by_cases hki : k = i
      · subst hki; simp [hZ1 k hi]
      · by_cases hkj : k = j
        · subst hkj
          simp [hZ, hki, hX i (by simp [hi, Ne.symm hki])]
        · simp [hZ, hki, hkj, Equiv.swap_apply_of_ne_of_ne hki hkj]
    rw [add_sub_cancel_left, Finset.sum_congr rfl h4, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ] at h3
    have h5 : ((sᶜ.card : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨j, by simpa using hj⟩)
    have := A.smul_mem h3 ((sᶜ.card : ℕ) : ℂ)⁻¹
    rwa [smul_smul, inv_mul_cancel₀ h5, one_smul] at this

theorem tens_unit_apply (I K I' K' : Fin d → Fin n) (π : Equiv.Perm (Fin d)) :
    tens ((fun p => Matrix.single (I p) (K p) (1 : ℂ)) ∘ π) I' K' =
      if I = I' ∘ π.symm then if K = K' ∘ π.symm then 1 else 0 else 0 := by
  simp only [tens, Matrix.of_apply, Function.comp_apply, Matrix.single_apply]
  rw [Finset.prod_ite_zero, ← ite_and]
  simp only [Finset.mem_univ, forall_const, Finset.prod_const_one, forall_and, funext_iff, Function.comp_apply]
  refine if_congr (and_congr ?_ ?_) rfl rfl <;>
  exact ⟨fun h q => by simpa using h (π.symm q), fun h q => by simpa using h (π q)⟩

theorem mem_adjoin_polar (n d : ℕ) (T : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ)
    (hT : ∀ π, T * permMat n d π = permMat n d π * T) :
    T ∈ Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => polar n d p.1 p.2) := by
  set A := Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => polar n d p.1 p.2)
  have h1 : ∀ (π : Equiv.Perm (Fin d)) I K, T (I ∘ π) (K ∘ π) = T I K := fun π I K => by
    have := congrFun (congrFun (hT π) (I ∘ π)) K
    simp only [Matrix.mul_apply, permMat, Matrix.of_apply, mul_ite, ite_mul, mul_one, mul_zero, one_mul, zero_mul,
      π.surjective.injective_comp_right.eq_iff] at this
    simpa using this
  have h2 : ∑ I, ∑ K, T I K • sym (fun p => Matrix.single (I p) (K p) (1 : ℂ)) = ((d.factorial : ℕ) : ℂ) • T := by
    ext I' K'
    simp only [sym, Matrix.sum_apply, Matrix.smul_apply, tens_unit_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
    simp [h1, Fintype.card_perm]
  have h3 : ((d.factorial : ℕ) : ℂ) • T ∈ A :=
    h2 ▸ A.sum_mem fun I _ => A.sum_mem fun K _ => A.smul_mem (sym_mem _) _
  have h5 : ((d.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 d.factorial_ne_zero
  have := A.smul_mem h3 ((d.factorial : ℕ) : ℂ)⁻¹
  rwa [smul_smul, inv_mul_cancel₀ h5, one_smul] at this

end GlobalTheory.SymmTensor

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.MemAdjoinGlActionOfCommuteTensorPermStatement
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_adjoin_glAction_of_commute_tensorPerm : ∀ (n d : ℕ) (T : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ), (∀ π, T * permMat n d π = permMat n d π * T) → T ∈ Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => polar n d p.1 p.2) := by
  first | exact @GlobalTheory.SymmTensor.mem_adjoin_polar | exact GlobalTheory.SymmTensor.mem_adjoin_polar | (intros; apply GlobalTheory.SymmTensor.mem_adjoin_polar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CommutatorGlGeneratorTensorWordMapMatrixUnits
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CommutatorGlGeneratorTensorWordMapMatrixUnits
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

namespace GlobalTheory.SmoothForms

theorem commutator_prod_ofFn {A : Type} [Ring A] (x : A) :
    ∀ (d : ℕ) (f : Fin d → A), x * (List.ofFn f).prod - (List.ofFn f).prod * x =
      ∑ p, (List.ofFn (Function.update f p (x * f p - f p * x))).prod
  | 0, f => by simp
  | d + 1, f => by
    have ih := commutator_prod_ofFn x d (fun i => f i.succ)
    have h : ∀ (p : Fin d) (y : A), (fun i : Fin d => Function.update f p.succ y i.succ) =
        Function.update (fun i => f i.succ) p y := fun p y => by
      funext i
      by_cases h : i = p
      · subst h; simp
      · simp [Function.update_of_ne h, Function.update_of_ne (fun h' => h (Fin.succ_injective _ h'))]
    rw [Fin.sum_univ_succ]
    simp only [List.ofFn_succ, List.prod_cons, Function.update_self, h,
      Function.update_of_ne (Fin.succ_ne_zero _), Function.update_of_ne (Fin.succ_ne_zero _).symm]
    rw [← Finset.mul_sum, ← ih]
    noncomm_ring

theorem sum_polar_left {A : Type} [AddCommGroup A] [Module ℂ A] {n d : ℕ} (a b : Fin n) (I : Fin d → Fin n)
    (g : (Fin d → Fin n) → A) :
    ∑ J, polar n d a b J I • g J = ∑ p, if b = I p then g (Function.update I p a) else 0 := by
  simp only [polar, Matrix.of_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  have h : ∀ J : Fin d → Fin n, (J p = a ∧ I p = b ∧ ∀ q, q ≠ p → J q = I q) ↔
      (b = I p ∧ J = Function.update I p a) := fun J => by
    rw [Function.eq_update_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h2.symm, h1, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1.symm, h3⟩
  simp only [h]
  by_cases hb : b = I p <;> simp [hb]

theorem sum_polar_right {A : Type} [AddCommGroup A] [Module ℂ A] {n d : ℕ} (a b : Fin n) (K : Fin d → Fin n)
    (g : (Fin d → Fin n) → A) :
    ∑ J, polar n d a b K J • g J = ∑ p, if K p = a then g (Function.update K p b) else 0 := by
  simp only [polar, Matrix.of_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  have h : ∀ J : Fin d → Fin n, (K p = a ∧ J p = b ∧ ∀ q, q ≠ p → K q = J q) ↔
      (K p = a ∧ J = Function.update K p b) := fun J => by
    rw [Function.eq_update_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, fun q hq => (h3 q hq).symm⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, fun q hq => (h3 q hq).symm⟩
  simp only [h]
  by_cases hb : K p = a <;> simp [hb]

theorem commutator_word {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} {E : Fin n → Fin n → A} (hE : Formalism.REAL.GlRel E)
    {d : ℕ} (a b : Fin n) (I K : Fin d → Fin n) :
    E a b * (List.ofFn fun q => E (I q) (K q)).prod - (List.ofFn fun q => E (I q) (K q)).prod * E a b =
      ∑ J, polar n d a b J I • (List.ofFn fun q => E (J q) (K q)).prod -
        ∑ J, polar n d a b K J • (List.ofFn fun q => E (I q) (J q)).prod := by
  rw [commutator_prod_ofFn, sum_polar_left, sum_polar_right, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  have h1 : (fun q => E (Function.update I p a q) (K q)) =
      Function.update (fun q => E (I q) (K q)) p (E a (K p)) := by
    funext q
    by_cases h : q = p
    · subst h; simp
    · simp [Function.update_of_ne h]
  have h2 : (fun q => E (I q) (Function.update K p b q)) =
      Function.update (fun q => E (I q) (K q)) p (E (I p) b) := by
    funext q
    by_cases h : q = p
    · subst h; simp
    · simp [Function.update_of_ne h]
  rw [h1, h2, hE a b (I p) (K p)]
  simp only [← MultilinearMap.mkPiAlgebraFin_apply (R := ℂ), MultilinearMap.map_update_sub]
  congr 1 <;> split_ifs <;> simp only [MultilinearMap.map_update_zero]

theorem commutator_wordMap : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A),
    Formalism.REAL.GlRel E → ∀ (d : ℕ) (a b : Fin n) (M : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ),
    E a b * wordMap E d M - wordMap E d M * E a b =
      wordMap E d (polar n d a b * M - M * polar n d a b) := by
  intro A _ _ n E hE d a b M
  have hw : ∀ N, wordMap E d N = ∑ I, ∑ K, N I K • (List.ofFn fun q : Fin d => E (I q) (K q)).prod := fun _ => rfl
  have hl : wordMap E d (polar n d a b * M) =
      ∑ I, ∑ K, M I K • ∑ J, polar n d a b J I • (List.ofFn fun q => E (J q) (K q)).prod := by
    simp only [hw, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun K _ => ?_
    rw [Finset.sum_comm]
    simp only [mul_comm]
  have hr : wordMap E d (M * polar n d a b) =
      ∑ I, ∑ K, M I K • ∑ J, polar n d a b K J • (List.ofFn fun q => E (I q) (J q)).prod := by
    simp only [hw, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [Finset.sum_comm]
  rw [map_sub, hl, hr, hw, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [← smul_sub, ← commutator_word hE, smul_sub, mul_smul_comm, smul_mul_assoc]

end GlobalTheory.SmoothForms
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CommutatorGlGeneratorTensorWordMapMatrixUnitsStatement
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutator_glGenerator_tensorWordMapMatrixUnits : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A), Formalism.REAL.GlRel E → ∀ (d : ℕ) (a b : Fin n) (M : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ), E a b * wordMap E d M - wordMap E d M * E a b = wordMap E d (polar n d a b * M - M * polar n d a b) := by
  first | exact @GlobalTheory.SmoothForms.commutator_wordMap | exact GlobalTheory.SmoothForms.commutator_wordMap | (intros; apply GlobalTheory.SmoothForms.commutator_wordMap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.BicommutantTensorFactorPermMemSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.BicommutantTensorFactorPermMemSpan
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

namespace GlobalTheory.SmoothForms

theorem bicomm_left_mul {ι G : Type} [Fintype ι] [DecidableEq ι] (ρ : G → Matrix ι ι ℂ)
    (p : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ) (hp : ∀ g X, p (ρ g * X) = ρ g * p X) (M : Matrix ι ι ℂ)
    (hM : ∀ T : Matrix ι ι ℂ, (∀ g, T * ρ g = ρ g * T) → M * T = T * M) (X : Matrix ι ι ℂ) :
    p (M * X) = M * p X := by
  have key : ∀ (A : Matrix ι ι ℂ) (i j a b : ι),
      ((Matrix.of fun a b => p (Matrix.single b i 1) a j) * A) a b = p (A * Matrix.single b i 1) a j := by
    intro A i j a b
    have : A * Matrix.single b i 1 = ∑ c, A c b • Matrix.single c i (1 : ℂ) := by
      ext x y
      simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.single_apply, smul_eq_mul]
      by_cases h : i = y <;> simp [h]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [this, map_sum]
    simp only [Matrix.mul_apply, Matrix.sum_apply, map_smul, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, mul_comm]
  have key2 : ∀ (A : Matrix ι ι ℂ) (i j a b : ι),
      (A * (Matrix.of fun a b => p (Matrix.single b i 1) a j)) a b = (A * p (Matrix.single b i 1)) a j := by
    intro A i j a b
    simp [Matrix.mul_apply]
  have h1 : ∀ b i, p (M * Matrix.single b i 1) = M * p (Matrix.single b i 1) := by
    intro b i
    ext a j
    rw [← key, ← key2, hM]
    intro g
    ext a b
    rw [key, key2, hp]
  have h2 : X = ∑ b, ∑ i, X b i • Matrix.single b i (1 : ℂ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    simp [Matrix.smul_single]
  rw [h2]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_sum, map_sum, Matrix.mul_smul, map_smul, h1]

theorem bicomm_mem_span {ι G : Type} [Fintype ι] [DecidableEq ι] [Group G] [Fintype G] (ρ : G → Matrix ι ι ℂ)
    (h1 : ρ 1 = 1) (hmul : ∀ g h, ρ g * ρ h = ρ (h * g)) (M : Matrix ι ι ℂ)
    (hM : ∀ T : Matrix ι ι ℂ, (∀ g, T * ρ g = ρ g * T) → M * T = T * M) :
    M ∈ Submodule.span ℂ (Set.range ρ) := by
  set B := Submodule.span ℂ (Set.range ρ) with hB
  have hst : ∀ g, ∀ X ∈ B, ρ g * X ∈ B := by
    intro g X hX
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      rw [hmul]
      exact Submodule.subset_span ⟨_, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mul_add]; exact B.add_mem hx hy
    | smul c x _ hx => rw [Matrix.mul_smul]; exact B.smul_mem c hx
  obtain ⟨q, hq⟩ := LinearMap.exists_extend (LinearMap.id : B →ₗ[ℂ] B)
  have hq' : ∀ X ∈ B, (q X : Matrix ι ι ℂ) = X := fun X hX => by
    have := LinearMap.congr_fun hq ⟨X, hX⟩
    exact congrArg Subtype.val this
  let p : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ :=
    ∑ g : G, LinearMap.mulLeft ℂ (ρ g⁻¹) ∘ₗ B.subtype ∘ₗ q ∘ₗ LinearMap.mulLeft ℂ (ρ g)
  have hp : ∀ X, p X = ∑ g : G, ρ g⁻¹ * (q (ρ g * X) : Matrix ι ι ℂ) := fun X => by
    simp [p, LinearMap.sum_apply]
  have hpB : ∀ X, p X ∈ B := fun X => by
    rw [hp]
    exact B.sum_mem fun g _ => hst _ _ (q _).2
  have hone : (1 : Matrix ι ι ℂ) ∈ B := Submodule.subset_span ⟨1, h1⟩
  have hp1 : p 1 = (Fintype.card G : ℂ) • (1 : Matrix ι ι ℂ) := by
    rw [hp]
    have : ∀ g : G, ρ g⁻¹ * (q (ρ g * 1) : Matrix ι ι ℂ) = 1 := fun g => by
      rw [hq' _ (hst _ _ hone), mul_one, hmul, mul_inv_cancel, h1]
    simp only [this]
    rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  have hpρ : ∀ h X, p (ρ h * X) = ρ h * p X := fun h X => by
    rw [hp, hp, Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_
    simp only [Equiv.coe_mulLeft]
    rw [← mul_assoc, hmul, ← mul_assoc, hmul]
    simp
  have := bicomm_left_mul ρ p hpρ M hM 1
  rw [hp1, mul_one, Matrix.mul_smul, mul_one] at this
  have hc : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have h3 := B.smul_mem (Fintype.card G : ℂ)⁻¹ (hpB M)
  rwa [this, smul_smul, inv_mul_cancel₀ hc, one_smul] at h3

theorem bicomm_permMat : ∀ (n d : ℕ) (M : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ), (∀ T : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ, (∀ π, T * permMat n d π = permMat n d π * T) → M * T = T * M) → M ∈ Submodule.span ℂ (Set.range (permMat n d)) := by
  intro n d M hM
  refine bicomm_mem_span (permMat n d) ?_ ?_ M hM
  · ext I K
    simp [permMat, Matrix.one_apply]
  · intro g h
    ext I K
    simp only [permMat, Matrix.mul_apply, Matrix.of_apply]
    rw [Finset.sum_eq_single (K ∘ h)]
    · rw [if_pos rfl, mul_one]
      rfl
    · intro J _ hJ
      simp [hJ]
    · simp

end GlobalTheory.SmoothForms
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.BicommutantTensorFactorPermMemSpanStatement
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bicommutant_tensorFactorPerm_mem_span : ∀ (n d : ℕ) (M : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ), (∀ T : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ, (∀ π, T * permMat n d π = permMat n d π * T) → M * T = T * M) → M ∈ Submodule.span ℂ (Set.range (permMat n d)) := by
  first | exact @GlobalTheory.SmoothForms.bicomm_permMat | exact GlobalTheory.SmoothForms.bicomm_permMat | (intros; apply GlobalTheory.SmoothForms.bicomm_permMat <;> assumption)
end
end

noncomputable section

open scoped ContDiff Topology
open Matrix

namespace GlobalTheory.SmoothForms

section Centre

variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} {E : Fin n → Fin n → A}

theorem range_le_filt {d d' : ℕ} (h : d' < d) : LinearMap.range (wordMap E d') ≤ filt E d :=
  le_iSup₂_of_le (f := fun d' (_ : d' < d) => LinearMap.range (wordMap E d')) d' h le_rfl

theorem filt_mono {d d' : ℕ} (h : d ≤ d') : filt E d ≤ filt E d' :=
  iSup₂_le fun _ hk => range_le_filt (hk.trans_le h)

theorem filt_succ (d : ℕ) : filt E (d + 1) ≤ LinearMap.range (wordMap E d) ⊔ filt E d :=
  iSup₂_le fun k hk => by
    rcases (Nat.lt_succ_iff.1 hk).eq_or_lt with rfl | h
    · exact le_sup_left
    · exact (range_le_filt h).trans le_sup_right

theorem filt_ad (hE : Formalism.REAL.GlRel E) (d : ℕ) (a b : Fin n) {y : A} (hy : y ∈ filt E d) :
    E a b * y - y * E a b ∈ filt E d := by
  have : filt E d ≤ (filt E d).comap (LinearMap.mulLeft ℂ (E a b) - LinearMap.mulRight ℂ (E a b)) :=
    iSup₂_le fun k hk => by
      rintro _ ⟨M, rfl⟩
      change E a b * wordMap E k M - wordMap E k M * E a b ∈ filt E d
      rw [GlobalTheory.T.commutator_glGenerator_tensorWordMapMatrixUnits A n E hE]
      exact range_le_filt hk ⟨_, rfl⟩
  exact this hy

theorem polar_conjTranspose (d : ℕ) (a b : Fin n) : (polar n d a b)ᴴ = polar n d b a := by
  ext I K
  simp only [polar, conjTranspose_apply, of_apply, star_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have : (K p = a ∧ I p = b ∧ ∀ q, q ≠ p → K q = I q) ↔ (I p = b ∧ K p = a ∧ ∀ q, q ≠ p → I q = K q) :=
    ⟨fun h => ⟨h.2.1, h.1, fun q hq => (h.2.2 q hq).symm⟩, fun h => ⟨h.2.1, h.1, fun q hq => (h.2.2 q hq).symm⟩⟩
  simp only [this]
  split_ifs <;> simp

theorem gelf_adjoin_comm (hE : Formalism.REAL.GlRel E) {c : A} (hc : c ∈ Algebra.adjoin ℂ (Set.range (gelfA E)))
    (a b : Fin n) : E a b * c = c * E a b := by
  have : Algebra.adjoin ℂ (Set.range (gelfA E)) ≤ Subalgebra.centralizer ℂ {E a b} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨k, rfl⟩ _ rfl
    exact GlobalTheory.T.commute_gelfandInvariantMatrixUnits_of_glRel A n E hE k a b
  exact this hc _ rfl

theorem central_of_filt (hE : Formalism.REAL.GlRel E) (d : ℕ) : ∀ z ∈ filt E d, (∀ a b, E a b * z = z * E a b) →
    z ∈ Algebra.adjoin ℂ (Set.range (gelfA E)) := by
  induction d with
  | zero =>
    intro z hz _
    have : filt E 0 ≤ ⊥ := iSup₂_le fun k hk => absurd hk (Nat.not_lt_zero k)
    rw [(Submodule.mem_bot ℂ).1 (this hz)]
    exact zero_mem _
  | succ d ih =>
    intro z hz hc
    obtain ⟨_, ⟨M, rfl⟩, y, hy, rfl⟩ := Submodule.mem_sup.1 (filt_succ d hz)
    obtain ⟨M₀, h1, h2⟩ := GlobalTheory.T.commutant_lift_mod_stable_selfAdjoint _ (Set.range fun p : Fin n × Fin n => polar n d p.1 p.2)
      ((filt E d).comap (wordMap E d))
      (by rintro _ ⟨p, rfl⟩; exact ⟨(p.2, p.1), (polar_conjTranspose d p.1 p.2).symm⟩)
      (by
        rintro _ ⟨p, rfl⟩ N hN
        rw [Submodule.mem_comap, ← GlobalTheory.T.commutator_glGenerator_tensorWordMapMatrixUnits A n E hE]
        exact filt_ad hE d _ _ hN) M
      (by
        rintro _ ⟨p, rfl⟩
        rw [Submodule.mem_comap, ← GlobalTheory.T.commutator_glGenerator_tensorWordMapMatrixUnits A n E hE]
        have h3 := neg_mem (filt_ad hE d p.1 p.2 hy)
        have h4 := hc p.1 p.2
        rw [mul_add, add_mul] at h4
        convert h3 using 1
        rw [neg_sub, sub_eq_sub_iff_add_eq_add, h4, add_comm])
    have h3 : M₀ ∈ Submodule.span ℂ (Set.range (permMat n d)) := by
      refine GlobalTheory.T.bicommutant_tensorFactorPerm_mem_span n d M₀ fun T hT => ?_
      have : Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => polar n d p.1 p.2) ≤
          Subalgebra.centralizer ℂ {M₀} := by
        refine Algebra.adjoin_le ?_
        rintro x hx _ rfl
        exact (h2 x hx).symm
      exact this (GlobalTheory.T.mem_adjoin_glAction_of_commute_tensorPerm n d T hT) _ rfl
    have h4 : Submodule.span ℂ (Set.range (permMat n d)) ≤
        (Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range (gelfA E))) ⊔ filt E d).comap (wordMap E d) := by
      rw [Submodule.span_le]
      rintro _ ⟨π, rfl⟩
      obtain ⟨c, hc1, hc2⟩ := GlobalTheory.T.permutationWord_gelfandPolynomial_mod_shorter A n E hE d π
      exact Submodule.mem_sup.2 ⟨c, hc1, _, hc2, by abel⟩
    obtain ⟨c, hc1, u, hu, hcu⟩ := Submodule.mem_sup.1 (h4 h3)
    have h5 : wordMap E d M + y - c ∈ filt E d := by
      have h6 : wordMap E d (M - M₀) ∈ filt E d := h1
      have := add_mem (add_mem h6 hu) hy
      convert this using 1
      rw [map_sub, ← hcu]; abel
    have h7 := ih _ h5 fun a b => by rw [mul_sub, sub_mul, hc, gelf_adjoin_comm hE hc1]
    simpa using add_mem h7 hc1

theorem exists_filt {z : A} (hz : z ∈ Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => E p.1 p.2)) :
    ∃ d, z ∈ filt E d := by
  have h : z ∈ Submodule.span ℂ (Submonoid.closure (Set.range fun p : Fin n × Fin n => E p.1 p.2) : Set A) := by
    rw [← Algebra.adjoin_eq_span]; exact hz
  clear hz
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := Submonoid.exists_list_of_mem_closure hx
    choose p hp using fun i : Fin l.length => hl (l.get i) (List.get_mem l i)
    refine ⟨l.length + 1, range_le_filt (Nat.lt_succ_self _)
      ⟨Matrix.single (fun i => (p i).1) (fun i => (p i).2) 1, ?_⟩⟩
    have e : (List.ofFn fun i => E (p i).1 (p i).2) = l := by
      simp only [hp]; exact List.ofFn_get l
    simp only [wordMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.single, of_apply, ite_smul, one_smul, zero_smul,
      ite_and]
    simp [e]
  | zero => exact ⟨0, zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨max a b, add_mem (filt_mono (le_max_left _ _) ha) (filt_mono (le_max_right _ _) hb)⟩
  | smul c x _ hx => exact ⟨_, Submodule.smul_mem _ c hx.choose_spec⟩

theorem center_eq_adjoin (hE : Formalism.REAL.GlRel E)
    (hgen : Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => E p.1 p.2) = ⊤) :
    Subalgebra.center ℂ A = Algebra.adjoin ℂ (Set.range (gelfA E)) := by
  refine le_antisymm (fun z hz => ?_) fun c hc => ?_
  · obtain ⟨d, hd⟩ := exists_filt (E := E) (z := z) (hgen ▸ Algebra.mem_top)
    exact central_of_filt hE d z hd fun a b => Subalgebra.mem_center_iff.1 hz _
  · refine Subalgebra.mem_center_iff.2 fun b => ?_
    have : Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => E p.1 p.2) ≤ Subalgebra.centralizer ℂ {c} := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨p, rfl⟩ _ rfl
      exact (gelf_adjoin_comm hE hc p.1 p.2).symm
    exact (this (hgen ▸ Algebra.mem_top : b ∈ _) _ rfl).symm

end Centre

section Operators

variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G}

def smSub (e : L → G) : Submodule ℂ (G → ℂ) where
  carrier := {φ | Sm e φ}
  zero_mem' := fun _ => contDiff_const
  add_mem' := fun h h' g => (h g).add (h' g)
  smul_mem' := fun c _ h g => (h g).const_smul c

theorem Sm.differentiableAt {e : L → G} {φ : G → ℂ} (h : Sm e φ) (g : G) (X : L) :
    DifferentiableAt ℝ (fun t : ℝ => φ (g * e (t • X))) 0 :=
  (((h g).comp (contDiff_id.smul contDiff_const : ContDiff ℝ ∞ fun t : ℝ => t • X)).differentiable
    (by simp)).differentiableAt

def derOp (H : IsLieData σ j s) (hl : HasLog σ j) (X : L) : Module.End ℂ (smSub (expMap j s)) where
  toFun φ := ⟨Der (expMap j s) X φ.1, (GlobalTheory.T.rightDerivativeAlongLie_smooth_and_linear 𝔸 L G σ j s H hl φ.1 φ.2).1 X⟩
  map_add' φ ψ := Subtype.ext (funext fun g => deriv_add (Sm.differentiableAt φ.2 g X) (Sm.differentiableAt ψ.2 g X))
  map_smul' c φ := Subtype.ext (funext fun g => deriv_const_smul c (Sm.differentiableAt φ.2 g X))

theorem derOp_add (H : IsLieData σ j s) (hl : HasLog σ j) (X Y : L) :
    derOp H hl (X + Y) = derOp H hl X + derOp H hl Y :=
  LinearMap.ext fun φ => Subtype.ext ((GlobalTheory.T.rightDerivativeAlongLie_smooth_and_linear 𝔸 L G σ j s H hl φ.1 φ.2).2.1 X Y)

theorem derOp_smul (H : IsLieData σ j s) (hl : HasLog σ j) (c : ℝ) (X : L) :
    derOp H hl (c • X) = (c : ℂ) • derOp H hl X :=
  LinearMap.ext fun φ => Subtype.ext ((GlobalTheory.T.rightDerivativeAlongLie_smooth_and_linear 𝔸 L G σ j s H hl φ.1 φ.2).2.2 c X)

theorem derOp_bracket (H : IsLieData σ j s) (hl : HasLog σ j) (X Y Z : L) (h : j Z = j X * j Y - j Y * j X) :
    derOp H hl Z = derOp H hl X * derOp H hl Y - derOp H hl Y * derOp H hl X :=
  LinearMap.ext fun φ => Subtype.ext (GlobalTheory.T.rightDerivativeAlongLie_commutator_eq_bracket 𝔸 L G σ j s H hl φ.1 φ.2 X Y Z h).symm

theorem derOp_zero (H : IsLieData σ j s) (hl : HasLog σ j) : derOp H hl 0 = 0 := by
  simpa using derOp_smul H hl 0 0

end Operators

end GlobalTheory.SmoothForms

end
