module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.MemHomogeneousExponentsOneBlock
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.LevelTwoFiniteIndex

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.WtMain
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.HomogeneousTraceDiagonal
open Polynomial UpperTheory.V.Z.Sym.Wt

private theorem tri (d : ℕ) : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (f : Module.End ℂ V),
    Module.finrank ℂ V = d → ∃ b : Module.Basis (Fin d) ℂ V, ∀ i j, i < j → b.repr (f (b j)) i = 0 := by
  induction d with
  | zero => exact fun V _ _ _ f h => ⟨Module.finBasisOfFinrankEq ℂ V h, fun i => i.elim0⟩
  | succ d ih =>
    intro V _ _ _ f h
    haveI : Nontrivial V := Module.nontrivial_of_finrank_eq_succ h
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue f
    have h1 : LinearMap.range (f - μ • (1 : Module.End ℂ V)) < ⊤ := by
      rw [lt_top_iff_ne_top, Ne, ← LinearMap.ker_eq_bot_iff_range_eq_top]
      rw [Module.End.hasEigenvalue_iff, Module.End.eigenspace_def] at hμ
      exact hμ
    obtain ⟨φ, hφ, hle⟩ := Submodule.exists_le_ker_of_lt_top _ h1
    have hk : Module.finrank ℂ (LinearMap.ker φ) = d := by
      have := Module.Dual.finrank_ker_add_one_of_ne_zero hφ
      omega
    have hm : ∀ x ∈ LinearMap.ker φ, f x ∈ LinearMap.ker φ := fun x hx => by
      have := (LinearMap.ker φ).add_mem (hle ⟨x, rfl⟩) ((LinearMap.ker φ).smul_mem μ hx)
      simpa using this
    obtain ⟨b, hb⟩ := ih _ (f.restrict hm) hk
    obtain ⟨y, hy⟩ : ∃ y, φ y = 1 := LinearMap.surjective_of_ne_zero hφ 1
    let b' := Module.Basis.mkFinCons y b (fun c x hx h => by
      have := congrArg φ h
      rwa [map_add, map_smul, hy, LinearMap.mem_ker.1 hx, map_zero, add_zero, smul_eq_mul, mul_one] at this)
      (fun z => ⟨-φ z, by simp [hy]⟩)
    have hb' : ∀ i, b' (Fin.succ i) = b i := fun i => by simp [b']
    refine ⟨b', fun i j hij => ?_⟩
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 (ne_of_gt (lt_of_le_of_lt (Fin.zero_le i) hij))
    have e : f (b' j.succ) = ∑ k, b.repr (f.restrict hm (b j)) k • b' k.succ := by
      have := congrArg Subtype.val (b.sum_repr (f.restrict hm (b j)))
      rw [hb']
      simp only [hb']
      rw [Submodule.coe_sum] at this
      exact this.symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, map_sum, Finsupp.finsetSum_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
    split_ifs with hk
    · rw [hb k j (by rw [← hk] at hij; exact Fin.succ_lt_succ_iff.1 hij), zero_smul]
    · simp

private theorem tri_mat {d : ℕ} (g : GL (Fin d) ℂ) : ∃ Q : GL (Fin d) ℂ, ∀ i j, i < j → (Q⁻¹ * g * Q : GL (Fin d) ℂ) i j = 0 := by
  obtain ⟨b, hb⟩ := tri d (Fin d → ℂ) (Matrix.toLin' (g : Matrix (Fin d) (Fin d) ℂ)) (by simp)
  let e := Pi.basisFun ℂ (Fin d)
  refine ⟨⟨e.toMatrix b, b.toMatrix e, e.toMatrix_mul_toMatrix_flip b, b.toMatrix_mul_toMatrix_flip e⟩, fun i j h => ?_⟩
  have := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix b e b e (Matrix.toLin' (g : Matrix (Fin d) (Fin d) ℂ))
  rw [show LinearMap.toMatrix e e (Matrix.toLin' (g : Matrix (Fin d) (Fin d) ℂ)) = g by simp [e]] at this
  change (b.toMatrix e * (g : Matrix (Fin d) (Fin d) ℂ) * e.toMatrix b) i j = 0
  rw [this, LinearMap.toMatrix_apply, hb i j h]

private theorem homogeneous_trace_conj {d : ℕ} (n : ℕ) (g Q : GL (Fin d) ℂ) : tr1 d n (Q⁻¹ * g * Q) = tr1 d n g := by
  haveI := finMH Unit d fun _ => n
  have e : ∀ a b : GL (Fin d) ℂ, mRep d (fun _ : Unit => n) (fun _ => a * b) = mRep d _ (fun _ => a) * mRep d _ fun _ => b :=
    fun a b => by rw [← map_mul]; rfl
  unfold tr1
  rw [e, LinearMap.trace_mul_comm, ← e, ← mul_assoc, mul_inv_cancel, one_mul]

open MvPolynomial in
private theorem cont_coeff {σ ι : Type} [Fintype ι] (F : ι → ℂ → MvPolynomial σ ℂ) (h : ∀ i m, Continuous fun t => (F i t).coeff m)
    (s : Multiset ι) : ∀ m, Continuous fun t => ((s.map fun i => F i t).prod).coeff m := by
  classical
  induction s using Multiset.induction_on with
  | empty => exact fun m => continuous_const
  | cons a s ih =>
    intro m
    simp only [Multiset.map_cons, Multiset.prod_cons, MvPolynomial.coeff_mul]
    exact continuous_finsetSum _ fun p _ => (h a _).mul (ih _)

open MvPolynomial in
private theorem homogeneous_trace_diagonal {d : ℕ} (n : ℕ) (g : GL (Fin d) ℂ) (h : ∀ i j, i ≠ j → g i j = 0) :
    tr1 d n g = MvPolynomial.eval (fun i => g i i) (hsymm (Fin d) ℂ n) := by
  classical
  have e : ∀ m : Unit × Fin d →₀ ℕ, AddMonoidAlgebra.coeff (sbs (fun _ : Unit => g) (MvPolynomial.monomial m 1)) m = ∏ i, g i i ^ m ((), i) := fun m => by
    have : sbs (fun _ : Unit => g) (MvPolynomial.monomial m 1) = MvPolynomial.monomial m (∏ i, g i i ^ m ((), i)) := by
      refine MvPolynomial.funext fun x => ?_
      have a : act (fun _ : Unit => g) x = fun p => x p * g p.2 p.2 := funext fun p =>
        Finset.sum_eq_single p.2 (fun j _ hj => by rw [h j _ hj, mul_zero]) (by simp)
      rw [eval_sbs, a, MvPolynomial.eval_monomial, MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (by simp),
        Finsupp.prod_fintype _ _ (by simp)]
      simp [Fintype.prod_prod_type, mul_pow, Finset.prod_mul_distrib, mul_comm]
    rw [this, MvPolynomial.coeff_monomial, if_pos rfl]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [symPowTrace_eq_sum_coeff, hsymm, map_sum]
  simp only [e]
  symm
  refine Finset.sum_bij (fun s _ => Finsupp.equivFunOnFinite.symm fun p : Unit × Fin d => s.1.count p.2) (fun s _ => mem_homogeneousExponentsOneBlock.2 ?_)
    (fun s _ s' _ hs => Subtype.ext (Multiset.ext' fun a => ?_)) (fun m hm => ?_) fun s _ => ?_
  · exact (Multiset.sum_count_eq_card fun a _ => Finset.mem_univ a).trans s.2
  · exact DFunLike.congr_fun hs ((), a)
  · refine ⟨⟨∑ i, Multiset.replicate (m ((), i)) i, by simpa using mem_homogeneousExponentsOneBlock.1 hm⟩, Finset.mem_univ _, ?_⟩
    ext ⟨⟨⟩, i⟩
    simp [Multiset.count_sum', Multiset.count_replicate]
  · rw [map_multiset_prod, Multiset.map_map, Finset.prod_multiset_map_count]
    simp only [Function.comp_apply, MvPolynomial.eval_X]
    exact Finset.prod_subset (Finset.subset_univ _) fun a _ ha => by
      rw [Multiset.count_eq_zero_of_notMem (by simpa using ha), pow_zero]

private theorem homogeneous_trace_triangular {d : ℕ} (n : ℕ) (g : GL (Fin d) ℂ) (h : ∀ i j, i < j → g i j = 0) :
    tr1 d n g = MvPolynomial.eval (fun i => g i i) (MvPolynomial.hsymm (Fin d) ℂ n) := by
  classical
  let A : ℂ → Matrix (Fin d) (Fin d) ℂ := fun t => Matrix.of fun i j => t ^ ((i : ℕ) - j) * g i j
  have hd : ∀ t, (A t).det ≠ 0 := fun t => by
    have h1 := Matrix.det_of_lowerTriangular (A t) fun i j hij => by simp [A, h i j hij]
    have h2 := Matrix.det_of_lowerTriangular (g : Matrix (Fin d) (Fin d) ℂ) fun i j hij => h i j hij
    rw [h1]
    simpa [A, ← h2] using g.det_ne_zero
  let γ : ℂ → GL (Fin d) ℂ := fun t => Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hd t)
  have hc : Continuous fun t => tr1 d n (γ t) := by
    simp only [symPowTrace_eq_sum_coeff]
    refine continuous_finsetSum _ fun m _ => ?_
    have := cont_coeff (fun (p : Unit × Fin d) t => ∑ j, MvPolynomial.X (p.1, j) * MvPolynomial.C (A t j p.2)) (fun p m => by
      simp only [MvPolynomial.coeff_sum, mul_comm (MvPolynomial.X _), MvPolynomial.coeff_C_mul, A, Matrix.of_apply]
      fun_prop) m.toMultiset m
    refine this.congr fun t => ?_
    congr 1
    rw [sbs, MvPolynomial.aeval_monomial, map_one, one_mul, Finsupp.toMultiset_map, Finsupp.prod_toMultiset,
      Finsupp.prod_mapDomain_index (by simp) (fun _ _ _ => pow_add _ _ _)]
    rfl
  have h1 : ∀ t ∈ ({0}ᶜ : Set ℂ), tr1 d n (γ t) = tr1 d n g := fun t ht => by
    have ht : t ≠ 0 := ht
    let Q : GL (Fin d) ℂ := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal fun i : Fin d => t ^ (i : ℕ))
      (by rw [Matrix.det_diagonal]; exact Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ ht)
    rw [← homogeneous_trace_conj n (γ t) Q]
    congr 1
    rw [mul_assoc, inv_mul_eq_iff_eq_mul]
    refine Units.ext (Matrix.ext fun i j => ?_)
    change (A t * Matrix.diagonal (fun i : Fin d => t ^ (i : ℕ)) : Matrix (Fin d) (Fin d) ℂ) i j =
      (Matrix.diagonal (fun i : Fin d => t ^ (i : ℕ)) * (g : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    rcases lt_or_ge i j with hij | hij
    · simp [A, h i j hij]
    · simp only [A, Matrix.of_apply]
      rw [mul_right_comm, ← pow_add, Nat.sub_add_cancel hij]
  have h2 := congrFun (Continuous.ext_on (dense_compl_singleton (0 : ℂ)) hc continuous_const h1) 0
  rw [← h2, homogeneous_trace_diagonal n (γ 0) fun i j hij => ?_]
  · congr 2
    funext i
    change A 0 i i = _
    simp [A]
  · change A 0 i j = 0
    rcases lt_or_gt_of_ne hij with h' | h'
    · simp [A, h i j h']
    · simp only [A, Matrix.of_apply]
      rw [zero_pow (Nat.sub_ne_zero_of_lt h'), zero_mul]

theorem UpperTheory.V.Z.Sym.Wt.trOne :
    UpperTheory.V.Z.Sym.Wt.TrOne := by
  intro d n g α hα
  classical
  obtain ⟨Q, hQ⟩ := tri_mat g
  rw [← homogeneous_trace_conj n g Q, homogeneous_trace_triangular n _ hQ]
  have h0 : ((Q⁻¹ * g * Q : GL (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ).charpoly = ∏ i, (X - C (α i)) := by
    rw [← hα, Units.val_mul, Units.val_mul, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mul]
  generalize Q⁻¹ * g * Q = u at h0 hQ
  obtain ⟨β, hβ⟩ : ∃ β : Fin d → ℂ, β = fun i => u i i := ⟨_, rfl⟩
  rw [← hβ]
  have h1 : ∏ i, (X - C (β i)) = ∏ i, (X - C (α i)) := by
    rw [← h0, ← Matrix.charpoly_transpose, Matrix.charpoly_of_upperTriangular (u : Matrix (Fin d) (Fin d) ℂ).transpose fun i j hij => hQ j i hij, hβ]
    rfl
  have h2 : Finset.univ.val.map β = Finset.univ.val.map α := by
    rw [← roots_multiset_prod_X_sub_C (Finset.univ.val.map β), ← roots_multiset_prod_X_sub_C (Finset.univ.val.map α),
      Multiset.map_map, Multiset.map_map]
    exact congrArg roots h1
  have h3 : ∀ c, Fintype.card {i // β i = c} = Fintype.card {i // α i = c} := fun c => by
    have := congrArg (Multiset.count c) h2
    rw [Multiset.count_map, Multiset.count_map] at this
    simp only [Fintype.card_subtype, eq_comm (b := c)]
    exact this
  let e : Fin d ≃ Fin d := Equiv.ofFiberEquiv fun c => Fintype.equivOfCardEq (h3 c)
  have h4 : β = α ∘ e := funext fun i => (Equiv.ofFiberEquiv_map _ i).symm
  rw [h4, ← MvPolynomial.eval_rename, MvPolynomial.rename_hsymm]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.HOption
open Polynomial UpperTheory.V.Z.Sym.Wt

private theorem ev_h {σ : Type} [Fintype σ] [DecidableEq σ] (x : σ → ℂ) (n : ℕ) :
    MvPolynomial.eval x (MvPolynomial.hsymm σ ℂ n) = ∑ s : Sym σ n, ((s : Multiset σ).map x).prod := by
  simp [MvPolynomial.hsymm, map_multiset_prod, Multiset.map_map]

private theorem h_option {σ : Type} [Fintype σ] [DecidableEq σ] (x : Option σ → ℂ) (n : ℕ) :
    MvPolynomial.eval x (MvPolynomial.hsymm (Option σ) ℂ (n + 1)) =
      x none * MvPolynomial.eval x (MvPolynomial.hsymm (Option σ) ℂ n) +
        MvPolynomial.eval (fun i => x (some i)) (MvPolynomial.hsymm σ ℂ (n + 1)) := by
  rw [ev_h, ev_h, ev_h, ← Equiv.sum_comp (symOptionSuccEquiv).symm, Fintype.sum_sum_type, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun s _ => ?_
    simp only [symOptionSuccEquiv, Equiv.coe_fn_symm_mk, SymOptionSuccEquiv.decode_inl]
    rw [Sym.coe_cons, Multiset.map_cons, Multiset.prod_cons]
  · refine Finset.sum_congr rfl fun s _ => ?_
    simp [symOptionSuccEquiv, Multiset.map_map, Function.comp_def]

private theorem h_equiv {σ τ : Type} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] (e : σ ≃ τ)
    (x : τ → ℂ) (n : ℕ) :
    MvPolynomial.eval x (MvPolynomial.hsymm τ ℂ n) = MvPolynomial.eval (x ∘ e) (MvPolynomial.hsymm σ ℂ n) := by
  rw [ev_h, ev_h, ← Equiv.sum_comp (Sym.equivCongr e)]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [Sym.equivCongr, Multiset.map_map]

private theorem h_succ (d : ℕ) (x : Fin (d + 1) → ℂ) (n : ℕ) :
    MvPolynomial.eval x (MvPolynomial.hsymm (Fin (d + 1)) ℂ (n + 1)) =
      x 0 * MvPolynomial.eval x (MvPolynomial.hsymm (Fin (d + 1)) ℂ n) +
        MvPolynomial.eval (fun i => x (Fin.succ i)) (MvPolynomial.hsymm (Fin d) ℂ (n + 1)) := by
  rw [h_equiv (finSuccEquiv d).symm x, h_equiv (finSuccEquiv d).symm x, h_option]
  simp

private theorem h_one (x : Fin 1 → ℂ) (n : ℕ) :
    MvPolynomial.eval x (MvPolynomial.hsymm (Fin 1) ℂ n) = x 0 ^ n := by
  rw [ev_h]
  have hs : ∀ s : Sym (Fin 1) n, ((s : Multiset (Fin 1)).map x).prod = x 0 ^ n := by
    intro s
    have hrep : (s : Multiset (Fin 1)).map x = Multiset.replicate n (x 0) := by
      rw [Multiset.eq_replicate]
      refine ⟨by simp, fun b hb => ?_⟩
      obtain ⟨a, _, rfl⟩ := Multiset.mem_map.mp hb
      rw [Subsingleton.elim a 0]
    rw [hrep, Multiset.prod_replicate]
  rw [Finset.sum_congr rfl fun s _ => hs s, Finset.sum_const, Finset.card_univ, Sym.card_sym_eq_multichoose]
  simp

private theorem hq_step (a b : ℂ) (n : ℕ) :
    hq (a + b) (a * b) (n + 1) = a * hq (a + b) (a * b) n + b ^ (n + 1) := by
  induction n with
  | zero => simp [hq.eq_1, hq.eq_2]
  | succ k ih =>
    rw [hq.eq_3, ih]
    ring

theorem UpperTheory.V.Z.Sym.Wt.hqTwo :
    UpperTheory.V.Z.Sym.Wt.HqTwo := by
  intro j a b
  induction j with
  | zero =>
    have h0 : ∀ s : Sym (Fin 2) 0, ((s : Multiset (Fin 2)).map ![a, b]).prod = 1 := by
      intro s
      rw [Subsingleton.elim s Sym.nil]
      simp
    rw [ev_h, Finset.sum_congr rfl fun s _ => h0 s, Finset.sum_const, Finset.card_univ, Sym.card_sym_eq_multichoose]
    simp [hq.eq_1]
  | succ k ih =>
    rw [hq_step, ← ih]
    refine (h_succ 1 ![a, b] k).trans ?_
    rw [h_one]
    simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.TwineC
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.TrSwap
open Polynomial UpperTheory.V.Z.Sym.Wt

open MvPolynomial in
private theorem homogeneous_trace_mul {d : ℕ} (n : ℕ) (g h : GL (Fin d) ℂ) :
    tr1 d n (g * h) = ∑ p ∈ deg1 d n ×ˢ deg1 d n,
      (sbs (fun _ : Unit => g) (monomial p.2 1)).coeff p.1 *
        (sbs (fun _ : Unit => h) (monomial p.1 1)).coeff p.2 := by
  classical
  have hcomp : ∀ P, sbs (fun _ : Unit => g * h) P = sbs (fun _ : Unit => g) (sbs (fun _ : Unit => h) P) := by
    intro P
    apply MvPolynomial.funext
    intro x
    rw [eval_sbs, eval_sbs, eval_sbs, ← act_mul]
    rfl
  rw [symPowTrace_eq_sum_coeff, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro m hm
  have hmono : (monomial m (1 : ℂ)) ∈ MH d (fun _ : Unit => n) := by
    refine (memMH Unit d (fun _ => n) _).2 ?_
    intro m0 hm0 k
    rw [Finset.mem_singleton.1 (MvPolynomial.support_monomial_subset hm0)]
    exact mem_homogeneousExponentsOneBlock.1 hm
  have hQ := sbs_mem (fun _ : Unit => h) hmono
  have hQsum : sbs (fun _ : Unit => h) (monomial m 1) =
      ∑ m' ∈ deg1 d n, monomial m' ((sbs (fun _ : Unit => h) (monomial m 1)).coeff m') := by
    conv_lhs => rw [(sbs (fun _ : Unit => h) (monomial m 1)).as_sum]
    apply Finset.sum_subset
    · intro m' hm'
      rw [mem_homogeneousExponentsOneBlock]
      exact (memMH Unit d (fun _ => n) _).1 hQ m' hm' ()
    · intro m' _ hm'
      rw [MvPolynomial.notMem_support_iff.1 hm', monomial_zero]
  rw [hcomp]
  conv_lhs => rw [hQsum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro m' _
  rw [show monomial m' ((sbs (fun _ : Unit => h) (monomial m 1)).coeff m') =
      (sbs (fun _ : Unit => h) (monomial m 1)).coeff m' • monomial m' (1 : ℂ) by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]]
  rw [map_smul, MvPolynomial.coeff_smul, smul_eq_mul, mul_comm]

theorem UpperTheory.V.Z.Sym.Wt.trSwap :
    UpperTheory.V.Z.Sym.Wt.TrSwap := by
  classical
  intro I _ d n g
  have hinv : ∀ p, UpperTheory.V.Z.Sym.Wt.flip I d (UpperTheory.V.Z.Sym.Wt.flip I d p) = p := by
    intro p
    simp [UpperTheory.V.Z.Sym.Wt.flip]
  have hinj : Function.Injective (UpperTheory.V.Z.Sym.Wt.flip I d) := Function.LeftInverse.injective hinv
  have hglue : ∀ μ : I × Bool → Unit × Fin d →₀ ℕ,
      Finsupp.mapDomain (UpperTheory.V.Z.Sym.Wt.flip I d) (glue μ) = glue (fun k => μ (k.1, !k.2)) := by
    intro μ
    ext ⟨⟨i, b⟩, j⟩
    have := Finsupp.mapDomain_apply_of_injective hinj (glue μ) ((i, !b), j)
    rw [show UpperTheory.V.Z.Sym.Wt.flip I d ((i, !b), j) = ((i, b), j) by
      simp [UpperTheory.V.Z.Sym.Wt.flip]] at this
    rw [this, glue_apply, glue_apply]
  rw [trace_blocks (K := I × Bool) (fun k => n k.1)
    ((sbs (dbl d g)).toLinearMap.comp (MvPolynomial.rename (UpperTheory.V.Z.Sym.Wt.flip I d)).toLinearMap)
    (biRep d n g * swp d n) (fun P => rfl)]
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, MvPolynomial.rename_monomial, hglue,
    coeff_sbs_glue]
  simp_rw [homogeneous_trace_mul]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_nbij' (fun μ v => (μ (v, false), μ (v, true)))
    (fun x k => if k.2 then (x k.1).2 else (x k.1).1) ?_ ?_ ?_ ?_ ?_
  · intro μ hμ
    rw [Fintype.mem_piFinset] at hμ ⊢
    intro v
    exact Finset.mem_product.2 ⟨hμ (v, false), hμ (v, true)⟩
  · intro x hx
    rw [Fintype.mem_piFinset] at hx ⊢
    rintro ⟨v, b⟩
    cases b
    · exact (Finset.mem_product.1 (hx v)).1
    · exact (Finset.mem_product.1 (hx v)).2
  · intro μ _
    funext ⟨v, b⟩
    cases b <;> rfl
  · intro x _
    rfl
  · intro μ _
    rw [Fintype.prod_prod_type]
    apply Finset.prod_congr rfl
    intro v _
    rw [Fintype.prod_bool]
    show AddMonoidAlgebra.coeff ((sbs fun _ : Unit => invT ℂ d (g v)) (MvPolynomial.monomial (μ (v, false)) 1))
        (μ (v, true)) *
      AddMonoidAlgebra.coeff ((sbs fun _ : Unit => g v) (MvPolynomial.monomial (μ (v, true)) 1))
        (μ (v, false)) = _
    exact mul_comm _ _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.HqThree
open Polynomial UpperTheory.V.Z.Sym.Wt

private theorem hs_opt {σ : Type} [Fintype σ] [DecidableEq σ] (x : Option σ → ℂ) (j : ℕ) :
    MvPolynomial.eval x (MvPolynomial.hsymm (Option σ) ℂ (j + 1)) =
      x none * MvPolynomial.eval x (MvPolynomial.hsymm (Option σ) ℂ j) +
        MvPolynomial.eval (x ∘ some) (MvPolynomial.hsymm σ ℂ (j + 1)) := by
  have ev : ∀ (τ : Type) [Fintype τ] [DecidableEq τ] (y : τ → ℂ) (n : ℕ),
      MvPolynomial.eval y (MvPolynomial.hsymm τ ℂ n) = ∑ s : Sym τ n, ((s : Multiset τ).map y).prod := by
    intro τ _ _ y n
    set_option synthInstance.maxHeartbeats 100000 in
      rw [MvPolynomial.hsymm, map_sum]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [map_multiset_prod, Multiset.map_map]
    congr 1
    exact Multiset.map_congr rfl (fun a _ => MvPolynomial.eval_X _)
  rw [ev, ev, ev]
  rw [← (symOptionSuccEquiv (α := σ) (n := j)).symm.sum_comp, Fintype.sum_sum_type, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl (fun s _ => ?_)
    show ((none ::ₘ (s : Multiset (Option σ))).map x).prod = _
    rw [Multiset.map_cons, Multiset.prod_cons]
  · refine Finset.sum_congr rfl (fun s _ => ?_)
    show ((Multiset.map some (s : Multiset σ)).map x).prod = _
    rw [Multiset.map_map]

private theorem hs_succ {d : ℕ} (x : Fin (d + 1) → ℂ) (k : Fin (d + 1)) (j : ℕ) :
    MvPolynomial.eval x (MvPolynomial.hsymm (Fin (d + 1)) ℂ (j + 1)) =
      x k * MvPolynomial.eval x (MvPolynomial.hsymm (Fin (d + 1)) ℂ j) +
        MvPolynomial.eval (x ∘ k.succAbove) (MvPolynomial.hsymm (Fin d) ℂ (j + 1)) := by
  have e1 : ∀ n, MvPolynomial.hsymm (Fin (d + 1)) ℂ n =
      MvPolynomial.rename (finSuccEquiv' k).symm (MvPolynomial.hsymm (Option (Fin d)) ℂ n) :=
    fun n => (MvPolynomial.rename_hsymm (Option (Fin d)) ℂ n (finSuccEquiv' k).symm).symm
  rw [e1, e1, MvPolynomial.eval_rename, MvPolynomial.eval_rename, hs_opt]
  have h1 : (x ∘ (finSuccEquiv' k).symm) none = x k := by simp
  have h2 : (x ∘ (finSuccEquiv' k).symm) ∘ some = x ∘ k.succAbove := by
    ext i
    simp
  rw [h1, h2]

theorem UpperTheory.V.Z.Sym.Wt.hqThree :
    UpperTheory.V.Z.Sym.Wt.HqThree := by
  intro j a b
  have hv : (![a, 1, b] ∘ (1 : Fin 3).succAbove) = ![a, b] := by
    ext i
    fin_cases i <;> rfl
  rw [hs_succ ![a, 1, b] 1 j, hv, UpperTheory.V.Z.Sym.Wt.hqTwo]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, one_mul]
  ring
end

open Polynomial UpperTheory.V.Z.Sym.Wt

private theorem tr_pi {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, FiniteDimensional ℂ (V i)] (f : ∀ i, Module.End ℂ (V i)) (F : Module.End ℂ (∀ i, V i)) (h : ∀ x i, F x i = f i (x i)) :
    LinearMap.trace ℂ _ F = ∑ i, LinearMap.trace ℂ _ (f i) := by
  have e : F = ∑ i, (LinearMap.single ℂ V i) ∘ₗ (f i ∘ₗ LinearMap.proj i) := by
    refine LinearMap.ext fun x => funext fun k => ?_
    rw [h, LinearMap.sum_apply, Finset.sum_apply, Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb.symm]
    · simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.trace_comp_comm']
  congr 1
  ext x
  simp

theorem UpperTheory.V.Z.Sym.Wt.twineC :
    UpperTheory.V.Z.Sym.Wt.TwineC := by
  intro I _ _ j hj g τ h
  haveI : ∀ S : I → Bool, FiniteDimensional ℂ (Bi 3 (dg j S)) := fun S => finMH _ _ _
  rw [tr_pi (fun S : I → Bool => sg S • (biRep 3 (dg j S) g * swp 3 (dg j S))) _ fun x S => by
    rw [Module.End.mul_apply, repG_apply, thG_apply, map_smul]; rfl]
  simp only [map_smul, trSwap _, smul_eq_mul, sg, ← Finset.prod_mul_distrib, dg]
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum (fun _ : I => (Finset.univ : Finset Bool))
    fun v b => (if b = true then (-1 : ℂ) else 1) * tr1 3 (if b = true then j - 1 else j) (g v * invT ℂ 3 (g v))]
  refine Finset.prod_congr rfl fun v _ => ?_
  obtain ⟨a, ha⟩ : ∃ a : ℂ, a * a = τ v ^ 2 - 4 := IsAlgClosed.exists_eq_mul_self _ |>.imp fun _ h => h.symm
  have h1 : (τ v + a) / 2 + (τ v - a) / 2 = τ v := by ring
  have h2 : (τ v + a) / 2 * ((τ v - a) / 2) = 1 := by linear_combination (-1 / 4 : ℂ) * ha
  have hc : ((g v * invT ℂ 3 (g v) : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ).charpoly =
      ∏ i, (X - C (![(τ v + a) / 2, 1, (τ v - a) / 2] i)) := by
    rw [h, Fin.prod_univ_three]
    have e1 := congrArg (C : ℂ →+* ℂ[X]) h1
    have e2 := congrArg (C : ℂ →+* ℂ[X]) h2
    rw [map_add (f := _)] at e1
    rw [map_mul, map_one] at e2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, map_one]
    linear_combination (X - 1) * X * e1 - (X - 1) * e2
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have := hqThree k ((τ v + a) / 2) ((τ v - a) / 2)
  rw [h1, h2] at this
  rw [Fintype.sum_bool, ← this]
  simp only [if_true, Bool.false_eq_true, if_false, Nat.add_sub_cancel, trOne _ _ _ _ hc]
  ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.DetE
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.TrProd
open Polynomial UpperTheory.V.Z.Sym.Wt

theorem UpperTheory.V.Z.Sym.Wt.trProd :
    UpperTheory.V.Z.Sym.Wt.TrProd := by
  classical
  intro K _ d n g
  rw [trace_blocks n (sbs g).toLinearMap (mRep d n g) (fun P => rfl)]
  simp only [AlgHom.toLinearMap_apply]
  simp_rw [coeff_sbs_glue, symPowTrace_eq_sum_coeff]
  rw [Finset.prod_univ_sum]
end

open Polynomial UpperTheory.V.Z.Sym.Wt

private theorem tr1_two_eq_hq_trace_det (g : GL (Fin 2) ℂ) (n : ℕ) :
    tr1 2 n g = hq (↑g : Matrix (Fin 2) (Fin 2) ℂ).trace (↑g : Matrix (Fin 2) (Fin 2) ℂ).det n := by
  set A : Matrix (Fin 2) (Fin 2) ℂ := ↑g with hA
  have hs : A.charpoly.Splits := IsAlgClosed.splits _
  have hcard : Multiset.card A.charpoly.roots = 2 := by
    rw [IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.mp hcard
  have hp : A.charpoly = ∏ i, (X - C (![a, b] i)) := by
    rw [hs.eq_prod_roots_of_monic (Matrix.charpoly_monic A), hab]
    simp [Fin.prod_univ_two]
  have htr : A.trace = a + b := by
    rw [Matrix.trace_eq_sum_roots_charpoly, hab]; simp
  have hdet : A.det = a * b := by
    rw [Matrix.det_eq_prod_roots_charpoly, hab]; simp
  rw [trOne 2 n g ![a, b] hp, hqTwo, htr, hdet]

theorem UpperTheory.V.Z.Sym.Wt.trDC :
    UpperTheory.V.Z.Sym.Wt.TrDC := by
  intro I _ n e g
  rw [repD_apply, map_smul, smul_eq_mul]
  have h := trProd I 2 (fun _ => n) g
  simp only [VD] at *
  rw [h]
  simp only [detE, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_prod, Units.val_zpow_eq_zpow_val,
    Matrix.GeneralLinearGroup.val_det_apply]
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun v _ => by rw [tr1_two_eq_hq_trace_det]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.ThFacts
open Polynomial UpperTheory.V.Z.Sym.Wt

private theorem swp_eval {I : Type} [Fintype I] {d : ℕ} (n : I → ℕ) (Q : Bi d n) (x : (I × Bool) × Fin d → ℂ) :
    MvPolynomial.eval x (swp d n Q).1 = MvPolynomial.eval (x ∘ UpperTheory.V.Z.Sym.Wt.flip I d) Q.1 := MvPolynomial.eval_rename _ _ _

theorem UpperTheory.V.Z.Sym.Wt.thFacts :
    UpperTheory.V.Z.Sym.Wt.ThFacts := by
  intro I _ j
  have key : ∀ (n : I → ℕ) (g : I → GL (Fin 3) ℂ) (P : Bi 3 n),
      swp 3 n (biRep 3 n g P) = biRep 3 n (fun v => invT ℂ 3 (g v)) (swp 3 n P) := by
    intro n g P
    apply Subtype.ext
    apply MvPolynomial.funext
    intro x
    rw [swp_eval]
    change MvPolynomial.eval _ ((mRep 3 (fun k => n k.1) (dbl 3 g)) P).1 =
      MvPolynomial.eval x ((mRep 3 (fun k => n k.1) (dbl 3 (fun v => invT ℂ 3 (g v)))) (swp 3 n P)).1
    rw [eval_mRep, eval_mRep, swp_eval]
    refine congrArg (fun y => MvPolynomial.eval y P.1) ?_
    funext p
    obtain ⟨⟨v, b⟩, i⟩ := p
    cases b <;> simp [act, UpperTheory.V.Z.Sym.Wt.flip, dbl, invT_invT]
  have hswp : ∀ (n : I → ℕ) (P : Bi 3 n), swp 3 n (swp 3 n P) = P := by
    intro n P
    apply Subtype.ext
    apply MvPolynomial.funext
    intro x
    rw [swp_eval, swp_eval]
    refine congrArg (fun y => MvPolynomial.eval y P.1) ?_
    funext p
    simp [UpperTheory.V.Z.Sym.Wt.flip]
  have hsg : ∀ S : I → Bool, sg S * sg S = 1 := by
    intro S
    simp only [sg, ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro v _
    split_ifs <;> norm_num
  refine ⟨?_, ?_⟩
  · apply LinearMap.ext
    intro P
    funext S
    simp only [Module.End.mul_apply, thG_apply, map_smul, smul_smul, hswp, hsg, one_smul, Module.End.one_apply]
  · intro g
    apply LinearMap.ext
    intro P
    funext S
    simp only [Module.End.mul_apply, thG_apply, repG_apply, map_smul, key]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.Scalars
open Polynomial UpperTheory.V.Z.Sym.Wt

private theorem mRep_scal {K : Type} [Fintype K] {d : ℕ} (n : K → ℕ) (s : K → ℂˣ) (Q : MH d n) :
    mRep d n (fun k => Matrix.GeneralLinearGroup.scalar (Fin d) (s k)) Q = (∏ k, (s k : ℂ) ^ n k) • Q := by
  apply Subtype.ext
  apply MvPolynomial.funext
  intro x
  rw [eval_mRep]
  have hact : act (fun k => Matrix.GeneralLinearGroup.scalar (Fin d) (s k)) x = fun p => (s p.1 : ℂ) * x p := by
    funext p
    simp [act, Matrix.scalar_apply, Matrix.diagonal_apply, mul_comm]
  rw [hact, Q.2 (fun k => (s k : ℂ)) x]
  simp

private theorem invT_scal {d : ℕ} (s : ℂˣ) :
    invT ℂ d (Matrix.GeneralLinearGroup.scalar (Fin d) s) = Matrix.GeneralLinearGroup.scalar (Fin d) s⁻¹ := by
  refine Units.ext ?_
  rw [invT_val, ← map_inv]
  exact Matrix.diagonal_transpose _

theorem UpperTheory.V.Z.Sym.Wt.scalars :
    UpperTheory.V.Z.Sym.Wt.Scalars := by
  intro I _ s
  refine ⟨fun j => ?_, fun n e => ?_⟩
  · have hd : dbl 3 (fun v ↦ Matrix.GeneralLinearGroup.scalar (Fin 3) (s v)) =
        fun k => Matrix.GeneralLinearGroup.scalar (Fin 3) (if k.2 then (s k.1)⁻¹ else s k.1) := by
      funext k
      obtain ⟨v, b⟩ := k
      cases b <;> simp [dbl, invT_scal]
    apply LinearMap.ext
    intro P
    funext S
    rw [repG_apply, Module.End.one_apply]
    change mRep 3 (fun k => dg j S k.1) (dbl 3 _) (P S) = P S
    rw [hd, mRep_scal]
    convert one_smul ℂ (P S)
    rw [Fintype.prod_prod_type]
    apply Finset.prod_eq_one
    intro v _
    rw [Fintype.prod_bool]
    simp
  · apply LinearMap.ext
    intro P
    rw [repD_apply, LinearMap.smul_apply, mRep_scal, smul_smul, LinearMap.smul_apply, Module.End.one_apply]
    congr 1
    simp only [detE, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_prod, Units.val_zpow_eq_zpow_val]
    simp
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    have ha : (s v : ℂ) ≠ 0 := (s v).ne_zero
    rw [zpow_add₀ ha, zpow_mul, zpow_natCast, mul_comm]
    norm_cast
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.HqKappa
open Polynomial
namespace UpperTheory.V.Z.Sym.Wt
private theorem hq_kap (τ : ℂ) (j : ℕ) : hq (2 + τ) (2 + τ) (2 * j + 1) = (2 + τ) ^ (j + 1) * hq τ 1 j ∧ hq (2 + τ) (2 + τ) (2 * (j+1) + 1) = (2 + τ) ^ (j + 2) * hq τ 1 (j+1) := by
  have e : ∀ i, hq (2 + τ) (2 + τ) (i + 2) = (2 + τ) * hq (2 + τ) (2 + τ) (i + 1) - (2 + τ) * hq (2 + τ) (2 + τ) i :=
    fun i => hq.eq_3 _ _ i
  have f : ∀ i, hq τ 1 (i + 2) = τ * hq τ 1 (i + 1) - 1 * hq τ 1 i := fun i => hq.eq_3 _ _ i
  induction j with
  | zero =>
    have e2 : hq (2 + τ) (2 + τ) 2 = (2 + τ) * hq (2 + τ) (2 + τ) 1 - (2 + τ) * hq (2 + τ) (2 + τ) 0 := e 0
    have e3 : hq (2 + τ) (2 + τ) 3 = (2 + τ) * hq (2 + τ) (2 + τ) 2 - (2 + τ) * hq (2 + τ) (2 + τ) 1 := e 1
    refine ⟨?_, ?_⟩
    · show hq (2 + τ) (2 + τ) 1 = (2 + τ) ^ 1 * hq τ 1 0
      rw [hq.eq_2, hq.eq_1]
      ring
    · show hq (2 + τ) (2 + τ) 3 = (2 + τ) ^ 2 * hq τ 1 1
      rw [e3, e2, hq.eq_2, hq.eq_1, hq.eq_2]
      ring
  | succ j ih =>
    refine ⟨ih.2, ?_⟩
    have e5 : hq (2 + τ) (2 + τ) (2 * j + 5) =
        (2 + τ) * hq (2 + τ) (2 + τ) (2 * j + 4) - (2 + τ) * hq (2 + τ) (2 + τ) (2 * j + 3) := e (2 * j + 3)
    have e4 : hq (2 + τ) (2 + τ) (2 * j + 4) =
        (2 + τ) * hq (2 + τ) (2 + τ) (2 * j + 3) - (2 + τ) * hq (2 + τ) (2 + τ) (2 * j + 2) := e (2 * j + 2)
    have e3 : hq (2 + τ) (2 + τ) (2 * j + 3) =
        (2 + τ) * hq (2 + τ) (2 + τ) (2 * j + 2) - (2 + τ) * hq (2 + τ) (2 + τ) (2 * j + 1) := e (2 * j + 1)
    have f2 : hq τ 1 (j + 2) = τ * hq τ 1 (j + 1) - 1 * hq τ 1 j := f j
    have i0 : hq (2 + τ) (2 + τ) (2 * j + 1) = (2 + τ) ^ (j + 1) * hq τ 1 j := ih.1
    have i1 : hq (2 + τ) (2 + τ) (2 * j + 3) = (2 + τ) ^ (j + 2) * hq τ 1 (j + 1) := ih.2
    show hq (2 + τ) (2 + τ) (2 * j + 5) = (2 + τ) ^ (j + 3) * hq τ 1 (j + 2)
    rw [f2]
    linear_combination e5 + (2 + τ) * e4 + (2 + τ) * e3 + ((2 + τ) ^ 2 - 2 * (2 + τ)) * i1 - (2 + τ) ^ 2 * i0
theorem hqKappa : HqKappa := fun j τ => (hq_kap τ j).1
end UpperTheory.V.Z.Sym.Wt
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.MainOf
open Polynomial
namespace UpperTheory.V.Z.Sym.Wt

private theorem map_invT {R : Type} [CommRing R] (f : R →+* ℂ) (d : ℕ) (g : GL (Fin d) R) :
    Matrix.GeneralLinearGroup.map f (invT R d g) = invT ℂ d (Matrix.GeneralLinearGroup.map f g) := by
  ext i k
  rw [Matrix.GeneralLinearGroup.map_apply, invT_val, invT_val, ← map_inv, Matrix.transpose_apply,
    Matrix.transpose_apply, Matrix.GeneralLinearGroup.map_apply]

private theorem map_scal {R : Type} [CommRing R] (f : R →+* ℂ) (d : ℕ) (x : Rˣ) :
    Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.scalar (Fin d) x) =
      Matrix.GeneralLinearGroup.scalar (Fin d) (Units.map f.toMonoidHom x) := by
  ext i k
  rw [Matrix.GeneralLinearGroup.map_apply]
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply, apply_ite f]

private theorem val_map {R : Type} [CommRing R] (f : R →+* ℂ) (d : ℕ) (g : GL (Fin d) R) :
    ((Matrix.GeneralLinearGroup.map f g : GL (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) = (g : Matrix (Fin d) (Fin d) R).map f := rfl

theorem wtMain_of (h1 : FinMH) (h2 : ThFacts) (h3 : TwineC) (h4 : TrDC) (h5 : Scalars) (h6 : HqKappa) : WtMain := by
  intro R I _ _ em j hj
  classical
  have hWG : ∀ g : GL (Fin 3) R,
      WG em j g = repG I j (fun w => Matrix.GeneralLinearGroup.map (em w) g) := fun _ => rfl
  have hWD : ∀ (n : ℕ) (e : ℤ) (g : GL (Fin 2) R),
      WD em n e g = repD I n e (fun w => Matrix.GeneralLinearGroup.map (em w) g) := fun _ _ _ => rfl
  have hdet : ∀ (w : I) (g : GL (Fin 2) R),
      ((Matrix.GeneralLinearGroup.map (em w) g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det =
        em w (g : Matrix (Fin 2) (Fin 2) R).det := by
    intro w g
    rw [val_map, RingHom.map_det]
    rfl
  have htr : ∀ (w : I) (g : GL (Fin 2) R),
      ((Matrix.GeneralLinearGroup.map (em w) g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).trace =
        em w (g : Matrix (Fin 2) (Fin 2) R).trace := by
    intro w g
    rw [val_map, AddMonoidHom.map_trace]
  refine
    { finG := ?_, finD := ?_, th_sq := (h2 I j).1, th_rep := ?_, scalG := ?_, scalD := ?_,
      twine := ?_, stable := ?_, kappa := ?_ }
  · haveI : ∀ S : I → Bool, FiniteDimensional ℂ (Bi 3 (dg j S)) := fun S => h1 _ _ _
    infer_instance
  · intro n
    exact h1 _ _ _
  · intro g
    rw [hWG, hWG, (h2 I j).2]
    have hfun : (fun v => invT ℂ 3 (Matrix.GeneralLinearGroup.map (em v) g)) =
        fun w => Matrix.GeneralLinearGroup.map (em w) (invT R 3 g) :=
      funext fun v => (map_invT _ _ _).symm
    rw [hfun]
  · intro x
    rw [hWG]
    have hfun : (fun w => Matrix.GeneralLinearGroup.map (em w) (Matrix.GeneralLinearGroup.scalar (Fin 3) x)) =
        fun w => Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.map (em w).toMonoidHom x) :=
      funext fun w => map_scal _ _ _
    rw [hfun]
    exact (h5 I _).1 j
  · intro n e x
    rw [hWD]
    have hfun : (fun w => Matrix.GeneralLinearGroup.map (em w) (Matrix.GeneralLinearGroup.scalar (Fin 2) x)) =
        fun w => Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (em w).toMonoidHom x) :=
      funext fun w => map_scal _ _ _
    rw [hfun, (h5 I _).2 n e]
    congr 1
    rw [Units.coe_prod]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [Units.val_zpow_eq_zpow_val, Units.coe_map]
    rfl
  · intro δ τ hch
    rw [hWG]
    refine h3 I j hj (fun w => Matrix.GeneralLinearGroup.map (em w) δ) (fun w => em w τ) ?_
    intro v
    rw [← map_invT, ← map_mul, val_map, Matrix.charpoly_map, hch]
    simp [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_add (f := _)]
  · intro e γ hγ
    rw [hWD, h4]
    show _ = ∏ w, hq (em w (γ : Matrix (Fin 2) (Fin 2) R).trace) 1 j
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [hdet, htr, hγ, map_one, one_zpow, one_mul]
  · intro z τ htz hdz
    rw [hWD, h4]
    show _ = ∏ w, hq (em w τ) 1 j
    refine Finset.prod_congr rfl fun w _ => ?_
    have hu : em w (z : Matrix (Fin 2) (Fin 2) R).det ≠ 0 := by
      have hz : IsUnit (z : Matrix (Fin 2) (Fin 2) R).det := by
        rw [← Matrix.GeneralLinearGroup.val_det_apply]
        exact Units.isUnit _
      exact (hz.map (em w)).ne_zero
    rw [hdet, htr, htz, hdz, map_add (f := _), map_ofNat, h6 j (em w τ)]
    rw [hdz, map_add (f := _), map_ofNat] at hu
    rw [zpow_neg, show ((j : ℤ) + 1) = ((j + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
      inv_mul_cancel_left₀ (pow_ne_zero _ hu)]

end UpperTheory.V.Z.Sym.Wt
end

theorem UpperTheory.V.Z.Sym.Wt.wtMain : UpperTheory.V.Z.Sym.Wt.WtMain :=
  UpperTheory.V.Z.Sym.Wt.wtMain_of UpperTheory.V.Z.Sym.Wt.finMH UpperTheory.V.Z.Sym.Wt.thFacts UpperTheory.V.Z.Sym.Wt.twineC UpperTheory.V.Z.Sym.Wt.trDC
    UpperTheory.V.Z.Sym.Wt.scalars UpperTheory.V.Z.Sym.Wt.hqKappa
end

noncomputable section

open UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

namespace UpperTheory.V.Z.Sym.Wt

variable {K I : Type} [Field K] [Fintype I] {Δ : K} (em : I → Lsq K Δ →+* ℂ) (j : ℕ)

def cG : Representation ℂ (U3 Δ) (VG I j) := (WG em j).comp Unitary.toUnits

def cD (n : ℕ) (e : ℤ) : Representation ℂ (DX Δ) (VD I n) := (WD em n e).comp (DX Δ).subtype

def cS : Representation ℂ (SU Δ) (VD I j) := (cD em j 0).comp (SU Δ).subtype

abbrev cK : Representation ℂ (DX Δ) (VD I (2 * j + 1)) := cD em (2 * j + 1) (-((j : ℤ) + 1))

def ch (τ : K) : ℂ := chi em j (algebraMap K _ τ)

theorem toUnits_theta (g : U3 Δ) :
    (Unitary.toUnits (theta Δ g) : GL (Fin 3) (Lsq K Δ)) = invT _ 3 (Unitary.toUnits g) := by
  exact Units.ext (Matrix.ext fun _ _ => rfl)

variable {j}

theorem cG_int (hj : 1 ≤ j) (γ : U3 Δ) (v : VG I j) : thG I j (cG em j γ v) = cG em j (theta Δ γ) (thG I j v) := by
  have := LinearMap.congr_fun ((wtMain _ I em j hj).th_rep (Unitary.toUnits γ)) v
  rw [← toUnits_theta] at this
  exact this

theorem cG_tr (hj : 1 ≤ j) (δ : U3 Δ) (τ : K) (h : HasTau δ τ) : LinearMap.trace ℂ _ (cG em j δ ∘ₗ thG I j) = ch em j τ := by
  refine (wtMain _ I em j hj).twine (Unitary.toUnits δ) _ ?_
  rw [← toUnits_theta, ← map_mul]
  exact h

theorem cS_tr (hj : 1 ≤ j) (γ : SU Δ) (τ : K) (h : HasTr (γ : DX Δ) τ) : LinearMap.trace ℂ _ (cS em j γ) = ch em j τ := by
  have := (wtMain _ I em j hj).stable 0 ((γ : DX Δ) : GL (Fin 2) (Lsq K Δ)) h.1
  rw [h.2] at this
  exact this

theorem cK_tr (hj : 1 ≤ j) (g : DX Δ) (τ : K) (h : (mt g).trace = algebraMap K _ (2 + τ)) (h' : (mt g).det = algebraMap K _ (2 + τ)) :
    LinearMap.trace ℂ _ (cK em j g) = ch em j τ :=
  (wtMain _ I em j hj).kappa g _ (by rw [h, map_add (f := _), map_ofNat]) (by rw [h', map_add (f := _), map_ofNat])

theorem cK_scal (hj : 1 ≤ j) (z : Kˣ) (s : DX Δ) (h : IsScal z s) (v : VD I (2 * j + 1)) :
    cK em j s v = (∏ w, em w (algebraMap K _ (z : K)))⁻¹ • v := by
  have e : (s : GL (Fin 2) (Lsq K Δ)) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap K (Lsq K Δ) : K →* Lsq K Δ) z) := Units.ext h
  have := LinearMap.congr_fun ((wtMain _ I em j hj).scalD (2 * j + 1) (-((j : ℤ) + 1)) (Units.map (algebraMap K (Lsq K Δ) : K →* Lsq K Δ) z)) v
  rw [← e, show ((2 * j + 1 : ℕ) : ℤ) + 2 * -((j : ℤ) + 1) = -1 by push_cast; ring] at this
  rw [← Finset.prod_inv_distrib]
  simp only [zpow_neg_one] at this
  exact this

end UpperTheory.V.Z.Sym.Wt

end
