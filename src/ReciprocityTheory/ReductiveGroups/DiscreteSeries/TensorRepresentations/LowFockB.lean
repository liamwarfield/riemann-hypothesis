module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CFPrimeA

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.LowFockA
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem lfa_mul_of_not_disjoint (s t : Finset (Fin (n * n))) (h : ¬ Disjoint s t) :
    fockBasis n s * fockBasis n t = 0 := by
  exact ExteriorAlgebra.basis_mul_of_not_disjoint _ (Set.powersetCard.ofCard (rfl : s.card = s.card))
    (Set.powersetCard.ofCard (rfl : t.card = t.card)) h

theorem eq_sign_smul_of_intUnit {A : Type*} [AddCommGroup A] [Module ℂ A] (u : ℤˣ) (x y : A) (h : x = u • y) :
    ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧ x = σ • y := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact ⟨1, Or.inl rfl, by simpa using h⟩
  · exact ⟨-1, Or.inr rfl, by simpa using h⟩

theorem lfa_mul_of_disjoint (s t : Finset (Fin (n * n))) (h : Disjoint s t) :
    ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧ fockBasis n s * fockBasis n t = σ • fockBasis n (s ∪ t) := by
  have hm := ExteriorAlgebra.basis_mul_of_disjoint ((Pi.basisFun ℂ (Fin n × Fin n)).reindex finProdFinEquiv)
    (Set.powersetCard.ofCard (rfl : s.card = s.card)) (Set.powersetCard.ofCard (rfl : t.card = t.card)) h
  obtain ⟨σ, hσ, h'⟩ := eq_sign_smul_of_intUnit _ _ _ hm
  refine ⟨σ, hσ, h'.trans ?_⟩
  exact congrArg (fun U => σ • fockBasis n U) (Finset.disjUnion_eq_union s t h)

theorem lfa_basis_list (S : Finset (Fin (n * n))) :
    fockBasis n S = ((List.ofFn fun i => finProdFinEquiv.symm (S.orderEmbOfFin rfl i)).map
      fun y => ExteriorAlgebra.ι ℂ (Pi.single y (1 : ℂ))).prod := by
  rw [fockBasis, ExteriorAlgebra.basis_apply_ofCard _ (rfl : S.card = S.card), ExteriorAlgebra.ιMulti_family,
    ExteriorAlgebra.ιMulti_apply, List.map_ofFn]
  congr 2
  funext i
  simp [Set.powersetCard.ofFinEmbEquiv_symm_apply]

theorem lf_basis_singleton (x : Fin n × Fin n) :
    fockBasis n {finProdFinEquiv x} = ExteriorAlgebra.ι ℂ (Pi.single x (1 : ℂ)) := by
  rw [fockBasis, ExteriorAlgebra.basis_apply_ofCard _ (Finset.card_singleton _), ExteriorAlgebra.ιMulti_family,
    ExteriorAlgebra.ιMulti_apply]
  simp [Set.powersetCard.ofFinEmbEquiv_symm_apply, Set.powersetCard.val_ofCard]

theorem lfa_cp_apply (x : Fin n × Fin n) (v : Fock n) :
    cpFock x.1 x.2 v = fockBasis n {finProdFinEquiv x} * v := by
  rw [lf_basis_singleton]
  rfl

theorem lfa_cm_list (x : Fin n × Fin n) (l : List (Fin n × Fin n)) (hx : x ∉ l) :
    cmFock x.1 x.2 (l.map fun y => ExteriorAlgebra.ι ℂ (Pi.single y (1 : ℂ))).prod = 0 := by
  induction l with
  | nil => simp [cmFock]
  | cons y l ih =>
    rw [List.mem_cons, not_or] at hx
    have ih' := ih hx.2
    simp only [cmFock] at ih' ⊢
    rw [List.map_cons, List.prod_cons, CliffordAlgebra.contractLeft_ι_mul, ih']
    simp [hx.1]

theorem lf_cp_basis_of_mem {x : Fin n × Fin n} {S : Finset (Fin (n * n))} (hx : finProdFinEquiv x ∈ S) :
    cpFock x.1 x.2 (fockBasis n S) = 0 := by
  rw [lfa_cp_apply]
  exact lfa_mul_of_not_disjoint _ _ (Finset.not_disjoint_iff.mpr ⟨_, Finset.mem_singleton_self _, hx⟩)

theorem lf_cm_basis_of_not_mem {x : Fin n × Fin n} {S : Finset (Fin (n * n))} (hx : finProdFinEquiv x ∉ S) :
    cmFock x.1 x.2 (fockBasis n S) = 0 := by
  rw [lfa_basis_list]
  apply lfa_cm_list
  intro hmem
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
  apply hx
  rw [← hi, Equiv.apply_symm_apply]
  exact Finset.orderEmbOfFin_mem S rfl i

theorem lf_cp_cm_basis {x : Fin n × Fin n} {S : Finset (Fin (n * n))} (hx : finProdFinEquiv x ∉ S) :
    ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧
      cpFock x.1 x.2 (fockBasis n S) = σ • fockBasis n (insert (finProdFinEquiv x) S) ∧
      cmFock x.1 x.2 (fockBasis n (insert (finProdFinEquiv x) S)) = σ • fockBasis n S := by
  obtain ⟨σ, hσ, h⟩ := lfa_mul_of_disjoint {finProdFinEquiv x} S (Finset.disjoint_singleton_left.mpr hx)
  rw [← Finset.insert_eq] at h
  have hcp : cpFock x.1 x.2 (fockBasis n S) = σ • fockBasis n (insert (finProdFinEquiv x) S) := by
    rw [lfa_cp_apply, h]
  have hcmcp : cmFock x.1 x.2 (cpFock x.1 x.2 (fockBasis n S)) = fockBasis n S := by
    have h0 := lf_cm_basis_of_not_mem hx
    simp only [cpFock, cmFock, LinearMap.mulLeft_apply] at h0 ⊢
    rw [CliffordAlgebra.contractLeft_ι_mul, h0]
    simp
  have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  refine ⟨σ, hσ, hcp, ?_⟩
  rw [hcp, map_smul] at hcmcp
  calc cmFock x.1 x.2 (fockBasis n (insert (finProdFinEquiv x) S))
      = (σ * σ) • cmFock x.1 x.2 (fockBasis n (insert (finProdFinEquiv x) S)) := by rw [hσσ, one_smul]
    _ = σ • fockBasis n S := by rw [← smul_smul, hcmcp]

theorem lf_cm_basis_of_mem {x : Fin n × Fin n} {S : Finset (Fin (n * n))} (hx : finProdFinEquiv x ∈ S) :
    ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧
      cmFock x.1 x.2 (fockBasis n S) = σ • fockBasis n (S.erase (finProdFinEquiv x)) ∧
      cpFock x.1 x.2 (fockBasis n (S.erase (finProdFinEquiv x))) = σ • fockBasis n S := by
  obtain ⟨σ, hσ, h1, h2⟩ := lf_cp_cm_basis (Finset.notMem_erase (finProdFinEquiv x) S)
  rw [Finset.insert_erase hx] at h1 h2
  exact ⟨σ, hσ, h2, h1⟩

theorem lf_num_basis (x : Fin n × Fin n) (S : Finset (Fin (n * n))) :
    cpFock x.1 x.2 (cmFock x.1 x.2 (fockBasis n S)) =
      if finProdFinEquiv x ∈ S then fockBasis n S else 0 := by
  split_ifs with hx
  · obtain ⟨σ, hσ, h1, h2⟩ := lf_cm_basis_of_mem hx
    rw [h1, map_smul, h2, smul_smul]
    rcases hσ with rfl | rfl <;> norm_num
  · rw [lf_cm_basis_of_not_mem hx, map_zero]

theorem lf_repr_cm_eq (x : Fin n × Fin n) (S T : Finset (Fin (n * n))) :
    (fockBasis n).repr (cmFock x.1 x.2 (fockBasis n S)) T =
      (fockBasis n).repr (cpFock x.1 x.2 (fockBasis n T)) S := by
  by_cases hT : finProdFinEquiv x ∈ T
  · rw [lf_cp_basis_of_mem hT, map_zero, Finsupp.zero_apply]
    by_cases hS : finProdFinEquiv x ∈ S
    · obtain ⟨σ, -, h1, -⟩ := lf_cm_basis_of_mem hS
      rw [h1, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, if_neg, smul_zero]
      intro h
      rw [← h] at hT
      exact Finset.notMem_erase _ _ hT
    · rw [lf_cm_basis_of_not_mem hS, map_zero, Finsupp.zero_apply]
  · obtain ⟨τ, -, h1, h2⟩ := lf_cp_cm_basis hT
    rw [h1, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
    by_cases hST : insert (finProdFinEquiv x) T = S
    · subst hST
      rw [if_pos rfl, h2, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, if_pos rfl]
    · rw [if_neg hST, smul_zero]
      by_cases hS : finProdFinEquiv x ∈ S
      · obtain ⟨σ, -, h3, -⟩ := lf_cm_basis_of_mem hS
        rw [h3, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, if_neg, smul_zero]
        intro h
        apply hST
        rw [← h, Finset.insert_erase hS]
      · rw [lf_cm_basis_of_not_mem hS, map_zero, Finsupp.zero_apply]

theorem lf_repr_cp_star (x : Fin n × Fin n) (S T : Finset (Fin (n * n))) :
    star ((fockBasis n).repr (cpFock x.1 x.2 (fockBasis n S)) T) =
      (fockBasis n).repr (cpFock x.1 x.2 (fockBasis n S)) T := by
  by_cases hS : finProdFinEquiv x ∈ S
  · rw [lf_cp_basis_of_mem hS]
    simp
  · obtain ⟨τ, hτ, h1, -⟩ := lf_cp_cm_basis hS
    rw [h1, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
    split_ifs <;> rcases hτ with rfl | rfl <;> simp

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def lfPhysModes (ε : Fin n → Bool) : Finset (Fin (n * n)) :=
  univ.filter fun m => ε (finProdFinEquiv.symm m).1 = true ∧ ε (finProdFinEquiv.symm m).2 = false

abbrev LfIdx (ε : Fin n → Bool) : Type := {S : Finset (Fin (n * n)) // S ⊆ lfPhysModes ε}

def lfMatFull (ε : Fin n → Bool) (a b : Fin n) : Matrix (Finset (Fin (n * n))) (Finset (Fin (n * n))) ℂ :=
  LinearMap.toMatrix (fockBasis n) (fockBasis n) (sgE ε cpFock cmFock a b)

def lfMat (ε : Fin n → Bool) (a b : Fin n) : Matrix (LfIdx ε) (LfIdx ε) ℂ :=
  (lfMatFull ε a b).submatrix Subtype.val Subtype.val

def lfP (i a : Fin n) : Matrix (Finset (Fin (n * n))) (Finset (Fin (n * n))) ℂ :=
  LinearMap.toMatrix (fockBasis n) (fockBasis n) (cpFock i a)

theorem lf_toMatrix_cp (i a : Fin n) :
    LinearMap.toMatrix (fockBasis n) (fockBasis n) (cpFock i a) = lfP i a := rfl

theorem lf_toMatrix_cm (i a : Fin n) :
    LinearMap.toMatrix (fockBasis n) (fockBasis n) (cmFock i a) = (lfP i a)ᵀ := by
  ext T S
  simp only [LinearMap.toMatrix_apply, lfP, transpose_apply]
  exact lf_repr_cm_eq (i, a) S T

theorem fockMatrix_conjTranspose_eq_transpose (i a : Fin n) : (lfP i a)ᴴ = (lfP i a)ᵀ := by
  ext T S
  simp only [conjTranspose_apply, transpose_apply, lfP, LinearMap.toMatrix_apply]
  exact lf_repr_cp_star (i, a) T S

theorem fockMatrix_transpose_conjTranspose (i a : Fin n) : (lfP i a)ᵀᴴ = lfP i a := by
  rw [← fockMatrix_conjTranspose_eq_transpose, Matrix.conjTranspose_conjTranspose]

theorem lfMatFull_eq (ε : Fin n → Bool) (a b : Fin n) : lfMatFull ε a b =
    if ε a = true ∧ ε b = true then ∑ x ∈ minusIdx ε, lfP a x * (lfP b x)ᵀ
    else if ε a = false ∧ ε b = false then -∑ i ∈ plusIdx ε, lfP i b * (lfP i a)ᵀ
    else 0 := by
  unfold lfMatFull sgE
  split_ifs <;> simp only [map_sum, map_neg, map_zero, LinearMap.toMatrix_mul, lf_toMatrix_cp, lf_toMatrix_cm]

theorem lfMatFull_kRel (ε : Fin n → Bool) : Formalism.REAL.KRel ε (lfMatFull ε) := by
  intro a b c d hab hcd
  have h := congrArg (LinearMap.toMatrix (fockBasis n) (fockBasis n))
    (sgE_comm isCAR_fock ε a b c d hab hcd)
  split_ifs at h ⊢ <;> simpa only [lfMatFull, map_sub, map_zero, LinearMap.toMatrix_mul] using h

theorem lfMatFull_conjTranspose (ε : Fin n → Bool) {a b : Fin n} (h : ε a = ε b) :
    lfMatFull ε b a = (lfMatFull ε a b)ᴴ := by
  rw [lfMatFull_eq, lfMatFull_eq]
  simp only [h]
  split_ifs <;> simp [Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, fockMatrix_conjTranspose_eq_transpose,
    fockMatrix_transpose_conjTranspose, Matrix.conjTranspose_neg]

theorem lf_mem_phys (ε : Fin n → Bool) (i a : Fin n) :
    finProdFinEquiv (i, a) ∈ lfPhysModes ε ↔ ε i = true ∧ ε a = false := by
  simp only [lfPhysModes, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]

theorem lf_cm_phys {ε : Fin n → Bool} (i a : Fin n) {S : Finset (Fin (n * n))} (hS : S ⊆ lfPhysModes ε) :
    ∃ c : ℂ, ∃ U, U ⊆ lfPhysModes ε ∧ cmFock i a (fockBasis n S) = c • fockBasis n U := by
  by_cases hx : finProdFinEquiv (i, a) ∈ S
  · obtain ⟨σ, -, h1, -⟩ := lf_cm_basis_of_mem (x := (i, a)) hx
    exact ⟨σ, S.erase (finProdFinEquiv (i, a)), (Finset.erase_subset _ _).trans hS, h1⟩
  · exact ⟨0, S, hS, by rw [zero_smul]; exact lf_cm_basis_of_not_mem (x := (i, a)) hx⟩

theorem lf_cp_phys {ε : Fin n → Bool} {i a : Fin n} (hia : ε i = true ∧ ε a = false)
    {S : Finset (Fin (n * n))} (hS : S ⊆ lfPhysModes ε) :
    ∃ c : ℂ, ∃ U, U ⊆ lfPhysModes ε ∧ cpFock i a (fockBasis n S) = c • fockBasis n U := by
  by_cases hx : finProdFinEquiv (i, a) ∈ S
  · exact ⟨0, S, hS, by rw [zero_smul]; exact lf_cp_basis_of_mem (x := (i, a)) hx⟩
  · obtain ⟨σ, -, h1, -⟩ := lf_cp_cm_basis (x := (i, a)) hx
    exact ⟨σ, insert (finProdFinEquiv (i, a)) S, Finset.insert_subset ((lf_mem_phys ε i a).2 hia) hS, h1⟩

theorem lf_cpcm_repr {ε : Fin n → Bool} {i a : Fin n} (j b : Fin n) (hia : ε i = true ∧ ε a = false)
    {S T : Finset (Fin (n * n))} (hS : S ⊆ lfPhysModes ε) (hT : ¬ T ⊆ lfPhysModes ε) :
    (fockBasis n).repr ((cpFock i a * cmFock j b) (fockBasis n S)) T = 0 := by
  obtain ⟨c, U, hU, hcm⟩ := lf_cm_phys (ε := ε) j b hS
  obtain ⟨c', U', hU', hcp⟩ := lf_cp_phys hia hU
  have e : (cpFock i a * cmFock j b) (fockBasis n S) = (c * c') • fockBasis n U' := by
    show cpFock i a (cmFock j b (fockBasis n S)) = _
    rw [hcm, map_smul, hcp, smul_smul]
  rw [e, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, if_neg, smul_zero]
  rintro rfl
  exact hT hU'

theorem lfMatFull_eq_zero (ε : Fin n → Bool) (a b : Fin n) {S T : Finset (Fin (n * n))}
    (hS : S ⊆ lfPhysModes ε) (hT : ¬ T ⊆ lfPhysModes ε) : lfMatFull ε a b T S = 0 := by
  rw [lfMatFull, LinearMap.toMatrix_apply]
  unfold sgE
  split_ifs with h1 h2
  · set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.sum_apply, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun x hx => ?_
    exact lf_cpcm_repr b x ⟨h1.1, by simpa [minusIdx] using hx⟩ hS hT
  · set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.neg_apply, LinearMap.sum_apply, map_neg, map_sum, Finsupp.coe_neg, Pi.neg_apply,
      Finsupp.coe_finsetSum, Finset.sum_apply, neg_eq_zero]
    refine Finset.sum_eq_zero fun i hi => ?_
    exact lf_cpcm_repr i a ⟨by simpa [plusIdx] using hi, h2.2⟩ hS hT
  · simp

theorem lfMat_mul_apply (ε : Fin n → Bool) (a b c d : Fin n) (T S : LfIdx ε) :
    (lfMat ε a b * lfMat ε c d) T S = (lfMatFull ε a b * lfMatFull ε c d) T.1 S.1 := by
  simp only [Matrix.mul_apply, lfMat, Matrix.submatrix_apply]
  have key : ∑ U : Finset (Fin (n * n)), lfMatFull ε a b T.1 U * lfMatFull ε c d U S.1 =
      ∑ U ∈ Finset.univ.filter (fun U : Finset (Fin (n * n)) => U ⊆ lfPhysModes ε),
        lfMatFull ε a b T.1 U * lfMatFull ε c d U S.1 := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro U _ hU
    have hU' : ¬ U ⊆ lfPhysModes ε := by simpa using hU
    rw [lfMatFull_eq_zero ε c d S.2 hU', mul_zero]
  rw [key, Finset.sum_subtype (p := fun U : Finset (Fin (n * n)) => U ⊆ lfPhysModes ε) _ (fun U => by simp)]

theorem lfMat_kRel (ε : Fin n → Bool) : Formalism.REAL.KRel ε (lfMat ε) := by
  intro a b c d hab hcd
  ext T S
  have h := congrFun (congrFun (lfMatFull_kRel ε a b c d hab hcd) T.1) S.1
  simp only [Matrix.sub_apply, lfMat_mul_apply] at h ⊢
  split_ifs at h ⊢ <;> simpa only [lfMat, Matrix.submatrix_apply, Matrix.zero_apply] using h

theorem lfMat_conjTranspose (ε : Fin n → Bool) {a b : Fin n} (h : ε a = ε b) :
    lfMat ε b a = (lfMat ε a b)ᴴ := by
  ext T S
  simp only [lfMat, Matrix.submatrix_apply, Matrix.conjTranspose_apply]
  rw [lfMatFull_conjTranspose ε h, Matrix.conjTranspose_apply]

theorem lfMat_basis (ε : Fin n → Bool) (a b : Fin n) (S : LfIdx ε) :
    sgE ε cpFock cmFock a b (fockBasis n S.1) = ∑ T : LfIdx ε, lfMat ε a b T S • fockBasis n T.1 := by
  have key : sgE ε cpFock cmFock a b (fockBasis n S.1) =
      ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin (n * n)) => T ⊆ lfPhysModes ε),
        (fockBasis n).repr (sgE ε cpFock cmFock a b (fockBasis n S.1)) T • fockBasis n T := by
    conv_lhs => rw [← (fockBasis n).sum_repr (sgE ε cpFock cmFock a b (fockBasis n S.1))]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro T _ hT
    have hT' : ¬ T ⊆ lfPhysModes ε := by simpa using hT
    have h0 := lfMatFull_eq_zero ε a b S.2 hT'
    rw [lfMatFull, LinearMap.toMatrix_apply] at h0
    rw [h0, zero_smul]
  rw [key, Finset.sum_subtype (p := fun T : Finset (Fin (n * n)) => T ⊆ lfPhysModes ε) _ (fun T => by simp)]
  refine Finset.sum_congr rfl fun T _ => ?_
  simp only [lfMat, lfMatFull, Matrix.submatrix_apply, LinearMap.toMatrix_apply]

theorem lfMat_mulVec_single (ε : Fin n → Bool) (a b : Fin n) (S : LfIdx ε) (c : ℂ)
    (h : sgE ε cpFock cmFock a b (fockBasis n S.1) = c • fockBasis n S.1) :
    lfMat ε a b *ᵥ Pi.single S 1 = c • Pi.single S 1 := by
  ext T
  rw [Matrix.mulVec_single_one, Matrix.col_apply]
  simp only [lfMat, Matrix.submatrix_apply, lfMatFull, LinearMap.toMatrix_apply]
  rw [h, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Pi.smul_apply, Finsupp.single_apply,
    Pi.single_apply]
  by_cases hTS : T = S
  · subst hTS
    simp
  · rw [if_neg (fun h' => hTS (Subtype.ext h'.symm)), if_neg hTS]

end ReciprocityTheory.ChartRestriction.DS
