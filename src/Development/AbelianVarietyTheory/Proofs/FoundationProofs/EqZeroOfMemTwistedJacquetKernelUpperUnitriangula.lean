module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApplyMemTwKerOfNormalizer
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JacquetModuleMaximalParabolicPrincipalSeriesType

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.JacquetKernelEigenvectorEqZeroOfConstCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SphericalVectorNotInBorelJacquetKernel
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SphericalVectorNotInBorelJacquetKernel
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType
open GlobalTheory.DepthZeroJac GlobalTheory.IwahoriInj GlobalTheory.StepData

theorem unipRad_points_eq (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) :
    unipRad k (Equiv.sigmaUnique (Fin n) fun _ => Fin 1) = unipB k (Fin n) := by
  ext g
  rw [mem_unipB, mem_unipRad, mem_parab]
  simp only [blk, Equiv.sigmaUnique_symm_apply, Equiv.sigmaUnique_apply]
  refine and_congr Iff.rfl ⟨fun h i => (h i 0 0).trans (by simp), fun h a i j => ?_⟩
  rw [h a, Subsingleton.elim i j]
  simp

theorem eq_zero_of_fixed_KO_twKer_unipB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → ∀ v ∈ twKer π (unipB k (Fin n)) 1, (∀ g ∈ KO k (Fin n), π g v = v) → v = 0 := by
  intro k _ _ _ _ n V _ _ π hπ v h1 hfix
  rw [← unipRad_points_eq] at h1
  obtain ⟨c, hc0, hc1, hc2⟩ := exists_deep (k := k) 1
  obtain ⟨M, hM⟩ := (eventually_mem_twKer (hc := hc0) hc1 hc2 h1).exists
  refine claim_of_antitone hc1 hc2 hπ _ _ rfl (antitone_expo M) v ?_ hM
  exact mem_fixed.2 fun g hg => hfix g ((sup_le KOne_le_KO inf_le_right) hg)

end GlobalTheory.PsType
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SphericalVectorNotInBorelJacquetKernelStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spherical_vector_not_in_borel_jacquet_kernel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → ∀ v ∈ twKer π (unipB k (Fin n)) 1, (∀ g ∈ KO k (Fin n), π g v = v) → v = 0 := by
  first | exact @GlobalTheory.PsType.eq_zero_of_fixed_KO_twKer_unipB | exact GlobalTheory.PsType.eq_zero_of_fixed_KO_twKer_unipB | (intros; apply GlobalTheory.PsType.eq_zero_of_fixed_KO_twKer_unipB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeConstantFamilyDetCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeConstantFamilyDetCharacter
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

noncomputable section
namespace GlobalTheory.PsType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem valuation_det_of_mem_KO' {n : Type} [Fintype n] [DecidableEq n] {g : GL n k} (hg : g ∈ KO k n) :
    valuation k g.val.det = 1 := by
  obtain ⟨h, rfl⟩ := hg
  have hu : IsUnit (h.val.det) := (Matrix.isUnit_iff_isUnit_det _).1 h.isUnit
  have := (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.1 hu
  change valuation k ((algebraMap 𝒪[k] k).mapMatrix h.val).det = 1
  rw [← RingHom.map_det]
  exact this

private theorem ev_one_local' (x : k) : ev (1 : kˣ →* ℂˣ) x = 1 := by
  unfold ev; split_ifs <;> simp

private theorem minor_last {n : ℕ} (g : GL (Fin (n + 1)) k) : minor g (Fin.last n) = g.val.det := by
  unfold minor Matrix.toSquareBlockProp Matrix.toBlock
  have := Matrix.det_submatrix_equiv_self (Equiv.subtypeUnivEquiv (p := fun i : Fin (n + 1) => i ≤ Fin.last n)
    (fun i => Fin.le_last i)) g.val
  rw [← this]; rfl

theorem const_family (n : ℕ) (χ : kˣ →* ℂˣ) :
    grp (fun _ : Fin n => χ) = (KO k (Fin n) : Set (GL (Fin n) k)) ∧
      ∀ g ∈ KO k (Fin n), theta (fun _ : Fin n => χ) g = (detChar (Fin n) χ g : ℂ) := by
  refine ⟨?_, ?_⟩
  · ext g
    simp only [grp, Set.mem_setOf_eq, SetLike.mem_coe, div_self', and_iff_left_iff_imp]
    intro _ i j _ u _ _
    rfl
  · intro g hg
    cases n with
    | zero =>
      simp [theta, detChar_apply]
      have h0 : Matrix.GeneralLinearGroup.det g = 1 := Units.ext (by simp [Matrix.det_isEmpty])
      rw [h0, map_one, Units.val_one]
    | succ n =>
      unfold theta
      rw [Fin.prod_univ_castSucc]
      have h1 : ∀ i : Fin n, ev (χ / nxt (fun _ : Fin (n+1) => χ) i.castSucc) (minor g i.castSucc) = 1 := by
        intro i
        have : nxt (fun _ : Fin (n+1) => χ) i.castSucc = χ := by
          unfold nxt; rw [dite_eq_left (by simp)]
        rw [this, div_self']; exact ev_one_local' _
      have h2 : nxt (fun _ : Fin (n+1) => χ) (Fin.last n) = 1 := by
        unfold nxt; rw [dite_eq_right (by simp)]
      simp only [h1, Finset.prod_const_one, one_mul, h2, div_one, minor_last]
      have hv := valuation_det_of_mem_KO' hg
      unfold ev
      rw [dite_eq_left hv, detChar_apply]
      congr 2
      ext; simp

theorem const_family_main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (χ : kˣ →* ℂˣ), grp (fun _ : Fin n => χ) = (KO k (Fin n) : Set (GL (Fin n) k)) ∧ ∀ g ∈ KO k (Fin n), theta (fun _ : Fin n => χ) g = (detChar (Fin n) χ g : ℂ) :=
  fun _ _ _ _ _ n χ => const_family n χ

end GlobalTheory.PsType
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeConstantFamilyDetCharacterStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalSeriesType_constant_family_det_character : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (χ : kˣ →* ℂˣ), grp (fun _ : Fin n => χ) = (KO k (Fin n) : Set (GL (Fin n) k)) ∧ ∀ g ∈ KO k (Fin n), theta (fun _ : Fin n => χ) g = (detChar (Fin n) χ g : ℂ) := by
  first | exact @GlobalTheory.PsType.const_family_main | exact GlobalTheory.PsType.const_family_main | (intros; apply GlobalTheory.PsType.const_family_main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.JacquetKernelEigenvectorEqZeroOfConstCharacter
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem eq_zero_of_isEig_const : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (χ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → IsSmoothChar χ → ∀ v ∈ twKer π (unipB k (Fin n)) 1, IsEig π (grp fun _ => χ) (theta fun _ => χ) v → v = 0 := by
  intro k _ _ _ _ n χ V _ _ π hπ hχ v hv he
  obtain ⟨h1, h2⟩ := GlobalTheory.T.principalSeriesType_constant_family_det_character k n χ
  have hs : IsSmoothChar (detChar (Fin n) χ)⁻¹ := by
    have hc : Continuous (Matrix.GeneralLinearGroup.det : GL (Fin n) k → kˣ) :=
      Matrix.GeneralLinearGroup.continuous_det
    have ho : IsOpen ((χ.ker : Set kˣ)) := hχ
    have := ho.preimage hc
    unfold IsSmoothChar
    convert this using 1
    ext g
    simp [detChar, MonoidHom.mem_ker]
  have hk : twKer (GlobalTheory.SmGL.twist π (detChar (Fin n) χ)⁻¹) (unipB k (Fin n)) 1 = twKer π (unipB k (Fin n)) 1 := by
    unfold twKer
    congr 1
    ext w
    refine exists_congr fun u => exists_congr fun x => ?_
    have hd : Matrix.GeneralLinearGroup.det (u : GL (Fin n) k) = 1 := det_eq_one_of_mem_unipRad k u.2
    have : GlobalTheory.SmGL.twist π (detChar (Fin n) χ)⁻¹ (u : GL (Fin n) k) x = π (u : GL (Fin n) k) x := by
      simp [GlobalTheory.SmGL.twist, detChar, hd]
    rw [this]
  refine GlobalTheory.T.spherical_vector_not_in_borel_jacquet_kernel k n V (GlobalTheory.SmGL.twist π (detChar (Fin n) χ)⁻¹) (isSmooth_twist hπ hs) v (hk ▸ hv) ?_
  intro g hg
  have h3 := he g (by rw [h1]; exact hg)
  rw [h2 g hg] at h3
  show (((detChar (Fin n) χ)⁻¹ g : ℂˣ) : ℂ) • π g v = v
  rw [h3, smul_smul]
  simp

end GlobalTheory.PsType
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.JacquetKernelEigenvectorEqZeroOfConstCharacterStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetKernel_eigenvector_eq_zero_of_const_character : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (χ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → IsSmoothChar χ → ∀ v ∈ twKer π (unipB k (Fin n)) 1, IsEig π (grp fun _ => χ) (theta fun _ => χ) v → v = 0 := by
  first | exact @GlobalTheory.PsType.eq_zero_of_isEig_const | exact GlobalTheory.PsType.eq_zero_of_isEig_const | (intros; apply GlobalTheory.PsType.eq_zero_of_isEig_const <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterBlockDiagonal
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterBlockDiagonal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType Matrix

noncomputable section

namespace GlobalTheory.PsType.BlockTheta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ev_mul_char (χ η : kˣ →* ℂˣ) (x : k) : ev (χ * η) x = ev χ x * ev η x := by
  unfold ev
  split_ifs with h
  · simp
  · simp

theorem ev_one_char (x : k) : ev (1 : kˣ →* ℂˣ) x = 1 := by
  unfold ev; split_ifs <;> simp

theorem ev_at_one (χ : kˣ →* ℂˣ) : ev χ (1 : k) = 1 := by
  unfold ev
  rw [dite_eq_left (by simp)]
  have : Units.mk0 (1 : k) one_ne_zero = 1 := by ext; simp
  simp [this]

theorem ev_mul_of_val (χ : kˣ →* ℂˣ) {x y : k} (hx : valuation k x = 1) (hy : valuation k y = 1) :
    ev χ (x * y) = ev χ x * ev χ y := by
  have hxy : valuation k (x * y) = 1 := by rw [map_mul, hx, hy, one_mul]
  unfold ev
  rw [dite_eq_left hxy, dite_eq_left hx, dite_eq_left hy, ← Units.val_mul, ← map_mul]
  congr 3
  ext; simp

theorem ev_of_triv_one (χ : kˣ →* ℂˣ) (h : Triv χ 1) (x : k) : ev χ x = 1 := by
  unfold ev
  split_ifs with hx
  · have hu : χ (Units.mk0 x fun h0 => by simp [h0] at hx) = 1 := by
      refine h _ (by simpa using hx) ?_
      calc valuation k ((Units.mk0 x fun h0 => by simp [h0] at hx : kˣ) - 1 : k)
          ≤ max (valuation k x) (valuation k 1) := by rw [Units.val_mk0]; exact Valuation.map_sub _ _ _
        _ = valuation k 1 := by rw [hx, map_one, max_self]
    simp [hu]
  · rfl

theorem val_det_of_mem_KO {n : Type} [Fintype n] [DecidableEq n] {g : GL n k} (hg : g ∈ KO k n) :
    valuation k g.val.det = 1 := by
  obtain ⟨A, rfl⟩ := hg
  have h1 : ((Matrix.GeneralLinearGroup.map (n := n) (algebraMap 𝒪[k] k)) A).val.det
      = algebraMap 𝒪[k] k A.val.det := by
    simp [RingHom.map_det]
  rw [h1]
  exact (Valuation.integer.integers (valuation k)).one_of_isUnit (Matrix.isUnits_det_units A)

def head {n : ℕ} (ψ : Fin n → kˣ →* ℂˣ) : kˣ →* ℂˣ := if h : 0 < n then ψ ⟨0, h⟩ else 1

theorem prod_ev_nxt : ∀ (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (x : k),
    ∏ m, ev (ψ m / nxt ψ m) x = ev (head ψ) x
  | 0, ψ, x => by simp [head, ev_one_char]
  | n + 1, ψ, x => by
    rw [Fin.prod_univ_succ]
    have h1 : ∀ j : Fin n, nxt ψ j.succ = nxt (fun i => ψ i.succ) j := by
      intro j; unfold nxt
      by_cases h : (j : ℕ) + 1 < n
      · rw [dite_eq_left (by simp [Fin.val_succ]; omega), dite_eq_left h]; congr 1
      · rw [dite_eq_right (by simp [Fin.val_succ]; omega), dite_eq_right h]
    have h2 : nxt ψ 0 = head (fun i : Fin n => ψ i.succ) := by
      unfold nxt head
      by_cases h : 0 < n
      · rw [dite_eq_left (by simp; omega), dite_eq_left h]; congr 1
      · rw [dite_eq_right (by simp; omega), dite_eq_right h]
    simp_rw [h1]
    rw [prod_ev_nxt n, ← h2, ← ev_mul_char, div_mul_cancel]
    simp [head]

variable {r t : ℕ}

theorem castAdd_eq (i : Fin r) : Fin.castAdd t i = stdSum (rfl : r + t = r + t) (Sum.inl i) := by ext; simp
theorem natAdd_eq (j : Fin t) : Fin.natAdd r j = stdSum (rfl : r + t = r + t) (Sum.inr j) := by ext; simp

theorem emb_ll (a : GL (Fin r) k) (b : GL (Fin t) k) (i j : Fin r) :
    (emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)).val (Fin.castAdd t i) (Fin.castAdd t j) = a.val i j := by
  rw [castAdd_eq, castAdd_eq]
  simpa only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply] using
    congrFun (congrFun (val_emb₂ k (stdSum (rfl : r + t = r + t)) (a, b))
      (stdSum (rfl : r + t = r + t) (Sum.inl i))) (stdSum (rfl : r + t = r + t) (Sum.inl j))

theorem emb_lr (a : GL (Fin r) k) (b : GL (Fin t) k) (i : Fin r) (j : Fin t) :
    (emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)).val (Fin.castAdd t i) (Fin.natAdd r j) = 0 := by
  rw [castAdd_eq, natAdd_eq]
  simpa only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply] using
    congrFun (congrFun (val_emb₂ k (stdSum (rfl : r + t = r + t)) (a, b))
      (stdSum (rfl : r + t = r + t) (Sum.inl i))) (stdSum (rfl : r + t = r + t) (Sum.inr j))

theorem emb_rl (a : GL (Fin r) k) (b : GL (Fin t) k) (i : Fin t) (j : Fin r) :
    (emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)).val (Fin.natAdd r i) (Fin.castAdd t j) = 0 := by
  rw [castAdd_eq, natAdd_eq]
  simpa only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply] using
    congrFun (congrFun (val_emb₂ k (stdSum (rfl : r + t = r + t)) (a, b))
      (stdSum (rfl : r + t = r + t) (Sum.inr i))) (stdSum (rfl : r + t = r + t) (Sum.inl j))

theorem emb_rr (a : GL (Fin r) k) (b : GL (Fin t) k) (i j : Fin t) :
    (emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)).val (Fin.natAdd r i) (Fin.natAdd r j) = b.val i j := by
  rw [natAdd_eq, natAdd_eq]
  simpa only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply] using
    congrFun (congrFun (val_emb₂ k (stdSum (rfl : r + t = r + t)) (a, b))
      (stdSum (rfl : r + t = r + t) (Sum.inr i))) (stdSum (rfl : r + t = r + t) (Sum.inr j))

def eqvL (i : Fin r) : {y : Fin r // y ≤ i} ≃ {x : Fin (r + t) // x ≤ Fin.castAdd t i} :=
  Equiv.ofBijective (fun y : {y : Fin r // y ≤ i} => (⟨Fin.castAdd t y.1, by
      have := y.2; simp only [Fin.le_def, Fin.coe_castAdd] at this ⊢; omega⟩ :
        {x : Fin (r + t) // x ≤ Fin.castAdd t i})) (by
    constructor
    · rintro ⟨y, hy⟩ ⟨z, hz⟩ h
      simp only [Subtype.mk.injEq, Fin.ext_iff, Fin.coe_castAdd] at h
      exact Subtype.ext (Fin.ext h)
    · rintro ⟨x, hx⟩
      have hx' : (x : ℕ) ≤ i := by simpa [Fin.le_def] using hx
      exact ⟨⟨⟨x, by omega⟩, by simp [Fin.le_def]; omega⟩, by ext; simp⟩)

theorem eqvL_val (i : Fin r) (y : {y : Fin r // y ≤ i}) : ((eqvL (t := t) i y) : Fin (r + t)) = Fin.castAdd t y.1 := rfl

def eqvR (j : Fin t) : Fin r ⊕ {y : Fin t // y ≤ j} ≃ {x : Fin (r + t) // x ≤ Fin.natAdd r j} :=
  Equiv.ofBijective (Sum.elim (fun i : Fin r => (⟨Fin.castAdd t i, by
        simp only [Fin.le_def, Fin.coe_castAdd, Fin.coe_natAdd]; omega⟩ : {x : Fin (r + t) // x ≤ Fin.natAdd r j}))
      (fun y : {y : Fin t // y ≤ j} => (⟨Fin.natAdd r y.1, by
        have := y.2; simp only [Fin.le_def, Fin.coe_natAdd] at this ⊢; omega⟩ : {x : Fin (r + t) // x ≤ Fin.natAdd r j}))) (by
    constructor
    · intro u v h
      rcases u with y | y <;> rcases v with z | z <;>
        simp only [Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq, Fin.ext_iff, Fin.coe_castAdd,
          Fin.coe_natAdd] at h
      · exact congrArg Sum.inl (Fin.ext h)
      · have := y.2; omega
      · have := z.2; omega
      · exact congrArg Sum.inr (Subtype.ext (Fin.ext (by omega)))
    · rintro ⟨x, hx⟩
      have hx' : (x : ℕ) ≤ r + j := by simpa [Fin.le_def] using hx
      by_cases h : (x : ℕ) < r
      · exact ⟨Sum.inl ⟨x, h⟩, by ext; simp⟩
      · exact ⟨Sum.inr ⟨⟨x - r, by omega⟩, by simp [Fin.le_def]; omega⟩, by ext; simp; omega⟩)

theorem eqvR_inl (j : Fin t) (i : Fin r) : ((eqvR j (Sum.inl i)) : Fin (r + t)) = Fin.castAdd t i := rfl
theorem eqvR_inr (j : Fin t) (y : {y : Fin t // y ≤ j}) : ((eqvR (r := r) j (Sum.inr y)) : Fin (r + t)) = Fin.natAdd r y.1 := rfl

theorem minor_castAdd (a : GL (Fin r) k) (b : GL (Fin t) k) (i : Fin r) :
    minor (emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)) (Fin.castAdd t i) = minor a i := by
  unfold minor
  rw [← Matrix.det_submatrix_equiv_self (eqvL i)]
  congr 1
  ext y z
  simp only [toSquareBlockProp, toBlock, submatrix_apply, eqvL_val, emb_ll]

theorem minor_natAdd (a : GL (Fin r) k) (b : GL (Fin t) k) (j : Fin t) :
    minor (emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)) (Fin.natAdd r j) = a.val.det * minor b j := by
  unfold minor
  rw [← Matrix.det_submatrix_equiv_self (eqvR j)]
  rw [show ((emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)).val.toSquareBlockProp fun x => x ≤ Fin.natAdd r j).submatrix (eqvR j) (eqvR j)
      = fromBlocks a.val 0 0 (b.val.toSquareBlockProp fun x => x ≤ j) by
    ext (y | y) (z | z) <;> simp only [toSquareBlockProp, toBlock, submatrix_apply, eqvR_inl, eqvR_inr,
      emb_ll, emb_lr, emb_rl, emb_rr, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, Matrix.zero_apply]]
  rw [det_fromBlocks_zero₂₁]

theorem minor_last {r : ℕ} (a : GL (Fin (r + 1)) k) : minor a (Fin.last r) = a.val.det := by
  unfold minor
  rw [← Matrix.det_submatrix_equiv_self (Equiv.subtypeUnivEquiv (fun x => Fin.le_last x)).symm]
  congr 1

theorem nxt_natAdd (ψ : Fin (r + t) → kˣ →* ℂˣ) (j : Fin t) :
    nxt ψ (Fin.natAdd r j) = nxt (fun i => ψ (Fin.natAdd r i)) j := by
  unfold nxt
  by_cases h : (j : ℕ) + 1 < t
  · rw [dite_eq_left (by simp; omega), dite_eq_left h]; congr 1
  · rw [dite_eq_right (by simp; omega), dite_eq_right h]

theorem nxt_castAdd_castSucc {r : ℕ} (ψ : Fin (r + 1 + t) → kˣ →* ℂˣ) (i : Fin r) :
    nxt ψ (Fin.castAdd t i.castSucc) = nxt (fun i => ψ (Fin.castAdd t i)) i.castSucc := by
  unfold nxt
  rw [dite_eq_left (by simp; omega), dite_eq_left (by simp)]
  congr 1

theorem nxt_castAdd_last {r : ℕ} (ψ : Fin (r + 1 + t) → kˣ →* ℂˣ) :
    nxt ψ (Fin.castAdd t (Fin.last r)) = head (fun j : Fin t => ψ (Fin.natAdd (r + 1) j)) := by
  unfold nxt head
  by_cases h : 0 < t
  · rw [dite_eq_left (by simp; omega), dite_eq_left h]; congr 1
  · rw [dite_eq_right (by simp; omega), dite_eq_right h]

theorem nxt_last_one {r : ℕ} (φ : Fin (r + 1) → kˣ →* ℂˣ) : nxt φ (Fin.last r) = 1 := by
  unfold nxt; rw [dite_eq_right (by simp)]

theorem first_part : ∀ (r t : ℕ) (ψ : Fin (r + t) → kˣ →* ℂˣ) (a : GL (Fin r) k),
    (∏ i : Fin r, ev (ψ (Fin.castAdd t i) / nxt ψ (Fin.castAdd t i)) (minor a i)) *
      ev (head fun j : Fin t => ψ (Fin.natAdd r j)) a.val.det = theta (fun i => ψ (Fin.castAdd t i)) a
  | 0, t, ψ, a => by simp [theta, Matrix.det_isEmpty, ev_at_one]
  | r + 1, t, ψ, a => by
    unfold theta
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, mul_assoc, minor_last, nxt_castAdd_last,
      nxt_last_one, ← ev_mul_char, div_mul_cancel, div_one]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [nxt_castAdd_castSucc]

end GlobalTheory.PsType.BlockTheta


open GlobalTheory.PsType.BlockTheta in
theorem GlobalTheory.PsType.theta_emb₂_std : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (ψ : Fin (r + t) → kˣ →* ℂˣ), Ordered ψ → ∀ a ∈ grp (fun i => ψ (Fin.castAdd t i)), ∀ b ∈ grp (fun i => ψ (Fin.natAdd r i)), theta ψ (emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)) = theta (fun i => ψ (Fin.castAdd t i)) a * theta (fun i => ψ (Fin.natAdd r i)) b := by
  intro k _ _ _ _ r t ψ hord a ha b hb
  have hord₂ : Ordered (fun i => ψ (Fin.natAdd r i)) := by
    intro i a' b' j h1 h2 h3 x hx
    exact hord (Fin.natAdd r i) (Fin.natAdd r a') (Fin.natAdd r b') (Fin.natAdd r j) (by rw [Fin.le_def] at h1 ⊢; simp only [Fin.coe_natAdd]; omega) (by rw [Fin.le_def] at h2 ⊢; simp only [Fin.coe_natAdd]; omega)
      (by rw [Fin.le_def] at h3 ⊢; simp only [Fin.coe_natAdd]; omega) x hx
  have hda : valuation k a.val.det = 1 := val_det_of_mem_KO ha.1
  have hsplit : theta ψ (emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)) =
      (∏ i : Fin r, ev (ψ (Fin.castAdd t i) / nxt ψ (Fin.castAdd t i)) (minor a i)) *
        ((∏ j : Fin t, ev ((fun i => ψ (Fin.natAdd r i)) j / nxt (fun i => ψ (Fin.natAdd r i)) j) a.val.det) *
          theta (fun i => ψ (Fin.natAdd r i)) b) := by
    unfold theta
    rw [Fin.prod_univ_add]
    congr 1
    · exact Finset.prod_congr rfl fun i _ => by rw [minor_castAdd]
    · rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [minor_natAdd, nxt_natAdd]
      by_cases hT : Triv ((fun i => ψ (Fin.natAdd r i)) j / nxt (fun i => ψ (Fin.natAdd r i)) j) 1
      · rw [GlobalTheory.PsType.BlockTheta.ev_of_triv_one _ hT, GlobalTheory.PsType.BlockTheta.ev_of_triv_one _ hT, GlobalTheory.PsType.BlockTheta.ev_of_triv_one _ hT, one_mul]
      · exact ev_mul_of_val _ hda ((GlobalTheory.T.leadingPrincipalMinor_mul_mod_conductor k t _ hord₂ j hT).1 b hb)
  rw [hsplit, prod_ev_nxt, ← mul_assoc, first_part]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterBlockDiagonalStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalSeriesTypeCharacter_blockDiagonal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (ψ : Fin (r + t) → kˣ →* ℂˣ), Ordered ψ → ∀ a ∈ grp (fun i => ψ (Fin.castAdd t i)), ∀ b ∈ grp (fun i => ψ (Fin.natAdd r i)), theta ψ (emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)) = theta (fun i => ψ (Fin.castAdd t i)) a * theta (fun i => ψ (Fin.natAdd r i)) b := by
  first | exact @GlobalTheory.PsType.theta_emb₂_std | exact GlobalTheory.PsType.theta_emb₂_std | (intros; apply GlobalTheory.PsType.theta_emb₂_std <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwistedJacquetSurvivalProductOfTwoGroups
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwistedJacquetSurvivalProductOfTwoGroups
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem eq_zero_of_mem_sup_twKer_prod : ∀ (G₁ G₂ V : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (G₁ × G₂) V), IsSmooth ρ → ∀ (U₁ : Subgroup G₁) (U₂ : Subgroup G₂) (J₁ : Set G₁) (J₂ : Set G₂) (θ₁ : G₁ → ℂ) (θ₂ : G₂ → ℂ), (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G₁ W), IsSmooth σ → ∀ w ∈ twKer σ U₁ 1, IsEig σ J₁ θ₁ w → w = 0) → (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G₂ W), IsSmooth σ → ∀ w ∈ twKer σ U₂ 1, IsEig σ J₂ θ₂ w → w = 0) → ∀ v ∈ twKer (ρ.comp (MonoidHom.inl G₁ G₂)) U₁ 1 ⊔ twKer (ρ.comp (MonoidHom.inr G₁ G₂)) U₂ 1, IsEig (ρ.comp (MonoidHom.inl G₁ G₂)) J₁ θ₁ v → IsEig (ρ.comp (MonoidHom.inr G₁ G₂)) J₂ θ₂ v → v = 0 := by
  intro G₁ G₂ V _ _ _ _ _ _ _ _ ρ hρ U₁ U₂ J₁ J₂ θ₁ θ₂ h₁ h₂ v hv e₁ e₂
  have s₁ : IsSmooth (ρ.comp (MonoidHom.inl G₁ G₂)) := fun w =>
    (hρ w).preimage (f := fun g : G₁ => ((g, 1) : G₁ × G₂)) (by fun_prop)
  have s₂ : IsSmooth (ρ.comp (MonoidHom.inr G₁ G₂)) := fun w =>
    (hρ w).preimage (f := fun g : G₂ => ((1, g) : G₁ × G₂)) (by fun_prop)
  set ρ₁ : Representation ℂ G₁ V := ρ.comp (MonoidHom.inl G₁ G₂) with hρ₁
  set ρ₂ : Representation ℂ G₂ V := ρ.comp (MonoidHom.inr G₁ G₂) with hρ₂
  have comm : ∀ (a : G₁) (b : G₂) (w : V), ρ₁ a (ρ₂ b w) = ρ₂ b (ρ₁ a w) := by
    intro a b w
    change ρ (a, 1) (ρ (1, b) w) = ρ (1, b) (ρ (a, 1) w)
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    simp
  set A : Submodule ℂ V := twKer ρ₂ U₂ 1 with hA
  have hst : ∀ g : G₁, A ≤ A.comap (ρ₁ g) := by
    intro g
    refine Submodule.span_le.2 ?_
    rintro w ⟨n, x, rfl⟩
    refine Submodule.subset_span ⟨n, ρ₁ g x, ?_⟩
    rw [map_sub, map_smul, comm]
  let σ : Representation ℂ G₁ (V ⧸ A) := Representation.quotient ρ₁ A hst
  have hσ : ∀ g x, σ g (A.mkQ x) = A.mkQ (ρ₁ g x) := fun g x => rfl
  have sσ : IsSmooth σ := by
    intro w
    obtain ⟨x, rfl⟩ := A.mkQ_surjective w
    let S : Subgroup G₁ :=
      { carrier := {g | σ g (A.mkQ x) = A.mkQ x}
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          rw [map_mul, Module.End.mul_apply, hb, ha]
        one_mem' := by simp
        inv_mem' := by
          intro a ha
          simp only [Set.mem_setOf_eq] at ha ⊢
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul]
          simp }
    have : (S : Set G₁) ∈ nhds (1 : G₁) := by
      refine Filter.mem_of_superset ((s₁ x).mem_nhds (by simp)) ?_
      intro g hg
      change σ g (A.mkQ x) = A.mkQ x
      rw [hσ, show ρ₁ g x = x from hg]
    exact S.isOpen_of_mem_nhds this
  have hmap : twKer ρ₁ U₁ 1 ≤ (twKer σ U₁ 1).comap A.mkQ := by
    refine Submodule.span_le.2 ?_
    rintro w ⟨n, x, rfl⟩
    refine Submodule.subset_span ⟨n, A.mkQ x, ?_⟩
    rw [map_sub, map_smul, hσ]
  have hA0 : A ≤ (twKer σ U₁ 1).comap A.mkQ := by
    intro x hx
    have : A.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero A).2 hx
    rw [Submodule.mem_comap, this]
    exact zero_mem _
  have hv' : A.mkQ v ∈ twKer σ U₁ 1 := sup_le hmap hA0 hv
  have hz : A.mkQ v = 0 := h₁ _ σ sσ _ hv' (by
    intro h hh
    rw [hσ, e₁ h hh, map_smul])
  exact h₂ V ρ₂ s₂ v ((Submodule.Quotient.mk_eq_zero A).1 hz) e₂

end GlobalTheory.PsType
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwistedJacquetSurvivalProductOfTwoGroupsStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedJacquet_survival_product_of_two_groups : ∀ (G₁ G₂ V : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (G₁ × G₂) V), IsSmooth ρ → ∀ (U₁ : Subgroup G₁) (U₂ : Subgroup G₂) (J₁ : Set G₁) (J₂ : Set G₂) (θ₁ : G₁ → ℂ) (θ₂ : G₂ → ℂ), (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G₁ W), IsSmooth σ → ∀ w ∈ twKer σ U₁ 1, IsEig σ J₁ θ₁ w → w = 0) → (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G₂ W), IsSmooth σ → ∀ w ∈ twKer σ U₂ 1, IsEig σ J₂ θ₂ w → w = 0) → ∀ v ∈ twKer (ρ.comp (MonoidHom.inl G₁ G₂)) U₁ 1 ⊔ twKer (ρ.comp (MonoidHom.inr G₁ G₂)) U₂ 1, IsEig (ρ.comp (MonoidHom.inl G₁ G₂)) J₁ θ₁ v → IsEig (ρ.comp (MonoidHom.inr G₁ G₂)) J₂ θ₂ v → v = 0 := by
  first | exact @GlobalTheory.PsType.eq_zero_of_mem_sup_twKer_prod | exact GlobalTheory.PsType.eq_zero_of_mem_sup_twKer_prod | (intros; apply GlobalTheory.PsType.eq_zero_of_mem_sup_twKer_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BlockDiagonalPrincipalSeriesCongruenceSubgroupSp
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BlockDiagonalPrincipalSeriesCongruenceSubgroupSp
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType Matrix

noncomputable section
namespace GlobalTheory.PsType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem triv_zero' (χ : kˣ →* ℂˣ) : Triv χ (0 : k) := by
  intro u _ h
  rw [map_zero] at h
  have h0 : valuation k ((u : k) - 1) = 0 := le_antisymm h zero_le'
  rw [(valuation k).zero_iff, sub_eq_zero] at h0
  have : u = 1 := Units.ext h0
  rw [this, map_one]

section Blocks

variable {r t : ℕ}

theorem castAdd_eq_stdSum (i : Fin r) : Fin.castAdd t i = stdSum (rfl : r + t = r + t) (Sum.inl i) := by
  ext; simp

theorem natAdd_eq_stdSum (j : Fin t) : Fin.natAdd r j = stdSum (rfl : r + t = r + t) (Sum.inr j) := by
  ext; simp

theorem emb₂_std_apply (a : GL (Fin r) k) (b : GL (Fin t) k) (x y : Fin r ⊕ Fin t) :
    (emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)).val (stdSum rfl x) (stdSum rfl y) =
      fromBlocks a.val 0 0 b.val x y := by
  exact (congrFun (congrFun (val_emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)) _) _).trans (by
    simp [Matrix.reindex_apply, Matrix.submatrix_apply])

theorem emb₂_std_inv (a : GL (Fin r) k) (b : GL (Fin t) k) :
    (emb₂ k (stdSum (rfl : r + t = r + t)) (a, b))⁻¹ = emb₂ k (stdSum (rfl : r + t = r + t)) (a⁻¹, b⁻¹) := by
  rw [← map_inv]; rfl

theorem emb₂_mem_KO_iff (a : GL (Fin r) k) (b : GL (Fin t) k) :
    emb₂ k (stdSum (rfl : r + t = r + t)) (a, b) ∈ KO k (Fin (r + t)) ↔
      a ∈ KO k (Fin r) ∧ b ∈ KO k (Fin t) := by
  rw [GlobalTheory.SplitFlip.mem_KO_iff, GlobalTheory.SplitFlip.mem_KO_iff, GlobalTheory.SplitFlip.mem_KO_iff, emb₂_std_inv]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun i j => ?_, fun i j => ?_⟩, ⟨fun i j => ?_, fun i j => ?_⟩⟩
    · have := h1 (stdSum rfl (.inl i)) (stdSum rfl (.inl j))
      rwa [emb₂_std_apply, fromBlocks_apply₁₁] at this
    · have := h2 (stdSum rfl (.inl i)) (stdSum rfl (.inl j))
      rwa [emb₂_std_apply, fromBlocks_apply₁₁] at this
    · have := h1 (stdSum rfl (.inr i)) (stdSum rfl (.inr j))
      rwa [emb₂_std_apply, fromBlocks_apply₂₂] at this
    · have := h2 (stdSum rfl (.inr i)) (stdSum rfl (.inr j))
      rwa [emb₂_std_apply, fromBlocks_apply₂₂] at this
  · rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩
    refine ⟨fun p q => ?_, fun p q => ?_⟩
    · obtain ⟨x, rfl⟩ := (stdSum (rfl : r + t = r + t)).surjective p
      obtain ⟨y, rfl⟩ := (stdSum (rfl : r + t = r + t)).surjective q
      rw [emb₂_std_apply]
      rcases x with x | x <;> rcases y with y | y
      · rw [fromBlocks_apply₁₁]; exact a1 x y
      · rw [fromBlocks_apply₁₂, Matrix.zero_apply]; exact zero_mem _
      · rw [fromBlocks_apply₂₁, Matrix.zero_apply]; exact zero_mem _
      · rw [fromBlocks_apply₂₂]; exact b1 x y
    · obtain ⟨x, rfl⟩ := (stdSum (rfl : r + t = r + t)).surjective p
      obtain ⟨y, rfl⟩ := (stdSum (rfl : r + t = r + t)).surjective q
      rw [emb₂_std_apply]
      rcases x with x | x <;> rcases y with y | y
      · rw [fromBlocks_apply₁₁]; exact a2 x y
      · rw [fromBlocks_apply₁₂, Matrix.zero_apply]; exact zero_mem _
      · rw [fromBlocks_apply₂₁, Matrix.zero_apply]; exact zero_mem _
      · rw [fromBlocks_apply₂₂]; exact b2 x y

theorem ordered_castAdd {ψ : Fin (r + t) → kˣ →* ℂˣ} (hψ : Ordered ψ) :
    Ordered (fun i : Fin r => ψ (Fin.castAdd t i)) := by
  intro i a b j hia hab hbj x hx
  exact hψ (Fin.castAdd t i) (Fin.castAdd t a) (Fin.castAdd t b) (Fin.castAdd t j)
    (Fin.le_def.2 (Fin.le_def.1 hia)) (Fin.le_def.2 (Fin.le_def.1 hab)) (Fin.le_def.2 (Fin.le_def.1 hbj)) x hx

theorem ordered_natAdd {ψ : Fin (r + t) → kˣ →* ℂˣ} (hψ : Ordered ψ) :
    Ordered (fun i : Fin t => ψ (Fin.natAdd r i)) := by
  intro i a b j hia hab hbj x hx
  exact hψ (Fin.natAdd r i) (Fin.natAdd r a) (Fin.natAdd r b) (Fin.natAdd r j)
    ((Fin.natAdd_le_natAdd_iff r).2 hia) ((Fin.natAdd_le_natAdd_iff r).2 hab) ((Fin.natAdd_le_natAdd_iff r).2 hbj) x hx

theorem emb₂_mem_grp_iff (ψ : Fin (r + t) → kˣ →* ℂˣ) (a : GL (Fin r) k) (b : GL (Fin t) k) :
    emb₂ k (stdSum (rfl : r + t = r + t)) (a, b) ∈ grp ψ ↔
      a ∈ grp (fun i => ψ (Fin.castAdd t i)) ∧ b ∈ grp (fun i => ψ (Fin.natAdd r i)) := by
  unfold grp
  simp only [Set.mem_setOf_eq]
  rw [emb₂_mem_KO_iff]
  constructor
  · rintro ⟨⟨ha, hb⟩, h⟩
    refine ⟨⟨ha, fun i j hij => ?_⟩, ⟨hb, fun i j hij => ?_⟩⟩
    · have := h (Fin.castAdd t i) (Fin.castAdd t j) (Fin.lt_def.2 (Fin.lt_def.1 hij))
      rwa [castAdd_eq_stdSum i, castAdd_eq_stdSum j, emb₂_std_apply, fromBlocks_apply₁₁] at this
    · have := h (Fin.natAdd r i) (Fin.natAdd r j) ((Fin.natAdd_lt_natAdd_iff r).2 hij)
      rwa [natAdd_eq_stdSum i, natAdd_eq_stdSum j, emb₂_std_apply, fromBlocks_apply₂₂] at this
  · rintro ⟨⟨ha, ha'⟩, ⟨hb, hb'⟩⟩
    refine ⟨⟨ha, hb⟩, fun p q hpq => ?_⟩
    obtain ⟨x, rfl⟩ := (stdSum (rfl : r + t = r + t)).surjective p
    obtain ⟨y, rfl⟩ := (stdSum (rfl : r + t = r + t)).surjective q
    rw [emb₂_std_apply]
    rcases x with x | x <;> rcases y with y | y
    · rw [fromBlocks_apply₁₁]
      have hxy : x < y := by
        rw [← castAdd_eq_stdSum, ← castAdd_eq_stdSum] at hpq
        exact Fin.lt_def.2 (Fin.lt_def.1 hpq)
      have := ha' x y hxy
      rwa [castAdd_eq_stdSum x, castAdd_eq_stdSum y] at this
    · rw [fromBlocks_apply₁₂, Matrix.zero_apply]; exact triv_zero' _
    · exfalso
      have := Fin.lt_def.1 hpq
      rw [stdSum_inr, stdSum_inl] at this
      omega
    · rw [fromBlocks_apply₂₂]
      have hxy : x < y := by
        rw [← natAdd_eq_stdSum, ← natAdd_eq_stdSum] at hpq
        exact (Fin.natAdd_lt_natAdd_iff r).1 hpq
      have := hb' x y hxy
      rwa [natAdd_eq_stdSum x, natAdd_eq_stdSum y] at this

end Blocks

theorem block_diag_mem_grp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (ψ : Fin (r + t) → kˣ →* ℂˣ), Ordered ψ → Cut ψ r → Ordered (fun i => ψ (Fin.castAdd t i)) ∧ Ordered (fun i => ψ (Fin.natAdd r i)) ∧ ∀ (a : GL (Fin r) k) (b : GL (Fin t) k), emb₂ k (stdSum (rfl : r + t = r + t)) (a, b) ∈ grp ψ ↔ a ∈ grp (fun i => ψ (Fin.castAdd t i)) ∧ b ∈ grp (fun i => ψ (Fin.natAdd r i)) :=
  fun _ _ _ _ _ _ _ ψ hψ _ => ⟨ordered_castAdd hψ, ordered_natAdd hψ, emb₂_mem_grp_iff ψ⟩

end GlobalTheory.PsType
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BlockDiagonalPrincipalSeriesCongruenceSubgroupSpStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockDiagonal_principalSeriesCongruenceSubgroup_split : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (ψ : Fin (r + t) → kˣ →* ℂˣ), Ordered ψ → Cut ψ r → Ordered (fun i => ψ (Fin.castAdd t i)) ∧ Ordered (fun i => ψ (Fin.natAdd r i)) ∧ ∀ (a : GL (Fin r) k) (b : GL (Fin t) k), emb₂ k (stdSum (rfl : r + t = r + t)) (a, b) ∈ grp ψ ↔ a ∈ grp (fun i => ψ (Fin.castAdd t i)) ∧ b ∈ grp (fun i => ψ (Fin.natAdd r i)) := by
  first | exact @GlobalTheory.PsType.block_diag_mem_grp | exact GlobalTheory.PsType.block_diag_mem_grp | (intros; apply GlobalTheory.PsType.block_diag_mem_grp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrderedCharacterFamilySplitsOrConstantOnUnits
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrderedCharacterFamilySplitsOrConstantOnUnits
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem apply_eq_one_of_triv_one_unit {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {χ : kˣ →* ℂˣ} (h : Triv χ 1) (u : kˣ) (hu : valuation k (u : k) = 1) : χ u = 1 := by
  apply h u hu
  calc valuation k ((u : k) - 1) ≤ max (valuation k (u : k)) (valuation k 1) := Valuation.map_sub _ _ _
    _ = valuation k 1 := by simp [hu]

theorem cut_or_const : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → (∃ r : ℕ, 0 < r ∧ r < n ∧ Cut ψ r) ∨ ∃ χ : kˣ →* ℂˣ, ((∀ i, IsSmoothChar (ψ i)) → IsSmoothChar χ) ∧ Agree ψ (fun _ => χ) := by
  intro k _ _ _ _ n ψ hord
  by_cases hc : ∃ m : ℕ, ∃ h : m + 1 < n, ¬ Triv (ψ ⟨m, by omega⟩ / ψ ⟨m + 1, h⟩) 1
  · obtain ⟨m, hm, hnt⟩ := hc
    refine Or.inl ⟨m + 1, by omega, hm, ?_⟩
    intro i j hi hj htr
    have h1 : i ≤ (⟨m, by omega⟩ : Fin n) := by rw [Fin.le_def]; simp; omega
    have h2 : (⟨m, by omega⟩ : Fin n) ≤ ⟨m + 1, hm⟩ := by rw [Fin.le_def]; simp
    have h3 : (⟨m + 1, hm⟩ : Fin n) ≤ j := by rw [Fin.le_def]; simp; omega
    exact hnt (hord i _ _ j h1 h2 h3 1 htr)
  · push_neg at hc
    right
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      refine ⟨1, fun _ => ?_, fun i => i.elim0⟩
      show IsOpen ((1 : kˣ →* ℂˣ).ker : Set kˣ)
      simp
    · refine ⟨ψ ⟨0, hn⟩, fun hs => hs _, ?_⟩
      have key : ∀ m (hm : m < n) (u : kˣ), valuation k (u : k) = 1 → ψ ⟨m, hm⟩ u = ψ ⟨0, hn⟩ u := by
        intro m
        induction m with
        | zero => intro _ _ _; rfl
        | succ m ih =>
          intro hm u hu
          have h1 := apply_eq_one_of_triv_one_unit (hc m hm) u hu
          rw [MonoidHom.div_apply, div_eq_one] at h1
          rw [← h1, ih (by omega) u hu]
      intro i u hu
      exact key i.1 i.2 u hu

end GlobalTheory.PsType
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrderedCharacterFamilySplitsOrConstantOnUnitsStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orderedCharacterFamily_splits_or_constant_on_units : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → (∃ r : ℕ, 0 < r ∧ r < n ∧ Cut ψ r) ∨ ∃ χ : kˣ →* ℂˣ, ((∀ i, IsSmoothChar (ψ i)) → IsSmoothChar χ) ∧ Agree ψ (fun _ => χ) := by
  first | exact @GlobalTheory.PsType.cut_or_const | exact GlobalTheory.PsType.cut_or_const | (intros; apply GlobalTheory.PsType.cut_or_const <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwistedJacquetKernelTwoBlockUnipotentLeStages
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwistedJacquetKernelTwoBlockUnipotentLeStages
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem twKer_unipB_le_of_stages : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (r + t)) k) V) (P : Submodule ℂ V), twKer π (unipRad k (two (stdSum (rfl : r + t = r + t)))) 1 ≤ P → (∀ u ∈ unipB k (Fin r), ∀ w, π (emb₂ k (stdSum (rfl : r + t = r + t)) (u, 1)) w - w ∈ P) → (∀ u ∈ unipB k (Fin t), ∀ w, π (emb₂ k (stdSum (rfl : r + t = r + t)) (1, u)) w - w ∈ P) → twKer π (unipB k (Fin (r + t))) 1 ≤ P := by
  intro k _ _ _ _ r t V _ _ π P h0 h1 h2
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨u, hu⟩, w, rfl⟩
  set e := stdSum (rfl : r + t = r + t) with he
  obtain ⟨hl, hd⟩ := (mem_unipB k).1 hu
  have hp : u ∈ parab k (two e) := (mem_parab_two k).2 fun j i => hl _ _ (by
    rw [Fin.lt_def, he, stdSum_inl, stdSum_inr]; omega)
  obtain ⟨y, hy, hdec⟩ := exists_levi_mul_unip k (two e) ⟨u, hp⟩
  set a : GL (Fin r) k := leviProj k (two e) ⟨u, hp⟩ false with ha
  set b : GL (Fin t) k := leviProj k (two e) ⟨u, hp⟩ true with hb
  have hau : a ∈ unipB k (Fin r) := (mem_unipB k).2 ⟨fun i j hij => hl (e (.inl i)) (e (.inl j)) (by
    rw [Fin.lt_def, he, stdSum_inl, stdSum_inl]; exact hij), fun i => hd (e (.inl i))⟩
  have hbu : b ∈ unipB k (Fin t) := (mem_unipB k).2 ⟨fun i j hij => hl (e (.inr i)) (e (.inr j)) (by
    rw [Fin.lt_def, he, stdSum_inr, stdSum_inr]; exact Nat.add_lt_add_left hij r), fun i => hd (e (.inr i))⟩
  have hlev : leviEmb k (two e) (leviProj k (two e) ⟨u, hp⟩) = emb₂ k e (a, 1) * emb₂ k e (1, b) := by
    rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
    show _ = leviEmb k (two e) (leviTwo k _ _ (a, b))
    congr 1
    funext x
    cases x <;> rfl
  have hdec' : u = emb₂ k e (a, 1) * emb₂ k e (1, b) * y := by rw [← hlev]; exact hdec
  have h3 : π y w - w ∈ P := h0 (Submodule.subset_span ⟨⟨y, hy⟩, w, by simp⟩)
  have h4 := P.add_mem (P.add_mem (h1 a hau (π (emb₂ k e (1, b)) (π y w))) (h2 b hbu (π y w))) h3
  have h5 : π u w - w ∈ P := by
    rw [hdec', map_mul, map_mul]
    simpa using h4
  simpa using h5

end GlobalTheory.PsType
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwistedJacquetKernelTwoBlockUnipotentLeStagesStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedJacquetKernel_twoBlock_unipotent_le_stages : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (r + t)) k) V) (P : Submodule ℂ V), twKer π (unipRad k (two (stdSum (rfl : r + t = r + t)))) 1 ≤ P → (∀ u ∈ unipB k (Fin r), ∀ w, π (emb₂ k (stdSum (rfl : r + t = r + t)) (u, 1)) w - w ∈ P) → (∀ u ∈ unipB k (Fin t), ∀ w, π (emb₂ k (stdSum (rfl : r + t = r + t)) (1, u)) w - w ∈ P) → twKer π (unipB k (Fin (r + t))) 1 ≤ P := by
  first | exact @GlobalTheory.PsType.twKer_unipB_le_of_stages | exact GlobalTheory.PsType.twKer_unipB_le_of_stages | (intros; apply GlobalTheory.PsType.twKer_unipB_le_of_stages <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeDataDependOnlyOnUnits
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeDataDependOnlyOnUnits
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem agree_div_apply {ψ ω : Fin n → kˣ →* ℂˣ} (h : Agree ψ ω) (i j : Fin n) (u : kˣ)
    (hu : valuation k (u : k) = 1) : (ψ i / ψ j) u = (ω i / ω j) u := by
  simp only [MonoidHom.div_apply, h i u hu, h j u hu]

theorem agree_triv_iff {ψ ω : Fin n → kˣ →* ℂˣ} (h : Agree ψ ω) (i j : Fin n) (x : k) :
    Triv (ψ i / ψ j) x ↔ Triv (ω i / ω j) x := by
  constructor
  · intro H u hu hx
    rw [← agree_div_apply h i j u hu]
    exact H u hu hx
  · intro H u hu hx
    rw [agree_div_apply h i j u hu]
    exact H u hu hx

theorem agree_nxt_apply {ψ ω : Fin n → kˣ →* ℂˣ} (h : Agree ψ ω) (m : Fin n) (u : kˣ)
    (hu : valuation k (u : k) = 1) : nxt ψ m u = nxt ω m u := by
  unfold nxt
  split_ifs
  · exact h _ u hu
  · rfl

theorem agree_ev {ψ ω : Fin n → kˣ →* ℂˣ} (h : Agree ψ ω) (m : Fin n) (x : k) :
    ev (ψ m / nxt ψ m) x = ev (ω m / nxt ω m) x := by
  unfold ev
  split_ifs with hx
  · have hv : valuation k ((Units.mk0 x fun h0 => by simp [h0] at hx : kˣ) : k) = 1 := by
      simpa using hx
    rw [MonoidHom.div_apply, MonoidHom.div_apply, h m _ hv, agree_nxt_apply h m _ hv]
  · rfl

theorem agree_main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (ψ ω : Fin n → kˣ →* ℂˣ), Agree ψ ω → grp ψ = grp ω ∧ theta ψ = theta ω ∧ (Ordered ψ → Ordered ω) ∧
      ∀ r, Cut ψ r → Cut ω r := by
  intro k _ _ _ _ n ψ ω h
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext g
    simp only [grp, Set.mem_setOf_eq, agree_triv_iff h]
  · funext g
    unfold theta
    exact Finset.prod_congr rfl fun m _ => agree_ev h m _
  · intro H i a b j hi ha hb x hT
    rw [← agree_triv_iff h]
    exact H i a b j hi ha hb x ((agree_triv_iff h i j x).2 hT)
  · intro r H i j hi hj hT
    exact H i j hi hj ((agree_triv_iff h i j 1).2 hT)

end GlobalTheory.PsType
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeDataDependOnlyOnUnitsStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalSeriesType_data_depend_only_on_units : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ ω : Fin n → kˣ →* ℂˣ), Agree ψ ω → grp ψ = grp ω ∧ theta ψ = theta ω ∧ (Ordered ψ → Ordered ω) ∧ ∀ r, Cut ψ r → Cut ω r := by
  first | exact @GlobalTheory.PsType.agree_main | exact GlobalTheory.PsType.agree_main | (intros; apply GlobalTheory.PsType.agree_main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqZeroOfMemTwistedJacquetKernelUpperUnitriangula
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem eq_zero_of_mem_twKer_unipB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → (∀ i, IsSmoothChar (ψ i)) → Ordered ψ → ∀ v ∈ twKer π (unipB k (Fin n)) 1, IsEig π (grp ψ) (theta ψ) v → v = 0 := by
  intro k _ _ _ _ n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ψ V _ _ π hπ hψ hord v hv heig
  rcases GlobalTheory.T.orderedCharacterFamily_splits_or_constant_on_units k n ψ hord with ⟨r, hr0, hrn, hcut⟩ | ⟨χ, hχ, hag⟩
  swap
  · obtain ⟨hg, hth, -, -⟩ := GlobalTheory.T.principalSeriesType_data_depend_only_on_units k n ψ _ hag
    rw [hg, hth] at heig
    exact GlobalTheory.T.jacquetKernel_eigenvector_eq_zero_of_const_character k n χ V π hπ (hχ hψ) v hv heig
  obtain ⟨t, rfl⟩ : ∃ t, n = r + t := ⟨n - r, by omega⟩
  have ht : 0 < t := by omega
  set e := stdSum (rfl : r + t = r + t) with he
  set ψ₁ : Fin r → kˣ →* ℂˣ := fun i => ψ (Fin.castAdd t i) with hψ₁
  set ψ₂ : Fin t → kˣ →* ℂˣ := fun i => ψ (Fin.natAdd r i) with hψ₂
  obtain ⟨ho₁, ho₂, hmem⟩ := GlobalTheory.T.blockDiagonal_principalSeriesCongruenceSubgroup_split k r t ψ hord hcut
  have hs₁ : ∀ i, IsSmoothChar (ψ₁ i) := fun i => hψ _
  have hs₂ : ∀ i, IsSmoothChar (ψ₂ i) := fun i => hψ _
  have one_grp : ∀ (m : ℕ) (φ : Fin m → kˣ →* ℂˣ), (1 : GL (Fin m) k) ∈ grp φ := by
    intro m φ
    refine ⟨(KO k (Fin m)).one_mem, fun i j hij => ?_⟩
    have h0 : ((1 : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) i j = 0 := by
      simp [Matrix.one_apply_ne (ne_of_lt hij)]
    rw [h0]
    exact (GlobalTheory.T.isTrivialOnUnitsModConductor_unitCharacterValue_props k).2.2.1 _
  let Q := twKer π (unipRad k (two e)) 1
  let ρ := jacU₂ e π
  have hρ : IsSmooth ρ := isSmooth_comp (isSmooth_jacU _ hπ) _ (continuous_leviTwo k)
  have hact : ∀ g w, ρ g (Q.mkQ w) = Q.mkQ (π (emb₂ k e g) w) := fun g w => rfl
  let P : Submodule ℂ V := (twKer (ρ.comp (MonoidHom.inl _ _)) (unipB k (Fin r)) 1 ⊔
      twKer (ρ.comp (MonoidHom.inr _ _)) (unipB k (Fin t)) 1).comap Q.mkQ
  have hP : twKer π (unipB k (Fin (r + t))) 1 ≤ P := by
    refine GlobalTheory.T.twistedJacquetKernel_twoBlock_unipotent_le_stages k r t V π P ?_ ?_ ?_
    · intro w hw
      refine Submodule.mem_comap.2 ?_
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero Q).2 hw]
      exact zero_mem _
    · intro u hu w
      refine Submodule.mem_comap.2 ?_
      refine Submodule.mem_sup_left (Submodule.subset_span ⟨⟨u, hu⟩, Q.mkQ w, ?_⟩)
      simp only [map_sub, MonoidHom.one_apply, Units.val_one, one_smul, Submodule.mkQ_apply]
      rfl
    · intro u hu w
      refine Submodule.mem_comap.2 ?_
      refine Submodule.mem_sup_right (Submodule.subset_span ⟨⟨u, hu⟩, Q.mkQ w, ?_⟩)
      simp only [map_sub, MonoidHom.one_apply, Units.val_one, one_smul, Submodule.mkQ_apply]
      rfl
  have hx := hP hv
  have hzero : Q.mkQ v = 0 := by
    refine GlobalTheory.T.twistedJacquet_survival_product_of_two_groups (GL (Fin r) k) (GL (Fin t) k) _ ρ hρ (unipB k (Fin r)) (unipB k (Fin t))
      (grp ψ₁) (grp ψ₂) (theta ψ₁) (theta ψ₂)
      (fun W _ _ σ hσ w hw hwe => ih r (by omega) ψ₁ W σ hσ hs₁ ho₁ w hw hwe)
      (fun W _ _ σ hσ w hw hwe => ih t (by omega) ψ₂ W σ hσ hs₂ ho₂ w hw hwe)
      (Q.mkQ v) hx ?_ ?_
    · intro a ha
      have hm : emb₂ k e (a, 1) ∈ grp ψ := (hmem a 1).2 ⟨ha, one_grp _ _⟩
      have hth := GlobalTheory.T.principalSeriesTypeCharacter_blockDiagonal k r t ψ hord a ha 1 (one_grp _ _)
      rw [(GlobalTheory.T.principalSeriesTypeCharacter_eq_one_near_one k t ψ₂ hs₂).1, mul_one] at hth
      show ρ (a, 1) (Q.mkQ v) = _
      rw [hact, heig _ hm, map_smul]
      exact congrArg (· • Q.mkQ v) hth
    · intro b hb
      have hm : emb₂ k e (1, b) ∈ grp ψ := (hmem 1 b).2 ⟨one_grp _ _, hb⟩
      have hth := GlobalTheory.T.principalSeriesTypeCharacter_blockDiagonal k r t ψ hord 1 (one_grp _ _) b hb
      rw [(GlobalTheory.T.principalSeriesTypeCharacter_eq_one_near_one k r ψ₁ hs₁).1, one_mul] at hth
      show ρ (1, b) (Q.mkQ v) = _
      rw [hact, heig _ hm, map_smul]
      exact congrArg (· • Q.mkQ v) hth
  have hvQ : v ∈ Q := (Submodule.Quotient.mk_eq_zero Q).1 hzero
  exact GlobalTheory.T.jacquetModule_maximalParabolic_principalSeriesTypeEigen k r t ψ V π hπ hψ hord hcut v hvQ heig

end GlobalTheory.PsType
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqZeroOfMemTwistedJacquetKernelUpperUnitriangulaStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_mem_twistedJacquetKernel_upperUnitriangular : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → (∀ i, IsSmoothChar (ψ i)) → Ordered ψ → ∀ v ∈ twKer π (unipB k (Fin n)) 1, IsEig π (grp ψ) (theta ψ) v → v = 0 := by
  first | exact @GlobalTheory.PsType.eq_zero_of_mem_twKer_unipB | exact GlobalTheory.PsType.eq_zero_of_mem_twKer_unipB | (intros; apply GlobalTheory.PsType.eq_zero_of_mem_twKer_unipB <;> assumption)
end
