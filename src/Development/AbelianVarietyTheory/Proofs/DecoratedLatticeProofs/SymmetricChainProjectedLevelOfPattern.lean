module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricChainProjectedLevelOfPattern
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricChainProjectedLevelOfPattern
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.SymChain.PrImage

section Plain
variable {k : Type*} [Field k] {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n] {c : ℕ}

variable (k n c) in
def fixX : Subgroup (GL (n ⊕ Fin c) k) where
  carrier := {v | ∀ r x, v.val r (.inl x) = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (.inl x)}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro v w hv hw r x
    have : (v.val * w.val) r (.inl x) = (v.val * (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)) r (.inl x) := by
      simp only [Matrix.mul_apply, hw _ x]
    rw [Units.val_mul, this, Matrix.mul_one, hv]
  inv_mem' := by
    intro v hv r x
    have : ((v⁻¹).val * v.val) r (.inl x) = ((v⁻¹).val * (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)) r (.inl x) := by
      simp only [Matrix.mul_apply, hv _ x]
    rw [Matrix.mul_one, Units.inv_mul] at this
    exact this.symm

theorem N_le_fixX : N k n c 1 ≤ fixX k n c := by
  refine (Subgroup.closure_le _).2 fun g hg r x => hg r (.inl x) ?_
  rcases r with r | r <;> simp [RootEx.lev]

theorem embA_mem_fixX (D : GL (Fin c) k) : embA n D ∈ fixX k n c := by
  intro r x
  change (fromBlocks 1 0 0 D.val : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (.inl x) = _
  rcases r with r | r <;> simp [Matrix.one_apply]

theorem embX_mul_embA (g : GL n k) (D : GL (Fin c) k) : embX c g * embA n D = embA n D * embX c g := by
  refine Units.ext ?_
  change (fromBlocks g.val 0 0 1 * fromBlocks 1 0 0 D.val : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) =
    fromBlocks 1 0 0 D.val * fromBlocks g.val 0 0 1
  simp [fromBlocks_multiply]

theorem mul_embX_inl {w : GL (n ⊕ Fin c) k} (hw : w ∈ fixX k n c) (g : GL n k) (r : n ⊕ Fin c) (x : n) :
    (w * embX c g).val r (.inl x) = (embX c g).val r (.inl x) := by
  have : (w.val * (fromBlocks g.val 0 0 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)) r (.inl x) =
      ((1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * (fromBlocks g.val 0 0 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k))
        r (.inl x) := by
    simp only [Matrix.mul_apply, Fintype.sum_sum_type, hw r, fromBlocks_apply₂₁, Matrix.zero_apply, mul_zero]
  rw [Matrix.one_mul] at this
  exact this

theorem embX_inr (g : GL n k) (r : n ⊕ Fin c) (i : Fin c) :
    (embX c g).val r (.inr i) = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (.inr i) := by
  change (fromBlocks g.val 0 0 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (.inr i) = _
  rcases r with r | r <;> simp [Matrix.one_apply]

theorem conj_symm_apply (F : LatFrame k ι (n ⊕ Fin c)) (y : GL (n ⊕ Fin c) k) :
    F.conj.symm y = (reGL F.ord).symm (F.bas⁻¹ * y * F.bas) := by
  rw [MulEquiv.symm_apply_eq, LatFrame.conj_apply]; simp [mul_assoc]

theorem entry_cases (ϖ : kˣ) (o : ι ≃ n ⊕ Fin c) {w : GL (n ⊕ Fin c) k} (hw : w ∈ fixX k n c) (g : GL n k)
    (a b : ι) :
    ((typeFrame ϖ o).conj.symm (embX c g)).val a b = ((typeFrame ϖ o).conj.symm (w * embX c g)).val a b ∨
      ((typeFrame ϖ o).conj.symm (embX c g)).val a b = (1 : Matrix ι ι k) a b := by
  obtain ⟨D, hD⟩ : ∃ D, (typeFrame ϖ o).bas = embA n D := ⟨_, rfl⟩
  have ho : (typeFrame ϖ o).ord = o := rfl
  have e1 : (embA n D)⁻¹ * embX c g * embA n D = embX c g := by
    rw [mul_assoc, embX_mul_embA, inv_mul_cancel_left]
  have e2 : (embA n D)⁻¹ * (w * embX c g) * embA n D = ((embA n D)⁻¹ * w * embA n D) * embX c g := by
    simp only [mul_assoc, embX_mul_embA]
  have hw' : (embA n D)⁻¹ * w * embA n D ∈ fixX k n c :=
    mul_mem (mul_mem (inv_mem (embA_mem_fixX D)) hw) (embA_mem_fixX D)
  rw [conj_symm_apply, conj_symm_apply, hD, ho, e1, e2, reGL_symm_val, reGL_symm_val, submatrix_apply,
    submatrix_apply, ← submatrix_one_equiv o, submatrix_apply]
  rcases o b with x | i
  · exact Or.inl (mul_embX_inl hw' g _ x).symm
  · exact Or.inr (embX_inr g _ i)

end Plain

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n] {c : ℕ}

theorem prX_eq_comap (P : Level (GL ι k)) (Fr : ι → ι → Prop)
    (hP : ∀ g, g ∈ P.J ↔ g ∈ KO k ι ∧ ∀ a b, ¬ Fr a b → valuation k (g.val a b - (1 : Matrix ι ι k) a b) < 1)
    (ϖ : kˣ) (o : ι ≃ n ⊕ Fin c) :
    prX (Cgrp (P.map (typeFrame ϖ o).conj).J 1) = (P.map (typeFrame ϖ o).conj).J.comap (embX c) := by
  have key : ∀ g : GL n k, g ∈ prX (Cgrp (P.map (typeFrame ϖ o).conj).J 1) →
      IntM ((typeFrame ϖ o).conj.symm (embX c g)).val ∧ ∀ a b, ¬ Fr a b →
        valuation k (((typeFrame ϖ o).conj.symm (embX c g)).val a b - (1 : Matrix ι ι k) a b) < 1 := by
    rintro g ⟨u, hu, hg⟩
    have h := (mem_Cgrp.1 hg).2
    rw [inv_one, one_mul, mul_one, Level.mem_map, hP] at h
    refine ⟨fun a b => ?_, fun a b hab => ?_⟩
    · rcases entry_cases ϖ o (N_le_fixX hu) g a b with e | e <;> rw [e]
      · exact intM_of_mem_KO h.1 a b
      · exact intM_one a b
    · rcases entry_cases ϖ o (N_le_fixX hu) g a b with e | e <;> rw [e]
      · exact h.2 a b hab
      · simp
  ext g
  rw [Subgroup.mem_comap]
  refine ⟨fun hg => ?_, fun hg => ⟨1, one_mem _, mem_Cgrp.2 ⟨?_, by simpa using hg⟩⟩⟩
  · rw [Level.mem_map, hP]
    refine ⟨mem_KO.2 ⟨(key g hg).1, ?_⟩, (key g hg).2⟩
    rw [← map_inv, ← map_inv]
    exact (key g⁻¹ (inv_mem hg)).1
  · rw [one_mul]
    exact Subgroup.mem_sup_left ⟨g, rfl⟩

theorem prLevel_of_pattern (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (h : S.Pattern t) : S.PrLevel t :=
  fun j c H => prX_eq_comap (S.P.iter t S.μ S.tame j).toLevel (FreeIx S.ρ) (h j) S.ϖ (stdOrd (Fin κ) t j c H)

end GlobalTheory.SymChain.PrImage
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricChainProjectedLevelOfPatternStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricChain_projected_level_of_pattern : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t → S.PrLevel t := by
  first | exact @GlobalTheory.SymChain.PrImage.prLevel_of_pattern | exact GlobalTheory.SymChain.PrImage.prLevel_of_pattern | (intros; apply GlobalTheory.SymChain.PrImage.prLevel_of_pattern <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricChainOneCouplingCosetOfPattern
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricChainOneCouplingCosetOfPattern
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

namespace GlobalTheory.SymChain
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

section SlopeTestRemainingChoices
variable {k : Type} [Field k] {ι ι' n n' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

omit [Fintype ι] [DecidableEq ι] in
theorem typeFrame_bas_zero (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin 0) : (typeFrame ϖ ord).bas = 1 := by
  apply Units.ext
  ext i j
  rcases i with i | i
  · rcases j with j | j
    · simp [typeFrame, embA, Matrix.one_apply]
    · exact j.elim0
  · exact i.elim0

omit [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] in
theorem coords_withCol (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin 0) (ord' : ι' ≃ n' ⊕ Fin (0 + 1)) (x₀ : Matrix n n' k)
    (y : n → k) : (typeFrame ϖ ord).coords (typeFrame ϖ ord') (withCol x₀ y) =
      (withCol x₀ ((ϖ : k) • y)).submatrix ord ord' := by
  unfold LatFrame.coords
  rw [typeFrame_bas_zero]
  congr 1
  ext i j
  rcases i with i | i
  · rcases j with j | j
    · simp [withCol, typeFrame, embA, Matrix.fromBlocks_multiply]
    · simp [withCol, typeFrame, embA, Matrix.fromBlocks_multiply, Fin.eq_zero j, mul_comm]
  · exact i.elim0

variable [ValuativeRel k]

theorem unif_mul_lt_one_iff {ϖ : kˣ} (h : IsUnif ϖ) (z : k) :
    valuation k ((ϖ : k) * z) < 1 ↔ valuation k z ≤ 1 := by
  rw [h, map_mul]
  have h0 : 0 < valuation k (ϖ : k) := by
    rw [zero_lt_iff]
    exact (Valuation.ne_zero_iff _).mpr (Units.ne_zero ϖ)
  exact mul_le_iff_le_one_right h0

end SlopeTestRemainingChoices

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

theorem SymData.Psi_one_eq (x₀ : Matrix (XIx (Fin κ) t (s + 1)) (XIx (Fin κ) t s) k) (y : XIx (Fin κ) t (s + 1) → k) :
    (S.T t).Psi 1 x₀ y = (S.P.iter t S.μ S.tame s).Phi t (S.μ (s + 1))
      (((withCol x₀ ((S.ϖ : k) • y)).submatrix (stdOrd (Fin κ) t (s + 1) 0 rfl)
        (stdOrd (Fin κ) t s (0 + 1) rfl)).submatrix (ixSucc _ t s) id) := by
  simp only [Chain.Psi, om_one, SymData.T, typeChain, Chain.ofType, LatFrame.transport, coords_withCol,
    TypeDatum.iterPhi]

omit [Fintype t] [DecidableEq t] in
theorem not_freeIx_col (ρ : ℕ) {l j : ℕ} (a : Ix (Fin κ ⊕ Fin (l + 1)) t j) :
    ¬ FreeIx ρ a (.inl (.inr 0)) := by
  rcases a with (i | i) | p <;> simp [FreeIx, FreeTop]

omit [Fintype t] [DecidableEq t] in
theorem stdOrd_last (s : ℕ) : stdOrd (Fin κ) t (s + 1) 0 rfl (.inl (.inr 0)) = .inl (.inl (.inr 0)) := by
  simpa using stdOrd_f (Fin κ) t (s + 1) 0 rfl 0

omit [Fintype t] [DecidableEq t] in
theorem stdOrd_pen (s : ℕ) : stdOrd (Fin κ) t s (0 + 1) rfl (.inl (.inr 0)) = .inr 0 := by
  simpa using standardOrderExtendedBasis_apply_low_block (Fin κ) t s (0 + 1) rfl 0

omit [Fintype t] in
theorem SymData.symmetricChain_sub_base_mem_latticeBox_iff (y : XIx (Fin κ) t (s + 1) → k) :
    y - S.y0 t ∈ box (XIx (Fin κ) t (s + 1)) (1 : kˣ) ↔ ∀ i, valuation k ((S.ϖ : k) * y i -
      (1 : Matrix (XIx (Fin κ) t (s + 1)) (XIx (Fin κ) t (s + 1)) k) i (Sum.inl (Sum.inr 0))) < 1 := by
  rw [mem_box]
  refine forall_congr' fun i => ?_
  have e : (S.ϖ : k) * y i - (1 : Matrix (XIx (Fin κ) t (s + 1)) (XIx (Fin κ) t (s + 1)) k) i (Sum.inl (Sum.inr 0)) =
      (S.ϖ : k) * (y - S.y0 t) i := by
    simp only [SymData.y0, Pi.sub_apply, Pi.single_apply, Matrix.one_apply, mul_sub]
    split_ifs <;> simp
  rw [e, unif_mul_lt_one_iff S.unif]
  simp

omit [Fintype t] [DecidableEq t] in
private theorem stdOrd_ixSucc_inl_inr_zero :
    stdOrd (Fin κ) t (s + 1) 0 rfl (ixSucc (Fin κ ⊕ Fin (s + 1)) t s (Sum.inl (Sum.inl (Sum.inr 0)))) =
      Sum.inl (Sum.inl (Sum.inr 0)) := by
  have h : ixSucc (Fin κ ⊕ Fin (s + 1)) t s (Sum.inl (Sum.inl (Sum.inr 0))) = Sum.inl (Sum.inr 0) := rfl
  rw [h, stdOrd_last]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype t] [DecidableEq t] in
private theorem submatrix_withCol_stdOrd_ixSucc_apply_eq (x₀ : Matrix (XIx (Fin κ) t (s + 1)) (XIx (Fin κ) t s) k)
    (w : XIx (Fin κ) t (s + 1) → k) (r : Ix (Fin κ ⊕ Fin (s + 1)) t s ⊕ t) (i : XIx (Fin κ) t (s + 1))
    (hr : stdOrd (Fin κ) t (s + 1) 0 rfl (ixSucc _ t s r) = Sum.inl i) :
    (((withCol x₀ w).submatrix (stdOrd (Fin κ) t (s + 1) 0 rfl) (stdOrd (Fin κ) t s (0 + 1) rfl)).submatrix
      (ixSucc _ t s) id) r (Sum.inl (Sum.inr 0)) = w i := by
  simp only [Matrix.submatrix_apply, id, hr, stdOrd_pen, withCol, Matrix.fromBlocks_apply₁₂, Matrix.of_apply]

private theorem sub_y0_mem_box_of_psi_ne_zero (hP : S.Pattern t)
    (x₀ : Matrix (XIx (Fin κ) t (s + 1)) (XIx (Fin κ) t s) k) (y : XIx (Fin κ) t (s + 1) → k)
    (h : (S.T t).Psi 1 x₀ y ≠ 0) : y - S.y0 t ∈ box (XIx (Fin κ) t (s + 1)) (1 : kˣ) := by
  rw [S.Psi_one_eq t x₀ y] at h
  have hent := submatrix_withCol_stdOrd_ixSucc_apply_eq t x₀ ((S.ϖ : k) • y)
  generalize hX : ((withCol x₀ ((S.ϖ : k) • y)).submatrix (stdOrd (Fin κ) t (s + 1) 0 rfl)
    (stdOrd (Fin κ) t s (0 + 1) rfl)).submatrix (ixSucc _ t s) id = X at h hent
  obtain ⟨⟨g, hgJ, hg⟩, hmax⟩ := (TypeDatum.Phi_ne_zero_iff _ _).mp h
  rw [hP s g] at hgJ
  rw [S.symmetricChain_sub_base_mem_latticeBox_iff t y]
  intro i
  set b' : Ix (Fin κ ⊕ Fin (s + 1)) t s := Sum.inl (Sum.inr 0) with hb'
  set r := (ixSucc _ t s).symm ((stdOrd (Fin κ) t (s + 1) 0 rfl).symm (Sum.inl i)) with hrdef
  have hr : stdOrd (Fin κ) t (s + 1) 0 rfl (ixSucc _ t s r) = Sum.inl i := by simp [r]
  have hf := stdOrd_ixSucc_inl_inr_zero (κ := κ) t (s := s)
  have key : i = Sum.inl (Sum.inr 0) ↔ r = Sum.inl b' := by
    constructor
    · intro hi
      apply (ixSucc _ t s).injective
      apply (stdOrd (Fin κ) t (s + 1) 0 rfl).injective
      rw [hr, hf, hi]
    · intro hrb
      rw [hrb, hf] at hr
      exact (Sum.inl_injective hr).symm
  have hv := hent r i hr
  clear_value r
  rcases r with a | τ
  · have h1 := hgJ.2 a b' (not_freeIx_col t S.ρ a)
    have hga : g.val a b' = (S.ϖ : k) * y i := by
      rw [hg]
      exact hv
    rw [hga] at h1
    have h1' : (1 : Matrix (Ix (Fin κ ⊕ Fin (s + 1)) t s) (Ix (Fin κ ⊕ Fin (s + 1)) t s) k) a b' =
        (1 : Matrix (XIx (Fin κ) t (s + 1)) (XIx (Fin κ) t (s + 1)) k) i (Sum.inl (Sum.inr 0)) := by
      simp only [Matrix.one_apply, key, Sum.inl.injEq]
    rwa [h1'] at h1
  · have h1 := hmax τ b'
    have hne : i ≠ Sum.inl (Sum.inr 0) := fun hi => by simpa using key.mp hi
    have hbot : X.toRows₂ τ b' = (S.ϖ : k) * y i := hv
    rw [hbot] at h1
    simpa [Matrix.one_apply, hne] using h1

private theorem psi_eq_psi_y0_of_sub_y0_mem_box (x₀ : Matrix (XIx (Fin κ) t (s + 1)) (XIx (Fin κ) t s) k) (y : XIx (Fin κ) t (s + 1) → k)
    (hy : y - S.y0 t ∈ box (XIx (Fin κ) t (s + 1)) (1 : kˣ)) :
    (S.T t).Psi 1 x₀ y = (S.T t).Psi 1 x₀ (S.y0 t) := by
  rw [S.Psi_one_eq t x₀ y, S.Psi_one_eq t x₀ (S.y0 t)]
  have hsplit : withCol x₀ ((S.ϖ : k) • y) =
      withCol x₀ ((S.ϖ : k) • S.y0 t) + withCol 0 ((S.ϖ : k) • (y - S.y0 t)) := by
    ext i j
    rcases i with i | i
    · rcases j with j | j
      · simp [withCol]
      · simp [withCol]
        ring
    · exact i.elim0
  have hw : ∀ a b, valuation k (withCol (0 : Matrix (XIx (Fin κ) t (s + 1)) (XIx (Fin κ) t s) k)
      ((S.ϖ : k) • (y - S.y0 t)) a b) < 1 := by
    rintro (a | a) (b | b)
    · simp [withCol]
    · simp only [withCol, Matrix.fromBlocks_apply₁₂, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
      exact (unif_mul_lt_one_iff S.unif _).mpr (by simpa using (mem_box.mp hy) a)
    · exact a.elim0
    · exact a.elim0
  rw [hsplit]
  have hsum : (((withCol x₀ ((S.ϖ : k) • S.y0 t) + withCol 0 ((S.ϖ : k) • (y - S.y0 t))).submatrix
      (stdOrd (Fin κ) t (s + 1) 0 rfl) (stdOrd (Fin κ) t s (0 + 1) rfl)).submatrix (ixSucc _ t s) id) =
      ((withCol x₀ ((S.ϖ : k) • S.y0 t)).submatrix (stdOrd (Fin κ) t (s + 1) 0 rfl)
        (stdOrd (Fin κ) t s (0 + 1) rfl)).submatrix (ixSucc _ t s) id +
      ((withCol 0 ((S.ϖ : k) • (y - S.y0 t))).submatrix (stdOrd (Fin κ) t (s + 1) 0 rfl)
        (stdOrd (Fin κ) t s (0 + 1) rfl)).submatrix (ixSucc _ t s) id := by
    ext i j
    rfl
  rw [hsum]
  exact TypeDatum.Phi_add _ (S.tame (s + 1)) _ (fun i j => hw _ _)

private theorem mulVec_y0_sub_y0_mem_box_of_embX_mem_J (hP : S.Pattern t) (γ : GL (XIx (Fin κ) t (s + 1)) k)
    (hγ : embX 0 γ ∈ ((S.T t).lev (s + 1) 0 rfl).J) :
    γ.val *ᵥ S.y0 t - S.y0 t ∈ box (XIx (Fin κ) t (s + 1)) (1 : kˣ) := by
  have h1 : (typeFrame S.ϖ (stdOrd (Fin κ) t (s + 1) 0 rfl)).conj.symm (embX 0 γ) ∈
      (S.P.iter t S.μ S.tame (s + 1)).J := Level.mem_map.mp hγ
  rw [hP] at h1
  have hval : ((typeFrame S.ϖ (stdOrd (Fin κ) t (s + 1) 0 rfl)).conj.symm (embX 0 γ)).val =
      (embX 0 γ).val.submatrix (stdOrd (Fin κ) t (s + 1) 0 rfl) (stdOrd (Fin κ) t (s + 1) 0 rfl) := by
    rw [LatFrame.conj, MulEquiv.symm_trans_apply, typeFrame_bas_zero, MulAut.conj_symm_apply, inv_one, one_mul,
      mul_one, reGL_symm_val]
    rfl
  rw [mem_box]
  intro i
  set b' : Ix (Fin κ ⊕ Fin (s + 1)) t (s + 1) := Sum.inl (Sum.inr 0) with hb'
  have hb : stdOrd (Fin κ) t (s + 1) 0 rfl b' = Sum.inl (Sum.inl (Sum.inr 0)) := stdOrd_last t s
  set a := (stdOrd (Fin κ) t (s + 1) 0 rfl).symm (Sum.inl i) with ha
  have hai : stdOrd (Fin κ) t (s + 1) 0 rfl a = Sum.inl i := by simp [a]
  have h2 := h1.2 a b' (not_freeIx_col t S.ρ a)
  rw [hval, Matrix.submatrix_apply, hai, hb] at h2
  have hone : (1 : Matrix (Ix (Fin κ ⊕ Fin (s + 1)) t (s + 1)) (Ix (Fin κ ⊕ Fin (s + 1)) t (s + 1)) k) a b' =
      (1 : Matrix (XIx (Fin κ) t (s + 1)) (XIx (Fin κ) t (s + 1)) k) i (Sum.inl (Sum.inr 0)) := by
    have : a = b' ↔ i = Sum.inl (Sum.inr 0) := by
      rw [← (stdOrd (Fin κ) t (s + 1) 0 rfl).apply_eq_iff_eq, hai, hb, Sum.inl.injEq]
    simp only [Matrix.one_apply, this]
  rw [hone] at h2
  have hemb : (embX 0 γ).val (Sum.inl i) (Sum.inl (Sum.inl (Sum.inr 0))) = γ.val i (Sum.inl (Sum.inr 0)) := by
    simp [embX]
  rw [hemb] at h2
  have hvec : (γ.val *ᵥ S.y0 t - S.y0 t) i =
      (γ.val i (Sum.inl (Sum.inr 0)) - (1 : Matrix (XIx (Fin κ) t (s + 1)) (XIx (Fin κ) t (s + 1)) k) i
        (Sum.inl (Sum.inr 0))) * ((S.ϖ⁻¹ : kˣ) : k) := by
    simp only [SymData.y0, Matrix.mulVec_single, Pi.sub_apply, Pi.single_apply, Matrix.one_apply, sub_mul]
    split_ifs <;> simp
  rw [hvec, map_mul, Units.val_one, map_one]
  have hu : valuation k ((S.ϖ⁻¹ : kˣ) : k) = (valuation k (S.ϖ : k))⁻¹ := by
    rw [Units.val_inv_eq_inv_val, map_inv₀]
  rw [hu, ← div_eq_mul_inv, div_le_one₀ (by
    rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).mpr (Units.ne_zero S.ϖ))]
  exact (S.unif _).mp h2

theorem SymData.oneCoupling_of_pattern (hP : S.Pattern t) : S.OneCoupling t := by
  exact ⟨fun x₀ y h => sub_y0_mem_box_of_psi_ne_zero S t hP x₀ y h,
    fun x₀ y hy => psi_eq_psi_y0_of_sub_y0_mem_box S t x₀ y hy,
    fun γ hγ => mulVec_y0_sub_y0_mem_box_of_embX_mem_J S t hP γ hγ⟩

theorem oneCoupling : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t → S.OneCoupling t := by
  intro k _ _ _ _ s κ S t _ _ hP
  exact S.oneCoupling_of_pattern t hP

end GlobalTheory.SymChain
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricChainOneCouplingCosetOfPatternStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricChain_oneCoupling_coset_of_pattern : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t → S.OneCoupling t := by
  first | exact @GlobalTheory.SymChain.oneCoupling | exact GlobalTheory.SymChain.oneCoupling | (intros; apply GlobalTheory.SymChain.oneCoupling <;> assumption)
end
end
