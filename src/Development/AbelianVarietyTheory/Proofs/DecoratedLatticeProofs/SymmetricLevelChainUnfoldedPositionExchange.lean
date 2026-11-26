module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedDepthOneLevelCharacterClosedForm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymLevelChainTestFunctionAddRow
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymLevelChainTestFunctionAddRow
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

namespace GlobalTheory.SymChain.RowShift

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_add_row {n : Type} [Fintype n] [DecidableEq n] {g : GL n k} (hg : g ∈ KO k n) (a : n) (w : n → k)
    (hw : ∀ s, w s ∈ 𝒪[k]) (h : valuation k ((w ᵥ* (g⁻¹).val) a) < 1) :
    ∃ g' ∈ KO k n, g'.val = g.val + vecMulVec (Pi.single a 1) w ∧
      ∀ μ : kˣ →* ℂˣ, IsTame μ → μ (Matrix.GeneralLinearGroup.det g') = μ (Matrix.GeneralLinearGroup.det g) := by
  obtain ⟨h1, h2⟩ := mem_KO.1 hg
  have hE : ∀ w : n → k, (∀ s, w s ∈ 𝒪[k]) → IntM (vecMulVec (Pi.single a (1 : k)) w) := fun w hw i j => by
    rw [vecMulVec_apply, Pi.single_apply]
    split_ifs
    · simpa using hw j
    · simp
  set f := w ᵥ* (g⁻¹).val with hf
  have hfi : ∀ s, f s ∈ 𝒪[k] := fun s => sum_mem fun i _ => mul_mem (hw i) (h2 i s)
  set F : Matrix n n k := vecMulVec (Pi.single a 1) f with hF
  have hFF : MaxM (F * F) := fun i j => by
    rw [hF, vecMulVec_mul_vecMulVec, vecMulVec_apply, dotProduct_single, mul_one, Pi.smul_apply, smul_eq_mul,
      Pi.single_apply]
    split_ifs
    · rw [one_mul, map_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_left zero_le h (hfi j)
    · simp
  obtain ⟨u, hu, eu⟩ := exists_mem_KO_of_mul (A := 1 + F) (A' := 1 + -F) (intM_one.add (hE f hfi))
    (intM_one.add (hE f hfi).neg) (by
      have : (1 + F) * (1 + -F) - 1 = -(F * F) := by noncomm_ring
      rw [this]; exact hFF.neg)
  refine ⟨u * g, mul_mem hu hg, ?_, fun μ hμ => ?_⟩
  · rw [Units.val_mul, eu, Matrix.add_mul, Matrix.one_mul, hF, vecMulVec_mul, hf, vecMul_vecMul, Units.inv_mul,
      vecMul_one]
  · rw [map_mul, map_mul, hμ (Matrix.GeneralLinearGroup.det u), one_mul]
    rw [Matrix.GeneralLinearGroup.val_det_apply, eu, hF, vecMulVec_eq Unit,
      det_one_add_replicateCol_mul_replicateRow, dotProduct_single, mul_one, add_sub_cancel_left]
    exact h

variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

theorem exists_mem_iter (hP : S.Pattern t) (j : ℕ) (q : Fin (s + 1)) (hq : q.val + 1 ≤ S.ρ)
    (w : Ix (Fin κ ⊕ Fin (s + 1)) t j → k) (hw : ∀ b, w b ∈ 𝒪[k])
    (h0 : ∀ l : Fin (s + 1), l.val ≤ q.val + 1 → w (.inl (.inr l)) = 0) (μ : kˣ →* ℂˣ) (hμ : IsTame μ)
    (g : (S.P.iter t S.μ S.tame j).J) :
    ∃ g' : (S.P.iter t S.μ S.tame j).J,
      g'.1.val = g.1.val + vecMulVec (Pi.single (.inl (.inr q)) 1) w ∧
      (S.P.iter t S.μ S.tame j).rho μ g' = (S.P.iter t S.μ S.tame j).rho μ g := by
  obtain ⟨hg, hgp⟩ := (hP j g.1).1 g.2
  obtain ⟨hgi, hgip⟩ := (hP j g.1⁻¹).1 (inv_mem g.2)
  obtain ⟨g', hg', e, hd⟩ := exists_add_row hg (.inl (.inr q)) w hw (by
    refine Valuation.map_sum_lt _ one_ne_zero fun b _ => ?_
    by_cases hb : w b = 0
    · simp [hb]
    · have hne : b ≠ .inl (.inr q) := by
        rintro rfl; exact hb (h0 q (by omega))
      have hnf : ¬ FreeIx S.ρ b (.inl (.inr q)) := by
        rcases b with (b | b) | b
        · simp only [FreeIx, FreeTop]; omega
        · simp only [FreeIx, FreeTop]
          intro hlt
          exact hb (h0 b (by have := Fin.lt_def.1 hlt; omega))
        · simp [FreeIx]
      have := hgip b _ hnf
      rw [Matrix.one_apply_ne hne, sub_zero] at this
      rw [map_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_right (hw b) zero_le this)
  have ent : ∀ a b, (a ≠ .inl (.inr q) ∨ w b = 0) → g'.val a b = g.1.val a b := by
    intro a b hab
    rw [e, Matrix.add_apply, vecMulVec_apply]
    rcases hab with hab | hab
    · rw [Pi.single_eq_of_ne hab, zero_mul, add_zero]
    · rw [hab, mul_zero, add_zero]
  have hm : g' ∈ (S.P.iter t S.μ S.tame j).J := by
    refine (hP j g').2 ⟨hg', fun a b hab => ?_⟩
    rw [ent a b]
    · exact hgp a b hab
    · by_cases ha : a = .inl (.inr q)
      · subst ha
        right
        rcases b with (b | b) | b
        · simp only [FreeIx, FreeTop] at hab; omega
        · simp only [FreeIx, FreeTop] at hab
          exact h0 b (by have := Fin.lt_def.not.1 hab; omega)
        · simp [FreeIx] at hab
      · exact Or.inl ha
  refine ⟨⟨g', hm⟩, e, ?_⟩
  rw [TypeDatum.rho_apply, TypeDatum.rho_apply, hd μ hμ]
  congr 1
  obtain ⟨a, D, ea, hD, el⟩ := GlobalTheory.SymBridge.iter_lam_closed k _ t S.P S.μ S.tame j g
  obtain ⟨a', D', ea', hD', el'⟩ := GlobalTheory.SymBridge.iter_lam_closed k _ t S.P S.μ S.tame j ⟨g', hm⟩
  have eD : D' = D := by
    funext i
    refine Units.ext ?_
    rw [(hD i).2, (hD' i).2]
    ext x y
    exact ent _ _ (Or.inl (by simp))
  have ela : S.P.lam a' = S.P.lam a := by
    refine Units.ext ?_
    rw [S.sym.2, S.sym.2]
    have e1 : simpleSum a'.1 = simpleSum a.1 := by
      unfold simpleSum
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      split_ifs with hxy
      · rw [ea, ea']
        refine ent _ _ ?_
        by_cases hx : x = q
        · subst hx; exact Or.inr (h0 y hxy.le)
        · exact Or.inl (by simpa using hx)
      · rfl
    have e2 : a'.1.val.toBlocks₁₁ = a.1.val.toBlocks₁₁ := by
      rw [ea, ea']
      ext x y
      exact ent _ _ (Or.inl (by simp))
    rw [e1, e2]
  rw [el, el', eD, ela]

theorem extZ_add_row (hP : S.Pattern t) (j : ℕ) (q : Fin (s + 1)) (hq : q.val + 1 ≤ S.ρ)
    (w : Ix (Fin κ ⊕ Fin (s + 1)) t j → k) (hw : ∀ b, w b ∈ 𝒪[k])
    (h0 : ∀ l : Fin (s + 1), l.val ≤ q.val + 1 → w (.inl (.inr l)) = 0) (μ : kˣ →* ℂˣ) (hμ : IsTame μ)
    (M : Matrix (Ix (Fin κ ⊕ Fin (s + 1)) t j) (Ix (Fin κ ⊕ Fin (s + 1)) t j) k) :
    extZ _ ((S.P.iter t S.μ S.tame j).rho μ) (M + vecMulVec (Pi.single (.inl (.inr q)) 1) w) =
      extZ _ ((S.P.iter t S.μ S.tame j).rho μ) M := by
  by_cases h : ∃ g ∈ (S.P.iter t S.μ S.tame j).J, g.val = M
  · obtain ⟨g, hg, rfl⟩ := h
    obtain ⟨g', e, er⟩ := exists_mem_iter S t hP j q hq w hw h0 μ hμ ⟨g, hg⟩
    rw [← e, extZ_coe, extZ_coe _ _ ⟨g, hg⟩, er]
  · rw [extZ_of_not _ _ h, extZ_of_not]
    rintro ⟨g, hg, e⟩
    obtain ⟨g', e', -⟩ := exists_mem_iter S t hP j q hq (-w) (fun b => neg_mem (hw b))
      (fun l hl => by simp [h0 l hl]) μ hμ ⟨g, hg⟩
    refine h ⟨g', g'.2, ?_⟩
    rw [e', e, vecMulVec_neg, add_neg_cancel_right]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem coords_typeFrame {ι ι' n n' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype n]
    [DecidableEq n] [Fintype n'] [DecidableEq n'] {c c' : ℕ} (ϖ : kˣ) (o : ι ≃ n ⊕ Fin c) (o' : ι' ≃ n' ⊕ Fin c')
    (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin c') k) (a : ι) (b : ι') :
    (typeFrame ϖ o).coords (typeFrame ϖ o') x a b =
      Sum.elim (fun _ => 1) (fun i : Fin c => (((ϖ ^ (i.val + 1))⁻¹ : kˣ) : k)) (o a) * x (o a) (o' b) *
        Sum.elim (fun _ => 1) (fun i : Fin c' => ((ϖ ^ (i.val + 1) : kˣ) : k)) (o' b) := by
  have e : ((typeFrame ϖ o).bas⁻¹).val =
      diagonal (Sum.elim (fun _ => 1) (fun i : Fin c => (((ϖ ^ (i.val + 1))⁻¹ : kˣ) : k))) := by
    rw [← fromBlocks_diagonal]
    refine Units.inv_eq_of_mul_eq_one_right ?_
    change fromBlocks 1 0 0 (diagonal _) * _ = _
    simp [fromBlocks_multiply, diagonal_mul_diagonal]
  have e' : ((typeFrame ϖ o').bas).val =
      diagonal (Sum.elim (fun _ => 1) (fun i : Fin c' => ((ϖ ^ (i.val + 1) : kˣ) : k))) := by
    rw [← fromBlocks_diagonal, diagonal_one]
    rfl
  unfold LatFrame.coords
  rw [e, e', submatrix_apply, mul_diagonal, diagonal_mul]
  rfl

theorem phi_add_row : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t → ∀ (j c : ℕ) (H : j + c = s) (q : Fin c), q.val + 1 ≤ S.ρ → ∀ (x : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin c) (XIx (Fin κ) t j ⊕ Fin (c + 1)) k), (∀ s', x (Sum.inr q) (Sum.inl s') = 0) → ∀ v : XIx (Fin κ) t j → k, (S.T t).Phi j c H (x + Matrix.of fun r s' => if r = Sum.inr q then Sum.elim v 0 s' else 0) = if ∀ s', valuation k ((((S.ϖ ^ (q.val + 1))⁻¹ : kˣ) : k) * v s') ≤ 1 then (S.T t).Phi j c H x else 0 := by
  intro k _ _ _ _ s κ S t _ _ hP j c H q hq x hx v
  let o := stdOrd (Fin κ) t (l := s + 1) (j + 1) c (by omega)
  let o' := stdOrd (Fin κ) t (l := s + 1) j (c + 1) (by omega)
  let q' : Fin (s + 1) := ⟨q.val, by omega⟩
  have hoq : o (.inl (.inr q')) = .inr q := standardOrderExtendedBasis_apply_low_block _ _ _ _ _ q
  let w : Ix (Fin κ ⊕ Fin (s + 1)) t j → k := fun b =>
    Sum.elim (fun s' => (((S.ϖ ^ (q.val + 1))⁻¹ : kˣ) : k) * v s') 0 (o' b)
  let C : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin c) (XIx (Fin κ) t j ⊕ Fin (c + 1)) k →
      Matrix (Ix (Fin κ ⊕ Fin (s + 1)) t j ⊕ t) (Ix (Fin κ ⊕ Fin (s + 1)) t j) k := fun z =>
    ((typeFrame S.ϖ o).coords (typeFrame S.ϖ o') z).submatrix (ixSucc _ t j) id
  have hPhi : ∀ z, (S.T t).Phi j c H z = (S.P.iter t S.μ S.tame j).Phi t (S.μ (j + 1)) (C z) := fun z => rfl
  set x' := x + Matrix.of fun r s' => if r = Sum.inr q then Sum.elim v 0 s' else 0 with hx'
  have key : ∀ a b, C x' a b = C x a b + if a = .inl (.inl (.inr q')) then w b else 0 := by
    intro a b
    have hiff : o (ixSucc _ t j a) = .inr q ↔ a = .inl (.inl (.inr q')) := by
      rw [← hoq, o.apply_eq_iff_eq, ← (ixSucc (Fin κ ⊕ Fin (s + 1)) t j).apply_eq_iff_eq]; rfl
    simp only [C, submatrix_apply, coords_typeFrame, hx', Matrix.add_apply, Matrix.of_apply, id, mul_add, add_mul]
    congr 1
    by_cases ha : a = .inl (.inl (.inr q'))
    · rw [if_pos ha, if_pos (hiff.2 ha), hiff.2 ha]
      simp only [w]
      rcases o' b with y | y <;> simp
    · rw [if_neg ha, if_neg (hiff.not.2 ha), mul_zero, zero_mul]
  have e2 : (C x').toRows₂ = (C x).toRows₂ := by
    ext a b; simp [toRows₂, key]
  have e1 : (C x').toRows₁ = (C x).toRows₁ + vecMulVec (Pi.single (.inl (.inr q')) 1) w := by
    ext a b
    simp only [toRows₁, Matrix.of_apply, key, Matrix.add_apply, vecMulVec_apply, Pi.single_apply, Sum.inl.injEq,
      ite_mul, one_mul, zero_mul]
  rw [hPhi, hPhi]
  split_ifs with hv
  · unfold TypeDatum.Phi
    rw [e1, e2, extZ_add_row S t hP j q' hq w ?_ ?_ _ (S.tame _)]
    · intro b
      simp only [w]
      rcases o' b with y | y
      · exact hv y
      · exact zero_mem _
    · intro l hl
      have hl' : l.val ≤ q.val + 1 := hl
      have : o' (.inl (.inr l)) = .inr ⟨l.val, by omega⟩ := standardOrderExtendedBasis_apply_low_block (Fin κ) t j (c + 1) _ ⟨l.val, by omega⟩
      simp only [w, this]; rfl
  · by_contra hne
    refine hv fun y => ?_
    have := TypeDatum.intM_of_Phi_ne_zero _ _ hne (.inl (.inl (.inr q'))) (o'.symm (.inl y))
    rw [key, if_pos rfl] at this
    have h0 : C x (.inl (.inl (.inr q'))) (o'.symm (.inl y)) = 0 := by
      change (typeFrame S.ϖ o).coords (typeFrame S.ϖ o') x (.inl (.inr q')) (o'.symm (.inl y)) = 0
      rw [coords_typeFrame, hoq, o'.apply_symm_apply, hx, mul_zero, zero_mul]
    rw [h0, zero_add] at this
    simp only [w, o'.apply_symm_apply, Sum.elim_inl] at this
    exact this

end GlobalTheory.SymChain.RowShift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymLevelChainTestFunctionAddRowStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symLevelChain_testFunction_add_row : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t → ∀ (j c : ℕ) (H : j + c = s) (q : Fin c), q.val + 1 ≤ S.ρ → ∀ (x : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin c) (XIx (Fin κ) t j ⊕ Fin (c + 1)) k), (∀ s', x (Sum.inr q) (Sum.inl s') = 0) → ∀ v : XIx (Fin κ) t j → k, (S.T t).Phi j c H (x + Matrix.of fun r s' => if r = Sum.inr q then Sum.elim v 0 s' else 0) = if ∀ s', valuation k ((((S.ϖ ^ (q.val + 1))⁻¹ : kˣ) : k) * v s') ≤ 1 then (S.T t).Phi j c H x else 0 := by
  first | exact @GlobalTheory.SymChain.RowShift.phi_add_row | exact GlobalTheory.SymChain.RowShift.phi_add_row | (intros; apply GlobalTheory.SymChain.RowShift.phi_add_row <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixBlockColumnVanishingStep
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixBlockColumnVanishingStep
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

namespace GlobalTheory.SymChain.ExchangeCol

section SlopeTestRemainingChoices
variable {k : Type} [Field k] {ι ι' n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c c' : ℕ}

theorem coords_typeFrame_apply (ϖ : kˣ) (o : ι ≃ n ⊕ Fin c) (o' : ι' ≃ n' ⊕ Fin c')
    (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin c') k) (a : ι) (b : ι') :
    (typeFrame ϖ o).coords (typeFrame ϖ o') x a b =
      Sum.elim (fun _ => 1) (fun i : Fin c => ((ϖ : k) ^ (i.val + 1))⁻¹) (o a) * x (o a) (o' b) *
        Sum.elim (fun _ => 1) (fun i : Fin c' => (ϖ : k) ^ (i.val + 1)) (o' b) := by
  have e : ((typeFrame ϖ o).bas⁻¹).val =
      fromBlocks 1 0 0 (diagonal fun i : Fin c => ((ϖ : k) ^ (i.val + 1))⁻¹) := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    change fromBlocks 1 0 0 (diagonal _) * _ = _
    simp [fromBlocks_multiply, diagonal_mul_diagonal]
  have e' : (typeFrame ϖ o').bas.val =
      fromBlocks 1 0 0 (diagonal fun i : Fin c' => (ϖ : k) ^ (i.val + 1)) := rfl
  unfold LatFrame.coords
  rw [e, e', ← diagonal_one, ← diagonal_one, fromBlocks_diagonal, fromBlocks_diagonal, submatrix_apply,
    mul_diagonal, diagonal_mul]
  rfl

theorem coords_add (F : LatFrame k ι (n ⊕ Fin c)) (F' : LatFrame k ι' (n' ⊕ Fin c'))
    (x y : Matrix (n ⊕ Fin c) (n' ⊕ Fin c') k) :
    F.coords F' (x + y) = F.coords F' x + F.coords F' y := by
  unfold LatFrame.coords
  rw [Matrix.mul_add, Matrix.add_mul]
  rfl

end SlopeTestRemainingChoices

theorem phi_add_col (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (hP : S.Pattern t)
    (j c : ℕ) (H : j + c = s) (q : Fin c) (hρ : q.val + 1 ≤ S.ρ) (hc : q.val + 2 ≤ c)
    (x : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin c) (XIx (Fin κ) t j ⊕ Fin (c + 1)) k)
    (hx : ∀ r, x (Sum.inl r) (Sum.inr q.succ) = 0) (w : XIx (Fin κ) t (j + 1) → k) :
    (S.T t).Phi j c H (x + Matrix.of fun r s' => if s' = Sum.inr q.succ then Sum.elim w 0 r else 0) =
      if ∀ r, valuation k (((S.ϖ ^ (q.val + 2) : kˣ) : k) * w r) < 1 then (S.T t).Phi j c H x else 0 := by
  have H1 : j + 1 + c = s + 1 := by omega
  have H2 : j + (c + 1) = s + 1 := by omega
  have hPhi : ∀ z, (S.T t).Phi j c H z = (S.P.iter t S.μ S.tame j).Phi t (S.μ (j + 1))
      (((typeFrame S.ϖ (stdOrd (Fin κ) t (j + 1) c H1)).coords
        (typeFrame S.ϖ (stdOrd (Fin κ) t j (c + 1) H2)) z).submatrix (ixSucc _ t j) id) := fun _ => rfl
  split_ifs with hw
  · rw [hPhi, hPhi, coords_add, Matrix.submatrix_add, Pi.add_apply, Pi.add_apply]
    refine (S.P.iter t S.μ S.tame j).Phi_add (S.tame _) _ fun a b => ?_
    rw [submatrix_apply, coords_typeFrame_apply, of_apply]
    split_ifs with hb
    · rw [hb]
      rcases stdOrd (Fin κ) t (j + 1) c H1 (ixSucc _ t j a) with r | r
      · simpa [mul_comm] using hw r
      · simp
    · simp
  · by_contra h
    rw [← Ne, hPhi, TypeDatum.Phi_ne_zero_iff] at h
    obtain ⟨⟨g, hg, e⟩, hb⟩ := h
    refine hw fun r => ?_
    obtain ⟨a, ha⟩ := ((ixSucc _ t j).trans (stdOrd (Fin κ) t (j + 1) c H1)).surjective (.inl r)
    simp only [Equiv.trans_apply] at ha
    have hq : q.succ.val < s + 1 := by have := q.succ.2; omega
    have hcol : stdOrd (Fin κ) t j (c + 1) H2 (.inl (.inr ⟨q.succ.val, hq⟩)) = .inr q.succ :=
      standardOrderExtendedBasis_apply_low_block (Fin κ) t j (c + 1) H2 q.succ
    have key : (((typeFrame S.ϖ (stdOrd (Fin κ) t (j + 1) c H1)).coords
        (typeFrame S.ϖ (stdOrd (Fin κ) t j (c + 1) H2))
        (x + Matrix.of fun r s' => if s' = Sum.inr q.succ then Sum.elim w 0 r else 0)).submatrix (ixSucc _ t j) id)
        a (.inl (.inr ⟨q.succ.val, hq⟩)) = ((S.ϖ ^ (q.val + 2) : kˣ) : k) * w r := by
      rw [submatrix_apply, coords_typeFrame_apply, id, ha, hcol]
      simp [hx, mul_comm]
    rw [← key]
    rcases a with a | a
    · have hne : ¬ FreeIx S.ρ a (.inl (.inr ⟨q.succ.val, hq⟩)) ∧ a ≠ .inl (.inr ⟨q.succ.val, hq⟩) := by
        rcases a with (a | a) | a
        · simp only [FreeIx, FreeTop, Fin.val_succ]
          exact ⟨by omega, by simp⟩
        · have hac : c ≤ a.val := by
            by_contra hlt
            have := standardOrderExtendedBasis_apply_low_block (Fin κ) t (j + 1) c H1 ⟨a.val, by omega⟩
            exact Sum.inr_ne_inl (this.symm.trans ha)
          simp only [FreeIx, FreeTop, Fin.lt_def, Fin.val_succ, ne_eq, Sum.inl.injEq, Sum.inr.injEq, Fin.ext_iff]
          omega
        · simp [FreeIx]
      have := ((hP j g).1 hg).2 a _ hne.1
      rw [e, Matrix.one_apply_ne hne.2, sub_zero] at this
      exact this
    · exact hb a _

end GlobalTheory.SymChain.ExchangeCol
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixBlockColumnVanishingStepStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_block_column_vanishing_step : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t → ∀ (j c : ℕ) (H : j + c = s) (q : Fin c), q.val + 1 ≤ S.ρ → q.val + 2 ≤ c → ∀ (x : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin c) (XIx (Fin κ) t j ⊕ Fin (c + 1)) k), (∀ r, x (Sum.inl r) (Sum.inr q.succ) = 0) → ∀ w : XIx (Fin κ) t (j + 1) → k, (S.T t).Phi j c H (x + Matrix.of fun r s' => if s' = Sum.inr q.succ then Sum.elim w 0 r else 0) = if ∀ r, valuation k (((S.ϖ ^ (q.val + 2) : kˣ) : k) * w r) < 1 then (S.T t).Phi j c H x else 0 := by
  first | exact @GlobalTheory.SymChain.ExchangeCol.phi_add_col | exact GlobalTheory.SymChain.ExchangeCol.phi_add_col | (intros; apply GlobalTheory.SymChain.ExchangeCol.phi_add_col <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralBlockIndicator
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralBlockIndicator
open MeasureTheory Classical

namespace GlobalTheory.BlockFubini

theorem integral_block_indicator (k : Type) [MeasurableSpace k] [Zero k] (ν : Measure k) [SigmaFinite ν] (I : Type) [Fintype I] (P Q R : I → Prop) [DecidablePred P] [DecidablePred Q] [DecidablePred R] (hR : ∀ i, R i ↔ P i ∧ ¬ Q i) (hQ : ∀ i, Q i → P i) (s : Set k) (hs : MeasurableSet s) (_hν : ν s ≠ ⊤) (G : (I → k) → ℂ) (hG : ∀ m : I → k, G m = (if ∀ i, Q i → m i ∈ s then (1 : ℂ) else 0) * G (fun i => if Q i then 0 else m i)) : ∫ e : {i // P i} → k, G (fun i => if h : P i then e ⟨i, h⟩ else 0) ∂(Measure.pi fun _ => ν) = (((ν s).toReal ^ Fintype.card {i // Q i} : ℝ) : ℂ) * ∫ e : {i // R i} → k, G (fun i => if h : R i then e ⟨i, h⟩ else 0) ∂(Measure.pi fun _ => ν) := by
  let σ : {i // Q i} ⊕ {i // R i} ≃ {i // P i} :=
    { toFun := Sum.elim (fun a => ⟨a.1, hQ _ a.2⟩) (fun a => ⟨a.1, ((hR _).1 a.2).1⟩)
      invFun := fun a => if h : Q a.1 then Sum.inl ⟨a.1, h⟩ else Sum.inr ⟨a.1, (hR _).2 ⟨a.2, h⟩⟩
      left_inv := by
        rintro (a | a)
        · simp [a.2]
        · simp [((hR _).1 a.2).2]
      right_inv := by
        intro a
        by_cases h : Q a.1 <;> simp [h] }
  have h1 := measurePreserving_piCongrLeft (α := fun _ : {i // P i} => k) (fun _ => ν) σ
  have h2 := measurePreserving_sumPiEquivProdPi_symm (X := fun _ : {i // Q i} ⊕ {i // R i} => k) (fun _ => ν)
  have h3 := h1.comp h2
  rw [← h3.integral_comp ((MeasurableEquiv.measurableEmbedding _).comp (MeasurableEquiv.measurableEmbedding _))]
  have key : ∀ z : ({i // Q i} → k) × ({i // R i} → k),
      G (fun i => if h : P i then ((MeasurableEquiv.piCongrLeft (fun _ : {i // P i} => k) σ) ∘ (MeasurableEquiv.sumPiEquivProdPi (fun _ : {i // Q i} ⊕ {i // R i} => k)).symm) z ⟨i, h⟩ else 0)
      = (Set.pi Set.univ (fun _ : {i // Q i} => s)).indicator (fun _ => (1:ℂ)) z.1 * G (fun i => if h : R i then z.2 ⟨i, h⟩ else 0) := by
    intro z
    set E := ((MeasurableEquiv.piCongrLeft (fun _ : {i // P i} => k) σ) ∘ (MeasurableEquiv.sumPiEquivProdPi (fun _ : {i // Q i} ⊕ {i // R i} => k)).symm) z with hE
    have e0 : ∀ a, E (σ a) = Sum.elim z.1 z.2 a := by
      intro a
      rw [hE]
      simp only [Function.comp_apply]
      rw [MeasurableEquiv.piCongrLeft_apply_apply]
      cases a <;> rfl
    have e1 : ∀ i (h : Q i), E ⟨i, hQ i h⟩ = z.1 ⟨i, h⟩ := fun i h => e0 (Sum.inl ⟨i, h⟩)
    have e2 : ∀ i (h : R i), E ⟨i, ((hR i).1 h).1⟩ = z.2 ⟨i, h⟩ := fun i h => e0 (Sum.inr ⟨i, h⟩)
    rw [hG]
    congr 1
    · rw [Set.indicator_apply]
      congr 1
      apply propext
      simp only [Set.mem_pi, Set.mem_univ, forall_true_left]
      constructor
      · intro h a
        have := h a.1 a.2
        rwa [dif_pos (hQ _ a.2), e1 _ a.2] at this
      · intro h i hi
        rw [dif_pos (hQ _ hi), e1 _ hi]
        exact h _
    · congr 1
      funext i
      by_cases hq : Q i
      · have : ¬ R i := fun h => ((hR i).1 h).2 hq
        simp [hq, this]
      · by_cases hp : P i
        · have : R i := (hR i).2 ⟨hp, hq⟩
          simp only [hq, if_false, dif_pos hp, dif_pos this]
          exact e2 i this
        · have : ¬ R i := fun h => hp ((hR i).1 h).1
          simp [hq, hp, this]
  simp_rw [key]
  rw [integral_prod_mul (fun x => (Set.pi Set.univ (fun _ : {i // Q i} => s)).indicator (fun _ => (1:ℂ)) x) (fun y : {i // R i} → k => G (fun i => if h : R i then y ⟨i, h⟩ else 0))]
  congr 1
  rw [integral_indicator_const _ (MeasurableSet.univ_pi fun _ => hs)]
  simp [Measure.real, Measure.pi_pi]

end GlobalTheory.BlockFubini
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralBlockIndicatorStatement
open MeasureTheory Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_pi_block_indicator_eq_pow_mul : ∀ (k : Type) [MeasurableSpace k] [Zero k] (ν : Measure k) [SigmaFinite ν] (I : Type) [Fintype I] (P Q R : I → Prop) [DecidablePred P] [DecidablePred Q] [DecidablePred R], (∀ i, R i ↔ P i ∧ ¬ Q i) → (∀ i, Q i → P i) → ∀ (s : Set k), MeasurableSet s → ν s ≠ ⊤ → ∀ (G : (I → k) → ℂ), (∀ m : I → k, G m = (if ∀ i, Q i → m i ∈ s then (1 : ℂ) else 0) * G (fun i => if Q i then 0 else m i)) → ∫ e : {i // P i} → k, G (fun i => if h : P i then e ⟨i, h⟩ else 0) ∂(Measure.pi fun _ => ν) = (((ν s).toReal ^ Fintype.card {i // Q i} : ℝ) : ℂ) * ∫ e : {i // R i} → k, G (fun i => if h : R i then e ⟨i, h⟩ else 0) ∂(Measure.pi fun _ => ν) := by
  first | exact @GlobalTheory.BlockFubini.integral_block_indicator | exact GlobalTheory.BlockFubini.integral_block_indicator | (intros; apply GlobalTheory.BlockFubini.integral_block_indicator <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainUnfoldedPositionExchange
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.SymChain.ExchangeProof

section Step
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_inv_mul_le_one (a : kˣ) (z : k) :
    valuation k (((a⁻¹ : kˣ) : k) * z) ≤ 1 ↔ valuation k z ≤ valuation k (a : k) := by
  have : 0 < valuation k (a : k) := by simp [zero_lt_iff]
  rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀, inv_mul_le_one₀ this]

variable [MeasurableSpace k] [BorelSpace k]


open Classical in
theorem opE_step (ν : Measure k) (hν : IsUnitVol ν) {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t]
    [DecidableEq t] (hP : S.Pattern t) (j c : ℕ) (H : j + c = s) (q : Fin c) (hq : q.val + 1 ≤ S.ρ)
    (hqc : q.val + 2 ≤ c) : ∃ C : ℝ, 0 < C ∧
      opE S.ψ ν (q.val + 2) ((S.T t).Phi j c H) = (C : ℂ) • opE S.ψ ν (q.val + 1) ((S.T t).Phi j c H) := by
  haveI := hν.1
  have := secondCountable k
  have := t2Space k
  set Φ := (S.T t).Phi j c H with hΦ
  let I := (XIx (Fin κ) t (j + 1) ⊕ Fin c) × (XIx (Fin κ) t j ⊕ Fin (c + 1))
  let A : I → Prop := fun i => i.1 = Sum.inr q ∧ i.2.isLeft = true
  let B : I → Prop := fun i => i.2 = Sum.inr q.succ ∧ i.1.isLeft = true
  let R : I → Prop := fun i => Free (q.val + 1) i ∧ ¬ B i
  let a : kˣ := S.ϖ ^ (q.val + 1)
  let b : kˣ := S.ϖ ^ (q.val + 2)
  let sA : Set k := cball a
  let sB : Set k := (fun z => (b : k) * z) ⁻¹' {z | valuation k z < 1}
  have oB : IsOpen sB := IsOpen.preimage (by fun_prop) (by simpa using (valuation k).isOpen_ball 1)
  have sBc : sB ⊆ cball b⁻¹ := fun z hz => by
    have hz : valuation k ((b : k) * z) < 1 := hz
    have : 0 < valuation k (b : k) := by simp [zero_lt_iff]
    rw [map_mul] at hz
    change valuation k z ≤ valuation k ((b⁻¹ : kˣ) : k)
    rw [Units.val_inv_eq_inv_val, map_inv₀]
    have h1 : valuation k z = (valuation k (b : k))⁻¹ * (valuation k (b : k) * valuation k z) := by
      rw [← mul_assoc, inv_mul_cancel₀ this.ne', one_mul]
    rw [h1]; exact mul_le_of_le_one_right' hz.le
  have mA : MeasurableSet sA := (isOpen_cball a).measurableSet
  have mB : MeasurableSet sB := oB.measurableSet
  have fA : ν sA ≠ ⊤ := (isCompact_cball a).measure_lt_top.ne
  have fB : ν sB ≠ ⊤ := ((isCompact_cball b⁻¹).measure_lt_top.trans_le' (measure_mono sBc)).ne
  have pA : 0 < ν sA := (isOpen_cball a).measure_pos ν ⟨0, by simp [sA, cball]⟩
  have pB : 0 < ν sB := oB.measure_pos ν ⟨0, by simp [sB]⟩
  let G : Matrix (XIx (Fin κ) t (j + 1)) (XIx (Fin κ) t j) k → (I → k) → ℂ := fun x₀ m =>
    Φ (basePt c x₀ + Matrix.of fun r s' => m (r, s')) * (S.ψ (-ch (basePt c x₀ + Matrix.of fun r s' => m (r, s'))) : ℂ)
  have hR2 : ∀ i, R i ↔ Free (q.val + 2) i ∧ ¬ A i := by
    rintro ⟨r | r, s' | s'⟩ <;> simp [R, A, B, Free, Fin.ext_iff] <;> omega
  have hR1 : ∀ i, R i ↔ Free (q.val + 1) i ∧ ¬ B i := fun i => Iff.rfl
  have hA : ∀ i, A i → Free (q.val + 2) i := by
    rintro ⟨r | r, s' | s'⟩ h <;> simp_all [A, Free]
  have hB : ∀ i, B i → Free (q.val + 1) i := by
    rintro ⟨r | r, s' | s'⟩ h <;> simp_all [B, Free]
  have gA : ∀ x₀ (m : I → k), G x₀ m = (if ∀ i, A i → m i ∈ sA then (1 : ℂ) else 0) * G x₀ (fun i => if A i then 0 else m i) := by
    intro x₀ m
    let v : XIx (Fin κ) t j → k := fun s' => m (Sum.inr q, Sum.inl s')
    have hx : (basePt c x₀ + Matrix.of fun r s' => m (r, s')) = (basePt c x₀ + Matrix.of fun r s' =>
        (if A (r, s') then 0 else m (r, s'))) + Matrix.of fun r s' => if r = Sum.inr q then Sum.elim v 0 s' else 0 := by
      ext (r | r) (s' | s')
      · simp [A]
      · simp [A]
      · by_cases h : r = q
        · subst h; simp [A, v, basePt]
        · simp [A, h]
      · simp [A]
    have hch : ch (basePt c x₀ + Matrix.of fun r s' => m (r, s')) =
        ch (basePt c x₀ + Matrix.of fun r s' => (if A (r, s') then 0 else m (r, s'))) := by
      simp [ch, A]
    have row0 : ∀ s', (basePt c x₀ + Matrix.of fun r s' => (if A (r, s') then 0 else m (r, s'))) (Sum.inr q) (Sum.inl s') = 0 := by
      intro s'; simp [basePt, A]
    have hiff : (∀ s', valuation k ((((S.ϖ ^ (q.val + 1))⁻¹ : kˣ) : k) * v s') ≤ 1) ↔ ∀ i, A i → m i ∈ sA := by
      constructor
      · rintro h ⟨r, s' | s'⟩ ⟨rfl, hs⟩
        · exact (val_inv_mul_le_one a _).1 (h s')
        · simp at hs
      · intro h s'; exact (val_inv_mul_le_one a _).2 (h (Sum.inr q, Sum.inl s') ⟨rfl, rfl⟩)
    simp only [G]
    rw [hch, hx, hΦ, GlobalTheory.T.symLevelChain_testFunction_add_row k s κ S t hP j c H q hq _ row0 v]
    by_cases hc : ∀ i, A i → m i ∈ sA
    · rw [if_pos (hiff.2 hc), if_pos hc, one_mul]
    · rw [if_neg (fun h => hc (hiff.1 h)), if_neg hc, zero_mul, zero_mul]
  have gB : ∀ x₀ (m : I → k), G x₀ m = (if ∀ i, B i → m i ∈ sB then (1 : ℂ) else 0) * G x₀ (fun i => if B i then 0 else m i) := by
    intro x₀ m
    let w : XIx (Fin κ) t (j + 1) → k := fun r => m (Sum.inl r, Sum.inr q.succ)
    have hx : (basePt c x₀ + Matrix.of fun r s' => m (r, s')) = (basePt c x₀ + Matrix.of fun r s' =>
        (if B (r, s') then 0 else m (r, s'))) + Matrix.of fun r s' => if s' = Sum.inr q.succ then Sum.elim w 0 r else 0 := by
      ext (r | r) (s' | s')
      · simp [B]
      · by_cases h : s' = q.succ
        · subst h; simp [B, w, basePt]
        · simp [B, h]
      · simp [B]
      · simp [B]
    have hch : ch (basePt c x₀ + Matrix.of fun r s' => m (r, s')) =
        ch (basePt c x₀ + Matrix.of fun r s' => (if B (r, s') then 0 else m (r, s'))) := by
      simp [ch, B]
    have col0 : ∀ r, (basePt c x₀ + Matrix.of fun r s' => (if B (r, s') then 0 else m (r, s'))) (Sum.inl r) (Sum.inr q.succ) = 0 := by
      intro r; simp [basePt, B]
    have hiff : (∀ r, valuation k (((S.ϖ ^ (q.val + 2) : kˣ) : k) * w r) < 1) ↔ ∀ i, B i → m i ∈ sB := by
      constructor
      · rintro h ⟨r | r, s'⟩ ⟨rfl, hs⟩
        · exact h r
        · simp at hs
      · intro h r; exact h (Sum.inl r, Sum.inr q.succ) ⟨rfl, rfl⟩
    simp only [G]
    rw [hch, hx, hΦ, GlobalTheory.T.matrix_block_column_vanishing_step k s κ S t hP j c H q hq hqc _ col0 w]
    by_cases hc : ∀ i, B i → m i ∈ sB
    · rw [if_pos (hiff.2 hc), if_pos hc, one_mul]
    · rw [if_neg (fun h => hc (hiff.1 h)), if_neg hc, zero_mul, zero_mul]
  have e2 : ∀ x₀, opE S.ψ ν (q.val + 2) Φ x₀ = (((ν sA).toReal ^ Fintype.card {i // A i} : ℝ) : ℂ) *
      ∫ e : {i // R i} → k, G x₀ (fun i => if h : R i then e ⟨i, h⟩ else 0) ∂(Measure.pi fun _ => ν) :=
    fun x₀ => GlobalTheory.T.integral_pi_block_indicator_eq_pow_mul k ν I (Free (q.val + 2)) A R hR2 hA sA mA fA (G x₀) (gA x₀)
  have e1 : ∀ x₀, opE S.ψ ν (q.val + 1) Φ x₀ = (((ν sB).toReal ^ Fintype.card {i // B i} : ℝ) : ℂ) *
      ∫ e : {i // R i} → k, G x₀ (fun i => if h : R i then e ⟨i, h⟩ else 0) ∂(Measure.pi fun _ => ν) :=
    fun x₀ => GlobalTheory.T.integral_pi_block_indicator_eq_pow_mul k ν I (Free (q.val + 1)) B R hR1 hB sB mB fB (G x₀) (gB x₀)
  have tA : 0 < (ν sA).toReal := ENNReal.toReal_pos pA.ne' fA
  have tB : 0 < (ν sB).toReal := ENNReal.toReal_pos pB.ne' fB
  refine ⟨(ν sA).toReal ^ Fintype.card {i // A i} / (ν sB).toReal ^ Fintype.card {i // B i},
    div_pos (pow_pos tA _) (pow_pos tB _), funext fun x₀ => ?_⟩
  rw [Pi.smul_apply, e2, e1, smul_eq_mul, ← mul_assoc, ← Complex.ofReal_mul, div_mul_cancel₀ _ (pow_pos tB _).ne']

end Step

theorem exchangeAt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type)
    [Fintype t] [DecidableEq t], S.Pattern t → S.ExchangeAt t ν := by
  intro k _ _ _ _ _ _ ν hν s κ S t _ _ hP j c H p hp1
  induction p, hp1 using Nat.le_induction with
  | base => intro _ _; exact ⟨1, one_pos, by simp⟩
  | succ p hp ih =>
    intro hpc hpρ
    obtain ⟨C, hC, e⟩ := ih (by omega) (by omega)
    obtain ⟨C', hC', e'⟩ := opE_step ν hν S t hP j c H ⟨p - 1, by omega⟩ (by simp; omega) (by simp; omega)
    have h2 : (p - 1) + 2 = p + 1 := by omega
    have h1 : (p - 1) + 1 = p := by omega
    simp only [h1, h2] at e'
    refine ⟨C' * C, mul_pos hC' hC, ?_⟩
    rw [e', e, smul_smul, Complex.ofReal_mul]

end GlobalTheory.SymChain.ExchangeProof
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainUnfoldedPositionExchangeStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricLevelChain_unfolded_position_exchange : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t → S.ExchangeAt t ν := by
  first | exact @GlobalTheory.SymChain.ExchangeProof.exchangeAt | exact GlobalTheory.SymChain.ExchangeProof.exchangeAt | (intros; apply GlobalTheory.SymChain.ExchangeProof.exchangeAt <;> assumption)
end
