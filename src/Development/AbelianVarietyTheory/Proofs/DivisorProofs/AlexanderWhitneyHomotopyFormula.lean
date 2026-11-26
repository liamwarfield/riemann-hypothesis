module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreMemInducedSpace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalNumberZeroOfHorizontal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BisimplicialOperatorChainsAcyclicPositiveDegree
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BisimplicialOperatorChainsAcyclicPositiveDegree
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ

noncomputable section
namespace GlobalTheory.EZ.Acyc
open GlobalTheory.EZ.AWChain

def cone {a p : ℕ} (α : SimplexCategory.mk p ⟶ SimplexCategory.mk a) :
    SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk a :=
  SimplexCategory.mkHom ⟨fun j => Fin.cases 0 (fun i => α.toOrderHom i) j, by
    intro i j h
    induction i using Fin.cases with
    | zero => exact Fin.zero_le _
    | succ i =>
      induction j using Fin.cases with
      | zero => exact absurd h (by simp [Fin.le_def])
      | succ j => exact α.toOrderHom.monotone (Fin.succ_le_succ_iff.mp h)⟩

theorem cone_zero {a p : ℕ} (α : SimplexCategory.mk p ⟶ SimplexCategory.mk a) :
    (cone α).toOrderHom 0 = 0 := rfl
theorem cone_succ {a p : ℕ} (α : SimplexCategory.mk p ⟶ SimplexCategory.mk a) (j : Fin (p + 1)) :
    (cone α).toOrderHom j.succ = α.toOrderHom j := rfl

abbrev Ix (a b p q : ℕ) : Type :=
  ((op (SimplexCategory.mk a), op (SimplexCategory.mk b)) : SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ) ⟶
    (op (SimplexCategory.mk p), op (SimplexCategory.mk q))

def c1 {a b p q : ℕ} (g : Ix a b p q) : Ix a b (p + 1) q := ((cone g.1.unop).op, g.2)

def c2 {a b p q : ℕ} (g : Ix a b p q) : Ix a b 0 (q + 1) := ((idc a 0).op, (cone g.2.unop).op)

def H1 {a b p q : ℕ} : (bo a b ⟶ bo p q) →+ (bo a b ⟶ bo (p + 1) q) :=
  Finsupp.mapDomain.addMonoidHom (c1 (a := a) (b := b) (p := p) (q := q))

def H2 {a b p q : ℕ} : (bo a b ⟶ bo p q) →+ (bo a b ⟶ bo 0 (q + 1)) :=
  Finsupp.mapDomain.addMonoidHom (c2 (a := a) (b := b) (p := p) (q := q))

theorem bisimplicialChainConeFirstIndex_operatorOfSimplexMaps {a b p q : ℕ} (α : SimplexCategory.mk p ⟶ SimplexCategory.mk a)
    (β : SimplexCategory.mk q ⟶ SimplexCategory.mk b) : H1 (bop α β) = bop (cone α) β := by
  change Finsupp.mapDomain c1 (Finsupp.single ((α.op, β.op) : Ix a b p q) (1 : ℤ)) =
    Finsupp.single (((cone α).op, β.op) : Ix a b (p + 1) q) (1 : ℤ)
  rw [Finsupp.mapDomain_single]
  rfl

theorem bisimplicialChainConeSecondIndex_operatorOfSimplexMaps {a b p q : ℕ} (α : SimplexCategory.mk p ⟶ SimplexCategory.mk a)
    (β : SimplexCategory.mk q ⟶ SimplexCategory.mk b) : H2 (bop α β) = bop (idc a 0) (cone β) := by
  change Finsupp.mapDomain c2 (Finsupp.single ((α.op, β.op) : Ix a b p q) (1 : ℤ)) =
    Finsupp.single (((idc a 0).op, (cone β).op) : Ix a b 0 (q + 1)) (1 : ℤ)
  rw [Finsupp.mapDomain_single]
  rfl

theorem hom_induct {a b p q : ℕ} (P : (bo a b ⟶ bo p q) → Prop) (h0 : P 0)
    (hadd : ∀ f g, P f → P g → P (f + g)) (hsm : ∀ (r : ℤ) f, P f → P (r • f))
    (hb : ∀ α β, P (bop α β)) (f : bo a b ⟶ bo p q) : P f := by
  induction f using Finsupp.induction_linear with
  | zero => exact h0
  | add f g hf hg => exact hadd _ _ hf hg
  | single g r =>
    have e : (Finsupp.single g r : bo a b ⟶ bo p q) = r • bop g.1.unop g.2.unop := by
      change Finsupp.single g r = r • Finsupp.single (g : Ix a b p q) (1 : ℤ)
      rw [Finsupp.smul_single_one]
    rw [e]
    exact hsm _ _ (hb _ _)

theorem idc_self' (n : ℕ) : idc n n = 𝟙 _ := by
  apply hom_ext'; intro j; have hj := j.isLt
  rw [idc_apply]; change min n (j : ℕ) = j; omega

theorem faceFun_succ (i j : ℕ) : faceFun (i + 1) (j + 1) = faceFun i j + 1 := by
  unfold faceFun; split_ifs <;> omega

theorem simplexClampedFaceHom_zero_comp_simplexConeMap {a p : ℕ} (α : SimplexCategory.mk p ⟶ SimplexCategory.mk a) :
    fc (p + 1) p 0 ≫ cone α = α := by
  apply hom_ext'; intro j
  rw [comp_apply']
  have : (fc (p + 1) p 0).toOrderHom j = j.succ := by
    apply Fin.ext; rw [fc_apply, faceFun_ge (Nat.zero_le _)]; simp; omega
  rw [this, cone_succ]

theorem faceSucc_cone {a p : ℕ} (α : SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk a) (i : ℕ) :
    fc (p + 1 + 1) (p + 1) (i + 1) ≫ cone α = cone (fc (p + 1) p i ≫ α) := by
  apply hom_ext'; intro j
  rw [comp_apply']
  induction j using Fin.cases with
  | zero =>
    have : (fc (p + 1 + 1) (p + 1) (i + 1)).toOrderHom 0 = 0 := by
      apply Fin.ext; rw [fc_apply, faceFun_lt (by simp)]; simp
    rw [this, cone_zero, cone_zero]
  | succ j =>
    have hj := j.isLt
    have : (fc (p + 1 + 1) (p + 1) (i + 1)).toOrderHom j.succ = ((fc (p + 1) p i).toOrderHom j).succ := by
      apply Fin.ext
      rw [Fin.val_succ, fc_apply, fc_apply, Fin.val_succ, faceFun_succ]
      have : faceFun i j ≤ j + 1 := by unfold faceFun; split_ifs <;> omega
      omega
    rw [this, cone_succ, cone_succ, comp_apply']

theorem simplexClampedFaceHom_one_comp_simplexConeMap_zero {a : ℕ} (α : SimplexCategory.mk 0 ⟶ SimplexCategory.mk a) :
    fc 1 0 1 ≫ cone α = idc a 0 := by
  apply hom_ext'; intro j
  have hj : (j : ℕ) = 0 := by have := j.isLt; omega
  have e : j = 0 := Fin.ext hj
  subst e
  rw [comp_apply']
  have : (fc 1 0 1).toOrderHom 0 = 0 := by
    apply Fin.ext; rw [fc_apply, faceFun_lt (by simp)]; simp
  rw [this, cone_zero, idc_apply]; simp

theorem face_zero_cone_identity {a : ℕ} (α : SimplexCategory.mk 0 ⟶ SimplexCategory.mk a) : fc 1 0 0 ≫ cone α = α :=
  simplexClampedFaceHom_zero_comp_simplexConeMap (p := 0) α

theorem bisimplicialTotalDifferentialOperator_one_zero_eq_sum (q : ℕ) : dT 1 q 0 q = ∑ i ∈ Finset.range (0 + 1 + 1), ((-1 : ℤ) ^ i) • bop (fc 1 0 i) (idc q q) :=
  dT_h 0 q

theorem idA {a b p q : ℕ} (f : bo a b ⟶ bo (p + 1) q) :
    H1 f ≫ dT (p + 1 + 1) q (p + 1) q = f - H1 (f ≫ dT (p + 1) q p q) := by
  refine hom_induct (fun f => H1 f ≫ dT (p + 1 + 1) q (p + 1) q = f - H1 (f ≫ dT (p + 1) q p q)) ?_ ?_ ?_ ?_ f
  · simp
  · intro f g hf hg; simp only [map_add (f := _), Preadditive.add_comp, Preadditive.add_comp, hf, hg]; abel
  · intro r f hf; simp only [map_zsmul, Preadditive.zsmul_comp, hf, smul_sub]
  · intro α β
    rw [bisimplicialChainConeFirstIndex_operatorOfSimplexMaps, dT_h (p + 1) q, dT_h p q]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Preadditive.comp_sum, Preadditive.comp_zsmul, bop_comp, map_sum, map_zsmul, bisimplicialChainConeFirstIndex_operatorOfSimplexMaps]
    rw [Finset.sum_range_succ' _ (p + 1 + 1)]
    simp only [simplexClampedFaceHom_zero_comp_simplexConeMap, faceSucc_cone, pow_succ, mul_neg_one, neg_smul, Finset.sum_neg_distrib, pow_zero,
      one_smul, idc_self', Category.id_comp]
    abel

theorem idB {a b p q : ℕ} (f : bo a b ⟶ bo p (q + 1)) :
    H1 f ≫ dT (p + 1) (q + 1) (p + 1) q = -H1 (f ≫ dT p (q + 1) p q) := by
  refine hom_induct (fun f => H1 f ≫ dT (p + 1) (q + 1) (p + 1) q = -H1 (f ≫ dT p (q + 1) p q)) ?_ ?_ ?_ ?_ f
  · simp
  · intro f g hf hg; simp only [map_add (f := _), Preadditive.add_comp, hf, hg, neg_add]
  · intro r f hf; simp only [map_zsmul, Preadditive.zsmul_comp, hf, smul_neg]
  · intro α β
    rw [bisimplicialChainConeFirstIndex_operatorOfSimplexMaps, dT_v (p + 1) q, dT_v p q]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Preadditive.comp_sum, Preadditive.comp_zsmul, Preadditive.comp_neg, bop_comp, map_sum, map_zsmul,
      bisimplicialChainConeFirstIndex_operatorOfSimplexMaps, idc_self', Category.id_comp, pow_succ, mul_neg_one, neg_smul]

theorem idC {a b q : ℕ} (f : bo a b ⟶ bo 0 (q + 1)) :
    H1 f ≫ dT 1 (q + 1) 0 (q + 1) + H2 f ≫ dT 0 (q + 1 + 1) 0 (q + 1) = f - H2 (f ≫ dT 0 (q + 1) 0 q) := by
  refine hom_induct (fun f => H1 f ≫ dT 1 (q + 1) 0 (q + 1) + H2 f ≫ dT 0 (q + 1 + 1) 0 (q + 1) =
    f - H2 (f ≫ dT 0 (q + 1) 0 q)) ?_ ?_ ?_ ?_ f
  · simp
  · intro f g hf hg
    simp only [map_add (f := _), Preadditive.add_comp] at hf hg ⊢
    rw [show H1 f ≫ dT 1 (q + 1) 0 (q + 1) + H1 g ≫ dT 1 (q + 1) 0 (q + 1) +
      (H2 f ≫ dT 0 (q + 1 + 1) 0 (q + 1) + H2 g ≫ dT 0 (q + 1 + 1) 0 (q + 1)) =
      (H1 f ≫ dT 1 (q + 1) 0 (q + 1) + H2 f ≫ dT 0 (q + 1 + 1) 0 (q + 1)) +
      (H1 g ≫ dT 1 (q + 1) 0 (q + 1) + H2 g ≫ dT 0 (q + 1 + 1) 0 (q + 1)) by abel, hf, hg]
    abel
  · intro r f hf
    simp only [map_zsmul, Preadditive.zsmul_comp, ← smul_add, hf, smul_sub]
  · intro α β
    rw [bisimplicialChainConeFirstIndex_operatorOfSimplexMaps, bisimplicialChainConeSecondIndex_operatorOfSimplexMaps, bisimplicialTotalDifferentialOperator_one_zero_eq_sum, dT_v 0 (q + 1), dT_v 0 q]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Preadditive.comp_sum, Preadditive.comp_zsmul, bop_comp, map_sum, map_zsmul, bisimplicialChainConeSecondIndex_operatorOfSimplexMaps]
    rw [Finset.sum_range_succ' _ (q + 1 + 1)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, face_zero_cone_identity, simplexClampedFaceHom_one_comp_simplexConeMap_zero, simplexClampedFaceHom_zero_comp_simplexConeMap,
      faceSucc_cone, pow_succ, mul_neg_one, neg_smul, Finset.sum_neg_distrib, pow_zero, one_smul, idc_self',
      Category.id_comp, smul_neg]
    abel

theorem idD {a b q : ℕ} (f : bo a b ⟶ bo 1 q) : H2 (f ≫ dT 1 q 0 q) = 0 := by
  refine hom_induct (fun f => H2 (f ≫ dT 1 q 0 q) = 0) ?_ ?_ ?_ ?_ f
  · simp
  · intro f g hf hg; simp only [map_add (f := _), Preadditive.add_comp, hf, hg, add_zero]
  · intro r f hf; simp only [map_zsmul, Preadditive.zsmul_comp, hf, smul_zero]
  · intro α β
    rw [bisimplicialTotalDifferentialOperator_one_zero_eq_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Preadditive.comp_sum, Preadditive.comp_zsmul, bop_comp, map_sum, map_zsmul, bisimplicialChainConeSecondIndex_operatorOfSimplexMaps,
      Finset.sum_range_succ]

theorem sum_dT {a b : ℕ} (u : ∀ a' b' : ℕ, bo a b ⟶ bo a' b') (c d : ℕ) :
    ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (c + d + 1), u x.1 x.2 ≫ dT x.1 x.2 c d =
      u (c + 1) d ≫ dT (c + 1) d c d + u c (d + 1) ≫ dT c (d + 1) c d := by
  rw [Finset.sum_eq_add (c + 1, d) (c, d + 1) (by simp)]
  · rintro x hx ⟨h1, h2⟩
    rw [dT_zero, Limits.comp_zero]
    · rintro ⟨e1, e2⟩; exact h1 (Prod.ext e1 e2)
    · rintro ⟨e1, e2⟩; exact h2 (Prod.ext e1 e2)
  · intro h; exact absurd (by rw [Finset.HasAntidiagonal.mem_antidiagonal]; omega) h
  · intro h; exact absurd (by rw [Finset.HasAntidiagonal.mem_antidiagonal]; omega) h

def wfill {a b : ℕ} (z : ∀ a' b' : ℕ, bo a b ⟶ bo a' b') : ∀ a' b' : ℕ, bo a b ⟶ bo a' b'
  | 0, 0 => 0
  | 0, q + 1 => H2 (z 0 q)
  | p + 1, q => H1 (z p q)

end GlobalTheory.EZ.Acyc

namespace GlobalTheory.EZ
open GlobalTheory.EZ.Acyc

theorem totChains_acyclic : ∀ a b k : ℕ, 1 ≤ k → ∀ z : ∀ a' b' : ℕ, bo a b ⟶ bo a' b',
    (∀ c d : ℕ, c + d + 1 = k → ∑ x ∈ Finset.HasAntidiagonal.antidiagonal k, z x.1 x.2 ≫ dT x.1 x.2 c d = 0) →
    ∃ w : ∀ a' b' : ℕ, bo a b ⟶ bo a' b', ∀ c d : ℕ, c + d = k →
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (k + 1), w x.1 x.2 ≫ dT x.1 x.2 c d = z c d := by
  intro a b k hk z hz
  refine ⟨wfill z, fun c d hcd => ?_⟩
  subst hcd
  rw [sum_dT]
  have cyc : ∀ c' d', c' + d' + 1 = c + d →
      z (c' + 1) d' ≫ dT (c' + 1) d' c' d' + z c' (d' + 1) ≫ dT c' (d' + 1) c' d' = 0 := by
    intro c' d' h
    have := hz c' d' h
    rw [← h, sum_dT] at this
    exact this
  cases c with
  | succ p =>
    show H1 (z (p + 1) d) ≫ dT (p + 1 + 1) d (p + 1) d + H1 (z p (d + 1)) ≫ dT (p + 1) (d + 1) (p + 1) d = _
    have h2 : H1 (z (p + 1) d ≫ dT (p + 1) d p d) + H1 (z p (d + 1) ≫ dT p (d + 1) p d) = 0 := by
      rw [← map_add (f := _), cyc p d (by omega), map_zero]
    rw [idA, idB, ← sub_eq_add_neg, sub_sub, h2, sub_zero]
  | zero =>
    obtain ⟨q, rfl⟩ : ∃ q, d = q + 1 := ⟨d - 1, by omega⟩
    show H1 (z 0 (q + 1)) ≫ dT 1 (q + 1) 0 (q + 1) + H2 (z 0 (q + 1)) ≫ dT 0 (q + 1 + 1) 0 (q + 1) = _
    rw [idC]
    have h3 : z 0 (q + 1) ≫ dT 0 (q + 1) 0 q = -(z 1 q ≫ dT 1 q 0 q) := by
      have := cyc 0 q (by omega)
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact this
    rw [h3, map_neg, idD, neg_zero, sub_zero]

end GlobalTheory.EZ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BisimplicialOperatorChainsAcyclicPositiveDegreeStatement
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bisimplicialOperatorChains_acyclic_positiveDegree : ∀ a b k : ℕ, 1 ≤ k → ∀ z : ∀ a' b' : ℕ, bo a b ⟶ bo a' b', (∀ c d : ℕ, c + d + 1 = k → ∑ x ∈ Finset.HasAntidiagonal.antidiagonal k, z x.1 x.2 ≫ dT x.1 x.2 c d = 0) → ∃ w : ∀ a' b' : ℕ, bo a b ⟶ bo a' b', ∀ c d : ℕ, c + d = k → ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (k + 1), w x.1 x.2 ≫ dT x.1 x.2 c d = z c d := by
  first | (exact @GlobalTheory.EZ.totChains_acyclic) | (exact GlobalTheory.EZ.totChains_acyclic) | (intros; apply GlobalTheory.EZ.totChains_acyclic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DTCompDT
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DTCompDT
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ

noncomputable section

namespace GlobalTheory.EZ.TotSq

theorem bop_comp {n m p q r s : ℕ} (α : SimplexCategory.mk p ⟶ SimplexCategory.mk n)
    (β : SimplexCategory.mk q ⟶ SimplexCategory.mk m) (α' : SimplexCategory.mk r ⟶ SimplexCategory.mk p)
    (β' : SimplexCategory.mk s ⟶ SimplexCategory.mk q) :
    bop α β ≫ bop α' β' = bop (α' ≫ α) (β' ≫ β) := by
  have := Free.single_comp_single (R := ℤ) (C := SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ)
    (show (op (SimplexCategory.mk n), op (SimplexCategory.mk m)) ⟶
      (op (SimplexCategory.mk p), op (SimplexCategory.mk q)) from (α.op, β.op))
    (show (op (SimplexCategory.mk p), op (SimplexCategory.mk q)) ⟶
      (op (SimplexCategory.mk r), op (SimplexCategory.mk s)) from (α'.op, β'.op)) 1 1
  simp only [mul_one] at this
  exact this

theorem idc_self (n : ℕ) : idc n n = 𝟙 _ := by
  ext j
  have hj : (j : ℕ) < n + 1 := j.isLt
  simp only [idc, clampHom, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk]
  change min n (j : ℕ) = ((j : Fin (n + 1)) : ℕ)
  omega

theorem fc_comp_fc (n i j : ℕ) (hji : j < i) (hi : i ≤ n + 2) :
    fc (n + 1) n j ≫ fc (n + 2) (n + 1) i = fc (n + 1) n (i - 1) ≫ fc (n + 2) (n + 1) j := by
  ext k
  have hk : (k : ℕ) < n + 1 := k.isLt
  simp only [fc, clampHom, faceFun, SimplexCategory.mkHom, SimplexCategory.comp_toOrderHom,
    SimplexCategory.Hom.toOrderHom_mk, OrderHom.comp_coe, Function.comp_apply, OrderHom.coe_mk]
  split_ifs <;> omega

theorem alt_double_sum {M : Type*} [AddCommGroup M] (n : ℕ)
    (F : (SimplexCategory.mk n ⟶ SimplexCategory.mk (n + 2)) → M) :
    ∑ i ∈ Finset.range (n + 3), ∑ j ∈ Finset.range (n + 2),
      ((-1 : ℤ) ^ i * (-1) ^ j) • F (fc (n + 1) n j ≫ fc (n + 2) (n + 1) i) = 0 := by
  rw [← Finset.sum_product']
  refine Finset.sum_involution (fun x _ => if x.2 < x.1 then (x.2, x.1 - 1) else (x.2 + 1, x.1)) ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ h
    simp only [Finset.mem_product, Finset.mem_range] at h
    dsimp only
    split_ifs with hji
    · dsimp only
      rw [fc_comp_fc n i j hji (by omega), ← add_smul]
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      rw [show i' + 1 - 1 = i' by omega, pow_succ]
      ring_nf
      simp
    · dsimp only
      rw [fc_comp_fc n (j + 1) i (by omega) (by omega), show j + 1 - 1 = j by omega, ← add_smul, pow_succ]
      ring_nf
      simp
  · rintro ⟨i, j⟩ _ _
    dsimp only
    split_ifs <;> simp only [ne_eq, Prod.mk.injEq] <;> omega
  · rintro ⟨i, j⟩ h
    simp only [Finset.mem_product, Finset.mem_range] at h ⊢
    split_ifs <;> simp only <;> omega
  · rintro ⟨i, j⟩ _
    by_cases h : j < i
    · simp only [h, if_true]
      rw [if_neg (by omega)]
      simp only [Prod.mk.injEq, and_true, true_and]
      omega
    · simp only [h, if_false]
      rw [if_pos (by omega)]
      simp only [Prod.mk.injEq, and_true, true_and]
      omega

theorem dH_comp_dH (a b x y c d : ℕ) : dH a b x y ≫ dH x y c d = 0 := by
  unfold dH
  by_cases h1 : a = x + 1 ∧ b = y
  · by_cases h2 : x = c + 1 ∧ y = d
    · obtain ⟨rfl, rfl⟩ := h1
      obtain ⟨rfl, rfl⟩ := h2
      rw [if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, Preadditive.sum_comp]
      simp only [Preadditive.comp_sum, Preadditive.zsmul_comp, Preadditive.comp_zsmul, bop_comp, smul_smul]
      have := alt_double_sum c (fun α => bop α (idc b b ≫ idc b b))
      simpa only [mul_comm] using this
    · rw [if_neg h2, comp_zero]
  · rw [if_neg h1, zero_comp]

theorem dV_comp_dV (a b x y c d : ℕ) : dV a b x y ≫ dV x y c d = 0 := by
  unfold dV
  by_cases h1 : a = x ∧ b = y + 1
  · by_cases h2 : x = c ∧ y = d + 1
    · obtain ⟨rfl, rfl⟩ := h1
      obtain ⟨rfl, rfl⟩ := h2
      rw [if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, Preadditive.sum_comp]
      simp only [Preadditive.comp_sum, Preadditive.zsmul_comp, Preadditive.comp_zsmul, bop_comp, smul_smul]
      have := alt_double_sum d (fun β => bop (idc a a ≫ idc a a) β)
      simpa only [mul_comm] using this
    · rw [if_neg h2, comp_zero]
  · rw [if_neg h1, zero_comp]

theorem dH_comp_dV (c d : ℕ) :
    dH (c + 1) (d + 1) c (d + 1) ≫ dV c (d + 1) c d = dV (c + 1) (d + 1) (c + 1) d ≫ dH (c + 1) d c d := by
  unfold dH dV
  rw [if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩,
    Preadditive.sum_comp, Preadditive.sum_comp]
  simp only [Preadditive.comp_sum, Preadditive.zsmul_comp, Preadditive.comp_zsmul, bop_comp, smul_smul,
    idc_self, Category.id_comp, Category.comp_id]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]

theorem dT_comp_dT (a b c d k : ℕ) (hk : c + d = k) :
    ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (k + 1), dT a b x.1 x.2 ≫ dT x.1 x.2 c d = 0 := by
  subst hk
  have hsplit : ∀ x : ℕ × ℕ, dT a b x.1 x.2 ≫ dT x.1 x.2 c d =
      ((-1 : ℤ) ^ x.1) • (dH a b x.1 x.2 ≫ dV x.1 x.2 c d) +
        ((-1 : ℤ) ^ a) • (dV a b x.1 x.2 ≫ dH x.1 x.2 c d) := by
    intro x
    simp only [dT, Preadditive.add_comp, Preadditive.comp_add, Preadditive.zsmul_comp, Preadditive.comp_zsmul,
      dH_comp_dH, dV_comp_dV, smul_zero, zero_add, add_zero]
    rw [add_comm]
  simp_rw [hsplit, Finset.sum_add_distrib]
  have hm1 : (c, d + 1) ∈ Finset.HasAntidiagonal.antidiagonal (c + d + 1) := by
    rw [Finset.HasAntidiagonal.mem_antidiagonal]; omega
  have hm2 : (c + 1, d) ∈ Finset.HasAntidiagonal.antidiagonal (c + d + 1) := by
    rw [Finset.HasAntidiagonal.mem_antidiagonal]; omega
  rw [Finset.sum_eq_single_of_mem (c, d + 1) hm1 ?_, Finset.sum_eq_single_of_mem (c + 1, d) hm2 ?_]
  · dsimp only
    by_cases h : a = c + 1 ∧ b = d + 1
    · obtain ⟨rfl, rfl⟩ := h
      rw [dH_comp_dV c d, ← add_smul, pow_succ]
      simp
    · have e1 : dH a b c (d + 1) = 0 := by unfold dH; rw [if_neg h]
      have e2 : dV a b (c + 1) d = 0 := by unfold dV; rw [if_neg h]
      rw [e1, e2, zero_comp, zero_comp, smul_zero, smul_zero, add_zero]
  · rintro ⟨x1, x2⟩ _ hx
    have : dH x1 x2 c d = 0 := by
      unfold dH; rw [if_neg]; rintro ⟨rfl, rfl⟩; exact hx rfl
    dsimp only
    rw [this, comp_zero, smul_zero]
  · rintro ⟨x1, x2⟩ _ hx
    have : dV x1 x2 c d = 0 := by
      unfold dV; rw [if_neg]; rintro ⟨rfl, rfl⟩; exact hx rfl
    dsimp only
    rw [this, comp_zero, smul_zero]

theorem dT_sq (a b c d : ℕ) (_h : c + d + 2 = a + b) :
    ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (c + d + 1), dT a b x.1 x.2 ≫ dT x.1 x.2 c d = 0 :=
  dT_comp_dT a b c d (c + d) rfl

end GlobalTheory.EZ.TotSq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DTCompDTStatement
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_antidiagonal_dT_comp_dT_eq_zero : ∀ a b c d : ℕ, c + d + 2 = a + b → ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (c + d + 1), dT a b x.1 x.2 ≫ dT x.1 x.2 c d = 0 := by
  first | (exact @GlobalTheory.EZ.TotSq.dT_sq) | (exact GlobalTheory.EZ.TotSq.dT_sq) | (intros; apply GlobalTheory.EZ.TotSq.dT_sq  <;> assumption)
end
end

open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ Finset

noncomputable section

namespace GlobalTheory.EZ.HTot

theorem idc_self (n : ℕ) : idc n n = 𝟙 _ := by
  ext j
  simp only [idc, clampHom, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk]
  change min n (j : ℕ) = (j : ℕ)
  have : (j : ℕ) < n + 1 := j.isLt
  omega

theorem backc_zero : backc 0 0 0 = 𝟙 _ := by
  ext j
  simp only [backc, clampHom, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk]
  change min 0 (0 + (j : ℕ)) = (j : ℕ)
  have : (j : ℕ) < 0 + 1 := j.isLt
  omega

theorem bop_id (a b : ℕ) : bop (𝟙 (SimplexCategory.mk a)) (𝟙 (SimplexCategory.mk b)) = 𝟙 (bo a b) := rfl

theorem idO_self (a b : ℕ) : idO a b a b = 𝟙 (bo a b) := by
  rw [idO, if_pos ⟨rfl, rfl⟩, idc_self, idc_self, bop_id]

theorem idO_ne {a b c d : ℕ} (h : ¬ (a = c ∧ b = d)) : idO a b c d = 0 := by
  rw [idO, if_neg h]

theorem awO_zero : awO 0 0 0 = 𝟙 (bo 0 0) := by
  rw [awO, if_pos rfl, idc_self, backc_zero, bop_id]

theorem sum_idO_comp {T : BOp} (k a b : ℕ) (h : a + b = k) (g : ∀ p q : ℕ, bo p q ⟶ T) :
    ∑ y ∈ antidiagonal k, idO a b y.1 y.2 ≫ g y.1 y.2 = g a b := by
  rw [Finset.sum_eq_single (a, b)]
  · simp [idO_self]
  · rintro ⟨p, q⟩ _ hne
    rw [idO_ne, Limits.zero_comp]
    rintro ⟨rfl, rfl⟩
    exact hne rfl
  · intro hn
    exact absurd (mem_antidiagonal.2 h) hn

theorem sum_comp_idO {S : BOp} (k c d : ℕ) (h : c + d = k) (f : ∀ p q : ℕ, S ⟶ bo p q) :
    ∑ x ∈ antidiagonal k, f x.1 x.2 ≫ idO x.1 x.2 c d = f c d := by
  rw [Finset.sum_eq_single (c, d)]
  · simp [idO_self]
  · rintro ⟨p, q⟩ _ hne
    rw [idO_ne, Limits.comp_zero]
    rintro ⟨rfl, rfl⟩
    exact hne rfl
  · intro hn
    exact absurd (mem_antidiagonal.2 h) hn

theorem dT_comp_dT (a b c d : ℕ) (h : c + d + 2 = a + b) :
    ∑ x ∈ antidiagonal (c + d + 1), dT a b x.1 x.2 ≫ dT x.1 x.2 c d = 0 :=
  GlobalTheory.T.sum_antidiagonal_dT_comp_dT_eq_zero a b c d h

theorem acyclic (a b k : ℕ) (hk : 1 ≤ k) (z : ∀ a' b' : ℕ, bo a b ⟶ bo a' b')
    (hz : ∀ c d : ℕ, c + d + 1 = k → ∑ x ∈ antidiagonal k, z x.1 x.2 ≫ dT x.1 x.2 c d = 0) :
    ∃ w : ∀ a' b' : ℕ, bo a b ⟶ bo a' b',
      ∀ c d : ℕ, c + d = k → ∑ x ∈ antidiagonal (k + 1), w x.1 x.2 ≫ dT x.1 x.2 c d = z c d :=
  GlobalTheory.T.bisimplicialOperatorChains_acyclic_positiveDegree a b k hk z hz

theorem exists_fill : ∃ H : ∀ a b k : ℕ, (∀ a' b' : ℕ, bo a b ⟶ bo a' b') → (∀ a' b' : ℕ, bo a b ⟶ bo a' b'),
    ∀ a b k (z : ∀ a' b' : ℕ, bo a b ⟶ bo a' b'), 1 ≤ k →
      (∀ c d : ℕ, c + d + 1 = k → ∑ x ∈ antidiagonal k, z x.1 x.2 ≫ dT x.1 x.2 c d = 0) →
      ∀ c d : ℕ, c + d = k → ∑ x ∈ antidiagonal (k + 1), H a b k z x.1 x.2 ≫ dT x.1 x.2 c d = z c d := by
  have : ∀ a b k (z : ∀ a' b' : ℕ, bo a b ⟶ bo a' b'), ∃ w : ∀ a' b' : ℕ, bo a b ⟶ bo a' b', 1 ≤ k →
      (∀ c d : ℕ, c + d + 1 = k → ∑ x ∈ antidiagonal k, z x.1 x.2 ≫ dT x.1 x.2 c d = 0) →
      ∀ c d : ℕ, c + d = k → ∑ x ∈ antidiagonal (k + 1), w x.1 x.2 ≫ dT x.1 x.2 c d = z c d := by
    intro a b k z
    by_cases hk : 1 ≤ k
    · by_cases hz : ∀ c d : ℕ, c + d + 1 = k → ∑ x ∈ antidiagonal k, z x.1 x.2 ≫ dT x.1 x.2 c d = 0
      · obtain ⟨w, hw⟩ := acyclic a b k hk z hz
        exact ⟨w, fun _ _ => hw⟩
      · exact ⟨0, fun _ h => absurd h hz⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose H hH using this
  exact ⟨H, hH⟩

noncomputable def kRec (G : ∀ a b n : ℕ, bo a b ⟶ bo n n)
    (H : ∀ a b k : ℕ, (∀ a' b' : ℕ, bo a b ⟶ bo a' b') → (∀ a' b' : ℕ, bo a b ⟶ bo a' b')) (n : ℕ) :
    ∀ a b a' b' : ℕ, bo a b ⟶ bo a' b' :=
  Nat.rec (motive := fun _ => ∀ a b a' b' : ℕ, bo a b ⟶ bo a' b') (fun _ _ _ _ => 0)
    (fun n K a b => H a b (n + 1) (fun a' b' => G a b (n + 1) ≫ awO (n + 1) a' b' - idO a b a' b' -
      ∑ x ∈ antidiagonal n, dT a b x.1 x.2 ≫ K x.1 x.2 a' b')) n

theorem kRec_zero (G : ∀ a b n : ℕ, bo a b ⟶ bo n n)
    (H : ∀ a b k : ℕ, (∀ a' b' : ℕ, bo a b ⟶ bo a' b') → (∀ a' b' : ℕ, bo a b ⟶ bo a' b')) (a b a' b' : ℕ) :
    kRec G H 0 a b a' b' = 0 := rfl

end GlobalTheory.EZ.HTot

namespace GlobalTheory.EZ.HTot

theorem kRec_spec (G : ∀ a b n : ℕ, bo a b ⟶ bo n n) (hG0 : G 0 0 0 = 𝟙 (bo 0 0))
    (hGd : ∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n =
      ∑ x ∈ antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n)
    (H : ∀ a b k : ℕ, (∀ a' b' : ℕ, bo a b ⟶ bo a' b') → (∀ a' b' : ℕ, bo a b ⟶ bo a' b'))
    (hH : ∀ a b k (z : ∀ a' b' : ℕ, bo a b ⟶ bo a' b'), 1 ≤ k →
      (∀ c d : ℕ, c + d + 1 = k → ∑ x ∈ antidiagonal k, z x.1 x.2 ≫ dT x.1 x.2 c d = 0) →
      ∀ c d : ℕ, c + d = k → ∑ x ∈ antidiagonal (k + 1), H a b k z x.1 x.2 ≫ dT x.1 x.2 c d = z c d) :
    ∀ n a b : ℕ, a + b = n → ∀ a' b' : ℕ, a' + b' = n →
      G a b n ≫ awO n a' b' = idO a b a' b' +
        ∑ x ∈ antidiagonal (n + 1), kRec G H n a b x.1 x.2 ≫ dT x.1 x.2 a' b' +
        ∑ x ∈ antidiagonal (n - 1), dT a b x.1 x.2 ≫ kRec G H (n - 1) x.1 x.2 a' b' := by
  intro n
  induction n with
  | zero =>
    intro a b hab a' b' hab'
    obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
    obtain ⟨rfl, rfl⟩ : a' = 0 ∧ b' = 0 := by omega
    simp [kRec_zero, hG0, awO_zero, idO_self]
  | succ n ih =>
    intro a b hab a' b' hab'
    set E : ∀ a' b' : ℕ, bo a b ⟶ bo a' b' := fun a' b' => G a b (n + 1) ≫ awO (n + 1) a' b' - idO a b a' b' -
      ∑ x ∈ antidiagonal n, dT a b x.1 x.2 ≫ kRec G H n x.1 x.2 a' b' with hE
    have hcyc : ∀ c d : ℕ, c + d + 1 = n + 1 → ∑ y ∈ antidiagonal (n + 1), E y.1 y.2 ≫ dT y.1 y.2 c d = 0 := by
      intro c d hcd
      have h1 : ∑ y ∈ antidiagonal (n + 1), (G a b (n + 1) ≫ awO (n + 1) y.1 y.2) ≫ dT y.1 y.2 c d =
          ∑ x ∈ antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n ≫ awO n c d := by
        simp only [Category.assoc, ← Preadditive.comp_sum]
        rw [← GlobalTheory.T.dD_comp_awO_eq_sum_awO_comp_dT n c d (by omega), ← Category.assoc, hGd a b n hab, Preadditive.sum_comp]
        simp only [Category.assoc]
      have h2 : ∑ y ∈ antidiagonal (n + 1), idO a b y.1 y.2 ≫ dT y.1 y.2 c d = dT a b c d :=
        sum_idO_comp (n + 1) a b hab (fun p q => dT p q c d)
      have key : ∀ x ∈ antidiagonal n, ∑ y ∈ antidiagonal (n + 1), kRec G H n x.1 x.2 y.1 y.2 ≫ dT y.1 y.2 c d =
          G x.1 x.2 n ≫ awO n c d - idO x.1 x.2 c d -
            ∑ z ∈ antidiagonal (n - 1), dT x.1 x.2 z.1 z.2 ≫ kRec G H (n - 1) z.1 z.2 c d := by
        intro x hx
        rw [ih x.1 x.2 (mem_antidiagonal.1 hx) c d (by omega)]
        abel
      have h4 : ∑ x ∈ antidiagonal n, dT a b x.1 x.2 ≫ idO x.1 x.2 c d = dT a b c d :=
        sum_comp_idO n c d (by omega) (fun p q => dT a b p q)
      have h5 : ∑ x ∈ antidiagonal n, ∑ z ∈ antidiagonal (n - 1),
          dT a b x.1 x.2 ≫ dT x.1 x.2 z.1 z.2 ≫ kRec G H (n - 1) z.1 z.2 c d = 0 := by
        rcases n with _ | m
        · simp [kRec_zero]
        · rw [Nat.add_sub_cancel, Finset.sum_comm]
          refine Finset.sum_eq_zero (fun z hz => ?_)
          have hz' := mem_antidiagonal.1 hz
          simp only [← Category.assoc]
          rw [← Preadditive.sum_comp]
          have h0 := dT_comp_dT a b z.1 z.2 (by omega)
          rw [show z.1 + z.2 + 1 = m + 1 by omega] at h0
          rw [h0, Limits.zero_comp]
      have h3 : ∑ y ∈ antidiagonal (n + 1),
          (∑ x ∈ antidiagonal n, dT a b x.1 x.2 ≫ kRec G H n x.1 x.2 y.1 y.2) ≫ dT y.1 y.2 c d =
          ∑ x ∈ antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n ≫ awO n c d - dT a b c d - 0 := by
        have e1 : ∑ y ∈ antidiagonal (n + 1),
            (∑ x ∈ antidiagonal n, dT a b x.1 x.2 ≫ kRec G H n x.1 x.2 y.1 y.2) ≫ dT y.1 y.2 c d =
            ∑ x ∈ antidiagonal n, dT a b x.1 x.2 ≫
              ∑ y ∈ antidiagonal (n + 1), kRec G H n x.1 x.2 y.1 y.2 ≫ dT y.1 y.2 c d := by
          simp only [Preadditive.sum_comp, Category.assoc, Preadditive.comp_sum]
          exact Finset.sum_comm
        rw [e1, Finset.sum_congr rfl (fun x hx => by rw [key x hx])]
        simp only [Preadditive.comp_sub, Finset.sum_sub_distrib, Preadditive.comp_sum]
        rw [h4, h5]
      calc ∑ y ∈ antidiagonal (n + 1), E y.1 y.2 ≫ dT y.1 y.2 c d
          = ∑ y ∈ antidiagonal (n + 1), (G a b (n + 1) ≫ awO (n + 1) y.1 y.2) ≫ dT y.1 y.2 c d -
            ∑ y ∈ antidiagonal (n + 1), idO a b y.1 y.2 ≫ dT y.1 y.2 c d -
            ∑ y ∈ antidiagonal (n + 1),
              (∑ x ∈ antidiagonal n, dT a b x.1 x.2 ≫ kRec G H n x.1 x.2 y.1 y.2) ≫ dT y.1 y.2 c d := by
            simp only [hE, Preadditive.sub_comp, Finset.sum_sub_distrib]
        _ = 0 := by rw [h1, h2, h3]; abel
    have hk : kRec G H (n + 1) a b = H a b (n + 1) E := rfl
    rw [Nat.add_sub_cancel, hk, hH a b (n + 1) E (by omega) hcyc a' b' hab']
    simp only [hE]
    abel

theorem htot : ∀ G : ∀ a b n : ℕ, bo a b ⟶ bo n n, G 0 0 0 = 𝟙 (bo 0 0) →
    (∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n) →
    ∃ K : ∀ a b a' b' : ℕ, bo a b ⟶ bo a' b', ∀ a b a' b' : ℕ, a' + b' = a + b →
      G a b (a + b) ≫ awO (a + b) a' b' = idO a b a' b' +
        ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (a + b + 1), K a b x.1 x.2 ≫ dT x.1 x.2 a' b' +
        ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (a + b - 1), dT a b x.1 x.2 ≫ K x.1 x.2 a' b' := by
  intro G hG0 hGd
  obtain ⟨H, hH⟩ := exists_fill
  refine ⟨fun a b => kRec G H (a + b) a b, ?_⟩
  intro a b a' b' h
  rw [kRec_spec G hG0 hGd H hH (a + b) a b rfl a' b' h]
  congr 1
  refine Finset.sum_congr rfl (fun x hx => ?_)
  show _ = dT a b x.1 x.2 ≫ kRec G H (x.1 + x.2) x.1 x.2 a' b'
  rw [mem_antidiagonal.1 hx]

end GlobalTheory.EZ.HTot
end
end

open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alexander_whitney_homotopy_formula : ∀ G : ∀ a b n : ℕ, bo a b ⟶ bo n n, G 0 0 0 = 𝟙 (bo 0 0) → (∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n) → ∃ K : ∀ a b a' b' : ℕ, bo a b ⟶ bo a' b', ∀ a b a' b' : ℕ, a' + b' = a + b → G a b (a + b) ≫ awO (a + b) a' b' = idO a b a' b' + ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (a + b + 1), K a b x.1 x.2 ≫ dT x.1 x.2 a' b' + ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (a + b - 1), dT a b x.1 x.2 ≫ K x.1 x.2 a' b' := by
  first | (exact @GlobalTheory.EZ.HTot.htot) | (exact GlobalTheory.EZ.HTot.htot) | (intros; apply GlobalTheory.EZ.HTot.htot <;> assumption)
