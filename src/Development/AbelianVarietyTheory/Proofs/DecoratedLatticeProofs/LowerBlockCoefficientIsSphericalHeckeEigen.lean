module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RelIndexPreimagePiEqProd
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SupportParahoricBiTransformingLeviDoubleCoset
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CardFilterLowerHeckeRepsEqRelIndexPow

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricBiTransformingLowerUnipotentDiagValue
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricDoubleCosetValuation
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section
namespace GlobalTheory.ParHeckeCap

theorem val_mul_lt_left {k : Type} [Field k] [ValuativeRel k] {X Y Z : Type} [Fintype Y] (c : Matrix X Y k)
    (w : Matrix Y Z k) (hc : ∀ i j, valuation k (c i j) < 1) (hw : ∀ i j, valuation k (w i j) ≤ 1) :
    ∀ i j, valuation k ((c * w) i j) < 1 := by
  intro i j
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_lt _ one_ne_zero fun l _ => ?_
  rw [map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_right' (hw l j)) (hc i l)

theorem val_mul_lt_right {k : Type} [Field k] [ValuativeRel k] {X Y Z : Type} [Fintype Y] (w : Matrix X Y k)
    (c : Matrix Y Z k) (hw : ∀ i j, valuation k (w i j) ≤ 1) (hc : ∀ i j, valuation k (c i j) < 1) :
    ∀ i j, valuation k ((w * c) i j) < 1 := by
  intro i j
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_lt _ one_ne_zero fun l _ => ?_
  rw [map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' (hw i l)) (hc l j)

theorem toBlocks₂₁_mul_mul {k : Type} [Field k] {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    (P E Q : Matrix (A ⊕ D) (A ⊕ D) k) (hP : P.toBlocks₂₁ = 0) (hE : E.toBlocks₂₁ = 0)
    (hQ : Q.toBlocks₂₁ = 0) : (P * E * Q).toBlocks₂₁ = 0 := by
  rw [← fromBlocks_toBlocks P, ← fromBlocks_toBlocks E, ← fromBlocks_toBlocks Q, hP, hE, hQ]
  simp [fromBlocks_multiply]

theorem lowUni_mul_toBlocks₂₁ {k : Type} [Field k] {A D : Type} [Fintype A] [DecidableEq A] [Fintype D]
    [DecidableEq D] (X : Matrix D A k) (M : Matrix (A ⊕ D) (A ⊕ D) k) :
    (fromBlocks 1 0 X 1 * M).toBlocks₂₁ = X * M.toBlocks₁₁ + M.toBlocks₂₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks M]
  simp [fromBlocks_multiply]

theorem mul_lowUni_toBlocks₂₁ {k : Type} [Field k] {A D : Type} [Fintype A] [DecidableEq A] [Fintype D]
    [DecidableEq D] (X : Matrix D A k) (M : Matrix (A ⊕ D) (A ⊕ D) k) :
    (M * fromBlocks 1 0 X 1).toBlocks₂₁ = M.toBlocks₂₁ + M.toBlocks₂₂ * X := by
  conv_lhs => rw [← fromBlocks_toBlocks M]
  simp [fromBlocks_multiply]

theorem lowerUni_mem_cap : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (g : GL (A ⊕ D) k) (ν : Matrix D A k)
    (m : GL D k), g.1 = fromBlocks 1 0 ν m.1 →
    (∃ x y, ∃ j ∈ parahoric k A D, ∃ j' ∈ parahoric k A D, g = j * emb₂ k (Equiv.refl (A ⊕ D)) (x, y) * j') →
    ∃ ν₁ ν₂ : Matrix D A k, (∀ i a, valuation k (ν₁ i a) < 1) ∧ (∀ i a, valuation k (ν₂ i a) < 1) ∧
      ν = ν₁ + m.1 * ν₂ := by
  intro k _ _ _ _ A D _ _ _ _ g ν m hg ⟨x, y, j, hj, j', hj', he⟩
  obtain ⟨⟨u, hu, hua⟩, -, hc, -⟩ := (GlobalTheory.ParahoricConjBlocks.mem_parahoric_val_iff j.1).1 ⟨j, hj, rfl⟩
  obtain ⟨-, -, hc', ⟨u', hu', hud⟩⟩ := (GlobalTheory.ParahoricConjBlocks.mem_parahoric_val_iff j'.1).1 ⟨j', hj', rfl⟩
  have hui := ((GlobalTheory.ParahoricConjBlocks.mem_KO_val_iff (u⁻¹).1).1 ⟨u⁻¹, inv_mem hu, rfl⟩).1
  have hui' := ((GlobalTheory.ParahoricConjBlocks.mem_KO_val_iff (u'⁻¹).1).1 ⟨u'⁻¹, inv_mem hu', rfl⟩).1
  set ν₁ := j.1.toBlocks₂₁ * (u⁻¹).1
  set ν₂ := (u'⁻¹).1 * j'.1.toBlocks₂₁
  refine ⟨ν₁, ν₂, val_mul_lt_left _ _ hc hui, val_mul_lt_right _ _ hui' hc', ?_⟩
  have hP : (fromBlocks 1 0 (-ν₁) 1 * j.1).toBlocks₂₁ = 0 := by
    have e1 : ν₁ * u.1 = j.1.toBlocks₂₁ := by simp only [ν₁, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    rw [lowUni_mul_toBlocks₂₁, ← hua, Matrix.neg_mul, e1, neg_add_cancel]
  have hQ : (j'.1 * fromBlocks 1 0 (-ν₂) 1).toBlocks₂₁ = 0 := by
    have e2 : u'.1 * ν₂ = j'.1.toBlocks₂₁ := by simp only [ν₂, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    rw [mul_lowUni_toBlocks₂₁, ← hud, Matrix.mul_neg, e2, add_neg_cancel]
  have hE : (emb₂ k (Equiv.refl (A ⊕ D)) (x, y)).1.toBlocks₂₁ = 0 := by
    rw [val_emb₂]
    simp
  have key := toBlocks₂₁_mul_mul _ _ _ hP hE hQ
  have h2 : fromBlocks 1 0 (-ν₁) 1 * j.1 * (emb₂ k (Equiv.refl (A ⊕ D)) (x, y)).1 *
      (j'.1 * fromBlocks 1 0 (-ν₂) 1) = fromBlocks 1 0 (-ν₁) 1 * g.1 * fromBlocks 1 0 (-ν₂) 1 := by
    rw [he]
    simp only [Units.val_mul, Matrix.mul_assoc]
  rw [h2, hg] at key
  simp [fromBlocks_multiply] at key
  rw [← sub_eq_zero, ← key]
  abel

end GlobalTheory.ParHeckeCap
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricBiTransformingLowerUnipotentDiagValue
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke GlobalTheory.LowerHecke
open Classical

namespace GlobalTheory.LowerHeckeSupp

theorem lowU_add {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (a b : Matrix D A k) :
    lowU (a + b) = lowU a * lowU b := by
  ext1
  rw [Units.val_mul, val_lowU, val_lowU, val_lowU, fromBlocks_multiply]
  simp [add_comm]

theorem biType_lowU_emb : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ξ : kˣ →* ℂˣ), IsTame ξ → ¬ IsUnram ξ → ∀ φ : GL (A ⊕ D) k → ℂ, IsBiType ξ φ → ∀ (ν : Matrix D A k) (y : GL D k), φ (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, y)) = if ∃ ν₁ ν₂ : Matrix D A k, (∀ i a, valuation k (ν₁ i a) < 1) ∧ (∀ i a, valuation k (ν₂ i a) < 1) ∧ ν = ν₁ + y.1 * ν₂ then φ (emb₂ k (Equiv.refl (A ⊕ D)) (1, y)) else 0 := by
  intro k _ _ _ _ A D _ _ _ _ ξ hT hU φ hφ ν y
  split_ifs with h
  · obtain ⟨ν₁, ν₂, h₁, h₂, rfl⟩ := h
    have hd : ∀ μ : Matrix D A k, ((1 : kˣ) : k) = ((lowU μ : GL (A ⊕ D) k) : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det := by
      intro μ; simp [val_lowU]
    rw [lowU_add, mul_assoc, ← emb_mul_lowU]
    rw [(hφ _ (lowU_mem h₁) 1 (hd ν₁) _).1, (hφ _ (lowU_mem h₂) 1 (hd ν₂) _).2]
    simp
  · by_contra hne
    obtain ⟨x, z, j, hj, j', hj', he⟩ := GlobalTheory.ParHeckeSupp.support_levi k A D ξ hT hU φ hφ _ hne
    have hv : (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, y)).1 = fromBlocks 1 0 ν y.1 := by
      rw [Units.val_mul, val_lowU, val_emb_one, fromBlocks_multiply]; simp
    exact h (GlobalTheory.ParHeckeCap.lowerUni_mem_cap k A D _ ν y hv ⟨x, z, j, hj, j', hj', he⟩)

end GlobalTheory.LowerHeckeSupp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricBiTransformingLowerUnipotentDiagValueStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke GlobalTheory.LowerHecke
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parahoricBiTransforming_lowerUnipotent_diag_value : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ξ : kˣ →* ℂˣ), IsTame ξ → ¬ IsUnram ξ → ∀ φ : GL (A ⊕ D) k → ℂ, IsBiType ξ φ → ∀ (ν : Matrix D A k) (y : GL D k), φ (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, y)) = if ∃ ν₁ ν₂ : Matrix D A k, (∀ i a, valuation k (ν₁ i a) < 1) ∧ (∀ i a, valuation k (ν₂ i a) < 1) ∧ ν = ν₁ + y.1 * ν₂ then φ (emb₂ k (Equiv.refl (A ⊕ D)) (1, y)) else 0 := by
  first | exact @GlobalTheory.LowerHeckeSupp.biType_lowU_emb | exact GlobalTheory.LowerHeckeSupp.biType_lowU_emb | (intros; apply GlobalTheory.LowerHeckeSupp.biType_lowU_emb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedHeightLatticeIndexIdentity
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RelIndexScaledMaxIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RelIndexScaledMaxIdeal
open ValuativeRel GlobalTheory.SplitWeil

namespace GlobalTheory.ScaledIdealIndex

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem relIndex_comap_mulLeft (a : kˣ) (H K : AddSubgroup k) :
    (H.comap (AddMonoidHom.mulLeft (a : k))).relIndex (K.comap (AddMonoidHom.mulLeft (a : k))) =
      H.relIndex K := by
  have hs : Function.Surjective (AddMonoidHom.mulLeft (a : k)) := fun y =>
    ⟨((a⁻¹ : kˣ) : k) * y, by simp [← mul_assoc]⟩
  rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hs]

theorem relIndex_maxIdeal (L : AddSubgroup k) (hL : ∀ x, x ∈ L ↔ valuation k x < 1) :
    L.relIndex (𝒪[k]).toAddSubgroup = resCard k := by
  let f : 𝒪[k] →+ k := (𝒪[k]).subtype.toAddMonoidHom
  have hr : f.range = (𝒪[k]).toAddSubgroup := by
    ext x; simp [f]
  let g : 𝒪[k] →+ 𝓀[k] := (IsLocalRing.residue 𝒪[k]).toAddMonoidHom
  have hk : L.comap f = g.ker := by
    ext y
    simp only [AddSubgroup.mem_comap, AddMonoidHom.mem_ker, g, RingHom.toAddMonoidHom_eq_coe,
      AddMonoidHom.coe_coe, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one, hL]
    rfl
  have hs : Function.Surjective g := Ideal.Quotient.mk_surjective
  rw [← hr, ← AddSubgroup.index_comap, hk, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hs]
  simp [resCard]

section
variable (L : AddSubgroup k) (hL : ∀ x, x ∈ L ↔ valuation k x < 1)
include hL

theorem mem_comap_mulLeft (a : kˣ) (x : k) :
    x ∈ L.comap (AddMonoidHom.mulLeft (a : k)) ↔ valuation k ((a : k) * x) < 1 := by
  simp [hL]

theorem comap_mulLeft_one : L.comap (AddMonoidHom.mulLeft ((1 : kˣ) : k)) = L := by
  ext x; simp [hL]

theorem comap_mulLeft_mul (a b : kˣ) :
    L.comap (AddMonoidHom.mulLeft ((a * b : kˣ) : k)) =
      (L.comap (AddMonoidHom.mulLeft (a : k))).comap (AddMonoidHom.mulLeft (b : k)) := by
  ext x; simp [hL, mul_assoc]

theorem comap_mulLeft_le_pow (ϖ : kˣ) (hϖ : valuation k (ϖ : k) ≤ 1) (a : kˣ) (j : ℕ) :
    L.comap (AddMonoidHom.mulLeft (a : k)) ≤ L.comap (AddMonoidHom.mulLeft ((ϖ ^ j * a : kˣ) : k)) := by
  intro x hx
  rw [mem_comap_mulLeft L hL] at hx ⊢
  rw [Units.val_mul, Units.val_pow_eq_pow_val, mul_assoc, map_mul, map_pow]
  exact lt_of_le_of_lt (mul_le_of_le_one_left zero_le' (pow_le_one₀ zero_le' hϖ)) hx

theorem relIndex_unif (ϖ : kˣ) (hϖ : valuation k (ϖ : k) = uniformizer k) :
    (L.comap (AddMonoidHom.mulLeft ((ϖ⁻¹ : kˣ) : k))).relIndex L = resCard k := by
  have hpos : 0 < valuation k (ϖ : k) := zero_lt_iff.2 (by simp)
  have e : L = (𝒪[k]).toAddSubgroup.comap (AddMonoidHom.mulLeft ((ϖ⁻¹ : kˣ) : k)) := by
    ext x
    rw [hL]
    simp only [AddSubgroup.mem_comap, AddMonoidHom.coe_mulLeft, Subring.mem_toAddSubgroup,
      Valuation.mem_integer_iff, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
    rw [inv_mul_le_iff₀ hpos, mul_one, hϖ, le_uniformizer_iff]
  calc (L.comap (AddMonoidHom.mulLeft ((ϖ⁻¹ : kˣ) : k))).relIndex L
      = (L.comap (AddMonoidHom.mulLeft ((ϖ⁻¹ : kˣ) : k))).relIndex
          ((𝒪[k]).toAddSubgroup.comap (AddMonoidHom.mulLeft ((ϖ⁻¹ : kˣ) : k))) := by rw [← e]
    _ = resCard k := by rw [relIndex_comap_mulLeft, relIndex_maxIdeal L hL]

theorem relIndex_unif_pow (ϖ : kˣ) (hϖ : valuation k (ϖ : k) = uniformizer k) (n : ℕ) :
    (L.comap (AddMonoidHom.mulLeft ((ϖ ^ (-(n : ℤ)) : kˣ) : k))).relIndex L = resCard k ^ n := by
  have h1 : valuation k (ϖ : k) ≤ 1 := hϖ ▸ uniformizer_lt_one.le
  induction n with
  | zero => rw [Nat.cast_zero, neg_zero, zpow_zero, comap_mulLeft_one L hL, pow_zero, AddSubgroup.relIndex_self]
  | succ n ih =>
    have ea : ϖ ^ (-((n + 1 : ℕ) : ℤ)) = ϖ⁻¹ * ϖ ^ (-(n : ℤ)) := by
      rw [← zpow_neg_one, ← zpow_add]; congr 1; push_cast; ring
    have eb : ϖ ^ (-(n : ℤ)) = ϖ ^ (1 : ℕ) * ϖ ^ (-((n + 1 : ℕ) : ℤ)) := by
      rw [ea, pow_one, ← mul_assoc, mul_inv_cancel, one_mul]
    have hle : L.comap (AddMonoidHom.mulLeft ((ϖ ^ (-((n + 1 : ℕ) : ℤ)) : kˣ) : k)) ≤
        L.comap (AddMonoidHom.mulLeft ((ϖ ^ (-(n : ℤ)) : kˣ) : k)) := by
      rw [eb]; exact comap_mulLeft_le_pow L hL ϖ h1 _ 1
    have hle2 : L.comap (AddMonoidHom.mulLeft ((ϖ ^ (-(n : ℤ)) : kˣ) : k)) ≤ L := by
      have := comap_mulLeft_le_pow L hL ϖ h1 (ϖ ^ (-(n : ℤ))) n
      rwa [← zpow_natCast, ← zpow_add, add_neg_cancel, zpow_zero, comap_mulLeft_one L hL] at this
    rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ hle hle2, ih, pow_succ, mul_comm]
    congr 1
    have e1 : L.comap (AddMonoidHom.mulLeft ((ϖ ^ (-(n : ℤ)) : kˣ) : k)) =
        L.comap (AddMonoidHom.mulLeft (((1 : kˣ) * ϖ ^ (-(n : ℤ)) : kˣ) : k)) := by rw [one_mul]
    rw [ea, e1, comap_mulLeft_mul L hL, comap_mulLeft_mul L hL, relIndex_comap_mulLeft,
      comap_mulLeft_one L hL, relIndex_unif L hL ϖ hϖ]

end

end GlobalTheory.ScaledIdealIndex

namespace GlobalTheory.ScaledIdealIndex

theorem relIndex_scaled_maxIdeal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k →
    ∀ (c : ℤ) (L P : AddSubgroup k), (∀ x, x ∈ L ↔ valuation k x < 1) →
      (∀ x, x ∈ P ↔ valuation k (((ϖ ^ c : kˣ) : k) * x) < 1) →
      (P ⊓ L).relIndex P * (P ⊓ L).relIndex L = resCard k ^ c.natAbs := by
  intro k _ _ _ _ ϖ hϖ c L P hL hP
  have h1 : valuation k (ϖ : k) ≤ 1 := hϖ ▸ uniformizer_lt_one.le
  have hPe : P = L.comap (AddMonoidHom.mulLeft ((ϖ ^ c : kˣ) : k)) := by
    ext x; rw [hP, mem_comap_mulLeft L hL]
  rw [AddSubgroup.inf_relIndex_left, AddSubgroup.inf_relIndex_right]
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg c
  · have hLP : L ≤ P := by
      have := comap_mulLeft_le_pow L hL ϖ h1 1 n
      rwa [mul_one, comap_mulLeft_one L hL, ← zpow_natCast, ← hPe] at this
    rw [AddSubgroup.relIndex_eq_one.2 hLP, mul_one, Int.natAbs_natCast]
    have eL : L = L.comap (AddMonoidHom.mulLeft (((ϖ ^ (-(n : ℤ)) * ϖ ^ (n : ℤ) : kˣ)) : k)) := by
      rw [← zpow_add, neg_add_cancel, zpow_zero, comap_mulLeft_one L hL]
    have eP : P = L.comap (AddMonoidHom.mulLeft ((((1 : kˣ) * ϖ ^ (n : ℤ) : kˣ)) : k)) := by
      rw [one_mul, hPe]
    calc L.relIndex P
        = (L.comap (AddMonoidHom.mulLeft (((ϖ ^ (-(n : ℤ)) * ϖ ^ (n : ℤ) : kˣ)) : k))).relIndex
            (L.comap (AddMonoidHom.mulLeft ((((1 : kˣ) * ϖ ^ (n : ℤ) : kˣ)) : k))) := by
          rw [← eL, ← eP]
      _ = resCard k ^ n := by
          rw [comap_mulLeft_mul L hL, comap_mulLeft_mul L hL, relIndex_comap_mulLeft,
            comap_mulLeft_one L hL, relIndex_unif_pow L hL ϖ hϖ n]
  · have hPL : P ≤ L := by
      have := comap_mulLeft_le_pow L hL ϖ h1 (ϖ ^ (-(n : ℤ))) n
      rwa [← zpow_natCast, ← zpow_add, add_neg_cancel, zpow_zero, comap_mulLeft_one L hL, ← hPe] at this
    rw [AddSubgroup.relIndex_eq_one.2 hPL, one_mul, Int.natAbs_neg, Int.natAbs_natCast, hPe,
      relIndex_unif_pow L hL ϖ hϖ n]

end GlobalTheory.ScaledIdealIndex
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RelIndexScaledMaxIdealStatement
open ValuativeRel GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_inf_mul_relIndex_inf_eq_resCard_pow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (c : ℤ) (L P : AddSubgroup k), (∀ x, x ∈ L ↔ valuation k x < 1) → (∀ x, x ∈ P ↔ valuation k (((ϖ ^ c : kˣ) : k) * x) < 1) → (P ⊓ L).relIndex P * (P ⊓ L).relIndex L = resCard k ^ c.natAbs := by
  first | exact @GlobalTheory.ScaledIdealIndex.relIndex_scaled_maxIdeal | exact GlobalTheory.ScaledIdealIndex.relIndex_scaled_maxIdeal | (intros; apply GlobalTheory.ScaledIdealIndex.relIndex_scaled_maxIdeal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedHeightLatticeIndexIdentity
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section
namespace GlobalTheory.HeckeLatIndex

theorem ko_pres : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (D : Type) [Fintype D] [DecidableEq D] (κ : GL D k), κ ∈ KO k D → ∀ v : D → k, (∀ i, valuation k (v i) < 1) → ∀ i, valuation k (κ.1.mulVec v i) < 1 := by
  intro k _ _ _ _ D _ _ κ hκ v hv i
  have hent : ∀ j, valuation k (κ.1 i j) ≤ 1 := fun j =>
    (Valuation.mem_integer_iff _ _).1 (((GlobalTheory.SplitFlip.mem_KO_iff κ).1 hκ).1 i j)
  rw [Matrix.mulVec, dotProduct]
  exact Valuation.map_sum_lt _ one_ne_zero fun j _ => by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hent j)) (hv j)

theorem line_index : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (c : ℤ) (L P : AddSubgroup k), (∀ x, x ∈ L ↔ valuation k x < 1) → (∀ x, x ∈ P ↔ valuation k (((ϖ ^ c : kˣ) : k) * x) < 1) → (P ⊓ L).relIndex P * (P ⊓ L).relIndex L = resCard k ^ c.natAbs := GlobalTheory.T.relIndex_inf_mul_relIndex_inf_eq_resCard_pow

theorem relIndex_pi_univ {ι G : Type} [Fintype ι] [AddCommGroup G] (A B : ι → AddSubgroup G) :
    (AddSubgroup.pi Set.univ A).relIndex (AddSubgroup.pi Set.univ B) = ∏ i, (A i).relIndex (B i) := by
  let g : (∀ i, B i) →+ (AddSubgroup.pi Set.univ B) :=
    { toFun := fun v => ⟨fun i => (v i : G), fun i _ => (v i).2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hg : Function.Surjective g := fun x => ⟨fun i => ⟨x.1 i, x.2 i (Set.mem_univ i)⟩, rfl⟩
  have hc : ((AddSubgroup.pi Set.univ A).addSubgroupOf (AddSubgroup.pi Set.univ B)).comap g =
      AddSubgroup.pi Set.univ fun i => (A i).addSubgroupOf (B i) := by
    ext v
    simp [g, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi]
  rw [AddSubgroup.relIndex, ← AddSubgroup.index_comap_of_surjective _ hg, hc]
  simp_rw [AddSubgroup.relIndex, AddSubgroup.index, ← Nat.card_pi]
  refine Nat.card_congr ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientAddGroup.leftRel_pi]

theorem diag_index : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (D : Type) [Fintype D] [DecidableEq D] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (e : D → ℤ) (L P : AddSubgroup (D → k)), (∀ v, v ∈ L ↔ ∀ i, valuation k (v i) < 1) → (∀ v, v ∈ P ↔ ∀ i, valuation k (((ϖ ^ e i : kˣ) : k) * v i) < 1) → (((P ⊓ L).relIndex P : ℕ) : ℝ) * (((P ⊓ L).relIndex L : ℕ) : ℝ) = (resCard k : ℝ) ^ (sumAbs e) := by
  intro k _ _ _ _ D _ _ ϖ hϖ e L P hL hP
  let L₀ : AddSubgroup k := (valuation k).ltAddSubgroup 1
  have hL₀ : ∀ x, x ∈ L₀ ↔ valuation k x < 1 := fun x => Iff.rfl
  let Pi : D → AddSubgroup k := fun i => L₀.comap (AddMonoidHom.mulLeft ((ϖ ^ e i : kˣ) : k))
  have hPi : ∀ i x, x ∈ Pi i ↔ valuation k (((ϖ ^ e i : kˣ) : k) * x) < 1 := fun i x => Iff.rfl
  have eL : L = AddSubgroup.pi Set.univ fun _ => L₀ := by
    ext v; rw [hL]; simp [AddSubgroup.mem_pi, hL₀]
  have eP : P = AddSubgroup.pi Set.univ Pi := by
    ext v; rw [hP]; simp [AddSubgroup.mem_pi, hPi]
  have eI : P ⊓ L = AddSubgroup.pi Set.univ fun i => Pi i ⊓ L₀ := by
    ext v; rw [AddSubgroup.mem_inf, eP, eL]; simp [AddSubgroup.mem_pi, forall_and]
  rw [eI, eP, eL, relIndex_pi_univ, relIndex_pi_univ]
  have h1 : ∀ i, (Pi i ⊓ L₀).relIndex (Pi i) * (Pi i ⊓ L₀).relIndex L₀ = resCard k ^ (e i).natAbs :=
    fun i => line_index k ϖ hϖ (e i) L₀ (Pi i) hL₀ (hPi i)
  rw [← Nat.cast_mul, ← Finset.prod_mul_distrib, Finset.prod_congr rfl (fun i _ => h1 i),
    Finset.prod_pow_eq_pow_sum]
  have hs : sumAbs e = ((∑ i, (e i).natAbs : ℕ) : ℤ) := by
    unfold sumAbs; push_cast; simp [Int.natCast_natAbs]
  rw [hs, zpow_natCast]
  push_cast
  rfl

theorem map_eq_of_preimage {k : Type} [Field k] {D : Type} [Fintype D] [DecidableEq D] (g : GL D k)
    (S T : AddSubgroup (D → k)) (hS : ∀ w, w ∈ S ↔ g.1.mulVec w ∈ T) :
    S.map (Matrix.mulVecLin g.1).toAddMonoidHom = T := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (hS w).1 hw
  · intro hv
    have hgv : g.1.mulVec ((g⁻¹).1.mulVec v) = v := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    refine ⟨(g⁻¹).1.mulVec v, (hS _).2 (by rw [hgv]; exact hv), hgv⟩

theorem mulVec_injective {k : Type} [Field k] {D : Type} [Fintype D] [DecidableEq D] (g : GL D k) :
    Function.Injective (Matrix.mulVecLin g.1).toAddMonoidHom := by
  intro v w h
  have h' : (g⁻¹).1.mulVec (g.1.mulVec v) = (g⁻¹).1.mulVec (g.1.mulVec w) := congrArg _ h
  simpa [Matrix.mulVec_mulVec, ← Units.val_mul] using h'

theorem ko_mem_iff {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {D : Type} [Fintype D] [DecidableEq D] (κ : GL D k) (hκ : κ ∈ KO k D) (L : AddSubgroup (D → k))
    (hL : ∀ v, v ∈ L ↔ ∀ i, valuation k (v i) < 1) (w : D → k) : w ∈ L ↔ κ.1.mulVec w ∈ L := by
  rw [hL, hL]
  refine ⟨ko_pres k D κ hκ w, fun h => ?_⟩
  have := ko_pres k D κ⁻¹ (inv_mem hκ) _ h
  rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at this

theorem ko_index : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (D : Type) [Fintype D] [DecidableEq D] (h κ κ' : GL D k), κ ∈ KO k D → κ' ∈ KO k D → ∀ (L P P' : AddSubgroup (D → k)), (∀ v, v ∈ L ↔ ∀ i, valuation k (v i) < 1) → (∀ v, v ∈ P ↔ h.1.mulVec v ∈ L) → (∀ v, v ∈ P' ↔ (κ * h * κ').1.mulVec v ∈ L) → (P' ⊓ L).relIndex P' = (P ⊓ L).relIndex P ∧ (P' ⊓ L).relIndex L = (P ⊓ L).relIndex L := by
  intro k _ _ _ _ D _ _ h κ κ' hκ hκ' L P P' hL hP hP'
  have h1 : ∀ w, w ∈ P' ↔ κ'.1.mulVec w ∈ P := fun w => by
    rw [hP', hP, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ← ko_mem_iff κ hκ L hL]
  have h2 : ∀ w, w ∈ L ↔ κ'.1.mulVec w ∈ L := ko_mem_iff κ' hκ' L hL
  have m1 := map_eq_of_preimage κ' P' P h1
  have m2 := map_eq_of_preimage κ' L L h2
  have hinj := mulVec_injective κ'
  constructor
  · rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hinj, AddSubgroup.map_inf_eq _ _ _ hinj, m1, m2]
  · rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hinj, AddSubgroup.map_inf_eq _ _ _ hinj, m1, m2]

theorem hgt_mul_index : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (D : Type) [Fintype D] [DecidableEq D] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ H : GL D k → ℝ, IsHgt ϖ H → ∀ (h : GL D k) (L P : AddSubgroup (D → k)), (∀ v, v ∈ L ↔ ∀ i, valuation k (v i) < 1) → (∀ v, v ∈ P ↔ h.1.mulVec v ∈ L) → H h * (((P ⊓ L).relIndex P : ℕ) : ℝ) * (((P ⊓ L).relIndex L : ℕ) : ℝ) = 1 := by
  intro k _ _ _ _ D _ _ ϖ hϖ H hH h L P hL hP
  have hq : (0 : ℝ) < resCard k := by exact_mod_cast (show 0 < resCard k by unfold resCard; exact Nat.card_pos)
  have hc : ∃ x ∈ KO k D, ∃ y ∈ KO k D, ∃ e : D → ℤ,
      h = x * torusElt k D ϖ e * y := by
    have ho : SmGL.ord k 1 = 0 := SmGL.ord_eq_zero_iff.mpr (by simp)
    have hi (y : kˣ) : SmGL.ord k y⁻¹ = -SmGL.ord k y := by
      have hh := SmGL.ord_mul k y y⁻¹
      rw [mul_inv_cancel, ho] at hh
      omega
    have hp (m : ℤ) : SmGL.ord k (ϖ ^ m) = m := by
      have h1 := SmGL.ord_eq_one hϖ
      induction m using Int.induction_on with
      | zero => simpa using ho
      | succ i ih => rw [_root_.zpow_add_one, SmGL.ord_mul, ih, h1]
      | pred i ih =>
        rw [_root_.zpow_sub_one, SmGL.ord_mul, ih, hi, h1]
        ring
    have hu (z : kˣ) : ∃ u : kˣ, ∃ m : ℤ, valuation k (u : k) = 1 ∧ z = u * ϖ ^ m := by
      refine ⟨z * (ϖ ^ SmGL.ord k z)⁻¹, SmGL.ord k z, ?_, by simp⟩
      apply SmGL.ord_eq_zero_iff.mp
      rw [SmGL.ord_mul, hi, hp]
      ring
    obtain ⟨x, hx, y, hy, t, rfl⟩ := GlobalTheory.LocalCartan.exists_diagT h
    choose u e hu htu using fun i => hu (t i)
    refine ⟨x * GlobalTheory.SmGL.diagT k D u,
      mul_mem hx (GlobalTheory.LocalCartan.diagT_mem_KO hu), y, hy, e, ?_⟩
    have ht : t = u * fun i => ϖ ^ e i := funext htu
    rw [ht, map_mul]
    simp only [torusElt, mul_assoc]
  obtain ⟨x, hx, y, hy, e, rfl⟩ := hc
  let t : GL D k := torusElt k D ϖ e
  let Pt : AddSubgroup (D → k) := L.comap (Matrix.mulVecLin t.1).toAddMonoidHom
  have hPt : ∀ v, v ∈ Pt ↔ t.1.mulVec v ∈ L := fun v => Iff.rfl
  obtain ⟨e1, e2⟩ := ko_index k D t x y hx hy L Pt P hL hPt hP
  have hd := diag_index k D ϖ hϖ e L Pt hL (fun v => by
    rw [hPt, hL]
    simp [t, torusElt, val_diagT, Matrix.mulVec_diagonal])
  have hH1 : H (x * t * y) = H t := by rw [(hH.1 y hy _).2, (hH.1 x hx _).1]
  rw [e1, e2, mul_assoc, hd]
  change H (x * t * y) * _ = 1
  rw [hH1, hH.2 e, ← zpow_add₀ hq.ne']
  simp

theorem index_identity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (D : Type) [Fintype D] [DecidableEq D] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ H : GL D k → ℝ, IsHgt ϖ H → ∀ (m g : GL D k) (s : Finset D), (∃ κ ∈ KO k D, ∃ κ' ∈ KO k D, g = κ * torusElt k D ϖ (indic s) * κ') → ∀ (L Lm large₂ : AddSubgroup (D → k)), (∀ v, v ∈ L ↔ ∀ i, valuation k (v i) < 1) → (∀ v, v ∈ Lm ↔ m.1.mulVec v ∈ L) → (∀ v, v ∈ large₂ ↔ (g⁻¹).1.mulVec v ∈ L) → (((Lm ⊓ large₂).relIndex (Lm ⊓ L) : ℕ) : ℝ) ^ 2 * H (m * g) = (resCard k : ℝ) ^ s.card * H m := by
  intro k _ _ _ _ D _ _ ϖ hϖ H hH m g s hg L Lm large₂ hL hLm hLg
  have hq : (0 : ℝ) < resCard k := by exact_mod_cast (show 0 < resCard k by unfold resCard; exact Nat.card_pos)
  obtain ⟨κ, hκ, κ', hκ', hgeq⟩ := hg

  have hgL : ∀ v, v ∈ L → g.1.mulVec v ∈ L := by
    intro v hv
    rw [hgeq, hL]
    have h1 := ko_pres k D κ' hκ' v ((hL v).1 hv)
    have h2 : ∀ i, valuation k ((torusElt k D ϖ (indic s)).1.mulVec (κ'.1.mulVec v) i) < 1 := by
      intro i
      simp only [torusElt, val_diagT, Matrix.mulVec_diagonal, map_mul]
      have hle : valuation k ((ϖ ^ indic s i : kˣ) : k) ≤ 1 := by
        unfold indic
        split_ifs
        · simp only [zpow_one]
          rw [hϖ]
          exact uniformizer_lt_one.le
        · simp
      exact lt_of_le_of_lt (mul_le_of_le_one_left' hle) (h1 i)
    have h3 := ko_pres k D κ hκ _ h2
    simpa [Matrix.mulVec_mulVec, Units.val_mul, Matrix.mul_assoc] using h3
  have hLgL : large₂ ≤ L := by
    intro v hv
    have : g.1.mulVec ((g⁻¹).1.mulVec v) = v := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [← this]
    exact hgL _ ((hLg v).1 hv)
  set φ := (Matrix.mulVecLin g.1).toAddMonoidHom with hφ
  have hinj : Function.Injective φ := mulVec_injective g

  let P₁ : AddSubgroup (D → k) := L.comap (Matrix.mulVecLin (m * g).1).toAddMonoidHom
  let P₂ : AddSubgroup (D → k) := L.comap (Matrix.mulVecLin g.1).toAddMonoidHom
  have hP₁ : ∀ v, v ∈ P₁ ↔ (m * g).1.mulVec v ∈ L := fun v => Iff.rfl
  have hP₂ : ∀ v, v ∈ P₂ ↔ g.1.mulVec v ∈ L := fun v => Iff.rfl
  have mP₁ : P₁.map φ = Lm := map_eq_of_preimage g P₁ Lm fun w => by
    rw [hP₁, hLm, Units.val_mul, Matrix.mulVec_mulVec]
  have mL : L.map φ = large₂ := by
    refine map_eq_of_preimage g L large₂ fun w => ?_
    rw [hLg, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have mP₂ : P₂.map φ = L := map_eq_of_preimage g P₂ L hP₂
  have k₁ := hgt_mul_index k D ϖ hϖ H hH m L Lm hL hLm
  have k₂ := hgt_mul_index k D ϖ hϖ H hH (m * g) L P₁ hL hP₁
  have k₃ := hgt_mul_index k D ϖ hϖ H hH g L P₂ hL hP₂
  rw [← AddSubgroup.relIndex_map_map_of_injective (f := φ) _ _ hinj,
    ← AddSubgroup.relIndex_map_map_of_injective (f := φ) (P₁ ⊓ L) L hinj,
    AddSubgroup.map_inf_eq _ _ _ hinj, mP₁, mL] at k₂
  have hLP₂ : L ≤ P₂ := fun v hv => hgL v hv
  rw [inf_eq_right.2 hLP₂, AddSubgroup.relIndex_self, ← AddSubgroup.relIndex_map_map_of_injective (f := φ) _ _ hinj,
    mL, mP₂] at k₃
  have hHg : H g = (resCard k : ℝ) ^ (-(s.card : ℤ)) := by
    rw [hgeq, (hH.1 κ' hκ' _).2, (hH.1 κ hκ _).1, hH.2]
    congr 2
    unfold sumAbs indic
    rw [Finset.sum_congr rfl (fun i _ => show |(if i ∈ s then (1:ℤ) else 0)| = if i ∈ s then 1 else 0 by split_ifs <;> simp)]
    simp
  rw [hHg] at k₃

  have t₁ := AddSubgroup.relIndex_mul_relIndex (Lm ⊓ large₂) (Lm ⊓ L) Lm (inf_le_inf_left _ hLgL) inf_le_left
  have t₂ := AddSubgroup.relIndex_mul_relIndex (Lm ⊓ large₂) large₂ L inf_le_right hLgL
  have t₃ := AddSubgroup.relIndex_mul_relIndex (Lm ⊓ large₂) (Lm ⊓ L) L (inf_le_inf_left _ hLgL) inf_le_right
  have hQ : (large₂.relIndex L : ℝ) = (resCard k : ℝ) ^ s.card := by
    have hne : (resCard k : ℝ) ^ (-(s.card : ℤ)) ≠ 0 := by positivity
    have hne' : (resCard k : ℝ) ^ s.card ≠ 0 := by positivity
    rw [_root_.zpow_neg, zpow_natCast, Nat.cast_one, mul_one, inv_mul_eq_one₀ hne'] at k₃
    exact k₃.symm
  have e1 : (((Lm ⊓ large₂).relIndex Lm : ℕ) : ℝ) = ((Lm ⊓ large₂).relIndex (Lm ⊓ L) : ℕ) * ((Lm ⊓ L).relIndex Lm : ℕ) := by
    rw [← t₁]; push_cast; ring
  have e2 : (resCard k : ℝ) ^ s.card * (((Lm ⊓ large₂).relIndex large₂ : ℕ) : ℝ) = ((Lm ⊓ large₂).relIndex (Lm ⊓ L) : ℕ) * ((Lm ⊓ L).relIndex L : ℕ) := by
    rw [← hQ]
    have := congrArg (fun n : ℕ => (n : ℝ)) (t₂.trans t₃.symm)
    push_cast at this
    linarith
  linear_combination (-(((Lm ⊓ large₂).relIndex (Lm ⊓ L) : ℕ) : ℝ) ^ 2 * H (m * g)) * k₁ + ((resCard k : ℝ) ^ s.card * H m) * k₂
    + (-(H m * H (m * g) * (resCard k : ℝ) ^ s.card * (((Lm ⊓ large₂).relIndex large₂ : ℕ) : ℝ))) * e1
    + (-(H m * H (m * g) * (((Lm ⊓ large₂).relIndex (Lm ⊓ L) : ℕ) : ℝ) * (((Lm ⊓ L).relIndex Lm : ℕ) : ℝ))) * e2

end GlobalTheory.HeckeLatIndex
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedHeightLatticeIndexIdentityStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
open GlobalTheory.HeckeLatIndex in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedHeight_lattice_index_identity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (D : Type) [Fintype D] [DecidableEq D] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ H : GL D k → ℝ, IsHgt ϖ H → ∀ (m g : GL D k) (s : Finset D), (∃ κ ∈ KO k D, ∃ κ' ∈ KO k D, g = κ * torusElt k D ϖ (indic s) * κ') → ∀ (L Lm large₂ : AddSubgroup (D → k)), (∀ v, v ∈ L ↔ ∀ i, valuation k (v i) < 1) → (∀ v, v ∈ Lm ↔ m.1.mulVec v ∈ L) → (∀ v, v ∈ large₂ ↔ (g⁻¹).1.mulVec v ∈ L) → (((Lm ⊓ large₂).relIndex (Lm ⊓ L) : ℕ) : ℝ) ^ 2 * H (m * g) = (resCard k : ℝ) ^ s.card * H m := by
  exact @_root_.GlobalTheory.HeckeLatIndex.index_identity
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerBlockCoefficientIsSphericalHeckeEigen
noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke GlobalTheory.LowerHecke
open Classical

namespace GlobalTheory.LowerHeckeEig

theorem esymm_map_mul_right' (t : ℂ) (M : Multiset ℂ) (j : ℕ) :
    (M.map fun b => b * t).esymm j = t ^ j * M.esymm j := by
  unfold Multiset.esymm
  rw [Multiset.powersetCard_map, Multiset.map_map, ← Multiset.sum_map_mul_left]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun s hs => ?_)
  have hc := (Multiset.mem_powersetCard.1 hs).2
  simp only [Function.comp, Multiset.prod_map_mul, Multiset.map_id', Multiset.map_const', Multiset.prod_replicate, hc]
  ring

theorem det_torus_indic {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {D : Type} [Fintype D] [DecidableEq D] (ϖ : kˣ) (s : Finset D) :
    GeneralLinearGroup.det (torusElt k D ϖ (indic s)) = ϖ ^ s.card := by
  ext
  rw [GeneralLinearGroup.val_det_apply, val_torusElt, det_diagonal, Units.val_pow_eq_pow_val]
  simp only [indic]
  simp only [apply_ite (fun n : ℤ => (ϖ : k) ^ n), zpow_one, zpow_zero]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

theorem genVal_shift (q a N : ℕ) (B : Multiset ℂˣ) (u : ℂˣ) (n : ℕ) :
    genVal q a N B n = genVal q 0 N (B.map (· * u⁻¹)) n * ((u : ℂ) ^ n * ((Real.sqrt q : ℝ) : ℂ) ^ (a * n)) := by
  have e : (B.map (· * u⁻¹)).map (fun b : ℂˣ => (b : ℂ)) =
      (B.map (fun b : ℂˣ => (b : ℂ))).map (fun z => z * ((u⁻¹ : ℂˣ) : ℂ)) := by
    simp [Multiset.map_map, Function.comp_def]
  simp only [genVal, e, esymm_map_mul_right', zero_mul, zero_add, pow_add, Units.val_inv_eq_inv_val, inv_pow]
  have := u.ne_zero
  field_simp

theorem realKey (a n : ℕ) (c q Hm Hmg : ℝ) (hc : 0 < c) (hq0 : 0 < q) (hq : c ^ 2 * Hmg = q ^ n * Hm)
    (h : a = 0 ∨ 0 < Hm) : (c * Real.sqrt Hmg) ^ a = (Real.sqrt q ^ n * Real.sqrt Hm) ^ a ∧ Real.sqrt Hmg ^ a ≠ 0 := by
  rcases h with h0 | hpos
  · simp [h0]
  · have hHmg : 0 < Hmg := by
      by_contra hle
      push_neg at hle
      have h3 : c ^ 2 * Hmg ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hle
      have h4 : 0 < q ^ n * Hm := mul_pos (pow_pos hq0 _) hpos
      linarith
    refine ⟨congrArg (· ^ a) ?_, pow_ne_zero _ (Real.sqrt_pos.2 hHmg).ne'⟩
    refine (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).1 ?_
    rw [mul_pow, mul_pow, Real.sq_sqrt hHmg.le, Real.sq_sqrt hpos.le, ← pow_mul, mul_comm n 2, pow_mul,
      Real.sq_sqrt hq0.le, hq]

theorem realNeg (n : ℕ) (c q Hm Hmg : ℝ) (hc : 0 < c) (hq0 : 0 ≤ q) (hq : c ^ 2 * Hmg = q ^ n * Hm)
    (h : Hm ≤ 0) : Hmg ≤ 0 := by
  by_contra hlt
  push_neg at hlt
  have h3 : 0 < c ^ 2 * Hmg := mul_pos (pow_pos hc 2) hlt
  have h4 : q ^ n * Hm ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hq0 _) h
  linarith

theorem alg1 (fmg P r ξm ξκ ξn ξκ' C : ℂ) (hr : r ≠ 0) (h1 : ξm ≠ 0) (h2 : ξκ ≠ 0) (h3 : ξn ≠ 0) (h4 : ξκ' ≠ 0)
    (hf : fmg = (ξm * (ξκ * (ξn * ξκ')))⁻¹ * P / r) :
    fmg * (ξn * ξm * (C * r)) = ξκ⁻¹ * (C * (ξκ'⁻¹ * P)) := by
  subst hf
  field_simp

theorem alg2 (S P lam0 ξn ξm Q Sg : ℂ) (h1 : ξn ≠ 0) (h2 : ξm ≠ 0) (h3 : Q ≠ 0) (h4 : Sg ≠ 0)
    (h : S * (ξn * ξm * (Q * Sg)) = lam0 * (ξn * Q) * P) : S = lam0 * (ξm⁻¹ * P / Sg) := by
  have hnq : ξn * Q ≠ 0 := mul_ne_zero h1 h3
  field_simp
  apply mul_left_cancel₀ hnq
  linear_combination h

theorem coeff_isEigen : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (ξ : kˣ →* ℂˣ), IsTame ξ → ¬ IsUnram ξ → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (A ⊕ D) k) V) (B : Multiset ℂˣ) (x : V) (ℓ : V →ₗ[ℂ] ℂ), IsGen π ξ ϖ B x → IsCoType π ξ ℓ → ∀ H : GL D k → ℝ, IsHgt ϖ H → ∀ f : GL D k → ℂ, (∀ m, f m = (((ξ (GeneralLinearGroup.det m))⁻¹ : ℂˣ) : ℂ) * ℓ (π (emb₂ k (Equiv.refl (A ⊕ D)) (1, m)) x) / ((Real.sqrt (H m) : ℝ) : ℂ) ^ Fintype.card A) → (∀ κ ∈ KO k D, ∀ m, f (κ * m) = f m ∧ f (m * κ) = f m) ∧ ∀ (s : Finset D) R, IsRepsK (torusElt k D ϖ (indic s)) R → ∀ m, ∑ g ∈ R, f (m * g) = genVal (resCard k) 0 (Fintype.card D) (B.map (· * (ξ ϖ)⁻¹)) s.card * f m := by
  intro k _ _ _ _ A D _ _ _ _ ϖ hϖ ξ hξt hξu V _ _ π B x ℓ hgen hco H hH f hf
  have hbi : IsBiType ξ (fun h => ℓ (π h x)) := by
    intro j hj d hd g
    constructor
    · show ℓ (π (j * g) x) = _
      rw [map_mul, Module.End.mul_apply]
      exact hco j hj d hd _
    · show ℓ (π (g * j) x) = _
      rw [map_mul, Module.End.mul_apply, hgen.1 j hj d hd, map_smul, map_smul, smul_eq_mul]
  have hdet : ∀ κ : GL D k, ((GeneralLinearGroup.det κ : kˣ) : k) = (emb₂ k (Equiv.refl (A ⊕ D)) (1, κ)).1.toBlocks₂₂.det := by
    intro κ
    rw [val_emb_one, toBlocks_fromBlocks₂₂, GeneralLinearGroup.val_det_apply]
  have hφL : ∀ κ ∈ KO k D, ∀ m, ℓ (π (emb₂ k (Equiv.refl (A ⊕ D)) (1, κ * m)) x) =
      (ξ (GeneralLinearGroup.det κ) : ℂ) * ℓ (π (emb₂ k (Equiv.refl (A ⊕ D)) (1, m)) x) := by
    intro κ hκ m
    rw [← emb_mul_emb]
    exact (hbi _ (emb_mem hκ) _ (hdet κ) _).1
  have hφR : ∀ κ ∈ KO k D, ∀ m, ℓ (π (emb₂ k (Equiv.refl (A ⊕ D)) (1, m * κ)) x) =
      (ξ (GeneralLinearGroup.det κ) : ℂ) * ℓ (π (emb₂ k (Equiv.refl (A ⊕ D)) (1, m)) x) := by
    intro κ hκ m
    rw [← emb_mul_emb]
    exact (hbi _ (emb_mem hκ) _ (hdet κ) _).2
  refine ⟨fun κ hκ m => ⟨?_, ?_⟩, fun s R hR m => ?_⟩
  · rw [hf, hf, hφL κ hκ m, (hH.1 κ hκ m).1, map_mul, map_mul]
    have := (ξ (GeneralLinearGroup.det κ)).ne_zero
    push_cast
    field_simp
  · rw [hf, hf, hφR κ hκ m, (hH.1 κ hκ m).2, map_mul, map_mul]
    have := (ξ (GeneralLinearGroup.det κ)).ne_zero
    push_cast
    field_simp
  · set w := torusElt k D ϖ (indic s) with hw
    choose! κc hκc κ'c hκ'c hgκ using hR.1
    have hdec : ∀ g ∈ R, ∃ κ ∈ KO k D, ∃ κ' ∈ KO k D, g = κ * w * κ' :=
      fun g hg => ⟨_, hκc g hg, _, hκ'c g hg, hgκ g hg⟩
    choose! N hN using fun g hg => GlobalTheory.T.exists_finset_reps_maximalIdealMatrix_mod_mul k A D ϖ hϖ s g (hdec g hg)
    obtain ⟨R', hrep, hsum⟩ := GlobalTheory.T.lowerUnipotent_diag_doubleCoset_representatives k A D ϖ hϖ s R hR κc κ'c
      (fun g hg => ⟨hκc g hg, hκ'c g hg, hgκ g hg⟩) N hN
    have heig := hgen.2.2 s R' blockDet hrep
    set E := fun m : GL D k => emb₂ k (Equiv.refl (A ⊕ D)) (1, m) with hE
    set φ : GL (A ⊕ D) k → ℂ := fun h => ℓ (π h x) with hφ
    have hφR' : ∀ κ ∈ KO k D, ∀ m, φ (E (m * κ)) = (ξ (GeneralLinearGroup.det κ) : ℂ) * φ (E m) := hφR
    set c : GL D k → ℕ := fun g => (preLat m.1 ⊓ preLat (g⁻¹).1).relIndex (preLat m.1 ⊓ mLat k D) with hc
    set lamA := genVal (resCard k) (Fintype.card A) (Fintype.card D) B s.card with hlamA
    have e0 : ∀ J, ℓ (π (E m) (π J x)) = φ (E m * J) := fun J => by simp only [hφ, map_mul, Module.End.mul_apply]
    have h1 : lamA * φ (E m) = ∑ j ∈ R', (((ξ (blockDet j))⁻¹ : ℂˣ) : ℂ) * φ (E m * (j * mtor ϖ (indic s))) := by
      have := congrArg (fun v => ℓ (π (E m) v)) heig
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, smul_eq_mul] at this
      simp only [← e0]
      exact this
    have hterm : ∀ g ∈ R, ∑ ν ∈ N g, (((ξ (blockDet (lowU ν * E (κc g))))⁻¹ : ℂˣ) : ℂ) *
        φ (E m * (lowU ν * E (κc g) * mtor ϖ (indic s))) =
        (((ξ (GeneralLinearGroup.det (κc g)))⁻¹ : ℂˣ) : ℂ) * ((c g : ℂ) ^ Fintype.card A *
          ((ξ (GeneralLinearGroup.det (κ'c g)⁻¹) : ℂ) * φ (E (m * g)))) := by
      intro g hg
      have hy : m * κc g * w = m * g * (κ'c g)⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq]
        calc m * κc g * w * κ'c g = m * (κc g * w * κ'c g) := by group
          _ = m * g := by rw [← hgκ g hg]
      have hcnt := (GlobalTheory.T.card_filter_lowerHecke_reps_eq_relIndex_pow k A D ϖ hϖ s m g (m * κc g * w) (hdec g hg) ⟨_, inv_mem (hκ'c g hg), hy⟩ (N g)
        (hN g hg)).1
      have e1 : ∀ ν : Matrix D A k, E m * (lowU ν * E (κc g) * mtor ϖ (indic s)) = lowU (m.1 * ν) * E (m * κc g * w) := by
        intro ν
        simp only [hE]
        rw [mtor_eq, ← mul_assoc, ← mul_assoc, emb_mul_lowU, mul_assoc (lowU _), emb_mul_emb, mul_assoc (lowU _),
          emb_mul_emb]
      have hb : ∀ (ν : Matrix D A k) (κ : GL D k), blockDet (lowU ν * E κ) = GeneralLinearGroup.det κ :=
        fun ν κ => blockDet_lowU_emb ν κ
      simp only [hb, e1]
      have hs : ∀ (ν : Matrix D A k) (y : GL D k), φ (lowU ν * E y) = if ∃ ν₁ ν₂ : Matrix D A k, (∀ i a, valuation k (ν₁ i a) < 1) ∧
          (∀ i a, valuation k (ν₂ i a) < 1) ∧ ν = ν₁ + y.1 * ν₂ then φ (E y) else 0 :=
        fun ν y => GlobalTheory.T.parahoricBiTransforming_lowerUnipotent_diag_value k A D ξ hξt hξu φ hbi ν y
      simp only [hs, mul_ite, mul_zero]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, hcnt]
      rw [hy, hφR' _ (inv_mem (hκ'c g hg))]
      simp only [hc]
      push_cast
      ring
    have hf' : ∀ m, f m = (((ξ (GeneralLinearGroup.det m))⁻¹ : ℂˣ) : ℂ) * φ (E m) / ((Real.sqrt (H m) : ℝ) : ℂ) ^ Fintype.card A := hf
    have h2 : lamA * φ (E m) = ∑ g ∈ R, (((ξ (GeneralLinearGroup.det (κc g)))⁻¹ : ℂˣ) : ℂ) * ((c g : ℂ) ^ Fintype.card A *
          ((ξ (GeneralLinearGroup.det (κ'c g)⁻¹) : ℂ) * φ (E (m * g)))) :=
      h1.trans ((hsum _).trans (Finset.sum_congr rfl hterm))
    have hqc : ∀ g ∈ R, ((c g : ℕ) : ℝ) ^ 2 * H (m * g) = (resCard k : ℝ) ^ s.card * H m := fun g hg =>
      GlobalTheory.T.unramifiedHeight_lattice_index_identity k D ϖ hϖ H hH m g s (hdec g hg) (mLat k D) (preLat m.1) (preLat (g⁻¹).1) (fun _ => Iff.rfl)
        (fun _ => Iff.rfl) (fun _ => Iff.rfl)
    have hcpos : ∀ g ∈ R, (0 : ℝ) < c g := by
      intro g hg
      have hy : m * κc g * w = m * g * (κ'c g)⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq]
        calc m * κc g * w * κ'c g = m * (κc g * w * κ'c g) := by group
          _ = m * g := by rw [← hgκ g hg]
      exact_mod_cast (GlobalTheory.T.card_filter_lowerHecke_reps_eq_relIndex_pow k A D ϖ hϖ s m g (m * κc g * w) (hdec g hg) ⟨_, inv_mem (hκ'c g hg), hy⟩ (N g) (hN g hg)).2
    have hdg : ∀ g ∈ R, (ξ (GeneralLinearGroup.det (m * g)) : ℂ) = ξ (GeneralLinearGroup.det m) *
        (ξ (GeneralLinearGroup.det (κc g)) * ((ξ ϖ : ℂ) ^ s.card * ξ (GeneralLinearGroup.det (κ'c g)))) := by
      intro g hg
      conv_lhs => rw [hgκ g hg]
      simp only [hw, map_mul, det_torus_indic, map_pow, Units.val_mul, Units.val_pow_eq_pow_val]
      ring
    have hlam := genVal_shift (resCard k) (Fintype.card A) (Fintype.card D) B (ξ ϖ) s.card
    have hq0' : (0 : ℝ) ≤ resCard k := Nat.cast_nonneg _
    by_cases hcase : Fintype.card A = 0 ∨ 0 < H m
    · have hq0 : (0 : ℝ) < resCard k := by
        have : 0 < resCard k := Nat.card_pos
        exact_mod_cast this
      have hσ : ((Real.sqrt (H m) : ℝ) : ℂ) ^ Fintype.card A ≠ 0 := by
        rcases hcase with h0 | hpos
        · simp [h0]
        · exact pow_ne_zero _ (Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hpos).ne')
      have hQ : ((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (Fintype.card A * s.card) ≠ 0 :=
        pow_ne_zero _ (Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hq0).ne')
      have hgU : ∀ g ∈ R, f (m * g) * ((ξ ϖ : ℂ) ^ s.card * ξ (GeneralLinearGroup.det m) *
          (((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (Fintype.card A * s.card) * ((Real.sqrt (H m) : ℝ) : ℂ) ^ Fintype.card A)) =
          (((ξ (GeneralLinearGroup.det (κc g)))⁻¹ : ℂˣ) : ℂ) *
          ((c g : ℂ) ^ Fintype.card A * ((ξ (GeneralLinearGroup.det (κ'c g)⁻¹) : ℂ) * φ (E (m * g)))) := by
        intro g hg
        obtain ⟨h6, h7⟩ := realKey (Fintype.card A) s.card (c g) (resCard k) (H m) (H (m * g)) (hcpos g hg) hq0
          (hqc g hg) hcase
        have h8 : ((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (Fintype.card A * s.card) * ((Real.sqrt (H m) : ℝ) : ℂ) ^ Fintype.card A =
            (c g : ℂ) ^ Fintype.card A * ((Real.sqrt (H (m * g)) : ℝ) : ℂ) ^ Fintype.card A := by
          have h9 : Real.sqrt (resCard k) ^ (Fintype.card A * s.card) * Real.sqrt (H m) ^ Fintype.card A =
              (c g : ℝ) ^ Fintype.card A * Real.sqrt (H (m * g)) ^ Fintype.card A := by
            rw [← mul_pow, h6, mul_pow, ← pow_mul, mul_comm s.card]
          exact_mod_cast h9
        have h10 : ((Real.sqrt (H (m * g)) : ℝ) : ℂ) ^ Fintype.card A ≠ 0 := by exact_mod_cast h7
        rw [h8]
        simp only [map_inv, Units.val_inv_eq_inv_val]
        refine alg1 _ _ _ _ _ _ _ _ h10 (ξ _).ne_zero (ξ _).ne_zero (pow_ne_zero _ (ξ ϖ).ne_zero) (ξ _).ne_zero ?_
        rw [hf' (m * g), Units.val_inv_eq_inv_val, hdg g hg]
      have hS := Finset.sum_mul R (fun g => f (m * g)) ((ξ ϖ : ℂ) ^ s.card * ξ (GeneralLinearGroup.det m) *
          (((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (Fintype.card A * s.card) * ((Real.sqrt (H m) : ℝ) : ℂ) ^ Fintype.card A))
      rw [Finset.sum_congr rfl hgU, ← h2, hlamA, hlam] at hS
      rw [hf' m, Units.val_inv_eq_inv_val]
      exact alg2 _ _ _ _ _ _ _ (pow_ne_zero _ (ξ ϖ).ne_zero) (ξ _).ne_zero hQ hσ (by rw [hS])
    · push_neg at hcase
      obtain ⟨ha, hle⟩ := hcase
      have hz : ∀ m', H m' ≤ 0 → f m' = 0 := by
        intro m' h
        rw [hf' m', Real.sqrt_eq_zero'.2 h, Complex.ofReal_zero, zero_pow ha, div_zero]
      rw [hz m hle, mul_zero]
      exact Finset.sum_eq_zero fun g hg => hz _ (realNeg s.card (c g) (resCard k) (H m) (H (m * g)) (hcpos g hg) hq0'
        (hqc g hg) hle)

end GlobalTheory.LowerHeckeEig

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerBlockCoefficientIsSphericalHeckeEigenStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowerBlockCoefficient_isSphericalHeckeEigen : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (ξ : kˣ →* ℂˣ), IsTame ξ → ¬ IsUnram ξ → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (A ⊕ D) k) V) (B : Multiset ℂˣ) (x : V) (ℓ : V →ₗ[ℂ] ℂ), IsGen π ξ ϖ B x → IsCoType π ξ ℓ → ∀ H : GL D k → ℝ, IsHgt ϖ H → ∀ f : GL D k → ℂ, (∀ m, f m = (((ξ (GeneralLinearGroup.det m))⁻¹ : ℂˣ) : ℂ) * ℓ (π (emb₂ k (Equiv.refl (A ⊕ D)) (1, m)) x) / ((Real.sqrt (H m) : ℝ) : ℂ) ^ Fintype.card A) → (∀ κ ∈ KO k D, ∀ m, f (κ * m) = f m ∧ f (m * κ) = f m) ∧ ∀ (s : Finset D) R, IsRepsK (torusElt k D ϖ (indic s)) R → ∀ m, ∑ g ∈ R, f (m * g) = genVal (resCard k) 0 (Fintype.card D) (B.map (· * (ξ ϖ)⁻¹)) s.card * f m := by
  first | exact @GlobalTheory.LowerHeckeEig.coeff_isEigen | exact GlobalTheory.LowerHeckeEig.coeff_isEigen | (intros; apply GlobalTheory.LowerHeckeEig.coeff_isEigen <;> assumption)
end
