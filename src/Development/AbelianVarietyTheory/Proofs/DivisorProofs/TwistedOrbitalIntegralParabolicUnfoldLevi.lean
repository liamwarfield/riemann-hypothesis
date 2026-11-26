module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralSemidirectProductUnfolding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsLocEqOfIsLocComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteParabolicDoubleCosetsOrbitalIntegral

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockUpperParabolicLeviProjectionUnipotent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockUpperParabolicLeviProjectionUnipotent
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LeviDesc.LeviHoms

variable {E : Type} [Field E] [NumberField E] {n a b : ℕ} (h : a + b = n) (w : Pl E)

def ix : Fin a ⊕ Fin b ≃ Fin n := finSumFinEquiv.trans (finCongr h)

theorem ix_inl_val (x : Fin a) : ((ix h (Sum.inl x) : Fin n) : ℕ) = x := by simp [ix]

theorem ix_inr_val (x : Fin b) : ((ix h (Sum.inr x) : Fin n) : ℕ) = a + x := by simp [ix]

theorem ext_ix {R : Type} {M N : Matrix (Fin n) (Fin n) R}
    (H : ∀ P Q, M (ix h P) (ix h Q) = N (ix h P) (ix h Q)) : M = N := by
  ext i j
  obtain ⟨P, rfl⟩ := (ix h).surjective i
  obtain ⟨Q, rfl⟩ := (ix h).surjective j
  exact H P Q

theorem mem_parabolic_iff (g : GLw n w) :
    g ∈ parP a n w ↔ ∀ i j, g.val (ix h (Sum.inr i)) (ix h (Sum.inl j)) = 0 := by
  constructor
  · intro hg i j
    apply hg
    have h1 : ¬ a ≤ (j : ℕ) := Nat.not_le.2 j.isLt
    simp only [ix_inl_val, ix_inr_val]
    simp [h1]
  · intro H i j hij
    obtain ⟨P, rfl⟩ := (ix h).surjective i
    obtain ⟨Q, rfl⟩ := (ix h).surjective j
    rcases P with x | x <;> rcases Q with y | y
    · have h1 : ¬ a ≤ (x : ℕ) := Nat.not_le.2 x.isLt
      simp only [ix_inl_val] at hij
      simp [h1] at hij
      exact absurd hij (by cases decide (a ≤ (y : ℕ)) <;> decide)
    · simp only [ix_inl_val, ix_inr_val] at hij
      simp at hij
      exact absurd hij (by cases decide (a ≤ (x : ℕ)) <;> decide)
    · exact H x y
    · simp only [ix_inr_val] at hij
      simp at hij

theorem blk_apply (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) (P Q : Fin a ⊕ Fin b) :
    (blk h w m X).val (ix h P) (ix h Q) = Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val P Q := by
  rw [UnipMean.blk_val]
  simp [ix]

theorem toBlocks₁₁_mul {R α β : Type} [CommRing R] [Fintype α] [Fintype β] (M N : Matrix (α ⊕ β) (α ⊕ β) R)
    (hN : N.toBlocks₂₁ = 0) : (M * N).toBlocks₁₁ = M.toBlocks₁₁ * N.toBlocks₁₁ := by
  ext i j
  have := fun y => congrFun (congrFun hN y) j
  simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply] at this
  simp [Matrix.toBlocks₁₁, Matrix.mul_apply, Fintype.sum_sum_type, this]

theorem toBlocks₂₂_mul {R α β : Type} [CommRing R] [Fintype α] [Fintype β] (M N : Matrix (α ⊕ β) (α ⊕ β) R)
    (hM : M.toBlocks₂₁ = 0) : (M * N).toBlocks₂₂ = M.toBlocks₂₂ * N.toBlocks₂₂ := by
  ext i j
  have := fun y => congrFun (congrFun hM i) y
  simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply] at this
  simp [Matrix.toBlocks₂₂, Matrix.mul_apply, Fintype.sum_sum_type, this]

theorem toBlocks₂₁_of_mem (p : parP a n w) :
    ((p : GLw n w).val.submatrix (ix h) (ix h)).toBlocks₂₁ = 0 := by
  exact Matrix.ext fun i j => (mem_parabolic_iff h w _).1 p.2 i j

def dgH : parP a n w →* Matrix (Fin a) (Fin a) (w.adicCompletion E) × Matrix (Fin b) (Fin b) (w.adicCompletion E) where
  toFun p := (((p : GLw n w).val.submatrix (ix h) (ix h)).toBlocks₁₁, ((p : GLw n w).val.submatrix (ix h) (ix h)).toBlocks₂₂)
  map_one' := by
    refine Prod.ext (Matrix.ext fun i j => ?_) (Matrix.ext fun i j => ?_) <;>
      simp [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.one_apply]
  map_mul' p q := by
    have e : ((p * q : parP a n w) : GLw n w).val.submatrix (ix h) (ix h) =
        (p : GLw n w).val.submatrix (ix h) (ix h) * (q : GLw n w).val.submatrix (ix h) (ix h) := by
      rw [Matrix.submatrix_mul_equiv]; rfl
    simp only [e, Prod.mk_mul_mk]
    rw [toBlocks₁₁_mul _ _ (toBlocks₂₁_of_mem h w q), toBlocks₂₂_mul _ _ (toBlocks₂₁_of_mem h w p)]

def sH : GLw a w × GLw b w →* parP a n w where
  toFun m := ⟨blk h w m 0, (mem_parabolic_iff h w _).2 fun i j => by rw [blk_apply]; rfl⟩
  map_one' := Subtype.ext (UnipMean.blk_one_zero h w)
  map_mul' m m' := by
    apply Subtype.ext
    ext1
    simp only [Subgroup.coe_mul, Units.val_mul, UnipMean.blk_val, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
      Matrix.fromBlocks_multiply, Prod.fst_mul, Prod.snd_mul, Units.val_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero,
      zero_add]

def piH : parP a n w →* GLw a w × GLw b w :=
  MulEquiv.prodUnits.toMonoidHom.comp ((Units.map (dgH h w)).comp (toUnits : parP a n w ≃* (parP a n w)ˣ).toMonoidHom)

theorem piH_fst_val (p : parP a n w) :
    ((piH h w p).1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) =
      ((p : GLw n w).val.submatrix (ix h) (ix h)).toBlocks₁₁ := rfl

theorem piH_snd_val (p : parP a n w) :
    ((piH h w p).2 : Matrix (Fin b) (Fin b) (w.adicCompletion E)) =
      ((p : GLw n w).val.submatrix (ix h) (ix h)).toBlocks₂₂ := rfl

def uH : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) →* parP a n w where
  toFun X := ⟨blk h w 1 (Multiplicative.toAdd X), (mem_parabolic_iff h w _).2 fun i j => by rw [blk_apply]; rfl⟩
  map_one' := Subtype.ext (UnipMean.blk_one_zero h w)
  map_mul' X Y := Subtype.ext (by simp only [toAdd_mul, Subgroup.coe_mul]; exact UnipMean.blk_add h w 1 _ _)

theorem piH_sH (m : GLw a w × GLw b w) : piH h w (sH h w m) = m := by
  refine Prod.ext (Units.ext ?_) (Units.ext ?_)
  · rw [piH_fst_val]; exact Matrix.ext fun i j => by simp [Matrix.toBlocks₁₁, sH, blk_apply]
  · rw [piH_snd_val]; exact Matrix.ext fun i j => by simp [Matrix.toBlocks₂₂, sH, blk_apply]

theorem uH_injective : Function.Injective (uH h w) := by
  intro X Y hXY
  have := congrArg (fun p : parP a n w => UnipMean.corner h w 1 (p : GLw n w)) hXY
  simpa [uH, UnipMean.corner_blk] using this

theorem piH_eq_one_iff (p : parP a n w) : piH h w p = 1 ↔ ∃ X, uH h w X = p := by
  constructor
  · intro hp
    have h1 := congrArg (fun q : GLw a w × GLw b w => (q.1 : Matrix (Fin a) (Fin a) (w.adicCompletion E))) hp
    have h2 := congrArg (fun q : GLw a w × GLw b w => (q.2 : Matrix (Fin b) (Fin b) (w.adicCompletion E))) hp
    simp only [piH_fst_val, piH_snd_val, Prod.fst_one, Prod.snd_one, Units.val_one] at h1 h2
    refine ⟨Multiplicative.ofAdd ((p : GLw n w).val.submatrix (ix h) (ix h)).toBlocks₁₂, ?_⟩
    apply Subtype.ext; ext1
    refine ext_ix h fun P Q => ?_
    simp only [uH, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
    rw [blk_apply]
    rcases P with x | x <;> rcases Q with y | y
    · have := congrFun (congrFun h1 x) y
      simp only [Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.submatrix_apply] at this
      simp [this]
    · simp [Matrix.toBlocks₁₂]
    · simp [(mem_parabolic_iff h w _).1 p.2 x y]
    · have := congrFun (congrFun h2 x) y
      simp only [Matrix.toBlocks₂₂, Matrix.of_apply, Matrix.submatrix_apply] at this
      simp [this]
  · rintro ⟨X, rfl⟩
    refine Prod.ext (Units.ext ?_) (Units.ext ?_)
    · rw [piH_fst_val]; exact Matrix.ext fun i j => by simp [Matrix.toBlocks₁₁, uH, blk_apply]
    · rw [piH_snd_val]; exact Matrix.ext fun i j => by simp [Matrix.toBlocks₂₂, uH, blk_apply]

theorem mem_intMat_iff (X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) :
    X ∈ intMat a b w ↔ ∀ i j, Valued.v (Multiplicative.toAdd X i j) ≤ 1 := by
  let T : Subgroup (Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) :=
    { carrier := {X | ∀ i j, Valued.v (Multiplicative.toAdd X i j) ≤ 1}
      one_mem' := fun i j => by simp
      mul_mem' := fun {x y} hx hy i j => by
        simp only [Set.mem_setOf_eq, toAdd_mul, Matrix.add_apply] at *
        exact Valuation.map_add_le _ (hx i j) (hy i j)
      inv_mem' := fun {x} hx i j => by
        simp only [Set.mem_setOf_eq, toAdd_inv, Matrix.neg_apply, Valuation.map_neg] at *
        exact hx i j }
  have e : intMat a b w = T :=
    le_antisymm ((Subgroup.closure_le _).2 fun x hx => hx) fun x hx => Subgroup.subset_closure hx
  rw [e]
  rfl

theorem ent_iff {M : Matrix (Fin n) (Fin n) (w.adicCompletion E)} :
    (∀ i j, Valued.v (M i j) ≤ 1) ↔ ∀ P Q, Valued.v (M (ix h P) (ix h Q)) ≤ 1 := by
  constructor
  · intro H P Q; exact H _ _
  · intro H i j
    obtain ⟨P, rfl⟩ := (ix h).surjective i
    obtain ⟨Q, rfl⟩ := (ix h).surjective j
    exact H P Q

theorem one_ent {k : Type} [Fintype k] [DecidableEq k] (i j : k) :
    Valued.v ((1 : Matrix k k (w.adicCompletion E)) i j) ≤ 1 := by
  rw [Matrix.one_apply]; split_ifs <;> simp

theorem blk_ent (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E))
    (H1 : ∀ i j, Valued.v (m.1.val i j) ≤ 1) (H2 : ∀ i j, Valued.v (m.2.val i j) ≤ 1)
    (HX : ∀ i j, Valued.v ((m.1.val * X) i j) ≤ 1) : ∀ i j, Valued.v ((blk h w m X).val i j) ≤ 1 := by
  rw [ent_iff h w]
  intro P Q
  rw [blk_apply]
  rcases P with x | x <;> rcases Q with y | y
  · simpa using H1 x y
  · simpa using HX x y
  · simp
  · simpa using H2 x y

theorem sH_mem (k : GLw a w × GLw b w) (hk : k ∈ (GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))) :
    sH h w k ∈ (GlobalTheory.LFun.KGL w (n := n)).subgroupOf (parP a n w) := by
  have mem_KGL (m : ℕ) (g : GLw m w) :
      g ∈ GlobalTheory.LFun.KGL w (n := m) ↔
        (∀ i j, Valued.v (g.val i j) ≤ 1) ∧ ∀ i j, Valued.v ((g⁻¹).val i j) ≤ 1 := by
    have hO : GroundTheory.Automorphic.GLnLocal.integralGL (w.adicCompletion E) m = GlobalTheory.LFun.KGL w (n := m) := by
      have h : (ValuativeRel.valuation (w.adicCompletion E)).integer = Formalism.UG.Ov E w :=
        Subring.ext fun x => GroundTheory.Global.mem_valuationInteger_iff w x
      rw [GlobalTheory.LFun.KGL, ← h]; rfl
    rw [← hO, GroundTheory.Automorphic.GLnLocal.mem_integralGL_iff]
    simp only [GroundTheory.Global.mem_valuationInteger_iff]
    rfl
  rw [Subgroup.mem_subgroupOf, mem_KGL]
  rw [Subgroup.mem_prod, mem_KGL, mem_KGL] at hk
  obtain ⟨⟨a1, a2⟩, b1, b2⟩ := hk
  refine ⟨blk_ent h w k 0 a1 b1 (by simp), ?_⟩
  have e : ((sH h w k : GLw n w))⁻¹ = (sH h w k⁻¹ : GLw n w) := by rw [map_inv]; rfl
  rw [e]
  exact blk_ent h w k⁻¹ 0 a2 b2 (by simp)

theorem piH_mem (k : parP a n w) (hk : k ∈ (GlobalTheory.LFun.KGL w (n := n)).subgroupOf (parP a n w)) :
    piH h w k ∈ (GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b)) := by
  have mem_KGL (m : ℕ) (g : GLw m w) :
      g ∈ GlobalTheory.LFun.KGL w (n := m) ↔
        (∀ i j, Valued.v (g.val i j) ≤ 1) ∧ ∀ i j, Valued.v ((g⁻¹).val i j) ≤ 1 := by
    have hO : GroundTheory.Automorphic.GLnLocal.integralGL (w.adicCompletion E) m = GlobalTheory.LFun.KGL w (n := m) := by
      have h : (ValuativeRel.valuation (w.adicCompletion E)).integer = Formalism.UG.Ov E w :=
        Subring.ext fun x => GroundTheory.Global.mem_valuationInteger_iff w x
      rw [GlobalTheory.LFun.KGL, ← h]; rfl
    rw [← hO, GroundTheory.Automorphic.GLnLocal.mem_integralGL_iff]
    simp only [GroundTheory.Global.mem_valuationInteger_iff]
    rfl
  rw [Subgroup.mem_subgroupOf, mem_KGL] at hk
  obtain ⟨k1, k2⟩ := hk
  have e : (piH h w k)⁻¹ = piH h w k⁻¹ := (map_inv _ _).symm
  rw [Subgroup.mem_prod, mem_KGL, mem_KGL]
  refine ⟨⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_, fun i j => ?_⟩
  · rw [piH_fst_val]; exact k1 (ix h (Sum.inl i)) (ix h (Sum.inl j))
  · rw [← Prod.fst_inv, e, piH_fst_val]; exact k2 (ix h (Sum.inl i)) (ix h (Sum.inl j))
  · rw [piH_snd_val]; exact k1 (ix h (Sum.inr i)) (ix h (Sum.inr j))
  · rw [← Prod.snd_inv, e, piH_snd_val]; exact k2 (ix h (Sum.inr i)) (ix h (Sum.inr j))

theorem uH_mem_iff (X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) :
    uH h w X ∈ (GlobalTheory.LFun.KGL w (n := n)).subgroupOf (parP a n w) ↔ X ∈ intMat a b w := by
  have mem_KGL (m : ℕ) (g : GLw m w) :
      g ∈ GlobalTheory.LFun.KGL w (n := m) ↔
        (∀ i j, Valued.v (g.val i j) ≤ 1) ∧ ∀ i j, Valued.v ((g⁻¹).val i j) ≤ 1 := by
    have hO : GroundTheory.Automorphic.GLnLocal.integralGL (w.adicCompletion E) m = GlobalTheory.LFun.KGL w (n := m) := by
      have h : (ValuativeRel.valuation (w.adicCompletion E)).integer = Formalism.UG.Ov E w :=
        Subring.ext fun x => GroundTheory.Global.mem_valuationInteger_iff w x
      rw [GlobalTheory.LFun.KGL, ← h]; rfl
    rw [← hO, GroundTheory.Automorphic.GLnLocal.mem_integralGL_iff]
    simp only [GroundTheory.Global.mem_valuationInteger_iff]
    rfl
  rw [mem_intMat_iff, Subgroup.mem_subgroupOf, mem_KGL]
  constructor
  · rintro ⟨H, -⟩ i j
    have := H (ix h (Sum.inl i)) (ix h (Sum.inr j))
    simpa [uH, blk_apply] using this
  · intro H
    have e : ((uH h w X : GLw n w))⁻¹ = (uH h w X⁻¹ : GLw n w) := by rw [map_inv]; rfl
    rw [e]
    refine ⟨blk_ent h w 1 _ (fun i j => by simpa using one_ent w i j) (fun i j => by simpa using one_ent w i j)
      (by simpa using H), blk_ent h w 1 _ (fun i j => by simpa using one_ent w i j)
      (fun i j => by simpa using one_ent w i j) (by simpa using H)⟩

end GlobalTheory.LeviDesc.LeviHoms

namespace GlobalTheory.LeviDesc.LeviHoms

theorem levi_homs : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E), ∃ (s : GLw a w × GLw b w →* GlobalTheory.LeviDesc.parP a n w) (π : GlobalTheory.LeviDesc.parP a n w →* GLw a w × GLw b w) (u : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) →* GlobalTheory.LeviDesc.parP a n w), (∀ m, (s m : GLw n w) = blk h w m 0) ∧ (∀ X, (u X : GLw n w) = blk h w 1 (Multiplicative.toAdd X)) ∧ (∀ m, π (s m) = m) ∧ Function.Injective u ∧ (∀ p, π p = 1 ↔ ∃ X, u X = p) ∧ (∀ k ∈ (GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b)), s k ∈ (GlobalTheory.LFun.KGL w (n := n)).subgroupOf (GlobalTheory.LeviDesc.parP a n w)) ∧ (∀ k ∈ (GlobalTheory.LFun.KGL w (n := n)).subgroupOf (GlobalTheory.LeviDesc.parP a n w), π k ∈ (GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))) ∧ (∀ X, u X ∈ (GlobalTheory.LFun.KGL w (n := n)).subgroupOf (GlobalTheory.LeviDesc.parP a n w) ↔ X ∈ intMat a b w) := by
  intro E _ _ n a b h w
  exact ⟨sH h w, piH h w, uH h w, fun m => rfl, fun X => rfl, piH_sH h w, uH_injective h w, piH_eq_one_iff h w,
    fun k hk => sH_mem h w k hk, fun k hk => piH_mem h w k hk, uH_mem_iff h w⟩

end GlobalTheory.LeviDesc.LeviHoms
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockUpperParabolicLeviProjectionUnipotentStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_blockUpperParabolic_levi_projection_unipotent : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E), ∃ (s : GLw a w × GLw b w →* GlobalTheory.LeviDesc.parP a n w) (π : GlobalTheory.LeviDesc.parP a n w →* GLw a w × GLw b w) (u : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) →* GlobalTheory.LeviDesc.parP a n w), (∀ m, (s m : GLw n w) = blk h w m 0) ∧ (∀ X, (u X : GLw n w) = blk h w 1 (Multiplicative.toAdd X)) ∧ (∀ m, π (s m) = m) ∧ Function.Injective u ∧ (∀ p, π p = 1 ↔ ∃ X, u X = p) ∧ (∀ k ∈ (GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b)), s k ∈ (GlobalTheory.LFun.KGL w (n := n)).subgroupOf (GlobalTheory.LeviDesc.parP a n w)) ∧ (∀ k ∈ (GlobalTheory.LFun.KGL w (n := n)).subgroupOf (GlobalTheory.LeviDesc.parP a n w), π k ∈ (GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))) ∧ (∀ X, u X ∈ (GlobalTheory.LFun.KGL w (n := n)).subgroupOf (GlobalTheory.LeviDesc.parP a n w) ↔ X ∈ intMat a b w) := by
  first | exact @GlobalTheory.LeviDesc.LeviHoms.levi_homs | exact GlobalTheory.LeviDesc.LeviHoms.levi_homs | (intros; apply GlobalTheory.LeviDesc.LeviHoms.levi_homs <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompactPartParabolicCentralizerIffBlockDiagon
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompactPartParabolicCentralizerIffBlockDiagon
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LeviDesc.CptLevi

open Topology

section Gen

variable {G M : Type} [Group G] [Group M] [TopologicalSpace G] [TopologicalSpace M]

theorem cptPart_map (j : M →* G) (hj : IsClosedEmbedding j) (T : Subgroup M) :
    cptPart (T.map j) = (cptPart T).map j := by
  unfold cptPart
  rw [MonoidHom.map_closure]
  congr 1
  have hc : ∀ x : M, IsCompact (closure (Subgroup.zpowers (j x) : Set G)) ↔
      IsCompact (closure (Subgroup.zpowers x : Set M)) := by
    intro x
    rw [← MonoidHom.map_zpowers, Subgroup.coe_map, hj.closure_image_eq, ← hj.isInducing.isCompact_iff]
  ext y
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hy⟩
    exact ⟨x, ⟨hx, (hc x).1 hy⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hx'⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, (hc x).2 hx'⟩

theorem isClosedEmbedding_unitsMap {A B : Type} [Monoid A] [Monoid B] [TopologicalSpace A] [TopologicalSpace B]
    [T1Space A] [ContinuousMul A] (f : A →* B) (hf : IsClosedEmbedding f) :
    IsClosedEmbedding (Units.map f) := by
  refine IsClosedEmbedding.of_comp (Units.isEmbedding_embedProduct (M := B)) ?_
  exact (hf.prodMap ((MulOpposite.opHomeomorph.isClosedEmbedding.comp hf).comp
    MulOpposite.opHomeomorph.symm.isClosedEmbedding)).comp Units.isClosedEmbedding_embedProduct

end Gen

section Mat

variable {R : Type} [CommRing R] {n a b : ℕ} (h : a + b = n)

def dHom : Matrix (Fin a) (Fin a) R × Matrix (Fin b) (Fin b) R →* Matrix (Fin n) (Fin n) R where
  toFun p := reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h)) (fromBlocks p.1 0 0 p.2)
  map_one' := by
    simp only [Prod.fst_one, Prod.snd_one, fromBlocks_one, reindex_apply]
    exact submatrix_one_equiv _
  map_mul' p q := by
    simp only [reindex_apply, submatrix_mul_equiv, fromBlocks_multiply, Prod.fst_mul, Prod.snd_mul]
    simp

theorem dHom_apply (p : Matrix (Fin a) (Fin a) R × Matrix (Fin b) (Fin b) R) :
    dHom h p = reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (fromBlocks p.1 0 0 p.2) := rfl

theorem reindex_mul_reindex (e : Fin a ⊕ Fin b ≃ Fin n) (A B : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) R) :
    reindex e e A * reindex e e B = reindex e e (A * B) := by
  simp only [reindex_apply, submatrix_mul_equiv]

theorem dHom_leftInverse : Function.LeftInverse
    (fun z : Matrix (Fin n) (Fin n) R =>
      ((reindex (finSumFinEquiv.trans (finCongr h)).symm (finSumFinEquiv.trans (finCongr h)).symm z).toBlocks₁₁,
        (reindex (finSumFinEquiv.trans (finCongr h)).symm (finSumFinEquiv.trans (finCongr h)).symm z).toBlocks₂₂))
    (dHom h) := fun p => by
  simp only [dHom_apply, ← reindex_symm, Equiv.symm_apply_apply, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₂]

theorem isClosedEmbedding_dHom [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    IsClosedEmbedding (dHom (R := R) h) := by
  refine (dHom_leftInverse h).isClosedEmbedding ?_ ?_
  · have : Continuous fun z : Matrix (Fin n) (Fin n) R =>
        reindex (finSumFinEquiv.trans (finCongr h)).symm (finSumFinEquiv.trans (finCongr h)).symm z :=
      continuous_id.matrix_reindex _ _
    exact (continuous_matrix fun i j => this.matrix_elem _ _).prodMk (continuous_matrix fun i j => this.matrix_elem _ _)
  · exact (continuous_fst.matrix_fromBlocks continuous_const continuous_const continuous_snd).matrix_reindex _ _

def jHom : GL (Fin a) R × GL (Fin b) R →* GL (Fin n) R :=
  (Units.map (dHom h)).comp MulEquiv.prodUnits.symm.toMonoidHom

theorem jHom_val (t : GL (Fin a) R × GL (Fin b) R) : (jHom h t).val = dHom h (t.1.val, t.2.val) := rfl

theorem isClosedEmbedding_jHom [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    IsClosedEmbedding (jHom (R := R) h) :=
  (isClosedEmbedding_unitsMap _ (isClosedEmbedding_dHom h)).comp Homeomorph.prodUnits.symm.isClosedEmbedding

theorem exists_jHom (g : GL (Fin n) R)
    (h12 : (reindex (finSumFinEquiv.trans (finCongr h)).symm (finSumFinEquiv.trans (finCongr h)).symm g.val).toBlocks₁₂ = 0)
    (h21 : (reindex (finSumFinEquiv.trans (finCongr h)).symm (finSumFinEquiv.trans (finCongr h)).symm g.val).toBlocks₂₁ = 0) :
    ∃ t, jHom h t = g := by
  set Q := reindex (finSumFinEquiv.trans (finCongr h)).symm (finSumFinEquiv.trans (finCongr h)).symm g.val with hQdef
  have hQ : Q = fromBlocks Q.toBlocks₁₁ 0 0 Q.toBlocks₂₂ := by
    have := (fromBlocks_toBlocks Q).symm
    rwa [h12, h21] at this
  have hdet : IsUnit Q.det := by
    rw [hQdef, det_reindex_self]
    exact (isUnit_iff_isUnit_det _).1 g.isUnit
  rw [hQ, det_fromBlocks_zero₁₂] at hdet
  have u1 : IsUnit Q.toBlocks₁₁ := (isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_left hdet)
  have u2 : IsUnit Q.toBlocks₂₂ := (isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_right hdet)
  refine ⟨(u1.unit, u2.unit), Units.ext ?_⟩
  rw [jHom_val, dHom_apply]
  simp only [IsUnit.unit_spec]
  rw [← hQ, hQdef, ← reindex_symm, Equiv.apply_symm_apply]

end Mat

variable {E : Type} [Field E] [NumberField E]

theorem blk_eq_jHom {n a b : ℕ} (h : a + b = n) (w : Pl E) (t : GLw a w × GLw b w) : blk h w t 0 = jHom h t := by
  unfold blk
  simp only [Matrix.mul_zero]
  split_ifs with hM
  · exact Units.ext (by rw [IsUnit.unit_spec]; rfl)
  · exact absurd (jHom h t).isUnit hM

theorem twCent_blk_eq {n a b : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (hsep : (m.1.val.charpoly * m.2.val.charpoly).Separable) :
    twCent (MonoidHom.id (GLw n w)) (blk h w m 0) = (twCent (MonoidHom.id _) m).map (jHom h) := by
  have hcop := hsep.isCoprime
  rw [blk_eq_jHom]
  ext g
  constructor
  · intro hg
    have hc : g.val * (jHom h m).val = (jHom h m).val * g.val := by
      have := congrArg Units.val (show g * jHom h m = jHom h m * MonoidHom.id _ g from hg)
      simpa using this
    set e := finSumFinEquiv.trans (finCongr h) with he
    set Q := reindex e.symm e.symm g.val with hQdef
    have hgQ : g.val = reindex e e Q := by simp [hQdef]
    rw [hgQ, jHom_val, dHom_apply, ← fromBlocks_toBlocks Q, reindex_mul_reindex, reindex_mul_reindex] at hc
    have hc2 := (reindex e e).injective hc
    simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at hc2
    rw [Matrix.fromBlocks_inj] at hc2
    have h21 := GlobalTheory.LeviDesc.intertwiner_eq_zero_of_isCoprime _ _ _ hcop hc2.2.2.1
    have h12 := GlobalTheory.LeviDesc.intertwiner_eq_zero_of_isCoprime _ _ _ hcop.symm hc2.2.1
    obtain ⟨t, rfl⟩ := exists_jHom h g h12 h21
    refine ⟨t, ?_, rfl⟩
    show t * m = m * MonoidHom.id _ t
    apply (isClosedEmbedding_jHom h).injective
    have : jHom h t * jHom h m = jHom h m * MonoidHom.id _ (jHom h t) := hg
    simpa [map_mul] using this
  · rintro ⟨t, ht, rfl⟩
    have : t * m = m * t := ht
    show jHom h t * jHom h m = jHom h m * MonoidHom.id _ (jHom h t)
    rw [MonoidHom.id_apply, ← map_mul, ← map_mul, this]

theorem isClosed_parP' (a n : ℕ) (w : Pl E) : IsClosed (GlobalTheory.LeviDesc.parP a n w : Set (GLw n w)) := by
  have : (parP a n w : Set (GLw n w)) = ⋂ i : Fin n, ⋂ j : Fin n,
      {g : GLw n w | decide (a ≤ (j : ℕ)) < decide (a ≤ (i : ℕ)) → (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j = 0} := by
    ext g
    simp only [Set.mem_iInter]
    rfl
  rw [this]
  refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
  by_cases hij : decide (a ≤ (j : ℕ)) < decide (a ≤ (i : ℕ))
  · simp only [hij, true_implies]
    exact isClosed_eq (Continuous.matrix_elem (Units.continuous_val (M := Matrix (Fin n) (Fin n) (w.adicCompletion E))) i j) continuous_const
  · simp only [hij, false_implies, Set.ofPred_true]
    exact isClosed_univ

theorem mem_compactPart_parabolic_iff : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w), (m.1.val.charpoly * m.2.val.charpoly).Separable → ∀ (hγ : blk h w m 0 ∈ GlobalTheory.LeviDesc.parP a n w) (p : GlobalTheory.LeviDesc.parP a n w), p ∈ cptPart (twCent (MonoidHom.id _) (⟨blk h w m 0, hγ⟩ : GlobalTheory.LeviDesc.parP a n w)) ↔ ∃ t ∈ cptPart (twCent (MonoidHom.id _) m), blk h w t 0 = (p : GLw n w) := by
  intro E _ _ n a b h w m hsep hγ p
  have hT := GlobalTheory.LeviDesc.twCent_blk_le_parP E n a b h w m hsep
  rw [← Subgroup.mem_map_iff_mem (f := (parP a n w).subtype) (parP a n w).subtype_injective,
    GlobalTheory.IwRed.cptPart_map_sub _ (isClosed_parP' a n w) _ hγ hT, twCent_blk_eq h w m hsep,
    cptPart_map _ (isClosedEmbedding_jHom h)]
  simp only [Subgroup.mem_map, blk_eq_jHom, Subgroup.coe_subtype]

end GlobalTheory.LeviDesc.CptLevi
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompactPartParabolicCentralizerIffBlockDiagonStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_compactPart_parabolicCentralizer_iff_blockDiagonal : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w), (m.1.val.charpoly * m.2.val.charpoly).Separable → ∀ (hγ : blk h w m 0 ∈ GlobalTheory.LeviDesc.parP a n w) (p : GlobalTheory.LeviDesc.parP a n w), p ∈ cptPart (twCent (MonoidHom.id _) (⟨blk h w m 0, hγ⟩ : GlobalTheory.LeviDesc.parP a n w)) ↔ ∃ t ∈ cptPart (twCent (MonoidHom.id _) m), blk h w t 0 = (p : GLw n w) := by
  first | exact @GlobalTheory.LeviDesc.CptLevi.mem_compactPart_parabolic_iff | exact GlobalTheory.LeviDesc.CptLevi.mem_compactPart_parabolic_iff | (intros; apply GlobalTheory.LeviDesc.CptLevi.mem_compactPart_parabolic_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteIndexLeviSubgroupUnipotentConjIntegr
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteIndexLeviSubgroupUnipotentConjIntegr
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LeviDesc.ConjStab

variable {E : Type} [Field E] [NumberField E]

def dgHom {n a b : ℕ} (h : a + b = n) (w : Pl E) : GLw a w × GLw b w →* GLw n w where
  toFun k := blk h w k 0
  map_one' := by
    ext : 1
    rw [LeviBlockConjugation.blk_val]
    simp only [Prod.fst_one, Prod.snd_one, Units.val_one, Matrix.mul_zero, Matrix.fromBlocks_one, Matrix.reindex_apply]
    exact Matrix.submatrix_one_equiv _
  map_mul' k k' := by
    ext : 1
    simp only [Units.val_mul, LeviBlockConjugation.blk_val, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
      Matrix.fromBlocks_multiply, Prod.fst_mul, Prod.snd_mul]
    simp

theorem continuous_dgHom {n a b : ℕ} (h : a + b = n) (w : Pl E) : Continuous (dgHom (E := E) h w) := by
  rw [Units.continuous_iff]
  constructor
  · have e : (fun k : GLw a w × GLw b w => (dgHom h w k).val) = fun k =>
        Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
          (Matrix.fromBlocks k.1.val (k.1.val * (0 : Matrix (Fin a) (Fin b) (w.adicCompletion E))) 0 k.2.val) := by
      funext k; exact LeviBlockConjugation.blk_val h w k 0
    change Continuous fun k : GLw a w × GLw b w => (dgHom h w k).val
    rw [e]
    exact (Continuous.matrix_fromBlocks (Units.continuous_val.comp continuous_fst)
      ((Units.continuous_val.comp continuous_fst).matrix_mul continuous_const) continuous_const
      (Units.continuous_val.comp continuous_snd)).matrix_reindex _ _
  · have e : (fun k : GLw a w × GLw b w => ((dgHom h w k)⁻¹).val) = fun k =>
        Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
          (Matrix.fromBlocks (k.1⁻¹).val ((k.1⁻¹).val * (0 : Matrix (Fin a) (Fin b) (w.adicCompletion E))) 0 (k.2⁻¹).val) := by
      funext k; rw [← map_inv]; exact LeviBlockConjugation.blk_val h w k⁻¹ 0
    change Continuous fun k : GLw a w × GLw b w => ((dgHom h w k)⁻¹).val
    rw [e]
    exact (Continuous.matrix_fromBlocks (Units.continuous_coe_inv.comp continuous_fst)
      ((Units.continuous_coe_inv.comp continuous_fst).matrix_mul continuous_const) continuous_const
      (Units.continuous_coe_inv.comp continuous_snd)).matrix_reindex _ _

def conjLevi {n a b : ℕ} (h : a + b = n) (w : Pl E) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    GLw a w × GLw b w →* GLw n w :=
  (MulAut.conj (blk h w 1 X)⁻¹).toMonoidHom.comp (dgHom h w)

theorem conjLevi_apply {n a b : ℕ} (h : a + b = n) (w : Pl E) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E))
    (k : GLw a w × GLw b w) : conjLevi h w X k = (blk h w 1 X)⁻¹ * blk h w k 0 * blk h w 1 X := by
  simp [conjLevi, dgHom, MulAut.conj_apply]

theorem continuous_conjLevi {n a b : ℕ} (h : a + b = n) (w : Pl E) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    Continuous (conjLevi h w X) := by
  have e : (conjLevi h w X : GLw a w × GLw b w → GLw n w) = fun k => (blk h w 1 X)⁻¹ * dgHom h w k * blk h w 1 X := by
    funext k; rw [conjLevi_apply]; rfl
  rw [e]
  exact (continuous_const.mul (continuous_dgHom h w)).mul continuous_const

end GlobalTheory.LeviDesc.ConjStab


open GlobalTheory.LeviDesc.ConjStab in
theorem GlobalTheory.LeviDesc.ConjStab.exists_stab : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)), ∃ U : Subgroup (GLw a w × GLw b w),
    U ≤ (GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b)) ∧ U.relIndex ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))) ≠ 0 ∧
    ∀ k ∈ U, (blk h w 1 X)⁻¹ * blk h w k 0 * blk h w 1 X ∈ GlobalTheory.LFun.KGL w (n := n) := by
  intro E _ _ n a b h w X
  set P : Subgroup (GLw a w × GLw b w) := (GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))
  set C : Subgroup (GLw a w × GLw b w) := (GlobalTheory.LFun.KGL w (n := n)).comap (conjLevi h w X)
  refine ⟨P ⊓ C, inf_le_left, ?_, fun k hk => ?_⟩
  · rw [Subgroup.inf_relIndex_left]
    have hP : IsCompact (P : Set (GLw a w × GLw b w)) := by
      simp only [P, Subgroup.coe_prod]
      exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).2
    have hC : IsOpen (C : Set (GLw a w × GLw b w)) :=
      (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1.preimage (continuous_conjLevi h w X)
    haveI : CompactSpace P := isCompact_iff_compactSpace.mp hP
    haveI : Finite (P ⧸ C.subgroupOf P) :=
      Subgroup.quotient_finite_of_isOpen _ (hC.preimage continuous_subtype_val)
    exact Subgroup.index_ne_zero_of_finite
  · have := (Subgroup.mem_inf.1 hk).2
    rw [Subgroup.mem_comap, conjLevi_apply] at this
    exact this
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteIndexLeviSubgroupUnipotentConjIntegrStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteIndex_levi_subgroup_unipotentConj_integral : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)), ∃ U : Subgroup (GLw a w × GLw b w), U ≤ (GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b)) ∧ U.relIndex ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))) ≠ 0 ∧ ∀ k ∈ U, (blk h w 1 X)⁻¹ * blk h w k 0 * blk h w 1 X ∈ GlobalTheory.LFun.KGL w (n := n) := by
  first | exact @GlobalTheory.LeviDesc.ConjStab.exists_stab | exact GlobalTheory.LeviDesc.ConjStab.exists_stab | (intros; apply GlobalTheory.LeviDesc.ConjStab.exists_stab <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerInfConjIntegralGLProdLeCptPart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerInfConjIntegralGLProdLeCptPart
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CentCpt

theorem twCent_inf_conjKK_le_cptPart (E : Type) [Field E] [NumberField E] (a b : ℕ) (w : Pl E)
    (m q : GLw a w × GLw b w) :
    twCent (MonoidHom.id _) m ⊓ ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))).map (MulAut.conj q).toMonoidHom ≤
      cptPart (twCent (MonoidHom.id _) m) := by
  rintro t ⟨ht, hK⟩
  apply Subgroup.subset_closure
  refine ⟨ht, ?_⟩
  have hc : IsCompact ((((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))).map (MulAut.conj q).toMonoidHom :
      Subgroup (GLw a w × GLw b w)) : Set (GLw a w × GLw b w)) := by
    rw [Subgroup.coe_map, Subgroup.coe_prod]
    refine ((GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).2).image ?_
    show Continuous fun x : GLw a w × GLw b w => q * x * q⁻¹
    fun_prop
  have hz : (Subgroup.zpowers t : Set (GLw a w × GLw b w)) ⊆ _ :=
    (Subgroup.zpowers_le (H := ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))).map (MulAut.conj q).toMonoidHom)).2 hK
  exact hc.of_isClosed_subset isClosed_closure (closure_minimal hz hc.isClosed)

end GlobalTheory.CentCpt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerInfConjIntegralGLProdLeCptPartStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralizer_inf_conj_integralGLProd_le_cptPart : ∀ (E : Type) [Field E] [NumberField E] (a b : ℕ) (w : Pl E) (m q : GLw a w × GLw b w), twCent (MonoidHom.id _) m ⊓ ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))).map (MulAut.conj q).toMonoidHom ≤ cptPart (twCent (MonoidHom.id _) m) := by
  first | exact @GlobalTheory.CentCpt.twCent_inf_conjKK_le_cptPart | exact GlobalTheory.CentCpt.twCent_inf_conjKK_le_cptPart | (intros; apply GlobalTheory.CentCpt.twCent_inf_conjKK_le_cptPart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTwistedCentralizerBlockIff
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfIntertwineOfIsCoprimeCharpoly
namespace GlobalTheory.IntertwinerCoprimeCharpoly

open Polynomial

theorem pow_intertwine {K : Type} [Field K] {a b : ℕ} (A : Matrix (Fin a) (Fin a) K)
    (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K) (h : C * A = B * C) (n : ℕ) :
    C * A ^ n = B ^ n * C := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, h, ← Matrix.mul_assoc]

theorem aeval_intertwine {K : Type} [Field K] {a b : ℕ} (A : Matrix (Fin a) (Fin a) K)
    (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K) (h : C * A = B * C) (p : K[X]) :
    C * aeval A p = aeval B p * C := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), Matrix.mul_add, Matrix.add_mul, hp, hq]
  | monomial n c =>
    simp only [aeval_monomial, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, pow_intertwine A B C h n]

theorem eq_zero_of_intertwine_of_isCoprime_charpoly {K : Type} [Field K] {a b : ℕ}
    (A : Matrix (Fin a) (Fin a) K) (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K)
    (hcop : IsCoprime (Matrix.charpoly A) (Matrix.charpoly B)) (h : C * A = B * C) :
    C = (0 : Matrix (Fin b) (Fin a) K) := by
  obtain ⟨u, v, huv⟩ := hcop
  have h1 : aeval B (u * A.charpoly + v * B.charpoly) = 1 := by rw [huv, map_one]
  rw [map_add (f := _), map_mul, map_mul, Matrix.aeval_self_charpoly, mul_zero, add_zero] at h1
  have h2 : aeval B A.charpoly * C = 0 := by
    rw [← aeval_intertwine A B C h, Matrix.aeval_self_charpoly, Matrix.mul_zero]
  calc C = 1 * C := (Matrix.one_mul C).symm
    _ = (aeval B u * aeval B A.charpoly) * C := by rw [h1]
    _ = aeval B u * (aeval B A.charpoly * C) := Matrix.mul_assoc _ _ _
    _ = 0 := by rw [h2, Matrix.mul_zero]

theorem main : ∀ {K : Type} [inst : Field K] {a b : ℕ} (A : Matrix (Fin a) (Fin a) K)
    (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K),
    IsCoprime (Matrix.charpoly A) (Matrix.charpoly B) → C * A = B * C →
      C = (0 : Matrix (Fin b) (Fin a) K) :=
  fun A B C hcop h => eq_zero_of_intertwine_of_isCoprime_charpoly A B C hcop h

end GlobalTheory.IntertwinerCoprimeCharpoly
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTwistedCentralizerBlockIff
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LeviDesc.CentPar

theorem intertwiner_eq_zero {K : Type} [Field K] {a b : ℕ}
    (A : Matrix (Fin a) (Fin a) K) (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K)
    (hc : IsCoprime A.charpoly B.charpoly) (hC : C * A = B * C) : C = 0 := by
  first
  | exact @_root_.GlobalTheory.IntertwinerCoprimeCharpoly.main
  | exact _root_.GlobalTheory.IntertwinerCoprimeCharpoly.main
  | (apply _root_.GlobalTheory.IntertwinerCoprimeCharpoly.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntertwinerCoprimeCharpoly.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntertwinerCoprimeCharpoly.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntertwinerCoprimeCharpoly.main ..)

variable {E : Type} [Field E] [NumberField E]

theorem blk_zero_val {n a b : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w) :
    ((blk h w m 0 : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (Matrix.fromBlocks m.1.val 0 0 m.2.val) := by
  have hM : IsUnit (Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * (0 : Matrix (Fin a) (Fin b) (w.adicCompletion E))) 0 m.2.val)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_reindex_self, Matrix.mul_zero, Matrix.det_fromBlocks_zero₁₂]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp m.1.isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).mp m.2.isUnit)
  simp only [blk]
  rw [dite_eq_left hM]
  simp

theorem blk_zero_mul {n a b : ℕ} (h : a + b = n) (w : Pl E) (x y : GLw a w × GLw b w) :
    blk h w (x * y) 0 = blk h w x 0 * blk h w y 0 := by
  apply Units.ext
  rw [Units.val_mul, blk_zero_val, blk_zero_val, blk_zero_val]
  simp only [Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp [Prod.fst_mul, Prod.snd_mul]

end GlobalTheory.LeviDesc.CentPar


open GlobalTheory.LeviDesc.CentPar in
theorem GlobalTheory.LeviDesc.mem_twistedCentralizer_parabolic_iff : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E)
    (m : GLw a w × GLw b w), (m.1.val.charpoly * m.2.val.charpoly).Separable →
    ∀ (hγ : blk h w m 0 ∈ GlobalTheory.LeviDesc.parP a n w) (p : GlobalTheory.LeviDesc.parP a n w),
      p ∈ twCent (MonoidHom.id _) (⟨blk h w m 0, hγ⟩ : GlobalTheory.LeviDesc.parP a n w) ↔
        ∃ t ∈ twCent (MonoidHom.id _) m, blk h w t 0 = (p : GLw n w) := by
  intro E _ _ n a b h w m hsep hγ p
  have hcop := hsep.isCoprime
  have hmem : p ∈ twCent (MonoidHom.id _) (⟨blk h w m 0, hγ⟩ : GlobalTheory.LeviDesc.parP a n w) ↔
      (p : GLw n w) * blk h w m 0 = blk h w m 0 * (p : GLw n w) := by
    show p * _ = _ * MonoidHom.id _ p ↔ _
    rw [MonoidHom.id_apply, Subtype.ext_iff]
    rfl
  rw [hmem]
  constructor
  · intro hc
    set e := finSumFinEquiv.trans (finCongr h) with he
    set g' := Matrix.reindex e.symm e.symm ((p : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hg'
    have hgg : ((p : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Matrix.reindex e e g' := by
      simp [hg']
    have hcM := congrArg Units.val hc
    rw [Units.val_mul, Units.val_mul, blk_zero_val, ← he, hgg, ← Matrix.fromBlocks_toBlocks g'] at hcM
    have hc2 := congrArg (Matrix.reindex e.symm e.symm) hcM
    simp only [Matrix.reindex_apply, Equiv.symm_symm, Matrix.submatrix_mul_equiv, Matrix.submatrix_submatrix,
      Equiv.symm_comp_self, Matrix.submatrix_id_id, Matrix.fromBlocks_multiply] at hc2
    rw [Matrix.fromBlocks_inj] at hc2
    obtain ⟨h11, h12, h21, h22⟩ := hc2
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at h11 h12 h21 h22
    have hC0 : g'.toBlocks₂₁ = 0 := intertwiner_eq_zero _ _ _ hcop h21
    have hB0 : g'.toBlocks₁₂ = 0 := intertwiner_eq_zero _ _ _ hcop.symm h12
    have hg'2 : g' = Matrix.fromBlocks g'.toBlocks₁₁ 0 0 g'.toBlocks₂₂ := by
      rw [← hB0, ← hC0, Matrix.fromBlocks_toBlocks]
    have hdet : IsUnit g'.det := by
      rw [hg', Matrix.det_reindex_self]
      exact (Matrix.isUnit_iff_isUnit_det _).mp (p : GLw n w).isUnit
    rw [hg'2, Matrix.det_fromBlocks_zero₂₁] at hdet
    have hA : IsUnit g'.toBlocks₁₁ := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_of_mul_isUnit_left hdet)
    have hD : IsUnit g'.toBlocks₂₂ := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_of_mul_isUnit_right hdet)
    refine ⟨(hA.unit, hD.unit), ?_, ?_⟩
    · show (hA.unit, hD.unit) * m = m * MonoidHom.id _ (hA.unit, hD.unit)
      rw [MonoidHom.id_apply]
      refine Prod.ext (Units.ext ?_) (Units.ext ?_)
      · simpa using h11
      · simpa using h22
    · apply Units.ext
      rw [blk_zero_val, ← he, hgg]
      conv_rhs => rw [hg'2]
      rfl
  · rintro ⟨t, ht, hp⟩
    have ht' : t * m = m * t := ht
    rw [← hp, ← blk_zero_mul, ← blk_zero_mul, ht']
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTwistedCentralizerBlockIffStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_twisted_centralizer_block_iff : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w), (m.1.val.charpoly * m.2.val.charpoly).Separable → ∀ (hγ : blk h w m 0 ∈ GlobalTheory.LeviDesc.parP a n w) (p : GlobalTheory.LeviDesc.parP a n w), p ∈ twCent (MonoidHom.id _) (⟨blk h w m 0, hγ⟩ : GlobalTheory.LeviDesc.parP a n w) ↔ ∃ t ∈ twCent (MonoidHom.id _) m, blk h w t 0 = (p : GLw n w) := by
  first | exact @GlobalTheory.LeviDesc.mem_twistedCentralizer_parabolic_iff | exact GlobalTheory.LeviDesc.mem_twistedCentralizer_parabolic_iff | (intros; apply GlobalTheory.LeviDesc.mem_twistedCentralizer_parabolic_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralParabolicUnfoldLevi
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LeviDesc

theorem cavg_conj_KGL : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (w : Pl E) (f : GLw n w → ℂ), (∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' f) → ∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∀ x, GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) f (k⁻¹ * x * k) = GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) f x := by
  intro E _ _ n w f _ k hk x
  unfold GlobalTheory.LeviDesc.cavg
  rw [← GlobalTheory.TwOrbConj.avg_left (fun k' : GlobalTheory.LFun.KGL w (n := n) => f ((k' : GLw n w)⁻¹ * x * k')) ⟨k, hk⟩]
  congr 1
  funext k'
  congr 1
  simp only [Subgroup.coe_mul, _root_.mul_inv_rev]
  group

theorem twistedOrbitalIntegral_parabolic_unfolding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∀ (n a : ℕ) (ha : a ≤ n) (w : Pl E) (f : GLw n w → ℂ), (∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' f) → ∀ m : GLw a w × GLw (n - a) w, (m.1.val.charpoly * m.2.val.charpoly).Separable → ∀ hγ : blk (Nat.add_sub_cancel' ha) w m 0 ∈ GlobalTheory.LeviDesc.parP a n w, twOrb (MonoidHom.id (GlobalTheory.LeviDesc.parP a n w)) ((GlobalTheory.LFun.KGL w (n := n)).subgroupOf (GlobalTheory.LeviDesc.parP a n w)) ⟨_, hγ⟩ (fun p => GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) f (p : GLw n w)) = twOrb (MonoidHom.id _) ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := (n - a)))) m (GlobalTheory.LeviDesc.orbN (Nat.add_sub_cancel' ha) w f) := by
  intro E _ _ _ n a ha w f hf m hsep hγ
  obtain ⟨s, π, u, hs, hu, hπs, hinj, hker, hKs, hKπ, hKu⟩ := GlobalTheory.T.exists_blockUpperParabolic_levi_projection_unipotent E n a (n - a) (Nat.add_sub_cancel' ha) w
  have hγs : (⟨blk (Nat.add_sub_cancel' ha) w m 0, hγ⟩ : GlobalTheory.LeviDesc.parP a n w) = s m := Subtype.ext (hs m).symm
  have hfin := GlobalTheory.T.finite_parabolicDoubleCosets_orbitalIntegral E n a (n - a) (Nat.add_sub_cancel' ha) w f hf m hsep hγ
  have hcent := GlobalTheory.T.mem_twisted_centralizer_block_iff E n a (n - a) (Nat.add_sub_cancel' ha) w m hsep hγ
  have hcpt := GlobalTheory.T.mem_compactPart_parabolicCentralizer_iff_blockDiagonal E n a (n - a) (Nat.add_sub_cancel' ha) w m hsep hγ
  rw [hγs] at hfin hcent hcpt ⊢
  have hrhs : GlobalTheory.LeviDesc.orbN (Nat.add_sub_cancel' ha) w f = fun m' => hint (intMat a (n - a) w) (fun X =>
      (fun p : GlobalTheory.LeviDesc.parP a n w => GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) f (p : GLw n w)) ((u X)⁻¹ * s m' * u X)) := by
    funext m'
    unfold GlobalTheory.LeviDesc.orbN
    refine congrArg (hint (intMat a (n - a) w)) (funext fun X => ?_)
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, hs, hu]
  rw [hrhs]
  refine GlobalTheory.T.orbitalIntegral_semidirectProduct_unfolding _ _ _ s π u hπs hinj hker _ _ (intMat a (n - a) w) hKs hKπ hKu m ?_ ?_ ?_ ?_ _ ?_ hfin
  · intro p
    rw [hcent]
    simp only [Subtype.ext_iff, hs]
  · intro p
    rw [hcpt]
    simp only [Subtype.ext_iff, hs]
  · intro q
    exact GlobalTheory.T.centralizer_inf_conj_integralGLProd_le_cptPart E a (n - a) w m q
  · intro X
    obtain ⟨U, hU, hUi, hUk⟩ := GlobalTheory.T.exists_finiteIndex_levi_subgroup_unipotentConj_integral E n a (n - a) (Nat.add_sub_cancel' ha) w (Multiplicative.toAdd X)
    refine ⟨U, hU, hUi, fun k hk => ?_⟩
    rw [Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, hs, hu]
    exact hUk k hk
  · intro k hk x
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
    exact cavg_conj_KGL E n w f hf _ (Subgroup.mem_subgroupOf.1 hk) _

end GlobalTheory.LeviDesc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralParabolicUnfoldLeviStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedOrbitalIntegral_parabolic_unfold_levi : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∀ (n a : ℕ) (ha : a ≤ n) (w : Pl E) (f : GLw n w → ℂ), (∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' f) → ∀ m : GLw a w × GLw (n - a) w, (m.1.val.charpoly * m.2.val.charpoly).Separable → ∀ hγ : blk (Nat.add_sub_cancel' ha) w m 0 ∈ GlobalTheory.LeviDesc.parP a n w, twOrb (MonoidHom.id (GlobalTheory.LeviDesc.parP a n w)) ((GlobalTheory.LFun.KGL w (n := n)).subgroupOf (GlobalTheory.LeviDesc.parP a n w)) ⟨_, hγ⟩ (fun p => GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) f (p : GLw n w)) = twOrb (MonoidHom.id _) ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := (n - a)))) m (GlobalTheory.LeviDesc.orbN (Nat.add_sub_cancel' ha) w f) := by
  first | exact @GlobalTheory.LeviDesc.twistedOrbitalIntegral_parabolic_unfolding | exact GlobalTheory.LeviDesc.twistedOrbitalIntegral_parabolic_unfolding | (intros; apply GlobalTheory.LeviDesc.twistedOrbitalIntegral_parabolic_unfolding <;> assumption)
end
