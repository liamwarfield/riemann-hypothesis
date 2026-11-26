module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdicCompletionTraceNormContinuous
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWeilOfFixes

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteImageOfIsOpenStabilizer
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteImageOfIsOpenStabilizer
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem finite_image_of_isOpen_stabilizer (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) (hH : IsOpen {g : G | ρ g v = v})
    (S : Set G) (hS : IsCompact S) : ((fun g => ρ g v) '' S).Finite := by
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover
    (fun s : G => (fun x => s⁻¹ * x) ⁻¹' {g : G | ρ g v = v})
    (fun s => hH.preimage (continuous_const.mul continuous_id))
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simp⟩)
  refine ((t : Set G).toFinite.image (fun g => ρ g v)).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.1 (ht hx)
  refine ⟨s, hs, ?_⟩
  have h1 : ρ (s⁻¹ * x) v = v := hxs
  have hx' : x = s * (s⁻¹ * x) := by group
  show ρ s v = ρ x v
  conv_rhs => rw [hx', map_mul, Module.End.mul_apply, h1]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteImageOfIsOpenStabilizerStatement
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_image_of_isOpen_stabilizer_alt : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (v : V), IsOpen {g : G | ρ g v = v} → ∀ S : Set G, IsCompact S → ((fun g => ρ g v) '' S).Finite := by
  first | exact @GlobalTheory.finite_image_of_isOpen_stabilizer | exact GlobalTheory.finite_image_of_isOpen_stabilizer | (intros; apply GlobalTheory.finite_image_of_isOpen_stabilizer <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LongElementConjInvolutive
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LongElementConjInvolutive
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem longElt_invT_involution : ∀ (R : Type) [CommRing R] (n : ℕ) (g : GL (Fin n) R), longElt n R * GlobalTheory.CuspRep.invT n R (longElt n R * GlobalTheory.CuspRep.invT n R g * longElt n R) * longElt n R = g := by
  intro R _ n g
  have hw : longElt n R * longElt n R = 1 := Units.ext (antidiag_mul_self n R)
  have hii : ∀ h : GL (Fin n) R, GlobalTheory.CuspRep.invT n R (GlobalTheory.CuspRep.invT n R h) = h := fun h => by
    apply Units.ext
    show (h.valᵀ)ᵀ = h.val
    exact Matrix.transpose_transpose _
  have hwT : GlobalTheory.CuspRep.invT n R (longElt n R) = longElt n R := by
    apply Units.ext
    show (Matrix.of fun i j : Fin n => if j = i.rev then (1 : R) else 0)ᵀ = Matrix.of fun i j : Fin n => if j = i.rev then (1 : R) else 0
    ext i j
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    congr 1
    exact propext ⟨fun h => by rw [h, Fin.rev_rev], fun h => by rw [h, Fin.rev_rev]⟩
  rw [map_mul, map_mul, hii, hwT, ← mul_assoc, ← mul_assoc, hw, one_mul, mul_assoc, hw, mul_one]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LongElementConjInvolutiveStatement
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.long_element_conj_involutive : ∀ (R : Type) [CommRing R] (n : ℕ) (g : GL (Fin n) R), longElt n R * GlobalTheory.CuspRep.invT n R (longElt n R * GlobalTheory.CuspRep.invT n R g * longElt n R) * longElt n R = g := by
  first | exact @GlobalTheory.longElt_invT_involution | exact GlobalTheory.longElt_invT_involution | (intros; apply GlobalTheory.longElt_invT_involution <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlCornerEmbeddingUpperUnitriangularSuperDiagonal
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlCornerEmbeddingUpperUnitriangularSuperDiagonal
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CornerUnip

theorem corner_symm_castSucc {m : ℕ} (i : Fin m) :
    (stdSum (rfl : m + 1 = m + 1)).symm (Fin.castSucc i) = Sum.inl i := by
  rw [Equiv.symm_apply_eq]; ext; simp [stdSum_inl]

theorem corner_symm_last (m : ℕ) :
    (stdSum (rfl : m + 1 = m + 1)).symm (Fin.last m) = Sum.inr 0 := by
  rw [Equiv.symm_apply_eq]; ext; simp [stdSum_inr]

variable {R : Type} [CommRing R] {m : ℕ}

theorem corner_cc (u : GL (Fin m) R) (i j : Fin m) :
    (corner u : Matrix (Fin (m+1)) (Fin (m+1)) R) (Fin.castSucc i) (Fin.castSucc j) = (u : Matrix _ _ R) i j := by
  have val_emb₂ (g : GL (Fin m) R × GL (Fin 1) R) :
      (emb₂ R (stdSum (rfl : m + 1 = m + 1)) g : Matrix (Fin (m+1)) (Fin (m+1)) R) =
        Matrix.reindex (stdSum (rfl : m + 1 = m + 1)) (stdSum (rfl : m + 1 = m + 1)) (Matrix.fromBlocks g.1.val 0 0 g.2.val) := by
    ext i j
    simp [emb₂, leviEmb, leviTwo, two, Matrix.reindex_apply, Matrix.blockDiagonal']
    rcases (stdSum (rfl : m + 1 = m + 1)).symm i with a | a <;>
      rcases (stdSum (rfl : m + 1 = m + 1)).symm j with b | b <;> simp
  rw [corner, val_emb₂]
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, corner_symm_castSucc]

theorem corner_cl (u : GL (Fin m) R) (i : Fin m) :
    (corner u : Matrix (Fin (m+1)) (Fin (m+1)) R) (Fin.castSucc i) (Fin.last m) = 0 := by
  have val_emb₂ (g : GL (Fin m) R × GL (Fin 1) R) :
      (emb₂ R (stdSum (rfl : m + 1 = m + 1)) g : Matrix (Fin (m+1)) (Fin (m+1)) R) =
        Matrix.reindex (stdSum (rfl : m + 1 = m + 1)) (stdSum (rfl : m + 1 = m + 1)) (Matrix.fromBlocks g.1.val 0 0 g.2.val) := by
    ext i j
    simp [emb₂, leviEmb, leviTwo, two, Matrix.reindex_apply, Matrix.blockDiagonal']
    rcases (stdSum (rfl : m + 1 = m + 1)).symm i with a | a <;>
      rcases (stdSum (rfl : m + 1 = m + 1)).symm j with b | b <;> simp
  rw [corner, val_emb₂]
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, corner_symm_castSucc, corner_symm_last]

theorem corner_lc (u : GL (Fin m) R) (j : Fin m) :
    (corner u : Matrix (Fin (m+1)) (Fin (m+1)) R) (Fin.last m) (Fin.castSucc j) = 0 := by
  have val_emb₂ (g : GL (Fin m) R × GL (Fin 1) R) :
      (emb₂ R (stdSum (rfl : m + 1 = m + 1)) g : Matrix (Fin (m+1)) (Fin (m+1)) R) =
        Matrix.reindex (stdSum (rfl : m + 1 = m + 1)) (stdSum (rfl : m + 1 = m + 1)) (Matrix.fromBlocks g.1.val 0 0 g.2.val) := by
    ext i j
    simp [emb₂, leviEmb, leviTwo, two, Matrix.reindex_apply, Matrix.blockDiagonal']
    rcases (stdSum (rfl : m + 1 = m + 1)).symm i with a | a <;>
      rcases (stdSum (rfl : m + 1 = m + 1)).symm j with b | b <;> simp
  rw [corner, val_emb₂]
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, corner_symm_castSucc, corner_symm_last]

theorem corner_ll (u : GL (Fin m) R) :
    (corner u : Matrix (Fin (m+1)) (Fin (m+1)) R) (Fin.last m) (Fin.last m) = 1 := by
  have val_emb₂ (g : GL (Fin m) R × GL (Fin 1) R) :
      (emb₂ R (stdSum (rfl : m + 1 = m + 1)) g : Matrix (Fin (m+1)) (Fin (m+1)) R) =
        Matrix.reindex (stdSum (rfl : m + 1 = m + 1)) (stdSum (rfl : m + 1 = m + 1)) (Matrix.fromBlocks g.1.val 0 0 g.2.val) := by
    ext i j
    simp [emb₂, leviEmb, leviTwo, two, Matrix.reindex_apply, Matrix.blockDiagonal']
    rcases (stdSum (rfl : m + 1 = m + 1)).symm i with a | a <;>
      rcases (stdSum (rfl : m + 1 = m + 1)).symm j with b | b <;> simp
  rw [corner, val_emb₂]
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, corner_symm_last]

end GlobalTheory.CornerUnip

open GlobalTheory.CornerUnip in
theorem GlobalTheory.CornerUnip.corner_unipB_superDiag : ∀ (R : Type) [CommRing R] (m : ℕ) (u : GL (Fin m) R), u ∈ unipB R (Fin m) → corner u ∈ unipB R (Fin (m + 1)) ∧ superDiag (corner u) = superDiag u := by
  intro R _ m u hu
  rw [mem_unipB] at hu
  obtain ⟨hl, hd⟩ := hu
  refine ⟨?_, ?_⟩
  · rw [mem_unipB]
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd hij (lt_irrefl _)
        | cast j => exact corner_lc u j
      | cast i =>
        induction j using Fin.lastCases with
        | last => exact absurd hij (not_lt.2 (Fin.le_last _))
        | cast j =>
          rw [corner_cc]
          exact hl i j (Fin.castSucc_lt_castSucc_iff.1 hij)
    · induction i using Fin.lastCases with
      | last => exact corner_ll u
      | cast i => rw [corner_cc]; exact hd i
  · unfold superDiag
    simp only [Finset.sum_filter]
    simp [Fin.sum_univ_castSucc, corner_cc, corner_cl, corner_lc, corner_ll]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlCornerEmbeddingUpperUnitriangularSuperDiagonalStatement
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glCornerEmbedding_upperUnitriangular_superDiagonalSum : ∀ (R : Type) [CommRing R] (m : ℕ) (u : GL (Fin m) R), u ∈ unipB R (Fin m) → corner u ∈ unipB R (Fin (m + 1)) ∧ superDiag (corner u) = superDiag u := by
  first | exact @GlobalTheory.CornerUnip.corner_unipB_superDiag | exact GlobalTheory.CornerUnip.corner_unipB_superDiag | (intros; apply GlobalTheory.CornerUnip.corner_unipB_superDiag <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTorusBoundsOfConsecutiveRatioBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTorusBoundsOfConsecutiveRatioBounds
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory

theorem valuation_chain_ratio_bounds (k : Type) [Field k] [ValuativeRel k] (m : ℕ) (r1 r2 : Fin m → kˣ) :
    ∃ R1 R2 : kˣ, 1 ≤ valuation k (R1 : k) ∧ valuation k (R2 : k) ≤ 1 ∧
      ∀ t : Fin (m + 1) → kˣ, t (Fin.last m) = 1 →
        (∀ i : Fin m, valuation k (r2 i : k) ≤ valuation k ((t i.castSucc : k) / t i.succ) ∧
          valuation k ((t i.castSucc : k) / t i.succ) ≤ valuation k (r1 i : k)) →
        ∀ i, valuation k (R2 : k) ≤ valuation k (t i : k) ∧ valuation k (t i : k) ≤ valuation k (R1 : k) := by
  induction m with
  | zero =>
    refine ⟨1, 1, by simp, by simp, ?_⟩
    intro t ht _ i
    have hi : i = Fin.last 0 := Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
    subst hi
    rw [ht]; simp
  | succ m ih =>
    obtain ⟨R1', R2', h1', h2', hR⟩ := ih (fun j => r1 j.succ) (fun j => r2 j.succ)
    set a : kˣ := if valuation k (r1 0 : k) ≤ 1 then 1 else r1 0 with ha_def
    set b : kˣ := if 1 ≤ valuation k (r2 0 : k) then 1 else r2 0 with hb_def
    have ha1 : 1 ≤ valuation k (a : k) := by
      rw [ha_def]; split_ifs with h
      · simp
      · exact le_of_lt (not_le.mp h)
    have har : valuation k (r1 0 : k) ≤ valuation k (a : k) := by
      rw [ha_def]; split_ifs with h
      · simpa using h
      · exact le_rfl
    have hb1 : valuation k (b : k) ≤ 1 := by
      rw [hb_def]; split_ifs with h
      · simp
      · exact le_of_lt (not_le.mp h)
    have hbr : valuation k (b : k) ≤ valuation k (r2 0 : k) := by
      rw [hb_def]; split_ifs with h
      · simpa using h
      · exact le_rfl
    refine ⟨R1' * a, R2' * b, ?_, ?_, ?_⟩
    · simp only [Units.val_mul, map_mul]
      exact one_le_mul h1' ha1
    · simp only [Units.val_mul, map_mul]
      exact mul_le_one' h2' hb1
    intro t ht hrat
    have hT := hR (fun j => t j.succ) (by simp only [Fin.succ_last]; exact ht) (fun i => by
      have := hrat i.succ
      rw [← Fin.succ_castSucc] at this; exact this)
    have hR1le : valuation k (R1' : k) ≤ valuation k ((R1' * a : kˣ) : k) := by
      simp only [Units.val_mul, map_mul]; exact le_mul_of_one_le_right' ha1
    have hR2le : valuation k ((R2' * b : kˣ) : k) ≤ valuation k (R2' : k) := by
      simp only [Units.val_mul, map_mul]; exact mul_le_of_le_one_right' hb1
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · have h0 := hrat 0
      have ht1 := hT 0
      simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one] at h0 ht1
      have hne : ((t 1 : kˣ) : k) ≠ 0 := (t 1).ne_zero
      have hsplit : ((t 0 : kˣ) : k) = ((t 0 : k) / t 1) * t 1 := by field_simp
      rw [hsplit, map_mul]
      constructor
      · simp only [Units.val_mul, map_mul]
        calc valuation k (R2' : k) * valuation k (b : k)
            = valuation k (b : k) * valuation k (R2' : k) := mul_comm _ _
          _ ≤ valuation k (r2 0 : k) * valuation k (t 1 : k) := mul_le_mul' hbr ht1.1
          _ ≤ _ := mul_le_mul' h0.1 le_rfl
      · simp only [Units.val_mul, map_mul]
        calc valuation k ((t 0 : k) / t 1) * valuation k (t 1 : k)
            ≤ valuation k (r1 0 : k) * valuation k (R1' : k) := mul_le_mul' h0.2 ht1.2
          _ ≤ valuation k (a : k) * valuation k (R1' : k) := mul_le_mul' har le_rfl
          _ = _ := mul_comm _ _
    · have := hT j
      exact ⟨hR2le.trans this.1, this.2.trans hR1le⟩

theorem chain_bound : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ) (r1 r2 : Fin m → kˣ), ∃ R1 R2 : kˣ, ∀ t : Fin (m + 1) → kˣ, t (Fin.last m) = 1 → (∀ i : Fin m, valuation k (r2 i : k) ≤ valuation k ((t i.castSucc : k) / t i.succ) ∧ valuation k ((t i.castSucc : k) / t i.succ) ≤ valuation k (r1 i : k)) → ∀ i, valuation k (R2 : k) ≤ valuation k (t i : k) ∧ valuation k (t i : k) ≤ valuation k (R1 : k) := by
  intro k _ _ _ _ m r1 r2
  obtain ⟨R1, R2, -, -, h⟩ := valuation_chain_ratio_bounds k m r1 r2
  exact ⟨R1, R2, h⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTorusBoundsOfConsecutiveRatioBoundsStatement
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torus_bounds_of_consecutive_ratio_bounds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ) (r1 r2 : Fin m → kˣ), ∃ R1 R2 : kˣ, ∀ t : Fin (m + 1) → kˣ, t (Fin.last m) = 1 → (∀ i : Fin m, valuation k (r2 i : k) ≤ valuation k ((t i.castSucc : k) / t i.succ) ∧ valuation k ((t i.castSucc : k) / t i.succ) ≤ valuation k (r1 i : k)) → ∀ i, valuation k (R2 : k) ≤ valuation k (t i : k) ∧ valuation k (t i : k) ≤ valuation k (R1 : k) := by
  first | exact @GlobalTheory.chain_bound | exact GlobalTheory.chain_bound | (intros; apply GlobalTheory.chain_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LongElementConjUnipotentBorel
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LongElementConjUnipotentBorel
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.UnipFlip

theorem longElt_conj_apply {R : Type} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    ((longElt n R : Matrix (Fin n) (Fin n) R) * A * (longElt n R : Matrix (Fin n) (Fin n) R)) i j
      = A i.rev j.rev := by
  simp only [Matrix.mul_apply, longElt, Matrix.of_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_eq_single j.rev]
  · simp
  · intro b _ hb; rw [if_neg]; intro e; exact hb (by rw [e, Fin.rev_rev])
  · simp

theorem inv_apply_succ {R : Type} [CommRing R] {n : ℕ} {u : GL (Fin n) R} (hu : u ∈ unipB R (Fin n))
    (p q : Fin n) (h : (q : ℕ) = p + 1) :
    ((u⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) p q = - (u : Matrix (Fin n) (Fin n) R) p q := by
  have hv : u⁻¹ ∈ unipB R (Fin n) := inv_mem hu
  rw [mem_unipB] at hu hv
  have hpq : p ≠ q := by intro e; subst e; omega
  have key := congrFun (congrFun (congrArg (fun g : GL (Fin n) R => (g : Matrix (Fin n) (Fin n) R)) (mul_inv_cancel u)) p) q
  simp only [Units.val_mul, Units.val_one, Matrix.mul_apply, Matrix.one_apply_ne hpq] at key
  rw [Fintype.sum_eq_add p q hpq] at key
  · rw [hu.2 p, hv.2 q, one_mul, mul_one] at key
    linear_combination key
  · intro c ⟨hcp, hcq⟩
    rcases lt_or_gt_of_ne hcp with hlt | hgt
    · rw [hu.1 p c hlt, zero_mul]
    · have : q < c := by
        have h1 : (p : ℕ) < c := hgt
        have h2 : (c : ℕ) ≠ q := fun e => hcq (Fin.ext e)
        show (q : ℕ) < c
        omega
      rw [hv.1 c q this, mul_zero]

theorem longElt_invT_conj_unipB : ∀ (R : Type) [CommRing R] (n : ℕ) (u : GL (Fin n) R), u ∈ unipB R (Fin n) →
    longElt n R * GlobalTheory.CuspRep.invT n R u * longElt n R ∈ unipB R (Fin n) ∧
      superDiag (longElt n R * GlobalTheory.CuspRep.invT n R u * longElt n R) = -superDiag u := by
  intro R _ n u hu
  have hv : u⁻¹ ∈ unipB R (Fin n) := inv_mem hu
  have hval : ∀ i j : Fin n,
      ((longElt n R * GlobalTheory.CuspRep.invT n R u * longElt n R : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j
        = ((u⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) j.rev i.rev := by
    intro i j
    rw [Units.val_mul, Units.val_mul]
    rw [longElt_conj_apply]
    rfl
  rw [mem_unipB] at hv
  refine ⟨?_, ?_⟩
  · rw [mem_unipB]
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [hval]; exact hv.1 _ _ (Fin.rev_lt_rev.2 hij)
    · rw [hval]; exact hv.2 _
  · simp only [superDiag, Finset.sum_filter]
    simp_rw [hval]
    rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Fintype.sum_equiv Fin.revPerm _ _ fun p => ?_
    rw [← Finset.sum_neg_distrib]
    refine Fintype.sum_equiv Fin.revPerm _ _ fun q => ?_
    simp only [Fin.revPerm_apply, Fin.rev_rev]

    have hiff : ((q.rev : Fin n) : ℕ) = (p.rev : ℕ) + 1 ↔ (p : ℕ) = q + 1 := by
      simp only [Fin.val_rev]; have := p.isLt; have := q.isLt; omega
    by_cases h : (p : ℕ) = q + 1
    · rw [if_pos h, if_pos (hiff.2 h), inv_apply_succ hu p.rev q.rev (hiff.2 h)]
    · rw [if_neg h, if_neg (mt hiff.1 h), neg_zero]

end GlobalTheory.UnipFlip
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LongElementConjUnipotentBorelStatement
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.long_element_conj_unipotent_borel : ∀ (R : Type) [CommRing R] (n : ℕ) (u : GL (Fin n) R), u ∈ unipB R (Fin n) → longElt n R * GlobalTheory.CuspRep.invT n R u * longElt n R ∈ unipB R (Fin n) ∧ superDiag (longElt n R * GlobalTheory.CuspRep.invT n R u * longElt n R) = -superDiag u := by
  first | exact @GlobalTheory.UnipFlip.longElt_invT_conj_unipB | exact GlobalTheory.UnipFlip.longElt_invT_conj_unipB | (intros; apply GlobalTheory.UnipFlip.longElt_invT_conj_unipB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCompactBoundedTorus
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCompactBoundedTorus
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem isOpen_setOf_valuation_lt_of_ne_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (γ : ValueGroupWithZero k) (hγ : γ ≠ 0) :
    IsOpen {x : k | valuation k x < γ} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 γ hγ, fun y hy => ?_⟩
  simp only [Set.mem_setOf_eq, Units.val_mk0] at hx hy ⊢
  have h := (valuation k).map_add (y - x) x
  rw [sub_add_cancel] at h
  exact h.trans_lt (max_lt hy hx)

theorem isCompact_boundedTorus : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ) (R1 R2 : kˣ), IsCompact {t : Fin m → kˣ | ∀ i, valuation k (R2 : k) ≤ valuation k (t i : k) ∧ valuation k (t i : k) ≤ valuation k (R1 : k)} := by
  intro k _ _ _ _ m R1 R2
  have hS : IsCompact {x : kˣ | valuation k (R2 : k) ≤ valuation k (x : k) ∧ valuation k (x : k) ≤ valuation k (R1 : k)} := by
    rw [Units.isEmbedding_val₀.isCompact_iff]
    have himg : (Units.val '' {x : kˣ | valuation k (R2 : k) ≤ valuation k (x : k) ∧ valuation k (x : k) ≤ valuation k (R1 : k)})
        = {y : k | valuation k y ≤ valuation k (R1 : k)} ∩ {y : k | valuation k (R2 : k) ≤ valuation k y} := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨hx.2, hx.1⟩
      · rintro ⟨h1, h2⟩
        have hy : y ≠ 0 := by
          rintro rfl
          simp at h2
        exact ⟨Units.mk0 y hy, ⟨h2, h1⟩, rfl⟩
    rw [himg]
    refine (IsNonarchimedeanLocalField.isCompact_closedBall k _).inter_right ?_
    have hne : valuation k (R2 : k) ≠ 0 := by simp
    have ho := isOpen_setOf_valuation_lt_of_ne_zero (valuation k (R2 : k)) hne
    have hc : {y : k | valuation k (R2 : k) ≤ valuation k y} = {y : k | valuation k y < valuation k (R2 : k)}ᶜ := by
      ext y; simp
    rw [hc]
    exact ho.isClosed_compl
  have : {t : Fin m → kˣ | ∀ i, valuation k (R2 : k) ≤ valuation k (t i : k) ∧ valuation k (t i : k) ≤ valuation k (R1 : k)}
      = Set.pi Set.univ (fun _ => {x : kˣ | valuation k (R2 : k) ≤ valuation k (x : k) ∧ valuation k (x : k) ≤ valuation k (R1 : k)}) := by
    ext t; simp
  rw [this]
  exact isCompact_univ_pi fun _ => hS

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCompactBoundedTorusStatement
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_boundedTorus' : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ) (R1 R2 : kˣ), IsCompact {t : Fin m → kˣ | ∀ i, valuation k (R2 : k) ≤ valuation k (t i : k) ∧ valuation k (t i : k) ≤ valuation k (R1 : k)} := by
  first | exact @GlobalTheory.isCompact_boundedTorus | exact GlobalTheory.isCompact_boundedTorus | (intros; apply GlobalTheory.isCompact_boundedTorus <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlCornerEmbeddingDiagonalTorusEqSnocOne
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlCornerEmbeddingDiagonalTorusEqSnocOne
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

theorem corner_diagT (R : Type) [CommRing R] (m : ℕ) (t : Fin m → Rˣ) :
    corner (diagT R (Fin m) t) = diagT R (Fin (m + 1)) (Fin.snoc t 1) := by
  apply Units.ext
  change (emb₂ R (stdSum (rfl : m + 1 = m + 1)) (diagT R (Fin m) t, 1) : Matrix (Fin (m + 1)) (Fin (m + 1)) R) = (diagT R (Fin (m + 1)) (Fin.snoc t 1) : Matrix (Fin (m + 1)) (Fin (m + 1)) R)
  rw [val_emb₂, val_diagT, val_diagT]
  ext i j
  obtain ⟨i, rfl⟩ := (stdSum (rfl : m + 1 = m + 1)).surjective i
  obtain ⟨j, rfl⟩ := (stdSum (rfl : m + 1 = m + 1)).surjective j
  have hl : ∀ a : Fin m, stdSum (rfl : m + 1 = m + 1) (Sum.inl a) = Fin.castSucc a := fun a => Fin.ext rfl
  have hr : ∀ a : Fin 1, stdSum (rfl : m + 1 = m + 1) (Sum.inr a) = Fin.last m := fun a => by
    apply Fin.ext; simp [stdSum, Subsingleton.elim a 0]
  simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j
  · rw [hl, hl, fromBlocks_apply₁₁]
    simp only [diagonal_apply, Fin.snoc_castSucc, Fin.castSucc_inj]
  · rw [hl, hr, fromBlocks_apply₁₂, diagonal_apply_ne _ (Fin.castSucc_lt_last i).ne, Matrix.zero_apply]
  · rw [hl, hr, fromBlocks_apply₂₁, diagonal_apply_ne _ (Fin.castSucc_lt_last j).ne', Matrix.zero_apply]
  · rw [hr, hr, fromBlocks_apply₂₂, diagonal_apply_eq, Fin.snoc_last, Subsingleton.elim i j]
    simp

end GlobalTheory.LocLanglands
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlCornerEmbeddingDiagonalTorusEqSnocOneStatement
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glCornerEmbedding_diagonalTorus_eq_snoc_one : ∀ (R : Type) [CommRing R] (m : ℕ) (t : Fin m → Rˣ), corner (diagT R (Fin m) t) = diagT R (Fin (m + 1)) (Fin.snoc t 1) := by
  first | exact @GlobalTheory.LocLanglands.corner_diagT | exact GlobalTheory.LocLanglands.corner_diagT | (intros; apply GlobalTheory.LocLanglands.corner_diagT <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WhittakerTorusTwKerRootBound
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WhittakerTorusTwKerRootBound
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RootDown

variable {k : Type} [Field k]

theorem blk_stdBlocks_eq_zero {n a b : ℕ} (h : ∑ i, ![a, b] i = n) (p : Fin n) :
    GlobalTheory.SmGL.blk (stdBlocks ![a, b] h) p = 0 ↔ p.val < a := by
  obtain ⟨⟨c, r⟩, rfl⟩ := (stdBlocks ![a, b] h).surjective p
  rw [GlobalTheory.SmGL.blk_apply, stdBlocks_val]
  rcases c with ⟨_ | _ | c, hc⟩
  · have := r.isLt
    simp at this ⊢
    omega
  · have := r.isLt
    simp
  · omega

theorem unip_entry {n a b : ℕ} (h : ∑ i, ![a, b] i = n) {u : GL (Fin n) k}
    (hu : u ∈ unipRad k (stdBlocks ![a, b] h)) (p q : Fin n) (hpq : ¬ (p.val < a ∧ a ≤ q.val)) :
    (u : Matrix (Fin n) (Fin n) k) p q = (1 : Matrix (Fin n) (Fin n) k) p q := by
  obtain ⟨hP, hD⟩ := mem_unipRad.1 hu
  rcases lt_trichotomy (GlobalTheory.SmGL.blk (stdBlocks ![a, b] h) q) (GlobalTheory.SmGL.blk (stdBlocks ![a, b] h) p)
    with hlt | heq | hgt
  · rw [mem_parab.1 hP p q hlt]
    have : p ≠ q := by rintro rfl; exact lt_irrefl _ hlt
    simp [Matrix.one_apply_ne this]
  · obtain ⟨⟨c, r⟩, rfl⟩ := (stdBlocks ![a, b] h).surjective p
    obtain ⟨⟨c', s⟩, rfl⟩ := (stdBlocks ![a, b] h).surjective q
    simp only [GlobalTheory.SmGL.blk_apply] at heq
    subst heq
    rw [hD c' r s]
    simp [Matrix.one_apply]
  · exfalso
    apply hpq
    have h1 := Fin.lt_def.1 hgt
    have h2 := (GlobalTheory.SmGL.blk (stdBlocks ![a, b] h) q).isLt
    have hp0 : GlobalTheory.SmGL.blk (stdBlocks ![a, b] h) p = 0 := Fin.ext (by simp; omega)
    have hq0 : GlobalTheory.SmGL.blk (stdBlocks ![a, b] h) q ≠ 0 := fun h0 => by
      rw [h0] at h1; simp at h1
    exact ⟨(blk_stdBlocks_eq_zero h p).1 hp0,
      not_lt.1 fun hq => hq0 ((blk_stdBlocks_eq_zero h q).2 hq)⟩

theorem conj_entry {n : ℕ} (t : Fin n → kˣ) (u : GL (Fin n) k) (p q : Fin n) :
    ((diagT k (Fin n) t * u * (diagT k (Fin n) t)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p q =
      (t p : k) * (u : Matrix (Fin n) (Fin n) k) p q * (((t q)⁻¹ : kˣ) : k) := by
  rw [← map_inv, Units.val_mul, Units.val_mul, val_diagT, val_diagT, Matrix.mul_diagonal,
    Matrix.diagonal_mul]
  simp

end GlobalTheory.RootDown

open GlobalTheory.RootDown in
theorem GlobalTheory.whittaker_torus_twKer_rootBound : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V) (l : Module.Dual ℂ V), IsFunctional ψ ρ l → ∀ (a b : ℕ) (h : ∑ i, ![a, b] i = n) (i j : Fin n), i.val + 1 = a → j.val = a → ∀ x ∈ twKer ρ (unipRad k (stdBlocks ![a, b] h)) 1, ∃ r : kˣ, ∀ t : Fin n → kˣ, l (ρ (diagT k (Fin n) t) x) ≠ 0 → valuation k (r : k) ≤ valuation k ((t i : k) / t j) := by
  intro k _ _ _ _ ψ hψ n V _ _ ρ l hl a b h i j hi hj x hx
  obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_addChar_eq_one ψ hψ
  unfold twKer at hx
  induction hx using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨⟨u, hu⟩, y, rfl⟩ := hw
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    have key : ∀ t : Fin n → kˣ, l (ρ (diagT k (Fin n) t) (ρ u y - y)) =
        ((ψ ((t i : k) / t j * (u : Matrix (Fin n) (Fin n) k) i j) : ℂ) - 1) *
          l (ρ (diagT k (Fin n) t) y) := by
      intro t
      have hmem : diagT k (Fin n) t * u * (diagT k (Fin n) t)⁻¹ ∈ unipB k (Fin n) := by
        refine (mem_unipB k).2 ⟨fun p q hqp => ?_, fun p => ?_⟩
        · have hqp' := Fin.lt_def.1 hqp
          rw [conj_entry, unip_entry h hu p q (by omega), Matrix.one_apply_ne hqp.ne']
          simp
        · rw [conj_entry, unip_entry h hu p p (by omega), Matrix.one_apply_eq]
          simp
      have hsd : GlobalTheory.Whittaker.superDiag (diagT k (Fin n) t * u * (diagT k (Fin n) t)⁻¹) =
          (t i : k) / t j * (u : Matrix (Fin n) (Fin n) k) i j := by
        unfold GlobalTheory.Whittaker.superDiag
        rw [Finset.sum_eq_single i]
        · rw [Finset.sum_eq_single_of_mem j (by simp; omega)]
          · rw [conj_entry, Units.val_inv_eq_inv_val, div_eq_mul_inv]
            ring
          · intro q hq hqj
            simp at hq
            exact absurd (Fin.ext (by omega)) hqj
        · intro p _ hpi
          refine Finset.sum_eq_zero fun q hq => ?_
          simp at hq
          have hpq : p ≠ q := fun e => by rw [e] at hq; omega
          rw [conj_entry, unip_entry h hu p q ?_, Matrix.one_apply_ne hpq]
          · simp
          · rintro ⟨h1, h2⟩
            exact hpi (Fin.ext (by omega))
        · intro hi'
          simp at hi'
      have hρ : ρ (diagT k (Fin n) t) (ρ u y) =
          ρ (diagT k (Fin n) t * u * (diagT k (Fin n) t)⁻¹) (ρ (diagT k (Fin n) t) y) := by
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        congr 2
        group
      simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub, hρ, hl _ hmem, hsd]
      ring
    by_cases hu0 : (u : Matrix (Fin n) (Fin n) k) i j = 0
    · refine ⟨1, fun t ht => absurd ?_ ht⟩
      rw [key, hu0, mul_zero, AddChar.map_zero_eq_one]
      simp
    · refine ⟨s * (Units.mk0 _ hu0)⁻¹, fun t ht => ?_⟩
      rw [key] at ht
      have hψ1 : ψ ((t i : k) / t j * (u : Matrix (Fin n) (Fin n) k) i j) ≠ 1 := fun h1 =>
        ht (by rw [h1]; simp)
      have hlt : valuation k (s : k) <
          valuation k ((t i : k) / t j * (u : Matrix (Fin n) (Fin n) k) i j) :=
        lt_of_not_ge fun hle => hψ1 (hs _ hle)
      rw [map_mul] at hlt
      have hpos : 0 < valuation k ((u : Matrix (Fin n) (Fin n) k) i j) := by
        simp [zero_lt_iff, hu0]
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, map_mul, map_inv₀]
      exact ((mul_inv_lt_iff₀ hpos).2 hlt).le
  | zero => exact ⟨1, fun t ht => absurd (by simp) ht⟩
  | add x y _ _ hx hy =>
    obtain ⟨r₁, h₁⟩ := hx
    obtain ⟨r₂, h₂⟩ := hy
    rcases le_total (valuation k (r₁ : k)) (valuation k (r₂ : k)) with h12 | h21
    · refine ⟨r₁, fun t ht => ?_⟩
      rw [map_add (f := _), map_add (f := _)] at ht
      by_cases h0 : l (ρ (diagT k (Fin n) t) x) = 0
      · rw [h0, zero_add] at ht
        exact h12.trans (h₂ t ht)
      · exact h₁ t h0
    · refine ⟨r₂, fun t ht => ?_⟩
      rw [map_add (f := _), map_add (f := _)] at ht
      by_cases h0 : l (ρ (diagT k (Fin n) t) y) = 0
      · rw [h0, add_zero] at ht
        exact h21.trans (h₁ t ht)
      · exact h₂ t h0
  | smul c x _ hx =>
    obtain ⟨r, hr⟩ := hx
    exact ⟨r, fun t ht => hr t fun h0 => ht (by rw [map_smul, map_smul, h0, smul_zero])⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WhittakerTorusTwKerRootBoundStatement
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_torus_twKer_rootBound' : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V) (l : Module.Dual ℂ V), IsFunctional ψ ρ l → ∀ (a b : ℕ) (h : ∑ i, ![a, b] i = n) (i j : Fin n), i.val + 1 = a → j.val = a → ∀ x ∈ twKer ρ (unipRad k (stdBlocks ![a, b] h)) 1, ∃ r : kˣ, ∀ t : Fin n → kˣ, l (ρ (diagT k (Fin n) t) x) ≠ 0 → valuation k (r : k) ≤ valuation k ((t i : k) / t j) := by
  first | exact @GlobalTheory.whittaker_torus_twKer_rootBound | exact GlobalTheory.whittaker_torus_twKer_rootBound | (intros; apply GlobalTheory.whittaker_torus_twKer_rootBound <;> assumption)
end
end

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocLanglands


open scoped Pointwise in
theorem exists_compact_mod_unipB_whittaker : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin (m + 1)) k) V), IsSmooth ρ → (∀ (a b : ℕ) (h : ∑ i, ![a, b] i = m + 1), 0 < a → 0 < b → ∀ x : V, x ∈ twKer ρ (unipRad k (stdBlocks ![a, b] h)) 1) → ∀ l : Module.Dual ℂ V, IsFunctional ψ ρ l → ∀ v : V, ∃ C : Set (GL (Fin m) k), IsCompact C ∧ ∀ g : GL (Fin m) k, l (ρ (corner g) v) ≠ 0 → ∃ u ∈ unipB k (Fin m), ∃ c ∈ C, g = u * c := by
  intro k _ _ _ _ ψ hψc hψ1 m V _ _ ρ hs hJ l hl v
  have hcm : ∀ g h : GL (Fin m) k, corner (g * h) = corner g * corner h := fun g h => by
    simp only [corner]
    rw [← map_mul, Prod.mk_mul_mk, mul_one]
  have hcc : Continuous (corner : GL (Fin m) k → GL (Fin (m + 1)) k) :=
    (continuous_leviEmb k _).comp ((continuous_leviTwo k).comp (continuous_id.prodMk continuous_const))
  have hdc : Continuous (diagT k (Fin m)) :=
    (continuous_leviEmb k _).comp (continuous_leviTorus k (Fin m))
  set X : Set V := (fun g => ρ g v) '' (corner '' (KO k (Fin m) : Set (GL (Fin m) k))) with hX
  have hXf : X.Finite := GlobalTheory.T.finite_image_of_isOpen_stabilizer_alt _ V ρ v (hs v) _ (GlobalTheory.SplitFlip.isCompact_KO.image hcc)
  choose r1 hr1 using GlobalTheory.T.whittaker_functional_torus_valuation_bound k ψ hψc hψ1 (m + 1) V ρ hs l hl
  have hlow : ∀ (x : V) (i : Fin m), ∃ r : kˣ, ∀ t : Fin (m + 1) → kˣ,
      l (ρ (diagT k (Fin (m + 1)) t) x) ≠ 0 → valuation k (r : k) ≤ valuation k ((t i.castSucc : k) / t i.succ) := by
    intro x i
    have hi := i.2
    have h : ∑ j, ![(i : ℕ) + 1, m - i] j = m + 1 := by
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    exact GlobalTheory.T.whittaker_torus_twKer_rootBound' k ψ hψc (m + 1) V ρ l hl _ _ h i.castSucc i.succ (by simp) (by simp) x
      (hJ _ _ h (Nat.succ_pos _) (by omega) x)
  choose r2 hr2 using hlow
  choose R1 R2 hR using fun x => GlobalTheory.T.exists_torus_bounds_of_consecutive_ratio_bounds k m (fun _ => r1 x) (r2 x)
  refine ⟨⋃ x ∈ X, diagT k (Fin m) '' {t : Fin m → kˣ | ∀ i, valuation k (R2 x : k) ≤ valuation k (t i : k) ∧
      valuation k (t i : k) ≤ valuation k (R1 x : k)} * (KO k (Fin m) : Set (GL (Fin m) k)),
    hXf.isCompact_biUnion fun x _ => ((GlobalTheory.T.isCompact_boundedTorus' k m (R1 x) (R2 x)).image hdc).mul GlobalTheory.SplitFlip.isCompact_KO,
    fun g hg => ?_⟩
  obtain ⟨u, hu, t, κ, hκ, rfl⟩ := GlobalTheory.T.exists_iwasawa_decomposition_upperUnitriangular_integral k m g
  have hcu := GlobalTheory.T.glCornerEmbedding_upperUnitriangular_superDiagonalSum k m u hu
  rw [hcm, hcm, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hl _ hcu.1, GlobalTheory.T.glCornerEmbedding_diagonalTorus_eq_snoc_one] at hg
  have hg' := right_ne_zero_of_mul hg
  have hxX : ρ (corner κ) v ∈ X := ⟨corner κ, ⟨κ, hκ, rfl⟩, rfl⟩
  have hlast : (Fin.snoc t 1 : Fin (m + 1) → kˣ) (Fin.last m) = 1 := Fin.snoc_last _ _
  have hb := hR _ _ hlast (fun i => ⟨hr2 _ i _ hg', hr1 _ _ i.castSucc i.succ (by simp) hg'⟩)
  refine ⟨u, hu, diagT k (Fin m) t * κ, Set.mem_biUnion hxX ⟨_, ⟨t, fun i => ?_, rfl⟩, κ, hκ, rfl⟩,
    mul_assoc _ _ _⟩
  have := hb i.castSucc
  simpa [Fin.snoc_castSucc] using this

end GlobalTheory.LocLanglands
