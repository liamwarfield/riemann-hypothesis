module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceConjStabilizesFramedLatticeIff
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeResiduePairEqScalarOfSameStabilizer

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthogonalEmbeddingKeepsGluedCoreIffFixesPair
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthogonalEmbeddingKeepsGluedCoreIffFixesPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch.StabPair

open GlobalTheory.FinPl.FrameLat

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mt_sec_any (p : SplitPt D k) {S : HSp D} (h : GA D S) (y : Fin S.rank → k) :
    Formalism.L2.Theta.mt S h *ᵥ (fun i => p.sec (y i)) = fun i => p.sec ((((Formalism.L2.Theta.mt S h).map p.pr) *ᵥ y) i) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sec_mul, p.sec_pr, mul_comm p.e, mul_assoc, e_mul_sec]

theorem col_mulVec {m : Type} [Fintype m] (Y : m → k) (t : Fin 1 → k) :
    Matrix.replicateCol (Fin 1) Y *ᵥ t = t 0 • Y := by
  funext i
  simp [Matrix.mulVec, dotProduct, Matrix.replicateCol, mul_comm]

theorem vec_emb {p : SplitPt D k} {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) {n : Type} [Fintype n]
    [DecidableEq n] {β : GlobalTheory.FinPl.Frame p A n} {β₀ : GlobalTheory.FinPl.Frame p S (n ⊕ Fin 1)} (hs : IsSumFrame o ζ β β₀)
    (g : GL n k) (x : n ⊕ Fin 1 → k) :
    (Formalism.L2.Theta.mt S (o.emb (β.gl g, 1))).map p.pr *ᵥ (β₀.b *ᵥ x) =
      β₀.b *ᵥ Sum.elim (g.val *ᵥ (x ∘ Sum.inl)) (x ∘ Sum.inr) := by
  have hA : (Formalism.L2.Theta.mt S (o.emb (β.gl g, 1))).map p.pr * o.jA.map p.pr = o.jA.map p.pr * (β.b * g.val * β.b') := by
    rw [← Matrix.map_mul, o.emb_jA, Matrix.map_mul, β.gl_mat]
  have hB : (Formalism.L2.Theta.mt S (o.emb (β.gl g, 1))).map p.pr * o.jB.map p.pr = o.jB.map p.pr := by
    rw [← Matrix.map_mul, o.emb_jB]
    simp
  have hz : (fun i => p.pr (ratV (vecB o ζ) i)) = o.jB.map p.pr *ᵥ (fun j => p.pr (incA D (ζ j))) := by
    funext i
    simp [ratV, vecB, Matrix.mulVec, dotProduct, OrthDec.jB, rat]
  have hY : (Formalism.L2.Theta.mt S (o.emb (β.gl g, 1))).map p.pr *ᵥ (fun i => p.pr (ratV (vecB o ζ) i)) =
      (fun i => p.pr (ratV (vecB o ζ) i)) := by
    rw [hz, Matrix.mulVec_mulVec, hB]
  rw [hs, Matrix.fromCols_mulVec, Matrix.fromCols_mulVec, col_mulVec, col_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul, hY,
    Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hA]
  have e : o.jA.map p.pr * (β.b * g.val * β.b') * β.b = (o.jA.map p.pr * β.b) * g.val := by
    simp only [Matrix.mul_assoc, β.b'b, Matrix.mul_one]
  rw [e, ← Matrix.mulVec_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr]

theorem mem_glued_iff {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]
    {β₀ : GlobalTheory.FinPl.Frame p S (n ⊕ Fin 1)} {M : Lat S} {q : GlobalTheory.LatPair.Unif k} {m : k} {P : GlobalTheory.LatPair.Pair k n}
    (hG : GluedW β₀ M q m P) (x : n ⊕ Fin 1 → k) :
    (fun i => p.sec ((β₀.b *ᵥ x) i)) ∈ latV S M (· = p.v) ↔
      ∃ s : 𝒪[k], x ∘ Sum.inl - s • P.vec ∈ P.ker ∧ m * x (Sum.inr 0) = q.inv * s := by
  rw [hG x, GlobalTheory.LevelUnfold.mem_gluedS, Sum.elim_comp_inl]
  refine exists_congr fun s => and_congr_right fun _ => ?_
  simp [Fin.forall_fin_one]

theorem glued_stab {n : Type} [Fintype n] [DecidableEq n] {q : GlobalTheory.LatPair.Unif k} {m : k} {P : GlobalTheory.LatPair.Pair k n}
    {g : GL n k} (hP : g • P = P) {u : n → k} {t : k}
    (h : ∃ s : 𝒪[k], u - s • P.vec ∈ P.ker ∧ m * t = q.inv * s) :
    ∃ s : 𝒪[k], g.val *ᵥ u - s • P.vec ∈ P.ker ∧ m * t = q.inv * s := by
  obtain ⟨hk, hv⟩ := (GlobalTheory.LatPair.Pair.smul_eq_iff P.hasVal_vec).1 hP
  obtain ⟨s, h1, h2⟩ := h
  refine ⟨s, ?_, h2⟩
  have h3 : g • (u - s • P.vec) ∈ P.ker := hk ▸ Submodule.smul_mem_pointwise_smul _ g _ h1
  have e : g.val *ᵥ u - s • P.vec = g • (u - s • P.vec) + s • (g • P.vec - P.vec) := by
    rw [smul_sub, smul_sub, smul_comm g s]
    change _ = g • u - _ + _
    change _ = g.val *ᵥ u - _ + _
    abel
  rw [e]
  exact add_mem h3 (P.ker.smul_mem s hv)

theorem glued_zero {n : Type} [Fintype n] [DecidableEq n] {q : GlobalTheory.LatPair.Unif k} {m : k} {P : GlobalTheory.LatPair.Pair k n}
    (u : n → k) : (∃ s : 𝒪[k], u - s • P.vec ∈ P.ker ∧ m * 0 = q.inv * s) ↔ u ∈ P.ker := by
  constructor
  · rintro ⟨s, h1, h2⟩
    have hs : (s : k) = 0 := by
      rw [mul_zero, eq_comm, mul_eq_zero] at h2
      exact h2.resolve_left (inv_ne_zero q.ne_zero)
    have hs' : s = 0 := Subtype.ext hs
    simpa [hs'] using h1
  · intro h
    exact ⟨0, by simpa using h, by simp⟩

end GlobalTheory.Core.Mi.LatMatch.StabPair


open GlobalTheory.Core.Mi.LatMatch.StabPair in
theorem GlobalTheory.Core.Mi.LatMatch.moves_emb_iff_smul_eq : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (n : Type) [Fintype n] [DecidableEq n] (β : GlobalTheory.FinPl.Frame p A n) (β₀ : GlobalTheory.FinPl.Frame p S (n ⊕ Fin 1)) (M : Lat S) (q : GlobalTheory.LatPair.Unif k) (m : k) (P : GlobalTheory.LatPair.Pair k n), IsSumFrame o ζ β β₀ → IsSelfDualC S M → m ≠ 0 → GluedW β₀ M q m P → ∀ g : GL n k, Moves S (o.emb (β.gl g, 1)) M M (· = p.v) ↔ g • P = P := by
  intro D k _ _ _ _ p S A L o ζ n _ _ β β₀ M q m P hs hM hm hG g
  have hE : ∀ x : n ⊕ Fin 1 → k, Formalism.L2.Theta.mt S (o.emb (β.gl g, 1)) *ᵥ (fun i => p.sec ((β₀.b *ᵥ x) i)) =
      fun i => p.sec ((β₀.b *ᵥ Sum.elim (g.val *ᵥ (x ∘ Sum.inl)) (x ∘ Sum.inr)) i) := fun x => by
    rw [mt_sec_any, vec_emb o ζ hs]
  constructor
  · intro hmov
    have hGG : ∀ (u : n → k) (t : k), (∃ s : 𝒪[k], u - s • P.vec ∈ P.ker ∧ m * t = q.inv * s) ↔
        ∃ s : 𝒪[k], g.val *ᵥ u - s • P.vec ∈ P.ker ∧ m * t = q.inv * s := fun u t => by
      have := hmov (fun i => p.sec ((β₀.b *ᵥ Sum.elim u fun _ => t) i)) (fun i => GlobalTheory.FinPl.FrameLat.sec_mem_idAt p _)
      rw [hE, mem_glued_iff hG, mem_glued_iff hG] at this
      simpa only [Sum.elim_comp_inl, Sum.elim_comp_inr, Sum.elim_inr, Function.comp_apply] using this
    rw [GlobalTheory.LatPair.Pair.smul_eq_iff P.hasVal_vec]
    have hker : ∀ u, u ∈ P.ker ↔ g.val *ᵥ u ∈ P.ker := fun u => by
      rw [← glued_zero (q := q) (m := m), ← glued_zero (q := q) (m := m), hGG]
    refine ⟨?_, ?_⟩
    · ext y
      rw [GlobalTheory.LatPair.mem_smul_iff, hker]
      change g.val *ᵥ ((g⁻¹ : GL n k).val *ᵥ y) ∈ P.ker ↔ _
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    · have h1 : ∃ s : 𝒪[k], P.vec - s • P.vec ∈ P.ker ∧ m * (m⁻¹ * q.inv) = q.inv * s :=
        ⟨1, by simp, by rw [← mul_assoc, mul_inv_cancel₀ hm, one_mul]; simp⟩
      obtain ⟨s, h2, h3⟩ := (hGG _ _).1 h1
      have hq : q.inv ≠ 0 := inv_ne_zero q.ne_zero
      have hs : (s : k) = 1 := by
        rw [← mul_assoc, mul_inv_cancel₀ hm, one_mul] at h3
        exact mul_left_cancel₀ hq (h3.symm.trans (mul_one _).symm)
      have hs' : s = 1 := Subtype.ext hs
      change g.val *ᵥ P.vec - P.vec ∈ P.ker
      simpa [hs'] using h2
  · intro hP
    refine (sMoves_one _ _ _ _).1 (GlobalTheory.T.normOneHomothety_carries_selfDual_of_splitComponent D k p S M M 1 _ hM hM (normOneAt_one _) fun x => ?_)
    rw [map_one, one_smul]
    obtain ⟨y, rfl⟩ : ∃ y, x = β₀.b *ᵥ y := ⟨β₀.b' *ᵥ x, by rw [Matrix.mulVec_mulVec, β₀.bb', Matrix.one_mulVec]⟩
    rw [vec_emb o ζ hs, mem_glued_iff hG, mem_glued_iff hG]
    simp only [Sum.elim_comp_inl, Sum.elim_inr, Function.comp_apply]
    refine ⟨glued_stab hP, fun h => ?_⟩
    have := glued_stab (inv_smul_eq_iff.2 hP.symm) h
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthogonalEmbeddingKeepsGluedCoreIffFixesPairStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonalEmbedding_keeps_gluedCore_iff_fixes_pair : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (n : Type) [Fintype n] [DecidableEq n] (β : GlobalTheory.FinPl.Frame p A n) (β₀ : GlobalTheory.FinPl.Frame p S (n ⊕ Fin 1)) (M : Lat S) (q : GlobalTheory.LatPair.Unif k) (m : k) (P : GlobalTheory.LatPair.Pair k n), IsSumFrame o ζ β β₀ → IsSelfDualC S M → m ≠ 0 → GluedW β₀ M q m P → ∀ g : GL n k, Moves S (o.emb (β.gl g, 1)) M M (· = p.v) ↔ g • P = P := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.moves_emb_iff_smul_eq | exact GlobalTheory.Core.Mi.LatMatch.moves_emb_iff_smul_eq | (intros; apply GlobalTheory.Core.Mi.LatMatch.moves_emb_iff_smul_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralElementHomotheticGluedCores
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch.CoreHomothety

variable {D : D7}

theorem mulVec_mem_idAt {P : GlobalTheory.FinPl.Pl D → Prop} {m l : ℕ} (X : Matrix (Fin m) (Fin l) (AE D))
    {y : Fin l → AE D} (hy : ∀ i, y i ∈ idAt D P) (i : Fin m) : (X *ᵥ y) i ∈ idAt D P := by
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)

theorem moves_inv {S : HSp D} {g : GA D S} {L M : Lat S} {P : GlobalTheory.FinPl.Pl D → Prop} (h : Moves S g L M P) :
    Moves S g⁻¹ M L P := by
  intro y hy
  have h1 := h (mt S g⁻¹ *ᵥ y) (mulVec_mem_idAt _ hy)
  have h2 : mt S g *ᵥ (mt S g⁻¹ *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, show mt S g * mt S g⁻¹ = mt S (g * g⁻¹) from rfl, mul_inv_cancel, mt_one,
      Matrix.one_mulVec]
  rw [h2] at h1
  exact h1.symm

theorem moves_trans {S : HSp D} {g h : GA D S} {L M N : Lat S} {P : GlobalTheory.FinPl.Pl D → Prop} (h1 : Moves S g L M P)
    (h2 : Moves S h M N P) : Moves S (h * g) L N P := by
  intro y hy
  rw [h1 y hy, h2 _ (mulVec_mem_idAt _ hy), Matrix.mulVec_mulVec]
  rfl

theorem moves_conj {S : HSp D} {h : GA D S} {L M : Lat S} {P : GlobalTheory.FinPl.Pl D → Prop} (hM : Moves S h L M P)
    (a : GA D S) : Moves S (h * a * h⁻¹) M M P ↔ Moves S a L L P := by
  constructor
  · intro H
    have e : h⁻¹ * (h * a * h⁻¹ * h) = a := by group
    have := moves_trans (moves_trans hM H) (moves_inv hM)
    rwa [e] at this
  · intro H
    have := moves_trans (moves_trans (moves_inv hM) H) hM
    rwa [← mul_assoc] at this

theorem sMoves_trans {S : HSp D} {c : AE D} {g h : GA D S} {L M N : Lat S} {v : GlobalTheory.FinPl.Pl D}
    (hS : SMoves S c g L M v) (hM : Moves S h M N (· = v)) : SMoves S c (h * g) L N v := by
  intro y hy
  rw [hS y hy, hM (c • (mt S g *ᵥ y)) (fun i => Ideal.mul_mem_left _ c (mulVec_mem_idAt _ hy i)),
    Matrix.mulVec_smul, Matrix.mulVec_mulVec]
  rfl

section Split

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]

theorem mem_gluedS_smul (q : GlobalTheory.LatPair.Unif k) {P P' : GlobalTheory.LatPair.Pair k n} {g : GL n k} {s : k} (hs : s ≠ 0)
    (hg : g.val = s • (1 : Matrix n n k)) (hP : P' = g • P) (u : n → k) (t : Fin 1 → k) :
    Sum.elim u t ∈ GlobalTheory.LatPair.gluedS q 1 P.ker P.vec ↔ Sum.elim (s • u) t ∈ GlobalTheory.LatPair.gluedS q 1 P'.ker P'.vec := by
  have hgx : ∀ x : n → k, g • x = s • x := fun x => by
    show g.val *ᵥ x = s • x
    rw [hg, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hgi : ∀ x : n → k, g⁻¹ • x = s⁻¹ • x := fun x => by
    have : x = g • (s⁻¹ • x) := by rw [hgx, smul_smul, mul_inv_cancel₀ hs, one_smul]
    conv_lhs => rw [this]
    rw [inv_smul_smul]
  have hker : ∀ x : n → k, x ∈ P'.ker ↔ s⁻¹ • x ∈ P.ker := fun x => by
    rw [hP, GlobalTheory.LatPair.Pair.smul_ker, GlobalTheory.LatPair.mem_smul_iff, hgi]
  have hvec : P'.vec - s • P.vec ∈ P'.ker := by
    have h1 := P.hasVal_vec.gl_smul g
    rw [← hP, hgx] at h1
    have := GlobalTheory.LatPair.Pair.sub_vec_mem h1
    rw [← neg_sub]
    exact neg_mem this
  rw [GlobalTheory.LevelUnfold.mem_gluedS, GlobalTheory.LevelUnfold.mem_gluedS]
  refine exists_congr fun σ => and_congr_left' ?_
  have e1 : (Sum.elim u t : n ⊕ Fin 1 → k) ∘ Sum.inl = u := rfl
  have e2 : (Sum.elim (s • u) t : n ⊕ Fin 1 → k) ∘ Sum.inl = s • u := rfl
  rw [e1, e2]
  have e3 : s • u - σ • P'.vec = s • (u - σ • P.vec) - σ • (P'.vec - s • P.vec) := by
    simp only [smul_sub]
    rw [smul_comm σ s P.vec]
    abel
  rw [e3, Submodule.sub_mem_iff_left _ (Submodule.smul_mem _ σ hvec), hker, smul_smul, inv_mul_cancel₀ hs, one_smul]

theorem emb_central_frame {p : SplitPt D k} {S A L : HSp D} {o : OrthDec S A L} {ζ : Fin L.rank → D.host.E}
    {β : GlobalTheory.FinPl.Frame p A n} {β₀ : GlobalTheory.FinPl.Frame p S (n ⊕ Fin 1)} (hsum : IsSumFrame o ζ β β₀) {a : GA D A}
    {c' : AE D} (ha : mt A a = c' • (1 : Matrix (Fin A.rank) (Fin A.rank) (AE D))) (y : n ⊕ Fin 1 → k) :
    (mt S (o.emb (a, 1))).map p.pr *ᵥ (β₀.b *ᵥ y) =
      β₀.b *ᵥ Sum.elim (fun i => p.pr c' * y (Sum.inl i)) (fun j => y (Sum.inr j)) := by
  have h3 : (mt A a).map p.pr = β.b * (p.pr c' • (1 : Matrix n n k)) * β.b' := by
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, β.bb', ha]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  have e := GlobalTheory.FinPl.Comm.block_calc p.pr _ _ _ _ _ _ _ (o.emb_jA a 1) (GlobalTheory.FinPl.Comm.emb_vecB o ζ a) h3 β.b'b
  rw [← hsum] at e
  rw [Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec]
  congr 1
  ext (i | j) <;> simp [Matrix.fromBlocks_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]

end Split

theorem exists_central_sMoves : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (n : Type) [Fintype n] [DecidableEq n] (β : GlobalTheory.FinPl.Frame p A n) (β₀ : GlobalTheory.FinPl.Frame p S (n ⊕ Fin 1)) (M M' : Lat S) (μ : D.host.E) (T : ℕ) (q : GlobalTheory.LatPair.Unif k) (P : GlobalTheory.LatPair.Pair k n) (a₀ : GA D A), 3 ≤ Fintype.card n → IsSumFrame o ζ β β₀ → IsSelfDualC S M → IsSelfDualC S M' → β₀.IsLat M (GlobalTheory.LatPair.gluedS q 1 P.ker P.vec) → μ ≠ 0 → LineAt (vecB o ζ) μ M' p.v → star ζ ⬝ᵥ L.gram *ᵥ ζ = -(μ * star μ * (T : D.host.E)) → valuation k (p.pr (incA D (T : D.host.E))) = valuation k ((q.1 : 𝒪[k]) : k) → (∀ a ∈ grpAt A (· = p.v), Moves S (o.emb (a, 1)) M M (· = p.v) ↔ Moves S (o.emb (a₀ * a * a₀⁻¹, 1)) M' M' (· = p.v)) → ∃ (a : GA D A) (c : AE D), CenAt A p.v a ∧ NormOneAt p.v c ∧ SMoves S c (o.emb (a₀ * a, 1)) M M' p.v := by
  intro D k _ _ _ _ p S A L o ζ n _ _ β β₀ M M' μ T q P a₀ hn hsum hM hM' hlat hμ hline hnorm hval hconj
  obtain ⟨M'', hsd'', hmv⟩ := (GlobalTheory.T.selfDual_image_adelicPoint_wittCore D S M' hM').1 (o.emb (a₀, 1))⁻¹
  have hmv' : Moves S (o.emb (a₀, 1)) M'' M' (· = p.v) := by
    have := moves_inv (hmv (· = p.v))
    rwa [inv_inv] at this
  have hline'' : LineAt (vecB o ζ) μ M'' p.v := by
    intro b hb
    rw [← hline b hb, hmv' (b • ratV (vecB o ζ)) (fun i => Ideal.mul_mem_right _ _ hb), Matrix.mulVec_smul,
      GlobalTheory.FinPl.Comm.emb_vecB]
  obtain ⟨P', hP'⟩ := GlobalTheory.T.selfDualCore_component_gluedAlongPair D k p S A L o ζ n β β₀ M'' μ T q hsum hsd'' hμ hline'' hnorm hval
  have hm : p.pr (incA D μ) ≠ 0 := by
    intro h0
    have h1 : p.pr (incA D μ * incA D μ⁻¹) = 1 := by rw [← map_mul, mul_inv_cancel₀ hμ, map_one, map_one]
    rw [map_mul, h0, zero_mul] at h1
    exact zero_ne_one h1
  have hW : GluedW β₀ M q 1 P := fun x => by
    have e : (Sum.elim (fun a => x (Sum.inl a)) (fun j => 1 * x (Sum.inr j)) : n ⊕ Fin 1 → k) = x := by
      ext (i | i) <;> simp
    rw [e]
    exact (hlat x).symm
  have hstab : ∀ g : GL n k, g • P = P ↔ g • P' = P' := fun g => by
    rw [← GlobalTheory.T.orthogonalEmbedding_keeps_gluedCore_iff_fixes_pair D k p S A L o ζ n β β₀ M q 1 P hsum hM one_ne_zero hW g,
      ← GlobalTheory.T.orthogonalEmbedding_keeps_gluedCore_iff_fixes_pair D k p S A L o ζ n β β₀ M'' q _ P' hsum hsd'' hm hP' g,
      hconj _ (GlobalTheory.FinPl.FrameLat.gl_mem_grpAt β g)]
    have e : o.emb (a₀ * β.gl g * a₀⁻¹, 1) = o.emb (a₀, 1) * o.emb (β.gl g, 1) * (o.emb (a₀, 1))⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul, Prod.inv_mk, Prod.mk_mul_mk, Prod.mk_mul_mk, inv_one, mul_one, mul_one]
    rw [e, moves_conj hmv']
  obtain ⟨g, s, hs, hg, hPP⟩ := GlobalTheory.T.latticeResiduePair_eq_scalar_of_same_stabilizer k n P P' hn hstab
  obtain ⟨c, hc, hcpr⟩ := GlobalTheory.T.exists_normOneIdele_with_splitPlace_component D k p (p.pr (incA D μ))⁻¹ (inv_ne_zero hm)
  obtain ⟨c', hc', hc'pr⟩ := GlobalTheory.T.exists_normOneIdele_with_splitPlace_component D k p (s * p.pr (incA D μ)) (mul_ne_zero hs hm)
  obtain ⟨a, hcen, hamt⟩ := GlobalTheory.T.exists_centralUnitary_scalar_of_normOneIdele D A p.v c' hc'
  refine ⟨a, c, hcen, hc, ?_⟩
  have key : SMoves S c (o.emb (a, 1)) M M'' p.v := by
    refine GlobalTheory.T.normOneHomothety_carries_selfDual_of_splitComponent D k p S M M'' c (o.emb (a, 1)) hM hsd'' hc fun x => ?_
    have hx : x = β₀.b *ᵥ (β₀.b' *ᵥ x) := by rw [Matrix.mulVec_mulVec, β₀.bb', Matrix.one_mulVec]
    rw [hx, emb_central_frame hsum hamt, ← Matrix.mulVec_smul, hW, hP']
    refine (mem_gluedS_smul q hs hg hPP _ _).trans (iff_of_eq ?_)
    congr 1
    ext (i | j)
    · simp only [Sum.elim_inl, Pi.smul_apply, smul_eq_mul, hcpr, hc'pr]
      field_simp
    · simp only [Sum.elim_inr, Pi.smul_apply, smul_eq_mul, hcpr]
      field_simp
  have e : o.emb (a₀ * a, 1) = o.emb (a₀, 1) * o.emb (a, 1) := by
    rw [← map_mul, Prod.mk_mul_mk, one_mul]
  rw [e]
  exact sMoves_trans key hmv'

end GlobalTheory.Core.Mi.LatMatch.CoreHomothety
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralElementHomotheticGluedCoresStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_central_element_homothetic_gluedCores : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (n : Type) [Fintype n] [DecidableEq n] (β : GlobalTheory.FinPl.Frame p A n) (β₀ : GlobalTheory.FinPl.Frame p S (n ⊕ Fin 1)) (M M' : Lat S) (μ : D.host.E) (T : ℕ) (q : GlobalTheory.LatPair.Unif k) (P : GlobalTheory.LatPair.Pair k n) (a₀ : GA D A), 3 ≤ Fintype.card n → IsSumFrame o ζ β β₀ → IsSelfDualC S M → IsSelfDualC S M' → β₀.IsLat M (GlobalTheory.LatPair.gluedS q 1 P.ker P.vec) → μ ≠ 0 → LineAt (vecB o ζ) μ M' p.v → star ζ ⬝ᵥ L.gram *ᵥ ζ = -(μ * star μ * (T : D.host.E)) → valuation k (p.pr (incA D (T : D.host.E))) = valuation k ((q.1 : 𝒪[k]) : k) → (∀ a ∈ grpAt A (· = p.v), Moves S (o.emb (a, 1)) M M (· = p.v) ↔ Moves S (o.emb (a₀ * a * a₀⁻¹, 1)) M' M' (· = p.v)) → ∃ (a : GA D A) (c : AE D), CenAt A p.v a ∧ NormOneAt p.v c ∧ SMoves S c (o.emb (a₀ * a, 1)) M M' p.v := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.CoreHomothety.exists_central_sMoves | exact GlobalTheory.Core.Mi.LatMatch.CoreHomothety.exists_central_sMoves | (intros; apply GlobalTheory.Core.Mi.LatMatch.CoreHomothety.exists_central_sMoves <;> assumption)
end
