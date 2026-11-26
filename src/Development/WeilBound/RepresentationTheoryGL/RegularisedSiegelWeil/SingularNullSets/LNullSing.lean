module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarScalingMultiplicative
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompositionStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColSqOfKerBasic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompInfSingleInfSelf

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NullSingOfIdemEx
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFrameLeftInvGram
open MeasureTheory Topology Filter GlobalTheory.CompanionTheory.NullFr
open scoped NNReal ENNReal Matrix
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.NullFr

theorem exists_frame_leftInv {A : Type} [CommRing A] {a r t : ℕ} (e : A) (x : Fx A a r) (v : Fx A a t)
    (P : Fx A r a) (M : Fx A t a) (hx : e • x = x) (hv : e • v = v) (hP : P * x = e • (1 : Fx A r r))
    (hM : M * (v - x * (P * v)) = e • (1 : Fx A t t)) :
    ∃ (L₁ : Fx A r a) (L₂ : Fx A t a), L₁ * x = e • (1 : Fx A r r) ∧ L₁ * v = 0 ∧ L₂ * x = 0 ∧
      L₂ * v = e • (1 : Fx A t t) := by
  have h2x : M * (1 - x * P) * x = 0 := by
    rw [Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hP, Matrix.mul_smul,
      Matrix.mul_one, hx, sub_self, Matrix.mul_zero]
  have h2v : M * (1 - x * P) * v = e • (1 : Fx A t t) := by
    rw [Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hM]
  have hPv : e • (P * v) = P * v := by
    rw [← Matrix.mul_smul, hv]
  refine ⟨P - (P * v) * (M * (1 - x * P)), M * (1 - x * P), ?_, ?_, h2x, h2v⟩
  · rw [Matrix.sub_mul, Matrix.mul_assoc, h2x, Matrix.mul_zero, sub_zero, hP]
  · rw [Matrix.sub_mul, Matrix.mul_assoc, h2v, Matrix.mul_smul, Matrix.mul_one, hPv, sub_self]

theorem exists_frame_leftInv_gram {A : Type} [CommRing A] {a r t : ℕ} (e : A) (x : Fx A a r) (v : Fx A a t)
    (B' B : Fx A r r) (C : Fx A r a) (H : Fx A a a) (M : Fx A t a) (hB : B' * B = 1)
    (hx : e • x = x) (hv : e • v = v) (hg : C * (H * x) = e • B)
    (hM : M * (v - x * (B' * (C * (H * v)))) = e • (1 : Fx A t t)) :
    ∃ (L₁ : Fx A r a) (L₂ : Fx A t a), L₁ * x = e • (1 : Fx A r r) ∧ L₁ * v = 0 ∧ L₂ * x = 0 ∧
      L₂ * v = e • (1 : Fx A t t) := by
  have hP : B' * (C * H) * x = e • (1 : Fx A r r) := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hg, Matrix.mul_smul, hB]
  have hM' : M * (v - x * (B' * (C * H) * v)) = e • (1 : Fx A t t) := by
    rw [Matrix.mul_assoc B', Matrix.mul_assoc C]
    exact hM
  exact exists_frame_leftInv e x v (B' * (C * H)) M hx hv hP hM'

theorem free_of_leftInv_orth {D : D7} {r t : ℕ} (V : HSp D) (b₀ : HermE D r) (hb : b₀.1.det ≠ 0) (e : AE D)
    (z : Mx D V.rank r × Mx D V.rank t) (hx : e • z.1 = z.1) (hv : e • z.2 = z.2)
    (hg : ip V z.1 z.1 = e • rat b₀.1)
    (M : Mx D t V.rank) (hM : mm M (z.2 - mm z.1 (yv V b₀ z)) = e • (1 : Mx D t t)) : Free e z := by
  have hB : rat b₀.1⁻¹ * rat b₀.1 = (1 : Mx D r r) := by
    have hu : IsUnit b₀.1.det := isUnit_iff_ne_zero.2 hb
    simp only [rat]
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
  exact exists_frame_leftInv_gram e z.1 z.2 (rat b₀.1⁻¹) (rat b₀.1) (adj z.1) (gA V) M hB hx hv hg hM

end GlobalTheory.CompanionTheory.NullFr
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GUEqOneAdd
open MeasureTheory Topology Filter GlobalTheory.CompanionTheory.NullFr
open scoped NNReal ENNReal Matrix

namespace GlobalTheory.CompanionTheory.NullFr

theorem gU_eq_one_add {A : Type} [CommRing A] {t : ℕ} (i : Fin t) (c₀ : Fin t → A) :
    gU i c₀ = 1 + Matrix.replicateCol Unit c₀ * Matrix.replicateRow Unit (Pi.single i (1 : A) : Fin t → A) := by
  unfold gU
  congr 1
  ext k j
  simp [Matrix.mul_apply, Pi.single_apply]

theorem det_gU {A : Type} [CommRing A] {t : ℕ} (i : Fin t) (c₀ : Fin t → A) (h : c₀ i = 0) :
    (gU i c₀).det = 1 := by
  rw [gU_eq_one_add, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp [h]

theorem exists_GL_gU : ∀ {A : Type} [CommRing A] {t : ℕ} (i : Fin t) (c₀ : Fin t → A) (_ : c₀ i = 0),
    ∃ g : GL (Fin t) A, g.1 = gU i c₀ ∧ Matrix.GeneralLinearGroup.det g = 1 := by
  intro A _ t i c₀ h
  refine ⟨Matrix.GeneralLinearGroup.mk'' (GlobalTheory.CompanionTheory.NullFr.gU i c₀)
    (by rw [GlobalTheory.CompanionTheory.NullFr.det_gU i c₀ h]; exact isUnit_one), rfl, ?_⟩
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  exact GlobalTheory.CompanionTheory.NullFr.det_gU i c₀ h

end GlobalTheory.CompanionTheory.NullFr
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PieceMeasureLtTop
open MeasureTheory Topology Filter GlobalTheory.CompanionTheory.NullFr
open scoped NNReal ENNReal Matrix

namespace GlobalTheory.CompanionTheory.NullFr

theorem entries_isCompact {A : Type} [TopologicalSpace A] {m n : ℕ} {C : Set A} (hC : IsCompact C) :
    IsCompact {M : Matrix (Fin m) (Fin n) A | ∀ p q, M p q ∈ C} := by
  have h : IsCompact (Set.pi Set.univ (fun _ : Fin m => Set.pi Set.univ (fun _ : Fin n => C))) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hC
  have e : {M : Matrix (Fin m) (Fin n) A | ∀ p q, M p q ∈ C} =
      Set.pi Set.univ (fun _ : Fin m => Set.pi Set.univ (fun _ : Fin n => C)) := by
    ext M
    exact ⟨fun h p _ q _ => h p q, fun h p q => h p (Set.mem_univ p) q (Set.mem_univ q)⟩
  rw [e]
  exact h

theorem exists_compact_comb {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (n : ℕ)
    {C₁ C₂ C₃ : Set A} (h₁ : IsCompact C₁) (h₂ : IsCompact C₂) (h₃ : IsCompact C₃) :
    ∃ D : Set A, IsCompact D ∧ ∀ (x : A) (b d : Fin n → A), x ∈ C₁ → (∀ k, b k ∈ C₂) → (∀ k, d k ∈ C₃) →
      x + ∑ k, b k * d k ∈ D := by
  have hK : IsCompact (C₁ ×ˢ ((Set.pi Set.univ (fun _ : Fin n => C₂)) ×ˢ
      (Set.pi Set.univ (fun _ : Fin n => C₃)))) :=
    h₁.prod ((isCompact_univ_pi fun _ => h₂).prod (isCompact_univ_pi fun _ => h₃))
  have hc : Continuous (fun w : A × (Fin n → A) × (Fin n → A) => w.1 + ∑ k, w.2.1 k * w.2.2 k) := by
    fun_prop
  refine ⟨_, hK.image hc, fun x b d hx hb hd => ⟨(x, b, d), ⟨hx, ?_, ?_⟩, rfl⟩⟩
  · exact fun k _ => hb k
  · exact fun k _ => hd k

theorem piece_measure_lt_top : ∀ {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] {a r t : ℕ}
    [MeasurableSpace (Fx A a r)] [MeasurableSpace (Fx A a t)] (e f : A) (P : Fx A a r → Fx A r a) (i : Fin t) (C : Set A)
    (_ : IsCompact C) (_ : (0 : A) ∈ C) (ν : Measure (Fx A a r × Fx A a t)) (_ : IsFiniteMeasureOnCompacts ν), ν (Piece e f P i C) < ∞ := by
  intro A _ _ _ a r t _ _ e f P i C hC h0 ν _
  obtain ⟨D₃, hD₃, h₃⟩ := exists_compact_comb (A := A) t hC hC hC
  have hS : IsCompact ((fun w : A × A => w.1 + w.2) '' (C ×ˢ C)) :=
    (hC.prod hC).image continuous_add
  obtain ⟨D, hD, hDm⟩ := exists_compact_comb (A := A) r (hC.union hD₃) hC hS
  refine lt_of_le_of_lt (measure_mono ?_)
    (((entries_isCompact (m := a) (n := r) hC).prod (entries_isCompact (m := a) (n := t) hD)).measure_lt_top)
  rintro z ⟨-, hz, hy, hv, hvi, c, hci, hc, hcv⟩
  refine ⟨hz, fun p k => ?_⟩
  have hyk : ∀ l, yc P z l k ∈ (fun w : A × A => w.1 + w.2) '' (C ×ˢ C) := fun l =>
    ⟨(f * yc P z l k, (1 - f) * yc P z l k), ⟨(hy l k).1, (hy l k).2⟩, by simp only; ring⟩
  have hvk : vc P z p k ∈ C ∪ D₃ := by
    by_cases hk : k = i
    · subst hk
      right
      have hmem := h₃ ((1 - f) * vc P z p k) c (fun j => if j = k then 0 else vc P z p j) (hvi p)
        (fun j => (hc j).2) (fun j => by
          by_cases hj : j = k
          · simpa [hj] using h0
          · simpa [hj] using hv p j hj)
      have hsum : ∑ j, c j * (if j = k then 0 else vc P z p j) = f * vc P z p k := by
        rw [hcv p]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : j = k
        · subst hj
          simp [hci]
        · simp [hj]
      rw [hsum] at hmem
      have hE : (1 - f) * vc P z p k + f * vc P z p k = vc P z p k := by ring
      rwa [hE] at hmem
    · exact Or.inl (hv p k hk)
  have hE : z.2 p k = vc P z p k + ∑ l, z.1 p l * yc P z l k := by
    simp [vc, Matrix.sub_apply, Matrix.mul_apply]
  rw [hE]
  exact hDm _ _ _ hvk (fun l => hz p l) hyk

end GlobalTheory.CompanionTheory.NullFr
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGlGD
open MeasureTheory Topology Filter GlobalTheory.CompanionTheory.NullFr
open scoped NNReal ENNReal Matrix

namespace GlobalTheory.CompanionTheory.NullFr

theorem gD_mul_gD {A : Type} [CommRing A] {t : ℕ} (i : Fin t) (u v : A) :
    gD i u * gD i v = gD i (u * v) := by
  unfold gD
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  by_cases h : k = i
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem gD_one {A : Type} [CommRing A] {t : ℕ} (i : Fin t) : gD i (1 : A) = 1 := by
  unfold gD
  have h : Function.update (1 : Fin t → A) i 1 = 1 := by
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [Function.update_of_ne hk]
  rw [h]
  exact Matrix.diagonal_one

theorem det_gD {A : Type} [CommRing A] {t : ℕ} (i : Fin t) (u : A) : (gD i u).det = u := by
  unfold gD
  rw [Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp

theorem exists_gl_gD : ∀ {A : Type} [CommRing A] {t : ℕ} (i : Fin t) (u : Aˣ),
    ∃ g : GL (Fin t) A, g.1 = gD i (u : A) ∧ Matrix.GeneralLinearGroup.det g = u := by
  intro A _ t i u
  refine ⟨⟨GlobalTheory.CompanionTheory.NullFr.gD i (u : A), GlobalTheory.CompanionTheory.NullFr.gD i ((u⁻¹ : Aˣ) : A), ?_, ?_⟩, rfl, ?_⟩
  · rw [GlobalTheory.CompanionTheory.NullFr.gD_mul_gD, Units.mul_inv, GlobalTheory.CompanionTheory.NullFr.gD_one]
  · rw [GlobalTheory.CompanionTheory.NullFr.gD_mul_gD, Units.inv_mul, GlobalTheory.CompanionTheory.NullFr.gD_one]
  · ext
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact GlobalTheory.CompanionTheory.NullFr.det_gD i (u : A)

end GlobalTheory.CompanionTheory.NullFr
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointEqTranslate
open MeasureTheory Topology Filter GlobalTheory.CompanionTheory.NullFr
open scoped NNReal ENNReal Matrix

namespace GlobalTheory.CompanionTheory.NullFr.CoverStep

variable {A : Type} [CommRing A] {a r t : ℕ}

private theorem yc_sub_mul_mul_mul_eq (e : A)
    (P : GlobalTheory.CompanionTheory.NullFr.Fx A a r → GlobalTheory.CompanionTheory.NullFr.Fx A r a)
    (z : GlobalTheory.CompanionTheory.NullFr.Fx A a r × GlobalTheory.CompanionTheory.NullFr.Fx A a t) (hP : P z.1 * z.1 = e • 1)
    (Y₀ : GlobalTheory.CompanionTheory.NullFr.Fx A r t) (hY₀ : e • Y₀ = Y₀) (S D : GlobalTheory.CompanionTheory.NullFr.Fx A t t) :
    GlobalTheory.CompanionTheory.NullFr.yc P (z.1, (z.2 - z.1 * Y₀) * S * D) =
      (GlobalTheory.CompanionTheory.NullFr.yc P z - Y₀) * S * D := by
  simp only [GlobalTheory.CompanionTheory.NullFr.yc]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_sub, ← Matrix.mul_assoc, hP,
    Matrix.smul_mul, Matrix.one_mul, hY₀]

private theorem vc_sub_mul_mul_mul_eq (e : A)
    (P : GlobalTheory.CompanionTheory.NullFr.Fx A a r → GlobalTheory.CompanionTheory.NullFr.Fx A r a)
    (z : GlobalTheory.CompanionTheory.NullFr.Fx A a r × GlobalTheory.CompanionTheory.NullFr.Fx A a t) (hP : P z.1 * z.1 = e • 1)
    (Y₀ : GlobalTheory.CompanionTheory.NullFr.Fx A r t) (hY₀ : e • Y₀ = Y₀) (S D : GlobalTheory.CompanionTheory.NullFr.Fx A t t) :
    GlobalTheory.CompanionTheory.NullFr.vc P (z.1, (z.2 - z.1 * Y₀) * S * D) = GlobalTheory.CompanionTheory.NullFr.vc P z * S * D := by
  simp only [GlobalTheory.CompanionTheory.NullFr.vc]
  rw [yc_sub_mul_mul_mul_eq e P z hP Y₀ hY₀ S D, ← Matrix.mul_assoc z.1,
    ← Matrix.mul_assoc z.1, ← Matrix.sub_mul, ← Matrix.sub_mul, Matrix.mul_sub z.1,
    sub_sub_sub_cancel_right]

theorem mul_gU_apply' {m : ℕ} (M : Fx A m t) (i : Fin t) (d : Fin t → A) (p : Fin m) (j : Fin t) :
    (M * gU i d) p j = M p j + if j = i then ∑ k, d k * M p k else 0 := by
  rw [GlobalTheory.CompanionTheory.NullFr.gU, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_apply]
  congr 1
  by_cases h : j = i
  · rw [if_pos h]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.of_apply, if_pos h, mul_comm]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Matrix.of_apply, if_neg h, mul_zero]

theorem mul_gD_apply' {m : ℕ} (M : Fx A m t) (i : Fin t) (u : A) (p : Fin m) (j : Fin t) :
    (M * gD i u) p j = if j = i then u * M p i else M p j := by
  rw [GlobalTheory.CompanionTheory.NullFr.gD, Matrix.mul_diagonal]
  by_cases h : j = i
  · subst h
    simp [mul_comm]
  · simp [h, Function.update_apply]

theorem mul_gU_gD_apply {m : ℕ} (M : Fx A m t) (i : Fin t) (c : Fin t → A) (u' : A) (p : Fin m)
    (j : Fin t) :
    (M * gU i (-c) * gD i u') p j =
      if j = i then u' * (M p i - ∑ k, c k * M p k) else M p j := by
  rw [GlobalTheory.CompanionTheory.NullFr.CoverStep.mul_gD_apply', GlobalTheory.CompanionTheory.NullFr.CoverStep.mul_gU_apply', GlobalTheory.CompanionTheory.NullFr.CoverStep.mul_gU_apply']
  by_cases h : j = i
  · rw [if_pos h, if_pos h, if_pos rfl]
    simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]
  · simp only [if_neg h, add_zero]

theorem gU_neg_mul (i : Fin t) (c : Fin t → A) (hc : c i = 0) : gU i (-c) * gU i c = 1 := by
  refine Matrix.ext fun p j => ?_
  rw [GlobalTheory.CompanionTheory.NullFr.CoverStep.mul_gU_apply']
  by_cases h : j = i
  · subst h
    simp [GlobalTheory.CompanionTheory.NullFr.gU, Matrix.one_apply, mul_add, Finset.sum_add_distrib, mul_ite,
      Finset.sum_ite_eq, Finset.sum_ite_eq', hc]
  · simp [GlobalTheory.CompanionTheory.NullFr.gU, h]

theorem gD_mul (i : Fin t) (u' u : A) (h : u' * u = 1) : gD i u' * gD i u = 1 := by
  refine Matrix.ext fun p q => ?_
  rw [GlobalTheory.CompanionTheory.NullFr.gD, GlobalTheory.CompanionTheory.NullFr.gD, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply,
    Matrix.one_apply]
  by_cases hpq : p = q
  · subst hpq
    by_cases hpi : p = i
    · subst hpi
      simp [h]
    · simp [Function.update_apply, hpi]
  · simp [hpq]

end GlobalTheory.CompanionTheory.NullFr.CoverStep

namespace GlobalTheory.CompanionTheory.NullFr.CoverStep

theorem point_eq_translate : ∀ {A : Type} [CommRing A] {a r t : ℕ} (e f : A) (_ : e * e = e) (_ : f * e = f) (_ : f * f = f) (P : Fx A a r → Fx A r a)
    (i : Fin t) (C : Set A) (z : Fx A a r × Fx A a t) (_ : z ∈ admitted e P) (_ : ∀ p q, z.1 p q ∈ C)
    (_ : ∀ l k, f * yc P z l k ∈ C ∧ (1 - f) * yc P z l k ∈ C)
    (_ : ∀ p k, k ≠ i → vc P z p k ∈ C) (_ : ∀ p, (1 - f) * vc P z p i ∈ C)
    (c : Fin t → A) (_ : c i = 0) (_ : ∀ k, f * c k = c k) (_ : ∀ p, f * vc P z p i = ∑ k, c k * vc P z p k)
    (u : Aˣ) (_ : (1 - f) * (u : A) = 1 - f)
    (c₀ c₁ : Fin t → A) (_ : c₀ i = 0) (_ : ∀ k, f * c₀ k = c₀ k) (_ : c₁ i = 0)
    (_ : ∀ k, f * c₁ k = c₁ k ∧ c₁ k ∈ C) (_ : ∀ k, c k = c₀ k + u * c₁ k)
    (y₀ y₁ : Fin r → A) (_ : ∀ l, f * y₀ l = y₀ l) (_ : ∀ l, f * y₁ l = y₁ l ∧ y₁ l ∈ C)
    (_ : ∀ l, f * yc P z l i - ∑ k, c₀ k * yc P z l k = y₀ l + u * y₁ l),
    ∃ w ∈ Piece e f P i C, z = (w.1, w.2 * gD i (u : A) * gU i c₀ + w.1 * yU i y₀) := by
  intro A _ a r t e f he hfe hff P i C z hz hz1 hY hKo hKi c hci hfc hfK u hu c₀ c₁ hc₀i hfc₀
    hc₁i hc₁ hc y₀ y₁ hfy₀ hy₁ hy
  simp only [GlobalTheory.CompanionTheory.NullFr.admitted, Set.mem_setOf_eq] at hz
  obtain ⟨hez1, hez2, hP⟩ := hz
  have hey₀ : ∀ l, e * y₀ l = y₀ l := fun l => by
    rw [← hfy₀ l, ← mul_assoc, mul_comm e f, hfe]
  have hY₀ : e • GlobalTheory.CompanionTheory.NullFr.yU i y₀ = GlobalTheory.CompanionTheory.NullFr.yU i y₀ := by
    refine Matrix.ext fun l j => ?_
    simp only [GlobalTheory.CompanionTheory.NullFr.yU, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    split_ifs
    · exact hey₀ l
    · exact mul_zero e
  have hY₀i : ∀ l, GlobalTheory.CompanionTheory.NullFr.yU i y₀ l i = y₀ l := fun l => by
    simp [GlobalTheory.CompanionTheory.NullFr.yU]
  have hu' : (1 - f) * ((u⁻¹ : Aˣ) : A) = 1 - f := by
    conv_lhs => rw [← hu]
    rw [mul_assoc, Units.mul_inv, mul_one]
  have h1fc₀ : ∀ k, (1 - f) * c₀ k = 0 := fun k => by
    rw [sub_mul, one_mul, hfc₀, sub_self]
  have h1fy₀ : ∀ l, (1 - f) * y₀ l = 0 := fun l => by
    rw [sub_mul, one_mul, hfy₀, sub_self]
  have hsum : ∀ l, ∑ k, c₀ k * (GlobalTheory.CompanionTheory.NullFr.yc P z - GlobalTheory.CompanionTheory.NullFr.yU i y₀) l k =
      ∑ k, c₀ k * GlobalTheory.CompanionTheory.NullFr.yc P z l k := by
    intro l
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : k = i
    · simp [hk, hc₀i]
    · simp [GlobalTheory.CompanionTheory.NullFr.yU, hk]
  have key : ∀ l, f * (GlobalTheory.CompanionTheory.NullFr.yc P z l i - y₀ l - ∑ k, c₀ k * GlobalTheory.CompanionTheory.NullFr.yc P z l k) =
      (u : A) * y₁ l := by
    intro l
    rw [mul_sub, mul_sub, hfy₀, Finset.mul_sum]
    simp_rw [← mul_assoc, hfc₀]
    rw [sub_right_comm, hy l, add_sub_cancel_left]
  have key2 : ∀ l, (1 - f) * (GlobalTheory.CompanionTheory.NullFr.yc P z l i - y₀ l -
      ∑ k, c₀ k * GlobalTheory.CompanionTheory.NullFr.yc P z l k) = (1 - f) * GlobalTheory.CompanionTheory.NullFr.yc P z l i := by
    intro l
    rw [mul_sub, mul_sub, h1fy₀, Finset.mul_sum]
    simp_rw [← mul_assoc, h1fc₀, zero_mul, Finset.sum_const_zero, sub_zero]
  have hD : GlobalTheory.CompanionTheory.NullFr.gD i ((u⁻¹ : Aˣ) : A) * GlobalTheory.CompanionTheory.NullFr.gD i (u : A) = 1 :=
    GlobalTheory.CompanionTheory.NullFr.CoverStep.gD_mul i _ _ u.inv_mul
  have hS : GlobalTheory.CompanionTheory.NullFr.gU i (-c₀) * GlobalTheory.CompanionTheory.NullFr.gU i c₀ = 1 :=
    GlobalTheory.CompanionTheory.NullFr.CoverStep.gU_neg_mul i c₀ hc₀i
  have hco := yc_sub_mul_mul_mul_eq e P z hP _ hY₀ (GlobalTheory.CompanionTheory.NullFr.gU i (-c₀))
    (GlobalTheory.CompanionTheory.NullFr.gD i ((u⁻¹ : Aˣ) : A))
  have hcm := vc_sub_mul_mul_mul_eq e P z hP _ hY₀ (GlobalTheory.CompanionTheory.NullFr.gU i (-c₀))
    (GlobalTheory.CompanionTheory.NullFr.gD i ((u⁻¹ : Aˣ) : A))
  refine ⟨(z.1, (z.2 - z.1 * GlobalTheory.CompanionTheory.NullFr.yU i y₀) * GlobalTheory.CompanionTheory.NullFr.gU i (-c₀) *
    GlobalTheory.CompanionTheory.NullFr.gD i ((u⁻¹ : Aˣ) : A)), ?_, ?_⟩
  · simp only [GlobalTheory.CompanionTheory.NullFr.Piece, GlobalTheory.CompanionTheory.NullFr.admitted, Set.mem_setOf_eq]
    rw [hco, hcm]
    refine ⟨⟨hez1, ?_, hP⟩, hz1, ?_, ?_, ?_, c₁, hc₁i, hc₁, ?_⟩
    · rw [← Matrix.smul_mul, ← Matrix.smul_mul, smul_sub, ← Matrix.smul_mul, hez2, hez1]
    · intro l k
      rw [GlobalTheory.CompanionTheory.NullFr.CoverStep.mul_gU_gD_apply]
      by_cases hk : k = i
      · rw [if_pos hk, hsum l, Matrix.sub_apply, hY₀i l]
        refine ⟨?_, ?_⟩
        · rw [mul_left_comm, key l, ← mul_assoc, Units.inv_mul, one_mul]
          exact (hy₁ l).2
        · rw [← mul_assoc, hu', key2 l]
          exact (hY l i).2
      · have hE : (GlobalTheory.CompanionTheory.NullFr.yc P z - GlobalTheory.CompanionTheory.NullFr.yU i y₀) l k =
            GlobalTheory.CompanionTheory.NullFr.yc P z l k := by
          simp [GlobalTheory.CompanionTheory.NullFr.yU, hk]
        rw [if_neg hk, hE]
        exact hY l k
    · intro p k hk
      rw [GlobalTheory.CompanionTheory.NullFr.CoverStep.mul_gU_gD_apply, if_neg hk]
      exact hKo p k hk
    · intro p
      rw [GlobalTheory.CompanionTheory.NullFr.CoverStep.mul_gU_gD_apply, if_pos rfl, ← mul_assoc, hu', mul_sub,
        Finset.mul_sum]
      simp_rw [← mul_assoc, h1fc₀, zero_mul, Finset.sum_const_zero, sub_zero]
      exact hKi p
    · intro p
      have hR : ∑ k, c₁ k * (GlobalTheory.CompanionTheory.NullFr.vc P z * GlobalTheory.CompanionTheory.NullFr.gU i (-c₀) *
          GlobalTheory.CompanionTheory.NullFr.gD i ((u⁻¹ : Aˣ) : A)) p k = ∑ k, c₁ k * GlobalTheory.CompanionTheory.NullFr.vc P z p k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [GlobalTheory.CompanionTheory.NullFr.CoverStep.mul_gU_gD_apply]
        by_cases hk : k = i
        · simp [hk, hc₁i]
        · rw [if_neg hk]
      have hL : f * (GlobalTheory.CompanionTheory.NullFr.vc P z p i - ∑ k, c₀ k * GlobalTheory.CompanionTheory.NullFr.vc P z p k) =
          (u : A) * ∑ k, c₁ k * GlobalTheory.CompanionTheory.NullFr.vc P z p k := by
        rw [mul_sub, hfK p, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← mul_assoc, hfc₀, ← sub_mul, hc k, add_sub_cancel_left, mul_assoc]
      rw [hR, GlobalTheory.CompanionTheory.NullFr.CoverStep.mul_gU_gD_apply, if_pos rfl, mul_left_comm, hL,
        ← mul_assoc, Units.inv_mul, one_mul]
  · refine Prod.ext rfl ?_
    dsimp only
    rw [Matrix.mul_assoc _ (GlobalTheory.CompanionTheory.NullFr.gD i ((u⁻¹ : Aˣ) : A)) (GlobalTheory.CompanionTheory.NullFr.gD i (u : A)),
      hD, Matrix.mul_one, Matrix.mul_assoc _ (GlobalTheory.CompanionTheory.NullFr.gU i (-c₀)) (GlobalTheory.CompanionTheory.NullFr.gU i c₀), hS,
      Matrix.mul_one, sub_add_cancel]

end GlobalTheory.CompanionTheory.NullFr.CoverStep
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDependentColumn
open MeasureTheory Topology Filter GlobalTheory.CompanionTheory.NullFr
open scoped NNReal ENNReal Matrix

namespace GlobalTheory.CompanionTheory.NullFr.Coeff

variable {A : Type} [CommRing A]

theorem mul_eq_zero_of_mem {f : A} (hf : f * f = f) {x : A}
    (hx : x ∈ Ideal.span ({1 - f} : Set A)) : f * x = 0 := by
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
  linear_combination (-y) * hf

theorem mem_of_mul_eq_zero {f x : A} (hx : f * x = 0) :
    x ∈ Ideal.span ({1 - f} : Set A) :=
  Ideal.mem_span_singleton'.2 ⟨x, by linear_combination (-1 : A) * hx⟩

theorem isMaximal_span {f : A} (hf : IsFieldIdem f) :
    (Ideal.span ({1 - f} : Set A)).IsMaximal := by
  refine Ideal.isMaximal_iff.2 ⟨fun h => hf.ne ?_, fun J x hJ hx hxJ => ?_⟩
  · simpa using mul_eq_zero_of_mem hf.idem h
  · have hne : f * x ≠ 0 := fun h => hx (mem_of_mul_eq_zero h)
    obtain ⟨y, hy⟩ := hf.inv x hne
    have h1 : (1 - f) ∈ J := hJ (Ideal.subset_span rfl)
    have h2 : x * (f * y) ∈ J := J.mul_mem_right _ hxJ
    have : (1 : A) = (1 - f) + x * (f * y) := by linear_combination (-1 : A) * hy
    rw [this]
    exact J.add_mem h1 h2

theorem alt_of_field {K : Type} [Field K] (π : A →+* K) (hs : Function.Surjective π) {f : A}
    (hf : f * f = f) (h1 : π f = 1) (h0 : ∀ x, π x = 0 → f * x = 0) {a t : ℕ} (v : Fx A a t) :
    (∃ M : Fx A t a, f • (M * v) = f • (1 : Fx A t t)) ∨
      ∃ (i : Fin t) (c : Fin t → A), c i = 0 ∧ (∀ k, f * c k = c k) ∧
        ∀ p, f * v p i = ∑ k, c k * v p k := by
  classical
  set w : Matrix (Fin a) (Fin t) K := v.map π with hw
  by_cases hli : LinearIndependent K w.col
  · left
    have hinj : Function.Injective w.mulVecLin := Matrix.mulVec_injective_iff.2 hli
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective w.mulVecLin
      (LinearMap.ker_eq_bot.2 hinj)
    set N : Matrix (Fin t) (Fin a) K := LinearMap.toMatrix' g with hN
    have hNw : N * w = 1 := by
      have : LinearMap.toMatrix' (g ∘ₗ w.mulVecLin) = N * w := by
        rw [LinearMap.toMatrix'_comp, hN]
        congr 1
        rw [← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
      rw [← this, hg, LinearMap.toMatrix'_id]
    choose l hl using hs
    refine ⟨Matrix.of fun p q => l (N p q), ?_⟩
    have hmap : ((Matrix.of fun p q => l (N p q) : Fx A t a) * v).map π = 1 := by
      rw [Matrix.map_mul, ← hNw]
      congr 1
      ext p q
      simp [hl]
    ext p q
    have hpq := congrFun (congrFun hmap p) q
    have hz : π (((Matrix.of fun p q => l (N p q) : Fx A t a) * v) p q - (1 : Fx A t t) p q) = 0 := by
      rw [map_sub, sub_eq_zero]
      have hpq' : π (((Matrix.of fun p q => l (N p q) : Fx A t a) * v) p q) = (1 : Matrix (Fin t) (Fin t) K) p q := hpq
      rw [hpq']
      by_cases h : p = q
      · subst h
        rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
      · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h, map_zero]
    have := h0 _ hz
    simp only [Matrix.smul_apply, smul_eq_mul]
    linear_combination this
  · right
    obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.1 hli
    set b : Fin t → K := fun k => if k = i then 0 else -(g k / g i) with hb
    choose l hl using hs
    refine ⟨i, fun k => f * l (b k), ?_, fun k => ?_, fun p => ?_⟩
    · have : π (l (b i)) = 0 := by simp [hl, hb]
      exact h0 _ this
    · rw [← mul_assoc, hf]
    · have hrow : ∑ k, g k * w p k = 0 := by
        have := congrFun hg p
        simpa [Matrix.col_apply, Finset.sum_apply] using this
      have hz : π (v p i - ∑ k, l (b k) * v p k) = 0 := by
        have hw' : ∀ k, π (v p k) = w p k := fun k => rfl
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sub, map_sum]
        simp only [map_mul, hl, hw']
        have hsum : ∑ k, b k * w p k = w p i := by
          have hsplit : ∀ k, b k * w p k = -(g i)⁻¹ * (g k * w p k) +
              (if k = i then w p i else 0) := by
            intro k
            by_cases h : k = i
            · subst h
              simp only [hb, if_true]
              field_simp
              ring
            · simp only [hb, if_neg h]
              field_simp
              ring
          rw [Finset.sum_congr rfl fun k _ => hsplit k, Finset.sum_add_distrib,
            ← Finset.mul_sum, hrow]
          simp
        rw [hsum, sub_self]
      have := h0 _ hz
      rw [mul_sub, Finset.mul_sum, sub_eq_zero] at this
      rw [this]
      exact Finset.sum_congr rfl fun k _ => by ring

theorem exists_dependent_column {A : Type} [CommRing A] {ι : Type} [Fintype ι] (e : A) (f : ι → A)
    (hd : IsFieldDec e f) {a t : ℕ} (v : Fx A a t)
    (hv : ¬ ∃ M : Fx A t a, M * v = e • (1 : Fx A t t)) :
    ∃ (j : ι) (i : Fin t) (c : Fin t → A), c i = 0 ∧ (∀ k, f j * c k = c k) ∧
      ∀ p, f j * v p i = ∑ k, c k * v p k := by
  classical
  have key : ∀ j, (∃ M : Fx A t a, f j • (M * v) = f j • (1 : Fx A t t)) ∨
      ∃ (i : Fin t) (c : Fin t → A), c i = 0 ∧ (∀ k, f j * c k = c k) ∧
        ∀ p, f j * v p i = ∑ k, c k * v p k := by
    intro j
    have hj := hd.field j
    haveI := isMaximal_span hj
    letI : Field (A ⧸ Ideal.span ({1 - f j} : Set A)) := Ideal.Quotient.field _
    refine alt_of_field (Ideal.Quotient.mk (Ideal.span ({1 - f j} : Set A)))
      Ideal.Quotient.mk_surjective hj.idem ?_ ?_ v
    · rw [← map_one (Ideal.Quotient.mk (Ideal.span ({1 - f j} : Set A)))]
      refine Ideal.Quotient.eq.2 ?_
      have : f j - 1 = (-1 : A) * (1 - f j) := by ring
      rw [this]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
    · intro x hx
      exact mul_eq_zero_of_mem hj.idem (Ideal.Quotient.eq_zero_iff_mem.1 hx)
  by_contra hno
  have hall : ∀ j, ∃ M : Fx A t a, f j • (M * v) = f j • (1 : Fx A t t) := fun j =>
    (key j).resolve_right fun ⟨i, c, h⟩ => hno ⟨j, i, c, h⟩
  choose M hM using hall
  refine hv ⟨∑ j, f j • M j, ?_⟩
  rw [Matrix.sum_mul, ← hd.sum, Finset.sum_smul]
  exact Finset.sum_congr rfl fun j _ => by rw [Matrix.smul_mul, hM j]

end GlobalTheory.CompanionTheory.NullFr.Coeff
end

open MeasureTheory Topology Filter GlobalTheory.CompanionTheory.NullFr
open scoped NNReal ENNReal Matrix

namespace GlobalTheory.CompanionTheory.NullFr

theorem scale_image {Z : Type} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z] (ν : Measure Z) (φ : Z ≃ₜ Z) (s : ℝ≥0)
    (h : ν.map φ = s • ν) (B : Set Z) : (s : ℝ≥0∞) * ν (φ '' B) = ν B := by
  have h1 : (ν.map φ) (φ '' B) = ν B := by
    have h2 := φ.toMeasurableEquiv.map_apply (μ := ν) (φ '' B)
    have h3 : (φ.toMeasurableEquiv : Z → Z) ⁻¹' (φ '' B) = B := by
      ext x; simp
    rw [h3] at h2
    exact h2
  rw [h] at h1
  rw [← h1, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]

section
variable {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] {a r t : ℕ}

def colH (g : GL (Fin t) A) : (Fx A a r × Fx A a t) ≃ₜ (Fx A a r × Fx A a t) where
  toFun z := (z.1, z.2 * g.1)
  invFun z := (z.1, z.2 * (g⁻¹).1)
  left_inv z := by
    have : g.1 * (g⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    simp [Matrix.mul_assoc, this]
  right_inv z := by
    have : (g⁻¹).1 * g.1 = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    simp [Matrix.mul_assoc, this]
  continuous_toFun := continuous_fst.prodMk (continuous_snd.matrix_mul continuous_const)
  continuous_invFun := continuous_fst.prodMk (continuous_snd.matrix_mul continuous_const)

def shH (y : Fx A r t) : (Fx A a r × Fx A a t) ≃ₜ (Fx A a r × Fx A a t) where
  toFun z := (z.1, z.2 + z.1 * y)
  invFun z := (z.1, z.2 - z.1 * y)
  left_inv z := by simp
  right_inv z := by simp
  continuous_toFun := continuous_fst.prodMk (continuous_snd.add (continuous_fst.matrix_mul continuous_const))
  continuous_invFun := continuous_fst.prodMk (continuous_snd.sub (continuous_fst.matrix_mul continuous_const))

end

section
variable {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] {a r t : ℕ}
  [MeasurableSpace (Fx A a r)] [MeasurableSpace (Fx A a t)] [BorelSpace (Fx A a r × Fx A a t)]

theorem exists_strictHenselian_absolutely_closed_local_ring (md : Aˣ →* ℝ≥0) (e : A) (ν : Measure (Fx A a r × Fx A a t))
    (invS : ∀ y : Fx A r t, e • y = y → ν.map (fun z : Fx A a r × Fx A a t => (z.1, z.2 + z.1 * y)) = ν)
    (cov : ∀ g : GL (Fin t) A, e • (g.1 - 1) = g.1 - 1 → ν.map (fun z : Fx A a r × Fx A a t => (z.1, z.2 * g.1)) =
      ((md (Matrix.GeneralLinearGroup.det g))⁻¹ ^ (r + t) : ℝ≥0) • ν) (i : Fin t) (c₀ : Fin t → A) (y₀ : Fin r → A)
    (hc₀ : c₀ i = 0) (hce : ∀ k, e * c₀ k = c₀ k) (hye : ∀ l, e * y₀ l = y₀ l) :
    ∃ φ : (Fx A a r × Fx A a t) ≃ₜ (Fx A a r × Fx A a t), ν.map φ = ν ∧
      ∀ w, φ w = (w.1, w.2 * gU i c₀ + w.1 * yU i y₀) := by
  obtain ⟨g, hg, hdet⟩ := GlobalTheory.CompanionTheory.NullFr.exists_GL_gU i c₀ hc₀
  have h1 : e • (g.1 - 1) = g.1 - 1 := by
    rw [hg]
    ext k j
    simp only [gU, add_sub_cancel_left, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    split_ifs <;> simp [hce]
  have h2 : e • yU i y₀ = (yU i y₀ : Fx A r t) := by
    ext l j
    simp only [yU, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    split_ifs <;> simp [hye]
  have c1 : ν.map (colH (a := a) (r := r) g) = ν := by
    have := cov g h1
    rw [hdet, map_one, inv_one, one_pow, one_smul] at this
    exact this
  have c2 : ν.map (shH (a := a) (yU i y₀ : Fx A r t)) = ν := invS _ h2
  refine ⟨(colH g).trans (shH (yU i y₀)), ?_, fun w => ?_⟩
  · have m1 : Measurable (colH (a := a) (r := r) g) := (colH g).continuous.measurable
    have m2 : Measurable (shH (a := a) (yU i y₀ : Fx A r t)) := (shH _).continuous.measurable
    have : (((colH (a := a) (r := r) g).trans (shH (yU i y₀)) : _ ≃ₜ _) : _ → _) = shH (yU i y₀) ∘ colH g := rfl
    rw [this, ← Measure.map_map m2 m1, c1, c2]
  · show (w.1, w.2 * g.1 + w.1 * yU i y₀) = _
    rw [hg]
end

section
variable {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [LocallyCompactSpace A] [T2Space A]
  [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A] {a r t : ℕ}
  [MeasurableSpace (Fx A a r)] [MeasurableSpace (Fx A a t)] [BorelSpace (Fx A a r × Fx A a t)]

theorem piece_null (md : Aˣ →* ℝ≥0) (hmd : IsHaarMod md) (e f : A) (he : e * e = e) (hfe : f * e = f) (hf : IsFieldIdem f)
    (hnd : NonDiscreteAt f) (P : Fx A a r → Fx A r a) (ν : Measure (Fx A a r × Fx A a t)) (hfin : IsFiniteMeasureOnCompacts ν)
    (invS : ∀ y : Fx A r t, e • y = y → ν.map (fun z : Fx A a r × Fx A a t => (z.1, z.2 + z.1 * y)) = ν)
    (cov : ∀ g : GL (Fin t) A, e • (g.1 - 1) = g.1 - 1 → ν.map (fun z : Fx A a r × Fx A a t => (z.1, z.2 * g.1)) =
      ((md (Matrix.GeneralLinearGroup.det g))⁻¹ ^ (r + t) : ℝ≥0) • ν) (i : Fin t) (C : Set A) (hC : IsCompact C)
    (hC0 : C ∈ 𝓝 (0 : A)) : ν (Piece e f P i C) = 0 := by
  classical
  have h0C : (0 : A) ∈ C := mem_of_mem_nhds hC0
  set B := Piece e f P i C with hB
  have hBfin : ν B < ∞ := GlobalTheory.CompanionTheory.NullFr.piece_measure_lt_top e f P i C hC h0C ν hfin
  let C₂ : Set A := (fun q : A × (Fin t → A) × (Fin t → A) => q.1 - ∑ k, q.2.1 k * q.2.2 k) ''
    (C ×ˢ (Set.pi Set.univ fun _ => C) ×ˢ (Set.pi Set.univ fun _ => C))
  have hC₂ : IsCompact C₂ :=
    (hC.prod ((isCompact_univ_pi fun _ => hC).prod (isCompact_univ_pi fun _ => hC))).image (by fun_prop)
  obtain ⟨κ₁, V₁, hV₁, hn₁⟩ := GlobalTheory.CompanionTheory.NullFr.Packing.net md hmd f hf.idem C C hC hC0
  obtain ⟨κ₂, V₂, hV₂, hn₂⟩ := GlobalTheory.CompanionTheory.NullFr.Packing.net md hmd f hf.idem C₂ C hC₂ hC0
  let Ti := {k : Fin t // k ≠ i}
  have hT : Fintype.card Ti + 1 = t := by
    have := Fintype.card_subtype_compl (fun k : Fin t => k = i)
    have h1 : Fintype.card {k : Fin t // k = i} = 1 := by simp
    have h2 : 0 < t := i.pos
    simp only [Fintype.card_fin, h1] at this
    change Fintype.card {k : Fin t // ¬ k = i} + 1 = t
    omega
  let κ : ℝ≥0 := κ₁ ^ Fintype.card Ti * κ₂ ^ r
  obtain ⟨u, hu, huV, hε⟩ := GlobalTheory.CompanionTheory.NullFr.exists_unit_small_module md hmd f hf hnd (1 / (κ + 1)) (by positivity) (V₁ ∩ V₂) (Filter.inter_mem hV₁ hV₂)
  obtain ⟨N₁, hN₁, hcard₁, hcov₁⟩ := hn₁ u hu huV.1
  obtain ⟨N₂, hN₂, hcard₂, hcov₂⟩ := hn₂ u hu huV.2
  let ext : (Ti → A) → Fin t → A := fun c' k => if h : k ≠ i then c' ⟨k, h⟩ else 0
  have ext_i : ∀ c', ext c' i = 0 := fun c' => by simp [ext]
  have ext_ne : ∀ c' (k : Ti), ext c' k.1 = c' k := fun c' k => by simp [ext, k.2]
  have eq_of_f : ∀ p : A, f * p = p → e * p = p := fun p hp => by
    rw [← hp, ← mul_assoc, mul_comm e f, hfe]
  let Q : Finset ((Ti → A) × (Fin r → A)) :=
    Fintype.piFinset (fun _ => N₁) ×ˢ Fintype.piFinset (fun _ => N₂)
  have hTq : ∀ q ∈ Q, ∃ φ : (Fx A a r × Fx A a t) ≃ₜ (Fx A a r × Fx A a t), ν.map φ = ν ∧
      ∀ w, φ w = (w.1, w.2 * gU i (ext q.1) + w.1 * yU i q.2) := by
    intro q hq
    obtain ⟨h1, h2⟩ := Finset.mem_product.1 hq
    rw [Fintype.mem_piFinset] at h1 h2
    refine exists_strictHenselian_absolutely_closed_local_ring md e ν invS cov i _ _ (ext_i _) (fun k => ?_) (fun l => eq_of_f _ (hN₂ _ (h2 l)).1)
    by_cases h : k = i
    · subst h; simp [ext_i]
    · have := ext_ne q.1 ⟨k, h⟩
      simp only at this
      rw [this]
      exact eq_of_f _ (hN₁ _ (h1 _)).1
  haveI : Nonempty ((Fx A a r × Fx A a t) ≃ₜ (Fx A a r × Fx A a t)) := ⟨Homeomorph.refl _⟩
  choose! T hT1 hT2 using hTq
  obtain ⟨gd, hgd, hdetd⟩ := GlobalTheory.CompanionTheory.NullFr.exists_gl_gD i u
  have hue : e * ((u : A) - 1) = (u : A) - 1 := by
    have h1 : (u : A) - 1 = f * u - f := by linear_combination hu
    rw [h1]
    have h2 : e * (f * u - f) = (f * e) * u - f * e := by ring
    rw [h2, hfe]
  have hgde : e • (gd.1 - 1) = gd.1 - 1 := by
    rw [hgd]
    ext k j
    simp only [gD, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Matrix.diagonal_apply, Matrix.one_apply]
    by_cases hkj : k = j
    · subst hkj
      by_cases hki : k = i
      · subst hki; simpa using hue
      · simp [hki]
    · simp [hkj]
  let Dh : (Fx A a r × Fx A a t) ≃ₜ (Fx A a r × Fx A a t) := colH gd
  have hmapD : ν.map Dh = ((md u)⁻¹ ^ (r + t) : ℝ≥0) • ν := by
    have := cov gd hgde
    rw [hdetd] at this
    exact this
  have hDB := scale_image ν Dh _ hmapD B
  have hcover : B ⊆ ⋃ q ∈ Q, T q '' (Dh '' B) := by
    rintro z ⟨hadm, hx, hy, hv, hv', c, hci, hc, hcv⟩
    have hpick : ∀ k : Ti, ∃ p ∈ N₁, ∃ w ∈ C, f * w = w ∧ c k.1 = p + u * w := fun k =>
      hcov₁ (c k.1) (hc k.1).2 (hc k.1).1
    choose p hpN w hwC hwf hpw using hpick
    have hc₀f : ∀ k, f * ext p k = ext p k := fun k => by
      by_cases h : k = i
      · subst h; simp [ext_i]
      · have := ext_ne p ⟨k, h⟩
        simp only at this
        rw [this]; exact (hN₁ _ (hpN _)).1
    have hc₀C : ∀ k, ext p k ∈ C := fun k => by
      by_cases h : k = i
      · subst h; simpa [ext_i] using h0C
      · have := ext_ne p ⟨k, h⟩
        simp only at this
        rw [this]; exact (hN₁ _ (hpN _)).2
    have hc₁ : ∀ k, f * ext w k = ext w k ∧ ext w k ∈ C := fun k => by
      by_cases h : k = i
      · subst h; simpa [ext_i] using h0C
      · have := ext_ne w ⟨k, h⟩
        simp only at this
        rw [this]; exact ⟨hwf _, hwC _⟩
    have hcc : ∀ k, c k = ext p k + u * ext w k := fun k => by
      by_cases h : k = i
      · subst h; simp [ext_i, hci]
      · have h1 := ext_ne w ⟨k, h⟩
        have h2 := ext_ne p ⟨k, h⟩
        simp only at h1 h2
        rw [h1, h2]; exact hpw ⟨k, h⟩
    have hterm : ∀ l, f * yc P z l i - ∑ k, ext p k * yc P z l k ∈ C₂ := fun l => by
      refine ⟨(f * yc P z l i, ext p, fun k => f * yc P z l k), ⟨(hy l i).1, fun k _ => hc₀C k, fun k _ => (hy l k).1⟩, ?_⟩
      simp only
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← mul_assoc, mul_comm (ext p k) f, hc₀f]
    have hfterm : ∀ l, f * (f * yc P z l i - ∑ k, ext p k * yc P z l k) = f * yc P z l i - ∑ k, ext p k * yc P z l k := fun l => by
      rw [mul_sub, ← mul_assoc, hf.idem, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← mul_assoc, hc₀f]
    have hpick2 : ∀ l, ∃ q ∈ N₂, ∃ w ∈ C, f * w = w ∧ f * yc P z l i - ∑ k, ext p k * yc P z l k = q + u * w := fun l =>
      hcov₂ _ (hterm l) (hfterm l)
    choose y₀ hyN y₁ hy₁C hy₁f hyy using hpick2
    obtain ⟨w', hw', hz'⟩ := GlobalTheory.CompanionTheory.NullFr.CoverStep.point_eq_translate e f he hfe hf.idem P i C z hadm hx hy hv hv' c hci (fun k => (hc k).1) hcv u hu (ext p) (ext w)
      (ext_i _) hc₀f (ext_i _) hc₁ hcc y₀ y₁ (fun l => (hN₂ _ (hyN l)).1) (fun l => ⟨hy₁f l, hy₁C l⟩) hyy
    have hq : (p, y₀) ∈ Q := Finset.mem_product.2 ⟨Fintype.mem_piFinset.2 hpN, Fintype.mem_piFinset.2 hyN⟩
    refine Set.mem_biUnion hq ⟨Dh w', ⟨w', hw', rfl⟩, ?_⟩
    rw [hT2 _ hq, hz']
    show ((w'.1, (w'.2 * gd.1) * gU i (ext p) + w'.1 * yU i y₀) : Fx A a r × Fx A a t) = _
    rw [hgd]
  set m : ℝ≥0 := md u with hm
  have hm0 : m ≠ 0 := by
    intro h
    have h1 : md u * md u⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    rw [← hm, h, zero_mul] at h1
    exact zero_ne_one h1
  have hDval : ν (Dh '' B) = ((m ^ (r + t) : ℝ≥0) : ℝ≥0∞) * ν B := by
    rw [← hDB, ← mul_assoc, ← ENNReal.coe_mul, ← mul_pow, mul_inv_cancel₀ hm0, one_pow, ENNReal.coe_one, one_mul]
  have hTval : ∀ q ∈ Q, ν (T q '' (Dh '' B)) = ν (Dh '' B) := fun q hq => by
    have := scale_image ν (T q) 1 (by rw [hT1 q hq, one_smul]) (Dh '' B)
    simpa using this
  have hle : ν B ≤ (Q.card : ℝ≥0∞) * ν (Dh '' B) := by
    calc ν B ≤ ν (⋃ q ∈ Q, T q '' (Dh '' B)) := measure_mono hcover
      _ ≤ ∑ q ∈ Q, ν (T q '' (Dh '' B)) := measure_biUnion_finset_le _ _
      _ = ∑ q ∈ Q, ν (Dh '' B) := Finset.sum_congr rfl hTval
      _ = _ := by simp
  have hcardQ : (Q.card : ℝ≥0) = (N₁.card : ℝ≥0) ^ Fintype.card Ti * (N₂.card : ℝ≥0) ^ r := by
    simp [Q, Finset.card_product, Fintype.card_piFinset]
  have hρ : (Q.card : ℝ≥0) * m ^ (r + t) ≤ κ * m := by
    have h1 : r + t = Fintype.card Ti + r + 1 := by omega
    rw [hcardQ, h1, pow_succ, pow_add]
    calc _ = ((N₁.card : ℝ≥0) * m) ^ Fintype.card Ti * (((N₂.card : ℝ≥0) * m) ^ r) * m := by
          rw [mul_pow, mul_pow]; ring
      _ ≤ κ * m := by
          refine mul_le_mul_left ?_ m
          exact mul_le_mul' (pow_le_pow_left' hcard₁ _) (pow_le_pow_left' hcard₂ _)
  have hlt : κ * m < 1 := by
    have h1 : m * (κ + 1) < 1 := by
      have := (lt_div_iff₀ (by positivity : 0 < κ + 1)).1 hε
      simpa using this
    calc κ * m ≤ m * (κ + 1) := by rw [mul_add, mul_one, mul_comm]; exact le_self_add
      _ < 1 := h1
  set ρ : ℝ≥0 := (Q.card : ℝ≥0) * m ^ (r + t) with hρdef
  have hρ1 : ρ < 1 := lt_of_le_of_lt hρ hlt
  have hle2 : ν B ≤ (ρ : ℝ≥0∞) * ν B := by
    calc ν B ≤ (Q.card : ℝ≥0∞) * ν (Dh '' B) := hle
      _ = (ρ : ℝ≥0∞) * ν B := by
          rw [hDval, ← mul_assoc, hρdef, ENNReal.coe_mul, ENNReal.coe_natCast]
  obtain ⟨b, hb⟩ : ∃ b : ℝ≥0, (b : ℝ≥0∞) = ν B := ⟨(ν B).toNNReal, ENNReal.coe_toNNReal hBfin.ne⟩
  rw [← hb] at hle2 ⊢
  have hb2 : b ≤ ρ * b := by exact_mod_cast hle2
  by_contra h0
  have hb0 : 0 < b := pos_iff_ne_zero.2 fun h => h0 (by simp [h])
  exact absurd hb2 (not_le.2 (mul_lt_of_lt_one_left hb0 hρ1))
end

section
variable {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [LocallyCompactSpace A] [T2Space A]
  [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A] {a r t : ℕ}
  [MeasurableSpace (Fx A a r)] [MeasurableSpace (Fx A a t)] [BorelSpace (Fx A a r × Fx A a t)]

theorem frames_null {ι : Type} [Fintype ι] (md : Aˣ →* ℝ≥0) (hmd : IsHaarMod md) (e : A) (f : ι → A) (hd : IsFieldDec e f)
    (hnd : ∀ j, NonDiscreteAt (f j)) (P : Fx A a r → Fx A r a) (ν : Measure (Fx A a r × Fx A a t))
    (hfin : IsFiniteMeasureOnCompacts ν)
    (invS : ∀ y : Fx A r t, e • y = y → ν.map (fun z : Fx A a r × Fx A a t => (z.1, z.2 + z.1 * y)) = ν)
    (cov : ∀ g : GL (Fin t) A, e • (g.1 - 1) = g.1 - 1 → ν.map (fun z : Fx A a r × Fx A a t => (z.1, z.2 * g.1)) =
      ((md (Matrix.GeneralLinearGroup.det g))⁻¹ ^ (r + t) : ℝ≥0) • ν)
    (supp : ν (admitted e P)ᶜ = 0) : ν {z | ¬ ∃ M : Fx A t a, M * vc P z = e • (1 : Fx A t t)} = 0 := by
  classical
  have hfe : ∀ j, f j * e = f j := fun j => by
    rw [← hd.sum, Finset.mul_sum, Finset.sum_eq_single j (fun b _ hb => hd.orth j b hb.symm) (by simp), (hd.field j).idem]
  have he : e * e = e := by
    nth_rw 1 [← hd.sum]
    rw [Finset.sum_mul, Finset.sum_congr rfl fun j _ => hfe j, hd.sum]
  let K : CompactExhaustion A := default
  obtain ⟨n₀, hn₀⟩ := K.exists_mem_nhds (0 : A)
  have ev : ∀ x : A, ∀ᶠ n in atTop, x ∈ K (n + n₀) := fun x => by
    obtain ⟨m, hm⟩ := K.exists_mem x
    exact eventually_atTop.2 ⟨m, fun n hn => K.subset (by omega) hm⟩
  have hsub : {z | ¬ ∃ M : Fx A t a, M * vc P z = e • (1 : Fx A t t)} ⊆
      (admitted e P)ᶜ ∪ ⋃ j, ⋃ i, ⋃ n, Piece e (f j) P i (K (n + n₀)) := by
    intro z hz
    by_cases hadm : z ∈ admitted e P
    · right
      obtain ⟨j, i, c, hci, hcf, hcv⟩ := GlobalTheory.CompanionTheory.NullFr.Coeff.exists_dependent_column e f hd (vc P z) hz
      have hall : ∀ᶠ n in atTop, (∀ p q, z.1 p q ∈ K (n + n₀)) ∧
          (∀ l k, f j * yc P z l k ∈ K (n + n₀) ∧ (1 - f j) * yc P z l k ∈ K (n + n₀)) ∧
          (∀ p k, vc P z p k ∈ K (n + n₀)) ∧ (∀ p, (1 - f j) * vc P z p i ∈ K (n + n₀)) ∧ ∀ k, c k ∈ K (n + n₀) := by
        refine (eventually_all.2 fun p => eventually_all.2 fun q => ev _).and
          ((eventually_all.2 fun l => eventually_all.2 fun k => (ev _).and (ev _)).and
          ((eventually_all.2 fun p => eventually_all.2 fun k => ev _).and
          ((eventually_all.2 fun p => ev _).and (eventually_all.2 fun k => ev _))))
      obtain ⟨n, h1, h2, h3, h4, h5⟩ := hall.exists
      simp only [Set.mem_union, Set.mem_iUnion]
      exact ⟨j, i, n, hadm, h1, h2, fun p k _ => h3 p k, h4, c, hci, fun k => ⟨hcf k, h5 k⟩, hcv⟩
    · exact Or.inl hadm
  refine measure_mono_null hsub (measure_union_null supp ?_)
  refine measure_iUnion_null fun j => measure_iUnion_null fun i => measure_iUnion_null fun n => ?_
  exact piece_null md hmd e (f j) he (hfe j) (hd.field j) (hnd j) P ν hfin invS cov i _ (K.isCompact _)
    (Filter.mem_of_superset hn₀ (K.subset (by omega)))
end

end GlobalTheory.CompanionTheory.NullFr

section
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.NullFr


set_option maxHeartbeats 1600000 in
theorem nullSing_of_idemEx : IdemEx → NullSing := by
  intro hI D r t V b₀ hb S e he ν hν
  haveI : IsTopologicalRing (AE D) := GlobalTheory.Doubling.isTopologicalRing_tens
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele D.host.F
  obtain ⟨eh⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (AF D.host.F)
  haveI : LocallyCompactSpace (AE D) := eh.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE D) := eh.secondCountableTopology
  haveI : T2Space (AE D) := eh.isEmbedding.t2Space
  haveI : BorelSpace (AE D) := ⟨rfl⟩
  haveI b1 : BorelSpace (Mx D V.rank r) := @BorelSpace.mk _ _ (measMx _ _) rfl
  haveI b2 : BorelSpace (Mx D V.rank t) := @BorelSpace.mk _ _ (measMx _ _) rfl
  haveI s1 : SecondCountableTopology (Mx D V.rank r) := inferInstanceAs (SecondCountableTopology (Fin V.rank → Fin r → AE D))
  haveI s2 : SecondCountableTopology (Mx D V.rank t) := inferInstanceAs (SecondCountableTopology (Fin V.rank → Fin t → AE D))
  haveI b3 : BorelSpace (Mx D V.rank r × Mx D V.rank t) := Prod.borelSpace
  obtain ⟨ι, _, f, hd, hnd⟩ := GlobalTheory.CompanionTheory.NullFr.FieldDec.exists_isFieldDec D S e he
  have hmd : IsHaarMod (absA D) := fun h hh u =>
    GlobalTheory.AdeleUnitModule.map_mul_eq_absE_inv_smul _ _ D.sp.cm.sig (isCMExt_host D) h hh u
  let P : Mx D V.rank r → Mx D r V.rank := fun x => mm (rat b₀.1⁻¹) (mm (adj x) (gA V))
  have hyv : ∀ z : Mx D V.rank r × Mx D V.rank t, yc P z = yv V b₀ z := fun z => by
    simp only [yc, P, yv, ip, mm, Matrix.mul_assoc]
  have hinv : mm (rat b₀.1⁻¹) (rat b₀.1) = (1 : Mx D r r) := by
    have h1 : b₀.1⁻¹ * b₀.1 = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hb)
    have h2 : (b₀.1⁻¹ * b₀.1).map (incA D) = (rat b₀.1⁻¹ : Mx D r r) * rat b₀.1 := Matrix.map_mul
    have h3 : ((1 : Matrix (Fin r) (Fin r) D.host.E)).map (incA D) = (1 : Mx D r r) := Matrix.map_one _ (map_zero _) (map_one _)
    rw [h1, h3] at h2
    exact h2.symm
  have hsupp : ν (admitted e P)ᶜ = 0 := by
    refine measure_mono_null ?_ hν.supp
    rintro z hz ⟨g1, g2, g3, -⟩
    refine hz ⟨g1, g2, ?_⟩
    show mm (mm (rat b₀.1⁻¹) (mm (adj z.1) (gA V))) z.1 = _
    have h4 : mm (mm (rat b₀.1⁻¹) (mm (adj z.1) (gA V))) z.1 = mm (rat b₀.1⁻¹) (ip V z.1 z.1) := by
      simp only [ip, mm, Matrix.mul_assoc]
    rw [h4, g3]
    simp only [mm, Matrix.mul_smul] at hinv ⊢
    rw [hinv]
  have key := frames_null (absA D) hmd e f hd hnd P ν hν.fin hν.invS hν.cov hsupp
  refine measure_mono_null ?_ (measure_union_null hν.supp key)
  intro z hz
  by_cases hg : e • z.1 = z.1 ∧ e • z.2 = z.2 ∧ ip V z.1 z.1 = e • rat b₀.1 ∧ qv V b₀ z = 0
  · right
    rintro ⟨M, hM⟩
    refine hz (GlobalTheory.CompanionTheory.NullFr.free_of_leftInv_orth V b₀ hb e z hg.1 hg.2.1 hg.2.2.1 M ?_)
    rw [← hyv]
    exact hM
  · exact Or.inl hg

end GlobalTheory.CompanionTheory.NullFr
end
end

namespace PositivityTheory.Rg.Rsw.L

theorem nullSing : IdemEx → NullSing := GlobalTheory.CompanionTheory.NullFr.nullSing_of_idemEx

end PositivityTheory.Rg.Rsw.L
