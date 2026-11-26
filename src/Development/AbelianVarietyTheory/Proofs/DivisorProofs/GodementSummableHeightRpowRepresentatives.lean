module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardRationalPointsFixerTorusClassesLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyPotentialSemiAbelianSplitTorus

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableHeightRpowParabolicCosets
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableAbsDetRationalPointsGodement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLowerBoundDiagonalExponentsRationalPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLowerBoundDiagonalExponentsRationalPoint
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SphEis

theorem exists_bound_exponents : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∀ W : Set (GAd σ J), IsCompact W → ∃ m₀ : ℕ, ∀ q ∈ fixG σ J C, ∀ l : Fin j → ℤ, ∀ w ∈ W, q * lv (tor F E l) * w ∈ ratPts σ J → ∀ i, -(m₀ : ℤ) ≤ l i := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF lv hlv W hW
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  set P : Matrix (Fin j) (Fin n) (AF F ⊗[F] E) := adMat F (cT (σ : E →+* E) C * J) with hP
  have hq : ∀ q ∈ fixG σ J C, P * (matHom _ σ J q).1 = P := by
    intro q hq
    have h1 : (matHom _ σ J q⁻¹).1 * adMat F C = adMat F C * (1 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) := by
      rw [Matrix.mul_one]; exact inv_mem hq
    have h := form_mul_of_mul_cols h1
    rwa [inv_inv, Formalism.UG.cT_one, Matrix.one_mul] at h
  have hl : ∀ α, P * (matHom _ σ J (lv α)).1 = cT (sigR (AF F) σ) (α⁻¹).1 * P := by
    intro α
    have h := form_mul_of_mul_cols (hlv.onC α⁻¹)
    rwa [map_inv lv α, inv_inv] at h
  have hc : Continuous fun w : GAd σ J => P * (matHom _ σ J w).1 :=
    continuous_const.matrix_mul (Units.continuous_val.comp (isEmbedding_matHom (AF F) σ J).continuous)
  have hb : GlobalTheory.Eis.Conv.Bdd fun w : W => (w : GAd σ J) := ⟨W, hW, fun w => w.2⟩
  obtain ⟨Ω, hΩ, hΩw⟩ := GlobalTheory.Eis.Conv.Bdd.entries (GlobalTheory.Eis.Conv.Bdd.map hb hc)
  obtain ⟨m₀, hm₀⟩ := (GlobalTheory.T.compact_adeles_rational_points_finite_eventually_zero F E Ω hΩ).2
  refine ⟨m₀, fun q hqm l w hw hg i => ?_⟩
  have ht : cT (sigR (AF F) σ) (tor F E l)⁻¹.1 = (tor F E l)⁻¹.1 :=
    congrArg Units.val (GlobalTheory.Eis.Conv.cti_dg (GlobalTheory.Eis.Conv.sigR_halfE σ) l)
  have h1 : P * (matHom _ σ J (q * lv (tor F E l) * w)).1 = (tor F E l)⁻¹.1 * (P * (matHom _ σ J w).1) := by
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hq q hqm, hl, ht,
      Matrix.mul_assoc]
  generalize q * lv (tor F E l) * w = g at hg h1
  have hg' : matHom _ σ J g ∈ HFin (AF F) σ J := Subgroup.mem_subgroupOf.1 hg
  obtain ⟨γ, -, e⟩ := Subgroup.mem_map.1 hg'
  have hm : (matHom _ σ J g).1 = γ.1.map (inclR (F := F) (AF F)) := by
    rw [← e]; rfl
  have hy : (cT (σ : E →+* E) C * J * γ.1).map (inclR (F := F) (AF F)) = P * (matHom _ σ J g).1 := by
    rw [hm, Matrix.map_mul]
  have hrow : ¬∀ x, (cT (σ : E →+* E) C * J * γ.1) i x = 0 :=
    GlobalTheory.GodementSectionReduction.row_ne_zero (N := γ⁻¹.1 * D) (by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc γ.1, Units.mul_inv, Matrix.one_mul, hF.cd]) i
  have hrow' : ¬∀ x, (cT (σ : E →+* E) C * J * γ.1).map (inclR (F := F) (AF F)) i x = 0 := fun h =>
    hrow fun x => by
      have := h x
      rwa [Matrix.map_apply, map_eq_zero_iff _ GlobalTheory.AutFunCompare.inclA_injective] at this
  exact GlobalTheory.GodementSectionReduction.bound_aux (inclR (F := F) (AF F)) hm₀ (fun i x => hΩw ⟨w, hw⟩ i x) (hy.trans h1) i hrow'

end GlobalTheory.SphEis

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLowerBoundDiagonalExponentsRationalPointStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lowerBound_diagonalExponents_rationalPoint : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∀ W : Set (GAd σ J), IsCompact W → ∃ m₀ : ℕ, ∀ q ∈ fixG σ J C, ∀ l : Fin j → ℤ, ∀ w ∈ W, q * lv (tor F E l) * w ∈ ratPts σ J → ∀ i, -(m₀ : ℤ) ≤ l i := by
  first | exact @GlobalTheory.SphEis.exists_bound_exponents | exact GlobalTheory.SphEis.exists_bound_exponents | (intros; apply GlobalTheory.SphEis.exists_bound_exponents <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionLeviGLIsotropicFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionLeviGLIsotropicFrame
noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem reduce_gl_cm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (hc : IsCMExt F E σ) (j : ℕ) : ∃ (L : Set (GL (Fin j) (AF F ⊗[F] E))) (B : ℝ), IsCompact L ∧
    ∀ α : GL (Fin j) (AF F ⊗[F] E), ∃ (δ : GL (Fin j) E) (l : Fin j → ℤ), ∃ c ∈ L,
      bc (inclR (F := F) (AF F)) δ * α = tor F E l * c ∧
      (absE F E (Matrix.GeneralLinearGroup.det α) : ℝ) ≤ B * ∏ i, (bse F ^ l i)⁻¹ :=
  haveI := GlobalTheory.Doubling.t2Space_adeleRing' (F := F)
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  haveI := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension (F := F) (E := E) (R := AF F)
  GlobalTheory.GodementSectionReduction.reduction_GL_diagonalUnitPowers_compact (inclR (F := F) (AF F)) GlobalTheory.Doubling.continuous_absE
    (fun u => GlobalTheory.Doubling.absE_inclR u) (by positivity)
    (by rw [GlobalTheory.T.tensorIdeleNormalizedAbs_ideleHalfAtInfinity _ _ _ hc]; simp) (GlobalTheory.Eis.Conv.red_gl _ _ _ hc j)

theorem reduce_levi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∃ (W : Set (GAd σ J)) (B : ℝ), IsCompact W ∧ ∀ (p : GAd σ J) (β : GL (Fin j) (AF F ⊗[F] E)), (matHom _ σ J p).1 * adMat F C = adMat F C * β.1 → ∃ γ ∈ ratPts σ J, γ ∈ parFlag σ J C (fun _ => 0) ∧ ∃ q ∈ fixG σ J C, ∃ l : Fin j → ℤ, ∃ w ∈ W, γ * p = q * lv (tor F E l) * w ∧ (absE F E (Matrix.GeneralLinearGroup.det β) : ℝ) ≤ B * ∏ i, (bse F ^ l i)⁻¹ := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF lv hl
  obtain ⟨L, B, hL, hR⟩ := reduce_gl_cm hF.cm j
  refine ⟨lv '' L, B, hL.image hl.cont, fun p β hp => ?_⟩
  obtain ⟨δ, l, c, hc, hred, hle⟩ := hR β
  have h1 := hl.rat δ
  generalize bc (inclR (F := F) (AF F)) δ = u at h1 hred
  refine ⟨lv u, h1, ⟨⟨u.1, fun _ _ h => absurd h (lt_irrefl _), hl.onC u⟩,
    (u⁻¹).1, fun _ _ h => absurd h (lt_irrefl _), by rw [← map_inv]; exact hl.onC u⁻¹⟩,
    lv u * p * lv (u * β)⁻¹, ?_, l, lv c, ⟨c, hc, rfl⟩, ?_, hle⟩
  · change _ * _ = _
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc, hl.onC, ← Matrix.mul_assoc,
      Matrix.mul_assoc _ _ (adMat F C), hp, ← Matrix.mul_assoc, hl.onC, Matrix.mul_assoc, Matrix.mul_assoc,
      ← Matrix.mul_assoc u.1, ← Units.val_mul, Units.mul_inv, Matrix.mul_one]
  · rw [mul_assoc _ (lv _) (lv c), ← map_mul, ← hred, map_inv, inv_mul_cancel_right]

end GlobalTheory.SphEis

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionLeviGLIsotropicFrameStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_leviGL_isotropicFrame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∃ (W : Set (GAd σ J)) (B : ℝ), IsCompact W ∧ ∀ (p : GAd σ J) (β : GL (Fin j) (AF F ⊗[F] E)), (matHom _ σ J p).1 * adMat F C = adMat F C * β.1 → ∃ γ ∈ ratPts σ J, γ ∈ parFlag σ J C (fun _ => 0) ∧ ∃ q ∈ fixG σ J C, ∃ l : Fin j → ℤ, ∃ w ∈ W, γ * p = q * lv (tor F E l) * w ∧ (absE F E (Matrix.GeneralLinearGroup.det β) : ℝ) ≤ B * ∏ i, (bse F ^ l i)⁻¹ := by
  first | exact @GlobalTheory.SphEis.reduce_levi | exact GlobalTheory.SphEis.reduce_levi | (intros; apply GlobalTheory.SphEis.reduce_levi <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableAbsDetRationalPointsGodement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

open scoped Pointwise

noncomputable section

namespace GlobalTheory.SphEis.Summ

theorem tor_add (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {j : ℕ}
    (μ : Fin j → ℕ) (m₀ : ℕ) :
    tor F E (fun i => (μ i : ℤ) + -(m₀ : ℤ)) = tor F E (fun i => (μ i : ℤ)) * tor F E (fun _ => -(m₀ : ℤ)) :=
  Units.ext (by
    change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
    rw [Matrix.diagonal_mul_diagonal]
    exact congrArg Matrix.diagonal (funext fun i => congrArg Units.val (_root_.zpow_add _ _ _)))

theorem summable_absDet : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∀ (ι : Type) (x p k : ι → GAd σ J) (β : ι → GL (Fin j) (AF F ⊗[F] E)) (K : Set (GAd σ J)), IsCompact K → (∀ q, x q ∈ ratPts σ J) → (∀ q, x q = p q * k q) → (∀ q, k q ∈ K) → (∀ q, (matHom _ σ J (p q)).1 * adMat F C = adMat F C * (β q).1) → (∀ q q', x q' * (x q)⁻¹ ∈ parFlag σ J C (fun _ => 0) → q = q') → ∀ t : ℝ, ((m + j : ℕ) : ℝ) < t → Summable fun q => (absE F E (Matrix.GeneralLinearGroup.det (β q)) : ℝ) ^ t := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF lv hlv ι x p k β K hK hx e hk hβ hi t ht
  classical
  have hb : 1 < bse F := one_lt_pow₀ (by norm_num) Fintype.card_ne_zero
  have hb0 : 0 < bse F := one_pos.trans hb
  have hfp : fixG σ J C ≤ parFlag σ J C (fun _ => 0) := fun g hg =>
    ⟨⟨1, Matrix.blockTriangular_one, by rw [Matrix.mul_one]; exact hg⟩, 1, Matrix.blockTriangular_one, by
      rw [Matrix.mul_one]; exact inv_mem hg⟩
  obtain ⟨W, B, hW, hR⟩ := GlobalTheory.T.reduction_leviGL_isotropicFrame F E σ n J j m C D Z J₀ hF lv hlv
  choose γ hγ hγP q hq l w hw hred hle using fun i => hR (p i) (β i) (hβ i)
  have hWK : IsCompact (W * K) := hW.mul hK
  obtain ⟨m₀, hm₀⟩ := GlobalTheory.T.exists_lowerBound_diagonalExponents_rationalPoint F E σ n J j m C D Z J₀ hF lv hlv (W * K) hWK
  have hl : ∀ i r, -(m₀ : ℤ) ≤ l i r := fun i =>
    hm₀ (q i) (hq i) (l i) (w i * k i) (Set.mul_mem_mul (hw i) (hk i)) (by
      have := mul_mem (hγ i) (hx i)
      rwa [e, ← mul_assoc, hred, mul_assoc _ (w i)] at this)
  obtain ⟨μ, hμ⟩ : ∃ μ : ι → Fin j → ℕ, ∀ i, l i = fun r => (μ i r : ℤ) + -(m₀ : ℤ) :=
    ⟨fun i r => (l i r + m₀).toNat, fun i => funext fun r => by have := hl i r; beta_reduce; omega⟩
  obtain ⟨a, ha⟩ : ∃ a, a = lv (tor F E fun _ => -(m₀ : ℤ)) := ⟨_, rfl⟩
  have hW' : IsCompact ((fun g => a * g) '' (W * K)) := hWK.image (continuous_const_mul a)
  obtain ⟨N, hN⟩ := GlobalTheory.T.card_rationalPoints_fixer_torusClasses_le F E σ n J j m C D Z J₀ hF lv hlv _ hW'
  have hz : ∀ i, γ i * x i = q i * lv (tor F E fun r => (μ i r : ℤ)) * (a * (w i * k i)) := fun i => by
    rw [e, ← mul_assoc, hred, hμ, tor_add, map_mul, ← ha]
    simp only [mul_assoc]
  have hinj : ∀ i i', γ i' * x i' * (γ i * x i)⁻¹ ∈ fixG σ J C → i = i' := fun i i' h => hi i i' (by
    have h2 : x i' * (x i)⁻¹ = (γ i')⁻¹ * (γ i' * x i' * (γ i * x i)⁻¹) * γ i := by group
    rw [h2]
    exact mul_mem (mul_mem (inv_mem (hγP i')) (hfp h)) (hγP i))
  refine GlobalTheory.GodementSectionReduction.summable_of_count ι j (m + j) (bse F) (max (B * bse F ^ (m₀ * j)) N) t μ _ hb ht
    (fun i => ⟨NNReal.coe_nonneg _, ?_⟩) fun μ' S hS => ?_
  · refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    refine (hle i).trans (le_of_eq ?_)
    rw [mul_assoc, hμ]
    simp only [zpow_add₀ hb0.ne', _root_.zpow_neg, zpow_natCast, mul_inv, inv_inv, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_mul]
    rw [mul_comm (∏ _, _)]
  · refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
    have hc : (S.image fun i => γ i * x i).card = S.card :=
      Finset.card_image_of_injOn fun i _ i' _ h => hinj i i' (by
        rw [← h, mul_inv_cancel]
        exact one_mem _)
    rw [← hc]
    refine hN μ' _ ?_ ?_ ?_
    · intro s hs
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hs
      exact mul_mem (hγ i) (hx i)
    · intro s hs s' hs' h
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hs
      obtain ⟨i', -, rfl⟩ := Finset.mem_image.1 hs'
      rw [hinj i i' h]
    · intro s hs
      obtain ⟨i, hi', rfl⟩ := Finset.mem_image.1 hs
      exact ⟨q i, hq i, a * (w i * k i), ⟨w i * k i, Set.mul_mem_mul (hw i) (hk i), rfl⟩, by rw [hz, hS i hi']⟩

end GlobalTheory.SphEis.Summ

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableAbsDetRationalPointsGodementStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_absDet_rational_points_godement : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∀ (ι : Type) (x p k : ι → GAd σ J) (β : ι → GL (Fin j) (AF F ⊗[F] E)) (K : Set (GAd σ J)), IsCompact K → (∀ q, x q ∈ ratPts σ J) → (∀ q, x q = p q * k q) → (∀ q, k q ∈ K) → (∀ q, (matHom _ σ J (p q)).1 * adMat F C = adMat F C * (β q).1) → (∀ q q', x q' * (x q)⁻¹ ∈ parFlag σ J C (fun _ => 0) → q = q') → ∀ t : ℝ, ((m + j : ℕ) : ℝ) < t → Summable fun q => (absE F E (Matrix.GeneralLinearGroup.det (β q)) : ℝ) ^ t := by
  first | exact @GlobalTheory.SphEis.Summ.summable_absDet | exact GlobalTheory.SphEis.Summ.summable_absDet | (intros; apply GlobalTheory.SphEis.Summ.summable_absDet <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableHeightRpowParabolicCosets
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem summable_height_rpow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)), Submodule.IsFullLattice E L → (∀ g : GAd σ J, ∃ (p : GAd σ J) (β : GL (Fin j) (AF F ⊗[F] E)), (matHom _ σ J p).1 * adMat F C = adMat F C * β.1 ∧ ∃ k ∈ levelAll σ J L a, g = p * k) → ∀ h : GAd σ J → ℝ≥0, (∀ (p : GAd σ J) (β : GL (Fin j) (AF F ⊗[F] E)), (matHom _ σ J p).1 * adMat F C = adMat F C * β.1 → ∀ k ∈ levelAll σ J L a, h (p * k) = absE F E (Matrix.GeneralLinearGroup.det β)) → ∀ (g : GAd σ J) (t : ℝ), (n : ℝ) - j < t → Summable fun q : GlobalTheory.Eis.Cosets (parFlag σ J C (fun _ => 0)) (ratPts σ J) => (h ((q.out : ratPts σ J) * g) : ℝ) ^ t := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF L a hL hI h hh g t ht
  let _ : Submodule.IsFullLattice E L := hL
  obtain ⟨lv, hlv⟩ := GlobalTheory.T.exists_leviSection_isotropicFrame F E σ n J j m C D Z J₀ hF
  have hK : IsCompact (levelAll σ J L a : Set (GAd σ J)) := GlobalTheory.Doubling.isCompact_levelAll hF.cm J L a
  choose p β hp k hk e using fun q : GlobalTheory.Eis.Cosets (parFlag σ J C (fun _ => 0)) (ratPts σ J) =>
    hI ((q.out : ratPts σ J) * g)
  have h1 := GlobalTheory.T.summable_absDet_rational_points_godement F E σ n J j m C D Z J₀ hF lv hlv _
    (fun q : GlobalTheory.Eis.Cosets (parFlag σ J C (fun _ => 0)) (ratPts σ J) => (q.out : ratPts σ J)) p
    (fun q => k q * g⁻¹) β _ (hK.image (continuous_mul_const g⁻¹)) (fun q => q.out.2)
    (fun q => (eq_mul_inv_of_mul_eq (e q)).trans (mul_assoc _ _ _)) (fun q => ⟨k q, hk q, rfl⟩) hp
    (fun q q' hq => ?_) t (by
      have h2 : (m : ℝ) + 2 * j = n := by exact_mod_cast hF.dim
      push_cast
      linarith)
  · refine h1.congr fun q => ?_
    rw [e, hh _ _ (hp q) _ (hk q)]
  · rw [← q.out_eq, ← q'.out_eq]
    exact GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.2 ⟨⟨q'.out * q.out⁻¹, Subgroup.mem_subgroupOf.2 hq⟩, inv_mul_cancel_right _ _⟩

end GlobalTheory.SphEis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableHeightRpowParabolicCosetsStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_height_rpow_parabolicCosets : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)), Submodule.IsFullLattice E L → (∀ g : GAd σ J, ∃ (p : GAd σ J) (β : GL (Fin j) (AF F ⊗[F] E)), (matHom _ σ J p).1 * adMat F C = adMat F C * β.1 ∧ ∃ k ∈ levelAll σ J L a, g = p * k) → ∀ h : GAd σ J → ℝ≥0, (∀ (p : GAd σ J) (β : GL (Fin j) (AF F ⊗[F] E)), (matHom _ σ J p).1 * adMat F C = adMat F C * β.1 → ∀ k ∈ levelAll σ J L a, h (p * k) = absE F E (Matrix.GeneralLinearGroup.det β)) → ∀ (g : GAd σ J) (t : ℝ), (n : ℝ) - j < t → Summable fun q : GlobalTheory.Eis.Cosets (parFlag σ J C (fun _ => 0)) (ratPts σ J) => (h ((q.out : ratPts σ J) * g) : ℝ) ^ t := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF L a hL hI h hh g t ht
  let _ : Submodule.IsFullLattice E L := hL
  first
  | exact GlobalTheory.SphEis.summable_height_rpow F E σ n J j m C D Z J₀ hF L a hL hI h hh g t ht
  | exact GlobalTheory.SphEis.summable_height_rpow F E σ n J j m C D Z J₀ hF L a (inferInstance : Submodule.IsLattice E L) hI h hh g t ht
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GodementSummableHeightRpowRepresentatives
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ResidueEisenstein

theorem summable_height_rpow_reps : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), DataJ σ J X Y L a h → ∀ T, IsRepsJ σ J X T → ∀ (g : GAd σ J) (e : ℝ), ((n : ℝ) - (r + 1)) < e → Summable fun t : T => h (t.1.1 * g) ^ e := by
  intro F E _ _ _ _ _ σ n J r X Y L a h hD T hT g e he
  obtain ⟨m, Z, J₀, hFr⟩ := GlobalTheory.SphEis.exists_fr_of_isotropic F E σ hD.cm n J hD.herm (r + 1) X Y hD.witt.xx hD.witt.yy hD.witt.xy
  have hinv := (GlobalTheory.T.isotropicEisensteinSeries_rationalPoints_permute_terms F E σ n J r X Y L a h hD T hT).2.2.1
  have hnn : ∀ x, 0 ≤ h x := by
    intro x
    obtain ⟨p, β, hp, k, hk, rfl⟩ := hD.iwa x
    rw [hD.ht p β hp k hk]
    exact NNReal.coe_nonneg _
  have hS := GlobalTheory.T.summable_height_rpow_parabolicCosets F E σ n J (r + 1) m X Y Z J₀ hFr L a hD.lat hD.iwa (fun x => Real.toNNReal (h x))
    (fun p β hp k hk => by simp only [hD.ht p β hp k hk, Real.toNNReal_coe]) g e (by push_cast; linarith)
  have hXinv : adMat F (Formalism.UG.cT (σ : E →+* E) Y * J) * adMat F X = 1 := by
    simp only [adMat, ← Matrix.map_mul, hFr.dc, Matrix.map_one _ (map_zero _) (map_one _)]
  have hsc : ∀ p ∈ GlobalTheory.UAut.parFlag σ J X (fun _ => 0), ∃ β : GL (Fin (r + 1)) (AF F ⊗[F] E), ScalesBy σ J X p β := by
    intro p hp
    obtain ⟨⟨B, -, hB⟩, B', -, hB'⟩ := hp
    have hX : adMat F X = adMat F X * (B * B') := by
      calc adMat F X = (matHom _ σ J p).1 * ((matHom _ σ J p⁻¹).1 * adMat F X) := by
            rw [← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mul]
        _ = adMat F X * (B * B') := by rw [hB', ← Matrix.mul_assoc, hB, Matrix.mul_assoc]
    have h1 : B * B' = 1 := by
      calc B * B' = adMat F (Formalism.UG.cT (σ : E →+* E) Y * J) * adMat F X * (B * B') := by rw [hXinv, Matrix.one_mul]
        _ = 1 := by rw [Matrix.mul_assoc, ← hX, hXinv]
    have h2 : B' * B = 1 := by
      first | exact mul_eq_one_comm.mp h1 | exact Matrix.mul_eq_one_comm.mp h1 | exact (Matrix.mul_eq_one_comm).1 h1 | exact Matrix.nonsing_inv_mul_cancel_left _ _ h1
    exact ⟨⟨B, B', h1, h2⟩, hB⟩
  let φ : T → GlobalTheory.Eis.Cosets (GlobalTheory.UAut.parFlag σ J X (fun _ => 0)) (ratPts σ J) := fun t =>
    GlobalTheory.AutomorphicL2Unitary.mk _ t.1
  have hrel : ∀ t : T, ∃ γ : ((GlobalTheory.UAut.parFlag σ J X (fun _ => 0)).subgroupOf (ratPts σ J)),
      (γ : ratPts σ J) * (φ t).out = t.1 :=
    fun t => GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.1 (Quotient.out_eq (φ t))
  have hinj : Function.Injective φ := by
    intro t t' htt
    obtain ⟨γ, hγ⟩ := GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.1 htt
    have hγP : ((γ : ratPts σ J) : GAd σ J) ∈ GlobalTheory.UAut.parFlag σ J X (fun _ => 0) := Subgroup.mem_subgroupOf.1 γ.2
    obtain ⟨β, hβ⟩ := hsc _ hγP
    refine Subtype.ext ((hT t'.1).unique ⟨t.2, β, ?_⟩ ⟨t'.2, 1, ?_⟩)
    · rw [← eq_mul_inv_of_mul_eq hγ]; exact hβ
    · simp [ScalesBy]
  refine (hS.comp_injective hinj).congr fun t => ?_
  obtain ⟨γ, hγ⟩ := hrel t
  have hγP : ((γ⁻¹ : ratPts σ J) : GAd σ J) ∈ GlobalTheory.UAut.parFlag σ J X (fun _ => 0) :=
    Subgroup.mem_subgroupOf.1 (inv_mem γ.2)
  obtain ⟨β, hβ⟩ := hsc _ hγP
  have hout : ((φ t).out : ratPts σ J) = γ⁻¹ * t.1 := eq_inv_mul_of_mul_eq hγ
  simp only [Function.comp, Real.coe_toNNReal _ (hnn _)]
  rw [hout, Subgroup.coe_mul, mul_assoc]
  refine congrArg (· ^ e) (hinv _ ⟨?_, β, Subgroup.mem_top _, ?_⟩ _)
  · exact SetLike.coe_mem _
  · exact hβ

end GlobalTheory.ResidueEisenstein
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GodementSummableHeightRpowRepresentativesStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.godement_summable_height_rpow_representatives : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), DataJ σ J X Y L a h → ∀ T, IsRepsJ σ J X T → ∀ (g : GAd σ J) (e : ℝ), ((n : ℝ) - (r + 1)) < e → Summable fun t : T => h (t.1.1 * g) ^ e := by
  first | exact @GlobalTheory.ResidueEisenstein.summable_height_rpow_reps | exact GlobalTheory.ResidueEisenstein.summable_height_rpow_reps | (intros; apply GlobalTheory.ResidueEisenstein.summable_height_rpow_reps <;> assumption)
end
