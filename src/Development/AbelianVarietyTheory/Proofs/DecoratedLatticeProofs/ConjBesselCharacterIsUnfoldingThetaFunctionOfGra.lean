module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelCentralTermsViaGramMatrices
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBorelSphericalFunction

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransvectionIsUnitaryAdelic
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransvectionIsUnitaryAdelic
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.TransvAdelic

theorem transv_unitary : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.TransvUnitary D :=
  fun D => (transv_unitary_conj D).1

end GlobalTheory.TransvAdelic
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransvectionIsUnitaryAdelicStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transvection_isUnitaryAdelic : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.TransvUnitary D := by
  first | exact @GlobalTheory.TransvAdelic.transv_unitary | exact GlobalTheory.TransvAdelic.transv_unitary | (intros; apply GlobalTheory.TransvAdelic.transv_unitary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTransvectionFixingFirstVectorsSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTransvectionFixingFirstVectorsSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TransvMid

open GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction

variable {D : D7}

theorem form_mulVec (S : HSp D) {n : ℕ} (y : VA S) (M : Mx D S.rank n) (c : Fin n → AE D) :
    form S y (M *ᵥ c) = (fun k => cA D (c k)) ⬝ᵥ ((adj M ⬝ gA S) *ᵥ y) := by
  have h : (fun i => cA D ((M *ᵥ c) i)) = M.map (cA D) *ᵥ fun k => cA D (c k) := by
    funext i; exact RingHom.map_mulVec (cA D) M c i
  rw [form, h, ← Matrix.mulVec_mulVec]
  conv_rhs => rw [Matrix.dotProduct_mulVec, adj, Matrix.vecMul_transpose]

theorem mul_apply_col {m n k : ℕ} (g : Mx D m n) (M : Mx D n k) (r : Fin m) (c : Fin k) :
    (g ⬝ M) r c = (g *ᵥ (M *ᵥ Pi.single c 1)) r := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one]; rfl

theorem col_apply {m n : ℕ} (M : Mx D m n) (c : Fin n) (r : Fin m) : (M *ᵥ Pi.single c 1) r = M r c := by
  rw [Matrix.mulVec_single_one]; rfl

theorem submatrix_col {m n : ℕ} (M : Mx D m n) (i : Fin n) (c : Fin 1) :
    (M.submatrix id fun _ : Fin 1 => i) *ᵥ Pi.single c 1 = M *ᵥ Pi.single i 1 := by
  funext r; rw [col_apply, col_apply]; rfl

theorem smul_vecMulVec_single {ρ : ℕ} (s : AE D) (x : Fin ρ → AE D) (J k : Fin ρ) :
    (s • vecMulVec x (Pi.single J 1)) *ᵥ Pi.single k 1 = (s * (Pi.single k 1 : Fin ρ → AE D) J) • x := by
  funext l
  rw [col_apply]
  by_cases hk : k = J
  · subst hk; simp [Matrix.vecMulVec_apply]
  · simp [Matrix.vecMulVec_apply, Pi.single_eq_of_ne hk, Pi.single_eq_of_ne' hk]

theorem upSum_smul_vecMulVec {ρ : ℕ} (s : AE D) (x : Fin ρ → AE D) (j J : Fin ρ) (hJ : J.1 = j.1 + 1) :
    GlobalTheory.MixPer.upSum (s • vecMulVec x (Pi.single J 1)) = s * x j := by
  have hTe : ∀ i k : Fin ρ, (if k.1 = i.1 + 1 then (s • vecMulVec x (Pi.single J 1)) i k else 0) =
      if i = j then (if k = J then s * x j else 0) else 0 := by
    intro i k
    by_cases hk : k = J
    · subst hk
      by_cases hi : i = j
      · subst hi
        simp [hJ, Matrix.vecMulVec_apply, mul_comm]
      · have : ¬ (k.1 = i.1 + 1) := fun h => hi (Fin.ext (by omega))
        simp [hi, this]
    · simp [hk, Matrix.vecMulVec_apply]
  rw [GlobalTheory.MixPer.upSum]
  simp only [hTe]
  simp

section Mid

variable {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ)

theorem form_jY_single (y : VA V) (J : Fin ρ) (s : AE D) :
    form V y (d.jY *ᵥ Pi.single J (cA D s)) = s * (d.pX *ᵥ y) J := by
  have h : (fun k => cA D ((Pi.single J (cA D s) : Fin ρ → AE D) k)) = (Pi.single J s : Fin ρ → AE D) := by
    funext k
    by_cases hk : k = J
    · subst hk; simp [cA_cA]
    · simp [Pi.single_apply, hk]
  rw [form_mulVec, h, ← d.pX_eq, single_dotProduct]

theorem form_jX (y : VA V) (b : Fin ρ → AE D) :
    form V y (d.jX *ᵥ b) = (fun k => cA D (b k)) ⬝ᵥ (d.pY *ᵥ y) := by
  rw [form_mulVec, ← d.pY_eq]

theorem transv_fix {w v : VA V} {u : GA D V} (hu : IsTransv V w v u) {y : VA V} (hv : form V y v = 0)
    (hw : form V y w = 0) : mt V u *ᵥ y = y := by
  have := hu y
  rw [act, transv, hv, hw] at this
  rw [this]; simp

theorem pX_jX_single (k : Fin ρ) : d.pX *ᵥ (d.jX *ᵥ Pi.single k 1) = Pi.single k 1 := by
  rw [Matrix.mulVec_mulVec, d.pX_jX, Matrix.one_mulVec]

theorem pY_jX_vec (x : Fin ρ → AE D) : d.pY *ᵥ (d.jX *ᵥ x) = 0 := by
  rw [Matrix.mulVec_mulVec, d.pY_jX, Matrix.zero_mulVec]

theorem isotropicProjection_anisotropic_vec_eq_zero (x : Fin V₀.rank → AE D) : d.pX *ᵥ (d.j0 *ᵥ x) = 0 := by
  rw [Matrix.mulVec_mulVec, d.pX_j0, Matrix.zero_mulVec]

theorem dualProjection_anisotropic_vec_eq_zero (x : Fin V₀.rank → AE D) : d.pY *ᵥ (d.j0 *ᵥ x) = 0 := by
  rw [Matrix.mulVec_mulVec, d.pY_j0, Matrix.zero_mulVec]

theorem transv_apply {w v : VA V} {u : GA D V} (hu : IsTransv V w v u) (y : VA V) :
    mt V u *ᵥ y = transv V w v y := hu y

variable {w v : VA V} {u : GA D V} {J : Fin ρ} {s : AE D} {c : Fin ρ → AE D}

theorem mem_fixer_of_ne (hu : IsTransv V w v u) (fv : ∀ y : VA V, form V y v = s * (d.pX *ᵥ y) J)
    (fw : ∀ y : VA V, form V y w = c ⬝ᵥ (d.pY *ᵥ y)) {i : Fin ρ} (hiJ : i ≠ J) :
    u ∈ GlobalTheory.MixPer.fixer V (d.jX.submatrix id fun _ : Fin 1 => i) := by
  rw [GlobalTheory.MixPer.mem_fixer]
  ext r k
  rw [mul_apply_col, submatrix_col, transv_fix hu, col_apply]
  · rfl
  · rw [fv, pX_jX_single d, Pi.single_eq_of_ne' hiJ, mul_zero]
  · rw [fw, pY_jX_vec d, dotProduct_zero]

theorem transv_jX (hu : IsTransv V w v u) (fv : ∀ y : VA V, form V y v = s * (d.pX *ᵥ y) J)
    (fw : ∀ y : VA V, form V y w = c ⬝ᵥ (d.pY *ᵥ y)) {x : Fin ρ → AE D} (hw : w = d.jX *ᵥ x) :
    mt V u ⬝ d.jX = d.jX + d.jX ⬝ (s • vecMulVec x (Pi.single J 1)) := by
  ext r k
  rw [mul_apply_col, transv_apply hu, transv, fv, fw, pX_jX_single d, pY_jX_vec d]
  simp only [dotProduct_zero, mul_zero, zero_smul, sub_zero]
  rw [Matrix.add_apply, mul_apply_col, smul_vecMulVec_single, Matrix.mulVec_smul, ← hw]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, col_apply]

theorem unitaryTransvection_on_anisotropic_part (hu : IsTransv V w v u) (fv : ∀ y : VA V, form V y v = s * (d.pX *ᵥ y) J)
    (fw : ∀ y : VA V, form V y w = c ⬝ᵥ (d.pY *ᵥ y)) : mt V u ⬝ d.j0 = d.j0 + d.jX ⬝ (0 : Mx D ρ V₀.rank) := by
  rw [Matrix.mul_zero, add_zero]
  ext r k
  rw [mul_apply_col, transv_fix hu, col_apply]
  · rw [fv, isotropicProjection_anisotropic_vec_eq_zero d, Pi.zero_apply, mul_zero]
  · rw [fw, dualProjection_anisotropic_vec_eq_zero d, dotProduct_zero]

end Mid

end GlobalTheory.TransvMid


open GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction in
theorem GlobalTheory.TransvMid.exists_mid : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (z : Fin V₀.rank → D.host.E) (j : Fin ρ) (a : Fin ρ → D.host.E), a j = 1 → (∀ i, j < i → a i = 0) → j.1 + 1 < ρ → ∀ s : AE D, ∃ v : GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.VA V, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v = 0 ∧ (∀ i k : Fin ρ, k ≤ i → GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (Pi.single k 1)) v * GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a i = 0) ∧ ∀ u : GA D V, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.IsTransv V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v u → (∀ i : {i : Fin ρ // i ≤ j}, u ∈ fixer V (d.jX.submatrix id fun _ : Fin 1 => i.1)) ∧ simpleSum d z u = s := by
  intro D V V₀ ρ d z j a haj hai hj s
  set J : Fin ρ := ⟨j.1 + 1, hj⟩ with hJ
  have hjJ : j < J := by rw [Fin.lt_def]; simp [hJ]
  have haJ : ratVec a J = 0 := by simp [ratVec, hai J hjJ]
  have hw : vecX d (ratVec a) = d.jX *ᵥ ratVec a := rfl
  refine ⟨d.jY *ᵥ Pi.single J (cA D s), ?_, ?_, ?_⟩
  · rw [GlobalTheory.TransvMid.form_jY_single, hw, Matrix.mulVec_mulVec, d.pX_jX, Matrix.one_mulVec, haJ, mul_zero]
  · intro i k hki
    rw [GlobalTheory.TransvMid.form_jY_single, vecX, Matrix.mulVec_mulVec, d.pX_jX, Matrix.one_mulVec]
    by_cases hk : k = J
    · subst hk
      have : ratVec a i = 0 := by simp [ratVec, hai i (lt_of_lt_of_le hjJ hki)]
      rw [this, mul_zero]
    · rw [Pi.single_eq_of_ne' hk, mul_zero, zero_mul]
  · intro u hu
    have fv : ∀ y : VA V, form V y (d.jY *ᵥ Pi.single J (cA D s)) = s * (d.pX *ᵥ y) J :=
      fun y => GlobalTheory.TransvMid.form_jY_single d y J s
    have fw : ∀ y : VA V, form V y (vecX d (ratVec a)) = (fun k => cA D (ratVec a k)) ⬝ᵥ (d.pY *ᵥ y) :=
      fun y => GlobalTheory.TransvMid.form_jX d y _
    generalize d.jY *ᵥ Pi.single J (cA D s) = v at hu fv
    generalize hwv : vecX d (ratVec a) = w at hu fw
    rw [vecX] at hwv
    refine ⟨fun i => GlobalTheory.TransvMid.mem_fixer_of_ne d hu fv fw (ne_of_lt (lt_of_le_of_lt i.2 hjJ)), ?_⟩
    rw [GlobalTheory.MixPer.simpleSum_eq d z (GlobalTheory.TransvMid.transv_jX d hu fv fw hwv.symm)
      (GlobalTheory.TransvMid.unitaryTransvection_on_anisotropic_part d hu fv fw), GlobalTheory.MixPer.superSum_const]
    simp only [Matrix.zero_mulVec, dotProduct_zero, add_zero, one_mul]
    rw [GlobalTheory.TransvMid.upSum_smul_vecMulVec s _ j J rfl]
    simp [ratVec, haj]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTransvectionFixingFirstVectorsSumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_transvection_fixing_first_vectors_sum : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (z : Fin V₀.rank → D.host.E) (j : Fin ρ) (a : Fin ρ → D.host.E), a j = 1 → (∀ i, j < i → a i = 0) → j.1 + 1 < ρ → ∀ s : AE D, ∃ v : GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.VA V, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v = 0 ∧ (∀ i k : Fin ρ, k ≤ i → GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (Pi.single k 1)) v * GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a i = 0) ∧ ∀ u : GA D V, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.IsTransv V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v u → (∀ i : {i : Fin ρ // i ≤ j}, u ∈ fixer V (d.jX.submatrix id fun _ : Fin 1 => i.1)) ∧ simpleSum d z u = s := by
  exact GlobalTheory.TransvMid.exists_mid
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTransvectionFixingIsotropicLastSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTransvectionFixingIsotropicLastSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.TransvLast

open GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction

variable {D : D7}

theorem form_mulVec (S : HSp D) {k l : ℕ} (M : Mx D S.rank k) (N : Mx D S.rank l) (x : Fin k → AE D)
    (y : Fin l → AE D) :
    form S (M *ᵥ x) (N *ᵥ y) = (fun i => cA D (y i)) ⬝ᵥ ((adj N * (gA S * M)) *ᵥ x) := by
  have h : (fun i => cA D ((N *ᵥ y) i)) = N.map (cA D) *ᵥ (fun i => cA D (y i)) :=
    funext fun i => RingHom.map_mulVec (cA D) N y i
  rw [form, h, ← Matrix.vecMul_transpose (N.map (cA D)), ← Matrix.dotProduct_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec]
  rfl

theorem conj_smul {n : ℕ} (c : AE D) (y : Fin n → AE D) :
    (fun i => cA D ((c • y) i)) = cA D c • fun i => cA D (y i) := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]

theorem conj_ratV {n : ℕ} (z : Fin n → D.host.E) : (fun i => cA D (ratV z i)) = ratV (star z) :=
  funext fun i => GlobalTheory.DualPairCheck.cA_incA (z i)

theorem ratV_dotProduct {n : ℕ} (x y : Fin n → D.host.E) : ratV x ⬝ᵥ ratV y = incA D (x ⬝ᵥ y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, map_sum, map_mul]
  rfl

theorem incA_inv_mul {x : D.host.E} (hx : x ≠ 0) : incA D x⁻¹ * incA D x = 1 := by
  rw [← map_mul, inv_mul_cancel₀ hx, map_one]

section Lemmas

variable {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ)

theorem hermSpaceAdelicForm_isotropic_anisotropic_zero (b : Fin ρ → AE D) (y : Fin V₀.rank → AE D) : form V (vecX d b) (d.j0 *ᵥ y) = 0 := by
  rw [vecX, form_mulVec, d.gram_0X, Matrix.zero_mulVec, dotProduct_zero]

theorem form_vecX_vecX (b b' : Fin ρ → AE D) : form V (vecX d b) (vecX d b') = 0 := by
  rw [vecX, vecX, form_mulVec, d.gram_XX, Matrix.zero_mulVec, dotProduct_zero]

theorem hermSpaceAdelicForm_anisotropic_isotropic_zero (y : Fin V₀.rank → AE D) (b : Fin ρ → AE D) : form V (d.j0 *ᵥ y) (vecX d b) = 0 := by
  rw [vecX, form_mulVec, d.wittDecomp_gram_X_anisotropic, Matrix.zero_mulVec, dotProduct_zero]

theorem hermSpaceAdelicForm_anisotropic_rational_smul (z : Fin V₀.rank → D.host.E) (c : AE D) :
    form V (d.j0 *ᵥ ratV z) (d.j0 *ᵥ (c • ratV z)) = cA D c * incA D (star z ⬝ᵥ V₀.gram *ᵥ z) := by
  rw [form_mulVec, d.gram_00, conj_smul, smul_dotProduct, conj_ratV, gA, ← GlobalTheory.MixPer.ratV_mulVec, ratV_dotProduct,
    smul_eq_mul]

theorem mt_jX_of_isTransv {w v : VA V} {u : GA D V} (hu : IsTransv V w v u)
    (hw : ∀ b, form V (vecX d b) w = 0) (hv : ∀ b, form V (vecX d b) v = 0) : mt V u * d.jX = d.jX := by
  refine Matrix.ext_of_mulVec_single fun i => ?_
  have h : act V u (vecX d (Pi.single i 1)) = transv V w v (vecX d (Pi.single i 1)) := hu _
  rw [transv, hv, hw, zero_smul, zero_smul, mul_zero, zero_smul, add_zero, sub_zero, sub_zero] at h
  rw [← Matrix.mulVec_mulVec]
  exact h

theorem mt_of_isTransv {S : HSp D} {w v y : VA S} {u : GA D S} (hu : IsTransv S w v u) (hy : form S y w = 0) :
    mt S u *ᵥ y = y + form S y v • w := by
  have h : act S u y = transv S w v y := hu _
  rw [transv, hy, zero_smul, mul_zero, zero_smul, sub_zero, sub_zero] at h
  exact h

theorem simpleSum_of {z : Fin V₀.rank → D.host.E} {u : GA D V} {c : Fin ρ → AE D} (s : AE D)
    (hX : mt V u * d.jX = d.jX) (hy : mt V u *ᵥ (d.j0 *ᵥ ratV z) = d.j0 *ᵥ ratV z + s • (d.jX *ᵥ c)) :
    simpleSum d z u = s * (ell D ρ ⬝ᵥ c) := by
  rw [simpleSum, blockX, hX, d.pX_jX, upSum_one, zero_add, coefX, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    hy, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, d.pX_j0,
    d.pX_jX, Matrix.zero_mulVec, Matrix.one_mulVec, zero_add, dotProduct_smul, smul_eq_mul]

theorem mem_fixer_column {u : GA D V} (hX : mt V u * d.jX = d.jX) (i : Fin ρ) :
    u ∈ fixer V (d.jX.submatrix id fun _ : Fin 1 => i) := by
  rw [mem_fixer]
  ext k l
  have h := congrFun (congrFun hX k) i
  rw [Matrix.mul_apply] at h
  simpa only [Matrix.mul_apply, Matrix.submatrix_apply, id] using h

theorem ell_dotProduct_last {j : Fin ρ} (hj : j.1 + 1 = ρ) {a : Fin ρ → D.host.E} (haj : a j = 1) :
    ell D ρ ⬝ᵥ ratVec a = 1 := by
  rw [dotProduct, Finset.sum_eq_single j]
  · simp [ell, hj, ratVec, haj]
  · intro i _ hij
    have : ¬ (i.1 + 1 = ρ) := fun h => hij (Fin.ext (Nat.add_right_cancel (h.trans hj.symm)))
    simp [ell, this]
  · intro h
    exact absurd (Finset.mem_univ j) h

end Lemmas

theorem exists_transv_simpleSum_last : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (z : Fin V₀.rank → D.host.E), star z ⬝ᵥ V₀.gram *ᵥ z ≠ 0 → ∀ (j : Fin ρ) (a : Fin ρ → D.host.E), a j = 1 → (∀ i, j < i → a i = 0) → j.1 + 1 = ρ → ∀ s : AE D, ∃ v : GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.VA V, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v = 0 ∧ (∀ i k : Fin ρ, k ≤ i → GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (Pi.single k 1)) v * GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a i = 0) ∧ ∀ u : GA D V, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.IsTransv V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v u → (∀ i : {i : Fin ρ // i ≤ j}, u ∈ fixer V (d.jX.submatrix id fun _ : Fin 1 => i.1)) ∧ simpleSum d z u = s := by
  intro D V V₀ ρ d z hz j a haj _ hj s
  refine ⟨d.j0 *ᵥ (cA D (s * incA D (star z ⬝ᵥ V₀.gram *ᵥ z)⁻¹) • ratV z), hermSpaceAdelicForm_isotropic_anisotropic_zero d _ _,
    fun i k _ => by rw [hermSpaceAdelicForm_isotropic_anisotropic_zero, zero_mul], fun u hu => ?_⟩
  have hX := mt_jX_of_isTransv d hu (fun b => form_vecX_vecX d b _) (fun b => hermSpaceAdelicForm_isotropic_anisotropic_zero d b _)
  have hy := mt_of_isTransv hu (hermSpaceAdelicForm_anisotropic_isotropic_zero d (ratV z) (ratVec a))
  rw [hermSpaceAdelicForm_anisotropic_rational_smul, cA_cA, mul_assoc, incA_inv_mul hz, mul_one] at hy
  exact ⟨fun i => mem_fixer_column d hX i.1, (simpleSum_of d s hX hy).trans (by rw [ell_dotProduct_last hj haj, mul_one])⟩

end GlobalTheory.TransvLast

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTransvectionFixingIsotropicLastSumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_transvection_fixing_isotropic_last_sum : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (z : Fin V₀.rank → D.host.E), star z ⬝ᵥ V₀.gram *ᵥ z ≠ 0 → ∀ (j : Fin ρ) (a : Fin ρ → D.host.E), a j = 1 → (∀ i, j < i → a i = 0) → j.1 + 1 = ρ → ∀ s : AE D, ∃ v : GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.VA V, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v = 0 ∧ (∀ i k : Fin ρ, k ≤ i → GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (Pi.single k 1)) v * GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a i = 0) ∧ ∀ u : GA D V, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.IsTransv V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v u → (∀ i : {i : Fin ρ // i ≤ j}, u ∈ fixer V (d.jX.submatrix id fun _ : Fin 1 => i.1)) ∧ simpleSum d z u = s := by
  first | exact @GlobalTheory.TransvLast.exists_transv_simpleSum_last | exact GlobalTheory.TransvLast.exists_transv_simpleSum_last | (intros; apply GlobalTheory.TransvLast.exists_transv_simpleSum_last <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransvectionStrictUpperMemFlagUnipotentRadical
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransvectionStrictUpperMemFlagUnipotentRadical
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.TransvFlag

open GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction

theorem form_vecX {D : D7} {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (b : Fin ρ → AE D) (y : VA V) :
    form V y (vecX d b) = (fun i => cA D (b i)) ⬝ᵥ (d.pY *ᵥ y) := by
  have h1 : (fun i => cA D (vecX d b i)) = (d.jX.map (cA D)) *ᵥ (fun i => cA D (b i)) := by
    funext i
    exact RingHom.map_mulVec (cA D) d.jX b i
  rw [form, h1, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec]
  have hp : d.pY = adj d.jX * gA V := by
    rw [HypDec.pY, HypDec.qY, HypDec.jX, gA, ← rat_conjTranspose]
    exact Matrix.map_mul
  conv_rhs => rw [hp, ← Matrix.mulVec_mulVec]
  rfl

theorem mul_eq_of_cols {R : Type} [CommRing R] {n ρ : ℕ} (M : Matrix (Fin n) (Fin n) R) (E : Matrix (Fin n) (Fin ρ) R)
    (T : Matrix (Fin ρ) (Fin ρ) R)
    (h : ∀ k, M *ᵥ (E *ᵥ Pi.single k 1) = E *ᵥ Pi.single k 1 + E *ᵥ (fun i => T i k)) : M * E = E + E * T := by
  refine Matrix.ext_of_mulVec_single fun k => ?_
  rw [← Matrix.mulVec_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_single_one T k, h k]
  rfl

theorem transv_mem_flagN : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (b : Fin ρ → AE D)
    (v : GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.VA V),
    (∀ i k : Fin ρ, k ≤ i → GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (Pi.single k 1)) v * b i = 0) →
    ∀ u : GA D V, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.IsTransv V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d b) v u → u ∈ flagN d := by
  intro D V V₀ ρ d b v hb u hu
  unfold flagN
  rw [GlobalTheory.BesselChar.mem_NFlag_iff V d.e (isIsoSub_e d).1]
  have hperp : ∀ y : VA V, d.pY *ᵥ y = 0 → act V u y = y + d.jX *ᵥ (form V y v • b) := by
    intro y hy
    rw [hu y, transv, form_vecX, hy, dotProduct_zero, zero_smul, sub_zero, mul_zero, zero_smul, sub_zero,
      Matrix.mulVec_smul]
    rfl
  refine ⟨⟨Matrix.of fun i k => form V (vecX d (Pi.single k 1)) v * b i, fun j i hij => hb j i hij, ?_⟩,
    fun y hy => ⟨form V y v • b, hperp y hy⟩⟩
  have e1 : d.e.map (incA D) = d.jX := rfl
  rw [e1]
  refine mul_eq_of_cols _ _ _ fun k => ?_
  have hp : d.pY * d.jX = 0 := by
    have h := congrArg rat d.ee
    rw [rat_zero] at h
    rw [HypDec.pY, HypDec.qY, HypDec.jX]
    simpa only [rat, Matrix.map_mul] using h
  have hk : d.pY *ᵥ vecX d (Pi.single k 1) = 0 := by
    rw [vecX, Matrix.mulVec_mulVec, hp, Matrix.zero_mulVec]
  exact hperp _ hk

end GlobalTheory.TransvFlag
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransvectionStrictUpperMemFlagUnipotentRadicalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transvection_strictUpper_mem_flagUnipotentRadical : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (b : Fin ρ → AE D) (v : GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.VA V), (∀ i k : Fin ρ, k ≤ i → GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (Pi.single k 1)) v * b i = 0) → ∀ u : GA D V, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.IsTransv V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d b) v u → u ∈ flagN d := by
  first | exact @GlobalTheory.TransvFlag.transv_mem_flagN | exact GlobalTheory.TransvFlag.transv_mem_flagN | (intros; apply GlobalTheory.TransvFlag.transv_mem_flagN <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjBesselCharacterIsUnfoldingThetaFunctionOfGra
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf.CutChar

theorem exists_psiE_ne_one : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∃ s : AE D, psiE ψ s ≠ 1 := by
  intro D ψ hψ
  obtain ⟨x₀, hx₀⟩ := hψ.1.2.2.2
  set q : D.host.F := Algebra.trace D.host.F D.host.E 1 with hq
  have hq0 : q ≠ 0 := by
    rw [hq, ← map_one (algebraMap D.host.F D.host.E), Algebra.trace_algebraMap, nsmul_eq_mul, mul_one]
    exact_mod_cast (Module.finrank_pos (R := D.host.F) (M := D.host.E)).ne'
  refine ⟨(x₀ * algebraMap D.host.F (AF D.host.F) q⁻¹) • incA D 1, ?_⟩
  rw [psiE, map_smul, GlobalTheory.BesselChar.trace_incA, ← hq, smul_eq_mul, mul_assoc, ← map_mul,
    inv_mul_cancel₀ hq0, map_one, mul_one]
  exact hx₀

theorem vecB_norm_ne : ∀ (D : D7) (V₀ A L : HSp D) (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → star (vecB o ζ) ⬝ᵥ V₀.gram *ᵥ vecB o ζ ≠ 0 := by
  intro D V₀ A L o ζ hζ
  rw [vecB, Matrix.star_mulVec, ← dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, o.isoB]
  exact hζ.2

theorem psi_qS_eq_one : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (W : HSp D) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E), gramQ W x₀ = 0 → ∀ c : skewA D ρ, ψ (d.qS W c (rat x₀)) = 1 := by
  intro D ψ hψ V V₀ ρ d W x₀ hx₀ c
  have hg : adj (rat x₀) * (gA W * rat x₀) = 0 := by
    have h : x₀ᴴ * HSpace.gram W * x₀ = 0 := by rw [Matrix.mul_assoc]; exact hx₀
    rw [gram_rat W h, rat_zero]
  have hq := ((GlobalTheory.T.mixedModelCentralTerms_via_gramMatrices D).1 V V₀ W ρ d).2.1 c (rat x₀)
  have h0 : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew W (rat x₀) = 0 := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew, hg, Matrix.transpose_zero, smul_zero]
  rw [HypDec.qS, hq, h0]
  simp

theorem conjBessel_isTh : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ : ℕ) (B : BesLev D ρ) (W : HSp D) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E), gramQ W x₀ = 0 → IsTh ψ B.d W x₀ fun n => star (psiBes ψ B.d 1 (vecB B.o B.ζ) n) := by
  intro D ψ hψ ρ B W x₀ hx₀
  have hC := GlobalTheory.T.flag_unipotent_bessel_character_laws D ψ hψ.1 B.V B.V₀ B.A B.L ρ B.d B.o B.ζ 1
  set z := vecB B.o B.ζ with hz
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact continuous_star.comp ((hC.1 z).comp continuous_subtype_val)
  · intro γ hγ hγN n hn
    rw [psiBes_mul B.d ψ 1 z hγN hn, hC.2.1 z γ hγ, one_mul]
  · intro c n hn
    rw [psiBes_mul B.d ψ 1 z (B.d.nC_mem_NFlag c) hn, psiBes_nC, one_mul,
      psi_qS_eq_one D ψ hψ B.V B.V₀ ρ B.d W x₀ hx₀ c, star_one, one_mul]
  · intro j a haj hai _
    obtain ⟨s, hs⟩ := exists_psiE_ne_one D ψ hψ
    have key : ∃ v : GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.VA B.V, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form B.V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX B.d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v = 0 ∧ (∀ i k : Fin ρ, k ≤ i → GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form B.V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX B.d (Pi.single k 1)) v * GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a i = 0) ∧ ∀ u : GA D B.V, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.IsTransv B.V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX B.d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v u → (∀ i : {i : Fin ρ // i ≤ j}, u ∈ fixer B.V (B.d.jX.submatrix id fun _ : Fin 1 => i.1)) ∧ simpleSum B.d z u = s := by
      rcases lt_or_eq_of_le (Nat.succ_le_of_lt j.2) with h | h
      · exact GlobalTheory.T.exists_transvection_fixing_first_vectors_sum D B.V B.V₀ ρ B.d z j a haj hai h s
      · exact GlobalTheory.T.exists_transvection_fixing_isotropic_last_sum D B.V B.V₀ ρ B.d z (vecB_norm_ne D B.V₀ B.A B.L B.o B.ζ B.line) j a haj hai h s
    obtain ⟨v, hv0, hvT, hv⟩ := key
    obtain ⟨u, hu⟩ := GlobalTheory.T.transvection_isUnitaryAdelic D B.V B.V₀ ρ B.d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a) v hv0
    obtain ⟨hfix, hus⟩ := hv u hu
    have huN : u ∈ Nfix B.d j :=
      ⟨GlobalTheory.T.transvection_strictUpper_mem_flagUnipotentRadical D B.V B.V₀ ρ B.d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a) v hvT u hu, Subgroup.mem_iInf.2 hfix⟩
    have hval : psiBes ψ B.d 1 z u = psiE ψ s := by
      rw [psiBes, hus, map_one, one_mul]
    refine ⟨v, u, star (psiE ψ s), hv0, hu, huN, ?_, ?_⟩
    · intro h1
      apply hs
      have := congrArg star h1
      rwa [star_star, star_one] at this
    · intro n hn n' hn'
      have huF : u ∈ flagN B.d := huN.1
      rw [psiBes_mul B.d ψ 1 z (mul_mem hn huF) hn', psiBes_mul B.d ψ 1 z hn huF, hval,
        psiBes_mul B.d ψ 1 z hn hn']
      simp only [star_mul']
      ring

end GlobalTheory.Unf.CutChar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjBesselCharacterIsUnfoldingThetaFunctionOfGraStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjBesselCharacter_isUnfoldingThetaFunction_of_gram_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ : ℕ) (B : BesLev D ρ) (W : HSp D) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E), gramQ W x₀ = 0 → IsTh ψ B.d W x₀ fun n => star (psiBes ψ B.d 1 (vecB B.o B.ζ) n) := by
  first | exact @GlobalTheory.Unf.CutChar.conjBessel_isTh | exact GlobalTheory.Unf.CutChar.conjBessel_isTh | (intros; apply GlobalTheory.Unf.CutChar.conjBessel_isTh <;> assumption)
end
