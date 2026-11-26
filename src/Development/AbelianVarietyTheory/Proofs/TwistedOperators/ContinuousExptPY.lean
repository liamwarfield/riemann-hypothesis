module

public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
noncomputable section
namespace GlobalTheory.PolarU
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Matrix

variable {p q : ℕ}

def vecM (V : Mat p q) : Ix p q × Ix p q → ℂ := fun ab => V ab.1 ab.2

def sAd (Y V : Mat p q) : Mat p q := Matrix.of fun a b => (sinhcAd Y *ᵥ vecM V) (a, b)

def pY (B : Fin p → Fin q → ℂ) : Mat p q := pOf (Matrix.of B)

theorem pY_add (B C : Fin p → Fin q → ℂ) : pY (B + C) = pY B + pY C := by
  ext (i | i) (j | j) <;> simp [pY, pOf]

theorem pY_smul (t : ℝ) (B : Fin p → Fin q → ℂ) : pY (t • B) = t • pY B := by
  ext (i | i) (j | j) <;> simp [pY, pOf, Complex.real_smul, mul_comm]

theorem continuous_pY : Continuous (pY : (Fin p → Fin q → ℂ) → Mat p q) := by
  show Continuous fun B : Fin p → Fin q → ℂ => Matrix.fromBlocks 0 (Matrix.of B) (Matrix.of B)ᴴ 0
  refine continuous_pi fun a => continuous_pi fun b => ?_
  rcases a with a | a <;> rcases b with b | b <;> simp <;> fun_prop

theorem sAd_add (Y V W : Mat p q) : sAd Y (V + W) = sAd Y V + sAd Y W := by
  have h : vecM (V + W) = vecM V + vecM W := rfl
  ext a b
  simp [sAd, h, Matrix.mulVec_add]

theorem sAd_smul_real (Y V : Mat p q) (t : ℝ) : sAd Y (t • V) = t • sAd Y V := by
  have h : vecM (t • V) = (t : ℂ) • vecM V := by
    funext ab
    simp [vecM, Complex.real_smul]
  ext a b
  simp [sAd, h, Matrix.mulVec_smul, Complex.real_smul]

def sP (Y : Mat p q) : (Fin p → Fin q → ℂ) →ₗ[ℝ] (Fin p → Fin q → ℂ) where
  toFun B := fun i j => sAd Y (pY B) (Sum.inl i) (Sum.inr j)
  map_add' B C := by funext i j; simp [pY_add, sAd_add]
  map_smul' t B := by funext i j; simp [pY_smul, sAd_smul_real]

theorem adMat_mulVec (Y V : Mat p q) : adMat Y *ᵥ vecM V = vecM (Y * V - V * Y) := by
  funext ⟨a, b⟩
  have h1 : (Matrix.kroneckerMap (· * ·) Y (1 : Mat p q) *ᵥ vecM V) (a, b) = (Y * V) a b := by
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply, Matrix.mul_apply,
      vecM, mul_ite, ite_mul]
  have h2 : (Matrix.kroneckerMap (· * ·) (1 : Mat p q) Yᵀ *ᵥ vecM V) (a, b) = (V * Y) a b := by
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type_right, Matrix.one_apply, Matrix.mul_apply,
      vecM, mul_ite, mul_comm]
  simp only [adMat, Matrix.sub_mulVec, Pi.sub_apply, h1, h2, vecM, Matrix.sub_apply]

theorem pY_conjTranspose (B : Fin p → Fin q → ℂ) : (pY B)ᴴ = pY B := by
  simp [pY, pOf, Matrix.fromBlocks_conjTranspose]

theorem pY_mem (B : Fin p → Fin q → ℂ) : pY B ∈ pR p q := by
  show pY B ∈ upq p q ∧ IsPC (pY B)
  refine ⟨?_, ?_⟩
  · show (pY B)ᴴ * Jm p q + Jm p q * pY B = 0
    rw [pY_conjTranspose]
    simp [pY, pOf, Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
  · intro a b h
    rcases a with a | a <;> rcases b with b | b <;> simp_all [pY, pOf, sameBlock]

theorem exists_pY {Y : Mat p q} (hY : Y ∈ pR p q) : ∃ B, Y = pY B := by
  have hY' : Y ∈ upq p q ∧ IsPC Y := hY
  obtain ⟨hu, hP⟩ := hY'
  have hu' : Yᴴ * Jm p q + Jm p q * Y = 0 := hu
  refine ⟨Y.toBlocks₁₂, ?_⟩
  ext (i | i) (j | j)
  · simpa [pY, pOf] using hP (Sum.inl i) (Sum.inl j) (by simp [sameBlock])
  · rfl
  · have h := congrFun (congrFun hu' (Sum.inr i)) (Sum.inl j)
    simp [Matrix.mul_apply, Jm, Formalism.UG.Jpq, Fintype.sum_sum_type, Matrix.one_apply, mul_ite,
      ite_mul] at h
    rw [starRingEnd_apply] at h
    show Y (Sum.inr i) (Sum.inl j) = star (Y (Sum.inl j) (Sum.inr i))
    linear_combination -h
  · simpa [pY, pOf] using hP (Sum.inr i) (Sum.inr j) (by simp [sameBlock])

def posIx : Ix p q → ℕ := Sum.elim (fun i => i.val) (fun j => j.val)

def cutH (p q : ℕ) (h : ℕ → ℝ) (n : ℕ) : ℝ := if n < min p q then h n else 0

def rootP (h : ℕ → ℝ) (ab : Ix p q × Ix p q) : ℝ :=
  if ab.1.isLeft then cutH p q h (posIx ab.1) - cutH p q h (posIx ab.2)
  else cutH p q h (posIx ab.1) + cutH p q h (posIx ab.2)

def eigP (ab cd : Ix p q × Ix p q) : ℂ :=
  if cd = ab then 1
  else if ¬ sameBlock cd.1 cd.2 ∧ posIx cd.1 = posIx ab.1 ∧ posIx cd.2 = posIx ab.2 then
    (if ab.1.isLeft then 1 else -1)
  else 0

theorem eigenvectorMatrix_eq_zero_of_sameBlock (ab : PIx p q) (cd : Ix p q × Ix p q) (h : sameBlock cd.1 cd.2) :
    eigP ab.1 cd = 0 := by
  have hne : cd ≠ ab.1 := by
    rintro rfl
    exact ab.2 h
  simp [eigP, hne, h]

def matG (T : GrpData p q) (x : T.G) : Mat p q := ((T.cov x : GL (Ix p q) ℂ) : Mat p q)

theorem matG_mul (T : GrpData p q) (x y : T.G) : matG T (x * y) = matG T x * matG T y := by
  simp only [matG, map_mul, Units.val_mul]

theorem matG_expt (T : GrpData p q) (B : Fin p → Fin q → ℂ) :
    matG T (T.expt (pY B)) = NormedSpace.exp (pY B) := by
  exact T.expt_cov (pY B) (show pY B ∈ upq p q ∧ IsPC (pY B) from pY_mem B).1

theorem continuous_expt_pY (T : GrpData p q) :
    Continuous fun B : Fin p → Fin q → ℂ => T.expt (pY B) := by
  exact T.expt_cont.comp_continuous continuous_pY
    (fun B => (show pY B ∈ upq p q ∧ IsPC (pY B) from pY_mem B).1)

theorem continuous_matG (T : GrpData p q) : Continuous (matG T) := by
  show Continuous fun x => ((T.cov x : GL (Ix p q) ℂ) : Mat p q)
  exact Units.continuous_val.comp (continuous_fst.comp T.emb.continuous)

theorem matG_J (T : GrpData p q) (x : T.G) : (matG T x)ᴴ * Jm p q * matG T x = Jm p q := by
  have h : Formalism.UG.cT (starRingEnd ℂ) (matG T x) * Formalism.UG.Jpq p q * matG T x = Formalism.UG.Jpq p q :=
    T.cov_mem x
  have hc : Formalism.UG.cT (starRingEnd ℂ) (matG T x) = (matG T x)ᴴ := by
    ext i j
    simp [Formalism.UG.cT]
  rw [hc] at h
  exact h

theorem matG_one (T : GrpData p q) : matG T 1 = 1 := by
  simp [matG]

theorem matG_inv (T : GrpData p q) (x : T.G) :
    matG T x⁻¹ = (((T.cov x)⁻¹ : GL (Ix p q) ℂ) : Mat p q) := by
  simp only [matG, map_inv]

theorem exists_blocks (T : GrpData p q) {k : T.G} (hk : k ∈ T.Kset) :
    ∃ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ∃ V ∈ Matrix.unitaryGroup (Fin q) ℂ,
      matG T k = Matrix.fromBlocks U 0 0 V := by
  have hK : IsKC (matG T k) := hk
  have h12 : (matG T k).toBlocks₁₂ = 0 := by
    ext i j
    exact hK (Sum.inl i) (Sum.inr j) (by simp [sameBlock])
  have h21 : (matG T k).toBlocks₂₁ = 0 := by
    ext i j
    exact hK (Sum.inr i) (Sum.inl j) (by simp [sameBlock])
  have hMe : matG T k = Matrix.fromBlocks (matG T k).toBlocks₁₁ 0 0 (matG T k).toBlocks₂₂ := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks (matG T k)]
    rw [h12, h21]
  have hJ := matG_J T k
  rw [hMe] at hJ
  generalize (matG T k).toBlocks₁₁ = A at hJ hMe
  generalize (matG T k).toBlocks₂₂ = D at hJ hMe
  simp only [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply] at hJ
  simp [Matrix.fromBlocks_inj] at hJ
  obtain ⟨hA, hD⟩ := hJ
  refine ⟨A, ?_, D, ?_, hMe⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    exact hA
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    exact hD

theorem matG_star_mul (T : GrpData p q) {k : T.G} (hk : k ∈ T.Kset) :
    (matG T k)ᴴ * matG T k = 1 := by
  obtain ⟨U, hU, V, hV, h⟩ := exists_blocks T hk
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hU hV
  rw [h, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  simp [hU, hV]

theorem matG_inv_of_mem (T : GrpData p q) {k : T.G} (hk : k ∈ T.Kset) :
    matG T k⁻¹ = (matG T k)ᴴ := by
  rw [matG_inv]
  exact Units.inv_eq_of_mul_eq_one_left (matG_star_mul T hk)

def Ksub (T : GrpData p q) : Subgroup T.G where
  carrier := T.Kset
  one_mem' := by
    show IsKC (matG T 1)
    rw [matG_one]; intro a b h
    have : a ≠ b := by rintro rfl; cases a <;> simp [sameBlock] at h
    simp [Matrix.one_apply, this]
  mul_mem' := by
    intro x y hx hy
    obtain ⟨U, -, V, -, h⟩ := exists_blocks T hx
    obtain ⟨U', -, V', -, h'⟩ := exists_blocks T hy
    show IsKC (matG T (x * y))
    rw [matG_mul, h, h', Matrix.fromBlocks_multiply]
    intro a b hab
    cases a <;> cases b <;> simp_all [sameBlock]
  inv_mem' := by
    intro x hx
    show IsKC (matG T x⁻¹)
    rw [matG_inv_of_mem T hx]
    have hx' : IsKC (matG T x) := hx
    intro a b hab
    have : ¬ sameBlock b a := by cases a <;> cases b <;> simp_all [sameBlock]
    simp [hx' b a this]

end GlobalTheory.PolarU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryQuotient
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryQuotient
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

noncomputable section

namespace GlobalTheory.GKQuot

variable {p q : ℕ}

def quotAct (M : GKMod p q) (N : Submodule ℂ M.V) (hN : ∀ Z, N ≤ N.comap (M.act Z)) :
    Mat p q →ₗ[ℂ] Module.End ℂ (M.V ⧸ N) where
  toFun Z := N.mapQ N (M.act Z) (hN Z)
  map_add' Z W := by
    apply Submodule.linearMap_qext
    ext x
    simp
  map_smul' c Z := by
    apply Submodule.linearMap_qext
    ext x
    simp

theorem quotAct_mk (M : GKMod p q) (N : Submodule ℂ M.V) (hN : ∀ Z, N ≤ N.comap (M.act Z))
    (Z : Mat p q) (x : M.V) : quotAct M N hN Z (N.mkQ x) = N.mkQ (M.act Z x) := rfl

def quotMod (M : GKMod p q) (N : Submodule ℂ M.V) (hN : ∀ Z, N ≤ N.comap (M.act Z)) :
    GKMod p q where
  V := M.V ⧸ N
  act := quotAct M N hN
  lie X Y := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨x, rfl⟩ := N.mkQ_surjective v
    rw [quotAct_mk, M.lie X Y]
    simp only [LinearMap.sub_apply, Module.End.mul_apply, quotAct_mk, map_sub]
  kfin v := by
    obtain ⟨x, rfl⟩ := N.mkQ_surjective v
    obtain ⟨W, hW, hx, hK⟩ := M.kfin x
    refine ⟨W.map N.mkQ, inferInstance, Submodule.mem_map_of_mem hx, ?_⟩
    rintro X hX _ ⟨w, hw, rfl⟩
    rw [quotAct_mk]
    exact Submodule.mem_map_of_mem (hK X hX w hw)
  wts v := by
    obtain ⟨x, rfl⟩ := N.mkQ_surjective v
    have h : (⨆ μ : Ix p q → ℚ, wtSub M.act μ) ≤
        (⨆ μ : Ix p q → ℚ, wtSub (quotAct M N hN) μ).comap N.mkQ := by
      refine iSup_le fun μ y hy => ?_
      rw [Submodule.mem_comap]
      refine Submodule.mem_iSup_of_mem μ ?_
      simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_apply] at hy ⊢
      intro a
      rw [quotAct_mk, ← map_smul, ← map_sub, hy a, map_zero]
    exact h (M.wts x)

theorem exists_unitary_quotient (p q : ℕ) (M : GKMod p q) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (E : M.V →ₗ[ℂ] H)
    (hE : ∀ Z x y, inner ℂ (E (M.act Z x)) (E y) = inner ℂ (E x) (E (M.act (adjZ Z) y))) :
    ∃ (A : UGKMod p q) (f : M.V →ₗ[ℂ] A.M.V) (Eb : A.M.V →ₗ[ℂ] H), Function.Surjective f ∧
      Function.Injective Eb ∧ (∀ x, Eb (f x) = E x) ∧ ∀ Z x, f (M.act Z x) = A.M.act Z (f x) := by

  let N : Submodule ℂ M.V := LinearMap.ker E
  have hN : ∀ Z, N ≤ N.comap (M.act Z) := by
    intro Z x hx
    have hx' : E x = 0 := hx
    show E (M.act Z x) = 0
    have h := hE Z x (M.act Z x)
    rw [hx', inner_zero_left] at h
    exact inner_self_eq_zero.mp h

  let Eb : M.V ⧸ N →ₗ[ℂ] H := N.liftQ E le_rfl
  have hEb : ∀ x, Eb (N.mkQ x) = E x := fun x => N.liftQ_apply E x
  have hinj : Function.Injective Eb := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro v hv
    obtain ⟨x, rfl⟩ := N.mkQ_surjective v
    rw [LinearMap.mem_ker, hEb] at hv
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_ker.mpr hv
  have hact : ∀ Z x, quotAct M N hN Z (N.mkQ x) = N.mkQ (M.act Z x) := quotAct_mk M N hN

  let ip : M.V ⧸ N →ₗ⋆[ℂ] M.V ⧸ N →ₗ[ℂ] ℂ := ((innerₛₗ ℂ).comp Eb).compl₂ Eb
  let A : UGKMod p q :=
    { M := quotMod M N hN
      ip := ip
      herm := by
        intro v w
        show star (inner ℂ (Eb v) (Eb w)) = inner ℂ (Eb w) (Eb v)
        exact inner_conj_symm (Eb w) (Eb v)
      pos := by
        intro v hv
        have hne : Eb v ≠ 0 := fun h0 => hv (hinj (h0.trans (map_zero Eb).symm))
        have h : 0 < RCLike.re (inner ℂ (Eb v) (Eb v)) := by
          rw [inner_self_eq_norm_sq]
          exact pow_pos (norm_pos_iff.mpr hne) 2
        show 0 < (inner ℂ (Eb v) (Eb v)).re
        exact h
      adj := by
        intro Z v w
        obtain ⟨x, rfl⟩ := N.mkQ_surjective v
        obtain ⟨y, rfl⟩ := N.mkQ_surjective w
        show inner ℂ (Eb (quotAct M N hN Z (N.mkQ x))) (Eb (N.mkQ y)) =
          inner ℂ (Eb (N.mkQ x)) (Eb (quotAct M N hN (adjZ Z) (N.mkQ y)))
        rw [hact, hact, hEb, hEb, hEb, hEb]
        exact hE Z x y }
  exact ⟨A, N.mkQ, Eb, N.mkQ_surjective, hinj, hEb, fun Z x => (hact Z x).symm⟩

end GlobalTheory.GKQuot
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryQuotientStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_module_quotient_of_invariant_inner : ∀ (p q : ℕ) (M : GKMod p q) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (E : M.V →ₗ[ℂ] H), (∀ Z x y, inner ℂ (E (M.act Z x)) (E y) = inner ℂ (E x) (E (M.act (adjZ Z) y))) → ∃ (A : UGKMod p q) (f : M.V →ₗ[ℂ] A.M.V) (Eb : A.M.V →ₗ[ℂ] H), Function.Surjective f ∧ Function.Injective Eb ∧ (∀ x, Eb (f x) = E x) ∧ ∀ Z x, f (M.act Z x) = A.M.act Z (f x) := by
  first | exact @GlobalTheory.GKQuot.exists_unitary_quotient | exact GlobalTheory.GKQuot.exists_unitary_quotient | (intros; apply GlobalTheory.GKQuot.exists_unitary_quotient <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfFactorialBound
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfFactorialBound
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory.FactorialJet

open Set Filter Topology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_le_right (g : ℕ → ℝ → E) (C ρ t0 : ℝ)
    (hd : ∀ k t, HasDerivAt (g k) (g (k + 1) t) t)
    (hb : ∀ k t, ‖g k t‖ ≤ C * ρ ^ k * (k.factorial : ℝ)) (h0 : ∀ k, g k t0 = 0) (n : ℕ) :
    ∀ k t, t0 ≤ t →
      ‖g k t‖ ≤ C * ρ ^ (k + n) * ((k + n).factorial : ℝ) * ((t - t0) ^ n / (n.factorial : ℝ)) := by
  induction n with
  | zero => intro k t _; simpa using hb k t
  | succ n ih =>
    intro k t ht
    set A : ℝ := C * ρ ^ (k + (n + 1)) * ((k + (n + 1)).factorial : ℝ) with hA
    have hB : ∀ x : ℝ, HasDerivAt (fun s : ℝ => A * ((s - t0) ^ (n + 1) / ((n + 1).factorial : ℝ)))
        (A * ((x - t0) ^ n / (n.factorial : ℝ))) x := by
      intro x
      have h1 : HasDerivAt (fun s : ℝ => (s - t0) ^ (n + 1)) (((n + 1 : ℕ) : ℝ) * (x - t0) ^ n * 1) x := by
        exact ((hasDerivAt_id x).sub_const t0).pow (n + 1)
      have h2 := (h1.div_const ((n + 1).factorial : ℝ)).const_mul A
      refine h2.congr_deriv ?_
      congr 1
      rw [Nat.factorial_succ]
      have : (n.factorial : ℝ) ≠ 0 := by positivity
      have : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      push_cast at *
      field_simp
    have := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := g k) (f' := g (k + 1))
      (a := t0) (b := t) (fun x _ => (hd k x).continuousAt.continuousWithinAt)
      (fun x _ => (hd k x).hasDerivWithinAt) (by simp [h0 k]) hB
      (fun x hx => by
        have h := ih (k + 1) x hx.1
        have e : k + 1 + n = k + (n + 1) := by ring
        rwa [e] at h) (x := t) ⟨ht, le_rfl⟩
    exact this

theorem eq_zero_near_right (g : ℕ → ℝ → E) (C ρ t0 : ℝ) (hρ : 0 < ρ)
    (hd : ∀ k t, HasDerivAt (g k) (g (k + 1) t) t)
    (hb : ∀ k t, ‖g k t‖ ≤ C * ρ ^ k * (k.factorial : ℝ)) (h0 : ∀ k, g k t0 = 0)
    (k : ℕ) (t : ℝ) (ht : t0 ≤ t) (ht' : ρ * (t - t0) < 1) : g k t = 0 := by
  have hr : ‖ρ * (t - t0)‖ < 1 := by
    rw [Real.norm_of_nonneg (mul_nonneg hρ.le (sub_nonneg.2 ht))]; exact ht'
  have hs := (summable_choose_mul_geometric_of_norm_lt_one k hr).tendsto_atTop_zero
  have hs2 := hs.const_mul (C * ρ ^ k * (k.factorial : ℝ))
  rw [mul_zero] at hs2
  have hle : ‖g k t‖ ≤ 0 := by
    refine ge_of_tendsto' hs2 fun n => ?_
    have h := norm_le_right g C ρ t0 hd hb h0 n k t ht
    refine h.trans (le_of_eq ?_)
    have e : ((k + n).factorial : ℝ) = ((n + k).choose k : ℝ) * n.factorial * k.factorial := by
      rw [add_comm k n]; exact_mod_cast (Nat.add_choose_mul_factorial_mul_factorial n k).symm
    have : (n.factorial : ℝ) ≠ 0 := by positivity
    rw [e, mul_pow, pow_add]
    field_simp
  exact norm_le_zero_iff.1 hle

theorem eq_zero_right (g : ℕ → ℝ → E) (C ρ : ℝ) (hρ : 0 < ρ)
    (hd : ∀ k t, HasDerivAt (g k) (g (k + 1) t) t)
    (hb : ∀ k t, ‖g k t‖ ≤ C * ρ ^ k * (k.factorial : ℝ)) (h0 : ∀ k, g k 0 = 0)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) : g k t = 0 := by
  have key : ∀ m : ℕ, ∀ k (t : ℝ), 0 ≤ t → 2 * ρ * t ≤ m → g k t = 0 := by
    intro m
    induction m with
    | zero =>
      intro k t ht h
      have : t = 0 := by
        have : t ≤ 0 := by
          by_contra hc
          push_neg at hc
          have := mul_pos hρ hc
          simp at h
          nlinarith
        linarith
      rw [this, h0]
    | succ m ih =>
      intro k t ht h
      by_cases hm : 2 * ρ * t ≤ m
      · exact ih k t ht hm
      · push_neg at hm
        have e : 2 * ρ * ((m : ℝ) / (2 * ρ)) = m := by field_simp
        have h1 : (m : ℝ) / (2 * ρ) ≤ t := by
          rw [div_le_iff₀ (by positivity)]; linarith
        refine eq_zero_near_right g C ρ ((m : ℝ) / (2 * ρ)) hρ hd hb
          (fun j => ih j _ (by positivity) e.le) k t h1 ?_
        push_cast at h
        linarith
  exact key ⌈2 * ρ * t⌉₊ k t ht (Nat.le_ceil _)

theorem eq_zero_of_factorial_bound :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℕ → ℝ → E) (C ρ : ℝ), 0 ≤ C → 0 < ρ → (∀ k t, HasDerivAt (g k) (g (k + 1) t) t) → (∀ k t, ‖g k t‖ ≤ C * ρ ^ k * (k.factorial : ℝ)) → (∀ k, g k 0 = 0) → ∀ k t, g k t = 0 := by
  intro E _ _ g C ρ _ hρ hd hb h0 k t
  rcases le_total 0 t with ht | ht
  · exact eq_zero_right g C ρ hρ hd hb h0 k t ht
  · have h := eq_zero_right (fun j s => ((-1 : ℝ) ^ j) • g j (-s)) C ρ hρ
      (fun j s => by
        have h1 := ((hd j (-s)).scomp s (hasDerivAt_neg s)).const_smul ((-1 : ℝ) ^ j)
        refine h1.congr_deriv ?_
        rw [smul_smul, pow_succ])
      (fun j s => by simpa [norm_smul] using hb j (-s))
      (fun j => by simp [h0 j]) k (-t) (by linarith)
    simpa using h

end GlobalTheory.FactorialJet
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfFactorialBoundStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_factorial_bound_of_vanish_at_zero : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℕ → ℝ → E) (C ρ : ℝ), 0 ≤ C → 0 < ρ → (∀ k t, HasDerivAt (g k) (g (k + 1) t) t) → (∀ k t, ‖g k t‖ ≤ C * ρ ^ k * (k.factorial : ℝ)) → (∀ k, g k 0 = 0) → ∀ k t, g k t = 0 := by
  first | exact @GlobalTheory.FactorialJet.eq_zero_of_factorial_bound | exact GlobalTheory.FactorialJet.eq_zero_of_factorial_bound | (intros; apply GlobalTheory.FactorialJet.eq_zero_of_factorial_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTensorEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTensorEmbedding
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory.FockTensor

theorem ext_orbit {p q : ℕ} {T : GrpData p q} (D : DSRep T) (u : D.U.H) (hu : u ≠ 0)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (A B : D.U.H →L[ℂ] E)
    (h : ∀ g, A (D.U.π g u) = B (D.U.π g u)) : A = B := by
  let S : Submodule ℂ D.U.H :=
    { carrier := {x | ∀ g, A (D.U.π g x) = B (D.U.π g x)}
      add_mem' := by
        intro a b ha hb g
        simp only [map_add (f := _)]
        rw [ha g, hb g]
      zero_mem' := by intro g; simp
      smul_mem' := by
        intro c a ha g
        simp only [map_smul]
        rw [ha g] }
  have hcl : IsClosed (S : Set D.U.H) := by
    have : (S : Set D.U.H) = ⋂ g, {x | A (D.U.π g x) = B (D.U.π g x)} := by
      ext x; simp only [Set.mem_iInter]; rfl
    rw [this]
    exact isClosed_iInter fun g => isClosed_eq (by fun_prop) (by fun_prop)
  have hinv : ∀ g, ∀ x ∈ S, D.U.π g x ∈ S := by
    intro g x hx g'
    have := hx (g' * g)
    rw [map_mul] at this
    exact this
  rcases D.irred S hcl hinv with h0 | h1
  · have : u ∈ S := h
    rw [h0] at this
    exact absurd ((Submodule.mem_bot ℂ).1 this) hu
  · ext x
    have hx : x ∈ S := by rw [h1]; trivial
    have := hx 1
    rw [map_one] at this
    exact this

theorem isHomG_ext {p q : ℕ} {T : GrpData p q} (D : DSRep T) (πU : URep T) (u : D.U.H)
    (hu : u ≠ 0) (A B : D.U.H →L[ℂ] πU.H) (hA : ∀ g x, A (D.U.π g x) = πU.π g (A x))
    (hB : ∀ g x, B (D.U.π g x) = πU.π g (B x)) (h : A u = B u) : A = B :=
  ext_orbit D u hu A B fun g => by rw [hA, hB, h]

theorem exists_tensor_embedding :
    ∀ (p q : ℕ) (T : GrpData p q) (D : DSRep T) (πU : URep T) (v : D.HK.V), ‖D.ι v‖ = 1 → ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] (j : K →ₗᵢ[ℂ] πU.H), (∀ g y y', inner ℂ (j y) (πU.π g (j y')) = mcoef D v g * inner ℂ y y') → (∀ y, ∃ io : D.U.H →L[ℂ] πU.H, IsHomG D πU io ∧ io (D.ι v) = j y) → ∃ Tm : D.U.H →L[ℂ] K →L[ℂ] πU.H, (∀ x x' y y', inner ℂ (Tm x y) (Tm x' y') = inner ℂ x x' * inner ℂ y y') ∧ (∀ y, Tm (D.ι v) y = j y) ∧ (∀ g x y, πU.π g (Tm x y) = Tm (D.U.π g x) y) ∧ ∀ (R : πU.H →L[ℂ] πU.H) (S : K →L[ℂ] K), (∀ g z, R (πU.π g z) = πU.π g (R z)) → (∀ y, R (j y) = j (S y)) → ∀ x y, R (Tm x y) = Tm x (S y) := by
  intro p q T D πU v hv K _ _ j hj hex
  choose io hio hiov using hex
  have hu : D.ι v ≠ 0 := by
    intro h; rw [h, norm_zero] at hv; exact zero_ne_one hv
  have hG : ∀ y g x, io y (D.U.π g x) = πU.π g (io y x) := fun y g x =>
    congrArg (fun f : D.U.H →L[ℂ] πU.H => f x) (hio y g)
  have key1 : ∀ y y' x', inner ℂ (j y) (io y' x') = inner ℂ (D.ι v) x' * inner ℂ y y' := by
    intro y y' x'
    have := ext_orbit D (D.ι v) hu ((innerSL ℂ (j y)).comp (io y'))
      ((inner ℂ y y' : ℂ) • innerSL ℂ (D.ι v)) (fun g => by
        show inner ℂ (j y) (io y' (D.U.π g (D.ι v))) =
          inner ℂ y y' * inner ℂ (D.ι v) (D.U.π g (D.ι v))
        rw [hG, hiov, hj, mcoef, mul_comm])
    have h2 := congrArg (fun f : D.U.H →L[ℂ] ℂ => f x') this
    rw [mul_comm]
    exact h2
  have key2 : ∀ y y' g x', inner ℂ (io y (D.U.π g (D.ι v))) (io y' x') =
      inner ℂ (D.U.π g (D.ι v)) x' * inner ℂ y y' := by
    intro y y' g x'
    rw [hG, hiov, inner_pi_left, ← hG, key1, inner_pi_left]
  have key : ∀ x x' y y', inner ℂ (io y x) (io y' x') = inner ℂ x x' * inner ℂ y y' := by
    intro x x' y y'
    have := ext_orbit D (D.ι v) hu ((innerSL ℂ (io y x)).comp (io y'))
      ((inner ℂ y y' : ℂ) • innerSL ℂ x) (fun g => by
        show inner ℂ (io y x) (io y' (D.U.π g (D.ι v))) =
          inner ℂ y y' * inner ℂ x (D.U.π g (D.ι v))
        rw [← inner_conj_symm, key2, map_mul, inner_conj_symm, inner_conj_symm, mul_comm])
    have h2 := congrArg (fun f : D.U.H →L[ℂ] ℂ => f x') this
    rw [mul_comm]
    exact h2
  have hnorm : ∀ x y, ‖io y x‖ ≤ 1 * ‖x‖ * ‖y‖ := by
    intro x y
    have h := key x x y y
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
    have h' : ‖io y x‖ ^ 2 = (‖x‖ * ‖y‖) ^ 2 := by
      rw [mul_pow]; exact_mod_cast h
    have := (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h'
    rw [this, one_mul]
  have hadd : ∀ y y', io (y + y') = io y + io y' := fun y y' =>
    isHomG_ext D πU _ hu _ _ (hG _) (fun g x => by
      show io y (D.U.π g x) + io y' (D.U.π g x) = πU.π g (io y x + io y' x)
      rw [hG, hG, map_add (f := _)]) (by
      show io (y + y') (D.ι v) = io y (D.ι v) + io y' (D.ι v)
      rw [hiov, hiov, hiov, map_add (f := _)])
  have hsmul : ∀ (c : ℂ) y, io (c • y) = c • io y := fun c y =>
    isHomG_ext D πU _ hu _ _ (hG _) (fun g x => by
      show c • io y (D.U.π g x) = πU.π g (c • io y x)
      rw [hG, map_smul]) (by
      show io (c • y) (D.ι v) = c • io y (D.ι v)
      rw [hiov, hiov, map_smul])
  let L : D.U.H →ₗ[ℂ] K →ₗ[ℂ] πU.H := LinearMap.mk₂ ℂ (fun x y => io y x)
    (fun a b y => map_add _ _ _) (fun c a y => map_smul _ _ _)
    (fun x a b => by rw [hadd]; rfl) (fun c x a => by rw [hsmul]; rfl)
  refine ⟨LinearMap.mkContinuous₂ L 1 hnorm, key, hiov, fun g x y => (hG y g x).symm, ?_⟩
  intro R S hR hS x y
  have := isHomG_ext D πU _ hu (R.comp (io y)) (io (S y)) (fun g x => by
      show R (io y (D.U.π g x)) = πU.π g (R (io y x))
      rw [hG, hR]) (hG _) (by
      show R (io y (D.ι v)) = _
      rw [hiov, hiov, hS])
  exact congrArg (fun f : D.U.H →L[ℂ] πU.H => f x) this

end GlobalTheory.FockTensor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTensorEmbeddingStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isometric_tensor_embedding_intertwining : ∀ (p q : ℕ) (T : GrpData p q) (D : DSRep T) (πU : URep T) (v : D.HK.V), ‖D.ι v‖ = 1 → ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] (j : K →ₗᵢ[ℂ] πU.H), (∀ g y y', inner ℂ (j y) (πU.π g (j y')) = mcoef D v g * inner ℂ y y') → (∀ y, ∃ io : D.U.H →L[ℂ] πU.H, IsHomG D πU io ∧ io (D.ι v) = j y) → ∃ Tm : D.U.H →L[ℂ] K →L[ℂ] πU.H, (∀ x x' y y', inner ℂ (Tm x y) (Tm x' y') = inner ℂ x x' * inner ℂ y y') ∧ (∀ y, Tm (D.ι v) y = j y) ∧ (∀ g x y, πU.π g (Tm x y) = Tm (D.U.π g x) y) ∧ ∀ (R : πU.H →L[ℂ] πU.H) (S : K →L[ℂ] K), (∀ g z, R (πU.π g z) = πU.π g (R z)) → (∀ y, R (j y) = j (S y)) → ∀ x y, R (Tm x y) = Tm x (S y) := by
  first | exact @GlobalTheory.FockTensor.exists_tensor_embedding | exact GlobalTheory.FockTensor.exists_tensor_embedding | (intros; apply GlobalTheory.FockTensor.exists_tensor_embedding <;> assumption)
end
end
