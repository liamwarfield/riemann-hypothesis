module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.ToMatrixLin
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.NCIface
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ModTop

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.IsClosedAsub
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.LeviInfUnipotentEqOne
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.LevLSubPerp
noncomputable section

namespace PI.LevelKSplit.W.NCL

open PI.VolSemiDirect.W.PG

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}

def pV (D : Dat A n r) : (n → A) →ₗ[A] (n → A) := LinearMap.id - D.pX - D.pXv

private theorem hL_apply_lemma (D : Dat A n r) (x y : n → A) : D.hL x y = D.h x y := rfl

private theorem pX_apply_lemma_2 (D : Dat A n r) (x : n → A) :
    D.pX x = ∑ a, D.h (D.f a) x • D.e a := by
  simp only [Dat.pX, LinearMap.sum_apply, LinearMap.smulRight_apply, hL_apply_lemma]

private theorem pXv_apply_lemma_3 (D : Dat A n r) (x : n → A) :
    D.pXv x = ∑ a, D.h (D.e a) x • D.f a := by
  simp only [Dat.pXv, LinearMap.sum_apply, LinearMap.smulRight_apply, hL_apply_lemma]

private theorem h_add_lemma_4 (D : Dat A n r) (v x y : n → A) : D.h v (x + y) = D.h v x + D.h v y :=
  map_add (D.hL v) x y

private theorem h_sub_lemma_5 (D : Dat A n r) (v x y : n → A) : D.h v (x - y) = D.h v x - D.h v y :=
  map_sub (D.hL v) x y

private theorem h_sum_lemma_6 (D : Dat A n r) (v : n → A) (t : Fin r → A) (w : Fin r → n → A) :
    D.h v (∑ a, t a • w a) = ∑ a, t a * D.h v (w a) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hL_apply_lemma, map_sum]
  simp only [map_smul, smul_eq_mul, hL_apply_lemma]

private theorem h_swap_lemma_7 (D : Dat A n r) (H : D.Hyp) (x y : n → A) :
    D.h y x = D.σA (D.h x y) := by
  show (∑ i, ∑ j, D.σA (y i) * D.JA i j * x j) = D.σA (∑ i, ∑ j, D.σA (x i) * D.JA i j * y j)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, H.σσ, H.herm]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private theorem h_fe_lemma_8 (D : Dat A n r) (H : D.Hyp) (a b : Fin r) :
    D.h (D.f a) (D.e b) = if b = a then 1 else 0 := by
  rw [h_swap_lemma_7 D H, H.ef]
  split_ifs <;> simp

private theorem h_add_left_lemma_9 (D : Dat A n r) (H : D.Hyp) (x x' y : n → A) :
    D.h (x + x') y = D.h x y + D.h x' y := by
  rw [h_swap_lemma_7 D H, h_add_lemma_4, map_add (f := _), ← h_swap_lemma_7 D H, ← h_swap_lemma_7 D H]

private theorem h_sum_left_lemma_10 (D : Dat A n r) (H : D.Hyp) (t : Fin r → A) (w : Fin r → n → A)
    (y : n → A) : D.h (∑ a, t a • w a) y = ∑ a, D.σA (t a) * D.h (w a) y := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h_swap_lemma_7 D H, h_sum_lemma_6, map_sum]
  simp only [map_mul, ← h_swap_lemma_7 D H]

theorem pV_apply (D : Dat A n r) (x : n → A) : pV D x = x - D.pX x - D.pXv x := rfl

theorem decomp (D : Dat A n r) (x : n → A) : x = pV D x + D.pX x + D.pXv x := by
  rw [pV_apply]
  abel

def levL (D : Dat A n r) (U W : Matrix (Fin r) (Fin r) A) : (n → A) →ₗ[A] (n → A) :=
  pV D + ∑ a, ∑ b, U a b • (D.hL (D.f b)).smulRight (D.e a) +
    ∑ d, ∑ b, W d b • (D.hL (D.e b)).smulRight (D.f d)

theorem levL_apply (D : Dat A n r) (U W : Matrix (Fin r) (Fin r) A) (x : n → A) :
    levL D U W x = pV D x + ∑ a, (∑ b, U a b * D.h (D.f b) x) • D.e a +
      ∑ d, (∑ b, W d b * D.h (D.e b) x) • D.f d := by
  simp only [levL, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply, hL_apply_lemma, Finset.sum_smul, smul_smul]

variable {D : Dat A n r}

section Hyp

variable (H : D.Hyp)
include H

theorem h_f_pX (c : Fin r) (x : n → A) : D.h (D.f c) (D.pX x) = D.h (D.f c) x := by
  rw [pX_apply_lemma_2, h_sum_lemma_6]
  simp [h_fe_lemma_8 D H]

theorem h_f_pXv (c : Fin r) (x : n → A) : D.h (D.f c) (D.pXv x) = 0 := by
  rw [pXv_apply_lemma_3, h_sum_lemma_6]
  simp [H.ff]

theorem h_e_pX' (c : Fin r) (x : n → A) : D.h (D.e c) (D.pX x) = 0 := by
  rw [pX_apply_lemma_2, h_sum_lemma_6]
  simp [H.ee]

theorem h_e_pXv (c : Fin r) (x : n → A) : D.h (D.e c) (D.pXv x) = D.h (D.e c) x := by
  rw [pXv_apply_lemma_3, h_sum_lemma_6]
  simp [H.ef]

theorem h_f_pV (c : Fin r) (x : n → A) : D.h (D.f c) (pV D x) = 0 := by
  rw [pV_apply, h_sub_lemma_5, h_sub_lemma_5, h_f_pX H, h_f_pXv H]
  ring

theorem h_e_pV (c : Fin r) (x : n → A) : D.h (D.e c) (pV D x) = 0 := by
  rw [pV_apply, h_sub_lemma_5, h_sub_lemma_5, h_e_pX' H, h_e_pXv H]
  ring

theorem h_f_levL (U W : Matrix (Fin r) (Fin r) A) (c : Fin r) (x : n → A) :
    D.h (D.f c) (levL D U W x) = ∑ b, U c b * D.h (D.f b) x := by
  rw [levL_apply, h_add_lemma_4, h_add_lemma_4, h_f_pV H, h_sum_lemma_6, h_sum_lemma_6]
  simp [h_fe_lemma_8 D H, H.ff]

theorem h_e_levL (U W : Matrix (Fin r) (Fin r) A) (c : Fin r) (x : n → A) :
    D.h (D.e c) (levL D U W x) = ∑ b, W c b * D.h (D.e b) x := by
  rw [levL_apply, h_add_lemma_4, h_add_lemma_4, h_e_pV H, h_sum_lemma_6, h_sum_lemma_6]
  simp [H.ee, H.ef]

theorem pV_levL (U W : Matrix (Fin r) (Fin r) A) (x : n → A) :
    pV D (levL D U W x) = pV D x := by
  rw [pV_apply, pX_apply_lemma_2, pXv_apply_lemma_3]
  simp only [h_f_levL H, h_e_levL H]
  rw [levL_apply]
  abel

theorem ext_coord {y y' : n → A} (h1 : pV D y = pV D y')
    (h2 : ∀ c, D.h (D.f c) y = D.h (D.f c) y') (h3 : ∀ c, D.h (D.e c) y = D.h (D.e c) y') :
    y = y' := by
  rw [decomp D y, decomp D y', h1, pX_apply_lemma_2, pX_apply_lemma_2, pXv_apply_lemma_3, pXv_apply_lemma_3]
  simp only [h2, h3]

theorem levL_comp (U W U' W' : Matrix (Fin r) (Fin r) A) (x : n → A) :
    levL D U W (levL D U' W' x) = levL D (U * U') (W * W') x := by
  apply ext_coord H
  · rw [pV_levL H, pV_levL H, pV_levL H]
  · intro c
    simp only [h_f_levL H, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  · intro c
    simp only [h_e_levL H, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm

theorem levL_one (x : n → A) : levL D 1 1 x = x := by
  apply ext_coord H
  · exact pV_levL H 1 1 x
  · intro c
    rw [h_f_levL H]
    simp [Matrix.one_apply]
  · intro c
    rw [h_e_levL H]
    simp [Matrix.one_apply]

theorem levL_e (U W : Matrix (Fin r) (Fin r) A) (b : Fin r) :
    levL D U W (D.e b) = ∑ a, U a b • D.e a := by
  rw [levL_apply, pV_apply, pX_apply_lemma_2, pXv_apply_lemma_3]
  simp [h_fe_lemma_8 D H, H.ee]

theorem levL_f (U W : Matrix (Fin r) (Fin r) A) (b : Fin r) :
    levL D U W (D.f b) = ∑ d, W d b • D.f d := by
  rw [levL_apply, pV_apply, pX_apply_lemma_2, pXv_apply_lemma_3]
  simp [H.ff, H.ef]

theorem levL_alt (U W : Matrix (Fin r) (Fin r) A) {w : n → A} (hf : ∀ b, D.h (D.f b) w = 0)
    (he : ∀ b, D.h (D.e b) w = 0) : levL D U W w = w := by
  rw [levL_apply, pV_apply, pX_apply_lemma_2, pXv_apply_lemma_3]
  simp [hf, he]

theorem levL_sub_perp (U W : Matrix (Fin r) (Fin r) A) {v : n → A} (he : ∀ b, D.h (D.e b) v = 0) :
    levL D U W v - v ∈ Submodule.span A (Set.range D.e) := by
  have key : levL D U W v - v =
      ∑ a, (∑ b, U a b * D.h (D.f b) v) • D.e a - ∑ a, D.h (D.f a) v • D.e a := by
    rw [levL_apply, pV_apply, pX_apply_lemma_2, pXv_apply_lemma_3]
    simp only [he, mul_zero, Finset.sum_const_zero, zero_smul, sub_zero, add_zero]
    abel
  rw [key]
  exact Submodule.sub_mem _
    (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))
    (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))

private theorem h_pV_e_lemma_11 (x : n → A) (a : Fin r) : D.h (pV D x) (D.e a) = 0 := by
  rw [h_swap_lemma_7 D H, h_e_pV H, map_zero]

private theorem h_pV_f_lemma_12 (x : n → A) (a : Fin r) : D.h (pV D x) (D.f a) = 0 := by
  rw [h_swap_lemma_7 D H, h_f_pV H, map_zero]

theorem h_decomp (x y : n → A) :
    D.h x y = D.h (pV D x) (pV D y) + ∑ a, D.σA (D.h (D.f a) x) * D.h (D.e a) y +
      ∑ a, D.σA (D.h (D.e a) x) * D.h (D.f a) y := by
  have hx : D.h x y = D.h (pV D x) y + D.h (D.pX x) y + D.h (D.pXv x) y := by
    conv_lhs => rw [decomp D x]
    rw [h_add_left_lemma_9 D H, h_add_left_lemma_9 D H]
  have hy : D.h (pV D x) y = D.h (pV D x) (pV D y) := by
    conv_lhs => rw [decomp D y]
    rw [h_add_lemma_4, h_add_lemma_4, pX_apply_lemma_2, pXv_apply_lemma_3, h_sum_lemma_6, h_sum_lemma_6]
    simp [h_pV_e_lemma_11 H, h_pV_f_lemma_12 H]
  rw [hx, hy, pX_apply_lemma_2, pXv_apply_lemma_3, h_sum_left_lemma_10 D H, h_sum_left_lemma_10 D H]

end Hyp

theorem sum_conj (σ : A →+* A) (U W : Fin r → Fin r → A) (α β : Fin r → A)
    (h : ∀ b c, ∑ a, σ (U a b) * W a c = if b = c then 1 else 0) :
    ∑ a, σ (∑ b, U a b * α b) * ∑ c, W a c * β c = ∑ b, σ (α b) * β b := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc ∑ c, ∑ a, ∑ b, σ (U a b) * σ (α b) * (W a c * β c)
      = ∑ c, ∑ b, (∑ a, σ (U a b) * W a c) * (σ (α b) * β c) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun a _ => by ring
    _ = ∑ b, σ (α b) * β b := by
        rw [Finset.sum_comm]
        simp [h]

theorem levL_uni (H : D.Hyp) (U W : Matrix (Fin r) (Fin r) A)
    (hUW : ∀ b c, ∑ a, D.σA (U a b) * W a c = if b = c then 1 else 0)
    (hWU : ∀ b c, ∑ a, D.σA (W a b) * U a c = if b = c then 1 else 0) (x y : n → A) :
    D.h (levL D U W x) (levL D U W y) = D.h x y := by
  rw [h_decomp H (levL D U W x), h_decomp H x y, pV_levL H, pV_levL H]
  simp only [h_f_levL H, h_e_levL H]
  rw [sum_conj D.σA U W _ _ hUW, sum_conj D.σA W U _ _ hWU]

end PI.LevelKSplit.W.NCL
end
end

noncomputable section

namespace PI.LevelKSplit.W.NCL

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub PI.LevelKSplit.W.NC PI.VolSemiDirect.W
open scoped TensorProduct

section R

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {r : ℕ} (P : Frame E M r) (T : F)

def uT (g : HA R σ J) : Matrix (Fin r) (Fin r) (R ⊗[F] E) :=
  Matrix.of fun a b => if a < b then
    hR R σ J (ratV (F := F) R (P.f a)) (lin R σ J g (ratV (F := F) R (P.e b)))
    else if a = b then 1 else 0

theorem uT_apply (g : HA R σ J) (a b : Fin r) : uT R σ J P g a b = if a < b then
    hR R σ J (ratV (F := F) R (P.f a)) (lin R σ J g (ratV (F := F) R (P.e b)))
    else if a = b then 1 else 0 := rfl

theorem det_uT (g : HA R σ J) : (uT R σ J P g).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · exact Finset.prod_eq_one fun a _ => by simp [uT]
  · intro i j hji
    have h : j < i := hji
    simp only [uT, Matrix.of_apply]
    rw [if_neg (lt_asymm h), if_neg (ne_of_gt h)]

def uI (g : HA R σ J) : Matrix (Fin r) (Fin r) (R ⊗[F] E) := (uT R σ J P g).adjugate

theorem uT_mul_uI (g : HA R σ J) : uT R σ J P g * uI R σ J P g = 1 := by
  rw [uI, Matrix.mul_adjugate, det_uT, one_smul]

theorem uI_mul_uT (g : HA R σ J) : uI R σ J P g * uT R σ J P g = 1 := by
  rw [uI, Matrix.adjugate_mul, det_uT, one_smul]

def cj (U : Matrix (Fin r) (Fin r) (R ⊗[F] E)) : Matrix (Fin r) (Fin r) (R ⊗[F] E) :=
  Matrix.of fun a b => sigR R σ (U b a)

theorem cj_apply (U : Matrix (Fin r) (Fin r) (R ⊗[F] E)) (a b : Fin r) :
    cj R σ U a b = sigR R σ (U b a) := rfl

theorem cj_mul (U V : Matrix (Fin r) (Fin r) (R ⊗[F] E)) : cj R σ U * cj R σ V = cj R σ (V * U) := by
  ext a b
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [cj, Matrix.mul_apply, Matrix.of_apply, map_sum, map_mul]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem cj_one : cj R σ (1 : Matrix (Fin r) (Fin r) (R ⊗[F] E)) = 1 := by
  ext a b
  simp only [cj, Matrix.of_apply, Matrix.one_apply]
  by_cases h : a = b
  · subst h
    simp
  · simp [h, Ne.symm h]

variable {R σ J P T}

section Hyp

variable (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T)
include hσσ hJ hP

theorem levTI (g : HA R σ J) (x : Fin M → R ⊗[F] E) :
    levL (datR R σ J P T) (uT R σ J P g) (cj R σ (uI R σ J P g))
      (levL (datR R σ J P T) (uI R σ J P g) (cj R σ (uT R σ J P g)) x) = x := by
  rw [levL_comp (datR_hyp hσσ hJ hP), uT_mul_uI, cj_mul, uT_mul_uI, cj_one,
    levL_one (datR_hyp hσσ hJ hP)]

theorem levIT (g : HA R σ J) (x : Fin M → R ⊗[F] E) :
    levL (datR R σ J P T) (uI R σ J P g) (cj R σ (uT R σ J P g))
      (levL (datR R σ J P T) (uT R σ J P g) (cj R σ (uI R σ J P g)) x) = x := by
  rw [levL_comp (datR_hyp hσσ hJ hP), uI_mul_uT, cj_mul, uI_mul_uT, cj_one,
    levL_one (datR_hyp hσσ hJ hP)]

end Hyp

def levU (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T) (g : HA R σ J) :
    GL (Fin M) (R ⊗[F] E) where
  val := LinearMap.toMatrix' (levL (datR R σ J P T) (uT R σ J P g) (cj R σ (uI R σ J P g)))
  inv := LinearMap.toMatrix' (levL (datR R σ J P T) (uI R σ J P g) (cj R σ (uT R σ J P g)))
  val_inv := by
    rw [← LinearMap.toMatrix'_comp]
    have : (levL (datR R σ J P T) (uT R σ J P g) (cj R σ (uI R σ J P g))).comp
        (levL (datR R σ J P T) (uI R σ J P g) (cj R σ (uT R σ J P g))) = LinearMap.id :=
      LinearMap.ext fun x => levTI hσσ hJ hP g x
    rw [this, LinearMap.toMatrix'_id]
  inv_val := by
    rw [← LinearMap.toMatrix'_comp]
    have : (levL (datR R σ J P T) (uI R σ J P g) (cj R σ (uT R σ J P g))).comp
        (levL (datR R σ J P T) (uT R σ J P g) (cj R σ (uI R σ J P g))) = LinearMap.id :=
      LinearMap.ext fun x => levIT hσσ hJ hP g x
    rw [this, LinearMap.toMatrix'_id]

section Hyp2

variable (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T)
include hσσ hJ hP

theorem levU_mem (g : HA R σ J) : levU hσσ hJ hP g ∈ HR R σ J := by
  have H : (datR R σ J P T).Hyp := datR_hyp hσσ hJ hP
  show Formalism.UG.cT (sigR R σ) (LinearMap.toMatrix' (levL (datR R σ J P T) (uT R σ J P g)
      (cj R σ (uI R σ J P g)))) * JR R J * LinearMap.toMatrix' (levL (datR R σ J P T)
      (uT R σ J P g) (cj R σ (uI R σ J P g))) = JR R J
  apply PI.LevelKSplit.W.SemiA.uj_of_uni
  intro x y
  rw [LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
  refine levL_uni H _ _ (fun b c => ?_) (fun b c => ?_) x y
  · calc ∑ a, sigR R σ (uT R σ J P g a b) * cj R σ (uI R σ J P g) a c
        = sigR R σ ((uI R σ J P g * uT R σ J P g) c b) := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [Matrix.mul_apply, map_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [cj_apply, map_mul, mul_comm]
      _ = if b = c then 1 else 0 := by
          rw [uI_mul_uT, Matrix.one_apply]
          by_cases h : b = c
          · subst h; simp
          · simp [h, Ne.symm h]
  · calc ∑ a, sigR R σ (cj R σ (uI R σ J P g) a b) * uT R σ J P g a c
        = (uI R σ J P g * uT R σ J P g) b c := by
          rw [Matrix.mul_apply]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [cj_apply]
          exact congrArg (· * uT R σ J P g a c) (H.σσ _)
      _ = if b = c then 1 else 0 := by rw [uI_mul_uT, Matrix.one_apply]

end Hyp2

def levG (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T) (g : HA R σ J) :
    HA R σ J :=
  ⟨levU hσσ hJ hP g, levU_mem hσσ hJ hP g⟩

variable (R σ J P)

def Asub : Subgroup (HA R σ J) where
  carrier := {g | g ∈ Nsub R σ J P ∧ (∀ w ∈ NC.Wp R σ J P, lin R σ J g w = w) ∧
    (∀ b, lin R σ J g (ratV (F := F) R (P.f b)) ∈ spanR (F := F) R P.f Set.univ) ∧
    (∀ b, lin R σ J g⁻¹ (ratV (F := F) R (P.f b)) ∈ spanR (F := F) R P.f Set.univ)}
  one_mem' := by
    refine ⟨(Nsub R σ J P).one_mem, fun w _ => lin_one R σ J w, fun b => ?_, fun b => ?_⟩
    · rw [lin_one]; exact Submodule.subset_span ⟨b, Set.mem_univ _, rfl⟩
    · rw [inv_one, lin_one]; exact Submodule.subset_span ⟨b, Set.mem_univ _, rfl⟩
  mul_mem' := by
    intro g h hg hh
    obtain ⟨hg1, hg2, hg3, hg4⟩ := hg
    obtain ⟨hh1, hh2, hh3, hh4⟩ := hh
    have key : ∀ (k : HA R σ J), (∀ b, lin R σ J k (ratV (F := F) R (P.f b)) ∈
        spanR (F := F) R P.f Set.univ) → ∀ y ∈ spanR (F := F) R P.f Set.univ,
        lin R σ J k y ∈ spanR (F := F) R P.f Set.univ := by
      intro k hk y hy
      have hle : spanR (F := F) R P.f Set.univ ≤ (spanR (F := F) R P.f Set.univ).comap (lin R σ J k) := by
        rw [spanR, Submodule.span_le]
        rintro _ ⟨b, _, rfl⟩
        exact hk b
      exact hle hy
    refine ⟨(Nsub R σ J P).mul_mem hg1 hh1, fun w hw => ?_, fun b => ?_, fun b => ?_⟩
    · rw [lin_mul, hh2 w hw, hg2 w hw]
    · rw [lin_mul]; exact key g hg3 _ (hh3 b)
    · rw [mul_inv_rev, lin_mul]; exact key h⁻¹ hh4 _ (hg4 b)
  inv_mem' := by
    intro g hg
    obtain ⟨hg1, hg2, hg3, hg4⟩ := hg
    refine ⟨(Nsub R σ J P).inv_mem hg1, fun w hw => ?_, hg4, fun b => ?_⟩
    · conv_lhs => rw [← hg2 w hw]
      exact lin_inv_lin R σ J g w
    · rw [inv_inv]; exact hg3 b

variable {R σ J P}

theorem spanE_f_zero (H : (datR R σ J P T).Hyp) {s : Set (Fin r)} {x : Fin M → R ⊗[F] E}
    (hx : x ∈ spanR (F := F) R P.e s) {a : Fin r} (ha : a ∉ s) :
    (datR R σ J P T).h ((datR R σ J P T).f a) x = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, hc, rfl⟩ := hy
    show (datR R σ J P T).h ((datR R σ J P T).f a) ((datR R σ J P T).e c) = 0
    rw [PG.Dat.fe H, if_neg]
    rintro rfl
    exact ha hc
  | zero => exact PG.Dat.h_zero_right _ _
  | add x y _ _ hx hy => rw [PG.Dat.h_add_right, hx, hy, add_zero]
  | smul c x _ hx => rw [PG.Dat.h_smul_right, hx, mul_zero]

theorem pXv_mem_span (x : Fin M → R ⊗[F] E) :
    (datR R σ J P T).pXv x ∈ Submodule.span (R ⊗[F] E) (Set.range (datR R σ J P T).f) := by
  rw [PG.Dat.pXv_apply]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem pXv_of_span (H : (datR R σ J P T).Hyp) {x : Fin M → R ⊗[F] E}
    (hx : x ∈ Submodule.span (R ⊗[F] E) (Set.range (datR R σ J P T).f)) :
    (datR R σ J P T).pXv x = x := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, rfl⟩ := hy
    rw [PG.Dat.pXv_apply]
    simp [H.ef]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
  | smul c x _ hx => rw [map_smul, hx]

theorem pX_mem (x : Fin M → R ⊗[F] E) :
    (datR R σ J P T).pX x ∈ Submodule.span (R ⊗[F] E) (Set.range fun a => ratV (F := F) R (P.e a)) :=
  PG.Dat.pX_mem_span (D := datR R σ J P T) x

theorem pXv_mem (x : Fin M → R ⊗[F] E) :
    (datR R σ J P T).pXv x ∈ Submodule.span (R ⊗[F] E) (Set.range fun a => ratV (F := F) R (P.f a)) :=
  pXv_mem_span (T := T) x

theorem pV_mem_Wp (H : (datR R σ J P T).Hyp) (x : Fin M → R ⊗[F] E) :
    pV (datR R σ J P T) x ∈ NC.Wp R σ J P :=
  ⟨fun a => h_e_pV H a x, fun a => h_f_pV H a x⟩

section Hyp3

variable (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T)
include hσσ hJ hP

theorem lin_levG (g : HA R σ J) :
    lin R σ J (levG hσσ hJ hP g) = levL (datR R σ J P T) (uT R σ J P g) (cj R σ (uI R σ J P g)) := by
  first
  | rfl
  | (unfold lin; simp [levG, levU, HA.mat]; exact Matrix.toLin'_toMatrix' _)
  | (unfold lin; simp [levG, levU, HA.mat]; exact LinearMap.ext fun x => LinearMap.toMatrix'_mulVec _ x)

theorem lin_levG_inv (g : HA R σ J) (x : Fin M → R ⊗[F] E) :
    lin R σ J (levG hσσ hJ hP g)⁻¹ x =
      levL (datR R σ J P T) (uI R σ J P g) (cj R σ (uT R σ J P g)) x := by
  unfold lin
  simp [levG, levU, HA.mat]
  first
  | exact LinearMap.toMatrix'_mulVec _ x
  | (show (LinearMap.toMatrix' (levL (datR R σ J P T) (uI R σ J P g) (cj R σ (uT R σ J P g)))).mulVec x = _
     exact LinearMap.toMatrix'_mulVec _ x)

theorem levG_mem (g : HA R σ J) : levG hσσ hJ hP g ∈ Asub R σ J P := by
  have H : (datR R σ J P T).Hyp := datR_hyp hσσ hJ hP
  have hfs : ∀ (U W : Matrix (Fin r) (Fin r) (R ⊗[F] E)) (b : Fin r),
      levL (datR R σ J P T) U W (ratV (F := F) R (P.f b)) ∈ spanR (F := F) R P.f Set.univ :=
    fun U W b => by
      show levL (datR R σ J P T) U W ((datR R σ J P T).f b) ∈ _
      rw [levL_f H]
      exact Submodule.sum_mem _ fun d _ => Submodule.smul_mem _ _
        (Submodule.subset_span ⟨d, Set.mem_univ _, rfl⟩)
  refine ⟨⟨fun b => ?_, fun v hv => ?_⟩, fun w hw => ?_, fun b => ?_, fun b => ?_⟩
  · rw [lin_levG]
    show levL (datR R σ J P T) _ _ ((datR R σ J P T).e b) - (datR R σ J P T).e b ∈ _
    rw [levL_e H]
    have e1 : ∑ a, uT R σ J P g a b • (datR R σ J P T).e a - (datR R σ J P T).e b =
        ∑ a, (if a < b then uT R σ J P g a b else 0) • (datR R σ J P T).e a := by
      have eb : (datR R σ J P T).e b =
          ∑ a, (if a = b then (1 : R ⊗[F] E) else 0) • (datR R σ J P T).e a := by simp
      rw [eb, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← sub_smul]
      congr 1
      rw [uT_apply]
      rcases lt_trichotomy a b with h | h | h
      · simp [h, h.ne]
      · subst h; simp
      · simp [not_lt.2 h.le, h.ne']
    rw [e1]
    refine Submodule.sum_mem _ fun a _ => ?_
    split_ifs with h
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, h, rfl⟩)
    · rw [zero_smul]; exact Submodule.zero_mem _
  · rw [lin_levG, PI.LevelKSplit.W.Glob.spanR_univ]
    exact levL_sub_perp H _ _ hv
  · rw [lin_levG]
    exact levL_alt H _ _ hw.2 hw.1
  · rw [lin_levG]; exact hfs _ _ b
  · rw [lin_levG_inv]; exact hfs _ _ b

theorem levG_e (n : HA R σ J) (hn : n ∈ Nsub R σ J P) (b : Fin r) :
    lin R σ J (levG hσσ hJ hP n) (ratV (F := F) R (P.e b)) = lin R σ J n (ratV (F := F) R (P.e b)) := by
  have H : (datR R σ J P T).Hyp := datR_hyp hσσ hJ hP
  have hn1 : UniC R σ J P.e n := hn.1
  have hmem : lin R σ J n (ratV (F := F) R (P.e b)) ∈
      Submodule.span (R ⊗[F] E) (Set.range (datR R σ J P T).e) := by
    have := uni_map_le hn1 Set.univ (fun _ _ _ _ => Set.mem_univ _)
      (Submodule.mem_map_of_mem (Submodule.subset_span ⟨b, Set.mem_univ _, rfl⟩))
    rw [PI.LevelKSplit.W.Glob.spanR_univ] at this
    exact this
  have e1 : lin R σ J n (ratV (F := F) R (P.e b)) = ∑ a, (datR R σ J P T).h ((datR R σ J P T).f a)
      (lin R σ J n (ratV (F := F) R (P.e b))) • (datR R σ J P T).e a := by
    conv_lhs => rw [← PG.Dat.pX_of_span H hmem]
    exact PG.Dat.pX_apply _ _
  rw [lin_levG]
  show levL (datR R σ J P T) _ _ ((datR R σ J P T).e b) = _
  rw [levL_e H, e1]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  rw [uT_apply]
  by_cases h1 : a < b
  · rw [if_pos h1]; rfl
  · rw [if_neg h1]
    have h0 := spanE_f_zero (T := T) H (hn1 b) (a := a) (fun h => h1 h)
    have hfe : (datR R σ J P T).h ((datR R σ J P T).f a) (ratV (F := F) R (P.e b)) =
        if a = b then 1 else 0 := PG.Dat.fe H a b
    rw [PG.Dat.h_sub_right, hfe, sub_eq_zero] at h0
    exact h0.symm

theorem levG_inv_mul (n : HA R σ J) (hn : n ∈ Nsub R σ J P) :
    (levG hσσ hJ hP n)⁻¹ * n ∈ LevelUnipotentSubgroup R σ J P := by
  refine Subgroup.mem_inf.2 ⟨(Nsub R σ J P).mul_mem ((Nsub R σ J P).inv_mem
    (levG_mem hσσ hJ hP n).1) hn, (mem_stabT R σ J P.e _).2 fun b => ?_⟩
  rw [lin_mul, ← levG_e hσσ hJ hP n hn b, lin_inv_lin]

theorem levi_inf_unipotent_eq_one (u : HA R σ J) (hu : u ∈ Asub R σ J P) (hu1 : u ∈ LevelUnipotentSubgroup R σ J P) : u = 1 := by
  have H : (datR R σ J P T).Hyp := datR_hyp hσσ hJ hP
  obtain ⟨_, hW, hF, _⟩ := hu
  have hS := (mem_stabT R σ J P.e u).1 (Subgroup.mem_inf.1 hu1).2
  have hf : ∀ b, lin R σ J u (ratV (F := F) R (P.f b)) = ratV (F := F) R (P.f b) := by
    intro b
    have hm : lin R σ J u (ratV (F := F) R (P.f b)) ∈
        Submodule.span (R ⊗[F] E) (Set.range (datR R σ J P T).f) := by
      have := hF b
      rw [PI.LevelKSplit.W.Glob.spanR_univ] at this
      exact this
    rw [← pXv_of_span H hm, PG.Dat.pXv_apply]
    have hc : ∀ d, (datR R σ J P T).h ((datR R σ J P T).e d) (lin R σ J u (ratV (F := F) R (P.f b))) =
        if d = b then 1 else 0 := fun d => by
      show hR R σ J (ratV (F := F) R (P.e d)) (lin R σ J u (ratV (F := F) R (P.f b))) = _
      rw [← hS d, hR_lin]
      exact H.ef d b
    simp only [hc, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl
  apply PI.LevelKSplit.W.SemiA.ext_lin
  intro x
  rw [lin_one]
  conv_lhs => rw [decomp (datR R σ J P T) x]
  rw [map_add (f := _), map_add (f := _), hW _ (pV_mem_Wp H x),
    PI.LevelKSplit.W.Glob.lin_fix_span u P.e hS _ (pX_mem x),
    PI.LevelKSplit.W.Glob.lin_fix_span u P.f hf _ (pXv_mem x)]
  exact (decomp (datR R σ J P T) x).symm

end Hyp3

theorem unipotent_radical_normal (n m : HA R σ J) (hn : n ∈ Nsub R σ J P) (hm : m ∈ LevelUnipotentSubgroup R σ J P) :
    n * m * n⁻¹ ∈ LevelUnipotentSubgroup R σ J P := by
  have hm' := Subgroup.mem_inf.1 hm
  refine Subgroup.mem_inf.2 ⟨(Nsub R σ J P).mul_mem ((Nsub R σ J P).mul_mem hn hm'.1)
    ((Nsub R σ J P).inv_mem hn), (mem_stabT R σ J P.e _).2 fun b => ?_⟩
  have hmS := (mem_stabT R σ J P.e m).1 hm'.2
  have h1 : lin R σ J n⁻¹ (ratV (F := F) R (P.e b)) ∈
      Submodule.span (R ⊗[F] E) (Set.range fun a => ratV (F := F) R (P.e a)) := by
    have := uni_map_le ((Nsub R σ J P).inv_mem hn).1 Set.univ (fun _ _ _ _ => Set.mem_univ _)
      (Submodule.mem_map_of_mem (Submodule.subset_span ⟨b, Set.mem_univ _, rfl⟩))
    rw [PI.LevelKSplit.W.Glob.spanR_univ] at this
    exact this
  rw [lin_mul, lin_mul, PI.LevelKSplit.W.Glob.lin_fix_span m P.e hmS _ h1, lin_lin_inv]

theorem H_comm_A (H : (datR R σ J P T).Hyp) (h u : HA R σ J) (hh : h ∈ Hsub R σ J P)
    (hu : u ∈ Asub R σ J P) : h * u = u * h := by
  obtain ⟨hu1, hW, hF, _⟩ := hu
  have hu1' : UniC R σ J P.e u := hu1.1
  have hhe := PI.LevelKSplit.W.Glob.lin_fix_span h P.e (PI.LevelKSplit.W.Glob.H_fix_e P h hh)
  have hhf := PI.LevelKSplit.W.Glob.lin_fix_span h P.f (PI.LevelKSplit.W.Glob.H_fix_f P h hh)
  apply PI.LevelKSplit.W.SemiA.ext_lin
  intro x
  have hWx : lin R σ J h (pV (datR R σ J P T) x) ∈ NC.Wp R σ J P := by
    refine ⟨fun a => ?_, fun a => ?_⟩
    · rw [← PI.LevelKSplit.W.Glob.H_fix_e P h hh a, hR_lin]; exact h_e_pV H a x
    · rw [← PI.LevelKSplit.W.Glob.H_fix_f P h hh a, hR_lin]; exact h_f_pV H a x
  have uE : lin R σ J u ((datR R σ J P T).pX x) ∈
      Submodule.span (R ⊗[F] E) (Set.range fun a => ratV (F := F) R (P.e a)) := by
    have hx : (datR R σ J P T).pX x ∈ spanR (F := F) R P.e Set.univ := by
      rw [PI.LevelKSplit.W.Glob.spanR_univ]; exact pX_mem x
    have := uni_map_le hu1' Set.univ (fun _ _ _ _ => Set.mem_univ _) (Submodule.mem_map_of_mem hx)
    rw [PI.LevelKSplit.W.Glob.spanR_univ] at this
    exact this
  have uF : lin R σ J u ((datR R σ J P T).pXv x) ∈
      Submodule.span (R ⊗[F] E) (Set.range fun a => ratV (F := F) R (P.f a)) := by
    have hle : spanR (F := F) R P.f Set.univ ≤ (spanR (F := F) R P.f Set.univ).comap (lin R σ J u) := by
      rw [spanR, Submodule.span_le]
      rintro _ ⟨b, _, rfl⟩
      exact hF b
    have hx : (datR R σ J P T).pXv x ∈ spanR (F := F) R P.f Set.univ := by
      rw [PI.LevelKSplit.W.Glob.spanR_univ]; exact pXv_mem x
    have := hle hx
    rw [PI.LevelKSplit.W.Glob.spanR_univ] at this
    exact this
  rw [lin_mul, lin_mul]
  conv_lhs => rw [decomp (datR R σ J P T) x]
  conv_rhs => rw [decomp (datR R σ J P T) x]
  simp only [map_add (f := _)]
  rw [hW _ (pV_mem_Wp H x), hW _ hWx, hhe _ (pX_mem x), hhf _ (pXv_mem x),
    hhe _ uE, hhf _ uF]

end R

end PI.LevelKSplit.W.NCL
end
end

noncomputable section

namespace PI.LevelKSplit.W.NCL

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField PI.LevelKSplit.W.NC PI.VolSemiDirect.W
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r}

theorem mem_Asub {g : HA R σ J} : g ∈ Asub R σ J P ↔ (g ∈ Nsub R σ J P ∧
    (∀ w ∈ NC.Wp R σ J P, lin R σ J g w = w) ∧
    (∀ b, lin R σ J g (ratV (F := F) R (P.f b)) ∈ spanR (F := F) R P.f Set.univ) ∧
    (∀ b, lin R σ J g⁻¹ (ratV (F := F) R (P.f b)) ∈ spanR (F := F) R P.f Set.univ)) := Iff.rfl

theorem Asub_le : Asub R σ J P ≤ Nsub R σ J P := fun _ hg => (mem_Asub.1 hg).1

end Gen

section Af

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ}

theorem isClosed_Asub (hJ : IsHermND σ J) (hinv : ∀ x, σ (σ x) = x) (P : Frame E M r) (T : F)
    (hP : P.IsStd σ J T) : IsClosed (Asub (Af F) σ J P : Set (HA (Af F) σ J)) := by
  have hD : ∀ a a', hE σ J (P.e a') (P.f a) = if a = a' then 1 else 0 := fun a a' => by
    rw [hP.2.2.1 a' a]
    by_cases h : a = a'
    · subst h; simp
    · simp [h, Ne.symm h]
  have hF : IsClosed (spanR (F := F) (Af F) P.f Set.univ : Set (Fin M → Af F ⊗[F] E)) :=
    PI.LevelKSplit.W.ExC.isClosed_spanR P.f P.e hD Set.univ
  have e : (Asub (Af F) σ J P : Set (HA (Af F) σ J)) =
      (Nsub (Af F) σ J P : Set (HA (Af F) σ J)) ∩
        ((⋂ w ∈ NC.Wp (Af F) σ J P, {g : HA (Af F) σ J | lin (Af F) σ J g w = w}) ∩
        ((⋂ b, {g : HA (Af F) σ J | lin (Af F) σ J g (ratV (F := F) (Af F) (P.f b)) ∈
            spanR (F := F) (Af F) P.f Set.univ}) ∩
          (⋂ b, {g : HA (Af F) σ J | lin (Af F) σ J g⁻¹ (ratV (F := F) (Af F) (P.f b)) ∈
            spanR (F := F) (Af F) P.f Set.univ}))) := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    exact mem_Asub
  rw [e]
  refine (PI.LevelKSplit.W.ExC.closed_SNH hJ hinv P T hP).2.1.inter
    ((isClosed_biInter fun w _ => ?_).inter ((isClosed_iInter fun b => ?_).inter
      (isClosed_iInter fun b => ?_)))
  · exact isClosed_eq (Md.continuous_linear_action (Af F) σ J continuous_id continuous_const) continuous_const
  · exact hF.preimage (Md.continuous_linear_action (Af F) σ J continuous_id continuous_const)
  · exact hF.preimage (Md.continuous_linear_action (Af F) σ J continuous_inv continuous_const)

end Af

end PI.LevelKSplit.W.NCL
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.ContinuousLevLMat
noncomputable section

namespace PI.LevelKSplit.W.NCL

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField PI.LevelKSplit.W.NC PI.VolSemiDirect.W
open scoped TensorProduct

section Af

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ}


set_option maxHeartbeats 800000 in
theorem continuous_uT (P : Frame E M r) (a b : Fin r) :
    Continuous fun g : HA (Af F) σ J => uT (Af F) σ J P g a b := by
  have h1 : Continuous fun g : HA (Af F) σ J => lin (Af F) σ J g (ratV (F := F) (Af F) (P.e b)) :=
    PI.LevelKSplit.W.ExC.continuous_lin _
  have h0 : Continuous fun g : HA (Af F) σ J =>
      ((ratV (F := F) (Af F) (P.f a), lin (Af F) σ J g (ratV (F := F) (Af F) (P.e b))) :
        (Fin M → Af F ⊗[F] E) × (Fin M → Af F ⊗[F] E)) :=
    continuous_const.prodMk h1
  have h3 := PI.VolStabSW.continuous_hR (R := Af F) σ J
  have h2 := h3.comp h0
  unfold uT
  simp only [Matrix.of_apply]
  split_ifs
  · exact h2
  · exact continuous_const
  · exact continuous_const

theorem continuous_levL_mat (T : F) (P : Frame E M r) {X : Type} [TopologicalSpace X]
    {U W : X → Matrix (Fin r) (Fin r) (Af F ⊗[F] E)}
    (hU : ∀ a b, Continuous fun x => U x a b) (hW : ∀ a b, Continuous fun x => W x a b) :
    Continuous fun x => LinearMap.toMatrix' (levL (datR (Af F) σ J P T) (U x) (W x)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [levL, map_add (f := _), map_sum, map_smul]
  refine (continuous_const.add (continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
    (hU a b).smul continuous_const)).add
    (continuous_finsetSum _ fun d _ => continuous_finsetSum _ fun b _ => (hW d b).smul continuous_const)

theorem continuous_levG (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (P : Frame E M r) (T : F)
    (hP : P.IsStd σ J T) : Continuous (levG (R := Af F) hσσ hJ hP) := by
  have hU : ∀ a b, Continuous fun g : HA (Af F) σ J => uT (Af F) σ J P g a b := continuous_uT P
  have hUm : Continuous fun g : HA (Af F) σ J => uT (Af F) σ J P g :=
    continuous_pi fun a => continuous_pi fun b => hU a b
  have hIm : Continuous fun g : HA (Af F) σ J => uI (Af F) σ J P g := by
    unfold uI
    exact hUm.matrix_adjugate
  have hI : ∀ a b, Continuous fun g : HA (Af F) σ J => uI (Af F) σ J P g a b := fun a b =>
    (continuous_apply b).comp ((continuous_apply a).comp hIm)
  have hcI : ∀ a b, Continuous fun g : HA (Af F) σ J => cj (Af F) σ (uI (Af F) σ J P g) a b := by
    intro a b
    unfold cj
    simp only [Matrix.of_apply]
    exact (PI.AdicCompletionValuation.continuous_sigR (R := Af F) σ).comp (hI b a)
  have hcT : ∀ a b, Continuous fun g : HA (Af F) σ J => cj (Af F) σ (uT (Af F) σ J P g) a b := by
    intro a b
    unfold cj
    simp only [Matrix.of_apply]
    exact (PI.AdicCompletionValuation.continuous_sigR (R := Af F) σ).comp (hU b a)
  have hM : Continuous fun g : HA (Af F) σ J =>
      LinearMap.toMatrix' (lin (Af F) σ J (levG hσσ hJ hP g)) := by
    simp only [lin_levG]
    exact continuous_levL_mat T P hU hcI
  have hMi : Continuous fun g : HA (Af F) σ J =>
      LinearMap.toMatrix' (lin (Af F) σ J (levG hσσ hJ hP g)⁻¹) := by
    have e : ∀ g : HA (Af F) σ J, lin (Af F) σ J (levG hσσ hJ hP g)⁻¹ =
        levL (datR (Af F) σ J P T) (uI (Af F) σ J P g) (cj (Af F) σ (uT (Af F) σ J P g)) :=
      fun g => LinearMap.ext fun x => by rw [lin_levG_inv]
    simp only [e]
    exact continuous_levL_mat T P hI hcT
  unfold levG
  apply Continuous.subtype_mk
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact hM.congr fun g => LinearMap.toMatrix'_toLin' _
  · exact hMi.congr fun g => LinearMap.toMatrix'_toLin' _

end Af

end PI.LevelKSplit.W.NCL
end
end

noncomputable section

namespace PI.LevelKSplit.W.NCL

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField PI.LevelKSplit.W.NC PI.VolSemiDirect.W
open scoped TensorProduct

theorem levi_part_all : LevPAll := by
  intro F E _ _ _ _ _ σ hσ M J _
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  intro hJ hinv r P T hP
  have H : (datR (Af F) σ J P T).Hyp := datR_hyp hinv hJ hP
  exact ⟨Asub (Af F) σ J P, levG hinv hJ hP, Asub_le, isClosed_Asub hJ hinv P T hP,
    continuous_levG hinv hJ P T hP,
    fun n hn => ⟨levG_mem hinv hJ hP n, levG_inv_mul hinv hJ hP n hn⟩,
    fun u hu hu1 => levi_inf_unipotent_eq_one hinv hJ hP u hu hu1,
    fun n hn m hm => unipotent_radical_normal n m hn hm,
    fun h hh u hu => H_comm_A H h u hh hu⟩

end PI.LevelKSplit.W.NCL
