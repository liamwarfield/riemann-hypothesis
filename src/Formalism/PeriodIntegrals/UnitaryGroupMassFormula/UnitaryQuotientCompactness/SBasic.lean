module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.SsetGroup

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.SBasic
open Matrix

noncomputable section

namespace PI.QuotSetU.UnitaryGroupMassFormula.SW

open PI PI.QuotSetU

variable {k r : ℕ}

def piI (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if r ≤ i.val ∧ i.val ≤ r + k then i else ⟨2 * r + k - i.val, by omega⟩

def epsI (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1

lemma piI_val (i : Fin (2 * r + k + 1)) :
    (piI k r i).val = if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val := by
  unfold piI
  split_ifs <;> rfl

lemma piI_piI (i : Fin (2 * r + k + 1)) : piI k r (piI k r i) = i := by
  have hi := i.isLt
  apply Fin.ext
  rw [piI_val, piI_val]
  split_ifs <;> omega

lemma epsI_piI (i : Fin (2 * r + k + 1)) : epsI k r (piI k r i) = epsI k r i := by
  have hi := i.isLt
  unfold epsI
  rw [piI_val]
  split_ifs <;> first | rfl | omega

lemma epsI_mul_self (i : Fin (2 * r + k + 1)) : epsI k r i * epsI k r i = 1 := by
  unfold epsI
  split_ifs <;> norm_num

lemma star_epsI (i : Fin (2 * r + k + 1)) : star (epsI k r i) = epsI k r i := by
  unfold epsI
  split_ifs <;> simp

lemma Hpk_apply (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = piI k r i then epsI k r i else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [Hpk, epsI, Fin.ext_iff, piI_val]
  split_ifs <;> first | rfl | omega

lemma Hpk_mul_apply (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j) :
    (Hpk k r * X) i j = epsI k r i * X (piI k r i) j := by
  simp [Matrix.mul_apply, Hpk_apply, ite_mul]

lemma mul_Hpk_apply (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j) :
    (X * Hpk k r) i j = X i (piI k r j) * epsI k r j := by
  have hc : ∀ l, (j = piI k r l) ↔ (l = piI k r j) :=
    fun l => ⟨fun h => by rw [h, piI_piI], fun h => by rw [h, piI_piI]⟩
  simp only [Matrix.mul_apply, Hpk_apply, hc, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, epsI_piI]

lemma Hpk_mulVec_apply (v : Fin (2 * r + k + 1) → ℂ) (i) :
    (Hpk k r *ᵥ v) i = epsI k r i * v (piI k r i) := by
  simp [Matrix.mulVec, dotProduct, Hpk_apply, ite_mul]

lemma Hpk_mul_self : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Hpk_mul_apply, Hpk_apply, piI_piI, epsI_piI, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp [epsI_mul_self]
  · simp [h, Ne.symm h]

lemma Hpk_conjTranspose : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  rw [Matrix.conjTranspose_apply, Hpk_apply, Hpk_apply]
  by_cases h : j = piI k r i
  · have h' : i = piI k r j := by rw [h, piI_piI]
    rw [if_pos h', if_pos h, star_epsI, h, epsI_piI]
  · have h' : ¬ i = piI k r j := fun h' => h (by rw [h', piI_piI])
    rw [if_neg h', if_neg h, star_zero]

lemma inv_mul_UH {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  rw [show Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) by
    simp only [Matrix.mul_assoc], hg', Hpk_mul_self]

lemma inv_eq_UH {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    g⁻¹ = Hpk k r * gᴴ * Hpk k r := Matrix.inv_eq_left_inv (inv_mul_UH hg)

lemma mul_inv_UH {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    g * g⁻¹ = 1 := by
  rw [inv_eq_UH hg]
  exact mul_eq_one_comm.mp (inv_mul_UH hg)

lemma inv_mul_UH' {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    g⁻¹ * g = 1 := by
  rw [inv_eq_UH hg]
  exact inv_mul_UH hg

lemma one_mem_UH : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ UH (Hpk k r) := by
  show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * Hpk k r * 1 = Hpk k r
  simp

lemma mul_mem_UH {a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ UH (Hpk k r)) (hb : b ∈ UH (Hpk k r)) : a * b ∈ UH (Hpk k r) := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

lemma inv_mem_UH {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ UH (Hpk k r)) : a⁻¹ ∈ UH (Hpk k r) := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have h1 : a * a⁻¹ = 1 := mul_inv_UH ha
  have h2 : (a⁻¹)ᴴ * aᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  show (a⁻¹)ᴴ * Hpk k r * a⁻¹ = Hpk k r
  calc (a⁻¹)ᴴ * Hpk k r * a⁻¹ = (a⁻¹)ᴴ * (aᴴ * Hpk k r * a) * a⁻¹ := by rw [ha']
    _ = ((a⁻¹)ᴴ * aᴴ) * Hpk k r * (a * a⁻¹) := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

lemma Hpk_mul_mul_Hpk_apply (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j) :
    (Hpk k r * X * Hpk k r) i j = epsI k r i * X (piI k r i) (piI k r j) * epsI k r j := by
  rw [mul_Hpk_apply, Hpk_mul_apply]

end PI.QuotSetU.UnitaryGroupMassFormula.SW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.ModBase
open MeasureTheory Matrix Topology
open scoped ENNReal NNReal

noncomputable section

namespace PI.QuotSetU.UnitaryGroupMassFormula.ModW

open PI

variable {m : ℕ}

def MG (G : Set (Matrix (Fin m) (Fin m) ℂ)) (_hG : IsMatGroup G) : Type :=
  {x : MtM m // Matrix.of x ∈ G}

variable {G : Set (Matrix (Fin m) (Fin m) ℂ)} {hG : IsMatGroup G}

namespace MG

def toM (x : MG G hG) : Matrix (Fin m) (Fin m) ℂ := Matrix.of x.1

def val (x : MG G hG) : MtM m := x.1

theorem toM_mem (x : MG G hG) : x.toM ∈ G := x.2

def mk (hG : IsMatGroup G) (g : Matrix (Fin m) (Fin m) ℂ) (h : g ∈ G) : MG G hG :=
  ⟨Matrix.of.symm g, by
    have heq : Matrix.of (Matrix.of.symm g) = g := (Matrix.of).apply_symm_apply g
    exact heq ▸ h⟩

@[simp] theorem toM_mk (g : Matrix (Fin m) (Fin m) ℂ) (h : g ∈ G) : (mk hG g h).toM = g := by
  rfl

theorem toM_injective : Function.Injective (toM : MG G hG → Matrix (Fin m) (Fin m) ℂ) := by
  intro x y h
  exact Subtype.ext (Matrix.of.injective h)

@[simp] theorem mk_toM (x : MG G hG) : mk hG x.toM x.toM_mem = x := toM_injective (toM_mk _ _)

instance : Mul (MG G hG) := ⟨fun x y => mk hG (x.toM * y.toM) (hG.2.2.1 _ x.2 _ y.2)⟩
instance : One (MG G hG) := ⟨mk hG 1 hG.2.1⟩
instance : Inv (MG G hG) := ⟨fun x => mk hG (x.toM)⁻¹ (hG.2.2.2 _ x.2).1⟩

@[simp] theorem toM_mul (x y : MG G hG) : (x * y).toM = x.toM * y.toM := toM_mk _ _
@[simp] theorem toM_one : (1 : MG G hG).toM = 1 := toM_mk _ _
@[simp] theorem toM_inv (x : MG G hG) : x⁻¹.toM = (x.toM)⁻¹ := toM_mk _ _

theorem mul_inv_toM (x : MG G hG) : x.toM * (x.toM)⁻¹ = 1 := (hG.2.2.2 _ x.toM_mem).2

theorem det_ne_zero (x : MG G hG) : x.toM.det ≠ 0 := by
  intro h
  have e := congrArg Matrix.det (mul_inv_toM x)
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at e
  exact zero_ne_one e

theorem inv_mul_toM (x : MG G hG) : (x.toM)⁻¹ * x.toM = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (det_ne_zero x))

instance : Group (MG G hG) where
  mul := (· * ·)
  one := 1
  inv := (·⁻¹)
  zpow := zpowRec npowRec
  zpow_zero' a := rfl
  zpow_succ' n a := rfl
  mul_assoc a b c := by
    apply toM_injective
    simp [Matrix.mul_assoc]
  one_mul a := by
    apply toM_injective
    simp
  mul_one a := by
    apply toM_injective
    simp
  inv_mul_cancel a := by
    apply toM_injective
    simp [inv_mul_toM]
  zpow_neg' n a := by
    change (npowRec n.succ a)⁻¹ = (npowRec n.succ a)⁻¹
    rfl

@[simp] theorem toM_mul' (x y : MG G hG) : (x * y).toM = x.toM * y.toM := toM_mul x y

end MG

open MG

theorem isClosed_set (hG : IsMatGroup G) : IsClosed {x : MtM m | Matrix.of x ∈ G} :=
  hG.1.preimage continuous_id

instance : TopologicalSpace (MG G hG) :=
  inferInstanceAs (TopologicalSpace {x : MtM m // Matrix.of x ∈ G})
instance : T2Space (MG G hG) := inferInstanceAs (T2Space {x : MtM m // Matrix.of x ∈ G})
instance : SecondCountableTopology (MG G hG) :=
  inferInstanceAs (SecondCountableTopology {x : MtM m // Matrix.of x ∈ G})
instance : LocallyCompactSpace (MG G hG) :=
  (isClosed_set hG).locallyCompactSpace
instance : MeasurableSpace (MG G hG) :=
  inferInstanceAs (MeasurableSpace {x : MtM m // Matrix.of x ∈ G})
instance : BorelSpace (MG G hG) := inferInstanceAs (BorelSpace {x : MtM m // Matrix.of x ∈ G})

theorem continuous_val : Continuous (val : MG G hG → MtM m) := continuous_subtype_val

theorem continuous_toM : Continuous (toM : MG G hG → Matrix (Fin m) (Fin m) ℂ) := continuous_subtype_val

theorem continuous_iff_toM {X : Type*} [TopologicalSpace X] {f : X → MG G hG} :
    Continuous f ↔ Continuous (fun x => (f x).toM) :=
  ⟨fun h => continuous_toM.comp h, fun h => continuous_induced_rng.2 h⟩

instance : IsTopologicalGroup (MG G hG) where
  continuous_mul := by
    rw [continuous_iff_toM]
    convert (continuous_toM.comp continuous_fst).matrix_mul
      (continuous_toM.comp continuous_snd) using 1
    funext x
    exact toM_mul x.1 x.2
  continuous_inv := by
    rw [continuous_iff_toM]
    have hfun : (fun x : MG G hG => x⁻¹.toM) = fun x => (x.toM)⁻¹ := funext toM_inv
    rw [hfun]
    refine continuous_iff_continuousAt.2 fun x => ?_
    refine (continuousAt_matrix_inv _ ?_).comp continuous_toM.continuousAt
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (det_ne_zero x)

theorem isClosedEmbedding_val : IsClosedEmbedding (val : MG G hG → MtM m) :=
  (isClosed_set hG).isClosedEmbedding_subtypeVal

def onG (hG : IsMatGroup G) (μ : Measure (MtM m)) : Measure (MG G hG) := μ.comap val

end PI.QuotSetU.UnitaryGroupMassFormula.ModW
end
end
