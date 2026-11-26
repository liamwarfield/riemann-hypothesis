module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBridgeAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.SpanPrism

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.CoreDefs
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.SuccAboveEqFc
noncomputable section

open Finset

namespace PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

variable {Y : Type}

def fc {n : ℕ} (i : ℕ) (l : Fin n) : Fin (n + 1) :=
  ⟨if (l : ℕ) < i then (l : ℕ) else (l : ℕ) + 1, by split_ifs <;> omega⟩

theorem fc_val {n : ℕ} (i : ℕ) (l : Fin n) :
    ((fc i l : Fin (n + 1)) : ℕ) = if (l : ℕ) < i then (l : ℕ) else (l : ℕ) + 1 :=
  rfl

theorem succAbove_eq_fc {n : ℕ} (i : Fin (n + 1)) (l : Fin n) : i.succAbove l = fc i l := by
  apply Fin.ext
  rw [fc_val]
  rcases Nat.lt_or_ge (l : ℕ) (i : ℕ) with h | h
  · rw [if_pos h, Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h)]
    rfl
  · rw [if_neg (by omega), Fin.succAbove_of_le_castSucc _ _ (by simpa [Fin.le_def] using h)]
    rfl

theorem dc_eq {m : ℕ} (F : (Fin (m + 1) → Y) → ℝ) (y : Fin (m + 2) → Y) :
    dc F y = ∑ i : Fin (m + 2), (-1 : ℝ) ^ (i : ℕ) * F (fun l => y (fc i l)) := by
  simp only [dc, succAbove_eq_fc]

theorem dc_smul {m : ℕ} (r : ℝ) (F : (Fin (m + 1) → Y) → ℝ) : dc (r • F) = r • dc F := by
  funext y; simp [dc, Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring

theorem dc_sub {m : ℕ} (F G : (Fin (m + 1) → Y) → ℝ) : dc (F - G) = dc F - dc G := by
  funext y; simp [dc, mul_sub, Finset.sum_sub_distrib]

private theorem fc_fc_eq_fc_fc_pred_of_lt {n : ℕ} (i j : ℕ) (hji : j < i) (l : Fin n) :
    (fc i (fc j l) : Fin (n + 2)) = fc j (fc (i - 1) l) := by
  apply Fin.ext
  simp only [fc_val]
  split_ifs <;> omega

theorem dc_dc {m : ℕ} (F : (Fin (m + 1) → Y) → ℝ) : dc (dc F) = 0 := by
  funext y
  rw [Pi.zero_apply, dc_eq]
  simp only [dc_eq, Finset.mul_sum]
  rw [← Finset.sum_product' (Finset.univ : Finset (Fin (m + 1 + 2)))
    (Finset.univ : Finset (Fin (m + 2)))
    (fun i j => (-1 : ℝ) ^ (i : ℕ) * ((-1 : ℝ) ^ (j : ℕ) * F (fun l => y (fc i (fc j l)))))]
  refine Finset.sum_involution (fun p _ => if h : (p.2 : ℕ) < (p.1 : ℕ) then
      ((⟨p.2, by have := p.1.isLt; have := p.2.isLt; omega⟩ : Fin (m + 1 + 2)),
        (⟨p.1 - 1, by have := p.1.isLt; have := p.2.isLt; omega⟩ : Fin (m + 2)))
    else ((⟨p.2 + 1, by have := p.1.isLt; have := p.2.isLt; omega⟩ : Fin (m + 1 + 2)),
      (⟨p.1, by have := p.1.isLt; have := p.2.isLt; omega⟩ : Fin (m + 2)))) ?_ ?_ ?_ ?_
  · intro p _
    split_ifs with h
    · simp only [Fin.val_mk, fc_fc_eq_fc_fc_pred_of_lt _ _ h]
      obtain ⟨t, ht⟩ : ∃ t, (p.1 : ℕ) = t + 1 := ⟨p.1 - 1, by omega⟩
      simp only [ht, Nat.add_sub_cancel, pow_succ]
      ring
    · simp only [Fin.val_mk, fc_fc_eq_fc_fc_pred_of_lt ((p.2 : ℕ) + 1) p.1 (by omega), Nat.add_sub_cancel,
        pow_succ]
      ring
  · intro p _ _
    split_ifs with h
    · intro he
      rw [Prod.ext_iff, Fin.ext_iff, Fin.ext_iff] at he
      simp only [Fin.val_mk] at he
      omega
    · intro he
      rw [Prod.ext_iff, Fin.ext_iff, Fin.ext_iff] at he
      simp only [Fin.val_mk] at he
      omega
  · intro p _
    simp
  · intro p _
    obtain ⟨i, j⟩ := p
    by_cases h : (j : ℕ) < (i : ℕ)
    · have h' : ¬ ((i : ℕ) - 1 < (j : ℕ)) := by omega
      simp only [h, h', dif_pos, dif_neg, not_false_eq_true, Prod.mk.injEq, Fin.ext_iff, Fin.val_mk]
      exact ⟨by omega, trivial⟩
    · have h' : (i : ℕ) < (j : ℕ) + 1 := by omega
      simp only [h, h', dif_pos, dif_neg, not_false_eq_true, Prod.mk.injEq, Fin.ext_iff, Fin.val_mk]
      exact ⟨trivial, by omega⟩

end PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

end
end

noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

variable {P Q : Type} [Group P] [Group Q]

abbrev Bi (P Q : Type) (a b : ℕ) : Type := (Fin a → Q) → (Fin b → P) → ℝ

def dh {a b : ℕ} (F : Bi P Q (a + 1) b) : Bi P Q (a + 2) b := fun x y => dc (fun x' => F x' y) x

def dv {a b : ℕ} (F : Bi P Q a (b + 1)) : Bi P Q a (b + 2) := fun x y => dc (F x) y

def PInv (pr : P →* Q) {a b : ℕ} (F : Bi P Q a b) : Prop :=
  ∀ (g : P) x y, F (fun i => pr g * x i) (fun j => g * y j) = F x y

def Ru (u : Q) {a b : ℕ} (F : Bi P Q a b) : Bi P Q a b := fun x y => F (fun i => x i * u) y

def Rt (t : P) {a b : ℕ} (F : Bi P Q a b) : Bi P Q a b := fun x y => F x (fun j => y j * t)

def Tc (t : P) {a b : ℕ} (F : Bi P Q a b) : Bi P Q a b := fun x y => F x (fun j => t⁻¹ * y j * t)

def Hv (t : P) {a b : ℕ} (F : Bi P Q a (b + 1)) : Bi P Q a b :=
  fun x y => PrismSpan.prism (fun p => p * t) (F x) y

def RuL (u : Q) (a b : ℕ) : Module.End ℝ (Bi P Q a b) where
  toFun := Ru u
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def TcL (t : P) (a b : ℕ) : Module.End ℝ (Bi P Q a b) where
  toFun := Tc t
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def cat {a c : ℕ} (x : Fin a → Q) (z : Fin c → Q) (n : ℕ) : Fin n → Q := fun i =>
  if h : (i : ℕ) < a then x ⟨i, h⟩ else if h' : (i : ℕ) - a < c then z ⟨(i : ℕ) - a, h'⟩ else 1

def zz (pr : P →* Q) {n : ℕ} (b : (Fin n → Q) → ℝ) (a c : ℕ) : Bi P Q a c :=
  fun x y => b (cat x (fun j => pr (y j)) n)

def Wtop (pr : P →* Q) {n : ℕ} (b : (Fin n → Q) → ℝ) : Bi P Q 1 n := fun _ y => b (fun j => pr (y j))

def QC {n : ℕ} (b : (Fin (n + 1) → Q) → ℝ) : Prop :=
  (∀ (g : Q) x, b (fun i => g * x i) = b x) ∧ dc b = 0

end PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.InclInj
noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.SplitAffineSpectral

def EvCob : Prop :=
  ∀ (G : Type) [Group G] (j : ℕ) (e : (Fin (j + 1) → G) → ℝ), Inv (MonoidHom.id G) e →
    ∀ z : Chn G (j + 1), IsCyc z → ev (MonoidHom.id G) (dC e) 1 z = 0

namespace GluingInclusion

set_option linter.unusedSectionVars false

variable (L : Type) [Field L] [NumberField L] (n r : ℕ)

end GluingInclusion

end PositivityTheory.KB.SplitAffineSpectral

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.CoreSteps
noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

def SplitA : Prop :=
  ∀ (P Q : Type) [Group P] [Group Q] (pr : P →* Q) (q : ℕ) (b : (Fin (q + 2) → Q) → ℝ), dc b = 0 →
    Wtop pr b = dv (zz pr b 1 (q + 1))

def SplitS : Prop :=
  ∀ (P Q : Type) [Group P] [Group Q] (pr : P →* Q) (p q : ℕ) (b : (Fin (p + q + 3) → Q) → ℝ), dc b = 0 →
    dh (zz pr b (p + 1) (q + 2)) = (-1 : ℝ) ^ (p + 1) • dv (zz pr b (p + 2) (q + 1))

def SplitB : Prop :=
  ∀ (P Q : Type) [Group P] [Group Q] (pr : P →* Q) (N : ℕ) (b : (Fin (N + 2) → Q) → ℝ), dc b = 0 →
    dh (zz pr b (N + 1) 1) = (-1 : ℝ) ^ (N + 1) • (fun x _ => b x : Bi P Q (N + 2) 1)

def ZInv : Prop :=
  ∀ (P Q : Type) [Group P] [Group Q] (pr : P →* Q) (n a c : ℕ) (b : (Fin n → Q) → ℝ), a + c = n →
    (∀ (g : Q) x, b (fun i => g * x i) = b x) → PInv pr (zz pr b a c)

def E2VanishingFirstColumn : Prop :=
  ∀ (P Q : Type) [Group P] [Group Q] (pr : P →* Q) (s : Q →* P), (∀ g, pr (s g) = g) →
    ∀ u : Q, (∀ g, g * u = u * g) → ∀ m : ℕ, ColPoly pr s u m → ∀ q : ℕ, q + 1 ≤ m →
    ∀ x : Bi P Q 1 (q + 2), PInv pr x → dv x = 0 → dh x = 0 →
      ∃ e : Bi P Q 1 (q + 1), PInv pr e ∧ x = dv e

def E2VanishingOtherColumns : Prop :=
  ∀ (P Q : Type) [Group P] [Group Q] (pr : P →* Q) (s : Q →* P), (∀ g, pr (s g) = g) →
    ∀ u : Q, (∀ g, g * u = u * g) → ∀ m : ℕ, ColPoly pr s u m → ∀ p q : ℕ, q + 1 ≤ m →
    ∀ x : Bi P Q (p + 2) (q + 2), PInv pr x → dv x = 0 → dh x = 0 →
      ∃ (w : Bi P Q (p + 1) (q + 2)) (e : Bi P Q (p + 2) (q + 1)),
        PInv pr w ∧ dv w = 0 ∧ PInv pr e ∧ x = dh w + dv e

end PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.RowExact
noncomputable section

open Finset

namespace PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

variable {P Q : Type} [Group P] [Group Q]

theorem dh_dh {a b : ℕ} (F : Bi P Q (a + 1) b) : dh (dh F) = 0 := by
  funext x y
  exact congrFun (dc_dc (fun x' => F x' y)) x

theorem dv_dv {a b : ℕ} (F : Bi P Q a (b + 1)) : dv (dv F) = 0 := by
  funext x y
  exact congrFun (dc_dc (F x)) y

theorem dh_dv {a b : ℕ} (F : Bi P Q (a + 1) (b + 1)) : dh (dv F) = dv (dh F) := by
  funext x y
  simp only [dh, dv, dc, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem dh_add {a b : ℕ} (F G : Bi P Q (a + 1) b) : dh (F + G) = dh F + dh G := by
  funext x y; simp only [dh, Pi.add_apply, dc, mul_add, Finset.sum_add_distrib]

theorem dh_sub {a b : ℕ} (F G : Bi P Q (a + 1) b) : dh (F - G) = dh F - dh G := by
  funext x y
  exact congrFun (dc_sub (fun x' => F x' y) (fun x' => G x' y)) x

theorem dh_smul {a b : ℕ} (r : ℝ) (F : Bi P Q (a + 1) b) : dh (r • F) = r • dh F := by
  funext x y
  exact congrFun (dc_smul r (fun x' => F x' y)) x

theorem dv_sub {a b : ℕ} (F G : Bi P Q a (b + 1)) : dv (F - G) = dv F - dv G := by
  funext x y
  exact congrFun (dc_sub (F x) (G x)) y

theorem dv_smul {a b : ℕ} (r : ℝ) (F : Bi P Q a (b + 1)) : dv (r • F) = r • dv F := by
  funext x y
  exact congrFun (dc_smul r (F x)) y

section Inv

variable (pr : P →* Q)

theorem PInv.sub {a b : ℕ} {F G : Bi P Q a b} (hF : PInv pr F) (hG : PInv pr G) : PInv pr (F - G) := by
  intro g x y
  show F _ _ - G _ _ = F x y - G x y
  rw [hF g x y, hG g x y]

theorem PInv.smul {a b : ℕ} (r : ℝ) {F : Bi P Q a b} (hF : PInv pr F) : PInv pr (r • F) := by
  intro g x y
  show r * F _ _ = r * F x y
  rw [hF g x y]

theorem PInv.dh {a b : ℕ} {F : Bi P Q (a + 1) b} (hF : PInv pr F) : PInv pr (dh F) := by
  intro g x y
  unfold PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas.dh PositivityTheory.KB.SplitAffineSpectral.dc
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact hF g (fun j => x (i.succAbove j)) y

theorem PInv.dv {a b : ℕ} {F : Bi P Q a (b + 1)} (hF : PInv pr F) : PInv pr (dv F) := by
  intro g x y
  unfold PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas.dv PositivityTheory.KB.SplitAffineSpectral.dc
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact hF g x (fun j => y (i.succAbove j))

end Inv

theorem cons_mul {Z : Type} [Mul Z] {n : ℕ} (g a : Z) (x : Fin n → Z) :
    (fun i => g * (Fin.cons a x : Fin (n + 1) → Z) i) = Fin.cons (g * a) (fun i => g * x i) := by
  funext i; refine Fin.cases ?_ (fun k => ?_) i <;> simp

theorem row_exact (pr : P →* Q) {a b : ℕ} (F : Bi P Q (a + 2) (b + 1)) (hF : PInv pr F) (h : dh F = 0) :
    ∃ G : Bi P Q (a + 1) (b + 1), PInv pr G ∧ F = dh G := by
  have hcs : ∀ (c : Q) (u : Fin (a + 2) → Q) (k : Fin (a + 2)),
      (fun j => (Fin.cons c u : Fin (a + 3) → Q) (k.succ.succAbove j)) =
        Fin.cons c (fun j => u (k.succAbove j)) := by
    intro c u k
    funext j
    cases j using Fin.cases <;> simp [Fin.succ_succAbove_zero, Fin.succ_succAbove_succ]
  refine ⟨fun x y => F (Fin.cons (pr (y 0)) x) y, ?_, ?_⟩
  · intro g x y
    show F (Fin.cons (pr (g * y 0)) (fun i => pr g * x i)) (fun j => g * y j) = F (Fin.cons (pr (y 0)) x) y
    rw [map_mul, ← cons_mul]
    exact hF g _ y
  · funext x y
    have h0 := congrFun (congrFun h (Fin.cons (pr (y 0)) x)) y
    simp only [dh, dc] at h0
    rw [Fin.sum_univ_succ] at h0
    simp only [hcs] at h0
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero, Fin.cons_succ, Fin.val_succ,
      pow_succ, mul_neg_one, neg_mul, Finset.sum_neg_distrib] at h0
    show F x y = ∑ i : Fin (a + 2), (-1) ^ (i : ℕ) * F (Fin.cons (pr (y 0)) (fun j => x (i.succAbove j))) y
    have h1 : F x y + -∑ i : Fin (a + 2), (-1) ^ (i : ℕ) * F (Fin.cons (pr (y 0)) (fun j => x (i.succAbove j))) y = 0 := h0
    linarith

end PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

end
end
