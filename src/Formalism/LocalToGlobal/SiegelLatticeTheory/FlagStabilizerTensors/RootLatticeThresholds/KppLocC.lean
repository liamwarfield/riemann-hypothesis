module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppFrameW
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsKpp

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppLocS
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppLocG
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppLoc
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppIdx
noncomputable section

open Matrix Finset

namespace Formalism.L2.SG.Pf.KppIdx

open Formalism.MainNotions.ArithmeticCylinders Formalism.L2.SG.Pf.AllRowsKpp

variable {s kk r : ℕ}

def xI (hr : r = kk + 2 * s + 1) (a : Fin s) : Fin r := ⟨a.1, by omega⟩
def wI (hr : r = kk + 2 * s + 1) (i : Fin kk) : Fin r := ⟨s + i.1, by omega⟩
def zI (hr : r = kk + 2 * s + 1) : Fin r := ⟨s + kk, by omega⟩
def yI (hr : r = kk + 2 * s + 1) (a : Fin s) : Fin r := ⟨s + kk + 1 + a.1, by omega⟩

theorem kind_cases (hr : r = kk + 2 * s + 1) (j : Fin r) :
    (∃ a, j = xI hr a) ∨ (∃ i, j = wI hr i) ∨ j = zI hr ∨ ∃ a, j = yI hr a := by
  rcases lt_or_ge j.1 s with h | h
  · exact Or.inl ⟨⟨j.1, h⟩, Fin.ext rfl⟩
  rcases lt_or_ge j.1 (s + kk) with h' | h'
  · exact Or.inr (Or.inl ⟨⟨j.1 - s, by omega⟩, Fin.ext (by show j.1 = s + (j.1 - s); omega)⟩)
  rcases eq_or_lt_of_le h' with h'' | h''
  · exact Or.inr (Or.inr (Or.inl (Fin.ext (by show j.1 = s + kk; omega))))
  · exact Or.inr (Or.inr (Or.inr ⟨⟨j.1 - (s + kk + 1), by omega⟩,
      Fin.ext (by show j.1 = s + kk + 1 + (j.1 - (s + kk + 1)); omega)⟩))

variable {g : ℕ}

theorem jPred_of (hr : r = kk + 2 * s + 1) {N : Matrix (Fin r) (Fin r) (ZMod g)}
    (hlow : ∀ a b : Fin r, b < a → N a b = 0) (hdiag : ∀ a, N a a = 1) (hwz : ∀ i, N (wI hr i) (zI hr) = 0) :
    JPred kk s N := by
  refine ⟨fun a b => ⟨hlow a b, fun h => h ▸ hdiag a⟩, fun a ha1 ha2 => ?_⟩
  unfold entN
  rw [dite_eq_left ⟨by omega, by omega⟩]
  have := hwz ⟨a - s, by omega⟩
  simpa only [wI, zI, Nat.add_sub_of_le ha1] using this

theorem low_of {N : Matrix (Fin r) (Fin r) (ZMod g)} (hJ : JPred kk s N) (a b : Fin r) (h : b < a) : N a b = 0 :=
  (hJ.1 a b).1 h

theorem diag_of {N : Matrix (Fin r) (Fin r) (ZMod g)} (hJ : JPred kk s N) (a : Fin r) : N a a = 1 :=
  (hJ.1 a a).2 rfl

theorem inv_super {N N' : Matrix (Fin r) (Fin r) (ZMod g)} (hJ : JPred kk s N) (hJ' : JPred kk s N')
    (h1 : N * N' = 1) (i : ℕ) (hi : i + 1 < r) : entN N' i (i + 1) = -entN N i (i + 1) := by
  have e := congrFun (congrFun h1 ⟨i, by omega⟩) ⟨i + 1, hi⟩
  rw [Matrix.mul_apply, Matrix.one_apply_ne (by intro h; have := congrArg Fin.val h; simp at this)] at e
  have hne : (⟨i, by omega⟩ : Fin r) ≠ ⟨i + 1, hi⟩ := by intro h; have := congrArg Fin.val h; simp at this
  rw [Finset.sum_eq_add (⟨i, by omega⟩ : Fin r) ⟨i + 1, hi⟩ hne (fun c _ hc => ?_) (by simp) (by simp)] at e
  · rw [diag_of hJ, diag_of hJ', one_mul, mul_one] at e
    unfold entN
    rw [dite_eq_left ⟨by omega, hi⟩, dite_eq_left ⟨by omega, hi⟩]
    linear_combination e
  · rcases lt_or_gt_of_ne (show c.1 ≠ i from fun h => hc.1 (Fin.ext h)) with h | h
    · rw [low_of hJ _ _ (show c < ⟨i, by omega⟩ from h), zero_mul]
    · have : i + 1 < c.1 := by
        rcases lt_or_gt_of_ne (show c.1 ≠ i + 1 from fun h => hc.2 (Fin.ext h)) with h' | h'
        · omega
        · exact h'
      rw [low_of hJ' _ _ (show (⟨i + 1, hi⟩ : Fin r) < c from this), mul_zero]

def dN (s kk : ℕ) (ob : Bool) (j : ℕ) : ZMod g :=
  if s + kk + 1 ≤ j then (-1) ^ (j - (s + kk + 1))
  else if ob = false ∧ s ≤ j ∧ j < s + kk then (-1) ^ (j - s) else 1

theorem dN_sq (ob : Bool) (j : ℕ) : dN (g := g) s kk ob j * dN s kk ob j = 1 := by
  unfold dN
  split_ifs <;> simp [← pow_add, ← two_mul, pow_mul]

theorem index_diag_isotropic (ob : Bool) {j : ℕ} (h : j < s) : dN (g := g) s kk ob j = 1 := by
  unfold dN; rw [if_neg (by omega), if_neg (fun h' => absurd h'.2.1 (by omega))]

theorem dN_wt {j : ℕ} (h1 : s ≤ j) (h2 : j < s + kk) : dN (g := g) s kk true j = 1 := by
  unfold dN; rw [if_neg (by omega), if_neg (fun h' => absurd h'.1 (by simp))]

theorem dN_wf {j : ℕ} (h1 : s ≤ j) (h2 : j < s + kk) : dN (g := g) s kk false j = (-1) ^ (j - s) := by
  unfold dN; rw [if_neg (by omega), if_pos ⟨rfl, h1, h2⟩]

theorem dN_add_eq_one (ob : Bool) : dN (g := g) s kk ob (s + kk) = 1 := by
  unfold dN; rw [if_neg (by omega), if_neg (fun h' => absurd h'.2.2 (by omega))]

theorem dN_y (ob : Bool) {j : ℕ} (h : s + kk + 1 ≤ j) : dN (g := g) s kk ob j = (-1) ^ (j - (s + kk + 1)) := by
  unfold dN; rw [if_pos h]

theorem neg_one_sq (i : ℕ) : ((-1 : ZMod g) ^ i) * (-1) ^ i = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]; simp

def dM (s kk : ℕ) (ob : Bool) : Matrix (Fin r) (Fin r) (ZMod g) := Matrix.diagonal fun j => dN s kk ob j.1

theorem dM_sq (ob : Bool) : dM (r := r) (g := g) s kk ob * dM s kk ob = 1 := by
  rw [dM, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext j
  exact dN_sq ob j.1

theorem entN_conj (ob : Bool) (N : Matrix (Fin r) (Fin r) (ZMod g)) (a b : ℕ) :
    entN (dM s kk ob * N * dM s kk ob) a b = dN s kk ob a * entN N a b * dN s kk ob b := by
  unfold entN
  split_ifs with h
  · simp [dM, Matrix.diagonal_mul, Matrix.mul_diagonal]
  · simp

theorem jPred_conj (hr : r = kk + 2 * s + 1) (ob : Bool) {N : Matrix (Fin r) (Fin r) (ZMod g)}
    (hJ : JPred kk s N) : JPred kk s (dM s kk ob * N * dM s kk ob) := by
  refine jPred_of hr (fun a b h => ?_) (fun a => ?_) (fun i => ?_)
  · simp only [dM, Matrix.diagonal_mul, Matrix.mul_diagonal]
    rw [low_of hJ a b h]; ring
  · simp only [dM, Matrix.diagonal_mul, Matrix.mul_diagonal]
    rw [diag_of hJ a, mul_one]
    exact dN_sq ob a.1
  · have := (hJ.2 (s + i.1) (by omega) (by omega))
    unfold entN at this
    rw [dite_eq_left ⟨by omega, by omega⟩] at this
    simp only [dM, Matrix.diagonal_mul, Matrix.mul_diagonal]
    have e : N (wI hr i) (zI hr) = 0 := this
    rw [e]; ring

theorem sum_range_pred (f : ℕ → ZMod g) (n : ℕ) :
    ∑ a ∈ range n, (if a + 1 < n then f a else 0) = ∑ a ∈ range (n - 1), f a := by
  cases n with
  | zero => simp
  | succ t =>
    rw [Finset.sum_range_succ, if_neg (by omega), add_zero, Nat.add_sub_cancel]
    exact Finset.sum_congr rfl fun a ha => by rw [Finset.mem_range] at ha; rw [if_pos (by omega)]

theorem sum_range_last (c : ZMod g) (n : ℕ) :
    ∑ a ∈ range n, (if a + 1 < n then 0 else c) = if 1 ≤ n then c else 0 := by
  cases n with
  | zero => simp
  | succ t =>
    rw [Finset.sum_range_succ, if_neg (by omega), if_pos (by omega)]
    rw [Finset.sum_eq_zero fun a ha => by rw [Finset.mem_range] at ha; rw [if_pos (by omega)], zero_add]

theorem phi_key (hr : r = kk + 2 * s + 1) (ob : Bool) {N N' : Matrix (Fin r) (Fin r) (ZMod g)}
    (hinv : ∀ i, i + 1 < r → entN N' i (i + 1) = -entN N i (i + 1)) :
    phiJ kk s (dM s kk ob * N * dM s kk ob) =
      (∑ a ∈ range s, (if a + 1 < s then entN N a (a + 1) + entN N' (s + kk + 1 + (s - 2 - a)) (s + kk + 1 + (s - 1 - a))
        else entN N a (s + kk) - entN N' (s + kk) (s + kk + 1))) +
      ∑ i ∈ range kk, (if i + 1 < kk then (if ob then entN N (s + i) (s + i + 1)
        else entN N' (s + (kk - 2 - i)) (s + (kk - 1 - i))) else 0) := by
  have split1 : ∀ a ∈ range s, (if a + 1 < s then entN N a (a + 1) + entN N' (s + kk + 1 + (s - 2 - a)) (s + kk + 1 + (s - 1 - a))
        else entN N a (s + kk) - entN N' (s + kk) (s + kk + 1)) =
      (if a + 1 < s then entN N a (a + 1) else 0) +
      (if a + 1 < s then entN N' (s + kk + 1 + (s - 2 - a)) (s + kk + 1 + (s - 1 - a)) else 0) +
      (if a + 1 < s then 0 else entN N (s - 1) (s + kk) - entN N' (s + kk) (s + kk + 1)) := by
    intro a ha
    rw [Finset.mem_range] at ha
    split_ifs with h
    · ring
    · have : a = s - 1 := by omega
      subst this; ring
  rw [Finset.sum_congr rfl split1, Finset.sum_add_distrib, Finset.sum_add_distrib, sum_range_pred, sum_range_pred,
    sum_range_last, sum_range_pred (fun i => if ob then entN N (s + i) (s + i + 1)
        else entN N' (s + (kk - 2 - i)) (s + (kk - 1 - i))) kk]

  have ry : ∑ a ∈ range (s - 1), entN N' (s + kk + 1 + (s - 2 - a)) (s + kk + 1 + (s - 1 - a)) =
      -∑ i ∈ range (s - 1), entN N (s + kk + 1 + i) (s + kk + 2 + i) := by
    rw [← Finset.sum_range_reflect, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.mem_range] at ha
    have e1 : s + kk + 1 + (s - 2 - (s - 1 - 1 - a)) = s + kk + 1 + a := by omega
    have e2 : s + kk + 1 + (s - 1 - (s - 1 - 1 - a)) = s + kk + 1 + a + 1 := by omega
    rw [e1, e2, hinv _ (by omega), show s + kk + 1 + a + 1 = s + kk + 2 + a by omega]
  have rw' : ∑ i ∈ range (kk - 1), (if ob then entN N (s + i) (s + i + 1)
        else entN N' (s + (kk - 2 - i)) (s + (kk - 1 - i))) =
      (if ob then 1 else -1) * ∑ a ∈ range (kk - 1), entN N (s + a) (s + a + 1) := by
    cases ob
    · simp only [Bool.false_eq_true, if_false, neg_one_mul]
      rw [← Finset.sum_range_reflect, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [Finset.mem_range] at ha
      have e1 : s + (kk - 2 - (kk - 1 - 1 - a)) = s + a := by omega
      have e2 : s + (kk - 1 - (kk - 1 - 1 - a)) = s + a + 1 := by omega
      rw [e1, e2, hinv _ (by omega)]
    · simp
  rw [ry, rw']
  unfold phiJ
  simp only [entN_conj]

  have hx : ∀ i ∈ range (s - 1), dN (g := g) s kk ob i * entN N i (i + 1) * dN s kk ob (i + 1) = entN N i (i + 1) := by
    intro i hi; rw [Finset.mem_range] at hi
    rw [index_diag_isotropic ob (by omega), index_diag_isotropic ob (by omega)]; ring
  have hy : ∀ i ∈ range (s - 1), dN (g := g) s kk ob (s + kk + 1 + i) * entN N (s + kk + 1 + i) (s + kk + 2 + i) *
      dN s kk ob (s + kk + 2 + i) = -entN N (s + kk + 1 + i) (s + kk + 2 + i) := by
    intro i hi
    rw [dN_y ob (by omega), dN_y ob (by omega)]
    have e1 : s + kk + 1 + i - (s + kk + 1) = i := by omega
    have e2 : s + kk + 2 + i - (s + kk + 1) = i + 1 := by omega
    rw [e1, e2, pow_succ]
    linear_combination (-(entN N (s + kk + 1 + i) (s + kk + 2 + i))) * neg_one_sq (g := g) i
  have hw : ∀ a ∈ range (kk - 1), dN (g := g) s kk ob (s + a) * entN N (s + a) (s + a + 1) * dN s kk ob (s + a + 1) =
      (if ob then 1 else -1) * entN N (s + a) (s + a + 1) := by
    intro a ha; rw [Finset.mem_range] at ha
    cases ob
    · rw [dN_wf (by omega) (by omega), dN_wf (by omega) (by omega)]
      have e1 : s + a - s = a := by omega
      have e2 : s + a + 1 - s = a + 1 := by omega
      rw [e1, e2, pow_succ]
      simp only [Bool.false_eq_true, if_false]
      linear_combination (-(entN N (s + a) (s + a + 1))) * neg_one_sq (g := g) a
    · rw [dN_wt (by omega) (by omega), dN_wt (by omega) (by omega)]
      simp
  rw [Finset.sum_congr rfl hx, Finset.sum_congr rfl hy, Finset.sum_congr rfl hw, ← Finset.mul_sum]
  by_cases hs : 1 ≤ s
  · rw [if_pos hs, if_pos hs]
    have h1 : dN (g := g) s kk ob (s - 1) = 1 := index_diag_isotropic ob (by omega)
    have h2 : dN (g := g) s kk ob (s + kk) = 1 := dN_add_eq_one ob
    have h3 : dN (g := g) s kk ob (s + kk + 1) = 1 := by rw [dN_y ob le_rfl]; simp
    rw [h1, h2, h3, hinv _ (by omega), Finset.sum_neg_distrib]
    ring
  · rw [if_neg hs, if_neg hs]
    have : s - 1 = 0 := by omega
    rw [this]
    simp

end Formalism.L2.SG.Pf.KppIdx
end
end

noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.KppLoc

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin Formalism.L2.SG.Pf.RedBasicsPf
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.Pf.AllRowsRedKerA Formalism.L2.SG.Pf.KppRedW Formalism.L2.SG.Pf.KppFrameW Formalism.L2.SG.Pf.KppIdx

section Gen

variable {I : AutInst} {w : HeightOneSpectrum (𝓞 I.E)} {g : ℕ}

theorem zmod_Wq (hg : (g : 𝓞 I.E) ∈ w.asIdeal) {c : I.E ⊗[I.F] Af I.F} (h : ZMod' I g c) : c ∈ Wq I w := by
  obtain ⟨t, ht, rfl⟩ := h
  have : (g : I.E ⊗[I.F] Af I.F) ∈ Wq I w := by
    have := iE_mem (I := I) hg
    simpa [iE] using this
  exact Wq_mul' this ht

theorem zmod_sg {c : I.E ⊗[I.F] Af I.F} (h : ZMod' I g c) : ZMod' I g (sg I c) := by
  obtain ⟨t, ht, rfl⟩ := h
  exact ⟨sg I t, DictLat.sigR_int I ht, by rw [map_mul, sg_natCast]⟩

theorem mL_le (hg : (g : 𝓞 I.E) ∈ w.asIdeal) : mL I g ≤ Lq I w := by
  unfold mL
  rw [Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  have := smul_mem I w hg hx
  simpa using this

theorem hhat_neg_left (u v : Fin I.n → I.E ⊗[I.F] Af I.F) : hhat I (-u) v = -hhat I u v := by
  have := hhat_sub_left I 0 u v
  rwa [zero_sub, DictLat.hhat_zero_left, zero_sub] at this

theorem pair_right (hg : (g : 𝓞 I.E) ∈ w.asIdeal) {u : Fin I.n → I.E ⊗[I.F] Af I.F} (hu : u ∈ I.Lf)
    {S : Set (VA I)} (hS : ∀ s ∈ S, hhat I u s ∈ Wq I w) {v : VA I} (hv : InMod I g S v) : hhat I u v ∈ Wq I w := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
  clear hv
  rw [DictLat.hhat_add_right]
  refine add_mem ?_ (hhat_Lq_right hu (mL_le hg hz))
  induction hy using Submodule.span_induction with
  | mem s hs => exact hS s hs
  | zero => rw [DictLat.hhat_zero_right]; exact zero_mem _
  | add a b _ _ ha hb => rw [DictLat.hhat_add_right]; exact add_mem ha hb
  | smul r a _ ha =>
    show hhat I u ((r : I.E ⊗[I.F] Af I.F) • a) ∈ Wq I w
    rw [DictLat.hhat_smul_right]; exact Wq_mul ha r.2

theorem pair_left (hg : (g : 𝓞 I.E) ∈ w.asIdeal) {v : Fin I.n → I.E ⊗[I.F] Af I.F} (hv : v ∈ I.Lf)
    {S : Set (VA I)} (hS : ∀ s ∈ S, hhat I s v ∈ Wq I w) {u : VA I} (hu : InMod I g S u) : hhat I u v ∈ Wq I w := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hu
  clear hu
  rw [DictLat.hhat_add_left]
  refine add_mem ?_ ?_
  · induction hy using Submodule.span_induction with
    | mem s hs => exact hS s hs
    | zero => rw [DictLat.hhat_zero_left]; exact zero_mem _
    | add a b _ _ ha hb => rw [DictLat.hhat_add_left]; exact add_mem ha hb
    | smul r a _ ha =>
      show hhat I ((r : I.E ⊗[I.F] Af I.F) • a) v ∈ Wq I w
      rw [DictLat.hhat_smul_left]; exact Wq_mul ha (DictLat.sigR_int I r.2)
  · have hgW : (g : I.E ⊗[I.F] Af I.F) ∈ Wq I w := by
      have := iE_mem (I := I) hg
      simpa [iE] using this
    unfold mL at hz
    induction hz using Submodule.span_induction with
    | mem s hs =>
      obtain ⟨x, hx, rfl⟩ := hs
      rw [DictLat.hhat_smul_left, sg_natCast]
      exact Wq_mul' hgW (dual_hat_integral I x hx v hv)
    | zero => rw [DictLat.hhat_zero_left]; exact zero_mem _
    | add a b _ _ ha hb => rw [DictLat.hhat_add_left]; exact add_mem ha hb
    | smul r a _ ha =>
      show hhat I ((r : I.E ⊗[I.F] Af I.F) • a) v ∈ Wq I w
      rw [DictLat.hhat_smul_left]; exact Wq_mul ha (DictLat.sigR_int I r.2)

theorem dir_col (hg : (g : 𝓞 I.E) ∈ w.asIdeal) {x : I.Gf} {u v : VA I} (hu : u ∈ I.Lf) {S : Set (VA I)}
    (hS : ∀ s ∈ S, hhat I u s ∈ Wq I w) (hx : InMod I g S ((I.fmat x - 1) *ᵥ v)) :
    hhat I u (I.fmat x *ᵥ v) - hhat I u v ∈ Wq I w := by
  have := pair_right hg hu hS hx
  rwa [Matrix.sub_mulVec, Matrix.one_mulVec, hhat_sub_right] at this

theorem dual_col (hg : (g : 𝓞 I.E) ∈ w.asIdeal) {x : I.Gf} {u v : VA I} (hv : v ∈ I.Lf) {S : Set (VA I)}
    (hS : ∀ s ∈ S, hhat I s v ∈ Wq I w) (hx : InMod I g S ((I.fmat x⁻¹ - 1) *ᵥ u)) :
    hhat I u (I.fmat x *ᵥ v) - hhat I u v ∈ Wq I w := by
  have h1 : hhat I u (I.fmat x *ᵥ v) = hhat I (I.fmat x⁻¹ *ᵥ u) v := by
    have := hhat_fmat I x (I.fmat x⁻¹ *ᵥ u) v
    rw [Matrix.mulVec_mulVec, ← fmat_mul, mul_inv_cancel, fmat_one, Matrix.one_mulVec] at this
    exact this
  have := pair_left hg hv hS hx
  rwa [Matrix.sub_mulVec, Matrix.one_mulVec, hhat_sub_left, ← h1] at this

variable {p : ℕ} {r : ℕ}

theorem cong_dir (hg : (g : 𝓞 I.E) ∈ w.asIdeal) {fr frd : Fin r → VA I} (hfrd : ∀ i, frd i ∈ I.Lf)
    (hgr : GramW w fr frd) {x : I.Gf} (i j : Fin r) {S : Set (VA I)}
    (hS : ∀ s ∈ S, ∃ j', s = fr j' ∧ j' ≠ i) (hx : InMod I g S ((I.fmat x - 1) *ᵥ fr j)) :
    CongW (w := w) p (hhat I (frd i) (I.fmat x *ᵥ fr j)) (if i = j then 1 else 0) := by
  have h1 := dir_col hg (hfrd i) (fun s hs => by
    obtain ⟨j', rfl, hj'⟩ := hS s hs
    have := hgr i j'
    rwa [if_neg (Ne.symm hj'), sub_zero] at this) hx
  refine congW_of_sub ?_ h1
  refine congW_of_sub (t := ((if i = j then 1 else 0 : ℤ) : I.E ⊗[I.F] Af I.F)) ?_ ?_
  · have := congW_intCast (I := I) (w := w) (p := p) (if i = j then 1 else 0)
    convert this using 2
    split_ifs <;> simp
  · have := hgr i j
    convert this using 2
    split_ifs <;> simp

theorem cong_dual (hg : (g : 𝓞 I.E) ∈ w.asIdeal) {fr frd : Fin r → VA I} (hfr : ∀ j, fr j ∈ I.Lf)
    (hgr : GramW w fr frd) {x : I.Gf} (i j : Fin r) {S : Set (VA I)}
    (hS : ∀ s ∈ S, ∃ i', s = frd i' ∧ i' ≠ j) (hx : InMod I g S ((I.fmat x⁻¹ - 1) *ᵥ frd i)) :
    CongW (w := w) p (hhat I (frd i) (I.fmat x *ᵥ fr j)) (if i = j then 1 else 0) := by
  have h1 := dual_col hg (hfr j) (fun s hs => by
    obtain ⟨i', rfl, hi'⟩ := hS s hs
    have := hgr i' j
    rwa [if_neg hi', sub_zero] at this) hx
  refine congW_of_sub ?_ h1
  refine congW_of_sub (t := ((if i = j then 1 else 0 : ℤ) : I.E ⊗[I.F] Af I.F)) ?_ ?_
  · have := congW_intCast (I := I) (w := w) (p := p) (if i = j then 1 else 0)
    convert this using 2
    split_ifs <;> simp
  · have := hgr i j
    convert this using 2
    split_ifs <;> simp

theorem inMod_neg {S : Set (VA I)} {v : VA I} (h : InMod I g S v) : InMod I g S (-v) := neg_mem h

end Gen

variable {D : D7} (X : HidaSetting D)

theorem hrD (D : D7) : D.R.r = D.R.k + 2 * D.R.rS + 1 := by
  unfold Ranks.r Ranks.rS
  obtain ⟨t, ht⟩ := D.R.m_even
  have := D.R.two_le_m
  omega

def fr (ob : Bool) (j : Fin D.R.r) : VA X.B.I :=
  if h1 : j.1 < D.R.rS then X.e0 ⟨j.1, h1⟩
  else if h2 : j.1 < D.R.rS + D.R.k then
    (if ob then X.bw ⟨j.1 - D.R.rS, by omega⟩ else X.bwd ⟨D.R.k - 1 - (j.1 - D.R.rS), by omega⟩)
  else if j.1 = D.R.rS + D.R.k then X.z0
  else if h4 : j.1 - (D.R.rS + D.R.k + 1) < D.R.rS then X.f0 ⟨D.R.rS - 1 - (j.1 - (D.R.rS + D.R.k + 1)), by omega⟩
  else 0

def frd (ob : Bool) (j : Fin D.R.r) : VA X.B.I :=
  if h1 : j.1 < D.R.rS then X.f0 ⟨j.1, h1⟩
  else if h2 : j.1 < D.R.rS + D.R.k then
    (if ob then X.bwd ⟨j.1 - D.R.rS, by omega⟩ else X.bw ⟨D.R.k - 1 - (j.1 - D.R.rS), by omega⟩)
  else if j.1 = D.R.rS + D.R.k then -X.z0
  else if h4 : j.1 - (D.R.rS + D.R.k + 1) < D.R.rS then X.e0 ⟨D.R.rS - 1 - (j.1 - (D.R.rS + D.R.k + 1)), by omega⟩
  else 0

def rv {n : ℕ} (a : Fin n) : Fin n := ⟨n - 1 - a.1, by omega⟩

theorem rv_rv {n : ℕ} (a : Fin n) : rv (rv a) = a := Fin.ext (by simp only [rv]; omega)

theorem frame_isotropic (ob : Bool) (a : Fin D.R.rS) : fr X ob (xI (hrD D) a) = X.e0 a := by
  unfold fr; rw [dite_eq_left (show (xI (hrD D) a).1 < D.R.rS from a.2)]; rfl

theorem fr_w (ob : Bool) (i : Fin D.R.k) : fr X ob (wI (hrD D) i) = if ob then X.bw i else X.bwd (rv i) := by
  unfold fr
  rw [dite_eq_right (show ¬ (wI (hrD D) i).1 < D.R.rS by simp [wI, rv]), dite_eq_left (show (wI (hrD D) i).1 < D.R.rS + D.R.k by simp [wI, rv])]
  congr 1 <;> congr 1 <;> ext <;> simp [wI, rv]

theorem frame_anisotropic (ob : Bool) : fr X ob (zI (hrD D)) = X.z0 := by
  unfold fr
  rw [dite_eq_right (show ¬ (zI (hrD D)).1 < D.R.rS by simp [zI] <;> omega),
    dite_eq_right (show ¬ (zI (hrD D)).1 < D.R.rS + D.R.k by simp [zI]), if_pos (by simp [zI])]

theorem fr_y (ob : Bool) (a : Fin D.R.rS) : fr X ob (yI (hrD D) a) = X.f0 (rv a) := by
  unfold fr
  rw [dite_eq_right (show ¬ (yI (hrD D) a).1 < D.R.rS by simp [yI, rv] <;> omega),
    dite_eq_right (show ¬ (yI (hrD D) a).1 < D.R.rS + D.R.k by simp [yI, rv] <;> omega), if_neg (by simp [yI, rv] <;> omega),
    dite_eq_left (show (yI (hrD D) a).1 - (D.R.rS + D.R.k + 1) < D.R.rS by simp [yI, rv])]
  congr 1; ext; simp [yI, rv]

theorem dual_frame_isotropic (ob : Bool) (a : Fin D.R.rS) : frd X ob (xI (hrD D) a) = X.f0 a := by
  unfold frd; rw [dite_eq_left (show (xI (hrD D) a).1 < D.R.rS from a.2)]; rfl

theorem frd_w (ob : Bool) (i : Fin D.R.k) : frd X ob (wI (hrD D) i) = if ob then X.bwd i else X.bw (rv i) := by
  unfold frd
  rw [dite_eq_right (show ¬ (wI (hrD D) i).1 < D.R.rS by simp [wI, rv]), dite_eq_left (show (wI (hrD D) i).1 < D.R.rS + D.R.k by simp [wI, rv])]
  congr 1 <;> congr 1 <;> ext <;> simp [wI, rv]

theorem dual_frame_anisotropic (ob : Bool) : frd X ob (zI (hrD D)) = -X.z0 := by
  unfold frd
  rw [dite_eq_right (show ¬ (zI (hrD D)).1 < D.R.rS by simp [zI] <;> omega),
    dite_eq_right (show ¬ (zI (hrD D)).1 < D.R.rS + D.R.k by simp [zI]), if_pos (by simp [zI])]

theorem frd_y (ob : Bool) (a : Fin D.R.rS) : frd X ob (yI (hrD D) a) = X.e0 (rv a) := by
  unfold frd
  rw [dite_eq_right (show ¬ (yI (hrD D) a).1 < D.R.rS by simp [yI, rv] <;> omega),
    dite_eq_right (show ¬ (yI (hrD D) a).1 < D.R.rS + D.R.k by simp [yI, rv] <;> omega), if_neg (by simp [yI, rv] <;> omega),
    dite_eq_left (show (yI (hrD D) a).1 - (D.R.rS + D.R.k + 1) < D.R.rS by simp [yI, rv])]
  congr 1; ext; simp [yI, rv]

end Formalism.L2.SG.Pf.KppLoc
end
end

noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.KppLoc

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin Formalism.L2.SG.Pf.RedBasicsPf
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.Pf.AllRowsRedKerA Formalism.L2.SG.Pf.KppRedW Formalism.L2.SG.Pf.KppFrameW Formalism.L2.SG.Pf.KppIdx

theorem ne_val {r : ℕ} {i j : Fin r} (h : i.1 ≠ j.1) : i ≠ j := fun e => h (congrArg Fin.val e)

theorem rv_inj {n : ℕ} {a b : Fin n} : rv a = rv b ↔ a = b :=
  ⟨fun h => by rw [← rv_rv a, h, rv_rv], fun h => h ▸ rfl⟩

theorem gram_of {I : AutInst} {w : HeightOneSpectrum (𝓞 I.E)} {u v : VA I} {P Q : Prop} [Decidable P] [Decidable Q]
    (h : hhat I u v - (if P then 1 else 0) ∈ Wq I w) (hPQ : P ↔ Q) :
    hhat I u v - (if Q then 1 else 0) ∈ Wq I w := by
  have e : (if P then (1 : I.E ⊗[I.F] Af I.F) else 0) = if Q then 1 else 0 := by
    by_cases hp : P
    · rw [if_pos hp, if_pos (hPQ.1 hp)]
    · rw [if_neg hp, if_neg (fun hq => hp (hPQ.2 hq))]
  rwa [e] at h

theorem gram_ne {I : AutInst} {w : HeightOneSpectrum (𝓞 I.E)} {u v : VA I} {Q : Prop} [Decidable Q]
    (h : hhat I u v ∈ Wq I w) (hQ : ¬ Q) : hhat I u v - (if Q then 1 else 0) ∈ Wq I w := by
  rwa [if_neg hQ, sub_zero]

variable {D : D7} (X : HidaSetting D)

theorem sg_hA (u v : VA X.B.I) : sg X.B.I (hA X.B.I u v) = hhat X.B.I v u := hhat_conj X.B.I u v

theorem fr_wt (i : Fin D.R.k) : fr X true (wI (hrD D) i) = X.bw i := by rw [fr_w]; rfl
theorem fr_wf (i : Fin D.R.k) : fr X false (wI (hrD D) i) = X.bwd (rv i) := by rw [fr_w]; rfl
theorem frd_wt (i : Fin D.R.k) : frd X true (wI (hrD D) i) = X.bwd i := by rw [frd_w]; rfl
theorem frd_wf (i : Fin D.R.k) : frd X false (wI (hrD D) i) = X.bw (rv i) := by rw [frd_w]; rfl

variable {w : HeightOneSpectrum (𝓞 X.B.I.E)}

theorem wq (hg : ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ w.asIdeal) {c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F}
    (h : ZMod' X.B.I X.B.g c) : c ∈ Wq X.B.I w := zmod_Wq hg h

theorem wqs (hg : ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ w.asIdeal) {c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F}
    (h : ZMod' X.B.I X.B.g c) : sg X.B.I c ∈ Wq X.B.I w := zmod_Wq hg (zmod_sg h)

theorem xI_inj {a b : Fin D.R.rS} : xI (hrD D) a = xI (hrD D) b ↔ a = b :=
  ⟨fun h => Fin.ext (by have := congrArg Fin.val h; simpa [xI, wI, yI] using this), fun h => h ▸ rfl⟩
theorem wI_inj {a b : Fin D.R.k} : wI (hrD D) a = wI (hrD D) b ↔ a = b :=
  ⟨fun h => Fin.ext (by have := congrArg Fin.val h; simpa [xI, wI, yI] using this), fun h => h ▸ rfl⟩
theorem yI_inj {a b : Fin D.R.rS} : yI (hrD D) a = yI (hrD D) b ↔ a = b :=
  ⟨fun h => Fin.ext (by have := congrArg Fin.val h; simpa [xI, wI, yI] using this), fun h => h ▸ rfl⟩

theorem gram (ob : Bool) (hg : ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ w.asIdeal)
    (hew : X.ew - (if ob then 1 else 0) ∈ Wq X.B.I w) (hsew : sg X.B.I X.ew - (if ob then 0 else 1) ∈ Wq X.B.I w) :
    GramW w (fr X ob) (frd X ob) := by
  intro i j
  have sg_ite : ∀ (P : Prop) [Decidable P],
      sg X.B.I (if P then (1 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) else 0) = if P then 1 else 0 := by
    intro P _; split_ifs <;> simp
  rcases kind_cases (hrD D) i with ⟨a, rfl⟩ | ⟨a, rfl⟩ | rfl | ⟨a, rfl⟩ <;>
  rcases kind_cases (hrD D) j with ⟨b, rfl⟩ | ⟨b, rfl⟩ | rfl | ⟨b, rfl⟩
  ·
    rw [dual_frame_isotropic, frame_isotropic]
    have h := wqs X hg ((X.gramIntegral b a).2.2)
    rw [map_sub, sg_hA, sg_ite] at h
    exact gram_of h (by rw [xI_inj]; exact eq_comm)
  ·
    refine gram_ne ?_ (ne_val (by simp [xI, wI, yI, zI] <;> omega))
    cases ob
    · rw [dual_frame_isotropic, fr_wf]; exact wq X hg ((X.weightVectorsIntegral (rv b)).2.2 a).2.2.2
    · rw [dual_frame_isotropic, fr_wt]; exact wq X hg ((X.weightVectorsIntegral b).2.2 a).2.1
  ·
    refine gram_ne ?_ (ne_val (by simp [xI, wI, yI, zI] <;> omega))
    rw [dual_frame_isotropic, frame_anisotropic]; exact wq X hg (X.formsAtZero.2 a).2
  ·
    refine gram_ne ?_ (ne_val (by simp [xI, wI, yI, zI] <;> omega))
    rw [dual_frame_isotropic, fr_y]; exact wq X hg (X.gramIntegral a (rv b)).2.1
  ·
    refine gram_ne ?_ (ne_val (by simp [xI, wI, yI, zI] <;> omega))
    cases ob
    · rw [frd_wf, frame_isotropic]; have := wqs X hg ((X.weightVectorsIntegral (rv a)).2.2 b).1; rwa [sg_hA] at this
    · rw [frd_wt, frame_isotropic]; have := wqs X hg ((X.weightVectorsIntegral a).2.2 b).2.2.1; rwa [sg_hA] at this
  ·
    cases ob
    · rw [frd_wf, fr_wf]
      simp only [Bool.false_eq_true, if_false] at hsew
      have h := wqs X hg (X.bw_dual (rv b) (rv a))
      rw [map_sub, sg_hA] at h
      by_cases hab : a = b
      · subst hab
        rw [if_pos rfl] at h ⊢
        have := add_mem h hsew
        convert this using 1; ring
      · rw [if_neg (fun h' => hab (rv_inj.1 h'.symm)), map_zero, sub_zero] at h
        exact gram_ne h (fun h' => hab (wI_inj.1 h'))
    · rw [frd_wt, fr_wt]
      simp only [if_true] at hew
      have h := wq X hg (X.bw_dual a b)
      by_cases hab : a = b
      · subst hab
        rw [if_pos rfl] at h ⊢
        change hhat X.B.I (X.bwd a) (X.bw a) - X.ew ∈ _ at h
        have := add_mem h hew
        convert this using 1; ring
      · rw [if_neg hab, sub_zero] at h
        exact gram_ne h (fun h' => hab (wI_inj.1 h'))
  ·
    refine gram_ne ?_ (ne_val (by simp [xI, wI, yI, zI] <;> omega))
    cases ob
    · rw [frd_wf, frame_anisotropic]; have := wqs X hg (X.weightVectorsIntegral (rv a)).1; rwa [sg_hA] at this
    · rw [frd_wt, frame_anisotropic]; have := wqs X hg (X.weightVectorsIntegral a).2.1; rwa [sg_hA] at this
  ·
    refine gram_ne ?_ (ne_val (by simp [xI, wI, yI, zI] <;> omega))
    cases ob
    · rw [frd_wf, fr_y]; have := wqs X hg ((X.weightVectorsIntegral (rv a)).2.2 (rv b)).2.1; rwa [sg_hA] at this
    · rw [frd_wt, fr_y]; have := wqs X hg ((X.weightVectorsIntegral a).2.2 (rv b)).2.2.2; rwa [sg_hA] at this
  ·
    refine gram_ne ?_ (ne_val (by simp [xI, wI, yI, zI] <;> omega))
    rw [dual_frame_anisotropic, frame_isotropic, hhat_neg_left]
    refine neg_mem ?_
    have := wqs X hg (X.formsAtZero.2 b).1; rwa [sg_hA] at this
  ·
    refine gram_ne ?_ (ne_val (by simp [xI, wI, yI, zI] <;> omega))
    cases ob
    · rw [dual_frame_anisotropic, fr_wf, hhat_neg_left]; exact neg_mem (wq X hg (X.weightVectorsIntegral (rv b)).2.1)
    · rw [dual_frame_anisotropic, fr_wt, hhat_neg_left]; exact neg_mem (wq X hg (X.weightVectorsIntegral b).1)
  ·
    rw [dual_frame_anisotropic, frame_anisotropic, hhat_neg_left, if_pos rfl]
    have := neg_mem (wq X hg X.formsAtZero.1)
    convert this using 1
    show -hhat X.B.I X.z0 X.z0 - 1 = -(hA X.B.I X.z0 X.z0 + 1)
    rw [show hA X.B.I X.z0 X.z0 = hhat X.B.I X.z0 X.z0 from rfl]; ring
  ·
    refine gram_ne ?_ (ne_val (by simp [xI, wI, yI, zI] <;> omega))
    rw [dual_frame_anisotropic, fr_y, hhat_neg_left]
    refine neg_mem ?_
    have := wqs X hg (X.formsAtZero.2 (rv b)).2; rwa [sg_hA] at this
  ·
    refine gram_ne ?_ (ne_val (by simp [xI, wI, yI, zI] <;> omega))
    rw [frd_y, frame_isotropic]; exact wq X hg (X.gramIntegral (rv a) b).1
  ·
    refine gram_ne ?_ (ne_val (by simp [xI, wI, yI, zI] <;> omega))
    cases ob
    · rw [frd_y, fr_wf]; exact wq X hg ((X.weightVectorsIntegral (rv b)).2.2 (rv a)).2.2.1
    · rw [frd_y, fr_wt]; exact wq X hg ((X.weightVectorsIntegral b).2.2 (rv a)).1
  ·
    refine gram_ne ?_ (ne_val (by simp [xI, wI, yI, zI] <;> omega))
    rw [frd_y, frame_anisotropic]; exact wq X hg (X.formsAtZero.2 (rv a)).1
  ·
    rw [frd_y, fr_y]
    exact gram_of (wq X hg (X.gramIntegral (rv a) (rv b)).2.2) (by rw [rv_inj, yI_inj])

end Formalism.L2.SG.Pf.KppLoc
end
end

noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.KppLoc

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin Formalism.L2.SG.Pf.RedBasicsPf
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.Pf.AllRowsRedKerA Formalism.L2.SG.Pf.KppRedW Formalism.L2.SG.Pf.KppFrameW Formalism.L2.SG.Pf.KppIdx
  Formalism.L2.SG.Pf.AllRowsKpp

variable {D : D7} (X : HidaSetting D)

theorem fr_L (ob : Bool) (j : Fin D.R.r) : fr X ob j ∈ X.B.I.Lf := by
  rcases kind_cases (hrD D) j with ⟨a, rfl⟩ | ⟨a, rfl⟩ | rfl | ⟨a, rfl⟩
  · rw [frame_isotropic]; exact (X.vectorsInLattice.1 a).1
  · cases ob
    · rw [fr_wf]; exact (X.vectorsInLattice.2.2 _).2
    · rw [fr_wt]; exact (X.vectorsInLattice.2.2 _).1
  · rw [frame_anisotropic]; exact X.vectorsInLattice.2.1
  · rw [fr_y]; exact (X.vectorsInLattice.1 _).2

theorem frd_L (ob : Bool) (j : Fin D.R.r) : frd X ob j ∈ X.B.I.Lf := by
  rcases kind_cases (hrD D) j with ⟨a, rfl⟩ | ⟨a, rfl⟩ | rfl | ⟨a, rfl⟩
  · rw [dual_frame_isotropic]; exact (X.vectorsInLattice.1 a).2
  · cases ob
    · rw [frd_wf]; exact (X.vectorsInLattice.2.2 _).1
    · rw [frd_wt]; exact (X.vectorsInLattice.2.2 _).2
  · rw [dual_frame_anisotropic]; exact neg_mem X.vectorsInLattice.2.1
  · rw [frd_y]; exact (X.vectorsInLattice.1 _).1

variable {w : HeightOneSpectrum (𝓞 X.B.I.E)} {p : ℕ}

theorem col (ob : Bool) (hg : ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ w.asIdeal)
    (hew : X.ew - (if ob then 1 else 0) ∈ Wq X.B.I w) (hsew : sg X.B.I X.ew - (if ob then 0 else 1) ∈ Wq X.B.I w)
    {x : X.B.I.Gf} (hx : x ∈ X.K2) (i j : Fin D.R.r)
    (hij : j.1 ≤ i.1 ∨ ((∃ l, i = wI (hrD D) l) ∧ j = zI (hrD D))) :
    CongW (w := w) p (hhat X.B.I (frd X ob i) (X.B.I.fmat x *ᵥ fr X ob j)) (if i = j then 1 else 0) := by
  have hc : K2cong X.B.I X.B.g X.e0 X.z0 X.bw x := hx.2
  have hci : K2cong X.B.I X.B.g X.e0 X.z0 X.bw x⁻¹ := ((Formalism.L2.SG.Pf.level_subgroup_character_unitary X).2.2.1 x hx).2
  have hgr := gram X ob hg hew hsew
  rcases kind_cases (hrD D) j with ⟨b, rfl⟩ | ⟨l, rfl⟩ | rfl | ⟨b, rfl⟩
  ·
    have hpos : b.1 ≤ i.1 := by
      rcases hij with h | ⟨-, h⟩
      · simpa [xI, wI, yI, zI] using h
      · exact absurd h (ne_val (by simp [xI, wI, yI, zI] <;> omega))
    refine cong_dir hg (frd_L X ob) hgr i (xI (hrD D) b) (S := X.e0 '' {c | c.1 < b.1}) ?_ ?_
    · rintro s ⟨c, hc', rfl⟩
      exact ⟨xI (hrD D) c, (frame_isotropic X ob c).symm, ne_val (by simp [xI, wI, yI, zI] at hc' ⊢; omega)⟩
    · rw [frame_isotropic]; exact hc.1 b
  ·
    have hpos : D.R.rS + l.1 ≤ i.1 := by
      rcases hij with h | ⟨-, h⟩
      · simpa [xI, wI, yI, zI] using h
      · exact absurd h (ne_val (by simp [xI, wI, yI, zI] <;> omega))
    cases ob
    ·
      rcases kind_cases (hrD D) i with ⟨a, rfl⟩ | ⟨l', rfl⟩ | rfl | ⟨a, rfl⟩
      · exfalso; simp [xI, wI, yI, zI] at hpos; omega
      · simp [xI, wI, yI, zI] at hpos
        refine cong_dual hg (fr_L X false) hgr (wI (hrD D) l') (wI (hrD D) l)
          (S := Set.range X.e0 ∪ X.bw '' {c | c.1 < (rv l').1}) ?_ ?_
        · rintro s (⟨c, rfl⟩ | ⟨c, hc', rfl⟩)
          · exact ⟨yI (hrD D) (rv c), by rw [frd_y, rv_rv], ne_val (by simp [xI, wI, yI, zI] <;> omega)⟩
          · exact ⟨wI (hrD D) (rv c), by rw [frd_wf, rv_rv], ne_val (by simp [xI, wI, yI, zI, rv] at hc' ⊢; omega)⟩
        · rw [frd_wf]; exact hci.2.2 (rv l')
      · refine cong_dual hg (fr_L X false) hgr (zI (hrD D)) (wI (hrD D) l) (S := Set.range X.e0) ?_ ?_
        · rintro s ⟨c, rfl⟩
          exact ⟨yI (hrD D) (rv c), by rw [frd_y, rv_rv], ne_val (by simp [xI, wI, yI, zI] <;> omega)⟩
        · rw [dual_frame_anisotropic, Matrix.mulVec_neg]; exact inMod_neg hci.2.1
      · refine cong_dual hg (fr_L X false) hgr (yI (hrD D) a) (wI (hrD D) l)
          (S := X.e0 '' {c | c.1 < (rv a).1}) ?_ ?_
        · rintro s ⟨c, -, rfl⟩
          exact ⟨yI (hrD D) (rv c), by rw [frd_y, rv_rv], ne_val (by simp [xI, wI, yI, zI] <;> omega)⟩
        · rw [frd_y]; exact hci.1 (rv a)
    ·
      refine cong_dir hg (frd_L X true) hgr i (wI (hrD D) l) (S := Set.range X.e0 ∪ X.bw '' {c | c.1 < l.1}) ?_ ?_
      · rintro s (⟨c, rfl⟩ | ⟨c, hc', rfl⟩)
        · exact ⟨xI (hrD D) c, (frame_isotropic X true c).symm, ne_val (by simp [xI, wI, yI, zI]; omega)⟩
        · exact ⟨wI (hrD D) c, (fr_wt X c).symm, ne_val (by simp [xI, wI, yI, zI] at hc' ⊢; omega)⟩
      · rw [fr_wt]; exact hc.2.2 l
  ·
    have hpos : D.R.rS ≤ i.1 := by
      rcases hij with h | ⟨⟨l, rfl⟩, -⟩
      · simp [xI, wI, yI, zI] at h; omega
      · simp [xI, wI, yI, zI]
    refine cong_dir hg (frd_L X ob) hgr i (zI (hrD D)) (S := Set.range X.e0) ?_ ?_
    · rintro s ⟨c, rfl⟩
      exact ⟨xI (hrD D) c, (frame_isotropic X ob c).symm, ne_val (by simp [xI, wI, yI, zI]; omega)⟩
    · rw [frame_anisotropic]; exact hc.2.1
  ·
    have hpos : D.R.rS + D.R.k + 1 + b.1 ≤ i.1 := by
      rcases hij with h | ⟨-, h⟩
      · simpa [xI, wI, yI, zI] using h
      · exact absurd h (ne_val (by simp [xI, wI, yI, zI] <;> omega))
    rcases kind_cases (hrD D) i with ⟨a, rfl⟩ | ⟨l', rfl⟩ | rfl | ⟨a, rfl⟩
    · exfalso; simp [xI, wI, yI, zI] at hpos; omega
    · exfalso; simp [xI, wI, yI, zI] at hpos; omega
    · exfalso; simp [xI, wI, yI, zI] at hpos; omega
    · simp [xI, wI, yI, zI] at hpos
      refine cong_dual hg (fr_L X ob) hgr (yI (hrD D) a) (yI (hrD D) b)
        (S := X.e0 '' {c | c.1 < (rv a).1}) ?_ ?_
      · rintro s ⟨c, hc', rfl⟩
        exact ⟨yI (hrD D) (rv c), by rw [frd_y, rv_rv], ne_val (by simp [xI, wI, yI, zI, rv] at hc' ⊢; omega)⟩
      · rw [frd_y]; exact hci.1 (rv a)

theorem shape (ob : Bool) (hg : ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ w.asIdeal)
    (hew : X.ew - (if ob then 1 else 0) ∈ Wq X.B.I w) (hsew : sg X.B.I X.ew - (if ob then 0 else 1) ∈ Wq X.B.I w)
    (hp : p.Prime) (hcard : Nat.card (𝓞 X.B.I.E ⧸ w.asIdeal) = p) (hn : 0 < X.B.I.n)
    {x : X.B.I.Gf} (hx : x ∈ X.K2) {N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod p)}
    (hN : ∀ i j, CongW (w := w) p (hhat X.B.I (frd X ob i) (X.B.I.fmat x *ᵥ fr X ob j)) (N i j)) :
    JPred D.R.k D.R.rS N := by
  refine jPred_of (hrD D) (fun a b hba => ?_) (fun a => ?_) (fun l => ?_)
  · have h := col (p := p) X ob hg hew hsew hx a b (Or.inl (le_of_lt hba))
    rw [if_neg (fun h' => (ne_of_gt hba) h')] at h
    exact congW_unique hp hcard hn (hN a b) h
  · have h := col (p := p) X ob hg hew hsew hx a a (Or.inl le_rfl)
    rw [if_pos rfl] at h
    exact congW_unique hp hcard hn (hN a a) h
  · have h := col (p := p) X ob hg hew hsew hx (wI (hrD D) l) (zI (hrD D)) (Or.inr ⟨⟨l, rfl⟩, rfl⟩)
    rw [if_neg (ne_val (by simp [xI, wI, yI, zI] <;> omega))] at h
    exact congW_unique hp hcard hn (hN _ _) h

end Formalism.L2.SG.Pf.KppLoc
end
end

noncomputable section

open NumberField IsDedekindDomain Matrix Finset
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.KppLoc

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin Formalism.L2.SG.Pf.RedBasicsPf
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.Pf.AllRowsRedKerA Formalism.L2.SG.Pf.KppRedW Formalism.L2.SG.Pf.KppFrameW Formalism.L2.SG.Pf.KppIdx
  Formalism.L2.SG.Pf.AllRowsKpp Formalism.MainNotions.ArithmeticCylinders

variable {D : D7} (X : HidaSetting D)

def argC (x : X.B.I.Gf) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F :=
  (∑ a, hA X.B.I (X.f0 a) (X.B.I.fmat x *ᵥ nxt X.e0 X.z0 a)) +
    ∑ i : Fin D.R.k, if h : i.1 + 1 < D.R.k then hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw ⟨i.1 + 1, h⟩) else 0

theorem quadratic_character_eq_additive (x : X.B.I.Gf) : X.chi2 x = X.psiEf (divN X.B.I X.B.g (argC X x)) := rfl

theorem argC_int {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) : argC X x ∈ IntAf X.B.I.F X.B.I.E := by
  unfold argC
  refine add_mem (sum_mem fun a _ => ?_) (sum_mem fun i _ => ?_)
  · refine dual_hat_integral X.B.I _ (X.vectorsInLattice.1 a).2 _ (K_mv X.B.I hx ?_)
    unfold nxt; split_ifs
    · exact (X.vectorsInLattice.1 _).1
    · exact X.vectorsInLattice.2.1
  · split_ifs
    · exact dual_hat_integral X.B.I _ (X.vectorsInLattice.2.2 i).2 _ (K_mv X.B.I hx (X.vectorsInLattice.2.2 _).1)
    · exact zero_mem _

theorem sg_swap (x : X.B.I.Gf) (u v : VA X.B.I) :
    sg X.B.I (hhat X.B.I u (X.B.I.fmat x *ᵥ v)) = hhat X.B.I v (X.B.I.fmat x⁻¹ *ᵥ u) := by
  rw [hhat_conj]
  have := hhat_fmat X.B.I x v (X.B.I.fmat x⁻¹ *ᵥ u)
  rw [Matrix.mulVec_mulVec, ← fmat_mul, mul_inv_cancel, fmat_one, Matrix.one_mulVec] at this
  exact this

variable {w : HeightOneSpectrum (𝓞 X.B.I.E)} {p : ℕ}

def tW (ob : Bool) (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod p)) : ZMod p :=
  (∑ a : Fin D.R.rS, if h : a.1 + 1 < D.R.rS then N (xI (hrD D) a) (xI (hrD D) ⟨a.1 + 1, h⟩)
      else N (xI (hrD D) a) (zI (hrD D))) +
    ∑ i : Fin D.R.k, if h : i.1 + 1 < D.R.k then (if ob then N (wI (hrD D) i) (wI (hrD D) ⟨i.1 + 1, h⟩) else 0) else 0

def tWc (ob : Bool) (N' : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod p)) : ZMod p :=
  (∑ a : Fin D.R.rS, if h : a.1 + 1 < D.R.rS then N' (yI (hrD D) (rv ⟨a.1 + 1, h⟩)) (yI (hrD D) (rv a))
      else -N' (zI (hrD D)) (yI (hrD D) (rv a))) +
    ∑ i : Fin D.R.k, if h : i.1 + 1 < D.R.k then
      (if ob then 0 else N' (wI (hrD D) (rv ⟨i.1 + 1, h⟩)) (wI (hrD D) (rv i))) else 0

theorem bw_Lq (hew : X.ew ∈ Wq X.B.I w) (i : Fin D.R.k) : X.bw i ∈ Lq X.B.I w := by
  rw [X.bw_w i]; exact Wq_smul hew (X.vectorsInLattice.2.2 i).1

theorem bwd_Lq (hsew : sg X.B.I X.ew ∈ Wq X.B.I w) (i : Fin D.R.k) : X.bwd i ∈ Lq X.B.I w := by
  rw [X.bwd_w i]; exact Wq_smul hsew (X.vectorsInLattice.2.2 i).2

theorem congC (ob : Bool) (hew : X.ew - (if ob then 1 else 0) ∈ Wq X.B.I w) {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kset)
    {N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod p)}
    (hN : ∀ i j, CongW (w := w) p (hhat X.B.I (frd X ob i) (X.B.I.fmat x *ᵥ fr X ob j)) (N i j)) :
    CongW (w := w) p (argC X x) (tW (D := D) ob N) := by
  unfold argC tW
  refine congW_add (congW_sum _ fun a _ => ?_) (congW_sum _ fun i _ => ?_)
  · unfold nxt
    split_ifs with h
    · have := hN (xI (hrD D) a) (xI (hrD D) ⟨a.1 + 1, h⟩)
      rwa [dual_frame_isotropic, frame_isotropic] at this
    · have := hN (xI (hrD D) a) (zI (hrD D))
      rwa [dual_frame_isotropic, frame_anisotropic] at this
  · split_ifs with h hob
    · have := hN (wI (hrD D) i) (wI (hrD D) ⟨i.1 + 1, h⟩)
      rw [hob] at this
      rwa [frd_wt, fr_wt] at this
    · refine congW_zero_of (hhat_Lq_right (X.vectorsInLattice.2.2 i).2 (stab_w X.B.I w hx (bw_Lq X ?_ _)))
      simp only [hob, Bool.false_eq_true, if_false, sub_zero] at hew
      exact hew
    · exact congW_zero_of (zero_mem _)

theorem congW_of_sg {t : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} {m : ZMod p} (h : CongW (w := w) p (sg X.B.I t) m) :
    CongW (w := wc X.B.I w) p t m := by
  have := (congW_sg (I := X.B.I) (w := w) (t := sg X.B.I t) (m := m)).2 h
  rwa [sg_sg] at this

theorem congCc (ob : Bool) (hsew : sg X.B.I X.ew - (if ob then 0 else 1) ∈ Wq X.B.I w) {x : X.B.I.Gf}
    (hx : x ∈ X.B.I.Kset) {N' : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod p)}
    (hN' : ∀ i j, CongW (w := w) p (hhat X.B.I (frd X ob i) (X.B.I.fmat x⁻¹ *ᵥ fr X ob j)) (N' i j)) :
    CongW (w := wc X.B.I w) p (argC X x) (tWc (D := D) ob N') := by
  refine congW_of_sg X ?_
  unfold argC tWc
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_add (f := _), map_sum, map_sum]
  refine congW_add (congW_sum _ fun a _ => ?_) (congW_sum _ fun i _ => ?_)
  · unfold nxt
    split_ifs with h
    · show CongW p (sg X.B.I (hhat X.B.I _ _)) _
      rw [sg_swap]
      have := hN' (yI (hrD D) (rv ⟨a.1 + 1, h⟩)) (yI (hrD D) (rv a))
      rwa [frd_y, fr_y, rv_rv, rv_rv] at this
    · show CongW p (sg X.B.I (hhat X.B.I _ _)) _
      rw [sg_swap]
      have := congW_neg (hN' (zI (hrD D)) (yI (hrD D) (rv a)))
      rwa [dual_frame_anisotropic, fr_y, rv_rv, hhat_neg_left, neg_neg] at this
  · split_ifs with h hob
    · show CongW p (sg X.B.I (hhat X.B.I _ _)) _
      rw [sg_swap]
      refine congW_zero_of (hhat_Lq_right (X.vectorsInLattice.2.2 _).1 (stab_w X.B.I w (K_inv X.B.I hx) (bwd_Lq X ?_ i)))
      simp only [hob, if_true, sub_zero] at hsew
      exact hsew
    · show CongW p (sg X.B.I (hhat X.B.I _ _)) _
      rw [sg_swap]
      have := hN' (wI (hrD D) (rv ⟨i.1 + 1, h⟩)) (wI (hrD D) (rv i))
      simp only [hob, Bool.false_eq_true] at this ⊢
      rwa [frd_wf, fr_wf, rv_rv, rv_rv] at this
    · rw [map_zero]; exact congW_zero_of (zero_mem _)

theorem entN_eq {r : ℕ} (M : Matrix (Fin r) (Fin r) (ZMod p)) (i j : Fin r) {a b : ℕ} (ha : i.1 = a) (hb : j.1 = b) :
    M i j = entN M a b := by
  subst ha hb
  unfold entN
  rw [dite_eq_left ⟨i.2, j.2⟩]

theorem sum_eq (ob : Bool) {N N' : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod p)}
    (hinv : ∀ i, i + 1 < D.R.r → entN N' i (i + 1) = -entN N i (i + 1)) :
    tW (D := D) ob N + tWc (D := D) ob N' = phiJ D.R.k D.R.rS (dM D.R.rS D.R.k ob * N * dM D.R.rS D.R.k ob) := by
  have hr := hrD D
  rw [phi_key hr ob hinv]
  unfold tW tWc
  have e1 : ∑ a : Fin D.R.rS, ((if h : a.1 + 1 < D.R.rS then N (xI hr a) (xI hr ⟨a.1 + 1, h⟩)
        else N (xI hr a) (zI hr)) + (if h : a.1 + 1 < D.R.rS then N' (yI hr (rv ⟨a.1 + 1, h⟩)) (yI hr (rv a))
        else -N' (zI hr) (yI hr (rv a)))) =
      ∑ a ∈ range D.R.rS, (if a + 1 < D.R.rS then entN N a (a + 1) +
        entN N' (D.R.rS + D.R.k + 1 + (D.R.rS - 2 - a)) (D.R.rS + D.R.k + 1 + (D.R.rS - 1 - a))
        else entN N a (D.R.rS + D.R.k) - entN N' (D.R.rS + D.R.k) (D.R.rS + D.R.k + 1)) := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs with h
    · have q1 : N (xI hr a) (xI hr ⟨a.1 + 1, h⟩) = entN N a.1 (a.1 + 1) := entN_eq N _ _ rfl rfl
      have q2 : N' (yI hr (rv ⟨a.1 + 1, h⟩)) (yI hr (rv a)) =
          entN N' (D.R.rS + D.R.k + 1 + (D.R.rS - 2 - a.1)) (D.R.rS + D.R.k + 1 + (D.R.rS - 1 - a.1)) :=
        entN_eq N' _ _ (by dsimp [yI, wI, rv]; omega) (by rfl)
      rw [q1, q2]
    · have q1 : N (xI hr a) (zI hr) = entN N a.1 (D.R.rS + D.R.k) := entN_eq N _ _ rfl rfl
      have q2 : N' (zI hr) (yI hr (rv a)) = entN N' (D.R.rS + D.R.k) (D.R.rS + D.R.k + 1) :=
        entN_eq N' _ _ rfl (by dsimp [yI, wI, rv]; omega)
      rw [q1, q2]; ring
  have e2 : ∑ i : Fin D.R.k, ((if h : i.1 + 1 < D.R.k then (if ob then N (wI hr i) (wI hr ⟨i.1 + 1, h⟩) else 0) else 0) +
        (if h : i.1 + 1 < D.R.k then (if ob then 0 else N' (wI hr (rv ⟨i.1 + 1, h⟩)) (wI hr (rv i))) else 0)) =
      ∑ i ∈ range D.R.k, (if i + 1 < D.R.k then (if ob then entN N (D.R.rS + i) (D.R.rS + i + 1)
        else entN N' (D.R.rS + (D.R.k - 2 - i)) (D.R.rS + (D.R.k - 1 - i))) else 0) := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h hob
    · have q1 : N (wI hr i) (wI hr ⟨i.1 + 1, h⟩) = entN N (D.R.rS + i.1) (D.R.rS + i.1 + 1) :=
        entN_eq N _ _ rfl (by dsimp [yI, wI, rv]; omega)
      rw [q1, add_zero]
    · have q1 : N' (wI hr (rv ⟨i.1 + 1, h⟩)) (wI hr (rv i)) =
          entN N' (D.R.rS + (D.R.k - 2 - i.1)) (D.R.rS + (D.R.k - 1 - i.1)) :=
        entN_eq N' _ _ (by dsimp [yI, wI, rv]; omega) (by rfl)
      rw [q1, zero_add]
    · simp
  rw [← e1, ← e2, Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

end Formalism.L2.SG.Pf.KppLoc
