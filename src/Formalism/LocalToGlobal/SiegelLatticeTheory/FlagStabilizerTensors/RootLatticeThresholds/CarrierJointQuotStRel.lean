module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LeadingMinors
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuotRel
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal ComplexConjugate
open Matrix

namespace Formalism.L2.SG.Pf.Carrier.JointQuot

section Alg

variable {r : ℕ}

theorem relAlg (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (π : Fin (r + 1) → Fin (r + 1)) (hπ : ∀ a, π (π a) = a)
    (hP1 : ∀ c b, Z c b ≠ 0 ↔ c = π b)
    (hP2 : ∀ k : Fin r, ((π k.succ).val + 1 = (π k.castSucc).val ∧
        Z (π k.succ) k.succ = - Z (π k.castSucc) k.castSucc) ∨ (π k.castSucc).val < (π k.succ).val)
    (m U : Fin r → Fin (r + 1) → ℂ)
    (hA : ∀ a b, (∑ c : Fin r, if c.castSucc < a then conj (m c a) * Z c.castSucc b else 0) =
      ∑ c : Fin r, if c.castSucc < b then U c b * Z a c.castSucc else 0) :
    ∑ k : Fin r, (U k k.succ).re = - ∑ k : Fin r, (m k k.succ).re := by
  have hπinj : Function.Injective π := Function.Involutive.injective hπ
  have hZ0 : ∀ c b, c ≠ π b → Z c b = 0 := fun c b h => by
    by_contra h'
    exact h ((hP1 c b).1 h')
  have hzne : ∀ b, Z (π b) b ≠ 0 := fun b => (hP1 _ b).2 rfl
  have hcond : ∀ k : Fin r, (π k.succ).val + 1 = (π k.castSucc).val → (π k.succ).val < r :=
    fun k h => by have := (π k.castSucc).isLt; omega
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : Fin r → Fin r, ∀ k, ψ k =
      if h : (π k.succ).val + 1 = (π k.castSucc).val then ⟨(π k.succ).val, hcond k h⟩ else k :=
    ⟨_, fun k => rfl⟩

  have hR1 : ∀ k : Fin r, (∑ c : Fin r, if c.castSucc < π k.castSucc then
        conj (m c (π k.castSucc)) * Z c.castSucc k.succ else 0) =
      U k k.succ * Z (π k.castSucc) k.castSucc := by
    intro k
    rw [hA, Finset.sum_eq_single k]
    · rw [if_pos (Fin.castSucc_lt_succ : k.castSucc < k.succ)]
    · intro c _ hck
      split_ifs
      · rw [hZ0 _ _ (fun e => hck (Fin.castSucc_injective r (hπinj e).symm)), mul_zero]
      · rfl
    · intro h
      exact absurd (Finset.mem_univ k) h

  have hR2 : ∀ j : Fin r, (∑ c : Fin r, if c.castSucc < π j.castSucc then
        U c (π j.castSucc) * Z j.succ c.castSucc else 0) =
      conj (m j j.succ) * Z j.castSucc (π j.castSucc) := by
    intro j
    rw [← hA, Finset.sum_eq_single j]
    · rw [if_pos (Fin.castSucc_lt_succ : j.castSucc < j.succ)]
    · intro c _ hcj
      split_ifs
      · rw [hZ0 _ _ (by rw [hπ]; exact fun e => hcj (Fin.castSucc_injective r e)), mul_zero]
      · rfl
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hψ : Function.Involutive ψ := by
    intro k
    by_cases h : (π k.succ).val + 1 = (π k.castSucc).val
    · obtain ⟨j, hjv⟩ : ∃ j : Fin r, j.val = (π k.succ).val := ⟨⟨_, hcond k h⟩, rfl⟩
      have hψk : ψ k = j := by
        rw [hψdef, dite_eq_left h]
        exact Fin.ext hjv.symm
      have hjc : j.castSucc = π k.succ := Fin.ext (by rw [Fin.coe_castSucc, hjv])
      have hjs : j.succ = π k.castSucc := Fin.ext (by rw [Fin.val_succ, hjv]; exact h)
      have h' : (π j.succ).val + 1 = (π j.castSucc).val := by
        rw [hjs, hjc, hπ, hπ, Fin.coe_castSucc, Fin.val_succ]
      rw [hψk, hψdef, dite_eq_left h']
      apply Fin.ext
      show (π j.succ).val = k.val
      rw [hjs, hπ, Fin.coe_castSucc]
    · have hψk : ψ k = k := by rw [hψdef, dite_eq_right h]
      rw [hψk, hψk]
  have hterm : ∀ k : Fin r, (U k k.succ).re = -(m (ψ k) (ψ k).succ).re := by
    intro k
    by_cases h : (π k.succ).val + 1 = (π k.castSucc).val
    · obtain ⟨j, hjv⟩ : ∃ j : Fin r, j.val = (π k.succ).val := ⟨⟨_, hcond k h⟩, rfl⟩
      have hψk : ψ k = j := by
        rw [hψdef, dite_eq_left h]
        exact Fin.ext hjv.symm
      have hjc : j.castSucc = π k.succ := Fin.ext (by rw [Fin.coe_castSucc, hjv])
      have hjs : j.succ = π k.castSucc := Fin.ext (by rw [Fin.val_succ, hjv]; exact h)
      have hz : Z (π k.succ) k.succ = - Z (π k.castSucc) k.castSucc := by
        rcases hP2 k with ⟨_, hz⟩ | hlt
        · exact hz
        · omega
      have hlt1 : π k.succ < π k.castSucc := Fin.lt_iff_val_lt_val.2 (by omega)
      have eL : (∑ c : Fin r, if c.castSucc < π k.castSucc then
          conj (m c (π k.castSucc)) * Z c.castSucc k.succ else 0) =
          conj (m j j.succ) * Z (π k.succ) k.succ := by
        rw [Finset.sum_eq_single j]
        · rw [hjs, hjc, if_pos hlt1]
        · intro c _ hcj
          split_ifs
          · rw [hZ0 _ _ (fun e => hcj (Fin.castSucc_injective r (e.trans hjc.symm))), mul_zero]
          · rfl
        · intro hj
          exact absurd (Finset.mem_univ j) hj
      have key := eL.symm.trans (hR1 k)
      rw [hz] at key
      have hU : U k k.succ = -conj (m j j.succ) := by
        apply mul_right_cancel₀ (hzne k.castSucc)
        rw [← key]
        ring
      rw [hψk, hU, Complex.neg_re, Complex.conj_re]
    · have hlt : (π k.castSucc).val < (π k.succ).val := by
        rcases hP2 k with ⟨h', _⟩ | hlt
        · exact absurd h' h
        · exact hlt
      have hψk : ψ k = k := by rw [hψdef, dite_eq_right h]
      have eL : (∑ c : Fin r, if c.castSucc < π k.castSucc then
          conj (m c (π k.castSucc)) * Z c.castSucc k.succ else 0) = 0 :=
        Finset.sum_eq_zero fun c _ => by
          split_ifs with hc
          · rw [hZ0 _ _ (fun e => by rw [e, Fin.lt_iff_val_lt_val] at hc; omega), mul_zero]
          · rfl
      have hU : U k k.succ = 0 := by
        have key := eL.symm.trans (hR1 k)
        exact (mul_eq_zero.1 key.symm).resolve_right (hzne _)
      have eR2 : (∑ c : Fin r, if c.castSucc < π k.castSucc then
          U c (π k.castSucc) * Z k.succ c.castSucc else 0) = 0 :=
        Finset.sum_eq_zero fun c _ => by
          split_ifs with hc
          · rw [hZ0 _ _ (fun e => by
                have e2 := congrArg π e
                rw [hπ] at e2
                rw [← e2, Fin.lt_iff_val_lt_val] at hc
                omega), mul_zero]
          · rfl
      have hm : conj (m k k.succ) = 0 := by
        have key := eR2.symm.trans (hR2 k)
        exact (mul_eq_zero.1 key.symm).resolve_right ((hP1 _ _).2 (hπ _).symm)
      have hre : (m k k.succ).re = 0 := by rw [← Complex.conj_re, hm, Complex.zero_re]
      rw [hψk, hU, Complex.zero_re, hre, neg_zero]
  rw [Finset.sum_congr rfl (fun k _ => hterm k), Finset.sum_neg_distrib]
  congr 1
  exact Equiv.sum_comp (Function.Involutive.toPerm ψ hψ) (fun j => (m j j.succ).re)

end Alg

section Pt

variable {K : Type*} [Zero K]

def ptPar : List (K × ℕ) → ℕ → ℕ
  | [], a => a
  | (_, s) :: bs, a => if a < s then s - 1 - a else s + ptPar bs (a - s)

def ptSc : List (K × ℕ) → ℕ → K
  | [], _ => 0
  | (t, s) :: bs, a => if a < s then t else ptSc bs (a - s)

theorem ptPar_cons (t : K) (s : ℕ) (bs : List (K × ℕ)) (a : ℕ) :
    ptPar ((t, s) :: bs) a = if a < s then s - 1 - a else s + ptPar bs (a - s) := rfl

theorem ptSc_cons (t : K) (s : ℕ) (bs : List (K × ℕ)) (a : ℕ) :
    ptSc ((t, s) :: bs) a = if a < s then t else ptSc bs (a - s) := rfl

theorem ptEntry_cons (t : K) (s : ℕ) (bs : List (K × ℕ)) (i j : ℕ) :
    ptEntry ((t, s) :: bs) i j = if i < s ∧ j < s then (if i + j + 1 = s then t else 0)
      else if s ≤ i ∧ s ≤ j then ptEntry bs (i - s) (j - s) else 0 := rfl

theorem ptEntry_eq : ∀ (bs : List (K × ℕ)) (c b : ℕ), b < (bs.map Prod.snd).sum →
    ptEntry bs c b = if c = ptPar bs b then ptSc bs b else 0
  | [], _, b, hb => by simp at hb
  | (t, s) :: bs, c, b, hb => by
    simp only [List.map_cons, List.sum_cons] at hb
    rw [ptEntry_cons]
    by_cases hbs : b < s
    · have hp : ptPar ((t, s) :: bs) b = s - 1 - b := by rw [ptPar_cons, if_pos hbs]
      have hq : ptSc ((t, s) :: bs) b = t := by rw [ptSc_cons, if_pos hbs]
      rw [hp, hq]
      by_cases hcs : c < s
      · rw [if_pos ⟨hcs, hbs⟩]
        by_cases h : c + b + 1 = s
        · rw [if_pos h, if_pos (by omega)]
        · rw [if_neg h, if_neg (by omega)]
      · rw [if_neg (fun h => hcs h.1), if_neg (fun h => by omega), if_neg (by omega)]
    · have hp : ptPar ((t, s) :: bs) b = s + ptPar bs (b - s) := by rw [ptPar_cons, if_neg hbs]
      have hq : ptSc ((t, s) :: bs) b = ptSc bs (b - s) := by rw [ptSc_cons, if_neg hbs]
      rw [hp, hq, if_neg (fun h => hbs h.2)]
      by_cases hcs : s ≤ c
      · rw [if_pos ⟨hcs, by omega⟩, ptEntry_eq bs (c - s) (b - s) (by omega)]
        by_cases h : c - s = ptPar bs (b - s)
        · rw [if_pos h, if_pos (by omega)]
        · rw [if_neg h, if_neg (by omega)]
      · rw [if_neg (fun h => hcs h.1), if_neg (by omega)]

theorem ptPar_lt : ∀ (bs : List (K × ℕ)) (b : ℕ), b < (bs.map Prod.snd).sum →
    ptPar bs b < (bs.map Prod.snd).sum
  | [], b, hb => by simp at hb
  | (t, s) :: bs, b, hb => by
    simp only [List.map_cons, List.sum_cons] at hb ⊢
    rw [ptPar_cons]
    by_cases hbs : b < s
    · rw [if_pos hbs]; omega
    · rw [if_neg hbs]; have := ptPar_lt bs (b - s) (by omega); omega

theorem ptPar_invol : ∀ (bs : List (K × ℕ)) (b : ℕ), b < (bs.map Prod.snd).sum →
    ptPar bs (ptPar bs b) = b
  | [], b, hb => by simp at hb
  | (t, s) :: bs, b, hb => by
    simp only [List.map_cons, List.sum_cons] at hb
    by_cases hbs : b < s
    · have hp : ptPar ((t, s) :: bs) b = s - 1 - b := by rw [ptPar_cons, if_pos hbs]
      rw [hp, ptPar_cons, if_pos (by omega)]; omega
    · have hp : ptPar ((t, s) :: bs) b = s + ptPar bs (b - s) := by rw [ptPar_cons, if_neg hbs]
      rw [hp, ptPar_cons, if_neg (by omega)]
      have : s + ptPar bs (b - s) - s = ptPar bs (b - s) := by omega
      rw [this, ptPar_invol bs (b - s) (by omega)]; omega

theorem ptSc_ne : ∀ (bs : List (K × ℕ)), (∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) → ∀ b : ℕ,
    b < (bs.map Prod.snd).sum → ptSc bs b ≠ 0
  | [], _, b, hb => by simp at hb
  | (t, s) :: bs, h, b, hb => by
    simp only [List.map_cons, List.sum_cons] at hb
    rw [ptSc_cons]
    by_cases hbs : b < s
    · rw [if_pos hbs]; exact (h (t, s) (by simp)).1
    · rw [if_neg hbs]; exact ptSc_ne bs (fun b hb => h b (by simp [hb])) (b - s) (by omega)

theorem ptPar_consec : ∀ (bs : List (K × ℕ)), (∀ b ∈ bs, 1 ≤ b.2) → ∀ k : ℕ,
    k + 1 < (bs.map Prod.snd).sum →
    (ptPar bs (k + 1) + 1 = ptPar bs k ∧ ptSc bs (k + 1) = ptSc bs k) ∨ ptPar bs k < ptPar bs (k + 1)
  | [], _, k, hk => by simp at hk
  | (t, s) :: bs, h, k, hk => by
    simp only [List.map_cons, List.sum_cons] at hk
    have hs1 : 1 ≤ s := h (t, s) (by simp)
    rw [ptPar_cons, ptPar_cons, ptSc_cons, ptSc_cons]
    by_cases h1 : k + 1 < s
    · left
      rw [if_pos h1, if_pos (by omega), if_pos h1, if_pos (by omega)]
      exact ⟨by omega, rfl⟩
    · by_cases h2 : k < s
      · right
        rw [if_neg h1, if_pos h2]; omega
      · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]
        have e : k + 1 - s = k - s + 1 := by omega
        rw [e]
        rcases ptPar_consec bs (fun b hb => h b (by simp [hb])) (k - s) (by omega) with h3 | h3
        · left; exact ⟨by omega, h3.2⟩
        · right; omega

end Pt

section Frame

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj

variable {n r : ℕ} (ε : Fin n → Bool)

theorem hJ_add_r' (x y y' : Fin n → ℂ) : hJ ε x (y + y') = hJ ε x y + hJ ε x y' := by
  simp only [hJ, Matrix.mulVec_add, dotProduct_add]

theorem hJ_sum_r' {ι : Type*} [Fintype ι] (x : Fin n → ℂ) (a : ι → ℂ) (y : ι → Fin n → ℂ) :
    hJ ε x (∑ c, a c • y c) = ∑ c, a c * hJ ε x (y c) := by
  simp only [hJ, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]

theorem hJ_cj' (x y : Fin n → ℂ) : hJ ε x y = conj (hJ ε y x) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hJ, Formalism.REAL.Jm, Matrix.mulVec_diagonal, dotProduct, Pi.star_apply, RCLike.star_def, map_sum,
    map_mul, Complex.conj_conj]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs <;> simp <;> ring

theorem hJ_sum_l' {ι : Type*} [Fintype ι] (x : Fin n → ℂ) (a : ι → ℂ) (y : ι → Fin n → ℂ) (w : Fin n → ℂ) :
    hJ ε (x + ∑ c, a c • y c) w = hJ ε x w + ∑ c, conj (a c) * hJ ε (y c) w := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hJ_cj' ε (x + ∑ c, a c • y c) w, hJ_add_r', hJ_sum_r', map_add (f := _), map_sum, ← hJ_cj' ε x w]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul, ← hJ_cj' ε (y c) w]

theorem span_expand (e f : Fin r → Fin n → ℂ) (hfe : ∀ a b, hJ ε (f a) (e b) = if b = a then 1 else 0)
    (k : ℕ) (y : Fin n → ℂ) (hy : y ∈ spanLt e k) :
    y = ∑ c : Fin r, (if c.val < k then hJ ε (f c) y else 0) • e c := by
  have hsm : ∀ (x : Fin n → ℂ) (t : ℂ) (v : Fin n → ℂ), hJ ε x (t • v) = t * hJ ε x v := by
    intro x t v
    simp only [hJ, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  unfold spanLt at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    have hb' : b.val < k := hb
    simp only [hfe]
    rw [Finset.sum_eq_single b]
    · simp [hb']
    · intro c _ hcb
      simp [Ne.symm hcb]
    · intro h
      exact absurd (Finset.mem_univ b) h
  | zero => simp [hJ]
  | add x y' _ _ hx hy =>
    conv_lhs => rw [hx, hy]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hJ_add_r']
    split_ifs <;> simp [add_smul]
  | smul t x _ hx =>
    conv_lhs => rw [hx]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hsm]
    split_ifs <;> simp [mul_smul]

theorem fam_castSucc (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (c : Fin r) : fam e z c.castSucc = e c := by
  simp [fam]

theorem fam_last (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : fam e z (Fin.last r) = z := by
  simp [fam]

theorem nxt_eq_fam (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (k : Fin r) : nxt e z k = fam e z k.succ := by
  unfold nxt
  have hk := k.isLt
  split_ifs with h
  · have e1 : k.succ = (⟨k.val + 1, h⟩ : Fin r).castSucc := Fin.ext (by simp)
    rw [e1, fam_castSucc]
  · have e1 : k.succ = Fin.last r := Fin.ext (by simp only [Fin.val_succ, Fin.val_last]; omega)
    rw [e1, fam_last]

theorem flag_expand (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ)
    (hfe : ∀ a b, hJ ε (f a) (e b) = if b = a then 1 else 0) (hfz : ∀ a, hJ ε (f a) z = 0)
    (g : Matrix (Fin n) (Fin n) ℂ) (hg : InS e z g) (a : Fin (r + 1)) :
    g *ᵥ fam e z a = fam e z a +
      ∑ c : Fin r, (if c.castSucc < a then hJ ε (f c) (g *ᵥ fam e z a) else 0) • e c := by
  have hmem : (g - 1) *ᵥ fam e z a ∈ spanLt e a.val := by
    induction a using Fin.lastCases with
    | last =>
      rw [fam_last]
      simpa using hg.2
    | cast b =>
      rw [fam_castSucc]
      simpa using hg.1 b
  have hzero : ∀ c : Fin r, c.castSucc < a → hJ ε (f c) (fam e z a) = 0 := by
    intro c hc
    induction a using Fin.lastCases with
    | last =>
      rw [fam_last]
      exact hfz c
    | cast b =>
      rw [fam_castSucc, hfe, if_neg]
      intro hbc
      subst hbc
      exact lt_irrefl _ hc
  have hsubJ : ∀ x y y' : Fin n → ℂ, hJ ε x (y - y') = hJ ε x y - hJ ε x y' := by
    intro x y y'
    simp only [hJ, Matrix.mulVec_sub, dotProduct_sub]
  have hexp := span_expand ε e f hfe a.val _ hmem
  rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hexp
  have hS : (∑ c : Fin r, (if c.val < a.val then hJ ε (f c) (g *ᵥ fam e z a - fam e z a) else 0) • e c) =
      ∑ c : Fin r, (if c.castSucc < a then hJ ε (f c) (g *ᵥ fam e z a) else 0) • e c := by
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : c.castSucc < a
    · have hc' : c.val < a.val := by
        rw [Fin.lt_iff_val_lt_val, Fin.coe_castSucc] at hc
        exact hc
      rw [if_pos hc', if_pos hc, hsubJ, hzero c hc, sub_zero]
    · have hc' : ¬ c.val < a.val := by
        rw [Fin.lt_iff_val_lt_val, Fin.coe_castSucc] at hc
        exact hc
      rw [if_neg hc', if_neg hc]
  rw [← hS, ← hexp]
  abel

end Frame

end Formalism.L2.SG.Pf.Carrier.JointQuot
end
end

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal ComplexConjugate
open Matrix

namespace Formalism.L2.SG.Pf.Carrier.JointQuot

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj

section LocRel

variable {n r : ℕ} (ε : Fin n → Bool)

theorem relA_loc (e f : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ)
    (hfe : ∀ a b, hJ ε (f a) (e b) = if b = a then 1 else 0) (hfz : ∀ a, hJ ε (f a) z = 0)
    (hfz' : ∀ a, hJ ε (f a) z' = 0) (S Si G T : Matrix (Fin n) (Fin n) ℂ)
    (hSi : InS e z Si) (hT : InS e z' T) (hadj : ∀ x y, hJ ε x (S *ᵥ y) = hJ ε (Si *ᵥ x) y)
    (hrel : S * G = G * T) (a b : Fin (r + 1)) :
    (∑ c : Fin r, if c.castSucc < a then conj (hJ ε (f c) (Si *ᵥ fam e z a)) *
        RealObj.Zhat ε (fam e z) (fam e z') G c.castSucc b else 0) =
      ∑ c : Fin r, if c.castSucc < b then hJ ε (f c) (T *ᵥ fam e z' b) *
        RealObj.Zhat ε (fam e z) (fam e z') G a c.castSucc else 0 := by
  have L : hJ ε (fam e z a) ((S * G) *ᵥ fam e z' b) = hJ ε (fam e z a) ((G * T) *ᵥ fam e z' b) := by
    rw [hrel]
  rw [← Matrix.mulVec_mulVec, hadj, flag_expand ε e f z hfe hfz Si hSi a, hJ_sum_l'] at L
  rw [← Matrix.mulVec_mulVec, flag_expand ε e f z' hfe hfz' T hT b, Matrix.mulVec_add, Matrix.mulVec_sum] at L
  simp only [Matrix.mulVec_smul] at L
  rw [hJ_add_r', hJ_sum_r'] at L
  have L2 := add_left_cancel L
  calc _ = ∑ c : Fin r, conj (if c.castSucc < a then hJ ε (f c) (Si *ᵥ fam e z a) else 0) *
        hJ ε (e c) (G *ᵥ fam e z' b) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        split_ifs
        · simp only [RealObj.Zhat, fam_castSucc]
        · simp
    _ = ∑ c : Fin r, (if c.castSucc < b then hJ ε (f c) (T *ᵥ fam e z' b) else 0) *
        hJ ε (fam e z a) (G *ᵥ e c) := L2
    _ = _ := by
        refine Finset.sum_congr rfl fun c _ => ?_
        split_ifs
        · simp only [RealObj.Zhat, fam_castSucc]
        · simp

theorem rootCoord_one (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ)
    (hfe : ∀ a b, hJ ε (f a) (e b) = if b = a then 1 else 0) (hfz : ∀ a, hJ ε (f a) z = 0) (a : Fin r) :
    rootCoord ε e f z 1 a = 0 := by
  unfold rootCoord nxt
  rw [Matrix.one_mulVec]
  split_ifs with hlt
  · rw [hfe, if_neg]
    intro h'
    have := congrArg Fin.val h'
    simp at this
  · exact hfz a

theorem rel_loc (e f : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ)
    (hfe : ∀ a b, hJ ε (f a) (e b) = if b = a then 1 else 0) (hfz : ∀ a, hJ ε (f a) z = 0)
    (hfz' : ∀ a, hJ ε (f a) z' = 0) (S Si G T : Matrix (Fin n) (Fin n) ℂ)
    (hS : InS e z S) (hSi : InS e z Si) (hSiS : Si * S = 1) (hT : InS e z' T)
    (hadj : ∀ x y, hJ ε x (S *ᵥ y) = hJ ε (Si *ᵥ x) y) (hrel : S * G = G * T)
    (π : Fin (r + 1) → Fin (r + 1)) (hπ : ∀ a, π (π a) = a)
    (hP1 : ∀ c b, RealObj.Zhat ε (fam e z) (fam e z') G c b ≠ 0 ↔ c = π b)
    (hP2 : ∀ k : Fin r, ((π k.succ).val + 1 = (π k.castSucc).val ∧
        RealObj.Zhat ε (fam e z) (fam e z') G (π k.succ) k.succ = - RealObj.Zhat ε (fam e z) (fam e z') G (π k.castSucc) k.castSucc) ∨
        (π k.castSucc).val < (π k.succ).val) :
    ∑ k : Fin r, (rootCoord ε e f z' T k).re = ∑ k : Fin r, (rootCoord ε e f z S k).re := by
  have h := relAlg (RealObj.Zhat ε (fam e z) (fam e z') G) π hπ hP1 hP2
    (fun c a => hJ ε (f c) (Si *ᵥ fam e z a)) (fun c b => hJ ε (f c) (T *ᵥ fam e z' b))
    (relA_loc ε e f z z' hfe hfz hfz' S Si G T hSi hT hadj hrel)
  have hU : ∀ k : Fin r, rootCoord ε e f z' T k = hJ ε (f k) (T *ᵥ fam e z' k.succ) := by
    intro k; unfold rootCoord; rw [nxt_eq_fam]
  have hm : ∀ k : Fin r, hJ ε (f k) (Si *ᵥ fam e z k.succ) = - rootCoord ε e f z S k := by
    intro k
    have h1 := Formalism.L2.SG.Pf.Vanish2.rootCoord_mul ε e f z hfe hfz hSi hS k
    rw [hSiS, rootCoord_one ε e f z hfe hfz] at h1
    have h2 : rootCoord ε e f z Si k = hJ ε (f k) (Si *ᵥ fam e z k.succ) := by
      unfold rootCoord; rw [nxt_eq_fam]
    rw [← h2]; linear_combination -h1
  simp only [hU]
  rw [h]
  simp only [hm, Complex.neg_re, Finset.sum_neg_distrib, neg_neg]

theorem sum_add_star {ι : Type*} [Fintype ι] (x : ι → ℂ) :
    ∑ a, (x a + star (x a)) = ((2 * ∑ a, (x a).re : ℝ) : ℂ) := by
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.star_def, Complex.add_conj]
  push_cast
  ring

theorem psiR_eq_of (gg : ℕ) (e f : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (S T : Matrix (Fin n) (Fin n) ℂ)
    (h : ∑ k : Fin r, (rootCoord ε e f z' T k).re = ∑ k : Fin r, (rootCoord ε e f z S k).re) :
    psiR ε gg e f z S = psiR ε gg e f z' T := by
  unfold psiR
  rw [sum_add_star, sum_add_star, h]

theorem psiR_mul_star (gg : ℕ) (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (S : Matrix (Fin n) (Fin n) ℂ) :
    psiR ε gg e f z S * star (psiR ε gg e f z S) = 1 := by
  unfold psiR
  rw [sum_add_star, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  convert Complex.exp_zero using 2
  simp only [map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_I, map_natCast, map_ofNat]
  ring

end LocRel

section Glob

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem famSc_one {n r : ℕ} (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : famSc 1 e z = fam e z := by
  funext a; simp [famSc]

theorem stRel_holds (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : StRel X u u' := by
  intro w hw s hs
  set γ := gamW X u u' w with hγdef
  have hγ : IsPtRep X u u' w γ := by
    rw [hγdef, gamW, dite_eq_left hw.1]; exact hw.1.choose_spec
  unfold psiU psiInf
  rw [Complex.star_def, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun v _ => ?_
  rw [← Complex.star_def]
  set ε := X.B.I.ε v
  set e : Fin D.R.rS → Fin X.B.I.n → ℂ := fun a => rv X.B.I v (X.eR a)
  set f : Fin D.R.rS → Fin X.B.I.n → ℂ := fun a => rv X.B.I v (X.fR a)
  set z := rv X.B.I v (X.zR u)
  set z' := rv X.B.I v (X.zR u')
  have hfe : ∀ a b, hJ ε (f a) (e b) = if b = a then 1 else 0 := by
    intro a b
    rw [Formalism.L2.SG.Pf.Level.hJ_rv, Formalism.L2.SG.Pf.Vanish2.hE_f_e]
    split_ifs <;> simp
  have hfz : ∀ (u : D.what₂.Word) a, hJ ε (f a) (rv X.B.I v (X.zR u)) = 0 := by
    intro u a
    rw [Formalism.L2.SG.Pf.Level.hJ_rv, Formalism.L2.SG.Pf.Vanish2.hermitian_f_z_zero, map_zero]
  have hS : InS e z (uMat (s v)) := (hs.1 v).1
  have hT : InS e z' (uMat ((γ⁻¹ * s * γ) v)) := (hs.2 v).1
  have hSiS : uMat (s v)⁻¹ * uMat (s v) = 1 := Formalism.L2.SG.RealObj.InfCut.uMat_inv_mul' (s v)
  have hSi : InS e z (uMat (s v)⁻¹) := Formalism.L2.SG.RealObj.InfCut.inS_inv e z _ _ hSiS hS
  have hrel : uMat (s v) * uMat (γ v) = uMat (γ v) * uMat ((γ⁻¹ * s * γ) v) := by
    have e1 : s v * γ v = γ v * (γ⁻¹ * s * γ) v := by
      simp only [Pi.mul_apply, Pi.inv_apply]; group
    have e2 : uMat (s v * γ v) = uMat (γ v * (γ⁻¹ * s * γ) v) := by rw [e1]
    simpa [uMat] using e2

  have hZ : ZX X u u' 1 γ v = RealObj.Zhat ε (fam e z) (fam e z') (uMat (γ v)) := by
    simp only [ZX, frm, famSc_one]; rfl
  have hO := hγ v
  have hsum : (w.1.map Prod.snd).sum = D.R.rS + 1 := w.2.2
  have hZe : ∀ c b : Fin (D.R.rS + 1), RealObj.Zhat ε (fam e z) (fam e z') (uMat (γ v)) c b =
      (-1 : ℂ) ^ (D.R.rS - b.1) * X.B.I.φ v (X.ιE.symm (if c.val = ptPar w.1 b.val then ptSc w.1 b.val else 0)) := by
    intro c b
    have h1 := congrFun (congrFun hO c) b
    simp only [RealObj.ZhatO, ptC, Matrix.map_apply, ptMat, hZ] at h1
    rw [← ptEntry_eq w.1 c.val b.val (by rw [hsum]; exact b.2), ← h1, ← mul_assoc, ← mul_pow]
    norm_num
  have hne : ∀ b : ℕ, b < D.R.rS + 1 → X.B.I.φ v (X.ιE.symm (ptSc w.1 b)) ≠ 0 := by
    intro b hb
    rw [map_ne_zero, map_ne_zero]
    exact ptSc_ne w.1 w.2.1 b (by rw [hsum]; exact hb)
  let π : Fin (D.R.rS + 1) → Fin (D.R.rS + 1) := fun b =>
    ⟨ptPar w.1 b.val, lt_of_lt_of_eq (ptPar_lt w.1 b.val (by rw [hsum]; exact b.2)) hsum⟩
  have hπ : ∀ a, π (π a) = a := fun a => Fin.ext (ptPar_invol w.1 a.val (by rw [hsum]; exact a.2))
  have hP1 : ∀ c b, RealObj.Zhat ε (fam e z) (fam e z') (uMat (γ v)) c b ≠ 0 ↔ c = π b := by
    intro c b
    rw [hZe]
    by_cases h : c.val = ptPar w.1 b.val
    · rw [if_pos h]
      refine ⟨fun _ => Fin.ext h, fun _ => mul_ne_zero (pow_ne_zero _ (by norm_num)) (hne b.val b.2)⟩
    · rw [if_neg h, map_zero, map_zero, mul_zero]
      exact ⟨fun h' => absurd rfl h', fun h' => absurd (congrArg Fin.val h') h⟩
  have hP2 : ∀ k : Fin D.R.rS, ((π k.succ).val + 1 = (π k.castSucc).val ∧
      RealObj.Zhat ε (fam e z) (fam e z') (uMat (γ v)) (π k.succ) k.succ =
        - RealObj.Zhat ε (fam e z) (fam e z') (uMat (γ v)) (π k.castSucc) k.castSucc) ∨
      (π k.castSucc).val < (π k.succ).val := by
    intro k
    have hsz : ∀ b ∈ w.1, 1 ≤ b.2 := fun b hb => (w.2.1 b hb).2
    rcases ptPar_consec w.1 hsz k.val (by rw [hsum]; omega) with h3 | h3
    · left
      refine ⟨h3.1, ?_⟩
      rw [hZe, hZe, if_pos rfl, if_pos rfl]
      simp only [Fin.val_succ, Fin.val_castSucc]
      rw [h3.2]
      have hk : D.R.rS - k.val = (D.R.rS - (k.val + 1)) + 1 := by omega
      rw [hk, pow_succ]; ring
    · right; exact h3
  have hR := rel_loc ε e f z z' hfe (hfz u) (hfz u') (uMat (s v)) (uMat (s v)⁻¹) (uMat (γ v))
    (uMat ((γ⁻¹ * s * γ) v)) hS hSi hSiS hT (fun x y => Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.hJ_adj (s v) x y)
    hrel π hπ hP1 hP2
  rw [psiR_eq_of ε X.B.g e f z z' _ _ hR]
  exact psiR_mul_star ε X.B.g e f z' _

end Glob

end Formalism.L2.SG.Pf.Carrier.JointQuot
