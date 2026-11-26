module

public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.DiracHW
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.RhoStrict

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.IrrCh
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

theorem UpperTheory.RealTr.irrCh :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F : Fin n → Fin n → Module.End ℂ V), UF F → LocF F → ∀ ν : Wt n, hw F ν ≠ ⊥ → Dom ν ∧ ∃ (S : Submodule ℂ V) (c : FR n) (d : ℂ), FiniteDimensional ℂ S ∧ Stb F S ∧ IsCh F S 1 c ∧ d ≠ 0 ∧
      alt (rhoV n) * c = d • alt (ν + rhoV n) := by
  intro n V _ _ F hU hL ν hν
  obtain ⟨x, hxh, hx0⟩ := (Submodule.ne_bot_iff _).1 hν
  obtain ⟨S0, hS0f, hxS0, hS0⟩ := hL x
  set S : Submodule ℂ V := Formalism.REAL.kSpan (fun _ => true) F x with hSdef
  have hSle : S ≤ S0 := by
    intro y hy
    exact (Submodule.mem_sInf.1 hy) S0 ⟨hxS0, fun a b _ z hz => hS0 a b z hz⟩
  have hxS : x ∈ S := Submodule.mem_sInf.2 (fun T hT => hT.1)
  have hSf : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hSle
  have hSs : Stb F S := by
    intro a b y hy
    exact Submodule.mem_sInf.2 (fun T hT => hT.2 a b rfl y (Submodule.mem_sInf.1 hy T hT))
  have hD : Dom ν := hwDom n V F hU S hSf hSs ν x hxS hx0 hxh
  obtain ⟨c, hc⟩ := chEx n V F hU S hSf hSs 1
  have hCm : Cm F S 1 := ⟨fun a b => by rw [one_mul, mul_one], fun y hy => by simpa using hy⟩
  have hKR : Formalism.REAL.KRel (fun _ => true) F := Formalism.REAL.glRel_kRel _ F hU.gl
  have hKU : Formalism.REAL.KUnit (fun _ => true) F := fun a b _ y z => hU.unit a b y z
  have hoth : ∀ μ : Wt n, μ ≠ ν → hw F μ ⊓ S = ⊥ := by
    intro μ hμ
    rw [eq_bot_iff]
    intro y hy
    rw [Submodule.mem_bot]
    rcases Formalism.REAL.kHiUniq V n (fun _ => true) F ν μ x y hKR hKU hxh hy.2 hy.1 with h | h
    · exact h
    · exact absurd h.1 hμ
  have key := wcfIso n V F hU S hSf hSs 1 c ν hCm hc hoth
  have hIf : FiniteDimensional ℂ (hw F ν ⊓ S : Submodule ℂ V) :=
    Submodule.finiteDimensional_of_le (inf_le_right : hw F ν ⊓ S ≤ S)
  have htr : trOn (hw F ν ⊓ S) (1 : Module.End ℂ V) = (Module.finrank ℂ (hw F ν ⊓ S : Submodule ℂ V) : ℂ) :=
    (trAdd V (1 : Module.End ℂ V)).2.2.2 _ hIf
  refine ⟨hD, S, c, trOn (hw F ν ⊓ S) 1, hSf, hSs, hc, ?_, key⟩
  rw [htr, Nat.cast_ne_zero]
  intro h0
  rw [Submodule.finrank_eq_zero] at h0
  have : x ∈ hw F ν ⊓ S := ⟨hxh, hxS⟩
  rw [h0, Submodule.mem_bot] at this
  exact hx0 this
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.DiracCh
section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifEx
section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.SgMulSelf
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

namespace UpperTheory.RealTr.CartanExamples

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private def sg (key : ι → ℕ) (i : ι) (A : Finset ι) : ℂ :=
  (-1) ^ (A.filter fun j => key j < key i).card

private def tw (key : ι → ℕ) (i j : ι) : ℂ := if key j < key i then -1 else 1

private theorem tw_self (key : ι → ℕ) (i : ι) : tw key i i = 1 := by simp [tw]

private theorem tw_mul_self (key : ι → ℕ) (i j : ι) : tw key i j * tw key i j = 1 := by
  unfold tw
  split_ifs <;> norm_num

private theorem tw_swap {key : ι → ℕ} (hk : Function.Injective key) {i j : ι} (h : i ≠ j) :
    tw key j i = -tw key i j := by
  have hne : key i ≠ key j := fun e => h (hk e)
  rcases lt_or_gt_of_ne hne with h1 | h1 <;> simp [tw, h1, lt_asymm h1]

private theorem sg_mul_self (key : ι → ℕ) (i : ι) (A : Finset ι) :
    sg key i A * sg key i A = 1 := by
  unfold sg
  rw [← mul_pow]
  norm_num

private theorem star_sg (key : ι → ℕ) (i : ι) (A : Finset ι) :
    star (sg key i A) = sg key i A := by
  unfold sg
  simp

private theorem sg_insert (key : ι → ℕ) (i : ι) {j : ι} {A : Finset ι} (h : j ∉ A) :
    sg key i (insert j A) = tw key i j * sg key i A := by
  unfold sg tw
  rw [Finset.filter_insert]
  split_ifs with hk
  · rw [Finset.card_insert_of_notMem (fun hm => h (Finset.mem_filter.1 hm).1), pow_succ]; ring
  · simp

private theorem sg_erase (key : ι → ℕ) (i : ι) {j : ι} {A : Finset ι} (h : j ∈ A) :
    sg key i (A.erase j) = tw key i j * sg key i A := by
  have h1 := sg_insert key i (Finset.notMem_erase j A)
  rw [Finset.insert_erase h] at h1
  rw [h1, ← mul_assoc, tw_mul_self, one_mul]

private def al (key : ι → ℕ) (i : ι) : Matrix (Finset ι) (Finset ι) ℂ :=
  Matrix.of fun A A' => if i ∉ A ∧ A' = insert i A then sg key i A else 0

private theorem al_mul (key : ι → ℕ) (i : ι) (M : Matrix (Finset ι) (Finset ι) ℂ) (A B : Finset ι) :
    (al key i * M) A B = if i ∈ A then 0 else sg key i A * M (insert i A) B := by
  rw [Matrix.mul_apply]
  simp only [al, Matrix.of_apply]
  split_ifs with hi
  · simp [hi]
  · simp [hi]

private theorem alH_mul (key : ι → ℕ) (i : ι) (M : Matrix (Finset ι) (Finset ι) ℂ)
    (A B : Finset ι) :
    ((al key i)ᴴ * M) A B = if i ∈ A then sg key i A * M (A.erase i) B else 0 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, al, Matrix.of_apply]
  split_ifs with hi
  · rw [Finset.sum_eq_single (A.erase i)]
    · rw [if_pos ⟨Finset.notMem_erase i A, (Finset.insert_erase hi).symm⟩, star_sg,
        sg_erase key i hi, tw_self, one_mul]
    · intro A' _ hA'
      rw [if_neg, star_zero, zero_mul]
      rintro ⟨h1, rfl⟩
      exact hA' (Finset.erase_insert h1).symm
    · intro hm
      exact absurd (Finset.mem_univ _) hm
  · apply Finset.sum_eq_zero
    intro A' _
    rw [if_neg, star_zero, zero_mul]
    rintro ⟨_, rfl⟩
    exact hi (Finset.mem_insert_self i A')

private theorem ann_ann {key : ι → ℕ} (hk : Function.Injective key) (i j : ι)
    (M : Matrix (Finset ι) (Finset ι) ℂ) :
    al key i * (al key j * M) + al key j * (al key i * M) = 0 := by
  ext A B
  simp only [Matrix.add_apply, Matrix.zero_apply, al_mul]
  by_cases hij : i = j
  · subst hij
    simp
  have hji : j ≠ i := fun e => hij e.symm
  by_cases hi : i ∈ A
  · simp [hi]
  by_cases hj : j ∈ A
  · simp [hj]
  simp only [hi, hj, Finset.mem_insert, hij, hji, or_self, if_false]
  rw [sg_insert key j hi, sg_insert key i hj, tw_swap hk hij, Finset.insert_comm j i]
  ring

private theorem ann_cre {key : ι → ℕ} (hk : Function.Injective key) (i j : ι)
    (M : Matrix (Finset ι) (Finset ι) ℂ) :
    al key i * ((al key j)ᴴ * M) + (al key j)ᴴ * (al key i * M) = if i = j then M else 0 := by
  ext A B
  simp only [Matrix.add_apply, al_mul, alH_mul]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    by_cases hi : i ∈ A
    · rw [if_pos hi, if_pos hi, if_neg (Finset.notMem_erase i A), Finset.insert_erase hi,
        sg_erase key i hi, tw_self, zero_add]
      linear_combination M A B * sg_mul_self key i A
    · rw [if_neg hi, if_neg hi, if_pos (Finset.mem_insert_self i A), Finset.erase_insert hi,
        sg_insert key i hi, tw_self, add_zero]
      linear_combination M A B * sg_mul_self key i A
  rw [if_neg hij, Matrix.zero_apply]
  by_cases hi : i ∈ A
  · rw [if_pos hi, zero_add, if_pos (Finset.mem_erase.2 ⟨hij, hi⟩)]
    simp
  by_cases hj : j ∈ A
  · rw [if_neg hi, if_pos (Finset.mem_insert_of_mem hj), if_pos hj,
      if_neg (fun hm => hi (Finset.mem_of_mem_erase hm)), sg_insert key j hi, sg_erase key i hj,
      tw_swap hk hij, Finset.erase_insert_of_ne hij]
    ring
  · have h1 : j ∉ insert i A := fun hm => (Finset.mem_insert.1 hm).elim (fun e => hij e.symm) hj
    rw [if_neg hi, if_neg h1, if_neg hj]
    simp

private theorem cre_ann (key : ι → ℕ) (i : ι) :
    (al key i)ᴴ * al key i = Matrix.diagonal fun A => if i ∈ A then 1 else 0 := by
  ext A B
  rw [alH_mul, Matrix.diagonal_apply]
  simp only [al, Matrix.of_apply]
  by_cases hi : i ∈ A
  · rw [if_pos hi, if_pos hi, Finset.insert_erase hi, sg_erase key i hi, tw_self, one_mul]
    by_cases hAB : A = B
    · subst hAB
      rw [if_pos ⟨Finset.notMem_erase i A, rfl⟩, if_pos rfl, sg_mul_self]
    · rw [if_neg (fun hc => hAB hc.2.symm), if_neg hAB, mul_zero]
  · rw [if_neg hi, if_neg hi]
    simp

end UpperTheory.RealTr.CartanExamples

open UpperTheory.RealTr.CartanExamples in
theorem UpperTheory.RealTr.carEx :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι], ∃ α : ι → Matrix (Finset ι) (Finset ι) ℂ, (∀ i j, α i * α j + α j * α i = 0) ∧
      (∀ i j, α i * (α j)ᴴ + (α j)ᴴ * α i = if i = j then 1 else 0) ∧ ∀ i, (α i)ᴴ * α i = Matrix.diagonal fun A => if i ∈ A then 1 else 0 := by
  intro ι _ _
  let key : ι → ℕ := fun i => (Fintype.equivFin ι i : ℕ)
  have hk : Function.Injective key := fun a b h => (Fintype.equivFin ι).injective (Fin.ext h)
  refine ⟨al key, fun i j => ?_, fun i j => ?_, cre_ann key⟩
  · simpa using ann_ann hk i j 1
  · simpa using ann_cre hk i j 1
end
end

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

namespace UpperTheory.RealTr.ClifP

variable {n : ℕ}

private abbrev Io (n : ℕ) : Type := {p : Fin n × Fin n // p.1 ≤ p.2}

private abbrev Mt (n : ℕ) : Type := Matrix (Finset (Io n)) (Finset (Io n)) ℂ

private def rr : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

private lemma rr_sq : rr * rr = 1 / 2 := by
  unfold rr
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

private lemma rr_conj : star rr = rr := by
  unfold rr
  rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]

private def pr (a b : Fin n) : Io n := ⟨(min a b, max a b), min_le_max⟩

private lemma pr_comm (a b : Fin n) : pr a b = pr b a := by
  unfold pr
  simp only [min_comm a b, max_comm a b]

private def cs (a b : Fin n) : ℂ := if a < b then 0 else if b < a then 1 else rr

private lemma cs_conj (a b : Fin n) : star (cs a b) = cs a b := by
  unfold cs; split_ifs <;> simp [rr_conj]

private lemma cs_lt {a b : Fin n} (h : a < b) : cs a b = 0 := by simp [cs, h]
private lemma cs_gt {a b : Fin n} (h : b < a) : cs a b = 1 := by
  simp [cs, h, not_lt.mpr h.le]

private def cM (α : Io n → Mt n) (a b : Fin n) : Mt n :=
  cs a b • α (pr a b) + cs b a • (α (pr a b))ᴴ

private lemma anti {R : Type} [Ring R] [Algebra ℂ R] (u u' v v' e : R) (s t s' t' : ℂ)
    (h1 : u * u' + u' * u = 0) (h2 : u * v' + v' * u = e) (h3 : v * u' + u' * v = e)
    (h4 : v * v' + v' * v = 0) :
    (s • u + t • v) * (s' • u' + t' • v') + (s' • u' + t' • v') * (s • u + t • v)
      = (s * t' + t * s') • e := by
  calc (s • u + t • v) * (s' • u' + t' • v') + (s' • u' + t' • v') * (s • u + t • v)
      = (s * s') • (u * u' + u' * u) + (s * t') • (u * v' + v' * u)
        + (t * s') • (v * u' + u' * v) + (t * t') • (v * v' + v' * v) := by
        simp only [add_mul, mul_add, smul_mul_smul_comm, smul_add, mul_comm s' s, mul_comm t' t,
          mul_comm s' t, mul_comm t' s]
        abel
    _ = (s * t' + t * s') • e := by
        rw [h1, h2, h3, h4, smul_zero, smul_zero, zero_add, add_zero, add_smul]

private lemma comb1 (a b d e : Fin n) (h : pr a b = pr d e) :
    cs a b * cs e d + cs b a * cs d e = if b = d ∧ a = e then 1 else 0 := by
  simp only [pr, Subtype.mk.injEq, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  rw [min_def, min_def] at h1
  rw [max_def, max_def] at h2
  unfold cs
  split_ifs at h1 h2 <;> split_ifs <;> first | omega | (simp_all [rr_sq]; done) | (simp_all [rr_sq]; norm_num)

private lemma relC (α : Io n → Mt n) (h1 : ∀ i j, α i * α j + α j * α i = 0)
    (h2 : ∀ i j, α i * (α j)ᴴ + (α j)ᴴ * α i = if i = j then 1 else 0) : Clif (cM α) := by
  intro a b d e
  have k2 : α (pr a b) * (α (pr d e))ᴴ + (α (pr d e))ᴴ * α (pr a b)
      = if pr a b = pr d e then 1 else 0 := h2 _ _
  have k3 : (α (pr a b))ᴴ * α (pr d e) + α (pr d e) * (α (pr a b))ᴴ
      = if pr a b = pr d e then 1 else 0 := by
    rw [add_comm, h2]
    simp only [eq_comm]
  have k4 : (α (pr a b))ᴴ * (α (pr d e))ᴴ + (α (pr d e))ᴴ * (α (pr a b))ᴴ = 0 := by
    have := congrArg Matrix.conjTranspose (h1 (pr d e) (pr a b))
    simpa [Matrix.conjTranspose_add, Matrix.conjTranspose_mul] using this
  unfold cM
  rw [anti _ _ _ _ _ _ _ _ _ (h1 _ _) k2 k3 k4]
  by_cases hp : pr a b = pr d e
  · rw [comb1 a b d e hp, if_pos hp]
    split_ifs <;> simp
  · rw [if_neg hp, smul_zero, if_neg]
    rintro ⟨rfl, rfl⟩
    exact hp (pr_comm _ _)

private lemma adjC (α : Io n → Mt n) (a b : Fin n) : (cM α a b)ᴴ = cM α b a := by
  unfold cM
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_conjTranspose, cs_conj, cs_conj, pr_comm b a, add_comm]

private def sg (a d : Fin n) : ℝ := (if a < d then 1 else 0) - (if d < a then 1 else 0)

private def eta (A : Finset (Io n)) : Wt n := -rhoV n + ∑ i ∈ A, rt i.1.1 i.1.2

private lemma sg_sum (a : Fin n) : ∑ d, sg a d = 2 * rhoV n a := by
  simp only [sg, Finset.sum_sub_distrib, Finset.sum_boole]
  rw [Finset.filter_lt_eq_Ioi, Finset.filter_gt_eq_Iio, Fin.card_Ioi, Fin.card_Iio]
  simp only [rhoV]
  have := a.isLt
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring

private lemma rt_eq (i : Io n) (a : Fin n) :
    rt i.1.1 i.1.2 a = ∑ d, if pr a d = i then sg a d else 0 := by
  obtain ⟨⟨p, q⟩, hpq⟩ := i
  dsimp only at hpq
  simp only [pr, Subtype.mk.injEq, Prod.mk.injEq, rt, Pi.sub_apply, Pi.single_apply]
  rw [Finset.sum_eq_single_of_mem (if a = p then q else p) (Finset.mem_univ _)]
  · simp only [sg, min_def, max_def]
    split_ifs <;> first | omega | norm_num
  · intro d _ hd
    simp only [sg, min_def, max_def]
    split_ifs at hd <;> split_ifs <;> first | rfl | omega | norm_num

private lemma sgN (A : Finset (Io n)) (a : Fin n) :
    ∑ d, sg a d * (if pr a d ∈ A then 1 else 0) = ∑ i ∈ A, rt i.1.1 i.1.2 a := by
  simp_rw [rt_eq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [Finset.sum_ite_eq]
  split_ifs <;> simp

private lemma Dlt (α : Io n → Mt n)
    (h3 : ∀ i, (α i)ᴴ * α i = Matrix.diagonal fun A => if i ∈ A then 1 else 0)
    {a d : Fin n} (h : a < d) :
    cM α a d * cM α d a = Matrix.diagonal fun A => if pr a d ∈ A then 1 else 0 := by
  unfold cM
  rw [cs_lt h, cs_gt h, pr_comm d a]
  simp only [zero_smul, one_smul, zero_add, add_zero]
  exact h3 _

private lemma Dall (α : Io n → Mt n) (hc : Clif (cM α))
    (h3 : ∀ i, (α i)ᴴ * α i = Matrix.diagonal fun A => if i ∈ A then 1 else 0)
    (a d : Fin n) :
    cM α a d * cM α d a = Matrix.diagonal fun A =>
      1 / 2 + (sg a d : ℂ) * ((if pr a d ∈ A then 1 else 0) - 1 / 2) := by
  rcases lt_trichotomy a d with h | h | h
  · rw [Dlt α h3 h]
    congr 1
    funext A
    simp [sg, h, not_lt.mpr h.le]
  · subst h
    have hcl := hc a a a a
    simp only [and_self, if_true] at hcl
    have hX : cM α a a * cM α a a = (1 / 2 : ℂ) • (1 : Mt n) := by
      have h2 : (2 : ℂ) • (cM α a a * cM α a a) = 1 := by
        rw [two_smul]
        exact hcl
      calc cM α a a * cM α a a = (1 / 2 : ℂ) • ((2 : ℂ) • (cM α a a * cM α a a)) := by
            rw [smul_smul]
            norm_num
        _ = _ := by rw [h2]
    rw [hX]
    ext i j
    simp [Matrix.diagonal_apply, Matrix.one_apply, sg]
  · have hcl := hc a d d a
    simp only [and_self, if_true] at hcl
    have e := Dlt α h3 h
    have hs : cM α a d * cM α d a = 1 - cM α d a * cM α a d := eq_sub_of_add_eq hcl
    rw [hs, e, pr_comm d a]
    ext i j
    simp [Matrix.diagonal_apply, Matrix.one_apply, sg, h, not_lt.mpr h.le]
    split_ifs <;> norm_num

private lemma diagC (α : Io n → Mt n) (hc : Clif (cM α))
    (h3 : ∀ i, (α i)ᴴ * α i = Matrix.diagonal fun A => if i ∈ A then 1 else 0) (a : Fin n) :
    spn (cM α) a a = Matrix.diagonal fun A => ((eta A a : ℝ) : ℂ) := by
  have key : ∀ A : Finset (Io n), (∑ d, ((1 / 2 : ℂ) + (sg a d : ℂ) * ((if pr a d ∈ A then 1 else 0) - 1 / 2)))
      - (n : ℂ) / 2 = ((eta A a : ℝ) : ℂ) := by
    intro A
    have c1 : ∑ d, (sg a d : ℂ) = 2 * (rhoV n a : ℂ) := by
      have := congrArg (fun x : ℝ => (x : ℂ)) (sg_sum a)
      push_cast at this
      exact this
    have c2 : ∑ d, (sg a d : ℂ) * (if pr a d ∈ A then 1 else 0)
        = ((∑ i ∈ A, rt i.1.1 i.1.2 a : ℝ) : ℂ) := by
      rw [← sgN A a]
      push_cast
      refine Finset.sum_congr rfl (fun d _ => ?_)
      split_ifs <;> simp
    have e : eta A a = -rhoV n a + ∑ i ∈ A, rt i.1.1 i.1.2 a := by
      simp [eta, Finset.sum_apply]
    rw [e]
    push_cast
    push_cast at c2
    simp only [Finset.sum_add_distrib, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, c1, c2,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  unfold spn
  simp only [if_true]
  simp_rw [Dall α hc h3 a]
  ext i j
  simp only [Matrix.sub_apply, Matrix.sum_apply, Matrix.diagonal_apply, Matrix.algebraMap_matrix_apply]
  split_ifs with hij
  · subst hij
    exact key i
  · simp

private lemma ex_sum {κ : Type} (s : Finset κ) (f : κ → Wt n) :
    ex (∑ i ∈ s, f i) = ∏ i ∈ s, ex (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (cfBasic n).2.1
  | insert a s ha ih => rw [sum_insert ha, prod_insert ha, (cfBasic n).1, ih]

private lemma chrC : ∑ A : Finset (Io n), ex (eta A) = (2 : ℂ) ^ n • chR n := by
  obtain ⟨hadd, h0, -⟩ := cfBasic n
  obtain ⟨-, -, -, -, -, -, -, hw, hwB⟩ := chRF n
  have s1 : ∀ A : Finset (Io n), ex (eta A) = ex (-rhoV n) * ∏ i ∈ A, ex (rt i.1.1 i.1.2) := by
    intro A
    rw [eta, hadd, ex_sum]
  simp_rw [s1]
  rw [← Finset.mul_sum, ← Finset.powerset_univ, ← Finset.prod_one_add,
    ← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i : Io n => i.1.1 = i.1.2)]
  have hcard' : (Finset.univ.filter (fun i : Io n => i.1.1 = i.1.2)).card
      = (Finset.univ : Finset (Fin n)).card := by
    refine Finset.card_nbij' (fun i => i.1.1) (fun a => ⟨(a, a), le_refl a⟩) ?_ ?_ ?_ ?_
    · intro i _
      simp
    · intro a _
      simp
    · intro i hi
      have h := (Finset.mem_filter.mp hi).2
      apply Subtype.ext
      ext <;> simp [h]
    · intro a _
      rfl
  have hcard : (Finset.univ.filter (fun i : Io n => i.1.1 = i.1.2)).card = n := by
    rw [hcard', Finset.card_univ, Fintype.card_fin]
  have d1 : ∏ i ∈ Finset.univ.filter (fun i : Io n => i.1.1 = i.1.2), (1 + ex (rt i.1.1 i.1.2))
      = (2:ℂ) ^ n • (1 : FR n) := by
    rw [Finset.prod_congr rfl (g := fun _ => (1 : FR n) + 1)]
    · rw [Finset.prod_const, hcard, ← two_mul, mul_one]
      rw [show (2 : FR n) = (2:ℂ) • (1 : FR n) by rw [two_smul, one_add_one_eq_two]]
      rw [smul_pow, one_pow]
    · intro i hi
      have h := (Finset.mem_filter.mp hi).2
      rw [h]
      simp [rt, h0]
  have d2 : ∏ i ∈ Finset.univ.filter (fun i : Io n => ¬ i.1.1 = i.1.2), (1 + ex (rt i.1.1 i.1.2))
      = ∏ p ∈ posP n, (1 + ex (rt p.1 p.2)) := by
    refine Finset.prod_nbij' (fun i => i.1) (fun p => pr p.1 p.2) ?_ ?_ ?_ ?_ ?_
    · intro i hi
      have h := (Finset.mem_filter.mp hi).2
      simp only [posP, Finset.mem_filter, Finset.mem_univ, true_and]
      exact lt_of_le_of_ne i.2 h
    · intro p hp
      simp only [posP, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp [pr, min_eq_left hp.le, max_eq_right hp.le, hp.ne]
    · intro i hi
      apply Subtype.ext
      simp [pr, min_eq_left i.2, max_eq_right i.2]
    · intro p hp
      simp only [posP, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp [pr, min_eq_left hp.le, max_eq_right hp.le]
    · intro i _
      rfl
  rw [d1, d2]
  have d3 : ∏ p ∈ posP n, (1 + ex (rt p.1 p.2))
      = ex (wtB (posP n)) * ∏ p ∈ posP n, (1 + ex (-rt p.1 p.2)) := by
    rw [hwB, ex_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun p _ => ?_)
    rw [mul_add, mul_one, ← hadd, add_neg_cancel, h0, add_comm]
  rw [d3, hw]
  unfold chR
  rw [smul_mul_assoc, one_mul, mul_smul_comm, ← mul_assoc, ← hadd]
  congr 3
  rw [two_smul]
  abel

end UpperTheory.RealTr.ClifP

theorem UpperTheory.RealTr.clifEx :
    ∀ n : ℕ, ∃ (J : Type) (_ : Fintype J) (_ : DecidableEq J) (c : Fin n → Fin n → Matrix J J ℂ) (η : J → Wt n), ClifMod c η := by
  intro n
  obtain ⟨α, h1, h2, h3⟩ := carEx (ClifP.Io n)
  exact ⟨Finset (ClifP.Io n), inferInstance, inferInstance, ClifP.cM α, ClifP.eta,
    ⟨ClifP.relC α h1 h2, ClifP.adjC α, ClifP.diagC α (ClifP.relC α h1 h2) h3, ClifP.chrC⟩⟩
end
end

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

theorem UpperTheory.RealTr.diracCh :
    ∀ (n : ℕ) (lam : Fin n → ℤ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
      IsPair E1 E2 → LocF (kF E1 E2) → (∀ m (x : V), gelA E1 m x = GlobalTheory.Dec.gelfVal (infOf lam true) m • x) →
      (∀ m (x : V), gelA (barF E2) m x = GlobalTheory.Dec.gelfVal (infOf lam false) m • x) → ∀ ν x : Wt n, hwSp E1 E2 ν ≠ ⊥ → StrictAnti x → cf (chR n * alt (ν + rhoV n)) x ≠ 0 → LSq lam ≤ nsq x := by
  intro n lam V _ _ E1 E2 hP hL h1 h2 ν x hν hx hc
  have hGl : GlRel (kF E1 E2) := by
    intro a b c d
    have e : kF E1 E2 a b * kF E1 E2 c d - kF E1 E2 c d * kF E1 E2 a b =
        (E1 a b * E1 c d - E1 c d * E1 a b) + (E2 a b * E2 c d - E2 c d * E2 a b) := by
      simp only [kF, add_mul, mul_add]
      rw [hP.comm a b c d, hP.comm c d a b]
      abel
    rw [e, hP.gl1 a b c d, hP.gl2 a b c d]
    split_ifs <;> simp [kF] <;> abel
  have hU : UF (kF E1 E2) := ⟨hGl, hP.unitK⟩
  rw [hwSp_eq] at hν
  obtain ⟨-, S, c₀, d, hfd, hS, hch, hd, hal⟩ := irrCh n V (kF E1 E2) hU hL ν hν
  obtain ⟨J, _, _, c, η, hcl⟩ := clifEx n
  obtain ⟨S', hfd', hS', hch'⟩ := tenCh n V (kF E1 E2) hU S hfd hS J c η hcl c₀ hch
  have hU' : UF (dg (kF E1 E2) c) := (tenF n V J).2.2.2.2 (kF E1 E2) c η hU hcl
  have hm := mult n (Ten J V) (dg (kF E1 E2) c) hU' S' hfd' hS' 1 _
    ⟨fun a b => by simp, fun y hy => by simpa using hy⟩ hch' (x - rhoV n)
    (by simpa using hx)
  have key : alt (rhoV n) * (c₀ * ∑ j, ex (η j)) =
      ((2 : ℂ) ^ n * d) • (chR n * alt (ν + rhoV n)) := by
    rw [hcl.chr, mul_smul_comm, mul_smul_comm, ← mul_assoc, hal, smul_mul_assoc, smul_smul,
      mul_comm (alt (ν + rhoV n)) (chR n)]
  have hne : hw (dg (kF E1 E2) c) (x - rhoV n) ≠ ⊥ := by
    intro hb
    rw [hb, bot_inf_eq, trOn_bot, sub_add_cancel, key, ((cfBasic n).2.2.2.1 (chR n * alt (ν + rhoV n)) 0 _ x).2] at hm
    rcases mul_eq_zero.1 hm with h | h
    · exact mul_ne_zero (pow_ne_zero n two_ne_zero) hd h
    · exact hc h
  have hfin := diracHW n lam V E1 E2 hP hL h1 h2 J c η hcl (x - rhoV n) hne
  rwa [sub_add_cancel] at hfin
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.MSymm
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

theorem UpperTheory.RealTr.mSymm :
    ∀ (n : ℕ) (x y : Wt n), cf (chR n * alt x) y = cf (chR n * alt y) x := by
  intro n x y
  obtain ⟨-, -, -, -, -, -, hA, -⟩ := cfBasic n
  obtain ⟨-, -, -, hS, hN, -⟩ := chRF n
  rw [mul_comm, hA, mul_comm, hA]
  refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin n))) _ _ (fun w => ?_)
  have hs : sg (Equiv.inv (Equiv.Perm (Fin n)) w) = sg w := by
    simp [sg, Equiv.Perm.sign_inv]
  rw [hs]
  congr 1
  have hc : cf (chR n) (x - y ∘ ⇑((Equiv.inv (Equiv.Perm (Fin n))) w))
      = cf (chR n) ((x - y ∘ ⇑((Equiv.inv (Equiv.Perm (Fin n))) w)) ∘ ⇑w) :=
    (hS w _).symm
  rw [hc, ← hN]
  congr 1
  ext i
  simp [Function.comp_def, sub_eq_add_neg, add_comm]
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Conclusion2
section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.DivSupp
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem character_support_pairing_le_of_strict_anti {n : ℕ} (κ : Wt n) (χ : FR n) (hκ : Antitone κ)
    (h : alt (rhoV n) * χ = alt (κ + rhoV n)) (x : Wt n) (hx : StrictAnti x) (ξ : Wt n)
    (hξ : cf χ ξ ≠ 0) : ∑ a, x a * ξ a ≤ ∑ a, x a * κ a := by
  classical
  have hρ : StrictAnti (rhoV n) := (rearr n).2.2.1
  have hsupp : ∀ v, cf χ v ≠ 0 ↔ v ∈ χ.coeff.support := by
    intro v
    simp [cf, Finsupp.mem_support_iff]
  obtain ⟨μ, hμ, hmax⟩ := Finset.exists_max_image χ.coeff.support
    (fun v => ∑ a, x a * v a) ⟨ξ, (hsupp ξ).1 hξ⟩
  have hμ' : cf χ μ ≠ 0 := (hsupp μ).2 hμ
  have hcoef : cf (alt (rhoV n) * χ) (rhoV n + μ) = cf χ μ := by
    rw [(cfBasic n).2.2.2.2.2.2.1, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
    · have e : rhoV n + μ - rhoV n ∘ ⇑(1 : Equiv.Perm (Fin n)) = μ := by
        funext a
        simp
      rw [e]
      simp [sg]
    · intro w _ hw
      have hz : cf χ (rhoV n + μ - rhoV n ∘ ⇑w) = 0 := by
        by_contra hc
        have h1 := hmax _ ((hsupp _).1 hc)
        have h2 := (rearr n).1 x (rhoV n) hx.antitone hρ.antitone w
        simp only [Pi.add_apply, Pi.sub_apply, Function.comp_apply, mul_sub, mul_add,
          Finset.sum_add_distrib, Finset.sum_sub_distrib] at h1
        exact hw (h2.2 hx hρ (by linarith [h2.1]))
      rw [hz, mul_zero]
    · intro h1
      exact absurd (Finset.mem_univ _) h1
  rw [h] at hcoef
  obtain ⟨w, hw⟩ := (cfBasic n).2.2.2.2.2.2.2.2.2.2.1 (κ + rhoV n) (rhoV n + μ)
    (by rw [hcoef]; exact hμ')
  have hanti : Antitone (κ + rhoV n) := hκ.add hρ.antitone
  have h2 := ((rearr n).1 x (κ + rhoV n) hx.antitone hanti w).1
  have e : ∑ a, x a * (rhoV n + μ) a = ∑ a, x a * (κ + rhoV n) (w a) := by
    rw [hw]
    rfl
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib] at e h2
  have h4 : ∑ a, x a * ξ a ≤ ∑ a, x a * μ a := hmax ξ ((hsupp ξ).1 hξ)
  linarith

private theorem character_support_pairing_le_of_antitone {n : ℕ} (κ : Wt n) (χ : FR n) (hκ : Antitone κ)
    (h : alt (rhoV n) * χ = alt (κ + rhoV n)) (x : Wt n) (hx : Antitone x) (ξ : Wt n)
    (hξ : cf χ ξ ≠ 0) : ∑ a, x a * ξ a ≤ ∑ a, x a * κ a := by
  have hρ : StrictAnti (rhoV n) := (rearr n).2.2.1
  have key : ∀ ε : ℝ, 0 < ε →
      ∑ a, x a * ξ a - ∑ a, x a * κ a ≤ ε * (∑ a, rhoV n a * κ a - ∑ a, rhoV n a * ξ a) := by
    intro ε hε
    have hs : StrictAnti (fun a => x a + ε * rhoV n a) := by
      intro a b hab
      have h1 := hρ hab
      have h2 := hx hab.le
      nlinarith
    have := character_support_pairing_le_of_strict_anti κ χ hκ h _ hs ξ hξ
    simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum] at this
    linarith
  by_contra hc
  push_neg at hc
  set A := ∑ a, x a * ξ a - ∑ a, x a * κ a with hA
  set B := ∑ a, rhoV n a * κ a - ∑ a, rhoV n a * ξ a with hB
  have hA0 : 0 < A := by rw [hA]; linarith
  have ht : 0 < |B| + 1 := by positivity
  have hε : 0 < A / (2 * (|B| + 1)) := by positivity
  have k := key _ hε
  have hle : A / (2 * (|B| + 1)) * B ≤ A / (2 * (|B| + 1)) * (|B| + 1) :=
    mul_le_mul_of_nonneg_left (by linarith [le_abs_self B]) hε.le
  have heq : A / (2 * (|B| + 1)) * (|B| + 1) = A / 2 := by
    field_simp
  linarith

theorem UpperTheory.RealTr.divSupp :
    ∀ (n : ℕ) (κ : Wt n) (χ : FR n), Antitone κ → alt (rhoV n) * χ = alt (κ + rhoV n) → cf χ κ = 1 ∧ (∀ ξ, cf χ ξ ≠ 0 → Maj ξ κ) ∧
      (Sym χ → ∀ ξ, cf χ ξ ≠ 0 → nsq ξ ≤ nsq κ) := by
  intro n κ χ hκ h
  have hρ : StrictAnti (rhoV n) := (rearr n).2.2.1
  refine ⟨?_, fun ξ hξ x hx => character_support_pairing_le_of_antitone κ χ hκ h x hx ξ hξ, ?_⟩
  · have hs : StrictAnti (κ + rhoV n) := by
      intro a b hab
      have h1 := hρ hab
      have h2 := hκ hab.le
      simp only [Pi.add_apply]
      linarith
    have hcoef : cf (alt (rhoV n) * χ) (κ + rhoV n) = cf χ κ := by
      rw [(cfBasic n).2.2.2.2.2.2.1, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
      · have e : κ + rhoV n - rhoV n ∘ ⇑(1 : Equiv.Perm (Fin n)) = κ := by
          funext a
          simp
        rw [e]
        simp [sg]
      · intro w _ hw
        have hz : cf χ (κ + rhoV n - rhoV n ∘ ⇑w) = 0 := by
          by_contra hc
          have h1 := character_support_pairing_le_of_strict_anti κ χ hκ h (rhoV n) hρ _ hc
          have h2 := (rearr n).1 (rhoV n) (rhoV n) hρ.antitone hρ.antitone w
          simp only [Pi.add_apply, Pi.sub_apply, Function.comp_apply, mul_sub, mul_add,
            Finset.sum_add_distrib, Finset.sum_sub_distrib] at h1
          exact hw (h2.2 hρ hρ (by linarith [h2.1]))
        rw [hz, mul_zero]
      · intro h1
        exact absurd (Finset.mem_univ _) h1
    rw [← hcoef, h]
    exact ((cfBasic n).2.2.2.2.2.2.2.2.2.2.2.1 _ hs).1
  · intro hS ξ hξ
    obtain ⟨w, hw⟩ := ((rearr n).2.1 ξ).2.1
    have hanti : Antitone (domC ξ) := ((rearr n).2.1 ξ).1
    have hc : cf χ (domC ξ) ≠ 0 := by
      rw [hw, hS w ξ]
      exact hξ
    have h1 := character_support_pairing_le_of_antitone κ χ hκ h (domC ξ) hanti (domC ξ) hc
    have h2 := ((rearr n).2.2.2.2.2 (domC ξ) κ (by
      simp only [nsq, sq]
      exact h1)).1
    rw [((rearr n).2.1 ξ).2.2.2.2] at h2
    exact h2
end
end

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

theorem UpperTheory.RealTr.aux₃ :
    ∀ (n : ℕ) (ν : Wt n), Dom ν → cf (chR n * alt (domC (ν - rhoV n) + rhoV n)) (ν + rhoV n) = 1 := by
  intro n ν hν
  obtain ⟨hR1, hR2, hR3, -, hR5, -⟩ := rearr n
  obtain ⟨hνA, hκD⟩ := hR5 ν hν
  obtain ⟨χ, hχS, hχ⟩ := divEx n (domC (ν - rhoV n)) hκD
  obtain ⟨hκA, ⟨w0, hw0⟩, -, -, hnsq⟩ := hR2 (ν - rhoV n)
  obtain ⟨c1, -, c3⟩ := divSupp n (domC (ν - rhoV n)) χ hκA hχ
  obtain ⟨hD2, -⟩ := chRF n
  obtain ⟨-, -, -, -, -, -, hA, -⟩ := cfBasic n
  have hx : StrictAnti (ν + rhoV n) := hνA.add_strictAnti hR3
  have hm : chR n * alt (domC (ν - rhoV n) + rhoV n) = alt ((2:ℝ) • rhoV n) * χ := by
    rw [← hχ, hD2]
    ring
  rw [hm, hA]
  rw [Finset.sum_eq_single 1]
  · have e1 : ν + rhoV n - ((2:ℝ) • rhoV n) ∘ ⇑(1 : Equiv.Perm (Fin n)) = ν - rhoV n := by
      funext a
      simp only [Pi.sub_apply, Pi.add_apply, Function.comp_apply, Equiv.Perm.coe_one, id_eq,
        Pi.smul_apply, two_smul]
      ring
    rw [e1, ← hχS w0, ← hw0, c1]
    simp [sg]
  · intro w _ hw
    by_contra h
    have hne := right_ne_zero_of_mul h
    have hle := c3 hχS _ hne
    rw [hnsq] at hle
    obtain ⟨hle2, heq⟩ := hR1 (ν + rhoV n) (rhoV n) hx.antitone hR3.antitone w
    have hlt : ∑ a, (ν + rhoV n) a * rhoV n (w a) < ∑ a, (ν + rhoV n) a * rhoV n a :=
      lt_of_le_of_ne hle2 (fun h' => hw (heq hx hR3 h'))
    have hsum : ∑ a, rhoV n (w a) ^ 2 = ∑ a, rhoV n a ^ 2 := Equiv.sum_comp w (fun a => rhoV n a ^ 2)
    have hdiff : nsq (ν + rhoV n - ((2:ℝ) • rhoV n) ∘ ⇑w) - nsq (ν - rhoV n)
        = 4 * (∑ a, (ν + rhoV n) a * rhoV n a - ∑ a, (ν + rhoV n) a * rhoV n (w a))
          + 4 * (∑ a, rhoV n (w a) ^ 2 - ∑ a, rhoV n a ^ 2) := by
      simp only [nsq, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      simp only [Pi.sub_apply, Pi.add_apply, Function.comp_apply, Pi.smul_apply, two_smul]
      ring
    rw [hsum] at hdiff
    linarith
  · intro h
    exact absurd (Finset.mem_univ _) h
end
end

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem uf_kF {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {E1 E2 : Fin n → Fin n → Module.End ℂ V} (hP : IsPair E1 E2) : UF (kF E1 E2) := by
  refine ⟨?_, hP.unitK⟩
  intro a b c d
  have g1 := hP.gl1 a b c d
  have g2 := hP.gl2 a b c d
  have h3 := hP.comm a b c d
  have h4 := hP.comm c d a b
  have e : kF E1 E2 a b * kF E1 E2 c d - kF E1 E2 c d * kF E1 E2 a b =
      (E1 a b * E1 c d - E1 c d * E1 a b) + (E2 a b * E2 c d - E2 c d * E2 a b) := by
    simp only [kF, add_mul, mul_add]
    rw [h3, h4]
    abel
  rw [e, g1, g2]
  split_ifs <;> (try simp only [kF]) <;> abel

theorem UpperTheory.RealTr.diracW :
    ∀ (n : ℕ) (lam : Fin n → ℤ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
      IsPair E1 E2 → LocF (kF E1 E2) → (∀ m (x : V), gelA E1 m x = GlobalTheory.Dec.gelfVal (infOf lam true) m • x) →
      (∀ m (x : V), gelA (barF E2) m x = GlobalTheory.Dec.gelfVal (infOf lam false) m • x) → ∀ ν : Wt n, hwSp E1 E2 ν ≠ ⊥ → LSq lam ≤ spinSq ν := by
  intro n lam V _ _ E1 E2 hP hL h1 h2 ν hν
  have hν' : hw (kF E1 E2) ν ≠ ⊥ := by rwa [hwSp_eq] at hν
  have hD : Dom ν := (irrCh n V (kF E1 E2) (uf_kF hP) hL ν hν').1
  have hR := rearr n
  have hx : StrictAnti (domC (ν - rhoV n) + rhoV n) := by
    intro a b hab
    exact add_lt_add_of_le_of_lt ((hR.2.1 (ν - rhoV n)).1 hab.le) (hR.2.2.1 hab)
  have hc : cf (chR n * alt (ν + rhoV n)) (domC (ν - rhoV n) + rhoV n) ≠ 0 := by
    rw [mSymm, aux₃ n ν hD]
    exact one_ne_zero
  exact diracCh n lam V E1 E2 hP hL h1 h2 ν _ hν hx hc
