module

public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.MultTrOnBot

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.SpnCas
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

namespace UpperTheory.RealTr.SpinCasimir

variable {n : ℕ} {J : Type} [Fintype J] [DecidableEq J]

private abbrev Fm (c : Fin n → Fin n → Matrix J J ℂ) : Fin n → Fin n → Module.End ℂ (Ten J ℂ) :=
  dg (fun _ _ : Fin n => (0 : Module.End ℂ ℂ)) c

private theorem Fm_eq (c : Fin n → Fin n → Matrix J J ℂ) (a b : Fin n) :
    Fm c a b = mt ℂ (spn c a b) := by
  simp [Fm, dg]

private theorem mem_wsp (c : Fin n → Fin n → Matrix J J ℂ) (η : J → Wt n) (h : ClifMod c η)
    (μ : Wt n) (x : Ten J ℂ) : x ∈ wsp (Fm c) μ ↔ ∀ j, x j ≠ 0 → η j = μ := by
  have key : ∀ a j, (Fm c a a x) j = (η j a : ℂ) * x j := by
    intro a j
    rw [Fm_eq, h.diag a]
    simp [mt, Matrix.diagonal_apply]
  constructor
  · intro hx j hj
    funext a
    have e : (Fm c a a x) j = ((μ a : ℂ) • x) j := congrArg (fun y : Ten J ℂ => y j) (hx a)
    rw [key] at e
    have e' : (η j a : ℂ) * x j = (μ a : ℂ) * x j := by simpa using e
    exact Complex.ofReal_injective (mul_right_cancel₀ hj e')
  · intro hx a
    ext j
    rw [key]
    by_cases hj : x j = 0
    · simp [hj]
    · simp [hx j hj]

private def wEquiv (c : Fin n → Fin n → Matrix J J ℂ) (η : J → Wt n) (h : ClifMod c η) (μ : Wt n) :
    wsp (Fm c) μ ≃ₗ[ℂ] ({j // η j = μ} → ℂ) where
  toFun x := fun j => x.1 j.1
  map_add' x y := by ext j; simp
  map_smul' r x := by ext j; simp
  invFun y := ⟨WithLp.toLp 2 fun j => if hj : η j = μ then y ⟨j, hj⟩ else 0, by
    rw [mem_wsp c η h]
    intro j hj
    by_contra hc
    exact hj (by simp [hc])⟩
  left_inv x := by
    ext j
    by_cases hj : η j = μ
    · simp [hj]
    · have : x.1 j = 0 := by
        by_contra hc
        exact hj ((mem_wsp c η h μ x.1).1 x.2 j hc)
      simp [hj, this]
  right_inv y := by
    ext j
    simp [j.2]

private theorem cf_sum_ex (η : J → Wt n) (μ : Wt n) :
    cf (∑ j, ex (η j)) μ = (Fintype.card {j // η j = μ} : ℂ) := by
  classical
  simp [cf, ex, Finsupp.finsetSum_apply, Finsupp.single_apply, Fintype.card_subtype]

private theorem isCh_top (c : Fin n → Fin n → Matrix J J ℂ) (η : J → Wt n) (h : ClifMod c η) :
    IsCh (Fm c) ⊤ 1 (∑ j, ex (η j)) := by
  intro μ
  rw [cf_sum_ex, inf_top_eq, (trAdd _ 1).2.2.2 _ inferInstance,
    (wEquiv c η h μ).finrank_eq, Module.finrank_fintype_fun_eq_card]

private theorem mt_ext (M : Matrix J J ℂ) (s : ℂ) (hs : ∀ x : Ten J ℂ, mt ℂ M x = s • x) :
    M = s • (1 : Matrix J J ℂ) := by
  ext j k
  have e := congrArg (fun y : Ten J ℂ => y j) (hs (WithLp.toLp 2 (Pi.single k 1)))
  simpa [mt, Pi.single_apply, Matrix.one_apply, eq_comm] using e

private theorem cas_eq (c : Fin n → Fin n → Matrix J J ℂ) :
    Cas (Fm c) = mt ℂ (Cas (spn c)) := by
  obtain ⟨φ, hφ⟩ := (tenF n ℂ J).1
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Cas, Fm_eq, ← hφ, map_sum, map_mul]

private theorem hw_bot (c : Fin n → Fin n → Matrix J J ℂ) (η : J → Wt n) (h : ClifMod c η)
    (hU : UF (Fm c)) (μ : Wt n) (hμ : μ ≠ rhoV n) : hw (Fm c) μ ⊓ ⊤ = ⊥ := by
  rw [inf_top_eq]
  by_contra hne
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hne
  have hS : FiniteDimensional ℂ (⊤ : Submodule ℂ (Ten J ℂ)) := inferInstance
  have hStb : Stb (Fm c) ⊤ := fun _ _ _ _ => Submodule.mem_top
  have hdom : Dom μ := hwDom n _ _ hU ⊤ hS hStb μ x Submodule.mem_top hx0 hx
  obtain ⟨-, -, hρ, -, hd, -⟩ := rearr n
  have hanti : StrictAnti (μ + rhoV n) := (hd μ hdom).1.add_strictAnti hρ
  have hm := mult n _ _ hU ⊤ hS hStb 1 _ ⟨fun a b => by simp, fun _ _ => Submodule.mem_top⟩
    (isCh_top c η h) μ hanti
  have hfin : FiniteDimensional ℂ (hw (Fm c) μ ⊓ ⊤ : Submodule ℂ (Ten J ℂ)) := inferInstance
  rw [(trAdd _ 1).2.2.2 _ hfin, inf_top_eq, h.chr, mul_smul_comm, ← (chRF n).1] at hm
  have hpos : Module.finrank ℂ (hw (Fm c) μ) ≠ 0 := by
    intro h0
    exact hne (Submodule.finrank_eq_zero.1 h0)
  have h2 : StrictAnti ((2 : ℝ) • rhoV n) := fun a b hab => by
    have := hρ hab
    simp only [Pi.smul_apply, smul_eq_mul]
    linarith
  obtain ⟨-, -, -, hcf, -, -, -, -, -, -, -, htop, -⟩ := cfBasic n
  have hne2 : μ + rhoV n ≠ (2 : ℝ) • rhoV n := fun e => hμ (by
    funext a
    have := congrFun e a
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    linarith)
  rw [(hcf _ 0 _ _).2, (htop _ h2).2 _ hanti hne2, mul_zero] at hm
  exact hpos (by exact_mod_cast hm.symm)

end UpperTheory.RealTr.SpinCasimir

open UpperTheory.RealTr.SpinCasimir in
theorem UpperTheory.RealTr.spnCas :
    ∀ n : ℕ, ∀ (J : Type) [Fintype J] [DecidableEq J] (c : Fin n → Fin n → Matrix J J ℂ) (η : J → Wt n), ClifMod c η → Cas (spn c) = ((3 * nsq (rhoV n) : ℝ) : ℂ) • (1 : Matrix J J ℂ) := by
  intro n J _ _ c η h
  have hU : UF (Fm c) := (tenF n ℂ J).2.2.2.2 _ c η uf_zero h
  have hS : FiniteDimensional ℂ (⊤ : Submodule ℂ (Ten J ℂ)) := inferInstance
  have hStb : Stb (Fm c) ⊤ := fun _ _ _ _ => Submodule.mem_top
  have hiso := (isoFacts n _ _ hU ⊤ hS hStb (rhoV n) (hw_bot c η h hU)).1
  have hn : nsq (rhoV n + rhoV n) - nsq (rhoV n) = 3 * nsq (rhoV n) := by
    simp only [nsq, Pi.add_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  refine mt_ext _ _ fun x => ?_
  rw [← cas_eq, hiso x Submodule.mem_top, hn]
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.DiracAlg
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem UpperTheory.RealTr.casPK {n : ℕ} {A : Type} [Ring A] (E1 E2 : Fin n → Fin n → A) :
    Cas (fun a b => E1 a b - E2 a b) + Cas (fun a b => E1 a b + E2 a b) = 2 * (Cas E1 + Cas E2) := by
  simp only [Cas, two_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  noncomm_ring

private theorem UpperTheory.RealTr.casAdd {n : ℕ} {A : Type} [Ring A] (K s : Fin n → Fin n → A)
    (h : ∀ a b d e, K a b * s d e = s d e * K a b) :
    Cas (fun a b => K a b + s a b) = Cas K + Cas s + 2 * ∑ a, ∑ b, K a b * s b a := by
  have h1 : ∑ a, ∑ b, s a b * K b a = ∑ a, ∑ b, K a b * s b a := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => (h a b b a).symm
  have h2 : Cas (fun a b => K a b + s a b) =
      Cas K + Cas s + (∑ a, ∑ b, K a b * s b a + ∑ a, ∑ b, s a b * K b a) := by
    simp only [Cas, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    noncomm_ring
  rw [h2, h1, two_mul]

private theorem UpperTheory.RealTr.dd1 {n : ℕ} {A : Type} [Ring A] (u : Fin n → Fin n → A) :
    (∑ a, ∑ b, u a b) * (∑ a, ∑ b, u a b) = ∑ a, ∑ b, ∑ d, ∑ e, u a b * u d e := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.mul_sum]

private theorem UpperTheory.RealTr.dd2 {n : ℕ} {A : Type} [Ring A] (u : Fin n → Fin n → A) :
    (∑ a, ∑ b, u a b) * (∑ a, ∑ b, u a b) = ∑ a, ∑ b, ∑ d, ∑ e, u d e * u a b := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_mul]

private theorem UpperTheory.RealTr.sum3 {n : ℕ} {A : Type} [AddCommMonoid A] (g : Fin n → Fin n → Fin n → A) :
    ∑ a, ∑ b, ∑ d, g a b d = ∑ d, ∑ b, ∑ a, g a b d := by
  calc ∑ a, ∑ b, ∑ d, g a b d = ∑ a, ∑ d, ∑ b, g a b d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ d, ∑ a, ∑ b, g a b d := Finset.sum_comm
    _ = ∑ d, ∑ b, ∑ a, g a b d := Finset.sum_congr rfl fun d _ => Finset.sum_comm

private theorem UpperTheory.RealTr.sumSpn {n : ℕ} {A : Type} [Ring A] [Algebra ℂ A] (c : Fin n → Fin n → A)
    (x y : Fin n) :
    ∑ z, c x z * c z y = spn c x y + if x = y then algebraMap ℂ A ((n : ℂ) / 2) else 0 := by
  simp only [spn, sub_add_cancel]

private theorem UpperTheory.RealTr.sumSwap {n : ℕ} {A : Type} [Ring A] [Algebra ℂ A] (c : Fin n → Fin n → A)
    (hc : Clif c) (x y : Fin n) :
    ∑ z, c z x * c y z = (if x = y then (n : A) else 0) -
      (spn c y x + if y = x then algebraMap ℂ A ((n : ℂ) / 2) else 0) := by
  rw [← UpperTheory.RealTr.sumSpn, eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
  have h : ∀ z, c z x * c y z + c y z * c z x = if x = y then 1 else 0 := by
    intro z
    rw [hc z x y z]
    simp
  simp only [h]
  by_cases hxy : x = y <;> simp [hxy]

private theorem UpperTheory.RealTr.dCore {n : ℕ} {A : Type} [Ring A] [Algebra ℂ A]
    (P K c : Fin n → Fin n → A)
    (hPP : ∀ a b d e, P a b * P d e - P d e * P a b =
      (if b = d then K a e else 0) - (if e = a then K d b else 0))
    (hPc : ∀ a b d e, P a b * c d e = c d e * P a b)
    (hc : Clif c) :
    2 * ((∑ a, ∑ b, P a b * c b a) * ∑ a, ∑ b, P a b * c b a) =
      Cas P - 2 * ∑ a, ∑ b, K a b * spn c b a := by
  have hmul : ∀ a b d e, (P a b * c b a) * (P d e * c e d) = P a b * P d e * (c b a * c e d) := by
    intro a b d e
    calc P a b * c b a * (P d e * c e d) = P a b * (c b a * P d e) * c e d := by
          simp only [mul_assoc]
      _ = P a b * (P d e * c b a) * c e d := by rw [hPc d e b a]
      _ = _ := by simp only [mul_assoc]
  have hpt : ∀ a b d e, (P a b * c b a) * (P d e * c e d) + (P d e * c e d) * (P a b * c b a) =
      (if a = e then (if b = d then P a b * P d e else 0) else 0)
      - (if b = d then K a e * (c e d * c b a) else 0)
      + (if e = a then K d b * (c e d * c b a) else 0) := by
    intro a b d e
    have h1 := hc b a e d
    have h3 : P d e * P a b = P a b * P d e -
        ((if b = d then K a e else 0) - (if e = a then K d b else 0)) := by
      rw [← hPP a b d e]; abel
    have h4 : P a b * P d e * (c b a * c e d) + P d e * P a b * (c e d * c b a) =
        P a b * P d e * (c b a * c e d + c e d * c b a) -
          ((if b = d then K a e else 0) - (if e = a then K d b else 0)) * (c e d * c b a) := by
      rw [h3, sub_mul, mul_add]; abel
    rw [hmul, hmul, h4, h1]
    by_cases hae : a = e <;> by_cases hbd : b = d <;> simp [hae, hbd, sub_mul, eq_comm] <;> abel
  have hS1 : ∑ a, ∑ b, ∑ d, ∑ e, (if a = e then (if b = d then P a b * P d e else 0) else 0) = Cas P := by
    simp [Cas, Finset.sum_ite_eq]
  have hS2 : ∑ a, ∑ b, ∑ d, ∑ e, (if b = d then K a e * (c e d * c b a) else 0) =
      ∑ a, ∑ b, K a b * (spn c b a + if b = a then algebraMap ℂ A ((n : ℂ) / 2) else 0) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    calc ∑ b, ∑ d, ∑ e, (if b = d then K a e * (c e d * c b a) else 0)
        = ∑ b, ∑ e, K a e * (c e b * c b a) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_comm]
          simp
      _ = ∑ e, ∑ b, K a e * (c e b * c b a) := Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [← Finset.mul_sum, UpperTheory.RealTr.sumSpn]
  have hS3 : ∑ a, ∑ b, ∑ d, ∑ e, (if e = a then K d b * (c e d * c b a) else 0) =
      ∑ a, ∑ b, K a b * ((if a = b then (n : A) else 0) -
        (spn c b a + if b = a then algebraMap ℂ A ((n : ℂ) / 2) else 0)) := by
    calc ∑ a, ∑ b, ∑ d, ∑ e, (if e = a then K d b * (c e d * c b a) else 0)
        = ∑ a, ∑ b, ∑ d, K d b * (c a d * c b a) := by simp
      _ = ∑ d, ∑ b, ∑ a, K d b * (c a d * c b a) := UpperTheory.RealTr.sum3 _
      _ = _ := by
          refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun b _ => ?_
          rw [← Finset.mul_sum, UpperTheory.RealTr.sumSwap c hc]
  have hhalf : algebraMap ℂ A ((n : ℂ) / 2) + algebraMap ℂ A ((n : ℂ) / 2) = (n : A) := by
    rw [← map_add (f := _), add_halves, map_natCast]
  have hfin : ∑ a, ∑ b, K a b * (spn c b a + if b = a then algebraMap ℂ A ((n : ℂ) / 2) else 0) -
      ∑ a, ∑ b, K a b * ((if a = b then (n : A) else 0) -
        (spn c b a + if b = a then algebraMap ℂ A ((n : ℂ) / 2) else 0)) =
      2 * ∑ a, ∑ b, K a b * spn c b a := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have hi : (if a = b then (n : A) else 0) =
        (if b = a then algebraMap ℂ A ((n : ℂ) / 2) else 0) +
          (if b = a then algebraMap ℂ A ((n : ℂ) / 2) else 0) := by
      by_cases hab : a = b
      · simp [hab, hhalf]
      · simp [hab, Ne.symm hab]
    rw [hi]
    noncomm_ring
  calc 2 * ((∑ a, ∑ b, P a b * c b a) * ∑ a, ∑ b, P a b * c b a)
      = (∑ a, ∑ b, P a b * c b a) * (∑ a, ∑ b, P a b * c b a) +
        (∑ a, ∑ b, P a b * c b a) * (∑ a, ∑ b, P a b * c b a) := two_mul _
    _ = ∑ a, ∑ b, ∑ d, ∑ e, ((P a b * c b a) * (P d e * c e d) + (P d e * c e d) * (P a b * c b a)) := by
        nth_rewrite 1 [UpperTheory.RealTr.dd1 (fun a b => P a b * c b a)]
        rw [UpperTheory.RealTr.dd2 (fun a b => P a b * c b a)]
        simp only [Finset.sum_add_distrib]
    _ = ∑ a, ∑ b, ∑ d, ∑ e, (if a = e then (if b = d then P a b * P d e else 0) else 0)
        - ∑ a, ∑ b, ∑ d, ∑ e, (if b = d then K a e * (c e d * c b a) else 0)
        + ∑ a, ∑ b, ∑ d, ∑ e, (if e = a then K d b * (c e d * c b a) else 0) := by
        simp only [hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = _ := by
        rw [hS1, hS2, hS3, ← hfin]; abel

private theorem UpperTheory.RealTr.commSpn {n : ℕ} {A : Type} [Ring A] [Algebra ℂ A] (c : Fin n → Fin n → A)
    (x : A) (h : ∀ d e, x * c d e = c d e * x) (a b : Fin n) : x * spn c a b = spn c a b * x := by
  have h' : Commute x (spn c a b) := by
    unfold spn
    refine Commute.sub_right (Commute.sum_right _ _ _ fun d _ => Commute.mul_right (h _ _) (h _ _)) ?_
    split_ifs
    · exact Algebra.commutes _ _ |>.symm
    · exact Commute.zero_right _
  exact h'

theorem UpperTheory.RealTr.diracAlg :
    ∀ (n : ℕ) (A : Type) [Ring A] [Algebra ℂ A] (E1 E2 c : Fin n → Fin n → A), GlRel E1 → GlRel E2 → (∀ a b d e, E1 a b * E2 d e = E2 d e * E1 a b) →
      Clif c → (∀ a b d e, E1 a b * c d e = c d e * E1 a b ∧ E2 a b * c d e = c d e * E2 a b) →
      2 * ((∑ a, ∑ b, (E1 a b - E2 a b) * c b a) * ∑ a, ∑ b, (E1 a b - E2 a b) * c b a) =
        2 * (Cas E1 + Cas E2) + Cas (spn c) - Cas fun a b => E1 a b + E2 a b + spn c a b := by
  intro n A _ _ E1 E2 c h1 h2 h12 hc hEc
  have hPP : ∀ a b d e, (E1 a b - E2 a b) * (E1 d e - E2 d e) - (E1 d e - E2 d e) * (E1 a b - E2 a b) =
      (if b = d then E1 a e + E2 a e else 0) - (if e = a then E1 d b + E2 d b else 0) := by
    intro a b d e
    have h : (E1 a b - E2 a b) * (E1 d e - E2 d e) - (E1 d e - E2 d e) * (E1 a b - E2 a b) =
        (E1 a b * E1 d e - E1 d e * E1 a b) + (E2 a b * E2 d e - E2 d e * E2 a b) := by
      simp only [sub_mul, mul_sub, h12 a b d e, h12 d e a b]
      abel
    rw [h, h1 a b d e, h2 a b d e]
    split_ifs <;> abel
  have hPc : ∀ a b d e, (E1 a b - E2 a b) * c d e = c d e * (E1 a b - E2 a b) := by
    intro a b d e
    rw [sub_mul, mul_sub, (hEc a b d e).1, (hEc a b d e).2]
  have hK : ∀ a b d e, (E1 a b + E2 a b) * spn c d e = spn c d e * (E1 a b + E2 a b) := by
    intro a b d e
    refine UpperTheory.RealTr.commSpn c _ (fun d e => ?_) d e
    rw [add_mul, mul_add, (hEc a b d e).1, (hEc a b d e).2]
  have e1 : Cas (fun a b => E1 a b + E2 a b + spn c a b) =
      Cas (fun a b => E1 a b + E2 a b) + Cas (spn c) +
        2 * ∑ a, ∑ b, (E1 a b + E2 a b) * spn c b a :=
    UpperTheory.RealTr.casAdd (fun a b => E1 a b + E2 a b) (spn c) hK
  rw [UpperTheory.RealTr.dCore (fun a b => E1 a b - E2 a b) (fun a b => E1 a b + E2 a b) c hPP hPc hc, e1,
    ← UpperTheory.RealTr.casPK E1 E2]
  abel
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Gelf2
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

theorem UpperTheory.RealTr.gelf2 :
    ∀ (n : ℕ) (χ : Fin n → ℂ), GlobalTheory.Dec.gelfVal χ 2 = ∑ a, χ a ^ 2 - (nsq (rhoV n) : ℂ) := by
  intro n χ
  have hr : Formalism.QuantumDeterminants.rhoStd n = rhoV n := rfl
  rw [GlobalTheory.CasimirEigen.gelfVal_two_eq, hr, nsq]
  push_cast
  simp only [sq]
end
end

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem rhoC_true (n : ℕ) : Formalism.REAL.rhoC (fun _ : Fin n => true) = rhoV n := by
  funext a
  have h1 : (univ.filter fun b : Fin n => a < b ∧ True) = Finset.Ioi a := by
    ext b; simp
  have h2 : (univ.filter fun b : Fin n => b < a ∧ True) = Finset.Iio a := by
    ext b; simp
  have h3 : ((n - 1 - (a : ℕ) : ℕ) : ℝ) = (n : ℝ) - 1 - (a : ℕ) := by
    have := a.2
    rw [Nat.sub_sub, Nat.cast_sub (by omega)]
    push_cast
    ring
  simp only [Formalism.REAL.rhoC, rhoV, eq_self_iff_true]
  rw [h1, h2, Fin.card_Ioi, Fin.card_Iio, h3]
  ring

private theorem nsq_eq {n : ℕ} (u : Fin n → ℝ) : Formalism.REAL.nsq u = nsq u := by
  simp [Formalism.REAL.nsq, Formalism.REAL.dot, nsq, sq]

private theorem cas_map {A B : Type} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B] {n : ℕ} (φ : A →ₐ[ℂ] B)
    (F : Fin n → Fin n → A) : φ (Cas F) = Cas fun a b => φ (F a b) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Cas, map_sum, map_mul]

private theorem spn_map {A B : Type} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B] {n : ℕ} (φ : A →ₐ[ℂ] B)
    (c : Fin n → Fin n → A) (a b : Fin n) : φ (spn c a b) = spn (fun a b => φ (c a b)) a b := by
  by_cases h : a = b <;> simp [spn, map_sum, map_sub, map_mul, h]

private theorem gl_map {A B : Type} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B] {n : ℕ} (φ : A →ₐ[ℂ] B)
    {F : Fin n → Fin n → A} (h : GlRel F) : GlRel fun a b => φ (F a b) := by
  intro a b c d
  have := congrArg φ (h a b c d)
  simp only [map_sub, map_mul] at this
  rw [this]
  split_ifs <;> simp

private theorem clif_map {A B : Type} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B] {n : ℕ} (φ : A →ₐ[ℂ] B)
    {c : Fin n → Fin n → A} (h : Clif c) : Clif fun a b => φ (c a b) := by
  intro a b d e
  have := congrArg φ (h a b d e)
  simp only [map_add (f := _), map_mul] at this
  rw [this]
  split_ifs <;> simp

private theorem cas_gel {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) : Cas E = gelA E 2 := by
  simp [Cas, gelA, epow, Finset.sum_ite_eq]

private theorem cas_bar {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) : Cas E = gelA (barF E) 2 := by
  rw [← cas_gel, Cas, Cas, Finset.sum_comm]
  simp [barF]

private theorem kF_gl {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    {E1 E2 : Fin n → Fin n → Module.End ℂ V} (hP : IsPair E1 E2) : GlRel (kF E1 E2) := by
  intro a b c d
  have e1 := hP.gl1 a b c d
  have e2 := hP.gl2 a b c d
  have h : (E1 a b + E2 a b) * (E1 c d + E2 c d) - (E1 c d + E2 c d) * (E1 a b + E2 a b) =
      (E1 a b * E1 c d - E1 c d * E1 a b) + (E2 a b * E2 c d - E2 c d * E2 a b) := by
    simp only [add_mul, mul_add]
    rw [hP.comm a b c d, hP.comm c d a b]
    abel
  simp only [kF]
  rw [h, e1, e2]
  split_ifs <;> abel

private theorem gel_val {n : ℕ} (lam : Fin n → ℤ) (s : Bool) :
    GlobalTheory.Dec.gelfVal (infOf lam s) 2 =
      (((nsq fun a => (lam a : ℝ) + rhoV n a) - nsq (rhoV n) : ℝ) : ℂ) := by
  rw [gelf2]
  have : ∀ a, infOf lam s a ^ 2 = ((((lam a : ℝ) + rhoV n a) ^ 2 : ℝ) : ℂ) := by
    intro a
    cases s <;> simp [infOf, rhoV] <;> ring
  simp only [this, nsq]
  push_cast
  rfl

private theorem lsq_eq {n : ℕ} (lam : Fin n → ℤ) :
    LSq lam = 4 * nsq fun a => (lam a : ℝ) + rhoV n a := by
  simp only [LSq, nsq, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem UpperTheory.RealTr.diracHW :
    ∀ (n : ℕ) (lam : Fin n → ℤ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
      IsPair E1 E2 → LocF (kF E1 E2) → (∀ m (x : V), gelA E1 m x = GlobalTheory.Dec.gelfVal (infOf lam true) m • x) →
      (∀ m (x : V), gelA (barF E2) m x = GlobalTheory.Dec.gelfVal (infOf lam false) m • x) → ∀ (J : Type) [Fintype J] [DecidableEq J] (c : Fin n → Fin n → Matrix J J ℂ) (η : J → Wt n), ClifMod c η → ∀ κ : Wt n, hw (dg (kF E1 E2) c) κ ≠ ⊥ → LSq lam ≤ nsq (κ + rhoV n) := by
  intro n lam V _ _ E1 E2 hP _ h1 h2 J _ _ c η hC κ hκ
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hκ
  have hx' : KHighest (fun _ => true) (dg (kF E1 E2) c) κ x := hx
  obtain ⟨⟨φ, hφ⟩, hcomm, hmadj, hladj, hUF⟩ := tenF n V J
  have hUFd : UF (dg (kF E1 E2) c) := hUF _ c η ⟨kF_gl hP, hP.unitK⟩ hC
  let lfJ : Module.End ℂ V →ₐ[ℂ] Module.End ℂ (Ten J V) := lf J
  let L1 : Fin n → Fin n → Module.End ℂ (Ten J V) := fun a b => lfJ (E1 a b)
  let L2 : Fin n → Fin n → Module.End ℂ (Ten J V) := fun a b => lfJ (E2 a b)
  let C : Fin n → Fin n → Module.End ℂ (Ten J V) := fun a b => φ (c a b)
  have hD := diracAlg n (Module.End ℂ (Ten J V)) L1 L2 C (gl_map lfJ hP.gl1) (gl_map lfJ hP.gl2)
    (fun a b d e => by
      simp only [L1, L2, ← map_mul]
      rw [hP.comm a b d e])
    (clif_map φ hC.rel)
    (fun a b d e => by
      simp only [L1, L2, C, hφ]
      exact ⟨hcomm _ _, hcomm _ _⟩)
  set T : Fin n → Fin n → Module.End ℂ (Ten J V) := fun a b => (L1 a b - L2 a b) * C b a with hTdef
  set D : Module.End ℂ (Ten J V) := ∑ a, ∑ b, T a b with hDdef
  have hT : ∀ a b (y z : Ten J V), ⟪T a b y, z⟫_ℂ = -⟪y, T b a z⟫_ℂ := by
    intro a b y z
    have hP' : L1 a b - L2 a b = lfJ (pF E1 E2 a b) := by simp [L1, L2, pF, map_sub]
    have hP'' : L1 b a - L2 b a = lfJ (pF E1 E2 b a) := by simp [L1, L2, pF, map_sub]
    have hneg : ∀ u w : V, ⟪pF E1 E2 a b u, w⟫_ℂ = ⟪u, (-(pF E1 E2 b a)) w⟫_ℂ := by
      intro u w
      rw [hP.unitP a b u w]
      simp [inner_neg_right]
    simp only [hTdef, hP', hP'', Module.End.mul_apply, C, hφ]
    rw [hladj _ _ hneg, hmadj, hC.adj b a, map_neg]
    have hc := LinearMap.congr_fun (hcomm (c a b) (pF E1 E2 b a)) z
    simp only [Module.End.mul_apply] at hc
    rw [LinearMap.neg_apply, map_neg, inner_neg_right]
    exact congrArg (fun w => -⟪y, w⟫_ℂ) hc.symm
  have hskew : ∀ y z : Ten J V, ⟪D y, z⟫_ℂ = -⟪y, D z⟫_ℂ := by
    intro y z
    calc ⟪D y, z⟫_ℂ = ∑ a, ∑ b, ⟪T a b y, z⟫_ℂ := by
          simp [hDdef, LinearMap.sum_apply, sum_inner]
      _ = ∑ a, ∑ b, -⟪y, T b a z⟫_ℂ := by simp_rw [hT]
      _ = -⟪y, D z⟫_ℂ := by
          rw [Finset.sum_comm]
          simp [hDdef, LinearMap.sum_apply, inner_sum, Finset.sum_neg_distrib]
  set A0 : ℝ := nsq fun a => (lam a : ℝ) + rhoV n a with hA0
  set R : ℝ := nsq (rhoV n) with hR
  set N : ℝ := nsq (κ + rhoV n) with hN
  have g1 : GlobalTheory.Dec.gelfVal (infOf lam true) 2 = ((A0 - R : ℝ) : ℂ) := gel_val lam true
  have g2 : GlobalTheory.Dec.gelfVal (infOf lam false) 2 = ((A0 - R : ℝ) : ℂ) := gel_val lam false
  have hc1 : Cas L1 = ((A0 - R : ℝ) : ℂ) • (1 : Module.End ℂ (Ten J V)) := by
    have : Cas E1 = ((A0 - R : ℝ) : ℂ) • (1 : Module.End ℂ V) := by
      ext v
      rw [cas_gel, h1 2 v, g1]
      simp
    rw [← cas_map lfJ, this, map_smul, map_one]
  have hc2 : Cas L2 = ((A0 - R : ℝ) : ℂ) • (1 : Module.End ℂ (Ten J V)) := by
    have : Cas E2 = ((A0 - R : ℝ) : ℂ) • (1 : Module.End ℂ V) := by
      ext v
      rw [cas_bar, h2 2 v, g2]
      simp
    rw [← cas_map lfJ, this, map_smul, map_one]
  have hspn : (fun a b => spn C a b) = fun a b => φ (spn c a b) := by
    funext a b
    exact (spn_map φ c a b).symm
  have hc3 : Cas (spn C) = ((3 * R : ℝ) : ℂ) • (1 : Module.End ℂ (Ten J V)) := by
    have e : Cas (spn C) = φ (Cas (spn c)) := by
      rw [cas_map φ]
      exact congrArg Cas hspn
    rw [e, spnCas n J c η hC, map_smul, map_one]
  have hdg : (fun a b => L1 a b + L2 a b + spn C a b) = dg (kF E1 E2) c := by
    funext a b
    have : spn C a b = mt V (spn c a b) := by rw [← hφ]; exact congrFun (congrFun hspn a) b
    simp only [dg, kF, L1, L2, lfJ, map_add (f := _), this]
  have hc4 : Cas (dg (kF E1 E2) c) x = ((N - R : ℝ) : ℂ) • x := by
    have h := Formalism.REAL.kCasSpan (Ten J V) n (fun _ => true) (dg (kF E1 E2) c) κ x
      (Formalism.REAL.glRel_kRel _ _ hUFd.gl) hx' x
      (Submodule.mem_sInf.2 fun S hS => hS.1)
    have hk : Formalism.REAL.CasK (fun _ : Fin n => true) (dg (kF E1 E2) c) = Cas (dg (kF E1 E2) c) := by
      simp [Formalism.REAL.CasK, Cas]
    rw [hk] at h
    rw [h, Formalism.REAL.ckv, rhoC_true, nsq_eq, nsq_eq]
  have key : D (D x) + D (D x) = ((LSq lam - N : ℝ) : ℂ) • x := by
    rw [hdg, hc1, hc2, hc3, two_mul, two_mul] at hD
    have h := LinearMap.congr_fun hD x
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, hc4] at h
    have h' : D (D x) + D (D x) = _ := h
    rw [h', lsq_eq, ← sub_eq_zero]
    simp only [← add_smul, ← sub_smul]
    rw [← hA0]
    convert zero_smul ℂ x using 2
    push_cast
    ring
  have e : ⟪x, D (D x)⟫_ℂ = -(((‖D x‖ ^ 2 : ℝ)) : ℂ) := by
    have h := hskew x (D x)
    rw [inner_self_eq_norm_sq_to_K] at h
    rw [eq_neg_iff_add_eq_zero] at h ⊢
    rw [← h]
    push_cast
    simp
    ring
  have h3 := congrArg (fun w => ⟪x, w⟫_ℂ) key
  simp only [inner_add_right, inner_smul_right, e, inner_self_eq_norm_sq_to_K] at h3
  have h4 : -(2 * ‖D x‖ ^ 2) = (LSq lam - N) * ‖x‖ ^ 2 := by
    apply Complex.ofReal_injective
    push_cast
    push_cast at h3
    linear_combination h3
  have hx2 : 0 < ‖x‖ ^ 2 := by
    have := norm_pos_iff.2 hx0
    positivity
  by_contra hlt
  have : 0 < LSq lam - N := sub_pos.2 (not_le.1 hlt)
  have := mul_pos this hx2
  nlinarith [sq_nonneg ‖D x‖]
