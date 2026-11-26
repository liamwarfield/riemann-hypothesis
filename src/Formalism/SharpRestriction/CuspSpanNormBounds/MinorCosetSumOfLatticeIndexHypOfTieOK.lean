module

public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLitG

@[expose] public section

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.KTwoCosetCount
noncomputable section

namespace Formalism.MainNotions.KTwoCosetCount

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section A

variable {D : D7}

theorem card_ends_le (j : ℕ) (δ : ℕ → D.host.E) : (KappaEndpoints.k2ends D j δ).card ≤ j := by
  classical
  unfold KappaEndpoints.k2ends
  calc _ ≤ (Finset.Icc 1 j).card := Finset.card_filter_le _ _
    _ = j := by simp

theorem sg_rpow_le (H1 : ℝ) {j : ℕ} (hj : j ≤ D.R.rS) (δ : ℕ → D.host.E) (τ : D.what₂.Tau) :
    KappaEndpoints.k2sg D H1 j δ τ ^ (-(3 * (D.R.rS : ℝ))) ≤
      ∏ l ∈ KappaEndpoints.k2ends D j δ,
        (max 1 (absReal D.host.rdE (embS D τ) D.R.rS l (δ l) / (2 * H1) ^ (2 * D.R.rS))) ^ (-(3 : ℝ)) := by
  set σ := KappaEndpoints.k2sg D H1 j δ τ with hσ
  have h1 : 1 ≤ σ := KappaEndpoints.one_le_minor_sigma H1 j δ τ
  have hle : ∀ l ∈ KappaEndpoints.k2ends D j δ,
      max 1 (absReal D.host.rdE (embS D τ) D.R.rS l (δ l) / (2 * H1) ^ (2 * D.R.rS)) ≤ σ := by
    intro l hl
    refine max_le h1 ?_
    rw [hσ]
    unfold KappaEndpoints.k2sg
    exact (Finset.le_fold_max _).2 (Or.inr ⟨l, hl, le_rfl⟩)
  have step1 : ∏ l ∈ KappaEndpoints.k2ends D j δ, σ ^ (-(3 : ℝ)) ≤
      ∏ l ∈ KappaEndpoints.k2ends D j δ,
        (max 1 (absReal D.host.rdE (embS D τ) D.R.rS l (δ l) / (2 * H1) ^ (2 * D.R.rS))) ^ (-(3 : ℝ)) := by
    apply Finset.prod_le_prod₀
    · intro l _; exact Real.rpow_nonneg (by linarith) _
    · intro l hl
      exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le one_pos (le_max_left _ _)) (hle l hl) (by norm_num)
  have hc := card_ends_le (D := D) j δ
  have step0 : σ ^ (-(3 * (D.R.rS : ℝ))) ≤ ∏ l ∈ KappaEndpoints.k2ends D j δ, σ ^ (-(3 : ℝ)) := by
    rw [Finset.prod_const, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    apply Real.rpow_le_rpow_of_exponent_le h1
    have : ((KappaEndpoints.k2ends D j δ).card : ℝ) ≤ D.R.rS := by exact_mod_cast hc.trans hj
    nlinarith
  exact step0.trans step1

end A

section B

variable {D : D7}

def wl (H1 : ℝ) (l : ℕ) (x : D.host.E) : ℝ :=
  ∏ τ : D.what₂.Tau, (max 1 (absReal D.host.rdE (embS D τ) D.R.rS l x / (2 * H1) ^ (2 * D.R.rS))) ^ (-(3 : ℝ))

theorem wl_nonneg (H1 : ℝ) (l : ℕ) (x : D.host.E) : 0 ≤ wl (D := D) H1 l x := Finset.prod_nonneg (fun τ _ => Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)

theorem S_rpow_le (H1 : ℝ) {j : ℕ} (hj : j ≤ D.R.rS) (δ : ℕ → D.host.E) :
    KappaEndpoints.k2S D H1 j δ ^ (-(3 * (D.R.rS : ℝ))) ≤ ∏ l ∈ KappaEndpoints.k2ends D j δ, wl (D := D) H1 l (δ l) := by
  unfold KappaEndpoints.k2S wl
  rw [← Real.finsetProd_rpow _ _ (fun τ _ => le_trans zero_le_one (KappaEndpoints.one_le_minor_sigma H1 j δ τ)), Finset.prod_comm]
  exact Finset.prod_le_prod₀ (fun τ _ => Real.rpow_nonneg (le_trans zero_le_one (KappaEndpoints.one_le_minor_sigma H1 j δ τ)) _)
    (fun τ _ => sg_rpow_le H1 hj δ τ)

def Rl (H1 : ℝ) (l : ℕ) : ℝ := max 1 (D.host.rdE ^ ((2 * frameExp D.R.rS l : ℕ) : ℝ) * (2 * H1) ^ (2 * D.R.rS))

theorem one_le_Rl (H1 : ℝ) (l : ℕ) : 1 ≤ Rl (D := D) H1 l := le_max_left _ _

theorem wl_le (hrd : 0 < D.host.rdE) {H1 : ℝ} (hH : 0 < H1) (l : ℕ) (x : D.host.E) :
    wl (D := D) H1 l x ≤ ∏ τ : D.what₂.Tau, (max 1 (‖embS D τ x‖ / Rl (D := D) H1 l)) ^ (-(3 : ℝ)) := by
  unfold wl
  refine Finset.prod_le_prod₀ (fun τ _ => Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _) (fun τ _ => ?_)
  apply Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le one_pos (le_max_left _ _)) _ (by norm_num)
  apply max_le_max le_rfl
  have hP : 0 < D.host.rdE ^ ((2 * frameExp D.R.rS l : ℕ) : ℝ) * (2 * H1) ^ (2 * D.R.rS) :=
    mul_pos (Real.rpow_pos_of_pos hrd _) (pow_pos (by linarith) _)
  have e : absReal D.host.rdE (embS D τ) D.R.rS l x / (2 * H1) ^ (2 * D.R.rS) =
      ‖embS D τ x‖ / (D.host.rdE ^ ((2 * frameExp D.R.rS l : ℕ) : ℝ) * (2 * H1) ^ (2 * D.R.rS)) := by
    unfold absReal
    rw [Real.rpow_neg hrd.le]
    push_cast
    field_simp
  rw [e]
  exact div_le_div_of_nonneg_left (norm_nonneg _) hP (le_max_right _ _)

theorem sum_one_coord (hNT : KTwoMinorIntegrality.NormLB) (hLS : KTwoMinorIntegrality.LatSum) [Nonempty D.what₂.Tau] (A : Finset D.host.E)
    (hA : ∀ x ∈ A, IsIntegral ℤ x) {R : ℝ} (hR : 1 ≤ R) :
    ∑ x ∈ A, ∏ τ : D.what₂.Tau, (max 1 (‖embS D τ x‖ / R)) ^ (-(3 : ℝ)) ≤ (64 * R) ^ (2 * Fintype.card D.what₂.Tau) := by
  classical
  set vec : D.host.E → D.what₂.Tau → ℂ := fun x τ => embS D τ x with hvec
  have hinj : Set.InjOn vec A := by
    intro x _ y _ hxy
    obtain ⟨τ⟩ := (inferInstance : Nonempty D.what₂.Tau)
    exact (embS D τ).injective (congrFun hxy τ)
  have hsum : ∑ x ∈ A, ∏ τ : D.what₂.Tau, (max 1 (‖embS D τ x‖ / R)) ^ (-(3 : ℝ)) =
      ∑ p ∈ A.image vec, ∏ τ : D.what₂.Tau, (max 1 (‖p τ‖ / R)) ^ (-(3 : ℝ)) := by
    rw [Finset.sum_image hinj]
  rw [hsum]
  apply hLS D.what₂.Tau (A.image vec) R hR
  intro p hp q hq hpq
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hp
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hq
  have hxy : x - y ≠ 0 := sub_ne_zero.2 (fun h => hpq (by rw [h]))
  have h := hNT D (x - y) ((hA x hx).sub (hA y hy)) hxy
  have e : ∏ τ : D.what₂.Tau, ‖embS D τ (x - y)‖ ^ 2 = (∏ τ : D.what₂.Tau, ‖vec x τ - vec y τ‖) ^ 2 := by
    rw [← Finset.prod_pow]
    simp [hvec, map_sub]
  rw [e] at h
  have h0 : 0 ≤ ∏ τ : D.what₂.Tau, ‖vec x τ - vec y τ‖ := Finset.prod_nonneg fun τ _ => norm_nonneg _
  nlinarith

end B

section C

theorem sum_prod_le {ι α : Type*} [DecidableEq ι] [DecidableEq α] (S : Finset ι) (T : Finset (ι → α)) (g : ι → α → ℝ)
    (hg : ∀ i a, 0 ≤ g i a) (hinj : ∀ δ ∈ T, ∀ δ' ∈ T, (∀ i ∈ S, δ i = δ' i) → δ = δ') :
    ∑ δ ∈ T, ∏ i ∈ S, g i (δ i) ≤ ∏ i ∈ S, ∑ a ∈ T.image (fun δ => δ i), g i a := by
  classical
  rw [Finset.prod_sum]
  let φ : (ι → α) → (∀ i ∈ S, α) := fun δ i _ => δ i
  have hφinj : ∀ δ ∈ T, ∀ δ' ∈ T, φ δ = φ δ' → δ = δ' := fun δ hδ δ' hδ' h =>
    hinj δ hδ δ' hδ' (fun i hi => congrFun (congrFun h i) hi)
  have hsub : T.image φ ⊆ S.pi (fun i => T.image (fun δ => δ i)) := by
    intro x hx
    obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_pi.mpr (fun i _ => Finset.mem_image_of_mem _ hδ)
  calc ∑ δ ∈ T, ∏ i ∈ S, g i (δ i)
      = ∑ x ∈ T.image φ, ∏ i ∈ S.attach, g i (x i i.2) := by
        rw [Finset.sum_image hφinj]
        refine Finset.sum_congr rfl (fun δ _ => ?_)
        exact (Finset.prod_attach S (fun i => g i (δ i))).symm
    _ ≤ ∑ x ∈ S.pi (fun i => T.image (fun δ => δ i)), ∏ i ∈ S.attach, g i (x i i.2) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun x _ _ => Finset.prod_nonneg (fun i _ => hg _ _))

end C

section Dsum

variable {D : D7}

end Dsum

end Formalism.MainNotions.KTwoCosetCount

end
end

noncomputable section

namespace Formalism.MainNotions.KTwoCosetCount

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section G

def ccOf (CH Cl : ℝ) : ℝ := 17 + 4 / Cl + 4 * |CH|

theorem frameExp_le {r l : ℕ} (hl : l ≤ r) : frameExp r l ≤ r * r := by
  unfold frameExp
  calc ∑ a ∈ Finset.Icc 1 l, (r + 1 - a) ≤ ∑ a ∈ Finset.Icc 1 l, r :=
        Finset.sum_le_sum fun a ha => by
          simp only [Finset.mem_Icc] at ha
          omega
    _ = l * r := by simp
    _ ≤ r * r := Nat.mul_le_mul_right r hl

theorem expo_le {x a J R M F Nn : ℝ} (hx : 0 ≤ x) (ha : 0 ≤ a) (hJ : 0 ≤ J) (hJR : J ≤ R) (hNn : 0 ≤ Nn) (hNF : Nn ≤ F)
    (hR : 1 ≤ R) (hRM : R ≤ M) (hF : 1 ≤ F) :
    J + (6 + x * (2 * (R * R)) + (1 + a * M) * (2 * R)) * (2 * Nn * J) ≤
      (17 + 4 * x + 4 * a) * M ^ 2 * F * ((17 + 4 * x + 4 * a) * R) := by
  have hR0 : 0 ≤ R := by linarith
  have hM1 : 1 ≤ M := le_trans hR hRM
  have hM0 : 0 ≤ M := by linarith
  have hF0 : 0 ≤ F := by linarith
  have hRM2 : R ≤ M ^ 2 := by nlinarith
  have hc : 1 ≤ 17 + 4 * x + 4 * a := by linarith
  have hA : 6 + x * (2 * (R * R)) + (1 + a * M) * (2 * R) ≤ (8 + 2 * x + 2 * a) * M ^ 2 := by
    have h1 : R * R ≤ M ^ 2 := by nlinarith
    have h3 : a * M * R ≤ a * M ^ 2 := by
      have h5 : M * R ≤ M ^ 2 := by nlinarith
      nlinarith
    have h4 : (1 : ℝ) ≤ M ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h1 hx]
  have hB : 2 * Nn * J ≤ 2 * F * R := by nlinarith
  have hApos : 0 ≤ 6 + x * (2 * (R * R)) + (1 + a * M) * (2 * R) := by
    have h1 : 0 ≤ x * (2 * (R * R)) := mul_nonneg hx (by nlinarith)
    have h2 : 0 ≤ (1 + a * M) * (2 * R) := mul_nonneg (by nlinarith) (by linarith)
    linarith
  have hstep : (6 + x * (2 * (R * R)) + (1 + a * M) * (2 * R)) * (2 * Nn * J) ≤
      (8 + 2 * x + 2 * a) * M ^ 2 * (2 * F * R) :=
    mul_le_mul hA hB (by nlinarith) (by nlinarith)
  have hMF : 1 ≤ M ^ 2 * F := by nlinarith
  have hJ2 : J ≤ M ^ 2 * F * R := by nlinarith
  have hQ : 0 ≤ (17 + 4 * x + 4 * a) * M ^ 2 * F * R := by
    have : 0 ≤ M ^ 2 * F * R := by nlinarith
    nlinarith
  have hc2 : (17 + 4 * x + 4 * a) * M ^ 2 * F * R ≤
      (17 + 4 * x + 4 * a) * M ^ 2 * F * ((17 + 4 * x + 4 * a) * R) := by
    nlinarith [mul_le_mul_of_nonneg_left hc hQ]
  nlinarith

theorem final_arith {L Cl CH rd : ℝ} {r m f n j : ℕ} (hL : 1 < L) (hCl : 0 < Cl) (hrd1 : 1 ≤ rd)
    (hrdL : Real.log rd ≤ L / Cl) (hr : 1 ≤ r) (hrm : r ≤ m) (hjr : j ≤ r) (hnf : n ≤ f) (hf : 1 ≤ f) :
    (2 : ℝ) ^ j * ((64 * (rd ^ (((2 * (r * r) : ℕ)) : ℝ) * (max 1 (2 * Real.exp L ^ (CH * (m : ℝ)))) ^ (2 * r))) ^ (2 * n)) ^ j ≤
      (Real.exp L ^ (ccOf CH Cl * (m : ℝ) ^ 2 * f)) ^ (ccOf CH Cl * (r : ℝ)) := by
  have hL0 : 0 < L := by linarith
  have h2 : (2:ℝ) ≤ Real.exp L := by have := Real.add_one_le_exp L; linarith
  have hrdpos : 0 < rd := by linarith
  have hrd : rd ≤ Real.exp (L / Cl) := by
    rw [← Real.exp_log hrdpos]
    exact Real.exp_le_exp.2 hrdL
  have hx : 0 ≤ 1 / Cl := by positivity
  have ha : 0 ≤ |CH| := abs_nonneg _
  have hM : max 1 (2 * Real.exp L ^ (CH * (m:ℝ))) ≤ Real.exp (L * (1 + |CH| * m)) := by
    have e1 : Real.exp L ^ (CH * (m:ℝ)) ≤ Real.exp (L * (|CH| * m)) := by
      rw [← Real.exp_mul]
      apply Real.exp_le_exp.2
      apply mul_le_mul_of_nonneg_left _ hL0.le
      exact mul_le_mul_of_nonneg_right (le_abs_self CH) (Nat.cast_nonneg m)
    have e2 : (1:ℝ) ≤ Real.exp (L * (|CH| * m)) := Real.one_le_exp (by positivity)
    have e3 : Real.exp (L * (1 + |CH| * m)) = Real.exp L * Real.exp (L * (|CH| * m)) := by
      rw [← Real.exp_add]
      ring_nf
    rw [e3]
    apply max_le
    · nlinarith
    · nlinarith
  have hrdp : rd ^ (((2 * (r * r) : ℕ)) : ℝ) ≤ Real.exp (L * (1 / Cl * (2 * ((r:ℝ) * r)))) := by
    calc rd ^ (((2 * (r * r) : ℕ)) : ℝ) ≤ (Real.exp (L / Cl)) ^ (((2 * (r * r) : ℕ)) : ℝ) :=
          Real.rpow_le_rpow hrdpos.le hrd (by positivity)
      _ = Real.exp (L * (1 / Cl * (2 * ((r:ℝ) * r)))) := by
          rw [← Real.exp_mul]
          congr 1
          push_cast
          ring
  have h64 : (64:ℝ) ≤ Real.exp (L * 6) := by
    rw [show L * 6 = ((6 : ℕ) : ℝ) * L by push_cast; ring, Real.exp_nat_mul]
    calc (64:ℝ) = 2 ^ 6 := by norm_num
      _ ≤ Real.exp L ^ 6 := pow_le_pow_left₀ (by norm_num) h2 6
  have hA : 64 * (rd ^ (((2 * (r * r) : ℕ)) : ℝ) * (max 1 (2 * Real.exp L ^ (CH * (m : ℝ)))) ^ (2 * r)) ≤
      Real.exp (L * 6) * (Real.exp (L * (1 / Cl * (2 * ((r:ℝ) * r)))) * Real.exp (L * (1 + |CH| * m)) ^ (2 * r)) := by
    have hmax0 : 0 ≤ max 1 (2 * Real.exp L ^ (CH * (m : ℝ))) := le_trans zero_le_one (le_max_left _ _)
    gcongr
  have h2j : (2:ℝ) ^ j ≤ Real.exp L ^ j := pow_le_pow_left₀ (by norm_num) h2 j
  have hexpo := expo_le (x := 1 / Cl) (a := |CH|) (J := (j:ℝ)) (R := (r:ℝ)) (M := (m:ℝ)) (F := (f:ℝ)) (Nn := (n:ℝ))
    hx ha (Nat.cast_nonneg j) (by exact_mod_cast hjr) (Nat.cast_nonneg n) (by exact_mod_cast hnf)
    (by exact_mod_cast hr) (by exact_mod_cast hrm) (by exact_mod_cast hf)
  have hcc : ccOf CH Cl = 17 + 4 * (1 / Cl) + 4 * |CH| := by unfold ccOf; ring
  calc (2 : ℝ) ^ j * ((64 * (rd ^ (((2 * (r * r) : ℕ)) : ℝ) * (max 1 (2 * Real.exp L ^ (CH * (m : ℝ)))) ^ (2 * r))) ^ (2 * n)) ^ j
      ≤ Real.exp L ^ j * ((Real.exp (L * 6) * (Real.exp (L * (1 / Cl * (2 * ((r:ℝ) * r)))) *
          Real.exp (L * (1 + |CH| * m)) ^ (2 * r))) ^ (2 * n)) ^ j := by
        have hA0 : 0 ≤ 64 * (rd ^ (((2 * (r * r) : ℕ)) : ℝ) * (max 1 (2 * Real.exp L ^ (CH * (m : ℝ)))) ^ (2 * r)) := by
          have hmax0 : 0 ≤ max 1 (2 * Real.exp L ^ (CH * (m : ℝ))) := le_trans zero_le_one (le_max_left _ _)
          positivity
        have hB := pow_le_pow_left₀ (pow_nonneg hA0 _) (pow_le_pow_left₀ hA0 hA (2 * n)) j
        exact mul_le_mul h2j hB (pow_nonneg (pow_nonneg hA0 _) _) (by positivity)
    _ = Real.exp (L * ((j:ℝ) + (6 + 1 / Cl * (2 * ((r:ℝ) * r)) + (1 + |CH| * m) * (2 * r)) * (2 * n * j))) := by
        simp only [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        push_cast
        ring
    _ ≤ Real.exp (L * ((17 + 4 * (1 / Cl) + 4 * |CH|) * (m:ℝ) ^ 2 * f * ((17 + 4 * (1 / Cl) + 4 * |CH|) * r))) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hexpo hL0.le)
    _ = (Real.exp L ^ (ccOf CH Cl * (m : ℝ) ^ 2 * f)) ^ (ccOf CH Cl * (r : ℝ)) := by
        rw [← Real.rpow_mul (Real.exp_pos L).le, ← Real.exp_mul, hcc]

end G

section H

variable {D : D7}

end H

end Formalism.MainNotions.KTwoCosetCount

end
