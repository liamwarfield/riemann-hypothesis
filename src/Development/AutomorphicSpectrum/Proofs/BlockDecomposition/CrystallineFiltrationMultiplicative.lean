module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFiltrationComapSpanPow
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineFiltrationMultiplicative
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineFiltrationMultiplicative
set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

noncomputable section

namespace GlobalTheory.CompanionTheory.FilMul

variable {l : ℕ} [Fact l.Prime] (A : PAlg l)

theorem divided_power_xi_zero : A.dxi0 0 = 1 := Subtype.ext (by simp [PAlg.dxi0, dpw])

theorem factorial_mul_dpw (k : ℕ) :
    (k.factorial : WL l A.A) * dpw k A.xi = algebraMap A.W (WL l A.A) A.xi ^ k := by
  rw [dpw, ← mul_assoc, Ring.mul_inverse_cancel _ (A.isUnit_natCast k.factorial_ne_zero), one_mul]

theorem factorial_mul_divided_power_xi (k : ℕ) :
    (k.factorial : A.Acr0) * A.dxi0 k = algebraMap A.W A.Acr0 A.xi ^ k :=
  Subtype.ext (by
    have h := factorial_mul_dpw A k
    simpa [PAlg.dxi0] using h)

theorem divided_power_xi_mul (i j : ℕ) :
    A.dxi0 i * A.dxi0 j = ((i + j).choose i : A.Acr0) * A.dxi0 (i + j) := by
  apply Subtype.ext
  show dpw i A.xi * dpw j A.xi = (((i + j).choose i : ℕ) : WL l A.A) * dpw (i + j) A.xi
  have hi := A.isUnit_natCast i.factorial_ne_zero
  have hj := A.isUnit_natCast j.factorial_ne_zero
  have h : (((i + j).choose i : ℕ) : WL l A.A) * (i.factorial : WL l A.A) * (j.factorial : WL l A.A)
      = ((i + j).factorial : WL l A.A) := by
    rw [Nat.choose_symm_add, ← Nat.cast_mul, ← Nat.cast_mul,
      Nat.add_choose_mul_factorial_mul_factorial i j]
  apply hj.mul_left_cancel
  apply hi.mul_left_cancel
  calc (i.factorial : WL l A.A) * ((j.factorial : WL l A.A) * (dpw i A.xi * dpw j A.xi))
      = ((i.factorial : WL l A.A) * dpw i A.xi) * ((j.factorial : WL l A.A) * dpw j A.xi) := by ring
    _ = ((i + j).factorial : WL l A.A) * dpw (i + j) A.xi := by
        rw [factorial_mul_dpw, factorial_mul_dpw, factorial_mul_dpw, pow_add]
    _ = (i.factorial : WL l A.A) * ((j.factorial : WL l A.A)
          * ((((i + j).choose i : ℕ) : WL l A.A) * dpw (i + j) A.xi)) := by
        rw [← h]; ring

theorem Fil0_zero : A.Fil0 0 = ⊤ :=
  (Ideal.eq_top_iff_one _).2 (Ideal.subset_span ⟨0, le_rfl, (divided_power_xi_zero A).symm⟩)

theorem Fil0_mul_le (r s : ℕ) : A.Fil0 r * A.Fil0 s ≤ A.Fil0 (r + s) := by
  unfold PAlg.Fil0
  rw [Ideal.span_mul_span', Ideal.span_le]
  rintro _ ⟨_, ⟨i, hi, rfl⟩, _, ⟨j, hj, rfl⟩, rfl⟩
  show A.dxi0 i * A.dxi0 j ∈ Ideal.span _
  rw [divided_power_xi_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i + j, by omega, rfl⟩)

theorem Fil_eq_map (n r : ℕ) : A.Fil n r = (A.Fil0 r).map (A.mkAcr n) := by
  unfold PAlg.Fil PAlg.Fil0
  rw [Ideal.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨_, ⟨k, hk, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨k, hk, rfl⟩

theorem PFil_eq_map (n : ℕ) : A.PFil n = A.PFil0.map (A.mkAcr n) := by
  rw [PAlg.PFil, PAlg.PFil0, Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_natCast,
    Fil_eq_map]

theorem Fil_zero (n : ℕ) : A.Fil n 0 = ⊤ := by
  rw [Fil_eq_map, Fil0_zero, Ideal.map_top]

theorem Fil_mul_le (n r s : ℕ) : A.Fil n r * A.Fil n s ≤ A.Fil n (r + s) := by
  rw [Fil_eq_map, Fil_eq_map, Fil_eq_map, ← Ideal.map_mul]
  exact Ideal.map_mono (Fil0_mul_le A r s)

theorem main : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), A.Fil0 0 = ⊤ ∧
    (∀ i j, A.dxi0 i * A.dxi0 j = ((i + j).choose i : A.Acr0) * A.dxi0 (i + j)) ∧
    (∀ k, (k.factorial : A.Acr0) * A.dxi0 k = algebraMap A.W A.Acr0 A.xi ^ k) ∧
    (∀ r s, A.Fil0 r * A.Fil0 s ≤ A.Fil0 (r + s)) ∧
    (∀ n r, A.Fil n r = (A.Fil0 r).map (A.mkAcr n)) ∧
    (∀ n, A.PFil n = A.PFil0.map (A.mkAcr n)) ∧
    (∀ n, A.Fil n 0 = ⊤) ∧ ∀ n r s, A.Fil n r * A.Fil n s ≤ A.Fil n (r + s) :=
  fun A => ⟨Fil0_zero A, divided_power_xi_mul A, factorial_mul_divided_power_xi A, Fil0_mul_le A, Fil_eq_map A,
    PFil_eq_map A, Fil_zero A, Fil_mul_le A⟩

end GlobalTheory.CompanionTheory.FilMul
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineFiltrationMultiplicativeStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_filtration_multiplicative : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), A.Fil0 0 = ⊤ ∧ (∀ i j, A.dxi0 i * A.dxi0 j = ((i + j).choose i : A.Acr0) * A.dxi0 (i + j)) ∧ (∀ k, (k.factorial : A.Acr0) * A.dxi0 k = algebraMap A.W A.Acr0 A.xi ^ k) ∧ (∀ r s, A.Fil0 r * A.Fil0 s ≤ A.Fil0 (r + s)) ∧ (∀ n r, A.Fil n r = (A.Fil0 r).map (A.mkAcr n)) ∧ (∀ n, A.PFil n = A.PFil0.map (A.mkAcr n)) ∧ (∀ n, A.Fil n 0 = ⊤) ∧ ∀ n r s, A.Fil n r * A.Fil n s ≤ A.Fil n (r + s) := by
  first | exact @GlobalTheory.CompanionTheory.FilMul.main | exact GlobalTheory.CompanionTheory.FilMul.main | (intros; apply GlobalTheory.CompanionTheory.FilMul.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectoidXiNonZeroDivisor
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectoidXiNonZeroDivisor
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.UntiltRegular

variable {W R : Type*} [CommRing W] [CommRing R]

theorem mem_span_of_mul_mem_of_hom {l xi : W} (φ : W →+* R)
    (hmem : ∀ y, y ∈ Ideal.span {l} ↔ φ y = 0) (hxi : φ xi ∈ nonZeroDivisors R) (y : W)
    (h : xi * y ∈ Ideal.span {l}) : y ∈ Ideal.span {l} := by
  rw [hmem] at h ⊢
  rw [map_mul] at h
  exact (mul_left_mem_nonZeroDivisors_eq_zero_iff hxi).mp h

private theorem eq_zero_of_pow_mul_eq_zero_of_nonzerodivisor' {l : W} (hl : ∀ x, l * x = 0 → x = 0) (m : ℕ) :
    ∀ t : W, l ^ m * t = 0 → t = 0 := by
  induction m with
  | zero => intro t ht; simpa using ht
  | succ m ihm =>
    intro t ht
    rw [pow_succ, mul_assoc] at ht
    exact hl t (ihm _ ht)

theorem mem_span_pow_of_mul_mem {l xi : W} (hl : ∀ x, l * x = 0 → x = 0)
    (key : ∀ y, xi * y ∈ Ideal.span {l} → y ∈ Ideal.span {l}) (n : ℕ) :
    ∀ x, xi * x ∈ Ideal.span {l ^ n} → x ∈ Ideal.span {l ^ n} := by
  induction n with
  | zero => intro x _; simp
  | succ n ih =>
    intro x hx
    have hx' : xi * x ∈ Ideal.span {l ^ n} := by
      rw [Ideal.mem_span_singleton] at hx ⊢
      exact (pow_dvd_pow l (Nat.le_succ n)).trans hx
    have h1 := ih x hx'
    rw [Ideal.mem_span_singleton] at h1 hx ⊢
    obtain ⟨c, rfl⟩ := h1
    obtain ⟨d, hd⟩ := hx
    have h2 : xi * c = l * d := by
      have h0 : l ^ n * (xi * c - l * d) = 0 := by linear_combination hd
      exact sub_eq_zero.mp (eq_zero_of_pow_mul_eq_zero_of_nonzerodivisor' hl n _ h0)
    obtain ⟨e, rfl⟩ := Ideal.mem_span_singleton.mp (key c (Ideal.mem_span_singleton.mpr ⟨d, h2⟩))
    exact ⟨e, by ring⟩

theorem eq_zero_of_mul_eq_zero {l xi : W} (hl : ∀ x, l * x = 0 → x = 0)
    (hH : IsHausdorff (Ideal.span {l}) W)
    (key : ∀ y, xi * y ∈ Ideal.span {l} → y ∈ Ideal.span {l}) (y : W) (h : xi * y = 0) :
    y = 0 := by
  have hall : ∀ n, y ∈ Ideal.span {l ^ n} :=
    fun n => mem_span_pow_of_mul_mem hl key n y (by rw [h]; exact zero_mem _)
  apply hH.haus y
  intro n
  rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  exact hall n

theorem mem_span_xi_of_mul_mem {l xi : W} (hl : ∀ x, l * x = 0 → x = 0)
    (key : ∀ y, xi * y ∈ Ideal.span {l} → y ∈ Ideal.span {l}) (y : W)
    (h : l * y ∈ Ideal.span {xi}) : y ∈ Ideal.span {xi} := by
  rw [Ideal.mem_span_singleton] at h ⊢
  obtain ⟨c, hc⟩ := h
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.mp (key c (Ideal.mem_span_singleton.mpr ⟨y, hc.symm⟩))
  refine ⟨d, sub_eq_zero.mp (hl _ ?_)⟩
  linear_combination hc

theorem regular_of_key {l xi : W} (hl : ∀ x, l * x = 0 → x = 0)
    (hH : IsHausdorff (Ideal.span {l}) W)
    (key : ∀ y, xi * y ∈ Ideal.span {l} → y ∈ Ideal.span {l}) :
    Ideal.Quotient.mk (Ideal.span {xi}) l ∈ nonZeroDivisors (W ⧸ Ideal.span {xi}) ∧
      xi ∈ nonZeroDivisors W ∧
      ∀ (n : ℕ) (x : W), xi * x ∈ Ideal.span {l ^ n} → x ∈ Ideal.span {l ^ n} := by
  refine ⟨?_, ?_, mem_span_pow_of_mul_mem hl key⟩
  · rw [mem_nonZeroDivisors_iff]
    have hq : ∀ x : W ⧸ Ideal.span {xi}, x * Ideal.Quotient.mk (Ideal.span {xi}) l = 0 → x = 0 := by
      intro x hx
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hx
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact mem_span_xi_of_mul_mem hl key x (by rw [mul_comm]; exact hx)
    exact ⟨fun x hx => hq x (by rw [mul_comm]; exact hx), hq⟩
  · rw [mem_nonZeroDivisors_iff]
    have hw : ∀ x : W, xi * x = 0 → x = 0 := fun x hx => eq_zero_of_mul_eq_zero hl hH key x hx
    exact ⟨hw, fun x hx => hw x (by rw [mul_comm]; exact hx)⟩

theorem key {l : ℕ} [Fact l.Prime] (A : PAlg l) (y : A.W)
    (h : A.xi * y ∈ Ideal.span {(l : A.W)}) : y ∈ Ideal.span {(l : A.W)} := by
  refine mem_span_of_mul_mem_of_hom (WittVector.constantCoeff : A.W →+* A.A) (fun x => ?_) ?_ y h
  · rw [A.mem_span_l_iff x]
    exact Iff.rfl
  · have hc : (WittVector.constantCoeff : A.W →+* A.A) A.xi = -A.pi := A.xi_coeff_zero
    have hpi : A.pi ∈ nonZeroDivisors A.A := A.tf
    rw [hc, ← neg_one_mul]
    exact mul_mem isUnit_one.neg.mem_nonZeroDivisors hpi

theorem untilt_regular : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l),
    (l : A.U) ∈ nonZeroDivisors A.U ∧ A.xi ∈ nonZeroDivisors A.W ∧
      ∀ (n : ℕ) (x : A.W), A.xi * x ∈ Ideal.span {(l : A.W) ^ n} →
        x ∈ Ideal.span {(l : A.W) ^ n} := by
  intro l _ A
  have hreg := regular_of_key (W := A.W) (l := (l : A.W)) (xi := A.xi)
    (fun x hx => A.l_mul_eq_zero hx) inferInstance (fun y hy => key A y hy)
  refine ⟨?_, hreg.2.1, hreg.2.2⟩
  have h1 := hreg.1
  rw [map_natCast] at h1
  exact h1

end GlobalTheory.CompanionTheory.UntiltRegular
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectoidXiNonZeroDivisorStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.perfectoid_xi_nonZeroDivisor : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), (l : A.U) ∈ nonZeroDivisors A.U ∧ A.xi ∈ nonZeroDivisors A.W ∧ ∀ (n : ℕ) (x : A.W), A.xi * x ∈ Ideal.span {(l : A.W) ^ n} → x ∈ Ideal.span {(l : A.W) ^ n} := by
  first | exact @GlobalTheory.CompanionTheory.UntiltRegular.untilt_regular | exact GlobalTheory.CompanionTheory.UntiltRegular.untilt_regular | (intros; apply GlobalTheory.CompanionTheory.UntiltRegular.untilt_regular <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFiltrationLTorsionFree
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFiltrationLTorsionFree
open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.Lat

theorem quot_pdP_no_torsion : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (m : ℕ), Lat.Hyp f ξ l m → ∀ hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ), ∀ (r : ℕ) (x : Lat.A f ξ l M), (l : Lat.A f ξ l M) * x ∈ pdP (Lat.γ f ξ l M hc) r → x ∈ pdP (Lat.γ f ξ l M hc) r := by
  intro W B _ _ _ f ξ l M m hH hc r x hx
  rw [GlobalTheory.T.lattice_filtration_comap_span_pow f ξ l M m hH hc r] at hx ⊢
  rw [Ideal.mem_comap, map_mul, map_natCast] at hx
  rw [Ideal.mem_comap]
  have hl0 : l ≠ 0 := by
    rintro rfl
    exact hH.l0 Nat.cast_zero
  have hl : (l : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hl0
  have hu : algebraMap ℚ B (l : ℚ)⁻¹ * (l : B) = 1 := by
    rw [← map_natCast (algebraMap ℚ B) l, ← map_mul, inv_mul_cancel₀ hl, map_one]
  have h2 := Ideal.mul_mem_left _ (algebraMap ℚ B (l : ℚ)⁻¹) hx
  rwa [← mul_assoc, hu, one_mul] at h2

end GlobalTheory.CompanionTheory.Lat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFiltrationLTorsionFreeStatement
open DividedPowers CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_filtration_l_torsion_free : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (m : ℕ), Lat.Hyp f ξ l m → ∀ hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ), ∀ (r : ℕ) (x : Lat.A f ξ l M), (l : Lat.A f ξ l M) * x ∈ pdP (Lat.γ f ξ l M hc) r → x ∈ pdP (Lat.γ f ξ l M hc) r := by
  first | exact @GlobalTheory.CompanionTheory.Lat.quot_pdP_no_torsion | exact GlobalTheory.CompanionTheory.Lat.quot_pdP_no_torsion | (intros; apply GlobalTheory.CompanionTheory.Lat.quot_pdP_no_torsion <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SharpSurjectiveKerSpan
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SharpSurjectiveKerSpan
set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.Untilt

theorem sharp_map_surjective_ker {l : ℕ} [Fact l.Prime] (A : PAlg l) :
    Function.Surjective A.aToU1 ∧ RingHom.ker A.aToU1 = Ideal.span {A.pi} := by
  constructor
  · intro y
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective u
    exact ⟨x.coeff 0, A.sharpMap_coeff x⟩
  · ext a
    rw [RingHom.mem_ker]
    constructor
    · intro h
      rw [A.sharpMap_eq, Ideal.Quotient.eq_zero_iff_mem, pow_one] at h
      obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 h
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective u
      have h0 : A.th (WittVector.teichmuller l a - y * (l : A.W)) = 0 := by
        rw [map_sub, map_mul, map_natCast]
        exact sub_eq_zero.2 hu.symm
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 h0)
      have h1 := congrArg (WittVector.constantCoeff : A.W →+* A.A) hc
      rw [map_mul, map_sub, map_mul, map_natCast, A.natCast_l, mul_zero, sub_zero,
        WittVector.constantCoeff_apply, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply,
        WittVector.teichmuller_coeff_zero, A.xi_coeff_zero] at h1
      exact Ideal.mem_span_singleton'.2 ⟨-c.coeff 0, by rw [← h1, neg_mul, mul_neg]⟩
    · intro h
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 h
      rw [map_mul, A.sharpMap_eq A.pi, A.sharp_pi,
        Ideal.Quotient.eq_zero_iff_mem.2 (by
          rw [pow_one]; exact Ideal.mem_span_singleton_self _), mul_zero]

end GlobalTheory.CompanionTheory.Untilt
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SharpSurjectiveKerSpanStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sharp_surjective_ker_span : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), Function.Surjective A.aToU1 ∧ RingHom.ker A.aToU1 = Ideal.span {A.pi} := by
  first | exact @GlobalTheory.CompanionTheory.Untilt.sharp_map_surjective_ker | exact GlobalTheory.CompanionTheory.Untilt.sharp_map_surjective_ker | (intros; apply GlobalTheory.CompanionTheory.Untilt.sharp_map_surjective_ker <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineFiltrationSpanDividedPowers
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.PerfFil

variable {l : ℕ} [Fact l.Prime] (A : PAlg l)

theorem divided_power_xi_zero : A.dxi0 0 = 1 :=
  Subtype.ext (by simp [PAlg.dxi0, dpw])

theorem divided_power_xi_mul (i j : ℕ) :
    A.dxi0 i * A.dxi0 j = (((i + j).choose i : ℕ) : A.Acr0) * A.dxi0 (i + j) := by
  apply Subtype.ext
  have hi := A.isUnit_natCast (Nat.factorial_ne_zero i)
  have hj := A.isUnit_natCast (Nat.factorial_ne_zero j)
  have hij := A.isUnit_natCast (Nat.factorial_ne_zero (i + j))
  change dpw i A.xi * dpw j A.xi = (((i + j).choose i : ℕ) : WL l A.A) * dpw (i + j) A.xi
  simp only [dpw]
  apply hij.mul_left_cancel
  have hc : (((i + j).factorial : ℕ) : WL l A.A) =
      (((i + j).choose i : ℕ) : WL l A.A) * ((i.factorial : ℕ) : WL l A.A) * ((j.factorial : ℕ) : WL l A.A) := by
    have := Nat.add_choose_mul_factorial_mul_factorial i j
    rw [← Nat.choose_symm_add] at this
    rw [← Nat.cast_mul, ← Nat.cast_mul, this]
  calc _ = (((i + j).choose i : ℕ) : WL l A.A) * (((i.factorial : ℕ) : WL l A.A) * Ring.inverse ((i.factorial : ℕ) : WL l A.A))
        * (((j.factorial : ℕ) : WL l A.A) * Ring.inverse ((j.factorial : ℕ) : WL l A.A))
        * (algebraMap _ (WL l A.A) A.xi ^ i * algebraMap _ (WL l A.A) A.xi ^ j) := by
          rw [hc]; ring
    _ = (((i + j).choose i : ℕ) : WL l A.A) * (algebraMap _ (WL l A.A) A.xi ^ (i + j)) := by
          rw [Ring.mul_inverse_cancel _ hi, Ring.mul_inverse_cancel _ hj, pow_add]; ring
    _ = _ := by
          rw [mul_left_comm, ← mul_assoc (((i + j).factorial : ℕ) : WL l A.A), Ring.mul_inverse_cancel _ hij, one_mul]

def spanFrom (r : ℕ) : Submodule A.W A.Acr0 :=
  Submodule.span A.W {z : A.Acr0 | ∃ k, r ≤ k ∧ z = A.dxi0 k}

theorem divided_power_xi_mem_span_from {r k : ℕ} (h : r ≤ k) : A.dxi0 k ∈ spanFrom A r :=
  Submodule.subset_span ⟨k, h, rfl⟩

theorem natCast_mul_mem (r : ℕ) (n : ℕ) {z : A.Acr0} (hz : z ∈ spanFrom A r) :
    (n : A.Acr0) * z ∈ spanFrom A r := by
  rw [← nsmul_eq_mul]
  exact (spanFrom A r).toAddSubmonoid.nsmul_mem hz n

theorem mul_mem_spanFrom (r : ℕ) {a b : A.Acr0} (ha : a ∈ spanFrom A 0) (hb : b ∈ spanFrom A r) :
    a * b ∈ spanFrom A r := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, -, rfl⟩ := hx
    induction hb using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      rw [divided_power_xi_mul]
      exact natCast_mul_mem A r _ (divided_power_xi_mem_span_from A (by omega))
    | zero => rw [mul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

theorem mem_spanFrom_zero (z : A.Acr0) : z ∈ spanFrom A 0 := by
  obtain ⟨y, hy⟩ := z
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    exact divided_power_xi_mem_span_from A (Nat.zero_le k)
  | algebraMap x =>
    have h := Submodule.smul_mem (spanFrom A 0) x (divided_power_xi_mem_span_from A (le_refl 0))
    rw [divided_power_xi_zero] at h
    convert h using 1
    exact Subtype.ext (by simp [Algebra.smul_def])
  | add x y hx' hy' hx hy => exact add_mem hx hy
  | mul x y hx' hy' hx hy => exact mul_mem_spanFrom A 0 hx hy

theorem mem_crystalline_filtration_iff_span {l : ℕ} [Fact l.Prime] (A : PAlg l) (r : ℕ) (z : A.Acr0) :
    z ∈ A.Fil0 r ↔ z ∈ Submodule.span A.W {z : A.Acr0 | ∃ k, r ≤ k ∧ z = A.dxi0 k} := by
  constructor
  · intro h
    induction h using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span hx
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul c x _ hx => exact mul_mem_spanFrom A r (mem_spanFrom_zero A c) hx
  · intro h
    induction h using Submodule.span_induction with
    | mem x hx => exact Ideal.subset_span hx
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul c x _ hx =>
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_left _ _ hx

end GlobalTheory.CompanionTheory.PerfFil
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralRingAdicCompletePrimeRegular
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralRingAdicCompletePrimeRegular
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.TiltCompl

variable {l : ℕ} [Fact l.Prime]

theorem norm_pFlat_pos : 0 < ‖pFlat l‖ := by
  rw [preTilt_norm_def, coe_untilt_pFlat]
  exact norm_pos_iff.2 natCast_p_ne_zero_cp

theorem norm_pFlat_lt_one : ‖pFlat l‖ < 1 := by
  rw [preTilt_norm_def, coe_untilt_pFlat]
  exact IsPerfectoidField.norm_natCast_lt_one

theorem smodEq_iff (n : ℕ) (x y : Ob l) :
    x ≡ y [SMOD (Ideal.span {pFlat l} ^ n • ⊤ : Ideal (Ob l))] ↔ ‖x - y‖ ≤ ‖pFlat l‖ ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, preTilt_dvd_iff_norm_le, norm_pow]

theorem complete_tf : ∀ {l : ℕ} [Fact l.Prime],
    IsAdicComplete (Ideal.span {pFlat l}) (Ob l) ∧ pFlat l ∈ nonZeroDivisors (Ob l) := by
  intro l _
  have h0 : 0 < ‖pFlat l‖ := norm_pFlat_pos
  have h1 : ‖pFlat l‖ < 1 := norm_pFlat_lt_one
  have hlim : Filter.Tendsto (fun n : ℕ => ‖pFlat l‖ ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one h0.le h1
  refine ⟨{ haus' := fun x hx => ?_, prec' := fun f hf => ?_ }, ?_⟩
  · have hb : ∀ n : ℕ, ‖x‖ ≤ ‖pFlat l‖ ^ n := fun n => by
      simpa using (smodEq_iff n x 0).1 (hx n)
    have : ‖x‖ ≤ 0 := ge_of_tendsto' hlim hb
    exact norm_le_zero_iff.1 this
  · have hb : ∀ {m n : ℕ}, m ≤ n → ‖f m - f n‖ ≤ ‖pFlat l‖ ^ m := fun h =>
      (smodEq_iff _ _ _).1 (hf h)
    have hc : CauchySeq f := by
      refine cauchySeq_of_le_geometric ‖pFlat l‖ 1 h1 fun n => ?_
      rw [dist_eq_norm, one_mul]
      exact hb n.le_succ
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
    refine ⟨L, fun n => (smodEq_iff _ _ _).2 ?_⟩
    have ht : Filter.Tendsto (fun m => ‖f n - f m‖) Filter.atTop (nhds ‖f n - L‖) :=
      (tendsto_const_nhds.sub hL).norm
    refine le_of_tendsto ht ?_
    filter_upwards [Filter.eventually_ge_atTop n] with m hm using hb hm
  · exact mem_nonZeroDivisors_iff_left.2 fun x hx => by
      have := congrArg norm hx
      rw [norm_mul, norm_zero] at this
      exact norm_eq_zero.1 ((mul_eq_zero.1 this).resolve_left h0.ne')

end GlobalTheory.CompanionTheory.TiltCompl
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralRingAdicCompletePrimeRegularStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_ring_adic_complete_prime_regular : ∀ {l : ℕ} [Fact l.Prime], IsAdicComplete (Ideal.span {pFlat l}) (Ob l) ∧ pFlat l ∈ nonZeroDivisors (Ob l) := by
  first | exact @GlobalTheory.CompanionTheory.TiltCompl.complete_tf | exact GlobalTheory.CompanionTheory.TiltCompl.complete_tf | (intros; apply GlobalTheory.CompanionTheory.TiltCompl.complete_tf <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctorialityOfPeriodRingMaps
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctorialityOfPeriodRingMaps
set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.PAlgNat

variable {l : ℕ} [Fact l.Prime]

theorem mapAcris_acrisOfTilt {A B : PAlg l} (f : A ⟶ B) (a : A.A) :
    mapAcr f 1 (A.aTo1 a) = B.aTo1 (Hom.f f a) := by
  have h := A.aTo1_coeff (WittVector.teichmuller l a)
  rw [WittVector.teichmuller_coeff_zero] at h
  have h' := B.aTo1_coeff (WittVector.teichmuller l (Hom.f f a))
  rw [WittVector.teichmuller_coeff_zero] at h'
  rw [h, h', mapAcr_toAcr, mapW, WittVector.map_teichmuller]

theorem mapAcr_expand {A B : PAlg l} (f : A ⟶ B) (c : ℕ →₀ A.A) :
    mapAcr f 1 (A.expand c) = B.expand (c.mapRange (Hom.f f) (map_zero _)) := by
  rw [expand, expand, map_finsuppSum, Finsupp.sum_mapRange_index (fun k => by simp)]
  refine Finsupp.sum_congr fun k _ => ?_
  rw [map_mul, mapAcris_acrisOfTilt, mapAcr_dxi]

theorem mapU_sharp {A B : PAlg l} (f : A ⟶ B) (a : A.A) :
    mapU f (A.sharp a) = B.sharp (Hom.f f a) := by
  change mapU f (A.th (WittVector.teichmuller l a)) = B.th (WittVector.teichmuller l (Hom.f f a))
  rw [mapU_th, mapW, WittVector.map_teichmuller]

theorem mapUnits_unitsOfTilt {A B : PAlg l} (f : A ⟶ B) (a : A.A) :
    mapUn f 1 (A.aToU1 a) = B.aToU1 (Hom.f f a) := by
  rw [sharpMap_eq, sharpMap_eq, ← mapU_sharp]
  rfl

theorem mk_mapAcr_toAcr {A B : PAlg l} (f : A ⟶ B) (n : ℕ) (x : A.W) :
    Ideal.Quotient.mk (B.Fil n 1) (mapAcr f n (A.toAcr n x)) = B.uToQ n (mapU f (A.th x)) := by
  rw [mapAcr_toAcr, mapU_th, uToQ_th]

theorem algebraMap_eq_acrisOfTilt (A : PAlg l) (x : Ainf l) :
    algebraMap (Ainf l) (A.Acr 1) x = A.aTo1 (A.s (x.coeff 0)) := by
  have h := A.aTo1_coeff (A.sW x)
  have e : (A.sW x).coeff 0 = A.s (x.coeff 0) := WittVector.map_coeff _ _ _
  rw [e] at h
  rw [h]
  rfl

theorem expand_nat {l : ℕ} [Fact l.Prime] (A : PAlg l) (B : PAlg l) (f : A ⟶ B) :
    (∀ a, mapAcr f 1 (A.aTo1 a) = B.aTo1 (Hom.f f a)) ∧
    (∀ c : ℕ →₀ A.A, mapAcr f 1 (A.expand c) = B.expand (c.mapRange (Hom.f f) (map_zero _))) ∧
    (∀ a, mapU f (A.sharp a) = B.sharp (Hom.f f a)) ∧
    (∀ a, mapUn f 1 (A.aToU1 a) = B.aToU1 (Hom.f f a)) ∧
    (∀ n x, Ideal.Quotient.mk (B.Fil n 1) (mapAcr f n (A.toAcr n x)) = B.uToQ n (mapU f (A.th x))) ∧
    ∀ x : Ainf l, algebraMap (Ainf l) (A.Acr 1) x = A.aTo1 (A.s (x.coeff 0)) :=
  ⟨mapAcris_acrisOfTilt f, mapAcr_expand f, mapU_sharp f, mapUnits_unitsOfTilt f, mk_mapAcr_toAcr f, algebraMap_eq_acrisOfTilt A⟩

end GlobalTheory.CompanionTheory.PAlgNat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctorialityOfPeriodRingMapsStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.functoriality_of_period_ring_maps : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (B : PAlg l) (f : A ⟶ B), (∀ a, mapAcr f 1 (A.aTo1 a) = B.aTo1 (Hom.f f a)) ∧ (∀ c : ℕ →₀ A.A, mapAcr f 1 (A.expand c) = B.expand (c.mapRange (Hom.f f) (map_zero _))) ∧ (∀ a, mapU f (A.sharp a) = B.sharp (Hom.f f a)) ∧ (∀ a, mapUn f 1 (A.aToU1 a) = B.aToU1 (Hom.f f a)) ∧ (∀ n x, Ideal.Quotient.mk (B.Fil n 1) (mapAcr f n (A.toAcr n x)) = B.uToQ n (mapU f (A.th x))) ∧ ∀ x : Ainf l, algebraMap (Ainf l) (A.Acr 1) x = A.aTo1 (A.s (x.coeff 0)) := by
  first | exact @GlobalTheory.CompanionTheory.PAlgNat.expand_nat | exact GlobalTheory.CompanionTheory.PAlgNat.expand_nat | (intros; apply GlobalTheory.CompanionTheory.PAlgNat.expand_nat <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeLPowMemSpanOfNotMem
set_option autoImplicit false

open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.Lat

private theorem exists_sub_iota_mem_of_sub_involution_mem {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W)
    (l M : ℕ) (b : B) (hb : b ∈ Lat.sub f ξ l M) : ∃ w : W, f w - b ∈ Lat.IB f ξ := by
  have hη : Lat.η f ξ l M ∈ Lat.IB f ξ := by
    rw [Lat.η, Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  have hle : Lat.sub f ξ l M ≤
      (((Ideal.Quotient.mk (Lat.IB f ξ)).comp f).range).comap (Ideal.Quotient.mk (Lat.IB f ξ)) := by
    show Subring.closure _ ≤ _
    rw [Subring.closure_le]
    rintro y (⟨w, rfl⟩ | ⟨i, rfl⟩)
    · exact Subring.mem_comap.2 (RingHom.mem_range.2 ⟨w, rfl⟩)
    · cases i with
      | zero => exact Subring.mem_comap.2 (RingHom.mem_range.2 ⟨1, by simp [Lat.dpE]⟩)
      | succ i =>
        have hd : Lat.dpE f ξ l M (i + 1) ∈ Lat.IB f ξ := by
          rw [Lat.dpE, Algebra.smul_def, pow_succ']
          exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hη)
        refine Subring.mem_comap.2 (RingHom.mem_range.2 ⟨0, ?_⟩)
        rw [map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem]
        exact hd
  obtain ⟨w, hw⟩ := RingHom.mem_range.1 (Subring.mem_comap.1 (hle hb))
  exact ⟨w, Ideal.Quotient.eq.1 hw⟩

theorem pow_mem_span_sup_I : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W)
    (l M : ℕ) (m : ℕ), Lat.Hyp f ξ l m → ∀ x : Lat.A f ξ l M, x ∉ Lat.I f ξ l M →
      ∃ n : ℕ, (l : Lat.A f ξ l M) ^ n ∈ Ideal.span {x} ⊔ Lat.I f ξ l M := by
  intro W B _ _ _ f ξ l M m hH x hx
  have hxmem : Lat.ι f ξ l M x ∈ Lat.sub f ξ l M := (show ↥(Lat.sub f ξ l M) from x).2
  obtain ⟨w, hw⟩ := exists_sub_iota_mem_of_sub_involution_mem f ξ l M _ hxmem
  have hxw : Lat.ofW f ξ l M w - x ∈ Lat.I f ξ l M := by
    show Lat.ι f ξ l M (Lat.ofW f ξ l M w - x) ∈ Lat.IB f ξ
    rw [map_sub, Lat.ι_ofW]
    exact hw
  have hξI : Lat.ofW f ξ l M ξ ∈ Lat.I f ξ l M := by
    show Lat.ι f ξ l M (Lat.ofW f ξ l M ξ) ∈ Lat.IB f ξ
    rw [Lat.ι_ofW]
    exact Ideal.mem_span_singleton_self _
  have hwnot : ¬ ξ ∣ w := by
    rintro ⟨v, rfl⟩
    apply hx
    have h1 : Lat.ofW f ξ l M (ξ * v) ∈ Lat.I f ξ l M := by
      rw [map_mul]
      exact Ideal.mul_mem_right _ _ hξI
    have h2 := (Lat.I f ξ l M).sub_mem h1 hxw
    simpa using h2
  have hq : Ideal.Quotient.mk (Ideal.span {ξ}) w ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact hwnot
  obtain ⟨n, c, hc⟩ := hH.dv _ hq
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective c
  have hmem : (l : W) ^ n - w * u ∈ Ideal.span {ξ} := by
    rw [← Ideal.Quotient.eq]
    simpa using hc
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 hmem
  refine ⟨n, ?_⟩
  have e : (l : Lat.A f ξ l M) ^ n = Lat.ofW f ξ l M ((l : W) ^ n) := by
    rw [map_pow, map_natCast]
  rw [e, show (l : W) ^ n = w * u + v * ξ by rw [hv]; ring, map_add (f := _), map_mul, map_mul]
  refine Ideal.add_mem _ ?_ (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ hξI))
  have e2 : Lat.ofW f ξ l M w * Lat.ofW f ξ l M u =
      x * Lat.ofW f ξ l M u + (Lat.ofW f ξ l M w - x) * Lat.ofW f ξ l M u := by ring
  rw [e2]
  exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self x)))
    (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ hxw))

end GlobalTheory.CompanionTheory.Lat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeDpowClosedOfHyp
open DividedPowers CrystallineSemistableComparison.Pb

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.LatDP

variable {B : Type} [CommRing B] [Algebra ℚ B]

theorem inv_fact_smul_add_pow_mem (S : Subring B) {z w : B}
    (hz : ∀ k : ℕ, ((k.factorial : ℚ))⁻¹ • z ^ k ∈ S) (hw : ∀ k : ℕ, ((k.factorial : ℚ))⁻¹ • w ^ k ∈ S)
    (k : ℕ) : ((k.factorial : ℚ))⁻¹ • (z + w) ^ k ∈ S := by
  have e : ((k.factorial : ℚ))⁻¹ • (z + w) ^ k =
      ∑ i ∈ Finset.range (k + 1), (((i.factorial : ℚ))⁻¹ • z ^ i) * ((((k - i).factorial : ℚ))⁻¹ • w ^ (k - i)) := by
    rw [add_pow, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hc : ((k.choose i : ℕ) : B) = ((k.choose i : ℕ) : ℚ) • (1 : B) := by
      rw [Algebra.smul_def, mul_one, map_natCast]
    rw [hc, mul_smul_comm, mul_one, smul_smul, smul_mul_smul_comm, Nat.cast_choose ℚ hik]
    congr 1
    have h1 : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
    have h2 : (i.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 i.factorial_ne_zero
    have h3 : ((k - i).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (k - i).factorial_ne_zero
    field_simp
  rw [e]
  exact S.sum_mem fun i _ => S.mul_mem (hz i) (hw _)

variable {W : Type} [CommRing W] (f : W →+* B) (ξ : W) (l M : ℕ)

theorem inv_fact_smul_dpE_pow (j k : ℕ) (hj : j ≠ 0) :
    ((k.factorial : ℚ))⁻¹ • Lat.dpE f ξ l M j ^ k =
      ((k.uniformBell j : ℕ) : B) * Lat.dpE f ξ l M (k * j) := by
  have hU : ((k.uniformBell j : ℕ) : ℚ) * (j.factorial : ℚ) ^ k * (k.factorial : ℚ) = ((k * j).factorial : ℚ) := by
    exact_mod_cast Nat.uniformBell_mul_eq k hj
  have hc : ((k.uniformBell j : ℕ) : B) = ((k.uniformBell j : ℕ) : ℚ) • (1 : B) := by
    rw [Algebra.smul_def, mul_one, map_natCast]
  have h1 : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
  have h2 : (j.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 j.factorial_ne_zero
  have h3 : ((k * j).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (k * j).factorial_ne_zero
  rw [Lat.dpE, Lat.dpE, smul_pow, ← pow_mul, smul_smul, hc, smul_mul_assoc, one_mul, smul_smul, mul_comm j k]
  congr 1
  have h4 : (j.factorial : ℚ) ^ k ≠ 0 := pow_ne_zero _ h2
  rw [eq_mul_inv_iff_mul_eq₀ h3, ← hU, inv_pow]
  field_simp

theorem inv_fact_smul_term_mem (c : W) (j k : ℕ) (hj : j ≠ 0) :
    ((k.factorial : ℚ))⁻¹ • (f c * Lat.dpE f ξ l M j) ^ k ∈ Lat.sub f ξ l M := by
  have e : ((k.factorial : ℚ))⁻¹ • (f c * Lat.dpE f ξ l M j) ^ k =
      f c ^ k * (((k.uniformBell j : ℕ) : B) * Lat.dpE f ξ l M (k * j)) := by
    rw [mul_pow, ← mul_smul_comm, inv_fact_smul_dpE_pow f ξ l M j k hj]
  rw [e]
  have hf : f c ∈ Lat.sub f ξ l M := Subring.subset_closure (Or.inl ⟨c, rfl⟩)
  have hd : Lat.dpE f ξ l M (k * j) ∈ Lat.sub f ξ l M := Subring.subset_closure (Or.inr ⟨_, rfl⟩)
  exact mul_mem (pow_mem hf _) (mul_mem (natCast_mem _ _) hd)

theorem inv_fact_smul_sum_mem {n : ℕ} (c : Fin n → W) (s : Finset (Fin n)) (k : ℕ) :
    ((k.factorial : ℚ))⁻¹ • (∑ i ∈ s, f (c i) * Lat.dpE f ξ l M (i + 1)) ^ k ∈ Lat.sub f ξ l M := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty =>
    rcases k with _ | k
    · simpa using (Lat.sub f ξ l M).one_mem
    · simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact inv_fact_smul_add_pow_mem _ (fun k => inv_fact_smul_term_mem f ξ l M _ _ k (Nat.succ_ne_zero _)) ih k

theorem dpClosed {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (m : ℕ)
    (h : Lat.Hyp f ξ l m) : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ) := by
  intro x hx k
  obtain ⟨n, c, e⟩ := (GlobalTheory.T.mem_lattice_ideal_iff_sum f ξ l M m h x).1 hx
  refine ⟨⟨_, inv_fact_smul_sum_mem f ξ l M c Finset.univ k⟩, ?_⟩
  rw [RatAlgebra.dpow_eq_inv_fact_smul _ (Lat.γB f ξ) hx, e, Ring.inverse_eq_inv']
  rfl

end GlobalTheory.CompanionTheory.LatDP
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SteinOfBijective
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Hodge

variable {R : Type} [CommRing R] {X : Scheme.{0}}

private theorem res_res_lemma {A B C : X.Opens} (f : B ⟶ A) (g' : C ⟶ B) (s : Γ(X, A)) :
    X.presheaf.map g'.op (X.presheaf.map f.op s) = X.presheaf.map (g' ≫ f).op s := by
  rw [op_comp, Functor.map_comp]
  rfl

theorem eq_of_res_affine (W : X.Opens) (a b : Γ(X, W))
    (h : ∀ (V : X.affineOpens) (hV : V.1 ≤ W),
      X.presheaf.map (homOfLE hV).op a = X.presheaf.map (homOfLE hV).op b) : a = b := by
  apply TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun i : {V : X.affineOpens // V.1 ≤ W} => i.1.1) W
    (fun i => homOfLE i.2)
  · intro x hx
    obtain ⟨V, hV, hxV, hVW⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp (AlgebraicGeometry.Scheme.isBasis_affineOpens X) hx
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨⟨⟨V, hV⟩, hVW⟩, hxV⟩
  · intro i
    exact h i.1 i.2

theorem exists_global (g : ∀ U : X.affineOpens, Γ(X, U.1))
    (hg : ∀ (U V : X.affineOpens) (h : V.1 ≤ U.1), X.presheaf.map (homOfLE h).op (g U) = g V) :
    ∃ t : Γ(X, ⊤), ∀ U : X.affineOpens,
      X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op t = g U := by
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf (fun i : X.affineOpens => i.1) g := by
    intro i j
    apply eq_of_res_affine
    intro V hV
    rw [res_res_lemma, res_res_lemma]
    exact (hg i V (hV.trans inf_le_left)).trans (hg j V (hV.trans inf_le_right)).symm
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf (fun i : X.affineOpens => i.1) ⊤
    (fun i => homOfLE le_top) (by
      intro x _
      obtain ⟨V, hV, hxV, -⟩ :=
        TopologicalSpace.Opens.isBasis_iff_nbhd.mp (AlgebraicGeometry.Scheme.isBasis_affineOpens X)
          (show x ∈ (⊤ : X.Opens) from trivial)
      rw [TopologicalSpace.Opens.mem_iSup]
      exact ⟨⟨V, hV⟩, hxV⟩) g hcompat
  exact ⟨t, ht⟩

theorem algebraMap_sec (s : X ⟶ Sp R) (U : X.Opens) (r : R) :
    algebraMap R (Sec s U) r = X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
      (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := rfl

theorem stein_of_bijective (s : X ⟶ Sp R) (h : Function.Bijective s.appTop.hom) : Stein (OAff s) := by
  have key : ∀ (r : R) (U : X.affineOpens),
      (algebraMap R (GlobalTheory.CatCoh.C0 (OAff s)) r) (op U) = X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op
        (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := by
    intro r U
    exact algebraMap_sec s U.1 r
  refine ⟨?_, ?_⟩
  · intro y
    constructor
    · intro hy
      have hg : ∀ (U V : X.affineOpens) (hUV : V.1 ≤ U.1),
          X.presheaf.map (homOfLE hUV).op (y (op U)) = y (op V) := by
        intro U V hUV
        have e := congrFun (congrFun (congrFun hy (op U)) (op V)) (homOfLE (show V ≤ U from hUV)).op
        have e' : (show Γ(X, V.1) from y (op V)) - X.presheaf.map (homOfLE hUV).op (y (op U)) = 0 := e
        exact (sub_eq_zero.mp e').symm
      obtain ⟨t, ht⟩ := exists_global (fun U => y (op U)) hg
      obtain ⟨x, hx⟩ := h.2 t
      refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x, ?_⟩
      funext T
      have hxinv : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
          ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x) = x :=
        congrArg (fun f => CommRingCat.Hom.hom f x) (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id
      have e1 := key ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x) T.unop
      rw [hxinv, hx] at e1
      exact e1.trans (ht T.unop)
    · rintro ⟨r, rfl⟩
      funext T T' φ
      have hc : (GlobalTheory.CatCoh.mp (OAff s) φ) ((algebraMap R (GlobalTheory.CatCoh.C0 (OAff s)) r) T) =
          (algebraMap R (GlobalTheory.CatCoh.C0 (OAff s)) r) T' := (GlobalTheory.CatCoh.mp (OAff s) φ).commutes r
      show (algebraMap R (GlobalTheory.CatCoh.C0 (OAff s)) r) T' -
          (GlobalTheory.CatCoh.mp (OAff s) φ) ((algebraMap R (GlobalTheory.CatCoh.C0 (OAff s)) r) T) = 0
      rw [hc, sub_self]
  · rw [injective_iff_map_eq_zero]
    intro r hr
    have e : s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = 0 := by
      apply eq_of_res_affine
      intro V hV
      rw [map_zero]
      have e2 := congrFun hr (op V)
      rw [key] at e2
      exact e2
    have e3 := h.1 (e.trans (map_zero _).symm)
    have hr2 : (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = r :=
      congrArg (fun f => CommRingCat.Hom.hom f r) (Scheme.ΓSpecIso (CommRingCat.of R)).inv_hom_id
    rw [e3, map_zero] at hr2
    exact hr2.symm

theorem stein_holds : SteinSt := by
  unfold MainStatements.Hodge.SteinSt MainStatements.Hodge.AllAb
  intro R _ A _ g hA _
  exact stein_of_bijective A.hom (GlobalTheory.globalFns_holds (Sp R) A hA)

end GlobalTheory.CompanionTheory.Hodge
end
end
