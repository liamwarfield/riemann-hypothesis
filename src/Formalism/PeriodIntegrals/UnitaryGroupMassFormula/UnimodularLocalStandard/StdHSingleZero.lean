module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepDefs

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.SatStdOfAll
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.ExistsGoodForm
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.CommOfBounded
noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

variable {a : ℕ} {b c : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
variable {m : Type*} [Fintype m] [DecidableEq m]

def IsKv (b : ℤ) (d : ℕ) (lam : ℂ) (v : m → ℂ) : Prop := ∀ i, IsK b d (v i / lam)

lemma cmL_omega1 : (cmL a b d ha hd lam hlam).ω₁ = lam * a := rfl
lemma cmL_omega2 : (cmL a b d ha hd lam hlam).ω₂ = lam * cmTheta b d := rfl

lemma mem_stdLat_iff (L : PeriodPair) (v : m → ℂ) : v ∈ stdLat L m ↔ ∀ i, v i ∈ L.lattice := by
  simp only [PI.ULS.stdLat, AddSubgroup.mem_pi, Set.mem_univ, forall_const,
    Submodule.mem_toAddSubgroup]

private theorem mul_div_cancel_left_of_ne_zero {w : ℂ} (hw : w ≠ 0) (x : ℂ) : w * x / w = x := by
  rw [mul_comm, mul_div_assoc, div_self hw, mul_one]

private theorem mem_cmL_lattice_iff (z : ℂ) :
    z ∈ (PI.ULS.cmL a b d ha hd lam hlam).lattice ↔
      ∃ p q : ℤ, z = lam * ((p : ℂ) * a + q * PI.ULS.cmTheta b d) := by
  rw [lattice_iff]
  simp only [cmL_omega1, cmL_omega2, Complex.real_smul, Complex.ofReal_intCast]
  constructor
  · rintro ⟨p, q, h⟩
    exact ⟨p, q, by rw [h]; ring⟩
  · rintro ⟨p, q, h⟩
    exact ⟨p, q, by rw [h]; ring⟩

lemma isKv_of_mem {s : m → ℂ} (hs : s ∈ stdLat (cmL a b d ha hd lam hlam) m) : IsKv b d lam s := by
  intro i
  obtain ⟨p, q, hpq⟩ := (mem_cmL_lattice_iff _).1 ((mem_stdLat_iff _ s).1 hs i)
  refine ⟨p * (a : ℤ), q, 1, one_ne_zero, ?_⟩
  rw [hpq, mul_div_cancel_left_of_ne_zero hlam]
  push_cast
  ring

private theorem natCast_smul_eq_nsmul (N : ℕ) (y : m → ℂ) : (N : ℂ) • y = N • y := by
  exact Nat.cast_smul_eq_nsmul ℂ N y

private theorem nsmul_apply_eq_natCast_mul (N : ℕ) (v : m → ℂ) (i : m) : (N • v) i = (N : ℂ) * v i := by
  rw [← natCast_smul_eq_nsmul, Pi.smul_apply, smul_eq_mul]

lemma exists_nsmul_mem {v : m → ℂ} (h : IsKv b d lam v) :
    ∃ N : ℕ, N ≠ 0 ∧ N • v ∈ stdLat (cmL a b d ha hd lam hlam) m := by
  choose p q r hr hpq using h
  have hself : ∀ z : ℤ, z ∣ (z.natAbs : ℤ) := fun _ => Int.dvd_natAbs.mpr dvd_rfl
  obtain ⟨M, hM0, hMdvd⟩ : ∃ M : ℕ, M ≠ 0 ∧ ∀ i, r i ∣ (M : ℤ) := by
    refine ⟨∏ j, (r j).natAbs, Finset.prod_ne_zero_iff.mpr fun j _ => Int.natAbs_ne_zero.mpr (hr j),
      fun i => (hself (r i)).trans ?_⟩
    have hi : (r i).natAbs ∣ ∏ j, (r j).natAbs :=
      Finset.dvd_prod_of_mem (fun j => (r j).natAbs) (Finset.mem_univ i)
    exact Int.natCast_dvd_natCast.mpr hi
  refine ⟨a * M, mul_ne_zero ha.ne' hM0, ?_⟩
  rw [mem_stdLat_iff]
  intro i
  obtain ⟨k, hk⟩ := hMdvd i
  have hk' : (M : ℂ) = (r i : ℂ) * k := by exact_mod_cast hk
  have e : v i = v i / lam * lam := (div_eq_iff hlam).mp rfl
  have hv : (r i : ℂ) * v i = lam * (p i + q i * PI.ULS.cmTheta b d) := by
    calc (r i : ℂ) * v i = (r i * (v i / lam)) * lam := by rw [mul_assoc, ← e]
      _ = (p i + q i * PI.ULS.cmTheta b d) * lam := by rw [hpq i]
      _ = lam * (p i + q i * PI.ULS.cmTheta b d) := mul_comm _ _
  rw [mem_cmL_lattice_iff]
  refine ⟨k * p i, a * k * q i, ?_⟩
  rw [nsmul_apply_eq_natCast_mul, Nat.cast_mul, hk']
  push_cast
  linear_combination ((a : ℂ) * k) * hv

lemma isKv_of_nsmul {v : m → ℂ} {N : ℕ} (hN : N ≠ 0) (h : IsKv b d lam (N • v)) : IsKv b d lam v := by
  intro i
  obtain ⟨p, q, r, hr, h'⟩ := h i
  refine ⟨p, q, r * N, mul_ne_zero hr (by exact_mod_cast hN), ?_⟩
  rw [← h', nsmul_apply_eq_natCast_mul]
  push_cast
  ring

lemma isKv_sub {v w : m → ℂ} (hv : IsKv b d lam v) (hw : IsKv b d lam w) : IsKv b d lam (v - w) := by
  intro i
  rw [Pi.sub_apply, sub_div]
  exact isK_sub (hv i) (hw i)

lemma isKv_smul {e : ℤ} (hn : cmTheta b d * (b - cmTheta b d) = (e : ℂ)) {t : ℂ} {v : m → ℂ}
    (ht : IsK b d t) (hv : IsKv b d lam v) : IsKv b d lam (t • v) := by
  intro i
  rw [Pi.smul_apply, smul_eq_mul, mul_div_assoc]
  exact isK_mul hn ht (hv i)

lemma isKv_single {w : ℂ} (hw : IsK b d (w / lam)) (i : m) : IsKv b d lam (Pi.single i w) := by
  intro j
  rw [Pi.single_apply]
  split_ifs
  · exact hw
  · rw [zero_div]
    exact ⟨0, 0, 1, one_ne_zero, by simp⟩

def kappa (L : PeriodPair) (lam : ℂ) : ℂ := lam * conj lam * ((area L : ℝ) : ℂ)⁻¹

lemma kappa_conj (L : PeriodPair) (lam : ℂ) : conj (kappa L lam) = kappa L lam := by
  simp only [kappa]
  rw [map_mul, map_mul, map_inv₀, Complex.conj_conj, Complex.conj_ofReal]
  ring

lemma kappa_ne (L : PeriodPair) (hlam : lam ≠ 0) : kappa L lam ≠ 0 := by
  have harea : ((area L : ℝ) : ℂ) ≠ 0 := by
    rw [area_eq]
    exact Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr (detD_ne L))
  have hc : conj lam ≠ 0 := by rwa [Ne, map_eq_zero]
  simp only [kappa]
  exact mul_ne_zero (mul_ne_zero hlam hc) (inv_ne_zero harea)

lemma stdH_kappa (L : PeriodPair) (hlam : lam ≠ 0) (x y : m → ℂ) :
    stdH L m x y = kappa L lam * ∑ i, (x i / lam) * conj (y i / lam) := by
  have hc : conj lam ≠ 0 := by rwa [Ne, map_eq_zero]
  have h1 : lam * lam⁻¹ = 1 := mul_inv_cancel₀ hlam
  have h2 : conj lam * (conj lam)⁻¹ = 1 := mul_inv_cancel₀ hc
  rw [stdH_apply]
  simp only [kappa]
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_div₀]
  linear_combination (-(x i * conj (y i) * ((area L : ℝ) : ℂ)⁻¹) * (conj lam * (conj lam)⁻¹)) * h1 +
    (-(x i * conj (y i) * ((area L : ℝ) : ℂ)⁻¹)) * h2

lemma isK_H {e : ℤ} (hn : cmTheta b d * (b - cmTheta b d) = (e : ℂ)) (L : PeriodPair) (hlam : lam ≠ 0)
    {x y : m → ℂ} (hx : IsKv b d lam x) (hy : IsKv b d lam y) :
    ∃ t, IsK b d t ∧ stdH L m x y = kappa L lam * t :=
  ⟨∑ i, (x i / lam) * conj (y i / lam),
    isK_sum hn _ _ fun i _ => isK_mul hn (hx i) (isK_conj (hy i)),
    stdH_kappa L hlam x y⟩

private theorem intCast_smul_eq_zsmul (p : ℤ) (y : m → ℂ) : (p : ℂ) • y = p • y := by
  exact Int.cast_smul_eq_zsmul ℂ p y

private theorem nsmul_intCast_smul_comm (N : ℕ) (p : ℤ) (y : m → ℂ) : N • ((p : ℂ) • y) = p • (N • y) := by
  rw [← natCast_smul_eq_nsmul N ((p : ℂ) • y), ← natCast_smul_eq_nsmul N y, smul_comm (N : ℂ) (p : ℂ) y,
    intCast_smul_eq_zsmul p ((N : ℂ) • y)]

private theorem nsmul_mem_of_dvd_of_nsmul_mem {S : AddSubgroup (m → ℂ)} {x : m → ℂ} {n N : ℕ} (hnN : n ∣ N)
    (hx : n • x ∈ S) : N • x ∈ S := by
  obtain ⟨k, rfl⟩ := hnN
  have e : (n * k) • x = k • (n • x) := by
    calc (n * k) • x = ((n * k : ℕ) : ℂ) • x := (natCast_smul_eq_nsmul _ _).symm
      _ = (k : ℂ) • (n : ℂ) • x := by rw [smul_smul, Nat.cast_mul, mul_comm]
      _ = k • n • x := by rw [natCast_smul_eq_nsmul, natCast_smul_eq_nsmul]
  rw [e]
  exact nsmul_mem hx k

lemma bounded_map (φ : (m → ℂ) →ₗ[ℂ] (m → ℂ))
    (h1 : ∀ i, IsKv b d lam (φ (Pi.single i (cmL a b d ha hd lam hlam).ω₁)))
    (h2 : ∀ i, IsKv b d lam (φ (Pi.single i (cmL a b d ha hd lam hlam).ω₂))) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ s ∈ stdLat (cmL a b d ha hd lam hlam) m,
      N • φ s ∈ stdLat (cmL a b d ha hd lam hlam) m := by
  choose N1 hN1 hm1 using fun i =>
    exists_nsmul_mem (ha := ha) (hd := hd) (hlam := hlam) (h1 i)
  choose N2 hN2 hm2 using fun i =>
    exists_nsmul_mem (ha := ha) (hd := hd) (hlam := hlam) (h2 i)
  refine ⟨∏ j, N1 j * N2 j, Finset.prod_ne_zero_iff.mpr fun j _ => mul_ne_zero (hN1 j) (hN2 j), ?_⟩
  have hdvd : ∀ i, N1 i * N2 i ∣ ∏ j, N1 j * N2 j := fun i =>
    Finset.dvd_prod_of_mem (fun j => N1 j * N2 j) (Finset.mem_univ i)
  have k1 : ∀ i, (∏ j, N1 j * N2 j) • φ (Pi.single i (PI.ULS.cmL a b d ha hd lam hlam).ω₁) ∈
      PI.ULS.stdLat (PI.ULS.cmL a b d ha hd lam hlam) m := fun i =>
    nsmul_mem_of_dvd_of_nsmul_mem ((dvd_mul_right (N1 i) (N2 i)).trans (hdvd i)) (hm1 i)
  have k2 : ∀ i, (∏ j, N1 j * N2 j) • φ (Pi.single i (PI.ULS.cmL a b d ha hd lam hlam).ω₂) ∈
      PI.ULS.stdLat (PI.ULS.cmL a b d ha hd lam hlam) m := fun i =>
    nsmul_mem_of_dvd_of_nsmul_mem ((dvd_mul_left (N2 i) (N1 i)).trans (hdvd i)) (hm2 i)
  intro s hs
  have hs' := (mem_stdLat_iff _ s).1 hs
  choose p q hpq using fun i => (lattice_iff _ _).1 (hs' i)
  have hs_sum : s = ∑ i, Pi.single i (s i) := by
    exact (Finset.univ_sum_single s).symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hs_sum, map_sum, Finset.smul_sum]
  refine sum_mem fun i _ => ?_
  have e : Pi.single i (s i) = ((p i : ℤ) : ℂ) • Pi.single i (PI.ULS.cmL a b d ha hd lam hlam).ω₁ +
      ((q i : ℤ) : ℂ) • Pi.single i (PI.ULS.cmL a b d ha hd lam hlam).ω₂ := by
    rw [hpq i]
    funext j
    by_cases h : j = i
    · subst h
      simp [Complex.real_smul]
    · simp [Pi.single_apply, h]
  rw [e, map_add (f := _), map_smul, map_smul, smul_add, nsmul_intCast_smul_comm, nsmul_intCast_smul_comm]
  exact add_mem (zsmul_mem (k1 i) _) (zsmul_mem (k2 i) _)

lemma comm_of_bounded (σ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)) {N N' : ℕ} (hN : N ≠ 0) (hN' : N' ≠ 0)
    (h1 : ∀ s ∈ stdLat (cmL a b d ha hd lam hlam) m, N • σ s ∈ stdLat (cmL a b d ha hd lam hlam) m)
    (h2 : ∀ s ∈ stdLat (cmL a b d ha hd lam hlam) m, N' • σ.symm s ∈ stdLat (cmL a b d ha hd lam hlam) m) :
    relIdx (stdLat (cmL a b d ha hd lam hlam) m)
        (imgLat (σ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (stdLat (cmL a b d ha hd lam hlam) m)) ≠ 0 ∧
      relIdx (imgLat (σ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (stdLat (cmL a b d ha hd lam hlam) m))
        (stdLat (cmL a b d ha hd lam hlam) m) ≠ 0 := by
  unfold PI.ULS.relIdx PI.ULS.imgLat
  refine ⟨?_, ?_⟩
  · rw [← AddSubgroup.relIndex_comap]
    refine relIdx_ne_zero_of_le_left ?_ (stdLat_smul_idx _ m hN)
    intro x hx
    obtain ⟨s, hs, rfl⟩ := AddSubgroup.mem_map.mp hx
    rw [AddSubgroup.mem_comap]
    show σ ((N : ℂ) • s) ∈ _
    rw [map_smul, natCast_smul_eq_nsmul]
    exact h1 s hs
  · refine relIdx_ne_zero_of_le_left ?_ (stdLat_smul_idx _ m hN')
    intro x hx
    obtain ⟨s, hs, rfl⟩ := AddSubgroup.mem_map.mp hx
    refine AddSubgroup.mem_map.mpr ⟨N' • σ.symm s, h2 s hs, ?_⟩
    show σ (N' • σ.symm s) = (N' : ℂ) • s
    rw [map_nsmul, LinearEquiv.apply_symm_apply, natCast_smul_eq_nsmul]

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.QequivApply
noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

section QR
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (H : Sesq V)

def qmap (z : V) (ν : ℂ) : V →ₗ[ℂ] V := LinearMap.id - (ν • H.flip z).smulRight z

lemma qmap_apply (z : V) (ν : ℂ) (w : V) : qmap H z ν w = w - (ν * H w z) • z := by
  simp [qmap]

lemma qmap_coef {c h k : ℂ} (hc0 : c ≠ 0) (hc : c + conj c = k) :
    c⁻¹ * h + (conj c)⁻¹ * (h - c⁻¹ * h * k) = 0 := by
  subst hc
  have hc1 : conj c ≠ 0 := by simpa using hc0
  field_simp
  ring

lemma qmap_qmap {z : V} {c : ℂ} (hc0 : c ≠ 0) (hc : c + conj c = H z z) (w : V) :
    qmap H z (conj c)⁻¹ (qmap H z c⁻¹ w) = w := by
  rw [qmap_apply, qmap_apply]
  have e : H (w - (c⁻¹ * H w z) • z) z = H w z - c⁻¹ * H w z * H z z := by
    simp [map_sub, map_smul, mul_assoc]
  rw [e, sub_sub, ← add_smul, qmap_coef hc0 hc, zero_smul, sub_zero]

lemma qmap_qmap' {z : V} {c : ℂ} (hc0 : c ≠ 0) (hc : c + conj c = H z z) (w : V) :
    qmap H z c⁻¹ (qmap H z (conj c)⁻¹ w) = w := by
  have h1 := qmap_qmap H (c := conj c) (by simpa using hc0) (by rw [Complex.conj_conj, add_comm]; exact hc) w
  rwa [Complex.conj_conj] at h1

def qequiv (z : V) {c : ℂ} (hc0 : c ≠ 0) (hc : c + conj c = H z z) : V ≃ₗ[ℂ] V :=
  LinearEquiv.ofLinear (qmap H z c⁻¹) (qmap H z (conj c)⁻¹)
    (LinearMap.ext fun w => qmap_qmap' H hc0 hc w) (LinearMap.ext fun w => qmap_qmap H hc0 hc w)

lemma qequiv_apply (z : V) {c : ℂ} (hc0 : c ≠ 0) (hc : c + conj c = H z z) (w : V) :
    qequiv H z hc0 hc w = w - (c⁻¹ * H w z) • z := by
  show qmap H z c⁻¹ w = _
  exact qmap_apply H z c⁻¹ w

lemma qequiv_isom (hsym : ∀ x y, H y x = conj (H x y)) (z : V) {c : ℂ} (hc0 : c ≠ 0)
    (hc : c + conj c = H z z) : IsIsom H H (qequiv H z hc0 hc : V →ₗ[ℂ] V) := by
  intro x y
  have hc1 : conj c ≠ 0 := by simpa using hc0
  simp only [LinearEquiv.coe_coe]
  rw [qequiv_apply, qequiv_apply]
  simp only [map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, map_mul, map_inv₀,
    RingHom.id_apply, hsym y z, ← hc]
  field_simp
  ring

end QR

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

section Transport
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

lemma mem_dualLat_iff (H : Sesq V) (Λ : AddSubgroup V) (x : V) :
    x ∈ dualLat H Λ ↔ ∀ y ∈ Λ, ∃ k : ℤ, altE H x y = k := by
  exact Iff.rfl

lemma mem_imgLat_iff (g : V ≃ₗ[ℂ] V) (Λ : AddSubgroup V) (x : V) :
    x ∈ imgLat (g : V →ₗ[ℂ] V) Λ ↔ ∃ y ∈ Λ, g y = x := by
  simp [imgLat, AddSubgroup.mem_map]

lemma selfDual_img (H : Sesq V) (g : V ≃ₗ[ℂ] V) (hg : IsIsom H H (g : V →ₗ[ℂ] V)) {Λ : AddSubgroup V}
    (hΛ : IsSelfDual H Λ) : IsSelfDual H (imgLat (g : V →ₗ[ℂ] V) Λ) := by
  have hg' : ∀ a b, H (g a) (g b) = H a b := fun a b => by simpa using hg a b
  unfold IsSelfDual at hΛ ⊢
  ext x
  rw [mem_dualLat_iff, mem_imgLat_iff]
  obtain ⟨x₀, rfl⟩ := g.surjective x
  have key : (∀ y ∈ imgLat (g : V →ₗ[ℂ] V) Λ, ∃ k : ℤ, altE H (g x₀) y = k) ↔ x₀ ∈ dualLat H Λ := by
    rw [mem_dualLat_iff]
    constructor
    · intro h y hy
      obtain ⟨k, hk⟩ := h (g y) ((mem_imgLat_iff g Λ _).mpr ⟨y, hy, rfl⟩)
      exact ⟨k, by rw [← hk]; simp only [altE]; rw [hg']⟩
    · intro h y' hy'
      obtain ⟨y, hy, rfl⟩ := (mem_imgLat_iff g Λ y').mp hy'
      obtain ⟨k, hk⟩ := h y hy
      exact ⟨k, by simp only [altE]; rw [hg']; exact hk⟩
  rw [key, hΛ]
  constructor
  · intro h
    exact ⟨x₀, h, rfl⟩
  · rintro ⟨y, hy, hxy⟩
    rwa [g.injective hxy] at hy

lemma comm_img (g : V ≃ₗ[ℂ] V) {S Λ : AddSubgroup V}
    (hg1 : relIdx S (imgLat (g : V →ₗ[ℂ] V) S) ≠ 0) (hg2 : relIdx (imgLat (g : V →ₗ[ℂ] V) S) S ≠ 0)
    (h1 : relIdx S Λ ≠ 0) (h2 : relIdx Λ S ≠ 0) :
    relIdx S (imgLat (g : V →ₗ[ℂ] V) Λ) ≠ 0 ∧ relIdx (imgLat (g : V →ₗ[ℂ] V) Λ) S ≠ 0 := by
  have hinj : Function.Injective (g : V →ₗ[ℂ] V).toAddMonoidHom := g.injective
  have hm : ∀ A B : AddSubgroup V, relIdx (imgLat (g : V →ₗ[ℂ] V) A) (imgLat (g : V →ₗ[ℂ] V) B) = relIdx A B :=
    fun A B => AddSubgroup.relIndex_map_map_of_injective A B hinj
  refine ⟨?_, ?_⟩
  · exact AddSubgroup.relIndex_ne_zero_trans hg1 (by rw [← hm S Λ] at h1; exact h1)
  · exact AddSubgroup.relIndex_ne_zero_trans (by rw [← hm Λ S] at h2; exact h2) hg2

lemma imgLat_trans (g σ : V ≃ₗ[ℂ] V) (Λ : AddSubgroup V) :
    imgLat ((g.trans σ : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) Λ = imgLat (σ : V →ₗ[ℂ] V) (imgLat (g : V →ₗ[ℂ] V) Λ) := by
  ext x
  simp only [mem_imgLat_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨g y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

lemma isom_trans (H : Sesq V) (g σ : V ≃ₗ[ℂ] V) (hg : IsIsom H H (g : V →ₗ[ℂ] V)) (hσ : IsIsom H H (σ : V →ₗ[ℂ] V)) :
    IsIsom H H ((g.trans σ : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) := by
  intro x y
  have h1 := hσ (g x) (g y)
  have h2 := hg x y
  simp only [LinearEquiv.coe_coe] at h1 h2 ⊢
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, h1, h2]

end Transport

lemma exists_good_form {a : ℕ} {b c : ℤ} {d : ℕ} (hok : CmOK a b c d) {l : ℕ} (hl : l.Prime) :
    ∃ x y : ℤ, ¬ (l : ℤ) ∣ a * x ^ 2 + b * x * y + c * y ^ 2 := by
  obtain ⟨hE, _, _, hd⟩ := hok
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  have h1 := hcon 1 0
  have h2 := hcon 0 1
  have h3 := hcon 1 1
  norm_num at h1 h2 h3
  have hb : (l : ℤ) ∣ b := by
    have h4 := dvd_sub (dvd_sub h3 h1) h2
    have e : (a : ℤ) + b + c - a - c = b := by ring
    rwa [e] at h4
  have hl2 : (l : ℤ) ^ 2 ∣ (d : ℤ) := by
    have e : (d : ℤ) = 4 * a * c - b ^ 2 := by linarith
    rw [e]
    refine dvd_sub ?_ (pow_dvd_pow_of_dvd hb 2)
    rw [pow_two]
    exact mul_dvd_mul (dvd_mul_of_dvd_right h1 4) h2
  have hl2' : l ^ 2 ∣ d := by exact_mod_cast hl2
  have hld : l ∣ d := (dvd_pow_self l two_ne_zero).trans hl2'
  have hleq : l = d := (Nat.prime_dvd_prime_iff_eq hl hd).mp hld
  subst hleq
  have h5 := Nat.le_of_dvd hd.pos hl2'
  have h6 := hd.two_le
  nlinarith

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

variable {a : ℕ} {b c : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
variable {m : Type*} [Fintype m] [DecidableEq m]

lemma altE_single (L : PeriodPair) (v : m → ℂ) (n : ℕ) (j : m) (w : ℂ) :
    altE (stdH L m) v (n • Pi.single j w) = (n : ℝ) * (v j * conj w).im / area L := by
  classical
  unfold altE
  rw [stdH_apply]
  have hs : (∑ i, v i * conj ((n • Pi.single j w : m → ℂ) i)) = (n : ℂ) * (v j * conj w) := by
    rw [Finset.sum_eq_single j]
    · simp [nsmul_eq_mul]
      ring
    · intro i _ hi
      simp [hi]
    · simp
  rw [hs, ← Complex.ofReal_inv, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    zero_add, ← Complex.ofReal_natCast, Complex.im_ofReal_mul, div_eq_mul_inv]

lemma alpha_eq (x y : ℤ) :
    lam * ((x * a : ℂ) + y * cmTheta b d) =
      (x : ℝ) • (cmL a b d ha hd lam hlam).ω₁ + (y : ℝ) • (cmL a b d ha hd lam hlam).ω₂ := by
  rw [cmL_omega1, cmL_omega2]
  simp only [Complex.real_smul]
  push_cast
  ring

lemma theta_alpha_eq (hn : cmTheta b d * (b - cmTheta b d) = (a : ℂ) * c) (x y : ℤ) :
    cmTheta b d * (lam * ((x * a : ℂ) + y * cmTheta b d)) =
      ((-y * c : ℤ) : ℝ) • (cmL a b d ha hd lam hlam).ω₁ +
        ((x * a + y * b : ℤ) : ℝ) • (cmL a b d ha hd lam hlam).ω₂ := by
  rw [cmL_omega1, cmL_omega2]
  simp only [Complex.real_smul]
  push_cast
  linear_combination (-(lam * y)) * hn

lemma coord_mem (hn : cmTheta b d * (b - cmTheta b d) = (a : ℂ) * c) (x y : ℤ) (n : ℕ) (w : ℂ)
    (h1 : ∃ k : ℤ, (n : ℝ) * (w * conj (lam * ((x * a : ℂ) + y * cmTheta b d))).im
      / area (cmL a b d ha hd lam hlam) = k)
    (h2 : ∃ k : ℤ, (n : ℝ) * (w * conj (cmTheta b d * (lam * ((x * a : ℂ) + y * cmTheta b d)))).im
      / area (cmL a b d ha hd lam hlam) = k) :
    ((n * (a * x ^ 2 + b * x * y + c * y ^ 2) : ℤ) : ℂ) * w ∈ (cmL a b d ha hd lam hlam).lattice := by
  set L := cmL a b d ha hd lam hlam with hL
  obtain ⟨s, t, hz⟩ := coords L ((n : ℂ) * w)
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  have hnim : ∀ u : ℂ, (n : ℝ) * (w * u).im = (((n : ℂ) * w) * u).im := by
    intro u
    rw [mul_assoc]
    simp [Complex.mul_im]
  rw [hnim, hz, alpha_eq (ha := ha) (hd := hd) (hlam := hlam), im_mul_conj] at hk1
  rw [hnim, hz, theta_alpha_eq (ha := ha) (hd := hd) (hlam := hlam) hn, im_mul_conj] at hk2
  obtain ⟨j1, hj1⟩ := int_of_div L hk1
  obtain ⟨j2, hj2⟩ := int_of_div L hk2
  push_cast at hj1 hj2
  have hQs : ((a * x ^ 2 + b * x * y + c * y ^ 2 : ℤ) : ℝ) * s = ((-(y * c * j1 + x * j2) : ℤ) : ℝ) := by
    push_cast
    linear_combination (-((y : ℝ) * c)) * hj1 + (-(x : ℝ)) * hj2
  have hQt : ((a * x ^ 2 + b * x * y + c * y ^ 2 : ℤ) : ℝ) * t =
      (((x * a + y * b) * j1 - y * j2 : ℤ) : ℝ) := by
    push_cast
    linear_combination ((x : ℝ) * a + y * b) * hj1 + (-(y : ℝ)) * hj2
  rw [show ((n * (a * x ^ 2 + b * x * y + c * y ^ 2) : ℤ) : ℂ) * w =
      ((a * x ^ 2 + b * x * y + c * y ^ 2 : ℤ) : ℂ) * ((n : ℂ) * w) by push_cast; ring, hz]
  refine (lattice_iff L _).mpr ⟨-(y * c * j1 + x * j2), (x * a + y * b) * j1 - y * j2, ?_⟩
  have cs := congrArg (fun r : ℝ => (r : ℂ)) hQs
  have ct := congrArg (fun r : ℝ => (r : ℂ)) hQt
  simp only [Complex.ofReal_mul, Complex.ofReal_intCast] at cs ct
  simp only [Complex.real_smul, Complex.ofReal_intCast]
  linear_combination L.ω₁ * cs + L.ω₂ * ct

lemma sat_std_of_all (hok : CmOK a b c d) {l : ℕ} (hl : l.Prime) (x y : ℤ)
    (hQ : ¬ (l : ℤ) ∣ a * x ^ 2 + b * x * y + c * y ^ 2) (Λ : AddSubgroup (m → ℂ))
    (hsd : IsSelfDual (stdH (cmL a b d ha hd lam hlam) m) Λ) (hθ : ∀ v ∈ Λ, cmTheta b d • v ∈ Λ)
    (hall : ∀ j, SatMem l Λ (Pi.single j (lam * ((x * a : ℂ) + y * cmTheta b d)))) :
    ∃ n : ℕ, ¬ l ∣ n ∧ ∀ v ∈ Λ, n • v ∈ stdLat (cmL a b d ha hd lam hlam) m := by
  classical
  have hn := theta_norm hok.1
  have hall' : ∀ j, ∃ N : ℕ, ¬ l ∣ N ∧
      N • (Pi.single j (lam * ((x * a : ℂ) + y * cmTheta b d)) : m → ℂ) ∈ Λ := hall
  choose N hNl hNmem using hall'
  set Q : ℤ := a * x ^ 2 + b * x * y + c * y ^ 2 with hQdef
  refine ⟨Q.natAbs * Q.natAbs * ∏ j, N j, ?_, ?_⟩
  · intro hdvd
    rcases (Nat.Prime.dvd_mul hl).mp hdvd with h | h
    · rcases (Nat.Prime.dvd_mul hl).mp h with h' | h' <;> exact hQ (Int.natCast_dvd.mpr h')
    · obtain ⟨j, _, hj⟩ := (Prime.dvd_finsetProd_iff hl.prime _).mp h
      exact hNl j hj
  · intro v hv
    have hvd : v ∈ dualLat (stdH (cmL a b d ha hd lam hlam) m) Λ := by
      rw [hsd]
      exact hv
    rw [mem_dualLat_iff] at hvd
    rw [mem_stdLat_iff]
    intro i
    have e1 := hvd _ (hNmem i)
    have e2 := hvd _ (hθ _ (hNmem i))
    have hsm : cmTheta b d • (N i • Pi.single i (lam * ((x * a : ℂ) + y * cmTheta b d)) : m → ℂ) =
        N i • Pi.single i (cmTheta b d * (lam * ((x * a : ℂ) + y * cmTheta b d))) := by
      ext k
      by_cases hk : k = i
      · subst hk
        simp [nsmul_eq_mul]
        ring
      · simp [hk]
    rw [altE_single] at e1
    rw [hsm, altE_single] at e2
    have hm := coord_mem hn x y (N i) (v i) e1 e2
    have hmem : ((N i : ℤ) * Q) • v i ∈ (cmL a b d ha hd lam hlam).lattice := by
      rw [zsmul_eq_mul]
      exact_mod_cast hm
    have hnZ : ((Q.natAbs * Q.natAbs * ∏ j, N j : ℕ) : ℤ) =
        (Q * ∏ j ∈ Finset.univ.erase i, (N j : ℤ)) * ((N i : ℤ) * Q) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      push_cast
      rw [abs_mul_abs_self]
      ring
    rw [Pi.smul_apply, ← natCast_zsmul, hnZ, mul_smul]
    exact Submodule.smul_mem _ _ hmem

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

variable {a : ℕ} {b c : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
variable {m : Type*} [Fintype m] [DecidableEq m]

lemma stdH_symm (L : PeriodPair) (x y : m → ℂ) : stdH L m y x = conj (stdH L m x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [stdH_apply, stdH_apply, map_mul, map_inv₀, Complex.conj_ofReal, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, Complex.conj_conj, mul_comm]

lemma stdH_single_zero (L : PeriodPair) (j : m) (w : ℂ) {z : m → ℂ} (hz : z j = 0) :
    stdH L m (Pi.single j w) z = 0 := by
  rw [stdH_apply]
  have hsum : ∑ i, (Pi.single j w : m → ℂ) i * conj (z i) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases h : i = j
    · subst h
      rw [hz, map_zero, mul_zero]
    · simp [h]
  rw [hsum, zero_mul]

private theorem stdH_sub_eq_and_add_conj_eq_of_stdH_eq (L : PeriodPair) (v f' : m → ℂ)
    (hvv : PI.ULS.stdH L m v v = PI.ULS.stdH L m f' f') :
    PI.ULS.stdH L m v (v - f') = PI.ULS.stdH L m v v - PI.ULS.stdH L m v f' ∧
      PI.ULS.stdH L m v (v - f') + conj (PI.ULS.stdH L m v (v - f')) =
        PI.ULS.stdH L m (v - f') (v - f') := by
  have h1 : PI.ULS.stdH L m v (v - f') = PI.ULS.stdH L m v v - PI.ULS.stdH L m v f' :=
    map_sub (PI.ULS.stdH L m v) v f'
  refine ⟨h1, ?_⟩
  have h2 : PI.ULS.stdH L m (v - f') (v - f') =
      PI.ULS.stdH L m v v - PI.ULS.stdH L m v f' - (PI.ULS.stdH L m f' v - PI.ULS.stdH L m f' f') := by
    simp only [map_sub, LinearMap.sub_apply]
    ring
  rw [h1, h2, map_sub, ← stdH_symm L v f', ← stdH_symm L v v, hvv]
  ring

private theorem isKv_sub_stdH_smul {L : PeriodPair} {e : ℤ}
    (hn : PI.ULS.cmTheta b d * (b - PI.ULS.cmTheta b d) = (e : ℂ)) (hl0 : lam ≠ 0) {z w : m → ℂ} {t : ℂ}
    (ht : IsK b d t) (hz : IsKv b d lam z) (hw : IsKv b d lam w) :
    IsKv b d lam (w - ((kappa L lam * t)⁻¹ * PI.ULS.stdH L m w z) • z) := by
  obtain ⟨s, hs, hH⟩ := isK_H hn L hl0 hw hz
  rw [hH, mul_inv_rev, mul_assoc, inv_mul_cancel_left₀ (kappa_ne L hl0)]
  exact isKv_sub hw (isKv_smul hn (isK_mul hn (isK_inv hn ht) hs) hz)

lemma qrefl_to (hok : CmOK a b c d) (v f' : m → ℂ)
    (hvv : stdH (cmL a b d ha hd lam hlam) m v v = stdH (cmL a b d ha hd lam hlam) m f' f')
    (hne : stdH (cmL a b d ha hd lam hlam) m v v - stdH (cmL a b d ha hd lam hlam) m v f' ≠ 0)
    (hvK : IsKv b d lam v) (hfK : IsKv b d lam f') :
    ∃ σ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ),
      IsIsom (stdH (cmL a b d ha hd lam hlam) m) (stdH (cmL a b d ha hd lam hlam) m) (σ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) ∧
      relIdx (stdLat (cmL a b d ha hd lam hlam) m) (imgLat (σ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (stdLat (cmL a b d ha hd lam hlam) m)) ≠ 0 ∧
      relIdx (imgLat (σ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (stdLat (cmL a b d ha hd lam hlam) m)) (stdLat (cmL a b d ha hd lam hlam) m) ≠ 0 ∧
      σ v = f' ∧ ∀ w, stdH (cmL a b d ha hd lam hlam) m w (v - f') = 0 → σ w = w := by
  obtain ⟨hvz, hκ⟩ := stdH_sub_eq_and_add_conj_eq_of_stdH_eq (PI.ULS.cmL a b d ha hd lam hlam) v f' hvv
  have hκ0 : PI.ULS.stdH (PI.ULS.cmL a b d ha hd lam hlam) m v (v - f') ≠ 0 := by
    rw [hvz]; exact hne
  have hn : PI.ULS.cmTheta b d * (b - PI.ULS.cmTheta b d) = ((a * c : ℤ) : ℂ) := by
    rw [theta_norm hok.1]; push_cast; ring
  have hzK : IsKv b d lam (v - f') := isKv_sub hvK hfK
  obtain ⟨t, ht, htF⟩ := isK_H hn (PI.ULS.cmL a b d ha hd lam hlam) hlam hvK hzK
  have htF' : conj (PI.ULS.stdH (PI.ULS.cmL a b d ha hd lam hlam) m v (v - f')) =
      kappa (PI.ULS.cmL a b d ha hd lam hlam) lam * conj t := by
    rw [htF, map_mul, kappa_conj]
  obtain ⟨σ, hσ⟩ : ∃ σ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ),
      σ = qequiv (PI.ULS.stdH (PI.ULS.cmL a b d ha hd lam hlam) m) (v - f') hκ0 hκ := ⟨_, rfl⟩
  have hσapp : ∀ x, σ x = x - ((PI.ULS.stdH (PI.ULS.cmL a b d ha hd lam hlam) m v (v - f'))⁻¹ *
      PI.ULS.stdH (PI.ULS.cmL a b d ha hd lam hlam) m x (v - f')) • (v - f') := by
    intro x; rw [hσ, qequiv_apply]
  have hσsymm : ∀ x, σ.symm x = x - ((conj (PI.ULS.stdH (PI.ULS.cmL a b d ha hd lam hlam) m v (v - f')))⁻¹ *
      PI.ULS.stdH (PI.ULS.cmL a b d ha hd lam hlam) m x (v - f')) • (v - f') := by
    intro x; rw [hσ, ← qmap_apply]; rfl
  have hs1 : ∀ i : m, IsKv b d lam (Pi.single i (PI.ULS.cmL a b d ha hd lam hlam).ω₁ : m → ℂ) := fun i =>
    isKv_single (by
      rw [cmL_omega1, mul_div_cancel_left₀ _ hlam]
      exact_mod_cast isK_int (b := b) (d := d) (a : ℤ)) i
  have hs2 : ∀ i : m, IsKv b d lam (Pi.single i (PI.ULS.cmL a b d ha hd lam hlam).ω₂ : m → ℂ) := fun i =>
    isKv_single (by
      rw [cmL_omega2, mul_div_cancel_left₀ _ hlam]
      exact isK_theta) i
  have hφ : ∀ x, IsKv b d lam x → IsKv b d lam ((σ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) x) := by
    intro x hx
    rw [LinearEquiv.coe_coe, hσapp, htF]
    exact isKv_sub_stdH_smul hn hlam ht hzK hx
  have hψ : ∀ x, IsKv b d lam x →
      IsKv b d lam ((σ.symm : (m → ℂ) →ₗ[ℂ] (m → ℂ)) x) := by
    intro x hx
    rw [LinearEquiv.coe_coe, hσsymm, htF']
    exact isKv_sub_stdH_smul hn hlam (isK_conj ht) hzK hx
  obtain ⟨N, hN, hN1⟩ := bounded_map (a := a) (b := b) (d := d) (ha := ha) (hd := hd)
    (lam := lam) (hlam := hlam) (σ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (fun i => hφ _ (hs1 i)) (fun i => hφ _ (hs2 i))
  obtain ⟨N', hN', hN2⟩ := bounded_map (a := a) (b := b) (d := d) (ha := ha) (hd := hd)
    (lam := lam) (hlam := hlam) (σ.symm : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (fun i => hψ _ (hs1 i)) (fun i => hψ _ (hs2 i))
  have hidx := comm_of_bounded σ hN hN' (fun s hs => hN1 s hs) (fun s hs => hN2 s hs)
  refine ⟨σ, ?_, hidx.1, hidx.2, ?_, ?_⟩
  · rw [hσ]
    exact qequiv_isom _ (fun x y => stdH_symm _ x y) _ hκ0 hκ
  · rw [hσapp, inv_mul_cancel₀ hκ0, one_smul, sub_sub_cancel]
  · intro w hw
    rw [hσapp, hw, mul_zero, zero_smul, sub_zero]

end PI.UnitaryGroupMassFormula.UnimodLocStd
