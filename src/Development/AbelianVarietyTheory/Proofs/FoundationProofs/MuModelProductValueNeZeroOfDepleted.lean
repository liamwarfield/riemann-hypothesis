module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CentralIdempotentIrreducibleCharacterProps

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AtkinLehnerEis
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DirichletFourierMixedTwistMultiple
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DirichletFourierMixedTwistMultiple
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM Filter Topology
open scoped MatrixGroups Real ComplexConjugate

noncomputable section

namespace GlobalTheory.EisM

theorem hat_mix_twist : ∀ (N l : ℕ) (ν : DirichletCharacter ℂ N) (ω : DirichletCharacter ℂ l) (φ : ZMod l → ℂ) (a c : ℤ),
    0 < N → 0 < l → N.Coprime l → (∀ x : ℤ, hat φ x = ch ω x) →
    (∀ d u : ZMod l, IsUnit d → φ u = ω d * φ (d * u)) → IsUnit (c : ZMod N) → IsUnit (a : ZMod l) →
    (∃ C : ℂ, C ≠ 0 ∧ ∀ x : ℤ, hat (fun z : ZMod (N * l) => ν (-(c : ZMod N) * ZMod.castHom (Dvd.intro l rfl) (ZMod N) z) *
        φ ((a : ZMod l) * ZMod.castHom (Dvd.intro_left N rfl) (ZMod l) z)) x = C * (ch ω x * hat ν x)) ∧
    ∀ d : ℤ, IsCoprime d (N * l : ℕ) → ∀ y : ZMod (N * l),
      ν (-(c : ZMod N) * ZMod.castHom (Dvd.intro l rfl) (ZMod N) y) * φ ((a : ZMod l) * ZMod.castHom (Dvd.intro_left N rfl) (ZMod l) y) =
      ch ω d * ch ν⁻¹ d * (ν (-(c : ZMod N) * ZMod.castHom (Dvd.intro l rfl) (ZMod N) (y * d)) *
        φ ((a : ZMod l) * ZMod.castHom (Dvd.intro_left N rfl) (ZMod l) (y * d))) := by
  intro N l ν ω φ a c hN hl hc hφ htw hcu hau
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero l := ⟨hl.ne'⟩
  haveI : NeZero (N * l) := ⟨(Nat.mul_pos hN hl).ne'⟩
  have hlu : IsUnit (l : ZMod N) := (ZMod.unitOfCoprime l hc.symm).isUnit
  have hNu : IsUnit (N : ZMod l) := (ZMod.unitOfCoprime N hc).isUnit
  refine ⟨?_, ?_⟩
  · have haN : IsUnit ((a : ZMod l) * N) := hau.mul hNu
    have hωaN : ω ((a : ZMod l) * N) ≠ 0 := (haN.map ω).ne_zero
    have hνcl : ν (-(c : ZMod N) * l) ≠ 0 := ((hcu.neg.mul hlu).map ν).ne_zero
    refine ⟨ν (-(c : ZMod N) * l) * (ω ((a : ZMod l) * N))⁻¹, mul_ne_zero hνcl (inv_ne_zero hωaN), fun x => ?_⟩
    rw [← hφ x, mul_comm (hat φ x)]
    let f : ZMod N × ZMod l → ZMod (N * l) := fun p => ((p.1.val * l + p.2.val * N : ℕ) : ZMod (N * l))
    have hcN : ∀ k : ℕ, ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N) (k : ZMod (N * l)) = (k : ZMod N) :=
      fun k => map_natCast _ k
    have hcl : ∀ k : ℕ, ZMod.castHom (Dvd.intro_left N rfl : l ∣ N * l) (ZMod l) (k : ZMod (N * l)) = (k : ZMod l) :=
      fun k => map_natCast _ k
    have hinj : Function.Injective f := by
      intro p q hpq
      have h1 := congrArg (ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N)) hpq
      have h2 := congrArg (ZMod.castHom (Dvd.intro_left N rfl : l ∣ N * l) (ZMod l)) hpq
      simp only [f, hcN, hcl] at h1 h2
      push_cast at h1 h2
      simp only [ZMod.natCast_self, mul_zero, add_zero, zero_add, ZMod.natCast_zmod_val] at h1 h2
      exact Prod.ext (hlu.mul_right_cancel h1) (hNu.mul_right_cancel h2)
    have hbij : Function.Bijective f := by
      rw [Fintype.bijective_iff_injective_and_card]
      exact ⟨hinj, by simp [ZMod.card]⟩
    rw [hat_eq_sum_std, hat_eq_sum_std, hat_eq_sum_std, ← Fintype.sum_bijective f hbij _ _ (fun _ => rfl),
      Finset.sum_mul_sum, ← Finset.univ_product_univ, Finset.sum_product, Finset.mul_sum]
    refine Fintype.sum_congr _ _ (fun p => ?_)
    rw [Finset.mul_sum]
    refine Fintype.sum_congr _ _ (fun q => ?_)
    have hN1 : ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N) (f (p, q)) = p * l := by
      simp only [f, hcN]; push_cast; simp [ZMod.natCast_self]
    have hl1 : ZMod.castHom (Dvd.intro_left N rfl : l ∣ N * l) (ZMod l) (f (p, q)) = q * N := by
      simp only [f, hcl]; push_cast; simp [ZMod.natCast_self]
    have htq := htw ((a : ZMod l) * N) q haN
    have hval : ν (-(c : ZMod N) * ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N) (f (p, q))) *
        φ ((a : ZMod l) * ZMod.castHom (Dvd.intro_left N rfl : l ∣ N * l) (ZMod l) (f (p, q)))
        = ν (-(c : ZMod N) * l) * (ω ((a : ZMod l) * N))⁻¹ * (ν p * φ q) := by
      rw [hN1, hl1, htq]
      have e1 : -(c : ZMod N) * (p * l) = (-(c : ZMod N) * l) * p := by ring
      have e2 : (a : ZMod l) * (q * N) = (a : ZMod l) * N * q := by ring
      rw [e1, e2, map_mul]
      field_simp
    have he : (ZMod.stdAddChar (f (p, q) * (x : ZMod (N * l))) : ℂ)
        = ZMod.stdAddChar (p * (x : ZMod N)) * ZMod.stdAddChar (q * (x : ZMod l)) := by
      have : f (p, q) * (x : ZMod (N * l)) = ((((p.val * l + q.val * N : ℕ) : ℤ) * x : ℤ) : ZMod (N * l)) := by
        simp only [f]; push_cast; rfl
      rw [this, ZMod.stdAddChar_coe, stdAddChar_nat_mul_int p x, stdAddChar_nat_mul_int q x, ← Complex.exp_add]
      congr 1
      have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
      have hl' : (l : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne'
      push_cast
      field_simp
    rw [hval, he]
    ring
  · intro d hd y
    have hdN : IsUnit (d : ZMod N) := isUnit_of_isCoprime d (by
      have := hd; push_cast at this; exact this.of_mul_right_left)
    have hdl : IsUnit (d : ZMod l) := isUnit_of_isCoprime d (by
      have := hd; push_cast at this; exact this.of_mul_right_right)
    have h1 : ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N) (y * d)
        = ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N) y * (d : ZMod N) := by
      rw [map_mul, map_intCast]
    have h2 : ZMod.castHom (Dvd.intro_left N rfl : l ∣ N * l) (ZMod l) (y * d)
        = ZMod.castHom (Dvd.intro_left N rfl : l ∣ N * l) (ZMod l) y * (d : ZMod l) := by
      rw [map_mul, map_intCast]
    rw [h1, h2]
    set u := ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N) y
    set v := ZMod.castHom (Dvd.intro_left N rfl : l ∣ N * l) (ZMod l) y
    have hν0 : ν (d : ZMod N) ≠ 0 := (hdN.map ν).ne_zero
    have htv := htw (d : ZMod l) ((a : ZMod l) * v) hdl
    have e1 : -(c : ZMod N) * (u * d) = (-(c : ZMod N) * u) * d := by ring
    have e2 : (a : ZMod l) * (v * d) = (d : ZMod l) * ((a : ZMod l) * v) := by ring
    rw [e1, e2, map_mul ν (-(c : ZMod N) * u) (d : ZMod N)]
    unfold ch
    rw [MulChar.inv_apply_eq_inv', htv]
    field_simp

end GlobalTheory.EisM

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DirichletFourierMixedTwistMultipleStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM Filter Topology
open scoped MatrixGroups Real ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dirichletFourier_mixed_twist_multiple : ∀ (N l : ℕ) (ν : DirichletCharacter ℂ N) (ω : DirichletCharacter ℂ l) (φ : ZMod l → ℂ) (a c : ℤ),
    0 < N → 0 < l → N.Coprime l → (∀ x : ℤ, hat φ x = ch ω x) →
    (∀ d u : ZMod l, IsUnit d → φ u = ω d * φ (d * u)) → IsUnit (c : ZMod N) → IsUnit (a : ZMod l) →
    (∃ C : ℂ, C ≠ 0 ∧ ∀ x : ℤ, hat (fun z : ZMod (N * l) => ν (-(c : ZMod N) * ZMod.castHom (Dvd.intro l rfl) (ZMod N) z) *
        φ ((a : ZMod l) * ZMod.castHom (Dvd.intro_left N rfl) (ZMod l) z)) x = C * (ch ω x * hat ν x)) ∧
    ∀ d : ℤ, IsCoprime d (N * l : ℕ) → ∀ y : ZMod (N * l),
      ν (-(c : ZMod N) * ZMod.castHom (Dvd.intro l rfl) (ZMod N) y) * φ ((a : ZMod l) * ZMod.castHom (Dvd.intro_left N rfl) (ZMod l) y) =
      ch ω d * ch ν⁻¹ d * (ν (-(c : ZMod N) * ZMod.castHom (Dvd.intro l rfl) (ZMod N) (y * d)) *
        φ ((a : ZMod l) * ZMod.castHom (Dvd.intro_left N rfl) (ZMod l) (y * d))) := by
  first | exact @GlobalTheory.EisM.hat_mix_twist | exact GlobalTheory.EisM.hat_mix_twist | (intros; apply GlobalTheory.EisM.hat_mix_twist <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RegularizedEisensteinLatticeSumDilate
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RegularizedEisensteinLatticeSumDilate
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM Filter Topology
open scoped MatrixGroups Real ComplexConjugate

namespace GlobalTheory.EisM

theorem dif_comp_add (L : ℕ) (ι : ℤ × ℤ → ℤ × ℤ) (hι : ∀ x v : ℤ × ℤ, ∀ r : ℤ, ι (x + r • v) = ι x + r • ι v)
    (v : ℤ × ℤ) (F : ℤ × ℤ → ℂ) :
    dif L v (fun y => F (ι y)) = fun x => dif L (ι v) F (ι x) := by
  funext x
  simp only [dif, hι]

theorem lat_dilate : ∀ (j L N : ℕ) (v : ℤ × ℤ) (Φ : ℤ × ℤ → ℂ) (τ τ' : ℍ), 0 < N → (τ' : ℂ) = N * τ →
    lat j 0 L v Φ τ' = lat j 0 L ((N : ℤ) * v.1, v.2) (fun y => if (N : ℤ) ∣ y.1 then Φ (y.1 / N, y.2) else 0) τ := by
  intro j L N v Φ τ τ' hN hτ
  set ι : ℤ × ℤ → ℤ × ℤ := fun x => ((N : ℤ) * x.1, x.2) with hιdef
  have hN' : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  have hinj : Function.Injective ι := by
    intro a b h
    simp only [hιdef, Prod.mk.injEq] at h
    exact Prod.ext (mul_left_cancel₀ hN' h.1) h.2
  have hι : ∀ x v : ℤ × ℤ, ∀ r : ℤ, ι (x + r • v) = ι x + r • ι v := by
    intro x v r
    simp only [hιdef, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.mk_add_mk,
      Prod.smul_mk]
    ext <;> simp only <;> ring
  set T : ℤ × ℤ → ℂ := fun y => trm j 0 ((y.1 : ℂ) * τ + y.2) with hT
  have hG : (fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * (τ' : ℂ) + y.2)) = fun y => T (ι y) := by
    funext y
    simp only [hT, hιdef, hτ]
    congr 1
    push_cast
    ring
  have hvι : ι v = ((N : ℤ) * v.1, v.2) := rfl
  have hdd : ∀ x, dif L v (dif L v fun y => trm j 0 ((y.1 : ℂ) * (τ' : ℂ) + y.2)) x =
      dif L (ι v) (dif L (ι v) T) (ι x) := by
    intro x
    rw [hG, dif_comp_add L ι hι, dif_comp_add L ι hι]
  set Ψ : ℤ × ℤ → ℂ := fun y => if (N : ℤ) ∣ y.1 then Φ (y.1 / N, y.2) else 0 with hΨ
  have hΨι : ∀ x, Ψ (ι x) = Φ x := by
    intro x
    simp only [hΨ, hιdef, dvd_mul_right, if_true, Int.mul_ediv_cancel_left _ hN']
  unfold lat
  rw [← hvι]
  simp_rw [hdd]
  set D := dif L (ι v) (dif L (ι v) T) with hD
  have key : (fun x => Φ x * D (ι x)) = fun x => (fun y => Ψ y * D y) (ι x) := by
    funext x; simp only [hΨι]
  rw [key]
  refine hinj.tsum_eq (f := fun y => Ψ y * D y) ?_
  intro y hy
  simp only [Function.mem_support] at hy
  by_cases h : (N : ℤ) ∣ y.1
  · obtain ⟨c, hc⟩ := h
    exact ⟨(c, y.2), by simp only [hιdef]; exact Prod.ext hc.symm rfl⟩
  · exact absurd (by simp only [hΨ, h, if_false, zero_mul]) hy

end GlobalTheory.EisM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RegularizedEisensteinLatticeSumDilateStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM Filter Topology
open scoped MatrixGroups Real ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularizedEisensteinLatticeSum_dilate : ∀ (j L N : ℕ) (v : ℤ × ℤ) (Φ : ℤ × ℤ → ℂ) (τ τ' : ℍ), 0 < N → (τ' : ℂ) = N * τ →
    lat j 0 L v Φ τ' = lat j 0 L ((N : ℤ) * v.1, v.2) (fun y => if (N : ℤ) ∣ y.1 then Φ (y.1 / N, y.2) else 0) τ := by
  first | exact @GlobalTheory.EisM.lat_dilate | exact GlobalTheory.EisM.lat_dilate | (intros; apply GlobalTheory.EisM.lat_dilate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeFunctionDivisibleFirstSubstitution
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeFunctionDivisibleFirstSubstitution
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM Filter Topology
open scoped MatrixGroups Real ComplexConjugate

namespace GlobalTheory

theorem latF_rows_subst : ∀ (N l : ℕ) (ν : DirichletCharacter ℂ N) (φ : ZMod l → ℂ) (a b c d : ℤ),
    (N : ℤ) * a * d - l * b * c = 1 → 0 < N → 0 < l → ∀ y : ℤ × ℤ,
    (if (N : ℤ) ∣ y.1 then latF l (ch ν) φ (y.1 / N * (N * d) - y.2 * (l * c), -(y.1 / N * b) + y.2 * a) else 0) =
      latF (N * l) (fun _ => 1) (fun z => ν (-(c : ZMod N) * ZMod.castHom (Dvd.intro l rfl) (ZMod N) z) *
        φ ((a : ZMod l) * ZMod.castHom (Dvd.intro_left N rfl) (ZMod l) z)) y := by
  intro N l ν φ a b c d hdet hN hl y
  obtain ⟨y1, y2⟩ := y
  have hNz : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  have hcop : IsCoprime ((N : ℤ) * d) (l : ℤ) := ⟨a, -(b * c), by linear_combination hdet⟩
  simp only [latF]
  by_cases h1 : (N : ℤ) ∣ y1
  · obtain ⟨m, rfl⟩ := h1
    rw [if_pos (dvd_mul_right _ _)]
    have hdiv : (N : ℤ) * m / N = m := Int.mul_ediv_cancel_left m hNz
    simp only [hdiv]
    have key : ((N : ℤ) * l ∣ N * m) ↔ ((l : ℤ) ∣ m) := by
      constructor
      · intro h; exact (mul_dvd_mul_iff_left hNz).mp h
      · intro h; exact mul_dvd_mul_left _ h
    have key2 : ((l : ℤ) ∣ m * (N * d) - y2 * (l * c)) ↔ ((l : ℤ) ∣ m) := by
      constructor
      · intro h
        have h' : (l : ℤ) ∣ m * (N * d) := by
          have := dvd_add h (dvd_mul_of_dvd_right (dvd_mul_right (l:ℤ) c) y2)
          simpa using this
        exact hcop.symm.dvd_of_dvd_mul_right h'
      · intro h
        exact dvd_sub (dvd_mul_of_dvd_left h _) (dvd_mul_of_dvd_right (dvd_mul_right (l:ℤ) c) y2)
    push_cast
    by_cases h2 : (l : ℤ) ∣ m
    · obtain ⟨m2, rfl⟩ := h2
      rw [if_pos ((key2).mpr (dvd_mul_right _ _)), if_pos (key.mpr (dvd_mul_right _ _))]
      have hlz : (l : ℤ) ≠ 0 := by exact_mod_cast hl.ne'
      have e1 : (l : ℤ) * m2 * (N * d) - y2 * (l * c) = l * (m2 * N * d - y2 * c) := by ring
      rw [e1, Int.mul_ediv_cancel_left _ hlz]
      simp only [ch, one_mul, map_intCast]
      congr 2
      · push_cast
        simp [mul_comm]
      · push_cast
        simp [mul_comm]
    · rw [if_neg (fun h => h2 (key2.mp h)), if_neg (fun h => h2 (key.mp h))]
  · rw [if_neg h1, if_neg]
    intro h
    push_cast at h
    exact h1 (dvd_trans (dvd_mul_right _ _) h)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeFunctionDivisibleFirstSubstitutionStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM Filter Topology
open scoped MatrixGroups Real ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeFunctionDivisibleFirst_substitution : ∀ (N l : ℕ) (ν : DirichletCharacter ℂ N) (φ : ZMod l → ℂ) (a b c d : ℤ),
    (N : ℤ) * a * d - l * b * c = 1 → 0 < N → 0 < l → ∀ y : ℤ × ℤ,
    (if (N : ℤ) ∣ y.1 then latF l (ch ν) φ (y.1 / N * (N * d) - y.2 * (l * c), -(y.1 / N * b) + y.2 * a) else 0) =
      latF (N * l) (fun _ => 1) (fun z => ν (-(c : ZMod N) * ZMod.castHom (Dvd.intro l rfl) (ZMod N) z) *
        φ ((a : ZMod l) * ZMod.castHom (Dvd.intro_left N rfl) (ZMod l) z)) y := by
  first | exact @GlobalTheory.latF_rows_subst | exact GlobalTheory.latF_rows_subst | (intros; apply GlobalTheory.latF_rows_subst <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AtkinLehnerEis
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisAL

theorem dif_comm' (L L' : ℕ) (v w : ℤ × ℤ) (F : ℤ × ℤ → ℂ) :
    dif L v (dif L' w F) = dif L' w (dif L v F) := by
  funext x
  simp only [dif]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h : ∑ s ∈ Finset.range L, ∑ r ∈ Finset.range L', F (x + (s : ℤ) • v + (r : ℤ) • w)
      = ∑ r ∈ Finset.range L', ∑ s ∈ Finset.range L, F (x + (r : ℤ) • w + (s : ℤ) • v) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
    rw [add_right_comm]
  rw [h]
  ring

theorem lat_indep2 (j L L' : ℕ) (v w : ℤ × ℤ) (Φ : ℤ × ℤ → ℂ) (τ : ℍ) (hj : 1 ≤ j) (hL : 0 < L) (hL' : 0 < L')
    (hΦ : ∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C) (hv : Kills L v Φ) (hw : Kills L' w Φ) :
    lat j 0 L v Φ τ = lat j 0 L' w Φ τ := by
  set T : ℤ × ℤ → ℂ := fun y => trm j 0 ((y.1 : ℂ) * τ + y.2) with hT
  have hsv := GlobalTheory.LatSumZ.latsum_summable j L v τ hj hL
  have hsw := GlobalTheory.LatSumZ.latsum_summable j L' w τ hj hL'
  simp only [lat]
  calc ∑' x, Φ x * dif L v (dif L v T) x
      = ∑' x, Φ x * dif L' w (dif L' w (dif L v (dif L v T))) x :=
        (sum_dif_dif L' w Φ _ hL' hΦ hw hsv).symm
    _ = ∑' x, Φ x * dif L v (dif L v (dif L' w (dif L' w T))) x := by
        have c1 : ∀ F : ℤ × ℤ → ℂ, dif L' w (dif L v (dif L v F)) = dif L v (dif L v (dif L' w F)) := by
          intro F; rw [dif_comm' L' L w v (dif L v F), dif_comm' L' L w v F]
        rw [c1 T, c1 (dif L' w T)]
    _ = ∑' x, Φ x * dif L' w (dif L' w T) x := sum_dif_dif L v Φ _ hL hΦ hv hsw

theorem inv_eq_zero_of_parity (k L : ℕ) (χ : ℤ → ℂ) (f : ℍ → ℂ) (h : Inv k L χ f)
    (hp : χ (-1) * (-1) ^ k ≠ 1) : f = 0 := by
  funext τ
  have h1 := h (-1) (by simp) τ
  have e : ((-1 : SL(2, ℤ)) • τ) = τ := by
    rw [ModularGroup.SL_neg_smul, one_smul]
  rw [e] at h1
  simp at h1
  have : (1 - χ (-1) * (-1) ^ k) * f τ = 0 := by linear_combination h1
  rcases mul_eq_zero.mp this with h2 | h2
  · exact absurd (by linear_combination -h2) hp
  · simpa using h2

theorem qs_eq_of_MF (k L : ℕ) (χ : ℤ → ℂ) (a a' : ℕ → ℂ) (hk : 1 ≤ k) (hL : 0 < L)
    (ha : MF k L χ a) (ha' : MF k L χ a') (h : ∀ n, n ≠ 0 → a n = a' n) : qs a = qs a' := by
  set K := a 0 - a' 0 with hK
  have hd : ∀ τ, qs a τ = qs a' τ + K := by
    intro τ
    have s := GlobalTheory.EisM.CharTwist.summable_of_polyB ha.1 τ
    have s' := GlobalTheory.EisM.CharTwist.summable_of_polyB ha'.1 τ
    unfold qs
    rw [s.tsum_eq_zero_add, s'.tsum_eq_zero_add]
    have : ∀ n : ℕ, a (n + 1) = a' (n + 1) := fun n => h _ (Nat.succ_ne_zero n)
    simp only [this, hK]
    simp
    ring
  suffices hK0 : K = 0 by funext τ; rw [hd, hK0, add_zero]
  let γ : SL(2, ℤ) := ⟨!![1, 0; (L : ℤ), 1], by simp [Matrix.det_fin_two]⟩
  let τ0 : ℍ := ⟨2 * Complex.I, by simp⟩
  have i1 := ha.2 γ (by simp [γ]) τ0
  have i2 := ha'.2 γ (by simp [γ]) τ0
  have j1 := ha.2 1 (by simp) τ0
  have j2 := ha'.2 1 (by simp) τ0
  simp only [one_smul] at j1 j2
  rw [hd, hd] at i1
  simp [γ] at i1 i2 j1 j2
  set w : ℂ := ((L : ℂ) * τ0 + 1) ^ k with hw
  have hw1 : w ≠ 1 := by
    intro hw1
    have hn : ‖((L : ℂ) * τ0 + 1)‖ ≥ 2 := by
      have := Complex.abs_im_le_norm ((L : ℂ) * τ0 + 1)
      have him : ((L : ℂ) * τ0 + 1).im = 2 * L := by simp [τ0]; ring
      rw [him] at this
      have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
      rw [abs_of_nonneg (by positivity)] at this
      linarith
    have : ‖w‖ = 1 := by rw [hw1]; simp
    rw [hw, norm_pow] at this
    have h2 : (2 : ℝ) ^ k ≤ ‖((L : ℂ) * τ0 + 1)‖ ^ k := pow_le_pow_left₀ (by norm_num) hn k
    have h3 : (1 : ℝ) < 2 ^ k := one_lt_pow₀ (by norm_num) (by omega)
    linarith
  rw [hd] at j1
  have hK1 : K = χ 1 * K := by linear_combination j1 - j2
  have hK2 : K = χ 1 * w * K := by linear_combination i1 - i2
  have h0 : (w - 1) * K = 0 := by linear_combination w * hK1 - hK2
  exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hw1)

end GlobalTheory.EisAL

namespace GlobalTheory.EisAL

theorem slz_diag (j N : ℕ) (g : ℍ → ℂ) (τ : ℍ) (hτ' : 0 < ((N : ℂ) * τ).im) :
    slz j !![(N : ℤ), 0; 0, 1] g τ = (N : ℂ) ^ (j - 1) * g ⟨(N : ℂ) * τ, hτ'⟩ := by
  unfold slz
  simp [Matrix.det_fin_two]
  left
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hτ']
end GlobalTheory.EisAL

namespace GlobalTheory.EisAL

theorem MF_smul (k L : ℕ) (χ : ℤ → ℂ) (a : ℕ → ℂ) (r : ℂ) (h : MF k L χ a) : MF k L χ (r • a) := by
  obtain ⟨⟨C, A, hC⟩, hI⟩ := h
  have hq : qs (r • a) = fun τ => r * qs a τ := by
    funext τ; unfold qs; rw [← tsum_mul_left]; congr 1; funext n; simp only [Pi.smul_apply, smul_eq_mul]; ring
  refine ⟨⟨‖r‖ * C, A, fun n => ?_⟩, ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC n) (norm_nonneg r)
  · intro γ hγ τ
    rw [hq]; simp only
    rw [hI γ hγ τ]; ring

theorem qs_smul (a : ℕ → ℂ) (r : ℂ) (τ : ℍ) : qs (r • a) τ = r * qs a τ := by
  unfold qs; rw [← tsum_mul_left]; congr 1; funext n; simp only [Pi.smul_apply, smul_eq_mul]; ring

theorem atkin_lehner_eis : ∀ (j N l : ℕ) (ω : DirichletCharacter ℂ l) (ν : DirichletCharacter ℂ N) (c₁ c₂ : ℂ) (a₀ b₀ c₀ d₀ : ℤ), N * a₀ * d₀ - l * b₀ * c₀ = 1 → 1 ≤ j → 0 < N → l.Prime → ¬ l ∣ N → MF j (N * l) (fun d => ch ω d * ch ν d) (eis j c₁ (ch ω) (ch ν)) → MF j (N * l) (fun d => ch ω d * ch ν⁻¹ d) (eis j c₂ (fun x => ch ω x * hat ν x) fun _ => 1) → ∃ κ : ℂ, κ ≠ 0 ∧ slz j !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs (eis j c₁ (ch ω) (ch ν))) = κ • qs (eis j c₂ (fun x => ch ω x * hat ν x) fun _ => 1) := by
  intro j N l ω ν c₁ c₂ a b c d hdet hj hN hl hlN h1 h2
  haveI : Fact l.Prime := ⟨hl⟩
  have hl0 : 0 < l := hl.pos
  haveI : NeZero l := ⟨hl.ne_zero⟩
  haveI : NeZero N := ⟨hN.ne'⟩
  have hNl : 0 < N * l := Nat.mul_pos hN hl0
  set E₁ := eis j c₁ (ch ω) (ch ν) with hE₁
  set E₂ := eis j c₂ (fun x => ch ω x * hat ν x) (fun _ => 1) with hE₂
  have hν1 : ch ν⁻¹ (-1) = ch ν (-1) := by
    unfold ch
    have e : ν ((-1 : ℤ) : ZMod N) * ν ((-1 : ℤ) : ZMod N) = 1 := by rw [← map_mul]; simp
    rw [MulChar.inv_apply_eq_inv']
    exact inv_eq_of_mul_eq_one_right e
  have hs : ((-1 : ℂ) ^ j) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  by_cases hpar : ch ω (-1) * ch ν (-1) = (-1) ^ j
  swap
  · have z1 : qs E₁ = 0 := inv_eq_zero_of_parity j (N * l) _ _ h1.2 (by
      intro h; apply hpar; linear_combination (-1 : ℂ) ^ j * h - (ch ω (-1) * ch ν (-1)) * hs)
    have z2 : qs E₂ = 0 := inv_eq_zero_of_parity j (N * l) _ _ h2.2 (by
      intro h; apply hpar; rw [hν1] at h; linear_combination (-1 : ℂ) ^ j * h - (ch ω (-1) * ch ν (-1)) * hs)
    refine ⟨1, one_ne_zero, ?_⟩
    rw [z1, z2]; funext τ; simp [slz]

  obtain ⟨φ, hφsum, hφtw⟩ := GlobalTheory.EisM.CharTwist.exists_coeffs ω
  have hhat : ∀ x : ℤ, hat φ x = ch ω x := fun x => by rw [hat_eq_sum_std]; exact hφsum _
  have hω0 : ch ω 0 = 0 := by simp only [ch, Int.cast_zero]; exact MulChar.map_zero ω

  obtain ⟨c', hMF', hlat'⟩ := GlobalTheory.EisForm.eis_latF_mf j l N (ch ν) (ch ω) (ch ν) φ hj hl0 hN
    (by rw [hhat, hω0]) (fun x => by simp [ch])
    (fun d hd => by
      have hd' : IsCoprime d (l : ℤ) := by push_cast at hd; exact hd.of_mul_right_left
      have hu : IsUnit (d : ZMod l) := isUnit_of_isCoprime d hd'
      refine ⟨fun y => ?_, fun x => by simp [ch, mul_comm]⟩
      rw [hφtw (d : ZMod l) y hu, mul_comm y]; rfl) hpar
  have hfun : hat φ = ch ω := funext hhat
  rw [hfun] at hMF' hlat'
  rw [mul_comm l N] at hMF'
  have hq1 : qs E₁ = qs (eis j c' (ch ω) (ch ν)) :=
    qs_eq_of_MF j (N * l) _ _ _ hj hNl h1 hMF' (fun n hn => by simp [hE₁, eis, hn])

  have hcop : N.Coprime l := ((Nat.Prime.coprime_iff_not_dvd hl).mpr hlN).symm
  have hcu : IsUnit (c : ZMod N) := isUnit_of_isCoprime c ⟨-(l * b), a * d, by linear_combination hdet⟩
  have hau : IsUnit (a : ZMod l) := isUnit_of_isCoprime a ⟨N * d, -(b * c), by linear_combination hdet⟩
  set φ₂ : ZMod (N * l) → ℂ := fun z => ν (-(c : ZMod N) * ZMod.castHom (Dvd.intro l rfl) (ZMod N) z) *
        φ ((a : ZMod l) * ZMod.castHom (Dvd.intro_left N rfl) (ZMod l) z) with hφ₂
  obtain ⟨⟨C, hC0, hChat0⟩, hφ₂tw0⟩ := GlobalTheory.T.dirichletFourier_mixed_twist_multiple N l ν ω φ a c hN hl0 hcop hhat hφtw hcu hau
  have hChat : ∀ x : ℤ, hat φ₂ x = C * (ch ω x * hat ν x) := hChat0
  have hφ₂tw : ∀ d : ℤ, IsCoprime d (N * l : ℕ) → ∀ y, φ₂ y = ch ω d * ch ν⁻¹ d * φ₂ (y * d) := hφ₂tw0
  have hhat0₂ : hat φ₂ 0 = 0 := by rw [hChat, hω0]; ring
  obtain ⟨c'', hMF'', hlat''⟩ := GlobalTheory.EisForm.eis_latF_mf j (N * l) 1 (fun _ => 1) (fun d => ch ω d * ch ν⁻¹ d)
    (fun _ => 1) φ₂ hj hNl one_pos hhat0₂ (fun _ => rfl)
    (fun d hd => ⟨fun y => hφ₂tw d (by rwa [mul_one] at hd) y, fun x => by simp⟩)
    (by rw [mul_one, hν1]; exact hpar)
  simp only [mul_one] at hMF''
  have hq2 : qs (C⁻¹ • eis j c'' (hat φ₂) fun _ => 1) = qs E₂ :=
    qs_eq_of_MF j (N * l) _ _ _ hj hNl (MF_smul _ _ _ _ _ hMF'') h2 (fun n hn => by
      simp only [hE₂, eis, Pi.smul_apply, smul_eq_mul, if_neg hn, hChat, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      field_simp)

  set Φ₁ := latF l (ch ν) φ with hΦ₁
  set Ψ := latF (N * l) (fun _ => 1) φ₂ with hΨ
  set K₁ : ℂ := 2 * (-2 * π * Complex.I / l) ^ j / (j - 1).factorial with hK₁
  set K₂ : ℂ := 2 * (-2 * π * Complex.I / ((N * l : ℕ) : ℂ)) ^ j / (j - 1).factorial with hK₂
  have hK₁0 : K₁ ≠ 0 := by
    have : (l : ℂ) ≠ 0 := by exact_mod_cast hl0.ne'
    simp [hK₁, Real.pi_ne_zero, Complex.I_ne_zero, this, Nat.factorial_ne_zero]
  have hK₂0 : K₂ ≠ 0 := by
    have h1 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have h2 : (l : ℂ) ≠ 0 := by exact_mod_cast hl0.ne'
    simp [hK₂, Real.pi_ne_zero, Complex.I_ne_zero, h1, h2, Nat.factorial_ne_zero]
  have hE₁lat : ∀ τ, qs E₁ τ = K₁⁻¹ * lat j 0 l (0, 1) Φ₁ τ := fun τ => by
    rw [hlat' τ, hq1, ← mul_assoc, inv_mul_cancel₀ hK₁0, one_mul]
  have hE₂lat : ∀ τ, lat j 0 (N * l) (0, 1) Ψ τ = K₂ * C * qs E₂ τ := fun τ => by
    have e := hlat'' τ
    have e2 : qs (eis j c'' (hat φ₂) fun _ => 1) τ = C * qs E₂ τ := by
      rw [← hq2, qs_smul, ← mul_assoc, mul_inv_cancel₀ hC0, one_mul]
    rw [e, e2]; push_cast; ring
  let γ₀ : SL(2, ℤ) := ⟨!![a, b; l * c, N * d], by simp [Matrix.det_fin_two]; linear_combination hdet⟩
  have hδ : !![(N : ℤ) * a, b; N * l * c, N * d] = (γ₀ : M2) * !![(N : ℤ), 0; 0, 1] := by
    ext i k; fin_cases i <;> fin_cases k <;> simp [γ₀] <;> ring
  have hdet0 : 0 < (γ₀ : M2).det := by rw [γ₀.2]; exact one_pos
  have hdet1 : 0 < (!![(N : ℤ), 0; 0, 1] : M2).det := by simp [Matrix.det_fin_two]; exact_mod_cast hN
  obtain ⟨hcomp, hSL, -⟩ := GlobalTheory.EisM.slz_props j (qs E₁) hj
  refine ⟨(N : ℂ) ^ (j - 1) * K₁⁻¹ * (K₂ * C), by
    have : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ this) (inv_ne_zero hK₁0)) (mul_ne_zero hK₂0 hC0), ?_⟩
  rw [hδ, hcomp _ _ hdet0 hdet1]
  funext τ
  have hτ' : 0 < ((N : ℂ) * τ).im := by simp; exact mul_pos (by exact_mod_cast hN) τ.2
  set τ' : ℍ := ⟨(N : ℂ) * τ, hτ'⟩ with hτ'def
  have hout : slz j !![(N : ℤ), 0; 0, 1] (slz j (γ₀ : M2) (qs E₁)) τ = (N : ℂ) ^ (j - 1) * slz j (γ₀ : M2) (qs E₁) τ' := by
    exact slz_diag j N _ τ hτ'
  rw [hout, hSL γ₀ τ', hE₁lat]
  set Φ₁' : ℤ × ℤ → ℂ := fun y => Φ₁ (y.1 * (N * d) - y.2 * (l * c), -(y.1 * b) + y.2 * a) with hΦ₁'
  have htr : ∀ x : ℤ × ℤ, Φ₁' (x.1 * γ₀ 0 0 + x.2 * γ₀ 1 0, x.1 * γ₀ 0 1 + x.2 * γ₀ 1 1) = Φ₁ x := by
    intro x
    simp only [hΦ₁', γ₀]
    simp
    congr 1
    ext
    · simp only; linear_combination x.1 * hdet
    · simp only; linear_combination x.2 * hdet
  rw [GlobalTheory.EisM.lat_smul j l (0, 1) Φ₁ Φ₁' γ₀ τ' htr]
  have hv : ((0 : ℤ) * γ₀ 0 0 + 1 * γ₀ 1 0, (0 : ℤ) * γ₀ 0 1 + 1 * γ₀ 1 1) = ((l : ℤ) * c, (N : ℤ) * d) := by
    simp [γ₀]
  simp only [Prod.fst, Prod.snd] at hv ⊢
  rw [hv, GlobalTheory.T.regularizedEisensteinLatticeSum_dilate j l N _ Φ₁' τ τ' hN rfl]
  have hrow : (fun y : ℤ × ℤ => if (N : ℤ) ∣ y.1 then Φ₁' (y.1 / N, y.2) else 0) = Ψ := by
    funext y; exact GlobalTheory.T.latticeFunctionDivisibleFirst_substitution N l ν φ a b c d hdet hN hl0 y
  rw [hrow]
  have hΨb : ∃ C : ℝ, ∀ x, ‖Ψ x‖ ≤ C := by
    refine ⟨∑ z, ‖φ₂ z‖, fun x => ?_⟩
    simp only [hΨ, latF]
    split_ifs
    · rw [one_mul]
      exact Finset.single_le_sum (f := fun z => ‖φ₂ z‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ _)
    · simpa using Finset.sum_nonneg fun z (_ : z ∈ Finset.univ) => norm_nonneg (φ₂ z)
  have hKl : Kills (N * l) (0, 1) Ψ := by
    simpa using GlobalTheory.EisForm.latF_kills (N * l) 1 hNl (fun _ => 1) φ₂ (fun _ => rfl) hhat0₂ 0 1 (by simp)
  have hKv : Kills l ((N : ℤ) * ((l : ℤ) * c), (N : ℤ) * d) Ψ := by
    have hsum0 : ∑ y, φ y = 0 := by rw [← GlobalTheory.EisForm.hat_zero, hhat, hω0]
    have hdl : (N : ZMod l) * (a : ZMod l) * (d : ZMod l) = 1 := by
      have := congrArg (fun z : ℤ => (z : ZMod l)) hdet
      push_cast at this; rw [ZMod.natCast_self] at this; linear_combination this
    intro x
    by_cases h : ((N * l : ℕ) : ℤ) ∣ x.1
    · calc ∑ r ∈ Finset.range l, Ψ (x - (r : ℤ) • ((N : ℤ) * ((l : ℤ) * c), (N : ℤ) * d))
          = ∑ r ∈ Finset.range l, ν (-(c : ZMod N) * (x.2 : ZMod N)) *
              φ ((a : ZMod l) * (x.2 : ZMod l) + (r : ZMod l) * (-1)) := by
            refine Finset.sum_congr rfl fun r _ => ?_
            simp only [hΨ, latF, Prod.fst_sub, Prod.snd_sub, Prod.smul_mk, smul_eq_mul]
            rw [if_pos (by obtain ⟨m, hm⟩ := h; exact ⟨m - r * c, by push_cast at hm ⊢; rw [hm]; ring⟩)]
            simp only [hφ₂, one_mul, map_intCast]
            congr 2
            · push_cast; rw [ZMod.natCast_self]; ring
            · push_cast; linear_combination (-(r : ZMod l)) * hdl
        _ = 0 := by rw [← Finset.mul_sum, GlobalTheory.EisForm.sum_shift l φ _ _ isUnit_one.neg, hsum0, mul_zero]
    · refine Finset.sum_eq_zero fun r _ => ?_
      simp only [hΨ, latF, Prod.fst_sub, Prod.snd_sub, Prod.smul_mk, smul_eq_mul]
      rw [if_neg]
      intro h2; apply h
      have h3 : ((N * l : ℕ) : ℤ) ∣ (r : ℤ) * ((N : ℤ) * ((l : ℤ) * c)) := ⟨r * c, by push_cast; ring⟩
      simpa using dvd_add h2 h3
  rw [lat_indep2 j l (N * l) _ (0, 1) Ψ τ hj hl0 hNl hΨb hKv hKl, hE₂lat]
  have hD : (((γ₀ 1 0 : ℤ) : ℂ) * τ' + ((γ₀ 1 1 : ℤ) : ℂ)) ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero γ₀ τ'
    simpa [UpperHalfPlane.denom] using this
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp

end GlobalTheory.EisAL
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AtkinLehnerEisStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_slz_qs_eis_eq_smul : ∀ (j N l : ℕ) (ω : DirichletCharacter ℂ l) (ν : DirichletCharacter ℂ N) (c₁ c₂ : ℂ) (a₀ b₀ c₀ d₀ : ℤ), N * a₀ * d₀ - l * b₀ * c₀ = 1 → 1 ≤ j → 0 < N → l.Prime → ¬ l ∣ N → MF j (N * l) (fun d => ch ω d * ch ν d) (eis j c₁ (ch ω) (ch ν)) → MF j (N * l) (fun d => ch ω d * ch ν⁻¹ d) (eis j c₂ (fun x => ch ω x * hat ν x) fun _ => 1) → ∃ κ : ℂ, κ ≠ 0 ∧ slz j !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs (eis j c₁ (ch ω) (ch ν))) = κ • qs (eis j c₂ (fun x => ch ω x * hat ν x) fun _ => 1) := by
  first | exact @GlobalTheory.EisAL.atkin_lehner_eis | exact GlobalTheory.EisAL.atkin_lehner_eis | (intros; apply GlobalTheory.EisAL.atkin_lehner_eis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MuModelProductValueNeZeroOfDepleted
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.ZMVal

lemma ch_per {M : ℕ} (φ : DirichletCharacter ℂ M) (m : ℕ) (hm : M ∣ m) (d : ℤ) : ch φ (d + (m : ℤ)) = ch φ d := by
  obtain ⟨r, rfl⟩ := hm
  simp [ch]

lemma ch_mul' {M : ℕ} (φ : DirichletCharacter ℂ M) (x y : ℤ) : ch φ (x * y) = ch φ x * ch φ y := by
  simp [ch]

lemma ch_zero_of_dvd {l : ℕ} (φ : DirichletCharacter ℂ l) (hl : l.Prime) (x : ℤ) (hx : (l : ℤ) ∣ x) : ch φ x = 0 := by
  haveI : Fact l.Prime := ⟨hl⟩
  have : ((x : ZMod l)) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd x l).2 hx
  simp only [ch]; rw [this]; exact MulChar.map_zero φ

lemma isUnit_of_coprime {M : ℕ} (d : ℤ) (h : IsCoprime d M) : IsUnit (d : ZMod M) := by
  obtain ⟨u, v, huv⟩ := h
  refine isUnit_iff_exists_inv.2 ⟨(u : ZMod M), ?_⟩
  have := congrArg (fun z : ℤ => (z : ZMod M)) huv
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero, add_zero, Int.cast_one] at this
  rw [mul_comm]; exact this

lemma ch_mul_inv {M : ℕ} (φ : DirichletCharacter ℂ M) (d : ℤ) (h : IsCoprime d M) : ch φ d * ch φ⁻¹ d = 1 := by
  have hu := isUnit_of_coprime d h
  simp only [ch]
  rw [← MulChar.mul_apply, mul_inv_cancel, ← hu.unit_spec]
  exact MulChar.one_apply_coe _

lemma ch_ne_zero {M : ℕ} (φ : DirichletCharacter ℂ M) (d : ℤ) (h : IsCoprime d M) : ch φ d ≠ 0 :=
  left_ne_zero_of_mul_eq_one (ch_mul_inv φ d h)

lemma sq_neg_one {M : ℕ} (φ : DirichletCharacter ℂ M) : φ (-1) * φ (-1) = 1 := by
  rw [← map_mul]; simp

lemma dc_inv_neg_one {M : ℕ} (φ : DirichletCharacter ℂ M) : φ⁻¹ (-1) = φ (-1) := by
  rw [MulChar.inv_apply_eq_inv']
  have h := sq_neg_one φ
  exact inv_eq_of_mul_eq_one_right h

lemma coprime_left {a b : ℕ} (d : ℤ) (h : IsCoprime d ((a * b : ℕ) : ℤ)) : IsCoprime d (a : ℤ) := by
  push_cast at h; exact h.of_mul_right_left

lemma coprime_right {a b : ℕ} (d : ℤ) (h : IsCoprime d ((a * b : ℕ) : ℤ)) : IsCoprime d (b : ℤ) := by
  push_cast at h; exact h.of_mul_right_right

lemma chi_neg_one {k N : ℕ} (hk : Odd k) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ) (h : Prim k N χ⁻¹ g) :
    χ (-1) = -1 := by
  have hsq := sq_neg_one χ
  by_contra hne
  have h1 : χ (-1) = 1 := by
    have : (χ (-1) - 1) * (χ (-1) + 1) = 0 := by linear_combination hsq
    rcases mul_eq_zero.1 this with h | h
    · linear_combination h
    · exact absurd (by linear_combination h) hne
  have hinv : χ⁻¹ (-1) = 1 := by rw [dc_inv_neg_one, h1]
  have hq : ∀ τ : ℍ, qs g τ = 0 := by
    intro τ
    have := h.cf.1.2 (-1) (by simp) τ
    have hs : ((-1 : SL(2, ℤ)) • τ) = τ := by
      rw [show (-1 : SL(2, ℤ)) = -(1 : SL(2, ℤ)) from rfl, ModularGroup.SL_neg_smul, one_smul]
    rw [hs] at this
    simp [ch, hinv, hk.neg_one_pow] at this
    linear_combination this / 2
  have hpb0 : PolyB (0 : ℕ → ℂ) := ⟨0, 0, by simp⟩
  have : g = 0 := GlobalTheory.EisM.qs_injective g 0 h.cf.1.1 hpb0 (by funext τ; rw [hq τ]; simp [qs])
  have := h.one
  simp_all

lemma slz_smul' (j : ℕ) (δ : M2) (c : ℂ) (f : ℍ → ℂ) : slz j δ (c • f) = c • slz j δ f := by
  funext τ; simp only [slz, Pi.smul_apply, smul_eq_mul]; ring

lemma slz_mul' (j j' : ℕ) (hj : 1 ≤ j) (hj' : 1 ≤ j') (δ : M2) (f g : ℍ → ℂ) :
    slz (j + j') δ (fun τ => f τ * g τ) = fun τ => ((δ.det : ℤ) : ℂ) * (slz j δ f τ * slz j' δ g τ) := by
  funext τ
  obtain ⟨a, rfl⟩ : ∃ a, j = a + 1 := ⟨j - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, j' = b + 1 := ⟨j' - 1, by omega⟩
  simp only [slz]
  rw [show a + 1 + (b + 1) - 1 = a + b + 1 by omega, show a + 1 - 1 = a by omega, show b + 1 - 1 = b by omega]
  have hx : ∀ x : ℂ, (x ^ (a + 1 + (b + 1)))⁻¹ = (x ^ (a + 1))⁻¹ * (x ^ (b + 1))⁻¹ := fun x => by rw [pow_add, mul_inv]
  rw [hx]; ring

lemma lam_sub_smul (B : ℕ) (c a b : ℕ → ℂ) (t : ℂ) : lam B c (a - t • b) = lam B c a - t * lam B c b := by
  simp only [lam, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1; refine Finset.sum_congr rfl fun n _ => by ring

lemma lam_smul (B : ℕ) (c a : ℕ → ℂ) (t : ℂ) : lam B c (t • a) = t * lam B c a := by
  simp only [lam, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => by ring

lemma mul_smul_smul (a b : ℕ → ℂ) (s t : ℂ) : mul (s • a) (t • b) = (s * t) • mul a b := by
  funext n; simp only [mul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => by ring

end GlobalTheory.ZMVal

namespace GlobalTheory.ZMVal

lemma U_eis_eq {j L l : ℕ} (ε : ℤ → ℂ) (c t : ℂ) (a b : ℤ → ℂ) (hj : 1 ≤ j) (hL : 0 < L) (hl : l.Prime)
    (hlL : l ∣ L) (hper : ∀ d, ε (d + L) = ε d) (hMF : MF j L ε (eis j c a b))
    (ha : ∀ x : ℤ, (l : ℤ) ∣ x → a x = 0) (hb : ∀ y, b (l * y) = t * b y) :
    Uo l (eis j c a b) = t • eis j c a b := by
  have h1 := (GlobalTheory.T.isModularFormCoeffSeq_heckeU_and_depletion j L l ε _ hj hl hlL hper hMF).1
  have h2 := ((GlobalTheory.EisM.mf_linear j L ε).2.2.1 t _ hMF).1
  refine GlobalTheory.EisM.eq_of_coeff_pos_eq j L ε _ _ hj hL h1 h2 (fun n hn => ?_)
  simp only [Uo, Pi.smul_apply, smul_eq_mul]
  exact (GlobalTheory.eis_U_V j l c t a b hl).1 ha hb n hn

lemma slashIntMatrixPosDet_atkinLehner_twice (j N l : ℕ) (a₀ b₀ c₀ d₀ : ℤ) (hdet : N * a₀ * d₀ - l * b₀ * c₀ = 1) (hj : 1 ≤ j) (hN : 0 < N)
    (ε : ℤ → ℂ) (f : ℍ → ℂ) (hf : Inv j (N * l) ε f) :
    ∃ d : ℤ, IsCoprime d ((N * l : ℕ) : ℤ) ∧
      slz j !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (slz j !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] f) =
        ((N : ℂ) ^ j / (N : ℂ) ^ 2 * ε d) • f := by
  set W : M2 := !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] with hW
  set γm : M2 := !![(N : ℤ) * a₀ ^ 2 + l * b₀ * c₀, (a₀ + d₀) * b₀; N * l * c₀ * (a₀ + d₀), l * b₀ * c₀ + N * d₀ ^ 2]
    with hγm
  have hγdet : γm.det = 1 := by
    rw [hγm, Matrix.det_fin_two_of]; linear_combination ((N : ℤ) * a₀ * d₀ - l * b₀ * c₀ + 1) * hdet
  let γ : SL(2, ℤ) := ⟨γm, hγdet⟩
  set D : M2 := !![(N : ℤ), 0; 0, (N : ℤ)] with hD
  have hWW : W * W = D * γm := by
    rw [hW, hD, hγm]
    ext i k; fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have hWdet : 0 < W.det := by
    have : W.det = N := by rw [hW, Matrix.det_fin_two_of]; linear_combination (N : ℤ) * hdet
    rw [this]; exact_mod_cast hN
  have hDdet : 0 < D.det := by rw [hD, Matrix.det_fin_two_of]; simp; positivity
  have hprops := GlobalTheory.EisM.slz_props j f hj
  refine ⟨l * b₀ * c₀ + N * d₀ ^ 2, ⟨(N : ℤ) * a₀ ^ 2 + l * b₀ * c₀, -((a₀ + d₀) * b₀ * c₀ * (a₀ + d₀)), ?_⟩, ?_⟩
  · push_cast; linear_combination ((N : ℤ) * a₀ * d₀ - l * b₀ * c₀ + 1) * hdet
  rw [← hprops.1 W W hWdet hWdet, hWW, hprops.1 D γm hDdet (by rw [hγdet]; norm_num)]
  have hDf : slz j D f = ((N : ℂ) ^ j / (N : ℂ) ^ 2) • f := by
    funext τ; rw [hD, hprops.2.2.2.2 N τ hN]; rfl
  rw [hDf, slz_smul']
  have hγ : slz j (γ : M2) f = fun τ => ε (γ 1 1) * f τ :=
    ((hprops.2.2.1 (N * l) ε).1 hf) γ (by
      show ((N * l : ℕ) : ℤ) ∣ γm 1 0
      rw [hγm]; simp; exact ⟨c₀ * (a₀ + d₀), by ring⟩)
  have hγ' : slz j γm f = fun τ => ε (l * b₀ * c₀ + N * d₀ ^ 2) * f τ := by
    rw [show γm = (γ : M2) from rfl, hγ]; rfl
  rw [hγ']
  funext τ; simp only [Pi.smul_apply, smul_eq_mul]; ring

end GlobalTheory.ZMVal

namespace GlobalTheory.ZMVal

lemma coprime_of_dvd {d : ℤ} {m M : ℕ} (h : IsCoprime d ((M : ℕ) : ℤ)) (hm : m ∣ M) : IsCoprime d (m : ℤ) :=
  h.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.2 hm)

end GlobalTheory.ZMVal


open GlobalTheory.ZMVal in
theorem _root_.GlobalTheory.zm_val_ne_zero : ∀ (e N l : ℕ) (χ θ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l) (g : ℕ → ℂ) (α β : ℂ) (a₀ b₀ c₀ d₀ : ℤ), N * a₀ * d₀ - l * b₀ * c₀ = 1 → 1 ≤ e → 0 < N → l.Prime → ¬ l ∣ N → Prim (2 * e + 1) N χ⁻¹ (fun n => conj (g n)) → α + β = χ l * conj (g l) → α * β = χ l * (l : ℂ) ^ (2 * e) → α ≠ 0 → θ (-1) = (-1) ^ e * ψ (-1) → θ * χ⁻¹ ≠ 1 → ∀ (B : ℕ) (c : ℕ → ℂ), EigF (2 * e + 1) N l χ (fun q => χ q * conj (g q)) α B c → val B c l α 1 (Zs (2 * e + 1) l (ch θ) (hat ⇑(θ * χ⁻¹)) (fun x y => ψ x * ψ⁻¹ y * ((y : ℂ) / x) ^ e)) ≠ 0 → ∀ (B' : ℕ) (c' : ℕ → ℂ), (∀ a a', MF (2 * e + 1) (N * l) (ch χ⁻¹) a → MF (2 * e + 1) (N * l) (ch χ) a' → qs a' = slz (2 * e + 1) !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs a) → lam B' c' a = lam B c a') → (∀ a, MF (2 * e + 1) (N * l) (ch χ⁻¹) a → lam B' c' (Uo l a) = χ⁻¹ l * α * lam B' c' a) → val B' c' l (χ⁻¹ l * α) 1 (Zm (2 * e + 1) l (hat θ) (ch (θ * χ⁻¹)) (fun A d => ψ A * ψ⁻¹ d * ((d : ℂ) / A) ^ e)) ≠ 0 := by
  intro e N l χ θ ψ g α β a₀ b₀ c₀ d₀ hdet he hN hl hlN hprim hsum hprod hα0 hpar hθχ B c hEig hval B' c' hAL hU'
  haveI : Fact l.Prime := ⟨hl⟩
  have hl0 : 0 < l := hl.pos
  have hNl : 0 < N * l := Nat.mul_pos hN hl0
  have hlNl : l ∣ N * l := dvd_mul_left l N
  have hNNl : N ∣ N * l := dvd_mul_right N l
  have hχm : χ (-1) = -1 := chi_neg_one (k := 2 * e + 1) ⟨e, rfl⟩ χ _ hprim
  have hψsq := sq_neg_one ψ
  set θ' := θ * χ⁻¹ with hθ'
  have chm : ∀ {M : ℕ} (φ : DirichletCharacter ℂ M), ch φ (-1) = φ (-1) := fun φ => by simp [ch]
  have hper : ∀ {M : ℕ} (φ : DirichletCharacter ℂ M), M ∣ N * l → ∀ d : ℤ, ch φ (d + ((N * l : ℕ) : ℤ)) = ch φ d :=
    fun φ h d => ch_per φ _ h d
  have hatch := (GlobalTheory.EisM.hat_char_props).1
  have hatper : ∀ (φ : DirichletCharacter ℂ N) (x : ℤ), hat φ (x + ((N * l : ℕ) : ℤ)) = hat φ x := by
    intro φ x
    have hp : Function.Periodic (hat φ) (N : ℤ) := fun x => (hatch N φ hN).1 x
    have := hp.nat_mul l x
    rw [show ((N * l : ℕ) : ℤ) = (l : ℤ) * (N : ℤ) by push_cast; ring]
    simpa using this
  have hθ'inv : ∀ d, ch θ'⁻¹ d = ch θ⁻¹ d * ch χ d := fun d => by
    simp only [ch, hθ', mul_inv, inv_inv, MulChar.mul_apply]
  have hθ'v : ∀ d, ch θ' d = ch θ d * ch χ⁻¹ d := fun d => by simp only [ch, hθ', MulChar.mul_apply]
  have hθ'm : θ' (-1) = -((-1 : ℂ) ^ e * ψ (-1)) := by
    rw [hθ', MulChar.mul_apply, dc_inv_neg_one, hχm, hpar]; ring

  obtain ⟨c1, hE1⟩ := GlobalTheory.T.eisenstein_periodic_weights_isModularForm e l N (ch ψ) (ch θ) (ch ψ) (ch θ) he hl0 hN
    (ch_zero_of_dvd ψ hl 0 (dvd_zero _))
    (fun x => ch_per ψ l dvd_rfl x) (fun x => ch_per θ N dvd_rfl x)
    (fun d _ => ⟨fun x => by rw [ch_mul', mul_comm], fun x => by rw [ch_mul', mul_comm]⟩)
    (by rw [chm, chm, hpar]; linear_combination ((-1 : ℂ) ^ e) * hψsq)
  rw [mul_comm l N] at hE1
  obtain ⟨c2, hE2⟩ := GlobalTheory.T.eisenstein_periodic_weights_isModularForm (e + 1) (N * l) 1 (fun y => ch ψ⁻¹ y * hat θ' y) (fun _ => 1)
    (fun d => ch ψ⁻¹ d * ch θ'⁻¹ d) (fun _ => 1) (by omega) hNl one_pos
    (by rw [ch_zero_of_dvd ψ⁻¹ hl 0 (dvd_zero _), zero_mul])
    (fun x => by rw [hper ψ⁻¹ hlNl, hatper]) (fun x => rfl)
    (fun d hd => ⟨fun x => by
        rw [ch_mul', (hatch N θ' hN).2.1 d x (coprime_of_dvd hd (dvd_mul_of_dvd_left hNNl 1))]; ring,
      fun x => by simp⟩)
    (by simp only [chm, dc_inv_neg_one, hθ'm]; linear_combination (-(-1 : ℂ) ^ e) * hψsq)
  simp only [mul_one] at hE2
  obtain ⟨c3, hF1⟩ := GlobalTheory.T.eisenstein_periodic_weights_isModularForm e (N * l) 1 (fun y => ch ψ y * hat θ y) (fun _ => 1)
    (fun d => ch ψ d * ch θ⁻¹ d) (fun _ => 1) he hNl one_pos
    (by rw [ch_zero_of_dvd ψ hl 0 (dvd_zero _), zero_mul])
    (fun x => by rw [hper ψ hlNl, hatper]) (fun x => rfl)
    (fun d hd => ⟨fun x => by
        rw [ch_mul', (hatch N θ hN).2.1 d x (coprime_of_dvd hd (dvd_mul_of_dvd_left hNNl 1))]; ring,
      fun x => by simp⟩)
    (by simp only [chm, dc_inv_neg_one, hpar]; linear_combination ((-1 : ℂ) ^ e) * hψsq)
  simp only [mul_one] at hF1
  obtain ⟨c4, hF2⟩ := GlobalTheory.T.eisenstein_periodic_weights_isModularForm (e + 1) l N (ch ψ⁻¹) (ch θ') (ch ψ⁻¹) (ch θ') (by omega) hl0 hN
    (ch_zero_of_dvd ψ⁻¹ hl 0 (dvd_zero _))
    (fun x => ch_per ψ⁻¹ l dvd_rfl x) (fun x => ch_per θ' N dvd_rfl x)
    (fun d _ => ⟨fun x => by rw [ch_mul', mul_comm], fun x => by rw [ch_mul', mul_comm]⟩)
    (by rw [chm, chm, dc_inv_neg_one, hθ'm]; linear_combination (-(-1 : ℂ) ^ e) * hψsq)
  rw [mul_comm l N] at hF2

  obtain ⟨κ1, hκ1, hW1⟩ := GlobalTheory.T.exists_ne_zero_slz_qs_eis_eq_smul e N l ψ θ c1 c3 a₀ b₀ c₀ d₀ hdet he hN hl hlN hE1 hF1
  obtain ⟨κ2, hκ2, hW2⟩ := GlobalTheory.T.exists_ne_zero_slz_qs_eis_eq_smul (e + 1) N l ψ⁻¹ θ' c4 c2 a₀ b₀ c₀ d₀ hdet (by omega) hN hl hlN hF2 hE2
  set W : M2 := !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] with hW
  have hWd : W.det = N := by rw [hW, Matrix.det_fin_two_of]; linear_combination (N : ℤ) * hdet
  obtain ⟨d, hd, hWW⟩ := slashIntMatrixPosDet_atkinLehner_twice e N l a₀ b₀ c₀ d₀ hdet he hN _ _ hE1.2
  set E1 := eis e c1 (ch ψ) (ch θ) with hE1d
  set E2 := eis (e + 1) c2 (fun y => ch ψ⁻¹ y * hat θ' y) (fun _ => 1) with hE2d
  set F1 := eis e c3 (fun y => ch ψ y * hat θ y) (fun _ => 1) with hF1d
  set F2 := eis (e + 1) c4 (ch ψ⁻¹) (ch θ') with hF2d
  set K0 : ℂ := (N : ℂ) ^ e / (N : ℂ) ^ 2 * (ch ψ d * ch θ d) with hK0
  have hF1W : slz e W (qs F1) = (κ1⁻¹ * K0) • qs E1 := by
    have h : qs F1 = κ1⁻¹ • slz e W (qs E1) := by rw [hW1, smul_smul, inv_mul_cancel₀ hκ1, one_smul]
    rw [h, slz_smul', hWW, smul_smul]

  have hmul := (GlobalTheory.EisM.mul_main).1
  have hmf := GlobalTheory.EisM.mul_main.2
  set X := mul E1 E2 with hXd
  set Xm := mul F1 F2 with hXmd
  have hk : 2 * e + 1 = e + (e + 1) := by ring
  have hX : MF (2 * e + 1) (N * l) (ch χ) X := by
    rw [hk]
    refine (GlobalTheory.EisM.mf_linear _ _ _).2.2.2.1 _ _ (fun x hx => ?_) (hmf e (e + 1) (N * l) _ _ E1 E2 hE1 hE2)
    have h1 := ch_mul_inv ψ x (coprime_right (a := N) x hx)
    have h2 := ch_mul_inv θ x (coprime_left (b := l) x hx)
    rw [hθ'inv]; linear_combination (ch θ x * ch θ⁻¹ x * ch χ x) * h1 + ch χ x * h2
  have hXm : MF (2 * e + 1) (N * l) (ch χ⁻¹) Xm := by
    rw [hk]
    refine (GlobalTheory.EisM.mf_linear _ _ _).2.2.2.1 _ _ (fun x hx => ?_) (hmf e (e + 1) (N * l) _ _ F1 F2 hF1 hF2)
    have h1 := ch_mul_inv ψ x (coprime_right (a := N) x hx)
    have h2 := ch_mul_inv θ x (coprime_left (b := l) x hx)
    rw [hθ'v]; linear_combination (ch θ x * ch θ⁻¹ x * ch χ⁻¹ x) * h1 + ch χ⁻¹ x * h2
  set K : ℂ := ((N : ℤ) : ℂ) * (κ1⁻¹ * K0) * κ2 with hK
  have ha' : MF (2 * e + 1) (N * l) (ch χ) (K • X) := ((GlobalTheory.EisM.mf_linear _ _ _).2.2.1 K X hX).1
  have hqs : qs (K • X) = slz (2 * e + 1) W (qs Xm) := by
    rw [((GlobalTheory.EisM.mf_linear _ _ _).2.2.1 K X hX).2, hXd, hXmd, (hmul E1 E2 hE1.1 hE2.1).2,
      (hmul F1 F2 hF1.1 hF2.1).2, hk, slz_mul' e (e + 1) he (by omega) W (qs F1) (qs F2), hF1W, hW2, hWd]
    funext τ; simp only [Pi.smul_apply, smul_eq_mul]; ring
  have hAL' := hAL Xm (K • X) hXm ha' hqs

  have hpE1 : ∀ x, (fun d => ch ψ d * ch θ d) (x + ((N * l : ℕ) : ℤ)) = (fun d => ch ψ d * ch θ d) x := fun x => by
    simp only; rw [hper ψ hlNl, hper θ hNNl]

  have UE1 : Uo l E1 = (ch θ l) • E1 := U_eis_eq _ c1 (ch θ l) (ch ψ) (ch θ) he hNl hl hlNl hpE1 hE1
      (fun x hx => ch_zero_of_dvd ψ hl x hx) (fun y => ch_mul' θ l y)
  have UnitaryRankTwoFlags : Uo l E2 = (1 : ℂ) • E2 := U_eis_eq (fun d => ch ψ⁻¹ d * ch θ'⁻¹ d) c2 1 (fun y => ch ψ⁻¹ y * hat θ' y) (fun _ => 1) (by omega) hNl hl hlNl
      (fun x => by simp only [hper ψ⁻¹ hlNl, hper θ'⁻¹ hNNl]) hE2
      (fun x hx => by simp only [ch_zero_of_dvd ψ⁻¹ hl x hx, zero_mul]) (fun y => by simp)
  have UF1 : Uo l F1 = (1 : ℂ) • F1 := U_eis_eq (fun d => ch ψ d * ch θ⁻¹ d) c3 1 (fun y => ch ψ y * hat θ y) (fun _ => 1) he hNl hl hlNl
      (fun x => by simp only [hper ψ hlNl, hper θ⁻¹ hNNl]) hF1
      (fun x hx => by simp only [ch_zero_of_dvd ψ hl x hx, zero_mul]) (fun y => by simp)
  have UF2 : Uo l F2 = (ch θ' l) • F2 := U_eis_eq (fun d => ch ψ⁻¹ d * ch θ' d) c4 (ch θ' l) (ch ψ⁻¹) (ch θ') (by omega) hNl hl hlNl
      (fun x => by simp only [hper ψ⁻¹ hlNl, hper θ' hNNl]) hF2
      (fun x hx => ch_zero_of_dvd ψ⁻¹ hl x hx) (fun y => ch_mul' θ' l y)
  have hfor := GlobalTheory.EisM.formal_identities ℂ l hl0
  have hFF : (fun x y : ℕ => ψ x * ψ⁻¹ y * ((y : ℂ) / x) ^ e) =
      fun x y : ℕ => ch ψ x * ch ψ⁻¹ y * ((y : ℂ) / x) ^ e := by
    funext x y; simp [ch]

  have hZs : Zs (2 * e + 1) l (ch θ) (hat θ') (fun x y => ψ x * ψ⁻¹ y * ((y : ℂ) / x) ^ e) =
      mul (dep l E1) (dep l E2) := by
    have := GlobalTheory.zs_eq_mul_dep_eis (2 * e + 1) l e (ch θ) (hat θ') (ch ψ) (ch ψ⁻¹) c1 c2 (by omega)
    rw [show 2 * e + 1 - 1 - e = e by omega] at this
    rw [hFF, this]
  simp only [val, pow_one, Function.iterate_one] at hval
  rw [hZs, (hfor.2.1 E1 E2), UE1, UnitaryRankTwoFlags, mul_smul_smul, lam_sub_smul, hEig.U _ hX] at hval

  have hZm : Zm (2 * e + 1) l (hat θ) (ch θ') (fun A d => ψ A * ψ⁻¹ d * ((d : ℂ) / A) ^ e) =
      mul (dep l F1) (dep l F2) := by
    have := GlobalTheory.T.eisensteinProductSeries_eq_depleted_eisenstein_product (2 * e + 1) l e (hat θ) (ch θ') (ch ψ) (ch ψ⁻¹) c3 c4 (by omega)
    rw [show 2 * e + 1 - 1 - e = e by omega,
      show (fun x => hat θ x * ch ψ x) = fun x => ch ψ x * hat θ x from funext fun x => mul_comm _ _] at this
    rw [hFF, this]
  simp only [val, pow_one, Function.iterate_one]
  rw [hZm, (hfor.2.1 F1 F2), UF1, UF2, mul_smul_smul, lam_sub_smul, hU' _ hXm, hAL', lam_smul]

  have hcl : χ⁻¹ (l : ZMod N) = ch χ⁻¹ l := by simp [ch]
  have hlc : IsCoprime (l : ℤ) (N : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hl).2 hlN)
  have hχl : ch χ⁻¹ l ≠ 0 := ch_ne_zero _ _ hlc
  have hKne : K ≠ 0 := by
    have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have h1 := ch_ne_zero ψ d (coprime_right (a := N) d hd)
    have h2 := ch_ne_zero θ d (coprime_left (b := l) d hd)
    rw [hK, hK0]; push_cast
    exact mul_ne_zero (mul_ne_zero hN0 (mul_ne_zero (inv_ne_zero hκ1)
      (mul_ne_zero (div_ne_zero (pow_ne_zero _ hN0) (pow_ne_zero _ hN0)) (mul_ne_zero h1 h2)))) hκ2
  have hv : (α - ch θ l) * lam B c X ≠ 0 := by
    intro h; apply hval; linear_combination α⁻¹ * h
  rw [hcl, hθ'v]
  have : (ch χ⁻¹ l * α)⁻¹ * (ch χ⁻¹ l * α * (K * lam B c X) - 1 * (ch θ l * ch χ⁻¹ l) * (K * lam B c X)) =
      (ch χ⁻¹ l * α)⁻¹ * (ch χ⁻¹ l * K * ((α - ch θ l) * lam B c X)) := by ring
  rw [this]
  exact mul_ne_zero (inv_ne_zero (mul_ne_zero hχl hα0)) (mul_ne_zero (mul_ne_zero hχl hKne) hv)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MuModelProductValueNeZeroOfDepletedStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.muModelProduct_value_ne_zero_of_depleted : ∀ (e N l : ℕ) (χ θ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l) (g : ℕ → ℂ) (α β : ℂ) (a₀ b₀ c₀ d₀ : ℤ), N * a₀ * d₀ - l * b₀ * c₀ = 1 → 1 ≤ e → 0 < N → l.Prime → ¬ l ∣ N → Prim (2 * e + 1) N χ⁻¹ (fun n => conj (g n)) → α + β = χ l * conj (g l) → α * β = χ l * (l : ℂ) ^ (2 * e) → α ≠ 0 → θ (-1) = (-1) ^ e * ψ (-1) → θ * χ⁻¹ ≠ 1 → ∀ (B : ℕ) (c : ℕ → ℂ), EigF (2 * e + 1) N l χ (fun q => χ q * conj (g q)) α B c → val B c l α 1 (Zs (2 * e + 1) l (ch θ) (hat ⇑(θ * χ⁻¹)) (fun x y => ψ x * ψ⁻¹ y * ((y : ℂ) / x) ^ e)) ≠ 0 → ∀ (B' : ℕ) (c' : ℕ → ℂ), (∀ a a', MF (2 * e + 1) (N * l) (ch χ⁻¹) a → MF (2 * e + 1) (N * l) (ch χ) a' → qs a' = slz (2 * e + 1) !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs a) → lam B' c' a = lam B c a') → (∀ a, MF (2 * e + 1) (N * l) (ch χ⁻¹) a → lam B' c' (Uo l a) = χ⁻¹ l * α * lam B' c' a) → val B' c' l (χ⁻¹ l * α) 1 (Zm (2 * e + 1) l (hat θ) (ch (θ * χ⁻¹)) (fun A d => ψ A * ψ⁻¹ d * ((d : ℂ) / A) ^ e)) ≠ 0 := by
  first | exact @GlobalTheory.zm_val_ne_zero | exact GlobalTheory.zm_val_ne_zero | (intros; apply GlobalTheory.zm_val_ne_zero <;> assumption)
end
