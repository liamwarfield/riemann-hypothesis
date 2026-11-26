module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.SumDivHecke
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.UnitFormC

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.ConstCj
open Finset UpperTheory.V.Sd

namespace UpperTheory.V.Z.Sym.Unl

private theorem gauss_mul_gauss_inv {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    gaussSum χ ZMod.stdAddChar * gaussSum χ⁻¹ ZMod.stdAddChar * χ (-1) = N := by
  have hi : (χ⁻¹).IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]; exact hχ
  have h1 : ZMod.dft (χ : ZMod N → ℂ) = fun k => χ⁻¹ (-k) * gaussSum χ ZMod.stdAddChar :=
    funext fun k => hχ.fourierTransform_eq_inv_mul_gaussSum k
  have h2 := congrFun (ZMod.dft_dft (χ : ZMod N → ℂ)) (-1)
  rw [h1, ZMod.dft_mul_const (fun k => χ⁻¹ (-k)), ZMod.dft_comp_neg (fun k => χ⁻¹ k)] at h2
  simp only [neg_neg, map_one, smul_eq_mul, mul_one] at h2
  have h3 := hi.fourierTransform_eq_inv_mul_gaussSum 1
  rw [inv_inv] at h3
  have h4 : ZMod.dft (fun k => χ⁻¹ k) 1 = χ (-1) * gaussSum χ⁻¹ ZMod.stdAddChar := h3
  rw [h4] at h2
  rw [← h2]; ring

private theorem gauss_inv_ne {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    gaussSum χ⁻¹ ZMod.stdAddChar ≠ 0 := by
  intro h
  have := gauss_mul_gauss_inv χ hχ
  rw [h, mul_zero, zero_mul] at this
  exact (NeZero.ne N) (by exact_mod_cast this.symm)

private theorem map_Lk (σ : ℂ ≃+* ℂ) (k : ℕ) (x : ℂ) : σ (Lk k x) = Lk k (σ x) := by
  unfold Lk
  rw [map_div₀, map_pow, map_sub, map_one]
  congr 1
  exact (Polynomial.aeval_algHom_apply (σ.toRingHom.toIntAlgHom) x (numL k)).symm

private theorem cj_inv_apply {N : ℕ} (σ : ℂ ≃+* ℂ) (χ : DirichletCharacter ℂ N) (a : ZMod N) :
    σ (χ⁻¹ a) = (cj σ χ)⁻¹ a := by
  rw [MulChar.inv_apply, MulChar.inv_apply]
  rfl

private theorem sum_conj {N : ℕ} [NeZero N] (σ : ℂ ≃+* ℂ) (χ : DirichletCharacter ℂ N) (s : (ZMod N)ˣ)
    (hs : ∀ b : ZMod N, σ (ZMod.stdAddChar b : ℂ) = (ZMod.stdAddChar ((s : ZMod N) * b) : ℂ))
    (F : ℂ → ℂ) (hF : ∀ x, σ (F x) = F (σ x)) :
    σ (∑ a : ZMod N, χ⁻¹ a * F (ZMod.stdAddChar a : ℂ)) =
      (cj σ χ)⁻¹ ((s⁻¹ : (ZMod N)ˣ) : ZMod N) * ∑ a : ZMod N, (cj σ χ)⁻¹ a * F (ZMod.stdAddChar a : ℂ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.mul_sum]
  refine Fintype.sum_equiv (Units.mulLeft s) _ _ fun a => ?_
  have hu : (Units.mulLeft s a : ZMod N) = (s : ZMod N) * a := rfl
  rw [map_mul, hF, hs, cj_inv_apply, hu, ← mul_assoc, ← map_mul, ← mul_assoc, Units.inv_mul, one_mul]

theorem constCj : ConstCj := by
  intro N k _ hN χ hχ σ c c' h1 h2
  obtain ⟨s, hs, -⟩ := eisCj N hN σ
  have hG := sum_conj σ χ s hs id (fun _ => rfl)
  have hS := sum_conj σ χ s hs (Lk k) (map_Lk σ k)
  simp only [id] at hG
  have hG' : σ (gaussSum χ⁻¹ ZMod.stdAddChar) =
      (cj σ χ)⁻¹ ((s⁻¹ : (ZMod N)ˣ) : ZMod N) * gaussSum (cj σ χ)⁻¹ ZMod.stdAddChar := hG
  have hne : (cj σ χ)⁻¹ ((s⁻¹ : (ZMod N)ˣ) : ZMod N) * gaussSum (cj σ χ)⁻¹ ZMod.stdAddChar ≠ 0 := by
    rw [← hG']
    exact (map_ne_zero σ).2 (gauss_inv_ne χ hχ)
  have h3 := congrArg σ h1
  rw [hS, ← h2, map_mul, map_mul, hG', map_ofNat] at h3
  have h4 : ((cj σ χ)⁻¹ ((s⁻¹ : (ZMod N)ˣ) : ZMod N) * gaussSum (cj σ χ)⁻¹ ZMod.stdAddChar) * (2 * σ c) =
      ((cj σ χ)⁻¹ ((s⁻¹ : (ZMod N)ˣ) : ZMod N) * gaussSum (cj σ χ)⁻¹ ZMod.stdAddChar) * (2 * c') := by
    linear_combination h3
  have h5 := mul_left_cancel₀ hne h4
  have h6 : (2 : ℂ) ≠ 0 := two_ne_zero
  exact (mul_left_cancel₀ h6 h5).symm

end UpperTheory.V.Z.Sym.Unl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.EigLiftC
open Formalism.ConjugateSelfDual CongruenceSubgroup UpperHalfPlane UpperTheory.V.Af UpperTheory.V.Sd
open scoped MatrixGroups ModularForm

noncomputable section

namespace UpperTheory.V.Z.Sym.Unl

private theorem one_mem_per (N : ℕ) :
    (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Gamma1 N)).strictPeriods := by
  show (1 : ℝ) ∈ (Gamma1 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods
  rw [strictPeriods_Gamma1]
  exact AddSubgroup.mem_zmultiples 1

private theorem coef_smul {N : ℕ} {k : ℤ} (c : ℂ) (f : CuspForm (Gamma1 N) k) (n : ℕ) :
    coef (c • f : CuspForm (Gamma1 N) k) n = c * coef f n := by
  unfold coef
  rw [show ((c • f : CuspForm (Gamma1 N) k) : ℍ → ℂ) = c • (f : ℍ → ℂ) from rfl,
    ModularForm.qExpansion_smul one_pos (one_mem_per N) c f]
  simp

private theorem coef_add {N : ℕ} {k : ℤ} (f g : CuspForm (Gamma1 N) k) (n : ℕ) :
    coef (f + g : CuspForm (Gamma1 N) k) n = coef f n + coef g n := by
  show PowerSeries.coeff n (qExpansion 1 ⇑(f + g)) =
    PowerSeries.coeff n (qExpansion 1 ⇑f) + PowerSeries.coeff n (qExpansion 1 ⇑g)
  rw [show ⇑(f + g) = ⇑f + ⇑g from rfl, ModularForm.qExpansion_add one_pos (one_mem_per N) f g, map_add (f := _)]

private theorem norm_chi {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (a : ZMod N) : ‖ι.symm (χ a)‖ ≤ 1 := by
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    have hpos : 0 < orderOf u := orderOf_pos u
    have hpow : (χ u) ^ orderOf u = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one, map_one]
    have h1 : ‖ι.symm (χ u)‖ ^ orderOf u = 1 := by
      rw [← norm_pow, ← map_pow, hpow, map_one, norm_one]
    exact le_of_eq ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hpos.ne').mp h1)
  · rw [MulChar.map_nonunit χ ha, map_zero, norm_zero]
    exact zero_le_one

private def fT {K : Type} [Field K] (p : ℕ) (e : K) : Module.End K (ℕ → K) where
  toFun c n := c (p * n) + e * (if p ∣ n then c (n / p) else 0)
  map_add' c d := by
    funext n
    by_cases h : p ∣ n <;> simp [h] <;> ring
  map_smul' a c := by
    funext n
    by_cases h : p ∣ n <;> simp [h] <;> ring

private theorem fT_apply {K : Type} [Field K] (p : ℕ) (e : K) (c : ℕ → K) (n : ℕ) :
    fT p e c n = c (p * n) + e * (if p ∣ n then c (n / p) else 0) := rfl

private theorem fT_comm {K : Type} [Field K] {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (e e' : K)
    (c : ℕ → K) : fT p e (fT q e' c) = fT q e' (fT p e c) := by
  funext n
  simp only [fT_apply]
  have hqp : ¬ q ∣ p := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp h).symm
  have hpq' : ¬ p ∣ q := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)
  have dq : ∀ m, q ∣ p * m ↔ q ∣ m := fun m =>
    ⟨fun h => (hq.dvd_mul.mp h).resolve_left hqp, fun h => dvd_mul_of_dvd_right h p⟩
  have dp : ∀ m, p ∣ q * m ↔ p ∣ m := fun m =>
    ⟨fun h => (hp.dvd_mul.mp h).resolve_left hpq', fun h => dvd_mul_of_dvd_right h q⟩
  have hc : q * (p * n) = p * (q * n) := Nat.mul_left_comm q p n
  have hdd : n / p / q = n / q / p := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]
  rw [hc, hdd]
  simp only [dq, dp]
  by_cases hpn : p ∣ n <;> by_cases hqn : q ∣ n
  · have h1 : q ∣ n / p := (dq _).mp (by rwa [Nat.mul_div_cancel' hpn])
    have h2 : p ∣ n / q := (dp _).mp (by rwa [Nat.mul_div_cancel' hqn])
    simp only [hpn, hqn, h1, h2, ↓reduceIte, Nat.mul_div_assoc p hqn, Nat.mul_div_assoc q hpn]
    ring
  · have h1 : ¬ q ∣ n / p := fun h => hqn (by
      rw [← Nat.mul_div_cancel' hpn]
      exact dvd_mul_of_dvd_right h p)
    simp only [hpn, hqn, h1, ↓reduceIte, Nat.mul_div_assoc q hpn]
    ring
  · have h2 : ¬ p ∣ n / q := fun h => hpn (by
      rw [← Nat.mul_div_cancel' hqn]
      exact dvd_mul_of_dvd_right h q)
    simp only [hpn, hqn, h2, ↓reduceIte, Nat.mul_div_assoc p hqn]
    ring
  · simp only [hpn, hqn, ↓reduceIte]
    ring

private theorem eq_zero_of_eig {K : Type} [Field K] (e b : Nat.Primes → K) (c : ℕ → K) (h0 : c 0 = 0) (h1 : c 1 = 0)
    (h : ∀ p : Nat.Primes, fT p.1 (e p) c = b p • c) : c = 0 := by
  funext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    show c n = 0
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · exact h0
      · exact h1
    · have hp : (Nat.minFac n).Prime := Nat.minFac_prime (by omega)
      obtain ⟨m, hm⟩ := Nat.minFac_dvd n
      have hp2 := hp.two_le
      have hm1 : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with h' | h'
        · rw [h', mul_zero] at hm
          omega
        · exact h'
      have hmn : m < n := by
        have : 1 * m < Nat.minFac n * m := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
        omega
      have hcm : c m = 0 := ih m hmn
      have hcmp : c (m / n.minFac) = 0 := ih _ (lt_of_le_of_lt (Nat.div_le_self _ _) hmn)
      have he := congrFun (h ⟨n.minFac, hp⟩) m
      simp only [fT_apply, Pi.smul_apply, smul_eq_mul, hcm, mul_zero, hcmp, ite_self, add_zero] at he
      rw [hm]
      exact he

private def Phi {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (N : ℕ) (k : ℤ) :
    CuspForm (Gamma1 N) k →ₛₗ[(ι.symm : ℂ →+* Qbar l)] (ℕ → Qbar l) where
  toFun g n := if n = 0 then 0 else ι.symm (coef g n)
  map_add' f g := by
    funext n
    by_cases h : n = 0 <;> simp only [h, if_true, if_false, coef_add, Pi.add_apply, map_add (f := _), add_zero]
  map_smul' a f := by
    funext n
    by_cases h : n = 0 <;> simp only [h, if_true, if_false, coef_smul, Pi.smul_apply, map_mul, smul_eq_mul, mul_zero]
    rfl

private theorem Phi_apply {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (N : ℕ) (k : ℤ) (g : CuspForm (Gamma1 N) k) (n : ℕ) :
    Phi ι N k g n = if n = 0 then 0 else ι.symm (coef g n) := rfl

private def chSub (N k : ℕ) (χ : DirichletCharacter ℂ N) : Submodule ℂ (CuspForm (Gamma1 N) (k : ℤ)) where
  carrier := {g | HasChar k χ g}
  add_mem' := by
    intro f g hf hg γ hγ
    rw [show ((f + g : CuspForm (Gamma1 N) (k : ℤ)) : ℍ → ℂ) = (f : ℍ → ℂ) + g from rfl, SlashAction.add_slash,
      hf γ hγ, hg γ hγ, smul_add]
  zero_mem' := by
    intro γ _
    rw [show ((0 : CuspForm (Gamma1 N) (k : ℤ)) : ℍ → ℂ) = 0 from rfl, SlashAction.zero_slash, smul_zero]
  smul_mem' := by
    intro c f hf γ hγ
    rw [show ((c • f : CuspForm (Gamma1 N) (k : ℤ)) : ℍ → ℂ) = c • (f : ℍ → ℂ) from rfl, ModularForm.SL_smul_slash,
      hf γ hγ, smul_comm]

private theorem coef_zero' {N : ℕ} {k : ℤ} (n : ℕ) : coef (0 : CuspForm (Gamma1 N) k) n = 0 := by
  show PowerSeries.coeff n (qExpansion 1 (0 : ℍ → ℂ)) = 0
  rw [qExpansion_zero]
  simp

private def cjSub (N k : ℕ) (χ : DirichletCharacter ℂ N) : Submodule ℂ (CuspForm (Gamma1 N) (k : ℤ)) where
  carrier := {g | HasChar k χ g ∧ Cj k N χ g}
  add_mem' := by
    rintro f g ⟨hf, hf'⟩ ⟨hg, hg'⟩
    refine ⟨(chSub N k χ).add_mem hf hg, fun σ => ?_⟩
    obtain ⟨f', a1, a2⟩ := hf' σ
    obtain ⟨g', b1, b2⟩ := hg' σ
    refine ⟨f' + g', (chSub N k (cj σ χ)).add_mem a1 b1, fun n hn => ?_⟩
    rw [coef_add, coef_add, a2 n hn, b2 n hn, map_add (f := _)]
  zero_mem' := by
    refine ⟨(chSub N k χ).zero_mem, fun σ => ⟨0, (chSub N k (cj σ χ)).zero_mem, fun n _ => ?_⟩⟩
    rw [coef_zero', map_zero]
  smul_mem' := by
    rintro c f ⟨hf, hf'⟩
    refine ⟨(chSub N k χ).smul_mem c hf, fun σ => ?_⟩
    obtain ⟨f', a1, a2⟩ := hf' σ
    refine ⟨σ c • f', (chSub N k (cj σ χ)).smul_mem _ a1, fun n hn => ?_⟩
    rw [coef_smul, coef_smul, a2 n hn, map_mul]

private theorem heckeC (N k : ℕ) [NeZero N] (hk : 1 ≤ k) (χ : DirichletCharacter ℂ N)
    (g : CuspForm (Gamma1 N) (k : ℤ)) (hg : g ∈ cjSub N k χ) (p : ℕ) (hp : p.Prime) :
    ∃ g' ∈ cjSub N k χ, ∀ n, 1 ≤ n → coef g' n =
      coef g (p * n) + χ (p : ZMod N) * (p : ℂ) ^ (k - 1) * (if p ∣ n then coef g (n / p) else 0) := by
  obtain ⟨hgc, hgj⟩ := hg
  obtain ⟨g', hg'c, hg'n⟩ := heckeEx N k hk χ g hgc p hp
  refine ⟨g', ⟨hg'c, fun σ => ?_⟩, hg'n⟩
  obtain ⟨f', hf'c, hf'n⟩ := hgj σ
  obtain ⟨f'', hf''c, hf''n⟩ := heckeEx N k hk (cj σ χ) f' hf'c p hp
  refine ⟨f'', hf''c, fun n hn => ?_⟩
  have hpn : 1 ≤ p * n := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hp.ne_zero (by omega))
  have hcj : (cj σ χ) (p : ZMod N) = σ (χ p) := rfl
  rw [hf''n n hn, hg'n n hn]
  by_cases hd : p ∣ n
  · have hq : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd (by omega) hd) hp.pos
    simp only [hd, if_true, hf'n _ hq, hf'n _ hpn, hcj, map_add (f := _), map_mul, map_pow, map_natCast]
  · simp only [hd, if_false, hf'n _ hpn, hcj, map_add (f := _), map_mul, mul_zero, map_zero]

private theorem fT_Phi {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (N : ℕ) (k : ℤ) (g : CuspForm (Gamma1 N) k)
    {p : ℕ} (hp : p.Prime) (e : ℂ) {n : ℕ} (hn : 1 ≤ n) :
    fT p (ι.symm e) (Phi ι N k g) n = ι.symm (coef g (p * n) + e * (if p ∣ n then coef g (n / p) else 0)) := by
  have hn0 : n ≠ 0 := by omega
  have hpn : p * n ≠ 0 := Nat.mul_ne_zero hp.ne_zero hn0
  rw [fT_apply, Phi_apply, if_neg hpn]
  by_cases hd : p ∣ n
  · have hq : n / p ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (by omega) hd) hp.pos).ne'
    rw [if_pos hd, if_pos hd, Phi_apply, if_neg hq, map_add (f := _), map_mul]
  · rw [if_neg hd, if_neg hd]
    simp

end UpperTheory.V.Z.Sym.Unl

set_option maxHeartbeats 1000000 in
open UpperTheory.V.Z.Sym.Unl in
theorem UpperTheory.V.Z.Sym.Unl.eigLiftC :
    UpperTheory.V.Z.Sym.Unl.EigLiftC := by
  intro l _ ι N k _ hk χ f hfc hfj hfI hf1 a ha
  obtain ⟨e, he_def⟩ : ∃ e : Nat.Primes → Qbar l,
      ∀ p, e p = ι.symm (χ (p.1 : ZMod N) * (p.1 : ℂ) ^ (k - 1)) := ⟨_, fun _ => rfl⟩
  have hfW : f ∈ cjSub N k χ := ⟨hfc, hfj⟩
  have hfd : FiniteDimensional (Qbar l) ((cjSub N k χ).map (Phi ι N k)) := by
    haveI := (finDim N k).1
    exact Module.Finite.iff_fg.mpr ((IsNoetherian.noetherian (cjSub N k χ)).map _)
  have hinv : ∀ p : Nat.Primes, ∀ v ∈ (cjSub N k χ).map (Phi ι N k),
      fT p.1 (e p) v ∈ (cjSub N k χ).map (Phi ι N k) := by
    intro p v hv
    obtain ⟨g, hg, rfl⟩ := hv
    obtain ⟨g', hg', hg'n⟩ := heckeC N k hk χ g hg p.1 p.2
    refine ⟨g', hg', ?_⟩
    funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Phi_apply, fT_apply]
    · show Phi ι N k g' n = fT p.1 (e p) (Phi ι N k g) n
      rw [he_def p, fT_Phi ι N k g p.2 _ hn, Phi_apply, if_neg (show n ≠ 0 by omega), hg'n n hn]
  have he : ∀ p : Nat.Primes, ‖e p‖ ≤ 1 := by
    intro p
    rw [he_def p, map_mul ι.symm, map_pow ι.symm, map_natCast ι.symm, norm_mul, norm_pow]
    exact mul_le_one₀ (norm_chi ι χ _) (by positivity)
      (pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one (Qbar l) _))
  have key : ∀ (p : Nat.Primes) (v : ℕ → Qbar l) (n : ℕ),
      ‖fT p.1 (e p) v n‖ ≤ max ‖v (p.1 * n)‖ (if p.1 ∣ n then ‖v (n / p.1)‖ else 0) := by
    intro p v n
    rw [fT_apply]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max le_rfl ?_)
    split_ifs
    · rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (he p)
    · simp
  let T : Nat.Primes → Module.End (Qbar l) ((cjSub N k χ).map (Phi ι N k)) :=
    fun p => (fT p.1 (e p)).restrict (hinv p)
  have hT : ∀ p v, ((T p v : ↥((cjSub N k χ).map (Phi ι N k))) : ℕ → Qbar l) = fT p.1 (e p) v := fun _ _ => rfl
  have hcomm : ∀ i j, T i * T j = T j * T i := by
    intro i j
    refine LinearMap.ext fun v => Subtype.ext ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, hT, hT, hT, hT]
    by_cases hij : i = j
    · rw [hij]
    · exact fT_comm i.2 j.2 (fun h => hij (Subtype.ext h)) _ _ _
  have hle : ∀ (j : Nat.Primes) (v : ↥((cjSub N k χ).map (Phi ι N k))), (∀ n, ‖(v : ℕ → Qbar l) n‖ ≤ 1) →
      ∀ n, ‖((T j v : ↥((cjSub N k χ).map (Phi ι N k))) : ℕ → Qbar l) n‖ ≤ 1 := by
    intro j v hv n
    rw [hT]
    refine (key j v n).trans (max_le (hv _) ?_)
    split_ifs
    · exact hv _
    · exact zero_le_one
  have hlt : ∀ (j : Nat.Primes) (v : ↥((cjSub N k χ).map (Phi ι N k))), (∀ n, ‖(v : ℕ → Qbar l) n‖ < 1) →
      ∀ n, ‖((T j v : ↥((cjSub N k χ).map (Phi ι N k))) : ℕ → Qbar l) n‖ < 1 := by
    intro j v hv n
    rw [hT]
    refine lt_of_le_of_lt (key j v n) (max_lt (hv _) ?_)
    split_ifs
    · exact hv _
    · exact zero_lt_one
  have hfint : ∀ n, ‖Phi ι N k f n‖ ≤ 1 := by
    intro n
    rw [Phi_apply]
    split_ifs
    · simp
    · exact hfI n
  have hf1' : ‖Phi ι N k f 1‖ = 1 := by
    rw [Phi_apply, if_neg one_ne_zero]
    exact hf1
  let f0 : ↥((cjSub N k χ).map (Phi ι N k)) := ⟨Phi ι N k f, Submodule.mem_map_of_mem hfW⟩
  have happ : ∀ (j : Nat.Primes) (n : ℕ),
      ‖((T j f0 : ↥((cjSub N k χ).map (Phi ι N k))) : ℕ → Qbar l) n - ι.symm (a j.1) * (f0 : ℕ → Qbar l) n‖ < 1 := by
    intro j n
    rw [hT]
    show ‖fT j.1 (e j) (Phi ι N k f) n - ι.symm (a j.1) * Phi ι N k f n‖ < 1
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Phi_apply, fT_apply]
    · rw [he_def j, fT_Phi ι N k f j.2 _ hn, Phi_apply, if_neg (show n ≠ 0 by omega), ← map_mul ι.symm, ← map_sub ι.symm]
      exact (ha j.1 j.2).2 n hn
  obtain ⟨h, b, hne, -, hhe, hb⟩ := delSerre l ℕ Nat.Primes ((cjSub N k χ).map (Phi ι N k)) hfd T hcomm hle hlt
    f0 (fun p => ι.symm (a p.1)) hfint ⟨1, hf1'⟩ (fun p => (ha p.1 p.2).1) happ
  obtain ⟨g, hgW, hgh⟩ := h.2
  have hev : ∀ p : Nat.Primes, fT p.1 (e p) (Phi ι N k g) = b p • Phi ι N k g := by
    intro p
    rw [hgh, ← hT]
    exact congrArg Subtype.val (hhe p)
  have hc1 : coef g 1 ≠ 0 := by
    intro hz
    apply hne
    apply Subtype.ext
    show (h : ℕ → Qbar l) = 0
    rw [← hgh]
    refine eq_zero_of_eig e b _ ?_ ?_ hev
    · rw [Phi_apply, if_pos rfl]
    · rw [Phi_apply, if_neg one_ne_zero, hz, map_zero]
  have heig : ∀ p (hp : p.Prime) n, 1 ≤ n →
      coef g (p * n) + χ p * (p : ℂ) ^ (k - 1) * (if p ∣ n then coef g (n / p) else 0) =
        ι (b ⟨p, hp⟩) * coef g n := by
    intro p hp n hn
    have h1 := congrFun (hev ⟨p, hp⟩) n
    change fT p (e ⟨p, hp⟩) (Phi ι N k g) n = b ⟨p, hp⟩ * Phi ι N k g n at h1
    rw [he_def ⟨p, hp⟩, fT_Phi ι N k g hp _ hn, Phi_apply, if_neg (show n ≠ 0 by omega)] at h1
    have h2 := congrArg ι h1
    rwa [RingEquiv.apply_symm_apply, map_mul ι, RingEquiv.apply_symm_apply] at h2
  have hlam : ∀ p (hp : p.Prime), (coef g 1)⁻¹ * coef g p = ι (b ⟨p, hp⟩) := by
    intro p hp
    have h1 := heig p hp 1 le_rfl
    rw [mul_one, if_neg hp.not_dvd_one, mul_zero, add_zero] at h1
    rw [h1, mul_comm, mul_assoc, mul_inv_cancel₀ hc1, mul_one]
  have hg1W : (coef g 1)⁻¹ • g ∈ cjSub N k χ := (cjSub N k χ).smul_mem _ hgW
  refine ⟨⟨(coef g 1)⁻¹ • g, hg1W.1, ?_, ?_⟩, hg1W.2, fun p hp => ?_⟩
  · rw [coef_smul]
    exact inv_mul_cancel₀ hc1
  · intro p hp n hn
    simp only [coef_smul]
    rw [hlam p hp]
    have hr : (coef g 1)⁻¹ * coef g (p * n) + χ p * (p : ℂ) ^ (k - 1) *
        (if p ∣ n then (coef g 1)⁻¹ * coef g (n / p) else 0) =
        (coef g 1)⁻¹ * (coef g (p * n) + χ p * (p : ℂ) ^ (k - 1) *
        (if p ∣ n then coef g (n / p) else 0)) := by
      split_ifs <;> ring
    rw [hr, heig p hp n hn]
    ring
  · show ‖ι.symm (coef ⇑((coef g 1)⁻¹ • g) p - a p)‖ < 1
    rw [coef_smul, hlam p hp, map_sub ι.symm, RingEquiv.symm_apply_apply]
    exact hb ⟨p, hp⟩
end
end

open Formalism.ConjugateSelfDual CongruenceSubgroup UpperHalfPlane UpperTheory.V.Af UpperTheory.V.Sd
open scoped MatrixGroups ModularForm

namespace UpperTheory.V.Z.Sym.Unl

private theorem sum_div_split (g : ℕ → ℂ) (hg : ∀ a b, g (a * b) = g a * g b) {p : ℕ} (hp : p.Prime) (n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ (p * n).divisors with p ∣ j, g j = g p * ∑ j ∈ n.divisors, g j := by
  have hp0 : 0 < p := hp.pos
  have hset : (p * n).divisors.filter (fun j => p ∣ j) = n.divisors.image (fun d => p * d) := by
    ext j
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_image]
    constructor
    · rintro ⟨⟨hj, _⟩, ⟨d, rfl⟩⟩
      exact ⟨d, ⟨(Nat.mul_dvd_mul_iff_left hp0).mp hj, by omega⟩, rfl⟩
    · rintro ⟨d, ⟨hd, _⟩, rfl⟩
      exact ⟨⟨Nat.mul_dvd_mul_left p hd, mul_ne_zero hp.ne_zero (by omega)⟩, dvd_mul_right p d⟩
  rw [hset, Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hp0 h), Finset.mul_sum]
  simp only [hg]

private theorem sum_div_hecke (g : ℕ → ℂ) (hg : ∀ a b, g (a * b) = g a * g b) {p : ℕ} (hp : p.Prime) (n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ (p * n).divisors, g j + g p * (if p ∣ n then ∑ j ∈ (n / p).divisors, g j else 0) =
      (1 + g p) * ∑ j ∈ n.divisors, g j := by
  rw [← Finset.sum_filter_add_sum_filter_not (p * n).divisors (fun j => p ∣ j) g,
    sum_div_split g hg hp n hn]
  have hnd : (p * n).divisors.filter (fun j => ¬ p ∣ j) = n.divisors.filter (fun j => ¬ p ∣ j) := by
    ext j
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hj, _⟩, hpj⟩
      have hc : Nat.Coprime j p := Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpj)
      exact ⟨⟨hc.dvd_of_dvd_mul_left hj, by omega⟩, hpj⟩
    · rintro ⟨⟨hj, _⟩, hpj⟩
      exact ⟨⟨dvd_mul_of_dvd_right hj p, mul_ne_zero hp.ne_zero (by omega)⟩, hpj⟩
  have hsplit := Finset.sum_filter_add_sum_filter_not n.divisors (fun j => p ∣ j) g
  have hdiv : (∑ j ∈ n.divisors with p ∣ j, g j) =
      g p * (if p ∣ n then ∑ j ∈ (n / p).divisors, g j else 0) := by
    split_ifs with hpn
    · obtain ⟨m, rfl⟩ := hpn
      have hm : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · subst h0
          simp at hn
        · exact h0
      rw [Nat.mul_div_cancel_left m hp.pos]
      exact sum_div_split g hg hp m hm
    · rw [mul_zero]
      apply Finset.sum_eq_zero
      intro j hj
      simp only [Finset.mem_filter, Nat.mem_divisors] at hj
      exact absurd (hj.2.trans hj.1.1) hpn
  rw [hnd, ← hdiv, ← hsplit]
  ring

private theorem sig_hecke (k : ℕ) {N : ℕ} (χ : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime) (n : ℕ) (hn : 1 ≤ n) :
    sigChi k χ (p * n) + χ (p : ZMod N) * (p : ℂ) ^ (k - 1) * (if p ∣ n then sigChi k χ (n / p) else 0) =
      (1 + χ (p : ZMod N) * (p : ℂ) ^ (k - 1)) * sigChi k χ n := by
  have hg : ∀ a b : ℕ, (fun j : ℕ => χ (j : ZMod N) * (j : ℂ) ^ (k - 1)) (a * b) =
      (fun j : ℕ => χ (j : ZMod N) * (j : ℂ) ^ (k - 1)) a *
        (fun j : ℕ => χ (j : ZMod N) * (j : ℂ) ^ (k - 1)) b := by
    intro a b
    simp only [Nat.cast_mul, map_mul, mul_pow]
    ring
  have h := sum_div_hecke (fun j : ℕ => χ (j : ZMod N) * (j : ℂ) ^ (k - 1)) hg hp n hn
  beta_reduce at h
  simp only [sigChi]
  exact h

section Int

variable {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ)

private theorem int_add {x y : ℂ} (hx : ‖ι.symm x‖ ≤ 1) (hy : ‖ι.symm y‖ ≤ 1) : ‖ι.symm (x + y)‖ ≤ 1 := by
  rw [map_add (f := _)]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)

private theorem int_sub {x y : ℂ} (hx : ‖ι.symm x‖ ≤ 1) (hy : ‖ι.symm y‖ ≤ 1) : ‖ι.symm (x - y)‖ ≤ 1 := by
  rw [map_sub, sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx (by rwa [norm_neg]))

private theorem int_mul {x y : ℂ} (hx : ‖ι.symm x‖ ≤ 1) (hy : ‖ι.symm y‖ ≤ 1) : ‖ι.symm (x * y)‖ ≤ 1 := by
  rw [map_mul, norm_mul]
  exact mul_le_one₀ hx (norm_nonneg _) hy

private theorem small_mul {x y : ℂ} (hx : ‖ι.symm x‖ < 1) (hy : ‖ι.symm y‖ ≤ 1) : ‖ι.symm (x * y)‖ < 1 := by
  rw [map_mul, norm_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) hy) hx

private theorem int_chi {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (a : ZMod N) : ‖ι.symm (χ a)‖ ≤ 1 := by
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    have hfin : 0 < orderOf u := orderOf_pos u
    have h1 : (ι.symm (χ u)) ^ orderOf u = 1 := by
      rw [← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one,
        map_one, map_one]
    have h2 : ‖ι.symm (χ u)‖ ^ orderOf u = 1 := by
      rw [← norm_pow, h1, norm_one]
    exact le_of_eq ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hfin.ne').mp h2)
  · rw [MulChar.map_nonunit χ ha, map_zero, norm_zero]
    exact zero_le_one

private theorem int_term (k : ℕ) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (j : ℕ) :
    ‖ι.symm (χ (j : ZMod N) * (j : ℂ) ^ (k - 1))‖ ≤ 1 := by
  refine int_mul ι (int_chi ι χ _) ?_
  rw [map_pow, map_natCast, norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ j)

private theorem int_sig (k : ℕ) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (n : ℕ) :
    ‖ι.symm (sigChi k χ n)‖ ≤ 1 := by
  unfold sigChi
  generalize n.divisors = s
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    rw [Finset.sum_insert ha]
    exact int_add ι (int_term ι k χ a) ih

end Int

private theorem chi_neg_one {l M w : ℕ} (hl : l.Prime) {φ θ χ} (h : EDat l M w φ θ χ) : χ (-1) = φ (-1) := by
  have hM := h.one_lt
  have hw := h.prime
  have hN : 1 ≤ M * w := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) hw.ne_zero)
  have hcast : ((M * w - 1 : ℕ) : ZMod (M * w)) = -1 := by
    rw [Nat.cast_sub hN, ZMod.natCast_self, Nat.cast_one, zero_sub]
  have hM' : ((M * w - 1 : ℕ) : ZMod M) = -1 := by
    rw [Nat.cast_sub hN, Nat.cast_mul, ZMod.natCast_self, zero_mul, Nat.cast_one, zero_sub]
  have hw' : ((M * w - 1 : ℕ) : ZMod w) = -1 := by
    rw [Nat.cast_sub hN, Nat.cast_mul, ZMod.natCast_self, mul_zero, Nat.cast_one, zero_sub]
  have hmul := h.mul (M * w - 1)
  rw [hcast, hM', hw'] at hmul
  rw [hmul]
  have hl0 : l ≠ 0 := hl.ne_zero
  have h2 : θ (-1) ^ l = 1 := by
    rw [← MulChar.pow_apply' θ hl0, h.θpow, MulChar.one_apply isUnit_one.neg]
  have hodd : Odd l := (hl.eq_two_or_odd').resolve_left h.odd
  have h1 : θ (-1) * θ (-1) = 1 := by
    rw [← map_mul, neg_one_mul, neg_neg, map_one]
  rcases mul_self_eq_one_iff.mp h1 with h3 | h3
  · rw [h3, mul_one]
  · exfalso
    rw [h3, hodd.neg_one_pow] at h2
    norm_num at h2

private theorem coef_comb {N k : ℕ} [NeZero N] (E G : ModularForm (Gamma1 N) (k : ℤ)) (c : ℂ) (n : ℕ) :
    coef (E - c • G : ModularForm (Gamma1 N) (k : ℤ)) n = coef E n - c * coef G n := by
  have h1 : (1 : ℝ) ∈ ((Gamma1 N : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by simp
  unfold coef
  rw [ModularForm.coe_sub, ModularForm.qExpansion_sub one_pos h1 E (c • G), ModularForm.coe_smul,
    ModularForm.qExpansion_smul one_pos h1 c G]
  simp

private theorem slash_comb (k : ℕ) (E G : ℍ → ℂ) (c : ℂ) (γ : SL(2, ℤ)) :
    (E - c • G) ∣[(k : ℤ)] γ = E ∣[(k : ℤ)] γ - c • G ∣[(k : ℤ)] γ := by
  rw [sub_eq_add_neg, sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash,
    ModularForm.SL_smul_slash]

private theorem sig_cj (k : ℕ) {N : ℕ} (χ : DirichletCharacter ℂ N) (σ : ℂ ≃+* ℂ) (n : ℕ) :
    σ (sigChi k χ n) = sigChi k (cj σ χ) n := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [sigChi, cj, MulChar.ringHomComp_apply, map_sum]

private theorem cusp_comb {N k : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (E G : ModularForm (Gamma1 N) (k : ℤ))
    (hEc : HasChar k χ E) (hGc : HasChar k χ G) (hEv : VanOff N k E) (hGv : VanOff N k G) (hG0 : coef G 0 = 1) :
    ∃ f : CuspForm (Gamma1 N) (k : ℤ), HasChar k χ f ∧ ∀ n, coef f n = coef E n - coef E 0 * coef G n := by
  have hFc : HasChar k χ ⇑(E - coef E 0 • G) := by
    intro γ hγ
    rw [ModularForm.coe_sub, ModularForm.coe_smul, slash_comb, hEc γ hγ, hGc γ hγ, smul_sub,
      smul_comm (χ _) (coef E 0)]
  have hFv : VanOff N k ⇑(E - coef E 0 • G) := by
    intro γ hγ
    rw [ModularForm.coe_sub, ModularForm.coe_smul, slash_comb, sub_eq_add_neg]
    exact Filter.ZeroAtFilter.add (hEv γ hγ)
      (Filter.ZeroAtFilter.neg (Filter.ZeroAtFilter.smul (coef E 0) (hGv γ hγ)))
  have hF0 : coef ⇑(E - coef E 0 • G) 0 = 0 := by
    rw [coef_comb, hG0, mul_one, sub_self]
  obtain ⟨g, hg⟩ := cuspOf N k χ (E - coef E 0 • G) hFc hFv hF0
  refine ⟨g, ?_, fun n => ?_⟩
  · rw [hg]
    exact hFc
  · rw [hg]
    exact coef_comb E G (coef E 0) n

end UpperTheory.V.Z.Sym.Unl

theorem UpperTheory.V.Z.Sym.Unl.propEC :
    UpperTheory.V.Z.Sym.Unl.PropEC := by
  unfold UpperTheory.V.Z.Sym.Unl.PropEC
  intro l _ ι M w φ θ χ h
  have hM := h.one_lt
  have hw := h.prime
  have hl : l.Prime := Fact.out
  haveI : NeZero (M * w) := ⟨mul_ne_zero (by omega) hw.ne_zero⟩
  have hN3 : 3 ≤ M * w := by
    have := hw.two_le
    nlinarith
  have hlN : ¬ l ∣ M * w := by
    intro hd
    rcases (Nat.Prime.dvd_mul hl).mp hd with h1 | h1
    · exact h.cop h1
    · have h2 := h.dvd
      have h3 : l ∣ 1 := (Nat.dvd_add_right h2).mp (by rwa [Nat.sub_add_cancel hw.one_le])
      exact hl.one_lt.ne' (Nat.dvd_one.mp h3)
  obtain ⟨k₀, hk₀⟩ := unitFormC l h.odd ι (M * w) hN3 hlN
  refine ⟨max k₀ 3, fun k hk hφk => ?_⟩
  have hk1 : k₀ ≤ k := le_trans (le_max_left _ _) hk
  have hk3 : 3 ≤ k := le_trans (le_max_right _ _) hk
  have hχk : χ (-1) = (-1) ^ k := by
    rw [chi_neg_one hl h, hφk]
  have hprim : χ.IsPrimitive := ePrim l M w φ θ χ h
  have h1N : 1 < M * w := by omega
  obtain ⟨E, hEc, hEv, hEn, hE0⟩ := eisChi (M * w) k h1N hk3 χ hprim hχk
  obtain ⟨G, hGc, hGi, hGv, hG0, hGσ⟩ := hk₀ k hk1 χ hχk
  obtain ⟨f, hfc, hfn⟩ := cusp_comb χ E G hEc hGc hEv hGv hG0
  have hc : ‖ι.symm (coef E 0)‖ < 1 := constSmall l ι M w φ θ χ h k (by omega) (coef E 0) hE0
  have hGint : ∀ n, ‖ι.symm (coef G n)‖ ≤ 1 := hGi
  have hfcoef : ∀ n, 1 ≤ n → coef f n = sigChi k χ n - coef E 0 * coef G n := by
    intro n hn
    rw [hfn, hEn n hn]
  have hfint : UpperTheory.V.Sd.IntQ ι f := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hfn, hG0, mul_one, sub_self, map_zero, norm_zero]
      exact zero_le_one
    · rw [hfcoef n hn]
      exact int_sub ι (int_sig ι k χ n) (int_mul ι hc.le (hGint n))
  have hf1 : ‖ι.symm (coef f 1)‖ = 1 := by
    have hs1 : sigChi k χ 1 = 1 := by simp [sigChi]
    have hsm : ‖ι.symm (coef E 0 * coef G 1)‖ < 1 := small_mul ι hc (hGint 1)
    rw [hfcoef 1 le_rfl, map_sub, hs1, map_one, sub_eq_add_neg,
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm]
    · rw [norm_neg, norm_one]
      exact max_eq_left hsm.le
    · rw [norm_neg, norm_one]
      exact hsm.ne'
  have hCj : Cj k (M * w) χ f := by
    intro σ
    have hprim' := primCj (M * w) χ σ hprim
    have hχk' : (cj σ χ) (-1) = (-1) ^ k := by
      rw [MulChar.ringHomComp_apply, hχk]
      simp
    obtain ⟨E', hE'c, hE'v, hE'n, hE'0⟩ := eisChi (M * w) k h1N hk3 (cj σ χ) hprim' hχk'
    obtain ⟨G', hG'c, hG'v, hG'n⟩ := hGσ σ
    have hG'0 : coef G' 0 = 1 := by
      rw [hG'n, hG0, map_one]
    obtain ⟨f', hf'c, hf'n⟩ := cusp_comb (cj σ χ) E' G' hE'c hG'c hE'v hG'v hG'0
    have hc' : coef E' 0 = σ (coef E 0) :=
      constCj (M * w) k h1N χ hprim σ (coef E 0) (coef E' 0) hE0 hE'0
    refine ⟨f', hf'c, fun n hn => ?_⟩
    rw [hf'n, hE'n n hn, hc', hG'n, hfcoef n hn, map_sub, map_mul, sig_cj]
  refine eigLiftC l ι (M * w) k (by omega) χ f hfc hCj hfint hf1
    (fun p => 1 + χ p * (p : ℂ) ^ (k - 1)) ?_
  intro p hp
  have hone : ‖ι.symm (1 : ℂ)‖ ≤ 1 := by
    rw [map_one, norm_one]
  refine ⟨int_add ι hone (int_term ι k χ p), fun n hn => ?_⟩
  have hkey : (coef f (p * n) + χ p * (p : ℂ) ^ (k - 1) * (if p ∣ n then coef f (n / p) else 0)) -
      (1 + χ p * (p : ℂ) ^ (k - 1)) * coef f n =
      coef E 0 * -((coef G (p * n) + χ p * (p : ℂ) ^ (k - 1) *
        (if p ∣ n then coef G (n / p) else 0)) - (1 + χ p * (p : ℂ) ^ (k - 1)) * coef G n) := by
    have hpn : 1 ≤ p * n := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hp.ne_zero (by omega))
    have hs := sig_hecke k χ hp n hn
    rw [hfcoef _ hpn, hfcoef n hn]
    split_ifs at hs ⊢ with hd
    · have hnp : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd (by omega) hd) hp.pos
      rw [hfcoef _ hnp]
      linear_combination hs
    · linear_combination hs
  beta_reduce
  rw [hkey]
  refine small_mul ι hc ?_
  rw [map_neg, norm_neg]
  have hite : ‖ι.symm (if p ∣ n then coef G (n / p) else 0)‖ ≤ 1 := by
    split_ifs
    · exact hGint _
    · rw [map_zero, norm_zero]
      exact zero_le_one
  exact int_sub ι (int_add ι (hGint _) (int_mul ι (int_term ι k χ p) hite))
    (int_mul ι (int_add ι hone (int_term ι k χ p)) (hGint n))
