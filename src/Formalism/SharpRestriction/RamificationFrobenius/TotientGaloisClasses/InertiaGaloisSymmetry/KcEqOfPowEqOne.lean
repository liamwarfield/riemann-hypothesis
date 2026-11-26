module

public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.DecompTypeI
public import Formalism.FrobeniusOrbits.HostCorollaries

@[expose] public section

section -- merged from Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.KcBase
open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors

noncomputable section

namespace Formalism.HC.Der

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

variable {φ : Frame} (H : HostRaw φ)

theorem kc_sqd_ne_zero : H.sqd ≠ 0 := by
  intro h
  have h1 := H.sqd_sq
  rw [h] at h1
  have hd : (H.d : H.E) = 0 := by linear_combination h1
  have hd0 : H.d = 0 := by exact_mod_cast hd
  have hc := H.QS_coprime
  rw [hd0, mul_zero, Nat.coprime_zero_right] at hc
  have ht := H.tower_dvd
  rw [hc] at ht
  have h2 : 2 ^ (φ.e + 2) ≤ 1 := Nat.le_of_dvd one_pos ht
  have h3 : 2 ^ 1 ≤ 2 ^ (φ.e + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem kc_mem_Psi_iff (σ : H.E ≃ₐ[ℚ] H.E) : H.gal σ ∈ φ.Psi ↔ σ H.sqd = H.sqd := by
  rw [Frame.Psi, MonoidHom.mem_ker, H.gal_sqd]
  simp only [Frame.chD, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_fst, MonoidHom.coe_snd]
  rcases Int.units_eq_one_or ((H.gal σ).1.2) with h | h <;> rw [h]
  · simp
  · constructor
    · intro h1
      exact absurd h1 (by decide)
    · intro h1
      exfalso
      have h2 : (2 : H.E) * H.sqd = 0 := by
        push_cast at h1
        linear_combination -h1
      rcases mul_eq_zero.mp h2 with h3 | h3
      · norm_num at h3
      · exact kc_sqd_ne_zero H h3

theorem kc_gal_conj : H.gal H.conj = φ.cc := by
  unfold HostRaw.conj
  exact H.gal.apply_symm_apply _

theorem kc_sqd_mem : H.sqd ∈ H.K := by
  unfold HostRaw.K
  exact IntermediateField.mem_adjoin_simple_self ℚ H.sqd

theorem kc_restrict_mem_Psi (σ : H.E ≃ₐ[H.K] H.E) : H.gal (σ.restrictScalars ℚ) ∈ φ.Psi := by
  rw [kc_mem_Psi_iff]
  exact σ.commutes ⟨H.sqd, kc_sqd_mem H⟩

theorem kc_fixK (σ : H.E ≃ₐ[ℚ] H.E) (hσ : H.gal σ ∈ φ.Psi) (x : H.K) : σ (x : H.E) = x := by
  have hs : H.sqd ∈ IntermediateField.fixedField (MulAction.stabilizer (H.E ≃ₐ[ℚ] H.E) H.sqd) :=
    (IntermediateField.mem_fixedField_iff _ _).mpr fun f hf => hf
  have hle : H.K ≤ IntermediateField.fixedField (MulAction.stabilizer (H.E ≃ₐ[ℚ] H.E) H.sqd) := by
    unfold HostRaw.K
    exact IntermediateField.adjoin_simple_le_iff.mpr hs
  have hx := hle x.2
  rw [IntermediateField.mem_fixedField_iff] at hx
  exact hx σ ((kc_mem_Psi_iff H σ).mp hσ)

theorem kc_cc_not_mem : φ.cc ∉ φ.Psi := by
  simp only [Frame.Psi, MonoidHom.mem_ker, Frame.chD, Frame.cc, c0, MonoidHom.coe_comp, Function.comp_apply,
    MonoidHom.coe_fst, MonoidHom.coe_snd]
  decide

theorem kc_iod_not_mem : φ.iod ∉ φ.Psi := by
  simp only [Frame.Psi, MonoidHom.mem_ker, Frame.chD, Frame.iod, MonoidHom.coe_comp, Function.comp_apply,
    MonoidHom.coe_fst, MonoidHom.coe_snd]
  decide

theorem kc_ne_bot {M : Type} [Field M] [NumberField M] (p : ℕ) (hp : p.Prime) (P : Ideal (𝓞 M))
    [P.LiesOver (span {(p : ℤ)})] : P ≠ ⊥ := by
  have hne : span {(p : ℤ)} ≠ ⊥ := by simp [hp.ne_zero]
  exact Ideal.ne_bot_of_liesOver_of_ne_bot hne P

theorem kc_two_dvd : 2 ∣ H.QS := (dvd_pow_self 2 (by omega)).trans H.tower_dvd

theorem kc_stab_of_inertia {G S : Type*} [Group G] [CommRing S] [MulSemiringAction G S] (g : G) (P : Ideal S)
    (h : ∀ x : S, g • x - x ∈ P) : g ∈ MulAction.stabilizer G P := by
  rw [MulAction.mem_stabilizer_iff]
  ext x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  have h1 := h (g⁻¹ • x)
  rw [smul_inv_smul] at h1
  constructor
  · intro hx
    simpa using P.add_mem h1 hx
  · intro hx
    simpa using P.sub_mem hx h1

theorem splitK : ∀ p : ℕ, p.Prime →
    ((primesOver (span {(p : ℤ)}) (𝓞 H.K)).ncard = 2 ↔ (p = 2 ∨ (p ≠ 2 ∧ jacobiSym (-(H.d : ℤ)) p = 1))) :=
  fun p hp => SplitK.clause (L := H.E) (b := H.sqd) H.hyp.2.1 (by have := H.hyp.2.2.2.1; omega) H.sqd_sq p hp

variable (C : HostCore H)
include C

theorem ordinary : ∀ (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})],
    (∀ σ τ : H.E ≃ₐ[ℚ] H.E, τ ∈ MulAction.stabilizer _ P → (H.gal (σ * τ) ∈ φ.Psi ↔ H.gal σ ∈ φ.Psi)) ↔
      (primesOver (span {(p : ℤ)}) (𝓞 H.K)).ncard = 2 := by
  intro p hpf P _ _
  have hp : p.Prime := hpf.out
  have hred : (∀ σ τ : H.E ≃ₐ[ℚ] H.E, τ ∈ MulAction.stabilizer _ P →
      (H.gal (σ * τ) ∈ φ.Psi ↔ H.gal σ ∈ φ.Psi)) ↔
      ∀ τ : H.E ≃ₐ[ℚ] H.E, τ ∈ MulAction.stabilizer _ P → H.gal τ ∈ φ.Psi := by
    constructor
    · intro h τ hτ
      have := h 1 τ hτ
      rw [one_mul, map_one] at this
      exact this.mpr (one_mem _)
    · intro h σ τ hτ
      rw [map_mul]
      exact Subgroup.mul_mem_cancel_right _ (h τ hτ)
  rw [hred, splitK H p hp]
  by_cases h1 : p ∣ H.QS * H.q
  · refine iff_of_true (fun τ hτ => C.decomp_typeI p hp h1 P τ hτ) ?_
    by_cases h2 : p = 2
    · exact Or.inl h2
    · refine Or.inr ⟨h2, ?_⟩
      rcases hp.dvd_mul.mp h1 with h3 | h3
      · exact H.QS_split p hp h2 h3
      · rw [(Nat.prime_dvd_prime_iff_eq hp H.hyp.1).mp h3]
        exact H.hyp.2.2.2.2
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact h1 ((kc_two_dvd H).mul_right _)
  by_cases hpd : p = H.d
  · subst hpd
    refine iff_of_false (fun h => ?_) ?_
    · obtain ⟨σ, hσ⟩ := H.gal.surjective φ.iod
      have h3 := h σ (kc_stab_of_inertia σ P ((C.inertia_d P σ).mpr (Or.inr hσ)))
      rw [hσ] at h3
      exact kc_iod_not_mem h3
    · rintro (h | ⟨-, h⟩)
      · exact hp2 h
      · have : NeZero H.d := ⟨hp.ne_zero⟩
        have h0 : jacobiSym (-(H.d : ℤ)) H.d = 0 :=
          jacobiSym.eq_zero_iff_not_coprime.mpr (by simpa using hp.ne_one)
        omega
  · have hN : ¬ p ∣ H.condN := fun h => by
      rcases hp.dvd_mul.mp h with h3 | h3
      · exact h1 h3
      · exact hpd ((Nat.prime_dvd_prime_iff_eq hp H.hyp.2.1).mp h3)
    obtain ⟨⟨F, hF⟩, -, f3, f4⟩ := C.frob p hN P
    have hj := (f3 F hF).2.1
    have hFP : H.gal F ∈ φ.Psi ↔ (p = 2 ∨ (p ≠ 2 ∧ jacobiSym (-(H.d : ℤ)) p = 1)) := by
      rw [Frame.mem_Psi_iff, ← hj, or_iff_right hp2, and_iff_right hp2]
      exact (Units.val_eq_one).symm
    rw [← hFP]
    constructor
    · intro h
      exact h F hF.mem_stabilizer
    · intro hFm τ hτ
      obtain ⟨k, ρ, hρ, rfl⟩ := Decomp.stab_eq_inertia_mul p P F τ hF hτ
      rw [(f4 ρ).mp hρ, one_mul, map_pow]
      exact Subgroup.pow_mem _ hFm k

theorem kc_conj_eq : haveI := C.cm; (IsCMField.complexConj H.E).restrictScalars ℚ = H.conj := by
  haveI := C.cm
  apply H.gal.injective
  rw [kc_gal_conj]
  let ψ : H.E →+* ℂ := (IsAlgClosed.lift : H.E →ₐ[ℚ] ℂ).toRingHom
  exact (C.conj_iff ψ _).mp (fun x => IsCMField.complexEmbedding_complexConj H.E ψ x)

theorem kc_unr : haveI := C.cm; ∀ P : Ideal (𝓞 H.E), P.IsPrime → P ≠ ⊥ →
    ¬ ∀ x : 𝓞 H.E, IsCMField.complexConj H.E • x - x ∈ P := by
  haveI := C.cm
  intro P hP hne h
  apply C.unramEF P hP hne
  intro x
  have e : H.conj • x = IsCMField.complexConj H.E • x := by
    rw [← kc_conj_eq H C]
    rfl
  rw [e]
  exact h x

theorem eta : (∀ 𝔭 : Ideal (𝓞 H.F), 𝔭.IsPrime → 𝔭 ≠ ⊥ →
      (primesOver 𝔭 (𝓞 H.E)).ncard = 2 ∨ ((primesOver 𝔭 (𝓞 H.E)).ncard = 1 ∧ 𝔭.inertiaDegIn (𝓞 H.E) = 2)) ∧
    (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ H.condN →
      ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E), IsArithFrobAt ℤ σ P →
        (H.etaF (P.comap (algebraMap (𝓞 H.F) (𝓞 H.E))) = -1 ↔ φ.cc ∈ Subgroup.zpowers (H.gal σ))) ∧
    (∀ (p : ℕ) [Fact p.Prime], p ∣ H.condN →
      ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})],
        H.etaF (P.comap (algebraMap (𝓞 H.F) (𝓞 H.E))) = 1) := by
  have := C.cm
  have hunr := kc_unr H C
  have hsm : ∀ P : Ideal (𝓞 H.E), IsCMField.complexConj H.E • P = H.conj • P := fun P => by
    rw [← kc_conj_eq H C]
    rfl
  have hetaiff : ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime], P ≠ ⊥ →
      (H.etaF (P.comap (algebraMap (𝓞 H.F) (𝓞 H.E))) = 1 ↔ H.conj • P ≠ P) := by
    intro P _ hP0
    have hk := Eta.ncard_eq_two_iff H.E hunr P hP0
    rw [hsm] at hk
    unfold HostRaw.etaF
    change (if (primesOver (P.under (𝓞 H.F)) (𝓞 H.E)).ncard = 2 then (1 : ℤ) else -1) = 1 ↔ _
    rw [← hk]
    split_ifs with h2
    · exact iff_of_true rfl h2
    · exact iff_of_false (by decide) h2
  refine ⟨fun 𝔭 hp h0 => ?_, ?_, ?_⟩
  · have := hp
    exact Eta.split_or_inert H.E hunr 𝔭 h0
  · intro p hpf hN P _ _ σ hσ
    have hP0 := kc_ne_bot p hpf.out P
    have hm1 : H.etaF (P.comap (algebraMap (𝓞 H.F) (𝓞 H.E))) = -1 ↔ H.conj • P = P := by
      have h1 := hetaiff P hP0
      have hval : H.etaF (P.comap (algebraMap (𝓞 H.F) (𝓞 H.E))) = 1 ∨
          H.etaF (P.comap (algebraMap (𝓞 H.F) (𝓞 H.E))) = -1 := by
        unfold HostRaw.etaF; split_ifs <;> simp
      constructor
      · intro hm
        by_contra hc
        rw [h1.mpr hc] at hm
        exact absurd hm (by decide)
      · intro hfix
        rcases hval with hv | hv
        · exact absurd hfix (h1.mp hv)
        · exact hv
    rw [hm1]
    constructor
    · intro hfix
      have hst : H.conj ∈ MulAction.stabilizer _ P := hfix
      obtain ⟨k, ρ, hρ, hρeq⟩ := Decomp.stab_eq_inertia_mul p P σ H.conj hσ hst
      rw [((C.frob p hN P).2.2.2 ρ).mp hρ, one_mul] at hρeq
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [zpow_natCast, ← map_pow, ← hρeq, kc_gal_conj]⟩
    · intro hg
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
      have hσc : σ ^ k = H.conj := H.gal.injective (by rw [map_zpow, hk, kc_gal_conj])
      rw [← hσc]
      exact Subgroup.zpow_mem _ hσ.mem_stabilizer k
  · intro p hpf hN P _ _
    exact (hetaiff P (kc_ne_bot p hpf.out P)).mpr (C.decompConj p hpf.out hN P)

end Formalism.HC.Der

end
end

section -- merged from Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.KcEqOfPowEqOne
open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors

noncomputable section

namespace Formalism.HC.Der

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

variable {φ : Frame} (H : HostRaw φ)

theorem kc_eq_of_pow_eq_one {S : Type*} [CommRing S] [IsDomain S] (P : Ideal S) [hP : P.IsPrime] {m : ℕ} (hm : (m : S) ∉ P)
    {x y : S} (hx : x ^ m = 1) (hy : y ^ m = 1) (hxy : x - y ∈ P) : x = y := by
  by_contra hne
  have h1 := geom_sum₂_mul x y m
  rw [hx, hy, sub_self, mul_eq_zero, sub_eq_zero] at h1
  have h2 := congrArg (Ideal.Quotient.mk P) (h1.resolve_right hne)
  have h3 : Ideal.Quotient.mk P x = Ideal.Quotient.mk P y := Ideal.Quotient.eq.mpr hxy
  rw [RingHom.map_geom_sum₂, h3, geom_sum₂_self, map_zero, ← map_pow, ← map_natCast (Ideal.Quotient.mk P), ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem] at h2
  rcases hP.mem_or_mem h2 with h4 | h4
  · exact hm h4
  · have h5 : y ∈ P := hP.mem_of_pow_mem _ h4
    have hm0 : m ≠ 0 := by rintro rfl; exact hm (by simp)
    have h6 := P.pow_mem_of_mem h5 m (Nat.pos_of_ne_zero hm0)
    rw [hy] at h6
    exact hP.ne_top ((Ideal.eq_top_iff_one P).mpr h6)

variable (C : HostCore H)
include C

theorem kc_no_root_d (η : H.E) (hη : IsPrimitiveRoot η H.d) : False := by
  have : Fact H.d.Prime := ⟨H.hyp.2.1⟩
  have := H.galois
  obtain ⟨⟨Q, hQp, hQl⟩⟩ : Nonempty ((span {(H.d : ℤ)}).primesOver (𝓞 H.E)) := inferInstance
  have hge := Mu.mu_le_ram H.d Q (H.d - 1) (Mu.mu_mem_pow H.d Q η hη)
  have hd := H.hyp.2.2.2.1
  have hle := Mu.mu_card_le_two (L := H.E) H.gal H.gal.injective φ.iod (Q.inertia Gal(H.E/ℚ))
    (fun ρ hρ => (C.inertia_d Q ρ).mp (AddSubgroup.mem_inertia.mp hρ))
  rw [odd_card H.E H.d Q] at hle
  omega

theorem kc_iod_fix (σ : H.E ≃ₐ[ℚ] H.E) (hσ : H.gal σ = φ.iod) (x : H.E) (hx : ∃ m : ℕ, 0 < m ∧ x ^ m = 1) : σ x = x := by
  obtain ⟨n, hn, hxn⟩ := hx
  have hfin : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, hxn⟩
  have hmpos : 0 < orderOf x := orderOf_pos_iff.2 hfin
  have hprim : IsPrimitiveRoot x (orderOf x) := IsPrimitiveRoot.orderOf x
  have hd : ¬ H.d ∣ orderOf x := by
    rintro ⟨k, hk⟩
    exact kc_no_root_d H C _ (hprim.pow hmpos (by rw [hk, mul_comm]))
  have : Fact H.d.Prime := ⟨H.hyp.2.1⟩
  obtain ⟨⟨P, hPp, hPl⟩⟩ : Nonempty ((span {(H.d : ℤ)}).primesOver (𝓞 H.E)) := inferInstance
  have hin := (C.inertia_d P σ).mpr (Or.inr hσ)
  have hint : IsIntegral ℤ x := hprim.isIntegral hmpos
  let X : 𝓞 H.E := ⟨x, hint⟩
  have hX : X ^ orderOf x = 1 := by
    apply RingOfIntegers.ext
    have : ((X ^ orderOf x : 𝓞 H.E) : H.E) = (X : H.E) ^ orderOf x := by push_cast; rfl
    rw [this]
    exact hprim.pow_eq_one
  have hX' : (σ • X) ^ orderOf x = 1 := by rw [← smul_pow', hX, smul_one]
  have hm : ((orderOf x : ℕ) : 𝓞 H.E) ∉ P := by
    intro h0
    have h1 := (odd_intCast_mem_iff H.d P ((orderOf x : ℕ) : ℤ)).mp (by exact_mod_cast h0)
    exact hd (by exact_mod_cast h1)
  have := kc_eq_of_pow_eq_one P hm hX' hX (hin X)
  exact congrArg (fun y : 𝓞 H.E => (y : H.E)) this

theorem kc_conj_mul_self (x : H.E) (hx : ∃ m : ℕ, 0 < m ∧ x ^ m = 1) : x * H.conj x = 1 := by
  obtain ⟨n, hn, hxn⟩ := hx
  let ψ : H.E →+* ℂ := Classical.choice inferInstance
  apply ψ.injective
  have h1 : ‖ψ x‖ = 1 := Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hxn, map_one]) hn.ne'
  rw [map_mul, (C.conj_iff ψ H.conj).mpr (kc_gal_conj H), Complex.mul_conj', h1, map_one]
  simp

theorem norm_mu : ∀ x : H.E, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → Algebra.norm H.K x = 1 := by
  classical
  intro x hx
  have := H.galois
  have : IsGalois H.K H.E := IsGalois.tower_top_of_isGalois ℚ _ _
  obtain ⟨ι, hι⟩ := H.gal.surjective φ.iod
  set s₀ := H.conj * ι with hs₀
  have hg : H.gal s₀ = φ.sg := by
    rw [hs₀, map_mul, kc_gal_conj, hι]
    exact Prod.ext (show c0 * ((1, -1) : G0) = (-1, 1) by decide) (mul_one _)
  have hΨ : H.gal s₀ ∈ φ.Psi := by rw [hg]; rfl
  let s : H.E ≃ₐ[H.K] H.E := AlgEquiv.ofRingEquiv (f := s₀.toRingEquiv) (fun y => kc_fixK H s₀ hΨ y)
  have hs : ∀ y, s y = s₀ y := fun _ => rfl
  have hsx : x * s x = 1 := by
    rw [hs, hs₀, AlgEquiv.mul_apply, kc_iod_fix H C ι hι x hx]
    exact kc_conj_mul_self H C x hx
  have hss0 : s₀ * s₀ = 1 := by
    apply H.gal.injective
    rw [map_mul, hg, map_one]
    exact Prod.ext (show ((-1, 1) : G0) * (-1, 1) = 1 by decide) (mul_one _)
  have hss : s * s = 1 := AlgEquiv.ext fun y => DFunLike.congr_fun hss0 y
  have hs1 : s ≠ 1 := by
    intro h1
    have h2 : s₀ = 1 := AlgEquiv.ext fun y => DFunLike.congr_fun h1 y
    rw [h2, map_one] at hg
    exact absurd (congrArg (fun g : φ.GG => g.1) hg) (show ¬ (1 : G0) = (-1, 1) by decide)
  apply (algebraMap H.K H.E).injective
  rw [Algebra.norm_eq_prod_automorphisms, map_one]
  refine Finset.prod_involution (fun σ _ => σ * s) (fun σ _ => ?_) (fun σ _ _ => ?_) (fun _ _ => Finset.mem_univ _)
    (fun σ _ => ?_)
  · rw [AlgEquiv.mul_apply, ← map_mul, hsx, map_one]
  · exact fun h1 => hs1 (mul_eq_left.mp h1)
  · rw [mul_assoc, hss, mul_one]

end Formalism.HC.Der

end
end

section -- merged from Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.KcDiffSmulMem
open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors

noncomputable section

namespace Formalism.HC.Der

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

variable {φ : Frame} (H : HostRaw φ)

theorem kc_comm_of (σ : H.E ≃ₐ[ℚ] H.E) (τ : H.E ≃ₐ[H.K] H.E) (x : H.E) : σ (τ x) = τ (σ x) := by
  have h : σ * τ.restrictScalars ℚ = τ.restrictScalars ℚ * σ :=
    H.gal.injective (by rw [map_mul, map_mul, mul_comm])
  have := congrArg (fun f : H.E ≃ₐ[ℚ] H.E => f x) h
  simpa only [AlgEquiv.mul_apply, AlgEquiv.restrictScalars_apply] using this

theorem kc_comm_symm (σ : H.E ≃ₐ[ℚ] H.E)
    (hc : ∀ (τ : H.E ≃ₐ[H.K] H.E) (x : H.E), σ (τ x) = τ (σ x))
    (τ : H.E ≃ₐ[H.K] H.E) (x : H.E) : σ.symm (τ x) = τ (σ.symm x) := by
  apply σ.injective
  rw [AlgEquiv.apply_symm_apply, hc, AlgEquiv.apply_symm_apply]

theorem kc_sum_comm (σ : H.E ≃ₐ[ℚ] H.E)
    (hc : ∀ (τ : H.E ≃ₐ[H.K] H.E) (x : H.E), σ (τ x) = τ (σ x)) (w : H.E) :
    σ (∑ τ : H.E ≃ₐ[H.K] H.E, τ w) = ∑ τ : H.E ≃ₐ[H.K] H.E, τ (σ w) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun τ _ => hc τ w

theorem kc_one_ne : (1 : FractionalIdeal (𝓞 H.E)⁰ H.E) ≠ 0 := one_ne_zero

private theorem mem_one_fractionalIdeal_iff_isIntegral (t : H.E) : t ∈ (1 : FractionalIdeal (𝓞 H.E)⁰ H.E) ↔ IsIntegral ℤ t := by
  rw [FractionalIdeal.mem_one_iff]
  constructor
  · rintro ⟨y, rfl⟩
    exact NumberField.RingOfIntegers.isIntegral_coe y
  · intro h
    exact ⟨⟨t, h⟩, rfl⟩

private theorem isIntegral_algEquiv_apply_iff (σ : H.E ≃ₐ[ℚ] H.E) (t : H.E) : IsIntegral ℤ (σ t) ↔ IsIntegral ℤ t :=
  isIntegral_algEquiv (σ.restrictScalars ℤ)

theorem kc_mem_dual_iff (y : H.E) :
    y ∈ FractionalIdeal.dual (𝓞 H.K) H.K (1 : FractionalIdeal (𝓞 H.E)⁰ H.E) ↔
      ∀ x : 𝓞 H.E, IsIntegral ℤ (∑ τ : H.E ≃ₐ[H.K] H.E, τ (y * x)) := by
  haveI := H.galois
  rw [FractionalIdeal.mem_dual (kc_one_ne H)]
  have key : ∀ w : H.E, Algebra.trace H.K H.E w ∈ (algebraMap (𝓞 H.K) H.K).range ↔
      IsIntegral ℤ (∑ τ : H.E ≃ₐ[H.K] H.E, τ w) := by
    intro w
    rw [← trace_eq_sum_automorphisms, isIntegral_algebraMap_iff ]
    constructor
    · rintro ⟨a, ha⟩
      rw [← ha]
      exact NumberField.RingOfIntegers.isIntegral_coe a
    · intro h
      exact ⟨⟨_, h⟩, rfl⟩
  constructor
  · intro h x
    rw [← key]
    have := h _ ((mem_one_fractionalIdeal_iff_isIntegral H _).mpr (NumberField.RingOfIntegers.isIntegral_coe x))
    rwa [Algebra.traceForm_apply] at this
  · intro h a ha
    rw [mem_one_fractionalIdeal_iff_isIntegral] at ha
    rw [Algebra.traceForm_apply, key]
    exact h ⟨a, ha⟩

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

theorem kc_mem_diff_iff (z : 𝓞 H.E) :
    z ∈ differentIdeal (𝓞 H.K) (𝓞 H.E) ↔
      ∀ y : H.E, (∀ x : 𝓞 H.E, IsIntegral ℤ (∑ τ : H.E ≃ₐ[H.K] H.E, τ (y * x))) →
        IsIntegral ℤ ((z : H.E) * y) := by
  have hd : FractionalIdeal.dual (𝓞 H.K) H.K (1 : FractionalIdeal (𝓞 H.E)⁰ H.E) ≠ 0 := by
    simpa [FractionalIdeal.dual_eq_zero_iff] using kc_one_ne H
  have e1 : z ∈ differentIdeal (𝓞 H.K) (𝓞 H.E) ↔
      (z : H.E) ∈ ((differentIdeal (𝓞 H.K) (𝓞 H.E) : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E) := by
    rw [FractionalIdeal.mem_coeIdeal]
    constructor
    · intro h
      exact ⟨z, h, rfl⟩
    · rintro ⟨w, hw, e⟩
      have : w = z := NumberField.RingOfIntegers.ext e
      rwa [← this]
  rw [e1, coeIdeal_differentIdeal (𝓞 H.K) H.K H.E (𝓞 H.E), FractionalIdeal.mem_inv_iff hd]
  simp only [kc_mem_dual_iff, mem_one_fractionalIdeal_iff_isIntegral]

theorem kc_dual_smul (σ : H.E ≃ₐ[ℚ] H.E)
    (hc : ∀ (τ : H.E ≃ₐ[H.K] H.E) (x : H.E), σ (τ x) = τ (σ x)) (y : H.E)
    (hy : ∀ x : 𝓞 H.E, IsIntegral ℤ (∑ τ : H.E ≃ₐ[H.K] H.E, τ (y * x))) :
    ∀ x : 𝓞 H.E, IsIntegral ℤ (∑ τ : H.E ≃ₐ[H.K] H.E, τ (σ y * x)) := by
  intro x
  have hx := hy (σ⁻¹ • x)
  have hx' : σ ((σ⁻¹ • x : 𝓞 H.E) : H.E) = (x : H.E) := by
    show σ (σ⁻¹ (x : H.E)) = x
    rw [AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
  have e : ∑ τ : H.E ≃ₐ[H.K] H.E, τ (σ y * x) =
      σ (∑ τ : H.E ≃ₐ[H.K] H.E, τ (y * ((σ⁻¹ • x : 𝓞 H.E) : H.E))) := by
    rw [kc_sum_comm H σ hc]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [map_mul σ, hx']
  rw [e, isIntegral_algEquiv_apply_iff]
  exact hx

theorem kc_diff_smul_mem (σ : H.E ≃ₐ[ℚ] H.E)
    (hc : ∀ (τ : H.E ≃ₐ[H.K] H.E) (x : H.E), σ (τ x) = τ (σ x)) (z : 𝓞 H.E)
    (hz : z ∈ differentIdeal (𝓞 H.K) (𝓞 H.E)) : σ • z ∈ differentIdeal (𝓞 H.K) (𝓞 H.E) := by
  rw [kc_mem_diff_iff] at hz ⊢
  intro y hy
  have hy' := kc_dual_smul H σ.symm (kc_comm_symm H σ hc) y hy
  have h1 := hz (σ.symm y) hy'
  rw [← isIntegral_algEquiv_apply_iff H σ, map_mul, AlgEquiv.apply_symm_apply] at h1
  have e : ((σ • z : 𝓞 H.E) : H.E) = σ (z : H.E) := rfl
  rw [e]
  exact h1

theorem kc_diff_smul_le (σ : H.E ≃ₐ[ℚ] H.E)
    (hc : ∀ (τ : H.E ≃ₐ[H.K] H.E) (x : H.E), σ (τ x) = τ (σ x)) :
    σ • differentIdeal (𝓞 H.K) (𝓞 H.E) ≤ differentIdeal (𝓞 H.K) (𝓞 H.E) := by
  intro x hx
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hx
  have := kc_diff_smul_mem H σ hc _ hx
  rwa [smul_inv_smul] at this

theorem kc_diff_smul_eq (σ : H.E ≃ₐ[ℚ] H.E) :
    σ • differentIdeal (𝓞 H.K) (𝓞 H.E) = differentIdeal (𝓞 H.K) (𝓞 H.E) := by
  apply le_antisymm (kc_diff_smul_le H σ (kc_comm_of H σ))
  intro x hx
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  exact kc_diff_smul_mem H σ⁻¹ (kc_comm_of H σ⁻¹) x hx

theorem kc_mem_one_iff (t : H.E) :
    t ∈ (1 : FractionalIdeal (𝓞 H.E)⁰ H.E) ↔ IsIntegral ℤ t := by
  rw [FractionalIdeal.mem_one_iff]
  constructor
  · rintro ⟨y, rfl⟩
    exact NumberField.RingOfIntegers.isIntegral_coe y
  · intro h
    exact ⟨⟨t, h⟩, rfl⟩

theorem kc_integ_iff (σ : H.E ≃ₐ[ℚ] H.E) (t : H.E) :
    IsIntegral ℤ (σ t) ↔ IsIntegral ℤ t :=
  isIntegral_algEquiv (σ.restrictScalars ℤ)

theorem kc_smul_ne_bot (σ : H.E ≃ₐ[ℚ] H.E) (B : Ideal (𝓞 H.E))
    (hB : B ≠ ⊥) : σ • B ≠ ⊥ := by
  intro h
  apply hB
  rw [← inv_smul_smul σ B, h]
  ext x
  simp [Ideal.mem_pointwise_smul_iff_inv_smul_mem]

theorem kc_mem_inv_smul (σ : H.E ≃ₐ[ℚ] H.E) (B : Ideal (𝓞 H.E))
    (hB : B ≠ ⊥) (y : H.E) :
    σ y ∈ ((σ • B : Ideal (𝓞 H.E)) :
        FractionalIdeal (𝓞 H.E)⁰ H.E)⁻¹ ↔
      y ∈ ((B : FractionalIdeal (𝓞 H.E)⁰ H.E))⁻¹ := by
  have hB' : (B : FractionalIdeal (𝓞 H.E)⁰ H.E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hB
  have hσB : ((σ • B : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr (kc_smul_ne_bot H σ B hB)
  rw [FractionalIdeal.mem_inv_iff hσB, FractionalIdeal.mem_inv_iff hB']
  constructor
  · intro h w hw
    rw [FractionalIdeal.mem_coeIdeal] at hw
    obtain ⟨b, hb, rfl⟩ := hw
    have hb' : σ • b ∈ σ • B := by
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_smul_smul]
      exact hb
    have := h (algebraMap (𝓞 H.E) H.E (σ • b)) (by rw [FractionalIdeal.mem_coeIdeal]; exact ⟨σ • b, hb', rfl⟩)
    rw [kc_mem_one_iff] at this ⊢
    rw [show algebraMap (𝓞 H.E) H.E (σ • b) = σ (algebraMap (𝓞 H.E) H.E b) from rfl, ← map_mul,
      kc_integ_iff] at this
    exact this
  · intro h w hw
    rw [FractionalIdeal.mem_coeIdeal] at hw
    obtain ⟨b, hb, rfl⟩ := hw
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hb
    have := h (algebraMap (𝓞 H.E) H.E (σ⁻¹ • b)) (by rw [FractionalIdeal.mem_coeIdeal]; exact ⟨σ⁻¹ • b, hb, rfl⟩)
    rw [kc_mem_one_iff] at this ⊢
    have e : σ (algebraMap (𝓞 H.E) H.E (σ⁻¹ • b)) = algebraMap (𝓞 H.E) H.E b := by
      show σ (σ⁻¹ (b : H.E)) = b
      rw [AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
    rw [← kc_integ_iff H σ, map_mul, e] at this
    exact this

theorem unimodular : ∀ 𝔟 : Ideal (𝓞 H.E), differentIdeal (𝓞 H.K) (𝓞 H.E) = 𝔟 * (H.conj • 𝔟) → ∀ x : H.E,
    x ∈ ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E)⁻¹) ↔
      ∀ y ∈ ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E)⁻¹),
        Algebra.trace H.K H.E (x * H.conj y) ∈ (algebraMap (𝓞 H.K) H.K).range := by
  intro B hdiff x
  have hD0 := differentIdeal_ne_bot (A := 𝓞 H.K) (B := 𝓞 H.E)
  have hB : B ≠ ⊥ := by
    rintro rfl
    rw [← Ideal.zero_eq_bot, zero_mul] at hdiff
    exact hD0 hdiff
  have hJ : ((H.conj • B : Ideal (𝓞 H.E)) :
      FractionalIdeal (𝓞 H.E)⁰ H.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr (kc_smul_ne_bot H H.conj B hB)
  have hdual : FractionalIdeal.dual (𝓞 H.K) H.K
      (((H.conj • B : Ideal (𝓞 H.E)) :
        FractionalIdeal (𝓞 H.E)⁰ H.E)⁻¹) =
      ((B : FractionalIdeal (𝓞 H.E)⁰ H.E))⁻¹ := by
    rw [FractionalIdeal.dual_eq_mul_inv, inv_inv,
      ← inv_inv (FractionalIdeal.dual (𝓞 H.K) H.K
        (1 : FractionalIdeal (𝓞 H.E)⁰ H.E)),
      ← coeIdeal_differentIdeal (𝓞 H.K) H.K H.E (𝓞 H.E),
      hdiff, FractionalIdeal.coeIdeal_mul, mul_inv, mul_assoc, inv_mul_cancel₀ hJ, mul_one]
  have hx : x ∈ ((B : FractionalIdeal (𝓞 H.E)⁰ H.E))⁻¹ ↔
      x ∈ FractionalIdeal.dual (𝓞 H.K) H.K
        (((H.conj • B : Ideal (𝓞 H.E)) :
          FractionalIdeal (𝓞 H.E)⁰ H.E)⁻¹) := by
    rw [hdual]
  rw [hx, FractionalIdeal.mem_dual (inv_ne_zero hJ)]
  constructor
  · intro hh y hy
    have := hh (H.conj y) ((kc_mem_inv_smul H H.conj B hB y).mpr hy)
    rwa [Algebra.traceForm_apply] at this
  · intro hh z hz
    rw [Algebra.traceForm_apply]
    have hz' : H.conj (H.conj.symm z) = z := H.conj.apply_symm_apply z
    rw [← hz'] at hz ⊢
    exact hh _ ((kc_mem_inv_smul H H.conj B hB _).mp hz)

end Formalism.HC.Der

end
end
