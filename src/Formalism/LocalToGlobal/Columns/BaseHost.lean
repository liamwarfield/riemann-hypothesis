module

public import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
public import Formalism.LocalToGlobal.Divisibility.CoeffLemmas
public import Formalism.LocalToGlobal.UnitaryNorms.RealPl
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators

@[expose] public section

section -- merged from Formalism.LocalToGlobal.UnitaryNorms.ExistsCycAct
section -- merged from Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostRam
open NumberField IntermediateField Ideal
open scoped Pointwise

noncomputable section

namespace Formalism.HC

open Formalism.FrobeniusOrbits

theorem exists_unit_val {N : ℕ} [NeZero N] {x : ℕ} (hx : Nat.Coprime x N) :
    ∃ u : (ZMod N)ˣ, (u : ZMod N).val ≡ x [MOD N] :=
  ⟨ZMod.unitOfCoprime x hx, by rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]; exact Nat.mod_modEq x N⟩

theorem exists_unit_crt {N a b : ℕ} [NeZero N] (hN : N = a * b) (hab : Nat.Coprime a b) {x y : ℕ}
    (hx : Nat.Coprime x a) (hy : Nat.Coprime y b) :
    ∃ u : (ZMod N)ˣ, (u : ZMod N).val ≡ x [MOD a] ∧ (u : ZMod N).val ≡ y [MOD b] := by
  obtain ⟨z, hza, hzb⟩ := Nat.chineseRemainder hab x y
  have hza' : Nat.Coprime z a :=
    Nat.coprime_iff_gcd_eq_one.mpr ((Nat.ModEq.gcd_eq hza).trans (Nat.coprime_iff_gcd_eq_one.mp hx))
  have hzb' : Nat.Coprime z b :=
    Nat.coprime_iff_gcd_eq_one.mpr ((Nat.ModEq.gcd_eq hzb).trans (Nat.coprime_iff_gcd_eq_one.mp hy))
  have hz : Nat.Coprime z N := by
    rw [hN]
    exact Nat.Coprime.mul_right hza' hzb'
  obtain ⟨u, hu⟩ := exists_unit_val hz
  exact ⟨u, (Nat.ModEq.of_dvd ⟨b, hN⟩ hu).trans hza, (Nat.ModEq.of_dvd ⟨a, hN.trans (Nat.mul_comm a b)⟩ hu).trans hzb⟩

theorem jacobi_pred {p : ℕ} (hp4 : p % 4 = 3) : Nat.Coprime (p - 1) p ∧ jacobiSym ((p - 1 : ℕ) : ℤ) p = -1 := by
  constructor
  · have h2 : Nat.gcd (p - 1) p ∣ p - 1 + 1 := by
      rw [show p - 1 + 1 = p by omega]
      exact Nat.gcd_dvd_right _ _
    exact Nat.dvd_one.mp ((Nat.dvd_add_right (Nat.gcd_dvd_left _ _)).mp h2)
  · have hodd : Odd p := Nat.odd_iff.mpr (by omega)
    have hmod : ((p - 1 : ℕ) : ℤ) % (p : ℤ) = (-1 : ℤ) % (p : ℤ) := by
      rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
      push_cast [Nat.cast_sub (by omega : 1 ≤ p)]
      simp
    rw [jacobiSym.mod_left, hmod, ← jacobiSym.mod_left, jacobiSym.at_neg_one hodd, ZMod.χ₄_nat_three_mod_four hp4]

theorem ordCompl_mul_prime {m l : ℕ} (hl : l.Prime) (hm : Nat.Coprime m l) : ordCompl[l] (m * l) = m := by
  have hnd : ¬ l ∣ m := (Nat.Prime.coprime_iff_not_dvd hl).mp (Nat.Coprime.symm hm)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hnd (dvd_zero l)
  have hf : (m * l).factorization l = 1 := by
    rw [Nat.factorization_mul hm0 hl.ne_zero, Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hnd,
      hl.factorization_self, zero_add]
  rw [hf, pow_one, Nat.mul_div_cancel _ hl.pos]

namespace HostRaw

variable {φ : Frame} (H : HostRaw φ)

theorem condN_eq_q : H.condN = H.QS * H.d * H.q := by
  rw [HostRaw.condN]
  ring

theorem condN_div_q : H.condN / H.q = H.QS * H.d := by
  obtain ⟨hq, -, -, -, -⟩ := H.hyp
  rw [condN_eq_q, Nat.mul_div_cancel _ hq.pos]

theorem condN_div_d : H.condN / H.d = H.QS * H.q := by
  obtain ⟨-, hd, -, -, -⟩ := H.hyp
  rw [HostRaw.condN, Nat.mul_div_cancel _ hd.pos]

theorem ordCompl_q : ordCompl[H.q] H.condN = H.QS * H.d := by
  obtain ⟨hq, hd, hq8, hd16, -⟩ := H.hyp
  rw [condN_eq_q]
  apply ordCompl_mul_prime hq
  have hqd : Nat.Coprime H.d H.q := (Nat.coprime_primes hd hq).mpr (by omega)
  exact Nat.Coprime.mul_left (Nat.Coprime.coprime_dvd_right (Nat.dvd_mul_right H.q H.d) H.QS_coprime) hqd

variable {H}

theorem PsQ.exists_q (hP : H.PsQ) :
    ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD H.QS * H.d] ∧ (H.art u).1.1 = -1 := by
  obtain ⟨hq, hd, hq8, hd16, -⟩ := H.hyp
  have hq4 : H.q % 4 = 3 := by omega
  obtain ⟨hcop, hj⟩ := jacobi_pred hq4
  have hqd : Nat.Coprime H.d H.q := (Nat.coprime_primes hd hq).mpr (by omega)
  have hc : Nat.Coprime (H.QS * H.d) H.q :=
    Nat.Coprime.mul_left (Nat.Coprime.coprime_dvd_right (Nat.dvd_mul_right H.q H.d) H.QS_coprime) hqd
  haveI : NeZero H.condN := ⟨(Nat.mul_pos (Nat.mul_pos H.QS_pos hq.pos) hd.pos).ne'⟩
  obtain ⟨u, hu1, hu2⟩ := exists_unit_crt (N := H.condN) (condN_eq_q H) hc (Nat.coprime_one_left _) hcop
  refine ⟨u, hu1, ?_⟩
  have hu2' : (u : ZMod H.condN).val % H.q = (H.q - 1) % H.q := hu2
  have h2 : (((u : ZMod H.condN).val : ℕ) : ℤ) % (H.q : ℤ) = ((H.q - 1 : ℕ) : ℤ) % (H.q : ℤ) := by
    exact_mod_cast hu2'
  have h3 : (((H.art u).1.1 : ℤˣ) : ℤ) = -1 := by
    rw [hP u, jacobiSym.mod_left' h2, hj]
  exact Units.ext (by simpa using h3)

end HostRaw

namespace HostAx

variable {φ : Frame} (H : HostAx φ)

theorem exists_d : ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD H.QS * H.q] ∧ H.art u = φ.iod := by
  obtain ⟨hq, hd, hq8, hd16, -⟩ := H.hyp
  have hd4 : H.d % 4 = 3 := by omega
  obtain ⟨hcop, hj⟩ := jacobi_pred hd4
  have hqd : Nat.Coprime H.q H.d := (Nat.coprime_primes hq hd).mpr (by omega)
  have hc : Nat.Coprime (H.QS * H.q) H.d :=
    Nat.Coprime.mul_left (Nat.Coprime.coprime_dvd_right (Nat.dvd_mul_left H.d H.q) H.QS_coprime) hqd
  haveI : NeZero H.condN := ⟨(Nat.mul_pos (Nat.mul_pos H.QS_pos hq.pos) hd.pos).ne'⟩
  obtain ⟨u, hu1, hu2⟩ := exists_unit_crt (N := H.condN) (a := H.QS * H.q) (b := H.d) rfl hc
    (Nat.coprime_one_left _) hcop
  refine ⟨u, hu1, ?_⟩
  have hu2' : (u : ZMod H.condN).val % H.d = (H.d - 1) % H.d := hu2
  have h2 : (((u : ZMod H.condN).val : ℕ) : ℤ) % (H.d : ℤ) = ((H.d - 1 : ℕ) : ℤ) % (H.d : ℤ) := by
    exact_mod_cast hu2'
  have h3 := H.der.art_ch u
  rw [jacobiSym.mod_left' h2, hj] at h3
  rcases H.art_d u hu1 with h | h
  · exfalso
    rw [h] at h3
    simp at h3
  · exact h

theorem exact_all (hP : H.PsQ) (hE : H.Exact) (l : ℕ) (hl : l.Prime) (h : l ∣ H.condN) :
    ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD H.condN / l] ∧ H.art u ≠ 1 := by
  obtain ⟨hq, hd, -, -, -⟩ := H.hyp
  rcases (Nat.Prime.dvd_mul hl).mp h with h' | h'
  · rcases (Nat.Prime.dvd_mul hl).mp h' with h'' | h''
    · exact hE l hl h''
    · rw [(Nat.prime_dvd_prime_iff_eq hl hq).mp h'', HostRaw.condN_div_q]
      obtain ⟨u, hu1, hu2⟩ := hP.exists_q
      refine ⟨u, hu1, fun h1 => ?_⟩
      have h3 := congrArg (fun x : ℤˣ => (x : ℤ)) hu2
      rw [h1] at h3
      simp at h3
  · rw [(Nat.prime_dvd_prime_iff_eq hl hd).mp h', HostRaw.condN_div_d]
    obtain ⟨u, hu1, hu2⟩ := exists_d H
    refine ⟨u, hu1, fun h1 => ?_⟩
    have h3 := congrArg (fun g : φ.GG => ((g.1.2 : ℤˣ) : ℤ)) (hu2.symm.trans h1)
    simp [Frame.iod] at h3

end HostAx

end Formalism.HC

end
end

noncomputable section

open NumberField IntermediateField

namespace Formalism.L2.Host

open Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem range_cyc (M : ℕ) [NeZero M] (κ : CyclotomicField M ℚ →ₐ[ℚ] Qb) : κ.fieldRange = cycQ M := by
  have hz : IsPrimitiveRoot (κ (Cond.z M)) M := (Cond.z_spec M).map_of_injective κ.toRingHom.injective
  rw [AlgHom.fieldRange_eq_map, ← Cond.top_adjoin M, adjoin_map, Set.image_singleton, cycQ_eq hz]

theorem exists_cyc_act (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) :
    ∃ s : Qb ≃ₐ[ℚ] Qb, ∀ z ∈ mus N, s z = z ^ (u : ZMod N).val := by
  have hco : (u : ZMod N).val.Coprime N := ZMod.val_coe_unit_coprime u
  obtain ⟨σ, hσ⟩ := Cond.aut N (u : ZMod N).val hco
  let κ : CyclotomicField N ℚ →ₐ[ℚ] Qb := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let _ : Algebra (CyclotomicField N ℚ) Qb := κ.toRingHom.toAlgebra
  have : IsScalarTower ℚ (CyclotomicField N ℚ) Qb := IsScalarTower.of_algebraMap_eq fun x => (κ.commutes x).symm
  have : IsGalois ℚ (CyclotomicField N ℚ) := IsCyclotomicExtension.isGalois {N} ℚ (CyclotomicField N ℚ)
  have : IsAlgClosure ℚ Qb := ⟨inferInstance, AlgebraicClosure.isAlgebraic ℚ⟩
  have : Normal ℚ Qb := IsAlgClosure.normal ℚ Qb
  refine ⟨σ.liftNormal Qb, fun z hz => ?_⟩
  have hzr : z ∈ κ.fieldRange := by rw [range_cyc N κ]; exact subset_adjoin ℚ _ hz
  obtain ⟨w, rfl⟩ := hzr
  have hw : w ^ N = 1 := κ.toRingHom.injective (by
    show κ (w ^ N) = κ 1
    rw [map_pow, map_one]; exact hz)
  have h := AlgEquiv.liftNormal_commutes σ Qb w
  calc σ.liftNormal Qb (κ w) = κ (σ w) := h
    _ = κ w ^ (u : ZMod N).val := by rw [hσ w hw, map_pow]

theorem condEQ_of {φ : Formalism.HC.Frame} (H : Formalism.HC.HostAx φ) (hP : H.PsQ) (hE : H.Exact) : H.CondEQ := by
  refine ⟨H.EQ_le_cycQ, fun M hM hle => ?_⟩
  by_contra hnd
  have hN := H.condN_ne_zero
  obtain ⟨c, hc⟩ := Nat.gcd_dvd_left H.condN M
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [mul_one] at hc
    exact hnd (hc ▸ Nat.gcd_dvd_right _ _)
  obtain ⟨l, hl, c', rfl⟩ := Nat.exists_prime_and_dvd hc1
  have hdiv : H.condN / l = Nat.gcd H.condN M * c' :=
    Nat.div_eq_of_eq_mul_right hl.pos (hc.trans (by ring))
  obtain ⟨u, hu, hne⟩ := H.exact_all hP hE l hl ⟨Nat.gcd H.condN M * c', hc.trans (by ring)⟩
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder' (hu.of_dvd (hdiv ▸ dvd_mul_right _ _))
  have : NeZero (H.condN * M) := ⟨mul_ne_zero hN hM.ne'⟩
  have hk : Nat.Coprime k (H.condN * M) :=
    Nat.Coprime.mul_right (by rw [Nat.Coprime, hk1.gcd_eq]; exact ZMod.val_coe_unit_coprime u)
      (by rw [Nat.Coprime, hk2.gcd_eq]; exact Nat.gcd_one_left _)
  obtain ⟨w, hw⟩ := Formalism.HC.exists_unit_val hk
  obtain ⟨s, hs⟩ := exists_cyc_act (H.condN * M) w
  have hs1 : ∀ z ∈ mus H.condN, s z = z ^ (u : ZMod H.condN).val := fun z hz => by
    rw [hs z (mus_mono (dvd_mul_right _ _) hz), pow_eq_pow_mod _ (show z ^ H.condN = 1 from hz),
      (hw.of_dvd (dvd_mul_right _ _)).trans hk1, ← pow_eq_pow_mod _ (show z ^ H.condN = 1 from hz)]
  have hs2 : ∀ z ∈ mus M, s z = z := fun z hz => by
    rw [hs z (mus_mono (dvd_mul_left _ _) hz), pow_eq_pow_mod _ (show z ^ M = 1 from hz),
      (hw.of_dvd (dvd_mul_left _ _)).trans hk2, ← pow_eq_pow_mod _ (show z ^ M = 1 from hz), pow_one]
  have hs3 : cycQ M ≤ fixedField (Subgroup.zpowers s) := by
    rw [cycQ, adjoin_le_iff]
    intro z hz
    refine (mem_fixedField_iff _ _).2 fun t ht => ?_
    exact (Subgroup.zpowers_le.2 (show s ∈ MulAction.stabilizer (Qb ≃ₐ[ℚ] Qb) z from hs2 z hz) ht : _)
  obtain ⟨j⟩ := H.nonempty_emb
  apply hne
  rw [← H.gal.symm.map_eq_one_iff]
  ext x
  apply j.toRingHom.injective
  have h1 := (mem_fixedField_iff _ _).1 (hs3 (hle (H.mem_EQ j x))) s (Subgroup.mem_zpowers s)
  exact (H.artin_apply s u hs1 j x).symm.trans h1

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

theorem condEQ : H.CondEQ := condEQ_of H.toHostAx H.flPS H.QS_exact

end Formalism.L2.Host
end
end

open NumberField IsDedekindDomain IntermediateField

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.Host Formalism.L2.DIV Formalism.FrobeniusOrbits

section Host

variable {R : Ranks} {H : Formalism.BasicNotions.Host R} (T : Frame H)


end Host

section Host2

variable {R : Ranks} {H : Formalism.BasicNotions.Host R} (T : Frame H)



variable (ι : Qb →+* ℂ) (LL : Fld) [Normal ℚ LL] (hE : H.EQ ≤ LL)




end Host2

section Host3

variable {R : Ranks} {H : Formalism.BasicNotions.Host R} (T : Frame H)
variable (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : H.EQ ≤ LL)


end Host3

theorem ram_conj_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (hrank : Module.finrank F E = 2) (c : 𝓞 E →+* 𝓞 E) (hcc : ∀ x, c (c x) = x)
    (hcF : ∀ a : 𝓞 F, c (algebraMap (𝓞 F) (𝓞 E) a) = algebraMap (𝓞 F) (𝓞 E) a)
    (P : HeightOneSpectrum (𝓞 E))
    (hP : (P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))).map (algebraMap (𝓞 F) (𝓞 E)) ≤ P.asIdeal ^ 2) (x : 𝓞 E) :
    c x - x ∈ P.asIdeal := by
  classical
  set p : Ideal (𝓞 F) := P.asIdeal.under (𝓞 F) with hp
  have hPmax : P.asIdeal.IsMaximal := P.isMaximal
  have hPprime : P.asIdeal.IsPrime := P.isPrime
  have hpmax : p.IsMaximal := Ideal.IsMaximal.under (𝓞 F) P.asIdeal
  have hp0 : p ≠ ⊥ := Ideal.under_ne_bot (𝓞 F) P.ne_bot
  have hlies : P.asIdeal.LiesOver p := ⟨rfl⟩
  have hmap0 : p.map (algebraMap (𝓞 F) (𝓞 E)) ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))).not.2 hp0

  let Q : Ideal (𝓞 E) := P.asIdeal.comap c
  have hQprime : Q.IsPrime := Ideal.comap_isPrime c P.asIdeal
  have hQlies : Q.LiesOver p := by
    refine ⟨?_⟩
    ext a
    show a ∈ p ↔ c (algebraMap (𝓞 F) (𝓞 E) a) ∈ P.asIdeal
    rw [hcF]
    rfl
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p (𝓞 E)
  have hfr : Module.finrank (𝓞 F) (𝓞 E) = 2 := by
    rw [← hrank]
    exact (IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E).symm
  rw [hfr] at hsum
  have he : 2 ≤ P.asIdeal.ramificationIdx (𝓞 F) := by
    rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity p P.asIdeal hmap0]
    have hfin : FiniteMultiplicity P.asIdeal (p.map (algebraMap (𝓞 F) (𝓞 E))) :=
      FiniteMultiplicity.of_not_isUnit (fun h => hPprime.ne_top (Ideal.isUnit_iff.1 h)) hmap0
    exact hfin.le_multiplicity_of_pow_dvd (Ideal.dvd_iff_le.2 hP)
  have hfP : 0 < P.asIdeal.inertiaDeg (𝓞 F) := Ideal.inertiaDeg_pos P.asIdeal (𝓞 F)
  have hfQ : 0 < Q.inertiaDeg (𝓞 F) := Ideal.inertiaDeg_pos Q (𝓞 F)
  have heQ : 0 < Q.ramificationIdx (𝓞 F) := Ideal.ramificationIdx_pos (R := 𝓞 F) Q
  let P' : p.primesOver (𝓞 E) := ⟨P.asIdeal, hPprime, hlies⟩
  let Q' : p.primesOver (𝓞 E) := ⟨Q, hQprime, hQlies⟩

  have hQP : Q = P.asIdeal := by
    by_contra hne
    have hne' : Q' ≠ P' := fun h => hne (congrArg Subtype.val h)
    have h2 : ∑ q ∈ ({P', Q'} : Finset (p.primesOver (𝓞 E))), q.1.ramificationIdx (𝓞 F) * q.1.inertiaDeg (𝓞 F) ≤
        ∑ q : p.primesOver (𝓞 E), q.1.ramificationIdx (𝓞 F) * q.1.inertiaDeg (𝓞 F) :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    rw [Finset.sum_pair hne'.symm, hsum] at h2
    have h3 : 2 ≤ P.asIdeal.ramificationIdx (𝓞 F) * P.asIdeal.inertiaDeg (𝓞 F) := by nlinarith
    have h4 : 1 ≤ Q.ramificationIdx (𝓞 F) * Q.inertiaDeg (𝓞 F) := Nat.mul_pos heQ hfQ
    have h5 : P'.1 = P.asIdeal := rfl
    have h6 : Q'.1 = Q := rfl
    rw [h5, h6] at h2
    omega

  have hf1 : P.asIdeal.inertiaDeg (𝓞 F) = 1 := by
    have h2 : P'.1.ramificationIdx (𝓞 F) * P'.1.inertiaDeg (𝓞 F) ≤
        ∑ q : p.primesOver (𝓞 E), q.1.ramificationIdx (𝓞 F) * q.1.inertiaDeg (𝓞 F) :=
      Finset.single_le_sum (f := fun q : p.primesOver (𝓞 E) => q.1.ramificationIdx (𝓞 F) * q.1.inertiaDeg (𝓞 F))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ P')
    rw [hsum] at h2
    have h5 : P'.1 = P.asIdeal := rfl
    rw [h5] at h2
    nlinarith
  rw [Ideal.inertiaDeg_eq_of_isMaximal p P.asIdeal] at hf1
  let : Field (𝓞 F ⧸ p) := Ideal.Quotient.field p
  let : Field (𝓞 E ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
  obtain ⟨a', ha'⟩ := (finrank_eq_one_iff_of_nonzero' (1 : 𝓞 E ⧸ P.asIdeal) one_ne_zero).1 hf1 (Ideal.Quotient.mk P.asIdeal x)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a'
  have hxa : x - algebraMap (𝓞 F) (𝓞 E) a ∈ P.asIdeal := by
    rw [← Ideal.Quotient.eq, ← ha', Algebra.smul_def, mul_one]
    rfl
  have hc : c (x - algebraMap (𝓞 F) (𝓞 E) a) ∈ P.asIdeal := by
    rw [← hQP]
    show c (c (x - algebraMap (𝓞 F) (𝓞 E) a)) ∈ P.asIdeal
    rw [hcc]
    exact hxa
  rw [map_sub, hcF] at hc
  have := P.asIdeal.sub_mem hc hxa
  have e : c x - algebraMap (𝓞 F) (𝓞 E) a - (x - algebraMap (𝓞 F) (𝓞 E) a) = c x - x := by ring
  rwa [e] at this

theorem Fields.Ok.ram_conj {X : Fields} (h : X.Ok) (P : HeightOneSpectrum (𝓞 X.E))
    (hP : (P.asIdeal.comap (algebraMap (𝓞 X.F) (𝓞 X.E))).map (algebraMap (𝓞 X.F) (𝓞 X.E)) ≤ P.asIdeal ^ 2) (x : 𝓞 X.E) :
    X.conjO x - x ∈ P.asIdeal := by
  refine ram_conj_mem h.rankE X.conjO ?_ ?_ P hP x
  · intro y
    apply RingOfIntegers.ext
    show star (star (y : X.E)) = y
    exact star_star _
  · intro a
    apply RingOfIntegers.ext
    exact h.star_F (a : X.F)

theorem Fields.Ok.unram_of_inertia {X : Fields} (h : X.Ok)
    (hin : ∀ P : HeightOneSpectrum (𝓞 X.E), ¬ ∀ x : 𝓞 X.E, X.conjO x - x ∈ P.asIdeal) (P : HeightOneSpectrum (𝓞 X.E)) :
    ¬ (P.asIdeal.comap (algebraMap (𝓞 X.F) (𝓞 X.E))).map (algebraMap (𝓞 X.F) (𝓞 X.E)) ≤ P.asIdeal ^ 2 :=
  fun hP => hin P (h.ram_conj P hP)

end Formalism.L2.Col
