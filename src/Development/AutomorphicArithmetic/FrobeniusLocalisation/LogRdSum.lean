module

public import Development.AutomorphicArithmetic.FrobeniusLocalisation.DiffDefs
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.RdArith
public import Formalism.DirichletDensity.DirichletDensityProofs.QuadDiscr

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.FrobeniusLocalisation.LogRdSum
open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

theorem UpperTheory.HF.log_rd_sum :
    ∀ {φ : Frame} (H : HostAx φ), Real.log H.rd = ∑ l ∈ H.ram, H.vdH l * Real.log l ∧ Real.log H.rd = ∑ l ∈ H.condN.primeFactors, H.vdH l * Real.log l ∧ H.ram ⊆ H.condN.primeFactors ∧ 0 < H.rd := by
  intro φ H
  have hd : discr H.E ≠ 0 := discr_ne_zero H.E
  have hd' : (discr H.E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 hd
  have habs : |(discr H.E : ℝ)| = ((discr H.E).natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hpos : 0 < |(discr H.E : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 hd)
  have h1 : Real.log H.rd = ∑ l ∈ H.ram, H.vdH l * Real.log l := by
    unfold HostRaw.rd HostRaw.ram HostRaw.vdH
    rw [Real.log_rpow hpos, habs, Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Nat.factorization_def _ (Nat.prime_of_mem_primeFactors hl)]
    rw [Nat.padicValNat_def]
    ring
  have h3 : H.ram ⊆ H.condN.primeFactors := by
    intro l hl
    have h := Nat.mem_primeFactors.1 hl
    exact Nat.mem_primeFactors.2 ⟨h.1, H.der.discr_primes.1 l h.1 (Int.natCast_dvd.2 h.2.1), H.condN_ne_zero⟩
  refine ⟨h1, ?_, h3, Real.rpow_pos_of_pos hpos _⟩
  rw [h1]
  refine Finset.sum_subset h3 fun l hl hn => ?_
  have hp := Nat.prime_of_mem_primeFactors hl
  have : ¬ l ∣ (discr H.E).natAbs := fun h => hn (Nat.mem_primeFactors.2 ⟨hp, h, hd'⟩)
  unfold HostRaw.vdH
  rw [Nat.padicValNat_def, multiplicity_eq_zero_of_not_dvd this]
  simp
end

section -- merged from Development.AutomorphicArithmetic.FrobeniusLocalisation.CardImgOneDvd
open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

private theorem card_map_dvd {G G' : Type*} [Group G] [Group G'] (a : G →* G') {A B : Subgroup G} (h : A ≤ B) :
    Nat.card (B.map a) ∣ Nat.card (A.map a) * A.relIndex B := by
  have hAB : A.map a ≤ B.map a := Subgroup.map_mono h
  have hc : Nat.card (B.map a) = Nat.card (A.map a) * (A.map a).relIndex (B.map a) := by
    rw [Subgroup.relIndex, ← Subgroup.card_mul_index ((A.map a).subgroupOf (B.map a))]
    congr 1
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv
  rw [hc]
  apply mul_dvd_mul_left
  rw [← Subgroup.relIndex_comap]
  exact Subgroup.relIndex_dvd_of_le_left B (Subgroup.le_comap_map a A)

private theorem index_unitsOne {φ : Frame} (H : HostRaw φ) {f : ℕ} (hf : f ∣ H.condN) :
    (H.unitsOne f).index = f.totient := by
  have hN : H.condN ≠ 0 := H.condN_ne_zero
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hN (zero_dvd_iff.1 hf)
  have hg : Nat.gcd f H.condN = f := Nat.gcd_eq_left hf
  haveI : NeZero (Nat.gcd f H.condN) := ⟨by rw [hg]; exact hf0⟩
  unfold HostRaw.unitsOne
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 (ZMod.unitsMap_surjective _), Subgroup.card_top,
    Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, hg]

theorem UpperTheory.HF.card_imgOne_dvd :
    ∀ {φ : Frame} (H : HostRaw φ) {f g : ℕ}, f ∣ g → g ∣ H.condN → Nat.card (H.imgOne f) ∣ Nat.card (H.imgOne g) * (g.totient / f.totient) := by
  intro φ H f g hfg hg
  have hf : f ∣ H.condN := hfg.trans hg
  have hle : H.unitsOne g ≤ H.unitsOne f := by
    intro u hu
    rw [H.mem_unitsOne hg] at hu
    rw [H.mem_unitsOne hf]
    exact Nat.ModEq.of_dvd hfg hu
  have hd := card_map_dvd H.art hle
  have hidx := Subgroup.relIndex_mul_index hle
  rw [index_unitsOne H hf, index_unitsOne H hg] at hidx
  have hf0 : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · exfalso
      subst h0
      exact H.condN_ne_zero (zero_dvd_iff.1 hf)
    · exact h0
  have htot : 0 < f.totient := Nat.totient_pos.2 hf0
  have hr : g.totient / f.totient = (H.unitsOne g).relIndex (H.unitsOne f) := by
    rw [← hidx, Nat.mul_div_cancel _ htot]
  rw [hr]
  exact hd
end

section -- merged from Development.AutomorphicArithmetic.FrobeniusLocalisation.CondESpec
section -- merged from Development.AutomorphicArithmetic.FrobeniusLocalisation.ImgOneGcd
open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

theorem UpperTheory.HF.imgOne_gcd :
    ∀ {φ : Frame} (H : HostRaw φ) {f g : ℕ}, f ∣ H.condN → g ∣ H.condN → H.imgOne (Nat.gcd f g) = H.imgOne f ⊔ H.imgOne g := by
  intro φ H f g hf hg
  have hgcd : Nat.gcd f g ∣ H.condN := (Nat.gcd_dvd_left f g).trans hf
  apply le_antisymm
  · rintro x hx
    rw [H.mem_imgOne hgcd] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    have key := Der.Rd.KK_gcd (N := H.condN) ((H.imgOne f ⊔ H.imgOne g).comap H.art) hf hg
      (fun v hv => Subgroup.mem_sup_left ((H.mem_imgOne hf _).2 ⟨v, Der.Rd.mem_KK.1 hv, rfl⟩))
      (fun v hv => Subgroup.mem_sup_right ((H.mem_imgOne hg _).2 ⟨v, Der.Rd.mem_KK.1 hv, rfl⟩))
      u (Der.Rd.mem_KK.2 hu)
    exact key
  · exact sup_le (H.imgOne_anti (Nat.gcd_dvd_left f g) hf) (H.imgOne_anti (Nat.gcd_dvd_right f g) hg)
end

open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

theorem UpperTheory.HF.condE_spec :
    ∀ {φ : Frame} (H : HostRaw φ), H.condE ∣ H.condN ∧ 0 < H.condE ∧ ∀ f : ℕ, f ∣ H.condN → (H.imgOne f = ⊥ ↔ H.condE ∣ f) := by
  intro φ H
  have hN0 : H.condN ≠ 0 := H.condN_ne_zero
  have hN : H.imgOne H.condN = ⊥ := by
    rw [H.imgOne_eq_bot_iff dvd_rfl]
    intro u hu
    have h1 : u = 1 := by
      haveI : NeZero H.condN := ⟨hN0⟩
      apply Units.ext
      have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).2 hu
      rw [ZMod.natCast_zmod_val, Nat.cast_one] at h2
      exact h2
    rw [h1, map_one]
  have hmem : H.condE ∣ H.condN ∧ H.imgOne H.condE = ⊥ :=
    Nat.sInf_mem (s := {f : ℕ | f ∣ H.condN ∧ H.imgOne f = ⊥}) ⟨H.condN, dvd_rfl, hN⟩
  have hpos : 0 < H.condE := Nat.pos_of_dvd_of_pos hmem.1 (Nat.pos_of_ne_zero hN0)
  refine ⟨hmem.1, hpos, fun f hf => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have hg : H.imgOne (Nat.gcd H.condE f) = ⊥ := by
      rw [UpperTheory.HF.imgOne_gcd H hmem.1 hf, hmem.2, h, sup_bot_eq]
    have hle : H.condE ≤ Nat.gcd H.condE f :=
      Nat.sInf_le (s := {f : ℕ | f ∣ H.condN ∧ H.imgOne f = ⊥})
        ⟨(Nat.gcd_dvd_right _ _).trans hf, hg⟩
    have heq : Nat.gcd H.condE f = H.condE := le_antisymm (Nat.gcd_le_left _ hpos) hle
    rw [← heq]
    exact Nat.gcd_dvd_right _ _
  · exact le_bot_iff.1 (hmem.2 ▸ H.imgOne_anti h hf)
end

section -- merged from Development.AutomorphicArithmetic.FrobeniusLocalisation.RhoArt
open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

theorem UpperTheory.HF.rho_art :
    ∀ {φ : Frame} (H : HostRaw φ) {f : ℕ}, f ∣ H.condN → Formalism.HC.Der.Rd.rho H.art.ker f = 1 - 1 / (Nat.card (H.imgOne f) : ℝ) := by
  intro φ H f hf
  classical
  rw [Formalism.HC.Der.Rd.rho_eq _ hf]
  have h1 := (H.art.ker.subgroupOf (H.unitsOne f)).card_mul_index
  have h2 : (H.art.ker.subgroupOf (H.unitsOne f)).index = Nat.card (H.imgOne f) :=
    Subgroup.relIndex_ker (H.unitsOne f) H.art
  have h3 : Nat.card (H.unitsOne f) = (Formalism.HC.Der.Rd.KK H.condN f).card := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun u => by
      rw [Formalism.HC.Der.Rd.mem_KK, H.mem_unitsOne hf])
  have h4 : Nat.card (H.art.ker.subgroupOf (H.unitsOne f)) =
      ((Formalism.HC.Der.Rd.KK H.condN f).filter fun u => u ∈ H.art.ker).card := by
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_congr ((Equiv.subtypeSubtypeEquivSubtypeInter (fun u => u ∈ H.unitsOne f)
      (fun u => u ∈ H.art.ker)).trans (Equiv.subtypeEquivRight fun u => ?_))
    rw [Finset.mem_filter, Formalism.HC.Der.Rd.mem_KK, H.mem_unitsOne hf]
  rw [h2, h3, h4] at h1
  have h5 := Formalism.HC.Der.Rd.card_KK hf
  rw [← h1] at h5
  have h6 := congrArg (Nat.cast : ℕ → ℝ) h5
  push_cast at h6
  have hN : (H.condN.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos H.condN)).ne'
  have hI : (Nat.card (H.imgOne f) : ℝ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  congr 1
  rw [div_eq_div_iff hN hI, one_mul, ← h6]
  rw [mul_right_comm]
  congr!
end

section -- merged from Development.AutomorphicArithmetic.FrobeniusLocalisation.FrobGSpec
open UpperTheory.HF

open NumberField IntermediateField Ideal Formalism.FrobeniusOrbits Formalism.HC
open scoped Pointwise

theorem UpperTheory.HF.frobG_spec :
    ∀ (φ : Frame) (H : HostAx φ) (p : ℕ) [Fact p.Prime], ¬ p ∣ H.condN →
      (∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E), IsArithFrobAt ℤ σ P ↔ H.galE σ = H.frobG p) ∧
      (((H.frobG p).1.2 : ℤˣ) : ℤ) = jacobiSym (-(H.d : ℤ)) p ∧ (((H.frobG p).1.1 : ℤˣ) : ℤ) = H.psAt p ∧
      (H.frobG p ∉ φ.Psi ↔ H.Inert p) ∧ (H.frobG p ∈ φ.Psi ↔ jacobiSym (-(H.d : ℤ)) p = 1) ∧
      ∃ v : (ZMod (2 ^ (φ.e + 2)))ˣ, (v : ZMod (2 ^ (φ.e + 2))) = (p : ZMod _) ∧ φ.hH (H.frobG p).2 = hcl φ.e v := by
  intro φ H p hpr hnd
  have hp : Nat.Coprime p H.condN := (Nat.Prime.coprime_iff_not_dvd hpr.out).2 hnd
  have hodd : p % 2 = 1 := H.odd_of_coprime hp
  set u := ZMod.unitOfCoprime p hp with hu
  have hval : (u : ZMod H.condN).val ≡ p [MOD H.condN] := H.val_unitOfCoprime hp
  have hF : H.frobG p = H.art u := H.frobG_of_coprime hp
  have hjac : (((H.frobG p).1.2 : ℤˣ) : ℤ) = jacobiSym (-(H.d : ℤ)) p := by
    rw [hF, H.der.art_ch u, jacobi_neg_recip H.d_mod_four hodd]
    exact jacobi_congr (hval.of_dvd H.d_dvd_condN)
  have hne : jacobiSym (-(H.d : ℤ)) p = 1 ∨ jacobiSym (-(H.d : ℤ)) p = -1 := by
    rw [← hjac]
    rcases Int.units_eq_one_or ((H.frobG p).1.2) with h | h <;> simp [h]
  have hpsi : H.frobG p ∈ φ.Psi ↔ jacobiSym (-(H.d : ℤ)) p = 1 := by
    rw [Frame.mem_Psi_iff, ← hjac]
    constructor
    · intro h
      rw [h]
      rfl
    · intro h
      exact Units.ext h
  refine ⟨?_, hjac, ?_, ?_, hpsi, ?_⟩
  · intro P _ _ σ
    rw [hF]
    exact H.frob_iff p hp P σ
  · rw [hF, H.psAt_of_coprime hp]
  · rw [hpsi]
    unfold UpperTheory.HF.Formalism.HC.HostRaw.Inert
    constructor
    · intro h
      refine ⟨hpr.out, ?_⟩
      rcases hne with h1 | h1
      · exact absurd h1 h
      · exact h1
    · rintro ⟨-, h⟩
      rw [h]
      decide
  · have hc2 : Nat.Coprime p (2 ^ (φ.e + 2)) :=
      Nat.Coprime.coprime_dvd_right H.tower_dvd_condN hp
    refine ⟨ZMod.unitOfCoprime p hc2, by simp, ?_⟩
    rw [hF]
    apply H.art_h
    rw [ZMod.coe_unitOfCoprime]
    exact ((ZMod.natCast_eq_natCast_iff _ _ _).2 (hval.of_dvd H.tower_dvd_condN)).symm
end

section -- merged from Development.AutomorphicArithmetic.FrobeniusLocalisation.DiscrK
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

section
open Polynomial

private theorem diffQuadK (K : Type) [Field K] [NumberField K] (d : ℕ) (hd : d.Prime) (hd4 : d % 4 = 3)
    (x : K) (hx : x ^ 2 = -(d : K)) (hadj : IntermediateField.adjoin ℚ {x} = ⊤)
    (hrank : Module.finrank ℚ K = 2) (β : 𝓞 K) (hβ : (β : K) = x) :
    discr K = -(d : ℤ) ∧ differentIdeal ℤ (𝓞 K) = span {β} := by
  have hdisc : discr K = -(d : ℤ) :=
    Formalism.HF.quadDiscr K (-(d : ℤ)) x (by push_cast; exact hx) hadj
      ((Nat.prime_iff_prime_int.mp hd).neg.squarefree) (by omega)
  refine ⟨hdisc, ?_⟩
  have hN : (differentIdeal ℤ (𝓞 K)).absNorm = d := by
    rw [absNorm_differentIdeal K, hdisc]; simp
  have hβ2 : β ^ 2 = -(d : 𝓞 K) := by
    apply RingOfIntegers.ext
    have : ((β ^ 2 : 𝓞 K) : K) = (β : K) ^ 2 := by push_cast; rfl
    rw [this, hβ, hx]
    push_cast; rfl
  have hadj' : Algebra.adjoin ℚ {algebraMap (𝓞 K) K β} = ⊤ := by
    have h1 : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
    have h2 := IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic h1
    rw [hadj] at h2
    show Algebra.adjoin ℚ {(β : K)} = ⊤
    rw [hβ, ← h2]
    rfl
  have hmem := aeval_derivative_mem_differentIdeal ℤ ℚ K β hadj'
  have hint : IsIntegral ℤ β := Algebra.IsIntegral.isIntegral β
  obtain ⟨r, hr⟩ := minpoly.isIntegrallyClosed_dvd hint (p := X ^ 2 + C (d : ℤ))
    (by simp [hβ2])
  have h2β : 2 * β ∈ differentIdeal ℤ (𝓞 K) := by
    have := congrArg (fun p => aeval β (derivative p)) hr
    simp only [derivative_X_pow, derivative_C, derivative_mul, map_add (f := _), map_mul,
      minpoly.aeval, zero_mul, add_zero] at this
    have e : (2 : 𝓞 K) * β = aeval β (derivative (minpoly ℤ β)) * aeval β r := by
      rw [← this]; simp [map_ofNat]
    rw [e]
    exact Ideal.mul_mem_right _ _ hmem
  have hdmem : (d : 𝓞 K) ∈ differentIdeal ℤ (𝓞 K) := by
    have := Ideal.absNorm_mem (differentIdeal ℤ (𝓞 K))
    rwa [hN] at this
  have hβmem : β ∈ differentIdeal ℤ (𝓞 K) := by
    have e : β = (d : 𝓞 K) * β - ((d / 2 : ℕ) : 𝓞 K) * (2 * β) := by
      have h : (d : 𝓞 K) = 2 * ((d / 2 : ℕ) : 𝓞 K) + 1 := by
        have : d = 2 * (d / 2) + 1 := by omega
        exact_mod_cast this
      linear_combination (-β) * h
    rw [e]
    exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hdmem) (Ideal.mul_mem_left _ _ h2β)
  have hle : span {β} ≤ differentIdeal ℤ (𝓞 K) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]; exact hβmem
  obtain ⟨C, hC⟩ := Ideal.dvd_iff_le.mpr hle
  have hNβ : (span {β}).absNorm ^ 2 = d ^ 2 := by
    rw [← map_pow, Ideal.span_singleton_pow, hβ2, Ideal.absNorm_span_singleton]
    have : (-(d : 𝓞 K)) = algebraMap ℤ (𝓞 K) (-(d : ℤ)) := by simp
    rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank, hrank]
    simp [Int.natAbs_pow]
  have hNβ' : (span {β}).absNorm = d := by
    exact Nat.pow_left_injective (n := 2) (by norm_num) hNβ
  have hC1 : C.absNorm = 1 := by
    have := congrArg Ideal.absNorm hC
    rw [map_mul, hNβ', hN] at this
    exact Nat.eq_of_mul_eq_mul_left hd.pos (by rw [mul_one]; exact this.symm)
  rw [Ideal.absNorm_eq_one_iff] at hC1
  rw [hC, hC1, Ideal.mul_top]

end

theorem UpperTheory.HF.discr_K :
    ∀ {φ : Frame} (H : HostAx φ), (discr H.K).natAbs = H.d ∧ ∃ s : 𝓞 H.E, (s : H.E) = H.sqd ∧ (differentIdeal ℤ (𝓞 H.K)).map (algebraMap (𝓞 H.K) (𝓞 H.E)) = span {s} ∧ differentIdeal ℤ (𝓞 H.E) = differentIdeal (𝓞 H.K) (𝓞 H.E) * span {s} := by
  intro φ H
  let x : H.K := ⟨H.sqd, H.sqd_mem_K⟩
  have hx : x ^ 2 = -(H.d : H.K) := by
    apply Subtype.ext
    simpa [x] using H.sqd_sq
  have hint : IsIntegral ℤ x := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [hx]
    exact (isIntegral_natCast H.d).neg
  have hadj : IntermediateField.adjoin ℚ {x} = ⊤ := by
    have h' : IntermediateField.lift (@IntermediateField.adjoin ℚ _ H.K _ H.K.algebra' {x}) =
        IntermediateField.lift (⊤ : @IntermediateField ℚ H.K _ _ H.K.algebra') := by
      rw [IntermediateField.lift_adjoin, IntermediateField.lift_top, Set.image_singleton]
      rfl
    have key := IntermediateField.lift_injective H.K h'
    convert key <;> exact Subsingleton.elim _ _
  obtain ⟨β, hβ⟩ : ∃ β : 𝓞 H.K, (β : H.K) = x := ⟨⟨x, hint⟩, rfl⟩
  obtain ⟨hd, hK⟩ := diffQuadK H.K H.d H.d_prime H.d_mod_four x hx hadj H.finrank_K β hβ
  have hmap : (differentIdeal ℤ (𝓞 H.K)).map (algebraMap (𝓞 H.K) (𝓞 H.E)) =
      span {algebraMap (𝓞 H.K) (𝓞 H.E) β} := by
    rw [hK, Ideal.map_span, Set.image_singleton]
  refine ⟨by rw [hd]; simp, algebraMap (𝓞 H.K) (𝓞 H.E) β, ?_, hmap, ?_⟩
  · show ((β : H.K) : H.E) = H.sqd
    rw [hβ]
  · rw [← hmap]
    exact differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 H.K) (𝓞 H.E)
end
