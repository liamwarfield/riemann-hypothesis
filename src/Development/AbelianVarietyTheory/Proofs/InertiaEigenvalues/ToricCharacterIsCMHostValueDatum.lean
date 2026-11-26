module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConductorExponentAtPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussNormCoeffWittDisc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineFrobeniusBijOnLettersDirectSum

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LamConductorExponent
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLeOfLe
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

theorem levelLe_of_le {E : Type} [Field E] [NumberField E] {χ : Formalism.L2.Host.HChar E} {w : HeightOneSpectrum (𝓞 E)} {m m' : ℕ}
    (h : χ.LevelLe w m) (hm : m ≤ m') : χ.LevelLe w m' := by
  intro x hx hv

  refine h x hx (le_trans hv ?_)
  rw [WithZero.exp_le_exp]
  omega

theorem expAt_mul_inv : ∀ (E : Type) [Field E] [NumberField E] (χ χ' : Formalism.L2.Host.HChar E) (w : HeightOneSpectrum (𝓞 E)) (n : ℕ),
    1 ≤ n → ExpAt χ w n → χ'.LevelLe w (n - 1) → ExpAt (χ' * χ⁻¹) w n := by
  intro E _ _ χ χ' w n hn hχ hχ' m
  constructor
  · intro hm

    by_contra hlt
    have h1 : (χ' * χ⁻¹).LevelLe w (n - 1) := levelLe_of_le hm (by omega)
    have h2 : χ.LevelLe w (n - 1) := by
      have h3 := Formalism.L2.Host.HChar.LevelLe.mul (Formalism.L2.Host.HChar.LevelLe.inv h1) hχ'
      have h4 : (χ' * χ⁻¹)⁻¹ * χ' = χ := by group
      rwa [h4] at h3
    have := (hχ (n - 1)).mp h2
    omega
  · intro hm

    have hc : χ.LevelLe w m := (hχ m).mpr hm
    have hc' : χ'.LevelLe w m := levelLe_of_le hχ' (by omega)
    exact Formalism.L2.Host.HChar.LevelLe.mul hc' (Formalism.L2.Host.HChar.LevelLe.inv hc)

end GlobalTheory.LamTie
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LamConductorExponent
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

theorem mu0_del_tame {D : D7} (C : CharFrame D) (l : ℕ) (j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    (C.mu0 j * C.delAt l).LevelLe w 1 := by
  have hd : (C.delAt l).TameAt w := by
    unfold CharFrame.delAt; split_ifs
    · exact C.isDel'.tame w
    · exact C.isDel.tame w
  exact HChar.LevelLe.mul ((C.isMu0 j).tame w) hd

theorem mu0_del_unr {D : D7} (C : CharFrame D) (l : ℕ) (j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : ¬ Over4 D.host w) : (C.mu0 j * C.delAt l).UnrAt w := by
  have h1 : ∀ k, ¬ OverP D.host (D.host.g k) w := fun k hk => hw (Or.inl ⟨k, hk⟩)
  have hd : (C.delAt l).UnrAt w := by
    unfold CharFrame.delAt; split_ifs
    · exact C.isDel'.unr w (fun h => hw (Or.inr (Or.inr h)))
    · exact C.isDel.unr w (fun h => hw (Or.inr (Or.inl h)))
  exact HChar.UnrAt.mul ((C.isMu0 j).unr w h1) hd

theorem lam0_expAt : ∀ (D : D7) (Z : LamDat D), Z.Ok → ∀ (l : ℕ) (j a : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)),
    ExpAt (Z.lam0 l j a) w (expIn (cond0 D.host Z.w0) (below w)) := by
  intro D Z hZ l j a w
  obtain ⟨h4, h0, hO⟩ := expIn_cond0 D.R D.host Z.q0 Z.w0 hZ.places w
  have hA := hZ.aux a
  unfold LamDat.lam0
  by_cases hw : Over4 D.host w
  · rw [h4 hw]
    exact expAt_mul_inv _ (Z.chi a) _ w 2 (by norm_num) (hA.two w hw) (mu0_del_tame Z.C l j w)
  · by_cases hb : below w = below Z.w0
    · rw [(h0 hb).2]
      have hu := mu0_del_unr Z.C l j w hw
      exact expAt_mul_inv _ (Z.chi a) _ w 1 le_rfl (hA.one w hb) ((HChar.unrAt_iff _ _).1 hu)
    · rw [hO hw hb]
      have hu := HChar.UnrAt.mul (mu0_del_unr Z.C l j w hw) (HChar.UnrAt.inv (hA.unr w hw hb))
      intro m
      exact ⟨fun _ => Nat.zero_le m, fun _ => HChar.UnrAt.levelLe hu m⟩

end GlobalTheory.LamTie
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LamConductorExponentStatement
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lam_conductor_exponent : ∀ (D : D7) (Z : LamDat D), Z.Ok → ∀ (l : ℕ) (j a : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)), ExpAt (Z.lam0 l j a) w (expIn (cond0 D.host Z.w0) (below w)) := by
  first | exact @GlobalTheory.LamTie.lam0_expAt | exact GlobalTheory.LamTie.lam0_expAt | (intros; apply GlobalTheory.LamTie.lam0_expAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBaseCondOfSplitPrimes
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBaseCondOfSplitPrimes
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

theorem basecond_exists_above {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (OF E)) :
    ∃ P : HeightOneSpectrum (𝓞 E), below P = v := by
  have hinj : Function.Injective (algebraMap (OF E) (𝓞 E)) :=
    FaithfulSMul.algebraMap_injective (OF E) (𝓞 E)
  obtain ⟨Q, -, hQ, hQv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 E) v.asIdeal ⊥
    (by
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_bot, ← map_zero (algebraMap (OF E) (𝓞 E))] at hx
      rw [hinj hx]
      exact v.asIdeal.zero_mem)
  have hQne : Q ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [← hQv]
    exact Ideal.comap_bot_of_injective _ hinj
  refine ⟨⟨Q, hQ, hQne⟩, ?_⟩
  ext x
  simp [below, Ideal.under, ← hQv]

theorem basecond_natCast_mem_below {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) :
    (n : OF E) ∈ (below P).asIdeal ↔ (n : 𝓞 E) ∈ P.asIdeal := by
  simp [below, Ideal.under, Ideal.mem_comap, map_natCast]

theorem isBaseCond_cond0 : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (q0 : ℕ) (w0 : HeightOneSpectrum (𝓞 H.E)), (∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], ∀ P : HeightOneSpectrum (𝓞 H.E), (p : 𝓞 H.E) ∈ P.asIdeal → Splits (below P)) → PlacesOk H q0 w0 → IsBaseCond (cond0 H w0) := by
  intro R H q0 w0 hspl hok
  have hprime : ∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], p.Prime := fun p hp => (hok.splits p hp).1

  have hN0 : ((H.g 0 * H.g 1 * H.pde * H.pde' : ℕ) : OF H.E) ≠ 0 := by
    have h : H.g 0 * H.g 1 * H.pde * H.pde' ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_ <;>
        exact (hprime _ (by simp)).ne_zero
    exact_mod_cast h
  have hle : cond0 H w0 ≤ (below w0).asIdeal := by
    unfold cond0
    first
    | exact Ideal.mul_le_right
    | exact Ideal.mul_le_left
  refine ⟨?_, ?_, ?_⟩
  · intro h
    rcases Ideal.mul_eq_bot.mp h with h1 | h1
    · rw [← Ideal.zero_eq_bot] at h1
      have h2 := pow_eq_zero_iff (two_ne_zero) |>.mp h1
      rw [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] at h2
      exact hN0 h2
    · exact (below w0).ne_bot h1
  · intro h
    exact (below w0).isPrime.ne_top (top_le_iff.mp (h ▸ hle))
  · intro v hv

    obtain ⟨p, hp, hpv⟩ : ∃ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], ((p : ℕ) : OF H.E) ∈ v.asIdeal := by
      have hvp : Prime v.asIdeal := Ideal.prime_of_isPrime v.ne_bot v.isPrime
      rcases hvp.dvd_or_dvd hv with h | h
      · have h1 : ((H.g 0 * H.g 1 * H.pde * H.pde' : ℕ) : OF H.E) ∈ v.asIdeal :=
          (Ideal.span_singleton_le_iff_mem _).mp (Ideal.le_of_dvd (hvp.dvd_of_dvd_pow h))
        push_cast at h1
        rcases v.isPrime.mem_or_mem h1 with h1 | h1
        · rcases v.isPrime.mem_or_mem h1 with h1 | h1
          · rcases v.isPrime.mem_or_mem h1 with h1 | h1
            · exact ⟨H.g 0, by simp, h1⟩
            · exact ⟨H.g 1, by simp, h1⟩
          · exact ⟨H.pde, by simp, h1⟩
        · exact ⟨H.pde', by simp, h1⟩
      · have h1 : (below w0).asIdeal = v.asIdeal :=
          ((below w0).isMaximal).eq_of_le v.isPrime.ne_top (Ideal.le_of_dvd h)
        refine ⟨q0, by simp, ?_⟩
        rw [← h1, basecond_natCast_mem_below]
        exact hok.referencePlaceOverPrime
    obtain ⟨P, hPv⟩ := basecond_exists_above v
    have hpP : ((p : ℕ) : 𝓞 H.E) ∈ P.asIdeal := by
      rw [← basecond_natCast_mem_below, hPv]
      exact hpv
    obtain ⟨hpr, hp2, hdisc, hnorm⟩ := hok.splits p hp
    refine ⟨hPv ▸ hspl p hp P hpP, ?_, p, hpr, hp2, hpv, hdisc, hnorm⟩

    obtain ⟨e4, eb, e0⟩ := GlobalTheory.T.conductor_exponent_at_places R H q0 w0 hok P
    rw [← hPv]
    by_cases h4 : Over4 H P
    · rw [e4 h4]
    · by_cases hb : below P = below w0
      · rw [(eb hb).2]; norm_num
      · rw [e0 h4 hb]; norm_num

end GlobalTheory.LamTie
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBaseCondOfSplitPrimesStatement
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBaseCond_of_split_primes : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (q0 : ℕ) (w0 : HeightOneSpectrum (𝓞 H.E)), (∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], ∀ P : HeightOneSpectrum (𝓞 H.E), (p : 𝓞 H.E) ∈ P.asIdeal → Splits (below P)) → PlacesOk H q0 w0 → IsBaseCond (cond0 H w0) := by
  first | exact @GlobalTheory.LamTie.isBaseCond_cond0 | exact GlobalTheory.LamTie.isBaseCond_cond0 | (intros; apply GlobalTheory.LamTie.isBaseCond_cond0 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToricLam0HasInfinityTypeConjRatio
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToricLam0HasInfinityTypeConjRatio
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie.InfType

theorem inf_eq_one {L : Type} [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] {χ : Formalism.L2.Host.HChar L} {n : ℕ} (hn : 0 < n)
    (h : χ.OrderDvd n) (k : Lˣ) : χ.inf k = 1 := by
  have hx : ∀ x, (χ.1 x) ^ n = 1 := fun x => congrArg (fun ξ : Formalism.L2.Host.HChar L => ξ.1 x) h
  have hw : ∀ (w : InfinitePlace L) (y : (w.Completion)ˣ), χ.locInf w y = 1 := by
    intro w y
    let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e (y : w.Completion)) hn
    have hz' : (e.symm z) ^ n = y := by rw [← map_pow, hz]; simp
    have hz0 : e.symm z ≠ 0 := by
      intro h0; rw [h0, zero_pow hn.ne'] at hz'; exact y.ne_zero hz'.symm
    have : y = (Units.mk0 _ hz0) ^ n := Units.ext (by simp [hz'])
    rw [this, map_pow]
    exact hx _
  show χ.1 (Formalism.L2.Host.infDiag k) = 1
  unfold Formalism.L2.Host.infDiag
  classical
  have hp : ∀ s : Finset (InfinitePlace L),
      (∏ w ∈ s, (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele L w).comp (atInf w)) k =
        ∏ w ∈ s, ReciprocityTheory.Neutral.Bridge.HCFR.infIdele L w (atInf w k) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert w s hws ih => simp [hws, ih, MonoidHom.mul_apply]
  rw [hp, map_prod]
  exact Finset.prod_eq_one fun w _ => hw w _

theorem conj_div_norm {z : ℂ} (hz : z ≠ 0) :
    starRingEnd ℂ z / ((‖starRingEnd ℂ z‖ : ℝ) : ℂ) = (z / ((‖z‖ : ℝ) : ℂ))⁻¹ := by
  have h1 : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz
  rw [Complex.norm_conj, inv_div, div_eq_div_iff h1 hz, ← sq, ← Complex.mul_conj', mul_comm]

theorem delAt_inf {D : D7} (C : CharFrame D) (l : ℕ) (k : D.host.Eˣ) : (C.delAt l).inf k = 1 := by
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  unfold CharFrame.delAt
  split_ifs
  · obtain ⟨n, hn, h⟩ := C.isDel'.fin
    exact inf_eq_one hn h k
  · obtain ⟨n, hn, h⟩ := C.isDel.fin
    exact inf_eq_one hn h k

theorem toricLam0_hasInfinityType_conjRatio (D : D7) (Z : LamDat D) (hZ : Z.Ok) (l : ℕ) (j a : Fin D.R.m) (s : ℕ)
    (hs : (s : ℤ) ≤ (BlochKatoReduction.Gen.NFun D.R : ℤ) + 1) :
    (∀ g, 1 ≤ Z.kap j a s g) ∧
      GlobalTheory.CMVal.HasInf (Z.lam0 l j a) (phi D.host) (fun g => (Z.kap j a s g : ℤ) + s) := by
  have he : ∀ g, ∃ z : ℤ, eExp D j g = z := fun g => (D.hc _).e_int j
  choose e he using he
  have hpos : ∀ g, 1 ≤ e g + Z.c a g - s := fun g => by
    have h := hZ.big j a g
    rw [he] at h
    have h' : (BlochKatoReduction.Gen.NFun D.R : ℤ) + 1 < e g + Z.c a g := by exact_mod_cast h
    omega
  have hk : ∀ g, (Z.kap j a s g : ℤ) = e g + Z.c a g - s := fun g => by
    unfold LamDat.kap
    rw [he, Int.floor_intCast]
    exact Int.toNat_of_nonneg (by have := hpos g; omega)
  refine ⟨fun g => by have := hk g; have := hpos g; omega, fun k => ?_⟩
  obtain ⟨n, hn, h1⟩ := (Z.C.isMu0 j).inf
  obtain ⟨n', hn', h2⟩ := (hZ.aux a).inf
  unfold LamDat.lam0
  rw [HChar.inf_mul, HChar.inf_mul, HChar.inf_inv, delAt_inf, mul_one, Units.val_mul, Units.val_inv_eq_inv_val, h1 k, h2 k,
    ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun g _ => ?_
  have hz : embPsi D.host g (k : D.host.E) ≠ 0 := by simp
  have hu : embPsi D.host g (k : D.host.E) / ((‖embPsi D.host g (k : D.host.E)‖ : ℝ) : ℂ) ≠ 0 :=
    div_ne_zero hz (by exact_mod_cast norm_ne_zero_iff.2 hz)
  have e1 : n g = 2 * -(e g) := by
    have := hn g
    simp only [he] at this
    exact_mod_cast this
  have e2 : n' g = 2 * Z.c a g := by
    have := hn' g
    beta_reduce at this
    exact_mod_cast this
  have e3 : phi D.host g (k : D.host.E) = starRingEnd ℂ (embPsi D.host g (k : D.host.E)) := rfl
  rw [e3, conj_div_norm hz, inv_zpow', ← zpow_neg, ← zpow_add₀ hu, e1, e2]
  congr 1
  beta_reduce
  rw [hk]
  ring

end GlobalTheory.LamTie.InfType
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToricLam0HasInfinityTypeConjRatioStatement
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_le_kap_and_lam0_hasInf : ∀ (D : D7) (Z : LamDat D), Z.Ok → ∀ (l : ℕ) (j a : Fin D.R.m) (s : ℕ), (s : ℤ) ≤ (BlochKatoReduction.Gen.NFun D.R : ℤ) + 1 → (∀ g, 1 ≤ Z.kap j a s g) ∧ GlobalTheory.CMVal.HasInf (Z.lam0 l j a) (phi D.host) (fun g => (Z.kap j a s g : ℤ) + s) := by
  first | exact @GlobalTheory.LamTie.InfType.toricLam0_hasInfinityType_conjRatio | exact GlobalTheory.LamTie.InfType.toricLam0_hasInfinityType_conjRatio | (intros; apply GlobalTheory.LamTie.InfType.toricLam0_hasInfinityType_conjRatio <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToricCharacterIsCMHostValueDatum
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

theorem toricCharacter_isCMHostValueDatum : ∀ (D : D7) (Z : LamDat D), Z.Ok → ∀ (l : ℕ) (j a : Fin D.R.m) (s : ℕ), 1 ≤ s → (s : ℤ) ≤ (BlochKatoReduction.Gen.NFun D.R : ℤ) + 1 → IsHostDatum D.host (phi D.host) s (Z.kap j a s) (cond0 D.host Z.w0) (Z.lam0 l j a) := by
  intro D Z hZ l j a s hs hN
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨hcm, hind⟩ := GlobalTheory.T.conjugateEmbedding_isCMType_sqrtMinusD D.R D.host
  obtain ⟨hκ, hinf⟩ := GlobalTheory.T.one_le_kap_and_lam0_hasInf D Z hZ l j a s hN
  obtain ⟨hu, ht⟩ := GlobalTheory.T.lam0_isUnitary_and_trivOnF D Z hZ l j a
  have hb : IsBaseCond (cond0 D.host Z.w0) :=
    GlobalTheory.T.isBaseCond_of_split_primes D.R D.host Z.q0 Z.w0 (fun p hp P hP => by
      obtain ⟨h1, -, h3, h4⟩ := hZ.places.splits p hp
      exact GlobalTheory.T.splitsInCMField_placeBelow_of_completelySplit D.host.E p h1 h3 h4 P hP) hZ.places
  refine ⟨hcm, hind, hs, hκ, hb, hu, ht, hinf, fun v P hP => ⟨fun h => absurd h (Finset.notMem_empty v), fun _ => ?_⟩⟩
  have hv : v = below P := HeightOneSpectrum.ext (hP.symm.trans (over_below P))
  subst hv
  exact GlobalTheory.T.lam_conductor_exponent D Z hZ l j a P

end GlobalTheory.LamTie
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToricCharacterIsCMHostValueDatumStatement
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHostDatum_kap_lam0_of_ok : ∀ (D : D7) (Z : LamDat D), Z.Ok → ∀ (l : ℕ) (j a : Fin D.R.m) (s : ℕ), 1 ≤ s → (s : ℤ) ≤ (BlochKatoReduction.Gen.NFun D.R : ℤ) + 1 → IsHostDatum D.host (phi D.host) s (Z.kap j a s) (cond0 D.host Z.w0) (Z.lam0 l j a) := by
  first | exact @GlobalTheory.LamTie.toricCharacter_isCMHostValueDatum | exact GlobalTheory.LamTie.toricCharacter_isCMHostValueDatum | (intros; apply GlobalTheory.LamTie.toricCharacter_isCMHostValueDatum <;> assumption)
end
