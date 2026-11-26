module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBlockValAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SChain
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SPrismMul

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.MemPowEqv
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

private theorem mem_eqv {R : Type} [CommRing R] (e : R ≃+* R) (P : HeightOneSpectrum R) (y : R) :
    y ∈ (HeightOneSpectrum.equivOfRingEquiv e P).asIdeal ↔ e.symm y ∈ P.asIdeal := Iff.rfl

private theorem mem_pow_eqv {R : Type} [CommRing R] (e : R ≃+* R) (P : HeightOneSpectrum R) (y : R) (n : ℕ) :
    e y ∈ (HeightOneSpectrum.equivOfRingEquiv e P).asIdeal ^ n ↔ y ∈ P.asIdeal ^ n := by
  have h : (HeightOneSpectrum.equivOfRingEquiv e P).asIdeal = Ideal.map (e : R →+* R) P.asIdeal := by
    rw [Ideal.map_comap_of_equiv]
    rfl
  rw [h, ← Ideal.map_pow, Ideal.map_comap_of_equiv, Ideal.mem_comap]
  simp

private theorem intVal_eqv {R : Type} [CommRing R] [IsDedekindDomain R] (e : R ≃+* R) (P : HeightOneSpectrum R) (y : R) :
    (HeightOneSpectrum.equivOfRingEquiv e P).intValuation (e y) = P.intValuation y := by
  set Q := HeightOneSpectrum.equivOfRingEquiv e P
  have key : ∀ n : ℕ, Q.intValuation (e y) ≤ WithZero.exp (-(n : ℤ)) ↔
      P.intValuation y ≤ WithZero.exp (-(n : ℤ)) := by
    intro n
    rw [HeightOneSpectrum.intValuation_le_pow_iff_dvd, HeightOneSpectrum.intValuation_le_pow_iff_dvd,
      Ideal.dvd_iff_le, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem,
      Ideal.span_singleton_le_iff_mem]
    exact mem_pow_eqv e P y n
  by_cases hy : y = 0
  · simp [hy]
  have hey : e y ≠ 0 := by simpa using hy
  have form : ∀ (v : HeightOneSpectrum R) (r : R), r ≠ 0 →
      ∃ m : ℕ, v.intValuation r = WithZero.exp (-(m : ℤ)) :=
    fun v r hr => ⟨_, by rw [HeightOneSpectrum.intValuation_def, if_neg hr]⟩
  obtain ⟨m1, h1⟩ := form Q _ hey
  obtain ⟨m2, h2⟩ := form P _ hy
  rw [h1, h2] at key ⊢
  have a := (key m1).1 le_rfl
  have b := (key m2).2 le_rfl
  rw [WithZero.exp_le_exp] at a b
  have : m1 = m2 := by omega
  rw [this]

theorem UpperTheory.V.ZK.Cl.cAct :
    UpperTheory.V.ZK.Cl.CAct := by
  intro L F _ _ _ _ _
  have val : ∀ (σ : Gal(F/L)) (P : HeightOneSpectrum (𝓞 F)) (x : F),
      HeightOneSpectrum.valuation F (actP σ P) (σ x) = HeightOneSpectrum.valuation F P x := by
    intro σ P x
    obtain ⟨p, q, -, hpq⟩ := IsFractionRing.div_surjective (𝓞 F) x
    have hpq' : (p : F) / q = x := hpq
    have hσ : ∀ a : 𝓞 F, σ (a : F) = ((RingOfIntegers.mapRingEquiv σ.toRingEquiv a : 𝓞 F) : F) :=
      fun a => by rw [RingOfIntegers.mapRingEquiv_apply]; rfl
    rw [← hpq', map_div₀, hσ, hσ, map_div₀, map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.valuation_of_algebraMap]
    unfold actP
    rw [intVal_eqv, intVal_eqv]
  have sym : ∀ (σ : Gal(F/L)) (y : 𝓞 F),
      (((RingOfIntegers.mapRingEquiv σ.toRingEquiv).symm y : 𝓞 F) : F) = σ.symm (y : F) := by
    intro σ y
    apply σ.injective
    rw [AlgEquiv.apply_symm_apply]
    have := RingOfIntegers.mapRingEquiv_apply σ.toRingEquiv
      ((RingOfIntegers.mapRingEquiv σ.toRingEquiv).symm y)
    rw [RingEquiv.apply_symm_apply] at this
    exact this.symm
  have memA : ∀ (σ : Gal(F/L)) (P : HeightOneSpectrum (𝓞 F)) (y : 𝓞 F),
      y ∈ (actP σ P).asIdeal ↔ (RingOfIntegers.mapRingEquiv σ.toRingEquiv).symm y ∈ P.asIdeal :=
    fun σ P y => mem_eqv _ P y
  refine ⟨val, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro σ τ P
    apply HeightOneSpectrum.ext
    ext y
    rw [memA, memA, memA]
    have h : (((RingOfIntegers.mapRingEquiv (σ * τ).toRingEquiv).symm y : 𝓞 F) : F) =
        (((RingOfIntegers.mapRingEquiv τ.toRingEquiv).symm
          ((RingOfIntegers.mapRingEquiv σ.toRingEquiv).symm y) : 𝓞 F) : F) := by
      rw [sym, sym, sym]
      rfl
    rw [show (RingOfIntegers.mapRingEquiv (σ * τ).toRingEquiv).symm y =
        (RingOfIntegers.mapRingEquiv τ.toRingEquiv).symm
          ((RingOfIntegers.mapRingEquiv σ.toRingEquiv).symm y) from by exact_mod_cast h]
  · intro P
    apply HeightOneSpectrum.ext
    ext y
    rw [memA]
    have h : (((RingOfIntegers.mapRingEquiv (1 : Gal(F/L)).toRingEquiv).symm y : 𝓞 F) : F) =
        (y : F) := by
      rw [sym]
      rfl
    rw [show (RingOfIntegers.mapRingEquiv (1 : Gal(F/L)).toRingEquiv).symm y = y from by
      exact_mod_cast h]
  · intro σ P b
    rw [memA]
    have h1 : algebraMap (𝓞 L) F b = ((algebraMap (𝓞 L) (𝓞 F) b : 𝓞 F) : F) := by
      rw [IsScalarTower.algebraMap_apply (𝓞 L) (𝓞 F) F]
    have h2 : algebraMap (𝓞 L) F b = algebraMap L F (b : L) := by
      rw [IsScalarTower.algebraMap_apply (𝓞 L) L F]
    have hc : ((algebraMap (𝓞 L) (𝓞 F) b : 𝓞 F) : F) = algebraMap L F (b : L) := by
      rw [← h1, h2]
    have h : (((RingOfIntegers.mapRingEquiv σ.toRingEquiv).symm (algebraMap (𝓞 L) (𝓞 F) b) : 𝓞 F) : F)
        = ((algebraMap (𝓞 L) (𝓞 F) b : 𝓞 F) : F) := by
      rw [sym, hc, AlgEquiv.commutes]
    rw [show (RingOfIntegers.mapRingEquiv σ.toRingEquiv).symm (algebraMap (𝓞 L) (𝓞 F) b) =
        algebraMap (𝓞 L) (𝓞 F) b from by exact_mod_cast h]
  · intro σ P α
    unfold ordP
    have : ((actU σ α : Fˣ) : F) = σ (α : F) := rfl
    rw [this, val]
  · intro P α β
    unfold ordP
    rw [Units.val_mul, map_mul, WithZero.log_mul (by simp) (by simp)]
    ring
  · intro P α n
    unfold ordP
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, WithZero.log_zpow, smul_eq_mul]
    ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CRes
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

private theorem exists_pow_mul_isIntegral_of_valuation_le_one_away {F : Type} [Field F] [NumberField F] (c : 𝓞 F) (x : F)
    (h : ∀ P : HeightOneSpectrum (𝓞 F), c ∉ P.asIdeal → HeightOneSpectrum.valuation F P x ≤ 1) :
    ∃ n : ℕ, ∃ a : 𝓞 F, (c : F) ^ n * x = a := by
  obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (𝓞 F) x
  have hpq' : (p : F) / q = x := hpq
  have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
  have hq0' : (q : F) ≠ 0 := by exact_mod_cast hq0
  let T : Ideal (𝓞 F) := (LinearMap.range (Algebra.linearMap (𝓞 F) F)).comap
    (LinearMap.toSpanSingleton (𝓞 F) F x)
  have memT : ∀ y : 𝓞 F, y ∈ T ↔ ∃ a : 𝓞 F, (y : F) * x = a := by
    intro y
    simp only [T, Submodule.mem_comap, LinearMap.mem_range, LinearMap.toSpanSingleton_apply,
      Algebra.linearMap_apply, Algebra.smul_def]
    constructor <;> rintro ⟨a, ha⟩ <;> exact ⟨a, ha.symm⟩
  have hqT : q ∈ T := (memT q).2 ⟨p, by rw [← hpq']; field_simp⟩
  have hrad : c ∈ T.radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro P ⟨hTP, hP⟩
    by_contra hc
    have hPne : P ≠ ⊥ := by
      intro h0
      have := hTP hqT
      rw [h0] at this
      exact hq0 (Ideal.mem_bot.1 this)
    let v : HeightOneSpectrum (𝓞 F) := ⟨P, hP, hPne⟩
    have hv := h v hc
    have hspan : Ideal.span {q} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact hq0
    have hPunit : ¬ IsUnit P := by
      rw [Ideal.isUnit_iff]
      exact hP.ne_top
    obtain ⟨n, J, hPJ, hJ⟩ := WfDvdMonoid.max_power_factor' hspan hPunit
    rw [Ideal.dvd_iff_le] at hPJ
    obtain ⟨s, hsJ, hsP⟩ := Set.not_subset.1 hPJ
    have hvq : v.intValuation q ≤ WithZero.exp (-(n : ℤ)) :=
      (v.intValuation_le_pow_iff_dvd q n).2 ⟨J, hJ⟩
    have hq' : v.intValuation q ≠ 0 := by
      rw [← v.valuation_of_algebraMap (K := F)]
      simpa using hq0'
    have hvp : v.intValuation p ≤ WithZero.exp (-(n : ℤ)) := by
      have hx : HeightOneSpectrum.valuation F v x = v.intValuation p / v.intValuation q := by
        rw [← hpq', map_div₀, v.valuation_of_algebraMap, v.valuation_of_algebraMap]
      rw [hx, div_le_one₀ (zero_lt_iff.2 hq')] at hv
      exact hv.trans hvq
    have hpn := (v.intValuation_le_pow_iff_dvd p n).1 hvp
    rw [Ideal.dvd_iff_le] at hpn
    have hps : p * s ∈ Ideal.span {q} := by
      rw [hJ]
      exact Ideal.mul_mem_mul (hpn (Ideal.mem_span_singleton_self p)) hsJ
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 hps
    have hd' : (d : F) * q = p * s := by exact_mod_cast hd
    refine hsP (hTP ((memT s).2 ⟨d, ?_⟩))
    rw [← hpq']
    field_simp
    linear_combination -hd'
  obtain ⟨n, hn⟩ := hrad
  obtain ⟨a, ha⟩ := (memT _).1 hn
  exact ⟨n, a, by push_cast at ha; exact ha⟩

theorem UpperTheory.V.ZK.Cl.cRes :
    UpperTheory.V.ZK.Cl.CRes := by
  intro L F _ _ _ _ _ k _ r
  have uniq : ∀ (x : F) (u u' : k), ResF r x u → ResF r x u' → u = u' := by
    rintro x u u' ⟨a, b, hb, hx, hu⟩ ⟨a', b', hb', hx', hu'⟩
    have h1 : a * b' = a' * b := by
      have : (a : F) * b' = a' * b := by
        rw [← hx, ← hx']
        ring
      exact_mod_cast this
    have h2 := congrArg r h1
    rw [map_mul, map_mul, hu, hu'] at h2
    have h3 : (u - u') * (r b * r b') = 0 := by linear_combination h2
    rcases mul_eq_zero.1 h3 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h (mul_ne_zero hb hb')
  have base : ∀ a : 𝓞 F, ResF r (a : F) (r a) := fun a => ⟨a, 1, by simp, by simp, by simp⟩
  have arith : ∀ (x y : F) (u w : k), ResF r x u → ResF r y w →
      ResF r (x + y) (u + w) ∧ ResF r (x * y) (u * w) := by
    rintro x y u w ⟨a, b, hb, hx, hu⟩ ⟨a', b', hb', hy, hw⟩
    refine ⟨⟨a * b' + a' * b, b * b', by simpa using mul_ne_zero hb hb', ?_, ?_⟩,
      ⟨a * a', b * b', by simpa using mul_ne_zero hb hb', ?_, ?_⟩⟩
    · have e : ((a * b' + a' * b : 𝓞 F) : F) = (a : F) * b' + a' * b := by push_cast; rfl
      have e' : ((b * b' : 𝓞 F) : F) = (b : F) * b' := by push_cast; rfl
      rw [e, e', ← hx, ← hy]
      ring
    · simp only [map_add (f := _), map_mul, hu, hw]
      ring
    · have e : ((a * a' : 𝓞 F) : F) = (a : F) * a' := by push_cast; rfl
      have e' : ((b * b' : 𝓞 F) : F) = (b : F) * b' := by push_cast; rfl
      rw [e, e', ← hx, ← hy]
      ring
    · simp only [map_mul, hu, hw]
      ring
  have integ : ∀ b : 𝓞 L, r (algebraMap (𝓞 L) (𝓞 F) b) ≠ 0 → ∀ x : F,
      (∀ P : HeightOneSpectrum (𝓞 F), algebraMap (𝓞 L) (𝓞 F) b ∉ P.asIdeal →
        HeightOneSpectrum.valuation F P x ≤ 1) →
      (∃ n, ∃ a : 𝓞 F, algebraMap (𝓞 L) F b ^ n * x = a) ∧ ∃ u, ResF r x u := by
    intro b hb x hx
    obtain ⟨n, a, ha⟩ := exists_pow_mul_isIntegral_of_valuation_le_one_away _ x hx
    have hcast : algebraMap (𝓞 L) F b = ((algebraMap (𝓞 L) (𝓞 F) b : 𝓞 F) : F) := by
      rw [IsScalarTower.algebraMap_apply (𝓞 L) (𝓞 F) F]
    refine ⟨⟨n, a, by rw [hcast]; exact ha⟩, ⟨r a / r (algebraMap (𝓞 L) (𝓞 F) b ^ n), a,
      algebraMap (𝓞 L) (𝓞 F) b ^ n, by rw [map_pow]; exact pow_ne_zero _ hb, ?_, ?_⟩⟩
    · have e : ((algebraMap (𝓞 L) (𝓞 F) b ^ n : 𝓞 F) : F)
          = ((algebraMap (𝓞 L) (𝓞 F) b : 𝓞 F) : F) ^ n := by push_cast; rfl
      rw [e, mul_comm]
      exact ha
    · rw [div_mul_cancel₀]
      rw [map_pow]
      exact pow_ne_zero _ hb
  refine ⟨uniq, base, arith, fun b hb => ⟨integ b hb, ?_⟩⟩
  intro α hα
  have hval : ∀ P : HeightOneSpectrum (𝓞 F), algebraMap (𝓞 L) (𝓞 F) b ∉ P.asIdeal →
      HeightOneSpectrum.valuation F P (α : F) = 1 := by
    intro P hP
    have h0 := hα P hP
    unfold ordP at h0
    have hne : HeightOneSpectrum.valuation F P (α : F) ≠ 0 := by simp
    rw [← WithZero.exp_log hne]
    have : (HeightOneSpectrum.valuation F P (α : F)).log = 0 := by linarith
    rw [this]
    rfl
  obtain ⟨-, u, hu⟩ := integ b hb (α : F) (fun P hP => (hval P hP).le)
  obtain ⟨-, u', hu'⟩ := integ b hb ((α⁻¹ : Fˣ) : F) (fun P hP => by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hval P hP, inv_one])
  have hmul := (arith _ _ _ _ hu hu').2
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one] at hmul
  have h1 : ResF r (1 : F) 1 := by simpa using base 1
  have huu : u * u' = 1 := uniq _ _ _ hmul h1
  exact ⟨⟨u, u', huu, by rw [mul_comm]; exact huu⟩, hu⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CSupp
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

theorem UpperTheory.V.ZK.Cl.cSupp :
    UpperTheory.V.ZK.Cl.CSupp := by
  intro L F _ _ _ _ _ 𝔡 b₀ hb₀
  refine ⟨b₀ * ∏ P ∈ 𝔡.support, ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 L), ?_, dvd_mul_right _ _, ?_⟩
  · refine mul_ne_zero hb₀ (Finset.prod_ne_zero_iff.mpr fun P _ => ?_)
    have h : Ideal.absNorm P.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot
    exact_mod_cast h
  · intro P hP
    rw [map_mul, map_prod]
    apply Ideal.mul_mem_left
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem
      (fun Q : HeightOneSpectrum (𝓞 F) =>
        algebraMap (𝓞 L) (𝓞 F) ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 L))
      (Finsupp.mem_support_iff.mpr hP)
    rw [hc]
    apply Ideal.mul_mem_right
    rw [map_natCast]
    exact Ideal.absNorm_mem P.asIdeal
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CTriv
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

theorem UpperTheory.V.ZK.Cl.cTriv :
    UpperTheory.V.ZK.Cl.CTriv := by
  intro k _ A _ m θ hθ H V P U
  intro _ _ _ _ _ _ _ _ _ _ μ φ z hz
  obtain ⟨-, hnat, hcomp, -, hsub⟩ := sChain A
  have cyc : ∀ {G G' : Type} [Group G] [Group G'] (f : G →* G') (w : Ch A G (m + 1)),
      Cyc w → Cyc (cm A f (m + 1) w) := by
    intro G G' _ _ f w hw
    unfold Cyc at hw ⊢
    rw [hnat, hw, map_zero]
  rw [hcomp, hθ.iso (V × P) U φ _ (cyc _ _ hz), hθ.add H V P μ 1 z hz]
  have htriv : (θ P) (cm A (1 : H →* P ≃ₗ[k] P) (m + 1) z) = 0 := by
    apply hθ.bdry
    have hf : (1 : H →* P ≃ₗ[k] P) = (1 : Unit →* P ≃ₗ[k] P).comp (1 : H →* Unit) := by
      ext h x
      rfl
    rw [hf, hcomp]
    obtain ⟨w, hw⟩ := hsub Unit m _ (cyc (1 : H →* Unit) z hz)
    rw [← hw, ← hnat]
    exact ⟨_, rfl⟩
  rw [htriv, add_zero]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CChain
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

theorem UpperTheory.V.ZK.Cl.cChain :
    UpperTheory.V.ZK.Cl.CChain := by
  unfold UpperTheory.V.ZK.Cl.CChain
  intro A _ C D G _ _ _ ι _ m H ρ d n z g t₀ hz hB hc hρ hσ hg
  obtain ⟨-, h1, h2, h3, -⟩ := sChain A
  have hz' : bd A C m z = 0 := hz
  have hcyc : ∀ (K : Type) [Group K] (f : C →* K), bd A K m (cm A f (m + 1) z) = 0 := by
    intro K _ f
    rw [h1, hz', map_zero]
  let ρH : D →* H := ρ.codRestrict H hρ
  have hσ' : ∀ x, (MulAut.conj (g t₀)⁻¹).toMonoidHom.comp ρ x ∈ H := by
    intro x
    simpa using hσ x
  let σH : D →* H := ((MulAut.conj (g t₀)⁻¹).toMonoidHom.comp ρ).codRestrict H hσ'
  let k : ι → H := fun t => (⟨(g t)⁻¹ * g t₀, hg t⟩ : H)⁻¹
  obtain ⟨b, hb⟩ := LinearMap.mem_range.mp hB
  have hconj : ∀ t, (MulAut.conj (k t)⁻¹).toMonoidHom.comp (σH.comp (d t)) = ρH.comp (d t) := by
    intro t
    ext c
    have e := (hc t c).eq
    simp [σH, ρH, k]
    calc _ = (g t)⁻¹ * (ρ (d t c) * g t) := by group
      _ = ρ (d t c) := by rw [← e]; group
  refine ⟨cm A σH (m + 2) b - cm A ρH (m + 2) b + ∑ t, n t • prism A (k t) (m + 1) (cm A (σH.comp (d t)) (m + 1) z), ?_, ?_⟩
  · show bd A H (m + 1) _ = 0
    have hp : ∀ t, bd A H (m + 1) (prism A (k t) (m + 1) (cm A (σH.comp (d t)) (m + 1) z)) = cm A (ρH.comp (d t)) (m + 1) z - cm A (σH.comp (d t)) (m + 1) z := by
      intro t
      have e := sPrism A H (k t) m (cm A (σH.comp (d t)) (m + 1) z)
      rw [hcyc, map_zero, add_zero, ← h2] at e
      rw [e, hconj t]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), map_sub, map_sum, h1, h1, hb]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_smul, hp, map_sum, ← h2, smul_sub, Finset.sum_sub_distrib]
    abel
  · have hk : ∀ t, H.subtype (k t) = (g t₀)⁻¹ * g t := by
      intro t
      simp [k]
    have hincl1 : H.subtype.comp σH = (MulAut.conj (g t₀)⁻¹).toMonoidHom.comp ρ := by
      ext x
      rfl
    have hincl2 : H.subtype.comp ρH = ρ := by
      ext x
      rfl
    have hincl3 : ∀ t, H.subtype.comp (σH.comp (d t)) = (MulAut.conj (g t₀)⁻¹).toMonoidHom.comp (ρ.comp (d t)) := by
      intro t
      ext x
      rfl
    have hx : ∀ t, Cyc (cm A (ρ.comp (d t)) (m + 1) z) := fun t => hcyc G _
    choose e he using fun t => LinearMap.mem_range.mp (sPrismMul A G (g t₀) ((g t₀)⁻¹ * g t) m _ (hx t))
    have hS := sPrism A G (g t₀) (m + 1) (cm A ρ (m + 2) b)
    rw [h1, hb, ← h2] at hS
    refine LinearMap.mem_range.mpr ⟨prism A (g t₀) (m + 2) (cm A ρ (m + 2) b) - ∑ t, n t • e t, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum, eq_sub_of_add_eq hS]
    simp only [map_smul, he, mul_inv_cancel_left]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_sub, map_sum, map_smul, h3, hk, ← h2, hincl1, hincl2, hincl3]
    simp only [smul_sub, Finset.sum_sub_distrib]
    abel
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CSplit
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

private theorem dualFam (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] :
    ∃ (n : ℕ) (e f : Fin n → 𝓞 F) (b : 𝓞 L), b ≠ 0 ∧ ∀ x : F,
      algebraMap L F b * x = ∑ i, algebraMap L F (Algebra.trace L F (x * f i)) * e i := by
  classical
  let B := Module.finBasis L F
  obtain ⟨m, hm, hi⟩ := exists_integral_multiples ℤ ℚ (L := F)
    (Finset.univ.image B ∪ Finset.univ.image B.traceDual)
  refine ⟨_, fun i => ⟨m • B.traceDual i, hi _ (by simp)⟩, fun i => ⟨m • B i, hi _ (by simp)⟩,
    (m : 𝓞 L) ^ 2, pow_ne_zero _ (Int.cast_ne_zero.2 hm), fun x => ?_⟩
  have h := B.traceDual.sum_repr x
  conv_lhs => rw [← h]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply, Algebra.smul_def]
  change _ = algebraMap L F (Algebra.trace L F (x * (m • B i))) * (m • B.traceDual i)
  rw [mul_smul_comm m x, map_zsmul, map_zsmul]
  simp only [zsmul_eq_mul, map_pow, map_intCast]
  ring

private theorem orth {L F : Type} [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] [IsGalois L F]
    {n : ℕ} (e f : Fin n → F) (b : L)
    (h : ∀ x : F, algebraMap L F b * x = ∑ i, algebraMap L F (Algebra.trace L F (x * f i)) * e i)
    (σ τ : F ≃ₐ[L] F) [Decidable (τ = σ)] : ∑ i, τ (f i) * σ (e i) = if τ = σ then algebraMap L F b else 0 := by
  classical
  have hli := (linearIndependent_monoidHom F F).comp (fun ρ : F ≃ₐ[L] F => (ρ : F →* F))
    (fun ρ ρ' hh => AlgEquiv.ext fun x => DFunLike.congr_fun hh x)
  have := (Fintype.linearIndependent_iffₛ.1 hli) (fun ρ => ∑ i, ρ (f i) * σ (e i))
    (fun ρ => if ρ = σ then algebraMap L F b else 0) (by
      funext x
      have h1 := congrArg σ (h x)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_mul, map_sum, AlgEquiv.commutes] at h1
      simp only [trace_eq_sum_automorphisms, map_mul, Finset.sum_mul] at h1
      rw [Finset.sum_comm] at h1
      simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, ite_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, MonoidHom.coe_coe, Finset.sum_mul]
      rw [h1]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring) τ
  convert this

theorem UpperTheory.V.ZK.Cl.cSplit :
    UpperTheory.V.ZK.Cl.CSplit := by
  classical
  intro L F _ _ _ _ _ hG
  obtain ⟨n, e, f, b, hb, h⟩ := dualFam L F
  refine ⟨b, hb, fun k _ _ r hr hrb => ⟨fun v => ?_, fun a ha => ?_⟩⟩
  · choose s hs using hr
    have hs' : ∀ y, r (algebraMap (𝓞 L) (𝓞 F) (s y)) = y := hs
    have hσ : ∀ (σ : F ≃ₐ[L] F) (c : 𝓞 L), actO σ (algebraMap (𝓞 L) (𝓞 F) c) = algebraMap (𝓞 L) (𝓞 F) c :=
      fun σ c => RingOfIntegers.ext (σ.commutes (c : L))
    have ho : ∀ σ τ : F ≃ₐ[L] F, ∑ i, actO τ (f i) * actO σ (e i) =
        if τ = σ then algebraMap (𝓞 L) (𝓞 F) b else 0 := by
      intro σ τ
      apply RingOfIntegers.ext
      have := orth (fun i => (e i : F)) (fun i => (f i : F)) (b : L) h σ τ
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul]
      refine this.trans ?_
      split_ifs
      · rfl
      · simp
    refine ⟨∑ i, algebraMap (𝓞 L) (𝓞 F)
      (s (∑ τ, (r (algebraMap (𝓞 L) (𝓞 F) b))⁻¹ * v τ * r (actO τ (f i)))) * e i, fun σ => ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, hσ, hs', Finset.sum_mul]
    rw [Finset.sum_comm]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [mul_assoc, ← Finset.mul_sum, ← map_mul, ← map_sum, ho]
    simp only [apply_ite r, map_zero, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    field_simp
  · let c : Fin n → 𝓞 L := fun i => ⟨Algebra.trace L F (a * f i),
      Algebra.isIntegral_trace (R := ℤ) (a * f i).isIntegral_coe⟩
    have hc : ∀ i, algebraMap (𝓞 L) (𝓞 F) (c i) = ∑ σ : F ≃ₐ[L] F, actO σ a * actO σ (f i) := by
      intro i
      apply RingOfIntegers.ext
      have := trace_eq_sum_automorphisms (K := L) ((a : F) * f i)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul] at this ⊢
      exact this
    have hba : algebraMap (𝓞 L) (𝓞 F) b * a = ∑ i, algebraMap (𝓞 L) (𝓞 F) (c i) * e i := by
      apply RingOfIntegers.ext
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul]
      exact h a
    obtain ⟨b', hb'⟩ := hr (r (algebraMap (𝓞 L) (𝓞 F) b))⁻¹
    have h1 : a = algebraMap (𝓞 L) (𝓞 F) (1 - b' * b) * a +
        algebraMap (𝓞 L) (𝓞 F) b' * ∑ i, algebraMap (𝓞 L) (𝓞 F) (c i) * e i := by
      rw [← hba, map_sub, map_mul, map_one]; ring
    rw [h1]
    refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_))
      (Ideal.mul_mem_left _ _ (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)))
    · rw [RingHom.mem_ker, map_sub, map_mul, map_one, hb', RingHom.comp_apply, inv_mul_cancel₀ hrb, sub_self]
    · rw [RingHom.mem_ker, RingHom.comp_apply, hc]
      simp [ha]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CLatLoc
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

private theorem pow_mul_exp_le_exp_neg_of_le_exp_neg_one (n : ℕ) (k a : ℤ) (h : k + a ≤ n) (v : WithZero (Multiplicative ℤ))
    (hv : v ≤ WithZero.exp (-1)) : v ^ n * WithZero.exp k ≤ WithZero.exp (-a) := by
  calc v ^ n * WithZero.exp k ≤ WithZero.exp (-1) ^ n * WithZero.exp k := by gcongr
    _ = WithZero.exp (k - n) := by
      rw [← WithZero.exp_nsmul, ← WithZero.exp_add]
      congr 1
      simp
      ring
    _ ≤ WithZero.exp (-a) := by
      rw [WithZero.exp_le_exp]
      omega

private theorem algebraMap_coe_ringOfIntegers_tower {L F : Type} [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F]
    (b : 𝓞 L) : algebraMap L F (algebraMap (𝓞 L) L b) = algebraMap (𝓞 F) F (algebraMap (𝓞 L) (𝓞 F) b) := by
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

private theorem valuation_eq_one_of_not_mem_asIdeal {F : Type} [Field F] [NumberField F] (P : HeightOneSpectrum (𝓞 F)) (β : 𝓞 F)
    (h : β ∉ P.asIdeal) : HeightOneSpectrum.valuation F P (algebraMap (𝓞 F) F β) = 1 := by
  rw [HeightOneSpectrum.valuation_of_algebraMap, P.intValuation_eq_one_iff_mem_primeCompl]
  exact h

private theorem valuation_le_exp_neg_one_of_mem_asIdeal {F : Type} [Field F] [NumberField F] (P : HeightOneSpectrum (𝓞 F)) (β : 𝓞 F)
    (h : β ∈ P.asIdeal) : HeightOneSpectrum.valuation F P (algebraMap (𝓞 F) F β) ≤ WithZero.exp (-1) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  have := (P.intValuation_le_pow_iff_mem β 1).mpr (by simpa using h)
  simpa using this

private theorem inLoc_of_inLat_pow_smul {L F : Type} [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F]
    {J : Type} (b : 𝓞 L) (𝔞 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ)
    (h𝔞 : ∀ j P, 𝔞 j P ≠ 0 → algebraMap (𝓞 L) (𝓞 F) b ∈ P.asIdeal) (n : ℕ) (x : J → F)
    (hx : InLat 𝔞 ((algebraMap (𝓞 L) L b) ^ n • x)) : InLoc b x := by
  intro j P hP
  have h0 : 𝔞 j P = 0 := by
    by_contra h
    exact hP (h𝔞 j P h)
  have hv := hx j P
  rw [Pi.smul_apply, Algebra.smul_def, map_pow, algebraMap_coe_ringOfIntegers_tower, Valuation.map_mul, Valuation.map_pow,
    valuation_eq_one_of_not_mem_asIdeal P _ hP, one_pow, one_mul, h0, neg_zero, WithZero.exp_zero] at hv
  exact hv

private theorem exists_inLat_pow_smul_of_inLoc {L F : Type} [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F]
    {J : Type} [Fintype J] (b : 𝓞 L) (hb : b ≠ 0) (𝔞 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ)
    (h𝔞 : ∀ j P, 𝔞 j P ≠ 0 → algebraMap (𝓞 L) (𝓞 F) b ∈ P.asIdeal) (x : J → F)
    (hx : InLoc b x) : ∃ n : ℕ, InLat 𝔞 ((algebraMap (𝓞 L) L b) ^ n • x) := by
  classical
  have hβ0 : algebraMap (𝓞 L) (𝓞 F) b ≠ 0 := by
    intro h
    apply hb
    apply FaithfulSMul.algebraMap_injective (𝓞 L) L
    apply (algebraMap L F).injective
    rw [algebraMap_coe_ringOfIntegers_tower, h]
    simp
  have hS : {P : HeightOneSpectrum (𝓞 F) | algebraMap (𝓞 L) (𝓞 F) b ∈ P.asIdeal}.Finite := by
    simp_rw [← Ideal.dvd_span_singleton]
    apply Ideal.finite_factors
    simpa only [Submodule.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot]
  refine ⟨∑ p ∈ (Finset.univ : Finset J) ×ˢ hS.toFinset,
    (WithZero.log (HeightOneSpectrum.valuation F p.2 (x p.1)) + 𝔞 p.1 p.2).toNat, fun j P => ?_⟩
  rw [Pi.smul_apply, Algebra.smul_def, map_pow, algebraMap_coe_ringOfIntegers_tower, Valuation.map_mul, Valuation.map_pow]
  by_cases hP : algebraMap (𝓞 L) (𝓞 F) b ∈ P.asIdeal
  · by_cases hxj : x j = 0
    · simp [hxj]
    · have hne : HeightOneSpectrum.valuation F P (x j) ≠ 0 := by simpa using hxj
      rw [← WithZero.exp_log hne]
      apply pow_mul_exp_le_exp_neg_of_le_exp_neg_one _ _ _ _ _ (valuation_le_exp_neg_one_of_mem_asIdeal P _ hP)
      have hmem : (j, P) ∈ (Finset.univ : Finset J) ×ˢ hS.toFinset :=
        Finset.mem_product.mpr ⟨Finset.mem_univ _, hS.mem_toFinset.mpr hP⟩
      have hle := Finset.single_le_sum (f := fun p : J × HeightOneSpectrum (𝓞 F) =>
        (WithZero.log (HeightOneSpectrum.valuation F p.2 (x p.1)) + 𝔞 p.1 p.2).toNat)
        (fun _ _ => Nat.zero_le _) hmem
      have h1 := Int.self_le_toNat (WithZero.log (HeightOneSpectrum.valuation F P (x j)) + 𝔞 j P)
      have h2 : ((WithZero.log (HeightOneSpectrum.valuation F P (x j)) + 𝔞 j P).toNat : ℤ) ≤
          ((∑ p ∈ (Finset.univ : Finset J) ×ˢ hS.toFinset,
            (WithZero.log (HeightOneSpectrum.valuation F p.2 (x p.1)) + 𝔞 p.1 p.2).toNat : ℕ) : ℤ) := by
        exact_mod_cast hle
      omega
  · have h0 : 𝔞 j P = 0 := by
      by_contra h
      exact hP (h𝔞 j P h)
    rw [valuation_eq_one_of_not_mem_asIdeal P _ hP, one_pow, one_mul, h0, neg_zero, WithZero.exp_zero]
    exact hx j P hP

theorem UpperTheory.V.ZK.Cl.cLatLoc :
    UpperTheory.V.ZK.Cl.CLatLoc := by
  intro L F _ _ _ _ _ J _ b hb 𝔞 𝔟 h𝔞 h𝔟 g hg
  show ∀ x, InLoc b x ↔ InLoc b (g x)
  intro x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := exists_inLat_pow_smul_of_inLoc b hb 𝔞 h𝔞 x hx
    apply inLoc_of_inLat_pow_smul b 𝔟 h𝔟 n
    rw [← map_smul]
    exact (hg _).mp hn
  · intro hx
    obtain ⟨n, hn⟩ := exists_inLat_pow_smul_of_inLoc b hb 𝔟 h𝔟 (g x) hx
    apply inLoc_of_inLat_pow_smul b 𝔞 h𝔞 n
    rw [hg, map_smul]
    exact hn
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBetaVal
open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

private theorem map_finset_prod_eq_sum_of_add_hom_on_subgroup {F M ι : Type} [Field F] [AddCommMonoid M] (U : Subgroup Fˣ)
    (f : Fˣ → M) (hf : ∀ x ∈ U, ∀ y ∈ U, f (x * y) = f x + f y) (hf1 : f 1 = 0)
    (s : Finset ι) (g : ι → Fˣ) (hg : ∀ i ∈ s, g i ∈ U) :
    f (∏ i ∈ s, g i) = ∑ i ∈ s, f (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hf1]
  | @insert a s ha ih =>
    have hs : ∀ i ∈ s, g i ∈ U := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      hf _ (hg a (Finset.mem_insert_self a s)) _ (Subgroup.prod_mem U hs), ih hs]

private theorem sum_eq_sum_range_pow_of_cyclic_generator {G M : Type} [Group G] [Fintype G] [AddCommMonoid M] (γ : G)
    (hγ : ∀ σ : G, σ ∈ Subgroup.zpowers γ) (g : G → M) :
    ∑ σ, g σ = ∑ j ∈ Finset.range (orderOf γ), g (γ ^ j) := by
  classical
  have hfin : IsOfFinOrder γ := isOfFinOrder_of_finite γ
  symm
  refine Finset.sum_nbij (fun j => γ ^ j) (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
  · intro i hi j hj hij
    exact pow_injOn_Iio_orderOf (by simpa using hi) (by simpa using hj) hij
  · intro σ _
    have h := hfin.mem_powers_iff_mem_zpowers.mpr (hγ σ)
    rw [hfin.mem_powers_iff_mem_range_orderOf] at h
    simpa using h

theorem UpperTheory.V.ZK.Cl.cBetaVal :
    UpperTheory.V.ZK.Cl.CBetaVal := by
  intro L F _ _ _ _ _ l c ν E _ ζ γ hL kap hk U f hU hf α hα p
  set z := toF ζ with hzdef
  have hz : IsPrimitiveRoot z (l ^ ν) :=
    hL.prim.map_of_injective (Units.map_injective RingOfIntegers.coe_injective)
  have hcong : ∀ m n : ℕ, z ^ m = z ^ n → (m : ZMod (l ^ ν)) = n := fun m n h =>
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr (by rw [hz.eq_orderOf]; exact pow_eq_pow_iff_modEq.mp h)
  have hact : ∀ (σ τ : Gal(F/L)) (x : Fˣ), actU (σ * τ) x = actU σ (actU τ x) :=
    fun σ τ x => Units.ext rfl
  have hkm : ∀ σ τ : Gal(F/L), ((kap (σ * τ) : ℕ) : ZMod (l ^ ν)) = kap σ * kap τ := by
    intro σ τ
    rw [← Nat.cast_mul]
    apply hcong
    rw [← hk, hact, hk, map_pow, hk, ← pow_mul]
  have hkγ : ((kap γ : ℕ) : ZMod (l ^ ν)) = 1 + (l : ZMod (l ^ ν)) ^ c := by
    have h := hcong (kap γ) (1 + l ^ c) (by
      rw [← hk]
      ext
      simpa [actU, toF, z] using hL.act)
    simpa using h
  have hk1 : ((kap 1 : ℕ) : ZMod (l ^ ν)) = 1 := by
    have h := hcong (kap 1) 1 (by rw [← hk, pow_one]; exact Units.ext rfl)
    simpa using h
  have hkpow : ∀ j : ℕ, ((kap (γ ^ j) : ℕ) : ZMod (l ^ ν)) = (1 + (l : ZMod (l ^ ν)) ^ c) ^ j := by
    intro j
    induction j with
    | zero => simpa using hk1
    | succ j ih => rw [pow_succ, hkm, ih, hkγ, pow_succ]
  have hf1 : f 1 = 0 := by
    have h := hf 1 U.one_mem 1 U.one_mem
    rw [mul_one] at h
    simpa using h
  have hfn : ∀ x ∈ U, ∀ n : ℕ, f (x ^ n) = n * f x := by
    intro x hx n
    induction n with
    | zero => simp [hf1]
    | succ n ih =>
      rw [pow_succ, hf _ (U.pow_mem hx n) _ hx, ih]
      push_cast
      ring
  have hfz : ∀ x ∈ U, ∀ n : ℤ, f (x ^ n) = n * f x := by
    intro x hx n
    obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
    · rw [zpow_natCast, hfn x hx]
      push_cast
      ring
    · have h := hf _ (U.pow_mem hx m) _ (U.inv_mem (U.pow_mem hx m))
      rw [mul_inv_cancel, hf1, hfn x hx] at h
      rw [zpow_neg, zpow_natCast]
      push_cast
      linear_combination -h
  have hUa : ∀ σ : Gal(F/L), actU σ α ∈ U := fun σ => hU σ α hα
  have hL1 : ∀ σ : Gal(F/L), f (actU σ (polAct γ p α)) =
      ∑ i ∈ Finset.range (p.natDegree + 1),
        (p.coeff i : ZMod (l ^ ν)) * f (actU (σ * (γ ^ i)⁻¹) α) := by
    intro σ
    simp only [polAct, map_prod, map_zpow]
    rw [map_finset_prod_eq_sum_of_add_hom_on_subgroup U f hf hf1 _ _ (fun i _ => U.zpow_mem (hU σ _ (hUa _)) _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hfz _ (hU σ _ (hUa _)), ← hact, inv_pow]
  set S := ∑ τ : Gal(F/L), (kap τ : ZMod (l ^ ν)) ^ E * f (actU τ α) with hSdef
  have hS : ∀ i : ℕ, ∑ σ : Gal(F/L), (kap σ : ZMod (l ^ ν)) ^ E * f (actU (σ * (γ ^ i)⁻¹) α) =
      ((1 + (l : ZMod (l ^ ν)) ^ c) ^ E) ^ i * S := by
    intro i
    rw [← (Equiv.mulRight (γ ^ i)).sum_comp, hSdef, Finset.mul_sum]
    · refine Finset.sum_congr rfl fun τ _ => ?_
      simp only [Equiv.coe_mulRight, mul_inv_cancel_right]
      rw [hkm, hkpow]
      ring
    · intro _ _
      simp
  have hR : f (nrm γ ((1 + l ^ c) ^ E) α) = S := by
    simp only [nrm]
    rw [map_finset_prod_eq_sum_of_add_hom_on_subgroup U f hf hf1 _ _ (fun j _ => U.pow_mem (hUa _) _), hSdef,
      sum_eq_sum_range_pow_of_cyclic_generator γ hL.gen]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hfn _ (hUa _), hkpow]
    push_cast
    ring
  have hE : ((eval (((1 + l ^ c) ^ E : ℕ) : ℤ) p : ℤ) : ZMod (l ^ ν)) =
      ∑ i ∈ Finset.range (p.natDegree + 1),
        (p.coeff i : ZMod (l ^ ν)) * ((1 + (l : ZMod (l ^ ν)) ^ c) ^ E) ^ i := by
    rw [eval_eq_sum_range]
    push_cast
    rfl
  rw [hE, hR, Finset.sum_mul]
  simp_rw [hL1, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_assoc, ← hS i, Finset.mul_sum]
  exact Finset.sum_congr rfl fun σ _ => by ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.RedApplyMap
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

private theorem red_apply_map {R k : Type} [CommRing R] [Field k] (r : R →+* k) (N : ℕ) (g : GL (Fin N) R)
    (x : Fin N → R) : red r N g (r ∘ x) = r ∘ (g : Matrix (Fin N) (Fin N) R).mulVec x := by
  funext j
  simp [red, RingHom.map_mulVec]

private theorem exists_ibar {R k M V : Type} [CommRing R] [Field k] [AddCommGroup M] [Module R M] [AddCommGroup V]
    [Module k V] {N : ℕ} (r : R →+* k) (hr : Function.Surjective r) (i : M →ₗ[R] (Fin N → R)) (π : M →+ V)
    (h1 : ∀ a x, π (a • x) = r a • π x) (h2 : Function.Surjective π)
    (h3 : ∀ x, π x = 0 → x ∈ RingHom.ker r • (⊤ : Submodule R M)) :
    ∃ ib : V →ₗ[k] (Fin N → k), ∀ x, ib (π x) = r ∘ i x := by
  have key : ∀ z ∈ RingHom.ker r • (⊤ : Submodule R M), r ∘ i z = 0 := by
    intro z hz
    refine Submodule.smul_induction_on hz ?_ ?_
    · intro a ha m _
      funext j
      simp [(RingHom.mem_ker).1 ha]
    · intro z w hz hw
      funext j
      have e₁ := congrFun hz j
      have e₂ := congrFun hw j
      simp only [Function.comp_apply, Pi.zero_apply] at e₁ e₂ ⊢
      rw [map_add (f := _), Pi.add_apply, map_add (f := _), e₁, e₂, add_zero]
  have wd : ∀ x y : M, π x = π y → r ∘ i x = r ∘ i y := by
    intro x y hxy
    have hz : x - y ∈ RingHom.ker r • (⊤ : Submodule R M) := h3 _ (by rw [map_sub, hxy, sub_self])
    have e := key _ hz
    funext j
    have ej := congrFun e j
    simp only [map_sub, Function.comp_apply, Pi.sub_apply, Pi.zero_apply] at ej
    exact sub_eq_zero.1 ej
  choose pre hpre using h2
  refine ⟨{ toFun := fun v => r ∘ i (pre v), map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro v w
    have e : π (pre (v + w)) = π (pre v + pre w) := by rw [map_add (f := _), hpre, hpre, hpre]
    rw [wd _ _ e, map_add (f := _)]
    funext j
    simp
  · intro c v
    obtain ⟨a, rfl⟩ := hr c
    have e : π (pre (r a • v)) = π (a • pre v) := by rw [h1, hpre, hpre]
    rw [wd _ _ e, map_smul]
    funext j
    simp
  · intro x
    exact wd _ _ (hpre _)

private theorem exists_sbar {R k M V : Type} [CommRing R] [Field k] [AddCommGroup M] [Module R M] [AddCommGroup V]
    [Module k V] {N : ℕ} (r : R →+* k) (s : (Fin N → R) →ₗ[R] M) (π : M →+ V)
    (h1 : ∀ a x, π (a • x) = r a • π x) :
    ∃ sb : (Fin N → k) →ₗ[k] V, ∀ x, sb (r ∘ x) = π (s x) := by
  refine ⟨(Pi.basisFun k (Fin N)).constr k (fun j => π (s (Pi.single j 1))), fun x => ?_⟩
  rw [Module.Basis.constr_apply_fintype]
  have hx : x = ∑ j, x j • (Pi.single j 1 : Fin N → R) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_rhs => rw [hx, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, h1]
  simp

theorem UpperTheory.V.ZK.Cl.cFree :
    UpperTheory.V.ZK.Cl.CFree := by
  intro R _ M _ _ _ _ H _ α
  obtain ⟨N, s, hs⟩ := Module.Finite.exists_fin' R M
  obtain ⟨i, hi⟩ := Module.projective_lifting_property s LinearMap.id hs
  have hsi : ∀ y, s (i y) = y := fun y => LinearMap.congr_fun hi y
  let E : H →* Module.End R (Fin N → R) :=
    { toFun := fun h => i ∘ₗ (α h).toLinearMap ∘ₗ s + (LinearMap.id - i ∘ₗ s)
      map_one' := LinearMap.ext fun x => by simp
      map_mul' := fun g h => LinearMap.ext fun x => by
        simp [hsi, map_mul, Module.End.mul_apply] }
  let lam : H →* GL (Fin N) R :=
    (Units.map (LinearMap.toMatrixAlgEquiv' :
      Module.End R (Fin N → R) ≃ₐ[R] Matrix (Fin N) (Fin N) R).toMonoidHom).comp E.toHomUnits
  refine ⟨N, lam, ?_⟩
  intro k _ r hr V _ _ π μ h1 h2 h3 h4
  obtain ⟨ib, hib⟩ := exists_ibar r hr i π h1 h2 h3
  obtain ⟨sb, hsb⟩ := exists_sbar r s π h1
  have sbib : ∀ v, sb (ib v) = v := by
    intro v
    obtain ⟨x, rfl⟩ := h2 v
    rw [hib, hsb, hsi]
  let f : (V × LinearMap.ker sb) →ₗ[k] (Fin N → k) := LinearMap.coprod ib (LinearMap.ker sb).subtype
  have hfa : ∀ w : V × LinearMap.ker sb, f w = ib w.1 + (w.2 : Fin N → k) := fun w => rfl
  have hf : Function.Bijective f := by
    constructor
    · intro w w' hww
      rw [hfa, hfa] at hww
      have e1 : w.1 = w'.1 := by
        have := congrArg sb hww
        rwa [map_add, map_add, sbib, sbib, LinearMap.mem_ker.1 w.2.2, LinearMap.mem_ker.1 w'.2.2,
          add_zero, add_zero] at this
      rw [e1] at hww
      exact Prod.ext e1 (Subtype.ext (add_left_cancel hww))
    · intro y
      refine ⟨(sb y, ⟨y - ib (sb y), ?_⟩), ?_⟩
      · rw [LinearMap.mem_ker, map_sub, sbib, sub_self]
      · rw [hfa]
        simp
  let φ := LinearEquiv.ofBijective f hf
  refine ⟨LinearMap.ker sb, φ, ?_⟩
  refine MonoidHom.ext fun h => LinearEquiv.ext fun y => ?_
  obtain ⟨x, rfl⟩ : ∃ x : Fin N → R, r ∘ x = y :=
    ⟨fun j => (hr (y j)).choose, funext fun j => (hr (y j)).choose_spec⟩
  have rhs : (cj φ) ((sumRep μ 1) h) (r ∘ x) =
      f ((μ h (φ.symm (r ∘ x)).1, (φ.symm (r ∘ x)).2)) := rfl
  have hfw : f (φ.symm (r ∘ x)) = r ∘ x := φ.apply_symm_apply (r ∘ x)
  simp only [MonoidHom.comp_apply]
  rw [rhs]
  obtain ⟨w, hw⟩ : ∃ w, φ.symm (r ∘ x) = w := ⟨_, rfl⟩
  rw [hw] at hfw ⊢
  have hyw : r ∘ x = ib w.1 + (w.2 : Fin N → k) := by
    rw [← hfa]
    exact hfw.symm
  have hv : π (s x) = w.1 := by
    rw [← hsb, hyw, map_add (f := _), sbib, LinearMap.mem_ker.1 w.2.2, add_zero]
  rw [red_apply_map]
  have hlam : ((lam h : GL (Fin N) R) : Matrix (Fin N) (Fin N) R).mulVec x = E h x := by
    show (LinearMap.toMatrix' (E h)).mulVec x = E h x
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  rw [hlam]
  have e1 : E h x = i (α h (s x)) + (x - i (s x)) := rfl
  have e2 : ∀ a b : Fin N → R, r ∘ (a + (x - b)) = r ∘ a + (r ∘ x - r ∘ b) := by
    intro a b
    funext j
    simp
  rw [e1, e2, ← hib, ← hib, h4, hv, hfa, hyw]
  abel
end
