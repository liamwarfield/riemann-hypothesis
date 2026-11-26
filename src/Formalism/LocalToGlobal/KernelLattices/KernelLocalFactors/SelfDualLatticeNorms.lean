module

public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.EmbCInjective
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.SelfDualComap
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.SelfDualFourfoldCurveIdealLattice
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.LocNormAmbOfOf
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.ConjCls
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.ExistsPeriodPairOfIsLat
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.IsTorsionPointStandardCM
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.KapAll
public import Formalism.LocalToGlobal.AlgebraicTheory.SplitPlaceScaledBound
public import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.CardTwoSidedQuotient
public import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.NormInter
public import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.NormPow

@[expose] public section

section -- merged from Formalism.LocalToGlobal.AlgebraicTheory.LocNormScale
section -- merged from Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.KerHalf
noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField IsDedekindDomain

namespace Formalism.L2.AlgTh

open Formalism.L2.Th1.H (IsReps)
open Formalism.L2.Col (Fields Sp HomE homAt divLat mulLat IsSdLat conjPrime₂ cO algebraMap_cO mem_conjP)
open Formalism.L2.Ker (Amb VCx LamC BC embH perO halfAO halfBO twist₂ expS mem_twO nat_smul_mem mem_of_forall_locP
  expS_cases expS_eq_one embH_inj homAt_le_locP_perO lf_mulLat ti_exists_lift)
open Formalism.HermitianLatticesTheory (localization₂)

namespace KH

section Emb

variable {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] {a b : ℕ}

theorem embH_smul (emb : ι → E →+* ℂ) (δ : ℂ) (r : E) (k : ℂ) (hr : ∀ τ, emb τ r = k) (x : HomE E a b) :
    embH emb δ (r • x) = k • embH emb δ x := by
  funext τ i j
  show δ * emb τ ((r • x) (Pi.single j 1) i) = k * (δ * emb τ (x (Pi.single j 1) i))
  rw [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul, hr]
  ring

theorem embH_nat (emb : ι → E →+* ℂ) (δ : ℂ) (n : ℕ) (x : HomE E a b) :
    embH emb δ ((n : E) • x) = (n : ℂ) • embH emb δ x :=
  embH_smul emb δ (n : E) (n : ℂ) (fun τ => map_natCast (emb τ) n) x

end Emb

section Loc

variable {E : Type} [Field E] [NumberField E] [StarRing E]
variable {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]

theorem smul_mem_of (M : Submodule (𝓞 E) W) {m : W} (hm : m ∈ M) (r : 𝓞 E) {e : E} (he : algebraMap (𝓞 E) E r = e) :
    e • m ∈ M := by
  subst he
  rw [algebraMap_smul]
  exact M.smul_mem r hm

theorem loc_of (M : Submodule (𝓞 E) W) (Q : HeightOneSpectrum (𝓞 E)) {z : W} (s : 𝓞 E) (hs : s ∉ Q.asIdeal)
    (hz : (algebraMap (𝓞 E) E s) • z ∈ M) : z ∈ localization₂ Q.asIdeal M := by
  refine ⟨s, hs, ?_⟩
  rw [← algebraMap_smul E s z]
  exact hz

end Loc

end KH

theorem level_kills_half_lattice : HalfKill := by
  intro X A a b S N N' c _ _ _ hc y hy
  obtain ⟨x, hx, rfl⟩ := AddSubgroup.mem_map.mp hy
  refine AddSubgroup.mem_map.mpr ⟨(c : X.E) • x, ?_, KH.embH_nat _ _ c x⟩
  show (c : X.E) • x ∈ perO A.AA N N'
  apply mem_of_forall_locP
  intro Q
  have hx' := (mem_twO (perO A.AA N N') c (expS S) x).mp hx Q
  have hc0 : (c : X.E) ≠ 0 := Nat.cast_ne_zero.mpr hc.ne'
  unfold expS at hx'
  split_ifs at hx'
  · rw [zpow_one] at hx'
    have e : (c : X.E) • x = ((c : X.E) * (c : X.E)) • ((c : X.E))⁻¹ • x := by
      rw [smul_smul, mul_assoc, mul_inv_cancel₀ hc0, mul_one]
    rw [e]
    exact KH.smul_mem_of _ hx' ((c : 𝓞 X.E) * (c : 𝓞 X.E)) (by simp)
  · rw [zpow_neg_one, inv_inv] at hx'
    exact hx'
  · rw [zpow_zero, inv_one, one_smul] at hx'
    exact KH.smul_mem_of _ hx' (c : 𝓞 X.E) (by simp)

theorem chosen_lift_killed_level : LiftKill := by
  intro X A a b S N N' c c' x hN hN' hLa hc hc' hdvd hx
  obtain ⟨-, -, -, hAU, -, -⟩ := hLa
  have hNfg : N.FG := by
    haveI := hN.1
    exact Submodule.IsLattice.fg X.E N
  have hN'sp : Submodule.span X.E (N' : Set (Sp X.E b)) = ⊤ := by
    apply Submodule.dualAnnihilator_eq_bot_iff.mp
    apply le_antisymm ?_ bot_le
    intro f hf
    let v : Sp X.E b := fun i => star (f (Pi.single i 1))
    have hpair : Formalism.L2.Col.hStd X.E b v = f := by
      apply (Pi.basisFun X.E (Fin b)).ext
      intro i
      rw [Pi.basisFun_apply, Formalism.L2.Col.hStd_apply, Finset.sum_eq_single i]
      · simp [v]
      · intro j _ hj
        simp [hj]
      · simp
    have hline (r : X.E) : r • v ∈ N' := by
      rw [← show Formalism.HermitianLatticesTheory.dual (Formalism.L2.Col.hStd X.E b) N' = N' from hN'.2,
        Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
      intro y hy
      have hy0 : Formalism.L2.Col.hStd X.E b v y = 0 := by
        rw [hpair]
        exact (Submodule.mem_dualAnnihilator f).mp hf y (Submodule.subset_span hy)
      have hz : Formalism.L2.Col.hStd X.E b y v = 0 := by
        simpa [hy0] using ((Formalism.L2.Col.hStd_isSymm (E := X.E) (n := b)).eq v y).symm
      simp [hz]
    have hv : v = 0 := by
      funext i
      change v i = 0
      by_contra hi
      let coord := (LinearMap.proj i : Sp X.E b →ₗ[X.E] X.E).restrictScalars (𝓞 X.E)
      have htop : N'.map coord = ⊤ := by
        rw [eq_top_iff]
        intro x _
        exact ⟨(x / v i) • v, hline _, div_mul_cancel₀ _ hi⟩
      have : Module.Finite (𝓞 X.E) X.E := Module.finite_def.mpr (htop ▸ hN'.1.fg.map coord)
      exact RingOfIntegers.not_isField X.E
        (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 X.E) X.E) (Field.toIsField X.E))
    rw [Submodule.mem_bot]
    simpa [hv] using hpair.symm
  have hx0 : (c' : 𝓞 X.E) • x ∈ homAt S N N' := hx
  have hxc : x ∈ divLat c (homAt S N N') := by
    obtain ⟨k, rfl⟩ := hdvd
    show ((c' * k : ℕ) : 𝓞 X.E) • x ∈ homAt S N N'
    rw [Nat.cast_mul, mul_comm, mul_smul]
    exact (homAt S N N').smul_mem _ hx0
  obtain ⟨s, hs, hsx⟩ := ti_exists_lift A.AA S N N' hNfg hN'sp hAU hc hxc
  have hL : A.IsLift S N N' c x (A.liftW S N N' c x) :=
    Classical.epsilon_spec (p := A.IsLift S N N' c x) ⟨s, ⟨c, hc, hs⟩, hsx⟩
  obtain ⟨⟨c'', hc'', hs''⟩, hsx''⟩ := hL
  refine AddSubgroup.mem_map.mpr ⟨(c' : X.E) • A.liftW S N N' c x, ?_, KH.embH_nat _ _ c' _⟩
  show (c' : X.E) • A.liftW S N N' c x ∈ perO A.AA N N'
  apply mem_of_forall_locP
  intro Q
  by_cases hQ : Q ∈ S
  · obtain ⟨-, h2⟩ := lf_mulLat S A.AA N N' hNfg hAU c hc hsx'' Q hQ
    have h3 : (c' : 𝓞 X.E) • x ∈ localization₂ Q.asIdeal (perO A.AA N N') :=
      homAt_le_locP_perO S A.AA N N' hNfg hQ (hAU Q hQ) hx0
    have e : (c' : X.E) • A.liftW S N N' c x
        = (c' : 𝓞 X.E) • (A.liftW S N N' c x - x) + (c' : 𝓞 X.E) • x := by
      rw [← smul_add, sub_add_cancel, ← algebraMap_smul X.E (c' : 𝓞 X.E), map_natCast]
    rw [e]
    exact add_mem ((localization₂ Q.asIdeal _).smul_mem _ h2) h3
  · have ht := (mem_twO (perO A.AA N N') c'' (fun Q => -expS S Q) (A.liftW S N N' c x)).mp hs'' Q
    have hc0 : (c'' : X.E) ≠ 0 := Nat.cast_ne_zero.mpr hc''.ne'
    by_cases hQ' : conjPrime₂ Q ∈ S
    · rw [show -expS S Q = 1 from by simp [expS, hQ, hQ'], zpow_one] at ht
      have e : (c' : X.E) • A.liftW S N N' c x
          = algebraMap (𝓞 X.E) X.E ((c' : 𝓞 X.E) * (c'' : 𝓞 X.E)) • ((c'' : X.E))⁻¹ • A.liftW S N N' c x := by
        rw [smul_smul, map_mul, map_natCast, map_natCast, mul_assoc, mul_inv_cancel₀ hc0, mul_one]
      rw [e]
      exact KH.smul_mem_of _ ht _ rfl
    · rw [show -expS S Q = 0 from by simp [expS, hQ, hQ'], zpow_zero, inv_one, one_smul] at ht
      exact KH.smul_mem_of _ ht (c' : 𝓞 X.E) (by simp)

namespace KH

section Arith

theorem trace_coprime (d p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hpd : ¬ p ∣ d) (π : ℂ) (hq : IsQInt d π)
    (hpp : π * conj π = p) : ∃ T : ℤ, π + conj π = T ∧ IsCoprime T (p : ℤ) := by
  obtain ⟨m, n, hπ⟩ := hq
  simp only [Formalism.L2.Th1.CM.omegaK] at hπ
  have hs : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = (d : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    simp
  have hc : conj π = (m : ℂ) + (n : ℂ) * ((1 - Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2) := by
    rw [hπ]
    simp only [map_add (f := _), map_mul, map_div₀, map_one, Complex.conj_ofReal, Complex.conj_I, map_intCast, map_ofNat]
    ring
  refine ⟨2 * m + n, ?_, ?_⟩
  · rw [hc, hπ]
    push_cast
    ring
  · have key : (((2 * m + n) ^ 2 + (d : ℤ) * n ^ 2 : ℤ) : ℂ) = ((4 * (p : ℤ) : ℤ) : ℂ) := by
      push_cast
      rw [← hpp, hc, hπ]
      linear_combination (-(n : ℂ) ^ 2) * hs + ((n : ℂ) ^ 2 * ((Real.sqrt d : ℝ) : ℂ) ^ 2) * Complex.I_sq
    have key' : (2 * m + n) ^ 2 + (d : ℤ) * n ^ 2 = 4 * (p : ℤ) := by exact_mod_cast key
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    refine (hpZ.irreducible.coprime_iff_not_dvd.mpr ?_).symm
    rintro ⟨t, ht⟩
    have h1 : (p : ℤ) ∣ (d : ℤ) * n ^ 2 :=
      ⟨4 - p * t ^ 2, by linear_combination key' - (p * t + (2 * m + n)) * ht⟩
    have h2 : (p : ℤ) ∣ n ^ 2 :=
      (hpZ.dvd_or_dvd h1).resolve_left (fun h => hpd (Int.natCast_dvd_natCast.mp h))
    obtain ⟨s, hs'⟩ := hpZ.dvd_of_dvd_pow h2
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have h4 : (p : ℤ) * (t ^ 2 + d * s ^ 2) = 4 := by
      apply mul_left_cancel₀ hp0
      linear_combination key' - (2 * m + n + p * t) * ht - (d : ℤ) * (n + p * s) * hs'
    have h5 : (p : ℤ) ∣ 4 := Dvd.intro _ h4
    have h6 : p ∣ 4 := by exact_mod_cast h5
    have h7 : p ∣ 2 := by
      rcases hp.dvd_mul.mp (show p ∣ 2 * 2 from h6) with h | h <;> exact h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h7)

theorem ring_facts {X : Fields} (σ₀ : X.K →+* ℂ) (π : ℂ) (pE : 𝓞 X.E) (p : ℕ) (T : ℤ) (hne : Nonempty X.Tau)
    (h1 : ∀ τ, X.embC σ₀ τ (pE : X.E) = π) (h2 : ∀ τ, X.embC σ₀ τ (star (pE : X.E)) = conj π)
    (hpp : π * conj π = p) (hT : π + conj π = T) :
    pE * cO X.E pE = (p : 𝓞 X.E) ∧ pE + cO X.E pE = (T : 𝓞 X.E) := by
  obtain ⟨τ⟩ := hne
  let f : 𝓞 X.E →+* ℂ := (X.embC σ₀ τ).comp (algebraMap (𝓞 X.E) X.E)
  have hinj : Function.Injective f :=
    (X.embC σ₀ τ).injective.comp (IsFractionRing.injective (𝓞 X.E) X.E)
  have f1 : f pE = π := h1 τ
  have f2 : f (cO X.E pE) = conj π := h2 τ
  constructor
  · apply hinj
    rw [map_mul, f1, f2, hpp, map_natCast]
  · apply hinj
    rw [map_add (f := _), f1, f2, hT, map_intCast]

end Arith

section Primes

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : Finset (HeightOneSpectrum (𝓞 E))) (p : ℕ) (ϖ : 𝓞 E)
  (hS : ∀ P : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ P.asIdeal → (P ∈ S ↔ ϖ ∉ P.asIdeal))
  (hprod : ϖ * cO E ϖ = p) (hcop : ∃ α β : 𝓞 E, α * (ϖ + cO E ϖ) + β * (p : 𝓞 E) = 1)

include hcop hprod in
theorem not_both (Q : HeightOneSpectrum (𝓞 E)) (h1 : ϖ ∈ Q.asIdeal) (h2 : cO E ϖ ∈ Q.asIdeal) : False := by
  obtain ⟨α, β, h⟩ := hcop
  have hp : (p : 𝓞 E) ∈ Q.asIdeal := hprod ▸ Q.asIdeal.mul_mem_right _ h1
  have hs : ϖ + cO E ϖ ∈ Q.asIdeal := Q.asIdeal.add_mem h1 h2
  have h1' : (1 : 𝓞 E) ∈ Q.asIdeal := h ▸ Q.asIdeal.add_mem (Q.asIdeal.mul_mem_left α hs) (Q.asIdeal.mul_mem_left β hp)
  exact Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1')

include hprod in
theorem p_of (Q : HeightOneSpectrum (𝓞 E)) (h : ϖ ∈ Q.asIdeal ∨ cO E ϖ ∈ Q.asIdeal) : (p : 𝓞 E) ∈ Q.asIdeal := by
  rw [← hprod]
  rcases h with h | h
  · exact Q.asIdeal.mul_mem_right _ h
  · exact Q.asIdeal.mul_mem_left _ h

include hS hprod in
theorem pi_notin_S (Q : HeightOneSpectrum (𝓞 E)) (hQ : Q ∈ S) : ϖ ∉ Q.asIdeal := by
  intro h
  exact ((hS Q (p_of p ϖ hprod Q (Or.inl h))).mp hQ) h

include hS hprod hcop in
theorem pibar_notin (Q : HeightOneSpectrum (𝓞 E)) (hQ : Q ∉ S) : cO E ϖ ∉ Q.asIdeal := by
  intro h
  have hp := p_of p ϖ hprod Q (Or.inr h)
  have h1 : ϖ ∈ Q.asIdeal := by
    by_contra h1
    exact hQ ((hS Q hp).mpr h1)
  exact not_both p ϖ hprod hcop Q h1 h

include hS hprod hcop in
theorem pi_notin_off (Q : HeightOneSpectrum (𝓞 E)) (hQ : Q ∉ S) (hQ' : conjPrime₂ Q ∉ S) : ϖ ∉ Q.asIdeal := by
  intro h
  have hp := p_of p ϖ hprod Q (Or.inl h)
  have hp' : (p : 𝓞 E) ∈ (conjPrime₂ Q).asIdeal := by
    show (p : 𝓞 E) ∈ Q.asIdeal.comap (cO E)
    rw [Ideal.mem_comap, map_natCast]
    exact hp
  have h2 : ϖ ∈ (conjPrime₂ Q).asIdeal := by
    by_contra h2
    exact hQ' ((hS (conjPrime₂ Q) hp').mpr h2)
  have h3 : cO E ϖ ∈ Q.asIdeal := by
    have : ϖ ∈ Q.asIdeal.comap (cO E) := h2
    rwa [Ideal.mem_comap] at this
  exact not_both p ϖ hprod hcop Q h h3

end Primes

end KH

namespace KH

section Halves

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : Finset (HeightOneSpectrum (𝓞 E))) (p : ℕ) (ϖ : 𝓞 E)
  (hS : ∀ P : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ P.asIdeal → (P ∈ S ↔ ϖ ∉ P.asIdeal))
  (hprod : ϖ * cO E ϖ = p) (hcop : ∃ α β : 𝓞 E, α * (ϖ + cO E ϖ) + β * (p : 𝓞 E) = 1)
variable {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W] (M : Submodule (𝓞 E) W)

theorem prod_E (hprod : ϖ * cO E ϖ = p) : algebraMap (𝓞 E) E ϖ * algebraMap (𝓞 E) E (cO E ϖ) = (p : E) := by
  rw [← map_mul, hprod, map_natCast]

theorem ne_zero_E (hp : 0 < p) (hprod : ϖ * cO E ϖ = p) :
    algebraMap (𝓞 E) E ϖ ≠ 0 ∧ algebraMap (𝓞 E) E (cO E ϖ) ≠ 0 := by
  have h := prod_E p ϖ hprod
  have hp' : (p : E) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hp)
  constructor
  · intro h0
    rw [h0, zero_mul] at h
    exact hp' h.symm
  · intro h0
    rw [h0, mul_zero] at h
    exact hp' h.symm


include hS hprod hcop in
theorem half_to (hp : 0 < p) (c' : ℕ) (hc' : 0 < c') {w : W} (hw : w ∈ twist₂ M (p * c') (expS S)) (hpw : (p : E) • w ∈ M) :
    (algebraMap (𝓞 E) E ϖ / algebraMap (𝓞 E) E (cO E ϖ)) • w ∈ M := by
  obtain ⟨ha, hb⟩ := ne_zero_E p ϖ hp hprod
  have hab := prod_E p ϖ hprod
  have hc0 : (c' : E) ≠ 0 := Nat.cast_ne_zero.mpr hc'.ne'
  apply mem_of_forall_locP
  intro Q
  by_cases hQ : Q ∈ S
  · have h1 := (mem_twO M (p * c') (expS S) w).mp hw Q
    rw [show expS S Q = 1 from if_pos hQ, zpow_one] at h1
    have e : (algebraMap (𝓞 E) E ϖ / algebraMap (𝓞 E) E (cO E ϖ)) • w
        = algebraMap (𝓞 E) E (ϖ * ϖ * (c' : 𝓞 E)) • (((p * c' : ℕ) : E))⁻¹ • w := by
      rw [smul_smul]
      congr 1
      rw [map_mul, map_mul, map_natCast, Nat.cast_mul, ← hab]
      field_simp
    rw [e]
    exact smul_mem_of _ h1 _ rfl
  · have hb' := pibar_notin S p ϖ hS hprod hcop Q hQ
    apply loc_of M Q (cO E ϖ * cO E ϖ) (fun h => hb' ((Q.isPrime.mem_or_mem h).elim id id))
    have e : algebraMap (𝓞 E) E (cO E ϖ * cO E ϖ) • (algebraMap (𝓞 E) E ϖ / algebraMap (𝓞 E) E (cO E ϖ)) • w
        = (p : E) • w := by
      rw [smul_smul]
      congr 1
      rw [map_mul, ← hab]
      field_simp
    rw [e]
    exact hpw


include hS hprod hcop in
theorem half_of (hp : 0 < p) (c' : ℕ) (hc' : 0 < c') (u : ℤ) {m : W} (hm : m ∈ M) :
    ((u * c' : ℤ) : E) • (algebraMap (𝓞 E) E (cO E ϖ) / algebraMap (𝓞 E) E ϖ) • m ∈ twist₂ M (p * c') (expS S) ∧
      (p : E) • (((u * c' : ℤ) : E) • (algebraMap (𝓞 E) E (cO E ϖ) / algebraMap (𝓞 E) E ϖ) • m) ∈ M := by
  obtain ⟨ha, hb⟩ := ne_zero_E p ϖ hp hprod
  have hab := prod_E p ϖ hprod
  have hc0 : (c' : E) ≠ 0 := Nat.cast_ne_zero.mpr hc'.ne'
  have hM : ∀ (Q : HeightOneSpectrum (𝓞 E)) {z : W}, z ∈ M → z ∈ localization₂ Q.asIdeal M :=
    fun Q z hz => ⟨1, Q.asIdeal.primeCompl.one_mem, by rw [one_smul]; exact hz⟩
  constructor
  · rw [mem_twO]
    intro Q
    by_cases hQ : Q ∈ S
    · rw [show expS S Q = 1 from if_pos hQ, zpow_one]
      have hpi := pi_notin_S S p ϖ hS hprod Q hQ
      apply loc_of M Q (ϖ * ϖ) (fun h => hpi ((Q.isPrime.mem_or_mem h).elim id id))
      have e : algebraMap (𝓞 E) E (ϖ * ϖ) • (((p * c' : ℕ) : E))⁻¹ • ((u * c' : ℤ) : E) •
          (algebraMap (𝓞 E) E (cO E ϖ) / algebraMap (𝓞 E) E ϖ) • m = algebraMap (𝓞 E) E (u : 𝓞 E) • m := by
        simp only [smul_smul]
        congr 1
        rw [map_mul, map_intCast, Nat.cast_mul, ← hab]
        push_cast
        field_simp
      rw [e]
      exact smul_mem_of M hm _ rfl
    · by_cases hQ' : conjPrime₂ Q ∈ S
      · rw [show expS S Q = -1 from by simp [expS, hQ, hQ'], zpow_neg_one, inv_inv]
        apply hM Q
        have e : ((p * c' : ℕ) : E) • ((u * c' : ℤ) : E) • (algebraMap (𝓞 E) E (cO E ϖ) / algebraMap (𝓞 E) E ϖ) • m
            = algebraMap (𝓞 E) E ((u : 𝓞 E) * c' * c' * cO E ϖ * cO E ϖ) • m := by
          simp only [smul_smul]
          congr 1
          simp only [map_mul, map_intCast, map_natCast, Nat.cast_mul]
          rw [← hab]
          push_cast
          field_simp
        rw [e]
        exact smul_mem_of M hm _ rfl
      · rw [show expS S Q = 0 from by simp [expS, hQ, hQ'], zpow_zero, inv_one, one_smul]
        have hpi := pi_notin_off S p ϖ hS hprod hcop Q hQ hQ'
        apply loc_of M Q ϖ hpi
        have e : algebraMap (𝓞 E) E ϖ • ((u * c' : ℤ) : E) • (algebraMap (𝓞 E) E (cO E ϖ) / algebraMap (𝓞 E) E ϖ) • m
            = algebraMap (𝓞 E) E ((u : 𝓞 E) * c' * cO E ϖ) • m := by
          simp only [smul_smul]
          congr 1
          simp only [map_mul, map_intCast, map_natCast]
          push_cast
          field_simp
        rw [e]
        exact smul_mem_of M hm _ rfl
  · have e : (p : E) • ((u * c' : ℤ) : E) • (algebraMap (𝓞 E) E (cO E ϖ) / algebraMap (𝓞 E) E ϖ) • m
        = algebraMap (𝓞 E) E ((u : 𝓞 E) * c' * cO E ϖ * cO E ϖ) • m := by
      simp only [smul_smul]
      congr 1
      simp only [map_mul, map_intCast, map_natCast]
      rw [← hab]
      push_cast
      field_simp
    rw [e]
    exact smul_mem_of M hm _ rfl

end Halves

theorem mem_killIn {V : Type*} [AddCommGroup V] [Module ℂ V] (m : ℂ) (L M : AddSubgroup V) (y : V) :
    y ∈ killIn m L M ↔ y ∈ L ∧ m • y ∈ M := Iff.rfl

theorem mem_cLat' {V : Type*} [AddCommGroup V] [Module ℂ V] (c : ℂ) (Λ : AddSubgroup V) (y : V) :
    y ∈ cLat c Λ ↔ ∃ x ∈ Λ, c • x = y := by
  show y ∈ AddSubgroup.map ((c • LinearMap.id : V →ₗ[ℂ] V).toAddMonoidHom) Λ ↔ _
  rw [AddSubgroup.mem_map]
  rfl

end KH

theorem p_torsion_represents_quotient : HalfP := by
  intro X A a b S N N' p hp hp2 hpd hN hN' hLa π pE hq hpp hsplit c' hc' hpc' S₂ hR
  obtain ⟨hδ, hTau, -, -, -, -⟩ := hLa
  obtain ⟨h1, h2, hS⟩ := hsplit
  obtain ⟨r1, r2, r3⟩ := hR
  obtain ⟨T, hT, hTc⟩ := KH.trace_coprime A.d p hp hp2 hpd π hq hpp
  obtain ⟨hprod, hsum⟩ := KH.ring_facts A.σ₀ π pE p T hTau h1 h2 hpp hT
  have hcop : ∃ α β : 𝓞 X.E, α * (pE + cO X.E pE) + β * (p : 𝓞 X.E) = 1 := by
    obtain ⟨u, v, huv⟩ := hTc
    refine ⟨u, v, ?_⟩
    rw [hsum]
    have := congrArg (Int.cast : ℤ → 𝓞 X.E) huv
    push_cast at this
    exact this
  obtain ⟨ha0, hb0⟩ := KH.ne_zero_E p pE hp.pos hprod
  have hab : (algebraMap (𝓞 X.E) X.E pE) * (algebraMap (𝓞 X.E) X.E (cO X.E pE)) = (p : X.E) := KH.prod_E p pE hprod
  have hainv : (algebraMap (𝓞 X.E) X.E pE) * (algebraMap (𝓞 X.E) X.E pE)⁻¹ = 1 := mul_inv_cancel₀ ha0
  have hbinv : (algebraMap (𝓞 X.E) X.E (cO X.E pE)) * (algebraMap (𝓞 X.E) X.E (cO X.E pE))⁻¹ = 1 := mul_inv_cancel₀ hb0
  have ha : ∀ τ, X.embC A.σ₀ τ (algebraMap (𝓞 X.E) X.E pE) = π := h1
  have hb : ∀ τ, X.embC A.σ₀ τ (algebraMap (𝓞 X.E) X.E (cO X.E pE)) = conj π := h2
  have hΛ : ∀ y, y ∈ LamC (X.embC A.σ₀) A.δ A.AA N N' ↔ ∃ w ∈ perO A.AA N N', embH (X.embC A.σ₀) A.δ w = y := fun y => AddSubgroup.mem_map
  have hB : ∀ y, y ∈ BC (X.embC A.σ₀) A.δ A.AA S N N' (p * c') ↔ ∃ w ∈ twist₂ (perO A.AA N N') (p * c') (expS S), embH (X.embC A.σ₀) A.δ w = y :=
    fun y => AddSubgroup.mem_map
  have hsa : ∀ x : HomE X.E a b, embH (X.embC A.σ₀) A.δ ((algebraMap (𝓞 X.E) X.E (cO X.E pE) / algebraMap (𝓞 X.E) X.E pE) • x) = (conj π / π) • embH (X.embC A.σ₀) A.δ x :=
    fun (x : HomE X.E a b) => KH.embH_smul _ _ _ _ (fun τ => by rw [map_div₀, ha, hb]) x
  have hsb : ∀ x : HomE X.E a b, embH (X.embC A.σ₀) A.δ (algebraMap (𝓞 X.E) X.E (cO X.E pE) • x) = conj π • embH (X.embC A.σ₀) A.δ x :=
    fun (x : HomE X.E a b) => KH.embH_smul _ _ _ _ hb x
  have hinj : ∀ w w' : HomE X.E a b, embH (X.embC A.σ₀) A.δ w = embH (X.embC A.σ₀) A.δ w' → w = w' := by
    intro w w' h
    obtain ⟨τ⟩ := hTau
    apply (Pi.basisFun X.E (Fin a)).ext
    intro j
    rw [Pi.basisFun_apply]
    funext i
    have hij : A.δ * X.embC A.σ₀ τ (w (Pi.single j 1) i) = A.δ * X.embC A.σ₀ τ (w' (Pi.single j 1) i) :=
      congr_fun (congr_fun (congr_fun h τ) i) j
    exact (X.embC A.σ₀ τ).injective (mul_left_cancel₀ hδ hij)
  have K1 : ∀ x ∈ S₂, ∃ w ∈ twist₂ (perO A.AA N N') (p * c') (expS S), embH (X.embC A.σ₀) A.δ w = x ∧ (algebraMap (𝓞 X.E) X.E pE / algebraMap (𝓞 X.E) X.E (cO X.E pE)) • w ∈ perO A.AA N N' := by
    intro x hx
    obtain ⟨hxB, hxp⟩ := (KH.mem_killIn _ _ _ x).mp (r1 x hx)
    obtain ⟨w, hw, rfl⟩ := (hB _).mp hxB
    obtain ⟨w', hw', he⟩ := (hΛ _).mp hxp
    have hww : w' = (p : X.E) • w := hinj _ _ (by rw [he, KH.embH_nat])
    have hpw : (p : X.E) • w ∈ perO A.AA N N' := by rw [← hww]; exact hw'
    exact ⟨w, hw, rfl, KH.half_to S p pE hS hprod hcop (perO A.AA N N') hp.pos c' hc' hw hpw⟩
  refine ⟨fun x hx => ?_, fun x hx y hy hxy => ?_, fun y hy => ?_⟩
  · obtain ⟨w, hw, rfl, haw⟩ := K1 x hx
    rw [KH.mem_cLat']
    refine ⟨embH (X.embC A.σ₀) A.δ ((algebraMap (𝓞 X.E) X.E pE / algebraMap (𝓞 X.E) X.E (cO X.E pE)) • w), (hΛ _).mpr ⟨_, haw, rfl⟩, ?_⟩
    rw [← hsa, smul_smul, div_mul_div_comm, mul_comm (algebraMap (𝓞 X.E) X.E (cO X.E pE)) (algebraMap (𝓞 X.E) X.E pE), div_self (mul_ne_zero ha0 hb0), one_smul]
  · refine r2 x hx y hy ?_
    obtain ⟨z, hz, hze⟩ := (KH.mem_cLat' _ _ _).mp hxy
    obtain ⟨m, hm, rfl⟩ := (hΛ z).mp hz
    rw [← hze, ← hsb]
    exact (hΛ _).mpr ⟨_, KH.smul_mem_of _ hm (cO X.E pE) rfl, rfl⟩
  · obtain ⟨z0, hz0, rfl⟩ := (KH.mem_cLat' _ _ y).mp hy
    obtain ⟨m, hm, rfl⟩ := (hΛ z0).mp hz0
    have hcp : IsCoprime (c' : ℤ) (p : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpc'))
    obtain ⟨u, k, hu⟩ := hcp
    have huE : ((u * c' : ℤ) : X.E) + (k : X.E) * (p : X.E) = 1 := by
      have := congrArg (Int.cast : ℤ → X.E) hu
      push_cast at this ⊢
      linear_combination this
    obtain ⟨hz1, hz2⟩ := KH.half_of S p pE hS hprod hcop (perO A.AA N N') hp.pos c' hc' u hm
    have ht : embH (X.embC A.σ₀) A.δ (((u * c' : ℤ) : X.E) • (algebraMap (𝓞 X.E) X.E (cO X.E pE) / algebraMap (𝓞 X.E) X.E pE) • m) ∈ killIn (p : ℂ) (BC (X.embC A.σ₀) A.δ A.AA S N N' (p * c')) (LamC (X.embC A.σ₀) A.δ A.AA N N') :=
      (KH.mem_killIn _ _ _ _).mpr ⟨(hB _).mpr ⟨_, hz1, rfl⟩, (hΛ _).mpr ⟨_, hz2, KH.embH_nat _ _ p _⟩⟩
    obtain ⟨x, hxS, htx⟩ := r3 _ ht
    obtain ⟨w, hw, rfl, haw⟩ := K1 x hxS
    obtain ⟨m₁, hm₁, he₁⟩ := (hΛ _).mp htx
    have hm₁w : m₁ = ((u * c' : ℤ) : X.E) • (algebraMap (𝓞 X.E) X.E (cO X.E pE) / algebraMap (𝓞 X.E) X.E pE) • m - w := hinj _ _ (by rw [he₁, map_sub])
    have hm₀ : (algebraMap (𝓞 X.E) X.E pE / algebraMap (𝓞 X.E) X.E (cO X.E pE)) • m₁ ∈ perO A.AA N N' := by
      rw [hm₁w, smul_sub]
      refine sub_mem ?_ haw
      rw [smul_smul, smul_smul,
        show algebraMap (𝓞 X.E) X.E pE / algebraMap (𝓞 X.E) X.E (cO X.E pE) * ((u * c' : ℤ) : X.E) * (algebraMap (𝓞 X.E) X.E (cO X.E pE) / algebraMap (𝓞 X.E) X.E pE) = ((u * c' : ℤ) : X.E) from by
          linear_combination (((u * c' : ℤ) : X.E) * (algebraMap (𝓞 X.E) X.E (cO X.E pE)) * (algebraMap (𝓞 X.E) X.E (cO X.E pE))⁻¹) * hainv + ((u * c' : ℤ) : X.E) * hbinv]
      exact KH.smul_mem_of _ hm ((u * c' : ℤ) : 𝓞 X.E) (map_intCast _ _)
    have hw₁ : w = (((u * c' : ℤ) : X.E) * (algebraMap (𝓞 X.E) X.E (cO X.E pE) / algebraMap (𝓞 X.E) X.E pE)) • m - m₁ := by
      rw [hm₁w, smul_smul]
      abel
    obtain ⟨α, β, hαβ⟩ := id hcop
    have h𝓞 : α * pE + (α + β * pE) * cO X.E pE = 1 := by linear_combination hαβ + β * hprod
    have hcopE : algebraMap (𝓞 X.E) X.E α * (algebraMap (𝓞 X.E) X.E pE) + (algebraMap (𝓞 X.E) X.E α + algebraMap (𝓞 X.E) X.E β * (algebraMap (𝓞 X.E) X.E pE)) * (algebraMap (𝓞 X.E) X.E (cO X.E pE)) = 1 := by
      have := congrArg (algebraMap (𝓞 X.E) X.E) h𝓞
      simp only [map_add (f := _), map_mul, map_one] at this
      exact this
    have hm₃ : ((k : X.E) * (algebraMap (𝓞 X.E) X.E (cO X.E pE))) • m + (algebraMap (𝓞 X.E) X.E α * (algebraMap (𝓞 X.E) X.E pE / algebraMap (𝓞 X.E) X.E (cO X.E pE)) +
        (algebraMap (𝓞 X.E) X.E α + algebraMap (𝓞 X.E) X.E β * (algebraMap (𝓞 X.E) X.E pE))) • m₁ ∈ perO A.AA N N' := by
      refine add_mem (KH.smul_mem_of _ hm ((k : 𝓞 X.E) * cO X.E pE) (by simp only [map_mul, map_intCast])) ?_
      rw [add_smul, ← smul_smul]
      exact add_mem (KH.smul_mem_of _ hm₀ α rfl) (KH.smul_mem_of _ hm₁ (α + β * pE) (by simp only [map_add (f := _), map_mul]))
    refine ⟨embH (X.embC A.σ₀) A.δ w, hxS, ?_⟩
    rw [KH.mem_cLat']
    refine ⟨embH (X.embC A.σ₀) A.δ (((k : X.E) * (algebraMap (𝓞 X.E) X.E (cO X.E pE))) • m + (algebraMap (𝓞 X.E) X.E α * (algebraMap (𝓞 X.E) X.E pE / algebraMap (𝓞 X.E) X.E (cO X.E pE)) +
        (algebraMap (𝓞 X.E) X.E α + algebraMap (𝓞 X.E) X.E β * (algebraMap (𝓞 X.E) X.E pE))) • m₁), (hΛ _).mpr ⟨_, hm₃, rfl⟩, ?_⟩
    rw [← hsb, ← hsa, ← map_sub]
    congr 1
    rw [hw₁, smul_add, smul_smul, smul_smul,
      show algebraMap (𝓞 X.E) X.E (cO X.E pE) * ((k : X.E) * algebraMap (𝓞 X.E) X.E (cO X.E pE)) = algebraMap (𝓞 X.E) X.E (cO X.E pE) / algebraMap (𝓞 X.E) X.E pE - ((u * c' : ℤ) : X.E) * (algebraMap (𝓞 X.E) X.E (cO X.E pE) / algebraMap (𝓞 X.E) X.E pE) from by
        linear_combination ((algebraMap (𝓞 X.E) X.E (cO X.E pE)) * (algebraMap (𝓞 X.E) X.E pE)⁻¹) * huE + ((algebraMap (𝓞 X.E) X.E (cO X.E pE)) * (algebraMap (𝓞 X.E) X.E pE)⁻¹ * (k : X.E)) * hab - ((k : X.E) * (algebraMap (𝓞 X.E) X.E (cO X.E pE)) ^ 2) * hainv,
      show algebraMap (𝓞 X.E) X.E (cO X.E pE) * (algebraMap (𝓞 X.E) X.E α * (algebraMap (𝓞 X.E) X.E pE / algebraMap (𝓞 X.E) X.E (cO X.E pE)) + (algebraMap (𝓞 X.E) X.E α + algebraMap (𝓞 X.E) X.E β * (algebraMap (𝓞 X.E) X.E pE))) = 1 from by
        linear_combination hcopE + (algebraMap (𝓞 X.E) X.E α * (algebraMap (𝓞 X.E) X.E pE)) * hbinv,
      one_smul, sub_smul]
    abel

end Formalism.L2.AlgTh
end
end

namespace Formalism.L2.AlgTh

theorem jetAtSplit : JetAtSplit :=
  jetAtSplit_of split_place_scaled_bound kernel_index_form representatives_split level_kills_half_lattice chosen_lift_killed_level p_torsion_represents_quotient card_two_sided_quotient index_product_formula
    taylor_jet_expansion linear_substitution_diagonal

end Formalism.L2.AlgTh
end

section -- merged from Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.IntCurveOfScale
noncomputable section
open scoped BigOperators
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.KS

open Formalism.MainNotions Formalism.L2.Col
open Formalism.L2.Th1.E (IntCurve curveL)

theorem intCurve_of_scale (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (L : PeriodPair) (c : ℂ) (hc : c ≠ 0)
    (h : IntCurve (curveL p (Formalism.L2.Th1.F.scalePair L c hc) ι)) (hΔ : ‖ι (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)‖ = 1) :
    IntCurve (curveL p L ι) := by
  have hH := Formalism.L2.Th1.F.homogeneity L c hc
  have h2 : (Formalism.L2.Th1.F.scalePair L c hc).g₂ = (c ^ 4)⁻¹ * L.g₂ := hH.2.2.2.2.2.2.2.2.2.1
  have h3 : (Formalism.L2.Th1.F.scalePair L c hc).g₃ = (c ^ 6)⁻¹ * L.g₃ := hH.2.2.2.2.2.2.2.2.2.2
  obtain ⟨-, -, -, h4, h6, hD⟩ := h
  have hS := fun g2 g3 : ℂ_[p] => (Formalism.L2.Th1.A.shortInv ℂ_[p] g2 g3).2.2.2
  have hιc : ι c ≠ 0 := by simpa using hc
  have hcn : ‖ι c‖ = 1 := by
    unfold curveL at hD
    rw [hS, h2, h3] at hD
    have e : ι ((c ^ 4)⁻¹ * L.g₂) ^ 3 - 27 * ι ((c ^ 6)⁻¹ * L.g₃) ^ 2 = (ι c ^ 12)⁻¹ * ι (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
      simp only [map_mul, map_inv₀, map_pow, map_sub, map_ofNat]
      field_simp
    rw [e, norm_mul, hΔ, mul_one, norm_inv, norm_pow, inv_eq_one] at hD
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 hD
  refine ⟨by simp [curveL, Formalism.L2.Th1.A.shortW], by simp [curveL, Formalism.L2.Th1.A.shortW], by simp [curveL, Formalism.L2.Th1.A.shortW], ?_, ?_, ?_⟩
  · have e : (curveL p L ι).a₄ = ι c ^ 4 * (curveL p (Formalism.L2.Th1.F.scalePair L c hc) ι).a₄ := by
      simp only [curveL, Formalism.L2.Th1.A.shortW, h2, map_mul, map_inv₀, map_pow]
      field_simp
    rw [e, norm_mul, norm_pow, hcn, one_pow, one_mul]
    exact h4
  · have e : (curveL p L ι).a₆ = ι c ^ 6 * (curveL p (Formalism.L2.Th1.F.scalePair L c hc) ι).a₆ := by
      simp only [curveL, Formalism.L2.Th1.A.shortW, h3, map_mul, map_inv₀, map_pow]
      field_simp
    rw [e, norm_mul, norm_pow, hcn, one_pow, one_mul]
    exact h6
  · unfold curveL
    rw [hS]
    simpa only [map_sub, map_mul, map_pow, map_ofNat] using hΔ

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

theorem disc_one (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) : B.L.g₂ ^ 3 - 27 * B.L.g₃ ^ 2 = 1 := by
  have hL : (B.L.lattice : Set ℂ) = TaylorLogMetric.lamOf D cc δ := by
    rw [← B.lat]; rfl
  obtain ⟨e2, e3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair (TaylorLogMetric.lamOf D cc δ) B.L hL
  have h := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_discr_lamOf D cc hcc δ hδ
  rw [← e2, ← e3]
  exact h

theorem intCurve_base (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (ι : ℂ ≃+* ℂ_[p]) :
    IntCurve (curveL p B.L ι) := by
  have hcm : Formalism.L2.Th1.CM.HasCMBy D.host.d B.L := by
    intro ω hω
    have := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.hst B ω hω
    rwa [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.theta_val] at this
  have hd8 : D.host.d % 8 = 7 := dMod8 D
  obtain ⟨c, hc, hI⟩ := Formalism.L2.Th1.Top.good_model_exists_all_primes D.host.d B.L D.host.hyp.2.1.squarefree (by omega) hcm p hp ι
  refine intCurve_of_scale p ι B.L c hc hI ?_
  rw [disc_one B hcc hδ, map_one, norm_one]

theorem chiFac_unit (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) {N N' : ℕ}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hA : TaylorLogMetric.admitted D N N' L L') (h1 : TaylorLogMetric.EqAt D p (StandardLatticesGL3.stdL D N) L) (h2 : TaylorLogMetric.EqAt D p (StandardLatticesGL3.stdL D N') L') :
    ‖ι (Base.chiFac χ N N' L L')‖ = 1 := by
  obtain ⟨hq, hn⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.chiFacUnit χ hχ p ((ι : ℂ →+* ℂ_[p]).comp (algebraMap TaylorLogMetric.Qbar ℂ)) N N' L L' hA h1 h2
  unfold TaylorLogMetric.lamC at hn
  rw [dite_eq_left hq] at hn
  exact hn

end Formalism.L2.Ker.KS
end
end

noncomputable section
open scoped BigOperators
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker

open Formalism.MainNotions Formalism.L2.Col
open Formalism.L2.Th1.H (cmL CmOK)
open Formalism.L2.Th1.E (IntCurve curveL)
open Formalism.L2.AlgTh (KerStd)

theorem kerStd_core {D : D7} {X : Fields} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)
    {a b : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p])
    (hok : s.Ok) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hχ : TaylorLogMetric.IsChi D χ) (hcm : CmOK a₀ b₀ c₀ D.host.d)
    (hB : B.IsCm a₀ b₀ ha hd lam hlam) (hae : Even a) (hbe : Even b) (hN : IsSdLat N) (hN' : IsSdLat N') (hsN : s.StdAtP p N) (hsN' : s.StdAtP p N')
    (hdisc : ¬ (p : ℤ) ∣ NumberField.discr X.E) (hcD : ∀ τ, ‖ι (cD τ)‖ ≤ 1)
    (hW : IntCurve (curveL p (cmL a₀ b₀ D.host.d ha hd lam hlam) ι)) (hK : B.KappaAt p ι) :
    KerStd (ambOf s B χ cD) N N' a₀ b₀ c₀ ha hd lam hlam p ι := by
  have hA : TaylorLogMetric.admitted D a b (s.lat N) (s.lat N') := s.admissible_of_selfDual_lattices hok hae hbe hN hN'
  have hT := KS.lamTie D X s cc δ B χ cD a b N N' hok
  have hodd : Odd b₀ := KS.Lat.odd_of_cmOK hcm
  have hchi : ‖ι ((ambOf s B χ cD : Amb X).chiF a b N N')‖ = 1 := KS.chiFac_unit χ hχ p ι hA hsN hsN'
  refine ⟨hcm, KS.Lat.sc_pos B, ?_, ?_, ?_, ?_, hW, ?_, ?_, hchi⟩
  · rw [hT]; exact KS.Lat.isLat_laF s B hcc hδ hA
  · rw [hT]; exact KS.Lat.selfDual_laF s B hcc hδ hA
  · rw [hT]; exact fun x hx => KS.Lat.theta_laF s B hodd hx
  · rw [hT]; exact KS.Lat.eNat_laF s B hcc hδ χ hA
  · exact KS.locNorm_ambOf_of s B KS.lamTie Formalism.L2.AlgTh.local_norm_scaling Formalism.L2.AlgTh.local_norm_power Formalism.L2.AlgTh.local_norm_intertwiner
      χ cD a₀ b₀ c₀ ha hd lam hlam p ι hok hcc hδ hcm
      (KS.MM.selfDual_lamMX s B hcc hδ) (KS.MM.stable_lamMX s B b₀ hodd) (KS.MM.thMMX_mem s B hcc hδ)
      (KS.MM.locNorm_thMMX s B hcc hδ a₀ b₀ c₀ ha hd lam hlam hcm hB p ι hK)
      (KS.Lat.posDef_hSc (KS.Lat.sc_pos B) a b)
      (fun L L' h => KS.Lat.isLat_laF s B hcc hδ h) (fun L L' _ x hx => KS.Lat.theta_laF s B hodd hx) hA hsN hsN' hchi.le
  · have h := KS.frame_std s B χ cD Formalism.L2.AlgTh.kerFrame hok N N' p ι hsN hsN' hdisc hcD
    rw [hB.1] at h
    exact h

theorem kerStd_congr {X : Fields} {A A' : Amb X} (h : A = A') {a b : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < A.d) (hd' : 0 < A'.d) (lam : ℂ) (hlam : lam ≠ 0) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p])
    (hK : KerStd A' N N' a₀ b₀ c₀ ha hd' lam hlam p ι) : KerStd A N N' a₀ b₀ c₀ ha hd lam hlam p ι := by
  subst h
  exact hK

theorem kerStdLatOn_of (Q : D7 → ℕ → Prop) (hK : ∀ D, KappaOn Q D) : KerStdLatOn Q := by
  intro D X s cc δ B χ cD a b N N' a₀ b₀ c₀ ha hd lam hlam p _ ι hok hcc hδ hχ hcm hl hae hbe hN hN' hsN hsN' hdisc hcD hp hQ
  refine kerStd_congr (KS.ambOf_cmBase B a₀ b₀ c₀ ha hd lam hlam s hcm hl χ cD) N N' a₀ b₀ c₀ ha hd hd lam hlam p ι ?_
  exact kerStd_core s (KS.cmBase B a₀ b₀ c₀ ha hd lam hlam hcm hl) χ cD N N' a₀ b₀ c₀ ha hd lam hlam p ι hok hcc hδ hχ hcm
    (KS.cmBase_isCm B a₀ b₀ c₀ ha hd lam hlam hcm hl) hae hbe hN hN' hsN hsN' hdisc hcD
    (KS.intCurve_base (KS.cmBase B a₀ b₀ c₀ ha hd lam hlam hcm hl) hcc hδ p hp ι)
    (hK D cc δ _ hcc hδ p ι hQ)

theorem kerStdExOn_of (Q : D7 → ℕ → Prop) (hK : ∀ D, KappaOn Q D) : KerStdExOn Q := by
  intro D X s cc δ B χ cD hok hcc hδ hχ
  have hd : 0 < D.host.d := D.host.hyp.2.1.pos
  obtain ⟨a₀, b₀, c₀, ha, lam, hlam, hcm, hL⟩ := KS.exists_cmOK D.host.d hd (dMod8 D) D.host.hyp.2.1 B.L (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.hst B)
  have hl : (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ := by rw [hL]; exact B.lat
  refine ⟨a₀, b₀, c₀, ha, hd, lam, hlam, hcm, hl, ?_⟩
  intro a b N N' p _ ι hae hbe hN hN' hsN hsN' hdisc hcD hp hQ
  exact kerStdLatOn_of Q hK D X s cc δ B χ cD a b N N' a₀ b₀ c₀ ha hd lam hlam p ι hok hcc hδ hχ hcm hl hae hbe hN hN' hsN hsN' hdisc hcD hp hQ

theorem kerStdEx : KerStdEx := kerStdExOn_of _ KS.kappaAll

namespace Test

open scoped ComplexConjugate
open IsDedekindDomain

theorem jetAtSplit_ambOf {D : D7} {X : Fields} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)
    (hok : s.Ok) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hχ : TaylorLogMetric.IsChi D χ)
    (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (hae : Even a) (hbe : Even b) (hN : IsSdLat N) (hN' : IsSdLat N')
    (hsN : s.StdAtP p N) (hsN' : s.StdAtP p N') (hdisc : ¬ (p : ℤ) ∣ NumberField.discr X.E) (hcD : ∀ τ, ‖ι (cD τ)‖ ≤ 1) (hp : 5 ≤ p)
    (hpd : ¬ p ∣ D.host.d) (hLa : (ambOf s B χ cD : Amb X).LaHyp a b S)
    (π : ℂ) (pE : 𝓞 X.E) (hπ : Formalism.L2.AlgTh.IsQInt D.host.d π) (hππ : π * conj π = (p : ℂ)) (hS : Formalism.L2.AlgTh.SplitS (ambOf s B χ cD) S p π pE)
    (c' : ℕ) (x : HomE X.E a b) (hc' : 0 < c') (hpc : ¬ p ∣ c') (hx : x ∈ divLat c' (homAt S N N')) (m : DVar X.Tau a b →₀ ℕ) :
    ‖ι ((ambOf s B χ cD : Amb X).σ₀ ((ambOf s B χ cD : Amb X).jetK S N N' (p * c') x m))‖ * ‖ι (conj π)‖ ^ m.degree *
      ‖(p : ℂ_[p])‖ ^ (Fintype.card X.Tau * b * a) ≤ 1 := by
  obtain ⟨a₀, b₀, c₀, ha, hd, lam, hlam, -, -, h⟩ := kerStdEx D X s cc δ B χ cD hok hcc hδ hχ
  exact Formalism.L2.AlgTh.jetAtSplit X (ambOf s B χ cD) a b S N N' a₀ b₀ c₀ ha hd lam hlam p ι (by omega) hpd
    (h a b N N' p ι hae hbe hN hN' hsN hsN' hdisc hcD hp trivial) hN hN' hLa π pE hπ hππ hS c' x hc' hpc hx m

end Test

end Formalism.L2.Ker
