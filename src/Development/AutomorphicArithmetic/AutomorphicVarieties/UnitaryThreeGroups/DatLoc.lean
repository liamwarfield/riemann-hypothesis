module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DecEmb
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.GdOfHost
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ArtKer

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DatLoc
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

theorem UpperTheory.V.U3.dat_loc :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ),
      ∃ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 ∧ D.ι.range = Dec (F := ℚ) A ∧ (Loc.Iq l).map D.ι = Ine (F := ℚ) A ∧
        Function.Injective D.ι ∧ (∀ x : Ω, x ∈ A ↔ ‖D.j x‖ ≤ 1) ∧ (∀ σ, cycZ ℚ Ω l (D.ι σ) = Loc.cyc l l σ) ∧
        ∀ A' : ValuationSubring Ω, A'.valuation (l : Ω) < 1 → ∃ g : G ℚ Ω,
          (∀ s, s ∈ Dec (F := ℚ) A' ↔ g⁻¹ * s * g ∈ Dec (F := ℚ) A) ∧ ∀ s, s ∈ Ine (F := ℚ) A' ↔ g⁻¹ * s * g ∈ Ine (F := ℚ) A := by
  intro Ω _ _ _ K _ _ _ l _ c N _ e ψ D
  have hι : D.ι = Loc.iota D.j := by
    ext σ x
    apply D.j.injective
    rw [Loc.iota_spec, ← D.ι_spec]
  obtain ⟨hemb, hrange, -, hmap, hcyc, -, -⟩ := Loc.iotaFacts D.j
  have hmem : ∀ x : Ω, x ∈ Loc.placeJ D.j ↔ Valued.v (D.j x) ≤ 1 := fun x => Iff.rfl
  have hA : (Loc.placeJ D.j).valuation (l : Ω) < 1 := by
    have hnot : (l : Ω)⁻¹ ∉ Loc.placeJ D.j := by
      rw [hmem, map_inv₀, map_natCast, map_inv₀, PadicAlgCl.valuation_p, not_le]
      have hl : (1 : NNReal) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
      simpa using hl
    by_contra h
    push_neg at h
    apply hnot
    have hle : (Loc.placeJ D.j).valuation (l : Ω) ≤ 1 :=
      ((Loc.placeJ D.j).valuation_le_one_iff _).2 (natCast_mem _ l)
    rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, le_antisymm hle h, inv_one]
  refine ⟨Loc.placeJ D.j, hA, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hι]; exact hrange
  · rw [hι]; exact hmap
  · rw [hι]; exact hemb.injective
  · intro x
    rw [hmem, ← NNReal.coe_le_coe, PadicAlgCl.valuation_coe, NNReal.coe_one]
  · intro σ
    rw [hι]
    exact DFunLike.congr_fun (hcyc l) σ
  · intro A' hA'
    obtain ⟨-, -, -, -, -, -, -, hconj, -, hact⟩ := ML.placeBasic Ω
    obtain ⟨g, rfl⟩ := hconj (Loc.placeJ D.j) A' l Fact.out hA hA'
    exact ⟨g, (hact _ g).1, (hact _ g).2.1⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.OrbEquiv
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsMoreLast
theorem UpperTheory.Reformulated.B.Qk10.exists_w :
    ∀ (K : Type) [inst : Field K] [NumberField K] {p : ℕ},
    Nat.Prime p →
      ∃ (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
        (↑p : NumberField.RingOfIntegers K) ∈ w.asIdeal := by
  intro K _ _ p hp
  have hnu : ¬ IsUnit (p : NumberField.RingOfIntegers K) := by
    intro h
    have h1 : IsUnit (algebraMap ℤ (NumberField.RingOfIntegers K) (p : ℤ)) := by
      simpa using h
    have h2 : IsUnit (p : ℤ) := (isUnit_map_iff _ _).mp h1
    exact (Nat.prime_iff_prime_int.mp hp).not_unit h2
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal
    (Ideal.span {(p : NumberField.RingOfIntegers K)})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hmem : (p : NumberField.RingOfIntegers K) ∈ M :=
    hle (Ideal.mem_span_singleton_self _)
  refine ⟨⟨M, hM.isPrime, ?_⟩, hmem⟩
  rintro rfl
  rw [Ideal.mem_bot] at hmem
  exact hp.ne_zero (Nat.cast_eq_zero.mp hmem)
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem exists_w (K : Type) [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) :
    ∃ w : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ w.asIdeal :=
  _root_.UpperTheory.Reformulated.B.Qk10.exists_w K hp

end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.CorGSumLog
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private lemma corG_sum_log (n : ℤ) (hn : n ≠ 0) (Ls : Finset Nat.Primes) :
    ∑ l ∈ Ls, Real.log (l : ℕ) * (padicValInt l n : ℝ) ≤ Real.log |(n : ℝ)| := by
  classical
  have hdvd : ∏ l ∈ Ls, ((l : ℕ) : ℤ) ^ (padicValInt l n) ∣ n := by
    apply Finset.prod_dvd_of_coprime
    · intro a _ b _ hab
      simp only [Function.onFun]
      apply IsCoprime.pow
      rw [Nat.isCoprime_iff_coprime]
      exact (Nat.coprime_primes a.2 b.2).mpr (fun h => hab (Subtype.ext h))
    · intro l _
      haveI : Fact (Nat.Prime l) := ⟨l.2⟩
      exact padicValInt_dvd n
  have hP : (∏ l ∈ Ls, ((l : ℕ) : ℝ) ^ (padicValInt l n)) ≤ |(n : ℝ)| := by
    have h1 := Int.le_of_dvd (abs_pos.mpr hn) ((dvd_abs _ _).mpr hdvd)
    have h2 : ((∏ l ∈ Ls, ((l : ℕ) : ℤ) ^ (padicValInt l n) : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by
      exact_mod_cast h1
    push_cast at h2
    exact h2
  have hpos : ∀ l ∈ Ls, (0 : ℝ) < ((l : ℕ) : ℝ) ^ (padicValInt l n) :=
    fun l _ => pow_pos (by exact_mod_cast l.2.pos) _
  calc ∑ l ∈ Ls, Real.log (l : ℕ) * (padicValInt l n : ℝ)
      = ∑ l ∈ Ls, Real.log (((l : ℕ) : ℝ) ^ (padicValInt l n)) := by
        apply Finset.sum_congr rfl
        intro l _
        rw [Real.log_pow]
        ring
    _ = Real.log (∏ l ∈ Ls, ((l : ℕ) : ℝ) ^ (padicValInt l n)) :=
        (Real.log_prod (fun l hl => (hpos l hl).ne')).symm
    _ ≤ Real.log |(n : ℝ)| := Real.log_le_log (Finset.prod_pos hpos) hP

theorem UpperTheory.V.U3.corGK :
    PropGK → CorGK := by
  intro hP K _ _
  obtain ⟨c₅, A, hK⟩ := hP K
  refine ⟨c₅, A, ?_⟩
  intro Ω _ _ _ _ e N _ H p p' hp hp' hne hd hd' c Ls hL
  rcases Ls.eq_empty_or_nonempty with rfl | ⟨l₀, hl₀⟩
  · refine ⟨by simp, ?_⟩
    rw [Finset.sum_empty]
    have h1 := Real.log_natCast_nonneg p
    have h2 := Real.log_natCast_nonneg p'
    positivity
  have he : 1 ≤ e := by
    obtain ⟨ψ, _, h⟩ := hL l₀ hl₀
    exact h.e_pos
  obtain ⟨n, hn, hb, h⟩ := hK e N H p he hp hd
  obtain ⟨n', hn', hb', h'⟩ := hK e N H p' he hp' hd'
  have key : ∀ l ∈ Ls, (∀ ψ ∈ orb (c l) H, Vlen Ω (c l) e ψ ≠ ⊤) ∧
      ∑ ψ ∈ orb (c l) H, Vn Ω (c l) e ψ ≤ 2 * (padicValInt l n : ℝ) + 2 * (padicValInt l n' : ℝ) := by
    intro l hl
    have a1 : (0 : ℝ) ≤ (padicValInt l n : ℝ) := Nat.cast_nonneg _
    have a2 : (0 : ℝ) ≤ (padicValInt l n' : ℝ) := Nat.cast_nonneg _
    by_cases hlp : (l : ℕ) = p
    · have hlp' : (l : ℕ) ≠ p' := fun x => hne (hlp.symm.trans x)
      obtain ⟨b1, b2⟩ := h' Ω l hlp' (c l) (hL l hl)
      exact ⟨b1, by linarith⟩
    · obtain ⟨b1, b2⟩ := h Ω l hlp (c l) (hL l hl)
      exact ⟨b1, by linarith⟩
  refine ⟨fun l hl => (key l hl).1, ?_⟩
  have s1 := corG_sum_log n hn Ls
  have s2 := corG_sum_log n' hn' Ls
  calc _ ≤ ∑ l ∈ Ls, Real.log (l : ℕ) * (2 * (padicValInt l n : ℝ) + 2 * (padicValInt l n' : ℝ)) :=
        Finset.sum_le_sum fun l hl => mul_le_mul_of_nonneg_left (key l hl).2 (Real.log_natCast_nonneg _)
    _ = 2 * ∑ l ∈ Ls, Real.log (l : ℕ) * (padicValInt l n : ℝ) + 2 * ∑ l ∈ Ls, Real.log (l : ℕ) * (padicValInt l n' : ℝ) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun l _ => by ring
    _ ≤ _ := by nlinarith
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.CountI
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem absorb (A N t e : ℝ) (k a : ℕ) (hk : A ≤ 16 ^ k) (hN : 16 ≤ N) (he : 0 ≤ e) (het : e + 1 ≤ t) :
    A * N * (N * (e + 1)) ^ a ≤ (N * t) ^ (k + 1 + a) := by
  have h0 : 0 ≤ N := by linarith
  have ht : 1 ≤ t := by linarith
  have h1 : A ≤ N ^ k := hk.trans (pow_le_pow_left₀ (by norm_num) hN k)
  have h2 : N ≤ N * t := le_mul_of_one_le_right h0 ht
  calc A * N * (N * (e + 1)) ^ a ≤ N ^ k * N * (N * t) ^ a := by gcongr
    _ ≤ (N * t) ^ k * (N * t) * (N * t) ^ a := by gcongr
    _ = (N * t) ^ (k + 1 + a) := by ring

theorem UpperTheory.V.U3.countI :
    CorGK → CountI := by
  intro hC χ
  classical
  obtain ⟨hpK, hpK4, hpK7, hpKcop⟩ := (pK_pOne_prime_conditions χ).1
  obtain ⟨hdisc, -, -, -⟩ := kstar (pK χ) hpK hpK4
  obtain ⟨c₅, A, hcor⟩ := hC (Kstar (pK χ))
  obtain ⟨r₁, hr₁B, hr₁⟩ := Nat.exists_infinite_primes (30 * χ.N * pK χ + 1)
  obtain ⟨r₂, hr₂B, hr₂⟩ := Nat.exists_infinite_primes (r₁ + 1)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (2 * (c₅ : ℝ) * (Real.log r₁ + Real.log r₂)) (by norm_num : (1 : ℝ) < 16)
  refine ⟨k + 1 + A, r₁, r₂, hr₁, hr₂, ?_⟩
  intro h hχ h1q h1d h2q h2d t hBig e he het Ω _ _ _ c Ls hLs
  subst hχ
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  letI : Algebra (Kstar (pK h.chi)) Ω :=
    (IsAlgClosed.lift (M := Ω) (R := ℚ) (S := Kstar (pK h.chi))).toRingHom.toAlgebra
  obtain ⟨-, -, h16, -, -, hprimeN, -⟩ := hostIndex h
  have hN0 := h.N_pos
  have hqpos : 0 < h.chi.N := Nat.pos_of_ne_zero (h.chi.ne.out)
  have hnd : ∀ p : ℕ, p.Prime → 30 * h.chi.N * pK h.chi + 1 ≤ p → p < h.q1 → p < h.d →
      ¬ p ∣ 30 * h.N * (NumberField.discr (Kstar (pK h.chi))).natAbs := by
    intro p hp hpB hpq hpd hdiv
    rw [hdisc, Int.natAbs_neg, Int.natAbs_natCast] at hdiv
    have hp30 : 30 < p := by nlinarith [hpK7]
    rcases (Nat.Prime.dvd_mul hp).1 hdiv with h1 | h1
    · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
      · have := Nat.le_of_dvd (by norm_num) h2
        omega
      · rcases (hprimeN p hp).1 h2 with h3 | h3 | h3 | h3
        · omega
        · have := Nat.le_of_dvd hqpos h3
          nlinarith [hpK7]
        · omega
        · omega
    · have := Nat.le_of_dvd (by omega) h1
      nlinarith [hqpos]
  have hnd1 := hnd r₁ hr₁ hr₁B h1q h1d
  have hnd2 := hnd r₂ hr₂ (by omega) h2q h2d
  have hne : r₁ ≠ r₂ := by omega
  set T : Finset (Subgroup (ZMod h.N)ˣ) :=
    Ls.biUnion (fun l => (h.X (c l) e).image (fun ψ => (MulChar.toUnitHom ψ).ker)) with hT
  have hcorK : ∀ K' : Subgroup (ZMod h.N)ˣ,
      (∀ l ∈ Ls.filter (fun l => ∃ ψ ∈ h.X (c l) e, (MulChar.toUnitHom ψ).ker = K'),
        ∀ ψ ∈ orb (c l) K', Vlen Ω (c l) e ψ ≠ ⊤) ∧
      ∑ l ∈ Ls.filter (fun l => ∃ ψ ∈ h.X (c l) e, (MulChar.toUnitHom ψ).ker = K'),
        Real.log ((l : ℕ) : ℝ) * ∑ ψ ∈ orb (c l) K', Vn Ω (c l) e ψ ≤
        2 * (c₅ : ℝ) * (K'.index.totient : ℝ) * ((h.N : ℝ) * ((e : ℝ) + 1)) ^ A *
          (Real.log r₁ + Real.log r₂) := by
    intro K'
    refine hcor Ω e h.N K' r₁ r₂ hr₁ hr₂ hne hnd1 hnd2 c _ ?_
    intro l hl
    obtain ⟨hlLs, ψ, hψ, hker⟩ := Finset.mem_filter.1 hl
    obtain ⟨hchar, hpar⟩ := (Host.mem_X h).1 hψ
    exact ⟨ψ, (mem_orb _).2 hker, gdOfHost h t hBig Ω l e (hLs l hlLs).1 he het (hLs l hlLs).2 _ ψ hchar hpar⟩
  have hmapT : ∀ l ∈ Ls, ∀ ψ ∈ h.X (c l) e, (MulChar.toUnitHom ψ).ker ∈ T := by
    intro l hl ψ hψ
    rw [hT, Finset.mem_biUnion]
    exact ⟨l, hl, Finset.mem_image_of_mem _ hψ⟩
  have hsumT : ∑ K' ∈ T, ((K'.index.totient : ℕ) : ℝ) ≤ (h.N : ℝ) := by
    have hcyc : ∀ K' ∈ T, IsCyclic ((ZMod h.N)ˣ ⧸ K') := by
      intro K' hK'
      rw [hT, Finset.mem_biUnion] at hK'
      obtain ⟨l, -, hK'⟩ := hK'
      obtain ⟨ψ, -, rfl⟩ := Finset.mem_image.1 hK'
      exact (orbFacts _ h.N ψ).2.1
    have h1 := orbSum (ZMod h.N)ˣ T hcyc
    have h2 : Nat.card (ZMod h.N)ˣ ≤ h.N := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
      exact Nat.totient_le _
    exact_mod_cast h1.trans h2
  have hc5 : (0 : ℝ) ≤ c₅ := by positivity
  have hL : 0 ≤ Real.log r₁ + Real.log r₂ := add_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
  have hP : 0 ≤ ((h.N : ℝ) * ((e : ℝ) + 1)) ^ A := by positivity
  have hN16 : (16 : ℝ) ≤ h.N := by exact_mod_cast Nat.le_of_dvd hN0 h16
  have het' : (e : ℝ) + 1 ≤ t := by exact_mod_cast Nat.succ_le_of_lt het
  refine ⟨?_, ?_⟩
  · intro l hl ψ hψ
    exact (hcorK _).1 l (Finset.mem_filter.2 ⟨hl, ψ, hψ, rfl⟩) ψ ((mem_orb _).2 rfl)
  · have hstep : ∀ l ∈ Ls, Real.log ((l : ℕ) : ℝ) * ∑ ψ ∈ h.X (c l) e, Vn Ω (c l) e ψ ≤
        ∑ K' ∈ T, if (∃ ψ ∈ h.X (c l) e, (MulChar.toUnitHom ψ).ker = K') then
          Real.log ((l : ℕ) : ℝ) * ∑ ψ ∈ orb (c l) K', Vn Ω (c l) e ψ else 0 := by
      intro l hl
      have hlog : 0 ≤ Real.log ((l : ℕ) : ℝ) := Real.log_natCast_nonneg _
      rw [← Finset.sum_fiberwise_of_maps_to (hmapT l hl), Finset.mul_sum]
      refine Finset.sum_le_sum fun K' _ => ?_
      split_ifs with hex
      · apply mul_le_mul_of_nonneg_left _ hlog
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro ψ hψ
          exact (mem_orb _).2 (Finset.mem_filter.1 hψ).2
        · intro ψ _ _
          exact Vn_nonneg Ω _ e ψ
      · have hempty : (h.X (c l) e).filter (fun ψ => (MulChar.toUnitHom ψ).ker = K') = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro ψ hψ hk
          exact hex ⟨ψ, hψ, hk⟩
        rw [hempty, Finset.sum_empty, mul_zero]
    calc _ ≤ ∑ l ∈ Ls, ∑ K' ∈ T, (if (∃ ψ ∈ h.X (c l) e, (MulChar.toUnitHom ψ).ker = K') then
          Real.log ((l : ℕ) : ℝ) * ∑ ψ ∈ orb (c l) K', Vn Ω (c l) e ψ else 0) := Finset.sum_le_sum hstep
      _ = ∑ K' ∈ T, ∑ l ∈ Ls.filter (fun l => ∃ ψ ∈ h.X (c l) e, (MulChar.toUnitHom ψ).ker = K'),
          Real.log ((l : ℕ) : ℝ) * ∑ ψ ∈ orb (c l) K', Vn Ω (c l) e ψ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun K' _ => ?_
        rw [Finset.sum_filter]
      _ ≤ ∑ K' ∈ T, 2 * (c₅ : ℝ) * (K'.index.totient : ℝ) * ((h.N : ℝ) * ((e : ℝ) + 1)) ^ A *
          (Real.log r₁ + Real.log r₂) := Finset.sum_le_sum fun K' _ => (hcorK K').2
      _ = (2 * (c₅ : ℝ) * (Real.log r₁ + Real.log r₂)) * ((h.N : ℝ) * ((e : ℝ) + 1)) ^ A *
          ∑ K' ∈ T, ((K'.index.totient : ℕ) : ℝ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun K' _ => by ring
      _ ≤ (2 * (c₅ : ℝ) * (Real.log r₁ + Real.log r₂)) * ((h.N : ℝ) * ((e : ℝ) + 1)) ^ A * (h.N : ℝ) :=
        mul_le_mul_of_nonneg_left hsumT (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc5) hL) hP)
      _ = (2 * (c₅ : ℝ) * (Real.log r₁ + Real.log r₂)) * (h.N : ℝ) * ((h.N : ℝ) * ((e : ℝ) + 1)) ^ A := by ring
      _ ≤ ((h.N : ℝ) * (t : ℝ)) ^ (k + 1 + A) :=
        absorb _ _ _ _ k A hk.le hN16 (Nat.cast_nonneg e) het'
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.IsPtOf
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

section SlopeTestRemainingChoices

variable {O R K : Type} [CommRing O] [CommRing R] [Algebra O R] [IsLocalRing R] [IsNoetherianRing R]
  [NormedField K] [IsUltrametricDist K] [Algebra O K]

omit [IsNoetherianRing R] [IsUltrametricDist K] in
private theorem ipo_mul {f : R →ₐ[O] K} (hf : IsLocPt f) (x : R) {z : R} (hz : z ∈ maximalIdeal R) :
    ‖f (x * z)‖ ≤ ‖f z‖ := by
  rw [map_mul, norm_mul]
  rcases eq_or_ne (f z) 0 with h0 | h0
  · simp [h0]
  have hpos : 0 < ‖f z‖ := norm_pos_iff.mpr h0
  suffices hx : ‖f x‖ ≤ 1 by nlinarith [norm_nonneg (f x)]
  by_contra hx
  push_neg at hx
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (‖f z‖⁻¹) hx
  have hmem : x ^ n * z ∈ maximalIdeal R := Ideal.mul_mem_left _ _ hz
  have h1 := hf _ hmem
  rw [map_mul, map_pow, norm_mul, norm_pow] at h1
  have := (inv_lt_iff_one_lt_mul₀ hpos).mp hn
  linarith [mul_comm (‖f x‖ ^ n) ‖f z‖]

private theorem ipo_rho {f : R →ₐ[O] K} (hf : IsLocPt f) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ z ∈ maximalIdeal R, ‖f z‖ ≤ ρ := by
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (maximalIdeal R) : (maximalIdeal R).FG)
  refine ⟨((s.sup fun g => ‖f g‖₊ : NNReal) : ℝ), NNReal.coe_nonneg _, ?_, ?_⟩
  · have : (s.sup fun g => ‖f g‖₊) < 1 := by
      rw [Finset.sup_lt_iff (by simp)]
      intro g hg
      have hgm : g ∈ maximalIdeal R := hs ▸ Ideal.subset_span hg
      have := hf g hgm
      exact_mod_cast this
    exact_mod_cast this
  · intro z hz
    rw [← hs] at hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      have : ‖f x‖₊ ≤ s.sup fun g => ‖f g‖₊ := Finset.le_sup (f := fun g => ‖f g‖₊) hx
      exact_mod_cast this
    | zero => simp
    | add x y hx hy ihx ihy =>
      rw [map_add (f := _)]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ihx ihy)
    | smul a x hx ihx =>
      rw [smul_eq_mul]
      refine (ipo_mul hf a ?_).trans ihx
      exact hs ▸ hx

private theorem ipo_pow {f : R →ₐ[O] K} (hf : IsLocPt f) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∀ z ∈ maximalIdeal R ^ n, ‖f z‖ < ε := by
  obtain ⟨ρ, hρ0, hρ1, hρ⟩ := ipo_rho hf
  have key : ∀ n : ℕ, ∀ z ∈ maximalIdeal R ^ (n + 1), ‖f z‖ ≤ ρ ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
      intro z hz
      rw [zero_add, pow_one] at hz ⊢
      exact hρ z hz
    | succ n ih =>
      intro z hz
      rw [pow_succ] at hz
      refine Submodule.mul_induction_on hz ?_ ?_
      · intro a ha b hb
        rw [map_mul, norm_mul, pow_succ]
        exact mul_le_mul (ih a ha) (hρ b hb) (norm_nonneg _) (pow_nonneg hρ0 _)
      · intro x y hx hy
        rw [map_add (f := _)]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hρ1
  refine ⟨n + 1, fun z hz => (key n z hz).trans_lt ?_⟩
  calc ρ ^ (n + 1) ≤ ρ ^ n := pow_le_pow_of_le_one hρ0 hρ1.le (Nat.le_succ n)
    _ < ε := hn

private theorem ipo_cont {f : R →ₐ[O] K} (hf : IsLocPt f) {X : Type} [TopologicalSpace X] (u : X → R)
    (hu : AdicCont (maximalIdeal R) u) : Continuous fun g => f (u g) := by
  rw [continuous_iff_continuousAt]
  intro g
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := ipo_pow hf hε
  have hopen := (hu n).isOpen_fiber (Ideal.Quotient.mk (maximalIdeal R ^ n) (u g))
  filter_upwards [hopen.mem_nhds rfl] with g' hg'
  have heq : Ideal.Quotient.mk (maximalIdeal R ^ n) (u g') = Ideal.Quotient.mk (maximalIdeal R ^ n) (u g) := hg'
  rw [Ideal.Quotient.eq] at heq
  rw [dist_eq_norm, ← map_sub]
  exact hn _ heq

end SlopeTestRemainingChoices

private theorem ipo_le_one {l : ℕ} [Fact l.Prime] {c : Coef l} {R : Type} [CommRing R] [Algebra c.O R] [IsCO c.O R]
    {f : R →ₐ[c.O] PadicAlgCl l} (hf : IsLocPt f) (x : R) : ‖f x‖ ≤ 1 := by
  haveI := c.dvr
  haveI : IsLocalHom (algebraMap c.O R) := IsCO.isLocalHom
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  have hm : algebraMap c.O R ϖ ∈ maximalIdeal R := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact hϖ.not_isUnit ((isUnit_map_iff (algebraMap c.O R) ϖ).mp hu)
  have hne : f (algebraMap c.O R ϖ) ≠ 0 := by
    rw [AlgHom.commutes]
    intro h
    apply hϖ.ne_zero
    exact Subtype.ext (by simpa using h)
  have hpos : 0 < ‖f (algebraMap c.O R ϖ)‖ := norm_pos_iff.mpr hne
  have h := ipo_mul hf x hm
  rw [map_mul, norm_mul] at h
  nlinarith [norm_nonneg (f x)]

private theorem diagonal_rep_map_entries {G A B : Type} [Group G] [CommRing A] [CommRing B] (φ : A →+* B) (η : G →* ℤˣ) (Ψ : G →* Aˣ)
    (g : G) (a b : Fin 3) :
    (r0 η ((Units.map φ.toMonoidHom).comp Ψ) g).mat a b = φ ((r0 η Ψ g).mat a b) := by
  simp only [GG.mat, unitaryThreeReflection_left, tor_val, Matrix.diagonal_apply, MonoidHom.comp_apply]
  split_ifs
  · first
      | (rw [← map_zpow, Units.coe_map]; rfl)
      | (rw [← map_pow, Units.coe_map]; rfl)
  · simp

theorem UpperTheory.V.U3.isPt_push :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : (_root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition _ (D.η.comp D.ι) (D.Ψ.comp D.ι)))} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ (S : D.Ring U g₁),
      ∀ f : S.R →ₐ[c.O] PadicAlgCl l, IsLocPt f → D.IsPt U g₁ (push f S.r.hom) := by
  intro Ω _ _ _ K _ _ _ l _ c N _ e ψ D U g₁ _ S f hf
  have hid : S.r.map (AlgHom.id c.O S.R) = S.r := GLift.ext rfl
  have h0 := (S.rep S.R).1 (AlgHom.id c.O S.R)
  rw [hid] at h0
  obtain ⟨hn, hk, φ, hφ, hI⟩ := h0
  have hm : ∀ g a b, (push f S.r.hom g).mat a b = f ((S.r.hom g).mat a b) := fun _ _ _ => rfl
  refine ⟨fun g => S.r.hasMult g, ?_, fun g a b => ipo_le_one hf _, fun g a b => ?_, ⟨?_, ?_, ?_⟩, fun g hg => ?_,
    f.comp φ, fun x hx => hf _ ?_, fun x hx => ?_, ?_⟩
  · exact continuous_matrix fun a b => ipo_cont hf _ (S.r.cont a b)
  · have h1 : (r0 D.η D.ΨQ g).mat a b = algebraMap c.O (PadicAlgCl l) ((r0 D.η D.Ψ g).mat a b) :=
      diagonal_rep_map_entries _ _ _ _ _ _
    rw [hm, h1, ← f.commutes, ← map_sub]
    refine hf _ ((res_eq_zero_iff c.O S.R _).1 ?_)
    have h2 : res c.O S.R ((S.r.hom g).mat a b) = (rbar c.O D.η D.Ψ g).mat a b :=
      congrArg (fun x : GG (m := 3) (R := ResidueField c.O) => x.mat a b) (S.r.red g)
    have h3 : (rbar c.O D.η D.Ψ g).mat a b = residue c.O ((r0 D.η D.Ψ g).mat a b) := diagonal_rep_map_entries _ _ _ _ _ _
    rw [map_sub, AlgHom.commutes, h2, h3]
    exact sub_self _
  · show (S.r.hom D.cc).mat.map (f : S.R →+* PadicAlgCl l) = 1
    rw [hn.atc, Matrix.map_one _ (map_zero _) (map_one _)]
  · have := congrArg f hn.z12
    rw [map_zero, zmat, Matrix.sub_apply, map_sub] at this
    exact this
  · have := congrArg f hn.z21
    rw [map_zero, zmat, Matrix.sub_apply, map_sub] at this
    exact this
  · show GG.map (f : S.R →+* PadicAlgCl l) (S.r.hom g) = 1
    rw [hk g hg, map_one]
  · show φ x ∈ maximalIdeal S.R
    rw [← res_eq_zero_iff c.O, res_map, res_eq_zero_iff]
    exact hx
  · have : φ x = 0 := hI hx
    show f (φ x) = 0
    rw [this, map_zero]
  · have h1 : (U.r.map φ).hom = S.r.hom.comp D.ι := congrArg GLift.hom hφ
    refine MonoidHom.ext fun g => ?_
    show GG.map (f : S.R →+* PadicAlgCl l) ((U.r.map φ).hom g) = _
    rw [h1]
    rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.PowEqOneOfUnr
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private def ball {F : Type} [NormedField F] [IsUltrametricDist F] (ε : ℝ) (h0 : 0 < ε) (h1 : ε ≤ 1) : Subgroup Fˣ where
  carrier := {u | ‖(u : F) - 1‖ < ε}
  one_mem' := by simpa using h0
  mul_mem' {a b} ha hb := by
    have ha' : ‖(a : F) - 1‖ < ε := ha
    have hb' : ‖(b : F) - 1‖ < ε := hb
    show ‖((a * b : Fˣ) : F) - 1‖ < ε
    have e : ((a * b : Fˣ) : F) - 1 = ((a : F) - 1) * ((b : F) - 1) + (((a : F) - 1) + ((b : F) - 1)) := by
      rw [Units.val_mul]; ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_
      ((IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha' hb')))
    rw [norm_mul]
    nlinarith [norm_nonneg ((a : F) - 1), norm_nonneg ((b : F) - 1)]
  inv_mem' {a} ha := by
    have ha' : ‖(a : F) - 1‖ < ε := ha
    show ‖((a⁻¹ : Fˣ) : F) - 1‖ < ε
    have hn : ‖(a : F)‖ = 1 := by
      have h2 : ‖(a : F) - 1‖ < ‖(1 : F)‖ := by rw [norm_one]; exact ha'.trans_le h1
      have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h2.ne
      rw [sub_add_cancel, max_eq_right h2.le, norm_one] at this
      exact this
    have e : (a : F) * (((a⁻¹ : Fˣ) : F) - 1) = -((a : F) - 1) := by
      rw [mul_sub, Units.mul_inv]; ring
    have := congrArg norm e
    rw [norm_mul, hn, one_mul, norm_neg] at this
    rwa [this]

private theorem eq_one_of_pow {F : Type} [NormedField F] [IsUltrametricDist F] (x : F) (hx : ‖x - 1‖ < 1) (h : ℕ)
    (hh : ‖(h : F)‖ = 1) (e : x ^ h = 1) : x = 1 := by
  have hn : ‖x‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (x - 1) 1
    rw [sub_add_cancel, norm_one] at this
    exact this.trans (max_le hx.le le_rfl)
  have h1 : ∀ n : ℕ, ‖x ^ n - 1‖ < 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : x ^ (n + 1) - 1 = x * (x ^ n - 1) + (x - 1) := by ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ hx)
      rw [norm_mul]
      nlinarith [norm_nonneg x, norm_nonneg (x ^ n - 1)]
  have h2 : ∀ n : ℕ, ‖∑ i ∈ Finset.range n, x ^ i - n‖ < 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : ∑ i ∈ Finset.range (n + 1), x ^ i - ((n + 1 : ℕ) : F) =
          (∑ i ∈ Finset.range n, x ^ i - n) + (x ^ n - 1) := by
        rw [Finset.sum_range_succ]; push_cast; ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ih (h1 n))
  have h3 := geom_sum_mul x h
  rw [e, sub_self, mul_eq_zero] at h3
  rcases h3 with h3 | h3
  · have := h2 h
    rw [h3, zero_sub, norm_neg, hh] at this
    exact absurd this (lt_irrefl _)
  · exact sub_eq_zero.1 h3

private theorem pow_eq_one_of_unr {K Ω F : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    [_root_.NumberField.IsTotallyComplex K] [NormedField F] [IsUltrametricDist F] (κ : G K Ω →* Fˣ) (hc : Continuous fun g => (κ g : F))
    (hI : ∀ (A : ValuationSubring Ω), ∀ g ∈ Ine (F := K) A, κ g = 1) (g : G K Ω) : (κ g : F) ^ classNumber K = 1 := by
  have key : ∀ (ε : ℝ) (h0 : 0 < ε) (h1 : ε ≤ 1), ‖(κ g : F) ^ classNumber K - 1‖ < ε := by
    intro ε h0 h1
    let χ := (QuotientGroup.mk' (ball (F := F) ε h0 h1)).comp κ
    have hχ : ∀ x, x ∈ χ.ker ↔ ‖(κ x : F) - 1‖ < ε := fun x => QuotientGroup.eq_one_iff (κ x)
    have hle := Kum.artKer K Ω _ χ ?_ ?_ ?_
    · have hg : g ^ classNumber K ∈ (Kum.artCl K Ω).ker := by
        rw [MonoidHom.mem_ker, map_pow, classNumber]
        exact pow_card_eq_one
      have := (hχ _).1 (hle hg)
      rwa [map_pow, Units.val_pow_eq_pow_val] at this
    · have : (χ.ker : Set (G K Ω)) = {x | ‖(κ x : F) - 1‖ < ε} := Set.ext hχ
      rw [this]
      exact isOpen_lt (hc.sub continuous_const).norm continuous_const
    · intro A x hx
      rw [hχ, hI A x hx]
      simpa using h0
    · rintro c ⟨j, hj⟩
      exfalso
      have hE : ComplexEmbedding.IsReal (j.comp (algebraMap K Ω)) := by
        rw [ComplexEmbedding.isReal_iff]
        ext y
        rw [ComplexEmbedding.conjugate_coe_eq]
        exact (hj (algebraMap K Ω y)).symm.trans (congrArg j (c.commutes y))
      exact IsTotallyComplex.complexEmbedding_not_isReal _ hE
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  by_contra hne
  have hpos := not_le.1 hne
  exact absurd (key _ (lt_min hpos one_pos) (min_le_right _ _)) (not_lt.2 (min_le_left _ _))

theorem UpperTheory.V.U3.char_eq_one :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) (κ : D.η.ker →* (PadicAlgCl l)ˣ),
      Continuous (fun g => (κ g : PadicAlgCl l)) → (∀ g, ‖(κ g : PadicAlgCl l) - 1‖ < 1) →
      (∀ (A : ValuationSubring Ω) (g : D.η.ker), (g : G ℚ Ω) ∈ Ine (F := ℚ) A → κ g = 1) → κ = 1 := by
  intro Ω _ _ _ K _ _ _ l _ c N _ e ψ D κ hc h1 hI
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  haveI := D.gd.imag
  let ι : G K Ω →* D.η.ker := (galEmb ℚ K Ω).codRestrict D.η.ker fun s => D.η_ker ▸ galEmb_mem ℚ K Ω s
  have hι : Continuous ι := (galEmbTop ℚ K Ω).1.continuous.subtype_mk _
  have hp := pow_eq_one_of_unr (κ.comp ι) (hc.comp hι) fun A g hg =>
    hI A (ι g) (by
      rw [← ((galEmbFam ℚ K Ω l).1 A).2] at hg
      exact hg)
  have hh : ‖((classNumber K : ℕ) : PadicAlgCl l)‖ = 1 := by
    have hnd : ¬ l ∣ classNumber K := fun h => D.gd.l_cop (h.mul_left _)
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap', Padic.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hnd
  refine MonoidHom.ext fun g => ?_
  have hg : g.1 ∈ (galEmb ℚ K Ω).range := by
    rw [range_galEmb, ← D.η_ker]
    exact g.2
  obtain ⟨s, hs⟩ := hg
  have e : ι s = g := Subtype.ext hs
  have := hp s
  rw [MonoidHom.comp_apply, e] at this
  exact Units.ext (eq_one_of_pow _ (h1 g) _ hh this)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsDat
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem dx_cc (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] :
    ∃ σ : G ℚ Ω, ∃ φ : Ω →+* ℂ, ∀ x, φ (σ x) = starRingEnd ℂ (φ x) := by
  obtain ⟨σ, h⟩ := exists_isConjOm (E := ℚ) (Ω := Ω)
  exact ⟨AlgEquiv.ofRingEquiv (f := σ) fun x => by rw [eq_ratCast (algebraMap ℚ Ω), map_ratCast], h⟩

private theorem dx_ker (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω]
    [IsGalois ℚ K] (σ : G ℚ Ω) : AlgEquiv.restrictNormalHom (F := ℚ) K σ = 1 ↔ σ ∈ galOf ℚ K Ω := by
  have h : ∀ x : K, algebraMap K Ω (AlgEquiv.restrictNormalHom (F := ℚ) K σ x) = σ (algebraMap K Ω x) :=
    fun x => AlgEquiv.restrictNormal_commutes σ K x
  refine ⟨fun h1 x => ?_, fun h1 => AlgEquiv.ext fun x => (algebraMap K Ω).injective ?_⟩
  · rw [← h, h1]; rfl
  · rw [h, h1]; rfl

private theorem dx_eta (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω]
    [IsGalois ℚ K] (h2 : Module.finrank ℚ K = 2) : ∃ η : G ℚ Ω →* ℤˣ, η.ker = galOf ℚ K Ω := by
  have hc : Nat.card Gal(K/ℚ) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  have hz : Nat.card ℤˣ = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_units_int]
  let e : Gal(K/ℚ) ≃* ℤˣ := mulEquivOfPrimeCardEq hc hz
  refine ⟨e.toMonoidHom.comp (AlgEquiv.restrictNormalHom (F := ℚ) K), Subgroup.ext fun σ => ?_⟩
  rw [← dx_ker, MonoidHom.mem_ker, MonoidHom.comp_apply]
  exact map_eq_one_iff e e.injective

private theorem dx_unr (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K]
    [Algebra K Ω] [IsGalois ℚ K] (l : ℕ) [hl : Fact l.Prime] (h : ¬ (l : ℤ) ∣ discr K) (A : ValuationSubring Ω)
    (hA : A.valuation (l : Ω) < 1) : Ine (F := ℚ) A ≤ galOf ℚ K Ω := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic K Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  haveI : IsAlgClosure K Ω := ⟨inferInstance, inferInstance⟩
  obtain ⟨p1, p2, p3, -⟩ := places K Ω l A
  obtain ⟨w, hw⟩ := p1 fun ht => (p2 ht).2 hA
  have hm : ((l : ℕ) : 𝓞 K) ∈ w.asIdeal := (p3 w hw).1 hA
  have hb := (CF.unramIff.1 K l hl.out).1 ((CF.unramIff.2.1 K l hl.out).2 h) w hm
  intro σ hσ
  have h1 := Subgroup.mem_map_of_mem (CF.resTo ℚ K Ω) hσ
  rw [CF.ineAbs ℚ K Ω A w hw, hb, Subgroup.mem_bot] at h1
  exact (dx_ker Ω K σ).1 h1

private theorem dx_lc {Γ M : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group M] (f : Γ →* M)
    (h : IsOpen (f.ker : Set Γ)) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hc : Continuous fun y : Γ => x⁻¹ * y := by fun_prop
  have h1 : (fun y : Γ => x⁻¹ * y) ⁻¹' (f.ker : Set Γ) ∈ nhds x :=
    (h.preimage hc).mem_nhds (by simp)
  filter_upwards [h1] with y hy
  have h2 : f (x⁻¹ * y) = 1 := hy
  rw [map_mul, map_inv, inv_mul_eq_one] at h2
  exact h2.symm

private theorem dx_zpow {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (I : Ideal R)
    (Ψ : Γ → Rˣ) (h : AdicCont I fun g => (Ψ g : R)) (j : ℤ) : AdicCont I fun g => ((Ψ g ^ j : Rˣ) : R) := by
  classical
  intro N
  have key : (fun g => Ideal.Quotient.mk (I ^ N) ((Ψ g ^ j : Rˣ) : R)) =
      (fun x : R ⧸ I ^ N => if hx : IsUnit x then ((hx.unit ^ j : (R ⧸ I ^ N)ˣ) : R ⧸ I ^ N) else 0) ∘
        fun g => Ideal.Quotient.mk (I ^ N) (Ψ g : R) := by
    funext g
    have hx : IsUnit (Ideal.Quotient.mk (I ^ N) (Ψ g : R)) := (Ψ g).isUnit.map _
    have e : hx.unit = Units.map (Ideal.Quotient.mk (I ^ N)).toMonoidHom (Ψ g) := Units.ext rfl
    simp only [Function.comp_apply, dif_pos hx]
    rw [e, ← map_zpow]
    rfl
  rw [key]
  exact (h N).comp _

private theorem dx_alg {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {l : ℕ} [Fact l.Prime] [Algebra ℤ_[l] R]
    (I : Ideal R) (hI : (l : R) ∈ I) (f : Γ → ℤ_[l]) (hf : Continuous f) :
    AdicCont I fun g => algebraMap ℤ_[l] R (f g) := by
  intro n
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hpos : (0 : ℝ) < (l : ℝ) ^ (-(n : ℤ)) := zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
  filter_upwards [hf.continuousAt.eventually (Metric.closedBall_mem_nhds (f x) hpos)] with y hy
  rw [dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton'] at hy
  obtain ⟨a, ha⟩ := hy
  rw [Ideal.Quotient.eq, ← map_sub, ← ha, map_mul, map_pow, map_natCast]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hI n)

private theorem dx_lmem (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    [Module.Finite ℤ_[l] O] : (l : O) ∈ IsLocalRing.maximalIdeal O := by
  have h : (IsLocalRing.maximalIdeal O).comap (algebraMap ℤ_[l] O) = IsLocalRing.maximalIdeal ℤ_[l] :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := ℤ_[l]) _)
  have h1 : (l : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l] := by
    rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
  rw [← h, Ideal.mem_comap, map_natCast] at h1
  exact h1

private theorem dx_dir (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {O : Type} [CommRing O] {N : ℕ} [NeZero N]
    (ψ : DirichletCharacter O N) : IsLocallyConstant (Chr.dirG ℚ Ω ψ) :=
  (dx_lc _ (Chr.clsFacts ℚ Ω N).1).comp ψ.toUnitHom

private theorem dx_cont (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
    {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
    {N : ℕ} [NeZero N] (e : ℕ) (ψ : DirichletCharacter O N) : CharCont (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) := by
  refine dx_zpow _ _ fun n => ?_
  have h1 : AdicCont (IsLocalRing.maximalIdeal O) fun g => (chiO ℚ Ω l O g : O) :=
    dx_alg _ (dx_lmem l O) (fun g => (cycZ ℚ Ω l g : ℤ_[l])) (Units.continuous_val.comp (contTw ℚ Ω l).1)
  have h2 := dx_zpow _ _ h1 (e : ℤ) n
  have h3 := (dx_dir Ω ψ).comp fun u : Oˣ => Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ n) (u : O)
  have h4 := h2.mul h3
  convert h4 using 1
  rfl

private theorem dx_place {Ω : Type} [Field Ω] [CharZero Ω] {l : ℕ} [hl : Fact l.Prime] (j : Ω →+* Om l) :
    (Loc.placeJ j).valuation (l : Ω) < 1 := by
  have h0 : (l : Ω) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  have h1 : (l : Ω)⁻¹ ∉ Loc.placeJ j := by
    intro h
    have h2 : ‖j (l : Ω)⁻¹‖ ≤ 1 := h
    have h3 : j (l : Ω)⁻¹ = algebraMap ℚ_[l] (Om l) (l : ℚ_[l])⁻¹ := by simp
    rw [h3, PadicAlgCl.norm_extends, norm_inv, Padic.norm_p, inv_inv] at h2
    exact absurd hl.out.one_lt (by exact_mod_cast h2.not_gt)
  rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, not_le,
    one_lt_inv₀ ((Valuation.pos_iff _).2 h0)] at h1
  exact h1

theorem UpperTheory.V.U3.exists_dat :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N}, GD Ω K l e ψ → Nonempty (Dat Ω K c e ψ) := by
  intro Ω _ _ _ K _ _ _ l hl c N _ e ψ h
  haveI : Algebra.IsQuadraticExtension ℚ K := ⟨h.quad⟩
  haveI : IsGalois ℚ K := inferInstance
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic K Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  haveI : IsAlgClosure K Ω := ⟨inferInstance, inferInstance⟩
  obtain ⟨η, hη⟩ := dx_eta Ω K h.quad
  obtain ⟨cc, hcc⟩ := dx_cc Ω
  obtain ⟨j⟩ := Loc.exists_emb (Ω := Ω) (v := l)
  obtain ⟨i1, -, i3, -, i5, -⟩ := Loc.iotaFacts j
  have hA : (Loc.placeJ j).valuation (l : Ω) < 1 := dx_place j
  have hI : ∀ g ∈ Loc.Iq l, Loc.iota j g ∈ Ine (F := ℚ) (Loc.placeJ j) := fun g hg => by
    rw [← i3] at hg; exact hg
  have hopen : IsOpen (((η.comp (Loc.iota j)).ker : Subgroup (GQ l)) : Set (GQ l)) := by
    have h1 := (galEmbTop ℚ K Ω).2.1
    rw [← hη] at h1
    exact h1.preimage i1.continuous
  obtain ⟨Kv, -, -, -, -, hKv, -⟩ := Loc.openField (η.comp (Loc.iota j)).ker.subtype hopen.isOpenEmbedding_subtypeVal
  rw [Subgroup.range_subtype] at hKv
  have hd : ¬ (l : ℤ) ∣ discr K := fun hd => h.l_cop (Dvd.dvd.mul_right (Int.natCast_dvd.1 hd) _)
  exact ⟨{
    gd := h
    η := η
    η_ker := hη
    cc := cc
    conj := hcc
    j := j
    ι := Loc.iota j
    ι_cont := i1.continuous
    ι_spec := fun σ x => (Loc.iota_spec j σ x).symm
    Kv := Kv
    Kv_spec := fun g => by rw [← hKv]; rfl
    η_unr := fun g hg => by
      have h1 := dx_unr Ω K l hd _ hA (hI g hg)
      rw [← hη] at h1
      exact h1
    τ_open := ((dx_dir Ω (comp l ψ)).comp_continuous i1.continuous).isOpen_fiber 1
    Ψ_cont := dx_cont Ω e ψ
    Ψ_I := fun g hg => by
      rw [← ((compIne Ω N l hl.out _ hA).2 c.O ψ).1 _ (hI g hg), Chr.Psi, MonoidHom.mul_apply, zpow_natCast,
        MonoidHom.pow_apply, Loc.cycA, ← i5 l]
      rfl }⟩
end
