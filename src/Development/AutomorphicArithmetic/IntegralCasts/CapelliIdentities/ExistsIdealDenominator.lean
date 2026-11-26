module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementT

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsIdealDenominator
theorem UpperTheory.Reformulated.B.ExistsIdealDenominator.exists_denI :
    ∀ {D : Formalism.BasicNotions.D7} (u : D.what₂.Word) (i : ℕ) (x : ((D.fm u).lat i).V),
    ∃ (d : NumberField.RingOfIntegers D.what₂.LL),
      d ≠ (0 : NumberField.RingOfIntegers D.what₂.LL) ∧
        d • x ∈
          ((D.fm u).lat
              i).L := by
  intro D u i x
  have hx : x ∈ Submodule.span D.what₂.LL (((D.fm u).lat i).L : Set ((D.fm u).lat i).V) := by
    rw [((D.fm u).lat_good i).2.2]
    exact Submodule.mem_top
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span
    (nonZeroDivisors (NumberField.RingOfIntegers D.what₂.LL)) D.what₂.LL _ x hx
  rw [Submodule.span_eq] at ht
  exact ⟨t.1, nonZeroDivisors.ne_zero t.2, ht⟩
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsSmulMemLattice
theorem UpperTheory.Reformulated.B.ExistsIntegerSmulMemOfSpanEqTop.exists_smul_mem :
    ∀ {D : Formalism.BasicNotions.D7} {N : ℕ}
    {L₁ : Submodule (NumberField.RingOfIntegers D.host.E) (Fin N → D.host.E)},
    Submodule.span D.host.E (↑L₁ : Set (Fin N → D.host.E)) = ⊤ →
      ∀ (x : Fin N → D.host.E),
        ∃ (n : NumberField.RingOfIntegers D.host.E),
          n ≠ (0 : NumberField.RingOfIntegers D.host.E) ∧
            (↑n : D.host.E) • x ∈
              L₁ := by
  intro D N L₁ h x
  have hx : x ∈ Submodule.span D.host.E (↑L₁ : Set (Fin N → D.host.E)) := h ▸ Submodule.mem_top
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span
    (nonZeroDivisors (NumberField.RingOfIntegers D.host.E)) D.host.E _ x hx
  rw [Submodule.span_eq] at ht
  exact ⟨t, nonZeroDivisors.ne_zero t.2, ht⟩
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LatticeVariant
theorem UpperTheory.Reformulated.B.LatticeVariant.lsd_spanDen :
    ∀ {D : Formalism.BasicNotions.D7} {n : ℕ}
    (L : Submodule (NumberField.RingOfIntegers D.host.E) (Fin n → D.host.E)),
    Submodule.span D.host.E (↑L : Set (Fin n → D.host.E)) = ⊤ →
      ∀ (x : Fin n → D.host.E),
        ∃ (d : NumberField.RingOfIntegers D.host.E),
          d ≠ (0 : NumberField.RingOfIntegers D.host.E) ∧
            (↑d : D.host.E) • x ∈
              L := by
  intro D n L hL x
  have hx : x ∈ Submodule.span D.host.E (↑L : Set (Fin n → D.host.E)) := hL ▸ Submodule.mem_top
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span
    (nonZeroDivisors (NumberField.RingOfIntegers D.host.E)) D.host.E _ x hx
  rw [Submodule.span_eq] at ht
  exact ⟨t.1, nonZeroDivisors.ne_zero t.2, ht⟩
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsDenominatorThird
theorem UpperTheory.Reformulated.B.ExistsDenominatorThird.exists_den :
    ∀ {D : Formalism.BasicNotions.D7} (u : D.what₂.Word) (x : ((D.fm u).lat (0 : ℕ)).V),
    ∃ (d : NumberField.RingOfIntegers D.what₂.LL),
      d ≠ (0 : NumberField.RingOfIntegers D.what₂.LL) ∧
        d • x ∈
          ((D.fm u).lat
              (0 :
                ℕ)).L := by
  intro D u x
  have hx : x ∈ Submodule.span D.what₂.LL
      ((((D.fm u).lat 0).L : Set ((D.fm u).lat 0).V)) := by
    rw [((D.fm u).lat_good 0).2.2]
    exact Submodule.mem_top
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span
    (nonZeroDivisors (NumberField.RingOfIntegers D.what₂.LL)) D.what₂.LL _ x hx
  rw [Submodule.span_eq] at ht
  exact ⟨t.1, nonZeroDivisors.ne_zero t.2, ht⟩
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsFurtherLast
theorem UpperTheory.Reformulated.B.Rd4.exists_nat_smul_mem :
    ∀ {D : Formalism.BasicNotions.D7} {n : ℕ}
    {Λ : Submodule (NumberField.RingOfIntegers D.host.E) (Fin n → D.host.E)},
    Submodule.IsFullLattice D.host.E Λ →
      ∀ (x : Fin n → D.host.E),
        ∃ (N : ℕ),
          (0 : ℕ) < N ∧
            (↑N : D.host.E) • x ∈
              Λ := by
  intro D n Λ h x
  obtain ⟨⟨_, m, hm, rfl⟩, ht⟩ := multiple_mem_span_of_mem_localization_span
    (Algebra.algebraMapSubmonoid (NumberField.RingOfIntegers D.host.E) (nonZeroDivisors ℤ))
    D.host.E (Λ : Set (Fin n → D.host.E)) x (by rw [h.span_eq_top]; trivial)
  change algebraMap ℤ (NumberField.RingOfIntegers D.host.E) m • x ∈ _ at ht
  rw [Submodule.span_eq, algebraMap_smul] at ht
  have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
  refine ⟨m.natAbs * m.natAbs, by positivity, ?_⟩
  rw [Nat.cast_smul_eq_nsmul, ← natCast_zsmul, Int.natAbs_mul_self, mul_smul]
  exact zsmul_mem ht m
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CanonicalTranslateJets
theorem UpperTheory.Reformulated.B.CanonicalTranslateJets.K_repr :
    ∀ (D : Formalism.BasicNotions.D7),
    ∀ x ∈ D.host.K,
      ∃ (p : ℚ) (q : ℚ),
        x =
          (↑p : D.host.E) +
            (↑q : D.host.E) *
              D.host.sqd := by
  intro D x hx
  have hs := D.host.sqd_sq
  have hx' : x ∈ Algebra.adjoin ℚ ({D.host.sqd} : Set D.host.E) :=
    (IntermediateField.adjoin_toSubalgebra_of_isAlgebraic fun y _ => Algebra.IsAlgebraic.isAlgebraic y).le hx
  clear hx
  induction hx' using Algebra.adjoin_induction with
  | mem y hy => exact ⟨0, 1, by simpa using hy⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy; obtain ⟨c, e, rfl⟩ := hz
    exact ⟨a + c, b + e, by push_cast; ring⟩
  | mul y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy; obtain ⟨c, e, rfl⟩ := hz
    exact ⟨a * c - b * e * D.host.d, a * e + b * c, by push_cast; linear_combination (b * e : D.host.E) * hs⟩
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsNatSmulMem
private theorem UpperTheory.Reformulated.B.ExistsNatSmulMem.exists_den {K : Type*} [Field K] [NumberField K] (c : K) :
    ∃ (M : ℕ) (a : NumberField.RingOfIntegers K), 0 < M ∧ (M : K) * c = a := by
  have hc : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic c)
  obtain ⟨y, hy, hi⟩ := hc.exists_integral_multiple
  have h2 : IsIntegral ℤ (y • y • c) := hi.smul y
  refine ⟨(y * y).natAbs, ⟨_, h2⟩, Int.natAbs_pos.2 (mul_ne_zero hy hy), ?_⟩
  have : (((y * y).natAbs : ℕ) : K) = ((y * y : ℤ) : K) := by
    rw [← Int.cast_natCast, Int.natAbs_of_nonneg (mul_self_nonneg y)]
  rw [this]
  change _ = y • y • c
  simp [mul_assoc]

private theorem UpperTheory.Reformulated.B.ExistsNatSmulMem.core {K V : Type*} [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V]
    {Λ : Submodule (NumberField.RingOfIntegers K) V}
    (h : Submodule.span K (Λ : Set V) = ⊤) (x : V) :
    ∃ N : ℕ, 0 < N ∧ (N : K) • x ∈ Λ := by
  have hn : ∀ (M : ℕ) (v : V), v ∈ Λ → (M : K) • v ∈ Λ := fun M v hv => by
    rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hv M
  have hx : x ∈ Submodule.span K (Λ : Set V) := h ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem v hv => exact ⟨1, one_pos, hn 1 v hv⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨N, hN, hu⟩ := hu
    obtain ⟨M, hM, hv⟩ := hv
    refine ⟨N * M, Nat.mul_pos hN hM, ?_⟩
    have : ((N * M : ℕ) : K) • (u + v) = (M : K) • (N : K) • u + (N : K) • (M : K) • v := by
      rw [smul_add, smul_smul, smul_smul, Nat.cast_mul, mul_comm (M : K)]
    rw [this]
    exact Λ.add_mem (hn _ _ hu) (hn _ _ hv)
  | smul c v _ hv =>
    obtain ⟨N, hN, hv⟩ := hv
    obtain ⟨M, a, hM, ha⟩ := UpperTheory.Reformulated.B.ExistsNatSmulMem.exists_den c
    refine ⟨N * M, Nat.mul_pos hN hM, ?_⟩
    have : ((N * M : ℕ) : K) • c • v = a • (N : K) • v := by
      rw [← algebraMap_smul K a, smul_smul, smul_smul, Nat.cast_mul, mul_assoc, ha, mul_comm]
    rw [this]
    exact Λ.smul_mem a hv

theorem UpperTheory.Reformulated.B.ExistsNatSmulMem.exists_nat_smul_mem :
    ∀ {D : Formalism.BasicNotions.D7} {n : ℕ}
    {Λ : Submodule (NumberField.RingOfIntegers D.host.E) (Fin n → D.host.E)},
    Submodule.IsFullLattice D.host.E Λ →
      ∀ (x : Fin n → D.host.E),
        ∃ (N : ℕ),
          (0 : ℕ) < N ∧
            (↑N : D.host.E) • x ∈
              Λ := by
  intro D n Λ h x
  exact UpperTheory.Reformulated.B.ExistsNatSmulMem.core h.span_eq_top x
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EmbeddingTypes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem UpperTheory.Reformulated.B.EmbeddingTypes.core {R K V : Type*} [CommRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    (L : Submodule R V) (hL : Submodule.span K (L : Set V) = ⊤) (y : V) :
    ∃ s ∈ nonZeroDivisors R, s • y ∈ L := by
  have hy : y ∈ Submodule.span K (L : Set V) := hL ▸ Submodule.mem_top
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors R) K _ y hy
  exact ⟨t, t.2, by simpa [Submonoid.smul_def] using ht⟩

theorem UpperTheory.Reformulated.B.EmbeddingTypes.exists_smul_mem_base_lattice_alt :
    ∀ (D : Formalism.BasicNotions.D7) (j : ℕ) (y : (D.sp.W j).V),
    ∃ s ∈ nonZeroDivisors (NumberField.RingOfIntegers D.host.E),
      s • y ∈
        (D.sp.W
            j).L0 := by
  intro D j y
  classical
  let S := D.sp.W j
  have hspan : Submodule.span D.host.E (S.L0 : Set S.V) = ⊤ := by
    let W := Submodule.span D.host.E (S.L0 : Set S.V)
    change W = ⊤
    by_contra h
    let b := Module.finBasis D.host.E W
    let g : S.V →ₗ[D.host.E] (Fin (Module.finrank D.host.E W) → D.host.E) :=
      LinearMap.pi fun k => S.hT (b k)
    have hdim : Module.finrank D.host.E (Fin (Module.finrank D.host.E W) → D.host.E) < Module.finrank D.host.E S.V := by
      simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
      exact Submodule.finrank_lt h
    obtain ⟨x, hx, hx₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    have hzero (y : W) : S.hT y x = 0 := by
      have hb : ∀ k, S.hT (b k) x = 0 := by
        intro k
        exact congrFun (LinearMap.mem_ker.mp hx) k
      have hy : y ∈ Submodule.span D.host.E (Set.range b) := b.span_eq ▸ Submodule.mem_top
      induction hy using Submodule.span_induction with
      | mem z hz => obtain ⟨k, rfl⟩ := hz; exact hb k
      | zero => simp
      | add u v _ _ hu hv => simp [map_add, hu, hv]
      | smul a z _ hz => simp [LinearMap.map_smulₛₗ, hz]
    have hsmul (a : D.host.E) : a • x ∈ S.L0 := by
      rw [← S.baseLattice_isUnimodular]
      change a • x ∈ Formalism.E.hdual S.hT S.L0
      simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
        LinearMap.restrictScalars_apply]
      intro y hy
      have hyzero := hzero ⟨y, Submodule.subset_span hy⟩
      simp [map_smul, hyzero]
    let i : D.host.E →ₗ[NumberField.RingOfIntegers D.host.E] S.L0 :=
      ((LinearMap.toSpanSingleton D.host.E _ x).restrictScalars _).codRestrict S.L0 hsmul
    let : Module.Finite (NumberField.RingOfIntegers D.host.E) S.L0 :=
      Module.Finite.iff_fg.mpr S.standardTuple_isLattice.fg
    let : Module.Finite (NumberField.RingOfIntegers D.host.E) D.host.E :=
      Module.Finite.of_injective i fun a b hab =>
        smul_left_injective D.host.E hx₀ (congrArg Subtype.val hab)
    exact NumberField.RingOfIntegers.not_isField D.host.E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (NumberField.RingOfIntegers D.host.E) D.host.E) (Field.toIsField D.host.E))
  exact UpperTheory.Reformulated.B.EmbeddingTypes.core (K := D.host.E) _ hspan y
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralClosureCriterionSecond
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralImagQuadraticHalfInt
open Polynomial

private lemma coords {E : Type} [Field E] [CharZero E] (d : ℕ) (s : E) (hs : s ^ 2 = -(d : E))
    (z : E) (hz : z ∈ IntermediateField.adjoin ℚ ({s} : Set E)) :
    ∃ a b : ℚ, z = (a : E) + (b : E) * s := by
  have hint : IsIntegral ℚ s := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [hs]
    exact (isIntegral_natCast d).neg
  have hz' : z ∈ Algebra.adjoin ℚ ({s} : Set E) := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hz
  clear hz
  induction hz' using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact ⟨0, 1, by simp [hx]⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, e, rfl⟩ := hy
    exact ⟨a + c, b + e, by push_cast; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, e, rfl⟩ := hy
    refine ⟨a * c - d * b * e, a * e + b * c, ?_⟩
    push_cast
    linear_combination (b : E) * e * hs

private lemma aeval_pair {E : Type} [Field E] [CharZero E] (d : ℕ) (s : E) (hs : s ^ 2 = -(d : E))
    (a b : ℚ) (p : ℤ[X]) :
    ∃ u v : ℚ, aeval ((a : E) + (b : E) * s) p = (u : E) + (v : E) * s ∧
      aeval ((a : E) - (b : E) * s) p = (u : E) - (v : E) * s := by
  induction p using Polynomial.induction_on with
  | C c => exact ⟨c, 0, by simp, by simp⟩
  | add p q hp hq =>
    obtain ⟨u, v, h1, h2⟩ := hp
    obtain ⟨u', v', h1', h2'⟩ := hq
    refine ⟨u + u', v + v', ?_, ?_⟩
    · rw [map_add (f := _), h1, h1']; push_cast; ring
    · rw [map_add (f := _), h2, h2']; push_cast; ring
  | monomial n c h =>
    obtain ⟨u, v, h1, h2⟩ := h
    refine ⟨u * a - d * v * b, u * b + v * a, ?_, ?_⟩
    · rw [pow_succ, ← mul_assoc, map_mul, h1, aeval_X]
      push_cast
      linear_combination (v : E) * b * hs
    · rw [pow_succ, ← mul_assoc, map_mul, h2, aeval_X]
      push_cast
      linear_combination (v : E) * b * hs

private lemma conj_integral {E : Type} [Field E] [CharZero E] (d : ℕ) (s : E) (hd : 0 < d)
    (hs : s ^ 2 = -(d : E)) (a b : ℚ) (h : IsIntegral ℤ ((a : E) + (b : E) * s)) :
    IsIntegral ℤ ((a : E) - (b : E) * s) := by
  obtain ⟨p, hp, h0⟩ := h
  obtain ⟨u, v, h1, h2⟩ := aeval_pair d s hs a b p
  rw [← aeval_def, h1] at h0
  have hn : u ^ 2 + d * v ^ 2 = 0 := by
    have : (u : E) ^ 2 + d * (v : E) ^ 2 = 0 := by
      linear_combination ((u : E) - v * s) * h0 + (v : E) ^ 2 * hs
    exact_mod_cast this
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  have hv2 : 0 ≤ (d : ℚ) * v ^ 2 := by positivity
  have hu : u = 0 := by nlinarith [sq_nonneg u]
  have hv : v = 0 := by
    rw [hu] at hn
    have : (d : ℚ) * v ^ 2 = 0 := by simpa using hn
    simpa [hd'.ne'] using this
  refine ⟨p, hp, ?_⟩
  rw [← aeval_def, h2, hu, hv]
  simp

private lemma rat_int {E : Type} [Field E] [CharZero E] (q : ℚ) (h : IsIntegral ℤ (q : E)) :
    ∃ n : ℤ, (n : ℚ) = q := by
  have h' : IsIntegral ℤ q := by
    have := (isIntegral_algebraMap_iff (R := ℤ) (A := ℚ) (B := E) (x := q)
      ).1 (by simpa using h)
    exact this
  simpa using (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1 h'

private lemma int_of_sqfree_mul_sq (d : ℕ) (hd : Squarefree d) (q : ℚ) (m : ℤ)
    (h : (m : ℚ) = d * q ^ 2) : ∃ n : ℤ, (n : ℚ) = q := by
  have h1 : q * q.den = q.num := Rat.mul_den_eq_num q
  have h2 : (d : ℤ) * q.num ^ 2 = (q.den : ℤ) ^ 2 * m := by
    have : (d : ℚ) * (q.num : ℚ) ^ 2 = (q.den : ℚ) ^ 2 * m := by
      rw [← h1, h]; ring
    exact_mod_cast this
  have hc : IsCoprime ((q.den : ℤ) ^ 2) (q.num ^ 2) :=
    (Rat.isCoprime_num_den q).symm.pow
  have h3 : (q.den : ℤ) ^ 2 ∣ d := hc.dvd_of_dvd_mul_right ⟨m, h2⟩
  have h4 : q.den * q.den ∣ d := by
    rw [← sq]; exact_mod_cast h3
  have h5 : q.den = 1 := Nat.isUnit_iff.1 (hd _ h4)
  exact ⟨q.num, by rw [← h1, h5]; simp⟩

theorem UpperTheory.integral_imag_quadratic_half_int :
    ∀ (E : Type) [Field E] [CharZero E] (d : ℕ) (s : E), Squarefree d → s ^ 2 = -(d : E) → ∀ z : E, z ∈ IntermediateField.adjoin ℚ ({s} : Set E) → IsIntegral ℤ z → ∃ x y : ℤ, Even (x - y) ∧ z = ((x : E) + (y : E) * s) / 2 := by
  intro E _ _ d s hd hs z hz hi
  obtain ⟨a, b, rfl⟩ := coords d s hs z hz
  have hc := conj_integral d s (Nat.pos_of_ne_zero hd.ne_zero) hs a b hi
  obtain ⟨x, hx⟩ := rat_int (E := E) (2 * a) (by
    have e : ((2 * a : ℚ) : E) = (a : E) + (b : E) * s + ((a : E) - (b : E) * s) := by
      push_cast; ring
    rw [e]
    exact hi.add hc)
  obtain ⟨n, hn⟩ := rat_int (E := E) (a ^ 2 + d * b ^ 2) (by
    have e : ((a ^ 2 + d * b ^ 2 : ℚ) : E)
        = ((a : E) + (b : E) * s) * ((a : E) - (b : E) * s) := by
      push_cast
      linear_combination (b : E) ^ 2 * hs
    rw [e]
    exact hi.mul hc)
  obtain ⟨y, hy⟩ := int_of_sqfree_mul_sq d hd (2 * b) (4 * n - x ^ 2) (by
    push_cast
    rw [hx, hn]; ring)
  have key : x ^ 2 + d * y ^ 2 = 4 * n := by
    have : (x : ℚ) ^ 2 + d * (y : ℚ) ^ 2 = 4 * n := by
      rw [hx, hy, hn]; ring
    exact_mod_cast this
  refine ⟨x, y, ?_, ?_⟩
  · rcases Int.even_or_odd' x with ⟨k, rfl | rfl⟩ <;>
      rcases Int.even_or_odd' y with ⟨l, rfl | rfl⟩
    · exact ⟨k - l, by ring⟩
    · exfalso
      have h4 : (4 : ℤ) ∣ d := ⟨n - k ^ 2 - d * (l ^ 2 + l), by linear_combination key⟩
      have h5 : 2 * 2 ∣ d := by exact_mod_cast h4
      simpa using hd 2 h5
    · exfalso
      have h4 : 4 * (n - k ^ 2 - k - d * l ^ 2) = 1 := by linear_combination -key
      omega
    · exact ⟨k - l, by ring⟩
  · have hx' : (x : E) = 2 * (a : E) := by exact_mod_cast congrArg (fun t : ℚ => (t : E)) hx
    have hy' : (y : E) = 2 * (b : E) := by exact_mod_cast congrArg (fun t : ℚ => (t : E)) hy
    rw [hx', hy']; ring
end

@[reducible] noncomputable def UpperTheory.Reformulated.B.IntegralClosureCriterionSecond.be :
    Formalism.BasicNotions.D7 → ℂ :=
    fun (D : Formalism.BasicNotions.D7) ↦ Complex.I * (↑√(↑D.host.d : ℝ) : ℂ)

noncomputable def UpperTheory.Reformulated.B.IntegralClosureCriterionSecond.OKc :
    Formalism.BasicNotions.D7 → ℂ → Prop :=
    fun (D : Formalism.BasicNotions.D7) (z : ℂ) ↦
      ∃ (x : ℤ) (y : ℤ), Even (x - y) ∧ z = ((↑x : ℂ) + (↑y : ℂ) * UpperTheory.Reformulated.B.IntegralClosureCriterionSecond.be D) / (2 : ℂ)

theorem UpperTheory.Reformulated.B.IntegralClosureCriterionSecond.okc_of :
    ∀ (D : Formalism.BasicNotions.D7) (u : NumberField.RingOfIntegers ↥D.host.K),
      UpperTheory.Reformulated.B.IntegralClosureCriterionSecond.OKc D ((D.host.φ₀ : D.host.E → ℂ) (↑(↑u : ↥D.host.K) : D.host.E)) := by
  intro D u
  have hd : Nat.Prime D.host.d := D.host.hyp.2.1
  have hint : IsIntegral ℤ ((u : D.host.K) : D.host.E) :=
    (NumberField.RingOfIntegers.isIntegral_coe u).map (D.host.K.val.toRingHom.toIntAlgHom)
  obtain ⟨x, y, hxy, hz⟩ := UpperTheory.integral_imag_quadratic_half_int D.host.E D.host.d D.host.sqd hd.squarefree
    D.host.sqd_sq _ (u : D.host.K).2 hint
  have hs : D.host.φ₀ D.host.sqd = UpperTheory.Reformulated.B.IntegralClosureCriterionSecond.be D := D.host.φ₀_mem
  refine ⟨x, y, hxy, ?_⟩
  rw [hz, map_div₀, map_add (f := _), map_mul, map_intCast, map_intCast, hs, map_ofNat]
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SeriesSubgroup
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FormalGroupCoeffMem
private theorem coeff_mul_mem_of_lt {R : Type} [CommRing R] (S : Subring R) (n : ℕ)
    (f g : PowerSeries R) (hf : ∀ k < n, PowerSeries.coeff k f ∈ S)
    (hg : ∀ k < n, PowerSeries.coeff k g ∈ S) :
    ∀ k < n, PowerSeries.coeff k (f * g) ∈ S := by
  intro k hk
  rw [PowerSeries.coeff_mul]
  refine S.sum_mem fun p hp => ?_
  have hp' : p.1 + p.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  exact S.mul_mem (hf _ (by omega)) (hg _ (by omega))

private theorem coeff_mul_mem_step {R : Type} [CommRing R] (S : Subring R) (n : ℕ)
    (f g : PowerSeries R) (hf0 : PowerSeries.constantCoeff f = 0)
    (hg0 : PowerSeries.constantCoeff g = 0)
    (hf : ∀ k < n, PowerSeries.coeff k f ∈ S)
    (hg : ∀ k < n, PowerSeries.coeff k g ∈ S) :
    PowerSeries.coeff n (f * g) ∈ S := by
  rw [PowerSeries.coeff_mul]
  refine S.sum_mem fun p hp => ?_
  have hp' : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  by_cases h1 : p.1 = 0
  · rw [h1, PowerSeries.coeff_zero_eq_constantCoeff_apply, hf0, zero_mul]
    exact S.zero_mem
  by_cases h2 : p.2 = 0
  · rw [h2, PowerSeries.coeff_zero_eq_constantCoeff_apply, hg0, mul_zero]
    exact S.zero_mem
  exact S.mul_mem (hf _ (by omega)) (hg _ (by omega))

theorem UpperTheory.formal_group_coeff_mem :
    ∀ (R : Type) [CommRing R] (S : Subring R) (a₁ a₂ a₃ a₄ a₆ : R) (w : PowerSeries R), a₁ ∈ S → a₂ ∈ S → a₃ ∈ S → a₄ ∈ S → a₆ ∈ S → PowerSeries.constantCoeff w = 0 → w = PowerSeries.X ^ 3 + PowerSeries.C a₁ * PowerSeries.X * w + PowerSeries.C a₂ * PowerSeries.X ^ 2 * w + PowerSeries.C a₃ * w ^ 2 + PowerSeries.C a₄ * PowerSeries.X * w ^ 2 + PowerSeries.C a₆ * w ^ 3 → ∀ n, PowerSeries.coeff n w ∈ S := by
  intro R _ S a₁ a₂ a₃ a₄ a₆ w h₁ h₂ h₃ h₄ h₆ h0 hw n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hX : ∀ k < n, PowerSeries.coeff k (PowerSeries.X : PowerSeries R) ∈ S := by
      intro k _
      rw [PowerSeries.coeff_X]
      split_ifs
      · exact S.one_mem
      · exact S.zero_mem
    have hX0 : PowerSeries.constantCoeff (PowerSeries.X : PowerSeries R) = 0 :=
      PowerSeries.constantCoeff_X
    have hX3 : PowerSeries.coeff n ((PowerSeries.X : PowerSeries R) ^ 3) ∈ S := by
      rw [PowerSeries.coeff_X_pow]
      split_ifs
      · exact S.one_mem
      · exact S.zero_mem
    have hXw0 : PowerSeries.constantCoeff (PowerSeries.X * w) = 0 := by
      rw [map_mul, h0, mul_zero]
    have hww0 : PowerSeries.constantCoeff (w * w) = 0 := by
      rw [map_mul, h0, mul_zero]
    have hXw := coeff_mul_mem_of_lt S n _ _ hX ih
    have hww := coeff_mul_mem_of_lt S n _ _ ih ih
    have e : w = PowerSeries.X ^ 3 + PowerSeries.C a₁ * (PowerSeries.X * w)
        + PowerSeries.C a₂ * (PowerSeries.X * (PowerSeries.X * w))
        + PowerSeries.C a₃ * (w * w) + PowerSeries.C a₄ * (PowerSeries.X * (w * w))
        + PowerSeries.C a₆ * (w * (w * w)) := by
      refine hw.trans ?_
      ring
    have e' := congrArg (PowerSeries.coeff n) e
    rw [e']
    simp only [map_add (f := _), PowerSeries.coeff_C_mul]
    exact S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem hX3
      (S.mul_mem h₁ (coeff_mul_mem_step S n _ _ hX0 h0 hX ih)))
      (S.mul_mem h₂ (coeff_mul_mem_step S n _ _ hX0 hXw0 hX hXw)))
      (S.mul_mem h₃ (coeff_mul_mem_step S n _ _ h0 h0 ih ih)))
      (S.mul_mem h₄ (coeff_mul_mem_step S n _ _ hX0 hww0 hX hww)))
      (S.mul_mem h₆ (coeff_mul_mem_step S n _ _ h0 hww0 ih hww))
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.InvOfUnitCoeffMem
theorem UpperTheory.invOfUnit_coeff_mem :
    ∀ (R : Type) [CommRing R] (S : Subring R) (f : PowerSeries R), (∀ n, PowerSeries.coeff n f ∈ S) → PowerSeries.constantCoeff f = 1 → ∀ n, PowerSeries.coeff n (PowerSeries.invOfUnit f 1) ∈ S := by
  intro R _ S f hf _ n
  have h1 : ((1⁻¹ : Rˣ) : R) ∈ S := by
    rw [inv_one, Units.val_one]
    exact S.one_mem
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [PowerSeries.coeff_invOfUnit]
    split_ifs with hn
    · exact h1
    · refine S.mul_mem (S.neg_mem h1) (S.sum_mem fun x _ => ?_)
      split_ifs with hx
      · exact S.mul_mem (hf _) (ih _ hx)
      · exact S.zero_mem
end

open PowerSeries

namespace UpperTheory.Reformulated.B.SeriesSubgroup

private def ball (K : Type) [NormedField K] [IsUltrametricDist K] : Subring K where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    show ‖a * b‖ ≤ 1
    rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := fun {a b} ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := fun {a} ha => by
    show ‖-a‖ ≤ 1
    rwa [norm_neg]

private def ser {R : Type} [CommRing R] (S : Subring R) : Subring R⟦X⟧ where
  carrier := {f | ∀ n, coeff n f ∈ S}
  mul_mem' := fun {a b} ha hb n => by
    rw [coeff_mul]
    exact S.sum_mem fun p _ => S.mul_mem (ha _) (hb _)
  one_mem' := fun n => by
    rw [coeff_one]
    split_ifs
    exacts [S.one_mem, S.zero_mem]
  add_mem' := fun {a b} ha hb n => by
    rw [map_add (f := _)]
    exact S.add_mem (ha n) (hb n)
  zero_mem' := fun n => by
    rw [map_zero]
    exact S.zero_mem
  neg_mem' := fun {a} ha n => by
    rw [map_neg]
    exact S.neg_mem (ha n)

private lemma C_mem {R : Type} [CommRing R] (S : Subring R) {a : R} (ha : a ∈ S) :
    (C a : R⟦X⟧) ∈ ser S := fun n => by
  rw [coeff_C]
  split_ifs
  exacts [ha, S.zero_mem]

private lemma X_mem {R : Type} [CommRing R] (S : Subring R) : (X : R⟦X⟧) ∈ ser S := fun n => by
  rw [coeff_X]
  split_ifs
  exacts [S.one_mem, S.zero_mem]

private lemma inv_mem {R : Type} [CommRing R] (S : Subring R) {f : R⟦X⟧} (hf : f ∈ ser S)
    (h : constantCoeff f = 1) : invOfUnit f 1 ∈ ser S := UpperTheory.invOfUnit_coeff_mem R S f hf h

open Formalism.L2.Th1.A in
private lemma xS_const {R : Type} [CommRing R] (W : WeierstrassCurve R) :
    constantCoeff (xS W) = 1 := by
  simp [xS]

open Formalism.L2.Th1.A in
private lemma xS_mem {R : Type} [CommRing R] (S : Subring R) (W : WeierstrassCurve R)
    (h₁ : W.a₁ ∈ S) (h₂ : W.a₂ ∈ S) (h₃ : W.a₃ ∈ S) (h₄ : W.a₄ ∈ S) (h₆ : W.a₆ ∈ S) :
    xS W ∈ ser S := by
  have hw : Formalism.ELL.WFixed W (wSer W) := (Formalism.ELL.wSeriesUnique R W).choose_spec.1
  have hm := UpperTheory.formal_group_coeff_mem R S W.a₁ W.a₂ W.a₃ W.a₄ W.a₆ (wSer W) h₁ h₂ h₃ h₄ h₆ hw.1 hw.2
  refine inv_mem S (fun n => ?_) ?_
  · rw [wU, coeff_mk]
    exact hm _
  · rw [← coeff_zero_eq_constantCoeff_apply, wU, coeff_mk]
    exact (Formalism.ELL.wSeriesLead R W _ hw).2.2.2

open Formalism.L2.Th1.A in
private lemma xPlus_mem {R : Type} [CommRing R] (S : Subring R) (W : WeierstrassCurve R)
    (h₁ : W.a₁ ∈ S) (h₂ : W.a₂ ∈ S) (h₃ : W.a₃ ∈ S) (h₄ : W.a₄ ∈ S) (h₆ : W.a₆ ∈ S)
    {x y : R} (hx : x ∈ S) (hy : y ∈ S) : xPlus W x y ∈ ser S := by
  have hs := xS_mem S W h₁ h₂ h₃ h₄ h₆
  have hX := X_mem S
  have two : (2 : R) ∈ S := ofNat_mem S 2
  have three : (3 : R) ∈ S := ofNat_mem S 3
  have hd : invOfUnit (tDen W x) 1 ∈ ser S :=
    inv_mem S (sub_mem hs (mul_mem (C_mem S hx) (pow_mem hX 2))) (by simp [tDen, xS_const])
  have hn : nS W x y ∈ ser S :=
    add_mem (sub_mem
      (mul_mem (mul_mem (C_mem S (add_mem (add_mem (sub_mem h₄ (mul_mem h₁ hy))
        (mul_mem (mul_mem two h₂) hx)) (mul_mem three (pow_mem hx 2)))) hX) hs)
      (mul_mem (C_mem S (add_mem (add_mem (mul_mem two hy) (mul_mem h₁ hx)) h₃)) (neg_mem hs)))
      (mul_mem (C_mem S (sub_mem (sub_mem (add_mem (mul_mem two h₆) (mul_mem h₄ hx))
        (mul_mem h₃ hy)) (pow_mem hx 3))) (pow_mem hX 3))
  exact add_mem (C_mem S hx) (mul_mem (mul_mem hX hn) (pow_mem hd 2))

open Formalism.L2.Th1.A in
private lemma xPlus_coeff {R : Type} [CommRing R] (W : WeierstrassCurve R) (x y : R) :
    coeff 0 (xPlus W x y) = x ∧ coeff 1 (xPlus W x y) = 2 * y + W.a₁ * x + W.a₃ ∧
      (2 * y + W.a₁ * x + W.a₃ = 0 →
        coeff 2 (xPlus W x y) = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) := by
  refine ⟨by simp [xPlus], ?_, fun h => ?_⟩
  · rw [xPlus, mul_assoc, map_add (f := _), coeff_succ_X_mul, coeff_C, if_neg one_ne_zero, zero_add,
      coeff_zero_eq_constantCoeff_apply]
    simp [nS, yS, xS_const]
  · have e : xPlus W x y = C x + X ^ 2 *
        ((C (W.a₄ - W.a₁ * y + 2 * W.a₂ * x + 3 * x ^ 2) * xS W
          + C (2 * W.a₆ + W.a₄ * x - W.a₃ * y - x ^ 3) * X ^ 2) *
          invOfUnit (tDen W x) 1 ^ 2) := by
      rw [xPlus, nS, h, map_zero]
      ring
    rw [e, map_add (f := _), coeff_C, if_neg two_ne_zero, zero_add, coeff_X_pow_mul', if_pos le_rfl,
      Nat.sub_self, coeff_zero_eq_constantCoeff_apply]
    simp only [map_mul, map_add (constantCoeff (R := R)), map_pow, constantCoeff_C, constantCoeff_X,
      xS_const, constantCoeff_invOfUnit]
    simp
    ring

theorem XTShape_holds : Formalism.L2.Th1.E.XTShape := by
  intro K _ _ _ W hW P _ hx hy
  obtain ⟨h₁, h₂, h₃, h₄, h₆, -⟩ := hW
  exact ⟨xPlus_mem (ball K) W h₁ h₂ h₃ h₄ h₆ hx hy, xPlus_coeff W _ _⟩

end UpperTheory.Reformulated.B.SeriesSubgroup
end
