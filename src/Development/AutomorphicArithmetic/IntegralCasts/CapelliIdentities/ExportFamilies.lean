module

public import Formalism.LocalToGlobal.KernelLattices.ColumnData
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExportFamilies
theorem UpperTheory.Reformulated.B.ExportFamilies.K_repr :
    ∀ (D : Formalism.L2.Ker.Car),
    ∀ x ∈ D.host.K,
      ∃ (p : ℚ) (q : ℚ),
        x =
          (↑p : D.host.E) +
            (↑q : D.host.E) *
              D.host.sqd := by
  intro D x hx
  have hs := D.host.sqd_sq
  have hx' : x ∈ Algebra.adjoin ℚ {D.host.sqd} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) D.host.sqd)]
    exact hx
  refine Algebra.adjoin_induction (p := fun x _ => ∃ p q : ℚ, x = (p : D.host.E) + q * D.host.sqd)
    (fun y hy => ⟨0, 1, by simpa using hy⟩) (fun r => ⟨r, 0, by simp⟩) ?_ ?_ hx'
  · rintro _ _ _ _ ⟨a, b, rfl⟩ ⟨c, e, rfl⟩
    exact ⟨a + c, b + e, by push_cast; ring⟩
  · rintro _ _ _ _ ⟨a, b, rfl⟩ ⟨c, e, rfl⟩
    exact ⟨a * c - D.host.d * (b * e), a * e + b * c, by
      push_cast; linear_combination ((b : D.host.E) * e) * hs⟩
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.WeightThresholdDefs
private theorem UpperTheory.Reformulated.B.WeightThresholdDefs.core {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
    [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
    {L : Submodule (NumberField.RingOfIntegers K) V} (h : Submodule.span K (L : Set V) = ⊤) (x : V) :
    ∃ n : NumberField.RingOfIntegers K, n ≠ 0 ∧ (n : K) • x ∈ L := by
  have hx : x ∈ Submodule.span K (L : Set V) := h ▸ Submodule.mem_top
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span
    (nonZeroDivisors (NumberField.RingOfIntegers K)) K (L : Set V) x hx
  refine ⟨t, nonZeroDivisors.coe_ne_zero t, ?_⟩
  rw [Submodule.span_eq, Submonoid.smul_def] at ht
  have : ((t : NumberField.RingOfIntegers K) : K) • x = (t : NumberField.RingOfIntegers K) • x :=
    algebraMap_smul K (t : NumberField.RingOfIntegers K) x
  rw [this]
  exact ht

theorem UpperTheory.Reformulated.B.WeightThresholdDefs.exists_smul_mem :
    ∀ {D : Formalism.L2.Ker.Car} {N : ℕ}
    {L₁ : Submodule (NumberField.RingOfIntegers D.host.E) (Fin N → D.host.E)},
    Submodule.span D.host.E (↑L₁ : Set (Fin N → D.host.E)) = ⊤ →
      ∀ (x : Fin N → D.host.E),
        ∃ (n : NumberField.RingOfIntegers D.host.E),
          n ≠ (0 : NumberField.RingOfIntegers D.host.E) ∧
            (↑n : D.host.E) • x ∈
              L₁ := by
  intro D N L₁ h x
  exact UpperTheory.Reformulated.B.WeightThresholdDefs.core h x
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.StarSqrtNeg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private lemma conj_eq_neg_of_sq {z : ℂ} {n : ℕ} (hn : 0 < n) (h : z ^ 2 = -(n : ℂ)) :
    (starRingEnd ℂ) z = -z := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [pow_two] at hre him
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hz : z.re = 0 := by
    have h2 : z.re * z.im = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h1 | h1
    · exact h1
    · exfalso; rw [h1] at hre; nlinarith [mul_self_nonneg z.re]
  apply Complex.ext <;> simp [hz]

theorem UpperTheory.Reformulated.B.StarSqrtNeg.star_sqrt_neg :
    ∀ {D : Formalism.L2.Ker.Car} (x : D.host.E) (n : ℕ),
    (0 : ℕ) < n →
      x ^ (2 : ℕ) = -(↑n : D.host.E) →
        Star.star x =
          -x := by
  intro D x n hn h
  haveI : NumberField.IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨φ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  apply φ.injective
  have key : φ (Star.star x) = (starRingEnd ℂ) (φ x) :=
    NumberField.IsCMField.complexEmbedding_complexConj D.host.E φ x
  have hsq : (φ x) ^ 2 = -(n : ℂ) := by
    have := congrArg φ h
    simpa using this
  rw [key, map_neg]
  exact conj_eq_neg_of_sq hn hsq
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.VanishKfLow
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MultilinearVanishLattice
theorem UpperTheory.multilinear_vanish_lattice :
    ∀ {ι : Type} [Finite ι] [DecidableEq ι] {M : ι → Type} {N : Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
        [AddCommGroup N] [Module ℂ N] (T : MultilinearMap (RingHom.id ℂ) M N) (L G : ∀ i, Set (M i)),
        (∀ v : ∀ i, M i, (∀ i, v i ∈ L i) → T v = 0) →
        (∀ i, ∀ w ∈ G i, ∃ w0 ∈ L i, ∀ v : ∀ i, M i, T (Function.update v i w0) = 0 → T (Function.update v i w) = 0) →
        ∀ v : ∀ i, M i, (∀ i, v i ∈ Submodule.span ℂ (G i)) → T v = 0 := by
  intro ι _ _ M N _ _ _ _ T L G hL hG
  have key : ∀ s : Finset ι, ∀ v : ∀ i, M i, (∀ i ∈ s, v i ∈ Submodule.span ℂ (G i)) →
      (∀ i, i ∉ s → v i ∈ L i) → T v = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact fun v _ h => hL v fun i => h i (Finset.notMem_empty i)
    | insert a s ha ih =>
      intro v hs hn
      have hker : Submodule.span ℂ (G a) ≤ LinearMap.ker (T.toLinearMap v a) := by
        rw [Submodule.span_le]
        intro w hw
        obtain ⟨w0, hw0, h⟩ := hG a w hw
        have h0 : T (Function.update v a w0) = 0 := by
          apply ih
          · intro i hi
            have hia : i ≠ a := fun e => ha (e ▸ hi)
            rw [Function.update_of_ne hia]
            exact hs i (Finset.mem_insert_of_mem hi)
          · intro i hi
            by_cases hia : i = a
            · subst hia
              rw [Function.update_self]
              exact hw0
            · rw [Function.update_of_ne hia]
              exact hn i (by simp [hia, hi])
        exact h v h0
      have hv : T (Function.update v a (v a)) = 0 := hker (hs a (Finset.mem_insert_self a s))
      rwa [Function.update_eq_self] at hv
  intro v hv
  haveI := Fintype.ofFinite ι
  exact key Finset.univ v (fun i _ => hv i) (fun i hi => absurd (Finset.mem_univ i) hi)
end

noncomputable def UpperTheory.Reformulated.B.LowTypeThetaMapVanishing.KfLow :
    {D : Formalism.BasicNotions.D7} →
      {V : Formalism.BasicNotions.TH.HSp D} →
        {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar} → (M : Formalism.IndefR.Mult.DSModel V S) → (τ : D.what₂.Tau) → Submodule ℂ ↥(M.sm τ) :=
    fun {D : Formalism.BasicNotions.D7} {V : Formalism.BasicNotions.TH.HSp D} {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar} (M : Formalism.IndefR.Mult.DSModel V S)
        (τ : D.what₂.Tau) ↦
      Submodule.span ℂ
        {w : ↥(M.sm τ) |
          ∃ g ∈ Formalism.QuantumDeterminants.UH (Formalism.BasicNotions.TH.gramAt D V τ),
            ∃ (w0 : ↥(Formalism.IndefR.Links.lowT M τ)), (↑w : M.H τ) = (M.rep τ g : M.H τ → M.H τ) (↑(↑w0 : ↥(M.sm τ)) : M.H τ)}

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Classical in
private theorem UpperTheory.Reformulated.B.LowTypeThetaMapVanishing.equiv_of_mem
    {D : Formalism.BasicNotions.D7} {V : Formalism.BasicNotions.TH.HSp D} {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar}
    (θ : D.what₂.Tau → TensorProduct (↥D.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf ↥D.host.F) D.host.E →+* ℂ)
    (M : Formalism.IndefR.Mult.DSModel V S) (J : Set (Formalism.L2.Theta.GA D V)) (χ : Formalism.L2.Theta.GA D V → ℂ)
    {T : Formalism.IndefR.Mult.MMap M} (hT : T ∈ Formalism.IndefR.Mult.Mult θ M J χ) (τ : D.what₂.Tau)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.BasicNotions.TH.gramAt D V τ))
    (v : M.Vec) (w : M.sm τ) (hw : (w : M.H τ) = M.rep τ g (v τ)) :
    ∃ k : Formalism.L2.Theta.GA D V, ∀ x : Formalism.L2.Theta.GA D V, T (Function.update v τ w) x = T v (x * k) := by
  refine ⟨Formalism.L2.Theta.atTau θ V τ g, ?_⟩
  unfold Formalism.IndefR.Mult.Mult at hT
  induction hT using Submodule.span_induction with
  | mem U hU => intro x; exact congrFun (hU.equiv τ g hg v w hw) x
  | zero => intro x; rfl
  | add U U' _ _ h h' =>
    intro x
    show U (Function.update v τ w) x + U' (Function.update v τ w) x = U v _ + U' v _
    rw [h x, h' x]
  | smul a U _ h =>
    intro x
    show a • U (Function.update v τ w) x = a • U v _
    rw [h x]

theorem UpperTheory.Reformulated.B.LowTypeThetaMapVanishing.vanish_KfLow :
    ∀ {D : Formalism.BasicNotions.D7} {V : Formalism.BasicNotions.TH.HSp D} {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar}
      (θ : D.what₂.Tau → TensorProduct (↥D.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf ↥D.host.F) D.host.E →+* ℂ)
      (M : Formalism.IndefR.Mult.DSModel V S) (J : Set (Formalism.L2.Theta.GA D V)) (χ : Formalism.L2.Theta.GA D V → ℂ)
      {T : Formalism.IndefR.Mult.MMap M},
      T ∈ Formalism.IndefR.Mult.Mult θ M J χ →
        (∀ (v : (ρ : D.what₂.Tau) → ↥(Formalism.IndefR.Links.lowT M ρ)),
            ((T : ((i : D.what₂.Tau) → ↥(M.sm i)) → Formalism.L2.Theta.GA D V → ℂ) fun (ρ : D.what₂.Tau) ↦ (↑(v ρ) : ↥(M.sm ρ))) =
              (0 : Formalism.L2.Theta.GA D V → ℂ)) →
          ∀ (s : Finset D.what₂.Tau) (v : M.Vec),
            (∀ τ ∈ s, v τ ∈ UpperTheory.Reformulated.B.LowTypeThetaMapVanishing.KfLow M τ) →
              (∀ τ ∉ s,
                  ∃ g ∈ Formalism.QuantumDeterminants.UH (Formalism.BasicNotions.TH.gramAt D V τ),
                    ∃ (w0 : ↥(Formalism.IndefR.Links.lowT M τ)),
                      (↑(v τ) : M.H τ) = (M.rep τ g : M.H τ → M.H τ) (↑(↑w0 : ↥(M.sm τ)) : M.H τ)) →
                (T : ((i : D.what₂.Tau) → ↥(M.sm i)) → Formalism.L2.Theta.GA D V → ℂ) v = (0 : Formalism.L2.Theta.GA D V → ℂ) := by
  intro D V S θ M J χ T hT h0 s v hs hns
  classical
  refine UpperTheory.multilinear_vanish_lattice T (fun τ => (Formalism.IndefR.Links.lowT M τ : Set (M.sm τ)))
    (fun τ => {w : ↥(M.sm τ) |
          ∃ g ∈ Formalism.QuantumDeterminants.UH (Formalism.BasicNotions.TH.gramAt D V τ),
            ∃ (w0 : ↥(Formalism.IndefR.Links.lowT M τ)), (↑w : M.H τ) = (M.rep τ g : M.H τ → M.H τ) (↑(↑w0 : ↥(M.sm τ)) : M.H τ)})
    (fun u hu => h0 (fun ρ => ⟨u ρ, hu ρ⟩)) ?_ v ?_
  · rintro τ w ⟨g, hg, w0, hw⟩
    refine ⟨w0.1, w0.2, fun u hu => ?_⟩
    obtain ⟨k, hk⟩ := UpperTheory.Reformulated.B.LowTypeThetaMapVanishing.equiv_of_mem θ M J χ hT τ g hg (Function.update u τ w0.1) w
      (by rw [Function.update_self]; exact hw)
    funext x
    have h1 := hk x
    rw [Function.update_idem] at h1
    have h2 : T (Function.update u τ w) x = T (Function.update u τ w0.1) (x * k) := by convert h1
    rw [h2, hu]
    rfl
  · intro τ
    by_cases h : τ ∈ s
    · exact hs τ h
    · exact Submodule.subset_span (hns τ h)
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralClosureCriterion
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralQuadraticHalfInt
private lemma int_of_isIntegral_cast (q : ℚ) (h : IsIntegral ℤ (q : ℂ)) : ∃ n : ℤ, (n : ℚ) = q := by
  have h1 : IsIntegral ℤ (algebraMap ℚ ℂ q) := by simpa using h
  have h2 : IsIntegral ℤ q := (isIntegral_algebraMap_iff ).1 h1
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  exact ⟨n, by simpa using hn⟩

private lemma int_of_sq_mul (d : ℕ) (hd : d.Prime) (q : ℚ) (m : ℤ)
    (h : q ^ 2 * (d : ℚ) = m) : ∃ n : ℤ, (n : ℚ) = q := by
  have hq : q * (q.den : ℚ) = q.num := Rat.mul_den_eq_num q
  have h1 : q.num ^ 2 * (d : ℤ) = m * (q.den : ℤ) ^ 2 := by
    have : ((q.num : ℚ)) ^ 2 * (d : ℚ) = (m : ℚ) * (q.den : ℚ) ^ 2 := by
      rw [← hq, ← h]; ring
    exact_mod_cast this
  have hc : IsCoprime ((q.den : ℤ) ^ 2) (q.num ^ 2) := by
    apply IsCoprime.pow
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
    simpa [Int.gcd] using q.reduced
  have h2 : (q.den : ℤ) ^ 2 ∣ (d : ℤ) :=
    hc.dvd_of_dvd_mul_left ⟨m, by rw [h1]; ring⟩
  have h3 : q.den * q.den ∣ d := by
    have : q.den ^ 2 ∣ d := by exact_mod_cast h2
    rwa [sq] at this
  have h4 : q.den = 1 := Nat.isUnit_iff.1 (hd.prime.squarefree _ h3)
  refine ⟨q.num, ?_⟩
  rw [← hq, h4]; simp

private lemma even_sub_of_norm (d : ℕ) (hd : d.Prime) (x y n : ℤ)
    (h : x ^ 2 + y ^ 2 * (d : ℤ) = 4 * n) : Even (x - y) := by
  obtain ⟨s, hs | hs⟩ := Int.even_or_odd' x <;> obtain ⟨t, ht | ht⟩ := Int.even_or_odd' y
  · exact ⟨s - t, by omega⟩
  · exfalso
    have h1 : (d : ℤ) = 4 * (n - s ^ 2 - (t ^ 2 + t) * d) := by
      rw [hs, ht] at h; linear_combination h
    have h2 : 2 * 2 ∣ d := by
      have : ((4 : ℕ) : ℤ) ∣ (d : ℤ) := ⟨_, by exact_mod_cast h1⟩
      exact_mod_cast this
    have h3 := Nat.isUnit_iff.1 (hd.prime.squarefree _ h2)
    omega
  · exfalso
    have h1 : (1 : ℤ) = 4 * (n - s ^ 2 - s - t ^ 2 * d) := by
      rw [hs, ht] at h; linear_combination h
    omega
  · exact ⟨s - t, by omega⟩

theorem UpperTheory.integral_quadratic_half_int :
    ∀ (d : ℕ), d.Prime → ∀ (a b : ℚ), IsIntegral ℤ ((a : ℂ) + (b : ℂ) * (Complex.I * ((Real.sqrt (d : ℝ) : ℝ) : ℂ))) → ∃ x y : ℤ, Even (x - y) ∧ (a : ℂ) + (b : ℂ) * (Complex.I * ((Real.sqrt (d : ℝ) : ℝ) : ℂ)) = ((x : ℂ) + (y : ℂ) * (Complex.I * ((Real.sqrt (d : ℝ) : ℝ) : ℂ))) / 2 := by
  intro d hd a b h
  have hr : ((Real.sqrt (d : ℝ) : ℝ) : ℂ) ^ 2 = (d : ℂ) := by
    have : Real.sqrt (d : ℝ) ^ 2 = (d : ℝ) := Real.sq_sqrt (Nat.cast_nonneg d)
    exact_mod_cast this
  generalize Real.sqrt (d : ℝ) = r at h hr ⊢
  have h' : IsIntegral ℤ ((a : ℂ) - (b : ℂ) * (Complex.I * (r : ℂ))) := by
    have h0 := map_isIntegral_int (starRingEnd ℂ) h
    have e : (starRingEnd ℂ) ((a : ℂ) + (b : ℂ) * (Complex.I * (r : ℂ)))
        = (a : ℂ) - (b : ℂ) * (Complex.I * (r : ℂ)) := by
      simp only [map_add (f := _), map_mul, map_ratCast, Complex.conj_I, Complex.conj_ofReal]
      ring
    rwa [e] at h0
  obtain ⟨x, hx⟩ := int_of_isIntegral_cast (2 * a) (by
    have e : ((2 * a : ℚ) : ℂ) = ((a : ℂ) + (b : ℂ) * (Complex.I * (r : ℂ)))
        + ((a : ℂ) - (b : ℂ) * (Complex.I * (r : ℂ))) := by
      push_cast; ring
    rw [e]; exact h.add h')
  obtain ⟨n, hn⟩ := int_of_isIntegral_cast (a ^ 2 + b ^ 2 * d) (by
    have e : ((a ^ 2 + b ^ 2 * d : ℚ) : ℂ) = ((a : ℂ) + (b : ℂ) * (Complex.I * (r : ℂ)))
        * ((a : ℂ) - (b : ℂ) * (Complex.I * (r : ℂ))) := by
      push_cast
      linear_combination (b : ℂ) ^ 2 * (r : ℂ) ^ 2 * Complex.I_sq - (b : ℂ) ^ 2 * hr
    rw [e]; exact h.mul h')
  obtain ⟨y, hy⟩ := int_of_sq_mul d hd (2 * b) (4 * n - x ^ 2) (by
    push_cast
    rw [hn, hx]; ring)
  refine ⟨x, y, even_sub_of_norm d hd x y n ?_, ?_⟩
  · have : (x : ℚ) ^ 2 + (y : ℚ) ^ 2 * (d : ℚ) = 4 * n := by
      rw [hx, hy, hn]; ring
    exact_mod_cast this
  · have hx' : (x : ℂ) = 2 * (a : ℂ) := by exact_mod_cast congrArg (Rat.cast : ℚ → ℂ) hx
    have hy' : (y : ℂ) = 2 * (b : ℂ) := by exact_mod_cast congrArg (Rat.cast : ℚ → ℂ) hy
    rw [hx', hy']; ring
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AdjoinSqrtEqRatSpan
theorem UpperTheory.adjoin_sqrt_eq_rat_span :
    ∀ (E : Type) [Field E] [CharZero E] (d : ℕ) (s : E), s ^ 2 = -(d : E) → ∀ x : E, x ∈ IntermediateField.adjoin ℚ ({s} : Set E) → ∃ a b : ℚ, x = (a : E) + (b : E) * s := by
  intro E _ _ d s hs x hx
  have hint : IsIntegral ℚ s := by
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    rw [hs]
    have h : (-(d : E)) = algebraMap ℚ E (-(d : ℚ)) := by simp
    rw [h]
    exact isIntegral_algebraMap
  have hx' : x ∈ Algebra.adjoin ℚ ({s} : Set E) := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hx
  clear hx
  induction hx' using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff] at hy
    exact ⟨0, 1, by simp [hy]⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨c, e, rfl⟩ := hz
    exact ⟨a + c, b + e, by push_cast; ring⟩
  | mul y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨c, e, rfl⟩ := hz
    refine ⟨a * c - d * b * e, a * e + b * c, ?_⟩
    push_cast
    linear_combination (b : E) * (e : E) * hs
end

@[reducible] noncomputable def UpperTheory.Reformulated.B.IntegralClosureCriterion.be :
    Formalism.L2.Ker.Car → ℂ :=
    fun (D : Formalism.L2.Ker.Car) ↦ Complex.I * (↑√(↑D.host.d : ℝ) : ℂ)

noncomputable def UpperTheory.Reformulated.B.IntegralClosureCriterion.OKc :
    Formalism.L2.Ker.Car → ℂ → Prop :=
    fun (D : Formalism.L2.Ker.Car) (z : ℂ) ↦
      ∃ (x : ℤ) (y : ℤ), Even (x - y) ∧ z = ((↑x : ℂ) + (↑y : ℂ) * UpperTheory.Reformulated.B.IntegralClosureCriterion.be D) / (2 : ℂ)

theorem UpperTheory.Reformulated.B.IntegralClosureCriterion.okc_of :
    ∀ (D : Formalism.L2.Ker.Car) (u : NumberField.RingOfIntegers ↥D.host.K),
      UpperTheory.Reformulated.B.IntegralClosureCriterion.OKc D ((D.host.φ₀ : D.host.E → ℂ) (↑(↑u : ↥D.host.K) : D.host.E)) := by
  intro D u
  have hφ : D.host.φ₀ D.host.sqd = Complex.I * ((Real.sqrt (D.host.d : ℝ) : ℝ) : ℂ) := D.host.φ₀_mem
  obtain ⟨a, b, hab⟩ := UpperTheory.adjoin_sqrt_eq_rat_span D.host.E D.host.d D.host.sqd D.host.sqd_sq
    ((u : D.host.K) : D.host.E) (u : D.host.K).2
  have hval : D.host.φ₀ ((u : D.host.K) : D.host.E)
      = (a : ℂ) + (b : ℂ) * (Complex.I * ((Real.sqrt (D.host.d : ℝ) : ℝ) : ℂ)) := by
    rw [hab, map_add (f := _), map_mul, map_ratCast, map_ratCast, hφ]
  have hint : IsIntegral ℤ (D.host.φ₀ ((u : D.host.K) : D.host.E)) :=
    (u.isIntegral_coe).map
      (D.host.φ₀.comp (algebraMap D.host.K D.host.E)).toIntAlgHom
  rw [hval] at hint
  obtain ⟨x, y, hxy, h⟩ := UpperTheory.integral_quadratic_half_int D.host.d D.host.hyp.2.1 a b hint
  exact ⟨x, y, hxy, hval.trans h⟩
end
