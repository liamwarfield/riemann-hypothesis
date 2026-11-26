module

public import GroundTheory.GlobalFields.Adele.Compact
public import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.Master
public import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PSAOpenHolds

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsBisBis
noncomputable def UpperTheory.Reformulated.B.DYhc9.IsLat :
    {E : Type} → [inst : Field E] → {N : ℕ} → Submodule (NumberField.RingOfIntegers E) (Fin N → E) → Prop :=
    fun {E : Type} [Field E] {N : ℕ} (Λ : Submodule (NumberField.RingOfIntegers E) (Fin N → E)) ↦
      Λ.FG ∧ Submodule.span E (↑Λ : Set (Fin N → E)) = ⊤

private theorem UpperTheory.Reformulated.B.DYhc9.exists_denom {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ d : ℕ, d ≠ 0 ∧ IsIntegral ℤ ((d : E) * a) := by
  have halg : IsAlgebraic ℤ a := by
    have : Algebra.IsAlgebraic ℤ E :=
      (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ)).mpr inferInstance
    exact Algebra.IsAlgebraic.isAlgebraic a
  obtain ⟨r, hr, hint⟩ := halg.exists_integral_multiple
  have hint' : IsIntegral ℤ ((r : E) * a) := by simpa [zsmul_eq_mul] using hint
  refine ⟨r.natAbs, Int.natAbs_ne_zero.mpr hr, ?_⟩
  rcases Int.natAbs_eq r with h | h
  · have : ((r.natAbs : E)) = (r : E) := by
      conv_rhs => rw [h]
      simp
    rwa [this]
  · have : ((r.natAbs : E)) = -(r : E) := by
      conv_rhs => rw [h]
      simp
    rw [this, neg_mul]
    exact hint'.neg

theorem UpperTheory.Reformulated.B.DYhc9.main :
    ∀ {E : Type} [inst : Field E] [NumberField E] {N : ℕ} {Λ : Submodule (NumberField.RingOfIntegers E) (Fin N → E)},
      UpperTheory.Reformulated.B.DYhc9.IsLat Λ → ∀ (x : Fin N → E), ∃ (m : ℕ), m ≠ (0 : ℕ) ∧ (↑m : E) • x ∈ Λ := by
  intro E _ _ N Λ h x
  have hx : x ∈ Submodule.span E (Λ : Set (Fin N → E)) := by
    rw [h.2]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨m, hm, hmy⟩ := hy
    obtain ⟨n, hn, hnz⟩ := hz
    refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
    have key : ((m * n : ℕ) : E) • (y + z) = n • ((m : E) • y) + m • ((n : E) • z) := by
      ext i
      simp
      ring
    rw [key]
    exact Λ.add_mem (nsmul_mem hmy n) (nsmul_mem hnz m)
  | smul a y _ hy =>
    obtain ⟨m, hm, hmy⟩ := hy
    obtain ⟨d, hd, hint⟩ := UpperTheory.Reformulated.B.DYhc9.exists_denom a
    refine ⟨d * m, mul_ne_zero hd hm, ?_⟩
    obtain ⟨b, hb⟩ : ∃ b : NumberField.RingOfIntegers E,
        algebraMap (NumberField.RingOfIntegers E) E b = (d : E) * a :=
      ⟨_, IsIntegralClosure.algebraMap_mk' _ _ hint⟩
    have key : ((d * m : ℕ) : E) • (a • y) = b • ((m : E) • y) := by
      ext i
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Algebra.smul_def, hb]
      push_cast
      ring
    rw [key]
    exact Λ.smul_mem _ hmy
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MultilinearSubMem
open MeasureTheory NumberField Matrix Filter Topology
open scoped Pointwise ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Cmp.DetMod

theorem multilinear_sub_mem {O V W ι : Type*} [CommRing O] [AddCommGroup V] [Module O V]
    [AddCommGroup W] [Module O W] [Fintype ι] [DecidableEq ι]
    (f : (ι → V) →ₘₗ[O] W) (Λ : Submodule O V) (I : Submodule O W)
    (𝔞 : Ideal O) (hI : ∀ z : ι → V, (∀ i, z i ∈ Λ) → f z ∈ I)
    (x y : ι → V) (hx : ∀ i, x i ∈ Λ) (hxy : ∀ i, y i - x i ∈ 𝔞 • Λ) :
    f y - f x ∈ 𝔞 • I := by
  have hy : ∀ i, y i ∈ Λ := fun i => by
    have h1 : y i - x i ∈ Λ := Submodule.smul_le_right (hxy i)
    simpa using Λ.add_mem h1 (hx i)
  have hupd : ∀ (z : ι → V), (∀ i, z i ∈ Λ) → ∀ i, ∀ w ∈ 𝔞 • Λ,
      f (Function.update z i w) ∈ 𝔞 • I := by
    intro z hz i w hw
    refine Submodule.smul_induction_on hw ?_ ?_
    · intro r hr n hn
      rw [f.map_update_smul]
      refine Submodule.smul_mem_smul hr (hI _ fun j => ?_)
      by_cases h : j = i
      · subst h; simpa using hn
      · simpa [Function.update_of_ne h] using hz j
    · intro a b ha hb
      rw [f.map_update_add]
      exact Submodule.add_mem _ ha hb
  have key : ∀ s : Finset ι, f (s.piecewise y x) - f x ∈ 𝔞 • I := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s his ih =>
      have hz : ∀ j, s.piecewise y x j ∈ Λ := fun j => by
        by_cases h : j ∈ s
        · simpa [h] using hy j
        · simpa [h] using hx j
      have h1 := hupd _ hz i _ (hxy i)
      rw [f.map_update_sub] at h1
      have h2 : Function.update (s.piecewise y x) i (x i) = s.piecewise y x := by
        rw [Function.update_eq_self_iff]; simp [his]
      rw [h2] at h1
      rw [Finset.piecewise_insert]
      simpa using Submodule.add_mem _ h1 ih
  simpa using key Finset.univ

theorem mem_of_smul_le {O K : Type*} [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] (I : Submodule O K) (hI : IsFractional (nonZeroDivisors O) I)
    (hI0 : I ≠ ⊥) (𝔞 : Ideal O) (δ : K) (h : ∀ t ∈ I, δ * t ∈ 𝔞 • I) :
    ∃ a ∈ 𝔞, δ = algebraMap O K a := by
  let J : FractionalIdeal (nonZeroDivisors O) K := ⟨I, hI⟩
  have hJ : J ≠ 0 := by
    intro h0
    apply hI0
    have : (J : Submodule O K) = ((0 : FractionalIdeal (nonZeroDivisors O) K) : Submodule O K) := by
      rw [h0]
    rw [FractionalIdeal.coe_zero] at this
    exact this
  have hle : FractionalIdeal.spanSingleton (nonZeroDivisors O) δ * J
      ≤ (𝔞 : FractionalIdeal (nonZeroDivisors O) K) * J := by
    rw [FractionalIdeal.spanSingleton_mul_le_iff]
    intro t ht
    refine Submodule.smul_induction_on (p := fun w => w ∈ (𝔞 : FractionalIdeal (nonZeroDivisors O) K) * J) (h t ht) ?_ ?_
    · intro r hr n hn
      rw [Algebra.smul_def]
      exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hr) hn
    · intro a b ha hb
      exact Submodule.add_mem (((𝔞 : FractionalIdeal (nonZeroDivisors O) K) * J : FractionalIdeal _ _) : Submodule O K) ha hb
  have hle2 := mul_le_mul_left hle J⁻¹
  rw [mul_assoc, mul_assoc, mul_inv_cancel₀ hJ, mul_one, mul_one,
    FractionalIdeal.spanSingleton_le_iff_mem, FractionalIdeal.mem_coeIdeal] at hle2
  obtain ⟨a, ha, rfl⟩ := hle2
  exact ⟨a, ha, rfl⟩

theorem main : ∀ (O K : Type) [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K] [IsFractionRing O K] (N : ℕ) (Λ : Submodule O (Fin N → K)) (𝔞 : Ideal O) (γ : Matrix (Fin N) (Fin N) K), Λ.FG → Submodule.span K (Λ : Set (Fin N → K)) = ⊤ → (∀ x ∈ Λ, γ *ᵥ x - x ∈ 𝔞 • Λ) → ∃ a ∈ 𝔞, γ.det = 1 + algebraMap O K a := by
  intro O K _ _ _ _ _ N Λ 𝔞 γ hfg hsp hγ
  let f : (Fin N → Fin N → K) →ₘₗ[O] K :=
    (Matrix.detRowAlternating (n := Fin N) (R := K)).toMultilinearMap.restrictScalars O
  have hf : ∀ z, f z = (Matrix.of z).det := fun z => rfl
  let I : Submodule O K := Submodule.span O {t | ∃ z : Fin N → Fin N → K, (∀ i, z i ∈ Λ) ∧ f z = t}
  have hI : ∀ z : Fin N → Fin N → K, (∀ i, z i ∈ Λ) → f z ∈ I :=
    fun z hz => Submodule.subset_span ⟨z, hz, rfl⟩

  obtain ⟨d, hd⟩ : ∃ d : nonZeroDivisors O, ∀ x ∈ Λ, ∀ j,
      IsLocalization.IsInteger O ((d : O) • x j) := by
    obtain ⟨S, rfl⟩ := hfg
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O)
      (fun p : S × Fin N => (p.1 : Fin N → K) p.2)
    refine ⟨d, fun x hx j => ?_⟩
    induction hx using Submodule.span_induction with
    | mem x hx => exact hd (⟨x, hx⟩, j)
    | zero => simpa using IsLocalization.isInteger_zero
    | add x y _ _ hx hy =>
      rw [Pi.add_apply, smul_add]; exact IsLocalization.isInteger_add hx hy
    | smul a x _ hx =>
      rw [Pi.smul_apply, smul_comm]; exact IsLocalization.isInteger_smul hx
  have hfrac : IsFractional (nonZeroDivisors O) I := by
    rw [FractionalIdeal.isFractional_span_iff]
    refine ⟨(d : O) ^ N, pow_mem d.2 N, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    choose m hm using fun i j => hd _ (hz i) j
    refine ⟨(Matrix.of m).det, ?_⟩
    rw [RingHom.map_det, hf, Algebra.smul_def, map_pow]
    have : (algebraMap O K).mapMatrix (Matrix.of m) = algebraMap O K d • Matrix.of z := by
      ext i j
      simp [hm, Algebra.smul_def]
    rw [this, Matrix.det_smul]
    simp
  have hI0 : I ≠ ⊥ := by
    intro h0
    obtain ⟨s, hs, hsp', hli⟩ := exists_linearIndependent K (Λ : Set (Fin N → K))
    rw [hsp] at hsp'
    let b : Module.Basis s K (Fin N → K) := Module.Basis.mk hli (by simp [hsp'])
    let e : s ≃ Fin N := b.indexEquiv (Pi.basisFun K (Fin N))
    let b' := b.reindex e
    have hb' : ∀ i, b' i ∈ Λ := fun i => by
      simp only [b', b, Module.Basis.reindex_apply, Module.Basis.mk_apply]
      exact hs (e.symm i).2
    have h1 := hI b' hb'
    rw [h0, Submodule.mem_bot, hf] at h1
    have h2 : IsUnit (Matrix.of (b' : Fin N → Fin N → K)) :=
      Matrix.linearIndependent_rows_iff_isUnit.mp b'.linearIndependent
    rw [Matrix.isUnit_iff_isUnit_det, h1] at h2
    exact not_isUnit_zero h2
  obtain ⟨a, ha, hδ⟩ := mem_of_smul_le I hfrac hI0 𝔞 (γ.det - 1) (by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      have h1 := multilinear_sub_mem f Λ I 𝔞 hI z (fun i => γ *ᵥ z i) hz (fun i => hγ _ (hz i))
      have h2 : Matrix.of (fun i => γ *ᵥ z i) = Matrix.of z * γᵀ := by
        ext i j
        simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
      rw [hf, h2, Matrix.det_mul, Matrix.det_transpose, ← hf] at h1
      convert h1 using 1
      ring
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx)
  exact ⟨a, ha, by rw [← hδ]; ring⟩

end GlobalTheory.CompanionTheory.Ar.Cmp.DetMod
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AdelicProofs.RelIndexNeZeroOfIsCompactOfRelOpen
open MeasureTheory NumberField Matrix Filter Topology
open scoped Pointwise ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem relIndex_ne_zero_of_isCompact_of_relOpen :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (S K K' : Subgroup G),
      K' ≤ S → IsCompact (K' : Set G) →
      (∃ O : Set G, IsOpen O ∧ O ∩ (S : Set G) = (K : Set G)) → K.relIndex K' ≠ 0 := by
  intro G _ _ _ S K K' hK'S hK' ⟨O, hO, hOS⟩
  have : CompactSpace K' := isCompact_iff_compactSpace.mp hK'
  have hopen : IsOpen ((K.subgroupOf K' : Subgroup K') : Set K') := by
    have hset : ((K.subgroupOf K' : Subgroup K') : Set K') = Subtype.val ⁻¹' O := by
      ext x
      simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_preimage]
      constructor
      · intro hx
        have : (x : G) ∈ O ∩ (S : Set G) := by rw [hOS]; exact hx
        exact this.1
      · intro hx
        have : (x : G) ∈ O ∩ (S : Set G) := ⟨hx, hK'S x.2⟩
        rw [hOS] at this
        exact this
    rw [hset]
    exact hO.preimage continuous_subtype_val
  have := (K.subgroupOf K').quotient_finite_of_isOpen hopen
  exact Subgroup.index_ne_zero_of_finite

end GlobalTheory.CompanionTheory.Ar.Cmp
end

section -- merged from Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.CongCompactOpen
noncomputable section

namespace PositivityTheory.EqVol

open Matrix NumberField IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Cmp
open scoped TensorProduct

open ReciprocityTheory.ChartRestriction.G.SA

theorem eich_mul {R : Type} [CommRing R] {N : ℕ} {σ : R →+* R} {J : Matrix (Fin N) (Fin N) R}
    (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) {e u u' : Fin N → R} (c c' : R) (he : hf σ J e e = 0)
    (hue : hf σ J u e = 0) (hue' : hf σ J u' e = 0) :
    eich σ J e u c * eich σ J e u' c' = eich σ J e (u + u') (c + c' - hf σ J u' u) := by
  have heu : hf σ J e u = 0 := by rw [← hf_symm hσ hJ, hue, map_zero]
  rw [ext_iff_mulVec]
  intro x
  rw [← mulVec_mulVec, eich_mulVec (σ := σ) (J := J) e u, eich_mulVec (σ := σ) (J := J) e u', eich_mulVec (σ := σ) (J := J) e (u + u')]
  simp only [hf_add_left, hf_sub_left, hf_smul_left, hf_add_right, he, hue', heu, mul_zero, add_zero, sub_zero]
  module

theorem eich_root {E : Type} [Field E] [CharZero E] {N : ℕ} {σ : E →+* E} {J : Matrix (Fin N) (Fin N) E}
    (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) {e f : Fin N → E} (he : hf σ J e e = 0)
    {M : Matrix (Fin N) (Fin N) E} (hM : M ∈ eichAlong σ J e f) (n : ℕ) (hn : 0 < n) :
    ∃ Y ∈ eichAlong σ J e f, Y ^ n = M := by
  obtain ⟨u, c, hue, huf, hc, rfl⟩ := hM
  have hn' : (n : E) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  set h := hf σ J u u with hh
  have hσh : σ h = h := by rw [hh, hf_symm hσ hJ]
  set t : E := (n : E)⁻¹ with ht
  have hσt : σ t = t := by rw [ht, map_inv₀, map_natCast]
  have hσ2 : σ 2 = 2 := map_ofNat σ 2
  have hpow : ∀ k : ℕ, eich σ J e (t • u) (t * (c + h / 2) - t ^ 2 * h / 2) ^ k =
      eich σ J e ((k * t) • u) (k * t * (c + h / 2) - (k * t) ^ 2 * h / 2) := by
    intro k
    induction k with
    | zero => simp [eich, Function.comp_def]; ext i j; simp [vecMulVec_apply, mulVec, dotProduct]
    | succ k ih =>
      rw [pow_succ, ih, eich_mul hσ hJ _ _ he (by rw [hf_smul_left, hue, mul_zero])
        (by rw [hf_smul_left, hue, mul_zero]), hf_smul_left, hf_smul_right, ← hh, map_mul, map_natCast, hσt, ← add_smul]
      congr 1
      · push_cast; ring_nf
      · push_cast; ring
  refine ⟨_, ⟨t • u, t * (c + h / 2) - t ^ 2 * h / 2, by rw [hf_smul_left, hue, mul_zero],
    by rw [hf_smul_left, huf, mul_zero], ?_, rfl⟩, ?_⟩
  · rw [hf_smul_left, hf_smul_right, ← hh]
    simp only [map_sub, map_mul, map_add (f := _), map_div₀, map_pow, hσt, hσh, hσ2]
    linear_combination t * hc
  · rw [hpow, ht, mul_inv_cancel₀ hn', one_smul]
    congr 1
    ring

theorem divisible : Divisible := by
  intro F E _ _ _ _ _ N c J ⟨h2, hc, hJ, hu, e, he0, he⟩ γ hγ
  have : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  have hcard : Nat.card (E ≃ₐ[F] E) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  have hall : ∀ g : E ≃ₐ[F] E, g = 1 ∨ g = c := fun g => by
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hcard
    by_cases h : g = 1
    · exact Or.inl h
    · exact Or.inr ((hy g h).trans (hy c hc).symm)
  have hcc : ∀ x, c (c x) = x := fun x => by
    rcases hall (c * c) with h | h
    · exact congrArg (fun g : E ≃ₐ[F] E => g x) h
    · exact absurd (mul_left_cancel (h.trans (mul_one c).symm)) hc
  have hfix : ∀ x, c x = x ↔ x ∈ Set.range (algebraMap F E) := fun x => by
    refine ⟨fun h => (IsGalois.mem_range_algebraMap_iff_fixed x).2 fun g => ?_, ?_⟩
    · rcases hall g with rfl | rfl
      · rfl
      · exact h
    · rintro ⟨y, rfl⟩
      exact c.commutes y
  obtain ⟨f, hff, hef⟩ := GroundTheory.Heights₂.Heights.StrongApprox.HypPairExists.proof E c.toRingHom hcc two_ne_zero N J hJ hu
    e he0 he
  have hgen := locGen F E c.toAlgHom hcc hfix h2 inferInstance two_ne_zero N J hJ hu e f he hff hef
  have hmem : (γ : Matrix (Fin N) (Fin N) E) ∈ Submonoid.closure (eichSet c.toRingHom J e f) :=
    hgen.le ⟨congrArg Units.val (show Matrix.GeneralLinearGroup.det γ = 1 from hγ.2), hγ.1⟩
  replace he : hf c.toRingHom J e e = 0 := he
  replace hcc : ∀ x, c.toRingHom (c.toRingHom x) = x := hcc
  replace hJ : Jᵀ = J.map c.toRingHom := hJ
  have key : ∀ M ∈ Submonoid.closure (eichSet c.toRingHom J e f), ∃ g : GL (Fin N) E, g.val = M ∧
      g ∈ Subgroup.closure {x : GL (Fin N) E | ∀ n : ℕ, 0 < n → ∃ y ∈ suGrp c.toRingHom J, y ^ n = x} := by
    intro M hM
    induction hM using Submonoid.closure_induction with
    | mem x hx =>
      have hx1 := eichSet_sub hcc hJ he hff hx
      refine ⟨Matrix.nonsingInvUnit x (by rw [hx1.1]; exact isUnit_one), rfl, Subgroup.subset_closure fun n hn => ?_⟩
      obtain ⟨Y, hY, hYn⟩ : ∃ Y ∈ SU c.toRingHom J, Y ^ n = x := by
        rcases hx with hx | hx
        · obtain ⟨Y, h1, h3⟩ := eich_root hcc hJ he hx n hn
          exact ⟨Y, eichAlong_sub hcc hJ he h1, h3⟩
        · obtain ⟨Y, h1, h3⟩ := eich_root hcc hJ hff hx n hn
          exact ⟨Y, eichAlong_sub hcc hJ hff h1, h3⟩
      exact ⟨Matrix.nonsingInvUnit Y (by rw [hY.1]; exact isUnit_one), ⟨hY.2, Units.ext hY.1⟩,
        Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hYn)⟩
    | one => exact ⟨1, rfl, one_mem _⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, rfl, ha⟩ := hx
      obtain ⟨b, rfl, hb⟩ := hy
      exact ⟨a * b, rfl, mul_mem ha hb⟩
  obtain ⟨g, hg, hg'⟩ := key _ hmem
  rwa [← Units.ext hg]

theorem congCompactOpen : CongCompactOpen := by
  intro R _ _ _ _ N Λ Λ' hc ho ho' ⟨u, hu⟩
  have tube : ∀ (φ : GL (Fin N) R → Matrix (Fin N) (Fin N) R) (T : Set (Fin N → R)), Continuous φ → IsOpen T →
      IsOpen {g | ∀ x ∈ Λ, φ g *ᵥ x ∈ T} := by
    intro φ T hφ hT
    rw [isOpen_iff_mem_nhds]
    intro g hg
    refine hc.eventually_forall_of_forall_eventually (P := fun g x => φ g *ᵥ x ∈ T) fun x hx => ?_
    have : Continuous fun p : GL (Fin N) R × (Fin N → R) => φ p.1 *ᵥ p.2 :=
      (hφ.comp continuous_fst).matrix_mulVec continuous_snd
    exact this.continuousAt.preimage_mem_nhds (hT.mem_nhds (hg x hx))
  have hinv : ∀ (g : GL (Fin N) R) x, ((g⁻¹ : GL (Fin N) R) : Matrix (Fin N) (Fin N) R) *ᵥ
      ((g : Matrix (Fin N) (Fin N) R) *ᵥ x) = x := fun g x => by
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec]
  have hopen : IsOpen (congGrp Λ Λ' : Set (GL (Fin N) R)) := by
    have := ((tube (fun g => g) Λ Units.continuous_val ho).inter
      (tube (fun g => ((g⁻¹ : GL (Fin N) R) : Matrix _ _ R)) Λ Units.continuous_coe_inv ho)).inter
      (tube (fun g => (g : Matrix _ _ R) - 1) Λ' (Units.continuous_val.sub continuous_const) ho')
    convert this using 1
    ext g
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_setOf_eq, sub_mulVec, one_mulVec]
    constructor
    · intro hg
      exact ⟨⟨fun x hx => (hg.1 x).1 hx, fun x hx => ((congGrp Λ Λ').inv_mem hg).1 x |>.1 hx⟩, hg.2⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨fun x => ⟨h1 x, fun hx => hinv g x ▸ h2 _ hx⟩, h3⟩
  refine ⟨?_, hopen⟩
  let C : Set (Matrix (Fin N) (Fin N) R) :=
    (fun y : Fin N → Fin N → R => Matrix.of fun i j => ((u⁻¹ : Rˣ) : R) * y j i) '' Set.univ.pi fun _ => (Λ : Set _)
  have hC : IsCompact C := (isCompact_univ_pi fun _ => hc).image
    (continuous_matrix fun i j => by simp only [Matrix.of_apply]; fun_prop)
  have hmem : ∀ g ∈ congGrp Λ Λ', (g : Matrix (Fin N) (Fin N) R) ∈ C := fun g hg =>
    ⟨fun j => (g : Matrix (Fin N) (Fin N) R) *ᵥ Pi.single j (u : R), fun j _ => (hg.1 _).1 (hu j), by
      ext i j
      simp only [Matrix.of_apply, mulVec, dotProduct_single]
      rw [mul_comm, Units.mul_inv_cancel_right]⟩
  have hK : IsCompact ((Units.embedProduct (Matrix (Fin N) (Fin N) R)) ⁻¹' (C ×ˢ (MulOpposite.op '' C))) :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage (hC.prod (hC.image MulOpposite.continuous_op))
  exact hK.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hopen) fun g hg =>
    ⟨hmem g hg, _, hmem _ ((congGrp Λ Λ').inv_mem hg), rfl⟩

end PositivityTheory.EqVol
end
end

section -- merged from Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.InclAdInjective
noncomputable section

namespace PositivityTheory.EqVol

open Matrix NumberField IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Cmp
open scoped TensorProduct

theorem topRing : TopRing := by
  intro F E _ _ _ _ _
  have hm : IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (Adf F E) := ⟨rfl⟩
  have := GroundTheory.Global.t2Space_finiteAdeleRing F
  refine ⟨IsModuleTopology.isTopologicalRing (FiniteAdeleRing (𝓞 F) F) (Adf F E), ?_, fun c => ?_⟩
  · let b := Algebra.TensorProduct.basis (FiniteAdeleRing (𝓞 F) F) (Module.finBasis F E)
    exact T2Space.of_injective_continuous b.equivFun.injective
      (IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap)
  · have := IsModuleTopology.isTopologicalRing (FiniteAdeleRing (𝓞 F) F) (Adf F E)
    exact IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.map (AlgHom.id (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F))
        c.toAlgHom).toLinearMap

theorem coInf : CoInf := by
  intro F E _ _ _ _ _ N c J K K' hK hK'
  have := (topRing F E).1
  obtain ⟨h1, h2, O, hO, e⟩ := hK
  obtain ⟨h1', h2', O', hO', e'⟩ := hK'
  refine ⟨⟨inf_le_left.trans h1, ?_, O ∩ O', hO.inter hO', ?_⟩, GlobalTheory.CompanionTheory.Ar.Cmp.relIndex_ne_zero_of_isCompact_of_relOpen _ _ K K' h1' h2' ⟨O, hO, e⟩⟩
  · have : CompactSpace K' := isCompact_iff_compactSpace.1 h2'
    have ho : IsOpen ((K.subgroupOf K' : Subgroup K') : Set K') := by
      have : ((K.subgroupOf K' : Subgroup K') : Set K') = Subtype.val ⁻¹' O := by
        ext x
        have hx : x.1 ∈ SUA c J := h1' x.2
        simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_preimage]
        exact ⟨fun h => (e.ge h).1, fun h => e.le ⟨h, hx⟩⟩
      rw [this]
      exact hO.preimage continuous_subtype_val
    have hc := ((Subgroup.isClosed_of_isOpen _ ho).isCompact).image continuous_subtype_val
    convert hc using 1
    ext x
    simp only [Subgroup.coe_inf, Set.mem_inter_iff, SetLike.mem_coe, Set.mem_image, Subgroup.mem_subgroupOf]
    exact ⟨fun h => ⟨⟨x, h.2⟩, h.1, rfl⟩, fun ⟨y, hy, e⟩ => e ▸ ⟨hy, y.2⟩⟩
  · rw [Subgroup.coe_inf, ← e, ← e']
    ext x
    simp only [Set.mem_inter_iff]
    tauto

theorem mem_conjBy {G : Type} [Group G] {g x : G} {K : Subgroup G} : x ∈ conjBy g K ↔ g⁻¹ * x * g ∈ K := by
  simp only [conjBy, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro h
    exact ⟨_, h, by simp [mul_assoc]⟩

theorem conj_mem_su {R : Type} [CommRing R] {N : ℕ} {σ : R →+* R} {J : Matrix (Fin N) (Fin N) R}
    {g x : GL (Fin N) R} (hg : g ∈ uGrp σ J) : g⁻¹ * x * g ∈ suGrp σ J ↔ x ∈ suGrp σ J := by
  simp only [suGrp, Subgroup.mem_inf, MonoidHom.mem_ker, map_mul, map_inv]
  rw [Subgroup.mul_mem_cancel_right _ hg, Subgroup.mul_mem_cancel_left _ (Subgroup.inv_mem _ hg),
    mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]

theorem coConj : CoConj := by
  intro F E _ _ _ _ _ N c J K hK g hg
  have := (topRing F E).1
  obtain ⟨h1, h2, O, hO, e⟩ := hK
  refine ⟨fun x hx => (conj_mem_su hg).1 (h1 (mem_conjBy.1 hx)), ?_, (fun x => g⁻¹ * x * g) ⁻¹' O,
    hO.preimage (by fun_prop), ?_⟩
  · rw [Subgroup.coe_map]
    exact h2.image (f := fun x => g * x * g⁻¹) (by fun_prop)
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe, mem_conjBy]
    exact ⟨fun h => e.le ⟨h.1, (conj_mem_su hg).2 h.2⟩, fun h => ⟨(e.ge h).1, (conj_mem_su hg).1 (e.ge h).2⟩⟩

theorem det_mul_conj {R : Type} [CommRing R] {N : ℕ} {σ : R →+* R} {J : Matrix (Fin N) (Fin N) R}
    (hJ : IsUnit J.det) {g : GL (Fin N) R} (hg : g ∈ uGrp σ J) :
    (g : Matrix (Fin N) (Fin N) R).det * σ (g : Matrix (Fin N) (Fin N) R).det = 1 := by
  have h : (g : Matrix (Fin N) (Fin N) R)ᵀ * J * (g : Matrix (Fin N) (Fin N) R).map σ = J := hg
  have h2 := congrArg Matrix.det h
  rw [det_mul, det_mul, det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h2
  apply hJ.mul_left_cancel
  linear_combination h2

theorem powerScalar : PowerScalar := by
  intro R _ N σ J hJ g hg
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · refine ⟨1, one_pos, 1, one_mem _, one_mem _, g, ⟨hg, ?_⟩, by simp⟩
    exact Units.ext (by simp [Matrix.det_isEmpty])
  · set d : Rˣ := Matrix.GeneralLinearGroup.det g with hd
    let z : GL (Fin N) R := Units.map (Matrix.scalar (Fin N)).toMonoidHom d
    have hz : (z : Matrix (Fin N) (Fin N) R) = (d : R) • (1 : Matrix (Fin N) (Fin N) R) := by
      show Matrix.scalar (Fin N) (d : R) = _
      rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    have hdd : (d : R) * σ d = 1 := det_mul_conj hJ hg
    have hzu : z ∈ uGrp σ J := by
      show (z : Matrix (Fin N) (Fin N) R)ᵀ * J * (z : Matrix (Fin N) (Fin N) R).map σ = J
      have : ((d : R) • (1 : Matrix (Fin N) (Fin N) R)).map σ = σ d • (1 : Matrix (Fin N) (Fin N) R) := by
        ext i j
        by_cases h : i = j <;> simp [h, Matrix.one_apply]
      rw [hz, this]
      simp only [transpose_smul, transpose_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
        smul_smul]
      rw [mul_comm, hdd, one_smul]
    have hdz : Matrix.GeneralLinearGroup.det z = d ^ N := Units.ext (by
      show (z : Matrix (Fin N) (Fin N) R).det = _
      rw [hz]; simp)
    refine ⟨N, hN, z, hzu, Subgroup.mem_center_iff.2 fun x => Units.ext ?_, z⁻¹ * g ^ N,
      ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hzu) (Subgroup.pow_mem _ hg _), ?_⟩, by simp⟩
    · simp [hz]
    · show Matrix.GeneralLinearGroup.det (z⁻¹ * g ^ N) = 1
      rw [map_mul, map_inv, map_pow, hdz, ← hd, inv_mul_cancel]

section diag

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}

theorem inclAd_injective : Function.Injective (inclAd F E) :=
  Algebra.TensorProduct.includeRight_injective (A := FiniteAdeleRing (𝓞 F) F) (B := E)
    fun a b h => by
      obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 F)
      let v : HeightOneSpectrum (𝓞 F) := ⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField F)⟩
      exact (algebraMap F (v.adicCompletion F)).injective (congrArg (fun x => x v) h)

theorem diagGL_val (γ : GL (Fin N) E) :
    (diagGL F γ : Matrix (Fin N) (Fin N) (Adf F E)) = (γ : Matrix (Fin N) (Fin N) E).map (inclAd F E) := rfl

theorem diagGL_mem_u (c : E ≃ₐ[F] E) (J : Matrix (Fin N) (Fin N) E) (γ : GL (Fin N) E) :
    diagGL F γ ∈ UA c J ↔ γ ∈ uGrp c.toRingHom J := by
  show (diagGL F γ : Matrix (Fin N) (Fin N) (Adf F E))ᵀ * _ * _ = _ ↔ _ * _ * _ = _
  have e : ((γ : Matrix (Fin N) (Fin N) E).map (inclAd F E)).map (sigAd c) =
      ((γ : Matrix (Fin N) (Fin N) E).map c.toRingHom).map (inclAd F E) := rfl
  rw [diagGL_val, e, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul]
  exact (Matrix.map_injective inclAd_injective).eq_iff

theorem diagGL_mem_su (c : E ≃ₐ[F] E) (J : Matrix (Fin N) (Fin N) E) (γ : GL (Fin N) E) :
    diagGL F γ ∈ SUA c J ↔ γ ∈ suGrp c.toRingHom J := by
  refine and_congr (diagGL_mem_u c J γ) ?_
  show Matrix.GeneralLinearGroup.det (diagGL F γ) = 1 ↔ Matrix.GeneralLinearGroup.det γ = 1
  simp only [Units.ext_iff, Matrix.GeneralLinearGroup.val_det_apply, diagGL_val, Units.val_one]
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, ← map_one (inclAd F E)]
  exact inclAd_injective.eq_iff

end diag

theorem coSA (h : ReciprocityTheory.ChartRestriction.G.SA.SAOpenStatement) : CoSA := by
  intro F E _ _ _ _ _ N c J K ⟨h2, hc, hJ, hu, he⟩ ⟨hK, _, O, hO, eO⟩ s hs
  have := (topRing F E).1
  have hm : IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (Adf F E) := ⟨rfl⟩
  have hdet : ∀ g ∈ SUA c J, (g : Matrix (Fin N) (Fin N) (Adf F E)).det = 1 := fun g hg =>
    congrArg Units.val (show Matrix.GeneralLinearGroup.det g = 1 from hg.2)
  have hSU : ∀ g ∈ SUA c J, (g : Matrix (Fin N) (Fin N) (Adf F E)) ∈
      ReciprocityTheory.ChartRestriction.G.SA.SU (ReciprocityTheory.ChartRestriction.G.SA.sigA c) (J.map (ReciprocityTheory.ChartRestriction.G.SA.inclA F E)) :=
    fun g hg => ⟨hdet g hg, hg.1⟩
  have hinv : ∀ g ∈ SUA c J, ((g⁻¹ : GL (Fin N) (Adf F E)) : Matrix (Fin N) (Fin N) (Adf F E)) =
      (g : Matrix (Fin N) (Fin N) (Adf F E)).adjugate := fun g hg => by
    rw [Matrix.coe_units_inv, Matrix.inv_def, hdet g hg]; simp
  obtain ⟨W, hW, rfl⟩ := Units.isInducing_embedProduct.isOpen_iff.1 hO
  obtain ⟨γ, hγ, _, ⟨k, hk, rfl⟩, e⟩ := h F E c h2 hc N J hJ hu he (Units.val '' (K : Set (GL (Fin N) (Adf F E))))
    (by rintro _ ⟨k, hk, rfl⟩; exact hSU k (hK hk)) ⟨1, K.one_mem, rfl⟩
    (by rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩; exact ⟨a * b, K.mul_mem ha hb, rfl⟩)
    (by rintro _ ⟨a, ha, rfl⟩; exact ⟨a⁻¹, K.inv_mem ha, Matrix.coe_units_inv a⟩)
    ⟨(fun M => (M, MulOpposite.op M.adjugate)) ⁻¹' W,
      hW.preimage (continuous_id.prodMk (MulOpposite.continuous_op.comp continuous_id.matrix_adjugate)), by
        ext M
        constructor
        · rintro ⟨h1, h3⟩
          let g : GL (Fin N) (Adf F E) := Matrix.nonsingInvUnit M (by rw [h3.1]; exact isUnit_one)
          have hg : g ∈ SUA c J := ⟨h3.2, Units.ext h3.1⟩
          refine ⟨g, eO.le ⟨?_, hg⟩, rfl⟩
          show ((g : Matrix (Fin N) (Fin N) (Adf F E)), MulOpposite.op ((g⁻¹ : GL (Fin N) (Adf F E)) : Matrix _ _ _)) ∈ W
          rw [hinv g hg]
          exact h1
        · rintro ⟨g, hg, rfl⟩
          refine ⟨?_, hSU g (hK hg)⟩
          have h1 : ((g : Matrix (Fin N) (Fin N) (Adf F E)),
            MulOpposite.op ((g⁻¹ : GL (Fin N) (Adf F E)) : Matrix _ _ _)) ∈ W := (eO.ge hg).1
          rwa [hinv g (hK hg)] at h1⟩ s (hSU s hs)
  exact ⟨Matrix.nonsingInvUnit γ (by rw [hγ.1]; exact isUnit_one), ⟨hγ.2, Units.ext hγ.1⟩, k, hk, Units.ext e⟩

theorem indexEq_of (h3 : CoSA) (h4 : Divisible) : IndexEq := by
  intro F E _ _ _ _ _ N c J K hS hK g hg
  let U := UA c J
  have hSU : SUA c J ≤ U := inf_le_left
  let Γ₀ := (suGrp c.toRingHom J).map (diagGL F)
  have hΓ₀ : Γ₀ ≤ SUA c J := by
    rintro _ ⟨γ, hγ, rfl⟩
    exact (diagGL_mem_su c J γ).2 hγ
  have hconj : ∀ (K : Subgroup (GL (Fin N) (Adf F E))) (g : U),
      (K.subgroupOf U).map (MulAut.conj g).toMonoidHom = (conjBy g.1 K).subgroupOf U := fun K g => by
    ext x
    exact (mem_conjBy (G := U)).trans (Subgroup.mem_subgroupOf.trans
      ((mem_conjBy (g := g.1) (x := x.1)).symm.trans Subgroup.mem_subgroupOf.symm))
  have hidx : ∀ A B : Subgroup (GL (Fin N) (Adf F E)), B ≤ SUA c J →
      (A.subgroupOf U ⊓ Γ₀.subgroupOf U).relIndex (B.subgroupOf U ⊓ Γ₀.subgroupOf U) = (rat A).relIndex (rat B) := by
    intro A B hB
    have e : (rat B).map (diagGL F) = B ⊓ Γ₀ := by
      ext x
      constructor
      · rintro ⟨γ, hγ, rfl⟩
        exact ⟨hγ, γ, (diagGL_mem_su c J γ).1 (hB hγ), rfl⟩
      · rintro ⟨hx, γ, -, rfl⟩
        exact ⟨γ, hx, rfl⟩
    have e1 : ∀ C : Subgroup (GL (Fin N) (Adf F E)), C.subgroupOf U ⊓ Γ₀.subgroupOf U = (C ⊓ Γ₀).subgroupOf U :=
      fun C => (Subgroup.comap_inf _ _ _).symm
    rw [e1, e1, Subgroup.relIndex_subgroupOf (inf_le_right.trans (hΓ₀.trans hSU)), rat, Subgroup.relIndex_comap, e,
      ← Subgroup.inf_relIndex_right A, ← Subgroup.inf_relIndex_right (A ⊓ Γ₀)]
    congr 1
    ext x
    simp only [Subgroup.mem_inf]
    tauto
  have hu : IsUnit (J.map (inclAd F E)).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hS.2.2.2.1.map _
  have key := master U ((SUA c J).subgroupOf U) (Γ₀.subgroupOf U) {L | ∃ K, IsCO c J K ∧ L = K.subgroupOf U}
    (by rintro _ ⟨K, hK, rfl⟩; exact Subgroup.comap_mono hK.1)
    (by
      rintro _ ⟨K, hK, rfl⟩ _ ⟨K', hK', rfl⟩
      exact ⟨K ⊓ K', (coInf F E N c J K K' hK hK').1, (Subgroup.comap_inf _ _ _).symm⟩)
    (by rintro _ ⟨K, hK, rfl⟩ g; exact ⟨_, coConj F E N c J K hK g.1 g.2, hconj K g⟩)
    (by
      rintro _ ⟨K, hK, rfl⟩ _ ⟨K', hK', rfl⟩
      rw [Subgroup.relIndex_subgroupOf (hK'.1.trans hSU)]
      exact (coInf F E N c J K K' hK hK').2)
    (by
      rintro _ ⟨K, hK, rfl⟩ s hs
      obtain ⟨γ, hγ, k, hk, e⟩ := h3 F E N c J K hS hK s.1 hs
      exact ⟨⟨diagGL F γ, hSU (hΓ₀ ⟨γ, hγ, rfl⟩)⟩, ⟨γ, hγ, rfl⟩, ⟨k, hSU (hK.1 hk)⟩, hk, Subtype.ext e⟩)
    (by
      rintro ⟨_, hx⟩ ⟨γ, hγ, rfl⟩
      have hcl := h4 F E N c J hS hγ
      clear hγ
      induction hcl using Subgroup.closure_induction with
      | mem x hx' =>
        refine Subgroup.subset_closure fun n hn => ?_
        obtain ⟨y, hy, e⟩ := hx' n hn
        exact ⟨⟨diagGL F y, hSU (hΓ₀ ⟨y, hy, rfl⟩)⟩, Subtype.ext (by simp [← e])⟩
      | one =>
        convert Subgroup.one_mem _
        simp
      | mul x y hx' hy' ihx ihy =>
        have mem : ∀ z ∈ Subgroup.closure {x : GL (Fin N) E | ∀ n : ℕ, 0 < n → ∃ y ∈ suGrp c.toRingHom J, y ^ n = x},
            diagGL F z ∈ U := fun z hz => hSU ((diagGL_mem_su c J z).2 ((Subgroup.closure_le _).2 (fun w hw => by
              obtain ⟨y, hy, e⟩ := hw 1 one_pos
              rw [← e, pow_one]; exact hy) hz))
        convert Subgroup.mul_mem _ (ihx (mem x hx')) (ihy (mem y hy')) using 1
        exact Subtype.ext (map_mul _ _ _)
      | inv x hx' ih =>
        have hx2 : diagGL F x ∈ U := by simpa using U.inv_mem hx
        convert Subgroup.inv_mem _ (ih hx2) using 1
        exact Subtype.ext (map_inv _ _))
    (by
      intro g
      obtain ⟨n, hn, z, hz, hzc, s, hs, e⟩ := powerScalar _ N _ _ hu g.1 g.2
      exact ⟨n, hn, ⟨z, hz⟩, Subgroup.mem_center_iff.2 fun x => Subtype.ext (Subgroup.mem_center_iff.1 hzc x.1),
        ⟨s, hs.1⟩, hs, Subtype.ext e⟩)
    _ ⟨K, hK, rfl⟩ ⟨g, hg⟩
  have hK' := coConj F E N c J K hK g hg
  rw [hconj, hidx _ _ hK'.1, hidx _ _ hK.1] at key
  exact key

end PositivityTheory.EqVol
end
end

noncomputable section

namespace PositivityTheory.EqVol

open Matrix NumberField IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Cmp
open scoped TensorProduct

section lat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}

theorem exists_smul_mem {Λ : Submodule (𝓞 E) (Fin N → E)} (h : IsLat Λ) (x : Fin N → E) :
    ∃ m : ℕ, m ≠ 0 ∧ (m : E) • x ∈ Λ :=
  _root_.UpperTheory.Reformulated.B.DYhc9.main h x

theorem isLat_smul {Λ : Submodule (𝓞 E) (Fin N → E)} (h : IsLat Λ) {𝔞 : Ideal (𝓞 E)} (h𝔞 : 𝔞 ≠ ⊥) :
    IsLat (𝔞 • Λ) := by
  refine ⟨Submodule.FG.smul (IsNoetherian.noetherian 𝔞) h.1, ?_⟩
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔞
  rw [eq_top_iff, ← h.2, Submodule.span_le]
  intro x hx
  have h1 : a • x ∈ Submodule.span E ((𝔞 • Λ : Submodule (𝓞 E) (Fin N → E)) : Set (Fin N → E)) :=
    Submodule.subset_span (Submodule.smul_mem_smul ha hx)
  have h2 := Submodule.smul_mem _ ((a : E)⁻¹) h1
  rwa [show a • x = (a : E) • x from rfl, smul_smul, inv_mul_cancel₀ (by exact_mod_cast ha0), one_smul] at h2

theorem tmul_mem_hat {Λ : AddSubgroup (Fin N → E)} {a : FiniteAdeleRing (𝓞 F) F}
    (ha : ∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F) {x : Fin N → E} (hx : x ∈ Λ) :
    (fun i => a ⊗ₜ[F] x i) ∈ hatLat F Λ := AddSubgroup.subset_closure ⟨a, ha, x, hx, rfl⟩

theorem incl_mem_hat {Λ : AddSubgroup (Fin N → E)} {x : Fin N → E} (hx : x ∈ Λ) :
    (fun i => inclAd F E (x i)) ∈ hatLat F Λ := tmul_mem_hat (fun _ => one_mem _) hx

theorem smul_hat_mem {Λ : Submodule (𝓞 E) (Fin N → E)} {𝔞 : Ideal (𝓞 E)} {a : 𝓞 E} (ha : a ∈ 𝔞)
    {y : Fin N → Adf F E} (hy : y ∈ hatLat F Λ.toAddSubgroup) :
    inclAd F E a • y ∈ hatLat F (𝔞 • Λ).toAddSubgroup := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, x, hx, rfl⟩ := hy
    convert tmul_mem_hat hb (show a • x ∈ (𝔞 • Λ).toAddSubgroup from Submodule.smul_mem_smul ha hx) using 1
    funext i
    show (1 ⊗ₜ[F] (a : E)) * (b ⊗ₜ[F] x i) = b ⊗ₜ[F] ((a : E) * x i)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem mulVec_hat_smul {Λ Λ' : Submodule (𝓞 E) (Fin N → E)} (𝔞 : Ideal (𝓞 E))
    {g : Matrix (Fin N) (Fin N) (Adf F E)}
    (hg : ∀ x ∈ hatLat F Λ.toAddSubgroup, g *ᵥ x ∈ hatLat F Λ'.toAddSubgroup) :
    ∀ x ∈ hatLat F (𝔞 • Λ).toAddSubgroup, g *ᵥ x ∈ hatLat F (𝔞 • Λ').toAddSubgroup := by
  intro y hy
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, x, hx, rfl⟩ := hy
    have hx' : x ∈ 𝔞 • Λ := hx
    refine Submodule.smul_induction_on
      (p := fun x : Fin N → E => g *ᵥ (fun i => (b ⊗ₜ[F] x i : Adf F E)) ∈ hatLat F (𝔞 • Λ').toAddSubgroup)
      hx' (fun a ha x hx => ?_) fun x y hx hy => ?_
    · have e : (fun i => b ⊗ₜ[F] (a • x) i) = inclAd F E a • fun i => b ⊗ₜ[F] x i := by
        funext i
        show b ⊗ₜ[F] ((a : E) * x i) = (1 ⊗ₜ[F] (a : E)) * (b ⊗ₜ[F] x i)
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [e, mulVec_smul]
      exact smul_hat_mem ha (hg _ (tmul_mem_hat hb hx))
    · have e : (fun i => b ⊗ₜ[F] (x + y) i) = (fun i => b ⊗ₜ[F] x i) + fun i => b ⊗ₜ[F] y i := by
        funext i
        exact TensorProduct.tmul_add _ _ _
      rw [e, mulVec_add]
      exact add_mem hx hy
  | zero => simp
  | add x y _ _ hx hy => rw [mulVec_add]; exact add_mem hx hy
  | neg x _ hx => rw [mulVec_neg]; exact neg_mem hx

theorem diag_mulVec_tmul (γ : Matrix (Fin N) (Fin N) E) (b : FiniteAdeleRing (𝓞 F) F) (x : Fin N → E) :
    γ.map (inclAd F E) *ᵥ (fun i => b ⊗ₜ[F] x i) = fun i => b ⊗ₜ[F] (γ *ᵥ x) i := by
  funext i
  simp only [mulVec, dotProduct, TensorProduct.tmul_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  show (1 ⊗ₜ[F] γ i j) * (b ⊗ₜ[F] x j) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem map_mulVec_hat {Λ Λ' : AddSubgroup (Fin N → E)} {γ : Matrix (Fin N) (Fin N) E} (h : ∀ x ∈ Λ, γ *ᵥ x ∈ Λ') :
    ∀ y ∈ hatLat F Λ, γ.map (inclAd F E) *ᵥ y ∈ hatLat F Λ' := by
  intro y hy
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, x, hx, rfl⟩ := hy
    rw [diag_mulVec_tmul]
    exact tmul_mem_hat hb (h x hx)
  | zero => simp
  | add x y _ _ hx hy => rw [mulVec_add]; exact add_mem hx hy
  | neg x _ hx => rw [mulVec_neg]; exact neg_mem hx

end lat

theorem conj_congGrp {R : Type} [CommRing R] {N : ℕ} {A A' B B' : AddSubgroup (Fin N → R)} (g : GL (Fin N) R)
    (h1 : ∀ x, x ∈ A ↔ (g : Matrix (Fin N) (Fin N) R) *ᵥ x ∈ B)
    (h2 : ∀ x, x ∈ A' ↔ (g : Matrix (Fin N) (Fin N) R) *ᵥ x ∈ B') (k : GL (Fin N) R) :
    g⁻¹ * k * g ∈ congGrp A A' ↔ k ∈ congGrp B B' := by
  have e : ∀ x, (g : Matrix (Fin N) (Fin N) R) *ᵥ (((g⁻¹ * k * g : GL (Fin N) R) : Matrix (Fin N) (Fin N) R) *ᵥ x) =
      (k : Matrix (Fin N) (Fin N) R) *ᵥ ((g : Matrix (Fin N) (Fin N) R) *ᵥ x) := fun x => by
    rw [mulVec_mulVec, mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, ← mul_assoc, ← mul_assoc, mul_inv_cancel,
      one_mul]
  have hs : ∀ y, ∃ x, (g : Matrix (Fin N) (Fin N) R) *ᵥ x = y := fun y =>
    ⟨((g⁻¹ : GL (Fin N) R) : Matrix (Fin N) (Fin N) R) *ᵥ y, by rw [mulVec_mulVec, Units.mul_inv, one_mulVec]⟩
  constructor
  · rintro ⟨a, b⟩
    refine ⟨fun y => ?_, fun y hy => ?_⟩ <;> obtain ⟨x, rfl⟩ := hs y
    · rw [← h1, a, h1, e]
    · have := (h2 _).1 (b x ((h1 x).2 hy))
      rwa [mulVec_sub, e] at this
  · rintro ⟨a, b⟩
    refine ⟨fun x => by rw [h1, a, h1, e], fun x hx => ?_⟩
    rw [h2, mulVec_sub, e]
    exact b _ ((h1 x).1 hx)

theorem levelConj : LevelConj := by
  intro F E _ _ _ _ _ N c J Λ Λ' 𝔞 g hg h
  have hinv : ∀ x, ((g⁻¹ : GL (Fin N) (Adf F E)) : Matrix (Fin N) (Fin N) (Adf F E)) *ᵥ
      ((g : Matrix (Fin N) (Fin N) (Adf F E)) *ᵥ x) = x := fun x => by rw [mulVec_mulVec, Units.inv_mul, one_mulVec]
  have h2 : ∀ x, x ∈ hatLat F (𝔞 • Λ).toAddSubgroup ↔
      (g : Matrix (Fin N) (Fin N) (Adf F E)) *ᵥ x ∈ hatLat F (𝔞 • Λ').toAddSubgroup := fun x =>
    ⟨mulVec_hat_smul 𝔞 (fun y => (h y).1) x, fun hx => hinv x ▸ mulVec_hat_smul 𝔞 (fun y hy => (h _).2 (by
      rwa [mulVec_mulVec, Units.mul_inv, one_mulVec])) _ hx⟩
  ext k
  rw [mem_conjBy]
  exact and_congr (conj_mem_su hg) (conj_congGrp g h h2 k)

theorem levelRat (hH : HatRat) : LevelRat := by
  intro F E _ _ _ _ _ N c J Λ 𝔞 hΛ h𝔞 hJ hN
  have hΛ' := isLat_smul hΛ h𝔞
  have e : ∀ (γ : Matrix (Fin N) (Fin N) E) (x : Fin N → E),
      γ.map (inclAd F E) *ᵥ (fun i => inclAd F E (x i)) = fun i => inclAd F E ((γ *ᵥ x) i) :=
    fun γ x => diag_mulVec_tmul γ 1 x
  ext γ
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨((diagGL_mem_su c J γ).1 h1).1, fun x => ?_, fun x hx => ?_⟩
    · have := h2 fun i => inclAd F E (x i)
      rwa [diagGL_val, e, hH F E N Λ hΛ, hH F E N Λ hΛ] at this
    · have := h3 _ (incl_mem_hat hx)
      rw [diagGL_val, e] at this
      refine (hH F E N _ hΛ' _).1 ?_
      convert this using 1
      ext i
      exact map_sub (inclAd F E) _ _
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(diagGL_mem_su c J γ).2 ⟨h1, ?_⟩, fun y => ⟨map_mulVec_hat (fun x => (h2 x).1) y, fun hy => ?_⟩,
      fun y hy => ?_⟩
    · obtain ⟨a, ha, hd⟩ := GlobalTheory.CompanionTheory.Ar.Cmp.DetMod.main (𝓞 E) E N Λ 𝔞 γ hΛ.1 hΛ.2 h3
      have h4 := det_mul_conj hJ h1
      have h5 := hN (1 + a) (by rw [hd] at h4; exact h4) (by simpa using ha)
      refine Units.ext ?_
      show (γ : Matrix (Fin N) (Fin N) E).det = 1
      rw [hd]
      exact congrArg (algebraMap (𝓞 E) E) h5
    · have := map_mulVec_hat (F := F) (γ := ((γ⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E))
        (Λ := Λ.toAddSubgroup) (Λ' := Λ.toAddSubgroup)
        (fun x hx => (h2 _).2 (by rwa [mulVec_mulVec, Units.mul_inv, one_mulVec])) _ hy
      rwa [diagGL_val, mulVec_mulVec, ← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _),
        one_mulVec] at this
    · have := map_mulVec_hat (F := F) (γ := (γ : Matrix (Fin N) (Fin N) E) - 1) (Λ := Λ.toAddSubgroup)
        (Λ' := (𝔞 • Λ).toAddSubgroup) (fun x hx => by rw [sub_mulVec, one_mulVec]; exact h3 x hx) y hy
      rwa [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), sub_mulVec, one_mulVec] at this

theorem levelCO (hH : HatCompactOpen) : LevelCO := by
  intro F E _ _ _ _ _ N c J Λ 𝔞 hΛ h𝔞
  obtain ⟨h1, h2, h3⟩ := topRing F E
  choose m hm hm' using fun i : Fin N => exists_smul_mem hΛ (Pi.single i 1)
  have hM : ((∏ i, m i : ℕ) : E) ≠ 0 := Nat.cast_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => hm i)
  obtain ⟨hc, ho⟩ := congCompactOpen (Adf F E) N _ _ (hH F E N Λ hΛ).1 (hH F E N Λ hΛ).2
    (hH F E N _ (isLat_smul hΛ h𝔞)).2 ⟨Units.map (inclAd F E).toMonoidHom (Units.mk0 _ hM), fun i => by
      have := incl_mem_hat (F := F) (Λ := Λ.toAddSubgroup)
        (Λ.smul_of_tower_mem (∏ j ∈ Finset.univ.erase i, m j) (hm' i))
      convert this using 1
      funext j
      show (Pi.single i (inclAd F E ((∏ i, m i : ℕ) : E)) : Fin N → Adf F E) j = _
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
      by_cases h : j = i
      · subst h
        simp
      · simp [Pi.single_eq_of_ne h]⟩
  have hcl : IsClosed (SUA c J : Set (GL (Fin N) (Adf F E))) := by
    refine IsClosed.inter (isClosed_eq ?_ continuous_const)
      (s₂ := {g : GL (Fin N) (Adf F E) | Matrix.GeneralLinearGroup.det g = 1}) ?_
    · exact (Units.continuous_val.matrix_transpose.matrix_mul continuous_const).matrix_mul
        (Units.continuous_val.matrix_map (h3 c))
    · simp only [Units.ext_iff]
      exact isClosed_eq Units.continuous_val.matrix_det continuous_const
  exact ⟨inf_le_left, hc.inter_left hcl, _, ho, Set.inter_comm _ _⟩

end PositivityTheory.EqVol
