module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.CardOfIsFiniteLength

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.Mprime
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem der_satSq {O A : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A] (x : A →ₐ[O] O)
    (D : A →ₗ[O] O) (hD : D ∈ PtDer x O) (f : A) (hf : f ∈ satSq x) : D f = 0 := by
  obtain ⟨c, hc, hcf⟩ := hf
  have hD' : ∀ f g, D (f * g) = x f • D g + x g • D f := hD
  have key : ∀ g ∈ RingHom.ker x ^ 2, D g = 0 := by
    intro g hg
    rw [sq] at hg
    refine Submodule.mul_induction_on hg ?_ ?_
    · intro a ha b hb
      have ha' : x a = 0 := ha
      have hb' : x b = 0 := hb
      rw [hD', ha', hb']; simp
    · intro a b ha hb
      rw [map_add (f := _), ha, hb, add_zero]
  have := key _ hcf
  rw [map_smul, smul_eq_mul] at this
  exact (mul_eq_zero.1 this).resolve_left hc

private theorem len_le_of_inj {O : Type} [CommRing O] [IsLocalRing O] [Finite (ResidueField O)]
    {M N : Type} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
    (hN : Module.length O N ≠ ⊤) (ψ : M → N) (hψ : Function.Injective ψ) :
    Module.length O M ≤ Module.length O N := by
  obtain ⟨hfN, n, hn, hcn⟩ := Formalism.MainNotions.V.Pf.V2.card_of_isFiniteLength (Module.length_ne_top_iff.1 hN)
  have hfM : Finite M := Finite.of_injective ψ hψ
  have hM : IsFiniteLength O M := isFiniteLength_iff_isNoetherian_isArtinian.2 ⟨inferInstance, inferInstance⟩
  obtain ⟨_, m, hm, hcm⟩ := Formalism.MainNotions.V.Pf.V2.card_of_isFiniteLength hM
  have hle := Nat.card_le_card_of_injective ψ hψ
  rw [hcm, hcn] at hle
  have h1 : 1 < Nat.card (ResidueField O) := Finite.one_lt_card
  rw [hm, hn]
  exact_mod_cast (Nat.pow_le_pow_iff_right h1).1 hle

theorem UpperTheory.V.Alg.M.mprime_holds :
    LemmaM' := by
  intro O _ _ _ _ A X _ _ _ _ 𝒜 _ x j hx ι F hF c hc M _ _ D hD hDF hlift
  by_cases htop : cotLen x 𝒜 j F = ⊤
  · rw [htop]; exact le_top
  have hsat : ∀ μ, satSq x ≤ LinearMap.ker (D μ) := by
    intro μ f hf
    obtain ⟨D', hD', -, h⟩ := hlift μ
    rw [LinearMap.mem_ker, h, der_satSq x D' hD' f hf, map_zero]
  have hspan : ∀ μ, (cotSpan x F).comap (cotLat x 𝒜 j).subtype ≤
      LinearMap.ker (((satSq x).liftQ (D μ) (hsat μ)) ∘ₗ (cotLat x 𝒜 j).subtype) := by
    intro μ
    rw [LinearMap.ker_comp]
    refine Submodule.comap_mono ?_
    rw [cotSpan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hDF μ i
  let ψ : M → ((cotLat x 𝒜 j ⧸ (cotSpan x F).comap (cotLat x 𝒜 j).subtype) →ₗ[O] O ⧸ Ideal.span {c}) :=
    fun μ => Submodule.liftQ _ _ (hspan μ)
  have hψ : Function.Injective ψ := by
    intro μ ν h
    apply hD
    have hj : ∀ f ∈ 𝒜 j, D μ f = D ν f := fun f hf =>
      LinearMap.congr_fun h (Submodule.Quotient.mk ⟨(satSq x).mkQ f, f, ⟨hf, hx f hf⟩, rfl⟩)
    have hi : ∀ μ i, i ≠ j → ∀ f ∈ 𝒜 i, D μ f = 0 := by
      intro μ i hi f hf
      obtain ⟨D', -, hw, h⟩ := hlift μ
      rw [h, hw i hi f hf, map_zero]
    refine LinearMap.ext fun f => ?_
    induction f using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => rw [map_zero, map_zero]
    | @homogeneous i m =>
      by_cases hij : i = j
      · subst hij; exact hj _ m.2
      · rw [hi μ i hij _ m.2, hi ν i hij _ m.2]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible hc hp
  have hQ : Module.length O ((O ⧸ maximalIdeal O) →ₗ[O] (O ⧸ Ideal.span {c})) ≤ 1 := by
    rw [Ideal.span_singleton_eq_span_singleton.2 hk]
    exact Formalism.MainNotions.V.Pf.V2.length_hom_residue_le p hp.maximalIdeal_eq hp.ne_zero k
  have hle := Formalism.MainNotions.V.Pf.V2.length_hom_le hQ (Module.length_ne_top_iff.1 htop)
  exact (len_le_of_inj (ne_top_of_le_ne_top htop hle) ψ hψ).trans hle
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.FgHolds
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

theorem UpperTheory.V.Alg.M.fg_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ j, (oz 𝒜 j).FG := by
  classical
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x hx j
  obtain ⟨s, -, hadj⟩ := hx.gen
  have hadj' : Algebra.adjoin (𝒜 0) (s : Set A) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hy : y ∈ Algebra.adjoin O ((𝒜 0 : Set A) ∪ ↑s) := by rw [hadj]; trivial
    have hle : Algebra.adjoin O ((𝒜 0 : Set A) ∪ ↑s) ≤
        (Algebra.adjoin (𝒜 0) (s : Set A)).restrictScalars O := by
      rw [Algebra.adjoin_le_iff]
      rintro z (hz | hz)
      · rw [SetLike.mem_coe, Subalgebra.mem_restrictScalars]
        exact (Algebra.adjoin (𝒜 0) (s : Set A)).algebraMap_mem ⟨z, hz⟩
      · rw [SetLike.mem_coe, Subalgebra.mem_restrictScalars]
        exact Algebra.subset_adjoin hz
    exact (Subalgebra.mem_restrictScalars O).1 (hle hy)
  haveI : Algebra.FiniteType (𝒜 0) A := ⟨⟨s, hadj'⟩⟩
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing (𝒜 0) A
  have hI : (Ideal.span (𝒜 j : Set A)).FG := IsNoetherian.noetherian _
  obtain ⟨t, ht, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hI
  refine ⟨t, le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    exact ht
  · intro y hy
    have hyA : y ∈ 𝒜 j := hy
    have hy' : y ∈ Submodule.span A (t : Set A) := by
      rw [← hspan]
      exact Submodule.subset_span hyA
    obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.1 hy'
    have hyj : y = (DirectSum.decompose 𝒜 y j : A) := (DirectSum.decompose_of_mem_same 𝒜 hyA).symm
    rw [hyj, ← hf, DirectSum.decompose_sum, DFinsupp.finsetSum_apply, Submodule.coe_sum]
    refine Submodule.sum_mem _ fun i hi => ?_
    have e : (DirectSum.decompose 𝒜 (f i • i) j : A) = (DirectSum.decompose 𝒜 (f i) 0 : A) * i := by
      have := DirectSum.coe_decompose_mul_add_of_right_mem 𝒜 (a := f i) (i := 0) (ht hi)
      rw [zero_add] at this
      exact this
    rw [e]
    exact Submodule.smul_mem _ (DirectSum.decompose 𝒜 (f i) 0) (Submodule.subset_span hi)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.GrEqRange
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

section

variable {B A : Type} [CommRing B] [CommRing A] [Algebra B A] {k : ℕ} (N : Fin k → Submodule B A)

private noncomputable def monoL (m : Fin k →₀ ℕ) : lat N m →ₗ[B] rees N where
  toFun f := mono N m f.1 f.2
  map_add' f g := Subtype.ext (by
    show MvPolynomial.monomial m (f.1 + g.1) = MvPolynomial.monomial m f.1 + MvPolynomial.monomial m g.1
    rw [map_add (f := _)])
  map_smul' c f := Subtype.ext (by
    show MvPolynomial.monomial m (c • f.1) = c • MvPolynomial.monomial m f.1
    rw [MvPolynomial.smul_monomial])

private theorem eq_mono {m : Fin k →₀ ℕ} {p : rees N} (hp : p ∈ reesGr N (toDeg m)) :
    p = mono N m (AddMonoidAlgebra.coeff p.1 m) (p.2 m) := by
  classical
  apply Subtype.ext
  ext n
  show _ = AddMonoidAlgebra.coeff (MvPolynomial.monomial m _) n
  rw [MvPolynomial.coeff_monomial]
  split_ifs with h
  · rw [h]
  · exact hp n fun h' => h (toDeg_injective h').symm

private theorem gr_eq_range (m : Fin k →₀ ℕ) : reesGr N (toDeg m) = LinearMap.range (monoL N m) := by
  apply le_antisymm
  · intro p hp
    exact ⟨⟨_, p.2 m⟩, (eq_mono N hp).symm⟩
  · rintro _ ⟨f, rfl⟩
    exact mono_mem N m f.1 f.2

private theorem e_eq (i : Fin k) : e i = toDeg (Finsupp.single i 1) := by
  funext j
  by_cases h : j = i
  · subst h
    simp [e, toDeg]
  · simp [e, toDeg, Pi.single_apply, h, Finsupp.single_apply, Ne.symm h]

private theorem gr_add (m m' : Fin k →₀ ℕ) :
    reesGr N (toDeg (m + m')) = reesGr N (toDeg m) * reesGr N (toDeg m') := by
  apply le_antisymm
  · intro p hp
    have hf : AddMonoidAlgebra.coeff p.1 (m + m') ∈ lat N m * lat N m' := by
      rw [← lat_add]
      exact p.2 (m + m')
    obtain ⟨q, hq, hqv⟩ : ∃ q ∈ reesGr N (toDeg m) * reesGr N (toDeg m'),
        q.1 = MvPolynomial.monomial (m + m') (AddMonoidAlgebra.coeff p.1 (m + m')) := by
      refine Submodule.mul_induction_on hf ?_ ?_
      · intro a ha b hb
        refine ⟨mono N m a ha * mono N m' b hb,
          Submodule.mul_mem_mul (mono_mem N m a ha) (mono_mem N m' b hb), ?_⟩
        show MvPolynomial.monomial m a * MvPolynomial.monomial m' b = _
        rw [MvPolynomial.monomial_mul]
      · rintro x y ⟨q₁, h₁, e₁⟩ ⟨q₂, h₂, e₂⟩
        refine ⟨q₁ + q₂, add_mem h₁ h₂, ?_⟩
        rw [map_add (f := _), ← e₁, ← e₂]
        rfl
    have hpq : p = q := by
      apply Subtype.ext
      rw [hqv]
      exact congrArg Subtype.val (eq_mono N hp)
    rw [hpq]
    exact hq
  · rw [Submodule.mul_le]
    intro a ha b hb
    have hab : AddMonoidAlgebra.coeff a.1 m * AddMonoidAlgebra.coeff b.1 m' ∈ lat N (m + m') := by
      rw [lat_add]
      exact Submodule.mul_mem_mul (a.2 m) (b.2 m')
    have h : a * b = mono N (m + m') _ hab := by
      apply Subtype.ext
      show a.1 * b.1 = MvPolynomial.monomial (m + m') _
      rw [← MvPolynomial.monomial_mul]
      exact congrArg₂ (· * ·) (congrArg Subtype.val (eq_mono N ha)) (congrArg Subtype.val (eq_mono N hb))
    rw [h]
    exact mono_mem N (m + m') _ hab

end

theorem UpperTheory.V.Alg.M.std_holds :
    ∀ (B A : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [CommRing A] [Algebra B A] (k : ℕ)
      (N : Fin k → Submodule B A), (∀ i, (N i).FG) → Std (reesGr N) := by
  intro B A _ _ hB _ _ k N hN
  have hdeg : ∀ d : Deg k, 0 ≤ d → ∃ m : Fin k →₀ ℕ, toDeg m = d := by
    intro d hd
    refine ⟨Finsupp.equivFunOnFinite.symm (fun j => (d j).toNat), ?_⟩
    funext j
    simp [toDeg, Int.toNat_of_nonneg (hd j)]
  refine ⟨hB, ?_, ?_, ?_, ?_⟩
  · intro d hd
    refine (Submodule.eq_bot_iff _).2 fun p hp => ?_
    apply Subtype.ext
    ext m
    have hnn : 0 ≤ toDeg m := fun j => by simp [toDeg]
    have hm : toDeg m ≠ d := fun h => hd (h ▸ hnn)
    simpa using hp m hm
  · have h0 : (0 : Deg k) = toDeg 0 := by
      funext j
      simp [toDeg]
    rw [h0, gr_eq_range]
    ext p
    simp only [LinearMap.mem_range]
    constructor
    · rintro ⟨⟨f, hf⟩, rfl⟩
      have hf' := hf
      rw [lat_zero, Submodule.mem_one] at hf'
      obtain ⟨b, hb⟩ := hf'
      refine ⟨b, Subtype.ext ?_⟩
      show algebraMap B (MvPolynomial (Fin k) A) b = MvPolynomial.monomial 0 f
      rw [MvPolynomial.algebraMap_apply, MvPolynomial.C_apply, hb]
    · rintro ⟨b, rfl⟩
      have hb : algebraMap B A b ∈ lat N 0 := by
        rw [lat_zero]
        exact Submodule.algebraMap_mem b
      refine ⟨⟨algebraMap B A b, hb⟩, Subtype.ext ?_⟩
      show MvPolynomial.monomial 0 (algebraMap B A b) = algebraMap B (MvPolynomial (Fin k) A) b
      rw [MvPolynomial.algebraMap_apply, MvPolynomial.C_apply]
  · intro i
    rw [e_eq, gr_eq_range, LinearMap.range_eq_map]
    refine Submodule.FG.map _ ((Submodule.fg_top _).2 ?_)
    rw [lat_single]
    exact hN i
  · intro d i hd
    obtain ⟨m, rfl⟩ := hdeg d hd
    rw [e_eq, ← toDeg_add, gr_add]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.HomHolds
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

theorem UpperTheory.V.Alg.M.hom_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m),
    Q.ideal.IsHomogeneous 𝒜 ∧ (ideal2 Q).IsHomogeneous 𝒜 ∧ ideal2 Q ≤ Q.ideal := by
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x _ r s r' s' m Q
  refine ⟨?_, ?_, ?_⟩
  · refine Ideal.homogeneous_span 𝒜 _ ?_
    rintro _ ((((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
    exacts [⟨_, Q.hF i⟩, ⟨_, Q.hG i⟩, ⟨_, Q.hE i⟩, ⟨_, Q.hE' i⟩, ⟨_, (Q.hZ i).1⟩]
  · refine Ideal.homogeneous_span 𝒜 _ ?_
    rintro _ ((((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
    exacts [⟨_, sq_mem_neg 𝒜 (Q.hF i)⟩, ⟨_, Q.hG i⟩, ⟨_, sq_mem_pos 𝒜 (Q.hE i)⟩, ⟨_, Q.hE' i⟩, ⟨_, (Q.hZ i).1⟩]
  · refine Ideal.span_le.2 ?_
    rintro _ ((((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
    · exact Ideal.pow_mem_of_mem Q.ideal
        (Ideal.subset_span (Or.inl (Or.inl (Or.inl (Or.inl ⟨i, rfl⟩))))) 2 (by norm_num)
    · exact Ideal.subset_span (Or.inl (Or.inl (Or.inl (Or.inr ⟨i, rfl⟩))))
    · exact Ideal.pow_mem_of_mem Q.ideal
        (Ideal.subset_span (Or.inl (Or.inl (Or.inr ⟨i, rfl⟩)))) 2 (by norm_num)
    · exact Ideal.subset_span (Or.inl (Or.inr ⟨i, rfl⟩))
    · exact Ideal.subset_span (Or.inr ⟨i, rfl⟩)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.NegWeightLe
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem UpperTheory.V.Alg.M.neg_weight_le {τ : Type} (wt : τ → ℤ) (ν : τ →₀ ℕ) :
    -Finsupp.weight wt ν ≤ ((Finsupp.weight (negW wt) ν : ℕ) : ℤ) := by
  simp only [Finsupp.weight_apply, Finsupp.sum]
  push_cast
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hi : -wt i ≤ ((negW wt i : ℕ) : ℤ) := by
    simp only [negW]
    exact Int.self_le_toNat _
  have hc : (0 : ℤ) ≤ (ν i : ℤ) := Int.natCast_nonneg _
  simp only [nsmul_eq_mul, smul_eq_mul]
  push_cast
  nlinarith

theorem UpperTheory.V.Alg.M.fil_holds :
    ∀ (E τ : Type) [CommRing E] (wt : τ → ℤ) (a b : ℕ) (g h : MvPowerSeries τ E), g ∈ fil E wt a → h ∈ fil E wt b →
      g * h ∈ fil E wt (a + b) ∧ ∀ j : ℤ, g ∈ wtPart E wt j → g ∈ fil E wt (-j).toNat := by
  intro E τ _ wt a b g h hg hh
  classical
  refine ⟨?_, ?_⟩
  · intro ν hν
    rw [MvPowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have hw : Finsupp.weight (negW wt) p.1 + Finsupp.weight (negW wt) p.2 =
        Finsupp.weight (negW wt) ν := by
      rw [← hp, map_add (f := _)]
    by_cases h1 : Finsupp.weight (negW wt) p.1 < a
    · rw [hg p.1 h1, zero_mul]
    · rw [hh p.2 (by omega), mul_zero]
  · intro j hj ν hν
    by_contra hne
    have hwj : Finsupp.weight wt ν = j := by
      by_contra h'
      exact hne (hj ν h')
    have key := neg_weight_le wt ν
    rw [hwj] at key
    omega
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.FtHolds
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

theorem UpperTheory.V.Alg.M.ft_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    Algebra.FiniteType (𝒜 0) A ∧ ∀ I : Ideal A, M2 𝒜 I → Algebra.FiniteType O (A ⧸ I) := by
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x hx
  classical
  obtain ⟨s, -, hs⟩ := hx.gen
  have htop : ∀ a : A, a ∈ Algebra.adjoin O ((𝒜 0 : Set A) ∪ (s : Set A)) := by
    intro a
    rw [hs]
    trivial
  refine ⟨?_, ?_⟩
  · refine ⟨⟨s, top_unique ?_⟩⟩
    intro a _
    have key : Algebra.adjoin O ((𝒜 0 : Set A) ∪ (s : Set A)) ≤
        (Algebra.adjoin (𝒜 0) (s : Set A)).restrictScalars O := by
      rw [Algebra.adjoin_le_iff]
      rintro z (hz | hz)
      · exact (Subalgebra.mem_restrictScalars O).mpr
          (Subalgebra.algebraMap_mem (Algebra.adjoin (𝒜 0) (s : Set A)) (⟨z, hz⟩ : 𝒜 0))
      · exact (Subalgebra.mem_restrictScalars O).mpr (Algebra.subset_adjoin hz)
    exact (Subalgebra.mem_restrictScalars O).mp (key (htop a))
  · intro I hI
    obtain ⟨t, ht⟩ := hI
    refine ⟨⟨t ∪ s.image (Ideal.Quotient.mkₐ O I), top_unique ?_⟩⟩
    rintro y -
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective O I y
    have hm : Ideal.Quotient.mkₐ O I a ∈
        (Algebra.adjoin O ((𝒜 0 : Set A) ∪ (s : Set A))).map (Ideal.Quotient.mkₐ O I) :=
      Subalgebra.mem_map.mpr ⟨a, htop a, rfl⟩
    rw [AlgHom.map_adjoin, Set.image_union] at hm
    refine (Algebra.adjoin_le ?_) hm
    rintro z (⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩)
    · have hz : Ideal.Quotient.mkₐ O I b ∈ Submodule.span O (t : Set (A ⧸ I)) := by
        rw [ht]
        exact Submodule.mem_map_of_mem hb
      have h2 := Algebra.span_le_adjoin O (t : Set (A ⧸ I)) hz
      refine Algebra.adjoin_mono ?_ h2
      push_cast
      exact Set.subset_union_left
    · apply Algebra.subset_adjoin
      push_cast
      exact Set.mem_union_right _ (Set.mem_image_of_mem _ hb)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.Satfil
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem satfil_wt {τ : Type} (wt : τ → ℤ) (ν : τ →₀ ℕ) :
    Finsupp.weight wt ν = (Finsupp.weight (posW wt) ν : ℤ) - (Finsupp.weight (negW wt) ν : ℤ) := by
  simp only [Finsupp.weight_apply, Finsupp.sum]
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [posW, negW, nsmul_eq_mul, smul_eq_mul]
  push_cast
  rw [← mul_sub, Int.toNat_sub_toNat_neg]

private theorem satfil_deg {τ : Type} (wt : τ → ℤ) (h : ∀ i, wt i ≠ 0) (ν : τ →₀ ℕ) :
    Finsupp.degree ν ≤ Finsupp.weight (posW wt) ν + Finsupp.weight (negW wt) ν := by
  change (∑ i ∈ ν.support, ν i) ≤ _
  simp only [Finsupp.weight_apply, Finsupp.sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hi : 1 ≤ posW wt i + negW wt i := by
    simp only [posW, negW]
    have := h i
    omega
  simp only [smul_eq_mul]
  nlinarith

theorem UpperTheory.V.Alg.M.satfil_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (τ : Type) [Fintype τ] (wt : τ → ℤ) (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)), IsChart0 𝒜 x wt φ →
      (∀ f ∈ 𝒜 (-1), f ∈ satSq x → φ f ∈ fil (FractionRing O) wt 2) ∧ ∀ b ∈ 𝒜 0, x b = 0 → φ b ∈ fil (FractionRing O) wt 1 := by
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x hx τ _ wt φ hφ
  have hnz : ∀ i, wt i ≠ 0 := by
    intro i
    rcases hφ.wts i with h | h | h | h <;> omega
  have hlow : ∀ y ∈ RingHom.ker x ^ 2, ∀ ν : τ →₀ ℕ, Finsupp.degree ν ≤ 1 →
      MvPowerSeries.coeff ν (φ y) = 0 := by
    intro y hy
    rw [pow_two] at hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro m hm n hn ν hν
      classical
      rw [map_mul, MvPowerSeries.coeff_mul]
      apply Finset.sum_eq_zero
      intro p hp
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      have hd : Finsupp.degree p.1 + Finsupp.degree p.2 ≤ 1 := by
        rw [← map_add (f := _), hp]
        exact hν
      have hm0 : MvPowerSeries.coeff 0 (φ m) = 0 := by
        rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hφ.const, RingHom.mem_ker.mp hm, map_zero]
      have hn0 : MvPowerSeries.coeff 0 (φ n) = 0 := by
        rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hφ.const, RingHom.mem_ker.mp hn, map_zero]
      by_cases h1 : Finsupp.degree p.1 = 0
      · rw [(Finsupp.degree_eq_zero_iff _).mp h1, hm0, zero_mul]
      · have h2 : Finsupp.degree p.2 = 0 := by omega
        rw [(Finsupp.degree_eq_zero_iff _).mp h2, hn0, mul_zero]
    · intro a b ha hb ν hν
      rw [map_add (f := _), map_add (f := _), ha ν hν, hb ν hν, add_zero]
  refine ⟨?_, ?_⟩
  · intro f hf hsat ν hν
    obtain ⟨c, hc, hcf⟩ := hsat
    by_contra hne
    have hw : Finsupp.weight wt ν = -1 := by
      by_contra h'
      exact hne (hφ.graded (-1) f hf ν h')
    have e := satfil_wt wt ν
    have hdeg := satfil_deg wt hnz ν
    have hd1 : Finsupp.degree ν ≤ 1 := by omega
    have h0 := hlow _ hcf ν hd1
    rw [map_smul, ← algebraMap_smul (FractionRing O) c (φ f), map_smul, smul_eq_mul] at h0
    have hc' : algebraMap O (FractionRing O) c ≠ 0 := by
      intro hz
      exact hc (IsFractionRing.injective O (FractionRing O) (by rw [hz, map_zero]))
    exact hne ((mul_eq_zero.mp h0).resolve_left hc')
  · intro b hb hxb ν hν
    by_contra hne
    have hw : Finsupp.weight wt ν = 0 := by
      by_contra h'
      exact hne (hφ.graded 0 b hb ν h')
    have e := satfil_wt wt ν
    have hdeg := satfil_deg wt hnz ν
    have hd : Finsupp.degree ν = 0 := by omega
    rw [(Finsupp.degree_eq_zero_iff _).mp hd, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hφ.const, hxb,
      map_zero] at hne
    exact hne rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.OzTwoMulEqPow
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

section SlopeTestRemainingChoices

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜]

private theorem absR {w a b c : ℤ} {z f : A} (hz : z ∈ 𝒜 w) (hf : f ∈ 𝒜 a * 𝒜 b) (hc : c = w + b) :
    z * f ∈ 𝒜 a * 𝒜 c := by
  subst hc
  refine Submodule.mul_induction_on hf (fun p hp q hq => ?_) (fun p q hp hq => ?_)
  · rw [mul_left_comm]
    exact Submodule.mul_mem_mul hp (SetLike.GradedMul.mul_mem hz hq)
  · rw [mul_add]; exact add_mem hp hq

private theorem absL {w a b c d : ℤ} {z f : A} (hz : z ∈ 𝒜 w) (hf : f ∈ 𝒜 a * 𝒜 b) (hc : c = w + a) (hd : d = b) :
    z * f ∈ 𝒜 c * 𝒜 d := by
  subst hd
  rw [mul_comm (𝒜 a)] at hf
  rw [mul_comm (𝒜 c)]
  exact absR 𝒜 hz hf hc

private def dec (ε j : ℤ) : Submodule O A where
  carrier := {f | f ∈ 𝒜 j ∧ (1 ≤ ε * j → f ∈ 𝒜 ε * 𝒜 (j - ε) ⊔ 𝒜 (2 * ε) * 𝒜 (j - 2 * ε)) ∧
    (2 ≤ ε * j → f ∈ 𝒜 (2 * ε) * 𝒜 (j - 2 * ε))}
  add_mem' ha hb := ⟨add_mem ha.1 hb.1, fun h => add_mem (ha.2.1 h) (hb.2.1 h), fun h => add_mem (ha.2.2 h) (hb.2.2 h)⟩
  zero_mem' := ⟨zero_mem _, fun _ => zero_mem _, fun _ => zero_mem _⟩
  smul_mem' c _ ha := ⟨Submodule.smul_mem _ c ha.1, fun h => Submodule.smul_mem _ c (ha.2.1 h),
    fun h => Submodule.smul_mem _ c (ha.2.2 h)⟩

private theorem dec_mul {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {w j : ℤ} (hw : -2 ≤ w ∧ w ≤ 2) {z f : A} (hz : z ∈ 𝒜 w)
    (hf : f ∈ dec 𝒜 ε j) : z * f ∈ dec 𝒜 ε (w + j) := by
  obtain ⟨h0, h1, h2⟩ := hf
  refine ⟨SetLike.GradedMul.mul_mem hz h0, ?_⟩
  by_cases c2 : w = 2 * ε
  · subst c2
    have : z * f ∈ 𝒜 (2 * ε) * 𝒜 (2 * ε + j - 2 * ε) := by
      rw [add_sub_cancel_left]; exact Submodule.mul_mem_mul hz h0
    exact ⟨fun _ => Submodule.mem_sup_right this, fun _ => this⟩
  by_cases c1 : w = ε
  · subst c1
    refine ⟨fun _ => Submodule.mem_sup_left ?_, fun h => ?_⟩
    · rw [add_sub_cancel_left]; exact Submodule.mul_mem_mul hz h0
    · obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 (h1 (by rcases hε with rfl | rfl <;> omega))
      rw [mul_add]
      exact add_mem (absL 𝒜 hz hp (by ring) (by ring)) (absR 𝒜 hz hq (by ring))
  refine ⟨fun h => ?_, fun h => absR 𝒜 hz (h2 (by rcases hε with rfl | rfl <;> omega)) (by ring)⟩
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 (h1 (by rcases hε with rfl | rfl <;> omega))
  rw [mul_add]
  exact add_mem (Submodule.mem_sup_left (absR 𝒜 hz hp (by ring))) (Submodule.mem_sup_right (absR 𝒜 hz hq (by ring)))

private theorem dec_all [IsLocalRing O] {x : A →ₐ[O] O} (hx : IsWRing 𝒜 x) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    {j : ℤ} {f : A} (hf : f ∈ 𝒜 j) : f ∈ dec 𝒜 ε j := by
  obtain ⟨s, hs, htop⟩ := hx.gen
  have gen : ∀ (w : ℤ), (-2 ≤ w ∧ w ≤ 2) → ∀ z ∈ 𝒜 w, ∀ g ∈ ⨆ i, dec 𝒜 ε i, z * g ∈ ⨆ i, dec 𝒜 ε i := by
    intro w hw z hz g hg
    refine Submodule.iSup_induction (motive := fun g => z * g ∈ ⨆ i, dec 𝒜 ε i) _ hg (fun i g hg => ?_) (by simp)
      (fun a b ha hb => by rw [mul_add]; exact add_mem ha hb)
    exact Submodule.mem_iSup_of_mem _ (dec_mul 𝒜 hε hw hz hg)
  have key : ∀ a ∈ Algebra.adjoin O ((𝒜 0 : Set A) ∪ s), ∀ g ∈ ⨆ i, dec 𝒜 ε i, a * g ∈ ⨆ i, dec 𝒜 ε i := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
      rcases ha with ha | ha
      · exact gen 0 (by omega) a ha
      · rcases hs a ha with h | h | h | h <;> exact gen _ (by omega) a h
    | algebraMap c =>
      intro g hg
      rw [← Algebra.smul_def]; exact Submodule.smul_mem _ c hg
    | add a b _ _ ha hb =>
      intro g hg
      rw [add_mul]; exact add_mem (ha g hg) (hb g hg)
    | mul a b _ _ ha hb =>
      intro g hg
      rw [mul_assoc]; exact ha _ (hb g hg)
  have h1 : (1 : A) ∈ dec 𝒜 ε 0 := ⟨SetLike.GradedOne.one_mem, fun h => by omega, fun h => by omega⟩
  have h2 := key f (htop ▸ Algebra.mem_top) 1 (Submodule.mem_iSup_of_mem _ h1)
  rw [mul_one] at h2
  have h3 : ∀ g ∈ ⨆ i, dec 𝒜 ε i, (DirectSum.decompose 𝒜 g j : A) ∈ dec 𝒜 ε j := by
    intro g hg
    refine Submodule.iSup_induction (motive := fun g => (DirectSum.decompose 𝒜 g j : A) ∈ dec 𝒜 ε j) _ hg
      (fun i g hg => ?_) (by simp) (fun a b ha hb => ?_)
    · by_cases hi : i = j
      · subst hi
        rwa [DirectSum.decompose_of_mem_same 𝒜 hg.1]
      · rw [DirectSum.decompose_of_mem_ne 𝒜 hg.1 hi]; exact zero_mem _
    · simp only [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add]
      exact add_mem ha hb
  have h4 := h3 f h2
  rwa [DirectSum.decompose_of_mem_same 𝒜 hf] at h4

private theorem pow_eps [IsLocalRing O] {x : A →ₐ[O] O} (hx : IsWRing 𝒜 x) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (n : ℕ) : oz 𝒜 (2 * ε * n) = oz 𝒜 (2 * ε) ^ n := by
  induction n with
  | zero =>
    ext f
    simp only [Nat.cast_zero, mul_zero, pow_zero, mem_oz, Submodule.mem_one]
    exact ⟨fun h => ⟨⟨f, h⟩, rfl⟩, fun ⟨b, hb⟩ => hb ▸ b.2⟩
  | succ n ih =>
    rw [pow_succ, mul_comm (_ ^ n), ← ih]
    apply le_antisymm
    · intro f hf
      have h := (dec_all 𝒜 hx hε hf).2.2 (by rcases hε with rfl | rfl <;> push_cast <;> omega)
      have e : 2 * ε * ((n + 1 : ℕ) : ℤ) - 2 * ε = 2 * ε * n := by push_cast; ring
      rw [e] at h
      clear hf
      refine Submodule.mul_induction_on h (fun p hp q hq => ?_) (fun p q hp hq => add_mem hp hq)
      exact Submodule.mul_mem_mul hp hq
    · refine Submodule.mul_le.2 fun p hp q hq => ?_
      have e : 2 * ε * ((n + 1 : ℕ) : ℤ) = 2 * ε + 2 * ε * n := by push_cast; ring
      rw [mem_oz, e]
      exact SetLike.GradedMul.mul_mem (A := 𝒜) hp hq

end SlopeTestRemainingChoices

theorem UpperTheory.V.Alg.M.oz_two_mul_eq_pow :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ n : ℕ, oz 𝒜 (-(2 * n)) = oz 𝒜 (-2) ^ n ∧ oz 𝒜 (2 * n) = oz 𝒜 2 ^ n := by
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x hx n
  have h1 := pow_eps 𝒜 hx (Or.inr rfl) n
  have h2 := pow_eps 𝒜 hx (Or.inl rfl) n
  have e : (2 * -1 * n : ℤ) = -(2 * n) := by ring
  rw [e] at h1
  rw [mul_one] at h2
  exact ⟨h1, h2⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ExistsSecNotMem
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

section SlopeTestRemainingChoices

variable {B A : Type} [CommRing B] [CommRing A] [Algebra B A] {k : ℕ} (N : Fin k → Submodule B A)

private theorem coe_sec_eq_monomial_single (i : Fin k) (f : A) (hf : f ∈ N i) :
    (sec N i f hf : MvPolynomial (Fin k) A) = MvPolynomial.monomial (Finsupp.single i 1) f := rfl

private theorem toDeg_single_one (i : Fin k) : toDeg (Finsupp.single i 1) = e i := by
  funext j
  by_cases h : j = i
  · subst h
    simp [toDeg, e]
  · simp [toDeg, e, h, Finsupp.single_apply, Ne.symm h]

private theorem exists_sec_notMem {p : Ideal (rees N)} (hp : ¬ Irr (reesGr N) ≤ p) (i : Fin k) :
    ∃ (f : A) (hf : f ∈ N i), sec N i f hf ∉ p := by
  by_contra hcon
  push_neg at hcon
  apply hp
  have hle : Ideal.span (reesGr N (e i) : Set (rees N)) ≤ p := by
    rw [Ideal.span_le]
    intro q hq
    have hc : AddMonoidAlgebra.coeff (q : MvPolynomial (Fin k) A) (Finsupp.single i 1) ∈ N i := by
      have := q.2 (Finsupp.single i 1)
      rwa [lat_single] at this
    have hq' : q = sec N i _ hc := by
      apply Subtype.ext
      rw [coe_sec_eq_monomial_single]
      ext m
      rw [MvPolynomial.coeff_monomial]
      split_ifs with hm
      · rw [hm]
      · apply hq m
        intro hd
        apply hm
        apply toDeg_injective
        rw [hd, toDeg_single_one]
    rw [hq']
    exact hcon _ hc
  exact le_trans (le_trans Ideal.prod_le_inf (Finset.inf_le (Finset.mem_univ i))) hle

private theorem sec_mul_sec (i j : Fin k) {f g : A} (hf : f ∈ N i) (hg : g ∈ N i) (hf' : f ∈ N j) (hg' : g ∈ N j) :
    sec N i f hf * sec N j g hg' = sec N i g hg * sec N j f hf' := by
  apply Subtype.ext
  simp only [Subalgebra.coe_mul, coe_sec_eq_monomial_single, MvPolynomial.monomial_mul]
  rw [mul_comm f g]

end SlopeTestRemainingChoices

private theorem algebraMap_mul_sec_mul_sec_eq_of_mul_eq {B A : Type} [CommRing B] [CommRing A] [Algebra B A] {k : ℕ}
    (N : Fin k → Submodule B A) (c : B) (i j : Fin k) {x y x' y' : A} (hx : x ∈ N i) (hy : y ∈ N j)
    (hx' : x' ∈ N i) (hy' : y' ∈ N j) (h : algebraMap B A c * x * y = x' * y') :
    algebraMap B (rees N) c * (sec N i x hx * sec N j y hy) = sec N i x' hx' * sec N j y' hy' := by
  apply Subtype.ext
  simp only [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, coe_sec_eq_monomial_single, MvPolynomial.algebraMap_apply,
    MvPolynomial.monomial_mul, MvPolynomial.C_mul_monomial]
  rw [← h, mul_assoc]

theorem UpperTheory.V.Alg.M.zi_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m),
    ∀ p : Ideal (mR Q), p.IsPrime → ¬ Irr (mGr Q) ≤ p → secs (ts Q) ≤ p → (∀ i, algebraMap (𝒜 0) (mR Q) ⟨Q.Z i, (Q.hZ i).1⟩ ∈ p) →
      (∀ b : 𝒜 0, (b : A) ∈ Q.ideal → algebraMap (𝒜 0) (mR Q) b ∈ p) ∧
      ∀ i, sec (mN 𝒜 (Q.F (Fin.last r))) 0 (Q.F i ^ 2) (sq_mem_neg 𝒜 (Q.hF i)) ∈ p := by
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x _ r s r' s' m Q P hP hIrr hts hZ
  have hmul : ∀ {i j l : ℤ} {a b : A}, i + j = l → a ∈ 𝒜 i → b ∈ 𝒜 j → a * b ∈ 𝒜 l := by
    rintro i j l a b rfl ha hb
    exact SetLike.mul_mem_graded ha hb
  have m0 : ∀ {a : A}, a ∈ 𝒜 (-2) → a ∈ mN 𝒜 (Q.F (Fin.last r)) 0 := fun h => h
  have m1 : ∀ {a : A}, a ∈ 𝒜 2 → a ∈ mN 𝒜 (Q.F (Fin.last r)) 1 := fun h => h
  have m2 : ∀ {a : A}, a ∈ mN 𝒜 (Q.F (Fin.last r)) 2 → a ∈ 𝒜 (-2) := by
    intro a ha
    have hle : ((𝒜 0) ∙ Q.F (Fin.last r) ^ 2 ⊔ oz 𝒜 (-2) * oz 𝒜 (-2) * oz 𝒜 2 : Submodule (𝒜 0) A)
        ≤ oz 𝒜 (-2) := by
      apply sup_le
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        exact sq_mem_neg 𝒜 (Q.hF _)
      · apply Submodule.mul_le.2
        intro u hu v hv
        have hu' : u ∈ oz 𝒜 (-4) :=
          (Submodule.mul_le.2 (fun a ha b hb => hmul (i := -2) (j := -2) (by norm_num) ha hb) :
            oz 𝒜 (-2) * oz 𝒜 (-2) ≤ oz 𝒜 (-4)) hu
        exact hmul (i := -4) (j := 2) (by norm_num) hu' hv
    exact hle ha
  have hF2 : Q.F (Fin.last r) ^ 2 ∈ mN 𝒜 (Q.F (Fin.last r)) 2 :=
    Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
  have hmem : ∀ {d : Deg 3} {u : mR Q}, (d, u) ∈ ts Q → u ∈ P := fun h => hts (Ideal.subset_span ⟨_, h⟩)
  obtain ⟨g0, hg0, hg0P⟩ := exists_sec_notMem _ hIrr 0
  obtain ⟨f1, hf1, hf1P⟩ := exists_sec_notMem _ hIrr 1
  obtain ⟨h2, hh2, hh2P⟩ := exists_sec_notMem _ hIrr 2
  have hFlast : sec (mN 𝒜 (Q.F (Fin.last r))) 2 (Q.F (Fin.last r) ^ 2) hF2 ∈ P :=
    hmem (d := e 2) (by simp [ts, tsR])
  have hsq : ∀ i, sec (mN 𝒜 (Q.F (Fin.last r))) 0 (Q.F i ^ 2) (sq_mem_neg 𝒜 (Q.hF i)) ∈ P := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have heq := sec_mul_sec (mN 𝒜 (Q.F (Fin.last r))) 0 2 (sq_mem_neg 𝒜 (Q.hF (Fin.last r)))
        (m0 (m2 hh2)) hF2 hh2
      have hin : sec (mN 𝒜 (Q.F (Fin.last r))) 0 (Q.F (Fin.last r) ^ 2) (sq_mem_neg 𝒜 (Q.hF (Fin.last r))) *
          sec (mN 𝒜 (Q.F (Fin.last r))) 2 h2 hh2 ∈ P := by
        rw [heq]
        exact P.mul_mem_left _ hFlast
      exact (hP.mem_or_mem hin).resolve_right hh2P
    · exact hmem (d := e 0) (by simp [ts, tsF, List.mem_ofFn])
  refine ⟨?_, hsq⟩
  set u := sec (mN 𝒜 (Q.F (Fin.last r))) 0 g0 hg0 * sec (mN 𝒜 (Q.F (Fin.last r))) 1 f1 hf1 with hu_def
  have hu : u ∉ P := fun h => (hP.mem_or_mem h).elim hg0P hf1P
  have key : ∀ w : 𝒜 0, algebraMap (𝒜 0) (mR Q) w * u ∈ P → algebraMap (𝒜 0) (mR Q) w ∈ P :=
    fun w h => (hP.mem_or_mem h).resolve_right hu
  have keysq : ∀ w : 𝒜 0, algebraMap (𝒜 0) (mR Q) (w * w) * u ∈ P → algebraMap (𝒜 0) (mR Q) w ∈ P := by
    intro w h
    have := key _ h
    rw [map_mul] at this
    exact (hP.mem_or_mem this).elim id id
  have hgen : ∀ (d : ℤ) (g : A) (hg : g ∈ 𝒜 d),
      (∀ (j : ℤ) (hj : j + d = 0) (c : A) (hc : c ∈ 𝒜 j),
        algebraMap (𝒜 0) (mR Q) ⟨c * g, hmul hj hc hg⟩ ∈ P) →
      ∀ a : A, algebraMap (𝒜 0) (mR Q) (DirectSum.decompose 𝒜 (a * g) 0) ∈ P := by
    intro d g hg hc a
    induction a using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | @homogeneous j a =>
      by_cases hj : j + d = 0
      · have h0 := hc j hj a a.2
        convert h0 using 2
        apply Subtype.ext
        exact DirectSum.decompose_of_mem_same 𝒜 (hmul hj a.2 hg)
      · have h0 : DirectSum.decompose 𝒜 ((a : A) * g) 0 = 0 :=
          Subtype.ext (DirectSum.decompose_of_mem_ne 𝒜 (hmul rfl a.2 hg) hj)
        rw [h0, map_zero]
        exact P.zero_mem
    | add a a' ha ha' =>
      rw [add_mul, DirectSum.decompose_add, DirectSum.add_apply, map_add (f := _)]
      exact P.add_mem ha ha'
  intro b hb
  have hall : ∀ y ∈ Q.ideal, ∀ a : A, algebraMap (𝒜 0) (mR Q) (DirectSum.decompose 𝒜 (a * y) 0) ∈ P := by
    intro y hy
    unfold Eqns.ideal at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      rcases hy with ((((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
      · refine hgen (-1) _ (Q.hF i) ?_
        intro j hj c hc
        obtain rfl : j = 1 := by omega
        apply keysq
        rw [algebraMap_mul_sec_mul_sec_eq_of_mul_eq _ _ 0 1 hg0 hf1 (sq_mem_neg 𝒜 (Q.hF i))
          (m1 (hmul (i := 0) (j := 2) (by norm_num) (hmul (i := 2) (j := -2) (by norm_num)
            (hmul (i := 1) (j := 1) (by norm_num) hc hc) hg0) hf1)) (by change c * Q.F i * (c * Q.F i) * g0 * f1 = _; ring)]
        exact P.mul_mem_right _ (hsq i)
      · refine hgen (-2) _ (Q.hG i) ?_
        intro j hj c hc
        obtain rfl : j = 2 := by omega
        apply key
        rw [algebraMap_mul_sec_mul_sec_eq_of_mul_eq _ _ 0 1 hg0 hf1 (Q.hG i)
          (m1 (hmul (i := 0) (j := 2) (by norm_num) (hmul (i := 2) (j := -2) (by norm_num) hc hg0) hf1))
          (by change c * Q.G i * g0 * f1 = _; ring)]
        exact P.mul_mem_right _ (hmem (d := e 0) (by simp [ts, tsR, List.mem_ofFn]))
      · refine hgen 1 _ (Q.hE i) ?_
        intro j hj c hc
        obtain rfl : j = -1 := by omega
        apply keysq
        rw [algebraMap_mul_sec_mul_sec_eq_of_mul_eq _ _ 0 1 hg0 hf1
          (m0 (hmul (i := -4) (j := 2) (by norm_num) (hmul (i := -2) (j := -2) (by norm_num)
            (hmul (i := -1) (j := -1) (by norm_num) hc hc) hg0) hf1)) (sq_mem_pos 𝒜 (Q.hE i))
          (by change c * Q.E i * (c * Q.E i) * g0 * f1 = _; ring)]
        exact P.mul_mem_left _ (hmem (d := e 1) (by simp [ts, tsR, List.mem_ofFn]))
      · refine hgen 2 _ (Q.hE' i) ?_
        intro j hj c hc
        obtain rfl : j = -2 := by omega
        apply key
        rw [algebraMap_mul_sec_mul_sec_eq_of_mul_eq _ _ 0 1 hg0 hf1
          (m0 (hmul (i := -4) (j := 2) (by norm_num) (hmul (i := -2) (j := -2) (by norm_num) hc hg0) hf1))
          (Q.hE' i) (by change c * Q.E' i * g0 * f1 = _; ring)]
        exact P.mul_mem_left _ (hmem (d := e 1) (by simp [ts, tsR, List.mem_ofFn]))
      · refine hgen 0 _ (Q.hZ i).1 ?_
        intro j hj c hc
        obtain rfl : j = 0 := by omega
        have : (⟨c * Q.Z i, hmul hj hc (Q.hZ i).1⟩ : 𝒜 0) = ⟨c, hc⟩ * ⟨Q.Z i, (Q.hZ i).1⟩ := rfl
        rw [this, map_mul]
        exact P.mul_mem_left _ (hZ i)
    | zero => intro a; simp
    | add y z _ _ hy hz =>
      intro a
      rw [mul_add, DirectSum.decompose_add, DirectSum.add_apply, map_add (f := _)]
      exact P.add_mem (hy a) (hz a)
    | smul c y _ hy =>
      intro a
      rw [smul_eq_mul, ← mul_assoc]
      exact hy (a * c)
  have h1 := hall _ hb 1
  rw [one_mul] at h1
  convert h1 using 2
  apply Subtype.ext
  exact (DirectSum.decompose_of_mem_same 𝒜 b.2).symm
end
