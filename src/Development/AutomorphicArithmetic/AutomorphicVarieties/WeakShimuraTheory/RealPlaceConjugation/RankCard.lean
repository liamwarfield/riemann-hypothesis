module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RbUVal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.KatoConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.RankCard
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

theorem UpperTheory.V.Ws.rank_le_of_card_le_pow_card_field :
    ∀ (k W : Type) [Field k] [Finite k] [AddCommGroup W] [Module k W] (n : ℕ), CardLe W (Nat.card k ^ n) → Module.rank k W ≤ n := by
  intro k W _ _ _ _ n hW
  obtain ⟨hfin, hle⟩ := hW
  haveI := hfin
  haveI : Module.Finite k W := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := k)] at hle
  have hk : 1 < Nat.card k := Finite.one_lt_card
  have hr : Module.finrank k W ≤ n := (Nat.pow_le_pow_iff_right hk).1 hle
  rw [← Module.finrank_eq_rank]
  exact_mod_cast hr
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.ExistsZmodPrimeRepresentationOfTorsion
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem UpperTheory.V.Ws.exists_zmod_representation (n : ℕ) (Γ : Type) [Group Γ] (R M : Type) [CommRing R]
    [AddCommGroup M] [Module R M] [Module (ZMod n) M] (ρ : Representation R Γ M) :
    ∃ ρ' : Representation (ZMod n) Γ M, ∀ g m, ρ' g m = ρ g m := by
  refine ⟨{ toFun := fun g => (ρ g).toAddMonoidHom.toZModLinearMap n
            map_one' := ?_
            map_mul' := ?_ }, ?_⟩
  · ext m
    simp
  · intro g h
    ext m
    simp
  · intro g m
    rfl

theorem UpperTheory.V.Ws.exists_zmod_prime_representation_of_torsion :
    ∀ (l : ℕ) (Γ : Type) [Group Γ] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M], (∀ m : M, l • m = 0) → ∀ ρ : Representation R Γ M, ∃ (_ : Module (ZMod (l ^ 1)) M) (ρ' : Representation (ZMod (l ^ 1)) Γ M), ∀ g m, ρ' g m = ρ g m := by
  intro l Γ _ R M _ _ _ hl ρ
  letI : Module (ZMod (l ^ 1)) M := AddCommGroup.zmodModule (fun m => by simpa using hl m)
  obtain ⟨ρ', hρ'⟩ := UpperTheory.V.Ws.exists_zmod_representation (l ^ 1) Γ R M ρ
  exact ⟨this, ρ', hρ'⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.LocalH1FiniteModL
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem natCard_dual_eq_natCard_of_finite (K V : Type) [Field K] [Finite K] [AddCommGroup V] [Module K V] [Finite V] :
    Nat.card (Module.Dual K V) = Nat.card V := by
  haveI : Module.Finite K V := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := K) (V := Module.Dual K V),
    Module.natCard_eq_pow_finrank (K := K) (V := V), Subspace.dual_finrank_eq]

theorem UpperTheory.V.Ws.local_h1_finite_mod_l :
    LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (ρ : Representation (ZMod (l ^ 1)) (Dec (F := F) A) M), IsPlaceOver A v → ContAction ρ → Finite (H1 ρ) ∧ Nat.card (H1 ρ) ≤ Nat.card (H0 ρ) * Nat.card M ^ (1 + if ((l : ℕ) : 𝓞 F) ∈ v.asIdeal then locDeg v else 0) := by
  intro hF hT hE F Ω _ _ _ _ _ l _ M _ _ _ _ _ A v ρ hv hρ
  haveI : Fact (Nat.Prime (l ^ 1)) := ⟨by rw [pow_one]; exact Fact.out⟩
  obtain ⟨_, hf1, _, _⟩ := hF F Ω l 1 M A ρ v one_pos hv hρ
  obtain ⟨⟨e2⟩, _, _, _, hbij⟩ := hT F Ω l 1 M A ρ v one_pos hv hρ
  obtain ⟨hEram, hEun⟩ := hE F Ω l 1 M A ρ v one_pos hv hρ
  obtain ⟨e2'⟩ : Nonempty (H2 ((charRep ((cycMod F Ω l 1).comp (Dec (F := F) A).subtype)).comp
      (MonoidHom.id _)) ≃ₗ[ZMod (l ^ 1)] ZMod (l ^ 1)) := by
    rw [MonoidHom.comp_id]
    exact ⟨e2⟩
  haveI hfinD : Finite (Module.Dual (ZMod (l ^ 1)) M) :=
    Finite.of_injective (fun f : Module.Dual (ZMod (l ^ 1)) M => (f : M → ZMod (l ^ 1))) DFunLike.coe_injective
  haveI hfinT : Finite (TDual (ZMod (l ^ 1)) M) := hfinD
  have hH2 : Nat.card (H2 ρ) ≤ Nat.card M := by
    calc Nat.card (H2 ρ) = Nat.card (H2 (ρ.comp (MonoidHom.id _))) := by rw [MonoidHom.comp_id]
      _ = _ := Nat.card_eq_of_bijective _ hbij
      _ = Nat.card (Module.Dual (ZMod (l ^ 1)) ↥(H0 ((twDual ((cycMod F Ω l 1).comp (Dec (F := F) A).subtype) ρ).comp
            (MonoidHom.id _)))) := Nat.card_congr (LinearEquiv.congrRight e2').toEquiv
      _ = Nat.card ↥(H0 ((twDual ((cycMod F Ω l 1).comp (Dec (F := F) A).subtype) ρ).comp
            (MonoidHom.id _))) := natCard_dual_eq_natCard_of_finite _ _
      _ ≤ Nat.card (TDual (ZMod (l ^ 1)) M) := Nat.card_le_card_of_injective _ Subtype.val_injective
      _ = Nat.card M := natCard_dual_eq_natCard_of_finite _ _
  refine ⟨hf1, ?_⟩
  by_cases hl : ((l : ℕ) : 𝓞 F) ∈ v.asIdeal
  · rw [if_pos hl, hEram hl, pow_add, pow_one (Nat.card M), ← mul_assoc]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hH2)
  · rw [if_neg hl, hEun hl, add_zero, pow_one (Nat.card M)]
    exact Nat.mul_le_mul_left _ hH2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.SumDeg
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

theorem UpperTheory.V.Ws.sum_local_degree_above_l_le_finrank :
    ∀ (F : Type) [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] (S : Finset (HeightOneSpectrum (𝓞 F))), (∑ v ∈ S, if ((l : ℕ) : 𝓞 F) ∈ v.asIdeal then locDeg v else 0) ≤ Module.finrank ℚ F := by
  intro F _ _ l hl S
  have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast hl.out.ne_zero
  set p : Ideal ℤ := Ideal.span {(l : ℤ)} with hpdef
  have hpp : p.IsPrime := (Ideal.span_singleton_prime hl0).2 (Nat.prime_iff_prime_int.mp hl.out)
  have hpb : p ≠ ⊥ := by
    rw [hpdef, Ne, Ideal.span_singleton_eq_bot]
    exact hl0
  haveI hpm : p.IsMaximal := hpp.isMaximal hpb
  have key := Ideal.sum_ramification_inertia_eq_finrank p (𝓞 F)
  rw [NumberField.RingOfIntegers.rank] at key
  rw [← key, ← Finset.sum_filter]
  set g : Ideal (𝓞 F) → ℕ := fun I => I.ramificationIdx ℤ * I.inertiaDeg ℤ with hg
  have h1 : ∑ v ∈ S.filter (fun v => ((l : ℕ) : 𝓞 F) ∈ v.asIdeal), locDeg v
      = ∑ I ∈ (S.filter (fun v => ((l : ℕ) : 𝓞 F) ∈ v.asIdeal)).image (fun v => v.asIdeal), g I := by
    rw [Finset.sum_image]
    · rfl
    · intro a _ b _ hab
      exact HeightOneSpectrum.ext hab
  have h2 : ∑ q : p.primesOver (𝓞 F), q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ
      = ∑ I ∈ (Finset.univ : Finset (p.primesOver (𝓞 F))).image Subtype.val, g I := by
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact Subtype.ext hab
  rw [h1, h2]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro I hI
    simp only [Finset.mem_image, Finset.mem_filter] at hI
    obtain ⟨v, ⟨_, hv⟩, rfl⟩ := hI
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    have hle : p ≤ Ideal.under ℤ v.asIdeal := by
      rw [hpdef, Ideal.span_le, Set.singleton_subset_iff]
      simpa [Ideal.under, Ideal.mem_comap] using hv
    have hne : Ideal.under ℤ v.asIdeal ≠ ⊤ := (Ideal.IsPrime.under ℤ v.asIdeal).ne_top
    have heq : p = Ideal.under ℤ v.asIdeal := hpm.eq_of_le hne hle
    exact ⟨⟨v.asIdeal, ⟨v.isPrime, ⟨heq⟩⟩⟩, rfl⟩
  · intro _ _ _
    exact Nat.zero_le _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.CocycleCardEulerFormula
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

theorem UpperTheory.V.Ws.cocycle_card_euler_formula :
    ∀ (R Γ M : Type) [CommRing R] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module R M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R Γ M), ContAction ρ → Finite (H1 ρ) → Finite (Z1 ρ) ∧ Nat.card (Z1 ρ) * Nat.card (H0 ρ) = Nat.card (H1 ρ) * Nat.card M := by
  intro R Γ M _ _ _ _ _ _ _ _ ρ hρ hH1
  have hB1Z1 : B1 ρ ≤ Z1 ρ := by
    intro f hf
    obtain ⟨m, rfl⟩ := LinearMap.mem_range.1 hf
    rw [mem_Z1_iff_cocycle]
    have hfun : (d0 ρ m) = fun g => ρ g m - m := funext fun g => amitsur_d0_apply ρ m g
    refine ⟨?_, fun g h => ?_⟩
    · rw [hfun]
      exact (hρ.comp (Continuous.prodMk continuous_id continuous_const)).sub continuous_const
    · simp only [amitsur_d0_apply, map_mul, Module.End.mul_apply, map_sub]
      abel
  have hker : LinearMap.ker (d0 ρ) = H0 ρ := by
    ext m
    rw [LinearMap.mem_ker, mem_riemannRochSpace_iff_regularAt_everywhere]
    constructor
    · intro h g
      have := congrFun h g
      rw [amitsur_d0_apply, Pi.zero_apply, sub_eq_zero] at this
      exact this
    · intro h
      funext g
      rw [amitsur_d0_apply, h g, sub_self, Pi.zero_apply]
  have hq : Nat.card (M ⧸ LinearMap.ker (d0 ρ)) = Nat.card (B1 ρ) :=
    Nat.card_congr (d0 ρ).quotKerEquivRange.toEquiv
  have hM := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker (d0 ρ))
  rw [hq, hker] at hM
  have hB : Nat.card (Submodule.comap (Z1 ρ).subtype (B1 ρ)) = Nat.card (B1 ρ) :=
    Nat.card_congr (Submodule.comapSubtypeEquivOfLe hB1Z1).toEquiv
  have hZ := Submodule.card_eq_card_quotient_mul_card (Submodule.comap (Z1 ρ).subtype (B1 ρ))
  rw [hB] at hZ
  have hMpos : Nat.card M ≠ 0 := Nat.card_pos.ne'
  have hB1pos : Nat.card (B1 ρ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hM
    exact hMpos hM
  have hH1pos : Nat.card (H1 ρ) ≠ 0 := Nat.card_pos.ne'
  refine ⟨Nat.finite_of_card_ne_zero ?_, ?_⟩
  · rw [hZ]
    exact mul_ne_zero hB1pos hH1pos
  · rw [hZ, hM]
    change Nat.card (B1 ρ) * Nat.card (H1 ρ) * Nat.card (H0 ρ) =
      Nat.card (H1 ρ) * (Nat.card (H0 ρ) * Nat.card (B1 ρ))
    ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.KrFacts
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.XdualBase
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.xdualBase :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (E : Type) [Field E] [NumberField E] [Algebra F E] [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω] (N : ℕ) (U : Subgroup (G F Ω)) (R M : Type) [CommRing R] [AddCommGroup M] [Module R M], U ≤ galOf F E Ω →
    (∃ ε : (U → M) ≃ₗ[R] (U.comap (galEmb F E Ω) → M), (∀ φ u, ε φ u = φ ⟨galEmb F E Ω u.1, u.2⟩) ∧ (XDual N U R M).map ε.toLinearMap = XDual N (U.comap (galEmb F E Ω)) R M ∧
      ∀ (σ : Ω ≃+* Ω) (T : M →ₗ[R] M), (conjCond U σ T).map ε.toLinearMap = conjCond (U.comap (galEmb F E Ω)) σ T) ∧
    ∀ (l : ℕ) [Fact l.Prime], (cycU l (galOf F E Ω)).comap (galEmb F E Ω) = Uinf E Ω l ∧ ∀ n, (levU l (galOf F E Ω) n).comap (galEmb F E Ω) = Un E Ω l n := by
  intro F Ω _ _ _ _ _ E _ _ _ _ _ _ N U R M _ _ _ hU
  obtain ⟨hD, hI, hc, -⟩ := toGalDict F Ω E U hU
  obtain ⟨hE, -, -⟩ := galEmbTop F E Ω
  let e : U.comap (galEmb F E Ω) ≃ U :=
    { toFun := fun u => ⟨galEmb F E Ω u.1, u.2⟩
      invFun := fun u => ⟨toGal E hU u, u.2⟩
      left_inv := fun u => rfl
      right_inv := fun u => rfl }
  have hec : Continuous e := (hE.continuous.comp continuous_subtype_val).subtype_mk _
  have hes : Continuous e.symm := hc.subtype_mk _
  have hm : ∀ a b, e (a * b) = e a * e b := fun a b => rfl
  have hms : ∀ a b, e.symm (a * b) = e.symm a * e.symm b := fun a b => rfl
  refine ⟨⟨LinearEquiv.funCongrLeft R M e, fun φ u => rfl, ?_, fun σ T => ?_⟩, fun l _ => ?_⟩
  · ext ψ
    constructor
    · rintro ⟨φ, ⟨h1, h2, h3, h4⟩, rfl⟩
      exact ⟨h1.comp_continuous hec, fun a b => h2 (e a) (e b), fun A u hu => h3 A (e u) ((hI A (e u)).1 hu),
        fun A hA u hu => h4 A hA (e u) ((hD A (e u)).1 hu)⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨ψ ∘ e.symm, ⟨h1.comp_continuous hes, fun a b => h2 (e.symm a) (e.symm b),
        fun A u hu => h3 A (e.symm u) ((hI A u).2 hu), fun A hA u hu => h4 A hA (e.symm u) ((hD A u).2 hu)⟩, rfl⟩
  · ext ψ
    constructor
    · rintro ⟨φ, h, rfl⟩
      exact fun u u' huu => h (e u) (e u') huu
    · intro h
      exact ⟨ψ ∘ e.symm, fun u u' huu => h (e.symm u) (e.symm u') huu, rfl⟩
  · have hz : ∀ g, cycZ F Ω l (galEmb F E Ω g) = cycZ E Ω l g := fun g => rfl
    refine ⟨?_, fun n => ?_⟩
    · ext g
      exact ⟨fun h => ⟨trivial, (hz g).symm.trans h.2⟩, fun h => ⟨galEmb_mem F E Ω g, (hz g).trans h.2⟩⟩
    · ext g
      exact ⟨fun h => ⟨trivial, h.2⟩, fun h => ⟨galEmb_mem F E Ω g, h.2⟩⟩
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem cyc_open (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ)
    [hl : Fact l.Prime] : IsOpen ((cycMod F Ω l 1).ker : Set (G F Ω)) := by
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  have e1 : ((cycMod F Ω l 1).ker : Set (G F Ω)) =
      (fun g => ((cycZ F Ω l g : ℤ_[l]ˣ) : ℤ_[l]) - 1) ⁻¹' Metric.closedBall 0 ((l : ℝ) ^ (-(1 : ℕ) : ℤ)) := by
    ext g
    rw [Set.mem_preimage, mem_closedBall_zero_iff, PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow,
      RingHom.mem_ker, map_sub, map_one, sub_eq_zero, SetLike.mem_coe, MonoidHom.mem_ker, Units.ext_iff]
    rfl
  rw [e1]
  refine (IsUltrametricDist.isOpen_closedBall _ (zpow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero))).preimage ?_
  exact (Units.continuous_val.comp (continuous_cycZ F Ω l)).sub continuous_const

private theorem not_dvd_ker {H : Type} [Group H] (l : ℕ) [hl : Fact l.Prime] (φ : H →* (ZMod (l ^ 1))ˣ) :
    ¬ l ∣ φ.ker.index := by
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  intro h
  rw [Subgroup.index_ker] at h
  have h1 : l ∣ Nat.card (ZMod (l ^ 1))ˣ := h.trans (Subgroup.card_subgroup_dvd_card _)
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, pow_one, Nat.totient_prime hl.out] at h1
  have h2 := hl.out.two_le
  have := Nat.le_of_dvd (by omega) h1
  omega

private theorem rbar_iff {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (D : Raw Ω c) (g : G ℚ Ω) :
    D.rbar g = 1 ↔ ∀ i, Units.map (residue c.O).toMonoidHom (D.ps i g) = 1 := by
  have hr : D.rbar g = Matrix.diagonal fun i => residue c.O (D.ps i g : c.O) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [Raw.rbar, Raw.r0, diagRep]
    · simp [Raw.rbar, Raw.r0, diagRep, h]
  rw [hr, ← Matrix.diagonal_one, Matrix.diagonal_eq_diagonal_iff]
  exact forall_congr' fun i => by rw [Units.ext_iff]; rfl

theorem UpperTheory.V.Ws.residualKernel_properties :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ T : Tower D, T.Kr.Normal ∧ IsOpen (T.Kr : Set (G T.F Ω)) ∧ ¬ l ∣ T.Kr.index ∧ T.Kr ≤ (cycMod T.F Ω l 1).ker ∧ (∀ g ∈ T.Kr, D.rbar (resQ T.F g) = 1) ∧ (∀ w g, D.rbar (resQ T.F g) = 1 → T.rbU w g = 1) ∧ (prodS D ≠ 0 ∧ l ∣ prodS D) ∧ (∀ g ∈ ineOff T.F Ω (prodS D), g ∈ (T.fr ∅).N ∧ D.rbar (resQ T.F g) = 1) ∧ ∀ r, XRk l 1 (kerQ D T.F) r → XRk l 1 T.Kr r := by
  intro Ω _ _ _ l hl c D hD T
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, fo, -, fu⟩ := UpperTheory.V.GradeZeroInterpolatingElement.facts D hD
  obtain ⟨hN, hI, -⟩ := UpperTheory.V.X.spKer D
  obtain ⟨hE, -, -⟩ := galEmbTop ℚ T.F Ω
  obtain ⟨hDI, -, -, -⟩ := galEmbFam ℚ T.F Ω l
  have hfix : ∀ g : G T.F Ω, resQ T.F g ∈ T.F.fixingSubgroup := fun g => by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    exact fun x hx => g.commutes ⟨x, hx⟩
  have hK : T.Kr = D.rbar.ker.comap (resQ T.F) ⊓ (cycMod T.F Ω l 1).ker := by
    ext g
    exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hfix g, h.1⟩, h.2⟩⟩
  refine ⟨?_, ?_, ?_, hK ▸ inf_le_right, fun g hg => hg.1.2, fun w g hg => ?_,
    ⟨Finset.prod_ne_zero_iff.2 fun p hp => (hD.S_prime p hp).ne_zero, Finset.dvd_prod_of_mem _ hD.l_mem⟩, ?_, fun r hr => ?_⟩
  · rw [hK]
    infer_instance
  · rw [hK]
    exact (fo.preimage hE.continuous).inter (cyc_open T.F Ω l)
  · rw [hK, ← Subgroup.relIndex_mul_index inf_le_left, Subgroup.inf_relIndex_left]
    intro h
    rcases (Nat.Prime.dvd_mul hl.out).1 h with h2 | h2
    · exact not_dvd_ker l _ (h2.trans (Subgroup.relIndex_dvd_index_of_normal _ _))
    · rw [Subgroup.index_comap] at h2
      exact hI (h2.trans (Subgroup.relIndex_dvd_index_of_normal _ _))
  · have h := fun i => (rbar_iff D _).1 hg (lab T.pr i)
    show Units.map (residue c.O).toMonoidHom
      ((D.ps (lab T.pr 0) (resQ T.F g) * (D.ps (lab T.pr 1) (resQ T.F g))⁻¹) ^ w.1 *
        (D.ps (lab T.pr 0) (resQ T.F g) * (D.ps (lab T.pr 2) (resQ T.F g))⁻¹) ^ w.2) = 1
    simp only [map_mul, map_zpow, map_inv, h, inv_one, mul_one, one_zpow]
  · rintro g ⟨A, hA, hg⟩
    have hS : Raw.Away D.S A := fun p hp hv => hA (by
      obtain ⟨m, hm⟩ : p ∣ prodS D := Finset.dvd_prod_of_mem _ hp
      rw [hm, Nat.cast_mul, map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' ((A.valuation_le_one_iff _).2 (natCast_mem A m))) hv)
    have hg' : resQ T.F g ∈ Ine (F := ℚ) A := by
      rw [← (hDI A).2] at hg
      exact hg
    have h1 : D.rbar (resQ T.F g) = 1 := (rbar_iff D _).2 fun i => by
      rw [MonoidHom.mem_ker.1 (fu i A hS hg'), map_one]
    refine ⟨⟨A, fun p hp => ?_, hg, h1⟩, h1⟩
    have : p = l := by simpa using hp
    exact hS p (this ▸ hD.l_mem)
  · have hle : kerQ D T.F ≤ galOf ℚ T.F Ω := fun g hg x =>
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg.1.1 x.1 x.2
    obtain ⟨⟨ε, -, hε, -⟩, -⟩ := UpperTheory.V.Kum.xdualBase ℚ Ω T.F 1 (kerQ D T.F) (ZMod l) (ZMod l) hle
    have e := (ε.ofSubmodules _ _ hε).toEquiv
    exact CardLe.of_injective hr e.symm e.symm.injective
end
