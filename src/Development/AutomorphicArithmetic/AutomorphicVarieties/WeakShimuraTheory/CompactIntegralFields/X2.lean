module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.IneConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PullOnto
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.BdGlob

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.RankLocalCocycleSpacesLe
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocallyConstantOpenPreimage
theorem UpperTheory.Reformulated.B.LocallyConstantOpenPreimage.lc_of_open :
    ∀ {Γ A : Type} [inst : Group Γ] [inst_1 : TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [inst_3 : Group A] (ψ : Γ →* A), IsOpen (↑ψ.ker : Set Γ) → IsLocallyConstant (⇑ψ : Γ → A) := by
  intro Γ A _ _ _ _ ψ h
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (ψ.ker : Set Γ),
    h.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp [MonoidHom.mem_ker]
  · intro y hy
    have hk : ψ (x⁻¹ * y) = 1 := MonoidHom.mem_ker.mp hy
    rw [map_mul, map_inv] at hk
    exact (inv_mul_eq_one.mp hk).symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.CardLocalCocyclesLeOfPlaceAbovePrime
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

theorem UpperTheory.V.Ws.card_localCocycles_le_of_place_above_prime :
    LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Finite M], (∀ m : M, l • m = 0) → ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (ρ : Representation R (Dec (F := F) A) M), IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → (∀ m, IsLocallyConstant fun g => ρ g m) → CardLe (cocOff ρ ∅) (Nat.card M ^ (2 + locDeg v)) := by
  intro hF hT hE F Ω _ _ _ _ _ l _ R M _ _ _ _ hl A v ρ hA hv hρ
  obtain ⟨inst, ρ', hρ'⟩ := exists_zmod_prime_representation_of_torsion l (Dec (F := F) A) R M hl ρ
  letI : TopologicalSpace M := ⊥
  haveI : DiscreteTopology M := ⟨rfl⟩
  have hc : ReciprocityTheory.Gal.ContAction ρ' := by
    unfold ReciprocityTheory.Gal.ContAction
    rw [continuous_prod_of_discrete_right]
    intro m
    simp only [hρ']
    exact (hρ m).continuous
  obtain ⟨f1, h1⟩ := local_h1_finite_mod_l hF hT hE F Ω l M A v ρ' hA hc
  obtain ⟨fz, hz⟩ := cocycle_card_euler_formula _ _ M ρ' hc f1
  rw [if_pos hv] at h1
  have h0 : 0 < Nat.card (H0 ρ') := by
    haveI : Finite (H0 ρ') := Subtype.finite
    haveI : Nonempty (H0 ρ') := ⟨0⟩
    exact Nat.card_pos
  have hZ : CardLe (Z1 ρ') (Nat.card M ^ (2 + locDeg v)) := by
    refine ⟨fz, Nat.le_of_mul_le_mul_right ?_ h0⟩
    rw [hz]
    calc Nat.card (H1 ρ') * Nat.card M
        ≤ Nat.card (H0 ρ') * Nat.card M ^ (1 + locDeg v) * Nat.card M := Nat.mul_le_mul_right _ h1
      _ = Nat.card M ^ (2 + locDeg v) * Nat.card (H0 ρ') := by ring
  have hmem : ∀ z : cocOff ρ ∅, z.1 ∈ Z1 ρ' := fun z =>
    (mem_Z1_iff_cocycle ρ' _).2 ⟨z.2.1.continuous, fun g h => by rw [hρ']; exact z.2.2.1 g h⟩
  exact hZ.of_injective (fun z => ⟨z.1, hmem z⟩) fun a b h => Subtype.ext (congrArg (fun z : Z1 ρ' => z.1) h)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.TowerPl
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical Pointwise

theorem UpperTheory.V.Ws.exists_injective_places_above_l_of_tower :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), ∃ pl : T.ι → HeightOneSpectrum (𝓞 T.F), Function.Injective pl ∧ ∀ v, IsPlaceOver (T.pl v) (pl v) ∧ ((l : ℕ) : 𝓞 T.F) ∈ (pl v).asIdeal := by
  intro Ω _ _ _ l _ c D T
  haveI := T.nF
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic T.F Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) T.F
  haveI : IsAlgClosure T.F Ω := ⟨inferInstance, inferInstance⟩
  obtain ⟨_, hex, hne, _⟩ := UpperTheory.V.Kum.placeDict T.F Ω
  have hpl : ∀ v, ∃ w : HeightOneSpectrum (𝓞 T.F), IsPlaceOver (T.pl v) w :=
    fun v => hex _ (hne _ l (Fact.out : l.Prime).ne_zero (T.ovl v))
  choose pl hpl using hpl
  refine ⟨pl, ?_, fun v => ⟨hpl v, ?_⟩⟩
  · intro v w hvw
    have h1 := hpl v
    have h2 := hpl w
    rw [hvw] at h1
    obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver h1 h2
    obtain ⟨u, _, huniq⟩ := T.cover (T.pl w) (T.ovl w)
    have hv : v = u := by
      apply huniq v
      refine ⟨σ, fun x => ?_⟩
      rw [← hσ]
      exact ValuationSubring.smul_mem_pointwise_smul_iff
    have hw : w = u := by
      apply huniq w
      exact ⟨1, fun x => Iff.rfl⟩
    rw [hv, hw]
  · apply (hpl v (l : 𝓞 T.F)).1
    simpa using T.ovl v
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem lc_of_open {Γ A : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group A] (ψ : Γ →* A)
    (h : IsOpen (ψ.ker : Set Γ)) : IsLocallyConstant ψ :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOpenPreimage.lc_of_open ψ h

private def scalRep {k Γ : Type} [Field k] [Group Γ] (γ : Γ →* kˣ) : Representation k Γ k where
  toFun g := (γ g : k) • LinearMap.id
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [mul_comm]

theorem UpperTheory.V.Ws.rank_localCocycleSpaces_le :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (T : Tower D) (g : ℕ), (plDvd T.F (prodS D)).ncard ≤ g → Nat.card T.ι ≤ g ∧ ∀ w, Module.rank (ResidueField c.O) (∀ v, (T.fr ∅).Zloc (residue c.O) ((T.fr ∅).Gv v) w) ≤ T.d + (2 * g : ℕ) := by
  intro P Ω _ _ _ l hl c D hD T g hg
  haveI : IsAlgClosure T.F Ω :=
    ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) T.F⟩
  obtain ⟨pl, hinj, hpl⟩ := exists_injective_places_above_l_of_tower D T
  obtain ⟨-, hKo, -, -, hK1, hK2, ⟨h0, hlS⟩, -, -⟩ := residualKernel_properties D hD T
  have hfin : (plDvd T.F (prodS D)).Finite := by
    have hne : Ideal.span {((prodS D : ℕ) : 𝓞 T.F)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact Nat.cast_ne_zero.2 h0
    refine (Ideal.finite_factors hne).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  have hmem : ∀ v, pl v ∈ plDvd T.F (prodS D) := fun v => by
    obtain ⟨m, hm⟩ := hlS
    show ((prodS D : ℕ) : 𝓞 T.F) ∈ (pl v).asIdeal
    rw [hm, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (hpl v).2
  have hcard : Nat.card T.ι ≤ g := by
    haveI := hfin.to_subtype
    refine le_trans ?_ hg
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_le_card_of_injective (fun v => (⟨pl v, hmem v⟩ : plDvd T.F (prodS D)))
      fun a b h => hinj (congrArg Subtype.val h)
  refine ⟨hcard, fun w => ?_⟩
  have hl0 : ((l : ℕ) : ResidueField c.O) = 0 := by
    obtain ⟨-, -, -, -, -, h0, -, hval, -⟩ := dvrFacts l c.O
    rw [hval, Ne, IsDiscreteValuationRing.addVal_eq_zero_iff] at h0
    rw [← map_natCast (residue c.O), residue_eq_zero_iff]
    exact h0
  haveI : Finite (ResidueField c.O) := (UpperTheory.V.abelian₂.dvr_finite l c.O).2.1
  have hlc : IsLocallyConstant (T.rbU w) :=
    lc_of_open _ (Subgroup.isOpen_mono (fun x hx => hK2 w x (hK1 x hx)) hKo)
  have hv : ∀ v : T.ι, CardLe ((T.fr ∅).Zloc (residue c.O) ((T.fr ∅).Gv v) w)
      (Nat.card (ResidueField c.O) ^ (2 + locDeg (pl v))) := fun v => by
    have h := card_localCocycles_le_of_place_above_prime P.loc.lf P.loc.lt P.loc.le T.F Ω l (ResidueField c.O) (ResidueField c.O)
      (fun m => by rw [nsmul_eq_mul, hl0, zero_mul]) (T.pl v) (pl v)
      (scalRep ((T.rbU w).comp (Dec (F := T.F) (T.pl v)).subtype)) (hpl v).1 (hpl v).2
      (fun m => (hlc.comp_continuous continuous_subtype_val).comp fun u => (u : ResidueField c.O) • m)
    exact h.of_injective (fun z => ⟨z.1, z.2.1, z.2.2, fun _ h => h.elim⟩)
      fun a b h => Subtype.ext (Subtype.mk.inj h)
  haveI : Fintype T.ι := Fintype.ofFinite _
  haveI : Finite (T.fr ∅).ι := T.fin
  have hsum : ∑ v : T.ι, (2 + locDeg (pl v)) ≤ T.d + 2 * g := by
    have h1 := sum_local_degree_above_l_le_finrank T.F l (Finset.univ.map ⟨pl, hinj⟩)
    rw [Finset.sum_map] at h1
    simp only [Function.Embedding.coeFn_mk, (hpl _).2, if_true] at h1
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, smul_eq_mul]
    have : T.d = Module.finrank ℚ T.F := rfl
    omega
  have hC : CardLe (∀ v : T.ι, (T.fr ∅).Zloc (residue c.O) ((T.fr ∅).Gv v) w)
      (Nat.card (ResidueField c.O) ^ (T.d + 2 * g)) := by
    haveI := fun v => (hv v).1
    refine ⟨inferInstance, ?_⟩
    rw [Nat.card_pi]
    refine (Finset.prod_le_prod' fun v _ => (hv v).2).trans ?_
    rw [Finset.prod_pow_eq_pow_sum]
    exact Nat.pow_le_pow_right Nat.card_pos hsum
  have := rank_le_of_card_le_pow_card_field (ResidueField c.O) _ _ hC
  rw [Nat.cast_add] at this
  exact this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.KerQFacts
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem mem_princ_of_pow {l : ℕ} [Fact l.Prime] {u : ℤ_[l]ˣ} (hu : u ∈ KStar.TotallyRealRoots.princ l 1) {n : ℕ}
    (h : u ^ (l - 1) ∈ KStar.TotallyRealRoots.princ l n) : u ∈ KStar.TotallyRealRoots.princ l n := by
  have hl : l.Prime := Fact.out
  rw [KStar.TotallyRealRoots.mem_princ] at hu h ⊢
  rw [Units.val_pow_eq_pow_val] at h
  set x : ℤ_[l] := (u : ℤ_[l]) with hx
  set S : ℤ_[l] := ∑ i ∈ Finset.range (l - 1), x ^ i with hSdef
  have hgeom : x ^ (l - 1) - 1 = (x - 1) * S := by
    rw [hSdef, mul_comm, geom_sum_mul]
  have hl1 : (l : ℤ_[l]) ∣ x - 1 := by simpa using hu
  have hdiff : (l : ℤ_[l]) ∣ ∑ i ∈ Finset.range (l - 1), (x ^ i - 1) :=
    Finset.dvd_sum fun i _ => dvd_trans hl1 (by simpa [one_pow] using sub_dvd_pow_sub_pow x 1 i)
  have hSeq : S = ∑ i ∈ Finset.range (l - 1), (x ^ i - 1) + ((l : ℤ_[l]) - 1) := by
    rw [Finset.sum_sub_distrib, hSdef]
    simp [Nat.cast_sub hl.one_le]
  have hlnu : ¬IsUnit (l : ℤ_[l]) := by
    rw [PadicInt.not_isUnit_iff, PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.one_lt)
  have hS : IsUnit S := by
    by_contra hne
    rw [PadicInt.not_isUnit_iff, PadicInt.norm_lt_one_iff_dvd] at hne
    apply hlnu
    apply isUnit_of_dvd_one
    have h2 := dvd_sub (dvd_add hdiff (dvd_refl (l : ℤ_[l]))) hne
    convert h2 using 1
    rw [hSeq]
    ring
  rw [hgeom] at h
  exact hS.dvd_mul_right.mp h

private theorem comm_le_ker {Γ M : Type} [Group Γ] [Monoid M] (f : Γ →* M) (hf : ∀ a b, f (a * b) = f (b * a)) :
    commutator Γ ≤ f.ker := by
  rw [commutator, Subgroup.commutator_le]
  intro a _ b _
  rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, ← map_mul f a b, hf a b,
    map_mul, mul_assoc (f b), ← map_mul f a a⁻¹, mul_inv_cancel, map_one, mul_one, ← map_mul,
    mul_inv_cancel, map_one]

theorem UpperTheory.V.Ws.kerOverRationals_open_commutator_layer :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (F : IntermediateField ℚ Ω) [NumberField F] [IsAbelianGalois ℚ F], IsOpen (kerQ D F : Set (G ℚ Ω)) ∧ commutator (G ℚ Ω) ≤ kerQ D F ∧ ∀ (m : ℕ) (F' : IntermediateField ℚ Ω), IsLayer l m F F' → kerQ D F' = levU l (kerQ D F) (m + 1) ∧ cycU l (kerQ D F) ≤ F'.fixingSubgroup := by
  intro Ω _ _ _ l _ c D hD F hnf hab
  haveI := hnf
  haveI := hab
  have hnorm : Normal ℚ F := by
    haveI : IsGalois ℚ F := IsAbelianGalois.toIsGalois
    exact IsGalois.to_normal
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hrb, -, -⟩ := UpperTheory.V.GradeZeroInterpolatingElement.facts D hD
  have hcm : (cycMod ℚ Ω l 1).ker = Subgroup.comap (cycZ ℚ Ω l) (KStar.TotallyRealRoots.princ l 1) := rfl
  have key : ∀ g, g ∈ (cycMod ℚ Ω l 1).ker ↔ cycZ ℚ Ω l g ∈ KStar.TotallyRealRoots.princ l 1 := fun g => by
    rw [hcm]
    rfl
  have hdiag : ∀ g, D.rbar g = Matrix.diagonal fun i => IsLocalRing.residue c.O ((D.ps i g : (c.O)ˣ) : c.O) := by
    intro g
    ext i j
    simp [Raw.rbar, Raw.r0, UpperTheory.V.GradeZeroInterpolatingElement.mapRep, UpperTheory.V.GradeZeroInterpolatingElement.diagRep, Matrix.diagonal_apply]
    split_ifs <;> simp
  have hrc : ∀ a b, D.rbar (a * b) = D.rbar (b * a) := by
    intro a b
    rw [map_mul, map_mul, hdiag, hdiag, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  refine ⟨?_, ?_, ?_⟩
  · show IsOpen ((F.fixingSubgroup ⊓ D.rbar.ker ⊓ (cycMod ℚ Ω l 1).ker : Subgroup (G ℚ Ω)) : Set (G ℚ Ω))
    rw [Subgroup.coe_inf, Subgroup.coe_inf, hcm, Subgroup.coe_comap]
    exact (F.fixingSubgroup_isOpen.inter hrb).inter
      ((KStar.TotallyRealRoots.isOpen_princ 1).preimage (continuous_cycZ ℚ Ω l))
  · refine le_inf (le_inf ?_ ?_) ?_
    · rw [← @IntermediateField.restrictNormalHom_ker _ _ _ _ _ F hnorm]
      exact comm_le_ker _ fun a b => by
        rw [map_mul, map_mul]
        exact (IsMulCommutative.is_comm (M := Gal(F/ℚ))).comm _ _
    · exact comm_le_ker _ hrc
    · exact comm_le_ker _ fun a b => by rw [map_mul, map_mul, mul_comm]
  · intro m F' hL
    constructor
    · ext g
      simp only [kerQ, levU, Subgroup.mem_inf, Subgroup.mem_comap, key, hL g]
      constructor
      · rintro ⟨⟨⟨hF, hp⟩, hr⟩, h1⟩
        exact ⟨⟨⟨hF, hr⟩, h1⟩, mem_princ_of_pow h1 hp⟩
      · rintro ⟨⟨⟨hF, hr⟩, h1⟩, hn⟩
        exact ⟨⟨⟨hF, Subgroup.pow_mem _ hn _⟩, hr⟩, h1⟩
    · intro g hg
      simp only [cycU, kerQ, Subgroup.mem_inf, MonoidHom.mem_ker] at hg
      rw [hL g]
      refine ⟨hg.1.1.1, ?_⟩
      rw [hg.2, one_pow]
      exact one_mem _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.BoundsExt
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.BaseCh
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem rank_span_range_le_of_linearForm_comp_mem {X k₀ k : Type} [Field k₀] [Field k] [Algebra k₀ k]
    (W₀ : Submodule k₀ (X → k₀)) (n : ℕ) (hW₀ : Module.rank k₀ W₀ ≤ n) (z : X → k)
    (hz : ∀ φ : k →ₗ[k₀] k₀, (fun x => φ (z x)) ∈ W₀) :
    Module.rank k₀ (Submodule.span k₀ (Set.range z)) ≤ n := by
  apply rank_le
  intro s hs
  have hy : LinearIndependent k₀ (fun i : s => (((i : Submodule.span k₀ (Set.range z))) : k)) :=
    hs.map' (Submodule.span k₀ (Set.range z)).subtype (Submodule.ker_subtype _)
  have hφ : ∀ j : s, ∃ φ : k →ₗ[k₀] k₀, ∀ i : s,
      φ (((i : Submodule.span k₀ (Set.range z))) : k) = if i = j then 1 else 0 := by
    intro j
    obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Module.Basis.span hy).coord j)
    refine ⟨g, fun i => ?_⟩
    have h1 := LinearMap.congr_fun hg (Module.Basis.span hy i)
    rw [Module.Basis.span_apply] at h1
    rw [LinearMap.comp_apply, Submodule.subtype_apply] at h1
    rw [h1, ← Module.Basis.span_apply hy i, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_apply]
  choose φ hφ using hφ
  have hw : LinearIndependent k₀ (fun j : s => (⟨fun x => φ j (z x), hz (φ j)⟩ : W₀)) := by
    rw [linearIndependent_iff']
    intro t c hc j hj
    have hψz : ∀ x, (∑ i ∈ t, c i • φ i) (z x) = 0 := by
      intro x
      have := congrArg (fun v : W₀ => (v : X → k₀) x) hc
      simpa [LinearMap.sum_apply, Finset.sum_apply] using this
    have hψL : Submodule.span k₀ (Set.range z) ≤ LinearMap.ker (∑ i ∈ t, c i • φ i) := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      exact hψz x
    have h2 := hψL (j : Submodule.span k₀ (Set.range z)).2
    rw [LinearMap.mem_ker, LinearMap.sum_apply] at h2
    simp only [LinearMap.smul_apply, hφ, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, hj, ite_true] at h2
    exact h2
  have hc := hw.cardinal_le_rank
  rw [Cardinal.mk_coe_finset] at hc
  exact_mod_cast hc.trans hW₀

private theorem mem_span_image_algebraMap_of_linearForm_comp_mem {X k₀ k : Type} [Field k₀] [Field k] [Algebra k₀ k]
    (W₀ : Submodule k₀ (X → k₀)) (n : ℕ) (hW₀ : Module.rank k₀ W₀ ≤ n) (z : X → k)
    (hz : ∀ φ : k →ₗ[k₀] k₀, (fun x => φ (z x)) ∈ W₀) :
    z ∈ Submodule.span k ((fun w : X → k₀ => fun x => algebraMap k₀ k (w x)) '' (W₀ : Set (X → k₀))) := by
  have hr := rank_span_range_le_of_linearForm_comp_mem W₀ n hW₀ z hz
  haveI : Module.Finite k₀ (Submodule.span k₀ (Set.range z)) :=
    Module.rank_lt_aleph0_iff.1 (hr.trans_lt Cardinal.natCast_lt_aleph0)
  set L := Submodule.span k₀ (Set.range z)
  let e := Module.finBasis k₀ L
  have hext : ∀ j, ∃ φ : k →ₗ[k₀] k₀, φ ∘ₗ L.subtype = e.coord j :=
    fun j => LinearMap.exists_extend (e.coord j)
  choose φ hφ using hext
  have hzx : ∀ x, z x = ∑ j, φ j (z x) • ((e j : L) : k) := by
    intro x
    have hx : z x ∈ L := Submodule.subset_span ⟨x, rfl⟩
    have h1 := congrArg L.subtype (e.sum_repr ⟨z x, hx⟩)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h1
    show L.subtype ⟨z x, hx⟩ = _
    rw [← h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, Submodule.subtype_apply]
    congr 1
    have := LinearMap.congr_fun (hφ j) ⟨z x, hx⟩
    rw [LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.coord_apply] at this
    exact this.symm
  have hzeq : z = ∑ j, ((e j : L) : k) • (fun x => algebraMap k₀ k (φ j (z x))) := by
    funext x
    rw [hzx x, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, Algebra.smul_def, mul_comm]
  rw [hzeq]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨_, hz (φ j), rfl⟩

theorem UpperTheory.V.Ws.rank_le_of_linearForm_comp_mem_of_rank_le :
    ∀ (X k₀ k : Type) [Field k₀] [Field k] [Algebra k₀ k] (W₀ : Submodule k₀ (X → k₀)) (W : Submodule k (X → k)) (n : ℕ), Module.rank k₀ W₀ ≤ n → (∀ z ∈ W, ∀ φ : k →ₗ[k₀] k₀, (fun x => φ (z x)) ∈ W₀) → Module.rank k W ≤ n := by
  intro X k₀ k _ _ _ W₀ W n hW₀ hW
  have hWS : W ≤ Submodule.span k
      ((fun w : X → k₀ => fun x => algebraMap k₀ k (w x)) '' (W₀ : Set (X → k₀))) :=
    fun z hz => mem_span_image_algebraMap_of_linearForm_comp_mem W₀ n hW₀ z (hW z hz)
  let A : (X → k₀) →ₗ[k₀] (X → k) :=
    LinearMap.pi fun x => (Algebra.linearMap k₀ k).comp (LinearMap.proj x)
  let b := Module.Free.chooseBasis k₀ W₀
  have hsub : Submodule.span k
      ((fun w : X → k₀ => fun x => algebraMap k₀ k (w x)) '' (W₀ : Set (X → k₀))) ≤
      Submodule.span k (Set.range fun i => A (b i : X → k₀)) := by
    rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    have h1 : A w ∈ Submodule.map (A ∘ₗ W₀.subtype) ⊤ := ⟨⟨w, hw⟩, trivial, rfl⟩
    rw [← b.span_eq, Submodule.map_span, ← Set.range_comp] at h1
    exact Submodule.span_le_restrictScalars k₀ k _ h1
  calc Module.rank k W
      ≤ Module.rank k (Submodule.span k
          ((fun w : X → k₀ => fun x => algebraMap k₀ k (w x)) '' (W₀ : Set (X → k₀)))) :=
        Submodule.rank_mono hWS
    _ ≤ Module.rank k (Submodule.span k (Set.range fun i => A (b i : X → k₀))) :=
        Submodule.rank_mono hsub
    _ ≤ Cardinal.mk (Set.range fun i => A (b i : X → k₀)) := rank_span_le _
    _ ≤ Cardinal.mk (Module.Free.ChooseBasisIndex k₀ W₀) := Cardinal.mk_range_le
    _ = Module.rank k₀ W₀ := (Module.Free.rank_eq_card_chooseBasisIndex k₀ W₀).symm
    _ ≤ n := hW₀
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private def sigSub {ι R : Type} {X : ι → Type} [CommRing R] (p : ∀ v, Submodule R (X v → R)) :
    Submodule R ((Σ v, X v) → R) where
  carrier := {z | ∀ v, (fun s => z ⟨v, s⟩) ∈ p v}
  add_mem' ha hb v := (p v).add_mem (ha v) (hb v)
  zero_mem' v := (p v).zero_mem
  smul_mem' c _ ha v := (p v).smul_mem c (ha v)

private def sigEquiv {ι R : Type} {X : ι → Type} [CommRing R] (p : ∀ v, Submodule R (X v → R)) :
    (∀ v, p v) ≃ₗ[R] sigSub p where
  toFun f := ⟨fun x => (f x.1).1 x.2, fun v => (f v).2⟩
  invFun z v := ⟨fun s => z.1 ⟨v, s⟩, z.2 v⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

private theorem phi_mul {k₀ k : Type} [Field k₀] [Field k] [Algebra k₀ k] (φ : k →ₗ[k₀] k₀) (x : k₀) (y : k) :
    φ (algebraMap k₀ k x * y) = x * φ y := by
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

private theorem zgl_phi {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] (Φ : Fr O Γ) {k₀ k : Type} [Field k₀]
    [Field k] [Algebra k₀ k] (a₀ : O →+* k₀) (w : ℤ × ℤ) (z : Γ → k) (hz : z ∈ Φ.Zgl ((algebraMap k₀ k).comp a₀) w)
    (φ : k →ₗ[k₀] k₀) : (fun x => φ (z x)) ∈ Φ.Zgl a₀ w := by
  obtain ⟨h1, h2, h3, h4⟩ := hz
  refine ⟨h1.comp φ, fun g h => ?_, fun g h => ?_, fun h => ?_⟩
  · show φ (z (g * h)) = φ (z g) + _ * φ (z h)
    rw [h2, map_add (f := _), RingHom.comp_apply, phi_mul]
  · show φ (z g) = 0
    rw [h3 g h, map_zero]
  · show φ (z Φ.g0) = 0
    rw [h4 h, map_zero]

theorem UpperTheory.V.Ws.cocycleBounds_of_ringHom_comp :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] (Φ : Fr O Γ) (k₀ k : Type) [Field k₀] [Field k] (a₀ : O →+* k₀) (j : k₀ →+* k) (d C : ℕ), Φ.Bounds a₀ d C → Φ.Bounds (j.comp a₀) d C := by
  intro O Γ _ _ _ Φ k₀ k _ _ a₀ j d C hB
  letI : Algebra k₀ k := j.toAlgebra
  change Φ.Bounds ((algebraMap k₀ k).comp a₀) d C
  refine ⟨hB.card, fun w hw => ?_, fun w hw => ?_, fun w hw => ?_, fun w hw => ?_⟩
  · refine rank_le_of_linearForm_comp_mem_of_rank_le Γ k₀ k _ _ C (hB.str w hw) ?_
    rintro z ⟨hz, n, hn⟩ φ
    refine ⟨zgl_phi Φ a₀ w z hz φ, fun v => φ (n v), fun v s hs => ?_⟩
    show φ (z s) = φ (n v) - _ * φ (n v)
    rw [hn v s hs, map_sub, RingHom.comp_apply, phi_mul]
  · exact rank_le_of_linearForm_comp_mem_of_rank_le Γ k₀ k _ _ C (hB.even w hw) fun z hz φ => zgl_phi Φ a₀ w z hz φ
  · have := rank_le_of_linearForm_comp_mem_of_rank_le Γ k₀ k _ _ (d + C) (by exact_mod_cast hB.odd w hw) fun z hz φ => zgl_phi Φ a₀ w z hz φ
    exact_mod_cast this
  · have h0 := hB.loc w hw
    rw [(sigEquiv _).rank_eq] at h0 ⊢
    have := rank_le_of_linearForm_comp_mem_of_rank_le _ k₀ k _ (sigSub fun v => Φ.Zloc ((algebraMap k₀ k).comp a₀) (Φ.Gv v) w) (d + C)
      (by exact_mod_cast h0) (by
        intro z hz φ v
        obtain ⟨h1, h2⟩ := hz v
        refine ⟨h1.comp φ, fun g h => ?_⟩
        have h3 := congrArg φ (h2 g h)
        rw [map_add (f := _), RingHom.comp_apply, phi_mul] at h3
        exact h3)
    exact_mod_cast this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.ExistsIwasawaRankBoundOfFerreroWashington
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem cardLe_map_of_cardLe {R M N : Type} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (f : M →ₗ[R] N) (S : Submodule R M) (n : ℕ) (h : CardLe S n) : CardLe (S.map f) n := by
  obtain ⟨hfin, hcard⟩ := h
  have hsurj : Function.Surjective
      (fun x : S => (⟨f x, Submodule.mem_map_of_mem x.2⟩ : S.map f)) := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
    exact ⟨⟨x, hx⟩, rfl⟩
  exact ⟨Finite.of_surjective _ hsurj, (Nat.card_le_card_of_surjective _ hsurj).trans hcard⟩

theorem UpperTheory.V.Ws.exists_iwasawaRank_bound_of_ferreroWashington :
    UpperTheory.V.Published.FerreroWashington → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (U : Subgroup (G ℚ Ω)), l ≠ 2 → IsOpen (U : Set (G ℚ Ω)) → commutator (G ℚ Ω) ≤ U → U ≤ (cycMod ℚ Ω l 1).ker → ∃ r : ℕ, ∀ n : ℕ, XRk l 1 (levU l U n) r := by
  intro hFW Ω _ _ _ l _ U hl2 hUo hc hUcyc
  have hl : l.Prime := Fact.out
  have hUc : IsClosed (U : Set (G ℚ Ω)) := Subgroup.isClosed_of_isOpen U hUo
  set K : IntermediateField ℚ Ω := IntermediateField.fixedField U
  have hUK : K.fixingSubgroup = U := InfiniteGalois.fixingSubgroup_fixedField ⟨U, hUc⟩
  haveI : FiniteDimensional ℚ K := (InfiniteGalois.isOpen_iff_finite K).1 (by rw [hUK]; exact hUo)
  haveI : NumberField K := ⟨⟩
  have hgal : galOf ℚ K Ω = U := by
    rw [← hUK]
    ext σ
    simp [UpperTheory.V.Base.galOf, IntermediateField.mem_fixingSubgroup_iff]
  have hnorm : U.Normal := by
    constructor
    intro h hh g
    have hcm : g * h * g⁻¹ * h⁻¹ ∈ U :=
      hc (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top h))
    have : g * h * g⁻¹ = (g * h * g⁻¹ * h⁻¹) * h := by group
    rw [this]
    exact U.mul_mem hcm hh
  haveI : IsGalois ℚ K := (InfiniteGalois.normal_iff_isGalois K).1 (by rw [hUK]; exact hnorm)
  haveI : IsMulCommutative Gal(K/ℚ) := by
    constructor
    constructor
    intro a b
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := K) Ω a
    obtain ⟨τ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := K) Ω b
    have hmem : σ * τ * σ⁻¹ * τ⁻¹ ∈ (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Ω) K).ker := by
      erw [IntermediateField.restrictNormalHom_ker K]
      rw [hUK]
      exact hc (Subgroup.commutator_mem_commutator (Subgroup.mem_top σ) (Subgroup.mem_top τ))
    rw [MonoidHom.mem_ker] at hmem
    simp only [map_mul, map_inv] at hmem
    have h1 := congrArg (· * (AlgEquiv.restrictNormalHom K τ) * (AlgEquiv.restrictNormalHom K σ)) hmem
    simp only [one_mul, inv_mul_cancel_right] at h1
    exact h1
  haveI : IsAbelianGalois ℚ K := ⟨⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : ∀ i : ℕ, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => by
    haveI : NeZero (l ^ i) := ⟨pow_ne_zero _ hl.ne_zero⟩
    infer_instance
  have hchar : ∀ σ : G ℚ Ω, cycMod ℚ Ω l 1 σ = 1 → galChar Ω (l ^ 1) σ = 1 := by
    intro σ h
    unfold ReciprocityTheory.Gal.cycMod ReciprocityTheory.Gal.cycZ at h
    unfold UpperTheory.V.Two.galChar
    rw [Units.ext_iff] at h ⊢
    simp only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe] at h
    erw [cyclotomicCharacter.toZModPow] at h
    exact h
  have hμ : ∃ ζ : K, IsPrimitiveRoot ζ (if l = 2 then 4 else l) := by
    rw [if_neg hl2]
    have := (muIff Ω K (l ^ 1)).2 (by
      rw [hgal]
      intro σ hσ
      exact hchar σ (hUcyc hσ))
    simpa only [pow_one] using this
  obtain ⟨r, hr⟩ := hFW l K hμ
  refine ⟨r, fun n => ?_⟩
  obtain ⟨hcyc, -, -⟩ := UpperTheory.V.Kum.fnCyc K Ω l n
  set K' := UpperTheory.V.Kum.Fn K Ω l n
  haveI : FiniteDimensional K K' := IsCyclotomicExtension.finiteDimensional {l ^ n} K K'
  haveI : FiniteDimensional ℚ K' := Module.Finite.trans K K'
  haveI : NumberField K' := ⟨⟩
  have hcl := hr n K'
  have hgo := UpperTheory.V.Kum.galOfCyc ℚ Ω l n K K'
  rw [hgal] at hgo
  have h2 : ∀ m : ZMod l, 2 • m = 0 → m = 0 := by
    intro m hm
    have h2ne : (2 : ZMod l) ≠ 0 := by
      intro h0
      have : ((2 : ℕ) : ZMod l) = 0 := by exact_mod_cast h0
      rw [ZMod.natCast_eq_zero_iff] at this
      exact hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 this)
    rw [nsmul_eq_mul, Nat.cast_ofNat] at hm
    exact (mul_eq_zero.1 hm).resolve_left h2ne
  have hpull := UpperTheory.V.Kum.pullOnto ℚ Ω K' (levU l U n) hgo.ge 1 (ZMod l) (ZMod l) one_ne_zero hgo.le (Or.inr h2)
  show CardLe (UpperTheory.V.Kum.XDual 1 (levU l U n) (ZMod l) (ZMod l)) (l ^ r)
  rw [← hpull]
  apply cardLe_map_of_cardLe
  have cardLe_dual_zmod_card (l : ℕ) [Fact l.Prime] (V : Type) [AddCommGroup V] [Module (ZMod l) V]
      [Finite V] : CardLe (V →ₗ[ZMod l] ZMod l) (Nat.card V) := by
    refine ⟨Finite.of_injective (fun f : V →ₗ[ZMod l] ZMod l => (f : V → ZMod l)) DFunLike.coe_injective, ?_⟩
    show Nat.card (Module.Dual (ZMod l) V) ≤ _
    rw [Nat.card_congr (LinearEquiv.ofFinrankEq _ _ Subspace.dual_finrank_eq).toEquiv]

  have cardLe_hom (A : Type) [CommGroup A] [Finite A] (l : ℕ) [Fact l.Prime] (P : Type) (θ : P → A → ZMod l)
      (hθ : Function.Injective θ) (hm : ∀ p a b, θ p (a * b) = θ p a + θ p b) :
      CardLe P (Nat.card (A ⧸ (powMonoidHom l : A →* A).range)) := by
    have hpow : ∀ p (c : A) (n : ℕ), θ p (c ^ n) = n • θ p c := by
      intro p c n
      induction n with
      | zero =>
        have h := hm p 1 1
        rw [mul_one] at h
        simpa using h
      | succ n ih => rw [pow_succ, hm, ih, succ_nsmul]
    have h1 : ∀ p, θ p 1 = 0 := fun p => by simpa using hpow p 1 0
    have hV : ∀ v : Additive (A ⧸ (powMonoidHom l : A →* A).range), l • v = 0 := by
      intro v
      change (Additive.toMul v : A ⧸ (powMonoidHom l : A →* A).range) ^ l = 1
      obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
      rw [← ha, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact ⟨a, rfl⟩
    let φ : P → A →* Multiplicative (ZMod l) := fun p =>
      { toFun := fun a => Multiplicative.ofAdd (θ p a)
        map_one' := by
          show Multiplicative.ofAdd (θ p 1) = 1
          rw [h1]
          rfl
        map_mul' := fun a b => by
          show Multiplicative.ofAdd (θ p (a * b)) = _
          rw [hm]
          rfl }
    let ψ : P → (A ⧸ (powMonoidHom l : A →* A).range) →* Multiplicative (ZMod l) := fun p =>
      QuotientGroup.lift _ (φ p) (by
        rintro _ ⟨c, rfl⟩
        show Multiplicative.ofAdd (θ p (c ^ l)) = 1
        rw [hpow, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
        rfl)
    let Φ : P → (Additive (A ⧸ (powMonoidHom l : A →* A).range) →+ ZMod l) := fun p =>
      AddMonoidHom.mk' (fun v => Multiplicative.toAdd (ψ p (Additive.toMul v))) (fun u v => by
        show Multiplicative.toAdd (ψ p (Additive.toMul u * Additive.toMul v)) = _
        rw [map_mul]
        rfl)
    have hΦ : ∀ p (a : A), Φ p (Additive.ofMul (QuotientGroup.mk a)) = θ p a := fun p a => rfl
    have hinj : Function.Injective Φ := by
      intro p q h
      apply hθ
      funext a
      rw [← hΦ p a, ← hΦ q a, h]
    letI : Module (ZMod l) (Additive (A ⧸ (powMonoidHom l : A →* A).range)) := AddCommGroup.zmodModule hV
    exact CardLe.of_injective (cardLe_dual_zmod_card l (Additive (A ⧸ (powMonoidHom l : A →* A).range))) _
      ((AddMonoidHom.toZModLinearMap_injective l (M := Additive (A ⧸ (powMonoidHom l : A →* A).range))
        (M₁ := ZMod l)).comp hinj)
  have hcard : CardLe (UpperTheory.V.Kum.ClDual K' 1 (ZMod l) (ZMod l))
      (Nat.card (ClassGroup (𝓞 K') ⧸ (powMonoidHom l : ClassGroup (𝓞 K') →* ClassGroup (𝓞 K')).range)) := by
    exact cardLe_hom (ClassGroup (𝓞 K')) l _ (fun θ => θ.1) Subtype.val_injective fun θ => θ.2.1
  obtain ⟨hf, hle⟩ := hcard
  exact ⟨hf, hle.trans hcl⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.PlacesBd
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.DecIdx
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.ClosedInf
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem addClosed_index (l : ℕ) [Fact l.Prime] (A : AddSubgroup ℤ_[l])
    (hA : IsClosed (A : Set ℤ_[l])) (a : ℤ_[l]) (ha : a ∈ A) (h0 : a ≠ 0) : A.index ≠ 0 := by
  have key : ∀ x : ℤ_[l], a * x ∈ A := by
    intro x
    refine PadicInt.denseRange_intCast.induction_on x ?_ ?_
    · exact hA.preimage (continuous_const.mul continuous_id)
    · intro m
      have hm : a * (m : ℤ_[l]) = m • a := by rw [zsmul_eq_mul, mul_comm]
      rw [hm]
      exact A.zsmul_mem ha m
  have hspec := PadicInt.unitCoeff_spec h0
  set w := PadicInt.unitCoeff h0
  set n := a.valuation
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  let f := (PadicInt.toZModPow (p := l) n).toAddMonoidHom
  have hle : f.ker ≤ A := by
    intro x hx
    have hx' : x ∈ RingHom.ker (PadicInt.toZModPow (p := l) n) := hx
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hx'
    obtain ⟨y, rfl⟩ := hx'
    have hw : (w : ℤ_[l]) * ↑w⁻¹ = 1 := Units.mul_inv w
    have heq : (l : ℤ_[l]) ^ n * y = a * (↑w⁻¹ * y) := by
      conv_rhs => rw [hspec]
      linear_combination (-((l : ℤ_[l]) ^ n * y)) * hw
    rw [heq]
    exact key _
  have hfin : f.ker.index ≠ 0 := by
    rw [AddSubgroup.index_ker]
    exact Nat.card_ne_zero.2 ⟨inferInstance, inferInstance⟩
  intro hA0
  apply hfin
  exact Nat.eq_zero_of_zero_dvd (hA0 ▸ AddSubgroup.index_dvd_of_le hle)

open GroundTheory.Global.Cyclotomic in
theorem UpperTheory.V.Ws.index_ne_zero_of_isClosed_of_not_isOfFinOrder :
    ∀ (l : ℕ) [Fact l.Prime] (H : Subgroup ℤ_[l]ˣ), IsClosed (H : Set ℤ_[l]ˣ) → (∃ u ∈ H, ¬ IsOfFinOrder u) → H.index ≠ 0 := by
  intro l _ H hH hu
  obtain ⟨u, huH, hu⟩ := hu
  set L := padicUnitsLog l with hL
  have hB : IsClosed ((H.map L : Subgroup (Multiplicative ℤ_[l])) : Set (Multiplicative ℤ_[l])) := by
    rw [Subgroup.coe_map]
    exact ((hH.isCompact).image (continuous_padicUnitsLog l)).isClosed
  let A : AddSubgroup ℤ_[l] := Subgroup.toAddSubgroup' (H.map L)
  have hAc : IsClosed (A : Set ℤ_[l]) := hB
  have haA : Multiplicative.toAdd (L u) ∈ A := by
    rw [Subgroup.mem_toAddSubgroup']
    exact ⟨u, huH, rfl⟩
  have ha0 : Multiplicative.toAdd (L u) ≠ 0 := by
    intro h
    apply hu
    have h1 : L u = 1 := by
      rw [← ofAdd_toAdd (L u), h]
      rfl
    rw [hL, padicUnitsLog_eq_one_iff] at h1
    exact isOfFinOrder_iff_pow_eq_one.2 ⟨_, torsionExponent_pos l, h1⟩
  have hAi : A.index ≠ 0 := addClosed_index l A hAc _ haA ha0
  have hMi : (H.map L).index ≠ 0 := hAi
  have hK : (H ⊔ L.ker).index ≠ 0 := by
    rw [← Subgroup.comap_map_eq, Subgroup.index_comap_of_surjective _ (padicUnitsLog_surjective l)]
    exact hMi
  have hker : L.ker ≤ rootsOfUnity (torsionExponent l) ℤ_[l] := by
    intro x hx
    rw [mem_rootsOfUnity]
    rw [MonoidHom.mem_ker, hL, padicUnitsLog_eq_one_iff] at hx
    exact hx
  have hcard : Nat.card L.ker ≠ 0 := by
    haveI : NeZero (torsionExponent l) := ⟨(torsionExponent_pos l).ne'⟩
    haveI : Finite L.ker := Finite.of_injective (Subgroup.inclusion hker) (Subgroup.inclusion_injective hker)
    exact Nat.card_ne_zero.2 ⟨inferInstance, inferInstance⟩
  have hrel : H.relIndex (H ⊔ L.ker) ≠ 0 := by
    rw [sup_comm, Subgroup.relIndex_sup_right]
    intro h0
    apply hcard
    exact Nat.eq_zero_of_zero_dvd (h0 ▸ Subgroup.relIndex_dvd_card H L.ker)
  rw [← Subgroup.relIndex_mul_index (le_sup_left : H ≤ H ⊔ L.ker)]
  exact mul_ne_zero hrel hK
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

theorem UpperTheory.V.Ws.index_cyclotomicKer_sup_decompositionGroup_ne_zero :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (p : ℕ) (A : ValuationSubring Ω), p.Prime → A.valuation (p : Ω) < 1 → ((cycZ ℚ Ω l).ker ⊔ Dec (F := ℚ) A).index ≠ 0 := by
  intro Ω _ _ _ l _ p A hp hA
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have hg : ∃ g ∈ Dec (F := ℚ) A, ¬ IsOfFinOrder (cycZ ℚ Ω l g) := by
    by_cases hlp : l = p
    · subst hlp
      obtain ⟨g, hg, hf⟩ := UpperTheory.V.Base.decInf ℚ Ω l ⊤ isOpen_univ A hA
      exact ⟨g, hg.2, hf⟩
    · obtain ⟨-, -, γ, hγ, -, hc⟩ := UpperTheory.V.Chr.decCyc Ω p A hp hA
      refine ⟨γ, hγ, fun hf => ?_⟩
      obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 hf
      have h3 := congrArg (Units.val : ℤ_[l]ˣ → ℤ_[l]) e
      rw [Units.val_pow_eq_pow_val, hc l hlp, Units.val_one] at h3
      have h4 : p ^ n = 1 := by exact_mod_cast h3
      exact (Nat.one_lt_pow hn.ne' hp.one_lt).ne' h4
  obtain ⟨g, hg, hf⟩ := hg
  have hcl : IsClosed (((Dec (F := ℚ) A).map (cycZ ℚ Ω l) : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) :=
    ((isClosed_Dec (F := ℚ) A).isCompact.image (continuous_cycZ ℚ Ω l)).isClosed
  have h0 := UpperTheory.V.Ws.index_ne_zero_of_isClosed_of_not_isOfFinOrder l _ hcl ⟨_, ⟨g, hg, rfl⟩, hf⟩
  have e : (cycZ ℚ Ω l).ker ⊔ Dec (F := ℚ) A = ((Dec (F := ℚ) A).map (cycZ ℚ Ω l)).comap (cycZ ℚ Ω l) := by
    rw [Subgroup.comap_map_eq, sup_comm]
  rw [e, Subgroup.index_comap]
  have hrel0 : ((Dec (F := ℚ) A).map (cycZ ℚ Ω l)).relIndex ⊤ ≠ 0 := by rwa [Subgroup.relIndex_top_right]
  exact fun h => hrel0 (Subgroup.relIndex_eq_zero_of_le_right le_top h)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.NcardPlacesDividingLeOfOrbitBound
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

open scoped Pointwise in
private theorem val_smul_fix {Ω : Type} [Field Ω] [CharZero Ω] (B : ValuationSubring Ω) (v : G ℚ Ω) (x : Ω)
    (hx : v x = x) : (v • B).valuation x < 1 ↔ B.valuation x < 1 := by
  have key : ∀ A : ValuationSubring Ω, A.valuation x < 1 ↔ x = 0 ∨ x⁻¹ ∉ A := by
    intro A
    rcases eq_or_ne x 0 with h | h
    · simp [h]
    · have e := (A.valuation).one_lt_val_iff (inv_ne_zero h)
      rw [inv_inv] at e
      rw [← e, ← not_le, A.valuation_le_one_iff]
      simp [h]
  have mem : x⁻¹ ∈ v • B ↔ x⁻¹ ∈ B := by
    have hv : v x⁻¹ = x⁻¹ := by rw [map_inv₀, hx]
    constructor
    · rintro ⟨z, hz, hzx⟩
      change v z = x⁻¹ at hzx
      have hz' : z = x⁻¹ := v.injective (hzx.trans hv.symm)
      exact hz' ▸ hz
    · intro h
      exact ⟨x⁻¹, h, hv⟩
  rw [key, key, mem]

theorem UpperTheory.V.Ws.ncard_placesDividing_le_of_orbitBound :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F : IntermediateField ℚ Ω) [NumberField F] (V : Subgroup (G ℚ Ω)) (p n : ℕ), p ≠ 0 → V ≤ F.fixingSubgroup → OrbLe V p n → (plDvd F p).ncard ≤ n := by
  intro Ω _ _ _ F _ V p n hp hV hO
  obtain ⟨T, hT, hTp, hTA⟩ := hO
  have po : ∀ (w : HeightOneSpectrum (𝓞 F)) (y : 𝓞 F),
      (placeOf Ω w).valuation (algebraMap F Ω (y : F)) < 1 ↔ y ∈ w.asIdeal := by
    intro w y
    have h := isPlaceOver_placeOf Ω w
    unfold IsPlaceOver at h
    exact h y
  have fix : ∀ σ ∈ V, ∀ y : 𝓞 F, σ (algebraMap F Ω (y : F)) = algebraMap F Ω (y : F) := by
    intro σ hσ y
    exact (IntermediateField.mem_fixingSubgroup_iff F σ).1 (hV hσ) _ (by simp)
  open scoped Pointwise in
  have hup : ∀ w ∈ plDvd F p, ∃ B ∈ T, ∃ σ ∈ V, σ • B = placeOf Ω w := by
    intro w hw
    apply hTA
    have hw' : ((p : 𝓞 F)) ∈ w.asIdeal := hw
    simpa using (po w p).2 hw'
  choose! f hfT σ hσV hσ using hup
  have hinj : Set.InjOn f (plDvd F p) := by
    intro w1 h1 w2 h2 he
    apply HeightOneSpectrum.ext
    ext y
    rw [← po w1 y, ← po w2 y, ← hσ w1 h1, ← hσ w2 h2,
      val_smul_fix _ _ _ (fix _ (hσV w1 h1) y), val_smul_fix _ _ _ (fix _ (hσV w2 h2) y), he]
  calc (plDvd F p).ncard ≤ (T : Set (ValuationSubring Ω)).ncard :=
        Set.ncard_le_ncard_of_injOn f (fun w hw => hfT w hw) hinj T.finite_toSet
    _ = T.card := Set.ncard_coe_finset T
    _ ≤ n := hT
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem plDvd_eq (F : Type) [Field F] (N : ℕ) (hN : N ≠ 0) :
    plDvd F N = ⋃ p ∈ N.primeFactors, plDvd F p := by
  ext v
  simp only [plDvd, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  constructor
  · have key : ∀ M : ℕ, M ≠ 0 → ((M : 𝓞 F) ∈ v.asIdeal) →
        ∃ p ∈ M.primeFactors, (p : 𝓞 F) ∈ v.asIdeal := by
      intro M
      induction M using Nat.strong_induction_on with
      | _ M ih =>
        intro hM hv
        by_cases h1 : M = 1
        · subst h1
          rw [Nat.cast_one] at hv
          exact (v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hv)).elim
        · obtain ⟨p, hp, m, rfl⟩ := Nat.exists_prime_and_dvd h1
          rw [Nat.cast_mul] at hv
          rcases v.isPrime.mem_or_mem hv with h | h
          · exact ⟨p, Nat.mem_primeFactors.2 ⟨hp, dvd_mul_right p m, hM⟩, h⟩
          · have hm0 : m ≠ 0 := by
              rintro rfl
              simp at hM
            have hlt : m < p * m := by
              have := hp.two_le
              have := Nat.pos_of_ne_zero hm0
              nlinarith
            obtain ⟨q, hq, hqv⟩ := ih m hlt hm0 h
            have hq' := Nat.mem_primeFactors.1 hq
            exact ⟨q, Nat.mem_primeFactors.2 ⟨hq'.1, hq'.2.1.mul_left p, hM⟩, hqv⟩
    exact key N hN
  · rintro ⟨p, hp, hpv⟩
    obtain ⟨m, hm⟩ := (Nat.mem_primeFactors.1 hp).2.1
    rw [hm, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hpv

theorem UpperTheory.V.Ws.exists_uniform_bound_ncard_placesDividing :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (U : Subgroup (G ℚ Ω)) (N : ℕ), U.Normal → IsOpen (U : Set (G ℚ Ω)) → N ≠ 0 → ∃ g : ℕ, ∀ (F : IntermediateField ℚ Ω) [NumberField F], cycU l U ≤ F.fixingSubgroup → (plDvd F N).ncard ≤ g := by
  intro Ω _ _ _ l _ U N hUn hUo hN
  haveI := hUn
  haveI : (cycU l U).Normal := by
    unfold cycU
    infer_instance
  have hUi : U.index ≠ 0 := by
    haveI := Subgroup.quotient_finite_of_isOpen U hUo
    exact Subgroup.index_ne_zero_of_finite
  have hUle : ∀ {X : Type} (s : Finset ℕ) (f : ℕ → Set X),
      (⋃ p ∈ s, f p).ncard ≤ ∑ p ∈ s, (f p).ncard := by
    intro X s f
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro a s ha ih
      rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
      exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_left ih _)
  have hb : ∀ p : ℕ, ∃ n, p.Prime → OrbLe (cycU l U) p n := by
    intro p
    by_cases hA : ∃ A₀ : ValuationSubring Ω, A₀.valuation (p : Ω) < 1
    · obtain ⟨A₀, hA₀⟩ := hA
      refine ⟨(cycU l U ⊔ Dec A₀).index, fun hp => ?_⟩
      have hK := index_cyclotomicKer_sup_decompositionGroup_ne_zero Ω l p A₀ hp hA₀
      have hs := supIndex (G ℚ Ω) (cycZ ℚ Ω l).ker U (Dec A₀) hUi hK
      exact orbIndex Ω p (cycU l U) A₀ hp hA₀ hs.1
    · exact ⟨0, fun _ => ⟨∅, by simp, by simp, fun A hA' => (hA ⟨A, hA'⟩).elim⟩⟩
  choose nf hnf using hb
  refine ⟨∑ p ∈ N.primeFactors, nf p, fun F _ hF => ?_⟩
  rw [plDvd_eq F N hN]
  refine (hUle _ _).trans (Finset.sum_le_sum fun p hp => ?_)
  have hpp := (Nat.mem_primeFactors.1 hp).1
  exact ncard_placesDividing_le_of_orbitBound Ω F (cycU l U) p (nf p) hpp.ne_zero hF (hnf p hpp)
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.x2 :
    CohomologyHyp → UpperTheory.V.Published.FerreroWashington → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → TameL l T.F → ∃ C : ℕ, ∀ (T' : Tower D) (m : ℕ), T.Le T' → IsLayer l m T.F T'.F →
      ∀ (k : Type) [Field k] (a : c.O →+* k), (∀ x ∈ maximalIdeal c.O, a x = 0) → (T'.fr ∅).Bounds a T'.d C := by
  intro P hFW Ω _ _ _ l _ c D T hT _
  have hD : D.Good := hT.2.elim (fun h => h.1.1) fun h => h.1.1
  obtain ⟨ho, hc, hl⟩ := kerOverRationals_open_commutator_layer D hD T.F
  obtain ⟨r, hr⟩ := exists_iwasawaRank_bound_of_ferreroWashington hFW Ω l (kerQ D T.F) hD.l_odd ho hc inf_le_right
  have hN : (kerQ D T.F).Normal := ⟨fun x hx g => by
    have h : g * x * g⁻¹ * x⁻¹ ∈ kerQ D T.F := hc (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top x))
    simpa using mul_mem h hx⟩
  obtain ⟨g, hg⟩ := exists_uniform_bound_ncard_placesDividing Ω l (kerQ D T.F) (prodS D) hN ho (residualKernel_properties D hD T).2.2.2.2.2.2.1.1
  refine ⟨r + 2 + 2 * g, fun T' m _ hm k _ a ha => ?_⟩
  obtain ⟨e, hle⟩ := hl m T'.F hm
  have hg' := hg T'.F hle
  have hK : UpperTheory.V.Two.XRk l 1 T'.Kr r := (residualKernel_properties D hD T').2.2.2.2.2.2.2.2 r (e ▸ hr (m + 1))
  obtain ⟨b1, b2⟩ := rank_localCocycleSpaces_le P D hD T' g hg'
  obtain ⟨b3, b4, b5⟩ := rank_cocycleSpaces_le_of_towerIwasawaRank P D hD T' r g hg' hK
  have ea : a = (Ideal.Quotient.lift (maximalIdeal c.O) a ha : ResidueField c.O →+* k).comp (residue c.O) :=
    RingHom.ext fun _ => rfl
  rw [ea]
  refine cocycleBounds_of_ringHom_comp _ (ResidueField c.O) k _ _ _ _ ⟨b1.trans (by omega), fun w _ => (b3 w).trans (Nat.cast_le.2 (by omega)),
    fun w hw => (b4 w hw).trans (Nat.cast_le.2 (by omega)),
    fun w _ => (b5 w).trans (add_le_add le_rfl (Nat.cast_le.2 (by omega))),
    fun w _ => (b2 w).trans (add_le_add le_rfl (Nat.cast_le.2 (by omega)))⟩
