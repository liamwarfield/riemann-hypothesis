module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.FinrankK
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TameRecAll
public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.GreenCuspLabels.GreenCuspidal
public import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.ConjTorusSubApply
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
  UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin
  UpperTheory.V.Alg.IsCO.toIsLocalRing UpperTheory.V.Alg.IsCO.complete
  UpperTheory.V.Alg.IsCO.isLocalHom UpperTheory.V.Alg.IsCO.self

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PTameRead
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.InertialTypesAlt.TameReduction

section Res

variable {Ω : Type} [Field Ω]

private noncomputable def toRes (A : ValuationSubring Ω) (F : Type) [Field F] [NumberField F] [Algebra F Ω] :
    𝓞 F →+* IsLocalRing.ResidueField A :=
  (IsLocalRing.residue A).comp
    { toFun := fun x => ⟨algebraMap F Ω (x : F), ReciprocityTheory.Gal.mem_of_isIntegral_int A (x.2.map (algebraMap F Ω).toIntAlgHom)⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }

private theorem toRes_eq_zero_iff (A : ValuationSubring Ω) {F : Type} [Field F] [NumberField F] [Algebra F Ω] (x : 𝓞 F) :
    toRes A F x = 0 ↔ A.valuation (algebraMap F Ω (x : F)) < 1 := by
  unfold toRes
  rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]
  exact A.valuation_lt_one_iff _

private theorem exists_emb {A : ValuationSubring Ω} {F : Type} [Field F] [NumberField F] [Algebra F Ω]
    {v : HeightOneSpectrum (𝓞 F)} (hv : IsPlaceOver A v) {K : Type} [Field K] (red : 𝓞 F →+* K)
    (hs : Function.Surjective red) (hk : RingHom.ker red = v.asIdeal) :
    ∃ ι : K →+* IsLocalRing.ResidueField A, ∀ x, ι (red x) = toRes A F x := by
  refine ⟨RingHom.liftOfSurjective red hs ⟨toRes A F, fun x hx => ?_⟩, fun x => ?_⟩
  · rw [hk] at hx
    rw [RingHom.mem_ker, toRes_eq_zero_iff]
    exact (hv x).2 hx
  · exact RingHom.liftOfRightInverse_comp_apply _ _ _ _ _

private theorem residue_eq_toRes {A : ValuationSubring Ω} {F : Type} [Field F] [NumberField F] [Algebra F Ω]
    (z : A) (x : 𝓞 F) (h : A.valuation ((z : Ω) - algebraMap F Ω (x : F)) < 1) :
    IsLocalRing.residue A z = toRes A F x := by
  unfold toRes
  rw [RingHom.comp_apply, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  exact (A.valuation_lt_one_iff _).2 h

end Res

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem res_read {g n : ℕ} [Fact g.Prime] (hn : 0 < n) (D : UpperTheory.Zero.LLC.Ext h g n) (R : Ine (F := E) A →* D.Kˣ) (hR : D.Res R)
    (t : Ine (F := E) A) : ∃ (t' : Ine (F := D.E') A) (x : 𝓞 D.E'),
      (∀ z : Ω, (t : G E Ω) z = (t' : G D.E' Ω) z) ∧
      Valued.v ((D.a' (ineIncl D.h' t') : D.w'.adicCompletion D.E') - algebraMap D.E' (D.w'.adicCompletion D.E') (x : D.E')) < 1 ∧
      ((R t : D.Kˣ) : D.K) = D.red x := by
  obtain ⟨t', ht', e⟩ := DiscreteGroups.sglob.DzType.ine_lift g A w h D.w' D.h' n hn D.unr D.card (t : G E Ω) t.2
  obtain ⟨x, hx⟩ := DiscreteGroups.sglob.DzType.exists_int_approx_compl D.w' _ (DiscreteGroups.sglob.DzType.val_artin_ine D.ha' ⟨t', ht'⟩).le
  have hne := DiscreteGroups.sglob.DzType.red_ne_zero_of_approx D.ha' D.ker hx
  refine ⟨⟨t', ht'⟩, x, fun z => by rw [← e]; rfl, hx, ?_⟩
  have := hR t ⟨t', ht'⟩ x (Units.mk0 _ hne) e.symm rfl hx
  rw [this]; rfl

end UpperTheory.Gal.InertialTypesAlt.TameReduction

open UpperTheory.Gal.InertialTypesAlt.TameReduction in
theorem UpperTheory.Gal.InertialTypesAlt.tameRead :
    TameRead := by
  intro E Ω _ _ _ _ _ A v h g _ m hm D R hR
  obtain ⟨ι, hι⟩ := exists_emb D.h' D.red D.surj D.ker
  refine ⟨ι, fun t ϖ hϖ z hz => ?_⟩
  obtain ⟨t', x, ht, hx, hr⟩ := res_read hm D R hR t
  have hg := DiscreteGroups.sglob.DzType.natCast_mem_of_normV D.w' g m hm D.card
  have h1 := UpperTheory.Zero.LLC.tameRecAll D.E' Ω g A D.w' D.h' hg D.unr D.a' D.ha' ϖ (by rw [D.card]; exact hϖ) t' x hx
  rw [hr, hι]
  refine (residue_eq_toRes z x ?_).symm
  rw [hz, ht]
  exact h1
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PCuspChar
noncomputable section

open GlobalTheory.SmGL GlobalTheory.Shin GlobalTheory.SplitWeil

namespace UpperTheory.Gal.InertialTypesAlt

private theorem blk_two {m a : ℕ} (ha : a < m) (hd : ∑ b, (![a, m - a] : Fin 2 → ℕ) b = m) (i : Fin m) :
    (blk (stdBlocks (![a, m - a] : Fin 2 → ℕ) hd) i = 0 ↔ (i : ℕ) < a) := by
  obtain ⟨⟨b, j⟩, hbj⟩ : ∃ p, (stdBlocks (![a, m - a] : Fin 2 → ℕ) hd).symm i = p := ⟨_, rfl⟩
  have hi := stdBlocks_val (![a, m - a] : Fin 2 → ℕ) hd b j
  rw [← hbj, Equiv.apply_symm_apply] at hi
  unfold blk
  rw [hbj]
  have hj := j.isLt
  fin_cases b
  · simp at hi hj ⊢
    omega
  · simp at hi hj ⊢
    omega

private theorem blk_lt_iff {m a : ℕ} (ha : a < m) (hd : ∑ b, (![a, m - a] : Fin 2 → ℕ) b = m) (i j : Fin m) :
    blk (stdBlocks (![a, m - a] : Fin 2 → ℕ) hd) i < blk (stdBlocks (![a, m - a] : Fin 2 → ℕ) hd) j ↔
      (i : ℕ) < a ∧ a ≤ (j : ℕ) := by
  have hi := blk_two ha hd i
  have hj := blk_two ha hd j
  have h1 := (blk (stdBlocks (![a, m - a] : Fin 2 → ℕ) hd) i).isLt
  have h2 := (blk (stdBlocks (![a, m - a] : Fin 2 → ℕ) hd) j).isLt
  rw [Fin.lt_iff_val_lt_val]
  rw [Fin.ext_iff, Fin.val_zero] at hi hj
  omega

private theorem rad_le {F : Type} [Field F] {m a : ℕ} (h0 : 0 < a) (ha : a < m) (H : Subgroup (GL (Fin m) F))
    (hH : (H : Set (GL (Fin m) F)) = {u : GL (Fin m) F | ∀ i j : Fin m, (u : Matrix (Fin m) (Fin m) F) i j = (if i = j then 1 else 0) ∨ (i.val < a ∧ a ≤ j.val)})
    (hd : ∑ b, (![a, m - a] : Fin 2 → ℕ) b = m) (u : GL (Fin m) F)
    (hu : u ∈ unipRad F (stdBlocks (![a, m - a] : Fin 2 → ℕ) hd)) : u ∈ H := by
  have hu' := GlobalTheory.SmGL.CuspMax.mem_unipRad_iff_entries.mp hu
  have hmem : u ∈ (H : Set (GL (Fin m) F)) := by
    rw [hH]
    intro i j
    by_cases h : (i : ℕ) < a ∧ a ≤ (j : ℕ)
    · exact Or.inr h
    · left
      rw [hu' i j (by rwa [blk_lt_iff ha hd])]
      simp [Matrix.one_apply]
  exact hmem

theorem cuspChar : CuspChar := by
  intro F _ _ θ hθ m hm W _ _ _ κ hirr hcusp
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have hc := GlobalTheory.T.isCharacterOverSubfield_of_representation ℂ ℂ (GL (Fin m) F) W κ
  have hprim : GlobalTheory.CuspGL.IsPrimitive
      (GlobalTheory.CuspGL.extZero (fun g : GL (Fin m) F => algebraMap ℂ ℂ (κ.character g))) := by
    refine GlobalTheory.T.isPrimitive_extendZero_of_sum_unipotentRadical F m _ hc.1 fun a h0 ham => ?_
    obtain ⟨A, H, -, hH, -⟩ := GlobalTheory.T.exists_standardUnipotentRadical_bijOn_nilradical F m a ham.le
    have hd : ∑ b, (![a, m - a] : Fin 2 → ℕ) b = m := by
      simp [Fin.sum_univ_two]
      omega
    have hne : unipRad F (stdBlocks (![a, m - a] : Fin 2 → ℕ) hd) ≠ ⊥ := by
      rw [GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff]
      refine ⟨⟨0, hm⟩, ⟨a, ham⟩, ?_⟩
      rw [blk_lt_iff ham hd]
      exact ⟨h0, le_refl a⟩
    have hfix : ∀ v : W, (∀ u ∈ H, κ u v = v) → v = 0 := fun v hv =>
      hcusp 2 _ _ hne v fun u hu => hv u (rad_le h0 ham H hH hd u hu)
    have hz := PositivityTheory.GreenCharacters.sum_char_eq_zero κ H hfix
    rw [← hH, finsum_mem_def, finsum_eq_sum_of_fintype]
    rw [← hz]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hu : u ∈ H <;> simp [Set.indicator_apply, hu]
  obtain ⟨k, hk, hx⟩ := GlobalTheory.CuspFormula.exists_regular F θ hθ m hm _ (hc.2 hirr) hprim
  refine ⟨k, hk, fun x => ?_⟩
  have := hx x
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at this
  exact this

end UpperTheory.Gal.InertialTypesAlt
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PArtRead
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem resS_eq_resS_of_mul_sub_eq_mul {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (y₁ y₂ : 𝒪[k]) (h : valuation k ((y₁ : k) - y₂) < 1) :
    IsLocalRing.residue 𝒪[k] y₁ = IsLocalRing.residue 𝒪[k] y₂ := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]
  exact ne_of_lt h

private theorem residue_eq_of_valuation_sub_lt_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (z₁ z₂ : A)
    (h : A.valuation ((z₁ : Ω) - z₂) < 1) :
    IsLocalRing.residue A z₁ = IsLocalRing.residue A z₂ := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  exact h

theorem UpperTheory.Gal.InertialTypesAlt.artRead :
    ArtRead := by
  unfold ArtRead
  intro E Ω _ _ _ _ _ A v h g _ hg1 hg2 a ha e he t ϖ hϖ
  unfold ResEmb at he
  have hp : Nat.Prime g := Fact.out
  have hEq : (valuation (HeightOneSpectrum.adicCompletion E v)).IsEquiv Valued.v := ValuativeRel.isEquiv _ _
  have hα : Valued.v (a (ineIncl h t) : HeightOneSpectrum.adicCompletion E v) = 1 :=
    DiscreteGroups.sglob.DzType.val_artin_ine ha t
  obtain ⟨u, hu⟩ := valuation_eq_one_iff.1 (hEq.eq_one_iff_eq_one.2 hα)
  have hg0 : (g : Ω) ≠ 0 := by
    rw [← map_natCast (algebraMap E Ω)]
    exact (_root_.map_ne_zero _).2 (Nat.cast_ne_zero.2 hp.ne_zero)
  have hg1' : (g : Ω) ≠ 1 := by
    rw [← map_natCast (algebraMap E Ω), ← map_one (algebraMap E Ω)]
    intro hc
    have := (algebraMap E Ω).injective hc
    exact hp.one_lt.ne' (by exact_mod_cast this)
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    rcases Nat.eq_zero_or_pos (normV v - 1) with hm | hm
    · rw [hm, pow_zero] at hϖ
      exact hg1' hϖ.symm
    · rw [zero_pow hm.ne'] at hϖ
      exact hg0 hϖ.symm
  have hz : A.valuation ((t : G E Ω) ϖ / ϖ) = 1 := DiscreteGroups.sglob.DzType.val_ratio (Ine_le_Dec A t.2) hϖ0
  obtain ⟨z, hzdef⟩ : ∃ z : A, (z : Ω) = (t : G E Ω) ϖ / ϖ :=
    ⟨⟨_, (A.valuation_le_one_iff _).1 hz.le⟩, rfl⟩
  obtain ⟨x, hx⟩ := DiscreteGroups.sglob.DzType.exists_int_approx_compl v
    (a (ineIncl h t) : HeightOneSpectrum.adicCompletion E v) hα.le
  have hx2 := UpperTheory.Zero.LLC.tameRecAll E Ω g A v h hg1 hg2 a ha ϖ hϖ t x hx
  refine ⟨z, u, hzdef, hu, ?_, ?_⟩
  · have hxA : algebraMap E Ω x ∈ A := by
      have h1 : ((t : G E Ω) ϖ / ϖ - algebraMap E Ω x) ∈ A := (A.valuation_le_one_iff _).1 hx2.le
      have h2 := A.sub_mem z.2 h1
      rw [hzdef, sub_sub_cancel] at h2
      exact h2
    have hyK : valuation (HeightOneSpectrum.adicCompletion E v)
        (algebraMap E (HeightOneSpectrum.adicCompletion E v) x) ≤ 1 :=
      hEq.le_one_iff_le_one.2 (DiscreteGroups.sglob.DzType.val_alg_le_one x)
    let y : 𝒪[HeightOneSpectrum.adicCompletion E v] := ⟨_, hyK⟩
    let zx : A := ⟨_, hxA⟩
    have hu' : (((u : 𝒪[HeightOneSpectrum.adicCompletion E v])) : HeightOneSpectrum.adicCompletion E v) =
        (a (ineIncl h t) : HeightOneSpectrum.adicCompletion E v) := congrArg Units.val hu
    have h1 : IsLocalRing.residue _ (u : 𝒪[HeightOneSpectrum.adicCompletion E v]) = IsLocalRing.residue _ y := by
      apply resS_eq_resS_of_mul_sub_eq_mul
      show valuation (HeightOneSpectrum.adicCompletion E v)
        (((u : 𝒪[HeightOneSpectrum.adicCompletion E v]) : HeightOneSpectrum.adicCompletion E v) -
          algebraMap E (HeightOneSpectrum.adicCompletion E v) x) < 1
      rw [hu']
      exact hEq.lt_one_iff_lt_one.2 hx
    have h2 : IsLocalRing.residue A z = IsLocalRing.residue A zx := by
      apply residue_eq_of_valuation_sub_lt_one
      show A.valuation ((z : Ω) - algebraMap E Ω x) < 1
      rw [hzdef]
      exact hx2
    rw [h2, ← he x y zx rfl rfl, ← h1]
    rfl
  · have hzm : z ^ (normV v - 1) = 1 := by
      apply Subtype.ext
      rw [SubmonoidClass.coe_pow, hzdef, div_pow, ← map_pow, hϖ, map_natCast, div_self hg0]
      rfl
    rw [← map_pow, hzm, map_one]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PUnrOfIne
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.unrOfIne :
    UnrOfIne := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ A v w hv hw hI
  have hunder : HeightOneSpectrum.under (𝓞 K) w = v := by
    apply HeightOneSpectrum.ext
    ext x
    show algebraMap (𝓞 K) (𝓞 M) x ∈ w.asIdeal ↔ x ∈ v.asIdeal
    rw [← hw, ← hv]
    have hx : algebraMap M Ω ((algebraMap (𝓞 K) (𝓞 M) x : 𝓞 M) : M) = algebraMap K Ω (x : K) := by
      rw [IsScalarTower.algebraMap_apply K M Ω]
      rfl
    rw [hx]
  have hlies : w.asIdeal.LiesOver v.asIdeal := ⟨congrArg HeightOneSpectrum.asIdeal hunder.symm⟩
  have hinert : Ideal.inertia Gal(M/K) w.asIdeal = ⊥ := by
    rw [← UpperTheory.V.CF.ineAbs K M Ω A w hw, Subgroup.map_eq_bot_iff]
    intro t ht
    rw [MonoidHom.mem_ker]
    ext x
    apply (algebraMap M Ω).injective
    show algebraMap M Ω ((t.restrictNormal M) x) = algebraMap M Ω x
    rw [AlgEquiv.restrictNormal_commutes]
    exact hI t ht x
  have he : w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
    rw [← (UpperTheory.V.CF.ineCard).1 K M w, hinert]
    simp
  refine ⟨hunder, ?_, ?_⟩
  · rintro ⟨w', hw'⟩
    rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain,
      ← Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w'.asIdeal Gal(M/K),
      Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.asIdeal Gal(M/K)]
    exact he
  · intro x hx hmem
    have hcomap : Ideal.comap (algebraMap (𝓞 K) (𝓞 M)) w.asIdeal = v.asIdeal :=
      congrArg HeightOneSpectrum.asIdeal hunder
    have hv1 : v.asIdeal.ramificationIdx' w.asIdeal = 1 := by
      rw [Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot]
      exact he
    have hle : Ideal.map (algebraMap (𝓞 K) (𝓞 M)) v.asIdeal ≤ w.asIdeal :=
      Ideal.map_le_iff_le_comap.2 hcomap.ge
    have hnot : ¬ Ideal.map (algebraMap (𝓞 K) (𝓞 M)) v.asIdeal ≤ w.asIdeal ^ 2 :=
      fun h => ((Ideal.ramificationIdx'_ne_one_iff hle).2 h) hv1
    by_cases hxv : x ∈ v.asIdeal
    · obtain ⟨J, hJ⟩ : v.asIdeal ∣ Ideal.span {x} :=
        Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hxv)
      have hJv : ¬ J ≤ v.asIdeal := by
        intro h
        apply hx
        rw [← Ideal.span_singleton_le_iff_mem, hJ, pow_two]
        exact Ideal.mul_mono_right h
      have hJw : ¬ Ideal.map (algebraMap (𝓞 K) (𝓞 M)) J ≤ w.asIdeal := by
        intro h
        rw [Ideal.map_le_iff_le_comap, hcomap] at h
        exact hJv h
      have hsup : Ideal.map (algebraMap (𝓞 K) (𝓞 M)) J ⊔ w.asIdeal = ⊤ := by
        by_contra hne
        exact hJw (le_sup_left.trans ((w.isMaximal.eq_of_le hne le_sup_right).symm.le))
      have hsup2 : Ideal.map (algebraMap (𝓞 K) (𝓞 M)) J ⊔ w.asIdeal ^ 2 = ⊤ := by
        have hc : IsCoprime (Ideal.map (algebraMap (𝓞 K) (𝓞 M)) J) w.asIdeal :=
          Ideal.isCoprime_iff_sup_eq.2 hsup
        exact Ideal.isCoprime_iff_sup_eq.1 hc.pow_right
      apply hnot
      have hx2 : Ideal.map (algebraMap (𝓞 K) (𝓞 M)) (Ideal.span {x}) ≤ w.asIdeal ^ 2 := by
        rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]
        exact hmem
      have hr : Ideal.map (algebraMap (𝓞 K) (𝓞 M)) v.asIdeal * w.asIdeal ^ 2 ≤ w.asIdeal ^ 2 :=
        Ideal.mul_le_right
      calc Ideal.map (algebraMap (𝓞 K) (𝓞 M)) v.asIdeal
          = Ideal.map (algebraMap (𝓞 K) (𝓞 M)) v.asIdeal *
              (Ideal.map (algebraMap (𝓞 K) (𝓞 M)) J ⊔ w.asIdeal ^ 2) := by rw [hsup2, Ideal.mul_top]
        _ = Ideal.map (algebraMap (𝓞 K) (𝓞 M)) (Ideal.span {x}) ⊔
              Ideal.map (algebraMap (𝓞 K) (𝓞 M)) v.asIdeal * w.asIdeal ^ 2 := by
            rw [Ideal.mul_sup, hJ, Ideal.map_mul]
        _ ≤ w.asIdeal ^ 2 := sup_le hx2 hr
    · apply hxv
      rw [← hcomap, Ideal.mem_comap]
      exact Ideal.pow_le_self two_ne_zero hmem
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PCuspIrr
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem redK_mem_unipRad {s : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin n) {g : GL (Fin n) k}
    (hu : g ∈ unipRad k e) (hK : g ∈ KO k (Fin n)) : redK k (Fin n) ⟨g, hK⟩ ∈ unipRad 𝓀[k] e := by
  refine CuspMax.mem_unipRad_iff_entries.2 fun i j hij => ?_
  have h := CuspMax.mem_unipRad_iff_entries.1 hu i j hij
  by_cases hh : i = j
  · subst hh
    have h1 := (redK_eq_iff ⟨g, hK⟩ i i 1).2 (by simp [h])
    simpa using h1
  · rw [Matrix.one_apply_ne hh]
    exact (redK_eq_zero_iff ⟨g, hK⟩ i j).2 (by simp [h, Matrix.one_apply_ne hh])

private theorem finCusp_levelZero {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)
    (hs : IsSmooth π) (hi : π.IsIrreducible) (hc : IsCuspidal π) : PositivityTheory.Rg.DzCount.FinCusp (levelZero π) := by
  intro s d e hne v hv
  have hV : (v : V) ∈ fixed π (KOne k (Fin n) ⊔ (unipRad k e ⊓ KO k (Fin n))) := by
    refine GlobalTheory.DepthZeroJac.mem_fixed_sup v.2 (GlobalTheory.Parabolic.mem_fixed.2 fun g hg => ?_)
    have h1 := congrArg Subtype.val (hv _ (redK_mem_unipRad e hg.1 hg.2))
    rwa [levelZero_apply] at h1
  have hne' : unipRad k e ≠ ⊥ := CuspMax.unipRad_ne_bot_iff.2 (CuspMax.unipRad_ne_bot_iff.1 hne)
  haveI := hc.2 s d e hne'
  exact Subtype.ext (GlobalTheory.DepthZeroJac.depthZeroJacquetInjective k n s d e ⟨V, π, hs, hi⟩ (v : V) hV (Subsingleton.elim _ _))

private theorem irreducible_levelZero (π : IrrRep (GL (Fin n) k)) (ω : kˣ →* ℂˣ) (hω : HasCentralChar π.ρ ω)
    (hF : PositivityTheory.Rg.DzCount.FinCusp (levelZero π.ρ)) (hD : fixed π.ρ (KOne k (Fin n)) ≠ ⊥) :
    (levelZero π.ρ).IsIrreducible := by
  have key : ∀ W : Subrepresentation (levelZero π.ρ), W ≠ ⊥ → W = ⊤ := by
    intro W hW
    haveI : Nontrivial W.toSubmodule := by
      rw [Submodule.nontrivial_iff_ne_bot]
      intro h
      exact hW (Subrepresentation.toSubmodule_injective h)
    let j : W.toSubmodule →ₗ[ℂ] π.V := (fixed π.ρ (KOne k (Fin n))).subtype ∘ₗ W.toSubmodule.subtype
    have hFτ : PositivityTheory.Rg.DzCount.FinCusp W.toRepresentation := by
      intro s d e hne w hw
      exact Subtype.ext (hF s d e hne w (fun u hu => congrArg Subtype.val (hw u hu)))
    have hj : PositivityTheory.Rg.DzCount.IsTypeMap W.toRepresentation π.ρ j := by
      refine ⟨?_, ?_⟩
      · intro a c hac
        exact Subtype.ext (Subtype.ext hac)
      · intro g w
        exact levelZero_apply π.ρ g w
    have hfix := PositivityTheory.Rg.DzCount.B.st6 k W.toSubmodule n W.toRepresentation hFτ π ω hω j hj
    apply Subrepresentation.toSubmodule_injective
    show W.toSubmodule = ⊤
    rw [eq_top_iff]
    intro v _
    have hv : (v : π.V) ∈ LinearMap.range j := hfix ▸ v.2
    obtain ⟨w, hw⟩ := hv
    have hwv : (w : fixed π.ρ (KOne k (Fin n))) = v := Subtype.ext hw
    rw [← hwv]
    exact w.2
  haveI : Nontrivial (Subrepresentation (levelZero π.ρ)) := by
    refine ⟨⟨⊥, ⊤, fun h => hD ?_⟩⟩
    have h' := congrArg Subrepresentation.toSubmodule h
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hm : (⟨v, hv⟩ : fixed π.ρ (KOne k (Fin n))) ∈ (⊤ : Subrepresentation (levelZero π.ρ)).toSubmodule :=
      Submodule.mem_top
    rw [← h'] at hm
    exact congrArg Subtype.val ((Submodule.mem_bot ℂ).1 hm)
  constructor
  intro W
  by_cases h : W = ⊥
  · exact Or.inl h
  · exact Or.inr (key W h)

end

theorem UpperTheory.Gal.InertialTypesAlt.cuspIrr :
    CuspIrr := by
  intro k _ _ _ _ _ y hc hD
  have hadm := (UpperTheory.Zero.LLC.Pr.adm k y.1 y.2.rep.V y.rep y.2.rep.smooth y.2.rep.irr).2 (levelPre ⊥)
    (isOpen_levelPre ⊥) (isCompact_levelPre ⊥)
  rw [levelPre_bot] at hadm
  obtain ⟨ω, hω⟩ := (GlobalTheory.T.centralCharacter_subquotient_productIrreducibles k).1 y
  have hF := finCusp_levelZero y.rep y.2.rep.smooth y.2.rep.irr hc.2
  exact ⟨hadm, irreducible_levelZero y.2.rep ω hω hF hD, hF⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PFrobL
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem hcL_cons_of {F : Type} [Field F] (p : Σ m : ℕ, GL (Fin m) F → ℂ)
    (Y : List (Σ m : ℕ, GL (Fin m) F → ℂ)) (b : ℕ) (h : (Y.map Sigma.fst).sum = b) (n : ℕ) :
    hcL (p :: Y) n = hc p.1 b p.2 (hcL Y b) n := by
  subst h
  exact hcL_cons p Y n

private theorem collapse {G X Z : Type} [Finite G] [Finite X] [Finite Z]
    (A : G → Prop) (B : Z → Prop) (I : G → Prop) (tl : G → X) (br : G → Z)
    (hA : ∀ p, A p ↔ I p ∧ B (br p))
    (u : X → ℂ) (v : Subtype B → ℂ) (T : G → ℂ) (w : Subtype A → ℂ)
    (hw : ∀ p (hp : A p) (hp' : B (br p)), w ⟨p, hp⟩ = u (tl p) * v ⟨br p, hp'⟩) :
    ∑ᶠ x, u x * ∑ᶠ p' : Subtype B, v p' * (∑ᶠ p : G, if I p ∧ tl p = x ∧ br p = p'.1 then T p else 0) =
      ∑ᶠ p : Subtype A, w p * T p := by
  classical
  haveI := Fintype.ofFinite G
  haveI := Fintype.ofFinite X
  haveI := Fintype.ofFinite Z
  have key : ∀ p : G, (∑ x, ∑ p' : Subtype B,
      u x * (v p' * if I p ∧ tl p = x ∧ br p = p'.1 then T p else 0)) =
      if h : A p then w ⟨p, h⟩ * T p else 0 := by
    intro p
    by_cases hI : I p
    · by_cases hB : B (br p)
      · have hAp : A p := (hA p).2 ⟨hI, hB⟩
        rw [dif_pos hAp, hw p hAp hB, Fintype.sum_eq_single (tl p), Fintype.sum_eq_single ⟨br p, hB⟩]
        · simp [hI]
          ring
        · intro q hq
          rw [if_neg]
          · simp
          · rintro ⟨_, _, h⟩
            exact hq (Subtype.ext h.symm)
        · intro x hx
          apply Finset.sum_eq_zero
          intro q _
          rw [if_neg]
          · simp
          · rintro ⟨_, h, _⟩
            exact hx h.symm
      · rw [dif_neg (fun h => hB ((hA p).1 h).2)]
        apply Finset.sum_eq_zero
        intro x _
        apply Finset.sum_eq_zero
        intro q _
        rw [if_neg]
        · simp
        · rintro ⟨_, _, h⟩
          exact hB (h ▸ q.2)
    · rw [dif_neg (fun h => hI ((hA p).1 h).1)]
      simp [hI]
  simp only [finsum_eq_sum_of_fintype, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun x _ => Finset.sum_comm, Finset.sum_comm,
    Finset.sum_congr rfl fun p _ => key p, ← Fintype.sum_subtype_add_sum_subtype A,
    Finset.sum_congr rfl fun p _ => dif_pos p.2,
    Finset.sum_congr rfl (fun (p : {p // ¬A p}) _ => dif_neg p.2), Finset.sum_const_zero, add_zero]

theorem UpperTheory.Gal.InertialTypesAlt.frobL :
    FrobTwo → ResCl → ParCons → FrobL := by
  intro hF2 hRes hPar F _ _ s
  induction s with
  | zero =>
    intro d n hd
    refine ⟨1, one_ne_zero, fun Y T _ => ?_⟩
    have hn : n = 0 := by rw [← hd]; simp
    subst hn
    have hall : ∀ g : GL (Fin 0) F, g ∈ GlobalTheory.SmGL.parab F (GlobalTheory.SmGL.stdBlocks d hd) :=
      fun g => GlobalTheory.SmGL.mem_parab_iff.2 fun a => a.elim0
    simp only [List.ofFn_zero, hcL_nil, star_one, one_mul, Fin.prod_univ_zero]
    exact (finsum_comp_equiv (Equiv.subtypeUnivEquiv hall)).symm
  | succ s ih =>
    intro d n hd
    have hn : n = d 0 + ∑ i : Fin s, d i.succ := by rw [← hd, Fin.sum_univ_succ]
    obtain ⟨c1, hc1, h1⟩ := hF2 F (d 0) (∑ i : Fin s, d i.succ) n hn
    obtain ⟨c2, hc2, h2⟩ := ih (fun i => d i.succ) _ rfl
    refine ⟨c1 * c2, mul_ne_zero hc1 hc2, fun Y T hT => ?_⟩
    have htail : (List.map Sigma.fst (List.ofFn fun i : Fin s =>
        (⟨d i.succ, Y i.succ⟩ : Σ m : ℕ, GL (Fin m) F → ℂ))).sum = ∑ i : Fin s, d i.succ := by
      simp [List.sum_ofFn]
    rw [List.ofFn_succ, hcL_cons_of _ _ _ htail, h1 _ _ T hT]
    have h2' := fun x => h2 (fun i => Y i.succ) _ (hRes F _ _ n hn T hT x)
    rw [finsum_congr fun x => by rw [h2' x, mul_left_comm], ← mul_finsum, ← mul_assoc]
    clear h1 h2 h2' ih htail hF2 hRes
    refine congrArg (c1 * c2 * ·) ?_
    unfold UpperTheory.Gal.InertialTypesAlt.resT
    have hc := collapse (fun p => p ∈ GlobalTheory.SmGL.parab F (GlobalTheory.SmGL.stdBlocks d hd))
      (fun z => z ∈ GlobalTheory.SmGL.parab F (GlobalTheory.SmGL.stdBlocks (fun i => d i.succ) rfl))
      (GlobalTheory.Shin.InPar (d 0)) (GlobalTheory.Shin.tlG (d 0)) (GlobalTheory.Shin.brG (d 0) _)
      (fun p => (hPar F s n d hd _ rfl p).1) (fun x => star (Y 0 x))
      (fun p' => star (∏ i, Y i.succ (GlobalTheory.SmGL.leviProj F (GlobalTheory.SmGL.stdBlocks (fun i => d i.succ) rfl) p' i)))
      T (fun p => star (∏ i, Y i (GlobalTheory.SmGL.leviProj F (GlobalTheory.SmGL.stdBlocks d hd) p i))) (by
        intro p hp hp'
        obtain ⟨h0, hs⟩ := (hPar F s n d hd _ rfl p).2 hp hp'
        rw [Fin.prod_univ_succ, h0, star_mul']
        congr 2
        exact Finset.prod_congr rfl fun i _ => by rw [hs i])
    convert hc
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PResEmbCompat
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem pow_self_of_alg (k : Type) [Field k] [Finite k] (x : AlgebraicClosure k) :
    ∃ c : ℕ, 2 ≤ c ∧ x ^ c = x := by
  have hx : IsIntegral k x := Algebra.IsIntegral.isIntegral x
  haveI : FiniteDimensional k (IntermediateField.adjoin k {x}) := IntermediateField.adjoin.finiteDimensional hx
  haveI : Finite (IntermediateField.adjoin k {x}) := Module.finite_of_finite k
  haveI : Fintype (IntermediateField.adjoin k {x}) := Fintype.ofFinite _
  refine ⟨Fintype.card (IntermediateField.adjoin k {x}), Fintype.one_lt_card, ?_⟩
  have h := FiniteField.pow_card (⟨x, IntermediateField.mem_adjoin_simple_self k x⟩ : IntermediateField.adjoin k {x})
  exact congrArg Subtype.val h

private theorem exists_preimage {F F' R : Type} [Field F] [Field F'] [IsAlgClosed F'] [Field R]
    (e : F →+* R) (e' : F' →+* R) (h : ∀ x : F, ∃ c : ℕ, 2 ≤ c ∧ x ^ c = x) (x : F) :
    ∃ y, e' y = e x := by
  obtain ⟨c, hc, hx⟩ := h x
  have hmon : (X ^ c - X : Polynomial F').Monic := by
    apply monic_X_pow_sub
    rw [degree_X]
    exact_mod_cast (by omega : 1 < c)
  have hroots := hmon.roots_map_of_card_eq_natDegree e' IsAlgClosed.card_roots_eq_natDegree
  have hmem : e x ∈ ((X ^ c - X : Polynomial F').map e').roots := by
    rw [mem_roots (map_monic_ne_zero hmon)]
    simp only [IsRoot, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, eval_sub, eval_pow, eval_X]
    rw [← map_pow, hx, sub_self]
  rw [← hroots, Multiset.mem_map] at hmem
  obtain ⟨y, -, hy⟩ := hmem
  exact ⟨y, hy⟩

private theorem exists_equiv_of_fin {k k' R : Type} [Field k] [Field k'] [Finite k] [Finite k'] [Field R]
    (e : AlgebraicClosure k →+* R) (e' : AlgebraicClosure k' →+* R) :
    ∃ j : AlgebraicClosure k ≃+* AlgebraicClosure k', ∀ x, e' (j x) = e x := by
  have h1 : ∀ x, ∃ y, e' y = e x := fun x => exists_preimage e e' (pow_self_of_alg k) x
  have h2 : ∀ x, ∃ y, e y = e' x := fun x => exists_preimage e' e (pow_self_of_alg k') x
  have hr : e.range = e'.range := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨y, hy⟩ := h1 x
      exact ⟨y, hy⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨y, hy⟩ := h2 x
      exact ⟨y, hy⟩
  let φ := RingEquiv.ofBijective e.rangeRestrict
    ⟨fun a b hab => e.injective (congrArg Subtype.val hab), e.rangeRestrict_surjective⟩
  let ψ := RingEquiv.ofBijective e'.rangeRestrict
    ⟨fun a b hab => e'.injective (congrArg Subtype.val hab), e'.rangeRestrict_surjective⟩
  refine ⟨φ.trans ((RingEquiv.subringCongr hr).trans ψ.symm), fun x => ?_⟩
  have hq := ψ.apply_symm_apply ((RingEquiv.subringCongr hr) (φ x))
  exact congrArg Subtype.val hq

private theorem val_le_one_iff {k : Type} [Field k] [ValuativeRel k] {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (u : Valuation k Γ) (hu : (valuation k).IsEquiv u) (x : k) : x ∈ 𝒪[k] ↔ u x ≤ 1 := hu.le_one_iff_le_one

private theorem isUnit_iff_val {k : Type} [Field k] [ValuativeRel k] {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (u : Valuation k Γ) (hu : (valuation k).IsEquiv u) (x : 𝒪[k]) : IsUnit x ↔ u (x : k) = 1 := by
  exact (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.trans hu.eq_one_iff_eq_one

theorem UpperTheory.Gal.InertialTypesAlt.resEmbCompat :
    ResEmbCompat := by
  intro K M Ω _ _ _ _ _ _ _ _ _ A v w e e' he he'
  obtain ⟨j, hj⟩ := exists_equiv_of_fin e e'
  have eqv : (valuation (v.adicCompletion K)).IsEquiv Valued.v := ValuativeRel.isEquiv _ _
  have eqw : (valuation (w.1.adicCompletion M)).IsEquiv Valued.v := ValuativeRel.isEquiv _ _
  have he0 : w.1.asIdeal.ramificationIdx (𝓞 K) ≠ 0 := (Ideal.ramificationIdx_pos (R := 𝓞 K) w.1.asIdeal).ne'
  let f : 𝒪[v.adicCompletion K] →+* 𝒪[w.1.adicCompletion M] :=
    (completionMap v w.1).comp (algebraMap 𝒪[v.adicCompletion K] (v.adicCompletion K)) |>.codRestrict
      (𝒪[w.1.adicCompletion M]) (fun x => by
        refine (val_le_one_iff _ eqw _).2 ?_
        change Valued.v (completionMap v w.1 x) ≤ 1
        rw [valued_completionMap]
        exact pow_le_one' ((val_le_one_iff _ eqv _).1 x.2) _)
  have hf : ∀ x, ((f x : 𝒪[w.1.adicCompletion M]) : w.1.adicCompletion M) = completionMap v w.1 x := fun _ => rfl
  haveI : IsLocalHom f := ⟨fun a ha => by
    rw [isUnit_iff_val _ eqw, hf, valued_completionMap] at ha
    rw [isUnit_iff_val _ eqv]
    exact (pow_eq_one_iff.1 ha).resolve_right he0⟩
  refine ⟨IsLocalRing.ResidueField.map f, j, fun x y hy => ?_, fun x => ?_, hj⟩
  · rw [IsLocalRing.ResidueField.map_residue]
    congr 1
    exact Subtype.ext hy
  · obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
    have hy1 : Valued.v (y : v.adicCompletion K) ≤ 1 := (val_le_one_iff _ eqv _).1 y.2
    obtain ⟨a, ha⟩ := DiscreteGroups.sglob.DzType.exists_int_approx_compl v (y : v.adicCompletion K) hy1
    have hb1 : Valued.v (algebraMap K (v.adicCompletion K) (a : K)) ≤ 1 := by
      have e2 : algebraMap K (v.adicCompletion K) (a : K) =
          (y : v.adicCompletion K) - ((y : v.adicCompletion K) - algebraMap K (v.adicCompletion K) (a : K)) := by ring
      rw [e2]
      exact (Valuation.map_sub _ _ _).trans (max_le hy1 ha.le)
    let b : 𝒪[v.adicCompletion K] := ⟨algebraMap K _ (a : K), (val_le_one_iff _ eqv _).2 hb1⟩
    have hyb : IsLocalRing.residue _ y = IsLocalRing.residue _ b := by
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        isUnit_iff_val _ eqv]
      exact ha.ne
    let a' : 𝓞 M := algebraMap (𝓞 K) (𝓞 M) a
    have ha' : (a' : M) = algebraMap K M (a : K) := rfl
    let z : A := ⟨algebraMap K Ω (a : K), mem_of_isIntegral_int A
      ((RingOfIntegers.isIntegral_coe a).map (IsScalarTower.toAlgHom ℤ K Ω))⟩
    have h1 := he a b z rfl rfl
    have h2 := he' a' (f b) z (by
      rw [hf, ha']
      change completionMap v w.1 (algebraMap K _ (a : K)) = _
      rw [completionMap_algebraMap]
      exact IsScalarTower.algebraMap_apply K M (w.1.adicCompletion M) _) (by
      rw [ha', ← IsScalarTower.algebraMap_apply])
    apply e'.injective
    rw [hj, hyb, h1, IsLocalRing.ResidueField.map_residue, h2]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PResEmbEx
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ResAlgClosed
theorem UpperTheory.Reformulated.B.Qk69.res_algClosed :
    ∀ {Ω : Type} [inst : Field Ω] [IsAlgClosed Ω]
    (A : ValuationSubring Ω), IsAlgClosed (IsLocalRing.ResidueField ↥A) := by
  intro Ω _ _ A
  refine IsAlgClosed.of_exists_root _ fun p hp hirr => ?_
  have hsurj : Function.Surjective (IsLocalRing.residue A) := IsLocalRing.residue_surjective
  have hl : p ∈ Polynomial.lifts (IsLocalRing.residue A) :=
    (Polynomial.mem_lifts _).2 (Polynomial.map_surjective _ hsurj p)
  obtain ⟨q, hq, hdeg, hm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl hp
  have hd : q.degree ≠ 0 := by
    rw [hdeg]
    exact (Polynomial.degree_pos_of_irreducible hirr).ne'
  have hinj : Function.Injective (algebraMap A Ω) := Subtype.val_injective
  have hd' : (q.map (algebraMap A Ω)).degree ≠ 0 := by
    rwa [hm.degree_map]
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hd'
  have hx' : Polynomial.eval₂ (algebraMap A Ω) x q = 0 := by
    rw [← Polynomial.eval_map]
    exact hx
  have hint : IsIntegral A x := ⟨q, hm, hx'⟩
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  have hy : q.eval y = 0 := by
    apply hinj
    rw [Polynomial.eval₂_at_apply] at hx'
    rw [hx', map_zero]
  refine ⟨IsLocalRing.residue A y, ?_⟩
  rw [← hq, Polynomial.eval_map, Polynomial.eval₂_at_apply, hy, map_zero]
end

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem res_algClosed {Ω : Type} [Field Ω] [IsAlgClosed Ω] (A : ValuationSubring Ω) :
    IsAlgClosed (IsLocalRing.ResidueField A) :=
  _root_.UpperTheory.Reformulated.B.Qk69.res_algClosed A

private theorem res_surj {Ω : Type} [Field Ω] [CharZero Ω] (hΩ : ∀ x : Ω, IsAlgebraic ℤ x) (A : ValuationSubring Ω) {κ : Type} [Field κ]
    [IsAlgClosed κ] (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
    (e : κ →+* IsLocalRing.ResidueField A) : Function.Surjective e := by
  letI := e.toAlgebra
  haveI : Algebra.IsIntegral κ (IsLocalRing.ResidueField A) := ⟨fun z => by
    obtain ⟨z', rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨P₀, h0, hP₀⟩ := hΩ (z' : Ω)
    have hP : aeval (z' : Ω) P₀.primPart = 0 := by
      have h1 := congrArg (aeval (z' : Ω)) P₀.eq_C_content_mul_primPart
      rw [hP₀, map_mul, aeval_C] at h1
      have h2 : algebraMap ℤ Ω P₀.content ≠ 0 := by
        simpa [Polynomial.content_eq_zero_iff] using h0
      exact (mul_eq_zero.1 h1.symm).resolve_left h2
    have hA : aeval z' P₀.primPart = 0 := by
      have h1 := aeval_algebraMap_apply Ω z' P₀.primPart
      change aeval (z' : Ω) _ = _ at h1
      rw [hP] at h1
      exact Subtype.val_injective h1.symm
    have hR : aeval (IsLocalRing.residue A z') P₀.primPart = 0 := by
      have h1 := aeval_algebraMap_apply (IsLocalRing.ResidueField A) z' P₀.primPart
      rw [hA, map_zero] at h1
      exact h1
    have hQ : P₀.primPart.map (algebraMap ℤ κ) ≠ 0 := by
      intro h
      have hdvd : C (p : ℤ) ∣ P₀.primPart := (C_dvd_iff_dvd_coeff _ _).2 fun n => by
        have h1 := congrArg (fun q => q.coeff n) h
        simp only [coeff_map, coeff_zero] at h1
        have h2 := congrArg e h1
        simp only [eq_intCast, map_intCast, map_zero] at h2
        exact (CharP.intCast_eq_zero_iff _ p _).1 h2
      exact (Nat.prime_iff_prime_int.1 Fact.out).not_unit (P₀.isPrimitive_primPart _ hdvd)
    refine IsAlgebraic.isIntegral ⟨_, hQ, ?_⟩
    rw [aeval_def, eval₂_map, Subsingleton.elim ((algebraMap κ (IsLocalRing.ResidueField A)).comp (algebraMap ℤ κ))
      (algebraMap ℤ (IsLocalRing.ResidueField A))]
    exact hR⟩
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := κ) (K := IsLocalRing.ResidueField A)).2

theorem UpperTheory.Gal.InertialTypesAlt.resEmbEx :
    ResEmbEx := by
  intro E Ω _ _ _ _ _ A v hv
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI := res_algClosed A
  obtain ⟨e₀, he₀⟩ : ∃ e₀ : 𝓀[v.adicCompletion E] →+* IsLocalRing.ResidueField A,
      ∀ x, e₀ (DiscreteGroups.sglob.DzType.kappaP v x) = DiscreteGroups.sglob.DzType.kappaQ A x := by
    refine ⟨RingHom.liftOfSurjective _ (DiscreteGroups.sglob.DzType.kappa_surj_O v) ⟨DiscreteGroups.sglob.DzType.kappaQ A, fun x hx => ?_⟩,
      fun x => ?_⟩
    · rw [DiscreteGroups.sglob.DzType.kappa_ker_O, ← DiscreteGroups.sglob.DzType.kappa_ker_A A v hv] at hx
      exact hx
    · exact RingHom.liftOfRightInverse_comp_apply _ _ _ _ _
  obtain ⟨p, hp⟩ := CharP.exists 𝓀[v.adicCompletion E]
  haveI : Fact p.Prime := ⟨CharP.char_is_prime 𝓀[v.adicCompletion E] p⟩
  haveI : CharP (IsLocalRing.ResidueField A) p := charP_of_injective_ringHom e₀.injective p
  letI := e₀.toAlgebra
  let e : AlgebraicClosure 𝓀[v.adicCompletion E] →ₐ[𝓀[v.adicCompletion E]] IsLocalRing.ResidueField A := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hres : ResEmb A v (e : AlgebraicClosure 𝓀[v.adicCompletion E] →+* IsLocalRing.ResidueField A) := by
    intro x y z hy hz
    have h1 : IsLocalRing.residue 𝒪[v.adicCompletion E] y = DiscreteGroups.sglob.DzType.kappaP v x := by
      rw [DiscreteGroups.sglob.DzType.kappaP, RingHom.comp_apply]
      exact congrArg _ (Subtype.ext hy)
    have h2 : IsLocalRing.residue A z = DiscreteGroups.sglob.DzType.kappaQ A x := by
      rw [DiscreteGroups.sglob.DzType.kappaQ, RingHom.comp_apply]
      exact congrArg _ (Subtype.ext hz)
    rw [h1, h2, ← he₀]
    exact e.commutes _
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have hΩ : ∀ x : Ω, IsAlgebraic ℤ x := by
    haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
    haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ E Ω
    exact fun x => (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).2 (Algebra.IsAlgebraic.isAlgebraic x)
  have hs := res_surj hΩ A p (e : AlgebraicClosure 𝓀[v.adicCompletion E] →+* IsLocalRing.ResidueField A)
  let e' := RingEquiv.ofBijective (e : AlgebraicClosure 𝓀[v.adicCompletion E] →+* IsLocalRing.ResidueField A)
    ⟨RingHom.injective _, hs⟩
  obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_teichmuller_map_algebraicClosure_finiteField 𝓀[v.adicCompletion E]
  refine ⟨⟨_, hres⟩, θ.comp (e'.symm : IsLocalRing.ResidueField A →* _), fun x y hx hy h => ?_⟩
  exact e'.symm.injective (hθ _ _ (by simpa using hx) (by simpa using hy) h)
end
