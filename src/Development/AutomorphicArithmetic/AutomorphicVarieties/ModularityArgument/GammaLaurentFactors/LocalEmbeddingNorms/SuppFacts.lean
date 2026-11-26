module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.MatchIndOf
public import Development.WeilBound.CoreStatements.PublishedTheorems.FiniteGLInvariants.AffineLieInvariants.Imports
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvOneSubBound
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.EigOfSat

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.SuppFacts
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.Gam

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}

private theorem supp_unique {π : Representation ℂ (GL (Fin n) k) V} {s t : Multiset (IrrGL (k := k))}
    (hs : HasSupport π s) (ht : HasSupport π t) : s = t :=
  GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique GlobalTheory.CompanionTheory.GeoLink.geometricLemma GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness hs ht

private theorem supp_exists {π : Representation ℂ (GL (Fin n) k) V} (h1 : IsSmooth π) (h2 : π.IsIrreducible) :
    ∃ s, HasSupport π s := by
  obtain ⟨s, hs⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_hasSupport GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
    GlobalTheory.CompanionTheory.GeoLink.geometricLemma (IrrGL.of π h1 h2)
  exact ⟨s, hs.of_equiv (IrrGL.equivOf π h1 h2).symm⟩

private theorem unram_of_fixed [CharZero k] {π : Representation ℂ (GL (Fin n) k) V} {s : Multiset (IrrGL (k := k))}
    (hs : HasSupport π s) {v : V} (h0 : v ≠ 0) (hv : ∀ g ∈ KO k (Fin n), π g v = v) : ∀ y ∈ s, y.IsUnramChar := by
  obtain ⟨α, hα⟩ := GlobalTheory.SatakeExists.exists_isSubquotient_prinSeries
    ((GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k).1 (Fin n) V π hs.isSmooth hs.isIrreducible) hs.isIrreducible
    ((Submodule.ne_bot_iff _).2 ⟨v, fun g => by simpa using hv g.1 (iwahori_le_KO k _ g.2), h0⟩)
  have h := GlobalTheory.LocLanglands.hasSupport_of_isSubquotient_prinSeries k n (fun i => unrChar k (α i))
    (fun i => isSmoothChar_of_isUnram (isUnram_unrChar k (α i))) ⟨V, π, hs.isSmooth, hs.isIrreducible⟩ hα
  rw [supp_unique hs h]
  intro y hy
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
  exact ⟨_, isUnram_unrChar k (α i), rfl⟩

private theorem tw_iff (y : IrrGL (k := k)) (χ θ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    (∃ ξ hξ, y.tw χ hχ = IrrGL.ofChar ξ hξ ∧ IsUnram (ξ * θ)) ↔
      ∃ ξ hξ, y = IrrGL.ofChar ξ hξ ∧ IsUnram (ξ * (χ * θ)) := by
  constructor
  · rintro ⟨ξ, hξ, e, hu⟩
    refine ⟨ξ * χ⁻¹, hξ.mul hχ.inv, ?_, ?_⟩
    · rw [← IrrGL.tw_ofChar ξ χ⁻¹ hξ hχ.inv, ← e, IrrGL.tw_tw_inv]
    · rwa [mul_assoc, inv_mul_cancel_left]
  · rintro ⟨ξ, hξ, rfl, hu⟩
    exact ⟨ξ * χ, hξ.mul hχ, IrrGL.tw_ofChar _ _ _ _, by rwa [mul_assoc]⟩

end Loc

section Glob

variable {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {n : ℕ}

omit [_root_.NumberField.IsTotallyComplex K] in
private theorem smooth_loc (χ : HChar K) (v : HeightOneSpectrum (𝓞 K)) : IsSmoothChar (χ.loc v) :=
  GlobalTheory.HeckeComp.smooth_loc χ v

private theorem exists_fixed {π : CuspSub K n} {v : HeightOneSpectrum (𝓞 K)} {σ : SmIrr (GL (Fin n) (v.adicCompletion K))}
    (hσ : π.IsLocComp v σ) {B : Multiset ℂˣ} (hB : (CG.mk π).HasSat v B) :
    ∃ y : σ.V, y ≠ 0 ∧ ∀ g ∈ KO (v.adicCompletion K) (Fin n), σ.ρ g y = y := by
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 ((CG.hasSat_mk π v B).1 hB).1
  rw [show KO (v.adicCompletion K) (Fin n) = GlobalTheory.LFun.KGL v (n := n) from SphCompletion.KO_completion v n]
  exact LocSph.exists_fixed_of_mem_iSup ((finRep K n).comp (locGL K n v)) σ.ρ σ.irred
    (fun f : LocSph.Maps π v σ => f.1) (fun f => f.2.2) (GlobalTheory.LFun.KGL v (n := n) : Set _) x.1 (fun e => hx0 (Subtype.ext e))
    (fun g hg => congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hx g hg))
    ((LocSph.iSup_range_eq π v σ hσ).symm ▸ x.2)

private theorem supp_twist {v : HeightOneSpectrum (𝓞 K)} {σ : SmIrr (GL (Fin n) (v.adicCompletion K))} (χ : HChar K)
    {s : Multiset (IrrGL (k := v.adicCompletion K))} (h : HasSupport σ.ρ s) :
    HasSupport (σ.twist (CuspSub.locDet n χ v) (CuspSub.isOpen_ker_locDet χ v)).ρ
      (s.map (·.tw (χ.loc v) (smooth_loc χ v))) :=
  h.tw (χ.loc v) (smooth_loc χ v)

end Glob

end UpperTheory.V.Z.Gam

open UpperTheory.V.Z.Gam in
theorem UpperTheory.V.Z.Gam.suppFacts :
    UpperTheory.V.Z.Gam.SuppFacts := by
  intro K _ _ _ n _ π v
  have uniq : ∀ {σ σ' s}, π.IsLocComp v σ → π.IsLocComp v σ' → HasSupport σ.ρ s → HasSupport σ'.ρ s :=
    fun h h' hs => hs.of_equiv (LocUniq.isLocComp_unique π v _ _ h h').some
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp CuspFormAutomorphicBounds.automorphicFormsFiniteGL K n π v
    obtain ⟨s, hs⟩ := supp_exists σ.smooth σ.irred
    exact ⟨s, σ, hσ, hs⟩
  · rintro s s' ⟨σ, hσ, hs⟩ ⟨σ', hσ', hs'⟩
    exact supp_unique (uniq hσ hσ' hs) hs'
  · rintro s ⟨σ, hσ, hs⟩
    refine ⟨⟨fun h => ?_, fun h σ' hσ' => ?_⟩, by simpa using hs.sum_fst, fun y hy => (hs.isCusp hy).1⟩
    · obtain ⟨t, ht, h1⟩ := h σ hσ
      rwa [supp_unique hs (ht.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm)]
    · exact ⟨s, (uniq hσ hσ' hs).of_equiv (IrrGL.equivOf σ'.ρ σ'.smooth σ'.irred), h⟩
  · rintro s B ⟨σ, hσ, hs⟩ hB
    obtain ⟨y, h0, hy⟩ := exists_fixed hσ hB
    haveI : CharZero (v.adicCompletion K) := charZero_of_injective_algebraMap (algebraMap K _).injective
    exact unram_of_fixed hs h0 hy
  · rintro χ s ⟨σ, hσ, hs⟩
    refine ⟨_, ⟨_, hσ.twist χ, supp_twist χ hs⟩, fun θ => ?_, ?_⟩
    · unfold cnt
      rw [Multiset.filter_map, Multiset.card_map]
      exact congrArg Multiset.card (Multiset.filter_congr fun y _ => tw_iff y (χ.loc v) θ _)
    · rw [Multiset.map_map]
      rfl
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.NormLoc
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.Gam

theorem normLoc : NormLoc := by
  intro K L _ _ _ _ _ χ
  let ξ : HChar L := ⟨χ.1.comp (GroundTheory.Global.ideleNorm K L), χ.2.1.comp GroundTheory.Global.continuous_ideleNorm, fun k =>
    (congrArg χ.1 (GroundTheory.Global.ideleNorm_diagonal (K := K) k)).trans (χ.2.2 _)⟩
  refine ⟨ξ, ?_⟩
  rintro v ⟨w, hw⟩
  have hN : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ fdeg (⟨w, hw⟩ : PlacesOver L v) :=
    Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.asIdeal v.asIdeal v.isPrime v.ne_bot
  obtain rfl : v = w.under (𝓞 K) := HeightOneSpectrum.ext hw.over
  refine ⟨MonoidHom.ext fun x => ?_, GlobalTheory.NormValGen.unrAt_val_of_comp_norm K L χ ξ (fun _ => rfl) w _ ?_, hN⟩
  exact congrArg χ.1 (GroundTheory.Global.ideleNorm_finiteEmbedding (K := K) w x)
  simpa only [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using hN

end UpperTheory.V.Z.Gam
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.NormCnt
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.SmGL GlobalTheory.SplitWeil
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.SemiLocal
open scoped Classical

namespace UpperTheory.V.Z.Gam

private theorem count_one {A : Type} [CommGroup A] (U : Subgroup A) (l : ℕ) (hl : l.Prime) (η θ : A →* ℂˣ)
    (hη : ∀ x, η x ^ l = 1) (hθ : ∀ x ∈ U, η x = 1 → θ x = 1) (u : A) (hu : u ∈ U) (h1 : η u ≠ 1) :
    ((Finset.range l).filter fun j => ∀ x ∈ U, θ x * η x ^ j = 1).card = 1 := by
  haveI : Fact l.Prime := ⟨hl⟩
  haveI : NeZero l := ⟨hl.ne_zero⟩
  have hp : IsPrimitiveRoot (η u) l := by
    rw [← orderOf_eq_prime (hη u) h1]
    exact IsPrimitiveRoot.orderOf _
  have h2 : (θ u)⁻¹ ∈ rootsOfUnity l ℂ := by
    rw [mem_rootsOfUnity, inv_pow, ← map_pow, hθ _ (U.pow_mem hu l) (by rw [map_pow, hη]), inv_one]
  obtain ⟨j, hj, e⟩ := hp.eq_pow_of_mem_rootsOfUnity h2
  rw [Finset.card_eq_one]
  refine ⟨j, Finset.eq_singleton_iff_unique_mem.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, fun x hx => ?_⟩, fun i hi => ?_⟩⟩
  · obtain ⟨m, -, hm⟩ := hp.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity l (η x)).2 (hη x))
    have h3 := hθ (x * (u ^ m)⁻¹) (U.mul_mem hx (U.inv_mem (U.pow_mem hu m)))
      (by rw [map_mul, map_inv, map_pow, hm, mul_inv_cancel])
    rw [map_mul, map_inv, mul_inv_eq_one, map_pow] at h3
    rw [h3, ← hm, ← pow_mul, mul_comm m, pow_mul, e, ← mul_pow, mul_inv_cancel, one_pow]
  · obtain ⟨hi, h⟩ := Finset.mem_filter.1 hi
    refine hp.pow_inj (Finset.mem_range.1 hi) hj ?_
    rw [e]
    exact (eq_inv_of_mul_eq_one_right (h u hu))

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] {v : HeightOneSpectrum (𝓞 K)}

private theorem fdeg_eq (w : PlacesOver L v) : fdeg w = w.1.asIdeal.inertiaDeg (𝓞 K) := by
  have := w.1.isMaximal
  have := v.isMaximal
  exact Ideal.inertiaDeg'_eq_inertiaDeg _ _

private theorem fdeg_pos (w : PlacesOver L v) : 0 < fdeg w := by
  have := w.1.isPrime
  rw [fdeg_eq]
  exact Ideal.inertiaDeg_pos _ _

private theorem ord_nm (w : PlacesOver L v) (x : (w.1.adicCompletion L)ˣ) :
    ord ((nm w x : (v.adicCompletion K)ˣ) : v.adicCompletion K) = fdeg w * ord (x : w.1.adicCompletion L) := by
  rw [fdeg_eq, ← inertiaDeg_integer v w.1]
  exact ord_norm (x : w.1.adicCompletion L)

private theorem unr_iff (θ : (v.adicCompletion K)ˣ →* ℂˣ) :
    IsUnram θ ↔ ∀ x ∈ unitFiltrationUnits (v.adicCompletion K) 0, θ x = 1 :=
  forall_congr' fun _ => by rw [mem_unitFiltrationUnits_zero_iff]

private theorem unr_nm (w : PlacesOver L v) (θ : (v.adicCompletion K)ˣ →* ℂˣ) :
    IsUnram (θ.comp (nm w)) ↔ ∀ x ∈ unitFiltrationUnits (v.adicCompletion K) 0, x ∈ (nm w).range → θ x = 1 := by
  rw [unr_iff]
  constructor
  · rintro h _ hx ⟨y, rfl⟩
    refine h y ?_
    rw [← ord_eq_zero_iff_mem, ord_nm] at hx
    exact ord_eq_zero_iff_mem.1 ((mul_eq_zero.1 hx).resolve_left (by exact_mod_cast (fdeg_pos w).ne'))
  · intro h y hy
    refine h _ ?_ ⟨y, rfl⟩
    rw [← ord_eq_zero_iff_mem, ord_nm, ord_eq_zero_iff_mem.2 hy, mul_zero]

private theorem sum_ef (v : HeightOneSpectrum (𝓞 K)) :
    ∑ w : PlacesOver L v, w.1.asIdeal.ramificationIdx (𝓞 K) * fdeg w = Module.finrank K L := by
  have := v.isMaximal
  rw [Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 K) K (𝓞 L) L,
    ← Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 L)]
  exact Fintype.sum_equiv (placesOverEquiv L v) _ _ fun w => by rw [fdeg_eq]; rfl

private theorem gal_e [IsGalois K L] (w w' : PlacesOver L v) :
    w.1.asIdeal.ramificationIdx (𝓞 K) = w'.1.asIdeal.ramificationIdx (𝓞 K) ∧ fdeg w = fdeg w' := by
  have := w.1.isPrime
  have := w'.1.isPrime
  have hw : w.1.asIdeal.LiesOver v.asIdeal := w.2
  have e : w.1.asIdeal.under (𝓞 K) = w'.1.asIdeal.under (𝓞 K) := w.2.over.symm.trans w'.2.over
  obtain ⟨σ, hσ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 K) (𝓞 L) (L ≃ₐ[K] L) _ _ e
  rw [fdeg_eq, fdeg_eq, hσ]
  exact ⟨(Ideal.ramificationIdx_smul _ _ σ).symm, (Ideal.inertiaDeg_smul _ _ σ).symm⟩

private theorem prim (η : HChar K) (w : PlacesOver L v) (hk : (η.loc v).ker = (nm w).range)
    (hu : unitFiltrationUnits (v.adicCompletion K) 0 ≤ (η.loc v).ker) :
    η.UnrAt v ∧ IsPrimitiveRoot (η.val v) (fdeg w) := by
  have h1 : η.UnrAt v := fun x hx => hu (mem_unitFiltrationUnits_zero_iff_valued.2 hx)
  obtain ⟨π, hπ, hπ'⟩ := exists_ord_eq_one_valued v
  obtain ⟨ϖ, hϖ⟩ := exists_ord_eq_one_units (w.1.adicCompletion L)
  refine ⟨h1, ?_⟩
  rw [← η.val_eq h1 π hπ']
  constructor
  · have h2 : π ^ (fdeg w : ℤ) * (nm w ϖ)⁻¹ ∈ (η.loc v).ker := by
      apply hu
      rw [← ord_eq_zero_iff_mem, Units.val_mul, ord_mul (Units.ne_zero _) (Units.ne_zero _), ← map_inv, ord_nm,
        ord_zpow_units hπ, ← zpow_neg_one, ord_zpow_units hϖ]
      ring
    have h3 : nm w ϖ ∈ (η.loc v).ker := hk ▸ ⟨ϖ, rfl⟩
    rw [MonoidHom.mem_ker] at h2 h3
    rwa [map_mul, map_inv, h3, inv_one, mul_one, zpow_natCast, map_pow] at h2
  · intro m hm
    rw [← map_pow, ← MonoidHom.mem_ker, hk] at hm
    obtain ⟨y, hy⟩ := hm
    have h4 := ord_nm w y
    rw [hy, ← zpow_natCast, ord_zpow_units hπ] at h4
    exact Int.natCast_dvd_natCast.1 ⟨_, h4⟩

private theorem exists_eta [IsGalois K L] (hl : (Module.finrank K L).Prime) :
    ∃ η : HChar K, ∀ v : HeightOneSpectrum (𝓞 K), (∀ x, η.loc v x ^ Module.finrank K L = 1) ∧
      ∀ w : PlacesOver L v, (η.loc v).ker = (nm w).range ∧
        (unitFiltrationUnits (v.adicCompletion K) 0 ≤ (nm w).range ↔ w.1.asIdeal.ramificationIdx (𝓞 K) = 1) := by
  haveI : Fact (Module.finrank K L).Prime := ⟨hl⟩
  haveI : NeZero (Module.finrank K L) := ⟨hl.ne_zero⟩
  have hc : Nat.card (L ≃ₐ[K] L) = Module.finrank K L := IsGalois.card_aut_eq_finrank K L
  haveI : IsCyclic (L ≃ₐ[K] L) := isCyclic_of_prime_card hc
  haveI : IsMulCommutative (L ≃ₐ[K] L) := inferInstance
  let ι : (L ≃ₐ[K] L) →* ℂˣ := (rootsOfUnity (Module.finrank K L) ℂ).subtype.comp
    (mulEquivOfPrimeCardEq hc (Complex.card_rootsOfUnity _)).toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp (MulEquiv.injective _)
  have hm : ι.comp (ideleSymbol K L) ∈ hcharSub K :=
    ⟨(continuous_of_discreteTopology (f := ι)).comp (continuous_ideleSymbol L),
      fun k => (congrArg ι (ideleSymbol_diagonal (L := L) k)).trans (map_one ι)⟩
  refine ⟨⟨_, hm⟩, fun v => ?_⟩
  have e : HChar.loc (⟨ι.comp (ideleSymbol K L), hm⟩ : HChar K) v = ι.comp (localSymbol L v) :=
    MonoidHom.ext fun x => congrArg ι (ideleSymbol_finiteEmbedding (L := L) v x)
  rw [e]
  refine ⟨fun x => by rw [MonoidHom.comp_apply, ← map_pow, ← hc, pow_card_eq_one', map_one], fun w => ?_⟩
  have hk : (localSymbol L v).ker = (nm w).range := ker_localSymbol L v w
  refine ⟨by rw [MonoidHom.ker_comp_of_injective _ _ hι, hk], ?_⟩
  rw [← hk]
  refine ⟨fun h => ramificationIdx_eq_one_of_units_le_ker_localSymbol v h w.1, fun h x hx => ?_⟩
  refine units_le_ker_localSymbol L v w h ?_
  have h1 := mem_unitFiltrationUnits_zero_iff_valued.1 hx
  have h2 := mem_unitFiltrationUnits_zero_iff_valued.1 (inv_mem hx)
  exact (Submonoid.mem_units_iff _ _).2 ⟨h1.le, h2.le⟩

private theorem loc_pow (η : HChar K) (j : ℕ) (x : (v.adicCompletion K)ˣ) : (η ^ j).loc v x = η.loc v x ^ j := by
  induction j with
  | zero => simp [HChar.loc]
  | succ j ih =>
    simp only [HChar.loc, MonoidHom.comp_apply] at ih ⊢
    rw [pow_succ]
    change (η ^ j).1 (Neutral.B1.localIdele K v x) * η.1 (Neutral.B1.localIdele K v x) = _
    rw [ih, pow_succ]

end UpperTheory.V.Z.Gam

theorem UpperTheory.V.Z.Gam.normCnt :
    UpperTheory.V.Z.Gam.NormCnt := by
  intro K L _ _ _ _ _ _ hl
  obtain ⟨η, hη⟩ := exists_eta (K := K) (L := L) hl
  refine ⟨η, ?_, fun v w => ?_⟩
  · filter_upwards [IdeleNorm.eventually_forall_placesOver K (IdeleNorm.eventually_ramificationIdx_eq_one K L)] with v hv
    have h := fun w : PlacesOver L v =>
      prim η w ((hη v).2 w).1 (by rw [((hη v).2 w).1]; exact ((hη v).2 w).2.2 (hv w))
    obtain ⟨w₀⟩ := nonempty_placesOver L v
    refine ⟨(h w₀).1, fun w => ⟨(h w).2, ?_⟩⟩
    rw [← sum_ef v, Finset.sum_congr rfl fun w' _ => show _ = fdeg w by rw [hv w', one_mul, (gal_e w' w).2]]
    simp
  obtain ⟨hp, hw⟩ := hη v
  refine ⟨MonoidHom.ext fun y => ?_, fun w' θ h => ?_, fun θ hθ => ⟨?_, fun h => ?_, fun h => ?_⟩⟩
  · exact ((hw w).1.ge ⟨y, rfl⟩ :)
  · have h1 := (unr_nm w θ).1 h
    rw [← (hw w).1, (hw w').1] at h1
    exact (unr_nm w' θ).2 h1
  · unfold IsSmoothChar at hθ ⊢
    rw [← MonoidHom.comap_ker]
    exact hθ.preimage (continuous_normUnits (K := v.adicCompletion K) (L := w.1.adicCompletion L))
  · exact (unr_nm w θ).2 fun x hx _ => (unr_iff θ).1 h x hx
  have h1 := (unr_nm w θ).1 h
  have e : ∀ j : ℕ, IsUnram (θ * (η ^ j).loc v) ↔
      ∀ x ∈ unitFiltrationUnits (v.adicCompletion K) 0, θ x * η.loc v x ^ j = 1 := fun j => by
    rw [unr_iff]
    simp only [MonoidHom.mul_apply, loc_pow]
  have hs : w.1.asIdeal.ramificationIdx (𝓞 K) * ∑ w' : PlacesOver L v, fdeg w' = Module.finrank K L := by
    rw [← sum_ef v, Finset.mul_sum]
    exact Finset.sum_congr rfl fun w' _ => by rw [(gal_e w w').1]
  refine (congrArg Finset.card (Finset.filter_congr fun j _ => e j)).trans ?_
  by_cases hr : w.1.asIdeal.ramificationIdx (𝓞 K) = 1
  · rw [hr, one_mul] at hs
    rw [hs, Finset.filter_true_of_mem, Finset.card_range]
    intro j _ x hx
    have h2 := (hw w).2.2 hr hx
    rw [h1 x hx h2, show η.loc v x = 1 from (hw w).1.ge h2, one_pow, one_mul]
  · obtain ⟨u, hu, hu'⟩ := SetLike.not_le_iff_exists.1 (mt (hw w).2.1 hr)
    rw [← (hw w).1] at hu' h1
    rw [← hs] at hl
    have h3 := ((Nat.prime_mul_iff.1 hl).resolve_right fun h => hr h.2).2
    rw [hs] at hl
    rw [h3]
    convert count_one _ _ hl (η.loc v) θ hp h1 u hu hu'
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.RegroupBC
noncomputable section

open NumberField IsDedekindDomain Polynomial GlobalTheory.HenQ
open GroundTheory.Global.SemiLocal

namespace UpperTheory.V.Z.Gam

namespace BaseChangeLocalFactorRegrouping

private theorem one_period {f : ℕ} {ζ : ℂ} (h : IsPrimitiveRoot ζ f) (hf : 0 < f) (y : ℂ) :
    ∏ j ∈ Finset.range f, (1 - ζ ^ j * y) = 1 - y ^ f := by
  have h1 := congrArg (Polynomial.eval (1 : ℂ)) (X_pow_sub_C_eq_prod h hf (rfl : y ^ f = y ^ f))
  rw [Polynomial.eval_prod] at h1
  simpa using h1.symm

private theorem periods {f : ℕ} {ζ : ℂ} (h : IsPrimitiveRoot ζ f) (hf : 0 < f) (y : ℂ) (g : ℕ) :
    ∏ j ∈ Finset.range (g * f), (1 - ζ ^ j * y) = (1 - y ^ f) ^ g := by
  induction g with
  | zero => simp
  | succ g ih =>
    rw [Nat.succ_mul, Finset.prod_range_add, ih, pow_succ, ← one_period h hf y]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [pow_add, mul_comm g f, pow_mul, h.pow_eq_one, one_pow, one_mul]

private theorem fac_eq {f : ℕ} {ζ : ℂ} (h : IsPrimitiveRoot ζ f) (hf : 0 < f) (g : ℕ) (B : Multiset ℂ) (x : ℂ) :
    ∏ j ∈ Finset.range (g * f), ((B.map (· * ζ ^ j)).map fun b => (1 - b * x)⁻¹).prod =
      (((B.map (· ^ f)).map fun b => (1 - b * x ^ f)⁻¹).prod) ^ g := by
  induction B using Multiset.induction_on with
  | empty => simp
  | cons a B ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [Finset.prod_mul_distrib, ih, mul_pow, Finset.prod_inv_distrib, ← mul_pow a x, inv_pow, ← periods h hf]
    congr 2
    refine Finset.prod_congr rfl fun j _ => ?_
    ring

private theorem cast_pow_cpow (N f : ℕ) (z : ℂ) : (((N ^ f : ℕ)) : ℂ) ^ z = (((N : ℕ) : ℂ) ^ z) ^ f := by
  induction f with
  | zero => simp
  | succ f ih => rw [pow_succ, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, ih, pow_succ]

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem norm_eq {p : HeightOneSpectrum (𝓞 K)} (w : PlacesOver L p) :
    Ideal.absNorm w.1.asIdeal = Ideal.absNorm p.asIdeal ^ fdeg w :=
  Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.1.asIdeal p.asIdeal p.isPrime p.ne_bot

private theorem under_eq {p : HeightOneSpectrum (𝓞 K)} (w : PlacesOver L p) : w.1.under (𝓞 K) = p := by
  ext1
  rw [HeightOneSpectrum.under_asIdeal]
  exact w.2.over.symm

private theorem nonempty_over (p : HeightOneSpectrum (𝓞 K)) : Nonempty (PlacesOver L p) := by
  haveI := p.isMaximal
  obtain ⟨P, hPm, hP⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) p.asIdeal
  exact ⟨⟨⟨P, hPm.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot P⟩, hP⟩⟩

private theorem core (d : ℕ) (MainNotions : Set (HeightOneSpectrum (𝓞 K))) (SL : Set (HeightOneSpectrum (𝓞 L)))
    (BK : HeightOneSpectrum (𝓞 K) → Multiset ℂ) (BL : HeightOneSpectrum (𝓞 L) → Multiset ℂ)
    (e : HeightOneSpectrum (𝓞 K) → ℂ) (c₀ : ℝ) (r : ℕ) (hd : 0 < d)
    (hS : ∀ w, w ∈ SL ↔ w.under (𝓞 K) ∈ MainNotions)
    (h : ∀ p ∉ MainNotions, Multiset.card (BK p) ≤ r ∧ (∀ b ∈ BK p, ‖b‖ ≤ (Ideal.absNorm p.asIdeal : ℝ) ^ c₀) ∧
      ∀ w : PlacesOver L p, IsPrimitiveRoot (e p) (fdeg w) ∧ Fintype.card (PlacesOver L p) * fdeg w = d ∧
        BL w.1 = (BK p).map (· ^ fdeg w))
    (s : ℂ) (hs : c₀ + 1 < s.re) :
    ∏ j ∈ Finset.range d, eulerL K (fun p => (BK p).map (· * e p ^ j)) MainNotions s = eulerL L BL SL s := by
  have hf : ∀ p ∉ MainNotions, ∀ w : PlacesOver L p, 0 < fdeg w := by
    intro p hp w
    have := ((h p hp).2.2 w).2.1
    rcases Nat.eq_zero_or_pos (fdeg w) with h0 | h0
    · rw [h0] at this; omega
    · exact h0
  have hL := (GlobalTheory.HenQ.Regroup.multipliable_E L SL BL c₀ r (by
    intro w hw
    have hp : w.under (𝓞 K) ∉ MainNotions := (hS w).not.mp hw
    let w' : PlacesOver L (w.under (𝓞 K)) := ⟨w, ⟨rfl⟩⟩
    obtain ⟨h1, h2, h3⟩ := h _ hp
    have hB : BL w = _ := (h3 w').2.2
    have hN : Ideal.absNorm w.asIdeal = _ := norm_eq w'
    refine ⟨by rw [hB, Multiset.card_map]; exact h1, fun b hb => ?_⟩
    rw [hB] at hb
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hb
    rw [hN, norm_pow, Nat.cast_pow, ← Real.rpow_pow_comm (Nat.cast_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (h2 a ha) _) s hs).hasProd
  have hK : ∀ j ∈ Finset.range d, Multipliable (fun p : {p : HeightOneSpectrum (𝓞 K) // p ∉ MainNotions} =>
      (((BK p.1).map (· * e p.1 ^ j)).map fun b => (1 - b * ((Ideal.absNorm p.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹).prod) := by
    intro j _
    refine GlobalTheory.HenQ.Regroup.multipliable_E K MainNotions (fun p => (BK p).map (· * e p ^ j)) c₀ r ?_ s hs
    intro p hp
    obtain ⟨h1, h2, h3⟩ := h _ hp
    obtain ⟨w⟩ := nonempty_over (L := L) p
    have he : ‖e p‖ = 1 := (h3 w).1.norm'_eq_one (hf p hp w).ne'
    refine ⟨by rw [Multiset.card_map]; exact h1, fun b hb => ?_⟩
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hb
    rw [norm_mul, norm_pow, he, one_pow, mul_one]
    exact h2 a ha
  let E : (Σ p : {p : HeightOneSpectrum (𝓞 K) // p ∉ MainNotions}, PlacesOver L p.1) ≃
      {w : HeightOneSpectrum (𝓞 L) // w ∉ SL} :=
    { toFun := fun x => ⟨x.2.1, by rw [hS, under_eq x.2]; exact x.1.2⟩
      invFun := fun w => ⟨⟨w.1.under (𝓞 K), (hS w.1).not.mp w.2⟩, ⟨w.1, ⟨rfl⟩⟩⟩
      left_inv := by
        rintro ⟨⟨p, hp⟩, w⟩
        have hw := under_eq w
        obtain ⟨w, hw'⟩ := w
        simp only at hw
        subst hw
        rfl
      right_inv := by intro w; rfl }
  have h2 := (E.hasProd_iff).mpr hL
  unfold eulerL
  rw [← Multipliable.tprod_finsetProd hK]
  refine (h2.sigma ?_).tprod_eq
  rintro ⟨p, hp⟩
  obtain ⟨w₀⟩ := nonempty_over (L := L) p
  obtain ⟨-, -, h3⟩ := h p hp
  have hcard : 0 < Fintype.card (PlacesOver L p) := Fintype.card_pos_iff.mpr ⟨w₀⟩
  have hff : ∀ w : PlacesOver L p, fdeg w = fdeg w₀ := fun w =>
    Nat.eq_of_mul_eq_mul_left hcard ((h3 w).2.1.trans (h3 w₀).2.1.symm)
  convert hasProd_fintype _ using 1
  · dsimp only [E, Equiv.coe_fn_mk, Function.comp_apply]
    rw [← (h3 w₀).2.1, fac_eq (h3 w₀).1 (hf p hp w₀), ← Finset.card_univ, ← Finset.prod_const]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [(h3 w).2.2, norm_eq w, cast_pow_cpow, hff w]

end BaseChangeLocalFactorRegrouping

end UpperTheory.V.Z.Gam

open UpperTheory.V.Z.Gam.BaseChangeLocalFactorRegrouping in
theorem UpperTheory.V.Z.Gam.regroupBC :
    UpperTheory.V.Z.Gam.RegroupBC := by
  intro K L _ _ _ _ _ d MainNotions SL BK BL e c₀ r hd hS h
  refine ⟨c₀ + 1, fun s => ⟨fun hs => core d MainNotions SL BK BL e c₀ r hd.pos hS
    (fun p hp => ⟨(h p hp).1, fun b hb => ((h p hp).2.1 b hb).1, (h p hp).2.2⟩) s hs, fun hs => ?_⟩⟩
  unfold eulerLd
  rw [← core d MainNotions SL (fun p => (BK p).map (·⁻¹)) (fun w => (BL w).map (·⁻¹)) (fun p => (e p)⁻¹) c₀ r hd.pos hS
    ?_ (1 - s) ?_]
  · refine Finset.prod_congr rfl fun j _ => ?_
    congr 1
    funext p
    simp only [Multiset.map_map]
    refine Multiset.map_congr rfl fun b _ => ?_
    simp only [Function.comp_apply, mul_inv, inv_pow]
  · intro p hp
    obtain ⟨h1, h2, h3⟩ := h p hp
    refine ⟨by rw [Multiset.card_map]; exact h1, fun b hb => ?_, fun w => ⟨(h3 w).1.inv, (h3 w).2.1, ?_⟩⟩
    · obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hb
      exact (h2 a ha).2
    · simp only [(h3 w).2.2, Multiset.map_map]
      refine Multiset.map_congr rfl fun b _ => ?_
      simp only [Function.comp_apply, inv_pow]
  · simp only [Complex.sub_re, Complex.one_re]
    linarith
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.GlobTw
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.L2.Host Formalism.ConjugateSelfDual GroundTheory.Global.SemiLocal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.DelEps.Twist
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.Gam

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem exists_retr : ∃ r : kˣ →* kˣ, (∀ x : kˣ, valuation k (x : k) = 1 → r x = x) ∧
    ∀ H : Subgroup kˣ, IsOpen (H : Set kˣ) → IsOpen (H.comap r : Set kˣ) ∧ Finite (kˣ ⧸ H.comap r) := by
  obtain ⟨p, -, hp⟩ := exists_unit_pow k 1
  let r : kˣ →* kˣ :=
    { toFun := fun x => x * p ^ (-ord k x)
      map_one' := by rw [ord_eq_zero (by simp)]; simp
      map_mul' := fun x y => by rw [ord_mul, neg_add, zpow_add, mul_mul_mul_comm] }
  have hr : ∀ x : kˣ, valuation k (x : k) = 1 → r x = x := fun x hx => by
    change x * p ^ (-ord k x) = x
    rw [ord_eq_zero hx]; simp
  have hrp : r p = 1 := by
    change p * p ^ (-ord k p) = 1
    rw [hp]; simp
  refine ⟨r, hr, fun H hH => ?_⟩
  have ho : IsOpen (H.comap r : Set kˣ) :=
    Subgroup.isOpen_mono (H₁ := H ⊓ filtSub k 0) (fun x hx => by rw [Subgroup.mem_comap, hr x hx.2.1]; exact hx.1)
      (hH.inter (isOpen_filtSub k 0))
  refine ⟨ho, ?_⟩
  haveI : DiscreteTopology (kˣ ⧸ H.comap r) := QuotientGroup.discreteTopology ho
  have hf := ((GroundTheory.LocalField.isCompact_unitFiltrationUnits (K := k) 0).image
    (QuotientGroup.continuous_mk (N := H.comap r))).finite_of_discrete
  refine Set.finite_univ_iff.1 (hf.subset ?_)
  intro g _
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  refine ⟨g * p ^ (-ord k g), ?_, ?_⟩
  · rw [SetLike.mem_coe, GroundTheory.LocalField.mem_unitFiltrationUnits_zero_iff, ← ord_eq_zero_iff, ord_mul, ord_zpow, hp]
    simp
  · rw [eq_comm, QuotientGroup.eq, inv_mul_cancel_left, Subgroup.mem_comap, map_zpow, hrp, one_zpow]
    exact one_mem _

private theorem exists_fin (θ : kˣ →* ℂˣ) (hθ : IsSmoothChar θ) :
    ∃ χ : kˣ →* ℂˣ, IsSmoothChar χ ∧ (∃ N : ℕ, 0 < N ∧ χ ^ N = 1) ∧ IsUnram (χ * θ⁻¹) := by
  obtain ⟨r, hr, hH⟩ := exists_retr (k := k)
  obtain ⟨ho, hf⟩ := hH θ.ker hθ
  refine ⟨θ.comp r, ho, ⟨Nat.card (kˣ ⧸ θ.ker.comap r), Nat.card_pos, MonoidHom.ext fun x => ?_⟩, fun x hx => ?_⟩
  · rw [MonoidHom.pow_apply, ← map_pow]
    exact Subgroup.pow_index_mem (θ.ker.comap r) x
  · rw [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.comp_apply, hr x hx, mul_inv_cancel]

private theorem exists_sep (y : kˣ) (hy : valuation k (y : k) = 1) (h1 : y ≠ 1) :
    ∃ χ : kˣ →* ℂˣ, IsSmoothChar χ ∧ (∃ N : ℕ, 0 < N ∧ χ ^ N = 1) ∧ χ y ≠ 1 := by
  obtain ⟨r, hr, hH⟩ := exists_retr (k := k)
  have h0 : valuation k ((y : k) - 1) ≠ 0 := by
    rw [Valuation.ne_zero_iff, sub_ne_zero]
    exact fun h => h1 (Units.ext h)
  obtain ⟨a, ha⟩ : ∃ a : ℕ, uniformizer k ^ a < valuation k ((y : k) - 1) :=
    exists_pow_lt₀ uniformizer_lt_one (Units.mk0 _ h0)
  obtain ⟨ho, hf⟩ := hH _ (isOpen_filtSub k a)
  set H := (filtSub k a).comap r
  have hyH : (QuotientGroup.mk y : kˣ ⧸ H) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff, Subgroup.mem_comap, hr y hy]
    exact fun h => absurd h.2 (not_le.2 ha)
  obtain ⟨θ, hθ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (kˣ ⧸ H) ℂ hyH
  refine ⟨θ.comp (QuotientGroup.mk' H), Subgroup.isOpen_mono (fun z hz => ?_) ho,
    ⟨Nat.card (kˣ ⧸ H), Nat.card_pos, MonoidHom.ext fun z => ?_⟩, hθ⟩
  · rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff z).2 hz, map_one]
  · rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← map_pow, pow_card_eq_one', map_one, MonoidHom.one_apply]

private theorem exists_avoid (x : kˣ) (hx : valuation k (x : k) = 1) (hi : ∀ n : ℕ, 0 < n → x ^ n ≠ 1)
    (F : Finset (ℕ × ℂˣ)) (hF : ∀ p ∈ F, 0 < p.1) :
    ∃ χ : kˣ →* ℂˣ, IsSmoothChar χ ∧ (∃ N : ℕ, 0 < N ∧ χ ^ N = 1) ∧ ∀ p ∈ F, p.2 * χ x ^ p.1 ≠ 1 := by
  have hM : 0 < ∏ p ∈ F, p.1 * max (orderOf p.2) 1 :=
    Finset.prod_pos fun p hp => Nat.mul_pos (hF p hp) (by omega)
  obtain ⟨χ, h1, ⟨N, hN, h2⟩, h3⟩ := exists_sep _ (by rw [Units.val_pow_eq_pow_val, map_pow, hx, one_pow]) (hi _ hM)
  refine ⟨χ, h1, ⟨N, hN, h2⟩, fun p hp h => h3 ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun p : ℕ × ℂˣ => p.1 * max (orderOf p.2) 1) hp
  have hN1 : χ x ^ N = 1 := by rw [← MonoidHom.pow_apply, h2, MonoidHom.one_apply]
  have e : χ x ^ p.1 = p.2⁻¹ := eq_inv_of_mul_eq_one_right h
  have hfin : IsOfFinOrder p.2 := by
    rw [← isOfFinOrder_inv_iff, ← e]
    exact (isOfFinOrder_iff_pow_eq_one.2 ⟨N, hN, hN1⟩).pow
  have hpos := hfin.orderOf_pos
  rw [hc, map_pow, max_eq_left (by omega), pow_mul, pow_mul, e, inv_pow, pow_orderOf_eq_one, inv_one, one_pow]

end Loc

private theorem val_one_iff {K : Type} [Field K] [NumberField K] (u : HeightOneSpectrum (𝓞 K)) (x : u.adicCompletion K) :
    valuation (u.adicCompletion K) x = 1 ↔ Valued.v x = 1 := by
  haveI : (Valued.v : Valuation (u.adicCompletion K) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (valuation (u.adicCompletion K)) Valued.v).eq_one_iff_eq_one

private theorem exists_at {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (u : HeightOneSpectrum (𝓞 K)) (bad : Finset ((u.adicCompletion K)ˣ →* ℂˣ))
    (bad' : ∀ w : HeightOneSpectrum (𝓞 L), Finset ((w.adicCompletion L)ˣ →* ℂˣ)) :
    ∃ χ : (u.adicCompletion K)ˣ →* ℂˣ, IsSmoothChar χ ∧ (∃ N : ℕ, 0 < N ∧ χ ^ N = 1) ∧
      (∀ ξ ∈ bad, ¬ IsUnram (ξ * χ)) ∧ ∀ w : PlacesOver L u, ∀ ζ ∈ bad' w.1, ¬ IsUnram (ζ * χ.comp (nm w)) := by
  haveI : CharZero (u.adicCompletion K) := charZero_of_injective_ringHom (algebraMap K (u.adicCompletion K)).injective
  obtain ⟨m, hm, hmu⟩ : ∃ m : ℕ, 0 < m ∧ ((m : ℕ) : 𝓞 K) ∈ u.asIdeal :=
    ⟨_, (GlobalTheory.LocalData.resChar_prime u).pos, GlobalTheory.LocalData.resChar_mem u⟩
  have hv : Valued.v (((1 + m : ℕ) : u.adicCompletion K)) = 1 := by
    have := (valued_algebraMap_int_lt_one_iff u _).2 hmu
    rw [map_natCast] at this
    rw [Nat.cast_add, Nat.cast_one]
    exact Valuation.map_one_add_of_lt _ this
  let x : (u.adicCompletion K)ˣ := Units.mk0 ((1 + m : ℕ) : u.adicCompletion K) (Nat.cast_ne_zero.2 (by omega))
  let ι : ∀ w : PlacesOver L u, (w.1.adicCompletion L)ˣ := fun w =>
    Units.map (algebraMap (u.adicCompletion K) (w.1.adicCompletion L) : u.adicCompletion K →* w.1.adicCompletion L) x
  let d : PlacesOver L u → ℕ := fun w => Module.finrank (u.adicCompletion K) (w.1.adicCompletion L)
  have hd : ∀ w, 0 < d w := fun w =>
    lt_of_lt_of_le (Nat.mul_pos (Ideal.ramificationIdx_pos _ _) (Ideal.inertiaDeg_pos _ _))
      (ramificationIdx_mul_inertiaDeg_le_finrank u w.1)
  have hι : ∀ w, valuation _ (ι w : w.1.adicCompletion L) = 1 := fun w => by
    rw [val_one_iff]
    change Valued.v (completionMap u w.1 ((1 + m : ℕ) : u.adicCompletion K)) = 1
    rw [valued_completionMap, hv, one_pow]
  have hn : ∀ w, nm w (ι w) = x ^ d w := fun w => Units.ext (Algebra.norm_algebraMap _)
  have hx : valuation _ (x : u.adicCompletion K) = 1 := (val_one_iff u _).2 hv
  obtain ⟨χ, h1, h2, h3⟩ := exists_avoid x hx
    (fun n hn h => by
      have h' : ((1 + m : ℕ) : u.adicCompletion K) ^ n = 1 := congrArg Units.val h
      have h'' : (1 + m) ^ n = 1 := by exact_mod_cast h'
      exact absurd h'' (Nat.one_lt_pow hn.ne' (by omega)).ne')
    (bad.image (fun ξ => (1, ξ x)) ∪ Finset.univ.biUnion fun w : PlacesOver L u => (bad' w.1).image fun ζ => (d w, ζ (ι w)))
    (fun p hp => by
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_biUnion] at hp
      rcases hp with ⟨_, -, rfl⟩ | ⟨w, -, _, -, rfl⟩
      · exact one_pos
      · exact hd w)
  refine ⟨χ, h1, h2, fun ξ hξ h => h3 (1, ξ x) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hξ)) ?_,
    fun w ζ hζ h => h3 (d w, ζ (ι w)) (Finset.mem_union_right _
      (Finset.mem_biUnion.2 ⟨w, Finset.mem_univ _, Finset.mem_image_of_mem _ hζ⟩)) ?_⟩
  · simpa using h x hx
  · have := h (ι w) (hι w)
    rwa [MonoidHom.mul_apply, MonoidHom.comp_apply, hn, map_pow] at this

theorem globTw : GlobTw := by
  intro K L _ _ _ _ _ v θ hθ S bad bad'
  obtain ⟨θ', a1, a2, a3⟩ := exists_fin θ hθ
  choose c c1 c2 c3 using fun u : HeightOneSpectrum (𝓞 K) => exists_at u (bad u) bad'
  obtain ⟨η, -, -, h⟩ := exists_hchar_prescribed K (insert v S) (Function.update c v θ')
    (fun w _ => by
      by_cases e : w = v
      · subst e; rwa [Function.update_self]
      · rw [Function.update_of_ne e]; exact c1 w)
    (fun w _ => by
      by_cases e : w = v
      · subst e; rwa [Function.update_self]
      · rw [Function.update_of_ne e]; exact c2 w)
  refine ⟨η, by rwa [h v (Finset.mem_insert_self _ _), Function.update_self], fun u hu e => ?_⟩
  rw [h u (Finset.mem_insert_of_mem hu), Function.update_of_ne e]
  exact c3 u

end UpperTheory.V.Z.Gam
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.LocIso
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.LocGL UpperTheory.V.Z.Inf
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.GJStandardLCuspidal
open scoped Classical

namespace UpperTheory.V.Z.Gam

private theorem localEmbedding_eq {K : Type} [Field K] [NumberField K] {n : ℕ}
    (w : HeightOneSpectrum (𝓞 K)) (g : GL (Fin n) (w.adicCompletion K)) :
    AdelicGLn.localEmbedding w g = locGL K n w g := by
  refine Units.ext <| Matrix.ext fun a b => FiniteAdeleRing.ext K fun v => ?_
  change ((AdelicGLn.finiteRestrictedEquiv K n).symm _ : AdelicGLn.FiniteAdelicGL K n) a b v = _
  rw [AdelicGLn.finiteRestrictedEquiv_symm_apply, RestrictedProduct.coe_mulSingle_apply]
  by_cases h : v = w
  · subst h
    rw [Pi.mulSingle_eq_same]
    exact (congrArg (fun x : GL (Fin n) (v.adicCompletion K) => x a b) (pLoc_locGL v g)).symm
  · rw [Pi.mulSingle_eq_of_ne h]
    exact (congrArg (fun x : GL (Fin n) (v.adicCompletion K) => x a b) (pLoc_locGL_of_ne h g)).symm

end UpperTheory.V.Z.Gam

open UpperTheory.V UpperTheory.V.Z.Gam in
theorem UpperTheory.V.Z.Gam.locIso :
    UpperTheory.V.Z.Gam.LocIso := by
  intro K _ _ _ n σ h D v
  let τ : SmIrr (GL (Fin n) (v.adicCompletion K)) :=
    { V := D.finite.W v
      ρ := D.finite.π v
      smooth := (D.finite.isAdmissible v).1
      irred := D.finite.isIrreducible v }
  have hτ : σ.IsLocComp v τ := by
    obtain ⟨a, x, hx, ha, hx0, -⟩ := exists_pureTensor_spherical (Cm.toRep σ h) D
    refine ⟨(Cm.carrierEq σ).toLinearMap ∘ₗ Iv D a x hx v, fun e => ?_, fun g y => ?_⟩
    · have e' : Iv D a x hx v (x v) = 0 := (Cm.carrierEq σ).map_eq_zero_iff.1 (LinearMap.congr_fun e (x v))
      rw [Iv_self] at e'
      exact phi_ne D a x hx ha hx0 e'
    · refine ((congrArg (Cm.carrierEq σ) (Iv_int D a x hx v g y)).trans (Cm.carrierEq_τ σ _ _)).trans ?_
      rw [localEmbedding_eq]
      rfl
  refine ⟨?_, fun B hB => ?_⟩
  · rintro s ⟨σ', h1, h2⟩
    obtain ⟨e⟩ := LocUniq.isLocComp_unique σ v σ' τ h1 hτ
    exact h2.of_equiv e
  · obtain ⟨α, -, h'⟩ := GlobalTheory.LFun.SphComp.hasSatake_of_isLocComp σ ((CG.hasSat_mk σ v B).1 hB) hτ
    have h1 : GlobalTheory.LGrp.IsSpherical τ.ρ (GlobalTheory.SplitWeil.KO (v.adicCompletion K) (Fin n)) := h'.2.1
    have hsph : GlobalTheory.LGrp.IsSpherical τ.ρ (GlobalTheory.LFun.KGL v (n := n)) := by
      rwa [GlobalTheory.SmGL.SphCompletion.KO_completion v n] at h1
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hsph
    rw [(Af.Smo.sphDict K n v).1]
    exact (Submodule.ne_bot_iff _).2 ⟨x, fun k hk => GlobalTheory.LGrp.mem_fixed.1 hx k hk, hx0⟩
end
end
