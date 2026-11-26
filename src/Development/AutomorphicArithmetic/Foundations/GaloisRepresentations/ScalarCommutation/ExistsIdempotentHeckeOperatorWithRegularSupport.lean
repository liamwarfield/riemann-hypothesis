module

public import Development.AutomorphicArithmetic.IwahoriCommensurability.IsCommensuratedIwahoriGl
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.TyFact
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.SeenShapeHolds
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwDomMul
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriGlCasselmanDatum
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CharpolySmul

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
  UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin
  UpperTheory.V.Alg.IsCO.toIsLocalRing UpperTheory.V.Alg.IsCO.complete
  UpperTheory.V.Alg.IsCO.isLocalHom UpperTheory.V.Alg.IsCO.self

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAddCharConductorMaxIdeal
open ValuativeRel

noncomputable section

namespace GlobalTheory.DZero.PsiM

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem valueGroupIso_uniformizer :
    IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k (uniformizer k) = WithZero.exp (-1) := by
  set φ := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
  have h0 : φ (uniformizer k) ≠ 0 := by simp
  apply le_antisymm
  · have : φ (uniformizer k) < φ 1 := φ.strictMono uniformizer_lt_one
    rw [map_one, ← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at this
    rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
    omega
  · have : φ.symm (WithZero.exp (-1)) ≤ uniformizer k := by
      rw [le_uniformizer_iff, ← map_one φ.symm]
      exact φ.symm.strictMono (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
    simpa using φ.strictMono.monotone this

variable {k}

theorem ord_eq_one {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) : SmGL.ord k ϖ = 1 := by
  rw [SmGL.ord, hϖ, valueGroupIso_uniformizer, WithZero.log_exp]; rfl

end GlobalTheory.DZero.PsiM
end
end

section -- merged from Development.AutomorphicArithmetic.IwahoriCommensurability.IsCommensuratedIwahoriSubgroupGlFin
open Formalism.UG

theorem UpperTheory.isCommensurated_iwahoriSubgroup_gl_fin :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), Formalism.UG.IsCommensurated (GlobalTheory.SmGL.iwahori k (Fin n)) := by
  intro k _ _ _ _ n
  have h : GlobalTheory.SmGL.iwahori k (Fin n) =
      GroundTheory.Automorphic.GLnLocal.iwahori k n := by
    ext g
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, GlobalTheory.SmGL.mem_borel] at hu
      refine ⟨u, ?_, ?_⟩
      · rw [SetLike.mem_coe, Subgroup.mem_comap, GroundTheory.Automorphic.mem_borel_iff]
        intro i j hij
        rw [GroundTheory.Automorphic.GLnLocal.residueReduction_apply]
        exact hu i j hij
      · ext i j
        rfl
    · rintro ⟨u, hu, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, GroundTheory.Automorphic.mem_borel_iff] at hu
      refine ⟨u, ?_, ?_⟩
      · rw [SetLike.mem_coe, Subgroup.mem_comap, GlobalTheory.SmGL.mem_borel]
        intro i j hij
        have h := hu i j hij
        rw [GroundTheory.Automorphic.GLnLocal.residueReduction_apply] at h
        exact h
      · ext i j
        rfl
  rw [h]
  exact UpperTheory.isCommensurated_iwahori_gl k n
end

section -- merged from Development.AutomorphicArithmetic.IwahoriCommensurability.ExistsPrimePowScalarIntegralOfGoodPrime
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl

private theorem val_natCast_lt_one {E : Type} [Field E] [NumberField E] (u : Plc E) (r : ℕ)
    (hu : (r : 𝓞 E) ∈ u.asIdeal) : Valued.v (r : u.adicCompletion E) < 1 := by
  have h := (u.valuation_lt_one_iff_mem (K := E) (r : 𝓞 E)).2 hu
  have e : ((r : ℕ) : u.adicCompletion E) = algebraMap E (u.adicCompletion E) (r : E) :=
    (map_natCast _ r).symm
  have e2 : Valued.v (algebraMap E (u.adicCompletion E) (r : E)) = u.valuation E (r : E) :=
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' u _
  rw [e, e2]
  simpa using h

private theorem eventually_integral {E : Type} [Field E] [NumberField E] (u : Plc E) (r : ℕ)
    (hu : (r : 𝓞 E) ∈ u.asIdeal) (x : u.adicCompletion E) :
    ∀ᶠ M : ℕ in Filter.atTop, ((r ^ M : ℕ) : u.adicCompletion E) * x ∈ u.adicCompletionIntegers E := by
  have h1 := val_natCast_lt_one u r hu
  by_cases hx : x = 0
  · simp [hx]
  have hv : Valued.v x ≠ 0 := by simpa using hx
  obtain ⟨M₀, hM₀⟩ := exists_pow_lt₀ h1 (Units.mk0 _ (inv_ne_zero hv))
  filter_upwards [Filter.eventually_ge_atTop M₀] with M hM
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, Nat.cast_pow, map_pow]
  have h2 : Valued.v (r : u.adicCompletion E) ^ M ≤ (Valued.v x)⁻¹ :=
    (pow_le_pow_of_le_one zero_le' h1.le hM).trans hM₀.le
  calc _ ≤ (Valued.v x)⁻¹ * Valued.v x := mul_le_mul' h2 le_rfl
    _ = 1 := inv_mul_cancel₀ hv

theorem UpperTheory.exists_primePow_scalar_integral_of_good_prime :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p) (F : Frame S) (r : ℕ), r.Prime → A.Good r → ∀ g : GUf E n, (∀ u : Plc E, (r : 𝓞 E) ∉ u.asIdeal → comp u g = 1) → ∃ M : ℕ, ∀ d : GUf E n, (∀ w : Plc E, (comp w d).val = ((r ^ M : ℕ) : w.adicCompletion E) • (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E))) → Integ S.L (F.j (g * d)) := by
  intro E _ _ _ A n p _ S F r hr _ g hg
  have hr0 : (r : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hr.ne_zero
  have hT : {u : Plc E | (r : 𝓞 E) ∈ u.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {(r : 𝓞 E)}) (by simpa using hr0)).subset fun u hu => ?_
    exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hu)
  have hev : ∀ᶠ M : ℕ in Filter.atTop, ∀ u ∈ {u : Plc E | (r : 𝓞 E) ∈ u.asIdeal}, ∀ i k,
      ((r ^ M : ℕ) : u.adicCompletion E) * F.cmp u g i k ∈ u.adicCompletionIntegers E := by
    rw [Filter.eventually_all_finite hT]
    intro u hu
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro k
    exact eventually_integral u r hu _
  obtain ⟨M, hM⟩ := hev.exists
  refine ⟨M, fun d hd => (integ_iff F _).2 fun w _ i k => ?_⟩
  have e : F.cmp w (g * d) = ((r ^ M : ℕ) : w.adicCompletion E) • F.cmp w g := by
    unfold Frame.cmp
    simp only [map_mul, Units.val_mul, hd w]
    simp [Matrix.mul_assoc]
  rw [e, Matrix.smul_apply, smul_eq_mul]
  by_cases hw : (r : 𝓞 E) ∈ w.asIdeal
  · exact hM w hw i k
  · have h1 : F.cmp w g = 1 := by
      unfold Frame.cmp
      simp [hg w hw]
    rw [h1, Matrix.one_apply]
    split_ifs
    · simpa using natCast_mem (w.adicCompletionIntegers E) (r ^ M)
    · simp
end

section -- merged from Development.AutomorphicArithmetic.IwahoriCommensurability.ExistsLevelSubgroupCentralScalarOfPos
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 Plc comp mat rat mem_Sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl

theorem UpperTheory.exists_levelSubgroup_central_scalar_of_pos :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p) (F : Frame S) (c : ℕ), 0 < c →
      ∃ y : Gam0 E n, y.1.1.val = (c : E) • (1 : Matrix (Fin n) (Fin n) E) ∧ ((y.1.2 : ℚˣ) : ℚ) = (c : ℚ) ^ 2 ∧
        (∀ w : Plc E, (comp w (rat y)).val = (c : w.adicCompletion E) • (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E))) ∧
        (∀ g : GUf E n, rat y * g = g * rat y) ∧
        (∀ h : S.G.GAf, F.j (rat y) * h = h * F.j (rat y)) ∧
        ∀ v, S.L.actG (F.j (rat y)) v = c • v := by
  intro E _ _ _ A n p _ S F c hc
  have hcE : (c : E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  have hcQ : (c : ℚ) ^ 2 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hc.ne')
  let u : GL (Fin n) E := ⟨(c : E) • 1, (c : E)⁻¹ • 1, by simp [smul_smul, hcE], by simp [smul_smul, hcE]⟩
  let s : ℚˣ := Units.mk0 ((c : ℚ) ^ 2) hcQ
  have hm : (u, s) ∈ Gam0 E n := by
    refine ⟨mem_Sim.2 ?_, ?_⟩
    · show (((c : E) • (1 : Matrix (Fin n) (Fin n) E)).map (GlobalTheory.SplitPts.conjE E).toRingHom)ᵀ * ((c : E) • (1 : Matrix (Fin n) (Fin n) E)) = algebraMap ℚ E ((c : ℚ) ^ 2) • 1
      ext i k
      by_cases hik : i = k
      · simp [hik, Matrix.one_apply, Matrix.mul_apply, pow_two]
      · simp [hik, Ne.symm hik, Matrix.one_apply, Matrix.mul_apply]
    · show (0 : ℚ) < (c : ℚ) ^ 2
      positivity
  let y : Gam0 E n := ⟨(u, s), hm⟩
  have hmat : (mat (rat y)).val = ((c : FiniteAdeleRing (𝓞 E) E)) • (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) := by
    show ((c : E) • (1 : Matrix (Fin n) (Fin n) E)).map (algebraMap E (FiniteAdeleRing (𝓞 E) E)) = _
    ext i k
    by_cases hik : i = k <;> simp [hik, Matrix.one_apply]
  have hcomp : ∀ w : Plc E, (comp w (rat y)).val = (c : w.adicCompletion E) • (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
    intro w
    show ((mat (rat y)).val).map (pLoc E w) = _
    rw [hmat]
    ext i k
    by_cases hik : i = k <;> simp [hik, Matrix.one_apply]
  have hcen : ∀ g : GUf E n, rat y * g = g * rat y := by
    intro g
    refine Subtype.ext (Prod.ext (Units.ext ?_) (mul_comm _ _))
    show (mat (rat y)).val * (mat g).val = (mat g).val * (mat (rat y)).val
    rw [hmat]
    simp
  refine ⟨y, rfl, rfl, hcomp, hcen, ?_, ?_⟩
  · intro h
    obtain ⟨g, rfl⟩ := F.surj h
    rw [← map_mul, ← map_mul, hcen]
  · intro v
    refine sub_eq_zero.1 (F.vec_inj (S.L.actG (F.j (rat y)) v - c • v) fun w hw => ?_)
    rw [map_sub, map_nsmul, F.vec_act w hw, sub_eq_zero]
    have e : (F.a w * comp w (rat y) * (F.a w)⁻¹).val = (c : w.adicCompletion E) • (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
      rw [Units.val_mul, Units.val_mul, hcomp w]
      simp
    rw [e, Matrix.smul_mulVec, Matrix.one_mulVec, Nat.cast_smul_eq_nsmul]
end

section -- merged from Development.AutomorphicArithmetic.IwahoriCommensurability.IwahoriDoubleCosetTorusMulOfStrictAnti
open Formalism.UG

namespace UpperTheory.IwMul

open GlobalTheory.PRep GlobalTheory.SmGL Matrix ValuativeRel GlobalTheory.CompanionTheory.IwJac

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem upper_entries {ϖ : kˣ} (hϖ : ord k ϖ = 1) {ν : Fin n → ℤ} (hν : StrictAnti ν)
    {c : GL (Fin n) k} (hc : c ∈ iwahori k (Fin n) ⊓ unipB k (Fin n)) (i j : Fin n) :
    valuation k (((tor ϖ ν * c * (tor ϖ ν)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j) ≤ 1 ∧
      (j < i → valuation k (((tor ϖ ν * c * (tor ϖ ν)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j) < 1) := by
  have hconj : tor ϖ ν * c * (tor ϖ ν)⁻¹ = (tor ϖ (fun i => -ν i))⁻¹ * c * tor ϖ (fun i => -ν i) := by
    rw [DCoset.tor_inv ϖ (fun i => -ν i), DCoset.tor_inv ϖ ν]
    simp only [neg_neg]
  rw [hconj, DCoset.conj_apply]
  obtain ⟨hc1, hc2⟩ := hc
  have hint := ((GlobalTheory.SplitFlip.mem_KO_iff c).mp (mem_iwahori.mp hc1).1).1 i j
  have hup := (mem_unipB k).mp hc2
  rcases lt_or_ge j i with hji | hij
  · rw [hup.1 i j hji]
    simp
  · refine ⟨?_, fun h => absurd h (not_lt.mpr hij)⟩
    rw [map_mul]
    have hpow : valuation k ((ϖ ^ (-ν j - -ν i) : kˣ) : k) ≤ 1 := by
      rcases hij.lt_or_eq with hlt | heq
      · exact (DCoset.val_zpow_lt_one hϖ (by have := hν hlt; omega)).le
      · subst heq
        simp
    exact mul_le_one' hpow hint

private theorem upper_conj_mem {ϖ : kˣ} (hϖ : ord k ϖ = 1) {ν : Fin n → ℤ} (hν : StrictAnti ν)
    {c : GL (Fin n) k} (hc : c ∈ iwahori k (Fin n) ⊓ unipB k (Fin n)) :
    tor ϖ ν * c * (tor ϖ ν)⁻¹ ∈ iwahori k (Fin n) := by
  refine mem_iwahori.2 ⟨(GlobalTheory.SplitFlip.mem_KO_iff _).2 ⟨fun i j => ?_, fun i j => ?_⟩,
    fun i j hij => (upper_entries hϖ hν hc i j).2 hij⟩
  · exact (Valuation.mem_integer_iff _ _).2 (upper_entries hϖ hν hc i j).1
  · have e : (tor ϖ ν * c * (tor ϖ ν)⁻¹)⁻¹ = tor ϖ ν * c⁻¹ * (tor ϖ ν)⁻¹ := by group
    rw [e]
    exact (Valuation.mem_integer_iff _ _).2 (upper_entries hϖ hν (inv_mem hc) i j).1

private theorem lower_conj_mem {ϖ : kˣ} (hϖ : ord k ϖ = 1) {ν : Fin n → ℤ} (hν : StrictAnti ν)
    {l : GL (Fin n) k} (hl : l ∈ iwahori k (Fin n) ⊓ unipBLower k (Fin n)) (m : ℕ) :
    (GlobalTheory.GLDoubling.torusElt k (Fin n) ϖ ν ^ m)⁻¹ * l * GlobalTheory.GLDoubling.torusElt k (Fin n) ϖ ν ^ m ∈
      iwahori k (Fin n) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa using hl.1
  · rw [GlobalTheory.TorusElementPower.torusElt_pow_eq]
    have hν' : StrictAnti (fun i : Fin n => (m : ℤ) * ν i) := by
      intro i j hij
      exact mul_lt_mul_of_pos_left (hν hij) (by exact_mod_cast hm)
    exact DCoset.conj_mem_iwahori hϖ hν' hl

end UpperTheory.IwMul

theorem UpperTheory.iwahori_doubleCoset_torus_mul_of_strictAnti :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ϖ : kˣ), ValuativeRel.valuation k (ϖ : k) = ValuativeRel.uniformizer k → ∀ ν : Fin n → ℤ, StrictAnti ν → ∀ m : ℕ, ∀ a ∈ DoubleCoset.doubleCoset (GlobalTheory.GLDoubling.torusElt k (Fin n) ϖ ν) (GlobalTheory.SmGL.iwahori k (Fin n) : Set (GL (Fin n) k)) (GlobalTheory.SmGL.iwahori k (Fin n)), ∀ b ∈ DoubleCoset.doubleCoset (GlobalTheory.GLDoubling.torusElt k (Fin n) ϖ ν ^ m) (GlobalTheory.SmGL.iwahori k (Fin n) : Set (GL (Fin n) k)) (GlobalTheory.SmGL.iwahori k (Fin n)), a * b ∈ DoubleCoset.doubleCoset (GlobalTheory.GLDoubling.torusElt k (Fin n) ϖ ν ^ (m + 1)) (GlobalTheory.SmGL.iwahori k (Fin n) : Set (GL (Fin n) k)) (GlobalTheory.SmGL.iwahori k (Fin n)) := by
  intro k _ _ _ _ n ϖ hϖu ν hν m a ha b hb
  have hϖ := GlobalTheory.SmGL.ord_eq_one hϖu
  have htt : GlobalTheory.GLDoubling.torusElt k (Fin n) ϖ ν = GlobalTheory.CompanionTheory.IwJac.tor ϖ ν := rfl
  obtain ⟨i1, hi1, i2, hi2, rfl⟩ := DoubleCoset.mem_doubleCoset.mp ha
  obtain ⟨i3, hi3, i4, hi4, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hb
  have hx : i2 * i3 ∈ GlobalTheory.SmGL.iwahori k (Fin n) := mul_mem hi2 hi3
  obtain ⟨c, hc, d, hd, l, hl, hcdl⟩ := GlobalTheory.CompanionTheory.IwahoriDatumGL.fact_up' k n hx
  obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp hd.2
  rw [DoubleCoset.mem_doubleCoset]
  refine ⟨i1 * (GlobalTheory.CompanionTheory.IwJac.tor ϖ ν * c * (GlobalTheory.CompanionTheory.IwJac.tor ϖ ν)⁻¹) * d,
    mul_mem (mul_mem hi1 (UpperTheory.IwMul.upper_conj_mem hϖ hν hc)) hd.1,
    (GlobalTheory.GLDoubling.torusElt k (Fin n) ϖ ν ^ m)⁻¹ * l * GlobalTheory.GLDoubling.torusElt k (Fin n) ϖ ν ^ m * i4,
    mul_mem (UpperTheory.IwMul.lower_conj_mem hϖ hν hl m) hi4, ?_⟩
  rw [htt, ← hs, ← GlobalTheory.CompanionTheory.IwJac.DCoset.diagT_conj_tor ϖ ν s, hs]
  have h2 : i2 = c * d * l * i3⁻¹ := by
    rw [← hcdl]
    group
  subst h2
  group
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PConvSupp
open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms
open scoped Classical

namespace UpperTheory.Gal.W2.Seed

theorem pConvSupp : ConvSupp := by
  intro X _ K f f' g h
  by_contra hne
  push_neg at hne
  apply h
  unfold conv
  apply finsum_eq_zero_of_forall_eq_zero
  intro q
  by_contra hq
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hq
  exact hne _ _ h1 h2 (mul_inv_cancel_left _ _).symm

end UpperTheory.Gal.W2.Seed
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.IwInvT
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTracePowRestrictNeZero
noncomputable section

open ValuativeRel GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.GLDoubling

namespace GlobalTheory.IwahoriUnit

section Gen

variable {G : Type} [Group G]

def cosets (I : Subgroup G) (x : G) : Set (G ⧸ I) :=
  (QuotientGroup.mk : G → G ⧸ I) '' DoubleCoset.doubleCoset x I I

theorem cosets_eq_orbit (I : Subgroup G) (x : G) : cosets I x = MulAction.orbit I (x : G ⧸ I) := by
  ext q
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
    refine ⟨⟨a, ha⟩, ?_⟩
    show ((a * x : G) : G ⧸ I) = ((a * x * b : G) : G ⧸ I)
    rw [QuotientGroup.mk_mul_of_mem _ hb]
  · rintro ⟨a, rfl⟩
    exact ⟨a * x * 1, DoubleCoset.mem_doubleCoset.2 ⟨a, a.2, 1, one_mem _, rfl⟩, by rw [mul_one]; rfl⟩

variable {E V : Type} [Field E] [AddCommGroup V] [Module E V]

theorem fixed_eq_fixd (π : Representation E G V) (I : Subgroup G) : fixed π I = UpperTheory.V.Hi.fixd π I := by
  ext v
  constructor
  · intro h u hu
    simpa using h ⟨u, hu⟩
  · intro h u
    simpa using h u u.2

theorem hk_apply (π : Representation E G V) (I : Subgroup G) (x : G) (h : (cosets I x).Finite)
    (v : UpperTheory.V.Hi.fixd π I) :
    (UpperTheory.V.AlgebraTools.hk π I x v : V) = ∑ᶠ q ∈ cosets I x, π q.out v := by
  rw [cosets_eq_orbit] at h ⊢
  have : Finite (MulAction.orbit I (x : G ⧸ I)) := h
  have := Fintype.ofFinite (MulAction.orbit I (x : G ⧸ I))
  rw [UpperTheory.V.AlgebraTools.hk, (UpperTheory.V.AlgebraTools.hkApply E G V π I I x h).1 v, UpperTheory.V.Hi.dc,
    ← finsum_set_coe_eq_finsum_mem, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, LinearMap.sum_apply]

end Gen

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

theorem finite_cosets (x : GL (Fin N) k) : (cosets (iwahori k (Fin N)) x).Finite := by
  rw [cosets_eq_orbit, ← (UpperTheory.V.AlgebraTools.memIwC k N ⊤).2.1]
  exact (UpperTheory.V.AlgebraTools.heckePairIwC k N ⊤).1 x

theorem dom_of_antitone {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) {ν : Fin N → ℤ} (hν : Antitone ν) :
    UpperTheory.V.AlgebraTools.Dom (fun i => ϖ ^ ν i) := by
  intro i j hij
  have h1 : valuation k (ϖ : k) ≤ 1 := (hϖ ▸ uniformizer_lt_one).le
  have h0 : 0 < valuation k (ϖ : k) := (Valuation.pos_iff _).2 ϖ.ne_zero
  simp only [Units.val_zpow_eq_zpow_val, map_zpow₀]
  exact zpow_le_zpow_right_of_le_one₀ h0 h1 (hν hij)

theorem torusElt_pow (ϖ : kˣ) (ν : Fin N → ℤ) (m : ℕ) :
    torusElt k (Fin N) ϖ ν ^ m = diagT k (Fin N) ((fun i => ϖ ^ ν i) ^ m) := by
  rw [map_pow]; rfl

theorem dom_pow {t : Fin N → kˣ} (ht : UpperTheory.V.AlgebraTools.Dom t) (m : ℕ) : UpperTheory.V.AlgebraTools.Dom (t ^ m) := by
  intro i j hij
  simp only [Pi.pow_apply, Units.val_pow_eq_pow_val, map_pow]
  exact pow_le_pow_left₀ zero_le' (ht i j hij) m

theorem exists_equiv_doubleCoset (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (ϖ : kˣ) (hϖ : valuation k (ϖ : k) = uniformizer k)
    (ν : Fin N → ℤ) (hν : Antitone ν) (E V : Type) [Field E] [CharZero E] [AddCommGroup V] [Module E V]
    (π : Representation E (GL (Fin N) k) V) :
    (∀ m : ℕ, (cosets (iwahori k (Fin N)) (torusElt k (Fin N) ϖ ν ^ m)).Finite) ∧
    ∃ T : fixed π (iwahori k (Fin N)) ≃ₗ[E] fixed π (iwahori k (Fin N)),
      (∀ v, (T v : V) = ∑ᶠ q ∈ cosets (iwahori k (Fin N)) (torusElt k (Fin N) ϖ ν), π q.out v) ∧
      ∀ (m : ℕ) v, ((T ^ m) v : V) =
        ∑ᶠ q ∈ cosets (iwahori k (Fin N)) (torusElt k (Fin N) ϖ ν ^ m), π q.out v := by
  refine ⟨fun m => finite_cosets _, ?_⟩
  have hd := dom_of_antitone hϖ hν
  have hq : IsUnit ((GlobalTheory.SplitWeil.resCard k : ℕ) : E) := by
    refine IsUnit.mk0 _ (Nat.cast_ne_zero.2 ?_)
    exact Nat.card_pos.ne'
  obtain ⟨hmul, hunit, -⟩ := UpperTheory.V.AlgebraTools.domMul k N ⊤ E V π
  rw [(UpperTheory.V.AlgebraTools.memIwC k N ⊤).2.1] at hmul hunit
  rw [fixed_eq_fixd]
  have hone : UpperTheory.V.AlgebraTools.hk π (iwahori k (Fin N)) (diagT k (Fin N) 1) = 1 := by
    have h := hmul 1 1 UpperTheory.V.AlgebraTools.dom_one UpperTheory.V.AlgebraTools.dom_one
    rw [mul_one] at h
    exact (hunit hq 1 UpperTheory.V.AlgebraTools.dom_one).mul_left_cancel (h.trans (mul_one _).symm)
  have hpow : ∀ m : ℕ, UpperTheory.V.AlgebraTools.hk π (iwahori k (Fin N)) (diagT k (Fin N) fun i => ϖ ^ ν i) ^ m =
      UpperTheory.V.AlgebraTools.hk π (iwahori k (Fin N)) (diagT k (Fin N) ((fun i => ϖ ^ ν i) ^ m)) := by
    intro m
    induction m with
    | zero => rw [pow_zero, pow_zero, hone]
    | succ m ih => rw [pow_succ, pow_succ, ih, hmul _ _ (dom_pow hd m) hd]
  have hb := (Module.End.isUnit_iff _).1 (hunit hq _ hd)
  refine ⟨LinearEquiv.ofBijective _ hb, fun v => hk_apply π _ _ (finite_cosets _) v, fun m v => ?_⟩
  rw [← hk_apply π _ _ (finite_cosets _) v, torusElt_pow, ← hpow]
  congr 1
  rw [LinearEquiv.pow_apply, Module.End.pow_apply]
  rfl

end GlobalTheory.IwahoriUnit
end
end

noncomputable section

open Formalism.UG GlobalTheory.PRep GlobalTheory.IwahoriUnit
open scoped Classical

namespace UpperTheory.Gal.CertificateRingHomMap

variable {G : Type} [Group G]

private def cfun (K : Subgroup G) : Submodule ℂ (G → ℂ) where
  carrier := {f | (∀ g, ∀ b ∈ K, f (g * b) = f g) ∧ ∃ S : Finset G, ∀ g, f g ≠ 0 → ∃ s ∈ S, ∃ b ∈ K, g = s * b}
  zero_mem' := ⟨fun _ _ _ => rfl, ∅, fun _ h => (h rfl).elim⟩
  add_mem' := by
    rintro f f' ⟨hf, S, hS⟩ ⟨hf', S', hS'⟩
    refine ⟨fun g b hb => by simp [hf g b hb, hf' g b hb], S ∪ S', fun g hg => ?_⟩
    by_cases h : f g = 0
    · obtain ⟨s, hs, e⟩ := hS' g (by simpa [h] using hg)
      exact ⟨s, Finset.mem_union_right _ hs, e⟩
    · obtain ⟨s, hs, e⟩ := hS g h
      exact ⟨s, Finset.mem_union_left _ hs, e⟩
  smul_mem' := by
    rintro c f ⟨hf, S, hS⟩
    exact ⟨fun g b hb => by simp [hf g b hb], S, fun g hg => hS g fun h => hg (by simp [h])⟩

private def lrep (K : Subgroup G) : Representation ℂ G (cfun K) where
  toFun x :=
    { toFun := fun f => ⟨fun g => f.1 (x⁻¹ * g), fun g b hb => (congrArg f.1 (mul_assoc _ _ _).symm).trans (f.2.1 _ b hb), by
        obtain ⟨S, hS⟩ := f.2.2
        refine ⟨S.image (x * ·), fun g hg => ?_⟩
        obtain ⟨s, hs, b, hb, e⟩ := hS _ hg
        exact ⟨x * s, Finset.mem_image_of_mem _ hs, b, hb, by rw [mul_assoc, ← e, mul_inv_cancel_left]⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := LinearMap.ext fun f => Subtype.ext (funext fun g => by simp)
  map_mul' x y := LinearMap.ext fun f => Subtype.ext (funext fun g => by simp [mul_assoc])

private theorem exists_conv_inv (K : Subgroup G) (hK : IsCommensurated K) (t : G) (hfin : ∀ x, (cosets K x).Finite)
    (T : fixed (lrep K) K ≃ₗ[ℂ] fixed (lrep K) K) (hT : ∀ v, (T v : cfun K) = ∑ᶠ q ∈ cosets K t, lrep K q.out v) :
    ∃ φ ∈ Hecke ℂ K, conv K φ (dosetInd ℂ K t) = dosetInd ℂ K 1 := by
  have toH : ∀ v : fixed (lrep K) K, v.1.1 ∈ Hecke ℂ K := fun v => by
    refine ⟨fun a b g => ?_, ?_⟩
    · have h := congrFun (congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 v.2 a⁻¹ (inv_mem a.2))) g
      rw [v.1.2.1 _ b b.2]
      simpa [lrep] using h
    · obtain ⟨S, hS⟩ := v.1.2.2
      refine ⟨S, fun g hg => ?_⟩
      obtain ⟨s, hs, b, hb, e⟩ := hS g hg
      exact ⟨s, hs, 1, ⟨b, hb⟩, by simpa using e⟩
  have ofH : ∀ f ∈ Hecke ℂ K, ∃ v : fixed (lrep K) K, v.1.1 = f := fun f hf => by
    obtain ⟨h1, S, hS⟩ := hf
    refine ⟨⟨⟨f, fun g b hb => by simpa using h1 1 ⟨b, hb⟩ g, S.biUnion fun s => (hfin s).toFinset.image Quotient.out, fun g hg => ?_⟩,
      GlobalTheory.LGrp.mem_fixed.2 fun a ha => Subtype.ext (funext fun g => ?_)⟩, rfl⟩
    · obtain ⟨s, hs, a, b, e⟩ := hS g hg
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
      refine ⟨(g : G ⧸ K).out, Finset.mem_biUnion.2 ⟨s, hs, Finset.mem_image_of_mem _ ((hfin s).mem_toFinset.2
        ⟨g, DoubleCoset.mem_doubleCoset.2 ⟨a, a.2, b, b.2, e⟩, rfl⟩)⟩, k⁻¹, inv_mem k.2, by rw [hk]; simp⟩
    · simpa [lrep] using h1 ⟨a⁻¹, inv_mem ha⟩ 1 g
  have hTc : ∀ v, (T v).1.1 = conv K (dosetInd ℂ K t) v.1.1 := fun v => by
    funext g
    rw [hT, finsum_mem_eq_finite_toFinset_sum _ (hfin t), Submodule.coe_sum, Finset.sum_apply, conv,
      finsum_eq_sum_of_support_subset (s := (hfin t).toFinset)]
    · refine Finset.sum_congr rfl fun q hq => ?_
      obtain ⟨y, hy, rfl⟩ := (hfin t).mem_toFinset.1 hq
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K y
      obtain ⟨a, ha, b, hb, e⟩ := DoubleCoset.mem_doubleCoset.1 hy
      have : (y : G ⧸ K).out ∈ DoubleCoset.doubleCoset t (K : Set G) K :=
        DoubleCoset.mem_doubleCoset.2 ⟨a, ha, b * k, mul_mem hb k.2, by rw [hk, e, mul_assoc]⟩
      rw [dosetInd, Set.indicator_of_mem this, Pi.one_apply, one_mul]
      rfl
    · intro q hq
      have h : dosetInd ℂ K t q.out ≠ 0 := left_ne_zero_of_mul hq
      exact Finset.mem_coe.2 ((hfin t).mem_toFinset.2 ⟨q.out, Set.mem_of_indicator_ne_zero h, q.out_eq'⟩)
  have ht := Final.DosetIndMem G K ℂ t
  have h1 := Final.DosetIndMem G K ℂ 1
  obtain ⟨e, he⟩ := ofH _ h1
  have hφ := toH (T.symm e)
  have h2 : conv K (dosetInd ℂ K t) (T.symm e).1.1 = dosetInd ℂ K 1 := by rw [← hTc, T.apply_symm_apply, he]
  refine ⟨_, hφ, ?_⟩
  obtain ⟨u, hu⟩ := ofH _ (Final.HeckeConvMem G K ℂ hK _ hφ _ ht)
  rw [← hu, ← he]
  congr 2
  apply T.injective
  refine Subtype.ext (Subtype.ext ?_)
  rw [hTc, hTc, hu, he, ← Final.HeckeAssoc G K ℂ hK _ ht _ hφ _ ht, h2,
    (Final.HeckeUnit G K ℂ _ ht).1, (Final.HeckeUnit G K ℂ _ ht).2]

private theorem comm_of_fin (K : Subgroup G) (hfin : ∀ x, (cosets K x).Finite) : IsCommensurated K := by
  intro g
  have h := hfin g
  rw [cosets_eq_orbit] at h
  have e : (K.map (MulAut.conj g).toMonoidHom).subgroupOf K = MulAction.stabilizer K (g : G ⧸ K) := by
    ext k
    rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff, Subgroup.mem_map_equiv]
    show _ ↔ ((k.1 * g : G) : G ⧸ K) = g
    rw [eq_comm, QuotientGroup.eq]
    simp [mul_assoc]
  rw [Subgroup.relIndex, e, MulAction.index_stabilizer]
  exact ((Set.ncard_pos h).2 ⟨_, MulAction.mem_orbit_self _⟩).ne'


open ValuativeRel GlobalTheory.SmGL GlobalTheory.GLDoubling in
theorem iwInvT (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ϖ : kˣ)
    (hϖ : valuation k (ϖ : k) = uniformizer k) (ν : Fin n → ℤ) (hν : Antitone ν) :
    ∃ φ ∈ Hecke ℂ (iwahori k (Fin n)), conv (iwahori k (Fin n)) φ (dosetInd ℂ (iwahori k (Fin n)) (torusElt k (Fin n) ϖ ν)) =
      dosetInd ℂ (iwahori k (Fin n)) 1 := by
  obtain ⟨-, T, hT, -⟩ := exists_equiv_doubleCoset k n ϖ hϖ ν hν ℂ _ (lrep (iwahori k (Fin n)))
  exact exists_conv_inv _ (comm_of_fin _ finite_cosets) _ finite_cosets T hT

end UpperTheory.Gal.CertificateRingHomMap
end
end

section -- merged from Development.AutomorphicArithmetic.IwahoriCommensurability.CharpolySmulSeparable
open Polynomial

namespace UpperTheory

theorem charpoly_smul_alt {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι k) {c : k} (hc : c ≠ 0) :
    (c • M).charpoly =
      C (c ^ Fintype.card ι) * M.charpoly.comp (C c⁻¹ * X) :=
  _root_.UpperTheory.Reformulated.B.Qh50.charpoly_smul_alt M hc

theorem charpoly_smul_separable :
    ∀ (k : Type) [Field k] (n : ℕ) (c : k), c ≠ 0 → ∀ M : Matrix (Fin n) (Fin n) k, M.charpoly.Separable → (c • M).charpoly.Separable := by
  intro k _ n c hc M h
  have hcc : (C c : k[X]) * C c⁻¹ = 1 := by rw [← C_mul, mul_inv_cancel₀ hc, C_1]
  rw [charpoly_smul_alt M hc]
  have hcomp : (M.charpoly.comp (C c⁻¹ * X)).Separable := by
    obtain ⟨a, b, hab⟩ := h
    refine ⟨a.comp (C c⁻¹ * X), b.comp (C c⁻¹ * X) * C c, ?_⟩
    have h1 := congrArg (fun p : k[X] => p.comp (C c⁻¹ * X)) hab
    simp only [add_comp, mul_comp, one_comp] at h1
    rw [derivative_comp, ← h1]
    simp only [derivative_mul, derivative_C, derivative_X, zero_mul, zero_add, mul_one]
    linear_combination ((b.comp (C c⁻¹ * X)) * (derivative M.charpoly).comp (C c⁻¹ * X)) * hcc
  have hu : IsUnit (C (c ^ Fintype.card (Fin n)) : k[X]) :=
    isUnit_C.2 (pow_ne_zero _ hc).isUnit
  rw [Polynomial.Separable, derivative_mul, derivative_C, zero_mul, zero_add]
  exact (isCoprime_mul_unit_left hu _ _).2 hcomp

end UpperTheory
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.ExistsInvertibleHeckeFunctionAtFinitePlaces
noncomputable section

open Formalism.UG (Hecke conv dosetInd IsCommensurated)
open UpperTheory.Gal.W2.Seed

namespace UpperTheory.Gal.Spc

variable {X M M' : Type} [Group X] [Group M] [Group M']

private theorem fin_out {K : Subgroup X} (hK : IsCommensurated K) {f : X → ℂ} (hf : f ∈ Hecke ℂ K) (c : X ⧸ K → ℂ) :
    (Function.support fun q : X ⧸ K => f q.out * c q).Finite := by
  refine (GlobalTheory.LFun.finite_heckeVec hK hf (1 : Representation ℂ X ℂ) 1).subset fun q hq => ?_
  simpa using left_ne_zero_of_mul hq

private theorem conv_add {K : Subgroup X} (hK : IsCommensurated K) {f f' : X → ℂ} (hf : f ∈ Hecke ℂ K) (hf' : f' ∈ Hecke ℂ K)
    (y : X → ℂ) (g : X) : conv K (f + f') y g = conv K f y g + conv K f' y g := by
  simp only [conv, Pi.add_apply, add_mul]
  exact finsum_add_distrib (fin_out hK hf _) (fin_out hK hf' _)

private theorem conv_smul (K : Subgroup X) (r : ℂ) (f y : X → ℂ) (g : X) : conv K (r • f) y g = r * conv K f y g := by
  simp only [conv, Pi.smul_apply, smul_eq_mul, mul_assoc, mul_finsum]

private theorem ind_one (K : Subgroup X) (g : X) : conv K (dosetInd ℂ K 1) (dosetInd ℂ K 1) g = dosetInd ℂ K 1 g := by
  have h1 : ∀ x, x ∈ DoubleCoset.doubleCoset (1 : X) (K : Set X) K ↔ x ∈ K := fun x => by
    rw [DoubleCoset.mem_doubleCoset]
    exact ⟨by rintro ⟨a, ha, b, hb, rfl⟩; exact mul_mem (mul_mem ha (one_mem K)) hb, fun h => ⟨x, h, 1, one_mem K, by simp⟩⟩
  have h0 : ((1 : X) : X ⧸ K).out ∈ K := by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (1 : X)
    rw [hk, one_mul]
    exact k.2
  rw [conv, finsum_eq_single _ ((1 : X) : X ⧸ K) fun q hq => ?_]
  · rw [dosetInd, Set.indicator_of_mem ((h1 _).2 h0), Pi.one_apply, one_mul]
    by_cases hg : g ∈ K
    · rw [Set.indicator_of_mem ((h1 _).2 hg), Set.indicator_of_mem ((h1 _).2 (mul_mem (inv_mem h0) hg))]
      rfl
    · rw [Set.indicator_of_notMem (mt (h1 _).1 hg), Set.indicator_of_notMem fun h => hg ?_]
      simpa using mul_mem h0 ((h1 _).1 h)
  · rw [dosetInd, Set.indicator_of_notMem fun h => hq ?_, zero_mul]
    rw [← q.out_eq', QuotientGroup.eq]
    simpa using (h1 _).1 h

private theorem lift_ex (T : TyLev X M) (L : Loc X M') (I : Subgroup M') (h1 : L.Fact T.K I) (h2 : T.L.Apart L) (hI : IsCommensurated I)
    (t : M') {φ : M' → ℂ} (hφ : φ ∈ Hecke ℂ I) : ∃ v ∈ Hecke ℂ T.K₀, ∀ g, conv T.K₀ v (T.tf (L.loc t)) g =
      T.tf 1 (g * (L.loc (L.pr g))⁻¹) * conv I φ (dosetInd ℂ I t) (L.pr g) := by
  refine GlobalTheory.LFun.hecke_induction (p := fun φ => ∃ v ∈ Hecke ℂ T.K₀, ∀ g, conv T.K₀ v (T.tf (L.loc t)) g =
      T.tf 1 (g * (L.loc (L.pr g))⁻¹) * conv I φ (dosetInd ℂ I t) (L.pr g)) ⟨0, zero_mem _, fun g => by simp [conv]⟩ ?_ ?_ hφ
  · rintro f hf f' hf' ⟨v, hv, e⟩ ⟨v', hv', e'⟩
    exact ⟨v + v', add_mem hv hv', fun g => by rw [conv_add T.cms hv hv', conv_add hI hf hf', e, e', mul_add]⟩
  · intro r s
    refine ⟨r • T.tf (L.loc s), Submodule.smul_mem _ _ (pTfAdm X M T _ (h2.1 s)).1.1, fun g => ?_⟩
    rw [conv_smul, conv_smul, tfLoc_holds X M M' T L I h1 h2, mul_left_comm]

private theorem inv_ex (T : TyLev X M) (L : Loc X M') (I : Subgroup M') (h1 : L.Fact T.K I) (h2 : T.L.Apart L) (hI : IsCommensurated I)
    (t : M') {φ : M' → ℂ} (hφ : φ ∈ Hecke ℂ I) (e : conv I φ (dosetInd ℂ I t) = dosetInd ℂ I 1) :
    ∃ v ∈ Hecke ℂ T.K₀, conv T.K₀ v (T.tf (L.loc t)) = T.tf 1 := by
  obtain ⟨v, hv, h⟩ := lift_ex T L I h1 h2 hI t hφ
  refine ⟨v, hv, funext fun g => ?_⟩
  have h3 := tfLoc_holds X M M' T L I h1 h2 1 1 g
  rw [map_one, (tfIdem_holds X M T 1 (map_one _)).2.1, ind_one] at h3
  rw [h, e, ← h3]

theorem exists_invertible_hecke_function_at_finite_places : ∀ (X M : Type) [Group X] [Group M] (T : TyLev X M) (ι : Type) (M' : ι → Type) [∀ w, Group (M' w)] (L : ∀ w, Loc X (M' w))
    (I : ∀ w, Subgroup (M' w)) (t : ∀ w, M' w) (W : Finset ι),
    (∀ w ∈ W, (L w).Fact T.K (I w) ∧ T.L.Apart (L w) ∧ ∀ w' ∈ W, w ≠ w' → (L w).Apart (L w')) →
    (∀ w ∈ W, IsCommensurated (I w) ∧ ∃ φ ∈ Hecke ℂ (I w), conv (I w) φ (dosetInd ℂ (I w) (t w)) = dosetInd ℂ (I w) 1) →
    ∃ τ ∈ Subgroup.closure {y | ∃ w ∈ W, y = (L w).loc (t w)}, T.L.pr τ = 1 ∧ (∀ w ∈ W, (L w).pr τ = t w) ∧
      (∀ h, T.L.pr h = 1 → (∀ w ∈ W, (L w).pr h = 1) → conv T.K₀ (T.tf τ) (T.tf h) = conv T.K₀ (T.tf h) (T.tf τ)) ∧
      ∃ u' ∈ Hecke ℂ T.K₀, conv T.K₀ u' (T.tf τ) = T.tf 1 := by
  intro X M _ _ T ι M' _ L I t W
  classical
  induction W using Finset.induction_on with
  | empty =>
    refine fun _ _ => ⟨1, one_mem _, map_one _, by simp, fun h hh _ => ?_, T.tf 1, (pTfAdm X M T 1 (map_one _)).1.1,
      (tfIdem_holds X M T 1 (map_one _)).2.1⟩
    rw [(tfIdem_holds X M T h hh).2.1, (tfIdem_holds X M T h hh).2.2]
  | insert w W hw ih =>
    intro h1 h2
    obtain ⟨τ, m, p0, p1, c, u, hu, e⟩ := ih
      (fun x hx => ⟨(h1 x (Finset.mem_insert_of_mem hx)).1, (h1 x (Finset.mem_insert_of_mem hx)).2.1,
        fun y hy => (h1 x (Finset.mem_insert_of_mem hx)).2.2 y (Finset.mem_insert_of_mem hy)⟩)
      fun x hx => h2 x (Finset.mem_insert_of_mem hx)
    obtain ⟨f1, f2, f3⟩ := h1 w (Finset.mem_insert_self w W)
    obtain ⟨g1, φ, g2, g3⟩ := h2 w (Finset.mem_insert_self w W)
    have ap : ∀ x ∈ W, (L w).Apart (L x) := fun x hx => f3 x (Finset.mem_insert_of_mem hx) fun h => hw (h ▸ hx)
    have q : (L w).pr τ = 1 := (Subgroup.closure_le (L w).pr.ker).2 (by rintro _ ⟨x, hx, rfl⟩; exact (ap x hx).1 _) m
    obtain ⟨v, hv, ev⟩ := inv_ex T (L w) (I w) f1 f2 g1 (t w) g2 g3
    have a1 := (pTfAdm X M T _ (f2.1 (t w))).1.1
    have a2 := (pTfAdm X M T τ p0).1.1
    have R := pConvRing X T.K₀ T.cms
    have e1 := tfMulL_holds X M _ T (L w) (I w) f1 f2 (t w) τ p0 q
    refine ⟨(L w).loc (t w) * τ, mul_mem (Subgroup.subset_closure ⟨w, Finset.mem_insert_self w W, rfl⟩)
      (Subgroup.closure_mono (by rintro _ ⟨x, hx, rfl⟩; exact ⟨x, Finset.mem_insert_of_mem hx, rfl⟩) m),
      by rw [map_mul, f2.1, p0, one_mul], fun x hx => ?_, fun h hh hW => ?_, conv T.K₀ u v, (R u hu v hv).1, ?_⟩
    · rcases Finset.mem_insert.1 hx with rfl | hx
      · rw [map_mul, (L x).pr_loc, q, mul_one]
      · rw [map_mul, (ap x hx).2, p1 x hx, one_mul]
    · have a3 := (pTfAdm X M T h hh).1.1
      have hw1 := hW w (Finset.mem_insert_self w W)
      rw [← e1, (R _ a1 _ a2).2 _ a3, c h hh fun x hx => hW x (Finset.mem_insert_of_mem hx), ← (R _ a1 _ a3).2 _ a2,
        tfMulL_holds X M _ T (L w) (I w) f1 f2 (t w) h hh hw1, ← tfMulR_holds X M _ T (L w) (I w) f1 f2 (t w) h hh hw1,
        (R _ a3 _ a1).2 _ a2]
    · rw [← e1, (R u hu v hv).2 _ (R _ a1 _ a2).1, ← (R v hv _ a1).2 _ a2, ev, (tfIdem_holds X M T τ p0).2.2, e]

end UpperTheory.Gal.Spc
end
end

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp cj GLw)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl
open Formalism.UG (Hecke conv dosetInd IsCommensurated)
open scoped Classical

namespace UpperTheory.Gal.Spc

section Abstract

variable {X : Type} [Group X]

private def trl (z : X) (f : X → ℂ) : X → ℂ := fun g => f (z * g)

private theorem trl_mem {K : Subgroup X} {z : X} (hz : ∀ g, z * g = g * z) {f : X → ℂ} (hf : f ∈ Hecke ℂ K) :
    trl z f ∈ Hecke ℂ K := by
  obtain ⟨hb, S, hS⟩ := hf
  refine ⟨fun a b g => ?_, S.image (z⁻¹ * ·), fun g hg => ?_⟩
  · show f (z * (a * g * b)) = f (z * g)
    rw [← hb a b (z * g), ← mul_assoc, ← mul_assoc, hz a, mul_assoc (a : X) z g]
  · obtain ⟨s, hs, a, b, e⟩ := hS _ hg
    refine ⟨z⁻¹ * s, Finset.mem_image_of_mem _ hs, a, b, ?_⟩
    have h1 : (a : X) * z⁻¹ = z⁻¹ * a := by
      rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hz a, inv_mul_cancel_left]
    rw [← mul_assoc, h1, mul_assoc z⁻¹, mul_assoc z⁻¹, ← e, inv_mul_cancel_left]

private theorem conv_trl_right (K : Subgroup X) {z : X} (hz : ∀ g, z * g = g * z) (f f' : X → ℂ) :
    conv K f (trl z f') = trl z (conv K f f') := by
  funext g
  unfold conv trl
  refine finsum_congr fun x => ?_
  rw [← mul_assoc, hz, mul_assoc]

private theorem conv_trl_left {K : Subgroup X} (z : X) {f f' : X → ℂ} (hf : f ∈ Hecke ℂ K) (hf' : f' ∈ Hecke ℂ K) :
    conv K (trl z f) f' = trl z (conv K f f') := by
  funext g
  unfold conv trl
  beta_reduce
  rw [← finsum_comp_equiv (MulAction.toPerm z : X ⧸ K ≃ X ⧸ K) (f := fun x : X ⧸ K => f x.out * f' (x.out⁻¹ * (z * g)))]
  refine finsum_congr fun y => ?_
  have hy : (MulAction.toPerm z : X ⧸ K ≃ X ⧸ K) y = (QuotientGroup.mk (z * y.out) : X ⧸ K) := by
    conv_lhs => rw [← QuotientGroup.out_eq' y]
    rfl
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K (z * y.out)
  simp only [hy, hh]
  congr 1
  · simpa using (hf.1 1 h (z * y.out)).symm
  · rw [← hf'.1 h⁻¹ 1 (y.out⁻¹ * g)]
    congr 1
    simp only [Subgroup.coe_inv, OneMemClass.coe_one]
    group

private theorem comm_span {K : Subgroup X} (hK : IsCommensurated K) {u : X → ℂ} (hu : u ∈ Hecke ℂ K) {s : Set (X → ℂ)}
    (hs : ∀ f ∈ s, f ∈ Hecke ℂ K ∧ conv K u f = conv K f u) :
    ∀ f ∈ Submodule.span ℂ s, f ∈ Hecke ℂ K ∧ conv K u f = conv K f u := by
  have fin : ∀ a ∈ Hecke ℂ K, ∀ b : X ⧸ K → ℂ, (Function.support fun x : X ⧸ K => a x.out * b x).Finite := fun a ha b =>
    (Formalism.UG.P.finite_support_cosets hK ha.2).subset fun x hx => left_ne_zero_of_mul hx
  intro f hf
  induction hf using Submodule.span_induction with
  | mem f h => exact hs f h
  | zero => exact ⟨zero_mem _, by funext g; simp [conv]⟩
  | add f f' _ _ h h' =>
    refine ⟨add_mem h.1 h'.1, funext fun g => ?_⟩
    have e := congrFun h.2 g
    have e' := congrFun h'.2 g
    unfold conv at e e' ⊢
    simp only [Pi.add_apply, mul_add, add_mul]
    rw [finsum_add_distrib (fin u hu _) (fin u hu _), finsum_add_distrib (fin f h.1 _) (fin f' h'.1 _), e, e']
  | smul c f _ h =>
    refine ⟨Submodule.smul_mem _ c h.1, funext fun g => ?_⟩
    have e := congrFun h.2 g
    unfold conv at e ⊢
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, mul_left_comm _ c]
    rw [← mul_finsum, ← mul_finsum, e]

private theorem tf_supp {M : Type} [Group M] (T : TyLev X M) {h g : X} (e : T.tf h g ≠ 0) :
    ∃ a ∈ T.K, ∃ b ∈ T.K, g = a * h * b := by
  refine DoubleCoset.mem_doubleCoset.1 ?_
  by_contra hn
  apply e
  simp [TyLev.tf, dosetInd, Set.indicator_of_notMem hn]

end Abstract

private theorem locT (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) :
    ∃ t : GL (Fin n) k,
      (∃ φ ∈ Hecke ℂ (GlobalTheory.SmGL.iwahori k (Fin n)), conv (GlobalTheory.SmGL.iwahori k (Fin n)) φ (dosetInd ℂ (GlobalTheory.SmGL.iwahori k (Fin n)) t) =
        dosetInd ℂ (GlobalTheory.SmGL.iwahori k (Fin n)) 1) ∧
      (∀ m : ℕ, ∀ a ∈ DoubleCoset.doubleCoset t (GlobalTheory.SmGL.iwahori k (Fin n) : Set (GL (Fin n) k)) (GlobalTheory.SmGL.iwahori k (Fin n)),
        ∀ b ∈ DoubleCoset.doubleCoset (t ^ m) (GlobalTheory.SmGL.iwahori k (Fin n) : Set (GL (Fin n) k)) (GlobalTheory.SmGL.iwahori k (Fin n)),
        a * b ∈ DoubleCoset.doubleCoset (t ^ (m + 1)) (GlobalTheory.SmGL.iwahori k (Fin n) : Set (GL (Fin n) k)) (GlobalTheory.SmGL.iwahori k (Fin n))) ∧
      ∀ m : ℕ, 1 ≤ m →
        ∀ y ∈ DoubleCoset.doubleCoset (t ^ m) (GlobalTheory.SmGL.iwahori k (Fin n) : Set (GL (Fin n) k)) (GlobalTheory.SmGL.iwahori k (Fin n)),
          y.val.charpoly.Separable := by
  obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective (ValuativeRel.uniformizer k)
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact ValuativeRel.uniformizer_ne_zero hx.symm
  have hν : StrictAnti fun i : Fin n => -(i : ℤ) := fun i j hij => by
    have : (i : ℕ) < j := hij
    show -((j : ℕ) : ℤ) < -((i : ℕ) : ℤ)
    omega
  refine ⟨_, CertificateRingHomMap.iwInvT k n (Units.mk0 x hx0) hx _ hν.antitone, UpperTheory.iwahori_doubleCoset_torus_mul_of_strictAnti k n (Units.mk0 x hx0) hx _ hν, fun m hm y hy => ?_⟩
  rw [GlobalTheory.TorusElementPower.torusElt_pow_eq] at hy
  obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hy
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  exact (GlobalTheory.IwahoriRegular.regular_split k n (Units.mk0 x hx0) hx _
    (fun i j hij => mul_lt_mul_of_pos_left (hν hij) hm') a ha b hb).1

private theorem integ_mul {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G} {a b : G.GAf}
    (ha : Integ L a) (hb : Integ L b) : Integ L (a * b) := fun v hv => by
  rw [map_mul, Module.End.mul_apply]
  exact ha _ (hb v hv)

private theorem scal_comm {k : Type} [Field k] {n : ℕ} {s : GL (Fin n) k} {a : k} (hs : s.val = a • (1 : Matrix (Fin n) (Fin n) k))
    (y : GL (Fin n) k) : Commute s y :=
  Units.ext (by rw [Units.val_mul, Units.val_mul, hs, smul_mul_assoc, mul_smul_comm, one_mul, mul_one])

private theorem scal_sep {k : Type} [Field k] {n : ℕ} {s : GL (Fin n) k} {a : k} (ha : a ≠ 0)
    (hs : s.val = a • (1 : Matrix (Fin n) (Fin n) k)) (m : ℕ) (y : GL (Fin n) k) (h : (s ^ m * y).val.charpoly.Separable) :
    y.val.charpoly.Separable := by
  have := UpperTheory.charpoly_smul_separable k n (a ^ m)⁻¹ (inv_ne_zero (pow_ne_zero m ha)) _ h
  rwa [Units.val_mul, Units.val_pow_eq_pow_val, hs, _root_.smul_pow, one_pow, smul_mul_assoc, one_mul, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero m ha), one_smul] at this

private theorem cen_ex {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime] {S : Setup A n p}
    (F : Frame S) (c : ℕ) (hc : 0 < c) : ∃ d : GUf E n, (∀ g, F.j d * g = g * F.j d) ∧
      (∀ w : Plc E, (comp w d).val = (c : w.adicCompletion E) • (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E))) ∧
      ∀ v, S.L.actG (F.j d) v = c • v := by
  first
    | exact UpperTheory.exists_levelSubgroup_central_scalar_of_pos E A n p S F c hc
    | (obtain ⟨y, -, -, h1, -, h2, h3⟩ := UpperTheory.exists_levelSubgroup_central_scalar_of_pos E A n p S F c hc; exact ⟨_, h2, h1, h3⟩)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem auxFn : ExistsIdempotentHeckeOperatorWithRegularSupport := by
  intro E _ _ _ A n p _ S F x U w₀ Up V hn hsc hgen hoff hq r W hA N hrN hst L hw Ty hTy
  obtain ⟨hF, -, c, hc, -, hcK⟩ := tyFact E A n p S F x U w₀ Up V hn hsc hgen hoff hq r W hA N hrN hst L hw Ty hTy
  choose t hti htm hts using fun w : Spl E p => locT (w.1.adicCompletion E) n
  obtain ⟨τ, hτ, hτ0, hτw, hcm, u', hu', hu'τ⟩ := exists_invertible_hecke_function_at_finite_places _ _ Ty (Spl E p) (fun w => GLw n w.1) L (fun w => Iw n w.1) t W hF
    fun w _ => ⟨UpperTheory.isCommensurated_iwahoriSubgroup_gl_fin _ n, hti w⟩
  obtain ⟨g₀, hg₀, hg₀u⟩ : ∃ g₀ : GUf E n, F.j g₀ = τ⁻¹ ∧ ∀ u : Plc E, (r : 𝓞 E) ∉ u.asIdeal → comp u g₀ = 1 := by
    have hτ' := inv_mem hτ
    generalize τ⁻¹ = σ at hτ'
    haveI : Fact r.Prime := ⟨hA.prime⟩
    induction hτ' using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨w, hwW, rfl⟩ := hy
      exact ⟨CertificateRingHomMap.loc w.2.1 (t w), ((hTy.fac w).2 _).symm, fun u hu =>
        CertificateRingHomMap.comp_loc_of_apart w.2.1 (Ne.symm (apart_of_not_mem hu (hA.half.above w hwW))) _⟩
    | one => exact ⟨1, map_one _, fun _ _ => map_one _⟩
    | mul a b _ _ ha hb =>
      obtain ⟨a', rfl, ha⟩ := ha
      obtain ⟨b', rfl, hb⟩ := hb
      exact ⟨a' * b', map_mul _ _ _, fun u hu => by rw [map_mul, ha u hu, hb u hu, one_mul]⟩
    | inv a _ ha =>
      obtain ⟨a', rfl, ha⟩ := ha
      exact ⟨a'⁻¹, map_inv _ _, fun u hu => by rw [map_inv, ha u hu, inv_one]⟩
  obtain ⟨M, hM⟩ := UpperTheory.exists_primePow_scalar_integral_of_good_prime E A n p S F r hA.prime hA.good g₀ hg₀u
  obtain ⟨dc, hdc, hdcw, hdcv⟩ := cen_ex F c hc
  obtain ⟨dr, hdr, hdrw, -⟩ := cen_ex F (r ^ M) (pow_pos hA.prime.pos M)
  have hI := hM dr hdrw
  rw [map_mul, hg₀] at hI
  have hK : ∀ k ∈ Ty.K, Integ S.L (k * F.j dc) := fun k hk v hv => by
    rw [map_mul, Module.End.mul_apply, hdcv, map_nsmul]
    exact hcK k hk v hv
  obtain ⟨D, hD⟩ : ∃ D, D = F.j dc * F.j dr * F.j dc := ⟨_, rfl⟩
  have hDc : ∀ g, D * g = g * D := fun g => by
    rw [hD, mul_assoc, hdc g, ← mul_assoc, mul_assoc _ _ g, hdr g, ← mul_assoc, hdc g]
    simp only [mul_assoc]
  have hDc' : ∀ g, D⁻¹ * g = g * D⁻¹ := fun g => by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hDc g, mul_inv_cancel_right]
  have hs : ∀ w : Spl E p, ((L w).pr D).val =
      ((c * r ^ M * c : ℕ) : w.1.adicCompletion E) • (1 : Matrix (Fin n) (Fin n) (w.1.adicCompletion E)) := fun w => by
    rw [hD, ← map_mul, ← map_mul, (hTy.fac w).1, map_mul, map_mul, Units.val_mul, Units.val_mul, hdcw, hdrw]
    simp only [smul_mul_assoc, one_mul, smul_smul, Nat.cast_mul]
  have hs0 : ∀ w : Spl E p, ((c * r ^ M * c : ℕ) : w.1.adicCompletion E) ≠ 0 := fun w => by
    haveI : CharZero (w.1.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
    exact Nat.cast_ne_zero.2 (Nat.mul_pos (Nat.mul_pos hc (pow_pos hA.prime.pos M)) hc).ne'
  have hτH : Ty.tf τ ∈ Hecke ℂ Ty.K₀ := (pTfAdm _ _ Ty τ hτ0).1.1
  have h1H : Ty.tf 1 ∈ Hecke ℂ Ty.K₀ := (pTfAdm _ _ Ty 1 (map_one _)).1.1
  have hid := (tfIdem_holds _ _ Ty τ hτ0).2
  have hue : conv Ty.K₀ (trl D (Ty.tf τ)) (Ty.tf 1) = trl D (Ty.tf τ) := by rw [conv_trl_left D hτH h1H, hid.1]
  have hsupp : ∀ g, trl D (Ty.tf τ) g ≠ 0 → Integ S.L g⁻¹ ∧
      ∀ w ∈ W, (L w).pr D * (L w).pr g ∈ DoubleCoset.doubleCoset (t w) (Iw n w.1 : Set (GLw n w.1)) (Iw n w.1) := by
    intro g hg
    obtain ⟨a, ha, b, hb, e⟩ := tf_supp Ty hg
    refine ⟨?_, fun w hwW => ?_⟩
    · have e' : g⁻¹ = b⁻¹ * F.j dc * (τ⁻¹ * F.j dr * (a⁻¹ * F.j dc)) := by
        have e1 : g⁻¹ = b⁻¹ * τ⁻¹ * a⁻¹ * D := by
          rw [← _root_.mul_inv_rev, ← _root_.mul_inv_rev, ← mul_assoc, ← e, _root_.mul_inv_rev, inv_mul_cancel_right]
        rw [e1, mul_assoc b⁻¹ (F.j dc), hdc, mul_assoc τ⁻¹, hdr, hD]
        simp only [mul_assoc]
      rw [e']
      exact integ_mul (hK _ (inv_mem hb)) (integ_mul hI (hK _ (inv_mem ha)))
    · rw [← map_mul, e, map_mul, map_mul, hτw w hwW]
      exact DoubleCoset.mem_doubleCoset.2 ⟨_, (hF w hwW).1.2 a ha, _, (hF w hwW).1.2 b hb, rfl⟩
  have hpow : ∀ m : ℕ, ∀ g, powFn Ty.K₀ (trl D (Ty.tf τ)) (Ty.tf 1) (m + 1) g ≠ 0 → Integ S.L g⁻¹ ∧
      ∀ w ∈ W, (L w).pr D ^ (m + 1) * (L w).pr g ∈
        DoubleCoset.doubleCoset (t w ^ (m + 1)) (Iw n w.1 : Set (GLw n w.1)) (Iw n w.1) := by
    intro m
    induction m with
    | zero =>
      intro g hg
      simp only [zero_add, pow_one]
      refine hsupp g ?_
      rw [← hue]
      exact hg
    | succ m ih =>
      intro g hg
      unfold powFn at hg
      rw [Function.iterate_succ_apply'] at hg
      obtain ⟨a, b, ha, hb, rfl⟩ := pConvSupp _ _ _ _ _ hg
      obtain ⟨a1, a2⟩ := hsupp a ha
      obtain ⟨b1, b2⟩ := ih b hb
      refine ⟨by rw [_root_.mul_inv_rev]; exact integ_mul b1 a1, fun w hwW => ?_⟩
      have := htm w (m + 1) _ (a2 w hwW) _ (b2 w hwW)
      rwa [mul_assoc, ← mul_assoc ((L w).pr a), ← ((scal_comm (hs w) ((L w).pr a)).pow_left (m + 1)).eq, mul_assoc,
        ← mul_assoc, ← pow_succ', ← map_mul] at this
  refine ⟨trl D (Ty.tf τ), trl_mem hDc hτH, trl D⁻¹ u', trl_mem hDc' hu', ?_, hue, ?_, fun f hf => ?_, fun m hm => ?_⟩
  · rw [conv_trl_right _ hDc, hid.2]
  · rw [conv_trl_left _ hu' (trl_mem hDc hτH), conv_trl_right _ hDc, hu'τ]
    funext g
    simp [trl]
  · obtain ⟨hfH, hfc⟩ := comm_span Ty.cms hτH (by
      rintro f ⟨h, h0, h1, rfl⟩
      exact ⟨(pTfAdm _ _ Ty h h0).1.1, hcm h h0 h1⟩) f hf
    rw [conv_trl_left D hτH hfH, conv_trl_right _ hDc, hfc]
  · obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    refine ⟨fun w => {y | (L w).pr D ^ (m + 1) * y ∈
      DoubleCoset.doubleCoset (t w ^ (m + 1)) (Iw n w.1 : Set (GLw n w.1)) (Iw n w.1)}, fun w _ y hy => ⟨?_, fun a ha => ?_⟩, hpow m⟩
    · exact scal_sep (hs0 w) (hs w) _ y (hts w _ hm _ hy)
    · obtain ⟨a₁, h₁, a₂, h₂, e⟩ := DoubleCoset.mem_doubleCoset.1 hy
      refine DoubleCoset.mem_doubleCoset.2 ⟨a * a₁, mul_mem ha h₁, a₂, h₂, ?_⟩
      rw [← mul_assoc, ((scal_comm (hs w) a).pow_left (m + 1)).eq, mul_assoc, e]
      simp only [mul_assoc]

end UpperTheory.Gal.Spc
