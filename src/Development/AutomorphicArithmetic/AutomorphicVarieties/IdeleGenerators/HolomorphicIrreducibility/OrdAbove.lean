module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SelfDualR
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.AlgOfCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.JacqOfU
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeCharLocalArtinEqCyclotomicTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcPolar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeOperatorsCommuteOnAutomorphicForms

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.LocalGlobalCompatibilityGl2
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.CompatReal
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsQuadraticOfInertia
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Published
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc

private theorem place_between {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
    [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (hA : IsPlaceOver A v) :
    ∃ w : HeightOneSpectrum (𝓞 L), IsPlaceOver A w ∧ w.under (𝓞 K) = v := by
  have hint : ∀ x : 𝓞 L, algebraMap L Ω (x : L) ∈ A := fun x => by
    have h : IsIntegral A (algebraMap L Ω (x : L)) :=
      (x.isIntegral_coe.map (algebraMap L Ω).toIntAlgHom).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
    rw [← hy]
    exact y.2
  let f : 𝓞 L →+* A := ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A hint
  let P : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal A).comap f
  have hP : ∀ x : 𝓞 L, A.valuation (algebraMap L Ω (x : L)) < 1 ↔ x ∈ P := fun x =>
    (A.valuation_lt_one_iff (f x)).symm
  have hu : v.asIdeal = P.under (𝓞 K) := by
    ext x
    rw [← hA x, Ideal.under, Ideal.mem_comap, ← hP, IsScalarTower.algebraMap_apply K L Ω]
    rfl
  have hne : P ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [hu, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  exact ⟨⟨P, inferInstance, hne⟩, hP, HeightOneSpectrum.ext hu.symm⟩

theorem UpperTheory.exists_quadratic_of_inertia :
    UpperTheory.V.Af.Cr.QuadCM → UpperTheory.V.Af.Cr.ImagGen → UpperTheory.V.Af.Cr.IneRes → UpperTheory.V.Af.Cr.ExQuadR := by
  intro hQ hI hR F Ω _ _ _ _ _ _ l _ h2 S hS
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : IsScalarTower ℚ F Ω := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosure ℚ Ω := ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.trans ℚ F Ω⟩
  have hT : {v | ¬ S v}.Finite := Filter.eventually_cofinite.1 hS
  have h1 : ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite,
      v ∉ (fun w : HeightOneSpectrum (𝓞 F) => w.under (𝓞 ℚ)) '' {v | ¬ S v} :=
    (hT.image _).eventually_cofinite_notMem
  obtain ⟨K₀, _, _, _, _, _, _, hK₀, hl, v₀, A, ⟨hv1, hv2⟩, hA, s, hs, hsn⟩ :=
    Cq.exQuad Ω l h2 _ (h1.and (hR ℚ F Ω))
  obtain ⟨d, y₀, hd, hy₀, hgen⟩ := hI K₀ hK₀
  obtain ⟨K, i1, i2, i3, i4, i5, i6, i7, hK, y, hy, hgenK⟩ := hQ F Ω (d : F) (algebraMap K₀ Ω y₀)
    (by rw [← map_pow, hy₀, map_ratCast, map_ratCast]) (fun φ => by rw [map_ratCast]; exact_mod_cast hd)
  obtain ⟨w, hw, hwv⟩ := place_between (L := F) hA
  obtain ⟨t, rfl⟩ := hv2 A hA hs
  refine ⟨K, i1, i2, i3, i4, i5, i6, i7, hK, fun j L hL x => ?_, w, A, ?_, hw, t, hs, ?_⟩
  · obtain ⟨a, b, rfl⟩ := hgenK x
    obtain ⟨z, hz⟩ := Cq.embPadic K₀ hK₀ l hl (j.comp (algebraMap K₀ Ω)) y₀
    rw [map_add (f := _), map_mul, hy, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, map_add (f := _), map_mul]
    refine add_mem (hL a) (mul_mem (hL b) ?_)
    rw [RingHom.comp_apply] at hz
    rw [← hz]
    exact L.1.algebraMap_mem z
  · by_contra h
    exact hv1 ⟨w, h, hwv⟩
  · rintro ⟨u, rfl⟩
    have hu : u (algebraMap K₀ Ω y₀) = algebraMap K₀ Ω y₀ := by rw [← hy]; exact u.commutes y
    refine hsn ⟨{ u.toRingEquiv with commutes' := fun x => ?_ }, AlgEquiv.ext fun _ => rfl⟩
    obtain ⟨a, b, rfl⟩ := hgen x
    show u _ = _
    simp only [map_add (f := _), map_mul, map_ratCast, hu]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ImaginaryGenerator
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Published
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc

theorem UpperTheory.imaginary_generator :
    UpperTheory.V.Af.Cr.ImagGen := by
  intro K _ _ _ h
  haveI : Algebra.IsQuadraticExtension ℚ K := ⟨h⟩
  obtain ⟨d, e, -, h0, h1⟩ := GlobalTheory.QuadSymbol.AlmostNorm.exists_basis_sq ℚ K
  have hy : e 1 ^ 2 = (d : K) := by rw [sq, h1]; simp
  have hx : ∀ x : K, ∃ a b : ℚ, x = (a : K) + (b : K) * e 1 := fun x => by
    refine ⟨e.repr x 0, e.repr x 1, ?_⟩
    conv_lhs => rw [← e.sum_repr x]
    rw [Fin.sum_univ_two, h0, Rat.smul_def, Rat.smul_def, mul_one]
  refine ⟨d, e 1, ?_, hy, hx⟩
  by_contra hd
  have hd0 : (0 : ℝ) ≤ d := by exact_mod_cast not_lt.1 hd
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  apply IsTotallyComplex.complexEmbedding_not_isReal φ
  have hφ : φ (e 1) ^ 2 = ((Real.sqrt d : ℝ) : ℂ) ^ 2 := by
    rw [← map_pow, hy, ← Complex.ofReal_pow, Real.sq_sqrt hd0]
    simp
  have hc : (starRingEnd ℂ) (φ (e 1)) = φ (e 1) := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hφ with h2 | h2 <;> simp [h2]
  rw [ComplexEmbedding.isReal_iff]
  ext1 x
  obtain ⟨a, b, rfl⟩ := hx x
  rw [ComplexEmbedding.conjugate_coe_eq]
  simp [hc]
end

noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open UpperTheory.V.Af.Bc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Af

private theorem eventually_under {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {P : HeightOneSpectrum (𝓞 E) → Prop} (h : ∀ᶠ w in Filter.cofinite, P w) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v ∧ P w := by
  rw [Filter.eventually_cofinite] at h ⊢
  refine (h.image fun w => w.under (𝓞 F)).subset fun v hv => ?_
  have := v.isMaximal
  obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
  have e : (⟨Q, hQ.isPrime, hne⟩ : HeightOneSpectrum (𝓞 E)).under (𝓞 F) = v :=
    HeightOneSpectrum.ext hl.over.symm
  exact ⟨_, fun hP => hv ⟨_, e, hP⟩, e⟩

private theorem sat_of_isoTwist {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ} {π : TR.CuspSub F n}
    {η : HChar F} (h : IsoTwist π η) {v : HeightOneSpectrum (𝓞 F)} (hη : η.UnrAt v) {B : Multiset ℂˣ}
    (hB : π.HasSat v B) : B = B.map (· * η.val v) := by
  obtain ⟨T, hT, -⟩ := h
  refine hB.unique (GlobalTheory.SphGal.hasSatGL_of_twist hη T.symm (fun g x => ?_) hB)
  obtain ⟨x, rfl⟩ := T.surjective x
  apply T.injective
  rw [LinearEquiv.symm_apply_apply, TR.CuspSub.locRep_eq, hT, map_smul, LinearEquiv.apply_symm_apply,
    TR.CuspSub.chiDet_locGL]
  rfl

private theorem algSat_eq (n q : ℕ) (B : Multiset ℂˣ) :
    algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := by
  simp [algSat, Multiset.bind_singleton, Multiset.map_map]

private theorem sf_isAlgPos_mul {F : Type} [Field F] [NumberField F] {χ χ' : HChar F} {n n' : (F →+* ℂ) → ℤ}
    (h : IsAlgPos χ n) (h' : IsAlgPos χ' n') : IsAlgPos (χ * χ') (n + n') := fun k hk => by
  have e : (χ * χ').inf k = χ.inf k * χ'.inf k := rfl
  rw [e, Units.val_mul, h k hk, h' k hk, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun φ _ => (zpow_add₀ ((map_ne_zero φ).2 k.ne_zero) _ _).symm

private theorem sf_quadChar_order (E : Type) [Field E] [NumberField E] [IsCMField E] : (quadChar E).OrderDvd 2 := by
  refine Subtype.ext (MonoidHom.ext fun x => ?_)
  change (Units.map (Int.castRingHom ℂ).toMonoidHom (GlobalTheory.IdeleNormChar.normSign E x)) ^ 2 = 1
  rw [← map_pow, Int.units_sq, map_one]

private theorem regAlg_twist {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {n : ℕ} {P : CuspSub K n}
    (h : (CG.mk P).IsRegAlg) {κ : HChar K} {m : (K →+* ℂ) → ℤ} (hκ : κ.IsAlg m) : (CG.mk (P.twist κ)).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
  have e := ((ParLaws.hasInfChar_infChar (CG.mk P) τ).twist κ).infChar_eq
  rw [CG.twist_mk] at e
  rw [e, (InfType.expo_of_infType K κ).1 m hκ τ]
  refine ⟨(h τ).1.map (add_left_injective _), fun z hz => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
  obtain ⟨k, rfl⟩ := (h τ).2 y hy
  exact ⟨k + m τ, by push_cast; ring⟩

private theorem noTwistRam (hP : Hypotheses₂) : Cr.NoTwistRam := by
  intro F E Ω _ _ _ _ _ _ _ _ _ _ _ l _ ι h2 n hn r π hc hatt ⟨s, hs, hs1⟩ η hη hT
  obtain ⟨δ, hδc, -, hδs, hδu⟩ := UpperTheory.exists_quadratic_sign_character F E Ω l h2
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed E, by
    haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
    exact Algebra.IsAlgebraic.trans F E Ω⟩
  obtain ⟨g, hg⟩ : RepIso r (tw r δ) := by
    refine isoOfFrob hP F Ω l ι n r _ hc (irrBasic.2 _ _ n r δ hc hδc) hatt.1 ((irrBasic.1 _ (G F Ω) _ n r).2.2 δ hatt.1) ?_
    filter_upwards [hatt.2, hδu, eventually_under (F := F) hη] with v hv hu hw
    obtain ⟨w, rfl, hw⟩ := hw
    obtain ⟨B, hB, hE⟩ := hv
    obtain ⟨h1, h3⟩ := hw (w.under (𝓞 F)) rfl
    refine ⟨_, hE, ?_⟩
    have h4 := UpperTheory.frobenius_eigenvalues_twist F Ω l ι n r δ _ _ _ hE (UpperTheory.frobenius_sign_compatibility F E Ω l ι δ hδs w hu)
    convert h4 using 1
    conv_lhs => rw [sat_of_isoTwist hT h1 hB]
    have h5 : ((η.val (w.under (𝓞 F)) : ℂˣ) : ℂ) = if normV w = normV (w.under (𝓞 F)) then 1 else -1 := by
      refine (congrArg Units.val h3).trans ?_
      change ((if normV w = normV (w.under (𝓞 F)) then 1 else -1 : ℂˣ) : ℂ) = _
      split_ifs <;> simp
    simp only [algSat_eq, Multiset.map_map]
    refine Multiset.map_congr rfl fun b _ => ?_
    rw [← h5]
    simp only [Function.comp_apply, Units.val_mul, mul_assoc]
  have h6 := congrArg (fun x : GL (Fin n) (Qbar l) => (x : Matrix (Fin n) (Fin n) (Qbar l)) ⟨0, hn⟩ ⟨0, hn⟩) (hg s)
  simp only [tw_val, hs1, mul_one, mul_inv_cancel, (hδs.2 s).resolve_left (mt (hδs.1 s).1 hs)] at h6
  norm_num at h6

private theorem exists_sign {K : Type} [Field K] [NumberField K] [IsCMField K] (χ : HChar (maximalRealSubfield K))
    (h : ∀ v v' : InfinitePlace (maximalRealSubfield K), χ.locInf v (-1) = χ.locInf v' (-1)) (b : ℤ) :
    ∃ k : ℕ, ∀ v, (χ * quadChar K ^ k).locInf v (-1) = (-1) ^ b := by
  obtain ⟨v₀⟩ : Nonempty (InfinitePlace (maximalRealSubfield K)) := inferInstance
  have hval : ∀ (k : ℕ) v, (χ * quadChar K ^ k).locInf v (-1) = χ.locInf v₀ (-1) * (-1) ^ k := fun k v => by
    change χ.locInf v (-1) * (quadChar K ^ k).locInf v (-1) = _
    rw [locInf_pow, quadChar_locInf, h v v₀]
  have h2 : χ.locInf v₀ (-1) ^ 2 = 1 := by rw [← map_pow, neg_one_sq, map_one]
  have h3 : ((χ.locInf v₀ (-1) : ℂˣ) : ℂ) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]
  simp only [hval, Units.ext_iff, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, Units.val_neg,
    Units.val_one]
  rcases sq_eq_one_iff.1 h3 with e | e <;> rcases Int.even_or_odd b with hb' | hb' <;> rw [e, hb'.neg_one_zpow]
  · exact ⟨0, fun _ => by simp⟩
  · exact ⟨1, fun _ => by simp⟩
  · exact ⟨1, fun _ => by simp⟩
  · exact ⟨0, fun _ => by simp⟩

private theorem csdTw (hg : GlobalTheory.Published.GaloisRepOfPolarizedPair) {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) : Cr.CsdTw := by
  intro K _ _ _ n hn P χ hreg hs hd
  have hN : ∀ (ψ : HChar (maximalRealSubfield K)) (k : ℕ), compNorm K (ψ * quadChar K ^ k) = compNorm K ψ := fun ψ k => by
    rw [map_mul, map_pow, compNorm_quadChar, one_pow, mul_one]
  obtain ⟨k, hk⟩ := exists_sign χ hs n
  obtain ⟨a, ha⟩ : ∃ a, IsAlgPos (χ * quadChar K ^ k) a := by
    obtain ⟨r, wt, HT, hr⟩ := hg K (AlgebraicClosure K) l ι n hn P (χ * quadChar K ^ k) hreg
      ⟨fun v => (hk v).trans (zpow_natCast _ _), by rwa [hN]⟩
    obtain ⟨μ, ⟨-, art, a, -, ha, -⟩, -⟩ := hr.pol
    exact ⟨a, ha⟩
  set χ₁ := χ * quadChar K ^ k with hχ₁
  have ha' : IsAlgPos χ₁⁻¹ (-a) := fun k hk => by
    rw [HChar.inf_inv, Units.val_inv_eq_inv_val, ha k hk, ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun φ _ => (zpow_neg _ _).symm
  obtain ⟨φ₀⟩ : Nonempty (maximalRealSubfield K →+* ℂ) := inferInstance
  obtain ⟨j, hj⟩ := exists_sign χ₁⁻¹ (fun v v' => congrArg (·⁻¹) ((hk v).trans (hk v').symm)) ((-a) φ₀)
  have ho : (quadChar K ^ j).OrderDvd 2 := by
    have := sf_quadChar_order K
    unfold HChar.OrderDvd at this ⊢
    rw [← pow_mul, mul_comm, pow_mul, this, one_pow]
  have hpos := sf_isAlgPos_mul ha' (isAlgPos_zero_of_orderDvd two_pos ho)
  rw [add_zero, show -a = fun _ => (-a) φ₀ from funext fun φ => UpperTheory.heckeChar_parallel_weight _ _ _ ha' φ φ₀] at hpos
  obtain ⟨κ, m, hκ, hκχ⟩ := Cq.extReal K _ _ (UpperTheory.heckeChar_algebraic_of_sign _ _ _ hpos hj)
  exact ⟨κ, m, hκ, Cq.csdTwist K n P _ κ hd (by rw [hκχ, hN, map_inv, hχ₁, hN])⟩

end UpperTheory.V.Af

theorem UpperTheory.V.Af.compatReal :
    UpperTheory.V.Af.HypothesesH → UpperTheory.V.Af.CompatReal := by
  intro PH F Ω _ _ _ _ _ _ l _ hl ι n _ hn r π χ hr hreg hpol hatt v σ hσ A h rc hrc
  have P := PH.toClassicalTheorems
  obtain ⟨-, wt, HT, -, -, hG⟩ := exR PH F Ω l ι n hn π χ hreg hpol
  replace hG := hG r hr hatt
  refine ⟨fun hv => hG.away v hv A h rc hrc σ hσ, fun O _ _ _ Bw hj => ?_⟩
  have hL : GlobalTheory.Published.LocalLanglandsGL :=
    GlobalTheory.LocLanglandsBridge.localLanglandsGL_of_depthZero_zelevinsky_bernstein P.litN.loc.llc P.litN.loc.conv P.litN.loc.dzc P.litN.loc.dzi
      P.litN.loc.brauer P.litN.loc.chev P.litN.aut.art P.litN.loc.exh P.litN.loc.multi P.litN.loc.cos P.litN.loc.zel
      P.litN.loc.geo P.litN.loc.bz
  have hpst : IsPstAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype) := by
    obtain ⟨T⟩ := Loc.tiedP l
    exact P.litN.aut.berger.isPstAt T Bw _ (Units.continuous_val.comp (hr.comp continuous_subtype_val))
      (hG.above _ _ ⟨T⟩ v A h O Bw hj).1
  refine ⟨hpst, ?_⟩
  obtain ⟨K, _, _, _, _, _, _, _, hK, hemb, v₀, A₀, ⟨B₀, -, hB₀⟩, hA₀, s, hs, hs'⟩ :=
    UpperTheory.exists_quadratic_of_inertia UpperTheory.quadratic_complex_multiplication UpperTheory.imaginary_generator UpperTheory.cm_inertia_restriction_holds F Ω l hl _ hatt.2
  obtain ⟨Q, hQ⟩ := (Br.quadBCw P F K hK n hn π hreg).resolve_left fun ⟨η, hη, ht⟩ =>
    noTwistRam P F K Ω l ι hK n hn r π hr hatt ⟨s, hs', (hB₀ A₀ hA₀).1 s hs⟩ η hη ht
  have hnorm : (res F Ω K).range.Normal := by
    obtain ⟨δ, -, -, hδ, -⟩ := UpperTheory.exists_quadratic_sign_character F K Ω l hK
    rw [show (res F Ω K).range = δ.ker from Subgroup.ext fun s => (hδ.1 s).symm]
    infer_instance
  obtain ⟨hQr, hQa⟩ := Br.bcAtt0 F K Ω l ι n r π Q hQ.toIsBC0
  replace hQr := hQr hreg
  replace hQa := hQa hatt (UpperTheory.semisimple_restriction_to_normal_subgroup _ _ _ n r _ hnorm hatt.1)
  obtain ⟨χ', hsg, hd⟩ := Br.bcDual0 P.litN.aut.js.1 P.litN.aut.gk F K hK n hn π χ Q hpol hQ.toIsBC0
  obtain ⟨κ, mκ, hκ, hcsd⟩ := csdTw P.litN.aut.gal ι K n hn Q χ' hQr hsg hd
  obtain ⟨artK, hartK, hμ⟩ := (GlobalTheory.Published.GlobalArtinReciprocity.heckeLAdicCharacter_and_principalIdealSt P.litN.aut.art).1 K Ω
  obtain ⟨μ, ⟨hμc, hμ⟩, -⟩ := hμ l ι κ mκ (isAlgPos_of_isAlg hκ)
  have hR : Continuous (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) :=
    hr.comp (continuous_restrictScalarsHom F K Ω)
  have hjK : ∀ x : K, Bw.j (algebraMap K Ω x) ∈ Bw.Kw.1 := hemb Bw.j Bw.Kw Bw.j_E
  obtain ⟨Bw', e1, e2, e3⟩ := Cq.exBridge F K Ω l A O Bw hjK
  have hj' : Induces Bw' := fun x => by rw [e2]; exact hj x
  obtain ⟨w, h', i, hi⟩ := Cq.exPlaceIso F K Ω l A v h O Bw hj hjK
  obtain ⟨⟨σ', hσ'⟩, -⟩ := locCompC P K n Q w
  obtain ⟨rc', hrc', -⟩ := hL.1 K Ω A w h'
  obtain ⟨e, he⟩ := hQ.split hreg ⟨χ, hpol⟩ v w i hi.cont hi.loc σ σ' hσ hσ'
  obtain ⟨c1, c2⟩ := (compatCsd PH K Ω l ι n hn _ _ (Bc.irrBasic.2 _ _ n _ μ hR hμc) (regAlg_twist hQr hκ) hcsd
    (Cq.attTwist K Ω l ι n _ Q hQa artK κ mκ μ hartK hμ) w _ (hσ'.twist κ) A h' rc' hrc').2 O Bw' hj'
  have c3 := Lev.untwistS P.litN.aut.chA P.litN.aut.chW P.litN.aut.berger K Ω l ι n _ hR artK κ mκ μ hartK
    (isAlgPos_of_isAlg hκ) hμc hμ w A h' O Bw' hj' (Cq.pstRes F K Ω l A O Bw Bw' e1 e2 e3 n r hpst) c1 σ' rc' hrc' c2
  refine Lev.recMove hL F K Ω A v w h h' _ i hi n σ σ' e he rc rc' hrc hrc' _ _ ?_ c3
  exact Cq.wdRelRes F K Ω l A O Bw Bw' e1 e2 e3 n r hpst ι v w h h' hj hj' i hi

end
end

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem norm_hom {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : K →ₐ[ℚ_[l]] PadicAlgCl l) (x : K) : ‖σ x‖ = ‖(x : PadicAlgCl l)‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm,
    minpoly.algHom_eq σ σ.injective, ← minpoly.algHom_eq K.val K.val.injective]
  rfl

private theorem embAt_of_induced {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ}
    [Fact l.Prime] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w) {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O)
    (hj : GlobalTheory.Pst.Induces Bw) (τ : F →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1)
    (hτ : GlobalTheory.Pst.IsInduced Bw τ τ') : EmbAt w τ := by
  intro x
  rw [hτ]
  have h1 := norm_hom (LL'.1.val.comp τ') ⟨Bw.j (algebraMap F Ω x), Bw.j_E x⟩
  refine ((hj.valuation_lt_one_iff _).symm.trans (h x)).symm.trans ?_
  exact iff_of_eq (congrArg (· < 1) h1.symm)

theorem UpperTheory.local_global_compatibility_gl2 :
    Af.HypothesesH → ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (ι : Qbar l ≃+* ℂ) (n : ℕ) [Fact (n = 2)], 1 ≤ n → ∀ (r : G F Ω →* GL (Fin n) (Qbar l)) (π : TR.CuspSub F n) (χ : HChar F), Continuous r → π.IsRegAlg → π.Polarized χ → AttR ι r π → ∀ (w : HeightOneSpectrum (𝓞 F)) (m : Fin n → ℤ), (∀ τ : F →+* Qbar l, EmbAt w τ → π.HasInfChar (InfinitePlace.mk (ι.toRingHom.comp τ)) (infOf m)) → ∀ σ, π.IsLocComp w σ → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) rc, IsRec h rc → UpperTheory.V.Lev.AbW (rc (algNorm σ)) → Hi.DRat ι h (r.comp (Dec (F := F) A).subtype) (fun _ => Finset.univ.val.map fun j => -m j) fun s => (rc (algNorm σ)).charPol s := by
  intro PH F Ω _ _ _ _ _ _ l _ hl ι n _ hn r π χ hr hreg hpol hatt w m hm σ hσ A h rc hrc hab O _ _ _ Bw hj
  obtain ⟨-, wt, HT, -, -, hG⟩ := Af.exR PH F Ω l ι n hn π χ hreg hpol
  replace hG := hG r hr hatt
  obtain ⟨h1, h2, -, -⟩ := hG.above _ _ (Loc.tiedP l) w A h O Bw hj
  refine ⟨h1, fun τ LL' τ' hτ => ?_, fun s => ?_⟩
  · have e : HT τ = Finset.univ.val.map fun j => -m j := by
      refine Multiset.map_injective (f := fun n : ℤ => (n : ℂ)) Int.cast_injective ?_
      have := hG.weights τ _ (hm τ (embAt_of_induced h Bw hj τ LL' τ' hτ))
      simp only [this, infOf, Multiset.map_map]
      exact Multiset.map_congr rfl fun i _ => by simp
    exact e ▸ h2 τ LL' τ' hτ
  · exact ((Af.compatReal PH F Ω l hl ι n hn r π χ hr hreg hpol hatt w σ hσ A h rc hrc).2 O Bw hj).2 (Or.inr hab) s
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSubquotientPrincipalSeriesOfBorelFunctional
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section SlopeTestRemainingChoices
open GlobalTheory.SmGL GlobalTheory.PRep Matrix

private theorem sep_of_irred {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (hρ : ρ.IsIrreducible) (L : V →ₗ[ℂ] ℂ) (hL : L ≠ 0) (v : V) (hv : ∀ g, L (ρ g v) = 0) : v = 0 := by
  let S : Subrepresentation ρ :=
    ⟨{ carrier := {v | ∀ g, L (ρ g v) = 0}
       add_mem' := fun {a b} ha hb g => by simp [ha g, hb g]
       zero_mem' := fun g => by simp
       smul_mem' := fun c a ha g => by simp [ha g] }, fun x a ha g => by
      have := ha (g * x)
      simpa using this⟩
  haveI := hρ
  rcases eq_bot_or_eq_top S with h | h
  · have : v ∈ S.toSubmodule := hv
    rw [h] at this
    exact this
  · exfalso
    apply hL
    ext a
    have : a ∈ S.toSubmodule := by rw [h]; trivial
    simpa using this 1

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem diag_eq (a d : kˣ) :
    diagT k (Fin 2) ![a, d] = GeneralLinearGroup.scalar (Fin 2) d * aff (a / d) 0 := by
  ext i j
  rw [val_diagT]
  fin_cases i <;> fin_cases j <;>
    simp [aff, GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_succ, mul_div_cancel₀]

private theorem cont_diag : Continuous (diagT k (Fin 2)) :=
  (continuous_leviEmb k (points (Fin 2))).comp (continuous_leviTorus k (Fin 2))

private theorem finiteRing_sq_sub_mul_sq_eq_of_card (σ : SmIrr (GL (Fin 2) k)) (μ₁ μ₂ : kˣ →* ℂˣ) (L : σ.V →ₗ[ℂ] ℂ) (hL : L ≠ 0)
    (h : ∀ (a d : kˣ) (x : k) v, L (σ.ρ (GeneralLinearGroup.scalar (Fin 2) d * aff (a / d) x) v) =
      ((μ₁ a * μ₂ d : ℂˣ) : ℂ) * L v) :
    IsSmoothChar μ₁ ∧ IsSmoothChar μ₂ ∧ IsSubquotient σ.ρ (Hi.PS ![μ₁ * absPow k (-1), μ₂]) ∧
      ∀ (z : kˣ) v, σ.ρ (GeneralLinearGroup.scalar (Fin 2) z) v = ((μ₁ z * μ₂ z : ℂˣ) : ℂ) • v := by
  obtain ⟨v₀, hv₀⟩ : ∃ v, L v ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hL (LinearMap.ext hc)
  have hst : ∀ a d : kˣ, σ.ρ (diagT k (Fin 2) ![a, d]) v₀ = v₀ → μ₁ a * μ₂ d = 1 := by
    intro a d had
    have := h a d 0 v₀
    rw [← diag_eq, had] at this
    ext
    exact (mul_eq_right₀ hv₀).1 this.symm
  have hopen : IsOpen {g | σ.ρ g v₀ = v₀} := σ.smooth v₀
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hc : Continuous fun a : kˣ => diagT k (Fin 2) ![a, 1] :=
      cont_diag.comp (continuous_pi fun i => by fin_cases i; exacts [continuous_id, continuous_const])
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset ((hopen.preimage hc).mem_nhds ?_) ?_)
    · have : (![1, 1] : Fin 2 → kˣ) = 1 := by funext i; fin_cases i <;> rfl
      simp [this]
    · intro a ha
      simpa using hst a 1 ha
  · have hc : Continuous fun a : kˣ => diagT k (Fin 2) ![1, a] :=
      cont_diag.comp (continuous_pi fun i => by fin_cases i; exacts [continuous_const, continuous_id])
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset ((hopen.preimage hc).mem_nhds ?_) ?_)
    · have : (![1, 1] : Fin 2 → kˣ) = 1 := by funext i; fin_cases i <;> rfl
      simp [this]
    · intro a ha
      simpa using hst 1 a ha
  · let τ : Representation ℂ (Levi k fun _ : Fin 2 => Unit) ℂ :=
      (ofChar (torusChar fun i => ![μ₁ * absPow k (-1), μ₂] i * absPow k ((((2 : ℕ) : ℂ) - 1) / 2))).comp
        (leviTorus k (Fin 2)).symm.toMonoidHom
    have law : ∀ (p : parab k (points (Fin 2))) (u : σ.V), L (σ.ρ p u) =
        (deltaHalf k (fun _ : Fin 2 => Unit) (leviProj k (points (Fin 2)) p) : ℂ) •
          τ (leviProj k (points (Fin 2)) p) (L u) := by
      intro p u
      set t : Fin 2 → kˣ := (leviTorus k (Fin 2)).symm (leviProj k (points (Fin 2)) p) with ht
      have ht1 : ∀ i, GeneralLinearGroup.det (leviProj k (points (Fin 2)) p i) = t i := fun i => rfl
      have ht2 : ∀ i, (t i : k) = ((p : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) i i := by
        intro i
        rw [← ht1]
        simp
      have h10 : ((p : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 :=
        (mem_borel k).1 p.2 1 0 (by decide)
      have hp : (p : GL (Fin 2) k) = GeneralLinearGroup.scalar (Fin 2) (t 1) *
          aff (t 0 / t 1) (((p : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) 0 1 / t 1) := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [aff, GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_succ, mul_div_cancel₀, ← ht2, h10]
      rw [hp, h]
      show _ = _ • ofChar _ t (L u)
      rw [ofChar_apply, deltaHalf_apply, torusChar_apply, Fin.prod_univ_two, Fin.prod_univ_two, ht1, ht1,
        modExp_fin _ (fun _ => by simp), modExp_fin _ (fun _ => by simp), smul_eq_mul, ← mul_assoc, ← Units.val_mul]
      congr 2
      have e1 : absPow k (-1) = (absPow k (1 / 2))⁻¹ * (absPow k (1 / 2))⁻¹ := by
        rw [← absPow_neg, ← absPow_add]; norm_num
      have e2 : ((((2 : ℕ) : ℤ) - 1 - 2 * ((0 : Fin 2) : ℕ) : ℤ) : ℂ) / 2 = 1 / 2 := by norm_num
      have e3 : ((((2 : ℕ) : ℤ) - 1 - 2 * ((1 : Fin 2) : ℕ) : ℤ) : ℂ) / 2 = -(1 / 2) := by norm_num
      have e4 : (((2 : ℕ) : ℂ) - 1) / 2 = 1 / 2 := by norm_num
      rw [e2, e3, e4, absPow_neg, e1]
      simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
      generalize absPow k (1 / 2) (t 0) = x
      generalize absPow k (1 / 2) (t 1) = y
      ext
      simp only [Units.val_mul, Units.val_inv_eq_inv_val]
      field_simp
    let f : σ.V →ₗ[ℂ] IndSp (points (Fin 2)) τ :=
      { toFun := fun v => ⟨⟨fun g => L (σ.ρ g v), fun p g => by
            refine Eq.trans ?_ (law p (σ.ρ g v))
            show L (σ.ρ (p * g) v) = _
            rw [map_mul, Module.End.mul_apply]⟩,
          mem_smoothPart_of_nhds (Filter.mem_of_superset
            (IsOpen.mem_nhds (σ.smooth v) (by simp)) fun g hg => by
              have hg' : σ.ρ g v = v := hg
              apply Subtype.ext
              funext x
              show L (σ.ρ (x * g) v) = L (σ.ρ x v)
              rw [map_mul, Module.End.mul_apply, hg'])⟩
        map_add' := fun c d => by ext g; simp
        map_smul' := fun c d => by ext g; simp }
    refine IsSubquotient.of_injective (ρ := parInd (points (Fin 2)) τ) ⟨f, fun g => ?_⟩ fun c d hcd => ?_
    · refine LinearMap.ext fun c => Subtype.ext (Subtype.ext (funext fun x => ?_))
      show L (σ.ρ x (σ.ρ g c)) = L (σ.ρ (x * g) c)
      rw [map_mul, Module.End.mul_apply]
    · refine sub_eq_zero.1 (sep_of_irred σ.ρ σ.irred L hL _ fun g => ?_)
      have : L (σ.ρ g c) = L (σ.ρ g d) := congrFun (congrArg (fun φ => φ.1.1) hcd) g
      rw [map_sub, map_sub, this, sub_self]
  · intro z v
    refine sub_eq_zero.1 (sep_of_irred σ.ρ σ.irred L hL _ fun g => ?_)
    have hc : g * GeneralLinearGroup.scalar (Fin 2) z =
        GeneralLinearGroup.scalar (Fin 2) z * aff (z / z) 0 * g := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [aff, GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_succ, mul_comm]
    rw [map_sub, map_sub, ← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply, h]
    simp

end SlopeTestRemainingChoices

theorem UpperTheory.isSubquotient_principalSeries_of_borel_functional :
    ∀ (F : Type) [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (σ : SmIrr (GL (Fin 2) (w.adicCompletion F))) (μ₁ μ₂ : (w.adicCompletion F)ˣ →* ℂˣ) (L : σ.V →ₗ[ℂ] ℂ), L ≠ 0 → (∀ (a d : (w.adicCompletion F)ˣ) (x : w.adicCompletion F) v, L (σ.ρ (Matrix.GeneralLinearGroup.scalar (Fin 2) d * aff (a / d) x) v) = ((μ₁ a * μ₂ d : ℂˣ) : ℂ) * L v) → GlobalTheory.SmGL.IsSmoothChar μ₁ ∧ GlobalTheory.SmGL.IsSmoothChar μ₂ ∧ GlobalTheory.SmGL.IsSubquotient σ.ρ (Hi.PS ![μ₁ * GlobalTheory.SmGL.absPow (w.adicCompletion F) (-1), μ₂]) ∧ ∀ (z : (w.adicCompletion F)ˣ) v, σ.ρ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) v = ((μ₁ z * μ₂ z : ℂˣ) : ℂ) • v := by
  intro F _ _ w σ μ₁ μ₂ L hL h
  exact finiteRing_sq_sub_mul_sq_eq_of_card σ μ₁ μ₂ L hL h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CentralCharSqEqOfIsSelfDualBy
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.central_char_sq_eq_of_isSelfDualBy :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (π : TR.CuspSub F 2) (χ : HChar F), π.IsSelfDualBy χ → ∀ (w : HeightOneSpectrum (𝓞 F)) (σ : SmIrr (GL (Fin 2) (w.adicCompletion F))), LocIsotypic π.finPart w σ → ∀ (z : (w.adicCompletion F)ˣ) (c : ℂ), (∀ v, σ.ρ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) v = c • v) → c ^ 2 = ((χ.loc w z : ℂˣ) : ℂ) ^ 2 := by
  intro F _ _ _ π χ hπ w σ hσ z c hc
  obtain ⟨B, d, hl, -, -, hf, -, -⟩ := hπ
  obtain ⟨hnt, htop⟩ := hσ
  set k := locGL F 2 w (Matrix.GeneralLinearGroup.scalar (Fin 2) z) with hk
  have hact : ∀ φ : π.V, π.finPart k φ = c • φ := by
    intro φ
    have hφ : φ ∈ (⊤ : Submodule ℂ π.V) := Submodule.mem_top
    rw [← htop] at hφ
    refine Submodule.iSup_induction _ (motive := fun φ => π.finPart k φ = c • φ) hφ ?_ ?_ ?_
    · rintro f _ ⟨v, rfl⟩
      rw [hk, ← f.2, hc, map_smul]
    · simp
    · intro x y hx hy
      rw [map_add (f := _), hx, hy, smul_add]
  have hop : ∀ φ : π.V, π.op (.fin k) φ = c • φ := fun φ => hact φ
  obtain ⟨φ, hφ⟩ := exists_ne (0 : π.V)
  obtain ⟨ψ, hψ⟩ : ∃ ψ, B φ ψ ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ (hl φ h)
  have h1 := hf k φ ψ
  rw [hop, hop, map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, ← mul_assoc] at h1
  have h2 := mul_right_cancel₀ hψ h1
  have hdet : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) z) = z ^ 2 := by
    ext
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.det_fin_two, sq]
  have h3 : chiDet 2 χ (finGL F 2 k) = χ.loc w (z ^ 2) := by
    rw [← hdet]
    exact TR.CuspSub.chiDet_locGL χ w _
  rw [sq, h2, h3, map_pow, Units.val_pow_eq_pow_val]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HasUEigenvalueOfLocIsotypic
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem dc_common {G : Type} [Group G] (K K' : Subgroup G) (x : G) :
    ∃ s : Finset (MulAction.orbit K (x : G ⧸ K')), ∀ (M : Type) [AddCommGroup M] [Module ℂ M]
      (ρ : Representation ℂ G M) (v : M), Hi.dc ρ K K' x v = ∑ q ∈ s, ρ (q : G ⧸ K').out v := by
  by_cases h : Finite (MulAction.orbit K (x : G ⧸ K'))
  · letI := Fintype.ofFinite (MulAction.orbit K (x : G ⧸ K'))
    refine ⟨Finset.univ, fun M _ _ ρ v => ?_⟩
    rw [Hi.dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply]
  · refine ⟨∅, fun M _ _ ρ v => ?_⟩
    rcases subsingleton_or_nontrivial M with hM | hM
    · exact Subsingleton.elim _ _
    have hs : (Function.support fun q : MulAction.orbit K (x : G ⧸ K') => ρ (q : G ⧸ K').out) = Set.univ := by
      refine Set.eq_univ_of_forall fun q hq => ?_
      have h1 : ρ ((q : G ⧸ K').out⁻¹ * (q : G ⧸ K').out) = 0 := by rw [map_mul, show ρ (q : G ⧸ K').out = 0 from hq, mul_zero]
      rw [inv_mul_cancel, map_one] at h1
      exact one_ne_zero h1
    rw [Hi.dc, finsum_of_infinite_support, Finset.sum_empty, LinearMap.zero_apply]
    rw [hs]
    exact fun hf => h (Set.finite_univ_iff.1 hf)

private theorem killed_of_mem_iSup {G V U ι J : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G U) (hσ : σ.IsIrreducible) (f : ι → U →ₗ[ℂ] V)
    (hf : ∀ i g u, f i (σ g u) = ρ g (f i u)) (T : J → V →ₗ[ℂ] V) (S : J → U →ₗ[ℂ] U)
    (hTS : ∀ j i u, f i (S j u) = T j (f i u))
    (hT : ∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → ∀ j, ∀ x ∈ W, T j x ∈ W)
    (φ : V) (h0 : φ ≠ 0) (hK : ∀ j, T j φ = 0)
    (hφ : φ ∈ ⨆ i, LinearMap.range (f i)) : ∃ v : U, v ≠ 0 ∧ ∀ j, S j v = 0 := by
  classical
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hφ
  have key : ∀ s : Finset ι, ∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → φ ∉ W →
      φ ∈ W ⊔ ⨆ i ∈ s, LinearMap.range (f i) → ∃ v : U, v ≠ 0 ∧ ∀ j, S j v = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro W _ h1 h2; exact absurd (by simpa using h2) h1
    | insert i s _ ih =>
      intro W hW h1 h2
      rw [Finset.iSup_insert, ← sup_assoc] at h2
      by_cases h3 : φ ∈ W ⊔ LinearMap.range (f i)
      · obtain ⟨x, hx, _, ⟨v, rfl⟩, e⟩ := Submodule.mem_sup.1 h3
        have hv : f i v ∉ W := fun h => h1 (e ▸ add_mem hx h)
        have hc : W.comap (f i) = ⊥ := by
          refine (((GlobalTheory.CuspRep.isIrreducible_iff σ).1 hσ).2 _ fun g u hu => ?_).resolve_right fun h => hv ?_
          · rw [Submodule.mem_comap, hf]; exact hW g _ hu
          · have : v ∈ W.comap (f i) := h ▸ Submodule.mem_top
            exact this
        refine ⟨v, fun h => hv (by rw [h, map_zero]; exact zero_mem _), fun j => ?_⟩
        have h4 : S j v ∈ W.comap (f i) := by
          have h5 := hK j
          rw [← e, map_add (f := _)] at h5
          rw [Submodule.mem_comap, hTS, eq_neg_of_add_eq_zero_right h5]
          exact neg_mem (hT W hW j x hx)
        rwa [hc, Submodule.mem_bot] at h4
      · refine ih _ (fun g y hy => ?_) h3 h2
        obtain ⟨x, hx, _, ⟨v, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hy
        rw [map_add (f := _), ← hf]
        exact Submodule.add_mem_sup (hW g x hx) ⟨_, rfl⟩
  exact key s ⊥ (fun g x hx => by simp_all) (by simpa using h0) (by simpa using hs)

private theorem dc_eigen_descend {G V U ι : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G U) (hσ : σ.IsIrreducible) (f : ι → U →ₗ[ℂ] V)
    (hf : ∀ i g u, f i (σ g u) = ρ g (f i u)) (K : Subgroup G) (x : G) (lam : ℂ)
    (φ : V) (h0 : φ ≠ 0) (hK : φ ∈ Hi.fixd ρ K) (hl : Hi.dc ρ K K x φ = lam • φ)
    (hφ : φ ∈ ⨆ i, LinearMap.range (f i)) :
    ∃ v : U, v ≠ 0 ∧ v ∈ Hi.fixd σ K ∧ Hi.dc σ K K x v = lam • v := by
  obtain ⟨s, hs⟩ := dc_common K K x
  obtain ⟨v, hv0, hv⟩ := killed_of_mem_iSup ρ σ hσ f hf
    (fun j : Option K => j.elim (Hi.dc ρ K K x - lam • LinearMap.id) fun k => ρ k - LinearMap.id)
    (fun j : Option K => j.elim (Hi.dc σ K K x - lam • LinearMap.id) fun k => σ k - LinearMap.id)
    (by
      rintro (_ | k) i u
      set_option synthInstance.maxHeartbeats 100000 in
        · simp only [Option.elim, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_smul, hs,
          map_sum, hf]
      · simp only [Option.elim, LinearMap.sub_apply, LinearMap.id_apply, map_sub, hf])
    (by
      rintro W hW (_ | k) y hy
      · simp only [Option.elim, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hs]
        exact sub_mem (Submodule.sum_mem _ fun q _ => hW _ _ hy) (W.smul_mem _ hy)
      · simp only [Option.elim, LinearMap.sub_apply, LinearMap.id_apply]
        exact sub_mem (hW _ _ hy) hy)
    φ h0
    (by
      rintro (_ | k)
      · simp only [Option.elim, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hl, sub_self]
      · simp only [Option.elim, LinearMap.sub_apply, LinearMap.id_apply]
        exact sub_eq_zero.2 (hK k k.2))
    hφ
  exact ⟨v, hv0, fun k hk => sub_eq_zero.1 (hv (some ⟨k, hk⟩)), sub_eq_zero.1 (hv none)⟩

theorem UpperTheory.hasUEigenvalue_of_locIsotypic :
    ∀ (F : Type) [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin 2) (Af F)) V) (σ : SmIrr (GL (Fin 2) (w.adicCompletion F))), LocIsotypic ρ w σ → ∀ (c : ℕ) (lam : ℂ), HasU w (ρ.comp (locGL F 2 w)) c lam → HasU w σ.ρ c lam := by
  intro F _ _ w V _ _ ρ σ ⟨_, htop⟩ c lam ⟨φ, h0, hK, hl⟩
  exact dc_eigen_descend (ρ.comp (locGL F 2 w)) σ.ρ σ.irred
    (fun f : {f : σ.V →ₗ[ℂ] V // ∀ g v, f (σ.ρ g v) = ρ (locGL F 2 w g) (f v)} => f.1) (fun f => f.2)
    (K1 w c) _ lam φ h0 hK hl (htop ▸ Submodule.mem_top)
end

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Sd.OrdinaryAbove

section Loc

variable {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))

private theorem unr_val (μ : (w.adicCompletion F)ˣ →* ℂˣ) (hμ : ∀ x, IsUnitAt w x → μ x = 1) (x : (w.adicCompletion F)ˣ) :
    μ x = μ (atFin w (Formalism.L2.Host.unif w)) ^ GlobalTheory.SmGL.ord (w.adicCompletion F) x := by
  have h1 := ((GlobalTheory.CompletionNorm.norm_nabs_valuation F w).1 x).2.2
  have h2 : Valued.v ((atFin w (Formalism.L2.Host.unif w) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = WithZero.exp (-1 : ℤ) :=
    unif_spec w
  have h3 : IsUnitAt w (x * (atFin w (Formalism.L2.Host.unif w) ^ GlobalTheory.SmGL.ord (w.adicCompletion F) x)⁻¹) := by
    unfold IsUnitAt
    rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul, map_inv₀, map_zpow₀, h1, h2,
      ← WithZero.exp_zsmul, ← WithZero.exp_neg, ← WithZero.exp_add]
    simp
  have h4 := hμ _ h3
  rwa [map_mul, map_inv, map_zpow, mul_inv_eq_one] at h4

private theorem abs_val (x : (w.adicCompletion F)ˣ) :
    ((GlobalTheory.SmGL.absPow (w.adicCompletion F) (-1) x : ℂˣ) : ℂ) = ((normV w : ℕ) : ℂ) ^ GlobalTheory.SmGL.ord (w.adicCompletion F) x := by
  obtain ⟨h1, h2, -⟩ := (GlobalTheory.CompletionNorm.norm_nabs_valuation F w).1 x
  rw [GlobalTheory.SmGL.val_absPow, ← h1, h2, Complex.cpow_neg_one]
  push_cast
  rw [zpow_neg, inv_inv]

end Loc

private theorem norm_fin {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
    (ξ : G F Ω →* (Qbar l)ˣ) (hξ : IsOpen (ξ.ker : Set (G F Ω))) (g : G F Ω) : ‖(ξ g : Qbar l)‖ = 1 := by
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  have : Finite (G F Ω ⧸ ξ.ker) := Subgroup.quotient_finite_of_isOpen _ hξ
  have h0 : ξ.ker.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 : ξ (g ^ ξ.ker.index) = 1 := Subgroup.pow_index_mem ξ.ker g
  have h2 : ‖(ξ g : Qbar l)‖ ^ ξ.ker.index = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, ← map_pow, h1, Units.val_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) h0).1 h2

private theorem dualTw_det {Γ k : Type} [Group Γ] [Field k] (r : Γ →* GL (Fin 2) k) :
    DualTw r (Matrix.GeneralLinearGroup.det.comp r) := by
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by simp), fun s => ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.det_fin_two] <;> ring

private theorem det_flag {Γ k : Type} [Group Γ] [Field k] (r : Γ →* GL (Fin 2) k) (κ : Fin 2 → Γ →* kˣ) (h : W.HasFlag r κ) (s : Γ) :
    Matrix.GeneralLinearGroup.det (r s) = κ 0 s * κ 1 s := by
  obtain ⟨g, hg⟩ := h
  have h1 : Matrix.GeneralLinearGroup.det (g * r s * g⁻¹) = Matrix.GeneralLinearGroup.det (r s) := by
    rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  rw [← h1]
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, (hg s).2 0, (hg s).2 1, (hg s).1 1 0 (by decide)]
  simp

private theorem cont_cyc (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] :
    Continuous (cycBar F Ω l) :=
  _root_.UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.cont_cyc F Ω l

private theorem cent_weil (hP : Af.HypothesesH) {F Ω : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {ξ : G F Ω →* (Qbar l)ˣ} {s c m a π r}
    (H : OrdForm ι ξ s c m a π r) {w : HeightOneSpectrum (𝓞 F)} (hw : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) {A : ValuationSubring Ω}
    (h : IsPlaceOver A w) {ar : Weil h →* (w.adicCompletion F)ˣ} (har : IsLocalArtin h ar)
    {σ : SmIrr (GL (Fin 2) (w.adicCompletion F))} (hσ : LocIsotypic π.finPart w σ) (t : Weil h) (z : ℂ)
    (hz : ∀ v, σ.ρ (Matrix.GeneralLinearGroup.scalar (Fin 2) (ar t)) v = z • v) :
    ‖ι.symm z‖ = ‖((normV w : ℕ) : Qbar l)‖ ^ ((s + 1) * deg t) := by
  have e : Matrix.GeneralLinearGroup.det.comp r * cycBar F Ω l ^ (((2 : ℕ) : ℤ) - 1) = cycBar F Ω l ^ (s + 1) * ξ := by
    rw [H.det, _root_.zpow_add, mul_right_comm]
    norm_num
  have hc : Continuous (cycBar F Ω l ^ (s + 1) * ξ : G F Ω →* (Qbar l)ˣ) := by
    rw [← e]
    exact (Matrix.GeneralLinearGroup.continuous_det.comp H.cont).mul ((cont_cyc F Ω l).zpow _)
  obtain ⟨χ, hχ⟩ := (Af.algOfCyc hP F Ω l ι).1 _ hc fun v hv => by
    have hA := isPlaceOver_placeOf Ω v
    refine ⟨_, hA, s + 1, 1, one_pos, fun g hg => ?_⟩
    have h1 : ξ g = 1 := (H.ram v _ hA).2 (Or.inr hv) hg
    rw [pow_one, MonoidHom.mul_apply, h1, mul_one, MonoidHom.zpow_apply, ← _root_.zpow_add, add_neg_cancel, zpow_zero]
  have hd := (Af.selfDualR hP F Ω l ι 2 one_le_two r π H.att _ χ (dualTw_det r) (e ▸ hχ)).1
  have h1 := UpperTheory.central_char_sq_eq_of_isSelfDualBy F π χ hd w σ hσ _ z hz
  rw [UpperTheory.heckeChar_localArtin_eq_cyclotomic_twist hP.litN F Ω l ι χ ξ (s + 1) H.ξ_open hχ w hw A h ar har t] at h1
  have h2 := congrArg (fun x => ‖ι.symm x‖) h1
  simp only [map_pow, map_mul, map_zpow₀, map_natCast, RingEquiv.symm_apply_apply, norm_pow, norm_mul, norm_zpow,
    norm_fin ξ H.ξ_open, mul_one] at h2
  exact (pow_left_inj₀ (norm_nonneg _) (zpow_nonneg (norm_nonneg _) _) two_ne_zero).1 h2

end UpperTheory.V.Sd.OrdinaryAbove

open UpperTheory.V.Sd.OrdinaryAbove in
theorem UpperTheory.V.Sd.ordAbove :
    UpperTheory.V.Af.HypothesesH → UpperTheory.V.Sd.OrdAbove := by
  intro hP F Ω _ _ _ _ _ _ l _ hl _ ι ξ s c m a π r H w hw A h
  obtain ⟨-, hm, hs, ha, ⟨lam, hU, hlam⟩, hinf⟩ := H.above w hw
  obtain ⟨χ₀, hpol⟩ := H.pol
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := Af.locCompR hP.toClassicalTheorems F 2 π w
  have hiso := hiso σ hσ
  obtain ⟨ar, har⟩ := Loc.laArtin hP.litN.aut.art h
  have L := hP.litN.loc
  obtain ⟨rc, hrc⟩ := L.llc F _ _ w h
  have hrc := GlobalTheory.LocLanglands.isRec_of_isRecLit L.dzc L.dzi L.exh L.multi L.cos L.zel L.geo L.bz F _ _ w h rc hrc
  have hq0 : ((normV w : ℕ) : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 (GlobalTheory.WeilDeligne.one_lt_normV w).ne_bot
  have hqc : ((normV w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (GlobalTheory.WeilDeligne.one_lt_normV w).ne_bot
  have hqn : ‖((normV w : ℕ) : Qbar l)‖ ≠ 0 := norm_ne_zero_iff.2 hq0
  have hn : ‖ι.symm lam * (normV w : Qbar l) ^ m w 0‖ = 1 := by
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := ι.symm lam * (normV w : Qbar l) ^ m w 0 - a w) (y := a w)
      (by rw [ha]; exact hlam.ne)
    rwa [sub_add_cancel, ha, max_eq_right hlam.le] at this
  have hl0 : lam ≠ 0 := by
    rintro rfl
    simp at hn
  have hn' : ‖ι.symm lam‖ = ‖((normV w : ℕ) : Qbar l)‖ ^ (-m w 0) := by
    rw [norm_mul, norm_zpow] at hn
    rw [zpow_neg]
    exact eq_inv_of_mul_eq_one_left hn
  obtain ⟨μ₁, μ₂, Lf, hL0, hunr, hval, hLf⟩ := Sd.jacqOfU hP.toClassicalTheorems F w σ 1 (Units.mk0 lam hl0) one_ne_zero
    (UpperTheory.hasUEigenvalue_of_locIsotypic F w _ π.finPart σ hiso 1 lam hU)
  obtain ⟨s1, s2, hsub, hcen⟩ := UpperTheory.isSubquotient_principalSeries_of_borel_functional F w σ μ₁ μ₂ Lf hL0 hLf
  set ω : Fin 2 → (w.adicCompletion F)ˣ →* ℂˣ := ![μ₁ * GlobalTheory.SmGL.absPow (w.adicCompletion F) (-1), μ₂] with hω
  have hω0 : ∀ t : Weil h, (ω 0 (ar t) : ℂ) = lam ^ (-deg t) := fun t => by
    change ((μ₁ (ar t) * GlobalTheory.SmGL.absPow (w.adicCompletion F) (-1) (ar t) : ℂˣ) : ℂ) = _
    rw [Units.val_mul, abs_val, unr_val w μ₁ hunr, har.ord_eq, Units.val_zpow_eq_zpow_val, ← mul_zpow, mul_comm, hval]
    rfl
  have hsm : ∀ j, GlobalTheory.SmGL.IsSmoothChar (ω j) := by
    refine Fin.forall_fin_two.2 ⟨?_, s2⟩
    exact Subgroup.isOpen_mono (H₁ := μ₁.ker ⊓ (GlobalTheory.SmGL.absPow (w.adicCompletion F) (-1)).ker)
      (fun x hx => by
        change μ₁ x * GlobalTheory.SmGL.absPow (w.adicCompletion F) (-1) x = 1
        rw [hx.1, hx.2, mul_one])
      (IsOpen.inter s1 (GlobalTheory.SmGL.isSmoothChar_of_isUnram (GlobalTheory.SmGL.isUnram_absPow _ _)))
  have hn0 : ∀ t : Weil h, ‖ι.symm (ω 0 (ar t) : ℂ)‖ = ‖((normV w : ℕ) : Qbar l)‖ ^ (m w 0 * deg t) := fun t => by
    rw [hω0, map_zpow₀, norm_zpow, hn', ← zpow_mul, neg_mul_neg]
  have hn1 : ∀ t : Weil h, ‖ι.symm (ω 1 (ar t) : ℂ)‖ = ‖((normV w : ℕ) : Qbar l)‖ ^ (m w 1 * deg t) := fun t => by
    have h1 := cent_weil hP H hw h har hiso t _ (hcen (ar t))
    have h2 : ((μ₁ (ar t) * μ₂ (ar t) : ℂˣ) : ℂ) = (ω 0 (ar t) : ℂ) * (ω 1 (ar t) : ℂ) * ((normV w : ℕ) : ℂ) ^ deg t := by
      change _ = ((μ₁ (ar t) * GlobalTheory.SmGL.absPow (w.adicCompletion F) (-1) (ar t) : ℂˣ) : ℂ) * (μ₂ (ar t) : ℂ) * _
      rw [Units.val_mul, Units.val_mul, abs_val, har.ord_eq, zpow_neg]
      field_simp
    rw [h2, map_mul, map_mul, norm_mul, norm_mul, hn0, map_zpow₀, map_natCast, norm_zpow, ← hs,
      show (m w 0 + m w 1 + 1) * deg t = m w 0 * deg t + m w 1 * deg t + deg t by ring, zpow_add₀ hqn, zpow_add₀ hqn] at h1
    exact mul_left_cancel₀ (zpow_ne_zero _ hqn) (mul_right_cancel₀ (zpow_ne_zero _ hqn) h1)
  have hcp := (Hi.psRec hP.litN F Ω 2 w A h ar har rc hrc σ ω hsm).1 hsub
  have hdr := UpperTheory.local_global_compatibility_gl2 hP F Ω l hl ι 2 one_le_two r π χ₀ H.cont H.reg hpol H.att w (m w) hinf σ hσ A h rc hrc
    ((Lev.ssCalc F Ω A w h).1 2 _ (fun j => (ω j).comp ar) hcp)
  rw [funext hcp] at hdr
  obtain ⟨κ, hκ, hv⟩ := UpperTheory.deRham_weights_of_localArtin_characters hP.litN F Ω l hl ι 2 w hw A h ar har _ (H.cont.comp continuous_subtype_val) (m w)
    (fun i j hij => by fin_cases i <;> fin_cases j <;> first | exact hm | exact absurd hij (by decide)) ω hsm
    (Fin.forall_fin_two.2 ⟨hn0, hn1⟩) hdr
  have k0 : ∀ g : ↥(Dec (F := F) A), (g : G F Ω) ∈ Ine (F := F) A → κ 0 g = cycBar F Ω l g ^ m w 0 := fun g hg => by
    have h1 := hv 0 (ineIncl h ⟨g, hg⟩)
    rw [hω0, deg_ineIncl, mul_zero, zpow_zero, neg_zero, zpow_zero, map_one, mul_one, one_mul] at h1
    exact Units.ext (h1.trans (Units.val_zpow_eq_zpow_val _ _).symm)
  refine ⟨κ, hκ, Fin.forall_fin_two.2 ⟨k0, fun g hg => ?_⟩, fun g hg => ?_⟩
  · have h1 := det_flag _ κ hκ g
    have h2 : Matrix.GeneralLinearGroup.det (r g) = cycBar F Ω l g ^ s * ξ g := DFunLike.congr_fun H.det (g : G F Ω)
    have h3 : ξ g = 1 := (H.ram w A h).2 (Or.inr hw) hg
    rw [h3, mul_one, ← hs, _root_.zpow_add] at h2
    rw [k0 g hg] at h1
    exact mul_left_cancel (h1.symm.trans h2)
  · let t : Weil h := ⟨g, mem_Weil_of_isFrob h hg⟩
    have hd : deg t = 1 := deg_eq_one_iff.2 hg
    have h1 := hv 0 t⁻¹
    rw [hω0, deg_inv, hd, neg_neg, zpow_one, mul_neg_one, zpow_neg] at h1
    have h2 : (κ 0 g⁻¹ : Qbar l) * ((normV w : Qbar l) ^ m w 0)⁻¹ = ι.symm lam * (cycBar F Ω l (g : G F Ω)⁻¹ : Qbar l) ^ m w 0 := h1
    have h3 : ((κ 0 g⁻¹ * cycBar F Ω l (g : G F Ω) ^ m w 0 : (Qbar l)ˣ) : Qbar l) = ι.symm lam * (normV w : Qbar l) ^ m w 0 := by
      rw [mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero _ hq0), map_inv (cycBar F Ω l), Units.val_inv_eq_inv_val (cycBar F Ω l _), inv_zpow] at h2
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val, h2, mul_right_comm _ _ (_ ^ _), inv_mul_cancel_right₀ (zpow_ne_zero _ (Units.ne_zero _))]
    rw [h3]
    exact hlam
