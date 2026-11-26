module

public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegralOfNormLeOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientPow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTameGenAtOfValuationSubring
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.TameGeneratorProjectors
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpecialisationToStrictlyHenselian
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QminorPolyMap

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.StdWeylLatticesFgAndSpanCoeffSpace
open NumberField MvPolynomial Formalism.BasicNotions Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.StdLatSpan

variable (K : Type) [Field K] [NumberField K]

open NumberField MvPolynomial Pointwise in
private lemma nabStd_fg' (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ)
    (lam : ι → _root_.Formalism.BasicNotions.DomWeight n) : (_root_.Formalism.L2.DIV.nabStd K lam).FG := by
  classical
  unfold _root_.Formalism.L2.DIV.nabStd
  choose b hb _ using fun τ : ι => _root_.Formalism.GradedWeylDivisibility.sSBasis (𝓞 K) n n (lam τ).natW
  have hinj : LinearMap.ker (_root_.Formalism.L2.DIV.toK K (Fin n × Fin n)) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (MvPolynomial.map_injective _ (IsFractionRing.injective (𝓞 K) K))
  have hwb : ∀ τ, LinearIndependent (𝓞 K) (b τ) ∧
      Submodule.span (𝓞 K) (Set.range (b τ)) = _root_.Formalism.GradedWeylDivisibility.dualWeyl (𝓞 K) n n (lam τ).natW := by
    intro τ
    have h := hb τ
    unfold _root_.Formalism.GradedWeylDivisibility.IsWeightBasis at h
    exact ⟨h.1, h.2.1⟩
  haveI : ∀ τ, Finite ↑(_root_.Formalism.GradedWeylDivisibility.ssIdx n n (lam τ).natW) := fun τ => (_root_.Formalism.GradedWeylDivisibility.sSIdxFinite n n _).to_subtype
  obtain ⟨-, hspan⟩ := _root_.Formalism.GradedWeylDivisibility.tensorBasis (𝓞 K) K ι n n (fun τ => ↑(_root_.Formalism.GradedWeylDivisibility.ssIdx n n (lam τ).natW))
    (fun τ => Submodule.map (_root_.Formalism.L2.DIV.toK K (Fin n × Fin n)) (_root_.Formalism.BasicNotions.nablaSq (𝓞 K) n (lam τ)))
    (fun τ i => _root_.Formalism.L2.DIV.toK K (Fin n × Fin n) (b τ i))
    (fun τ => (hwb τ).1.map' _ hinj)
    (fun τ => by
      rw [Set.range_comp' (g := _root_.Formalism.L2.DIV.toK K (Fin n × Fin n)) (f := b τ), ← Submodule.map_span, (hwb τ).2]
      rfl)
  rw [← hspan]
  exact Submodule.fg_def.mpr ⟨_, Set.finite_range _, rfl⟩

open NumberField MvPolynomial Pointwise in
private lemma prod_image_blockEmb_eq_setOf_prod {K : Type} [Field K] {S : Type} [Fintype S] {k n : ℕ}
    (X : S → Set (MvPolynomial (Fin k × Fin n) K)) :
    (∏ s ∈ Finset.univ, (_root_.Formalism.GradedWeylDivisibility.blockEmb K s : MvPolynomial (Fin k × Fin n) K → _) '' X s) =
      {P | ∃ F : S → MvPolynomial (Fin k × Fin n) K, (∀ s, F s ∈ X s) ∧
        P = ∏ s, _root_.Formalism.GradedWeylDivisibility.blockEmb K s (F s)} := by
  ext P
  rw [Set.mem_finsetProd]
  constructor
  · rintro ⟨g, hg, rfl⟩
    choose F hF hFe using fun s => hg (Finset.mem_univ s)
    exact ⟨F, hF, Finset.prod_congr rfl fun s _ => (hFe s).symm⟩
  · rintro ⟨F, hF, rfl⟩
    exact ⟨fun s => _root_.Formalism.GradedWeylDivisibility.blockEmb K s (F s), fun {s} _ => ⟨F s, hF s, rfl⟩, rfl⟩

open NumberField MvPolynomial Pointwise in
private lemma span_setOf_prod_blockEmb_eq_prod_map_span {K : Type} [Field K] {S : Type} [Fintype S] {k n : ℕ}
    (X : S → Set (MvPolynomial (Fin k × Fin n) K)) :
    Submodule.span K {P | ∃ F : S → MvPolynomial (Fin k × Fin n) K, (∀ s, F s ∈ X s) ∧
        P = ∏ s, _root_.Formalism.GradedWeylDivisibility.blockEmb K s (F s)} =
      ∏ s, Submodule.map (_root_.Formalism.GradedWeylDivisibility.blockEmb K s).toLinearMap (Submodule.span K (X s)) := by
  rw [← prod_image_blockEmb_eq_setOf_prod, ← Submodule.prod_span]
  simp only [Submodule.map_span, AlgHom.coe_toLinearMap]

open NumberField MvPolynomial Pointwise in
private lemma span_tensorLat_eq_prod_map_span {R K : Type} [CommRing R] [Field K] [Algebra R K] {S : Type} [Fintype S]
    {k n : ℕ} (L : S → Submodule R (MvPolynomial (Fin k × Fin n) K)) :
    Submodule.span K (_root_.Formalism.GradedWeylDivisibility.tensorLat R K L : Set (MvPolynomial (S × Fin k × Fin n) K)) =
      ∏ s, Submodule.map (_root_.Formalism.GradedWeylDivisibility.blockEmb K s).toLinearMap (Submodule.span K (L s : Set _)) := by
  unfold _root_.Formalism.GradedWeylDivisibility.tensorLat
  rw [Submodule.span_span_of_tower]
  exact span_setOf_prod_blockEmb_eq_prod_map_span (K := K) (k := k) (n := n)
    fun s => (L s : Set (MvPolynomial (Fin k × Fin n) K))

open NumberField MvPolynomial Pointwise in
private lemma span_map_toK_nablaSq_eq_nablaSq (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : _root_.Formalism.BasicNotions.DomWeight n) :
    Submodule.span K (Submodule.map (_root_.Formalism.L2.DIV.toK K (Fin n × Fin n)) (_root_.Formalism.BasicNotions.nablaSq (𝓞 K) n μ) : Set _) =
      _root_.Formalism.BasicNotions.nablaSq K n μ := by
  unfold _root_.Formalism.BasicNotions.nablaSq
  obtain ⟨b, hb, -⟩ := _root_.Formalism.GradedWeylDivisibility.sSBasis (𝓞 K) n n μ.natW
  rw [← _root_.Formalism.GradedWeylDivisibility.span_map_weightBasis_eq_dualWeyl (K := K) hb]
  have hspan : Submodule.span (𝓞 K) (Set.range b) = _root_.Formalism.GradedWeylDivisibility.dualWeyl (𝓞 K) n n μ.natW := by
    unfold _root_.Formalism.GradedWeylDivisibility.IsWeightBasis at hb
    exact hb.2.1
  rw [← hspan, Submodule.map_span, Submodule.span_span_of_tower, ← Set.range_comp]
  rfl

open NumberField MvPolynomial Pointwise in
private lemma span_map_toK_delSq_eq_nablaSq (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : _root_.Formalism.BasicNotions.DomWeight n) :
    Submodule.span K (Submodule.map (_root_.Formalism.L2.DIV.toK K (Fin n × Fin n)) (_root_.Formalism.BasicNotions.delSq (𝓞 K) n μ) : Set _) =
      _root_.Formalism.BasicNotions.nablaSq K n μ := by
  rw [_root_.Formalism.L2.Col.nablaSq_eq_delSq]
  unfold _root_.Formalism.BasicNotions.delSq _root_.Formalism.GradedWeylDivisibility.weyl
  rw [Submodule.map_span, Submodule.span_span_of_tower, ← Set.range_comp]
  congr 2
  funext w
  change MvPolynomial.map (algebraMap (𝓞 K) K) _ = _
  rw [← _root_.Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, _root_.Formalism.GradedWeylDivisibility.lclosedeq_hw_map]

open NumberField MvPolynomial Pointwise in
theorem _root_.GlobalTheory.StdLatSpan.std_fg_span : ∀ (K : Type) [Field K] [NumberField K] (ι : Type)
    [Fintype ι] (n : ℕ) (lam : ι → _root_.Formalism.BasicNotions.DomWeight n),
    (_root_.Formalism.L2.DIV.nabStd K lam).FG ∧ (_root_.Formalism.L2.DIV.delStd K lam).FG ∧
      Submodule.span K (_root_.Formalism.L2.DIV.nabStd K lam : Set (_root_.Formalism.L2.DIV.Pol K ι n)) = _root_.Formalism.L2.DIV.VV K lam ∧
      Submodule.span K (_root_.Formalism.L2.DIV.delStd K lam : Set (_root_.Formalism.L2.DIV.Pol K ι n)) = _root_.Formalism.L2.DIV.VV K lam := by
  intro K _ _ ι _ n lam
  have hnab := nabStd_fg' K ι n lam
  refine ⟨hnab, hnab.of_le (_root_.Formalism.L2.DIV.delStd_le_nabStd K lam), ?_, ?_⟩
  · unfold _root_.Formalism.L2.DIV.nabStd _root_.Formalism.L2.DIV.VV
    rw [span_tensorLat_eq_prod_map_span, ← Submodule.span_eq (_root_.Formalism.GradedWeylDivisibility.tensorLat K K _), span_tensorLat_eq_prod_map_span]
    simp only [span_map_toK_nablaSq_eq_nablaSq, Submodule.span_eq]
  · unfold _root_.Formalism.L2.DIV.delStd _root_.Formalism.L2.DIV.VV
    rw [span_tensorLat_eq_prod_map_span, ← Submodule.span_eq (_root_.Formalism.GradedWeylDivisibility.tensorLat K K _), span_tensorLat_eq_prod_map_span]
    simp only [span_map_toK_delSq_eq_nablaSq, Submodule.span_eq]

end GlobalTheory.StdLatSpan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NatCastPowNeZero
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction

namespace GlobalTheory.BlochKatoRank

theorem rank_subquotient_eq {O K X Y : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup X] [Module O X] [AddCommGroup Y] [Module K Y] [Module O Y]
    [IsScalarTower O K Y] (φ : X →ₗ[O] Y) (Z B A : Submodule O X) (Zf BV : Submodule K Y)
    (h1 : ∀ a ∈ A, φ a ∈ Zf) (h2 : ∀ b ∈ B, φ b ∈ BV)
    (h3 : ∀ a, φ a ∈ BV → ∃ m : O, m ≠ 0 ∧ m • a ∈ B)
    (h4 : ∀ y ∈ Zf, ∃ m : O, m ≠ 0 ∧ ∃ a ∈ Z, a ∈ A ∧ φ a = m • y) :
    Module.rank O ((A.comap Z.subtype).map (Submodule.mkQ (B.comap Z.subtype))) =
      Module.rank K (Zf ⧸ BV.comap Zf.subtype) := by
  let A' := A.comap Z.subtype
  let g : A' →ₗ[O] (Z ⧸ B.comap Z.subtype) := (Submodule.mkQ _).comp A'.subtype
  have hg : LinearMap.range g = A'.map (Submodule.mkQ (B.comap Z.subtype)) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  let f0 : A' →ₗ[O] Zf :=
    { toFun := fun a => ⟨φ a.1.1, h1 _ a.2⟩
      map_add' := fun a b => Subtype.ext (by simp)
      map_smul' := fun c a => Subtype.ext (by simp) }
  let f : A' →ₗ[O] (Zf ⧸ BV.comap Zf.subtype) :=
    ((Submodule.mkQ (BV.comap Zf.subtype)).restrictScalars O).comp f0
  have hgk : ∀ a : A', g a = 0 ↔ a.1.1 ∈ B := fun a => Submodule.Quotient.mk_eq_zero _
  have hfk : ∀ a : A', f a = 0 ↔ φ a.1.1 ∈ BV := fun a => Submodule.Quotient.mk_eq_zero _
  have hle : LinearMap.ker g ≤ LinearMap.ker f := fun a ha =>
    (hfk a).2 (h2 _ ((hgk a).1 ha))
  let F := (LinearMap.ker g).liftQ f hle
  haveI : IsLocalizedModule (nonZeroDivisors O) F := by
    refine ⟨fun s => ?_, fun y => ?_, fun {x y} h => ?_⟩
    · have hs : algebraMap O K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
      rw [Module.End.isUnit_iff]
      refine ⟨fun a b h => ?_, fun a => ⟨(algebraMap O K s)⁻¹ • a, ?_⟩⟩
      · simp only [Module.algebraMap_end_apply] at h
        rw [← algebraMap_smul K, ← algebraMap_smul K (s : O) b] at h
        exact smul_right_injective _ hs h
      · rw [Module.algebraMap_end_apply, ← algebraMap_smul K, smul_inv_smul₀ hs]
    · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      obtain ⟨m, hm, a, haZ, haA, ha⟩ := h4 y.1 y.2
      refine ⟨(Submodule.Quotient.mk ⟨⟨a, haZ⟩, haA⟩, ⟨m, mem_nonZeroDivisors_of_ne_zero hm⟩), ?_⟩
      have : f0 ⟨⟨a, haZ⟩, haA⟩ = m • y := Subtype.ext ha
      change m • ((BV.comap Zf.subtype).mkQ.restrictScalars O) y =
        ((BV.comap Zf.subtype).mkQ.restrictScalars O) (f0 ⟨⟨a, haZ⟩, haA⟩)
      rw [this, map_smul]
    · rw [← sub_eq_zero, ← map_sub] at h
      suffices H : ∃ m : O, m ≠ 0 ∧ m • (x - y) = 0 by
        obtain ⟨m, hm, H⟩ := H
        exact ⟨⟨m, mem_nonZeroDivisors_of_ne_zero hm⟩, by
          rw [smul_sub, sub_eq_zero] at H; exact H⟩
      obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (x - y)
      rw [← ha] at h ⊢
      obtain ⟨m, hm, H⟩ := h3 _ ((hfk a).1 h)
      refine ⟨m, hm, ?_⟩
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact (hgk _).2 H
  rw [← hg, ← (LinearMap.quotKerEquivRange g).rank_eq,
    IsLocalization.rank_eq K (nonZeroDivisors O) le_rfl,
    IsLocalizedModule.rank_eq (nonZeroDivisors O) le_rfl F]

section Bridge

open GlobalTheory.BlochKatoIntegralScalars

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O₀ : Type} [CommRing O₀] [Algebra ℤ_[l] O₀] [TopologicalSpace O₀]
  (Bw : LocBridge l E Ω Gw O₀) (P : LocPrime l) {m : ℕ}

include Bw in
theorem natCast_pow_ne_zero (N : ℕ) : (l : O₀) ^ N ≠ 0 := by
  intro h
  have := congrArg Bw.toLL h
  rw [map_pow, map_natCast, map_zero] at this
  exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast (eq_zero_of_pow_eq_zero this))

theorem exists_integral {X : Type} [TopologicalSpace X] [CompactSpace X]
    (c : X → Fin m → ↥Bw.LL.1) (hc : Continuous c) :
    ∃ d : O₀, d ≠ 0 ∧ ∃ f : X → Fin m → O₀, Continuous f ∧
      ∀ g j, Bw.toLL (f g j) = Bw.toLL d * c g j := by
  obtain ⟨N, hN⟩ := exists_pow_mul_mem_OL Bw.LL c hc
  refine ⟨(l : O₀) ^ N, natCast_pow_ne_zero Bw N, fun g j => Bw.eO.symm ⟨_, hN g j⟩, ?_, ?_⟩
  · refine continuous_pi fun j => Bw.eO_symm_cont.comp ?_
    exact Continuous.subtype_mk (continuous_const.mul ((continuous_apply j).comp hc)) _
  · intro g j
    show ((Bw.eO (Bw.eO.symm _) : Loc.OL Bw.LL) : Bw.LL.1) = _
    rw [RingEquiv.apply_symm_apply, map_pow, map_natCast]

end Bridge

end GlobalTheory.BlochKatoRank
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalGaloisRepInvariantsFromFractionRing
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction

namespace GlobalTheory.BKDimNoInv

section Bridge

open Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O)

theorem rep_apply {m : ℕ} (r : ↥Gw →* GL (Fin m) O) (g : ↥(GK Bw.Kw)) (x : Fin m → ↥Bw.LL.1) :
    Bw.rep r g x = (((r (Bw.e.symm g) : GL (Fin m) O) : Matrix (Fin m) (Fin m) O).map Bw.toLL).mulVec x :=
  rfl

theorem toLL_injective : Function.Injective Bw.toLL :=
  Subtype.val_injective.comp Bw.eO.injective

theorem toLL_continuous : Continuous Bw.toLL :=
  continuous_subtype_val.comp Bw.eO_cont

theorem rep_continuous {m : ℕ} (r : ↥Gw →* GL (Fin m) O)
    (hr : Continuous fun g => ((r g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O))
    (x : Fin m → ↥Bw.LL.1) : Continuous fun g => Bw.rep r g x := by
  haveI : IsTopologicalRing ↥Bw.LL.1 := (GlobalTheory.LocalIntegers.good_integers l Bw.LL).1.2.2.2.1
  simp only [rep_apply]
  exact ((hr.comp Bw.e_symm_cont).matrix_map (toLL_continuous Bw)).matrix_mulVec continuous_const

theorem localGaloisRep_invariants_from_fractionRing [IsDomain O] {m : ℕ} (r : ↥Gw →* GL (Fin m) O)
    (h : ∀ x : Fin m → FractionRing O, (∀ g : ↥Gw,
      (((r g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O).map (algebraMap O (FractionRing O))).mulVec x = x) →
        x = 0) : H0V (Bw.rep r) = ⊥ := by
  obtain ⟨_, -, hfr⟩ := (GlobalTheory.LocalIntegers.good_integers l Bw.LL).1.1
  let φ : FractionRing O →+* ↥Bw.LL.1 := IsFractionRing.lift (g := Bw.toLL) (toLL_injective Bw)
  have hφ : ∀ a, φ (algebraMap O _ a) = Bw.toLL a := fun a => IsFractionRing.lift_algebraMap _ a
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨n, d, -, rfl⟩ := IsFractionRing.div_surjective (A := ↥(OL Bw.LL)) y
    refine ⟨algebraMap O _ (Bw.eO.symm n) / algebraMap O _ (Bw.eO.symm d), ?_⟩
    rw [map_div₀, hφ, hφ]
    simp [LocBridge.toLL]
  rw [eq_bot_iff]
  intro x hx
  choose x₀ hx₀ using fun a => hsurj (x a)
  have h0 : x₀ = 0 := by
    refine h x₀ fun g => ?_
    have h1 : Bw.rep r (Bw.e g) x = x := by
      have := (Submodule.mem_iInf _).1 hx (Bw.e g)
      rwa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
    rw [rep_apply, MulEquiv.symm_apply_apply] at h1
    funext a
    apply φ.injective
    rw [hx₀, ← congrFun h1 a]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, hφ, hx₀]
  rw [Submodule.mem_bot]
  funext a
  rw [← hx₀, h0]
  exact map_zero φ

noncomputable def grepOf {m : ℕ} (r : ↥Gw →* GL (Fin m) O)
    (hr : Continuous fun g => ((r g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O)) :
    GRep ↥(GK Bw.Kw) ℚ_[l] ↥Bw.LL.1 ↥(OL Bw.LL) :=
  haveI : IsTopologicalRing ↥Bw.LL.1 := (GlobalTheory.LocalIntegers.good_integers l Bw.LL).1.2.2.2.1
  { V := Fin m → ↥Bw.LL.1
    acg := inferInstance
    modLL := inferInstance
    modQp := inferInstance
    towQp := inferInstance
    modO := inferInstance
    towO := inferInstance
    fd := inferInstance
    top := inferInstance
    mtop := inferInstance
    cadd := inferInstance
    csmul := inferInstance
    ρ := Bw.rep r
    cont := rep_continuous Bw r hr }

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
theorem finrank_h1f_no_invariants [IsDomain O] (P : LocPrime l) {m : ℕ} (r : ↥Gw →* GL (Fin m) O)
    (hr : Continuous fun g => ((r g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O))
    (hBK : Formalism.MainNotions.LocalSituation.bkADim (P.PD Bw.Kw)) (hdR : Bw.IsdRW P r)
    (h : ∀ x : Fin m → FractionRing O, (∀ g : ↥Gw,
      (((r g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O).map (algebraMap O (FractionRing O))).mulVec x = x) →
        x = 0) :
    (Module.finrank ↥Bw.LL.1 (FiniteCohomology (P.PD Bw.Kw) (Bw.rep r)) : ℤ) =
      (Module.finrank ↥Bw.LL.1 ↥(DdR (P.PD Bw.Kw) (Bw.rep r)) : ℤ) -
        Module.finrank ↥Bw.LL.1 ↥(DdR (P.PD Bw.Kw) (Bw.rep r) ⊓
          FilV (P.PD Bw.Kw) (LL := ↥Bw.LL.1) (V := Fin m → ↥Bw.LL.1) 0) := by
  have hG := (GlobalTheory.LocalIntegers.good_integers l Bw.LL).1
  let A := grepOf Bw r hr
  have hA : IsDR (P.PD Bw.Kw) A.ρ := by
    change Module.finrank ↥Bw.LL.1 ↥(DdR (P.PD Bw.Kw) (Bw.rep r)) =
      Module.finrank ℚ_[l] ↥Bw.Kw.1 * Module.finrank ↥Bw.LL.1 (Fin m → ↥Bw.LL.1)
    rw [Module.finrank_fin_fun]
    exact hdR
  have key := hBK _ _ hG A hA
  have h0 : Module.finrank ↥Bw.LL.1 ↥(H0V A.ρ) = 0 := by
    have : H0V A.ρ = ⊥ := localGaloisRep_invariants_from_fractionRing Bw r h
    rw [this, finrank_bot]
  rw [h0, Nat.cast_zero, zero_add] at key
  exact key

end Bridge

end GlobalTheory.BKDimNoInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTameGenAtOfIsPlaceOver
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions

namespace GlobalTheory

theorem exists_tameGenAt_of_isPlaceOver :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
      (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)),
      IsPlaceOver A v → ∃ γ : G E Ω, TameGenAt A γ :=
  fun E Ω _ _ _ _ _ A v h => GlobalTheory.TameInertiaGen.exists_tameGenAt E Ω v A h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TateH2IffAllFiniteExtensions
noncomputable section

namespace GlobalTheory.TateTopCompare

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.TateLocalDualityDegreeTwo

section Transport

variable {O O' G M M' : Type} [CommRing O] [CommRing O'] [Group G] [TopologicalSpace G]
  [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O' M'] [TopologicalSpace M']
  [DiscreteTopology M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul O' M']
  {σ : O →+* O'} {σ' : O' →+* O} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  (π : Representation O G M) (ρ : Representation O' G M') (e : M ≃ₛₗ[σ] M')

variable (he : ∀ g x, e (π g x) = ρ g (e x))
include he

end Transport

section Integers

variable {l : ℕ} [Fact l.Prime] {LL O : Type} [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL]
  [CommRing O] [Algebra O LL]

theorem mem_range_of_norm_le (h : GoodO (Qp := ℚ_[l]) LL O) (L' : FinExt l)
    (φ : LL ≃ₐ[ℚ_[l]] ↥L'.1) (x : LL) (hx : ‖((φ x : ↥L'.1) : Om l)‖ ≤ 1) :
    x ∈ Set.range (algebraMap O LL) := by
  obtain ⟨⟨hO, hdvr, hfr⟩, hfd, hmt, htr, hop⟩ := h
  obtain ⟨-, -, hmt', -, -⟩ := (GlobalTheory.LocalIntegers.good_integers l L').1
  have hcont : Continuous φ.symm :=
    IsModuleTopology.continuous_of_linearMap φ.symm.toLinearEquiv.toLinearMap
  have hU : IsOpen (φ.symm ⁻¹' Set.range (algebraMap O LL)) := hop.preimage hcont
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU 0 ⟨0, by simp⟩
  obtain ⟨c, hc0, hc⟩ := NormedField.exists_norm_lt ℚ_[l] hε
  have hc0' : c ≠ 0 := norm_pos_iff.1 hc0
  have hk : ∀ k : ℕ, ∃ b : O, algebraMap O LL b = algebraMap ℚ_[l] LL c * x ^ k := by
    intro k
    have : φ (algebraMap ℚ_[l] LL c * x ^ k) ∈ Metric.ball (0 : ↥L'.1) ε := by
      rw [mem_ball_zero_iff]
      change ‖((φ (algebraMap ℚ_[l] LL c * x ^ k) : ↥L'.1) : Om l)‖ < ε
      rw [map_mul, map_pow, AlgEquiv.commutes]
      push_cast
      rw [norm_mul, norm_pow]
      have h1 : ‖((algebraMap ℚ_[l] ↥L'.1 c : ↥L'.1) : Om l)‖ = ‖c‖ := PadicAlgCl.norm_extends l c
      calc _ ≤ ‖c‖ * 1 := by
            gcongr
            · exact h1.le
            · exact pow_le_one₀ (norm_nonneg _) hx
        _ < ε := by simpa using hc
    simpa using hball this
  rcases ValuationRing.isInteger_or_isInteger O x with h | ⟨y, hy⟩
  · exact h
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨0, by simp⟩
  by_cases hu : IsUnit y
  · obtain ⟨z, hz⟩ := hu.exists_right_inv
    refine ⟨z, ?_⟩
    have := congrArg (algebraMap O LL) hz
    rw [map_mul, hy, map_one] at this
    field_simp at this
    exact this
  · exfalso
    obtain ⟨a, ha⟩ := hk 0
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hc0' (by simpa using ha.symm)
    obtain ⟨n, hn⟩ := FiniteMultiplicity.of_not_isUnit hu ha0
    obtain ⟨b, hb⟩ := hk (n + 1)
    refine hn ⟨b, IsFractionRing.injective O LL ?_⟩
    rw [map_mul, map_pow, hy, hb, ha, inv_pow]
    field_simp

theorem mem_range_iff (h : GoodO (Qp := ℚ_[l]) LL O) (L' : FinExt l)
    (φ : LL ≃ₐ[ℚ_[l]] ↥L'.1) (x : LL) :
    x ∈ Set.range (algebraMap O LL) ↔ φ x ∈ OL L' := by
  have hO : φ x ∈ OL L' ↔ ‖((φ x : ↥L'.1) : Om l)‖ ≤ 1 := mem_integralClosure_padicInt_iff L'.1 _
  rw [hO]
  refine ⟨?_, mem_range_of_norm_le h L' φ x⟩
  rintro ⟨a, rfl⟩
  by_contra hlt
  rw [not_le] at hlt
  have hsurj : Function.Surjective (algebraMap O LL) := by
    intro w
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ‖((φ w : ↥L'.1) : Om l)‖ hlt
    have hpos : 0 < ‖((φ (algebraMap O LL a) : ↥L'.1) : Om l)‖ ^ k := by positivity
    have ha : algebraMap O LL a ≠ 0 := by
      intro h0
      rw [h0] at hlt
      norm_num at hlt
    obtain ⟨b, hb⟩ := mem_range_of_norm_le h L' φ (w / algebraMap O LL a ^ k) (by
      rw [map_div₀, map_pow]
      push_cast
      rw [norm_div, norm_pow, div_le_one hpos]
      exact hk.le)
    exact ⟨b * a ^ k, by rw [map_mul, map_pow, hb]; field_simp⟩
  obtain ⟨⟨hO, hdvr, hfr⟩, -⟩ := h
  exact IsDiscreteValuationRing.not_isField O
    ((RingEquiv.ofBijective (algebraMap O LL)
      ⟨IsFractionRing.injective O LL, hsurj⟩).toMulEquiv.isField (Field.toIsField LL))

theorem exists_finExt (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [FiniteDimensional ℚ_[l] LL] :
    ∃ L' : FinExt l, Nonempty (LL ≃ₐ[ℚ_[l]] ↥L'.1) := by
  let ψ : LL →ₐ[ℚ_[l]] Om l := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  exact ⟨⟨ψ.fieldRange, (AlgEquiv.ofInjectiveField ψ).toLinearEquiv.finiteDimensional⟩,
    ⟨AlgEquiv.ofInjectiveField ψ⟩⟩

end Integers

section Quotients

variable {G LL O LL' O' M' : Type} [Group G] [TopologicalSpace G] [Field LL] [CommRing O]
  [Algebra O LL] [Field LL'] [CommRing O'] [Algebra O' LL'] [AddCommGroup M'] [Module O' M']
  [TopologicalSpace M'] [DiscreteTopology M'] [IsTopologicalAddGroup M']
  [ContinuousConstSMul O' M']

omit [TopologicalSpace G] in
def rangeLattice (hinj : Function.Injective (algebraMap O LL)) (χ : G →* LLˣ)
    (hχ : ∀ g, ((χ g : LLˣ) : LL) ∈ Set.range (algebraMap O LL)) :
    Lattice (O := O) (charRep χ) where
  T := LinearMap.range (Algebra.linearMap O LL)
  stable := by
    rintro g x ⟨y, rfl⟩
    obtain ⟨a, ha⟩ := hχ g
    exact ⟨a * y, by simp [charRep, ha]⟩
  fg := by
    rw [LinearMap.range_eq_map]
    exact Submodule.FG.map _ Module.Finite.fg_top
  free := Module.Free.of_equiv (LinearEquiv.ofInjective (Algebra.linearMap O LL) hinj)
  span := by
    rw [eq_top_iff]
    intro x _
    have : (1 : LL) ∈ Submodule.span LL ((LinearMap.range (Algebra.linearMap O LL) :
        Submodule O LL) : Set LL) := Submodule.subset_span ⟨1, by simp⟩
    simpa using Submodule.smul_mem _ x this

end Quotients

section Compare

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l)

end Compare

end GlobalTheory.TateTopCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSqCentredHarishChandraParameterSubRhoSq
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSqCentredHarishChandraParameterSubRhoSq
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory

theorem normSq_hcParam_sub_rhoSq (p q n : ℕ) (ap : Fin p → ℕ) (am : Fin q → ℕ) :
    normSq (hcParam n ap am) - rhoSq (p + q) = (∑ a, wtK n ap am a ^ 2 + ∑ i : Fin p, wtK n ap am (Sum.inl i) * ((p : ℚ) - q - 1 - 2 * (i : ℕ)) + ∑ j : Fin q, wtK n ap am (Sum.inr j) * ((p : ℚ) + q - 1 - 2 * (j : ℕ))) := by
  have hr : rhoSq (p + q) = ∑ i : Fin p, (((p : ℚ) - q - 1) / 2 - (i : ℕ)) ^ 2
      + ∑ j : Fin q, (((p : ℚ) + q - 1) / 2 - (j : ℕ)) ^ 2 := by
    unfold rhoSq
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (((p : ℚ) - q - 1) / 2 - (i : ℕ)) ^ 2) p,
      Fin.sum_univ_eq_sum_range (fun i : ℕ => (((p : ℚ) + q - 1) / 2 - (i : ℕ)) ^ 2) q,
      Nat.add_comm p q, Finset.sum_range_add, add_comm]
    congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;> push_cast <;> ring
  rw [hr]
  unfold normSq
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have h1 : ∑ i : Fin p, hcParam n ap am (Sum.inl i) ^ 2
      = ∑ i : Fin p, wtK n ap am (Sum.inl i) ^ 2
        + ∑ i : Fin p, wtK n ap am (Sum.inl i) * ((p : ℚ) - q - 1 - 2 * (i : ℕ))
        + ∑ i : Fin p, (((p : ℚ) - q - 1) / 2 - (i : ℕ)) ^ 2 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hcParam, wtK]
    ring
  have h2 : ∑ j : Fin q, hcParam n ap am (Sum.inr j) ^ 2
      = ∑ j : Fin q, wtK n ap am (Sum.inr j) ^ 2
        + ∑ j : Fin q, wtK n ap am (Sum.inr j) * ((p : ℚ) + q - 1 - 2 * (j : ℕ))
        + ∑ j : Fin q, (((p : ℚ) + q - 1) / 2 - (j : ℕ)) ^ 2 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hcParam, wtK]
    ring
  rw [h1, h2]
  ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSqCentredHarishChandraParameterSubRhoSqStatement
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normSq_centredHarishChandraParameter_sub_rhoSq : ∀ (p q n : ℕ) (ap : Fin p → ℕ) (am : Fin q → ℕ), normSq (hcParam n ap am) - rhoSq (p + q) = (∑ a, wtK n ap am a ^ 2 + ∑ i : Fin p, wtK n ap am (Sum.inl i) * ((p : ℚ) - q - 1 - 2 * (i : ℕ)) + ∑ j : Fin q, wtK n ap am (Sum.inr j) * ((p : ℚ) + q - 1 - 2 * (j : ℕ))) := by
  first | exact @GlobalTheory.normSq_hcParam_sub_rhoSq | exact GlobalTheory.normSq_hcParam_sub_rhoSq | (intros; apply GlobalTheory.normSq_hcParam_sub_rhoSq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CasimirScalarOnModuleGeneratedKilledByLower
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CasimirScalarOnModuleGeneratedKilledByLower
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.CasimirLowest

open GlobalTheory.CasimirHighest

theorem casimir_on_vector {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (h : IsLieAct act) (Λ : Ix p q → ℚ) (e : V)
    (hv : e ∈ hwSub act Λ) (hk : KilledByLower act e) :
    casimir act e = (((∑ a, Λ a ^ 2 + ∑ i : Fin p, Λ (Sum.inl i) * ((p : ℚ) - q - 1 - 2 * (i : ℕ)) +
      ∑ j : Fin q, Λ (Sum.inr j) * ((p : ℚ) + q - 1 - 2 * (j : ℕ))) : ℚ) : ℂ) • e := by
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hv
  obtain ⟨hw, hr⟩ := hv
  have h1 := casimir_on_highest_rat (fun i j : Fin p => act (Eab (.inl i) (.inl j)))
    (fun i j => by simpa using act_Eab_comm h (.inl i) (.inl j) (.inl j) (.inl i)) e
    (fun i => Λ (.inl i)) (fun i j hij => hr _ _ hij) (fun i => hw _)
  have h2 := casimir_on_highest_rat (fun i j : Fin q => act (Eab (.inr i) (.inr j)))
    (fun i j => by simpa using act_Eab_comm h (.inr i) (.inr j) (.inr j) (.inr i)) e
    (fun i => Λ (.inr i)) (fun i j hij => hr _ _ hij) (fun i => hw _)
  have h3 : ∀ (a : Fin p) (b : Fin q),
      act (Eab (.inl a) (.inr b)) (act (Eab (.inr b) (.inl a)) e) = 0 := by
    intro a b; rw [hk a b, map_zero]
  have h4 : ∀ (b : Fin q) (a : Fin p),
      act (Eab (.inr b) (.inl a)) (act (Eab (.inl a) (.inr b)) e) =
        ((Λ (.inr b) - Λ (.inl a) : ℚ) : ℂ) • e := by
    intro b a
    have h5 := congrArg (fun f : Module.End ℂ V => f e)
      (act_Eab_comm h (.inr b) (.inl a) (.inl a) (.inr b))
    simp only [if_true, LinearMap.sub_apply, Module.End.mul_apply, h3, sub_zero, hw] at h5
    rw [h5, Rat.cast_sub, sub_smul]
  have h6 : ∑ b : Fin q, ∑ a : Fin p, ((Λ (.inr b) - Λ (.inl a) : ℚ) : ℂ) • e =
      ((∑ b : Fin q, ∑ a : Fin p, (Λ (.inr b) - Λ (.inl a)) : ℚ) : ℂ) • e := by
    simp only [Rat.cast_sum, Finset.sum_smul]
  simp only [casimir, LinearMap.sum_apply, LinearMap.add_apply, Module.End.mul_apply,
    Fintype.sum_sum_type, Finset.sum_add_distrib, h3, h4, Finset.sum_const_zero, zero_add]
  rw [h1, h2, h6, ← add_smul, ← add_smul, ← Rat.cast_add, ← Rat.cast_add]
  congr 2
  have e1 : ∑ i : Fin p, Λ (Sum.inl i) * ((p : ℚ) - q - 1 - 2 * (i : ℕ)) =
      ∑ i : Fin p, Λ (Sum.inl i) * ((p : ℚ) - 1 - 2 * (i : ℕ)) - q * ∑ i : Fin p, Λ (Sum.inl i) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ j : Fin q, Λ (Sum.inr j) * ((p : ℚ) + q - 1 - 2 * (j : ℕ)) =
      ∑ j : Fin q, Λ (Sum.inr j) * ((q : ℚ) - 1 - 2 * (j : ℕ)) + p * ∑ j : Fin q, Λ (Sum.inr j) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e3 : ∑ b : Fin q, ∑ a : Fin p, (Λ (.inr b) - Λ (.inl a)) =
      p * ∑ j : Fin q, Λ (Sum.inr j) - q * ∑ i : Fin p, Λ (Sum.inl i) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Finset.mul_sum]
  rw [e1, e2, e3]
  ring

theorem casimir_on_generated : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → ∀ (Λ : Ix p q → ℚ) (e : V), e ∈ hwSub act Λ → KilledByLower act e → genSub act {e} = ⊤ → ∀ x, casimir act x = (((∑ a, Λ a ^ 2 + ∑ i : Fin p, Λ (Sum.inl i) * ((p : ℚ) - q - 1 - 2 * (i : ℕ)) + ∑ j : Fin q, Λ (Sum.inr j) * ((p : ℚ) + q - 1 - 2 * (j : ℕ))) : ℚ) : ℂ) • x := by
  intro p q V _ _ act h Λ e hv hk hg x
  have he := casimir_on_vector h Λ e hv hk
  generalize (((∑ a, Λ a ^ 2 + ∑ i : Fin p, Λ (Sum.inl i) * ((p : ℚ) - q - 1 - 2 * (i : ℕ)) +
      ∑ j : Fin q, Λ (Sum.inr j) * ((p : ℚ) + q - 1 - 2 * (j : ℕ))) : ℚ) : ℂ) = c at he ⊢
  have hc := (casimir_central_and_highest p q V act h).1
  have hle : genSub act {e} ≤ LinearMap.ker (casimir act - c • LinearMap.id) := by
    refine sInf_le ⟨?_, ?_⟩
    · rintro y rfl
      simp [he]
    · intro Z y hy
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        sub_eq_zero] at hy ⊢
      have := congrArg (fun f : Module.End ℂ V => f y) (hc Z)
      simp only [Module.End.mul_apply] at this
      rw [this, hy, map_smul]
  have hx := hle (hg ▸ Submodule.mem_top : x ∈ genSub act {e})
  simpa [sub_eq_zero] using hx

end GlobalTheory.CasimirLowest
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CasimirScalarOnModuleGeneratedKilledByLowerStatement
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casimir_scalar_on_module_generated_killedByLower : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → ∀ (Λ : Ix p q → ℚ) (e : V), e ∈ hwSub act Λ → KilledByLower act e → genSub act {e} = ⊤ → ∀ x, casimir act x = (((∑ a, Λ a ^ 2 + ∑ i : Fin p, Λ (Sum.inl i) * ((p : ℚ) - q - 1 - 2 * (i : ℕ)) + ∑ j : Fin q, Λ (Sum.inr j) * ((p : ℚ) + q - 1 - 2 * (j : ℕ))) : ℚ) : ℂ) • x := by
  first | exact @GlobalTheory.CasimirLowest.casimir_on_generated | exact GlobalTheory.CasimirLowest.casimir_on_generated | (intros; apply GlobalTheory.CasimirLowest.casimir_on_generated <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntertwinerMapHighestWeightVectorCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntertwinerMapHighestWeightVectorCompact
open Formalism.BasicNotions.TH

namespace GlobalTheory

theorem mat_compact_eq_sum_units {n : ℕ} (Z : Mat n 0) :
    Z = ∑ a : Fin n, ∑ b : Fin n,
      Z (Sum.inl a) (Sum.inl b) • Eab (Sum.inl a : Ix n 0) (Sum.inl b) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
  simp only [Fintype.sum_sum_type, Finset.univ_eq_empty, Finset.sum_empty, add_zero, Eab,
    Matrix.smul_single, smul_eq_mul, mul_one]

theorem gkMod_compact_glRel {n : ℕ} (M : GKMod n 0) :
    Formalism.REAL.GlRel (fun a b : Fin n => M.act (Eab (Sum.inl a : Ix n 0) (Sum.inl b))) := by
  intro a b c d
  show M.act _ * M.act _ - M.act _ * M.act _ = _
  rw [← M.lie, map_sub]
  congr 1
  · split_ifs with h
    · subst h; simp [Eab]
    · rw [Eab, Eab, Matrix.single_mul_single_of_ne, map_zero]
      intro h'; exact h (Sum.inl_injective h')
  · split_ifs with h
    · subst h; simp [Eab]
    · rw [Eab, Eab, Matrix.single_mul_single_of_ne, map_zero]
      intro h'; exact h (Sum.inl_injective h')

theorem gkMod_compact_irr_units {n : ℕ} (M : GKMod n 0) (h : Formalism.MainNotions.SchurIrreducible.IrrGK M)
    (S : Submodule ℂ M.V)
    (hS : ∀ a b : Fin n, ∀ x ∈ S, M.act (Eab (Sum.inl a : Ix n 0) (Sum.inl b)) x ∈ S) :
    S = ⊥ ∨ S = ⊤ := by
  refine h.2 S fun Z y hy => ?_
  rw [mat_compact_eq_sum_units Z]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  exact S.sum_mem fun a _ => S.sum_mem fun b _ => S.smul_mem _ (hS a b y hy)

theorem gkMod_compact_isHW_units {n : ℕ} (M : GKMod n 0) (Λ : Ix n 0 → ℚ) (v : M.V)
    (h : IsHW M.act Λ v) :
    Formalism.REAL.IsHW (fun a b : Fin n => M.act (Eab (Sum.inl a : Ix n 0) (Sum.inl b)))
      (fun a => ((Λ (Sum.inl a) : ℚ) : ℂ)) v := by
  obtain ⟨-, h1, h2⟩ := h
  simp only [wtSub, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h1 h2
  exact ⟨fun a => h1 _, fun a b hab => h2 (Sum.inl a) (Sum.inl b) hab⟩

theorem exists_intertwiner_map_highestVector :
    ∀ (n : ℕ) (M M' : GKMod n 0) (Λ : Ix n 0 → ℚ) (v : M.V) (v' : M'.V),
      Formalism.MainNotions.SchurIrreducible.IrrGK M → Formalism.MainNotions.SchurIrreducible.IrrGK M' → IsHW M.act Λ v → IsHW M'.act Λ v' →
      ∃ f : M.V →ₗ[ℂ] M'.V, f v = v' ∧ ∀ Z x, f (M.act Z x) = M'.act Z (f x) := by
  intro n M M' Λ v v' hM hM' hv hv'
  have w := gkMod_compact_isHW_units M Λ v hv
  have w' := gkMod_compact_isHW_units M' Λ v' hv'
  obtain ⟨T, hT⟩ := exists_linearEquiv_of_irreducible_isHW M.V M'.V n _ _ _ v v'
    (gkMod_compact_glRel M) (gkMod_compact_glRel M') (gkMod_compact_irr_units M hM)
    (gkMod_compact_irr_units M' hM') w w' hv.1 hv'.1
  obtain ⟨S, hS, hvS, htop⟩ :=
    exists_stable_submodule_topWeight_line M'.V n _ _ v' (gkMod_compact_glRel M') w'
  have hStop : S = ⊤ := by
    rcases gkMod_compact_irr_units M' hM' S hS with h | h
    · rw [h, Submodule.mem_bot] at hvS
      exact absurd hvS hv'.1
    · exact h
  obtain ⟨c, hc⟩ := htop (T v) (by rw [hStop]; trivial) (fun a => by
    rw [← hT a a v, w.1 a, map_smul])
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul, map_eq_zero_iff T T.injective] at hc
    exact hv.1 hc
  refine ⟨c⁻¹ • T.toLinearMap, ?_, fun Z x => ?_⟩
  · simp [hc, smul_smul, hc0]
  · have key : T (M.act Z x) = M'.act Z (T x) := by
      rw [mat_compact_eq_sum_units Z]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [hT a b x]
    simp only [LinearMap.smul_apply, LinearEquiv.coe_coe, key, map_smul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntertwinerMapHighestWeightVectorCompactStatement
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_intertwiner_map_highestWeightVector_compact : ∀ (n : ℕ) (M M' : GKMod n 0) (Λ : Ix n 0 → ℚ) (v : M.V) (v' : M'.V), IrrGK M → IrrGK M' → IsHW M.act Λ v → IsHW M'.act Λ v' → ∃ f : M.V →ₗ[ℂ] M'.V, f v = v' ∧ ∀ Z x, f (M.act Z x) = M'.act Z (f x) := by
  first | exact @GlobalTheory.exists_intertwiner_map_highestVector | exact GlobalTheory.exists_intertwiner_map_highestVector | (intros; apply GlobalTheory.exists_intertwiner_map_highestVector <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FockTensorIntertwinerUniqueAndRange
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FockTensorIntertwinerUniqueAndRange
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.FockUniq

theorem genSub_le {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (S : Set V) (N : Submodule ℂ V)
    (h1 : S ⊆ N) (h2 : ∀ Z, ∀ y ∈ N, act Z y ∈ N) : genSub act S ≤ N :=
  sInf_le ⟨h1, h2⟩

theorem subset_genSub {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (S : Set V) : S ⊆ genSub act S := by
  intro x hx
  simp only [genSub, SetLike.mem_coe, Submodule.mem_sInf]
  exact fun N hN => hN.1 hx

theorem genSub_stable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (S : Set V) (Z : Mat p q) (y : V)
    (hy : y ∈ genSub act S) : act Z y ∈ genSub act S := by
  simp only [genSub, Submodule.mem_sInf] at hy ⊢
  exact fun N hN => hN.2 Z y (hy N hN)

theorem intertwiner_unique_and_range : ∀ (p q n : ℕ) (T0 : GrpData (p * n + q * 0) (p * 0 + q * n)) (T1 : GrpData p q) (T2 : GrpData n 0) (F : FockData T0 T1 T2) (M₁ : GKMod p q) (W : Submodule ℂ M₁.V) (M : GKMod n 0) (I : M₁.V ⊗[ℂ] M.V →ₗ[ℂ] Pol p q n 0) (e₀ : W) (v₀ : M.V), genSub M₁.act (W : Set M₁.V) = ⊤ → KStable M₁.act W → (∀ N : Submodule ℂ M₁.V, N ≤ W → KStable M₁.act N → N = ⊥ ∨ N = W) → IrrGK M → e₀ ≠ 0 → v₀ ≠ 0 → IsGIntw F M₁ M I → (∀ io', IsKIntw F M₁ W M io' → io' (e₀ ⊗ₜ v₀) = I ((e₀ : M₁.V) ⊗ₜ v₀) → io' = I ∘ₗ TensorProduct.map W.subtype LinearMap.id) ∧ (∀ I', IsGIntw F M₁ M I' → (∀ (e : W) (v : M.V), I' ((e : M₁.V) ⊗ₜ v) = I ((e : M₁.V) ⊗ₜ v)) → I' = I) ∧ ∀ v : M.V, Set.range (fun x : M₁.V => I (x ⊗ₜ v)) = (genSub F.act1 (Set.range fun e : W => I ((e : M₁.V) ⊗ₜ v)) : Set (Pol p q n 0)) := by
  intro p q n T0 T1 T2 F M₁ W M I e₀ v₀ hgen hK hirr hM he hv hI
  refine ⟨?_, ?_, ?_⟩
  · intro io hio h0
    have h1 : ∀ v, io (e₀ ⊗ₜ v) = I ((e₀ : M₁.V) ⊗ₜ v) := by
      let N : Submodule ℂ M.V := LinearMap.eqLocus (io ∘ₗ TensorProduct.mk ℂ W M.V e₀)
        (I ∘ₗ TensorProduct.mk ℂ M₁.V M.V e₀)
      have hN : ∀ v, v ∈ N ↔ io (e₀ ⊗ₜ v) = I ((e₀ : M₁.V) ⊗ₜ v) := fun v => Iff.rfl
      rcases hM.2 N (fun Z y hy => by
        rw [hN] at hy ⊢
        rw [← hio.2, ← hI.2, hy]) with h | h
      · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ (hN v₀).2 h0)) hv
      · intro v
        exact (hN v).1 (h ▸ Submodule.mem_top)
    refine TensorProduct.ext' fun e v => ?_
    let N : Submodule ℂ W := LinearMap.eqLocus (io ∘ₗ (TensorProduct.mk ℂ W M.V).flip v)
        (I ∘ₗ (TensorProduct.mk ℂ M₁.V M.V).flip v ∘ₗ W.subtype)
    have hN : ∀ e, e ∈ N ↔ io (e ⊗ₜ v) = I ((e : M₁.V) ⊗ₜ v) := fun v => Iff.rfl
    have hst : KStable M₁.act (N.map W.subtype) := by
      rintro Z hZ _ ⟨w, hw, rfl⟩
      refine ⟨⟨M₁.act Z w, hK Z hZ w w.2⟩, ?_, rfl⟩
      have hw' := (hN w).1 hw
      refine (hN _).2 ?_
      rw [← hio.1 Z hZ w _ v rfl, hw', hI.1]
    have h0' : (e₀ : M₁.V) ∈ N.map W.subtype := ⟨e₀, (hN e₀).2 (h1 v), rfl⟩
    rcases hirr _ (Submodule.map_subtype_le W N) hst with h | h
    · rw [h, Submodule.mem_bot] at h0'
      exact absurd (Subtype.ext h0') he
    · have : (e : M₁.V) ∈ N.map W.subtype := by rw [h]; exact e.2
      obtain ⟨e', he', hee⟩ := this
      have : e' = e := Subtype.ext hee
      subst this
      simpa using (hN e').1 he'
  · intro I' hI' hW
    refine TensorProduct.ext' fun x v => ?_
    let N : Submodule ℂ M₁.V := LinearMap.eqLocus (I' ∘ₗ (TensorProduct.mk ℂ M₁.V M.V).flip v)
        (I ∘ₗ (TensorProduct.mk ℂ M₁.V M.V).flip v)
    have hN : ∀ e, e ∈ N ↔ I' (e ⊗ₜ v) = I (e ⊗ₜ v) := fun v => Iff.rfl
    have := genSub_le M₁.act (W : Set M₁.V) N (fun w hw => (hN w).2 (hW ⟨w, hw⟩ v))
      (fun Z y hy => by
        rw [hN] at hy ⊢
        rw [← hI'.1, ← hI.1, hy])
    rw [hgen] at this
    exact (hN x).1 (this Submodule.mem_top)
  · intro v
    let f : M₁.V →ₗ[ℂ] Pol p q n 0 := I ∘ₗ (TensorProduct.mk ℂ M₁.V M.V).flip v
    have hf : ∀ x, f x = I (x ⊗ₜ v) := fun x => rfl
    apply Set.Subset.antisymm
    · rintro _ ⟨x, rfl⟩
      have := genSub_le M₁.act (W : Set M₁.V)
        ((genSub F.act1 (Set.range fun e : W => I ((e : M₁.V) ⊗ₜ v))).comap f)
        (fun w hw => subset_genSub F.act1 _ ⟨⟨w, hw⟩, rfl⟩)
        (fun Z y hy => by
          rw [Submodule.mem_comap, hf] at hy ⊢
          rw [← hI.1]
          exact genSub_stable _ _ _ _ hy)
      rw [hgen] at this
      exact this (Submodule.mem_top : x ∈ ⊤)
    · have := genSub_le F.act1 (Set.range fun e : W => I ((e : M₁.V) ⊗ₜ v)) (LinearMap.range f)
        (by rintro _ ⟨e, rfl⟩; exact ⟨e, rfl⟩)
        (by rintro Z _ ⟨x, rfl⟩; exact ⟨M₁.act Z x, by rw [hf, hf, hI.1]⟩)
      intro y hy
      obtain ⟨x, hx⟩ := this hy
      exact ⟨x, hx⟩

end GlobalTheory.FockUniq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FockTensorIntertwinerUniqueAndRangeStatement
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_tensor_intertwiner_unique_and_range : ∀ (p q n : ℕ) (T0 : GrpData (p * n + q * 0) (p * 0 + q * n)) (T1 : GrpData p q) (T2 : GrpData n 0) (F : FockData T0 T1 T2) (M₁ : GKMod p q) (W : Submodule ℂ M₁.V) (M : GKMod n 0) (I : M₁.V ⊗[ℂ] M.V →ₗ[ℂ] Pol p q n 0) (e₀ : W) (v₀ : M.V), genSub M₁.act (W : Set M₁.V) = ⊤ → KStable M₁.act W → (∀ N : Submodule ℂ M₁.V, N ≤ W → KStable M₁.act N → N = ⊥ ∨ N = W) → IrrGK M → e₀ ≠ 0 → v₀ ≠ 0 → IsGIntw F M₁ M I → (∀ io', IsKIntw F M₁ W M io' → io' (e₀ ⊗ₜ v₀) = I ((e₀ : M₁.V) ⊗ₜ v₀) → io' = I ∘ₗ TensorProduct.map W.subtype LinearMap.id) ∧ (∀ I', IsGIntw F M₁ M I' → (∀ (e : W) (v : M.V), I' ((e : M₁.V) ⊗ₜ v) = I ((e : M₁.V) ⊗ₜ v)) → I' = I) ∧ ∀ v : M.V, Set.range (fun x : M₁.V => I (x ⊗ₜ v)) = (genSub F.act1 (Set.range fun e : W => I ((e : M₁.V) ⊗ₜ v)) : Set (Pol p q n 0)) := by
  first | exact @GlobalTheory.FockUniq.intertwiner_unique_and_range | exact GlobalTheory.FockUniq.intertwiner_unique_and_range | (intros; apply GlobalTheory.FockUniq.intertwiner_unique_and_range <;> assumption)
end
end
