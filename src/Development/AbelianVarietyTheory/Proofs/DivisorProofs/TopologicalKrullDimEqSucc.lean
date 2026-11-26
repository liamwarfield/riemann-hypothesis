module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open scoped TensorProduct

namespace GlobalTheory.RegGenSmooth

theorem injective_of_charZero {k A : Type} [CommRing k] [IsDomain k] [Module.Finite ℤ k]
    [CommRing A] [CharZero A] (f : k →+* A) : Function.Injective f := by
  rw [RingHom.injective_iff_ker_eq_bot]
  refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
  rw [Ideal.under_def, RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
  exact RingHom.injective_int _

theorem smooth_of_regular (K : Type) [Field K] [PerfectField K] (B : Type) [CommRing B]
    [Algebra K B] [Algebra.FiniteType K B] (d : ℕ)
    (h : ∀ (m : Ideal B) [m.IsMaximal], IsRegularLocalRing (Localization.AtPrime m) ∧
      ringKrullDim (Localization.AtPrime m) = d) :
    SmoothOfRelativeDimension d (spMap (algebraMap K B)) := by
  have : Algebra.FinitePresentation K B := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have key (m : Ideal B) (hm : m.IsMaximal) :
      ∃ f ∉ m, Algebra.IsStandardSmoothOfRelativeDimension d K (Localization.Away f) := by
    obtain ⟨h₁, h₂⟩ := h m
    have h₃ := formallySmooth_of_isRegularLocalRing_of_perfectField K (Localization.AtPrime m)
    have := formallyEtale_residueField_of_isMaximal K K m (Localization.AtPrime m)
    obtain ⟨-, h₄⟩ := free_and_finrank_kaehler_eq_finrank_cotangentSpace K (Localization.AtPrime m)
    have h₅ := (IsRegularLocalRing.iff_finrank_cotangentSpace (Localization.AtPrime m)).1 h₁
    rw [h₂, ← h₄] at h₅
    have : Algebra.IsSmoothAt K m := h₃
    exact exists_isStandardSmoothOfRelativeDimension_of_isSmoothAt K m (by exact_mod_cast h₅)
  refine (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension d)).mpr ?_
  refine ⟨{f | Algebra.IsStandardSmoothOfRelativeDimension d K (Localization.Away f)}, ?_, ?_⟩
  · by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨f, hf, hs⟩ := key m hm
    exact hf (hle (Ideal.subset_span hs))
  · intro f hf
    have := (RingHom.isStandardSmoothOfRelativeDimension_algebraMap d).mpr hf
    rwa [IsScalarTower.algebraMap_eq K B] at this

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}

theorem ringKrullDim_base (h : IsArithVar p D) : ringKrullDim k = 1 := by
  have := h.isDomain
  have := h.finite
  have := h.charZero_base
  rw [ringKrullDim_eq_of_isIntegral ℤ k]
  exact IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField

theorem chart_props (h : IsArithVar p D) {A : Type} [CommRing A] [Algebra k A] (i : Sp A ⟶ X)
    [IsOpenImmersion i] (hi : i ≫ p = spMap (algebraMap k A)) [Nontrivial A] :
    IsDomain A ∧ Algebra.FiniteType k A ∧ FaithfulSMul k A := by
  have := h.isDomain
  have := h.finite
  have := h.isIntegral
  have := h.flat
  have : IsProper p := CommonModel.isProper_of_isProjOver h.isProjOver
  have : IsIntegral (Spec (.of A)) := isIntegral_of_isOpenImmersion i
  have : IsDomain A := (affine_isIntegral_iff (.of A)).1 this
  have hft : LocallyOfFiniteType (spMap (algebraMap k A)) := by rw [← hi]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hft
  have hfl : Flat (i ≫ p ≫ spMap (Int.castRingHom k)) := inferInstance
  have h₁ := (flat_int_iff_charZero _).1 hfl
  have : CharZero A := (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv.toRingHom.charZero_iff
    (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv.injective |>.1 h₁
  exact ⟨‹_›, RingHom.finiteType_algebraMap.mp hft,
    (faithfulSMul_iff_algebraMap_injective _ _).2 (injective_of_charZero _)⟩

theorem topologicalKrullDim_eq_succ (h : IsArithVar p D) {K : Type} [Field K] [Algebra k K]
    [IsFractionRing k K] {Y : Scheme.{0}} {j : Y ⟶ X} {q : Y ⟶ Sp K}
    (H : IsPullback j q p (spMap (algebraMap k K))) {d : ℕ} (hd : topologicalKrullDim Y = d) :
    topologicalKrullDim X = (d + 1 : ℕ) := by
  have := h.isDomain
  have := h.isNoetherianRing
  have : IsProper p := CommonModel.isProper_of_isProjOver h.isProjOver
  have hO1 := ringKrullDim_base h
  have hO : ¬ IsField k := fun e => by
    rw [ringKrullDim_eq_zero_of_isField e] at hO1
    exact absurd hO1 (by decide)
  refine le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_) ?_
  · obtain ⟨A, _, _, i, _, a, rfl, hi⟩ := exists_affine_chart_over p x
    obtain ⟨i₀, _, -⟩ := exists_affine_chart_of_isPullback H i hi
    refine ⟨Set.range i, i.isOpenEmbedding.isOpen_range, ⟨a, rfl⟩, ?_⟩
    rw [topologicalKrullDim_eq_of_isEmbedding i.isOpenEmbedding.isEmbedding rfl]
    have : Nontrivial A := PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨a⟩
    obtain ⟨_, _, _⟩ := chart_props h i hi
    have h₁ : ringKrullDim (K ⊗[k] A) ≤ d :=
      (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).ge.trans
        (i₀.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans hd.le)
    refine (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A).le.trans
      ((IntModel.ringKrullDim_le_add (O := k) K).trans ?_)
    refine (add_le_add hO1.le h₁).trans_eq ?_
    push_cast
    exact add_comm _ _
  · have := IsPreimmersion.of_isLocalization (R := k) (S := K) (nonZeroDivisors k)
    have : IsPreimmersion j := MorphismProperty.of_isPullback H.flip this
    have hj := j.isEmbedding
    have eX : topologicalKrullDim X = Order.krullDim X :=
      Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))
    have eY : topologicalKrullDim Y = Order.krullDim Y :=
      Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Y))
    rw [eY] at hd
    rw [eX]
    obtain ⟨l, hl⟩ := Order.le_krullDim_iff.1 hd.ge
    have hm : StrictMono (j : Y → X) := fun a b h =>
      ⟨hj.isInducing.specializes_iff.2 h.1, fun h' => h.2 (hj.isInducing.specializes_iff.1 h')⟩
    obtain ⟨m, hm0, hmp⟩ := Ring.not_isField_iff_exists_prime.1 hO
    have hp (y : Y) : (p (j y)).asIdeal = ⊥ := by
      rw [← Scheme.Hom.comp_apply, H.w, Scheme.Hom.comp_apply]
      change Ideal.comap (algebraMap k K) (q y).asIdeal = ⊥
      rw [(Ideal.eq_bot_or_top _).resolve_right (q y).2.ne_top]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective k K)
    have hs : p (j l.head) ⤳ (⟨m, hmp⟩ : PrimeSpectrum k) :=
      (PrimeSpectrum.le_iff_specializes _ _).1 ((hp _).le.trans bot_le)
    obtain ⟨x, hx, hxm⟩ := p.isClosedMap.specializingMap hs
    have hlt : x < (l.map _ hm).head := by
      refine ⟨hx, fun h' => hm0 ?_⟩
      have h₁ : p x ⤳ p (j l.head) := Specializes.map h' p.continuous
      rw [hxm] at h₁
      have h₂ : m ≤ (p (j l.head)).asIdeal := (PrimeSpectrum.le_iff_specializes _ _).2 h₁
      exact le_bot_iff.1 (h₂.trans (hp _).le)
    refine Order.le_krullDim_iff.2 ⟨(l.map _ hm).cons x hlt, ?_⟩
    simp [hl]


attribute [local instance] Algebra.TensorProduct.rightAlgebra in
theorem ringKrullDim_chart (h : IsArithVar p D) {K : Type} [Field K] [Algebra k K]
    [IsFractionRing k K] {Y : Scheme.{0}} {j : Y ⟶ X} {q : Y ⟶ Sp K}
    (H : IsPullback j q p (spMap (algebraMap k K))) {A : Type} [CommRing A] [Algebra k A]
    (i : Sp A ⟶ X) [IsOpenImmersion i] (hi : i ≫ p = spMap (algebraMap k A)) [Nontrivial A] :
    IsDomain (K ⊗[k] A) ∧ ringKrullDim (K ⊗[k] A) = D := by
  have := h.isDomain
  have := h.isIntegral
  have : IsProper p := CommonModel.isProper_of_isProjOver h.isProjOver
  obtain ⟨_, _, _⟩ := chart_props h i hi
  have := IsLocalization.tensorRight (S := A) K (nonZeroDivisors k)
  have hle : Algebra.algebraMapSubmonoid A (nonZeroDivisors k) ≤ nonZeroDivisors A :=
    Submonoid.map_le_iff_le_comap.mpr fun x hx ↦ mem_nonZeroDivisors_of_ne_zero
      (by simpa using nonZeroDivisors.ne_zero hx)
  have : IsDomain (K ⊗[k] A) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hle
  have hinj : Function.Injective (algebraMap A (K ⊗[k] A)) := IsLocalization.injective _ hle
  refine ⟨this, ?_⟩
  obtain ⟨i₀, _, H₀⟩ := exists_affine_chart_of_isPullback H i hi
  obtain ⟨d, hd, -⟩ := exists_ringKrullDim_eq_and_trdeg_eq K (K ⊗[k] A)
  have : LocallyOfFiniteType q := MorphismProperty.of_isPullback H inferInstance
  have := IsPreimmersion.of_isLocalization (R := k) (S := K) (nonZeroDivisors k)
  have : IsPreimmersion j := MorphismProperty.of_isPullback H.flip this
  let η : Spec (.of (K ⊗[k] A)) := (⟨⊥, inferInstance⟩ : PrimeSpectrum _)
  have e₁ : topologicalKrullDim (closure {i₀ η} : Set Y) = d :=
    (topologicalKrullDim_closure_eq_ringKrullDim_quotient q i₀ η).trans
      ((ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _)).trans hd)
  have e₂ : j (i₀ η) = genericPoint X := by
    rw [← Scheme.Hom.comp_apply, H₀.w, Scheme.Hom.comp_apply, ← genericPoint_eq_of_isOpenImmersion i]
    congr 1
    rw [genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective _ hinj)
  have e₃ : closure {i₀ η} = Set.univ :=
    Set.eq_univ_of_forall fun y => specializes_iff_mem_closure.1
      (j.isEmbedding.isInducing.specializes_iff.1 (e₂ ▸ genericPoint_specializes _))
  rw [e₃, (Homeomorph.Set.univ Y).isHomeomorph.topologicalKrullDim_eq] at e₁
  have e₄ := (topologicalKrullDim_eq_succ h H e₁).symm.trans h.dim_eq
  rw [hd]
  have e₅ : d + 1 = D + 1 := by exact_mod_cast e₄
  rw [Nat.succ_injective e₅]

theorem smooth_genericFibre (h : IsArithVar p D) (hr : ∀ x, IsRegularLocalRing (X.presheaf.stalk x)) :
    SmoothOfRelativeDimension D (pullback.snd p (spMap (algebraMap k (FractionRing k)))) := by
  have := h.isDomain
  have := h.charZero_base
  have H := IsPullback.of_hasPullback p (spMap (algebraMap k (FractionRing k)))
  refine smoothOfRelativeDimension_genericFibre_of_affine k X p D fun A _ _ i _ hi => ?_
  have : IsProper p := CommonModel.isProper_of_isProjOver h.isProjOver
  have hft : LocallyOfFiniteType (spMap (algebraMap k A)) := by rw [← hi]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hft
  have : Algebra.FiniteType k A := RingHom.finiteType_algebraMap.mp hft
  refine smooth_of_regular _ _ D fun m hm => ⟨?_, ?_⟩
  · obtain ⟨i₀, _, -⟩ := exists_affine_chart_of_isPullback H i hi
    have : Flat (spMap (algebraMap k (FractionRing k))) :=
      flat_specMap_localization (nonZeroDivisors k) _
    have : IsPreimmersion (spMap (algebraMap k (FractionRing k))) :=
      IsPreimmersion.of_isLocalization (nonZeroDivisors k)
    let y : Spec (.of (FractionRing k ⊗[k] A)) := (⟨m, inferInstance⟩ : PrimeSpectrum _)
    have := GenSpread.isIso_stalkMap_of_flat
      (pullback.fst p (spMap (algebraMap k (FractionRing k)))) (i₀ y)
    have := hr (pullback.fst p (spMap (algebraMap k (FractionRing k))) (i₀ y))
    exact IsRegularLocalRing.of_ringEquiv
      (asIso ((pullback.fst p (spMap (algebraMap k (FractionRing k)))).stalkMap (i₀ y)) ≪≫
        asIso (i₀.stalkMap y) ≪≫ Spec.stalkIso (.of _) y).commRingCatIsoToRingEquiv
  · have : Nontrivial (FractionRing k ⊗[k] A) := Ideal.Quotient.nontrivial_iff.2 hm.ne_top |>
      fun _ => (Ideal.Quotient.mk m).domain_nontrivial
    have : Nontrivial A := by
      by_contra hA
      rw [not_nontrivial_iff_subsingleton] at hA
      exact false_of_nontrivial_of_subsingleton (FractionRing k ⊗[k] A)
    obtain ⟨_, hd⟩ := ringKrullDim_chart h H i hi
    have e := height_add_ringKrullDim_quotient_of_finiteType (FractionRing k) m
    rw [hd, ringKrullDim_eq_zero_of_isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient m).1 hm),
      add_zero] at e
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m), e]

theorem exists_opens_smooth (h : IsArithVar p D) (hr : ∀ x, IsRegularLocalRing (X.presheaf.stalk x))
    (σ : k →+* ℂ) (y : CxPts p σ) :
    ∃ U : X.Opens, y ∈ ptsIn p σ U ∧ SmoothOfRelativeDimension D (U.ι ≫ p) := by
  have := h.isDomain
  have := h.finite
  have := h.isNoetherianRing
  have : IsProper p := CommonModel.isProper_of_isProjOver h.isProjOver
  have : LocallyOfFinitePresentation p := inferInstance
  have := smooth_genericFibre h hr
  have H := IsPullback.of_hasPullback p (spMap (algebraMap k (FractionRing k)))
  have : Flat (spMap (algebraMap k (FractionRing k))) :=
    flat_specMap_localization (nonZeroDivisors k) _
  have : IsPreimmersion (spMap (algebraMap k (FractionRing k))) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors k)
  obtain ⟨τ, hτ⟩ : ∃ τ : FractionRing k →+* ℂ, τ.comp (algebraMap k _) = σ :=
    ⟨IsFractionRing.lift (K := FractionRing k) (injective_of_charZero σ), RingHom.ext fun a => by
      rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap]⟩
  have hτ' : spMap τ ≫ spMap (algebraMap k _) = spMap σ := by
    rw [← hτ, ← Spec.map_comp]
    rfl
  obtain ⟨y', hy'⟩ : ∃ y' : Sp ℂ ⟶ pullback p (spMap (algebraMap k (FractionRing k))),
      y' ≫ pullback.fst _ _ = y.1 :=
    ⟨H.lift y.1 (spMap τ) (y.2.trans hτ'.symm), H.lift_fst _ _ _⟩
  obtain ⟨W, hW, hs⟩ := GenSpread.exists_opens_smoothOfRelativeDimension_of_isPullback H D
    (y' (IsLocalRing.closedPoint ℂ))
  refine ⟨W, mem_ptsIn.2 ?_, hs⟩
  change y.1 (IsLocalRing.closedPoint ℂ) ∈ W
  rw [← hy']
  exact hW

theorem genSmooth (h : IsArithVar p D) (hr : ∀ x, IsRegularLocalRing (X.presheaf.stalk x)) :
    GenSmooth p D := fun σ => by
  refine ⟨⟨AlgChart p σ D, id, fun y => ?_⟩⟩
  obtain ⟨W, hW, _⟩ := exists_opens_smooth h hr σ y
  obtain ⟨U, x, hU, hz, hx⟩ := ModelCharts.exists_etale_coords_of_opens p D W (mem_ptsIn.1 hW)
  obtain ⟨c, hc, -⟩ := AlgChart.exists_of_etale hU x hx (mem_ptsIn.2 hz)
  exact ⟨c, hc⟩

end GlobalTheory.RegGenSmooth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCotangentFrameSmoothGroupScheme
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCotangentFrameSmoothGroupScheme
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.VB GlobalTheory.Conormal

namespace GlobalTheory.ConormalFrame

theorem sub_isLocalizedModule {X : Scheme.{0}} {F : X.Modules} [F.IsQuasicoherent] (N : Sub F)
    {U : X.Opens} (hU : IsAffineOpen U)
    (h : ∀ (f : Γ(X, U)) (t : Γ(F, U)),
      GlobalTheory.Twist.resM F (X.basicOpen_le f) t ∈ N.sec _ → ∃ n : ℕ, f ^ n • t ∈ N.sec U)
    (f : Γ(X, U)) : IsLocalizedModule.Away f (GlobalTheory.QCoh.resBasicOpen N.toMod f) := by
  refine (GlobalTheory.QCoh.isLocalizedModule_resBasicOpen_iff _ f).2 ⟨fun s => ?_, fun t ht => ?_⟩
  · obtain ⟨n, t, e⟩ := GlobalTheory.QCoh.exists_pow_smul_eq_res F hU f (X.basicOpen_le f) rfl
      (N.incl.app _ s)
    obtain ⟨m, hm⟩ := h f t (by
      change F.presheaf.map _ t ∈ _
      rw [← e]
      exact (N.sec _).smul_mem _ (N.incl_app_mem s))
    refine ⟨m + n, N.mkSec _ hm, N.incl_app_injective _ ?_⟩
    rw [Scheme.Modules.Hom.app_smul, GlobalTheory.QCoh.app_res, Sub.incl_app_mkSec, Scheme.Modules.map_smul,
      ← e, pow_add, mul_smul, map_pow]
  · obtain ⟨n, e⟩ := GlobalTheory.QCoh.exists_pow_smul_eq_zero F hU f (X.basicOpen_le f) rfl
      (N.incl.app _ t) (by rw [← GlobalTheory.QCoh.app_res, ht, map_zero])
    exact ⟨n, N.incl_app_injective _ (by rw [Scheme.Modules.Hom.app_smul, e, map_zero])⟩

variable {S X : Scheme.{0}} {π : X ⟶ S} {e : S ⟶ X} (he : e ≫ π = 𝟙 S) {U : S.Opens}
  {W : X.Opens}


include he in
theorem preimage_eq (c : IsChart π e U W) : e ⁻¹ᵁ W = U :=
  le_antisymm ((le_preimage_iff he).1 (e.preimage_mono c.le_base)) c.le


include he in
theorem isQuasicoherent_restrict_ideal (c : IsChart π e U W) :
    ((ideal e).restrict c.affine.fromSpec).IsQuasicoherent := by
  have := (isVB_structureModule X).isQuasicoherent
  refine (GlobalTheory.QCoh.isQuasicoherent_restrict_fromSpec_iff _ c.affine).2
    (sub_isLocalizedModule _ c.affine fun f (t : Γ(X, W)) ht => ?_)
  have hcpt : IsCompact ((e ⁻¹ᵁ W : S.Opens) : Set S) := by
    rw [preimage_eq he c]; exact c.affine_base.isCompact
  obtain ⟨n, hn⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact S
    (U := e ⁻¹ᵁ W) hcpt (e.appLE W _ le_rfl t) (e.appLE W _ le_rfl f) (by
      have hle : S.basicOpen (e.appLE W _ le_rfl f) ≤ e ⁻¹ᵁ X.basicOpen f := by
        rw [Scheme.Hom.appLE_eq_app, e.preimage_basicOpen]
      have := congrArg (ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG S hle)
        (show e.appLE _ _ le_rfl (ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG X (X.basicOpen_le f) t) = 0 from ht)
      rw [GlobalTheory.DualPull.resG_appLE, GlobalTheory.DualPull.appLE_resG, map_zero] at this
      exact (GlobalTheory.DualPull.resG_appLE e _ _ _).trans this)
  refine ⟨n, ?_⟩
  change e.appLE W _ le_rfl (f ^ n * t) = 0
  rw [map_mul, map_pow, hn]

end GlobalTheory.ConormalFrame

namespace GlobalTheory.ConormalFrame

variable {S X : Scheme.{0}} {π : X ⟶ S} {e : S ⟶ X} (he : e ≫ π = 𝟙 S) {U : S.Opens}
  {W : X.Opens}


include he in
theorem isQuasicoherent_conormal : (conormal e).IsQuasicoherent := by
  refine GlobalTheory.QCoh.isQuasicoherent_of_forall_exists_affine _ fun x => ?_
  obtain ⟨U, W, hx, -, c⟩ := exists_isChart he (x := x) (V := ⊤) trivial
  have := isQuasicoherent_restrict_ideal he c
  refine ⟨U, c.affine_base, hx,
    (GlobalTheory.QCoh.isQuasicoherent_restrict_fromSpec_iff _ c.affine_base).mp ?_⟩
  exact (SheafOfModules.isQuasicoherent (Spec Γ(S, U)).ringCatSheaf).prop_of_iso
    ((GlobalTheory.QCoh.restrictPullbackIso
      (IsAffineOpen.SpecMap_appLE_fromSpec e c.affine c.affine_base c.le)).app (ideal e))
    (GlobalTheory.QCoh.isQuasicoherent_pullback_Spec (e.appLE W U c.le) ((ideal e).restrict c.affine.fromSpec))

end GlobalTheory.ConormalFrame

namespace GlobalTheory.ConormalFrame

open GlobalTheory.QCoh


set_option backward.isDefEq.respectTransparency false in
theorem isBaseChange_pullbackSections {X Y : Scheme.{0}} (f : X ⟶ Y) (G : Y.Modules)
    {U : X.Opens} {V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    [(G.restrict hV.fromSpec).IsQuasicoherent] (e : U ≤ f ⁻¹ᵁ V) :
    letI := appLEAlgebra f e
    letI := appLEModule f ((Scheme.Modules.pullback f).obj G) e
    haveI := appLE_isScalarTower f ((Scheme.Modules.pullback f).obj G) e
    IsBaseChange Γ(X, U) (pullbackSections f G e) := by
  letI := appLEAlgebra f e
  letI := appLEModule f ((Scheme.Modules.pullback f).obj G) e
  haveI := appLE_isScalarTower f ((Scheme.Modules.pullback f).obj G) e
  obtain ⟨a, ha⟩ := exists_equiv_pullback_Spec (f.appLE V U e) (G.restrict hV.fromSpec)
  have w := IsAffineOpen.SpecMap_appLE_fromSpec f hV hU e
  let κ : Γ((Scheme.Modules.pullback (Spec.map (f.appLE V U e))).obj (G.restrict hV.fromSpec), ⊤)
      ≃ₗ[Γ(X, U)] Γ(((Scheme.Modules.pullback f).obj G).restrict hU.fromSpec, ⊤) :=
    (moduleSpecΓFunctor.mapIso ((restrictPullbackIso w).app G)).toLinearEquiv
  refine IsBaseChange.of_equiv
    ((sectionsEquivFromSpec G hV).baseChange Γ(Y, V) Γ(X, U) _ _ ≪≫ₗ a ≪≫ₗ κ ≪≫ₗ
      (sectionsEquivFromSpec _ hU).symm) fun s ↦ ?_
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_eq, LinearEquiv.baseChange_tmul, ha, sectionsEquivFromSpec_apply,
    sectionsEquivFromSpec_apply, res_pullbackSections]
  refine Eq.trans ?_ (restrictPullbackIso_hom_app_pullbackSections w G (V' := ⊤) (U' := ⊤)
    (fromSpec_image_le hV ⊤) le_rfl _ s)
  exact congr(κ $(res_self _ le_rfl _)).symm

end GlobalTheory.ConormalFrame

namespace GlobalTheory.ConormalFrame

variable {S X : Scheme.{0}} {π : X ⟶ S} {e : S ⟶ X} (he : e ≫ π = 𝟙 S) {U : S.Opens}
  {W : X.Opens}

theorem ofAugCot_bijective (c : IsChart π e U W) : Function.Bijective (c.ofAugCot he) := by
  letI := c.algebra
  letI := GlobalTheory.QCoh.appLEAlgebra e c.le
  letI := GlobalTheory.QCoh.appLEModule e ((Scheme.Modules.pullback e).obj (ideal e)) c.le
  haveI := GlobalTheory.QCoh.appLE_isScalarTower e ((Scheme.Modules.pullback e).obj (ideal e)) c.le
  haveI := AugCot.isScalarTower_of_algebraMap_eq (c.aug he) fun _ => rfl
  haveI := isQuasicoherent_restrict_ideal he c
  have hb := isBaseChange_pullbackSections e (ideal e) c.affine_base c.affine c.le
  let g : Γ(ideal e, W) →ₗ[Γ(X, W)] AugCot (c.aug he) := (RingHom.ker (c.aug he)).toCotangent ∘ₗ
    (GlobalTheory.QCoh.appLinear (idealSub e).incl W).codRestrict (RingHom.ker (c.aug he)) fun s =>
      (c.aug_eq_zero_iff he).2 ((idealSub e).incl_app_mem s)
  have key (x : RingHom.ker (c.aug he)) : c.ofAugCot he ((RingHom.ker (c.aug he)).toCotangent x) =
      cls c.le x ((c.aug_eq_zero_iff he).1 x.2) := d_eq_cls he _ _ _
  refine Function.bijective_iff_has_inverse.2 ⟨hb.lift g, fun x => ?_, fun y => ?_⟩
  · obtain ⟨x, rfl⟩ := (RingHom.ker (c.aug he)).toCotangent_surjective x
    rw [key]
    exact hb.lift_eq g _
  · refine hb.inductionOn y (fun s => ?_) (fun r y hy => ?_) fun y z hy hz => ?_
    · rw [hb.lift_eq]
      exact key _
    · rw [map_smul, map_smul, hy]
      rfl
    · rw [map_add (f := _), map_add (f := _), hy, hz]
      rfl


include he in
theorem exists_isFrame [Smooth π] (x : S) :
    ∃ (U : S.Opens) (n : ℕ) (s : Fin n → Γ(conormal e, U)), x ∈ U ∧ IsFrame s := by
  have := isQuasicoherent_conormal he
  obtain ⟨U, W, hx, -, c⟩ := exists_isChart he (x := x) (V := ⊤) trivial
  letI := c.algebra
  have : Algebra.Smooth Γ(S, U) Γ(X, W) := Smooth.smooth_appLE π c.affine_base c.affine c.le_base
  let E := LinearEquiv.ofBijective (c.ofAugCot he) (ofAugCot_bijective he c)
  have := Module.Finite.equiv E
  have := Module.Projective.of_equiv E
  exact Summand.exists_frame_of_projective c.affine_base ⟨x, hx⟩

end GlobalTheory.ConormalFrame

theorem GlobalTheory.ConormalFrame.exists_isFrame_omega : ∀ (O : Type) [CommRing O] (A : Over (Sp O))
    [GrpObj A] [Smooth A.hom] (x : Sp O), ∃ (U : (Sp O).Opens) (n : ℕ)
    (s : Fin n → Γ(GlobalTheory.LieVB.omega A, U)), x ∈ U ∧ GlobalTheory.VB.IsFrame s :=
  fun _ _ A _ _ x => GlobalTheory.ConormalFrame.exists_isFrame (GlobalTheory.LieVB.sec_hom η[A]) x
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCotangentFrameSmoothGroupSchemeStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cotangent_frame_smooth_groupScheme : ∀ (O : Type) [CommRing O] (A : Over (Sp O)) [GrpObj A] [Smooth A.hom] (x : Sp O), ∃ (U : (Sp O).Opens) (n : ℕ) (s : Fin n → Γ(GlobalTheory.LieVB.omega A, U)), x ∈ U ∧ GlobalTheory.VB.IsFrame s := by
  first | exact @GlobalTheory.ConormalFrame.exists_isFrame_omega | exact GlobalTheory.ConormalFrame.exists_isFrame_omega | (intros; apply GlobalTheory.ConormalFrame.exists_isFrame_omega <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqZeroPointEqOfCotangentFormEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqZeroPointEqOfCotangentFormEq
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent resG)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
open GlobalTheory.LieVB GlobalTheory.Conormal
open GlobalTheory.LB (resG_self)
open GlobalTheory.DualPull (appLE_resG resG_appLE)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroPt

theorem sub_mul_sub_eq_zero_of_closure {B : Type*} [CommRing B] (ψ : B →+* B) (s : Set B)
    (hs : Subring.closure s = ⊤) (H : ∀ x ∈ s, ∀ y ∈ s, (x - ψ x) * (y - ψ y) = 0) (x y : B) :
    (x - ψ x) * (y - ψ y) = 0 := by
  have step (x : B) (hx : ∀ y ∈ s, (x - ψ x) * (y - ψ y) = 0) (y : B) :
      (x - ψ x) * (y - ψ y) = 0 := by
    have hy : y ∈ Subring.closure s := hs ▸ Subring.mem_top y
    induction hy using Subring.closure_induction with
    | mem y hy => exact hx y hy
    | zero => simp
    | one => simp
    | add a b _ _ ha hb =>
      calc (x - ψ x) * (a + b - ψ (a + b)) = (x - ψ x) * (a - ψ a) + (x - ψ x) * (b - ψ b) := by
            rw [map_add (f := _)]; ring
        _ = 0 := by rw [ha, hb, add_zero]
    | neg a _ ha =>
      calc (x - ψ x) * (-a - ψ (-a)) = -((x - ψ x) * (a - ψ a)) := by rw [map_neg]; ring
        _ = 0 := by rw [ha, neg_zero]
    | mul a b _ _ ha hb =>
      calc (x - ψ x) * (a * b - ψ (a * b)) =
            b * ((x - ψ x) * (a - ψ a)) + ψ a * ((x - ψ x) * (b - ψ b)) := by rw [map_mul]; ring
        _ = 0 := by rw [ha, hb]; ring
  have hx : x ∈ Subring.closure s := hs ▸ Subring.mem_top x
  revert y
  induction hx using Subring.closure_induction with
  | mem x hx => exact step x (H x hx)
  | zero => intro y; simp
  | one => intro y; simp
  | add a b _ _ ha hb =>
    intro y
    calc (a + b - ψ (a + b)) * (y - ψ y) = (a - ψ a) * (y - ψ y) + (b - ψ b) * (y - ψ y) := by
          rw [map_add (f := _)]; ring
      _ = 0 := by rw [ha, hb, add_zero]
  | neg a _ ha =>
    intro y
    calc (-a - ψ (-a)) * (y - ψ y) = -((a - ψ a) * (y - ψ y)) := by rw [map_neg]; ring
      _ = 0 := by rw [ha, neg_zero]
  | mul a b _ _ ha hb =>
    intro y
    calc (a * b - ψ (a * b)) * (y - ψ y) =
          b * ((a - ψ a) * (y - ψ y)) + ψ a * ((b - ψ b) * (y - ψ y)) := by rw [map_mul]; ring
      _ = 0 := by rw [ha, hb]; ring

variable (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M]
  [IsCentralScalar O M]

theorem toTsze_injective : Function.Injective (toTsze O M) :=
  (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt O M))).hom).1

theorem surjective_sec_zeroSec : Function.Surjective (sec (zeroSec O M)) := by
  intro t
  have hs : Function.Surjective (TrivSqZeroExt.fstHom O O M).toRingHom :=
    fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have ht : (t : PrimeSpectrum (TrivSqZeroExt O M)) ∈
      Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom O O M).toRingHom) := by
    rw [_root_.range_comap_of_surjective _ _ hs]
    intro a ha
    have ha : a.fst = 0 := ha
    have h : a * a = 0 := by ext <;> simp [ha]
    have := (t : PrimeSpectrum (TrivSqZeroExt O M)).isPrime
    exact (this.mem_or_mem (h ▸ Ideal.zero_mem _)).elim id id
  exact ht

theorem kappa_injective : Function.Injective (kappa O M) := by
  letI := (isChart O M).algebra
  letI := topModule O M
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨y, rfl⟩ := ((isChart O M).augCotEquiv (sec_hom _)).surjective x
  obtain ⟨y, rfl⟩ := (RingHom.ker ((isChart O M).aug (sec_hom _))).toCotangent_surjective y
  have h1 : (toTsze O M y).snd = 0 := by
    change (AugCot.lift _ (sndFn O M) (sndFn_der O M)) (((isChart O M).augCotEquiv
      (sec_hom _)).symm ((isChart O M).augCotEquiv (sec_hom _) _)) = 0 at hx
    rw [LinearEquiv.symm_apply_apply, AugCot.lift_toCotangent] at hx
    exact hx
  have h2 : (toTsze O M y).fst = 0 := by
    rw [← toO_sec]
    have : (isChart O M).aug (sec_hom _) y = 0 := y.2
    rw [IsChart.aug_apply] at this
    rw [this, map_zero]
  have h3 : (y : Γ((TM O M).left, ⊤)) = 0 :=
    toTsze_injective O M (by rw [map_zero]; ext <;> simp [h1, h2])
  have : y = 0 := Subtype.ext h3
  rw [this, map_zero, map_zero]

end GlobalTheory.SqZeroPt

namespace GlobalTheory.SqZeroPt

variable {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M]
  [IsCentralScalar O M]


variable (M) in
abbrev preimTop (U : (Sp O).Opens) : (TM O M).left.Opens :=
  (𝟙 (TM O M).left) ⁻¹ᵁ ⊤ ⊓ (TM O M).hom ⁻¹ᵁ U

theorem mul_eq_zero_of_appLE {U : (Sp O).Opens} (hU : IsAffineOpen U)
    (hle : U ≤ sec (zeroSec O M) ⁻¹ᵁ (preimTop M U))
    (a b : Γ((TM O M).left, preimTop M U))
    (ha : (sec (zeroSec O M)).appLE (preimTop M U) U hle a = 0)
    (hb : (sec (zeroSec O M)).appLE (preimTop M U) U hle b = 0) : a * b = 0 := by
  obtain ⟨-, po⟩ := isAffineOpen_and_isPushout (IsPullback.id_horiz (TM O M).hom)
    (isAffineOpen_top (Sp O)) hU (isChart O M).affine (le_top : U ≤ (𝟙 (Sp O)) ⁻¹ᵁ ⊤) le_top
  have hs := CommRingCat.closure_range_union_range_eq_top_of_isPushout po
  let ψ := ((TM O M).hom.appLE U (preimTop M U) inf_le_right).hom.comp ((sec (zeroSec O M)).appLE (preimTop M U) U hle).hom
  have hψ₁ (r : Γ(Sp O, U)) : ψ ((TM O M).hom.appLE U (preimTop M U) inf_le_right r) =
      (TM O M).hom.appLE U (preimTop M U) inf_le_right r := by
    change (TM O M).hom.appLE U (preimTop M U) inf_le_right ((sec (zeroSec O M)).appLE (preimTop M U) U hle
      ((TM O M).hom.appLE U (preimTop M U) inf_le_right r)) = _
    rw [appLE_base (sec_hom _) hle inf_le_right le_rfl, resG_self]
  have hψ₂ (x : Γ((TM O M).left, ⊤)) : ψ (Scheme.Hom.appLE (𝟙 (TM O M).left) ⊤ (preimTop M U) inf_le_left x) =
      Scheme.Hom.appLE (𝟙 (TM O M).left) ⊤ (preimTop M U) inf_le_left
        ((TM O M).hom.appLE ⊤ ⊤ le_top ((sec (zeroSec O M)).appLE ⊤ ⊤ le_top x)) := by
    change (TM O M).hom.appLE U (preimTop M U) inf_le_right ((sec (zeroSec O M)).appLE (preimTop M U) U hle
      (resG (TM O M).left (le_top : preimTop M U ≤ ⊤) x)) =
      resG (TM O M).left (le_top : preimTop M U ≤ ⊤) _
    rw [appLE_resG, ← resG_appLE (sec (zeroSec O M)) (le_top : U ≤ ⊤) le_top, appLE_resG]
    exact (resG_appLE (TM O M).hom (le_top : preimTop M U ≤ ⊤) le_top _).symm
  have h₀ (x y : Γ((TM O M).left, ⊤)) :
      (x - (TM O M).hom.appLE ⊤ ⊤ le_top ((sec (zeroSec O M)).appLE ⊤ ⊤ le_top x)) *
        (y - (TM O M).hom.appLE ⊤ ⊤ le_top ((sec (zeroSec O M)).appLE ⊤ ⊤ le_top y)) = 0 := by
    apply toTsze_injective O M
    rw [map_mul, map_sub, map_sub, toTsze_base, toTsze_base, toO_sec, toO_sec, map_zero]
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have key := sub_mul_sub_eq_zero_of_closure ψ _ hs (by
    rintro x (⟨x, rfl⟩ | ⟨r, rfl⟩) y (⟨y, rfl⟩ | ⟨s, rfl⟩)
    · rw [hψ₂, hψ₂, ← map_sub, ← map_sub, ← map_mul, h₀, map_zero]
    · rw [hψ₁, sub_self, mul_zero]
    · rw [hψ₁, sub_self, zero_mul]
    · rw [hψ₁, sub_self, zero_mul]) a b
  have ha' : ψ a = 0 := by
    change (TM O M).hom.appLE U (preimTop M U) inf_le_right ((sec (zeroSec O M)).appLE (preimTop M U) U hle a) = 0
    rw [ha, map_zero]
  have hb' : ψ b = 0 := by
    change (TM O M).hom.appLE U (preimTop M U) inf_le_right ((sec (zeroSec O M)).appLE (preimTop M U) U hle b) = 0
    rw [hb, map_zero]
  rwa [ha', hb', sub_zero, sub_zero] at key

variable {A : Over (Sp O)} [GrpObj A]

theorem preimage_le_of_zeroSec (z : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) {U : (Sp O).Opens}
    {W : A.left.Opens} (hU : U ≤ unitSec A ⁻¹ᵁ W) : (TM O M).hom ⁻¹ᵁ U ≤ z.left ⁻¹ᵁ W := by
  intro t ht
  obtain ⟨s, rfl⟩ := surjective_sec_zeroSec O M t
  have h₁ : s ∈ (sec (zeroSec O M) ≫ (TM O M).hom) ⁻¹ᵁ U := ht
  rw [sec_hom] at h₁
  have h₂ := hU h₁
  rw [← show sec (zeroSec O M) ≫ z.left = unitSec A from congrArg (·.left) h] at h₂
  exact h₂

end GlobalTheory.SqZeroPt

namespace GlobalTheory.SqZeroPt

theorem eq_of_Phi_eq : ∀ (O : Type) [CommRing O] (A : Over (Sp O)) [GrpObj A],
    (GlobalTheory.LieVB.omega A).IsQuasicoherent → (∀ (M : Type) [AddCommGroup M] [Module O M]
      [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (z z' : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A])
      (h' : zeroSec O M ≫ z' = η[A]), (∀ w, Phi z h w = Phi z' h' w) → z = z') := by
  intro O _ A _ hq M _ _ _ _ z z' h h' hΦ
  have hq' : (conormal (sec η[A])).IsQuasicoherent := hq
  have hglob (w : Γ(conormal (sec η[A]), ⊤)) : (cotMap z h).app ⊤ w = (cotMap z' h').app ⊤ w :=
    kappa_injective O M ((Phi_apply z h w).symm.trans ((hΦ w).trans (Phi_apply z' h' w)))
  have : IsIso ((tilde.adjunction (R := .of O)).counit.app (conormal (sec η[A]))) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := .of O) (conormal (sec η[A]))
  have hcot : cotMap z h = cotMap z' h' := by
    apply (GlobalTheory.OmegaGlobal.map_bijective_of_isIso_counit (tilde.adjunction (R := .of O)) _ _).1
    ext s
    exact hglob s
  have hz : sec (zeroSec O M) ≫ z.left = unitSec A := congrArg (·.left) h
  have hz' : sec (zeroSec O M) ≫ z'.left = unitSec A := congrArg (·.left) h'
  refine Over.OverMorphism.ext (Scheme.hom_ext_of_forall _ _ fun t => ?_)
  obtain ⟨U, W, hU, -, c⟩ := exists_isChart (sec_hom η[A]) (V := ⊤) (x := (TM O M).hom t) trivial
  have hT : IsAffineOpen (preimTop M U) := (isAffineOpen_and_isPushout
    (IsPullback.id_horiz (TM O M).hom) (isAffineOpen_top (Sp O)) c.affine_base (isChart O M).affine
    (le_top : U ≤ (𝟙 (Sp O)) ⁻¹ᵁ ⊤) le_top).1
  have kz : preimTop M U ≤ z.left ⁻¹ᵁ W := inf_le_right.trans (preimage_le_of_zeroSec z h c.le)
  have kz' : preimTop M U ≤ z'.left ⁻¹ᵁ W := inf_le_right.trans (preimage_le_of_zeroSec z' h' c.le)
  have c₀ : IsChart (TM O M).hom (sec (zeroSec O M)) U (preimTop M U) :=
    ⟨c.affine_base, hT, fun x hx => ⟨trivial,
      (le_preimage_iff (π := (TM O M).hom) (sec_hom (zeroSec O M))).2 le_rfl hx⟩, inf_le_right⟩
  have e : z.left.appLE W (preimTop M U) kz = z'.left.appLE W (preimTop M U) kz' := by
    ext f
    rw [← sub_eq_zero]
    have ha : (sec (zeroSec O M)).appLE (preimTop M U) U c₀.le
        (z.left.appLE W (preimTop M U) kz f - z'.left.appLE W (preimTop M U) kz' f) = 0 := by
      rw [map_sub, appLE_appLE hz kz c₀.le c.le, appLE_appLE hz' kz' c₀.le c.le, sub_self]
    have hd : d (sec_hom (zeroSec O M)) c₀.le
        (z.left.appLE W (preimTop M U) kz f - z'.left.appLE W (preimTop M U) kz' f) = 0 := by
      rw [map_sub, ← cotMap_d z h c.le c₀.le kz f, ← cotMap_d z' h' c.le c₀.le kz' f, hcot,
        sub_self]
    letI := c₀.algebra
    have h₁ : AugCot.d (c₀.aug (sec_hom _))
        (z.left.appLE W (preimTop M U) kz f - z'.left.appLE W (preimTop M U) kz' f) = 0 :=
      (c₀.ofAugCot_bijective (sec_hom _)).1 (by rw [c₀.ofAugCot_d, map_zero]; exact hd)
    have h₂ := (AugCot.d_eq_zero_iff _ _).1 h₁
    rw [show c₀.aug (sec_hom _) _ = 0 from ha, map_zero, sub_zero] at h₂
    have hsq : RingHom.ker (c₀.aug (sec_hom (zeroSec O M))) ^ 2 = ⊥ := by
      rw [pow_two, eq_bot_iff, Ideal.mul_le]
      intro a ha' b hb'
      exact (Ideal.mem_bot).2 (mul_eq_zero_of_appLE c.affine_base c₀.le a b ha' hb')
    rw [hsq] at h₂
    exact (Ideal.mem_bot).1 h₂
  refine ⟨preimTop M U, ⟨trivial, hU⟩, ?_⟩
  rw [← cancel_epi hT.isoSpec.inv, ← Category.assoc, ← Category.assoc, hT.isoSpec_inv_ι,
    ← c.affine.SpecMap_appLE_fromSpec _ hT kz, ← c.affine.SpecMap_appLE_fromSpec _ hT kz', e]

end GlobalTheory.SqZeroPt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqZeroPointEqOfCotangentFormEqStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sqZeroPoint_eq_of_cotangentForm_eq : ∀ (O : Type) [CommRing O] (A : Over (Sp O)) [GrpObj A], (GlobalTheory.LieVB.omega A).IsQuasicoherent → (∀ (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (z z' : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (h' : zeroSec O M ≫ z' = η[A]), (∀ w, Phi z h w = Phi z' h' w) → z = z') := by
  first | exact @GlobalTheory.SqZeroPt.eq_of_Phi_eq | exact GlobalTheory.SqZeroPt.eq_of_Phi_eq | (intros; apply GlobalTheory.SqZeroPt.eq_of_Phi_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeSpectrumDualNumberEq
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.TopForm GlobalTheory.Adelic GlobalTheory.TangentOrigin
open GlobalTheory.FlagTan (IsDef)

theorem exists_isFreeGen_dForm {k A : Type} [CommRing k] [CommRing A] {α : k →+* A} {D : ℕ}
    (h : α.IsStandardSmoothOfRelativeDimension D) : ∃ f : Fin D → A, IsFreeGen A (dForm α f) := by
  classical
  letI := α.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension D k A := h
  obtain ⟨ι, σ, _, _, P, hP⟩ := ‹Algebra.IsStandardSmoothOfRelativeDimension D k A›.out
  letI := Fintype.ofFinite ι
  letI := Fintype.ofFinite σ
  have hc : Fintype.card ((Set.range P.map)ᶜ : Set ι) = D := by
    rw [Fintype.card_compl_set, Set.card_range_of_injective P.map_inj, ← hP]
    simp [Algebra.Presentation.dimension]
  let e := Fintype.equivFinOfCardEq hc
  exact ⟨fun i => P.val (e.symm i), isFreeGen_dForm _ (P.basisKaehler.reindex e) fun i => by
    simp⟩

theorem exists_isFrame_dOn {k : Type} [CommRing k] {Y : Scheme.{0}} (p : Y ⟶ Sp k) (D : ℕ)
    [SmoothOfRelativeDimension D p] (x : Y) :
    ∃ (U : Y.Opens) (f : Fin D → Γ(Y, U)), x ∈ U ∧ IsFrame (dOn p f) := by
  obtain ⟨V, hV, hx, -⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens (Opens.mem_top x)
  have h := HasRingHomProperty.appLE (@SmoothOfRelativeDimension D) p ‹_›
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
  obtain ⟨s, hs, h⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h
  obtain ⟨t, hxt⟩ : ∃ t : (s : Set Γ(Y, V)), x ∈ Y.basicOpen (t : Γ(Y, V)) :=
    Opens.mem_iSup.1 (((IsAffineOpen.iSup_basicOpen_eq_self_iff hV).2 hs).ge hx)
  have := IsAffineOpen.isLocalization_basicOpen hV (t : Γ(Y, V))
  have h₁ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
    (h t t.2 Γ(Y, Y.basicOpen (t : Γ(Y, V))))
  have h₂ : (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (Y.basicOpen (t : Γ(Y, V)))).IsStandardSmoothOfRelativeDimension D := by
    rw [← resG_comp_algX p (Y.basicOpen_le (t : Γ(Y, V)))]
    exact h₁
  obtain ⟨f, hf⟩ := exists_isFreeGen_dForm h₂
  exact ⟨_, f, hxt, IsAffineOpen.basicOpen hV _, hf⟩

theorem primeSpectrum_dualNumber_eq {L : Type} [Field L] (x y : PrimeSpectrum (DualNumber L)) : x = y := by
  have h : ∀ z : PrimeSpectrum (DualNumber L), ∀ a, a ∈ z.asIdeal ↔ a.fst = 0 := fun z a => by
    constructor
    · intro ha
      by_contra h0
      exact z.2.ne_top (z.asIdeal.eq_top_of_isUnit_mem ha (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit h0)))
    · intro ha
      refine z.2.mem_of_pow_mem 2 ?_
      rw [show a ^ 2 = 0 by ext <;> simp [pow_two, ha]]
      exact z.asIdeal.zero_mem
  ext a
  rw [h, h]

theorem le_preimage_of_dualNumber {L : Type} [Field L] {T : Scheme.{0}} (φ : DualNumber L →+* L)
    (x : Sp (DualNumber L) ⟶ T) (V : T.Opens) (h : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ V) : ⊤ ≤ x ⁻¹ᵁ V := by
  intro s _
  have hp : (spMap φ) (IsLocalRing.closedPoint L) = s := primeSpectrum_dualNumber_eq _ _
  have h₁ : (spMap φ ≫ x) (IsLocalRing.closedPoint L) ∈ V := h (Set.mem_univ _)
  exact hp ▸ h₁

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c}
  (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw))

theorem exists_tanLift {L : Type} [Field L] [Algebra c.F L] {Q : FrPt Xo c L} {v : FrPt Xo c (DualNumber L)}
    (hd : IsDef Q v) {z : Sp L ⟶ M.X} (hz : z ≫ toFlag M = X.ptY Q) (ho : ⊤ ≤ z ⁻¹ᵁ M.off) :
    ∃ zv : Sp (DualNumber L) ⟶ M.X, zv ≫ toFlag M = X.ptY v ∧ ∀ O : M.X.Opens, ⊤ ≤ z ⁻¹ᵁ O → ⊤ ≤ zv ⁻¹ᵁ O := by
  have e := (X.ptY_frMap hd).trans hz.symm
  have hU : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ U₀ X Z := fun s _ => by
    have := ho (Set.mem_univ s)
    rw [M.off_eq] at this
    exact this
  have hb : ⊤ ≤ X.ptY v ⁻¹ᵁ (inc₀ X Z).opensRange := le_preimage_of_dualNumber _ _ _ (by
    rw [e]
    rintro s -
    exact ⟨(z ≫ M.σ) s, rfl⟩)
  have hr : Set.range (X.ptY v) ⊆ Set.range (inc₀ X Z) := by
    rintro _ ⟨s, rfl⟩
    exact hb (Set.mem_univ s)
  obtain ⟨w, hw⟩ : ∃ w, w ≫ inc₀ X Z = X.ptY v := ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
  have ered : spMap (GlobalTheory.FlagTan.red c L).toRingHom ≫ w = z ≫ M.σ := by
    rw [← cancel_mono (inc₀ X Z), Category.assoc, hw, e, Category.assoc]
  have hwU : ⊤ ≤ w ⁻¹ᵁ U₀ X Z := le_preimage_of_dualNumber _ _ _ (by rw [ered]; exact hU)
  obtain ⟨zv, hzv, -⟩ := M.existsUnique_lift w hwU
  have hred : spMap (GlobalTheory.FlagTan.red c L).toRingHom ≫ zv = z :=
    (M.existsUnique_lift (z ≫ M.σ) hU).unique (by rw [Category.assoc, hzv, ered]) rfl
  refine ⟨zv, ?_, fun O hO => le_preimage_of_dualNumber _ _ _ (by rw [hred]; exact hO)⟩
  rw [toFlag, ← Category.assoc, hzv, hw]

end GlobalTheory.CompHS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimensionOfDominantFlatCover
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DimCover

theorem exists_trdeg_eq_and_dim_eq {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Sp ℤ) [IsProper f]
    [Flat f] : ∃ d : ℕ, Algebra.trdeg ℤ (X.residueField (genericPoint X)) = d ∧
      topologicalKrullDim X = (d + 1 : ℕ) := by
  obtain ⟨A, _, _, _, _, _, j, _, -, -, hA⟩ := exists_affine_chart_trdeg_eq f (genericPoint X)
  obtain ⟨d, hd⟩ := exists_trdeg_eq_natCast ℤ (A := A)
  rw [hA] at hd
  have h₁ := topologicalKrullDim_preimage_genericPoint_eq f hd
  have H := IsPullback.of_hasPullback f (spMap (algebraMap ℤ ℚ))
  have := IsPreimmersion.of_isLocalization (R := ℤ) (S := ℚ) (nonZeroDivisors ℤ)
  obtain ⟨e₁, r₁⟩ := isEmbedding_and_range_eq_of_isPullback f H
  have hr₁ : Set.range (spMap (algebraMap ℤ ℚ)) = {genericPoint (Spec (.of ℤ))} := by
    refine Set.eq_singleton_iff_nonempty_unique_mem.mpr ⟨Set.range_nonempty _, ?_⟩
    rintro _ ⟨x, rfl⟩
    rw [genericPoint_eq_bot_of_affine]
    refine PrimeSpectrum.ext ?_
    change Ideal.comap (algebraMap ℤ ℚ) x.asIdeal = ⊥
    have := x.isPrime
    rw [Ideal.eq_bot_of_prime x.asIdeal]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective ℤ ℚ)
  rw [hr₁] at r₁
  refine ⟨d, ?_, IntModel.topologicalKrullDim_eq_succ Int.not_isField H
    ((topologicalKrullDim_eq_of_isEmbedding e₁ r₁).symm.trans h₁)⟩
  have hb : Function.Bijective (IsLocalRing.residue X.functionField) :=
    ⟨RingHom.injective _, IsLocalRing.residue_surjective⟩
  have e := ((RingEquiv.ofBijective _ hb).toIntAlgEquiv).trdeg_eq
  exact e.symm.trans
    ((congrArg (@Algebra.trdeg ℤ X.functionField _ _) (Subsingleton.elim _ _)).trans hd)

theorem charZero_residueField {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Sp ℤ) [Flat f] :
    CharZero (X.residueField (genericPoint X)) := by
  have := (flat_int_iff_charZero f).1 inferInstance
  have : CharZero X.functionField :=
    ((X.presheaf.germ ⊤ (genericPoint X) trivial).hom.charZero_iff
      (germ_injective_of_isIntegral X _ _)).1 this
  exact ((IsLocalRing.residue X.functionField).charZero_iff (RingHom.injective _)).1 this

theorem topologicalKrullDim_eq (k : Type) [CommRing k] (Y Z : Scheme.{0}) [IsIntegral Y]
    [IsIntegral Z] (p : Y ⟶ Sp k) (q : Z ⟶ Sp k) (D : ℕ) (h : IsArithVar p D) (hq : IsProjOver q)
    (hf : Flat (q ≫ spMap (Int.castRingHom k))) (g : Z ⟶ Y) (_ : g ≫ p = q)
    (hη : g (genericPoint Z) = genericPoint Y) (hd : g.residueDegree (genericPoint Z) ≠ 0) :
    topologicalKrullDim Z = (D + 1 : ℕ) := by
  have := h.finite
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.2 this
  have := CommonModel.isProper_of_isProjOver hq
  have := CommonModel.isProper_of_isProjOver h.isProjOver
  have := h.flat
  obtain ⟨a, ha, ha'⟩ := exists_trdeg_eq_and_dim_eq (p ≫ spMap (Int.castRingHom k))
  obtain ⟨b, hb, hb'⟩ := exists_trdeg_eq_and_dim_eq (q ≫ spMap (Int.castRingHom k))
  rw [← hη] at ha
  let := (g.residueFieldMap (genericPoint Z)).hom.toAlgebra
  have : Module.Finite (Y.residueField (g (genericPoint Z))) (Z.residueField (genericPoint Z)) :=
    Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hd)
  have : CharZero (Y.residueField (g (genericPoint Z))) :=
    hη ▸ charZero_residueField (p ≫ spMap (Int.castRingHom k))
  have e := trdeg_eq_of_isAlgebraic_top ℤ (Y.residueField (g (genericPoint Z)))
    (Z.residueField (genericPoint Z))
  obtain rfl : b = a := by exact_mod_cast hb.symm.trans (e.trans ha)
  rw [hb', ← ha', h.dim_eq]

end GlobalTheory.DimCover
end
end
