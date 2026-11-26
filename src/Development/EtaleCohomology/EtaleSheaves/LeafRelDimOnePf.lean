module

public import Development.EtaleCohomology.EtaleSheaves.LeafVanStalk
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsNeZeroIsStandardSmoothOfRelativeDimension
public import Development.EtaleCohomology.EtaleSheaves.ZeroSheafMaps.EtaleSheafMapZeroOfLocallyZeroOnFreeSheafGenerat

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafRelDimOnePf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafRelDimOnePf

theorem exists_ne_generic {C : Scheme.{0}} [IsIntegral C] (hd : topologicalKrullDim C = 1) :
    ∃ x : C, x ≠ genericPoint C := by
  by_contra h
  push Not at h
  have : Subsingleton C := ⟨fun a b => (h a).trans (h b).symm⟩
  have : DiscreteTopology C := inferInstance
  have := topologicalKrullDim_zero_of_discreteTopology C
  rw [hd] at this
  exact absurd this (by decide)

theorem isField_top (Ω : Type) [Field Ω] : IsField Γ(Sp Ω, ⊤) :=
  MulEquiv.isField (Field.toIsField Ω)
    (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv.toMulEquiv

theorem chart (Ω : Type) [Field Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω) [IsIntegral C]
    (hd : topologicalKrullDim C = 1) (U : (Sp Ω).Opens) (V : C.Opens) (hV : IsAffineOpen V)
    (x : C) (hx : x ∈ V) (hxη : x ≠ genericPoint C) (e : V ≤ c ⁻¹ᵁ U)
    (hs : (c.appLE U V e).hom.IsStandardSmooth) :
    RingHom.IsStandardSmoothOfRelativeDimension 1 (c.appLE U V e).hom := by
  have hU : U = ⊤ := by
    ext p
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    have : p = c x := Subsingleton.elim _ _
    subst this
    exact e hx
  subst hU
  have : Nonempty V := ⟨⟨x, hx⟩⟩
  let : Field Γ(Sp Ω, ⊤) := (isField_top Ω).toField
  let : Algebra Γ(Sp Ω, ⊤) Γ(C, V) := (c.appLE ⊤ V e).hom.toAlgebra
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hs.out
  have : Algebra.IsStandardSmoothOfRelativeDimension P.dimension Γ(Sp Ω, ⊤) Γ(C, V) :=
    P.isStandardSmoothOfRelativeDimension rfl
  have h1 := GlobalTheory.AffinePoints.ringKrullDim_eq_of_isStandardSmooth (K := Γ(Sp Ω, ⊤)) (A := Γ(C, V))
    (d := P.dimension)
  have hle : ringKrullDim Γ(C, V) ≤ 1 := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ← hd]
    exact hV.fromSpec.isOpenEmbedding.isInducing.topologicalKrullDim_le
  have hne : ringKrullDim Γ(C, V) ≠ 0 := by
    intro h0
    have : Ring.KrullDimLE 0 Γ(C, V) := Ring.krullDimLE_iff.mpr (by rw [h0]; rfl)
    have hF := Ring.KrullDimLE.isField_of_isDomain (R := Γ(C, V))
    let := hF.toField
    have hη : genericPoint C ∈ V :=
      ((genericPoint_spec C).mem_open_set_iff V.isOpen).mpr ⟨x, by simp, hx⟩
    have hx' : x ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hx
    have hη' : genericPoint C ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hη
    obtain ⟨a, rfl⟩ := hx'
    obtain ⟨b, hb⟩ := hη'
    apply hxη
    rw [← hb]
    have key : ∀ p : PrimeSpectrum Γ(C, V), p.asIdeal = ⊥ := by
      intro p
      have hp := p.isPrime
      exact Ideal.eq_bot_of_prime _
    congr 1
    exact PrimeSpectrum.ext ((key a).trans (key b).symm)
  rw [h1] at hle hne
  have h2 : P.dimension ≤ 1 := by exact_mod_cast hle
  have h3 : P.dimension ≠ 0 := by exact_mod_cast hne
  exact P.isStandardSmoothOfRelativeDimension (by omega)

theorem LeafRelDimOne_of : LateralTheory.E.LeafSmoothOfNormalPf.LeafRelDimOne := by
  intro Ω _ C c hC hs hd
  obtain ⟨x₀, hx₀⟩ := exists_ne_generic hd
  constructor
  intro y
  by_cases hy : y = genericPoint C
  · obtain ⟨U, hU, V, hV, hx, e, h⟩ := Smooth.exists_isStandardSmooth c x₀
    have hyV : y ∈ V := hy ▸ ((genericPoint_spec C).mem_open_set_iff V.isOpen).mpr ⟨x₀, by simp, hx⟩
    exact ⟨U, hU, V, hV, hyV, e, chart Ω c hd U V hV x₀ hx hx₀ e h⟩
  · obtain ⟨U, hU, V, hV, hx, e, h⟩ := Smooth.exists_isStandardSmooth c y
    exact ⟨U, hU, V, hV, hx, e, chart Ω c hd U V hV y hx hy e h⟩

end LateralTheory.E.LeafRelDimOnePf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.BaseLocLocPf
set_option linter.style.haveILetI false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

namespace LateralTheory.E.BaseLocLocPf

theorem pb_cancel {C : Type*} [Category C] {P X Y Z T : C} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    {i : Z ⟶ T} [Mono i] (h : IsPullback a b (f ≫ i) (g ≫ i)) : IsPullback a b f g := by
  refine ⟨⟨by simpa [← cancel_mono i] using h.w⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => h.lift s.fst s.snd (by simp [s.condition_assoc])) (fun s => by simp) (fun s => by simp) ?_⟩⟩
  intro s m h1 h2
  apply h.hom_ext <;> simp [h1, h2]

theorem loc_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (M : Submonoid A)
    (hf : @IsLocalization _ _ M _ _ f.toAlgebra) [Algebra B C] (N : Submonoid B) [IsLocalization N C] :
    ∃ M' : Submonoid A, @IsLocalization _ _ M' _ _ ((algebraMap B C).comp f).toAlgebra := by
  letI := f.toAlgebra
  letI : Algebra A C := ((algebraMap B C).comp f).toAlgebra
  haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact ⟨_, IsLocalization.localization_localization_isLocalization M N C⟩

theorem loc_equiv' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] (M : Submonoid A)
    [IsLocalization M B] (e : B ≃+* C) :
    @IsLocalization _ _ M _ _ ((e : B →+* C).comp (algebraMap A B)).toAlgebra := by
  letI : Algebra A C := ((e : B →+* C).comp (algebraMap A B)).toAlgebra
  exact IsLocalization.isLocalization_of_algEquiv M (AlgEquiv.ofRingEquiv (f := e) (fun _ => rfl))

theorem chart {Z S : Scheme.{0}} (c : Z ⟶ S) (x : S) (W : (pullback c (S.fromSpecStalk x) : Scheme.{0}).Opens)
    (y : (pullback c (S.fromSpecStalk x) : Scheme.{0})) (hy : y ∈ W) :
    ∃ U : (pullback c (S.fromSpecStalk x) : Scheme.{0}).Opens, y ∈ U ∧ U ≤ W ∧
    ∃ V : Z.Opens, IsAffineOpen V ∧ (V : Set Z).Nonempty ∧
    ∃ f : Γ(Z, V) →+* Γ((pullback c (S.fromSpecStalk x) : Scheme.{0}), U), ∃ M : Submonoid Γ(Z, V),
      @IsLocalization _ _ M _ _ f.toAlgebra := by
  obtain ⟨U0, hU0a, hxU0, -⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : S.Opens) from trivial)
  have hg : S.fromSpecStalk x = Spec.map (S.presheaf.germ U0 x hxU0) ≫ hU0a.fromSpec :=
    (hU0a.fromSpecStalk_eq_fromSpecStalk hxU0).symm
  have hgU : ∀ z, S.fromSpecStalk x z ∈ U0 := by
    intro z; rw [hg, Scheme.Hom.comp_apply]; exact hU0a.range_fromSpec.le (Set.mem_range_self _)
  have hcy : c (pullback.fst c (S.fromSpecStalk x) y) ∈ U0 := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]; exact hgU _
  obtain ⟨V, hVa, hyV, hVU⟩ := exists_isAffineOpen_mem_and_subset
    (show pullback.fst c (S.fromSpecStalk x) y ∈ c ⁻¹ᵁ U0 from hcy)
  have hVU' : V ≤ c ⁻¹ᵁ U0 := hVU
  set p := pullback.fst c (S.fromSpecStalk x)
  set O := p ⁻¹ᵁ V with hOdef
  have H1 : IsPullback (p ∣_ V) O.ι V.ι p := isPullback_morphismRestrict p V
  have H2 : IsPullback (p ∣_ V) (O.ι ≫ pullback.snd c (S.fromSpecStalk x)) (V.ι ≫ c) (S.fromSpecStalk x) :=
    H1.paste_vert (IsPullback.of_hasPullback c (S.fromSpecStalk x))
  let ψ := c.appLE U0 V hVU'
  have e1 : V.ι ≫ c = hVa.isoSpec.hom ≫ Spec.map ψ ≫ hU0a.fromSpec := by
    rw [IsAffineOpen.SpecMap_appLE_fromSpec c hU0a hVa hVU', ← IsAffineOpen.isoSpec_inv_ι]; simp
  have H3 : IsPullback ((p ∣_ V) ≫ hVa.isoSpec.hom) (O.ι ≫ pullback.snd c (S.fromSpecStalk x)) (Spec.map ψ ≫ hU0a.fromSpec)
      (Spec.map (S.presheaf.germ U0 x hxU0) ≫ hU0a.fromSpec) := by
    rw [← hg]
    exact IsPullback.of_iso H2 (Iso.refl _) hVa.isoSpec (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (by simp [e1]) (by simp)
  have H4 := pb_cancel H3
  letI : Algebra Γ(S, U0) Γ(Z, V) := ψ.hom.toAlgebra
  letI := S.presheaf.algebra_section_stalk ⟨x, hxU0⟩
  haveI hSt : IsLocalization.AtPrime (S.presheaf.stalk x) (hU0a.primeIdealOf ⟨x, hxU0⟩).asIdeal :=
    hU0a.isLocalization_stalk ⟨x, hxU0⟩
  have H5 := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct Γ(S, U0) Γ(Z, V) (S.presheaf.stalk x))
  let e := H4.isoIsPullback _ _ H5
  haveI : IsAffine O.toScheme := IsAffine.of_isIso e.hom
  have hOa : IsAffineOpen O := this
  let eR : CommRingCat.of (Γ(Z, V) ⊗[Γ(S, U0)] S.presheaf.stalk x) ≅ Γ(pullback c (S.fromSpecStalk x), O) :=
    (Scheme.ΓSpecIso _).symm ≪≫ Scheme.Γ.mapIso e.op ≪≫ O.topIso
  have hL := loc_equiv' (Algebra.algebraMapSubmonoid Γ(Z, V) (hU0a.primeIdealOf ⟨x, hxU0⟩).asIdeal.primeCompl)
    eR.commRingCatIsoToRingEquiv
  have hyO : y ∈ O := hyV
  obtain ⟨h, hhW, hyh⟩ := hOa.exists_basicOpen_le (V := W) ⟨y, hy⟩ hyO
  haveI := hOa.isLocalization_basicOpen h
  obtain ⟨M, hM⟩ := loc_comp (C := Γ(pullback c (S.fromSpecStalk x), (pullback c (S.fromSpecStalk x)).basicOpen h)) _ _ hL (Submonoid.powers h)
  exact ⟨_, hyh, hhW, V, hVa, ⟨_, hyV⟩, _, M, hM⟩

theorem BaseLocLoc_of : LateralTheory.E.BaseAICPf.BaseLocLoc := by
  intro Z S c _ _ _ _ _ x W y hy
  exact chart c x W y hy

end LateralTheory.E.BaseLocLocPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafTensUPPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace LateralTheory.E.LeafTensUPPf
open LateralTheory.E.LeafTwTensExPf
open Classical

variable {R : Type} [CommRing R] {I J K : Cx R}

theorem lift_lo (μ : Pair I J K) (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    μ.lift U w (lo I J ⟨(s, t), h⟩ (a ⊗ₜ b)) = μ.mul U s t w h a b := by
  simp [Pair.lift, lo]

theorem lift_nat (μ : Pair I J K) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) :
    ((K.X w).obj.map g.op).hom ∘ₗ μ.lift U w = μ.lift V w ∘ₗ Tens.res g w := by
  apply DirectSum.linearMap_ext; rintro ⟨⟨s, t⟩, h⟩
  apply TensorProduct.ext'; intro a b
  simp only [LinearMap.comp_apply]
  have e := tres_tmul I J g w ⟨(s, t), h⟩ a b
  change Sec.res g (μ.lift U w (lo I J ⟨(s, t), h⟩ (a ⊗ₜ b))) = μ.lift V w (Tens.res g w (lo I J ⟨(s, t), h⟩ (a ⊗ₜ b)))
  rw [e]
  change Sec.res g (μ.lift U w (lo I J ⟨(s, t), h⟩ (a ⊗ₜ b))) = μ.lift V w (lo I J ⟨(s, t), h⟩ (Sec.res g a ⊗ₜ Sec.res g b))
  rw [lift_lo, lift_lo, μ.nat]

theorem lift_d (μ : Pair I J K) (U : Scheme.{0}) (w : ℤ) :
    ((K.d w (w + 1)).hom.app (op U)).hom ∘ₗ μ.lift U w = μ.lift U (w + 1) ∘ₗ dT I J U w := by
  apply DirectSum.linearMap_ext; rintro ⟨⟨s, t⟩, h⟩
  apply TensorProduct.ext'; intro a b
  simp only [LinearMap.comp_apply]
  change Sec.map (K.d w (w + 1)) (μ.lift U w (lo I J ⟨(s, t), h⟩ (a ⊗ₜ b))) =
    μ.lift U (w + 1) (dT I J U w (lo I J ⟨(s, t), h⟩ (a ⊗ₜ b)))
  rw [dT_tmul, map_add (f := _), map_zsmul, lift_lo, lift_lo, lift_lo, μ.leibniz, Units.smul_def]

def liftP (μ : Pair I J K) (w : ℤ) : TP I J w ⟶ (K.X w).obj where
  app U := ModuleCat.ofHom (μ.lift U.unop w)
  naturality _ _ g := ModuleCat.hom_ext (lift_nat μ g.unop w).symm

theorem tensorPresheafLift_comm (μ : Pair I J K) (w : ℤ) :
    liftP μ w ≫ (K.d w (w + 1)).hom = dTP I J w ≫ liftP μ (w + 1) := by
  ext U : 2
  exact ModuleCat.hom_ext (lift_d μ U.unop w)

theorem etale_tensor_presheaf_lift_is_local_iso {T : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (w : ℤ) :
    Scheme.etaleTopology.{0}.W (liftP τ w) := by
  have : Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (liftP τ w) := ⟨fun {U} y => by
    obtain ⟨S, hS, hP⟩ := hτ.1 U w y
    refine Scheme.etaleTopology.{0}.superset_covering ?_ hS
    intro V g hg
    obtain ⟨x, hx⟩ := hP V g hg
    exact ⟨x, hx⟩⟩
  have : Presheaf.IsLocallyInjective Scheme.etaleTopology.{0} (liftP τ w) := ⟨fun {X} x y hxy => by
    let x' : Tens I J X.unop w := x
    let y' : Tens I J X.unop w := y
    have hxy' : τ.lift X.unop w x' = τ.lift X.unop w y' := hxy
    have h0 : τ.lift X.unop w (x' - y') = 0 := by
      rw [map_sub]; exact sub_eq_zero.mpr hxy'
    obtain ⟨S, hS, hP⟩ := hτ.2 X.unop w (x' - y') h0
    refine Scheme.etaleTopology.{0}.superset_covering ?_ hS
    intro V g hg
    have h1 : Tens.res g w (x' - y') = 0 := hP V g hg
    rw [map_sub, sub_eq_zero] at h1
    exact h1⟩
  exact GrothendieckTopology.W_of_isLocallyBijective _ _

theorem etale_tensor_pairing_universal_property_holds : LateralTheory.E.LeafPairExtPf2.LeafTensUP := by
  intro R _ I J T K τ hτ μ
  have hb : ∀ w, Function.Bijective (fun g : (T.X w).obj ⟶ (K.X w).obj => liftP τ w ≫ g) :=
    fun w => etale_tensor_presheaf_lift_is_local_iso τ hτ w _ (K.X w).property
  choose u0 hu0' using fun w => (hb w).2 (liftP μ w)
  have hu0 : ∀ w, liftP τ w ≫ u0 w = liftP μ w := hu0'
  let u : T ⟶ K :=
    { f := fun w => ⟨u0 w⟩
      comm' := by
        rintro i j rfl
        apply Sheaf.hom_ext
        change u0 i ≫ (K.d i (i + 1)).hom = (T.d i (i + 1)).hom ≫ u0 (i + 1)
        have key : liftP τ i ≫ (u0 i ≫ (K.d i (i + 1)).hom) = liftP τ i ≫ ((T.d i (i + 1)).hom ≫ u0 (i + 1)) := by
          rw [← Category.assoc, ← Category.assoc, hu0, tensorPresheafLift_comm, tensorPresheafLift_comm, Category.assoc, hu0]
        exact (etale_tensor_presheaf_lift_is_local_iso τ hτ i _ (K.X (i + 1)).property).1 key }
  refine ⟨u, fun U s t w h a b => ?_⟩
  have e := congrArg (fun f => (f.app (op U)).hom (lo I J ⟨(s, t), h⟩ (a ⊗ₜ b))) (hu0 w)
  simp only at e
  rw [← lift_lo τ, ← lift_lo μ]
  exact e

end LateralTheory.E.LeafTensUPPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.ChartMapBase
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.StandardEtaleChartsIdempotentGluing LateralTheory.E.StdChartsProof
  LateralTheory.E.ChartsGeom_vpaPf

namespace LateralTheory.E.ChartOverlap₂

set_option linter.unusedSectionVars false

variable {A K : Type} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]

theorem restr_iff (B : Subalgebra A K) (t : K) (S : Subalgebra A K) {R W : Type} [CommRing R] [CommRing W]
    (eR : R ≃+* S) (eW : W ≃+* AdjoinInv B t) (res : R →+* W) (hc : ∀ r, ((eW (res r) : AdjoinInv B t) : K) = (eR r : K))
    (P : PrimeSpectrum W) (x : PrimeSpectrum S) :
    Restr B t (PrimeSpectrum.comap (eW.symm : AdjoinInv B t →+* W) P) S x ↔
      PrimeSpectrum.comap (eR : R →+* S) x = PrimeSpectrum.comap res P := by
  have key : ∀ s : S, (∃ d ∈ (PrimeSpectrum.comap (eW.symm : AdjoinInv B t →+* W) P).asIdeal, (d : K) = (s : K)) ↔
      res (eR.symm s) ∈ P.asIdeal := by
    intro s
    have hd : eW (res (eR.symm s)) = ⟨(s : K), by simpa [hc] using (eW (res (eR.symm s))).2⟩ := by
      apply Subtype.ext; simp [hc]
    constructor
    · rintro ⟨d, hd1, hd2⟩
      have : d = eW (res (eR.symm s)) := by rw [hd]; exact Subtype.ext hd2
      subst this
      simpa using hd1
    · intro h
      refine ⟨eW (res (eR.symm s)), ?_, by simp [hc]⟩
      simpa using h
  unfold Restr
  simp_rw [key]
  constructor
  · intro h
    ext r
    simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, RingHom.coe_coe]
    have := h (eR r)
    simpa using this
  · intro h s
    have := congrArg (fun q : PrimeSpectrum R => eR.symm s ∈ q.asIdeal) h
    simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, RingHom.coe_coe, RingEquiv.apply_symm_apply] at this
    exact Iff.of_eq this

theorem chartMap_base {Z : Scheme.{0}} {U : Z.Opens} (hU : IsAffineOpen U) (φ : Γ(Z, U) →+* K)
    (hi : Function.Injective φ) (B : Subalgebra A K) (hr : φ.range = B.toSubring) (x : PrimeSpectrum B) :
    (chartMap hU φ hi B hr).base x =
      hU.fromSpec.base (PrimeSpectrum.comap (chartEquiv φ hi B hr : Γ(Z, U) →+* B) x) := rfl

theorem fromSpec_res {Z : Scheme.{0}} {U W : Z.Opens} (hU : IsAffineOpen U) (hW : IsAffineOpen W) (h : W ≤ U)
    (P : PrimeSpectrum Γ(Z, W)) :
    hU.fromSpec.base (PrimeSpectrum.comap (Z.presheaf.map (homOfLE h).op).hom P) = hW.fromSpec.base P := by
  rw [← hU.map_fromSpec hW (homOfLE h).op]; rfl

theorem Overlap_of : LateralTheory.E.ChartsGeom_vpaPf.Overlap := by
  intro A _ _ K _ _ Z p B C t _ U V φU φV φW hU hV hW hUV iU iV iW rU rV rW cU cV x y
  set eU := chartEquiv φU iU B rU
  set eV := chartEquiv φV iV C rV
  set eW := chartEquiv φW iW (AdjoinInv B t) rW
  have hcU : ∀ r, ((eW ((Z.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom r) : AdjoinInv B t) : K) =
      (eU r : K) := fun r => cU r
  have hcV : ∀ r, ((eW ((Z.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom r) : AdjoinInv B t) : K) =
      (eV r : K) := fun r => cV r
  rw [chartMap_base, chartMap_base]
  constructor
  · intro h
    have hzU : hU.fromSpec.base (PrimeSpectrum.comap (eU : Γ(Z, U) →+* B) x) ∈ (U : Set Z) := by
      rw [← hU.range_fromSpec]; exact ⟨_, rfl⟩
    have hzV : hU.fromSpec.base (PrimeSpectrum.comap (eU : Γ(Z, U) →+* B) x) ∈ (V : Set Z) := by
      rw [h, ← hV.range_fromSpec]; exact ⟨_, rfl⟩
    have hz : hU.fromSpec.base (PrimeSpectrum.comap (eU : Γ(Z, U) →+* B) x) ∈ Set.range hW.fromSpec.base := by
      rw [hW.range_fromSpec]; exact ⟨hzU, hzV⟩
    obtain ⟨P, hP⟩ := hz
    refine ⟨PrimeSpectrum.comap (eW.symm : AdjoinInv B t →+* Γ(Z, U ⊓ V)) P,
      (restr_iff B t B eU eW _ hcU P x).2 ?_, (restr_iff B t C eV eW _ hcV P y).2 ?_⟩
    · apply hU.fromSpec.isOpenEmbedding.injective
      exact ((fromSpec_res hU hW inf_le_left P).trans hP).symm
    · apply hV.fromSpec.isOpenEmbedding.injective
      exact (h.symm.trans hP.symm).trans (fromSpec_res hV hW inf_le_right P).symm
  · rintro ⟨Q, hx, hy⟩
    have hQ : Q = PrimeSpectrum.comap (eW.symm : AdjoinInv B t →+* Γ(Z, U ⊓ V))
        (PrimeSpectrum.comap (eW : Γ(Z, U ⊓ V) →+* AdjoinInv B t) Q) := by
      ext a; simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, RingHom.coe_coe, RingEquiv.apply_symm_apply]
    rw [hQ] at hx hy
    have hx1 := (restr_iff B t B eU eW _ hcU _ x).1 hx
    have hy1 := (restr_iff B t C eV eW _ hcV _ y).1 hy
    exact (congrArg hU.fromSpec.base hx1).trans ((fromSpec_res hU hW inf_le_left _).trans
      ((fromSpec_res hV hW inf_le_right _).symm.trans (congrArg hV.fromSpec.base hy1).symm))

end LateralTheory.E.ChartOverlap₂
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafClosedSHPosPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite Polynomial IsLocalRing GlobalTheory.EtC LateralTheory.E.E4

namespace LateralTheory.E.LeafClosedSHPosPf

theorem hens_of_surj {A B : Type} [CommRing A] [CommRing B] [HenselianLocalRing A] [Nontrivial B]
    (φ : A →+* B) (hφ : Function.Surjective φ) : HenselianLocalRing B := by
  have := IsLocalHom.of_surjective φ hφ
  have : IsLocalRing B := IsLocalRing.of_surjective φ hφ
  refine { is_henselian := ?_ }
  intro f hf a₀ h₁ h₂
  have hl : f ∈ Polynomial.lifts φ := (Polynomial.lifts_iff_coeff_lifts f).2 (fun n => hφ _)
  obtain ⟨g, hg, -, hgm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hf
  obtain ⟨b₀, rfl⟩ := hφ a₀
  have hev : ∀ (p : A[X]) (x : A), (p.map φ).eval (φ x) = φ (p.eval x) := fun p x => by
    rw [Polynomial.eval_map, eval₂_at_apply]
  subst hg
  have h1 : g.eval b₀ ∈ maximalIdeal A := by
    rw [hev] at h₁
    exact (mem_maximalIdeal _).2 (fun hu => (mem_maximalIdeal _).1 h₁ (hu.map φ))
  have h2 : IsUnit (g.derivative.eval b₀) := by
    rw [derivative_map, hev] at h₂
    exact IsUnit.of_map φ _ h₂
  obtain ⟨a, ha, ham⟩ := HenselianLocalRing.is_henselian g hgm b₀ h1 h2
  refine ⟨φ a, ?_, ?_⟩
  · rw [IsRoot, hev, ha.eq_zero, map_zero]
  · rw [← map_sub]
    exact (mem_maximalIdeal _).2 (fun hu => (mem_maximalIdeal _).1 ham (IsUnit.of_map φ _ hu))

theorem sepClosed_of_surj {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (φ : A →+* B) [IsLocalHom φ] (hφ : Function.Surjective φ) [IsSepClosed (ResidueField A)] :
    IsSepClosed (ResidueField B) := by
  have hs : Function.Surjective (ResidueField.map φ) := by
    intro y
    obtain ⟨b, rfl⟩ := residue_surjective y
    obtain ⟨a, rfl⟩ := hφ b
    exact ⟨residue A a, ResidueField.map_residue φ a⟩
  let e : ResidueField A ≃+* ResidueField B :=
    RingEquiv.ofBijective (ResidueField.map φ) ⟨(ResidueField.map φ).injective, hs⟩
  refine ⟨fun p hp => ?_⟩
  have h1 : (p.map (e.symm : ResidueField B →+* ResidueField A)).Separable := hp.map
  have h2 := (IsSepClosed.splits_of_separable _ h1).map (e : ResidueField A →+* ResidueField B)
  rw [Polynomial.map_map] at h2
  convert h2
  ext x; simp

theorem sub_of_iso {X Y : Scheme.{0}} (e : X ≅ Y) (R : Type) [CommRing R] (F : Shv R) (n : ℤ)
    (h : Subsingleton (H R (sch.obj Y) F n)) : Subsingleton (H R (sch.obj X) F n) := by
  refine ⟨fun x y => ?_⟩
  have key : ∀ z : H R (sch.obj X) F n,
      z = pull R (sch.map e.hom) F n (pull R (sch.map e.inv) F n z) := by
    intro z
    rw [← pull_comp, ← CategoryTheory.Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]
  rw [key x, key y, Subsingleton.elim (pull R (sch.map e.inv) F n x) (pull R (sch.map e.inv) F n y)]

theorem sub_of_empty (hy : Hyps) (R : Type) [CommRing R] (F : Shv R) (W : Scheme.{0}) [IsEmpty W] (n : ℤ)
    (hn : 0 < n) : Subsingleton (H R (sch.obj W) F n) := by
  have a5 : A5 := hy.2.2.2.2.1
  suffices h : ∀ x : H R (sch.obj W) F n, x = 0 from ⟨fun a b => by rw [h a, h b]⟩
  intro x
  obtain ⟨Z, f, -, -, hf⟩ := a5 R W F n hn x
  have : IsEmpty Z := ⟨fun z => isEmptyElim (f.base z)⟩
  let g : W ⟶ Z := (isInitialOfIsEmpty (X := W)).to Z
  have hgf : g ≫ f = 𝟙 W := (isInitialOfIsEmpty (X := W)).hom_ext _ _
  have : pull R (sch.map (g ≫ f)) F n x = x := by rw [hgf, CategoryTheory.Functor.map_id, pull_id]
  rw [← this, CategoryTheory.Functor.map_comp, pull_comp, hf, map_zero]

theorem LeafClosedSHPos_of : LateralTheory.E.LeafVanBPf.LeafClosedSHPos := by
  intro hy q _ i A _ _ hA hq W' ι' _ n hn
  rcases isEmpty_or_nonempty W' with hW | ⟨⟨w⟩⟩
  · exact sub_of_empty hy _ _ W' n hn
  obtain ⟨hAff, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine ι'
  let B : Type := Γ(W', ⊤)
  let ψ : A →+* B := (ι'.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  have hψ : Function.Surjective ψ := hsurj.comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).2
  have : Nontrivial B := by
    by_contra hB
    rw [not_nontrivial_iff_subsingleton] at hB
    let p := W'.isoSpec.hom.base w
    exact p.isPrime.ne_top (Subsingleton.elim _ _)
  obtain ⟨hH, hS⟩ := hA
  have := IsLocalHom.of_surjective ψ hψ
  have hHB : HenselianLocalRing B := hens_of_surj ψ hψ
  have hSB : SH B := ⟨hHB, sepClosed_of_surj ψ hψ⟩
  have h2 := LateralTheory.E.LeafVanBPf.heightFunctionalStatement_of_pairingProperties hy (ZMod q) B hSB (tw q i) n hn
  exact sub_of_iso W'.isoSpec (ZMod q) (tw q i) n h2

end LateralTheory.E.LeafClosedSHPosPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.DegreeZeroGenerators
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.DegreeZeroGenerators
open LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafShMapZeroPf LateralTheory.E.LeafShMapZeroPf.Gen

abbrev Rq (q : ℕ) := ULift.{1} (ZMod q)

abbrev Gq (q : ℕ) : Type 0 ⥤ ModuleCat.{1} (Rq q) := uliftFunctor.{1, 0} ⋙ ModuleCat.free (Rq q)

abbrev P0 (B : Scheme.{0}) (q : ℕ) (U : B.Etale) : B.Etaleᵒᵖ ⥤ ModuleCat.{1} (Rq q) :=
  ((Functor.whiskeringRight B.Etaleᵒᵖ (Type 0) (ModuleCat.{1} (Rq q))).obj (Gq q)).obj (yoneda.obj U)

def gen {B : Scheme.{0}} {q : ℕ} (U : B.Etale) : ((F0 B q).obj U).obj.obj (op U) :=
  (toSheafify (EtTop B) (P0 B q U)).app (op U) (ModuleCat.freeMk (ULift.up (𝟙 U)))

theorem gen_nat {B : Scheme.{0}} {q : ℕ} {U U' : B.Etale} (a : U' ⟶ U) :
    ((F0 B q).map a).hom.app (op U') (gen U') = ((F0 B q).obj U).obj.map a.op (gen U) := by
  have h1 := ConcreteCategory.congr_hom (NatTrans.congr_app (toSheafify_naturality (EtTop B)
    (((Functor.whiskeringRight B.Etaleᵒᵖ (Type 0) (ModuleCat.{1} (Rq q))).obj (Gq q)).map (yoneda.map a))) (op U'))
    (ModuleCat.freeMk (ULift.up (𝟙 U')))
  have h2 := ConcreteCategory.congr_hom ((toSheafify (EtTop B) (P0 B q U)).naturality a.op)
    (ModuleCat.freeMk (ULift.up (𝟙 U)))
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h1 h2
  unfold gen
  refine Eq.trans ?_ (h1.symm.trans ?_)
  · rfl
  · refine Eq.trans ?_ h2
    congr 1
    simp only [Gq, Functor.comp_map]
    erw [ModuleCat.free_map_apply, ModuleCat.free_map_apply]
    show ModuleCat.freeMk (ULift.up (𝟙 U' ≫ a)) = ModuleCat.freeMk (ULift.up (a ≫ 𝟙 U))
    simp

theorem free_etale_sheaf_zmod_exists_hom_sending_generator {B : Scheme.{0}} {q : ℕ} (H : SShv B q) (U : B.Etale) (x : H.obj.obj (op U)) :
    ∃ t : (F0 B q).obj U ⟶ H, t.hom.app (op U) (gen U) = x := by
  let φ : P0 B q U ⟶ H.obj :=
    { app := fun W => ModuleCat.freeDesc (TypeCat.ofHom (fun f : ULift.{1} (W.unop ⟶ U) => H.obj.map f.down.op x))
      naturality := by
        intro W W' f
        apply ModuleCat.free_hom_ext
        intro y
        simp only [Gq, ConcreteCategory.comp_apply, Functor.comp_map]
        erw [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
        show H.obj.map (f.unop ≫ y.down).op x = H.obj.map f (H.obj.map y.down.op x)
        simp }
  refine ⟨((sheafificationAdjunction (EtTop B) _).homEquiv (P0 B q U) H).symm φ, ?_⟩
  have e := ((sheafificationAdjunction (EtTop B) _).homEquiv (P0 B q U) H).apply_symm_apply φ
  rw [Adjunction.homEquiv_unit] at e
  have e2 := ConcreteCategory.congr_hom (NatTrans.congr_app e (op U)) (ModuleCat.freeMk (ULift.up (𝟙 U)))
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at e2
  unfold gen
  refine Eq.trans ?_ (e2.trans ?_)
  · rfl
  · simp only [φ]
    erw [ModuleCat.freeDesc_apply]
    show H.obj.map (𝟙 U).op x = x
    simp

theorem free_etale_sheaf_zmod_representable_generates : EtaleSheafMapZeroOfLocallyZeroOnFreeSheafGenerators := by
  intro B q H H' g h
  apply (sheafToPresheaf (EtTop B) (ModuleCat.{1} (Rq q))).map_injective
  rw [Functor.map_zero]
  apply NatTrans.ext
  funext U
  induction U with | op U => ?_
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨t, ht⟩ := free_etale_sheaf_zmod_exists_hom_sending_generator H U x
  obtain ⟨S, hS, hP⟩ := h U t
  have key : ∀ (U' : B.Etale) (a : U' ⟶ U), S a →
      H'.obj.map a.op (g.hom.app (op U) x) = H'.obj.map a.op 0 := by
    intro U' a ha
    have h3 := congrArg (fun m : (F0 B q).obj U' ⟶ H' =>
      ((sheafToPresheaf (EtTop B) (ModuleCat.{1} (Rq q))).map m).app (op U') (gen U')) (hP U' a ha)
    simp only [Functor.map_comp, Functor.map_zero, NatTrans.comp_app, NatTrans.app_zero,
      ConcreteCategory.comp_apply] at h3
    rw [map_zero, ← ht]
    have n := ConcreteCategory.congr_hom (g.hom.naturality a.op) (t.hom.app (op U) (gen U))
    simp only [ConcreteCategory.comp_apply] at n
    rw [← n]
    have n2 := ConcreteCategory.congr_hom (t.hom.naturality a.op) (gen U)
    simp only [ConcreteCategory.comp_apply] at n2
    rw [← n2, ← gen_nat a]
    exact h3
  have := Sheaf.isSeparated H' U S hS _ 0 key
  simp only [NatTrans.app_zero]
  exact this

end LateralTheory.E.DegreeZeroGenerators
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.RootPowPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC Polynomial

namespace LateralTheory.E.RootPowPf

theorem prim_eval {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) : IsRoot (cyclotomic q A) ζ.1 := by
  have h := ζ.2.2
  rw [IsRoot.def, ← map_cyclotomic_int q A, Polynomial.eval_map]
  rw [aeval_def] at h
  exact h

theorem prim_pow {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  have h := (prim_eval ζ).dvd (cyclotomic.dvd_X_pow_sub_one q A)
  simpa [IsRoot.def, sub_eq_zero] using h

theorem field_case {q : ℕ} {K : Type} [Field K] (ζ ξ : Prim q K) :
    ∃ a : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (a : ZMod q).val := by
  have : NeZero (q : K) := ⟨ζ.2.1.ne_zero⟩
  have : NeZero q := NeZero.of_neZero_natCast K
  have hζ : IsPrimitiveRoot ζ.1 q := isRoot_cyclotomic_iff.1 (prim_eval ζ)
  have hξ : IsPrimitiveRoot ξ.1 q := isRoot_cyclotomic_iff.1 (prim_eval ξ)
  obtain ⟨i, hi, he⟩ := hζ.eq_pow_of_pow_eq_one hξ.pow_eq_one
  have hc : i.Coprime q := (hζ.pow_iff_coprime (NeZero.pos q) i).1 (he ▸ hξ)
  refine ⟨ZMod.unitOfCoprime i hc, ?_⟩
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi, he]

theorem local_case {q : ℕ} {O : Type} [CommRing O] [IsLocalRing O] (ζ ξ : Prim q O) :
    ∃ a : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (a : ZMod q).val := by
  obtain ⟨a, ha⟩ := field_case (ζ.map (IsLocalRing.residue O)) (ξ.map (IsLocalRing.residue O))
  refine ⟨a, ?_⟩
  change IsLocalRing.residue O ξ.1 = (IsLocalRing.residue O ζ.1) ^ _ at ha
  rw [← map_pow] at ha
  set η := ζ.1 ^ (a : ZMod q).val with hη
  have hηq : η ^ q = 1 := by rw [hη, ← pow_mul, mul_comm, pow_mul, prim_pow, one_pow]
  have hq : q ≠ 0 := by
    rintro rfl
    have := ζ.2.1
    simp at this
  have hηu : IsUnit η := IsUnit.of_pow_eq_one hηq hq
  have hg := (Commute.all ξ.1 η).geom_sum₂_mul q
  rw [prim_pow, hηq, sub_self] at hg
  have hu : IsUnit (∑ i ∈ Finset.range q, ξ.1 ^ i * η ^ (q - 1 - i)) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, map_pow, ha]
    rw [geom_sum₂_self]
    have h1 : IsUnit ((q : O) * η ^ (q - 1)) := ζ.2.1.mul (hηu.pow _)
    have h2 := (h1.map (IsLocalRing.residue O)).ne_zero
    simpa using h2
  exact sub_eq_zero.1 (hu.mul_right_eq_zero.1 hg)

def sv {q : ℕ} {Y : Scheme.{0}} (ζ ξ : Prim q Γ(Y, ⊤)) : Sieve Y where
  arrows := fun Z g => ∃ a : (ZMod q)ˣ, (ξ.map g.appTop.hom).1 = (ζ.map g.appTop.hom).1 ^ (a : ZMod q).val
  downward_closed := by
    rintro Z W g ⟨a, ha⟩ h
    refine ⟨a, ?_⟩
    change g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ _ at ha
    change (h ≫ g).appTop.hom ξ.1 = (h ≫ g).appTop.hom ζ.1 ^ _
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, ha, map_pow]

theorem nhd {q : ℕ} {Y : Scheme.{0}} (ζ ξ : Prim q Γ(Y, ⊤)) (y : Y) :
    ∃ U : Y.Opens, y ∈ U ∧ sv ζ ξ U.ι := by
  obtain ⟨a, ha⟩ := local_case (ζ.map (Y.presheaf.germ ⊤ y trivial).hom) (ξ.map (Y.presheaf.germ ⊤ y trivial).hom)
  change (Y.presheaf.germ ⊤ y trivial).hom ξ.1 = (Y.presheaf.germ ⊤ y trivial).hom ζ.1 ^ _ at ha
  rw [← map_pow] at ha
  obtain ⟨(U : Y.Opens), hU, i, i', he⟩ := TopCat.Presheaf.germ_eq Y.presheaf (U := ⊤) (V := ⊤) y trivial trivial _ _ ha
  refine ⟨U, hU, a, ?_⟩
  change U.ι.appTop.hom ξ.1 = U.ι.appTop.hom ζ.1 ^ _
  rw [← map_pow]
  have hf : U.ι.appTop = Y.presheaf.map i.op ≫ U.topIso.inv := by
    rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv]
    exact (Y.presheaf.map_comp _ _).symm ▸ rfl
  have hi : i' = i := Subsingleton.elim _ _
  subst hi
  rw [hf]
  exact congrArg U.topIso.inv.hom he

theorem sv_mem {q : ℕ} {Y : Scheme.{0}} (ζ ξ : Prim q Γ(Y, ⊤)) : sv ζ ξ ∈ Scheme.etaleTopology Y := by
  apply Scheme.zariskiTopology_le_etaleTopology
  choose U hU hS using nhd ζ ξ
  refine Scheme.mem_grothendieckTopology_iff.2 ⟨Scheme.Cover.mkOfCovers Y (fun y => (U y : Scheme)) (fun y => (U y).ι)
    (fun y => ⟨y, ⟨y, hU y⟩, rfl⟩) (fun y => inferInstance), ?_⟩
  rintro _ _ ⟨y⟩
  exact hS y

theorem RootPow_of : LateralTheory.E.MulPf.RootPow := by
  classical
  intro q Y ζ s
  induction s using Finset.induction_on with
  | empty => exact ⟨⊤, GrothendieckTopology.top_mem _ _, fun _ _ _ ξ h => absurd h (Finset.notMem_empty ξ)⟩
  | insert ξ s _ ih =>
    obtain ⟨S, hS, h⟩ := ih
    refine ⟨S ⊓ sv ζ ξ, GrothendieckTopology.intersection_covering _ hS (sv_mem ζ ξ), ?_⟩
    rintro Z g ⟨h1, h2⟩ η hη
    rcases Finset.mem_insert.1 hη with rfl | hη
    · exact h2
    · exact h g h1 η hη

end LateralTheory.E.RootPowPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.MulRightMem
noncomputable section
open LateralTheory.E.StandardEtaleChartsIdempotentGluing

namespace LateralTheory.E.LZIdemPowProof

variable {A K : Type} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]

theorem mul_left_mem (S : Subalgebra A K) (I : Ideal A) {s y : K} (hs : s ∈ S)
    (hy : y ∈ I • Subalgebra.toSubmodule S) : s * y ∈ I • Subalgebra.toSubmodule S := by
  refine Submodule.smul_induction_on hy (fun r hr n hn => ?_) (fun x y hx hy => ?_)
  · rw [mul_smul_comm]
    exact Submodule.smul_mem_smul hr (S.mul_mem hs hn)
  · rw [mul_add]; exact add_mem hx hy

theorem mul_right_mem (S : Subalgebra A K) (I : Ideal A) {s y : K} (hs : s ∈ S)
    (hy : y ∈ I • Subalgebra.toSubmodule S) : y * s ∈ I • Subalgebra.toSubmodule S := by
  rw [mul_comm]; exact mul_left_mem S I hs hy

theorem mul_mem_mul (S : Subalgebra A K) (I J : Ideal A) {x y : K}
    (hx : x ∈ I • Subalgebra.toSubmodule S) (hy : y ∈ J • Subalgebra.toSubmodule S) :
    x * y ∈ (I * J) • Subalgebra.toSubmodule S := by
  refine Submodule.smul_induction_on hx (fun r hr n hn => ?_) (fun a b ha hb => ?_)
  · rw [smul_mul_assoc, Submodule.mul_smul]
    exact Submodule.smul_mem_smul hr (mul_left_mem S J hn hy)
  · rw [add_mul]; exact add_mem ha hb

theorem lift_pow (S : Subalgebra A K) (x : K) (hx : x ∈ S) (hp : x * x - x ∈ mS S) (n : ℕ) :
    ∃ y ∈ S, y - x ∈ mS S ∧
      y * y - y ∈ (IsLocalRing.maximalIdeal A ^ (2 ^ n)) • Subalgebra.toSubmodule S := by
  induction n with
  | zero => exact ⟨x, hx, by simp, by simpa [mS] using hp⟩
  | succ n ih =>
    obtain ⟨y, hy, hyx, hyy⟩ := ih
    have hle : IsLocalRing.maximalIdeal A ^ (2 ^ n) ≤ IsLocalRing.maximalIdeal A :=
      Ideal.pow_le_self (by positivity)
    have h2y : y + y - 1 ∈ S := S.sub_mem (S.add_mem hy hy) S.one_mem
    have hpS : y * y - y ∈ S := S.sub_mem (S.mul_mem hy hy) hy
    refine ⟨y - (y + y - 1) * (y * y - y), S.sub_mem hy (S.mul_mem h2y hpS), ?_, ?_⟩
    · rw [show y - (y + y - 1) * (y * y - y) - x = (y - x) - (y + y - 1) * (y * y - y) by ring]
      exact sub_mem hyx (Submodule.smul_mono_left hle (mul_left_mem S _ h2y hyy))
    · have h4 : (y * y - y) + (y * y - y) + (y * y - y) + (y * y - y) - 1 - 1 - 1 ∈ S :=
        S.sub_mem (S.sub_mem (S.sub_mem (S.add_mem (S.add_mem (S.add_mem hpS hpS) hpS) hpS)
          S.one_mem) S.one_mem) S.one_mem
      have hsq := mul_mem_mul S _ _ hyy hyy
      rw [← pow_add, ← two_mul, ← pow_succ'] at hsq
      have := mul_right_mem S _ h4 hsq
      convert this using 1
      ring

theorem LZIdemPow_of : LateralTheory.E.LZIdemSumNoetherian.LZIdemPow := by
  intro A _ _ K _ _ B C t hc e f hp k
  obtain ⟨he, hf, hee, hff, hef⟩ := hp
  obtain ⟨b, hb, hbe, hbb⟩ := lift_pow B e he hee (k + 1)
  obtain ⟨c, hcC, hcf, hcc⟩ := lift_pow C f hf hff (k + 1)
  have hBD : B ≤ AdjoinInv B t := fun x hx => Algebra.subset_adjoin (Or.inl hx)
  have hCD : C ≤ AdjoinInv B t := by
    intro x hx; rw [hc.glue]; exact Algebra.subset_adjoin (Or.inl hx)
  have hbD : b ∈ AdjoinInv B t := hBD hb
  have hcD : c ∈ AdjoinInv B t := hCD hcC
  have hmono : ∀ (I : Ideal A) (S : Subalgebra A K), S ≤ AdjoinInv B t → ∀ x,
      x ∈ I • Subalgebra.toSubmodule S → x ∈ I • Subalgebra.toSubmodule (AdjoinInv B t) :=
    fun I S h x hx => Submodule.smul_mono (le_refl I) (fun y hy => h hy) hx
  have hpow : IsLocalRing.maximalIdeal A ^ (2 ^ (k + 1)) ≤ IsLocalRing.maximalIdeal A ^ (k + 1) :=
    Ideal.pow_le_pow_right (Nat.lt_two_pow_self).le
  have hp : b * b - b ∈ (IsLocalRing.maximalIdeal A ^ (k + 1)) • Subalgebra.toSubmodule (AdjoinInv B t) :=
    Submodule.smul_mono_left hpow (hmono _ B hBD _ hbb)
  have hq : c * c - c ∈ (IsLocalRing.maximalIdeal A ^ (k + 1)) • Subalgebra.toSubmodule (AdjoinInv B t) :=
    Submodule.smul_mono_left hpow (hmono _ C hCD _ hcc)
  have hd1 : b - c ∈ (IsLocalRing.maximalIdeal A ^ 1) • Subalgebra.toSubmodule (AdjoinInv B t) := by
    rw [pow_one, show b - c = (b - e) + (e - f) - (c - f) by ring]
    exact sub_mem (add_mem (hmono _ B hBD _ hbe) hef) (hmono _ C hCD _ hcf)
  have hcube : (b - c) * (b - c) * (b - c) - (b - c) ∈
      (IsLocalRing.maximalIdeal A ^ (k + 1)) • Subalgebra.toSubmodule (AdjoinInv B t) := by
    rw [show (b - c) * (b - c) * (b - c) - (b - c) = (b * b - b) - (c * c - c) - (c + c) * (b * b - b)
      + (b + b) * (c * c - c) + (b - c) * (b * b - b) + (b - c) * (c * c - c) by ring]
    have hbc : b - c ∈ AdjoinInv B t := (AdjoinInv B t).sub_mem hbD hcD
    refine add_mem (add_mem (add_mem (sub_mem (sub_mem hp hq) ?_) ?_) ?_) ?_
    · exact mul_left_mem _ _ ((AdjoinInv B t).add_mem hcD hcD) hp
    · exact mul_left_mem _ _ ((AdjoinInv B t).add_mem hbD hbD) hq
    · exact mul_left_mem _ _ hbc hp
    · exact mul_left_mem _ _ hbc hq
  have key : ∀ j, j + 1 ≤ k + 1 →
      b - c ∈ (IsLocalRing.maximalIdeal A ^ (j + 1)) • Subalgebra.toSubmodule (AdjoinInv B t) := by
    intro j
    induction j with
    | zero => intro _; simpa using hd1
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have h3 := mul_mem_mul _ _ _ (mul_mem_mul _ _ _ h1 h1) h1
      rw [← pow_add, ← pow_add] at h3
      have h3' := Submodule.smul_mono_left (Ideal.pow_le_pow_right (show j + 1 + 1 ≤ j + 1 + (j + 1) + (j + 1) by omega)) h3
      have hc' := Submodule.smul_mono_left (Ideal.pow_le_pow_right hj) hcube
      rw [show b - c = (b - c) * (b - c) * (b - c) - ((b - c) * (b - c) * (b - c) - (b - c)) by ring]
      exact sub_mem h3' hc'
  refine ⟨b, hb, c, hcC, ?_, hcf, ?_⟩
  · rw [← neg_sub]; exact neg_mem hbe
  · exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega)) (key k le_rfl)

end LateralTheory.E.LZIdemPowProof
end
end
