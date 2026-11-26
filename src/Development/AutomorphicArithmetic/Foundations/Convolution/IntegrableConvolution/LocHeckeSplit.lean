module

public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.MatchProd

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.SphLaws
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.SphIso
noncomputable section

open MeasureTheory ValuativeRel
open GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.Spherical
open GroundTheory.Automorphic.HeckeAlgebra

namespace UpperTheory.ConvolutionTheory.L1

variable {F F' : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field F'] [ValuativeRel F'] [TopologicalSpace F'] [IsNonarchimedeanLocalField F']

def intEquiv (c : F ≃+* F') (hv : ∀ x, c x ∈ 𝒪[F'] ↔ x ∈ 𝒪[F]) : 𝒪[F] ≃+* 𝒪[F'] where
  toFun x := ⟨c x, (hv x).2 x.2⟩
  invFun y := ⟨c.symm y, (hv _).1 (by simpa using y.2)⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

theorem qF_eq_of_iso (c : F ≃+* F') (hv : ∀ x, c x ∈ 𝒪[F'] ↔ x ∈ 𝒪[F]) : qF F' = qF F :=
  (Nat.card_congr (IsLocalRing.ResidueField.mapEquiv (intEquiv c hv)).toEquiv).symm

theorem exists_unit_uniformizer (c : F ≃+* F') (hv : ∀ x, c x ∈ 𝒪[F'] ↔ x ∈ 𝒪[F]) :
    ∃ u : (𝒪[F'])ˣ, c (uniformizer F : F) = (uniformizer F' : F') * ((u : 𝒪[F']) : F') := by
  have h1 : Irreducible (intEquiv c hv (uniformizer F)) :=
    (MulEquiv.irreducible_iff (intEquiv c hv)).2 (irreducible_uniformizer F)
  obtain ⟨u, hu⟩ := IsDiscreteValuationRing.associated_of_irreducible _ (irreducible_uniformizer F') h1
  exact ⟨u, (congrArg Subtype.val hu).symm⟩

abbrev mapIso (c : F ≃+* F') (n : ℕ) : GL (Fin n) F →* GL (Fin n) F' :=
  Matrix.GeneralLinearGroup.map (c : F →+* F')

variable {n : ℕ}

theorem mapIso_mem_unipotent (c : F ≃+* F') {g : GL (Fin n) F} (hg : g ∈ unipotent F n) :
    mapIso c n g ∈ unipotent F' n := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · change c ((g : Matrix (Fin n) (Fin n) F) i j) = 0
    rw [hg.1 hij, map_zero]
  · change c (g i i) = 1
    rw [hg.2 i, map_one]

theorem mapIso_mem_integralGL (c : F ≃+* F') (hv : ∀ x, c x ∈ 𝒪[F'] ↔ x ∈ 𝒪[F]) {g : GL (Fin n) F}
    (hg : g ∈ integralGL F n) : mapIso c n g ∈ integralGL F' n := by
  rw [mem_integralGL_iff] at hg ⊢
  refine ⟨fun i j => (hv _).2 (hg.1 i j), fun i j => ?_⟩
  rw [← map_inv]
  exact (hv _).2 (hg.2 i j)

theorem mapIso_torusPow (c : F ≃+* F') (hv : ∀ x, c x ∈ 𝒪[F'] ↔ x ∈ 𝒪[F]) (l : Fin n → ℤ) :
    ∃ k ∈ integralGL F' n, mapIso c n (torusPow F n l) = torusPow F' n l * k := by
  obtain ⟨u, hu⟩ := exists_unit_uniformizer c hv
  refine ⟨diagGL F' n fun i => Units.map (𝒪[F']).subtype.toMonoidHom (u ^ l i),
    diagGL_map_mem_integralGL F' n _, Units.ext (Matrix.ext fun i j => ?_)⟩
  change c (((torusPow F n l : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j) = _
  rw [Units.val_mul, coe_torusPow, coe_torusPow, coe_diagGL, Matrix.diagonal_mul_diagonal]
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.diagonal_apply_eq, map_zpow₀, RingEquiv.coe_toRingHom]
    rw [hu, mul_zpow]
    simp [Units.val_zpow_eq_zpow_val]
  · simp [Matrix.diagonal_apply_ne _ hij]

theorem iwasawaExponent_mapIso (c : F ≃+* F') (hv : ∀ x, c x ∈ 𝒪[F'] ↔ x ∈ 𝒪[F]) (g : GL (Fin n) F) :
    iwasawaExponent F' n (mapIso c n g) = iwasawaExponent F n g := by
  obtain ⟨u, hu, k, hk, h⟩ := exists_eq_mul_torusPow_iwasawaExponent F n g
  set l := iwasawaExponent F n g
  obtain ⟨k', hk', ht⟩ := mapIso_torusPow c hv l
  rw [h, map_mul, map_mul, ht,
    show mapIso c n u * (torusPow F' n l * k') * mapIso c n k = mapIso c n u * torusPow F' n l * (k' * mapIso c n k) by group]
  exact iwasawaExponent_eq F' n (mapIso_mem_unipotent c hu)
    ((integralGL F' n).mul_mem hk' (mapIso_mem_integralGL c hv hk))

theorem normalize_congr (hq : qF F' = qF F) (p : LaurentRing n) : normalize F' n p = normalize F n p := by
  apply AddMonoidAlgebra.coeff_injective
  ext l
  rw [coeff_normalize, coeff_normalize, halfModulus_eq, halfModulus_eq, sqrtQ, sqrtQ, hq]

section Transport

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  [MeasurableSpace (GL (Fin n) F')] [BorelSpace (GL (Fin n) F')]
  {m : Measure (GL (Fin n) F)} [m.IsHaarMeasure] {m' : Measure (GL (Fin n) F')} [m'.IsHaarMeasure]

private def cosetMap (e : GL (Fin n) F ≃* GL (Fin n) F') (y : GL (Fin n) F' ⧸ integralGL F' n) :
    GL (Fin n) F ⧸ integralGL F n :=
  QuotientGroup.mk (e.symm y.out)

private theorem cosetMap_injective (e : GL (Fin n) F ≃* GL (Fin n) F')
    (hK : ∀ g, e g ∈ integralGL F' n ↔ g ∈ integralGL F n) : Function.Injective (cosetMap e) := by
  intro y y' h
  have h1 := QuotientGroup.eq.1 h
  rw [← hK, map_mul, map_inv, e.apply_symm_apply, e.apply_symm_apply] at h1
  rw [← QuotientGroup.out_eq' y, ← QuotientGroup.out_eq' y']
  exact QuotientGroup.eq.2 h1

private theorem cosetMap_surjective (e : GL (Fin n) F ≃* GL (Fin n) F')
    (hK : ∀ g, e g ∈ integralGL F' n ↔ g ∈ integralGL F n) : Function.Surjective (cosetMap e) := by
  intro x
  refine ⟨QuotientGroup.mk (e x.out), ?_⟩
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (integralGL F' n) (e x.out)
  have hk2 : e.symm (k : GL (Fin n) F') ∈ integralGL F n := (hK _).1 (by simpa using k.2)
  rw [cosetMap, hk, map_mul, e.symm_apply_apply, QuotientGroup.mk_mul_of_mem _ hk2, QuotientGroup.out_eq']

theorem satake_transport (e : GL (Fin n) F ≃* GL (Fin n) F')
    (hK : ∀ g, e g ∈ integralGL F' n ↔ g ∈ integralGL F n)
    (hl : ∀ g, iwasawaExponent F' n (e g) = iwasawaExponent F n g)
    (hm : m.real (integralGL F n : Set (GL (Fin n) F)) = m'.real (integralGL F' n : Set (GL (Fin n) F')))
    (H : SphericalHecke m (F := F) (n := n)) (H' : SphericalHecke m' (F := F') (n := n))
    (hH : ∀ g, (H : HeckeAlgebra m) g = (H' : HeckeAlgebra m') (e g)) : satake m H = satake m' H' := by
  classical
  have key : ∀ y : GL (Fin n) F' ⧸ integralGL F' n, ∃ k ∈ integralGL F n,
      (cosetMap e y).out = e.symm y.out * k := fun y => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (integralGL F n) (e.symm y.out)
    exact ⟨k, k.2, hk⟩
  have hval : ∀ y, (H : HeckeAlgebra m) (cosetMap e y).out = (H' : HeckeAlgebra m') y.out := fun y => by
    obtain ⟨k, hk, h⟩ := key y
    rw [h, (HeckeAlgebraLevel.val_mem _ _ H k hk _).2, hH, e.apply_symm_apply]
  have hexp : ∀ y, iwasawaExponent F n (cosetMap e y).out = iwasawaExponent F' n y.out := fun y => by
    obtain ⟨k, hk, h⟩ := key y
    rw [h, iwasawaExponent_mul_of_mem_integralGL F n _ hk, ← hl, e.apply_symm_apply]
  rw [satake_eq_sum H ((cosetSupport H').image (cosetMap e)) ?_, satake, hm,
    Finset.sum_image (cosetMap_injective e hK).injOn]
  · simp only [hval, hexp]
  · intro x hx
    obtain ⟨y, rfl⟩ := cosetMap_surjective e hK x
    rw [hval]
    exact apply_out_eq_zero fun hy => hx (Finset.mem_image_of_mem _ hy)

theorem satakeTransform_transport (e : GL (Fin n) F ≃* GL (Fin n) F')
    (hK : ∀ g, e g ∈ integralGL F' n ↔ g ∈ integralGL F n)
    (hl : ∀ g, iwasawaExponent F' n (e g) = iwasawaExponent F n g) (hq : qF F' = qF F)
    (hm : m.real (integralGL F n : Set (GL (Fin n) F)) = m'.real (integralGL F' n : Set (GL (Fin n) F')))
    (H : SphericalHecke m (F := F) (n := n)) (H' : SphericalHecke m' (F := F') (n := n))
    (hH : ∀ g, (H : HeckeAlgebra m) g = (H' : HeckeAlgebra m') (e g)) :
    satakeTransform m H = satakeTransform m' H' := by
  rw [satakeTransform_apply, satakeTransform_apply, satake_transport e hK hl hm H H' hH, normalize_congr hq]

end Transport

theorem exists_transport [MeasurableSpace (GL (Fin n) F')] [BorelSpace (GL (Fin n) F')]
    {m' : Measure (GL (Fin n) F')} [m'.IsHaarMeasure] (e : GL (Fin n) F ≃ₜ* GL (Fin n) F')
    (hK : ∀ g, e g ∈ integralGL F' n ↔ g ∈ integralGL F n)
    (hl : ∀ g, iwasawaExponent F' n (e g) = iwasawaExponent F n g) (hq : qF F' = qF F)
    (h1 : m' (integralGL F' n : Set (GL (Fin n) F')) = 1) (H' : SphericalHecke m' (F := F') (n := n)) :
    ∃ (_ : MeasurableSpace (GL (Fin n) F)) (_ : BorelSpace (GL (Fin n) F))
      (m : Measure (GL (Fin n) F)) (_ : m.IsHaarMeasure), m (integralGL F n : Set (GL (Fin n) F)) = 1 ∧
      ∃ H : SphericalHecke m (F := F) (n := n), (∀ x, (H : HeckeAlgebra m) x = (H' : HeckeAlgebra m') (e x)) ∧
        satakeTransform m H = satakeTransform m' H' := by
  borelize (GL (Fin n) F)
  let m : Measure (GL (Fin n) F) := Measure.map e.symm m'
  haveI hm : m.IsHaarMeasure := (e.symm.toMulEquiv).isHaarMeasure_map m' e.symm.continuous e.continuous
  have hset : (e.symm ⁻¹' (integralGL F n : Set (GL (Fin n) F))) = (integralGL F' n : Set (GL (Fin n) F')) := by
    ext x
    simp only [Set.mem_preimage, SetLike.mem_coe]
    rw [← hK, e.apply_symm_apply]
  have hmK : m (integralGL F n : Set (GL (Fin n) F)) = m' (integralGL F' n : Set (GL (Fin n) F')) := by
    change Measure.map e.symm m' _ = _
    rw [Measure.map_apply (map_continuous e.symm).measurable (isOpen_integralGL F n).measurableSet, hset]
  let f : HeckeAlgebra m := HeckeAlgebra.mk m (fun x => (H' : HeckeAlgebra m') (e x))
    ⟨(H' : HeckeAlgebra m').mem.1.comp_continuous e.continuous,
      (H' : HeckeAlgebra m').mem.2.comp_homeomorph e.toHomeomorph⟩
  have hf : f ∈ biInvariant m (integralGL F n) := fun k hk x => by
    have hk' := (hK k).2 hk
    exact ⟨by
      change (H' : HeckeAlgebra m') (e (k * x)) = (H' : HeckeAlgebra m') (e x)
      rw [map_mul]
      exact (HeckeAlgebraLevel.val_mem _ _ H' _ hk' _).1, by
      change (H' : HeckeAlgebra m') (e (x * k)) = (H' : HeckeAlgebra m') (e x)
      rw [map_mul]
      exact (HeckeAlgebraLevel.val_mem _ _ H' _ hk' _).2⟩
  refine ⟨_, inferInstance, m, hm, hmK.trans h1, HeckeAlgebraLevel.mk _ _ f hf, fun _ => rfl, ?_⟩
  exact satakeTransform_transport e.toMulEquiv hK hl hq (by simp [Measure.real, hmK]) _ H' fun _ => rfl

end UpperTheory.ConvolutionTheory.L1
end
end

open MeasureTheory NumberField IsDedekindDomain ValuativeRel
open GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Global GroundTheory.Global.SemiLocal PositivityTheory.Rg.Tf.Geo

namespace UpperTheory.ConvolutionTheory.L1

private theorem haar_uniq {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {K : Set G} {m m' : Measure G}
    (hm : m.IsHaarMeasure) (hm' : m'.IsHaarMeasure) (h : m K = 1) (h' : m' K = 1) : m = m' := by
  have e := Measure.isMulLeftInvariant_eq_smul m m'
  have e2 : m K = (Measure.haarScalarFactor m m' • m') K := by rw [← e]
  rw [h, Measure.smul_apply, h', ENNReal.smul_def, smul_eq_mul, mul_one] at e2
  have e3 : Measure.haarScalarFactor m m' = 1 := by exact_mod_cast e2.symm
  rw [e3, one_smul] at e
  exact e

private theorem gl_sc (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [SecondCountableTopology R] (n : ℕ) : SecondCountableTopology (GL (Fin n) R) := by
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) R) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → R))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

variable {K : Type} [Field K] [NumberField K] {n : ℕ} {v : HeightOneSpectrum (𝓞 K)}

private theorem sph_at [ms : MeasurableSpace (GL (Fin n) (v.adicCompletion K))]
    [bs : BorelSpace (GL (Fin n) (v.adicCompletion K))] (m : Measure (GL (Fin n) (v.adicCompletion K)))
    (hm : m.IsHaarMeasure) (h1 : m (GLnLocal.integralGL (v.adicCompletion K) n) = 1)
    {p : MvPolynomial (Fin n) ℂ} {h : GL (Fin n) (v.adicCompletion K) → ℂ} (hs : GM.IsSph v p h) :
    ∃ H : SphericalHecke m (F := v.adicCompletion K) (n := n), (∀ x, (H : HeckeAlgebra m) x = h x) ∧
      satakeTransform m H = polyEmb (n := n) (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1)) p) := by
  obtain ⟨ms', bs', m', hm', h1', H, hH, S⟩ := hs
  obtain rfl : ms' = ms := bs'.measurable_eq.trans bs.measurable_eq.symm
  haveI := gl_sc (v.adicCompletion K) n
  obtain rfl := haar_uniq hm hm' h1 h1'
  exact ⟨H, hH, S⟩

end UpperTheory.ConvolutionTheory.L1

open UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.sphLaws :
    UpperTheory.ConvolutionTheory.L1.SphLaws := by
  refine ⟨?_, fun K _ _ n v => ⟨?_, ?_, ?_⟩⟩
  · intro F E _ _ _ _ _ v w hs n p h hsph
    obtain ⟨ms, bs, m, hm, hk, H, hH, S⟩ := hsph
    obtain ⟨⟨e, he⟩, hint, -, -, -⟩ := UpperTheory.ConvolutionTheory.L1.splitLoc F E v w hs n
    let c : v.adicCompletion F ≃+* w.1.adicCompletion E :=
      RingEquiv.ofBijective (completionMap v w.1) ⟨(completionMap v w.1).injective, hs⟩
    have he0 : w.1.asIdeal.ramificationIdx (𝓞 F) ≠ 0 := (Ideal.ramificationIdx_pos (R := 𝓞 F) w.1.asIdeal).ne'
    have hv : ∀ x, c x ∈ 𝒪[w.1.adicCompletion E] ↔ x ∈ 𝒪[v.adicCompletion F] := fun x => by
      have h1 : ∀ y : w.1.adicCompletion E, y ∈ 𝒪[w.1.adicCompletion E] ↔ Valued.v y ≤ 1 := fun y => by
        have := ValuativeRel.isEquiv (valuation (w.1.adicCompletion E)) Valued.v y 1
        rw [map_one, map_one] at this
        exact (Valuation.mem_integer_iff _ _).trans this
      have h2 : ∀ y : v.adicCompletion F, y ∈ 𝒪[v.adicCompletion F] ↔ Valued.v y ≤ 1 := fun y => by
        have := ValuativeRel.isEquiv (valuation (v.adicCompletion F)) Valued.v y 1
        rw [map_one, map_one] at this
        exact (Valuation.mem_integer_iff _ _).trans this
      rw [h1, h2]
      change Valued.v (completionMap v w.1 x) ≤ 1 ↔ _
      rw [valued_completionMap]
      exact pow_le_one_iff_of_nonneg zero_le he0
    have hee : ∀ g, e g = mapIso c n g := fun g => he g
    obtain ⟨ms', bs', m', hm', h1, H', hH', S'⟩ := exists_transport e (fun g => by rw [he]; exact hint g)
      (fun g => by rw [hee]; exact iwasawaExponent_mapIso c hv g) (qF_eq_of_iso c hv) hk H
    exact ⟨ms', bs', m', hm', h1, H', fun x => (hH' x).trans ((hH _).trans (by rw [he])), S'.trans S⟩
  · rintro p h ⟨_, _, m, _, -, H, hH, -⟩
    obtain rfl : (fun x => (H : HeckeAlgebra m) x) = h := funext hH
    exact ⟨(H : HeckeAlgebra m).mem.1.continuous, (H : HeckeAlgebra m).mem.2⟩
  · intro p h h' hs hs'
    obtain ⟨ms, bs, m, hm, h1, H, hH, S⟩ := id hs
    obtain ⟨H', hH', S'⟩ := sph_at m hm h1 hs'
    obtain rfl := satakeTransform_injective (S.trans S'.symm)
    exact funext fun x => (hH x).symm.trans (hH' x)
  · intro _ _ m hm h1 p p' h h' hs hs'
    obtain ⟨H, hH, S⟩ := sph_at m hm h1 hs
    obtain ⟨H', hH', S'⟩ := sph_at m hm h1 hs'
    refine ⟨_, inferInstance, m, hm, h1, H * H', fun x => ?_, ?_⟩
    · change ∫ y, (H : HeckeAlgebra m) y * (H' : HeckeAlgebra m) (y⁻¹ * x) ∂m = _
      simp only [hH, hH']
      rfl
    · rw [map_mul, S, S', map_mul, map_mul]
end

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Geo

namespace UpperTheory.ConvolutionTheory.L1

private theorem isSph_cvAll {K : Type} [Field K] [NumberField K] {n : ℕ} {v : Pl K}
    [MeasurableSpace (GL (Fin n) (v.adicCompletion K))] [BorelSpace (GL (Fin n) (v.adicCompletion K))]
    (mF : Measure (GL (Fin n) (v.adicCompletion K))) (hH : mF.IsHaarMeasure)
    (h1 : mF (GLnLocal.integralGL (v.adicCompletion K) n) = 1) :
    ∀ (m : ℕ) (p : Fin (m + 1) → MvPolynomial (Fin n) ℂ) (φ : Fin (m + 1) → GL (Fin n) (v.adicCompletion K) → ℂ),
      (∀ i, GM.IsSph v (p i) (φ i)) → GM.IsSph v (∏ i, p i) (cvAll mF m φ)
  | 0, p, φ, h => by simpa [cvAll] using h 0
  | m + 1, p, φ, h => by
    rw [Fin.prod_univ_succ]
    exact (sphLaws.2 K n v).2.2 mF hH h1 _ _ _ _ (h 0)
      (isSph_cvAll mF hH h1 m (Fin.tail p) (Fin.tail φ) fun i => h i.succ)

end UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.locHeckeSplit :
    UpperTheory.ConvolutionTheory.GM.LocHeckeSplit := by
  intro F E _ _ _ _ _ _ σ hσ hp n hn v hv p h f hh hf
  obtain ⟨m, hm⟩ : ∃ m, Module.finrank F E = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hp.pos).symm⟩
  obtain ⟨w₀⟩ := nonempty_placesOver E v
  obtain ⟨w, -, hM⟩ := UpperTheory.ConvolutionTheory.L1.matchProd F E σ hσ m hm n v w₀ hv
  intro _ _ _ _ mE mF hE hF h1E h1F
  have hc : ∀ u : PlacesOver E v, Continuous (h u) ∧ HasCompactSupport (h u) :=
    fun u => (UpperTheory.ConvolutionTheory.L1.sphLaws.2 E n u.1).1 _ _ (hh u)
  have hm' := hM h hc mF hF h1F
  have hs := UpperTheory.ConvolutionTheory.L1.isSph_cvAll mF hF h1F m (fun i => p (w i))
    (fun i g => h (w i) (mapGL n (completionMap v (w i).1) g))
    (fun i => UpperTheory.ConvolutionTheory.L1.sphLaws.1 F E v (w i) (hv (w i)) n _ _ (hh (w i)))
  have hprod : (∏ i, p (w i)) = ∏ᶠ u, p u := by
    rw [finprod_eq_prod_of_fintype]
    exact Equiv.prod_comp w p
  rw [hprod] at hs
  have key := (UpperTheory.ConvolutionTheory.L1.sphLaws.2 F n v).2.1 _ _ _ hs hf
  rw [key] at hm'
  exact hm' mE mF hE hF h1E h1F
