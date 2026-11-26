module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsExtensionAllModelsUniformized
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTraceOrthogonality
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralScalarOfPulledBackGeneratorExtendsModel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModuliPointIntegralFrameAfterFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaTraceBaseChangeIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumSymmetricTranslatesThetaPullbackExtends
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicityMapEqZeroOfTranslatedEvaluationAeZer
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsPureTensors
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralInverseAtSplitPlacesOfUnits

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralIff
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

set_option autoImplicit false

namespace GlobalTheory.IntegralData

theorem integralIff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), IntegralIffSt Xo c := by
  intro E _ _ _ H Dw l Xo c T io y
  constructor
  · rintro ⟨G, t', m1, m2, ⟨ub, h1, h2, h3, h4⟩, θ, h5, w1, w2, σ, s1, θ2, r1, r2, a1, a2, p, g⟩
    exact ⟨⟨G, t', m1, m2, ub, h1, h2, h3, h4, θ, h5, w1, w2, σ, s1, θ2, r1, r2, a1, a2, p, g⟩⟩
  · rintro ⟨⟨G, t', m1, m2, ub, h1, h2, h3, h4, θ, h5, w1, w2, σ, s1, θ2, r1, r2, a1, a2, p, g⟩⟩
    exact ⟨G, t', m1, m2, ⟨ub, h1, h2, h3, h4⟩, θ, h5, w1, w2, σ, s1, θ2, r1, r2, a1, a2, p, g⟩

end GlobalTheory.IntegralData
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTraceIsTranslSum
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTraceIsTranslSum
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkIntegral

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {K : Type} [CommRing K]

theorem conj_pullback_map (x : Sp K ⟶ Xo.X) (g : Xo.univ.t.G ⟶ Xo.univ.t.G) :
    conj x x ((Over.pullback x).map g).left =
      (lift (fst (Over.mk x) Xo.univ.t.G) (snd (Over.mk x) Xo.univ.t.G ≫ g)).left := by
  refine gx_ext ?_ ?_
  · rw [lift_l_fst]
    exact (over_iff _).2 (pullback.lift_snd _ _ _)
  · rw [lift_l_snd, conj_apply, Category.assoc, Category.assoc, swap_inv_snd, Over.comp_left, ← swap_hom_fst,
      Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)

theorem conj_comp_left {x x' x'' : Sp K ⟶ Xo.X} (f : Fib Xo x ⟶ Fib Xo x') (g : Fib Xo x' ⟶ Fib Xo x'') :
    conj x x'' (f ≫ g).left = conj x x' f.left ≫ conj x' x'' g.left := by
  simp only [conj_apply, Category.assoc, Iso.inv_hom_id_assoc]
  rw [Over.comp_left]
  simp only [Category.assoc]

theorem conj_id_pow (x : Sp K ⟶ Xo.X) (n : ℕ) :
    conj x x (𝟙 (Fib Xo x) ^ n).left = (mulT Xo.univ.t.G (Over.mk x) n).left := by
  have e : (Over.pullback x).map (𝟙 Xo.univ.t.G ^ n) = 𝟙 (Fib Xo x) ^ n := by
    have := map_pow (Over.pullback x).homMonoidHom (𝟙 Xo.univ.t.G) n
    rw [← (Over.pullback x).map_id]
    exact this
  rw [← e, conj_pullback_map, MonObj.comp_pow, Category.comp_id, mulT]

theorem conj_id_inv (x : Sp K ⟶ Xo.X) :
    conj x x (𝟙 (Fib Xo x))⁻¹.left = (negT Xo.univ.t.G (Over.mk x)).left := by
  have e : (Over.pullback x).map (𝟙 Xo.univ.t.G)⁻¹ = (𝟙 (Fib Xo x))⁻¹ := by
    rw [Functor.map_inv', CategoryTheory.Functor.map_id]
  rw [← e, conj_pullback_map, GrpObj.comp_inv, Category.comp_id, negT]
  rfl

theorem negT_comm_conj {x x' : Sp K ⟶ Xo.X} (f : Fib Xo x ⟶ Fib Xo x') [IsMonHom f] :
    (negT Xo.univ.t.G (Over.mk x)).left ≫ conj x x' f.left =
      conj x x' f.left ≫ (negT Xo.univ.t.G (Over.mk x')).left := by
  rw [← conj_id_inv, ← conj_id_inv, ← conj_comp_left, ← conj_comp_left, GrpObj.inv_comp, GrpObj.comp_inv,
    Category.id_comp, Category.comp_id]

theorem pow_eq_one_of_mem_transKer_conj {x x' : Sp K ⟶ Xo.X} {f : Fib Xo x ⟶ Fib Xo x'} {f' : Fib Xo x' ⟶ Fib Xo x}
    {n : ℕ} (h : f ≫ f' = 𝟙 _ ^ n) {c : Over.mk x ⟶ Xo.univ.t.G} (hc : c ∈ transKer Xo.univ.t.G (conj x x' f.left)) :
    c ^ n = 1 := by
  rw [← mem_transKer_mulT, mem_transKer, ← conj_id_pow, ← h, conj_comp_left, ← Category.assoc, mem_transKer.1 hc]

theorem thetaTrace_isTranslSum (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x x' : Sp K ⟶ Xo.X) (f : Fib Xo x ⟶ Fib Xo x')
    (f' : Fib Xo x' ⟶ Fib Xo x) (p : ℕ) (s : LB.Sec (PPx x)) (s₀ s' : LB.Sec (PPx x')) (a : K)
    (hf : IsPair (p ^ 2) f f') (hs' : ∀ i, s'.f i = scal x' a i * s₀.f i)
    (h : IsThetaTrace Xo.univ.t.G Xo.univ.t.PP (conj x x' f.left) p s s') :
    ∃ t, IsPullOf p f a s₀ t ∧ IsTranslSum p s t := by
  obtain ⟨β, s₁, t, n, U, F, hβ, hs, ht, hr, hU, hF, hsum⟩ := h
  have := hf.1
  refine ⟨t, ⟨β, s', hβ, hs', ht⟩, n, F, fun i => ?_, hsum⟩
  have hk : (U i).pt ^ (p ^ 2) = 1 := pow_eq_one_of_mem_transKer_conj hf.2.2.1 (hU i).1
  obtain ⟨α₀, α, h₁, h₂, h₃, h₄⟩ := hs
  exact ⟨_, (U i).pt, α₀, α, s₁, U i, rfl, hk, h₁, h₂, h₃, h₄,
    (hU i).symLift hβ.2.1 Xo.univ.t.sym (negT_comm_conj f) hk, hF i⟩

end GlobalTheory.HkIntegral
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTraceIsTranslSumStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pull_isTranslSum_of_isThetaTrace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x x' : Sp K ⟶ Xo.X) (f : Fib Xo x ⟶ Fib Xo x') (f' : Fib Xo x' ⟶ Fib Xo x) (p : ℕ) (s : LB.Sec (PPx x)) (s₀ s' : LB.Sec (PPx x')) (a : K), IsPair (p ^ 2) f f' → (∀ i, s'.f i = scal x' a i * s₀.f i) → IsThetaTrace Xo.univ.t.G Xo.univ.t.PP (conj x x' f.left) p s s' → ∃ t, IsPullOf p f a s₀ t ∧ IsTranslSum p s t := by
  first | exact @GlobalTheory.HkIntegral.thetaTrace_isTranslSum | exact GlobalTheory.HkIntegral.thetaTrace_isTranslSum | (intros; apply GlobalTheory.HkIntegral.thetaTrace_isTranslSum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAndIntegralStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringHom_finite_and_isIntegral_of_valuation_scaled : ∀ (T T' : CDVR) (i : T.Fr →+* T'.Fr) (r : ℕ), 0 < r → (∀ a : T.Fr, vV T'.V (i a) = (r : ℤ) * vV T.V a) → T'.FinRes → i.Finite ∧ ∀ b : T'.V, (i.comp (algebraMap T.V T.Fr)).IsIntegralElem (algebraMap T'.V T'.Fr b) := by
  first | exact @GlobalTheory.CompleteValExt.finite_and_integral | exact GlobalTheory.CompleteValExt.finite_and_integral | (intros; apply GlobalTheory.CompleteValExt.finite_and_integral <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FibreIsogenyPairDefinedOverFiniteSubextension
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FibreIsogenyPairDefinedOverFiniteSubextension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkIntegral

open GlobalTheory.Spread

theorem fibre_transition {G X : Scheme.{0}} (p : G ⟶ X) {K L : Type} [Field K] [Field L] [Algebra K L]
    (M : IntermediateField K L) (x : Sp K ⟶ X)
    (π : pullback p (spMap (algebraMap K L) ≫ x) ⟶ pullback p (spMap (algebraMap K M) ≫ x))
    (h₁ : π ≫ pullback.fst _ _ = pullback.fst _ _)
    (h₂ : π ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap M.val.toRingHom) :
    (pullbackLeftPullbackSndIso p x (spMap (algebraMap K L))).hom ≫ π =
      bcMap (pullback.snd p x) M.val ≫ (pullbackLeftPullbackSndIso p x (spMap (algebraMap K M))).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, h₁, Category.assoc, pullbackLeftPullbackSndIso_hom_fst,
      pullbackLeftPullbackSndIso_hom_fst, bcMap_fst_assoc]
  · rw [Category.assoc, h₂, Category.assoc, pullbackLeftPullbackSndIso_hom_snd,
      pullbackLeftPullbackSndIso_hom_snd_assoc, bcMap_snd]

theorem exists_descend_fibre {G X : Scheme.{0}} (p : G ⟶ X) [QuasiCompact p] [QuasiSeparated p]
    [LocallyOfFinitePresentation p] {K L : Type} [Field K] [Field L] [Algebra K L] (x x' : Sp K ⟶ X)
    (g : pullback p (spMap (algebraMap K L) ≫ x) ⟶ pullback p (spMap (algebraMap K L) ≫ x'))
    (hg : g ≫ pullback.snd _ _ = pullback.snd _ _) :
    ∃ s : Finset L, ∀ M : IntermediateField K L, (s : Set L) ⊆ M →
      ∃ f : pullback p (spMap (algebraMap K M) ≫ x) ⟶ pullback p (spMap (algebraMap K M) ≫ x'),
        f ≫ pullback.snd _ _ = pullback.snd _ _ ∧
        ∀ (π : pullback p (spMap (algebraMap K L) ≫ x) ⟶ pullback p (spMap (algebraMap K M) ≫ x))
          (π' : pullback p (spMap (algebraMap K L) ≫ x') ⟶ pullback p (spMap (algebraMap K M) ≫ x')),
          π ≫ pullback.fst _ _ = pullback.fst _ _ →
          π ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap M.val.toRingHom →
          π' ≫ pullback.fst _ _ = pullback.fst _ _ →
          π' ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap M.val.toRingHom →
          g ≫ π' = π ≫ f := by
  let A : Over (Sp K) := Over.mk (pullback.snd p x)
  let B : Over (Sp K) := Over.mk (pullback.snd p x')
  have : QuasiCompact A.hom := inferInstanceAs (QuasiCompact (pullback.snd p x))
  have : QuasiSeparated A.hom := inferInstanceAs (QuasiSeparated (pullback.snd p x))
  have : LocallyOfFinitePresentation B.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd p x'))
  let g₀ : pullback (pullback.snd p x) (spMap (algebraMap K L)) ⟶
      pullback (pullback.snd p x') (spMap (algebraMap K L)) :=
    (pullbackLeftPullbackSndIso p x (spMap (algebraMap K L))).hom ≫ g ≫
      (pullbackLeftPullbackSndIso p x' (spMap (algebraMap K L))).inv
  have hg₀ : g₀ ≫ pullback.snd _ _ = pullback.snd _ _ := by
    simp only [g₀, Category.assoc, pullbackLeftPullbackSndIso_inv_snd_snd, hg, pullbackLeftPullbackSndIso_hom_snd]
  obtain ⟨s, hs⟩ := HomPairDescent.exists_descend (Ω := L) A B (Over.homMk g₀ hg₀)
  refine ⟨s, fun M hM => ?_⟩
  obtain ⟨f, hf⟩ := hs M hM
  let f₀ : pullback (pullback.snd p x) (spMap (algebraMap K M)) ⟶
      pullback (pullback.snd p x') (spMap (algebraMap K M)) := f.left
  have hf₀ : f₀ ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w f
  have hf₁ : bcMap (pullback.snd p x) M.val ≫ f₀ = g₀ ≫ bcMap (pullback.snd p x') M.val := hf
  refine ⟨(pullbackLeftPullbackSndIso p x (spMap (algebraMap K M))).inv ≫ f₀ ≫
      (pullbackLeftPullbackSndIso p x' (spMap (algebraMap K M))).hom, ?_, fun π π' h₁ h₂ h₃ h₄ => ?_⟩
  · simp only [Category.assoc, pullbackLeftPullbackSndIso_inv_snd_snd, hf₀, pullbackLeftPullbackSndIso_hom_snd]
  · have e := fibre_transition p M x π h₁ h₂
    have e' := fibre_transition p M x' π' h₃ h₄
    rw [← cancel_epi (pullbackLeftPullbackSndIso p x (spMap (algebraMap K L))).hom, reassoc_of% e,
      Iso.hom_inv_id_assoc, reassoc_of% hf₁, ← e']
    simp only [g₀, Category.assoc, Iso.inv_hom_id_assoc]

theorem pair_defined_over_finite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K L : Type) [Field K] [Field L] (φ : K →+* L) (x x' : Sp K ⟶ Xo.X) (w w' : Sp L ⟶ Xo.X) (g : Fib Xo w ⟶ Fib Xo w') (g' : Fib Xo w' ⟶ Fib Xo w), φ.IsIntegral → w = spMap φ ≫ x → w' = spMap φ ≫ x' → IsMonHom g → IsMonHom g' → ∃ (M : Type) (_ : Field M) (i : K →+* M) (j : M →+* L), j.comp i = φ ∧ i.Finite ∧ ∀ v v' : Sp M ⟶ Xo.X, v = spMap i ≫ x → v' = spMap i ≫ x' → ∃ (f : Fib Xo v ⟶ Fib Xo v') (f' : Fib Xo v' ⟶ Fib Xo v), IsBC j f g ∧ IsBC j f' g' := by
  classical
  intro E _ _ _ H Dw l Xo K L _ _ φ x x' w w' g g' hφ hw hw' _ _
  let _ : Algebra K L := φ.toAlgebra
  have hint : Algebra.IsIntegral K L := ⟨hφ⟩
  subst hw hw'
  have hA := ObjDim.isAbelianScheme Xo.univ
  have := hA.proper
  have := hA.smooth
  obtain ⟨s, hs⟩ := exists_descend_fibre Xo.univ.t.G.hom (L := L) x x' g.left (Over.w g)
  obtain ⟨t, ht⟩ := exists_descend_fibre Xo.univ.t.G.hom (L := L) x' x g'.left (Over.w g')
  let M : IntermediateField K L := IntermediateField.adjoin K ((s ∪ t : Finset L) : Set L)
  have hM : ((s ∪ t : Finset L) : Set L) ⊆ M := IntermediateField.subset_adjoin _ _
  obtain ⟨f, hf, hf'⟩ := hs M ((Finset.coe_subset.2 Finset.subset_union_left).trans hM)
  obtain ⟨r, hr, hr'⟩ := ht M ((Finset.coe_subset.2 Finset.subset_union_right).trans hM)
  have hfin : FiniteDimensional K M :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine ⟨M, inferInstance, algebraMap K M, M.val.toRingHom, RingHom.ext fun _ => rfl,
    RingHom.finite_algebraMap.2 hfin, ?_⟩
  rintro v v' rfl rfl
  have e : ∀ y : Sp K ⟶ Xo.X, spMap φ ≫ y = spMap M.val.toRingHom ≫ spMap (algebraMap K M) ≫ y := fun y => by
    rw [← Category.assoc, GlobalTheory.Spread.spMap_algHom_comp]
  exact ⟨Over.homMk f hf, Over.homMk r hr, ⟨e x, e x', hf'⟩, ⟨e x', e x, hr'⟩⟩

end GlobalTheory.HkIntegral
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FibreIsogenyPairDefinedOverFiniteSubextensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibreIsogenyPair_defined_over_finite_subextension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K L : Type) [Field K] [Field L] (φ : K →+* L) (x x' : Sp K ⟶ Xo.X) (w w' : Sp L ⟶ Xo.X) (g : Fib Xo w ⟶ Fib Xo w') (g' : Fib Xo w' ⟶ Fib Xo w), φ.IsIntegral → w = spMap φ ≫ x → w' = spMap φ ≫ x' → IsMonHom g → IsMonHom g' → ∃ (M : Type) (_ : Field M) (i : K →+* M) (j : M →+* L), j.comp i = φ ∧ i.Finite ∧ ∀ v v' : Sp M ⟶ Xo.X, v = spMap i ≫ x → v' = spMap i ≫ x' → ∃ (f : Fib Xo v ⟶ Fib Xo v') (f' : Fib Xo v' ⟶ Fib Xo v), IsBC j f g ∧ IsBC j f' g' := by
  first | exact @GlobalTheory.HkIntegral.pair_defined_over_finite | exact GlobalTheory.HkIntegral.pair_defined_over_finite | (intros; apply GlobalTheory.HkIntegral.pair_defined_over_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieLatticeOnto
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieLatticeOnto
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj hiding smT smT_smT combT kapI isEigV_kapI_iff smT_left combT_combT combT_single isComb_iff isTan_kapI kapI_kap_assoc smT_add smT_one' smT_prod smT_unit smT_zero_kap
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkLie

open GlobalTheory.IntRebase

section Gen

variable {X0 : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) {G G' : Over X0} [GrpObj G] [GrpObj G']

theorem smT_post' (a : S) (v : overAt x0 (DualNumber S) ⟶ G) (φ : G ⟶ G') :
    smT x0 a (v ≫ φ) = smT x0 a v ≫ φ := (Category.assoc _ _ _).symm

theorem smT_comm (a b : S) (v : overAt x0 (DualNumber S) ⟶ G) :
    smT x0 a (smT x0 b v) = smT x0 b (smT x0 a v) := by
  rw [smT_smT, smT_smT, _root_.mul_comm]

theorem tan_image (q : S) (v : overAt x0 (DualNumber S) ⟶ G) (h0 : smT x0 0 v = 1) (φ : G ⟶ G') [IsMonHom φ] :
    smT x0 0 (smT x0 q (v ≫ φ)) = 1 := by
  rw [smT_comm, smT_post', h0, MonObj.one_comp, smT_one']

theorem smT_natCast (v : overAt x0 (DualNumber S) ⟶ G) (h0 : smT x0 0 v = 1) (n : ℕ) :
    smT x0 (n : S) v = v ^ n := by
  induction n with
  | zero => simpa using h0
  | succ n ih => rw [Nat.cast_succ, smT_add x0 v h0, ih, smT_unit, pow_succ]

theorem comp_id_pow {P : Over X0} (v : P ⟶ G) (n : ℕ) : v ≫ (𝟙 G ^ n) = v ^ n := by
  have h := map_pow (IntRebase.preHom (G := G) v) (𝟙 G) n
  have h2 : IntRebase.preHom (G := G) v (𝟙 G) = v := Category.comp_id v
  rw [h2] at h
  exact h

variable [IsCommMonObj G] [IsCommMonObj G']

theorem combT_image {m : ℕ} (q : S) (v : Fin m → (overAt x0 (DualNumber S) ⟶ G)) (a : Fin m → S) (φ : G ⟶ G')
    [IsMonHom φ] : smT x0 q (combT x0 v a ≫ φ) = combT x0 (fun j => smT x0 q (v j ≫ φ)) a := by
  let ph : (overAt x0 (DualNumber S) ⟶ G) →* (overAt x0 (DualNumber S) ⟶ G') :=
    { toFun := fun v => v ≫ φ
      map_one' := MonObj.one_comp φ
      map_mul' := fun u w => MonObj.mul_comp u w φ }
  have h : combT x0 v a ≫ φ = ∏ j, smT x0 (a j) (v j) ≫ φ :=
    map_prod ph (fun j => smT x0 (a j) (v j)) Finset.univ
  rw [h, smT_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← smT_post', smT_comm]

theorem mul_eq_one_of_pair {m : ℕ} (p : ℕ) (q : S) (hq : q * p = 1) (U : Fin m → (overAt x0 (DualNumber S) ⟶ G))
    (U' : Fin m → (overAt x0 (DualNumber S) ⟶ G')) (hU' : ∀ j, smT x0 0 (U' j) = 1)
    (huniq : ∀ i (a b : Fin m → S), U' i = combT x0 U' a → U' i = combT x0 U' b → a = b)
    (F : G ⟶ G') (F' : G' ⟶ G) [IsMonHom F] (hF : F' ≫ F = 𝟙 _ ^ (p ^ 2)) (k k' : Matrix (Fin m) (Fin m) S)
    (hk : ∀ i, smT x0 q (U i ≫ F) = combT x0 U' (fun j => k j i))
    (hk' : ∀ i, smT x0 q (U' i ≫ F') = combT x0 U (fun j => k' j i)) : k * k' = 1 := by
  ext j i
  have h1 : smT x0 q (smT x0 q (U' i ≫ F') ≫ F) = U' i := by
    rw [← smT_post', Category.assoc, hF, comp_id_pow, ← smT_natCast x0 _ (hU' i), smT_smT, smT_smT]
    have e : q * q * ((p ^ 2 : ℕ) : S) = 1 := by
      push_cast
      linear_combination (q * p + 1) * hq
    rw [e, smT_unit]
  rw [hk', combT_image, funext hk, combT_combT x0 U' hU'] at h1
  have h2 := congrFun (huniq i _ _ h1.symm (combT_single x0 U' hU' i).symm) j
  rw [Matrix.one_apply, Matrix.mul_apply]
  rw [Pi.single_apply] at h2
  exact h2

end Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_coords {V Fr : Type} [CommRing V] [Field Fr] [Algebra V Fr] (io : c.F →+* Fr) {G G' : SAB H (Sp V)}
    (τ : E →+* ℂ) (F : G.G ⟶ G'.G) [IsMonHom F] (hF : ∀ a, G.act.act a ≫ F = F ≫ G'.act.act a) (q : V) {m : ℕ}
    (ub' : Fin m → (epsOver V V ⟶ G'.G))
    (hb : ∀ w : epsOver V V ⟶ G'.G, IsTan w → IsEigV c io G' τ w → ∃! a : Fin m → V, IsComb ub' a w)
    (w : epsOver V V ⟶ G.G) (ht : IsTan w) (he : IsEigV c io G τ w) :
    ∃ a : Fin m → V, IsComb ub' a (kapI ≫ smT (𝟙 (Sp V)) q ((IntRebase.kap ≫ w) ≫ F)) := by
  refine (hb _ (isTan_kapI _ (tan_image _ q _ (smT_zero_kap w ht) F)) ?_).exists
  refine (isEigV_kapI_iff io G' τ _).2 fun a z hz => ?_
  have h1 := (isEigV_kapI_iff io G τ (IntRebase.kap ≫ w)).1 (by rw [kapI_kap_assoc]; exact he) a z hz
  rw [← smT_post', Category.assoc (IntRebase.kap ≫ w), ← hF, ← Category.assoc (IntRebase.kap ≫ w), h1, ← smT_post', smT_comm]

theorem lie_lattice_onto : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y y' : IntFr Xo c T io) (I : IntData Xo c T io y.1) (I' : IntData Xo c T io y'.1) (f : Fib Xo (xOf y) ⟶ Fib Xo (xOf y')) (F : I.G.G ⟶ I'.G.G) (F' : I'.G.G ⟶ I.G.G) (p : ℕ) (v : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber T.Fr) ⟶ Xo.univ.t.G.left)), IsUnit (p : T.V) → IsMonHom F → IsMonHom F' → Ext I.m1 I.m2 I'.m1 I'.m2 f F → F ≫ F' = 𝟙 _ ^ (p ^ 2) → F' ≫ F = 𝟙 _ ^ (p ^ 2) → (∀ a, I.G.act.act a ≫ F = F ≫ I'.G.act.act a) → (∀ a, I'.G.act.act a ≫ F' = F' ≫ I.G.act.act a) → letI := io.toAlgebra; (∀ τ j, IsLieImageH p f.left (y.1.u τ j) (v τ j)) → ∃ k : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.V, (∀ τ, IsUnit (k τ).det) ∧ ∀ τ i, IsCombAt y'.1.x (y'.1.u τ) (fun j => algebraMap T.V T.Fr (k τ j i)) (v τ i) := by
  intro E _ _ _ H Dw l Xo c T io y y' I I' f F F' p v hp hF hF' hExt _ hFF hl hl'
  let _ := io.toAlgebra
  intro hv
  obtain ⟨q, hq⟩ := hp.exists_left_inv
  choose k hk using fun τ i => exists_coords io τ F hl q (I'.ub τ) (I'.basis τ) (I.ub τ i) (I.tan τ i) (I.eig τ i)
  choose k' hk' using fun τ i => exists_coords io τ F' hl' q (I.ub τ) (I.basis τ) (I'.ub τ i) (I'.tan τ i) (I'.eig τ i)
  refine ⟨fun τ => Matrix.of fun j i => k τ i j, fun τ => ?_, fun τ i => ?_⟩
  · refine Matrix.isUnit_det_of_right_inverse (B := Matrix.of fun j i => k' τ i j) ?_
    refine mul_eq_one_of_pair (𝟙 (Sp T.V)) p q hq (fun i => IntRebase.kap ≫ I.ub τ i) (fun i => IntRebase.kap ≫ I'.ub τ i)
      (fun i => smT_zero_kap _ (I'.tan τ i)) ?_ F F' hFF _ _ (fun i => (isComb_iff _ _ _).1 (hk τ i))
      (fun i => (isComb_iff _ _ _).1 (hk' τ i))
    intro i a b ha hb
    have ha' := (isComb_iff (I'.ub τ) a _).2 ha
    have hb' := (isComb_iff (I'.ub τ) b _).2 hb
    rw [kapI_kap_assoc] at ha' hb'
    exact (I'.basis τ _ (I'.tan τ i) (I'.eig τ i)).unique ha' hb'
  · obtain ⟨ψ, -, hψ, hg⟩ := hExt
    obtain ⟨u, hu1, hu2⟩ := I.lift τ i
    choose u' hu1' hu2' using I'.lift τ
    obtain ⟨w, hw1, hw2, hw3⟩ := hv τ i
    have hqp : algebraMap T.V T.Fr q = (p : T.Fr)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← map_natCast (algebraMap T.V T.Fr), ← map_mul, hq, map_one]
    have hov : u ≫ I.t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
      apply GlobalTheory.IntLie.spMap_frac_cancel (V := T.V)
      rw [Category.assoc, ← I.m2.cart.1.w, ← Category.assoc, hu2, Category.assoc, Over.w (I.ub τ i)]
      show spMap _ ≫ spMap _ = _
      rw [GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.spMap_comp₂]
      show spMap ((dualMap (algebraMap T.V T.Fr)).comp (algebraMap T.V (DualNumber T.V))) = _
      rw [GlobalTheory.IntLie.dualMap_alg]
    have h := GlobalTheory.IntLie.comb_generic I'.m1 I'.m2 (I'.ub τ) u' hu2' _
      (spMap (epsMul (algebraMap T.V T.Fr q)) ≫ u ≫ ψ.left) (by
        simp only [Over.comp_left, kapI, IntRebase.kap, smT_left, Over.homMk_left, Category.id_comp, Category.assoc]
        rw [hψ, ← Category.assoc u, hu2, Category.assoc, ← Category.assoc, ← Category.assoc (spMap _) (spMap _),
          GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.dualMap_epsMul]) (k τ i) (hk τ i)
    let g : I.t'.G.left ⟶ pullback Xo.univ.t.G.hom (xOf y) := pullback.lift I.m1.φ I.t'.G.hom I.m1.cart.1.w
    let g' : I'.t'.G.left ⟶ pullback Xo.univ.t.G.hom (xOf y') := pullback.lift I'.m1.φ I'.t'.G.hom I'.m1.cart.1.w
    have hgg := hg g g' (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _)
      (pullback.lift_snd _ _ _)
    have hw : w = u ≫ g := by
      apply pullback.hom_ext
      · rw [hw1, Category.assoc, pullback.lift_fst, hu1]
      · rw [hw2, Category.assoc, pullback.lift_snd, hov]
    have hg' : g' ≫ pullback.fst _ _ = I'.m1.φ := pullback.lift_fst _ _ _
    have hvv : v τ i = (spMap (epsMul (algebraMap T.V T.Fr q)) ≫ u ≫ ψ.left) ≫ I'.m1.φ := by
      rw [hw3, hqp, hw, ← hg', Category.assoc, Category.assoc, Category.assoc, ← Category.assoc ψ.left, ← hgg,
        Category.assoc]
    rw [funext hu1', ← hvv] at h
    exact h

end GlobalTheory.HkLie
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieLatticeOntoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieLattice_onto_of_monHom_pair_pow_p_sq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y y' : IntFr Xo c T io) (I : IntData Xo c T io y.1) (I' : IntData Xo c T io y'.1) (f : Fib Xo (xOf y) ⟶ Fib Xo (xOf y')) (F : I.G.G ⟶ I'.G.G) (F' : I'.G.G ⟶ I.G.G) (p : ℕ) (v : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber T.Fr) ⟶ Xo.univ.t.G.left)), IsUnit (p : T.V) → IsMonHom F → IsMonHom F' → Ext I.m1 I.m2 I'.m1 I'.m2 f F → F ≫ F' = 𝟙 _ ^ (p ^ 2) → F' ≫ F = 𝟙 _ ^ (p ^ 2) → (∀ a, I.G.act.act a ≫ F = F ≫ I'.G.act.act a) → (∀ a, I'.G.act.act a ≫ F' = F' ≫ I.G.act.act a) → letI := io.toAlgebra; (∀ τ j, IsLieImageH p f.left (y.1.u τ j) (v τ j)) → ∃ k : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.V, (∀ τ, IsUnit (k τ).det) ∧ ∀ τ i, IsCombAt y'.1.x (y'.1.u τ) (fun j => algebraMap T.V T.Fr (k τ j i)) (v τ i) := by
  first | exact @GlobalTheory.HkLie.lie_lattice_onto | exact GlobalTheory.HkLie.lie_lattice_onto | (intros; apply GlobalTheory.HkLie.lie_lattice_onto <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieImageCompatibleWithBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieImageCompatibleWithBaseChange
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.LieImageBC

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem epi_of_local {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (d : A →+* B)
    [IsLocalHom d] (hd : Function.Injective d) : Epi (spMap d) := by
  refine ⟨fun {X} a b h => ?_⟩
  obtain ⟨⟨x, f, hf⟩, rfl⟩ := (SpecToEquivOfLocalRing X (CommRingCat.of A)).symm.surjective a
  obtain ⟨⟨y, g, hg⟩, rfl⟩ := (SpecToEquivOfLocalRing X (CommRingCat.of A)).symm.surjective b
  have h1 : IsLocalHom (f ≫ CommRingCat.ofHom d).hom := by
    rw [CommRingCat.hom_comp]; exact RingHom.isLocalHom_comp d f.hom
  have h2 : IsLocalHom (g ≫ CommRingCat.ofHom d).hom := by
    rw [CommRingCat.hom_comp]; exact RingHom.isLocalHom_comp d g.hom
  have h3 : (SpecToEquivOfLocalRing X (CommRingCat.of B)).symm ⟨x, _, h1⟩ =
      (SpecToEquivOfLocalRing X (CommRingCat.of B)).symm ⟨y, _, h2⟩ := by
    simpa [SpecToEquivOfLocalRing] using h
  have h4 := (SpecToEquivOfLocalRing X (CommRingCat.of B)).symm.injective h3
  obtain rfl : x = y := congrArg Sigma.fst h4
  have h5 : f ≫ CommRingCat.ofHom d = g ≫ CommRingCat.ofHom d :=
    congrArg Subtype.val (eq_of_heq (Sigma.mk.inj h4).2)
  obtain rfl : f = g := by
    ext s
    exact hd (congrArg (fun k => k.hom s) h5)
  rfl

theorem epi_dualMap {K L : Type} [Field K] [Field L] (φ : K →+* L) : Epi (spMap (dualMap φ)) := by
  have : IsLocalHom (dualMap φ) := ⟨fun a ha => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero] at ha ⊢
    intro h
    exact ha (by simp [dualMap, h])⟩
  refine epi_of_local _ fun a b h => ?_
  have h1 := congrArg TrivSqZeroExt.fst h
  have h2 := congrArg TrivSqZeroExt.snd h
  ext
  · exact φ.injective (by simpa [dualMap] using h1)
  · exact φ.injective (by simpa [dualMap] using h2)

theorem dual_eps {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (a : S) :
    spMap (dualMap ψ) ≫ spMap (epsMul a) = spMap (epsMul (ψ a)) ≫ spMap (dualMap ψ) := by
  rw [sp_comp, sp_comp]
  congr 1
  ext s <;> simp [dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem dual_alg {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    spMap (dualMap ψ) ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap T (DualNumber T)) ≫ spMap ψ := by
  rw [sp_comp, sp_comp]
  congr 1
  ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem isLieImageH_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K L : Type) [Field K] [Field L] (φ : K →+* L) (x x' : Sp K ⟶ Xo.X) (w w' : Sp L ⟶ Xo.X) (f : Fib Xo x ⟶ Fib Xo x') (g : Fib Xo w ⟶ Fib Xo w') (p : ℕ) (v u : Sp (DualNumber K) ⟶ Xo.univ.t.G.left), IsBC φ f g → IsTanAt x v → (IsLieImageH p f.left v u ↔ IsLieImageH p g.left (spMap (dualMap φ) ≫ v) (spMap (dualMap φ) ≫ u)) := by
  intro E _ _ _ H Dw l Xo K L _ _ φ x x' w w' f g p v u hbc hv
  obtain ⟨rfl, rfl, hbc⟩ := hbc
  let π : pullback Xo.univ.t.G.hom (spMap φ ≫ x) ⟶ pullback Xo.univ.t.G.hom x :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap φ) (by rw [pullback.condition, Category.assoc])
  let π' : pullback Xo.univ.t.G.hom (spMap φ ≫ x') ⟶ pullback Xo.univ.t.G.hom x' :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap φ) (by rw [pullback.condition, Category.assoc])
  have hπ1 : π ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  have hπ2 : π ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap φ := pullback.lift_snd _ _ _
  have hπ1' : π' ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  have hπ2' : π' ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap φ := pullback.lift_snd _ _ _
  have hc := hbc π π' hπ1 hπ2 hπ1' hπ2'
  generalize hF : (f.left : pullback Xo.univ.t.G.hom x ⟶ pullback Xo.univ.t.G.hom x') = F at hc ⊢
  generalize hG : (g.left : pullback Xo.univ.t.G.hom (spMap φ ≫ x) ⟶ pullback Xo.univ.t.G.hom (spMap φ ≫ x')) = G
    at hc ⊢
  have key : ∀ (a : Sp (DualNumber K) ⟶ pullback Xo.univ.t.G.hom x)
      (b : Sp (DualNumber L) ⟶ pullback Xo.univ.t.G.hom (spMap φ ≫ x)),
      a ≫ pullback.fst _ _ = v → a ≫ pullback.snd _ _ = spMap (algebraMap K (DualNumber K)) →
      b ≫ pullback.fst _ _ = spMap (dualMap φ) ≫ v → b ≫ pullback.snd _ _ = spMap (algebraMap L (DualNumber L)) →
      spMap (dualMap φ) ≫ spMap (epsMul ((p : K)⁻¹)) ≫ a ≫ F ≫ pullback.fst _ _ =
        spMap (epsMul ((p : L)⁻¹)) ≫ b ≫ G ≫ pullback.fst _ _ := by
    intro a b ha1 ha2 hb1 hb2
    have hab : b ≫ π = spMap (dualMap φ) ≫ a := by
      apply pullback.hom_ext
      · rw [Category.assoc, hπ1, hb1, Category.assoc, ha1]
      · rw [Category.assoc, hπ2, ← Category.assoc, hb2, Category.assoc, ha2, dual_alg]
    have hGF : G ≫ pullback.fst _ _ = π ≫ F ≫ pullback.fst _ _ := by
      rw [← hπ1', ← Category.assoc, hc, Category.assoc]
    rw [hGF, ← Category.assoc b, hab, ← Category.assoc, dual_eps, map_inv₀, map_natCast]
    simp only [Category.assoc]
  constructor
  · rintro ⟨a, ha1, ha2, rfl⟩
    refine ⟨pullback.lift (spMap (dualMap φ) ≫ v) (spMap (algebraMap L (DualNumber L))) ?_,
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _,
      key a _ ha1 ha2 (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)⟩
    rw [Category.assoc, hv.1, ← Category.assoc, dual_alg, Category.assoc]
  · rintro ⟨b, hb1, hb2, hu⟩
    refine ⟨pullback.lift v (spMap (algebraMap K (DualNumber K))) hv.1,
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, ?_⟩
    have := epi_dualMap φ
    rw [← cancel_epi (spMap (dualMap φ)), hu]
    exact (key _ b (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) hb1 hb2).symm

end GlobalTheory.LieImageBC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieImageCompatibleWithBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_image_compatible_with_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K L : Type) [Field K] [Field L] (φ : K →+* L) (x x' : Sp K ⟶ Xo.X) (w w' : Sp L ⟶ Xo.X) (f : Fib Xo x ⟶ Fib Xo x') (g : Fib Xo w ⟶ Fib Xo w') (p : ℕ) (v u : Sp (DualNumber K) ⟶ Xo.univ.t.G.left), IsBC φ f g → IsTanAt x v → (IsLieImageH p f.left v u ↔ IsLieImageH p g.left (spMap (dualMap φ) ≫ v) (spMap (dualMap φ) ≫ u)) := by
  first | exact @GlobalTheory.LieImageBC.isLieImageH_baseChange | exact GlobalTheory.LieImageBC.isLieImageH_baseChange | (intros; apply GlobalTheory.LieImageBC.isLieImageH_baseChange <;> assumption)
end
end

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HkIntegral

open GlobalTheory.FlagTan GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39

theorem exists_lift {L L' Ω : Type} [Field L] [Field L'] [Field Ω] [IsAlgClosed Ω] (j : L →+* Ω) (i : L →+* L')
    (hi : i.Finite) : ∃ j' : L' →+* Ω, j'.comp i = j := by
  letI := j.toAlgebra
  letI := i.toAlgebra
  haveI : Module.Finite L L' := hi
  let τ : L' →ₐ[L] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  exact ⟨τ.toRingHom, RingHom.ext fun a => τ.commutes a⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem hkWith_iff {K L : Type} [Field K] [Field L] [Algebra c.F K] [Algebra c.F L] (φ : K →ₐ[c.F] L) {p : ℕ}
    (hp : 0 < p) {y z : FrPt Xo c K} {y' z' : FrPt Xo c L} (hy : FrMap φ y y') (hz : FrMap φ z z')
    {f : Fib Xo y.x ⟶ Fib Xo z.x} {f' : Fib Xo z.x ⟶ Fib Xo y.x} {g : Fib Xo y'.x ⟶ Fib Xo z'.x}
    {g' : Fib Xo z'.x ⟶ Fib Xo y'.x} (h : IsBC φ.toRingHom f g) (h' : IsBC φ.toRingHom f' g')
    (hR : AllRat Xo y.x (p ^ 2)) : HkWith p y z f f' ↔ HkWith p y' z' g g' := by
  have e₁ := (GlobalTheory.T.exists_fibreMap_baseChange_and_isogenyPair_iff E H Dw l Xo K L φ.toRingHom y.x z.x y'.x z'.x).2 f f' g g' (p ^ 2) h h'
  have e₂ : ∀ τ j, IsLieImageH p f.left (y.u τ j) (z.u τ j) ↔ IsLieImageH p g.left (y'.u τ j) (z'.u τ j) :=
    fun τ j => by
      rw [hy.2.1, hz.2.1]
      exact GlobalTheory.T.lie_image_compatible_with_base_change E H Dw l Xo K L φ.toRingHom y.x z.x y'.x z'.x f g p _ _ h (y.tan τ j)
  have e₃ := fun a b => GlobalTheory.T.isThetaTrace_conj_iff_of_rigIso E H Dw l Xo c K L φ y z y' z' f f' g p hp hy hz a h hR b
  constructor
  · rintro ⟨a, b, d⟩
    have ⟨β, _, _, _, _, _, hβ, _⟩ := d
    exact ⟨e₁.1 a, fun τ j => (e₂ τ j).1 (b τ j), (e₃ a ⟨β, hβ⟩).1 d⟩
  · rintro ⟨a, b, d⟩
    have ⟨β, _, _, _, _, _, hβ, _⟩ := d
    have a' := e₁.2 a
    exact ⟨a', fun τ j => (e₂ τ j).2 (b τ j),
      (e₃ a' (GlobalTheory.T.exists_isRigIso_of_baseChange' E H Dw l Xo K L φ.toRingHom y.x z.x y'.x z'.x f g _ h a'.1 ⟨β, hβ⟩)).2 d⟩

theorem allRat_up {K L : Type} [Field K] [Field L] (φ : K →+* L) {x : Sp K ⟶ Xo.X} {w : Sp L ⟶ Xo.X} {M : ℕ}
    (hM : 0 < M) (hw : w = spMap φ ≫ x) (h : AllRat Xo x M) : AllRat Xo w M :=
  hw ▸ ((torsion_rational_over_finite_extension E H Dw l Xo K x M hM).2 h).1 L φ

theorem HkOver.up {K L : Type} [Field K] [Field L] [Algebra c.F K] [Algebra c.F L] (φ : K →ₐ[c.F] L) {p : ℕ}
    (hp : 0 < p) {y z : FrPt Xo c K} {y' z' : FrPt Xo c L} (hy : FrMap φ y y') (hz : FrMap φ z z')
    (h : HkOver p y z) : HkOver p y' z' := by
  obtain ⟨h₁, h₂, f, f', h⟩ := h
  obtain ⟨g, hg⟩ := (GlobalTheory.T.exists_fibreMap_baseChange_and_isogenyPair_iff E H Dw l Xo K L φ.toRingHom y.x z.x y'.x z'.x).1 hy.1 hz.1 f
  obtain ⟨g', hg'⟩ := (GlobalTheory.T.exists_fibreMap_baseChange_and_isogenyPair_iff E H Dw l Xo K L φ.toRingHom z.x y.x z'.x y'.x).1 hz.1 hy.1 f'
  exact ⟨allRat_up _ (pow_pos hp _) hy.1 h₁, allRat_up _ (pow_pos hp _) hz.1 h₂, g, g',
    (hkWith_iff φ hp hy hz hg hg' h₁).1 h⟩

theorem exists_hkOver {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed Ω] [Algebra c.F K] [Algebra c.F Ω]
    (k : K →ₐ[c.F] Ω) (hk : k.toRingHom.IsIntegral) {p : ℕ} (hp : 0 < p) {y : FrPt Xo c K} {w z : FrPt Xo c Ω}
    (hw : FrMap k y w) (h : ∃ g g', HkWith p w z g g') :
    ∃ (L : Type) (_ : Field L) (_ : Algebra c.F L) (i : K →ₐ[c.F] L) (j : L →ₐ[c.F] Ω) (y' z' : FrPt Xo c L),
      j.comp i = k ∧ i.toRingHom.Finite ∧ FrMap i y y' ∧ FrMap j z' z ∧ HkOver p y' z' := by
  obtain ⟨g, g', h⟩ := h
  obtain ⟨L₁, _, _, i₁, j₁, z₁, e₁, f₁, hz₁⟩ := GlobalTheory.T.framedPoint_descends_finite_subextension E H Dw l Xo c K Ω k z hk
  obtain ⟨y₁, hy₁⟩ := exists_frMap i₁ y
  have hw₁ : FrMap j₁ y₁ w := frMap_of_comp hy₁ hw fun a => DFunLike.congr_fun e₁ a
  obtain ⟨L₂, _, _, f₂, r₂⟩ := (torsion_rational_over_finite_extension E H Dw l Xo L₁ y₁.x _ (pow_pos hp 2)).1
  obtain ⟨L₃, _, _, f₃, r₃⟩ := (torsion_rational_over_finite_extension E H Dw l Xo L₂
    (spMap (algebraMap L₁ L₂) ≫ z₁.x) _ (pow_pos hp 3)).1
  let a : L₁ →+* L₃ := (algebraMap L₂ L₃).comp (algebraMap L₁ L₂)
  have fa : a.Finite := (RingHom.finite_algebraMap.2 f₃).comp (RingHom.finite_algebraMap.2 f₂)
  obtain ⟨j₃, e₃⟩ := exists_lift j₁.toRingHom a fa
  have hint : j₃.IsIntegral := by
    refine RingHom.IsIntegral.tower_top (a.comp i₁.toRingHom) j₃ ?_
    rw [← RingHom.comp_assoc, e₃]
    subst e₁
    exact hk
  have sq : ∀ x : Sp L₁ ⟶ Xo.X, spMap j₁.toRingHom ≫ x = spMap j₃ ≫ spMap a ≫ x := fun x => by
    rw [← Category.assoc, TorsionRat.sp_comp, e₃]
  obtain ⟨M, _, i₄, j₄, e₄, f₄, hM⟩ := GlobalTheory.T.fibreIsogenyPair_defined_over_finite_subextension E H Dw l Xo L₃ Ω j₃ (spMap a ≫ y₁.x) (spMap a ≫ z₁.x) w.x z.x g g'
    hint (hw₁.1.trans (sq _)) (hz₁.1.trans (sq _)) h.1.1 h.1.2.1
  letI : Algebra c.F M := ((i₄.comp a).comp (algebraMap c.F L₁)).toAlgebra
  let b : L₁ →ₐ[c.F] M := ⟨i₄.comp a, fun _ => rfl⟩
  have eb : ∀ u, j₄ (b u) = j₁ u := fun u =>
    (DFunLike.congr_fun e₄ (a u)).trans (DFunLike.congr_fun e₃ u)
  let j : M →ₐ[c.F] Ω := ⟨j₄, fun u => (eb _).trans (j₁.commutes u)⟩
  obtain ⟨y', hy'⟩ := exists_frMap b y₁
  obtain ⟨z', hz'⟩ := exists_frMap b z₁
  have sq' : ∀ x : Sp L₁ ⟶ Xo.X, spMap b.toRingHom ≫ x = spMap i₄ ≫ spMap a ≫ x := fun x => by
    rw [← Category.assoc, TorsionRat.sp_comp]
  obtain ⟨f, f', hf, hf'⟩ := hM y'.x z'.x (hy'.1.trans (sq' _)) (hz'.1.trans (sq' _))
  have hyw : FrMap j y' w := frMap_of_comp hy' hw₁ eb
  have hzz : FrMap j z' z := frMap_of_comp hz' hz₁ eb
  have R₁ : AllRat Xo y'.x (p ^ 2) := allRat_up (i₄.comp (algebraMap L₂ L₃)) (pow_pos hp _)
    (hy'.1.trans (by rw [← Category.assoc, TorsionRat.sp_comp])) r₂
  have R₂ : AllRat Xo z'.x (p ^ 3) := allRat_up i₄ (pow_pos hp _)
    (hz'.1.trans (by rw [← Category.assoc, ← Category.assoc, TorsionRat.sp_comp, TorsionRat.sp_comp])) r₃
  refine ⟨M, inferInstance, inferInstance, b.comp i₁, j, y', z', AlgHom.ext fun u => (eb _).trans
    (DFunLike.congr_fun e₁ u), (f₄.comp fa).comp f₁, frMap_comp hy₁ hy' fun _ => rfl, hzz, R₁, R₂, f, f',
    (hkWith_iff j hp hyw hzz hf hf' R₁).2 h⟩

theorem frBor_reduce {S : Type} [CommRing S] [Algebra c.F S] {y z : FrPt Xo c S} {t : Ix Dw → Sˣ}
    (hb : FrBor t y z) : ∃ u tan eig basis s gen, z = ⟨y.x, y.x_over, u, tan, eig, basis, s, gen⟩ ∧
      ∀ i, s.f i = scal y.x (t none : S) i * y.s.f i := by
  obtain ⟨x, xo, u, tan, eig, basis, s, gen⟩ := z
  obtain ⟨hx, -, pm, h₁, h₂, h₃⟩ := hb
  dsimp only at hx
  subst hx
  obtain rfl : pm = 𝟙 _ := gx_ext (h₂.trans (Category.id_comp _).symm) (h₁.trans (Category.id_comp _).symm)
  refine ⟨u, tan, eig, basis, s, gen, rfl, fun i => ?_⟩
  have e : Scheme.Hom.appLE (𝟙 (Gx y.x)) ((PPx y.x).U i) ((PPx y.x).U i) le_rfl = 𝟙 _ := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
    exact (Category.id_comp _).trans (CategoryTheory.Functor.map_id _ _)
  have := h₃ i le_rfl
  rw [e] at this
  exact this.symm

theorem frBor_map {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) {t : Ix Dw → Sˣ} {y y' : FrPt Xo c S} {z z' : FrPt Xo c T} (h : FrBor t y y')
    (hz : FrMap φ y z) (hz' : FrMap φ y' z') : FrBor (fun i => Units.map (φ : S →* T) (t i)) z z' := by
  obtain ⟨g, hg2, hg1, hg⟩ := (GlobalTheory.Frames.frBor_iff_frChg y y' t).1 h
  have hc := (frMap_iff_frChg hg hz).1 hz'
  exact (GlobalTheory.Frames.frBor_iff_frChg z z' _).2
    ⟨fun τ => (g τ).map φ, fun τ i j hij => by simp [hg2 τ i j hij], fun τ i => by simp [hg1], hc⟩

section Theta

variable {T : CDVR} {io : c.F →+* T.Fr} {p : ℕ}

theorem theta_low (hp : IsUnit (p : T.V)) (y y' : IntFr Xo c T io)
    (hU : ∀ I : IntData Xo c T io y.1, ∃ P : PELUnif (IsLocalRing.maximalIdeal T.V) I.G, P.TorsionIso) :
    letI := io.toAlgebra
    ∀ (z : FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), HkOver p y.1 z → FrBor t y'.1 z →
      (t none : T.Fr) ∈ Set.range (algebraMap T.V T.Fr) := by
  letI := io.toAlgebra
  intro z t h hb
  obtain ⟨u, tan, eig, basis, s, gen, rfl, hs⟩ := frBor_reduce hb
  obtain ⟨-, -, f, f', hP, -, hT⟩ := h
  obtain ⟨I⟩ := (GlobalTheory.IntegralData.integralIff E H Dw l Xo c T io y.1).1 y.2.2
  obtain ⟨I'⟩ := (GlobalTheory.IntegralData.integralIff E H Dw l Xo c T io y'.1).1 y'.2.2
  obtain ⟨F, F', a₁, a₂, a₃, -, -, a₄, -⟩ :=
    GlobalTheory.T.exists_ext_pair_alt E H Dw l Xo T _ _ I.G I'.G I.t' I'.t' I.m1 I.m2 I'.m1 I'.m2 f f' hP.1 hP.2.1
  obtain ⟨w, w₁, w₂⟩ := GlobalTheory.T.exists_pull_isTranslSum_of_isThetaTrace E H Dw l Xo T.Fr _ _ f f' p y.1.s y'.1.s s _ hP hs hT
  exact GlobalTheory.T.integral_scalar_of_pulledBack_generator_extends_model E H Dw l Xo c T io y y' I I' f F F' (p ^ 2) p _ w a₁ a₂ a₃ (a₄ _ hP.2.2.2.1)
    (by rw [Nat.cast_pow]; exact hp.pow 2) w₁ (GlobalTheory.T.sum_symmetricTranslates_thetaPullback_extends E H Dw l Xo c T io y I p w (hU I) hp w₂)

theorem theta_high (hpp : p.Prime) (hp : IsUnit (p : T.V)) (y y' : IntFr Xo c T io)
    (hU : ∀ I : IntData Xo c T io y'.1, ∃ P : PELUnif (IsLocalRing.maximalIdeal T.V) I.G, P.TorsionIso) :
    letI := io.toAlgebra
    ∀ (z : FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), HkOver p y.1 z → FrBor t y'.1 z →
      vV T.V (t none : T.Fr) ≤ 0 := by
  letI := io.toAlgebra
  intro z t h hb
  obtain ⟨u, tan, eig, basis, s, gen, rfl, hs⟩ := frBor_reduce hb
  obtain ⟨-, hR, f, f', hP, -, hT⟩ := h
  obtain ⟨I⟩ := (GlobalTheory.IntegralData.integralIff E H Dw l Xo c T io y.1).1 y.2.2
  obtain ⟨I'⟩ := (GlobalTheory.IntegralData.integralIff E H Dw l Xo c T io y'.1).1 y'.2.2
  obtain ⟨b, ζ, m, hζ, hab, f₂, hf₂, hff, w, w₁, w₂⟩ :=
    GlobalTheory.T.exists_orth_pull_isTranslSum_of_isThetaTrace E H Dw l Xo T.Fr _ _ f f' p y.1.s y'.1.s s _ hpp hP hR (t none).ne_zero hs hT
  obtain ⟨F, F', a₁, a₂, -, a₃, a₄, -⟩ :=
    GlobalTheory.T.exists_ext_pair_alt E H Dw l Xo T _ _ I.G I'.G I.t' I'.t' I.m1 I.m2 I'.m1 I'.m2 f f₂ hP.1 hf₂
  have hb : b ∈ Set.range (algebraMap T.V T.Fr) := GlobalTheory.T.integral_scalar_of_pulledBack_generator_extends_model E H Dw l Xo c T io y' y I' I f₂ F' F (p ^ 3) (p ^ 2) b w a₂ a₁ a₃ (a₄ _ hff)
    (by rw [Nat.cast_pow]; exact hp.pow 3) w₁
    (GlobalTheory.T.sum_symmetricTranslates_thetaPullback_extends E H Dw l Xo c T io y' I' (p ^ 2) w (hU I') (by rw [Nat.cast_pow]; exact hp.pow 2) w₂)
  obtain ⟨b₀, rfl⟩ := hb
  have hζ0 : ζ ≠ 0 := fun h => by simp [h, hpp.ne_zero] at hζ
  have hp0 : (p : T.Fr) ≠ 0 := by simpa using (hp.map (algebraMap T.V T.Fr)).ne_zero
  have vp : vV T.V (p : T.Fr) = 0 := by
    simpa using GlobalTheory.IntegralFrameCheck.vV_map_unit (V := T.V) (V' := T.V) (RingHom.id T.Fr) (fun a => ⟨a, rfl⟩) hp.unit
  have vζ : vV T.V ζ = 0 := by
    have := GlobalTheory.IntegralFrameCheck.vV_pow (V := T.V) hζ0 p
    rw [hζ, GlobalTheory.IntegralFrameCheck.vV_one] at this
    exact (mul_eq_zero.1 this.symm).resolve_left (by exact_mod_cast hpp.ne_zero)
  have hb0 : algebraMap T.V T.Fr b₀ ≠ 0 := fun h => by
    rw [h, mul_zero] at hab
    exact mul_ne_zero (pow_ne_zero _ hp0) hζ0 hab.symm
  have e := congrArg (vV T.V) hab
  rw [vV_mul (t none).ne_zero hb0, vV_mul (pow_ne_zero _ hp0) hζ0, GlobalTheory.IntegralFrameCheck.vV_pow hp0, vp, vζ] at e
  have := GlobalTheory.IntegralFrameCheck.vV_algebraMap_nonneg (K' := T.Fr) b₀
  omega

theorem isUnit_natCast_up {T' : CDVR} (hp : IsUnit (p : T.V)) (i : T.Fr →+* T'.Fr) {r : ℕ}
    (hi : ∀ a : T.Fr, a ≠ 0 → vV T'.V (i a) = (r : ℤ) * vV T.V a) : IsUnit (p : T'.V) := by
  have hu : (algebraMap T.V T.Fr (hp.unit⁻¹ : T.Vˣ)) ≠ 0 := ((hp.unit⁻¹).isUnit.map _).ne_zero
  obtain ⟨b, hb⟩ := Formalism.L2.PjFree.mem_range_of_vV_nonneg (V := T'.V) (x := i (algebraMap T.V T.Fr (hp.unit⁻¹ : T.Vˣ)))
    (by rw [hi _ hu]; exact mul_nonneg (Int.natCast_nonneg _) (GlobalTheory.IntegralFrameCheck.vV_algebraMap_nonneg _))
  refine IsUnit.of_mul_eq_one b (IsFractionRing.injective T'.V T'.Fr ?_)
  rw [map_mul, hb, map_natCast, ← map_natCast (i.comp (algebraMap T.V T.Fr)), RingHom.comp_apply, ← map_mul,
    ← map_mul, hp.mul_val_inv, map_one, map_one, map_one]

theorem exists_intFr_up {T' : CDVR} {io' : c.F →+* T'.Fr} {e : ℕ} (he : 0 < e) :
    letI := io.toAlgebra; letI := io'.toAlgebra
    ∀ (φ : T.Fr →ₐ[c.F] T'.Fr), (∀ a : T.Fr, a ≠ 0 → vV T'.V (φ a) = (e : ℤ) * vV T.V a) →
      ∀ w : IntFr Xo c T io, ∃ w' : IntFr Xo c T' io', FrMap φ w.1 w'.1 := by
  letI := io.toAlgebra
  have key : ∀ (i : T.Fr →+* T'.Fr), io' = i.comp io → letI := io'.toAlgebra
      ∀ (φ : T.Fr →ₐ[c.F] T'.Fr), φ.toRingHom = i → (∀ a : T.Fr, a ≠ 0 → vV T'.V (i a) = (e : ℤ) * vV T.V a) →
      ∀ w : IntFr Xo c T io, ∃ w' : IntFr Xo c T' io', FrMap φ w.1 w'.1 := by
    rintro i rfl φ hφ hv w
    obtain ⟨w', ψ, hψ, hm⟩ := GlobalTheory.IntFrBaseChange.exists_intFr_baseChange E H Dw l Xo c T T' io w i e he hv
    letI := (i.comp io).toAlgebra
    obtain rfl : ψ = φ := AlgHom.coe_ringHom_injective (hψ.trans hφ.symm)
    exact ⟨w', hm⟩
  letI := io'.toAlgebra
  exact fun φ hφ => key φ.toRingHom (RingHom.ext fun a => (φ.commutes a).symm) φ rfl hφ

theorem theta_unit (hpp : p.Prime) (hp : IsUnit (p : T.V)) (hT : T.FinRes) (y y' : IntFr Xo c T io) :
    letI := io.toAlgebra
    ∀ (z : FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), HkOver p y.1 z → FrBor t y'.1 z →
      vV T.V (t none : T.Fr) = 0 := by
  letI := io.toAlgebra
  intro z t h hb
  apply le_antisymm
  · obtain ⟨T', io', y₁', e, -, he, hU, φ, hφ, hm'⟩ :=
      GlobalTheory.IntegralPull.exists_ext_all_models_uniformised E H Dw l Xo c T io y' hT
    letI := io'.toAlgebra
    obtain ⟨y₁, hm⟩ := exists_intFr_up he φ hφ y
    obtain ⟨z₁, hz⟩ := exists_frMap φ z
    have := theta_high hpp (isUnit_natCast_up hp φ.toRingHom hφ) y₁ y₁' hU z₁ _ (h.up φ hpp.pos hm hz)
      (frBor_map φ hb hm' hz)
    have e₁ : vV T'.V (φ (t none)) ≤ 0 := this
    rw [hφ _ (t none).ne_zero] at e₁
    exact nonpos_of_mul_nonpos_right e₁ (by exact_mod_cast he)
  · obtain ⟨T', io', y₁, e, -, he, hU, φ, hφ, hm⟩ :=
      GlobalTheory.IntegralPull.exists_ext_all_models_uniformised E H Dw l Xo c T io y hT
    letI := io'.toAlgebra
    obtain ⟨y₁', hm'⟩ := exists_intFr_up he φ hφ y'
    obtain ⟨z₁, hz⟩ := exists_frMap φ z
    obtain ⟨b, hb'⟩ := theta_low (isUnit_natCast_up hp φ.toRingHom hφ) y₁ y₁' hU z₁ _ (h.up φ hpp.pos hm hz)
      (frBor_map φ hb hm' hz)
    have e₁ : 0 ≤ vV T'.V (φ (t none)) := by
      have := GlobalTheory.IntegralFrameCheck.vV_algebraMap_nonneg (K' := T'.Fr) b
      rwa [hb'] at this
    rw [hφ _ (t none).ne_zero] at e₁
    exact nonneg_of_mul_nonneg_right e₁ (by exact_mod_cast he)

end Theta

section Frame

variable {T : CDVR} {io : c.F →+* T.Fr} {p : ℕ}

theorem exists_unit_of_vV {a : T.Frˣ} (h : vV T.V (a : T.Fr) = 0) : ∃ u : T.Vˣ, algebraMap T.V T.Fr u = a := by
  obtain ⟨b, hb⟩ := Formalism.L2.PjFree.mem_range_of_vV_nonneg h.ge
  have h' := vV_mul (V := T.V) a.ne_zero a⁻¹.ne_zero
  rw [Units.mul_inv, GlobalTheory.IntegralFrameCheck.vV_one, h, zero_add] at h'
  obtain ⟨b', hb'⟩ := Formalism.L2.PjFree.mem_range_of_vV_nonneg h'.le
  have e : b * b' = 1 := IsFractionRing.injective T.V T.Fr (by rw [map_mul, hb, hb', Units.mul_inv, map_one])
  exact ⟨Units.mkOfMulEqOne b b' e, hb⟩

theorem exists_frBor_unit (hpp : p.Prime) (hp : IsUnit (p : T.V)) (hT : T.FinRes) (y y₀ : IntFr Xo c T io) :
    letI := io.toAlgebra
    ∀ z : FrPt Xo c T.Fr, z.x = y₀.1.x → HkOver p y.1 z →
      ∃ (y' : IntFr Xo c T io) (u : Ix Dw → T.Vˣ), (GlobalTheory.GoodPts.Good y → GlobalTheory.GoodPts.Good y') ∧
        FrBor (fun a => Units.map (algebraMap T.V T.Fr).toMonoidHom (u a)) y'.1 z := by
  letI := io.toAlgebra
  intro z hx h
  obtain ⟨x, xo, u, tan, eig, basis, s, gen⟩ := z
  dsimp only at hx
  subst hx
  have ⟨_, _, f, f', hP, hL, _⟩ := h
  obtain ⟨I⟩ := (GlobalTheory.IntegralData.integralIff E H Dw l Xo c T io y.1).1 y.2.2
  obtain ⟨I'⟩ := (GlobalTheory.IntegralData.integralIff E H Dw l Xo c T io y₀.1).1 y₀.2.2
  obtain ⟨F, F', a₁, a₂, a₃, -, a₄, a₅, a₆, a₇⟩ :=
    GlobalTheory.T.exists_ext_pair_alt E H Dw l Xo T _ _ I.G I'.G I.t' I'.t' I.m1 I.m2 I'.m1 I'.m2 f f' hP.1 hP.2.1
  obtain ⟨k, hk, hc⟩ := GlobalTheory.T.lieLattice_onto_of_monHom_pair_pow_p_sq E H Dw l Xo c T io y y₀ I I' f F F' p u hp a₁ a₂ a₃ (a₄ _ hP.2.2.1) (a₅ _ hP.2.2.2.1)
    (a₆ hP.2.2.2.2.1) (a₇ hP.2.2.2.2.2) hL
  obtain ⟨y', -, hx, hu, -⟩ := GlobalTheory.IntRebase.intRebase GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c T io y₀
    ⟨_, xo, u, tan, eig, basis, s, gen⟩ rfl k hk
  have hu' : ∀ τ i, u τ i = y'.1.u τ i := fun τ i => Formalism.L2.PjFree.isCombAt_unique (hc τ i) (hu τ i)
  have hs : ∀ τ i, IsCombAt y'.1.x (y'.1.u τ) (Pi.single i 1) (u τ i) := fun τ i =>
    hu' τ i ▸ Formalism.L2.PjFree.isCombAt_single (y'.1.tan τ) i
  obtain ⟨t, ht⟩ := (GlobalTheory.Frames.frBor_calculus E H Dw l Xo c T.Fr y'.1 ⟨_, xo, u, tan, eig, basis, s, gen⟩ y'.1).2.1
    hx.symm fun τ i => ⟨Pi.single i 1, by simp, fun j hj => Pi.single_eq_of_ne hj.ne' _,
      hs τ i⟩
  obtain ⟨u₀, hu₀⟩ := exists_unit_of_vV (theta_unit hpp hp hT y y' _ t h ht)
  refine ⟨y', fun a => Option.elim a u₀ fun _ => 1, ?_, ht.1, fun τ i => ⟨Pi.single i 1, by simp,
    fun j hj => Pi.single_eq_of_ne hj.ne' _, hs τ i⟩, ?_⟩
  · rintro ⟨G, t₁, m₁, m₂, hG⟩
    obtain ⟨F₁, -, -, -, b₁, -⟩ := GlobalTheory.T.exists_ext_pair_alt E H Dw l Xo T _ _ G I'.G t₁ I'.t' m₁ m₂ I'.m1 I'.m2 f f' hP.1 hP.2.1
    exact ⟨I'.G, I'.t', hx ▸ I'.m1, I'.m2, GlobalTheory.T.isProper_model_of_extends_fibreIsogeny E H Dw l Xo T _ _ G I'.G t₁ I'.t' m₁ m₂ I'.m1 I'.m2 f f' F₁ _ b₁
      hP.2.2.2.1 (pow_pos hpp.pos 2) hG⟩
  · have := ht.2.2
    rw [← hu₀] at this
    exact this

end Frame

theorem intFrExt (Xo : Moduli Dw l) (c : Coeff l) : IntFrExt Xo c :=
  (Nat.eq_zero_or_pos (Dw.p + Dw.q)).elim (GlobalTheory.T.integralFrameExtension_of_rank_zero_signature E H Dw l Xo c) (GlobalTheory.T.moduliPoint_integralFrame_after_finiteExtension E H Dw l Xo c)

theorem heckeFrameInt (cls : PtClass Xo c)
    (hcls : ∀ T io y T' io' y', cls T io y → (GlobalTheory.GoodPts.Good y → GlobalTheory.GoodPts.Good y') → cls T' io' y') :
    HeckeFrameInt Xo c cls := by
  intro la P p n hP hla T io e ho y hy hc Ω _ _ _
  letI := io.toAlgebra
  intro k hk w hw C z hz
  have hpp : p.Prime := hP.2.2.1
  have hk' : k.toRingHom.IsIntegral := by
    letI := k.toRingHom.toAlgebra
    haveI := hk
    exact fun a => Algebra.IsIntegral.isIntegral (R := T.Fr) a
  obtain ⟨L, _, _, i₁, j₁, y₁, z₁, e₁, f₁, hy₁, hz₁, h₁⟩ :=
    exists_hkOver k hk' hpp.pos hw (GlobalTheory.T.exists_linear_heckeIsogeny_inverse_up_to_p_sq E H Dw l Xo c P p n hP Ω w C z hz)
  obtain ⟨T₁, iT, r₁, ψ, hr₁, hv₁, hψ, hT₁⟩ : ∃ (T₁ : CDVR) (iT : T.Fr →+* T₁.Fr) (r : ℕ) (ψ : L ≃+* T₁.Fr), 0 < r ∧
      (∀ a : T.Fr, vV T₁.V (iT a) = (r : ℤ) * vV T.V a) ∧ (∀ a, ψ (i₁ a) = iT a) ∧ T₁.FinRes := by
    letI := i₁.toRingHom.toAlgebra
    haveI : FiniteDimensional T.Fr L := f₁
    obtain ⟨T₁, iT, r, ψ, -, a, b, d, -, g⟩ := GlobalTheory.PlaceExtField.exists_cdvr_finite_extension T L
    exact ⟨T₁, iT, r, ψ, a, b, d, g hy⟩
  obtain ⟨T₂, i₂, r₂, hr₂, hv₂, hT₂, y₀, hx₀⟩ := intFrExt Xo c T₁ (iT.comp io) hT₁ (spMap ψ.toRingHom ≫ z₁.x) (by
    rw [Category.assoc, z₁.x_over, sOf, sOf, TorsionRat.sp_comp]
    congr 1
    refine RingHom.ext fun a => ?_
    exact (congrArg ψ (i₁.commutes _).symm).trans (hψ _))
  let i : T.Fr →+* T₂.Fr := i₂.comp iT
  have hv : ∀ a, vV T₂.V (i a) = ((r₂ * r₁ : ℕ) : ℤ) * vV T.V a := fun a => by
    rw [RingHom.comp_apply, hv₂, hv₁, Nat.cast_mul, _root_.mul_assoc]
  have hr : 0 < r₂ * r₁ := Nat.mul_pos hr₂ hr₁
  obtain ⟨j, hj⟩ := exists_lift (j₁.toRingHom.comp ψ.symm.toRingHom) i₂ (GlobalTheory.T.ringHom_finite_and_isIntegral_of_valuation_scaled T₁ T₂ i₂ r₂ hr₂ hv₂ hT₂).1
  have hj' : ∀ a : L, j (i₂ (ψ a)) = j₁ a := fun a => by simpa using DFunLike.congr_fun hj (ψ a)
  letI := (i.comp io).toAlgebra
  let b : L →ₐ[c.F] T₂.Fr := ⟨i₂.comp ψ.toRingHom, fun a =>
    congrArg i₂ ((congrArg ψ (i₁.commutes a).symm).trans (hψ _))⟩
  let φ : T.Fr →ₐ[c.F] T₂.Fr := ⟨i, fun _ => rfl⟩
  have hφ : ∀ a, b (i₁ a) = φ a := fun a => congrArg i₂ (hψ a)
  have hjk : ∀ a, j (i a) = k a := fun a =>
    (congrArg j (hφ a).symm).trans ((hj' _).trans (DFunLike.congr_fun e₁ a))
  let J : T₂.Fr →ₐ[c.F] Ω := ⟨j, fun a => (hjk _).trans (k.commutes a)⟩
  obtain ⟨y₂, hy₂⟩ := exists_intFr_up (io' := i.comp io) hr φ (fun a _ => hv a) y
  obtain ⟨z₂, hz₂⟩ := exists_frMap b z₁
  obtain ⟨y', u, hg, hb⟩ := exists_frBor_unit (io := i.comp io) hpp
    (isUnit_natCast_up (PullbackSections.isUnit_natCast_of_overLa T ho hla) i fun a _ => hv a) hT₂ y₂ y₀ z₂
    (hz₂.1.trans (hx₀.trans (by rw [← Category.assoc, TorsionRat.sp_comp])).symm)
    (h₁.up b hpp.pos (frMap_of_comp hy₁ hy₂ hφ) hz₂)
  obtain ⟨w', hw'⟩ := exists_frMap J y'.1
  refine ⟨T₂, i, ⟨(GlobalTheory.T.ringHom_finite_and_isIntegral_of_valuation_scaled T T₂ i _ hr hv hT₂).1, _, hr, hv⟩, J, RingHom.ext hjk, y', hT₂,
    hcls T io y T₂ _ y' hc fun h => hg (GlobalTheory.T.goodReduction_stable_valuationRing_extension E H Dw l Xo c T T₂ io _ y y₂ i _ hr hv hy₂.1 h), w', u, hw', ?_⟩
  exact frBor_map J hb hw' (frMap_of_comp hz₂ hz₁ hj')

theorem heckeValueInt (cls : PtClass Xo c) (h : HeckeFrameInt Xo c cls) : HeckeValueInt Xo c cls := by
  intro la P p n hP hla T io e ho y hy hc Ω _ _ _
  letI := io.toAlgebra
  intro k hk w hw C z hz
  refine ⟨fromTest_of_isLocalRing z, fun a m f hf hv => ?_⟩
  obtain ⟨T', i, ⟨-, r, hr, hi⟩, j, hj, y', hy', -, w', u, hw', hb⟩ :=
    h la P p n hP hla T io e ho y hy hc Ω k hk w hw C z hz
  letI := (i.comp io).toAlgebra
  have h0 : 0 ≤ nval T'.V (r * e) (evI y' f) := hv _ ⟨PtV.mk la (ho.bc i hr hi) y' hy' () trivial, rfl⟩
  obtain ⟨b, hb'⟩ : evI y' f ∈ Set.range (algebraMap T'.V T'.Fr) := by
    by_cases hx : evI y' f = 0
    · exact ⟨0, by rw [hx, map_zero]⟩
    refine Formalism.L2.PjFree.mem_range_of_vV_nonneg ?_
    rw [nval_of_ne hx, EReal.coe_nonneg, le_div_iff₀ (by exact_mod_cast Nat.mul_pos hr ho.1), zero_mul] at h0
    exact_mod_cast h0
  have e₁ := (GlobalTheory.Frames.algebraic_laws GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c).2.2.2.2.2.2 Ω inferInstance
    a m f hf _ w' z hb
  have e₂ : evR Xo c f w' = j (algebraMap T'.V T'.Fr b) := (evR_frMap hf.1 hw').trans (congrArg j hb'.symm)
  have e₃ : evR Xo c f z = j (algebraMap T'.V T'.Fr (wchar (ex Dw a m) u * b)) := by
    rw [e₁, e₂, map_mul, map_mul]
    congr 1
    simp [wchar]
  obtain ⟨q, hq, hq'⟩ := (GlobalTheory.T.ringHom_finite_and_isIntegral_of_valuation_scaled T T' i r hr hi hy').2 (wchar (ex Dw a m) u * b)
  refine ⟨q, hq, ?_⟩
  rw [e₃, ← hj, RingHom.comp_assoc]
  exact (Polynomial.hom_eval₂ q _ j.toRingHom _).symm.trans ((congrArg j.toRingHom hq').trans (map_zero _))

theorem heckeInt : HeckeInt := fun _ _ _ _ _ _ _ Xo c =>
  have g : HeckeFrameInt Xo c (goodCls Xo c) := heckeFrameInt _ fun _ _ _ _ _ _ a b => b a
  have a : HeckeFrameInt Xo c (GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.trivialClassCondition Xo c) := heckeFrameInt _ fun _ _ _ _ _ _ _ _ => trivial
  ⟨⟨g, heckeValueInt _ g⟩, a, heckeValueInt _ a⟩

end GlobalTheory.HkIntegral
