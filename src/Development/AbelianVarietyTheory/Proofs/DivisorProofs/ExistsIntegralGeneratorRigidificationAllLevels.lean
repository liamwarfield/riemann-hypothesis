module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateSimilitudeHeckeTranslateGeometric
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndOnId
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorDataFactorInclusionProjectionProps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionRationalOfRetractGaloisFixedPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralGeneratorRigidificationAllLevels
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralGeneratorRigidificationAllLevels
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.IntEval

section

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {G : Over (Sp R)} {D : DegData R I}
  {A : PolAV (Sp (FractionRing R))} [GrpObj G] [IsCommMonObj G]

theorem hRed_pGl {U : UnifPre I D A G} {h : 𝟙_ (Over (Sp R)) ⟶ G} {g : GtPt D.toPre (𝟙_ (Over (Sp R)))}
    (hg : GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U h g) (e : ℕ) : hRed I h e ≫ pGl U e = thick R I e ≫ g.b.left := by
  have a : hRed I (𝟙 (𝟙_ (Over (Sp R)))) e ≫ (fstG I e (𝟙_ (Over (Sp R)))).left = thick R I e :=
    (hRed_fst _ e).trans (Category.comp_id _)
  have b : hRed I (𝟙 (𝟙_ (Over (Sp R)))) e ≫ ((Over.pullback (thick R I e)).map h).left = hRed I h e := by
    have := GlobalTheory.TorsionTranslate.mono_fst (I := I) e G
    rw [← cancel_mono (fstG I e G).left, hRed_fst, Category.assoc]
    have c : ((Over.pullback (thick R I e)).map h).left ≫ (fstG I e G).left =
        (fstG I e (𝟙_ (Over (Sp R)))).left ≫ h.left := pullback.lift_fst _ _ _
    rw [c, ← Category.assoc, a]
  exact (congrArg (· ≫ pGl U e) b).symm.trans ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (hg e).1.symm).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ g.b.left) a))))

theorem exists_tRel [IsLocalRing R] [IsAdicComplete I R] (hI : I ≠ ⊤) {U : UnifPre I D A G}
    {h : 𝟙_ (Over (Sp R)) ⟶ G} {b : 𝟙_ (Over (Sp R)) ⟶ D.toPre.P.A}
    (hb : ∀ e, hRed I h e ≫ pGl U e = thick R I e ≫ b.left)
    (f : LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => h.left) (fun _ => 1))) (hf : f.IsGen) :
    ∃ t : LB.Gen (LB.LinComb D.toPre.P.L ![(η[D.toPre.P.A]).left, b.left] (DegPre.lineε 1)),
      t.IsGen ∧ ∀ e : ℕ, TRel U h b f t e := by
  obtain ⟨ν, ν', hν, hν', v⟩ := GlobalTheory.TorsionTranslate.exists_matching U hI (K := Fin 1) (fun _ => 1)
    (fun _ => b.left) (fun _ => h.left) (fun e _ => hRed I h e) (fun e _ => hb e) (fun e _ => hRed_fst h e)
  obtain ⟨ρ, hρ⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_ratio U.LG.isLB rfl f ν' hf hν'
  obtain ⟨μ₁, hμ, vμ⟩ := GlobalTheory.TorsionTranslate.exists_scale ν hν ρ
  obtain ⟨t, ht, vt⟩ := exists_gen D.toPre.P.isLB (φ' := ![(η[D.toPre.P.A]).left, b.left]) (ε' := DegPre.lineε 1)
    (fun W _ k => by
      refine (Fintype.prod_sum_type _).trans ?_
      rw [Fin.prod_univ_two, Fintype.prod_unique, Fintype.prod_unique]
      rfl)
    (LB.mulGen D.toPre.P.L (K := PUnit) _ _ _ _ D.toPre.rig (LB.invGen D.toPre.P.L _ _ μ₁))
    (mulGen_isGen _ _ _ _ _ _ _ D.toPre.rig_gen (invGen_isGen _ _ _ _ hμ))
  refine ⟨t, ht, fun e Z r z J JG hJ hJG => ?_⟩
  have k := v e Z r z J JG hJ hJG
  rw [Fintype.prod_unique, zpow_one] at k
  have w : wv U e (r ≫ hRed I h e) z (J (r ≫ hRed I h e ≫ pGl U e)) (JG (r ≫ hRed I h e ≫ fGl I G e)) =
      GlobalTheory.TorusInvariance.wVal U e z J JG (r ≫ hRed I h e) := by
    rw [← Category.assoc, ← Category.assoc]; rfl
  have k₁ := (vt _ (r ≫ thick R I e) z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg (_ * ·)
    ((val_inv _ _).trans (congrArg (·⁻¹) ((vμ _ _ z J hJ).trans (congrArg (_ * ·) k))))))
  have k₂ := hρ _ (r ≫ thick R I e) z JG hJG
  refine (congrArg₂ (· * ·) (congrArg₂ (· * ·) k₁ w) k₂).trans ?_
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end

theorem exists_integral_frame : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal V) D A G) (h : 𝟙_ (Over (Sp V)) ⟶ G) (g : GtPt D.toPre (𝟙_ (Over (Sp V)))), GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U h g → ∀ f : LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => h.left) (fun _ => 1)), f.IsGen → ∃ t : LB.Gen (LB.LinComb D.toPre.P.L ![(η[D.toPre.P.A]).left, g.b.left] (DegPre.lineε 1)), t.IsGen ∧ ∀ e : ℕ, GlobalTheory.Poinc.IntEval.TRel U h g.b f t e := by
  intro V _ _ _ hV D A G _ _ U h g hg f hf
  have := hV.2.2.1
  exact exists_tRel (maximalIdeal.isMaximal V).ne_top (hRed_pGl hg) f hf

end GlobalTheory.Poinc.IntEval
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralGeneratorRigidificationAllLevelsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_generator_rigidification_all_levels : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal V) D A G) (h : 𝟙_ (Over (Sp V)) ⟶ G) (g : GtPt D.toPre (𝟙_ (Over (Sp V)))), GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U h g → ∀ f : LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => h.left) (fun _ => 1)), f.IsGen → ∃ t : LB.Gen (LB.LinComb D.toPre.P.L ![(η[D.toPre.P.A]).left, g.b.left] (DegPre.lineε 1)), t.IsGen ∧ ∀ e : ℕ, GlobalTheory.Poinc.IntEval.TRel U h g.b f t e := by
  first | exact @GlobalTheory.Poinc.IntEval.exists_integral_frame | exact GlobalTheory.Poinc.IntEval.exists_integral_frame | (intros; apply GlobalTheory.Poinc.IntEval.exists_integral_frame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetAevalEqProdArootsCharpoly
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetAevalEqProdArootsCharpoly
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DetAevalRoots

open Polynomial

theorem det_aeval_X_sub_C {Ω : Type} [Field Ω] [IsAlgClosed Ω] {n : ℕ}
    (N : Matrix (Fin n) (Fin n) Ω) (r : Ω) :
    (aeval N (Polynomial.X - C r)).det
      = (N.charpoly.roots.map fun a => (Polynomial.X - C r).eval a).prod := by
  have hs := IsAlgClosed.splits N.charpoly
  have hR : Multiset.card N.charpoly.roots = n := by
    rw [← hs.natDegree_eq_card_roots, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have h : aeval N (Polynomial.X - C r) = -(Matrix.scalar (Fin n) r - N) := by
    simp [Matrix.algebraMap_eq_diagonal]
  rw [h, Matrix.det_neg, Fintype.card_fin, ← Matrix.eval_charpoly]
  conv_lhs => rw [hs.eq_prod_roots_of_monic (Matrix.charpoly_monic N)]
  rw [eval_multiset_prod, Multiset.map_map]
  simp only [Function.comp_def, eval_sub, eval_X, eval_C]
  have e2 : (N.charpoly.roots.map fun x => x - r)
      = (N.charpoly.roots.map fun x => r - x).map Neg.neg := by
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl (fun _ _ => by simp)
  rw [e2, Multiset.prod_map_neg, Multiset.card_map, hR]

theorem det_aeval_eq_prod_roots {Ω : Type} [Field Ω] [IsAlgClosed Ω] {n : ℕ}
    (N : Matrix (Fin n) (Fin n) Ω) (G : Polynomial Ω) :
    (aeval N G).det = (N.charpoly.roots.map fun a => G.eval a).prod := by
  have hs := IsAlgClosed.splits N.charpoly
  have hR : Multiset.card N.charpoly.roots = n := by
    rw [← hs.natDegree_eq_card_roots, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have key : ∀ (c : Ω) (s : Multiset Ω),
      (aeval N (C c * (s.map fun r => Polynomial.X - C r).prod)).det
        = (N.charpoly.roots.map fun a =>
            (C c * (s.map fun r => Polynomial.X - C r).prod).eval a).prod := by
    intro c s
    induction s using Multiset.induction_on with
    | empty =>
      simp [Matrix.algebraMap_eq_diagonal, Matrix.det_diagonal, hR]
    | cons r s ih =>
      have e : C c * ((r ::ₘ s).map fun r => Polynomial.X - C r).prod
          = (Polynomial.X - C r) * (C c * (s.map fun r => Polynomial.X - C r).prod) := by
        rw [Multiset.map_cons, Multiset.prod_cons]; ring
      rw [e, map_mul, Matrix.det_mul, ih, det_aeval_X_sub_C, ← Multiset.prod_map_mul]
      simp only [eval_mul]
  have hG := C_leadingCoeff_mul_prod_multiset_X_sub_C
    ((IsAlgClosed.splits G).natDegree_eq_card_roots).symm
  rw [← hG]
  exact key _ _

end GlobalTheory.DetAevalRoots


open Polynomial in
theorem GlobalTheory.det_aeval_eq_prod_aroots_charpoly : ∀ (k Ω V : Type) [Field k] [Field Ω] [IsAlgClosed Ω] [Algebra k Ω] [AddCommGroup V] [Module k V] [Module.Finite k V] (φ : V →ₗ[k] V) (F : Polynomial k), algebraMap k Ω (LinearMap.det (Polynomial.aeval φ F)) = ((φ.charpoly.aroots Ω).map (fun a => Polynomial.aeval a F)).prod := by
  intro k Ω V _ _ _ _ _ _ _ φ F
  let b := Module.finBasis k V
  let f := algebraMap k Ω
  have h1 : LinearMap.det (aeval φ F) = (aeval (LinearMap.toMatrix b b φ) F).det := by
    rw [← LinearMap.det_toMatrix b]
    congr 1
    exact (aeval_algHom_apply (LinearMap.toMatrixAlgEquiv b).toAlgHom φ F).symm
  have h2 : f.mapMatrix (aeval (LinearMap.toMatrix b b φ) F)
      = aeval ((LinearMap.toMatrix b b φ).map f) (F.map f) := by
    refine map_aeval_eq_aeval_map (φ := f) (ψ := RingHom.mapMatrix (m := Fin (Module.finrank k V)) f) ?_ F _
    ext x i j
    simp [Matrix.algebraMap_matrix_apply, apply_ite f]
  have h3 : φ.charpoly.aroots Ω = ((LinearMap.toMatrix b b φ).map f).charpoly.roots := by
    rw [Matrix.charpoly_map, LinearMap.charpoly_toMatrix]
  rw [h1, RingHom.map_det, h2, h3, GlobalTheory.DetAevalRoots.det_aeval_eq_prod_roots]
  simp only [eval_map_algebraMap, f]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetAevalEqProdArootsCharpolyStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_aeval_eq_prod_aroots_charpoly' : ∀ (k Ω V : Type) [Field k] [Field Ω] [IsAlgClosed Ω] [Algebra k Ω] [AddCommGroup V] [Module k V] [Module.Finite k V] (φ : V →ₗ[k] V) (F : Polynomial k), algebraMap k Ω (LinearMap.det (Polynomial.aeval φ F)) = ((φ.charpoly.aroots Ω).map (fun a => Polynomial.aeval a F)).prod := by
  first | (exact @GlobalTheory.det_aeval_eq_prod_aroots_charpoly) | (exact GlobalTheory.det_aeval_eq_prod_aroots_charpoly) | (intros; apply GlobalTheory.det_aeval_eq_prod_aroots_charpoly  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticCurveIsAffineAndFiniteInt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticCurveIsAffineAndFiniteInt
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.ArithCurve

theorem isProper_of_projOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : IsProper f := by
  obtain ⟨m, i, hi, rfl⟩ := h
  have := isProper_str R m
  infer_instance

theorem not_isClosed_genericPoint_int : ¬ IsClosed ({genericPoint (Sp ℤ)} : Set (Sp ℤ)) := by
  intro hc
  have hu : ∀ x : Sp ℤ, x = genericPoint (Sp ℤ) := fun x => by
    have hx : x ∈ closure ({genericPoint (Sp ℤ)} : Set (Sp ℤ)) :=
      (genericPoint_spec (Sp ℤ)).def ▸ Set.mem_univ x
    rwa [hc.closure_eq] at hx
  let a : PrimeSpectrum ℤ := ⟨⊥, Ideal.isPrime_bot⟩
  let b : PrimeSpectrum ℤ := ⟨Ideal.span {(2 : ℤ)},
    (Ideal.span_singleton_prime (by norm_num)).2 Int.prime_two⟩
  have hab : a = b := (hu (show Sp ℤ from a)).trans (hu (show Sp ℤ from b)).symm
  have h2 : (2 : ℤ) ∈ b.asIdeal := Ideal.subset_span rfl
  rw [← hab] at h2
  exact absurd ((Submodule.mem_bot ℤ).1 h2) (by norm_num)

theorem isAffine_and_finite : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k),
    IsArithVar q 0 → IsAffine Y ∧ Module.Finite ℤ Γ(Y, ⊤) := by
  intro k _ Y q h
  have := h.isIntegral
  have := h.isNoetherian
  have hd : topologicalKrullDim Y = 1 := by simpa using h.dim_eq
  have : IsProper q := isProper_of_projOver h.isProjOver
  have : IsFinite (spMap (Int.castRingHom k)) := by
    have := h.finite
    rw [IsFinite.SpecMap_iff]
    change (Int.castRingHom k).Finite
    rw [← algebraMap_int_eq]
    exact RingHom.finite_algebraMap.2 ‹_›
  set f : Y ⟶ Sp ℤ := q ≫ spMap (Int.castRingHom k) with hf
  have : Flat f := h.flat
  have : IsProper f := inferInstance
  have hη : f (genericPoint Y) = genericPoint (Sp ℤ) := by
    obtain ⟨y, hy, e⟩ := Flat.generalizingMap f (genericPoint_specializes (f (genericPoint Y)))
    rwa [(hy.antisymm (genericPoint_specializes y)).eq] at e
  have hfib : ∀ z, (f ⁻¹' {z}).Finite := by
    intro z
    by_cases hz : z = genericPoint (Sp ℤ)
    · refine (Set.finite_singleton (genericPoint Y)).subset fun y hy => ?_
      by_contra hne
      have hc := f.isClosedMap _ (ProperCurve.isClosed_singleton hd hne)
      rw [Set.image_singleton, show f y = z from hy, hz] at hc
      exact not_isClosed_genericPoint_int hc
    · refine (ProperCurve.finite_of_isClosed hd (isClosed_closure.preimage f.continuous) ?_).subset
        (Set.preimage_mono subset_closure)
      intro hmem
      rw [Set.mem_preimage, hη, ← specializes_iff_mem_closure] at hmem
      exact hz (hmem.antisymm (genericPoint_specializes z)).eq
  have : LocallyQuasiFinite f := .of_finite_preimage_singleton f hfib
  have : IsFinite f := .of_isProper_of_locallyQuasiFinite f
  have : IsAffine Y := isAffine_of_isAffineHom f
  refine ⟨this, ?_⟩
  have h1 := IsFinite.finite_app f ⊤ (isAffineOpen_top _)
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom.Finite :=
    RingHom.Finite.of_surjective _ fun x => ⟨(Scheme.ΓSpecIso (CommRingCat.of ℤ)).hom x, by simp⟩
  have e : (f.app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom =
      algebraMap ℤ Γ(Y, ⊤) := RingHom.ext_int _ _
  exact RingHom.finite_algebraMap.1 (e ▸ h1.comp h2)

end GlobalTheory.ArithCurve
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticCurveIsAffineAndFiniteIntStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmeticCurve_isAffine_and_finite_int : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsArithVar q 0 → IsAffine Y ∧ Module.Finite ℤ Γ(Y, ⊤) := by
  first | exact @GlobalTheory.ArithCurve.isAffine_and_finite | exact GlobalTheory.ArithCurve.isAffine_and_finite | (intros; apply GlobalTheory.ArithCurve.isAffine_and_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormDensityChangeOfChart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormDensityChangeOfChart
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mix.ChartChange

section
variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

def colSum (H : Fin D → Matrix (Fin D) (Fin D) ℂ) : ℂ :=
  ∑ τ : Equiv.Perm (Fin D), (Matrix.of fun j l => H (τ l) j l).det

theorem colSum_mul_left (A : Matrix (Fin D) (Fin D) ℂ) (H : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    colSum (fun a => A * H a) = A.det * colSum H := by
  simp only [colSum, Finset.mul_sum, ← Matrix.det_mul]
  refine Finset.sum_congr rfl fun τ _ => congrArg _ ?_
  ext j l
  simp [Matrix.mul_apply]

theorem colSum_transpose (H : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    colSum (fun a => (H a).transpose) = colSum H := by
  simp only [colSum, Matrix.det_apply', Matrix.of_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun (τ ρ : Equiv.Perm (Fin D)) => ((Equiv.Perm.sign ρ : ℤ) : ℂ) * ∏ i, H (τ i) (ρ i) i)]
  refine Fintype.sum_equiv (Equiv.inv _) _ _ fun ρ => ?_
  refine Fintype.sum_equiv (Equiv.mulRight ρ⁻¹) _ _ fun τ => ?_
  simp only [Equiv.inv_apply, Equiv.Perm.sign_inv, Equiv.coe_mulRight]
  congr 1
  refine Fintype.prod_equiv ρ _ _ fun i => ?_
  simp

theorem colSum_mul (A B : Matrix (Fin D) (Fin D) ℂ) (H : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    colSum (fun a => A * H a * B) = A.det * B.det * colSum H := by
  have e : colSum (fun a => H a * B) = B.det * colSum H := by
    rw [← colSum_transpose, ← colSum_transpose H, ← Matrix.det_transpose B, ← colSum_mul_left]
    simp only [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]
  rw [colSum_mul_left A fun a => H a * B, e, mul_assoc]

theorem dens_eq (L : Fin D → MLine p σ) (c : AlgChart p σ D) (y : CxPts p σ) :
    dens L c y = (Real.pi ^ D)⁻¹ * (colSum fun a => c.hess (L a).φ (pick (L a).φ.isLB y) y).re := rfl

theorem dens_trans (L : Fin D → MLine p σ) (c c' : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source)
    (hy' : y ∈ c'.e.source) : dens L c y = ‖transDet c.e c'.e y‖ ^ 2 * dens L c' y := by
  have ho := isOpen_over c.e c'.e.open_source
  have hm := mem_over c.e hy hy'
  have e₂ : (c'.e ∘ c.e.symm) (c.e y) = c'.e y := congrArg c'.e (c.e.left_inv hy)
  let J : Matrix (Fin D) (Fin D) ℂ :=
    Matrix.of fun l j => (fderiv ℂ (c'.e ∘ c.e.symm) (c.e y) (ReciprocityTheory.L2DbarEstimates.bas D j)) l
  have h (a) : c.hess (L a).φ (pick (L a).φ.isLB y) y =
      J.transpose * c'.hess (L a).φ (pick (L a).φ.isLB y) y * J.map (starRingEnd ℂ) := by
    have e : (fun v => ((L a).φ.φ (pick (L a).φ.isLB y) (c.e.symm v) : ℂ)) =ᶠ[𝓝 (c.e y)]
        (fun v => ((L a).φ.φ (pick (L a).φ.isLB y) (c'.e.symm v) : ℂ)) ∘ c'.e ∘ c.e.symm :=
      eventually_of_mem (ho.mem_nhds hm) fun v hv => by
        simp only [Function.comp_apply, c'.e.left_inv hv.2]
    rw [AlgChart.hess, AlgChart.hess, ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr e,
      ReciprocityTheory.L2DbarEstimates.Y.cmpa_cHess_comp ho hm (c.holo_trans c') (e₂ ▸
        Complex.ofRealCLM.contDiff.contDiffAt.comp _ ((L a).cInf.contDiffAt c' hy' (mem_pick _ y))), e₂]
  have hJ : J.det = transDet c.e c'.e y := ReciprocityTheory.L2DbarEstimates.Y.cmpa_det_jac _
  have hd : J.transpose.det * (J.map (starRingEnd ℂ)).det = ((‖transDet c.e c'.e y‖ ^ 2 : ℝ) : ℂ) := by
    have hm' : (J.map (starRingEnd ℂ)).det = starRingEnd ℂ J.det := (RingHom.map_det (starRingEnd ℂ) J).symm
    rw [hm', Matrix.det_transpose, hJ, Complex.mul_conj']
    push_cast
    rfl
  rw [dens_eq, dens_eq]
  simp only [h]
  rw [colSum_mul, hd, Complex.re_ofReal_mul]
  ring

end

theorem dens_change_chart : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (L : Fin D → MLine p σ) (c c' : AlgChart p σ D) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source → dens L c y = ‖transDet c.e c'.e y‖ ^ 2 * dens L c' y :=
  fun _ _ _ _ _ _ L c c' _ hy hy' => dens_trans L c c' hy hy'

end GlobalTheory.Mix.ChartChange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormDensityChangeOfChartStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedChernFormDensity_change_of_chart : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (L : Fin D → MLine p σ) (c c' : AlgChart p σ D) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source → dens L c y = ‖transDet c.e c'.e y‖ ^ 2 * dens L c' y := by
  first | exact @GlobalTheory.Mix.ChartChange.dens_change_chart | exact GlobalTheory.Mix.ChartChange.dens_change_chart | (intros; apply GlobalTheory.Mix.ChartChange.dens_change_chart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiPosFubiniStudyPowerAddSmoothFn
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiPosFubiniStudyPowerAddSmoothFn
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WeightShift

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {B : LB Y}

theorem exists_semiPosReg_pow_addFn [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)]
    (R : AnRead p σ D) {φ : Weight p σ B} (h : φ.IsSmooth R) (hp : φ.StrictPos R)
    {v : CxPts p σ → ℝ} (hv : ∀ y, CInfAt v y) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ((φ.pow m).addFn v).SemiPosReg D := by
  have hA : IsAlgAtlas R.finAtlas := R.isAlgAtlas_finAtlas
  have hv' : R.SmoothOn univ v := (cInfAt_iff_smoothOn R isOpen_univ).1 fun y _ => hv y
  have hw : R.finAtlas.Smooth fun y => v y / 2 :=
    (hA.smooth_iff R).2 fun c => (hv' c).div_const 2
  have hΩ := h.isPotential hA
  have hpos := (h.isPosPot_iff hA).2 hp
  have hpsh : IsPsh R.finAtlas φ.locPot := fun x j z hz w => by
    by_cases h0 : w = 0
    · rw [h0, ReciprocityTheory.AnForm.levi_zero]
    · exact (hpos x j z hz w h0).le
  obtain ⟨C, hC⟩ := pshShift R.finAtlas φ.locPot hΩ hpos _ hw
  refine ⟨⌈C⌉₊, fun m hm i c y hy ξ => ?_⟩
  have hmC : 0 ≤ (m : ℝ) - C := sub_nonneg.2 (Nat.ceil_le.1 hm)
  have hχ : ((φ.pow m).addFn v).IsSmooth R := (h.zpow m).addFn hv'
  obtain ⟨j, hj⟩ := R.finAtlas.cover y
  obtain ⟨c', hc'⟩ := hA j
  rw [hc'] at hj
  have hb : y ∈ ptsIn p σ ((lbPow B m).U fun _ => pick φ.isLB y) :=
    mem_pow_iff.2 (mem_pick φ.isLB y)
  obtain ⟨w, -, e⟩ := hχ.exists_levi_eq c c' hy.1 hj hy.2 hb ξ
  rw [hχ.leviV_re_eq c hy.1 hy.2, e]
  have hz : c'.finChart y ∈ c'.finChart.target ∩ c'.finChart.symm ⁻¹' φ.locPot.U y :=
    mem_over c'.e hj (φ.locPot.mem_U y)
  have h₁ := hC y j (c'.finChart y) (by rw [hc']; exact ⟨hz.1, trivial, hz.2⟩) w
  have h₂ := hpsh y j (c'.finChart y) (by rw [hc']; exact hz) w
  rw [hc'] at h₁ h₂
  have d₁ : ContDiffAt ℝ 2 (((φ.pow m).addFn v).φ (fun _ => pick φ.isLB y) ∘ c'.finChart.symm)
      (c'.finChart y) := hχ.contDiffAt_finChart c' hj hb
  have d₂ : ContDiffAt ℝ 2 (φ.locPot.φ y ∘ c'.finChart.symm) (c'.finChart y) :=
    (h.contDiffAt_finChart c' hj (mem_pick φ.isLB y)).div_const 2
  have e₁ := ReciprocityTheory.AnForm.levi_add_smul (w := w) (C - m) (d₁.div_const 2) d₂
  rw [FinChart.levi_half] at e₁
  have e₂ : (LocPot.ofFun (fun y => v y / 2) + φ.locPot.rsmul C).φ y ∘ c'.finChart.symm =
      fun z => (((φ.pow m).addFn v).φ (fun _ => pick φ.isLB y) ∘ c'.finChart.symm) z / 2 +
        (C - m) * (φ.locPot.φ y ∘ c'.finChart.symm) z := by
    funext z
    have := φ.zpow_φ (m : ℤ) (fun _ => pick φ.isLB y) (c'.finChart.symm z)
    change v (c'.finChart.symm z) / 2 + C * (φ.φ (pick φ.isLB y) (c'.finChart.symm z) / 2) =
      ((φ.zpow (m : ℤ)).φ (fun _ => pick φ.isLB y) (c'.finChart.symm z) + v (c'.finChart.symm z)) / 2 +
        (C - m) * (φ.φ (pick φ.isLB y) (c'.finChart.symm z) / 2)
    rw [this]
    push_cast
    ring
  rw [e₂, e₁] at h₁
  nlinarith [mul_nonneg hmC h₂]

theorem strictPos_fsO1 (N : ℕ) (R : AnRead (PSpace.str k N) σ N) :
    (ProjAn.fsO1 k σ N).StrictPos R := fun i c y hy ξ h0 => by
  have := ProjPos.fubiniStudy_weight_pullback_closed_immersion_strictPos (σ := σ) (𝟙 _) (Category.id_comp (PSpace.str k N)) R
    (fun _ => i) c y ⟨hy.1, mem_ptsIn.2 (Set.mem_iInter.2 fun _ => mem_ptsIn.1 hy.2)⟩ ξ h0
  have e (z) : ((ProjAn.fsO1 k σ N).pull (𝟙 _) (Category.id_comp (PSpace.str k N))).φ (fun _ => i) z =
      (ProjAn.fsO1 k σ N).φ i z := by
    refine (Weight.pull_φ _ _ _ _ _).trans ?_
    have e : PtsOver.map (𝟙 _) (Category.id_comp (PSpace.str k N)) _ z = z :=
      Subtype.ext (Category.comp_id _)
    erw [e]
  simpa only [e] using this

theorem exists_semiPosReg_fubiniStudy : ∀ (k : Type) [CommRing k] (σ : k →+* ℂ) (N : ℕ) (v : CxPts (PSpace.str k N) σ → ℝ), (∀ y, CInfAt v y) → ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ((((ProjSpace.hermitianTwistingSheaf k N).φ σ).pow m).addFn v).SemiPosReg N := fun k _ σ N v hv =>
  haveI : T2Space (CxPts (PSpace.str k N) σ) :=
    CxPts.t2Space_cxPts_of_isProjOver σ ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩
  exists_semiPosReg_pow_addFn (AnRead.all _ σ N)
    ((Weight.isCInf_iff_isSmooth _).1 ((ProjSpace.hermitianTwistingSheaf k N).cInf σ)) (strictPos_fsO1 N _) hv

end GlobalTheory.WeightShift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiPosFubiniStudyPowerAddSmoothFnStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semiPos_fubiniStudy_power_add_smooth_fn : ∀ (k : Type) [CommRing k] (σ : k →+* ℂ) (N : ℕ) (v : CxPts (PSpace.str k N) σ → ℝ), (∀ y, CInfAt v y) → ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ((((ProjSpace.hermitianTwistingSheaf k N).φ σ).pow m).addFn v).SemiPosReg N := by
  first | exact @GlobalTheory.WeightShift.exists_semiPosReg_fubiniStudy | exact GlobalTheory.WeightShift.exists_semiPosReg_fubiniStudy | (intros; apply GlobalTheory.WeightShift.exists_semiPosReg_fubiniStudy <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianEndExtendingAbelianSchemeEnd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianEndExtendingAbelianSchemeEnd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical
open Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.Poinc.Sep.Spz

theorem endOn_exists : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), (U₀ : Set M.Z).Nonempty → ∀ f : ρ.P.A ⟶ ρ.P.A, IsMonHom f → ∃ Fm : FinalForm.G ⟶ FinalForm.G, EndOn FinalForm f Fm := by
  intro o' Ω _ _ _ _ S ρ M U₀ EE FinalForm hU f₁ hf₁
  have : IsMonHom f₁ := hf₁
  have hr : Set.range M.pt ⊆ Set.range U₀.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact M.top_le_preimage_pt hU (x := w) trivial
  let x : Sp Ω ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι M.pt hr
  have hx : x ≫ U₀.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  let Q := (Over.pullback FinalForm.u₀).obj ρ.P.A
  let ν : pullback FinalForm.G.hom M.pt ⟶ pullback ρ.P.A.hom FinalForm.u₀ :=
    FinalForm.cart.1.lift (pullback.fst FinalForm.G.hom M.pt) (pullback.snd FinalForm.G.hom M.pt ≫ x)
             (by rw [pullback.condition, Category.assoc, hx])
  have hν₁ : ν ≫ FinalForm.φ = pullback.fst FinalForm.G.hom M.pt := FinalForm.cart.1.lift_fst _ _ _
  have hν₂ : ν ≫ Q.hom = pullback.snd FinalForm.G.hom M.pt ≫ x := FinalForm.cart.1.lift_snd _ _ _
  have gη : IsGrpPullback ((Over.pullback M.pt).obj FinalForm.G) FinalForm.G (x ≫ U₀.ι) (ν ≫ FinalForm.φ) :=
    (isGrpPullback_pullback FinalForm.G M.pt).congr hx.symm hν₁.symm
  have gν : IsGrpPullback ((Over.pullback M.pt).obj FinalForm.G) Q x ν := FinalForm.cart.cancel gη hν₂
  have gψ := gν.comp (isGrpPullback_pullback ρ.P.A FinalForm.u₀)
  obtain ⟨w', hw', pa⟩ := GlobalTheory.SymBaseChange.exists_endo gψ f₁
  have hw'l : w'.left ≫ ν ≫ pullback.fst ρ.P.A.hom FinalForm.u₀ = (ν ≫ pullback.fst ρ.P.A.hom FinalForm.u₀) ≫ f₁.left := by
    have := congrArg (fun z => z.left) (pa (𝟙 _))
    simpa [pushPt] using this
  obtain ⟨F, ⟨hF, hFw⟩, -⟩ := FinalForm.endo w' hw'
  refine ⟨F, ?_⟩
  unfold EndOn
  have hsep : IsSeparated FinalForm.G.hom := FinalForm.semi.separated
  have hsm : Smooth FinalForm.G.hom := FinalForm.semi.smooth
  have hQf : Flat Q.hom := MorphismProperty.of_isPullback (P := @Flat) FinalForm.cart.1 inferInstance
  have hqc : QuasiCompact M.pt := by
    have : IsSeparated M.s := M.sep
    have : QuasiCompact (M.pt ≫ M.s) := by rw [M.pt_s]; infer_instance
    exact QuasiCompact.of_comp M.pt M.s
  have hdom : IsSchemeTheoreticallyDominant M.pt := .of_isDominant M.pt
  let p : pullback ρ.P.A.hom FinalForm.u₀ ⟶ M.Z := Q.hom ≫ U₀.ι
  let j := pullback.fst p M.pt
  have hj : j ≫ Q.hom = pullback.snd p M.pt ≫ x := by
    rw [← cancel_mono U₀.ι, Category.assoc, Category.assoc, hx]
    exact pullback.condition
  let k : pullback p M.pt ⟶ pullback FinalForm.G.hom M.pt := pullback.lift (j ≫ FinalForm.φ) (pullback.snd p M.pt) (by
    rw [Category.assoc, FinalForm.cart.1.w]; exact pullback.condition)
  have hk₁ : k ≫ pullback.fst FinalForm.G.hom M.pt = j ≫ FinalForm.φ := pullback.lift_fst _ _ _
  have hk₂ : k ≫ pullback.snd FinalForm.G.hom M.pt = pullback.snd p M.pt := pullback.lift_snd _ _ _
  have hkν : k ≫ ν = j := by
    apply FinalForm.cart.1.hom_ext
    · rw [Category.assoc, hν₁, hk₁]
    · rw [Category.assoc, hν₂, ← Category.assoc, hk₂, hj]
  have hF' : ((Over.pullback M.pt).map F).left ≫ pullback.fst FinalForm.G.hom M.pt = pullback.fst FinalForm.G.hom M.pt ≫ F.left := by
    simp only [Over.pullback_map_left, pullback.lift_fst]
  have hw₂ : w'.left ≫ pullback.snd FinalForm.G.hom M.pt = pullback.snd FinalForm.G.hom M.pt := Over.w w'
  have key : k ≫ w'.left ≫ ν = j ≫ ((Over.pullback FinalForm.u₀).map f₁).left := by
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [hw'l]
      simp only [← Category.assoc]
      rw [hkν]
      simp only [Category.assoc, Over.pullback_map_left]
      exact congrArg (j ≫ ·) (pullback.lift_fst _ _ _).symm
    · have e : ((Over.pullback FinalForm.u₀).map f₁).left ≫ Q.hom = Q.hom := Over.w ((Over.pullback FinalForm.u₀).map f₁)
      show (k ≫ w'.left ≫ ν) ≫ Q.hom = (j ≫ ((Over.pullback FinalForm.u₀).map f₁).left) ≫ Q.hom
      simp only [Category.assoc]
      rw [hν₂, e, hj, ← Category.assoc w'.left, hw₂, ← Category.assoc, hk₂]
  refine GlobalTheory.SS.GenProj.ext_of_dense j FinalForm.G.hom ?_ ?_
  · have e1 : j ≫ FinalForm.φ ≫ F.left = k ≫ w'.left ≫ ν ≫ FinalForm.φ := by
      rw [hν₁, ← hFw, hF', ← Category.assoc k, hk₁, Category.assoc]
    rw [e1]
    simp only [← Category.assoc] at key ⊢
    rw [key]
  · rw [Category.assoc, Category.assoc, Over.w F, FinalForm.cart.1.w, ← Category.assoc, Over.w]

end GlobalTheory.Poinc.Sep.Spz
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianEndExtendingAbelianSchemeEndStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semiAbelianEnd_extending_abelianSchemeEnd : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), (U₀ : Set M.Z).Nonempty → ∀ f : ρ.P.A ⟶ ρ.P.A, IsMonHom f → ∃ Fm : FinalForm.G ⟶ FinalForm.G, EndOn FinalForm f Fm := by
  first | exact @GlobalTheory.Poinc.Sep.Spz.endOn_exists | exact GlobalTheory.Poinc.Sep.Spz.endOn_exists | (intros; apply GlobalTheory.Poinc.Sep.Spz.endOn_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusSpreadLatticeMapCommutesEndomorphisms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusSpreadLatticeMapCommutesEndomorphisms
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

noncomputable section

namespace GlobalTheory.Poinc.Sep.Spz

theorem endU_gtTorus_comp {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {D : DegData V (maximalIdeal V)}
    {A : PolAV (Sp (FractionRing V))} {G : Over (Sp V)} [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G)
    (E : EndU U.toUnifPre) {κ : Type} [Field κ] {a : V →+* κ} (ha : ∀ x ∈ maximalIdeal V ^ (0 + 1), a x = 0)
    {G₀ : Over (Sp κ)} [GrpObj G₀] {φ : G₀.left ⟶ G.left} (h : IsGrpPullback G₀ G (spMap a) φ) (f₀ : G₀ ⟶ G₀)
    (hf : f₀.left ≫ φ = φ ≫ E.aG.left) :
    GlobalTheory.TorusPart.gtTorus (U.gt 0) ha h ≫ f₀ =
      GlobalTheory.SplitTorus.torusMap (Sp κ) E.h ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) ha h := by
  obtain ⟨t, ht, hi⟩ := E.i_lin 0
  have htm := GlobalTheory.Poinc.Eq8.eq_torusMap_of_torusEndOf E.h t ht
  have k := GlobalTheory.TorusPart.isGrpPullback_thickLift ha h
  have e : f₀.left ≫ GlobalTheory.TorusPart.thickLift ha h =
      GlobalTheory.TorusPart.thickLift ha h ≫ ((Over.pullback (thick V (maximalIdeal V) 0)).map E.aG).left := by
    apply pullback.hom_ext
    · rw [Category.assoc, GlobalTheory.TorusPart.thickLift_fst, hf, Category.assoc]
      simp only [GlobalTheory.TorusPart.thickLift, Over.pullback_map_left, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    · simp only [GlobalTheory.TorusPart.thickLift, Over.pullback_map_left]
      rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc,
        Over.w]
  have hc := GlobalTheory.TorusPart.pullTorus_comp k k _ f₀ e (U.gt 0).i
  unfold GlobalTheory.TorusPart.gtTorus
  rw [← hc, hi, htm, GlobalTheory.TorusPart.pullTorus_torusMap_comp]

def pullEnd {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (u : G ⟶ G) : G' ⟶ G' :=
  Over.homMk (h.1.lift (φ ≫ u.left) G'.hom (by rw [Category.assoc, Over.w, h.1.w])) (h.1.lift_snd _ _ _)

theorem pullEnd_left {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (u : G ⟶ G) : (pullEnd h u).left ≫ φ = φ ≫ u.left :=
  h.1.lift_fst _ _ _

theorem over_of_two_pullbacks {B S₁ : Scheme.{0}} {H : Over B} {G₁ : Over S₁} {X Y : Scheme.{0}} {ξ₁ : S₁ ⟶ B}
    {β₁ : G₁.left ⟶ H.left} (h₁ : IsPullback β₁ G₁.hom H.hom ξ₁) {φW : Y ⟶ H.left} {n : X ⟶ Y} {n₁ : X ⟶ G₁.left}
    {f₀ : X ⟶ X} {FW : Y ⟶ Y} {Fm : H.left ⟶ H.left} {a : G₁.left ⟶ G₁.left}
    (e1 : f₀ ≫ n = n ≫ FW) (e2 : FW ≫ φW = φW ≫ Fm) (e3 : n ≫ φW = n₁ ≫ β₁) (e4 : a ≫ β₁ = β₁ ≫ Fm)
    (e5 : a ≫ G₁.hom = G₁.hom) (e6 : f₀ ≫ n₁ ≫ G₁.hom = n₁ ≫ G₁.hom) : f₀ ≫ n₁ = n₁ ≫ a := by
  apply h₁.hom_ext
  · rw [Category.assoc, ← e3, ← Category.assoc, e1, Category.assoc, e2, ← Category.assoc, e3, Category.assoc,
      Category.assoc, e4]
  · rw [Category.assoc, e6, Category.assoc, e5]

theorem spread₂_endU_comm : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], GlobalTheory.Mum.Base V₁ → ∀ (G₁ : Over (Sp V₁)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (D₁ : DegData V₁ (maximalIdeal V₁)) (A₁ : PolAV (Sp (FractionRing V₁))) (U₁ : Unif (maximalIdeal V₁) D₁ A₁ G₁) (ξ₁ : Sp V₁ ⟶ B) (β₁ : G₁.left ⟶ H.left), IsGrpPullback G₁ H ξ₁ β₁ → ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂], GlobalTheory.Mum.Base V₂ → ∀ (G₂ : Over (Sp V₂)) [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₂ → ∀ (D₂ : DegData V₂ (maximalIdeal V₂)) (A₂ : PolAV (Sp (FractionRing V₂))) (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (ξ₂ : Sp V₂ ⟶ B) (β₂ : G₂.left ⟶ H.left), IsGrpPullback G₂ H ξ₂ β₂ → ∀ ρ : D₂.toPre.X →+ D₁.toPre.X, Spread₂ H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ρ → ∀ (Fm : H ⟶ H) (E₁ : EndU U₁.toUnifPre) (E₂ : EndU U₂.toUnifPre), E₁.aG.left ≫ β₁ = β₁ ≫ Fm.left → E₂.aG.left ≫ β₂ = β₂ ≫ Fm.left → ∀ y, ρ (E₂.h y) = E₁.h (ρ y) := by
  intro B H _ _ hH V₁ _ _ _ hV₁ G₁ _ _ hG₁ D₁ A₁ U₁ ξ₁ β₁ h₁ V₂ _ _ _ hV₂ G₂ _ _ hG₂ D₂ A₂ U₂ ξ₂ β₂ h₂ ρ hsp
    Fm E₁ E₂ hE₁ hE₂
  obtain ⟨W, _, _, _, ψ, GW, _, _, φW, j, Ω, _, α, b₁, hb₁, GΩ, _, n, hn, n₁, hn₁, κ, _, c, b₂, hb₂, Gκ, _, m, hm, m₂, hm₂,
    hW, hj, hα, -, -, -, hnφ, hmφ, hjΩ, hjκ⟩ := hsp
  let FW := pullEnd hW Fm
  have hFW : FW.left ≫ φW = φW ≫ Fm.left := pullEnd_left hW Fm

  have key : j ≫ FW = GlobalTheory.SplitTorus.torusMap _ E₁.h ≫ j := by
    have : IsSchemeTheoreticallyDominant (spMap α) :=
      GlobalTheory.ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _ hα
    have : IsSeparated H.hom := hH.separated
    have : IsSeparated GW.hom := MorphismProperty.of_isPullback hW.1 this
    have : Flat (splitTorusAff ZU D₁.toPre.X).hom :=
      (GlobalTheory.ExtUnique.splitTorusAff_flat_and_isSeparated _ _).1
    have : Flat (splitTorus (Sp W) D₁.toPre.X).hom := inferInstanceAs (Flat (pullback.snd _ _))
    refine GlobalTheory.ExtUnique.over_hom_ext_of_isPullback (GlobalTheory.SplitTorus.isPullback_bcMap (spMap α) _) ?_
    let FΩ := pullEnd hn FW
    have hFΩ : FΩ.left ≫ n = n ≫ FW.left := pullEnd_left hn FW
    have hover : FΩ.left ≫ n₁ = n₁ ≫ E₁.aG.left :=
      over_of_two_pullbacks h₁.1 hFΩ hFW hnφ hE₁ (Over.w E₁.aG)
        (by rw [hn₁.1.w, ← Category.assoc, Over.w FΩ])
    have e1 := GlobalTheory.TorusPart.pullTorus_comp hn hn FW FΩ hFΩ j
    have e2 := GlobalTheory.TorusPart.pullTorus_torusMap_comp hn j E₁.h
    have e3 := endU_gtTorus_comp U₁ E₁ hb₁ hn₁ FΩ hover
    rw [hjΩ, e3] at e1
    rw [hjΩ] at e2
    rw [← GlobalTheory.TorusPart.pullTorus_left hn, ← GlobalTheory.TorusPart.pullTorus_left hn, e1, e2]

  let Fκ := pullEnd hm FW
  have hFκ : Fκ.left ≫ m = m ≫ FW.left := pullEnd_left hm FW
  have hover₂ : Fκ.left ≫ m₂ = m₂ ≫ E₂.aG.left :=
    over_of_two_pullbacks h₂.1 hFκ hFW hmφ hE₂ (Over.w E₂.aG)
      (by rw [hm₂.1.w, ← Category.assoc, Over.w Fκ])
  have hmono := (GlobalTheory.TorusPart.mono_gtTorus_and_factor (U₂.gt 0) hb₂ hm₂).1
  have e := congrArg (GlobalTheory.TorusPart.pullTorus hm) key
  rw [GlobalTheory.TorusPart.pullTorus_comp hm hm FW Fκ hFκ j, GlobalTheory.TorusPart.pullTorus_torusMap_comp hm j, hjκ, Category.assoc,
    endU_gtTorus_comp U₂ E₂ hb₂ hm₂ Fκ hover₂, ← Category.assoc, ← Category.assoc,
    ← GlobalTheory.SplitTorus.torusMap_comp, ← GlobalTheory.SplitTorus.torusMap_comp] at e
  have : Nonempty (Sp κ) := inferInstance
  have e' := GlobalTheory.SplitTorus.torusMap_injective ((cancel_mono _).1 e)
  intro y
  exact DFunLike.congr_fun e' y

end GlobalTheory.Poinc.Sep.Spz
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusSpreadLatticeMapCommutesEndomorphismsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_spread_lattice_map_commutes_endomorphisms : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], GlobalTheory.Mum.Base V₁ → ∀ (G₁ : Over (Sp V₁)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (D₁ : DegData V₁ (maximalIdeal V₁)) (A₁ : PolAV (Sp (FractionRing V₁))) (U₁ : Unif (maximalIdeal V₁) D₁ A₁ G₁) (ξ₁ : Sp V₁ ⟶ B) (β₁ : G₁.left ⟶ H.left), IsGrpPullback G₁ H ξ₁ β₁ → ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂], GlobalTheory.Mum.Base V₂ → ∀ (G₂ : Over (Sp V₂)) [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₂ → ∀ (D₂ : DegData V₂ (maximalIdeal V₂)) (A₂ : PolAV (Sp (FractionRing V₂))) (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (ξ₂ : Sp V₂ ⟶ B) (β₂ : G₂.left ⟶ H.left), IsGrpPullback G₂ H ξ₂ β₂ → ∀ ρ : D₂.toPre.X →+ D₁.toPre.X, Spread₂ H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ρ → ∀ (Fm : H ⟶ H) (E₁ : EndU U₁.toUnifPre) (E₂ : EndU U₂.toUnifPre), E₁.aG.left ≫ β₁ = β₁ ≫ Fm.left → E₂.aG.left ≫ β₂ = β₂ ≫ Fm.left → ∀ y, ρ (E₂.h y) = E₁.h (ρ y) := by
  first | exact @GlobalTheory.Poinc.Sep.Spz.spread₂_endU_comm | exact GlobalTheory.Poinc.Sep.Spz.spread₂_endU_comm | (intros; apply GlobalTheory.Poinc.Sep.Spz.spread₂_endU_comm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompProdOfFn
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FirstOrderValue

def evalSq {S : Type} [CommRing S] (e : S) (he : e * e = 0) : DualNumber S →+* S where
  toFun z := z.fst + e * z.snd
  map_one' := by simp
  map_mul' a b := by
    simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, op_smul_eq_smul]
    linear_combination (-(a.snd * b.snd)) * he
  map_zero' := by simp
  map_add' a b := by simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add]; ring

theorem evalSq_apply {S : Type} [CommRing S] (e : S) (he : e * e = 0) (z : DualNumber S) :
    evalSq e he z = z.fst + e * z.snd := rfl

theorem dual_apply {R S : Type} [CommRing R] [CommRing S] (f : DualNumber R →+* S) (z : DualNumber R) :
    f z = f (TrivSqZeroExt.inl z.fst) + f (TrivSqZeroExt.inl z.snd) * f DualNumber.eps := by
  have hz : z = TrivSqZeroExt.inl z.fst + TrivSqZeroExt.inl z.snd * DualNumber.eps := by
    ext <;> simp
  conv_lhs => rw [hz]
  rw [map_add (f := _), map_mul]

theorem comp_prod_ofFn {C : Type*} [Category C] [CartesianMonoidalCategory C] {M A B : C} [MonObj M]
    (k : A ⟶ B) : ∀ {m : ℕ} (u : Fin m → (B ⟶ M)), k ≫ (List.ofFn u).prod = (List.ofFn fun i => k ≫ u i).prod
  | 0, u => by simp [MonObj.comp_one]
  | m + 1, u => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, MonObj.comp_mul, comp_prod_ofFn]

end GlobalTheory.FirstOrderValue

namespace GlobalTheory.FirstOrderValue

theorem valR_mul_comb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart U) (v i)) → ∀ (c : Fin n → Γ(X, U.1)) (x : tEpsG (chart U) ⟶ t.G), IsCombAtG t (chart U) v c x.left → (∀ (S : Type) [CommRing S] (ψ : DualNumber Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (a : Over.mk (g₀ ≫ t.G.hom) ⟶ tEpsG (chart U)) (w : Fin n → (Sp (DualNumber S) ⟶ t.G.left)), a.left = spMap ψ → (∀ b, IsTranslate t (ψ.comp (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1)))) g₀ (v b) (w b)) → ∀ (O : t.G.left.Opens) (f : Γ(t.G.left, O)), ⊤ ≤ g₀ ⁻¹ᵁ O → ⊤ ≤ ((a ≫ x) * (Over.homMk g₀ rfl : Over.mk (g₀ ≫ t.G.hom) ⟶ t.G)).left ⁻¹ᵁ O ∧ valR ((a ≫ x) * (Over.homMk g₀ rfl : Over.mk (g₀ ≫ t.G.hom) ⟶ t.G)).left O f = valR g₀ O f + ψ DualNumber.eps * ∑ b, ψ (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1)) (c b)) * (valR (w b) O f).snd) := by
  intro E _ _ _ H X t U n v hv c x hx S _ ψ g₀ a w ha hw O f hO
  obtain ⟨φ, hφ⟩ : ∃ φ : Γ(X, U.1) →+* S, φ = ψ.comp (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) := ⟨_, rfl⟩
  rw [← hφ] at hw
  obtain ⟨e, hedef⟩ : ∃ e : S, e = ψ DualNumber.eps := ⟨_, rfl⟩
  rw [← hedef]
  have he : e * e = 0 := by rw [hedef, ← map_mul, DualNumber.eps_mul_eps, map_zero]
  have hφs : ∀ s, φ s = ψ (TrivSqZeroExt.inl s) := fun s => by
    rw [hφ, RingHom.comp_apply, TrivSqZeroExt.algebraMap_eq_inl]

  have hg₀ : g₀ ≫ t.G.hom = spMap φ ≫ chart U := by
    have h1 : a.left ≫ spMap (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) ≫ chart U = g₀ ≫ t.G.hom := Over.w a
    rw [← h1, ha, ← Category.assoc, GlobalTheory.KSLin.spMap_comp_spMap, hφ]
  choose g'' v'' hg'' hv'' hw'' using hw
  let g' : tEpsG (g₀ ≫ t.G.hom) ⟶ t.G :=
    Over.homMk (spMap (algebraMap S (DualNumber S)) ≫ g₀) (Category.assoc _ _ _)
  have hgg : ∀ b, g'' b = g' := fun b => Over.OverMorphism.ext (hg'' b)

  let h : tEpsG (g₀ ≫ t.G.hom) ⟶ Over.mk (chart U) :=
    Over.homMk (spMap (algebraMap S (DualNumber S)) ≫ spMap φ) (by
      show (spMap _ ≫ spMap φ) ≫ chart U = spMap _ ≫ g₀ ≫ t.G.hom
      rw [Category.assoc, hg₀])
  have hy0 : ∀ b, smT (g₀ ≫ t.G.hom) 0 (v'' b) = 1 := by
    intro b
    apply Over.OverMorphism.ext
    have h1 : (smT (g₀ ≫ t.G.hom) 0 (v'' b)).left = spMap (epsMul 0) ≫ (v'' b).left := rfl
    have e1 : (epsMul (0 : S)).comp (dualMap φ) = ((algebraMap S (DualNumber S)).comp φ).comp
        (TrivSqZeroExt.fstHom Γ(X, U.1) Γ(X, U.1) Γ(X, U.1)).toRingHom := by
      apply RingHom.ext; intro z; ext <;> simp [epsMul, dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    rw [h1, hv'' b, ← Category.assoc, GlobalTheory.KSLin.spMap_comp_spMap, e1, ← GlobalTheory.KSLin.spMap_comp_spMap,
      ← GlobalTheory.KSLin.spMap_comp_spMap, Category.assoc, Category.assoc, (hv b).2]
    have h2 : (h ≫ (1 : Over.mk (chart U) ⟶ t.G)).left = (1 : tEpsG (g₀ ≫ t.G.hom) ⟶ t.G).left :=
      congrArg (fun k : tEpsG (g₀ ≫ t.G.hom) ⟶ t.G => k.left) (MonObj.comp_one h)
    have h3 : (spMap (algebraMap S (DualNumber S)) ≫ spMap φ) ≫ (1 : Over.mk (chart U) ⟶ t.G).left =
        (1 : tEpsG (g₀ ≫ t.G.hom) ⟶ t.G).left := h2
    rw [← h3, Category.assoc]

  obtain ⟨u, hu, hux⟩ := hx
  obtain rfl : x = (List.ofFn u).prod := (Over.OverMorphism.ext hux).symm

  let ρ := evalSq e he
  have hρψ : ∀ r, ψ.comp (epsMul r) = (ρ.comp (epsMul (φ r))).comp (dualMap φ) := by
    intro r
    apply RingHom.ext; intro z
    simp only [RingHom.comp_apply]
    rw [dual_apply ψ, ← hedef, evalSq_apply]
    simp [epsMul, dualMap, hφs]
    ring
  have hsp : spMap ρ ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _ := by
    rw [GlobalTheory.KSLin.spMap_comp_spMap]
    have : ρ.comp (algebraMap S (DualNumber S)) = RingHom.id S := by
      ext s; simp [ρ, evalSq_apply, TrivSqZeroExt.algebraMap_eq_inl]
    rw [this]; simp [spMap]
  let ρh : Over.mk (g₀ ≫ t.G.hom) ⟶ tEpsG (g₀ ≫ t.G.hom) :=
    Over.homMk (spMap ρ) (by
      show spMap ρ ≫ spMap (algebraMap S (DualNumber S)) ≫ g₀ ≫ t.G.hom = g₀ ≫ t.G.hom
      rw [← Category.assoc, hsp, Category.id_comp])
  have hu' : ∀ b, a ≫ u b = ρh ≫ smT (g₀ ≫ t.G.hom) (φ (c b)) (v'' b) := by
    intro b
    apply Over.OverMorphism.ext
    have h1 : (smT (g₀ ≫ t.G.hom) (φ (c b)) (v'' b)).left = spMap (epsMul (φ (c b))) ≫ (v'' b).left := rfl
    simp only [Over.comp_left]
    rw [h1, hv'' b, hu b, ha]
    show spMap ψ ≫ spMap (epsMul (c b)) ≫ v b = spMap ρ ≫ spMap (epsMul (φ (c b))) ≫ spMap (dualMap φ) ≫ v b
    simp only [← Category.assoc, GlobalTheory.KSLin.spMap_comp_spMap, hρψ]
  have hg'eq : (Over.homMk g₀ rfl : Over.mk (g₀ ≫ t.G.hom) ⟶ t.G) = ρh ≫ g' := by
    apply Over.OverMorphism.ext
    show g₀ = spMap ρ ≫ spMap (algebraMap S (DualNumber S)) ≫ g₀
    rw [← Category.assoc, hsp, Category.id_comp]
  have hmain : (a ≫ (List.ofFn u).prod) * (Over.homMk g₀ rfl : Over.mk (g₀ ≫ t.G.hom) ⟶ t.G) =
      ρh ≫ (g' * (List.ofFn fun b => smT (g₀ ≫ t.G.hom) (φ (c b)) (v'' b)).prod) := by
    rw [comp_prod_ofFn, hg'eq, MonObj.comp_mul, comp_prod_ofFn, mul_comm]
    simp only [hu']
  have hP1 := GlobalTheory.KSLin.snd_sectionValue_translate_list_prod_induction g₀ g' rfl O hO f n v'' (fun b => φ (c b)) hy0
  have hQ0 : smT (g₀ ≫ t.G.hom) 0 (g' * (List.ofFn fun b => smT (g₀ ≫ t.G.hom) (φ (c b)) (v'' b)).prod) = g' := by
    rw [smT_mul, GlobalTheory.KSLin.smT_const g₀ g' rfl, hP1.1, _root_.mul_one]
  have hQ : ⊤ ≤ (Over.Hom.left (g' * (List.ofFn fun b => smT (g₀ ≫ t.G.hom) (φ (c b)) (v'' b)).prod)) ⁻¹ᵁ O :=
    GlobalTheory.KSLin.top_le_of_smT_zero g₀ g' rfl O hO _ hQ0
  have hfst := GlobalTheory.KSLin.fst_comp_of_smT_zero g₀ g' rfl _ hQ0
  have hwb : ∀ b, (g' * v'' b).left = w b := fun b => by rw [← hgg b]; exact hw'' b
  rw [hmain, Over.comp_left]
  show ⊤ ≤ (spMap ρ ≫ _) ⁻¹ᵁ O ∧ valR (spMap ρ ≫ _) O f = _
  refine ⟨GlobalTheory.TanDeriv.comp_top_le ρ _ O hQ, ?_⟩
  have hOg : ⊤ ≤ g₀ ⁻¹ᵁ O := hO
  rw [GlobalTheory.KSLin.valR_spMap_comp ρ _ O hQ f, evalSq_apply, hP1.2]
  conv_rhs => rw [← hfst, GlobalTheory.KSLin.valR_spMap_comp _ _ O hQ f]
  simp only [hwb, hφs, TrivSqZeroExt.algebraMap_eq_inl]
  rfl

end GlobalTheory.FirstOrderValue
end
end
