module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusExtensionPointsDivisible
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelFamilyTangentDimensionBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverFibreTorsorTrivialLevelChanges
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolyMaximalCompactCasimirKillsKType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableZetaIntegralMatrixSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCharacterOfTrivialNearOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointPicardClassEqTranslateOfTrivialLambda
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointPicardClassEqTranslateOfTrivialLambda
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open MonoidalCategory CartesianMonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic (Pic cls lam)
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.PrimitiveOverField
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PointTranslate

theorem exists_point_cls_eq_lam : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ (L : LB B.left) (hL : L.IsLB), Out.KTriv B L → ∀ (O : LB B.left) (hO : O.IsLB), lam (cls O hO) (fst B B) (snd B B) = 0 → ∃ x : 𝟙_ (Over (Sp K)) ⟶ B, cls O hO = lam (cls L hL) (toUnit B ≫ x) (𝟙 B) := by
  intro K _ _ B _ hB L hL hK O hO lamO
  by_contra hno
  have := hB.comm
  have := hB.smooth
  have := hB.proper
  have hpr : IsProjBy B.hom := GlobalTheory.T.isProjectiveOverRingByCharts_abelian_variety K B hB
  have hproj : ∀ (R : Type) [CommRing R] (u : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K)) (X : Scheme.{0})
      (π : X ⟶ B.left) (f : X ⟶ Spec (CommRingCat.of R)), IsPullback π f B.hom u → IsProjBy f :=
    fun R _ u X π f h => GlobalTheory.AbLaw.CubeProj.isProjBy_baseChange hpr h
  have hΘ := GlobalTheory.exists_gen_theta_of_isAbelianScheme K B hB L hL
  obtain ⟨F, hF, eF⟩ := cls_surj (lam (cls L hL) (fst B B) (snd B B) -
    CechPic.pull (snd B B).left (cls O hO))
  have hpq : IsPullback (fst B B).left (snd B B).left B.hom B.hom := IsPullback.of_hasPullback _ _
  have cst_left : ∀ x : 𝟙_ _ ⟶ B, (toUnit B ≫ x).left = B.hom ≫ x.left := fun x =>
    congrArg (· ≫ x.left) ((Category.comp_id _).symm.trans (Over.w (toUnit B)))
  have s₁ : ∀ x : 𝟙_ _ ⟶ B, cls _ (pull_isLB hF (lift (toUnit B ≫ x) (𝟙 B)).left) =
      lam (cls L hL) (toUnit B ≫ x) (𝟙 B) - cls O hO := fun x => by
    rw [cls_pull hF, eF, map_sub, pull_lam, ← pull_comp, ← Over.comp_left, lift_fst, lift_snd, Over.id_left, pull_id]
  have s₂ : ∀ x : 𝟙_ _ ⟶ B, cls _ (pull_isLB hF (lift (𝟙 B) (toUnit B ≫ x)).left) =
      lam (cls L hL) (toUnit B ≫ x) (𝟙 B) := fun x => by
    rw [cls_pull hF, eF, map_sub, pull_lam, ← pull_comp, ← Over.comp_left, lift_fst, lift_snd, pull_const, sub_zero,
      lam_comm]
  have total : Ac ((fst B B).left ≫ B.hom) F := by
    refine (GlobalTheory.T.lineBundle_product_acyclic_of_affine_base_acyclic K _ _ _ _ _ _ _ hpq inferInstance inferInstance inferInstance inferInstance F hF).1
      fun R _ t Y π f h ht => ac_of_slices hproj hpq h hF fun x hx _ => ?_
    let x' : 𝟙_ _ ⟶ B := Over.homMk x hx
    refine ⟨(lift (toUnit B ≫ x') (𝟙 B)).left, ?_, ?_, ac_of_primitive hB hpr (pull_isLB hF _) ?_ ?_⟩
    · exact (congrArg CommaMorphism.left (lift_fst (toUnit B ≫ x') (𝟙 B))).trans (cst_left x')
    · exact congrArg CommaMorphism.left (lift_snd (toUnit B ≫ x') (𝟙 B))
    · rw [s₁, lam_sub, lam_lam hL hΘ, lamO, sub_zero]
    · rw [s₁, sub_ne_zero]
      exact fun e => hno ⟨x', e.symm⟩
  rw [hpq.w] at total
  let o : Spec (CommRingCat.of K) ⟶ B.left := η[B].left
  have ho : o ≫ B.hom = 𝟙 _ := Over.w η[B]
  have hcl : IsClosed ({o (IsLocalRing.closedPoint K)} : Set B.left) := by
    have : IsClosedImmersion (o ≫ B.hom) := by rw [ho]; infer_instance
    have : IsClosedImmersion o := IsClosedImmersion.of_comp o B.hom
    have h := o.isClosedEmbedding.isClosedMap {IsLocalRing.closedPoint K}
      (by rw [show ({IsLocalRing.closedPoint K} : Set (Spec (CommRingCat.of K))) = Set.univ from
        Set.eq_univ_of_forall fun z => Subsingleton.elim (α := PrimeSpectrum K) _ _]; exact isClosed_univ)
    exact (congrArg IsClosed Set.image_singleton).mp h
  have all := (GlobalTheory.T.lineBundle_product_acyclic_of_affine_base_acyclic K _ _ _ _ _ _ _ hpq.flip inferInstance inferInstance inferInstance inferInstance F hF).2
    _ hcl (fun R _ t Y π f h ht hne => ac_of_slices hproj hpq.flip h hF fun x hx hr => by
      let x' : 𝟙_ _ ⟶ B := Over.homMk x hx
      refine ⟨(lift (𝟙 B) (toUnit B ≫ x')).left, ?_, ?_, ac_of_primitive hB hpr (pull_isLB hF _) ?_ ?_⟩
      · exact (congrArg CommaMorphism.left (lift_snd (𝟙 B) (toUnit B ≫ x'))).trans (cst_left x')
      · exact congrArg CommaMorphism.left (lift_fst (𝟙 B) (toUnit B ≫ x'))
      · rw [s₂, lam_lam hL hΘ]
      · rw [s₂]
        intro e
        have e₁ : x' = η[B] := (eq_one_of_lam_eq_zero hL hK x' e).trans (by
          rw [Hom.one_def, toUnit_unit, Category.id_comp])
        have e₂ : x = o := congrArg CommaMorphism.left e₁
        obtain ⟨y, hy⟩ := hr (IsLocalRing.closedPoint K)
        exact hne y (e₂ ▸ hy)) total
  have hs := ac_slice hproj hpq.flip hF all o ho (lift (𝟙 B) (toUnit B ≫ η[B])).left
    ((congrArg CommaMorphism.left (lift_snd (𝟙 B) (toUnit B ≫ η[B]))).trans (cst_left η[B]))
    (congrArg CommaMorphism.left (lift_fst (𝟙 B) (toUnit B ≫ η[B])))
  have : CompactSpace B.left := QuasiCompact.compactSpace_of_compactSpace B.hom
  have : Nonempty B.left := ⟨o (IsLocalRing.closedPoint K)⟩
  exact not_ac_of_cls_eq_zero _ (pull_isLB hF _) ((s₂ _).trans (lam_one_left _ _)) hs

end GlobalTheory.PointTranslate
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointPicardClassEqTranslateOfTrivialLambdaStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open MonoidalCategory CartesianMonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic (Pic cls lam)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_point_picardClass_eq_translate_of_trivial_lambda : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ (L : LB B.left) (hL : L.IsLB), Out.KTriv B L → ∀ (O : LB B.left) (hO : O.IsLB), lam (cls O hO) (fst B B) (snd B B) = 0 → ∃ x : 𝟙_ (Over (Sp K)) ⟶ B, cls O hO = lam (cls L hL) (toUnit B ≫ x) (𝟙 B) := by
  first | exact @GlobalTheory.PointTranslate.exists_point_cls_eq_lam | exact GlobalTheory.PointTranslate.exists_point_cls_eq_lam | (intros; apply GlobalTheory.PointTranslate.exists_point_cls_eq_lam <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitMinorTranslate
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitMinorTranslate
open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL

noncomputable section

namespace GlobalTheory.FullRankCoinv.UnitMinor

theorem det_one_updateCol_eq {K : Type} [Field K] {n : ℕ} (i : Fin n) (c : Fin n → K) :
    ((1 : Matrix (Fin n) (Fin n) K).updateCol i c).det = c i := by
  rw [← Matrix.cramer_apply, Matrix.cramer_one]; rfl

theorem exists_minor_det_ne_zero {K : Type} [Field K] {n d : ℕ} (Y : Matrix (Fin n) (Fin d) K)
    (hY : Y.rank = n) : ∃ f : Fin n ↪ Fin d, (Y.submatrix id f).det ≠ 0 := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K (fun j => Yᵀ j)
  have htop : Submodule.span K (Set.range (fun j => Yᵀ j)) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fin_fun]; rw [Matrix.rank_eq_finrank_span_cols] at hY; exact hY
  have hsp : ⊤ ≤ Submodule.span K (Set.range ((fun j => Yᵀ j) ∘ a)) := by rw [hspan, htop]
  let b := Module.Basis.mk hli hsp
  let e : κ ≃ Fin n := b.indexEquiv (Pi.basisFun K (Fin n))
  let f : Fin n ↪ Fin d := e.symm.toEmbedding.trans ⟨a, ha⟩
  refine ⟨f, ?_⟩
  have hli' : LinearIndependent K (fun i => (Y.submatrix id f)ᵀ i) := by
    have : (fun i => (Y.submatrix id f)ᵀ i) = ((fun j => Yᵀ j) ∘ a) ∘ e.symm := by
      funext i r; rfl
    rw [this]; exact hli.comp _ e.symm.injective
  have hu := Matrix.linearIndependent_cols_iff_isUnit.mp hli'
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero

theorem submatrix_mul_left {K : Type} [Field K] {n d : ℕ} (B : Matrix (Fin n) (Fin n) K)
    (Y : Matrix (Fin n) (Fin d) K) (g : Fin n ↪ Fin d) :
    (B * Y).submatrix id g = B * Y.submatrix id g := by
  ext r s; simp [Matrix.mul_apply]

theorem exists_GL_mul_mem_unitMinorSet (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n d : ℕ) (Y : Matrix (Fin n) (Fin d) k) (hY : Y.rank = n) :
    ∃ E : GL (Fin n) k, E.val * Y ∈ unitMinorSet k n d := by
  classical
  obtain ⟨f0, hf0⟩ := exists_minor_det_ne_zero Y hY
  haveI : Nonempty (Fin n ↪ Fin d) := ⟨f0⟩
  obtain ⟨f, hf⟩ := Finite.exists_max (fun g : Fin n ↪ Fin d => valuation k (Y.submatrix id g).det)
  have hAdet : (Y.submatrix id f).det ≠ 0 := by
    intro h0
    have h1 := hf f0
    simp only [h0, map_zero] at h1
    exact hf0 ((map_eq_zero _).mp (le_antisymm h1 zero_le'))
  have hAu : IsUnit (Y.submatrix id f).det := isUnit_iff_ne_zero.mpr hAdet
  let E : GL (Fin n) k := Matrix.GeneralLinearGroup.mkOfDetNeZero (Y.submatrix id f)⁻¹
    (by rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']; exact inv_ne_zero hAdet)
  have hEv : E.val = (Y.submatrix id f)⁻¹ := rfl
  set Z := E.val * Y with hZ
  have hZf : Z.submatrix id f = 1 := by
    rw [hZ, submatrix_mul_left, hEv, Matrix.nonsing_inv_mul _ hAu]
  have hZg : ∀ g : Fin n ↪ Fin d, valuation k (Z.submatrix id g).det ≤ 1 := by
    intro g
    rw [hZ, submatrix_mul_left, hEv, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv',
      map_mul, map_inv₀, inv_mul_le_one₀ (zero_lt_iff.mpr (by simpa using hAdet))]
    exact hf g
  refine ⟨E, fun i j => ?_, f, by rw [hZf, Matrix.det_one, map_one]⟩
  rw [Valuation.mem_integer_iff]
  show valuation k (Z i j) ≤ 1
  by_cases hj : ∃ i', f i' = j
  · obtain ⟨i', rfl⟩ := hj
    have := congrFun (congrFun hZf i) i'
    simp only [Matrix.submatrix_apply, id] at this
    rw [this, Matrix.one_apply]
    split_ifs <;> simp
  · push_neg at hj
    have hsub : Z.submatrix id (f.setValue i j) = (1 : Matrix (Fin n) (Fin n) k).updateCol i (fun r => Z r j) := by
      ext r s
      by_cases hs : s = i
      · subst hs; simp [Function.Embedding.setValue_eq]
      · rw [Matrix.updateCol_ne hs]
        have h2 : f.setValue i j s = f s := by
          simp [Function.Embedding.setValue, hs, hj s]
        simp only [Matrix.submatrix_apply, id, h2]
        exact congrFun (congrFun hZf r) s
    have := hZg (f.setValue i j)
    rwa [hsub, det_one_updateCol_eq] at this

end GlobalTheory.FullRankCoinv.UnitMinor
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitMinorTranslateStatement
open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_minor_translate : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (Y : Matrix (Fin n) (Fin d) k), Y.rank = n →
    ∃ E : GL (Fin n) k, E.val * Y ∈ GlobalTheory.FullRankCoinv.UnitMinor.unitMinorSet k n d := by
  first | exact @GlobalTheory.FullRankCoinv.UnitMinor.exists_GL_mul_mem_unitMinorSet | exact GlobalTheory.FullRankCoinv.UnitMinor.exists_GL_mul_mem_unitMinorSet | (intros; apply GlobalTheory.FullRankCoinv.UnitMinor.exists_GL_mul_mem_unitMinorSet <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLaplacianPolynomialKillsHarishChandraFinit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLaplacianPolynomialKillsHarishChandraFinit
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic GlobalTheory.HCAlpha
open scoped ContDiff
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

noncomputable section

namespace GlobalTheory.GLPoly

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem commute_lieS' {z : Module.End ℂ (Sm E a)} (hz : ∀ X, Commute z (lie E a X)) (i j : Fin a) (x : Cinf E) :
    Commute z (lieS E a i j x) := by
  rw [lieS_apply]; exact hz _

theorem commute_casKOp' {z : Module.End ℂ (Sm E a)} (hz : ∀ X, Commute z (lie E a X)) :
    Commute z (casKOp E a) := by
  unfold casKOp
  refine Commute.sum_right _ _ _ fun τ _ => Commute.sum_right _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ => ?_
  refine Commute.smul_right (Commute.add_right (Commute.pow_right ?_ 2) (Commute.pow_right ?_ 2)) _
  · exact (commute_lieS' hz _ _ _).sub_right (commute_lieS' hz _ _ _)
  · exact (commute_lieS' hz _ _ _).add_right (commute_lieS' hz _ _ _)

theorem commute_cas' {z : Module.End ℂ (Sm E a)} (hz : ∀ X, Commute z (lie E a X)) (τ : E →+* ℂ) :
    Commute z (Formalism.REAL.Cas (Eop (a := a) τ)) := by
  have hE : ∀ i j, Commute z (Eop τ i j) := fun i j =>
    Commute.smul_right ((commute_lieS' hz _ _ _).sub_right ((commute_lieS' hz _ _ _).smul_right _)) _
  unfold Formalism.REAL.Cas
  exact Commute.sum_right _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ => (hE i j).mul_right (hE j i)

theorem foldr_replicate' (z : Module.End ℂ (Sm E a)) (χ : Module.End ℂ (Sm E a) → ℂ) (N : ℕ) (φ : Sm E a) :
    (List.replicate N z).foldr (fun z f => z f - χ z • f) φ =
      Polynomial.aeval z ((Polynomial.X - Polynomial.C (χ z)) ^ N) φ := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.foldr_cons, ih, pow_succ', map_mul, Module.End.mul_apply]
    simp [sub_smul, Polynomial.aeval_X, Polynomial.aeval_C]


variable (E a) in
theorem exists_poly_one (W : Submodule ℂ (Kinf E a → ℂ)) (hW : FiniteDimensional ℂ W)
    (χ : Module.End ℂ (Sm E a) → ℂ) (N : ℕ) :
    ∃ p : Polynomial ℂ, p ≠ 0 ∧ ∀ φ : Sm E a,
      (∀ g : GA E a, (fun k : Kinf E a => (cptRep E a k φ).1 g) ∈ W) → GlobalTheory.HCF.CentralNilGL χ N φ →
        Polynomial.aeval (lapOp E a) p φ = 0 := by
  obtain ⟨q, hq0, hq⟩ := GlobalTheory.T.exists_poly_maximalCompactCasimir_kills_KType E a W hW
  let A : Option (E →+* ℂ) → Module.End ℂ (Sm E a) := fun o => o.elim (casKOp E a) fun τ => Formalism.REAL.Cas (Eop τ)
  let c : Option (E →+* ℂ) → ℂ := fun o => o.elim 2 fun _ => 4
  let P : Option (E →+* ℂ) → Polynomial ℂ := fun o =>
    o.elim q fun τ => (Polynomial.X - Polynomial.C (χ (Formalism.REAL.Cas (Eop (a := a) τ)))) ^ N
  have hZ : ∀ τ : E →+* ℂ, ∀ X, Commute (Formalism.REAL.Cas (Eop (a := a) τ)) (lie E a X) := fun τ X =>
    GlobalTheory.CuspRep.Zalg_mul_lie E a X _ (GlobalTheory.CasCentre.cas_Eop_mem_Zalg E a τ)
  have hc : ∀ i j, Commute (A i) (A j) := by
    rintro (_ | τ) (_ | τ')
    · exact Commute.refl _
    · exact (commute_casKOp' (hZ τ')).symm
    · exact commute_casKOp' (hZ τ)
    · exact commute_cas' (hZ τ) τ'
  have hP : ∀ i, P i ≠ 0 := by
    rintro (_ | τ)
    · exact hq0
    · exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _)
  obtain ⟨p, hp0, hp⟩ := GlobalTheory.CommutingPoly.exists_poly_annihilates_linear_combination A hc c P hP
  refine ⟨p, hp0, fun φ hK hN => ?_⟩
  have e : ∑ i, c i • A i = lapOp E a := by
    rw [GlobalTheory.HCAlpha.lapOp_eq_casKOp_add_cas E a, Fintype.sum_option]; rfl
  rw [← e]
  refine hp φ ?_
  rintro (_ | τ)
  · exact hq φ hK
  · have h := hN (List.replicate N (Formalism.REAL.Cas (Eop τ))) (List.length_replicate ..)
      (fun z hz => (List.eq_of_mem_replicate hz) ▸ GlobalTheory.CasCentre.cas_Eop_mem_Zalg E a τ)
    rw [foldr_replicate'] at h
    exact h

theorem exists_poly_formsGL : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ),
    ∀ (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Kinf E a → ℂ)), FiniteDimensional ℂ W →
    ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∃ p : Polynomial ℂ, p ≠ 0 ∧
      ∀ φ ∈ GlobalTheory.HCF.formsGL E a L W X N, Polynomial.aeval (lapOp E a) p φ = 0 := by
  intro E _ _ _ a L W hW X hX N
  classical
  choose pχ hpχ0 hpχ using fun χ => exists_poly_one E a W hW χ N
  refine ⟨∏ χ ∈ hX.toFinset, pχ χ, Finset.prod_ne_zero_iff.mpr fun χ _ => hpχ0 χ, fun φ hφ => ?_⟩
  obtain ⟨χ, hχX, hN⟩ := hφ.2.2.2
  have hmem : χ ∈ hX.toFinset := hX.mem_toFinset.mpr hχX
  rw [← Finset.mul_prod_erase _ _ hmem, mul_comm, map_mul, Module.End.mul_apply, hpχ χ φ hφ.2.2.1 hN, map_zero]

end GlobalTheory.GLPoly

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLaplacianPolynomialKillsHarishChandraFinitStatement
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic GlobalTheory.HCAlpha
open scoped ContDiff
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_laplacianPolynomial_kills_harishChandraFinite : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∀ (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Kinf E a → ℂ)), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∃ p : Polynomial ℂ, p ≠ 0 ∧ ∀ φ ∈ GlobalTheory.HCF.formsGL E a L W X N, Polynomial.aeval (lapOp E a) p φ = 0 := by
  first | exact @GlobalTheory.GLPoly.exists_poly_formsGL | exact GlobalTheory.GLPoly.exists_poly_formsGL | (intros; apply GlobalTheory.GLPoly.exists_poly_formsGL <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaIntegralEquivariantNonzero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaIntegralEquivariantNonzero
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit

noncomputable section
namespace GlobalTheory.GJForm

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

theorem isEqv_integral (n : ℕ) (ν : kˣ →* ℂˣ) (z : ℂ) (hν : IsSmU ν) (hz : (n : ℝ) - 1 < z.re) :
    IsEqv ν z (fun φ : Matrix (Fin n) (Fin n) k → ℂ =>
      ∫ g : GL (Fin n) k, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂(haarVol (KO k (Fin n)))) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have : BorelSpace (GL (Fin n) k) := borel_GL
  have : MeasurableMul (GL (Fin n) k) := inferInstance
  have : (haarVol (KO k (Fin n))).IsHaarMeasure := isHaarMeasure_haarVol_KO
  refine ⟨fun φ hφ φ' hφ' => ?_, fun c φ hφ => ?_, fun g₁ g₂ φ hφ => ?_⟩
  · dsimp only
    rw [← integral_add (GlobalTheory.T.integrable_zeta_integral_matrix_schwartz k n ν z hν hz φ hφ) (GlobalTheory.T.integrable_zeta_integral_matrix_schwartz k n ν z hν hz φ' hφ')]
    congr 1; funext g; simp only [Pi.add_apply]; ring
  · dsimp only
    rw [← integral_const_mul]; congr 1; funext g; simp only [Pi.smul_apply, smul_eq_mul]; ring
  · set F : GL (Fin n) k → ℂ := fun g => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z with hF
    set d := gdet g₁ * gdet g₂ with hd'
    have hd : (ν d : ℂ) * apow d z ≠ 0 := mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)
    have key : ∀ g : GL (Fin n) k, φ (g₁.val * g.val * g₂.val) * (ν (gdet g) : ℂ) * apow (gdet g) z
        = ((ν d : ℂ) * apow d z)⁻¹ * F (g₁ * (g * g₂)) := by
      intro g
      have e : gdet (g₁ * (g * g₂)) = gdet g * d := by
        rw [gdet_mul, gdet_mul, hd', mul_left_comm]
      have ha := apow_ne_zero d z
      have hn : (ν d : ℂ) ≠ 0 := Units.ne_zero _
      simp only [hF, e, map_mul, Units.val_mul, apow_mul, Matrix.mul_assoc]
      field_simp
    simp_rw [key]
    rw [integral_const_mul]
    have h1 : ∫ g, F (g₁ * (g * g₂)) ∂(haarVol (KO k (Fin n))) = ∫ g, F g ∂(haarVol (KO k (Fin n))) := by
      have h2 := integral_mul_right_eq_self (μ := haarVol (KO k (Fin n))) (fun g => F (g₁ * g)) g₂
      exact h2.trans (integral_mul_left_eq_self (μ := haarVol (KO k (Fin n))) F g₁)
    rw [h1, ← mul_assoc, mul_inv_cancel₀ hd, one_mul]

theorem exists_integral_ne_zero (n : ℕ) (ν : kˣ →* ℂˣ) (z : ℂ) (hν : IsSmU ν) :
    ∃ φ ∈ SB (Matrix (Fin n) (Fin n) k),
      ∫ g : GL (Fin n) k, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂(haarVol (KO k (Fin n))) ≠ 0 := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have : BorelSpace (GL (Fin n) k) := borel_GL
  have : MeasurableMul (GL (Fin n) k) := inferInstance
  have : (haarVol (KO k (Fin n))).IsHaarMeasure := isHaarMeasure_haarVol_KO
  set H : Subgroup (GL (Fin n) k) := KO k (Fin n) ⊓ (ν.comp Matrix.GeneralLinearGroup.det).ker with hH
  have hHo : IsOpen (H : Set (GL (Fin n) k)) := by
    rw [hH, Subgroup.coe_inf]
    exact isOpen_KO.inter (hν.1.preimage Matrix.GeneralLinearGroup.continuous_det)
  have hHc : IsCompact (H : Set (GL (Fin n) k)) :=
    isCompact_KO.of_isClosed_subset (H.isClosed_of_isOpen hHo) fun x hx => hx.1
  have hemb : Topology.IsOpenEmbedding (fun g : GL (Fin n) k => g.val) := by
    refine { toIsEmbedding := isEmbedding_val_GL, isOpen_range := ?_ }
    have e : Set.range (fun g : GL (Fin n) k => g.val) = {A | A.det ≠ 0} := by
      ext A
      refine ⟨?_, fun h => ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A h, rfl⟩⟩
      rintro ⟨g, rfl⟩
      exact g.det_ne_zero
    rw [e]
    exact isOpen_ne_fun (continuous_id.matrix_det) continuous_const
  set S : Set (Matrix (Fin n) (Fin n) k) := (fun g : GL (Fin n) k => g.val) '' H with hS
  have hSc : IsCompact S := hHc.image Units.continuous_val
  have hSo : IsClopen S := ⟨hSc.isClosed, hemb.isOpenMap _ hHo⟩
  refine ⟨S.indicator 1, ⟨(LocallyConstant.indicator (1 : LocallyConstant _ ℂ) hSo).isLocallyConstant,
    HasCompactSupport.intro hSc fun x hx => Set.indicator_of_notMem hx _⟩, ?_⟩
  have hfun : (fun g : GL (Fin n) k => S.indicator 1 g.val * (ν (gdet g) : ℂ) * apow (gdet g) z) =
      (H : Set (GL (Fin n) k)).indicator (fun _ => (1 : ℂ)) := by
    funext g
    by_cases hg : g ∈ H
    · have h1 : g.val ∈ S := ⟨g, hg, rfl⟩
      have h2 : ν (gdet g) = 1 := hg.2
      rw [Set.indicator_of_mem h1, Set.indicator_of_mem (show g ∈ (H : Set _) from hg), h2,
        apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hg.1)]
      simp
    · have h1 : g.val ∉ S := by
        rintro ⟨g', hg', e⟩
        exact hg (Units.ext e ▸ hg')
      rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem (show g ∉ (H : Set _) from hg)]
      simp
  simp only [hfun]
  have hI := integral_indicator_const (μ := haarVol (KO k (Fin n))) (1 : ℂ) hHo.measurableSet
  have hpos := hHo.measure_pos (haarVol (KO k (Fin n))) ⟨1, H.one_mem⟩
  have hfin := hHc.measure_lt_top (μ := haarVol (KO k (Fin n)))
  erw [hI]
  rw [Complex.real_smul, mul_one, Complex.ofReal_ne_zero, measureReal_def]
  exact (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'

theorem isEqv_integral_and_ne_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : ℕ) (ν : kˣ →* ℂˣ) (z : ℂ), IsSmU ν → (n : ℝ) - 1 < z.re →
    IsEqv ν z (fun φ : Matrix (Fin n) (Fin n) k → ℂ => ∫ g : GL (Fin n) k, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂(haarVol (KO k (Fin n)))) ∧
    ∃ φ ∈ SB (Matrix (Fin n) (Fin n) k), ∫ g : GL (Fin n) k, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂(haarVol (KO k (Fin n))) ≠ 0 :=
  fun _ _ _ _ _ _ _ n ν z hν hz => ⟨isEqv_integral n ν z hν hz, exists_integral_ne_zero n ν z hν⟩

end GlobalTheory.GJForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaIntegralEquivariantNonzeroStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zeta_integral_equivariant_nonzero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : ℕ) (ν : kˣ →* ℂˣ) (z : ℂ), IsSmU ν → (n : ℝ) - 1 < z.re →
    IsEqv ν z (fun φ : Matrix (Fin n) (Fin n) k → ℂ => ∫ g : GL (Fin n) k, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂(haarVol (KO k (Fin n)))) ∧
    ∃ φ ∈ SB (Matrix (Fin n) (Fin n) k), ∫ g : GL (Fin n) k, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂(haarVol (KO k (Fin n))) ≠ 0 := by
  first | exact @GlobalTheory.GJForm.isEqv_integral_and_ne_zero | exact GlobalTheory.GJForm.isEqv_integral_and_ne_zero | (intros; apply GlobalTheory.GJForm.isEqv_integral_and_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimConeImageOfBirationalLinearSystem
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimConeImageOfBirationalLinearSystem
open NumberField MvPolynomial GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.CompHt
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Adelic.ConeDim

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {N : ℕ}

theorem isAlgebraic_of_closure_eq_top (y : Fin N → Ω) (hy : y ≠ 0)
    (hgen : Subfield.closure (Set.range (algebraMap k Ω) ∪ {r | ∃ i j, r = y i / y j}) = ⊤)
    (A : Subalgebra k (Polynomial Ω)) (hXy : ∀ i, Polynomial.X * Polynomial.C (y i) ∈ A) :
    Algebra.IsAlgebraic A (Polynomial Ω) := by
  classical
  let ι : Polynomial Ω →+* FractionRing (Polynomial Ω) := algebraMap _ _
  have hι : Function.Injective ι := IsFractionRing.injective _ _
  let L : Subfield (FractionRing (Polynomial Ω)) := Subfield.closure (ι '' (A : Set (Polynomial Ω)))
  have hA : ∀ a ∈ A, ι a ∈ L := fun a ha => Subfield.subset_closure ⟨a, ha, rfl⟩
  have hne : ∀ j, y j ≠ 0 → ι (Polynomial.X * Polynomial.C (y j)) ≠ 0 := fun j hj =>
    (map_ne_zero_iff ι hι).2 (mul_ne_zero Polynomial.X_ne_zero (Polynomial.C_ne_zero.2 hj))
  let M : Subfield Ω := L.comap (ι.comp Polynomial.C)
  have hM : M = ⊤ := by
    refine top_unique (hgen ▸ Subfield.closure_le.2 ?_)
    rintro _ (⟨c, rfl⟩ | ⟨i, j, rfl⟩)
    · show ι (Polynomial.C (algebraMap k Ω c)) ∈ L
      rw [← Polynomial.algebraMap_apply]
      exact hA _ (A.algebraMap_mem c)
    · show ι (Polynomial.C (y i / y j)) ∈ L
      by_cases hj : y j = 0
      · rw [hj, div_zero, Polynomial.C_0, map_zero]
        exact zero_mem L
      · have e : ι (Polynomial.C (y i / y j)) =
            ι (Polynomial.X * Polynomial.C (y i)) / ι (Polynomial.X * Polynomial.C (y j)) := by
          rw [eq_div_iff (hne j hj), ← map_mul]
          congr 1
          rw [mul_left_comm, ← Polynomial.C_mul, div_mul_cancel₀ _ hj]
        rw [e]
        exact div_mem (hA _ (hXy i)) (hA _ (hXy j))
  have hC : ∀ c, ι (Polynomial.C c) ∈ L := fun c => by
    have h : c ∈ M := hM ▸ Subfield.mem_top c
    exact h
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hy
  have hX : ι Polynomial.X ∈ L := by
    have e : ι Polynomial.X = ι (Polynomial.X * Polynomial.C (y j)) * ι (Polynomial.C (y j)⁻¹) := by
      rw [← map_mul, mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hj, Polynomial.C_1, mul_one]
    rw [e]
    exact mul_mem (hA _ (hXy j)) (hC _)
  have hall : ∀ p, ι p ∈ L := fun p => by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | monomial n c =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
      exact mul_mem (hC c) (pow_mem hX n)
  have hcl : Subring.closure (ι '' (A : Set (Polynomial Ω))) ≤ (A.toSubring.map ι) :=
    Subring.closure_le.2 (by rintro _ ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩)
  refine ⟨fun p => ?_⟩
  obtain ⟨_, ha₀, _, hb₀, hab⟩ := Subfield.mem_closure_iff.1 (hall p)
  obtain ⟨a, ha, rfl⟩ := hcl ha₀
  obtain ⟨b, hb, rfl⟩ := hcl hb₀
  by_cases hb0 : b = 0
  · rw [hb0, map_zero, div_zero, eq_comm, map_eq_zero_iff ι hι] at hab
    rw [hab]
    exact isAlgebraic_zero
  · have e : b * p = a := by
      apply hι
      rw [map_mul, ← hab, mul_div_cancel₀ _ ((map_ne_zero_iff ι hι).2 hb0)]
    refine ⟨Polynomial.C (⟨b, hb⟩ : A) * Polynomial.X - Polynomial.C (⟨a, ha⟩ : A), fun h => hb0 ?_, ?_⟩
    · have := congrArg (fun q => _root_.AddMonoidAlgebra.coeff (M := ℕ) q 1) h
      simp at this
      exact congrArg Subtype.val this
    · simp [e]

theorem ringKrullDim_imageIdeal_of_birational : ∀ (k : Type) [Field k] (S : LinSys k), S.IsVariety →
    S.BasePointFree → S.Birational →
    ringKrullDim (MvPolynomial (Fin S.N) k ⧸ S.imageIdeal) = ((S.D + 1 : ℕ) : WithBot ℕ∞) := by
  intro k _ S h hb ⟨η, hη, hr⟩
  have := HeightExists.isIntegral h
  let Ω := S.Y.residueField η
  let : Algebra k Ω := (S.baseHom (resPt η)).toAlgebra
  let x : S.Pt Ω := ⟨resPt η, S.comp_str _⟩
  set y : Fin S.N → Ω := S.coords (resPt η) with hy
  have hI : S.imageIdeal = coneIdeal k y :=
    imageIdeal_eq_coneIdeal_of_generic k Ω S x (by rw [ptOf_resPt]; exact hη) 1 y one_ne_zero
      (one_smul _ _).symm
  have hD : Algebra.trdeg k Ω = S.D :=
    (residueField_fg_trdeg_of_smoothOfRelativeDimension S.str S.D h.smooth η
      fun z hz => (hz.antisymm (hη.specializes trivial)).eq).2
  rw [hI]
  have := isPrime_coneIdeal (K := k) y
  refine ringKrullDim_eq_of_trdeg_eq k _ ?_
  let f := Ideal.kerLiftAlg (coneMap k y)
  have hf : Function.Injective f := Ideal.kerLiftAlg_injective _
  let A := f.range
  let e := AlgEquiv.ofInjective f hf
  have hQA : Algebra.trdeg k (MvPolynomial (Fin S.N) k ⧸ coneIdeal k y) = Algebra.trdeg k A :=
    le_antisymm (trdeg_le_of_injective e.toAlgHom e.injective)
      (trdeg_le_of_injective e.symm.toAlgHom e.symm.injective)
  have hXy : ∀ i, Polynomial.X * Polynomial.C (y i) ∈ A := fun i => by
    have := AlgHom.mem_range_self f (Ideal.Quotient.mk _ (X i))
    rw [Ideal.kerLiftAlg_mk] at this
    simp only [coneMap, aeval_X] at this
    exact this
  have := ConeDim.isAlgebraic_of_closure_eq_top y (hb.coords_ne_zero _) hr A hXy
  have : FaithfulSMul k A := (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.injective _)
  have : FaithfulSMul A (Polynomial Ω) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  rw [hQA, ← GlobalTheory.trdeg_eq_of_isAlgebraic_top k A (Polynomial Ω), ← trdeg_add_eq k Ω (A := Polynomial Ω),
    Polynomial.trdeg_of_isDomain, hD]
  norm_cast

end GlobalTheory.Adelic.ConeDim
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimConeImageOfBirationalLinearSystemStatement
open NumberField MvPolynomial GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.CompHt
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringKrullDim_cone_image_of_birational_linearSystem : ∀ (k : Type) [Field k] (S : LinSys k), S.IsVariety → S.BasePointFree → S.Birational → ringKrullDim (MvPolynomial (Fin S.N) k ⧸ S.imageIdeal) = ((S.D + 1 : ℕ) : WithBot ℕ∞) := by
  first | exact @GlobalTheory.Adelic.ConeDim.ringKrullDim_imageIdeal_of_birational | exact GlobalTheory.Adelic.ConeDim.ringKrullDim_imageIdeal_of_birational | (intros; apply GlobalTheory.Adelic.ConeDim.ringKrullDim_imageIdeal_of_birational <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClopenIntegrabilityFullRankOrbit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClopenIntegrabilityFullRankOrbit
noncomputable section

open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL

namespace GlobalTheory.FullRankCoinv.Reduce

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem lact_mem {n d : ℕ} (ν : kˣ →* ℂˣ) (g : GL (Fin n) k) {Ψ : Matrix (Fin n) (Fin d) k → ℂ}
    (hΨ : Ψ ∈ fullRk k n d) : lact ν g Ψ ∈ fullRk k n d := by
  have hmem : (fun Y => Ψ ((g.1)ᵀ * Y)) ∈ fullRk k n d := by
    let e : Matrix (Fin n) (Fin d) k ≃ₜ Matrix (Fin n) (Fin d) k :=
      { toFun := fun X => (g.1)ᵀ * X
        invFun := fun X => ((g⁻¹).1)ᵀ * X
        left_inv := fun X => by
          simp only [← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one,
            Matrix.one_mul]
        right_inv := fun X => by
          simp only [← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one,
            Matrix.one_mul]
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    refine ⟨⟨hΨ.1.1.comp_continuous e.continuous, hΨ.1.2.comp_homeomorph e⟩, fun Y hY => hΨ.2 _ ?_⟩
    rwa [Matrix.rank_mul_eq_right_of_isUnit_det _ _
      (by rw [Matrix.det_transpose]; exact Matrix.isUnits_det_units g)]
  exact (fullRk k n d).smul_mem ((ν (gdet g) : ℂ) * apow (gdet g) ((d : ℂ) / 2)) hmem

theorem indicator_mem {n d : ℕ} {T : Set (Matrix (Fin n) (Fin d) k)} (hT : IsClopen T)
    {Ψ : Matrix (Fin n) (Fin d) k → ℂ} (hΨ : Ψ ∈ fullRk k n d) : T.indicator Ψ ∈ fullRk k n d := by
  refine ⟨⟨?_, ?_⟩, fun Y hY => ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ T
    · filter_upwards [hT.isOpen.mem_nhds hx, hΨ.1.1.eventually_eq x] with y hy h
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy, h]
    · filter_upwards [hT.compl.isOpen.mem_nhds hx] with y hy
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]
  · refine HasCompactSupport.mono hΨ.1.2 fun y hy h => hy ?_
    by_cases hy' : y ∈ T
    · rw [Set.indicator_of_mem hy', h]
    · exact Set.indicator_of_notMem hy' _
  · by_cases hy' : Y ∈ T
    · rw [Set.indicator_of_mem hy', hΨ.2 Y hY]
    · exact Set.indicator_of_notMem hy' _

end

theorem reduce_support : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n d : ℕ) (ν : kˣ →* ℂˣ) (S : Set (Matrix (Fin n) (Fin d) k)), IsClopen S →
    (∀ Φ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∀ Y : Matrix (Fin n) (Fin d) k, Integrable (fun g : GL (Fin n) k =>
      Φ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin d) : ℂ) / 2))
      (haarVol (GlobalTheory.SplitWeil.KO k (Fin n)))) →
    ∀ (s : Finset (GL (Fin n) k)), ∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d,
    (∀ Y, Ψ Y ≠ 0 → ∃ E ∈ s, E.val * Y ∈ S) →
    ∃ Φ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, (∀ Y, Y ∉ S → Φ Y = 0) ∧ Ψ - Φ ∈ GlobalTheory.FullRankCoinv.augRk n d ν ∧
      ∀ Y, smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Φ Y = smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ Y := by
  intro k _ _ _ _ _ _ n d ν S hS hint s
  classical
  have hadd : ∀ Ψ ∈ fullRk k n d, ∀ Φ ∈ fullRk k n d, ∀ Y,
      smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν (Ψ + Φ) Y =
        smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ Y + smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Φ Y := by
    intro Ψ hΨ Φ hΦ Y
    simp only [smallF, Pi.add_apply]
    rw [← integral_add (hint Ψ hΨ Y) (hint Φ hΦ Y)]
    congr 1; funext g; ring
  induction s using Finset.induction_on with
  | empty =>
    intro Ψ hΨ h
    refine ⟨Ψ, hΨ, fun Y _ => ?_, by simp, fun _ => rfl⟩
    by_contra h0
    simpa using h Y h0
  | insert E s _ ih =>
    intro Ψ hΨ h
    set T : Set (Matrix (Fin n) (Fin d) k) := (fun Y => E.val * Y) ⁻¹' S with hTdef
    have hT : IsClopen T := hS.preimage (by fun_prop)
    have h1 := indicator_mem hT hΨ
    have h2 := indicator_mem hT.compl hΨ
    have hsum : T.indicator Ψ + Tᶜ.indicator Ψ = Ψ := Set.indicator_self_add_compl T Ψ
    obtain ⟨Φ₂, hΦ₂, hS₂, ha₂, hF₂⟩ := ih _ h2 fun Y hY => by
      have hYT : Y ∈ Tᶜ := by
        by_contra hc
        exact hY (Set.indicator_of_notMem hc _)
      rw [Set.indicator_of_mem hYT] at hY
      obtain ⟨E', hE', hS'⟩ := h Y hY
      rcases Finset.mem_insert.1 hE' with rfl | hE'
      · exact absurd hS' hYT
      · exact ⟨E', hE', hS'⟩
    have hΦ₁ := lact_mem ν (invT E) h1
    refine ⟨lact ν (invT E) (T.indicator Ψ) + Φ₂, add_mem hΦ₁ hΦ₂, fun Y hY => ?_, ?_, fun Y => ?_⟩
    · have hn : (invT E).1ᵀ * Y ∉ T := by
        intro hc
        apply hY
        have hc' : E.val * ((invT E).1ᵀ * Y) ∈ S := hc
        rwa [invT_val, Matrix.transpose_transpose, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul] at hc'
      simp only [Pi.add_apply, hS₂ Y hY, lact, Set.indicator_of_notMem hn, mul_zero, add_zero]
    · have ha₁ : lact ν (invT E) (T.indicator Ψ) - T.indicator Ψ ∈ augRk n d ν :=
        Submodule.subset_span ⟨_, _, h1, rfl⟩
      have : Ψ - (lact ν (invT E) (T.indicator Ψ) + Φ₂) =
          (Tᶜ.indicator Ψ - Φ₂) - (lact ν (invT E) (T.indicator Ψ) - T.indicator Ψ) := by
        linear_combination -hsum
      rw [this]
      exact sub_mem ha₂ ha₁
    · rw [hadd _ hΦ₁ _ hΦ₂, UnitMinor.smallF_lact, hF₂, ← hadd _ h1 _ h2, hsum]

end GlobalTheory.FullRankCoinv.Reduce
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClopenIntegrabilityFullRankOrbitStatement
open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.clopen_integrability_full_rank_orbit : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n d : ℕ) (ν : kˣ →* ℂˣ) (S : Set (Matrix (Fin n) (Fin d) k)), IsClopen S →
    (∀ Φ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∀ Y : Matrix (Fin n) (Fin d) k, Integrable (fun g : GL (Fin n) k =>
      Φ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin d) : ℂ) / 2))
      (haarVol (GlobalTheory.SplitWeil.KO k (Fin n)))) →
    ∀ (s : Finset (GL (Fin n) k)), ∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d,
    (∀ Y, Ψ Y ≠ 0 → ∃ E ∈ s, E.val * Y ∈ S) →
    ∃ Φ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, (∀ Y, Y ∉ S → Φ Y = 0) ∧ Ψ - Φ ∈ GlobalTheory.FullRankCoinv.augRk n d ν ∧
      ∀ Y, smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Φ Y = smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ Y := by
  first | exact @GlobalTheory.FullRankCoinv.Reduce.reduce_support | exact GlobalTheory.FullRankCoinv.Reduce.reduce_support | (intros; apply GlobalTheory.FullRankCoinv.Reduce.reduce_support <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlLatCongMove
open Matrix MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel
open scoped Pointwise

namespace GlobalTheory.PrimFrameMove

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

theorem exists_rightInverse {X : Matrix A D k} (hX : IsPrimFrame (SplitFlip.stdLat k D) X) :
    ∃ R : Matrix D A k, (∀ i j, R i j ∈ 𝒪[k]) ∧ X * R = 1 := by
  have hli : LinearIndependent k X.row := by
    rw [linearIndependent_iff_card_eq_finrank_span, ← hX.1, rank_eq_finrank_span_row]; rfl
  let X' : Matrix A D 𝒪[k] := Matrix.of fun i j => ⟨X i j, mem_matLat_stdLat.1 hX.2.1 i j⟩
  let f : (A → 𝒪[k]) →ₗ[𝒪[k]] (D → 𝒪[k]) := X'.vecMulLinear
  have hf : ∀ v j, ((f v j : 𝒪[k]) : k) = (∑ i, (v i : k) • X.row i) j := fun v j => by
    simp [f, X', vecMul, dotProduct, Finset.sum_apply]
  have hinj : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro v hv
    have h1 : ∑ i, (v i : k) • X.row i = 0 := by
      funext j; rw [← hf, hv]; rfl
    funext i
    exact Subtype.ext (Fintype.linearIndependent_iff.1 hli _ h1 i)
  have hsat : ∀ (r : 𝒪[k]) (x : D → 𝒪[k]), r ≠ 0 → r • x ∈ LinearMap.range f → x ∈ LinearMap.range f := by
    rintro r x hr ⟨v, hv⟩
    have hr' : (r : k) ≠ 0 := fun h => hr (Subtype.ext h)
    have h1 : (fun j => (x j : k)) = (r : k)⁻¹ • ∑ i, (v i : k) • X.row i := by
      funext j
      rw [Pi.smul_apply, ← hf, hv]
      simp [hr']
    have h2 : (fun j => (x j : k)) ∈ Submodule.span 𝒪[k] (Set.range X.row) := by
      rw [hX.2.2]
      refine ⟨?_, mem_stdLat.2 fun j => (x j).2⟩
      rw [h1]
      exact Submodule.smul_mem (Submodule.span k _) _
        (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i)))
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun 𝒪[k]).1 h2
    refine ⟨d, funext fun j => Subtype.ext ?_⟩
    rw [hf]
    exact congrFun hd j
  have : Module.IsTorsionFree 𝒪[k] ((D → 𝒪[k]) ⧸ LinearMap.range f) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r q h => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    by_cases hr : r = 0
    · exact .inl hr
    · refine .inr ((Submodule.Quotient.mk_eq_zero _).2 (hsat r x hr ?_))
      rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (LinearMap.range f).mkQ LinearMap.id
    (Submodule.mkQ_surjective _)
  obtain ⟨l, hl⟩ : ∃ l : (D → 𝒪[k]) →ₗ[𝒪[k]] (A → 𝒪[k]), l ∘ₗ f = LinearMap.id := by
    have hs' : ∃ s : _ →ₗ[𝒪[k]] _, (LinearMap.range f).mkQ ∘ₗ s = LinearMap.id := ⟨s, hs⟩
    have H := ((LinearMap.exact_map_mkQ_range f).split_tfae hinj (Submodule.mkQ_surjective _)).out 1 2
    exact H.1 hs'
  refine ⟨Matrix.of fun j i => (l (Pi.single j 1) i : k), fun j i => (l (Pi.single j 1) i).2, ?_⟩
  ext i i'
  have h1 : l (f (Pi.single i 1)) = Pi.single i 1 := LinearMap.congr_fun hl _
  have h2 : f (Pi.single i 1) = ∑ j, X' i j • Pi.single j 1 := by
    funext j; simp [f, Finset.sum_apply, Pi.single_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h2, map_sum] at h1
  have h3 := congrArg Subtype.val (congrFun h1 i')
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h3
  push_cast at h3
  rw [Matrix.mul_apply, Matrix.one_apply]
  refine h3.trans ?_
  rw [Pi.single_apply]
  by_cases h : i = i'
  · simp [h]
  · simp [h, Ne.symm h]

theorem exists_mem_glLatCong {u : kˣ} (hu : valuation k (u : k) < 1) {M : Matrix D D k}
    (hM : ∀ i j, valuation k (M i j) ≤ valuation k (u : k)) :
    ∃ κ ∈ glLatCong u (SplitFlip.stdLat k D), κ.val = 1 + M := by
  let M' : Matrix D D 𝒪[k] := Matrix.of fun i j => ⟨M i j, (hM i j).trans hu.le⟩
  have hK : IsUnit (1 + M') := by
    rw [Matrix.isUnit_iff_isUnit_det, ← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
    have : (IsLocalRing.residue 𝒪[k]).mapMatrix M' = 0 := by
      ext r j
      simp only [RingHom.mapMatrix_apply, map_apply, Matrix.zero_apply]
      rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        Valuation.Integer.not_isUnit_iff_valuation_lt_one]
      exact (hM r j).trans_lt hu
    rw [map_add (f := _), this]; simp
  obtain ⟨w, hw⟩ := hK
  have hv : (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) w).val = 1 + M := by
    show (algebraMap 𝒪[k] k).mapMatrix w.val = _
    rw [hw, map_add (f := _), map_one]; rfl
  refine ⟨_, GlobalTheory.FunObj.GivenAdm.mem_glLatCong.2 ⟨⟨w, rfl⟩, ?_⟩, hv⟩
  rw [hv, add_sub_cancel_left]
  exact hM


omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem vecMul_diagGL_mem (a b c : D → kˣ) (h : ∀ j, b j = a j * c j) (x : D → k) :
    x ᵥ* (diagGL c).val ∈ diagLat b ↔ x ∈ diagLat a := by
  refine forall_congr' fun j => ?_
  have h0 : 0 < valuation k (c j : k) := zero_lt_iff.2 (by simp)
  rw [diagGL_val, vecMul_diagonal, map_mul, h, Units.val_mul, map_mul]
  exact mul_le_mul_iff_left₀ h0

theorem exists_glLatCong_move (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    (c : D → kˣ) (u : kˣ) (hu : valuation k (u : k) < 1) (X Z : Matrix A D k) (hX : IsPrimFrame (diagLat c) X)
    (hZ : Z ∈ matLat A (u • diagLat c)) : ∃ κ ∈ glLatCong u (diagLat c), X + Z = X * κ.val := by
  set g : GL D k := diagGL c with hg
  have h1 : ∀ x, x ᵥ* g.val ∈ diagLat c ↔ x ∈ SplitFlip.stdLat k D := vecMul_diagGL_mem 1 c c (by simp)
  have h2 : ∀ x, x ᵥ* g.val ∈ u • diagLat c ↔ x ∈ u • SplitFlip.stdLat k D := fun x => by
    rw [SplitFlip.stdLat, smul_diagLat, smul_diagLat]
    exact vecMul_diagGL_mem _ _ c (by simp) x
  have h1' : ∀ x, x ᵥ* (g⁻¹).val ∈ SplitFlip.stdLat k D ↔ x ∈ diagLat c := fun x => by
    rw [← h1, vecMul_vecMul, Units.inv_mul, vecMul_one]
  have h2' : ∀ x, x ᵥ* (g⁻¹).val ∈ u • SplitFlip.stdLat k D ↔ x ∈ u • diagLat c := fun x => by
    rw [← h2, vecMul_vecMul, Units.inv_mul, vecMul_one]
  obtain ⟨R, hR, hXR⟩ := exists_rightInverse (SplitFlip.Model.isPrimFrame_mul hX g⁻¹ h1')
  have hZ' : GlobalTheory.FunObj.GivenAdm.CongM u (Z * (g⁻¹).val) :=
    GlobalTheory.FunObj.GivenAdm.mem_matLat_smul.1 fun i => (h2' (Z.row i)).2 (hZ i)
  obtain ⟨κ, ⟨hκ, hκ'⟩, hv⟩ := exists_mem_glLatCong hu (hZ'.mul_left (Y := R) hR)
  refine ⟨g⁻¹ * κ * g, ⟨fun x => ?_, fun x hx => ?_⟩, ?_⟩
  · rw [Units.val_mul, Units.val_mul, ← vecMul_vecMul, ← vecMul_vecMul, h1, hκ, h1']
  · rw [show (g⁻¹ * κ * g).val - 1 = (g⁻¹).val * (κ.val - 1) * g.val by
      rw [mul_sub, sub_mul, mul_one, Units.inv_mul, Units.val_mul, Units.val_mul],
      ← vecMul_vecMul, ← vecMul_vecMul, h2]
    exact hκ' _ ((h1' x).2 hx)
  · rw [Units.val_mul, Units.val_mul, hv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_add,
      ← Matrix.mul_assoc _ R, hXR, Matrix.mul_one, Matrix.one_mul, ← Matrix.add_mul, Matrix.mul_assoc,
      Units.inv_mul, Matrix.mul_one]

end GlobalTheory.PrimFrameMove
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetGramSkewHermitianSignature
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetGramSkewHermitianSignature
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.SkewUnit

theorem isUnit_det_of_isSkew : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (d : ℕ) (W : Spc F E d) (r s : ℕ), W.IsSkew σ B r s → IsUnit W.J.det := by
  intro F E _ _ _ _ _ σ B d W r s hW
  exact isUnit_iff_ne_zero.2 (GlobalTheory.SkewDet.det_ne_zero_of_isSkew F E σ B d r s W hW)

end GlobalTheory.SkewUnit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetGramSkewHermitianSignatureStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_det_gram_skewHermitian_signature : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (d : ℕ) (W : Spc F E d) (r s : ℕ), W.IsSkew σ B r s → IsUnit W.J.det := by
  first | exact @GlobalTheory.SkewUnit.isUnit_det_of_isSkew | exact GlobalTheory.SkewUnit.isUnit_det_of_isSkew | (intros; apply GlobalTheory.SkewUnit.isUnit_det_of_isSkew <;> assumption)
end
end
