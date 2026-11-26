module

public import Formalism.LocalToGlobal.ProjectiveLattices.ReadProofs
public import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsHomOfLinearScalingHermForm
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqZeroOfSumEmbeddingSmul
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HolomorphicUniformizationTangentUnimodularRiemann
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NatCastMemMaximalIdealOfOverLa
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

open IsDedekindDomain

theorem modelAtSt_of_good : PartI → N1ab → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → ∀ la, Formalism.L2.Pj.ModelAtSt Xo c la := by
  intro hP hN E _ _ _ H Dw l Xo c hpq hg la
  exact Formalism.L2.Pj.modelAtSt_of (Formalism.L2.Pj.partIAt_of hP hN Xo c hpq) hg la

end GlobalTheory.Frames
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsValuationSubringComplexComapValEq
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsValuationSubringComplexComapValEq
namespace GlobalTheory

theorem exists_valuationSubring_complex_comap_val_eq (F : IntermediateField ℚ ℂ)
    (U : ValuationSubring F) (p : ℕ) (hp : (p : F) ∈ U.nonunits) :
    ∃ W : ValuationSubring ℂ, (p : ℂ) ∈ W.nonunits ∧ W.comap F.val.toRingHom = U := by
  obtain ⟨W, hW⟩ : ∃ W : ValuationSubring ℂ, W.comap (algebraMap F ℂ) = U :=
    exists_valuationSubring_comap_eq U _
  refine ⟨W, ?_, hW⟩
  rw [ValuationSubring.mem_nonunits_iff_or] at hp ⊢
  rcases hp with h | h
  · left
    simpa using congrArg (algebraMap F ℂ) h
  · right
    rw [← hW, ValuationSubring.mem_comap] at h
    simpa using h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsValuationSubringComplexComapValEqStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_valuationSubring_complex_comap_eq : ∀ (F : IntermediateField ℚ ℂ) (U : ValuationSubring F) (p : ℕ), (p : F) ∈ U.nonunits → ∃ W : ValuationSubring ℂ, (p : ℂ) ∈ W.nonunits ∧ W.comap F.val.toRingHom = U := by
  first | exact @GlobalTheory.exists_valuationSubring_complex_comap_val_eq | exact GlobalTheory.exists_valuationSubring_complex_comap_val_eq | (intros; apply GlobalTheory.exists_valuationSubring_complex_comap_val_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCmEndomorphismCommConjugation
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCmEndomorphismCommConjugation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CurveEndo

theorem scale_dual (f : ℂ →+* ℂ) (c : ℂ) :
    spMap (Chart.dualMapR f) ≫ spMap (epsScaleR c) = spMap (epsScaleR (f c)) ≫ spMap (Chart.dualMapR f) := by
  rw [spMap_comp_spMap, spMap_comp_spMap]
  congr 1
  ext a <;> simp [Chart.dualMapR, epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]

theorem dual_symm_dual (τ : ℂ ≃+* ℂ) :
    spMap (Chart.dualMapR (τ.symm : ℂ →+* ℂ)) ≫ spMap (Chart.dualMapR (τ : ℂ →+* ℂ)) = 𝟙 _ := by
  rw [spMap_comp_spMap]
  refine Eq.trans ?_ (Spec.map_id (CommRingCat.of (DualNumber ℂ)))
  congr 1
  ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem left_eq_scale {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
    (he : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) {w : Fin g → ℂ} {v v' : epsR ℂ ⟶ A} (α : ℂ) (hv : IsTangent v)
    (hw : u.IsDiff w v) (hv' : IsTangent v') (hw' : u.IsDiff (α • w) v') :
    v'.left = spMap (epsScaleR α) ≫ v.left := by
  have hx := (LieMultiple.isLieComb_one_iff_comp α v _).2 rfl
  have hxt : IsTangent (Chart.spMap (Chart.scaleD α) ≫ v) :=
    (Chart.isTan_iff _).1 (Chart.isTan_scale α ((Chart.isTan_iff _).2 hv))
  rw [(he (α • w)).unique ⟨hv', hw'⟩ ⟨hxt, CMNormIdentity.isDiff_of_isLieComb u hw α hx⟩]
  exact (LieMultiple.isLieComb_one_iff α v _).1 hx

theorem comm_of_fixed (P : Out.PolAV (Sp ℂ)) (hg : P.g = 1) (u : HolUnif P.A P.L P.g)
    (hd : ∀ v, IsTangent v → ∃! w, u.IsDiff w v) (he : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v)
    (W : P.A ⟶ P.A) [IsMonHom W] (α : ℂ) (hW : ∀ z, u.ex (α • z) = u.ex z ≫ W)
    (τ : ℂ ≃+* ℂ) (hτ : τ α = α) (io : P.A.left ⟶ P.A.left) (h : IsGrpPullback P.A P.A (spMap (τ : ℂ →+* ℂ)) io) :
    W.left ≫ io = io ≫ W.left := by
  obtain ⟨W', hW', e⟩ := HomDescent.exists_isMonHom_pull h h W
  obtain ⟨v, ⟨hv, dv⟩, -⟩ := he (fun _ => 1)
  obtain ⟨v', hv', -⟩ := existsUnique_isVecOver h.1 v
  have tv' := hv'.isTangent h hv
  unfold IsVecOver at hv'
  obtain ⟨w', dw', -⟩ := hd v' tv'
  have h1 : (v ≫ W).left = spMap (epsScaleR α) ≫ v.left :=
    left_eq_scale u he α hv dv (HomLinear.isTangent_comp W hv)
      (HomLinear.isDiff_comp u u W (α • LinearMap.id) hW hv dv)
  have h2 : (v' ≫ W').left = spMap (epsScaleR α) ≫ v'.left := by
    refine h.1.hom_ext ?_ ?_
    · rw [Over.comp_left, Category.assoc, e, ← Category.assoc, hv', Category.assoc, ← Over.comp_left, h1,
        ← Category.assoc, scale_dual, Category.assoc, Category.assoc, hv']
      simp [hτ]
    · rw [Over.w, Category.assoc, Over.w]
      refine Eq.trans ?_ (spMap_comp_spMap _ _).symm
      show spMap _ = spMap _
      congr 1
      ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have hne : w' ≠ 0 := by
    rintro rfl
    have h3 := left_eq_scale u he 0 tv' dw' tv' (by rwa [zero_smul])
    have h4 : v.left = spMap (epsScaleR 0) ≫ v.left := by
      have h5 : spMap (Chart.dualMapR (τ : ℂ →+* ℂ)) ≫ v.left =
          spMap (Chart.dualMapR (τ : ℂ →+* ℂ)) ≫ spMap (epsScaleR 0) ≫ v.left := by
        rw [← Category.assoc, scale_dual, map_zero, Category.assoc, ← hv', ← Category.assoc, ← h3]
      have h6 := congrArg (spMap (Chart.dualMapR (τ.symm : ℂ →+* ℂ)) ≫ ·) h5
      simpa only [← Category.assoc, dual_symm_dual, Category.id_comp] using h6
    have h7 := (hd v hv).unique dv
      (CMNormIdentity.isDiff_of_isLieComb u dv 0 ((LieMultiple.isLieComb_one_iff 0 v v).2 h4))
    simpa using congrFun h7 ⟨0, by omega⟩
  obtain ⟨F, hF, -, hT, hu⟩ := HomLinear.exists_linear_of_isMonHom P.A P.A P.isAb P.isAb P.L P.L _ _ u u hd he W' hW'
  obtain ⟨tf, df⟩ := hT w' v' tv' dw'
  have h8 : F w' = α • w' := (hd _ tf).unique df
    (CMNormIdentity.isDiff_of_isLieComb u dw' α ((LieMultiple.isLieComb_one_iff α v' _).2 h2))
  have h9 : ∀ z, F z = α • z := fun z => by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
    have hz : z = (z i / w' i) • w' := by
      funext j
      have : j = i := Fin.ext (by have := j.2; have := i.2; omega)
      rw [this, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hi]
    rw [hz, map_smul, h8, smul_comm]
  rw [← e, ← hu W fun z => by rw [h9, hW]]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem cmHost_rootComplex_eq_pm_sqrt (H : Host E) : H.rt0 = Complex.I * Real.sqrt H.d ∨ H.rt0 = -(Complex.I * Real.sqrt H.d) := by
  rw [← sq_eq_sq_iff_eq_or_eq_neg, H.sqrt_neg_disc_sq, mul_pow, Complex.I_sq, ← Complex.ofReal_pow,
    Real.sq_sqrt (by positivity)]
  simp

theorem rt0_conj_neg_ne_zero (H : Host E) : starRingEnd ℂ H.rt0 = -H.rt0 := by
  rcases cmHost_rootComplex_eq_pm_sqrt H with h | h <;> rw [h] <;> simp

theorem mem_lattice (C : Curve H) (z : Fin C.P.g → ℂ) : z ∈ C.u.Λ ↔ ∃ a, z = fun _ => C.c * wC H a := by
  rw [C.lat z]
  rcases cmHost_rootComplex_eq_pm_sqrt H with h | h
  · exact ⟨fun ⟨m, n, e⟩ => ⟨(m, n), by rw [e, wC, h]⟩, fun ⟨a, e⟩ => ⟨a.1, a.2, by rw [e, wC, h]⟩⟩
  · refine ⟨fun ⟨m, n, e⟩ => ⟨(m + n, -n), ?_⟩, fun ⟨a, e⟩ => ⟨a.1 + a.2, -a.2, ?_⟩⟩
    · rw [e, wC, h]
      funext _
      push_cast
      ring
    · rw [e, wC, h]
      funext _
      push_cast
      ring

theorem exists_norm (H : Host E) : ∃ n : ℕ, (1 + H.d : ℂ) = 4 * n := by
  have := H.d_mod
  refine ⟨(1 + H.d) / 4, ?_⟩
  exact_mod_cast (by omega : 1 + H.d = 4 * ((1 + H.d) / 4))

theorem exists_endo_comm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (C : Curve H), ∃ W : C.P.A ⟶ C.P.A, IsMonHom W ∧ (∀ z, C.pt z ≫ W.left = C.pt (wC H (0, 1) * z)) ∧ (∀ z z', C.pt z = C.pt z' ↔ ∃ a, z - z' = wC H a) ∧ (∀ x : Sp ℂ ⟶ C.P.A.left, x ≫ C.P.A.hom = 𝟙 _ → ∃ z, C.pt z = x) ∧ ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ io : C.P.A.left ⟶ C.P.A.left, IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io → W.left ≫ io = io ≫ W.left := by
  intro E _ _ _ H C
  obtain ⟨Hm, χ, Ef, hA, hd, he, hθ, -⟩ := C.theta
  obtain ⟨n, hn⟩ := exists_norm H
  have hsq := H.sqrt_neg_disc_sq
  have hα : wC H (0, 1) = (1 + H.rt0) / 2 := by simp [wC]
  obtain ⟨W, hW, hF⟩ := exists_hom_of_linear_scaling_hermForm C.P C.P C.u C.u Hm χ Hm χ hA hA
    (fun k => (hθ k).2) (fun k => (hθ k).1) (wC H (0, 1) • LinearMap.id) n
    (fun l hl => by
      obtain ⟨a, rfl⟩ := (mem_lattice C l).1 hl
      refine (mem_lattice C _).2 ⟨(-(n * a.2), a.1 + a.2), ?_⟩
      funext _
      simp only [LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply, smul_eq_mul, wC]
      push_cast
      linear_combination (C.c * a.2 / 4) * hsq - (C.c * a.2 / 4) * hn)
    (fun x y => by
      have e : wC H (0, 1) * starRingEnd ℂ (wC H (0, 1)) = n := by
        rw [hα, map_div₀, map_add (f := _), rt0_conj_neg_ne_zero, map_one, map_ofNat]
        linear_combination (-1 / 4 : ℂ) * hsq + (1 / 4 : ℂ) * hn
      simp only [LinearMap.smul_apply, LinearMap.id_apply, hermForm, star_smul, Matrix.mulVec_smul, smul_dotProduct,
        dotProduct_smul, smul_eq_mul]
      rw [← e, ← _root_.mul_assoc, _root_.mul_comm (wC H (0, 1))]
      rfl)
  refine ⟨W, hW, fun z => ?_, fun z z' => ?_, fun x hx => ?_, fun τ hτ io h => ?_⟩
  · unfold Curve.pt
    rw [← Over.comp_left, ← hF]
    congr 2
    ext i
    simp only [LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · have e := C.u.ex_add (fun _ => C.c * (z - z')) (fun _ => C.c * z')
    have e' : ((fun _ => C.c * (z - z')) + fun _ => C.c * z' : Fin C.P.g → ℂ) = fun _ => C.c * z := by
      funext _
      simp only [Pi.add_apply]
      ring
    rw [e'] at e
    have e₁ : C.pt z = C.pt z' ↔ C.u.ex (fun _ => C.c * z) = C.u.ex (fun _ => C.c * z') :=
      ⟨fun h => Over.OverMorphism.ext h, fun h => congrArg (fun t => t.left) h⟩
    rw [e₁, e, mul_eq_right, C.u.ker, mem_lattice]
    refine exists_congr fun a => ⟨fun h => ?_, fun h => by rw [h]⟩
    exact mul_left_cancel₀ C.c_ne (congrFun h ⟨0, by rw [C.g_eq]; omega⟩)
  · obtain ⟨z, hz⟩ := C.u.ex_onto (Over.homMk x hx)
    have hg := C.g_eq
    refine ⟨z ⟨0, by omega⟩ / C.c, ?_⟩
    have : (fun _ => C.c * (z ⟨0, by omega⟩ / C.c)) = z := by
      funext j
      rw [mul_div_cancel₀ _ C.c_ne]
      congr 1
      exact Fin.ext (by have := j.2; simp only; omega)
    unfold Curve.pt
    rw [this, hz]
    rfl
  · refine comm_of_fixed C.P C.g_eq C.u hd he W (wC H (0, 1)) hF τ ?_ io h
    rw [hα, map_div₀, map_add (f := _), hτ, map_one, map_ofNat]

end GlobalTheory.CurveEndo
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCmEndomorphismCommConjugationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmEndomorphism_comm_conjugation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (C : Curve H), ∃ W : C.P.A ⟶ C.P.A, IsMonHom W ∧ (∀ z, C.pt z ≫ W.left = C.pt (wC H (0, 1) * z)) ∧ (∀ z z', C.pt z = C.pt z' ↔ ∃ a, z - z' = wC H a) ∧ (∀ x : Sp ℂ ⟶ C.P.A.left, x ≫ C.P.A.hom = 𝟙 _ → ∃ z, C.pt z = x) ∧ ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ io : C.P.A.left ⟶ C.P.A.left, IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io → W.left ≫ io = io ≫ W.left := by
  first | exact @GlobalTheory.CurveEndo.exists_endo_comm | exact GlobalTheory.CurveEndo.exists_endo_comm | (intros; apply GlobalTheory.CurveEndo.exists_endo_comm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsChartEigenframe
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ModuliChart

theorem exists_sec_of_secOn {X X' S S' : Scheme.{0}} {p : X ⟶ S} {p' : X' ⟶ S'} {t : S' ⟶ S} {F : X' ⟶ X}
    (hF : IsPullback F p' p t) {L : LB X} {L' : LB X'} (hL : L.IsLB) (hL' : L'.IsLB) (hw : LBIso L' (L.pull F))
    {V : S.Opens} (hV : ∀ y, t y ∈ V) {θ : ∀ i, Γ(X, p ⁻¹ᵁ V ⊓ L.U i)} (hθ : θ ∈ secOn L (p ⁻¹ᵁ V))
    (hne : ∀ y ∈ V, ∃ (g : X) (i : L.ι), p g = y ∧ g ∈ X.basicOpen (θ i)) :
    ∃ th : L'.Sec, ∀ y : S', ∃ x : X', p' x = y ∧ x ∈ Out.nonzeroLocus th := by
  obtain ⟨w, hw⟩ := hw
  have hFV : ∀ y : X', p (F y) ∈ V := fun y => by
    rw [← Scheme.Hom.comp_apply, hF.w, Scheme.Hom.comp_apply]; exact hV _
  have le : ∀ j, F ⁻¹ᵁ L.U j ≤ F ⁻¹ᵁ (p ⁻¹ᵁ V ⊓ L.U j) := fun j y hy => ⟨hFV y, hy⟩
  have val : ∀ (y : X') j, F y ∈ L.U j → gs (𝟙 X') y _ ((F.appLE _ _ (le j)).hom (θ j)) =
      (F.stalkMap y).hom (gs (𝟙 X) (F y) _ (θ j)) := fun y j h => by
    rw [gs_appLE F _ _ (le j) (𝟙 X') y h, Category.id_comp, gs_stalkMap F y _ (le j h)]
  obtain ⟨th, hth⟩ := sec_down ((isGen_iff w).1 hw) hL hL' (fun j => (F.appLE _ _ (le j)).hom (θ j))
    fun y j j' h h' => by
      rw [val y j h, val y j' h', LBGerm.gs_secOn hθ (F y) j j' (hFV y) h h', map_mul]
      congr 1
      have := PushInv.gm_comp F (𝟙 X) y (L.U j ⊓ L.U j') ⟨h, h'⟩ (L.g j j')
      rw [Category.comp_id] at this
      exact this.symm
  refine ⟨th, fun y => ?_⟩
  obtain ⟨g, i, hg, hi⟩ := hne (t y) (hV y)
  obtain ⟨x, h₁, h₂⟩ := Scheme.exists_preimage_of_isPullback hF g y hg
  obtain rfl : F x = g := h₁
  obtain ⟨k, hk⟩ := exists_chart hL' x
  have hm : F x ∈ p ⁻¹ᵁ V ⊓ L.U i := X.basicOpen_le _ hi
  refine ⟨x, h₂, (SectionBaseChange.mem_nonzeroLocus th _).2 ⟨k, hk, ?_⟩⟩
  have e := hth _ (𝟙 _) x i k hm.2 hk
  rw [val x i hm.2] at e
  have hu : IsUnit (gs (𝟙 X) (F x) _ (θ i)) := by
    rw [gs_eq (𝟙 X) (F x) _ hm]
    exact (X.mem_basicOpen _ _ hm).1 hi
  exact isUnit_of_mul_isUnit_right (e ▸ hu.map (F.stalkMap x).hom)

theorem exists_away_point {R : Type} [CommRing R] (p : PrimeSpectrum R) {r : R} (hr : r ∉ p.asIdeal) :
    ∃ q : PrimeSpectrum (Localization.Away r), spMap (algebraMap R (Localization.Away r)) q = p := by
  have h : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away r))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
    exact hr
  exact h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem exists_pull {B : Type} [CommRing B] {b : Base l B} {S S' : Scheme.{0}} {s : S ⟶ Sp B} (s' : S' ⟶ Sp B)
    (f : S' ⟶ S) (h : f ≫ s = s') (o : Obj D l b s) : ∃ o' : Obj D l b s', Nonempty (ObjMap o' o f) :=
  ObjPull.objPull_of_pol pol_pull E H D l B B b b (RingHom.id B) S S' s s' f rfl rfl
    (h.trans ((Category.comp_id _).symm.trans (congrArg (s' ≫ ·) (Spec.map_id _).symm))) o

theorem objMap_comp {B : Type} [CommRing B] {b : Base l B} {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B}
    {s'' : S'' ⟶ Sp B} {o : Obj D l b s} {o' : Obj D l b s'} {o'' : Obj D l b s''} {f : S' ⟶ S} {f' : S'' ⟶ S'}
    (m' : ObjMap o'' o' f') (m : ObjMap o' o f) : Nonempty (ObjMap o'' o (f' ≫ f)) := by
  obtain ⟨n, -⟩ := ((ObjMaps.id_comp_cancel E H D l B B B b b b S S' S'' s s' s'' o o' o'').2 f f' m).1 m'
  exact ⟨n⟩

theorem exists_eigen_chart (c : Coeff l) {g : ℕ} {ty : Fin g → (E →+* ℂ)} (hty : IsTypeFn H D.p D.q ty)
    {R : Type} [CommRing R] (j : c.F →+* R)
    (o : Obj D l (baseKA l) (spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom)) (p : Sp R) :
    ∃ (R' : Type) (_ : CommRing R') (f : R →+* R')
      (o' : Obj D l (baseKA l) (spMap (f.comp j) ≫ spMap (IntermediateField.inclusion c.le).toRingHom))
      (v : Fin g → (epsR R' ⟶ o'.t.G)), IsOpenImmersion (spMap f) ∧ p ∈ Set.range (spMap f) ∧
      Nonempty (ObjMap o' o (spMap f)) ∧ IsLieBasis v ∧
      ∀ i a, (v i ≫ o'.t.act.act a).left =
        spMap (epsScaleR (f.comp j ⟨ty i (a : E), c.conj (ty i) a⟩)) ≫ (v i).left := by
  obtain ⟨r, hr, v₀, hv₀⟩ := LieLoc.lie_locally_free R o.t.G _ (ObjDim.smoothOfRelativeDimension o) p
  obtain ⟨p₁, hp₁⟩ := exists_away_point p hr
  let R₁ := Localization.Away r
  let f₁ : R →+* R₁ := algebraMap R R₁
  obtain ⟨o₁, ⟨m₁⟩⟩ := exists_pull
    (spMap (f₁.comp j) ≫ spMap (IntermediateField.inclusion c.le).toRingHom) (spMap f₁)
    (by rw [spMap_comp j f₁, Category.assoc]) o
  obtain ⟨e, he, -⟩ := grpPullback_iso m₁.cart (isGrpPullback_pullback o.t.G (spMap f₁))
  have hv₁ : IsLieBasis (fun i => v₀ i ≫ e.inv) := Chart.isLieBasis_iso e (by
    simpa only [Category.assoc, e.inv_hom_id, Category.comp_id] using hv₀)
  obtain ⟨r', hr', Hv⟩ := exists_isLieBasis_eigen E H D l c g ty hty R₁ (f₁.comp j) o₁ _ _ hv₁ p₁
  obtain ⟨p₂, hp₂⟩ := exists_away_point p₁ hr'
  let R₂ := Localization.Away r'
  let f₂ : R₁ →+* R₂ := algebraMap R₁ R₂
  obtain ⟨o₂, ⟨m₂⟩⟩ := exists_pull
    (spMap ((f₂.comp f₁).comp j) ≫ spMap (IntermediateField.inclusion c.le).toRingHom) (spMap f₂)
    (by rw [RingHom.comp_assoc, spMap_comp (f₁.comp j) f₂, Category.assoc]) o₁
  obtain ⟨v, hv, hev⟩ := Hv o₂.t ⟨m₂.toSABMap⟩
  have i₁ : IsOpenImmersion (spMap f₁) := inferInstanceAs (IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))))
  have i₂ : IsOpenImmersion (spMap f₂) := inferInstanceAs (IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (algebraMap R₁ (Localization.Away r')))))
  refine ⟨R₂, inferInstance, f₂.comp f₁, o₂, v, ?_, ?_, ?_, hv, hev⟩
  · rw [spMap_comp f₁ f₂]; infer_instance
  · refine ⟨p₂, ?_⟩
    rw [spMap_comp f₁ f₂]
    exact (congrArg (spMap f₁) hp₂).trans hp₁
  · rw [spMap_comp f₁ f₂]; exact objMap_comp m₂ m₁

theorem exists_chart_eigenframe : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty → ∀ x : Xo.XF c, ∃ (R : Type) (_ : CommRing R) (_ : Algebra c.F R) (jR : Sp R ⟶ Xo.XF c) (o : Obj D l (baseKA l) (spMap (algebraMap c.F R) ≫ spMap (IntermediateField.inclusion c.le).toRingHom)) (v : Fin g → (epsR R ⟶ o.t.G)) (th : o.t.PP.L.Sec), Algebra.FiniteType c.F R ∧ IsReduced R ∧ IsOpenImmersion jR ∧ x ∈ Set.range jR ∧ jR ≫ pullback.snd _ _ = spMap (algebraMap c.F R) ∧ Nonempty (ObjMap o Xo.univ (jR ≫ pullback.fst _ _)) ∧ IsLieBasis v ∧ (∀ i a, (v i ≫ o.t.act.act a).left = spMap (epsScaleR (algebraMap c.F R ⟨ty i (a : E), c.conj (ty i) a⟩)) ≫ (v i).left) ∧ (∀ y : Sp R, ∃ x : o.t.G.left, o.t.G.hom x = y ∧ x ∈ Out.nonzeroLocus th) ∧ (∀ s : o.t.PP.L.Sec, ∃! a : R, ∀ i, s.f i = constFn o.t.G.hom _ a * th.f i) := by
  intro hS E _ _ _ H D l Xo c g ty hty x
  have := Xo.smooth
  have hsm : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have : IsLocallyNoetherian Xo.X := LocallyOfFiniteType.isLocallyNoetherian Xo.s
  let π : Xo.XF c ⟶ Xo.X := pullback.fst _ _
  let σ : Xo.XF c ⟶ Sp c.F := pullback.snd _ _
  have hσ : Smooth σ := inferInstanceAs (Smooth (pullback.snd Xo.s _))
  have hred : AlgebraicGeometry.IsReduced (Xo.XF c) :=
    (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field c.F _ σ hσ).1
  obtain ⟨V, hV, θ, hθ, -, hne⟩ := PushInv.pushInvertible hS Xo.X (Obj.toPolAV Xo.univ) (π x)
  obtain ⟨B, j₀, hj₀, ⟨p, hp⟩, hsub⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (X := Xo.XF c) (x := x) (U := π ⁻¹ᵁ V) hV
  let j : c.F →+* B := (Spec.preimage (j₀ ≫ σ)).hom
  have hj : j₀ ≫ σ = spMap j := (Spec.map_preimage (j₀ ≫ σ)).symm
  obtain ⟨o₀, ⟨m₀⟩⟩ := exists_pull (spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom) (j₀ ≫ π)
    (by rw [← hj, Category.assoc, Category.assoc]; exact congrArg (j₀ ≫ ·) pullback.condition) Xo.univ
  obtain ⟨R, _, f, o, v, hf, ⟨q, hq⟩, ⟨m₁⟩, hv, hev⟩ := exists_eigen_chart c hty j o₀ p
  obtain ⟨m⟩ := objMap_comp m₁ m₀
  let jR : Sp R ⟶ Xo.XF c := spMap f ≫ j₀
  have hjR : IsOpenImmersion jR := IsOpenImmersion.comp (spMap f) j₀
  have hs : jR ≫ σ = spMap (f.comp j) := by
    rw [spMap_comp j f, ← hj]; exact Category.assoc _ _ _
  have hL : LBIso o.t.PP.L (Xo.univ.t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  obtain ⟨th, hth⟩ := exists_sec_of_secOn m.cart.1 Xo.univ.t.PP.isLB o.t.PP.isLB hL (V := V)
    (fun y => hsub ⟨spMap f y, rfl⟩) hθ hne
  letI : Algebra c.F R := (f.comp j).toAlgebra
  refine ⟨R, inferInstance, inferInstance, jR, o, v, th, ?_, ?_, hjR, ⟨q, ?_⟩, hs, ?_, hv, hev, hth,
    SectionBaseChange.generates hS (Obj.toPolAV Xo.univ) m.cart.1 o.t.PP.isLB hL th hth⟩
  · have h : LocallyOfFiniteType (spMap (f.comp j)) := by rw [← hs]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := CommRingCat.ofHom (f.comp j))).1 h
  · have h : AlgebraicGeometry.IsReduced (Sp R) := isReduced_of_isOpenImmersion jR
    exact (affine_isReduced_iff (CommRingCat.of R)).1 h
  · exact (congrArg j₀ hq).trans hp
  · have e : jR ≫ π = spMap f ≫ j₀ ≫ π := Category.assoc _ _ _
    exact (congrArg (fun u => Nonempty (ObjMap o Xo.univ u)) e).mpr ⟨m⟩

end GlobalTheory.ModuliChart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ValVEqOneIntegralGenerators
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ValVEqOneIntegralGenerators
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.IntegralGenerator

section Calc

variable {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}

theorem isoMaps_pt {w : LB.Iso L' (L.pull F)} {σ : LB.Sec L'} {s : LB.Sec (L.pull F)} (h : IsoMaps w σ s)
    {Z : Scheme.{0}} (r : Z ⟶ X') (z : Z) (j : L.ι) (k : L'.ι) (hj : F (r z) ∈ L.U j) (hk : r z ∈ L'.U k) :
    gs r z _ (s.f (fun _ => j)) = (gw w r z j k).val * gs r z _ (σ.f k) := by
  have hm : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
  have e := congrArg (gs r z _) (h (fun _ => j) k)
  exact (gs_res r z _ hm _).symm.trans (e.trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_unit r z _ hm _) (gs_res r z _ hm _))))

theorem pullSec_pt {s : LB.Sec L} {s' : LB.Sec (L.pull F)} (h : PullSec F s s')
    {Z : Scheme.{0}} (r : Z ⟶ X') (z : Z) (j : L.ι) (hj : F (r z) ∈ L.U j) :
    gs r z _ (s'.f (fun _ => j)) = gs (r ≫ F) z _ (s.f j) :=
  (congrArg (gs r z _) (h (fun _ => j) (LB.wchart_le L _ _ PUnit.unit))).trans
    (gs_appLE F _ _ _ r z (mem_pull.2 hj) _)

theorem exists_sec_along (ρ : X ⟶ X') (e : ρ ≫ F = 𝟙 X) (s : LB.Sec (L.pull F)) :
    ∃ τ : LB.Sec L, ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (j : L.ι), r z ∈ L.U j →
      gs r z _ (τ.f j) = gs (r ≫ ρ) z _ (s.f (fun _ => j)) := by
  have le : ∀ j, L.U j ≤ ρ ⁻¹ᵁ (L.pull F).U (fun _ => j) := fun j y hy =>
    mem_pull.2 ((congrArg (fun q => q y ∈ L.U j) e).mpr hy)
  refine ⟨⟨fun j => (ρ.appLE _ _ (le j)).hom (s.f (fun _ => j)), fun j j' => fn_ext fun y hy => ?_⟩,
    fun Z r z j hj => gs_appLE ρ _ _ (le j) r z hj _⟩
  have h₁ : (𝟙 X ≫ ρ) y ∈ (L.pull F).U (fun _ => j) := le j hy.1
  have h₂ : (𝟙 X ≫ ρ) y ∈ (L.pull F).U (fun _ => j') := le j' hy.2
  have g := gm_pull_g L F (𝟙 X ≫ ρ) y _ _ h₁ h₂
  rw [Category.assoc, e, Category.comp_id] at g
  rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_unit _ y _ hy, gs_appLE ρ _ _ _ _ y hy.1,
    gs_appLE ρ _ _ _ _ y hy.2, gs_compat s _ y h₁ h₂, g]

theorem exists_unit_of_iso {V : Type} [CommRing V] (p : X ⟶ Sp V) (p' : X' ⟶ Sp V) (hp : F ≫ p = p') [IsIso F]
    (hL : L.IsLB) (hL' : L'.IsLB) {w : LB.Iso L' (L.pull F)} (hw : PGen w) (θ : LB.Sec L) (θ' : LB.Sec L')
    (hθ : ∀ σ : LB.Sec L, ∃! a : V, ∀ i, σ.f i = constFn p _ a * θ.f i)
    (hθ' : ∀ σ : LB.Sec L', ∃! a : V, ∀ i, σ.f i = constFn p' _ a * θ'.f i) :
    ∃ b : Vˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) j k, F (r z) ∈ L.U j → r z ∈ L'.U k →
      gs (r ≫ F) z _ (θ.f j) = (gw w r z j k).val * (cst (r ≫ p') z (b : V) * gs r z _ (θ'.f k)) := by
  obtain ⟨τ', hτ'⟩ := sec_pull_down hw hL hL' θ
  obtain ⟨b, hb, -⟩ := hθ' τ'
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) j k, F (r z) ∈ L.U j → r z ∈ L'.U k →
      gs (r ≫ F) z _ (θ.f j) = (gw w r z j k).val * (cst (r ≫ p') z b * gs r z _ (θ'.f k)) :=
    fun Z r z j k hj hk => by rw [hτ' Z r z j k hj hk, hb k, gs_mul _ z _ hk, gs_constFn _ _ _ z hk]
  obtain ⟨s, hs⟩ := thf_secUp hw hL hL' θ'
  obtain ⟨τ, hτ⟩ := exists_sec_along (inv F) (IsIso.inv_hom_id F) s
  obtain ⟨b', hb', -⟩ := hθ τ
  have one : ∀ k, θ'.f k = constFn p' _ (b' * b) * θ'.f k := (sec_eq_iff _ _ _ _).2 fun k y hy => by
    obtain ⟨j, hj⟩ := exists_chart hL (F y)
    have e₁ := hτ _ F y j hj
    have e₂ := key _ (𝟙 _) y j k hj hy
    rw [IsIso.hom_inv_id, hs _ (𝟙 _) y (fun _ => j) k (mem_pull.2 hj) hy, hb' j, gs_mul _ y _ hj,
      gs_constFn _ _ _ y hj, hp] at e₁
    rw [Category.id_comp, Category.id_comp] at e₂
    rw [e₂, mul_left_comm, Units.mul_right_inj, ← _root_.mul_assoc, ← H1.cst_mul] at e₁
    exact e₁.symm
  have one' : ∀ k, θ'.f k = constFn p' _ 1 * θ'.f k := (sec_eq_iff _ _ _ _).2 fun k y _ => by
    rw [H1.cst_one, _root_.one_mul]
  have u : b' * b = 1 := (hθ' θ').unique one one'
  exact ⟨⟨b, b', (mul_comm _ _).trans u, u⟩, key⟩

end Calc

section Rig

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']

theorem gw_eq_of_rig (hp : Function.Surjective G'.hom.appTop.hom) (L : RigLB G) (L' : RigLB G')
    {F₁ F₂ : G'.left ⟶ G.left} {e₁ e₂ : S' ⟶ S} (hF : F₁ = F₂) (he : e₁ = e₂)
    {w₁ : LB.Iso L'.L (L.L.pull F₁)} {w₂ : LB.Iso L'.L (L.L.pull F₂)} (g₁ : PGen w₁) (g₂ : PGen w₂)
    (m₁ : PMaps w₁ (K := PUnit) (fun _ => eSec G') (fun _ => eSec G) (fun _ => 1) L'.rig L.rig e₁)
    (m₂ : PMaps w₂ (K := PUnit) (fun _ => eSec G') (fun _ => eSec G) (fun _ => 1) L'.rig L.rig e₂)
    {Z : Scheme.{0}} (r : Z ⟶ G'.left) (z : Z) (j : L.L.ι) (k : L'.L.ι) : gw w₁ r z j k = gw w₂ r z j k := by
  subst hF he
  have : w₁ = w₂ := by
    refine gen_eq_of_eq_along_section (fun y => ?_) G'.hom (eSec G') (Over.w η[G']) hp
      ((isGen_iff _).2 g₁) ((isGen_iff _).2 g₂) ?_
    · obtain ⟨i, hi⟩ := exists_chart L'.isLB y
      obtain ⟨j, hj⟩ := exists_chart L.isLB (F₁ y)
      exact ⟨(fun _ => j, i), mem_pull.2 hj, hi⟩
    · rintro s ⟨j, i⟩ ⟨hj, hi⟩
      have k₁ := m₁ _ (𝟙 _) s j (fun _ => i) (fun _ => mem_pull.1 hj) (fun _ => hi)
      have k₂ := m₂ _ (𝟙 _) s j (fun _ => i) (fun _ => mem_pull.1 hj) (fun _ => hi)
      rw [Fintype.prod_unique, zpow_one] at k₁ k₂
      have := mul_right_cancel (k₁.symm.trans k₂)
      rw [Category.id_comp] at this
      exact this
  rw [this]

end Rig

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem rigIso_iff {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    (w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)) :
    RigIso m w ↔ PGen w ∧
      PMaps w (K := PUnit) (fun _ => eSec t'.G) (fun _ => eSec t.G) (fun _ => 1) t'.PP.rig t.PP.rig m.cm.e :=
  and_congr (isGen_iff w) (maps_iff w _ (fun _ => eSec t.G) _ t'.PP.rig t.PP.rig m.cm.e _
    (rigPull_le m.cm.F m.cm.e m.cm.e_comm t.PP.L) (fun _ => rfl))

theorem valV_unit (T : CDVR) (b : T.Vˣ) : valV T.V (algebraMap T.V T.Fr (b : T.V)) = 1 := by
  have h₁ : valV T.V (algebraMap T.V T.Fr (b : T.V)) ≤ 1 := IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ _
  have h₂ : valV T.V (algebraMap T.V T.Fr ((b⁻¹ : T.Vˣ) : T.V)) ≤ 1 :=
    IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ _
  have h₃ : valV T.V (algebraMap T.V T.Fr (b : T.V)) * valV T.V (algebraMap T.V T.Fr ((b⁻¹ : T.Vˣ) : T.V)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  exact le_antisymm h₁ (h₃.ge.trans (mul_le_of_le_one_right' h₂))

theorem valV_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (y y' : FrPt Xo c T.Fr) (G G₂ : SAB H (Sp T.V)) (t t₂ : SAB H (Sp T.Fr)) (m₁ : SABMap t Xo.univ.t y.x) (m₂ : SABMap t G (spMap (algebraMap T.V T.Fr))) (n₁ : SABMap t₂ Xo.univ.t y'.x) (n₂ : SABMap t₂ G₂ (spMap (algebraMap T.V T.Fr))) (k : SABMap t t₂ (𝟙 _)) (n : SABMap G G₂ (𝟙 _)), y'.x = y.x → k.φ ≫ n₁.φ = m₁.φ → m₂.φ ≫ n.φ = k.φ ≫ n₂.φ → ∀ (θ : LB.Sec G.PP.L) (θ₂ : LB.Sec G₂.PP.L), ((∀ σ : LB.Sec G.PP.L, ∃! a : T.V, ∀ i, σ.f i = resG G.G.left (le_top : G.PP.L.U i ≤ ⊤) ((G.G.hom).appTop.hom (toΓ T.V a)) * θ.f i) ∧ ∃ (w1 : LB.Iso t.PP.L (Xo.univ.t.PP.L.pull m₁.φ)) (w2 : LB.Iso t.PP.L (G.PP.L.pull m₂.φ)) (σ : LB.Sec t.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull m₁.φ)) (θ2 : LB.Sec (G.PP.L.pull m₂.φ)), RigIso m₁ w1 ∧ RigIso m₂ w2 ∧ IsoMaps w1 σ s1 ∧ IsoMaps w2 σ θ2 ∧ PullSec m₂.φ θ θ2 ∧ ∀ g : t.G.left ⟶ Gx y.x, g ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = m₁.φ → g ≫ (fst (Over.mk y.x) Xo.univ.t.G).left = t.G.hom → ∀ j (h : (Xo.univ.t.PP.L.pull m₁.φ).U j ≤ g ⁻¹ᵁ (PPx y.x).U (fun _ => j PUnit.unit)), s1.f j = (g.appLE _ _ h).hom (y.s.f (fun _ => j PUnit.unit))) → ((∀ σ : LB.Sec G₂.PP.L, ∃! a : T.V, ∀ i, σ.f i = resG G₂.G.left (le_top : G₂.PP.L.U i ≤ ⊤) ((G₂.G.hom).appTop.hom (toΓ T.V a)) * θ₂.f i) ∧ ∃ (w1 : LB.Iso t₂.PP.L (Xo.univ.t.PP.L.pull n₁.φ)) (w2 : LB.Iso t₂.PP.L (G₂.PP.L.pull n₂.φ)) (σ : LB.Sec t₂.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull n₁.φ)) (θ2 : LB.Sec (G₂.PP.L.pull n₂.φ)), RigIso n₁ w1 ∧ RigIso n₂ w2 ∧ IsoMaps w1 σ s1 ∧ IsoMaps w2 σ θ2 ∧ PullSec n₂.φ θ₂ θ2 ∧ ∀ g : t₂.G.left ⟶ Gx y'.x, g ≫ (snd (Over.mk y'.x) Xo.univ.t.G).left = n₁.φ → g ≫ (fst (Over.mk y'.x) Xo.univ.t.G).left = t₂.G.hom → ∀ j (h : (Xo.univ.t.PP.L.pull n₁.φ).U j ≤ g ⁻¹ᵁ (PPx y'.x).U (fun _ => j PUnit.unit)), s1.f j = (g.appLE _ _ h).hom (y'.s.f (fun _ => j PUnit.unit))) → ∀ a : T.Frˣ, SecBC (RingHom.id T.Fr) (a : T.Fr) y.x y'.x y.s y'.s → valV T.V (a : T.Fr) = 1 := by
  intro E _ _ _ H Dw l Xo c T io
  letI := io.toAlgebra
  intro y y' G G₂ t t₂ m₁ m₂ n₁ n₂ k n hx hk hn θ θ₂ ⟨hθ, w1, w2, σ, s1, θ2, r1, r2, i1, i2, q, hg⟩
    ⟨hθ', w1', w2', σ', s1', θ2', r1', r2', i1', i2', q', hg'⟩ a hab
  obtain ⟨x, hxo, u, htan, heig, hbas, s, hgen⟩ := y
  obtain ⟨x', hxo', u', htan', heig', hbas', s', hgen'⟩ := y'
  dsimp only at hx m₁ n₁ hk hn w1 s1 r1 i1 hg w1' s1' r1' i1' hg' hab
  subst hx
  obtain ⟨g1, p1⟩ := (rigIso_iff _ _).1 r1
  obtain ⟨g2, p2⟩ := (rigIso_iff _ _).1 r2
  obtain ⟨g1', p1'⟩ := (rigIso_iff _ _).1 r1'
  obtain ⟨g2', p2'⟩ := (rigIso_iff _ _).1 r2'
  obtain ⟨wk, gk, pk, -⟩ := (isPullCubical_iff _ _ _).1 k.lin
  obtain ⟨wn, gn, pn, -⟩ := (isPullCubical_iff _ _ _).1 n.lin
  have hsurj : Function.Surjective t.G.hom.appTop.hom :=
    (GlobalTheory.laws_without_cohomology.1 _ t.G ⟨inferInstance, t.semi.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) m₁.cart.1 Xo.univ.proper, t.semi.geomConnected⟩).2

  obtain ⟨wa, Ta⟩ := exists_comp t₂.PP.isLB w1' wk g1' gk Xo.univ.t.PP.isLB t.PP.isLB
  obtain ⟨wb, Tb⟩ := exists_comp t₂.PP.isLB w2' wk g2' gk G₂.PP.isLB t.PP.isLB
  obtain ⟨wc, Tc⟩ := exists_comp G.PP.isLB wn w2 gn g2 G₂.PP.isLB t.PP.isLB
  have ea := @gw_eq_of_rig _ _ _ _ _ _ _ _ hsurj Xo.univ.t.PP t.PP _ _ _ _ hk
    (by rw [k.base, n₁.base, m₁.base]; exact Category.id_comp _) wa w1 (Ta.pgen_comp t₂.PP.isLB g1' gk) g1
    (Ta.pmaps_comp t₂.PP.isLB (fun _ => k.cm.e_comm) p1' pk) p1
  have eb := @gw_eq_of_rig _ _ _ _ _ _ _ _ hsurj G₂.PP t.PP _ _ _ _ hn
    (by rw [k.base, n₂.base, m₂.base, n.base]; exact (Category.comp_id _).trans (Category.id_comp _).symm) wc wb
    (Tc.pgen_comp G.PP.isLB gn g2) (Tb.pgen_comp t₂.PP.isLB g2' gk)
    (Tc.pmaps_comp G.PP.isLB (fun _ => m₂.cm.e_comm) pn p2) (Tb.pmaps_comp t₂.PP.isLB (fun _ => k.cm.e_comm) p2' pk)
  haveI : IsIso n.φ := n.cart.1.isIso_fst_of_isIso
  obtain ⟨b, hb⟩ := exists_unit_of_iso G₂.G.hom G.G.hom (n.cart.1.w.trans (Category.comp_id _)) G₂.PP.isLB G.PP.isLB gn
    θ₂ θ hθ' hθ

  let A := Xo.univ.t.G
  have canon : ∀ (t' : SAB H (Sp T.Fr)) (m : SABMap t' Xo.univ.t x'), ∃ g : t'.G.left ⟶ Gx x',
      g ≫ (snd (Over.mk x') A).left = m.φ ∧ g ≫ (fst (Over.mk x') A).left = t'.G.hom := fun t' m =>
    let a0 : Over.mk (t'.G.hom ≫ x') ⟶ Over.mk x' := Over.homMk t'.G.hom rfl
    let b0 : Over.mk (t'.G.hom ≫ x') ⟶ A := Over.homMk m.φ m.cart.1.w
    ⟨(lift a0 b0).left, congrArg (fun q => q.left) (lift_snd a0 b0), congrArg (fun q => q.left) (lift_fst a0 b0)⟩
  obtain ⟨g, gs₁, gf₁⟩ := canon t m₁
  obtain ⟨g', gs₂, gf₂⟩ := canon t₂ n₁
  have cond : (snd (Over.mk x') A).left ≫ A.hom = (fst (Over.mk x') A).left ≫ x' :=
    (Over.w (snd (Over.mk x') A)).trans (Over.w (fst (Over.mk x') A)).symm
  obtain ⟨h, hφ, hh⟩ : ∃ h : Gx x' ⟶ t.G.left, h ≫ m₁.φ = (snd (Over.mk x') A).left ∧
      h ≫ t.G.hom = (fst (Over.mk x') A).left :=
    ⟨m₁.cart.1.lift _ _ cond, m₁.cart.1.lift_fst _ _ cond, m₁.cart.1.lift_snd _ _ cond⟩
  have ext : ∀ e : Gx x' ⟶ Gx x', e ≫ (snd (Over.mk x') A).left = (snd (Over.mk x') A).left →
      e ≫ (fst (Over.mk x') A).left = (fst (Over.mk x') A).left → e = 𝟙 _ := fun e e₁ e₂ =>
    pullback.hom_ext (e₂.trans (Category.id_comp _).symm) (e₁.trans (Category.id_comp _).symm)
  have kw : k.φ ≫ t₂.G.hom = t.G.hom := k.cart.1.w.trans (Category.comp_id _)
  have hg₁ : h ≫ g = 𝟙 _ := ext _ (by rw [Category.assoc, gs₁, hφ]) (by rw [Category.assoc, gf₁, hh])
  have hg₂ : (h ≫ k.φ) ≫ g' = 𝟙 _ := ext _ (by rw [Category.assoc, gs₂, Category.assoc, hk, hφ])
    (by rw [Category.assoc, gf₂, Category.assoc, kw, hh])
  have le : ∀ (t' : SAB H (Sp T.Fr)) (φ : t'.G.left ⟶ A.left) (g : t'.G.left ⟶ Gx x'),
      g ≫ (snd (Over.mk x') A).left = φ → ∀ j,
      (Xo.univ.t.PP.L.pull φ).U (fun _ => j) ≤ g ⁻¹ᵁ (PPx x').U (fun _ => j) := fun t' φ g e j z hz =>
    Set.mem_iInter.2 fun _ => (congrArg (fun q => q z ∈ Xo.univ.t.PP.L.U j) e).mpr (mem_pull.1 hz)
  have main : ∀ i, s'.f i = scal x' (algebraMap T.V T.Fr (b : T.V)) i * s.f i := by
    intro (i : Fin 1 → Xo.univ.t.PP.L.ι)
    obtain ⟨j, rfl⟩ : ∃ j, i = fun _ => j := ⟨i 0, funext fun k => congrArg i (Subsingleton.elim k 0)⟩
    refine fn_ext fun z hz => ?_
    have hj : m₁.φ (h z) ∈ Xo.univ.t.PP.L.U j :=
      (congrArg (fun q => q z ∈ Xo.univ.t.PP.L.U j) hφ).mpr (Set.mem_iInter.1 hz 0)
    have hj' : n₁.φ (k.φ (h z)) ∈ Xo.univ.t.PP.L.U j := (congrArg (fun q => q (h z) ∈ Xo.univ.t.PP.L.U j) hk).mpr hj
    obtain ⟨κ, hκ⟩ := exists_chart t.PP.isLB (h z)
    obtain ⟨κ', hκ'⟩ := exists_chart t₂.PP.isLB (k.φ (h z))
    obtain ⟨ν, hν⟩ := exists_chart G.PP.isLB (m₂.φ (h z))
    obtain ⟨ν', hν'⟩ := exists_chart G₂.PP.isLB (n.φ (m₂.φ (h z)))
    have hν'' : n₂.φ (k.φ (h z)) ∈ G₂.PP.L.U ν' := (congrArg (fun q => q (h z) ∈ G₂.PP.L.U ν') hn).mp hν'
    have e₁ : gs (𝟙 _) z _ (s.f (fun _ => j)) = (gw w1 h z j κ).val * gs h z _ (σ.f κ) := by
      rw [← isoMaps_pt i1 h z j κ hj hκ, hg g gs₁ gf₁ (fun _ => j) (le t _ g gs₁ j), ← hg₁]
      exact (gs_appLE g _ _ _ h z (mem_pull.2 hj) _).symm
    have e₂ : gs (𝟙 _) z _ (s'.f (fun _ => j)) = (gw w1' (h ≫ k.φ) z j κ').val * gs (h ≫ k.φ) z _ (σ'.f κ') := by
      rw [← isoMaps_pt i1' (h ≫ k.φ) z j κ' hj' hκ', hg' g' gs₂ gf₂ (fun _ => j) (le t₂ _ g' gs₂ j), ← hg₂]
      exact (gs_appLE g' _ _ _ (h ≫ k.φ) z (mem_pull.2 hj') _).symm
    have e₃ := (pullSec_pt q h z ν hν).symm.trans (isoMaps_pt i2 h z ν κ hν hκ)
    have e₄ := (pullSec_pt q' (h ≫ k.φ) z ν' hν'').symm.trans (isoMaps_pt i2' (h ≫ k.φ) z ν' κ' hν'' hκ')
    have e₅ := hb _ (h ≫ m₂.φ) z ν' ν hν' hν
    have e₆ := (Ta _ h z j κ' κ hj' hκ' hκ).symm.trans (ea h z j κ)
    have e₇ := (Tc _ h z ν' ν κ hν' hν hκ).symm.trans ((eb h z ν' κ).trans (Tb _ h z ν' κ' κ hν'' hκ' hκ))
    have c₁ : (h ≫ m₂.φ) ≫ n.φ = (h ≫ k.φ) ≫ n₂.φ := by rw [Category.assoc, hn, Category.assoc]
    have c₂ : cst ((h ≫ m₂.φ) ≫ G.G.hom) z (b : T.V) =
        gs (𝟙 _) z _ (scal x' (algebraMap T.V T.Fr (b : T.V)) (fun _ => j)) := by
      rw [Category.assoc, m₂.cart.1.w, ← Category.assoc, hh, cst_comp]
      exact ((gs_constFn (fst (Over.mk x') A).left _ (𝟙 _) z hz _).trans (by rw [Category.id_comp])).symm
    rw [c₁, e₄, e₃, c₂, mul_left_comm, ← _root_.mul_assoc (gw wn _ _ _ _).val, ← Units.val_mul, e₇,
      Units.val_mul, _root_.mul_assoc, mul_left_comm _ (gw w2' _ _ _ _).val, Units.mul_right_inj] at e₅
    rw [gs_mul _ z _ hz, e₁, e₂, e₅, ← e₆, Units.val_mul]
    ring
  obtain ⟨pm, h₁, h₂, h₃⟩ := hab
  obtain rfl : pm = 𝟙 _ := ext pm h₁ (h₂.trans ((congrArg (_ ≫ ·) (Spec.map_id _)).trans (Category.comp_id _)))
  have main' : ∀ i, s'.f i = scal x' (a : T.Fr) i * s.f i := fun i => fn_ext fun z hz => by
    rw [← h₃ i le_rfl]
    exact (gs_appLE (𝟙 _) _ _ _ (𝟙 _) z hz _).trans (by rw [Category.id_comp])
  rw [(hgen s').unique main' main]
  exact valV_unit T b

end GlobalTheory.IntegralGenerator
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ValVEqOneIntegralGeneratorsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valV_eq_one_integral_generators : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (y y' : FrPt Xo c T.Fr) (G G₂ : SAB H (Sp T.V)) (t t₂ : SAB H (Sp T.Fr)) (m₁ : SABMap t Xo.univ.t y.x) (m₂ : SABMap t G (spMap (algebraMap T.V T.Fr))) (n₁ : SABMap t₂ Xo.univ.t y'.x) (n₂ : SABMap t₂ G₂ (spMap (algebraMap T.V T.Fr))) (k : SABMap t t₂ (𝟙 _)) (n : SABMap G G₂ (𝟙 _)), y'.x = y.x → k.φ ≫ n₁.φ = m₁.φ → m₂.φ ≫ n.φ = k.φ ≫ n₂.φ → ∀ (θ : LB.Sec G.PP.L) (θ₂ : LB.Sec G₂.PP.L), ((∀ σ : LB.Sec G.PP.L, ∃! a : T.V, ∀ i, σ.f i = resG G.G.left (le_top : G.PP.L.U i ≤ ⊤) ((G.G.hom).appTop.hom (toΓ T.V a)) * θ.f i) ∧ ∃ (w1 : LB.Iso t.PP.L (Xo.univ.t.PP.L.pull m₁.φ)) (w2 : LB.Iso t.PP.L (G.PP.L.pull m₂.φ)) (σ : LB.Sec t.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull m₁.φ)) (θ2 : LB.Sec (G.PP.L.pull m₂.φ)), RigIso m₁ w1 ∧ RigIso m₂ w2 ∧ IsoMaps w1 σ s1 ∧ IsoMaps w2 σ θ2 ∧ PullSec m₂.φ θ θ2 ∧ ∀ g : t.G.left ⟶ Gx y.x, g ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = m₁.φ → g ≫ (fst (Over.mk y.x) Xo.univ.t.G).left = t.G.hom → ∀ j (h : (Xo.univ.t.PP.L.pull m₁.φ).U j ≤ g ⁻¹ᵁ (PPx y.x).U (fun _ => j PUnit.unit)), s1.f j = (g.appLE _ _ h).hom (y.s.f (fun _ => j PUnit.unit))) → ((∀ σ : LB.Sec G₂.PP.L, ∃! a : T.V, ∀ i, σ.f i = resG G₂.G.left (le_top : G₂.PP.L.U i ≤ ⊤) ((G₂.G.hom).appTop.hom (toΓ T.V a)) * θ₂.f i) ∧ ∃ (w1 : LB.Iso t₂.PP.L (Xo.univ.t.PP.L.pull n₁.φ)) (w2 : LB.Iso t₂.PP.L (G₂.PP.L.pull n₂.φ)) (σ : LB.Sec t₂.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull n₁.φ)) (θ2 : LB.Sec (G₂.PP.L.pull n₂.φ)), RigIso n₁ w1 ∧ RigIso n₂ w2 ∧ IsoMaps w1 σ s1 ∧ IsoMaps w2 σ θ2 ∧ PullSec n₂.φ θ₂ θ2 ∧ ∀ g : t₂.G.left ⟶ Gx y'.x, g ≫ (snd (Over.mk y'.x) Xo.univ.t.G).left = n₁.φ → g ≫ (fst (Over.mk y'.x) Xo.univ.t.G).left = t₂.G.hom → ∀ j (h : (Xo.univ.t.PP.L.pull n₁.φ).U j ≤ g ⁻¹ᵁ (PPx y'.x).U (fun _ => j PUnit.unit)), s1.f j = (g.appLE _ _ h).hom (y'.s.f (fun _ => j PUnit.unit))) → ∀ a : T.Frˣ, SecBC (RingHom.id T.Fr) (a : T.Fr) y.x y'.x y.s y'.s → valV T.V (a : T.Fr) = 1 := by
  first | exact @GlobalTheory.IntegralGenerator.valV_eq_one | exact GlobalTheory.IntegralGenerator.valV_eq_one | (intros; apply GlobalTheory.IntegralGenerator.valV_eq_one <;> assumption)
end
end
