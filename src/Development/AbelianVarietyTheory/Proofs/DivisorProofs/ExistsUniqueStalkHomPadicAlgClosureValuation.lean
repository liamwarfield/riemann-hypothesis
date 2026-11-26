module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReferenceCoreOfSumPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharactersRestrictLinearToTraitUniformisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFromBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionTowerPresentationCotangentPullbackResRigi
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CountingVolumeLeSelfIntersectionNefHermitianBund
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMultiplierIntegralImaginary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFacts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalLagrangianInvariantFormUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalScalarNormalisedStandardFrame

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueStalkHomPadicAlgClosureValuation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueStalkHomPadicAlgClosureValuation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.ValPt

theorem exists_unique_stalk_hom : ∀ (X : Scheme.{0}) (x : X) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ X), y (cPt p) = x → ∃ φ : X.presheaf.stalk x →+* OO p, IsLocalHom φ ∧ spMap φ ≫ X.fromSpecStalk x = y ∧ ∀ g : X.presheaf.stalk x →+* OO p, spMap g ≫ X.fromSpecStalk x = y → g = φ := by
  intro X x p _ y hy
  subst hy
  refine ⟨(Scheme.stalkClosedPointTo y).hom, inferInstance, Scheme.Spec_stalkClosedPointTo_fromSpecStalk y, ?_⟩
  intro g hg
  have hpt : (X.fromSpecStalk (y (cPt p))) ((spMap g) (cPt p)) =
      (X.fromSpecStalk (y (cPt p))) (closedPoint (X.presheaf.stalk (y (cPt p)))) := by
    rw [Scheme.fromSpecStalk_closedPoint]
    exact congrArg (fun f : Sp (OO p) ⟶ X => f (cPt p)) hg
  have hinj : Function.Injective (X.fromSpecStalk (y (cPt p))) :=
    (X.fromSpecStalk (y (cPt p))).isEmbedding.injective
  have hloc : IsLocalHom g := by
    rw [isLocalHom_iff_comap_closedPoint]
    exact hinj hpt
  have e2 := (SpecToEquivOfLocalRing X (CommRingCat.of (OO p))).symm.injective
    (a₁ := ⟨y (cPt p), CommRingCat.ofHom g, hloc⟩)
    (a₂ := ⟨y (cPt p), Scheme.stalkClosedPointTo y, inferInstance⟩)
    (by rw [SpecToEquivOfLocalRing_symm_apply, SpecToEquivOfLocalRing_symm_apply]
        exact hg.trans (Scheme.Spec_stalkClosedPointTo_fromSpecStalk y).symm)
  obtain ⟨_, e3⟩ := SpecToEquivOfLocalRing_eq_iff.mp e2
  simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp] at e3
  exact congrArg CommRingCat.Hom.hom e3

end GlobalTheory.ValPt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueStalkHomPadicAlgClosureValuationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unique_stalkHom_padicAlgClosure_valuation : ∀ (X : Scheme.{0}) (x : X) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ X), y (cPt p) = x → ∃ φ : X.presheaf.stalk x →+* OO p, IsLocalHom φ ∧ spMap φ ≫ X.fromSpecStalk x = y ∧ ∀ g : X.presheaf.stalk x →+* OO p, spMap g ≫ X.fromSpecStalk x = y → g = φ := by
  first | exact @GlobalTheory.ValPt.exists_unique_stalk_hom | exact GlobalTheory.ValPt.exists_unique_stalk_hom | (intros; apply GlobalTheory.ValPt.exists_unique_stalk_hom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefShiftOfGeneratedAtCharZeroPoints
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefOfGen

theorem card_pos_of_isAlgPt {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}
    (hX : IsArithVar p D) {x : X} (hx : IsAlgPt x) : (0 : ℝ) < Nat.card (X.residueField x →+* ℂ) := by
  obtain ⟨hc, hd⟩ := hx
  obtain ⟨Z, i, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint x
  have hr : Set.range i = closure {i (genericPoint Z)} := by
    have h₁ := (genericPoint_spec Z).image i.continuous
    rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] at h₁
    exact h₁.def.symm
  rw [topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hr] at hd
  have hbij : Function.Bijective (i.residueFieldMap (genericPoint Z)).hom := by
    refine ⟨RingHom.injective _, fun u => ?_⟩
    obtain ⟨u, rfl⟩ := Z.residue_surjective _ u
    obtain ⟨u, rfl⟩ := i.stalkMap_surjective _ u
    exact ⟨X.residue _ u, ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap i _) u⟩
  have hc' : CharZero (Z.residueField (genericPoint Z)) := (RingHom.charZero_iff hbij.1).1 hc
  have hcΓ : CharZero Γ(Z, ⊤) := (Z.Γevaluation (genericPoint Z)).hom.charZero
  have hZ : IsArithVar (i ≫ p) 0 := hX.of_isClosedImmersion i hcΓ hd
  have := GlobalTheory.SmallSecHeight.numberField hZ hc'
  rw [GlobalTheory.HtSelfInter.card_ringHom_eq]
  exact_mod_cast Nat.card_pos

theorem nef_of_gen : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M : HermLB p) (m N : ℕ) (s : Fin N → (M.pow m).B.Sec), 1 ≤ m → (∀ x : X, CharZero (X.residueField x) → ∃ i, x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s i)) → M.SemiPos D → NefFib M → ∃ t : ℝ, 0 ≤ t ∧ (M.shift (fun _ => t) fun _ => rfl).IsNef D := by
  intro hA k _ X _ p D hX M m N s hm hs hsp hf
  have hc : ∀ i, ∃ c : ℝ, s i ∈ ((M.shift (fun _ => -c) fun _ => rfl).pow m).smallSec :=
    fun i => GlobalTheory.AmpleHtLow.small_of_shift k X p D hX M m hm (s i)
  choose c hc using hc
  obtain ⟨h, H⟩ := (hA.arExists k X p D hX).1 M
  refine ⟨-(-(∑ i, |c i|)), ?_, GlobalTheory.HtSelfInter.isNef_shift hX hsp hf fun x hx => ?_⟩
  · rw [neg_neg]
    exact Finset.sum_nonneg fun j _ => abs_nonneg (c j)
  obtain ⟨i, hi⟩ := hs x hx.1
  have hN := card_pos_of_isAlgPt hX hx
  have hb : IsPtHt M x (h x / Nat.card (X.residueField x →+* ℂ)) :=
    ⟨h, H, (div_mul_cancel₀ _ hN.ne').symm⟩
  refine ⟨_, hb, ?_⟩
  have h1 := GlobalTheory.SmallSecHeight.le_ptHt k X p D hX M m (c i) _ x (s i) hm (hc i) hi hx hb
  have h2 : -(∑ j, |c j|) ≤ c i :=
    (neg_le_neg (Finset.single_le_sum (fun j _ => abs_nonneg (c j)) (Finset.mem_univ i))).trans (neg_abs_le _)
  exact h2.trans h1

end GlobalTheory.NefOfGen

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoEighthPowerGroupPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoEighthPowerGroupPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.Eq8

theorem lift_left_comp {T T' : Scheme.{0}} {B C : Over T} {B' C' : Over T'} {φB : B'.left ⟶ B.left}
    {χ : C'.left ⟶ C.left} {χ₂ : (C' ⊗ C').left ⟶ (C ⊗ C).left} (hsq : IsSquare χ χ₂)
    (x y : B ⟶ C) (x' y' : B' ⟶ C') (hx : x'.left ≫ χ = φB ≫ x.left) (hy : y'.left ≫ χ = φB ≫ y.left) :
    (lift x' y').left ≫ χ₂ = φB ≫ (lift x y).left := by
  have f1 : (lift x y).left ≫ (fst C C).left = x.left := congrArg (fun q => q.left) (lift_fst x y)
  have f2 : (lift x y).left ≫ (snd C C).left = y.left := congrArg (fun q => q.left) (lift_snd x y)
  have f1' : (lift x' y').left ≫ (fst C' C').left = x'.left := congrArg (fun q => q.left) (lift_fst x' y')
  have f2' : (lift x' y').left ≫ (snd C' C').left = y'.left := congrArg (fun q => q.left) (lift_snd x' y')
  apply pullback.hom_ext
  · show (_ ≫ _) ≫ (fst C C).left = (_ ≫ _) ≫ (fst C C).left
    rw [Category.assoc, hsq.1, ← Category.assoc, f1', hx, Category.assoc, f1]
  · show (_ ≫ _) ≫ (snd C C).left = (_ ≫ _) ≫ (snd C C).left
    rw [Category.assoc, hsq.2, ← Category.assoc, f2', hy, Category.assoc, f2]

theorem lbIso_eighth_pull : ∀ {T T' : Scheme.{0}} {B C : Over T} {B' C' : Over T'} {φB : B'.left ⟶ B.left} {χ : C'.left ⟶ C.left} {χ₂ : (C' ⊗ C').left ⟶ (C ⊗ C).left} (Q : LB (C ⊗ C).left) (Q' : LB (C' ⊗ C').left) (L : LB B.left) (L' : LB B'.left) (pr : Fin 8 → (B ⟶ C)) (pr' : Fin 8 → (B' ⟶ C')) (W : Matrix (Fin 8) (Fin 8) ℤ), Q.IsLB → Q'.IsLB → L.IsLB → L'.IsLB → IsSquare χ χ₂ → LBIso Q' (Q.pull χ₂) → (∀ a, (pr' a).left ≫ χ = φB ≫ (pr a).left) → LBIso L' (L.pull φB) → LBIso L (LB.LinComb Q (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → LBIso L' (LB.LinComb Q' (K := Fin 8 × Fin 8) (fun ab => (lift (pr' ab.1) (pr' ab.2)).left) (fun ab => W ab.1 ab.2)) := by
  intro T T' B C B' C' φB χ χ₂ Q Q' L L' pr pr' W hQ hQ' hL hL' hsq HQ hpr h1 hLL
  have h3 := GlobalTheory.ShapePull.iso_linComb_pull HQ (K := Fin 8 × Fin 8)
    (fun ab => (lift (pr' ab.1) (pr' ab.2)).left) (fun ab => (lift (pr ab.1) (pr ab.2)).left)
    (fun ab => W ab.1 ab.2) φB (fun ab => lift_left_comp hsq _ _ _ _ (hpr ab.1) (hpr ab.2))
  have h2 := GlobalTheory.SiegelPullComp.iso_pull φB hLL
  have lc : (LB.LinComb Q (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left)
      (fun ab => W ab.1 ab.2)).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ hQ _ _
  have lc' : (LB.LinComb Q' (K := Fin 8 × Fin 8) (fun ab => (lift (pr' ab.1) (pr' ab.2)).left)
      (fun ab => W ab.1 ab.2)).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ hQ' _ _
  exact LBIso.trans hL' (pull_isLB hL φB) lc' h1
    (LBIso.trans (pull_isLB hL φB) (pull_isLB lc φB) lc' h2 h3.symm)

end GlobalTheory.Poinc.Eq8
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoEighthPowerGroupPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIso_eighthPower_groupPullback : ∀ {T T' : Scheme.{0}} {B C : Over T} {B' C' : Over T'} {φB : B'.left ⟶ B.left} {χ : C'.left ⟶ C.left} {χ₂ : (C' ⊗ C').left ⟶ (C ⊗ C).left} (Q : LB (C ⊗ C).left) (Q' : LB (C' ⊗ C').left) (L : LB B.left) (L' : LB B'.left) (pr : Fin 8 → (B ⟶ C)) (pr' : Fin 8 → (B' ⟶ C')) (W : Matrix (Fin 8) (Fin 8) ℤ), Q.IsLB → Q'.IsLB → L.IsLB → L'.IsLB → IsSquare χ χ₂ → LBIso Q' (Q.pull χ₂) → (∀ a, (pr' a).left ≫ χ = φB ≫ (pr a).left) → LBIso L' (L.pull φB) → LBIso L (LB.LinComb Q (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → LBIso L' (LB.LinComb Q' (K := Fin 8 × Fin 8) (fun ab => (lift (pr' ab.1) (pr' ab.2)).left) (fun ab => W ab.1 ab.2)) := by
  first | exact @GlobalTheory.Poinc.Eq8.lbIso_eighth_pull | exact GlobalTheory.Poinc.Eq8.lbIso_eighth_pull | (intros; apply GlobalTheory.Poinc.Eq8.lbIso_eighth_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesAlgHomKillHighOrder
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

theorem mvPowerSeries_algHom_kill_high_order :
    ∀ (k : Type) [CommRing k] (σ : Type) [Finite σ] (A : Type) [CommRing A] [Algebra k A],
      ∀ φ : MvPowerSeries σ k →ₐ[k] A, (∀ i, IsNilpotent (φ (X i))) →
        ∃ N : ℕ, ∀ f : MvPowerSeries σ k,
          (∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) → φ f = 0 := by
  intro k _ σ _ A _ _ φ hφ
  classical
  haveI := Fintype.ofFinite σ
  choose m hm using hφ
  set M := Finset.univ.sup m with hMdef
  have hM : ∀ i, φ (X i) ^ M = 0 := fun i =>
    pow_eq_zero_of_le (Finset.le_sup (Finset.mem_univ i)) (hm i)
  refine ⟨Fintype.card σ * M + 1, fun f hf => ?_⟩

  let fi : σ → MvPowerSeries σ k := fun i α =>
    if h : ∃ j, M ≤ α j then (if h.choose = i then coeff α f else 0) else 0
  have hcoeff : ∀ i α, coeff α (fi i) =
      if h : ∃ j, M ≤ α j then (if h.choose = i then coeff α f else 0) else 0 :=
    fun i α => rfl
  have hsum : f = ∑ i, fi i := by
    ext α
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [hcoeff]
    by_cases h : ∃ j, M ≤ α j
    · simp only [dif_pos h]
      rw [Finset.sum_ite_eq]
      simp
    · simp only [dif_neg h, Finset.sum_const_zero]
      apply hf
      push_neg at h
      rw [Finsupp.degree_eq_sum]
      calc ∑ i, α i ≤ ∑ _i : σ, M := Finset.sum_le_sum fun i _ => (h i).le
        _ = Fintype.card σ * M := by simp
        _ < Fintype.card σ * M + 1 := Nat.lt_succ_self _
  have hdvd : ∀ i, (X i : MvPowerSeries σ k) ^ M ∣ fi i := by
    intro i
    rw [MvPowerSeries.X_pow_dvd_iff]
    intro α hα
    rw [hcoeff]
    split_ifs with h h'
    · exact absurd (h'.symm ▸ h.choose_spec) (not_le.mpr hα)
    · rfl
    · rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsum, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  obtain ⟨g, hg⟩ := hdvd i
  rw [hg, map_mul, map_pow, hM i, zero_mul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndomorphismCharacterActionConjugate
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndomorphismCharacterActionConjugate
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc

theorem endChar_act : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (a : 𝓞 E), EndChar P.U (t.act.act a) (DistribSMul.toAddMonoidHom P.D.toPre.X (H.bar a)) := by
  intro E _ _ _ H R _ _ _ _ t P a κ _ ρ hρ G₀ _ φ h f₀ hf
  letI := H.starRing
  obtain ⟨τ, hτ, hi⟩ := P.lin.i_lin 0 a
  have e : τ = GlobalTheory.SplitTorus.torusMap _ (DistribSMul.toAddMonoidHom P.D.toPre.X (H.bar a)) :=
    (GlobalTheory.SplitTorus.eq_torusMap_iff _ _).2 fun x =>
      (GlobalTheory.SplitTorus.res_pullU_charUnit τ x _).symm.trans
        ((congrArg Units.val (hτ x)).trans (GlobalTheory.SplitTorus.charUnit_val _))
  have k := GlobalTheory.TorusPart.isGrpPullback_thickLift hρ h
  have c : f₀.left ≫ GlobalTheory.TorusPart.thickLift hρ h =
      GlobalTheory.TorusPart.thickLift hρ h ≫
        ((Over.pullback (Out.thick R (maximalIdeal R) 0)).map (t.act.act a)).left := by
    apply pullback.hom_ext
    · refine (Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) (GlobalTheory.TorusPart.thickLift_fst _ _)).trans (hf.trans ?_))
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      refine Eq.trans ?_ (congrArg (_ ≫ ·) (GlobalTheory.ExtUnique.pullback_map_left_fst _ _).symm)
      exact (congrArg (· ≫ _) (GlobalTheory.TorusPart.thickLift_fst _ _).symm).trans (Category.assoc _ _ _)
    · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) k.1.w).trans ?_)
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      refine Eq.trans ?_ (congrArg (_ ≫ ·)
        (Over.w ((Over.pullback (Out.thick R (maximalIdeal R) 0)).map (t.act.act a))).symm)
      refine Eq.trans ?_ k.1.w.symm
      rw [← Category.assoc, Over.w]
  exact (GlobalTheory.TorusPart.pullTorus_comp k k _ _ c (P.U.gt 0).i).symm.trans
    ((congrArg (GlobalTheory.TorusPart.pullTorus k) (hi.trans (congrArg (· ≫ _) e))).trans
      (GlobalTheory.TorusPart.pullTorus_torusMap_comp k _ _))

end GlobalTheory.UPoinc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndomorphismCharacterActionConjugateStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.endomorphism_characterAction_conjugate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (a : 𝓞 E), EndChar P.U (t.act.act a) (DistribSMul.toAddMonoidHom P.D.toPre.X (H.bar a)) := by
  first | exact @GlobalTheory.UPoinc.endChar_act | exact GlobalTheory.UPoinc.endChar_act | (intros; apply GlobalTheory.UPoinc.endChar_act <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointExtendsOverNormalDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointExtendsOverNormalDomain
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH
open GlobalTheory.Poinc.Tors

noncomputable section

namespace GlobalTheory.Poinc.Tors

theorem torsion_extend : Laws → ∀ (R : Type) [CommRing R] [IsDomain R], IsNoetherianRing R → IsIntegrallyClosed R → ∀ (P : PolAV (Spec (CommRingCat.of R))) (N : ℕ), 1 ≤ N → ∀ x : TF (R := R) (FractionRing R) ⟶ P.A, x ^ N = 1 → ∃ b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ P.A, b ^ N = 1 ∧ x = toUnit _ ≫ b := by
  intro hL R _ _ hR hIC P N hN x hx
  have hfin : IsFinite (mulA P.A N).left := (hL.mulN _ P N hN).1
  have hj : jFK (R := R) (FractionRing R) = 𝟙 _ := by
    simp [jFK]
  have hTF : (TF (R := R) (FractionRing R)).hom = jK R := by
    simp [TF, hj]
  have e1 : x ≫ mulA P.A N = toUnit _ ≫ η[P.A] := by
    rw [mulA, MonObj.comp_pow, Category.comp_id, hx]; rfl
  have h : x.left ≫ (mulA P.A N).left = jK R ≫ η[P.A].left := by
    have := congrArg CommaMorphism.left e1
    simp only [Over.comp_left] at this
    rw [this]
    congr 1
  obtain ⟨l, hl1, hl2⟩ := GlobalTheory.FiniteLift.exists_lift (mulA P.A N).left η[P.A].left x.left h
  have hl3 : l ≫ P.A.hom = 𝟙 _ := by
    rw [← Over.w (mulA P.A N), ← Category.assoc, hl1, Over.w η[P.A]]
    simp
  let b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ P.A := Over.homMk l (by simpa using hl3)
  refine ⟨b, ?_, ?_⟩
  · have e2 : b ^ N = b ≫ mulA P.A N := by rw [mulA, MonObj.comp_pow, Category.comp_id]
    rw [e2]
    ext1
    simp only [Over.comp_left, b, Over.homMk_left, hl1]
    show _ = (toUnit _ ≫ η[P.A]).left
    rw [toUnit_unit, Category.id_comp]
  · ext1
    simp only [Over.comp_left, b, Over.homMk_left]
    have w := Over.w (toUnit (TF (R := R) (FractionRing R)))
    have w' : (toUnit (TF (R := R) (FractionRing R))).left = jK R := by
      rw [← hTF, ← w]
      first | rfl | simp | (erw [Category.comp_id])
    rw [w', hl2]

end GlobalTheory.Poinc.Tors
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointExtendsOverNormalDomainStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH
open GlobalTheory.Poinc.Tors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionPoint_extends_over_normal_domain : Laws → ∀ (R : Type) [CommRing R] [IsDomain R], IsNoetherianRing R → IsIntegrallyClosed R → ∀ (P : PolAV (Spec (CommRingCat.of R))) (N : ℕ), 1 ≤ N → ∀ x : TF (R := R) (FractionRing R) ⟶ P.A, x ^ N = 1 → ∃ b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ P.A, b ^ N = 1 ∧ x = toUnit _ ≫ b := by
  first | exact @GlobalTheory.Poinc.Tors.torsion_extend | exact GlobalTheory.Poinc.Tors.torsion_extend | (intros; apply GlobalTheory.Poinc.Tors.torsion_extend <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorActionCompatibleWithDegeneration
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorActionCompatibleWithDegeneration
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

def precompHom {C : Type*} [Category C] [CartesianMonoidalCategory C] {M X Y : C} [MonObj M] (f : X ⟶ Y) :
    (Y ⟶ M) →* (X ⟶ M) where
  toFun g := f ≫ g
  map_one' := MonObj.comp_one f
  map_mul' g₁ g₂ := MonObj.comp_mul f g₁ g₂

def degCHom {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) :
    D.X →+ Additive (𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) where
  toFun x := Additive.ofMul (D.c x)
  map_zero' := by
    have h : D.c (0 + 0) = D.c 0 * D.c 0 := D.c_add 0 0
    rw [add_zero] at h
    have h1 : D.c 0 = 1 := by simpa using h.symm
    rw [h1]; rfl
  map_add' x y := by rw [D.c_add]; rfl

theorem degC_sum_zsmul {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {r : ℕ} (n : Fin r → ℤ) (x : Fin r → D.X) :
    D.c (∑ j, n j • x j) = ∏ j, D.c (x j) ^ n j := by
  have h := congrArg Additive.toMul (map_sum (degCHom D) (fun j => n j • x j) Finset.univ)
  rw [toMul_sum] at h
  refine h.trans ?_
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [map_zsmul, toMul_zsmul]
  rfl

theorem Tens.c_smul : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (T : Tens D D' W) (s : SymUnit r), letI := T.mod s; ∀ (a : TensO s) (y : D'.X),
    D'.c (a • y) = D'.c y ≫ T.act (TensO.mat s a) := by
  intro R _ _ D D' r W T s
  letI := T.mod s
  intro a y
  refine Fan.IsLimit.hom_ext T.lim _ _ fun i => ?_
  show D'.c (a • y) ≫ T.pr i = (D'.c y ≫ T.act (TensO.mat s a)) ≫ T.pr i
  rw [T.c_pr, Category.assoc, T.act_pr, Tens.xe_smul, degC_sum_zsmul D]
  have h := map_prod (precompHom (M := D.P.A) (D'.c y)) (fun j => T.pr j ^ TensO.mat s a i j) Finset.univ
  refine Eq.trans ?_ h.symm
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [map_zpow]
  show _ = (D'.c y ≫ T.pr j) ^ _
  rw [T.c_pr]

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorActionCompatibleWithDegenerationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_action_compatible_with_degeneration : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) (s : SymUnit r), letI := T.mod s; ∀ (a : TensO s) (y : D'.X), D'.c (a • y) = D'.c y ≫ T.act (TensO.mat s a) := by
  first | exact @GlobalTheory.Mum.Tens.c_smul | exact GlobalTheory.Mum.Tens.c_smul | (intros; apply GlobalTheory.Mum.Tens.c_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TauCoordMulSq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open MonObj
open Classical

noncomputable section

namespace GlobalTheory.PsiFromTauEven

open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues

theorem tauCoord_mul_sq (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] (D : DegPre A) (hB : D.TauBimult)
    (hE : D.PsiEven) (y : D.X) (r : A) (hr : PsiCoord D y r) (x : (FractionRing A)ˣ) (hx : IsTauCoord D y (-y) x) :
    ∃ w : Aˣ, (x : FractionRing A) * algebraMap A (FractionRing A) r ^ 2 = algebraMap A (FractionRing A) w := by
  obtain ⟨x₀, hx₀, e₀⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff D y r).1 hr
  have h0 : IsPsiCoord D (y + -y) (psiCoord D 0) := by rw [add_neg_cancel]; exact psiCoord_spec D 0
  obtain ⟨u₂, hu₂⟩ := GlobalTheory.T.tauCoordinate_eq_unit_mul_psi_quotient A D y (-y) x _ _ _ hx h0 hx₀ (psiCoord_spec D (-y))
  obtain ⟨u₃, hu₃⟩ := GlobalTheory.T.psiEven_coordinates_neg_differ_by_unit A D hE y _ _ hx₀ (psiCoord_spec D (-y))
  obtain ⟨u₄, hu₄⟩ := GlobalTheory.MonoTriv.psiCoord_zero D hB _ (psiCoord_spec D 0)
  refine ⟨u₂ * u₄ * u₃⁻¹, ?_⟩
  have hne : (x₀ : FractionRing A) ≠ 0 := x₀.ne_zero
  have h3 : algebraMap A (FractionRing A) (u₃ : A) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).2 u₃.ne_zero
  rw [hu₂, hu₃, hu₄, ← e₀]
  simp only [Units.val_mul, map_mul, map_units_inv]
  field_simp

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsDiscreteValuationRing V → ∀ (g : R →+* V) (gK : FractionRing R →+* FractionRing V), (∀ r, gK (algebraMap R _ r) = algebraMap V _ (g r)) →
  ∀ (D : DegPre R) (D' : DegPre V), D.TauBimult → D.PsiEven → D'.TauBimult → D'.PsiEven → ∀ ρ : D.X →+ D'.X,
    (∀ (a b : D.X) (x : (FractionRing R)ˣ) (x' : (FractionRing V)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D a b x → GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D' (ρ a) (ρ b) x' →
      ∃ u : Vˣ, gK (x : FractionRing R) = algebraMap V (FractionRing V) (u : V) * (x' : FractionRing V)) →
    ∀ (y : D.X) (r : R) (r' : V), PsiCoord D y r → PsiCoord D' (ρ y) r' → Associated (g r) r' := by
  intro R _ _ _ V _ _ _ hV g gK hgK D D' hB hE hB' hE' ρ hρ y r r' hr hr'
  obtain ⟨x, hx⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D y (-y)
  obtain ⟨x', hx'⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord V D' (ρ y) (-(ρ y))
  obtain ⟨w, hw⟩ := tauCoord_mul_sq R D hB hE y r hr x hx
  obtain ⟨w', hw'⟩ := tauCoord_mul_sq V D' hB' hE' (ρ y) r' hr' x' hx'
  have hx'' : IsTauCoord D' (ρ y) (ρ (-y)) x' := by rwa [map_neg]
  obtain ⟨u, hu⟩ := hρ y (-y) x x' hx hx''
  have e := congrArg gK hw
  rw [map_mul, map_pow, hgK, hgK, hu] at e
  let v : Vˣ := u * w' * (Units.map g.toMonoidHom w)⁻¹
  have key : (g r) ^ 2 * (v : V) = r' ^ 2 := by
    have k1 : ((u : V) * w') * (g r) ^ 2 = g w * r' ^ 2 := by
      apply IsFractionRing.injective V (FractionRing V)
      simp only [map_mul, map_pow]
      rw [← hw', ← e]; ring
    have hw1 : (g w : V) * ((Units.map g.toMonoidHom w)⁻¹ : Vˣ) = 1 := by
      have h : ((Units.map g.toMonoidHom w : Vˣ) : V) = g w := rfl
      rw [← h, Units.mul_inv]
    simp only [v, Units.val_mul]
    calc g r ^ 2 * (↑u * ↑w' * ↑(Units.map g.toMonoidHom w)⁻¹)
        = (↑u * ↑w') * g r ^ 2 * ↑(Units.map g.toMonoidHom w)⁻¹ := by ring
      _ = r' ^ 2 * ((g w : V) * ((Units.map g.toMonoidHom w)⁻¹ : Vˣ)) := by rw [k1]; ring
      _ = r' ^ 2 := by rw [hw1, _root_.mul_one]
  have hsq : Associated ((g r) ^ 2) (r' ^ 2) := ⟨v, key⟩
  haveI : IsIntegrallyClosed V := inferInstance
  exact associated_of_dvd_dvd ((IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).1 hsq.dvd)
    ((IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).1 hsq.symm.dvd)

end GlobalTheory.PsiFromTauEven
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionSpecialOfLocal
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Published
open scoped CategoryTheory.Obj
open MonObj
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorusFibre

open GlobalTheory.SplitTorus (torusMap bcIso)

theorem isClosedImmersion_special_of_local : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (K : Type) [Field K] [Algebra R K]
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G], IsSemiAbelian G →
    ∀ (r : ℕ) (u : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.torus R r ⟶ G), IsMonHom u →
    Mono ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R K).map u) →
    IsClosedImmersion ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R (IsLocalRing.ResidueField R)).map u).left := by
  intro R _ _ _ K _ _ G _ hG r u hu hmono
  let k := IsLocalRing.ResidueField R
  let Ω := AlgebraicClosure k
  refine GlobalTheory.T.closedImmersion_of_baseChange_field_ext R k Ω (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.torus R r) G u ?_
  let p : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R Ω))
  obtain ⟨E⟩ := hG.fibres Ω p
  let v := (bcIso p (Fin r → ℤ)).hom ≫ (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map u
  have hv : IsClosedImmersion v.left := by
    refine GlobalTheory.T.isClosedImmersion_splitTorus_into_torusExtension Ω _ E r v inferInstance fun q hq φ hφ h => hφ ?_
    have hsep : IsSeparated G.hom := hG.separated
    have e1 : torusMap _ φ ≫ (bcIso p (Fin r → ℤ)).hom =
        (bcIso p (ZMod q)).hom ≫ (Over.pullback p).map (torusMap _ φ) :=
      (GlobalTheory.SplitTorus.comm_bcMap_iff p _ _).1 (GlobalTheory.SplitTorus.torusMap_bcMap p φ)

    have hΩ : (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map (torusMap _ φ ≫ u) =
        (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map 1 := by
      rw [Functor.map_comp, Functor.map_one, ← cancel_epi (bcIso p (ZMod q)).hom, MonObj.comp_one,
        ← Category.assoc]
      change ((bcIso p (ZMod q)).hom ≫ (Over.pullback p).map (torusMap _ φ)) ≫ _ = _
      rw [← e1, Category.assoc]
      exact h

    have hk := GlobalTheory.T.overSpecBaseChange_map_eq_of_fieldExtension R k Ω _ _ _ _ hΩ
    have hf : torusMap _ φ ≫ u = 1 :=
      GlobalTheory.T.splitTorus_hom_ext_of_eq_mod_maximalIdeal_pow R (ZMod q) G hsep _ _ (GlobalTheory.T.splitTorus_hom_pullback_quotient_pow_eq_one R (ZMod q) G _ inferInstance hk)

    let pK : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) :=
      Spec.map (CommRingCat.ofHom (algebraMap R K))
    have hK' : (Over.pullback pK).map (torusMap _ φ) = (Over.pullback pK).map (torusMap _ 0) := by
      rw [← cancel_mono ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R K).map u)]
      change (Over.pullback pK).map (torusMap _ φ) ≫ (Over.pullback pK).map u =
        (Over.pullback pK).map (torusMap _ 0) ≫ (Over.pullback pK).map u
      rw [← Functor.map_comp, ← Functor.map_comp, hf, GlobalTheory.SplitTorus.torusMap_zero, MonObj.one_comp]
    rw [GlobalTheory.SplitTorus.pullback_map_torusMap, GlobalTheory.SplitTorus.pullback_map_torusMap,
      cancel_epi, cancel_mono] at hK'
    exact GlobalTheory.SplitTorus.torusMap_injective hK'
  have : (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map u = (bcIso p (Fin r → ℤ)).inv ≫ v := by
    simp [v]
  rw [this, Over.comp_left]
  haveI : IsIso (bcIso p (Fin r → ℤ)).inv.left :=
    inferInstanceAs (IsIso ((Over.forget _).map (bcIso p (Fin r → ℤ)).inv))
  exact IsClosedImmersion.comp _ _

end GlobalTheory.TorusFibre
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegOfValWOpen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.PullDegCancelTop

open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem exists_psiOn_pull {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') :
    ∃ ψ : PsiOn D' (specOf φ ⁻¹ᵁ hD.W), ∀ (x : D'.X) (Z : Scheme.{0}) (r : Z ⟶ (specOf φ ⁻¹ᵁ hD.W).toScheme) (z : Z) J J',
      Good D.P.L z J → Good D'.P.L z J' →
      val (hD.psiW.psi (hD.xe x)) (r ≫ (specOf φ ∣_ hD.W)) z J =
        (om hD.w z J J' (r ≫ (specOf φ ⁻¹ᵁ hD.W).ι ≫ (D'.c x).left))⁻¹ * val (ψ.psi x) r z J' := by
  have hm : (specOf φ ∣_ hD.W) ≫ hD.W.ι = (specOf φ ⁻¹ᵁ hD.W).ι ≫ specOf φ := morphismRestrict_ι _ _
  have key : ∀ x : D'.X, ∃ a : LB.Gen (LB.LinComb D'.P.L (K := PUnit)
      (fun _ => (toUnit (TW (specOf φ ⁻¹ᵁ hD.W)) ≫ D'.c x).left) (fun _ => -1)), a.IsGen ∧
      LB.Gen.Corr D'.P.L _ _ _ _ (LB.pullGen D'.P.L _ _ a (jK R' ∣_ (specOf φ ⁻¹ᵁ hD.W)))
        (LB.pullGen D'.P.L _ _ (D'.psi x) (jK R' ⁻¹ᵁ (specOf φ ⁻¹ᵁ hD.W)).ι) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (specOf φ ⁻¹ᵁ hD.W).toScheme) (z : Z) J J',
      Good D.P.L z J → Good D'.P.L z J' →
      val (hD.psiW.psi (hD.xe x)) (r ≫ (specOf φ ∣_ hD.W)) z J =
        (om hD.w z J J' (r ≫ (specOf φ ⁻¹ᵁ hD.W).ι ≫ (D'.c x).left))⁻¹ * val a r z J' := by
    intro x
    have hψ : (toUnit (TW (specOf φ ⁻¹ᵁ hD.W)) ≫ D'.c x).left ≫ proj hD =
        (specOf φ ∣_ hD.W) ≫ (toUnit (TW hD.W) ≫ D.c (hD.xe x)).left := by
      show (specOf φ ⁻¹ᵁ hD.W).ι ≫ (D'.c x).left ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) =
        (specOf φ ∣_ hD.W) ≫ hD.W.ι ≫ (D.c (hD.xe x)).left
      rw [hD.c_pr x, ← Category.assoc, ← Category.assoc, hm]
    obtain ⟨a, ha, H⟩ := DegPull.exists_pmaps ((isGen_iff _).1 hD.w_gen) D.P.isLB D'.P.isLB (K := PUnit)
      (ε := fun _ => -1) (specOf φ ∣_ hD.W) (fun _ => hψ) (hD.psiW.psi (hD.xe x)) (hD.psiW.psi_gen _)
    refine ⟨a, ha, corr_of_val D'.P.isLB fun y J' hJ' => ?_, fun Z r z J J' hJ hJ' => ?_⟩
    swap
    · have v := DegPull.pmaps_val (fun _ => hψ) H r z hJ hJ'
      rw [Fintype.prod_unique, zpow_neg_one] at v
      exact v
    obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
    have hz : ((jK R' ∣_ (specOf φ ⁻¹ᵁ hD.W)) ≫ (specOf φ ∣_ hD.W)) ≫ hD.W.ι =
        (jK R' ⁻¹ᵁ (specOf φ ⁻¹ᵁ hD.W)).ι ≫ jK R' ≫ specOf φ := by
      rw [Category.assoc, hm, ← Category.assoc, morphismRestrict_ι, Category.assoc]
    obtain ⟨hp, P⟩ := ArcSpecialise.pmaps_psiOn hD hD.psiW _ _ hz x
    have v₁ := DegPull.pmaps_val (fun _ => hψ) H (jK R' ∣_ (specOf φ ⁻¹ᵁ hD.W)) y hJ hJ'
    have v₂ := DegPull.pmaps_val (fun _ => hp) P (𝟙 _) y hJ hJ'
    rw [val_pull hJ', val_pull hJ']
    rw [val_pull hJ, val_pull hJ'] at v₂
    simp only [Category.id_comp] at v₁ v₂ ⊢
    have hmor : (jK R' ∣_ (specOf φ ⁻¹ᵁ hD.W)) ≫ (toUnit (TW (specOf φ ⁻¹ᵁ hD.W)) ≫ D'.c x).left =
        (jK R' ⁻¹ᵁ (specOf φ ⁻¹ᵁ hD.W)).ι ≫ D'.xK x := by
      show (jK R' ∣_ (specOf φ ⁻¹ᵁ hD.W)) ≫ (specOf φ ⁻¹ᵁ hD.W).ι ≫ (D'.c x).left =
        (jK R' ⁻¹ᵁ (specOf φ ⁻¹ᵁ hD.W)).ι ≫ jK R' ≫ (D'.c x).left
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
    rw [hmor] at v₁
    exact mul_left_cancel (v₁.symm.trans v₂)
  choose a ha hc hv using key
  exact ⟨⟨a, ha, hc⟩, hv⟩

end GlobalTheory.PullDegCancelTop

namespace GlobalTheory.Mum

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumDoubledTargetSiegelRule
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumDoubledTargetSiegelRule
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

theorem GlobalTheory.WeilSchrodinger.DblTargetF.siegelRule_dblTarget : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.ResEtaF χS nS →
      ∀ (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : Darboux (symp (cA σ) ξ (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB)) κ),
        (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ → F,
          co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
        ∀ ωd : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
            Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS (nT + nT) → ℂ),
          Formalism.IndefR.DatumF.IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
            (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
        ∀ omp : UG (cA σ) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) × UG (cA σ) (incM F JB) →*
            Module.End ℂ ((κ → AF F) → ℂ),
          GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ωd omp →
          SiegelRule (cA σ) (adeleClass F) B.ψ ξ (incM F JB) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ)
            (GlobalTheory.WeilSchrodinger.transD (cA σ) co) χS
            ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id)
            (omp.comp (MonoidHom.inl _ _)) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ χS hχS rχS JB ξ hξ κ _ co hco ωd hωd omp htr
  intro l hl hinv p t hpt φ hφ
  obtain ⟨ν, 𝓕, hν, h𝓕⟩ := GlobalTheory.TowerFD.exists_fd_any F E nS nT
  obtain ⟨c, hc⟩ := GlobalTheory.T.diagonalLagrangian_invariantForm_unique F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ JB ξ hξ κ co hco ν 𝓕 hν h𝓕 l hl hinv
  obtain ⟨hmem, hrule⟩ := GlobalTheory.T.siegelWeil_section_law_diagonalLagrangian F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ JB ξ hξ κ co hco ν 𝓕 hν h𝓕 χS hχS rχS
    ωd hωd omp htr p t hpt φ hφ
  show l (omp (p, 1) φ) = _
  rw [hc _ hmem, hrule, hc _ hφ]
  ring

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumDoubledTargetSiegelRuleStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.weilDatum_doubledTarget_siegelRule : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.ResEtaF χS nS →
      ∀ (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : Darboux (symp (cA σ) ξ (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB)) κ),
        (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ → F,
          co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
        ∀ ωd : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
            Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS (nT + nT) → ℂ),
          Formalism.IndefR.DatumF.IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
            (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
        ∀ omp : UG (cA σ) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) × UG (cA σ) (incM F JB) →*
            Module.End ℂ ((κ → AF F) → ℂ),
          GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ωd omp →
          SiegelRule (cA σ) (adeleClass F) B.ψ ξ (incM F JB) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ)
            (GlobalTheory.WeilSchrodinger.transD (cA σ) co) χS
            ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id)
            (omp.comp (MonoidHom.inl _ _)) := by
  first | exact @GlobalTheory.WeilSchrodinger.DblTargetF.siegelRule_dblTarget | exact GlobalTheory.WeilSchrodinger.DblTargetF.siegelRule_dblTarget | (intros; apply GlobalTheory.WeilSchrodinger.DblTargetF.siegelRule_dblTarget <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegId
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.PullDegUniqAny

open GlobalTheory.ArcPull GlobalTheory.ArcQ GlobalTheory.PullDegUniq
open GlobalTheory.PsiEvenPull (proj)

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem nonempty_isPullDeg_id {φ : R →+* R'} {D : DegPre R} {D₁ D₂ : DegPre R'} (h₁ : IsPullDeg φ D D₁)
    (h₂ : IsPullDeg φ D D₂) : Nonempty (IsPullDeg (RingHom.id R') D₁ D₂) := by
  have hβ : Function.Injective (RingHom.id R') := Function.injective_id
  have h : IsPullDeg ((RingHom.id R').comp φ) D D₂ := (RingHom.id_comp φ).symm ▸ h₂
  have p₁ : IsGrpPullback D₁.P.A D.P.A (spMap φ) (proj h₁) := pull_grp h₁
  have sc : spMap (RingHom.id R') ≫ spMap φ = spMap ((RingHom.id R').comp φ) := (spMap_comp φ _).symm
  have p : IsGrpPullback D₂.P.A D.P.A (spMap (RingHom.id R') ≫ spMap φ) (proj h) := (pull_grp h).congr sc.symm rfl
  obtain ⟨Φ, e₁, e₂⟩ : ∃ Φ : D₂.P.A.left ⟶ D₁.P.A.left, Φ ≫ proj h₁ = proj h ∧
      Φ ≫ D₁.P.A.hom = D₂.P.A.hom ≫ spMap (RingHom.id R') :=
    ⟨p₁.1.lift (proj h) (D₂.P.A.hom ≫ spMap (RingHom.id R')) (p.1.w.trans (Category.assoc _ _ _).symm),
      p₁.1.lift_fst _ _ _, p₁.1.lift_snd _ _ _⟩
  have gp : IsGrpPullback D₂.P.A D₁.P.A (spMap (RingHom.id R')) Φ :=
    IsGrpPullback.cancel p₁ (p.congr rfl e₁.symm) e₂
  obtain ⟨w, hw, hr, T⟩ := FieldPull.exists_cancel_of_eq e₁ D.P.isLB D₁.P.isLB D₂.P.isLB h₁.w h.w
    ((isGen_iff _).1 h₁.w_gen) ((isGen_iff _).1 h.w_gen) sc (cubeMapOf gp).e_comm (FieldPull.pmaps_rig h₁)
    (FieldPull.pmaps_rig h)
  let xe : D₂.X ≃+ D₁.X := h.xe.trans h₁.xe.symm
  have hxe : ∀ x, h₁.xe (xe x) = h.xe x := fun x => h₁.xe.apply_symm_apply _
  have hc : ∀ x, (D₂.c x).left ≫ Φ = spMap (RingHom.id R') ≫ (D₁.c (xe x)).left := fun x => by
    apply p₁.1.hom_ext
    · rw [Category.assoc, e₁, Category.assoc, h₁.c_pr, hxe]
      exact (h.c_pr x).trans ((congrArg (· ≫ _) sc.symm).trans (Category.assoc _ _ _))
    · rw [Category.assoc, e₂, ← Category.assoc, Over.w, Category.assoc, Over.w]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨ψW⟩ := nonempty_psiOn_pull h₁
  obtain ⟨s, hs⟩ := exists_generic_section h₁
  obtain ⟨hD, -⟩ := DvrDeg.exists_isPullDeg_of_val hβ D₁ D₂ ψW s hs gp w hw hr xe hc (fun x z J₁ J hJ₁ hJ => by
    obtain ⟨J₀, hJ₀⟩ := DegPull.exists_good' D.P.isLB z
    have sβ : jK R' ≫ spMap (RingHom.id R') = genMap hβ ≫ jK R' :=
      (Category.id_comp _).symm.trans (fracMap_sq hβ)
    have v := PsiEvenPull.psi_pull h x (𝟙 _) z hJ₀ hJ
    have v₁ := PsiEvenPull.psi_pull h₁ (xe x) (genMap hβ) z hJ₀ hJ₁
    have ag : val (h₁.psiW.psi (h.xe x)) (genMap hβ ≫ h₁.g) z J₀ = val (h.psiW.psi (h.xe x)) (𝟙 _ ≫ h.g) z J₀ :=
      ArcSpecialise.psiOn_agree h₁.psiW h.psiW _ _ _ (by
        rw [Category.assoc, h₁.g_comm, Category.assoc, h.g_comm, Category.id_comp, ← Category.assoc, ← sβ,
          Category.assoc]
        exact congrArg (jK R' ≫ ·) sc) hJ₀
    have hx : D₂.xK x ≫ Φ = genMap hβ ≫ D₁.xK (xe x) := by
      show (jK R' ≫ (D₂.c x).left) ≫ Φ = genMap hβ ≫ jK R' ≫ (D₁.c (xe x)).left
      rw [Category.assoc, hc, ← Category.assoc, sβ, Category.assoc]
    change _ = (om h₁.w z J₀ J₁ (genMap hβ ≫ D₁.xK (xe x)))⁻¹ * _ at v₁
    change _ = (om h.w z J₀ J (𝟙 _ ≫ D₂.xK x))⁻¹ * _ at v
    rw [hxe, ag, v, Category.id_comp, T _ z J₀ J₁ J hJ₀ hJ₁ hJ, hx, mul_inv, _root_.mul_assoc] at v₁
    exact (mul_left_cancel v₁).symm)
  exact ⟨hD⟩

end GlobalTheory.PullDegUniqAny

namespace GlobalTheory.Mum

theorem isPullDeg_unique_any : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D₁ D₂ : DegPre R'), Nonempty (IsPullDeg φ D D₁) → Nonempty (IsPullDeg φ D D₂) → Nonempty (IsPullDeg (RingHom.id R') D₁ D₂) :=
  fun _ _ _ _ _ _ _ _ _ _ ⟨h₁⟩ ⟨h₂⟩ => GlobalTheory.PullDegUniqAny.nonempty_isPullDeg_id h₁ h₂

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulPullOfRigOfSym
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SymMulPull

open GlobalTheory.MulPull

section Base

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem hasGen_theta (hC : GlobalTheory.Published.CubeTheorem) (hA : IsAbelianScheme A) {L : LB A.left} (hL : L.IsLB) :
    HasGen L (thφ A (x3 A)) thε := by
  have := hA.comm
  obtain ⟨t, ht⟩ := hC S A hA L hL _ (x3 A 0) (x3 A 1) (x3 A 2)
  obtain ⟨t', ht', -⟩ := exists_gen hL (φ' := thφ A (x3 A)) (ε' := thε) (fun U _ h => by
    have e := prod_cub (x3 A 0) (x3 A 1) (x3 A 2) h
    have i : lift (x3 A 0) (lift (x3 A 1) (x3 A 2)) = 𝟙 _ := by ext <;> simp [x3]
    rw [i] at e
    simp only [Over.id_left, Category.id_comp] at e
    rw [e, Fin.prod_univ_eight]
    simp only [Matrix.cons_val, zpow_one, zpow_neg]) t ht
  exact ⟨t', ht'⟩

end Base

end GlobalTheory.SymMulPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPushoutFaithfullyFlat
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_pushout_faithfullyFlat : ∀ (R : Type) [CommRing R] (D D' E : Type) [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] [CommRing E] [Algebra R E] (ψ : D →ₐ[R] D') (φ : D →ₐ[R] E), (ψ : D →+* D').FaithfullyFlat → ∃ (E' : Type) (_ : CommRing E') (_ : Algebra R E') (ψ' : E →ₐ[R] E') (φ' : D' →ₐ[R] E'), (ψ' : E →+* E').FaithfullyFlat ∧ ψ'.comp φ = φ'.comp ψ := by
  intro R _ D D' E _ _ _ _ _ _ ψ φ hψ
  letI : Algebra D E := φ.toRingHom.toAlgebra
  letI : Algebra D D' := ψ.toRingHom.toAlgebra
  haveI : Module.FaithfullyFlat D D' := hψ
  let f : E →+* TensorProduct D E D' := Algebra.TensorProduct.includeLeftRingHom
  let g : D' →+* TensorProduct D E D' := (Algebra.TensorProduct.includeRight : D' →ₐ[D] _).toRingHom
  have hfg : f.comp (algebraMap D E) = g.comp (algebraMap D D') :=
    RingHom.ext fun d => by
      change (algebraMap D E d) ⊗ₜ[D] (1 : D') = (1 : E) ⊗ₜ[D] algebraMap D D' d
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  letI iR : Algebra R (TensorProduct D E D') := (f.comp (algebraMap R E)).toAlgebra
  have hf : f.FaithfullyFlat := by
    have : Module.FaithfullyFlat E (TensorProduct D E D') := inferInstance
    exact (RingHom.faithfullyFlat_algebraMap_iff).2 this
  refine ⟨TensorProduct D E D', inferInstance, iR,
    { f with commutes' := fun r => rfl },
    { g with commutes' := fun r => ?_ }, hf, ?_⟩
  · change g (algebraMap R D' r) = f (algebraMap R E r)
    rw [← ψ.commutes r, ← φ.commutes r]
    exact (congrArg (fun h => h (algebraMap R D r)) hfg).symm
  · ext d
    exact congrArg (fun h => h d) hfg

end GlobalTheory
end
