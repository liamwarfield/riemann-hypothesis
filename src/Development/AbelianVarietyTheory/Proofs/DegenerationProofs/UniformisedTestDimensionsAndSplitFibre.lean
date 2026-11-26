module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecOfLeChart
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsLocalModelOfIntegral
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UtestGeomNonempty
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsInvertibleAdaptedBasisLinkMatrix
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeometricTestMapClassicalPoint
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyClosureExtensionAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAutomorphismPermutationMaxOrderMembers

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedTestDimensionsAndSplitFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedTestDimensionsAndSplitFibre
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

theorem exists_isGt_specialFibre (hB : GtBaseChangeSt) {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V]
    (D : DegPre V) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (g : GtCoord (IsLocalRing.maximalIdeal V) D 0 G) :
    ∃ E : SplitExt (Sp (IsLocalRing.ResidueField V)),
      E.IsGt ((Over.pullback (spMap (IsLocalRing.residue V))).obj G) := by
  obtain ⟨E₀, -, -, -, -, hE⟩ := GlobalTheory.gtCoord_isGt V (IsLocalRing.maximalIdeal V) D 0 G ⟨g⟩
  have hle : IsLocalRing.maximalIdeal V ^ (0 + 1) ≤ RingHom.ker (IsLocalRing.residue V) := by
    rw [zero_add, pow_one, IsLocalRing.ker_residue]
  let c : V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1) →+* IsLocalRing.ResidueField V :=
    Ideal.Quotient.lift _ (IsLocalRing.residue V) fun a ha => (RingHom.mem_ker).1 (hle ha)
  obtain ⟨E₁, -, -, -, -, hE₁⟩ := hB _ _ (spMap c) E₀ _ hE
  have hc : spMap c ≫ thick V (IsLocalRing.maximalIdeal V) 0 = spMap (IsLocalRing.residue V) := by
    rw [show thick V (IsLocalRing.maximalIdeal V) 0 = spMap (Ideal.Quotient.mk _) from rfl, ← spMap_comp]
    congr 1
  have gp := ((isGrpPullback_pullback (thickObj V (IsLocalRing.maximalIdeal V) 0 G) (spMap c)).comp
    (isGrpPullback_pullback G (thick V (IsLocalRing.maximalIdeal V) 0))).congr hc rfl
  obtain ⟨e, he, -⟩ := grpPullback_iso gp (isGrpPullback_pullback G (spMap (IsLocalRing.residue V)))
  exact ⟨E₁, isGt_of_iso e hE₁⟩

theorem utest_dim_and_split : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), u.A.g = S.g ∧ u.D.toPre.P.g + Module.finrank ℤ u.D.toPre.X = S.g ∧ SmoothOfRelativeDimension S.g u.G.hom ∧ 4 ≤ S.N ∧ ∃ E : SplitExt (Sp (IsLocalRing.ResidueField u.V)), E.IsGt ((Over.pullback (spMap (IsLocalRing.residue u.V))).obj u.G) := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u
  have : CharZero u.V :=
    ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V))).charZero
  have hA : AdmBase u.V (IsLocalRing.maximalIdeal u.V) := ⟨inferInstance, inferInstance, inferInstance, u.complete⟩
  have hsm : SmoothOfRelativeDimension S.g u.A.A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback u.cart.1 (ρ.g_eq ▸ ρ.P.smoothDim)
  have hg : u.A.g = S.g :=
    H1.dim_unique u.A.A.hom u.A.smoothDim hsm (eSec u.A.A (IsLocalRing.closedPoint (FractionRing u.V)))
  refine ⟨hg, ?_, ?_, ?_, exists_isGt_specialFibre hL.2.2.1.gtBaseChange _ _ (u.U.gt 0)⟩
  · have h := GlobalTheory.UT.dim_eq_rank_add_dim hL u.V _ hA u.D u.A u.G u.semi u.U
    rw [← hg, add_comm]
    exact h.symm
  · have := u.semi.smooth
    have := u.semi.geomConnected
    refine GlobalTheory.GenericDim.smoothOfRelativeDimension_of_generic u.V u.G S.g ?_
    have w : u.U.gen.hom.left ≫ u.A.A.hom = pullback.snd u.G.hom (jK u.V) := Over.w u.U.gen.hom
    have : IsIso u.U.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map u.U.gen.hom))
    exact (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
      (IsPullback.of_horiz_isIso (g := 𝟙 _) ⟨w.trans (Category.comp_id _).symm⟩) hsm
  · rw [ρ.N_eq]
    have h₁ : 2 ≤ ρ.n ^ ρ.k := ρ.n_prime.two_le.trans (Nat.le_self_pow (by have := ρ.two_le; omega) _)
    exact Nat.pow_le_pow_left h₁ 2

end GlobalTheory.ZH
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedTestDimensionsAndSplitFibreStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
theorem _root_.GlobalTheory.T.uniformisedTest_dimensions_and_split_fibre : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), u.A.g = S.g ∧ u.D.toPre.P.g + Module.finrank ℤ u.D.toPre.X = S.g ∧ SmoothOfRelativeDimension S.g u.G.hom ∧ 4 ≤ S.N ∧ ∃ E : SplitExt (Sp (IsLocalRing.ResidueField u.V)), E.IsGt ((Over.pullback (spMap (IsLocalRing.residue u.V))).obj u.G) := by
  first | exact @GlobalTheory.ZH.utest_dim_and_split | exact GlobalTheory.ZH.utest_dim_and_split | (intros; apply GlobalTheory.ZH.utest_dim_and_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSectionNonzeroFibresLocalRing
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSectionNonzeroFibresLocalRing
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

noncomputable section
namespace GlobalTheory.PsiRing

theorem basis_prod_famφT_zero {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R)))
    (U : Type) [CommGroup U] (h : ((T ⊗ D.P.A).left ⟶ D.P.A.left) → U) :
    ∏ k, h (famφT D T 0 k) ^ DegPre.famε 1 k = h (snd T D.P.A).left := by
  have := D.P.isAb.comm
  rw [PsiExists.famφT_eq, PsiExists.cT_zero, _root_.mul_one]
  simp [Fin.prod_univ_four, DegPre.famε]

theorem exists_basis_fibNZ : SecTwistSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R), ∃ th : SecBT D (𝟙_ _) 1 0, FibNZ (𝟙_ _ ⊗ D.P.A).hom th ∧ ∀ g : SecBT D (𝟙_ _) 1 0, ∃ b : R, Mult D th g b := by
  intro hT R _ _ _ D
  have := D.P.isAb.comm
  let T : Over (Spec (CommRingCat.of R)) := 𝟙_ _
  have e : translPt D.P.A (1 : T ⟶ D.P.A) = snd T D.P.A := by
    show (fst T D.P.A ≫ 1) * snd T D.P.A = _
    rw [MonObj.comp_one, _root_.one_mul]
  obtain ⟨⟨b, hb⟩, -⟩ := hT _ D.P 1 le_rfl R (𝟙 _) (1 : T ⟶ D.P.A)
  change Fin (1 ^ D.P.g) → LB.Sec (twistLB D.P.A D.P.L 1 (1 : T ⟶ D.P.A)) at b
  change IsSecBasis (T := T) (A := D.P.A) _ b at hb
  have : Subsingleton (Fin (1 ^ D.P.g)) := by rw [one_pow]; infer_instance
  let i₀ : Fin (1 ^ D.P.g) := ⟨0, by simp⟩
  have H : FormEq (K := Fin 2) ![(snd T D.P.A).left, (translPt D.P.A (1 : T ⟶ D.P.A)).left] ![((1 : ℕ) : ℤ) - 1, 1]
      (famφT D T 0) (DegPre.famε 1) := fun U _ h => by
    rw [basis_prod_famφT_zero, e]
    simp [Fin.prod_univ_two]
  obtain ⟨th, hth⟩ := exists_sec D.P.isLB H (b i₀)
  have hf : (fst T D.P.A).left = (T ⊗ D.P.A).hom :=
    (Category.comp_id _).symm.trans (Over.w (fst T D.P.A))
  have key : ∀ g : SecBT D T 1 0, ∃ c : R, Mult D th g c := fun g => by
    obtain ⟨s, hs⟩ := exists_sec D.P.isLB (fun U _ h => (H U h).symm) g
    obtain ⟨c, hc, -⟩ := hb s
    have hc' := fun j => (hc j).trans (Fintype.sum_subsingleton _ i₀)
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (c i₀), fun Z r z J hJ => ?_⟩
    refine (hs Z r z J hJ).symm.trans (Eq.trans ?_ (congrArg _ (hth Z r z J hJ).symm))
    refine (congrArg (gs r z _) (hc' _)).trans ((gs_mul r z _ (hJ.mem _ r) _ _).trans (congrArg₂ (· * ·)
        ((gs_res r z le_top (hJ.mem _ r) _).trans ((gs_pull r (fst T D.P.A).left z ⊤ trivial _).trans ?_)) rfl))
    exact congrArg₂ (fun (q : Z ⟶ Spec (CommRingCat.of R)) (a : Γ(Spec (CommRingCat.of R), ⊤)) => gs q z ⊤ a)
      (congrArg (r ≫ ·) hf) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id_apply (c i₀)).symm
  refine ⟨th, fun y => ?_, key⟩
  have hp : IsPullback (snd T D.P.A).left (T ⊗ D.P.A).hom D.P.A.hom (𝟙 _) := by
    rw [← hf]
    exact (IsPullback.of_hasPullback T.hom D.P.A.hom).flip
  obtain ⟨t, ht⟩ := KeyPow.exists_sec_fibre_ne_zero hT D.P hp
  obtain ⟨z, hz, hz'⟩ := ht y
  obtain ⟨g, hg⟩ := exists_sec D.P.isLB (K := PUnit) (φ := fun _ => (snd T D.P.A).left) (ε := fun _ => 1)
    (φ' := famφT D T 0) (ε' := DegPre.famε 1) (fun U _ h => by
      rw [basis_prod_famφT_zero]; simp) t
  obtain ⟨c, hc⟩ := key g
  choose J hJ using fun χ : (T ⊗ D.P.A).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
  refine ⟨z, hz, (MulPullSec.mem_nonzeroLocus_iff th (𝟙 _) z hJ).2 ?_⟩
  have u := (MulPullSec.mem_nonzeroLocus_iff (K := PUnit) (φ := fun _ => (snd T D.P.A).left) (ε := fun _ => 1)
    t (𝟙 _) z hJ).1 hz'
  rw [← hg _ _ z J hJ, hc _ _ z J hJ] at u
  exact isUnit_of_mul_isUnit_right u

end GlobalTheory.PsiRing
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSectionNonzeroFibresLocalRingStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaSection_nonzeroFibres_localRing : SecTwistSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R), ∃ th : SecBT D (𝟙_ _) 1 0, FibNZ (𝟙_ _ ⊗ D.P.A).hom th ∧ ∀ g : SecBT D (𝟙_ _) 1 0, ∃ b : R, Mult D th g b := by
  first | exact @GlobalTheory.PsiRing.exists_basis_fibNZ | exact GlobalTheory.PsiRing.exists_basis_fibNZ | (intros; apply GlobalTheory.PsiRing.exists_basis_fibNZ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationDataOfSemiAbelianSymmetry
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationDataOfSemiAbelianSymmetry
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH

theorem exists_setting_of_hypS : Laws → (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → (∃ E : SplitExt (Sp (IsLocalRing.ResidueField V)), E.IsGt ((Over.pullback (spMap (IsLocalRing.residue V))).obj G)) → HypS A.A A.L → ∀ gen : (Over.pullback (jK V)).obj G ≅ A.A, IsMonHom gen.hom → ∃ s : GlobalTheory.UU.HidaSetting V A G, s.gen = gen := by
  intro laws hext V _ _ hd _ hc A G _ _ hG hE hS gen hgen
  have hV : GlobalTheory.UU.CDVR V := ⟨hd, hc, inferInstance⟩
  obtain ⟨L, hL⟩ := GlobalTheory.UU.polarisation_extends laws V A G hG gen hgen
  obtain ⟨P, rfl⟩ := GlobalTheory.CubicalPackage.exists_package laws V hV A G hG gen hgen L hL
  obtain ⟨w, -, hw, -, -, hiso, -⟩ := GlobalTheory.T.symmetryHyp_extends_semiAbelian_dvr hext V A G hG hS gen hgen P.L hL
  obtain ⟨E, ⟨d⟩⟩ := hE
  have : IsCommMonObj ((Over.pullback (spMap (IsLocalRing.residue V))).obj G) := Functor.isCommMonObj_obj
  obtain ⟨r, hr⟩ := GlobalTheory.UU.thick_zero_factor V
  obtain ⟨Q₀⟩ := GlobalTheory.UU.nonempty_tq_pullback_comp r _ hr G (GlobalTheory.UU.TQ.ofGtDatum d)
  obtain ⟨P₀, h₀⟩ := GlobalTheory.UU.exists_isLevelCP (IsLocalRing.maximalIdeal V) 0 P
  obtain ⟨wA, hwA⟩ := hL
  have := E.free
  have := E.finite
  exact ⟨⟨hV, hG, gen, hgen, P, wA, hwA, E.X, Q₀, P₀, h₀,
    GlobalTheory.T.exists_even_cubical_trivialisation_specialFibre laws V hV A G hG gen hgen P w hw hiso E.X Q₀ P₀ h₀⟩, rfl⟩

end GlobalTheory.ZH
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationDataOfSemiAbelianSymmetryStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformisationData_of_semiAbelianSymmetry : Laws → (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → (∃ E : SplitExt (Sp (IsLocalRing.ResidueField V)), E.IsGt ((Over.pullback (spMap (IsLocalRing.residue V))).obj G)) → HypS A.A A.L → ∀ gen : (Over.pullback (jK V)).obj G ≅ A.A, IsMonHom gen.hom → ∃ s : GlobalTheory.UU.HidaSetting V A G, s.gen = gen := by
  first | exact @GlobalTheory.ZH.exists_setting_of_hypS | exact GlobalTheory.ZH.exists_setting_of_hypS | (intros; apply GlobalTheory.ZH.exists_setting_of_hypS <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymplecticLevelBaseChangePolarisedAbelian
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymplecticLevelBaseChangePolarisedAbelian
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal

namespace GlobalTheory

theorem exists_level_baseChange : Laws → ∀ (S S' : Scheme.{0}) [IsLocallyNoetherian S] [IsLocallyNoetherian S'] (f : S' ⟶ S) (P : PolAV S) (P' : PolAV S') (φ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A f φ → LBIso P'.L (P.L.pull φ) → P'.g = P.g → ∀ (k : ℕ) (ze : Γ(S, ⊤)ˣ) (ze' : Γ(S', ⊤)ˣ), f.appTop.hom ze.val = ze'.val → IsPrimitiveRoot ze' k → ∀ lev : Out.Level P k ze, ∃ lev' : Out.Level P' k ze', ∀ (i : Fin (2 * P.g)) (i' : Fin (2 * P'.g)), (i : ℕ) = i' → (lev'.pt i').left ≫ φ = f ≫ (lev.pt i).left := by
  intro hL S S' _ _ f P P' φ h hiso hg k ze ze' hz hprim lev
  have e : 2 * P'.g = 2 * P.g := congrArg (2 * ·) hg
  have cast : ∀ {n n' : ℕ} (e : n' = n) {T : Over S} (y : Fin n → (T ⟶ P.A)) (a : Fin n' → ℕ),
      linComb (fun i => y (Fin.cast e i)) a = linComb y (fun i => a (Fin.cast e.symm i)) := by
    intro n n' e T y a
    subst e
    rfl
  choose pt hpt using fun i => ThetaObjPull.exists_sec h (lev.pt (Fin.cast e i))
  have hpt' : ∀ i, (pt i).left ≫ φ = f ≫ (lev.pt (Fin.cast e i)).left := fun i =>
    congrArg (fun z => z.left) (hpt i)
  have key : ∀ (K : Type) [Field K] (x : Spec (CommRingCat.of K) ⟶ S') (c : Fin (2 * P'.g) → ℕ),
      pushHom h (Over.mk x) (linComb (fun i =>
        (Over.homMk x (by simp) : Over.mk x ⟶ baseOver S') ≫ pt i) c) =
      linComb (fun i => (Over.homMk (x ≫ f) (by simp) : Over.mk (x ≫ f) ⟶ baseOver S) ≫ lev.pt i)
        (fun i => c (Fin.cast e.symm i)) := fun K _ x c => by
    rw [ThetaObjPull.map_linComb]
    refine Eq.trans ?_ (cast e _ c)
    congr 1
    funext i
    apply Over.OverMorphism.ext
    show (x ≫ (pt i).left) ≫ _ = (x ≫ f) ≫ (lev.pt _).left
    rw [Category.assoc, hpt', Category.assoc]
  have := P.isAb.comm
  refine ⟨{ pt := pt
            prim := hprim
            torsion := fun i => ThetaObjPull.pushHom_injective h _ ?_
            indep := fun K _ _ x c c' hc => ?_
            span := fun K _ _ x y hy => ?_
            pairing := fun i j => ?_ }, fun i i' hi => ?_⟩
  · rw [map_pow, map_one, hpt]
    exact (map_pow (preHom (ThetaObjPull.toBase f)) _ _).symm.trans (by rw [lev.torsion, map_one])
  · have q := lev.indep K (x ≫ f) (fun i => c (Fin.cast e.symm i)) (fun i => c' (Fin.cast e.symm i))
      ((key K x _).symm.trans ((congrArg (pushHom h (Over.mk x)) hc).trans (key K x _)))
    funext i
    exact congrFun q (Fin.cast e i)
  · have hy' : pushHom h (Over.mk x) y ^ k = 1 := by rw [← map_pow, hy, map_one]
    obtain ⟨c, hc⟩ := lev.span K (x ≫ f) (pushHom h (Over.mk x) y) hy'
    exact ⟨fun i => c (Fin.cast e i), ThetaObjPull.pushHom_injective h _ ((key K x _).trans hc)⟩
  · refine (weilIs_grpPullback_of_comm _ _ _ _ f _ _ _ P.isLB P'.isLB h hiso (baseOver S') k (pt i) (pt j)
      (ThetaObjPull.toBase f ≫ lev.pt _) (ThetaObjPull.toBase f ≫ lev.pt _) _ (hpt' i).symm (hpt' j).symm).2 ?_
    have w := CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB (ThetaObjPull.toBase f)
      (lev.pairing (Fin.cast e i) (Fin.cast e j))
    rw [map_zpow] at w
    have e₁ : Units.map (ThetaObjPull.toBase f).left.appTop.hom.toMonoidHom ze = ze' := Units.ext hz
    have e₂ : stdSymp P.g (Fin.cast e i) (Fin.cast e j) = stdSymp P'.g i j := by
      simp only [stdSymp, Fin.val_cast, hg]
    rw [e₁, e₂] at w
    exact w
  · obtain rfl : i = Fin.cast e i' := Fin.ext hi
    exact hpt' i'

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymplecticLevelBaseChangePolarisedAbelianStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symplecticLevel_baseChange_polarisedAbelian : Laws → ∀ (S S' : Scheme.{0}) [IsLocallyNoetherian S] [IsLocallyNoetherian S'] (f : S' ⟶ S) (P : PolAV S) (P' : PolAV S') (φ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A f φ → LBIso P'.L (P.L.pull φ) → P'.g = P.g → ∀ (k : ℕ) (ze : Γ(S, ⊤)ˣ) (ze' : Γ(S', ⊤)ˣ), f.appTop.hom ze.val = ze'.val → IsPrimitiveRoot ze' k → ∀ lev : Out.Level P k ze, ∃ lev' : Out.Level P' k ze', ∀ (i : Fin (2 * P.g)) (i' : Fin (2 * P'.g)), (i : ℕ) = i' → (lev'.pt i').left ≫ φ = f ≫ (lev.pt i).left := by
  first | exact @GlobalTheory.exists_level_baseChange | exact GlobalTheory.exists_level_baseChange | (intros; apply GlobalTheory.exists_level_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LinearIndependentThetaBasisGeometricFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LinearIndependentThetaBasisGeometricFibre
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory.UT GlobalTheory.ZH.ClassWeight

noncomputable section
namespace GlobalTheory.ZH.FibreIndep

open GlobalTheory.VVRank GlobalTheory.UnivBasisMove

theorem linearIndependent_pullM (hS : SecBaseChangeAnySt) {S : Scheme.{0}} (P : PolAV S) (n : ℕ) (hn : 1 ≤ n)
    {T T' : Over S} [IsAffine T.left] [IsAffine T'.left] (p : T'.left) (hp : ∀ q, q = p) (h : T' ⟶ T)
    {J : Type} [Fintype J] (hJ : Fintype.card J = n ^ P.g) (s : J → SecM P.A P.L n T)
    (hs : ∀ x, ∃ c : J → Γ(T.left, ⊤), x = ∑ i, c i • s i) :
    LinearIndependent Γ(T'.left, ⊤) (fun i => pullM P.A P.L n h (s i)) := by
  have hne : Nonempty (⊤ : T'.left.Opens) := ⟨⟨p, trivial⟩⟩
  have hnt : Nontrivial Γ(T'.left, ⊤) := Scheme.component_nontrivial T'.left ⊤
  obtain ⟨V, hV, b, hb⟩ := hS S P n hn (T'.hom p)
  let l : T' ⟶ overRes (T := baseOver S) V := Over.homMk
    (IsOpenImmersion.lift V.ι T'.hom (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨y, rfl⟩
      rw [hp y]
      exact hV)) ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (IsOpenImmersion.lift_fac _ _ _))
  obtain ⟨c, -⟩ := exists_basis P n b hb T' l
  have := Module.Free.of_basis c
  have := Module.Finite.of_basis c
  refine linearIndependent_of_top_le_span_of_card_eq_finrank (fun x _ => ?_)
    (by rw [Module.finrank_eq_card_basis c, Fintype.card_fin, hJ])
  refine Submodule.span_le.2 ?_ (LinkMatrix.mem_span_pullM hS P n hn p hp h x)
  rintro _ ⟨u, rfl⟩
  obtain ⟨a, rfl⟩ := hs u
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Submodule.sum_mem _ fun i _ => by
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem linearIndependent_moved : LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (w : LB.Iso u.A.L (ρ.P.L.pull u.φ)), w.IsGen → ∀ t : S.J → SecA u.A (PadicAlgCl p) S.N, (∀ i, Moved u w (t i) (ρ.s i)) → LinearIndependent Γ((TFK (R := u.V) (PadicAlgCl p)).left, ⊤) (fun i => SecM.ofSec u.A.A (t i)) := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u w hw t ht
  have hN : 1 ≤ S.N := by
    rw [ρ.N_eq]
    exact Nat.one_le_pow _ _ (pow_pos ρ.n_prime.pos _)
  let T := TFK (R := u.V) (PadicAlgCl p)
  let T' : Over (Sp S.R) := Over.mk (T.hom ≫ spMap u.yK)
  have : IsAffine T'.left := inferInstanceAs (IsAffine (Sp (PadicAlgCl p)))
  have : IsAffine (baseOver (Sp S.R)).left := inferInstanceAs (IsAffine (Sp S.R))
  let h₀ : T' ⟶ baseOver (Sp S.R) := Over.homMk (spMap y₀) (base_eq u)
  have li := linearIndependent_pullM hL.2.1.secBaseChangeAny ρ.P S.N hN (T' := T')
    (IsLocalRing.closedPoint (PadicAlgCl p))
    (fun q => Subsingleton.elim (α := PrimeSpectrum (PadicAlgCl p)) _ _) h₀ (J := S.J)
    (by rw [ρ.g_eq]; exact ρ.card) (fun i => SecM.ofSec ρ.P.A (ρ.s i)) (fun x => by
      obtain ⟨c, hc⟩ := (ρ.s_basis (SecM.toSec ρ.P.A x)).exists
      refine ⟨c, Subtype.ext (funext fun j => ?_)⟩
      rw [Submodule.coe_sum, Finset.sum_apply]
      exact hc j)
  obtain ⟨E, hE⟩ := exists_linearEquiv u.cart hw ρ.P.isLB u.A.isLB (S.N : ℤ) T
  have e : ∀ i, E (pullM ρ.P.A ρ.P.L S.N h₀ (SecM.ofSec ρ.P.A (ρ.s i))) = SecM.ofSec u.A.A (t i) := fun i => by
    have r : Rel u.cart (T := T) (T₀ := baseOver (Sp S.R)) (spMap y₀) (base_eq u) w (SecM.ofSec u.A.A (t i))
      (SecM.ofSec ρ.P.A (ρ.s i)) := ht i
    have r' := r.pull (T' := T) (T₀' := T') (𝟙 T.left) (Category.id_comp _) (𝟙 T) h₀ rfl
    rw [pullM_id _ u.A.isLB] at r'
    exact (hE _).unique_down ρ.P.isLB u.A.isLB r'
  have li' := LinearIndependent.map' (R := Γ(T.left, ⊤)) li E.toLinearMap E.ker
  exact (funext e : _ = fun i => SecM.ofSec u.A.A (t i)) ▸ li'

end GlobalTheory.ZH.FibreIndep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LinearIndependentThetaBasisGeometricFibreStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory.UT GlobalTheory.ZH.ClassWeight
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_thetaBasis_geometric_fibre : LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (w : LB.Iso u.A.L (ρ.P.L.pull u.φ)), w.IsGen → ∀ t : S.J → SecA u.A (PadicAlgCl p) S.N, (∀ i, Moved u w (t i) (ρ.s i)) → LinearIndependent Γ((TFK (R := u.V) (PadicAlgCl p)).left, ⊤) (fun i => SecM.ofSec u.A.A (t i)) := by
  first | exact @GlobalTheory.ZH.FibreIndep.linearIndependent_moved | exact GlobalTheory.ZH.FibreIndep.linearIndependent_moved | (intros; apply GlobalTheory.ZH.FibreIndep.linearIndependent_moved <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitGeneratingSectionPullbackField
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitGeneratingSectionPullbackField
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.GenSecField

open GlobalTheory.IndivisibleSection ReciprocityTheory.ChartRestriction.G.DVR

theorem flat_of_injective {R K : Type} [CommRing R] [IsDomain R] [Field K] {φ : R →+* K}
    (hφ : Function.Injective φ) : φ.Flat := by
  have e : φ = (IsFractionRing.lift (A := R) (K := FractionRing R) hφ).comp (algebraMap R (FractionRing R)) :=
    RingHom.ext fun x => (IsFractionRing.lift_algebraMap hφ x).symm
  rw [e]
  refine RingHom.Flat.comp ?_ ?_
  · exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors R))
  · let _ := (IsFractionRing.lift (A := R) (K := FractionRing R) hφ).toAlgebra
    exact (inferInstance : Module.Flat (FractionRing R) K)

variable {X X' : Scheme.{0}} {L : LB X} {L' : LB X'}

theorem exists_pow_one (u : LB.Sec L) : ∃ s : H0 L 1, ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) J, Good L z J →
    sval s r z J = gs r z _ (u.f (J r)) := by
  have le : ∀ j : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => 𝟙 X) j ≤ L.U (j 0) :=
    fun j y hy => Set.mem_iInter.1 hy 0
  refine ⟨⟨fun j => (X.presheaf.map (homOfLE (le j)).op).hom (u.f (j 0)), fun j j' => fn_ext fun y hy => ?_⟩,
    fun Z r z J hJ => ?_⟩
  · refine (gs_res (𝟙 X) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 X) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 X) y _ hy _).trans (congrArg Units.val (gm_linComb L _ _ (𝟙 X) y j j' hy.1 hy.2)))
      (gs_res (𝟙 X) y _ hy _))).symm)
    refine (gs_res (𝟙 X) y (le j) hy.1 _).trans ((FlatSec.gs_sec_trans u (𝟙 X) y (le j hy.1) (le j' hy.2)).trans
      (congrArg₂ (· * ·) (congrArg Units.val ?_) (gs_res (𝟙 X) y (le j') hy.2 _).symm))
    simp
  · rw [sval_of _ r z J (fun _ => J r) (fun _ => by rw [Category.comp_id])]
    exact gs_res r z (le fun _ => J r) (Set.mem_iInter.2 fun _ => hJ r) _

theorem cst_zero' {R : Type} [CommRing R] {Z : Scheme.{0}} (q : Z ⟶ Sp R) (z : Z) : cst q z 0 = 0 := by
  rw [cst, map_zero, gs_eq q z ⊤ trivial, map_zero, map_zero]

theorem sval_eq_zero {R R' : Type} [CommRing R] [CommRing R'] {g : R →+* R'} (hg : g.Flat) [CompactSpace X]
    [QuasiSeparatedSpace X] {f : X ⟶ Sp R} {π : X' ⟶ X} {f' : X' ⟶ Sp R'}
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom g))) (hL : L.IsLB) (hL' : L'.IsLB)
    {w : LB.Iso L' (L.pull π)} (hw : w.IsGen) {th : H0 L 1} (hth : ∀ s : H0 L 1, ∃ a, SecIsMul f a s th)
    (h₀ : ∀ y J, Good L y J → sval th π y J = 0) (s : H0 L' 1) (y : X') {J'} (hJ' : Good L' y J') :
    sval s (𝟙 X') y J' = 0 := by
  obtain ⟨t, ht⟩ := exists_sec hL' (φ' := fun _ : PUnit => 𝟙 X') (ε' := fun _ => 1)
    (fun U _ h => by simp) s
  obtain ⟨σ, hσ⟩ := ArcPull.exists_up_sec ((isGen_iff w).1 hw) hL hL' (fun _ : PUnit => 𝟙 X') (fun _ => π)
    (fun _ => 1) (𝟙 X') (fun _ => by simp) t
  obtain ⟨n, c, u, hu⟩ := FlatSec.exists_comb_of_flat R R' g hg X f X' π f' H L hL σ
  obtain ⟨J, hJ⟩ := DegPull.exists_good' hL y
  have e := hσ _ (𝟙 X') y J J' hJ hJ'
  rw [ht _ _ y J' hJ', sval_of σ _ y J (fun _ => J π) (fun _ => by rw [Category.id_comp]), Category.id_comp] at e
  have z : ∀ i, gs π y _ ((u i).f (J π)) = 0 := fun i => by
    obtain ⟨v, hv⟩ := exists_pow_one (u i)
    obtain ⟨a, ha⟩ := hth v
    rw [← hv _ π y J hJ, sval_of_secIsMul ha π y hJ, h₀ y J hJ, mul_zero]
  have e' := (hu y (J π) (hJ π)).symm.trans e
  simp only [z, mul_zero, Finset.sum_const_zero] at e'
  exact (Units.mul_right_eq_zero _).1 e'.symm

end GlobalTheory.GenSecField

namespace GlobalTheory


open GlobalTheory.IndivisibleSection ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.GenSecField in
theorem exists_unit_generating_section_pull : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] (φ : R →+* K), Function.Injective φ → ∀ (D : DegPre R) (D' : DegPre K) (hD : IsPullDeg φ D D') (th : H0 D.P.L 1) (th' : H0 D'.P.L 1), (∀ s : H0 D.P.L 1, ∃ r : R, ∀ j, s.f j = resTop _ (scal D.P.A.hom r) * th.f j) → (∀ s : H0 D'.P.L 1, ∃ r : K, ∀ j, s.f j = resTop _ (scal D'.P.A.hom r) * th'.f j) → ∃ c : Kˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι), Good D.P.L z J → Good D'.P.L z J' → sval th (r ≫ PsiEvenPull.proj hD) z J = (TauTwist.unitAt (r ≫ D'.P.A.hom) z c * ArcPull.om hD.w z J J' r).val * sval th' r z J' := by
  intro R K _ _ _ φ hφ D D' hD th th' hth hth'
  have hc : ∀ _ : Fin 1, 𝟙 D'.P.A.left ≫ PsiEvenPull.proj hD = PsiEvenPull.proj hD ≫ 𝟙 D.P.A.left :=
    fun _ => (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨a, ha, -⟩ := SecPull.existsUnique_secPull _ _ _ _ D.P.L D'.P.L _ D.P.isLB D'.P.isLB hD.w hD.w_gen (Fin 1)
    (fun _ => 𝟙 _) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ)) (PsiEvenPull.proj hD) hc th
  obtain ⟨c, hac⟩ := hth' a
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) J J', Good D.P.L z J → Good D'.P.L z J' →
      sval th (r ≫ PsiEvenPull.proj hD) z J =
        cst (r ≫ D'.P.A.hom) z c * (ArcPull.om hD.w z J J' r).val * sval th' r z J' := fun Z r z J J' hJ hJ' => by
    have e := FamFieldPull.IsSecPull.val ha hc r z hJ hJ'
    rw [sval_of_secIsMul (p := D'.P.A.hom) hac r z hJ', Fin.prod_univ_one, Category.comp_id, zpow_natCast,
      pow_one] at e
    exact e.trans ((mul_left_comm _ _ _).trans (_root_.mul_assoc _ _ _).symm)
  by_cases h : c = 0
  · subst h
    have : IsProper D.P.A.hom := D.P.isAb.proper
    have : CompactSpace D.P.A.left := QuasiCompact.compactSpace_of_compactSpace D.P.A.hom
    have : QuasiSeparatedSpace D.P.A.left := quasiSeparatedSpace_of_quasiSeparated D.P.A.hom
    have h₀ : SecIsMul D'.P.A.hom (0 : K) th' th' := secIsMul_of_sval D'.P.isLB fun y J' hJ' => by
      rw [cst_zero', zero_mul]
      refine sval_eq_zero (flat_of_injective hφ) (pull_grp hD).1 D.P.isLB D'.P.isLB hD.w_gen hth
        (fun x J hJ => ?_) th' y hJ'
      obtain ⟨I, hI⟩ := DegPull.exists_good' D'.P.isLB x
      have e := key _ (𝟙 _) x J I hJ hI
      rwa [Category.id_comp, cst_zero', zero_mul, zero_mul] at e
    refine ⟨1, fun Z r z J J' hJ hJ' => ?_⟩
    rw [key Z r z J J' hJ hJ', sval_of_secIsMul h₀ r z hJ', cst_zero', zero_mul, zero_mul, zero_mul, mul_zero]
  · refine ⟨Units.mk0 c h, fun Z r z J J' hJ hJ' => ?_⟩
    rw [key Z r z J J' hJ hJ', Units.val_mul, TauTwist.unitAt_val]
    rfl

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitGeneratingSectionPullbackFieldStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_generatingSection_pullback_field : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] (φ : R →+* K), Function.Injective φ → ∀ (D : DegPre R) (D' : DegPre K) (hD : IsPullDeg φ D D') (th : H0 D.P.L 1) (th' : H0 D'.P.L 1), (∀ s : H0 D.P.L 1, ∃ r : R, ∀ j, s.f j = resTop _ (scal D.P.A.hom r) * th.f j) → (∀ s : H0 D'.P.L 1, ∃ r : K, ∀ j, s.f j = resTop _ (scal D'.P.A.hom r) * th'.f j) → ∃ c : Kˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι), Good D.P.L z J → Good D'.P.L z J' → sval th (r ≫ PsiEvenPull.proj hD) z J = (TauTwist.unitAt (r ≫ D'.P.A.hom) z c * ArcPull.om hD.w z J J' r).val * sval th' r z J' := by
  first | exact @GlobalTheory.exists_unit_generating_section_pull | exact GlobalTheory.exists_unit_generating_section_pull | (intros; apply GlobalTheory.exists_unit_generating_section_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSectionsIndependentOnClosedFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSectionsIndependentOnClosedFibre
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.IndepFib

theorem eq_zero_of_points {k : Type} [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsReduced X] (π : X ⟶ Sp k)
    [LocallyOfFiniteType π] (U : X.Opens) (f : Γ(X, U))
    (h : ∀ x : Sp k ⟶ X, x ≫ π = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U → GlobalTheory.ZH.valR x U f = 0) : f = 0 := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace π
  refine (basicOpen_eq_bot_iff f).1 ?_
  by_contra hne
  have hne' : ((X.basicOpen f : X.Opens) : Set X).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact fun e => hne (SetLike.coe_injective e)
  obtain ⟨y, hy, hc⟩ := nonempty_inter_closedPoints hne' (X.basicOpen f).isOpen.isLocallyClosed
  have hb : ⊤ ≤ (pointOfClosedPoint π y hc) ⁻¹ᵁ X.basicOpen f := fun q _ => by
    show pointOfClosedPoint π y hc q ∈ X.basicOpen f
    rw [pointOfClosedPoint_apply π y hc q]
    exact hy
  have hU : ⊤ ≤ (pointOfClosedPoint π y hc) ⁻¹ᵁ U := hb.trans (Scheme.Hom.preimage_mono _ (X.basicOpen_le f))
  exact ((CrdCalc.isUnit_valR_iff _ U hU f).2 hb).ne_zero (h _ (pointOfClosedPoint_comp π y hc) hU)

theorem lin_eq_zero {k : Type} [Field k] [IsAlgClosed k] (Φ : FibPre k) [Smooth Φ.G.hom] {N : ℕ}
    {q : QuadraticMap ℤ Φ.E.X ℝ} {J : Type} [Fintype J] {cls : J → Φ.E.X} {F : J → (Φ.H 1).Sec}
    (hG : Φ.Good N q cls F) (a : J → k) (h : ∀ v ∈ cone Φ.G.hom (Φ.H 1) F, ∑ i, a i * v i = 0) : a = 0 := by
  have : IsReduced Φ.G.left := GlobalTheory.isReduced_of_smooth_of_isReduced Φ.G.hom
  refine GlobalTheory.ZH.WtLin.linIndep k Φ N q J cls F hG a fun l => ?_
  refine eq_zero_of_points Φ.G.hom _ _ fun x hx hU => ?_
  have h1 := h _ ⟨x, hx, l, 1, hU, fun _ => rfl⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [CrdCalc.valR_eq x _ hU, map_sum, ← h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← CrdCalc.valR_eq, ← CrdCalc.valR_eq, Units.val_one, _root_.one_mul]
  exact congrArg (· * _) (GlobalTheory.Points.valR_constFn_of_section Φ.G.hom x hx _ hU (a i))

theorem change_mul_change {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {J : Type} [Fintype J]
    {A : Subalgebra o Ω} {B B' C : Matrix J J Ω} (hC : C * B' = 1) {g g' : Matrix J J A}
    (h : B' = g.map (↑) * B) (h' : B = g'.map (↑) * B') : g * g' = 1 := by
  have h1 : B' * C = 1 := mul_eq_one_comm.1 hC
  have h2 : (g.map (↑) * g'.map (↑) : Matrix J J Ω) = 1 := by
    calc (g.map (↑) * g'.map (↑) : Matrix J J Ω) = (g.map (↑) * (g'.map (↑) * B')) * C := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_one]
      _ = 1 := by rw [← h', ← h, h1]
  ext i j
  have := congrFun (congrFun h2 i) j
  by_cases hij : i = j <;> simpa [Matrix.mul_apply, Matrix.one_apply, hij] using this

theorem indep_on_closed_fibre : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE), S.Big → ρ.HasGeo → ∀ l, ∀ z ∈ Q.W l, IsClosed ({z} : Set M.Z) → ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ M.Z), Set.range x = {z} ∧ ∀ c : S.J → K, (∀ (g : Sp K ⟶ (Q.P.hom ⁻¹ᵁ Q.W l).toScheme) (j), Set.range (g ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι) ⊆ Q.G → g ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom = x → ∑ i, c i * valF g _ ((Q.σ l i).f j) = 0) → c = 0 := by
  intro L o Ω _ _ _ _ S ρ M U₀ EE hB Q hBig hGeo l z hz hcl
  obtain ⟨hT, hC⟩ := GlobalTheory.T.exists_geometricTest_map_classicalPoint L o Ω S ρ M U₀ EE hB Q hBig hGeo
  obtain ⟨p, hp, y, hy, hyU⟩ := hC z hcl
  obtain ⟨y₀, t, c, ⟨tm⟩⟩ := hT p y hyU
  have hG := GlobalTheory.T.testModel_maps_into_openPart L o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hBig
  haveI : IsAlgClosed (kb p) := (GlobalTheory.ZJ.kb_isAlgClosed_and_conj p).1
  have hx : (rPt p ≫ y) (IsLocalRing.closedPoint (kb p)) = z := by
    exact (Scheme.Hom.comp_apply _ _ _).trans
      ((congrArg y (IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p)))).trans hy)
  have hr : Set.range (rPt p ≫ y) = {z} := hx ▸ RatModel.range_eq_singleton _ _
  refine ⟨kb p, inferInstance, rPt p ≫ y, hr, fun a ha => ?_⟩
  have hz' : z ∈ Q.W tm.l := hy ▸ tm.mem
  obtain ⟨g, hg, -⟩ := InFibChart.exists_change Q tm.l l hz' hz
  obtain ⟨g', hg', hc'⟩ := InFibChart.exists_change Q l tm.l hz hz'
  have hgg := change_mul_change (Q.c_inv l) hg hg'
  let χ := RatModel.valHom (rPt p ≫ y) z hr
  have hGG : g.map χ * g'.map χ = 1 := by
    rw [← Matrix.map_mul, hgg, Matrix.map_one _ χ.map_zero χ.map_one]
  let ψ : t.u.V →+* kb p := (IsLocalRing.residue (OO p)).comp t.u.j
  have hψ : spMap ψ = rPt p ≫ spMap t.u.j := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have pb : IsPullback t.mod.r t.mod.Φ.G.hom t.u.G.hom (rPt p ≫ spMap t.u.j) := t.mod.cart.1
  have hs : Smooth t.u.G.hom := t.mod.smooth.smooth
  have : Smooth t.mod.Φ.G.hom := MorphismProperty.of_isPullback pb hs
  have h0 := lin_eq_zero t.mod.Φ t.mod.good (Matrix.vecMul (Matrix.vecMul a (g.map χ)) (tm.m.map ψ)) ?_
  · have hdet : (tm.m.map ψ).det ≠ 0 := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact (tm.unit.map ψ).ne_zero
    have h1 := Matrix.eq_zero_of_vecMul_eq_zero hdet h0
    have h2 := congrArg (Matrix.vecMul · (g'.map χ)) h1
    simpa [Matrix.vecMul_vecMul, hGG] using h2
  rintro v ⟨x, hxs, hv⟩
  have h1 := t.mod.red (Over.homMk x hxs) v hv
  have hxG : (x ≫ t.mod.r) ≫ t.u.G.hom = spMap ψ := by
    rw [Category.assoc, pb.w, ← Category.assoc, hxs, Category.id_comp, hψ]
  have h2 := tm.crd (kb p) ψ (x ≫ t.mod.r) v hxG h1
  have hov : ((x ≫ t.mod.r) ≫ tm.f) ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι ≫ Q.P.hom = rPt p ≫ y := by
    rw [Category.assoc, tm.f_over, ← Category.assoc, hxG, hψ, Category.assoc, c.fac]
  obtain ⟨x', hx'⟩ : ∃ x' : Sp (kb p) ⟶ (Q.P.hom ⁻¹ᵁ Q.W l).toScheme,
      x' ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι = ((x ≫ t.mod.r) ≫ tm.f) ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι :=
    ⟨IsOpenImmersion.lift _ _ (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨w, rfl⟩
      have e : Q.P.hom ((((x ≫ t.mod.r) ≫ tm.f) ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) w) = z := by
        rw [← Scheme.Hom.comp_apply, Category.assoc, hov, Subsingleton.elim w (IsLocalRing.closedPoint (kb p)), hx]
      show Q.P.hom _ ∈ Q.W l
      rw [e]
      exact hz), IsOpenImmersion.lift_fac _ _ _⟩
  have hov' : x' ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom = rPt p ≫ y := by
    rw [← Category.assoc, hx', Category.assoc, hov]
  obtain ⟨w, hw⟩ := CrdCalc.crd_exists (LB.isLB_pull Q.isLB _) (Q.σ l) x'
  obtain ⟨u, hu⟩ := InFibChart.crd_change Q hB.ov.ne l tm.l x' _ (rPt p ≫ y) hx'.symm hov' hx hz hz' g' hc' hw h2
  have h3 : a ⬝ᵥ w = 0 := by
    obtain ⟨j, e, -, he⟩ := hw
    have h4 := ha x' j (by
      rw [hx', Category.assoc]
      rintro _ ⟨q, rfl⟩
      rw [Scheme.Hom.comp_apply]
      exact hG (Set.mem_univ _)) hov'
    rw [dotProduct, ← mul_zero (e : kb p), ← h4, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [he i, mul_left_comm]
    rfl
  have h5 : (tm.m.map ψ).mulVec v = u • (g'.map χ).mulVec w := hu
  show Matrix.vecMul (Matrix.vecMul a (g.map χ)) (tm.m.map ψ) ⬝ᵥ v = 0
  rw [← Matrix.dotProduct_mulVec, ← Matrix.dotProduct_mulVec, h5, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hGG,
    Matrix.one_mulVec, dotProduct_smul, h3, smul_zero]

end GlobalTheory.ZH.IndepFib
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSectionsIndependentOnClosedFibreStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSections_independent_on_closed_fibre : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE), S.Big → ρ.HasGeo → ∀ l, ∀ z ∈ Q.W l, IsClosed ({z} : Set M.Z) → ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ M.Z), Set.range x = {z} ∧ ∀ c : S.J → K, (∀ (g : Sp K ⟶ (Q.P.hom ⁻¹ᵁ Q.W l).toScheme) (j), Set.range (g ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι) ⊆ Q.G → g ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom = x → ∑ i, c i * valF g _ ((Q.σ l i).f j) = 0) → c = 0 := by
  first | exact @GlobalTheory.ZH.IndepFib.indep_on_closed_fibre | exact GlobalTheory.ZH.IndepFib.indep_on_closed_fibre | (intros; apply GlobalTheory.ZH.IndepFib.indep_on_closed_fibre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAutomorphismPermutationMaxOrderMembersStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_automorphism_permutation_maxOrder_members : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (n : ℕ) (M : Fin n → Model R A), (∀ i, (M i).Irr) → WeakNeron M → ∃ S : Finset (Fin n), S.Nonempty ∧ (∀ (f : A ≅ A), ∀ i ∈ S, ∃ i' ∈ S, GenIso (M i) (M i') f.hom) ∧ ∀ (Θ : A ⊗ A ≅ A ⊗ A), ∀ i ∈ S, ∀ j ∈ S, ∃ i' ∈ S, ∃ j' ∈ S, GenIso ((M i).prod (M j)) ((M i').prod (M j')) Θ.hom := by
  first | exact @GlobalTheory.SS.exists_permuted_members | exact GlobalTheory.SS.exists_permuted_members | (intros; apply GlobalTheory.SS.exists_permuted_members <;> assumption)
end
