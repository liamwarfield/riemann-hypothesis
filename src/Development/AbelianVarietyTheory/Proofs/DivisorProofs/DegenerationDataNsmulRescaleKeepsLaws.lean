module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
public import Development.AutomorphicArithmetic.LocalEmbeddings.BadRepAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadPartDimLeSumLocalSharesWhittaker
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalShareSumBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoveringRepresentationTypeFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftedPolarisationKernelKilledOfUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLFunctionBottomPair

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataNsmulRescaleKeepsLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataNsmulRescaleKeepsLaws
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon.MulDeg

variable {R : Type} [CommRing R] [IsDomain R]

def tau3 (D : DegPre R) (s a b : D.X) :=
  LB.mulGen D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (D.psi s) (LB.invGen D.P.L _ _ (D.psi a)))
      (LB.invGen D.P.L _ _ (D.psi b)))
    (LB.invGen D.P.L _ _ D.rigK)

theorem corr_even_degenerationData_negPoint (D : DegPre R) (h : D.PsiEven) (a m : D.X) (hm : m = -a) :
    LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (D.psi m) (LB.pullGen D.P.L _ _ D.sym (D.xK a))) (D.psi a) := by
  subst hm
  exact h a

theorem corr_bimultiplicative_degenerationData_sums (D : DegPre R) (h : D.TauBimult) (a a' b s t u v : D.X) (hs : s = a + a') (ht : t = a + a' + b)
    (hu : u = a + b) (hv : v = a' + b) :
    LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (tau3 D t s b)
        (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a a' b)))
      (LB.mulGen D.P.L _ _ _ _ (tau3 D u a b) (tau3 D v a' b)) := by
  subst hs ht hu hv
  exact h a a' b

theorem corr_balanced_degenerationData_rosati (D : DegPre R) (f g : D.P.A ⟶ D.P.A) (p q : D.X → D.X) (h : D.TauBal f g p q)
    (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A f g) rosatiε)) (hu : u.IsGen)
    (h1 : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L))
    (y y' a a' s t : D.X) (ha : a = p y) (ha' : a' = q y') (hs : s = p y + y') (ht : t = y + q y') :
    LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (tau3 D s a y') (LB.pullGen D.P.L _ _ u (D.pt2 y y')))
      (tau3 D t y a') := by
  subst ha ha' hs ht
  exact h u hu h1 y y'

variable {O : Type} [CommRing O] [StarRing O]

local instance modMul (D : DegPre R) [h : Module O D.X] (n : ℕ) : Module O (mulDeg D n).X := h

def mulAct (D : DegPre R) [Module O D.X] (oa : D.OAct O) (n : ℕ) : (mulDeg D n).OAct O where
  onB := oa.onB
  c_lin := fun a (y : D.X) => by
    show D.c (n • (a • y)) = D.c (n • y) ≫ oa.onB.act a
    rw [smul_comm n a y, oa.c_lin]
  tau_bal := fun a u hu h1 (y y' : D.X) =>
    corr_balanced_degenerationData_rosati D _ _ _ _ (oa.tau_bal a) u hu h1 (n • y) (n • y') (n • (a • y)) (n • (star a • y'))
      (n • (a • y + y')) (n • (y + star a • y')) (smul_comm n a y) (smul_comm n (star a) y')
      (by rw [nsmul_add, smul_comm n a y]) (by rw [nsmul_add, smul_comm n (star a) y'])

theorem corr_polarisationElement_degenerationData (D : DegPre R) [Module O D.X] (oa : D.OAct O) (w0 : O)
    (u : LB.Gen (LB.LinComb D.P.L (K := Fin 4)
      ![(padd D.P.A (𝟙 _) (oa.onB.act w0)).left, 𝟙 D.P.A.left, (oa.onB.act w0).left, (toUnit D.P.A ≫ η[D.P.A]).left]
      ![1, -2, -1, 2]))
    (h : ∀ y, LB.Gen.Corr D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (D.tau y (w0 • y)) (LB.pullGen D.P.L _ _ u (D.xK y)))
      (LB.mulGen D.P.L _ _ _ _ (D.psi y) D.rigK)) (y s b : D.X) (hb : b = w0 • y) (hs : s = y + w0 • y) :
    LB.Gen.Corr D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (tau3 D s y b) (LB.pullGen D.P.L _ _ u (D.xK y)))
      (LB.mulGen D.P.L _ _ _ _ (D.psi y) D.rigK) := by
  subst hb hs
  exact h y

theorem mulDeg_laws : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O D.X] (oa : D.OAct O) (w0 : O) (n : ℕ), D.PsiEven → D.TauBimult → TraceFormTwistIso D oa w0 → (∀ y, PsiUnitOn D y Set.univ) → letI : Module O (mulDeg D n).X := ‹Module O D.X›; (mulDeg D n).PsiEven ∧ (mulDeg D n).TauBimult ∧ (∀ y, PsiUnitOn (mulDeg D n) y Set.univ) ∧ ∃ oa' : (mulDeg D n).OAct O, oa'.onB = oa.onB ∧ TraceFormTwistIso (mulDeg D n) oa' w0 := by
  intro R _ _ D O _ _ _ oa w0 n he hb hw hg
  refine ⟨fun (a : D.X) => corr_even_degenerationData_negPoint D he (n • a) (n • (-a)) (neg_nsmul a n),
    fun (a a' b : D.X) => corr_bimultiplicative_degenerationData_sums D hb (n • a) (n • a') (n • b) (n • (a + a')) (n • (a + a' + b)) (n • (a + b))
      (n • (a' + b)) (nsmul_add _ _ _) (by rw [nsmul_add, nsmul_add]) (nsmul_add _ _ _) (nsmul_add _ _ _),
    fun (y : D.X) => hg (n • y), mulAct D oa n, rfl, ?_⟩
  obtain ⟨u, hu, h1, h⟩ := hw
  exact ⟨u, hu, h1, fun (y : D.X) => corr_polarisationElement_degenerationData D oa w0 u h (n • y) (n • (y + w0 • y)) (n • (w0 • y)) (smul_comm n w0 y)
    (by rw [nsmul_add, smul_comm n w0 y])⟩

end GlobalTheory.UCanon.MulDeg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataNsmulRescaleKeepsLawsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degenerationDataNsmulRescale_keeps_laws : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O D.X] (oa : D.OAct O) (w0 : O) (n : ℕ), D.PsiEven → D.TauBimult → TraceFormTwistIso D oa w0 → (∀ y, PsiUnitOn D y Set.univ) → letI : Module O (mulDeg D n).X := ‹Module O D.X›; (mulDeg D n).PsiEven ∧ (mulDeg D n).TauBimult ∧ (∀ y, PsiUnitOn (mulDeg D n) y Set.univ) ∧ ∃ oa' : (mulDeg D n).OAct O, oa'.onB = oa.onB ∧ TraceFormTwistIso (mulDeg D n) oa' w0 := by
  first | exact @GlobalTheory.UCanon.MulDeg.mulDeg_laws | exact GlobalTheory.UCanon.MulDeg.mulDeg_laws | (intros; apply GlobalTheory.UCanon.MulDeg.mulDeg_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBaseWith
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

noncomputable section

namespace GlobalTheory.USep.EvG

def FromBaseWith {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) (τ₀ : GlobalTheory.UChart.Gens Q) {W₀ : Type} [CommRing W₀]
    (ιb : W₀ →+* V) (B₀ : Over (Sp W₀)) [GrpObj B₀] (M₀ : LB B₀.left) (c₀ : Q.X → (Sp W₀ ⟶ B₀.left))
    (τ₁ : ∀ a b : Q.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
    (β : Q.P.A.left ⟶ B₀.left) (w : LB.Iso Q.P.L (M₀.pull β)) : Prop :=
  IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback Q.P.A B₀ (spMap ιb) β ∧ w.IsGen ∧
    (∀ a, GlobalTheory.UChart.cpt Q a ≫ β = spMap ιb ≫ c₀ a) ∧ (∀ a b, (τ₁ a b).IsGen) ∧
    ∀ (a b : Q.X) zz (J : (Sp V ⟶ Q.P.A.left) → Q.P.L.ι) (J₀ : (Sp V ⟶ B₀.left) → M₀.ι),
      Good Q.P.L zz J → Good M₀ zz J₀ →
      val (τ₀ a b) (𝟙 (Sp V)) zz J =
        gm (GlobalTheory.UChart.cpt Q (a + b)) zz _
            (w.s (fun _ => J₀ (GlobalTheory.UChart.cpt Q (a + b) ≫ β), J (GlobalTheory.UChart.cpt Q (a + b)))) *
        (gm (GlobalTheory.UChart.cpt Q a) zz _ (w.s (fun _ => J₀ (GlobalTheory.UChart.cpt Q a ≫ β), J (GlobalTheory.UChart.cpt Q a))))⁻¹ *
        (gm (GlobalTheory.UChart.cpt Q b) zz _ (w.s (fun _ => J₀ (GlobalTheory.UChart.cpt Q b ≫ β), J (GlobalTheory.UChart.cpt Q b))))⁻¹ *
        gm (GlobalTheory.UChart.cpt Q 0) zz _ (w.s (fun _ => J₀ (GlobalTheory.UChart.cpt Q 0 ≫ β), J (GlobalTheory.UChart.cpt Q 0))) *
        val (τ₁ a b) (spMap ιb) zz J₀

theorem fromBase_iff {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) (τ₀ : GlobalTheory.UChart.Gens Q) {W₀ : Type}
    [CommRing W₀] (ιb : W₀ →+* V) :
    GlobalTheory.UChart.FromBase Q τ₀ ιb ↔ ∃ (B₀ : Over (Sp W₀)) (_ : GrpObj B₀) (M₀ : LB B₀.left) (c₀ : Q.X → (Sp W₀ ⟶ B₀.left))
      (τ₁ : ∀ a b : Q.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
      (β : Q.P.A.left ⟶ B₀.left) (w : LB.Iso Q.P.L (M₀.pull β)), FromBaseWith Q τ₀ ιb B₀ M₀ c₀ τ₁ β w :=
  Iff.rfl

abbrev gwx {X' X Y : Scheme.{0}} {L' : LB X'} {L : LB X} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F)) (y : Y)
    (J : (Y ⟶ X') → L'.ι) (J₀ : (Y ⟶ X) → L.ι) (x : Y ⟶ X') : (Y.presheaf.stalk y)ˣ :=
  gw w x y (J₀ (x ≫ F)) (J x)

end GlobalTheory.USep.EvG
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfIsAlgClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfIsAlgClosed
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbDivPt

theorem exists_pow_eq_of_isAlgClosed : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A →
    ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (n : ℕ), 0 < n →
      ∀ g : Over.mk x ⟶ A, ∃ g' : Over.mk x ⟶ A, g' ^ n = g := by
  intro S A _ hA k _ _ x n hn g
  have hc := hA.comm
  obtain ⟨hfin, -, hsurj⟩ := GlobalTheory.KthRoot.finite_flat_surjective_mulN_any S A hA n hn
  have : IsFinite (pullback.snd (mulN A n).left g.left) := by
    haveI := hfin; infer_instance
  have : Surjective (pullback.snd (mulN A n).left g.left) := by
    haveI := hsurj; infer_instance
  obtain ⟨t, ht⟩ := ReciprocityTheory.ChartRestriction.G.H1.SectionDivision.exists_section (pullback.snd (mulN A n).left g.left)
  have hb' : (t ≫ pullback.fst (mulN A n).left g.left) ≫ (mulN A n).left = g.left := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ht, Category.id_comp]
  have hw : (t ≫ pullback.fst (mulN A n).left g.left) ≫ A.hom = (Over.mk x).hom := by
    rw [← Over.w (mulN A n), ← Category.assoc, hb', Over.w g]
  refine ⟨Over.homMk _ hw, ?_⟩
  have e : ∀ b : Over.mk x ⟶ A, b ^ n = b ≫ mulN A n := fun b => by
    rw [GlobalTheory.MulFlatSurj.mulN_eq_pow, MonObj.comp_pow, Category.comp_id]
  rw [e]
  exact Over.OverMorphism.ext hb'

end GlobalTheory.AbDivPt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfIsAlgClosedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_eq_point_of_isAbelianScheme : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (n : ℕ), 0 < n → ∀ g : Over.mk x ⟶ A, ∃ g' : Over.mk x ⟶ A, g' ^ n = g := by
  first | (exact @GlobalTheory.AbDivPt.exists_pow_eq_of_isAlgClosed) | (exact GlobalTheory.AbDivPt.exists_pow_eq_of_isAlgClosed) | (intros; apply GlobalTheory.AbDivPt.exists_pow_eq_of_isAlgClosed  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSpecializesSameFibreIsIntegralHom
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSpecializesSameFibreIsIntegralHom
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

namespace GlobalTheory

theorem eq_of_specializes_of_isIntegralHom : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIntegralHom f] {x x' : X}, x ⤳ x' → f x = f x' → x = x' := by
  intro X Y f _ x x' hxx' hf
  obtain ⟨_, ⟨V, hV0, rfl⟩, hxV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x')) isOpen_univ
  have hV : IsAffineOpen V := hV0
  have hU : IsAffineOpen (f ⁻¹ᵁ V) := hV.preimage f
  have hx' : x' ∈ f ⁻¹ᵁ V := hxV
  have hx : x ∈ f ⁻¹ᵁ V := hxx'.mem_open (f ⁻¹ᵁ V).isOpen hx'
  set P := hU.primeIdealOf ⟨x, hx⟩ with hPdef
  set P' := hU.primeIdealOf ⟨x', hx'⟩ with hP'def
  have eP : hU.fromSpec P = x := hU.fromSpec_primeIdealOf ⟨x, hx⟩
  have eP' : hU.fromSpec P' = x' := hU.fromSpec_primeIdealOf ⟨x', hx'⟩
  have hsp : P ⤳ P' := by
    exact hU.fromSpec.isOpenEmbedding.toIsInducing.specializes_iff.1 (by rw [eP, eP']; exact hxx')
  have hle : P.asIdeal ≤ P'.asIdeal := (PrimeSpectrum.le_iff_specializes P P').mpr hsp
  have sq : Spec.map (f.app V) ≫ hV.fromSpec = hU.fromSpec ≫ f := by
    rw [Scheme.Hom.app_eq_appLE]
    exact IsAffineOpen.SpecMap_appLE_fromSpec f hV hU le_rfl
  have img : ∀ Q : Spec Γ(X, f ⁻¹ᵁ V), hV.fromSpec (Spec.map (f.app V) Q) = f (hU.fromSpec Q) :=
    fun Q => (Scheme.Hom.comp_apply _ _ _).symm.trans
      ((congrArg (fun m : Spec Γ(X, f ⁻¹ᵁ V) ⟶ Y => m Q) sq).trans (Scheme.Hom.comp_apply _ _ _))
  have hc : Spec.map (f.app V) P = Spec.map (f.app V) P' := by
    apply hV.fromSpec.isOpenEmbedding.injective
    exact (img P).trans ((congrArg f eP).trans (hf.trans ((congrArg f eP').symm.trans (img P').symm)))
  have hc' : P.asIdeal.comap (f.app V).hom = P'.asIdeal.comap (f.app V).hom :=
    congrArg PrimeSpectrum.asIdeal hc
  letI : Algebra Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
  haveI : Algebra.IsIntegral Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := ⟨f.isIntegral_app V hV⟩
  have heq : P.asIdeal = P'.asIdeal := by
    by_contra hne
    have hlt := Ideal.IsIntegral.comap_lt_comap (R := Γ(Y, V)) (lt_of_le_of_ne hle hne)
    exact (ne_of_lt hlt) hc'
  have : P = P' := PrimeSpectrum.ext heq
  rw [← eP, ← eP', this]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSpecializesSameFibreIsIntegralHomStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_specializes_same_fibre_isIntegralHom : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIntegralHom f] {x x' : X}, x ⤳ x' → f x = f x' → x = x' := by
  first | exact @GlobalTheory.eq_of_specializes_of_isIntegralHom | exact GlobalTheory.eq_of_specializes_of_isIntegralHom | (intros; apply GlobalTheory.eq_of_specializes_of_isIntegralHom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicEqZeroOfFpqc
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackOneProdKernel
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.RigDesc

theorem isPullback_one_prod {S : Scheme.{0}} (A : Over S) {V V' : Over S} (v : V ⟶ V') :
    IsPullback (lift (fst A V) (snd A V ≫ v)).left (snd A V).left (snd A V').left v.left := by
  have hT : IsPullback (fst A V).left (snd A V).left A.hom V.hom := IsPullback.of_hasPullback _ _
  have hY : IsPullback (fst A V').left (snd A V').left A.hom V'.hom := IsPullback.of_hasPullback _ _
  have m₁ : (lift (fst A V) (snd A V ≫ v)).left ≫ (fst A V').left = (fst A V).left := by
    rw [← Over.comp_left, lift_fst]
  have m₂ : (lift (fst A V) (snd A V ≫ v)).left ≫ (snd A V').left = (snd A V).left ≫ v.left := by
    rw [← Over.comp_left, lift_snd, Over.comp_left]
  have hT' : IsPullback ((lift (fst A V) (snd A V ≫ v)).left ≫ (fst A V').left) (snd A V).left A.hom
      (v.left ≫ V'.hom) := by
    rw [m₁, Over.w v]; exact hT
  exact IsPullback.of_right hT' m₂ hY

theorem isPullback_one_prod_kernel {S : Scheme.{0}} (A Y Y' W : Over S) (c : Y' ⟶ Y) (w₁ w₂ : W ⟶ Y')
    (hK : IsPullback w₁.left w₂.left c.left c.left) :
    IsPullback (lift (fst A W) (snd A W ≫ w₁)).left (lift (fst A W) (snd A W ≫ w₂)).left
      (lift (fst A Y') (snd A Y' ≫ c)).left (lift (fst A Y') (snd A Y' ≫ c)).left := by
  have Hc := isPullback_one_prod A c
  have H₂ := isPullback_one_prod A w₂
  have outer := H₂.flip.paste_horiz hK
  have e₁ : (lift (fst A W) (snd A W ≫ w₁)).left ≫ (snd A Y').left = (snd A W).left ≫ w₁.left := by
    rw [← Over.comp_left, lift_snd, Over.comp_left]
  have e₂ : (lift (fst A Y') (snd A Y' ≫ c)).left ≫ (snd A Y).left = (snd A Y').left ≫ c.left := by
    rw [← Over.comp_left, lift_snd, Over.comp_left]
  have hw : w₁ ≫ c = w₂ ≫ c := Over.OverMorphism.ext hK.w
  refine IsPullback.of_right (h₁₂ := (snd A Y').left) (h₂₂ := (snd A Y).left) ?_ ?_ Hc.flip
  · rw [e₁, e₂]; exact outer
  · rw [← Over.comp_left, ← Over.comp_left, comp_lift, comp_lift, lift_fst, lift_fst, lift_snd_assoc,
      lift_snd_assoc, Category.assoc, Category.assoc, hw]

theorem triv_of_triv_zero_of_fpqc : ∀ (S : Scheme.{0}) (X Y Y' : Over S) [GrpObj X], IsAbelianScheme X →
    ∀ (c : Y' ⟶ Y), Flat c.left → Surjective c.left → QuasiCompact c.left → ∀ D : LB (X ⊗ Y).left, D.IsLB →
    Triv (ev D (1 : Y ⟶ X) (𝟙 Y)) → Triv (ev D (fst X Y') (snd X Y' ≫ c)) → Triv D := by
  intro S X Y Y' _ hA c hfl hsu hqc L hL h0 h1
  let F : X ⊗ Y' ⟶ X ⊗ Y := lift (fst X Y') (snd X Y' ≫ c)
  let e : Y ⟶ X ⊗ Y := lift 1 (𝟙 Y)
  let e' : Y' ⟶ X ⊗ Y' := lift 1 (𝟙 Y')
  change Triv (L.pull e.left) at h0
  change Triv (L.pull F.left) at h1
  have hEF : e' ≫ F = c ≫ e := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [e, e', F]
  have hep : e' ≫ snd X Y' = 𝟙 Y' := lift_snd _ _
  have H : IsPullback F.left (snd X Y').left (snd X Y).left c.left := isPullback_one_prod X c
  have hF₁ : Flat F.left := MorphismProperty.of_isPullback H.flip hfl
  have hF₂ : Surjective F.left := MorphismProperty.of_isPullback H.flip hsu
  have hF₃ : QuasiCompact F.left := MorphismProperty.of_isPullback H.flip hqc
  let W : Over S := Over.mk (pullback.fst c.left c.left ≫ Y'.hom)
  let w₁ : W ⟶ Y' := Over.homMk (pullback.fst c.left c.left) rfl
  let w₂ : W ⟶ Y' := Over.homMk (pullback.snd c.left c.left) (by
    show pullback.snd c.left c.left ≫ Y'.hom = pullback.fst c.left c.left ≫ Y'.hom
    rw [← Over.w c, ← Category.assoc, ← pullback.condition, Category.assoc])
  have hw : w₁ ≫ c = w₂ ≫ c := Over.OverMorphism.ext pullback.condition
  have hK : IsPullback w₁.left w₂.left c.left c.left := IsPullback.of_hasPullback c.left c.left
  let g₁ : X ⊗ W ⟶ X ⊗ Y' := lift (fst X W) (snd X W ≫ w₁)
  let g₂ : X ⊗ W ⟶ X ⊗ Y' := lift (fst X W) (snd X W ≫ w₂)
  have hKP : IsPullback g₁.left g₂.left F.left F.left := isPullback_one_prod_kernel X Y Y' W c w₁ w₂ hK
  have hg : g₁.left ≫ F.left = g₂.left ≫ F.left := hKP.w
  obtain ⟨g, hgg⟩ := h0
  obtain ⟨t, ht⟩ := h1
  have n₁ : (snd X Y' ≫ e').left ≫ F.left = (snd X Y' ≫ c).left ≫ e.left := by
    rw [← Over.comp_left, ← Over.comp_left, Category.assoc, hEF, Category.assoc]
  obtain ⟨t', ht', hv⟩ := exists_gen hL (K' := PUnit) (φ' := fun _ => F.left) (ε' := fun _ => 1)
    (fun U _ k => by
      simp only [Fintype.prod_sum_type, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, n₁]
      simp)
    (LB.mulGen L _ _ _ _ (LB.mulGen L _ _ _ _ t (LB.invGen L _ _ (LB.pullGen L _ _ t (snd X Y' ≫ e').left)))
      (LB.pullGen L _ _ g (snd X Y' ≫ c).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)))
      (DVR.pullGen_isGen _ _ _ _ hgg _))
  have norm : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y'.left) (z : Z) (J), Geo.Tor.Good L z J →
      val t' (r ≫ e'.left) z J = val g (r ≫ c.left) z J := by
    intro Z r z J hJ
    have a₁ : (r ≫ e'.left) ≫ (snd X Y' ≫ e').left = r ≫ e'.left := by
      rw [Category.assoc, ← Over.comp_left, ← Category.assoc e', hep, Category.id_comp]
    have a₂ : (r ≫ e'.left) ≫ (snd X Y' ≫ c).left = r ≫ c.left := by
      rw [Category.assoc, ← Over.comp_left, ← Category.assoc e', hep, Category.id_comp]
    rw [hv Z _ z J hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, a₁, a₂, mul_inv_cancel,
      _root_.one_mul]
  refine GlobalTheory.FlatDescent.triv_of_gen_descent L hL F.left hF₁ hF₂ hF₃ g₁.left g₂.left hKP t' ht' (fun z J hJ => ?_)
  let o : W ⟶ X ⊗ W := lift 1 (𝟙 W)
  have hg1 : o.left ≫ g₁.left = w₁.left ≫ e'.left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp [o, g₁, e']
  have hg2 : o.left ≫ g₂.left = w₂.left ≫ e'.left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp [o, g₂, e']
  have ho : o.left ≫ (snd X W).left = 𝟙 _ := by rw [← Over.comp_left, lift_snd, Over.id_left]
  have hwc : w₁.left ≫ c.left = w₂.left ≫ c.left := by rw [← Over.comp_left, ← Over.comp_left, hw]
  have key2 := gen_unique' hL (φ := fun _ : PUnit => g₁.left ≫ F.left) (ε := fun _ => (1 : ℤ))
    (φ' := fun _ : PUnit => g₂.left ≫ F.left) (ε' := fun _ => 1)
    (fun U _ k => by simp only [hg]) (snd X W).left o.left ho (surj_snd GlobalTheory.SemiRigid.globalFns hA W)
    (u := LB.pullGen L _ _ t' g₁.left) (u' := LB.pullGen L _ _ t' g₂.left)
    (DVR.pullGen_isGen _ _ _ _ ht' _) (DVR.pullGen_isGen _ _ _ _ ht' _)
    (fun y I hI => by rw [val_pull hI, val_pull hI, hg1, hg2, norm _ _ _ _ hI, norm _ _ _ _ hI, hwc])
    _ (𝟙 _) z J hJ
  rwa [val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp] at key2

end GlobalTheory.RigDesc
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.BirigUniq

theorem one_comp_monHom {S : Scheme.{0}} {T A A' : Over S} [GrpObj A] [GrpObj A'] (f : A ⟶ A') [IsMonHom f] :
    (1 : T ⟶ A) ≫ f = 1 := by
  rw [Hom.one_def, Hom.one_def, Category.assoc, IsMonHom.one_hom]

theorem pull_comp_left {S : Scheme.{0}} {U V W : Over S} (g : U ⟶ V) (f : V ⟶ W) (c : GlobalTheory.CechPic.Pic W.left) :
    GlobalTheory.CechPic.pull (g ≫ f).left c = GlobalTheory.CechPic.pull g.left (GlobalTheory.CechPic.pull f.left c) := by
  rw [Over.comp_left, GlobalTheory.CechPic.pull_comp]

theorem pic_eq_zero_of_fpqc {S : Scheme.{0}} (X Y Y' : Over S) [GrpObj X] (hX : IsAbelianScheme X)
    (c : Y' ⟶ Y) (hfl : Flat c.left) (hsu : Surjective c.left) (hqc : QuasiCompact c.left)
    (d : GlobalTheory.CechPic.Pic (X ⊗ Y).left)
    (h0 : GlobalTheory.CechPic.pull (lift (1 : Y ⟶ X) (𝟙 Y)).left d = 0)
    (h1 : GlobalTheory.CechPic.pull (lift (fst X Y') (snd X Y' ≫ c)).left d = 0) : d = 0 := by
  obtain ⟨D, hD, rfl⟩ := GlobalTheory.CechPic.cls_surj d
  have t := GlobalTheory.RigDesc.triv_of_triv_zero_of_fpqc S X Y Y' hX c hfl hsu hqc D hD
    ((GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hD _)).1 h0) ((GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hD _)).1 h1)
  exact (GlobalTheory.CechPic.cls_eq_zero_iff hD).2 t

end GlobalTheory.BirigUniq

namespace GlobalTheory.BirigUniq

end GlobalTheory.BirigUniq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadAtFromInputs
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.BadIndef

theorem finiteDimensional_of_lat {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L : Submodule (𝓞 K) V) (hL : L.FG)
    (hs : Submodule.span K (L : Set V) = ⊤) : FiniteDimensional K V := by
  obtain ⟨s, rfl⟩ := hL
  refine Module.finite_def.2 ⟨s, ?_⟩
  rw [← Submodule.span_span_of_tower (𝓞 K) K (s : Set V)]
  exact hs


end GlobalTheory.BadIndef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShimuraObjectPullbackCompCancel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShimuraObjectPullbackCompCancel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon

theorem obj_pull_comp_cancel : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}, (∀ {S S' : Scheme.{0}} (s : S ⟶ Sp (KA l)) (o : Obj D l (baseKA l) s) (f : S' ⟶ S) (s' : S' ⟶ Sp (KA l)), s' = f ≫ s → ∃ o' : Obj D l (baseKA l) s', Nonempty (ObjMap o' o f)) ∧ (∀ {S S' S'' : Scheme.{0}} (s : S ⟶ Sp (KA l)) (s' : S' ⟶ Sp (KA l)) (s'' : S'' ⟶ Sp (KA l)) (o : Obj D l (baseKA l) s) (o' : Obj D l (baseKA l) s') (o'' : Obj D l (baseKA l) s'') (f : S' ⟶ S) (g : S'' ⟶ S') (m : ObjMap o' o f), (∀ n : ObjMap o'' o' g, ∃ k : ObjMap o'' o (g ≫ f), k.toSABMap.φ = n.toSABMap.φ ≫ m.toSABMap.φ) ∧ ∀ k : ObjMap o'' o (g ≫ f), ∃ n : ObjMap o'' o' g, k.toSABMap.φ = n.toSABMap.φ ≫ m.toSABMap.φ) := by
  intro E _ _ _ H D l
  refine ⟨fun {S S'} s o f s' hs => ?_, fun {S S' S''} s s' s'' o o' o'' f g m =>
    ⟨fun n => ObjComp.objMap_comp m n, fun k => ObjComp.objMap_cancel m k⟩⟩
  exact obj_pull E H D l (KA l) (KA l) (baseKA l) (baseKA l) (RingHom.id _) _ S' _ s' f rfl rfl
    (hs.symm.trans ((Category.comp_id _).symm.trans (congrArg (s' ≫ ·) (Spec.map_id _).symm))) o

end GlobalTheory.UCanon
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShimuraObjectPullbackCompCancelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shimuraObject_pullback_comp_cancel : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}, (∀ {S S' : Scheme.{0}} (s : S ⟶ Sp (KA l)) (o : Obj D l (baseKA l) s) (f : S' ⟶ S) (s' : S' ⟶ Sp (KA l)), s' = f ≫ s → ∃ o' : Obj D l (baseKA l) s', Nonempty (ObjMap o' o f)) ∧ (∀ {S S' S'' : Scheme.{0}} (s : S ⟶ Sp (KA l)) (s' : S' ⟶ Sp (KA l)) (s'' : S'' ⟶ Sp (KA l)) (o : Obj D l (baseKA l) s) (o' : Obj D l (baseKA l) s') (o'' : Obj D l (baseKA l) s'') (f : S' ⟶ S) (g : S'' ⟶ S') (m : ObjMap o' o f), (∀ n : ObjMap o'' o' g, ∃ k : ObjMap o'' o (g ≫ f), k.toSABMap.φ = n.toSABMap.φ ≫ m.toSABMap.φ) ∧ ∀ k : ObjMap o'' o (g ≫ f), ∃ n : ObjMap o'' o' g, k.toSABMap.φ = n.toSABMap.φ ≫ m.toSABMap.φ) := by
  first | exact @GlobalTheory.UCanon.obj_pull_comp_cancel | exact GlobalTheory.UCanon.obj_pull_comp_cancel | (intros; apply GlobalTheory.UCanon.obj_pull_comp_cancel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsPolarisationBundleLift
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsPolarisationBundleLift
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.UPel.HT.PolLift
open GlobalTheory.AbDual GlobalTheory.CechPic

theorem lbIso_symm {X : Scheme.{0}} {P Q : LB X} (hP : P.IsLB) (hQ : Q.IsLB) (e : LBIso P Q) : LBIso Q P :=
  (cls_eq_iff hQ hP).1 ((cls_eq_iff hP hQ).2 e).symm

theorem gen_comp {X Y Z : Scheme.{0}} {P : LB X} (hP : P.IsLB) (f : Y ⟶ X) (g : Z ⟶ Y)
    (h : ∃ t : (P.pull f).Gen, t.IsGen) : ∃ t : (P.pull (g ≫ f)).Gen, t.IsGen := by
  refine (cls_eq_zero_iff (pull_isLB hP _)).1 ?_
  rw [cls_pull hP, pull_comp, ← cls_pull hP _ (pull_isLB hP _), (cls_eq_zero_iff (pull_isLB hP _)).2 h, map_zero]

theorem gen_pull_pull {X Y Z : Scheme.{0}} {P : LB X} (hP : P.IsLB) (a : Y ⟶ X) (x : Z ⟶ Y)
    (h : ∃ t : (P.pull (x ≫ a)).Gen, t.IsGen) : ∃ t : ((P.pull a).pull x).Gen, t.IsGen := by
  refine (cls_eq_zero_iff (pull_isLB (pull_isLB hP _) _)).1 ?_
  rw [cls_pull (pull_isLB hP _), cls_pull hP, ← pull_comp, ← cls_pull hP _ (pull_isLB hP _)]
  exact (cls_eq_zero_iff (pull_isLB hP _)).2 h

theorem gen_left {S : Scheme.{0}} {A : Over S} [GrpObj A] (P : LB (A ⊗ A).left) (hP : P.IsLB) (u : A ⟶ A) [IsMonHom u]
    (h₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen)
    (h₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) :
    (∃ t : ((P.pull (lift (fst A A ≫ u) (snd A A)).left).pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) ∧
    (∃ t : ((P.pull (lift (fst A A ≫ u) (snd A A)).left).pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) := by
  refine ⟨gen_pull_pull hP _ _ ?_, gen_pull_pull hP _ _ ?_⟩
  · rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd, MonObj.one_comp]
    exact h₁
  · have e : lift (𝟙 A) (1 : A ⟶ A) ≫ lift (fst A A ≫ u) (snd A A) = u ≫ lift (𝟙 A) (1 : A ⟶ A) := by
      rw [comp_lift, lift_fst_assoc, lift_snd, comp_lift, Category.id_comp, Category.comp_id, MonObj.comp_one]
    rw [← Over.comp_left, e, Over.comp_left]
    exact gen_comp hP _ _ h₂

theorem sq_left {S S' : Scheme.{0}} {A₀ : Over S'} {A : Over S} [GrpObj A₀] [GrpObj A] {i : A₀.left ⟶ A.left}
    {l : (A₀ ⊗ A₀).left ⟶ (A ⊗ A).left} (l₁ : l ≫ (fst A A).left = (fst A₀ A₀).left ≫ i)
    (l₂ : l ≫ (snd A A).left = (snd A₀ A₀).left ≫ i) (u₀ : A₀ ⟶ A₀) (u : A ⟶ A) (w : u₀.left ≫ i = i ≫ u.left) :
    (lift (fst A₀ A₀ ≫ u₀) (snd A₀ A₀)).left ≫ l = l ≫ (lift (fst A A ≫ u) (snd A A)).left := by
  apply GlobalTheory.AbDual.left_ext
  · rw [Category.assoc, l₁, Category.assoc, GlobalTheory.AbDual.lift_left_fst, ← Category.assoc, GlobalTheory.AbDual.lift_left_fst,
      Over.comp_left, Over.comp_left, Category.assoc, w, ← Category.assoc, ← l₁, Category.assoc]
  · rw [Category.assoc, l₂, Category.assoc, GlobalTheory.AbDual.lift_left_snd, ← Category.assoc, GlobalTheory.AbDual.lift_left_snd, l₂]

theorem exists_pol_lift : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)), ∀ (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A] (i : o₀.A.left ⟶ A.left) (h : IsGrpPullback o₀.A A (spMap π) i), IsAbelianScheme A → ∀ (act : GlobalTheory.UPel.HT.OActN D.O A), (∀ c, (o₀.act.act c).left ≫ i = i ≫ (act.act c).left) → (∀ φ : Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C, GlobalTheory.AbDual.IsCorrForm (divided₂ hsq) (spMap π) o₀.A o₀.A o₀.P φ → ∀ x ∈ liftFil (divided₂ hsq) h, ∀ y ∈ liftFil (divided₂ hsq) h, φ x y = 0) → ∃ (P : LB (G2 A).left) (φ₂ : (G2 o₀.A).left ⟶ (G2 A).left), P.IsLB ∧ (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) ∧ (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) ∧ LBIso P (P.pull (lift (snd A A) (fst A A)).left) ∧ Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) ∧ (∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over (Sp C)) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ e = 1) ∧ (∀ c : D.O, LBIso (P.pull (lift (fst A A ≫ act.act c) (snd A A)).left) (P.pull (lift (fst A A) (snd A A ≫ act.act (D.star c).unop)).left)) ∧ IsSquare i φ₂ ∧ LBIso o₀.P (P.pull φ₂) := by
  intro p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR o₀ A _ _ i h hA act hact hiso
  haveI : Nontrivial C₀ := by
    refine ⟨⟨0, 1, fun h ↦ ?_⟩⟩
    have h1 : (1 : C) ∈ RingHom.ker π := by rw [RingHom.mem_ker, map_one]; exact h.symm
    have h2 : (1 : C) ∈ RingHom.ker π ^ 2 := by
      rw [pow_two]; simpa using Ideal.mul_mem_mul h1 h1
    rw [hsq] at h2
    exact one_ne_zero ((Submodule.mem_bot C).1 h2)
  let κ := divided₂ hsq
  have hκ : IsNilDP κ := isDPNilpotent_squareZero hsq
  have ADR : GlobalTheory.Published.AbelianDeRham := GlobalTheory.abelianDeRham
  have ADC : GlobalTheory.Published.AbelianDualCrystal := GlobalTheory.abelianDualCrystal
  have GD : GlobalTheory.Published.GrothendieckDeformation :=
    GlobalTheory.Published.grothendieckDeformation_of_lifting GlobalTheory.abelianDeRham GlobalTheory.abelianScheme_hom_lifting_nilpotent_dividedPowers
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim C A hA
  obtain ⟨l, l₁, l₂⟩ := exists_prod_pullback h h
  have hsq2 : Geo.Tor.IsSquare i l := ⟨l₁, l₂⟩
  have C' := GlobalTheory.Published.AbelianDualCrystal.cupSquare_crys_prod ADR.1 ADC.2 hκ hπ rfl hA hg hA hg h h
  obtain ⟨φ₀, hφ₀⟩ := exists_isCorrForm C' o₀.isLB o₀.rig₁ o₀.rig₂
  have hΔ₀ : (o₀.P.pull (lift (𝟙 o₀.A) (𝟙 o₀.A)).left).IsLB := pull_isLB o₀.isLB _
  obtain ⟨P, hP, t₁, t₂, -, -, eP⟩ := GlobalTheory.BirigidLift.exists_lift GD ADR ADC hκ hπ rfl hA hg hA hg h h l₁ l₂
    hΔ₀ o₀.ample hΔ₀ o₀.ample o₀.isLB o₀.rig₁ o₀.rig₂ hφ₀ (hiso φ₀ hφ₀)
  have wΔ : (lift (𝟙 o₀.A) (𝟙 o₀.A)).left ≫ l = i ≫ (lift (𝟙 A) (𝟙 A)).left := by
    apply GlobalTheory.AbDual.left_ext
    · rw [Category.assoc, l₁, Category.assoc, GlobalTheory.AbDual.lift_left_fst, ← Category.assoc, GlobalTheory.AbDual.lift_left_fst]
      simp
    · rw [Category.assoc, l₂, Category.assoc, GlobalTheory.AbDual.lift_left_snd, ← Category.assoc, GlobalTheory.AbDual.lift_left_snd]
      simp
  have hL : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have aL : Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) := by
    haveI := hA.smooth
    exact GlobalTheory.T.relAmple_lift_of_nilpotentDividedPowers_thickening C C₀ (RingHom.ker π) κ hκ π hπ rfl A o₀.A i h.1 inferInstance _ _
      hL hΔ₀ (GlobalTheory.RMDeform.lbIso_pull_square hP o₀.isLB eP _ _ i wΔ) o₀.ample
  have symm := GlobalTheory.T.birigidified_lift_symmetric_of_symmetric_reduction GD ADC C C₀ (RingHom.ker π) κ hκ π hπ rfl g o₀.A A i h hA hg l hsq2
    _ hL aL o₀.P o₀.isLB o₀.symm P hP t₁ t₂ eP
  have ros : ∀ c : D.O, LBIso (P.pull (lift (fst A A ≫ act.act c) (snd A A)).left)
      (P.pull (lift (fst A A) (snd A A ≫ act.act (D.star c).unop)).left) := by
    intro c
    haveI := o₀.act.hom c
    haveI := act.hom c
    haveI := o₀.act.hom (D.star c).unop
    haveI := act.hom (D.star c).unop
    have hQ := pull_isLB hP (lift (fst A A ≫ act.act c) (snd A A)).left
    have hQ₀ := pull_isLB o₀.isLB (lift (fst o₀.A o₀.A ≫ o₀.act.act c) (snd o₀.A o₀.A)).left
    obtain ⟨q₁, q₂⟩ := gen_left P hP (act.act c) t₁ t₂
    have eQ : LBIso ((P.pull (lift (fst A A ≫ act.act c) (snd A A)).left).pull l)
        (o₀.P.pull (lift (fst o₀.A o₀.A ≫ o₀.act.act c) (snd o₀.A o₀.A)).left) :=
      lbIso_symm hQ₀ (pull_isLB hQ _) (GlobalTheory.RMDeform.lbIso_pull_square hP o₀.isLB eP _ _ l
        (sq_left l₁ l₂ _ _ (hact c)))
    exact GlobalTheory.T.birigidified_lift_pullback_one_prod_endomorphism GD ADC C C₀ (RingHom.ker π) κ hκ π hπ rfl g o₀.A A i h hA hg l hsq2 _ hL aL
      (o₀.act.act (D.star c).unop) (act.act (D.star c).unop) (hact _) o₀.P _ o₀.isLB hQ₀ (o₀.rosati c)
      P _ hP hQ t₁ t₂ q₁ q₂ eP eQ
  have ker : ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over (Sp C)) (x : T ⟶ A),
      (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ e = 1 := by
    obtain ⟨e, he, H⟩ := o₀.kerP
    have hu : IsUnit (e : C) := by
      have := (b.unit e he).map tR
      simpa using this
    exact ⟨e, he, GlobalTheory.T.lifted_polarisation_kernel_killed_of_unit C C₀ π hπ hsq o₀.A A i h hA l hsq2 o₀.P P o₀.isLB hP t₁ t₂ symm aL eP e hu H⟩
  exact ⟨P, l, hP, t₁, t₂, symm, aL, ker, ros, hsq2, lbIso_symm (pull_isLB hP l) o₀.isLB eP⟩

end GlobalTheory.UPel.HT.PolLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsPolarisationBundleLiftStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_exists_polarisation_bundle_lift : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)), ∀ (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A] (i : o₀.A.left ⟶ A.left) (h : IsGrpPullback o₀.A A (spMap π) i), IsAbelianScheme A → ∀ (act : GlobalTheory.UPel.HT.OActN D.O A), (∀ c, (o₀.act.act c).left ≫ i = i ≫ (act.act c).left) → (∀ φ : Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C, GlobalTheory.AbDual.IsCorrForm (divided₂ hsq) (spMap π) o₀.A o₀.A o₀.P φ → ∀ x ∈ liftFil (divided₂ hsq) h, ∀ y ∈ liftFil (divided₂ hsq) h, φ x y = 0) → ∃ (P : LB (G2 A).left) (φ₂ : (G2 o₀.A).left ⟶ (G2 A).left), P.IsLB ∧ (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) ∧ (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) ∧ LBIso P (P.pull (lift (snd A A) (fst A A)).left) ∧ Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) ∧ (∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over (Sp C)) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ e = 1) ∧ (∀ c : D.O, LBIso (P.pull (lift (fst A A ≫ act.act c) (snd A A)).left) (P.pull (lift (fst A A) (snd A A ≫ act.act (D.star c).unop)).left)) ∧ IsSquare i φ₂ ∧ LBIso o₀.P (P.pull φ₂) := by
  first | exact @GlobalTheory.UPel.HT.PolLift.exists_pol_lift | exact GlobalTheory.UPel.HT.PolLift.exists_pol_lift | (intros; apply GlobalTheory.UPel.HT.PolLift.exists_pol_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSabMapOfGrpPullbackRespectingActionBundle
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSabMapOfGrpPullbackRespectingActionBundle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon.TriplePull

theorem exists_sabMap_of_isProper : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}} (t' : SAB H S') (t : SAB H S) (f : S' ⟶ S) (π : t'.G.left ⟶ t.G.left), IsProper t.G.hom → IsGrpPullback t'.G t.G f π → (∀ a, (t'.act.act a).left ≫ π = π ≫ (t.act.act a).left) → LBIso t'.PP.L (t.PP.L.pull π) → ∃ m : SABMap t' t f, m.φ = π := by
  intro E _ _ _ H S S' t' t f π hp gp hact h
  have hp' : IsProper t'.G.hom := MorphismProperty.of_isPullback (P := @IsProper) gp.1 hp
  exact GlobalTheory.CartTriple.exists_tripleMap GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 E H S S' f t' t π
    ⟨t'.semi.comm, t'.semi.smooth, hp', t'.semi.geomConnected⟩ gp hact h

end GlobalTheory.UCanon.TriplePull
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSabMapOfGrpPullbackRespectingActionBundleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sabMap_of_grpPullback_respecting_action_bundle : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}} (t' : SAB H S') (t : SAB H S) (f : S' ⟶ S) (π : t'.G.left ⟶ t.G.left), IsProper t.G.hom → IsGrpPullback t'.G t.G f π → (∀ a, (t'.act.act a).left ≫ π = π ≫ (t.act.act a).left) → LBIso t'.PP.L (t.PP.L.pull π) → ∃ m : SABMap t' t f, m.φ = π := by
  first | exact @GlobalTheory.UCanon.TriplePull.exists_sabMap_of_isProper | exact GlobalTheory.UCanon.TriplePull.exists_sabMap_of_isProper | (intros; apply GlobalTheory.UCanon.TriplePull.exists_sabMap_of_isProper <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteEtaleSurjectiveOfIsQuasiInv
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES

theorem isFinite_etale_surjective_of_isQuasiInv : ∀ (Y : Scheme.{0}) (A B : Over Y) [GrpObj A] [GrpObj B] (k : ℕ) (ψ : A ⟶ B) (ψ' : B ⟶ A), IsAbelianScheme A → IsAbelianScheme B → IsUnit (k : Γ(Y, ⊤)) → IsQuasiInv k ψ ψ' → IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left := by
  intro Y A B _ _ k ψ ψ' hA hB hk hq
  obtain ⟨-, -, h1, h2⟩ := hq
  obtain ⟨⟨hAf, hAe⟩, -⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion A (hG := hA) hk
  obtain ⟨⟨-, hBe⟩, -⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion B (hG := hB) hk
  rw [GlobalTheory.GrpTangent.mulN_eq_pow, ← h1, Over.comp_left] at hAf hAe
  rw [GlobalTheory.GrpTangent.mulN_eq_pow, ← h2, Over.comp_left] at hBe
  haveI := hB.proper
  haveI : IsSeparated (ψ'.left ≫ A.hom) := by rw [Over.w]; infer_instance
  haveI := IsSeparated.of_comp ψ'.left A.hom
  haveI := FormallyUnramified.of_comp ψ'.left ψ.left
  haveI := locallyOfFiniteType_of_comp ψ'.left ψ.left
  refine ⟨IsFinite.of_comp ψ.left ψ'.left, Etale.of_comp ψ.left ψ'.left, ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · refine ⟨fun b => ?_⟩
    have hu := hk.map (Y.evaluation ⊤ (B.hom.base b) trivial).hom
    rw [map_natCast, Nat.cast_zero] at hu
    exact absurd hu not_isUnit_zero
  · obtain ⟨-, hs, -⟩ := GlobalTheory.UPel.HT.SiegUniqBase.flat_surjective_qc_pow Y B hB k hk0
    rw [← h2, Over.comp_left] at hs
    exact Surjective.of_comp ψ'.left ψ.left

end GlobalTheory.UPel.HT.ES
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComesFromTautBaseOfRescaledPullbackMonomial
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComesFromTautBaseOfRescaledPullbackMonomial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon GlobalTheory.PolDeg GlobalTheory.TInj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TInj

set_option synthInstance.maxHeartbeats 400000 in
theorem from_rescale_pull : ∀ {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (T : TautBase o W) (n : ℕ) (D₀ : DegPre W), D₀.PsiEven → D₀.TauBimult → (∀ y, PsiUnitOn D₀ y Set.univ) → ∀ (ib : D₀.X ≃+ (Fin T.r → ℤ)) (β : D₀.P.A.left ⟶ T.B.left) (ββ : (G2 D₀.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D₀.P.A D₀.P.L) ((abelian₂ T.B T.M.L).pull ββ)), From T (RingHom.id W) (fun _ : Empty => (1 : W)) (fun _ => 0) n D₀ ib β ββ w → ∀ (V : Type) [CommRing V] [IsDomain V] (iw : W →+* V), Function.Injective iw → ∀ (Q : DegPre V) (g : Q.X → (FractionRing V)ˣ) (hD : IsPullDeg iw D₀ (rescale Q g)) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (e : Q.X ≃+ (Fin T.r → ℤ)), (∀ y : Q.X, e y = ib (hD.xe y)) → (∀ a a' : Q.X, (((g (a + a'))⁻¹ * g a * g a' : (FractionRing V)ˣ) : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s i) ^ ((n : ℤ) * ε i (e a) (e a'))) → ∃ (β' : Q.P.A.left ⟶ T.B.left) (ββ' : (G2 Q.P.A).left ⟶ (G2 T.B).left) (w' : LB.Iso (abelian₂ Q.P.A Q.P.L) ((abelian₂ T.B T.M.L).pull ββ')), From T iw s ε n Q e β' ββ' w' := by
  intro o W _ _ _ _ T n D₀ hev hbi hun ib β ββ w hF V _ _ iw hiw Q g hD I _ s ε e he hg
  haveI : IsEmpty Empty := Empty.instIsEmpty
  have hin : ∀ χ, D₀.PsiIn χ ⊤ := fun χ j U hU hle h => by
    obtain ⟨r, -, hr⟩ := hun χ j U hU (Set.subset_univ _) hle h
    exact ⟨r, by rw [Ideal.map_top]; trivial, hr⟩
  let D₁ : DegData W ⊤ :=
    { toPre := D₀
      psi_even := hev
      tau_bimult := hbi
      psi_pos := fun χ _ => hin χ
      psi_tendsto := fun m => by
        rw [Ideal.top_pow]
        exact Set.finite_empty.subset fun χ hχ => hχ (hin χ) }
  obtain ⟨ββ', w', pb, sq, gen, hc, hτ⟩ :=
    from_pull T (fun _ : Empty => 0) n W V ⊤ D₁ (RingHom.id W) (fun _ => 1) ib β ββ w iw (rescale Q g) hD hiw hF
  rw [RingHom.comp_id] at pb hc hτ
  refine ⟨_, ββ', w', pb, sq, gen, fun a => ?_, fun a b => ?_⟩
  · rw [he a]; exact hc a
  · obtain ⟨k, hk, hv⟩ := hτ a b
    have hk1 : k = 1 := Units.ext (by rw [hk]; simp)
    refine ⟨_, hg a b, fun z J J' hJ hJ' => ?_⟩
    have H := hv z J J' hJ hJ'
    have E := rescale_tau_val Q g a b hJ'
    have H' := E.symm.trans H
    rw [hk1] at H'
    rw [he a, he b]
    have aux : ∀ {G : Type} [CommGroup G] (x y u t p : G), x * y⁻¹ * u⁻¹ * t = 1 * p → t = x⁻¹ * y * u * p := by
      intro G _ x y u t p h
      rw [_root_.one_mul] at h
      rw [← h, ← _root_.mul_assoc]
      have h1 : x⁻¹ * y * u * (x * y⁻¹ * u⁻¹) = (x⁻¹ * x) * (y * y⁻¹) * (u * u⁻¹) := by ac_rfl
      rw [h1]
      simp
    simp only [unitOn, map_mul, map_inv, map_one] at H' ⊢
    exact aux _ _ _ _ _ H'

end GlobalTheory.TInj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComesFromTautBaseOfRescaledPullbackMonomialStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon GlobalTheory.PolDeg GlobalTheory.TInj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comesFromTautBase_of_rescaled_pullback_monomial : ∀ {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (T : TautBase o W) (n : ℕ) (D₀ : DegPre W), D₀.PsiEven → D₀.TauBimult → (∀ y, PsiUnitOn D₀ y Set.univ) → ∀ (ib : D₀.X ≃+ (Fin T.r → ℤ)) (β : D₀.P.A.left ⟶ T.B.left) (ββ : (G2 D₀.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D₀.P.A D₀.P.L) ((abelian₂ T.B T.M.L).pull ββ)), From T (RingHom.id W) (fun _ : Empty => (1 : W)) (fun _ => 0) n D₀ ib β ββ w → ∀ (V : Type) [CommRing V] [IsDomain V] (iw : W →+* V), Function.Injective iw → ∀ (Q : DegPre V) (g : Q.X → (FractionRing V)ˣ) (hD : IsPullDeg iw D₀ (rescale Q g)) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (e : Q.X ≃+ (Fin T.r → ℤ)), (∀ y : Q.X, e y = ib (hD.xe y)) → (∀ a a' : Q.X, (((g (a + a'))⁻¹ * g a * g a' : (FractionRing V)ˣ) : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s i) ^ ((n : ℤ) * ε i (e a) (e a'))) → ∃ (β' : Q.P.A.left ⟶ T.B.left) (ββ' : (G2 Q.P.A).left ⟶ (G2 T.B).left) (w' : LB.Iso (abelian₂ Q.P.A Q.P.L) ((abelian₂ T.B T.M.L).pull ββ')), From T iw s ε n Q e β' ββ' w' := by
  first | exact @GlobalTheory.TInj.from_rescale_pull | exact GlobalTheory.TInj.from_rescale_pull | (intros; apply GlobalTheory.TInj.from_rescale_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationIffReductionGluedFilHtObject
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationIffReductionGluedFilHtObject
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTGlue

theorem red_pull_constMorV_pull {k : Type} [Field k] {d : ℕ} (A₀ : Over (Sp k)) [GrpObj A₀]
    (c : prim (dp0 k) (𝟙 _) A₀) :
    (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) rfl A₀).pull
      ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c) = c := by
  rw [GrpMor.pull_pull _ _ (homMor (dp0 k) (𝟙 _) (𝟙 A₀)) (fun r => rfl) (by simp)]
  exact Subtype.ext (IsMor.pullCohomologyOne_id _ c.1)

theorem eq_of_liftSemi_surj {K C : Type} [Field K] [CommRing C] [Algebra K C] {M M' : Type*} [AddCommGroup M]
    [Module K M] [AddCommGroup M'] [Module C M'] (P : M →ₛₗ[algebraMap K C] M')
    (hP : Function.Surjective (liftSemi P)) (π : C →+* K)
    (Q : M' →ₛₗ[π] M) (e : M' →ₗ[C] C) (y : M →ₗ[K] K) (hQ : ∀ c, Q (P c) = c)
    (he : ∀ c, π (e (P c)) = y c) (c' : M') : y (Q c') = π (e c') := by
  obtain ⟨u, rfl⟩ := hP c'
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hu, hv]
  | tmul r c =>
    rw [liftSemi_tmul, LinearMap.map_smulₛₗ, hQ, map_smul, map_smul, smul_eq_mul, smul_eq_mul, map_mul, he]

theorem corr_of_fst {k : Type} [Field k] {d : ℕ} (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀)
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀)
    (y : HdR A₀) (hc : ∀ c, (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom
      (e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c)) = y c) :
    (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) rfl A₀).Corr e y :=
  eq_of_liftSemi_surj _ (GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k (Fin d → k) A₀ hA (GlobalTheory.FODef.sqZero k (Fin d → k))
    (GlobalTheory.FODef.constMorV k (Fin d → k) A₀)).2 _ _ e y (red_pull_constMorV_pull A₀) hc

theorem fil_iff_red_glueFil : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), (∀ j, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) (f j)) → (∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ e ∈ (GlobalTheory.HTGlue.glueFil o₀.A f), (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) rfl o₀.A).Corr e y) := by
  intro p _ D R _ b N _ _ k _ _ t o₀ β _ φ _ d f _ y
  constructor
  · intro hy
    obtain ⟨e, he, hc⟩ := exists_mem_glueFil o₀.A o₀.ab f hy
    refine ⟨e, he, corr_of_fst o₀.A o₀.ab e y fun c => ?_⟩
    rw [hc c]
    simp
  · rintro ⟨e, ⟨x, hx, z, hz, he⟩, hcorr⟩
    have hxy : y = x := LinearMap.ext fun c => by
      have h1 := hcorr ((GlobalTheory.FODef.constMorV k (Fin d → k) o₀.A).pull c)
      rw [red_pull_constMorV_pull, he c] at h1
      simpa using h1
    exact hxy ▸ hx

end GlobalTheory.HTGlue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationIffReductionGluedFilHtObjectStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_hodgeFiltration_iff_reduction_gluedFil_htObject : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), (∀ j, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) (f j)) → (∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ e ∈ (GlobalTheory.HTGlue.glueFil o₀.A f), (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) rfl o₀.A).Corr e y) := by
  first | exact @GlobalTheory.HTGlue.fil_iff_red_glueFil | exact GlobalTheory.HTGlue.fil_iff_red_glueFil | (intros; apply GlobalTheory.HTGlue.fil_iff_red_glueFil <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormBigOfNonvanishing
open Finset
open GlobalTheory.SqTop GlobalTheory.FunObj.SqNum
open GlobalTheory.NormSum (Pair)
open GlobalTheory.CMVal (IsHeckeL)

namespace GlobalTheory.NormBigProof

theorem squareBottomHalfRankSum_le_halfRank (D : Formalism.BasicNotions.D7) (i j : ℕ) : h0 D i j ≤ halfRank D i j := by
  unfold h0 halfRank botBig botSmall
  exact Nat.div_le_div_right (Nat.add_le_add (Nat.sub_le _ _) (Nat.sub_le _ _))

end GlobalTheory.NormBigProof
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleNonzeroPeriod
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KerFin

theorem gbig_comb {Q1 Q2 Q : GlobalTheory.SqTop.GP} (h1 : GlobalTheory.SqTop.GBig Q1) (h2 : GlobalTheory.SqTop.GBig Q2)
    (h : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Q1 G μ₀ C x b → Q2 G μ₀ C x b → Q G μ₀ C x b) : GlobalTheory.SqTop.GBig Q := by
  obtain ⟨A1, h1⟩ := h1
  obtain ⟨A2, h2⟩ := h2
  refine ⟨max A1 A2, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, h1⟩ := h1 ε CF (le_of_max_le_left hCF)
  obtain ⟨C2, x2, h2⟩ := h2 ε CF (le_of_max_le_right hCF)
  refine ⟨max C1 C2, max x1 x2, fun C hC D large₂ he hx hR T Lc μ₀ hL G => h G μ₀ C _ _
    (h1 C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) hR T Lc μ₀ hL G)
    (h2 C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) hR T Lc μ₀ hL G)⟩

end GlobalTheory.KerFin
end
end
