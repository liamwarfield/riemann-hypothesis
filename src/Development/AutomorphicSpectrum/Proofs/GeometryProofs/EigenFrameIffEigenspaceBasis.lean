module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackCorrespondence
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyCoordIdeal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.BtExistsBc
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGeneric
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIntegralPivotDecomposition
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorIff

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFrameIffEigenspaceBasis
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFrameIffEigenspaceBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.LieEigFrame

variable {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G] {x : Sp R ⟶ S} {Em : Type}
  [AddCommGroup Em] [Module R Em]

theorem isComb_pt_iff (M : LieModel G x Em) {n : ℕ} (b : Fin n → Em) (cf : Fin n → R) (w : epsAt x ⟶ G) :
    IsComb cf (fun i => M.pt (b i)) w ↔ w = M.pt (∑ i, cf i • b i) := by
  have hsum : M.pt (∑ i, cf i • b i) = (List.ofFn fun i => M.pt (cf i • b i)).prod :=
    GlobalTheory.CompanionTheory.Ar.CombEig.pt_sum M fun i => cf i • b i
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hue : u = fun i => M.pt (cf i • b i) :=
      funext fun i => Over.OverMorphism.ext (by rw [hu i, M.smul])
    rw [hsum, hue]
  · rintro rfl
    exact ⟨fun i => M.pt (cf i • b i), fun i => M.smul _ _, hsum⟩

theorem isEigVec_pt_iff {Oe : Type} [CommRing Oe] (M : LieModel G x Em) (act : OAct Oe G)
    {ρ : Oe →+* Module.End R Em} (τ : Oe →+* R) (hρ : M.IsActOf act.act ρ) (e : Em) :
    IsEigVec act x τ (M.pt e) ↔ e ∈ eigSp ρ τ := by
  have hmem : e ∈ eigSp ρ τ ↔ ∀ a, ρ a e = τ a • e := by
    simp [eigSp, Submodule.mem_iInf, sub_eq_zero]
  rw [hmem]
  constructor
  · intro h a
    exact M.inj (Over.OverMorphism.ext (by rw [hρ a e, M.smul]; exact h.2 a))
  · intro h
    exact ⟨M.tan e, fun a => by rw [← hρ a e, h a, M.smul]⟩

theorem isEigFrame_pt_iff : ∀ (S : Scheme.{0}) (R : Type) [CommRing R] (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Sp R ⟶ S) (Em : Type)
    [AddCommGroup Em] [Module R Em] (M : LieModel G x Em) (Oe : Type) [CommRing Oe] (act : OAct Oe G)
    (ρ : Oe →+* Module.End R Em) (τ : Oe →+* R) (n : ℕ) (b : Fin n → Em), M.IsActOf act.act ρ →
    (IsEigFrame act x τ (fun i => M.pt (b i)) ↔
      (∀ i, b i ∈ eigSp ρ τ) ∧ ∀ e ∈ eigSp ρ τ, ∃! cf : Fin n → R, e = ∑ i, cf i • b i) := by
  intro S R _ G _ _ x Em _ _ M Oe _ act ρ τ n b hρ
  have eig := isEigVec_pt_iff M act τ hρ
  have key := isComb_pt_iff M b
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => (eig _).1 (h1 i), fun e he => ?_⟩
    obtain ⟨c, hc, hu⟩ := h2 (M.pt e) ((eig e).2 he)
    exact ⟨c, M.inj ((key c _).1 hc), fun c' hc' => hu c' ((key c' _).2 (congrArg M.pt hc'))⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => (eig _).2 (h1 i), fun w hw => ?_⟩
    obtain ⟨e, rfl⟩ := M.onto w hw.1
    obtain ⟨c, hc, hu⟩ := h2 e ((eig e).1 hw)
    exact ⟨c, (key c _).2 (congrArg M.pt hc), fun c' hc' => hu c' (M.inj ((key c' _).1 hc'))⟩

end GlobalTheory.CompanionTheory.Ar.Flat.LieEigFrame
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFrameIffEigenspaceBasisStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_frame_iff_eigenspace_basis : ∀ (S : Scheme.{0}) (R : Type) [CommRing R] (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Sp R ⟶ S) (Em : Type)
    [AddCommGroup Em] [Module R Em] (M : LieModel G x Em) (Oe : Type) [CommRing Oe] (act : OAct Oe G)
    (ρ : Oe →+* Module.End R Em) (τ : Oe →+* R) (n : ℕ) (b : Fin n → Em), M.IsActOf act.act ρ →
    (IsEigFrame act x τ (fun i => M.pt (b i)) ↔
      (∀ i, b i ∈ eigSp ρ τ) ∧ ∀ e ∈ eigSp ρ τ, ∃! cf : Fin n → R, e = ∑ i, cf i • b i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.LieEigFrame.isEigFrame_pt_iff | exact GlobalTheory.CompanionTheory.Ar.Flat.LieEigFrame.isEigFrame_pt_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.LieEigFrame.isEigFrame_pt_iff <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SqMap
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FrGauge

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Conj Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

section Values

variable {X Y F : Scheme.{0}} {L : LB X} {M : LB Y} {f : F ⟶ X} {g : F ⟶ Y}

def wv (w : LB.Iso (L.pull f) (M.pull g)) {Z : Scheme.{0}} (ψ : Z ⟶ F) (z : Z) (JL : (Z ⟶ X) → L.ι)
    (JM : (Z ⟶ Y) → M.ι) : (Z.presheaf.stalk z)ˣ :=
  gm ψ z _ (w.s (fun _ => JM (ψ ≫ g), fun _ => JL (ψ ≫ f)))

def Tr (w : LB.Iso (L.pull f) (M.pull g)) {Y' : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y' ⟶ F))
    (φL : K → (Y' ⟶ X)) (φM : K → (Y' ⟶ Y)) (ε : K → ℤ) (c : LB.Gen (LB.LinComb L φL ε))
    (b : LB.Gen (LB.LinComb M φM ε)) (u : Γ(Y', ⊤)ˣ) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (JL : (Z ⟶ X) → L.ι) (JM : (Z ⟶ Y) → M.ι), Good L z JL → Good M z JM →
    val c r z JL * ∏ k, wv w (r ≫ φ k) z JL JM ^ ε k = gm r z ⊤ u * val b r z JM

end Values

section Series

variable {R : Type} [CommRing R] {d d' : ℕ}

def linQ (Qs : Fin d' → PS R 1 d) : Matrix (Fin d') (Fin d) R :=
  fun i l => MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), l) 1) (Qs i)

def subQ (Qs : Fin d' → PS R 1 d) (f : PS R 2 d') : PS R 2 d :=
  MvPowerSeries.subst (fun p : Fin 2 × Fin d' => ev (n := 2) ![pt R d p.1] (Qs p.2)) f

def sub1 (Qs : Fin d' → PS R 1 d) (m : ℕ) : Jet R (Fin 1 × Fin d') m →ₐ[R] Jet R (Fin 1 × Fin d) m :=
  jetSubstP m fun p : Fin 1 × Fin d' => psTrunc m (Qs p.2)

def sub2 (Qs : Fin d' → PS R 1 d) (m : ℕ) : Jet R (Fin 2 × Fin d') m →ₐ[R] Jet R (Fin 2 × Fin d) m :=
  jetSubstP m fun p : Fin 2 × Fin d' => psIn d m ![p.1] (Qs p.2)

end Series

section Fibre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
  {k : Type} [Field k] (x : Sp k ⟶ X)

abbrev GF : Over (Sp k) := (Over.pullback x).obj t.G

def toF {T : Over (Sp k)} (a : T.left ⟶ t.G.left) (h : a ≫ t.G.hom = T.hom ≫ x) : T ⟶ GF t x :=
  Over.homMk (pullback.lift a T.hom h) (pullback.lift_snd _ _ _)

def fibPt {A : Type} [CommRing A] [Algebra k A] (y : overAt x A ⟶ t.G) : overAt (𝟙 (Sp k)) A ⟶ GF t x :=
  toF t x y.left (by simpa using Over.w y)

def cubeF {A : Type} [CommRing A] [Algebra k A] (xs : Fin 2 → (overAt x A ⟶ t.G)) (I : ULift (Finset (Fin 2))) :
    Sp A ⟶ (GF t x).left :=
  (fibPt t x (psum t.G xs I.down)).left

def sqPr (p : GF t x ⊗ GF t x ⟶ GF t x) : Over.mk ((GF t x ⊗ GF t x).hom ≫ x) ⟶ t.G :=
  Over.homMk (p.left ≫ pullback.fst t.G.hom x) (by
    have h : p.left ≫ pullback.snd t.G.hom x = (GF t x ⊗ GF t x).hom := Over.w p
    show (p.left ≫ pullback.fst t.G.hom x) ≫ t.G.hom = (GF t x ⊗ GF t x).hom ≫ x
    rw [Category.assoc, pullback.condition, ← Category.assoc, h])

def sqMap : (GF t x ⊗ GF t x).left ⟶ (t.G ⊗ t.G).left :=
  (lift (sqPr t x (fst _ _)) (sqPr t x (snd _ _))).left

def sqPt (a : t.G ⊗ t.G ⟶ t.G) : GF t x ⊗ GF t x ⟶ GF t x :=
  toF t x (sqMap t x ≫ a.left) (Over.w (lift (sqPr t x (fst _ _)) (sqPr t x (snd _ _)) ≫ a))

abbrev AdTy (t : SAB H X) (a : 𝓞 E) : Type :=
  LB.Gen (LB.LinComb t.PP.L
    (Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)])
      (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]))
    (Sum.elim (cε 2) fun I => -cε 2 I))

def adF (a : 𝓞 E) : ULift (Finset (Fin 2)) ⊕ ULift (Finset (Fin 2)) →
    ((GF t x ⊗ GF t x).left ⟶ (GF t x).left) :=
  Sum.elim (fun I => (sqPt t x (psum t.G ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)] I.down)).left)
    (fun I => (sqPt t x (psum t.G ![fst t.G t.G ≫ t.act.act a, snd t.G t.G] I.down)).left)

def ax0 : (GF t x).left ⟶ (GF t x ⊗ GF t x).left := (lift (1 : GF t x ⟶ GF t x) (𝟙 (GF t x))).left

def ax1 : (GF t x).left ⟶ (GF t x ⊗ GF t x).left := (lift (𝟙 (GF t x)) (1 : GF t x ⟶ GF t x)).left

def qq {t : SAB H X} {x : Sp k ⟶ X} (Q : AbQuot t x) : (GF t x ⊗ GF t x).left ⟶ (Q.tB.G ⊗ Q.tB.G).left :=
  (lift (fst (GF t x) (GF t x) ≫ Q.q) (snd (GF t x) (GF t x) ≫ Q.q)).left

end Fibre

section AdRel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
  {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)

def AdRel (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S)
    (e : ∀ m, FrTyG t x0 d x m) (a : 𝓞 E) (wL : AdTy t a) : Prop :=
  ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m (ad a) ∧
    LB.Gen.Corr t.PP.L _ _ _ _
      (LB.mulGen t.PP.L _ _ _ _
        (LB.pullGen t.PP.L _ _ wL (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left)
        (peG t x0 d x e m ![fun j => psIn d m ![0] (act a j), fun j => MvPolynomial.X ((1 : Fin 2), j)]))
      (scaleGenG t _ _ (unitΓ u)
        (peG t x0 d x e m ![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)]))

end AdRel

end GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsBaseChangeGroup
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsBaseChangeGroup
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem QFGroup.exists_isBaseChange_of_injective : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] (φ : R →+* R'), Function.Injective φ → ∃ (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ φ F :=
  @PositivityTheory.UnitarySelfGeneration.bt_exists_bc

end GlobalTheory.CompanionTheory.Ar.BT
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsBaseChangeGroupStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_base_change_group : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] (φ : R →+* R'), Function.Injective φ → ∃ (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ φ F := by
  exact @GlobalTheory.CompanionTheory.Ar.BT.QFGroup.exists_isBaseChange_of_injective
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointComponentLocalRing
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointComponentLocalRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

noncomputable def regAtEquivStalk {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (h : IsCptGen ξ) (q : Cpt ξ) : X.presheaf.stalk q.1 ≃+* regAt ξ q :=
  RingEquiv.ofBijective (genMap ξ q).rangeRestrict
    ⟨fun _ _ e => h.inj q (congrArg Subtype.val e), (genMap ξ q).rangeRestrict_surjective⟩

theorem isLocalRing_regAt : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → ∀ q : Cpt ξ, IsLocalRing (regAt ξ q) := by
  intro X Ω _ ξ h q
  exact (regAtEquivStalk h q).isLocalRing

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointComponentLocalRingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_point_component_local_ring : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → ∀ q : Cpt ξ, IsLocalRing (regAt ξ q) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.isLocalRing_regAt | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.isLocalRing_regAt | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.isLocalRing_regAt <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsCombTangentIffLinearSum
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsCombTangentIffLinearSum
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem isComb_lieModel_pt_iff : ∀ (S : Scheme.{0}) (R : Type) [CommRing R] (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Sp R ⟶ S) (Em : Type)
    [AddCommGroup Em] [Module R Em] (M : LieModel G x Em) (n : ℕ) (b : Fin n → Em) (cf : Fin n → R) (e : Em),
    IsComb cf (fun i => M.pt (b i)) (M.pt e) ↔ e = ∑ i, cf i • b i := by
  intro S R _ G _ _ x Em _ _ M n b cf e
  have hu : ∀ u : Fin n → (epsAt x ⟶ G),
      (∀ i, (u i).left = spMap (epsMul (cf i)) ≫ (M.pt (b i)).left) ↔ u = fun i => M.pt (cf i • b i) := by
    intro u
    constructor
    · intro h
      funext i
      exact Over.OverMorphism.ext ((h i).trans (M.smul _ _).symm)
    · rintro rfl i
      exact M.smul _ _
  have h0 : M.pt 0 = 1 := by
    have h := M.add 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
  have hsum : ∀ (m : ℕ) (f : Fin m → Em), M.pt (∑ i, f i) = (List.ofFn fun i => M.pt (f i)).prod := by
    intro m f
    induction m with
    | zero => rw [Finset.univ_eq_empty, Finset.sum_empty, List.ofFn_zero, List.prod_nil, h0]
    | succ m ih => rw [Fin.sum_univ_succ, List.ofFn_succ, List.prod_cons, M.add, ih]
  constructor
  · rintro ⟨u, hu1, hu2⟩
    rw [(hu u).1 hu1] at hu2
    apply M.inj
    rw [hu2]
    exact (hsum n (fun i => cf i • b i)).symm
  · intro he
    refine ⟨fun i => M.pt (cf i • b i), (hu _).2 rfl, ?_⟩
    rw [he]
    exact hsum n (fun i => cf i • b i)

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsCombTangentIffLinearSumStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.is_comb_tangent_iff_linear_sum : ∀ (S : Scheme.{0}) (R : Type) [CommRing R] (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Sp R ⟶ S) (Em : Type)
    [AddCommGroup Em] [Module R Em] (M : LieModel G x Em) (n : ℕ) (b : Fin n → Em) (cf : Fin n → R) (e : Em),
    IsComb cf (fun i => M.pt (b i)) (M.pt e) ↔ e = ∑ i, cf i • b i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.isComb_lieModel_pt_iff | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.isComb_lieModel_pt_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.isComb_lieModel_pt_iff <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericTrdegEqDimension
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericTrdegEqDimension
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CptTrdeg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped TensorProduct

theorem trdeg_residueField_of_isIntegral {K B : Type} [Field K] [CharZero K] [CommRing B] [Algebra K B]
    [Algebra.IsIntegral K B] (q : Ideal B) [q.IsPrime] :
    Algebra.trdeg ℤ q.ResidueField = Algebra.trdeg ℤ K := by
  have hcm : (Ideal.comap (algebraMap K B) q).IsMaximal :=
    Ideal.IsPrime.isMaximal' (Ideal.comap_isPrime _ _)
  have hmax : q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := K) q hcm
  have hs : Function.Surjective (IsScalarTower.toAlgHom K B q.ResidueField) :=
    Ideal.algebraMap_residueField_surjective q
  have : Algebra.IsIntegral K q.ResidueField := Algebra.IsIntegral.of_surjective _ hs
  have : CharZero q.ResidueField :=
    charZero_of_injective_algebraMap (algebraMap K q.ResidueField).injective
  have h0 : Algebra.trdeg K q.ResidueField = 0 := trdeg_eq_zero
  rw [← trdeg_add_eq ℤ K (A := q.ResidueField), h0, add_zero]

theorem trdeg_int_eq_of_ringEquiv {A B : Type} [CommRing A] [CommRing B] [Algebra ℤ A] [Algebra ℤ B] (e : A ≃+* B) :
    Algebra.trdeg ℤ A = Algebra.trdeg ℤ B :=
  (AlgEquiv.ofRingEquiv (f := e) (fun n => by simp [eq_intCast (algebraMap ℤ A), eq_intCast (algebraMap ℤ B)])).trdeg_eq

theorem residueFieldMap_bijective {X Y : Scheme.{0}} (f : X ⟶ Y) [SurjectiveOnStalks f] (x : X) :
    Function.Bijective (f.residueFieldMap x).hom := by
  refine ⟨RingHom.injective _, fun b => ?_⟩
  obtain ⟨c, rfl⟩ := X.residue_surjective x b
  obtain ⟨d, rfl⟩ := SurjectiveOnStalks.stalkMap_surjective f x c
  exact ⟨Y.residue (f x) d, congr($(Scheme.residue_residueFieldMap f x).hom d)⟩

theorem trdeg_residueField_of_fst {X : Scheme.{0}} {O F Ω₀ : Type} [CommRing O] [Field F] [Field Ω₀] [CharZero Ω₀]
    (s : X ⟶ Sp O) (β : O →+* F) (g₀ : O →+* Ω₀) (ξ₀ : Sp Ω₀ ⟶ X) (h₀ : IsCptGen ξ₀) (hs : ξ₀ ≫ s = spMap g₀)
    (hγ : Function.Injective g₀)
    (hF : letI := β.toAlgebra; ∀ u : F, ∃ a : O, a ≠ 0 ∧ _root_.IsIntegral O (a • u))
    {y : ↥(pullback s (spMap β))} (hy : pullback.fst s (spMap β) y = genPt ξ₀) :
    Algebra.trdeg ℤ ((pullback s (spMap β)).residueField y) = Algebra.trdeg ℤ Ω₀ := by
  letI := β.toAlgebra
  letI := g₀.toAlgebra
  have hsurj : SurjectiveOnStalks ξ₀ := by
    have : IsIso (Scheme.stalkClosedPointTo ξ₀) := (ConcreteCategory.isIso_iff_bijective _).2 h₀.bij
    rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ₀]
    infer_instance
  obtain ⟨z, rfl, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.fst s (spMap β)) (g := ξ₀) y
    (IsLocalRing.closedPoint Ω₀) hy
  have sq : IsPullback (pullback.snd (pullback.fst s (spMap β)) ξ₀)
      (pullback.fst (pullback.fst s (spMap β)) ξ₀ ≫ pullback.snd s (spMap β)) (spMap g₀) (spMap β) := by
    rw [← hs]
    exact (IsPullback.of_hasPullback (pullback.fst s (spMap β)) ξ₀).flip.paste_vert
      (IsPullback.of_hasPullback s (spMap β))
  let e := sq.isoPullback ≪≫ pullbackSpecIso O Ω₀ F
  have hint : Algebra.IsIntegral Ω₀ (Ω₀ ⊗[O] F) := HodgeBasic.isIntegral_tensor hγ hF
  let p : PrimeSpectrum (Ω₀ ⊗[O] F) := e.hom z
  have h1 : Algebra.trdeg ℤ p.asIdeal.ResidueField = Algebra.trdeg ℤ Ω₀ :=
    trdeg_residueField_of_isIntegral (K := Ω₀) p.asIdeal
  have hst : SurjectiveOnStalks (pullback.fst (pullback.fst s (spMap β)) ξ₀) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback (pullback.fst s (spMap β)) ξ₀).flip hsurj
  have h2 := trdeg_int_eq_of_ringEquiv (RingEquiv.ofBijective _ (residueFieldMap_bijective
    (pullback.fst (pullback.fst s (spMap β)) ξ₀) z))
  have h3 := trdeg_int_eq_of_ringEquiv (asIso (e.hom.residueFieldMap z)).commRingCatIsoToRingEquiv
  have h4 : Algebra.trdeg ℤ ((Spec (.of (Ω₀ ⊗[O] F))).residueField p) = Algebra.trdeg ℤ p.asIdeal.ResidueField :=
    trdeg_int_eq_of_ringEquiv (B := p.asIdeal.ResidueField)
      (Scheme.Spec.residueFieldIso (.of (Ω₀ ⊗[O] F)) p).commRingCatIsoToRingEquiv
  exact h2.trans (h3.symm.trans (h4.trans h1))

theorem trdeg_eq_dim : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Ω₀ : Type) [Field Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X) (Ω : Type) [Field Ω] (x : Sp Ω ⟶ Xo.XF c) (i : Ω₀ →+* Ω), Function.Injective β → IsCptGen ξ₀ → x ≫ Y.j = Spec.map (CommRingCat.ofHom i) ≫ ξ₀ → Algebra.trdeg ℤ Ω₀ = ((D.dim : ℕ) : Cardinal) := by
  intro E _ _ _ H D l Xo c O _ β Y Ω₀ _ ξ₀ Ω _ x i hβ h₀ hx
  have := c.fin
  have := Y.jQ_open

  let g₀ : O →+* Ω₀ := (Spec.preimage (ξ₀ ≫ Y.s)).hom
  have hs : ξ₀ ≫ Y.s = spMap g₀ := by
    show _ = Spec.map (CommRingCat.ofHom (Spec.preimage (ξ₀ ≫ Y.s)).hom)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  let str := pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)
  let cst : c.F →+* Ω := (Spec.preimage (x ≫ str)).hom
  have hc : x ≫ str = spMap cst := by
    show _ = Spec.map (CommRingCat.ofHom (Spec.preimage (x ≫ str)).hom)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hj : Y.j ≫ Y.s = str ≫ spMap β := by
    simp only [Model.j, Category.assoc, pullback.condition]
    rw [← Category.assoc, Y.jQ_over]
  have hcomp : i.comp g₀ = cst.comp β := by
    have h1 : spMap (i.comp g₀) = spMap (cst.comp β) := by
      have h2 : spMap i ≫ ξ₀ ≫ Y.s = x ≫ str ≫ spMap β := by
        rw [← hj, ← Category.assoc, ← Category.assoc, ← hx]
      rw [hs, ← Category.assoc, hc] at h2
      simpa only [spMap, CommRingCat.ofHom_comp, Spec.map_comp] using h2
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  have hg : Function.Injective g₀ := by
    refine Function.Injective.of_comp (f := i) ?_
    have h3 : (i ∘ g₀) = cst ∘ β := congrArg DFunLike.coe hcomp
    rw [h3]
    exact cst.injective.comp hβ
  have hΩ : CharZero Ω := charZero_of_injective_ringHom cst.injective
  have hΩ₀ : CharZero Ω₀ := (RingHom.charZero_iff i.injective).2 hΩ

  let w : Xo.XF c := x (IsLocalRing.closedPoint Ω)
  have hy : pullback.fst Y.s (spMap β) (Y.jQ w) = genPt ξ₀ := by
    have h4 : pullback.fst Y.s (spMap β) (Y.jQ w) = (x ≫ Y.j) (IsLocalRing.closedPoint Ω) := rfl
    have h6 : (Spec.map (CommRingCat.ofHom i) ≫ ξ₀) (IsLocalRing.closedPoint Ω) =
        ξ₀ ((Spec.map (CommRingCat.ofHom i)) (IsLocalRing.closedPoint Ω)) := rfl
    have h5 : (Spec.map (CommRingCat.ofHom i)) (IsLocalRing.closedPoint Ω) = IsLocalRing.closedPoint Ω₀ :=
      Subsingleton.elim (α := PrimeSpectrum _) _ _
    rw [h4, hx, h6, h5]
    rfl
  have hF := HodgeBasic.exists_integral_multiple_of_injective β hβ
  have hw : ∀ w' : Xo.XF c, w' ⤳ w → w' = w := fun w' h =>
    Y.jQ.isOpenEmbedding.injective
      (HodgeBasic.eq_of_specializes_of_fst Y.s β g₀ ξ₀ h₀ hs hg hF hy (h.map Y.jQ.continuous))

  have hsm : SmoothOfRelativeDimension D.dim str :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) Xo.smooth
  obtain ⟨-, htr⟩ := GlobalTheory.residueField_fg_trdeg_of_smoothOfRelativeDimension str D.dim hsm w hw
  letI : Algebra c.F ((Xo.XF c).residueField w) :=
    (Spec.preimage ((Xo.XF c).fromSpecResidueField w ≫ str)).hom.toAlgebra
  have : CharZero ((Xo.XF c).residueField w) :=
    charZero_of_injective_algebraMap (algebraMap c.F ((Xo.XF c).residueField w)).injective
  have h6 : Algebra.trdeg ℤ ((Xo.XF c).residueField w) = (D.dim : Cardinal) := by
    have hal : Algebra.IsAlgebraic ℤ c.F :=
      ⟨fun u => (IsFractionRing.isAlgebraic_iff ℤ ℚ c.F).2 (Algebra.IsAlgebraic.isAlgebraic u)⟩
    have h0 : Algebra.trdeg ℤ c.F = 0 := trdeg_eq_zero
    rw [← trdeg_add_eq ℤ c.F (A := (Xo.XF c).residueField w), h0, zero_add]
    exact htr
  have h7 := trdeg_int_eq_of_ringEquiv (asIso (Y.jQ.residueFieldMap w)).commRingCatIsoToRingEquiv
  have h8 := trdeg_residueField_of_fst Y.s β g₀ ξ₀ h₀ hs hg hF hy
  rw [← h8, h7, h6]

end GlobalTheory.CompanionTheory.Ar.CptTrdeg
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericTrdegEqDimensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_trdeg_eq_dimension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Ω₀ : Type) [Field Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X) (Ω : Type) [Field Ω] (x : Sp Ω ⟶ Xo.XF c) (i : Ω₀ →+* Ω), Function.Injective β → IsCptGen ξ₀ → x ≫ Y.j = Spec.map (CommRingCat.ofHom i) ≫ ξ₀ → Algebra.trdeg ℤ Ω₀ = ((D.dim : ℕ) : Cardinal) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CptTrdeg.trdeg_eq_dim | exact GlobalTheory.CompanionTheory.Ar.CptTrdeg.trdeg_eq_dim | (intros; apply GlobalTheory.CompanionTheory.Ar.CptTrdeg.trdeg_eq_dim <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperHasPowerFns
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperHasPowerFns
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Conj.ProperPowFns

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem powFns_of_proper_algClosed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [IsAlgClosed k] (tB : SAB H (Sp k)), IsProper tB.G.hom → PowFns tB :=
  fun _ _ _ _ _ _ _ _ tB hp n =>
    haveI := hp
    AbelianSchemeGerms.globalFns_powObj GlobalTheory.globalFns_holds tB.G tB.semi n

end GlobalTheory.CompanionTheory.Ar.Conj.ProperPowFns
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperHasPowerFnsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_has_power_fns : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [IsAlgClosed k] (tB : SAB H (Sp k)), IsProper tB.G.hom → PowFns tB := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.ProperPowFns.powFns_of_proper_algClosed | exact GlobalTheory.CompanionTheory.Ar.Conj.ProperPowFns.powFns_of_proper_algClosed | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.ProperPowFns.powFns_of_proper_algClosed <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionHiddenSecond
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionHiddenSecond
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.DegZ

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegZ

open Module

theorem linearIndependent_span_of_toMatrix {S M C A : Type} [CommRing S] [AddCommGroup M] [Module S M]
    [Fintype C] [DecidableEq C] [Fintype A] [DecidableEq A] (e : Basis C S M) (w : A → M)
    (Q : Matrix A C S) (h₁ : e.toMatrix w * Q = 1) (h₂ : Q * e.toMatrix w = 1) :
    LinearIndependent S w ∧ Submodule.span S (Set.range w) = ⊤ := by
  let L : (A → S) ≃ₗ[S] (C → S) := LinearEquiv.ofLinearMap (Matrix.toLin' (e.toMatrix w)) (Matrix.toLin' Q)
    (by rw [← Matrix.toLin'_mul, h₁, Matrix.toLin'_one]) (by rw [← Matrix.toLin'_mul, h₂, Matrix.toLin'_one])
  let b : Basis A S M := (Pi.basisFun S A).map (L ≪≫ₗ e.equivFun.symm)
  have hb : ⇑b = w := by
    funext i
    apply e.equivFun.injective
    ext a
    simp [b, L, Basis.toMatrix_apply, Matrix.toLin'_apply]
  exact ⟨hb ▸ b.linearIndependent, hb ▸ b.span_eq⟩

def pairBasis (R : Type) [CommRing R] (d : ℕ) : Basis (Fin d ⊕ Fin d) R ((Fin d → R) × (Fin d → R)) :=
  (Pi.basisFun R (Fin d)).prod (Pi.basisFun R (Fin d))

theorem pairBasis_repr_vmap {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {d : ℕ}
    (y : (Fin d → R) × (Fin d → R)) (a : Fin d ⊕ Fin d) :
    (pairBasis S d).repr (vmap f y) a = f ((pairBasis R d).repr y a) := by
  cases a <;> simp [pairBasis, vmap]

theorem linearIndependent_span_vmap {R S A : Type} [CommRing R] [CommRing S] [Fintype A] (f : R →+* S) {d : ℕ}
    (v : A → (Fin d → R) × (Fin d → R)) (hli : LinearIndependent R v)
    (hsp : Submodule.span R (Set.range v) = ⊤) :
    LinearIndependent S (fun i => vmap f (v i)) ∧
      Submodule.span S (Set.range fun i => vmap f (v i)) = ⊤ := by
  classical
  let b : Basis A R ((Fin d → R) × (Fin d → R)) := Basis.mk hli hsp.ge
  have hb : ⇑b = v := Basis.coe_mk hli hsp.ge
  have hP : (pairBasis S d).toMatrix (fun i => vmap f (v i)) = ((pairBasis R d).toMatrix v).map f := by
    ext a i
    simp [Basis.toMatrix_apply, pairBasis_repr_vmap]
  have h₁ : (pairBasis R d).toMatrix v * b.toMatrix (pairBasis R d) = 1 := by
    rw [← hb]; exact Basis.toMatrix_mul_toMatrix_flip _ _
  have h₂ : b.toMatrix (pairBasis R d) * (pairBasis R d).toMatrix v = 1 := by
    rw [← hb]; exact Basis.toMatrix_mul_toMatrix_flip _ _
  refine linearIndependent_span_of_toMatrix (pairBasis S d) _ ((b.toMatrix (pairBasis R d)).map f) ?_ ?_
  · rw [hP, ← Matrix.map_mul, h₁, Matrix.map_one _ f.map_zero f.map_one]
  · rw [hP, ← Matrix.map_mul, h₂, Matrix.map_one _ f.map_zero f.map_one]

theorem isHBasis_map : ∀ (E : Type) [Field E] [NumberField E] [StarRing (𝓞 E)] (R S : Type) [CommRing R]
    [Nontrivial R] [CommRing S] (f : R →+* S) (d r : ℕ) (B : Germ.FB R d (𝓞 E)) (B₂ : Germ.FB S d (𝓞 E))
    (x : Fin r → (Fin d → R) × (Fin d → R)), IsMapOf f B B₂ → IsHBasis B x →
      IsHBasis B₂ (fun j => vmap f (x j)) := by
  intro E _ _ _ R S _ _ _ f d r B B₂ x h hx
  have key := linearIndependent_span_vmap f _ hx.1 hx.2
  have he : (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
      rhoH B₂ (RingOfIntegers.basis E q.2) (vmap f (x q.1))) =
      fun q => vmap f (rhoH B (RingOfIntegers.basis E q.2) (x q.1)) :=
    funext fun q => (vmap_rhoH h _ _).symm
  unfold IsHBasis
  rw [he]
  exact key

end GlobalTheory.CompanionTheory.Ar.Flat.DegZ
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionHiddenSecondStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.DegZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_second : ∀ (E : Type) [Field E] [NumberField E] [StarRing (𝓞 E)] (R S : Type) [CommRing R] [Nontrivial R] [CommRing S] (f : R →+* S) (d r : ℕ) (B : Germ.FB R d (𝓞 E)) (B₂ : Germ.FB S d (𝓞 E)) (x : Fin r → (Fin d → R) × (Fin d → R)), IsMapOf f B B₂ → IsHBasis B x → IsHBasis B₂ (fun j => vmap f (x j)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.DegZ.isHBasis_map | exact GlobalTheory.CompanionTheory.Ar.Flat.DegZ.isHBasis_map | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.DegZ.isHBasis_map <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdaptedBasesChangeByBlockMatrices
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdaptedBasesChangeByBlockMatrices
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem det_eq_det_mul_det_of_block {K : Type} [Field K] {p q : ℕ} (M : Matrix (Fin (p + q)) (Fin (p + q)) K)
    (P : Matrix (Fin p) (Fin p) K) (D : Matrix (Fin q) (Fin q) K)
    (h11 : ∀ i k, M (Fin.castAdd q i) (Fin.castAdd q k) = P i k)
    (h21 : ∀ j k, M (Fin.natAdd p j) (Fin.castAdd q k) = 0)
    (h22 : ∀ j l, M (Fin.natAdd p j) (Fin.natAdd p l) = D j l) : M.det = P.det * D.det := by
  have hM : M.submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks P (Matrix.of fun i l => M (Fin.castAdd q i) (Fin.natAdd p l)) 0 D := by
    ext a b
    rcases a with i | j <;> rcases b with k | l
    · simp [h11]
    · simp
    · simp [h21]
    · simp [h22]
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv M, hM, Matrix.det_fromBlocks_zero₂₁]

theorem exists_det_mul_eq_of_isAdapted
    (E : Type) [Field E] [NumberField E] (K W : Type) [Field K] [AddCommGroup W] [Module K W]
    (ρH : 𝓞 E →+* Module.End K (W × Module.Dual K W)) (σ : E →+* K) (p q : ℕ) (v v' : Fin p → W) (w w' : Fin q → W)
    (u u' : Fin (p + q) → W × Module.Dual K W) (P : Matrix (Fin p) (Fin p) K) (Q : Matrix (Fin q) (Fin q) K) :
    IsAdapted ρH σ v w u → IsAdapted ρH σ v' w' u' → LinearIndependent K v →
    Submodule.span K (Set.range u) = HT.eigSp ρH σ →
    (∀ i, v' i = ∑ k, P i k • v k) → (∀ i, w' i = ∑ k, Q i k • w k) →
    ∃ B : Matrix (Fin (p + q)) (Fin (p + q)) K, (∀ i, u' i = ∑ k, B i k • u k) ∧ B.det * Q.det = P.det := by
  intro h h' hv hspan hP hQ
  obtain ⟨-, h1, h2⟩ := h
  obtain ⟨he', h1', h2'⟩ := h'
  have hex : ∀ i, ∃ c : Fin (p + q) → K, ∑ k, c k • u k = u' i := fun i => by
    rw [← Submodule.mem_span_range_iff_exists_fun, hspan]
    exact he' i
  choose B hB using hex
  let M : Matrix (Fin (p + q)) (Fin (p + q)) K := Matrix.of B
  have hMB : ∀ i k, M i k = B i k := fun _ _ => rfl
  refine ⟨M, fun i => (hB i).symm, ?_⟩
  have hfst : ∀ i, (u' i).1 = ∑ k : Fin p, M i (Fin.castAdd q k) • v k := fun i => by
    rw [← hB i, Prod.fst_sum, Fin.sum_univ_add]
    simp [h1, (h2 _).1, hMB]
  have h11 : ∀ i k, M (Fin.castAdd q i) (Fin.castAdd q k) = P i k := fun i k => by
    have e := (hfst (Fin.castAdd q i)).symm.trans ((h1' i).trans (hP i))
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at e
    simp only [← sub_smul] at e
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hv _ e k)
  have h21 : ∀ j k, M (Fin.natAdd p j) (Fin.castAdd q k) = 0 := fun j k => by
    have e := (hfst (Fin.natAdd p j)).symm.trans (h2' j).1
    exact Fintype.linearIndependent_iff.1 hv _ e k
  have hsnd : ∀ j, (u' (Fin.natAdd p j)).2 =
      ∑ l : Fin q, M (Fin.natAdd p j) (Fin.natAdd p l) • (u (Fin.natAdd p l)).2 := fun j => by
    rw [← hB (Fin.natAdd p j), Prod.snd_sum, Fin.sum_univ_add]
    simp only [← hMB, Prod.smul_snd, h21, zero_smul, Prod.snd_zero, Finset.sum_const_zero, _root_.zero_add]
  let D : Matrix (Fin q) (Fin q) K := fun j l => M (Fin.natAdd p j) (Fin.natAdd p l)
  have hDQ : D * Q.transpose = 1 := by
    ext j j'
    have e := (h2' j).2 j'
    rw [hsnd j, hQ j'] at e
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, (h2 _).2, smul_eq_mul] at e
    simp only [mul_ite, _root_.mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true] at e
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.transpose_apply]
    rw [← e]
    exact Finset.sum_congr rfl fun _ _ => _root_.mul_comm _ _
  have hdet : M.det = P.det * D.det := det_eq_det_mul_det_of_block M P D h11 h21 fun _ _ => rfl
  have hDQd : D.det * Q.det = 1 := by
    rw [← Matrix.det_transpose Q, ← Matrix.det_mul, hDQ, Matrix.det_one]
  rw [hdet, _root_.mul_assoc, hDQd, _root_.mul_one]

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdaptedBasesChangeByBlockMatricesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_bases_change_by_block_matrices : ∀ (E : Type) [Field E] [NumberField E] (K W : Type) [Field K] [AddCommGroup W] [Module K W]
    (ρH : 𝓞 E →+* Module.End K (W × Module.Dual K W)) (σ : E →+* K) (p q : ℕ) (v v' : Fin p → W) (w w' : Fin q → W)
    (u u' : Fin (p + q) → W × Module.Dual K W) (P : Matrix (Fin p) (Fin p) K) (Q : Matrix (Fin q) (Fin q) K),
    IsAdapted ρH σ v w u → IsAdapted ρH σ v' w' u' → LinearIndependent K v →
    Submodule.span K (Set.range u) = HT.eigSp ρH σ →
    (∀ i, v' i = ∑ k, P i k • v k) → (∀ i, w' i = ∑ k, Q i k • w k) →
    ∃ B : Matrix (Fin (p + q)) (Fin (p + q)) K, (∀ i, u' i = ∑ k, B i k • u k) ∧ B.det * Q.det = P.det := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.exists_det_mul_eq_of_isAdapted | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.exists_det_mul_eq_of_isAdapted | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.exists_det_mul_eq_of_isAdapted <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentTwistFrameCompat
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentTwistFrameCompat
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TwistInterior

theorem genPt_specializes_of_injective {Ω : Type} [Field Ω] {R : CommRingCat.{0}} [IsDomain R]
    (φ : R ⟶ CommRingCat.of Ω) (hφ : Function.Injective φ.hom) (q : Spec R) :
    genPt (Spec.map φ) ⤳ q := by
  refine (PrimeSpectrum.le_iff_specializes (genPt (Spec.map φ) : PrimeSpectrum R) q).1 ?_
  intro a ha
  have hm : φ.hom a ∈ IsLocalRing.maximalIdeal Ω := ha
  have h0 : φ.hom a = 0 := by
    by_contra hne
    exact hm (isUnit_iff_ne_zero.2 hne)
  have : a = 0 := hφ (h0.trans (map_zero φ.hom).symm)
  rw [this]
  exact zero_mem _

theorem lift_transfer {X X' W W' V : Scheme.{0}} {Ω : Type} [Field Ω] {R : Type} [CommRing R]
    (e : X' ≅ X) (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω ⟶ X') (hξ : ξ' ≫ e.hom = ξ)
    (hgen : IsCptGen ξ') (hall : ∀ q : X', genPt ξ' ⤳ q) (hdom : ∀ p : X', IsDomain (X'.presheaf.stalk p))
    (sW : W ⟶ Sp R) (hproj : IsProjOver sW)
    (f : X ⟶ W) (f' : X' ⟶ W') (j : V ⟶ W) (j' : V ⟶ W') [Mono j'] (Ψ : V ≅ V) (x x' : Sp Ω ⟶ V)
    (hx : x' ≫ Ψ.inv = x) (hf : ξ ≫ f = x ≫ j) (hf' : ξ' ≫ f' = x' ≫ j') (p : X')
    (hu : ∃ u' : Spec (X'.presheaf.stalk p) ⟶ V, u' ≫ j' = X'.fromSpecStalk p ≫ f') :
    ∃ u : Spec (X.presheaf.stalk (e.hom p)) ⟶ V, u ≫ j = X.fromSpecStalk (e.hom p) ≫ f := by
  obtain ⟨u', hu'⟩ := hu
  haveI := hdom p
  have h' : ξ' (IsLocalRing.closedPoint Ω) ⤳ p := hall p
  let φ : X'.presheaf.stalk p ⟶ CommRingCat.of Ω := X'.presheaf.stalkSpecializes h' ≫ Scheme.stalkClosedPointTo ξ'
  let ξp : Sp Ω ⟶ Spec (X'.presheaf.stalk p) := Spec.map φ
  have hξp : ξp ≫ X'.fromSpecStalk p = ξ' := by
    simp only [ξp, φ]
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ'
  have hgp : ∀ q, genPt ξp ⤳ q := genPt_specializes_of_injective φ (hgen.inj ⟨p, hall p⟩)
  have hxu : ξp ≫ u' = x' := by
    rw [← cancel_mono j', Category.assoc, hu', ← Category.assoc, hξp, hf']
  have heq : u' ≫ Ψ.inv ≫ j = X'.fromSpecStalk p ≫ e.hom ≫ f := by
    refine GlobalTheory.T.eq_of_eq_generic_projective R (Spec (X'.presheaf.stalk p)) W sW Ω ξp _ _ hproj hgp ?_
    have h1 : ξp ≫ u' ≫ Ψ.inv ≫ j = x ≫ j := by rw [reassoc_of% hxu, reassoc_of% hx]
    have h2 : ξp ≫ X'.fromSpecStalk p ≫ e.hom ≫ f = x ≫ j := by rw [reassoc_of% hξp, reassoc_of% hξ, hf]
    rw [h1, h2]
  haveI : IsIso (e.hom.stalkMap p) := inferInstance
  refine ⟨inv (Spec.map (e.hom.stalkMap p)) ≫ u' ≫ Ψ.inv, ?_⟩
  rw [Category.assoc, Category.assoc, heq, ← Scheme.SpecMap_stalkMap_fromSpecStalk_assoc, IsIso.inv_hom_id_assoc]

end GlobalTheory.CompanionTheory.Ar.TwistInterior

namespace GlobalTheory.CompanionTheory.Ar.TwistInterior

theorem interior_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F)
    (Y : Model Xo c β) (Y' : Model Xo c β') (g : HostAut H) (Φ : Xo.X ≅ Xo.X)
    (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K]
    (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (A' : HodgeCpt Y' S y)
    (e : A'.X ≅ A.X) (x x' : Sp Ω ⟶ Xo.XF c),
    Mono (spMap β) → Mono (spMap β') → Φ.hom ≫ Xo.s = Xo.s → A'.ξ ≫ e.hom = A.ξ → A.ξ ≫ A.f = x ≫ Y.j → A'.ξ ≫ A'.f = x' ≫ Y'.j →
    x' ≫ pullback.fst _ _ = x ≫ pullback.fst _ _ ≫ Φ.hom → x' ≫ pullback.snd _ _ = x ≫ pullback.snd _ _ →
    A.cst = A'.cst → x ≫ pullback.snd _ _ = spMap A.cst → (∀ p ∈ S, A'.R p = A.R p) →
    ∀ z : Sp ℂ ⟶ A'.X, A'.Interior z ↔ A.Interior (z ≫ e.hom) := by
  intro E _ _ _ H D l Xo c O O' _ _ β β' Y Y' g Φ n S Ω _ K _ J _ y A A' e x x' hβ hβ' hΦ hξ hf hf' hfst hsnd _ _ _ z
  have hΦ' : Φ.inv ≫ Xo.s = Xo.s := (Iso.inv_comp_eq Φ).2 hΦ.symm
  let ΦF : Xo.XF c ≅ Xo.XF c :=
    { hom := pullback.lift (pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Φ.hom)
        (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
        (by rw [Category.assoc, hΦ, pullback.condition])
      inv := pullback.lift (pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Φ.inv)
        (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
        (by rw [Category.assoc, hΦ', pullback.condition])
      hom_inv_id := pullback.hom_ext
        (by simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Iso.hom_inv_id, Category.comp_id,
          Category.id_comp])
        (by simp only [Category.assoc, pullback.lift_snd, Category.id_comp])
      inv_hom_id := pullback.hom_ext
        (by simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Iso.inv_hom_id, Category.comp_id,
          Category.id_comp])
        (by simp only [Category.assoc, pullback.lift_snd, Category.id_comp]) }
  have hxx : x ≫ ΦF.hom = x' := by
    apply pullback.hom_ext
    · simp only [ΦF, Category.assoc, pullback.lift_fst, hfst]
    · simp only [ΦF, Category.assoc, pullback.lift_snd, hsnd]
  obtain ⟨hjY, hA⟩ := GlobalTheory.T.hodge_cpt_interior_iff E H D l Xo c O β Y S Ω K J y A (z ≫ e.hom) hβ
  obtain ⟨hjY', hA'⟩ := GlobalTheory.T.hodge_cpt_interior_iff E H D l Xo c O' β' Y' S Ω K J y A' z hβ'
  have hc : centre (z ≫ e.hom) = e.hom (centre z) := rfl
  rw [hA, hA', hc]
  constructor
  · exact lift_transfer e A.ξ A'.ξ hξ A'.tie.gen A'.all (fun p => A'.normal.isDomain_stalk p) Y.s Y.proj A.f A'.f Y.j Y'.j
      ΦF x x' (by rw [← hxx, Category.assoc, Iso.hom_inv_id, Category.comp_id]) hf hf' (centre z)
  · intro hu
    have key := lift_transfer e.symm A'.ξ A.ξ (by rw [← hξ, Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id])
      A.tie.gen A.all (fun p => A.normal.isDomain_stalk p) Y'.s Y'.proj A'.f A.f Y'.j Y.j ΦF.symm x' x
      (by rw [Iso.symm_inv, hxx]) hf' hf (e.hom (centre z)) hu
    have hp : e.symm.hom (e.hom (centre z)) = centre z := by
      rw [Iso.symm_hom, ← Scheme.Hom.comp_apply, e.hom_inv_id]
      rfl
    rwa [hp] at key

end GlobalTheory.CompanionTheory.Ar.TwistInterior
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentTwistFrameCompatStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_component_twist_frame_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F)
    (Y : Model Xo c β) (Y' : Model Xo c β') (g : HostAut H) (Φ : Xo.X ≅ Xo.X)
    (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K]
    (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (A' : HodgeCpt Y' S y)
    (e : A'.X ≅ A.X) (x x' : Sp Ω ⟶ Xo.XF c),
    Mono (spMap β) → Mono (spMap β') → Φ.hom ≫ Xo.s = Xo.s → A'.ξ ≫ e.hom = A.ξ → A.ξ ≫ A.f = x ≫ Y.j → A'.ξ ≫ A'.f = x' ≫ Y'.j →
    x' ≫ pullback.fst _ _ = x ≫ pullback.fst _ _ ≫ Φ.hom → x' ≫ pullback.snd _ _ = x ≫ pullback.snd _ _ →
    A.cst = A'.cst → x ≫ pullback.snd _ _ = spMap A.cst → (∀ p ∈ S, A'.R p = A.R p) →
    ∀ z : Sp ℂ ⟶ A'.X, A'.Interior z ↔ A.Interior (z ≫ e.hom) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TwistInterior.interior_iff | exact GlobalTheory.CompanionTheory.Ar.TwistInterior.interior_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.TwistInterior.interior_iff <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmConjugationCompatComplexConj
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmConjugationCompatComplexConj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem conjugate_coe_eq_bar (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (τ : E →+* ℂ) (a : 𝓞 E) :
    ComplexEmbedding.conjugate τ (a : E) = τ (H.bar a : 𝓞 E) ∧ H.bar (H.bar a) = a := by
  constructor
  · rw [H.bar_eq, IsCMField.complexEmbedding_complexConj, ComplexEmbedding.conjugate_coe_eq]
  · apply RingOfIntegers.ext
    rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmConjugationCompatComplexConjStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_conjugation_compat_complex_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (τ : E →+* ℂ) (a : 𝓞 E),
    ComplexEmbedding.conjugate τ (a : E) = τ (H.bar a : 𝓞 E) ∧ H.bar (H.bar a) = a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.conjugate_coe_eq_bar | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.conjugate_coe_eq_bar | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.conjugate_coe_eq_bar <;> assumption)
end
end
