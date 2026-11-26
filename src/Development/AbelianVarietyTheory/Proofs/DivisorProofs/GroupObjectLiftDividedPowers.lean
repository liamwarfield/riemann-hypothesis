module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisQuotientAffineOpenSpecInvariants
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClearDenominatorsAmpleHermLineBundle
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousLatticeVectorsAlongArc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeDecompositionOfIdeleApprox
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CountingVolumeLeSelfIntersectionNefHermitianBund
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFacts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedLiftSymmetricOfSymmetricReduction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedLiftSymmetricOfSymmetricReduction
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic

namespace GlobalTheory.BirigidLift

theorem symm_of_lift : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDualCrystal →
    ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I), IsNilDP κ →
    ∀ (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left),
      IsGrpPullback A₀ A (spMap π) i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (l : (A₀ ⊗ A₀).left ⟶ (A ⊗ A).left), IsSquare i l →
    ∀ (L : LB A.left), L.IsLB → Out.RelAmple A L →
    ∀ (P₀ : LB (A₀ ⊗ A₀).left), P₀.IsLB → LBIso P₀ (P₀.pull (lift (snd A₀ A₀) (fst A₀ A₀)).left) →
    ∀ (P : LB (A ⊗ A).left), P.IsLB → HasGen (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left) →
      HasGen (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left) → LBIso (P.pull l) P₀ →
      LBIso P (P.pull (lift (snd A A) (fst A A)).left) := by
  intro HG HD R R₀ _ _ I κ hκ π hπ hI g A₀ _ A _ i h hA hg l hl L hL aL P₀ hP₀ hsym P hP h₁ h₂ e
  obtain ⟨l₁, l₂⟩ := hl
  have hs : (P.pull (lift (snd A A) (fst A A)).left).IsLB := pull_isLB hP _
  have h₁' : Triv (ev (swap P) (1 : A ⟶ A) (𝟙 A)) := by
    rw [triv_ev_iff hs, evc_swap hP hs, ← triv_ev_iff hP]
    exact h₂
  have h₂' : Triv (ev (swap P) (𝟙 A) (1 : A ⟶ A)) := by
    rw [triv_ev_iff hs, evc_swap hP hs, ← triv_ev_iff hP]
    exact h₁
  have sq : l ≫ (lift (snd A A) (fst A A)).left = (lift (snd A₀ A₀) (fst A₀ A₀)).left ≫ l := by
    apply left_ext
    · rw [Category.assoc, Category.assoc, lift_left_fst, l₂, l₁, lift_left_fst_assoc]
    · rw [Category.assoc, Category.assoc, lift_left_snd, l₁, l₂, lift_left_snd_assoc]
  have hl0 := pull_isLB hP l
  have e' : LBIso ((swap P).pull l) P₀ := by
    refine (cls_eq_iff (pull_isLB hs l) hP₀).1 ?_
    rw [cls_pull hs l, cls_pull hP, ← pull_comp, sq, pull_comp, ← cls_pull hP l hl0,
      (cls_eq_iff hl0 hP₀).2 e, ← cls_pull hP₀ _ (pull_isLB hP₀ _)]
    exact ((cls_eq_iff hP₀ (pull_isLB hP₀ _)).2 hsym).symm
  exact lift_unique HG HD.1 hκ hπ hI hA hg hA hg h h l₁ l₂ hL aL hL aL hP₀ hP h₁ h₂ e hs h₁' h₂' e'

end GlobalTheory.BirigidLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedLiftSymmetricOfSymmetricReductionStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.birigidified_lift_symmetric_of_symmetric_reduction : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDualCrystal →
    ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I), IsNilDP κ →
    ∀ (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left),
      IsGrpPullback A₀ A (spMap π) i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (l : (A₀ ⊗ A₀).left ⟶ (A ⊗ A).left), IsSquare i l →
    ∀ (L : LB A.left), L.IsLB → Out.RelAmple A L →
    ∀ (P₀ : LB (A₀ ⊗ A₀).left), P₀.IsLB → LBIso P₀ (P₀.pull (lift (snd A₀ A₀) (fst A₀ A₀)).left) →
    ∀ (P : LB (A ⊗ A).left), P.IsLB → HasGen (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left) →
      HasGen (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left) → LBIso (P.pull l) P₀ →
      LBIso P (P.pull (lift (snd A A) (fst A A)).left) := by
  first | exact @GlobalTheory.BirigidLift.symm_of_lift | exact GlobalTheory.BirigidLift.symm_of_lift | (intros; apply GlobalTheory.BirigidLift.symm_of_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianLiftDeRhamUnique
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OActLift


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
attribute [local instance] Over.cartesianMonoidalCategory in
set_option autoImplicit false in
theorem _root_.GlobalTheory.OActLift.isMonHom_mul_of_comm {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
    (f g : G ⟶ G) [IsMonHom f] [IsMonHom g] : IsMonHom (f * g) := by
  rw [Hom.mul_def]
  infer_instance

end GlobalTheory.OActLift
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RMDeform

theorem exists_lift_abelian (GD : GlobalTheory.Published.GrothendieckDeformation) (ADR : GlobalTheory.Published.AbelianDeRham)
    {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} (κ : DividedPowers I) (hκ : IsNilDP κ) (π : R →+* R₀)
    (hπ : Function.Surjective π) (hI : RingHom.ker π = I) {g : ℕ}
    {A₀ : Over (Sp R₀)} [GrpObj A₀] {A : Over (Sp R)} [GrpObj A] {i : A₀.left ⟶ A.left}
    (h : IsGrpPullback A₀ A (spMap π) i) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    (E : Submodule R (Crys κ (spMap π) A₀)) (hE : ∃ N, IsCompl E N)
    (hF : ∀ y : HdR A₀, y ∈ Fil A₀ ↔ ∃ d ∈ E, (GlobalTheory.Published.GrothendieckMessing.crysRedMor κ hI A₀).Corr d y) :
    ∃ (A' : Over (Sp R)) (_ : GrpObj A') (i' : A₀.left ⟶ A'.left) (h' : IsGrpPullback A₀ A' (spMap π) i'),
      IsAbelianScheme A' ∧ SmoothOfRelativeDimension g A'.hom ∧ liftFil κ h' = E := by
  obtain ⟨HC, HL, -⟩ := GD R I κ hκ R₀ π hπ hI
  have b := (HC g A₀ A i h hA hg).1
  have c := HC.crysToDR_bijective h hA hg
  obtain ⟨N, hN⟩ := hE
  have adm : GlobalTheory.Published.GrothendieckMessing.IsAdmissible h (E.map (crysToDR κ h)) := by
    refine ⟨⟨N.map (crysToDR κ h), (Submodule.orderIsoMapComap (LinearEquiv.ofBijective _ c)).isCompl hN⟩,
      fun y ↦ ?_⟩
    rw [hF]
    constructor
    · rintro ⟨d, hd, e⟩
      exact ⟨_, ⟨d, hd, rfl⟩, (GlobalTheory.Published.GrothendieckMessing.corr_crysToDR_iff hI h b.2 d y).2 e⟩
    · rintro ⟨_, ⟨d, hd, rfl⟩, e⟩
      exact ⟨d, hd, (GlobalTheory.Published.GrothendieckMessing.corr_crysToDR_iff hI h b.2 d y).1 e⟩
  obtain ⟨A', _, i', h', hA', hg', e⟩ := HL g A₀ A i h hA hg _ adm
  exact ⟨A', inferInstance, i', h', hA', hg', by rw [e, Submodule.comap_map_eq_of_injective c.1]⟩

theorem lbIso_pull_square {X₀ X Y₀ Y : Scheme.{0}} {P : LB X} {P₀ : LB X₀} (hP : P.IsLB) (hP₀ : P₀.IsLB)
    {l : X₀ ⟶ X} (e : LBIso (P.pull l) P₀) (a₀ : Y₀ ⟶ X₀) (a : Y ⟶ X) (y : Y₀ ⟶ Y) (w : a₀ ≫ l = y ≫ a) :
    LBIso (P₀.pull a₀) ((P.pull a).pull y) := by
  refine (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hP₀ _) (pull_isLB (pull_isLB hP _) _)).1 ?_
  rw [GlobalTheory.CechPic.cls_pull hP₀, ← (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hP l) hP₀).2 e, GlobalTheory.CechPic.cls_pull hP,
    GlobalTheory.CechPic.cls_pull (pull_isLB hP a), GlobalTheory.CechPic.cls_pull hP, ← GlobalTheory.CechPic.pull_comp,
    ← GlobalTheory.CechPic.pull_comp, w]

end GlobalTheory.RMDeform
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExponentialOfSemiAbelianFibreLinearChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExponentialOfSemiAbelianFibreLinearChange
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped CategoryTheory.MonObj
open GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix

namespace GlobalTheory.ShFam.Hor.LogCh

theorem isExpAt_mulVec {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (X : Scheme.{0}) (t : SAB H X) (y : Sp ℂ ⟶ X) (g : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ t.G))
    (M : Matrix (Fin g) (Fin g) ℂ) (hM : IsUnit M.det) (hhol : IsHolTo Set.univ (fun z => (e z).left))
    (he : IsExpAt t y e) : IsExpAt t y (fun w => e (M *ᵥ w)) := by
  have hchain : ∀ w v, IsDerivAt0 (fun u => (e (M *ᵥ u)).left) w v ↔
      IsDerivAt0 (fun u => (e u).left) (M *ᵥ w) v := by
    intro w v
    rw [GlobalTheory.HolHom.isDerivAt0_iff, GlobalTheory.HolHom.isDerivAt0_iff]
    exact GlobalTheory.ShFam.BdArc.LatSec.isDerivAt_comp_iff (GlobalTheory.HolHom.holAt_of_isHolTo hhol (Set.mem_univ 0))
      (Matrix.mulVecLin M).toContinuousLinearMap w v
  have hMi : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hM
  have hiM : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hM
  refine ⟨fun v w => ?_, fun w => ?_, fun v hv => ?_⟩
  · simp only [Matrix.mulVec_add]
    exact he.1 _ _
  · simp_rw [hchain]
    exact he.2.1 (M *ᵥ w)
  · obtain ⟨w', hw', huniq⟩ := he.2.2 v hv
    refine ⟨M⁻¹ *ᵥ w', ?_, fun w₂ hw₂ => ?_⟩
    · show IsDerivAt0 (fun u => (e (M *ᵥ u)).left) (M⁻¹ *ᵥ w') v
      rw [hchain, Matrix.mulVec_mulVec, hMi, Matrix.one_mulVec]
      exact hw'
    · have h2 : M *ᵥ w₂ = w' := huniq _ ((hchain w₂ v).1 hw₂)
      rw [← h2, Matrix.mulVec_mulVec, hiM, Matrix.one_mulVec]

end GlobalTheory.ShFam.Hor.LogCh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExponentialOfSemiAbelianFibreLinearChangeStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped CategoryTheory.MonObj
open GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isExponentialOfSemiAbelianFibre_linearChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (y : Sp ℂ ⟶ X) (g : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ t.G)) (M : Matrix (Fin g) (Fin g) ℂ), IsUnit M.det → IsHolTo Set.univ (fun z => (e z).left) → GlobalTheory.ShFam.Hor.LogCh.IsExpAt t y e → GlobalTheory.ShFam.Hor.LogCh.IsExpAt t y (fun w => e (M *ᵥ w)) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.isExpAt_mulVec | exact GlobalTheory.ShFam.Hor.LogCh.isExpAt_mulVec | (intros; apply GlobalTheory.ShFam.Hor.LogCh.isExpAt_mulVec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.Mum.Two

def TorusHomOf {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (h : X' → X)
    (t : splitTorus S X ⟶ splitTorus S X') : Prop :=
  ∀ χ : X', res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
    (pullU t.left ⊤ (charUnit S X' χ)) = charUnit S X (h χ)

variable {R : Type} [CommRing R] [IsDomain R]

instance nonempty_av {S : Type} [CommRing S] [IsDomain S] (P : PolAV (Sp S)) : Nonempty P.A.left :=
  ⟨eSec P.A (⊥ : PrimeSpectrum S)⟩

abbrev JN (D₁ D₂ : DegPre R) : LB (D₁.P.A.left ⨿ D₂.P.A.left) := join D₁.P.L D₂.P.L

theorem jn_isLB (D₁ D₂ : DegPre R) : (JN D₁ D₂).IsLB := join_isLB D₁.P.isLB D₂.P.isLB

abbrev CmpLB (D₁ D₂ : DegPre R) (a : D₁.P.A ⟶ D₂.P.A) (χ₁ : D₁.X) (χ₂ : D₂.X) : LB D₁.P.A.left :=
  LB.LinComb (JN D₁ D₂) (Sum.elim (fun k => D₁.Oφ (𝟙 _) χ₁ k ≫ coprod.inl) (fun k => D₂.Oφ a χ₂ k ≫ coprod.inr))
    (Sum.elim Oε Oinvε)

def Nrm {D₁ D₂ : DegPre R} {a : D₁.P.A ⟶ D₂.P.A} {χ₁ : D₁.X} {χ₂ : D₂.X} (u : LB.Gen (CmpLB D₁ D₂ a χ₁ χ₂)) : Prop :=
  u.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J), Good (JN D₁ D₂) z J → val u (r ≫ eSec D₁.P.A) z J = 1

def Act (D₁ D₂ : DegPre R) (a : D₁.P.A ⟶ D₂.P.A) (h : D₂.X →+ D₁.X) {F : Type} [Field F] [Algebra (FractionRing R) F]
    (g : GtPtF D₁ F) (g' : GtPtF D₂ F) : Prop :=
  g'.b = g.b ≫ a ∧ ∀ (χ : D₂.X) (u : LB.Gen (CmpLB D₁ D₂ a (h χ) χ)), Nrm u → ∀ z J, Good (JN D₁ D₂) z J →
    val (g'.s χ) (𝟙 _) z (rr J) = val (g.s (h χ)) (𝟙 _) z (rl J) * val u g.b.left z J

variable {I : Ideal R} {D₁ D₂ : DegData R I} {A₁ A₂ : PolAV (Sp (FractionRing R))}
  {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]

def Over₀ (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) : Prop :=
  ∀ e, (Over.pullback (thick R I e)).map a ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map b

def OnTorus (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (h : D₂.toPre.X → D₁.toPre.X) : Prop :=
  ∀ e, ∃ t : splitTorus (Sp (R ⧸ I ^ (e + 1))) D₁.toPre.X ⟶ splitTorus (Sp (R ⧸ I ^ (e + 1))) D₂.toPre.X,
    TorusHomOf h t ∧ (U₁.gt e).i ≫ (Over.pullback (thick R I e)).map a = t ≫ (U₂.gt e).i

def Lin (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A)
    (h : D₂.toPre.X →+ D₁.toPre.X) : Prop :=
  IsMonHom a ∧ IsMonHom b ∧ Over₀ U₁ U₂ a b ∧ OnTorus U₁ U₂ a h

def Coord (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A)
    (h : D₂.toPre.X →+ D₁.toPre.X) : Prop :=
  ∀ χ, ∃ u : LB.Gen (CmpLB D₁.toPre D₂.toPre b (h χ) χ), Nrm u ∧
    ∀ (e : ℕ) (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G₁).left) (z : Z) (J), Good (JN D₁.toPre D₂.toPre) z J →
      val ((U₂.gt e).t χ) (x ≫ ((Over.pullback (thick R I e)).map a).left) z (rr J) =
        val ((U₁.gt e).t (h χ)) x z (rl J) * val u (x ≫ (U₁.gt e).pG.left) z J

def Gen₀ (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (c : A₁.A ⟶ A₂.A) : Prop :=
  (Over.pullback (jK R)).map a ≫ U₂.gen.hom = U₁.gen.hom ≫ c

def CrossH {F : Type} [Field F] [Algebra (FractionRing R) F] (c : A₁.A ⟶ A₂.A) {j j' : ℕ} (t₁ t₂ : SecA A₂ F j)
    (t₁' t₂' : SecA A₁ F j') : Prop :=
  ∀ z J₁ J₂, Good A₁.L z J₁ → Good A₂.L z J₂ →
    sA t₁ (TFK (R := R) F ◁ c).left z J₂ * sA t₂' (𝟙 _) z J₁ = sA t₂ (TFK (R := R) F ◁ c).left z J₂ * sA t₁' (𝟙 _) z J₁

def Key (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (c : A₁.A ⟶ A₂.A) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A)
    (h : D₂.toPre.X →+ D₁.toPre.X) (F : Type) [Field F] [Algebra (FractionRing R) F] : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ (p : QkPt D₁.toPre F k) (x : TFK (R := R) F ⟶ A₁.A), QkToAkU U₁ F k p x →
    ∀ g', Act D₁.toPre D₂.toPre b h p.g g' → ∃ p' : QkPt D₂.toPre F k, p'.g = g' ∧ QkToAkU U₂ F k p' (x ≫ c)

theorem lin_of_endU {U : UnifPre I D₁ A₁ G₁} (E : EndU U) : Lin U U E.aG E.aB E.h ∧ Gen₀ U U E.aG E.aA :=
  ⟨⟨E.homG, E.homB, E.q_lin, E.i_lin⟩, E.ext⟩

end GlobalTheory.Mum.Two
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProductOfEach
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.FlagFamily

open Limits

theorem isProjOver_pullback_over {k : Type} [CommRing k] {B X Y : Scheme.{0}} {q : B ⟶ Sp k} (hq : IsProjOver q)
    {f : X ⟶ B} {g : Y ⟶ B} (hf : IsProjOver (f ≫ q)) (hg : IsProjOver (g ≫ q)) :
    IsProjOver (pullback.fst f g ≫ f ≫ q) := by
  have : IsProper q := projProper k B q hq
  have h := ProjSpace.isProjOver_comp_of_isClosedImmersion (pullback.mapDesc f g q)
    (ProjSpace.isProjOver_pullback hf hg)
  rwa [pullback.lift_fst_assoc, Category.comp_id] at h

end GlobalTheory.FlagFamily
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelObjectOddLevelRigid
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelObjectOddLevelRigid
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegRigid

open GlobalTheory.CechPic GlobalTheory.AmpleRigid

theorem serreAmple : SerreAmpleSt :=
  serreAmple_of_finiteOrder_of_separated (GlobalTheory.AmpleFiniteOrder.finiteOrder_of_const_of_cube constSt GlobalTheory.AmpleCube.cubeSt)
    (separatedSt_of_const_cube constSt GlobalTheory.AmpleCube.cubeSt)

theorem exists_aut {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ φ' : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) (h' : IsGrpPullback A' A f φ') :
    ∃ σ : A' ≅ A', IsMonHom σ.hom ∧ σ.hom.left ≫ φ' = φ := by
  let ψ : A'.left ⟶ A'.left := h'.1.lift φ A'.hom h.1.w
  have e₁ : ψ ≫ φ' = φ := h'.1.lift_fst _ _ _
  have e₂ : ψ ≫ A'.hom = A'.hom := h'.1.lift_snd _ _ _
  have hψ : IsGrpPullback A' A' (𝟙 _) ψ :=
    IsGrpPullback.cancel h' (by rw [Category.id_comp, e₁]; exact h) (by rw [e₂, Category.comp_id])
  haveI : IsIso ψ := hψ.1.isIso_fst_of_isIso
  let σ : A' ≅ A' := Over.isoMk (asIso ψ) e₂
  exact ⟨σ, isMonHom_of_mul_comp σ.hom fun T x y => mul_comp_of_grpPullback_id σ.hom hψ x y, e₁⟩

theorem eq_of_field {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) (hamp : Out.RelAmple A L)
    {K : Type} [Field K] [IsAlgClosed K] {A' : Over (Sp K)} [GrpObj A'] (hA' : IsAbelianScheme A') {z : Sp K ⟶ S}
    {φ φ' : A'.left ⟶ A.left} (h : IsGrpPullback A' A z φ) (h' : IsGrpPullback A' A z φ')
    (hc : pull φ (cls L hL) = pull φ' (cls L hL)) {N : ℕ} (hN : 3 ≤ N) (hNK : (N : K) ≠ 0)
    (hfix : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ Sp K) (x : Over.mk t ⟶ A'), x ^ N = 1 →
      x.left ≫ φ = x.left ≫ φ') : φ = φ' := by
  obtain ⟨σ, hσ, e⟩ := exists_aut h h'
  have := hA'.comm
  have hL' := pull_isLB hL φ'
  obtain ⟨w, hw⟩ := (cls_eq_iff hL' hL').1 rfl
  obtain ⟨U, hU, hcl, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤)
    (x := z (IsLocalRing.closedPoint K)) trivial
  have hy : ∀ y, z y ∈ U := fun y =>
    (congrArg (fun V => y ∈ V) (Scheme.preimage_eq_top_of_closedPoint_mem z hcl)).mpr trivial
  have key := serreAmple K A' hA' (L.pull φ') hL'
    (relAmple_pull h'.1 hL hL' ((isGen_iff w).1 hw) U hU hy hamp) N hN hNK σ hσ
    (by rw [cls_pull hL, ← pull_comp, e, hc]) fun Ω _ _ t x hx => by
      apply Over.OverMorphism.ext
      apply h'.1.hom_ext
      · rw [Over.comp_left, Category.assoc, e]
        exact hfix Ω t x hx
      · rw [Over.w, Over.w]
  rw [← e, key, Over.id_left, Category.id_comp]

variable {h n n' : ℕ} {B B' : Type} [CommRing B] [CommRing B'] {ζ : B} {ζ' : B'} {S S' : Scheme.{0}}
  {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'}

theorem pull_cls_diag {c : SiegPre h n ζ s} {c' : SiegPre h n' ζ' s'} {φ : c'.A.left ⟶ c.A.left}
    {φ₂ : (G2 c'.A).left ⟶ (G2 c.A).left} (hs : IsSquare φ φ₂) (hw : LBIso c'.P (c.P.pull φ₂)) :
    pull φ (cls c.diag (pull_isLB c.isLB _)) = cls c'.diag (pull_isLB c'.isLB _) := by
  have e : (lift (𝟙 c'.A) (𝟙 c'.A)).left ≫ φ₂ = φ ≫ (lift (𝟙 c.A) (𝟙 c.A)).left := by
    have a₁ := congrArg (fun q => q.left) (lift_fst (𝟙 c.A) (𝟙 c.A))
    have a₂ := congrArg (fun q => q.left) (lift_snd (𝟙 c.A) (𝟙 c.A))
    have b₁ := congrArg (fun q => q.left) (lift_fst (𝟙 c'.A) (𝟙 c'.A))
    have b₂ := congrArg (fun q => q.left) (lift_snd (𝟙 c'.A) (𝟙 c'.A))
    simp only [Over.comp_left, Over.id_left] at a₁ a₂ b₁ b₂
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst c.A c.A).left = (_ ≫ _) ≫ (fst c.A c.A).left
      rw [Category.assoc, hs.1, ← Category.assoc, b₁, Category.assoc, a₁]; simp
    · show (_ ≫ _) ≫ (snd c.A c.A).left = (_ ≫ _) ≫ (snd c.A c.A).left
      rw [Category.assoc, hs.2, ← Category.assoc, b₂, Category.assoc, a₂]; simp
  have h1 : pull φ₂ (cls c.P c.isLB) = cls c'.P c'.isLB :=
    ((cls_eq_iff c'.isLB (pull_isLB c.isLB φ₂)).2 hw).symm
  unfold SiegPre.diag
  rw [cls_pull c.isLB, cls_pull c'.isLB, ← pull_comp, ← e, pull_comp, h1]

theorem eq_on_torsion (hζ : IsUnit ζ) (c : SiegPre h n ζ s) {A' : Over S'} [GrpObj A'] {f : S' ⟶ S}
    {φ φ' : A'.left ⟶ c.A.left} (hφ : IsGrpPullback A' c.A f φ)
    (lv : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S') ⟶ A'))
    (h₁ : ∀ a, (lv a).left ≫ φ = f ≫ (c.lev a).left) (h₂ : ∀ a, (lv a).left ≫ φ' = f ≫ (c.lev a).left)
    (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S') (y : Over.mk x ⟶ A') (hy : y ^ n = 1) :
    y.left ≫ φ = y.left ≫ φ' := by
  let β : B →+* k := (Spec.preimage ((x ≫ f) ≫ s)).hom
  obtain ⟨-, hs, -⟩ := c.geom k (x ≫ f) β (hζ.map β).unit (Spec.map_preimage _).symm rfl
  have hy₁ : pushHom hφ (Over.mk x) y ^ n = 1 := by rw [← map_pow, hy, map_one]
  obtain ⟨a, ha⟩ := hs _ hy₁
  have hu : (toUnit (Over.mk (x ≫ f))).left = x ≫ f := (Category.comp_id _).symm.trans (Over.w (toUnit _))
  have e : (x ≫ f) ≫ (c.lev a).left = y.left ≫ φ := by
    rw [← hu]
    exact congrArg (fun q => q.left) ha
  have e₁ : y.left = x ≫ (lv a).left := by
    apply hφ.1.hom_ext
    · rw [Category.assoc]
      exact e.symm.trans ((Category.assoc _ _ _).trans (congrArg (x ≫ ·) (h₁ a).symm))
    · rw [Over.w, Category.assoc, Over.w]
      exact (Category.comp_id _).symm
  rw [e₁, Category.assoc, Category.assoc]
  exact congrArg (x ≫ ·) ((h₁ a).trans (h₂ a).symm)

theorem eq_of_sRelBy : ∀ (h n n' d' : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (b : TBase B n) (ζ' : B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (c : SiegPre h n (b.ζ : B) s) (c' : SiegPre h n' ζ' s') (f : S' ⟶ S) (φ φ' : c'.A.left ⟶ c.A.left), 3 ≤ n → Odd n → c.Principal → SRelBy c' c d' 1 f φ → SRelBy c' c d' 1 f φ' → φ = φ' := by
  intro h n n' d' B B' _ _ b ζ' S S' s s' c c' f φ φ' hn _ hc ⟨g, ⟨φ₂, q, w⟩, l⟩ ⟨g', ⟨φ₂', q', w'⟩, l'⟩
  simp only [pow_one] at l l'
  obtain ⟨σ, hσ, e⟩ := exists_aut g g'
  have key : σ.hom = 𝟙 _ := by
    refine eq_id_of_forall_geometric_fibre laws_without_cohomology.1 c'.A c'.ab σ.hom (IsMonHom.one_hom σ.hom)
      fun t => ?_
    let K : Type := AlgebraicClosure (S'.residueField t)
    let j : Sp K ⟶ S' := Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField t) K)) ≫ S'.fromSpecResidueField t
    have hp := isGrpPullback_pullback c'.A j
    have := c'.ab.smooth
    have := c'.ab.proper
    have := c'.ab.geomConnected
    have hab : IsAbelianScheme ((Over.pullback j).obj c'.A) :=
      { comm := Functor.isCommMonObj_obj
        smooth := by change Smooth (pullback.snd c'.A.hom j); infer_instance
        proper := by change IsProper (pullback.snd c'.A.hom j); infer_instance
        geomConnected := by change GeometricallyConnected (pullback.snd c'.A.hom j); infer_instance }
    have hNK : (n : K) ≠ 0 := by
      have hu := b.unit.map (Spec.preimage ((j ≫ f) ≫ s)).hom
      rw [map_natCast] at hu
      exact hu.ne_zero
    have e' := eq_of_field (pull_isLB c.isLB _) hc.1 hab (hp.comp g) (hp.comp g')
      (by rw [pull_comp, pull_comp]; exact congrArg _ ((pull_cls_diag q w).trans (pull_cls_diag q' w').symm)) hn hNK
      fun Ω _ _ x y hy => by
        have hy₁ : pushHom hp (Over.mk x) y ^ n = 1 := by rw [← map_pow, hy, map_one]
        have e₁ := eq_on_torsion b.ζ.isUnit c g _ l l' Ω (x ≫ j) _ hy₁
        rw [← Category.assoc, ← Category.assoc]
        exact e₁
    refine ⟨_, _, j, _, _, (default : PrimeSpectrum K), ?_, hp.1, ?_⟩
    · exact (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply t _)
    · apply g'.1.hom_ext
      · rw [Category.assoc, e]
        exact e'
      · rw [Category.assoc, Over.w]
  rw [← e, key, Over.id_left, Category.id_comp]

end GlobalTheory.SiegRigid
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelObjectOddLevelRigidStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principal_siegel_object_odd_level_rigid : ∀ (h n n' d' : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (b : TBase B n) (ζ' : B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (c : SiegPre h n (b.ζ : B) s) (c' : SiegPre h n' ζ' s') (f : S' ⟶ S) (φ φ' : c'.A.left ⟶ c.A.left), 3 ≤ n → Odd n → c.Principal → SRelBy c' c d' 1 f φ → SRelBy c' c d' 1 f φ' → φ = φ' := by
  first | exact @GlobalTheory.SiegRigid.eq_of_sRelBy | exact GlobalTheory.SiegRigid.eq_of_sRelBy | (intros; apply GlobalTheory.SiegRigid.eq_of_sRelBy <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfSwap2
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt GlobalTheory.VB

namespace GlobalTheory.CovTest

def GdegPull : Prop :=
  ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ),
    IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X →
    π.residueDegree (genericPoint Y) ≠ 0 → ∀ L : HermLB p,
      gdeg (L.pull π hπ) D = (π.residueDegree (genericPoint Y) : ℝ) * gdeg L D

end GlobalTheory.CovTest

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesEvalAtNilpotentXEqCoordinate
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesEvalAtNilpotentXEqCoordinate
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

theorem evA_X (k : Type) [CommRing k] (σ : Type) [Finite σ] (A : Type) [CommRing A] [Algebra k A]
    (x : σ → A) (hx : ∀ i, IsNilpotent (x i)) (i : σ) : evA k x hx (X i) = x i := by
  have ha : HasSubst (fun i => (C (x i) : MvPowerSeries Empty A)) :=
    hasSubst_of_constantCoeff_nilpotent fun i => by simpa using hx i
  show (constantCoeff : MvPowerSeries Empty A →+* A) (substAlgHom (R := k) ha (X i)) = x i
  rw [substAlgHom_apply, subst_X ha, constantCoeff_C]

end GlobalTheory.Katz
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesEvalAtNilpotentXEqCoordinateStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate : ∀ (k : Type) [CommRing k] (σ : Type) [Finite σ] (A : Type) [CommRing A] [Algebra k A], ∀ (x : σ → A) (hx : ∀ i, IsNilpotent (x i)) (i : σ), evA k x hx (X i) = x i := by
  first | exact @GlobalTheory.Katz.evA_X | exact GlobalTheory.Katz.evA_X | (intros; apply GlobalTheory.Katz.evA_X <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSumPolAV
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MumProd

def tensLB {X : Scheme.{0}} (L M : LB X) : LB X :=
  LB.mk (L.ι × M.ι) (fun p => L.U p.1 ⊓ M.U p.2) fun p q =>
    res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
      L.U p.1 ⊓ M.U p.2 ⊓ (L.U q.1 ⊓ M.U q.2) ≤ L.U p.1 ⊓ L.U q.1) (L.g p.1 q.1) *
    res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
      L.U p.1 ⊓ M.U p.2 ⊓ (L.U q.1 ⊓ M.U q.2) ≤ M.U p.2 ⊓ M.U q.2) (M.g p.2 q.2)

abbrev extLB {X X₁ X₂ : Scheme.{0}} (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : X ⟶ X₁) (f₂ : X ⟶ X₂) : LB X :=
  tensLB (L₁.pull f₁) (L₂.pull f₂)

section MapsAt

variable {Y X X₁ X₂ : Scheme.{0}} {L : LB X} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : X ⟶ X₁} {f₂ : X ⟶ X₂}

def extIdx (j₁ : L₁.ι) (j₂ : L₂.ι) : (extLB L₁ L₂ f₁ f₂).ι :=
  ((fun _ => j₁, fun _ => j₂) : (PUnit → L₁.ι) × (PUnit → L₂.ι))

lemma mapsAt₂_le_a (w : LB.Iso L (extLB L₁ L₂ f₁ f₂)) (p : Y ⟶ X) (j₁ : L₁.ι) (j₂ : L₂.ι) (jL : L.ι) :
    p ⁻¹ᵁ (LB.div (extLB L₁ L₂ f₁ f₂) L).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂, jL) ≤
      LB.wchart L (fun _ : PUnit => p) (fun _ => jL) :=
  fun _ hy => Set.mem_iInter.2 fun _ => hy.2

lemma mapsAt₂_le_1 (w : LB.Iso L (extLB L₁ L₂ f₁ f₂)) (p : Y ⟶ X) (j₁ : L₁.ι) (j₂ : L₂.ι) (jL : L.ι) :
    p ⁻¹ᵁ (LB.div (extLB L₁ L₂ f₁ f₂) L).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂, jL) ≤
      LB.wchart L₁ (fun _ : PUnit => p ≫ f₁) (fun _ => j₁) := by
  intro y hy
  refine Set.mem_iInter.2 fun _ => ?_
  have h1 := Set.mem_iInter.1 hy.1.1 PUnit.unit
  exact h1

lemma mapsAt₂_le_2 (w : LB.Iso L (extLB L₁ L₂ f₁ f₂)) (p : Y ⟶ X) (j₁ : L₁.ι) (j₂ : L₂.ι) (jL : L.ι) :
    p ⁻¹ᵁ (LB.div (extLB L₁ L₂ f₁ f₂) L).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂, jL) ≤
      LB.wchart L₂ (fun _ : PUnit => p ≫ f₂) (fun _ => j₂) := by
  intro y hy
  refine Set.mem_iInter.2 fun _ => ?_
  have h1 := Set.mem_iInter.1 hy.1.2 PUnit.unit
  exact h1

def MapsAt₂ (w : LB.Iso L (extLB L₁ L₂ f₁ f₂)) (p : Y ⟶ X) (n : ℤ)
    (a : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p) (fun _ => n)))
    (b₁ : LB.Gen (LB.LinComb L₁ (K := PUnit) (fun _ => p ≫ f₁) (fun _ => n)))
    (b₂ : LB.Gen (LB.LinComb L₂ (K := PUnit) (fun _ => p ≫ f₂) (fun _ => n))) : Prop :=
  ∀ (j₁ : L₁.ι) (j₂ : L₂.ι) (jL : L.ι),
    res (mapsAt₂_le_1 w p j₁ j₂ jL) (b₁.s fun _ => j₁) * res (mapsAt₂_le_2 w p j₁ j₂ jL) (b₂.s fun _ => j₂) =
      (pullU p _ (w.s (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂, jL))) ^ n * res (mapsAt₂_le_a w p j₁ j₂ jL) (a.s fun _ => jL)

end MapsAt

structure IsSumPolAV {S : Scheme.{0}} (P P₁ P₂ : PolAV S) (a₁ : P.A ⟶ P₁.A) (a₂ : P.A ⟶ P₂.A) : Prop where
  hom₁ : IsMonHom a₁
  hom₂ : IsMonHom a₂
  lim : IsIso (lift a₁ a₂)
  w : ∃ w : LB.Iso P.L (extLB P₁.L P₂.L a₁.left a₂.left), w.IsGen

variable {R : Type} [CommRing R] [IsDomain R]

structure IsSumDeg (D D₁ D₂ : DegPre R) (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X)
    (q₂ : D.X →+ D₂.X) : Prop where
  hom₁ : IsMonHom p₁
  hom₂ : IsMonHom p₂
  lim : IsIso (lift p₁ p₂)
  xsum : Function.Bijective (q₁.prod q₂)
  c_pr₁ : ∀ x, D.c x ≫ p₁ = D₁.c (q₁ x)
  c_pr₂ : ∀ x, D.c x ≫ p₂ = D₂.c (q₂ x)
  w : ∃ w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left), w.IsGen ∧
    (∃ b₁ b₂, MapsAt₂ w (eSec D.P.A) 1 D.rig b₁ b₂ ∧ LB.Gen.Corr D₁.P.L _ _ _ _ b₁ D₁.rig ∧
      LB.Gen.Corr D₂.P.L _ _ _ _ b₂ D₂.rig) ∧
    ∀ x, ∃ b₁ b₂, MapsAt₂ w (D.xK x) (-1) (D.psi x) b₁ b₂ ∧ LB.Gen.Corr D₁.P.L _ _ _ _ b₁ (D₁.psi (q₁ x)) ∧
      LB.Gen.Corr D₂.P.L _ _ _ _ b₂ (D₂.psi (q₂ x))

end GlobalTheory.MumProd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt
open GlobalTheory.VBExt (AdaptedChart)
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder

namespace GlobalTheory.MixDens

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D d : ℕ}

def part (ρ : AlgChart p σ D → CxPts p σ → ℝ) : Measure (CxPts p σ) :=
  ChartGlue.glueMeas (fun c : AlgChart p σ D => c.e) fun c y => ENNReal.ofReal (ρ c y)

def IsDens (ρ : AlgChart p σ D → CxPts p σ → ℝ) : Prop :=
  (∀ (c c' : AlgChart p σ D) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source →
    ρ c y = ‖ChartGlue.transDet c.e c'.e y‖ ^ 2 * ρ c' y) ∧
  ∀ c : AlgChart p σ D, ContinuousOn (fun v => ρ c (c.e.symm v)) c.e.target

variable {ρ ρ' : AlgChart p σ D → CxPts p σ → ℝ}

def transMat (c c' : AlgChart p σ D) (y : CxPts p σ) : Matrix (Fin D) (Fin D) ℂ :=
  Matrix.of fun a b => fderiv ℂ (c'.e ∘ c.e.symm) (c.e y) (EuclideanSpace.single b 1) a

def IsForm (M : AlgChart p σ D → CxPts p σ → Matrix (Fin D) (Fin D) ℂ) : Prop :=
  (∀ (c c' : AlgChart p σ D) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source →
    M c y = chg (transMat c c' y) (M c' y)) ∧
  (∀ c : AlgChart p σ D, ContinuousOn (fun v => M c (c.e.symm v)) c.e.target) ∧
  ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, (M c y).IsHermitian

variable {A M M' J : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}

def chernMat {B : LB X} (φ : Weight p σ B) (c : AlgChart p σ D) (y : CxPts p σ) : Matrix (Fin D) (Fin D) ℂ :=
  c.hess φ (pick φ.isLB y) y

theorem chernMat_congr {L N : HermLB p} (e : L.Isometric N) (c : AlgChart p σ D) {y : CxPts p σ}
    (hy : y ∈ c.e.source) : chernMat (L.φ σ) c y = chernMat (N.φ σ) c y := by
  unfold chernMat
  exact (e.hess_eq c hy (mem_pick _ y) (mem_pick _ y)).symm

section Flag

variable {E : X.Modules} {r : ℕ} (h : VMetric p E r) (fl : Vert.Flag E r)

end Flag

section Cell

variable {ι : Type} [Fintype ι] {r : ι → ℕ} (e : Fin (d + 1) ≃ Option (Σ a, Low (r a)))



def emb {m : ℕ} (i : Fin m) : Fin i ⊕ Fin 1 → Fin m := Sum.elim (Fin.castLE i.isLt.le) fun _ => i



variable {m : ℕ}

variable {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} (π : Y ⟶ B) (w : π ≫ q = p)

end Cell

end GlobalTheory.MixDens
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti
set_option autoImplicit false

noncomputable section

open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup Coalgebra Bialgebra TensorProduct

namespace GlobalTheory.PDiv.FrobKerOrder

theorem add_pow_of_cast_eq_zero {A : Type*} [CommRing A] {p : ℕ} (hp : p.Prime)
    (h : (p : A) = 0) (x y : A) : (x + y) ^ p = x ^ p + y ^ p := by
  rw [add_pow_prime_eq hp, h]; simp

theorem cast_eq_zero_of_algebra (p : ℕ) (k A : Type*) [CommRing k] [CharP k p] [CommRing A]
    [Algebra k A] : (p : A) = 0 := by
  rw [← map_natCast (algebraMap k A), CharP.cast_eq_zero, map_zero]

variable (p : ℕ) [hp : Fact p.Prime] (k H : Type) [Field k] [CharP k p] [CommRing H]
  [HopfAlgebra k H]

theorem mk_pow_eq (x : H) :
    Ideal.Quotient.mkₐ k (frobKerIdeal p k H) x ^ p =
      algebraMap k _ (counit (R := k) x) ^ p := by
  have hx : x - algebraMap k H (counit (R := k) x) ∈ augIdeal k H := by
    simp [RingHom.mem_ker]
  have h0 : Ideal.Quotient.mkₐ k (frobKerIdeal p k H)
      ((x - algebraMap k H (counit (R := k) x)) ^ p) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (pow_mem_frobKerIdeal hx)
  have e : x = (x - algebraMap k H (counit (R := k) x)) + algebraMap k H (counit (R := k) x) := by
    ring
  conv_lhs => rw [e, ← map_pow, add_pow_of_cast_eq_zero hp.out (cast_eq_zero_of_algebra p k H),
    map_add, h0, zero_add, map_pow, AlgHom.commutes]

theorem map_pow_eq (t : H ⊗[k] H) :
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (frobKerIdeal p k H))
      (Ideal.Quotient.mkₐ k (frobKerIdeal p k H)) t ^ p =
    (1 : H ⧸ frobKerIdeal p k H) ⊗ₜ[k] (Ideal.Quotient.mkₐ k (frobKerIdeal p k H)
      (TensorProduct.lid k H (LinearMap.rTensor H (counit (R := k) (A := H)) t)) ^ p) := by
  induction t with
  | add x y hx hy =>
    simp only [map_add (f := _)]
    rw [add_pow_of_cast_eq_zero hp.out (cast_eq_zero_of_algebra p k _),
      add_pow_of_cast_eq_zero hp.out (cast_eq_zero_of_algebra p k _), hx, hy, tmul_add]
  | tmul x y =>
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_pow, mk_pow_eq,
      LinearMap.rTensor_tmul, TensorProduct.lid_tmul, map_smul, smul_pow, ← map_pow,
      Algebra.algebraMap_eq_smul_one, smul_tmul]

theorem isHopfIdeal : (frobKerIdeal p k H).IsHopfIdeal k := by
  have : ((frobKerIdeal p k H).restrictScalars k).IsCoideal := by
    refine ⟨?_, ?_⟩
    · intro x hx
      exact frobKerIdeal_le_augIdeal hp.out.ne_zero k H hx
    · intro x hx
      have h : frobKerIdeal p k H ≤ RingHom.ker
          ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (frobKerIdeal p k H))
            (Ideal.Quotient.mkₐ k (frobKerIdeal p k H))).comp (comulAlgHom k H)) := by
        refine Ideal.span_le.2 ?_
        rintro _ ⟨a, ha, rfl⟩
        rw [SetLike.mem_coe, RingHom.mem_ker, map_pow, AlgHom.comp_apply, map_pow_eq,
          comulAlgHom_apply, rTensor_counit_comul, TensorProduct.lid_tmul, one_smul, ← map_pow]
        have : Ideal.Quotient.mkₐ k (frobKerIdeal p k H) (a ^ p) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.2 (pow_mem_frobKerIdeal ha)
        rw [this, tmul_zero]
      exact h hx
  refine ⟨?_⟩
  · intro x hx
    have h : frobKerIdeal p k H ≤ (frobKerIdeal p k H).comap (HopfAlgebra.antipodeAlgHom k H) := by
      refine Ideal.span_le.2 ?_
      rintro _ ⟨a, ha, rfl⟩
      rw [SetLike.mem_coe, Ideal.mem_comap, map_pow]
      apply pow_mem_frobKerIdeal
      have ha' : counit (R := k) a = 0 := ha
      simp [RingHom.mem_ker, ha']
    exact h hx

omit [CharP k p] in
theorem le_sq : frobKerIdeal p k H ≤ augIdeal k H ^ 2 := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨a, ha, rfl⟩
  exact Ideal.pow_le_pow_right hp.out.two_le (Ideal.pow_mem_pow ha p)

theorem pow_le_finrank {n d : ℕ} {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    [Module.Finite K A] (x : Fin d → A)
    (h : RingHom.ker (MvPolynomial.aeval (R := K) x) =
      Ideal.span (Set.range fun i => (MvPolynomial.X i : MvPolynomial (Fin d) K) ^ n)) :
    n ^ d ≤ Module.finrank K A := by
  classical
  let e : (Fin d → Fin n) → (Fin d →₀ ℕ) := fun a => Finsupp.equivFunOnFinite.symm fun i => a i
  have he : Function.Injective e := by
    intro a b hab
    funext i
    have := DFunLike.congr_fun hab i
    exact Fin.ext (by simpa [e] using this)
  have hli : LinearIndependent K fun a : Fin d → Fin n =>
      MvPolynomial.aeval (R := K) x (MvPolynomial.monomial (e a) 1) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg a
    have hmem : (∑ a, g a • MvPolynomial.monomial (e a) (1 : K)) ∈
        RingHom.ker (MvPolynomial.aeval (R := K) x) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [RingHom.mem_ker, map_sum]
      simpa only [map_smul] using hg
    have hr : (Set.range fun i => (MvPolynomial.X i : MvPolynomial (Fin d) K) ^ n) =
        (fun s => MvPolynomial.monomial s (1 : K)) '' Set.range (fun i => Finsupp.single i n) := by
      rw [← Set.range_comp]
      congr 1
      funext i
      simp [MvPolynomial.X_pow_eq_monomial]
    rw [h, hr, MvPolynomial.mem_ideal_span_monomial_image] at hmem
    by_contra hne
    have hc : AddMonoidAlgebra.coeff (∑ a, g a • MvPolynomial.monomial (e a) (1 : K)) (e a) = g a := by
      simp [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, he.eq_iff]
    obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hmem (e a) (by rw [MvPolynomial.mem_support_iff, hc]; exact hne)
    have h1 := hi i
    have h2 := (a i).2
    simp [e] at h1
    omega
  simpa using hli.fintype_card_le_finrank

theorem pow_finrank_cot_le [Module.Finite k H] :
    p ^ Module.finrank k (Cot k H) ≤ Module.finrank k (H ⧸ frobKerIdeal p k H) := by
  haveI := isHopfIdeal p k H
  set J := frobKerIdeal p k H with hJ
  let π := Ideal.Quotient.mkₐ k J
  have hπ : Function.Surjective π := Ideal.Quotient.mkₐ_surjective k J
  have hε : (counitAlgHom k (H ⧸ J)).comp π = counitAlgHom k H := rfl
  have hbij : Function.Bijective (AugCot.map π hε) := by
    refine ⟨?_, AugCot.map_surjective π hε hπ⟩
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨z, rfl⟩ := (AugCot.exact_kerMap_map π hε hπ y).1 hy
    rw [AugCot.kerMap_apply, AugCot.d_of_mem _ (AugCot.ker_le π hε z.2),
      Ideal.toCotangent_eq_zero]
    exact le_sq p k H (Ideal.Quotient.eq_zero_iff_mem.1 z.2)
  rw [(LinearEquiv.ofBijective _ hbij).finrank_eq]
  set ε := counitAlgHom k (H ⧸ J) with hεdef
  let b := Module.finBasis k (AugCot ε)
  choose x hx using fun i => (RingHom.ker ε).toCotangent_surjective (b i)
  have hsum : ∀ l : Fin (Module.finrank k (AugCot ε)) → k,
      AugCot.d ε (∑ i, l i • (x i : H ⧸ J)) = ∑ i, l i • b i := by
    intro l
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, hx]
  have hmem : ∀ l : Fin (Module.finrank k (AugCot ε)) → k,
      (∑ i, l i • (x i : H ⧸ J)) ∈ RingHom.ker ε := by
    intro l
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (x i).2
  refine pow_le_finrank (fun i => (x i : H ⧸ J))
    (GlobalTheory.HeightOneHopf.truncated_polynomial p k (H ⧸ J) _ _ ?_ (fun i => (x i).2) ?_ ?_).2
  · intro f hf
    obtain ⟨a, rfl⟩ := hπ f
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (pow_mem_frobKerIdeal (R := k) hf)
  · intro y hy
    refine ⟨b.repr (AugCot.d ε y), ?_⟩
    have h1 : AugCot.d ε (y - ∑ i, b.repr (AugCot.d ε y) i • (x i : H ⧸ J)) = 0 := by
      rw [map_sub, hsum, b.sum_repr, sub_self]
    rwa [AugCot.d_of_mem _ (sub_mem hy (hmem _)), Ideal.toCotangent_eq_zero] at h1
  · intro l hl
    have h1 : AugCot.d ε (∑ i, l i • (x i : H ⧸ J)) = 0 := by
      rw [AugCot.d_of_mem _ (hmem _), Ideal.toCotangent_eq_zero]
      exact hl
    rw [hsum] at h1
    funext i
    exact Fintype.linearIndependent_iff.1 b.linearIndependent l h1 i

end GlobalTheory.PDiv.FrobKerOrder
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaPos
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc

theorem Trait.beta_pos : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (T : Trait F)
    (a : T.D.toPre.X), a ≠ 0 → 0 < T.β a a := by
  intro g n o _ ζ F T a ha
  obtain ⟨i, hi⟩ := T.mono.exists_pos (maximalIdeal.isMaximal T.V).ne_top ha
  fin_cases i
  simpa using hi

end GlobalTheory.Poinc
end
end
