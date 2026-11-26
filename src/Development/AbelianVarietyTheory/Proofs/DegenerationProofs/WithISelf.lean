module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPolAVGenericFibre
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPowerSectionOfChartFunctions
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniquePoint
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormValFUnit
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNumOf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PullInvClsOfFibres
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfield
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSquareUnique
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolOfSecondQuotient
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyTorusExtensionOfSurjectivePointsStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WithISelf
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
noncomputable section
namespace GlobalTheory.Relabel

def TwJ {O : Type} [CommRing O] {N N' : NumD O} {k : ℕ} (β : N.Form k) (u r : Oˣ) (J : NumD.Iso (N.twist β u) N')
    {j : ℕ} (q : N.QT j) (q' : N'.QT j) : Prop :=
  ∃ p : (N.twist β u).QT j, TwRel β u r q p ∧ q'.1.1.toAdd = J.e p.1.1.toAdd ∧ J.Rel p.1.2 q'.1.2
section
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {N : NumD F} {O : Type} [CommRing O] [StarRing O]

def actV (ν : NumOf D F N) (oa : D.P.OAct O) (x : O) (b : N.A) : N.A := ν.eA.symm (ν.eA b ≫ oa.act x)

def RosV (ν : NumOf D F N) (oa : D.P.OAct O) (x : O) (ρ : N.A → N.A → F) : Prop :=
  ∃ u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (oa.act (star x)) (oa.act x)) rosatiε), u.IsGen ∧
    LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L) ∧
    ∀ b b', ρ b b' = vF u (lift (ν.eA b) (ν.eA b')).left ν.J

def ActCompat [Module O D.X] (ν : NumOf D F N) (oa : D.OAct O) {R' : Type} [CommRing R'] [IsDomain R'] {D' : DegPre R'}
    [Algebra (FractionRing R') F] {N' : NumD F} [Module O D'.X] (ν' : NumOf D' F N') (oa' : D'.OAct O) {k : ℕ}
    (β : N.Form k) (u : Fˣ) (r : ℕ → Fˣ) (J : NumD.Iso (N.twist β u) N') : Prop :=
  ∀ j, 0 < j → ∀ (x : O) (p₀ p₁ : QkPt D F j) (p₀' p₁' : QkPt D' F j) q₀ q₁ q₀' q₁', QkAct oa x p₀ p₁ → ν.QPt p₀ q₀ →
    ν.QPt p₁ q₁ → TwJ β u (r j) J q₀ q₀' → TwJ β u (r j) J q₁ q₁' → ν'.QPt p₀' q₀' → ν'.QPt p₁' q₁' →
    QkAct oa' x p₀' p₁'
end
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {K : Type} [Field K]

abbrev FullI (o : Full D K) : Type :=
  letI := H.starRing
  TateIso D K (baseOver (Sp K) ⟶ o.P.A) (fun a g => g ≫ o.oa.act a) (fun n g g' c => WeilIs o.P.A o.P.L n g g' (unitOn c))

def withI (o : Full D K) (I : FullI o) : Full D K := { o with I := I }

end GlobalTheory.Relabel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPolAVGenericFibreOfTriple
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPolAVGenericFibreOfTriple
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

theorem GlobalTheory.LN.exists_polAV_of_polAt : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] (t : SAB H (Sp R)), PolAt t (jK R) → letI := H.starRing; ∃ (A : PolAV (Sp (FractionRing R))) (oA : A.OAct (𝓞 E)) (gen : (Over.pullback (jK R)).obj t.G ≅ A.A), IsMonHom gen.hom ∧ LBIso (A.L.pull gen.hom.left) (t.PP.L.pull (pullback.fst t.G.hom (jK R))) ∧ ∀ x, (Over.pullback (jK R)).map (t.act.act x) ≫ gen.hom = gen.hom ≫ oA.act x := by
  intro _ _ E _ _ _ H R _ _ t ⟨hp, hA, hK⟩
  let := H.starRing
  obtain ⟨PP', cub, sym, adj, prim, m₁, hm₁⟩ := sabPull CubePf.cubePull (jK R) t
  let t' : SAB H (Spec (CommRingCat.of (FractionRing R))) :=
    ⟨(Over.pullback (jK R)).obj t.G, IsSemiAbelian.pullback _ t.G t.semi,
      Geo.Tor.OAct.pullback _ t.G t.act, PP', cub, sym, adj, prim⟩
  let m₀ : SABMap t' t (jK R) := m₁
  have hm₀ : m₀.cm.F = pullback.fst t.G.hom (jK R) := hm₁
  obtain ⟨w, hw, -⟩ := m₀.lin
  have hL : LBIso t'.PP.L (t.PP.L.pull (pullback.fst t.G.hom (jK R))) := hm₀ ▸ ⟨w, hw⟩
  have hM := pull_isLB t.PP.isLB (pullback.fst t.G.hom (jK R))
  have hL' : LBIso t'.PP.L ((t.PP.L.pull (pullback.fst t.G.hom (jK R))).pull (𝟙 t'.G.left)) :=
    LBIso.chartPull (Geo.Tor.chartPullId _) (Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl) hL
  obtain ⟨v, hv⟩ := hL'
  have : IsMonHom (Iso.refl t'.G).hom := inferInstanceAs (IsMonHom (𝟙 t'.G))
  have hid : IsGrpPullback t'.G t'.G (𝟙 _) (𝟙 t'.G.left) := isGrpPullback_of_iso (Iso.refl t'.G)
  have hA' : RelAmple t'.G t'.PP.L :=
    relAmple_pull hid.1 hM t'.PP.isLB ((isGen_iff v).1 hv) ⊤ (isAffineOpen_top _) (fun _ => trivial) hA
  have hK' : KTriv t'.G t'.PP.L := kTriv_pull hid hM t'.PP.isLB ((isGen_iff v).1 hv) hK
  have := t'.semi.smooth
  have := t'.semi.geomConnected
  have : ConnectedSpace ↥t'.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := t'.G.hom) (𝟙 _) (𝟙 _) t'.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨g, hg⟩ := exists_dim_of_preconnected t'.G.hom (Classical.arbitrary _)
  refine ⟨GenericPol.toPolAV t' g hg hp hA' hK', ⟨t'.act.toRingAct, GenericPol.rosatiAdj t'⟩, Iso.refl _,
    inferInstanceAs (IsMonHom (𝟙 t'.G)), ?_,
    fun a => ?_⟩
  · exact LBIso.chartPull (Geo.Tor.chartPullPull t'.PP.L (𝟙 _) (𝟙 _) rfl) (Geo.Tor.chartPullId _) hL
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPolAVGenericFibreOfTripleStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN
theorem _root_.GlobalTheory.T.exists_polAV_generic_fibre_of_triple : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] (t : SAB H (Sp R)), PolAt t (jK R) → letI := H.starRing; ∃ (A : PolAV (Sp (FractionRing R))) (oA : A.OAct (𝓞 E)) (gen : (Over.pullback (jK R)).obj t.G ≅ A.A), IsMonHom gen.hom ∧ LBIso (A.L.pull gen.hom.left) (t.PP.L.pull (pullback.fst t.G.hom (jK R))) ∧ ∀ x, (Over.pullback (jK R)).map (t.act.act x) ≫ gen.hom = gen.hom ≫ oA.act x := by
  first | exact @GlobalTheory.LN.exists_polAV_of_polAt | exact GlobalTheory.LN.exists_polAV_of_polAt | (intros; apply GlobalTheory.LN.exists_polAV_of_polAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RatTors
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
noncomputable section
namespace GlobalTheory.Ex.Trait

def Along {O' R : Type} [CommRing O'] [IsDomain O'] [CommRing R] [IsDomain R] (f : O' →+* R) (C : Type) [Field C]
    [Algebra (FractionRing O') C] [Algebra (FractionRing R) C] : Prop :=
  ∀ x, algebraMap (FractionRing R) C (algebraMap _ _ (f x)) = algebraMap (FractionRing O') C (algebraMap _ _ x)

def RatTors {R : Type} [CommRing R] [IsDomain R] (B : PolAV (Sp R)) (C : Type) [Field C] [Algebra (FractionRing R) C]
    (n : ℕ) : Prop :=
  ∀ x : TF (R := R) C ⟶ B.A, x ^ n = 1 → ∃ x₀ : TK R ⟶ B.A, x.left = jFK (R := R) C ≫ x₀.left

def wVal {R O' : Type} [CommRing R] [IsDomain R] [CommRing O'] [IsDomain O'] {P : DegPre R} {D₀ : DegPre O'} {C : Type}
    [Field C] [Algebra (FractionRing R) C] [Algebra (FractionRing O') C] {N' N : NumD C} (ν' : NumOf P C N')
    (ν : NumOf D₀ C N) {ψ : P.P.A.left ⟶ D₀.P.A.left} (w : LB.Iso P.P.L (D₀.P.L.pull ψ)) (x : N'.A) : C :=
  valF (ν'.eA x).left _ (w.s (fun _ => ν.J ((ν'.eA x).left ≫ ψ), ν'.J (ν'.eA x).left)).val
section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}
  {a : ArcIn D l β O' b} {C : Type} [NontriviallyNormedField C] [Algebra (FractionRing O') C]

def Labels (A : Lift a C) (u : Cˣ) (r : ℕ → Cˣ) {o : Full D C} (M : Mdl o) {N' : NumD C} (ν' : NumOf M.P.D.toPre C N')
    (J : NumD.Iso (A.N.twist A.be u) N') (k : ℕ) : Prop :=
  ∀ x (p : (A.N.twist A.be u).QT k) (q' : N'.QT k) p' z, TwRel A.be u (r k) (A.q _ x) p →
    q'.1.1.toAdd = J.e p.1.1.toAdd → J.Rel p.1.2 q'.1.2 → ν'.QPt p' q' → z.left = (o.I.ev k x).left ≫ M.φ →
    M.P.ToA C k p' z

def Fit (A : Lift a C) (u : Cˣ) {o : Full D C} (M : Mdl o) (f : O' →+* M.W) {N' : NumD C} (ν' : NumOf M.P.D.toPre C N')
    (J : NumD.Iso (A.N.twist A.be u) N') (ψ : M.P.D.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (w : LB.Iso M.P.D.toPre.P.L (a.D₀.P.L.pull ψ)) (e : a.D₀.X ≃ₗ[𝓞 E] M.P.D.toPre.X) : Prop :=
  IsGrpPullback M.P.D.toPre.P.A a.D₀.P.A (spMap f) ψ ∧ w.IsGen ∧
    (∀ x : A.N.A, (ν'.eA (J.φ x)).left ≫ ψ = (A.ν.eA x).left) ∧ (∀ y : A.N.X, e (A.ν.eX y) = ν'.eX (J.e y)) ∧
    (∀ x, wVal ν' A.ν w x ≠ 0) ∧ ∀ x : A.N.A, (J.h x : C) * wVal ν' A.ν w (J.φ x) = wVal ν' A.ν w 1
end

def AllS (P : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}
    (a : ArcIn D l β O' b) {C : Type} [NontriviallyNormedField C] [Algebra (FractionRing O') C] (A : Lift a C) (u : Cˣ)
    (_ : ℕ → Cˣ) {o : Full D C} (M : Mdl o) (_ : O' →+* M.W) {N' : NumD C} (_ : NumOf M.P.D.toPre C N'),
    NumD.Iso (A.N.twist A.be u) N' → Prop) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (c : Coeff l)
    (O : Type) [CommRing O] (β : O →+* c.F) (O' : Type) [CommRing O'] [IsDomain O'] [IsNoetherianRing O'] (b : O →+* O')
    (a : ArcIn D l β O' b) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C]
    [CharZero C] [Algebra (FractionRing O') C] (A : Lift a C) (u : Cˣ) (r : ℕ → Cˣ) (o : Full D C) (M : Mdl o)
    (f : O' →+* M.W) (N' : NumD C) (ν' : NumOf M.P.D.toPre C N') (J : NumD.Iso (A.N.twist A.be u) N'),
    Roots u r → Along f C → P a A u r M f ν' J
end GlobalTheory.Ex.Trait
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteIsAlgClosedCExt
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteIsAlgClosedCExt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex

theorem exists_complete_isAlgClosed_cExt :
    ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (K : Type) [Field K] [Algebra (FractionRing W) K] [Algebra.IsAlgebraic (FractionRing W) K], ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C) (_ : Algebra (FractionRing W) C) (gam : K →+* C), (∀ x, gam (algebraMap (FractionRing W) K x) = algebraMap (FractionRing W) C x) ∧ CExt W (IsLocalRing.maximalIdeal W) C := by
  intro W _ _ _ K _ _ _
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W
  have hmax : IsLocalRing.maximalIdeal W = Ideal.span {π} := hπ.maximalIdeal_eq
  have hπm : π ∈ IsLocalRing.maximalIdeal W := hmax ▸ Ideal.mem_span_singleton_self π
  obtain ⟨C, i1, i2, i3, i4, i5, h1, h2⟩ :=
    GlobalTheory.exists_complete_isAlgClosed_of_isDiscreteValuationRing W (FractionRing W) hπ.ne_zero hπm
      (r := 1 / 2) (by norm_num) (by norm_num)
  have hle : ∀ r : W, ‖algebraMap (FractionRing W) C (algebraMap W _ r)‖ ≤ 1 :=
    fun r => (h1 _).2 ⟨r, rfl⟩
  let g : K →ₐ[FractionRing W] C := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨C, i1, i2, i3, i4, i5, g.toRingHom, fun x => g.commutes x, hle, fun r hr => ?_⟩
  rw [hmax, Ideal.mem_span_singleton] at hr
  obtain ⟨s, rfl⟩ := hr
  rw [map_mul, map_mul, norm_mul, h2]
  have := hle s
  linarith

end GlobalTheory.Ex
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteIsAlgClosedCExtStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complete_isAlgClosed_cExt' : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (K : Type) [Field K] [Algebra (FractionRing W) K] [Algebra.IsAlgebraic (FractionRing W) K], ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C) (_ : Algebra (FractionRing W) C) (gam : K →+* C), (∀ x, gam (algebraMap (FractionRing W) K x) = algebraMap (FractionRing W) C x) ∧ CExt W (IsLocalRing.maximalIdeal W) C := by
  first | exact @GlobalTheory.Ex.exists_complete_isAlgClosed_cExt | exact GlobalTheory.Ex.exists_complete_isAlgClosed_cExt | (intros; apply GlobalTheory.Ex.exists_complete_isAlgClosed_cExt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsFib
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.Ex.AbPartIso
variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {N N' : NumD F}

def HomF (φ : TF (R := R) F ⊗ D.P.A ≅ TF (R := R) F ⊗ D'.P.A) : Prop :=
  φ.hom ≫ fst _ _ = fst _ _ ∧ ∀ (Z : Over (Sp R)) (t : Z ⟶ TF (R := R) F) (x y : Z ⟶ D.P.A),
    lift t (x * y) ≫ φ.hom ≫ snd _ _ = (lift t x ≫ φ.hom ≫ snd _ _) * (lift t y ≫ φ.hom ≫ snd _ _)

abbrev BunIso (φ : TF (R := R) F ⊗ D.P.A ≅ TF (R := R) F ⊗ D'.P.A) : Type :=
  LB.Iso (D.P.L.pull (snd (TF (R := R) F) D.P.A).left) (D'.P.L.pull (φ.hom ≫ snd (TF (R := R) F) D'.P.A).left)

def Carries (ν : NumOf D F N) (ν' : NumOf D' F N') (φ : TF (R := R) F ⊗ D.P.A ≅ TF (R := R) F ⊗ D'.P.A)
    (x : N.A) (x' : N'.A) : Prop :=
  lift (𝟙 _) (ν.eA x) ≫ φ.hom = lift (𝟙 _) (ν'.eA x')

def wVal (ν : NumOf D F N) (ν' : NumOf D' F N') {φ : TF (R := R) F ⊗ D.P.A ≅ TF (R := R) F ⊗ D'.P.A} (w : BunIso φ)
    (f : N.A → N'.A) (x : N.A) : F :=
  valF (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left _
    (w.s (fun _ => ν'.J (ν'.eA (f x)).left, fun _ => ν.J (ν.eA x).left)).val

def AllIso (P : ∀ {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {N N' : NumD F} (_ : NumOf D F N) (_ : NumOf D' F N') {φ : TF (R := R) F ⊗ D.P.A ≅ TF (R := R) F ⊗ D'.P.A},
    BunIso φ → (N.A → N'.A) → Prop) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]
    (N N' : NumD F) (ν : NumOf D F N) (ν' : NumOf D' F N') (φ : TF (R := R) F ⊗ D.P.A ≅ TF (R := R) F ⊗ D'.P.A)
    (w : BunIso φ) (f : N.A → N'.A), HomF φ → w.IsGen → (∀ x, Carries ν ν' φ x (f x)) → P ν ν' w f

def TorsMap {O : Type} [CommRing O] (B B' : NumB O) (m : ℕ) (c : O) (ρ : B.A → B'.A) : Prop :=
  (∀ b b', b ^ m ^ 2 = 1 → b' ^ m ^ 2 = 1 →
    ρ (b * b') = ρ b * ρ b' ∧ B'.weil (m ^ 2) (ρ b) (ρ b') = B.weil (m ^ 2) b b') ∧
  ∀ b, b ^ m ^ 2 = 1 → ρ b ^ m ^ 2 = 1 ∧ B'.uth m (ρ b) 1 = c * B.uth m b 1

def IsFib (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (Q : PolAV (Sp F))
    (Φ : Q.A.left ⟶ D.P.A.left) : Prop :=
  IsGrpPullback Q.A D.P.A (TF (R := R) F).hom Φ ∧ LBIso Q.L (D.P.L.pull Φ) ∧ Q.g = D.P.g

theorem exists_isFib (hB : PolBaseChangeSt) (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] :
    ∃ Q Φ, IsFib D F Q Φ := by
  obtain ⟨P', φ, hφ, hg, hm, ht⟩ := hB _ _ (TF (R := R) F).hom D.P
  refine ⟨P', φ, ⟨hφ, fun T x y x₀ y₀ hx hy => ?_⟩, LBIso.symm ht, hg⟩
  rw [(Over.OverMorphism.ext hx : x₀ = Out.toBase hφ.w x), (Over.OverMorphism.ext hy : y₀ = Out.toBase hφ.w y), ← hm]
  rfl

end GlobalTheory.Ex.AbPartIso
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianPartValuesOfExpansionLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianPartValuesOfExpansionLaws
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section

namespace GlobalTheory.ThetaInValues

theorem brUth_of_laws : Laws → BrUthSt := fun hL _ _ _ _ _ _ _ _ _ _ _ ν =>
  ⟨fun _ _ _ _ hb hb' => weilIs_weil ν hL.globalFns hb hb', fun _ hm hF _ _ hb =>
    ⟨isThetaPt_uth ν hL.globalFns hm hF hb, isCoordPt_uth ν hL.globalFns hm hF hb⟩⟩

end GlobalTheory.ThetaInValues
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianPartValuesOfExpansionLawsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianPartValues_of_expansionLaws : Laws → BrUthSt := by
  first | exact @GlobalTheory.ThetaInValues.brUth_of_laws | exact GlobalTheory.ThetaInValues.brUth_of_laws | (intros; apply GlobalTheory.ThetaInValues.brUth_of_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsStrict
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.ModelData

def Labels {O : Type} [CommRing O] (N : NumD O) {La : Type} [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La)
    (ζ : ℕ → Oˣ) (lab : ∀ k : ℕ, La → N.QT k) : Prop :=
  (∀ k, 0 < k → ∀ a b, N.QEq (lab k a * lab k b) (lab k (a + b))) ∧
  (∀ k, 0 < k → ∀ a b, N.QEq (lab k a) (lab k b) ↔ ∃ e, a = b + k • e) ∧
  (∀ k, 0 < k → ∀ p, ∃ a, N.QEq (lab k a) p) ∧
  (∀ k m, 0 < k → 0 < m → ∀ a (p : N.QT k), p.1.1 = (lab (k * m) a).1.1 → p.1.2 = (lab (k * m) a).1.2 ^ m →
    N.QEq p (lab k a)) ∧
  ∀ k, 0 < k → ∀ a b, N.wp (lab k a) (lab k b) = ζ k ^ EF a b

def Strict {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F)) : Prop :=
  ∃ c : L.ι → L'.ι, ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι), F (r z) ∈ L.U j →
    r z ∈ L'.U (c j) ∧ gw w r z j (c j) = 1

theorem exists_strict {X X' : Scheme.{0}} {L : LB X} (hL : L.IsLB) (F : X' ⟶ X) :
    ∃ w : LB.Iso (L.pull F) (L.pull F), w.IsGen ∧ Strict w := by
  have hL' := pull_isLB hL F
  refine ⟨⟨fun j => (L.pull F).g j.1 j.2⟩, (isGen_iff _).2 fun Y f y j j' k k' hj hj' hk hk' => ?_,
    fun j _ => j, fun Z r z j hj => ⟨mem_pull.2 hj, gm_self hL' r z (mem_pull.2 hj)⟩⟩
  have a := gm_cocycle hL' f y (i := fun _ => j) (j := fun _ => j') (k := k') (mem_pull.2 hj) (mem_pull.2 hj') hk'
  have b := gm_cocycle hL' f y (i := fun _ => j) (j := k) (k := k') (mem_pull.2 hj) hk hk'
  have c := gm_pull_g L F f y (fun _ => j) (fun _ => j') (mem_pull.2 hj) (mem_pull.2 hj')
  rw [c, ← b] at a
  show gm f y _ ((L.pull F).g (fun _ => j) k) = _ * _ * gm f y _ ((L.pull F).g (fun _ => j') k')
  rw [mul_right_comm, a, mul_inv_cancel_right]

end GlobalTheory.ModelData
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FullTorsionObjectExistsUniqueModuliPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FullTorsionObjectExistsUniqueModuliPoint
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

theorem GlobalTheory.FullPoint.fullAt_iff {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
    {K : Type} [Field K] (y : Sp K ⟶ Xo.XF c) (o : Full D K) :
    FullAt Y y o ↔ FullPoint.IsFibre Y.oF y o ∧ ∀ f : KA l →+* K, y ≫ pullback.fst _ _ ≫ Xo.s = spMap f →
      o.ρ = f (baseKA l).ρ ∧ (o.I.ζ l.A : K) = f (baseKA l).ζ :=
  ⟨fun ⟨φ, a, b, c, d, e, f⟩ => ⟨⟨φ, a, b, c, d, e⟩, f⟩, fun ⟨⟨φ, a, b, c, d, e⟩, f⟩ => ⟨φ, a, b, c, d, e, f⟩⟩

theorem GlobalTheory.FullPoint.fullAt_existsUnique_exists_ext : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype), ∀ (K : Type) [Field K] [IsAlgClosed K] (bF : c.F →+* K), (∀ o : Full D K, (∀ r : c.F, (r : ℂ) = H.rt0 → o.ρ = bF r) → (∀ z : c.F, (z : ℂ) = zeta l.A → (o.I.ζ l.A : K) = bF z) → ∃! y : Sp K ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap bF ∧ FullAt Y y o) ∧ (∀ y : Sp K ⟶ Xo.XF c, ∃ o, FullAt Y y o) ∧ ∀ (K' : Type) [Field K'] (f : K →+* K') y o o', FullAt Y y o → FullExt f o o' → FullAt Y (spMap f ≫ y) o' := by
  intro hv _ _ _ _ _ _ E _ _ _ H D l Xo c W₀ Y K _ _ bF
  refine ⟨fun o hρ hζ => ?_, fun y => ?_, fun K' _ f y o o' h h' => ?_⟩
  · obtain ⟨y, ⟨h₁, h₂⟩, hu⟩ := FullPoint.existsUnique_point hv.1.1 Y bF o hρ hζ
    refine ⟨y, ⟨h₁, (FullPoint.fullAt_iff Y y o).2 ⟨h₂, fun f hf => ?_⟩⟩,
      fun y' h => hu y' ⟨h.1, ((FullPoint.fullAt_iff Y y' o).1 h.2).1⟩⟩
    rw [pullback.condition, ← Category.assoc, h₁, ← spMap_comp] at hf
    obtain rfl := FullPoint.spMap_inj hf
    exact ⟨hρ _ rfl, hζ _ rfl⟩
  · obtain ⟨o, h⟩ := FullPoint.exists_isFibre Y.oF y
    exact ⟨o, (FullPoint.fullAt_iff Y y o).2 h⟩
  · obtain ⟨hρ, hζ, ψ, g₁, g₂, g₃, g₄⟩ := h'
    obtain ⟨h₁, h₂⟩ := (FullPoint.fullAt_iff Y y o).1 h
    refine (FullPoint.fullAt_iff Y _ o').2 ⟨FullPoint.IsFibre.ext f h₁ ψ g₁ g₂ g₃ g₄, fun g hg => ?_⟩
    obtain ⟨j, hj⟩ : ∃ j : KA l →+* K, y ≫ pullback.fst _ _ ≫ Xo.s = spMap j :=
      ⟨(Spec.preimage (y ≫ pullback.fst _ _ ≫ Xo.s)).hom, (Spec.map_preimage _).symm⟩
    rw [Category.assoc, hj, ← spMap_comp] at hg
    obtain rfl := FullPoint.spMap_inj hg
    rw [hρ, hζ _ l.A_pos, (h₂ j hj).1, (h₂ j hj).2]
    exact ⟨rfl, rfl⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FullTorsionObjectExistsUniqueModuliPointStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fullTorsionObject_existsUnique_moduliPoint : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype), ∀ (K : Type) [Field K] [IsAlgClosed K] (bF : c.F →+* K), (∀ o : Full D K, (∀ r : c.F, (r : ℂ) = H.rt0 → o.ρ = bF r) → (∀ z : c.F, (z : ℂ) = zeta l.A → (o.I.ζ l.A : K) = bF z) → ∃! y : Sp K ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap bF ∧ FullAt Y y o) ∧ (∀ y : Sp K ⟶ Xo.XF c, ∃ o, FullAt Y y o) ∧ ∀ (K' : Type) [Field K'] (f : K →+* K') y o o', FullAt Y y o → FullExt f o o' → FullAt Y (spMap f ≫ y) o' := by
  first | exact @GlobalTheory.FullPoint.fullAt_existsUnique_exists_ext | exact GlobalTheory.FullPoint.fullAt_existsUnique_exists_ext | (intros; apply GlobalTheory.FullPoint.fullAt_existsUnique_exists_ext <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcTorsionValuesNormsIntegralPositive
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcTorsionValuesNormsIntegralPositive
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
noncomputable section
namespace GlobalTheory.Ex.UnitNorm

theorem norms_of_arc_input : AllA fun {_} _ _ _ {_} {_} {_} {_} {_} {_} _ {O'} _ _ {_} a => ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [Algebra (FractionRing O') C], CExt O' ⊥ C → ∀ A : Lift a C, A.ν.IntN → (∀ χ, ‖(A.N.ψ χ : C)‖ = 1) ∧ (∀ m, Odd m → ∀ (p : A.N.QT (m ^ 2)) χ, ‖A.N.txT m p χ‖ ≤ 1) ∧ ∀ u : Cˣ, ‖(u : C)‖ < 1 → ∃ q : QuadraticMap ℤ A.N.X ℝ, (A.N.twist A.be u).Int q ∧ ∀ y, q y = -Real.log ‖(u : C)‖ * (A.be.be y y / 2) := by
  intro E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a _ C _ _ _ hC A ⟨S, hS, hν⟩
  obtain ⟨s, hs⟩ := exists_base hS hC.1
  have hθ := norm_θ hS hν hs
  have hσ := norm_σ hS hν hs
  have hth := norm_th hS hν hs
  have hψ := fun χ => norm_ψ hS hν hs χ (a.gen _)
  exact ⟨hψ, fun m hm p χ => norm_txT A.N hθ hσ hψ hth hm.pos.ne' p χ, twist_int A.N hθ hσ hψ hth A.be⟩

end GlobalTheory.Ex.UnitNorm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcTorsionValuesNormsIntegralPositiveStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arcTorsionValues_norms_integral_positive : AllA fun {_} _ _ _ {_} {_} {_} {_} {_} {_} _ {O'} _ _ {_} a => ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [Algebra (FractionRing O') C], CExt O' ⊥ C → ∀ A : Lift a C, A.ν.IntN → (∀ χ, ‖(A.N.ψ χ : C)‖ = 1) ∧ (∀ m, Odd m → ∀ (p : A.N.QT (m ^ 2)) χ, ‖A.N.txT m p χ‖ ≤ 1) ∧ ∀ u : Cˣ, ‖(u : C)‖ < 1 → ∃ q : QuadraticMap ℤ A.N.X ℝ, (A.N.twist A.be u).Int q ∧ ∀ y, q y = -Real.log ‖(u : C)‖ * (A.be.be y y / 2) := by
  first | exact @GlobalTheory.Ex.UnitNorm.norms_of_arc_input | exact GlobalTheory.Ex.UnitNorm.norms_of_arc_input | (intros; apply GlobalTheory.Ex.UnitNorm.norms_of_arc_input <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsSemiAbelianOfRetract
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem isSemiAbelian_of_retract : ∀ (S : Scheme.{0}) (G G₁ : Over S) [GrpObj G] [GrpObj G₁], IsSemiAbelian G → SmConn G₁ → ∀ (i : G₁ ⟶ G) (r : G ⟶ G₁), IsMonHom r → i ≫ r = 𝟙 G₁ → IsSemiAbelian G₁ := by
  intro S G G₁ _ _ hG h₁ i r hr hir
  obtain ⟨hc, hs, hsep, hq, hg⟩ := h₁
  refine ⟨hc, hs, hsep, hq, hg, fun Ω _ _ p => ?_⟩
  have h₂ : SmConn ((Over.pullback p).obj G₁) := by
    refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
    · show Smooth (pullback.snd G₁.hom p); infer_instance
    · show IsSeparated (pullback.snd G₁.hom p); infer_instance
    · show QuasiCompact (pullback.snd G₁.hom p); infer_instance
    · show GeometricallyConnected (pullback.snd G₁.hom p); infer_instance
  refine GlobalTheory.T.nonempty_torusExtension_of_surjective_points' Ω ((Over.pullback p).obj G) ((Over.pullback p).obj G₁) h₂ (hG.fibres Ω p)
    ((Over.pullback p).map r) inferInstance fun y => ⟨y ≫ (Over.pullback p).map i, ?_⟩
  rw [Category.assoc, ← Functor.map_comp, hir, CategoryTheory.Functor.map_id, Category.comp_id]

end GlobalTheory.SS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FullTorsionPolarizedCMObjectExtendsAlgClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FullTorsionPolarizedCMObjectExtendsAlgClosed
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.FullExtend

theorem main : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllD fun D => ∀ (K K' : Type) [Field K] [IsAlgClosed K] [CharZero K] [Field K'] [IsAlgClosed K'] (f : K →+* K') (o : Full D K), ∃ o' : Full D K', FullExt f o o' ∧ (∀ m v, o.Theta m v → o'.Theta m fun x => f (v x)) ∧ ∀ m j z v, 0 < j → o.Coord m (o.I.ev j z) v → o'.Coord m (o'.I.ev j z) fun x => f (v x) := by
  intro hV _ _ _ _ _ _ E _ _ _ H D K K' _ _ _ _ _ f o
  obtain ⟨o', h₁, h₂, h₃⟩ := exists_fullExt hV.1.1 D f o
  exact ⟨o', h₁, h₂, fun m j z v _ => h₃ m j z v⟩

end GlobalTheory.FullExtend
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FullTorsionPolarizedCMObjectExtendsAlgClosedStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fullTorsionPolarizedCMObject_extends_algClosed : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllD fun D => ∀ (K K' : Type) [Field K] [IsAlgClosed K] [CharZero K] [Field K'] [IsAlgClosed K'] (f : K →+* K') (o : Full D K), ∃ o' : Full D K', FullExt f o o' ∧ (∀ m v, o.Theta m v → o'.Theta m fun x => f (v x)) ∧ ∀ m j z v, 0 < j → o.Coord m (o.I.ev j z) v → o'.Coord m (o'.I.ev j z) fun x => f (v x) := by
  first | exact @GlobalTheory.FullExtend.main | exact GlobalTheory.FullExtend.main | (intros; apply GlobalTheory.FullExtend.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymmetricSpreadOutLineBundleAbelianScheme
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymmetricSpreadOutLineBundleAbelianScheme
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenSpread

theorem pull_inv_cls_iff {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB)
    (hL' : L'.IsLB) (e : LBIso L' (L.pull φ)) :
    CechPic.pull (GrpObj.inv : G' ⟶ G').left (CechPic.cls L' hL') = CechPic.cls L' hL' ↔
      LBIso ((L.pull (GrpObj.inv : G ⟶ G).left).pull φ) (L.pull φ) := by
  rw [← CechPic.cls_eq_iff (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _),
    (CechPic.cls_eq_iff hL' (pull_isLB hL _)).2 e, CechPic.cls_pull hL, CechPic.cls_pull (pull_isLB hL _),
    CechPic.cls_pull hL, ← CechPic.pull_comp, ← CechPic.pull_comp, OddDescent.inv_left_comp h]

theorem exists_sym : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (φ : A.left ⟶ G.left) (L : LB G.left) (L₀ : LB A.left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap R K)) φ → L.IsLB → L₀.IsLB → LBIso L₀ (L.pull φ) → Out.Sym A L₀ → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (π : G'.left ⟶ G.left) (L' : LB G'.left), IsGrpPullback G' G (spMap g) π → L'.IsLB → LBIso L' (L.pull π) → Out.Sym G' L' := by
  intro R K _ _ _ _ _ _ G _ _ A _ _ φ L L₀ hG h hL hL₀ e hs
  have := hG.proper
  obtain ⟨a, ha, H⟩ := exists_lbIso G.hom h.1 (pull_isLB hL _) hL
    ((pull_inv_cls_iff h hL hL₀ e).1 (OddDescent.pull_inv_cls_of_sym A hL₀ hs))
  exact ⟨a, ha, fun R' _ g hg G' _ _ π L' h' hL' e' => OddDescent.sym_of_pull_inv_cls G' hL'
    ((pull_inv_cls_iff h' hL hL' e').2 (H R' g hg _ π G'.hom h'.1.w))⟩

end GlobalTheory.GenSpread
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymmetricSpreadOutLineBundleAbelianSchemeStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symmetric_spread_out_lineBundle_abelian_scheme : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (φ : A.left ⟶ G.left) (L : LB G.left) (L₀ : LB A.left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap R K)) φ → L.IsLB → L₀.IsLB → LBIso L₀ (L.pull φ) → Out.Sym A L₀ → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (π : G'.left ⟶ G.left) (L' : LB G'.left), IsGrpPullback G' G (spMap g) π → L'.IsLB → LBIso L' (L.pull π) → Out.Sym G' L' := by
  first | exact @GlobalTheory.GenSpread.exists_sym | exact GlobalTheory.GenSpread.exists_sym | (intros; apply GlobalTheory.GenSpread.exists_sym <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolAVDescendsToCountableSubfield
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolAVDescendsToCountableSubfield
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PolCountableDescent

theorem countable_closure {K : Type} [Field K] (s : Finset K) :
    Countable (Subfield.closure (s : Set K)) := by
  rw [← Cardinal.mk_le_aleph0_iff]
  refine (Subfield.cardinalMk_closure_le_max _).trans ?_
  exact max_le (Cardinal.mk_le_aleph0_iff.2 s.countable_toSet.to_subtype) le_rfl

theorem subset_closure_of_subset {K : Type} [Field K] {s s' : Finset K} (h : s ⊆ s') :
    (s : Set K) ⊆ Subfield.closure (s' : Set K) :=
  fun _ hx => Subfield.subset_closure (h hx)

theorem spMap_subtype_comp {K : Type} [Field K] {K₀ K₁ : Subfield K} (h : K₀ ≤ K₁) :
    spMap K₁.subtype ≫ spMap (Subfield.inclusion h) = spMap K₀.subtype := by
  rw [← Spec.map_comp]; rfl

theorem polAV_descends_to_countable_subfield :
    ∀ (K : Type) [Field K] (P : PolAV (Sp K)) (J I : Type) [Finite J] [Finite I] (a : J → (P.A ⟶ P.A)) (x : I → (𝟙_ (Over (Sp K)) ⟶ P.A)), ∃ (K₀ : Subfield K) (P₀ : PolAV (Sp K₀)) (Φ : P.A.left ⟶ P₀.A.left) (a₀ : J → (P₀.A ⟶ P₀.A)) (x₀ : I → (𝟙_ (Over (Sp K₀)) ⟶ P₀.A)), Countable K₀ ∧ IsGrpPullback P.A P₀.A (spMap K₀.subtype) Φ ∧ LBIso P.L (P₀.L.pull Φ) ∧ (∀ j, (a j).left ≫ Φ = Φ ≫ (a₀ j).left) ∧ ∀ i, (x i).left ≫ Φ = spMap K₀.subtype ≫ (x₀ i).left := by
  intro K _ P J I _ _ a x
  classical
  obtain ⟨s₀, H₀⟩ := GlobalTheory.exists_finset_isProjOver_descends K ⊥ P.A.left P.A.hom
    (GlobalTheory.ProjSpace.isProjOver_of_relAmple P.ample)
  let K₀ : Subfield K := Subfield.closure (s₀ : Set K)
  obtain ⟨X₀, p₀, φ, hp₀, sq⟩ := H₀ K₀ bot_le Subfield.subset_closure
  have : IsProper p₀ := by
    obtain ⟨N, i, hi, rfl⟩ := hp₀
    have := isProper_str K₀ N
    infer_instance
  have : LocallyOfFinitePresentation p₀ := inferInstance
  have : QuasiCompact (Over.mk p₀).hom := inferInstanceAs (QuasiCompact p₀)
  have : QuasiSeparated (Over.mk p₀).hom := inferInstanceAs (QuasiSeparated p₀)
  have : LocallyOfFinitePresentation (Over.mk p₀).hom := inferInstanceAs (LocallyOfFinitePresentation p₀)
  obtain ⟨s₁, H₁⟩ := GlobalTheory.grpObj_descends_to_large_subfield K K₀ (Over.mk p₀) P.A φ sq
  obtain ⟨s₂, H₂⟩ := GlobalTheory.LBDescent.exists_lb_subfield K K₀ X₀ P.A.left p₀ P.A.hom φ P.L P.isLB sq
  obtain ⟨s₃, H₃⟩ := GlobalTheory.morphisms_descend_to_large_subfield K K₀ X₀ P.A.left p₀ P.A.hom φ X₀ p₀ J
    (fun j => (a j).left ≫ φ) sq
    (fun j => by rw [Category.assoc, sq.w, ← Category.assoc, Over.w])
  obtain ⟨s₄, H₄⟩ := GlobalTheory.morphisms_descend_to_large_subfield K K₀ (Sp K₀) (Sp K) (𝟙 _) (𝟙 _)
    (spMap K₀.subtype) X₀ p₀ I (fun i => (x i).left ≫ φ) (IsPullback.of_vert_isIso ⟨by simp⟩)
    (fun i => by
      have e : (x i).left ≫ P.A.hom = 𝟙 _ := Over.w (x i)
      rw [Category.assoc, sq.w, ← Category.assoc, e]; simp)
  let s : Finset K := s₀ ∪ s₁ ∪ s₂ ∪ s₃ ∪ s₄
  let K₁ : Subfield K := Subfield.closure (s : Set K)
  have h : K₀ ≤ K₁ := Subfield.closure_mono (Finset.coe_subset.2 (fun y hy => by simp [s, hy]))
  let inc := spMap (Subfield.inclusion h)
  let A₁ : Over (Sp K₁) := Over.mk (pullback.snd p₀ inc)
  let φ₁ : A₁.left ⟶ X₀ := pullback.fst p₀ inc
  have sq₁ : IsPullback φ₁ A₁.hom p₀ inc := IsPullback.of_hasPullback p₀ inc
  let ψ : P.A.left ⟶ A₁.left := sq₁.lift φ (P.A.hom ≫ spMap K₁.subtype)
    (by rw [Category.assoc, spMap_subtype_comp h, sq.w])
  have hψ₁ : ψ ≫ φ₁ = φ := sq₁.lift_fst _ _ _
  have hψ₂ : ψ ≫ A₁.hom = P.A.hom ≫ spMap K₁.subtype := sq₁.lift_snd _ _ _
  obtain ⟨gr₁, hG⟩ := H₁ K₁ h (subset_closure_of_subset (fun y hy => by simp [s, hy])) A₁ φ₁ ψ sq₁ hψ₁ hψ₂
  obtain ⟨L₁, hL₁, hL⟩ := H₂ K₁ h (subset_closure_of_subset (fun y hy => by simp [s, hy])) A₁.left A₁.hom φ₁ ψ
    sq₁ hψ₁ hψ₂
  obtain ⟨f₁, hf₁⟩ := H₃ K₁ h (subset_closure_of_subset (fun y hy => by simp [s, hy])) A₁.left A₁.hom φ₁ ψ
    sq₁ hψ₁ hψ₂
  obtain ⟨x₁, hx₁⟩ := H₄ K₁ h (subset_closure_of_subset (fun y hy => by simp [s, hy])) (Sp K₁) (𝟙 _) inc
    (spMap K₁.subtype) (IsPullback.of_vert_isIso ⟨by simp [inc]⟩) (spMap_subtype_comp h) (by simp)
  let act₁ : J → (A₁ ⟶ A₁) := fun j =>
    Over.homMk (sq₁.lift (f₁ j) A₁.hom (by rw [(hf₁ j).2, sq₁.w])) (sq₁.lift_snd _ _ _)
  let pt₁ : I → (𝟙_ (Over (Sp K₁)) ⟶ A₁) := fun i =>
    Over.homMk (sq₁.lift (x₁ i) (𝟙 _) (by rw [(hx₁ i).2]; simp)) (sq₁.lift_snd _ _ _)
  obtain ⟨hab, hdim⟩ := GlobalTheory.FieldDescentAb.isAbelianScheme_and_relDim_descend K₁ K K₁.subtype A₁ P.A ψ hG P.isAb
  obtain ⟨hrig, hsym, hkt⟩ := GlobalTheory.PolDescent.rigidified_sym_kTriv_descend K₁ K K₁.subtype A₁ P.A ψ L₁ P.L
    hab hG hL₁ P.isLB hL
  have hamp := GlobalTheory.AmpleDescent.relAmple_of_fieldExtension K₁ K K₁.subtype A₁ P.A ψ L₁ P.L
    hab hG hL₁ P.isLB hL P.ample
  let P₁ : PolAV (Sp K₁) :=
    { A := A₁, grp := gr₁, isAb := hab, g := P.g, smoothDim := hdim P.g P.smoothDim, L := L₁,
      isLB := hL₁, rigid := hrig P.rigid, sym := hsym P.sym, ample := hamp, ktriv := hkt P.ktriv }
  refine ⟨K₁, P₁, ψ, act₁, pt₁, countable_closure s, hG, hL, fun j => ?_, fun i => ?_⟩
  · change (a j).left ≫ ψ = ψ ≫ (act₁ j).left
    have e₁ : (act₁ j).left ≫ φ₁ = f₁ j := sq₁.lift_fst _ _ _
    apply sq₁.hom_ext
    · rw [Category.assoc, hψ₁, Category.assoc, e₁, (hf₁ j).1]
    · rw [Category.assoc, hψ₂, ← Category.assoc, Over.w, Category.assoc, Over.w, hψ₂]
  · change (x i).left ≫ ψ = spMap K₁.subtype ≫ (pt₁ i).left
    have e : (x i).left ≫ P.A.hom = 𝟙 _ := Over.w (x i)
    have e₁ : (pt₁ i).left ≫ φ₁ = x₁ i := sq₁.lift_fst _ _ _
    have e₂ : (pt₁ i).left ≫ A₁.hom = 𝟙 _ := sq₁.lift_snd _ _ _
    apply sq₁.hom_ext
    · rw [Category.assoc, hψ₁]
      exact ((hx₁ i).1.symm.trans (congrArg _ e₁.symm)).trans (Category.assoc _ _ _).symm
    · rw [Category.assoc, hψ₂, ← Category.assoc, e]
      refine (Category.id_comp _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
      exact ((congrArg _ e₂).trans (Category.comp_id _)).symm

end GlobalTheory.PolCountableDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolAVDescendsToCountableSubfieldStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polAV_descends_to_countable_subfield' : ∀ (K : Type) [Field K] (P : PolAV (Sp K)) (J I : Type) [Finite J] [Finite I] (a : J → (P.A ⟶ P.A)) (x : I → (𝟙_ (Over (Sp K)) ⟶ P.A)), ∃ (K₀ : Subfield K) (P₀ : PolAV (Sp K₀)) (Φ : P.A.left ⟶ P₀.A.left) (a₀ : J → (P₀.A ⟶ P₀.A)) (x₀ : I → (𝟙_ (Over (Sp K₀)) ⟶ P₀.A)), Countable K₀ ∧ IsGrpPullback P.A P₀.A (spMap K₀.subtype) Φ ∧ LBIso P.L (P₀.L.pull Φ) ∧ (∀ j, (a j).left ≫ Φ = Φ ≫ (a₀ j).left) ∧ ∀ i, (x i).left ≫ Φ = spMap K₀.subtype ≫ (x₀ i).left := by
  first | exact @GlobalTheory.PolCountableDescent.polAV_descends_to_countable_subfield | exact GlobalTheory.PolCountableDescent.polAV_descends_to_countable_subfield | (intros; apply GlobalTheory.PolCountableDescent.polAV_descends_to_countable_subfield <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenericSquare
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section

namespace GlobalTheory.ClosedPol

theorem exists_fibre_pull (laws : Laws) {S S' Z Z' : Scheme.{0}} {j : Z ⟶ S} {j' : Z' ⟶ S'} {f : S' ⟶ S} {ψ : Z' ⟶ Z}
    (sq : ψ ≫ j = j' ≫ f) {G : Over S} [GrpObj G] {L : LB G.left} (hL : L.IsLB) (A : PolAV Z)
    (gen : (Over.pullback j).obj G ≅ A.A) [IsMonHom gen.hom]
    (hA : LBIso (A.L.pull gen.hom.left) (L.pull (pullback.fst G.hom j))) :
    ∃ (A' : PolAV Z') (gen' : (Over.pullback j').obj ((Over.pullback f).obj G) ≅ A'.A),
      IsMonHom gen'.hom ∧ LBIso (A'.L.pull gen'.hom.left) ((L.pull (pullback.fst G.hom f)).pull
        (pullback.fst ((Over.pullback f).obj G).hom j')) := by
  obtain ⟨A', g, hg, -, mul, t, ht⟩ := laws.polBaseChange _ _ ψ A
  have pg : IsGrpPullback A'.A A.A ψ g := ⟨hg, fun T x y x₀ y₀ hx hy => by
    obtain rfl : x₀ = toBase hg.w x := Over.OverMorphism.ext hx
    obtain rfl : y₀ = toBase hg.w y := Over.OverMorphism.ext hy
    exact (congrArg (fun a => a.left) (mul T x y)).symm⟩
  have : IsMonHom gen.symm.hom := inferInstanceAs (IsMonHom gen.inv)
  have h₂ := (pg.comp ((isGrpPullback_of_iso gen.symm).comp (isGrpPullback_pullback G j))).congr
    ((congrArg _ (Category.id_comp _)).trans sq) rfl
  obtain ⟨gen', hgen', e⟩ := grpPullback_iso ((isGrpPullback_pullback _ j').comp
    (isGrpPullback_pullback G f)) h₂
  have hi : gen.inv.left ≫ gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, gen.inv_hom_id, Over.id_left]
  refine ⟨A', gen', hgen', LBIso.trans (LB.isLB_pull A'.isLB _) (LB.isLB_pull (LB.isLB_pull A.isLB g) gen'.hom.left)
    (LB.isLB_pull (LB.isLB_pull hL _) _) ?_ ?_⟩
  · exact LBIso.chartPull (Geo.Tor.chartPullPull _ _ _ rfl) (Geo.Tor.chartPullPull _ _ _ rfl) (LBIso.symm ⟨t, ht⟩)
  · refine LBIso.chartPull (h := gen'.hom.left ≫ g ≫ gen.inv.left)
      (chartPullLinComb A.L g _ (fun _ : PUnit => gen.hom.left) _ _ fun _ => ?_)
      (chartPullLinComb L _ _ (fun _ : PUnit => pullback.fst G.hom j) _ _ fun _ => ?_) hA
    · rw [Category.assoc, Category.assoc, hi, Category.comp_id]
    · rw [Category.assoc, Category.assoc]
      exact e.symm

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

theorem exists_generic_square {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V]
    (φ : R →+* V) (hφ : Function.Injective φ) :
    ∃ ψ : Spec (CommRingCat.of (FractionRing V)) ⟶ Spec (CommRingCat.of (FractionRing R)),
      ψ ≫ jK R = jK V ≫ spMap φ := by
  have gen : ∀ (K F : Type) [Field K] [Field F] [Algebra R K] [IsFractionRing R K] (g : R →+* F),
      Function.Injective g → ∃ ψ : K →+* F, ψ.comp (algebraMap R K) = g := fun K F _ _ _ _ g hg =>
    ⟨IsFractionRing.lift hg, RingHom.ext fun x => IsFractionRing.lift_algebraMap hg x⟩
  obtain ⟨ψ, hψ⟩ := gen (FractionRing R) (FractionRing V) ((algebraMap V (FractionRing V)).comp φ)
    ((IsFractionRing.injective V (FractionRing V)).comp hφ)
  exact ⟨spMap ψ, (spMap_comp _ ψ).trans ((congrArg spMap hψ).trans (spMap_comp φ _).symm)⟩

theorem exists_desc_pull {S S' : Scheme.{0}} {f : S' ⟶ S} {X : Type} [AddCommGroup X] {G : Over S} {G' : Over S'}
    [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {F : G'.left ⟶ G.left} (pF : IsGrpPullback G' G f F)
    (Q : TQ G X) {P : CP G} (D : Q.Desc P) {P' : CP G'} {hw w} (k : IsCPMap P' P f F hw w) :
    ∃ (Q' : TQ G' X) (D' : Q'.Desc P') (β : Q'.B.left ⟶ Q.B.left), IsGrpPullback Q'.B Q.B f β ∧
      LBIso D'.M.L.L (D.M.L.L.pull β) := by
  obtain ⟨Q₀, hQ⟩ := exists_tq_baseChange _ _ _ X _ _ F pF Q
  obtain ⟨β, eβ, pβ⟩ := TQ.exists_isGrpPullback _ _ _ X _ _ F pF Q Q₀ hQ
  obtain ⟨M₀, v, hv⟩ := exists_pull (hw := pβ.1.w) D.M
    (fun Z x y => Over.OverMorphism.ext (pβ.2 Z x y _ _ rfl rfl).symm)
  obtain ⟨w₄, -, k₄⟩ := D.map.exists_comp k (by rw [Category.assoc, Over.w, hw, Category.comp_id])
  obtain ⟨w₅, k₅⟩ := cpMap_congr ((Category.comp_id _).trans (Category.id_comp _).symm) eβ.symm k₄
    (by rw [Category.assoc, pβ.1.w, Over.w_assoc, Category.id_comp])
  have := Q₀.q_hom
  obtain ⟨w₆, k₆, -⟩ := (isCPMap_comp_cancel _ _ _ _ _ _ _ _ _ _ P' _ _ _ Q₀.q.left (by simp) _ hv).2
    (toBase_mul_of_isMonHom Q₀.q _) w₅ k₅
  exact ⟨Q₀, ⟨M₀, w₆, k₆⟩, β, pβ, v, hv.gen⟩

theorem exists_fourth {S S' Z Z' : Scheme.{0}} {t : Z ⟶ S} {t' : Z' ⟶ S'} {f : S' ⟶ S} {b : Z' ⟶ Z}
    (sq : b ≫ t = t' ≫ f) {G : Over S} {G' : Over S'} {H : Over Z} {H' : Over Z'} [GrpObj G] [IsCommMonObj G]
    [GrpObj G'] [IsCommMonObj G'] [GrpObj H] [IsCommMonObj H] [GrpObj H'] [IsCommMonObj H']
    {F : G'.left ⟶ G.left} {c : H.left ⟶ G.left} {c' : H'.left ⟶ G'.left} (pF : IsGrpPullback G' G f F)
    (pc : IsGrpPullback H G t c) (pc' : IsGrpPullback H' G' t' c') {P : CP G} {P' : CP G'} {N : CP H} {N' : CP H'}
    {h₁ w₁ h₂ w₂ h₃ w₃} (k₁ : IsCPMap P' P f F h₁ w₁) (k₂ : IsCPMap N P t c h₂ w₂) (k₃ : IsCPMap N' P' t' c' h₃ w₃) :
    ∃ (E : H'.left ⟶ H.left) (pE : IsGrpPullback H' H b E) (w : _), IsCPMap N' N b E pE.1.w w := by
  have p := pc'.comp pF
  have w : (c' ≫ F) ≫ G.hom = (H'.hom ≫ b) ≫ t := p.1.w.trans (by rw [Category.assoc, sq])
  have e₁ := pc.1.lift_fst _ _ w
  have e₂ := pc.1.lift_snd _ _ w
  have p' := p.congr sq.symm e₁.symm
  have pE := pc.cancel p' e₂
  obtain ⟨w₄, -, k₄⟩ := k₁.exists_comp k₃ p.1.w
  obtain ⟨w₅, k₅⟩ := cpMap_congr sq.symm e₁.symm k₄ p'.1.w
  obtain ⟨w₆, k₆, -⟩ := (isCPMap_comp_cancel _ _ _ _ _ _ _ _ _ _ N' _ _ _ _ e₂ _ k₂).2
    (fun Z x y => Over.OverMorphism.ext (pE.2 Z x y _ _ rfl rfl).symm) w₅ k₅
  exact ⟨_, pE, w₆, k₆⟩

theorem exists_trait (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CharZero R] (I : Ideal R) {k : Type}
    [Field k] (a : R ⧸ I ^ (0 + 1) →+* k) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (φ : R →+* V)
      (b : R ⧸ I ^ (0 + 1) →+* V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)), CDVR V ∧ Function.Injective φ ∧
      RingHom.ker a = RingHom.ker b ∧ spMap b ≫ thick R I 0 = thick V _ 0 ≫ spMap φ := by
  have := RingHom.ker_isPrime a
  obtain ⟨V, _, _, _, φ, hV, hφ, hm⟩ := exists_cdvr R ((RingHom.ker a).comap (Ideal.Quotient.mk _))
  have hm' : (IsLocalRing.maximalIdeal V ^ (0 + 1)).comap φ = (RingHom.ker a).comap (Ideal.Quotient.mk _) := by
    rw [← hm, zero_add, pow_one]
  have le : I ^ (0 + 1) ≤ (IsLocalRing.maximalIdeal V ^ (0 + 1)).comap φ := fun r hr => by
    rw [hm', Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hr]
    exact zero_mem _
  refine ⟨V, _, ‹_›, ‹_›, φ, Ideal.quotientMap (IsLocalRing.maximalIdeal V ^ (0 + 1)) φ le, hV, hφ,
    Ideal.ext fun y => ?_, ?_⟩
  · obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← Ideal.mem_comap, ← hm', RingHom.mem_ker, Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem]
    rfl
  · rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      Ideal.quotientMap_comp_mk]


set_option maxHeartbeats 800000 in
theorem main : Laws → Laws2 → Laws3 → USt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (P : CP G), IsSemiAbelian G → HypW G P.L.L → ∀ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (T : TowerR I P X) (k : Type) [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (0 + 1)))), RelAmple ((Over.pullback x).obj (T.l 0).Q.B) ((T.l 0).D.M.L.L.pull (pullback.fst _ x)) ∧ KTriv ((Over.pullback x).obj (T.l 0).Q.B) ((T.l 0).D.M.L.L.pull (pullback.fst _ x)) := by
  intro laws _ _ hU R _ _ _ I ⟨⟨hN, _⟩, _, hc, _⟩ G _ _ P hG ⟨w, _, hw, _, _, prim, _⟩ A gen hgen hA X _ _ _ T k _ x
  obtain ⟨a, rfl⟩ : ∃ a : R ⧸ I ^ (0 + 1) →+* k, spMap a = x := ⟨(Spec.preimage x).hom, Spec.map_preimage x⟩
  obtain ⟨V, _, _, _, φ, b, hV, hφ, hab, sq⟩ := exists_trait R I a
  obtain ⟨ψ, sq'⟩ := exists_generic_square φ hφ
  obtain ⟨A', gen', hgen', hA'⟩ := exists_fibre_pull laws sq' P.L.isLB A gen hA
  obtain ⟨P', wP, hP', H⟩ := exists_cp_pull _ _ (spMap φ) G ((Over.pullback (spMap φ)).obj G) _ _
    (toBase_mul_pullback G (spMap φ)) P
  have prim' := prim_pull (spMap φ) prim
  rw [← hP'] at hA' prim'
  obtain ⟨P₀, w₀, H₀⟩ := exists_isLevelCP (IsLocalRing.maximalIdeal V) 0 P'
  obtain ⟨wl, hl⟩ := (T.l 0).lev
  obtain ⟨F, pF, w₃, k₃⟩ := exists_fourth (G := G) (G' := (Over.pullback (spMap φ)).obj G) (H := thickObj R I 0 G)
    (H' := thickObj V (IsLocalRing.maximalIdeal V) 0 ((Over.pullback (spMap φ)).obj G)) (P := P) (P' := P')
    (N := (T.l 0).Pe) (N' := P₀) sq (isGrpPullback_pullback G (spMap φ))
    (isGrpPullback_pullback G (thick R I 0)) (isGrpPullback_pullback _ (thick V (IsLocalRing.maximalIdeal V) 0)) H hl H₀
  obtain ⟨Q₀, D₀, β, pβ, hβ⟩ := exists_desc_pull pF (T.l 0).Q (T.l 0).D k₃
  have hG' : IsSemiAbelian ((Over.pullback (spMap φ)).obj G) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := hG.comm; infer_instance
    · have := hG.smooth; change Smooth (pullback.snd G.hom (spMap φ)); infer_instance
    · have := hG.separated; change IsSeparated (pullback.snd G.hom (spMap φ)); infer_instance
    · have := hG.quasiCompact; change QuasiCompact (pullback.snd G.hom (spMap φ)); infer_instance
    · have := hG.geomConnected; change GeometricallyConnected (pullback.snd G.hom (spMap φ)); infer_instance
    · intro Ω _ _ q
      obtain ⟨E⟩ := hG.fibres Ω (q ≫ spMap φ)
      let em := (Functor.mapMonNatIso (Over.pullbackComp q (spMap φ)) ≪≫ Functor.mapMonCompIso).app (Mon.mk G)
      let e : (Over.pullback (q ≫ spMap φ)).obj G ≅ (Over.pullback q).obj ((Over.pullback (spMap φ)).obj G) := (Mon.forget _).mapIso em
      haveI : IsMonHom e.hom := by
        show IsMonHom em.hom.hom
        infer_instance
      letI := E.grpB
      haveI := E.q_hom
      haveI := E.i_hom
      exact ⟨{ X := E.X
               addCommGroup := E.addCommGroup
               free := E.free
               finite := E.finite
               B := E.B
               grpB := E.grpB
               isAbelian := E.isAbelian
               q := e.inv ≫ E.q
               q_hom := inferInstance
               q_flat := by rw [Over.comp_left]; have := E.q_flat; have : IsIso e.inv.left := Functor.map_isIso (Over.forget _) e.inv; infer_instance
               q_surjective := by rw [Over.comp_left]; have := E.q_surjective; have : IsIso e.inv.left := Functor.map_isIso (Over.forget _) e.inv; infer_instance
               q_quasiCompact := by rw [Over.comp_left]; have := E.q_quasiCompact; have : IsIso e.inv.left := Functor.map_isIso (Over.forget _) e.inv; infer_instance
               i := E.i ≫ e.hom
               i_hom := inferInstance
               isKernel := by refine IsPullback.of_iso E.isKernel (Iso.refl _) e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp }⟩
  have ev := GlobalTheory.T.exists_even_cubical_trivialisation_specialFibre laws V hV A' _ hG' gen' hgen' P' ((Over.pullback (spMap φ)).map w) inferInstance
    prim' X Q₀ P₀ ⟨w₀, H₀⟩
  obtain ⟨wA, hwA⟩ := hA'
  have pol := pol_dvr laws hU
    { cdvr := hV, semi := hG', gen := gen', gen_hom := hgen', P := P', wA := wA, wA_gen := hwA, X := X, Q₀ := Q₀,
      P₀ := P₀, lev₀ := ⟨w₀, H₀⟩, even₀ := ev } D₀
  have : (IsLocalRing.maximalIdeal V ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  let _ : Field (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) := Ideal.Quotient.field _
  exact pol_of_ker_eq a b hab _ (T.l 0).Q.isAb (T.l 0).D.M.L.isLB Q₀.B pβ D₀.M.L.isLB hβ pol

end GlobalTheory.ClosedPol

end
end
