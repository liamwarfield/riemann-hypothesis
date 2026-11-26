module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow

section Translates

variable {S : Scheme.{0}} (P : PolAV S)

def IsPolAVSectionInverseImage (T : Over S) (s : P.L.Sec) (t : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T)) : Prop :=
  ∀ (i : P.L.ι) (h : (LPow P.A P.L ((1 : ℕ) : ℤ) T).U (fun _ => i) ≤ (snd T P.A).left ⁻¹ᵁ P.L.U i),
    t.f (fun _ => i) = ((snd T P.A).left.appLE _ _ h).hom (s.f i)

def Tr (ρ : LB.Gen (P.L.pull (eSec P.A))) (m : ℕ) {T : Over S} (th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T))
    (U : ThetaGrp P.A P.L ((m ^ 2 : ℕ) : ℤ) T) (t : LB.Sec (LPow P.A P.L ((m ^ 2 : ℕ) : ℤ) T)) : Prop :=
  ∃ (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]))
    (s₁ : LB.Sec (LPow P.A P.L ((m ^ 2 : ℕ) : ℤ) T)),
    α.IsGen ∧ LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ α (ptSecT P.A 1).left) (rigT P.A P.L ρ T (((m ^ 2 : ℕ) : ℤ) - 1)) ∧
    IsTwistPull P.A P.L (mulT P.A T m) (snd T P.A ^ m) (lift_snd _ _) ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α th s₁ ∧
    IsActOf P.A P.L ((m ^ 2 : ℕ) : ℤ) U s₁ t

def ThJetT (ρ : LB.Gen (P.L.pull (eSec P.A))) (m : ℕ) {B : Type} [CommRing B] (s : Sp B ⟶ S)
    (th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) (Over.mk s))) {I : Type} (pt : I → (Over.mk s ⟶ P.A)) {g : ℕ}
    (y : Fin g → (Sp (DualNumber B) ⟶ (Over.mk s ⊗ P.A).left)) (ϑ : I → B) (J : I → Fin g → B) : Prop :=
  ∃ (U : I → ThetaGrp P.A P.L ((m ^ 2 : ℕ) : ℤ) (Over.mk s)) (t : I → LB.Sec (LPow P.A P.L ((m ^ 2 : ℕ) : ℤ) (Over.mk s)))
    (i₀ : P.L.ι) (c : Fin g → B),
    (∀ i, SymLift P.A P.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) (pt i) (U i) ∧ Tr P ρ m th (U i) (t i)) ∧
    ⊤ ≤ (s ≫ eSec P.A) ⁻¹ᵁ P.L.U i₀ ∧
    ∀ i j, valR (y j) ((LPow P.A P.L ((m ^ 2 : ℕ) : ℤ) (Over.mk s)).U fun _ => i₀) ((t i).f fun _ => i₀) =
      TrivSqZeroExt.inl (valR s ((P.L.pull (eSec P.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ^ (m ^ 2)) *
        (TrivSqZeroExt.inl (ϑ i) + TrivSqZeroExt.inr (J i j + c j * ϑ i))

end Translates

def epsLift {R : Type} [CommRing R] {A : Over (Sp R)} (v : epsR R ⟶ A) :
    Sp (DualNumber R) ⟶ (baseOver (Sp R) ⊗ A).left :=
  (lift (Over.homMk (epsR R).hom (by simp) : epsR R ⟶ baseOver (Sp R)) v).left

def ThJet {R : Type} [CommRing R] (x : KeyIn R) {g : ℕ} (hg : x.P.g = g) (m : ℕ) {I : Type}
    (pt : I → (baseOver (Sp R) ⟶ x.P.A)) (ϑ : I → R) (J : I → Fin g → R) : Prop :=
  ∃ th, IsPolAVSectionInverseImage x.P (baseOver (Sp R)) x.th th ∧
    ThJetT x.P x.rig m (𝟙 (Sp R)) th pt (fun j => epsLift (x.v (j.cast hg.symm))) ϑ J

def Rule4 (κ : Rule) : Prop := Homog (fun _ => 1) κ ∧ Funct κ ∧ ThetaOne κ ∧ FamUnit κ

def KapF (κ : Rule) : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (IsLocalRing.maximalIdeal V) V → Finite (IsLocalRing.ResidueField V) →
    ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (x : KeyIn (FractionRing V)) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G],
    IsSemiAbelian G → ∀ (U : Unif (IsLocalRing.maximalIdeal V) D x.P G) (w₀ : GlobalTheory.UT.W0 U.toUnifPre),
    GlobalTheory.UT.NormW U.toUnifPre w₀ x.rig → ∀ y : Fin x.P.g → (epsR V ⟶ G), IsLieBasis y →
    (∀ i, IsVecOver (algebraMap V (FractionRing V)) (U.gen.inv.left ≫ pullback.fst G.hom (jK V)) (y i) (x.v i)) →
    ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C]
      [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → Nonempty (C ≃+* ℂ) →
    ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → ∀ (th : GlobalTheory.UT.SecA x.P C 1) (ϑ : Fam D.toPre C 1) (c : C),
      IsPolAVSectionInverseImage x.P (TFK (R := V) C) x.th th → U.ExpandsF C 1 w₀ th ϑ → ν.FamV ϑ (c • N.vth) →
      ‖c‖ ^ 8 * ‖algebraMap (FractionRing V) C (κ (FractionRing V) x : FractionRing V)‖ = 1

def Deform (κ : Rule) {C : Type} [NormedField C] [CharZero C] (e : C →+* ℂ) (x : KeyIn C) {g : ℕ} (hg : x.P.g = g) (m : ℕ)
    (ζ : Cˣ) (lev : Out.Level x.P (m ^ 2) (unitOn ζ)) (k : C) : Prop :=
  ∃ (Θ : (Fin (2 * g) → ZMod (m ^ 2)) → PowerSeries C) (Γ : (Fin (2 * g) → ZMod (m ^ 2)) → Fin g → PowerSeries C) (π : C) (b : ℝ),
    ‖π‖ < 1 ∧ (∀ a n, ‖PowerSeries.coeff n (Θ a)‖ ≤ b ∧ ∀ j, ‖PowerSeries.coeff n (Γ a j)‖ ≤ b) ∧
    ThJet x hg m (levelPoint lev hg) (fun a => ∑' n, PowerSeries.coeff n (Θ a) * π ^ n)
      (fun a j => ∑' n, PowerSeries.coeff n (Γ a j) * π ^ n) ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε →
      (∀ a, (Summable fun n => ‖e (PowerSeries.coeff n (Θ a)) * u ^ n‖) ∧
        ∀ j, Summable fun n => ‖e (PowerSeries.coeff n (Γ a j)) * u ^ n‖) ∧
      ∃ (x₀ : KeyIn ℂ) (hg₀ : x₀.P.g = g) (lev₀ : Out.Level x₀.P (m ^ 2) (unitOn (Units.map e.toMonoidHom ζ))),
        ThJet x₀ hg₀ m (levelPoint lev₀ hg₀) (fun a => ∑' n, e (PowerSeries.coeff n (Θ a)) * u ^ n)
          (fun a j => ∑' n, e (PowerSeries.coeff n (Γ a j)) * u ^ n) ∧ (κ ℂ x₀ : ℂ) = e k

def Transfer (κ : Rule) : Prop :=
  ∀ g n : ℕ, n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀,
    ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C]
      (e : C →+* ℂ) (x : KeyIn C) (hg : x.P.g = g) (ζ : Cˣ) (lev : Out.Level x.P ((n ^ j) ^ 2) (unitOn ζ)) (k : C),
      Deform κ e x hg (n ^ j) ζ lev k → (κ C x : C) = k

section Jets

abbrev redE (F : Type) [CommRing F] : Sp F ⟶ Sp (DualNumber F) := spMap (TrivSqZeroExt.fstHom F F F).toRingHom

variable {F : Type} [Field F] {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

def vE (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp (DualNumber F) ⟶ Y) (J : (Sp F ⟶ X) → L.ι) : DualNumber F :=
  valR r (LB.wchart L φ fun k => J (redE F ≫ r ≫ φ k)) (t.s fun k => J (redE F ≫ r ≫ φ k)).val

def sE (s : LB.Sec (LB.LinComb L φ ε)) (r : Sp (DualNumber F) ⟶ Y) (J : (Sp F ⟶ X) → L.ι) : DualNumber F :=
  valR r (LB.wchart L φ fun k => J (redE F ≫ r ≫ φ k)) (s.f fun k => J (redE F ≫ r ≫ φ k))

end Jets

section GtJets

variable {R : Type} [CommRing R] [IsDomain R]

abbrev TE (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F] : Over (Sp R) :=
  Over.mk (spMap (algebraMap F (DualNumber F)) ≫ (TF (R := R) F).hom)

def dualMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) : DualNumber A →+* DualNumber B where
  toFun z := TrivSqZeroExt.inl (f z.fst) + TrivSqZeroExt.inr (f z.snd)
  map_one' := by ext <;> simp
  map_mul' a b := by ext <;> simp [mul_comm, add_comm]
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp

variable {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F] {N : NumD F}

def jc (ν : NumOf D F N) {k : ℕ} (s : Fam D F k) (gm : GtPt D (TE R F)) (α : N.X) : DualNumber F :=
  sE (s.s (ν.eX α)) (lift (Over.homMk (spMap (algebraMap F (DualNumber F))) rfl : TE R F ⟶ TF (R := R) F) gm.b).left ν.J *
    vE (gm.s (ν.eX α)) (𝟙 _) ν.J

def Adapted (ν : NumOf D F N) (vB : Fin D.P.g → (epsR R ⟶ D.P.A)) {r g : ℕ} (bX : Module.Basis (Fin r) ℤ N.X)
    (σ : Fin g ≃ Fin D.P.g ⊕ Fin r) (gm : Fin g → GtPt D (TE R F)) : Prop :=
  IsLieBasis vB ∧ (∀ j, ∃ o : GtPtF D F, o.IsZero ∧ GtPt.IsPullF F (redE F) (gm j) o) ∧
  (∀ i, (gm (σ.symm (Sum.inl i))).b.left =
    spMap (dualMap ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)))) ≫ (vB i).left) ∧
  ∀ l, (gm (σ.symm (Sum.inr l))).b = DegPre.zeroT D (TE R F) ∧
    ∀ χ, vE ((gm (σ.symm (Sum.inr l))).s (ν.eX χ)) (𝟙 _) ν.J = 1 + TrivSqZeroExt.inr ((bX.repr χ l : ℤ) : F)

def BKey (κ : Rule) [CharZero F] (ν : NumOf D F N) (vB : Fin D.P.g → (epsR R ⟶ D.P.A)) (k : F) : Prop :=
  (D.P.g = 0 → N.th 1 ^ 8 * k = 1) ∧
  ∀ (hg : 1 ≤ D.P.g) (hr : D.rig.IsGen) (th : D.P.L.Sec) (hth) (hv : IsLieBasis vB) (x : KeyIn F),
    (∀ i : D.P.L.ι, ∀ h : LB.wchart D.P.L (fun _ : Fin 1 => 𝟙 D.P.A.left) (fun _ => i) ≤ D.P.L.U i,
      ν.th.f (fun _ => i) = resG _ h (th.f i)) →
    KeyPB x ⟨D.P, hg, D.rig, hr, th, hth, vB, hv⟩ ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))) →
    (κ F x : F) = k

end GtJets

def QLevel {O : Type} [CommRing O] (N : NumD O) (g k : ℕ) (ζ : Oˣ) (q : (Fin (2 * g) → ZMod k) → N.QT k) : Prop :=
  IsPrimitiveRoot ζ k ∧ (∀ a b, N.QEq (q a * q b) (q (a + b))) ∧ (∀ a b, N.QEq (q a) (q b) → a = b) ∧
  (∀ p, ∃ a, N.QEq (q a) p) ∧ ∀ i j, N.wp (q (Pi.single i 1)) (q (Pi.single j 1)) = ζ ^ stdSymp g i j

def IsEvFam {O : Type} [CommRing O] (N : NumD O) (m : ℕ) (p : N.QT (m ^ 2)) (f : N.X → N.A → O) : Prop :=
  (∀ (h : N.Gt) (χ : N.X), f (p.1.1.toAdd + m • χ) h.b * h.s (p.1.1.toAdd + m • χ) = N.evT m p h χ) ∧
  ∀ α, (∀ χ, α ≠ p.1.1.toAdd + m • χ) → ∀ x, f α x = 0

def Arch (κ : Rule) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] (D : DegPre R), D.PsiEven → D.TauBimult →
    ∀ [Algebra (FractionRing R) ℂ] (N : NumD ℂ) (ν : NumOf D ℂ N) (g r m k : ℕ), 1 ≤ g → Odd m → m ^ 2 ∣ k →
    ∀ (β : N.Form k) (ζ : ℂˣ) (q : (Fin (2 * g) → ZMod (m ^ 2)) → N.QT (m ^ 2)), QLevel N g (m ^ 2) ζ q →
    ∀ (s : (Fin (2 * g) → ZMod (m ^ 2)) → Fam D ℂ (m ^ 2)), (∀ a, ∃ f, ν.FamV (s a) f ∧ IsEvFam N m (q a) f) →
    ∀ (vB : Fin D.P.g → (epsR R ⟶ D.P.A)) (bX : Module.Basis (Fin r) ℤ N.X) (σ : Fin g ≃ Fin D.P.g ⊕ Fin r)
      (gm : Fin g → GtPt D (TE R ℂ)), Adapted ν vB bX σ gm → ∀ k₀ : ℂ, BKey κ ν vB k₀ →
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε →
      (∀ a j, (Summable fun α => ‖(jc ν (s a) (gm j) α).fst * u ^ (β.be α α / (2 * m ^ 2)).toNat‖) ∧
        Summable fun α => ‖(jc ν (s a) (gm j) α).snd * u ^ (β.be α α / (2 * m ^ 2)).toNat‖) ∧
      ∃ (x₀ : KeyIn ℂ) (hg₀ : x₀.P.g = g) (lev₀ : Out.Level x₀.P (m ^ 2) (unitOn ζ)) (ϑ : _ → ℂ),
        (∀ a j, ϑ a = ∑' α, (jc ν (s a) (gm j) α).fst / ν.rg ^ (m ^ 2) * u ^ (β.be α α / (2 * m ^ 2)).toNat) ∧
        ThJet x₀ hg₀ m (levelPoint lev₀ hg₀) ϑ
          (fun a j => ∑' α, (jc ν (s a) (gm j) α).snd / ν.rg ^ (m ^ 2) * u ^ (β.be α α / (2 * m ^ 2)).toNat) ∧
        (κ ℂ x₀ : ℂ) = k₀

end GlobalTheory.MBLow

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU

variable {p : ℕ} [Fact p.Prime]

def Datum.inv (D : Datum p) (x : D.O) : D.O := (D.star x).unop

def Datum.plat (D : Datum p) : PLat D.O D.inv where
  La := D.La
  fin := D.finLa
  free := D.freeLa
  EF := (2 : ℤ) • D.EF
  alt x := by simp [D.alt]
  nondeg x h := D.nondeg (by
    ext y
    have := h y
    simpa using this)
  adj a x y := by simp [D.adj, Datum.inv]

def Datum.g (D : Datum p) : ℕ := D.m * D.n * Module.finrank ℚ D.F / 2

def HalfPerf {O : Type} [Ring O] {bar : O → O} (p : ℕ) (D' : PLat O bar) : Prop :=
  ∃ E₁ : LinearMap.BilinForm ℤ D'.La, D'.EF = (2 : ℤ) • E₁ ∧
    ∃ e : ℕ, e.Coprime p ∧ ∀ f : D'.La →ₗ[ℤ] ℤ, ∃ x, E₁ x = e • f

def Datum.Cls (D : Datum p) (N : ℕ) (D' : PLat D.O D.inv) (t : D.La → D'.La) : Prop :=
  Genus p N D.plat D' t ∧ HalfPerf p D'


open Classical in
def Base.IsType {D : Datum p} {R : Type} [CommRing R] (b : Base D R) (σ : R →+* ℂ)
    (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) : Prop :=
  ∀ c : 𝓞 D.F, (ρ (algebraMap (𝓞 D.F) D.O c)).trace = (D.m : ℂ) * (∑ i, σ (b.t i c) +
    ∑ τ ∈ Finset.univ.filter (fun τ : D.F →+* ℂ => τ (D.ω : D.F) ≠ σ b.ρ), (D.n : ℂ) * τ (c : D.F) -
    ∑ i, (starRingEnd ℂ) (σ (b.t i c)))

def Obj.fam {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R}
    (o : Obj b N s) (h : SmoothOfRelativeDimension D.g o.A.hom) (hL : (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB) :
    Fam R D.O D.La D.g where
  X := S
  s := s
  A := o.A
  ab := o.ab
  dim := h
  act := o.act.act
  hom := o.act.hom
  act_one := o.act.one
  act_mul := o.act.mul
  act_add := o.act.add
  L := o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left
  isLB := hL
  ample := o.ample
  eta := o.eta

def Model.Uniformised {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} (M : Model b N) (σ : R →+* ℂ)
    (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) : Prop :=
  ∃ h hL, Nonempty (Unif (M.univ.fam h hL) σ ρ N (D.Cls N))

end GlobalTheory.UPel.HT
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne
noncomputable section

open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix
open scoped Classical

namespace GlobalTheory.LKLoc

section Generic

variable {G : Type} [Group G]

def locPart (T K : Subgroup G) (x : G) : Subgroup G := T ⊓ K.map (MulAut.conj x).toMonoidHom

def volRat (U V : Subgroup G) : ℝ := (V.relIndex U : ℝ) / (U.relIndex V : ℝ)

def orbSum (θ : G →* G) (K : Subgroup G) (δ : G) (w : G → ℝ) (f : G → ℂ) : ℂ :=
  ∑ᶠ q : DoubleCoset.Quotient (GlobalTheory.BCT.twCent θ δ : Set G) (K : Set G),
    (w (Quotient.out q) : ℂ) * GlobalTheory.BCT.avg fun k : K => f ((Quotient.out q * k)⁻¹ * δ * θ (Quotient.out q * k))

def twOrbU (θ : G →* G) (K : Subgroup G) (δ : G) (U : Subgroup G) (f : G → ℂ) : ℂ :=
  orbSum θ K δ (fun x => volRat U (locPart (GlobalTheory.BCT.twCent θ δ) K x)) f

end Generic

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

def frobR (r : ℕ) : Kn p K r →+* Kn p K r where
  toFun x := ⟨frobK p K (x : PadicAlgCl p), Kn_stable p K r (frobK p K) x x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

def intR (r : ℕ) : Subring (Kn p K r) := (Obar p).toSubring.comap (algebraMap (Kn p K r) (PadicAlgCl p))

def intK : Subring K := (Obar p).toSubring.comap (algebraMap K (PadicAlgCl p))

def sig (n r : ℕ) : GL (Fin n) (Kn p K r) →* GL (Fin n) (Kn p K r) :=
  GeneralLinearGroup.map (frobR p K r)

def Kint (n r : ℕ) : Subgroup (GL (Fin n) (Kn p K r)) :=
  (GeneralLinearGroup.map (intR p K r).subtype).range

def KintK (n : ℕ) : Subgroup (GL (Fin n) K) :=
  (GeneralLinearGroup.map (intK p K).subtype).range

end GlobalTheory.LKLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.WhiskerLeftEqLift
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

variable {X Y : Scheme.{0}}

structure IsOn (W : X.Opens) (L : LB X) : Prop where
  le : ∀ a, L.U a ≤ W
  cov : ∀ x ∈ W, ∃ a, x ∈ L.U a
  coc : ∀ (x : X) (a b c : L.ι), x ∈ L.U a → x ∈ L.U b → x ∈ L.U c →
    gm (𝟙 X) x _ (L.g a b) * gm (𝟙 X) x _ (L.g b c) = gm (𝟙 X) x _ (L.g a c)

abbrev Cmp (W : X.Opens) (L M : LB X) : Type := ∀ (a : L.ι) (b : M.ι), Γ(X, W ⊓ (L.U a ⊓ M.U b))ˣ

def IsoOn (W : X.Opens) (L M : LB X) (w : Cmp W L M) : Prop :=
  ∀ x ∈ W, ∀ (a a' : L.ι) (b b' : M.ι), x ∈ L.U a → x ∈ L.U a' → x ∈ M.U b → x ∈ M.U b' →
    gm (𝟙 X) x _ (w a b) * gm (𝟙 X) x _ (M.g b b') = gm (𝟙 X) x _ (L.g a a') * gm (𝟙 X) x _ (w a' b')

abbrev RigD (e : Y ⟶ X) (L : LB X) : Type := ∀ a : L.ι, Γ(Y, e ⁻¹ᵁ L.U a)ˣ

def RigOn (e : Y ⟶ X) (L : LB X) (r : RigD e L) : Prop :=
  ∀ (y : Y) (a b : L.ι), e y ∈ L.U a → e y ∈ L.U b →
    gm (𝟙 Y) y _ (r a) = gm e y _ (L.g a b) * gm (𝟙 Y) y _ (r b)

def Norm (e : Y ⟶ X) (W : X.Opens) (L M : LB X) (w : Cmp W L M) (r : RigD e L) (r' : RigD e M) : Prop :=
  ∀ (y : Y) (a : L.ι) (b : M.ι), e y ∈ W → e y ∈ L.U a → e y ∈ M.U b →
    gm e y _ (w a b) * gm (𝟙 Y) y _ (r' b) = gm (𝟙 Y) y _ (r a)

def FnBij (p : X ⟶ Y) : Prop := ∀ V : Y.Opens, Function.Bijective (p.app V).hom

variable {S : Scheme.{0}} (A : Over S) [GrpObj A]

def AddCls {T : Over S} (c : Pic (A ⊗ T).left) : Prop :=
  ∀ (Z : Over S) (a a' : Z ⟶ A) (t : Z ⟶ T),
    CechPic.pull (lift (a * a') t).left c = CechPic.pull (lift a t).left c + CechPic.pull (lift a' t).left c

theorem AddCls.pull {T T' : Over S} {c : Pic (A ⊗ T).left} (h : AddCls A c) (u : T' ⟶ T) :
    AddCls A (CechPic.pull (A ◁ u).left c) := fun Z a a' t ↦ by
  simpa only [← pull_comp, ← Over.comp_left, lift_whiskerLeft] using h Z a a' (t ≫ u)

def addF : (Over S)ᵒᵖ ⥤ Type 1 where
  obj T := {c : Pic (A ⊗ T.unop).left // AddCls A c}
  map u := TypeCat.ofHom fun c ↦ ⟨CechPic.pull (A ◁ u.unop).left c.1, c.2.pull A u.unop⟩
  map_id T := by
    ext c
    change CechPic.pull (A ◁ 𝟙 T.unop).left c.1 = c.1
    rw [MonoidalCategory.whiskerLeft_id, Over.id_left, pull_id]
  map_comp u v := by
    ext c
    change CechPic.pull (A ◁ (v.unop ≫ u.unop)).left c.1 =
      CechPic.pull (A ◁ v.unop).left (CechPic.pull (A ◁ u.unop).left c.1)
    rw [MonoidalCategory.whiskerLeft_comp, Over.comp_left, pull_comp]

theorem addF_map_val {T T' : Over S} (u : T' ⟶ T) (c : (addF A).obj (Opposite.op T)) :
    ((addF A).map u.op c).1 = CechPic.pull (A ◁ u).left c.1 := rfl

variable {A}

def famCls {T : Over S} {N : LB (A ⊗ T).left} (h : Fam A N) : (addF A).obj (Opposite.op T) :=
  ⟨cls N h.isLB, (isAdditive_iff h.isLB).1 h.add⟩

theorem famCls_surj {T : Over S} (c : (addF A).obj (Opposite.op T)) :
    ∃ (N : LB (A ⊗ T).left) (h : Fam A N), famCls h = c := by
  obtain ⟨c, hc⟩ := c
  obtain ⟨N, hN, rfl⟩ := cls_surj c
  exact ⟨N, ⟨hN, (isAdditive_iff hN).2 hc⟩, rfl⟩


omit [GrpObj A] in
theorem whiskerLeft_eq_lift {T T' : Over S} (u : T' ⟶ T) : A ◁ u = lift (fst A T') (snd A T' ≫ u) := by
  ext <;> simp

theorem same_iff_map {T U Z : Over S} {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left} (hN : Fam A N) (hM : Fam A M)
    (y : Z ⟶ T) (u : Z ⟶ U) : Same A N M y u ↔ (addF A).map y.op (famCls hN) = (addF A).map u.op (famCls hM) := by
  refine (same_iff hN.isLB hM.isLB y u).trans (Iff.trans ?_ Subtype.ext_iff.symm)
  rw [addF_map_val, addF_map_val, whiskerLeft_eq_lift, whiskerLeft_eq_lift]
  rfl

end GlobalTheory.PicGlue
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.NotIsIsoSpMapDnFst
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualOpen

variable {S : Scheme.{0}}

def ptMap {C C' : Type} [CommRing C] [CommRing C'] (s : Sp C ⟶ S) (φ : C →+* C') :
    Over.mk (spMap φ ≫ s) ⟶ Over.mk s := Over.homMk (spMap φ)

@[simp] theorem ptMap_left {C C' : Type} [CommRing C] [CommRing C'] (s : Sp C ⟶ S) (φ : C →+* C') :
    (ptMap s φ).left = spMap φ := rfl

abbrev dnInl (k : Type) [CommRing k] : k →+* DualNumber k := algebraMap k (DualNumber k)

abbrev dnFst (k : Type) [CommRing k] : DualNumber k →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom

structure Milnor {T T₁ T₂ T₀ : Scheme.{0}} (j₁ : T₁ ⟶ T) (j₂ : T₂ ⟶ T) (k₁ : T₀ ⟶ T₁) (k₂ : T₀ ⟶ T₂) : Prop where
  aff : IsAffine T
  aff₁ : IsAffine T₁
  aff₂ : IsAffine T₂
  closed : IsClosedImmersion k₂
  w : k₁ ≫ j₁ = k₂ ≫ j₂
  cart : IsPullback j₁.appTop j₂.appTop k₁.appTop k₂.appTop

variable (A : Over S) [GrpObj A] {U : Over S} (M : LB (A ⊗ U).left)

def FieldChart : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (s : Sp K ⟶ S) (T : Over S) (_ : T ⟶ Over.mk s) (N : LB (A ⊗ T).left),
    Fam A N → ChartAt A M N

def TanLift : Prop :=
  ∀ (k : Type) [Field k] (s : Sp k ⟶ S) (N : LB (A ⊗ Over.mk (spMap (dnInl k) ≫ s)).left), Fam A N →
    ∀ u₀ : Over.mk (spMap (dnFst k) ≫ spMap (dnInl k) ≫ s) ⟶ U, Same A N M (ptMap _ (dnFst k)) u₀ →
      ∃ u : Over.mk (spMap (dnInl k) ≫ s) ⟶ U, Same A N M (𝟙 _) u

def SmallLift : Prop :=
  ∀ (C : Type) [CommRing C] [IsLocalRing C] (e : C), e ∈ IsLocalRing.maximalIdeal C →
    (∀ a ∈ IsLocalRing.maximalIdeal C, a * e = 0) → ∀ (s : Sp C ⟶ S) (N : LB (A ⊗ Over.mk s).left), Fam A N →
    ∀ u₀ : Over.mk (spMap (Ideal.Quotient.mk (Ideal.span {e})) ≫ s) ⟶ U,
      Same A N M (ptMap s (Ideal.Quotient.mk (Ideal.span {e}))) u₀ → ∃ u : Over.mk s ⟶ U, Same A N M (𝟙 _) u

variable {A M}

theorem Milnor.of_isPullback {R R₁ R₂ R₀ : CommRingCat.{0}} {a : R ⟶ R₁} {b : R ⟶ R₂} {c : R₁ ⟶ R₀} {d : R₂ ⟶ R₀}
    (h : IsPullback a b c d) (hd : Function.Surjective d) :
    Milnor (Spec.map a) (Spec.map b) (Spec.map c) (Spec.map d) := by
  refine ⟨inferInstance, inferInstance, inferInstance, IsClosedImmersion.spec_of_surjective d hd, ?_, ?_⟩
  · rw [← Spec.map_comp, ← Spec.map_comp, h.w]
  · exact h.of_iso (Scheme.ΓSpecIso R).symm (Scheme.ΓSpecIso R₁).symm (Scheme.ΓSpecIso R₂).symm
      (Scheme.ΓSpecIso R₀).symm (Scheme.ΓSpecIso_inv_naturality a) (Scheme.ΓSpecIso_inv_naturality b)
      (Scheme.ΓSpecIso_inv_naturality c) (Scheme.ΓSpecIso_inv_naturality d)


end GlobalTheory.DualOpen
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.NontrivialOfArtinQE
noncomputable section
namespace GlobalTheory.KS
namespace Model
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.EtC GlobalTheory.UPel.HT
open scoped TensorProduct

variable {S : Scheme.{0}} {O : Type} [Ring O]

theorem act_zero {A : Over S} [GrpObj A] (act : OActN O A) : act.act 0 = 1 := by
  have h := act.add 0 0
  rw [add_zero] at h
  have : act.act 0 * act.act 0 = act.act 0 * 1 := h.symm.trans (_root_.mul_one _).symm
  exact mul_left_cancel this

variable (l : ℕ) [Fact l.Prime] {E : Type} [CommRing E] [Algebra ℚ_[l] E]

section Gal
variable {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω]

end Gal

theorem powMap_pr {S' : Scheme.{0}} {A' : Over S'} {A : Over S} (f : S' ⟶ S) (φ : A'.left ⟶ A.left)
    (h : φ ≫ A.hom = A'.hom ≫ f) (m : ℕ) (i : Fin m) : powMap f φ h m ≫ (pr A i).left = (pr A' i).left ≫ φ := by
  unfold powMap
  rw [← Over.comp_left, Pi.lift_comp_π]
  rfl

theorem powMap_over {S' : Scheme.{0}} {A' : Over S'} {A : Over S} (f : S' ⟶ S) (φ : A'.left ⟶ A.left)
    (h : φ ≫ A.hom = A'.hom ≫ f) (m : ℕ) : powMap f φ h m ≫ (pow A m).hom = (pow A' m).hom ≫ f := by
  unfold powMap
  exact Over.w _

end Model
end GlobalTheory.KS
end
end
