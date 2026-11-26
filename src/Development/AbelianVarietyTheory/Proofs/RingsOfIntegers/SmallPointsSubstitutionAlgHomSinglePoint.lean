module

public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LatticeTrivialAtPrimeIndicesAndUnits
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RegularSectionIntegralGermUniqueScale
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPref
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointsLiftToLevelCover
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsFramedPointOfArcBaseChange
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FormalGroupPointsOfIntegralChartSpec

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SmallPointsSubstitutionAlgHomSinglePoint
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open GlobalTheory.PlaceInt.FormalPts

namespace GlobalTheory.TransUnit

section Alg
variable {Γ Γ' U U' : Type*} [CommGroup Γ] [CommGroup Γ'] [CommGroup U] [CommGroup U']

def c3 (q : Γ → U) (x y z : Γ) : U := q (x * y * z) * q x * q y * q z / (q (x * y) * q (x * z) * q (y * z))

def quadT (p₁ p₂ : Γ → Γ → Γ → U) (w : Γ → Γ) (x y : Γ) : U :=
  p₁ x y (w (x * y)) * p₂ x (w x) (w y) * p₂ y (w x) (w y)

def quadQ (p₁ p₂ : Γ → Γ → Γ → U) (w : Γ → Γ) (x y z : Γ) : U :=
  quadT p₁ p₂ w (x * y) z / (quadT p₁ p₂ w x z * quadT p₁ p₂ w y z) * p₁ x y (w z) * p₂ z (w x) (w y)

def quadN (p₁ p₂ : Γ → Γ → Γ → U) (w : Γ → Γ) (x : Γ) : U := p₂ x⁻¹ (w x) (w x)⁻¹ / p₁ x x⁻¹ (w x)

def LiftLaws (θ : Γ → Γ → Γ → U) (ρ φ : Γ → U) (w : Γ → Γ) (a : Γ) (k : ℕ) : Prop :=
  (∀ x, ∏ j ∈ Finset.range k, φ (a ^ j * x) = 1) ∧
  φ 1 * φ a⁻¹ * (ρ a / ρ a⁻¹ * quadN θ θ w a) ^ k = 1 ∧
  ∀ x y, φ (x * y) * φ 1 * (c3 ρ x y a / ρ 1 * quadQ θ θ w x y a) ^ k = φ x * φ y

theorem quadQ_of_diff {p₁ p₂ q₁ q₂ : Γ → Γ → Γ → U} {e : Γ → Γ → U} (w : Γ →* Γ)
    (h₁ : ∀ x y z, p₁ x y z = q₁ x y z * (e (x * y) z / (e x z * e y z)))
    (h₂ : ∀ x y z, p₂ x y z = q₂ x y z * (e x (y * z) / (e x y * e x z))) (x y z : Γ) :
    quadQ p₁ p₂ w x y z = quadQ q₁ q₂ w x y z * c3 (fun x => e x (w x)) x y z := by
  apply Additive.ofMul.injective
  simp only [quadQ, quadT, c3, h₁, h₂, map_mul, ofMul_mul, ofMul_div]
  abel

theorem quadN_of_diff {p₁ p₂ q₁ q₂ : Γ → Γ → Γ → U} {e : Γ → Γ → U} (w : Γ →* Γ)
    (h₁ : ∀ x y z, p₁ x y z = q₁ x y z * (e (x * y) z / (e x z * e y z)))
    (h₂ : ∀ x y z, p₂ x y z = q₂ x y z * (e x (y * z) / (e x y * e x z)))
    (e₁ : ∀ z, e 1 z = 1) (e₂ : ∀ x, e x 1 = 1) (x : Γ) :
    quadN p₁ p₂ w x = quadN q₁ q₂ w x * (e x (w x) / e x⁻¹ (w x⁻¹)) := by
  apply Additive.ofMul.injective
  simp only [quadN, h₁, h₂, map_inv, mul_inv_cancel, e₁, e₂, ofMul_mul, ofMul_div, ofMul_one]
  abel

theorem quadQ_one (w : Γ → Γ) (x y z : Γ) : quadQ (fun _ _ _ => (1 : U)) (fun _ _ _ => 1) w x y z = 1 := by simp [quadQ, quadT]

theorem quadN_one (w : Γ → Γ) (x : Γ) : quadN (fun _ _ _ => (1 : U)) (fun _ _ _ => 1) w x = 1 := by simp [quadN]

theorem map_lineCoeffCubic (P : Γ →* Γ') (g : U →* U') {q : Γ → U} {q' : Γ' → U'} (h : ∀ x, q' (P x) = g (q x)) (x y z : Γ) :
    c3 q' (P x) (P y) (P z) = g (c3 q x y z) := by
  have hP : ∀ a b, P a * P b = P (a * b) := fun a b => (map_mul P a b).symm
  simp only [c3, hP, h, map_mul g, map_div g]

theorem quadQ_map (P : Γ →* Γ') (g : U →* U') {p₁ p₂ : Γ → Γ → Γ → U} {p₁' p₂' : Γ' → Γ' → Γ' → U'} {w : Γ → Γ}
    {w' : Γ' → Γ'} (hw : ∀ x, w' (P x) = P (w x)) (h₁ : ∀ x y z, p₁' (P x) (P y) (P z) = g (p₁ x y z))
    (h₂ : ∀ x y z, p₂' (P x) (P y) (P z) = g (p₂ x y z)) (x y z : Γ) :
    quadQ p₁' p₂' w' (P x) (P y) (P z) = g (quadQ p₁ p₂ w x y z) := by
  have hP : ∀ a b, P a * P b = P (a * b) := fun a b => (map_mul P a b).symm
  simp only [quadQ, quadT, hP, hw, h₁, h₂, map_mul g, map_div g]

theorem quadN_map (P : Γ →* Γ') (g : U →* U') {p₁ p₂ : Γ → Γ → Γ → U} {p₁' p₂' : Γ' → Γ' → Γ' → U'} {w : Γ → Γ}
    {w' : Γ' → Γ'} (hw : ∀ x, w' (P x) = P (w x)) (h₁ : ∀ x y z, p₁' (P x) (P y) (P z) = g (p₁ x y z))
    (h₂ : ∀ x y z, p₂' (P x) (P y) (P z) = g (p₂ x y z)) (x : Γ) :
    quadN p₁' p₂' w' (P x) = g (quadN p₁ p₂ w x) := by
  have hP : ∀ a, (P a)⁻¹ = P a⁻¹ := fun a => (map_inv P a).symm
  simp only [quadN, hw, hP, h₁, h₂, map_div g]

end Alg

section Jet
variable {V : Type} [CommRing V]

def jetA (κ : Type) [Fintype κ] [DecidableEq κ] (m : ℕ) : MvPowerSeries κ V →ₐ[V] Jet V κ m where
  toFun := psJet m
  map_one' := FBIdJet.psJet_one m
  map_mul' := FBIdJet.psJet_mul m
  map_zero' := FrameBiextId.psJet_zero m
  map_add' f g := by simp only [psJet, FBIdJet.psTrunc_eq, map_add (f := _)]
  commutes' c := by
    have := RegularGerm.psJet_smul (κ := κ) m c 1
    rw [FBIdJet.psJet_one, _root_.mul_one] at this
    rw [Algebra.algebraMap_eq_smul_one, this]


variable (V) in
abbrev limO (d n : ℕ) : Over (Sp V) := overAt (𝟙 (Sp V)) (PS V n d)

def IsLimit {G : Over (Sp V)} {d : ℕ} (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G) (X : limO V d 1 ⟶ G) : Prop :=
  ∀ m, Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetA (Fin 1 × Fin d) m) ≫ X = x m

end Jet

section Small
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V]
  {d : ℕ} {O : Type} [CommRing O] [StarRing O]

def Sm (_B : FB V d O) (n : ℕ) : Type := {x : Pt V n d // SmallPt x}

variable {B : FB V d O} {l m n : ℕ}

instance : CommGroup (Sm B n) :=
  { mul := fun x y => ⟨addV B.G.F x.1 y.1, fun i => small_evV _ (small_two x.2 y.2) _ (B.G.const i)⟩
    one := ⟨0, fun i => by simp⟩
    inv := fun x => ⟨compV (B.A.act (-1)) x.1, fun i => small_evV _ (small_one x.2) _ (B.A.const _ i)⟩
    mul_assoc := fun x y z => Subtype.ext (addV_assoc B.G x.2 y.2 z.2)
    one_mul := fun x => Subtype.ext (zero_addV B.G x.2)
    mul_one := fun x => Subtype.ext (addV_zero B.G x.2)
    mul_comm := fun x y => Subtype.ext (addV_comm B.G x.2 y.2)
    inv_mul_cancel := fun x => Subtype.ext ((addV_comm B.G
      (fun i => small_evV _ (small_one x.2) _ (B.A.const _ i)) x.2).trans (addV_neg_actV B.A x.2)) }

theorem Sm.mul_val (x y : Sm B n) : (x * y).1 = addV B.G.F x.1 y.1 := rfl
theorem Sm.one_val : (1 : Sm B n).1 = 0 := rfl
theorem Sm.inv_val (x : Sm B n) : (x⁻¹).1 = compV (B.A.act (-1)) x.1 := rfl


variable (B) in
def Sm.act (o : O) : Sm B n →* Sm B n :=
  MonoidHom.mk' (fun x => ⟨compV (B.A.act o) x.1, fun i => small_evV _ (small_one x.2) _ (B.A.const _ i)⟩)
    fun x y => Subtype.ext (act_addV B.A o x.2 y.2)

theorem Sm.act_val (o : O) (x : Sm B n) : (Sm.act B o x).1 = compV (B.A.act o) x.1 := rfl


variable (B) in
def Sm.gen (j : Fin n) : Sm B n := ⟨pt V d j, fun i => by simp [pt]⟩


variable (B) in
def Sm.const (α : Fin d → V) (hα : Small α) : Sm B n := ⟨cpt α, fun i => by simpa [PlaceInt.cpt] using hα i⟩

def evA (a : Fin m → Sm B n) : PS V m d →ₐ[V] PS V n d :=
  (exists_algHom_evC (fun p : Fin m × Fin d => (a p.1).1 p.2) (fun p => (a p.1).2 p.2)).choose

theorem evA_X (a : Fin m → Sm B n) (p : Fin m × Fin d) : evA a (MvPowerSeries.X p) = (a p.1).1 p.2 := (exists_algHom_evC (fun p : Fin m × Fin d => (a p.1).1 p.2) (fun p => (a p.1).2 p.2)).choose_spec p

theorem evA_apply (a : Fin m → Sm B n) (f : PS V m d) : evA a f = evV (fun j => (a j).1) f := (evC_eq_algHom (fun p : Fin m × Fin d => (a p.1).1 p.2) (fun p => (a p.1).2 p.2) (evA a) (evA_X a) f).symm

theorem smallPointsSubstitutionAlgHom_single_point (x : Sm B n) (f : PS V 1 d) : evA ![x] f = evV ![x.1] f := by
  rw [evA_apply]
  exact congrArg (evV · f) (funext fun j => by fin_cases j <;> rfl)

theorem smallPointsSubstitutionAlgHom_two_points (x y : Sm B n) (f : PS V 2 d) : evA ![x, y] f = evV ![x.1, y.1] f := by
  rw [evA_apply]
  exact congrArg (evV · f) (funext fun j => by fin_cases j <;> rfl)

theorem smallPointsSubstitutionAlgHom_three_points (x y z : Sm B n) (f : PS V 3 d) : evA ![x, y, z] f = evV ![x.1, y.1, z.1] f := by
  rw [evA_apply]
  exact congrArg (evV · f) (funext fun j => by fin_cases j <;> rfl)

def Sm.subFun (b : Fin m → Sm B n) (x : Sm B m) : Sm B n :=
  ⟨fun i => evA b (x.1 i), fun i =>
    (congrArg (fun q => MvPowerSeries.constantCoeff q ∈ maximalIdeal V) (evA_apply b (x.1 i))).mpr
      (constantCoeff_evC_mem (fun p : Fin m × Fin d => (b p.1).1 p.2) (fun p => (b p.1).2 p.2) _ (x.2 i))⟩

theorem evA_evA' (b : Fin m → Sm B n) (a : Fin l → Sm B m) (f : PS V l d) :
    evA b (evA a f) = evA (fun j => Sm.subFun b (a j)) f := by
  rw [evA_apply (fun j => Sm.subFun b (a j))]
  exact (evC_eq_algHom (fun p : Fin l × Fin d => (Sm.subFun b (a p.1)).1 p.2) (fun p => (Sm.subFun b (a p.1)).2 p.2)
    ((evA b).comp (evA a)) (fun p => by rw [AlgHom.comp_apply, evA_X]; rfl) f).symm

def Sm.sub (b : Fin m → Sm B n) : Sm B m →* Sm B n :=
  MonoidHom.mk' (Sm.subFun b) fun x y => Subtype.ext (funext fun i => by
    show evA b (evV ![x.1, y.1] (B.G.F i)) = evV ![(Sm.subFun b x).1, (Sm.subFun b y).1] (B.G.F i)
    rw [← smallPointsSubstitutionAlgHom_two_points, ← smallPointsSubstitutionAlgHom_two_points, evA_evA']
    exact congrArg (evA · (B.G.F i)) (funext fun j => by fin_cases j <;> rfl))

theorem evA_evA (b : Fin m → Sm B n) (a : Fin l → Sm B m) (f : PS V l d) :
    evA b (evA a f) = evA (fun j => Sm.sub b (a j)) f := evA_evA' b a f

theorem Sm.sub_gen (b : Fin m → Sm B n) (j : Fin m) : Sm.sub b (Sm.gen B j) = b j := Subtype.ext (funext fun i => evA_X b (j, i))

theorem Sm.sub_const (b : Fin m → Sm B n) (α : Fin d → V) (hα : Small α) :
    Sm.sub b (Sm.const B α hα) = Sm.const B α hα := Subtype.ext (funext fun i => (evA b).commutes (α i))

theorem Sm.sub_act (b : Fin m → Sm B n) (o : O) (x : Sm B m) : Sm.sub b (Sm.act B o x) = Sm.act B o (Sm.sub b x) := Subtype.ext (funext fun i => by
    show evA b (evV ![x.1] (B.A.act o i)) = evV ![(Sm.sub b x).1] (B.A.act o i)
    rw [← smallPointsSubstitutionAlgHom_single_point, ← smallPointsSubstitutionAlgHom_single_point, evA_evA]
    exact congrArg (evA · (B.A.act o i)) (funext fun j => by fin_cases j; rfl))

theorem evA_gen (f : PS V n d) : evA (Sm.gen B) f = f := by
  rw [evA_apply]
  exact evC_eq_algHom _ (fun p => (Sm.gen B p.1).2 p.2) (AlgHom.id V _) (fun p => rfl) f

theorem evA_eq_ev (a : Fin m → Sm B n) (ha : ∀ j i, MvPowerSeries.constantCoeff ((a j).1 i) = 0) (f : PS V m d) :
    evA a f = ev (fun j => (a j).1) f := by
  rw [evA_apply]
  exact (evC_spec V (Fin m × Fin d) (Fin n × Fin d) (Fin n × Fin d) (fun p => (a p.1).1 p.2) (fun p => (a p.1).2 p.2)).2.2.1
    (fun p => ha p.1 p.2) f

def evU (a : Fin m → Sm B n) : (PS V m d)ˣ →* (PS V n d)ˣ := Units.map (evA a : PS V m d →* PS V n d)

theorem evU_val (a : Fin m → Sm B n) (f : (PS V m d)ˣ) : (evU a f).val = evA a f.val := rfl

def u1 (f : (PS V 1 d)ˣ) (x : Sm B n) : (PS V n d)ˣ := evU ![x] f

def u2 (f : (PS V 2 d)ˣ) (x y : Sm B n) : (PS V n d)ˣ := evU ![x, y] f

def u3 (f : (PS V 3 d)ˣ) (x y z : Sm B n) : (PS V n d)ˣ := evU ![x, y, z] f

theorem besselUnipotentSubgroup_zero_subsingleton (b : Fin m → Sm B n) (f : (PS V 1 d)ˣ) (x : Sm B m) : u1 f (Sm.sub b x) = evU b (u1 f x) := Units.ext (by
    show evA ![Sm.sub b x] f.val = evA b (evA ![x] f.val)
    rw [evA_evA]
    exact congrArg (evA · f.val) (funext fun j => by fin_cases j <;> rfl))

theorem unitSeriesValueTwoPoints_substitution (b : Fin m → Sm B n) (f : (PS V 2 d)ˣ) (x y : Sm B m) :
    u2 f (Sm.sub b x) (Sm.sub b y) = evU b (u2 f x y) := Units.ext (by
    show evA ![Sm.sub b x, Sm.sub b y] f.val = evA b (evA ![x, y] f.val)
    rw [evA_evA]
    exact congrArg (evA · f.val) (funext fun j => by fin_cases j <;> rfl))

theorem unitSeriesValueThreePoints_substitution (b : Fin m → Sm B n) (f : (PS V 3 d)ˣ) (x y z : Sm B m) :
    u3 f (Sm.sub b x) (Sm.sub b y) (Sm.sub b z) = evU b (u3 f x y z) := Units.ext (by
    show evA ![Sm.sub b x, Sm.sub b y, Sm.sub b z] f.val = evA b (evA ![x, y, z] f.val)
    rw [evA_evA]
    exact congrArg (evA · f.val) (funext fun j => by fin_cases j <;> rfl))

def ptOf {G : Over (Sp V)} (X : limO V d 1 ⟶ G) (a : Sm B n) : limO V d n ⟶ G :=
  Formalism.L2.Pj.homAt (𝟙 (Sp V)) (evA ![a]) ≫ X

theorem ptOf_sub {G : Over (Sp V)} (X : limO V d 1 ⟶ G) (b : Fin m → Sm B n) (a : Sm B m) :
    Formalism.L2.Pj.homAt (𝟙 (Sp V)) (evA b) ≫ ptOf X a = ptOf X (Sm.sub b a) := by
  have hc : (evA b).comp (evA ![a]) = evA ![Sm.sub b a] :=
    AlgHom.ext fun f => by
      rw [AlgHom.comp_apply, evA_evA]
      exact congrArg (evA · f) (funext fun j => by fin_cases j <;> rfl)
  simp only [ptOf]
  rw [← Category.assoc]
  congr 1
  ext1
  simp only [Over.comp_left, Formalism.L2.Pj.homAt, Over.homMk_left]
  rw [← hc]
  unfold spMap
  rw [← Spec.map_comp]
  rfl

end Small

end GlobalTheory.TransUnit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralOfFramedPointOverIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralOfFramedPointOverIntegral
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PlaceInt

theorem integral_of_frOver : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (T : CDVR) (io : c.F →+* T.Fr) (io₂ : d.c₂.F →+* T.Fr) (y : IntFr Xo c T io), letI := io.toAlgebra; letI := io₂.toAlgebra; (∀ a : c.F, io₂ (d.eF a) = io a) → ∀ y₂ : FrPt d.Xo₂ d.c₂ T.Fr, FrOver d y₂ y.1 → Integral T io₂ y₂ := by
  intro E _ _ _ H Dw l Xo c n d T io io₂ y hio y₂ hy
  letI := io.toAlgebra
  letI := io₂.toAlgebra
  obtain ⟨y, hInt⟩ := y
  have hy' : FrOver d y₂ y := hy
  obtain ⟨G, t', m1, m2, ⟨ub, b1, b2, b3, b4⟩, θ, hθ, w1, w2, σ, s1, θ2, r1, r2, i1, i2, p2, hg⟩ := hInt.2
  obtain ⟨e, hu, w, p, hw, p₁, p₂, R⟩ := (FrameLift.frOver_iff d y₂ y).1 hy'
  have key : ∀ (x : Sp T.Fr ⟶ Xo.X) (m : SABMap t' Xo.univ.t x), x = y₂.x ≫ d.r →
      ∃ m' : SABMap t' d.Xo₂.univ.t y₂.x, m.φ = m'.φ ≫ d.m.φ := by
    intro x m hx
    subst hx
    exact sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ d.m m
  obtain ⟨m', e₁⟩ := key _ m1 e.symm
  have eig : ∀ τ v, Formalism.L2.Pj.IsEigV d.c₂ io₂ G τ v ↔ Formalism.L2.Pj.IsEigV c io G τ v := fun τ v =>
    forall_congr' fun a => forall_congr' fun z => by rw [← FrameLift.embK_eF d τ a, hio]
  have he : m1.cm.e = m'.cm.e ≫ d.m.cm.e := by rw [m1.base, m'.base, d.m.base]; exact e.symm
  obtain ⟨w', r', tri⟩ := ArcQ.FrBC.exists_rigIso_cancel d.m.cm m'.cm m1.cm e₁ he t'.PP d.Xo₂.univ.t.PP Xo.univ.t.PP
    w w1 hw r1
  obtain ⟨s', hs'⟩ := thf_secUp ((isGen_iff w').1 r'.1) d.Xo₂.univ.t.PP.isLB t'.PP.isLB σ
  refine ⟨G, t', m', m2, ⟨ub, b1, fun τ i => (eig τ _).2 (b2 τ i), fun τ v h1 h2 => b3 τ v h1 ((eig τ v).1 h2),
    fun τ i => ?_⟩, θ, hθ, w', w2, σ, s', θ2, r', r2,
    (ArcQ.FrUniq.isoMaps_iff w' σ s').2 fun Z r z j k hj hk => hs' Z r z (fun _ => j) k (mem_pull.2 hj) hk,
    i2, p2, ?_⟩
  · obtain ⟨q, h2, h3⟩ := b4 τ i
    have ubo : (ub τ i).left ≫ G.G.hom = spMap (algebraMap T.V (DualNumber T.V)) := Over.w (ub τ i)
    have h4 : q ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
      have : Mono (spMap (algebraMap T.V T.Fr)) :=
        haveI := IsPreimmersion.of_isLocalization (R := CommRingCat.of T.V) (S := CommRingCat.of T.Fr)
          (nonZeroDivisors T.V)
        inferInstanceAs (Mono (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr))))
      rw [← cancel_mono (spMap (algebraMap T.V T.Fr)), Category.assoc, ← m2.cart.1.w, ← Category.assoc, h3,
        Category.assoc]
      exact (congrArg _ ubo).trans (ArcQ.FrBC.dual_alg _)
    refine ⟨q, d.m.cart.1.hom_ext ?_ ?_, h3⟩
    · exact (Category.assoc _ _ _).trans ((congrArg (q ≫ ·) e₁.symm).trans (h2.trans (hu τ i).symm))
    · rw [Category.assoc, m'.cart.1.w, ← Category.assoc, h4]
      exact (y₂.tan τ i).1.symm
  · intro g g₁ g₂ (J : PUnit → d.Xo₂.univ.t.PP.L.ι) hJ
    refine fn_ext fun z hz => ?_
    obtain ⟨k, hk⟩ := exists_chart t'.PP.isLB z
    obtain ⟨j, hj⟩ := exists_chart Xo.univ.t.PP.isLB (d.m.φ (m'.φ z))
    have hi : m'.φ z ∈ d.Xo₂.univ.t.PP.L.U (J PUnit.unit) := mem_pull.1 hz
    have hj' : m1.φ z ∈ Xo.univ.t.PP.L.U j :=
      (congrArg (· ∈ Xo.univ.t.PP.L.U j) (FrameLift.pt_eq e₁ z)).mpr hj
    have a₁ : (g ≫ p) ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = m1.φ := by
      rw [Category.assoc, p₁, ← Category.assoc, g₁, e₁]
    have a₂ : (g ≫ p) ≫ (fst (Over.mk y.x) Xo.univ.t.G).left = t'.G.hom := by
      rw [Category.assoc, p₂, g₂]
    have le : (Xo.univ.t.PP.L.pull m1.φ).U (fun _ => j) ≤ (g ≫ p) ⁻¹ᵁ (PPx y.x).U (fun _ => j) := fun q hq =>
      Set.mem_iInter.2 fun _ => (congrArg (· ∈ Xo.univ.t.PP.L.U j) (FrameLift.pt_eq a₁ q)).mpr (mem_pull.1 hq)
    have u₁ := (ArcQ.FrUniq.isoMaps_iff w1 σ s1).1 i1 _ (𝟙 _) z j k hj' hk
    rw [hg (g ≫ p) a₁ a₂ (fun _ => j) le, gs_appLE (g ≫ p) _ _ le (𝟙 _) z (mem_pull.2 hj'),
      tri _ (𝟙 _) z j (J PUnit.unit) k hj hi hk, Category.id_comp, Category.id_comp] at u₁
    have u₂ := R _ g z j (J PUnit.unit)
      ((congrArg (fun t => d.m.φ t ∈ Xo.univ.t.PP.L.U j) (FrameLift.pt_eq g₁ z)).mpr hj)
      ((congrArg (· ∈ d.Xo₂.univ.t.PP.L.U (J PUnit.unit)) (FrameLift.pt_eq g₁ z)).mpr hi)
    rw [g₁] at u₂
    have u₃ := u₁.symm.trans u₂
    rw [Units.val_mul, _root_.mul_assoc, Units.mul_right_inj] at u₃
    rw [hs' _ (𝟙 _) z J k hz hk, gs_appLE _ _ _ hJ (𝟙 _) z hz, Category.id_comp]
    exact u₃

end GlobalTheory.PlaceInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralOfFramedPointOverIntegralStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_of_framed_point_over_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (T : CDVR) (io : c.F →+* T.Fr) (io₂ : d.c₂.F →+* T.Fr) (y : IntFr Xo c T io), letI := io.toAlgebra; letI := io₂.toAlgebra; (∀ a : c.F, io₂ (d.eF a) = io a) → ∀ y₂ : FrPt d.Xo₂ d.c₂ T.Fr, FrOver d y₂ y.1 → Integral T io₂ y₂ := by
  first | exact @GlobalTheory.PlaceInt.integral_of_frOver | exact GlobalTheory.PlaceInt.integral_of_frOver | (intros; apply GlobalTheory.PlaceInt.integral_of_frOver <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.KillsFormalPointsIffMemCoordinateKernel
section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.KillsFormalPointsIffMemCoordinateKernel
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
namespace GlobalTheory.PlaceInt.FormKer

lemma cpt_const {V : Type} [CommRing V] {d : ℕ} (x : Pt V 0 d) :
    (cpt (fun i => MvPowerSeries.constantCoeff (x i)) : Pt V 0 d) = x := by
  funext i
  ext m

  obtain rfl : m = 0 := Subsingleton.elim _ _
  simp [cpt]

lemma rel_prod {M P : Type*} [Monoid M] (R : M → P → Prop) (z : P) (s : P → P → P) (h1 : R 1 z)
    (hm : ∀ a a' x x', R a x → R a' x' → R (a * a') (s x x')) :
    ∀ (n : ℕ) (f : Fin n → M) (g : Fin n → P), (∀ j, R (f j) (g j)) →
      R (List.ofFn f).prod ((List.ofFn g).foldr s z) := by
  intro n
  induction n with
  | zero => intro f g _; simpa using h1
  | succ n ih =>
    intro f g hfg
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.foldr_cons]
    exact hm _ _ _ _ (hfg 0) (ih _ _ fun j => hfg j.succ)

theorem kills_iff_mem_kerM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), ∀ B : FB T.V (chD C.ch) (𝓞 E), IsBT C B → ∀ (n : ℕ) (mu : Matrix (Fin n) (Fin n) (𝓞 E)) (a : Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) (α : Fin n → Fin (chD C.ch) → T.V), (∀ b, FormPt C (a b) (α b)) → (Kills Xo mu a ↔ α ∈ kerM B mu) := by
  intro E _ _ _ H Dw l Xo c _ hstar T io y C B hB n mu a α hα
  obtain ⟨h1, hinj, hmul, hact, -⟩ := GlobalTheory.T.formal_group_points_of_integral_chart_spec E H Dw l Xo c hstar T io y C B hB

  have h0 : (0 : Pt T.V 0 (chD C.ch)) = cpt 0 := by
    funext k
    simp [cpt]
  have hstep : ∀ (g g' : ptO Xo (xOf y) ⟶ Xo.univ.t.G) (x x' : Pt T.V 0 (chD C.ch)),
      (∃ δ, x = cpt δ ∧ FormPt C g δ) → (∃ δ, x' = cpt δ ∧ FormPt C g' δ) →
        ∃ δ, addV B.G.F x x' = cpt δ ∧ FormPt C (g * g') δ := by
    rintro g g' x x' ⟨al, rfl, hg⟩ ⟨al', rfl, hg'⟩
    exact ⟨_, (cpt_const _).symm, hmul g g' al al' _ hg hg' (cpt_const _)⟩
  have key : ∀ i, ∃ δ : Fin (chD C.ch) → T.V,
      matV B (m := 0) mu (fun j => cpt (α j)) i = cpt δ ∧
        FormPt C (List.ofFn fun j => a j ≫ Xo.univ.t.act.act (mu i j)).prod δ := by
    intro i
    have hrow : ∀ j, ∃ δ, compV (B.A.act (mu i j)) (cpt (α j)) = cpt δ ∧
        FormPt C (a j ≫ Xo.univ.t.act.act (mu i j)) δ := fun j =>
      ⟨_, (cpt_const _).symm, hact (a j) (α j) _ (mu i j) (hα j) (cpt_const _)⟩
    exact rel_prod (fun g x => ∃ δ, x = cpt δ ∧ FormPt C g δ) 0 (addV B.G.F) ⟨0, h0, h1⟩
      hstep n (fun j => a j ≫ Xo.univ.t.act.act (mu i j))
      (fun j => compV (B.A.act (mu i j)) (cpt (α j))) hrow
  have hcpt : ∀ δ : Fin (chD C.ch) → T.V, cpt (n := 0) δ = 0 → δ = 0 := by
    intro δ h
    funext k
    have := congrArg MvPowerSeries.constantCoeff (congrFun h k)
    simpa [cpt] using this
  simp only [Kills, kerM, Set.mem_ofPred_eq]
  constructor
  · intro hk
    refine ⟨fun b => (hα b).1, funext fun i => ?_⟩
    obtain ⟨δ, hm, hF⟩ := key i
    obtain rfl : δ = 0 := (hinj _ 1 δ 0 hF h1).mp (hk i)
    rw [hm, ← h0]
    rfl
  · rintro ⟨-, hz⟩ i
    obtain ⟨δ, hm, hF⟩ := key i
    have hδ : δ = 0 := hcpt δ (by rw [← hm]; exact congrFun hz i)
    subst hδ
    exact (hinj _ 1 0 0 hF h1).mpr rfl

end GlobalTheory.PlaceInt.FormKer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.KillsFormalPointsIffMemCoordinateKernelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kills_formalPoints_iff_mem_coordinateKernel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), ∀ B : FB T.V (chD C.ch) (𝓞 E), IsBT C B → ∀ (n : ℕ) (mu : Matrix (Fin n) (Fin n) (𝓞 E)) (a : Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) (α : Fin n → Fin (chD C.ch) → T.V), (∀ b, FormPt C (a b) (α b)) → (Kills Xo mu a ↔ α ∈ kerM B mu) := by
  first | exact @GlobalTheory.PlaceInt.FormKer.kills_iff_mem_kerM | exact GlobalTheory.PlaceInt.FormKer.kills_iff_mem_kerM | (intros; apply GlobalTheory.PlaceInt.FormKer.kills_iff_mem_kerM <;> assumption)
end
end
