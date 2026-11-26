module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CoeffFSumDerivEqFderiv
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsBasisB
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.Ex.Arch

section Values
variable {O : Type} [CommRing O] [StarRing O]

def lin (B : AnArc O) (la : B.La) (v : B.V) : ℂ := -(2 * Real.pi * Complex.I) * v.1 la.y + Real.pi * B.H v.2 la.l

def IsPrim (B : AnArc O) (w₀ : O) : Prop :=
  w₀ + star w₀ = 1 ∧ (∀ l, B.chi l = (-1) ^ B.Ef l (B.FLam w₀ l)) ∧ ∀ y, (B.psi y : ℂ) = eTwoPi (B.T y (w₀ • y))

def IsAbFrame (M : NumB ℂ) (B : AnArc O) (ex : (Fin B.gB → ℂ) → M.A) (fr : (Fin B.gB → ℂ) → ℂˣ)
    (th : (Fin B.gB → ℂ) → ℂ) : Prop :=
  (∀ z w, ex (z + w) = ex z * ex w) ∧ Function.Surjective ex ∧ (∀ z, ex z = 1 ↔ z ∈ B.abelian₂) ∧ fr 0 = 1 ∧
    (∀ (l : B.abelian₂) z, (fr z : ℂ) = B.ah l z * fr (z + l)) ∧
    (∀ x y z, M.θ (ex x) (ex y) (ex z) * fr (x + y) * fr (x + z) * fr (y + z) = fr (x + y + z) * fr x * fr y * fr z) ∧
    (∀ x, M.σ (ex x) * fr x = fr (-x)) ∧ th ∈ B.Theta 1 0 ∧ ∀ z, M.th (ex z) = th z * fr z

structure Dict (N : NumD ℂ) (B : AnArc O) where

  eX : B.X ≃+ N.X

  ex : (Fin B.gB → ℂ) → N.A

  fr : (Fin B.gB → ℂ) → ℂˣ

  th : (Fin B.gB → ℂ) → ℂ

  ab : IsAbFrame N.toNumB B ex fr th

  c_eq : ∀ x, N.c (eX x) = ex (B.ct x)

  ψ_eq : ∀ x, N.ψ (eX x) * fr (B.ct x) = B.psi x

variable {N : NumD ℂ} {B : AnArc O}

def Dict.IsPt (d : Dict N B) (v : B.V) (g : N.Gt) : Prop :=
  g.b = d.ex v.2 ∧ ∀ x, (g.s (d.eX x) : ℂ) * d.fr (B.ct x + v.2) = eTwoPi (v.1 x) * d.fr (B.ct x) * d.fr v.2

def Dict.Rep (d : Dict N B) (k : ℕ) (la : B.La) (p : N.QT k) : Prop :=
  p.1.1.toAdd = d.eX la.y ∧ d.IsPt ((k : ℂ)⁻¹ • B.P0 la) p.1.2

def AllDict (P : ∀ {O : Type} [CommRing O] [StarRing O] {N : NumD ℂ} {B : AnArc O}, Dict N B → Prop) : Prop :=
  ∀ (O : Type) [CommRing O] [StarRing O] (N : NumD ℂ) (B : AnArc O) (d : Dict N B), P d

def PtSt : Prop := AllDict fun {_} _ _ {N} {B} d => (∀ v, ∃! g, d.IsPt v g) ∧ (∀ g, ∃ v, d.IsPt v g) ∧
  (∀ v v' g g', d.IsPt v g → d.IsPt v' g' → d.IsPt (v + v') (g * g')) ∧
  (∀ v, d.IsPt v 1 ↔ ∃ la : B.La, la.y = 0 ∧ v = B.P0 la) ∧ ∀ la : B.La, d.IsPt (B.P0 la) (N.io (d.eX la.y))

def QkSt : Prop := AllDict fun {_} _ _ {N} {B} d => ∀ k : ℕ, 0 < k → (∀ p, ∃ la, d.Rep k la p) ∧ (∀ la, ∃! p, d.Rep k la p) ∧
  (∀ la la' p p', d.Rep k la p → d.Rep k la' p' → d.Rep k (la + la') (p * p')) ∧
  ∀ (la la' : B.La) p p', d.Rep k la p → d.Rep k la' p' → (N.QEq p p' ↔ ∃ e, la' = la + k • e)

def WpSt : Prop := AllDict fun {_} _ _ {N} {B} d => ∀ k : ℕ, 0 < k → ∀ la la' p p', d.Rep k la p → d.Rep k la' p' →
  (N.wp p p' : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (B.EF la la' : ℂ) / k)

def TxSt : Prop := AllDict fun {O} _ _ {N} {B} d => ∀ w₀ : O, IsPrim B w₀ → ∀ (k : ℕ) (β : N.Form k),
  (∀ x y, B.be x y = β.be (d.eX x) (d.eX y)) → ∀ (m : ℕ) (hm : m ^ 2 ∣ k), Odd m → ∀ (w : ℂ) (u : ℂˣ), (u : ℂ) = eTwoPi w →
  ∀ la p, d.Rep (m ^ 2) la p → ∀ x : B.X, (N.twist β u).txT m (N.twQ β u hm p) (d.eX x) =
    (-1) ^ B.EF la (w₀ • la) * Complex.exp (-(lin B la (B.Pw w la) / (2 * (m : ℂ) ^ 2))) *
      (B.term 1 0 d.th x ((m : ℂ)⁻¹ • B.Pw w la) * eTwoPi (w * B.exponent 1 0 x))

def ThetaSt : Prop := ∀ (O : Type) [CommRing O] [StarRing O] (B : AnArc O) (w₀ : O), IsPrim B w₀ →
  ∀ th ∈ B.Theta 1 0, ∀ w : ℂ, Differentiable ℂ (B.Sum 1 0 th w) →
  ∀ (g : ℕ) (h : B.V ≃ₗ[ℂ] (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), Hm.IsHermitian →
    Submodule.span ℝ (Set.range (B.Pw w)) = ⊤ →
    (∀ a b, (hermForm Hm (h (B.Pw w a)) (h (B.Pw w b))).im = B.EF a b) →
    ∃ Θ : (Fin g → ℂ) → ℂ, Differentiable ℂ Θ ∧ (∀ v, Θ (h v) = 0 ↔ B.Sum 1 0 th w v = 0) ∧
      (∀ a z, Θ (z + h (B.Pw w a)) = (-1) ^ B.EF a (w₀ • a) * Complex.exp (Real.pi * hermForm Hm z (h (B.Pw w a)) +
        Real.pi / 2 * hermForm Hm (h (B.Pw w a)) (h (B.Pw w a))) * Θ z) ∧
      ∀ a (m : ℕ), m ≠ 0 → Complex.exp (-(Real.pi / 2 / (m : ℂ) ^ 2) * hermForm Hm (h (B.Pw w a)) (h (B.Pw w a))) *
          Θ ((m : ℂ)⁻¹ • h (B.Pw w a)) =
        Complex.exp (-(lin B a (B.Pw w a) / (2 * (m : ℂ) ^ 2))) * B.Sum 1 0 th w ((m : ℂ)⁻¹ • B.Pw w a)
end Values

section Fibre
variable {R : Type} [CommRing R] [IsDomain R]

def IsFib [Algebra (FractionRing R) ℂ] (P : PolAV (Sp R)) (J : (Sp ℂ ⟶ P.A.left) → P.L.ι) {g : ℕ}
    (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ)
    (ex : (Fin g → ℂ) → (TF (R := R) ℂ ⟶ P.A)) (fr : (Fin g → ℂ) → ℂˣ) : Prop :=
  (∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ P.L.U (J ψ)) ∧
  ∃ (P' : PolAV (Sp ℂ)) (φ : P'.A.left ⟶ P.A.left) (w : LB.Iso P'.L (P.L.pull φ)) (u : HolUnif P'.A P'.L g) (hΛ : u.Λ = Λ),
    IsGrpPullback P'.A P.A (TF (R := R) ℂ).hom φ ∧ w.IsGen ∧ u.IsAH Hm (fun l => χ ⟨l.1, hΛ ▸ l.2⟩) ∧
    (∀ v, IsTangent v → ∃! z, u.IsDiff z v) ∧ (∀ z, ∃! v, IsTangent v ∧ u.IsDiff z v) ∧
    (∀ f : P'.A ⟶ P'.A, IsMonHom f → ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, u.ex (F z) = u.ex z ≫ f) ∧
    (∀ z, (ex z).left = (u.ex z).left ≫ φ) ∧
    ∀ z i, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P'.L.U i →
      (fr z : ℂ) = valAt' (u.ex z).left _ (w.s (fun _ => J (ex z).left, i)).val * u.fr i z

def RosGen (P : PolAV (Sp R)) (f f' : P.A ⟶ P.A) (r : LB.Gen (LB.LinComb P.L (rosatiφ P.A f f') rosatiε)) : Prop :=
  r.IsGen ∧ LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ r (zero2 P.A)) (LB.oneGen P.L)

abbrev PrimT (P : PolAV (Sp R)) (f : P.A ⟶ P.A) : Type := LB.Gen (LB.LinComb P.L (K := Fin 4)
  ![(padd P.A (𝟙 _) f).left, 𝟙 P.A.left, f.left, (toUnit P.A ≫ η[P.A]).left] ![1, -2, -1, 2])

def PrimGen (P : PolAV (Sp R)) (f : P.A ⟶ P.A) (t : PrimT P f) : Prop :=
  t.IsGen ∧ LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ t (eSec P.A)) (LB.oneGen P.L)
end Fibre

def AllFib (P : ∀ {R : Type} [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (D : DegPre R)
    (_ : (Sp ℂ ⟶ D.P.A.left) → D.P.L.ι) {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) (_ : Matrix (Fin g) (Fin g) ℂ) (_ : Λ → ℂ)
    (_ : (Fin g → ℂ) → (TF (R := R) ℂ ⟶ D.P.A)) (_ : (Fin g → ℂ) → ℂˣ), Prop) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (D : DegPre R)
    (J : (Sp ℂ ⟶ D.P.A.left) → D.P.L.ι) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ)
    (ex : (Fin g → ℂ) → (TF (R := R) ℂ ⟶ D.P.A)) (fr : (Fin g → ℂ) → ℂˣ), IsFib D.P J Λ Hm χ ex fr → P D J Λ Hm χ ex fr

def FibExSt : Prop := ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (P : PolAV (Sp R))
  (J : (Sp ℂ ⟶ P.A.left) → P.L.ι), (∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ P.L.U (J ψ)) →
  ∃ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (Ef : LinearMap.BilinForm ℤ Λ)
    (ex : (Fin g → ℂ) → (TF (R := R) ℂ ⟶ P.A)) (fr : (Fin g → ℂ) → ℂˣ), IsFib P J Λ Hm χ ex fr ∧
    (∀ a b : Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧ Function.Bijective Ef

def FibGrpSt : Prop := AllFib fun {_} _ _ _ D _ {g} Λ Hm χ ex fr =>
  DiscreteTopology Λ ∧ Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ ∧ Hm.IsHermitian ∧
  (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ (∀ l, ‖χ l‖ = 1) ∧
  (∀ l m : Λ, χ (l + m) = χ l * χ m * Complex.exp (Real.pi * Complex.I * ((hermForm Hm l m).im : ℂ))) ∧
  (∀ z w, ex (z + w) = ex z * ex w) ∧ Function.Surjective ex ∧ (∀ z, ex z = 1 ↔ z ∈ Λ) ∧
  (∀ (l : Λ) z, (fr z : ℂ) = χ l * Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) * fr (z + l)) ∧
  ∀ f : D.P.A ⟶ D.P.A, IsMonHom f → ∃! F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, ex (F z) = ex z ≫ f

def FibCubeSt : Prop := AllFib fun {_} _ _ _ D J {_} _ _ _ ex fr => ∀ x y z,
  vF (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t (lift (ex x) (lift (ex y) (ex z))).left J *
    fr (x + y) * fr (x + z) * fr (y + z) * fr 0 = fr (x + y + z) * fr x * fr y * fr z

def FibSymSt : Prop := AllFib fun {_} _ _ _ D J {_} _ _ χ ex fr =>
  (∀ x, vF D.sym (ex x).left J * fr x = fr (-x)) ∧ ∀ l, χ (-l) = χ l

def FibRosSt : Prop := AllFib fun {_} _ _ _ D J {g} _ Hm _ ex fr => ∀ (f f' : D.P.A ⟶ D.P.A), IsMonHom f → IsMonHom f' →
  ∀ F G : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ z, ex (F z) = ex z ≫ f) → (∀ z, ex (G z) = ex z ≫ f') →
  ∀ r, RosGen D.P f f' r → (∀ x z, hermForm Hm (F x) z = hermForm Hm x (G z)) ∧
    ∀ x z, vF r (lift (ex x) (ex z)).left J * fr (F x) * fr z * fr (x + G z) = fr (F x + z) * fr x * fr (G z)

def FibPrimSt : Prop := AllFib fun {_} _ _ _ D J {g} Λ Hm χ ex fr => ∀ (f : D.P.A ⟶ D.P.A), IsMonHom f →
  ∀ (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hF : ∀ l ∈ Λ, F l ∈ Λ), (∀ z, ex (F z) = ex z ≫ f) →
  (∀ z w, hermForm Hm z w = hermForm Hm z (F w) + hermForm Hm (F z) w) →
  ∀ Ef : LinearMap.BilinForm ℤ Λ, (∀ a b : Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) →
  ∀ t, PrimGen D.P f t → (∀ l : Λ, χ l = (-1) ^ Ef l ⟨F l, hF l l.2⟩) ∧
    ∀ z, vF t (ex z).left J * fr z ^ 2 * fr (F z) = fr (z + F z) * fr 0 ^ 2

def FibSecSt : Prop := AllFib fun {_} _ _ _ D J {g} _ _ _ ex fr => ∀ s : H0 D.P.L 1, ∃ θ : (Fin g → ℂ) → ℂ,
  Differentiable ℂ θ ∧ ∀ z, sF s (ex z).left J = θ z * fr z

def FibLieSt : Prop := AllFib fun {R} _ _ _ D _ {g} _ _ _ ex _ => ∀ (O : Type) [CommRing O] (act : Geo.Tor.OAct O D.P.A)
  (F : O → Module.End ℂ (Fin g → ℂ)), (∀ a z, ex (F a z) = ex z ≫ act.act a) → ∀ (τ : O →+* ℂ) (n : ℕ),
  LieMult act (spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R _))) τ n →
    Module.finrank ℂ (⨅ a, (F a).eigenspace (τ a) : Submodule ℂ (Fin g → ℂ)) = n

def BrActSt : Prop := AllN fun {_} _ _ {D} {F} _ _ {N} ν => ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.X] (oa : D.OAct O),
  (∀ a, ∃ r, RosGen D.P (oa.onB.act a) (oa.onB.act (star a)) r ∧ ∀ y y' : N.X,
    (N.τ (ν.eX.symm (a • ν.eX y)) y' : F) * vF r (lift (ν.eA (N.c y)) (ν.eA (N.c y'))).left ν.J =
      N.τ y (ν.eX.symm (star a • ν.eX y'))) ∧
  (∀ a, ∃ r, RosGen D.P (oa.onB.act (star a)) (oa.onB.act a) r ∧ ∀ g g' c c', ν.Pt g c → ν.Pt g' c' → GtAct oa a g g' →
    ν.eA c'.b = ν.eA c.b ≫ oa.onB.act a ∧ ∀ χ : N.X,
      (c'.s χ : F) = c.s (ν.eX.symm (star a • ν.eX χ)) * vF r (lift (ν.eA (N.c χ)) (ν.eA c.b)).left ν.J) ∧
  ∀ w₀, TraceFormTwistIso D oa w₀ → ∃ t, PrimGen D.P (oa.onB.act w₀) t ∧ ∀ y : N.X,
    (N.τ y (ν.eX.symm (w₀ • ν.eX y)) : F) * vF t (ν.eA (N.c y)).left ν.J = N.ψ y

section ThetaShiftProofs
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

abbrev An (H : Host E) : Type 1 := @AnArc (𝓞 E) _ H.starRing

def SigOK (D : Datum H) (B : An H) (r : ℕ) (ρ : ℂ) : Prop := letI := H.starRing
  ∀ τ : 𝓞 E →+* ℂ, Module.finrank ℂ (⨅ a, (B.F a).eigenspace (τ a) : Submodule ℂ (Fin B.gB → ℂ)) + r =
    open Classical in if τ H.rt = ρ then D.p else D.q

variable {D : Datum H} {R : Type} [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ]

def AbLinked (A : ArcF D R ℂ) (B : An H) : letI := H.starRing
    ((Fin B.gB → ℂ) → A.N.A) → ((Fin B.gB → ℂ) → ℂˣ) → ((Fin B.gB → ℂ) → ℂ) → Prop := letI := H.starRing
  fun ex fr th => IsAbFrame A.N.toNumB B ex fr th ∧ th ≠ 0 ∧ (∀ l, B.chi l = (-1) ^ B.Ef l (B.FLam H.w0 l)) ∧
    SigOK D B (Module.finrank (𝓞 E) A.D₀.X) A.ρ ∧
    (∀ a z, A.ν.eA (ex (B.F a z)) = A.ν.eA (ex z) ≫ A.oa.onB.act a) ∧
    (∀ a b r, RosGen A.D₀.P (A.oa.onB.act a) (A.oa.onB.act b) r → ∀ x z,
      vF r (lift (A.ν.eA (ex x)) (A.ν.eA (ex z))).left A.ν.J * fr (B.F a x) * fr z * fr (x + B.F b z) =
        fr (B.F a x + z) * fr x * fr (B.F b z)) ∧
    ∀ t, PrimGen A.D₀.P (A.oa.onB.act H.w0) t → ∀ z,
      vF t (A.ν.eA (ex z)).left A.ν.J * fr z ^ 2 * fr (B.F H.w0 z) = fr (z + B.F H.w0 z)

def ActLinked (A : ArcF D R ℂ) (B : An H) : letI := H.starRing; Dict A.N B → Prop := letI := H.starRing
  fun d => (∀ (a : 𝓞 E) x, d.eX (a • x) = A.act a (d.eX x)) ∧
    ∀ (a : 𝓞 E) g g' c c' v, A.ν.Pt g c → A.ν.Pt g' c' → GtAct A.oa a g g' → d.IsPt v c → d.IsPt (B.actV a v) c'

def IsTower (D : Datum H) {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (EF : LinearMap.BilinForm ℤ La) (ζ : ℕ → ℂˣ)
    (f : ℕ → D.La → La) : Prop := ∀ n : ℕ, 0 < n →
  (∀ a b, ∃ e, f n (a + b) = f n a + f n b + n • e) ∧ (∀ (c : 𝓞 E) a, ∃ e, f n (c • a) = c • f n a + n • e) ∧
  (∀ a, (∃ e, f n a = n • e) ↔ ∃ b, a = n • b) ∧ (∀ x, ∃ a e, x = f n a + n • e) ∧
  (∀ m : ℕ, 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧
  ∀ a b, ((ζ n ^ D.EF a b : ℂˣ) : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF (f n a) (f n b) : ℂ) / n)
end ThetaShiftProofs

def ValSt : Prop := AllD fun {_} _ _ _ {H} D => ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ]
  (A : ArcF D R ℂ), ∃ (B : An H) (ex : _) (fr : _) (th : _), AbLinked A B ex fr th

def DictSt : Prop := AllD fun {E} _ _ _ {H} D => letI := H.starRing
  ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (A : ArcF D R ℂ) (k : ℕ) (β : A.N.Form k), A.Bal β →
  ∃ (B : An H) (d : Dict A.N B), ActLinked A B d ∧ (∀ x y, B.be x y = β.be (d.eX x) (d.eX y)) ∧ IsPrim B H.w0 ∧ d.th ≠ 0 ∧
    SigOK D B (Module.finrank (𝓞 E) B.X) A.ρ

def TowerSt : Prop := AllD fun {_} _ _ _ {H} D => letI := H.starRing
  ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (A : ArcF D R ℂ) (B : An H) (d : Dict A.N B),
  ActLinked A B d → ∃ f : ℕ → D.La → B.La, IsTower D B.EF A.I.ζ f ∧ ∀ n, 0 < n → ∀ a, d.Rep n (f n a) (A.q n a)

def TypeSt : Prop := AllD fun {E} _ _ _ {H} D => letI := H.starRing
  ∀ B : An H, SigOK D B (Module.finrank (𝓞 E) B.X) H.rt0 →
  ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)) (h : B.V ≃ₗ[ℂ] (Fin g → ℂ)), IsTypeFn H D.p D.q ty ∧
    ∀ (a : 𝓞 E) v i, h (B.actV a v) i = ty i (a : E) * h v i

def AllPer (Q : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (_ : Datum H) {La : Type} [AddCommGroup La]
    [Module (𝓞 E) La] (_ : LinearMap.BilinForm ℤ La) {g : ℕ} (_ : Fin g → (E →+* ℂ)) (_ : La →+ (Fin g → ℂ)), Prop) : Prop :=
  AllD fun {E} _ _ _ {H} D => ∀ (La : Type) [AddCommGroup La] [Module (𝓞 E) La] (EF : LinearMap.BilinForm ℤ La) (g : ℕ)
    (ty : Fin g → (E →+* ℂ)) (P : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), IsTypeFn H D.p D.q ty →
    Function.Bijective EF → (∀ (a : 𝓞 E) x y, EF (a • x) y = EF x (H.bar a • y)) →
    (∀ (a : 𝓞 E) x i, P (a • x) i = ty i (a : E) * P x i) → Function.Injective P → DiscreteTopology P.range →
    Submodule.span ℝ (Set.range P) = ⊤ → Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) →
    (∀ x y, (hermForm Hm (P x) (P y)).im = EF x y) → Q D EF ty P

def TripleSt : Prop := AllPer fun {E} _ _ _ {H} D {_} _ _ EF {g} ty P => letI := H.starRing
  ∃ (Q : PolAV (Sp ℂ)) (oa : Q.OAct (𝓞 E)) (L₀ : LB Q.A.left) (u : HolUnif Q.A L₀ g), Q.g = g ∧
    LBIso Q.L (cubeLB Q.A ![𝟙 Q.A, oa.act H.w0] Q.L) ∧ DetCond D (ofRingAct oa.toRingAct) (𝟙 (Sp ℂ)) H.rt0 ∧
    (∀ v, IsTangent v → ∃! z, u.IsDiff z v) ∧ (∀ z, ∃! v, IsTangent v ∧ u.IsDiff z v) ∧
    (∀ z, u.ex z = 1 ↔ z ∈ P.range) ∧ (∀ (a : 𝓞 E) z, u.ex (fun k => ty k (a : E) * z k) = u.ex z ≫ oa.act a) ∧
    ∀ (k : ℕ) a b (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) →
      WeilIs Q.A Q.L k (u.ex ((k : ℂ)⁻¹ • P a)) (u.ex ((k : ℂ)⁻¹ • P b)) (unitOn c)

def ReframeSt : Prop := ∀ (Q : PolAV (Sp ℂ)) (L₀ : LB Q.A.left) (g : ℕ) (u₀ : HolUnif Q.A L₀ g), Q.g = g →
  (∀ v, IsTangent v → ∃! z, u₀.IsDiff z v) → (∀ z, ∃! v, IsTangent v ∧ u₀.IsDiff z v) →
  ∃ (u : HolUnif Q.A Q.L Q.g) (Hm : Matrix (Fin Q.g) (Fin Q.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ)
    (F : (Fin g → ℂ) ≃ₗ[ℂ] (Fin Q.g → ℂ)), u.IsAH Hm χ ∧ (∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧
    ∀ z, u.ex (F z) = u₀.ex z

def ObjSt : Prop := AllPer fun {E} _ _ _ {H} D {_} _ _ EF {g} ty P => letI := H.starRing
  ∃ (Q : PolAV (Sp ℂ)) (oa : Q.OAct (𝓞 E)) (u : HolUnif Q.A Q.L Q.g) (Hm : Matrix (Fin Q.g) (Fin Q.g) ℂ) (χ : u.Λ → ℂ)
    (F : (Fin g → ℂ) ≃ₗ[ℂ] (Fin Q.g → ℂ)) (hΛ : ∀ a, F (P a) ∈ u.Λ),
    LBIso Q.L (cubeLB Q.A ![𝟙 Q.A, oa.act H.w0] Q.L) ∧ DetCond D (ofRingAct oa.toRingAct) (𝟙 (Sp ℂ)) H.rt0 ∧
    u.IsAH Hm χ ∧ (∀ z ∈ u.Λ, ∃ a, z = F (P a)) ∧ (∀ a b, (hermForm Hm (F (P a)) (F (P b))).im = EF a b) ∧
    (∀ a, χ ⟨F (P a), hΛ a⟩ = (-1) ^ EF a (H.w0 • a)) ∧
    (∀ (a : 𝓞 E) z, u.ex (F fun k => ty k (a : E) * z k) = u.ex (F z) ≫ oa.act a) ∧
    ∀ (k : ℕ) a b (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) →
      WeilIs Q.A Q.L k (u.ex ((k : ℂ)⁻¹ • F (P a))) (u.ex ((k : ℂ)⁻¹ • F (P b))) (unitOn c)

end GlobalTheory.Ex.Arch
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.OneBasis
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex

section Geo
variable {S S' : Scheme.{0}}

def RigPull (G' : Over S') [GrpObj G'] (G : Over S) [GrpObj G] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) {L' : LB G'.left}
    {L : LB G.left} (w : LB.Iso L' (L.pull φ)) (ρ' : LB.Gen (L'.pull (eSec G'))) (ρ : LB.Gen (L.pull (eSec G))) : Prop :=
  IsGrpPullback G' G f φ ∧ w.IsGen ∧ ρ'.IsGen ∧
    PMaps w (K := PUnit) (fun _ => eSec G') (fun _ => eSec G) (fun _ => 1) ρ' ρ f

def Thru {G' : Over S'} {G : Over S} {φ : G'.left ⟶ G.left} {L' : LB G'.left} {L : LB G.left} (w : LB.Iso L' (L.pull φ))
    (k : ℕ) {T' : Over S'} {T : Over S} (h : T'.left ⟶ T.left) (s : LB.Sec (LPow G L (k : ℤ) T))
    (s' : LB.Sec (LPow G' L' (k : ℤ) T')) : Prop :=
  ∀ (Z : Scheme.{0}) (r' : Z ⟶ (T' ⊗ G').left) (r : Z ⟶ (T ⊗ G).left),
    r ≫ (fst T G).left = r' ≫ (fst T' G').left ≫ h → r ≫ (snd T G).left = r' ≫ (snd T' G').left ≫ φ →
    ∀ (z : Z) (J) (J'), Good L z J → Good L' z J' →
      sval (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (k : ℤ)) s r z J =
        (GlobalTheory.ConstFam.wVal w z J J' (r' ≫ (snd T' G').left)).val ^ k *
          sval (L := L') (φ := fun _ : Fin 1 => (snd T' G').left) (ε := fun _ => (k : ℤ)) s' r' z J'

abbrev fnR {R : Type} [CommRing R] (x : R) : Γ(Sp R, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x

def FrameAt (G : Over S) (L : LB G.left) (N : ℕ) {K : Type} [Field K] (x : Sp K ⟶ S) {W : Type} [CommRing W] [IsDomain W]
    (gam : K →+* FractionRing W) (χ : Sp W ⟶ S) (h : spMap gam ≫ x = jK W ≫ χ) {n : ℕ}
    (b : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk x))) : Prop :=
  ∃ b' : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk χ)), BasisAlong G L N (𝟙 _) b' ∧
    ∀ i, ∃ s : LB.Sec (LPow G L (N : ℤ) (Over.mk (jK W ≫ χ))),
      Lin G L N (Over.homMk (spMap gam) h : Over.mk (jK W ≫ χ) ⟶ Over.mk x) (fun _ : Fin 1 => b i) (fun _ => 1) s ∧
      Lin G L N (Over.homMk (jK W) rfl : Over.mk (jK W ≫ χ) ⟶ Over.mk χ) (fun _ : Fin 1 => b' i) (fun _ => 1) s

def BasisBy (G : Over S) (L : LB G.left) (N : ℕ) {K : Type} [Field K] (x : Sp K ⟶ S) {W : Type} [CommRing W] [IsDomain W]
    (gam : K →+* FractionRing W) (χ : Sp W ⟶ S) (h : spMap gam ≫ x = jK W ≫ χ) {n : ℕ}
    (τ : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk x))) (B : Matrix (Fin n) (Fin n) (FractionRing W)) : Prop :=
  ∃ b : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk χ)), BasisAlong G L N (𝟙 _) b ∧
    ∀ i, ∃ s : LB.Sec (LPow G L (N : ℤ) (Over.mk (jK W ≫ χ))),
      Lin G L N (Over.homMk (spMap gam) h : Over.mk (jK W ≫ χ) ⟶ Over.mk x) τ (fun j => fnR (B i j)) s ∧
      Lin G L N (Over.homMk (jK W) rfl : Over.mk (jK W ≫ χ) ⟶ Over.mk χ) (fun _ : Fin 1 => b i) (fun _ => 1) s

def AllBasis (G : Over S) (L : LB G.left) (N : ℕ) {K : Type} [Field K] (x : Sp K ⟶ S) {n : ℕ}
    (τ : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk x))) : Prop :=
  ∀ (K' : Type) [Field K'] (ga : K →+* K') (x' : Sp K' ⟶ S) (h : spMap ga ≫ x = x'),
    BasisAlong G L N (Over.homMk (spMap ga) h : Over.mk x' ⟶ Over.mk x) τ
end Geo

section Tables

structure Tab (K : Type) (r : ℕ) where

  Pt : Type
  [grp : CommGroup Pt]

  E : Pt → (Fin r → K) → Prop

  C : ℕ → Pt → K → Prop

  Λ : ℕ → Pt → (Fin r → K) → Prop
attribute [instance] Tab.grp
variable {K K' : Type} [Field K] [Field K'] {r : ℕ}

def Tab.Full (T : Tab K r) (N n : ℕ) : Prop :=
  (∀ x, x ^ N = 1 → ∃ a, T.E x a) ∧ (∀ j x, x ^ ((n ^ j) ^ 2) = 1 → ∃ c, T.C (n ^ j) x c) ∧
    ∀ j h, h ^ (n ^ j) = 1 → ∃ l, T.Λ (n ^ j) h l

def Tab.Uniq (T : Tab K r) (N n : ℕ) : Prop :=
  (∀ x a, T.E x a → x ^ N = 1 ∧ ∀ a', T.E x a' → a' = a) ∧
    ∀ j x c, T.C (n ^ j) x c → x ^ ((n ^ j) ^ 2) = 1 ∧ ∀ c', T.C (n ^ j) x c' → c' = c

def Tab.Map (σ : K →+* K') (T : Tab K r) (T' : Tab K' r) : Prop :=
  ∃ β : T.Pt →* T'.Pt, (∀ k y, 1 ≤ k → y ^ k = 1 → ∃ x, x ^ k = 1 ∧ β x = y) ∧
    (∀ x a, T.E x a → T'.E (β x) (σ ∘ a)) ∧ (∀ k x c, T.C k x c → T'.C k (β x) (σ c)) ∧
    ∀ k h l, T.Λ k h l → T'.Λ k (β h) (σ ∘ l)

def Tab.Hs (T : Tab K r) (O : ValuationSubring K) (k : ℕ) : Subgroup T.Pt :=
  Subgroup.closure {y | ∃ x c, T.C k x c ∧ O.valuation c = 1 ∧ y = x ^ k}

def Tab.Loc (T : Tab K r) (O : ValuationSubring K) (B : Matrix (Fin r) (Fin r) K) (n d : ℕ) (κ : K) : Prop :=
  B.det ≠ 0 ∧ (∀ j x c, T.C (n ^ j) x c → c ∈ O) ∧
  (∀ j h l, h ∈ T.Hs O (n ^ j) → T.Λ (n ^ j) h l → ∀ i, B.mulVec l i ∈ O) ∧
  (∀ a : Fin r → K, (∀ i, a i ∈ O) → (∃ i, O.valuation (a i) = 1) →
    ∃ j h, h ∈ T.Hs O (n ^ j) ∧ ∀ l, T.Λ (n ^ j) h l → O.valuation (a ⬝ᵥ B.mulVec l) = 1) ∧
  ∃ π : Fin r → K, (∀ i, π i ≠ 0) ∧ O.valuation ((∏ i, π i) ^ d) = O.valuation κ ∧
    ∀ a : Fin r → K, (∀ i, a i / π i ∈ O) ↔ Matrix.vecMul a B ∈ Submodule.span O {e | ∃ x, T.E x e}

def Tab.Near (T : Tab K r) (N n d : ℕ) (κ : K) (σ : K →+* K') (O : ValuationSubring K') (T' : Tab K' r)
    (B : Matrix (Fin r) (Fin r) K') : Prop :=
  Tab.Map σ T T' ∧ T'.Uniq N n ∧ T'.Loc O B n d (σ κ)
end Tables

section Av
variable {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {F : Type} [Field F] [Algebra (FractionRing R) F]

def Cmb {k n : ℕ} (b : Fin n → SecA A F k) (a : Fin n → F) (t : SecA A F k) : Prop :=
  ∀ j, t.f j = ∑ i, liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (a i)) * (b i).f j

def ValAt {k : ℕ} (t : SecA A F k) (x : TFK (R := R) F ⟶ A.A)
    (e : LB.Gen (LB.LinComb A.L (Y := (TFK (R := R) F).left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))) (c : F) : Prop :=
  ∀ z J, Good A.L z J → sA t (ptSecT A.A x).left z J =
    @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) * (val (powFrame A.A A.L x e k) (𝟙 _) z J).val

def tab (ρ : LB.Gen (A.L.pull (eSec A.A))) (m : ℕ) (θ : SecA A F 1) {r : ℕ} (τ : Fin r → SecA A F (m ^ 2)) : Tab F r where
  Pt := TFK (R := R) F ⟶ A.A
  grp := Hom.commGroup
  E x a := x ^ (m ^ 2) = 1 ∧ ∃ t c, ThC A ρ m θ x t c ∧ Cmb τ a t
  C k x c := x ^ (k ^ 2) = 1 ∧ ∃ t, ThC A ρ k θ x t c
  Λ k h l := ∃ e, IsTorsFrame A ρ k h e ∧ ∀ j, ValAt (τ j) h e (l j)

def unitGrp (v : AddValuation F (WithTop ℚ)) (ρ : LB.Gen (A.L.pull (eSec A.A))) (θ : SecA A F 1) (k : ℕ) :
    Subgroup (TFK (R := R) F ⟶ A.A) :=
  Subgroup.closure {y | ∃ x t c, x ^ (k ^ 2) = 1 ∧ ThC A ρ k θ x t c ∧ v c = 0 ∧ y = x ^ k}

def FromGt {I : Ideal R} {D : DegData R I} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G) (k : ℕ) (x : TFK (R := R) F ⟶ A.A) : Prop :=
  ∃ p : QkPt D.toPre F k, p.y = 0 ∧ QkToAkU U F k p x

def IsBasisH {G : Over (Spec (CommRingCat.of R))} {L : LB G.left} {k n : ℕ} (σ : Fin n → H0 L k) : Prop :=
  ∀ s : H0 L k, ∃! c : Fin n → R, ∀ j, s.f j = ∑ i, resTop _ (scal G.hom (c i)) * (σ i).f j
end Av

def Adapted {X : Type} [AddCommGroup X] (k : ℕ) (Q : X → ℤ) {r : ℕ} (cls : Fin r → X) (mu : ℕ) : Prop :=
  (∀ i z, Q (cls i) ≤ Q (cls i + k • z)) ∧ (∀ i i', (∃ z, cls i = cls i' + k • z) → cls i = cls i') ∧
    (∀ α, ∃ i z, α = cls i + k • z) ∧ ∀ i₀, Nat.card {i // cls i = cls i₀} = mu

section Dvr
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V))
  (Q : D.toPre.X → ℤ)

open Classical in
def AdFam (k : ℕ) {r : ℕ} (cls : Fin r → D.toPre.X) (mu : ℕ) (f : Fin r → ∀ α, D.toPre.SecB k α) : Prop :=
  Adapted k Q cls mu ∧ (∀ i, ∃ s : Fam D.toPre (FractionRing V) k, GlobalTheory.ZH.FamOf D.toPre _ (f i) s) ∧
    (∀ i α, (∀ z, α ≠ cls i + k • z) → ∀ j, (f i α).f j = 0) ∧
    ∀ i₀, GlobalTheory.ZH.IsBasisB D.toPre (fun i : {i // cls i = cls i₀} => f i (cls i₀))
variable {F : Type} [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ))

def IntGe {k : ℕ} (s : Fam D.toPre F k) (q : ℚ) : Prop := ∀ α, VGe D F v k α (s.s α) q

def Norms (k : ℕ) {r : ℕ} (cls : Fin r → D.toPre.X) (s : Fin r → Fam D.toPre F k) : Prop :=
  (∀ s' : Fam D.toPre F k, ∃! a : Fin r → F, s' = ∑ i, a i • s i) ∧ ∀ (a : Fin r → F) (q : ℚ),
    (NuGe D Q F v k (∑ i, a i • s i) q ↔ ∀ i, ((q + (Q (cls i) : ℚ) / k : ℚ) : WithTop ℚ) ≤ v (a i)) ∧
    (IntGe D v (∑ i, a i • s i) q ↔ ∀ i, (q : WithTop ℚ) ≤ v (a i)) ∧
    ∀ i, VGe D F v k (cls i) ((∑ i, a i • s i).s (cls i)) q → (q : WithTop ℚ) ≤ v (a i)
end Dvr

theorem exists_valuationSubring {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) :
    ∃ O : ValuationSubring F, ∀ x, x ∈ O ↔ 0 ≤ v x :=
  ⟨(AddValuation.toValuation v).valuationSubring, fun _ => Iff.rfl⟩

theorem valuation_eq_one_iff {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {O : ValuationSubring F}
    (h : ∀ x, x ∈ O ↔ 0 ≤ v x) (x : F) : O.valuation x = 1 ↔ v x = 0 := by
  have e : O = (AddValuation.toValuation v).valuationSubring := ValuationSubring.ext _ _ h
  subst e
  exact (Valuation.isEquiv_valuation_valuationSubring (AddValuation.toValuation v)).eq_one_iff_eq_one.symm

end GlobalTheory.OneBasis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralDegenerationValues
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralDegenerationValues
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.ValuesExist
open GlobalTheory.TorusExt GlobalTheory.IndivisibleSection

section Sym
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A} (c : CubicalStr A L)
  {s : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[A]).left, 𝟙 A.left] ![1, -1])}

theorem prod_sym {T : Over S} (x : T ⟶ A) {U : Type} [CommGroup U] (h : (T.left ⟶ A.left) → U) :
    ∏ k : Fin 2, h (x.left ≫ ![(ι[A]).left, 𝟙 A.left] k) ^ (![1, -1] : Fin 2 → ℤ) k =
      h (x⁻¹).left * (h x.left)⁻¹ := by
  rw [Fin.prod_univ_two]
  simp [Hom.inv_def]

theorem val_sym_one (hr : LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ s (eSec A)) (LB.oneGen L.L))
    {T : Over S} {z : T.left} {J} (hJ : Good L.L z J) : val s (1 : T ⟶ A).left z J = 1 := by
  have := val_corr hJ hr (toUnit T).left
  rw [val_one, val_pull hJ] at this
  exact this

theorem val_sym_mul (hs : Function.Surjective (A ⊗ A).hom.appTop.hom) (hg : s.IsGen)
    (hr : LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ s (eSec A)) (LB.oneGen L.L))
    {T : Over S} {z : T.left} {J} (hJ : Good L.L z J) (x y : T ⟶ A) :
    val s (x * y).left z J * cubV c z J x x⁻¹ y⁻¹ = val s x.left z J * val s y.left z J * cubV c z J y y⁻¹ x := by
  have vs : ∀ {T : Over S} {z : T.left} {J} (_ : Good L.L z J) (r : T ⟶ A ⊗ A) (a : A ⊗ A ⟶ A),
      val (LB.pullGen L.L _ _ s a.left) r.left z J = val s (r ≫ a).left z J := fun hJ r a => val_pull hJ _ _ _
  have v : ∀ {T : Over S} {z : T.left} {J} (_ : Good L.L z J) (x y : T ⟶ A),
      val (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L _ _ s (fst A A * snd A A).left)
        (LB.pullGen L.L (thφ A (x3 A)) thε c.t (lift (fst A A) (lift (fst A A)⁻¹ (snd A A)⁻¹)).left)) (lift x y).left z J =
        val s (x * y).left z J * cubV c z J x x⁻¹ y⁻¹ ∧
      val (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L _ _ s (fst A A).left)
        (LB.pullGen L.L _ _ s (snd A A).left))
        (LB.pullGen L.L (thφ A (x3 A)) thε c.t (lift (snd A A) (lift (snd A A)⁻¹ (fst A A))).left)) (lift x y).left z J =
        val s x.left z J * val s y.left z J * cubV c z J y y⁻¹ x := fun hJ x y => by
    refine ⟨((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vs hJ _ _) (val_cub c _ hJ _ _ _))).trans ?_,
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
        (congrArg₂ (· * ·) (vs hJ _ _) (vs hJ _ _))) (val_cub c _ hJ _ _ _))).trans ?_⟩ <;>
    simp only [MonObj.comp_mul, GrpObj.comp_inv, lift_fst, lift_snd]
  rw [← (v hJ x y).1, ← (v hJ x y).2]
  refine gen_unique' L.isLB (fun U _ h => ?_) (A ⊗ A).hom (lift (1 : 𝟙_ (Over S) ⟶ A) (1 : 𝟙_ (Over S) ⟶ A)).left
    (Over.w _) hs
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hg _) (DVR.pullGen_isGen _ _ _ _ c.isGen _))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hg _)
      (DVR.pullGen_isGen _ _ _ _ hg _)) (DVR.pullGen_isGen _ _ _ _ c.isGen _)) (fun w I hI => ?_) _ _ z J hJ
  · refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) ((Fintype.prod_sum_type _).trans
      (congrArg₂ (· * ·) (prod_sym _ h) (prod_sym _ h))) (prod_cub _ _ _ h))).trans
      (Eq.trans ?_ ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (prod_sym _ h) (prod_cub _ _ _ h))).symm)
    simp only [mul_inv_cancel, _root_.one_mul, mul_inv, mul_comm (snd A A) (fst A A), mul_comm (snd A A)⁻¹ (fst A A)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · refine (v (T := 𝟙_ (Over S)) hI 1 1).1.trans (Eq.trans ?_ (v (T := 𝟙_ (Over S)) hI 1 1).2.symm)
    simp only [_root_.mul_one, inv_one, val_sym_one (T := 𝟙_ (Over S)) hr hI]
end Sym

section Val
variable {F : Type} [Field F] {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem coe_val (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) {z : Sp F} {J : (Sp F ⟶ X) → L.ι} (hJ : Good L z J) :
    ((stalkUnits z).symm (val t r z J) : F) = vF t r J := by
  refine (stalkConst z).injective ?_
  rw [← stalkUnits_val, MulEquiv.apply_symm_apply]
  exact (gs_unit r z _ (hJ.mem φ r) _).symm.trans (gs_eq_stalkConst r z
    (fun w _ => (Subsingleton.elim (α := PrimeSpectrum F) z w) ▸ hJ.mem φ r) _)
end Val

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem exists_th (hS : SecBaseChangeSt) [IsLocalRing R] [IsNoetherianRing R] :
    ∃ th : H0 D.P.L 1, ∀ s : H0 D.P.L 1, ∃ r : R, ∀ j, s.f j = resTop _ (scal D.P.A.hom r) * th.f j := by
  have hL := D.P.isLB
  obtain ⟨b, hb⟩ := exists_generator D hS
  obtain ⟨th, hth⟩ := exists_sec hL (φ' := fun _ : Fin 1 => 𝟙 D.P.A.left) (ε' := fun _ => ((1 : ℕ) : ℤ))
    (fun U _ h => by rw [prod_fam_zero]; simp) b
  refine ⟨th, fun s => ?_⟩
  obtain ⟨s', hs'⟩ := exists_sec hL (φ' := D.famφB 0) (ε' := DegPre.famε 1)
    (fun U _ h => by rw [prod_fam_zero]; simp) s
  obtain ⟨a, ha, -⟩ := hb s'
  refine ⟨a, secIsMul_of_sval hL fun y J hJ => ?_⟩
  rw [← hs' _ _ y J hJ, sval_of_secIsMul ha _ y hJ, hth _ _ y J hJ, Category.id_comp]

variable (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem exists_ext (S : ValuationSubring F) (hS : ∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) ∈ S)
    (x : TF (R := R) F ⟶ D.P.A) : ∃ x₀ : Sp S ⟶ D.P.A.left, spMap S.subtype ≫ x₀ = x.left := by
  haveI := D.P.isAb.proper
  have hE : ValuativeCriterion.Existence D.P.A.hom := by
    have h : UniversallyClosed D.P.A.hom := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  let f : R →+* S := ((algebraMap (FractionRing R) F).comp (algebraMap R _)).codRestrict S hS
  let Q : ValuativeCommSq D.P.A.hom :=
    { R := S, K := F, i₁ := x.left, i₂ := Spec.map (CommRingCat.ofHom f),
      commSq := ⟨by
        refine (Over.w x).trans ?_
        show Spec.map _ ≫ Spec.map _ = _
        rw [← Spec.map_comp, ← Spec.map_comp]
        rfl⟩ }
  obtain ⟨⟨l, h1, -⟩⟩ := hE Q
  exact ⟨l, h1⟩

theorem exists_gauge (S : ValuationSubring F) {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) :
    ∃ J : (Sp F ⟶ X) → L.ι, (∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) ∧ ∀ ψ, (∃ x₀ : Sp S ⟶ X, spMap S.subtype ≫ x₀ = ψ) →
      ∃ x₀ : Sp S ⟶ X, spMap S.subtype ≫ x₀ = ψ ∧ ⊤ ≤ x₀ ⁻¹ᵁ L.U (J ψ) := by
  have key : ∀ ψ : Sp F ⟶ X, ∃ j, ⊤ ≤ ψ ⁻¹ᵁ L.U j ∧ ((∃ x₀ : Sp S ⟶ X, spMap S.subtype ≫ x₀ = ψ) →
      ∃ x₀ : Sp S ⟶ X, spMap S.subtype ≫ x₀ = ψ ∧ ⊤ ≤ x₀ ⁻¹ᵁ L.U j) := fun ψ => by
    by_cases h : ∃ x₀ : Sp S ⟶ X, spMap S.subtype ≫ x₀ = ψ
    · obtain ⟨x₀, rfl⟩ := h
      obtain ⟨j, hj⟩ := exists_chart hL (x₀ (IsLocalRing.closedPoint S))
      have e : x₀ ⁻¹ᵁ L.U j = ⊤ := DVR.eq_top_of_closedPoint_mem _ hj
      exact ⟨j, fun w _ => e.ge (trivial : spMap S.subtype w ∈ (⊤ : (Sp S).Opens)), fun _ => ⟨x₀, rfl, e.ge⟩⟩
    · obtain ⟨j, hj⟩ := exists_chart hL (ψ (IsLocalRing.closedPoint F))
      exact ⟨j, (DVR.eq_top_of_closedPoint_mem (ψ ⁻¹ᵁ L.U j) hj).ge, fun h' => (h h').elim⟩
  choose J h₁ h₂ using key
  exact ⟨J, h₁, h₂⟩

theorem exists_numOf (hG : GlobalFnsSt) (he : D.PsiEven) (hb : D.TauBimult) (th : H0 D.P.L 1)
    (hth : ∀ s : H0 D.P.L 1, ∃ r : R, ∀ j, s.f j = resTop _ (scal D.P.A.hom r) * th.f j)
    (J : (Sp F ⟶ D.P.A.left) → D.P.L.ι) (good : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U (J ψ)) :
    ∃ (N : NumD F) (ν : NumOf D F N), ν.J = J := by
  let z : Sp F := IsLocalRing.closedPoint F
  have hJ : Good D.P.L z J := fun ψ => good ψ trivial
  let e := (stalkUnits z).symm
  have C : IsCub (cubV D.cub (T := TF (R := R) F) z J) := isCub_cubV D.cub (T := TF (R := R) F) hJ
  have sj : Function.Surjective (D.P.A ⊗ D.P.A).hom.appTop.hom := by
    rw [← Over.w (snd D.P.A D.P.A)]
    exact surj_comp (surj_snd hG D.P.isAb _) (hG _ _ D.P.isAb).2
  let ρ : ((Sp F).presheaf.stalk z)ˣ := val (Z := Sp F) (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (TF (R := R) F).hom z J
  let p : D.X → ((Sp F).presheaf.stalk z)ˣ := fun χ => val (Z := Sp F) (D.psi χ) (jFK (R := R) F) z J
  have hτ : ∀ a b, val (Z := Sp F) (D.tau a b) (jFK (R := R) F) z J = p (a + b) * (p a)⁻¹ * (p b)⁻¹ * ρ⁻¹ := fun a b =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _)))
      ((val_inv _ _).trans (congrArg (·⁻¹) (val_pull hJ _ _ _))))
  have hx : ∀ χ, jFK (R := R) F ≫ D.xK χ = (DegPre.cF D F χ).left := fun χ => (Category.assoc _ _ _).symm
  let N : NumD F :=
    { A := TF (R := R) F ⟶ D.P.A
      θ := fun x y u => e (cubV D.cub (T := TF (R := R) F) z J x y u)
      cub := ⟨fun x y => by rw [C.face, map_one], fun x y u => by rw [C.s01], fun x y u => by rw [C.s12],
        fun x x' x'' y => by rw [← map_mul, ← map_mul, C.coc]⟩
      σ := fun x => e (val D.sym x.left z J)
      σ_one := (congrArg e (val_sym_one (L := ⟨D.P.L, D.rig, D.P.isLB, D.rig_gen⟩) D.sym_rig
        (T := TF (R := R) F) hJ)).trans (map_one e)
      σ_mul := fun x y => by
        rw [← map_mul, ← map_mul, ← map_mul]
        exact congrArg e (val_sym_mul D.cub sj D.sym_gen D.sym_rig (T := TF (R := R) F) hJ x y)
      th := fun x => sF th x.left J * ((e ρ)⁻¹ : Fˣ)
      X := D.X
      c := DegPre.cF D F
      c_add := fun a b => by
        rw [DegPre.cF, D.c_add]
        exact MonObj.comp_mul _ _ _
      ψ := fun χ => e (p χ * ρ)
      even := fun χ => by
        have h := val_corr hJ (he χ) (jFK (R := R) F)
        rw [val_mul hJ, val_pull hJ, hx] at h
        rw [← map_mul, mul_right_comm]
        exact congrArg (fun q => e (q * ρ)) h
      bimult := fun a a' b => by
        have h := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hτ _ _) (val_pull hJ _ _ _))).symm.trans
          ((val_corr hJ (hb a a' b) (jFK (R := R) F)).trans
            ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hτ _ _) (hτ _ _))))
        have h3 : jFK (R := R) F ≫ D.pt3 a a' b =
            (lift (DegPre.cF D F a) (lift (DegPre.cF D F a') (DegPre.cF D F b))).left := by
          let κ : TF (R := R) F ⟶ TK R := Over.homMk (jFK (R := R) F) rfl
          refine congrArg CommaMorphism.left (show κ ≫ lift _ (lift _ _) = _ from ?_)
          simp only [comp_lift, comp_toUnit_assoc]
        rw [h3] at h
        simp only [← map_div, ← map_mul]
        refine congrArg e ?_
        have k : ∀ u v w, (u * ρ) / (v * ρ) / (w * ρ) = u * v⁻¹ * w⁻¹ * ρ⁻¹ := fun u v w => by
          apply Additive.ofMul.injective
          simp only [ofMul_mul, ofMul_inv, ofMul_div]
          abel
        rw [k, k, k]
        exact h }
  have hρ : (e ρ : F) = vF (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig
    (TF (R := R) F).hom J := coe_val _ _ hJ
  exact ⟨N,
    { J := J, good := good, th := th, th_gen := hth, eA := MulEquiv.refl _, eX := AddEquiv.refl _
      c_eq := fun _ => rfl
      θ_eq := fun x y u => coe_val _ _ hJ
      σ_eq := fun x => coe_val _ _ hJ
      th_eq := fun x => by
        rw [← hρ]
        exact Units.inv_mul_cancel_right _ _
      ψ_eq := fun χ => by
        rw [← hρ, ← coe_val _ _ hJ]
        exact (congrArg Units.val (map_mul e _ _)).trans (Units.val_mul _ _) }, rfl⟩

theorem exists_integral_values : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (D : DegPre R), D.PsiEven → D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (S : ValuationSubring F), (∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) ∈ S) → ∃ (N : NumD F) (ν : NumOf D F N), ν.Integral S := by
  intro hL R _ _ _ _ D he hb F _ _ S hS
  obtain ⟨th, hth⟩ := exists_th D hL.secBaseChange
  obtain ⟨J, good, hJ⟩ := exists_gauge F S D.P.isLB
  obtain ⟨N, ν, rfl⟩ := exists_numOf D F hL.globalFns he hb th hth J good
  exact ⟨N, ν, fun x => hJ _ (exists_ext D F S hS x)⟩

end GlobalTheory.ValuesExist
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralDegenerationValuesStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_degeneration_values : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (D : DegPre R), D.PsiEven → D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (S : ValuationSubring F), (∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) ∈ S) → ∃ (N : NumD F) (ν : NumOf D F N), ν.Integral S := by
  first | exact @GlobalTheory.ValuesExist.exists_integral_values | exact GlobalTheory.ValuesExist.exists_integral_values | (intros; apply GlobalTheory.ValuesExist.exists_integral_values <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidificationPullbackCompatibleIso
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam

noncomputable section
namespace GlobalTheory.Ex.OneGen

section Defs
variable {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G)))

def ThG (m : ℕ) {T : Over S} (th : LB.Sec (LPow G L ((1 : ℕ) : ℤ) T)) (x : T ⟶ G) (c : Γ(T.left, ⊤)) : Prop :=
  x ^ (m ^ 2) = 1 ∧ ∃ (t : LB.Sec (LPow G L ((m ^ 2 : ℕ) : ℤ) T))
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T G).left, (snd T G ^ m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]))
    (s₁ : LB.Sec (LPow G L ((m ^ 2 : ℕ) : ℤ) T)) (θ : ThetaGrp G L ((m ^ 2 : ℕ) : ℤ) T),
    α.IsGen ∧ LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ α (ptSecT G 1).left) (rigT G L ρ T (((m ^ 2 : ℕ) : ℤ) - 1)) ∧
    IsTwistPull G L (mulT G _ m) (snd _ G ^ m) (lift_snd _ _) ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α th s₁ ∧
    SymLift G L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) x θ ∧ IsActOf G L ((m ^ 2 : ℕ) : ℤ) θ s₁ t ∧
    ∀ z J, Good L z J → VVRank.sv G t (ptSecT G 1).left z J =
      gs (𝟙 _) z ⊤ c * (val (rigT G L ρ T ((m ^ 2 : ℕ) : ℤ)) (𝟙 _) z J).val

def NZ {V : Type} [CommRing V] [IsLocalRing V] (χ : Sp V ⟶ S) (σ : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ))) : Prop :=
  ∃ g : (Over.mk χ ⊗ G).left, (fst (Over.mk χ) G).left g = closedPoint V ∧ g ∈ nonzeroLocus σ

def UnivBasis {K : Type} [CommRing K] (x : Sp K ⟶ S) (e : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk x))) : Prop :=
  ∀ (K' : Type) [CommRing K'] (i : K →+* K') (x' : Sp K' ⟶ S) (h : spMap i ≫ x = x') (s : SecM G L ((1 : ℕ) : ℤ) (Over.mk x')),
    ∃! c : Γ((Over.mk x').left, ⊤),
      s = c • SecM.ofSec G (VVRank.pullS G _ (Over.homMk (spMap i) h : Over.mk x' ⟶ Over.mk x) e)


variable {G L} in
def IsRigidificationPullbackCompatibleIso {S' : Scheme.{0}} {A : Over S'} [GrpObj A] {φ : A.left ⟶ G.left} {L' : LB A.left} (w : LB.Iso L' (L.pull φ))
    (f : S' ⟶ S) (ρ' : LB.Gen (L'.pull (eSec A))) (ρ : LB.Gen (L.pull (eSec G))) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ S') (z : Z) (J) (J'), Good L z J → Good L' z J' →
    val (L := L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) ρ (r ≫ f) z J =
      wVal w z J J' (r ≫ eSec A) * val (L := L') (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) ρ' r z J'
end Defs

theorem thG_iff {R : Type} [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) {F : Type} [Field F]
    [Algebra (FractionRing R) F] (ρ : LB.Gen (A.L.pull (eSec A.A))) (m : ℕ) (th : GlobalTheory.UT.SecA A F 1)
    (x : TFK (R := R) F ⟶ A.A) (c : F) :
    ThG A.A A.L ρ m th x (fnOf c) ↔ x ^ (m ^ 2) = 1 ∧ ∃ t, GlobalTheory.UT.ThC A ρ m th x t c := Iff.rfl

section Move
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left} {w : LB.Iso L₁ (L₀.pull φ)}
  {ρ₀ : LB.Gen (L₀.pull (eSec G))} {ρ₁ : LB.Gen (L₁.pull (eSec A))}

theorem val_rigT (k : ℤ) {Z : Scheme.{0}} (r : Z ⟶ T₀.left) (z : Z) {J} (hJ : Good L₀ z J) :
    val (rigT G L₀ ρ₀ T₀ k) r z J =
      val (L := L₀) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) ρ₀ (r ≫ T₀.hom) z J ^ k := by
  have hz := hJ.mem (fun _ : Fin 1 => T₀.hom ≫ eSec G) r
  rw [val_of (L := L₀) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) ρ₀ (r ≫ T₀.hom) z J
    (fun _ => J (r ≫ T₀.hom ≫ eSec G)) (fun _ => by rw [Category.assoc])]
  refine (map_zpow _ _ _).trans (congrArg (· ^ k) ?_)
  exact (gm_res r z _ hz _).trans (gm_pull r T₀.hom z _ (rigT_le G L₀ _ hz) _)


include hτ in
theorem IsRigidificationPullbackCompatibleIso.rigT (h : IsRigidificationPullbackCompatibleIso w f ρ₁ ρ₀) (k : ℤ) {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) {J J'}
    (hJ : Good L₀ z J) (hJ' : Good L₁ z J') : val (rigT G L₀ ρ₀ T₀ k) (r ≫ τ) z J =
      wVal w z J J' (r ≫ T.hom ≫ eSec A) ^ k * val (rigT A L₁ ρ₁ T k) r z J' := by
  rw [val_rigT k _ z hJ, val_rigT k _ z hJ', Category.assoc, hτ, ← Category.assoc, h _ _ z J J' hJ hJ', mul_zpow,
    Category.assoc]

theorem norm_iff (hr : IsRigidificationPullbackCompatibleIso w f ρ₁ ρ₀) {m : ℕ} {a : ℤ}
    {α₀ : LB.Gen (LB.LinComb L₀ (K := Fin 2) ![(snd T₀ G).left, (snd T₀ G ^ m).left] ![a, -((1 : ℕ) : ℤ)])}
    {α : LB.Gen (LB.LinComb L₁ (K := Fin 2) ![(snd T A).left, (snd T A ^ m).left] ![a, -((1 : ℕ) : ℤ)])}
    (H : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) J J', Good L₀ z J → Good L₁ z J' →
      val α₀ (r ≫ psi hp τ hτ) z J = (wVal w z J J' (r ≫ (snd T A).left) ^ a *
        wVal w z J J' (r ≫ (snd T A ^ m).left) ^ (-((1 : ℕ) : ℤ))) * val α r z J')
    {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) {J J'} (hJ : Good L₀ z J) (hJ' : Good L₁ z J') :
    val α₀ ((r ≫ τ) ≫ (ptSecT G 1).left) z J = val (Out.rigT G L₀ ρ₀ T₀ (a - 1)) (r ≫ τ) z J ↔
      val α (r ≫ (ptSecT A 1).left) z J' = val (Out.rigT A L₁ ρ₁ T (a - 1)) r z J' := by
  rw [hr.rigT τ hτ _ r z hJ hJ', Category.assoc, ← psi_ptSec hp τ hτ (over_one hp τ hτ), ← Category.assoc,
    H _ _ _ _ _ hJ hJ', Category.assoc, Category.assoc, NormTheta.ptSec_snd, NormTheta.ptSec_snd_pow, ← zpow_add,
    show a + -((1 : ℕ) : ℤ) = a - 1 from rfl, mul_right_inj]

theorem value_iff (hr : IsRigidificationPullbackCompatibleIso w f ρ₁ ρ₀) {a : ℤ} {t₀ : LB.Sec (LPow G L₀ a T₀)} {t : LB.Sec (LPow A L₁ a T)}
    (ht : SecRel hp τ hτ w t t₀) {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) {J J'} (hJ : Good L₀ z J) (hJ' : Good L₁ z J')
    (c : Z.presheaf.stalk z) :
    VVRank.sv G t₀ ((r ≫ τ) ≫ (ptSecT G 1).left) z J = c * (val (Out.rigT G L₀ ρ₀ T₀ a) (r ≫ τ) z J).val ↔
      VVRank.sv A t (r ≫ (ptSecT A 1).left) z J' = c * (val (Out.rigT A L₁ ρ₁ T a) r z J').val := by
  rw [hr.rigT τ hτ _ r z hJ hJ', Category.assoc, ← psi_ptSec hp τ hτ (over_one hp τ hτ), ← Category.assoc,
    ht _ _ _ _ _ hJ hJ', Category.assoc, NormTheta.ptSec_snd, Units.val_mul, mul_left_comm, Units.mul_right_inj]

theorem value_at {a : ℤ} {t : LB.Sec (LPow A L₁ a T)} {c : Γ(T.left, ⊤)} (hL₁ : L₁.IsLB)
    (h : ∀ z J, Good L₁ z J → VVRank.sv A t (ptSecT A 1).left z J =
      gs (𝟙 _) z ⊤ c * (val (Out.rigT A L₁ ρ₁ T a) (𝟙 _) z J).val)
    {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) {J} (hJ : Good L₁ z J) :
    VVRank.sv A t (r ≫ (ptSecT A 1).left) z J = gs r z ⊤ c * (val (Out.rigT A L₁ ρ₁ T a) r z J).val :=
  sv_of_isValueAt (x := (1 : T ⟶ A)) (ρ := Out.rigT A L₁ ρ₁ T a) (isValueAt_of_sv hL₁ fun y J hJ => by
    rw [Category.id_comp]; exact h y J hJ) r z hJ

theorem ThG.move [IsCommMonObj A] (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (hr : IsRigidificationPullbackCompatibleIso w f ρ₁ ρ₀) {m : ℕ}
    {x : T ⟶ A} {x₀ : T₀ ⟶ G} (hx : τ ≫ x₀.left = x.left ≫ φ) (hn : x ^ (m ^ 2) = 1)
    {th : LB.Sec (LPow A L₁ ((1 : ℕ) : ℤ) T)} {th₀ : LB.Sec (LPow G L₀ ((1 : ℕ) : ℤ) T₀)} (hth : SecRel hp τ hτ w th th₀)
    {c : Γ(T₀.left, ⊤)} (H : ThG G L₀ ρ₀ m th₀ x₀ c) : ThG A L₁ ρ₁ m th x (τ.appTop.hom c) := by
  obtain ⟨-, t₀, α₀, s₀, θ₀, h₁, h₂, h₃, h₄, h₅, h₆⟩ := H
  obtain ⟨s, hs⟩ := exists_secRel hp τ hτ hw hL₀ hL₁ s₀
  obtain ⟨t, ht⟩ := exists_secRel hp τ hτ hw hL₀ hL₁ t₀
  obtain ⟨α, hα, vα⟩ := exists_genThrough₂ hp τ hτ hw hL₀ hL₁ (psi_pow hp τ hτ m) α₀ h₁
  obtain ⟨θ, hθ, hθ'⟩ := symLift_move hp τ hτ hw hL₀ hL₁ hx hn h₄
  refine ⟨hn, t, α, s, θ, hα, corr_of_val hL₁ fun y J' hJ' => ?_,
    isTwistPull_move hp τ hτ hL₀ hL₁ (psi_pow hp τ hτ m) hα vα hth hs h₃, hθ, hθ' _ _ _ _ hs ht h₅, fun y J' hJ' => ?_⟩
  · obtain ⟨J, hJ⟩ := exists_good' hL₀ y
    rw [val_pull hJ']
    exact (norm_iff hp τ hτ hr vα _ y hJ hJ').1 ((val_pull hJ _ _ _).symm.trans (val_corr hJ h₂ _))
  · obtain ⟨J, hJ⟩ := exists_good' hL₀ y
    have q := (value_iff hp τ hτ hr ht (𝟙 _) y hJ hJ' _).1 (value_at hL₀ h₆ (𝟙 _ ≫ τ) y hJ)
    rw [Category.id_comp (ptSecT A 1).left] at q
    exact q.trans (congrArg (· * _) (gs_pull (𝟙 _) τ y ⊤ trivial c).symm)

theorem ThG.up [IsIso τ] [IsCommMonObj A] (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (hr : IsRigidificationPullbackCompatibleIso w f ρ₁ ρ₀) {m : ℕ}
    {x : T ⟶ A} {x₀ : T₀ ⟶ G} (hx : τ ≫ x₀.left = x.left ≫ φ) (hn : x₀ ^ (m ^ 2) = 1)
    {th : LB.Sec (LPow A L₁ ((1 : ℕ) : ℤ) T)} {th₀ : LB.Sec (LPow G L₀ ((1 : ℕ) : ℤ) T₀)} (hth : SecRel hp τ hτ w th th₀)
    {c : Γ(T.left, ⊤)} (H : ThG A L₁ ρ₁ m th x c) : ThG G L₀ ρ₀ m th₀ x₀ ((inv τ).appTop.hom c) := by
  obtain ⟨h₀, t, α, s, θ, h₁, h₂, h₃, h₄, h₅, h₆⟩ := H
  obtain ⟨s₀, hs⟩ := exists_secRel_up hp τ hτ hw hL₀ hL₁ s
  obtain ⟨t₀, ht⟩ := exists_secRel_up hp τ hτ hw hL₀ hL₁ t
  obtain ⟨α₀, hα, vα⟩ := ThetaPtUp.exists_genThrough_up hp τ hτ hw hL₀ hL₁ (psi_pow hp τ hτ m) α h₁
  obtain ⟨θ₀, hθ, hθ'⟩ := ThetaPtUp.symLift_up hp τ hτ hw hL₀ hL₁ hx h₀ h₄
  refine ⟨hn, t₀, α₀, s₀, θ₀, hα, corr_of_val hL₀ fun y J hJ => ?_,
    ThetaPtUp.isTwistPull_up hp τ hτ hL₀ hL₁ (psi_pow hp τ hτ m) hα vα hth hs h₃, hθ, hθ' _ _ _ _ hs ht h₅,
    fun y J hJ => ?_⟩
  · obtain ⟨J', hJ'⟩ := exists_good' hL₁ y
    rw [val_pull hJ, ← IsIso.inv_hom_id τ]
    exact (norm_iff hp τ hτ hr vα _ y hJ hJ').2 ((val_pull hJ' _ _ _).symm.trans (val_corr hJ' h₂ _))
  · obtain ⟨J', hJ'⟩ := exists_good' hL₁ y
    have q := (value_iff hp τ hτ hr ht (inv τ) y hJ hJ' _).2 (value_at hL₁ h₆ (inv τ) y hJ')
    rw [IsIso.inv_hom_id, Category.id_comp] at q
    exact q.trans (congrArg (· * _) ((gs_pull (𝟙 _) (inv τ) y ⊤ trivial c).trans (by rw [Category.id_comp])).symm)

theorem ThG.smul (hL₁ : L₁.IsLB) {m : ℕ} {x : T ⟶ A} {th th' : LB.Sec (LPow A L₁ ((1 : ℕ) : ℤ) T)} {a c : Γ(T.left, ⊤)}
    (h : SecM.ofSec A th' = a • SecM.ofSec A th) (H : ThG A L₁ ρ₁ m th x c) : ThG A L₁ ρ₁ m th' x (a * c) := by
  obtain ⟨h₀, t, α, s, θ, h₁, h₂, h₃, h₄, h₅, h₆⟩ := H
  have tw : ∀ {p q : ℤ} {κ : T ⊗ A ⟶ A} {β} (_ : β.IsGen) {u u' : LB.Sec (LPow A L₁ q T)} {v : LB.Sec (LPow A L₁ p T)},
      SecM.ofSec A u' = a • SecM.ofSec A u → IsTwistPull A L₁ (lift (fst T A) κ) κ (lift_snd _ _) p q β u v →
      IsTwistPull A L₁ (lift (fst T A) κ) κ (lift_snd _ _) p q β u' (SecM.toSec A (a • SecM.ofSec A v)) := by
    intro p q κ β hβ u u' v hu hv
    refine VVRank.isTwistPull_of_sv A hL₁ hβ fun y J hJ => ?_
    have e₁ := sv_of_eq_mul (s := u') (t := u) (c := a) (fun j => congrArg (fun q => q.1 j) hu)
      (𝟙 _ ≫ (lift (fst T A) κ).left) y hJ
    have e₂ := sv_of_eq_mul (s := SecM.toSec A (a • SecM.ofSec A v)) (t := v) (c := a) (fun j => rfl) (𝟙 _) y hJ
    rw [e₁, e₂, VVRank.sv_of_isTwistPull A hv (𝟙 _) y hJ, Category.assoc, ← Over.comp_left, lift_fst, mul_left_comm]
  refine ⟨h₀, SecM.toSec A (a • SecM.ofSec A t), α, SecM.toSec A (a • SecM.ofSec A s), θ, h₁, h₂, tw h₁ h h₃, h₄,
    tw θ.isGen rfl h₅, fun y J hJ => ?_⟩
  rw [sv_of_eq_mul (s := SecM.toSec A (a • SecM.ofSec A t)) (t := t) (c := a) (fun j => rfl) _ y hJ, h₆ y J hJ,
    ptSecT_fst, ← _root_.mul_assoc, gs_mul _ y ⊤ trivial]


include hp in
theorem exists_rigidificationPullbackCompatibleIso (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (hρ : ρ₀.IsGen) :
    ∃ ρ₁ : LB.Gen (L₁.pull (eSec A)), ρ₁.IsGen ∧ IsRigidificationPullbackCompatibleIso w f ρ₁ ρ₀ := by
  have e : eSec A ≫ φ = f ≫ eSec G := by
    have := over_one hp (T := baseOver S') (T₀ := baseOver S) f ((Category.comp_id _).trans (Category.id_comp _).symm)
    exact ((Category.id_comp _).symm.trans (Category.assoc _ _ _).symm).trans
      (this.symm.trans (congrArg (f ≫ ·) (Category.id_comp _)))
  obtain ⟨ρ₁, h₁, h₂⟩ := exists_gen_through (φ' := fun _ : PUnit => eSec A) (φ := fun _ : PUnit => eSec G)
    (ε := fun _ => 1) (h := f) hw hL₀ hL₁ (fun _ => e) ρ₀ hρ
  exact ⟨ρ₁, h₁, fun Z r z J J' hJ hJ' => (h₂ Z r z J J' hJ hJ').trans (by rw [Fintype.prod_unique, zpow_one])⟩

end Move

theorem ThG.unique (hLaw : Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S)
    {ρ : LB.Gen (P.L.pull (eSec P.A))} {m : ℕ} (hm : Odd m) (hu : IsUnit ((m ^ 2 : ℕ) : Γ(S, ⊤))) {T : Over S}
    {th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T)} {x : T ⟶ P.A} {c c' : Γ(T.left, ⊤)} (H : ThG P.A P.L ρ m th x c)
    (H' : ThG P.A P.L ρ m th x c') : c = c' := by
  obtain ⟨hx, t, α, s₁, θ, hα, hn, hs₁, hθ, ht, hc⟩ := H
  obtain ⟨-, t', α', s₁', θ', hα', hn', hs₁', hθ', ht', hc'⟩ := H'
  have hL := P.isLB
  obtain ⟨-, huniq⟩ := hLaw.symLift _ P (m ^ 2) hm.pow hu T x hx
  have ea := gen_unique hL (fst T P.A).left (ptSecT P.A 1).left NormTheta.ptSec_fst
    (CommPairing.surj_fst hLaw.globalFns P.isAb T) hα hα' (fun y J hJ => by
      have a := (val_corr hJ hn (𝟙 _)).trans (val_corr hJ hn' (𝟙 _)).symm
      rwa [val_pull hJ, val_pull hJ, Category.id_comp] at a)
  obtain rfl : s₁ = s₁' := NormTheta.sec_ext (sec_ext_val hL fun y J hJ =>
    (ThetaLin.sval_of_isTwistPull P.A hs₁ _ y hJ).trans
      (Eq.trans (by rw [ea _ _ y J hJ]) (ThetaLin.sval_of_isTwistPull P.A hs₁' _ y hJ).symm))
  have eθ := huniq θ θ' hθ hθ'
  have ept : θ.pt = θ'.pt := hθ.pt_eq.trans hθ'.pt_eq.symm
  obtain rfl : t = t' := NormTheta.sec_ext (sec_ext_val hL fun y J hJ =>
    (ThetaLin.sval_of_isTwistPull P.A ht _ y hJ).trans
      (Eq.trans (by rw [val_corr hJ eθ, ept]) (ThetaLin.sval_of_isTwistPull P.A ht' _ y hJ).symm))
  refine fn_ext (V := ⊤) fun y _ => ?_
  obtain ⟨J, hJ⟩ := exists_good' hL y
  exact (Units.mul_left_inj _).1 ((hc y J hJ).symm.trans (hc' y J hJ))

end GlobalTheory.Ex.OneGen
end
end
