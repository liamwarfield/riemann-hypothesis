module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SmoothLift

structure Data where

  R : Type
  [ring : CommRing R]

  I : Ideal R

  κ : DividedPowers I
  nil : IsNilDP κ

  X : Scheme.{0}

  X₀ : Scheme.{0}

  s : X ⟶ Sp R

  t : X₀ ⟶ Sp R

  i : X₀ ⟶ X
  smooth : Smooth s
  sep : IsSeparated s
  qc : QuasiCompact s
  red : ∃ s₀ : X₀ ⟶ Sp (R ⧸ I), IsPullback i s₀ s (spMap (Ideal.Quotient.mk I)) ∧ t = s₀ ≫ spMap (Ideal.Quotient.mk I)

attribute [instance] Data.ring

def Data.ofQuot {R : Type} [CommRing R] {I : Ideal R} (κ : DividedPowers I) (hκ : IsNilDP κ)
    {R₀ : Type} [CommRing R₀] (π : R →+* R₀) (hπ : Function.Surjective π) (hI : RingHom.ker π = I)
    {X X₀ : Scheme.{0}} (s : X ⟶ Sp R) (s₀ : X₀ ⟶ Sp R₀) (i : X₀ ⟶ X) (hs : Smooth s) (hs' : IsSeparated s)
    (hs'' : QuasiCompact s) (h : IsPullback i s₀ s (spMap π)) (t : X₀ ⟶ Sp R) (ht : t = s₀ ≫ spMap π) : Data where
  R := R
  I := I
  κ := κ
  nil := hκ
  X := X
  X₀ := X₀
  s := s
  t := t
  i := i
  smooth := hs
  sep := hs'
  qc := hs''
  red := by
    subst hI
    let e' := RingHom.quotientKerEquivOfSurjective hπ
    let e : R ⧸ RingHom.ker π →+* R₀ := e'
    have he : spMap e ≫ spMap (Ideal.Quotient.mk (RingHom.ker π)) = spMap π := by
      rw [← Cris.spMap_comp]; rfl
    haveI : IsIso (spMap e) := (inferInstance : IsIso (Spec.map e'.toCommRingCatIso.hom))
    refine ⟨s₀ ≫ spMap e, ?_, by rw [ht, Category.assoc, he]⟩
    exact h.of_iso (Iso.refl _) (Iso.refl _) (asIso (spMap e)) (Iso.refl _) (by simp) (by simp) (by simp)
      (by simp [he])

def Data.self {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (hs : Smooth s) (hs' : IsSeparated s)
    (hs'' : QuasiCompact s) : Data :=
  Data.ofQuot (dp0 R) (isDPNilpotent_bot R) (RingHom.id R) Function.surjective_id
    ((RingHom.injective_iff_ker_eq_bot _).1 fun _ _ h ↦ h) s s (𝟙 X) hs hs' hs''
    (by rw [Cris.spMap_id]; exact IsPullback.id_horiz s) s (by rw [Cris.spMap_id, Category.comp_id])

def affDiag (X : Scheme.{0}) : AffOp X ⥤ (Pair (𝟙 X))ᵒᵖ :=
  (Monotone.functor (f := fun U : X.affineOpens ↦ (⟨(U, U), le_rfl⟩ : Pair (𝟙 X))) fun _ _ h ↦
    Subtype.coe_le_coe.1 (Prod.le_def.2 ⟨h, h⟩)).op

def affDiagCoef {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) :
    CoefMap (RingHom.id R) (OPair (𝟙 X) s) (OAff s) where
  G := affDiag X
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

theorem pairRes2_id_injective {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) :
    Function.Injective (pullHyp2 (pairRes (𝟙 X) s)) := by
  refine Function.LeftInverse.injective (g := pullHyp2 (affDiagCoef s)) fun c ↦ ?_
  exact (pullHyp2_comp _ _ c).symm.trans (pullHyp2_id c)

end GlobalTheory.SmoothLift

namespace GlobalTheory.Published

open GlobalTheory.SmoothLift

def CrystallineSmoothLift : Prop :=
  ∃ (e₁ : ∀ D : Data, CatCoh.H1 (O D.κ D.t) ≃ₗ[D.R] HH1 D.s) (e₂ : ∀ D : Data, CatCoh.H2 (O D.κ D.t) ≃ₗ[D.R] HH2 D.s),
    (∀ (D : Data) (a b : CatCoh.H1 (O D.κ D.t)), e₂ D (cup _ a b) = cupHH D.s (e₁ D a) (e₁ D b)) ∧
    (∀ (D : Data) (m : IsMor (dp0 D.R) D.s D.κ D.t (RingHom.id D.R) D.i) (c : FirstDeRham D.s), e₁ D (m.pull1 c) = cmp1 D.s c) ∧
    ∀ (D D' : Data) (σ : D.R →+* D'.R) (φ : D'.X ⟶ D.X) (φ₀ : D'.X₀ ⟶ D.X₀) (h : φ ≫ D.s = D'.s ≫ spMap σ)
      (m : IsMor D.κ D.t D'.κ D'.t σ φ₀), φ₀ ≫ D.i = D'.i ≫ φ →
      (∀ c, IsPull1 h (e₁ D c) (e₁ D' (m.pull1 c))) ∧ ∀ c, IsPull2 h (e₂ D c) (e₂ D' (m.pull2 c))

theorem CrystallineSmoothLift.bijective_cechDeRhamComparison_degreeOne (H : CrystallineSmoothLift) {R : Type} [CommRing R] {X : Scheme.{0}}
    (s : X ⟶ Sp R) (hs : Smooth s) (hs' : IsSeparated s) (hs'' : QuasiCompact s) : Function.Bijective (cmp1 s) := by
  obtain ⟨e₁, -, -, h, -⟩ := H
  have k : ∀ c, e₁ (Data.self s hs hs' hs'') c = cmp1 s c := fun c ↦
    (congrArg _ ((IsMor.id (dp0 R) s).pullCohomologyOne_id c)).symm.trans (h (Data.self s hs hs' hs'') (IsMor.id _ s) c)
  exact (funext k : _ = ⇑(cmp1 s)) ▸ (e₁ (Data.self s hs hs' hs'')).bijective

theorem CrystallineSmoothLift.toCrystallineDeRham (H : CrystallineSmoothLift) : CrystallineDeRham := by
  intro R _ I κ hκ R₀ _ π hπ hI X X₀ s s₀ i hs hs' hs'' hp m
  have b := H.bijective_cechDeRhamComparison_degreeOne s hs hs' hs''
  obtain ⟨e₁, e₂, -, h, n⟩ := H
  let D := Data.ofQuot κ hκ π hπ hI s s₀ i hs hs' hs'' hp _ rfl
  let D₀ := Data.self s hs hs' hs''
  have w : 𝟙 X ≫ s = s ≫ spMap (RingHom.id R) := by rw [Cris.spMap_id]; simp
  constructor
  · have : ⇑(e₁ D) ∘ ⇑m.pull1 = ⇑(cmp1 s) := funext (h D m)
    exact (Function.Bijective.of_comp_iff' (e₁ D).bijective _).1 (this ▸ b)
  · have k := (n D₀ D (RingHom.id R) (𝟙 X) i w m rfl).2
    have : ⇑(e₂ D) ∘ ⇑m.pull2 = ⇑(e₂ D₀) := funext fun c ↦
      pairRes2_id_injective s ((k c).symm.trans (isPull2_id w _))
    exact (Function.Bijective.of_comp_iff' (e₂ D).bijective _).1 (this ▸ (e₂ D₀).bijective)

end GlobalTheory.Published
end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}

def IsFineModuli {B : Type} [CommRing B] {M : Scheme.{0}} (s : M ⟶ Sp B) {N : ℕ} {U : Obj F 𝔠 M}
    (α : U.Level N) : Prop :=
  ∀ (S : Scheme.{0}) (t : S ⟶ Sp B) (X : Obj F 𝔠 S) (β : X.Level N),
    ∃! b : S ⟶ M, b ≫ s = t ∧ Obj.IsLevelPull β α b

def IsRelCI {B : Type} [CommRing B] {M : Scheme.{0}} (s : M ⟶ Sp B) (n : ℕ) : Prop :=
  (∀ (K : Type) [Field K] (t : Sp K ⟶ Sp B), topologicalKrullDim ↥(pullback s t) = n) ∧
    ∀ x : M, ∃ (V : M.Opens) (_ : IsAffineOpen V) (_ : x ∈ V) (c : ℕ) (g : Fin c → MvPolynomial (Fin (c + n)) B)
      (e : Γ(M, V) ≃+* MvPolynomial (Fin (c + n)) B ⧸ Ideal.span (Set.range g)),
      ∀ b : B, e (constFn s V b) = Ideal.Quotient.mk _ (MvPolynomial.C b)

def Obj.IsLinearKS {R : Type} [CommRing R] (X : Obj F 𝔠 (Sp R)) (κ : Fil X.A →ₗ[R] X.Lie) : Prop :=
  ∀ (a : 𝓞 F) (x y : Fil X.A), (y : HdR X.A) = act (dp0 R) (𝟙 _) X.rm a x → κ y = a • κ x

def Obj.HasKS {R : Type} [CommRing R] {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp (DualNumber R))}
    {i : X.A.left ⟶ X'.A.left} (h : X.IsPullBy X' (DeRham.epsRed R) i) (κ : Fil X.A →ₗ[R] X.Lie) : Prop :=
  ∀ x : Fil X.A, IsKSValue h.grp (x : HdR X.A) (κ x).hom

end GlobalTheory.RealMult

namespace GlobalTheory.Published

def DelignePappasModel : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (N : ℕ), 3 ≤ N →
    ∃ (M : Scheme.{0}) (s : M ⟶ Sp (Localization.Away (N : ℤ))) (U : Obj F 𝔠 M) (α : U.Level N),
      IsFineModuli s α ∧ IsSeparated s ∧ QuasiCompact s ∧ LocallyOfFinitePresentation s ∧
      Flat s ∧ IsRelCI s (Module.finrank ℚ F) ∧
      (∃ V : M.Opens, (V : Set M) = U.rapLocus ∧ SmoothOfRelativeDimension (Module.finrank ℚ F) (V.ι ≫ s) ∧
        M.basicOpen ((discr F : ℤ) : Γ(M, ⊤)) ≤ V ∧
        ∀ (K : Type) [Field K] (t : Sp K ⟶ Sp (Localization.Away (N : ℤ))) (y : ↥(pullback s t)),
          pullback.fst s t y ∉ V → 2 ≤ ringKrullDim ((pullback s t).presheaf.stalk y)) ∧
      (∀ (K : Type) [Field K] (t : Sp K ⟶ Sp (Localization.Away (N : ℤ))), Geo.Tor.IsNormalScheme (pullback s t)) ∧
      ∀ (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Algebra (Localization.Away (N : ℤ)) B]
        [IsCyclotomicExtension {N} (Localization.Away (N : ℤ)) B]
        (x : ↥(pullback s (spMap (algebraMap (Localization.Away (N : ℤ)) B))))
        (K : Type) [Field K] (t : Sp K ⟶ Sp B),
        IsIrreducible (pullback.fst (pullback.snd s (spMap (algebraMap (Localization.Away (N : ℤ)) B))) t ⁻¹'
          connectedComponent x)

def HilbertQExpansion : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F →
    ∀ (e : Fin (Module.finrank ℚ F) ≃ (F →+* ℝ)) (𝔞 𝔟 : FracId F) (k : ℕ) (R₀ : Subring ℂ)
      (g : ((F →+* ℝ) → ℂ) → ℂ) (a : (𝔞 * 𝔟).elt → ℂ),
      IsHolForm 𝔞 𝔟 k g → HasFourier 𝔞 𝔟 g a → (∀ ξ, a ξ ∈ R₀) →
      ∃! r : Rule (rapObj (𝔞 * 𝔟⁻¹)) R₀ k, r.HasValues e 𝔞 𝔟 g

def GoetzkyKoecher : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F →
    ∀ (𝔞 𝔟 : FracId F) (k : ℕ) (g : ((F →+* ℝ) → ℂ) → ℂ), IsHolForm 𝔞 𝔟 k g →
      (∃! a, HasFourier 𝔞 𝔟 g a) ∧
      ∀ a, HasFourier 𝔞 𝔟 g a → ∀ ξ, a ξ ≠ 0 → ξ = 0 ∨ IsTotPos (ξ : F)

def HilbertKodairaSpencer : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R : Type) [CommRing R]
    (X : Obj F 𝔠 (Sp R)), X.IsRapoport →
    (∀ (X' : Obj F 𝔠 (Sp (DualNumber R))) (i : X.A.left ⟶ X'.A.left) (h : X.IsPullBy X' (DeRham.epsRed R) i),
      ∃! κ, X.IsLinearKS κ ∧ Obj.HasKS h κ) ∧
    (∀ κ, X.IsLinearKS κ → ∃ (X' : Obj F 𝔠 (Sp (DualNumber R))) (i : X.A.left ⟶ X'.A.left)
      (h : X.IsPullBy X' (DeRham.epsRed R) i), Obj.HasKS h κ) ∧
    ∀ (X' X'' : Obj F 𝔠 (Sp (DualNumber R))) (i' : X.A.left ⟶ X'.A.left) (i'' : X.A.left ⟶ X''.A.left)
      (h' : X.IsPullBy X' (DeRham.epsRed R) i') (h'' : X.IsPullBy X'' (DeRham.epsRed R) i'') κ, Obj.HasKS h' κ → Obj.HasKS h'' κ →
      ∃ ψ : X'.A.left ⟶ X''.A.left, X'.IsPullBy X'' (𝟙 _) ψ ∧ i' ≫ ψ = i''

def RealMultDeRhamRank : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R : Type) [CommRing R] [IsLocalRing R]
    (X : Obj F 𝔠 (Sp R)),
    letI := tensorModule (dp0 R) (𝟙 _) X.rm
    Nonempty (Module.Basis (Fin 2) (R ⊗[ℤ] 𝓞 F) (HdR X.A))

def HilbertBlumenthal : Prop :=
  DelignePappasModel ∧ HilbertQExpansion ∧ GoetzkyKoecher ∧ HilbertKodairaSpencer ∧ RealMultDeRhamRank

end GlobalTheory.Published
end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsUniquePairsToTower
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent unitOn)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta)
open ReciprocityTheory.ChartRestriction.G.Out (WeilIs)
open GlobalTheory.Cris (dp0)
open GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace PDivGroup

open PDiv

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] (G : PDivGroup p R)

def IsConnecting (x : G.VecExt) (b : G.A 1) : Prop :=
  ∃ (c : G.cocycles) (B : G.funs), Submodule.Quotient.mk c = x ∧
    G.cob B = cocyclesMap ((p : ℤ_[p]) • 𝟙 G) c ∧ Coalgebra.counit (R := R) b = 0 ∧ B.1 1 = b

variable {G}

end PDivGroup

namespace EpsWeil

variable {R : Type} [CommRing R] (D : Type) [CommRing D] [Algebra R D]


variable {D} in
def epsUnit (b : D) : (DualNumber D)ˣ where
  val := 1 + TrivSqZeroExt.inr b
  inv := 1 - TrivSqZeroExt.inr b
  val_inv := by ext <;> simp
  inv_val := by ext <;> simp


variable (R) in
def epsMap : DualNumber R →ₐ[R] DualNumber D :=
  DualNumber.lift ⟨(Algebra.ofId R _, DualNumber.eps), DualNumber.eps_mul_eps, fun _ ↦ Commute.all _ _⟩

variable {D} {A B : Over (Sp R)} [GrpObj A] [GrpObj B]

def PairsTo (P : LB (A ⊗ B).left) (n : ℕ) (x : PDiv.SpAlg R D ⟶ A) (v : epsR R ⟶ B) (b : D) : Prop :=
  WeilIs (A ⊗ B) P (n : ℤ) (T := PDiv.SpAlg R (DualNumber D))
    (lift (spOver (TrivSqZeroExt.inlAlgHom R D D) ≫ x) 1) (lift 1 (spOver (epsMap R D) ≫ v))
    (unitOn (epsUnit b))

theorem unitOn_bijective : Function.Bijective (unitOn (R := D)) :=
  (Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of D)).symm.commRingCatIsoToRingEquiv.toMulEquiv).bijective

theorem map_unitOn {D' : Type} [CommRing D'] (f : D →+* D') (u : Dˣ) :
    Units.map (spMap f).appTop.hom.toMonoidHom (unitOn u) = unitOn (Units.map f.toMonoidHom u) :=
  Units.ext (congrArg (fun q ↦ q.hom u.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm

end EpsWeil

namespace Published

namespace BarsottiTateDieudonne

def WittModule : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p],
    ∃ (M : PDivGroup p k → ModuleCat.{0} (WittVector p k))
      (map : ∀ G H : PDivGroup p k, (G ⟶ H) →+ (M H →ₗ[WittVector p k] M G))
      (red : ∀ G : PDivGroup p k,
        M G →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] G.RigExt),
      (∀ G : PDivGroup p k, Module.Free (WittVector p k) (M G) ∧ Module.Finite (WittVector p k) (M G) ∧
        Module.finrank (WittVector p k) (M G) = G.height ∧ Function.Surjective (red G) ∧
        (∀ m, red G m = 0 ↔ ∃ n, m = p • n) ∧ map G G (𝟙 G) = LinearMap.id) ∧
      (∀ (G H K : PDivGroup p k) (f : G ⟶ H) (g : H ⟶ K),
        map G K (f ≫ g) = map G H f ∘ₗ map H K g) ∧
      ∀ (G H : PDivGroup p k) (f : G ⟶ H) (m : M H),
        red G (map G H f m) = PDivGroup.rigExtMap f (red H m)

def WeilCompatible {p : ℕ} [Fact p.Prime] (e : DeRhamVectorExtension.Family p) (s : ℤˣ) : Prop :=
  ∀ ⦃R : Type⦄ [CommRing R] (hR : (p : R) = 0) ⦃A B : Over (Sp R)⦄ [GrpObj A] [GrpObj B] ⦃g : ℕ⦄
    (hA : IsAbelianScheme A), IsAbelianScheme B → SmoothOfRelativeDimension g A.hom →
    SmoothOfRelativeDimension g B.hom → ∀ ⦃P : LB (A ⊗ B).left⦄, AbDual.IsDual A B P →
    ∀ ⦃φ : HdR A →ₗ[R] HdR B →ₗ[R] R⦄, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ →
    ∀ ⦃G : PDivGroup p R⦄ (t : G.TorsionTower A) ⦃h' : HdR B⦄ ⦃v : epsR R ⟶ B⦄, IsLieImage h' v →
    ∀ ⦃b : G.A 1⦄, EpsWeil.PairsTo P p (t.y 1) v b →
    ∀ ⦃c : primDR A⦄, (∀ h ∈ Fil A, φ h h' = h c) →
      G.IsConnecting (G.rigToExt (e (hR ▸ IsNilpotent.zero) hA t c)) (s • b)

def HodgeQuotient : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∃ (e : DeRhamVectorExtension.Family p) (s : ℤˣ),
    e.Natural ∧ e.Filtered ∧ e.Tangent ∧ WeilCompatible e s

end BarsottiTateDieudonne

def BarsottiTateDieudonne : Prop :=
  BarsottiTateDieudonne.WittModule ∧ BarsottiTateDieudonne.HodgeQuotient

namespace BarsottiTateDieudonne

end BarsottiTateDieudonne

end Published

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsPerfectOfIsDual
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.CechPic

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published.PoincareDeRhamDuality.Test

theorem isPerfect_of_isDual (D : DualAbelianScheme) {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]
    (hA : IsAbelianScheme A) {P : LB (A ⊗ B).left} (h : IsDual A B P) : IsPerfect A B P := by
  obtain ⟨B', _, P', -, -, h₁, h₂⟩ := D S A hA
  obtain ⟨u, hu, -⟩ := h.univ B' P' h₁.isLB h₁.additive
  refine ⟨h.isLB, (triv_ev_iff h.isLB _ _).2 (h.additive.evc_one h.isLB _), h.zero, fun T x hx ↦ ?_,
    fun _ ↦ h.eq_one⟩
  apply (h₁.isPerfect h₂).ker_left T x
  apply (triv_ev_iff h₁.isLB _ _).2
  have e := congrArg (CechPic.pull (lift (fst T B') (snd T B' ≫ u)).left) ((triv_ev_iff h.isLB _ _).1 hx)
  rw [pull_evc, map_zero, lift_fst_assoc, lift_snd] at e
  have k := (cls_eq_iff h₁.isLB (pull_isLB h.isLB _)).2 hu
  rw [evc, k, cls_ev h.isLB, pull_evc, lift_fst, lift_snd_assoc, e]

variable (R : Type) [CommRing R]

end GlobalTheory.Published.PoincareDeRhamDuality.Test
end
end
