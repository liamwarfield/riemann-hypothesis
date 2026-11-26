module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormMapRowThreeLevelOfCharacterisation
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLineC1LogBound

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IsMumfordFamOfSubsingleton
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg

section Family

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {R : Type} [CommRing R] [IsDomain R]
  (y : Sp (FractionRing R) ⟶ F.X) {G₁ : Over (Sp R)} [GrpObj G₁] (α₁ : pullback G₁.hom (jK R) ⟶ F.univ.A.left)

def IsGenFibre : Prop := IsGrpPullback ((Over.pullback (jK R)).obj G₁) F.univ.A y α₁

def IsUnifAlong {R' : Type} [CommRing R'] [IsDomain R'] {I : Ideal R'} (ρ : R →+* R') {G' : Over (Sp R')} [GrpObj G']
    [IsCommMonObj G'] (π : G'.left ⟶ G₁.left) {D : DegData R' I} {A : PolAV (Sp (FractionRing R'))} (U : Unif I D A G') : Prop :=
  IsGrpPullback G' G₁ (spMap ρ) π ∧
    ∃ (κ : Sp (FractionRing R') ⟶ Sp (FractionRing R)) (πK : pullback G'.hom (jK R') ⟶ pullback G₁.hom (jK R))
      (α : A.A.left ⟶ F.univ.A.left) (α₂ : (G2 A.A).left ⟶ (G2 F.univ.A).left),
      κ ≫ jK R = jK R' ≫ spMap ρ ∧ πK ≫ pullback.fst G₁.hom (jK R) = pullback.fst G'.hom (jK R') ≫ π ∧
        IsGrpPullback A.A F.univ.A (κ ≫ y) α ∧ IsSquare α α₂ ∧ LBIso (abelian₂ A.A A.L) (F.univ.P.pull α₂) ∧
        U.gen.hom.left ≫ α = πK ≫ α₁

def IsMumfordFam [IsLocalRing R] (Q : Data R) : Prop :=
  IsCN R ∧ Q.IsPos (maximalIdeal R) ∧
  ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), IsCN R' → Function.Injective ρ → ρ.Finite →
    ∀ (D : DegData R' (maximalIdeal R')) (ε : D.toPre.X ≃+ Q.X), Refines Q ρ D.toPre ε →
      ∃ (G' : Over (Sp R')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ G₁.left) (A : PolAV (Sp (FractionRing R')))
        (U : Unif (maximalIdeal R') D A G'), IsUnifAlong F y α₁ ρ π U

variable {F y α₁}

theorem IsMumfordFam.isCN [IsLocalRing R] {Q : Data R} (h : IsMumfordFam F y α₁ Q) : IsCN R := h.1

theorem IsMumfordFam.isPos [IsLocalRing R] {Q : Data R} (h : IsMumfordFam F y α₁ Q) : Q.IsPos (maximalIdeal R) := h.2.1

theorem IsMumfordFam.unif [IsLocalRing R] {Q : Data R} (h : IsMumfordFam F y α₁ Q) :
    ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), IsCN R' → Function.Injective ρ → ρ.Finite →
    ∀ (D : DegData R' (maximalIdeal R')) (ε : D.toPre.X ≃+ Q.X), Refines Q ρ D.toPre ε →
      ∃ (G' : Over (Sp R')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ G₁.left) (A : PolAV (Sp (FractionRing R')))
        (U : Unif (maximalIdeal R') D A G'), IsUnifAlong F y α₁ ρ π U := h.2.2

end Family

section Charts

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S : Scheme.{0}} (s : S ⟶ Sp o) (j : F.X ⟶ S)

def PreChart [IsOpenImmersion j] (φ : InvFun ℤ) (BD : EffCartierData S) (d : ℕ) (x : S) : Prop :=
  ∃ (R : Type) (_ : CommRing R) (_ : IsRegularLocalRing R) (_ : IsDomain R) (b : o →+* R) (ξ : Sp R ⟶ S) (m : ℕ)
    (t : Fin m → R) (Q : Data R) (δ : Fin m → LinearMap.BilinForm ℤ Q.X) (a : Fin m → ℕ)
    (G₁ : Over (Sp R)) (_ : GrpObj G₁) (y : Sp (FractionRing R) ⟶ F.X) (α₁ : pullback G₁.hom (jK R) ⟶ F.univ.A.left),
    (IsAdicComplete (maximalIdeal R) R ∧ CharZero R ∧ ξ ≫ s = spMap b ∧ ξ (closedPoint R) = x ∧
      IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom ∧
      ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified) ∧
    (IsRelParam b t ∧ idlAlong (Scheme.IdealSheafData.vanishingIdeal j.opensRange.compl) ξ = Ideal.span {∏ i, t i} ∧
      ∀ p : Sp R, ξ p ∈ Set.range j ↔ ∏ i, t i ∉ p.asIdeal) ∧
    (IsSemiAbelian G₁ ∧ (∀ p : Sp R, p ∈ abLocus G₁ ↔ ∏ i, t i ∉ p.asIdeal) ∧ y ≫ j = jK R ≫ ξ ∧ IsGenFibre F y α₁) ∧
    (IsMumfordFam F y α₁ Q ∧ Module.finrank ℤ Q.X ≤ g ∧ IsCone id φ δ ∧ (∀ z, z ≠ 0 → ∃ i, 0 < δ i z z) ∧
      Q.IsMonomialTau t fun i => (n : ℤ) • δ i) ∧
    (∀ i, (a i : ℝ) = d * φ.evalZ ((n : ℤ) • δ i)) ∧ idlAlong BD.idealSheaf ξ = Ideal.span {∏ i, t i ^ a i}

end Charts

section Generic

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem exists_genericMap {ρ : R →+* R'} (hρ : Function.Injective ρ) :
    ∃ κ : Sp (FractionRing R') ⟶ Sp (FractionRing R), κ ≫ jK R = jK R' ≫ spMap ρ := by
  have h : Function.Injective ((algebraMap R' (FractionRing R')).comp ρ) := (IsFractionRing.injective R' _).comp hρ
  refine ⟨spMap (IsFractionRing.lift (K := FractionRing R) h), ?_⟩
  change spMap _ ≫ spMap (algebraMap R (FractionRing R)) = spMap (algebraMap R' (FractionRing R')) ≫ spMap ρ
  rw [← spMap_comp, ← spMap_comp]
  congr 1
  ext r
  simp


omit [IsDomain R] in
theorem ne_zero_of_isRelParam {o : Type} [CommRing o] [IsLocalRing R] {b : o →+* R} {m : ℕ} {t : Fin m → R}
    (h : IsRelParam b t) (i : Fin m) : t i ≠ 0 := fun h0 => by
  have h₁ := h.mem_of_mem_sq (Pi.single i 1) (by
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [Pi.single_eq_of_ne hk]) (by simp), h0, mul_zero]
    exact zero_mem _) i
  exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using h₁))

end Generic

section Good

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {F : SFam g n ζ} {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem lbIso_pull_comp {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {a : Y ⟶ X} (h : LBIso M (L.pull a)) (j : Z ⟶ Y)
    {a' : Z ⟶ X} (e : a' = j ≫ a) : LBIso (M.pull j) (L.pull a') :=
  LBIso.chartPull (Geo.Tor.chartPullPull M j j rfl) (Geo.Tor.chartPullSame L _ (fun _ => a) _ j fun _ => e) h

theorem isSquare_comp {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} {φ : G'.left ⟶ G.left}
    {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} {ψ : G''.left ⟶ G'.left} {ψ₂ : (G'' ⊗ G'').left ⟶ (G' ⊗ G').left}
    (h' : IsSquare ψ ψ₂) (h : IsSquare φ φ₂) : IsSquare (ψ ≫ φ) (ψ₂ ≫ φ₂) :=
  ⟨by rw [Category.assoc, h.1, ← Category.assoc, h'.1, Category.assoc],
    by rw [Category.assoc, h.2, ← Category.assoc, h'.2, Category.assoc]⟩

end Good

section Compare

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {F : SFam g n ζ} {S : Scheme.{0}} {s : S ⟶ Sp o} {j : F.X ⟶ S}
  {G : Over S} [GrpObj G] {e : F.univ.A.left ⟶ G.left} {R : Type} [CommRing R] [IsDomain R]
  {y : Sp (FractionRing R) ⟶ F.X} {G₁ : Over (Sp R)} [GrpObj G₁] {α₁ : pullback G₁.hom (jK R) ⟶ F.univ.A.left}
  {ξ : Sp R ⟶ S} {π₁ : G₁.left ⟶ G.left}

theorem IsUnifAlong.isUnifOf (h₁ : IsGrpPullback G₁ G ξ π₁) (hy : y ≫ j = jK R ≫ ξ)
    (hα : α₁ ≫ e = pullback.fst G₁.hom (jK R) ≫ π₁) {R' : Type} [CommRing R'] [IsDomain R'] {I : Ideal R'} {ρ : R →+* R'}
    {G' : Over (Sp R')} [GrpObj G'] [IsCommMonObj G'] {π : G'.left ⟶ G₁.left} {D : DegData R' I}
    {A : PolAV (Sp (FractionRing R'))} {U : Unif I D A G'} (h : IsUnifAlong F y α₁ ρ π U) :
    IsUnifOf F j e (spMap ρ ≫ ξ) (π ≫ π₁) U := by
  obtain ⟨hπ, κ, πK, α, α₂, hκ, hK, hA, hsq, hL, hU⟩ := h
  refine ⟨hπ.comp h₁, κ ≫ y, α, α₂, ?_, hA, hsq, hL, ?_⟩
  · rw [Category.assoc, hy, ← Category.assoc, hκ, Category.assoc]
  · rw [← Category.assoc, hU, Category.assoc, hα, ← Category.assoc, hK, Category.assoc]

theorem IsMumfordFam.isMumfordOf [IsLocalRing R] (h₁ : IsGrpPullback G₁ G ξ π₁) (hy : y ≫ j = jK R ≫ ξ)
    (hα : α₁ ≫ e = pullback.fst G₁.hom (jK R) ≫ π₁) {Q : Data R} (h : IsMumfordFam F y α₁ Q) : IsMumfordOf F j e ξ Q := by
  refine ⟨h.isCN, h.isPos, fun R' _ _ _ ρ hR hρ hf D ε hD => ?_⟩
  obtain ⟨G', _, _, π, A, U, hU⟩ := h.unif R' ρ hR hρ hf D ε hD
  exact ⟨G', inferInstance, inferInstance, π ≫ π₁, A, U, hU.isUnifOf h₁ hy hα⟩

theorem IsGenFibre.exists_isGrpPullback [IsNoetherianRing R] [IsIntegrallyClosed R] (hG : IsSemiAbelian G)
    (he : IsGrpPullback F.univ.A G j e) (hG₁ : IsSemiAbelian G₁) (hy : y ≫ j = jK R ≫ ξ) (h : IsGenFibre F y α₁) :
    ∃ π₁ : G₁.left ⟶ G.left, IsGrpPullback G₁ G ξ π₁ ∧ α₁ ≫ e = pullback.fst G₁.hom (jK R) ≫ π₁ := by
  have h₀ := isGrpPullback_pullback G ξ
  have h₂ := (isGrpPullback_pullback ((Over.pullback ξ).obj G) (jK R)).comp h₀
  obtain ⟨E, hE, hE'⟩ := grpPullback_iso ((IsGrpPullback.comp h he).congr hy rfl) h₂
  obtain ⟨E₁, ⟨hE₁, hE₂⟩, -⟩ := GlobalTheory.SemiAbExtDomain.existsUnique_iso_extension_generic (FractionRing R) G₁
    ((Over.pullback ξ).obj G) hG₁ (IsSemiAbelian.pullback ξ G hG) E
  refine ⟨E₁.hom.left ≫ pullback.fst G.hom ξ, ((isGrpPullback_of_iso E₁).comp h₀).congr (Category.id_comp _) rfl, ?_⟩
  have h₃ : ((Over.pullback (jK R)).map E₁.hom).left ≫ pullback.fst ((Over.pullback ξ).obj G).hom (jK R) =
      pullback.fst G₁.hom (jK R) ≫ E₁.hom.left := pullback.lift_fst _ _ _
  have h₄ : E.hom = (Over.pullback (jK R)).map E₁.hom := hE₂.symm
  refine hE'.symm.trans ?_
  rw [h₄]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.fst G.hom ξ) h₃).trans (Category.assoc _ _ _))

variable [IsOpenImmersion j] {φ : InvFun ℤ} {BD : EffCartierData S} {d : ℕ} {x : S}

theorem PreChart.hasPolChart (hG : IsSemiAbelian G) (he : IsGrpPullback F.univ.A G j e) (h : PreChart F s j φ BD d x) :
    HasPolChart F s j e φ BD d x := by
  obtain ⟨R, _, _, _, b, ξ, m, t, Q, δ, a, G₁, _, y, α₁, c₁, c₂, ⟨hG₁, -, hy, hα⟩, ⟨hM, c₃⟩, c₄⟩ := h
  have := (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R).2
  obtain ⟨π₁, h₁, h₂⟩ := hα.exists_isGrpPullback hG he hG₁ hy
  exact ⟨R, inferInstance, inferInstance, inferInstance, b, ξ, m, t, Q, δ, a, c₁, c₂, ⟨hM.isMumfordOf h₁ hy h₂, c₃⟩, c₄⟩

end Compare

end GlobalTheory.PolDeg
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

def DefOver {K : Type} [Field K] (k₀ : Subfield K) {Y : Scheme.{0}} (P : Sp K ⟶ Y) : Prop :=
  ∃ P₀ : Sp k₀ ⟶ Y, spMap k₀.subtype ≫ P₀ = P

variable {V : Type} [CommRing V] [IsDomain V]

abbrev Gens (Q : Data V) : Type := ∀ a b : Q.X, LB.Gen (LB.LinComb Q.M.L (lamPts (Q.c a) (Q.c b)) negε)

def TauIn (Q : Data V) (τ₀ : Gens Q) {N : ℕ} (s : Fin N → V) (ε : Fin N → LinearMap.BilinForm ℤ Q.X) : Prop :=
  ∀ a b, (τ₀ a b).IsGen ∧ ∃ k : (FractionRing V)ˣ,
    (k : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s i) ^ ε i a b ∧ ∀ z J, Good Q.M.L z J →
      val (Q.tau a b) (𝟙 _) z J = gm (𝟙 (TK V).left) z ⊤ (unitOn k) * val (τ₀ a b) (toUnit (TK V)).left z J

def FromBase (Q : Data V) (τ₀ : Gens Q) {W₀ : Type} [CommRing W₀] (ιb : W₀ →+* V) : Prop :=
  ∃ (B₀ : Over (Sp W₀)) (_ : GrpObj B₀) (_ : IsCommMonObj B₀) (M₀ : LB B₀.left) (c₀ : Q.X → (𝟙_ (Over (Sp W₀)) ⟶ B₀))
    (τ₁ : ∀ a b : Q.X, LB.Gen (LB.LinComb M₀ (lamPts (c₀ a) (c₀ b)) negε))
    (β : Q.B.left ⟶ B₀.left) (β₂ : (G2 Q.B).left ⟶ (G2 B₀).left)
    (w : LB.Iso (abelian₂ Q.B Q.M.L) ((abelian₂ B₀ M₀).pull β₂)),
    IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback Q.B B₀ (spMap ιb) β ∧ IsSquare β β₂ ∧ w.IsGen ∧
    (∀ a, (Q.c a).left ≫ β = spMap ιb ≫ (c₀ a).left) ∧ (∀ a b, (τ₁ a b).IsGen) ∧
    ∀ (T : Over (Sp V)) (a b : Q.X) z J J', Good M₀ z J → Good Q.M.L z J' →
      val (τ₀ a b) (toUnit T).left z J' =
        lamVal w (lift (toUnit T ≫ Q.c a) (toUnit T ≫ Q.c b)).left z J J' * val (τ₁ a b) (T.hom ≫ spMap ιb) z J

def UnifOver {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S : Scheme.{0}} (j : F.X ⟶ S) [IsLocalRing V]
    (ξ : Sp V ⟶ S) (Q : Data V) : Prop :=
  IsCN V ∧ ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : V →+* R'), IsCN R' → Function.Injective ρ →
    ρ.Finite → ∀ (D : DegData R' (maximalIdeal R')) (ε : D.toPre.X ≃+ Q.X), Refines Q ρ D.toPre ε →
      ∃ (G' : Over (Sp R')) (_ : GrpObj G') (_ : IsCommMonObj G') (A : PolAV (Sp (FractionRing R')))
        (_ : Unif (maximalIdeal R') D A G') (y' : Sp (FractionRing R') ⟶ F.X) (α : A.A.left ⟶ F.univ.A.left)
        (α₂ : (G2 A.A).left ⟶ (G2 F.univ.A).left),
        IsSemiAbelian G' ∧ y' ≫ j = jK R' ≫ spMap ρ ≫ ξ ∧ IsGrpPullback A.A F.univ.A y' α ∧
          IsSquare α α₂ ∧ LBIso (abelian₂ A.A A.L) (F.univ.P.pull α₂)

def SepAt (Q : Data V) (τ₀ : Gens Q) {m N : ℕ} (s : Fin m ⊕ Fin N → V) {K : Type} [Field K] (ev : V →+* K)
    (k₀ : Subfield K) : Prop :=
  (∀ i, ev (s (.inl i)) = 0) ∧
  (∀ (o' : Type) [CommRing o'] (ζ' : o') (g' n' : ℕ) (F' : SFam g' n' ζ') (lam : Sp V ⟶ F'.X) (β : Q.B.left ⟶ F'.univ.A.left)
      (β₂ : (G2 Q.B).left ⟶ (G2 F'.univ.A).left), 1 ≤ n' → DefOver k₀ (spMap ev ≫ lam ≫ F'.s) →
      IsGrpPullback Q.B F'.univ.A lam β → IsSquare β β₂ → LBIso (abelian₂ Q.B Q.M.L) (F'.univ.P.pull β₂) →
      ∀ a, DefOver k₀ (spMap ev ≫ (Q.c a).left ≫ β)) ∧
  ∀ (W₀ : Type) [CommRing W₀] (ιb : W₀ →+* V), FromBase Q τ₀ ιb → (∀ a, ev (ιb a) ∈ k₀) → ∀ i, ev (s i) ∈ k₀

def SepSt : Prop :=
  ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n))
    (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ →
    ∀ (d : ℕ) (J : Z.IdealSheafData) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S), 1 ≤ d →
      (∀ x ∈ J.support, x ∉ Set.range i) → ValOn F i φ J d → IsNormBl π J → j ≫ π = i →
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (ξ : Sp V ⟶ S), UnifOver F j ξ Q →
    ∀ (m N : ℕ) (s : Fin m ⊕ Fin N → V) (ε : Module.Basis (Fin m ⊕ Fin N) ℤ (balForms (id : ℤ → ℤ) Q.X)) (τ₀ : Gens Q),
      Module.finrank ℤ Q.X ≤ g → IsCone id φ (fun k => (ε (.inl k) : LinearMap.BilinForm ℤ Q.X)) →
      (∀ x, x ≠ 0 → ∃ k, 0 < (ε (.inl k) : LinearMap.BilinForm ℤ Q.X) x x) →
      (∀ k, s (.inl k) ∈ maximalIdeal V ∧ s (.inl k) ≠ 0) → (∀ k, IsUnit (s (.inr k))) →
      TauIn Q τ₀ (fun k => s (finSumFinEquiv.symm k))
        (fun k => (n : ℤ) • (ε (finSumFinEquiv.symm k) : LinearMap.BilinForm ℤ Q.X)) →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
      (∀ p, (spMap ev ≫ ξ) p = ξ (closedPoint V)) → DefOver k₀ (spMap ev ≫ ξ) → SepAt Q τ₀ s ev k₀

end GlobalTheory.Poinc.Sep
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.OrdGeOfForall
noncomputable section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.Poinc

def mono {s m : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) {X : Type} [AddCommGroup X] {V : Type} [CommRing V] (t : Fin m → V)
    (δ : Fin m → LinearMap.BilinForm ℤ X) (μ : Fin s → X) : V := ∏ i, t i ^ (qW W (δ i) μ).toNat

def lin {s l : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) {X : Type} [AddCommGroup X] (a : Fin l × Fin s → X)
    (β : LinearMap.BilinForm ℤ X) : ℤ := ∑ i, qW W β fun u => a (i, u)

theorem qW_nonneg {s : ℕ} {W : Matrix (Fin s) (Fin s) ℤ} (hW : PosW W) {X : Type} [AddCommGroup X]
    {β : LinearMap.BilinForm ℤ X} (hs : ∀ a b, β a b = β b a) (hβ : ∀ y, 0 ≤ β y y) (y : Fin s → X) : 0 ≤ qW W β y := by
  obtain ⟨c, hc0, hc⟩ := QWDom.qW_ge s W hW
  have h2 : (0 : ℝ) ≤ ((∑ u, β (y u) (y u) : ℤ) : ℝ) := by
    exact_mod_cast Finset.sum_nonneg fun u _ => hβ _
  exact_mod_cast (mul_nonneg hc0.le h2).trans (hc X β hs hβ y)

structure Dominant {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) (d N₁ : ℕ) {s l : ℕ} (W : Matrix (Fin s) (Fin s) ℤ)
    {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] {r : ℕ} (γ : Fin r → LinearMap.BilinForm ℤ X)
    (a : Fin l × Fin s → X) : Prop where
  span : Submodule.span ℤ (Set.range a) = ⊤
  le : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → d * φ.evalZ β ≤ (lin W a β : ℤ)
  min : ∀ e : X ≃ₗ[O] X, (∀ x, CongMod N₁ (e x) x) → ∀ j, lin W a (γ j) ≤ lin W (fun i => e (a i)) (γ j)
  strict : ∀ e : X ≃ₗ[O] X, (∀ x, CongMod N₁ (e x) x) → (∃ x, e x ≠ x) → ∃ j, lin W a (γ j) < lin W (fun i => e (a i)) (γ j)

structure VSys {O : Type} [CommRing O] (bar : O → O) (q : ℕ) {s : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) (N₁ : ℕ)
    (A : Type) [CommRing A] [IsLocalRing A] : Type 2 where
  posW : PosW W

  Y : Type 1

  V : Y → Type
  [ring : ∀ y, CommRing (V y)]
  [dom : ∀ y, IsDomain (V y)]
  [loc : ∀ y, IsLocalRing (V y)]
  cn : ∀ y, IsCN (V y)

  ev : ∀ y, A →+* V y
  ev_loc : ∀ y, IsLocalHom (ev y)

  X : Y → Type
  [add : ∀ y, AddCommGroup (X y)]
  [mod : ∀ y, Module O (X y)]
  [fin : ∀ y, Module.Finite O (X y)]
  [proj : ∀ y, Module.Projective O (X y)]
  [freeZ : ∀ y, Module.Free ℤ (X y)]
  [finZ : ∀ y, Module.Finite ℤ (X y)]
  rank_le : ∀ y, Module.finrank O (X y) ≤ q

  m : Y → ℕ

  t : ∀ y, Fin (m y) → V y
  t_mem : ∀ y i, t y i ∈ maximalIdeal (V y) ∧ t y i ≠ 0

  δ : ∀ y, Fin (m y) → LinearMap.BilinForm ℤ (X y)
  bal : ∀ y i, δ y i ∈ balForms bar (X y)
  nonneg : ∀ y i x, 0 ≤ δ y i x x
  pos : ∀ y x, x ≠ 0 → ∃ i, 0 < δ y i x x

  Q : Type

  u : ∀ y, (Fin s → X y) → Q → V y
  u_unit : ∀ y μ, ∃ c, IsUnit (u y μ c)
  lam : ∃ C : ℕ, ∀ y, m y = 1 → ∀ i x, x ≠ 0 → ∃ h ∈ maximalIdeal A, ev y h ∣ t y i ^ (C * (δ y i x x).toNat)
  four : ∀ (y₀ : Y) (N₀ : ℕ), ∃ N, N₀ ≤ N ∧ N₁ ∣ N ∧ ∃ k : ∀ y, X y₀ →ₗ[ℤ] X y, k y₀ = LinearMap.id ∧
    (∀ y, IsUnimodMod O N (k y)) ∧ ∀ (l : ℕ) (a : Fin l × Fin s → X y₀) (c : Fin l → Q) (e : ℕ), ∃ f : A, ∀ (y : Y) (j : ℕ),
      ∃ S : Finset (Fin l × Fin s → X y), (↑S : Set _) ⊆ orbit O N₁ N (k y) a ∧
        (∀ μ ∈ orbit O N₁ N (k y) a, μ ∉ S → (j : ℤ) ≤ ∑ i, lin W μ (δ y i)) ∧
        ev y f - ∑ μ ∈ S, ∏ i, u y (fun v => μ (i, v)) (c i) * mono W (t y) (δ y) (fun v => μ (i, v)) ∈
          maximalIdeal (V y) ^ j ⊔ (maximalIdeal A ^ e).map (ev y)

attribute [instance] VSys.ring VSys.dom VSys.loc VSys.add VSys.mod VSys.fin VSys.proj VSys.freeZ VSys.finZ

namespace VSys

variable {O : Type} [CommRing O] {bar : O → O} {q s : ℕ} {W : Matrix (Fin s) (Fin s) ℤ} {N₁ : ℕ} {A : Type} [CommRing A]
  [IsLocalRing A] (Φ : VSys bar q W N₁ A)

theorem qW_nonneg (y : Φ.Y) (i : Fin (Φ.m y)) (μ : Fin s → Φ.X y) : 0 ≤ qW W (Φ.δ y i) μ :=
  GlobalTheory.Poinc.qW_nonneg Φ.posW (Φ.bal y i).1 (Φ.nonneg y i) μ

def monoT (y : Φ.Y) {l : ℕ} (a : Fin l × Fin s → Φ.X y) : Φ.V y := ∏ i, mono W (Φ.t y) (Φ.δ y) fun v => a (i, v)

def coefT (y : Φ.Y) {l : ℕ} (a : Fin l × Fin s → Φ.X y) (c : Fin l → Φ.Q) : Φ.V y := ∏ i, Φ.u y (fun v => a (i, v)) (c i)

def OrdGe (φ : InvFun O) (d e : ℕ) (f : A) : Prop :=
  ∀ y, IsPrincipalIdealRing (Φ.V y) → Φ.m y = 1 → ∀ i : Fin (Φ.m y),
    Φ.ev y f ∈ Ideal.span {Φ.t y i ^ ⌈(d : ℝ) * φ.evalZ (Φ.δ y i)⌉₊} ⊔ ((maximalIdeal A).map (Φ.ev y)) ^ e


variable {Φ} in
theorem OrdGe.mem {φ : InvFun O} {d e : ℕ} {f : A} (h : Φ.OrdGe φ d e f) (y : Φ.Y) (hP : IsPrincipalIdealRing (Φ.V y))
    (hm : Φ.m y = 1) (i : Fin (Φ.m y)) (b : ℕ) (hb : (b : ℝ) = d * φ.evalZ (Φ.δ y i)) :
    Φ.ev y f ∈ Ideal.span {Φ.t y i ^ b} ⊔ ((maximalIdeal A).map (Φ.ev y)) ^ e := by
  have := h y hP hm i
  rwa [← hb, Nat.ceil_natCast] at this

theorem ordGe_of_forall {φ : InvFun O} {d e : ℕ} {f : A}
    (h : ∀ y, IsPrincipalIdealRing (Φ.V y) → Φ.m y = 1 → ∀ (i : Fin (Φ.m y)) (b : ℕ),
      (∀ n : ℕ, d * φ.evalZ (Φ.δ y i) ≤ n → b ≤ n) →
      Φ.ev y f ∈ Ideal.span {Φ.t y i ^ b} ⊔ ((maximalIdeal A).map (Φ.ev y)) ^ e) : Φ.OrdGe φ d e f :=
  fun y hP hm i => h y hP hm i _ fun _ hn => Nat.ceil_le.2 hn

def Leads (y : Φ.Y) {l : ℕ} (a : Fin l × Fin s → Φ.X y) (c : Fin l → Φ.Q) (e : ℕ) (f : A) : Prop :=
  Φ.ev y f - Φ.coefT y a c * Φ.monoT y a ∈
    Ideal.span {Φ.monoT y a} * Ideal.span (Set.range (Φ.t y)) ⊔ maximalIdeal (Φ.V y) ^ e

end VSys

end GlobalTheory.Poinc
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IdlAlongNeTopOfValOn
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj

namespace GlobalTheory.Poinc.Basic₂

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {F : SFam g n ζ}

theorem trait_nonneg (T : Trait F) (x : T.D.toPre.X) : 0 ≤ T.β x x := by
  simpa using T.mono.nonneg 0 x

end GlobalTheory.Poinc.Basic₂
end
end
