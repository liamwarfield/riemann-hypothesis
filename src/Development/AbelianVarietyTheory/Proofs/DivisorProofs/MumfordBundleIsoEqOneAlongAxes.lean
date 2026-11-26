module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrFactorPointPadicAlgClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeClsPullHom
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerDifferentialsFreeCoordinateFormsAbelian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeformedLatticeSumDerivativesEqEisensteinJets
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPointPairsLowerBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndOnId
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalChartQuotientByIdealWithPrimePow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyAgreeRealOfReadGalois
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorialMulRankLeDegreeOfIndepSmallSections

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoEqOneAlongAxes
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoCartesianSquareTrivialSecondAxis
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoCartesianSquareTrivialSecondAxis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
open GlobalTheory.LamRigid GlobalTheory.LamBiext GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumRigidZero

theorem lamVal_one_right_base : ∀ {S S' : Scheme.{0}} (B : Over S) (B' : Over S') [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] (M : LB B.left) (M' : LB B'.left), M.IsLB → M'.IsLB → IsAbelianScheme B' → ∀ (f : S' ⟶ S) (β : B'.left ⟶ B.left) (β₂ : (G2 B').left ⟶ (G2 B).left) (w : LB.Iso (abelian₂ B' M') ((abelian₂ B M).pull β₂)), IsGrpPullback B' B f β → IsSquare β β₂ → w.IsGen → (∀ (T : Over S') (z : T.left) (J : (T.left ⟶ B.left) → M.ι) (J' : (T.left ⟶ B'.left) → M'.ι), Good M z J → Good M' z J' → lamVal w (lift (1 : T ⟶ B') (1 : T ⟶ B')).left z J J' = 1) → ∀ (T : Over S') (y : T ⟶ B') (z : T.left) (J : (T.left ⟶ B.left) → M.ι) (J' : (T.left ⟶ B'.left) → M'.ι), Good M z J → Good M' z J' → lamVal w (lift y (1 : T ⟶ B')).left z J J' = 1 := by
  intro S S' B B' _ _ _ _ M M' hM hM' hB f β β₂ w hβ hsq hw hn T y z J J' hJ hJ'
  have hG := GlobalTheory.globalFns_holds
  have hL : (abelian₂ B M).IsLB := DVR.linComb_isLB _ hM _ _
  have hL' : (abelian₂ B' M').IsLB := DVR.linComb_isLB _ hM' _ _
  have hw₀ : β ≫ B.hom = B'.hom ≫ f := hβ.1.w
  have pt_mul : ∀ {T₀ : Over S'} (a b : T₀ ⟶ B'), toBase hw₀ (a * b) = toBase hw₀ a * toBase hw₀ b :=
    fun a b => Over.OverMorphism.ext (hβ.2 _ a b _ _ rfl rfl).symm
  have pt_one : ∀ T₀ : Over S', toBase hw₀ (1 : T₀ ⟶ B') = 1 := fun T₀ =>
    mul_eq_left.1 ((pt_mul 1 1).symm.trans (congrArg (toBase hw₀) (_root_.mul_one 1)))
  have β₂_lift : ∀ {T₀ : Over S'} (a b : T₀ ⟶ B'),
      (lift a b).left ≫ β₂ = (lift (toBase hw₀ a) (toBase hw₀ b)).left := fun a b => square_over_hom_ext
    (by rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]; rfl)
    (by rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd]; rfl)
  have Hlam : ∀ {T₀ : Over S'} (a b : T₀ ⟶ B') {U : Type} [CommGroup U] (h : (T₀.left ⟶ B.left) → U),
      ∏ i, h (((lift a b).left ≫ β₂) ≫ lamφ B i) ^ lamε i =
        h (toBase hw₀ a * toBase hw₀ b).left * (h (toBase hw₀ a).left)⁻¹ * (h (toBase hw₀ b).left)⁻¹ *
          h (1 : Over.mk (T₀.hom ≫ f) ⟶ B).left := fun a b U _ h => by
    rw [β₂_lift]; exact prod_lam (toBase hw₀ a) (toBase hw₀ b) h
  let φ1 : Fin 1 → (B'.left ⟶ (G2 B').left) := fun _ => (lift (𝟙 B') (1 : B' ⟶ B')).left
  let ε1 : Fin 1 → ℤ := fun _ => 1
  have fe' : FormEq (K := PEmpty) PEmpty.elim PEmpty.elim (flatφ (lamφ B') φ1) (flatε lamε ε1) := fun U _ h => by
    rw [prod_flat, Fin.prod_univ_one, Fintype.prod_empty]
    show 1 = (∏ i, h ((lift (𝟙 B') (1 : B' ⟶ B')).left ≫ lamφ B' i) ^ lamε i) ^ (1 : ℤ)
    rw [prod_lam, _root_.mul_one (𝟙 B')]
    apply Additive.ofMul.injective
    simp only [zpow_one, ofMul_mul, ofMul_inv, ofMul_one]
    abel
  have fe : FormEq (K := PEmpty) PEmpty.elim PEmpty.elim (flatφ (lamφ B) fun k => φ1 k ≫ β₂) (flatε lamε ε1) :=
    fun U _ h => by
      rw [prod_flat, Fin.prod_univ_one, Fintype.prod_empty]
      show 1 = (∏ i, h (((lift (𝟙 B') (1 : B' ⟶ B')).left ≫ β₂) ≫ lamφ B i) ^ lamε i) ^ (1 : ℤ)
      rw [Hlam, pt_one, _root_.mul_one (toBase hw₀ (𝟙 B'))]
      apply Additive.ofMul.injective
      simp only [zpow_one, ofMul_mul, ofMul_inv, ofMul_one]
      abel
  obtain ⟨g', hg', hv'⟩ := exists_gen hM' fe' (LB.oneGen M') (oneGen_isGen _)
  obtain ⟨g, hg, hv⟩ := exists_gen hM fe (LB.oneGen M) (oneGen_isGen _)
  have Fa : ∀ {Z : Scheme.{0}} (r : Z ⟶ B'.left) (z₀ : Z) J₀, Good M' z₀ J₀ →
      val (L := abelian₂ B' M') (nest M' (lamφ B') lamε φ1 ε1 g') r z₀ (ind B' J₀) = 1 := fun r z₀ J₀ hJ₀ => by
    refine (val_nest hg' r (good_ind hJ₀) hJ₀).trans ?_
    simp only [adj_ind hM' hJ₀, one_zpow, Finset.prod_const_one, _root_.one_mul]
    exact (hv' _ r z₀ J₀ hJ₀).trans (val_one r)
  have Ft : ∀ {Z : Scheme.{0}} (r : Z ⟶ B'.left) (z₀ : Z) J₀, Good M z₀ J₀ →
      val (L := abelian₂ B M) (nest M (lamφ B) lamε (fun k => φ1 k ≫ β₂) ε1 g) r z₀ (ind B J₀) = 1 :=
    fun r z₀ J₀ hJ₀ => by
      refine (val_nest hg r (good_ind hJ₀) hJ₀).trans ?_
      simp only [adj_ind hM hJ₀, one_zpow, Finset.prod_const_one, _root_.one_mul]
      exact (hv _ r z₀ J₀ hJ₀).trans (val_one r)
  have Fp : ∀ {T₀ : Over S'} (c : T₀ ⟶ B') (z₀ : T₀.left) (J₀ : (T₀.left ⟶ B.left) → M.ι)
      (J₀' : (T₀.left ⟶ B'.left) → M'.ι),
      pw w φ1 ε1 c.left z₀ (fun k => ind B J₀ (c.left ≫ φ1 k ≫ β₂)) (fun k => ind B' J₀' (c.left ≫ φ1 k)) =
        lamVal w (lift c (1 : T₀ ⟶ B')).left z₀ J₀ J₀' := by
    intro T₀ c z₀ J₀ J₀'
    rw [pw_eq, Fin.prod_univ_one]
    show lamVal w (c ≫ lift (𝟙 B') (1 : B' ⟶ B')).left z₀ J₀ J₀' ^ (1 : ℤ) = _
    rw [comp_lift, comp_one_pt, Category.comp_id, zpow_one]
  have he : (1 : 𝟙_ (Over S') ⟶ B').left ≫ B'.hom = 𝟙 _ := Over.w (1 : 𝟙_ (Over S') ⟶ B')
  have E := rigid_pw w hw hL hL' φ1 ε1 (nest_isGen hg') (nest_isGen hg) B'.hom _ he (hG _ _ hB).2
    (fun y₀ => by
      obtain ⟨J₁, hJ₁⟩ := GlobalTheory.UU.exists_good_pt hM y₀
      obtain ⟨J₁', hJ₁'⟩ := GlobalTheory.UU.exists_good_pt hM' y₀
      refine ⟨ind B J₁, ind B' J₁', good_ind hJ₁, good_ind hJ₁', ?_⟩
      rw [Ft _ y₀ J₁ hJ₁, Fp (1 : 𝟙_ (Over S') ⟶ B'), Fa _ y₀ J₁' hJ₁', hn (𝟙_ (Over S')) y₀ J₁ J₁' hJ₁ hJ₁',
        _root_.mul_one])
    T.left y.left z (ind B J) (ind B' J') (good_ind hJ) (good_ind hJ')
  rw [Ft _ z J hJ, Fp y, Fa _ z J' hJ', _root_.mul_one] at E
  exact E.symm

end GlobalTheory.MumRigidZero
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoCartesianSquareTrivialSecondAxisStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordBundleIso_cartesianSquare_trivial_second_axis : ∀ {S S' : Scheme.{0}} (B : Over S) (B' : Over S') [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] (M : LB B.left) (M' : LB B'.left), M.IsLB → M'.IsLB → IsAbelianScheme B' → ∀ (f : S' ⟶ S) (β : B'.left ⟶ B.left) (β₂ : (G2 B').left ⟶ (G2 B).left) (w : LB.Iso (abelian₂ B' M') ((abelian₂ B M).pull β₂)), IsGrpPullback B' B f β → IsSquare β β₂ → w.IsGen → (∀ (T : Over S') (z : T.left) (J : (T.left ⟶ B.left) → M.ι) (J' : (T.left ⟶ B'.left) → M'.ι), Good M z J → Good M' z J' → lamVal w (lift (1 : T ⟶ B') (1 : T ⟶ B')).left z J J' = 1) → ∀ (T : Over S') (y : T ⟶ B') (z : T.left) (J : (T.left ⟶ B.left) → M.ι) (J' : (T.left ⟶ B'.left) → M'.ι), Good M z J → Good M' z J' → lamVal w (lift y (1 : T ⟶ B')).left z J J' = 1 := by
  first | exact @GlobalTheory.MumRigidZero.lamVal_one_right_base | exact GlobalTheory.MumRigidZero.lamVal_one_right_base | (intros; apply GlobalTheory.MumRigidZero.lamVal_one_right_base <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoCartesianSquareTrivialFirstAxis
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoCartesianSquareTrivialFirstAxis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

open GlobalTheory.LamRigid GlobalTheory.LamBiext GlobalTheory.MumRigidZero

noncomputable section

namespace GlobalTheory.MumRigidZeroPull

theorem lamVal_one_left_pull : ∀ {S S' : Scheme.{0}} (B : Over S) (B' : Over S') [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] (M : LB B.left) (M' : LB B'.left), M.IsLB → M'.IsLB → IsAbelianScheme B' → ∀ (f : S' ⟶ S) (β : B'.left ⟶ B.left) (β₂ : (G2 B').left ⟶ (G2 B).left) (w : LB.Iso (abelian₂ B' M') ((abelian₂ B M).pull β₂)), IsGrpPullback B' B f β → IsSquare β β₂ → w.IsGen → (∀ (T : Over S') (z : T.left) (J : (T.left ⟶ B.left) → M.ι) (J' : (T.left ⟶ B'.left) → M'.ι), Good M z J → Good M' z J' → lamVal w (lift (1 : T ⟶ B') (1 : T ⟶ B')).left z J J' = 1) → ∀ (T : Over S') (y : T ⟶ B') (z : T.left) (J : (T.left ⟶ B.left) → M.ι) (J' : (T.left ⟶ B'.left) → M'.ι), Good M z J → Good M' z J' → lamVal w (lift (1 : T ⟶ B') y).left z J J' = 1 := by
  intro S S' B B' _ _ _ _ M M' hM hM' hB' f β β₂ w hβ hsq hw hn T y z J J' hJ hJ'
  have hG := GlobalTheory.globalFns_holds
  have hL : (abelian₂ B M).IsLB := DVR.linComb_isLB _ hM _ _
  have hL' : (abelian₂ B' M').IsLB := DVR.linComb_isLB _ hM' _ _
  have hw₀ : β ≫ B.hom = B'.hom ≫ f := hβ.1.w
  have pt_mul : ∀ {T₀ : Over S'} (a b : T₀ ⟶ B'), toBase hw₀ (a * b) = toBase hw₀ a * toBase hw₀ b :=
    fun a b => Over.OverMorphism.ext (hβ.2 _ a b _ _ rfl rfl).symm
  have pt_one : ∀ T₀ : Over S', toBase hw₀ (1 : T₀ ⟶ B') = 1 := fun T₀ =>
    mul_eq_left.1 ((pt_mul 1 1).symm.trans (congrArg (toBase hw₀) (mul_one 1)))
  have β₂_lift : ∀ {T₀ : Over S'} (a b : T₀ ⟶ B'),
      (lift a b).left ≫ β₂ = (lift (toBase hw₀ a) (toBase hw₀ b)).left := fun a b => square_over_hom_ext
    (by rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]; rfl)
    (by rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd]; rfl)
  have Hlam : ∀ {T₀ : Over S'} (a b : T₀ ⟶ B') {U : Type} [CommGroup U] (h : (T₀.left ⟶ B.left) → U),
      ∏ i, h (((lift a b).left ≫ β₂) ≫ lamφ B i) ^ lamε i =
        h (toBase hw₀ a * toBase hw₀ b).left * (h (toBase hw₀ a).left)⁻¹ * (h (toBase hw₀ b).left)⁻¹ *
          h (1 : Over.mk (T₀.hom ≫ f) ⟶ B).left := fun a b U _ h => by
    rw [β₂_lift]; exact prod_lam (toBase hw₀ a) (toBase hw₀ b) h
  let φ1 : Fin 1 → (B'.left ⟶ (G2 B').left) := fun _ => (lift (1 : B' ⟶ B') (𝟙 B')).left
  let ε1 : Fin 1 → ℤ := fun _ => 1
  have fe' : FormEq (K := PEmpty) PEmpty.elim PEmpty.elim (flatφ (lamφ B') φ1) (flatε lamε ε1) := fun U _ h => by
    rw [prod_flat, Fin.prod_univ_one, Fintype.prod_empty]
    show 1 = (∏ i, h ((lift (1 : B' ⟶ B') (𝟙 B')).left ≫ lamφ B' i) ^ lamε i) ^ (1 : ℤ)
    rw [prod_lam, _root_.one_mul (𝟙 B')]
    apply Additive.ofMul.injective
    simp only [zpow_one, ofMul_mul, ofMul_inv, ofMul_one]
    abel
  have fe : FormEq (K := PEmpty) PEmpty.elim PEmpty.elim (flatφ (lamφ B) fun k => φ1 k ≫ β₂) (flatε lamε ε1) :=
    fun U _ h => by
      rw [prod_flat, Fin.prod_univ_one, Fintype.prod_empty]
      show 1 = (∏ i, h (((lift (1 : B' ⟶ B') (𝟙 B')).left ≫ β₂) ≫ lamφ B i) ^ lamε i) ^ (1 : ℤ)
      rw [Hlam, pt_one, _root_.one_mul]
      apply Additive.ofMul.injective
      simp only [zpow_one, ofMul_mul, ofMul_inv, ofMul_one]
      abel
  obtain ⟨g', hg', hv'⟩ := exists_gen hM' fe' (LB.oneGen M') (oneGen_isGen _)
  obtain ⟨g, hg, hv⟩ := exists_gen hM fe (LB.oneGen M) (oneGen_isGen _)
  have Fa : ∀ {Z : Scheme.{0}} (r : Z ⟶ B'.left) (z₀ : Z) J₀, Good M' z₀ J₀ →
      val (L := abelian₂ B' M') (nest M' (lamφ B') lamε φ1 ε1 g') r z₀ (ind B' J₀) = 1 := fun r z₀ J₀ hJ₀ => by
    refine (val_nest hg' r (good_ind hJ₀) hJ₀).trans ?_
    simp only [adj_ind hM' hJ₀, one_zpow, Finset.prod_const_one, _root_.one_mul]
    exact (hv' _ r z₀ J₀ hJ₀).trans (val_one r)
  have Ft : ∀ {Z : Scheme.{0}} (r : Z ⟶ B'.left) (z₀ : Z) J₀, Good M z₀ J₀ →
      val (L := abelian₂ B M) (nest M (lamφ B) lamε (fun k => φ1 k ≫ β₂) ε1 g) r z₀ (ind B J₀) = 1 :=
    fun r z₀ J₀ hJ₀ => by
      refine (val_nest hg r (good_ind hJ₀) hJ₀).trans ?_
      simp only [adj_ind hM hJ₀, one_zpow, Finset.prod_const_one, _root_.one_mul]
      exact (hv _ r z₀ J₀ hJ₀).trans (val_one r)
  have Fp : ∀ {T₀ : Over S'} (c : T₀ ⟶ B') (z₀ : T₀.left) (J₀ : (T₀.left ⟶ B.left) → M.ι)
      (J₀' : (T₀.left ⟶ B'.left) → M'.ι),
      pw w φ1 ε1 c.left z₀ (fun k => ind B J₀ (c.left ≫ φ1 k ≫ β₂)) (fun k => ind B' J₀' (c.left ≫ φ1 k)) =
        lamVal w (lift (1 : T₀ ⟶ B') c).left z₀ J₀ J₀' := by
    intro T₀ c z₀ J₀ J₀'
    rw [pw_eq, Fin.prod_univ_one]
    show lamVal w (c ≫ lift (1 : B' ⟶ B') (𝟙 B')).left z₀ J₀ J₀' ^ (1 : ℤ) = _
    rw [comp_lift, comp_one_pt, Category.comp_id, zpow_one]
  have he : (1 : 𝟙_ (Over S') ⟶ B').left ≫ B'.hom = 𝟙 _ := Over.w (1 : 𝟙_ (Over S') ⟶ B')
  have E := rigid_pw w hw hL hL' φ1 ε1 (nest_isGen hg') (nest_isGen hg) B'.hom _ he (hG _ _ hB').2
    (fun y₀ => by
      obtain ⟨J₁, hJ₁⟩ := GlobalTheory.UU.exists_good_pt hM y₀
      obtain ⟨J₁', hJ₁'⟩ := GlobalTheory.UU.exists_good_pt hM' y₀
      refine ⟨ind B J₁, ind B' J₁', good_ind hJ₁, good_ind hJ₁', ?_⟩
      rw [Ft _ y₀ J₁ hJ₁, Fp (1 : 𝟙_ (Over S') ⟶ B'), Fa _ y₀ J₁' hJ₁', hn (𝟙_ (Over S')) y₀ J₁ J₁' hJ₁ hJ₁',
        _root_.mul_one])
    T.left y.left z (ind B J) (ind B' J') (good_ind hJ) (good_ind hJ')
  rw [Ft _ z J hJ, Fp y, Fa _ z J' hJ', _root_.mul_one] at E
  exact E.symm

end GlobalTheory.MumRigidZeroPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoCartesianSquareTrivialFirstAxisStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordBundleIso_cartesianSquare_trivial_first_axis : ∀ {S S' : Scheme.{0}} (B : Over S) (B' : Over S') [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] (M : LB B.left) (M' : LB B'.left), M.IsLB → M'.IsLB → IsAbelianScheme B' → ∀ (f : S' ⟶ S) (β : B'.left ⟶ B.left) (β₂ : (G2 B').left ⟶ (G2 B).left) (w : LB.Iso (abelian₂ B' M') ((abelian₂ B M).pull β₂)), IsGrpPullback B' B f β → IsSquare β β₂ → w.IsGen → (∀ (T : Over S') (z : T.left) (J : (T.left ⟶ B.left) → M.ι) (J' : (T.left ⟶ B'.left) → M'.ι), Good M z J → Good M' z J' → lamVal w (lift (1 : T ⟶ B') (1 : T ⟶ B')).left z J J' = 1) → ∀ (T : Over S') (y : T ⟶ B') (z : T.left) (J : (T.left ⟶ B.left) → M.ι) (J' : (T.left ⟶ B'.left) → M'.ι), Good M z J → Good M' z J' → lamVal w (lift (1 : T ⟶ B') y).left z J J' = 1 := by
  first | exact @GlobalTheory.MumRigidZeroPull.lamVal_one_left_pull | exact GlobalTheory.MumRigidZeroPull.lamVal_one_left_pull | (intros; apply GlobalTheory.MumRigidZeroPull.lamVal_one_left_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoEqOneAlongAxes
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.TInj

theorem lamVal_axes_one : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (ω : W →+* V) (s : I → V) (e : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left) (ββ : (G2 D.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull ββ)), D.TauBimult → From T ω s ε n D e β ββ w → ∀ (Z : Over (Sp V)) (y : Z ⟶ D.P.A) (z : Z.left) J J', Good T.M.L z J → Good D.P.L z J' → lamVal w (lift (1 : Z ⟶ D.P.A) y).left z J J' = 1 ∧ lamVal w (lift y (1 : Z ⟶ D.P.A)).left z J J' = 1 := by
  intro o W _ _ _ T I _ ε n V _ _ D ω s e β ββ w hB hF Z y z J J' hJ hJ'
  letI := D.P.isAb.comm
  have hpb := hF.1
  have hsq := hF.2.1
  have hw := hF.2.2.1
  have N := GlobalTheory.T.mumfordBundleIso_origin_one_of_generic_origin_domain T.B D.P.A T.M.L D.P.L T.M.isLB D.P.isLB (spMap ω) β ββ w hpb hsq hw
    (GlobalTheory.T.mumfordBundleIso_generic_origin_one_tautologicalBase T ε n V D ω s e β ββ w hB hF)
  exact ⟨GlobalTheory.T.mumfordBundleIso_cartesianSquare_trivial_first_axis T.B D.P.A T.M.L D.P.L T.M.isLB D.P.isLB D.P.isAb (spMap ω) β ββ w hpb hsq hw N Z y z J J' hJ hJ',
    GlobalTheory.T.mumfordBundleIso_cartesianSquare_trivial_second_axis T.B D.P.A T.M.L D.P.L T.M.isLB D.P.isLB D.P.isAb (spMap ω) β ββ w hpb hsq hw N Z y z J J' hJ hJ'⟩

end GlobalTheory.TInj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoEqOneAlongAxesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumford_bundle_iso_eq_one_along_axes : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (ω : W →+* V) (s : I → V) (e : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left) (ββ : (G2 D.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull ββ)), D.TauBimult → From T ω s ε n D e β ββ w → ∀ (Z : Over (Sp V)) (y : Z ⟶ D.P.A) (z : Z.left) J J', Good T.M.L z J → Good D.P.L z J' → lamVal w (lift (1 : Z ⟶ D.P.A) y).left z J J' = 1 ∧ lamVal w (lift y (1 : Z ⟶ D.P.A)).left z J J' = 1 := by
  first | exact @GlobalTheory.TInj.lamVal_axes_one | exact GlobalTheory.TInj.lamVal_axes_one | (intros; apply GlobalTheory.TInj.lamVal_axes_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareClassAdditiveInDualVariable
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareClassAdditiveInDualVariable
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

theorem GlobalTheory.AbDual.poincare_evc_mul_right : ∀ (K : Type) [Field K] (A A' : AbVar K) (P : LB (A.X ⊗ A'.X).left)
    (hP : AbDual.IsDual A.X A'.X P) (Y : Over (Sp K)) (a : Y ⟶ A.X) (b b' : Y ⟶ A'.X),
    AbDual.evc hP.isLB a (b * b') = AbDual.evc hP.isLB a b + AbDual.evc hP.isLB a b' := by
  intro K _ A A' P hP Y a b b'
  have hs : (AbDual.swap P).IsLB := pull_isLB hP.isLB _
  have h := (AbDual.isAdditive_iff hs).1 (AbDual.isDual_isAdditive_swap _ A.X A'.X P A'.ab hP) Y b b' a
  rwa [AbDual.evc_swap hP.isLB hs, AbDual.evc_swap hP.isLB hs, AbDual.evc_swap hP.isLB hs] at h
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareClassAdditiveInDualVariableStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincareClass_additive_in_dual_variable : ∀ (K : Type) [Field K] (A A' : AbVar K) (P : LB (A.X ⊗ A'.X).left) (hP : AbDual.IsDual A.X A'.X P) (Y : Over (Sp K)) (a : Y ⟶ A.X) (b b' : Y ⟶ A'.X), AbDual.evc hP.isLB a (b * b') = AbDual.evc hP.isLB a b + AbDual.evc hP.isLB a b' := by
  first | (exact @GlobalTheory.AbDual.poincare_evc_mul_right) | (exact GlobalTheory.AbDual.poincare_evc_mul_right) | (intros; apply GlobalTheory.AbDual.poincare_evc_mul_right  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerOneFormEqZeroOfUniformisedValues
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerOneFormEqZeroOfUniformisedValues
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem form_eq_zero_of_evForm_eq_zero : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.affineOpens) (ξ : Ω[Sec (str A) U.1⁄ℂ]), (∀ z ∈ pre u.ex U.1, evForm u.ex U.1 z ξ = 0) → ξ = 0 := by
  intro A _ g L u hA U ξ hξ
  obtain ⟨d, ω, -, -, -, hsum, hev⟩ := GlobalTheory.T.kaehler_differentials_free_coordinate_forms_abelian A g L u hA U
  have hz : ∀ a, (d a).liftKaehlerDifferential ξ = 0 := by
    intro a
    apply GlobalTheory.T.eq_zero_of_val_eq_zero_abelian A g L u hA U.1
    intro z hz
    rw [← hev a ξ z hz, hξ z hz]
    rfl
  rw [hsum ξ]
  simp [hz]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerOneFormEqZeroOfUniformisedValuesStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kaehlerOneForm_eq_zero_of_uniformised_values : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.affineOpens) (ξ : Ω[Sec (str A) U.1⁄ℂ]), (∀ z ∈ pre u.ex U.1, evForm u.ex U.1 z ξ = 0) → ξ = 0 := by
  first | exact @GlobalTheory.form_eq_zero_of_evForm_eq_zero | exact GlobalTheory.form_eq_zero_of_evForm_eq_zero | (intros; apply GlobalTheory.form_eq_zero_of_evForm_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchIntegrableOfProjArithAmbient
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchIntegrableOfProjArithAmbient
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem archIntegrable_of_isAmb : ArchInteg → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k),
    IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 : ℕ) →
    ∀ (M N : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), N.ArchIntegrable M e hr := by
  intro H k _ Y _ q hq e he M N r hr σ
  rcases isEmpty_or_nonempty (CxPts q σ) with h0 | ⟨⟨y⟩⟩
  · exact ⟨MeasureTheory.Integrable.of_isEmpty, MeasureTheory.Integrable.of_isEmpty⟩
  · have hc : CharZero Γ(Y, ⊤) :=
      RingHom.charZero (S := ℂ) ((Scheme.ΓSpecIso (.of ℂ)).hom.hom.comp y.1.appTop.hom)
    exact H k Y q e ⟨hq.1, hq.2, ‹_›, hq.3, (flat_int_iff_charZero _).2 hc, he⟩ M N r hr σ

end GlobalTheory.MixHt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchIntegrableOfProjArithAmbientStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archIntegrable_of_projArithAmbient : ArchInteg → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 : ℕ) → ∀ (M N : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), N.ArchIntegrable M e hr := by
  first | exact @GlobalTheory.MixHt.archIntegrable_of_isAmb | exact GlobalTheory.MixHt.archIntegrable_of_isAmb | (intros; apply GlobalTheory.MixHt.archIntegrable_of_isAmb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinValueDerivativesViaJets
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinValueDerivativesViaJets
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.CMVal (OF Af lattice IsCMType)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum IsEisValue polydisc)

theorem GlobalTheory.HilbFam.eValue_derivs : EisExp → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ) (e : I ≃ Emb (FR E)) (θ : E) (τ : ℍ) (Λ : Set E) (L : Lat (FR E)) (n : ℕ) (s N : ℕ) (g : (I → ℂ) → ℂ) (κ : I → ℕ) (u : List I) (Ch : ℍ → ℂ), 2 ≤ Module.finrank ℚ (FR E) → 1 ≤ s → 0 < N → HasLevel N L → (∀ i (x : FR E), φ i (x : E) = ((e i x : ℝ) : ℂ)) → (∀ i, φ i θ = (τ : ℂ)) → 0 < n → (∀ x : Fin 2 → FR E, x ∈ L ↔ ∃ y ∈ Λ, (n : E) * y = (x 0 : E) * θ + (x 1 : E)) → IsDefSum φ (2 * s) Λ g → (∀ i, u.count i = κ i) → iterD u g 0 * ((Real.pi / τ.im : ℝ) : ℂ) ^ (∑ i, κ i) / (2 * Real.pi * Complex.I) ^ (2 * s * Module.finrank ℚ (FR E) + 2 * ∑ i, κ i) = (n : ℂ) ^ (2 * s * Module.finrank ℚ (FR E)) * ∑ μ ∈ Finset.Iic (fun j ↦ κ (e.symm j)), ((∏ j, rco (2 * s) (κ (e.symm j)) (μ j) : ℤ) : ℂ) * (((Real.pi / τ.im : ℝ) : ℂ) / (2 * Real.pi * Complex.I) ^ 2 - Ch τ) ^ (∑ j, (κ (e.symm j) - μ j)) * hfun (2 * s) L μ Ch τ := by
  intro hE E _ _ _ I _ _ φ e θ τ Λ L n s N g κ u Ch hf hs hN hL hφ hθ hn hLΛ hD hu
  have h1 := GlobalTheory.T.deformed_lattice_sum_derivatives_eq_eisenstein_jets hE E I φ e θ τ Λ L n s N g κ u hf hs hN hL hφ hθ hn hLΛ hD hu
  have h2 := GlobalTheory.T.eisenstein_jet_conj_direction_diagonal_expansion hE (FR E) hf s N L hs hN hL τ (fun j ↦ κ (e.symm j)) Ch
  have hsum : ∑ j, κ (e.symm j) = ∑ i, κ i := Equiv.sum_comp e.symm κ
  rw [hsum] at h2
  unfold wt at h2
  rw [hsum] at h2
  rw [h1, ← h2]
  ring
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinValueDerivativesViaJetsStatement
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.CMVal (OF Af lattice IsCMType)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum IsEisValue polydisc)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertEisenstein_value_derivatives_via_jets : EisExp → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ) (e : I ≃ Emb (FR E)) (θ : E) (τ : ℍ) (Λ : Set E) (L : Lat (FR E)) (n : ℕ) (s N : ℕ) (g : (I → ℂ) → ℂ) (κ : I → ℕ) (u : List I) (Ch : ℍ → ℂ), 2 ≤ Module.finrank ℚ (FR E) → 1 ≤ s → 0 < N → HasLevel N L → (∀ i (x : FR E), φ i (x : E) = ((e i x : ℝ) : ℂ)) → (∀ i, φ i θ = (τ : ℂ)) → 0 < n → (∀ x : Fin 2 → FR E, x ∈ L ↔ ∃ y ∈ Λ, (n : E) * y = (x 0 : E) * θ + (x 1 : E)) → IsDefSum φ (2 * s) Λ g → (∀ i, u.count i = κ i) → iterD u g 0 * ((Real.pi / τ.im : ℝ) : ℂ) ^ (∑ i, κ i) / (2 * Real.pi * Complex.I) ^ (2 * s * Module.finrank ℚ (FR E) + 2 * ∑ i, κ i) = (n : ℂ) ^ (2 * s * Module.finrank ℚ (FR E)) * ∑ μ ∈ Finset.Iic (fun j ↦ κ (e.symm j)), ((∏ j, rco (2 * s) (κ (e.symm j)) (μ j) : ℤ) : ℂ) * (((Real.pi / τ.im : ℝ) : ℂ) / (2 * Real.pi * Complex.I) ^ 2 - Ch τ) ^ (∑ j, (κ (e.symm j) - μ j)) * hfun (2 * s) L μ Ch τ := by
  first | exact @GlobalTheory.HilbFam.eValue_derivs | exact GlobalTheory.HilbFam.eValue_derivs | (intros; apply GlobalTheory.HilbFam.eValue_derivs <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftOfEtaleSurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftOfEtaleSurjective
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_lift_of_etale_surjective : ∀ (K : Type) [Field K] [IsAlgClosed K] (X Y : Scheme.{0}) (π : Y ⟶ X), Etale π → Surjective π → ∀ x : Sp K ⟶ X, ∃ y : Sp K ⟶ Y, y ≫ π = x := by
  intro K _ _ X Y π hE hS x
  haveI := hE
  haveI := hS
  have : LocallyOfFiniteType π := inferInstance
  let t : Sp K := IsLocalRing.closedPoint K
  obtain ⟨w, hw⟩ := π.surjective (x t)
  obtain ⟨y, -, -⟩ := Scheme.Pullback.exists_preimage_pullback w t hw
  have : JacobsonSpace ↥(pullback π x) := LocallyOfFiniteType.jacobsonSpace (pullback.snd π x)
  obtain ⟨y', -, hy'⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set ↥(pullback π x)))
    ⟨y, trivial⟩ isOpen_univ.isLocallyClosed
  have hc : IsClosed {y'} := hy'
  refine ⟨pointOfClosedPoint (pullback.snd π x) y' hc ≫ pullback.fst π x, ?_⟩
  rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftOfEtaleSurjectiveStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_of_etale_surjective' : ∀ (K : Type) [Field K] [IsAlgClosed K] (X Y : Scheme.{0}) (π : Y ⟶ X), Etale π → Surjective π → ∀ x : Sp K ⟶ X, ∃ y : Sp K ⟶ Y, y ≫ π = x := by
  first | exact @GlobalTheory.exists_lift_of_etale_surjective | exact GlobalTheory.exists_lift_of_etale_surjective | (intros; apply GlobalTheory.exists_lift_of_etale_surjective; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothWeightsDifferBySmoothFunction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothWeightsDifferBySmoothFunction
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem weight_sub_cInf : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (B : LB X) (φ ψ : Weight p σ B), φ.IsCInf → ψ.IsCInf → ∃ u : CxPts p σ → ℝ, (∀ y, CInfAt u y) ∧ ∀ i, ∀ y ∈ ptsIn p σ (B.U i), ψ.φ i y = φ.φ i y + u y := by
  intro k _ X p σ B φ ψ hφ hψ
  have key : ∀ i y, y ∈ ptsIn p σ (B.U i) →
      ψ.φ i y - φ.φ i y = ψ.φ (pick φ.isLB y) y - φ.φ (pick φ.isLB y) y := by
    intro i y hi
    rw [ψ.trans _ i y (mem_pick φ.isLB y) hi, φ.trans _ i y (mem_pick φ.isLB y) hi]
    ring
  refine ⟨fun y => ψ.φ (pick φ.isLB y) y - φ.φ (pick φ.isLB y) y, fun y => ?_, fun i y hi => ?_⟩
  · have hy := mem_pick φ.isLB y
    have hs : CInfAt (fun z => ψ.φ (pick φ.isLB y) z + -φ.φ (pick φ.isLB y) z) y :=
      (hψ _ y hy).add (hφ _ y hy).neg
    refine hs.congr ?_
    filter_upwards [(isOpen_ptsIn _).mem_nhds hy] with z hz
    rw [← key _ z hz, sub_eq_add_neg]
  · have := key i y hi
    linarith

end GlobalTheory.Mix
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothWeightsDifferBySmoothFunctionStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_weights_differ_by_smooth_function : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (B : LB X) (φ ψ : Weight p σ B), φ.IsCInf → ψ.IsCInf → ∃ u : CxPts p σ → ℝ, (∀ y, CInfAt u y) ∧ ∀ i, ∀ y ∈ ptsIn p σ (B.U i), ψ.φ i y = φ.φ i y + u y := by
  first | exact @GlobalTheory.Mix.weight_sub_cInf | exact GlobalTheory.Mix.weight_sub_cInf | (intros; apply GlobalTheory.Mix.weight_sub_cInf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LePreimageOfIsTranslate
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory.KSRechart

theorem resG_appLE {Y Z : Scheme.{0}} (m : Z ⟶ Y) (U : Y.Opens) {V V' : Z.Opens} (h : V ≤ m ⁻¹ᵁ U) (e : V' ≤ V)
    (r : Γ(Y, U)) : resG Z e ((m.appLE U V h).hom r) = (m.appLE U V' (e.trans h)).hom r := by
  show ((m.appLE U V h) ≫ Z.presheaf.map (homOfLE e).op).hom r = _
  rw [Scheme.Hom.appLE_map]

end GlobalTheory.KSRechart

namespace GlobalTheory.KSRechart


private theorem valR_comp_eq_valR_app' {A : Type} [CommRing A] {X Z : Scheme.{0}} (x : Sp A ⟶ Z) (m : Z ⟶ X)
    (U : X.Opens) (O : Z.Opens) (h : O ≤ m ⁻¹ᵁ U) (hO : ⊤ ≤ x ⁻¹ᵁ O) (r : Γ(X, U)) :
    valR x O ((m.appLE U O h).hom r) = valR (x ≫ m) U r := by
  have hU : ⊤ ≤ (x ≫ m) ⁻¹ᵁ U := fun p hp => h (hO hp)
  unfold valR
  rw [dite_eq_left hO, dite_eq_left hU]
  congr 1
  show ((m.appLE U O h) ≫ x.appLE O ⊤ hO).hom r = _
  rw [Scheme.Hom.appLE_comp_appLE]

end GlobalTheory.KSRechart

namespace GlobalTheory.KSRechart

theorem valR_appLE {X Z : Scheme.{0}} (m : Z ⟶ X) (U : X.affineOpens) {S : Type} [CommRing S] (φ : Γ(X, U.1) →+* S)
    (g₀ : Sp S ⟶ Z) (hg : g₀ ≫ m = spMap φ ≫ chart U) {O : Z.Opens} (h : O ≤ m ⁻¹ᵁ U.1) (hO : ⊤ ≤ g₀ ⁻¹ᵁ O)
    (r : Γ(X, U.1)) : valR g₀ O ((m.appLE U.1 O h).hom r) = φ r := by
  rw [valR_comp_eq_valR_app' g₀ m U.1 O h hO r, hg]
  exact GlobalTheory.FlagEmb.QuotLine.valR_chart U.2 φ r

end GlobalTheory.KSRechart

namespace GlobalTheory.KSRechart

end GlobalTheory.KSRechart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarOperatorLocalCalculusComplexForms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarOperatorLocalCalculusComplexForms
set_option autoImplicit false

open Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.CxForm

namespace GlobalTheory.CxForm

theorem dbarAt_local_calculus : ∀ (n : ℕ) (v : V n),
    (∀ α β : V n → Alt n, α =ᶠ[𝓝 v] β → dbarAt α v = dbarAt β v) ∧
    (∀ (J : Type) (s : Finset J) (α : J → V n → Alt n),
      (∀ j ∈ s, ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (α j x) S) v) →
      dbarAt (fun x => ∑ j ∈ s, α j x) v = ∑ j ∈ s, dbarAt (α j) v) ∧
    (∀ (c : ℂ) (α : V n → Alt n), (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (α x) S) v) →
      dbarAt (fun x => c • α x) v = c • dbarAt α v) ∧
    (∀ γ : Alt n, dbarAt (fun _ => γ) v = 0) ∧
    (∀ (w : V n → Ev n) (β : V n → Alt n),
      (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr ((w x : Alt n)) S) v) →
      (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (β x) S) v) →
      dbarAt (fun x => (w x : Alt n) * β x) v =
        dbarAt (fun x => (w x : Alt n)) v * β v + (w v : Alt n) * dbarAt β v) := by
  intro n v
  obtain ⟨-, hsmul, hsum, hgerm, hconst⟩ := GlobalTheory.CxForm.delAt_dbarAt_linear_local n v
  exact ⟨fun α β h => (hgerm α β h).2, fun J s α h => (hsum J s α h).2, fun c α h => (hsmul α c h).2,
    fun γ => (hconst γ).2, fun w β hw hβ =>
      (FormMul.leibniz_of_comm n (fun x => (w x : Alt n)) β v (w v : Alt n) hw hβ).2
        fun a => Subalgebra.mem_center_iff.1 (w v).2 (dzb a)⟩

end GlobalTheory.CxForm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarOperatorLocalCalculusComplexFormsStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dbar_operator_local_calculus_complex_forms : ∀ (n : ℕ) (v : V n), (∀ α β : V n → Alt n, α =ᶠ[𝓝 v] β → dbarAt α v = dbarAt β v) ∧ (∀ (J : Type) (s : Finset J) (α : J → V n → Alt n), (∀ j ∈ s, ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (α j x) S) v) → dbarAt (fun x => ∑ j ∈ s, α j x) v = ∑ j ∈ s, dbarAt (α j) v) ∧ (∀ (c : ℂ) (α : V n → Alt n), (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (α x) S) v) → dbarAt (fun x => c • α x) v = c • dbarAt α v) ∧ (∀ γ : Alt n, dbarAt (fun _ => γ) v = 0) ∧ (∀ (w : V n → Ev n) (β : V n → Alt n), (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr ((w x : Alt n)) S) v) → (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (β x) S) v) → dbarAt (fun x => (w x : Alt n) * β x) v = dbarAt (fun x => (w x : Alt n)) v * β v + (w v : Alt n) * dbarAt β v) := by
  first | exact @GlobalTheory.CxForm.dbarAt_local_calculus | exact GlobalTheory.CxForm.dbarAt_local_calculus | (intros; apply GlobalTheory.CxForm.dbarAt_local_calculus <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorSectionsNonvanishingFiniteSet
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorSectionsNonvanishingFiniteSet
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixHt

theorem exists_tens_sec_finite_subset_nonzeroLocus : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k),
    IsAmb q → ∀ (M : HermLB q) (S : Set Y), S.Finite →
      ∃ (A : HermLB q) (s : (M.tens A).B.Sec) (u : A.B.Sec), S ⊆ nonzeroLocus s ∧ S ⊆ nonzeroLocus u := by
  intro k _ Y q hq M S hS
  have := hq.isNoetherian
  obtain ⟨N, j, hj, e⟩ := hq.isProjOver
  let A₀ : HermLB q := (ProjSpace.hermitianTwistingSheaf k N).pull j e
  have hA : IsAmpleLB A₀.B := by
    dsimp [A₀, HermLB.pull, ProjSpace.hermitianTwistingSheaf, HermLB.fs]
    exact (isAmple_projective_O_one k N).pull_of_isClosedImmersion j
  obtain ⟨n, h₁, h₂⟩ := (tendsto_natCast_atTop_atTop.eventually
    ((hA.eventually_exists_finite_subset_nonzeroLocus M.isLB hS).and
      (hA.eventually_exists_finite_subset_nonzeroLocus (LB.isLB_triv Y) hS))).exists
  obtain ⟨s, hs⟩ := h₁ (CechPic.tens M.B (lbPow A₀.B n)) (isLB_tens M.isLB (isLB_lbPow A₀.isLB n)) (by
    rw [cls_tens M.isLB (isLB_lbPow A₀.isLB n), cls_lbPow A₀.isLB, natCast_zsmul])
  obtain ⟨u, hu⟩ := h₂ (lbPow A₀.B n) (isLB_lbPow A₀.isLB n) (by
    rw [cls_lbPow A₀.isLB, cls_triv, zero_add, natCast_zsmul])
  exact ⟨A₀.pow n, s, u, hs, hu⟩

end GlobalTheory.MixHt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorSectionsNonvanishingFiniteSetStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tensor_sections_nonvanishing_finite_set : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∀ (M : HermLB q) (S : Set Y), S.Finite → ∃ (A : HermLB q) (s : (M.tens A).B.Sec) (u : A.B.Sec), S ⊆ nonzeroLocus s ∧ S ⊆ nonzeroLocus u := by
  first | exact @GlobalTheory.MixHt.exists_tens_sec_finite_subset_nonzeroLocus | exact GlobalTheory.MixHt.exists_tens_sec_finite_subset_nonzeroLocus | (intros; apply GlobalTheory.MixHt.exists_tens_sec_finite_subset_nonzeroLocus <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPosRegPull
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Weight

open ReciprocityTheory.L2DbarEstimates (V leviV)

theorem semiPosReg_pull : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (π : Y ⟶ X) (hπ : π ≫ p = q) (D D' : ℕ), SmoothOfRelativeDimension D p → ∀ (B : LB X) (φ : Weight p σ B), φ.IsCInf → φ.SemiPosReg D → (φ.pull π hπ).SemiPosReg D' := by
  intro k _ X Y p q σ π hπ D D' hs B φ hC hSP
  haveI := hs
  intro i c y hy ξ
  set m := PtsOver.map π hπ (spMap σ)
  have hm : ∀ z, (m z).1 = z.1 ≫ π := fun _ => rfl
  obtain ⟨c0, h0⟩ := AlgChart.exists_mem_source (p := p) (σ := σ) (D := D) (m y)
  have him : m y ∈ ptsIn p σ (B.U (i PUnit.unit)) :=
    mem_of_mem_linComb (m := fun _ => m y) (fun _ => rfl) hy.2 PUnit.unit
  set F : V D' → V D := c0.e ∘ m ∘ c.e.symm with hFdef
  set U := c.e.target ∩ c.e.symm ⁻¹' (m ⁻¹' c0.e.source)
  have hU : IsOpen U := GlobalTheory.ChartGlue.isOpen_over c.e (c0.e.open_source.preimage (continuous_of_comp hm))
  have hyU : c.e y ∈ U := GlobalTheory.ChartGlue.mem_over c.e hy.1 h0
  have hF0 : DifferentiableOn ℂ F U := AlgChart.holo_map hm c c0
  have hF : ContDiffOn ℂ 2 F U := (contDiffOn_piLp 2).2 fun a =>
    (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn D' _ U hU
      (differentiableOn_euclidean.1 hF0 a)).of_le (by norm_cast)
  have hFy : F (c.e y) = c0.e (m y) := by
    simp only [hFdef, Function.comp_apply, c.e.left_inv hy.1]
  set g : V D → ℂ := fun v => (φ.φ (i PUnit.unit) (c0.e.symm v) : ℂ) with hgdef
  have hg : ContDiffAt ℝ 2 g (F (c.e y)) := hFy ▸
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ (hC.contDiffAt c0 h0 him)
  have e : (fun v => ((φ.pull π hπ).φ i (c.e.symm v) : ℂ)) =ᶠ[𝓝 (c.e y)] g ∘ F := by
    filter_upwards [hU.mem_nhds hyU] with v hv
    have := Weight.pull_φ φ π hπ i (c.e.symm v)
    simp only [g, hFdef, Function.comp_apply, c0.e.left_inv hv.2]
    exact congrArg _ this
  rw [ReciprocityTheory.L2DbarEstimates.leviV_congr e,
    ReciprocityTheory.ChartRestriction.G.AR.Up.RGF.gc_leviV_comp D' D g F U hU _ hyU hF hg ξ, hFy]
  exact hSP (i PUnit.unit) c0 (m y) ⟨h0, him⟩ _

end GlobalTheory.Weight
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHodgeFiltrationToPDivOmegaLinearMap
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHodgeFiltrationToPDivOmegaLinearMap
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

theorem GlobalTheory.PtExt.exists_hodge_to_omega : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 →
    ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A →
    ∀ (G : PDivGroup p R) (t : GlobalTheory.PDivGroup.TorsionTower G A),
    ∃ ψ : PrimitiveSubmodule A →ₗ[R] G.omega,
      ∀ c : PrimitiveSubmodule A, GlobalTheory.PtExt.IsCan t c.1 (G.rigOfOmega (ψ c)) := by
  intro p _ R _ N hN A _ hA G t
  obtain ⟨L, hL⟩ := GlobalTheory.PtExt.exists_canMap R A p G t hA
  have hinj := GlobalTheory.PDivGroup.rigOfOmega_injective_of_pow p R N hN G
  have hmem : ∀ c : PrimitiveSubmodule A, (L ∘ₗ (PrimitiveSubmodule A).subtype) c ∈ LinearMap.range G.rigOfOmega := by
    intro c
    have hc : c.1.1 ∈ F1 (A.hom ≫ 𝟙 _) := c.2
    rw [hodgeFiltration_eq_range] at hc
    obtain ⟨β, hβ⟩ := hc
    have hβp : Form.cl _ β ∈ primDR A := hβ ▸ c.1.2
    obtain ⟨w, -, hw⟩ := GlobalTheory.PtExt.isCan_form R A p G t β hβp
    have hcc : (⟨_, hβp⟩ : primDR A) = c.1 := Subtype.ext hβ
    rw [hcc] at hw
    exact ⟨w, ((hL _ _).1 hw).symm⟩
  refine ⟨(LinearEquiv.ofInjective G.rigOfOmega hinj).symm ∘ₗ
    (L ∘ₗ (PrimitiveSubmodule A).subtype).codRestrict (LinearMap.range G.rigOfOmega) hmem, fun c ↦ ?_⟩
  rw [hL]
  exact (LinearEquiv.ofInjective_symm_apply G.rigOfOmega (h := hinj)
    ((L ∘ₗ (PrimitiveSubmodule A).subtype).codRestrict (LinearMap.range G.rigOfOmega) hmem c)).symm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHodgeFiltrationToPDivOmegaLinearMapStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_hodgeFiltration_to_pDivOmega_linearMap
    (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ) (hN : (p : R) ^ N = 0)
    (A : Over (Sp R)) [GrpObj A] (hA : IsAbelianScheme A) (G : PDivGroup p R)
    (t : G.TorsionTower A) :
    ∃ ψ : PrimitiveSubmodule A →ₗ[R] G.omega,
      ∀ c : PrimitiveSubmodule A, GlobalTheory.PtExt.IsCan t c.1 (G.rigOfOmega (ψ c)) :=
  GlobalTheory.PtExt.exists_hodge_to_omega p R N hN A hA G t
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMulTopChernFormIsTopDegree
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMulTopChernFormIsTopDegree
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem isTopForm_mul_topDens : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → ∀ {ρ : CxPts X.str σ → ℝ}, Continuous ρ → IsTopForm (fun c : AlgChart X.str σ X.dim => c.e) (fun c y => ρ y * topDens E H c y) (ptsIn X.str σ O) := by
  intro F _ σ X m E O H hM ρ hρ
  refine ⟨?_, ?_⟩
  · intro c c' y hy hc hc'
    have hA := (E.nonempty (under y)).choose_spec
    simp only [topDens]
    rw [chernTop_frame_chart_trans E O H hM _ hy c c' hc hc' hA hA]
    ring
  · intro c
    refine GlobalTheory.T.aemeasurable_chart_of_locally_continuous_density c.e (d := fun z => ρ z * topDens E H c z) (isOpen_ptsIn O) ?_
    intro y hy hc
    have hA := (E.nonempty (under y)).choose_spec
    refine ⟨fun v => ρ (c.e.symm v) * chernTop (MvPolynomial.X ((), X.dim))
      (fun w => H (E.nonempty (under y)).choose (c.e.symm w)) v, ?_, ?_⟩
    · have h1 : ContinuousAt (fun v => ρ (c.e.symm v)) (c.e y) :=
        hρ.continuousAt.comp (c.e.continuousAt_symm (c.e.map_source hc))
      have hsm := hM.mContDiffAt_chart hy c hc hA ()
      have hu := hM.isUnit_det_chart hy c hc hA ()
      have h2 : ContinuousAt (fun v => chernTop (MvPolynomial.X ((), X.dim))
          (fun w => H (E.nonempty (under y)).choose (c.e.symm w)) v) (c.e y) := by
        simp only [GlobalTheory.T.chernTopDensity_eq_polarisedTopChern]
        refine continuousAt_const.mul (Complex.continuous_re.continuousAt.comp ?_)
        refine GlobalTheory.T.continuousAt_polarisedTopChernCoeff (fun i a b p q => ?_)
        exact ((MContDiffAt.curv (j := 0) hsm hu (by norm_num) (coordVec a) (coordVec b)) p q).continuousAt
      exact h1.mul h2
    · filter_upwards [(isOpen_ptsIn O).mem_nhds hy, c.e.open_source.mem_nhds hc,
        GlobalTheory.FrameLift.eventually_mem hA] with z hz hzc hzA
      simp only [topDens, c.e.left_inv hzc]
      rw [hM.chernTop_frame _ hz c hzc (E.nonempty (under z)).choose_spec hzA]

end GlobalTheory.GoodTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMulTopChernFormIsTopDegreeStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_mul_top_chern_form_isTopDegree : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → ∀ {ρ : CxPts X.str σ → ℝ}, Continuous ρ → IsTopForm (fun c : AlgChart X.str σ X.dim => c.e) (fun c y => ρ y * topDens E H c y) (ptsIn X.str σ O) := by
  first | exact @GlobalTheory.GoodTop.isTopForm_mul_topDens | exact GlobalTheory.GoodTop.isTopForm_mul_topDens | (intros; apply GlobalTheory.GoodTop.isTopForm_mul_topDens <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoheightOneNotMemOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoheightOneNotMemOpen
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem finite_coheight_one_notMem_open : ∀ (X : Scheme.{0}) [IsIntegral X]
    [AlgebraicGeometry.IsNoetherian X] (U : X.Opens), genericPoint X ∈ U →
    {z : X | Order.coheight z = 1 ∧ z ∉ U}.Finite := by
  intro X _ _ U hU
  classical
  obtain ⟨S, hS, hc, hi, hUn⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible U.isOpen.isClosed_compl
  refine (hS.image fun T => if h : IsIrreducible T then h.genericPoint else genericPoint X).subset
    fun z hz => ?_
  obtain ⟨hz1, hzU⟩ := hz
  obtain ⟨T, hT, hzT⟩ := mem_sUnion.1 (hUn.le (show z ∈ (U : Set X)ᶜ from hzU))
  refine ⟨T, hT, ?_⟩
  simp only [dif_pos (hi T hT)]
  have hg := (hi T hT).isGenericPoint_genericPoint (hc T hT)
  have h₁ : z ≤ (hi T hT).genericPoint := hg.specializes hzT
  have h₂ : (hi T hT).genericPoint < genericPoint X := by
    refine lt_of_le_not_ge (genericPoint_specializes _) fun e => ?_
    have e' : _ = genericPoint X := (Specializes.antisymm e (genericPoint_specializes _)).eq
    have hm : (hi T hT).genericPoint ∈ (U : Set X)ᶜ := hUn.ge (mem_sUnion.2 ⟨T, hT, hg.mem⟩)
    exact hm (e' ▸ hU)
  by_contra hne
  have h₃ := Order.coheight_add_one_le (lt_of_le_not_ge h₁ fun e =>
    hne (Specializes.antisymm h₁ e).eq)
  have h₄ := Order.coheight_add_one_le h₂
  rw [hz1] at h₃
  have h₅ : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add_left (le_add_self.trans h₄) 1).trans h₃
  exact absurd h₅ (by decide)

end GlobalTheory.Mix
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoheightOneNotMemOpenStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_coheight_one_notMem_of_genericPoint_mem : ∀ (X : Scheme.{0}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X] (U : X.Opens), genericPoint X ∈ U → {z : X | Order.coheight z = 1 ∧ z ∉ U}.Finite := by
  first | exact @GlobalTheory.Mix.finite_coheight_one_notMem_open | exact GlobalTheory.Mix.finite_coheight_one_notMem_open | (intros; apply GlobalTheory.Mix.finite_coheight_one_notMem_open <;> assumption)
end
end
