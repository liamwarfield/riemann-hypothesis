module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInnerProductFormulaDataDefiniteBottom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTrianglePolynomialFactor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleNonzeroConstantSecond
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareConstantProportionalRegular

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsHeckeOfIsHeckeWit
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo

namespace GlobalTheory.DrinLev.HT.HeckePt

section Pull

variable {S S' : Scheme.{0}} {f : S' ⟶ S}

theorem ext_of_left {B : Over S} {B' : Over S'} [GrpObj B] [GrpObj B'] {b : B'.left ⟶ B.left}
    (hb : IsGrpPullback B' B f b) {T : Over S'} {u v : T ⟶ B'} (h : u.left ≫ b = v.left ≫ b) : u = v := Over.OverMorphism.ext (hb.1.hom_ext h (by rw [Over.w u, Over.w v]))

variable {A B : Over S} {A' B' : Over S'} [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B']
  {a : A'.left ⟶ A.left} {b : B'.left ⟶ B.left}

def pullMor (ha : IsGrpPullback A' A f a) (hb : IsGrpPullback B' B f b) (ψ : A ⟶ B) : A' ⟶ B' :=
  Over.homMk (hb.1.lift (a ≫ ψ.left) A'.hom (by rw [Category.assoc, Over.w ψ, ha.1.w])) (hb.1.lift_snd _ _ _)

theorem pullMor_left (ha : IsGrpPullback A' A f a) (hb : IsGrpPullback B' B f b) (ψ : A ⟶ B) :
    (pullMor ha hb ψ).left ≫ b = a ≫ ψ.left := by
  simp only [pullMor, Over.homMk_left]
  exact hb.1.lift_fst _ _ _

private theorem pushHom_left_satake_parameters {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) (T : Over S') (x : T ⟶ G') : (pushHom h T x).left = x.left ≫ φ := by
  rfl

theorem push_pullMor (ha : IsGrpPullback A' A f a) (hb : IsGrpPullback B' B f b) (ψ : A ⟶ B) (T : Over S')
    (x : T ⟶ A') : pushHom hb T (x ≫ pullMor ha hb ψ) = pushHom ha T x ≫ ψ := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, pushHom_left_satake_parameters, Category.assoc, pullMor_left]

private theorem isMonHom_of_comp_mul {C : Type*} [Category C] [CartesianMonoidalCategory C] {G H : C} [GrpObj G] [GrpObj H]
    (g : G ⟶ H) (hg : ∀ (T : C) (x y : T ⟶ G), (x * y) ≫ g = x ≫ g * y ≫ g) : IsMonHom g := by
  constructor
  · have h1 := hg (𝟙_ C) 1 1
    rw [_root_.mul_one] at h1
    have h2 : (1 : 𝟙_ C ⟶ G) ≫ g = 1 := mul_left_cancel (h1.symm.trans (_root_.mul_one _).symm)
    simpa [Hom.one_def, toUnit_unit] using h2
  · have h := hg _ (fst G G) (snd G G)
    simp only [Hom.mul_def, lift_fst_snd, Category.id_comp] at h
    rw [h]
    congr 1
    ext <;> simp

theorem isMonHom_pullMor (ha : IsGrpPullback A' A f a) (hb : IsGrpPullback B' B f b) (ψ : A ⟶ B) [IsMonHom ψ] :
    IsMonHom (pullMor ha hb ψ) := by
  refine isMonHom_of_comp_mul _ fun T x y => ext_of_left hb ?_
  rw [← pushHom_left_satake_parameters hb, ← pushHom_left_satake_parameters hb, push_pullMor, map_mul, map_mul, push_pullMor, push_pullMor,
    MonObj.mul_comp]

theorem pow_id_left (ha : IsGrpPullback A' A f a) (n : ℕ) : ((𝟙 A') ^ n).left ≫ a = a ≫ ((𝟙 A) ^ n).left := by
  have h1 := pushHom_left_satake_parameters ha A' ((𝟙 A') ^ n)
  rw [map_pow] at h1
  rw [← h1]
  have h2 : pushHom ha A' (𝟙 A') ^ n = pushHom ha A' (𝟙 A') ≫ (𝟙 A) ^ n := by
    rw [MonObj.comp_pow, Category.comp_id]
  rw [h2]
  simp only [Over.comp_left, pushHom_left_satake_parameters, Over.id_left, Category.id_comp]

theorem pullMor_comp_eq_pow (ha : IsGrpPullback A' A f a) (hb : IsGrpPullback B' B f b) (ψ : A ⟶ B) (ψ' : B ⟶ A)
    (n : ℕ) (h : ψ ≫ ψ' = (𝟙 A) ^ n) : pullMor ha hb ψ ≫ pullMor hb ha ψ' = (𝟙 A') ^ n := by
  apply ext_of_left ha
  rw [Over.comp_left, Category.assoc, pullMor_left hb ha ψ', ← Category.assoc, pullMor_left ha hb ψ, Category.assoc,
    ← Over.comp_left, h, pow_id_left ha n]

end Pull

end GlobalTheory.DrinLev.HT.HeckePt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleIntegralsNeZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NonVanBottom

theorem squareBottomHalfRankSum_le_halfRank (D : D7) (i j : ℕ) : h0 D i j ≤ halfRank D i j := by
  unfold h0 halfRank botBig botSmall
  omega

theorem exists_ne_zero_of_integral {Y : Type} [MeasurableSpace Y] {ν : Measure Y} {S : Set Y} {f : Y → ℂ}
    (h : (∫ y in S, ‖f y‖ ^ 2 ∂ν) ≠ 0) : ∃ y, f y ≠ 0 := by
  by_contra hc
  push_neg at hc
  exact h (by simp [hc])

theorem exists_ne_zero_of_norm_formula {Y : Type} [MeasurableSpace Y] {ν : Measure Y} {S : Set Y} {f : Y → ℂ} {c : ℂ}
    {Λ : ℂ → ℂ} {a b : ℤ} (hc : c ≠ 0) (hΛ : ∀ s : ℤ, a ≤ s → s ≤ b → Λ s ≠ 0)
    (h : ((∫ y in S, ‖f y‖ ^ 2 ∂ν : ℝ) : ℂ) = c * ∏ s ∈ Icc a b, Λ s) : ∃ y, f y ≠ 0 := by
  refine exists_ne_zero_of_integral (ν := ν) (S := S) fun h0 => ?_
  have hp : ∏ s ∈ Icc a b, Λ s ≠ 0 := Finset.prod_ne_zero_iff.2 fun s hs => hΛ s (mem_Icc.1 hs).1 (mem_Icc.1 hs).2
  rw [h0, Complex.ofReal_zero] at h
  exact mul_ne_zero hc hp h.symm

end GlobalTheory.NonVanBottom

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorOfStageTriangle
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StageFactor

open MeasureTheory

variable {D : D7} {T : Type} {A A' WW : HSp D}

theorem ker_add_smul (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (t : T)
    (P Q : PolF D WW.rank A.rank) (c : ℂ) (h : GA D WW) :
    X.ker ψ θ t (P + c • Q) h = fun g => X.ker ψ θ t P h g + c * X.ker ψ θ t Q h g := by
  funext g
  simp [Tri.ker, thetaKO, map_add (f := _), map_smul]

def linI (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (t : T)
    (hint : ∀ P h, IntegrableOn (X.ker ψ θ t P h) X.fd X.m) : PolF D WW.rank A.rank →ₗ[ℂ] (GA D WW → ℂ) where
  toFun P := X.I ψ θ t P
  map_add' P Q := by
    funext h
    have e := ker_add_smul X ψ θ t P Q 1 h
    simp only [one_smul, one_mul] at e
    simp only [Tri.I, Pi.add_apply, e]
    exact integral_add (hint P h) (hint Q h)
  map_smul' c Q := by
    funext h
    have e := ker_add_smul X ψ θ t 0 Q c h
    simp only [zero_add] at e
    have e0 : X.ker ψ θ t 0 h = 0 := by funext g; simp [Tri.ker, thetaKO]
    simp only [Tri.I, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, e, e0, Pi.zero_apply, zero_add]
    exact integral_const_mul c _

theorem linI_apply (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (t : T)
    (hint : ∀ P h, IntegrableOn (X.ker ψ θ t P h) X.fd X.m) (P : PolF D WW.rank A.rank) :
    linI X ψ θ t hint P = X.I ψ θ t P := rfl

theorem factor_of_parts (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (hint : ∀ t P h, IntegrableOn (X.ker ψ θ t P h) X.fd X.m)
    (hker : ∀ t t' P, X.I ψ θ t P = 0 → X.I ψ θ t' P = 0)
    (lam : T → ℂ) (s : PolF D WW.rank A'.rank →ₗ[ℂ] PolF D WW.rank A.rank) (hlam : ∀ t, lam t ≠ 0)
    (hs : ∀ t P', (∀ h, IntegrableOn (X.ker' ψ θ t P' h) X.fd' X.m') → X.I ψ θ t (s P') = lam t • X.I' ψ θ t P')
    (hconv : ∃ P', (∀ t h, IntegrableOn (X.ker' ψ θ t P' h) X.fd' X.m') ∧ ∀ t, X.I' ψ θ t P' ≠ 0) :
    Factor X ψ θ lam := by
  rcases isEmpty_or_nonempty T with hT | ⟨⟨t₀⟩⟩
  · refine ⟨hlam, ModuleCat.of ℂ ℂ, MvPolynomial.lcoeff ℂ 0, MvPolynomial.lcoeff ℂ 0, fun _ => 0,
      fun z => ⟨MvPolynomial.C z, by simp⟩, fun t => hT.elim t, fun t => hT.elim t, fun t => hT.elim t,
      fun t => hT.elim t, 1, by simp, fun t => hT.elim t⟩
  · let K : Submodule ℂ (PolF D WW.rank A.rank) := LinearMap.ker (linI X ψ θ t₀ (hint t₀))
    have hK : ∀ t, LinearMap.ker (linI X ψ θ t (hint t)) = K := fun t => by
      ext P
      simp only [K, LinearMap.mem_ker, linI_apply]
      exact ⟨hker t t₀ P, hker t₀ t P⟩
    let Jb : T → ((PolF D WW.rank A.rank ⧸ K) →ₗ[ℂ] (GA D WW → ℂ)) := fun t =>
      K.liftQ (linI X ψ θ t (hint t)) (hK t).ge
    have hJb : ∀ t, Function.Injective (Jb t) := fun t => by
      rw [← LinearMap.ker_eq_bot]
      exact Submodule.ker_liftQ_eq_bot _ _ _ (hK t).le
    refine ⟨hlam, ModuleCat.of ℂ (PolF D WW.rank A.rank ⧸ K), K.mkQ, K.mkQ ∘ₗ s, fun t => (lam t)⁻¹ • Jb t,
      K.mkQ_surjective, fun t => ?_, hint, fun t P => ?_, fun t P' hP' => ?_, ?_⟩
    · intro x y hxy
      exact hJb t (smul_right_injective _ (inv_ne_zero (hlam t)) hxy)
    · show X.I ψ θ t P = lam t • ((lam t)⁻¹ • Jb t (K.mkQ P))
      rw [smul_smul, mul_inv_cancel₀ (hlam t), one_smul]
      rfl
    · show X.I' ψ θ t P' = (lam t)⁻¹ • Jb t (K.mkQ (s P'))
      have : Jb t (K.mkQ (s P')) = X.I ψ θ t (s P') := rfl
      rw [this, hs t P' hP', smul_smul, inv_mul_cancel₀ (hlam t), one_smul]
    · obtain ⟨P', hc, hne⟩ := hconv
      refine ⟨P', fun h0 => hne t₀ ?_, hc⟩
      have h1 : s P' ∈ K := (Submodule.Quotient.mk_eq_zero K).1 h0
      have h2 : X.I ψ θ t₀ (s P') = 0 := h1
      rw [hs t₀ P' (hc t₀)] at h2
      exact (smul_eq_zero.1 h2).resolve_left (hlam t₀)

end GlobalTheory.StageFactor

open GlobalTheory.StageFactor

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleConstantNormalized
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.BotFormula.root_unit {ζ : ℂ} {n : ℕ} (hn : 0 < n) (h : ζ ^ n = 1) :
    ζ ≠ 0 ∧ ζ ∈ Qbar ∧ ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), ‖lamC lam ζ‖ = 1 := by
  have hQ : ζ ∈ Qbar := by
    have : IsIntegral ℚ ζ := IsIntegral.of_pow hn (h ▸ isIntegral_one)
    exact mem_algebraicClosure_iff.2 this.isAlgebraic
  refine ⟨fun e => by simp [e, hn.ne'] at h, hQ, fun p _ lam => ?_⟩
  have h2 : (⟨ζ, hQ⟩ : Qbar) ^ n = 1 := Subtype.ext (by simpa using h)
  have h3 : lamC lam ζ = lam ⟨ζ, hQ⟩ := by simp [lamC, hQ]
  have h4 : ‖lam ⟨ζ, hQ⟩‖ ^ n = 1 := by rw [← norm_pow, ← map_pow, h2, map_one, norm_one]
  rw [h3]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h4
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonvanishingFactorStage
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SqCompare

theorem gBig_three {Q₁ Q₂ Q₃ Q : GP} (h₁ : GBig Q₁) (h₂ : GBig Q₂) (h₃ : GBig Q₃)
    (H : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Q₁ G μ₀ C x b → Q₂ G μ₀ C x b → Q₃ G μ₀ C x b → Q G μ₀ C x b) : GBig Q := by
  obtain ⟨F₁, h₁⟩ := h₁
  obtain ⟨F₂, h₂⟩ := h₂
  obtain ⟨F₃, h₃⟩ := h₃
  refine ⟨max F₁ (max F₂ F₃), fun ε CF hCF => ?_⟩
  obtain ⟨C₁, x₁, k₁⟩ := h₁ ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨C₂, x₂, k₂⟩ := h₂ ε CF (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCF)
  obtain ⟨C₃, x₃, k₃⟩ := h₃ ε CF (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCF)
  refine ⟨max C₁ (max C₂ C₃), max x₁ (max x₂ x₃), fun C hC D large₂ he hx hR T Lc μ₀ hL G => H G μ₀ C _ _ ?_ ?_ ?_⟩
  · exact k₁ C (le_trans (le_max_left _ _) hC) D large₂ he (le_trans (le_max_left _ _) hx) hR T Lc μ₀ hL G
  · exact k₂ C (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC) D large₂ he
      (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx) hR T Lc μ₀ hL G
  · exact k₃ C (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC) D large₂ he
      (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx) hR T Lc μ₀ hL G

end GlobalTheory.SqCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPIsogPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES.ValExt


open GlobalTheory.DrinLev.HT.HeckePt GlobalTheory.CechPic in
theorem isPIsog_pull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N c : ℕ) (S S' : Scheme.{0}) (σ : S ⟶ Sp R) (σ' : S' ⟶ Sp R) (f : S' ⟶ S) (o o' : Obj b N σ) (o₁ o₁' : Obj b N σ') (m : ObjMap o₁ o f) (m' : ObjMap o₁' o' f) (ψ : o.A ⟶ o'.A), IsPIsog c o o' ψ → ∃ ψ₁ : o₁.A ⟶ o₁'.A, IsPIsog c o₁ o₁' ψ₁ ∧ m.φ ≫ ψ.left = ψ₁.left ≫ m'.φ := by
  intro p _ D R _ b N c S S' σ σ' f o o' o₁ o₁' m m' ψ hψ
  obtain ⟨hk, hmon, hlin, heta, ⟨hP⟩, ψ', hmon', h₁, h₂⟩ := hψ
  haveI := hmon
  haveI := hmon'
  have e : m.φ ≫ ψ.left = (pullMor m.cart m'.cart ψ).left ≫ m'.φ := (pullMor_left m.cart m'.cart ψ).symm
  refine ⟨pullMor m.cart m'.cart ψ, ⟨hk, isMonHom_pullMor _ _ _, fun a => ?_, fun y => ?_, ⟨?_⟩,
    pullMor m'.cart m.cart ψ', isMonHom_pullMor _ _ _, pullMor_comp_eq_pow m.cart m'.cart ψ ψ' c h₁,
    pullMor_comp_eq_pow m'.cart m.cart ψ' ψ c h₂⟩, e⟩
  · apply ext_of_left m'.cart
    rw [Over.comp_left, Over.comp_left, Category.assoc, ← e, ← Category.assoc, m.act, Category.assoc,
      ← Over.comp_left, hlin a, Over.comp_left, Category.assoc, m'.act, ← Category.assoc, ← Category.assoc, e]
  · apply ext_of_left m'.cart
    rw [Over.comp_left, Category.assoc, ← e, ← Category.assoc, m.eta, m'.eta, Category.assoc, ← Over.comp_left,
      ← heta y]
  · have hsq := PIsogExt.isSquare_square_compatible_homs m.sq m'.sq e
    have hcL : ∀ {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) (h : (Hecke.lbPow L c).IsLB), cls _ h = c • cls L hL :=
      fun {X} L hL h => (cls_linComb (L := L) hL (fun _ => 𝟙 X) (fun _ => 1) h).trans (by simp [pull_id])
    have e1 := (cls_eq_iff o₁'.isLB (pull_isLB o'.isLB _)).2 m'.pol
    have e2 := (cls_eq_iff o₁.isLB (pull_isLB o.isLB _)).2 m.pol
    have e3 : cls (Hecke.lbPow o.P c) (LB.isLB_linComb o.isLB _ _) = cls (o'.P.pull (sq2 ψ)) (pull_isLB o'.isLB _) :=
      (cls_eq_iff _ _).2 hP
    refine (cls_eq_iff (LB.isLB_linComb o₁.isLB _ _) (pull_isLB o₁'.isLB _)).1 ?_
    refine (hcL o₁.P o₁.isLB _).trans ?_
    rw [e2, cls_pull o.isLB, ← map_nsmul, ← hcL o.P o.isLB (LB.isLB_linComb o.isLB _ _), e3,
      cls_pull o'.isLB, ← pull_comp, hsq, pull_comp, ← cls_pull o'.isLB _ (pull_isLB o'.isLB _), ← e1]
    all_goals rw [← cls_pull o₁'.isLB]

theorem of_ext (hext : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (c : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (v : Sp V ⟶ Sp R) (o : Obj b N v) (o₀ o₀' : Obj b N (spMap (algebraMap V (FractionRing V)) ≫ v)) (m : ObjMap o₀ o (spMap (algebraMap V (FractionRing V)))) (ψ₀ : o₀.A ⟶ o₀'.A), IsPIsog c o₀ o₀' ψ₀ → ∃ (o' : Obj b N v) (m' : ObjMap o₀' o' (spMap (algebraMap V (FractionRing V)))) (ψ : o.A ⟶ o'.A), IsPIsog c o o' ψ ∧ m.φ ≫ ψ.left = ψ₀.left ≫ m'.φ) : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∀ (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs gt : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → gt ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = t₀ → IsFinite gs → Etale gs → IsFinite gt → Etale gt → IsPIsog c o₀ o₀' ψ₀ → IsTj r w j o₀ o₀' ψ₀ → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (y : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y = x ≫ s₀ → ∃ z : Sp V ⟶ M.X, spMap (algebraMap V K) ≫ z = x ≫ t₀ := by
  intro p _ D R _ _ _ _ b N hN hNp _ r w j c _ _ _ _ _ M Y₀ s₀ t₀ gs gt o₀ o₀' ms₀ mt₀ ψ₀ hst _ _ _ _ _ _ hψ _ V K _ _ _ _ _ _ y x hxy
  let eK : K →+* FractionRing V := (IsLocalization.algEquiv (nonZeroDivisors V) K (FractionRing V)).toRingEquiv.toRingHom
  have heK : eK.comp (algebraMap V K) = algebraMap V (FractionRing V) := by
    ext a; exact (IsLocalization.algEquiv (nonZeroDivisors V) K (FractionRing V)).commutes a
  let kF : Sp (FractionRing V) ⟶ Sp V := spMap (algebraMap V (FractionRing V))
  let x' : Sp (FractionRing V) ⟶ Y₀ := spMap eK ≫ x
  have hk : kF = spMap eK ≫ spMap (algebraMap V K) := by
    simp only [kF, spMap, ← heK, CommRingCat.ofHom_comp, Spec.map_comp]
  have hxy' : kF ≫ y = x' ≫ s₀ := by rw [hk, Category.assoc, hxy]; rfl
  obtain ⟨o, ⟨my⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N M.X (Sp V) M.s y M.univ
  obtain ⟨oK, ⟨mK⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N (Sp V) (Sp (FractionRing V)) (y ≫ M.s) kF o
  have m1 : ObjMap oK M.univ (x' ≫ s₀) := hxy' ▸ GlobalTheory.UPel.HT.ObjMapComp.comp mK my
  obtain ⟨n₀, -⟩ := GlobalTheory.HTSympCover.exists_objMap_cancel_φ m1 ms₀
  have key : ∀ σ : Sp (FractionRing V) ⟶ Sp R, x' ≫ (s₀ ≫ M.s) = σ → ∃ o' : Obj b N σ, Nonempty (ObjMap o' o₀' x') := by
    rintro σ rfl
    exact GlobalTheory.HTPull.exists_objMap_pull p D R b N Y₀ (Sp (FractionRing V)) (s₀ ≫ M.s) x' o₀'
  obtain ⟨oK', ⟨n₀'⟩⟩ := key (kF ≫ (y ≫ M.s)) (by rw [← Category.assoc, ← hxy', Category.assoc])
  obtain ⟨ψK, hψK, -⟩ := isPIsog_pull p D R b N c Y₀ (Sp (FractionRing V)) (s₀ ≫ M.s) (kF ≫ (y ≫ M.s)) x' o₀ o₀' oK oK' n₀ n₀' ψ₀ hψ
  obtain ⟨o', m', -, -, -⟩ := hext p D R b N hN hNp c V (y ≫ M.s) o oK oK' mK ψK hψK
  obtain ⟨z, ⟨hz, ⟨mz⟩⟩, -⟩ := M.rep (Sp V) (y ≫ M.s) o'
  refine ⟨z, ?_⟩
  obtain ⟨f, -, huniq⟩ := M.rep (Sp (FractionRing V)) (kF ≫ (y ≫ M.s)) oK'
  have e1 := huniq (kF ≫ z) ⟨by rw [Category.assoc, hz], ⟨GlobalTheory.UPel.HT.ObjMapComp.comp m' mz⟩⟩
  have e2 := huniq (x' ≫ t₀) ⟨by rw [Category.assoc, ← hst, ← Category.assoc, ← hxy', Category.assoc],
    ⟨GlobalTheory.UPel.HT.ObjMapComp.comp n₀' mt₀⟩⟩
  have e3 : spMap eK ≫ (spMap (algebraMap V K) ≫ z) = spMap eK ≫ (x ≫ t₀) := by
    rw [← Category.assoc, ← hk, e1, ← e2, Category.assoc]
  haveI : IsIso (spMap eK) := by
    let e := (IsLocalization.algEquiv (nonZeroDivisors V) K (FractionRing V)).toRingEquiv
    have h1 : IsIso (CommRingCat.ofHom eK) := (RingEquiv.toCommRingCatIso e).isIso_hom
    exact inferInstanceAs (IsIso (Spec.map (CommRingCat.ofHom eK)))
  exact (cancel_epi (spMap eK)).1 e3

end GlobalTheory.UPel.HT.ES.ValExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPIsogenyTargetOfPointPairFieldExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPIsogenyTargetOfPointPairFieldExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES.CorrQF

open GlobalTheory.DrinLev.HT.HeckePt GlobalTheory.CechPic

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

private theorem cls_lbPow_eq_nsmul {X : Scheme} {L : LB X} (hL : L.IsLB) (c : ℕ) (h : (Hecke.lbPow L c).IsLB) :
    cls (Hecke.lbPow L c) h = c • cls L hL := by
  refine (cls_linComb hL _ _ h).trans ?_
  simp [pull_id]

theorem isPIsog_pullMor {S S' : Scheme.{0}} {s : S ⟶ Sp R} {f : S' ⟶ S} {o o' : Obj b N s}
    {o₁ o₁' : Obj b N (f ≫ s)} (n : ObjMap o₁ o f) (n' : ObjMap o₁' o' f) {c : ℕ} {ψ : o.A ⟶ o'.A}
    (hψ : IsPIsog c o o' ψ) : IsPIsog c o₁ o₁' (pullMor n.cart n'.cart ψ) := by
  obtain ⟨hc, hmon, hact, heta, ⟨hpol⟩, ψ', hmon', h1, h2⟩ := hψ
  haveI := hmon
  haveI := hmon'
  have hl := pullMor_left n.cart n'.cart ψ
  set pm := pullMor n.cart n'.cart ψ with hpm
  refine ⟨hc, isMonHom_pullMor _ _ _, ?_, ?_, ?_, pullMor n'.cart n.cart ψ', isMonHom_pullMor _ _ _,
    pullMor_comp_eq_pow _ _ _ _ _ h1, pullMor_comp_eq_pow _ _ _ _ _ h2⟩
  · intro c'
    apply ext_of_left n'.cart
    have e := congrArg Over.Hom.left (hact c')
    simp only [Over.comp_left] at e
    simp only [Over.comp_left, Category.assoc, hl, reassoc_of% hl, reassoc_of% (n.act c'), n'.act, e]
  · intro x
    apply ext_of_left n'.cart
    have e := congrArg Over.Hom.left (heta x)
    simp only [Over.comp_left] at e
    simp only [Over.comp_left, Category.assoc, hl, n'.eta, reassoc_of% (n.eta x), e]
  · have hsq : n.φ₂ ≫ sq2 ψ = sq2 pm ≫ n'.φ₂ := PIsogExt.isSquare_square_compatible_homs n.sq n'.sq hl.symm
    have hA : (Hecke.lbPow o₁.P c).IsLB := LB.isLB_linComb o₁.isLB _ _
    have hB : (o₁'.P.pull (sq2 pm)).IsLB := pull_isLB o₁'.isLB _
    have hX : (Hecke.lbPow o.P c).IsLB := LB.isLB_linComb o.isLB _ _
    refine ⟨(cls_eq_iff hA hB).1 ?_⟩
    have e1 := (cls_eq_iff o₁.isLB (pull_isLB o.isLB n.φ₂)).2 n.pol
    have e1' := (cls_eq_iff o₁'.isLB (pull_isLB o'.isLB n'.φ₂)).2 n'.pol
    have e0 : c • cls o.P o.isLB = pull (sq2 ψ) (cls o'.P o'.isLB) := by
      rw [← cls_lbPow_eq_nsmul o.isLB c hX, ← cls_pull o'.isLB (sq2 ψ) (pull_isLB o'.isLB _)]
      exact (cls_eq_iff hX _).2 hpol
    rw [cls_pull o.isLB] at e1
    rw [cls_pull o'.isLB] at e1'
    rw [cls_lbPow_eq_nsmul o₁.isLB c hA, cls_pull o₁'.isLB, e1, e1', ← pull_comp, ← hsq, pull_comp, ← e0,
      map_nsmul]

theorem isogTarget_spMap : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ)
    (M : Model b N) (c : ℕ) (k L : Type) [Field k] [Field L] (j : k →+* L) (ξ ζ : Sp k ⟶ M.X),
    CorrQF.IsogTarget M c ξ ζ → CorrQF.IsogTarget M c (spMap j ≫ ξ) (spMap j ≫ ζ) := by
  intro p _ D R _ b N M c k L _ _ j ξ ζ h
  obtain ⟨hs, o, o', ψ, ⟨m⟩, ⟨m'⟩, hψ⟩ := h
  obtain ⟨o₁, ⟨n⟩⟩ := HTPull.exists_objMap_pull p D R b N (Sp k) (Sp L) (ξ ≫ M.s) (spMap j) o
  obtain ⟨o₁', ⟨n'⟩⟩ := HTPull.exists_objMap_pull p D R b N (Sp k) (Sp L) (ξ ≫ M.s) (spMap j) o'
  have key : ∀ (w : Sp L ⟶ Sp R), spMap j ≫ ξ ≫ M.s = w →
      ∃ (a a' : Obj b N w) (φ : a.A ⟶ a'.A), Nonempty (ObjMap a M.univ (spMap j ≫ ξ)) ∧
        Nonempty (ObjMap a' M.univ (spMap j ≫ ζ)) ∧ IsPIsog c a a' φ := by
    intro w hw
    subst hw
    exact ⟨o₁, o₁', _, ⟨n.comp m⟩, ⟨n'.comp m'⟩, isPIsog_pullMor n n' hψ⟩
  obtain ⟨a, a', φ, ha, ha', hφ⟩ := key _ (Category.assoc _ _ _).symm
  exact ⟨by simp only [Category.assoc, hs], a, a', φ, ha, ha', hφ⟩

end GlobalTheory.UPel.HT.ES.CorrQF
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPIsogenyTargetOfPointPairFieldExtensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPIsogenyTargetOfPointPair_field_extension : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (M : Model b N) (c : ℕ) (k L : Type) [Field k] [Field L] (j : k →+* L) (ξ ζ : Sp k ⟶ M.X), CorrQF.IsogTarget M c ξ ζ → CorrQF.IsogTarget M c (spMap j ≫ ξ) (spMap j ≫ ζ) := by
  first | (exact @GlobalTheory.UPel.HT.ES.CorrQF.isogTarget_spMap) | (exact GlobalTheory.UPel.HT.ES.CorrQF.isogTarget_spMap) | (intros; apply GlobalTheory.UPel.HT.ES.CorrQF.isogTarget_spMap  <;> assumption)
end
end
