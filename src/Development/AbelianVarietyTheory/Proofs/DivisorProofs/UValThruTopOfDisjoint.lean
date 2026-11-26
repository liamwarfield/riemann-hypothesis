module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.BaseChangeMapRingAct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentImageDegreeBetweenOfProportionality
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformisationComponentsCovolumeEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankComponentWeightInvariance
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationMultiplicityWeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFiniteFreeFinrankLeFourMulDim
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChooseMulComponentDegreeLeDimension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorPeriodDefectIsCocycle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightConditionsAtIndex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BinomialFlagDimensionDegreeBound

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UValThruTopOfDisjoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}

def UValThru (Xo : Moduli D l) (c : Coeff l) {S T : Scheme.{0}} (i : Xo.XF c ⟶ T) (π : S ⟶ T) (A : Set S)
    (φ : InvFun (𝓞 E)) (J : S.IdealSheafData) (d : ℕ) : Prop :=
  ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ →
    ∀ (χ : Sp W ⟶ S) (y : Sp (FractionRing W) ⟶ Xo.XF c), y ≫ i = jK W ≫ χ ≫ π → χ (closedPoint W) ∈ A →
    ∀ (t : SAB H (Sp W)) (tK : SAB H (Sp (FractionRing W))), Nonempty (SABMap tK t (jK W)) →
      Nonempty (SABMap tK Xo.univ.t (y ≫ pullback.fst _ _)) → ∀ P : PELUnif (maximalIdeal W) t,
      ∀ be ∈ levelForms H 1 P.D.toPre.X, IsMonomial P.D.toPre ![ϖ] ![be] →
        ∃ n : ℕ, (n : ℝ) = d * φ.evalZ be ∧ idlAlong J χ = Ideal.span {ϖ ^ n}

variable {Xo : Moduli D l} {c : Coeff l}

theorem uValThru_top_of_disjoint {S : Scheme.{0}} {i : Xo.XF c ⟶ S} {A : Set S} (hA : IsOpen A)
    (hd : A ∩ Set.range i = ∅) (φ : InvFun (𝓞 E)) (d : ℕ) : UValThru Xo c i (𝟙 S) A φ ⊤ d := by
  intro W _ _ _ _ ϖ _ χ y hy hA' _ _ _ _ _ _ _ _
  exfalso
  let g : Sp (FractionRing W) := closedPoint (FractionRing W)
  have hsp : (jK W) g ⤳ closedPoint W := IsLocalRing.specializes_closedPoint _
  have hmem : χ ((jK W) g) ∈ A := (hsp.map χ.continuous).mem_open hA hA'
  have hrange : χ ((jK W) g) ∈ Set.range i := ⟨y g, by
    have := congrArg (fun f => f.base g) hy
    simpa using this⟩
  have : χ ((jK W) g) ∈ A ∩ Set.range i := ⟨hmem, hrange⟩
  rw [hd] at this
  exact this

theorem exists_uValOn_of_pieces {S : Scheme.{0}} (i : Xo.XF c ⟶ S) (φ : InvFun (𝓞 E)) {ι : Type} [Fintype ι]
    (A : ι → Set S) (J : ι → S.IdealSheafData) (d : ι → ℕ) (huniq : ∀ x, ∃! k, x ∈ A k) (hd : ∀ k, 1 ≤ d k)
    (hsupp : ∀ k, ∀ x ∈ (J k).support, x ∈ A k ∧ x ∉ Set.range i)
    (hv : ∀ k, UValThru Xo c i (𝟙 S) (A k) φ (J k) (d k)) :
    ∃ (d' : ℕ) (J' : S.IdealSheafData), 1 ≤ d' ∧ (∀ x ∈ J'.support, x ∉ Set.range i) ∧ UValOn Xo c i φ J' d' := by
  have hdvd : ∀ k, d k ∣ ∏ k, d k := fun k => Finset.dvd_prod_of_mem (s := Finset.univ) d (Finset.mem_univ k)
  have htop : ∀ k x, x ∉ A k → FinalTheorems.stalkId (J k) x = ⊤ := fun k x hx =>
    GlobalTheory.Vanishing.stalkId_eq_top (J k) fun hs => hx (hsupp k x hs).1
  refine ⟨∏ k, d k, ∏ k, J k ^ ((∏ k, d k) / d k), ?_, ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun k _ => by have := hd k; omega)
  · intro x hx
    obtain ⟨k, hk, -⟩ := huniq x
    by_cases hs : x ∈ (J k).support
    · exact (hsupp k x hs).2
    · exfalso
      refine (mem_support_iff_stalkId _ x).1 hx ?_
      rw [stalkId_prodPow, ← Ideal.one_eq_top]
      refine Finset.prod_eq_one fun k' _ => ?_
      by_cases e : k' = k
      · subst e; rw [GlobalTheory.Vanishing.stalkId_eq_top (J k') hs, ← Ideal.one_eq_top, one_pow]
      · rw [htop k' x fun h => e ((huniq x).unique h hk), ← Ideal.one_eq_top, one_pow]
  · intro W _ _ _ hW ϖ hϖ χ y hy t tK h1 h2 P be hbe hmono
    obtain ⟨k, hk, -⟩ := huniq (χ (closedPoint W))
    obtain ⟨a, ha, hJ⟩ := hv k W hW ϖ hϖ χ y (by rw [Category.comp_id]; exact hy) hk t tK h1 h2 P be hbe hmono
    refine ⟨(∏ k, d k) / d k * a, ?_, ?_⟩
    · have hd0 : (d k : ℝ) ≠ 0 := by have := hd k; positivity
      rw [Nat.cast_mul, Nat.cast_div (hdvd k) hd0, ha]
      field_simp
    · unfold idlAlong at hJ ⊢
      rw [stalkId_prodPow, Finset.prod_eq_single k, Ideal.map_pow, hJ, Ideal.span_singleton_pow, ← pow_mul, mul_comm]
      · intro k' _ e
        rw [htop k' _ fun h => e ((huniq _).unique h hk), ← Ideal.one_eq_top, one_pow]
      · intro h; exact absurd (Finset.mem_univ k) h

end GlobalTheory.UPoinc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeMulNFiniteFlatSurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeMulNFiniteFlatSurjective
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB mulN)
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
open GlobalTheory.DeRham (spOver)
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.MulFlatSurj

theorem mulN_eq_pow {S : Scheme.{0}} (G : Over S) [GrpObj G] (n : ℕ) : mulN G n = (𝟙 G) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, ← ih]; rfl

theorem finite_flat_surjective_mulN : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A],
    IsAbelianScheme A → ∀ n : ℕ, 0 < n →
      IsFinite (mulN A n).left ∧ Flat (mulN A n).left ∧ Surjective (mulN A n).left := by
  intro R _ A _ hA n hn
  have hc := hA.comm
  obtain ⟨h1, h2⟩ := GlobalTheory.AbTorsionAnyBase.isFinite_and_flat_mulA (Sp R) A hA n hn
  have e : mulN A n = ReciprocityTheory.ChartRestriction.G.Out.mulA A n := mulN_eq_pow A n
  rw [e]
  refine ⟨h1, h2, GlobalTheory.AbLaw.MulN.surjective_of_geomFibres _ fun K _ _ t => ?_⟩
  have hf : IsFinite ((Over.pullback t).map (ReciprocityTheory.ChartRestriction.G.Out.mulA A n)).left :=
    MorphismProperty.of_isPullback (P := @IsFinite) (GlobalTheory.AbLaw.MulN.isPullback_baseChange t _) h1
  rw [GlobalTheory.MulFiniteFlat.pullback_map_mulA] at hf ⊢
  have hB := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback t A hA
  have hBc := hB.comm
  exact (GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K _
    hB _ (GlobalTheory.AbLaw.MulN.isMonHom_mulA _ n) hf).2

end GlobalTheory.MulFlatSurj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeMulNFiniteFlatSurjectiveStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB mulN)
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
open GlobalTheory.DeRham (spOver)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_mulN_finite_flat_surjective : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ n : ℕ, 0 < n → IsFinite (mulN A n).left ∧ Flat (mulN A n).left ∧ Surjective (mulN A n).left := by
  first | exact @GlobalTheory.MulFlatSurj.finite_flat_surjective_mulN | exact GlobalTheory.MulFlatSurj.finite_flat_surjective_mulN | (intros; apply GlobalTheory.MulFlatSurj.finite_flat_surjective_mulN <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterGroupFinrankLeMinSignatureUnitaryTrait
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterGroupFinrankLeMinSignatureUnitaryTrait
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.UTrait

theorem finrank_le_min : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : UTrait Xo c),
    Module.finrank (𝓞 E) T.P.D.toPre.X ≤ min Dw.p Dw.q := by
  intro E _ _ _ H Dw l Xo c T
  obtain ⟨hdvr, -, hch⟩ := T.cdvr
  haveI := hdvr
  haveI := hch
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := T.gen
  let K := AlgebraicClosure (FractionRing T.V)
  let g : FractionRing T.V →+* K := algebraMap (FractionRing T.V) K
  let f : T.V →+* K := g.comp (algebraMap T.V (FractionRing T.V))
  have hf : Function.Injective f :=
    (algebraMap (FractionRing T.V) K).injective.comp (IsFractionRing.injective T.V (FractionRing T.V))
  haveI : CharZero K := ⟨fun a b h => Nat.cast_injective (R := T.V) (hf (by simpa using h))⟩
  let x' : Sp K ⟶ Xo.X := spMap g ≫ T.y ≫ pullback.fst _ _
  obtain ⟨β₀, hβ₀⟩ := Spec.map_surjective (x' ≫ Xo.s)
  have hβ : x' ≫ Xo.s = spMap β₀.hom := hβ₀.symm
  have hdet := (Xo.univ.geom K x' β₀.hom hβ).1
  have hr : (β₀.hom (baseKA l).ρ) ^ 2 = -(H.d : K) := by
    rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
  have hjK : spMap g ≫ jK T.V = spMap f := by
    show Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    rfl
  have bound : ∀ (τ : 𝓞 E →+* K) (N : ℕ), LieMult Xo.univ.t.act x' τ N →
      Module.finrank (𝓞 E) T.P.D.toPre.X ≤ N := by
    intro τ N hN
    have h₅ := (GlobalTheory.lieMult_iff_of_isGrpPullback m₂.cart tK.act Xo.univ.t.act m₂.act (spMap g) τ N).2 hN
    have h₆ := (GlobalTheory.lieMult_iff_of_isGrpPullback m₁.cart tK.act T.t.act m₁.act (spMap g) τ N).1 h₅
    rw [hjK] at h₆
    obtain ⟨n, -, hn⟩ := GlobalTheory.CharRank.lieMult_unif_loc H T.V T.t T.P K f hf τ N h₆
    omega
  obtain ⟨τ₁, τ₂, h₁, h₂⟩ := GlobalTheory.CharRank.exists_chars H K _ hr
  exact le_min (bound τ₁ _ ((hdet τ₁).1 h₁)) (bound τ₂ _ ((hdet τ₂).2 h₂))

end GlobalTheory.UPoinc.UTrait
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterGroupFinrankLeMinSignatureUnitaryTraitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_group_finrank_le_min_signature_unitary_trait : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : UTrait Xo c), Module.finrank (𝓞 E) T.P.D.toPre.X ≤ min Dw.p Dw.q := by
  first | exact @GlobalTheory.UPoinc.UTrait.finrank_le_min | exact GlobalTheory.UPoinc.UTrait.finrank_le_min | (intros; apply GlobalTheory.UPoinc.UTrait.finrank_le_min <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltGraded
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowDat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def perp (D : Datum H) (Z : Submodule (𝓞 E) D.La) : Submodule (𝓞 E) D.La where
  carrier := {x | ∀ z ∈ Z, D.EF x z = 0}
  zero_mem' := by intro z _; simp
  add_mem' := by
    intro x y hx hy z hz
    show D.EF (x + y) z = 0
    rw [map_add (f := _), LinearMap.add_apply, hx z hz, hy z hz, add_zero]
  smul_mem' := by
    intro a x hx z hz
    show D.EF (a • x) z = 0
    rw [D.adj]
    exact hx _ (Z.smul_mem _ hz)

def IsIsoSat (D : Datum H) (Z : Submodule (𝓞 E) D.La) : Prop :=
  Z ≤ perp D Z ∧ ∀ (n : ℕ) (x : D.La), n ≠ 0 → n • x ∈ Z → x ∈ Z

def IsLower (D D' : Datum H) (Z : Submodule (𝓞 E) D.La) (f : perp D Z →ₗ[𝓞 E] D'.La) : Prop :=
  Function.Surjective f ∧ (∀ x, f x = 0 ↔ (x : D.La) ∈ Z) ∧ ∀ x y, D'.EF (f x) (f y) = D.EF x y

def lowLevel (l : Level H) : Level H :=
  { l with A := l.M', A_pos := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos }

theorem ka_le (l : Level H) (c : Coeff l) : KA (lowLevel l) ≤ c.F := by
  unfold KA
  rw [IntermediateField.adjoin_le_iff]
  intro x hx
  rcases hx with rfl | hx
  · exact c.le (IntermediateField.subset_adjoin _ _ (by simp))
  · rw [Set.mem_singleton_iff] at hx; subst hx; exact c.zeta_mem

end GlobalTheory.LowDat

namespace GlobalTheory.LowDat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

def lowS (C : UChart.Fam Xo c R) : Sp R ⟶ Sp (KA (lowLevel l)) :=
  spMap (C.b.comp (IntermediateField.inclusion (ka_le l c)).toRingHom)

def toF (C : UChart.Fam Xo c R) (F : Type) [Field F] [Algebra (FractionRing R) F] : c.F →+* F :=
  (algebraMap (FractionRing R) F).comp ((algebraMap R (FractionRing R)).comp C.b)

def XFLevel (C : UChart.Fam Xo c R) (tK : SAB H (Sp (FractionRing R))) (m1 : SABMap tK C.t (jK R))
    (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _)) (F : Type) [Field F] [Algebra (FractionRing R) F]
    (I : letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F) : Prop :=
  ((I.ζ l.M' : Fˣ) : F) = toF C F ⟨zeta l.M', c.zeta_mem⟩ ∧
  ∀ (k : ℕ) (a : Dw.La) (σ : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G),
    ((k = l.A ∧ σ = Xo.univ.etaA a) ∨
      (k = l.M ∧ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La) ∧ σ = Xo.univ.eta a)) →
    ∀ x : TFK (R := R) F ⟶ C.P.A.A, C.P.ToA F k (I.ev k a) x →
      ∃ g : Sp F ⟶ tK.G.left, g ≫ m1.φ = x.left ≫ C.P.U.gen.inv.left ≫ pullback.fst C.t.G.hom (jK R) ∧
        g ≫ m2.φ = jFK (R := R) F ≫ C.y ≫ pullback.fst _ _ ≫ σ.left

def FiltGraded (C : UChart.Fam Xo c R) (Z : Submodule (𝓞 E) Dw.La) (F : Type) [Field F] [Algebra (FractionRing R) F]
    (I : letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F) : Prop :=
  ∀ n, 0 < n → ∀ a, (∃ q : QkPt C.P.D.toPre F n, QkPt.Equiv C.P.D.toPre F (I.ev n a) q ∧ q.y = 0) ↔
    ∃ b ∈ perp Dw Z, ∃ e, a = b + n • e

abbrev LowTate (C : UChart.Fam Xo c R) (D' : Datum H) (o' : Obj D' (lowLevel l) (baseKA (lowLevel l)) (lowS C))
    (F : Type) [Field F] [Algebra (FractionRing R) F] :=
  TateIso D' F (Over.mk (jFK (R := R) F ≫ jK R) ⟶ o'.t.G) (fun a g => g ≫ o'.t.act.act a)
    (fun n g g' z => Out.WeilIs o'.t.G o'.t.PP.L n g g' (unitOn z))

def LowGraded (C : UChart.Fam Xo c R) (Z : Submodule (𝓞 E) Dw.La) (D' : Datum H) (f : perp Dw Z →ₗ[𝓞 E] D'.La)
    (o' : Obj D' (lowLevel l) (baseKA (lowLevel l)) (lowS C)) (φB : o'.t.G.left ⟶ C.P.D.toPre.P.A.left)
    (F : Type) [Field F] [Algebra (FractionRing R) F]
    (I : letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F) (I' : LowTate C D' o' F) : Prop :=
  (∀ n, I'.ζ n = I.ζ n) ∧
  (∀ w, toUnit _ ≫ o'.etaA w = I'.ev (lowLevel l).A w) ∧
  (∀ w ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D'.La), toUnit _ ≫ o'.eta w = I'.ev l.M w) ∧
  ∀ n, 0 < n → ∀ a : perp Dw Z, ∃ q : QkPt C.P.D.toPre F n,
    QkPt.Equiv C.P.D.toPre F (I.ev n a) q ∧ q.y = 0 ∧ q.g.b.left = (I'.ev n (f a)).left ≫ φB

end GlobalTheory.LowDat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionModHodgeFiltration
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionModHodgeFiltration
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HTSummand.LieMod

variable {R : Type} [CommRing R]

def epsIso : epsR R ≅ GlobalTheory.UPel.HT.epsPtR (𝟙 (Sp R)) := Over.isoMk (Iso.refl _) (by simp)

@[simp] lemma epsIso_hom_left : (epsIso (R := R)).hom.left = 𝟙 _ := rfl
@[simp] lemma epsIso_inv_left : (epsIso (R := R)).inv.left = 𝟙 _ := rfl

lemma one_left {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Scheme.{0}} (x : X ⟶ S) :
    (1 : Over.mk x ⟶ G).left = x ≫ η[G].left := by
  rw [Hom.one_def, Over.comp_left]
  congr 1

lemma comp_prod {S : Scheme.{0}} {G Y Z : Over S} [GrpObj G] (f : Z ⟶ Y) (l : List (Y ⟶ G)) :
    f ≫ l.prod = (l.map (f ≫ ·)).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [MonObj.comp_mul, ih]

lemma isLieImage_sum {A : Over (Sp R)} [GrpObj A] : ∀ (n : ℕ) (u : Fin n → HdR A) (w : Fin n → (epsR R ⟶ A)),
    (∀ i, IsLieImage (u i) (w i)) → IsLieImage (∑ i, u i) (List.ofFn w).prod
  | 0, u, w, _ => by simpa using (isLieImage_one_iff (A := A)).2 (zero_mem _)
  | n + 1, u, w, h => by
    rw [Fin.sum_univ_succ, List.ofFn_succ, List.prod_cons]
    exact (h 0).add (isLieImage_sum n _ _ fun i => h i.succ)

lemma isLieImage_eq {A : Over (Sp R)} [GrpObj A] (H : LieExact A) {h h' : HdR A} {v v' : epsR R ⟶ A}
    (e : IsLieImage h v) (e' : IsLieImage h' v') (hd : h - h' ∈ Fil A) : v = v' := by
  have k : IsLieImage (h' + (h - h')) (v' * 1) := e'.add (isLieImage_one_iff.2 hd)
  rw [add_sub_cancel, _root_.mul_one] at k
  exact (H.1 h).unique e k

lemma tan_of {A : Over (Sp R)} [GrpObj A] {v : epsR R ⟶ A} (hv : IsTangent v) :
    spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ (epsIso.inv ≫ v).left =
      (1 : Over.mk (𝟙 (Sp R)) ⟶ A).left := by
  rw [one_left, Category.id_comp, Over.comp_left, epsIso_inv_left, Category.id_comp]
  exact hv

lemma tan_to {A : Over (Sp R)} [GrpObj A] {w : GlobalTheory.UPel.HT.epsPtR (𝟙 (Sp R)) ⟶ A}
    (hw : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ w.left = (1 : Over.mk (𝟙 (Sp R)) ⟶ A).left) :
    IsTangent (epsIso.hom ≫ w) := by
  rw [one_left, Category.id_comp] at hw
  show _ ≫ (epsIso.hom ≫ w).left = _
  rw [Over.comp_left, epsIso_hom_left, Category.id_comp]
  exact hw

end GlobalTheory.HTSummand.LieMod

namespace GlobalTheory.HTSummand


open LieMod in
theorem lie_mod_fil : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C₀ : Type) [CommRing C₀] [IsLocalRing C₀] (β : R →+* C₀) (s : Sp C₀ ⟶ Sp R), s = spMap β → ∀ (o₀ : GlobalTheory.UPel.HT.Obj b N s) (y : HdR o₀.A), GlobalTheory.HTSummand.crysAct (dp0 C₀) (𝟙 _) o₀.act (algebraMap (𝓞 D.F) D.O D.ω) y - β b.ρ • y ∈ Fil o₀.A → ∃ w : Fin D.a → HdR o₀.A, (∀ i (c : 𝓞 D.F), GlobalTheory.HTSummand.crysAct (dp0 C₀) (𝟙 _) o₀.act (algebraMap (𝓞 D.F) D.O c) (w i) - β (b.t i c) • w i ∈ Fil o₀.A) ∧ y - ∑ i, w i ∈ Fil o₀.A := by
  intro p _ D R _ b N C₀ _ _ β s hs o₀ y hy
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim C₀ o₀.A o₀.ab
  have H : LieExact o₀.A := (GlobalTheory.abelianDeRham.2.1 C₀ o₀.A g o₀.ab hg).1
  obtain ⟨v, hv, -⟩ := H.1 y
  set ωO := algebraMap (𝓞 D.F) D.O D.ω
  haveI := o₀.act.hom ωO
  have hω : v ≫ o₀.act.act ωO = GlobalTheory.GrpTangent.epsScale (β b.ρ) ≫ v :=
    isLieImage_eq H (hv.push (o₀.act.act ωO)) (hv.smul (β b.ρ)) hy
  have hx : 𝟙 (Sp C₀) ≫ s = spMap β := by rw [Category.id_comp, hs]
  have hvT : GlobalTheory.UPel.HT.IsTanScal o₀.act (𝟙 (Sp C₀)) ωO (β b.ρ) (epsIso.inv ≫ v) := by
    refine ⟨tan_of hv.1, ?_⟩
    rw [Category.assoc, Over.comp_left, hω, Over.comp_left, Over.comp_left, epsIso_inv_left, Category.id_comp,
      Category.id_comp, GlobalTheory.GrpTangent.epsScale_left]
  obtain ⟨w, hw, hprod⟩ := o₀.lie C₀ β (𝟙 (Sp C₀)) hx (epsIso.inv ≫ v) hvT
  have hwT : ∀ i, IsTangent (epsIso.hom ≫ w i) := fun i => tan_to (hw i 0).1
  choose u hu using fun i => H.2 _ (hwT i)
  refine ⟨u, fun i c => ?_, ?_⟩
  · haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c)
    have e : (epsIso.hom ≫ w i) ≫ o₀.act.act (algebraMap (𝓞 D.F) D.O c) =
        GlobalTheory.GrpTangent.epsScale (β (b.t i c)) ≫ epsIso.hom ≫ w i := by
      ext1
      simp only [Over.comp_left, epsIso_hom_left, Category.id_comp, GlobalTheory.GrpTangent.epsScale_left]
      rw [← Over.comp_left]
      exact (hw i c).2
    have k₁ := (hu i).push (o₀.act.act (algebraMap (𝓞 D.F) D.O c))
    rw [e] at k₁
    exact k₁.sub_mem ((hu i).smul (β (b.t i c)))
  · have k := isLieImage_sum D.a u _ hu
    have e : (List.ofFn fun i => epsIso.hom ≫ w i).prod = v := by
      rw [show (List.ofFn fun i => epsIso.hom ≫ w i) = (List.ofFn w).map (epsIso.hom ≫ ·) from
        List.map_ofFn.symm, ← comp_prod, ← hprod, Iso.hom_inv_id_assoc]
    rw [e] at k
    exact hv.sub_mem k

end GlobalTheory.HTSummand
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionModHodgeFiltrationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_lie_condition_mod_hodgeFiltration : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C₀ : Type) [CommRing C₀] [IsLocalRing C₀] (β : R →+* C₀) (s : Sp C₀ ⟶ Sp R), s = spMap β → ∀ (o₀ : GlobalTheory.UPel.HT.Obj b N s) (y : HdR o₀.A), GlobalTheory.HTSummand.crysAct (dp0 C₀) (𝟙 _) o₀.act (algebraMap (𝓞 D.F) D.O D.ω) y - β b.ρ • y ∈ Fil o₀.A → ∃ w : Fin D.a → HdR o₀.A, (∀ i (c : 𝓞 D.F), GlobalTheory.HTSummand.crysAct (dp0 C₀) (𝟙 _) o₀.act (algebraMap (𝓞 D.F) D.O c) (w i) - β (b.t i c) • w i ∈ Fil o₀.A) ∧ y - ∑ i, w i ∈ Fil o₀.A := by
  first | (exact @GlobalTheory.HTSummand.lie_mod_fil) | (exact GlobalTheory.HTSummand.lie_mod_fil) | (intros; apply GlobalTheory.HTSummand.lie_mod_fil  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankGrowthBoundSmallScale
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChooseAddLePowMulChooseAdd
open scoped BigOperators Matrix
open Polynomial

namespace GlobalTheory

private theorem choose_succ_mul_succ_eq_mul_choose (c n : ℕ) :
    (((c + (n + 1)).choose (n + 1) : ℕ) : ℝ) * ((n : ℝ) + 1)
      = ((c : ℝ) + n + 1) * (((c + n).choose n : ℕ) : ℝ) := by
  have h := Nat.add_one_mul_choose_eq (c + n) n
  have h' : (c + (n + 1)).choose (n + 1) * (n + 1) = (c + n + 1) * (c + n).choose n := by
    rw [show c + (n + 1) = c + n + 1 by ring]
    linarith
  exact_mod_cast h'

theorem choose_add_le_pow_mul_choose_add (a b : ℕ) (y : ℝ) (hy : 0 ≤ y)
    (h : (a : ℝ) ≤ b + y * (b + 1)) (n : ℕ) :
    (((a + n).choose n : ℕ) : ℝ) ≤ (1 + y) ^ n * (((b + n).choose n : ℕ) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hA := choose_succ_mul_succ_eq_mul_choose a n
    have hB := choose_succ_mul_succ_eq_mul_choose b n
    have hCa : (0 : ℝ) ≤ (((a + n).choose n : ℕ) : ℝ) := Nat.cast_nonneg _
    have hCb : (0 : ℝ) ≤ (((b + n).choose n : ℕ) : ℝ) := Nat.cast_nonneg _
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hlin : (a : ℝ) + n + 1 ≤ (1 + y) * ((b : ℝ) + n + 1) := by
      nlinarith [mul_nonneg hy hn]
    have hfac : (0 : ℝ) ≤ (1 + y) * ((b : ℝ) + n + 1) :=
      mul_nonneg (by linarith) (by positivity)
    have hpow : (0 : ℝ) ≤ (1 + y) ^ n * (((b + n).choose n : ℕ) : ℝ) :=
      mul_nonneg (pow_nonneg (by linarith) n) hCb
    rw [← mul_le_mul_iff_of_pos_right hpos]
    rw [hA, mul_assoc, hB]
    calc ((a : ℝ) + n + 1) * (((a + n).choose n : ℕ) : ℝ)
        ≤ ((1 + y) * ((b : ℝ) + n + 1)) * ((1 + y) ^ n * (((b + n).choose n : ℕ) : ℝ)) :=
          mul_le_mul hlin ih hCa hfac
      _ = (1 + y) ^ (n + 1) * (((b : ℝ) + n + 1) * (((b + n).choose n : ℕ) : ℝ)) := by ring

theorem exp_le_one_add_of_le_tenth (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1 / 10) :
    Real.exp x ≤ 1 + 53 / 50 * x := by
  have hx : |x| ≤ 1 := by rw [abs_of_nonneg h0]; linarith
  have hb := Real.exp_bound hx (n := 3) (by norm_num)
  have h2 := (abs_le.mp hb).2
  rw [abs_of_nonneg h0] at h2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h2
  norm_num at h2
  have hx2 : x ^ 2 ≤ x / 10 := by nlinarith
  have hx3 : x ^ 3 ≤ x / 100 := by nlinarith
  nlinarith

theorem choose_rank_ratio_le :
    ∀ (D T a : ℕ) (ρ : ℝ), 2 ≤ D → 20 * D ≤ T → 0 ≤ ρ → ρ ≤ 1 / 4 → (a : ℝ) ≤ ((T : ℝ) + D + 4) / (1 - ρ) → (D : ℝ) * (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)) ≤ 1 / 10 → (((a + D).choose D : ℕ) : ℝ) ≤ (1 + (7 * (D : ℝ) ^ 2 / T + 3 / 2 * D * ρ)) * (((T - 1).choose D : ℕ) : ℝ) := by
  intro D T a ρ hD hT hρ0 hρ1 ha hε
  have hD' : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hT' : (20 : ℝ) * D ≤ T := by exact_mod_cast hT
  have hTpos : (0 : ℝ) < T := by linarith
  have hbD : (T - 1 - D) + D = T - 1 := by omega
  have hbR : ((T - 1 - D : ℕ) : ℝ) = T - 1 - D := by
    have h3 : (T - 1 - D) + D + 1 = T := by omega
    have h := congrArg (fun k : ℕ => (k : ℝ)) h3
    push_cast at h
    linarith
  have hρ' : 0 < 1 - ρ := by linarith
  have hTD : 0 < (T : ℝ) - D := by linarith
  have hden : 0 < (1 - ρ) * ((T : ℝ) - D) := mul_pos hρ' hTD
  have hnum0 : (0 : ℝ) ≤ 2 * D + 5 + ρ * T := by nlinarith [mul_nonneg hρ0 hTpos.le]
  have hy0 : (0 : ℝ) ≤ (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)) := div_nonneg hnum0 hden.le
  have hyb : (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)) * (((T - 1 - D : ℕ) : ℝ) + 1)
      = (2 * D + 5 + ρ * T) / (1 - ρ) := by
    rw [hbR]
    field_simp
    ring
  have hab : (a : ℝ) ≤ ((T - 1 - D : ℕ) : ℝ)
      + (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)) * (((T - 1 - D : ℕ) : ℝ) + 1) := by
    rw [hyb, hbR]
    have key : ((T : ℝ) + D + 4) / (1 - ρ) ≤ (T - 1 - D) + (2 * D + 5 + ρ * T) / (1 - ρ) := by
      rw [div_le_iff₀ hρ', add_mul, div_mul_cancel₀ _ hρ'.ne']
      nlinarith [mul_nonneg hρ0 (by linarith : (0 : ℝ) ≤ D + 1)]
    linarith
  have h1 := choose_add_le_pow_mul_choose_add a (T - 1 - D) _ hy0 hab D
  rw [hbD] at h1
  have hC : (0 : ℝ) ≤ (((T - 1).choose D : ℕ) : ℝ) := Nat.cast_nonneg _
  have hDy : (D : ℝ) * ((2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)))
      = (D : ℝ) * (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)) := by ring
  have hε0 : (0 : ℝ) ≤ (D : ℝ) * (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)) := by
    rw [← hDy]; exact mul_nonneg (Nat.cast_nonneg _) hy0
  have hpow : (1 + (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D))) ^ D
      ≤ Real.exp ((D : ℝ) * (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D))) := by
    rw [← hDy, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith)
      (by linarith [Real.add_one_le_exp ((2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)))]) D
  have hexp := exp_le_one_add_of_le_tenth _ hε0 hε
  have hu : (57 / 80 : ℝ) * T ≤ (1 - ρ) * (T - D) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 4 - ρ) hTD.le]
  have hnum : (0 : ℝ) ≤ (D : ℝ) * (2 * D + 5 + ρ * T) := mul_nonneg (Nat.cast_nonneg _) hnum0
  have h2 : (D : ℝ) * (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D))
      ≤ (D : ℝ) * (2 * D + 5 + ρ * T) / ((57 / 80) * T) :=
    div_le_div_of_nonneg_left hnum (by positivity) hu
  have e1 : (D : ℝ) * (2 * D + 5 + ρ * T) / ((57 / 80) * T)
      = (80 / 57) * ((D : ℝ) * (2 * D + 5) / T) + (80 / 57) * ((D : ℝ) * ρ) := by
    field_simp
  have e2 : (D : ℝ) * (2 * D + 5) / T ≤ (9 / 2) * ((D : ℝ) ^ 2 / T) := by
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right (by nlinarith) hTpos.le
  have e3 : 7 * (D : ℝ) ^ 2 / T = 7 * ((D : ℝ) ^ 2 / T) := by ring
  have hq : (0 : ℝ) ≤ (D : ℝ) ^ 2 / T := by positivity
  have hdr : (0 : ℝ) ≤ (D : ℝ) * ρ := mul_nonneg (Nat.cast_nonneg _) hρ0
  have hfin : (1 + (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D))) ^ D
      ≤ 1 + (7 * (D : ℝ) ^ 2 / T + 3 / 2 * D * ρ) := by
    rw [e3]
    nlinarith
  calc (((a + D).choose D : ℕ) : ℝ)
      ≤ (1 + (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D))) ^ D * (((T - 1).choose D : ℕ) : ℝ) := h1
    _ ≤ (1 + (7 * (D : ℝ) ^ 2 / T + 3 / 2 * D * ρ)) * (((T - 1).choose D : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hfin hC

end GlobalTheory
end

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CovTop.HodgeSteps

theorem exists_jet_order (d T : ℕ) (ρ : ℝ) (hd : 2 ≤ d) (hT : 1000 * (d : ℝ) ^ 2 ≤ T) (h0 : 0 ≤ ρ)
    (hz : 7 * ((d : ℝ) ^ 2 / T + d * ρ) ≤ 1 / 2) :
    ∃ a : ℕ, ((T + d + 4 : ℕ) : ℝ) < (a + 1) * (1 - ρ) ∧
      (((a + d).choose d : ℕ) : ℝ) ≤ (1 + 7 * ((d : ℝ) ^ 2 / T + d * ρ)) * (((T - 1).choose d : ℕ) : ℝ) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hTd : 2000 * (d : ℝ) ≤ T := by nlinarith
  have hT0 : (0 : ℝ) < T := by linarith
  have h1 : 0 ≤ (d : ℝ) ^ 2 / T := by positivity
  have h2 : (d : ℝ) * ρ ≤ 1 / 14 := by linarith
  have h3 : ρ ≤ 1 / 28 := by nlinarith
  have h4 : 0 < 1 - ρ := by linarith
  refine ⟨⌊((T : ℝ) + d + 4) / (1 - ρ)⌋₊, ?_, ?_⟩
  · have := Nat.lt_floor_add_one (((T : ℝ) + d + 4) / (1 - ρ))
    rw [div_lt_iff₀ h4] at this
    push_cast
    exact this
  · refine (GlobalTheory.choose_rank_ratio_le d T _ ρ hd (by exact_mod_cast (by linarith : 20 * (d : ℝ) ≤ T)) h0 (by linarith)
      (Nat.floor_le (by positivity)) ?_).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    · rw [div_le_iff₀ (mul_pos h4 (by linarith))]
      have a1 : (d : ℝ) * ρ * T ≤ 1 / 14 * T := mul_le_mul_of_nonneg_right h2 hT0.le
      have a2 : 27 / 28 * (1999 / 2000 * (T : ℝ)) ≤ (1 - ρ) * (T - d) :=
        mul_le_mul (by linarith) (by linarith) (by positivity) h4.le
      nlinarith
    · have : 0 ≤ (d : ℝ) * ρ := by positivity
      rw [mul_div_assoc]
      linarith

theorem le_gap_bar {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (hp : 1 ≤ Dw.p) (hq : 1 ≤ Dw.q) (u : AllWt.Weight Dw) (τ : Psi H) (hu : Antitone (u τ)) (t : ℤ) :
    t ≤ gap (u τ + t • hodgeWt Dw τ) (Dw.p - 1) := by
  have h := hu (show (⟨Dw.p - 1, by omega⟩ : Fin (Dw.p + Dw.q)) ≤ ⟨Dw.p - 1 + 1, by omega⟩ from Nat.le_succ _)
  rw [gap, dite_eq_left (by omega)]
  simp only [hodgeWt, CompHt.barWt, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [if_pos (by omega), if_neg (by omega)]
  linarith

theorem bir_gap_le (d N : ℕ) (hd : 3 ≤ d) : (d + 3) ^ 2 + 2 * N ≤ (d + 3) * ((d + 1).choose 2 + 4 * N + d + 3) := by
  nlinarith [Nat.zero_le ((d + 1).choose 2), Nat.zero_le N]

end GlobalTheory.CovTop.HodgeSteps
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualLatticeDegreeNeg
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LKGeo

variable {p : ℕ} [Fact p.Prime]

def actAf (D : Datum p) (c : D.O) : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D) :=
  Module.End.baseChangeHom ℚ (AfP p) (VQ D) (actQ D c)

theorem actAf_tmul (D : Datum p) (c : D.O) (a : AfP p) (x : D.La) :
    actAf D c (a ⊗ₜ ((1 : ℚ) ⊗ₜ x)) = a ⊗ₜ ((1 : ℚ) ⊗ₜ (c • x)) := by
  show LinearMap.baseChange (AfP p) (actQ D c) (a ⊗ₜ ((1 : ℚ) ⊗ₜ x)) = _
  rw [LinearMap.baseChange_tmul, actQ, LinearMap.baseChange_tmul]
  rfl

theorem actAf_inAf (D : Datum p) (c : D.O) (x : D.La) : actAf D c (inAf D x) = inAf D (c • x) :=
  actAf_tmul D c 1 x

theorem actAf_mem_laHat (D : Datum p) (c : D.O) {v : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) :
    actAf D c v ∈ LaHat D := by
  induction hv using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, x, ha, rfl⟩ := hz
    rw [actAf_tmul]
    exact AddSubgroup.subset_closure ⟨a, c • x, ha, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add u w _ _ hu hw => rw [map_add]; exact add_mem hu hw
  | neg u _ hu => rw [map_neg]; exact neg_mem hu

theorem actG_actAf {D : Datum p} {G : HTGroup p} (L : Link D G) (g : G.GAf) (c : D.O)
    (v : AfP p ⊗[ℚ] VQ D) : L.actG g (actAf D c v) = actAf D c (L.actG g v) := by
  have key : ∀ z : AfP p ⊗[ℚ] G.C, Commute (actOn L.rep (AfP p) z) (actAf D c) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul r x =>
      have h1 : Commute (L.rep x) (actQ D c) := (L.rep_range (L.rep x)).1 ⟨x, rfl⟩ c
      simp only [actOn]
      refine Commute.mul_left ?_ ?_
      · exact Algebra.commute_algebraMap_left r _
      · exact h1.map (Module.End.baseChangeHom ℚ (AfP p) (VQ D))
    | add a b ha hb => rw [map_add (f := _)]; exact ha.add_left hb
  unfold Link.actG
  simp only [MonoidHom.coe_comp, Function.comp_apply]
  exact LinearMap.congr_fun (key _).eq v

end GlobalTheory.LKGeo

namespace GlobalTheory.LKGeo

variable {p : ℕ} [Fact p.Prime]

end GlobalTheory.LKGeo
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShareStatementOfKnownTheorems
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

namespace GlobalTheory.CovTop.ShareRowsNef

section Weights

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem antitone_of_gapGe (hp : 1 ≤ Dw.p) (hq : 1 ≤ Dw.q) {la : AllWt.Weight Dw} (h : GapGe 1 la) :
    (∀ τ, Antitone (la τ)) ∧ ∀ τ, 1 ≤ gap (la τ) (Dw.p - 1) := _root_.GlobalTheory.CovTop.DgShare.antitone_of_gapGe (la := la) hp hq h

theorem gapGe_of_wtBig {P : WtPar Dw} (h : WtBig P) : GapGe 1 P.u₁ ∧ GapGe 1 P.u₂ ∧ ∀ j, GapGe 1 (P.wt j) := _root_.GlobalTheory.CovTop.DgShare.gapGe_of_wtBig (P := P) h

theorem two_le_dimFlag (hp : 1 ≤ Dw.p) (hq : 1 ≤ Dw.q) (hf : 2 < Module.finrank ℚ E / 2) : 2 ≤ FlagTan.dimFlag Dw := by
  unfold FlagTan.dimFlag
  have : 1 ≤ (Dw.p + Dw.q).choose 2 := Nat.choose_pos (by omega)
  nlinarith

end Weights

end GlobalTheory.CovTop.ShareRowsNef

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepGoodReductionStatement
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CovTop.DeepGoodAll

theorem shiftG_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : shiftG Dw a n 0 = wtZ a n := by
  unfold shiftG
  rw [zero_smul]
  have : wtOf Dw (0 : AllWt.Weight Dw) 0 = 0 := by
    unfold wtOf
    ext x <;> simp
  rw [this, add_zero]

end GlobalTheory.CovTop.DeepGoodAll
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBCTrivSqZeroExt
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroCrys

theorem isBC_trivSqZeroExt : ∀ (k : Type) [Field k] (V : Type) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V]
    [IsCentralScalar k V] (A₀ : Over (Sp k)) [GrpObj A₀], IsAbelianScheme A₀ →
    ∀ (h2 : RingHom.ker (TrivSqZeroExt.fstHom k k V).toRingHom ^ 2 = 0)
      (m : GrpMor (dp0 k) (𝟙 _) A₀ (divided₂ h2) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀
        (algebraMap k (TrivSqZeroExt k V)) (𝟙 _) (Over.Hom.left (𝟙 A₀))), m.IsBC := by
  intro k _ V _ _ _ _ A₀ _ hA h2 m
  have := hA.smooth
  obtain ⟨g, hg⟩ := GlobalTheory.SerreDim.exists_dim_of_grpObj A₀
  have e : (𝟙 _ : Sp k ⟶ Sp k) = spMap (RingHom.id k) := (Cris.spMap_id k).symm
  have h := (GlobalTheory.CrysConn.isGrpPullback_refl A₀).congr e rfl
  have key : ∀ (t : Sp k ⟶ Sp k), t = spMap (RingHom.id k) →
      ∀ m : GrpMor (dp0 k) t A₀ (divided₂ h2) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀
        (algebraMap k (TrivSqZeroExt k V)) (𝟙 _) (Over.Hom.left (𝟙 A₀)), m.IsBC := by
    rintro _ rfl m
    exact GlobalTheory.CrysConn.isBC_of_lift GlobalTheory.T.abelianScheme_firstDeRham_structure hA hg (isDPNilpotent_bot k) Function.surjective_id
      ((RingHom.injective_iff_ker_eq_bot _).1 Function.injective_id) h (isDPNilpotent_squareZero _)
      (fun r ↦ ⟨TrivSqZeroExt.inl r, rfl⟩) rfl m (GlobalTheory.CrysConn.isGrpPullback_refl A₀)
  exact key _ e m

end GlobalTheory.SqZeroCrys
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsDeRhamPairing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsDeRhamPairing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.UPel.HT.CorrForm
open GlobalTheory.AbDual

theorem exists_isCorrForm_obj : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t), ∃ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ := by
  intro p _ D R _ b N _ _ k _ _ t o₀
  obtain ⟨g, hg⟩ := GlobalTheory.AbVarRelDim.exists_relDim k o₀.A o₀.ab
  have C := cupSquare_of_free GlobalTheory.abelianDeRham.1 (AbelianSchemeGerms.isAbelianScheme_tensor o₀.A o₀.A o₀.ab o₀.ab)
    (smooth_prod hg hg)
  exact exists_isCorrForm C o₀.isLB o₀.rig₁ o₀.rig₂

end GlobalTheory.UPel.HT.CorrForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsDeRhamPairingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_exists_deRham_pairing : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t), ∃ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ := by
  first | exact @GlobalTheory.UPel.HT.CorrForm.exists_isCorrForm_obj | exact GlobalTheory.UPel.HT.CorrForm.exists_isCorrForm_obj | (intros; apply GlobalTheory.UPel.HT.CorrForm.exists_isCorrForm_obj <;> assumption)
end
end
