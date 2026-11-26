module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFunctionalEquationSectionNonzeroClass
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpansionComponentsProportionalShiftMultiple
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GmResPull

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniformisationOfFunctionalEquationDegreeOn
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FunctionalEquationAllDegreesAlgebraicClosure
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecZeroOfPull
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU.SchurConst

theorem gs_zero {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs
  split_ifs with h
  · simp only [map_zero]
  · rfl

theorem sec_zero_of_val {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : ∀ y J, Good L y J → sval s (𝟙 Y) y J = 0)
    (j : K → L.ι) : s.f j = 0 := by
  refine fn_ext fun y hy => ?_
  obtain ⟨J, hJ, e⟩ := sval_trans hL s y j hy
  rw [h y J hJ, mul_zero] at e
  exact e.trans (gs_zero _ _ _).symm

theorem sec_zero_of_pull {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K₃ : Type} [Fintype K] [Fintype K₃]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (τ : Y' ⟶ Y) (σ : Y ⟶ Y') (hστ : σ ≫ τ = 𝟙 Y)
    {φ₃ : K₃ → (Y' ⟶ X)} {ε₃ : K₃ → ℤ} (u : LB.Gen (LB.LinComb L φ₃ ε₃)) (hu : u.IsGen)
    (h : ∀ y J, Good L y J → sval s τ y J = 0) (j : K → L.ι) : s.f j = 0 := by
  have h1 := sec_zero_of_val hL (pullMulSec s τ u hu) (fun y J hJ => by
    rw [sval_pullMulSec s τ u hu _ y hJ, Category.id_comp, h y J hJ, zero_mul])
  refine sec_zero_of_val hL s (fun y J hJ => ?_) j
  have h2 : sval (pullMulSec s τ u hu) σ y J = 0 := by
    unfold sval
    rw [h1]
    exact gs_zero _ _ _
  rw [sval_pullMulSec s τ u hu _ y hJ, hστ] at h2
  exact (Units.mul_left_eq_zero _).1 h2

theorem main : Laws → Laws2 → AllPre fun {V} _ _ _ {D} {_} {_} _ _ U => ∀ N : ℕ, 1 ≤ N → (∀ α, ∃ t s, U.ExpF (Kbar V) N t s ∧ DegPre.FamFE D (Kbar V) N s ∧ ∃ j, (s α).f j ≠ 0) → U.FE (Kbar V) N := by
  intro hL1 hL2 V _ _ _ hV D A G _ _ U N hN hw t s hts mu α u hu hcorr
  obtain ⟨t₀, s₀, he₀, hfe₀, j, hj⟩ := hw α
  obtain ⟨a, ha⟩ := GlobalTheory.T.expansionComponents_proportional_shift_multiple hL1 hL2 V hV D A G U N hN α mu u hu ⟨t₀, s₀, he₀, j, hj⟩
  have hc : ∀ (z : (DegPre.BF D (Kbar V)).left) (b c : Kbar V),
      gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) (b * c) ⊤) =
        gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) b ⊤) * gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) c ⊤) := by
    intro z b c
    rw [← gs_mul _ _ ⊤ trivial]
    simp only [DegPre.constBF, map_mul]
  have hc1 : ∀ (z : (DegPre.BF D (Kbar V)).left),
      gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) 1 ⊤) = 1 := by
    intro z
    rw [gs_eq _ _ ⊤ trivial]
    simp only [DegPre.constBF, map_one]
  have hca : ∀ (z : (DegPre.BF D (Kbar V)).left) (b : Kbar V),
      gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) (b - 1) ⊤) =
        gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) b ⊤) - 1 := by
    intro z b
    rw [gs_eq _ _ ⊤ trivial, gs_eq _ _ ⊤ trivial]
    simp only [DegPre.constBF, map_sub, map_one]
  have ha1 : a = 1 := by
    by_contra hne
    apply hj
    have hinv : (DegPre.trF D (Kbar V) (-mu)).left ≫ (DegPre.trF D (Kbar V) mu).left = 𝟙 _ := by
      rw [← Over.comp_left, DVR.UUA.trF_add, neg_add_cancel, DVR.UUA.trF_zero, Over.id_left]
    refine sec_zero_of_pull D.P.isLB (s₀ α) _ _ hinv u hu (fun z J hJ => ?_) j
    have e1 := ha t₀ s₀ he₀ z J hJ
    have e2 := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ _).1 (hfe₀ mu α u hu hcorr) _ (𝟙 _) z J hJ
    rw [Category.id_comp] at e2
    have e3 : gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) (a - 1) ⊤) *
        (sval (s₀ α) (DegPre.trF D (Kbar V) mu).left z J * (val u (𝟙 _) z J).val) = 0 := by
      rw [hca, _root_.sub_mul, _root_.one_mul, ← e1, ← e2, sub_self]
    have e4 := congrArg (gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) (a - 1)⁻¹ ⊤) * ·) e3
    simp only [mul_zero] at e4
    rw [← _root_.mul_assoc, ← hc, inv_mul_cancel₀ (sub_ne_zero.2 hne), hc1, _root_.one_mul] at e4
    exact (Units.mul_left_eq_zero _).1 e4
  refine (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ _).2 fun z J hJ => ?_
  rw [Category.id_comp, ha t s hts z J hJ, ha1, hc1, _root_.one_mul]

end GlobalTheory.UU.SchurConst
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FunctionalEquationAllDegreesAlgebraicClosure
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem fe_all_degrees : Laws → Laws2 → AllPre fun {V} _ _ _ {D} {_} {_} _ _ U =>
    D.TauBimult → U.FE (Kbar V) 1 → ∀ N : ℕ, 1 ≤ N → U.FE (Kbar V) N := by
  intro h1 h2 V _ _ _ hV D A G _ _ U hτ hFE
  have hsupp : ∀ N : ℕ, 1 ≤ N → ∃ β, U.Supp (Kbar V) N β := fun N hN => by
    obtain ⟨mu, hmu⟩ := (GlobalTheory.T.lineBundleSections_torusTorsion_weightSpaces h1 h2 V hV D A G U N hN).2.1 0
    exact ⟨_, hmu⟩
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => exact hFE
  | succ k hk ih =>
    exact GlobalTheory.UU.SchurConst.main h1 h2 V hV D A G U (k + 1) (by omega)
      (GlobalTheory.T.exists_functionalEquation_section_nonzero_class h1 h2 V hV D A G U hτ k hk hFE ih (hsupp 1 le_rfl) (hsupp k hk))

end GlobalTheory.UU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FunctionalEquationAllDegreesAlgebraicClosureStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.functional_equation_all_degrees_algebraic_closure : Laws → Laws2 → AllPre fun {V} _ _ _ {D} {_} {_} _ _ U => D.TauBimult → U.FE (Kbar V) 1 → ∀ N : ℕ, 1 ≤ N → U.FE (Kbar V) N := by
  first | exact @GlobalTheory.UU.fe_all_degrees | exact GlobalTheory.UU.fe_all_degrees | (intros; apply GlobalTheory.UU.fe_all_degrees <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpBijOfMatch
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ChartExpansionOfValueExpansion
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ChartExpansionOfValueExpansion
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.ExpFrac

def sc {F : Type} [CommRing F] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of F)) (z : Z) :
    F →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ ⊤ z trivial).hom.comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom)

theorem gs_inv {F : Type} [CommRing F] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of F)) (z : Z) (a : F) :
    gs p z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom a) = sc p z a := by
  rw [gs_eq p z ⊤ trivial]; rfl

theorem gs_scal {F : Type} [CommRing F] {Y Z : Scheme.{0}} (r : Z ⟶ Y) (p : Y ⟶ Spec (CommRingCat.of F)) (z : Z)
    (a : F) : gs r z ⊤ (scal p a) = sc (r ≫ p) z a :=
  (gs_pull r p z ⊤ trivial _).trans (gs_inv _ z a)

theorem sc_map {F F' : Type} [CommRing F] [CommRing F'] (φ : F →+* F') {Z : Scheme.{0}}
    (p : Z ⟶ Spec (CommRingCat.of F')) (z : Z) (a : F) :
    sc (p ≫ Spec.map (CommRingCat.ofHom φ)) z a = sc p z (φ a) := by
  have e := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  simp only [sc, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, e]

theorem jFK_self (R : Type) [CommRing R] [IsDomain R] :
    jFK (R := R) (FractionRing R) = 𝟙 (Spec (CommRingCat.of (FractionRing R))) := by
  show Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) (FractionRing R))) = _
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

theorem clear_sum {R S : Type} [CommRing R] [IsDomain R] [CommRing S] (χ : FractionRing R →+* S) {n : ℕ} (r : R)
    (a : Fin n → R) (c : Fin n → FractionRing R) (h : ∀ i, algebraMap R (FractionRing R) (a i) = r • c i)
    (v : Fin n → S) :
    ∑ i, χ (algebraMap R _ (a i)) * v i = χ (algebraMap R _ r) * ∑ i, χ (c i) * v i := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h i, Algebra.smul_def, map_mul, _root_.mul_assoc]

theorem expands_of_expF : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D.toPre A G) (U' : UnifPre I D A G), Match U U' → ∀ (k : ℕ) (σ : U'.SecK k) (σ₀) (t) (s : Fam D.toPre (FractionRing R) k), HEq σ σ₀ → U.SameK (k := k) σ₀ t → U.ExpF (FractionRing R) k t s.s → U'.Expands k σ s := by
  intro R _ _ I D A G _ _ U U' hM k σ σ₀ t s hσ hK hE
  obtain ⟨n, c, σs, fs, hT, hA, hB⟩ := hE
  obtain ⟨⟨r, hr⟩, ha⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) c
  choose a ha using ha
  obtain ⟨σ', f', hT', hσ', hf'⟩ := ExpLin.expT_linear R I D.toPre A G U (𝟙_ _) k n
    (fun i => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (a i)) σs fs hT
  obtain ⟨-, e₁, -, e₂⟩ := UnitSec.same_exists R D.toPre G U.P.L.L U.P.L.isLB k
  obtain ⟨τ, hτ⟩ := e₁ σ'
  obtain ⟨f, hf⟩ := e₂ f'
  have hAt := fun τ' => expandsAt_of_expT R I D A G U U' hM k τ' τ σ' f f'
  have hG : GeneratorPullback.SecScal U.P.L.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => (k : ℤ)) σ₀
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) τ (pullback.fst G.hom (jK R))
      (scal (pullback.snd G.hom (jK R) ≫ jK R) r) := by
    refine BoxFamScalar.secScal_of_pointwise U.P.L.isLB fun y J hJ => ?_
    obtain ⟨rG, hG₁, hG₂⟩ := exists_lift_unit_tensor G (𝟙 _ ≫ pullback.fst G.hom (jK R))
    choose JA hJA using fun ψ : pullback G.hom (jK R) ⟶ A.A.left => exists_chart A.isLB (ψ y)
    have w : pullback.snd G.hom (jK R) ≫ (TFK (R := R) (FractionRing R)).hom = U.gen.hom.left ≫ A.A.hom :=
      ((congrArg (pullback.snd G.hom (jK R) ≫ ·) (jFK_self R)).trans (Category.comp_id _)).trans
        (Over.w U.gen.hom).symm
    obtain ⟨rA, hA₁, hA₂⟩ : ∃ rA : pullback G.hom (jK R) ⟶ (TFK (R := R) (FractionRing R) ⊗ A.A).left,
        rA ≫ (fst _ A.A).left = pullback.snd G.hom (jK R) ∧ rA ≫ (snd _ A.A).left = 𝟙 _ ≫ U.gen.hom.left :=
      ⟨pullback.lift _ _ w, pullback.lift_fst _ _ w, (pullback.lift_snd _ _ w).trans (Category.id_comp _).symm⟩
    have e₃ := (hK _ rA (𝟙 _) hA₂ y JA J hJA hJ).symm.trans (hA _ rA (𝟙 _) rG hA₂ hG₁ y JA J hJA hJ)
    have e₄ : rG ≫ (fst _ G).left = pullback.snd G.hom (jK R) ≫ jK R :=
      hG₂.trans ((congrArg (· ≫ G.hom) (Category.id_comp _)).trans pullback.condition)
    refine ((congrArg (fun q => sval τ q y J) hG₁).symm.trans (hτ _ rG y J hJ).symm).trans
      ((hσ' _ rG y J hJ).trans ?_)
    refine Eq.trans ?_ (congrArg (_ * ·) e₃).symm
    refine Eq.trans ?_ ((clear_sum (sc (pullback.snd G.hom (jK R)) y) r a c ha (fun i => sval (σs i) rG y J)).trans ?_)
    · refine Finset.sum_congr rfl fun i _ => congrArg (· * _) ?_
      exact (gs_inv _ y _).trans ((congrArg (fun q => sc q y (a i)) e₄).trans (sc_map _ _ y _))
    · refine congrArg₂ (· * ·) ?_ (Finset.sum_congr rfl fun i _ => congrArg (· * _) ?_)
      · rw [gs_scal, Category.id_comp, sc_map]
      · exact ((gs_scal _ _ y _).trans (congrArg (fun q => sc q y (c i)) hA₁)).symm
  have hF : ∀ α : D.toPre.X,
      GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) (s.s α)
        (D.toPre.famφB α) (DegPre.famε k) (f α) (DegPre.prB D.toPre (FractionRing R)).left
        (scal (DegPre.BF D.toPre (FractionRing R)).hom r) := by
    intro α
    refine BoxFamScalar.secScal_of_pointwise D.toPre.P.isLB fun y J hJ => ?_
    obtain ⟨rB, hB₁, hB₂⟩ := exists_lift_unit_tensor D.toPre.P.A (𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing R)).left)
    have e₃ := hB α _ (𝟙 _) rB hB₁ y J hJ
    have e₅ : (DegPre.BF D.toPre (FractionRing R)).hom =
        (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ jK R :=
      (Over.w (fst (TF (R := R) (FractionRing R)) D.toPre.P.A)).symm.trans (congrArg
        ((fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ ·)
        ((congrArg (· ≫ jK R) (jFK_self R)).trans (Category.id_comp _)))
    have e₄ : rB ≫ (fst _ D.toPre.P.A).left = (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ jK R :=
      hB₂.trans ((congrArg (· ≫ D.toPre.P.A.hom) (Category.id_comp _)).trans
        ((Over.w (DegPre.prB D.toPre (FractionRing R))).trans e₅))
    refine ((congrArg (fun q => sval (f α) q y J) hB₁).symm.trans (hf α _ rB y J hJ).symm).trans
      ((hf' α _ rB y J hJ).trans ?_)
    refine Eq.trans ?_ (congrArg (_ * ·) e₃).symm
    refine Eq.trans ?_ ((clear_sum (sc (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left y) r a c ha
      (fun i => sval (fs i α) rB y J)).trans ?_)
    · refine Finset.sum_congr rfl fun i _ => congrArg (· * _) ?_
      exact (gs_inv _ y _).trans ((congrArg (fun q => sc q y (a i)) e₄).trans (sc_map _ _ y _))
    · refine congrArg₂ (· * ·) ?_ (Finset.sum_congr rfl fun i _ => congrArg (· * _) ?_)
      · exact ((gs_scal _ _ y _).trans ((congrArg (fun q => sc q y r) ((Category.id_comp _).trans e₅)).trans
          (sc_map _ _ y _))).symm
      · exact ((gs_scal _ _ y _).trans (congrArg (fun q => sc q y (c i)) (Category.id_comp _))).symm
  obtain ⟨semi, gen, gen_hom, P, wA, wA_gen, gt, gt_q, gt_t, w, w_gen, w_vals, w_compat⟩ := U
  cases P
  have hL := hM.LG
  dsimp only at hL
  subst hL
  obtain rfl := eq_of_heq hσ
  exact ⟨r, nonZeroDivisors.ne_zero hr, τ, f, hG, hF, hAt τ HEq.rfl hτ hf hT'⟩

end GlobalTheory.UU.ExpFrac
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ChartExpansionOfValueExpansionStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.chartExpansion_of_valueExpansion : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D.toPre A G) (U' : UnifPre I D A G), Match U U' → ∀ (k : ℕ) (σ : U'.SecK k) (σ₀) (t) (s : Fam D.toPre (FractionRing R) k), HEq σ σ₀ → U.SameK (k := k) σ₀ t → U.ExpF (FractionRing R) k t s.s → U'.Expands k σ s := by
  first | exact @GlobalTheory.UU.ExpFrac.expands_of_expF | exact GlobalTheory.UU.ExpFrac.expands_of_expF | (intros; apply GlobalTheory.UU.ExpFrac.expands_of_expF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueExpansionOfChartExpansion
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueExpansionOfChartExpansion
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem sval_of_secScal {X Y Y' Z : Scheme.{0}} {L : LB X} {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
    {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)}
    {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y} {c : Γ(Y', ⊤)}
    (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval s₂ (r ≫ h) z J = gs r z ⊤ c * sval s₁ r z J := by
  have e := H (fun k => J (r ≫ φ₁ k)) (fun k => J (r ≫ h ≫ φ₂ k)) (by
    rintro (a | a) (b | b) e <;> exact congrArg (fun q => J (r ≫ q)) e)
  have hm : r z ∈ LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓
      LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k)) :=
    ⟨hJ.mem φ₁ r, hJ.mem (fun k => h ≫ φ₂ k) r⟩
  have le : LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k)) ≤
      h ⁻¹ᵁ LB.wchart L φ₂ (fun k => J (r ≫ h ≫ φ₂ k)) :=
    fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  rw [sval_of s₂ (r ≫ h) z J (fun k => J (r ≫ h ≫ φ₂ k)) (fun k => by rw [Category.assoc])]
  have e2 := congrArg (gs r z _) e
  exact ((gs_res r z _ hm _).trans (gs_pull r h z _ (le hm.2) _)).symm.trans (e2.trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_res r z le_top hm _) (gs_res r z _ hm _))))

theorem scal_specMap {A C : Type} [CommRing A] [CommRing C] (φ : A →+* C) {Y : Scheme.{0}}
    (p : Y ⟶ Spec (CommRingCat.of C)) (a : A) :
    scal (p ≫ Spec.map (CommRingCat.ofHom φ)) a = scal p (φ a) := by
  have e := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  exact congrArg p.appTop.hom e.symm

theorem gs_scal_inv_mul {R : Type} [CommRing R] [IsDomain R] {Y₁ Y₂ Z : Scheme.{0}}
    (p₁ : Y₁ ⟶ Spec (CommRingCat.of (FractionRing R))) (p₂ : Y₂ ⟶ Spec (CommRingCat.of R))
    (r₁ : Z ⟶ Y₁) (r₂ : Z ⟶ Y₂) (h : r₂ ≫ p₂ = ((r₁ ≫ p₁) ≫ jFK (R := R) (FractionRing R)) ≫ jK R) (z : Z)
    {a : R} (ha : a ≠ 0) :
    gs r₁ z ⊤ (scal p₁ (algebraMap R (FractionRing R) a)⁻¹) * gs r₂ z ⊤ (scal p₂ a) = 1 := by
  have k : ∀ {S : Type} [CommRing S] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of S)) (r : Z ⟶ Y) (c : S),
      gs r z ⊤ (scal p c) = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := by
    intro S _ Y p r c
    calc gs r z ⊤ (scal p c) = gs (𝟙 _ ≫ r) z ⊤ (scal p c) := by rw [Category.id_comp]
      _ = gs (𝟙 _) z (r ⁻¹ᵁ ⊤) ((r.app ⊤).hom (scal p c)) := (gs_pull (𝟙 _) r z ⊤ (by trivial) _).symm
      _ = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := rfl
  have e : scal (((r₁ ≫ p₁) ≫ jFK (R := R) (FractionRing R)) ≫ jK R) a =
      scal (r₁ ≫ p₁) (algebraMap R (FractionRing R) a) :=
    (scal_specMap _ _ a).trans (scal_specMap _ _ _)
  have ha' : algebraMap R (FractionRing R) a ≠ 0 := fun h0 =>
    ha (IsFractionRing.injective R (FractionRing R) (h0.trans (map_zero _).symm))
  rw [k p₁, k p₂, h, e, ← gs_mul _ z ⊤ trivial, scal, scal, ← map_mul, ← map_mul, inv_mul_cancel₀ ha', map_one, map_one,
    gs_eq _ z ⊤ trivial, map_one, map_one]

theorem expF_of_expands : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D.toPre A G) (U' : UnifPre I D A G), Match U U' → ∀ (k : ℕ) (σ : U'.SecK k) (σ₀) (t) (s : Fam D.toPre (FractionRing R) k), HEq σ σ₀ → U.SameK (k := k) σ₀ t → U'.Expands k σ s → U.ExpF (FractionRing R) k t s.s := by
  intro R _ _ I D A G _ _ U U' hM k σ σ₀ t s hσ hK hE
  obtain ⟨r, hr, τ, f, hτ, hf, hE⟩ := hE
  have hL := hM.LG
  have hX := fun τ₀ τ' f' h₁ h₂ h₃ => expT_of_expandsAt R I D A G U U' hM k τ τ₀ τ' f f' h₁ h₂ h₃ hE
  clear hE hM
  cases U'
  dsimp only at hL
  subst hL
  cases hσ
  obtain ⟨e₁, -, e₃, -⟩ := GlobalTheory.UnitSec.same_exists R D.toPre G U.P.L.L U.P.L.isLB k
  obtain ⟨τ', hτ'⟩ := e₁ τ
  obtain ⟨f', hf'⟩ := e₃ f
  refine ⟨1, fun _ => (algebraMap R (FractionRing R) r)⁻¹, fun _ => τ', fun _ => f',
    fun _ => hX τ τ' f' HEq.rfl hτ' hf', ?_, ?_⟩
  · intro Z rA y rG h₁ h₂ z JA JG hJA hJG
    refine (hK Z rA y h₁ z JA JG hJA hJG).trans ?_
    rw [Fin.sum_univ_one, hτ' Z rG z JG hJG, h₂]
    refine Eq.trans ?_ (congrArg (_ * ·) (sval_of_secScal hτ y z hJG)).symm
    rw [← _root_.mul_assoc]
    refine (_root_.one_mul _).symm.trans (congrArg (· * _) (gs_scal_inv_mul _ _ rA y ?_ z hr).symm)
    have w₁ := Over.w (fst (TFK (R := R) (FractionRing R)) A.A)
    have w₂ := Over.w (snd (TFK (R := R) (FractionRing R)) A.A)
    have w₃ := Over.w U.gen.hom
    have w₄ : (rA ≫ (fst (TFK (R := R) (FractionRing R)) A.A).left) ≫ jFK (R := R) (FractionRing R) =
        y ≫ pullback.snd G.hom (jK R) :=
      (Category.assoc _ _ _).trans ((congrArg (rA ≫ ·) (w₁.trans w₂.symm)).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ A.A.hom) h₁).trans ((Category.assoc _ _ _).trans (congrArg (y ≫ ·) w₃)))))
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ jK R) w₄.symm)
  · intro α Z rF rB h₁ z J hJ
    rw [Fin.sum_univ_one, hf' α Z rB z J hJ, h₁]
    refine Eq.trans ?_ (congrArg (_ * ·) (sval_of_secScal (hf α) rF z hJ)).symm
    rw [← _root_.mul_assoc]
    refine (_root_.one_mul _).symm.trans (congrArg (· * _) (gs_scal_inv_mul _ _ rF rF ?_ z hr).symm)
    have w₁ := Over.w (fst (TF (R := R) (FractionRing R)) D.toPre.P.A)
    exact (congrArg (rF ≫ ·) w₁.symm).trans ((Category.assoc _ _ _).symm.trans (Category.assoc _ _ _).symm)

end GlobalTheory.UU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueExpansionOfChartExpansionStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.valueExpansion_of_chartExpansion : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D.toPre A G) (U' : UnifPre I D A G), Match U U' → ∀ (k : ℕ) (σ : U'.SecK k) (σ₀) (t) (s : Fam D.toPre (FractionRing R) k), HEq σ σ₀ → U.SameK (k := k) σ₀ t → U'.Expands k σ s → U.ExpF (FractionRing R) k t s.s := by
  first | exact @GlobalTheory.UU.expF_of_expands | exact GlobalTheory.UU.expF_of_expands | (intros; apply GlobalTheory.UU.expF_of_expands <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpBijOfMatch
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.ExpansionClause

theorem expBij_of_match : Laws → Laws2 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : PreU (IsLocalRing.maximalIdeal V) D.toPre A G) (U' : UnifPre (IsLocalRing.maximalIdeal V) D A G), Match U U' → ∀ k : ℕ, 1 ≤ k → U.FE (FractionRing V) k → (∀ s : Fam D.toPre (FractionRing V) k, ∃ t, U.ExpF (FractionRing V) k t s.s) → U'.ExpBij k := by
  intro h1 h2 V _ _ _ hV D A G _ _ U U' hM k hk hFE hsurj
  have hT : U'.SecK k = LB.Sec (LB.LinComb U.P.L.L (K := Fin 1) (fun _ => pullback.fst G.hom (jK V)) (fun _ => (k : ℤ))) := by
    unfold UnifPre.SecK
    rw [hM.LG]
  have hK := GlobalTheory.GenericFibreSections.sameK_bijective V _ D.toPre A G U k
  have hu := GlobalTheory.T.fourierJacobiExpansion_overField_injective V hV D.toPre A G U (FractionRing V) k
  have ht := GlobalTheory.T.exists_fourierJacobi_expansion_over_field h1 h2 V hV D.toPre A G U (FractionRing V) k hk
  have e1 := GlobalTheory.T.valueExpansion_of_chartExpansion V _ D A G U U' hM k
  have e2 := GlobalTheory.T.chartExpansion_of_valueExpansion V _ D A G U U' hM k
  unfold UnifPre.ExpBij
  refine ⟨fun σ => ?_, fun s => ?_⟩
  · obtain ⟨t, hσt, -⟩ := hK.1 (cast hT σ)
    obtain ⟨s, hs⟩ := ht t
    refine ⟨⟨s, hFE t s hs⟩, e2 σ _ t _ (cast_heq hT σ).symm hσt hs, fun s' hs' => ?_⟩
    have h := (hu t t s'.s s (e1 σ _ t s' (cast_heq hT σ).symm hσt hs') hs).1 rfl
    obtain ⟨s', fe⟩ := s'
    cases h
    rfl
  · obtain ⟨t, hts⟩ := hsurj s
    obtain ⟨σ₀, hσt, huniq⟩ := hK.2 t
    refine ⟨cast hT.symm σ₀, e2 _ σ₀ t s (cast_heq hT.symm σ₀) hσt hts, fun σ hσ => ?_⟩
    obtain ⟨t', hσt', -⟩ := hK.1 (cast hT σ)
    have h := (hu t' t s.s s.s (e1 σ _ t' s (cast_heq hT σ).symm hσt' hσ) hts).2 rfl
    subst h
    rw [← huniq _ hσt']
    simp

end GlobalTheory.ExpansionClause
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpBijOfMatchStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expBij_of_match_of_fam_expF : Laws → Laws2 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : PreU (IsLocalRing.maximalIdeal V) D.toPre A G) (U' : UnifPre (IsLocalRing.maximalIdeal V) D A G), Match U U' → ∀ k : ℕ, 1 ≤ k → U.FE (FractionRing V) k → (∀ s : Fam D.toPre (FractionRing V) k, ∃ t, U.ExpF (FractionRing V) k t s.s) → U'.ExpBij k := by
  first | exact @GlobalTheory.ExpansionClause.expBij_of_match | exact GlobalTheory.ExpansionClause.expBij_of_match | (intros; apply GlobalTheory.ExpansionClause.expBij_of_match <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsExpFOfFam
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalLincomb
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU.ExpLinC

theorem gs_sum' {Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (hm : r z ∈ U) {K : Type} (S : Finset K)
    (a : K → Γ(Y, U)) : gs r z U (∑ i ∈ S, a i) = ∑ i ∈ S, gs r z U (a i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have h := gs_add r z U hm 0 0
    rw [add_zero] at h
    simpa using h
  | insert i S hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, gs_add r z U hm, ih]

theorem sval_lincomb {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {n : ℕ}
    {t : Fin n → LB.Sec (LB.LinComb L φ ε)} {t' : LB.Sec (LB.LinComb L φ ε)} (a : Fin n → Γ(Y, ⊤))
    (h : ∀ j, t'.f j = ∑ i, (Y.presheaf.map (homOfLE le_top).op).hom (a i) * (t i).f j)
    (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval t' r z J = ∑ i, gs r z ⊤ (a i) * sval (t i) r z J := by
  have hm := hJ.mem φ r
  refine (congrArg (gs r z _) (h _)).trans ?_
  refine (gs_sum' _ _ _ hm _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
  exact (gs_mul _ _ _ hm _ _).trans (congrArg (· * _) (gs_res r z le_top hm (a i)))

theorem expF_lincomb : (AllPre fun {V} _ _ _ {D} {A} {_} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k n : ℕ) (c : Fin n → F) (t : Fin n → LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := V) F))) (s : Fin n → Raw D F k) (t' : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := V) F))) (s' : Raw D F k), (∀ i, U.ExpF F k (t i) (s i)) → (∀ j, t'.f j = ∑ i, liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i)) * (t i).f j) → (∀ α j, (s' α).f j = ∑ i, DegPre.constBF D F (c i) _ * (s i α).f j) → U.ExpF F k t' s') := by
  intro V _ _ _ _ D A G _ _ U F _ _ k n c t s t' s' H ht hs
  choose m a σ f h1 h2 h3 using H
  let e : Fin (Fintype.card (Σ i, Fin (m i))) ≃ (Σ i, Fin (m i)) := (Fintype.equivFin _).symm
  refine ⟨_, fun p => c (e p).1 * a (e p).1 (e p).2, fun p => σ (e p).1 (e p).2, fun p => f (e p).1 (e p).2,
    fun p => h1 _ _, fun Z rA y rG e1 e2 z JA JG hA hG => ?_, fun α Z rF rB e0 z J hJ => ?_⟩
  · rw [e.sum_comp (fun q => gs rA z ⊤ (scal (fst (TFK (R := V) F) A.A).left (c q.1 * a q.1 q.2)) *
      sval (σ q.1 q.2) rG z JG), Fintype.sum_sigma,
      sval_lincomb (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := V) F) A.A).left) (ε := fun _ => (k : ℤ))
        (fun i => scal (fst (TFK (R := V) F) A.A).left (c i)) ht rA z hA, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ExpLin.gs_scal_mul, _root_.mul_assoc]
    rw [← Finset.mul_sum, ← h2 i Z rA y rG e1 e2 z JA JG hA hG]
    ring
  · rw [e.sum_comp (fun q => gs rF z ⊤ (scal (fst (TF (R := V) F) D.P.A).left (c q.1 * a q.1 q.2)) *
      sval (f q.1 q.2 α) rB z J), Fintype.sum_sigma]
    refine (sval_lincomb (fun i => scal (fst (TF (R := V) F) D.P.A).left (c i)) (hs α) rF z hJ).trans ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ExpLin.gs_scal_mul, _root_.mul_assoc]
    rw [← Finset.mul_sum, ← h3 i α Z rF rB e0 z J hJ]

end GlobalTheory.UU.ExpLinC
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU.ExpOnto

theorem exists_sec_comb {X : Scheme.{0}} {L : LB X} {n : ℕ} (r : Fin n → Γ(X, ⊤)) (b : Fin n → LB.Sec L) :
    ∃ t : LB.Sec L, ∀ j, t.f j = ∑ i, resTop _ (r i) * (b i).f j := by
  induction n with
  | zero => exact ⟨DVR.SecOps.secZero, fun j => by simp [DVR.SecOps.secZero]⟩
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih (fun i => r i.succ) (fun i => b i.succ)
    refine ⟨DVR.SecOps.secAdd (DVR.SecOps.secScale (r 0) (b 0)) t, fun j => ?_⟩
    rw [Fin.sum_univ_succ, ← ht j]
    rfl

theorem fam_sum_f {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {k : ℕ} {K : Type} (S : Finset K) (s : K → Fam D F k) (α : D.X) (j) :
    ((∑ i ∈ S, s i).s α).f j = ∑ i ∈ S, ((s i).s α).f j := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, DVR.add_f, ih]

theorem exists_expF_of_fam : Laws → Laws2 → AllPre fun {V} _ _ _ {D} {_} {_} _ _ U => D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → U.FE F k → ∀ s : Fam D F k, ∃ t, U.ExpF F k t s.s := by
  intro hL hL2 V _ _ _ hV D A G _ _ U hB F _ _ k hk hFE s
  obtain ⟨b, hb⟩ := GlobalTheory.PowBasis.exists_basis_pow_field hL2.secTwist V A F k hk
  choose e he using fun i => GlobalTheory.T.exists_fourierJacobi_expansion_over_field hL hL2 V hV D A G U F k hk (b i)
  let f : Fin (k ^ A.g) → Fam D F k := fun i => ⟨e i, hFE _ _ (he i)⟩
  have comb : ∀ c : Fin (k ^ A.g) → F, ∃ t, (∀ j, t.f j = ∑ i,
      liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i)) * (b i).f j) ∧
      U.ExpF F k t (∑ i, c i • f i).s := fun c => by
    obtain ⟨t, ht⟩ := exists_sec_comb (fun i => (fst (TFK (R := V) F) A.A).left.appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i))) b
    refine ⟨t, ht, ExpLinC.expF_lincomb V hV D A G U F k _ c b e t _ he ht fun α j => ?_⟩
    exact fam_sum_f _ _ α j
  have hli : LinearIndependent F f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    obtain ⟨t, ht, hE⟩ := comb c
    obtain ⟨t', ht', hE'⟩ := comb 0
    have h0 : (∑ i, (0 : Fin (k ^ A.g) → F) i • f i) = ∑ i, c i • f i := by
      rw [hc]; simp
    have htt : t = t' := (GlobalTheory.T.fourierJacobiExpansion_overField_injective V hV D A G U F k t t' _ _ hE hE').2 (by rw [h0])
    subst htt
    exact congrFun ((hb t).unique ht ht')
  obtain ⟨hfin, hdim⟩ := finrank_fam_of_laws hL hL2 V D hB F k hk
  have hg : A.g = D.P.g + D.rank := PreU.dim_eq V hV D A G U
  have hsp := hli.span_eq_top_of_card_eq_finrank' (by rw [hdim, Fintype.card_fin, hg])
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 (hsp ▸ Submodule.mem_top (x := s))
  obtain ⟨t, -, hE⟩ := comb c
  exact ⟨t, hc ▸ hE⟩

end GlobalTheory.UU.ExpOnto

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FiniteExponentBaseChangeField
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FamilyFunctionalEquationFieldChange
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FamilyFunctionalEquationFieldChange
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory
namespace FieldChange

theorem sval_extend {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {φ₁ : K → (Y' ⟶ X)} {ε : K → ℤ} (h : Y' ⟶ Y) (hφ : φ₁ = fun k => h ≫ φ k)
    (s : LB.Sec (LB.LinComb L φ₁ ε)) (f : LB.Sec (LB.LinComb L φ ε))
    (H : ∀ y J, Good L y J → sval s (𝟙 _) y J = sval f h y J) {Z : Scheme.{0}} (r : Z ⟶ Y') (z : Z) (J)
    (hJ : Good L z J) : sval s r z J = sval f (r ≫ h) z J := by
  subst hφ
  have e := sec_ext_val hL (s := s) (s' := DVR.pullSec L φ ε f h) (fun y J hJ => by
    rw [DVR.SectionScalarValuation.sval_pullSec φ ε f h _ y hJ, Category.id_comp]; exact H y J hJ)
  rw [← DVR.SectionScalarValuation.sval_pullSec φ ε f h r z hJ]
  exact congrArg (gs r z _) (e _)

theorem gs_scal_comp {R : Type} [CommRing R] {Y Y' Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (h : Y' ⟶ Y)
    (r : Z ⟶ Y') (z : Z) (c : R) : gs (r ≫ h) z ⊤ (scal p c) = gs r z ⊤ (scal (h ≫ p) c) :=
  (gs_pull r h z ⊤ (by trivial) _).symm

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {T : Over (Spec (CommRingCat.of R))}
  {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem fam_comp (φ : TF (R := R) F ⟶ T) (α : D.X) :
    DegPre.famφ D F α = fun i => (φ ▷ D.P.A).left ≫ famφT D T α i := by
  have e₀ : φ ▷ D.P.A ≫ snd T D.P.A = snd _ _ := whiskerRight_snd _ _
  have e₂ : φ ▷ D.P.A ≫ DVR.cP D _ α = DVR.cP D _ α := DVR.comp_cP D _ α
  funext i
  fin_cases i
  · exact (congrArg (fun q => q.left) e₀).symm
  · refine (congrArg (fun q : DegPre.BF D F ⟶ D.P.A => q.left)
      ((MonObj.comp_mul (φ ▷ D.P.A) (snd T D.P.A) (DVR.cP D _ α)).trans ?_)).symm
    rw [e₀, e₂]; rfl
  · exact (congrArg (fun q => q.left) e₂).symm
  · exact (congrArg (fun q : DegPre.BF D F ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) (φ ▷ D.P.A))).symm

theorem tr_comp (φ : TF (R := R) F ⟶ T) (mu : D.X) :
    φ ▷ D.P.A ≫ trT D (toUnit T ≫ D.c mu) = DegPre.trF D F mu ≫ φ ▷ D.P.A := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [trT, DegPre.trF]
  · rw [Category.assoc, Category.assoc, whiskerRight_snd, trT, DegPre.trF, lift_snd, lift_snd]
    refine (MonObj.comp_mul (φ ▷ D.P.A) (snd T D.P.A) (fst _ _ ≫ DVR.cP D _ mu)).trans ?_
    rw [whiskerRight_snd, DVR.comp_cP, DVR.comp_cP]; rfl

theorem pullB_all {φ : TF (R := R) F ⟶ T} {k : ℕ} {f : ∀ α, SecBT D T k α} {s : Raw D F k} (H : PullB D F φ k f s)
    (α : D.X) {Z : Scheme.{0}} (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J) (hJ : Good D.P.L z J) :
    sval (s α) r z J = sval (f α) (r ≫ (φ ▷ D.P.A).left) z J :=
  sval_extend D.P.isLB _ (fam_comp D φ α) (s α) (f α) (H α) r z J hJ

theorem isUnit_scal {c : R} (hc : c ≠ 0) {Z : Scheme.{0}} (r : Z ⟶ (DegPre.BF D F).left) (z : Z) :
    IsUnit (gs r z ⊤ (scal (DegPre.BF D F).hom c)) := by
  have e : (DegPre.BF D F).hom = ((fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F) ≫ jK R := by
    rw [Category.assoc]; exact (Over.w (fst (TF (R := R) F) D.P.A)).symm
  have hu : IsUnit (scal (jK R) c) := by
    have n := congrArg (fun q => q.hom c)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at n
    have hc' : IsUnit (algebraMap R (FractionRing R) c) :=
      IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hc)
    exact (congrArg IsUnit n).mp (hc'.map _)
  rw [e, gs_eq _ _ ⊤ (by trivial)]
  exact ((hu.map ((fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F).appTop.hom).map _).map _

end FieldChange


open FieldChange in
theorem famFE_field_change : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) [IsAffine T.left] (k : ℕ) (f : ∀ α, SecBT D T k α) (F F' : Type) [Field F] [Algebra (FractionRing R) F] [Field F'] [Algebra (FractionRing R) F'] (φ : TF (R := R) F ⟶ T) (φ' : TF (R := R) F' ⟶ T) (s : Raw D F k) (s' : Raw D F' k), Function.Injective φ.left.appTop.hom → PullB D F φ k f s → PullB D F' φ' k f s' → DegPre.FamFE D F k s → DegPre.FamFE D F' k s' := by
  intro hG R _ _ _ D T _ k f F F' _ _ _ _ φ φ' s s' hinj hs hs' hfe mu α u' hu' hc'
  obtain ⟨u₀, r₁, r₂, hu₀, -, h₂, hv⟩ := GlobalTheory.UU.IntGen.main hG R D T k α mu
  obtain ⟨⟨u, hu, hc⟩, -⟩ := DVR.gen_fe (D := D) (F := F) hG k mu α
  have : Smooth D.P.A.hom := D.P.isAb.smooth
  have : IsAffine (TF (R := R) F).left := inferInstanceAs (IsAffine (Spec _))
  have sc : ∀ {E : Type} [Field E] [Algebra (FractionRing R) E] (ψ : TF (R := R) E ⟶ T) (c : R)
      (y : (DegPre.BF D E).left), gs (ψ ▷ D.P.A).left y ⊤ (scal (T ⊗ D.P.A).hom c) =
        gs (𝟙 _) y ⊤ (scal (DegPre.BF D E).hom c) := fun ψ c y => by
    rw [← Over.w (ψ ▷ D.P.A), ← gs_scal_comp, Category.id_comp]
  have tr : ∀ {E : Type} [Field E] [Algebra (FractionRing R) E] (ψ : TF (R := R) E ⟶ T),
      (ψ ▷ D.P.A).left ≫ (trT D (toUnit T ≫ D.c mu)).left = (𝟙 _ ≫ (DegPre.trF D E mu).left) ≫ (ψ ▷ D.P.A).left :=
    fun ψ => by rw [Category.id_comp]; exact congrArg (fun q => q.left) (tr_comp D ψ mu)
  have key := sec_relation_descends _ D.P.A T (TF (R := R) F) φ hinj _ _ D.P.L D.P.isLB _ _ _
    (famφT D T α) (DegPre.famε k) (famφT D T (α + k • mu)) (DegPre.famε k)
    (deltaφT D (α + k • mu) α (toUnit T ≫ D.c mu)) (DegPre.deltaε k) (trT D (toUnit T ≫ D.c mu)).left
    (f α) (f (α + k • mu)) u₀ (scal (T ⊗ D.P.A).hom r₁) (scal (T ⊗ D.P.A).hom r₂) hu₀
    (fun U _ h => by
      refine Eq.symm (Eq.trans (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4 ⊕ Fin 4) (U := U) _
          (c := ∏ i, h ((trT D (toUnit T ≫ D.c mu)).left ≫ famφT D T α i) ^ DegPre.famε k i) rfl
          (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _
            (c := ∏ i, h (famφT D T (α + k • mu) i) ^ DegPre.famε k i) rfl (DVR.prod_neg _ _ rfl))) ?_)
      exact (mul_comm _ _).trans (inv_mul_cancel_right _ _))
    (fun y J hJ => by
      have e₁ := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (hfe mu α u hu hc) _ (𝟙 _) y J hJ
      have e₂ := hv F φ u hu hc _ (𝟙 _) y J hJ
      rw [Category.id_comp] at e₂
      rw [sc, sc, tr, ← pullB_all D hs α _ y J hJ, ← hs _ y J hJ, e₁, mul_left_comm, e₂, mul_left_comm])
  refine (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u').2 fun y J hJ => ?_
  have e₁ := key _ (φ' ▷ D.P.A).left y J hJ
  have e₂ := hv F' φ' u' hu' hc' _ (𝟙 _) y J hJ
  rw [Category.id_comp] at e₂
  rw [sc, sc, tr, ← pullB_all D hs' α _ y J hJ, ← hs' _ y J hJ, mul_left_comm, ← e₂, mul_left_comm] at e₁
  exact (isUnit_scal D h₂ _ y).mul_left_cancel e₁

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FamilyFunctionalEquationFieldChangeStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.familyFunctionalEquation_field_change : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) [IsAffine T.left] (k : ℕ) (f : ∀ α, SecBT D T k α) (F F' : Type) [Field F] [Algebra (FractionRing R) F] [Field F'] [Algebra (FractionRing R) F'] (φ : TF (R := R) F ⟶ T) (φ' : TF (R := R) F' ⟶ T) (s : Raw D F k) (s' : Raw D F' k), Function.Injective φ.left.appTop.hom → PullB D F φ k f s → PullB D F' φ' k f s' → DegPre.FamFE D F k s → DegPre.FamFE D F' k s' := by
  first | exact @GlobalTheory.famFE_field_change | exact GlobalTheory.famFE_field_change | (intros; apply GlobalTheory.famFE_field_change <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FiniteExponentBaseChangeField
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU.FEDesc

theorem spec_appTop_injective {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Injective f) :
    Function.Injective (Spec.map (CommRingCat.ofHom f)).appTop.hom := by
  have e : (Spec.map (CommRingCat.ofHom f)).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom f ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).inv := by
    rw [← Category.assoc, ← Scheme.ΓSpecIso_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [e, CommRingCat.hom_comp, CommRingCat.hom_comp, RingHom.coe_comp, RingHom.coe_comp]
  exact ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of B)).inv).1.comp hf).comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).hom).1

theorem toUnit_injective (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F] :
    Function.Injective (toUnit (TF (R := R) F)).left.appTop.hom := by
  have e₂ : (toUnit (TF (R := R) F)).left = jFK (R := R) F ≫ jK R := by
    have a := Over.w (toUnit (TF (R := R) F))
    exact (Category.comp_id _).symm.trans a
  rw [e₂]
  exact (spec_appTop_injective _ (algebraMap (FractionRing R) F).injective).comp
    (spec_appTop_injective _ (IsFractionRing.injective R (FractionRing R)))

theorem famFE_of_sum {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k n : ℕ) (c : Fin n → F) (s : Raw D F k) (t : Fin n → Raw D F k)
    (h : ∀ (α : D.X) (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J), Good D.P.L z J →
      sval (s α) r z J = ∑ i, gs r z ⊤ (scal (fst (TF (R := R) F) D.P.A).left (c i)) * sval (t i α) r z J)
    (ht : ∀ i, DegPre.FamFE D F k (t i)) : DegPre.FamFE D F k s := by
  intro mu α u hu hc
  refine (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_
  rw [h _ _ _ y J hJ, h _ _ _ y J hJ, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (ht i mu α u hu hc) _ (𝟙 _) y J hJ, _root_.mul_assoc]
  congr 1
  have e : (DegPre.trF D F mu).left ≫ (fst (TF (R := R) F) D.P.A).left = (fst (TF (R := R) F) D.P.A).left :=
    congrArg (fun q => q.left) (lift_fst _ _ : DegPre.trF D F mu ≫ fst (TF (R := R) F) D.P.A = _)
  have key : ∀ {Y : Scheme.{0}} (y : Y) (a : Y ⟶ Y) (p : Y ⟶ Spec (CommRingCat.of F)) (x : F), a ≫ p = p →
      gs (𝟙 Y) y ⊤ (scal p x) = gs (𝟙 Y ≫ a) y ⊤ (scal p x) := by
    intro Y y a p x hap
    rw [← gs_pull (𝟙 Y) a y ⊤ trivial]
    conv_lhs => rw [← hap]
    rfl
  exact key y _ _ _ e

theorem fe_of_fe_kbar : GlobalFnsSt → AllPre fun {V} _ _ _ {_} {_} {_} _ _ U => ∀ k : ℕ, U.FE (Kbar V) k → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F], U.FE F k := by
  intro hG V _ _ _ hV D A G _ _ U k hK F _ _ t s hE
  obtain ⟨n, c, σ, f, hT, -, hs⟩ := hE
  have P := PullSec.pullEx V hV D A G U
  choose tK htK using fun i => ((P (Kbar V) (𝟙_ _) (toUnit _) k).1 (σ i)).exists
  choose sK hsK using fun i => ((P (Kbar V) (𝟙_ _) (toUnit _) k).2 (f i)).exists
  choose sF hsF using fun i => ((P F (𝟙_ _) (toUnit _) k).2 (f i)).exists
  have : IsAffine (𝟙_ (Over (Spec (CommRingCat.of V)))).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of V)))
  refine famFE_of_sum D F k n c s sF (fun α Z r z J hJ => ?_) fun i =>
    GlobalTheory.T.familyFunctionalEquation_field_change hG V D (𝟙_ _) k (f i) (Kbar V) F (toUnit _) (toUnit _) (sK i) (sF i) (toUnit_injective V _)
      (hsK i) (hsF i) (hK (tK i) (sK i)
        (IntExp.expF_of_expT V _ D A G U (Kbar V) k (σ i) (f i) (tK i) (sK i) (hT i) (htK i) (hsK i)))
  have w : (toUnit (TF (R := V) F) ▷ D.P.A).left ≫ (snd (𝟙_ _) D.P.A).left = (snd _ D.P.A).left :=
    congrArg CommaMorphism.left (whiskerRight_snd (toUnit (TF (R := V) F)) D.P.A)
  rw [hs α Z r (r ≫ (toUnit (TF (R := V) F) ▷ D.P.A).left) (by rw [Category.assoc, w]) z J hJ]
  refine Finset.sum_congr rfl fun i _ => congrArg (_ * ·) ?_
  rw [IntExp.sval_comp (f i α) _ r z J hJ, ← hsF i α (r z) _ (fun ψ => hJ (r ≫ ψ)),
    ← IntExp.sval_comp (sF i α) _ r z J hJ, Category.comp_id]

end GlobalTheory.UU.FEDesc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FiniteExponentBaseChangeFieldStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_exponent_base_change_field : GlobalFnsSt → AllPre fun {V} _ _ _ {_} {_} {_} _ _ U => ∀ k : ℕ, U.FE (Kbar V) k → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F], U.FE F k := by
  first | exact @GlobalTheory.UU.FEDesc.fe_of_fe_kbar | exact GlobalTheory.UU.FEDesc.fe_of_fe_kbar | (intros; apply GlobalTheory.UU.FEDesc.fe_of_fe_kbar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniformisationOfFunctionalEquationDegreeOn
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem exists_unif_of_fe_one : Laws → Laws2 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : PreU (IsLocalRing.maximalIdeal V) D.toPre A G), U.FE (Kbar V) 1 → ∃ U' : Unif (IsLocalRing.maximalIdeal V) D A G, Match U U'.toUnifPre := by
  intro hL hL2 V _ _ _ hV D A G _ _ U h1
  obtain ⟨U', hM⟩ := ToChart.exists_match V (IsLocalRing.maximalIdeal V) D A G U
  refine ⟨⟨U', fun k hk => ?_⟩, hM⟩
  have hb : U.FE (Kbar V) k := GlobalTheory.T.functional_equation_all_degrees_algebraic_closure hL hL2 V hV D.toPre A G U D.tau_bimult h1 k hk
  have hF : U.FE (FractionRing V) k :=
    GlobalTheory.T.finite_exponent_base_change_field hL.globalFns V hV D.toPre A G U k hb (FractionRing V)
  exact GlobalTheory.T.expBij_of_match_of_fam_expF hL hL2 V hV D A G U U' hM k hk hF
    (ExpOnto.exists_expF_of_fam hL hL2 V hV D.toPre A G U D.tau_bimult (FractionRing V) k hk hF)

end GlobalTheory.UU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniformisationOfFunctionalEquationDegreeOnStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformisation_of_functionalEquation_degreeOne : Laws → Laws2 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : PreU (IsLocalRing.maximalIdeal V) D.toPre A G), U.FE (Kbar V) 1 → ∃ U' : Unif (IsLocalRing.maximalIdeal V) D A G, Match U U'.toUnifPre := by
  first | exact @GlobalTheory.UU.exists_unif_of_fe_one | exact GlobalTheory.UU.exists_unif_of_fe_one | (intros; apply GlobalTheory.UU.exists_unif_of_fe_one <;> assumption)
end
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem unif_assembly : Laws → Laws2 → (AllSet fun {V} _ _ _ {A} {G} _ _ s => ∃ (D : DegPre V) (U : PreU (IsLocalRing.maximalIdeal V) D A G), U.P = s.P ∧ U.gen = s.gen) → (AllPre fun {V} _ _ _ {_} {A} {G} _ _ U => ∃ (D' : DegData V (IsLocalRing.maximalIdeal V)) (U' : PreU (IsLocalRing.maximalIdeal V) D'.toPre A G), U'.P = U.P ∧ U'.gen = U.gen ∧ U'.FE (Kbar V) 1) → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∃ (D : DegData V (IsLocalRing.maximalIdeal V)) (U : Unif (IsLocalRing.maximalIdeal V) D A G), U.LG = s.P.L ∧ U.gen = s.gen ∧ HEq U.cubG s.P.c := by
  intro h1 h2 hA hB V _ _ _ A G _ _ s
  obtain ⟨D, U, hP, hg⟩ := hA V A G s
  obtain ⟨D', U', hP', hg', hFE⟩ := hB V s.cdvr D A G U
  obtain ⟨U'', hM⟩ := GlobalTheory.T.exists_uniformisation_of_functionalEquation_degreeOne h1 h2 V s.cdvr D' A G U' hFE
  have e : U'.P = s.P := hP'.trans hP
  refine ⟨D', U'', ?_, ?_, ?_⟩
  · exact hM.LG.trans (by rw [e])
  · exact hM.gen.trans (hg'.trans hg)
  · exact hM.cub.trans (by rw [e])
end GlobalTheory.UU
