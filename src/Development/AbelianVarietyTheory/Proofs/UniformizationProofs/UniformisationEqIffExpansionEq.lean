module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianPartIsoIsMonHomAndRigidified
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidTorsionOfDataRigid
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdNeg
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEqIffExpansionEq
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEqIffExpansionEq
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace ExpansionFunction

open FieldBaseChange

theorem eq_iff_comb_eq_zero {R : Type} [CommRing R] [IsDomain R] {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)} {ε : K → ℤ}
    (π : Y ⟶ Spec (CommRingCat.of R)) (π' : Y' ⟶ Spec (CommRingCat.of (FractionRing R))) {p : Y' ⟶ Y}
    (hp : p ≫ π = π' ≫ jK R) (hφ : ∀ k, φ' k = p ≫ φ k) (hinj : ∀ W : Y.Opens, Function.Injective (p.app W))
    (π₀ : Y' ⟶ Spec (CommRingCat.of R)) (h₀ : π₀ = π' ≫ jK R)
    {s s' : LB.Sec (LB.LinComb L φ' ε)} {σ σ' : LB.Sec (LB.LinComb L φ ε)} {r r' : R} (hr : r ≠ 0) (hr' : r' ≠ 0)
    (H : GeneratorPullback.SecScal L φ' ε s φ ε σ p (scal π₀ r)) (H' : GeneratorPullback.SecScal L φ' ε s' φ ε σ' p (scal π₀ r')) :
    s = s' ↔ ∀ j, ∑ i : Fin 2, resTop _ (scal π (![r', -r] i)) * (![σ, σ'] i).f j = 0 := by
  let t : SecOver π' (LB.LinComb L φ' ε) := s
  let t' : SecOver π' (LB.LinComb L φ' ε) := s'
  let τ : SecOver π (LB.LinComb L φ ε) := σ
  let τ' : SecOver π (LB.LinComb L φ ε) := σ'
  have E : pullOver L ε hp hφ τ = algebraMap R (FractionRing R) r • t :=
    (secScal_iff hp hφ hL t τ π₀ _ h₀ r).1 H
  have E' : pullOver L ε hp hφ τ' = algebraMap R (FractionRing R) r' • t' :=
    (secScal_iff hp hφ hL t' τ' π₀ _ h₀ r').1 H'
  have hi : ∀ x : SecOver π (LB.LinComb L φ ε), pullOver L ε hp hφ x = 0 → x = 0 := fun x hx =>
    SecOver.ext _ _ fun j => hinj _ (by
      have e := congrArg (chartFun π' _ j) hx
      have hw := wchart_eq (L := L) hφ j
      refine Geo.Tor.fn_ext fun y hy => ?_
      have hy' : (𝟙 Y' : Y' ⟶ Y') y ∈ LB.wchart L φ' j := hw.ge hy
      have e₂ := congrArg (Geo.Tor.gs (𝟙 Y') y (LB.wchart L φ' j)) e
      refine (Geo.Tor.gs_pull _ p y _ hy _).trans ((gs_pullFn hp hw.le _ (𝟙 Y') y hy').symm.trans
        (e₂.trans ((gs_zero' _ y _ hy').trans ?_)))
      exact ((Geo.Tor.gs_pull _ p y _ hy _).trans (gs_zero' (𝟙 Y' ≫ p) y (LB.wchart L φ j) hy)).symm)
  have ha : algebraMap R (FractionRing R) r ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 hr
  have ha' : algebraMap R (FractionRing R) r' ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 hr'
  have key : pullOver L ε hp hφ (r' • τ + (-r) • τ') =
      (algebraMap R (FractionRing R) r * algebraMap R (FractionRing R) r') • (t - t') := by
    rw [map_add (f := _), map_smulₛₗ, map_smulₛₗ, E, E', map_neg, smul_smul, smul_smul, smul_sub, sub_eq_add_neg,
      ← neg_smul, neg_mul, mul_comm (algebraMap R (FractionRing R) r')]
  have main : t = t' ↔ r' • τ + (-r) • τ' = 0 := by
    constructor
    · intro h
      exact hi _ (by rw [key, h, sub_self, smul_zero])
    · intro h
      rw [h, map_zero] at key
      exact sub_eq_zero.1 ((smul_eq_zero_iff_right (mul_ne_zero ha ha')).1 key.symm)
  refine main.trans ⟨fun h j => ?_, fun h => SecOver.ext _ _ fun j => ?_⟩
  · rw [Fin.sum_univ_two]
    exact congrArg (chartFun π _ j) h
  · have := h j
    rw [Fin.sum_univ_two] at this
    exact this

end ExpansionFunction

theorem eq_iff_expansion_eq : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GeometricallyConnected G.hom] (U : UnifPre I D A G) (k : ℕ) (s s' : U.SecK k) (F F' : Fam D.toPre (FractionRing R) k), U.Expands k s F → U.Expands k s' F' → (s = s' ↔ F = F') := by
  intro R _ _ I hR D A G _ _ hG U k s s' F F' ⟨r, hr, σ, f, hσ, hf, hE⟩ ⟨r', hr', σ', f', hσ', hf', hE'⟩
  have := U.smooth
  have := D.toPre.P.isAb.smooth
  have : Flat G.hom := inferInstance
  have : Flat D.toPre.P.A.hom := inferInstance
  have e : (TF (R := R) (FractionRing R)).hom = jK R := by
    show Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]; rfl
  have hd : IsDominant (TF (R := R) (FractionRing R)).hom := DVR.GC.isDominant_jFR (V := R) (FractionRing R)
  have h₁ : IsSchemeTheoreticallyDominant (TF (R := R) (FractionRing R)).hom := .of_isDominant _
  have h₂ : IsSchemeTheoreticallyDominant (jK R) := e ▸ h₁
  have h₅ : QuasiCompact (jK R) :=
    inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))
  have h₃ : QuasiCompact (TF (R := R) (FractionRing R)).hom := e ▸ h₅
  have h₄ : IsSchemeTheoreticallyDominant (pullback.fst G.hom (jK R)) :=
    .of_isPullback (IsPullback.of_hasPullback G.hom (jK R)).flip
  have hs := ExpansionFunction.eq_iff_comb_eq_zero U.LG.isLB G.hom (pullback.snd G.hom (jK R))
    pullback.condition (fun _ => (Category.comp_id _).symm) (pullback.fst G.hom (jK R)).app_injective _ rfl
    hr hr' hσ hσ'
  have hw : (DegPre.BF D.toPre (FractionRing R)).hom =
      (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ jK R := by
    rw [← e]; exact (Over.w _).symm
  have hF := fun α => ExpansionFunction.eq_iff_comb_eq_zero D.toPre.P.isLB D.toPre.P.A.hom
    (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left
    ((Over.w (DegPre.prB D.toPre (FractionRing R))).trans hw) (DVR.GC.famφ_eq D.toPre (FractionRing R) α)
    (pullback.snd (TF (R := R) (FractionRing R)).hom D.toPre.P.A.hom).app_injective _ hw hr hr' (hf α) (hf' α)
  have H := comb_eq_zero_iff_expansion_comb_eq_zero R I hR D A G U k 2 ![r', -r] ![σ, σ'] ![f, f']
    (fun i => by fin_cases i; exacts [hE, hE'])
  have hc : ∀ α (i : Fin 2), (![f, f'] i) α = ![f α, f' α] i := fun α i => by fin_cases i <;> rfl
  simp only [hc] at H
  constructor
  · intro h
    exact DVR.fam_ext fun α j => by rw [(hF α).2 (H.1 (hs.1 h) α)]
  · intro h
    exact hs.2 (H.2 hG fun α => (hF α).1 (by rw [h]))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEqIffExpansionEqStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.uniformisation_eq_iff_expansion_eq : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GeometricallyConnected G.hom] (U : UnifPre I D A G) (k : ℕ) (s s' : U.SecK k) (F F' : Fam D.toPre (FractionRing R) k), U.Expands k s F → U.Expands k s' F' → (s = s' ↔ F = F') := by
  first | exact @GlobalTheory.eq_iff_expansion_eq | exact GlobalTheory.eq_iff_expansion_eq | (intros; apply GlobalTheory.eq_iff_expansion_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsShiftGen
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.QkShift

section Alg

variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ)
include h

theorem cubN_one_mul (k : ℕ) (b m x : A) :
    cubN θ k 1 (b * m) x * θ m b x ^ k = θ (m ^ k) (b ^ k) x * cubN θ k 1 b x * cubN θ k 1 m x := by
  induction k with
  | zero => simp [cubN, h.face]
  | succ k ih =>
    have c₁ := h.coc (b ^ k * m ^ k) m b x
    have c₂ := h.coc (b ^ k) (m ^ k) m x
    have c₃ := h.coc (m ^ k * m) (b ^ k) b x
    rw [mul_comm m b] at c₁
    rw [h.s01 (b ^ k) (m ^ k), h.s01 (b ^ k) (m ^ k * m)] at c₂
    rw [mul_comm (m ^ k * m) (b ^ k), ← _root_.mul_assoc] at c₃
    simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
    rw [mul_pow b m k, pow_succ m, pow_succ b, pow_succ (θ m b x)]
    apply Additive.ofMul.injective
    have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
    have a₀ := E ih; have a₁ := E c₁; have a₂ := E c₂; have a₃ := E c₃
    simp only [ofMul_mul] at a₀ a₁ a₂ a₃ ⊢
    linear_combination (norm := abel) a₀ - a₁ + a₂ + a₃

theorem cub_shift (k : ℕ) (a m b x : A) (Sa Sm Sam Sq τ P w : U) (h₁ : Sam * cubN θ k a m b = Sa * Sm ^ k)
    (h₂ : Sq * θ a b m = Sa * τ) :
    cubN θ k a m (x * b) * (θ a (x * b) m)⁻¹ * (τ * P) *
        (cubN θ k (a * m ^ k) b x * (θ (a * m ^ k) x b)⁻¹ * (Sam * w)) =
      cubN θ k a (b * m) x * (θ a x (b * m))⁻¹ * (Sq * (w * P * Sm ^ k)) := by
  have e₁ := h.N_add k a m x b
  have e₂ := cubN_one_mul h k b m x
  have e₃ := h.N_split k (a * m ^ k) b x
  have e₄ := h.N_split k a (b * m) x
  have e₅ := h.N_split k a m x
  have e₆ := h.coc a (m ^ k) (b ^ k) x
  have e₇ := h.coc x b m a
  rw [h.s12 m x b] at e₁
  rw [← mul_pow, mul_comm m b] at e₆
  rw [h.s12 (x * b), h.s01 (x * b), h.s12 x b a, h.s01 x a b, h.s12 x (b * m), h.s01 x a, h.s12 b m a,
    h.s01 b a m] at e₇
  apply Additive.ofMul.injective
  have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
  have a₁ := E e₁; have a₂ := E e₂; have a₃ := E e₃; have a₄ := E e₄; have a₅ := E e₅; have a₆ := E e₆
  have a₇ := E e₇; have c₁ := E h₁; have c₂ := E h₂
  simp only [ofMul_mul, ofMul_inv] at *
  linear_combination (norm := abel) a₁ - a₂ + a₃ - a₄ + a₅ + a₆ - a₇ + c₁ - c₂

end Alg

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem trPt_comp (m m' : TF (R := R) F ⟶ D.P.A) :
    DegPre.trPt D F m ≫ DegPre.trPt D F m' = DegPre.trPt D F (m * m') := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, tr_fst, tr_fst, tr_fst]
  · refine Eq.trans ?_ (tr_pr D F (m * m')).symm
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (tr_pr D F m')).trans ?_)
    rw [MonObj.comp_mul, tr_pr, ← Category.assoc, tr_fst, MonObj.comp_mul, _root_.mul_assoc]

theorem exists_shift_gen (n : ℕ) (g : GtPtF D F) (z : D.X) (b' : TF (R := R) F ⟶ D.P.A)
    (hb : b' = g.b * cP D _ z)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε n))) (hw : w.IsGen) :
    ∃ w₂ : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F b') (DegPre.lineε n)), w₂.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (y : Z) (J), Good D.P.L y J →
        val w₂ r y J = val w r y J *
          (val (GeneratorPullback.powGen D.P.L _ _ (D.psi z) n) (r ≫ jFK (R := R) F) y J *
            val (GeneratorPullback.powGen D.P.L _ _ D.rigK n) (r ≫ jFK (R := R) F) y J) * val (g.s z) r y J ^ n := by
  subst hb
  obtain ⟨w₂, h₂, v₂⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F (g.b * cP D _ z)) (ε' := DegPre.lineε n)
    (fun U _ h => by
      have a₁ : ∀ χ, jFK (R := R) F ≫ D.xK χ = (cP D (TF (R := R) F) χ).left := fun χ => (Category.assoc _ _ _).symm
      have a₂ : jFK (R := R) F ≫ (toUnit (TK R)).left ≫ eSec D.P.A = (1 : TF (R := R) F ⟶ D.P.A).left :=
        (Category.assoc _ _ _).symm
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, a₁, a₂]
      rw [Fin.prod_univ_four, Fin.prod_univ_two, Fin.prod_univ_two]
      show h (1 : TF (R := R) F ⟶ D.P.A).left ^ (n : ℤ) * h g.b.left ^ (-(n : ℤ)) * _ *
        (h (cP D _ z * g.b).left ^ ((n : ℤ) * -1) * h (cP D _ z).left ^ ((n : ℤ) * 1) * h g.b.left ^ ((n : ℤ) * 1) *
          h (1 : TF (R := R) F ⟶ D.P.A).left ^ ((n : ℤ) * -1)) =
        h (1 : TF (R := R) F ⟶ D.P.A).left ^ (n : ℤ) * h (g.b * cP D _ z).left ^ (-(n : ℤ))
      rw [mul_comm g.b]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ w (LB.pullGen D.P.L _ _
      (LB.mulGen D.P.L _ _ _ _ (GeneratorPullback.powGen D.P.L _ _ (D.psi z) n) (GeneratorPullback.powGen D.P.L _ _ D.rigK n)) (jFK (R := R) F)))
      (GeneratorPullback.powGen D.P.L _ _ (g.s z) n))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hw (pullGen_isGen _ _ _ _
      (mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ (D.psi_gen z) n)
        (powGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.rig_gen _) n)) _)) (powGen_isGen _ _ _ _ (g.isGen z) n))
  refine ⟨w₂, h₂, fun Z r y J hJ => (v₂ Z r y J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans (val_mul hJ _ _ _)))) ?_))⟩
  exact map_pow _ _ _

theorem qk_shift : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (n : ℕ), 1 ≤ n → ∀ (p q : QkPt D F n) (z : D.X) (h : GtPtF D F), q.y = p.y + n • z → GtPtF.IsIota z h → GtPtF.IsAdd p.g h q.g → ∀ w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε n)), w.IsGen → ∃ w₂ : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F q.g.b) (DegPre.lineε n)), w₂.IsGen ∧ ∀ s s' : Fam D F n, PhiRel D F n p w s s' → PhiRel D F n q w₂ s s' := by
  intro hG R _ _ D _ F _ _ n _ p q z h hy hι hadd w hw
  have hh : h.b = cP D _ z := hι.1
  have hb : q.g.b = p.g.b * cP D _ z := hadd.1.trans (congrArg (p.g.b * ·) hh)
  obtain ⟨w₂, h₂, v₂⟩ := exists_shift_gen n p.g z q.g.b hb w hw
  refine ⟨w₂, h₂, fun s t H => ?_⟩
  rw [phiRel_iff hG p w hw] at H
  rw [phiRel_iff hG q w₂ h₂]
  intro α β hβ T ρ y J hJ
  have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
  have e₁ := H (α + n • z) β (by rw [← hβ, hy]; abel) T ρ y J hJ
  obtain ⟨⟨u', hu', hc'⟩, hv'⟩ := gen_fe (D := D) (F := F) hG n z α
  have e₄ := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u').1 (s.fe z α u' hu' hc') _
    (ρ ≫ DegPre.trPt D F p.g.b).left y J hJ
  rw [hv' u' hu' hc' _ (ρ ≫ DegPre.trPt D F p.g.b) y J hJ, trF_eq, ← Over.comp_left, Category.assoc, trPt_comp, ← hb,
    Category.assoc, tr_fst] at e₄
  rw [e₁, e₄, _root_.mul_assoc, ← Units.val_mul]
  congr 2
  have t₁ := gt_nsmul (ρ ≫ fst (TF (R := R) F) D.P.A) hJ p.g α z n
  have t₂ := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl
    (val_cub D.cub (ρ ≫ fst (TF (R := R) F) D.P.A) hJ _ _ _))).symm.trans
    ((val_corr hJ (hadd.2 α) (ρ ≫ fst (TF (R := R) F) D.P.A).left).trans ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl ((val_corr hJ (hι.2 α) _).trans (val_pull hJ _ _ _)))))
  have c₁ : (ρ ≫ fst (TF (R := R) F) D.P.A) ≫ DegPre.cF D F α = cP D T α := comp_cP D _ α
  have c₂ : (ρ ≫ fst (TF (R := R) F) D.P.A) ≫ cP D _ z = cP D T z := comp_cP D _ z
  rw [hh, c₁, c₂] at t₂
  have key := cub_shift C n _ _ _ (ρ ≫ DegPre.prB D F) _ _ _ _ _
    (val (GeneratorPullback.powGen D.P.L _ _ (D.psi z) n) ((ρ ≫ fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F) y J *
      val (GeneratorPullback.powGen D.P.L _ _ D.rigK n) ((ρ ≫ fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F) y J)
    (val w (ρ ≫ fst (TF (R := R) F) D.P.A).left y J) t₁ t₂
  have d₁ : (ρ ≫ DegPre.trPt D F p.g.b) ≫ fst _ _ ≫ cP D _ z = cP D T z := by
    rw [← Category.assoc]; exact comp_cP D _ z
  have d₂ : (ρ ≫ DegPre.trPt D F p.g.b) ≫ DegPre.prB D F =
      (ρ ≫ DegPre.prB D F) * ((ρ ≫ fst (TF (R := R) F) D.P.A) ≫ p.g.b) := by
    rw [Category.assoc, tr_pr, MonObj.comp_mul, Category.assoc]
  have d₃ : ρ ≫ fst _ _ ≫ q.g.b = ((ρ ≫ fst (TF (R := R) F) D.P.A) ≫ p.g.b) * cP D T z := by
    rw [← Category.assoc, hb, MonObj.comp_mul, c₂]
  rw [val_famMult _ hJ, val_mul hJ, val_mul hJ, v₂ _ _ y J hJ, uVal, uVal, uVal, d₁, d₂, d₃, cPoint_add, cPoint_nsmul,
    ← Category.assoc ρ]
  exact key

end GlobalTheory.QkShift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PullbackSectionEndomorphismExpansion
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PullbackSectionEndomorphismExpansion
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.PullInt

theorem oneLeft {S : Scheme.{0}} {X M : Over S} [GrpObj M] : (1 : X ⟶ M).left = X.hom ≫ eSec M := by
  have h : (toUnit X).left = X.hom := by simpa using Over.w (toUnit X)
  rw [Hom.one_def, Over.comp_left, h]; rfl

theorem exists_zpow {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (a b : ℕ) :
    ∃ t' : LB.Gen (LB.LinComb L φ (fun i => ((a : ℤ) - b) * ε i)), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → val t' r z J = val t r z J ^ ((a : ℤ) - b) := by
  obtain ⟨t', h₁, h₂⟩ := exists_gen hL (φ' := φ) (ε' := fun i => ((a : ℤ) - b) * ε i) (fun U _ h => by
      rw [Fintype.prod_sum_type, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [← zpow_add]; congr 1; ring)
    (LB.mulGen L _ _ _ _ (GeneratorPullback.powGen L φ ε t a) (LB.invGen L _ _ (GeneratorPullback.powGen L φ ε t b)))
    (mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ ht a) (invGen_isGen _ _ _ _ (powGen_isGen _ _ _ _ ht b)))
  refine ⟨t', h₁, fun Z r z J hJ => (h₂ Z r z J hJ).trans ((val_mul hJ _ _ _).trans ?_)⟩
  rw [val_inv, zpow_sub, zpow_natCast, zpow_natCast]
  exact congrArg₂ (fun u v => u * v⁻¹) (map_pow _ _ _) (map_pow _ _ _)

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

theorem rig_val (e : ℕ) {Z : Scheme.{0}} (s : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) {z : Z}
    {N : (Z ⟶ G.left) → U.LG.L.ι} {J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι}
    (hN : Good U.LG.L z N) (hJ : Good D.toPre.P.L z J) (o : Z ⟶ (thickObj R I e G).left)
    (ho : o = s ≫ eSec (thickObj R I e G)) :
    rigV D.toPre (s ≫ thick R I e) z J =
      wv U e o z (J (o ≫ pGl U e)) (N (o ≫ fGl I G e)) *
        val (L := U.LG.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.LG.rig (s ≫ thick R I e) z N := by
  subst ho
  have hp : (s ≫ eSec (thickObj R I e G)) ≫ pGl U e = (s ≫ thick R I e) ≫ eSec D.toPre.P.A :=
    (Category.assoc _ _ _).trans ((congrArg (s ≫ ·) (UnitValue.eSec_pGl U e)).trans
      (Category.assoc _ _ _).symm)
  have hf : (s ≫ eSec (thickObj R I e G)) ≫ fGl I G e = (s ≫ thick R I e) ≫ eSec G :=
    (Category.assoc _ _ _).trans ((congrArg (s ≫ ·) (UnitValue.eSec_fGl (G := G) e)).trans
      (Category.assoc _ _ _).symm)
  rw [hp, hf, rigV]
  obtain ⟨j, hj⟩ : ∃ j, J ((s ≫ thick R I e) ≫ eSec D.toPre.P.A) = j := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k, N ((s ≫ thick R I e) ≫ eSec G) = k := ⟨_, rfl⟩
  have mj : ((s ≫ thick R I e) ≫ eSec D.toPre.P.A) z ∈ D.toPre.P.L.U j := hj ▸ hJ _
  have mk : ((s ≫ thick R I e) ≫ eSec G) z ∈ U.LG.L.U k := hk ▸ hN _
  rw [val_of _ _ z J (fun _ => j) (fun _ => hj), val_of _ _ z N (fun _ => k) (fun _ => hk), hj, hk]
  have m₁ : s z ∈ eSec (thickObj R I e G) ⁻¹ᵁ
      ((D.toPre.P.L.pull (U.gt e).pG.left).U (fun _ => j) ⊓ (U.LG.L.pull (fstG I e G).left).U (fun _ => k)) :=
    ⟨mem_pull.2 ((congrArg (fun q => q z ∈ D.toPre.P.L.U j) hp).mpr mj),
      mem_pull.2 ((congrArg (fun q => q z ∈ U.LG.L.U k) hf).mpr mk)⟩
  have m₂ : s z ∈ thick R I e ⁻¹ᵁ (U.LG.L.pull (eSec G)).U (fun _ => k) := mem_pull.2 mk
  have m₃ : s z ∈ thick R I e ⁻¹ᵁ (D.toPre.P.L.pull (eSec D.toPre.P.A)).U (fun _ => j) := mem_pull.2 mj
  have W := congrArg (gm s z _) (U.w_rig e (fun _ => j, fun _ => k) (_ ⊓ _ ⊓ _) (inf_le_left.trans inf_le_left)
    (inf_le_left.trans inf_le_right) inf_le_right)
  exact ((gm_res _ z _ (by exact ⟨⟨m₁, m₂⟩, m₃⟩) _).trans (gm_pull _ _ z _ m₃ _)).symm.trans (W.symm.trans
    ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res _ z _ (by exact ⟨⟨m₁, m₂⟩, m₃⟩) _).trans (gm_pull _ _ z _ m₁ _))
      ((gm_res _ z _ (by exact ⟨⟨m₁, m₂⟩, m₃⟩) _).trans (gm_pull _ _ z _ m₂ _)))))

variable {U} (E : EndU U)

theorem act_fGl (e : ℕ) :
    ((Over.pullback (thick R I e)).map E.aG).left ≫ fGl I G e = fGl I G e ≫ E.aG.left :=
  pullback.lift_fst _ _ _

theorem act_pGl (e : ℕ) :
    ((Over.pullback (thick R I e)).map E.aG).left ≫ pGl U e = pGl U e ≫ E.aB.left := by
  have h1 := congrArg (fun f => f.left) (E.q_lin e)
  simp only [Over.comp_left] at h1
  simp only [GtCoord.pG, Over.comp_left, Over.map_map_left, DegPre.prBe, Over.homMk_left]
  rw [← Category.assoc, h1, Category.assoc, Category.assoc]
  congr 1
  simp only [Over.pullback_map_left, pullback.lift_fst]

theorem exists_secG (k' k : ℕ) (β : LB.Gen (LB.LinComb U.LG.L (K := Fin 3) ![𝟙 _, E.aG.left, (1 : G ⟶ G).left]
    ![(k' : ℤ), -(k : ℤ), (k : ℤ) - k'])) (hβ : β.IsGen) (σ : H0 U.LG.L k) :
    ∃ σ' : H0 U.LG.L k', ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J), Good U.LG.L z J →
      sval σ' r z J = sval σ (r ≫ E.aG.left) z J * (val β r z J * val (L := U.LG.L) (φ := fun _ : PUnit => eSec G)
        (ε := fun _ => 1) U.LG.rig (r ≫ G.hom) z J ^ ((k' : ℤ) - k)).val := by
  obtain ⟨ρ, hρ, vρ⟩ := exists_zpow U.LG.isLB (LB.pullGen U.LG.L (fun _ : PUnit => eSec G) (fun _ => 1) U.LG.rig G.hom)
    (pullGen_isGen _ _ _ _ U.LG.rigGen _) k' k
  obtain ⟨s, hs⟩ := exists_sec U.LG.isLB (φ' := fun _ : Fin 1 => 𝟙 G.left) (ε' := fun _ => (k' : ℤ)) (fun V _ h => by
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_three, Matrix.cons_val, Category.comp_id,
        Fintype.prod_unique, oneLeft]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
      module)
    (pullMulSec σ E.aG.left (LB.mulGen U.LG.L _ _ _ _ β ρ) (mulGen_isGen _ _ _ _ _ _ _ hβ hρ))
  refine ⟨s, fun Z r z J hJ => (hs Z r z J hJ).trans ((sval_pullMulSec _ _ _ _ r z hJ).trans ?_)⟩
  rw [val_mul hJ, vρ Z r z J hJ, val_pull hJ]

theorem exists_secB (k' k : ℕ) (κ : LB.Gen (kapLB D.toPre E.aB k' k)) (hκ : κ.IsGen) (χ : D.toPre.X)
    (f : D.toPre.SecB k χ) :
    ∃ g : D.toPre.SecB k' (E.h χ), ∀ (Z : Scheme.{0}) (r : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J →
      sval g r z J = sval f (r ≫ E.aB.left) z J * (val κ r z J *
        rigV D.toPre (r ≫ D.toPre.P.A.hom) z J ^ ((k' : ℤ) - k) * val (E.u χ) r z J).val := by
  obtain ⟨ρ, hρ, vρ⟩ := exists_zpow D.toPre.P.isLB (LB.pullGen D.toPre.P.L (fun _ : PUnit => eSec D.toPre.P.A)
    (fun _ => 1) D.toPre.rig D.toPre.P.A.hom) (pullGen_isGen _ _ _ _ D.toPre.rig_gen _) k' k
  obtain ⟨s, hs⟩ := exists_sec D.toPre.P.isLB (φ' := D.toPre.famφB (E.h χ)) (ε' := DegPre.famε k') (fun V _ h => by
      have p₁ := SectionScalarValuation.prod_famB D.toPre E.aB χ k h
      have p₂ := SectionScalarValuation.prod_famB D.toPre (𝟙 _) (E.h χ) k' h
      have e₃ : ∀ i, Over.Hom.left (𝟙 D.toPre.P.A) ≫ D.toPre.famφB (E.h χ) i = D.toPre.famφB (E.h χ) i :=
        fun i => by simp
      simp only [e₃] at p₂
      have p₃ : ∏ i, h (D.toPre.Oφ (𝟙 _) (E.h χ) i) ^ Oε i =
          h (𝟙 D.toPre.P.A * SectionScalarValuation.cQ D.toPre _ (E.h χ)).left ^ (1 : ℤ) * h (SectionScalarValuation.cQ D.toPre _ (E.h χ)).left ^ (-1 : ℤ) *
            h (Over.Hom.left (𝟙 D.toPre.P.A)) ^ (-1 : ℤ) * h (1 : D.toPre.P.A ⟶ D.toPre.P.A).left ^ (1 : ℤ) := by
        rw [Fin.prod_univ_four]; rfl
      have p₄ : ∏ i, h (D.toPre.Oφ E.aB χ i) ^ Oinvε i =
          h (E.aB * SectionScalarValuation.cQ D.toPre _ χ).left ^ (-1 : ℤ) * h (SectionScalarValuation.cQ D.toPre _ χ).left ^ (1 : ℤ) *
            h E.aB.left ^ (1 : ℤ) * h (1 : D.toPre.P.A ⟶ D.toPre.P.A).left ^ (-1 : ℤ) := by
        rw [Fin.prod_univ_four]; rfl
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [p₁, p₂, p₃, p₄]
      simp only [Fin.prod_univ_three, Matrix.cons_val, Fintype.prod_unique, oneLeft, Over.id_left]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
      module)
    (pullMulSec f E.aB.left (LB.mulGen D.toPre.P.L _ _ _ _ (LB.mulGen D.toPre.P.L _ _ _ _ κ ρ) (E.u χ))
      (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hκ hρ) (E.u_norm χ).1))
  refine ⟨s, fun Z r z J hJ => (hs Z r z J hJ).trans ((sval_pullMulSec _ _ _ _ r z hJ).trans ?_)⟩
  rw [val_mul hJ, val_mul hJ, vρ Z r z J hJ, val_pull hJ, rigV]

theorem alg {Γ : Type} [CommRing Γ] (k' k : ℕ) (wx wa wo β κ ρG ρB : Γˣ) (s : Γ)
    (h₁ : κ = β * wx ^ (k' : ℤ) * wa ^ (-(k : ℤ)) * wo ^ ((k : ℤ) - k')) (h₂ : ρB = wo * ρG) :
    (wx ^ k').val * (s * (β * ρG ^ ((k' : ℤ) - k)).val) = (κ * ρB ^ ((k' : ℤ) - k)).val * ((wa ^ k).val * s) := by
  have : wx ^ k' * (β * ρG ^ ((k' : ℤ) - k)) = κ * ρB ^ ((k' : ℤ) - k) * wa ^ k := by
    rw [h₁, h₂]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_pow]
    module
  rw [mul_comm s, ← _root_.mul_assoc, ← Units.val_mul, this, Units.val_mul, _root_.mul_assoc]

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (E : EndU U), Function.Injective E.h → ∀ (k' k : ℕ) (β : LB.Gen (LB.LinComb U.LG.L (K := Fin 3) ![𝟙 _, E.aG.left, (1 : G ⟶ G).left] ![(k' : ℤ), -(k : ℤ), (k : ℤ) - k'])), β.IsGen → ∀ κ : LB.Gen (kapLB D.toPre E.aB k' k), κ.IsGen → (∀ (e : ℕ) (Z : Scheme.{0}) (x o : Z ⟶ (thickObj R I e G).left) (z : Z) (JG) (J), Good U.LG.L z JG → Good D.toPre.P.L z J → o = x ≫ (1 : thickObj R I e G ⟶ thickObj R I e G).left → ∀ W : (Z ⟶ (thickObj R I e G).left) → (Z.presheaf.stalk z)ˣ, (∀ y, W y = gw (U.w e) y z (J (y ≫ (U.gt e).pG.left)) (fun _ => JG (y ≫ (fstG I e G).left))) → val κ (x ≫ (U.gt e).pG.left) z J = val β (x ≫ (fstG I e G).left) z JG * W x ^ (k' : ℤ) * W (x ≫ ((Over.pullback (thick R I e)).map E.aG).left) ^ (-(k : ℤ)) * W o ^ ((k : ℤ) - k')) → ∀ (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α), (∀ e, U.ExpandsAt e k σ f) → ∃ (σ' : H0 U.LG.L k') (f' : ∀ α : D.toPre.X, D.toPre.SecB k' α), (∀ e, U.ExpandsAt e k' σ' f') ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J), Good U.LG.L z J → sval σ' r z J = sval σ (r ≫ E.aG.left) z J * (val β r z J * val (L := U.LG.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.LG.rig (r ≫ G.hom) z J ^ ((k' : ℤ) - k)).val) ∧ (∀ (χ : D.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J → sval (f' (E.h χ)) r z J = sval (f χ) (r ≫ E.aB.left) z J * (val κ r z J * rigV D.toPre (r ≫ D.toPre.P.A.hom) z J ^ ((k' : ℤ) - k) * val (E.u χ) r z J).val) ∧ ∀ b, b ∉ Set.range E.h → ∀ j, (f' b).f j = 0 := by
  classical
  intro R _ _ I D A G _ _ U E hinj k' k β hβ κ hκ H σ f hf
  obtain ⟨σ', hσ'⟩ := exists_secG E k' k β hβ σ
  have key : ∀ b, ∃ s : D.toPre.SecB k' b, (∀ χ, b = E.h χ → ∀ (Z : Scheme.{0}) (r : Z ⟶ D.toPre.P.A.left) (z : Z) (J),
      Good D.toPre.P.L z J → sval s r z J = sval (f χ) (r ≫ E.aB.left) z J * (val κ r z J *
        rigV D.toPre (r ≫ D.toPre.P.A.hom) z J ^ ((k' : ℤ) - k) * val (E.u χ) r z J).val) ∧
      (b ∉ Set.range E.h → ∀ j, s.f j = 0) := by
    intro b
    by_cases hb : b ∈ Set.range E.h
    · obtain ⟨χ, rfl⟩ := hb
      obtain ⟨g, hg⟩ := exists_secB E k' k κ hκ χ (f χ)
      refine ⟨g, fun χ' e => ?_, fun h => (h ⟨χ, rfl⟩).elim⟩
      obtain rfl := hinj e
      exact hg
    · exact ⟨SecOps.secZero, fun χ e => (hb ⟨χ, e.symm⟩).elim, fun _ _ => rfl⟩
  choose f' hf₁ hf₂ using key
  refine ⟨σ', f', fun e => ?_, hσ', fun χ => hf₁ _ χ rfl, hf₂⟩
  obtain ⟨S, hS⟩ := expandsAt_val U e k σ f (hf e)
  refine expandsAt_of_val U e k' σ' f' (S.image E.h) fun y J hJ => ?_
  obtain ⟨b₁, b₂⟩ := hS _ ((Over.pullback (thick R I e)).map E.aG).left y J hJ
  simp only [act_pGl E e, act_fGl E e] at b₁
  refine ⟨fun α hα => ?_, fun jL hL => ?_⟩
  · by_cases hb : α ∈ Set.range E.h
    · obtain ⟨χ, rfl⟩ := hb
      rw [hf₁ _ χ rfl _ _ y J hJ, b₁ χ fun h => hα (Finset.mem_image_of_mem _ h), zero_mul]
    · exact (congrArg (gs _ y _) (hf₂ α hb _)).trans (gs_zero _ y _ (hJ.mem _ _))
  · obtain ⟨JG, hJG, eJ⟩ := exists_good U.LG.L U.LG.isLB y (fun _ : Unit => fGl I G e) (fun _ => jL)
      (fun _ _ _ => rfl) (fun _ => hL)
    obtain rfl : JG (fGl I G e) = jL := eJ ()
    have c₁ := b₂ _ (hJG (((Over.pullback (thick R I e)).map E.aG).left ≫ fGl I G e))
    have c₂ := H e _ (𝟙 _) _ y JG J hJG hJ rfl
      (fun x => wv U e x y (J (x ≫ pGl U e)) (JG (x ≫ fGl I G e))) (fun _ => rfl)
    have c₃ := rig_val U e (thickObj R I e G).hom hJG hJ _ oneLeft
    have c₄ := hσ' _ (fGl I G e) y JG hJG
    have sv_eq : ∀ (n : ℕ) (τ : H0 U.LG.L n) (q : (thickObj R I e G).left ⟶ G.left),
        sval τ q y JG = sv U n τ q y (JG q) := fun n τ q =>
      sval_of τ q y JG (fun _ => JG q) (fun _ => by rw [Category.comp_id])
    have w₁ : fGl I G e ≫ G.hom = (thickObj R I e G).hom ≫ thick R I e := Over.w (fstG I e G)
    have w₂ : pGl U e ≫ D.toPre.P.A.hom = (thickObj R I e G).hom ≫ thick R I e := Over.w (U.gt e).pG
    simp only [Category.id_comp] at c₂
    rw [sv_eq, sv_eq, w₁, ← act_fGl E e] at c₄
    rw [c₄, Finset.sum_image fun _ _ _ _ h => hinj h]
    refine (alg k' k _ _ _ _ _ _ _ _ c₂ c₃).trans ?_
    rw [c₁, Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    have t := E.t_lin e χ _ (𝟙 _) y J hJ
    simp only [Category.id_comp] at t
    rw [hf₁ _ χ rfl _ _ y J hJ, w₂, act_pGl E e]
    refine (congrArg (fun u : ((thickObj R I e G).left.presheaf.stalk y)ˣ => _ * (_ * u.val)) t).trans ?_
    simp only [Units.val_mul]
    ring

end GlobalTheory.PullInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PullbackSectionEndomorphismExpansionStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_section_endomorphism_expansion : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (E : EndU U), Function.Injective E.h → ∀ (k' k : ℕ) (β : LB.Gen (LB.LinComb U.LG.L (K := Fin 3) ![𝟙 _, E.aG.left, (1 : G ⟶ G).left] ![(k' : ℤ), -(k : ℤ), (k : ℤ) - k'])), β.IsGen → ∀ κ : LB.Gen (kapLB D.toPre E.aB k' k), κ.IsGen → (∀ (e : ℕ) (Z : Scheme.{0}) (x o : Z ⟶ (thickObj R I e G).left) (z : Z) (JG) (J), Good U.LG.L z JG → Good D.toPre.P.L z J → o = x ≫ (1 : thickObj R I e G ⟶ thickObj R I e G).left → ∀ W : (Z ⟶ (thickObj R I e G).left) → (Z.presheaf.stalk z)ˣ, (∀ y, W y = gw (U.w e) y z (J (y ≫ (U.gt e).pG.left)) (fun _ => JG (y ≫ (fstG I e G).left))) → val κ (x ≫ (U.gt e).pG.left) z J = val β (x ≫ (fstG I e G).left) z JG * W x ^ (k' : ℤ) * W (x ≫ ((Over.pullback (thick R I e)).map E.aG).left) ^ (-(k : ℤ)) * W o ^ ((k : ℤ) - k')) → ∀ (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α), (∀ e, U.ExpandsAt e k σ f) → ∃ (σ' : H0 U.LG.L k') (f' : ∀ α : D.toPre.X, D.toPre.SecB k' α), (∀ e, U.ExpandsAt e k' σ' f') ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J), Good U.LG.L z J → sval σ' r z J = sval σ (r ≫ E.aG.left) z J * (val β r z J * val (L := U.LG.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.LG.rig (r ≫ G.hom) z J ^ ((k' : ℤ) - k)).val) ∧ (∀ (χ : D.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J → sval (f' (E.h χ)) r z J = sval (f χ) (r ≫ E.aB.left) z J * (val κ r z J * rigV D.toPre (r ≫ D.toPre.P.A.hom) z J ^ ((k' : ℤ) - k) * val (E.u χ) r z J).val) ∧ ∀ b, b ∉ Set.range E.h → ∀ j, (f' b).f j = 0 := by
  first | exact @GlobalTheory.PullInt.main | exact GlobalTheory.PullInt.main | (intros; apply GlobalTheory.PullInt.main <;> assumption)
end
end
