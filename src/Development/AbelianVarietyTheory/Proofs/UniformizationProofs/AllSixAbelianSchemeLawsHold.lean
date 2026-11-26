module

public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairing
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBasisOfCoord
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuationsSymmetricFrameAndTerms
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueHomExtensionSemiAbelian

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem allSixLaws : Laws ∧ Laws2 ∧ Laws3 ∧ Laws4 ∧ Laws5 ∧ Laws6 :=
  ⟨abelianSchemeLaws_all.1, abelianSchemeLaws_all.2,
    furtherLaws_of_laws abelianSchemeLaws_all.1 twistBaseChange⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHoldStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.all_six_abelian_scheme_laws_hold : Laws ∧ Laws2 ∧ Laws3 ∧ Laws4 ∧ Laws5 ∧ Laws6 := by
  first | exact @GlobalTheory.allSixLaws | exact GlobalTheory.allSixLaws | (intros; apply GlobalTheory.allSixLaws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.thetaUnifAV_all : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ThetaUnifAV := by
  obtain ⟨h, -⟩ := _root_.GlobalTheory.abelianSchemeLaws_all
  exact _root_.GlobalTheory.thetaUnifAV_of_laws h.cube h.mulN h.weil h.weilNondeg h.globalSectionsRank

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVarietyStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaUniformisation_complexAbelianVariety : ThetaUnifAV := by
  first | exact @GlobalTheory.thetaUnifAV_all | exact GlobalTheory.thetaUnifAV_all | (intros; apply GlobalTheory.thetaUnifAV_all <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.twistBaseChange_and_valuation_statements :
    _root_.ReciprocityTheory.ChartRestriction.G.DVR.TwistBaseChangeStatement ∧ _root_.ReciprocityTheory.ChartRestriction.G.DVR.TwistBCSpanStatement ∧ _root_.ReciprocityTheory.ChartRestriction.G.DVR.TWM.VRatioGtStatement ∧ _root_.ReciprocityTheory.ChartRestriction.G.DVR.TWStatement ∧ _root_.ReciprocityTheory.ChartRestriction.G.DVR.UUStatement := by
  have hbc : _root_.ReciprocityTheory.ChartRestriction.G.DVR.TwistBaseChangeStatement := _root_.GlobalTheory.twistBaseChange
  have hgl : _root_.ReciprocityTheory.ChartRestriction.G.Out.GlobalFnsSt := _root_.GlobalTheory.globalFns_holds
  have hspan : _root_.ReciprocityTheory.ChartRestriction.G.DVR.TwistBCSpanStatement := _root_.ReciprocityTheory.ChartRestriction.G.DVR.twistBCSpan_of hbc
  have hval : _root_.ReciprocityTheory.ChartRestriction.G.DVR.TWM.VRatioGtStatement := _root_.GlobalTheory.RatioVal.main
  exact ⟨hbc, hspan, hval, _root_.ReciprocityTheory.ChartRestriction.G.DVR.TWM.tw_of hgl hspan hval, _root_.GlobalTheory.UnitBallFree.main hgl hbc⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionMapsCompatibleInLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionMapsCompatibleInLevel
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.LevelCompat

open GlobalTheory.TorusExt
attribute [local instance] gtGroup

noncomputable def qkNsmul {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] (hB : D.TauBimult) {k : ℕ} (j : ℕ) (p : QkPt D F k) : QkPt D F k :=
  qkMk hB (j • p.y) (j • p.g) (by rw [smul_comm k j, qk_nsmul hB, map_nsmul])

theorem qkAdd_qkNsmul {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] (hB : D.TauBimult) {k : ℕ} (j : ℕ) (p : QkPt D F k) :
    QkAdd (qkNsmul hB j p) p (qkNsmul hB (j + 1) p) := by
  have e : qkNsmul hB (j + 1) p = qkAdd hB (qkNsmul hB j p) p :=
    qk_ext (succ_nsmul p.y j) (succ_nsmul p.g j)
  rw [e]
  exact qkAdd_qkAdd hB _ _

theorem qkNsmul_one {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] (hB : D.TauBimult) {k : ℕ} (p : QkPt D F k) : qkNsmul hB 1 p = p :=
  qk_ext (one_nsmul p.y) (one_nsmul p.g)

theorem qkToAkU_level : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (k n N : ℕ), 1 ≤ k → 1 ≤ n → N = k * n → ∀ (p : QkPt D.toPre F k) (q : QkPt D.toPre F N) x, (q.y = n • p.y → q.g = p.g → (QkToAkU U.toUnifPre F k p x ↔ QkToAkU U.toUnifPre F N q x)) ∧ (p.y = q.y → GtPtF.IsNsmul n q.g p.g → QkToAkU U.toUnifPre F N q x → QkToAkU U.toUnifPre F k p (x ^ n)) := by
  intro hL R _ _ _ I hI D A G _ _ hG U F _ _ _ k n N hk hn hN
  have hN1 : 1 ≤ N := hN ▸ Nat.mul_pos hk hn
  obtain ⟨f, hf, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL R I hI D A G hG U F k hk
  obtain ⟨f', hf', -, -, hadd, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL R I hI D A G hG U F N hN1
  have key : ∀ (p : QkPt D.toPre F k) (q : QkPt D.toPre F N), q.y = n • p.y → q.g = p.g → f p = f' q := by
    intro p q hy hg
    obtain ⟨x₀, h₀⟩ := GlobalTheory.T.exists_inducedTranslation_frobeniusOnSections hL R I hI D A G hG U F k hk p
    have a := (GlobalTheory.UT.indAt_translT_iff hL R I hI D A G hG U F k hk p x₀).1
      (h₀ 1 k le_rfl (Nat.mul_one k).symm p (one_nsmul _).symm rfl)
    have b := (GlobalTheory.UT.indAt_translT_iff hL R I hI D A G hG U F N hN1 q x₀).1 (h₀ n N hn hN q hy hg)
    exact ((hf p x₀).1 a).symm.trans ((hf' q x₀).1 b)
  intro p q x
  refine ⟨fun hy hg => by rw [hf, hf', key p q hy hg], fun hy hg hx => ?_⟩
  have hx' : x = f' q := (hf' q x).1 hx
  have hp : ∀ j : ℕ, f' (qkNsmul D.tau_bimult (j + 1) q) = x ^ (j + 1) := by
    intro j
    induction j with
    | zero => rw [Nat.zero_add, qkNsmul_one, pow_one, hx']
    | succ j ih => rw [hadd _ _ _ (qkAdd_qkNsmul D.tau_bimult (j + 1) q), ih, ← hx', ← pow_succ]
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  rw [hf, ← hp j]
  exact (key p _ (by rw [hy]; rfl) ((isNsmul_iff_eq _ _ _).1 hg).symm).symm

end GlobalTheory.LevelCompat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionMapsCompatibleInLevelStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_torsion_maps_compatible_in_level : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (k n N : ℕ), 1 ≤ k → 1 ≤ n → N = k * n → ∀ (p : QkPt D.toPre F k) (q : QkPt D.toPre F N) x, (q.y = n • p.y → q.g = p.g → (QkToAkU U.toUnifPre F k p x ↔ QkToAkU U.toUnifPre F N q x)) ∧ (p.y = q.y → GtPtF.IsNsmul n q.g p.g → QkToAkU U.toUnifPre F N q x → QkToAkU U.toUnifPre F k p (x ^ n)) := by
  first | exact @GlobalTheory.LevelCompat.qkToAkU_level | exact GlobalTheory.LevelCompat.qkToAkU_level | (intros; apply GlobalTheory.LevelCompat.qkToAkU_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaConstantValuationsUnitsEveryCoset
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaConstantValuationsUnitsEveryCoset
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.ThetaConstVal
open GlobalTheory.TorusExt

theorem le_of_sumV {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {Ix : Type} {x : Ix → F} {s : F}
    (h : SumV v x s) {q : ℚ} (hq : ∀ i, (q : WithTop ℚ) ≤ v (x i)) : (q : WithTop ℚ) ≤ v s := by
  obtain ⟨S, hS⟩ := h q
  have := v.map_le_add (hS S le_rfl) (v.map_le_sum (s := S) (f := x) fun i _ => hq i)
  rwa [sub_add_cancel] at this

theorem eq_zero_of_sumV {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {Ix : Type} {x : Ix → F} {s : F}
    (h : SumV v x s) {q : ℚ} (q0 : 0 < q) (i₀ : Ix) (h₀ : v (x i₀) = 0)
    (hq : ∀ i, i ≠ i₀ → (q : WithTop ℚ) ≤ v (x i)) : v s = 0 := by
  classical
  obtain ⟨S, hS⟩ := h q
  have a := v.map_le_add (hS (insert i₀ S) (Finset.subset_insert _ _))
    (v.map_le_sum (s := (insert i₀ S).erase i₀) (f := x) fun i hi => hq i (Finset.ne_of_mem_erase hi))
  have e : s = x i₀ + (s - ∑ i ∈ insert i₀ S, x i + ∑ i ∈ (insert i₀ S).erase i₀, x i) := by
    rw [← Finset.add_sum_erase _ x (Finset.mem_insert_self i₀ S)]; ring
  have lt : v (x i₀) < v (s - ∑ i ∈ insert i₀ S, x i + ∑ i ∈ (insert i₀ S).erase i₀, x i) := by
    rw [h₀]
    exact lt_of_lt_of_le (by exact_mod_cast q0) a
  rw [e, v.map_add_eq_of_lt_left lt, h₀]

section
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem exists_kap (hM : MulPullSt) [IsNoetherianRing R] (m : ℕ) :
    ∃ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ m) (m ^ 2) 1), Normd κ := by
  obtain ⟨α, hα⟩ := hM _ D.P m
  have o : ∀ f : D.P.A ⟶ D.P.A, f = 𝟙 D.P.A ^ m → (1 : D.P.A ⟶ D.P.A).left ≫ f.left = (1 : D.P.A ⟶ D.P.A).left := by
    rintro _ rfl
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id, one_pow]
  obtain ⟨κ, hκ, vκ⟩ := exists_gen D.P.isLB
    (φ' := ![𝟙 _, (𝟙 D.P.A ^ m).left, (1 : D.P.A ⟶ D.P.A).left])
    (ε' := ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ), ((1 : ℕ) : ℤ) - (m ^ 2 : ℕ)])
    (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans ?_
      apply Additive.ofMul.injective
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero, Category.comp_id,
        Matrix.cons_val_zero, Matrix.cons_val_succ, ofMul_mul, ofMul_zpow, ofMul_one, o _ rfl]
      push_cast
      module)
    (LB.mulGen D.P.L _ _ _ _ α (LB.invGen D.P.L _ _ (LB.pullGen D.P.L _ _ α (1 : D.P.A ⟶ D.P.A).left)))
    (mulGen_isGen _ _ _ _ _ _ _ hα (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ hα _)))
  refine ⟨κ, hκ, corr_of_val D.P.isLB fun y J hJ => ?_⟩
  have e : eSec D.P.A ≫ (1 : D.P.A ⟶ D.P.A).left = eSec D.P.A := by
    rw [eSec, ← Over.comp_left, MonObj.comp_one, Hom.one_def, toUnit_unit, Category.id_comp]
  rw [val_pull hJ, vκ _ _ y J hJ, val_mul hJ, val_inv, val_pull hJ, val_one, Category.id_comp, e, mul_inv_cancel]

theorem exists_frm {F : Type} [Field F] [Algebra (FractionRing R) F] (m : ℕ) (b b' : TF (R := R) F ⟶ D.P.A)
    (hb : b' = b ^ m) (w : Frm D F (m ^ 2) b) (hw : w.IsGen) (κ : LB.Gen (kapLB D (𝟙 D.P.A ^ m) (m ^ 2) 1))
    (hκ : κ.IsGen) : ∃ w' : Frm D F 1 b', w'.IsGen ∧
      ∀ z J, Good D.P.L z J → val w (𝟙 _) z J * val κ b.left z J = val w' (𝟙 _) z J := by
  subst hb
  have o₁ : b.left ≫ (𝟙 D.P.A ^ m).left = (b ^ m).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  have o₂ : b.left ≫ (1 : D.P.A ⟶ D.P.A).left = (DegPre.zeroF D F).left := by
    rw [← Over.comp_left, MonObj.comp_one]; rfl
  obtain ⟨w', hw', vw⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F (b ^ m)) (ε' := DegPre.lineε 1)
    (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans ?_
      apply Additive.ofMul.injective
      simp only [DegPre.lineφ, DegPre.lineε, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero,
        Category.comp_id, Matrix.cons_val_zero, Matrix.cons_val_succ, ofMul_mul, ofMul_zpow, ofMul_one, o₁, o₂]
      push_cast
      module)
    (LB.mulGen D.P.L _ _ _ _ w (LB.pullGen D.P.L _ _ κ b.left))
    (mulGen_isGen _ _ _ _ _ _ _ hw (pullGen_isGen _ _ _ _ hκ _))
  refine ⟨w', hw', fun z J hJ => ?_⟩
  rw [vw _ _ z J hJ, val_mul hJ, val_pull hJ, Category.id_comp]

end

attribute [local instance] gtGroup

theorem pow_eq_one_of_nsmul {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (hB : D.TauBimult) {F : Type} [Field F]
    [Algebra (FractionRing R) F] {k : ℕ} {M : Type} [Group M] (f : QkPt D F k → M)
    (hf : ∀ p p' p'', QkAdd p p' p'' → f p'' = f p * f p') (p : QkPt D F k) (hy : p.y = 0) (j : ℕ) (hj : j • p.g = 0) :
    f p ^ j = 1 := by
  have z : ∀ i : ℕ, k • (i • p.g) = iota hB F 0 := fun i => by
    rw [smul_comm, qk_nsmul hB, hy, map_zero, smul_zero]
  let r : ℕ → QkPt D F k := fun i => qkMk hB 0 (i • p.g) (z i)
  have radd : ∀ i i', f (r (i + i')) = f (r i) * f (r i') := fun i i' => by
    rw [← hf _ _ _ (qkAdd_qkAdd hB (r i) (r i'))]
    exact congrArg f (qk_ext (add_zero _).symm (add_smul i i' p.g))
  have r0 : f (r 0) = 1 := mul_eq_left.1 (radd 0 0).symm
  have r1 : r 1 = p := qk_ext hy.symm (one_smul ℕ p.g)
  have rpow : ∀ i, f (r i) = f p ^ i := fun i => by
    induction i with
    | zero => rw [r0, pow_zero]
    | succ i ih => rw [radd, ih, r1, pow_succ]
  rw [← rpow, ← r0]
  exact congrArg f (qk_ext rfl (hj.trans (zero_smul ℕ p.g).symm))

theorem exists_terms : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ → Prim D Q v ϑ → ∀ (m : ℕ), Odd m → ∀ (p : QkPt D.toPre F (m ^ 2)) x t c, QkToAkU U.toUnifPre F (m ^ 2) p x → ThC A ρ m th x t c → ∃ w' : Frm D.toPre F 1 (m • p.g).b, w'.IsGen ∧ SumV v (coef ϑ (m • p.g) w') c ∧ GenV hϖ hv w' ((Q p.y : ℚ) / (m ^ 2 : ℕ)) ∧ GtV hϖ hv (m • p.g) (fun χ => (QForm.bOf D.toPre Q p.y χ : ℚ) / m) ∧ ∀ χ, (((Q (m • χ + p.y) : ℚ) / (m ^ 2 : ℕ) : ℚ) : WithTop ℚ) ≤ v (coef ϑ (m • p.g) w' χ) := by
  intro hL h₁ h₂ h₃ h₄ V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN th ϑ hE hP m hm p x t c hx hT
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  obtain ⟨w, hw⟩ := (GlobalTheory.UT.SymFrame.main hL V _ hA D F (m ^ 2) hm.pow p).1
  obtain ⟨κ, hκ⟩ := exists_kap D.toPre hL.1.mulPull m
  obtain ⟨w', hw', e⟩ := exists_frm D.toPre m p.g.b (m • p.g).b (nsmul_b m p.g) w hw.1 κ hκ.1
  have hg : GtPtF.IsNsmul m p.g (m • p.g) := (isNsmul_iff_eq _ _ _).2 rfl
  have s := (GlobalTheory.T.thetaConstant_eq_sum_thetaTerms_odd_multiple hL V _ hA D A G hG U F w₀ ρ hN th ϑ hE m hm p x t c hx hT w hw _ hg κ hκ w' hw' e).1
  obtain ⟨a₁, a₂, a₃⟩ := (GlobalTheory.T.valuations_symmetricFrame_and_terms hL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ F v hv).2 m hm.pos p w hw _ hg κ hκ w' hw' e
  exact ⟨w', hw', (AdicValSum.main V ϖ hϖ F v hv _ _ _ s).1, a₁, a₂, a₃ ϑ hP.1⟩

theorem main : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ → Prim D Q v ϑ → ∀ (m : ℕ), Odd m → IsUnit (m : V) → (∀ (p : QkPt D.toPre F (m ^ 2)) x t c, QkToAkU U.toUnifPre F (m ^ 2) p x → ThC A ρ m th x t c → (∀ q : ℚ, (∀ χ, q ≤ (Q (m • χ + p.y) : ℚ) / (m ^ 2 : ℕ)) → (q : WithTop ℚ) ≤ v c) ∧ (v c = 0 → ∃ z, p.y = m • z)) ∧ ∀ n, 2 ≤ n → n ∣ m → ∀ (p : QkPt D.toPre F (m ^ 2)) x, p.y = 0 → QkToAkU U.toUnifPre F (m ^ 2) p x → ∃ (p' : QkPt D.toPre F (m ^ 2)) (x' : _) (t : _) (c : F), p'.y = 0 ∧ QkToAkU U.toUnifPre F (m ^ 2) p' x' ∧ (x' ^ m * (x ^ m)⁻¹) ^ n = 1 ∧ ThC A ρ m th x' t c ∧ v c = 0 := by
  intro hL h₁ h₂ h₃ h₄ V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN th ϑ hE hP m hm hu
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  have T := exists_terms hL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hN th ϑ hE hP m hm
  have m0 : (0 : ℚ) < (m ^ 2 : ℕ) := by exact_mod_cast pow_pos hm.pos 2
  have q0 : (0 : ℚ) < 1 / (m ^ 2 : ℕ) := one_div_pos.2 m0
  have pos : ∀ χ : D.toPre.X, χ ≠ 0 → (1 : ℚ) / (m ^ 2 : ℕ) ≤ (Q χ : ℚ) / (m ^ 2 : ℕ) := fun χ h =>
    div_le_div_of_nonneg_right (by exact_mod_cast QForm.Q_pos hϖ D hQ h) m0.le
  refine ⟨fun p x t c hx hT => ?_, fun n hn hnm p x hy hx => ?_⟩
  · obtain ⟨w', -, s, -, -, a⟩ := T p x t c hx hT
    have k : ∀ q : ℚ, (∀ χ, q ≤ (Q (m • χ + p.y) : ℚ) / (m ^ 2 : ℕ)) → (q : WithTop ℚ) ≤ v c := fun q hq =>
      le_of_sumV s fun χ => (WithTop.coe_le_coe.2 (hq χ)).trans (a χ)
    refine ⟨k, fun h0 => by_contra fun hz => ?_⟩
    have := k _ fun χ => pos (m • χ + p.y) fun e => hz ⟨-χ, by rw [smul_neg]; exact eq_neg_of_add_eq_zero_right e⟩
    rw [h0] at this
    exact absurd (by exact_mod_cast this) q0.not_ge
  · have hB := D.tau_bimult
    obtain ⟨d, rfl⟩ := hnm
    obtain ⟨h, o, g₂, ho, hh, hg₂, hv₂⟩ := GlobalTheory.T.exists_nsmul_add_decomp_with_coef_valuation hL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ F v hv ϑ hP n hn
      (isUnit_of_mul_isUnit_left (by rwa [Nat.cast_mul] at hu)) ((n * d) • p.g) 0
    obtain ⟨h', hh'⟩ := (gt_onto_divisible_kernel hL V _ hA D F).2.1 (n * d) hm.pos h
    rw [isZero_iff_eq] at ho
    rw [isNsmul_iff_eq] at hh hh'
    rw [isAdd_iff_eq] at hg₂
    have z₁ : (n * d * n) • h' = 0 := by rw [_root_.mul_comm (n * d) n, mul_smul, ← hh', ← hh, ho]
    have z₂ : (n * d) ^ 2 • h' = iota hB F 0 := by
      rw [map_zero, show (n * d) ^ 2 = d * (n * d * n) by ring, mul_smul, z₁, smul_zero]
    obtain ⟨f, f₁, -, -, f₄, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL V _ hA D A G hG U F ((n * d) ^ 2) (pow_pos hm.pos 2)
    let r : QkPt D.toPre F ((n * d) ^ 2) := qkMk hB 0 h' z₂
    let p' := qkAdd hB p r
    have y' : p'.y = 0 := (add_zero _).trans hy
    have fp : f p' = x * f r := ((f₁ p x).1 hx).symm ▸ f₄ _ _ _ (qkAdd_qkAdd hB p r)
    have hx' : QkToAkU U.toUnifPre F ((n * d) ^ 2) p' (f p') := (f₁ _ _).2 rfl
    have t' : f p' ^ ((n * d) ^ 2) = 1 := pow_eq_one_of_nsmul hB f f₄ p' y' _ (by rw [qk_nsmul hB, y', map_zero])
    obtain ⟨⟨t, c⟩, hT, -⟩ := GlobalTheory.T.existsUnique_theta_const_of_odd hL V A F ρ hN.2.1 (n * d) hm th (f p') t'
    refine ⟨p', f p', t, c, y', hx', ?_, hT, ?_⟩
    · rw [fp, mul_pow x, mul_inv_cancel_comm, ← pow_mul]
      exact pow_eq_one_of_nsmul hB f f₄ r rfl _ z₁
    · obtain ⟨w', hw', s, a₁, a₂, a⟩ := T p' _ t c hx' hT
      have e : g₂ = (n * d) • p'.g := by
        rw [hg₂, hh']; exact (smul_add _ _ _).symm
      subst e
      refine eq_zero_of_sumV s q0 0 ?_ fun χ hχ => (WithTop.coe_le_coe.2 (pos _ fun e => hχ ?_)).trans (a χ)
      · rw [hv₂ w' _ _ hw' a₂ a₁, y', QForm.Q_zero hϖ D hQ, bOf_zero_left hϖ hQ]
        simp
      · rw [y', add_zero] at e
        by_contra h0
        have b₁ := QForm.Q_pos hϖ D hQ h0
        have b₂ := Q_nsmul hϖ hQ (n * d) χ
        rw [e, QForm.Q_zero hϖ D hQ] at b₂
        have b₃ : (0 : ℤ) < ((n * d : ℕ) : ℤ) ^ 2 := by exact_mod_cast pow_pos hm.pos 2
        exact absurd b₂ (mul_pos b₃ (by omega)).ne

end GlobalTheory.UT.ThetaConstVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaConstantValuationsUnitsEveryCosetStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_constant_valuations_units_every_coset : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ → Prim D Q v ϑ → ∀ (m : ℕ), Odd m → IsUnit (m : V) → (∀ (p : QkPt D.toPre F (m ^ 2)) x t c, QkToAkU U.toUnifPre F (m ^ 2) p x → ThC A ρ m th x t c → (∀ q : ℚ, (∀ χ, q ≤ (Q (m • χ + p.y) : ℚ) / (m ^ 2 : ℕ)) → (q : WithTop ℚ) ≤ v c) ∧ (v c = 0 → ∃ z, p.y = m • z)) ∧ ∀ n, 2 ≤ n → n ∣ m → ∀ (p : QkPt D.toPre F (m ^ 2)) x, p.y = 0 → QkToAkU U.toUnifPre F (m ^ 2) p x → ∃ (p' : QkPt D.toPre F (m ^ 2)) (x' : _) (t : _) (c : F), p'.y = 0 ∧ QkToAkU U.toUnifPre F (m ^ 2) p' x' ∧ (x' ^ m * (x ^ m)⁻¹) ^ n = 1 ∧ ThC A ρ m th x' t c ∧ v c = 0 := by
  first | exact @GlobalTheory.UT.ThetaConstVal.main | exact GlobalTheory.UT.ThetaConstVal.main | (intros; apply GlobalTheory.UT.ThetaConstVal.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KernelFiniteFlatHolds
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.kernelFiniteFlat_holds : _root_.GlobalTheory.Published.KernelFiniteFlatSt :=
  _root_.GlobalTheory.KernelFlat.kernelFiniteFlat _root_.GlobalTheory.abelianSchemeLaws_all.1

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkInjectiveClosed
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionMapInj

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.TorsionMapInj.qkToAk_injective_closed : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.QkToAkInjSt :=
  _root_.GlobalTheory.TorsionMapInj.qkToAk_injective _root_.GlobalTheory.abelianSchemeLaws_all.1 _root_.GlobalTheory.abelianSchemeLaws_all.2

end GlobalTheory.TorsionMapInj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsIsoOfFlatOfClosedPoint
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.PrimitiveOverValuationRing
open GlobalTheory.CechPic

theorem pull_eq_zero_of_mem {Y Z : Scheme.{0}} (W : Y.Opens) (r : Z ⟶ Y) (hr : ∀ z, r z ∈ W) {c : CechPic.Pic Y}
    (h : CechPic.pull W.ι c = 0) : CechPic.pull r c = 0 := by
  have e := IsOpenImmersion.lift_fac W.ι r (by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hr z)
  rw [← e, pull_comp, h, map_zero]

theorem cls_pair {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (a b : Y ⟶ X)
    (h : (LB.LinComb L (K := Fin 2) ![a, b] ![1, -1]).IsLB) :
    cls _ h = CechPic.pull a (cls L hL) - CechPic.pull b (cls L hL) := by
  refine (cls_linComb hL _ _ h).trans ?_
  rw [Fin.sum_univ_two, sub_eq_add_neg]
  exact congrArg₂ (· + ·) (one_zsmul _) (neg_one_zsmul _)

section Points

variable {S : Scheme.{0}} {B : Over S} [GrpObj B] {L O : LB B.left}

theorem triv_iff (hL : L.IsLB) (hO : O.IsLB) {T : Over S} (x : T ⟶ B) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ B).left) :
    Triv ((LB.div (translDiff B L x) (O.pull (snd T B).left)).pull r) ↔
      CechPic.pull r (CechPic.pull ((fst T B ≫ x) * snd T B).left (cls L hL) - CechPic.pull (snd T B).left (cls L hL) -
        CechPic.pull (snd T B).left (cls O hO)) = 0 := by
  have h₁ : (translDiff B L x).IsLB := LB.isLB_linComb hL _ _
  have h₂ := pull_isLB hO (snd T B).left
  have hM := LB.isLB_div h₁ h₂
  refine (cls_eq_zero_iff (pull_isLB hM r)).symm.trans ?_
  rw [cls_pull hM, cls_div h₁ h₂, cls_pull hO]
  exact Iff.of_eq (congrArg (fun q => CechPic.pull r (q - _) = 0) (cls_pair hL _ _ h₁))

theorem inK_mul_inv (hL : L.IsLB) (hO : O.IsLB) {T : Over S} (x y : T ⟶ B)
    (hx : ∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧
      Triv ((LB.div (translDiff B L x) (O.pull (snd T B).left)).pull ((fst T B).left ⁻¹ᵁ U).ι))
    (hy : ∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧
      Triv ((LB.div (translDiff B L y) (O.pull (snd T B).left)).pull ((fst T B).left ⁻¹ᵁ U).ι)) :
    InK B L (x * y⁻¹) := by
  intro p
  obtain ⟨U, hU, h₁⟩ := hx p
  obtain ⟨U', hU', h₂⟩ := hy p
  refine ⟨U ⊓ U', ⟨hU, hU'⟩, ?_⟩
  have hD : (translDiff B L (x * y⁻¹)).IsLB := LB.isLB_linComb hL _ _
  let τ : T ⊗ B ⟶ T ⊗ B := lift (fst T B) ((fst T B ≫ y⁻¹) * snd T B)
  have k₁ : τ ≫ fst T B = fst T B := lift_fst _ _
  have k₂ : ∀ z : T ⟶ B, τ ≫ ((fst T B ≫ z) * snd T B) = (fst T B ≫ (z * y⁻¹)) * snd T B := fun z => by
    rw [MonObj.comp_mul, lift_snd, ← Category.assoc, k₁, MonObj.comp_mul, _root_.mul_assoc]
  have m : ∀ z, (fst T B).left ((((fst T B).left ⁻¹ᵁ (U ⊓ U')).ι ≫ τ.left) z) ∈ U ⊓ U' := fun z => by
    have e := congrArg (fun q : T ⊗ B ⟶ T => q.left z.1) k₁
    exact (congrArg (· ∈ U ⊓ U') e).mpr z.2
  have a₁ := pull_eq_zero_of_mem _ _ (fun z => (m z).1) ((triv_iff hL hO x _).1 h₁)
  have a₂ := pull_eq_zero_of_mem _ _ (fun z => (m z).2) ((triv_iff hL hO y _).1 h₂)
  have a := congrArg₂ (· - ·) a₁ a₂
  simp only [← map_sub, sub_sub_sub_cancel_right, sub_zero] at a
  rw [pull_comp, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, k₂, k₂, mul_inv_cancel,
    MonObj.comp_one, _root_.one_mul] at a
  refine (cls_eq_zero_iff (pull_isLB hD _)).1 ?_
  rw [cls_pull hD]
  exact (congrArg _ (cls_pair hL _ _ hD)).trans a

end Points

theorem exists_geometric_point (hL : Laws) {S : Scheme.{0}} (P : PolAV S) {O : LB P.A.left} (hO : O.IsLB)
    (hu : ∃ u : LB.Gen (abelian₂ P.A O), u.IsGen) (K : Type) [Field K] [IsAlgClosed K] (f : Spec (CommRingCat.of K) ⟶ S) :
    ∃ x : Over.mk f ⟶ P.A, Triv (LB.div (translDiff P.A P.L x) (O.pull (snd (Over.mk f) P.A).left)) := by
  obtain ⟨P', g, hg, -, hm, ht⟩ := hL.polBaseChange S _ f P
  have hc : CechPic.pull g (cls P.L P.isLB) = cls P'.L P'.isLB := (cls_eq_iff (pull_isLB P.isLB g) P'.isLB).2 ht
  have hO' := pull_isLB hO g
  have one : ∀ T : Over (Spec (CommRingCat.of K)), toBase hg.w (1 : T ⟶ P'.A) = 1 := fun T => by
    have := hm T 1 1
    rw [_root_.mul_one] at this
    exact left_eq_mul.1 this
  have lamO : lam (cls O hO) (fst P.A P.A) (snd P.A P.A) = 0 :=
    (cls_cube_two hO _ _ (LB.isLB_linComb hO _ _)).symm.trans ((cls_eq_zero_iff _).2 hu)
  have lamO' : lam (cls _ hO') (fst P'.A P'.A) (snd P'.A P'.A) = 0 := by
    have e := congrArg (CechPic.pull (lift (toBase hg.w (fst P'.A P'.A)) (toBase hg.w (snd P'.A P'.A))).left) lamO
    rw [pull_lam, lift_fst, lift_snd, map_zero, lam, ← hm, ← one] at e
    rw [cls_pull hO, lam, ← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp]
    exact e
  obtain ⟨x', hx'⟩ := GlobalTheory.T.exists_point_primitiveBundle_eq_translate_ppav hL K P' (O.pull g) hO'
    ((cls_eq_zero_iff (LB.isLB_linComb hO' _ _)).1 ((cls_cube_two hO' _ _ (LB.isLB_linComb hO' _ _)).trans lamO'))
  have e := ((cls_eq_iff hO' (LB.isLB_linComb P'.isLB _ _)).2 hx').trans (cls_pair P'.isLB _ _ _)
  let T : Over S := Over.mk f
  have wx : x'.left ≫ P'.A.hom = 𝟙 _ := Over.w x'
  let x : T ⟶ P.A := Over.homMk (x'.left ≫ g) (by
    show (x'.left ≫ g) ≫ P.A.hom = f
    rw [Category.assoc, hg.w, ← Category.assoc, wx]
    exact Category.id_comp _)
  have w : (snd T P.A).left ≫ P.A.hom = (fst T P.A).left ≫ f := (Over.w (snd T P.A)).trans (Over.w (fst T P.A)).symm
  let T' : Over (Spec (CommRingCat.of K)) := Over.mk (Y := (T ⊗ P.A).left) (fst T P.A).left
  let h : T' ⟶ P'.A := Over.homMk (hg.lift (snd T P.A).left (fst T P.A).left w) (hg.lift_snd _ _ _)
  have hh : h.left ≫ g = (snd T P.A).left := hg.lift_fst _ _ _
  let u : Over.mk (T'.hom ≫ f) ⟶ T ⊗ P.A := Over.homMk (𝟙 _) ((Category.id_comp _).trans (Over.w (fst T P.A)).symm)
  have b₁ : u ≫ snd T P.A = toBase hg.w h := Over.OverMorphism.ext ((Category.id_comp _).trans hh.symm)
  have b₂ : u ≫ fst T P.A ≫ x = toBase hg.w (toUnit T' ≫ x') := by
    refine Over.OverMorphism.ext ((Category.id_comp _).trans ?_)
    have : (toUnit T').left = (fst T P.A).left := (Category.comp_id _).symm.trans (Over.w (toUnit T'))
    show (fst T P.A).left ≫ x'.left ≫ g = ((toUnit T').left ≫ x'.left) ≫ g
    rw [this]
    exact (Category.assoc _ _ _).symm
  have b : h.left ≫ ((toUnit P'.A ≫ x') * 𝟙 P'.A).left ≫ g = ((fst T P.A ≫ x) * snd T P.A).left := by
    have b₃ : toBase hg.w (h ≫ ((toUnit P'.A ≫ x') * 𝟙 P'.A)) = u ≫ ((fst T P.A ≫ x) * snd T P.A) := by
      rw [MonObj.comp_mul, MonObj.comp_mul, b₁, b₂, ← hm, Category.comp_id, ← Category.assoc, comp_toUnit]
    exact (Category.assoc _ _ _).symm.trans ((congrArg CommaMorphism.left b₃).trans (Category.id_comp _))
  have e' := congrArg (CechPic.pull h.left) e
  rw [cls_pull hO, ← hc, pull_id, map_sub, ← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp, Category.assoc, b, hh] at e'
  have h₁ : (translDiff P.A P.L x).IsLB := LB.isLB_linComb P.isLB _ _
  have h₂ := pull_isLB hO (snd T P.A).left
  refine ⟨x, (cls_eq_zero_iff (LB.isLB_div h₁ h₂)).1 ?_⟩
  rw [cls_div h₁ h₂, sub_eq_zero]
  exact (cls_pair P.isLB _ _ h₁).trans e'.symm

theorem isIso_of_flat_of_closedPoint {V : Type} [CommRing V] [IsLocalRing V] [_root_.IsReduced V] {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of V)) [IsClosedImmersion q] [Flat q] (h : X) (hh : q h = IsLocalRing.closedPoint V) :
    IsIso q := by
  have : Surjective q := ⟨fun s => by
    obtain ⟨y, -, hy⟩ := Flat.generalizingMap q (a := h) (b := s) (by
      rw [hh]; exact IsLocalRing.specializes_closedPoint s)
    exact ⟨y, hy⟩⟩
  exact isIso_of_isClosedImmersion_of_surjective q

theorem exists_section_translate : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (P : PolAV (Spec (CommRingCat.of V))) (O : LB P.A.left), O.IsLB → (∃ u : LB.Gen (abelian₂ P.A O), u.IsGen) → ∃ x : 𝟙_ _ ⟶ P.A, LBIso O (LB.LinComb P.L (K := Fin 2) ![((toUnit P.A ≫ x) * 𝟙 P.A).left, 𝟙 P.A.left] ![1, -1]) := by
  intro hL V _ _ _ P O hO hu
  have proj : IsProjBy P.A.hom := by
    obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy V P.A P.L P.isLB).1 P.ample
    exact ⟨_, isLB_pw P.isLB _, n, s, hs⟩
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.T.exists_closed_subscheme_translation_kernel hL.globalFns V P.A P.isAb proj P.L O P.isLB hO
  have fin : IsFinite H.hom := GlobalTheory.AmpleStabFinite.isFinite_of_relAmple hL.globalFns V P.A P.isAb P.L O P.isLB hO
    P.ample H j hj hH
  obtain ⟨r, hr⟩ := P.rigid
  obtain ⟨c⟩ := (hL.cube _ P ⟨P.L, r, P.isLB, hr⟩ rfl).1
  have flat : Flat H.hom := GlobalTheory.T.flat_kernelPolarisation_cosets_over_DVR hL.globalFns V P.A P.isAb proj ⟨P.L, r, P.isLB, hr⟩ c O hO hu H j hj hH fin
  have mono : Mono H.hom := ⟨fun {Z} a b e => by
    let a' : Over.mk (b ≫ H.hom) ⟶ H := Over.homMk a e
    let b' : Over.mk (b ≫ H.hom) ⟶ H := Over.homMk b rfl
    have := (inK_mul_inv P.isLB hO (a' ≫ j) (b' ≫ j) ((hH _ _).2 ⟨_, rfl⟩) ((hH _ _).2 ⟨_, rfl⟩)).eq_one P.ktriv
    rw [mul_inv_eq_one] at this
    exact (cancel_mono j.left).1 (congrArg CommaMorphism.left this)⟩
  have : IsClosedImmersion H.hom := (IsClosedImmersion.iff_isFinite_and_mono _).2 ⟨fin, mono⟩
  let K : Type := AlgebraicClosure (IsLocalRing.ResidueField V)
  let φ : V →+* K := (algebraMap (IsLocalRing.ResidueField V) K).comp (IsLocalRing.residue V)
  have : IsLocalHom φ := RingHom.isLocalHom_comp _ _
  obtain ⟨x₀, hx₀⟩ := exists_geometric_point hL P hO hu K (Spec.map (CommRingCat.ofHom φ))
  obtain ⟨y, -⟩ := (hH _ x₀).1 fun p => ⟨⊤, trivial, by
    have hM := LB.isLB_div (show (translDiff P.A P.L x₀).IsLB from LB.isLB_linComb P.isLB _ _)
      (pull_isLB hO (snd _ P.A).left)
    refine (cls_eq_zero_iff (pull_isLB hM _)).1 ?_
    rw [cls_pull hM, (cls_eq_zero_iff hM).2 hx₀, map_zero]⟩
  have : IsIso H.hom := isIso_of_flat_of_closedPoint H.hom (y.left (IsLocalRing.closedPoint K))
    ((congrArg (fun q => q (IsLocalRing.closedPoint K)) (Over.w y)).trans (IsLocalRing.comap_closedPoint φ))
  let σ : 𝟙_ (Over (Spec (CommRingCat.of V))) ⟶ H := Over.homMk (inv H.hom) (IsIso.inv_hom_id _)
  obtain ⟨U, hU, ht⟩ := (hH _ (σ ≫ j)).2 ⟨σ, rfl⟩ (IsLocalRing.closedPoint V)
  obtain rfl : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).1 hU
  have e := pull_eq_zero_of_mem ((fst _ P.A).left ⁻¹ᵁ ⊤) (lift (toUnit P.A) (𝟙 P.A)).left (fun _ => trivial)
    ((triv_iff P.isLB hO (σ ≫ j) _).1 ht)
  rw [map_sub, map_sub, ← pull_comp, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_mul,
    lift_snd, lift_fst_assoc, sub_eq_zero, Over.id_left, pull_id (cls O hO)] at e
  exact ⟨σ ≫ j, (cls_eq_iff hO (LB.isLB_linComb P.isLB _ _)).1 (e.symm.trans (cls_pair P.isLB _ _ _).symm)⟩

end GlobalTheory.PrimitiveOverValuationRing
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HomExtDvrAndLaws
open ReciprocityTheory.ChartRestriction.G

namespace GlobalTheory

theorem homExtDvr_and_laws : Out.HomExtDvrSt ∧ Out.Laws7 := by
  have h : Out.HomExtDvrSt := fun T _ _ _ G G' _ _ hG hG' φ hφ =>
    GlobalTheory.existsUnique_hom_extension_semiAbelian T (FractionRing T) G G' hG hG' φ hφ
  exact ⟨h, ⟨h⟩⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionEqOfLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionEqOfLaws
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH

theorem uTors_of_laws : Laws → Laws2 → Laws3 → Laws4 → Laws5 → GlobalTheory.ZH.UTorsSt := by
  intro h1 h2 h3 h4 h5 V _ _ _ _ hV A G _ _ D U F _ _ _ k hk
  have hB : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV⟩
  exact GlobalTheory.TorsionIso.torsion_eq ⟨h1, h2, h3, h4, h5⟩ V (maximalIdeal V) hB D A G
    (GlobalTheory.T.isSemiAbelian_of_uniformisation_over_dvr V D A G U.toUnifPre) U F k hk

end GlobalTheory.ZH
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionEqOfLawsStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_torsion_eq_of_laws : Laws → Laws2 → Laws3 → Laws4 → Laws5 → GlobalTheory.ZH.UTorsSt := by
  first | exact @GlobalTheory.ZH.uTors_of_laws | exact GlobalTheory.ZH.uTors_of_laws | (intros; apply GlobalTheory.ZH.uTors_of_laws <;> assumption)
end
end
