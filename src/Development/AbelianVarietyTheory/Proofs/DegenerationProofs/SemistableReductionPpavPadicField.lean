module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianModelPadicPrincipallyPolarised
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsDegenerationDataUniformisationOfTorsionCou

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemistableReductionPpavPadicField
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemistableReductionPpavPadicField
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem _root_.GlobalTheory.SS.semistableReductionSt : _root_.GlobalTheory.Published.SemistableReductionSt := by
  unfold _root_.GlobalTheory.Published.SemistableReductionSt
  exact fun p _ K _ P => _root_.GlobalTheory.SS.exists_semiAbelian_model_padic_polAV p K P

end GlobalTheory.SS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemistableReductionPpavPadicFieldStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semistableReduction_ppav_padicField : GlobalTheory.Published.SemistableReductionSt := by
  first | exact @GlobalTheory.SS.semistableReductionSt | exact GlobalTheory.SS.semistableReductionSt | (intros; apply GlobalTheory.SS.semistableReductionSt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisationCompleteDvrOfLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisationCompleteDvrOfLaws
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory.LN

theorem uniformisation_dvr : Laws → Laws2 → Laws3 → Laws4 → Laws5 → USt := by
  intro h1 h2 h3 h4 h5 V _ _ _ A G _ _ s
  obtain ⟨D, U, hL, hg, -⟩ := GlobalTheory.T.exists_degenerationData_uniformisation_of_torsionCount (GlobalTheory.T.card_torsion_points_abelianVariety h1.globalFns h1.rigidity) h1 h2 V A G s
  refine ⟨D, U, hL, hg, ?_⟩
  obtain ⟨hdvr, hcomp, hchar⟩ := s.cdvr
  have hadm : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hcomp⟩
  intro F _ _ _ k hk p
  obtain ⟨f, hf, -⟩ := GlobalTheory.TorsionIso.torsion_eq ⟨h1, h2, h3, h4, h5⟩ V _ hadm D A G s.semi U F k hk
  exact ⟨f p, (hf p _).2 rfl⟩

end GlobalTheory.LN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisationCompleteDvrOfLawsStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_complete_dvr_of_laws : Laws → Laws2 → Laws3 → Laws4 → Laws5 → USt := by
  first | exact @GlobalTheory.LN.uniformisation_dvr | exact GlobalTheory.LN.uniformisation_dvr | (intros; apply GlobalTheory.LN.uniformisation_dvr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusOperatorEigenOfExpansionSingleClass
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusPointsLevelWeightsFromOrthogonalLabels
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusPointsLevelWeightsFromOrthogonalLabels
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

noncomputable section

namespace GlobalTheory.TestFibre

open GlobalTheory.TorusExt

theorem torus_points_level_weights : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), PtsOver u x → ∀ t : S.perp l.yy.ker, ∃ (τ : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ) (q : QkPt u.D.toPre (PadicAlgCl p) S.N), q.y = 0 ∧ IsTor τ q.g ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) S.N q (x (S.r • (t : S.Gam))) ∧ ∀ β, (τ (Multiplicative.ofAdd β) : PadicAlgCl p) = y₀ (algebraMap o S.R S.ζN) ^ (l.wt β t).val := by
  intro h₁ h₂ hT o Ω _ _ _ _ S ρ p _ y₀ u l hy x hx t
  obtain ⟨hc, -, hA, -, -, -⟩ := GlobalTheory.T.uniformisedModel_valuation_data o Ω S ρ p y₀ u l hy
  obtain ⟨hadd, -⟩ := (GlobalTheory.T.uniformisedModel_torsionPoints_group_pairing h₁ o Ω S ρ p y₀ u).2 x hx
  obtain ⟨τ, q, hq0, hqτ, hq, hval⟩ := GlobalTheory.T.thetaSystem_orthogonal_labels_are_torus_points h₁ h₂ hT o Ω S ρ p y₀ u l hy x hx t
  have hL : LL := (laws_all h₁ h₂).1
  letI := gtGroup u.D.toPre (PadicAlgCl p)
  have hB := u.D.tau_bimult
  have hN : 1 ≤ S.N := le_trans (by norm_num) S.N_ge
  have hx0 : x 0 = 1 := by
    have e := hadd 0 0
    rw [add_zero] at e
    exact mul_eq_left.1 e.symm
  have hpow : ∀ (n : ℕ) (a : S.Gam), x (n • a) = x a ^ n := fun n a => by
    induction n with
    | zero => rw [zero_nsmul, pow_zero, hx0]
    | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]
  have hg : S.N • (S.r • q.g) = iota hB (PadicAlgCl p) q.y := by
    rw [← mul_nsmul, qk_nsmul hB q]
  refine ⟨τ ^ S.r, qkMk hB q.y (S.r • q.g) hg, hq0, ?_, ?_, fun β => ?_⟩
  · rw [isTor_iff, isTorusPtF_iff_eq] at hqτ ⊢
    show S.r • q.g = _
    rw [hqτ, ofMul_pow, map_nsmul]
  · rw [hpow]
    exact (GlobalTheory.T.uniformisation_torsion_maps_compatible_in_level hL u.V _ hA u.D u.A u.G u.semi u.U (PadicAlgCl p) S.N S.r (S.r * S.N) hN S.r_pos
      (mul_comm _ _) (qkMk hB q.y (S.r • q.g) hg) q (x t)).2 rfl ((isNsmul_iff_eq _ _ _).2 rfl) hq
  · obtain ⟨a, ha⟩ := l.yy_onto (QuotientAddGroup.mk β)
    haveI : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by omega)⟩
    have hζ : y₀ (algebraMap o S.R S.ζN) ^ S.N = 1 := by
      rw [← map_pow, ← map_pow, ThetaSys.ζN, ← pow_mul,
        show S.r ^ 2 * S.N * S.N = (S.r * S.N) ^ 2 by ring, S.prim.pow_eq_one, map_one, map_one]
    rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, hval a β ha, l.wt_eq a β ha t, ZMod.castHom_apply,
      ZMod.cast_eq_val, ZMod.val_natCast, ← pow_eq_pow_mod _ hζ, ThetaSys.ζN, map_pow, map_pow, ← pow_mul, ← pow_mul]
    congr 1
    ring

end GlobalTheory.TestFibre
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusPointsLevelWeightsFromOrthogonalLabelsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusPoints_level_weights_from_orthogonal_labels : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), PtsOver u x → ∀ t : S.perp l.yy.ker, ∃ (τ : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ) (q : QkPt u.D.toPre (PadicAlgCl p) S.N), q.y = 0 ∧ IsTor τ q.g ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) S.N q (x (S.r • (t : S.Gam))) ∧ ∀ β, (τ (Multiplicative.ofAdd β) : PadicAlgCl p) = y₀ (algebraMap o S.R S.ζN) ^ (l.wt β t).val := by
  first | exact @GlobalTheory.TestFibre.torus_points_level_weights | exact GlobalTheory.TestFibre.torus_points_level_weights | (intros; apply GlobalTheory.TestFibre.torus_points_level_weights <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusOperatorEigenOfExpansionSingleClass
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

namespace GlobalTheory.TestFibre

theorem eigen_of_expansion_in_class : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)) (rig : LB.Gen (u.A.L.pull (eSec u.A.A))) (e : ∀ a, FrameAt u.A (x a)) (th : SecA u.A (PadicAlgCl p) 1) (s : S.J → SecA u.A (PadicAlgCl p) S.N), PtsOver u x → SecsOver u x rig e th s → ∀ (w₀ : W0 u.U.toUnifPre), w₀.IsGen → ∀ (α : u.D.toPre.X) (b : S.J → PadicAlgCl p) (σ : SecA u.A (PadicAlgCl p) S.N) (Φ : Fam u.D.toPre (PadicAlgCl p) S.N), IsComb u.A s b σ → u.U.ExpandsF (PadicAlgCl p) S.N w₀ σ Φ → (∀ β, (∀ z : u.D.toPre.X, β ≠ α + S.N • z) → ∀ j, (Φ.s β).f j = 0) → ∀ (t : S.perp l.yy.ker) (h : S.Gam), ∑ j, (∑ i, y₀ (algebraMap o S.R (S.ρ t j i)) * b i) * y₀ ⟨S.ev h j, S.ev_mem h j⟩ = y₀ (algebraMap o S.R S.ζN) ^ (l.wt α t).val * ∑ j, b j * y₀ ⟨S.ev h j, S.ev_mem h j⟩ := by
  intro h1 h2 hT o Ω _ _ _ _ S ρ p _ y₀ u l hy x rig e th s hx hs w₀ hw₀ α b σ Φ hσ hΦ hsupp t h
  obtain ⟨hLL, -⟩ := laws_all h1 h2
  obtain ⟨hc, -, hadm, -⟩ := GlobalTheory.T.uniformisedModel_valuation_data o Ω S ρ p y₀ u l hy
  have hodd : Odd S.N := by
    rw [ρ.N_eq]; exact (ρ.n_odd.pow).pow
  have hN1 : 1 ≤ S.N := le_trans (by norm_num) S.N_ge
  obtain ⟨-, -, -, hval, -, hθ⟩ := hs
  obtain ⟨θ, hθs, hθa⟩ := hθ (t : S.Gam)
  obtain ⟨τ, q, hqy, hqt, hqx, hτ⟩ := GlobalTheory.T.torusPoints_level_weights_from_orthogonal_labels h1 h2 hT o Ω S ρ p y₀ u l hy x hx t
  obtain ⟨⟨w, hw⟩, -⟩ := GlobalTheory.UT.SymFrame.main hLL u.V _ hadm u.D (PadicAlgCl p) S.N hodd q
  obtain ⟨-, -, c3, c4, c5⟩ := GlobalTheory.T.fibreSection_linearComb_exists_unique_thetaAction u.V u.A (PadicAlgCl p) S.N S.J s b
  choose s' hs' using fun i => (c4 θ (s i)).exists
  obtain ⟨σ', hσ'⟩ := (c4 θ σ).exists
  have hσ'c : IsComb u.A s' b σ' := (c3 θ s' σ σ' hs' hσ).1 hσ'
  have hσ'c2 := c5 S.J (fun i j => y₀ (algebraMap o S.R (S.ρ t j i))) s' b σ' (fun i => hθa i _ (hs' i)) hσ'c
  obtain ⟨hbij, hlin⟩ := GlobalTheory.UT.expBijF_and_expandsF_lin hLL u.V _ hadm u.D u.A u.G u.semi u.U
  obtain ⟨hb1, hb2⟩ := hbij (PadicAlgCl p) S.N hN1 w₀ hw₀
  obtain ⟨Φ', hΦ'⟩ := (hb1 σ').exists
  have hrel := GlobalTheory.T.symmetricLift_oddOrder_acts_as_expansionOperator hLL u.V _ hadm u.D u.A u.G u.semi u.U (PadicAlgCl p) S.N hodd q _ hqx θ hθs w₀ hw₀ w hw
    σ σ' Φ Φ' hΦ hΦ' hσ'
  have hwt := ((GlobalTheory.UT.TorusWeight.torus_weight hLL u.V _ hadm u.D u.A u.G u.semi u.U (PadicAlgCl p) S.N hodd q τ hqy
    hqt w hw).2 Φ Φ').1 hrel
  set κ : PadicAlgCl p := y₀ (algebraMap o S.R S.ζN) ^ (l.wt α t).val with hκ
  have hΦeq : Φ' = (κ - 1) • Φ + Φ := by
    rw [sub_smul, one_smul, sub_add_cancel]
    refine fam_ext fun β j => ?_
    rw [hwt β j, smul_f, ← constBF_eq]
    by_cases hβ : ∀ z : u.D.toPre.X, β ≠ α + S.N • z
    · rw [hsupp β hβ j, mul_zero, mul_zero]
    · push Not at hβ
      obtain ⟨z, rfl⟩ := hβ
      rw [hτ, hκ]
      simp
  obtain ⟨⟨σ'', hσ''⟩, -⟩ := GlobalTheory.T.fibreSection_linearComb_exists_unique_thetaAction u.V u.A (PadicAlgCl p) S.N (Fin 2) (fun _ => σ) ![κ - 1, 1]
  have hσ''e : u.U.ExpandsF (PadicAlgCl p) S.N w₀ σ'' ((κ - 1) • Φ + Φ) := by
    refine hlin (PadicAlgCl p) S.N w₀ σ σ σ'' Φ Φ (κ - 1) hΦ hΦ fun j => ?_
    rw [hσ'' j, Fin.sum_univ_two]
    simp [liftFun, cF]
  have heq : σ'' = σ' := (hb2 Φ').unique (hΦeq ▸ hσ''e) hΦ'
  subst heq
  obtain ⟨v1, -, v3, -⟩ := GlobalTheory.T.isFibreSectionValueInFrame_linear_unique_exists h1 u.V u.A (PadicAlgCl p) S.N (x h) (e h)
  have a1 := v1 S.J s b _ σ hσ (fun i => hval i h)
  have a2 := v1 S.J s _ _ σ'' hσ'c2 (fun i => hval i h)
  have a3 := v1 (Fin 2) (fun _ => σ) _ _ σ'' hσ'' (fun _ => a1)
  rw [v3 _ _ _ a2 a3, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

end GlobalTheory.TestFibre
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusOperatorEigenOfExpansionSingleClassStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusOperator_eigen_of_expansion_single_class : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)) (rig : LB.Gen (u.A.L.pull (eSec u.A.A))) (e : ∀ a, FrameAt u.A (x a)) (th : SecA u.A (PadicAlgCl p) 1) (s : S.J → SecA u.A (PadicAlgCl p) S.N), PtsOver u x → SecsOver u x rig e th s → ∀ (w₀ : W0 u.U.toUnifPre), w₀.IsGen → ∀ (α : u.D.toPre.X) (b : S.J → PadicAlgCl p) (σ : SecA u.A (PadicAlgCl p) S.N) (Φ : Fam u.D.toPre (PadicAlgCl p) S.N), IsComb u.A s b σ → u.U.ExpandsF (PadicAlgCl p) S.N w₀ σ Φ → (∀ β, (∀ z : u.D.toPre.X, β ≠ α + S.N • z) → ∀ j, (Φ.s β).f j = 0) → ∀ (t : S.perp l.yy.ker) (h : S.Gam), ∑ j, (∑ i, y₀ (algebraMap o S.R (S.ρ t j i)) * b i) * y₀ ⟨S.ev h j, S.ev_mem h j⟩ = y₀ (algebraMap o S.R S.ζN) ^ (l.wt α t).val * ∑ j, b j * y₀ ⟨S.ev h j, S.ev_mem h j⟩ := by
  first | exact @GlobalTheory.TestFibre.eigen_of_expansion_in_class | exact GlobalTheory.TestFibre.eigen_of_expansion_in_class | (intros; apply GlobalTheory.TestFibre.eigen_of_expansion_in_class <;> assumption)
end
end
