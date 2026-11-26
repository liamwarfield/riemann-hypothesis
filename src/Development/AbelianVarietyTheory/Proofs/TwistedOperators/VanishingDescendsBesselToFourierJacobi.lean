module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralLeOfTsum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralStripEqZeroOfRealModulationVanishing

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselToJacobiFlatMapEquivariant
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselToJacobiFlatMapEquivariant
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.AscFlatEqui

open GlobalTheory.EvalAtZero GlobalTheory.Unf.FlatCommBF GlobalTheory.FlatEqui

section
variable {D : D7}

theorem evalAt_rad (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesL D ρ) (J : JacL D ρ) (s : StBF ψ B J)
    (om' : Om B.V₀ J.W) (hom' : IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om') (Ψ : WO B.V J.W → ℂ) (hΨ : IsThetaFunO ψ B.V J.W Ψ) :
    ∀ (u : UX D ρ) h₀, ∀ n ∈ radX J.d, ∀ h', evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) = s.om₀ (B.o.emb (h₀, 1), 1) (opA ψ J.d B.o B.ζ s.om₀ n h' (evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)))) := by
  have FS := fun f hf => GlobalTheory.T.mixedModelFormulasWittSource_proof D ψ B.V B.V₀ J.W ρ B.d s.χV s.χW s.om om' s.weil hom' s.vS.μ s.vS.𝓕 s.vS.covol f hf
  have FT := fun f hf => GlobalTheory.T.mixedModelFormulas_wittTarget D ψ B.V₀ J.W J.W₀ ρ J.d s.χV s.χW om' s.om₀ hom' s.weil₀ s.vT.μ s.vT.𝓕 s.vT.covol f hf
  have MV := fun x => (GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ s.weil.std).1 B.V B.V₀ J.W ρ B.d s.vS.μ s.vS.𝓕 s.vS.covol Ψ hΨ x
  set y₀ := yZero B.V₀ ρ (vecB B.o B.ζ) with hy₀
  intro u h₀ n hn h'
  obtain ⟨b, c, rfl⟩ := ((GlobalTheory.MixPer.flag_jacobi_structure D J.W J.W₀ ρ J.d).2.1 n).1 hn
  set k := J.d.nB b * J.d.nC c * J.d.emb0 h' with hk
  have hks : k ∈ stabX J.d := mul_mem (radX_le_stabX J.d hn) (wittSmallGroupEmbedding_mem_pointwiseStabilizerIsotropic J.d h')
  have hkx : mt J.W k⁻¹ ⬝ J.d.jX = J.d.jX := inv_mem hks
  have e1 : (embA B.d B.o h₀, k) = (embA B.d B.o h₀, 1) * (1, k) := Prod.ext (mul_one _).symm (one_mul _).symm
  have hk1 := s.weil.om_pres (1, k) Ψ hΨ
  have s1 : B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 (s.om (embA B.d B.o h₀, k) Ψ) (xZero J.d ⬝ u.1.1) =
      om' (B.o.emb (h₀, 1), 1) (om' (1, k) (B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 Ψ (xZero J.d ⬝ u.1.1))) := by
    have hc := (FS _ hk1).core (B.o.emb (h₀, 1)) (xZero J.d ⬝ u.1.1)
    have ht := (FS _ hΨ).target k (xZero J.d ⬝ u.1.1)
    change B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 _ _ = _ at hc ht
    rw [e1, map_mul, Module.End.mul_apply, embA_apply, hc]
    change om' _ (B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 _ _) = _
    rw [ht, ← Matrix.mul_assoc,
      xZero, hkx]
    rfl
  set G := B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 Ψ (xZero J.d ⬝ u.1.1) with hG
  have hGt : IsThetaFunO ψ B.V₀ J.W G := MV _
  have e2 : ((1 : GA D B.V₀), k) = (1, J.d.nB b) * ((1, J.d.nC c) * (1, J.d.emb0 h')) :=
    Prod.ext (by rw [Prod.fst_mul, Prod.fst_mul, mul_one, mul_one]) (by rw [Prod.snd_mul, Prod.snd_mul, hk, mul_assoc])
  have h3 := hom'.om_pres (1, J.d.emb0 h') G hGt
  have h2 := hom'.om_pres (1, J.d.nC c) _ h3
  have hy : mt B.V₀ (B.o.emb (h₀, 1))⁻¹ ⬝ y₀ = y₀ := by
    rw [hy₀, yZero_vecB, ← map_inv, Prod.inv_mk, inv_one, ← Matrix.mul_assoc, B.o.emb_jB, mt_one, Matrix.mul_one]
  have hpt : ptT J.d B.V₀ y₀ (J.d.nB b * J.d.nC c) = GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj B.V₀ J.W₀ (y₀ ⬝ b) := by
    rw [ptT_nB_mul_nC, ← ptT_nB_mul_nC J.d B.V₀ y₀ b 0, J.d.nC_zero, mul_one, ptT,
      GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.wittSmallProjection_wittNB_inv_mul_adjointInclusion]
  have hcen : cenT J.d B.V₀ y₀ (J.d.nB b * J.d.nC c) = J.d.qT B.V₀ c y₀ :=
    (GlobalTheory.T.jacobi_action_target_flag_unipotent_hom_equivariant D ψ J.W J.W₀ B.V₀ ρ J.d y₀ (fun v hv => yZero_mul B.V₀ _ hv)).1 b c
  have t1 := (FT _ hGt).core h' y₀
  have t2 := (FT _ h3).centre c y₀
  have t3 := (FT _ h2).unip b y₀
  have t4 := (FT _ (hom'.om_pres (1, k) G hGt)).source (B.o.emb (h₀, 1)) y₀
  have t5 : om' (1, k) G = om' (1, J.d.nB b) (om' (1, J.d.nC c) (om' (1, J.d.emb0 h') G)) := by
    rw [e2, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  change (_root_.I195MixedCoordinates_14b5fd3aa93c7f4842f1a892.source B.d) J.W ψ s.vS.μ s.vS.𝓕 _ _ = _ at s1
  rw [evalAt, s1]
  change (_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target J.d) B.V₀ ψ s.vT.μ s.vT.𝓕 _ _ = _
  rw [t4, hy, t5, t3, t2, t1]
  show _ = s.om₀ (B.o.emb (h₀, 1), 1) (jacT ψ J.d B.V₀ y₀ (J.d.nB b * J.d.nC c) (s.om₀ (1, h') _))
  unfold jacT
  simp only [hpt, hcen, heisO_smul, evalAt, hG]
  rfl

theorem evalAt_levi (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesL D ρ) (J : JacL D ρ) (s : StBF ψ B J)
    (om' : Om B.V₀ J.W) (hom' : IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om') (Ψ : WO B.V J.W → ℂ) (hΨ : IsThetaFunO ψ B.V J.W Ψ) :
    ∀ (u γ : UX D ρ), evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, J.d.levi γ.1) Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) = evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ (γ⁻¹ * u).1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) := by
  have FS := fun f hf => GlobalTheory.T.mixedModelFormulasWittSource_proof D ψ B.V B.V₀ J.W ρ B.d s.χV s.χW s.om om' s.weil hom' s.vS.μ s.vS.𝓕 s.vS.covol f hf
  have FT := fun f hf => GlobalTheory.T.mixedModelFormulas_wittTarget D ψ B.V₀ J.W J.W₀ ρ J.d s.χV s.χW om' s.om₀ hom' s.weil₀ s.vT.μ s.vT.𝓕 s.vT.covol f hf
  have MV := fun x => (GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ s.weil.std).1 B.V B.V₀ J.W ρ B.d s.vS.μ s.vS.𝓕 s.vS.covol Ψ hΨ x
  intro u γ
  have e0 : (mt J.W (J.d.levi γ.1)⁻¹ ⬝ (xZero J.d ⬝ u.1.1) : Mx D J.W.rank ρ) = xZero J.d ⬝ (γ⁻¹ * u).1.1 := by
    rw [← map_inv, ← Matrix.mul_assoc, levi_xZero, Matrix.mul_assoc, Subgroup.coe_mul, Subgroup.coe_inv,
      Units.val_mul]
  have ht := (FS _ hΨ).target (J.d.levi γ.1) (xZero J.d ⬝ u.1.1)
  change (_root_.I195MixedCoordinates_14b5fd3aa93c7f4842f1a892.source B.d) J.W ψ s.vS.μ s.vS.𝓕 _ _ = _ at ht
  have hl := (FT _ (MV (xZero J.d ⬝ (γ⁻¹ * u).1.1))).levi γ.1 (yZero B.V₀ ρ (vecB B.o B.ζ))
  rw [evalAt, evalAt, ht, e0]
  change (_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target J.d) B.V₀ ψ s.vT.μ s.vT.𝓕 _ _ = _
  rw [hl, yZero_mul B.V₀ _ γ.2, det_UX, halfMod_UX, map_one,
    Circle.coe_one, Complex.ofReal_one, mul_one, one_smul]


set_option maxHeartbeats 400000 in
theorem flBF_om : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesL D ρ) (J : JacL D ρ) (s : StBF ψ B J) (om' : Om B.V₀ J.W), IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om' → ∀ (Ψ : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W Ψ → ∀ h₀, ∀ n ∈ radX J.d, ∀ h', flBF s (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) = s.om₀ (B.o.emb (h₀, 1), 1) (opA ψ J.d B.o B.ζ s.om₀ n h' (flBF s Ψ)) := by
  intro D ψ ρ B J s om' hom' Ψ hΨ h₀ n hn h'
  have hstd : IsStdChar D ψ (-1) := s.weil.std
  obtain ⟨hloc, hsc, -⟩ := GlobalTheory.UnitU.topology D ρ
  haveI := hloc
  haveI := hsc
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  haveI : SFinite s.vU.ν := @sFinite_of_haar (UX D ρ) _ _ _ hloc hsc s.vU.ν s.vU.unit.1
  obtain ⟨hbase, -, hx0, -⟩ := GlobalTheory.Unf.base_point D J.W J.W₀ ρ J.d
  have hlin : LinearIndependent D.host.E J.d.e.transpose := hbase.1
  have hev := And.intro (evalAt_rad D ψ ρ B J s om' hom' Ψ hΨ) (evalAt_levi D ψ ρ B J s om' hom' Ψ hΨ)
  have hom1 : s.om 1 Ψ = Ψ := by rw [map_one]; rfl

  have e3 : ∀ u : UX D ρ, evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1)
      (yZero B.V₀ ρ (vecB B.o B.ζ)) = s.om₀ (1, h') (evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ u.1.1)
      (yZero B.V₀ ρ (vecB B.o B.ζ))) := by
    intro u
    have h := hev.1 u 1 1 (one_mem _) h'
    rw [map_one, one_mul, ← Prod.one_eq_mk, map_one, ← Prod.one_eq_mk, map_one] at h
    rw [h]
    simp only [opA, jacT_one]
    rfl
  have e2 : ∀ u : UX D ρ, evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1)
      (yZero B.V₀ ρ (vecB B.o B.ζ)) = opA ψ J.d B.o B.ζ s.om₀ n h' (evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ
      (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ))) := by
    intro u
    have h := hev.1 u 1 n hn h'
    rw [map_one, ← Prod.one_eq_mk, map_one, ← Prod.one_eq_mk, map_one] at h
    exact h

  have hmix := GlobalTheory.MixValues.mixed_values D ψ hstd
  have thev : ∀ Φ, IsThetaFunO ψ B.V J.W Φ → ∀ u : UX D ρ, IsThetaFunO ψ B.V₀ J.W₀
      (evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Φ (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ))) :=
    fun Φ hΦ u => hmix.2 B.V₀ J.W J.W₀ ρ J.d s.vT.μ s.vT.𝓕 s.vT.covol _
      (hmix.1 B.V B.V₀ J.W ρ B.d s.vS.μ s.vS.𝓕 s.vS.covol Φ hΦ _) _
  have thom : ∀ p, IsThetaFunO ψ B.V J.W (s.om p Ψ) := fun p => s.weil.om_pres p Ψ hΨ
  have hFL := GlobalTheory.Unf.Flat.flatLaw D ψ hstd B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s.vS s.vT s.vU J.d.e hlin
    (yZero B.V₀ ρ (vecB B.o B.ζ))
  have thflat : ∀ p, IsThetaFunO ψ B.V₀ J.W₀ (flBF s (s.om p Ψ)) := fun p => by
    have h := (hFL _ (thom p)).2
    rw [← hx0] at h
    exact h
  obtain ⟨M, hMi, hM⟩ := GlobalTheory.Unf.flatFun_majorant D ψ B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s.vS s.vT s.χV s.χW s.om s.weil s.vU J.d.e hlin
    Ψ hΨ {1, (1, J.d.emb0 h'), (1, n * J.d.emb0 h'), (embA B.d B.o h₀, n * J.d.emb0 h')} (Set.toFinite _).isCompact
  simp only [← hx0] at hM
  have bound : ∀ p ∈ ({1, (1, J.d.emb0 h'), (1, n * J.d.emb0 h'), (embA B.d B.o h₀, n * J.d.emb0 h')} :
      Set (GA D B.V × GA D J.W)), ∀ (u : UX D ρ) w, ‖star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕
      (s.om p Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w‖ ≤ M u :=
    fun p hp u w => hM p hp _ w u
  have hmc := GlobalTheory.MixCont.mixed_coords_continuous D ψ B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s.vS s.vT s.χV s.χW s.om s.weil Ψ hΨ
  have hxu : Continuous fun u : UX D ρ => xZero J.d ⬝ u.1.1 :=
    continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val)
  have cont : ∀ p, Continuous fun q : UX D ρ × WO B.V₀ J.W₀ => star (psiUni ψ q.1.1) *
      evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om p Ψ) (xZero J.d ⬝ q.1.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) q.2 := by
    intro p
    have h1 : Continuous fun q : UX D ρ × WO B.V₀ J.W₀ => ((p, xZero J.d ⬝ q.1.1.1, yZero B.V₀ ρ (vecB B.o B.ζ), q.2) :
        (GA D B.V × GA D J.W) × Mx D J.W.rank ρ × Mx D B.V₀.rank ρ × WO B.V₀ J.W₀) :=
      continuous_const.prodMk ((hxu.comp continuous_fst).prodMk (continuous_const.prodMk continuous_snd))
    have h2 := hmc.2.comp h1
    have h3 : Continuous fun q : UX D ρ × WO B.V₀ J.W₀ => star (psiUni ψ q.1.1) :=
      ((continuous_psiUni ψ hstd.1.1 ρ).comp continuous_fst).star
    exact h3.mul h2
  have hci := GlobalTheory.CommInt.om_integral_comm D ψ B.V₀ J.W₀ s.χV s.χW s.om₀ s.weil₀ (UX D ρ) s.vU.ν

  have hF : ∀ u : UX D ρ, (fun w => star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w) = star (psiUni ψ u.1) • evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) :=
    fun u => rfl
  have hG : ∀ (u : UX D ρ) w, s.om₀ (1, h') (fun w => star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w) w =
      star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w := by
    intro u w
    rw [hF, map_smul, e3]
    rfl
  have step1 : ∀ w, s.om₀ (1, h') (flBF s Ψ) w = ∫ u, star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w ∂s.vU.ν := by
    intro w
    have h := hci (fun u w => star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w) (1, h') M
      (fun u => by rw [hF]; exact GlobalTheory.OrientedHeis.theta_smul _ (thev Ψ hΨ u))
      (by have h := cont 1; rw [hom1] at h; exact h)
      (by simp only [hG]; exact cont _)
      hMi
      (fun u w => ⟨by have h := bound 1 (by simp) u w; rw [hom1] at h; exact h, by rw [hG]; exact bound _ (by simp) u w⟩)
      (by have h := thflat 1; rw [hom1] at h; exact h) w
    exact h.trans (integral_congr_ae (Filter.Eventually.of_forall fun u => hG u w))

  have hF2 : ∀ u : UX D ρ, (fun w => star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w) =
      star (psiUni ψ u.1) • evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) := fun u => rfl
  have hG2 : ∀ (u : UX D ρ) w, s.om₀ (B.o.emb (h₀, 1), 1) (fun w => star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w) w =
      star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w := by
    intro u w
    rw [hF2, map_smul, e2, hev.1 u h₀ n hn h']
    rfl
  have step2 : ∀ w, s.om₀ (B.o.emb (h₀, 1), 1) (fun w => ∫ u, star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w ∂s.vU.ν) w =
      ∫ u, star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w ∂s.vU.ν := by
    intro w
    have h := hci (fun u w => star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w) (B.o.emb (h₀, 1), 1) M
      (fun u => by rw [hF2]; exact GlobalTheory.OrientedHeis.theta_smul _ (thev _ (thom _) u))
      (cont _)
      (by simp only [hG2]; exact cont _)
      hMi
      (fun u w => ⟨bound _ (by simp) u w, by rw [hG2]; exact bound _ (by simp) u w⟩)
      (thflat _) w
    exact h.trans (integral_congr_ae (Filter.Eventually.of_forall fun u => hG2 u w))

  have hopa : opA ψ J.d B.o B.ζ s.om₀ n h' (flBF s Ψ) =
      fun w => ∫ u, star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w ∂s.vU.ν := by
    funext w
    have h1 : s.om₀ (1, h') (flBF s Ψ) = fun w => ∫ u, star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w ∂s.vU.ν :=
      funext step1
    show jacT ψ J.d B.V₀ (yZero B.V₀ ρ (vecB B.o B.ζ)) n (s.om₀ (1, h') (flBF s Ψ)) w = _
    rw [h1, jacT_integral]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    have h2 : (fun w => star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w) =
        star (psiUni ψ u.1) • s.om₀ (1, h') (evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ))) := by
      rw [e3]; rfl
    dsimp only
    rw [h2, jacT_smul, e2]
    rfl
  rw [hopa]
  funext w
  exact (step2 w).symm

theorem flBF_levi (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesL D ρ) (J : JacL D ρ) (s : StBF ψ B J)
    (om' : Om B.V₀ J.W) (hom : IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om') (Ψ : WO B.V J.W → ℂ)
    (hΨ : IsThetaFunO ψ B.V J.W Ψ) (γ : UX D ρ) :
    flBF s (s.om (1, J.d.levi γ.1) Ψ) = star (psiUni ψ γ.1) • flBF s Ψ := by
  have : BorelSpace (UX D ρ) := ⟨rfl⟩
  have := s.vU.unit.1
  funext w
  have he := evalAt_levi D ψ ρ B J s om' hom Ψ hΨ
  simp only [flBF, flatS, flatAt, flatFun, Pi.smul_apply, smul_eq_mul, he]
  rw [← integral_const_mul, ← integral_mul_left_eq_self _ γ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [inv_mul_cancel_left]
  rw [Subgroup.coe_mul, psiUni_mul ψ J.d γ.2 u.2, star_mul', mul_assoc]

theorem flBF_equivariant_of : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesL D ρ) (J : JacL D ρ) (s : StBF ψ B J) (om' : Om B.V₀ J.W), IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om' → ∀ (Ψ : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W Ψ → ∀ h₀, ∀ n ∈ flagN J.d, ∀ h', flBF s (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) = star (psiFlag ψ J.d n) • s.om₀ (B.o.emb (h₀, 1), 1) (opA ψ J.d B.o B.ζ s.om₀ n h' (flBF s Ψ)) := by
  intro D ψ ρ B J s om' hom Ψ hΨ h₀ n hn h'
  obtain ⟨γ, hγ, b, c, rfl⟩ := ((flag_jacobi_structure D J.W J.W₀ ρ J.d).1 n).1 hn
  have hr : J.d.nB b * J.d.nC c ∈ radX J.d := mul_mem (nB_mem_radX J.d b) (nC_mem_radX J.d c)
  have e : s.om (embA B.d B.o h₀, J.d.levi γ * (J.d.nB b * J.d.nC c) * J.d.emb0 h') Ψ =
      s.om (1, J.d.levi γ) (s.om (embA B.d B.o h₀, J.d.nB b * J.d.nC c * J.d.emb0 h') Ψ) := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, mul_assoc]
  rw [e, flBF_levi ψ ρ B J s om' hom _ (s.weil.om_pres _ _ hΨ) ⟨γ, hγ⟩,
    flBF_om D ψ ρ B J s om' hom Ψ hΨ h₀ _ hr h', psiFlag_levi_mul ψ J.d γ (radX_le_stabX J.d hr), opA, opA,
    jacT_levi_mul ψ J.d B.V₀ _ (yZero_mul B.V₀ _ hγ)]

end

theorem flBF_equivariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesL D ρ) (J : JacL D ρ) (s : StBF ψ B J), ∀ Ψ, IsThetaFunO ψ B.V J.W Ψ → ∀ h₀, ∀ n ∈ flagN J.d, ∀ h', flBF s (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) = star (psiFlag ψ J.d n) • s.om₀ (B.o.emb (h₀, 1), 1) (opA ψ J.d B.o B.ζ s.om₀ n h' (flBF s Ψ)) := by
  intro D ψ ρ B J s Ψ hΨ h₀ n hn h'
  obtain ⟨om', hom'⟩ := (GlobalTheory.Unf.descent_of_weilDatumExists D (GlobalTheory.WeilDatumExistence.weilDatumExists D) ψ _ _ _ _ s.om s.weil).1 B.V₀ ρ B.d
  exact flBF_equivariant_of D ψ ρ B J s om' hom' Ψ hΨ h₀ n hn h'

end GlobalTheory.AscFlatEqui

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselToJacobiFlatMapEquivariantStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselToJacobiFlatMap_equivariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesL D ρ) (J : JacL D ρ) (s : StBF ψ B J), ∀ Ψ, IsThetaFunO ψ B.V J.W Ψ → ∀ h₀, ∀ n ∈ flagN J.d, ∀ h', flBF s (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) = star (psiFlag ψ J.d n) • s.om₀ (B.o.emb (h₀, 1), 1) (opA ψ J.d B.o B.ζ s.om₀ n h' (flBF s Ψ)) := by
  first | exact @GlobalTheory.AscFlatEqui.flBF_equivariant | exact GlobalTheory.AscFlatEqui.flBF_equivariant | (intros; apply GlobalTheory.AscFlatEqui.flBF_equivariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselMeanPeriodConvergesContinuous
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselMeanPeriodConvergesContinuous
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.BesMean

theorem continuous_integral_of_le {P X : Type} [TopologicalSpace P] [FirstCountableTopology P] [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] {T : P → X → ℂ}
    (hT : Continuous fun q : P × X => T q.1 q.2) {b : P → ℝ} (hb : Continuous b) (hle : ∀ p x, ‖T p x‖ ≤ b p) :
    Continuous fun p => ∫ x, T p x ∂μ := by
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  refine continuousAt_of_dominated (bound := fun _ => b p₀ + 1) ?_ ?_ (integrable_const _) ?_
  · exact .of_forall fun p => (hT.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [hb.continuousAt.eventually (gt_mem_nhds (lt_add_one (b p₀)))] with p hp
    exact .of_forall fun x => (hle p x).trans hp.le
  · exact .of_forall fun x => (hT.comp (continuous_id.prodMk continuous_const)).continuousAt

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem ptT_rat {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) (z : Fin S.rank → D.host.E) {n : GA D T}
    (hn : n ∈ GQ T) : ptT d S (yZero S ρ z) n ∈ ratMx D T₀.rank S.rank := by
  have hy : yZero S ρ z ∈ ratMx D S.rank ρ := by
    refine neg_mem ⟨vecMulVec z fun i : Fin ρ => if i.1 + 1 = ρ then 1 else 0, ?_⟩
    ext i j
    change incA D (z i * if j.1 + 1 = ρ then 1 else 0) = incA D (z i) * ell D ρ j
    rw [map_mul, ell]
    split_ifs
    · rw [map_one]
    · rw [map_zero]
  exact ratMx_mul (rat_mem _) (ratMx_mul ((mem_GQ_iff T _).1 (inv_mem hn))
    (ratMx_mul (rat_mem _) (ratMx_smul _ (ratMx_mul (ratMx_adj hy) (rat_mem _)))))

theorem heisO_zero_pt (S T : HSp D) (w : WO S T) (f : WO S T → ℂ) : heisO ψ S T w f 0 = f w := by
  rw [heisO, symplOH_zero_left, AddChar.map_zero_eq_one, one_mul, zero_add]

variable {ρ : ℕ} {B : BesL D ρ} {J : JacL D ρ} (s : StBF ψ B J) {Φ : WO B.V J.W → ℂ}

def ker (Φ : WO B.V J.W → ℂ) (h₀ : GA D B.A) (g : GA D J.W) : ℂ := flBF s (s.om (embA B.d B.o h₀, g) Φ) 0

theorem ker_val (hΦ : IsThetaFunO ψ B.V J.W Φ) (h₀ : GA D B.A) {n : GA D J.W} (hn : n ∈ flagN J.d)
    (h' : GA D J.W₀) (h : GA D J.W) :
    ker s Φ h₀ (n * J.d.emb0 h' * h) =
      star (psiFlag ψ J.d n) * fjKer ψ J.d B.o B.ζ s.om₀ (flBF s (s.om (1, h) Φ)) h₀ n h' := by
  have e : s.om (embA B.d B.o h₀, n * J.d.emb0 h' * h) Φ = s.om (embA B.d B.o h₀, n * J.d.emb0 h') (s.om (1, h) Φ) := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  rw [ker, e, GlobalTheory.AscFlatEqui.flBF_equivariant D ψ ρ B J s _ (s.weil.om_pres _ _ hΦ) h₀ n hn h']
  rfl

theorem theta_flBF (hΦ : IsThetaFunO ψ B.V J.W Φ) : IsThetaFunO ψ B.V₀ J.W₀ (flBF s Φ) := by
  obtain ⟨hb, -, hx, -⟩ := GlobalTheory.Unf.base_point D J.W J.W₀ ρ J.d
  have h := (GlobalTheory.Unf.Flat.flatLaw D ψ s.weil.std B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s.vS s.vT s.vU J.d.e hb.1
    (yZero B.V₀ ρ (vecB B.o B.ζ)) Φ hΦ).2
  rw [← hx] at h
  exact h

theorem ker_left (hΦ : IsThetaFunO ψ B.V J.W Φ) {γ : GA D B.A} (hγ : γ ∈ GQ B.A) (h₀ : GA D B.A) (g : GA D J.W) :
    ‖ker s Φ (γ * h₀) g‖ = ‖ker s Φ h₀ g‖ := by
  have hΨ := s.weil.om_pres (embA B.d B.o h₀, g) _ hΦ
  have hΞ := theta_flBF s hΨ
  have e : s.om (embA B.d B.o (γ * h₀), g) Φ =
      s.om (embA B.d B.o γ, 1 * J.d.emb0 1) (s.om (embA B.d B.o h₀, g) Φ) := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, map_one, one_mul, one_mul, map_mul (embA B.d B.o)]
  have e1 : ((1, 1) : GA D B.V₀ × GA D J.W₀) = 1 := rfl
  have hp : ‖star (psiFlag ψ J.d 1)‖ = 1 := by rw [norm_star]; exact s.weil.std.1.2.1 _
  rw [ker, e, GlobalTheory.AscFlatEqui.flBF_equivariant D ψ ρ B J s _ hΨ γ 1 (one_mem _) 1, opA, jacT_one, e1, map_one,
    Module.End.one_apply, id, Pi.smul_apply, smul_eq_mul, norm_mul, hp, one_mul,
    s.weil₀.om_aut _ (B.o.emb_mem_GQ hγ (one_mem _)) 1 (one_mem _) _ hΞ]
  rfl

theorem ker_right (hΦ : IsThetaFunO ψ B.V J.W Φ) (h₀ : GA D B.A) {n : GA D J.W} (hn : n ∈ flagN J.d) (hnq : n ∈ GQ J.W)
    {h' : GA D J.W₀} (hhq : h' ∈ GQ J.W₀) (g : GA D J.W) :
    ‖ker s Φ h₀ (n * J.d.emb0 h' * g)‖ = ‖ker s Φ h₀ g‖ := by
  have hΨ := s.weil.om_pres (embA B.d B.o h₀, g) _ hΦ
  have hΞ := theta_flBF s hΨ
  have e : s.om (embA B.d B.o h₀, n * J.d.emb0 h' * g) Φ =
      s.om (embA B.d B.o 1, n * J.d.emb0 h') (s.om (embA B.d B.o h₀, g) Φ) := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, map_one, one_mul]
  have e2 : ((B.o.emb (1, 1), 1) : GA D B.V₀ × GA D J.W₀) = 1 := by
    rw [show ((1, 1) : GA D B.A × GA D B.L) = 1 from rfl, map_one]; rfl
  obtain ⟨δ, hδ⟩ := ptT_rat J.d B.V₀ (vecB B.o B.ζ) hnq
  have hψ := s.weil.std.1.2.1
  have hp : ‖star (psiFlag ψ J.d n)‖ = 1 := by rw [norm_star]; exact hψ _
  have h2 := (s.weil₀.om_pres (1, h') _ hΞ).quasi δ 0
  rw [add_zero, s.weil₀.om_aut 1 (one_mem _) h' hhq _ hΞ] at h2
  rw [ker, e, GlobalTheory.AscFlatEqui.flBF_equivariant D ψ ρ B J s _ hΨ 1 n hn h', e2, map_one, Module.End.one_apply,
    Pi.smul_apply, smul_eq_mul, norm_mul, hp, one_mul, opA, jacT, Pi.smul_apply, heisO_zero_pt, ← hδ, smul_eq_mul,
    norm_mul, hψ, one_mul]
  refine (congrArg norm h2).trans ?_
  rw [norm_mul, hψ, one_mul]
  rfl

theorem continuous_ker (hΦ : IsThetaFunO ψ B.V J.W Φ) :
    Continuous fun p : GA D J.W × GA D B.A => ker s Φ p.2 p.1 := by
  obtain ⟨hb, -, hx, -⟩ := GlobalTheory.Unf.base_point D J.W J.W₀ ρ J.d
  have hemb : Continuous (embA B.d B.o) :=
    B.d.continuous_embed.comp (B.o.continuous_emb.comp (continuous_id.prodMk continuous_const))
  have h2 := GlobalTheory.FlatCont.flatAt_om_continuous D ψ B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s.vS s.vT s.χV s.χW s.om s.weil s.vU J.d.e hb.1 Φ hΦ
  rw [← hx] at h2
  have h3 : Continuous fun p : GA D J.W × GA D B.A =>
      (((embA B.d B.o p.2, p.1), yZero B.V₀ ρ (vecB B.o B.ζ), 0) :
        (GA D B.V × GA D J.W) × Mx D B.V₀.rank ρ × WO B.V₀ J.W₀) :=
    ((hemb.comp continuous_snd).prodMk continuous_fst).prodMk continuous_const
  have h4 := h2.comp h3
  simp only [Function.comp_def] at h4
  simp only [ker, flBF, flatS]
  exact h4

theorem ker_le (hΦ : IsThetaFunO ψ B.V J.W Φ) : ∃ (C : ℝ) (a b : ℕ), 0 ≤ C ∧ ∀ h₀ g,
    ‖ker s Φ h₀ g‖ ≤ C * quotHeight B.A h₀ ^ a * height J.W g ^ b := by
  obtain ⟨hb, -, hx, -⟩ := GlobalTheory.Unf.base_point D J.W J.W₀ ρ J.d
  obtain ⟨C₁, A₁, hC₁⟩ := GlobalTheory.FlatSup.flat_sup_growth D ψ B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s J.d.e hb.1 Φ hΦ
  obtain ⟨C₄, hC₄⟩ := GlobalTheory.EmbHeight.unitaryAdelicHeight_wittEmbedding_le D B.V B.V₀ ρ B.d
  obtain ⟨C₅, a₅, hC₅⟩ := GlobalTheory.EmbHeight.height_emb_le D B.V₀ B.A B.L B.o
  rw [← hx] at hC₁
  refine ⟨|C₁| * (|C₄| * (|C₅| * 2 ^ a₅)) ^ A₁, a₅ * A₁, A₁, by positivity, fun h₀ g => ?_⟩
  obtain ⟨γ, hγ, e1⟩ := exists_height_le_two_mul_quotHeight B.A h₀
  rw [← ker_left s hΦ hγ]
  have p1 := height_pos B.A (γ * h₀)
  have p2 := height_pos J.W g
  have p3 := height_pos B.V (embA B.d B.o (γ * h₀))
  have p4 := height_pos B.V₀ (B.o.emb (γ * h₀, 1))
  have q0 := quotHeight_pos B.A h₀
  have f1 : height B.V (embA B.d B.o (γ * h₀)) ≤ |C₄| * (|C₅| * (2 * quotHeight B.A h₀) ^ a₅) := by
    refine (hC₄ _).trans (mul_le_mul (le_abs_self _) ((hC₅ _).trans ?_) p4.le (abs_nonneg _))
    exact mul_le_mul (le_abs_self _) (pow_le_pow_left₀ p1.le e1 _) (pow_pos p1 _).le (abs_nonneg _)
  calc _ ≤ C₁ * (height B.V (embA B.d B.o (γ * h₀)) * height J.W g) ^ A₁ := hC₁ _ _ _ _
    _ ≤ |C₁| * (|C₄| * (|C₅| * (2 * quotHeight B.A h₀) ^ a₅) * height J.W g) ^ A₁ :=
        mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (mul_pos p3 p2).le (mul_le_mul_of_nonneg_right f1 p2.le) _)
          (pow_pos (mul_pos p3 p2) _).le (abs_nonneg _)
    _ = _ := by simp only [mul_pow, pow_mul]; ring

theorem ker_le_quot (hΦ : IsThetaFunO ψ B.V J.W Φ) : ∃ (C : ℝ) (a b : ℕ), 0 ≤ C ∧ ∀ h₀, ∀ n ∈ flagN J.d, ∀ h' h,
    ‖ker s Φ h₀ (n * J.d.emb0 h' * h)‖ ≤ C * quotHeight B.A h₀ ^ a * (quotHeight J.W₀ h' * height J.W h) ^ b := by
  obtain ⟨C, a, b, hC0, hC⟩ := ker_le s hΦ
  obtain ⟨C₃, hC₃⟩ := GlobalTheory.EmbHeight.unitaryAdelicHeight_wittEmbedding_le D J.W J.W₀ ρ J.d
  obtain ⟨KN, hKN, cN⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D J.W ρ J.d.e (isIsoSub_e J.d)).1
  obtain ⟨M, hM⟩ := exists_height_le_of_isCompact J.W (hKN.image continuous_subtype_val)
  refine ⟨C * (|M| * (|C₃| * 2)) ^ b, a, b, by positivity, fun h₀ n hn h' h => ?_⟩
  obtain ⟨γ, hγ, e1⟩ := exists_height_le_two_mul_quotHeight J.W₀ h'
  obtain ⟨δ, hδ, m, hm, e⟩ := cN ⟨J.d.emb0 γ * n * (J.d.emb0 γ)⁻¹, GlobalTheory.MixPer.witt_anisotropic_group_normalizes_flag_unipotent D J.W J.W₀ ρ J.d n hn γ⟩
  have e' : J.d.emb0 γ * n * (J.d.emb0 γ)⁻¹ = δ.1 * m.1 := congrArg Subtype.val e
  have e2 : 1 * J.d.emb0 γ * (n * J.d.emb0 h' * h) = δ.1 * J.d.emb0 1 * (m.1 * J.d.emb0 (γ * h') * h) := by
    rw [map_mul, map_one]
    calc 1 * J.d.emb0 γ * (n * J.d.emb0 h' * h)
        = (J.d.emb0 γ * n * (J.d.emb0 γ)⁻¹) * (J.d.emb0 γ * J.d.emb0 h') * h := by group
      _ = _ := by rw [e']; group
  rw [← ker_right s hΦ h₀ (one_mem _) (one_mem _) hγ, e2, ker_right s hΦ h₀ δ.2 hδ (one_mem _)]
  have p1 := height_pos J.W₀ (γ * h')
  have p2 := height_pos J.W h
  have p3 := height_pos J.W (J.d.emb0 (γ * h'))
  have q0 := quotHeight_pos B.A h₀
  have q1 := quotHeight_pos J.W₀ h'
  have f1 : height J.W (m.1 * J.d.emb0 (γ * h') * h) ≤ |M| * (|C₃| * (2 * quotHeight J.W₀ h')) * height J.W h := by
    refine (height_mul_le _ _ _).trans (mul_le_mul_of_nonneg_right ((height_mul_le _ _ _).trans ?_) p2.le)
    exact mul_le_mul ((hM _ ⟨m, hm, rfl⟩).trans (le_abs_self _))
      ((hC₃ _).trans (mul_le_mul (le_abs_self _) e1 p1.le (abs_nonneg _))) p3.le (abs_nonneg _)
  calc _ ≤ C * quotHeight B.A h₀ ^ a * height J.W (m.1 * J.d.emb0 (γ * h') * h) ^ b := hC _ _
    _ ≤ C * quotHeight B.A h₀ ^ a * (|M| * (|C₃| * (2 * quotHeight J.W₀ h')) * height J.W h) ^ b :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (height_pos _ _).le f1 _) (by positivity)
    _ = _ := by simp only [mul_pow]; ring

def inner (φ : GA D B.A → ℂ) (Φ : WO B.V J.W → ℂ) (g : GA D J.W) : ℂ := ∫ h₀ in B.vA.𝓕, φ h₀ * ker s Φ h₀ g ∂B.vA.μ

theorem norm_mul_le_of_decay {z w : ℂ} {q C c y : ℝ} (hC : 0 ≤ C) (hy : 0 ≤ y) (hz : ‖z‖ * q ≤ c) (hw : ‖w‖ ≤ C * q * y) :
    ‖z * w‖ ≤ c * C * y := by
  calc ‖z * w‖ = ‖z‖ * ‖w‖ := norm_mul _ _
    _ ≤ ‖z‖ * (C * q * y) := mul_le_mul_of_nonneg_left hw (norm_nonneg _)
    _ = ‖z‖ * q * (C * y) := by ring
    _ ≤ c * (C * y) := mul_le_mul_of_nonneg_right hz (mul_nonneg hC hy)
    _ = _ := by ring

variable {φ : GA D B.A → ℂ} {G : GA D J.W → ℂ}

theorem inner_law (hφ : RapidDec B.A φ) (hΦ : IsThetaFunO ψ B.V J.W Φ) : Continuous (inner s φ Φ) ∧
    ∃ (C : ℝ) (b : ℕ), 0 ≤ C ∧ ∀ n ∈ flagN J.d, ∀ h' h,
      ‖inner s φ Φ (n * J.d.emb0 h' * h)‖ ≤ C * (quotHeight J.W₀ h' * height J.W h) ^ b := by
  haveI : ∀ V : HSp D, SecondCountableTopology (GA D V) := fun V => (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.1
  haveI : ∀ V : HSp D, BorelSpace (GA D V) := fun V => ⟨rfl⟩
  have hfin : B.vA.μ B.vA.𝓕 < ⊤ := GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol B.A _ _ B.vA.haar B.vA.fund
  haveI : IsFiniteMeasure (B.vA.μ.restrict B.vA.𝓕) := isFiniteMeasure_restrict.2 hfin.ne
  constructor
  · obtain ⟨C, a, b, hC0, hC⟩ := ker_le s hΦ
    obtain ⟨c, hc⟩ := hφ.decay a
    exact continuous_integral_of_le (B.vA.μ.restrict B.vA.𝓕) (T := fun g h₀ => φ h₀ * ker s Φ h₀ g)
      ((hφ.continuous.comp continuous_snd).mul (continuous_ker s hΦ)) (b := fun g => c * C * height J.W g ^ b)
      (continuous_const.mul ((continuous_height J.W).pow b))
      fun g h₀ => norm_mul_le_of_decay hC0 (pow_pos (height_pos _ _) _).le (hc h₀) (hC h₀ g)
  · obtain ⟨C, a, b, hC0, hC⟩ := ker_le_quot s hΦ
    obtain ⟨c, hc⟩ := hφ.decay a
    refine ⟨|c| * C * (B.vA.μ B.vA.𝓕).toReal, b, by positivity, fun n hn h' h => ?_⟩
    have := norm_setIntegral_le_of_norm_le_const hfin fun h₀ _ =>
      norm_mul_le_of_decay hC0 (pow_pos (mul_pos (quotHeight_pos _ h') (height_pos _ h)) b).le
        ((hc h₀).trans (le_abs_self c)) (hC h₀ n hn h' h)
    refine this.trans (le_of_eq ?_)
    simp only [Measure.real]
    ring

theorem fjAllFun_eq (hΦ : IsThetaFunO ψ B.V J.W Φ) (h : GA D J.W) (h' : GA D J.W₀) (n : flagN J.d) :
    fjAllFun ψ J.d B.o B.ζ s.om₀ B.vA.μ B.vA.𝓕 φ (rTrans h G) (flBF s (s.om (1, h) Φ)) h' n =
      G (n.1 * J.d.emb0 h' * h) * inner s φ Φ (n.1 * J.d.emb0 h' * h) := by
  rw [fjAllFun, rTrans, mul_assoc (G _), ← integral_const_mul (star _), inner]
  simp only [ker_val s hΦ _ n.2, mul_left_comm (φ _)]

theorem perAll_flBF_cont : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesL D ρ) (J : JacL D ρ) (s : StBF ψ B J), ∀ (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ) (Φ : WO B.V J.W → ℂ), RapidDec B.A φ → RapidDec J.W G → IsThetaFunO ψ B.V J.W Φ → (∀ h, AbsConv J.v0.μ J.v0.𝓕 J.vN.ν J.vN.𝓝 (fjAllFun ψ J.d B.o B.ζ s.om₀ B.vA.μ B.vA.𝓕 φ (rTrans h G) (flBF s (s.om (1, h) Φ)))) ∧ Continuous fun h => J.perAll ψ B s.om₀ φ (rTrans h G) (flBF s (s.om (1, h) Φ)) := by
  intro D ψ ρ B J s φ G Φ hφ hG hΦ
  haveI : ∀ V : HSp D, SecondCountableTopology (GA D V) := fun V => (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.1
  haveI : ∀ V : HSp D, BorelSpace (GA D V) := fun V => ⟨rfl⟩
  haveI : IsFiniteMeasure (J.v0.μ.restrict J.v0.𝓕) := isFiniteMeasure_restrict.2
    (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol J.W₀ _ _ J.v0.haar J.v0.fund).ne
  haveI : IsFiniteMeasure (J.vN.ν.restrict J.vN.𝓝) := isFiniteMeasure_restrict.2 (by rw [J.vN.unit.2.2]; exact ENNReal.one_ne_top)
  obtain ⟨hIc, C, b, hC0, hI⟩ := inner_law s hφ hΦ
  obtain ⟨C₁, a₁, h1⟩ := GlobalTheory.T.unitaryQuotientHeight_comparable_wittDecomposition D J.W J.W₀ ρ J.d
  obtain ⟨C₃, h3⟩ := (GlobalTheory.RTransDecay.rapidDec_rTrans D J.W G hG).2 (a₁ * b)
  obtain ⟨F, hF⟩ : ∃ F : GA D J.W → GA D J.W₀ × flagN J.d → ℂ,
      F = fun h p => G (p.2.1 * J.d.emb0 p.1 * h) * inner s φ Φ (p.2.1 * J.d.emb0 p.1 * h) := ⟨_, rfl⟩
  have hFe : ∀ h, Function.uncurry (fjAllFun ψ J.d B.o B.ζ s.om₀ B.vA.μ B.vA.𝓕 φ (rTrans h G) (flBF s (s.om (1, h) Φ))) = F h :=
    fun h => by subst hF; exact funext fun p => fjAllFun_eq s hΦ h p.1 p.2
  have hbound : ∀ h p, ‖F h p‖ ≤ C₃ * height J.W h ^ (a₁ * b) * (C * |C₁| ^ b) * height J.W h ^ b := by
    subst hF
    rintro h ⟨h', n⟩
    have ht := height_pos J.W h
    have qg := quotHeight_pos J.W (n.1 * J.d.emb0 h')
    refine norm_mul_le_of_decay (by positivity) (pow_pos ht b).le (h3 (n.1 * J.d.emb0 h') h) ((hI n.1 n.2 h' h).trans ?_)
    have hq : quotHeight J.W₀ h' ≤ |C₁| * quotHeight J.W (n.1 * J.d.emb0 h') ^ a₁ :=
      (h1 n.1 n.2 h').1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_pos qg _).le)
    calc _ ≤ C * (|C₁| * quotHeight J.W (n.1 * J.d.emb0 h') ^ a₁ * height J.W h) ^ b :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_pos (quotHeight_pos _ _) ht).le
            (mul_le_mul_of_nonneg_right hq ht.le) b) hC0
      _ = _ := by simp only [mul_pow, pow_mul]; ring
  have hcont : Continuous fun q : GA D J.W × (GA D J.W₀ × flagN J.d) => F q.1 q.2 := by
    subst hF
    have hg : Continuous fun q : GA D J.W × (GA D J.W₀ × flagN J.d) => (q.2.2 : GA D J.W) * J.d.emb0 q.2.1 * q.1 :=
      ((continuous_subtype_val.comp (continuous_snd.comp continuous_snd)).mul
        (J.d.continuous_embed.comp (continuous_fst.comp continuous_snd))).mul continuous_fst
    exact (hG.continuous.comp hg).mul (hIc.comp hg)
  have hint : ∀ h, AbsConv J.v0.μ J.v0.𝓕 J.vN.ν J.vN.𝓝
      (fjAllFun ψ J.d B.o B.ζ s.om₀ B.vA.μ B.vA.𝓕 φ (rTrans h G) (flBF s (s.om (1, h) Φ))) := by
    intro h
    rw [AbsConv, hFe]
    exact Integrable.of_bound (hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable _
      (.of_forall (hbound h))
  refine ⟨hint, ?_⟩
  have heq : ∀ h, J.perAll ψ B s.om₀ φ (rTrans h G) (flBF s (s.om (1, h) Φ)) =
      ∫ p, F h p ∂((J.v0.μ.restrict J.v0.𝓕).prod (J.vN.ν.restrict J.vN.𝓝)) := fun h => by
    rw [← hFe, integral_prod _ (hint h)]; rfl
  refine (continuous_congr heq).2 ?_
  exact continuous_integral_of_le _ hcont
    (((continuous_const.mul ((continuous_height J.W).pow _)).mul continuous_const).mul ((continuous_height J.W).pow b)) hbound

end GlobalTheory.BesMean

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselMeanPeriodConvergesContinuousStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselMean_period_converges_continuous : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesL D ρ) (J : JacL D ρ) (s : StBF ψ B J), ∀ (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ) (Φ : WO B.V J.W → ℂ), RapidDec B.A φ → RapidDec J.W G → IsThetaFunO ψ B.V J.W Φ → (∀ h, AbsConv J.v0.μ J.v0.𝓕 J.vN.ν J.vN.𝓝 (fjAllFun ψ J.d B.o B.ζ s.om₀ B.vA.μ B.vA.𝓕 φ (rTrans h G) (flBF s (s.om (1, h) Φ)))) ∧ Continuous fun h => J.perAll ψ B s.om₀ φ (rTrans h G) (flBF s (s.om (1, h) Φ)) := by
  first | exact @GlobalTheory.BesMean.perAll_flBF_cont | exact GlobalTheory.BesMean.perAll_flBF_cont | (intros; apply GlobalTheory.BesMean.perAll_flBF_cont <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselLevelUnfoldingCharacterAndFlatMap
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselLevelUnfoldingCharacterAndFlatMap
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.Asc.FromBes

theorem conjBessel_isTh (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (ρ : ℕ) (B : BesL D ρ) (W : HSp D)
    (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (hx₀ : gramQ W x₀ = 0) :
    IsTh ψ B.d W x₀ fun n => star (psiBes ψ B.d 1 (vecB B.o B.ζ) n) := by
  have hC := GlobalTheory.T.flag_unipotent_bessel_character_laws D ψ hψ.1 B.V B.V₀ B.A B.L ρ B.d B.o B.ζ 1
  set z := vecB B.o B.ζ with hz
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact continuous_star.comp ((hC.1 z).comp continuous_subtype_val)
  · intro γ hγ hγN n hn
    rw [psiBes_mul B.d ψ 1 z hγN hn, hC.2.1 z γ hγ, one_mul]
  · intro c n hn
    rw [psiBes_mul B.d ψ 1 z (B.d.nC_mem_NFlag c) hn, psiBes_nC, one_mul,
      GlobalTheory.Unf.CutChar.psi_qS_eq_one D ψ hψ B.V B.V₀ ρ B.d W x₀ hx₀ c, star_one, one_mul]
  · intro j a haj hai _
    obtain ⟨s, hs⟩ := GlobalTheory.Unf.CutChar.exists_psiE_ne_one D ψ hψ
    have key : ∃ v : GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.VA B.V, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form B.V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX B.d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v = 0 ∧ (∀ i k : Fin ρ, k ≤ i → GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form B.V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX B.d (Pi.single k 1)) v * GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a i = 0) ∧ ∀ u : GA D B.V, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.IsTransv B.V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX B.d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v u → (∀ i : {i : Fin ρ // i ≤ j}, u ∈ fixer B.V (B.d.jX.submatrix id fun _ : Fin 1 => i.1)) ∧ simpleSum B.d z u = s := by
      rcases lt_or_eq_of_le (Nat.succ_le_of_lt j.2) with h | h
      · exact GlobalTheory.T.exists_transvection_fixing_first_vectors_sum D B.V B.V₀ ρ B.d z j a haj hai h s
      · exact GlobalTheory.T.exists_transvection_fixing_isotropic_last_sum D B.V B.V₀ ρ B.d z (GlobalTheory.Unf.CutChar.vecB_norm_ne D B.V₀ B.A B.L B.o B.ζ B.line) j a haj hai h s
    obtain ⟨v, hv0, hvT, hv⟩ := key
    obtain ⟨u, hu⟩ := GlobalTheory.T.transvection_isUnitaryAdelic D B.V B.V₀ ρ B.d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a) v hv0
    obtain ⟨hfix, hus⟩ := hv u hu
    have huN : u ∈ Nfix B.d j :=
      ⟨GlobalTheory.T.transvection_strictUpper_mem_flagUnipotentRadical D B.V B.V₀ ρ B.d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a) v hvT u hu, Subgroup.mem_iInf.2 hfix⟩
    have hval : psiBes ψ B.d 1 z u = psiE ψ s := by
      rw [psiBes, hus, map_one, one_mul]
    refine ⟨v, u, star (psiE ψ s), hv0, hu, huN, ?_, ?_⟩
    · intro h1
      apply hs
      have := congrArg star h1
      rwa [star_star, star_one] at this
    · intro n hn n' hn'
      have huF : u ∈ flagN B.d := huN.1
      rw [psiBes_mul B.d ψ 1 z (mul_mem hn huF) hn', psiBes_mul B.d ψ 1 z hn huF, hval,
        psiBes_mul B.d ψ 1 z hn hn']
      simp only [star_mul']
      ring

theorem fl_eq_flBF (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesL D ρ) (J : JacL D ρ) (s : StBF ψ B J)
    (Ψ : WO B.V J.W → ℂ) (hΨ : IsThetaFunO ψ B.V J.W Ψ) :
    fl ψ B.d J.W s.vS s.vT s.vU (fun n => star (psiBes ψ B.d 1 (vecB B.o B.ζ) n)) (xZero J.d) Ψ = flBF s Ψ 0 := by
  have hψ : IsStdChar D ψ (-1) := s.weil.std
  have hf : ∀ x, IsThetaFunO ψ B.V₀ J.W (B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 Ψ x) := fun x =>
    (GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ hψ).1 B.V B.V₀ J.W ρ B.d s.vS.μ s.vS.𝓕 s.vS.covol Ψ hΨ x
  unfold fl flBF flatS flatAt
  congr 1
  funext u
  have hu : ∀ b, star (psiBes ψ B.d 1 (vecB B.o B.ζ) (B.d.nB b * B.d.levi u.1)) =
      star (psiUni ψ u.1) * star (psiBes ψ B.d 1 (vecB B.o B.ζ) (B.d.nB b)) := by
    intro b
    rw [psiBes_mul B.d ψ 1 _ (B.d.nB_mem_NFlag b) (B.d.levi_mem_NFlag (mem_UX.1 u.2)), psiBes_levi, star_mul',
      mul_comm]
  unfold flFun flatFun evalAt
  simp_rw [hu, mul_assoc]
  rw [integral_const_mul]
  congr 1
  congr 1
  funext b
  exact GlobalTheory.Unf.StepFour.integrand_eq hψ B.d J.d _ _ (hf _) b

theorem isTh_and_fl : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesL D ρ) (J : JacL D ρ) (s : StBF ψ B J), IsTh ψ B.d J.W J.d.e (fun n => star (psiBes ψ B.d 1 (vecB B.o B.ζ) n)) ∧ ∀ Ψ, IsThetaFunO ψ B.V J.W Ψ → fl ψ B.d J.W s.vS s.vT s.vU (fun n => star (psiBes ψ B.d 1 (vecB B.o B.ζ) n)) (xZero J.d) Ψ = flBF s Ψ 0 := by
  intro D ψ ρ B J s
  exact ⟨conjBessel_isTh D ψ s.weil.std ρ B J.W J.d.e (gramQ_e J.d), fun Ψ hΨ => fl_eq_flBF D ψ ρ B J s Ψ hΨ⟩

end GlobalTheory.Asc.FromBes

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselLevelUnfoldingCharacterAndFlatMapStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselLevel_unfolding_character_and_flatMap : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesL D ρ) (J : JacL D ρ) (s : StBF ψ B J), IsTh ψ B.d J.W J.d.e (fun n => star (psiBes ψ B.d 1 (vecB B.o B.ζ) n)) ∧ ∀ Ψ, IsThetaFunO ψ B.V J.W Ψ → fl ψ B.d J.W s.vS s.vT s.vU (fun n => star (psiBes ψ B.d 1 (vecB B.o B.ζ) n)) (xZero J.d) Ψ = flBF s Ψ 0 := by
  first | exact @GlobalTheory.Asc.FromBes.isTh_and_fl | exact GlobalTheory.Asc.FromBes.isTh_and_fl | (intros; apply GlobalTheory.Asc.FromBes.isTh_and_fl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VanishingDescendsBesselToFourierJacobi
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.Asc.VanBessel

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {ρ : ℕ} {B : BesL D ρ} {J : JacL D ρ} (s : StBF ψ B J)

theorem isTh_const_mul {V V₀ W : HSp D} {d : HypDec V V₀ ρ} {x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E} {Th : GA D V → ℂ}
    (h : IsTh ψ d W x₀ Th) (c : ℂ) : IsTh ψ d W x₀ fun n => c * Th n := by
  refine ⟨continuous_const.mul h.cont, fun γ hγ hN n hn => by rw [h.left γ hγ hN n hn],
    fun c' n hn => by rw [h.cen c' n hn]; ring, fun j a h1 h2 h3 => ?_⟩
  obtain ⟨v, u, c', e1, e2, e3, e4, e5⟩ := h.dep j a h1 h2 h3
  exact ⟨v, u, c', e1, e2, e3, e4, fun n hn n' hn' => by rw [e5 n hn n' hn']; ring⟩

theorem fl_const_mul {V V₀ W : HSp D} (d : HypDec V V₀ ρ) (v : VolM D W.rank ρ) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ)
    (Th : GA D V → ℂ) (c : ℂ) (x : Mx D W.rank ρ) (Ψ : WO V W → ℂ) :
    fl ψ d W v vb vU (fun n => c * Th n) x Ψ = c * fl ψ d W v vb vU Th x Ψ := by
  simp only [fl, flFun, mul_assoc, integral_const_mul]

def gen (φ : GA D B.A → ℂ) : Gen ψ B.V B.V₀ J.W ρ (GA D B.A) where
  d := B.d
  χV := s.χV
  χW := s.χW
  om := s.om
  vS := s.vS
  vN := B.vN
  vb := s.vT
  vU := s.vU
  vW := s.vW
  x₀ := J.d.e
  m := B.vA.μ.restrict B.vA.𝓕
  g := fun h₀ => B.o.emb (h₀, 1)
  Th := fun h₀ n => φ h₀ * star (psiBes ψ B.d 1 (vecB B.o B.ζ) n)

theorem gen_is {φ : GA D B.A → ℂ} (hφ : RapidDec B.A φ) : (gen s φ).Is := by
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D B.A
  haveI : BorelSpace (GA D B.A) := ⟨rfl⟩
  haveI := B.vA.haar
  have hTh := (GlobalTheory.T.besselLevel_unfolding_character_and_flatMap D ψ ρ B J s).1
  have hg : Continuous fun h₀ : GA D B.A => B.o.emb (h₀, 1) :=
    B.o.continuous_emb.comp (continuous_id.prodMk continuous_const)
  refine ⟨s.weil, (GlobalTheory.T.unfolding_base_point_fourierJacobi_group D J.W J.W₀ ρ J.d).1, inferInstanceAs (SFinite (B.vA.μ.restrict B.vA.𝓕)), hg,
    fun y => isTh_const_mul hTh (φ y), (hφ.2.1.comp continuous_fst).mul (hTh.cont.comp continuous_snd),
    fun y => ‖φ y‖, hφ.2.1.norm.measurable, fun y n _ => ?_, fun k => ?_⟩
  · change ‖φ y * star (psiBes ψ B.d 1 (vecB B.o B.ζ) n)‖ ≤ ‖φ y‖
    rw [norm_mul, norm_star, psiBes, psiE, s.weil.std.1.2.1, mul_one]
  · obtain ⟨C, a, hC⟩ := GlobalTheory.T.unitaryQuotientHeight_orthogonalSum_comparable D B.V₀ B.A B.L B.o
    have hq : Continuous fun y : GA D B.A => quotHeight B.V₀ (B.o.emb (y, 1)) ^ k :=
      ((continuous_quotHeight B.V₀).comp hg).pow k
    have h := hφ.integrableOn_mul_of_le B.vA.haar B.vA.fund
      (f := fun y => ((quotHeight B.V₀ (B.o.emb (y, 1)) ^ k : ℝ) : ℂ))
      (Complex.continuous_ofReal.comp hq).measurable.aestronglyMeasurable (C := C ^ k) (A := a * k) fun y => by
        rw [Complex.norm_real, Real.norm_of_nonneg (pow_pos (quotHeight_pos _ _) k).le, pow_mul, ← mul_pow]
        exact pow_le_pow_left₀ (quotHeight_pos _ _).le (hC y).2 k
    refine (Integrable.norm h).congr (Filter.Eventually.of_forall fun y => ?_)
    change ‖((quotHeight B.V₀ (B.o.emb (y, 1)) ^ k : ℝ) : ℂ) * φ y‖ = ‖φ y‖ * quotHeight B.V₀ (B.o.emb (y, 1)) ^ k
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (pow_pos (quotHeight_pos _ _) k).le, mul_comm]

theorem gen_lhs (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ) (Φ : WO B.V J.W → ℂ) :
    (gen s φ).lhs G Φ = B.per ψ φ (s.lift G Φ) := by
  simp only [Gen.lhs, BesL.per, besPer, besFun]
  refine congrArg _ (funext fun h₀ => congrArg _ (funext fun n => ?_))
  change φ h₀ * star (psiBes ψ B.d 1 (vecB B.o B.ζ) n.1) * s.lift G Φ (n.1 * embA B.d B.o h₀) = _
  ring

theorem gen_ker (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ) {Φ : WO B.V J.W → ℂ} (hΦ : IsThetaFunO ψ B.V J.W Φ) :
    (gen s φ).ker G Φ = fun h => G h * ∫ h₀ in B.vA.𝓕, φ h₀ * flBF s (s.om (embA B.d B.o h₀, h) Φ) 0 ∂B.vA.μ := by
  funext h
  refine congrArg (G h * ·) (congrArg _ (funext fun h₀ => ?_))
  change fl ψ B.d J.W s.vS s.vT s.vU (fun n => φ h₀ * star (psiBes ψ B.d 1 (vecB B.o B.ζ) n)) (xZero J.d)
    (s.om (embA B.d B.o h₀, h) Φ) = _
  rw [fl_const_mul, (GlobalTheory.T.besselLevel_unfolding_character_and_flatMap D ψ ρ B J s).2 _ (s.weil.om_pres _ _ hΦ)]

theorem flBF_theta {Ψ : WO B.V J.W → ℂ} (hΨ : IsThetaFunO ψ B.V J.W Ψ) : IsThetaFunO ψ B.V₀ J.W₀ (flBF s Ψ) :=
  (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D ψ s.weil.std B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s.vS s.vT s.vU J.d.e
    (GlobalTheory.T.unfolding_base_point_fourierJacobi_group D J.W J.W₀ ρ J.d).1.1 _ Ψ hΨ).2

theorem flBF_rat {Ψ : WO B.V J.W → ℂ} (hΨ : IsThetaFunO ψ B.V J.W Ψ) {γ : GA D J.W}
    (hγ : γ ∈ GQ J.W ⊓ jacGrp J.d) : flBF s (s.om (1, γ) Ψ) 0 = flBF s Ψ 0 := by
  obtain ⟨n, hn, h', rfl⟩ := (GlobalTheory.MixPer.Decomp.mem_jacGrp_iff J.d).1 hγ.2
  obtain ⟨hnQ, hh'⟩ := ((GlobalTheory.T.unfolding_base_point_fourierJacobi_group D J.W J.W₀ ρ J.d).2.2.2.2.2 n hn h').1 hγ.1
  have hψ := s.weil.std.1
  have hΞ := flBF_theta s hΨ
  have hy : yZero B.V₀ ρ (vecB B.o B.ζ) ∈ ratMx D B.V₀.rank ρ := neg_mem (GlobalTheory.UnfKer.zEll_rat _ _ _)
  rw [← map_one (embA B.d B.o), GlobalTheory.T.besselToJacobiFlatMap_equivariant D ψ ρ B J s Ψ hΨ 1 n hn h', psiFlag_eq,
    GlobalTheory.CharLaws.psiBes_rat ψ J.d hψ.2.2.1 1 0 hnQ,
    star_one, one_smul, Prod.mk_one_one, map_one, Prod.mk_one_one, map_one, Module.End.one_apply, opA,
    GlobalTheory.UnfKer.jacT_rat hψ J.d B.V₀ hy hnQ (s.weil₀.om_pres _ _ hΞ), s.weil₀.om_aut 1 (one_mem _) h' hh' _ hΞ]

theorem om_om (g g' : GA D B.V) (h h' : GA D J.W) (Φ : WO B.V J.W → ℂ) :
    s.om (g * g', h * h') Φ = s.om (g, h) (s.om (g', h') Φ) := by
  rw [← Module.End.mul_apply, ← map_mul s.om, Prod.mk_mul_mk]

end GlobalTheory.Asc.VanBessel

namespace GlobalTheory.Asc


open VanBessel in
theorem vanBF : ∀ D : D7, VanBF D := by
  intro D ψ ρ B J s 𝒮 Γ₀ K hL φ G hφ hG hGK hvan Φ hΦ𝒮
  have hΦ := hL.theta Φ hΦ𝒮
  obtain ⟨hb, -, hx, hR, hemb, hrat⟩ := GlobalTheory.T.unfolding_base_point_fourierJacobi_group D J.W J.W₀ ρ J.d
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D B.A
  obtain ⟨j1, j2, j3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D J.W
  haveI : BorelSpace (GA D B.A) := ⟨rfl⟩
  haveI : BorelSpace (GA D J.W) := ⟨rfl⟩
  haveI := B.vA.haar
  haveI := s.vW.haar
  have ha := gen_is s hφ
  obtain ⟨-, -, hfd⟩ := GlobalTheory.T.rational_unitary_subgroup_countable_discrete_fundDomain D J.W (GQ J.W ⊓ jacGrp J.d) inf_le_left
  obtain ⟨𝓑, h𝓑⟩ := hfd s.vW.μ s.vW.haar
  have h𝓑' := h𝓑
  rw [← hR] at h𝓑'
  have hint := (GlobalTheory.T.thetaLift_unfolding_integrated_over_family D ψ B.V B.V₀ J.W ρ (GA D B.A) (gen s φ) ha G Φ hG hΦ 𝓑 h𝓑').2.1
  have hcut := GlobalTheory.T.integral_strip_eq_zero_of_real_modulation_vanishing D ψ B.V B.V₀ J.W ρ (GA D B.A) (gen s φ) ha G hG Φ hΦ (fun c hc => by
    rw [gen_lhs]
    refine hvan _ (hL.real Φ hΦ𝒮 _ ?_)
    change (c ⬝ B.d.pY).map (finPart D) = 0
    have hm : (c ⬝ B.d.pY).map (finPart D) = c.map (finPart D) * (B.d.pY).map (finPart D) := Matrix.map_mul
    rw [hm, hc, Matrix.zero_mul]) 𝓑 h𝓑'
  rw [gen_ker s φ G hΦ] at hint hcut
  set f : GA D J.W → ℂ := fun h => G h * ∫ h₀ in B.vA.𝓕, φ h₀ * flBF s (s.om (embA B.d B.o h₀, h) Φ) 0 ∂B.vA.μ with hf

  have hm : Measurable f := by
    have hc := GlobalTheory.T.continuous_flatMap_weilRepresentation_joint D ψ B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s.vS s.vT s.χV s.χW s.om s.weil s.vU J.d.e hb.1 Φ hΦ
    have he : Continuous (embA B.d B.o) :=
      B.d.continuous_embed.comp (B.o.continuous_emb.comp (continuous_id.prodMk continuous_const))
    have hq : Continuous fun p : GA D J.W × GA D B.A =>
        (((embA B.d B.o p.2, p.1), yZero B.V₀ ρ (vecB B.o B.ζ), 0) :
          (GA D B.V × GA D J.W) × Mx D B.V₀.rank ρ × WO B.V₀ J.W₀) :=
      ((he.comp continuous_snd).prodMk continuous_fst).prodMk continuous_const
    have hF : Continuous fun p : GA D J.W × GA D B.A => flBF s (s.om (embA B.d B.o p.2, p.1) Φ) 0 := by
      refine (hc.comp hq).congr fun p => ?_
      rw [Function.comp_apply, ← hx]
      rfl
    have hK : Continuous fun p : GA D J.W × GA D B.A => φ p.2 * flBF s (s.om (embA B.d B.o p.2, p.1) Φ) 0 :=
      (hφ.2.1.comp continuous_snd).mul hF
    exact hG.2.1.measurable.mul
      (hK.measurable.stronglyMeasurable.integral_prod_right' (ν := B.vA.μ.restrict B.vA.𝓕)).measurable

  have hinv : ∀ γ ∈ GQ J.W ⊓ jacGrp J.d, ∀ g, f (γ * g) = f g := fun γ hγ g => by
    simp only [hf]
    rw [hG.1 γ hγ.1]
    refine congrArg (G g * ·) (congrArg _ (funext fun h₀ => ?_))
    rw [← one_mul (embA B.d B.o h₀), om_om, flBF_rat s (s.weil.om_pres _ _ hΦ) hγ, one_mul]

  have hval : ∀ h h' (n : flagN J.d), f (n.1 * J.d.emb0 h' * h) =
      fjAllFun ψ J.d B.o B.ζ s.om₀ B.vA.μ B.vA.𝓕 φ (rTrans h G) (flBF s (s.om (1, h) Φ)) h' n := fun h h' n => by
    simp only [hf]
    rw [fjAllFun, rTrans, mul_assoc (G _), ← integral_const_mul (star _)]
    refine congrArg (G _ * ·) (congrArg _ (funext fun h₀ => ?_))
    rw [← mul_one (embA B.d B.o h₀), om_om,
      GlobalTheory.T.besselToJacobiFlatMap_equivariant D ψ ρ B J s _ (s.weil.om_pres _ _ hΦ) h₀ n.1 n.2 h', Pi.smul_apply, smul_eq_mul, fjKer]
    ring

  obtain ⟨-, -, -, -, hconj, hinj, -⟩ := GlobalTheory.MixPer.flag_jacobi_structure D J.W J.W₀ ρ J.d
  have hclN := (GlobalTheory.T.flag_subgroups_closed_normal_cocompact' D J.W J.W₀ ρ J.d).1
  let Z : HSp D := {
    V := Fin 0 → D.host.E
    hT := 0
    herm := ⟨fun _ _ => by simp⟩
    nondeg := ⟨fun x _ => Subsingleton.elim x 0, fun x _ => Subsingleton.elim x 0⟩
    rank := 0
    rank_eq := by simp
    frame := Pi.basisFun D.host.E (Fin 0)
    sig := fun _ => (0, 0)
    L0 := ⊥
    standardTuple_isLattice := by
      refine ⟨?_, ?_⟩
      · exact Submodule.fg_bot
      · intro t _ ht
        have : t = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun x hx =>
          ht.ne_zero hx (Subsingleton.elim x 0)
        subst t
        exact linearIndepOn_empty _ _
    baseLattice_isUnimodular := Subsingleton.elim _ _ }
  let o : OrthDec J.W₀ J.W₀ Z := {
    iA := 1
    iB := 0
    isoA := by simp
    isoB := by ext i; exact Fin.elim0 (show Fin 0 from i)
    orth := by ext i; exact Fin.elim0 (show Fin 0 from i)
    rank_add := rfl }
  obtain ⟨⟨hRcl, hRhaar⟩, -⟩ := GlobalTheory.T.fourierJacobi_bessel_groups_closed_haar_product D J.W J.W₀ J.W₀ Z ρ J.d o
    J.vN.ν J.vN.𝓝 J.vN.unit
  obtain ⟨hνh, h𝓝, -⟩ := J.vN.unit
  have hμR : (semiMeas (flagN J.d) J.d.emb0 J.v0.μ J.vN.ν).IsHaarMeasure := hRhaar J.v0.μ J.v0.haar
  obtain ⟨𝓡, h𝓡, hsem⟩ := GlobalTheory.T.semidirect_haar_measure_fundamental_domain D J.W J.W₀ (flagN J.d) J.d.emb0 hemb hclN hconj hinj hrat J.v0 J.vN.ν J.vN.𝓝
    hνh h𝓝 hμR
  obtain ⟨hsplit, hunim, -⟩ := ((GlobalTheory.T.unitaryAdelic_inf_fin_split_periods_unimodular D J.W).2.2.2.2.2 J.W₀ ρ J.d).1
  obtain ⟨habs, hTc⟩ := GlobalTheory.T.besselMean_period_converges_continuous D ψ ρ B J s φ G Φ hφ hG hΦ
  have hmeas : ∀ h, Measurable fun g => f (g * h) := fun h => hm.comp (measurable_mul_const h)
  have habs' : ∀ h, AbsConv J.v0.μ J.v0.𝓕 J.vN.ν J.vN.𝓝 fun h' n => f (n.1 * J.d.emb0 h' * h) := fun h => by
    simp only [hval]
    exact habs h
  have hfun : ∀ h, ∫ r in 𝓡, f ((r : GA D J.W) * h) ∂(semiMeas (flagN J.d) J.d.emb0 J.v0.μ J.vN.ν) =
      J.perAll ψ B s.om₀ φ (rTrans h G) (flBF s (s.om (1, h) Φ)) := fun h => by
    refine ((hsem (fun g => f (g * h)) (hmeas h)).2 (habs' h)).trans ?_
    simp only [JacL.perAll, fjAll, hval]
  have key := GlobalTheory.T.continuousMean_vanishing_on_strips_at_one D J.W s.vW (jacGrp J.d) K hRcl hsplit hL.fin hL.cpt hL.opn _ hμR (hunim _ hμR) 𝓡 𝓑 h𝓡 h𝓑 f hm hinv
    hint (fun h => ((hsem (fun g => f (g * h)) (hmeas h)).1).2 (habs' h)) (hTc.congr fun h => (hfun h).symm)
    (fun k hk g => by
      simp only [hf]
      rw [hGK k hk]
      refine congrArg (G g * ·) (congrArg _ (funext fun h₀ => ?_))
      rw [← mul_one (embA B.d B.o h₀), om_om, hL.fix Φ hΦ𝒮 k hk, mul_one])
    (fun h hh => by
      rw [← hR, ← hx]
      refine hL.supp Φ hΦ𝒮 h fun h0 => hh ?_
      have h0' : flBF s (s.om (1, h) Φ) = 0 := h0
      have := hval h 1 1
      rw [map_one, OneMemClass.coe_one, one_mul, one_mul] at this
      rw [this, h0']
      simp only [fjAllFun, fjKer, opA, OneMemClass.coe_one, jacT_one, map_zero, id, Pi.zero_apply, mul_zero, integral_zero])
    (fun C hC hCi => by
      rw [← hR]
      exact ⟨(GlobalTheory.T.adelicStripSet_measurable_read_on_realPart D J.W ρ J.d.e hb C hC hCi).1, hcut C hC hCi⟩)
  have h1 := hfun 1
  simp only [mul_one] at h1
  rw [show rTrans 1 G = G from funext fun h => congrArg G (mul_one h), Prod.mk_one_one, map_one, Module.End.one_apply] at h1
  exact h1.symm.trans key

end GlobalTheory.Asc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VanishingDescendsBesselToFourierJacobiStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vanishing_descends_bessel_to_fourierJacobi : ∀ D : D7, VanBF D := by
  first | exact @GlobalTheory.Asc.vanBF | exact GlobalTheory.Asc.vanBF | (intros; apply GlobalTheory.Asc.vanBF <;> assumption)
end
