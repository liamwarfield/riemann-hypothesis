module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportRationalPointsStabiliserFrame
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuBLGapPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.STiesR
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairVrGramPRatPosDef

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeterssonCoefficientBoundedSphericalUnramified
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeterssonCoefficientBoundedSphericalUnramified
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Core.Rk.SphCoef

variable {D : D7}

theorem mem_l2_add {A : HSp D} {m : Measure (GA D A)} {φ ψ : GA D A → ℂ} (h : MemL2Quotient (GQ A) m φ)
    (h' : MemL2Quotient (GQ A) m ψ) : MemL2Quotient (GQ A) m (φ + ψ) :=
  ⟨fun γ hγ g => by simp only [Pi.add_apply, h.1 γ hγ g, h'.1 γ hγ g], h.2.add h'.2⟩

theorem mem_l2_smul {A : HSp D} {m : Measure (GA D A)} {φ : GA D A → ℂ} (c : ℂ) (h : MemL2Quotient (GQ A) m φ) :
    MemL2Quotient (GQ A) m (c • φ) :=
  ⟨fun γ hγ g => by simp only [Pi.smul_apply, h.1 γ hγ g], h.2.const_smul c⟩

theorem mem_l2_zero {A : HSp D} {m : Measure (GA D A)} : MemL2Quotient (GQ A) m (0 : GA D A → ℂ) :=
  ⟨fun _ _ _ => rfl, MemLp.zero⟩

theorem isSphCoef_rcoef : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfFam D) (A : HSp D) (cA : CptF A) (L : Lat A), IsInfFam θ → ∀ (m : Measure (GA D A)), m.IsHaarMeasure → ∀ (Sf : Finset (FinPl D)), ∀ u₁ ∈ A0 θ A cA, ∀ u₂ ∈ A0 θ A cA, ∀ par : GlobalTheory.LFun.Fam D.host.E, GlobalTheory.LFun.IsParamFun D.sp.cm.sig A.gram L (Sf : Set (FinPl D)) u₁ par → SphFun A L Sf u₂ → ∀ v ∉ Sf, ∀ x : GA D A, proj D.sp.cm.sig A.gram v x = 1 → IsSphCoef A L v par fun y => rcoef m u₁ u₂ (x * emb D.sp.cm.sig A.gram v y) := by
  intro hP D θ A cA L hθ m hm Sf u₁ hu₁ u₂ hu₂ par hpar hsph v hv x hx
  have : m.IsMulRightInvariant := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D A m hm
  have h1 : MemL2Quotient (GQ A) m u₁ := memL2_of_cusp_form hP hθ (mem_cuspForms.1 hu₁).1
  have h2 : MemL2Quotient (GQ A) m u₂ := memL2_of_cusp_form hP hθ (mem_cuspForms.1 hu₂).1
  have hR : ∀ g, MemL2Quotient (GQ A) m (rTr A g u₁) := fun g => h1.mul_right g
  let p : Submodule ℂ (GA D A → ℂ) :=
    { carrier := {F | MemL2Quotient (GQ A) m (rTr A x F)}
      zero_mem' := mem_l2_zero
      add_mem' := fun ha hb => mem_l2_add ha hb
      smul_mem' := fun c _ hF => mem_l2_smul c hF }
  let ℓ₀ : p →ₗ[ℂ] ℂ :=
    { toFun := fun F => petersson A m (rTr A x F) u₂
      map_add' := fun F G => petersson_add_left F.2 G.2 h2
      map_smul' := fun c F => petersson_smul_left c _ _ }
  obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend ℓ₀
  let ρ : Representation ℂ (Gv A v) (GA D A → ℂ) :=
    (GlobalTheory.PRep.rightReg ℂ (GA D A) ℂ).comp (emb D.sp.cm.sig A.gram v)
  have hρ : ∀ y g, ρ y u₁ g = u₁ (g * emb D.sp.cm.sig A.gram v y) := fun _ _ => rfl
  have htr : ∀ y, rTr A x (ρ y u₁) = rTr A (x * emb D.sp.cm.sig A.gram v y) u₁ := fun y => funext fun g => by
    simp only [rTr, hρ, mul_assoc]
  have hmem : ∀ y, ρ y u₁ ∈ p := fun y => by
    show MemL2Quotient _ _ (rTr A x (ρ y u₁))
    rw [htr]; exact hR _
  have hval : ∀ y, ℓ (ρ y u₁) = petersson A m (rTr A (x * emb D.sp.cm.sig A.gram v y) u₁) u₂ := fun y => by
    have e := LinearMap.congr_fun hℓ ⟨_, hmem y⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at e
    rw [e, ← htr]; rfl
  have hnorm : ∀ g, ‖(hR g).toL2‖ = ‖h1.toL2‖ := fun g => by
    have e1 := (hR g).inner_toL2_eq_theta_pairing (hR g)
    have e2 := h1.inner_toL2_eq_theta_pairing h1
    have e3 : pet (GQ A) m (rTr A g u₁) (rTr A g u₁) = pet (GQ A) m u₁ u₁ := by
      have := petersson_rTr (μ := m) h1 h1 g
      exact this
    rw [e3, ← e2, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at e1
    have e4 : ‖(hR g).toL2‖ ^ 2 = ‖h1.toL2‖ ^ 2 := by exact_mod_cast e1
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 e4
  refine ⟨⟨‖h2.toL2‖ * ‖h1.toL2‖, fun y => ?_⟩, GA D A → ℂ, inferInstance, inferInstance, ρ, u₁, ℓ,
    fun w h => hpar v (by simpa using hv) w h, fun k hk y => ?_, fun y => (hval y).symm⟩
  · show ‖petersson A m (rTr A (x * emb D.sp.cm.sig A.gram v y) u₁) u₂‖ ≤ _
    rw [petersson, ← (hR _).inner_toL2_eq_theta_pairing h2, ← hnorm (x * emb D.sp.cm.sig A.gram v y)]
    exact norm_inner_le_norm _ _
  · rw [hval, hval, map_mul]
    have hc : emb D.sp.cm.sig A.gram v k * x = x * emb D.sp.cm.sig A.gram v k :=
      (GlobalTheory.AdelicU.commute_emb (σ := D.sp.cm.sig) (J := A.gram) k hx).eq
    have e1 : rTr A (x * (emb D.sp.cm.sig A.gram v k * emb D.sp.cm.sig A.gram v y)) u₁ =
        rTr A (emb D.sp.cm.sig A.gram v k) (rTr A (x * emb D.sp.cm.sig A.gram v y) u₁) := funext fun g => by
      simp only [rTr]
      rw [← mul_assoc x, ← hc]
      simp only [mul_assoc]
    have e2 : u₂ = rTr A (emb D.sp.cm.sig A.gram v k) u₂ := funext fun g => (hsph v hv k hk g).symm
    rw [e1]
    conv_lhs => rw [e2]
    exact petersson_rTr (hR _) h2 _

end GlobalTheory.Core.Rk.SphCoef

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeterssonCoefficientBoundedSphericalUnramifiedStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.petersson_coefficient_bounded_spherical_unramified : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfFam D) (A : HSp D) (cA : CptF A) (L : Lat A), IsInfFam θ → ∀ (m : Measure (GA D A)), m.IsHaarMeasure → ∀ (Sf : Finset (FinPl D)), ∀ u₁ ∈ A0 θ A cA, ∀ u₂ ∈ A0 θ A cA, ∀ par : GlobalTheory.LFun.Fam D.host.E, GlobalTheory.LFun.IsParamFun D.sp.cm.sig A.gram L (Sf : Set (FinPl D)) u₁ par → SphFun A L Sf u₂ → ∀ v ∉ Sf, ∀ x : GA D A, proj D.sp.cm.sig A.gram v x = 1 → IsSphCoef A L v par fun y => rcoef m u₁ u₂ (x * emb D.sp.cm.sig A.gram v y) := by
  first | exact @GlobalTheory.Core.Rk.SphCoef.isSphCoef_rcoef | exact GlobalTheory.Core.Rk.SphCoef.isSphCoef_rcoef | (intros; apply GlobalTheory.Core.Rk.SphCoef.isSphCoef_rcoef <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatFamilyZetaConvergenceHolomorphyStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatFamilyZetaConvergenceHolomorphy
open MeasureTheory Set

namespace GlobalTheory.FlatFamily

open GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral

variable {X : Type} [MeasurableSpace X]


omit [MeasurableSpace X] in
theorem flatIntegrand_rebase (f : X → ℂ) {a : X → ℝ} (ha : ∀ x, 0 < a x) (s₀ s₁ s : ℂ) (x : X) :
    flatIntegrand f a s₀ s x = flatIntegrand f a s₀ s₁ x * ((a x : ℝ) : ℂ) ^ (s - s₁) := by
  have h : ((a x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ha x).ne'
  simp only [flatIntegrand]
  rw [mul_assoc, ← Complex.cpow_add _ _ h]
  congr 2
  ring


omit [MeasurableSpace X] in
theorem norm_flatIntegrand_le (f : X → ℂ) {a : X → ℝ} (ha : ∀ x, 0 < a x) (ha1 : ∀ x, a x ≤ 1)
    (s₀ : ℂ) {s₁ s : ℂ} (hs : s₁.re ≤ s.re) (x : X) :
    ‖flatIntegrand f a s₀ s x‖ ≤ ‖flatIntegrand f a s₀ s₁ x‖ := by
  letI : MeasurableSpace X := ⊥
  rw [norm_flatIntegrand f s₀ s (ha x), norm_flatIntegrand f s₀ s₁ (ha x)]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge (ha x) (ha1 x) (by linarith)) (norm_nonneg _)

theorem aestronglyMeasurable_flatIntegrand {μ : Measure X} {f : X → ℂ} {a : X → ℝ}
    (hm : Measurable a) (ha : ∀ x, 0 < a x) {s₀ s₁ : ℂ}
    (h : AEStronglyMeasurable (flatIntegrand f a s₀ s₁) μ) (s : ℂ) :
    AEStronglyMeasurable (flatIntegrand f a s₀ s) μ := by
  have e : flatIntegrand f a s₀ s
      = fun x => flatIntegrand f a s₀ s₁ x * ((a x : ℝ) : ℂ) ^ (s - s₁) :=
    funext (flatIntegrand_rebase f ha s₀ s₁ s)
  rw [e]
  refine h.mul ?_
  exact ((Complex.measurable_ofReal.comp hm).pow_const (s - s₁)).aestronglyMeasurable

omit [MeasurableSpace X] in
theorem hasDerivAt_flatIntegrand (f : X → ℂ) {a : X → ℝ} (ha : ∀ x, 0 < a x) (s₀ s : ℂ) (x : X) :
    HasDerivAt (fun z => flatIntegrand f a s₀ z x)
      (flatIntegrand f a s₀ s x * ((Real.log (a x) : ℝ) : ℂ)) s := by
  have h : ((a x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ha x).ne'
  have h1 := (((hasDerivAt_id s).sub_const s₀).const_cpow (c := ((a x : ℝ) : ℂ))
    (Or.inl h)).const_mul (f x)
  simp only [flatIntegrand]
  refine h1.congr_deriv ?_
  rw [Complex.ofReal_log (ha x).le]
  simp only [id, mul_one]
  ring

theorem flatZetaHolomorphic : FlatZetaHolomorphic := by
  intro X _ μ f a s₀ s₁ hm ha ha1 hint
  have hmeas := aestronglyMeasurable_flatIntegrand hm ha hint.aestronglyMeasurable
  have hI : ∀ s : ℂ, s₁.re ≤ s.re → Integrable (flatIntegrand f a s₀ s) μ := fun s hs =>
    hint.norm.mono' (hmeas s) (Filter.Eventually.of_forall (norm_flatIntegrand_le f ha ha1 s₀ hs))
  refine ⟨⟨hI, fun s _ => ⟨_, self_mem_nhdsWithin, _, hint.norm,
    fun s' hs' x => norm_flatIntegrand_le f ha ha1 s₀ hs' x⟩⟩, ?_, ?_⟩
  · intro s hs
    have hs' : s₁.re < s.re := hs
    set ε : ℝ := (s.re - s₁.re) / 2 with hε
    have hεpos : 0 < ε := by rw [hε]; linarith
    have hU : {z : ℂ | s₁.re + ε < z.re} ∈ nhds s :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by
        change s₁.re + ε < s.re
        rw [hε]; linarith)
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
      (F := fun z x => flatIntegrand f a s₀ z x)
      (F' := fun z x => flatIntegrand f a s₀ z x * ((Real.log (a x) : ℝ) : ℂ))
      (x₀ := s) (bound := fun x => ‖flatIntegrand f a s₀ s₁ x‖ * (1 / ε)) hU
      (Filter.Eventually.of_forall hmeas) (hI s hs'.le)
      ((hmeas s).mul
        (Complex.measurable_ofReal.comp (Real.measurable_log.comp hm)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x z hz => by
        have hz' : s₁.re + ε < z.re := hz
        rw [flatIntegrand_rebase f ha s₀ s₁ z x, mul_assoc, norm_mul]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (ha x), Complex.norm_real,
          Real.norm_eq_abs, Complex.sub_re]
        have h1 : a x ^ (z.re - s₁.re) ≤ a x ^ ε :=
          Real.rpow_le_rpow_of_exponent_ge (ha x) (ha1 x) (by linarith)
        have h2 := Real.abs_log_mul_self_rpow_lt (a x) ε (ha x) (ha1 x) hεpos
        rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (ha x) ε), mul_comm] at h2
        exact (mul_le_mul_of_nonneg_right h1 (abs_nonneg _)).trans h2.le)
      (hint.norm.mul_const _)
      (Filter.Eventually.of_forall fun x z _ => hasDerivAt_flatIntegrand f ha s₀ z x)
    exact key.2.differentiableAt.differentiableWithinAt
  · exact continuousOn_of_dominated (bound := fun x => ‖flatIntegrand f a s₀ s₁ x‖)
      (fun s _ => hmeas s)
      (fun s hs => Filter.Eventually.of_forall (norm_flatIntegrand_le f ha ha1 s₀ hs))
      hint.norm
      (Filter.Eventually.of_forall fun x z _ =>
        (hasDerivAt_flatIntegrand f ha s₀ z x).continuousAt.continuousWithinAt)

end GlobalTheory.FlatFamily
end

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatFamilyZeta_convergence_holomorphy : GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral.FlatZetaHolomorphic := by
  first | exact @GlobalTheory.FlatFamily.flatZetaHolomorphic | exact GlobalTheory.FlatFamily.flatZetaHolomorphic | (intros; apply GlobalTheory.FlatFamily.flatZetaHolomorphic <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RtrMemOfNorm
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MiTop.CenIsom

variable {D : D7} {X : HidaSetting D} {u : D.what₂.Word}

theorem rtr_mem_of_norm (hK : X.LevelSubgroupCharacter) {δ : Hfin X u}
    (hn : ∀ κ : Ku X u hK, ∃ κ' : Ku X u hK, (κ : Hfin X u) * δ = δ * κ' ∧
      ((psiK X u hK κ' : ℂˣ) : ℂ) = ((psiK X u hK κ : ℂˣ) : ℂ))
    {T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)} (hT : T ∈ Cu X u hK) : rtr X δ T ∈ Cu X u hK := by
  obtain ⟨h1, h2⟩ := hT
  refine ⟨fun ξ => ⟨fun γ y => ?_, fun y κ => ?_⟩, fun g ξ y => ?_⟩
  · show T ξ ((_, _) * y * (1, δ)) = T ξ (y * (1, δ))
    rw [mul_assoc]
    exact (h1 ξ).1 γ _
  · obtain ⟨κ', hκ', hψ⟩ := hn κ
    have hc : ((1 : Hinf X u), (κ : Hfin X u)) * (1, δ) = (1, δ) * (1, (κ' : Hfin X u)) :=
      Prod.ext rfl hκ'
    have e : y * (1, (κ : Hfin X u)) * (1, δ) = y * (1, δ) * (1, (κ' : Hfin X u)) := by
      rw [mul_assoc, mul_assoc, hc]
    refine (congrArg (T ξ) e).trans (((h1 ξ).2 _ κ').trans ?_)
    rw [hψ]
    rfl
  · have hc : ((g : Hinf X u), (1 : Hfin X u)) * (1, δ) = (1, δ) * (g, 1) :=
      Prod.ext ((mul_one g).trans (one_mul g).symm) ((one_mul δ).trans (mul_one δ).symm)
    have e : y * (g, 1) * (1, δ) = y * (1, δ) * (g, 1) := by
      rw [mul_assoc, mul_assoc, hc]
    exact (h2 g ξ (y * (1, δ))).trans (congrArg (T ξ) e.symm)

theorem rtr_comm {δ δ' : Hfin X u} (h : δ * δ' = δ' * δ) (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) :
    rtr X δ' (rtr X δ T) = rtr X δ (rtr X δ' T) := by
  ext ξ y
  have hc : ((1 : Hinf X u), δ') * (1, δ) = (1, δ) * (1, δ') := Prod.ext rfl h.symm
  have e : y * (1, δ') * (1, δ) = y * (1, δ) * (1, δ') := by rw [mul_assoc, mul_assoc, hc]
  exact congrArg (T ξ) e


set_option maxHeartbeats 3000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem exists_rtr_dia {F : Formalism.L2.Forms.Forms0 D u} (Tr : Transport X u F) (hK : X.LevelSubgroupCharacter) (hL : LevelMatch X Tr hK)
    (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) :
    ∃ δ : Hfin X u, ∀ T ∈ Cu X u hK, rtr X δ T ∈ Cu X u hK ∧
      dictA X Tr (rtr X δ T) = (D.mem u).A.rhoT v a (dictA X Tr T) := by
  have hW : WittX X u Tr.wt := ⟨Tr.wt_isom, Tr.wt_e, Tr.wt_f, Tr.weight_z⟩
  have hA : IsAdeleIso X Tr.ιA := ⟨Tr.ιA_rat, Tr.ιA_int⟩
  have hσ := GlobalTheory.St.G.IotaSigmaCompatibility.iotaA_sigA D X Tr.ιA hA
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.frame_action_mulEquiv D X u Tr.wt Tr.ιA hW hA hσ
  obtain ⟨-, hΓ, hsT⟩ := GlobalTheory.transport_rational_points D X u Tr.wt Tr.ιA hW hA Φ hΦ
  obtain ⟨hψ, -, hφ, -, -⟩ := cols_sharp_dictionary D X u hK
  obtain ⟨k, hk, hkT⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.unit_lift_int_prime_field (D.mem u).A.T_prime ((D.mem u).A.card_Fv v) a
  obtain ⟨e, he, hee, hσe⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.splitAtT_of_tied F.atT v
  obtain ⟨y, hy⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.is_diamond_of_local_diamond F.cls0.lev (F.atT.eV v).1 (F.atT.eV v).2 k
    (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.local_diamond_of_split_idempotent F.cls0.lev _ _ (D.mem u).A.T_prime k hkT e he hee hσe)
  have hlev := fun h => hL.2 h (Φ h) ((hΦ h (Φ h)).2 rfl)
  obtain ⟨δ, hδ⟩ : ∃ δ : Hfin X u, Φ δ = Tr.h0 * y * Tr.h0⁻¹ := Φ.surjective _
  refine ⟨δ, fun T hT => ⟨rtr_mem_of_norm hK (fun κ => ?_) hT, ?_⟩⟩
  · have hκ := (hlev κ).1.1 κ.2
    have hm := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.diamond_conj_mem_level F.cls0.lev _ _ hy ⟨_, hκ⟩
    have hχ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.level_character_conj_diamond F.cls0.lev _ _ (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.level_places_not_bad F.atT v) hy ⟨_, hκ⟩
    have e1 : Tr.h0⁻¹ * Φ (δ⁻¹ * κ * δ) * Tr.h0 = y⁻¹ * (Tr.h0⁻¹ * Φ κ * Tr.h0) * y := by
      rw [map_mul, map_mul, map_inv, hδ]
      group
    have e2 := congrArg Subtype.val e1
    have hm' : (Tr.h0⁻¹ * Φ (δ⁻¹ * κ * δ) * Tr.h0).1 ∈ F.cls0.lev.U := by
      rw [e2]
      exact hm
    have hin := (hlev (δ⁻¹ * κ * δ)).1.2 hm'
    refine ⟨⟨δ⁻¹ * κ * δ, hin⟩, by simp only [← mul_assoc, mul_inv_cancel, one_mul], ?_⟩
    rw [(hlev _).2 hin hm', (hlev κ).2 κ.2 hκ, ← hχ]
    exact congrArg (fun x => ((F.cls0.lev.chi x : ℂˣ) : ℂ)) (Subtype.ext e2)
  · have key := GlobalTheory.adForms_of_equivariant D.host.F D.host.E (Formalism.L2.Forms.sigD D) (D.R.N 0)
      (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) _ _ _ F.cls0.lev (Gam X u) (Hinf X u) (Hfin X u)
      (iotaI X u) (iotaF X u) (Ku X u hK) (psiK X u hK) Φ Tr.h0 D.what₂.Tau (Formalism.L2.Forms.embT D)
      ((D.fm u).lam 0) (X.Vpi u) (piRep X u) Tr.J hψ
      (fun h => (hlev h).1) (fun h hk hy => (hlev h).2 hk hy) hΓ
      (fun γ g hγ ξ y y' hy => Tr.J_eqv _ (iotaI X u γ).2 ξ y y' (by rw [hsT γ g hγ]; exact hy))
      (fun ξ => by rw [← Formalism.L2.Forms.lamT_zero]; exact Tr.J_val ξ)
      (shP X u T) (hφ ⟨T, hT⟩)
    have hc : ∀ c, Φ (Tr.hc c) = F.cls0.y c * Tr.h0⁻¹ := fun c => (hΦ (Tr.hc c) _).1 (Tr.hc_rep c)
    have e1 : dictA X Tr T = fun c s =>
        (fun x => Tr.J (shP X u T (Φ.symm (x * Tr.h0⁻¹)))) (F.cls0.y c) (F.val0.eY s) := by
      funext c s
      show Tr.J (shP X u T (Tr.hc c)) (F.val0.eY s) = Tr.J (shP X u T (Φ.symm (F.cls0.y c * Tr.h0⁻¹))) (F.val0.eY s)
      rw [← hc, MulEquiv.symm_apply_apply]
    rw [e1, Formalism.L2.Forms.rhoT_eq F.val0 v a k hk y hy _ key.1]
    funext c s
    have e2 : Tr.hc c * δ = Φ.symm (F.cls0.y c * y * Tr.h0⁻¹) := by
      apply Φ.injective
      rw [map_mul, MulEquiv.apply_symm_apply, hc, hδ]
      group
    show Tr.J (shP X u (rtr X δ T) (Tr.hc c)) (F.val0.eY s) =
      Tr.J (shP X u T (Φ.symm (F.cls0.y c * y * Tr.h0⁻¹))) (F.val0.eY s)
    rw [Formalism.L2.SG.Pf.ColDictPf.rieszVector_rightTranslate, e2]

theorem ram_rtr {F : Formalism.L2.Forms.Forms0 D u} (Tr : Transport X u F) (hK : X.LevelSubgroupCharacter) (hL : LevelMatch X Tr hK)
    (hI : ColDictInto X Tr hK) (hB : ColDictBij X Tr hK) (δ : Hfin X u) (hδ : ∀ k : Hfin X u, δ * k = k * δ)
    (T S : Cu X u hK) (hS : S.1 = rtr X δ T.1) (hT : colDictL X Tr hK T ∈ (D.mem u).A.Mram) :
    colDictL X Tr hK S ∈ (D.mem u).A.Mram := by
  refine ⟨hI S, (Submodule.mem_iInf _).2 fun v => ?_⟩
  have h0 : (D.mem u).A.Nm v (dictA X Tr T.1) = 0 := (Submodule.mem_iInf _).1 hT.2 v
  choose d hd using exists_rtr_dia Tr hK hL v
  have hsum : ∀ P ∈ Cu X u hK, (D.mem u).A.Nm v (dictA X Tr P) = dictA X Tr (∑ a, rtr X (d a) P) := by
    intro P hP
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Formalism.BasicNotions.ColumnsAtT.Nm, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun a _ => (hd a P hP).2.symm
  have hmem : ∑ a, rtr X (d a) T.1 ∈ Cu X u hK := Submodule.sum_mem _ fun a _ => (hd a T.1 T.2).1
  have hz : (⟨_, hmem⟩ : Cu X u hK) = 0 :=
    hB.1 (((hsum T.1 T.2).symm.trans h0).trans (map_zero (colDictL X Tr hK)).symm)
  have hz' : ∑ a, rtr X (d a) T.1 = 0 := congrArg Subtype.val hz
  have e : ∑ a, rtr X (d a) S.1 = rtr X δ (∑ a, rtr X (d a) T.1) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, hS]
    exact Finset.sum_congr rfl fun a _ => rtr_comm (hδ (d a)) T.1
  show (D.mem u).A.Nm v (dictA X Tr S.1) = 0
  rw [hsum S.1 S.2, e, hz', map_zero, map_zero]

theorem sum_inner_rieszVector_rightTranslate (hK : X.LevelSubgroupCharacter) {ι : Type} [Fintype ι] (s : ι → Hfin X u)
    (hs : ∀ h, ∃! i, ∃ (γ : Gam X u) (κ : Ku X u hK), h = iotaF X u γ * s i * (κ : Hfin X u))
    (δ : Hfin X u) (hδ : ∀ k : Hfin X u, δ * k = k * δ) (T T' : Cu X u hK) :
    ∑ i, ⟪shP X u (rtr X δ T'.1) (s i), shP X u (rtr X δ T.1) (s i)⟫_ℂ =
      ∑ i, ⟪shP X u T'.1 (s i), shP X u T.1 (s i)⟫_ℂ := by
  simp only [Formalism.L2.SG.Pf.ColDictPf.rieszVector_rightTranslate]
  refine Formalism.L2.SG.Pf.ColDictPf.sum_reps X u (fun i => s i * δ) s (Ku X u hK) (fun h => ?_) hs
    (fun h => ⟪shP X u T'.1 h, shP X u T.1 h⟫_ℂ)
    (fun γ h κ => Formalism.L2.SG.Pf.ColDictPf.inner_shP_rat X u hK T T' γ h κ)
  have e : ∀ (i : ι) (γ : Gam X u) (κ : Ku X u hK), h * δ⁻¹ = iotaF X u γ * s i * (κ : Hfin X u) ↔
      h = iotaF X u γ * (s i * δ) * (κ : Hfin X u) := by
    intro i γ κ
    rw [mul_inv_eq_iff_eq_mul, mul_assoc _ (κ : Hfin X u) δ, ← hδ κ]
    simp only [mul_assoc]
  simpa only [e] using hs (h * δ⁻¹)

open Formalism.MainNotions Formalism.L2 Formalism.L2.DIV

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {R : Formalism.L2.RecT ex}


end GlobalTheory.MiTop.CenIsom

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainHeckeParamAddSmulOfAgreeOffSet
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainHeckeParamAddSmulOfAgreeOffSet
noncomputable section

namespace GlobalTheory.LFun.ParLin

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.SatCompare
open Formalism.MainNotions.SchurIrreducible (IsSplit)

section GLcase
variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} {x x' : V}
  {B : Multiset ℂˣ}

theorem satGL_add (hx : IsSatVecGL w ρ x B) (hx' : IsSatVecGL w ρ x' B) (h0 : x + x' ≠ 0) :
    IsSatVecGL w ρ (x + x') B :=
  ⟨h0, add_mem hx.2.1 hx'.2.1, hx.2.2.1, fun ϖ hϖ j hj => by
    have e := (heckeLin (Final.GLintComm E w n) (Tj_mem_hecke hϖ j) ρ).map_add x x'
    simp only [heckeLin_apply] at e
    rw [e, hx.2.2.2 ϖ hϖ j hj, hx'.2.2.2 ϖ hϖ j hj, smul_add]⟩

theorem satGL_smul (hx : IsSatVecGL w ρ x B) {a : ℂ} (ha : a ≠ 0) : IsSatVecGL w ρ (a • x) B :=
  ⟨smul_ne_zero ha hx.1, Submodule.smul_mem _ a hx.2.1, hx.2.2.1, fun ϖ hϖ j hj => by
    rw [GlobalTheory.LFun.SatCompare.heckeVec_smul (Final.GLintComm E w n) (Tj_mem_hecke hϖ j), hx.2.2.2 ϖ hϖ j hj, smul_comm]⟩

end GLcase

section Ucase
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {c : L →+* L} {n : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V] {ϖ : L} {q : ℕ} {ρ : Representation ℂ (GU c n) V} {x x' : V}
  {α : Fin (n / 2) → ℂˣ}

theorem satU_add (hU : IsUnramInv ϖ c q) (hx : IsSatVecU ϖ q ρ x α) (hx' : IsSatVecU ϖ q ρ x' α) (h0 : x + x' ≠ 0) :
    IsSatVecU ϖ q ρ (x + x') α :=
  ⟨h0, add_mem hx.2.1 hx'.2.1, fun t ht => by
    have e := (heckeLin (P.isCommensurated_integral_unitary_of_unramified hU n) ht ρ).map_add x x'
    simp only [heckeLin_apply] at e
    rw [e, hx.2.2 t ht, hx'.2.2 t ht, smul_add]⟩

theorem satU_smul (hU : IsUnramInv ϖ c q) (hx : IsSatVecU ϖ q ρ x α) {a : ℂ} (ha : a ≠ 0) :
    IsSatVecU ϖ q ρ (a • x) α :=
  ⟨smul_ne_zero ha hx.1, Submodule.smul_mem _ a hx.2.1, fun t ht => by
    rw [GlobalTheory.LFun.SatCompare.heckeVec_smul (P.isCommensurated_integral_unitary_of_unramified hU n) ht, hx.2.2 t ht, smul_comm]⟩

end Ucase

section Vec
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} {h : w.under (𝓞 F) = v}
  {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GLoc σ J v) V} {x x' : V} {B : Multiset ℂˣ}

theorem paramVec_smul (hx : IsParamVec σ J L h ρ x B) {a : ℂ} (ha : a ≠ 0) : IsParamVec σ J L h ρ (a • x) B := by
  rcases hx with ⟨hv, e, he, hx⟩ | ⟨hw, c, ϖ, e, α, hU, he, hx, hB⟩
  · exact Or.inl ⟨hv, e, he, satGL_smul hx ha⟩
  · exact Or.inr ⟨hw, c, ϖ, e, α, hU, he, satU_smul hU hx ha, hB⟩

theorem paramVec_add (hx : IsParamVec σ J L h ρ x B) (hx' : IsParamVec σ J L h ρ x' B) (h0 : x + x' ≠ 0) :
    IsParamVec σ J L h ρ (x + x') B := by
  rcases hx with ⟨hv, e, he, hx⟩ | ⟨hw, c, ϖ, e, α, hU, he, hx, hB⟩
  · exact Or.inl ⟨hv, e, he, satGL_add hx (hx'.isSatVecGL hv he) h0⟩
  · rcases hx' with ⟨hv, -⟩ | ⟨-, c', ϖ', e', α', hU', he', hx', hB'⟩
    · exact absurd hv (not_isSplit_of_isInertAt hw)
    · obtain rfl : c' = c := (InertChart.existsUnique_isConjAt σ hw h).unique he'.1 he.1
      have h1 := IsSatVecU.of_unif hU' hU (IsSatVecU.of_chart he' he hx')
      have h2 : IsSatVecU ϖ (qV F v) (ρ.comp e.symm.toMonoidHom) x' α := ⟨h1.1, h1.2.1, fun t ht => by
        rw [h1.2.2 t ht, GlobalTheory.T.unitarySatakeTransform_eq_of_baseChangeSatakeParameter_eq (w.adicCompletion E) ϖ c' (qV F v) n hU α' α (hB'.symm.trans hB) t ht]⟩
      exact Or.inr ⟨hw, c', ϖ, e, α, hU, he, satU_add hU hx h2 h0, hB⟩

end Vec

end GlobalTheory.LFun.ParLin

noncomputable section

namespace GlobalTheory.LFun.ParLin

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun

section Fun
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
  {S : Set (HeightOneSpectrum (𝓞 F))} {V : Type} [AddCommGroup V] [Module ℂ V] {f f' : GAd σ J → V} {B B' : Fam E}

theorem paramFun_of_agree (hf : IsParamFun σ J L S f B') (hB : ∀ w ∉ above E S, B w = B' w) :
    IsParamFun σ J L S f B := fun v hv w h => by
  have hw : w ∉ above E S := fun hm => hv (h ▸ hm)
  rw [hB w hw]
  exact hf v hv w h

theorem paramFun_add (hf : IsParamFun σ J L S f B) (hf' : IsParamFun σ J L S f' B) (h0 : f + f' ≠ 0) :
    IsParamFun σ J L S (f + f') B := fun v hv w h => paramVec_add (hf v hv w h) (hf' v hv w h) h0

theorem paramFun_smul (hf : IsParamFun σ J L S f B) {a : ℂ} (ha : a ≠ 0) : IsParamFun σ J L S (a • f) B :=
  fun v hv w h => paramVec_smul (hf v hv w h) ha

end Fun

end GlobalTheory.LFun.ParLin

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate

namespace GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LFun.ParLin in
theorem isPar_add_smul : ∀ (D : D7) (c : Com D) (s : PiLocalization₂ D), (∀ (u u' : s.CC c) B B' (a : ℂ), IsPar u B → IsPar u' B' →
    (∀ w ∉ (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))), B w = B' w) →
    u + a • u' ≠ 0 → IsPar (u + a • u') B) ∧ ∀ (u : s.CC c) B (a : ℂ), IsPar u B → a ≠ 0 → IsPar (a • u) B := by
  intro D c s
  have cne : ∀ f : GA D s.V → ℂ, f ≠ 0 → (fun g => conj (f g)) ≠ 0 := fun f hf h0 =>
    hf (funext fun g => by simpa using congrFun h0 g)
  refine ⟨fun u u' B B' a hu hu' hB h0 => ⟨h0, fun v hv => ?_⟩, fun u B a hu ha => ⟨smul_ne_zero ha hu.1, fun v hv => ?_⟩⟩
  · have hval : PiLocalization₂.val (u + a • u') v = PiLocalization₂.val u v + a • PiLocalization₂.val u' v := by simp [PiLocalization₂.val]
    have hc : (fun g => conj (PiLocalization₂.val (u + a • u') v g)) =
        (fun g => conj (PiLocalization₂.val u v g)) + (conj a) • (fun g => conj (PiLocalization₂.val u' v g)) := by
      funext g; simp [hval]
    unfold ParFun
    rw [hc]
    by_cases h1 : PiLocalization₂.val u v = 0
    · have h2 : a • PiLocalization₂.val u' v ≠ 0 := by rw [hval, h1, zero_add] at hv; exact hv
      have ha : a ≠ 0 := fun e => h2 (by simp [e])
      have hu'v : PiLocalization₂.val u' v ≠ 0 := fun e => h2 (by simp [e])
      have hz : (fun g => conj (PiLocalization₂.val u v g)) = 0 := by funext g; simp [h1]
      rw [hz, zero_add]
      exact paramFun_smul (paramFun_of_agree (hu'.2 v hu'v) hB) (by simpa using ha)
    · by_cases h2 : a • PiLocalization₂.val u' v = 0
      · have hz : (conj a) • (fun g => conj (PiLocalization₂.val u' v g)) = 0 := by
          funext g
          have := congrFun h2 g
          simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
          rw [← map_mul, this, map_zero]
        rw [hz, add_zero]
        exact hu.2 v h1
      · have ha : a ≠ 0 := fun e => h2 (by simp [e])
        have hu'v : PiLocalization₂.val u' v ≠ 0 := fun e => h2 (by simp [e])
        refine paramFun_add (hu.2 v h1) (paramFun_smul (paramFun_of_agree (hu'.2 v hu'v) hB) (by simpa using ha)) ?_
        rw [← hc]
        exact cne _ hv
  · have hval : PiLocalization₂.val (a • u) v = a • PiLocalization₂.val u v := by simp [PiLocalization₂.val]
    have hu0 : PiLocalization₂.val u v ≠ 0 := fun e => hv (by rw [hval, e, smul_zero])
    have hc : (fun g => conj (PiLocalization₂.val (a • u) v g)) = (conj a) • (fun g => conj (PiLocalization₂.val u v g)) := by
      funext g; simp [hval]
    unfold ParFun
    rw [hc]
    exact paramFun_smul (hu.2 v hu0) (by simpa using ha)

end GlobalTheory.ChainOnto
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainHeckeParamAddSmulOfAgreeOffSetStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChainHeckeParam_add_smul_of_agree_off_set : ∀ (D : D7) (c : Com D) (s : PiLocalization₂ D), (∀ (u u' : s.CC c) B B' (a : ℂ), IsPar u B → IsPar u' B' → (∀ w ∉ (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))), B w = B' w) → u + a • u' ≠ 0 → IsPar (u + a • u') B) ∧ ∀ (u : s.CC c) B (a : ℂ), IsPar u B → a ≠ 0 → IsPar (a • u) B := by
  first | exact @GlobalTheory.ChainOnto.isPar_add_smul | exact GlobalTheory.ChainOnto.isPar_add_smul | (intros; apply GlobalTheory.ChainOnto.isPar_add_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesDatumInvLeftMulTargetLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesDatumInvLeftMulTargetLevel
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.LevelMove

section Mat

variable {κ : Type} [CommRing κ] {a b r t j : ℕ}

def IsTopB (r t : ℕ) (y : Matrix (Fin b) (Fin a) κ) (g : GL (Fin a) κ) : Prop :=
  LowZero a y ∧ g.val = topL a y ∧ g ∈ blockTri (blkOf r t)

theorem IsTopB.move (hab : a ≤ b) (ea : a = r + j * t) (eb : b = r + (j + 1) * t)
    {y : Matrix (Fin b) (Fin a) κ} {g : GL (Fin a) κ} {H : GL (Fin b) κ} (h : IsTopB r t y g)
    (hT : H ∈ blockTri (blkOf r t)) :
    IsTopB r t ((H⁻¹).val * y) ((upperLeftBlock hab H)⁻¹ * g) := by
  obtain ⟨h1, h2, h3⟩ := h
  have t2 := GlobalTheory.StepLaw.TypeDatum.mem_twoBlockTriangular_of_blockTriangular ea eb hT
  have tm := GlobalTheory.StepLaw.TypeDatum.top_mem hab t2 hT
  have hinv : upperLeftBlock hab H⁻¹ = (upperLeftBlock hab H)⁻¹ := extendOne_inv _ t2
  have e1 := GlobalTheory.StepLaw.TypeDatum.topL_mul hab (Subgroup.inv_mem _ t2) h1 1
  have e2 := GlobalTheory.StepLaw.TypeDatum.lowZero_mul (Subgroup.inv_mem _ t2) h1 1
  rw [Matrix.mul_one] at e1 e2
  rw [Matrix.mul_one] at e1
  refine ⟨e2, ?_, Subgroup.mul_mem _ (Subgroup.inv_mem _ tm) h3⟩
  rw [e1, hinv, ← h2, Units.val_mul]

theorem restrictBlock_inv_mul_block_triangular_move (hab : a ≤ b) (ha : r ≤ a) (hb : r ≤ b) (ea : a = r + j * t) (eb : b = r + (j + 1) * t)
    {g : GL (Fin a) κ} {H : GL (Fin b) κ} (hg : g ∈ blockTri (blkOf r t)) (hT : H ∈ blockTri (blkOf r t)) :
    upperLeftBlock ha ((upperLeftBlock hab H)⁻¹ * g) = (upperLeftBlock hb H)⁻¹ * upperLeftBlock ha g := by
  have t2 := GlobalTheory.StepLaw.TypeDatum.mem_twoBlockTriangular_of_blockTriangular ea eb hT
  have tm := GlobalTheory.StepLaw.TypeDatum.top_mem hab t2 hT
  have le := blockTri_blkOf_le (κ := κ) (n := a) r t
  have m2 : upperLeftBlock ha ((upperLeftBlock hab H)⁻¹ * g) = upperLeftBlock ha (upperLeftBlock hab H)⁻¹ * upperLeftBlock ha g :=
    extendMatrixByIdentityAlongIndices_mul _ (le (Subgroup.inv_mem _ tm)) (le hg)
  have m3 : upperLeftBlock ha (upperLeftBlock hab H)⁻¹ = (upperLeftBlock ha (upperLeftBlock hab H))⁻¹ := extendOne_inv _ (le tm)
  rw [m2, m3, GlobalTheory.StepLaw.TypeDatum.restrictTopBlock_restrictTopBlock hab ha hb t2 hT]

theorem char_move (hab : a ≤ b) (ea : a = r + j * t) (eb : b = r + (j + 1) * t) {A : Type} [CommGroup A]
    (χ : ℕ → κˣ →* A) {g : GL (Fin a) κ} {H : GL (Fin b) κ} (hg : g ∈ blockTri (blkOf r t))
    (hT : H ∈ blockTri (blkOf r t)) :
    (∏ c ∈ Finset.range j, χ (c + 1) (dBlk (blkOf r t) (c + 1) ((upperLeftBlock hab H)⁻¹ * g))) *
        (χ (j + 1) (Matrix.GeneralLinearGroup.det ((upperLeftBlock hab H)⁻¹ * g)))⁻¹ =
      (∏ c ∈ Finset.range (j + 1), χ (c + 1) (dBlk (blkOf r t) (c + 1) H))⁻¹ *
        χ (j + 1) (Matrix.GeneralLinearGroup.det H) *
        ((∏ c ∈ Finset.range j, χ (c + 1) (dBlk (blkOf r t) (c + 1) g)) *
          (χ (j + 1) (Matrix.GeneralLinearGroup.det g))⁻¹) := by
  have h := GlobalTheory.StepLaw.TypeDatum.char_law hab ea eb χ hg (Subgroup.one_mem _) hT
  have d1 : ∀ c, dBlk (blkOf r t) c (1 : GL (Fin a) κ) = 1 := fun c => blockDiagonalExtendByOnePrimeField_one _ _
  simp only [mul_one, d1, map_one, Finset.prod_const_one, one_mul] at h
  rw [inv_mul_eq_iff_eq_mul] at h
  rw [h]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end Mat

section Dat

variable {D : D7} {a b r t k : ℕ} (ha : r ≤ a) (Pg : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ)
  (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ χj : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
  (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP))

theorem omegaG_of_top (g : ∀ PP : ↥Pg, GL (Fin a) (kP PP.1)) (hg : ∀ PP : ↥Pg, IsTopB r t (y PP.1) (g PP))
    (hm : (fun PP : ↥Pg => upperLeftBlock ha (g PP)) ∈ P.H) :
    omegaG (Lev.datY a r t k ha Pg ∅ P χ ξ Lev.Frm.B) χj y =
      ((P.chi ⟨_, hm⟩ * ∏ PP : ↥Pg, ((∏ c ∈ Finset.range k, χ (c + 1) PP.1 (dBlk (blkOf r t) (c + 1) (g PP))) *
        (χj PP.1 (Matrix.GeneralLinearGroup.det (g PP)))⁻¹) : ℂˣ) : ℂ) := by
  unfold omegaG
  split_ifs with h
  · have e : h.2.choose = g := funext fun PP =>
      Units.ext ((h.2.choose_spec.1 PP).trans (hg PP).2.1.symm)
    have e2 : (Lev.datY a r t k ha Pg ∅ P χ ξ Lev.Frm.B).P.chi
        ⟨fun PP => upperLeftBlock (Lev.datY a r t k ha Pg ∅ P χ ξ Lev.Frm.B).hr (h.2.choose PP), h.2.choose_spec.2.2⟩ =
        P.chi ⟨_, hm⟩ := by
      show P.chi _ = P.chi _
      congr 1
      exact Subtype.ext (funext fun PP => congrArg (fun x => upperLeftBlock ha x) (congrFun e PP))
    rw [e2]
    simp only [e, Finset.prod_mul_distrib, Units.val_mul, Units.coe_prod, Units.val_inv_eq_inv_val, mul_assoc]
    rfl
  · exfalso
    exact h ⟨fun PP hP => (hg ⟨PP, hP⟩).1, g, fun PP => (hg PP).2.1, fun PP => (hg PP).2.2, hm⟩

theorem omegaG_of_notTop (hg : ¬ ∃ g : ∀ PP : ↥Pg, GL (Fin a) (kP PP.1), (∀ PP : ↥Pg, IsTopB r t (y PP.1) (g PP)) ∧
      (fun PP : ↥Pg => upperLeftBlock ha (g PP)) ∈ P.H) :
    omegaG (Lev.datY a r t k ha Pg ∅ P χ ξ Lev.Frm.B) χj y = 0 := by
  unfold omegaG
  split_ifs with h
  · exfalso
    obtain ⟨h1, g, g1, g2, g3⟩ := h
    exact hg ⟨g, fun PP => ⟨h1 PP.1 PP.2, g1 PP, g2 PP⟩, g3⟩
  · rfl

end Dat

end GlobalTheory.ChainOnto.LevelMove

namespace GlobalTheory.ChainOnto

open LevelMove

theorem omegaG_levelP_move : ∀ (D : D7) (a b r t k : ℕ) (ha : r ≤ a) (hb : r ≤ b), a = r + k * t → b = r + (k + 1) * t → ∀ (Pg : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (H : ∀ PP : Pl D.host.E, GL (Fin b) (kP PP)), (∀ PP ∈ Pg, H PP ∈ blockTri (blkOf r t)) → ∀ hP : (fun PP : ↥Pg => upperLeftBlock hb (H PP.1)) ∈ P.H, ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP), omegaG (Lev.datY a r t k ha Pg ∅ P χ ξ Lev.Frm.B) (χ (k + 1)) (fun PP => ((H PP)⁻¹).val * y PP) = (((P.chi ⟨_, hP⟩ * ∏ PP ∈ Pg, ∏ i ∈ Finset.range (k + 1), χ (i + 1) PP (dBlk (blkOf r t) (i + 1) (H PP)))⁻¹ * ∏ PP ∈ Pg, χ (k + 1) PP (Matrix.GeneralLinearGroup.det (H PP)) : ℂˣ) : ℂ) * omegaG (Lev.datY a r t k ha Pg ∅ P χ ξ Lev.Frm.B) (χ (k + 1)) y := by
  intro D a b r t k ha hb ea eb Pg P χ ξ H hH hP y
  have hab : a ≤ b := by rw [ea, eb, add_mul]; omega
  by_cases h : ∃ g : ∀ PP : ↥Pg, GL (Fin a) (kP PP.1), (∀ PP : ↥Pg, IsTopB r t (y PP.1) (g PP)) ∧
      (fun PP : ↥Pg => upperLeftBlock ha (g PP)) ∈ P.H
  · obtain ⟨g, hg, hm⟩ := h
    have hg' : ∀ PP : ↥Pg, IsTopB r t (((H PP.1)⁻¹).val * y PP.1) ((upperLeftBlock hab (H PP.1))⁻¹ * g PP) :=
      fun PP => (hg PP).move hab ea eb (hH _ PP.2)
    have hr : (fun PP : ↥Pg => upperLeftBlock ha ((upperLeftBlock hab (H PP.1))⁻¹ * g PP)) =
        (fun PP : ↥Pg => upperLeftBlock hb (H PP.1))⁻¹ * (fun PP : ↥Pg => upperLeftBlock ha (g PP)) :=
      funext fun PP => restrictBlock_inv_mul_block_triangular_move hab ha hb ea eb (hg PP).2.2 (hH _ PP.2)
    have hm' : (fun PP : ↥Pg => upperLeftBlock ha ((upperLeftBlock hab (H PP.1))⁻¹ * g PP)) ∈ P.H := by
      rw [hr]; exact P.H.mul_mem (P.H.inv_mem hP) hm
    have hc : P.chi ⟨_, hm'⟩ = (P.chi ⟨_, hP⟩)⁻¹ * P.chi ⟨_, hm⟩ := by
      rw [← map_inv, ← map_mul]; congr 1; exact Subtype.ext hr
    have hx : ∀ PP : ↥Pg, (∏ c ∈ Finset.range k, χ (c + 1) PP.1 (dBlk (blkOf r t) (c + 1) ((upperLeftBlock hab (H PP.1))⁻¹ * g PP))) *
        (χ (k + 1) PP.1 (Matrix.GeneralLinearGroup.det ((upperLeftBlock hab (H PP.1))⁻¹ * g PP)))⁻¹ =
        (∏ c ∈ Finset.range (k + 1), χ (c + 1) PP.1 (dBlk (blkOf r t) (c + 1) (H PP.1)))⁻¹ *
          χ (k + 1) PP.1 (Matrix.GeneralLinearGroup.det (H PP.1)) *
          ((∏ c ∈ Finset.range k, χ (c + 1) PP.1 (dBlk (blkOf r t) (c + 1) (g PP))) *
            (χ (k + 1) PP.1 (Matrix.GeneralLinearGroup.det (g PP)))⁻¹) :=
      fun PP => char_move hab ea eb (fun c => χ c PP.1) (hg PP).2.2 (hH _ PP.2)
    rw [omegaG_of_top ha Pg P χ ξ _ (fun PP => ((H PP)⁻¹).val * y PP) _ hg' hm', omegaG_of_top ha Pg P χ ξ _ y g hg hm,
      hc, ← Units.val_mul]
    congr 1
    rw [Finset.prod_congr rfl fun PP _ => hx PP, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_inv_distrib,
      ← Finset.prod_coe_sort Pg (fun PP => χ (k + 1) PP (Matrix.GeneralLinearGroup.det (H PP))),
      ← Finset.prod_coe_sort Pg (fun PP => ∏ i ∈ Finset.range (k + 1), χ (i + 1) PP (dBlk (blkOf r t) (i + 1) (H PP)))]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have h' : ¬ ∃ g : ∀ PP : ↥Pg, GL (Fin a) (kP PP.1),
        (∀ PP : ↥Pg, IsTopB r t ((fun PP => ((H PP)⁻¹).val * y PP) PP.1) (g PP)) ∧ (fun PP : ↥Pg => upperLeftBlock ha (g PP)) ∈ P.H := by
      rintro ⟨g, hg, hm⟩
      refine h ⟨fun PP => (upperLeftBlock hab (H PP.1)⁻¹)⁻¹ * g PP, fun PP => ?_, ?_⟩
      · have e : y PP.1 = ((H PP.1)⁻¹⁻¹).val * (((H PP.1)⁻¹).val * y PP.1) := by
          rw [← Matrix.mul_assoc, ← Units.val_mul, inv_inv, mul_inv_cancel, Units.val_one, Matrix.one_mul]
        rw [e]
        exact (hg PP).move hab ea eb (Subgroup.inv_mem _ (hH _ PP.2))
      · have hr : (fun PP : ↥Pg => upperLeftBlock ha ((upperLeftBlock hab (H PP.1)⁻¹)⁻¹ * g PP)) =
            (fun PP : ↥Pg => upperLeftBlock hb (H PP.1)⁻¹)⁻¹ * (fun PP : ↥Pg => upperLeftBlock ha (g PP)) :=
          funext fun PP => restrictBlock_inv_mul_block_triangular_move hab ha hb ea eb (hg PP).2.2 (Subgroup.inv_mem _ (hH _ PP.2))
        have i2 : (fun PP : ↥Pg => upperLeftBlock hb (H PP.1)⁻¹) = (fun PP : ↥Pg => upperLeftBlock hb (H PP.1))⁻¹ :=
          funext fun PP => extendOne_inv _ (blockTri_blkOf_le r t (hH _ PP.2))
        rw [hr, i2, inv_inv]
        exact P.H.mul_mem hP hm
    rw [omegaG_of_notTop ha Pg P χ ξ _ y h, omegaG_of_notTop ha Pg P χ ξ _ _ h', mul_zero]

end GlobalTheory.ChainOnto

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesDatumInvLeftMulTargetLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelPlacesDatum_inv_left_mul_target_level : ∀ (D : D7) (a b r t k : ℕ) (ha : r ≤ a) (hb : r ≤ b), a = r + k * t → b = r + (k + 1) * t → ∀ (Pg : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (H : ∀ PP : Pl D.host.E, GL (Fin b) (kP PP)), (∀ PP ∈ Pg, H PP ∈ blockTri (blkOf r t)) → ∀ hP : (fun PP : ↥Pg => upperLeftBlock hb (H PP.1)) ∈ P.H, ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP), omegaG (Lev.datY a r t k ha Pg ∅ P χ ξ Lev.Frm.B) (χ (k + 1)) (fun PP => ((H PP)⁻¹).val * y PP) = (((P.chi ⟨_, hP⟩ * ∏ PP ∈ Pg, ∏ i ∈ Finset.range (k + 1), χ (i + 1) PP (dBlk (blkOf r t) (i + 1) (H PP)))⁻¹ * ∏ PP ∈ Pg, χ (k + 1) PP (Matrix.GeneralLinearGroup.det (H PP)) : ℂˣ) : ℂ) * omegaG (Lev.datY a r t k ha Pg ∅ P χ ξ Lev.Frm.B) (χ (k + 1)) y := by
  first | exact @GlobalTheory.ChainOnto.omegaG_levelP_move | exact GlobalTheory.ChainOnto.omegaG_levelP_move | (intros; apply GlobalTheory.ChainOnto.omegaG_levelP_move <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NuRowZeroLeThreeMul
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.CoreHt.RowsRange

variable {D : D7}

theorem one_le_scL (L : SizeData₂ D) : 1 ≤ L.sc.L :=
  Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le

theorem one_le_b (L : SizeData₂ D) : 1 ≤ L.sc.b :=
  Real.one_le_exp (by linarith [one_le_scL L])

theorem b'_pos (L : SizeData₂ D) : 0 < L.sc.b' := by
  have := L.sc.one_lt_alt
  have := one_le_b L
  unfold Scale.b' Scale.a Scale.X'
  positivity

theorem one_le_n (D : D7) : (1 : ℝ) ≤ D.R.n := by
  have : 1 ≤ D.R.n := by
    have := D.R.two_le_m
    have := D.R.m_le_f
    unfold Ranks.n
    omega
  exact_mod_cast this

theorem exists_top {τ : D.what₂.Tau} (h : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces) :
    ∃ t : D.host.TT, (D.eTau τ : D.R.GG) = D.R.tau1 t := by
  unfold Host.topPlaces at h
  obtain ⟨t, ht, hte⟩ := Finset.mem_image.1 h
  exact ⟨⟨t, ht⟩, hte.symm⟩

theorem nuRow_zero_le_three_mul (large₂ : SizeData₂ D) (P : ParameterChoice' D large₂) (hb : ∀ t, (large₂.bT t : ℝ) ≤ 2 * large₂.sc.b')
    (hT : ThickUp large₂) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) :
    DV.nuRow D u (i + 1) τ 0 ≤ 3 * large₂.sc.a := by
  have hm := D.R.two_le_m
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hk0 : 0 < D.R.k := by omega
  have hk' : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk
  have hm' : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hkN : (D.R.k : ℝ) ≤ D.R.N i := by
    have : D.R.k ≤ D.R.N i := by unfold Ranks.N; omega
    exact_mod_cast this
  have hx := large₂.sc.one_lt_alt
  have hb1 := one_le_b large₂
  have hb' := b'_pos large₂
  have hba : large₂.sc.b ≤ large₂.sc.a := le_mul_of_one_le_left (by linarith) hx.le
  have hX : 2 ≤ large₂.sc.X' := by
    have h1 : 1 ≤ large₂.sc.x ^ (large₂.sc.eps / 3) := Real.one_le_rpow hx.le (by linarith [large₂.sc.eps_pos])
    have h2 := Real.add_one_le_exp (large₂.sc.x ^ (large₂.sc.eps / 3))
    unfold Scale.X'
    linarith
  have hb'a : large₂.sc.b' ≤ large₂.sc.a / 2 := div_le_div_of_nonneg_left (by linarith) (by norm_num) hX
  have hw : large₂.sc.w'' D.R.n ≤ large₂.sc.b' :=
    div_le_self hb'.le (one_le_mul_of_one_le_of_one_le hx.le (one_le_n D))
  have he := large₂.etaSz_pos
  have hS := large₂.Sc_pos
  have heta : 2 * large₂.etaSz ≤ large₂.sc.b' := by
    have h1 : (2 : ℝ) ≤ D.R.m * ((D.R.t : ℝ) + 1) := by nlinarith
    linarith [P.mteta, mul_le_mul_of_nonneg_right h1 he.le]
  have hSc : 5 * large₂.Sc ≤ large₂.sc.b' := by
    linarith [P.kS_le, mul_le_mul_of_nonneg_right hk' hS.le]
  have hwj : wj D (i + 1) τ = (((D.hc τ).e ⟨i, hi⟩ : ℚ) : ℝ) := by
    unfold wj
    rw [dite_eq_left (by simpa using hi)]
    rfl
  rw [RowWeightLemmas.nuRow_head D u i hi τ 0 hk0, D.hcW_first u τ hk0, D.hcW_e]
  push_cast
  rw [← hwj]
  by_cases ha : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
  · obtain ⟨t, htt⟩ := exists_top ha
    rw [(large₂.top_u τ t hk0 htt).1]
    have a1 := (large₂.win_top (i + 1) (by omega) hi τ t htt).2
    have a2 := (large₂.aT_win t).2
    have a3 : (5 : ℝ) ≤ (D.R.k : ℝ) * large₂.sc.x ^ (Scale.A / 2) :=
      hk'.trans (le_mul_of_one_le_right (by linarith) (Real.one_le_rpow hx.le (by unfold Scale.A; norm_num)))
    have a4 : large₂.sc.a / ((D.R.k : ℝ) * large₂.sc.x ^ (Scale.A / 2)) ≤ large₂.sc.a / 5 :=
      div_le_div_of_nonneg_left (by linarith) (by norm_num) a3
    have a5 : large₂.sc.b' / large₂.sc.x ≤ large₂.sc.b' := div_le_self hb'.le hx.le
    linarith [hb t]
  · have h1 := P.cloud_place_bound τ (by omega) ha
    have h2 := (large₂.cloud_v τ ⟨0, by omega⟩).2
    push_cast at h1
    by_cases hc : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
    · have a1 := hT (i + 1) (by omega) hi τ hc
      linarith
    · have a1 := (large₂.win_thin (i + 1) (by omega) hi τ ⟨(D.eTau τ).2, ha, hc⟩).2
      linarith

end GlobalTheory.CoreHt.RowsRange
end
