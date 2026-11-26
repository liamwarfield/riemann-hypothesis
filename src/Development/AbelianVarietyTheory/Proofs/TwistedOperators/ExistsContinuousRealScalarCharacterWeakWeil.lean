module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnOfRapidDec
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionTranslatesThetaByUnitScalar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightLabelAtUnfolding
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTIota
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocKIntMem

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsContinuousRealScalarCharacterWeakWeil
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.OneMemRowHighestAndThPSmulOne
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW

theorem one_mem_rowHighest_and_thP_smul_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), (1 : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) ∈ Harm.rowHighest ℂ (fun _ _ => 0) (fun _ _ => 0) ∧ ∀ (c : ℂ) (φ : TF n g) (x : Frame X.Ψ r), thP X hr bas idx (c • φ) 1 x = c * (hMat X bas idx x).det ^ (n / 2) * thS φ (tauMat X bas idx x) 0 := by
  intro E _ _ _ r X g q0 hr bas idx n
  refine ⟨?_, fun c φ x => ?_⟩
  · simp only [Harm.rowHighest, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, MvPolynomial.mem_weightedHomogeneousSubmodule]
    refine ⟨⟨?_, fun _ _ => ?_, fun _ _ => ?_⟩, ?_, ?_⟩
    · show Harm.IsHarmonic _
      unfold Harm.IsHarmonic
      intro t a b
      simp [Harm.laplacian]
    · simp only [Harm.partOf, Finset.sum_const_zero]
      exact MvPolynomial.isWeightedHomogeneous_one _ _
    · simp only [Harm.partOf, Finset.sum_const_zero]
      exact MvPolynomial.isWeightedHomogeneous_one _ _
    · intro t a b _ s
      simp
    · intro t a b _ s
      simp
  · simp only [thP, ReciprocityTheory.ChartRestriction.G.I2.polyDeriv, MvPolynomial.support_one, Finset.sum_singleton,
      MvPolynomial.coeff_zero_one, one_mul]
    have h0 : ∀ (k : ℕ) (hk : k = 0) (v : Fin k → (Fin n → Fin g → ℂ)),
        iteratedFDeriv ℂ k (thA X bas idx (c • φ) x) 0 v = thA X bas idx (c • φ) x 0 := by
      rintro _ rfl v
      exact iteratedFDeriv_zero_apply v
    rw [h0 _ (by simp)]
    unfold thA thS
    simp only [Pi.zero_apply, Matrix.mulVec_zero, dotProduct_zero, Finset.sum_const_zero, mul_zero, Complex.exp_zero,
      one_mul, Pi.smul_apply, smul_eq_mul, mul_assoc, tsum_mul_left, add_zero]
    ring

end GlobalTheory.SW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsContinuousRealScalarCharacterWeakWeil
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdSpan.RealChar

variable {D : D7} {S T : HSp D}

theorem realPt_zero (C : Ctx S T) : C.realPt 0 = 0 := by
  funext σ k a
  simp [Ctx.realPt, compAt]

theorem th_zero_eq (C : Ctx S T) {x : Frame C.X.Ψ T.rank} (hx : x ∈ C.X.dom) {φ : TF S.rank C.g}
    (hφ : SW.IsSB φ) : C.Th x φ 0 = thR C.X C.bas C.idx φ x 0 := by
  have h0 : IsRealPt (0 : WO S T) := by
    ext i j
    simp
  rw [(GlobalTheory.Ker.ZakEx.isZak_Th D S T C x hx φ hφ).1.2 0 h0, realPt_zero]

theorem th_zero_eq_thP (C : Ctx S T) {x : Frame C.X.Ψ T.rank} (hx : x ∈ C.X.dom) {φ : TF S.rank C.g}
    (hφ : SW.IsSB φ) : C.Th x φ 0 = thP C.X C.hr C.bas C.idx φ 1 x := by
  have h := (GlobalTheory.SW.one_mem_rowHighest_and_thP_smul_one D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx S.rank).2 1 φ x
  rw [one_smul, one_mul] at h
  rw [h, th_zero_eq C hx hφ, thR]
  have hz : zR C.X C.idx x (0 : WR C.X S.rank) = 0 := by
    funext k i
    simp [zR, hermC]
  rw [hz, GlobalTheory.Ker.RealScalar.gaussR_zero C x, one_mul, thA]
  simp
  exact Or.inl rfl

theorem continuous_th_mvB (C : Ctx S T) (B : C.Bas) (hB : C.IsB B) (φ : TF S.rank C.g) (hφ : SW.IsSB φ) :
    Continuous (fun a : GA D T => C.Th (C.xB (C.mvB a B)) φ 0) := by
  have hS := fun B (hB : C.IsB B) => (GlobalTheory.Ker.onBasis_frame_period D S T C).2 B hB
  have hdom : ∀ a : GA D T, C.xB (C.mvB a B) ∈ C.X.dom := fun a => (hS _ ((hS B hB).2.2.2.2.2 a).1).2.1
  have e : (fun a : GA D T => C.Th (C.xB (C.mvB a B)) φ 0) =
      (thP C.X C.hr C.bas C.idx φ 1) ∘ fun a => C.xB (C.mvB a B) := by
    funext a
    exact th_zero_eq_thP C (hdom a) hφ
  rw [e]
  have hP := (GlobalTheory.SW.theta_holomorphic_weight D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx S.rank C.sympl C.even (fun _ _ => 0)
    (fun _ _ => 0) φ hφ 1 (GlobalTheory.SW.one_mem_rowHighest_and_thP_smul_one D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx S.rank).1).1
  refine hP.continuousOn.comp_continuous ?_ hdom
  have hc : ∀ τ, Continuous fun a : GA D T => compAt C.θ τ (Formalism.L2.Theta.mt T a) := fun τ =>
    (GlobalTheory.RealWeil.continuous_compAt C.inf τ T.rank T.rank).comp (GlobalTheory.RealWeil.continuous_mt T).1
  refine continuous_pi fun σ => continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Ctx.xB, Ctx.mvB]
  exact Complex.continuous_conj.comp
    ((continuous_apply j).comp ((continuous_apply i).comp ((hc _).matrix_mul continuous_const)))

theorem exists_th_zero_ne (C : Ctx S T) (B : C.Bas) (hB : C.IsB B) (φ : TF S.rank C.g) (hφ : SW.IsSB φ)
    (h0 : φ ≠ 0) : ∃ φ' : TF S.rank C.g, SW.IsSB φ' ∧ C.Th (C.xB B) φ' 0 ≠ 0 := by
  have hx : C.xB B ∈ C.X.dom := ((GlobalTheory.Ker.onBasis_frame_period D S T C).2 B hB).2.1
  have R := GlobalTheory.Ker.thR_laws D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx S.rank C.sympl C.even _ hx φ hφ
  have hd := (GlobalTheory.Ker.zR_laws D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx S.rank C.sympl C.even _ hx).2.2.2.1
  obtain ⟨y, hy⟩ : ∃ y, thR C.X C.bas C.idx φ (C.xB B) (embR C.X y) ≠ 0 := by
    by_contra hn
    push_neg at hn
    have hs : SW.IsSB ((0 : ℂ) • φ) := (isSB_algebra_haar_linear _ _ _ _ _ hφ hφ).2.1 0
    have e : thR C.X C.bas C.idx φ (C.xB B) = thR C.X C.bas C.idx ((0 : ℂ) • φ) (C.xB B) := by
      rw [R.2.2.2.2 0, zero_smul]
      exact hd.equalizer R.1.continuous continuous_const (funext hn)
    exact h0 (((R.2.2.2.1 _ hs).1 e).trans (zero_smul ℂ φ))
  have hs' := ((GlobalTheory.SW.heisG_laws D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even).2.2.2 y φ hφ).1
  refine ⟨_, hs', ?_⟩
  rw [th_zero_eq C hx hs', R.2.1 y 0, zero_add]
  exact mul_ne_zero (Complex.exp_ne_zero _) hy

end GlobalTheory.AdSpan.RealChar

namespace GlobalTheory.AdSpan.RealChar

theorem smul_cancel {α : Type} {F : α → ℂ} (hF : F ≠ 0) {c c' : ℂ} (h : c • F = c' • F) : c = c' := by
  obtain ⟨w, hw⟩ : ∃ w, F w ≠ 0 := by
    by_contra h'
    push_neg at h'
    exact hF (funext h')
  have := congrFun h w
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact mul_right_cancel₀ hw this

variable {D : D7} {S T : HSp D}

theorem th_ne (C : Ctx S T) {x : Frame C.X.Ψ T.rank} (hx : x ∈ C.X.dom) {φ : TF S.rank C.g}
    (hφ : SW.IsSB φ) (h0 : φ ≠ 0) : C.Th x φ ≠ 0 := by
  intro h
  have L := GlobalTheory.Ker.Ctx.th_laws D S T C x hx φ hφ
  have hs : SW.IsSB ((0 : ℂ) • φ) := (isSB_algebra_haar_linear _ _ _ _ _ hφ hφ).2.1 0
  have e : C.Th x φ = C.Th x ((0 : ℂ) • φ) := by rw [L.2.1, h, smul_zero]
  exact h0 (((L.1 _ hs).2 e).trans (zero_smul ℂ φ))

theorem th_zero (C : Ctx S T) {x : Frame C.X.Ψ T.rank} (hx : x ∈ C.X.dom) {φ : TF S.rank C.g}
    (hφ : SW.IsSB φ) (h0 : φ = 0) : C.Th x φ = 0 := by
  have L := GlobalTheory.Ker.Ctx.th_laws D S T C x hx φ hφ
  have e : φ = (0 : ℂ) • φ := by rw [h0, smul_zero]
  rw [e, L.2.1, zero_smul]

theorem kZero_ne (C : Ctx S T) {x₁ x₂ : Frame C.X.Ψ T.rank} (h₁ : x₁ ∈ C.X.dom) (h₂ : x₂ ∈ C.X.dom) :
    kZero C.X C.idx x₁ x₂ (0 : Fin S.rank → Fin C.g → ℂ) 0 ≠ 0 := by
  rw [GlobalTheory.AdTh.Overlap.kZero_zero]
  exact Finset.prod_ne_zero_iff.2 fun τ _ => inv_ne_zero (pow_ne_zero _ (mul_ne_zero
    (DblPoint.det_aLin_ne_zero h₁ h₂ τ) (DblPoint.det_aAnti_ne_zero h₁ h₂ τ)))

theorem realScal_character : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ContT C.ψ om → ∃ z : GA D T → ℂ, (∀ a ∈ GinfC T, ∀ a' ∈ GinfC T, z (a * a') = z a * z a') ∧ (∀ a ∈ GinfC T, ‖z a‖ = 1) ∧ ContinuousOn z (GinfC T : Set (GA D T)) ∧ ∀ B, C.IsB B → ∀ a ∈ GinfC T, RealScal C om B a (z a) := by
  intro D S T C om hom hcont
  obtain ⟨B₀, hB₀⟩ := (GlobalTheory.Ker.onBasis_frame_period D S T C).1
  have hS := fun B (hB : C.IsB B) => (GlobalTheory.Ker.onBasis_frame_period D S T C).2 B hB
  have hdom : ∀ B, C.IsB B → C.xB B ∈ C.X.dom := fun B hB => (hS B hB).2.1
  have hmvB : ∀ B, C.IsB B → ∀ g : GA D T, C.IsB (C.mvB g B) := fun B hB g => ((hS B hB).2.2.2.2.2 g).1
  have hex : ∀ B, C.IsB B → ∀ a ∈ GinfC T, ∃ c : ℂ, ‖c‖ = 1 ∧ RealScal C om B a c := fun B hB a ha =>
    GlobalTheory.Ker.RealScalar.om_real_Th D S T C om hom 1 (one_mem _) a ha B hB
  by_cases hne : ∃ φ : TF S.rank C.g, SW.IsSB φ ∧ φ ≠ 0
  swap
  · refine ⟨fun _ => 1, fun _ _ _ _ => (mul_one 1).symm, fun _ _ => norm_one, continuousOn_const,
      fun B hB a ha φ hφ => ?_⟩
    obtain ⟨c, -, hc⟩ := hex B hB a ha
    have h0 : φ = 0 := by
      by_contra h
      exact hne ⟨φ, hφ, h⟩
    rw [hc φ hφ, th_zero C (hdom _ (hmvB B hB a)) hφ h0, smul_zero, smul_zero]
  obtain ⟨φ₀, hφ₀, h0⟩ := hne
  let z : GA D T → ℂ := fun a => if h : a ∈ GinfC T then (hex B₀ hB₀ a h).choose else 1
  have hz : ∀ a (ha : a ∈ GinfC T), ‖z a‖ = 1 ∧ RealScal C om B₀ a (z a) := fun a ha => by
    simp only [z, dif_pos ha]
    exact (hex B₀ hB₀ a ha).choose_spec
  obtain ⟨⟨μ, 𝓕, hμ⟩, hip⟩ := GlobalTheory.Ker.ScalarProduct.ip_basic D S T C
  have hth : ∀ B, C.IsB B → ∀ φ : TF S.rank C.g, SW.IsSB φ → C.IsTh (C.Th (C.xB B) φ) :=
    fun B hB φ hφ => (GlobalTheory.Ker.ZakEx.isZak_Th D S T C _ (hdom B hB) φ hφ).1.1

  have hip2 : ∀ B B', C.IsB B → C.IsB B' → ∀ g : GA D T,
      ipO μ 𝓕 (C.Th (C.xB (C.mvB g B)) φ₀) (C.Th (C.xB (C.mvB g B')) φ₀) =
        ipO μ 𝓕 (C.Th (C.xB B) φ₀) (C.Th (C.xB B') φ₀) := fun B B' hB hB' g => by
    rw [GlobalTheory.AdTh.Overlap.ipO_Th C hμ (hdom _ (hmvB B hB g)) (hdom _ (hmvB B' hB' g)) hφ₀ hφ₀,
      GlobalTheory.AdTh.Overlap.ipO_Th C hμ (hdom _ hB) (hdom _ hB') hφ₀ hφ₀, GlobalTheory.AdTh.Overlap.kZero_mvB C hB g]
  have hdbl : dbl C.X C.bas C.idx φ₀ φ₀ 0 ≠ 0 := by
    intro hc
    have h1 := GlobalTheory.AdTh.Overlap.ipO_Th C hμ (hdom _ hB₀) (hdom _ hB₀) hφ₀ hφ₀
    rw [hc, zero_mul] at h1
    exact th_ne C (hdom _ hB₀) hφ₀ h0 ((hip μ 𝓕 hμ _ (hth B₀ hB₀ φ₀ hφ₀)).2.1 h1)
  have hipne : ∀ B B', C.IsB B → C.IsB B' →
      ipO μ 𝓕 (C.Th (C.xB B) φ₀) (C.Th (C.xB B') φ₀) ≠ 0 := fun B B' hB hB' => by
    rw [GlobalTheory.AdTh.Overlap.ipO_Th C hμ (hdom _ hB) (hdom _ hB') hφ₀ hφ₀]
    exact mul_ne_zero hdbl (kZero_ne C (hdom _ hB) (hdom _ hB'))

  have hind : ∀ B, C.IsB B → ∀ a (ha : a ∈ GinfC T), RealScal C om B a (z a) := by
    intro B hB a ha
    obtain ⟨c, -, hc⟩ := hex B hB a ha
    obtain ⟨hzn, hzs⟩ := hz a ha
    suffices e : c = z a by rw [← e]; exact hc
    have t1 := hth B hB φ₀ hφ₀
    have t2 := hth B₀ hB₀ φ₀ hφ₀
    have t1' := hth _ (hmvB B hB a) φ₀ hφ₀
    have t2' := hth _ (hmvB B₀ hB₀ a) φ₀ hφ₀
    have u := ((hip μ 𝓕 hμ _ t1).2.2.2 _ t2).2.2.2.2.2 om hom (1, a)
    have t3 : C.IsTh ((z a) • C.Th (C.xB (C.mvB a B₀)) φ₀) := hzs φ₀ hφ₀ ▸ hom.om_pres (1, a) _ t2
    rw [hc φ₀ hφ₀, hzs φ₀ hφ₀, ((hip μ 𝓕 hμ _ t1').2.2.2 _ t3).2.2.1,
      ((hip μ 𝓕 hμ _ t3).2.2.2 _ t1').2.1, ((hip μ 𝓕 hμ _ t2').2.2.2 _ t1').2.2.1, map_mul,
      ((hip μ 𝓕 hμ _ t1').2.2.2 _ t2').2.1, Complex.conj_conj, hip2 B B₀ hB hB₀ a] at u
    have K := hipne B B₀ hB hB₀
    have h1 : c * conj (z a) = 1 := mul_right_cancel₀ K (by linear_combination u)
    have h2 : z a * conj (z a) = 1 := by
      rw [Complex.mul_conj', hzn]; simp
    calc c = c * (z a * conj (z a)) := by rw [h2, mul_one]
      _ = (c * conj (z a)) * z a := by ring
      _ = z a := by rw [h1, one_mul]
  refine ⟨z, fun a ha a' ha' => ?_, fun a ha => (hz a ha).1, ?_, hind⟩
  ·
    have e1 := hind B₀ hB₀ (a * a') (mul_mem ha ha') φ₀ hφ₀
    have e2 := hind B₀ hB₀ a' ha' φ₀ hφ₀
    have e3 := hind _ (hmvB B₀ hB₀ a') a ha φ₀ hφ₀
    have hm : om (1, a * a') = om (1, a) * om (1, a') := by
      rw [← map_mul, Prod.mk_mul_mk, one_mul]
    rw [hm, Module.End.mul_apply, e2, map_smul, e3, smul_smul,
      ← ((hS B₀ hB₀).2.2.2.2.2 a').2.1 a] at e1
    have := smul_cancel (th_ne C (hdom _ (hmvB B₀ hB₀ (a * a'))) hφ₀ h0) e1
    rw [← this, mul_comm]
  ·
    intro a₀ ha₀
    obtain ⟨φ, hφ, hφ0⟩ := exists_th_zero_ne C _ (hmvB B₀ hB₀ a₀) φ₀ hφ₀ h0
    have hN : Continuous fun a : GA D T => om (1, a) (C.Th (C.xB B₀) φ) 0 :=
      hcont _ (hth B₀ hB₀ φ hφ) 0
    have hD := continuous_th_mvB C B₀ hB₀ φ hφ
    have heq : ∀ a ∈ GinfC T, C.Th (C.xB (C.mvB a B₀)) φ 0 ≠ 0 →
        om (1, a) (C.Th (C.xB B₀) φ) 0 / C.Th (C.xB (C.mvB a B₀)) φ 0 = z a := fun a ha hne => by
      rw [hind B₀ hB₀ a ha φ hφ, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self hne, mul_one]
    refine ContinuousWithinAt.congr_of_eventuallyEq
      ((hN.continuousAt.div hD.continuousAt hφ0).continuousWithinAt) ?_ (heq a₀ ha₀ hφ0).symm
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hD.continuousAt.eventually_ne hφ0)] with a ha hne
    exact (heq a ha hne).symm

end GlobalTheory.AdSpan.RealChar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsContinuousRealScalarCharacterWeakWeilStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_realScalar_character_weakWeil : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ContT C.ψ om → ∃ z : GA D T → ℂ, (∀ a ∈ GinfC T, ∀ a' ∈ GinfC T, z (a * a') = z a * z a') ∧ (∀ a ∈ GinfC T, ‖z a‖ = 1) ∧ ContinuousOn z (GinfC T : Set (GA D T)) ∧ ∀ B, C.IsB B → ∀ a ∈ GinfC T, RealScal C om B a (z a) := by
  first | exact @GlobalTheory.AdSpan.RealChar.realScal_character | exact GlobalTheory.AdSpan.RealChar.realScal_character | (intros; apply GlobalTheory.AdSpan.RealChar.realScal_character <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateMaximalCompactMemParahoricLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateMaximalCompactMemParahoricLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open Matrix
namespace GlobalTheory.KapLevel

theorem cast_one_fin {I I' : Formalism.MainNotions.S.AutInst} (e : I = I') (k : I'.Gf) (hk : k ∈ I'.Kset) :
    ((Formalism.L2.SG.RowsJoinPinned.castGA e).symm (1, k)).1 = 1 ∧
      ((Formalism.L2.SG.RowsJoinPinned.castGA e).symm (1, k)).2 ∈ I.Kset := by
  subst e
  exact ⟨rfl, hk⟩

theorem lat_eq (D : D7) : Formalism.L2.SG.InstExistsPf.Lv D = Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0 := by
  rw [Formalism.L2.SG.InstExistsPf.Lv_eq_map]
  rfl

theorem hatL_eq (D : D7) :
    (Formalism.IndefR.RationalEmbedding.inst D).Lf = Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) := by
  show Formalism.MainNotions.S.lamAf (F := D.host.F) (Formalism.L2.SG.InstExistsPf.Lv D) = _
  rw [Formalism.MainNotions.S.Inh.aut_lamAf_eq, lat_eq]
  rfl

theorem kset_stab {D : D7} (x : (Formalism.IndefR.RationalEmbedding.inst D).Gf) (hx : x ∈ (Formalism.IndefR.RationalEmbedding.inst D).Kset)
    (g : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)) (hg : g = x.1) :
    (∀ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0),
      g.1 *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0)) ∧
    ∀ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0),
      (g⁻¹).1 *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) := by
  subst hg
  have h0 : x.1 ∈ Formalism.UG.stabGL (Formalism.IndefR.RationalEmbedding.inst D).Lf := hx
  have h1 : x.1⁻¹ ∈ Formalism.UG.stabGL (Formalism.IndefR.RationalEmbedding.inst D).Lf := (Formalism.UG.stabGL (Formalism.IndefR.RationalEmbedding.inst D).Lf).inv_mem h0
  have e := SetLike.ext_iff.1 (hatL_eq D)
  refine ⟨fun y hy => (e _).1 ((h0 y).1 ((e y).2 hy)), fun y hy => (e _).1 ((h1 y).1 ((e y).2 hy))⟩

theorem st_of_stab {D : D7} (g ft β : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D))
    (hF : Formalism.L2.DIV.IsFrame (ft * β) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0))
    (h0 : ∀ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0),
      g.1 *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0))
    (h1 : ∀ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0),
      (g⁻¹).1 *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0)) :
    ft⁻¹ * g * ft ∈ Formalism.L2.DIV.St β := by
  have hS : g ∈ Formalism.L2.DIV.St (ft * β) := (GlobalTheory.LevSplit.mem_St_iff (ft * β) _ hF g).2 ⟨h0, h1⟩
  obtain ⟨z, hz⟩ := hS
  refine ⟨z, ?_⟩
  rw [← hz]
  show β * Formalism.L2.DIV.intGL _ _ _ z * β⁻¹ = ft⁻¹ * ((ft * β) * Formalism.L2.DIV.intGL _ _ _ z * (ft * β)⁻¹) * ft
  group

theorem kap_mem_parLev : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (t : GA D (Yc D 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧ (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)) → IdempotentRealFixed D → t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ k ∈ X.B.I.Kset, kap X h t k ∈ GfC (Yc D 0) ∧ finE (Yc D 0) (kap X h t k) ∈ Formalism.L2.DIV.parLev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 R.triv) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h _ _ _ cG t _ _ _ ht _ hF k hk
  obtain ⟨hy1, hy2⟩ := cast_one_fin h.symm k hk
  have hkap : kap X h t k = (@id (GA D (D.sp.Y 0)) t)⁻¹ * (Formalism.IndefR.RationalEmbedding.iota D).symm
      ((Formalism.L2.SG.RowsJoinPinned.castGA h.symm).symm (1, k)) * @id (GA D (D.sp.Y 0)) t := rfl
  refine ⟨?_, ?_⟩
  · rw [hkap]
    exact mul_mem (mul_mem (inv_mem ht) ((Formalism.L2.SG.EvalTIota.brg_mem_GfC_i _).2 hy1)) ht
  · have hU := GlobalTheory.LevSplit.finE_mem_UA (Yc D 0) (kap X h t k)
    have hfin0 : Formalism.IndefR.Lev.finE (D.sp.Y 0) (kap X h t k) = (Formalism.IndefR.Lev.finE (D.sp.Y 0) t)⁻¹ *
        @id (GL (Fin (D.sp.Y 0).rank) (Formalism.IndefR.Lev.EAf D)) ((Formalism.L2.SG.RowsJoinPinned.castGA h.symm).symm (1, k)).2.1 *
        Formalism.IndefR.Lev.finE (D.sp.Y 0) t := by
      rw [hkap, map_mul, map_mul, map_inv, Formalism.L2.SG.EvalTIota.finE_brg_i]
      rfl
    have hfin : Formalism.IndefR.Lev.finE (Yc D 0) (kap X h t k) = (Formalism.IndefR.Lev.finE (Yc D 0) t)⁻¹ *
        @id (GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)) ((Formalism.L2.SG.RowsJoinPinned.castGA h.symm).symm (1, k)).2.1 *
        Formalism.IndefR.Lev.finE (Yc D 0) t := hfin0
    rw [hfin] at hU ⊢
    obtain ⟨s0, s1⟩ := kset_stab _ hy2 _ rfl
    have hr : ∀ a : Fin (Yc D 0).rank, (a : ℕ) < (R.dat0 R.triv).r := fun a =>
      lt_of_lt_of_eq a.2 (Formalism.L2.SG.InstExistsPf.rank_eq D)
    refine Formalism.L2.DIV.mem_parLev.2 ⟨hU, st_of_stab _ _ _ hF s0 s1, fun PP _ => ?_, fun PP hP => ?_⟩
    · rw [Formalism.L2.DIV.mem_blockTri]
      intro i j hij
      exfalso
      unfold Formalism.L2.DIV.blkOf at hij
      rw [if_pos (hr i), if_pos (hr j)] at hij
      exact lt_irrefl 0 hij
    · exact absurd hP (Finset.notMem_empty PP)

end GlobalTheory.KapLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateMaximalCompactMemParahoricLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_maximalCompact_mem_parahoricLevel : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (t : GA D (Yc D 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧ (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)) → IdempotentRealFixed D → t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ k ∈ X.B.I.Kset, kap X h t k ∈ GfC (Yc D 0) ∧ finE (Yc D 0) (kap X h t k) ∈ Formalism.L2.DIV.parLev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 R.triv) := by
  first | exact @GlobalTheory.KapLevel.kap_mem_parLev | exact GlobalTheory.KapLevel.kap_mem_parLev | (intros; apply GlobalTheory.KapLevel.kap_mem_parLev <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfSEEofTT
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankComapOfLeRange
noncomputable section

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.Lev Formalism.L2.Theta NumberField MeasureTheory GlobalTheory.Mem.SJ Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ.RowIso

theorem finrank_eq_of_semi {σ : ℂ →+* ℂ} (hσ : Function.Bijective σ) {E F : Type} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] (f : E →ₛₗ[σ] F) (hf : Function.Bijective f) :
    Module.finrank ℂ E = Module.finrank ℂ F := by
  unfold Module.finrank
  congr 1
  exact rank_eq_of_equiv_equiv σ (AddEquiv.ofBijective f.toAddMonoidHom hf) hσ (fun r m => f.map_smulₛₗ r m)

theorem finrank_twSub (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (V : Submodule ℂ E) :
    Module.finrank ℂ (Tw.sub s V) = Module.finrank ℂ V := by
  have hσ : Function.Bijective (cj s) := Function.Involutive.bijective (cj_cj s)
  let f : (Tw.sub s V) →ₛₗ[cj s] V :=
    { toFun := fun x => ⟨Tw.out x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact finrank_eq_of_semi hσ f ⟨fun x y h => Subtype.ext (congrArg Subtype.val h), fun y => ⟨⟨Tw.mk s y.1, y.2⟩, rfl⟩⟩

theorem finrank_comap_of_le_range {E F : Type} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (e : E →ₗ[ℂ] F) (he : Function.Injective e) (V : Submodule ℂ F) (hV : V ≤ LinearMap.range e) :
    Module.finrank ℂ (V.comap e) = Module.finrank ℂ V := by
  have h := (Submodule.equivMapOfInjective e he (V.comap e)).finrank_eq
  rwa [Submodule.map_comap_eq_self hV] at h

theorem finrank_EEC {D : D7} (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (Gd : GoodOp St) :
    Module.finrank ℂ (EEC St Gd) = Module.finrank ℂ (goodSub St Gd) := by
  let f : EEC St Gd →ₛₗ[starRingEnd ℂ] goodSub St Gd :=
    { toFun := fun x => ⟨star (x : L2X St), (mem_EEC St Gd _).1 x.2⟩
      map_add' := fun x y => Subtype.ext ((conjL (muX St)).map_add _ _)
      map_smul' := fun c x => Subtype.ext ((conjL (muX St)).map_smulₛₗ c _) }
  refine finrank_eq_of_semi (Function.Involutive.bijective (fun z => Complex.conj_conj z)) f ⟨fun x y h => ?_, fun y => ?_⟩
  · exact Subtype.ext (star_injective (congrArg Subtype.val h))
  · refine ⟨⟨star (y : L2X St), ?_⟩, Subtype.ext (star_star _)⟩
    rw [mem_EEC, star_star]
    exact y.2

theorem finrank_of_evalTieT {D : D7} {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar} {M : DSModel (D.sp.Y 0) S}
    {μ : Measure (GA D (D.sp.Y 0))} {𝓕 : Set (GA D (D.sp.Y 0))} {E : Submodule ℂ (MMap M)}
    {St : Formalism.L2.SG.HidaSetting.HidaSetting D} {Gd : GoodOp St} {ι : GA D (D.sp.Y 0) ≃* St.B.I.GA} {t : GA D (D.sp.Y 0)} {c : ℝ}
    (hE : EvalTieT M μ 𝓕 E St Gd ι t c) : Module.finrank ℂ (goodSub St Gd) = Module.finrank ℂ E := by
  obtain ⟨_, _, j, _⟩ := hE
  rw [← finrank_EEC, ← j.finrank_eq]

theorem clauses {D : D7} {St : Formalism.L2.SG.HidaSetting.HidaSetting D} (s : Bool) {Bs : DefBase D.what₂.LL} {Df : DefSide Bs}
    (Dc : DefCols Df) (hK : St.LevelSubgroupCharacter) (Gd : GoodOp St) (wdD : Dc.Mem → D.what₂.Word) (pw : ∀ x, PerW St hK (wdD x))
    (bR : ∀ x, Fin (Dc.a x) → (D.mem (wdD x)).A.Mram) (Sp : SPer Dc) (hSp : Sp = spOf s Dc hK Gd wdD pw bR)
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (V : Submodule ℂ E) (n : ℝ)
    (sEE : E →ₗ⋆[ℂ] Sp.HH) (sEEc : E →ₗ⋆[ℂ] Tw s (HHX St)) (h : HEq sEE sEEc)
    (h1 : ∀ e ∈ V, n * ‖sEEc e‖ ^ 2 = ‖e‖ ^ 2)
    (h2 : ∀ e ∈ V, ((Tw.out (s := s) (sEEc e) : HHX St) : L2X St) ∈ goodSub St Gd)
    (h3 : Module.finrank ℂ (goodSub St Gd) = Module.finrank ℂ V) :
    (∀ e ∈ V, n * ‖sEE e‖ ^ 2 = ‖e‖ ^ 2) ∧ (∀ e ∈ V, sEE e ∈ Sp.Rw) ∧
      Module.finrank ℂ Sp.Rw = Module.finrank ℂ V := by
  subst hSp
  obtain rfl := eq_of_heq h
  refine ⟨h1, h2, ?_⟩
  rw [← h3]
  refine (finrank_twSub s ((goodSub St Gd).comap (HHX St).subtype)).trans ?_
  refine finrank_comap_of_le_range _ Subtype.val_injective _ ?_
  rw [Submodule.range_subtype]
  exact inf_le_left

end GlobalTheory.Mem.SJ.RowIso

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Twist.SeeIsoRow

variable {D : D7} {S : D.what₂.Tau → SPar}

theorem sEEofTT_apply {M : DSModel (D.sp.Y 0) S} {μ : Measure (GA D (D.sp.Y 0))} {𝓕 : Set (GA D (D.sp.Y 0))}
    {E : Submodule ℂ (MMap M)} {St : Formalism.L2.SG.HidaSetting.HidaSetting D} {Gd : GoodOp St} {ι : GA D (D.sp.Y 0) ≃* St.B.I.GA}
    {t : GA D (D.sp.Y 0)} {c : ℝ} (hE : EvalTieT M μ 𝓕 E St Gd ι t c) (T : E) :
    sEEofTT M μ 𝓕 E St Gd ι t c T = conjHH St Gd (hE.choose_spec.2.choose T) := by
  unfold sEEofTT
  simp only [dif_pos hE]
  rfl

theorem norm_sq_sEEofTT {M : DSModel (D.sp.Y 0) S} {μ : Measure (GA D (D.sp.Y 0))} {𝓕 : Set (GA D (D.sp.Y 0))}
    {E : Submodule ℂ (MMap M)} {St : Formalism.L2.SG.HidaSetting.HidaSetting D} {Gd : GoodOp St} {ι : GA D (D.sp.Y 0) ≃* St.B.I.GA}
    {t : GA D (D.sp.Y 0)} {c : ℝ} (hE : EvalTieT M μ 𝓕 E St Gd ι t c) (T : E) :
    ‖sEEofTT M μ 𝓕 E St Gd ι t c T‖ ^ 2 = c * (ipM M μ 𝓕 (T : MMap M) (T : MMap M)).re := by
  have h := congrArg norm (sEEofTT_apply hE T)
  rw [LinearIsometry.norm_map] at h
  rw [h]
  exact (hE.choose_spec.2.choose_spec T).2

theorem eq_zero_of_sEEofTT {M : DSModel (D.sp.Y 0) S} {μ : Measure (GA D (D.sp.Y 0))} {𝓕 : Set (GA D (D.sp.Y 0))}
    {E : Submodule ℂ (MMap M)} {St : Formalism.L2.SG.HidaSetting.HidaSetting D} {Gd : GoodOp St} {ι : GA D (D.sp.Y 0) ≃* St.B.I.GA}
    {t : GA D (D.sp.Y 0)} {c : ℝ} (hE : EvalTieT M μ 𝓕 E St Gd ι t c) (T : E)
    (h : ‖sEEofTT M μ 𝓕 E St Gd ι t c T‖ = 0) : T = 0 := by
  have h1 := congrArg norm (sEEofTT_apply hE T)
  rw [LinearIsometry.norm_map] at h1
  have h2 : ‖hE.choose_spec.2.choose T‖ = 0 := h1.symm.trans h
  exact (LinearEquiv.map_eq_zero_iff _).1 (norm_eq_zero.1 h2)

theorem seeIso_row : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Gd : GoodOp X) (hK : X.LevelSubgroupCharacter) (Zs : DefSub A3.fam3.amb3) (Dc : DefCols (A3.side3 F.P1 F.ψ1 Zs)) (wdD : Dc.Mem → D.what₂.Word) (pw : ∀ x, PerW X hK (wdD x)) (bR : ∀ x, Fin (Dc.a x) → (D.mem (wdD x)).A.Mram) (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH) (sEEc : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H →ₗ⋆[ℂ] Tw (twAt D.what₂.embLL A3.A.v0) (HHX X)) (ι : GA D (Yc D 0) ≃* X.B.I.GA) (tS : GA D (Yc D 0)) (cS κS : ℝ) (uS : ℂ), R.toRealDat.IsModels → (R.toCx3 F).zs = Zs → F.Dc Zs = Dc → HEq (F.Sp Zs) (spOf (X := X) (twAt D.what₂.embLL A3.A.v0) Dc hK Gd wdD pw bR) → HEq sEE sEEc → EvalTieT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) X Gd ι tS cS → ‖uS‖ = 1 → (∀ (x : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H) (hx : R.HE.e (Tw.out x) ∈ (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true))), sEEc x = Tw.mk (twAt D.what₂.embLL A3.A.v0) ((uS * (κS : ℂ)) • (sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) X Gd ι tS cS) ⟨R.HE.e (Tw.out x), hx⟩)) → (0 < κS ∧ ((∃ κ' : ℝ, 0 < κ' ∧ ∀ (x : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H) (hx : R.HE.e (Tw.out x) ∈ (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true))), ‖(κ' : ℂ) • (sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) X Gd ι tS cS) ⟨R.HE.e (Tw.out x), hx⟩‖ = ‖x‖) → ∀ (x : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H), R.HE.e (Tw.out x) ∈ (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) → RealDat.nP F.lv2 true * ‖sEEc x‖ ^ 2 = ‖x‖ ^ 2)) → (R.toCx3 F).SEEIso sEE := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F X Gd hK Zs Dc wdD pw bR sEE sEEc ι tS cS κS uS hM hzs hDc hSp hh hE _ hDef hK'
  subst hzs
  subst hDc
  have hSp' := eq_of_heq hSp
  have hHE := hM.HE
  have hle := (GlobalTheory.T.goodRows_level_sub_principalLevel_hilbertModel R.toRealDat hM).1 (R.toRealDat.levR F.lv2 true)
  have key : ∀ (x : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H)
      (hx : R.HE.e (Tw.out x) ∈ R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)),
      ‖sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) X Gd ι tS cS ⟨R.HE.e (Tw.out x), hx⟩‖ ^ 2 = cS * ‖x‖ ^ 2 := by
    intro x hx
    rw [norm_sq_sEEofTT hE]
    congr 1
    show (ipM (R.MY 0) R.ν0 R.fd0 (R.HE.e (Tw.out x)) (R.HE.e (Tw.out x))).re = ‖Tw.out x‖ ^ 2
    rw [← hHE.2.2]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (Tw.out x)
  have hex : ∃ κ' : ℝ, 0 < κ' ∧ ∀ (x : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H)
      (hx : R.HE.e (Tw.out x) ∈ R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)),
      ‖(κ' : ℂ) • sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) X Gd ι tS cS ⟨R.HE.e (Tw.out x), hx⟩‖ = ‖x‖ := by
    by_cases hc : 0 < cS
    · have hsp : 0 < Real.sqrt cS := Real.sqrt_pos.2 hc
      refine ⟨(Real.sqrt cS)⁻¹, inv_pos.2 hsp, fun x hx => ?_⟩
      have h1 : ‖sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) X Gd ι tS cS ⟨R.HE.e (Tw.out x), hx⟩‖ = Real.sqrt cS * ‖x‖ := by
        rw [← pow_left_inj₀ (norm_nonneg _) (mul_nonneg hsp.le (norm_nonneg _)) two_ne_zero, key x hx, mul_pow,
          Real.sq_sqrt hc.le]
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_pos.2 hsp).le, h1, ← mul_assoc,
        inv_mul_cancel₀ hsp.ne', one_mul]
    · refine ⟨1, one_pos, fun x hx => ?_⟩
      have h2 : ‖sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) X Gd ι tS cS ⟨R.HE.e (Tw.out x), hx⟩‖ ^ 2 ≤ 0 := by
        rw [key x hx]
        exact mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hc) (sq_nonneg _)
      have h0 : ‖sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) X Gd ι tS cS ⟨R.HE.e (Tw.out x), hx⟩‖ = 0 :=
        pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h2 (sq_nonneg _))
      have hT := eq_zero_of_sEEofTT hE _ h0
      have he0 : R.HE.e (Tw.out x) = 0 := congrArg Subtype.val hT
      have hx0 : Tw.out x = 0 := (map_eq_zero_iff _ hHE.1).1 he0
      rw [norm_smul, h0, mul_zero]
      show 0 = ‖Tw.out x‖
      rw [hx0, norm_zero]
  have hn := hK'.2 hex
  refine GlobalTheory.Mem.SJ.RowIso.clauses (twAt D.what₂.embLL A3.A.v0) (F.Dc (R.toCx3 F).zs) hK Gd wdD pw bR (F.Sp (R.toCx3 F).zs)
    hSp' ((R.toCx3 F).EEl true) ((R.toCx3 F).nP true) sEE sEEc hh (fun e he => hn e he) (fun e he => ?_) ?_
  · refine (congrArg (fun y : Tw (twAt D.what₂.embLL A3.A.v0) (HHX X) =>
      ((Tw.out y : HHX X) : L2X X) ∈ goodSub X Gd) (hDef e he)).mpr ?_
    show (((uS * (κS : ℂ)) • sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) X Gd ι tS cS ⟨R.HE.e (Tw.out e), he⟩ : HHX X) : L2X X) ∈ goodSub X Gd
    rw [Submodule.coe_smul]
    refine Submodule.smul_mem _ _ ?_
    unfold sEEofTT
    rw [dif_pos hE]
    exact (mem_EEC X Gd _).1 (hE.choose_spec.2.choose _).2
  · refine (GlobalTheory.Mem.SJ.RowIso.finrank_of_evalTieT hE).trans ?_
    refine Eq.symm ((GlobalTheory.Mem.SJ.RowIso.finrank_twSub (E := R.HE.H) (twAt D.what₂.embLL A3.A.v0)
      ((R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)).comap R.HE.e)).trans ?_)
    refine GlobalTheory.Mem.SJ.RowIso.finrank_comap_of_le_range _ hHE.1 _ ?_
    rw [hHE.2.1]
    exact hle

end GlobalTheory.Twist.SeeIsoRow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharacterFiniteOrderValuesInField
namespace HeckeCharacterValueBounds
section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio

namespace GlobalTheory.CompanionTheory.CharValues

open Formalism.L2.Host

section General

variable {E : Type} [Field E] [NumberField E]

theorem exp_lt_one (m : ℕ) : (WithZero.exp (-((m : ℤ) + 1)) : WithZero (Multiplicative ℤ)) < 1 := by
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
  omega

private theorem valued_v_algebraMap_adicCompletion' (v : HeightOneSpectrum (𝓞 E)) (a : E) :
    Valued.v (algebraMap E (v.adicCompletion E) a) = v.valuation E a := by
  first
    | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v a
    | (rw [HeightOneSpectrum.algebraMap_adicCompletion]; exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v a)

theorem locK_eq_of_level (χ : HChar E) {v : HeightOneSpectrum (𝓞 E)} {m : ℕ} (h : χ.LevelLe v m) (x y : Eˣ)
    (hxy : v.valuation E ((y : E) - x) ≤ WithZero.exp (-((m : ℤ) + 1)) * v.valuation E (x : E)) :
    χ.locK v y = χ.locK v x := by
  have hx0 : (x : E) ≠ 0 := x.ne_zero
  have hv0 : v.valuation E (x : E) ≠ 0 := ((v.valuation E).ne_zero_iff).mpr hx0

  have hd : ((y * x⁻¹ : Eˣ) : E) - 1 = ((y : E) - x) * (x : E)⁻¹ := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, sub_mul, mul_inv_cancel₀ hx0]
  have hle : v.valuation E (((y * x⁻¹ : Eˣ) : E) - 1) ≤ WithZero.exp (-((m : ℤ) + 1)) := by
    rw [hd, map_mul, map_inv₀]
    calc v.valuation E ((y : E) - x) * (v.valuation E (x : E))⁻¹
        ≤ WithZero.exp (-((m : ℤ) + 1)) * v.valuation E (x : E) * (v.valuation E (x : E))⁻¹ := by
          first | gcongr | exact mul_le_mul_right' hxy _
      _ = WithZero.exp (-((m : ℤ) + 1)) := by rw [mul_assoc, mul_inv_cancel₀ hv0, mul_one]
  have hlt : v.valuation E (((y * x⁻¹ : Eˣ) : E) - 1) < v.valuation E 1 := by
    rw [map_one]
    exact lt_of_le_of_lt hle (exp_lt_one m)
  have hu : v.valuation E ((y * x⁻¹ : Eˣ) : E) = 1 := ((v.valuation E).map_eq_of_sub_lt hlt).trans (map_one _)

  have hA : IsUnitAt v (atFin v (y * x⁻¹)) := by
    show Valued.v (algebraMap E (v.adicCompletion E) ((y * x⁻¹ : Eˣ) : E)) = 1
    rw [valued_v_algebraMap_adicCompletion']
    exact hu
  have hB : Valued.v (((atFin v (y * x⁻¹) : (v.adicCompletion E)ˣ) : v.adicCompletion E) - 1) ≤
      WithZero.exp (-(m : ℤ)) := by
    show Valued.v (algebraMap E (v.adicCompletion E) ((y * x⁻¹ : Eˣ) : E) - 1) ≤ _
    rw [← map_one (algebraMap E (v.adicCompletion E)), ← map_sub, valued_v_algebraMap_adicCompletion']
    exact le_trans hle (WithZero.exp_le_exp.mpr (by omega))
  have h1 : χ.locK v (y * x⁻¹) = 1 := h _ hA hB
  calc χ.locK v y = χ.locK v (y * x⁻¹ * x) := by rw [mul_assoc, inv_mul_cancel, mul_one]
    _ = χ.locK v x := by rw [map_mul, h1, one_mul]

theorem exists_approx (S : Finset (HeightOneSpectrum (𝓞 E))) (t : HeightOneSpectrum (𝓞 E) → 𝓞 E) (m : HeightOneSpectrum (𝓞 E) → ℕ)
    (ht : ∀ v, t v ≠ 0) : ∃ y : 𝓞 E, ∀ v ∈ S,
      v.valuation E ((y : E) - (t v : E)) ≤ WithZero.exp (-((m v : ℤ) + 1)) * v.valuation E (t v : E) := by
  classical

  have hk : ∀ v : HeightOneSpectrum (𝓞 E),
      WithZero.exp (WithZero.log (v.intValuation (t v))) = v.intValuation (t v) :=
    fun v => WithZero.exp_log (v.intValuation_ne_zero _ (ht v))
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun v => v.asIdeal)
    (fun v => ((m v : ℤ) + 1 - WithZero.log (v.intValuation (t v))).toNat)
    (fun v _ => Ideal.prime_of_isPrime v.ne_bot v.isPrime)
    (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h))
    (fun v => t v.1)
  refine ⟨y, fun v hv => ?_⟩
  have h1 := (v.intValuation_le_pow_iff_mem (y - t v) _).mpr (hy v hv)
  have h2 : v.valuation E ((y : E) - (t v : E)) = v.intValuation (y - t v) := by
    have h := v.valuation_of_algebraMap (K := E) (y - t v)
    first
      | (push_cast at h; exact h)
      | exact h
      | simpa using h
  have h3 : v.valuation E (t v : E) = v.intValuation (t v) := v.valuation_of_algebraMap (K := E) (t v)
  rw [h2, h3, ← hk v, ← WithZero.exp_add]
  refine le_trans h1 (WithZero.exp_le_exp.mpr ?_)
  have := Int.self_le_toNat ((m v : ℤ) + 1 - WithZero.log (v.intValuation (t v)))
  omega

private theorem exp_neg_succ_mul_lt_self (m : ℕ) {b : WithZero (Multiplicative ℤ)} (hb : b ≠ 0) :
    WithZero.exp (-((m : ℤ) + 1)) * b < b := by
  rw [← WithZero.exp_log hb, ← WithZero.exp_add, WithZero.exp_lt_exp]
  omega

theorem locK_mem (χ : HChar E) (G : Subgroup ℂˣ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (hunr : ∀ v, v ∉ T → χ.UnrAt v) (hval : ∀ v, v ∉ T → χ.val v ∈ G)
    (hinf : ∀ k, χ.inf k ∈ G) (P : HeightOneSpectrum (𝓞 E)) (x : Eˣ) : χ.locK P x ∈ G := by
  classical
  choose m hm using GlobalTheory.Mem.UnrAe.exists_levelLe χ

  have key : ∀ a : 𝓞 E, a ≠ 0 → ∀ k : Eˣ, (k : E) = (a : E) → χ.locK P k ∈ G := by
    intro a ha k hk

    obtain ⟨y, hy⟩ := exists_approx (insert P T) (fun v => if v = P then a else 1) m
      (fun v => by by_cases h : v = P <;> simp [h, ha])
    have hyP : P.valuation E ((y : E) - (a : E)) ≤ WithZero.exp (-((m P : ℤ) + 1)) * P.valuation E (a : E) := by
      simpa using hy P (Finset.mem_insert_self P T)
    have hva : P.valuation E (a : E) ≠ 0 := by
      rw [(P.valuation E).ne_zero_iff]
      intro h0
      exact ha (RingOfIntegers.ext (by rw [h0]; rfl))
    have hy0 : (y : E) ≠ 0 := by
      intro h0
      rw [h0, zero_sub, Valuation.map_neg] at hyP
      exact absurd hyP (not_le.mpr (exp_neg_succ_mul_lt_self (m P) hva))
    set ky : Eˣ := Units.mk0 (y : E) hy0 with hky
    have hone : ∀ v ∈ insert P T, v ≠ P → χ.locK v ky = 1 := by
      intro v hv hvP
      have h1 : v.valuation E ((ky : E) - ((1 : Eˣ) : E)) ≤
          WithZero.exp (-((m v : ℤ) + 1)) * v.valuation E ((1 : Eˣ) : E) := by
        simpa [hvP, hky] using hy v hv
      rw [locK_eq_of_level χ (hm v) 1 ky h1, map_one]
    have hPk : χ.locK P ky = χ.locK P k := by
      apply locK_eq_of_level χ (hm P) k ky
      simpa [hky, hk] using hyP

    have hS : ∀ v, v ∉ insert P T → χ.UnrAt v := fun v hv => hunr v (fun h => hv (Finset.mem_insert_of_mem h))
    have hPR := GlobalTheory.TypeValues.productRule χ (insert P T) hS ky
    rw [Finset.prod_eq_single_of_mem P (Finset.mem_insert_self P T) hone] at hPR
    have hF : (∏ᶠ (v : HeightOneSpectrum (𝓞 E)) (_ : v ∉ insert P T), χ.val v ^ ordF v ky) ∈ G :=
      finprod_induction (· ∈ G) G.one_mem (fun _ _ => G.mul_mem) fun v =>
        finprod_induction (· ∈ G) G.one_mem (fun _ _ => G.mul_mem) fun hv =>
          G.zpow_mem (hval v fun h => hv (Finset.mem_insert_of_mem h)) _
    have h1 := G.one_mem
    rw [← hPR] at h1
    rw [← hPk]
    exact (G.mul_mem_cancel_left (hinf ky)).mp ((G.mul_mem_cancel_right hF).mp h1)

  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (𝓞 E) (x : E)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hinj : Function.Injective (algebraMap (𝓞 E) E) := IsFractionRing.injective (𝓞 E) E
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hab
    exact x.ne_zero hab.symm
  have haE : algebraMap (𝓞 E) E a ≠ 0 := (map_ne_zero_iff _ hinj).mpr ha0
  have hbE : algebraMap (𝓞 E) E b ≠ 0 := (map_ne_zero_iff _ hinj).mpr hb0
  have hx : x = Units.mk0 _ haE * (Units.mk0 _ hbE)⁻¹ := by
    ext
    rw [← hab, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_mk0, div_eq_mul_inv]
  rw [hx, map_mul, map_inv]
  exact G.mul_mem (key a ha0 _ rfl) (G.inv_mem (key b hb0 _ rfl))

end General

theorem main : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (n : ℕ) (L : Type) [Field L] (σ : L →+* ℂ), ChrEq c χ → 0 < n → χ.OrderDvd n → χ.ValuesIn 0 σ → ∀ x : (AE D)ˣ, ∃ y : Lˣ, σ y = (c x : ℂ) := by
  intro D c χ n L _ σ hc hn ho hv x
  classical
  have hfin := GlobalTheory.Mem.UnrAe.finite_ramified χ
  have hunr : ∀ v, v ∉ hfin.toFinset → χ.UnrAt v := fun v hv => by
    by_contra h
    exact hv (hfin.mem_toFinset.mpr h)
  have hval : ∀ v, v ∉ hfin.toFinset → χ.val v ∈ GlobalTheory.TameVal.unitsIn σ.fieldRange := by
    intro v hv'
    obtain ⟨y, hy⟩ := hv v (hunr v hv')
    have hw : χ.valTw 0 v = ((χ.val v : ℂˣ) : ℂ) := by simp [HChar.valTw]
    exact RingHom.mem_fieldRange.mpr ⟨y, hy.trans hw⟩
  have hinf : ∀ k, χ.inf k ∈ GlobalTheory.TameVal.unitsIn σ.fieldRange := fun k => by
    rw [GlobalTheory.TypeValues.inf_eq_one χ hn ho k]
    exact Subgroup.one_mem _
  have hM : ∀ P k, ((χ.locK P k : ℂˣ) : ℂ) ∈ σ.fieldRange := fun P k =>
    locK_mem χ (GlobalTheory.TameVal.unitsIn σ.fieldRange) hfin.toFinset hunr hval hinf P k
  obtain ⟨y, hy⟩ := RingHom.mem_fieldRange.mp (GlobalTheory.TwistValues.char_mem c χ hc hn ho σ.fieldRange hM x)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy
    exact Circle.coe_ne_zero _ hy.symm
  exact ⟨Units.mk0 y hy0, hy⟩

end GlobalTheory.CompanionTheory.CharValues

end

end

end HeckeCharacterValueBounds
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio
theorem _root_.GlobalTheory.Adopt.heckeCharacter_finiteOrder_values_in_field : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (n : ℕ) (L : Type) [Field L] (σ : L →+* ℂ), ChrEq c χ → 0 < n → χ.OrderDvd n → χ.ValuesIn 0 σ → ∀ x : (AE D)ˣ, ∃ y : Lˣ, σ y = (c x : ℂ) := by
  intro D c χ n L _ σ h₁ h₂ h₃ h₄ x
  exact HeckeCharacterValueBounds.GlobalTheory.CompanionTheory.CharValues.main D c χ n L σ h₁ h₂ h₃ h₄ x

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRadicalSpanGMul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypePrimesRadical

theorem isRadical_span_g_mul : ∀ (D : D7),
    (Ideal.span {((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E)}).IsRadical := by
  intro D
  have hrad : ∀ i : Fin 2, (Ideal.span {((D.host.g i : ℕ) : 𝓞 D.host.E)}).IsRadical := fun i =>
    GlobalTheory.SplitRadical.isRadical_span_of_ncard_primesOver D.host.E (D.host.g i) (D.host.g_prime i)
      ((Formalism.MainNotions.Inhab.primesOver_ncard D.host.E (D.host.g i) (D.host.g_prime i)).trans (D.nd.g_split i))
  have hcop : Nat.Coprime (D.host.g 0) (D.host.g 1) :=
    (Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne
  have hsup : Ideal.span {((D.host.g 0 : ℕ) : 𝓞 D.host.E)} ⊔ Ideal.span {((D.host.g 1 : ℕ) : 𝓞 D.host.E)} = ⊤ := by
    have h1 : IsCoprime ((D.host.g 0 : ℕ) : 𝓞 D.host.E) ((D.host.g 1 : ℕ) : 𝓞 D.host.E) := by
      have h2 := (Nat.isCoprime_iff_coprime.2 hcop).map (Int.castRingHom (𝓞 D.host.E))
      simpa using h2
    exact Ideal.isCoprime_iff_sup_eq.1 ((Ideal.isCoprime_span_singleton_iff _ _).2 h1)
  rw [Nat.cast_mul, ← Ideal.span_singleton_mul_span_singleton, Ideal.mul_eq_inf_of_coprime hsup]
  exact (hrad 0).inf (hrad 1)

end GlobalTheory.TypePrimesRadical
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceCoverProd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TypeProductCover

theorem star_eq_conj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  apply D.host.φ₀.injective
  have := D.host.isCMField_hostE
  exact (IsCMField.complexEmbedding_complexConj _ D.host.φ₀ x).trans
    (D.host.conjE_apply D.host.φ₀ x).symm

theorem lev_of_isConjPl (D : D7) {P P' : Formalism.L2.DIV.Pl D.host.E} (h : Formalism.BasicNotions.IsConjPl D.host P P') :
    Formalism.IndefR.Lev.IsConjPl P P' := fun c hc =>
  ⟨RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E) c,
    (h c _ rfl).1 hc, by
      show D.host.conj (c : D.host.E) = star (c : D.host.E)
      rw [star_eq_conj]⟩

theorem place_cover_prod : ∀ (D : D7) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ ↥Pg),
    (∀ kv, ((plg kv : ↥Pg) : Formalism.L2.DIV.Pl D.host.E) = D.naut.plGw kv.1 kv.2) →
    ∀ PP : Formalism.L2.DIV.Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal →
      PP ∈ Pg ∨ ∃ PP' ∈ Pg, Formalism.IndefR.Lev.IsConjPl PP' PP := by
  intro D Pg plg hplg PP hPP
  have hmul : ((D.host.g 0 : ℕ) : 𝓞 D.host.E) * ((D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    rw [← Nat.cast_mul]; exact hPP
  have hk : ∃ k : Fin 2, PP ∈ placesOver D.host.E (D.host.g k) := by
    rcases PP.isPrime.mem_or_mem hmul with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨k, hk⟩ := hk
  obtain ⟨v, hv | hv⟩ := GlobalTheory.TypePlaceCover.place_cover D k PP hk
  · left
    rw [hv, ← hplg ⟨k, v⟩]
    exact (plg ⟨k, v⟩).2
  · right
    refine ⟨(plg ⟨k, v⟩ : Formalism.L2.DIV.Pl D.host.E), (plg ⟨k, v⟩).2, ?_⟩
    rw [hplg ⟨k, v⟩]
    exact lev_of_isConjPl D hv

end GlobalTheory.TypeProductCover
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralDefiniteSourceConvergesContinuousIn
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralDefiniteSourceConvergesContinuousIn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio

namespace GlobalTheory.DefSourceInt

theorem theta_integral_source_definite : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ε : Bool) (S W : HSp D) (χS χW : (AE D)ˣ →* Circle) (ω : WRep S W) (μ : Measure (GA D S)) (𝓕 : Set (GA D S)) (f : WO S W → ℂ), IsWeil ψ ε S W χS χW ω → (∀ τ, (gramAt D S τ).PosDef) → μ.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 μ → IsThetaFunO ψ (sgn ε S) W f → (∀ h, IntegrableOn (fun g => thetaKO ω g h f) 𝓕 μ) ∧ (Continuous fun h => ∫ g in 𝓕, thetaKO ω g h f ∂μ) ∧ ∀ γ ∈ GQ W, ∀ h, ∫ g in 𝓕, thetaKO ω g (γ * h) f ∂μ = ∫ g in 𝓕, thetaKO ω g h f ∂μ := by
  intro D ψ ε S W χS χW ω μ 𝓕 f hω hpos hμ h𝓕 hf
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact S hpos
  obtain ⟨hcont, hinv⟩ := GlobalTheory.thetaKO_continuous_and_rat_invariant ψ (sgn ε S) W χS χW (WRep.toSgn ε ω) hω f hf
  have hK : ∀ g h, thetaKO ω g h f = thetaKO (WRep.toSgn ε ω) ((ofSgn ε S).symm g) h f := fun _ _ => rfl
  have hKc : Continuous fun p : GA D S × GA D W => thetaKO ω p.1 p.2 f :=
    (hcont.comp (((continuous_ofSgn_symm ε S).comp continuous_fst).prodMk continuous_snd)).congr fun p => (hK p.1 p.2).symm
  have hI : ∀ γ ∈ GQ S, ∀ γ' ∈ GQ W, ∀ g h, thetaKO ω (γ * g) (γ' * h) f = thetaKO ω g h f := by
    intro γ hγ γ' hγ' g h
    rw [hK, hK, map_mul]
    exact hinv _ (GlobalTheory.SquareComm.ofSgn_symm_mem_GQ ε hγ) γ' hγ' _ _
  have hIS : ∀ γ ∈ GQ S, ∀ g h, thetaKO ω (γ * g) h f = thetaKO ω g h f := fun γ hγ g h => by
    have := hI γ hγ 1 (one_mem _) g h
    rwa [one_mul] at this
  have hIW : ∀ γ ∈ GQ W, ∀ g h, thetaKO ω g (γ * h) f = thetaKO ω g h f := fun γ hγ g h => by
    have := hI 1 (one_mem _) γ hγ g h
    rwa [one_mul] at this
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D S
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  refine ⟨fun h => ?_, ?_, fun γ hγ h => ?_⟩
  · exact GlobalTheory.CocompactIntegrable.integrableOn_fundamentalDomain S μ 𝓕 C hμ h𝓕 hC hcov _
      (hKc.comp (Continuous.prodMk_left h)) (fun γ hγ g => hIS γ hγ g h)
  · exact GlobalTheory.DefLiftCont.continuous_integral_of_cocompact (GQ S) μ 𝓕 C h𝓕 hC hcov
      (fun h g => thetaKO ω g h f) (hKc.comp continuous_swap) (fun γ hγ h g => hIS γ hγ g h)
  · have e : (fun g => thetaKO ω g (γ * h) f) = fun g => thetaKO ω g h f := funext fun g => hIW γ hγ g h
    exact congrArg (fun F : GA D S → ℂ => ∫ g in 𝓕, F g ∂μ) e

end GlobalTheory.DefSourceInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralDefiniteSourceConvergesContinuousInStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaIntegral_definiteSource_converges_continuous_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ε : Bool) (S W : HSp D) (χS χW : (AE D)ˣ →* Circle) (ω : WRep S W) (μ : Measure (GA D S)) (𝓕 : Set (GA D S)) (f : WO S W → ℂ), IsWeil ψ ε S W χS χW ω → (∀ τ, (gramAt D S τ).PosDef) → μ.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 μ → IsThetaFunO ψ (sgn ε S) W f → (∀ h, IntegrableOn (fun g => thetaKO ω g h f) 𝓕 μ) ∧ (Continuous fun h => ∫ g in 𝓕, thetaKO ω g h f ∂μ) ∧ ∀ γ ∈ GQ W, ∀ h, ∫ g in 𝓕, thetaKO ω g (γ * h) f ∂μ = ∫ g in 𝓕, thetaKO ω g h f ∂μ := by
  first | exact @GlobalTheory.DefSourceInt.theta_integral_source_definite | exact GlobalTheory.DefSourceInt.theta_integral_source_definite | (intros; apply GlobalTheory.DefSourceInt.theta_integral_source_definite <;> assumption)
end
end
