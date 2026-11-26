module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlCSurjectiveAndLinearIndependentBLie
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankZetaSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicChartSmooth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeImageBirationalLinearSystemEqSelfInt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneZeroInsertionLinearApply
noncomputable section

namespace GlobalTheory.ThK.PlaneEv

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {n d d₁ : ℕ}

def idx (hd : d = d₁ + 2) : Fin n × Fin d ≃ Fin n × Fin d₁ ⊕ Fin n × Fin 2 :=
  ((Equiv.refl (Fin n)).prodCongr ((finCongr hd).trans finSumFinEquiv.symm)).trans (Equiv.prodSumDistrib _ _ _)

def ins0 {R : Type} [Zero R] (hd : d = d₁ + 2) (x : Fin n × Fin d₁ → R) : Fin n × Fin d → R :=
  fun k => Sum.elim x 0 (idx hd k)

section Ins

variable {R : Type} (hd : d = d₁ + 2)

@[simp] theorem planeZeroInsertion_apply_inl [Zero R] (x : Fin n × Fin d₁ → R) (p : Fin n × Fin d₁) :
    ins0 hd x ((idx hd).symm (Sum.inl p)) = x p := by
  simp [ins0]

@[simp] theorem planeZeroInsertion_apply_inr [Zero R] (x : Fin n × Fin d₁ → R) (p : Fin n × Fin 2) :
    ins0 hd x ((idx hd).symm (Sum.inr p)) = 0 := by
  simp [ins0]

theorem ins0_zero [Zero R] : ins0 hd (0 : Fin n × Fin d₁ → R) = 0 := by
  funext k; simp only [ins0]; rcases idx hd k with p | p <;> rfl

theorem ins0_add [AddZeroClass R] (x y : Fin n × Fin d₁ → R) : ins0 hd (x + y) = ins0 hd x + ins0 hd y := by
  funext k; simp only [ins0, Pi.add_apply]; rcases idx hd k with p | p <;> simp

theorem ins0_smul {S : Type} [Zero R] [SMulZeroClass S R] (c : S) (x : Fin n × Fin d₁ → R) :
    ins0 hd (c • x) = c • ins0 hd x := by
  funext k; simp only [ins0, Pi.smul_apply]; rcases idx hd k with p | p <;> simp

theorem ins0_map {R' : Type} [Zero R] [Zero R'] (g : R → R') (hg : g 0 = 0) (x : Fin n × Fin d₁ → R) :
    (fun k => g (ins0 hd x k)) = ins0 hd (fun p => g (x p)) := by
  funext k; simp only [ins0]; rcases idx hd k with p | p <;> simp [hg]

theorem ins0_dotProduct [NonUnitalNonAssocSemiring R] (x : Fin n × Fin d₁ → R) (b : Fin n × Fin d → R) :
    ins0 hd x ⬝ᵥ b = x ⬝ᵥ fun p => b ((idx hd).symm (Sum.inl p)) := by
  simp only [dotProduct]
  rw [← (idx hd).symm.sum_comp, Fintype.sum_sum_type]
  simp

theorem ins0_dotProduct_ins0 [NonUnitalNonAssocSemiring R] (x y : Fin n × Fin d₁ → R) :
    ins0 hd x ⬝ᵥ ins0 hd y = x ⬝ᵥ y := by
  rw [ins0_dotProduct]; simp

end Ins

open scoped Classical

variable (F : Type) [Field F] [NumberField F]

def insertZerosCLM (hd : d = d₁ + 2) :
    (Fin n × Fin d₁ → mixedEmbedding.mixedSpace F) →L[ℝ] (Fin n × Fin d → mixedEmbedding.mixedSpace F) :=
  LinearMap.toContinuousLinearMap
    { toFun := ins0 hd
      map_add' := ins0_add hd
      map_smul' := fun c x => ins0_smul hd c x }

@[simp] theorem planeZeroInsertionLinear_apply (hd : d = d₁ + 2) (x : Fin n × Fin d₁ → mixedEmbedding.mixedSpace F) :
    insertZerosCLM F hd x = ins0 hd x := rfl

theorem norm_le_ins0 (hd : d = d₁ + 2) (x : Fin n × Fin d₁ → mixedEmbedding.mixedSpace F) : ‖x‖ ≤ ‖ins0 hd x‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun p => ?_
  have := norm_le_pi_norm (ins0 hd x) ((idx hd).symm (Sum.inl p))
  rwa [planeZeroInsertion_apply_inl] at this

def ei (hd : d = d₁ + 2) : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d₁) :=
  SchwartzMap.compCLM ℂ (insertZerosCLM F hd).hasTemperateGrowth
    ⟨1, 1, fun x => by
      have := norm_le_ins0 F hd x
      simp only [planeZeroInsertionLinear_apply, pow_one, one_mul]
      linarith [norm_nonneg (ins0 hd x)]⟩

@[simp] theorem ei_apply (hd : d = d₁ + 2) (f : SInf F (Fin n × Fin d)) (x : Fin n × Fin d₁ → mixedEmbedding.mixedSpace F) :
    ei F hd f x = f (ins0 hd x) := rfl

variable {F}

def ev (hd : d = d₁ + 2) (v : Pl F) : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d₁ → Fv F v) → ℂ :=
  LinearMap.funLeft ℂ ℂ (ins0 hd)

@[simp] theorem ev_apply (hd : d = d₁ + 2) (v : Pl F) (φ : (Fin n × Fin d → Fv F v) → ℂ) (x : Fin n × Fin d₁ → Fv F v) :
    ev hd v φ x = φ (ins0 hd x) := rfl


variable (F) in
def evA (hd : d = d₁ + 2) : Fn F n d →ₗ[ℂ] Fn F n d₁ := LinearMap.funLeft ℂ ℂ (ins0 hd)

@[simp] theorem evA_apply (hd : d = d₁ + 2) (Φ : Fn F n d) (x : Fin n × Fin d₁ → AF F) : evA F hd Φ x = Φ (ins0 hd x) := rfl

theorem ei_ne_zero (hd : d = d₁ + 2) : ei (n := n) F hd ≠ 0 := by
  classical
  intro h
  let b : ContDiffBump (0 : Fin n × Fin d → mixedEmbedding.mixedSpace F) := ⟨1, 2, one_pos, one_lt_two⟩
  have hs : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) := b.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun x => ((b x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp b.contDiff
  have h1 := congrArg (fun T : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d₁) => T (hs.toSchwartzMap hc) 0) h
  have h2 : b 0 = 1 := b.one_of_mem_closedBall (by simp [b])
  simp [ins0_zero, h2] at h1

theorem evA_pure (hd : d = d₁ + 2) (f : SInf F (Fin n × Fin d)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) :
    evA F hd (pure f φ) = pure (ei F hd f) fun v => ev hd v (φ v) := by
  funext x
  simp only [evA_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, ei_apply, ev_apply]
  rw [ins0_map hd (evI F) (by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : AF F).1 = 0
    rw [show (0 : AF F).1 = 0 from rfl, map_zero])]
  congr 1
  congr 1
  funext v
  rw [ins0_map hd (evFin F v) (map_zero _)]

end GlobalTheory.ThK.PlaneEv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfDualDataTransvectionPrincipalLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfDualDataTransvectionPrincipalLevel
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.LevGeo

theorem gam_keeps_L' {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r)
    (A : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hA : A ≠ 0)
    (hΛ : X.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ A, ∃ u ∈ X.L', v = a • u}) :
    ∀ γ ∈ X.Γ, ∀ v ∈ X.L', (γ : Matrix (Fin r) (Fin r) E).mulVec v ∈ X.L' := by
  have hinv : A⁻¹ * A = 1 := inv_mul_cancel₀ hA
  have hA1 : ∀ b ∈ A⁻¹, ∀ x ∈ X.Λ, b • x ∈ X.L' := by
    intro b hb x hx
    rw [hΛ] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, u, hu, rfl⟩ := hx
      have hm : b * a ∈ A⁻¹ * A := FractionalIdeal.mul_mem_mul hb ha
      rw [hinv, FractionalIdeal.mem_one_iff] at hm
      obtain ⟨z, hz⟩ := hm
      rw [smul_smul, ← hz, algebraMap_smul]
      exact X.L'.smul_mem z hu
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul c x _ hx => rw [smul_comm]; exact X.L'.smul_mem c hx
  intro γ hγ v hv
  have key : ∀ y ∈ ((A⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) *
      (A : Submodule (𝓞 E) E), (γ : Matrix (Fin r) (Fin r) E).mulVec (y • v) ∈ X.L' := by
    intro y hy
    refine Submodule.mul_induction_on hy (fun b hb a ha => ?_) (fun y1 y2 h1 h2 => ?_)
    · have hav : a • v ∈ X.Λ := by
        rw [hΛ]; exact Submodule.subset_span ⟨a, ha, v, hv, rfl⟩
      have h1 := ((X.Γ_stab γ hγ).2 (a • v)).1 hav
      rw [mul_smul, Matrix.mulVec_smul]
      exact hA1 b hb _ h1
    · rw [add_smul, Matrix.mulVec_add]; exact add_mem h1 h2
  have h1 : (1 : E) ∈ ((A⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) *
      (A : Submodule (𝓞 E) E) := by
    rw [← FractionalIdeal.coe_mul, hinv]
    exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩
  have := key 1 h1
  rwa [one_smul] at this

theorem level_mul_two_div (m n d : ℝ) (hn : 0 < n) (hd : 0 < d) :
    m * (n * d) * (2 * (1 / (n * Real.sqrt d))) = 2 * m * Real.sqrt d := by
  have key : ∀ s : ℝ, 0 < s → s * s = d → m * (n * d) * (2 * (1 / (n * s))) = 2 * m * s := by
    intro s hs hss
    subst hss
    field_simp
  exact key _ (Real.sqrt_pos.2 hd) (Real.mul_self_sqrt hd.le)

theorem exists_dataX_transv : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ k : (U σ).Comp, ∃ Xx : DataX D.host.E D.R.r, Xx.toData = (U σ).X k ∧ Xx.g = l.M ∧ Xx.Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ D.host.AA, ∃ u ∈ Xx.L', v = a • u} ∧ (∀ γ ∈ Xx.Γ, ∀ v ∈ Xx.L', (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v ∈ Xx.L') ∧ ∃ M : ℝ, 0 < M ∧ M * Xx.k0 = 2 * l.M * Real.sqrt D.host.d ∧ ∀ v ∈ Xx.L', herm Xx.Gm v v = 0 → ∀ b : D.host.E, cc b = b → IsIntegral ℤ b → ∃ γ ∈ Xx.Γ, ∀ τ : Xx.Ψ, (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 = Xx.flowMat v τ ((M : ℂ) * τ.1 b) := by
  intro D j H Dw l Xo c U dict h σ hσ k
  have hP := GlobalTheory.T.principalLevel_arithmeticGroups_contain_congruence D j H Dw l Xo c U dict h σ hσ
  have hN : 0 < Ideal.absNorm D.host.ccK :=
    Nat.pos_of_ne_zero fun h0 => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have hd : 0 < D.host.d := by have := D.host.qd_big.2; omega
  have hN' : (0 : ℝ) < Ideal.absNorm D.host.ccK := by exact_mod_cast hN
  have hd' : (0 : ℝ) < D.host.d := by exact_mod_cast hd
  have hs := Real.sqrt_pos.2 hd'
  have hx1 : xiR D ≤ 1 := by
    rw [GlobalTheory.TransvModel.xiR_eq]
    have h1 : (1 : ℝ) ≤ Ideal.absNorm D.host.ccK := by exact_mod_cast hN
    have h2 : (1 : ℝ) ≤ Real.sqrt D.host.d := by
      rw [Real.one_le_sqrt]; exact_mod_cast hd
    rw [div_le_one (by positivity)]
    nlinarith
  have habs := h.xiAbs σ hσ k
  have hperf := GlobalTheory.traceForm_integral_perfect_of_isUnf _ _ _ _ _ _ σ _ (Formalism.L2.PjFree.Unf.ofPj (U σ))
    ((Formalism.L2.PjFree.isUnf_ofPj _).2 (h.unf σ hσ)) k
  have hξ := GlobalTheory.eq_or_eq_neg_of_purelyImaginary_of_norm_eq _ D.host.xi0 ((U σ).X k).ξ0 D.host.φ₀
    (GlobalTheory.LatticeData.flagDomainConj_hostXi_eq_neg D) ((U σ).X k).ξ0_im (habs _).symm
  have hone : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) ((U σ).X k).ξ0 * D.host.AA *
      D.host.AAbar * (differentIdeal ℤ (𝓞 D.host.E) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) = 1 := by
    have h1 := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
    rcases hξ with e | e
    · rw [e]; exact h1
    · rw [e, show -D.host.xi0 = (-1 : (𝓞 D.host.E)ˣ) • D.host.xi0 by simp,
        ← (FractionalIdeal.spanSingleton_eq_spanSingleton.2 ⟨-1, rfl⟩)]
      exact h1
  have hA : D.host.AA ≠ 0 := by
    intro e
    rw [e] at hone
    simp at hone
  have hM : 0 < l.M := by have := l.three_le; omega
  obtain ⟨Xx, h1, h2, h3⟩ := GlobalTheory.exists_dataX_of_perfect_traceForm _ _ ((U σ).X k) D.host.AA D.host.AAbar
    (xiR D) l.M
    (fun a => by
      rw [GlobalTheory.LatticeData.cc_eq_conj]
      exact ⟨conj_mem_AA D, fun ha => by simpa only [conj_conj] using conj_mem_AAbar D ha⟩)
    hone habs hx1 hperf.1 hperf.2 hM (hP k)
  let Xy : DataX D.host.E D.R.r := { Xx with
    k0 := 2 * xiR D
    minWeight_pos := by have := GlobalTheory.TransvModel.xiR_eq D; rw [this]; positivity
    k0_le := by linarith
    ξ0_abs := fun τ => by rw [show Xx.ξ0 = ((U σ).X k).ξ0 from congrArg _ h1, habs]; ring }
  have hΛ : Xy.Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ D.host.AA, ∃ u ∈ Xy.L', v = a • u} := h3
  have hX0 : Xy.toData = (U σ).X k := h1
  have habs' : ∀ τ : D.host.E →+* ℂ,
      ‖τ Xy.ξ0‖ = 1 / ((Ideal.absNorm D.host.ccK : ℝ) * Real.sqrt D.host.d) := fun τ => by
    rw [← GlobalTheory.TransvModel.xiR_eq, ← habs τ, ← hX0]
  refine ⟨Xy, h1, h2, h3, gam_keeps_L' Xy _ hA hΛ, ((l.M * (Ideal.absNorm D.host.ccK * D.host.d) : ℕ) : ℝ),
    by positivity, ?_, fun v hv hiso b hb hbi => ?_⟩
  · change _ * (2 * xiR D) = _
    rw [GlobalTheory.TransvModel.xiR_eq]
    push_cast
    exact level_mul_two_div _ _ _ hN' hd'
  · have := GlobalTheory.TransvModel.transv_mem_of_span Xy (D.host.AA : Set D.host.E) hΛ (Ideal.absNorm D.host.ccK * D.host.d)
      (GlobalTheory.TransvModel.isIntegral_level_mul_kappa Xy.toData hN hd D.host.φ₀ (habs' _)) v hv hiso b hb hbi
    have hg : Xy.g = l.M := h2
    rwa [hg] at this

end GlobalTheory.LevGeo
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfDualDataTransvectionPrincipalLevelStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_selfDual_data_transvection_principal_level : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ k : (U σ).Comp, ∃ Xx : DataX D.host.E D.R.r, Xx.toData = (U σ).X k ∧ Xx.g = l.M ∧ Xx.Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ D.host.AA, ∃ u ∈ Xx.L', v = a • u} ∧ (∀ γ ∈ Xx.Γ, ∀ v ∈ Xx.L', (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v ∈ Xx.L') ∧ ∃ M : ℝ, 0 < M ∧ M * Xx.k0 = 2 * l.M * Real.sqrt D.host.d ∧ ∀ v ∈ Xx.L', herm Xx.Gm v v = 0 → ∀ b : D.host.E, cc b = b → IsIntegral ℤ b → ∃ γ ∈ Xx.Γ, ∀ τ : Xx.Ψ, (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 = Xx.flowMat v τ ((M : ℂ) * τ.1 b) := by
  first | exact @GlobalTheory.LevGeo.exists_dataX_transv | exact GlobalTheory.LevGeo.exists_dataX_transv | (intros; apply GlobalTheory.LevGeo.exists_dataX_transv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankCoinvariantInducedIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankZetaSurjectiveStatement
open MeasureTheory GlobalTheory.SplitFlip
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.full_rank_zeta_surjective : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d → GlobalTheory.SmGL.IsSmoothChar ν →
    ∀ f ∈ GlobalTheory.FullRankCoinv.indSp k n d ν,
    ∃ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∀ h : GL (Fin d) k,
      smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ (GlobalTheory.FullRankCoinv.Y0 k n d * h.val) = f h := by
  first | exact @GlobalTheory.FullRankOnto.exists_fullRk_smallF_eq | exact GlobalTheory.FullRankOnto.exists_fullRk_smallF_eq | (intros; apply GlobalTheory.FullRankOnto.exists_fullRk_smallF_eq <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankCoinvariantInducedIso
noncomputable section

open MeasureTheory GlobalTheory.SplitFlip
open scoped Topology Matrix

namespace GlobalTheory.FullRankCoinv

theorem sb_right_invariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n d : ℕ) (Ψ : Matrix (Fin n) (Fin d) k → ℂ), Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) →
    ∃ U ∈ nhds (1 : GL (Fin d) k), ∀ u ∈ U, ∀ X : Matrix (Fin n) (Fin d) k, Ψ (X * u.val) = Ψ X := by
  intro k _ _ _ _ n d Ψ hΨ
  have h1 : ∀ᶠ u in 𝓝 (1 : GL (Fin d) k), ∀ X ∈ tsupport Ψ, Ψ (X * u.val) = Ψ X := by
    refine IsCompact.eventually_forall_of_forall_eventually hΨ.2 fun y _ => ?_
    have h2 : IsLocallyConstant fun q : GL (Fin d) k × Matrix (Fin n) (Fin d) k => (Ψ (q.2 * q.1.val), Ψ q.2) :=
      (hΨ.1.comp_continuous (by fun_prop)).prodMk (hΨ.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (1, y)] with q hq
    simp only [Prod.mk.injEq, Units.val_one, Matrix.mul_one] at hq
    rw [hq.1, hq.2]
  have h3 : ∀ᶠ u in 𝓝 (1 : GL (Fin d) k), ∀ X ∈ tsupport Ψ, Ψ (X * (u⁻¹).val) = Ψ X := by
    have ht : Filter.Tendsto (fun u : GL (Fin d) k => u⁻¹) (𝓝 1) (𝓝 1) := by
      simpa using (continuous_inv.tendsto (1 : GL (Fin d) k))
    exact ht.eventually h1
  refine ⟨_, h1.and h3, fun u hu X => ?_⟩
  by_cases hX : X ∈ tsupport Ψ
  · exact hu.1 X hX
  by_cases hX' : X * u.val ∈ tsupport Ψ
  · have := hu.2 _ hX'
    rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hX, image_eq_zero_of_notMem_tsupport hX']

theorem fibre_coinvariants : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d → GlobalTheory.SmGL.IsSmoothChar ν →
    ∃ Z : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] (GL (Fin d) k → ℂ),
      (∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, Z Ψ ∈ GlobalTheory.FullRankCoinv.indSp k n d ν) ∧
      (∀ f ∈ GlobalTheory.FullRankCoinv.indSp k n d ν, ∃ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, Z Ψ = f) ∧
      (∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, Z Ψ = 0 → Ψ ∈ GlobalTheory.FullRankCoinv.augRk n d ν) ∧
      ∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∀ h₀ : GL (Fin d) k,
        Z (fun Y => Ψ (Y * h₀.1)) = fun h => Z Ψ (h * h₀) := by
  intro k _ _ _ _ n d ν hnd hν
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  let Z₀ : fullRk k n d →ₗ[ℂ] (GL (Fin d) k → ℂ) :=
    { toFun := fun Ψ h => smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ.1 (Y0 k n d * h.val)
      map_add' := fun Ψ Φ => by
        funext h
        simp only [smallF, Submodule.coe_add, Pi.add_apply]
        rw [← integral_add (GlobalTheory.T.integrable_full_rank_zeta k n d ν hν Ψ.1 Ψ.2 _) (GlobalTheory.T.integrable_full_rank_zeta k n d ν hν Φ.1 Φ.2 _)]
        congr 1; funext g; ring
      map_smul' := fun c Ψ => by
        funext h
        simp only [smallF, SetLike.val_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1; funext g; ring }
  obtain ⟨Z, hZ⟩ := LinearMap.exists_extend Z₀
  have hZΨ : ∀ Ψ (hΨ : Ψ ∈ fullRk k n d),
      Z Ψ = fun h => smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ (Y0 k n d * h.val) :=
    fun Ψ hΨ => LinearMap.congr_fun hZ ⟨Ψ, hΨ⟩
  refine ⟨Z, fun Ψ hΨ => ?_, fun f hf => ?_, fun Ψ hΨ h0 => ?_, fun Ψ hΨ h₀ => ?_⟩
  · rw [hZΨ Ψ hΨ]
    refine ⟨?_, fun b h D hD => ?_⟩
    · obtain ⟨U, hU, hinv⟩ := sb_right_invariant k n d Ψ hΨ.1
      refine ⟨U, hU, fun h u hu => ?_⟩
      simp only [smallF]
      congr 1; funext g
      rw [Units.val_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hinv u hu, Matrix.mul_assoc]
    · have e1 : Y0 k n d * (b * h).val = D.val * (Y0 k n d * h.val) := by
        rw [Units.val_mul, ← Matrix.mul_assoc, hD, Matrix.mul_assoc]
      have key := smallF_mul_left (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ D (Y0 k n d * h.val)
      simp only [Fintype.card_fin] at key
      show smallF _ ν Ψ (Y0 k n d * (b * h).val) = _
      rw [e1]
      beta_reduce
      rw [← key, Units.val_inv_eq_inv_val, neg_div, apow_neg]
      have h1 : (ν (gdet D) : ℂ) ≠ 0 := Units.ne_zero _
      have h2 := apow_ne_zero (gdet D) ((d : ℂ) / 2)
      field_simp
  · obtain ⟨Ψ, hΨ, hf'⟩ := GlobalTheory.T.full_rank_zeta_surjective k n d ν hnd hν f hf
    exact ⟨Ψ, hΨ, by rw [hZΨ Ψ hΨ]; funext h; exact hf' h⟩
  · refine GlobalTheory.T.full_rank_zeta_kernel k n d ν hnd hν Ψ hΨ fun h => ?_
    have := congrFun h0 h
    rwa [hZΨ Ψ hΨ] at this
  · have hmem : (fun Y => Ψ (Y * h₀.1)) ∈ fullRk k n d := by
      let e : Matrix (Fin n) (Fin d) k ≃ₜ Matrix (Fin n) (Fin d) k :=
        { toFun := fun X => X * h₀.1
          invFun := fun X => X * (h₀⁻¹).1
          left_inv := fun X => by simp [Matrix.mul_assoc]
          right_inv := fun X => by simp [Matrix.mul_assoc]
          continuous_toFun := by fun_prop
          continuous_invFun := by fun_prop }
      refine ⟨⟨hΨ.1.1.comp_continuous e.continuous, hΨ.1.2.comp_homeomorph e⟩, fun Y hY => hΨ.2 _ ?_⟩
      rwa [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnits_det_units h₀)]
    rw [hZΨ _ hmem, hZΨ _ hΨ]
    funext h
    simp only [smallF, Units.val_mul, Matrix.mul_assoc]

end GlobalTheory.FullRankCoinv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankCoinvariantInducedIsoStatement
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.full_rank_coinvariant_induced_iso : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d → GlobalTheory.SmGL.IsSmoothChar ν →
    ∃ Z : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] (GL (Fin d) k → ℂ),
      (∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, Z Ψ ∈ GlobalTheory.FullRankCoinv.indSp k n d ν) ∧
      (∀ f ∈ GlobalTheory.FullRankCoinv.indSp k n d ν, ∃ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, Z Ψ = f) ∧
      (∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, Z Ψ = 0 → Ψ ∈ GlobalTheory.FullRankCoinv.augRk n d ν) ∧
      ∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∀ h₀ : GL (Fin d) k,
        Z (fun Y => Ψ (Y * h₀.1)) = fun h => Z Ψ (h * h₀) := by
  first | exact @GlobalTheory.FullRankCoinv.fibre_coinvariants | exact GlobalTheory.FullRankCoinv.fibre_coinvariants | (intros; apply GlobalTheory.FullRankCoinv.fibre_coinvariants <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSetArchimedeanNormBound
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.TorusHeight

open scoped Matrix.Norms.L2Operator

theorem opNorm_le_of_shape {n q : ℕ} (X Y' : Matrix (Fin n) (Fin q) ℂ) (Y X' : Matrix (Fin q) (Fin n) ℂ)
    (d d' : Fin q → ℂ) {s : ℝ} (hs : 0 ≤ s) (hd : ∀ i, ‖d i‖ ≤ s) (hd' : ∀ i, ‖d' i‖ ≤ s) :
    (opNorm (1 + X * Matrix.diagonal d * Y + Y' * Matrix.diagonal d' * X') : ℝ) ≤
      1 + (‖X‖ * ‖Y‖ + ‖Y'‖ * ‖X'‖) * s := by
  have e : ∀ M : Matrix (Fin n) (Fin n) ℂ, (opNorm M : ℝ) = ‖M‖ := fun M => by
    rw [opNorm, coe_nnNorm]; exact (Matrix.l2_opNorm_def M).symm
  rw [e]
  have h1 : ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 1 := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun _ => by simp
  have hD : ‖Matrix.diagonal d‖ ≤ s := by
    rw [Matrix.l2_opNorm_diagonal]; exact (pi_norm_le_iff_of_nonneg hs).2 hd
  have hD' : ‖Matrix.diagonal d'‖ ≤ s := by
    rw [Matrix.l2_opNorm_diagonal]; exact (pi_norm_le_iff_of_nonneg hs).2 hd'
  have h2 : ‖X * Matrix.diagonal d * Y‖ ≤ ‖X‖ * s * ‖Y‖ :=
    (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right
      ((Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_left hD (norm_nonneg _))) (norm_nonneg _))
  have h3 : ‖Y' * Matrix.diagonal d' * X'‖ ≤ ‖Y'‖ * s * ‖X'‖ :=
    (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right
      ((Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_left hD' (norm_nonneg _))) (norm_nonneg _))
  calc _ ≤ ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ + ‖X * Matrix.diagonal d * Y‖ + ‖Y' * Matrix.diagonal d' * X'‖ :=
        norm_add₃_le
    _ ≤ 1 + ‖X‖ * s * ‖Y‖ + ‖Y'‖ * s * ‖X'‖ := by linarith
    _ = _ := by ring

theorem le_prod_of_forall_le {q : ℕ} {c : ℝ} (hc : 0 < c) (t : Fin q → ℝ) (ht : ∀ i, c ≤ t i) (k : Fin q) :
    t k * (min 1 c) ^ (q - 1) ≤ ∏ i, t i := by
  have hm : 0 < min 1 c := lt_min one_pos hc
  rw [← Finset.mul_prod_erase Finset.univ t (Finset.mem_univ k)]
  have hk : 0 ≤ t k := hc.le.trans (ht k)
  refine mul_le_mul_of_nonneg_left ?_ hk
  have := Finset.prod_le_prod₀ (s := Finset.univ.erase k) (f := fun _ => min 1 c) (g := t) (fun _ _ => hm.le)
    (fun i _ => (min_le_right _ _).trans (ht i))
  simpa [Finset.prod_const, Finset.card_erase_of_mem, Finset.card_univ, Fintype.card_fin] using this

theorem norm_ofReal_sub_one (x : ℝ) : ‖(x : ℂ) - 1‖ = |x - 1| := by
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

theorem norm_ofReal_inv_sub_one (x : ℝ) : ‖(x : ℂ)⁻¹ - 1‖ = |x⁻¹ - 1| := by
  rw [← Complex.ofReal_inv, norm_ofReal_sub_one]

theorem height_torus_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (q : ℕ) (Xf Yf : Matrix (Fin n) (Fin q) E) (c : ℝ), 0 < c →
    ∃ (C : ℝ) (A : ℕ), ∀ (t : Fin q → ℝ), (∀ i, c ≤ t i) → ∀ a : GAd σ J, a ∈ infPts σ J →
      (∀ (w : InfinitePlace F) (τ : EmbOver E w),
        GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = (1 + (Xf).map τ.1 * Matrix.diagonal (fun i => ((t i : ℝ) : ℂ) - 1) * (Formalism.UG.cT (σ : E →+* E) Yf * J).map τ.1 +
          (Yf).map τ.1 * Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)⁻¹ - 1) * (Formalism.UG.cT (σ : E →+* E) Xf * J).map τ.1) ∧
        GlobalTheory.Orb.archMat σ J τ (projArch σ J w a⁻¹) = (1 + (Xf).map τ.1 * Matrix.diagonal (fun i => (((fun i => (t i)⁻¹) i : ℝ) : ℂ) - 1) * (Formalism.UG.cT (σ : E →+* E) Yf * J).map τ.1 +
          (Yf).map τ.1 * Matrix.diagonal (fun i => (((fun i => (t i)⁻¹) i : ℝ) : ℂ)⁻¹ - 1) * (Formalism.UG.cT (σ : E →+* E) Xf * J).map τ.1)) →
      (height σ J a : ℝ) ≤ C * (1 + ∏ i, t i) ^ A := by
  intro F E _ _ _ _ _ σ hcm n J q Xf Yf c hc
  classical
  have hm : 0 < min 1 c := lt_min one_pos hc
  set c0 : ℝ := ((min 1 c) ^ (q - 1))⁻¹ + c⁻¹ + 1 with hc0
  have hc0' : 1 ≤ c0 := by
    have : 0 ≤ ((min 1 c) ^ (q - 1))⁻¹ := inv_nonneg.2 (pow_nonneg hm.le _)
    have : 0 ≤ c⁻¹ := inv_nonneg.2 hc.le
    linarith
  let τ0 : ∀ w : InfinitePlace F, EmbOver E w := fun w => Classical.arbitrary _
  let K : InfinitePlace F → ℝ := fun w =>
    ‖(Xf).map (τ0 w).1‖ * ‖(Formalism.UG.cT (σ : E →+* E) Yf * J).map (τ0 w).1‖ +
      ‖(Yf).map (τ0 w).1‖ * ‖(Formalism.UG.cT (σ : E →+* E) Xf * J).map (τ0 w).1‖
  have hK : ∀ w, 0 ≤ K w := fun w => by positivity
  refine ⟨∏ w, (1 + K w * c0), Fintype.card (InfinitePlace F), fun t ht a ha hA => ?_⟩
  set P := ∏ i, t i with hP'
  have hP : 0 ≤ P := Finset.prod_nonneg fun i _ => hc.le.trans (ht i)
  have hs : 0 ≤ c0 * (1 + P) := by positivity
  have hs1 : ∀ k, |t k - 1| ≤ c0 * (1 + P) := fun k => by
    have htk : 0 ≤ t k := hc.le.trans (ht k)
    have h1 := le_prod_of_forall_le hc t ht k
    have hpow : 0 < (min 1 c) ^ (q - 1) := pow_pos hm _
    have h2 : t k ≤ ((min 1 c) ^ (q - 1))⁻¹ * P := by
      rw [← div_eq_inv_mul, le_div_iff₀ hpow]; exact h1
    have h3 : |t k - 1| ≤ t k + 1 := by
      rw [abs_le]; constructor <;> linarith
    have h4 : ((min 1 c) ^ (q - 1))⁻¹ * P ≤ c0 * P := by
      apply mul_le_mul_of_nonneg_right _ hP
      have : 0 ≤ c⁻¹ := inv_nonneg.2 hc.le
      linarith
    nlinarith
  have hs2 : ∀ k, |(t k)⁻¹ - 1| ≤ c0 * (1 + P) := fun k => by
    have htk : 0 < t k := hc.trans_le (ht k)
    have h1 : (t k)⁻¹ ≤ c⁻¹ := inv_anti₀ hc (ht k)
    have h0 : 0 ≤ (t k)⁻¹ := inv_nonneg.2 htk.le
    have h3 : |(t k)⁻¹ - 1| ≤ (t k)⁻¹ + 1 := by
      rw [abs_le]; constructor <;> linarith
    have : 0 ≤ ((min 1 c) ^ (q - 1))⁻¹ := inv_nonneg.2 (pow_nonneg hm.le _)
    nlinarith

  have hfin : ∀ v, htFin F v (matHom _ σ J (proj σ J v a)) = 1 := fun v => by
    rw [mem_infPts_iff_forall.1 ha v, map_one]
    exact htOf_eq_one.2 ⟨by simpa using normFin_one_le (E := E) F v, by simpa using normFin_one_le (E := E) F v⟩

  have hinf : ∀ w, (htInf F w (matHom _ σ J (projArch σ J w a)) : ℝ) ≤ (1 + K w * c0) * (1 + P) := by
    intro w
    obtain ⟨h1, h2⟩ := hA w (τ0 w)
    have e1 : normInf F w ((matHom _ σ J (projArch σ J w a) : GL (Fin n) (w.Completion ⊗[F] E)) :
        Matrix (Fin n) (Fin n) (w.Completion ⊗[F] E)) = opNorm (GlobalTheory.Orb.archMat σ J (τ0 w) (projArch σ J w a)) :=
      normInf_eq_opNorm hcm (τ0 w) _
    have e2 : normInf F w (((matHom _ σ J (projArch σ J w a))⁻¹ : GL (Fin n) (w.Completion ⊗[F] E)) :
        Matrix (Fin n) (Fin n) (w.Completion ⊗[F] E)) =
        opNorm (GlobalTheory.Orb.archMat σ J (τ0 w) (projArch σ J w a⁻¹)) := by
      rw [← map_inv, ← map_inv]; exact normInf_eq_opNorm hcm (τ0 w) _
    have B1 : (opNorm (GlobalTheory.Orb.archMat σ J (τ0 w) (projArch σ J w a)) : ℝ) ≤ 1 + K w * (c0 * (1 + P)) := by
      rw [h1]
      refine (opNorm_le_of_shape _ _ _ _ _ _ hs (fun i => ?_) (fun i => ?_)).trans le_rfl
      · rw [norm_ofReal_sub_one]; exact hs1 i
      · rw [norm_ofReal_inv_sub_one]; exact hs2 i
    have B2 : (opNorm (GlobalTheory.Orb.archMat σ J (τ0 w) (projArch σ J w a⁻¹)) : ℝ) ≤ 1 + K w * (c0 * (1 + P)) := by
      rw [h2]
      refine (opNorm_le_of_shape _ _ _ _ _ _ hs (fun i => ?_) (fun i => ?_)).trans le_rfl
      · rw [norm_ofReal_sub_one]; exact hs2 i
      · rw [norm_ofReal_inv_sub_one, inv_inv]; exact hs1 i
    have hfin' : (1 + K w * (c0 * (1 + P))) ≤ (1 + K w * c0) * (1 + P) := by
      have := hK w; nlinarith
    have hone : (1 : ℝ) ≤ (1 + K w * c0) * (1 + P) := by
      have := hK w; nlinarith
    simp only [htInf, htOf, NNReal.coe_max, NNReal.coe_one]
    rw [e1, e2]
    exact max_le hone (max_le (B1.trans hfin') (B2.trans hfin'))
  have hh : (height σ J a : ℝ) = ∏ w, (htInf F w (matHom _ σ J (projArch σ J w a)) : ℝ) := by
    rw [height_eq]
    simp only [hfin, finprod_one, mul_one, NNReal.coe_prod]
  rw [hh]
  calc _ ≤ ∏ w, ((1 + K w * c0) * (1 + P)) :=
        Finset.prod_le_prod₀ (fun _ _ => NNReal.coe_nonneg _) (fun w _ => hinf w)
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

end GlobalTheory.TorusHeight
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormOneMulCompactOfTwistedNormCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormOneMulCompactOfTwistedNormCompact
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.Tw.NormOneCore

theorem exists_normOne_mul_compact : ∀ (K : Type) [NontriviallyNormedField K] [ProperSpace K] [StarRing K], (∀ x : K, ‖star x‖ = ‖x‖) → ∀ (n : ℕ) (δ : Matrix (Fin n) (Fin n) K), GlobalTheory.Tw.Reg δ → ∀ C : Set (GL (Fin n) K), IsCompact C → ∃ D : Set (GL (Fin n) K), IsCompact D ∧ ∀ z : GL (Fin n) K, (z : Matrix (Fin n) (Fin n) K) ∈ Algebra.adjoin K {GlobalTheory.Tw.nrm δ} → ∀ u ∈ C, (u : Matrix (Fin n) (Fin n) K) = (z : Matrix (Fin n) (Fin n) K) * GlobalTheory.Tw.adj δ (z : Matrix (Fin n) (Fin n) K) → ∃ t : GL (Fin n) K, (t : Matrix (Fin n) (Fin n) K) ∈ Algebra.adjoin K {GlobalTheory.Tw.nrm δ} ∧ (t : Matrix (Fin n) (Fin n) K) * GlobalTheory.Tw.adj δ (t : Matrix (Fin n) (Fin n) K) = 1 ∧ ∃ d ∈ D, z = t * d := by
  intro K _ _ _ hK n δ hδ C hC
  have hu := hδ.1
  set N := GlobalTheory.Tw.nrm δ with hNdef
  set A := Algebra.adjoin K {N} with hAdef
  letI : CommRing A := Algebra.instCommRingAdjoinSingleton N
  have hA := GlobalTheory.Tw.CentralizerAdjoin.adj_adjoin hu
  have hmul := GlobalTheory.Tw.CentralizerAdjoin.adj_mul' hu
  have hsemi := GlobalTheory.Tw.CentralizerAdjoin.adj_semi δ
  have hone := GlobalTheory.Tw.CentralizerAdjoin.adj_one' hu
  have hadd : ∀ x y : Matrix (Fin n) (Fin n) K, GlobalTheory.Tw.adj δ (x + y) = GlobalTheory.Tw.adj δ x + GlobalTheory.Tw.adj δ y :=
    fun x y => by simpa using hsemi 1 x y
  have hzero : GlobalTheory.Tw.adj δ 0 = 0 := by simp [GlobalTheory.Tw.adj]
  let σ : A →+* A :=
    { toFun := fun x => ⟨GlobalTheory.Tw.adj δ x, (hA x x.2).1⟩
      map_one' := Subtype.ext hone
      map_mul' := fun x y => by
        apply Subtype.ext
        change GlobalTheory.Tw.adj δ (x.1 * y.1) = _
        rw [hmul]
        simpa only [Subalgebra.coe_mul] using congrArg Subtype.val (mul_comm (⟨_, (hA y y.2).1⟩ : A) ⟨_, (hA x x.2).1⟩)
      map_zero' := Subtype.ext hzero
      map_add' := fun x y => Subtype.ext (hadd x.1 y.1) }
  have hσv : ∀ x : A, (σ x : Matrix (Fin n) (Fin n) K) = GlobalTheory.Tw.adj δ x := fun x => rfl
  have hσσ : ∀ x : A, σ (σ x) = x := fun x => Subtype.ext (hA x x.2).2
  haveI : IsReduced A := ⟨fun x ⟨m, hm⟩ => Subtype.ext
    (GlobalTheory.T.eq_zero_of_pow_eq_zero_of_mem_adjoin_of_charpoly_separable K n N hδ.2 x x.2 m (by simpa using congrArg Subtype.val hm))⟩
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  obtain ⟨e, f, he, hf, hes, hsum, hnull⟩ := GlobalTheory.T.reduced_artinian_involution_idempotent_split A σ hσσ

  have hse : σ e * f = 0 := by
    have h1 : σ e * σ e = σ e := by rw [← map_mul, he.eq]
    have : f = 1 - e - σ e := by rw [← hsum]; ring
    rw [this]; linear_combination (-1 : A) * h1 + (-1 : A) * hes
  have hef : e * f = 0 := by
    have : f = 1 - e - σ e := by rw [← hsum]; ring
    rw [this]; linear_combination -he.eq - hes
  have hσf : σ f = f := by
    have h := congrArg σ hsum
    rw [map_add (f := _), map_add (f := _), hσσ, map_one] at h
    linear_combination h - hsum
  letI : ContinuousStar K := ⟨(Isometry.of_dist_eq fun x y => by
    rw [dist_eq_norm, dist_eq_norm, ← star_sub, hK]).continuous⟩
  have hqc : Continuous fun w : Matrix (Fin n) (Fin n) K => w * GlobalTheory.Tw.adj δ w := by
    unfold GlobalTheory.Tw.adj
    fun_prop
  have hss : σ e * σ e = σ e := by rw [← map_mul, he.eq]
  let S : Submodule K (Matrix (Fin n) (Fin n) K) :=
    Submodule.map (LinearMap.mulRight K (f : Matrix (Fin n) (Fin n) K)) (Subalgebra.toSubmodule A)
  have hhom : ∀ (c : K) (w : Matrix (Fin n) (Fin n) K),
      (c • w) * GlobalTheory.Tw.adj δ (c • w) = (c * star c) • (w * GlobalTheory.Tw.adj δ w) := by
    intro c w
    have : GlobalTheory.Tw.adj δ (c • w) = star c • GlobalTheory.Tw.adj δ w := by simpa [hzero] using hsemi c w 0
    rw [this, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hnullS : ∀ w ∈ S, w * GlobalTheory.Tw.adj δ w = 0 → w = 0 := by
    intro w hw h0
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hw
    have hx : (⟨a, ha⟩ * f : A) * σ (⟨a, ha⟩ * f) = 0 := Subtype.ext h0
    have h1 := hnull _ hx
    rw [mul_assoc, hf.eq] at h1
    exact congrArg Subtype.val h1
  obtain ⟨B1, hB1, hB1m⟩ := GlobalTheory.T.isCompact_preimage_quadratic_map_no_null_vectors K hK n S (fun w => w * GlobalTheory.Tw.adj δ w) hqc hhom hnullS
    ((fun u : GL (Fin n) K => (f : Matrix (Fin n) (Fin n) K) * u) '' C)
    (hC.image (continuous_const.mul Units.continuous_val))
  obtain ⟨B2, hB2, hB2m⟩ := GlobalTheory.T.isCompact_preimage_quadratic_map_no_null_vectors K hK n S (fun w => w * GlobalTheory.Tw.adj δ w) hqc hhom hnullS
    ((fun u : GL (Fin n) K => (f : Matrix (Fin n) (Fin n) K) * ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) '' C)
    (hC.image (continuous_const.mul (Units.continuous_coe_inv (M := Matrix (Fin n) (Fin n) K))))
  let φ : GL (Fin n) K × Matrix (Fin n) (Fin n) K × Matrix (Fin n) (Fin n) K →
      Matrix (Fin n) (Fin n) K × (Matrix (Fin n) (Fin n) K)ᵐᵒᵖ := fun p =>
    ((e : Matrix (Fin n) (Fin n) K) + (σ e : Matrix (Fin n) (Fin n) K) * p.1 + p.2.1,
      MulOpposite.op ((e : Matrix (Fin n) (Fin n) K) + (σ e : Matrix (Fin n) (Fin n) K) * ((p.1⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) + p.2.2))
  have hφ : Continuous φ :=
    ((continuous_const.add (continuous_const.mul (Units.continuous_val.comp continuous_fst))).add
      (continuous_fst.comp continuous_snd)).prodMk
      (MulOpposite.continuous_op.comp ((continuous_const.add
        (continuous_const.mul ((Units.continuous_coe_inv (M := Matrix (Fin n) (Fin n) K)).comp continuous_fst))).add
          (continuous_snd.comp continuous_snd)))
  refine ⟨Units.embedProduct _ ⁻¹' (φ '' (C ×ˢ (B1 ×ˢ B2))),
    Units.isClosedEmbedding_embedProduct.isCompact_preimage ((hC.prod (hB1.prod hB2)).image hφ), ?_⟩
  intro z hz u hu' huz
  have hzi : ((z⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∈ A := by
    rw [Matrix.coe_units_inv]
    exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr hz) (GlobalTheory.Tw.CentralizerAdjoin.inv_mem_adjoin_of_isUnit z.isUnit)
  set z' : A := ⟨z, hz⟩ with hz'
  set zi : A := ⟨_, hzi⟩ with hzi'
  have hz1 : z' * zi = 1 := Subtype.ext (Units.mul_inv z)
  have hsz1 : σ z' * σ zi = 1 := by rw [← map_mul, hz1, map_one]
  set tA : A := e * z' + σ e * σ zi + f with htA
  set tiA : A := e * zi + σ e * σ z' + f with htiA
  have hprod : tA * tiA = 1 := by
    rw [htA, htiA]
    linear_combination (z' * zi) * he.eq + e * hz1 + (z' * σ z' + σ zi * zi) * hes + (z' + zi) * hef +
      (σ zi * σ z') * hss + σ e * hsz1 + (σ zi + σ z') * hse + hf.eq + hsum
  have hprod' : tiA * tA = 1 := by rw [mul_comm]; exact hprod
  have hσt : σ tA = tiA := by
    rw [htA, htiA]; simp only [map_add (f := _), map_mul, hσσ, hσf]; ring
  let t : GL (Fin n) K := ⟨tA, tiA, congrArg Subtype.val hprod, congrArg Subtype.val hprod'⟩
  have hinvu : ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = ((zi * σ zi : A) : Matrix (Fin n) (Fin n) K) := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [huz]
    exact congrArg Subtype.val (show (z' * σ z') * (zi * σ zi) = 1 by
      linear_combination (σ z' * σ zi) * hz1 + hsz1)
  refine ⟨t, tA.2, ?_, t⁻¹ * z, ?_, by simp⟩
  · show (tA : Matrix (Fin n) (Fin n) K) * GlobalTheory.Tw.adj δ tA = 1
    rw [← hσv, hσt]; exact congrArg Subtype.val hprod
  refine ⟨(u, (z : Matrix (Fin n) (Fin n) K) * f, ((z⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * f),
    ⟨hu', hB1m _ (Submodule.mem_map.mpr ⟨z, hz, rfl⟩) ⟨u, hu', ?_⟩,
      hB2m _ (Submodule.mem_map.mpr ⟨_, hzi, rfl⟩) ⟨u, hu', ?_⟩⟩, ?_⟩
  · show (f : Matrix (Fin n) (Fin n) K) * u = ((z' * f : A) : Matrix (Fin n) (Fin n) K) * ((σ (z' * f) : A) : Matrix (Fin n) (Fin n) K)
    rw [huz]
    exact congrArg Subtype.val (show f * (z' * σ z') = (z' * f) * σ (z' * f) by
      rw [map_mul, hσf]; linear_combination (-(z' * σ z')) * hf.eq)
  · show (f : Matrix (Fin n) (Fin n) K) * ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = ((zi * f : A) : Matrix (Fin n) (Fin n) K) * ((σ (zi * f) : A) : Matrix (Fin n) (Fin n) K)
    rw [hinvu]
    exact congrArg Subtype.val (show f * (zi * σ zi) = (zi * f) * σ (zi * f) by
      rw [map_mul, hσf]; linear_combination (-(zi * σ zi)) * hf.eq)
  · apply Prod.ext
    · show (e : Matrix (Fin n) (Fin n) K) + (σ e : Matrix (Fin n) (Fin n) K) * (u : Matrix (Fin n) (Fin n) K) + (z : Matrix (Fin n) (Fin n) K) * f = ((t⁻¹ * z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      rw [huz]
      exact congrArg Subtype.val (show e + σ e * (z' * σ z') + z' * f = tiA * z' by
        rw [htiA]; linear_combination (-e) * hz1)
    · show MulOpposite.op ((e : Matrix (Fin n) (Fin n) K) + (σ e : Matrix (Fin n) (Fin n) K) * ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) + ((z⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * f) = MulOpposite.op (((t⁻¹ * z)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      rw [hinvu, _root_.mul_inv_rev, inv_inv, Units.val_mul]
      exact congrArg MulOpposite.op (congrArg Subtype.val (show e + σ e * (zi * σ zi) + zi * f = zi * tA by
        rw [htA]; linear_combination (-e) * hz1))
end GlobalTheory.Tw.NormOneCore
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormOneMulCompactOfTwistedNormCompactStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normOne_mul_compact_of_twistedNorm_compact : ∀ (K : Type) [NontriviallyNormedField K] [ProperSpace K] [StarRing K], (∀ x : K, ‖star x‖ = ‖x‖) → ∀ (n : ℕ) (δ : Matrix (Fin n) (Fin n) K), GlobalTheory.Tw.Reg δ → ∀ C : Set (GL (Fin n) K), IsCompact C → ∃ D : Set (GL (Fin n) K), IsCompact D ∧ ∀ z : GL (Fin n) K, (z : Matrix (Fin n) (Fin n) K) ∈ Algebra.adjoin K {GlobalTheory.Tw.nrm δ} → ∀ u ∈ C, (u : Matrix (Fin n) (Fin n) K) = (z : Matrix (Fin n) (Fin n) K) * GlobalTheory.Tw.adj δ (z : Matrix (Fin n) (Fin n) K) → ∃ t : GL (Fin n) K, (t : Matrix (Fin n) (Fin n) K) ∈ Algebra.adjoin K {GlobalTheory.Tw.nrm δ} ∧ (t : Matrix (Fin n) (Fin n) K) * GlobalTheory.Tw.adj δ (t : Matrix (Fin n) (Fin n) K) = 1 ∧ ∃ d ∈ D, z = t * d := by
  first | exact @GlobalTheory.Tw.NormOneCore.exists_normOne_mul_compact | exact GlobalTheory.Tw.NormOneCore.exists_normOne_mul_compact | (intros; apply GlobalTheory.Tw.NormOneCore.exists_normOne_mul_compact <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PLocPrjGOfNotMem
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTw.Transport

open GlobalTheory.BCT

variable {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

theorem map_eq_of_mem (e : G ≃ₜ* H) (A : Subgroup G) (A' : Subgroup H) (h : ∀ g, g ∈ A ↔ e g ∈ A') :
    A' = A.map (e : G →* H) := by
  ext y
  constructor
  · intro hy
    refine ⟨e.symm y, (h _).2 (by simpa using hy), by simp⟩
  · rintro ⟨g, hg, rfl⟩
    exact (h g).1 hg

theorem cptPart_map_equiv (e : G ≃ₜ* H) (T : Subgroup G) :
    cptPart (T.map (e : G →* H)) = (cptPart T).map (e : G →* H) := by
  unfold cptPart
  rw [MonoidHom.map_closure]
  congr 1
  have hz : ∀ t, (Subgroup.zpowers ((e : G →* H) t) : Set H) = e.toHomeomorph '' (Subgroup.zpowers t : Set G) := by
    intro t
    rw [← MonoidHom.map_zpowers, Subgroup.coe_map]
    rfl
  have hk : ∀ t, IsCompact (closure (Subgroup.zpowers ((e : G →* H) t) : Set H)) ↔
      IsCompact (closure (Subgroup.zpowers t : Set G)) := by
    intro t
    rw [hz, ← Homeomorph.image_closure, Homeomorph.isCompact_image]
  ext x
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, hc⟩
    exact ⟨t, ⟨ht, (hk t).1 hc⟩, rfl⟩
  · rintro ⟨t, ⟨ht, hc⟩, rfl⟩
    exact ⟨⟨t, ht, rfl⟩, (hk t).2 hc⟩

end GlobalTheory.EulerTw.Transport

namespace GlobalTheory.EulerTw.Transport

open GlobalTheory.BCT GlobalTheory.TwOrbConj

variable {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

theorem twCent_mem (e : G ≃ₜ* H) (θ : G →* G) (θ' : H →* H) (he : ∀ g, e (θ g) = θ' (e g)) (δ g : G) :
    g ∈ twCent θ δ ↔ e g ∈ twCent θ' (e δ) := by
  rw [mem_twCent, mem_twCent, ← he, ← map_mul, ← map_mul]
  exact e.injective.eq_iff.symm

theorem summand_map (e : G ≃ₜ* H) (θ : G →* G) (θ' : H →* H) (K : Subgroup G) (K' : Subgroup H) (δ : G)
    (f : G → ℂ) (f' : H → ℂ) (he : ∀ g, e (θ g) = θ' (e g)) (hK : ∀ g, g ∈ K ↔ e g ∈ K')
    (hf : ∀ g, f' (e g) = f g) (y : G) :
    summand θ' K' (e δ) f' (e y) = summand θ K δ f y := by
  have hT : twCent θ' (e δ) = (twCent θ δ).map (e : G →* H) :=
    map_eq_of_mem e _ _ (twCent_mem e θ θ' he δ)
  have hK' : K' = K.map (e : G →* H) := map_eq_of_mem e _ _ hK
  subst hK'
  unfold summand
  congr 1
  · have h1 : (K.map (e : G →* H)).map (MulAut.conj (e y)).toMonoidHom =
        (K.map (MulAut.conj y).toMonoidHom).map (e : G →* H) := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply]
    rw [h1, hT, ← Subgroup.map_inf_eq _ _ _ e.injective, cptPart_map_equiv,
      Subgroup.relIndex_map_map_of_injective _ _ e.injective]
  · let ψ : K ≃* (K.map (e : G →* H)) := e.toMulEquiv.subgroupMap K
    rw [← GlobalTheory.BCT.OrbProd.avg_comp_equiv ψ]
    congr 1
    funext k
    simp only [Function.comp_apply]
    rw [← hf]
    congr 1
    show (e y * e k.1)⁻¹ * e δ * θ' (e y * e k.1) = _
    rw [← map_mul, ← he, ← map_inv, ← map_mul, ← map_mul]

end GlobalTheory.EulerTw.Transport

namespace GlobalTheory.EulerTw.Transport

open GlobalTheory.BCT GlobalTheory.TwOrbConj

variable {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

def dcMap (e : G ≃ₜ* H) (T K : Subgroup G) (T' K' : Subgroup H) :
    DoubleCoset.Quotient (T : Set G) (K : Set G) → DoubleCoset.Quotient (T' : Set H) (K' : Set H) :=
  fun q => DoubleCoset.mk T' K' (e (Quotient.out q))

theorem dcMap_bij (e : G ≃ₜ* H) (T K : Subgroup G) (T' K' : Subgroup H) (hT : ∀ g, g ∈ T ↔ e g ∈ T')
    (hK : ∀ g, g ∈ K ↔ e g ∈ K') : Function.Bijective (dcMap e T K T' K') := by
  constructor
  · intro q1 q2 h
    obtain ⟨a, ha, b, hb, hab⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 h
    rw [← DoubleCoset.out_eq' q1, ← DoubleCoset.out_eq' q2, DoubleCoset.eq]
    refine ⟨e.symm a, (hT _).2 (by simpa using ha), e.symm b, (hK _).2 (by simpa using hb), ?_⟩
    apply e.injective
    simp only [map_mul, ContinuousMulEquiv.apply_symm_apply]
    exact hab
  · intro q'
    refine ⟨DoubleCoset.mk T K (e.symm (Quotient.out q')), ?_⟩
    obtain ⟨a, ha, b, hb, hab⟩ := DoubleCoset.mk_out_eq_mul T K (e.symm (Quotient.out q'))
    unfold dcMap
    rw [hab]
    conv_rhs => rw [← DoubleCoset.out_eq' q']
    rw [DoubleCoset.eq]
    refine ⟨(e a)⁻¹, T'.inv_mem ((hT a).1 ha), (e b)⁻¹, K'.inv_mem ((hK b).1 hb), ?_⟩
    simp only [map_mul, ContinuousMulEquiv.apply_symm_apply]
    group

end GlobalTheory.EulerTw.Transport

namespace GlobalTheory.EulerTw.Transport

open GlobalTheory.BCT GlobalTheory.TwOrbConj

theorem twOrb_transport : ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (e : G ≃ₜ* H) (θ : G →* G) (θ' : H →* H) (K : Subgroup G) (K' : Subgroup H) (δ : G) (f : G → ℂ) (f' : H → ℂ), (∀ g, e (θ g) = θ' (e g)) → (∀ g, g ∈ K ↔ e g ∈ K') → (∀ g, f' (e g) = f g) → twOrb θ K δ f = twOrb θ' K' (e δ) f' := by
  intro G H _ _ _ _ _ _ e θ θ' K K' δ f f' he hK hf
  have hT := twCent_mem e θ θ' he δ
  rw [twOrb_eq, twOrb_eq,
    ← finsum_comp_equiv (Equiv.ofBijective _ (dcMap_bij e (twCent θ δ) K (twCent θ' (e δ)) K' hT hK))]
  refine finsum_congr fun q => ?_
  obtain ⟨a, ha, b, hb, hab⟩ := DoubleCoset.mk_out_eq_mul (twCent θ' (e δ)) K' (e (Quotient.out q))
  have e2 : Quotient.out (Equiv.ofBijective _ (dcMap_bij e (twCent θ δ) K (twCent θ' (e δ)) K' hT hK) q) =
      a * e (Quotient.out q) * b := hab
  rw [e2, summand_rep θ' K' (e δ) f' _ ha hb, summand_map e θ θ' K K' δ f f' he hK hf]

end GlobalTheory.EulerTw.Transport

namespace GlobalTheory.EulerTw.Inert

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

end GlobalTheory.EulerTw.Inert

namespace GlobalTheory.EulerTw.Inert

open GlobalTheory.EulerTw

end GlobalTheory.EulerTw.Inert
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageDegEqDel
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open Formalism.L2.Pj Formalism.NormVectorIdentities.Items

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSCore.ImageDegree

theorem imageDeg_eq_del : Quoted → ∀ (F : Type) [Field F] [NumberField F] (T : Tuple F) (V Ω : Type) [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] [Field Ω] [Algebra F Ω] (Nm : (F →+* ℂ) → V → ℝ) (W : Submodule (𝓞 F) V) (ev : V →ₗ[F] Ω), T.IsGeometric → T.Birational → CompHt.Presents T.toHermSys Nm W ev → (CompHt.imageDeg ev T.D : ℤ) = T.del := by
  intro hQ F _ _ T V Ω _ _ _ _ _ _ Nm W ev hG hB hP
  obtain ⟨-, hdeg, hdim⟩ := GlobalTheory.T.degree_image_birational_linearSystem_eq_selfInt hQ F T.toLinSys hG.alg.variety hG.alg.bpf hB
  obtain ⟨f, hf, -⟩ := hQ.chowInt F T.N T.D T.imageIdeal T.toLinSys.isHomogeneous_imageIdeal
    (GlobalTheory.Adelic.HeightExists.isPrime_imageIdeal hG.alg.variety) hdim
  rw [hP.imageDeg_eq hf]
  exact hdeg

end GlobalTheory.HSCore.ImageDegree
end
end
