module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.WhitAtCOneIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.IwaRedOfC
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

theorem kFinK : KFinK := fun _ _ _ _ _ _ _ _ d Φ hΦ k hk => kfin_om d hΦ hk

theorem iwaRedC : IwaRedC := by
  intro hT c F E _ _ _ _ _ σ d Q hQs hQK hL Φ hΦ x nb lam 𝓖 hcd ε w hw T hTnd
  obtain ⟨p, t, hp, k, hk, rfl⟩ := d.ok.hgt.iwa x
  obtain ⟨n0, m0, β₀, hn, hm, rfl⟩ := par_decomp d p t hp
  have key := hL (d.om k Φ) (hQK Φ hΦ k hk) m0 hm nb lam 𝓖 hcd ε w hw T hTnd
  have e1 : (fun z => ∫ β, GlobalTheory.ThK.Dbl.flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * (n0 * m0 * k)) *
      d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam) = fun z => d.B.ψ (d.tt (T.1.1 * β₀)) *
      ∫ β, GlobalTheory.ThK.Dbl.flat d.a (d.sec0 (d.om k Φ)) (s0 d.m d.n) z (w * nb β * m0) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam := by
    funext z
    rw [← int_n d nb lam 𝓖 hcd T w n0 m0 β₀ hn]
    congr 1
    funext β
    rw [show w * nb β * (n0 * m0 * k) = (w * nb β * (n0 * m0)) * k by simp only [mul_assoc]]
    simp only [GlobalTheory.ThK.Dbl.flat, a_mul_K d _ k hk, section_mul_weil_action]
  have e2 : d.orb T (d.om (n0 * m0 * k) Φ) = d.B.ψ (d.tt (T.1.1 * β₀)) * d.orb T (d.om m0 (d.om k Φ)) := by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
    exact orb_n hT d T (om_mem_sch d _ (om_mem_sch d _ (hQs Φ hΦ))) n0 β₀ hn
  show HolValueAt _ _ _
  rw [e1, e2, mul_left_comm]
  exact holValueAt_const_mul _ key

end PositivityTheory.SiegelWeilFormula.KWhit

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.CoreX
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.HolValueAtConstMulCpow
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem holValueAt_const_mul_cpow (c : ℂ) {C : ℝ} (hC : 0 < C) (s₀ : ℂ) :
    HolValueAt (fun z => c * (C : ℂ) ^ (z - s₀)) s₀ c := by
  have h := holValueAt_self (h := fun z => c * (C : ℂ) ^ (z - s₀)) (σ := s₀.re - 1) (s₀ := s₀)
    (fun z _ => analyticAt_const.mul (analyticAt_const.cpow (analyticAt_id.sub analyticAt_const)
      (Complex.ofReal_mem_slitPlane.2 hC))) (by linarith)
  convert h using 1
  simp

end PositivityTheory.SiegelWeilFormula.KWhit

end
end

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

theorem coreX : CoreX := by
  intro ok vac c hT hA hS hU hW hD F E _ _ _ _ _ σ d R hok hE Φ hΦ P gf hpg hv x hx nb lam 𝓖 hcd ε w hw T hTnd
  obtain ⟨dd, J, T', bs, ψ, θ, l, εs, fr, g, lv, L₁, L₂, Φg, Φf, Φv, μ, ν, c', C, hDat, hAn, ⟨e, he⟩, hC, ⟨t, ht⟩,
    μH, 𝓕, hH, hF, horb⟩ := hD hT hA F E σ d R Φ hΦ P gf hpg x hx nb lam 𝓖 hcd ε w hw T hTnd
  obtain ⟨t', ht'⟩ := hU F E σ d (s0 d.m d.n) (d.sec0 Φ) (hS F E σ d Φ hΦ) (hE Φ hΦ)
  have hG := hW F E σ d.m d.n dd J T' bs ψ (InfinitePlace F) θ l εs fr g P lv L₁ L₂ Φg Φf Φv μ ν hDat hok
    (Or.inr hAn) (fun h => ⟨fun i => congrFun (hv h) i, e, he⟩)
    ⟨max t t', fun z hz => (ht z (lt_of_le_of_lt (le_max_left _ _) hz)).1
      ((ht' z (lt_of_le_of_lt (le_max_right _ _) hz) nb lam 𝓖 hcd ε w hw x).1)⟩ μH 𝓕 hH hF
  rw [horb, mul_left_comm]
  exact ((holValueAt_const_mul_cpow c' hC (s0 d.m d.n)).mul hG).congr ⟨t, fun z hz => ((ht z hz).2).symm⟩

end PositivityTheory.SiegelWeilFormula.KWhit

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.SectionLinearFinsetSum
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem lin_addChar_sum {A : Type} [AddCommMonoid A] (ψ : AddChar A ℂ) {ι : Type} (s : Finset ι) (f : ι → A) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, AddChar.map_add_eq_mul, ih]

theorem lin_holValueAt_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (h : ι → ℂ → ℂ) (v : ι → ℂ) (s₀ : ℂ)
    (hh : ∀ i ∈ s, HolValueAt (h i) s₀ (v i)) :
    HolValueAt (fun z => ∑ i ∈ s, c i * h i z) s₀ (∑ i ∈ s, c i * v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using holValueAt_const 0 s₀
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact ((holValueAt_const (c j) s₀).mul (hh j (Finset.mem_insert_self j s))).add
      (ih fun i hi => hh i (Finset.mem_insert_of_mem hi))

section SDl

variable (d : SD σ)

def linRhoL (v : Mx F E d.m d.n) : d.Fn →ₗ[ℂ] d.Fn where
  toFun := d.dd.rho d.B.ψ (v * (incM F d.b.1.toCols₂)ᵀ)
  map_add' Φ Ψ := by
    funext y
    simp only [Darboux.rho, schr, Pi.add_apply]
    ring
  map_smul' a Φ := by
    funext y
    simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem lin_T_eq (Φ : d.Fn) (X : Mx F E d.m d.n) : d.T Φ X = d.l (linRhoL d X Φ) := rfl

theorem lin_T_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (Φs : ι → d.Fn) (X : Mx F E d.m d.n) :
    d.T (∑ i ∈ s, c i • Φs i) X = ∑ i ∈ s, c i * d.T (Φs i) X := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [lin_T_eq, map_sum, map_smul, smul_eq_mul]

theorem section_linear_finset_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (Φs : ι → d.Fn) (x : d.G) :
    d.sec0 (∑ i ∈ s, c i • Φs i) x = ∑ i ∈ s, c i * d.sec0 (Φs i) x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [SD.sec0, map_sum, map_smul, smul_eq_mul]

theorem lin_om_mem (x : d.G) {Φ : d.Fn} (h : Φ ∈ d.sch) : d.om x Φ ∈ d.sch := d.ok.dbl.weil.2.1.pres x Φ h

theorem lin_S_mem (g : UA σ d.A.J) {Φ : d.Fn} (h : Φ ∈ d.sch) : d.S g Φ ∈ d.sch := d.ok.dbl.lin.pres g Φ h

theorem lin_sum_mem {ι : Type} (s : Finset ι) (c : ι → ℂ) (Φs : ι → d.Fn) (h : ∀ i ∈ s, Φs i ∈ d.sch) :
    ∑ i ∈ s, c i • Φs i ∈ d.sch :=
  Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (h i hi)

theorem lin_thetaSum_sum (hT : TTheta) {ι : Type} (s : Finset ι) (c : ι → ℂ) (Φs : ι → d.Fn) (h : ∀ i ∈ s, Φs i ∈ d.sch) :
    thetaSum F (∑ i ∈ s, c i • Φs i) = ∑ i ∈ s, c i * thetaSum F (Φs i) := by
  have h1 := (hT F E σ d _ (lin_sum_mem d s c Φs h)).1
  have h2 : HasSum (fun X : Matrix (Fin d.m) (Fin d.n) E => ∑ i ∈ s, c i * d.T (Φs i) (incM F X))
      (∑ i ∈ s, c i * thetaSum F (Φs i)) :=
    hasSum_sum fun i hi => ((hT F E σ d _ (h i hi)).1).mul_left (c i)
  simp only [lin_T_sum] at h1
  exact h1.unique h2

theorem lin_I_sum (hT : TTheta) (hA : ThetaAuto) {ι : Type} (s : Finset ι) (c : ι → ℂ) (Φs : ι → d.Fn)
    (h : ∀ i ∈ s, Φs i ∈ d.sch) (x : d.G) : d.I (∑ i ∈ s, c i • Φs i) x = ∑ i ∈ s, c i * d.I (Φs i) x := by
  have e : ∀ g : UA σ d.A.J, thetaSum F (d.om x (d.S g (∑ i ∈ s, c i • Φs i))) =
      ∑ i ∈ s, c i * thetaSum F (d.om x (d.S g (Φs i))) := by
    intro g
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum]
    simp only [map_smul]
    exact lin_thetaSum_sum d hT s c (fun i => d.om x (d.S g (Φs i))) fun i hi => lin_om_mem d x (lin_S_mem d g (h i hi))
  have hint : ∀ i ∈ s, IntegrableOn (fun g => thetaSum F (d.om x (d.S g (Φs i)))) d.D d.μ :=
    fun i hi => ((hA F E σ d).2.2 _ (h i hi)).1 x
  show ⨍ g in d.D, thetaSum F (d.om x (d.S g (∑ i ∈ s, c i • Φs i))) ∂d.μ =
    ∑ i ∈ s, c i * ⨍ g in d.D, thetaSum F (d.om x (d.S g (Φs i))) ∂d.μ
  simp only [e, setAverage_eq]
  rw [integral_finsetSum s fun i hi => (hint i hi).const_mul (c i), Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, mul_smul_comm]

end SDl

theorem lin_psi_meas (d : SD σ) (M : Mx F E d.n d.n) :
    Measurable (fun β : nA σ d.Y d.b => d.B.ψ (-d.tt (M * β.1))) := by
  have key : ∀ β : nA σ d.Y d.b, d.B.ψ (-d.tt (M * β.1)) =
      ∏ i, ∏ k, d.B.ψ (-(Algebra.trace (AF F) (AE F E) (M i k * β.1 k i))) := by
    intro β
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [SD.tt, Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, ← Finset.sum_neg_distrib, lin_addChar_sum]
  rw [show (fun β : nA σ d.Y d.b => d.B.ψ (-d.tt (M * β.1))) = fun β =>
      ∏ i, ∏ k, d.B.ψ (-(Algebra.trace (AF F) (AE F E) (M i k * β.1 k i))) from funext key]
  have : OpensMeasurableSpace (AE F E) := ⟨le_rfl⟩
  refine Finset.measurable_prod _ fun i _ => Finset.measurable_prod _ fun k _ => ?_
  have hc : Continuous fun y : AE F E => d.B.ψ (-(Algebra.trace (AF F) (AE F E) (M i k * y))) :=
    d.ok.good.std.1.comp (IsModuleTopology.continuous_of_linearMap
      ((Algebra.trace (AF F) (AE F E)).comp (LinearMap.mulLeft (AF F) (M i k)))).neg
  exact hc.measurable.comp ((measurable_pi_apply i).comp ((measurable_pi_apply k).comp measurable_subtype_coe))

theorem lin_fc_sum (hLB : LamBd) (d : SD σ) {nb lam 𝓖} (hcd : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖)
    (T : nF σ d.Y d.b) (hND : IsND T) (x : d.G) {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → d.G → ℂ)
    (hc : ∀ i, Continuous (f i)) (hi : ∀ i, ∀ γ ∈ rat2 σ d.Y, ∀ g, f i (γ * g) = f i g) :
    fc d.B.ψ d.b nb lam 𝓖 (∑ i ∈ s, c i • f i) T x = ∑ i ∈ s, c i * fc d.B.ψ d.b nb lam 𝓖 (f i) T x := by
  classical
  obtain ⟨hlin, -⟩ := hLB F E σ d (fun f => fc d.B.ψ d.b nb lam 𝓖 f T x) ⟨nb, lam, 𝓖, T, x, hcd, hND, rfl⟩
  have hfun : ∀ s : Finset ι, (∑ i ∈ s, c i • f i) = fun a => ∑ i ∈ s, c i * f i a := by
    intro s; funext a; simp [Finset.sum_apply]
  have hcs : ∀ s : Finset ι, Continuous (∑ i ∈ s, c i • f i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      change Continuous (fun _ : d.G => (0 : ℂ))
      exact continuous_const
    | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (continuous_const.smul (hc i)).add ih
  have his : ∀ s : Finset ι, ∀ γ ∈ rat2 σ d.Y, ∀ g, (∑ i ∈ s, c i • f i) (γ * g) = (∑ i ∈ s, c i • f i) g := by
    intro s γ hγ g; rw [hfun s]; exact Finset.sum_congr rfl fun i _ => by rw [hi i γ hγ g]
  induction s using Finset.induction_on with
  | empty =>
    have h0 := hlin 1 0 0 continuous_const continuous_const (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    simp only [one_smul, add_zero, one_mul] at h0
    simpa using h0
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, hlin (c j) (f j) _ (hc j) (hcs s) (hi j) (his s), ih]

end PositivityTheory.SiegelWeilFormula.KWhit

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.VacIsPureBy
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def vac_gen {d : SD σ} (R : RD d) : Set (Mx F E d.m d.n → ℂ) :=
  {f | ∃ φ, Dense.Good φ ∧ f = genF R (fun _ => 1) (Dense.pf φ)}

theorem vac_gen_sub {d : SD σ} (R : RD d) : vac_gen R ⊆ R.vac := by
  rintro _ ⟨φ, hφ, rfl⟩
  exact Submodule.subset_span ⟨Dense.pf φ, Dense.pf_mem hφ, rfl⟩

theorem vac_le_span {d : SD σ} (R : RD d) : R.vac ≤ Submodule.span ℂ (vac_gen R) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, hg, rfl⟩
  have := Dense.mem_span_pf hg
  clear hg
  have key : genL R (fun _ => 1) g ∈ Submodule.span ℂ (vac_gen R) := by
    induction this using Submodule.span_induction with
    | mem x hx => obtain ⟨φ, hφ, rfl⟩ := hx; exact Submodule.subset_span ⟨φ, hφ, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  exact key

theorem vac_isPureBy {d : SD σ} (R : RD d)
    (φ : ∀ u : HeightOneSpectrum (𝓞 F), (Fin d.m × Fin d.n × Fin 2 → Fv F u) → ℂ) (hφ : Dense.Good φ) (Φ : d.Fn)
    (h : d.T Φ = genF R (fun _ => 1) (Dense.pf φ)) : ∃ gf, IsPureBy R Φ (fun _ => 1) gf := by
  refine ⟨φ, fun v => hφ.1 v, hφ.2.mono fun v hv => hv, ?_⟩
  rw [h]
  rfl

theorem vacSpan : VacSpan := by
  intro hT hF hPK hVK F E _ _ _ _ _ σ d R Φ hΦ hTΦ
  have hB := hT.1 F E σ d
  have hvf : R.vac ≤ R.fock := (hVK F E σ d R).2.1
  have h1 : d.T Φ ∈ Submodule.span ℂ (vac_gen R) := vac_le_span R hTΦ
  obtain ⟨k, c, gs, hsum⟩ := Submodule.mem_span_set'.1 h1
  have hpre : ∀ i : Fin k, ∃ Ψ ∈ d.sch, d.T Ψ = (gs i : Mx F E d.m d.n → ℂ) := fun i =>
    hB.2.1 _ ((hF F E σ d R).1 (hvf (vac_gen_sub R (gs i).2)))
  choose Φs hΦs hTs using hpre
  refine ⟨k, c, Φs, fun i => ⟨hPK F E σ d R (Φs i) (hΦs i) (hTs i ▸ hvf (vac_gen_sub R (gs i).2)),
    hTs i ▸ vac_gen_sub R (gs i).2, ?_⟩, ?_⟩
  · obtain ⟨φ, hφ, e⟩ := (gs i).2
    exact vac_isPureBy R φ hφ (Φs i) ((hTs i).trans e)
  · have hmem : Φ - ∑ i, c i • Φs i ∈ d.sch :=
      sub_mem hΦ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hΦs i))
    have h0 : d.T (Φ - ∑ i, c i • Φs i) = 0 := by
      rw [T_sub, T_sum, ← hsum]
      simp only [hTs, sub_self]
    exact (sub_eq_zero.1 (hB.2.2 _ hmem h0))

end PositivityTheory.SiegelWeilFormula.KWhit

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ThMSymmApply
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

instance th_borelUA {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : BorelSpace (UA σ J) := ⟨rfl⟩

instance th_borelHA {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : BorelSpace (HeckeCharacterZeroLocus.SiegelWeilU.HA (AF F) σ J) := ⟨rfl⟩

def thM (d : SD σ) {η : E} (hη : η ≠ 0) : UA σ d.A.J ≃ᵐ HeckeCharacterZeroLocus.SiegelWeilU.HA (AF F) σ (Jd d η) :=
  (Homeomorph.mk (thE d hη).toEquiv (thE_cont d hη) (thE_symm_cont d hη)).toMeasurableEquiv

theorem th_sigR_incl (x : E) :
    HeckeCharacterZeroLocus.SiegelWeilU.sigR (AF F) σ (inclR (F := F) (E := E) (AF F) x) = inclR (F := F) (E := E) (AF F) (σ x) := by
  simp [HeckeCharacterZeroLocus.SiegelWeilU.sigR, inclR, Algebra.TensorProduct.map_tmul]

theorem th_cT_map {M : ℕ} (γ : Matrix (Fin M) (Fin M) E) :
    (HeckeCharacterZeroLocus.SiegelWeilU.cT (σ : E →+* E) γ).map (inclR (F := F) (E := E) (AF F)) =
      HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR (AF F) σ) (γ.map (inclR (F := F) (E := E) (AF F))) := by
  ext i j
  simp only [HeckeCharacterZeroLocus.SiegelWeilU.cT, Matrix.map_apply, Matrix.transpose_apply]
  exact (th_sigR_incl _).symm

def thE' (d : SD σ) {η : E} (hη : η ≠ 0) (g : UA σ d.A.J) : HeckeCharacterZeroLocus.SiegelWeilU.HR (AF F) σ (Jd d η) := thE d hη g

theorem th_rat_iff (d : SD σ) {η : E} (hη : η ≠ 0) (g : UA σ d.A.J) :
    g ∈ ratU σ d.A.J ↔ thE' d hη g ∈ HeckeCharacterZeroLocus.SiegelWeilU.HFinIn (AF F) σ (Jd d η) := by
  rw [ratU, Subgroup.mem_subgroupOf, MonoidHom.mem_range, HeckeCharacterZeroLocus.SiegelWeilU.HFinIn, Subgroup.mem_subgroupOf,
    HeckeCharacterZeroLocus.SiegelWeilU.HFin, Subgroup.mem_map]
  constructor
  · rintro ⟨γ, hγ⟩
    refine ⟨γ, ?_, hγ⟩
    have hg : (g.1 : GL (Fin d.m) (AE F E)) ∈ HeckeCharacterZeroLocus.SiegelWeilU.HR (AF F) σ (Jd d η) := (th_mem_iff d hη g.1).1 g.2
    rw [← hγ] at hg
    change HeckeCharacterZeroLocus.SiegelWeilU.cT (σ : E →+* E) (γ : Matrix (Fin d.m) (Fin d.m) E) * Jd d η * (γ : Matrix (Fin d.m) (Fin d.m) E) =
      Jd d η
    apply Matrix.map_injective (th_inclR_injective (F := F) (E := E))
    change HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR (AF F) σ) ((γ : Matrix (Fin d.m) (Fin d.m) E).map (inclR (F := F) (E := E) (AF F))) *
      HeckeCharacterZeroLocus.SiegelWeilU.JR (AF F) (Jd d η) * (γ : Matrix (Fin d.m) (Fin d.m) E).map (inclR (F := F) (E := E) (AF F)) =
      HeckeCharacterZeroLocus.SiegelWeilU.JR (AF F) (Jd d η) at hg
    dsimp only
    rw [Matrix.map_mul, Matrix.map_mul, th_cT_map]
    exact hg
  · rintro ⟨γ, -, hγ⟩
    exact ⟨γ, hγ⟩

def thR (d : SD σ) {η : E} (hη : η ≠ 0) : HeckeCharacterZeroLocus.SiegelWeilU.HFinIn (AF F) σ (Jd d η) ≃ ratU σ d.A.J where
  toFun h := ⟨(thE d hη).symm h.1, (th_rat_iff d hη _).2
    (by have e1 : thE' d hη ((thE d hη).symm h.1) = h.1 := (thE d hη).apply_symm_apply h.1
        rw [e1]; exact h.2)⟩
  invFun g := ⟨thE' d hη g.1, (th_rat_iff d hη _).1 g.2⟩
  left_inv h := Subtype.ext ((thE d hη).apply_symm_apply h.1)
  right_inv g := Subtype.ext ((thE d hη).symm_apply_apply g.1)

theorem th_haar (d : SD σ) {η : E} (hη : η ≠ 0) :
    HeckeCharacterZeroLocus.SiegelWeilU.IsHaarH F E σ d.m (Jd d η) (d.μ.map (thM d hη)) := by
  let : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  let : IsTopologicalGroup (UA σ d.A.J) := Subgroup.instIsTopologicalGroupSubtypeMem _
  have := d.ok.haar
  exact th_haar_map d.μ (thE d hη) (thE_cont d hη) (thE_symm_cont d hη)

theorem th_fd (d : SD σ) {η : E} (hη : η ≠ 0) :
    HeckeCharacterZeroLocus.SiegelWeilU.IsFDH F E σ d.m (Jd d η) (d.μ.map (thM d hη)) (thM d hη '' d.D) := by
  refine d.ok.dom.image_of_equiv (thM d hη).toEquiv ⟨(thM d hη).symm.measurable.aemeasurable, ?_⟩ (thR d hη) ?_
  · change Measure.map (thM d hη).symm (Measure.map (thM d hη) d.μ) ≪ d.μ
    rw [MeasurableEquiv.map_symm_map]
  · intro h x
    rfl

end PositivityTheory.SiegelWeilFormula.KWhit

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ExistsRationalMatrixUnipotent
noncomputable section

open scoped TensorProduct NNReal Matrix ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem rel_algebraMap_injective : Function.Injective (algebraMap F (AF F)) := by
  intro x y h
  have := congrArg Prod.fst h
  exact (algebraMap F (NumberField.InfiniteAdeleRing F)).injective this

theorem rel_inclR_injective : Function.Injective (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) (AF F)) :=
  Algebra.TensorProduct.includeRight_injective rel_algebraMap_injective

theorem rel_incM_injective {a b : Type} : Function.Injective (incM F (E := E) (m := a) (n := b)) := by
  intro X Y h
  ext i j
  exact rel_inclR_injective (congrFun (congrFun h i) j)

theorem rel_sigR_eq_cA (z : AE F E) : HeckeCharacterZeroLocus.SiegelWeilU.sigR (AF F) σ z = cA σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [HeckeCharacterZeroLocus.SiegelWeilU.sigR, cA, Algebra.TensorProduct.map_tmul]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem rel_definite {m r s : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (h : HasSig M r s) (h0 : min r s = 0)
    (z : Fin m → ℂ) (hz : z ≠ 0) : z ⬝ᵥ M *ᵥ star z ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  set S : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ := Matrix.fromBlocks 1 0 0 (-1) with hS
  have hSS : S * S = 1 := by
    simp [S, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  have hSu : IsUnit S := ⟨⟨S, S, hSS, hSS⟩, rfl⟩
  have hrank : A.rank = m := by
    apply le_antisymm ((Matrix.rank_le_card_height A).trans (by simp))
    have h1 : S.rank = r + s := by
      rw [Matrix.rank_of_isUnit S hSu]
      simp
    have h2 : S.rank ≤ Aᵀ.rank := by
      rw [← hA]
      exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_left _ _)
    rw [Matrix.rank_transpose] at h2
    omega
  have hsurj : ∃ w, A *ᵥ w = z := by
    have : LinearMap.range A.mulVecLin = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [← Matrix.rank, hrank]
      simp
    exact LinearMap.range_eq_top.mp this z
  obtain ⟨w, rfl⟩ := hsurj
  have hw : w ≠ 0 := by
    rintro rfl
    simp at hz
  have hst : star (A *ᵥ w) = A.map star *ᵥ star w := by
    ext i
    simp [Matrix.mulVec, dotProduct, star_sum, mul_comm]
  have key : (A *ᵥ w) ⬝ᵥ M *ᵥ star (A *ᵥ w) = w ⬝ᵥ S *ᵥ star w := by
    rw [hst, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul,
      ← Matrix.dotProduct_mulVec, ← Matrix.mul_assoc, hA]
  rw [key]
  have hne : w ⬝ᵥ star w ≠ 0 := by
    rw [dotProduct_comm]
    exact fun h => hw (dotProduct_star_self_eq_zero.mp h)
  rcases Nat.min_eq_zero_iff.mp h0 with hr | hs
  · subst hr
    have : S *ᵥ star w = -star w := by
      ext k
      rcases k with i | j
      · exact i.elim0
      · simp [S, Matrix.mulVec, dotProduct, Matrix.fromBlocks, Fintype.sum_sum_type, Matrix.one_apply]
    rw [this, dotProduct_neg]
    exact neg_ne_zero.mpr hne
  · subst hs
    have : S *ᵥ star w = star w := by
      ext k
      rcases k with i | j
      · simp [S, Matrix.mulVec, dotProduct, Matrix.fromBlocks, Fintype.sum_sum_type, Matrix.one_apply]
      · exact j.elim0
    rw [this]
    exact hne

theorem rel_aniso (d : SD σ) (η : E) (hη : η ≠ 0) (y : Fin d.m → E)
    (hy : HeckeCharacterZeroLocus.SiegelWeilU.hE σ (Jd d η) y y = 0) : y = 0 := by
  by_contra hy0
  let w : InfinitePlace F := Classical.arbitrary _
  let τ : E →+* ℂ := (d.B.emb w).1
  have hτ : ∀ x, τ (σ x) = star (τ x) := d.ok.good.cm.2.2.2 τ
  let z : Fin d.m → ℂ := fun i => τ (y i)
  have hz : z ≠ 0 := by
    intro h
    apply hy0
    funext i
    apply τ.injective
    simpa [z] using congrFun h i
  have key : τ (HeckeCharacterZeroLocus.SiegelWeilU.hE σ (Jd d η) y y) = τ η * (z ⬝ᵥ (d.A.J.map τ) *ᵥ star z) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [HeckeCharacterZeroLocus.SiegelWeilU.hE, HeckeCharacterZeroLocus.SiegelWeilU.hform, Jd, Matrix.mulVec, dotProduct, map_sum, map_mul,
      Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, Finset.mul_sum, Pi.star_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [z]
    rw [show ((σ : E →+* E) (y j)) = σ (y j) from rfl, hτ]
    ring
  rw [hy, map_zero] at key
  have hQ : z ⬝ᵥ (d.A.J.map τ) *ᵥ star z ≠ 0 := by
    rcases d.ok.sign with ⟨hA, -⟩ | ⟨hA, -⟩
    · exact rel_definite _ (hA.sig w) d.ok.aniso z hz
    · have h1 := rel_definite _ (hA.sig w) d.ok.aniso z hz
      intro h0
      apply h1
      simp only [Matrix.smul_mulVec, dotProduct_smul]
      change Complex.I • (z ⬝ᵥ d.A.J.map τ *ᵥ star z) = 0
      rw [h0, smul_zero]
  have hτη : τ η ≠ 0 := (map_ne_zero τ).mpr hη
  exact (mul_ne_zero hτη hQ) key.symm

theorem exists_rational_matrix_unipotent (d : SD σ) (T : nF σ d.Y d.b) : ∃ T₀ : Matrix (Fin d.n) (Fin d.n) E, T.1.1 = incM F T₀ := by
  obtain ⟨T, hT⟩ := T
  induction hT using AddSubgroup.closure_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, by ext i j; simp [incM]⟩
  | add x y _ _ hx hy =>
    obtain ⟨X, hX⟩ := hx
    obtain ⟨Y, hY⟩ := hy
    refine ⟨X + Y, ?_⟩
    change x.1 + y.1 = _
    rw [hX, hY]
    ext i j
    simp [incM]
  | neg x _ hx =>
    obtain ⟨X, hX⟩ := hx
    refine ⟨-X, ?_⟩
    change -x.1 = _
    rw [hX]
    ext i j
    simp [incM]

def relH (d : SD σ) (η : E) (β : nA σ d.Y d.b) : Matrix (Fin d.n) (Fin d.n) (AE F E) :=
  -(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) (AF F) η⁻¹ • β.1ᵀ)

theorem relH_mem (d : SD σ) (ε : ℤˣ)
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (η : E) (hη : η ≠ 0)
    (hση : σ η = -(((ε : ℤ) : E) * η)) (β : nA σ d.Y d.b) :
    relH d η β ∈ HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n := by
  intro a b
  have hn := congrFun (congrFun (rel_nA_cond d ε hε β) a) b
  simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
    Matrix.zero_apply] at hn
  have he2 : ((ε : ℤ) : E) * ((ε : ℤ) : E) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
    simp
  have hinv : σ η⁻¹ = -(((ε : ℤ) : E) * η⁻¹) := by
    rw [map_inv₀, hση, inv_neg, mul_inv, inv_eq_of_mul_eq_one_right he2]
  have hc : ∀ x : E, cA σ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) x) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (σ x) := by
    intro x
    simp [cA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Algebra.TensorProduct.map_tmul]
  simp only [relH, Matrix.neg_apply, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul]
  rw [map_neg, map_mul, rel_sigR_eq_cA, rel_sigR_eq_cA, hc, hinv, map_neg, map_mul, map_intCast]
  linear_combination (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) (AF F) η⁻¹) * hn

theorem relH_eq (d : SD σ) (η : E) (hη : η ≠ 0) (β : nA σ d.Y d.b) :
    β.1 = -(incM F (Matrix.scalar (Fin d.n) η) * (relH d η β)ᵀ) := by
  have h1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) (AF F) η * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) η⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hη, map_one]
  ext i j
  simp [relH, incM, Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, ← mul_assoc, h1]
  rw [mul_comm (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) (AF F) η⁻¹), h1, one_mul]

theorem rel_Td (d : SD σ) (ε : ℤˣ)
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (η : E) (hη : η ≠ 0)
    (hση : σ η = -(((ε : ℤ) : E) * η)) (T : nF σ d.Y d.b) (hT : IsND T) (T₀ : Matrix (Fin d.n) (Fin d.n) E)
    (h0 : T.1.1 = incM F T₀) : (∀ a b, σ (Td η T₀ b a) = Td η T₀ a b) ∧ (Td η T₀).det ≠ 0 := by
  have hn := rel_nA_cond d ε hε T.1
  rw [h0, rel_cA_incM] at hn
  have hn' : incM F (T₀ᵀ + ((ε : ℤ) : E) • T₀.map σ) = incM F 0 := by
    have e0 : incM F (0 : Matrix (Fin d.n) (Fin d.n) E) = 0 := by
      ext i j
      simp [incM]
    rw [e0, ← hn]
    ext i j
    simp [incM]
  have hz := rel_incM_injective hn'
  refine ⟨fun a b => ?_, ?_⟩
  · have he := congrFun (congrFun hz a) b
    simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
      Matrix.zero_apply] at he
    simp only [Td, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
    rw [map_mul, map_mul, map_neg, map_ofNat, hση]
    linear_combination (2 * η) * he
  · have hdet : T₀.det ≠ 0 := by
      intro h
      apply hT
      show (T.1.1).det = 0
      rw [h0, incM, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]
    simp only [Td, Matrix.det_transpose, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero (neg_ne_zero.mpr two_ne_zero) hη)) hdet

theorem relAlg_pf : RelAlg := by
  intro F E _ _ _ _ _ σ d
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨η, hη, hση, hherm⟩ := rel_eta d ε hε
  refine ⟨η, fun β => ⟨relH d η β, relH_mem d ε hε η hη hση β⟩, hη, hherm, fun β => relH_eq d η hη β,
    fun y hy => rel_aniso d η hη y hy, d.ok.good.cm, ⟨fun i j => ?_, ?_⟩, fun T hT => ?_⟩
  · simp only [Jd, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
    exact hherm j i
  · intro h0
    obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    apply hy0
    apply rel_aniso d η hη y
    have h2 : HeckeCharacterZeroLocus.SiegelWeilU.hE σ (Jd d η) y y = ∑ i, σ (y i) * (Jd d η *ᵥ y) i := by
      simp only [HeckeCharacterZeroLocus.SiegelWeilU.hE, HeckeCharacterZeroLocus.SiegelWeilU.hform, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
      rfl
    rw [h2, hy]
    simp
  · obtain ⟨T₀, h0⟩ := exists_rational_matrix_unipotent d T
    exact ⟨T₀, h0, rel_Td d ε hε η hη hση T hT T₀ h0⟩

end PositivityTheory.SiegelWeilFormula.KWhit

end
end
