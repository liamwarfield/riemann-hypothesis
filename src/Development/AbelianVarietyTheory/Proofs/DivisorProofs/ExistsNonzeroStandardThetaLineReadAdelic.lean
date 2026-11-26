module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaModerateGrowthHeight
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumDoubledOfSchrodingerFormulas

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvSmulMemRationalHomLatticeScaledOfNormScale
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvSmulMemRationalHomLatticeScaledOfNormScale
noncomputable section

open NumberField

namespace GlobalTheory.VacRead

theorem int_of_mem_bInv (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (hc : cc ≠ ⊥) (hr : r ≠ 0)
    {γ : D.host.E} (hγ : γ ∈ cE D D.host.ccK) {c : 𝓞 D.host.K} (hcc : c ∈ cc) {y : D.host.E} (hy : y ∈ bInv D cc r) :
    GlobalTheory.InertSign.IntE D (D.host.conj γ * ((c : D.host.K) : D.host.E) * r⁻¹ * y /
      (Ideal.absNorm D.host.ccK : D.host.E)) := by
  have hN0 : (Ideal.absNorm D.host.ccK : D.host.E) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact D.host.ccK_ne_bot
  have hN : (Ideal.absNorm cc : D.host.E) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact hc
  have hcE : ((c : D.host.K) : D.host.E) ∈ cE D cc := Submodule.subset_span ⟨c, hcc, rfl⟩
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨α, hα, γ₂, hγ₂, rfl⟩ := hy
    obtain ⟨o₁, h₁⟩ := (GlobalTheory.T.idealExtend_conj_mul_eq_absNorm D D.host.ccK).1 γ hγ γ₂ hγ₂
    obtain ⟨o₂, h₂⟩ := (GlobalTheory.T.idealExtend_conj_mul_eq_absNorm D cc).1 α hα _ hcE
    refine ⟨o₁ * o₂, ?_⟩
    have e : D.host.conj γ * ((c : D.host.K) : D.host.E) * r⁻¹ * (r * D.host.conj α * γ₂ / (Ideal.absNorm cc : D.host.E)) /
        (Ideal.absNorm D.host.ccK : D.host.E) =
        (D.host.conj γ * γ₂ / (Ideal.absNorm D.host.ccK : D.host.E)) *
          (D.host.conj α * ((c : D.host.K) : D.host.E) / (Ideal.absNorm cc : D.host.E)) := by
      field_simp
    rw [e, h₁, h₂, mul_div_cancel_left₀ _ hN0, mul_div_cancel_left₀ _ hN]
    simp
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    exact ⟨u + v, by rw [map_add (f := _), hu, hv]; ring⟩
  | smul o x _ hx =>
    obtain ⟨u, hu⟩ := hx
    refine ⟨o * u, ?_⟩
    rw [map_mul, hu, Algebra.smul_def]
    ring

theorem mul_mem_Iid (D : Formalism.BasicNotions.D7) {ε α : D.host.E} (hε : ε ∈ cE D D.host.ccK)
    (hα : α ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E)) : ε * α ∈ GlobalTheory.InertSign.Iid D D.host.ccK := by
  induction hε using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c₀, hc₀, rfl⟩ := hx
    exact Submodule.subset_span ⟨c₀, hc₀, α, hα, rfl⟩
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul o x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ o hx

theorem smul_mem_homL (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (a d : ℕ) (hc : cc ≠ ⊥) (hr : r ≠ 0)
    {γ : D.host.E} (hγ : γ ∈ cE D D.host.ccK) {c : 𝓞 D.host.K} (hcc : c ∈ cc)
    {A : Matrix (Fin d) (Fin a) D.host.E} (hA : A ∈ Formalism.MainNotions.TaylorLogMetric.homL D (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d)) :
    (D.host.conj γ * ((c : D.host.K) : D.host.E) * r⁻¹ / (Ideal.absNorm D.host.ccK : D.host.E)) • A ∈
      Formalism.MainNotions.TaylorLogMetric.homL D (lsB D cc r a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d) := by
  have hA' := GlobalTheory.ThetaLatImage.mem_homL.1 hA
  have hint : ∀ i j, GlobalTheory.InertSign.IntE D (A i j) := by
    intro i j
    have h1 : Pi.single j (1 : D.host.E) ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D a := by
      rw [GlobalTheory.ThetaLatImage.mem_stdL]
      intro k
      refine ⟨if k = j then 1 else 0, ?_⟩
      by_cases h : k = j
      · subst h; simp
      · simp [h]
    have h2 := GlobalTheory.ThetaLatImage.mem_stdL.1 (hA' _ h1) i
    have hcol : A.mulVec (Pi.single j 1) i = A i j := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rwa [hcol] at h2
  rw [GlobalTheory.ThetaLatImage.mem_homL]
  intro x hx
  rw [GlobalTheory.ThetaLatImage.mem_stdL]
  intro i
  have hy : A.mulVec x i ∈ bInv D cc r := by
    simp only [Matrix.mulVec, dotProduct]
    refine Submodule.sum_mem _ fun j _ => ?_
    obtain ⟨o, ho⟩ := hint i j
    rw [← ho, ← Algebra.smul_def]
    exact Submodule.smul_mem _ o (mem_lsB.1 hx j)
  have := int_of_mem_bInv D cc r hc hr hγ hcc hy
  rw [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
  convert this using 1
  ring

theorem gen_mem_RL (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (a d : ℕ) (hc : cc ≠ ⊥) (hr : r ≠ 0)
    {c : 𝓞 D.host.K} (hcc : c ∈ cc) {α : D.host.E} (hα : α ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E))
    {A : Matrix (Fin d) (Fin a) D.host.E} (hA : A ∈ Formalism.MainNotions.TaylorLogMetric.homL D (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d)) :
    (r⁻¹ * (((c : D.host.K) : D.host.E) * α)) • A ∈
      GlobalTheory.InertSign.RL D D.host.ccK (lsB D cc r a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d) := by
  have hN0 : (Ideal.absNorm D.host.ccK : D.host.E) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact D.host.ccK_ne_bot
  set X := r⁻¹ * (((c : D.host.K) : D.host.E) * α) with hX
  have key : ∀ t ∈ Submodule.span (𝓞 D.host.E) {t | ∃ γ ∈ cE D D.host.ccK, ∃ ε ∈ cE D D.host.ccK,
      t = D.host.conj γ * ε},
      (t * ((Ideal.absNorm D.host.ccK : D.host.E)⁻¹ * X)) • A ∈
        GlobalTheory.InertSign.RL D D.host.ccK (lsB D cc r a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d) := by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨γ, hγ, ε, hε, rfl⟩ := ht
      have e : (D.host.conj γ * ε * ((Ideal.absNorm D.host.ccK : D.host.E)⁻¹ * X)) • A =
          (ε * α) • ((D.host.conj γ * ((c : D.host.K) : D.host.E) * r⁻¹ /
            (Ideal.absNorm D.host.ccK : D.host.E)) • A) := by
        rw [smul_smul, hX]
        congr 1
        ring
      rw [e]
      exact Submodule.subset_span ⟨ε * α, mul_mem_Iid D hε hα, _, smul_mem_homL D cc r a d hc hr hγ hcc hA, rfl⟩
    | zero => rw [zero_mul, zero_smul]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [add_mul, add_smul]; exact Submodule.add_mem _ hx hy
    | smul o x _ hx => rw [smul_mul_assoc, smul_assoc]; exact Submodule.smul_mem _ o hx
  have h := key _ (GlobalTheory.T.idealExtend_conj_mul_eq_absNorm D D.host.ccK).2
  rwa [mul_inv_cancel_left₀ hN0] at h

theorem rl_div_scale : ∀ (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (a d : ℕ), cc ≠ ⊥ →
    GlobalTheory.NormExact.IsScale D cc r → ∀ z ∈ GlobalTheory.InertSign.RL D cc (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d),
      r⁻¹ • z ∈ GlobalTheory.InertSign.RL D D.host.ccK (GlobalTheory.VacRead.lsB D cc r a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d) := by
  intro D cc r a d hc hs z hz
  have hr : r ≠ 0 := GlobalTheory.NormExact.IsScale.ne_zero hc hs
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨t, ht, A, hA, rfl⟩ := hz
    rw [smul_smul]
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨c, hcc, α, hα, rfl⟩ := ht
      exact gen_mem_RL D cc r a d hc hr hcc hα hA
    | zero => rw [mul_zero, zero_smul]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [mul_add, add_smul]; exact Submodule.add_mem _ hx hy
    | smul o x _ hx => rw [mul_smul_comm, smul_assoc]; exact Submodule.smul_mem _ o hx
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul o x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ o hx

end GlobalTheory.VacRead
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvSmulMemRationalHomLatticeScaledOfNormScaleStatement
open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inv_smul_mem_rationalHomLatticeScaled_of_normScale : ∀ (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (a d : ℕ), cc ≠ ⊥ → GlobalTheory.NormExact.IsScale D cc r → ∀ z ∈ GlobalTheory.InertSign.RL D cc (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d), r⁻¹ • z ∈ GlobalTheory.InertSign.RL D D.host.ccK (GlobalTheory.VacRead.lsB D cc r a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d) := by
  first | exact @GlobalTheory.VacRead.rl_div_scale | exact GlobalTheory.VacRead.rl_div_scale | (intros; apply GlobalTheory.VacRead.rl_div_scale <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroStandardThetaLineReadAdelic
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacRead

def posSig {D : D7} (S : HSp D) : HSp D := {S with sig := fun _ => (S.rank, 0)}

theorem hasSignature_one (n : ℕ) : Formalism.UG.HasSignature (1 : Matrix (Fin n) (Fin n) ℂ) n 0 := by
  refine ⟨(Equiv.sumEmpty (Fin n) (Fin 0)).symm, 1, ?_⟩
  ext i j
  rcases i with i | i
  · rcases j with j | j
    · simp [Formalism.UG.Jpq, Formalism.UG.cT, Matrix.one_apply]
    · exact j.elim0
  · exact i.elim0

theorem sigOK_posSig {D : D7} (S : HSp D) (h : S.gram = 1) : (posSig S).SigOK := by
  intro τ
  show Formalism.UG.HasSignature (S.gram.map τ) S.rank 0
  rw [h, Matrix.map_one _ (map_zero τ) (map_one τ)]
  exact hasSignature_one _

open scoped ComplexOrder in
theorem isCartanInv_one {D : D7} (S : HSp D) (h : S.gram = 1) (τ : D.what₂.Tau) : IsCartanInv (gramAt D S τ) 1 := by
  have : gramAt D S τ = 1 := by
    show (HSpace.gram S).map (tauE D τ) = 1
    rw [h, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [this]
  exact ⟨by simp, by simp, by simpa using (Matrix.PosDef.one : Matrix.PosDef (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ))⟩

theorem vac_exists_gram_one {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) (S T : HSp D) (gS : S.gram = 1) (gT : T.gram = 1)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) :
    ∃ f : WO S T → ℂ, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) ΛS ΛT f := by
  obtain ⟨f, hf⟩ := GlobalTheory.VacuumO.vacExists D ψ θ hψ hθ (posSig S) (posSig T) (fun _ => 1) (fun _ => 1)
    (sigOK_posSig S gS) (sigOK_posSig T gT) (isCartanInv_one S gS) (isCartanInv_one T gT) ΛS ΛT hS hT
  exact ⟨f, hf.1, ⟨hf.2.inf, ⟨hf.2.theta.quasi, hf.2.theta.level, hf.2.theta.cont, hf.2.theta.smooth⟩, hf.2.lat,
    hf.2.fock, hf.2.norm⟩⟩

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {r : D.host.E}

theorem Hf_div_scale (hc : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ) (h : IsScale D cc r) {a d : ℕ} (z x : VC D a d) :
    Hf D (tor0 D D.host.ccK δ) (fun τ i j => z τ i j / embT D τ r) (fun τ i j => x τ i j / embT D τ r) =
      Hf D (tor0 D cc δ) z x := by
  have hr : r ≠ 0 := IsScale.ne_zero hc.1.1 h
  have hA := area_pos hc
  have hx := xiR_pos D
  have key : ∀ τ, Complex.normSq (embT D τ r) * area (lamOf D D.host.ccK δ) = area (lamOf D cc δ) := by
    intro τ
    have h1 := normSq_scale hc.1.1 h δ τ
    have h2 := normSq_scale D.host.ccK_ne_bot (isScale_one D) δ τ
    rw [map_one, mul_one] at h2
    rw [Complex.normSq_mul, h2] at h1
    have h3 : (2 * Formalism.L2.Pj.xiR D) * (Complex.normSq (embT D τ r) * area (lamOf D D.host.ccK δ)) =
        (2 * Formalism.L2.Pj.xiR D) * area (lamOf D cc δ) := by rw [← h1]; ring
    exact mul_left_cancel₀ (by positivity) h3
  have hL : ∀ c : Ideal (𝓞 D.host.K), (tor0 D c δ).abelian₂ = lamOf D c δ := fun _ => rfl
  rw [Formalism.MainNotions.TaylorLogMetric.Hf, Formalism.MainNotions.TaylorLogMetric.Hf, hL, hL, Finset.sum_div, Finset.sum_div]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_div, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_div, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  have ht : embT D τ r ≠ 0 := (map_ne_zero _).2 hr
  have htc : starRingEnd ℂ (embT D τ r) ≠ 0 := (map_ne_zero _).2 ht
  have hK : (area (lamOf D D.host.ccK δ) : ℂ) ≠ 0 := by
    have : 0 < area (lamOf D D.host.ccK δ) := by
      have := key τ
      have h0 : 0 < Complex.normSq (embT D τ r) := Complex.normSq_pos.2 ht
      nlinarith
    exact_mod_cast this.ne'
  rw [← key τ, map_div₀]
  push_cast
  rw [← Complex.mul_conj]
  field_simp

theorem th_div_scale (hc : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ) (h : IsScale D cc r) {a d : ℕ}
    {L Ls : GlobalTheory.InertSign.Lat D a} {L' Lt : GlobalTheory.InertSign.Lat D d}
    (hLa : ∀ x ∈ Formalism.MainNotions.TaylorLogMetric.La D (tor0 D cc δ) L L',
      (fun τ i j => x τ i j / embT D τ r) ∈ Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK δ) Ls Lt)
    {Φ : VC D a d → ℂ} (hΦ : Φ ∈ Th D (tor0 D D.host.ccK δ) Ls Lt) :
    (fun Y => Φ (fun τ i j => Y τ i j / embT D τ r)) ∈ Th D (tor0 D cc δ) L L' := by
  refine ⟨?_, ?_⟩
  · have hl : Differentiable ℂ (fun Y : VC D a d => (fun τ i j => Y τ i j / embT D τ r : VC D a d)) := by
      fun_prop
    exact hΦ.1.comp hl
  · intro x hx z
    have e1 := hΦ.2 _ (hLa x hx) (fun τ i j => z τ i j / embT D τ r)
    have hal : Formalism.MainNotions.TaylorLogMetric.al D (tor0 D cc δ) x =
        Formalism.MainNotions.TaylorLogMetric.al D (tor0 D D.host.ccK δ) (fun τ i j => x τ i j / embT D τ r) := by
      simp only [Formalism.MainNotions.TaylorLogMetric.al, Hf_div_scale hc h]
    have hadd : (fun τ i j => (z + x) τ i j / embT D τ r) =
        (fun τ i j => z τ i j / embT D τ r) + (fun τ i j => x τ i j / embT D τ r) := by
      funext τ i j
      simp [add_div]
    show _ = Φ fun τ i j => z τ i j / embT D τ r
    rw [← e1, hal]
    simp only [Formalism.MainNotions.TaylorLogMetric.U]
    rw [Hf_div_scale hc h, Hf_div_scale hc h, hadd]

end GlobalTheory.VacRead

namespace GlobalTheory.VacRead

theorem exists_vac_reads : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∃ e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d), e0 ≠ 0 ∧ ∃ f₀, Reads ψ θ hS hT cc δ r e0 f₀ := by
  intro D ψ θ S T a d hS hT cc δ r hset
  subst hS hT
  obtain ⟨hψ, hθ, gS, gT, crv, sc⟩ := hset
  have hc : cc ≠ ⊥ := crv.1.1
  have hr : r ≠ 0 := IsScale.ne_zero hc sc
  have hδ : δ ≠ 0 := delta_ne_zero crv
  have hS1 : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : GL (Fin S.rank) D.host.E).1 * S.gram *
      (1 : GL (Fin S.rank) D.host.E).1 = 1 := by
    rw [gS]; simp [Formalism.UG.cT]
  have hT1 : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : GL (Fin T.rank) D.host.E).1 * T.gram *
      (1 : GL (Fin T.rank) D.host.E).1 = 1 := by
    rw [gT]; simp [Formalism.UG.cT]
  have hLs : Formalism.MainNotions.StandardLatticesGL3.SD D (lsB D cc r S.rank) := GlobalTheory.T.invDifferentLatticeProductHermitian_isSelfDual D cc r S.rank hc sc
  have hLt : Formalism.MainNotions.StandardLatticesGL3.SD D (stdL D T.rank) := GlobalTheory.MovedVacuum.sd_stdL D T.rank
  obtain ⟨ΛS, hΛS, hSd⟩ := GlobalTheory.MovedDict.isSelfDualC_inV S 1 hS1 _ hLs
  obtain ⟨ΛT, hΛT, hTd⟩ := GlobalTheory.MovedDict.isSelfDualC_inV T 1 hT1 _ hLt
  obtain ⟨f, hf⟩ := vac_exists_gram_one ψ θ hψ hθ S T gS gT ΛS ΛT hSd hTd
  rw [hΛS, hΛT] at hf
  obtain ⟨Φ, hΦd, hΦ⟩ := GlobalTheory.FockPos.vacuum_real_entire ψ θ S T 1 1 _ _ hS1 hT1 f hf
  have hth := theta_of_unit_vacuum ψ θ S T 1 1 hS1 hT1 δ hδ _ _ hLs hLt f hf Φ hΦd hΦ
  have hLa : ∀ x ∈ Formalism.MainNotions.TaylorLogMetric.La D (tor0 D cc δ) (stdL D S.rank) (stdL D T.rank),
      (fun τ i j => x τ i j / embT D τ r) ∈ Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK δ) (lsB D cc r S.rank) (stdL D T.rank) := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := GlobalTheory.ThetaLatImage.La_sub hx
    have h2 := GlobalTheory.ThetaLatImage.pt_mem_La (δ := δ) (GlobalTheory.T.inv_smul_mem_rationalHomLatticeScaled_of_normScale D cc r S.rank T.rank hc sc z hz) 1
    convert h2 using 1
    funext τ i j
    rw [one_smul, GlobalTheory.ThetaLatImage.pt_apply, GlobalTheory.ThetaLatImage.pt_apply]
    have ht : embT D τ r ≠ 0 := (map_ne_zero _).2 hr
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀]
    field_simp
  have hG := th_div_scale crv sc hLa hth
  have hback : ∀ Z : VC D S.rank T.rank,
      (δ⁻¹ • fun τ i j => (δ * embT D τ r * Z τ i j) / embT D τ r : VC D S.rank T.rank) = Z := by
    intro Z
    funext τ i j
    have ht : embT D τ r ≠ 0 := (map_ne_zero _).2 hr
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  refine ⟨_, hG, ?_, f, (reads_iff crv sc _ f).2 ⟨hf.2.theta, fun w hw => ?_⟩⟩
  · intro h0
    apply GlobalTheory.StepMove.vacO_ne_zero hf
    refine GlobalTheory.TwistFactorCompare.theta_eq_zero_of_real hf.2.theta fun w hw => ?_
    rw [hΦ w hw]
    have e := congrFun h0 (fun τ i j => δ * embT D τ r * GlobalTheory.FockPos.zCo θ 1 1 w τ i j)
    simp only [Pi.zero_apply, hback] at e
    rw [e, mul_zero]
  · rw [hΦ w hw]
    simp only [hback]

end GlobalTheory.VacRead
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroStandardThetaLineReadAdelicStatement
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_standardThetaLine_read_adelic : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∃ e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d), e0 ≠ 0 ∧ ∃ f₀, Reads ψ θ hS hT cc δ r e0 f₀ := by
  first | exact @GlobalTheory.VacRead.exists_vac_reads | exact GlobalTheory.VacRead.exists_vac_reads | (intros; apply GlobalTheory.VacRead.exists_vac_reads <;> assumption)
end
