module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsSelfDualOfHasConductor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilObjectsInhabited
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoboundaryOfNormOneInSubalgebra
public import Formalism.PadicSubsetSums.StableGradedCounts.IRRPrimeToPartEqIff
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MapDofIterate
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsParahoricVec
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilTensorLiftConclusion

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousRhoApply
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousRhoApply
noncomputable section

open MeasureTheory Complex
open scoped Matrix Real RealInnerProductSpace InnerProductSpace

namespace GlobalTheory.RealWeil

variable {l : Type} [Fintype l]

omit [Fintype l] in
theorem continuous_pPart : Continuous (pPart : (l ⊕ l → ℝ) → EuclideanSpace ℝ l) := by
  unfold pPart
  fun_prop

omit [Fintype l] in
theorem continuous_qPart : Continuous (qPart : (l ⊕ l → ℝ) → EuclideanSpace ℝ l) := by
  unfold qPart
  fun_prop

theorem continuous_inner_rho_schwartz (φ f : Sch l) :
    Continuous fun w : l ⊕ l → ℝ => ⟪φ.toLp 2, rho w (f.toLp 2)⟫_ℂ := by
  have e : ∀ w : l ⊕ l → ℝ, ⟪φ.toLp 2, rho w (f.toLp 2)⟫_ℂ = ∫ x, starRingEnd ℂ (φ x) * rhoFun w f x := by
    intro w
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [φ.coeFn_toLp 2 volume, coeFn_rho w (f.toLp 2),
      rhoFun_congr w (f.coeFn_toLp 2 volume)] with x h1 h2 h3
    rw [h1, h2, h3]
    simp [mul_comm]
  simp only [e]
  refine continuous_of_dominated (bound := fun x => ‖φ x‖ * SchwartzMap.seminorm ℝ 0 0 f) (fun w => ?_)
    (fun w => .of_forall fun x => ?_) ((φ.integrable (μ := volume)).norm.mul_const _) (.of_forall fun x => ?_)
  · exact ((continuous_star.comp φ.continuous).mul
      ((continuous_phase w).mul (f.continuous.comp (continuous_add_const _)))).aestronglyMeasurable
  · rw [norm_mul, RCLike.norm_conj, rhoFun, norm_mul, norm_phase, one_mul]
    exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ f _) (norm_nonneg _)
  · simp only [rhoFun, phase]
    have := continuous_pPart (l := l)
    have := continuous_qPart (l := l)
    fun_prop

theorem continuous_rho_schwartz (f : Sch l) : Continuous fun w : l ⊕ l → ℝ => rho w (f.toLp 2) := by
  rw [continuous_iff_continuousAt]
  intro w₀
  set v : L2 l := f.toLp 2 with hv
  set g : L2 l := (rhoSch w₀ f).toLp 2 with hg
  have h0 : rho w₀ v = g := by
    refine Lp.ext ?_
    filter_upwards [coeFn_rho w₀ (f.toLp 2), rhoFun_congr w₀ (f.coeFn_toLp 2 volume),
      (rhoSch w₀ f).coeFn_toLp 2 volume] with x h1 h2 h3
    rw [h1, h2, h3, coe_rhoSch]
  have hsq : ∀ w, ‖rho w v - rho w₀ v‖ ^ 2 =
      2 * ‖v‖ ^ 2 - 2 * (⟪g, rho w v⟫_ℂ).re := by
    intro w
    rw [@norm_sub_sq ℂ, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map, inner_re_symm, h0,
      RCLike.re_to_complex]
    ring
  have hc : Continuous fun w => ‖rho w v - rho w₀ v‖ ^ 2 := by
    simp only [hsq]
    exact continuous_const.sub (continuous_const.mul (continuous_re.comp (continuous_inner_rho_schwartz (rhoSch w₀ f) f)))
  have ht := hc.tendsto w₀
  simp only [sub_self, norm_zero] at ht
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have := (Real.continuous_sqrt.tendsto _).comp ht
  simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this

theorem continuous_rho_prod : Continuous fun x : L2 l × (l ⊕ l → ℝ) => rho x.2 x.1 := by
  have hd : Dense (Set.range (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure (EuclideanSpace ℝ l)))) :=
    SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
  exact continuous_prod_of_dense_continuous_lipschitzWith (fun x : L2 l × (l ⊕ l → ℝ) => rho x.2 x.1) 1 hd
    (by rintro _ ⟨f, rfl⟩; exact continuous_rho_schwartz f) fun w => (rho w).lipschitz

theorem continuous_rho : ∀ (l : Type) [Fintype l] (v : L2 l), Continuous fun w : l ⊕ l → ℝ => rho w v :=
  fun l _ v => (continuous_rho_prod (l := l)).comp (f := fun w : l ⊕ l → ℝ => ((v, w) : L2 l × (l ⊕ l → ℝ)))
    (Continuous.prodMk continuous_const continuous_id)

end GlobalTheory.RealWeil
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousRhoApplyStatement
open scoped Matrix
open MeasureTheory GlobalTheory.RealWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_rho_apply : ∀ (l : Type) [Fintype l] (v : L2 l), Continuous fun w : l ⊕ l → ℝ => rho w v := by
  first | exact @GlobalTheory.RealWeil.continuous_rho | exact GlobalTheory.RealWeil.continuous_rho | (intros; apply GlobalTheory.RealWeil.continuous_rho <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquaringOpenAtOneOfCompleteTwoNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquaringOpenAtOneOfCompleteTwoNeZero
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology

namespace GlobalTheory

theorem sqOpen_of_two_ne_zero : ∀ (K : Type) [NormedField K] [CompleteSpace K], (2 : K) ≠ 0 → SqOpen K := by
  intro K _ _ h2 V hV
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hV
  set c := ‖(2:K)⁻¹‖ with hc
  have hc0 : 0 ≤ c := norm_nonneg _
  set ρ := min (ε / 2) (1 / (4 * c + 1)) with hρ
  have hρ0 : 0 < ρ := lt_min (by linarith) (by positivity)
  have hρε : ρ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hρc : 2 * ρ * c ≤ 1 / 2 := by
    have h1 : ρ ≤ 1 / (4 * c + 1) := min_le_right _ _
    have h4 : 0 < 4 * c + 1 := by positivity
    have h5 : ρ * (4 * c + 1) ≤ 1 := by rwa [le_div_iff₀ h4] at h1
    nlinarith
  set δ := ρ / (2 * c + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  have hcδ : c * δ ≤ ρ / 2 := by
    have h : 0 < 2 * c + 1 := by positivity
    have h' : δ * (2 * c + 1) = ρ := div_mul_cancel₀ _ (ne_of_gt h)
    nlinarith
  refine ⟨Metric.closedBall 1 δ, Metric.closedBall_mem_nhds _ hδ0, ?_⟩
  intro r hr
  have hr' : ‖r - 1‖ ≤ δ := by simpa [dist_eq_norm] using hr
  set f : K → K := fun μ => μ - (μ ^ 2 - r) * (2:K)⁻¹ with hfdef
  have h22 : (2:K) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  have hdiff : ∀ μ₁ μ₂ : K, f μ₁ - f μ₂ = (μ₁ - μ₂) * ((1 - μ₁) + (1 - μ₂)) * (2:K)⁻¹ := by
    intro μ₁ μ₂
    simp only [hfdef]
    linear_combination (-(μ₁ - μ₂)) * h22
  have hf1 : f 1 - 1 = (r - 1) * (2:K)⁻¹ := by
    simp only [hfdef]; ring
  set s := Metric.closedBall (1:K) ρ with hs
  have hlip : ∀ μ₁ ∈ s, ∀ μ₂ ∈ s, ‖f μ₁ - f μ₂‖ ≤ (1 / 2) * ‖μ₁ - μ₂‖ := by
    intro μ₁ h1 μ₂ h2'
    rw [hdiff, norm_mul, norm_mul]
    have a1 : ‖1 - μ₁‖ ≤ ρ := by
      rw [norm_sub_rev]; simpa [hs, dist_eq_norm] using h1
    have a2 : ‖1 - μ₂‖ ≤ ρ := by
      rw [norm_sub_rev]; simpa [hs, dist_eq_norm] using h2'
    have a3 : ‖(1 - μ₁) + (1 - μ₂)‖ ≤ 2 * ρ := (norm_add_le _ _).trans (by linarith)
    have a4 : 0 ≤ ‖μ₁ - μ₂‖ := norm_nonneg _
    have a5 : 0 ≤ ‖(1 - μ₁) + (1 - μ₂)‖ := norm_nonneg _
    calc ‖μ₁ - μ₂‖ * ‖(1 - μ₁) + (1 - μ₂)‖ * c ≤ ‖μ₁ - μ₂‖ * (2 * ρ) * c := by gcongr
      _ = ‖μ₁ - μ₂‖ * (2 * ρ * c) := by ring
      _ ≤ ‖μ₁ - μ₂‖ * (1 / 2) := by gcongr
      _ = (1 / 2) * ‖μ₁ - μ₂‖ := by ring
  have h1s : (1:K) ∈ s := Metric.mem_closedBall_self hρ0.le
  have hmaps : Set.MapsTo f s s := by
    intro μ hμ
    have hl := hlip μ hμ 1 h1s
    have hμ' : ‖μ - 1‖ ≤ ρ := by simpa [hs, dist_eq_norm] using hμ
    have hf1' : ‖f 1 - 1‖ ≤ c * δ := by
      rw [hf1, norm_mul, mul_comm]; gcongr
    have key : ‖f μ - 1‖ ≤ ρ := by
      calc ‖f μ - 1‖ = ‖(f μ - f 1) + (f 1 - 1)‖ := by congr 1; ring
        _ ≤ ‖f μ - f 1‖ + ‖f 1 - 1‖ := norm_add_le _ _
        _ ≤ (1 / 2) * ρ + c * δ := by gcongr; exact hl.trans (by gcongr)
        _ ≤ ρ := by linarith
    simpa [hs, dist_eq_norm] using key
  have hcomplete : IsComplete s := Metric.isClosed_closedBall.isComplete
  have hcon : ContractingWith (1 / 2 : NNReal) (hmaps.restrict f s s) := by
    constructor
    · rw [← NNReal.coe_lt_coe]; push_cast; norm_num
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      simp only [Set.MapsTo.val_restrict_apply, Subtype.dist_eq, dist_eq_norm]
      push_cast
      exact hlip _ x.2 _ y.2
  obtain ⟨μ, hμs, hfix, -⟩ :=
    hcon.exists_fixedPoint' hcomplete hmaps h1s (edist_ne_top _ _)
  refine ⟨μ, hball (Metric.closedBall_subset_ball hρε hμs), ?_⟩
  have hfix' : f μ = μ := hfix
  have hz : (μ ^ 2 - r) * (2:K)⁻¹ = 0 := by
    simp only [hfdef] at hfix'
    linear_combination -hfix'
  rcases mul_eq_zero.1 hz with h | h
  · linear_combination h
  · exact absurd h (inv_ne_zero h2)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquaringOpenAtOneOfCompleteTwoNeZeroStatement
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squaringOpenAtOne_of_complete_two_ne_zero : ∀ (K : Type) [NormedField K] [CompleteSpace K], (2 : K) ≠ 0 → SqOpen K := by
  first | exact @GlobalTheory.sqOpen_of_two_ne_zero | exact GlobalTheory.sqOpen_of_two_ne_zero | (intros; apply GlobalTheory.sqOpen_of_two_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTwistedNormOneMulCardFixedUnits
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTwistedNormOneMulCardFixedUnits
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem card_nrm_one_mul_card_fixed (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F']
    (s : F' ≃ₐ[F] F') (hs : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) (n : ℕ)
    (B : Subalgebra F' (Matrix (Fin n) (Fin n) F')) (hB : ∀ x ∈ B, x.map s ∈ B) :
    Nat.card {ε : GL (Fin n) F' // (ε : Matrix (Fin n) (Fin n) F') ∈ B ∧ nrm s ε = 1} *
      Nat.card {x : GL (Fin n) F // ((incl F F' n x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B} =
      Nat.card {x : GL (Fin n) F' // (x : Matrix (Fin n) (Fin n) F') ∈ B} := by
  obtain ⟨hfix, hinj, hconj, -, -⟩ := GlobalTheory.T.galoisTwistedNormGL_basic_properties F F' s hs n
  have h90 := GlobalTheory.T.exists_coboundary_of_norm_one_in_subalgebra F F' s hs n B hB
  have hsB : ∀ x : GL (Fin n) F', (x : Matrix (Fin n) (Fin n) F') ∈ B →
      ((galAct F F' n s x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B := fun x hx => hB _ hx
  have hinv : ∀ x : GL (Fin n) F', (x : Matrix (Fin n) (Fin n) F') ∈ B →
      ((x⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B := by
    intro x hx
    obtain ⟨k, hk, hxk⟩ := (isOfFinOrder_of_finite x).exists_pow_eq_one
    have hx' : x⁻¹ = x ^ (k - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel hk, hxk]
    rw [hx', Units.val_pow_eq_pow_val]
    exact pow_mem hx _
  have hmul : ∀ a b : GL (Fin n) F', (a : Matrix (Fin n) (Fin n) F') ∈ B → (b : Matrix (Fin n) (Fin n) F') ∈ B →
      ((a * b : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B := by
    intro a b ha hb
    rw [Units.val_mul]
    exact mul_mem ha hb
  have hn1 : nrm s (1 : GL (Fin n) F') = 1 := by
    unfold nrm nrmG
    apply List.prod_eq_one
    intro y hy
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
    exact map_one _
  have hnorm : ∀ x : GL (Fin n) F', nrm s (x⁻¹ * galAct F F' n s x) = 1 := by
    intro x
    have h := hconj 1 x
    rw [mul_one, hn1, mul_one, inv_mul_cancel] at h
    exact h
  let U := {x : GL (Fin n) F' // (x : Matrix (Fin n) (Fin n) F') ∈ B}
  let N := {ε : GL (Fin n) F' // (ε : Matrix (Fin n) (Fin n) F') ∈ B ∧ nrm s ε = 1}
  let U₀ := {x : GL (Fin n) F // ((incl F F' n x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B}
  let φ : U → N := fun x =>
    ⟨x.1⁻¹ * galAct F F' n s x.1, hmul _ _ (hinv _ x.2) (hsB _ x.2), hnorm _⟩
  have hsec : ∀ ε : N, ∃ x : U, φ x = ε := by
    intro ε
    obtain ⟨x, hx, he⟩ := h90 ε.1 ε.2.1 ε.2.2
    exact ⟨⟨x, hx⟩, Subtype.ext he.symm⟩
  choose sec hsec using hsec
  have hfixI : ∀ z : GL (Fin n) F, galAct F F' n s (incl F F' n z) = incl F F' n z :=
    fun z => (hfix _).2 ⟨z, rfl⟩
  let f : ∀ ε : N, U₀ → {x : U // φ x = ε} := fun ε z =>
    ⟨⟨incl F F' n z.1 * (sec ε).1, hmul _ _ z.2 (sec ε).2⟩, by
      refine Eq.trans ?_ (hsec ε)
      apply Subtype.ext
      show (incl F F' n z.1 * (sec ε).1)⁻¹ * galAct F F' n s (incl F F' n z.1 * (sec ε).1) =
        (sec ε).1⁻¹ * galAct F F' n s (sec ε).1
      rw [map_mul, hfixI]
      group⟩
  have hbij : ∀ ε : N, Function.Bijective (f ε) := by
    intro ε
    constructor
    · intro z w h
      have h' : incl F F' n z.1 * (sec ε).1 = incl F F' n w.1 * (sec ε).1 :=
        congrArg (fun u : {x : U // φ x = ε} => u.1.1) h
      exact Subtype.ext (hinj (mul_right_cancel h'))
    · rintro ⟨y, hy⟩
      set x := sec ε with hxdef
      have hyx : φ y = φ x := by rw [hy, hsec ε]
      have h1 : y.1⁻¹ * galAct F F' n s y.1 = x.1⁻¹ * galAct F F' n s x.1 :=
        congrArg Subtype.val hyx
      have h2 : galAct F F' n s (y.1 * x.1⁻¹) = y.1 * x.1⁻¹ := by
        rw [map_mul, map_inv]
        calc galAct F F' n s y.1 * (galAct F F' n s x.1)⁻¹
            = y.1 * (y.1⁻¹ * galAct F F' n s y.1) * (galAct F F' n s x.1)⁻¹ := by group
          _ = y.1 * (x.1⁻¹ * galAct F F' n s x.1) * (galAct F F' n s x.1)⁻¹ := by rw [h1]
          _ = y.1 * x.1⁻¹ := by group
      obtain ⟨z, hz⟩ := (hfix _).1 h2
      have hzB : ((incl F F' n z : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B := by
        rw [hz]; exact hmul _ _ y.2 (hinv _ x.2)
      refine ⟨⟨z, hzB⟩, ?_⟩
      apply Subtype.ext; apply Subtype.ext
      show incl F F' n z * x.1 = y.1
      rw [hz]; group
  let E : U ≃ N × U₀ := (Equiv.sigmaFiberEquiv φ).symm.trans
    (Equiv.sigmaEquivProdOfEquiv fun ε => (Equiv.ofBijective (f ε) (hbij ε)).symm)
  rw [← Nat.card_prod]
  exact (Nat.card_congr E).symm

end GlobalTheory.Shin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTwistedNormOneMulCardFixedUnitsStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_twistedNorm_one_mul_card_fixed_units : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (B : Subalgebra F' (Matrix (Fin n) (Fin n) F')), (∀ x ∈ B, x.map s ∈ B) → Nat.card {ε : GL (Fin n) F' // (ε : Matrix (Fin n) (Fin n) F') ∈ B ∧ nrm s ε = 1} * Nat.card {x : GL (Fin n) F // ((incl F F' n x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B} = Nat.card {x : GL (Fin n) F' // (x : Matrix (Fin n) (Fin n) F') ∈ B} := by
  first | (exact @GlobalTheory.Shin.card_nrm_one_mul_card_fixed) | (exact GlobalTheory.Shin.card_nrm_one_mul_card_fixed) | (intros; apply GlobalTheory.Shin.card_nrm_one_mul_card_fixed  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjOfCharpolyLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearIndependentIterates
open Polynomial Matrix

namespace GlobalTheory.ConjLocal

variable {R : Type} [CommRing R] {n : ℕ}

def iterMat (Y : Matrix (Fin n) (Fin n) R) (v : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => (Y ^ (j : ℕ) *ᵥ v) i

def compMat (Q : R[X]) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if (j : ℕ) + 1 < n then (if (i : ℕ) = (j : ℕ) + 1 then 1 else 0) else -Q.coeff i

theorem exists_linearIndependent_iterates {K : Type} [Field K] (M : Matrix (Fin n) (Fin n) K)
    (hs : M.charpoly.Separable) :
    ∃ v : Fin n → K, LinearIndependent K (fun j : Fin n => (M ^ (j : ℕ)) *ᵥ v) := by
  obtain ⟨e, -, he⟩ := Formalism.IrreducibleCountingLemmas.Z.exists_annihilator_eq (toLin' M) (by rw [charpoly_toLin']; exact hs)
    (toLin' M).charpoly dvd_rfl
  refine ⟨e, ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro c hc
  let q : K[X] := ∑ j : Fin n, monomial (j : ℕ) (c j)
  have ha : ∀ p : K[X], aeval (toLin' M) p = toLin' (aeval M p) := fun p =>
    aeval_algHom_apply (toLinAlgEquiv' (R := K) (n := Fin n)) M p
  have hq0 : aeval (toLin' M) q e = 0 := by
    rw [ha, toLin'_apply]
    have haq : aeval M q = ∑ j : Fin n, c j • M ^ (j : ℕ) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [q, map_sum, aeval_monomial, Algebra.smul_def]
    rw [haq, Matrix.sum_mulVec]
    simpa [Matrix.smul_mulVec] using hc
  have hdvd := he q hq0
  rw [charpoly_toLin'] at hdvd
  have hdeg : q.degree < M.charpoly.degree := by
    rw [degree_eq_natDegree M.charpoly_monic.ne_zero, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun j _ => ?_
    exact lt_of_le_of_lt (degree_monomial_le _ _) (by exact_mod_cast j.2)
  have hq : q = 0 := eq_zero_of_dvd_of_degree_lt hdvd hdeg
  intro j
  have := congrArg (fun p : K[X] => p.coeff j) hq
  simp only [q, Polynomial.finsetSum_coeff, coeff_monomial_apply, Fin.val_inj,
    coeff_zero] at this
  simpa using this

end GlobalTheory.ConjLocal

namespace GlobalTheory.ConjLocal

variable {R : Type} [CommRing R] {n : ℕ}

theorem pow_dim_mulVec [Nontrivial R] (Y : Matrix (Fin n) (Fin n) R) (v : Fin n → R) (i : Fin n) :
    (Y ^ n *ᵥ v) i = -∑ k : Fin n, Y.charpoly.coeff k * (Y ^ (k : ℕ) *ᵥ v) i := by
  have h0 := Matrix.aeval_self_charpoly Y
  have hm := Y.charpoly_monic.as_sum
  rw [charpoly_natDegree_eq_dim, Fintype.card_fin] at hm
  rw [hm] at h0
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_pow, aeval_X, map_sum, map_mul, aeval_C] at h0
  have := congrArg (fun M => (M *ᵥ v) i) h0
  simp only [add_mulVec, sum_mulVec, Pi.add_apply, Finset.sum_apply, zero_mulVec, Pi.zero_apply] at this
  rw [eq_neg_iff_add_eq_zero, ← this, ← Fin.sum_univ_eq_sum_range]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mulVec_mulVec, algebraMap_eq_diagonal, mulVec_diagonal]
  rfl

theorem mul_iterMat [Nontrivial R] (Y : Matrix (Fin n) (Fin n) R) (v : Fin n → R) :
    Y * iterMat Y v = iterMat Y v * compMat Y.charpoly := by
  ext i j
  have hl : (Y * iterMat Y v) i j = (Y ^ ((j : ℕ) + 1) *ᵥ v) i := by
    rw [pow_succ', ← mulVec_mulVec]; rfl
  rw [hl, Matrix.mul_apply]
  simp only [iterMat, compMat, Matrix.of_apply]
  split_ifs with hj
  · rw [Finset.sum_eq_single ⟨(j : ℕ) + 1, hj⟩]
    · simp
    · intro b _ hb
      rw [if_neg (fun h => hb (Fin.ext h)), mul_zero]
    · simp
  · have : (j : ℕ) + 1 = n := by omega
    rw [this, pow_dim_mulVec, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

theorem exists_isUnit_det_iterMat [IsLocalRing R] (Y : Matrix (Fin n) (Fin n) R) (hs : Y.charpoly.Separable) :
    ∃ v : Fin n → R, IsUnit (iterMat Y v).det := by
  let f := IsLocalRing.residue R
  have hs' : (Y.map f).charpoly.Separable := by rw [Matrix.charpoly_map]; exact hs.map
  obtain ⟨w, hw⟩ := exists_linearIndependent_iterates (Y.map f) hs'
  choose v hv using fun i => IsLocalRing.residue_surjective (w i)
  refine ⟨v, ?_⟩
  have hmap : (iterMat Y v).map f = iterMat (Y.map f) w := by
    ext i j
    simp only [iterMat, Matrix.map_apply, Matrix.of_apply, ← Matrix.map_pow, RingHom.map_mulVec]
    congr 1
    funext k
    exact hv k
  have hunit : IsUnit (iterMat (Y.map f) w) := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    convert hw using 1
    funext j
    ext i
    rfl
  apply isUnit_of_map_unit f
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap]
  exact (Matrix.isUnit_iff_isUnit_det _).1 hunit

end GlobalTheory.ConjLocal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjOfCharpolyLocal
open Polynomial Matrix

namespace GlobalTheory.ConjLocal

theorem conj_of_charpoly_local : ∀ (R : Type) [CommRing R] [IsLocalRing R] (n : ℕ) (Y Y' : Matrix (Fin n) (Fin n) R),
    Y.charpoly = Y'.charpoly → Y.charpoly.Separable →
    ∃ g : GL (Fin n) R, Y' = (g⁻¹ : GL (Fin n) R).val * Y * g.val := by
  intro R _ _ n Y Y' h hs
  obtain ⟨v, hv⟩ := exists_isUnit_det_iterMat Y hs
  obtain ⟨v', hv'⟩ := exists_isUnit_det_iterMat Y' (h ▸ hs)
  let u : GL (Fin n) R := nonsingInvUnit (iterMat Y v) hv
  let u' : GL (Fin n) R := nonsingInvUnit (iterMat Y' v') hv'
  have e1 : Y * u.val = u.val * compMat Y.charpoly := mul_iterMat Y v
  have e2 : Y' * u'.val = u'.val * compMat Y.charpoly := by rw [h]; exact mul_iterMat Y' v'
  refine ⟨u * u'⁻¹, ?_⟩
  rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul]
  calc Y' = Y' * u'.val * (u'⁻¹ : GL (Fin n) R).val := by rw [mul_assoc, Units.mul_inv, mul_one]
    _ = u'.val * compMat Y.charpoly * (u'⁻¹ : GL (Fin n) R).val := by rw [e2]
    _ = u'.val * ((u⁻¹ : GL (Fin n) R).val * (u.val * compMat Y.charpoly)) * (u'⁻¹ : GL (Fin n) R).val := by
      rw [← mul_assoc (u⁻¹ : GL (Fin n) R).val, Units.inv_mul, one_mul]
    _ = u'.val * ((u⁻¹ : GL (Fin n) R).val * (Y * u.val)) * (u'⁻¹ : GL (Fin n) R).val := by rw [e1]
    _ = _ := by simp only [mul_assoc]

end GlobalTheory.ConjLocal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjOfCharpolyLocalStatement
open Polynomial Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_of_charpoly_eq_of_separable_local : ∀ (R : Type) [CommRing R] [IsLocalRing R] (n : ℕ) (Y Y' : Matrix (Fin n) (Fin n) R), Y.charpoly = Y'.charpoly → Y.charpoly.Separable → ∃ g : GL (Fin n) R, Y' = (g⁻¹ : GL (Fin n) R).val * Y * g.val := by
  first | exact @GlobalTheory.ConjLocal.conj_of_charpoly_local | exact GlobalTheory.ConjLocal.conj_of_charpoly_local | (intros; apply GlobalTheory.ConjLocal.conj_of_charpoly_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvalEqOfMultiplicativeOnPoints
open scoped TensorProduct

namespace GlobalTheory

open scoped TensorProduct in
private lemma eq_zero_of_forall_algHom_apply_eq_zero_of_isReduced {C V : Type} [Field C] [IsAlgClosed C] [CommRing V]
    [Algebra C V] [Module.Finite C V] [IsReduced V] (v : V) (hv : ∀ z : V →ₐ[C] C, z v = 0) :
    v = 0 := by
  haveI : IsArtinianRing V := IsArtinianRing.of_finite C V
  have hmem : v ∈ (⊥ : Ideal V).jacobson := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    rintro m ⟨-, hm⟩
    letI : Field (V ⧸ m) := Ideal.Quotient.field m
    have hsurj : Function.Surjective (algebraMap C (V ⧸ m)) := IsSepClosed.algebraMap_surjective C _
    let eqv : C ≃ₐ[C] V ⧸ m := AlgEquiv.ofBijective (Algebra.ofId C (V ⧸ m))
      ⟨(algebraMap C (V ⧸ m)).injective, hsurj⟩
    have h := hv (eqv.symm.toAlgHom.comp (Ideal.Quotient.mkₐ C m))
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgEquiv.coe_toAlgHom,
      AlgHom.coe_coe] at h
    exact Ideal.Quotient.eq_zero_iff_mem.mp ((map_eq_zero_iff _ eqv.symm.injective).mp h)
  rw [IsArtinianRing.jacobson_eq_radical] at hmem
  obtain ⟨n, hn⟩ := hmem
  exact IsReduced.eq_zero v ⟨n, by simpa using hn⟩

open scoped TensorProduct in
private lemma exists_eq_one_and_eq_zero_of_ne_algHom {C V : Type} [Field C] [CommRing V] [Algebra C V]
    [Fintype (V →ₐ[C] C)] (z : V →ₐ[C] C) :
    ∃ w : V, z w = 1 ∧ ∀ z' : V →ₐ[C] C, z' ≠ z → z' w = 0 := by
  have hsep : ∀ z' : V →ₐ[C] C, z' ≠ z → ∃ a : V, z a ≠ z' a := by
    intro z' hz'
    by_contra h
    push_neg at h
    exact hz' (AlgHom.ext fun a => (h a).symm)
  classical
  let u : (V →ₐ[C] C) → V := fun z' =>
    if h : z' ≠ z then
      (z (hsep z' h).choose - z' (hsep z' h).choose)⁻¹ •
        ((hsep z' h).choose - algebraMap C V (z' (hsep z' h).choose))
    else 1
  have hu : ∀ z', z (u z') = 1 := by
    intro z'
    by_cases h : z' ≠ z
    · simp only [u, dif_pos h, map_smul, map_sub, AlgHom.commutes, Algebra.algebraMap_self,
        RingHom.id_apply, smul_eq_mul]
      exact inv_mul_cancel₀ (sub_ne_zero.mpr (hsep z' h).choose_spec)
    · simp only [u]
      rw [dite_eq_right h, map_one]
  have hu' : ∀ z', z' ≠ z → z' (u z') = 0 := by
    intro z' h
    simp only [u]
    rw [dif_pos h]
    simp
  refine ⟨∏ z' ∈ Finset.univ.erase z, u z', ?_, ?_⟩
  · rw [map_prod]
    exact Finset.prod_eq_one fun z' _ => hu z'
  · intro z' hz'
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hz', Finset.mem_univ _⟩) (hu' z' hz')

open scoped TensorProduct in
private lemma sum_sum_mul_sub_mul_mul_eq_zero_of_sum_mul_eq {C ι : Type} [Field C] [Fintype ι] (c X Y : ι → C)
    (M : ι → ι → ι → C)
    (h : ∑ k, c k * ∑ i, ∑ j, M k i j * (X i * Y j) = (∑ i, c i * X i) * ∑ j, c j * Y j) :
    ∑ j, (∑ i, (∑ k, c k * M k i j - c i * c j) * X i) * Y j = 0 := by
  have e1 : ∑ j, (∑ i, (∑ k, c k * M k i j - c i * c j) * X i) * Y j =
      ∑ k, c k * ∑ i, ∑ j, M k i j * (X i * Y j) - (∑ i, c i * X i) * ∑ j, c j * Y j := by
    simp only [Finset.sum_mul, Finset.mul_sum, sub_mul, Finset.sum_sub_distrib]
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
    congr 1
    · conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      conv_rhs => rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e1, h, sub_self]


open scoped TensorProduct in
theorem _root_.GlobalTheory.exists_eval_eq_of_multiplicative_on_points : ∀ (O C A : Type) [CommRing O] [IsDomain O] [Field C] [IsAlgClosed C] [Algebra O C] [IsFractionRing O C] [IsIntegrallyClosed O] [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Free O A], IsReduced (C ⊗[O] A) → ∀ (Δ : A →ₐ[O] A ⊗[O] A) (ε : A →ₐ[O] O) (κ : (A →ₐ[O] C) → C), (∀ x y : A →ₐ[O] C, κ ((Algebra.TensorProduct.lift x y (fun _ _ => Commute.all _ _)).comp Δ) = κ x * κ y) → κ ((Algebra.ofId O C).comp ε) = 1 → ∃ b : A, ∀ x : A →ₐ[O] C, x b = κ x := by
  intro O C A _ _ _ _ _ _ _ _ _ _ _ hred Δ ε κ hmul _
  classical
  let e := Module.Free.chooseBasis O A
  let eC : Module.Basis (Module.Free.ChooseBasisIndex O A) C (C ⊗[O] A) :=
    Algebra.TensorProduct.basis C e
  let ext : (A →ₐ[O] C) → (C ⊗[O] A →ₐ[C] C) := fun x =>
    Algebra.TensorProduct.lift (Algebra.ofId C C) x (fun _ _ => Commute.all _ _)
  let res : (C ⊗[O] A →ₐ[C] C) → (A →ₐ[O] C) := fun z =>
    (z.restrictScalars O).comp Algebra.TensorProduct.includeRight
  have hres : ∀ x, res (ext x) = x := by
    intro x
    ext a
    simp [res, ext]
  have hevC : ∀ (z : C ⊗[O] A →ₐ[C] C) (a : Module.Free.ChooseBasisIndex O A → C),
      z (∑ i, a i • eC i) = ∑ i, a i * res z (e i) := by
    intro z a
    set_option synthInstance.maxHeartbeats 100000 in
      simp [eC, res, map_sum, Algebra.TensorProduct.basis_apply]
  have hcoord : ∀ a : Module.Free.ChooseBasisIndex O A → C,
      (∀ x : A →ₐ[O] C, ∑ i, a i * x (e i) = 0) → a = 0 := by
    intro a ha
    have hv : ∑ i, a i • eC i = 0 := by
      refine eq_zero_of_forall_algHom_apply_eq_zero_of_isReduced (C := C) _ fun z => ?_
      rw [hevC]
      exact ha (res z)
    funext i
    have hi := congrArg (fun v => eC.repr v i) hv
    simpa [Finsupp.single_apply] using hi
  haveI : Finite (C ⊗[O] A →ₐ[C] C) := (linearIndependent_toLinearMap C (C ⊗[O] A) C).finite
  letI : Fintype (C ⊗[O] A →ₐ[C] C) := Fintype.ofFinite _
  choose w hw1 hw0 using fun z : C ⊗[O] A →ₐ[C] C => exists_eq_one_and_eq_zero_of_ne_algHom z
  let b' : C ⊗[O] A := ∑ z, κ (res z) • w z
  let c := eC.repr b'
  have hval : ∀ x, κ x = ∑ i, c i * x (e i) := by
    intro x
    have h1 : ext x b' = κ x := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [b', map_sum, map_smul, smul_eq_mul]
      rw [Finset.sum_eq_single (ext x)]
      · rw [hw1, mul_one, hres]
      · intro z _ hz
        rw [hw0 z (ext x) (Ne.symm hz), mul_zero]
      · simp
    rw [← h1]
    conv_lhs => rw [← eC.sum_repr b']
    rw [hevC, hres]
  let m : Module.Free.ChooseBasisIndex O A → Module.Free.ChooseBasisIndex O A →
      Module.Free.ChooseBasisIndex O A → O := fun k i j => (e.tensorProduct e).repr (Δ (e k)) (i, j)
  have hprod : ∀ (x y : A →ₐ[O] C) k,
      (Algebra.TensorProduct.lift x y (fun _ _ => Commute.all _ _)) (Δ (e k)) =
        ∑ i, ∑ j, algebraMap O C (m k i j) * (x (e i) * y (e j)) := by
    intro x y k
    conv_lhs => rw [← (e.tensorProduct e).sum_repr (Δ (e k))]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Module.Basis.tensorProduct_apply,
      Algebra.smul_def, Fintype.sum_prod_type, map_mul, AlgHom.commutes,
      Algebra.TensorProduct.lift_tmul, m]
  have key : ∀ x y : A →ₐ[O] C, ∑ j, (∑ i, (∑ k, c k * algebraMap O C (m k i j) - c i * c j) *
      x (e i)) * y (e j) = 0 := by
    intro x y
    have h := hmul x y
    simp only [hval, AlgHom.comp_apply, hprod] at h
    exact sum_sum_mul_sub_mul_mul_eq_zero_of_sum_mul_eq c (fun i => x (e i)) (fun j => y (e j))
      (fun k i j => algebraMap O C (m k i j)) h
  have hrel : ∀ i j, c i * c j = ∑ k, c k * algebraMap O C (m k i j) := by
    have h1 : ∀ j, ∀ x : A →ₐ[O] C,
        ∑ i, (∑ k, c k * algebraMap O C (m k i j) - c i * c j) * x (e i) = 0 := by
      intro j x
      exact congrFun (hcoord (fun j => ∑ i, (∑ k, c k * algebraMap O C (m k i j) - c i * c j) *
        x (e i)) (key x)) j
    intro i j
    have h2 := congrFun (hcoord (fun i => ∑ k, c k * algebraMap O C (m k i j) - c i * c j) (h1 j)) i
    exact (sub_eq_zero.mp h2).symm
  let M : Submodule O C := Submodule.span O (insert 1 (Set.range c))
  have hcM : ∀ i, c i ∈ M := fun i => Submodule.subset_span (Set.mem_insert_of_mem 1 ⟨i, rfl⟩)
  have hoM : (1 : C) ∈ M := Submodule.subset_span (Set.mem_insert 1 _)
  have hMM : M * M ≤ M := by
    rw [Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨s, hs, t, ht, rfl⟩
    rcases hs with rfl | ⟨i, rfl⟩ <;> rcases ht with rfl | ⟨j, rfl⟩ <;> dsimp only
    · rw [one_mul]
      exact hoM
    · rw [one_mul]
      exact hcM j
    · rw [mul_one]
      exact hcM i
    · rw [hrel]
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [mul_comm, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (hcM k)
  let S : Subalgebra O C :=
    M.toSubalgebra hoM fun u v hu hv => hMM (Submodule.mul_mem_mul hu hv)
  have hfg : (Subalgebra.toSubmodule S).FG := Submodule.fg_span ((Set.finite_range c).insert 1)
  have hint : ∀ i, ∃ o : O, algebraMap O C o = c i := fun i =>
    IsIntegrallyClosed.isIntegral_iff.mp (IsIntegral.of_mem_of_fg S hfg _ (hcM i))
  choose o ho using hint
  refine ⟨∑ i, o i • e i, fun x => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hval, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Algebra.smul_def, ho]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacTwistMapSurjective
noncomputable section

open GlobalTheory.SmGL (twist twist_apply)

namespace GlobalTheory.TypeTwo.EndTwist

section General

variable {F G V W : Type} [Field F] [Group G] [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

def twistSubIso (ρ : Representation F G V) (χ : G →* Fˣ) :
    Subrepresentation ρ ≃o Subrepresentation (twist ρ χ) where
  toFun S := ⟨S.toSubmodule, fun g v hv => by
    rw [twist_apply]
    exact S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule g hv)⟩
  invFun S := ⟨S.toSubmodule, fun g v hv => by
    have h := S.toSubmodule.smul_mem ((χ g)⁻¹ : Fˣ).val (S.apply_mem_toSubmodule g hv)
    have h2 : ((χ g)⁻¹ : Fˣ).val • (twist ρ χ g v) = ρ g v := by
      rw [twist_apply, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
    rwa [h2] at h⟩
  left_inv S := rfl
  right_inv S := rfl
  map_rel_iff' := Iff.rfl

theorem isIrreducible_twist {ρ : Representation F G V} (h : ρ.IsIrreducible) (χ : G →* Fˣ) :
    (twist ρ χ).IsIrreducible :=
  (OrderIso.isSimpleOrder_iff (twistSubIso ρ χ)).1 h

end General

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n a b V : Type} [Fintype n] [DecidableEq n] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [AddCommGroup V] [Module ℂ V]

end Local

section Ends

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V : Type} [AddCommGroup V] [Module ℂ V]

end Ends

end GlobalTheory.TypeTwo.EndTwist
end
end
