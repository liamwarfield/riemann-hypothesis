module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSLTwoPermutedModularFamilyAlgebraClosure
public import ReciprocityTheory.Chebotarev.EulerSum
public import Formalism.LatticeTheta.Statement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSeminormTranslateSubLineDerivLe
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeftMulMatrixTransfer
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothHolomorphicInSigmaFamilyAdd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothHolomorphicInSigmaFamilyAdd
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.HeckeTwo.GoodAdd

variable {Φ : Type} [Fintype Φ]

open Classical in
theorem wirt_contDiffOn {U : Set (Φ → ℂ)} (hU : IsOpen U) {f : (Φ → ℂ) → ℂ}
    (hf : ContDiffOn ℝ ∞ f U) (τ : Φ) (b : Bool) : ContDiffOn ℝ ∞ (wirt τ b f) U := by
  have hd : ContDiffOn ℝ ∞ (fun y => fderiv ℝ f y) U :=
    hf.fderiv_of_isOpen hU (by simp)
  have h1 : ContDiffOn ℝ ∞ (fun y => fderiv ℝ f y (Pi.single τ 1)) U :=
    hd.clm_apply contDiffOn_const
  have h2 : ContDiffOn ℝ ∞ (fun y => fderiv ℝ f y (Pi.single τ I)) U :=
    hd.clm_apply contDiffOn_const
  unfold wirt
  exact (h1.add (contDiffOn_const.mul h2)).div_const _

theorem wirtWord_contDiffOn {U : Set (Φ → ℂ)} (hU : IsOpen U) (w : List (Φ × Bool)) {f : (Φ → ℂ) → ℂ}
    (hf : ContDiffOn ℝ ∞ f U) : ContDiffOn ℝ ∞ (wirtWord w f) U := by
  induction w with
  | nil => simpa [wirtWord_nil] using hf
  | cons a w ih => rw [wirtWord_cons]; exact wirt_contDiffOn hU ih _ _

theorem wirt_congr {U : Set (Φ → ℂ)} (hU : IsOpen U) {f g : (Φ → ℂ) → ℂ} (h : Set.EqOn f g U)
    (τ : Φ) (b : Bool) : Set.EqOn (wirt τ b f) (wirt τ b g) U := by
  intro z hz
  have he : f =ᶠ[nhds z] g := Filter.eventuallyEq_of_mem (hU.mem_nhds hz) h
  simp only [wirt, he.fderiv_eq]

theorem wirt_add {f g : (Φ → ℂ) → ℂ} {z : Φ → ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) (τ : Φ) (b : Bool) :
    wirt τ b (f + g) z = wirt τ b f z + wirt τ b g z := by
  have h : fderiv ℝ (f + g) z = fderiv ℝ f z + fderiv ℝ g z := fderiv_add hf hg
  simp only [wirt, h, ContinuousLinearMap.add_apply]
  ring

theorem wirtWord_add {U : Set (Φ → ℂ)} (hU : IsOpen U) (w : List (Φ × Bool)) {f g : (Φ → ℂ) → ℂ}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) :
    Set.EqOn (wirtWord w (f + g)) (wirtWord w f + wirtWord w g) U := by
  induction w with
  | nil => intro z _; rfl
  | cons a w ih =>
    intro z hz
    rw [wirtWord_cons, wirtWord_cons, wirtWord_cons, wirt_congr hU ih _ _ hz]
    have hf' := wirtWord_contDiffOn hU w hf
    have hg' := wirtWord_contDiffOn hU w hg
    exact wirt_add ((hf'.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))
      ((hg'.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)) _ _

theorem upperHalf_isOpen (F : Type) [Field F] [NumberField F] : IsOpen (upperHalf F) := by
  have : upperHalf F = ⋂ τ : Emb F, {z : Emb F → ℂ | 0 < (z τ).im} := by
    ext z; simp [upperHalf]
  rw [this]
  exact isOpen_iInter_of_finite fun τ =>
    isOpen_lt continuous_const (Complex.continuous_im.comp (continuous_apply τ))

end GlobalTheory.HeckeTwo.GoodAdd

theorem GlobalTheory.HeckeTwo.isGood_add : ∀ (F : Type) [Field F] [NumberField F] (P Q : ℂ → (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) → ℂ), GlobalTheory.HeckeTwo.IsGood P → GlobalTheory.HeckeTwo.IsGood Q → GlobalTheory.HeckeTwo.IsGood (fun σ z => P σ z + Q σ z) := by
  intro F _ _ P Q hP hQ
  have hU := GlobalTheory.HeckeTwo.GoodAdd.upperHalf_isOpen F
  refine ⟨fun σ hσ => (hP.1 σ hσ).add (hQ.1 σ hσ), fun w z hz => ?_⟩
  refine ((hP.2 w z hz).add (hQ.2 w z hz)).congr fun σ hσ => ?_
  exact GlobalTheory.HeckeTwo.GoodAdd.wirtWord_add hU w (hP.1 σ hσ) (hQ.1 σ hσ) hz
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothHolomorphicInSigmaFamilyAddStatement
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSmoothHolomorphicInSigmaFamily_add : ∀ (F : Type) [Field F] [NumberField F] (P Q : ℂ → (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) → ℂ), GlobalTheory.HeckeTwo.IsGood P → GlobalTheory.HeckeTwo.IsGood Q → GlobalTheory.HeckeTwo.IsGood (fun σ z => P σ z + Q σ z) := by
  first | exact @GlobalTheory.HeckeTwo.isGood_add | exact GlobalTheory.HeckeTwo.isGood_add | (intros; apply GlobalTheory.HeckeTwo.isGood_add <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateOpenSubgroupsFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateOpenSubgroupsFinite
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.LocalBoxIndicator

theorem indicator_mem_SB {X : Type} [TopologicalSpace X] {S : Set X} (hcl : IsClopen S) (hco : IsCompact S) :
    Set.indicator S (1 : X → ℂ) ∈ GlobalTheory.WeilM.SB X := by
  classical
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ S
    · filter_upwards [hcl.isOpen.mem_nhds hx] with y hy
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]; rfl
    · filter_upwards [hcl.isClosed.isOpen_compl.mem_nhds hx] with y hy
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
  · exact HasCompactSupport.intro' hco hcl.isClosed (fun y hy => Set.indicator_of_notMem hy _)

theorem indicator_box_translate : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (B : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F)),
    (∀ v, IsOpen (B v : Set (v.adicCompletion F))) →
    (∀ v, (B v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F) →
    (∀ᶠ v in Filter.cofinite, (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F) →
    ∀ r : κ → FiniteAdeleRing (𝓞 F) F,
      (∀ v, Set.indicator {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ B v}
        (1 : (κ → v.adicCompletion F) → ℂ) ∈ GlobalTheory.WeilM.SB (κ → v.adicCompletion F)) ∧
      ∀ᶠ v in Filter.cofinite, Set.indicator {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ B v}
        (1 : (κ → v.adicCompletion F) → ℂ) = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
  intro F _ _ κ _ B hBo hBO hBcof r
  refine ⟨fun v => ?_, ?_⟩
  · set c : κ → v.adicCompletion F := fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) with hc
    have hS : {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ B v}
        = (Homeomorph.subRight c) ⁻¹' (Set.univ.pi fun _ => (B v : Set (v.adicCompletion F))) := by
      ext x
      simp [Set.mem_pi, hc]
    have hBc : IsCompact (B v : Set (v.adicCompletion F)) :=
      (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v).of_isClosed_subset
        (AddSubgroup.isClosed_of_isOpen (B v) (hBo v)) (hBO v)
    have hT : IsClopen (Set.univ.pi fun _ : κ => (B v : Set (v.adicCompletion F))) :=
      ⟨isClosed_set_pi fun _ _ => AddSubgroup.isClosed_of_isOpen (B v) (hBo v),
        isOpen_set_pi Set.finite_univ fun _ _ => hBo v⟩
    rw [hS]
    exact indicator_mem_SB (hT.preimage (Homeomorph.subRight c).continuous)
      ((Homeomorph.subRight c).isCompact_preimage.2 (isCompact_univ_pi fun _ => hBc))
  · have hr : ∀ᶠ v in Filter.cofinite, ∀ i, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ v.adicCompletionIntegers F :=
      Filter.eventually_all.2 fun i => (r i).2
    filter_upwards [hr, hBcof] with v hv hBv
    congr 1
    ext x
    simp only [Set.mem_setOf_eq]
    refine forall_congr' fun i => ?_
    rw [← SetLike.mem_coe, hBv, SetLike.mem_coe]
    constructor
    · intro h
      have := (v.adicCompletionIntegers F).add_mem _ _ h (hv i)
      simpa using this
    · intro h
      exact (v.adicCompletionIntegers F).sub_mem h (hv i)

end GlobalTheory.LocalBoxIndicator

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateOpenSubgroupsFiniteStatement
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translate_open_subgroups_finite : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (B : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F)),
    (∀ v, IsOpen (B v : Set (v.adicCompletion F))) →
    (∀ v, (B v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F) →
    (∀ᶠ v in Filter.cofinite, (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F) →
    ∀ r : κ → FiniteAdeleRing (𝓞 F) F,
      (∀ v, Set.indicator {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ B v}
        (1 : (κ → v.adicCompletion F) → ℂ) ∈ GlobalTheory.WeilM.SB (κ → v.adicCompletion F)) ∧
      ∀ᶠ v in Filter.cofinite, Set.indicator {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (r i) ∈ B v}
        (1 : (κ → v.adicCompletion F) → ℂ) = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
  first | exact @GlobalTheory.LocalBoxIndicator.indicator_box_translate | exact GlobalTheory.LocalBoxIndicator.indicator_box_translate | (intros; apply GlobalTheory.LocalBoxIndicator.indicator_box_translate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionsCoeffwiseConjugateRingClosure
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionsCoeffwiseConjugateRingClosure
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators

namespace GlobalTheory.QFam

variable {g : ℂ ≃+* ℂ} {N : ℕ}

theorem QConj.const (g : ℂ ≃+* ℂ) (N : ℕ) (c : ℂ) : QConj g N (fun _ => c) fun _ => g c := by
  refine ⟨fun n => if n = 0 then c else 0, HasQ.const N c, ?_⟩
  have e : (fun n : ℕ => g (if n = 0 then c else 0)) = fun n => if n = 0 then g c else 0 := by
    funext n
    split_ifs <;> simp
  rw [e]
  exact HasQ.const N (g c)

theorem QConj.add {f f' h h' : ℍ → ℂ} (hf : QConj g N f f') (hh : QConj g N h h') :
    QConj g N (fun τ => f τ + h τ) fun τ => f' τ + h' τ := by
  obtain ⟨a, ha, ha'⟩ := hf
  obtain ⟨b, hb, hb'⟩ := hh
  refine ⟨fun n => a n + b n, ha.add hb, ?_⟩
  simpa only [map_add (f := _)] using ha'.add hb'

theorem QConj.sub {f f' h h' : ℍ → ℂ} (hf : QConj g N f f') (hh : QConj g N h h') :
    QConj g N (fun τ => f τ - h τ) fun τ => f' τ - h' τ := by
  obtain ⟨a, ha, ha'⟩ := hf
  obtain ⟨b, hb, hb'⟩ := hh
  refine ⟨fun n => a n - b n, ha.sub hb, ?_⟩
  simpa only [map_sub] using ha'.sub hb'

theorem map_conv (g : ℂ ≃+* ℂ) (a b : ℕ → ℂ) (n : ℕ) :
    g (conv a b n) = conv (fun n => g (a n)) (fun n => g (b n)) n := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [conv, map_sum, map_mul]

theorem QConj.mul (hN : 0 < N) {f f' h h' : ℍ → ℂ} (hf : QConj g N f f') (hh : QConj g N h h') :
    QConj g N (fun τ => f τ * h τ) fun τ => f' τ * h' τ := by
  obtain ⟨a, ha, ha'⟩ := hf
  obtain ⟨b, hb, hb'⟩ := hh
  refine ⟨conv a b, ha.mul_conv hb, ?_⟩
  have e : (fun n => g (conv a b n)) = conv (fun n => g (a n)) (fun n => g (b n)) :=
    funext (map_conv g a b)
  rw [e]
  exact ha'.mul_conv hb'

theorem QConj.pow (hN : 0 < N) {f f' : ℍ → ℂ} (k : ℕ) (hf : QConj g N f f') :
    QConj g N (fun τ => f τ ^ k) fun τ => f' τ ^ k := by
  induction k with
  | zero =>
    simp only [pow_zero]
    simpa using QConj.const g N 1
  | succ k ih =>
    simp only [pow_succ]
    exact QConj.mul hN ih hf

theorem QConj.sum {κ : Type} (s : Finset κ) {f f' : κ → ℍ → ℂ}
    (h : ∀ k ∈ s, QConj g N (f k) (f' k)) :
    QConj g N (fun τ => ∑ k ∈ s, f k τ) fun τ => ∑ k ∈ s, f' k τ := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp only [Finset.sum_empty]
    simpa using QConj.const g N 0
  · intro j s hj ih h
    simp only [Finset.sum_insert hj]
    exact QConj.add (h j (Finset.mem_insert_self j s))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem QConj.prod (hN : 0 < N) {κ : Type} (s : Finset κ) {f f' : κ → ℍ → ℂ}
    (h : ∀ k ∈ s, QConj g N (f k) (f' k)) :
    QConj g N (fun τ => ∏ k ∈ s, f k τ) fun τ => ∏ k ∈ s, f' k τ := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp only [Finset.prod_empty]
    simpa using QConj.const g N 1
  · intro j s hj ih h
    simp only [Finset.prod_insert hj]
    exact QConj.mul hN (h j (Finset.mem_insert_self j s))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem qConj_ring : ∀ (g : ℂ ≃+* ℂ) (N : ℕ), 0 < N → (∀ c : ℂ, QConj g N (fun _ => c) fun _ => g c) ∧ (∀ f f' h h', QConj g N f f' → QConj g N h h' → QConj g N (fun τ => f τ + h τ) fun τ => f' τ + h' τ) ∧ (∀ f f' h h', QConj g N f f' → QConj g N h h' → QConj g N (fun τ => f τ - h τ) fun τ => f' τ - h' τ) ∧ (∀ f f' h h', QConj g N f f' → QConj g N h h' → QConj g N (fun τ => f τ * h τ) fun τ => f' τ * h' τ) ∧ (∀ f f' (k : ℕ), QConj g N f f' → QConj g N (fun τ => f τ ^ k) fun τ => f' τ ^ k) ∧ (∀ (κ : Type) (s : Finset κ) (f f' : κ → ℍ → ℂ), (∀ k ∈ s, QConj g N (f k) (f' k)) → (QConj g N (fun τ => ∑ k ∈ s, f k τ) fun τ => ∑ k ∈ s, f' k τ) ∧ QConj g N (fun τ => ∏ k ∈ s, f k τ) fun τ => ∏ k ∈ s, f' k τ) := by
  intro g N hN
  exact ⟨fun c => QConj.const g N c,
    fun _ _ _ _ hf hh => QConj.add hf hh,
    fun _ _ _ _ hf hh => QConj.sub hf hh,
    fun _ _ _ _ hf hh => QConj.mul hN hf hh,
    fun _ _ k hf => QConj.pow hN k hf,
    fun _ s _ _ h => ⟨QConj.sum s h, QConj.prod hN s h⟩⟩

end GlobalTheory.QFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionsCoeffwiseConjugateRingClosureStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qExpansionsCoeffwiseConjugate_ring_closure : ∀ (g : ℂ ≃+* ℂ) (N : ℕ), 0 < N → (∀ c : ℂ, QConj g N (fun _ => c) fun _ => g c) ∧ (∀ f f' h h', QConj g N f f' → QConj g N h h' → QConj g N (fun τ => f τ + h τ) fun τ => f' τ + h' τ) ∧ (∀ f f' h h', QConj g N f f' → QConj g N h h' → QConj g N (fun τ => f τ - h τ) fun τ => f' τ - h' τ) ∧ (∀ f f' h h', QConj g N f f' → QConj g N h h' → QConj g N (fun τ => f τ * h τ) fun τ => f' τ * h' τ) ∧ (∀ f f' (k : ℕ), QConj g N f f' → QConj g N (fun τ => f τ ^ k) fun τ => f' τ ^ k) ∧ (∀ (κ : Type) (s : Finset κ) (f f' : κ → ℍ → ℂ), (∀ k ∈ s, QConj g N (f k) (f' k)) → (QConj g N (fun τ => ∑ k ∈ s, f k τ) fun τ => ∑ k ∈ s, f' k τ) ∧ QConj g N (fun τ => ∏ k ∈ s, f k τ) fun τ => ∏ k ∈ s, f' k τ) := by
  first | exact @GlobalTheory.QFam.qConj_ring | exact GlobalTheory.QFam.qConj_ring | (intros; apply GlobalTheory.QFam.qConj_ring <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelUnipotentAntidiagonalCorner
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelUnipotentAntidiagonalCorner
open GlobalTheory.WeilM
open scoped Matrix

namespace GlobalTheory.SiegelUnip
open Matrix

variable {R : Type} [CommRing R] {n : ℕ}

abbrev adR (n : ℕ) (R : Type) [CommRing R] : Matrix (Fin n) (Fin n ⊕ Fin n) R := fromCols 1 (-1)

abbrev adC (n : ℕ) (R : Type) [CommRing R] : Matrix (Fin n ⊕ Fin n) (Fin n) R := fromRows 1 (-1)

abbrev dgC (n : ℕ) (R : Type) [CommRing R] : Matrix (Fin n ⊕ Fin n) (Fin n) R := diagCols (Fin n)

theorem adR_mul_dgC : adR n R * dgC n R = 0 := by
  simp [diagCols, fromCols_mul_fromRows]

theorem adR_mul_adC : adR n R * adC n R = 2 • (1 : Matrix (Fin n) (Fin n) R) := by
  simp [fromCols_mul_fromRows, two_smul]

theorem dbl_mul_dgC (J₀ : Matrix (Fin n) (Fin n) R) : dbl J₀ * dgC n R = adC n R * J₀ := by
  rw [dbl, dgC, diagCols, fromBlocks_mul_fromRows, adC, fromRows_mul]
  simp

theorem dgC_tr_mul_dbl (J₀ : Matrix (Fin n) (Fin n) R) : (dgC n R)ᵀ * dbl J₀ = J₀ * adR n R := by
  rw [dbl, dgC, diagCols, transpose_fromRows, fromCols_mul_fromBlocks, adR, mul_fromCols]
  simp

theorem dgC_tr_dbl_dgC (J₀ : Matrix (Fin n) (Fin n) R) : (dgC n R)ᵀ * dbl J₀ * dgC n R = 0 := by
  rw [dgC_tr_mul_dbl, Matrix.mul_assoc, adR_mul_dgC, Matrix.mul_zero]

theorem adR_tr : (adR n R)ᵀ = adC n R := by
  simp [adR, adC, transpose_fromCols]

theorem dgC_map {R₀ : Type} [CommRing R₀] [Algebra R₀ R] (c : R →ₐ[R₀] R) : (dgC n R).map c = dgC n R := by
  rw [dgC, diagCols, fromRows_map, Matrix.map_one _ (map_zero c) (map_one c)]

theorem adR_map {R₀ : Type} [CommRing R₀] [Algebra R₀ R] (c : R →ₐ[R₀] R) : (adR n R).map c = adR n R := by
  rw [adR, fromCols_map, Matrix.map_neg _ (map_neg c), Matrix.map_one _ (map_zero c) (map_one c)]

end GlobalTheory.SiegelUnip


open Matrix GlobalTheory.SiegelUnip in
theorem GlobalTheory.siegel_unip_corner : ∀ {R₀ R : Type} [CommRing R₀] [CommRing R] [Algebra R₀ R] [Invertible (2 : R)] (c : R →ₐ[R₀] R) {n : ℕ} (J₀ : Matrix (Fin n) (Fin n) R) (x : Matrix (Fin n) (Fin n) R), xᵀ * J₀ + J₀ * x.map c = 0 → ∃ p : UG c (dbl J₀), (p.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) * diagCols (Fin n) = diagCols (Fin n) * (1 : Matrix (Fin n) (Fin n) R) ∧ ∀ h : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R, Matrix.fromCols (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) * (h * p.1.1) * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) = Matrix.fromCols (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) * h * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) + Matrix.fromCols (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) * h * diagCols (Fin n) * x := by
  intro R₀ R _ _ _ _ c n J₀ x hx
  set N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R := GlobalTheory.SiegelUnip.dgC n R * x * GlobalTheory.SiegelUnip.adR n R with hN
  have hNN : N * N = 0 := by
    rw [hN, show GlobalTheory.SiegelUnip.dgC n R * x * GlobalTheory.SiegelUnip.adR n R * (GlobalTheory.SiegelUnip.dgC n R * x * GlobalTheory.SiegelUnip.adR n R) = GlobalTheory.SiegelUnip.dgC n R * x * (GlobalTheory.SiegelUnip.adR n R * GlobalTheory.SiegelUnip.dgC n R) * x * GlobalTheory.SiegelUnip.adR n R by
      simp only [Matrix.mul_assoc], GlobalTheory.SiegelUnip.adR_mul_dgC, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul]
  have hsq : (⅟(2 : R) • N) * (⅟(2 : R) • N) = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hNN, smul_zero, smul_zero]
  have hPQ : (1 + ⅟(2 : R) • N) * (1 - ⅟(2 : R) • N) = 1 := by
    rw [add_mul, one_mul, mul_sub, mul_one, hsq]; abel
  have hQP : (1 - ⅟(2 : R) • N) * (1 + ⅟(2 : R) • N) = 1 := by
    rw [sub_mul, one_mul, mul_add, mul_one, hsq]; abel
  have hc2 : c (⅟(2 : R)) = ⅟(2 : R) := by
    refine (invOf_eq_right_inv ?_).symm
    have := congrArg c (mul_invOf_self (2 : R))
    rwa [map_mul, map_ofNat, map_one] at this
  have hNc : N.map c = GlobalTheory.SiegelUnip.dgC n R * x.map c * GlobalTheory.SiegelUnip.adR n R := by
    change (GlobalTheory.SiegelUnip.dgC n R * x * GlobalTheory.SiegelUnip.adR n R).map (c.toRingHom : R → R) = _
    rw [Matrix.map_mul, Matrix.map_mul]
    exact congrArg₂ _ (congrArg₂ _ (GlobalTheory.SiegelUnip.dgC_map c) rfl) (GlobalTheory.SiegelUnip.adR_map c)
  have hPc : (1 + ⅟(2 : R) • N).map c = 1 + ⅟(2 : R) • (GlobalTheory.SiegelUnip.dgC n R * x.map c * GlobalTheory.SiegelUnip.adR n R) := by
    rw [Matrix.map_add _ (map_add c), Matrix.map_one _ (map_zero c) (map_one c), ← hNc]
    congr 1
    ext i j
    simp [hc2]
  have hNt : Nᵀ = GlobalTheory.SiegelUnip.adC n R * xᵀ * (GlobalTheory.SiegelUnip.dgC n R)ᵀ := by
    rw [hN, Matrix.transpose_mul, Matrix.transpose_mul, GlobalTheory.SiegelUnip.adR_tr, Matrix.mul_assoc]
  have hmem : (1 + ⅟(2 : R) • N)ᵀ * dbl J₀ * (1 + ⅟(2 : R) • N).map c = dbl J₀ := by
    rw [hPc, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul, hNt]
    have e1 : dbl J₀ * (GlobalTheory.SiegelUnip.dgC n R * x.map c * GlobalTheory.SiegelUnip.adR n R) = GlobalTheory.SiegelUnip.adC n R * (J₀ * x.map c) * GlobalTheory.SiegelUnip.adR n R := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, GlobalTheory.SiegelUnip.dbl_mul_dgC]; simp only [Matrix.mul_assoc]
    have e2 : GlobalTheory.SiegelUnip.adC n R * xᵀ * (GlobalTheory.SiegelUnip.dgC n R)ᵀ * dbl J₀ = GlobalTheory.SiegelUnip.adC n R * (xᵀ * J₀) * GlobalTheory.SiegelUnip.adR n R := by
      rw [Matrix.mul_assoc, GlobalTheory.SiegelUnip.dgC_tr_mul_dbl]; simp only [Matrix.mul_assoc]
    have e3 : GlobalTheory.SiegelUnip.adC n R * xᵀ * (GlobalTheory.SiegelUnip.dgC n R)ᵀ * dbl J₀ * (GlobalTheory.SiegelUnip.dgC n R * x.map c * GlobalTheory.SiegelUnip.adR n R) = 0 := by
      rw [show GlobalTheory.SiegelUnip.adC n R * xᵀ * (GlobalTheory.SiegelUnip.dgC n R)ᵀ * dbl J₀ * (GlobalTheory.SiegelUnip.dgC n R * x.map c * GlobalTheory.SiegelUnip.adR n R) =
        GlobalTheory.SiegelUnip.adC n R * xᵀ * ((GlobalTheory.SiegelUnip.dgC n R)ᵀ * dbl J₀ * GlobalTheory.SiegelUnip.dgC n R) * x.map c * GlobalTheory.SiegelUnip.adR n R by simp only [Matrix.mul_assoc],
        GlobalTheory.SiegelUnip.dgC_tr_dbl_dgC]
      simp
    have e4 : GlobalTheory.SiegelUnip.adC n R * (J₀ * x.map c) * GlobalTheory.SiegelUnip.adR n R + GlobalTheory.SiegelUnip.adC n R * (xᵀ * J₀) * GlobalTheory.SiegelUnip.adR n R = 0 := by
      rw [← Matrix.add_mul, ← Matrix.mul_add, add_comm, hx, Matrix.mul_zero, Matrix.zero_mul]
    calc (1 + ⅟(2 : R) • (GlobalTheory.SiegelUnip.adC n R * xᵀ * (GlobalTheory.SiegelUnip.dgC n R)ᵀ)) * dbl J₀ * (1 + ⅟(2 : R) • (GlobalTheory.SiegelUnip.dgC n R * x.map c * GlobalTheory.SiegelUnip.adR n R))
        = dbl J₀ + ⅟(2 : R) • (dbl J₀ * (GlobalTheory.SiegelUnip.dgC n R * x.map c * GlobalTheory.SiegelUnip.adR n R)) +
          ⅟(2 : R) • (GlobalTheory.SiegelUnip.adC n R * xᵀ * (GlobalTheory.SiegelUnip.dgC n R)ᵀ * dbl J₀) +
          (⅟(2 : R) * ⅟(2 : R)) • (GlobalTheory.SiegelUnip.adC n R * xᵀ * (GlobalTheory.SiegelUnip.dgC n R)ᵀ * dbl J₀ * (GlobalTheory.SiegelUnip.dgC n R * x.map c * GlobalTheory.SiegelUnip.adR n R)) := by
          simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul]; abel
      _ = dbl J₀ + ⅟(2 : R) • (GlobalTheory.SiegelUnip.adC n R * (J₀ * x.map c) * GlobalTheory.SiegelUnip.adR n R + GlobalTheory.SiegelUnip.adC n R * (xᵀ * J₀) * GlobalTheory.SiegelUnip.adR n R) := by
          rw [e3, e1, e2, smul_zero, add_zero, smul_add, add_assoc]
      _ = dbl J₀ := by rw [e4, smul_zero, add_zero]
  let u : GL (Fin n ⊕ Fin n) R := ⟨1 + ⅟(2 : R) • N, 1 - ⅟(2 : R) • N, hPQ, hQP⟩
  refine ⟨⟨u, hmem⟩, ?_, fun h => ?_⟩
  · have hp : ((⟨u, hmem⟩ : UG c (dbl J₀)) : GL (Fin n ⊕ Fin n) R).1 = 1 + ⅟(2 : R) • N := rfl
    rw [hp]
    have hpd : N * GlobalTheory.SiegelUnip.dgC n R = 0 := by rw [hN, Matrix.mul_assoc, GlobalTheory.SiegelUnip.adR_mul_dgC, Matrix.mul_zero]
    have key : ((1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) + ⅟(2 : R) • N) * GlobalTheory.SiegelUnip.dgC n R =
        GlobalTheory.SiegelUnip.dgC n R * (1 : Matrix (Fin n) (Fin n) R) := by
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, hpd, smul_zero, add_zero, Matrix.mul_one]
    exact key
  · have hp : ((⟨u, hmem⟩ : UG c (dbl J₀)) : GL (Fin n ⊕ Fin n) R).1 = 1 + ⅟(2 : R) • N := rfl
    rw [hp]
    have e : GlobalTheory.SiegelUnip.adR n R * (h * N) * GlobalTheory.SiegelUnip.adC n R = (2 : R) • (GlobalTheory.SiegelUnip.adR n R * h * GlobalTheory.SiegelUnip.dgC n R * x) := by
      rw [hN, show GlobalTheory.SiegelUnip.adR n R * (h * (GlobalTheory.SiegelUnip.dgC n R * x * GlobalTheory.SiegelUnip.adR n R)) * GlobalTheory.SiegelUnip.adC n R = GlobalTheory.SiegelUnip.adR n R * h * GlobalTheory.SiegelUnip.dgC n R * x * (GlobalTheory.SiegelUnip.adR n R * GlobalTheory.SiegelUnip.adC n R) by
        simp only [Matrix.mul_assoc], GlobalTheory.SiegelUnip.adR_mul_adC, Matrix.mul_smul, Matrix.mul_one, two_smul, two_smul]
    rw [mul_add, mul_one, Matrix.mul_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, e, smul_smul,
      invOf_mul_self, one_smul, Matrix.mul_assoc (GlobalTheory.SiegelUnip.adR n R) h]
    rfl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelUnipotentAntidiagonalCornerStatement
open GlobalTheory.WeilM
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelUnipotent_antidiagonal_corner : ∀ {R₀ R : Type} [CommRing R₀] [CommRing R] [Algebra R₀ R] [Invertible (2 : R)] (c : R →ₐ[R₀] R) {n : ℕ} (J₀ : Matrix (Fin n) (Fin n) R) (x : Matrix (Fin n) (Fin n) R), xᵀ * J₀ + J₀ * x.map c = 0 → ∃ p : UG c (dbl J₀), (p.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) * diagCols (Fin n) = diagCols (Fin n) * (1 : Matrix (Fin n) (Fin n) R) ∧ ∀ h : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R, Matrix.fromCols (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) * (h * p.1.1) * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) = Matrix.fromCols (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) * h * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) + Matrix.fromCols (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) * h * diagCols (Fin n) * x := by
  first | exact @GlobalTheory.siegel_unip_corner | exact GlobalTheory.siegel_unip_corner | (intros; apply GlobalTheory.siegel_unip_corner <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEisensteinConstantTermPartDifferentiableOn
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEisensteinConstantTermPartDifferentiableOn
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwo.APart

variable {F : Type} [Field F] [NumberField F]

theorem exists_den (I : FractionalIdeal (𝓞 F)⁰ F) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ b ∈ I, ∃ x : 𝓞 F, (x : F) = (d : F) * b := by
  obtain ⟨d, hd, h⟩ := I.isFractional
  refine ⟨d, nonZeroDivisors.ne_zero hd, fun b hb => ?_⟩
  obtain ⟨x, hx⟩ := h b hb
  exact ⟨x, by rw [← Algebra.smul_def] at *; simpa using hx⟩

theorem summable_norm_rpow (I : FractionalIdeal (𝓞 F)⁰ F) {s : ℝ} (hs : 1 < s) :
    Summable (fun c : Quotient (unitRel I) => |((Algebra.norm ℚ c.out.1 : ℚ) : ℝ)| ^ (-s)) := by
  obtain ⟨d, hd, hdI⟩ := exists_den I
  choose g hg using fun c : Quotient (unitRel I) => hdI c.out.1 c.out.2.1
  have hd' : (d : F) ≠ 0 := by exact_mod_cast hd
  have hinj : Function.Injective (fun c : Quotient (unitRel I) => Ideal.span ({g c} : Set (𝓞 F))) := by
    intro c c' h
    obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.1 h
    have h2 := congrArg (fun x : 𝓞 F => (x : F)) hu
    push_cast at h2
    refine Quotient.out_equiv_out.1 ⟨u, ?_⟩
    apply mul_left_cancel₀ hd'
    linear_combination ((u : 𝓞 F) : F) * hg c - hg c' - h2
  have hS := (ReciprocityTheory.Cheb.summable_absNorm_rpow_ideal F hs).comp_injective hinj
  have hNd : 0 < |((Algebra.norm ℚ (d : F) : ℚ) : ℝ)| := by
    simp [Algebra.norm_eq_zero_iff, hd']
  refine (hS.mul_left (|((Algebra.norm ℚ (d : F) : ℚ) : ℝ)| ^ s)).congr fun c => ?_
  have e1 : ((Algebra.norm ℤ (g c) : ℤ) : ℚ) = Algebra.norm ℚ (d : F) * Algebra.norm ℚ c.out.1 := by
    rw [Algebra.coe_norm_int, hg, map_mul]
  have e2 : ((Algebra.norm ℤ (g c) : ℤ) : ℝ) =
      ((Algebra.norm ℚ (d : F) : ℚ) : ℝ) * ((Algebra.norm ℚ c.out.1 : ℚ) : ℝ) := by
    exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) e1
  have hN : ((Ideal.absNorm (Ideal.span ({g c} : Set (𝓞 F))) : ℕ) : ℝ) =
      |((Algebra.norm ℚ (d : F) : ℚ) : ℝ)| * |((Algebra.norm ℚ c.out.1 : ℚ) : ℝ)| := by
    rw [Ideal.absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs, e2, abs_mul]
  simp only [Function.comp_apply]
  rw [hN, Real.mul_rpow (abs_nonneg _) (abs_nonneg _), ← mul_assoc, ← Real.rpow_add hNd, add_neg_cancel,
    Real.rpow_zero, one_mul]

theorem inv_natPow_rpow_neg_half_even_eq_pow {x : ℝ} (hx : 0 < x) (t : ℝ) : x ^ (-(2 + 2 * t)) = x⁻¹ ^ 2 * x ^ (-2 * t) := by
  rw [show -(2 + 2 * t) = -(2 : ℝ) + -2 * t by ring, Real.rpow_add hx, Real.rpow_neg hx.le, Real.rpow_two, inv_pow]

theorem rpow_le_add {x : ℝ} (hx : 0 < x) {r t R : ℝ} (hr : r ≤ t) (hR : t ≤ R) :
    x ^ (-2 * t) ≤ x ^ (-2 * r) + x ^ (-2 * R) := by
  rcases le_total x 1 with h | h
  · have := Real.rpow_le_rpow_of_exponent_ge hx h (show -2 * R ≤ -2 * t by linarith)
    linarith [Real.rpow_nonneg hx.le (-2 * r)]
  · have := Real.rpow_le_rpow_of_exponent_le h (show -2 * t ≤ -2 * r by linarith)
    linarith [Real.rpow_nonneg hx.le (-2 * R)]

variable [IsTotallyReal F]

theorem prod_latPt_zero (a : F) :
    ∏ τ : Emb F, latPt 0 (a, 0) τ =
      (2 * (Real.pi : ℂ) * I) ^ Fintype.card (Emb F) * ((Algebra.norm ℚ a : ℚ) : ℂ) := by
  simp only [latPt, Pi.zero_apply, map_zero, ofReal_zero, zero_mul, add_zero]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, prod_emb]

end GlobalTheory.HeckeTwo.APart


open GlobalTheory.HeckeTwo.APart in
theorem GlobalTheory.HeckeTwo.aPart_differentiableOn : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F), DifferentiableOn ℂ (GlobalTheory.HeckeTwo.aPart 𝔞) GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.halfPlane := by
  intro F _ _ _ 𝔞
  set P : Quotient (unitRel (latM 𝔞)) → ℂ := fun c => ∏ τ : Emb F, latPt 0 ((c.out.1 : F), (0 : F)) τ with hP
  have hP0 : ∀ c, P c ≠ 0 := fun c => by
    simp only [hP, prod_latPt_zero]
    refine mul_ne_zero (pow_ne_zero _ ?_) ?_
    · have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      exact mul_ne_zero (mul_ne_zero two_ne_zero hπ) I_ne_zero
    · exact_mod_cast (Algebra.norm_ne_zero_iff).2 c.out.2.2
  set K : ℝ := ‖(2 * (Real.pi : ℂ) * I) ^ Fintype.card (Emb F)‖ with hK
  have hK0 : 0 < K := by
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact norm_pos_iff.2 (pow_ne_zero _ (mul_ne_zero (mul_ne_zero two_ne_zero hπ) I_ne_zero))
  have hnP : ∀ c, ‖P c‖ = K * |((Algebra.norm ℚ c.out.1 : ℚ) : ℝ)| := fun c => by
    simp only [hP, prod_latPt_zero, norm_mul, hK]
    congr 1
    rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
  have hsum : ∀ t : ℝ, 1 < t → Summable fun c => ‖P c‖ ^ (-t) := fun t ht =>
    ((summable_norm_rpow (latM 𝔞) ht).mul_left (K ^ (-t))).congr fun c => by
      rw [hnP, Real.mul_rpow hK0.le (abs_nonneg _)]
  have hnorm : ∀ c σ, ‖eisTerm 2 σ 0 ((c.out.1 : F), (0 : F))‖ = ‖P c‖⁻¹ ^ 2 * ‖P c‖ ^ (-2 * σ.re) := fun c σ => by
    show ‖(P c)⁻¹ ^ 2 * ((‖P c‖ : ℝ) : ℂ) ^ (-2 * σ)‖ = _
    rw [norm_mul, norm_pow, norm_inv, norm_cpow_eq_rpow_re_of_pos (norm_pos_iff.2 (hP0 c))]
    simp
  intro σ₀ hσ₀
  have hσ₀' : -1 / 2 < σ₀.re := hσ₀
  set r : ℝ := (σ₀.re - 1 / 2) / 2 with hr
  set R : ℝ := σ₀.re + 1 with hR
  set U : Set ℂ := {σ | r < σ.re} ∩ {σ | σ.re < R} with hUdef
  have hU : IsOpen U := (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)
  have hmem : σ₀ ∈ U := ⟨by show r < σ₀.re; rw [hr]; linarith, by show σ₀.re < R; rw [hR]; linarith⟩
  have hd : DifferentiableOn ℂ (fun σ => ∑' c : Quotient (unitRel (latM 𝔞)), eisTerm 2 σ 0 ((c.out.1 : F), (0 : F))) U := by
    refine differentiableOn_tsum_of_summable_norm
      (u := fun c => ‖P c‖⁻¹ ^ 2 * (‖P c‖ ^ (-2 * r) + ‖P c‖ ^ (-2 * R))) ?_ ?_ hU ?_
    · refine ((hsum (2 + 2 * r) (by rw [hr]; linarith)).add (hsum (2 + 2 * R) (by rw [hR]; linarith))).congr
        fun c => ?_
      have hx := norm_pos_iff.2 (hP0 c)
      rw [inv_natPow_rpow_neg_half_even_eq_pow hx, inv_natPow_rpow_neg_half_even_eq_pow hx]
      ring
    · intro c σ _
      show DifferentiableWithinAt ℂ (fun σ => (P c)⁻¹ ^ 2 * ((‖P c‖ : ℝ) : ℂ) ^ (-2 * σ)) U σ
      refine DifferentiableAt.differentiableWithinAt (DifferentiableAt.const_mul ?_ _)
      refine DifferentiableAt.const_cpow (differentiableAt_id.const_mul _) (Or.inl ?_)
      exact_mod_cast (norm_pos_iff.2 (hP0 c)).ne'
    · intro c σ hσ
      rw [hnorm]
      have hx := norm_pos_iff.2 (hP0 c)
      gcongr
      exact rpow_le_add hx hσ.1.le hσ.2.le
  exact (hd.differentiableAt (hU.mem_nhds hmem)).differentiableWithinAt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEisensteinConstantTermPartDifferentiableOnStatement
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeEisensteinConstantTermPart_differentiableOn : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F), DifferentiableOn ℂ (GlobalTheory.HeckeTwo.aPart 𝔞) GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.halfPlane := by
  first | exact @GlobalTheory.HeckeTwo.aPart_differentiableOn | exact GlobalTheory.HeckeTwo.aPart_differentiableOn | (intros; apply GlobalTheory.HeckeTwo.aPart_differentiableOn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableLipschitzLatticeNormPowSummand
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableLipschitzLatticeNormPowSummand
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace

noncomputable section

namespace GlobalTheory.LipschitzTR.LhsSum

variable {F : Type} [Field F] [NumberField F]

theorem prod_realEmb_eq_norm [IsTotallyReal F] (x : F) :
    (∏ τ : F →+* ℝ, τ x) = ((Algebra.norm ℚ x : ℚ) : ℝ) := by
  apply Complex.ofReal_injective
  push_cast
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  rw [show ((Algebra.norm ℚ x : ℚ) : ℂ) = algebraMap ℚ ℂ (Algebra.norm ℚ x) from rfl, h]
  have hb : Function.Bijective (fun τ : F →+* ℝ => Complex.ofRealHom.comp τ) := by
    refine ⟨fun τ τ' h => ?_, fun φ => ?_⟩
    · ext x
      exact Complex.ofReal_injective (RingHom.congr_fun h x)
    · exact ⟨(IsTotallyReal.complexEmbedding_isReal φ).embedding, RingHom.ext fun x =>
        (IsTotallyReal.complexEmbedding_isReal φ).coe_embedding_apply x⟩
  refine Fintype.prod_bijective (fun τ : F →+* ℝ => RingHom.equivRatAlgHom F ℂ (Complex.ofRealHom.comp τ))
    ((RingHom.equivRatAlgHom F ℂ).bijective.comp hb) _ _ (fun τ => ?_)
  rfl

theorem one_le_abs_prod_int [IsTotallyReal F] (y : 𝓞 F) (hy : y ≠ 0) :
    1 ≤ |∏ τ : F →+* ℝ, τ (y : F)| := by
  rw [prod_realEmb_eq_norm, ← Algebra.coe_norm_int]
  have h : Algebra.norm ℤ y ≠ 0 := Algebra.norm_ne_zero_iff.2 hy
  have h1 : (1 : ℤ) ≤ |Algebra.norm ℤ y| := Int.one_le_abs h
  have h2 : (((Algebra.norm ℤ y : ℤ) : ℚ) : ℝ) = ((Algebra.norm ℤ y : ℤ) : ℝ) := by push_cast; rfl
  rw [h2]
  exact_mod_cast h1

theorem exists_lower_norm [IsTotallyReal F] (M : FractionalIdeal (𝓞 F)⁰ F) :
    ∃ ν : ℝ, 0 < ν ∧ ∀ a ∈ M, a ≠ 0 → ν ≤ |∏ τ : F →+* ℝ, τ a| := by
  obtain ⟨d, hd, hint⟩ := M.isFractional
  have hd0 : (d : F) ≠ 0 := by
    have := nonZeroDivisors.ne_zero hd
    exact_mod_cast this
  have hP : 0 < |∏ τ : F →+* ℝ, τ (d : F)| :=
    abs_pos.2 (Finset.prod_ne_zero_iff.2 fun τ _ => (map_ne_zero τ).2 hd0)
  refine ⟨1 / |∏ τ : F →+* ℝ, τ (d : F)|, by positivity, fun a ha ha0 => ?_⟩
  obtain ⟨y, hy⟩ := hint a ha
  have hy' : (y : F) = (d : F) * a := by
    rw [← Algebra.smul_def]; exact hy
  have hy0 : y ≠ 0 := by
    intro h; apply mul_ne_zero hd0 ha0; rw [← hy', h]; simp
  have h1 := one_le_abs_prod_int y hy0
  rw [hy'] at h1
  simp only [map_mul, Finset.prod_mul_distrib, abs_mul] at h1
  rw [div_le_iff₀ hP]
  linarith [mul_comm (|∏ τ : F →+* ℝ, τ (d : F)|) (|∏ τ : F →+* ℝ, τ a|)]

theorem exists_lower_one_add (w : ℂ) (hw : w.im ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, c * (1 + |t|) ≤ ‖w + (t : ℂ)‖ := by
  have him : 0 < |w.im| := abs_pos.2 hw
  refine ⟨|w.im| / (|w.im| + 1 + ‖w‖), by positivity, fun t => ?_⟩
  have h1 : |w.im| ≤ ‖w + (t : ℂ)‖ := by
    have := Complex.abs_im_le_norm (w + (t : ℂ))
    simpa using this
  have h2 : |t| ≤ ‖w + (t : ℂ)‖ + ‖w‖ := by
    have := norm_sub_le (w + (t : ℂ)) w
    simp only [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs] at this
    exact this
  have hn : 0 ≤ ‖w‖ := norm_nonneg _
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith

theorem floor_bound {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (x : ℝ) :
    s / 2 * (1 + |((⌊x / s⌋ : ℤ) : ℝ)|) ≤ 1 + |x| := by
  set n : ℤ := ⌊x / s⌋ with hn
  have h1 : (n : ℝ) ≤ x / s := Int.floor_le _
  have h2 : x / s < (n : ℝ) + 1 := Int.lt_floor_add_one _
  have h1' : (n : ℝ) * s ≤ x := by rwa [le_div_iff₀ hs0] at h1
  have h2' : x < ((n : ℝ) + 1) * s := by rwa [div_lt_iff₀ hs0] at h2
  rcases le_or_gt 0 (n : ℝ) with hn0 | hn0
  · rw [abs_of_nonneg hn0, abs_of_nonneg (by nlinarith)]
    nlinarith
  · have hn1 : (n : ℝ) ≤ -1 := by
      have : n ≤ -1 := by
        have : n < 0 := by exact_mod_cast hn0
        omega
      exact_mod_cast this
    rw [abs_of_neg hn0]
    have : |x| ≥ -x := neg_le_abs x
    nlinarith

def wt (m : ℤ) : ℝ := ((1 + |(m : ℝ)|) ^ 2)⁻¹

theorem wt_nonneg (m : ℤ) : 0 ≤ wt m := by unfold wt; positivity

theorem summable_wt : Summable wt := by
  have hA : Summable (fun m : ℤ => |(m : ℝ)| ^ (-(2 : ℝ))) := Real.summable_abs_int_rpow (by norm_num)
  have hB : Summable (fun m : ℤ => if m = 0 then (1 : ℝ) else 0) := (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable
  refine Summable.of_nonneg_of_le wt_nonneg (fun m => ?_) (hA.add hB)
  by_cases hm : m = 0
  · subst hm
    simp [wt, Real.zero_rpow]
  · simp only [hm, if_false, add_zero]
    have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by
      have : (1 : ℤ) ≤ |m| := Int.one_le_abs hm
      exact_mod_cast this
    rw [Real.rpow_neg (abs_nonneg _), wt]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    apply inv_anti₀ (by positivity)
    nlinarith [abs_nonneg (m : ℝ)]

theorem summable_prod_wt (ι : Type) [Fintype ι] [DecidableEq ι] :
    Summable (fun n : ι → ℤ => ∏ i, wt (n i)) := by
  refine summable_of_sum_le (c := ∏ _i : ι, ∑' m, wt m)
    (fun n => Finset.prod_nonneg fun i _ => wt_nonneg _) (fun u => ?_)
  calc ∑ n ∈ u, ∏ i, wt (n i)
      ≤ ∑ n ∈ Fintype.piFinset (fun i => u.image (fun n : ι → ℤ => n i)), ∏ i, wt (n i) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          rw [Fintype.mem_piFinset]
          intro i
          exact Finset.mem_image_of_mem _ hn
        · intro n _ _
          exact Finset.prod_nonneg fun i _ => wt_nonneg _
    _ = ∏ i, ∑ m ∈ u.image (fun n : ι → ℤ => n i), wt m := (Finset.prod_univ_sum _ _).symm
    _ ≤ ∏ _i : ι, ∑' m, wt m := by
        apply Finset.prod_le_prod₀
        · intro i _; exact Finset.sum_nonneg fun m _ => wt_nonneg m
        · intro i _; exact summable_wt.sum_le_tsum _ (fun m _ => wt_nonneg m)

end GlobalTheory.LipschitzTR.LhsSum


open GlobalTheory.LipschitzTR.LhsSum in
theorem GlobalTheory.LipschitzTR.summable_lhsTerm_ideal :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M : FractionalIdeal (𝓞 F)⁰ F), M ≠ 0 →
      ∀ (k : ℕ), 2 ≤ k → ∀ (z : (F →+* ℝ) → ℂ), (∀ τ, (z τ).im ≠ 0) →
        Summable (fun a : (M : Set F) => lhsTerm k z a) := by
  intro F _ _ _ M _ k hk z hz
  classical
  obtain ⟨ν, hν0, hν⟩ := exists_lower_norm M
  have hcard : 0 < Fintype.card (F →+* ℝ) := by
    rw [card_realEmb]; exact Module.finrank_pos
  set s : ℝ := min 1 (ν / 2) with hs
  have hs0 : 0 < s := lt_min one_pos (by positivity)
  have hs1 : s ≤ 1 := min_le_left _ _
  have hsν : s ^ Fintype.card (F →+* ℝ) < ν :=
    lt_of_le_of_lt (pow_le_of_le_one hs0.le hs1 hcard.ne') (lt_of_le_of_lt (min_le_right _ _) (by linarith))
  let N : ↥(M : Set F) → ((F →+* ℝ) → ℤ) := fun a τ => ⌊τ (a : F) / s⌋
  have hN : Function.Injective N := by
    intro a b hab
    by_contra hne
    have hne' : (a : F) - b ≠ 0 := sub_ne_zero.2 (fun h => hne (Subtype.ext h))
    have hmem : (a : F) - b ∈ M := (M : Submodule (𝓞 F) F).sub_mem a.2 b.2
    have h1 := hν _ hmem hne'
    have h2 : |∏ τ : F →+* ℝ, τ ((a : F) - b)| ≤ s ^ Fintype.card (F →+* ℝ) := by
      rw [Finset.abs_prod, ← Finset.card_univ, ← Finset.prod_const]
      refine Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun τ _ => ?_)
      have hf := Int.abs_sub_lt_one_of_floor_eq_floor (congrFun hab τ)
      rw [← sub_div, abs_div, abs_of_pos hs0, div_lt_one hs0] at hf
      rw [map_sub]; exact hf.le
    linarith
  have hc : ∀ τ : F →+* ℝ, ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, c * (1 + |t|) ≤ ‖z τ + (t : ℂ)‖ :=
    fun τ => exists_lower_one_add (z τ) (hz τ)
  choose c hc0 hc using hc
  set C : ℝ := ∏ τ : F →+* ℝ, ((c τ * (s / 2)) ^ k)⁻¹ with hC
  refine Summable.of_norm_bounded (g := fun a => C * ∏ τ, wt (N a τ))
    (((summable_prod_wt (F →+* ℝ)).comp_injective hN).mul_left C) (fun a => ?_)
  simp only [lhsTerm, zpow_neg, zpow_natCast, ← Finset.prod_pow, ← Finset.prod_inv_distrib, norm_prod, norm_inv, norm_pow]
  rw [hC, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun τ _ => ?_)
  have hD : 0 < c τ * (s / 2) := by have := hc0 τ; positivity
  have hfl := floor_bound hs0 hs1 (τ (a : F))
  have he : c τ * (s / 2) * (1 + |((N a τ : ℤ) : ℝ)|) ≤ ‖z τ + ((τ (a : F) : ℝ) : ℂ)‖ := by
    calc c τ * (s / 2) * (1 + |((N a τ : ℤ) : ℝ)|) = c τ * (s / 2 * (1 + |((N a τ : ℤ) : ℝ)|)) := by ring
      _ ≤ c τ * (1 + |τ (a : F)|) := mul_le_mul_of_nonneg_left hfl (hc0 τ).le
      _ ≤ _ := hc τ _
  have hone : (1 : ℝ) ≤ 1 + |((N a τ : ℤ) : ℝ)| := by linarith [abs_nonneg ((N a τ : ℤ) : ℝ)]
  rw [wt, ← mul_inv]
  apply inv_anti₀ (by positivity)
  calc (c τ * (s / 2)) ^ k * (1 + |((N a τ : ℤ) : ℝ)|) ^ 2
      ≤ (c τ * (s / 2)) ^ k * (1 + |((N a τ : ℤ) : ℝ)|) ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hone hk) (by positivity)
    _ = (c τ * (s / 2) * (1 + |((N a τ : ℤ) : ℝ)|)) ^ k := by rw [mul_pow (c τ * (s / 2))]
    _ ≤ _ := pow_le_pow_left₀ (by positivity) he k
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableLipschitzLatticeNormPowSummandStatement
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_lipschitzLatticeNormPowSummand : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M : FractionalIdeal (𝓞 F)⁰ F), M ≠ 0 → ∀ (k : ℕ), 2 ≤ k → ∀ (z : (F →+* ℝ) → ℂ), (∀ τ, (z τ).im ≠ 0) → Summable (fun a : (M : Set F) => lhsTerm k z a) := by
  first | exact @GlobalTheory.LipschitzTR.summable_lhsTerm_ideal | exact GlobalTheory.LipschitzTR.summable_lhsTerm_ideal | (intros; apply GlobalTheory.LipschitzTR.summable_lhsTerm_ideal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsUnitDetKrylovMatrixOfSeparable
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsUnitDetKrylovMatrixOfSeparable
open Matrix Polynomial

namespace GlobalTheory.LeviDesc.Krylov

theorem exists_isUnit_det_krylov_of_separable {F : Type} [Field F] {r : ℕ}
    (y : Matrix (Fin r) (Fin r) F) (hs : y.charpoly.Separable) :
    ∃ e : Fin r → F, IsUnit (GlobalTheory.LeviDesc.Krylov.krylov y e).det := by
  obtain ⟨v, hv⟩ := GlobalTheory.ClassParam.exists_cyclic_field y hs
  exact ⟨v, isUnit_iff_ne_zero.2 hv⟩

end GlobalTheory.LeviDesc.Krylov
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsUnitDetKrylovMatrixOfSeparableStatement
open Matrix Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isUnit_det_krylovMatrix_of_separable : ∀ {F : Type} [Field F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F), y.charpoly.Separable → ∃ e : Fin r → F, IsUnit (GlobalTheory.LeviDesc.Krylov.krylov y e).det := by
  first | exact @GlobalTheory.LeviDesc.Krylov.exists_isUnit_det_krylov_of_separable | exact GlobalTheory.LeviDesc.Krylov.exists_isUnit_det_krylov_of_separable | (intros; apply GlobalTheory.LeviDesc.Krylov.exists_isUnit_det_krylov_of_separable <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitZetaAct
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

theorem ch_eq_exp_pow_val (N : ℕ) (j : ZMod N) :
    ch N j = Complex.exp (2 * Real.pi * Complex.I / N) ^ j.val := by
  rw [ch, ← Complex.exp_nat_mul]; congr 1; ring

theorem exists_unit_zetaAct : ∀ (N : ℕ) [NeZero N] (g : ℂ ≃+* ℂ), ∃ a : (ZMod N)ˣ, ZetaAct g N a := by
  intro N _ g
  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / N)) N :=
    Complex.isPrimitiveRoot_exp N (NeZero.ne N)
  have hg : IsPrimitiveRoot (g (Complex.exp (2 * Real.pi * Complex.I / N))) N :=
    hζ.map_of_injective g.injective
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hg.pow_eq_one
  have hcop : i.Coprime N := by
    rw [← hi] at hg
    exact (hζ.pow_iff_coprime (NeZero.pos N) i).mp hg
  refine ⟨ZMod.unitOfCoprime i hcop, fun j => ?_⟩
  rw [ch_eq_exp_pow_val, ch_eq_exp_pow_val, map_pow, ← hi, ← pow_mul, ZMod.coe_unitOfCoprime,
    ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod]
  conv_lhs => rw [← Nat.div_add_mod (i * j.val) N, pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]

end GlobalTheory.WpFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOfMemSchA
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.WeilM

namespace GlobalTheory.ThKOp


open scoped Classical in
theorem continuous_of_mem_schA {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ schA F κ) : Continuous Φ := by
  have hr : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
    have : (InfiniteAdeleRing.ringEquiv_mixedSpace F : InfiniteAdeleRing F → mixedEmbedding.mixedSpace F) =
        fun x => ((fun v : {w : InfinitePlace F // InfinitePlace.IsReal w} =>
            InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
          (fun v : {w : InfinitePlace F // InfinitePlace.IsComplex w} =>
            InfinitePlace.Completion.extensionEmbedding v.1 (x v))) := by
      funext x; exact InfiniteAdeleRing.ringEquiv_mixedSpace_apply F x
    rw [this]
    refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
    · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
        (continuous_apply _)
    · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp
        (continuous_apply _)
  induction hΦ using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨f, g, hg, rfl⟩ := hΦ
    have h1 : Continuous fun x : κ → AdeleRing (𝓞 F) F => fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 :=
      continuous_pi fun i => hr.comp (continuous_fst.comp (continuous_apply i))
    have h2 : Continuous fun x : κ → AdeleRing (𝓞 F) F => fun i => (x i).2 :=
      continuous_pi fun i => continuous_snd.comp (continuous_apply i)
    exact (f.continuous.comp h1).mul (hg.1.continuous.comp h2)
  | zero => exact continuous_const
  | add _ _ _ _ h h' => exact h.add h'
  | smul c _ _ h => exact continuous_const.mul h

end GlobalTheory.ThKOp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogLiftOfUnitMemMap
set_option autoImplicit false

namespace GlobalTheory.DI


set_option autoImplicit false in
theorem _root_.GlobalTheory.DI.logLift_of_unit_mem_map : ∀ {K Kt : Type} [Field K] [CommRing Kt] (p : ℕ) [Fact p.Prime] [CharP K p]
    (π : Kt →+* K) {ι : Type} (F : ι → Kt →+* Kt) (s : Finset ι) (At : Subring Kt), _root_.GlobalTheory.DI.IsFlatLift p π →
    (∀ i ∈ s, ∀ z ∈ At, ∃ w ∈ At, F i z = z ^ p + p * w) → ∀ g : K, g ≠ 0 → g ∈ At.map π →
    g⁻¹ ∈ At.map π → _root_.GlobalTheory.DI.LogLift p π F s (At.map π : Set K) g := by
  intro K Kt _ _ p _ _ π ι F s At hflat hF g hg hmem hinv
  obtain ⟨z, hz, rfl⟩ := Subring.mem_map.mp hmem
  obtain ⟨y, hy, hyz⟩ := Subring.mem_map.mp hinv
  unfold _root_.GlobalTheory.DI.LogLift
  refine ⟨z, rfl, fun i hi => ?_⟩
  obtain ⟨w, hw, hFw⟩ := hF i hi z hz
  refine ⟨y ^ p * w, Subring.mem_map.mpr ⟨y ^ p * w, At.mul_mem (At.pow_mem hy p) hw, rfl⟩, ?_⟩
  have h0 : (p : Kt) * (w - z ^ p * y ^ p * w) = 0 := by
    rw [hflat.ann]
    simp only [map_sub, map_mul, map_pow, hyz]
    rw [← mul_pow, mul_inv_cancel₀ hg, one_pow, one_mul, sub_self]
  rw [hFw]
  linear_combination h0

end GlobalTheory.DI
end
