module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishing
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
public import GroundTheory.AutomorphicForms.GeometricLemma

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeBasicOfConjPlaces
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeBasicOfConjPlaces
noncomputable section

open NumberField IsDedekindDomain Matrix Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.Size

theorem le_sup {ι : Type} [Finite ι] (f : ι → ℝ) (p : ι) : f p ≤ ⨆ q, f q :=
  le_ciSup (Set.finite_range f).bddAbove p

theorem sz_nonneg {K ι κ : Type} [NormedField K] (g : Matrix ι κ K) : 0 ≤ sz g :=
  Real.iSup_nonneg fun _ => norm_nonneg _

theorem sz_mul_le {K : Type} [NormedField K] [IsUltrametricDist K] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) K) : sz (A * B) ≤ sz A * sz B := by
  have hA := sz_nonneg A
  have hB := sz_nonneg B
  refine Real.iSup_le (fun p => ?_) (mul_nonneg hA hB)
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hA hB) fun k _ => ?_
  rw [norm_mul]
  exact mul_le_mul (le_sup (fun q : Fin n × Fin n => ‖A q.1 q.2‖) (p.1, k))
    (le_sup (fun q : Fin n × Fin n => ‖B q.1 q.2‖) (k, p.2)) (norm_nonneg _) hA

def s2 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ℝ := ⨆ p : Fin n × Fin n, ‖A p.1 p.2‖ ^ 2

theorem max_sq_entry_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ s2 A :=
  Real.iSup_nonneg fun _ => sq_nonneg _

theorem norm_entry_le_sqrt_max_sq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ‖A i j‖ ≤ √(s2 A) :=
  Real.le_sqrt_of_sq_le (le_sup (fun q : Fin n × Fin n => ‖A q.1 q.2‖ ^ 2) (i, j))

theorem max_sq_entry_mul_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    s2 (A * B) ≤ (n : ℝ) ^ 2 * s2 A * s2 B := by
  have hA := max_sq_entry_nonneg A
  have hB := max_sq_entry_nonneg B
  refine Real.iSup_le (fun p => ?_) (mul_nonneg (mul_nonneg (sq_nonneg _) hA) hB)
  have h1 : ‖(A * B) p.1 p.2‖ ≤ n * (√(s2 A) * √(s2 B)) := by
    rw [Matrix.mul_apply]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k, ‖A p.1 k * B k p.2‖ ≤ ∑ _k : Fin n, √(s2 A) * √(s2 B) :=
          Finset.sum_le_sum fun k _ => by
            rw [norm_mul]
            exact mul_le_mul (norm_entry_le_sqrt_max_sq A _ _) (norm_entry_le_sqrt_max_sq B _ _) (norm_nonneg _)
              (Real.sqrt_nonneg _)
      _ = n * (√(s2 A) * √(s2 B)) := by simp
  calc ‖(A * B) p.1 p.2‖ ^ 2 ≤ (n * (√(s2 A) * √(s2 B))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = (n : ℝ) ^ 2 * s2 A * s2 B := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB, mul_assoc]

theorem finsum_mono {α : Type} {f g : α → ℝ} (hf : (Function.support f).Finite)
    (hg : (Function.support g).Finite) (h : ∀ a, f a ≤ g a) : ∑ᶠ a, f a ≤ ∑ᶠ a, g a := by
  classical
  rw [finsum_eq_sum_of_support_subset f (s := hf.toFinset ∪ hg.toFinset) (by simp),
    finsum_eq_sum_of_support_subset g (s := hf.toFinset ∪ hg.toFinset) (by simp)]
  exact Finset.sum_le_sum fun a _ => h a

theorem posLog_max_one {x : ℝ} (hx : 0 ≤ x) : Real.posLog (max x 1) = Real.posLog x := by
  rcases le_total x 1 with h | h
  · rw [max_eq_right h, (Real.posLog_eq_zero_iff x).2 (by rwa [abs_of_nonneg hx])]
    simp
  · rw [max_eq_left h]

section Global

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}

theorem logSizeM_eq (A : Matrix (Fin n) (Fin n) (Ad E)) :
    logSizeM A = ∑ v, Real.posLog (s2 (A.map (cV v))) + ∑ᶠ w, Real.posLog (sz (A.map (cW w))) :=
  rfl

theorem logSizeM_nonneg (A : Matrix (Fin n) (Fin n) (Ad E)) : 0 ≤ logSizeM A :=
  add_nonneg (Finset.sum_nonneg fun _ _ => Real.posLog_nonneg)
    (finsum_nonneg fun _ => Real.posLog_nonneg)

theorem supp_fin (hS : SzFin) (A : Matrix (Fin n) (Fin n) (Ad E)) :
    (Function.support fun w => Real.posLog (sz (A.map (cW w)))).Finite := by
  refine (hS E (Fin n) (Fin n) A).subset fun w hw => ?_
  by_contra h
  exact hw ((Real.posLog_eq_zero_iff _).2 (by rw [abs_of_nonneg (sz_nonneg _)]; exact not_lt.1 h))

theorem logSizeM_mul (hS : SzFin) (A B : Matrix (Fin n) (Fin n) (Ad E)) :
    logSizeM (A * B) ≤ logSizeM A + logSizeM B +
      Fintype.card (InfinitePlace E) * Real.posLog ((n : ℝ) ^ 2) := by
  have hinf : ∑ v, Real.posLog (s2 ((A * B).map (cV v))) ≤
      ∑ v, Real.posLog (s2 (A.map (cV v))) + ∑ v, Real.posLog (s2 (B.map (cV v))) +
        Fintype.card (InfinitePlace E) * Real.posLog ((n : ℝ) ^ 2) := by
    have : ∀ v, Real.posLog (s2 ((A * B).map (cV v))) ≤
        Real.posLog (s2 (A.map (cV v))) + Real.posLog (s2 (B.map (cV v))) +
          Real.posLog ((n : ℝ) ^ 2) := fun v => by
      rw [Matrix.map_mul]
      refine (Real.posLog_le_posLog (le_trans (by norm_num) (max_sq_entry_nonneg _)) (max_sq_entry_mul_le _ _)).trans ?_
      refine Real.posLog_mul.trans ?_
      have := Real.posLog_mul (x := (n : ℝ) ^ 2) (y := s2 (A.map (cV v)))
      linarith
    refine (Finset.sum_le_sum fun v _ => this v).trans (le_of_eq ?_)
    simp [Finset.sum_add_distrib]
  have hfin : ∑ᶠ w, Real.posLog (sz ((A * B).map (cW w))) ≤
      ∑ᶠ w, Real.posLog (sz (A.map (cW w))) + ∑ᶠ w, Real.posLog (sz (B.map (cW w))) := by
    rw [← finsum_add_distrib (supp_fin hS A) (supp_fin hS B)]
    refine finsum_mono (supp_fin hS _) (((supp_fin hS A).union (supp_fin hS B)).subset
      (Function.support_add _ _)) fun w => ?_
    rw [Matrix.map_mul]
    exact (Real.posLog_le_posLog (le_trans (by norm_num) (sz_nonneg _)) (sz_mul_le _ _)).trans Real.posLog_mul
  rw [logSizeM_eq, logSizeM_eq, logSizeM_eq]
  linarith

theorem continuous_cV (v : InfinitePlace E) : Continuous (cV v : Ad E → ℂ) :=
  (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
    (IsTotallyComplex.isComplex v)).continuous.comp ((continuous_apply v).comp continuous_fst)

theorem eventually_fin (a₀ : Ad E) :
    ∀ᶠ a in 𝓝 a₀, ∀ w, ‖cW w a‖ ≤ max ‖cW w a₀‖ 1 := by
  have hU : IsOpen {f : Af E | ∀ w, f w ∈ (w.adicCompletionIntegers E : Set (w.adicCompletion E))} :=
    RestrictedProduct.isOpen_forall_mem fun w => Valued.isOpen_valuationSubring _
  have hc : Continuous fun a : Ad E => pFin E a - pFin E a₀ :=
    (continuous_snd).sub continuous_const
  have h0 : (fun a : Ad E => pFin E a - pFin E a₀) a₀ ∈
      {f : Af E | ∀ w, f w ∈ (w.adicCompletionIntegers E : Set (w.adicCompletion E))} := by
    intro w
    change (pFin E a₀ - pFin E a₀) w ∈ w.adicCompletionIntegers E
    rw [sub_self]
    exact zero_mem (w.adicCompletionIntegers E)
  filter_upwards [hc.continuousAt.eventually (hU.mem_nhds h0)] with a ha w
  have h1 : ‖cW w a - cW w a₀‖ ≤ 1 := by
    have := ha w
    exact Valued.toNormedField.norm_le_one_iff.2 this
  have h2 : cW w a = (cW w a - cW w a₀) + cW w a₀ := by ring
  rw [h2]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · exact h1.trans (le_max_right _ _)
  · exact le_max_left _ _

theorem logSizeM_locBdd (hS : SzFin) (A₀ : Matrix (Fin n) (Fin n) (Ad E)) :
    ∃ r, ∀ᶠ A in 𝓝 A₀, logSizeM A ≤ r := by
  refine ⟨∑ v, Real.posLog (⨆ p : Fin n × Fin n, (‖cV v (A₀ p.1 p.2)‖ + 1) ^ 2) +
    ∑ᶠ w, Real.posLog (sz (A₀.map (cW w))), ?_⟩
  have hev : ∀ p : Fin n × Fin n, ∀ᶠ A : Matrix (Fin n) (Fin n) (Ad E) in 𝓝 A₀,
      (∀ v, ‖cV v (A p.1 p.2)‖ ≤ ‖cV v (A₀ p.1 p.2)‖ + 1) ∧
        ∀ w, ‖cW w (A p.1 p.2)‖ ≤ max ‖cW w (A₀ p.1 p.2)‖ 1 := fun p => by
    have hc : Continuous fun A : Matrix (Fin n) (Fin n) (Ad E) => A p.1 p.2 :=
      continuous_id.matrix_elem p.1 p.2
    refine Filter.Eventually.and ?_ (hc.continuousAt.eventually (eventually_fin (A₀ p.1 p.2)))
    refine Filter.eventually_all.2 fun v => ?_
    have hc' : Continuous fun A : Matrix (Fin n) (Fin n) (Ad E) => ‖cV v (A p.1 p.2)‖ :=
      ((continuous_cV v).comp hc).norm
    exact (hc'.continuousAt.eventually (gt_mem_nhds (lt_add_one _))).mono fun _ h => h.le
  filter_upwards [Filter.eventually_all.2 hev] with A hA
  rw [logSizeM_eq]
  refine add_le_add (Finset.sum_le_sum fun v _ => ?_) ?_
  · refine Real.posLog_le_posLog (le_trans (by norm_num) (max_sq_entry_nonneg _)) (Real.iSup_le (fun p => ?_)
      (Real.iSup_nonneg fun _ => sq_nonneg _))
    exact (pow_le_pow_left₀ (norm_nonneg _) ((hA p).1 v) 2).trans
      (le_sup (fun q : Fin n × Fin n => (‖cV v (A₀ q.1 q.2)‖ + 1) ^ 2) p)
  · refine finsum_mono (supp_fin hS A) (supp_fin hS A₀) fun w => ?_
    rw [← posLog_max_one (sz_nonneg (A₀.map (cW w)))]
    refine Real.posLog_le_posLog (le_trans (by norm_num) (sz_nonneg _)) (Real.iSup_le (fun p => ?_) (by positivity))
    exact ((hA p).2 w).trans (max_le_max_right 1
      (le_sup (fun q : Fin n × Fin n => ‖cW w (A₀ q.1 q.2)‖) p))

theorem logSize_compact (hS : SzFin) (C : Set (GA E n)) (hC : IsCompact C) :
    ∃ r, ∀ g ∈ C, logSize g ≤ r := by
  refine hC.induction_on (p := fun S => ∃ r, ∀ g ∈ S, logSize g ≤ r) ⟨0, by simp⟩
    (fun s t hst ⟨r, hr⟩ => ⟨r, fun g hg => hr g (hst hg)⟩)
    (fun s t ⟨r, hr⟩ ⟨r', hr'⟩ => ⟨max r r', fun g hg => hg.elim
      (fun h => (hr g h).trans (le_max_left _ _)) (fun h => (hr' g h).trans (le_max_right _ _))⟩)
    fun x _ => ?_
  obtain ⟨r₁, h₁⟩ := logSizeM_locBdd hS x.val
  obtain ⟨r₂, h₂⟩ := logSizeM_locBdd hS (x⁻¹ : GA E n).val
  have e₁ := (Units.continuous_val (M := Matrix (Fin n) (Fin n) (Ad E))).continuousAt.eventually h₁
  have e₂ := (Units.continuous_coe_inv (M := Matrix (Fin n) (Fin n) (Ad E))).continuousAt.eventually h₂
  refine ⟨{g | logSize g ≤ r₁ + r₂}, mem_nhdsWithin_of_mem_nhds ?_, ⟨r₁ + r₂, fun g hg => hg⟩⟩
  filter_upwards [e₁, e₂] with g a b
  exact add_le_add a b

end Global

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem logSizeM_conj (hC : ConjPlaces) (A : Matrix (Fin n) (Fin n) (Ad E)) :
    logSizeM ((A.map (conjAd E))ᵀ) = logSizeM A := by
  obtain ⟨h1, -, π, ψ, hψ, h3⟩ := hC E
  have hinf : ∀ v, (⨆ p : Fin n × Fin n, ‖cV v ((A.map (conjAd E))ᵀ p.1 p.2)‖ ^ 2) =
      ⨆ p : Fin n × Fin n, ‖cV v (A p.1 p.2)‖ ^ 2 := fun v => by
    rw [← (Equiv.prodComm (Fin n) (Fin n)).iSup_comp
      (g := fun p : Fin n × Fin n => ‖cV v (A p.1 p.2)‖ ^ 2)]
    refine iSup_congr fun p => ?_
    simp [h1, Matrix.transpose_apply]
  have hfin : ∀ w, (⨆ p : Fin n × Fin n, ‖cW w ((A.map (conjAd E))ᵀ p.1 p.2)‖) =
      ⨆ p : Fin n × Fin n, ‖cW (π w) (A p.1 p.2)‖ := fun w => by
    rw [← (Equiv.prodComm (Fin n) (Fin n)).iSup_comp
      (g := fun p : Fin n × Fin n => ‖cW (π w) (A p.1 p.2)‖)]
    refine iSup_congr fun p => ?_
    simp [h3, hψ, Matrix.transpose_apply]
  unfold logSizeM
  simp only [hinf, hfin]
  congr 1
  exact finsum_comp_equiv π
    (f := fun w => Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (A p.1 p.2)‖))

theorem inv_thetaR_val {A : Type} [CommRing A] (σ : A →+* A) (g : GL (Fin n) A) :
    ((thetaR σ n g)⁻¹ : GL (Fin n) A).val = (g.val.map σ)ᵀ := rfl

end CM

theorem sizeBasic : SzFin → ConjPlaces → SizeBasic := by
  intro hS hC E _ _ _ n
  refine ⟨logSize_compact hS, fun g => add_nonneg (logSizeM_nonneg _) (logSizeM_nonneg _),
    fun g => ?_, 2 * (Fintype.card (InfinitePlace E) * Real.posLog ((n : ℝ) ^ 2)), fun g h => ?_⟩
  · change logSizeM (thetaR (conjAd E) n g).val + logSizeM ((thetaR (conjAd E) n g)⁻¹ : GA E n).val = _
    rw [inv_thetaR_val, thetaR_val, logSizeM_conj hC, logSizeM_conj hC, logSize, add_comm]
  · have a := logSizeM_mul hS g.val h.val
    have b := logSizeM_mul hS (h⁻¹ : GA E n).val (g⁻¹ : GA E n).val
    simp only [logSize, _root_.mul_inv_rev, Units.val_mul]
    linarith

end GlobalTheory.CompanionTheory.Size

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeBasicOfConjPlacesStatement
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.size_basic_of_conj_places : SzFin → ConjPlaces → SizeBasic := by
  first | exact @GlobalTheory.CompanionTheory.Size.sizeBasic | exact GlobalTheory.CompanionTheory.Size.sizeBasic | (intros; apply GlobalTheory.CompanionTheory.Size.sizeBasic <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableNilrad
noncomputable section

open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.LocVan

variable {n : ℕ}

theorem locallyCompact_GL (n : ℕ) : LocallyCompactSpace (GL (Fin n) ℂ) := by
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem secondCountable_GL (n : ℕ) : SecondCountableTopology (GL (Fin n) ℂ) := by
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem isClosed_nilrad (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) :
    IsClosed (nilrad W₁ W₂ : Set (Matrix (Fin n) (Fin n) ℂ)) := by
  haveI : FiniteDimensional ℂ (Matrix (Fin n) (Fin n) ℂ) := inferInstance
  letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedAddCommGroup
  letI : NormedSpace ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedSpace
  exact Submodule.closed_of_finiteDimensional (nilrad W₁ W₂)

theorem nil_mul_mem {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (hW : W₁ ≤ W₂)
    {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ nilrad W₁ W₂) (hY : Y ∈ nilrad W₁ W₂) :
    X * Y ∈ nilrad W₁ W₂ := by
  refine ⟨fun y => ?_, fun y hy => ?_, fun y hy => ?_⟩
  · rw [← Matrix.mulVec_mulVec]; exact hW (hX.2.1 _ (hY.1 y))
  · rw [← Matrix.mulVec_mulVec, hX.2.2 _ (hY.2.1 y hy)]; exact W₁.zero_mem
  · rw [← Matrix.mulVec_mulVec, hY.2.2 y hy, Matrix.mulVec_zero]

def nmul {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (hW : W₁ ≤ W₂) (Y X : nilrad W₁ W₂) : nilrad W₁ W₂ :=
  ⟨Y.1 + X.1 + Y.1 * X.1, (nilrad W₁ W₂).add_mem ((nilrad W₁ W₂).add_mem Y.2 X.2) (nil_mul_mem hW Y.2 X.2)⟩

theorem isClosed_twCent (d : GL (Fin n) ℂ) :
    IsClosed (twCent (thC n) d : Set (GL (Fin n) ℂ)) := by
  have h : Continuous fun g : GL (Fin n) ℂ => g⁻¹ * d * thC n g :=
    (continuous_inv.mul continuous_const).mul continuous_thC
  exact isClosed_eq h continuous_const

theorem locallyCompact_twCent (d : GL (Fin n) ℂ) : LocallyCompactSpace (twCent (thC n) d) := by
  haveI := locallyCompact_GL n
  exact (isClosed_twCent d).isClosedEmbedding_subtypeVal.locallyCompactSpace

theorem sigmaFinite_twCent [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)]
    (d : GL (Fin n) ℂ) (μd : Measure (twCent (thC n) d)) [μd.IsHaarMeasure] : SigmaFinite μd := by
  haveI := locallyCompact_twCent d
  haveI := secondCountable_GL n
  haveI : SecondCountableTopology (twCent (thC n) d) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  infer_instance

theorem invInvariant_twCent [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)]
    (d : GL (Fin n) ℂ) (μd : Measure (twCent (thC n) d)) [μd.IsHaarMeasure]
    (hc : ∀ a ∈ twCent (thC n) d, ∀ b ∈ twCent (thC n) d, a * b = b * a) : μd.IsInvInvariant := by
  haveI := locallyCompact_twCent d
  haveI := secondCountable_GL n
  letI : CommGroup (twCent (thC n) d) :=
    { (inferInstance : Group (twCent (thC n) d)) with
      mul_comm := fun a b => Subtype.ext (hc a a.2 b b.2) }
  haveI : SecondCountableTopology (twCent (thC n) d) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  exact Measure.IsHaarMeasure.isInvInvariant_of_regular μd

end GlobalTheory.CompanionTheory.LocVan
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSupportOfSize
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSupportOfSize
noncomputable section

open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1 NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.WedgeSupport

theorem nF_nonneg' {K ι κ : Type} [NormedField K] [Fintype κ] [DecidableEq κ] (A : Matrix ι κ K) : 0 ≤ nF A :=
  Real.iSup_nonneg fun _ => norm_nonneg _

theorem sz_nonneg' {K ι κ : Type} [NormedField K] (g : Matrix ι κ K) : 0 ≤ sz g :=
  Real.iSup_nonneg fun _ => norm_nonneg _

theorem map_mul_eq_one {R S ι κ : Type} [CommRing R] [CommRing S] [Fintype ι] [DecidableEq κ] (f : R →+* S)
    {A : Matrix ι κ R} {Y : Matrix κ ι R} (h : Y * A = 1) : Y.map f * A.map f = 1 := by
  rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero f) (map_one f)]

theorem one_le_sz_pow_mul_nF (hF : MulF) {K ι κ : Type} [NormedField K] [IsUltrametricDist K] [Fintype ι] [Fintype κ]
    [DecidableEq κ] {A : Matrix ι κ K} {Y : Matrix κ ι K} (h : Y * A = 1) :
    1 ≤ sz Y ^ Fintype.card κ * nF A := by
  have h1 := (hF K ι κ κ A).1 Y
  rw [h, (hF K κ κ κ 1).2.2 1, det_one, norm_one] at h1
  exact h1

theorem nF_le_sz_pow (hF : MulF) {K ι κ : Type} [NormedField K] [IsUltrametricDist K] [Fintype ι] [Fintype κ]
    [DecidableEq κ] (A : Matrix ι κ K) : nF A ≤ sz A ^ Fintype.card κ := by
  have h1 := (hF K κ ι κ (1 : Matrix κ κ K)).1 A
  rw [Matrix.mul_one, (hF K κ κ κ 1).2.2 1, det_one, norm_one, mul_one] at h1
  exact h1

theorem nF_ne_zero_of_left_inv (hF : MulF) {K ι κ : Type} [NormedField K] [IsUltrametricDist K] [Fintype ι] [Fintype κ]
    [DecidableEq κ] {A : Matrix ι κ K} {Y : Matrix κ ι K} (h : Y * A = 1) : nF A ≠ 0 := by
  intro h0
  have h1 := one_le_sz_pow_mul_nF hF h
  rw [h0, mul_zero] at h1
  linarith

theorem nF_eq_one_of_sz_le (hF : MulF) {K ι κ : Type} [NormedField K] [IsUltrametricDist K] [Fintype ι] [Fintype κ]
    [DecidableEq κ] {A : Matrix ι κ K} {Y : Matrix κ ι K} (h : Y * A = 1) (hY : sz Y ≤ 1) (hA : sz A ≤ 1) :
    nF A = 1 := by
  apply le_antisymm
  · exact (nF_le_sz_pow hF A).trans (pow_le_one₀ (sz_nonneg' A) hA)
  · have h1 := one_le_sz_pow_mul_nF hF h
    have h2 : sz Y ^ Fintype.card κ ≤ 1 := pow_le_one₀ (sz_nonneg' Y) hY
    nlinarith [nF_nonneg' A]

theorem nI_ne_zero_of_left_inv (hI : MulI) {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
    {A : Matrix ι κ ℂ} {Y : Matrix κ ι ℂ} (h : Y * A = 1) : nI A ≠ 0 := by
  intro h0
  have h1 := (hI ι κ κ A).1 Y
  rw [h, (hI κ κ κ 1).2.2 1, det_one, norm_one, h0, mul_zero] at h1
  norm_num at h1

theorem finSupp_of_mul : MulF → MulI → SzFin → FinSupp := by
  intro hF hI hS E _ _ _ ι κ _ _ _ _ A Y h
  refine ⟨fun v => nI_ne_zero_of_left_inv hI (map_mul_eq_one (cV v) h),
    fun w => nF_ne_zero_of_left_inv hF (map_mul_eq_one (cW w) h), ?_⟩
  refine ((hS E κ ι Y).union (hS E ι κ A)).subset fun w hw => ?_
  by_contra hn
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt] at hn
  exact hw (nF_eq_one_of_sz_le hF (map_mul_eq_one (cW w) h) hn.1 hn.2)

end GlobalTheory.CompanionTheory.WedgeSupport

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSupportOfSizeStatement
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_support_of_size : MulF → MulI → SzFin → FinSupp := by
  first | exact @GlobalTheory.CompanionTheory.WedgeSupport.finSupp_of_mul | exact GlobalTheory.CompanionTheory.WedgeSupport.finSupp_of_mul | (intros; apply GlobalTheory.CompanionTheory.WedgeSupport.finSupp_of_mul <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeRationalSubspace
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeRationalSubspace
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.Degree

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}

theorem basisMat_transpose_eq (W : Submodule E (Fin n → E)) :
    ((basisMat W)ᵀ : Fin (Module.finrank E W) → Fin n → E) =
      W.subtype ∘ (Module.finBasis E W) := by
  funext j i
  rfl

theorem basisMat_linearIndependent (W : Submodule E (Fin n → E)) :
    LinearIndependent E (basisMat W)ᵀ := by
  rw [basisMat_transpose_eq]
  exact (Module.finBasis E W).linearIndependent.map' W.subtype W.ker_subtype

theorem span_basisMat (W : Submodule E (Fin n → E)) :
    Submodule.span E (Set.range (basisMat W)ᵀ) = W := by
  rw [basisMat_transpose_eq, Set.range_comp, ← Submodule.map_span, (Module.finBasis E W).span_eq,
    Submodule.map_top, Submodule.range_subtype]

theorem mul_transpose_apply {κ : Type} [Fintype κ] (g : GL (Fin n) E) (M : Matrix (Fin n) κ E) (j : κ) :
    (g.val * M)ᵀ j = Matrix.toLin' g.val (Mᵀ j) := by
  funext i
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem ker_toLin'_eq_bot (g : GL (Fin n) E) : LinearMap.ker (Matrix.toLin' g.val) = ⊥ := by
  refine LinearMap.ker_eq_bot.2 fun a b hab => ?_
  have h := congrArg (Matrix.toLin' (g⁻¹ : GL (Fin n) E).val) hab
  simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec] using h

theorem frame_rat {κ : Type} [Fintype κ] (x : GA E n) (g : GL (Fin n) E) (M : Matrix (Fin n) κ E) :
    ((ratGL E n g * x)⁻¹ : GA E n).val * (g.val * M).map (algebraMap E (Ad E)) =
      (x⁻¹ : GA E n).val * M.map (algebraMap E (Ad E)) := by
  have hr : (g.val * M).map (algebraMap E (Ad E)) =
      (ratGL E n g).val * M.map (algebraMap E (Ad E)) := by
    rw [Matrix.map_mul]
    rfl
  rw [hr, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (ratGL E n g)⁻¹.val,
    Units.inv_mul, Matrix.one_mul]

theorem degG_rat {κ : Type} [Fintype κ] [DecidableEq κ] (x : GA E n) (g : GL (Fin n) E)
    (M : Matrix (Fin n) κ E) : degG (ratGL E n g * x) (g.val * M) = degG x M := by
  simp only [degG, frame_rat]

theorem degRat_of_degBasisG : DegBasisG → DegRat := by
  intro h E _ _ _ n x g W
  have hli : LinearIndependent E (g.val * basisMat W)ᵀ := by
    have e : (fun j => (g.val * basisMat W)ᵀ j) = Matrix.toLin' g.val ∘ fun j => (basisMat W)ᵀ j :=
      funext (mul_transpose_apply g (basisMat W))
    have l : LinearIndependent E (fun j => (g.val * basisMat W)ᵀ j) :=
      e ▸ (basisMat_linearIndependent W).map' _ (ker_toLin'_eq_bot g)
    exact l
  have hspan : Submodule.span E (Set.range (g.val * basisMat W)ᵀ) = img g W := by
    have e : Set.range (g.val * basisMat W)ᵀ = Matrix.toLin' g.val '' Set.range (basisMat W)ᵀ :=
      Set.ext fun y => ⟨fun ⟨j, hj⟩ => ⟨(basisMat W)ᵀ j, ⟨j, rfl⟩,
          (mul_transpose_apply g (basisMat W) j).symm.trans hj⟩,
        fun ⟨_, ⟨j, hj⟩, hy⟩ => ⟨j, (mul_transpose_apply g (basisMat W) j).trans (hj ▸ hy)⟩⟩
    rw [e, ← Submodule.map_span, span_basisMat]
    rfl
  have key := h E n (Fin (Module.finrank E W)) (ratGL E n g * x) (g.val * basisMat W) hli
  rw [hspan] at key
  rw [← key, degG_rat]
  rfl

end GlobalTheory.CompanionTheory.Degree

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeRationalSubspaceStatement
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_rational_subspace : DegBasisG → DegRat := by
  first | exact @GlobalTheory.CompanionTheory.Degree.degRat_of_degBasisG | exact GlobalTheory.CompanionTheory.Degree.degRat_of_degBasisG | (intros; apply GlobalTheory.CompanionTheory.Degree.degRat_of_degBasisG <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MahlerBoundOfDegree
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MahlerBoundOfDegree
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.Cutoff

section Img

variable {K : Type} [Field K] {n : ℕ}

def imgEquiv (g : GL (Fin n) K) : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
  LinearEquiv.ofLinear (Matrix.toLin' g.val) (Matrix.toLin' (g⁻¹ : GL (Fin n) K).val)
    (by rw [← Matrix.toLin'_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.toLin'_one])

theorem img_eq_map (g : GL (Fin n) K) (W : Submodule K (Fin n → K)) :
    img g W = W.map ((imgEquiv g : (Fin n → K) ≃ₗ[K] (Fin n → K)) : (Fin n → K) →ₗ[K] (Fin n → K)) := rfl

theorem finrank_img (g : GL (Fin n) K) (W : Submodule K (Fin n → K)) :
    Module.finrank K (img g W) = Module.finrank K W := by
  rw [img_eq_map]
  exact LinearEquiv.finrank_map_eq _ _

theorem img_top (g : GL (Fin n) K) : img g (⊤ : Submodule K (Fin n → K)) = ⊤ := by
  rw [img_eq_map, Submodule.map_top]
  exact LinearEquiv.range _

theorem img_img_inv (g : GL (Fin n) K) (W : Submodule K (Fin n → K)) :
    img g (img (g⁻¹ : GL (Fin n) K) W) = W := by
  unfold img
  rw [← Submodule.map_comp, ← Matrix.toLin'_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.toLin'_one, Submodule.map_id]

end Img

theorem mem_cutSet_of_mem (hR : DegRat) {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ} {τ : ℝ}
    (g : GL (Fin n) E) {x : GA E n} (hx : x ∈ cutSet E n τ) : ratGL E n g * x ∈ cutSet E n τ := by
  have hx' : (∀ W : Submodule E (Fin n → E), deg x W ≤ prof n τ (Module.finrank E W)) ∧ -τ ≤ deg x ⊤ := hx
  show (∀ W : Submodule E (Fin n → E), deg (ratGL E n g * x) W ≤ prof n τ (Module.finrank E W)) ∧
    -τ ≤ deg (ratGL E n g * x) ⊤
  refine ⟨fun W => ?_, ?_⟩
  · have h := hR E n x g (img (g⁻¹ : GL (Fin n) E) W)
    rw [img_img_inv] at h
    rw [h, ← finrank_img (g⁻¹ : GL (Fin n) E) W]
    exact hx'.1 _
  · have h := hR E n x g ⊤
    rw [img_top] at h
    rw [h]
    exact hx'.2

theorem mahler_of : DegBdd → DegRat → MahlerC → Mahler := by
  intro hB hR hM E _ _ _ n τ
  refine ⟨?_, ?_, ?_⟩
  · have hset : cutSet E n τ = (⋂ W : Submodule E (Fin n → E), {x : GA E n | deg x W ≤ prof n τ (Module.finrank E W)}) ∩
        {x : GA E n | -τ ≤ deg x ⊤} := by
      ext x
      simp [cutSet]
    rw [hset]
    exact (isClosed_iInter fun W => isClosed_le ((hB E n).2 W) continuous_const).inter
      (isClosed_le continuous_const ((hB E n).2 ⊤))
  · intro g x
    constructor
    · intro h
      have h' := mem_cutSet_of_mem hR (g⁻¹) h
      rwa [map_inv, inv_mul_cancel_left] at h'
    · exact mem_cutSet_of_mem hR g
  · obtain ⟨C, hC, hsub⟩ := hM E n (|τ| * (2 * n + 1) ^ 2)
    refine ⟨C, hC, fun x hx => ?_⟩
    have hx' : (∀ W : Submodule E (Fin n → E), deg x W ≤ prof n τ (Module.finrank E W)) ∧ -τ ≤ deg x ⊤ := hx
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hτ : τ ≤ |τ| := le_abs_self τ
    have hτ0 : 0 ≤ |τ| := abs_nonneg τ
    apply hsub x
    · intro W hW
      have h1 := hx'.1 W
      rw [hW] at h1
      simp only [prof] at h1
      push_cast at h1
      nlinarith [mul_nonneg hτ0 hn, mul_nonneg (sub_nonneg.2 hτ) hn, mul_nonneg hτ0 (mul_nonneg hn hn)]
    · have h1 := hx'.1 ⊤
      rw [finrank_top, Module.finrank_fin_fun] at h1
      simp only [prof] at h1
      have h2 := hx'.2
      rw [abs_le]
      constructor
      · nlinarith [mul_nonneg hτ0 hn, mul_nonneg hτ0 (mul_nonneg hn hn)]
      · nlinarith [mul_nonneg hτ0 hn, mul_nonneg hτ0 (mul_nonneg hn hn),
          mul_nonneg (sub_nonneg.2 hτ) (mul_nonneg hn (by linarith : (0 : ℝ) ≤ n + 1))]

end GlobalTheory.CompanionTheory.Cutoff

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MahlerBoundOfDegreeStatement
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mahler_bound_of_degree : DegBdd → DegRat → MahlerC → Mahler := by
  first | exact @GlobalTheory.CompanionTheory.Cutoff.mahler_of | exact GlobalTheory.CompanionTheory.Cutoff.mahler_of | (intros; apply GlobalTheory.CompanionTheory.Cutoff.mahler_of <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeBasisGeneral
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeBasisGeneral
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.DegBasisGen

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}

theorem ultra (w : HeightOneSpectrum (𝓞 E)) : IsUltrametricDist (w.adicCompletion E) :=
  inferInstanceAs (@IsUltrametricDist (w.adicCompletion E)
    (Valued.toNormedField (w.adicCompletion E) (WithZero (Multiplicative ℤ))).toDist)

theorem exists_left_inv {K ι κ : Type} [Field K] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (P : Matrix ι κ K) (hP : LinearIndependent K Pᵀ) : ∃ Y : Matrix κ ι K, Y * P = 1 := by
  have inj : LinearMap.ker P.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    have h0 := hv
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_eq_sum] at h0
    simp only [op_smul_eq_smul] at h0
    funext i
    exact Fintype.linearIndependent_iff.1 hP v h0 i
  obtain ⟨f, hf⟩ := P.mulVecLin.exists_leftInverse_of_injective inj
  refine ⟨LinearMap.toMatrix' f, ?_⟩
  have h := congrArg LinearMap.toMatrix' hf
  rwa [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin',
    LinearMap.toMatrix'_id] at h

theorem degG_reindex (hF : WedgeF) (hI : WedgeI) {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ']
    [DecidableEq κ'] (e : κ' ≃ κ) (x : GA E n) (M : Matrix (Fin n) κ E) :
    degG x (M.submatrix id e) = degG x M := by
  have hfr : (x⁻¹ : GA E n).val * (M.submatrix id e).map (algebraMap E (Ad E)) =
      ((x⁻¹ : GA E n).val * M.map (algebraMap E (Ad E))).submatrix id e := by
    ext i j
    simp [Matrix.mul_apply]
  obtain ⟨A, hA⟩ : ∃ A, A = (x⁻¹ : GA E n).val * M.map (algebraMap E (Ad E)) := ⟨_, rfl⟩
  have hv : ∀ v, nI ((A.submatrix id e).map (cV v)) = nI (A.map (cV v)) := fun v => by
    rw [← Matrix.submatrix_map]
    exact (hI (Fin n)).reindex κ κ' e (A.map (cV v))
  have hw : ∀ w, nF ((A.submatrix id e).map (cW w)) = nF (A.map (cW w)) := fun w => by
    haveI := ultra w
    rw [← Matrix.submatrix_map]
    exact (hF (w.adicCompletion E) (Fin n)).reindex κ κ' e (A.map (cW w))
  simp only [degG, hfr, ← hA, hv, hw]

theorem degG_mul (mF : MulF) (mI : MulI) (lg : LogAbsBasic) (fs : FinSupp) {κ : Type} [Fintype κ] [DecidableEq κ]
    (x : GA E n) (P : Matrix (Fin n) κ E) (hP : LinearIndependent E Pᵀ) (s : Matrix κ κ E) (hs : s.det ≠ 0) :
    degG x (P * s) = degG x P := by
  obtain ⟨A, hA⟩ : ∃ A, A = (x⁻¹ : GA E n).val * P.map (algebraMap E (Ad E)) := ⟨_, rfl⟩
  have hfr : (x⁻¹ : GA E n).val * (P * s).map (algebraMap E (Ad E)) = A * s.map (algebraMap E (Ad E)) := by
    rw [hA, Matrix.map_mul, Matrix.mul_assoc]
  obtain ⟨Y₀, hY₀⟩ := exists_left_inv P hP
  have hYA : (Y₀.map (algebraMap E (Ad E)) * x.val) * A = 1 := by
    rw [hA, Matrix.mul_assoc, ← Matrix.mul_assoc x.val, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mul, ← Matrix.map_mul, hY₀, Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨h1, h2, h3⟩ := (lg E).1, (lg E).2.1, (lg E).2.2
  obtain ⟨f1, f2, f3⟩ := fs E (Fin n) κ A _ hYA
  have hu : IsUnit (algebraMap E (Ad E) s.det) := (IsUnit.mk0 _ hs).map _
  have hdet : ∀ {R : Type} [CommRing R] (f : Ad E →+* R),
      ((s.map (algebraMap E (Ad E))).map f).det = f (algebraMap E (Ad E) s.det) := fun f => by
    rw [RingHom.map_det, RingHom.map_det]
    rfl
  have hv : ∀ v, Real.log (nI ((A * s.map (algebraMap E (Ad E))).map (cV v))) =
      Real.log (nI (A.map (cV v))) + Real.log (‖cV v (algebraMap E (Ad E) s.det)‖ ^ 2) := fun v => by
    have hne : ‖cV v (algebraMap E (Ad E) s.det)‖ ^ 2 ≠ 0 :=
      pow_ne_zero _ (norm_ne_zero_iff.2 (hu.map (cV v)).ne_zero)
    rw [Matrix.map_mul, (mI (Fin n) (Fin n) κ _).2.1, hdet, Real.log_mul (f1 v) hne]
  have hw : ∀ w, Real.log (nF ((A * s.map (algebraMap E (Ad E))).map (cW w))) =
      Real.log (nF (A.map (cW w))) + Real.log ‖cW w (algebraMap E (Ad E) s.det)‖ := fun w => by
    haveI := ultra w
    have hne : ‖cW w (algebraMap E (Ad E) s.det)‖ ≠ 0 := norm_ne_zero_iff.2 (hu.map (cW w)).ne_zero
    rw [Matrix.map_mul, (mF _ (Fin n) (Fin n) κ _).2.1, hdet, Real.log_mul (f2 w) hne]
  have hsupp : (Function.support fun w => Real.log (nF (A.map (cW w)))).Finite :=
    f3.subset fun w hw' h => hw' (by simp [h])
  have hprod := h3 s.det hs
  simp only [degG, hfr, ← hA, hv, hw]
  rw [Finset.sum_add_distrib, finsum_add_distrib hsupp (h1 _ hu)]
  unfold logAbs at hprod
  linarith

theorem degBasisG_of : WedgeF → WedgeI → MulF → MulI → LogAbsBasic → FinSupp → DegBasisG := by
  intro hF hI mF mI lg fs E _ _ _ n κ _ _ x M hM
  obtain ⟨W, hW⟩ : ∃ W, W = Submodule.span E (Set.range Mᵀ) := ⟨_, rfl⟩
  rw [← hW]
  have hcard : Module.finrank E W = Fintype.card κ := by
    rw [hW]
    exact finrank_span_eq_card hM
  have hsub : ∀ k, (fun i => M i k) ∈ W := fun k => by
    rw [hW]
    exact Submodule.subset_span ⟨k, rfl⟩
  let e : Fin (Module.finrank E W) ≃ κ := (Fintype.equivFinOfCardEq hcard.symm).symm
  have hcol : ∀ j, (fun i => M i (e j)) ∈ W := fun j => hsub (e j)
  let b := Module.finBasis E W
  let s : Matrix (Fin (Module.finrank E W)) (Fin (Module.finrank E W)) E :=
    Matrix.of fun i j => b.repr ⟨fun i' => M i' (e j), hcol j⟩ i
  have hfac : M.submatrix id e = basisMat W * s := by
    ext i j
    have h := congrArg (fun y : W => (y : Fin n → E) i) (b.sum_repr ⟨fun i' => M i' (e j), hcol j⟩)
    simp only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at h
    simp only [Matrix.mul_apply, basisMat, Matrix.of_apply, Matrix.submatrix_apply, id, s]
    rw [← h]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  have hlin : LinearIndependent E (M.submatrix id e)ᵀ := hM.comp e e.injective
  have hs : s.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have h1 : M.submatrix id e *ᵥ v = 0 := by
      rw [hfac, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
    rw [Matrix.mulVec_eq_sum] at h1
    simp only [op_smul_eq_smul] at h1
    exact hv0 (funext fun i => Fintype.linearIndependent_iff.1 hlin v h1 i)
  have hP : LinearIndependent E (basisMat W)ᵀ :=
    b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  calc degG x M = degG x (M.submatrix id e) := (degG_reindex hF hI e x M).symm
    _ = degG x (basisMat W * s) := by rw [hfac]
    _ = degG x (basisMat W) := degG_mul mF mI lg fs x _ hP s hs
    _ = deg x W := rfl

end GlobalTheory.CompanionTheory.DegBasisGen

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeBasisGeneralStatement
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_basis_general : WedgeF → WedgeI → MulF → MulI → LogAbsBasic → FinSupp → DegBasisG := by
  first | exact @GlobalTheory.CompanionTheory.DegBasisGen.degBasisG_of | exact GlobalTheory.CompanionTheory.DegBasisGen.degBasisG_of | (intros; apply GlobalTheory.CompanionTheory.DegBasisGen.degBasisG_of <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicLeviProjection
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicLeviProjection
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.SmGLBridge

theorem leviProj_found_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → ∀ (φ : Levi k m ≃* levi k N β), (∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) → ∀ (p : GL (Fin N) k) (h1 : p ∈ parab k e) (h2 : p ∈ blockUpper k N β), φ (leviProj k e ⟨p, h1⟩) = GroundTheory.Automorphic.Parabolic.leviProj k N β ⟨p, h2⟩ := by
  intro k _ _ _ _ α _ _ N m _ _ e β hβ φ hφ p h1 h2
  have hblk : ∀ x y, β x = β y ↔ blk e x = blk e y := by
    intro x y
    constructor
    · intro h
      have h3 := (hβ x y).not.1 (by omega)
      have h4 := (hβ y x).not.1 (by omega)
      exact le_antisymm (not_lt.1 h4) (not_lt.1 h3)
    · intro h
      have h3 := (hβ x y).not.2 (by rw [h]; exact lt_irrefl _)
      have h4 := (hβ y x).not.2 (by rw [h]; exact lt_irrefl _)
      omega
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro x y
  rw [hφ]
  rw [show ((GroundTheory.Automorphic.Parabolic.leviProj k N β ⟨p, h2⟩ : levi k N β) : GL (Fin N) k).val x y = _ from GroundTheory.Automorphic.Parabolic.leviProj_apply _ x y]
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective x
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective y
  by_cases hab : a = b
  · subst hab
    rw [if_pos ((hblk _ _).2 (by simp))]
    have := leviEmb_apply_same k e (leviProj k e ⟨p, h1⟩) a i j
    rw [this, leviProj_apply]
  · rw [if_neg (fun h => hab (by simpa using (hblk _ _).1 h))]
    exact leviEmb_apply_ne k e _ hab i j

end GlobalTheory.CompanionTheory.SmGLBridge
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicLeviProjectionStatement
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_levi_projection : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → ∀ (φ : Levi k m ≃* levi k N β), (∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) → ∀ (p : GL (Fin N) k) (h1 : p ∈ parab k e) (h2 : p ∈ blockUpper k N β), φ (leviProj k e ⟨p, h1⟩) = GroundTheory.Automorphic.Parabolic.leviProj k N β ⟨p, h2⟩ := by
  first | exact @GlobalTheory.CompanionTheory.SmGLBridge.leviProj_found_eq | exact GlobalTheory.CompanionTheory.SmGLBridge.leviProj_found_eq | (intros; apply GlobalTheory.CompanionTheory.SmGLBridge.leviProj_found_eq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KerSCShortExact
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory.CompanionTheory.GE.KerSeq

variable {X : Scheme.{0}} {k : ℕ} {M : ℕ → X.Modules}

abbrev sumN (M : ℕ → X.Modules) (k d e : ℕ) : X.Modules := ⨁ fun _ : Fin k => M (d + e)

def sumMap (T : Fin k → ∀ e, M e ⟶ M (e + 1)) (d e : ℕ) : sumN M k d e ⟶ M (d + e + 1) :=
  biproduct.desc fun i => T i (d + e)

def diagOp (T : Fin k → ∀ e, M e ⟶ M (e + 1)) (d : ℕ) (j : Fin k) (e : ℕ) :
    sumN M k d e ⟶ sumN M k d (e + 1) :=
  biproduct.map fun _ => T j (d + e)

abbrev kerSeq (T : Fin k → ∀ e, M e ⟶ M (e + 1)) (d e : ℕ) : X.Modules := kernel (sumMap T d e)

theorem diagOp_sumMap (T : Fin k → ∀ e, M e ⟶ M (e + 1))
    (hc : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)) (d : ℕ) (j : Fin k) (e : ℕ) :
    diagOp T d j e ≫ sumMap T d (e + 1) = sumMap T d e ≫ T j (d + e + 1) := by
  apply biproduct.hom_ext'
  intro i
  simp only [diagOp, sumMap, biproduct.ι_map_assoc, biproduct.ι_desc, biproduct.ι_desc_assoc]
  exact hc j i (d + e)

def kerOp (T : Fin k → ∀ e, M e ⟶ M (e + 1))
    (hc : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)) (d : ℕ) (j : Fin k) (e : ℕ) :
    kerSeq T d e ⟶ kerSeq T d (e + 1) :=
  kernel.lift _ (kernel.ι _ ≫ diagOp T d j e) (by
    rw [Category.assoc, diagOp_sumMap T hc, kernel.condition_assoc, zero_comp])

@[reassoc (attr := simp)]
theorem kerOp_ι (T : Fin k → ∀ e, M e ⟶ M (e + 1))
    (hc : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)) (d : ℕ) (j : Fin k) (e : ℕ) :
    kerOp T hc d j e ≫ kernel.ι _ = kernel.ι _ ≫ diagOp T d j e :=
  kernel.lift_ι _ _ _

theorem diagOp_comm (T : Fin k → ∀ e, M e ⟶ M (e + 1))
    (hc : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)) (d : ℕ) (i j : Fin k) (e : ℕ) :
    diagOp T d i e ≫ diagOp T d j (e + 1) = diagOp T d j e ≫ diagOp T d i (e + 1) := by
  apply biproduct.hom_ext
  intro l
  simp only [diagOp, Category.assoc, biproduct.map_π, biproduct.map_π_assoc]
  exact biproduct.π _ l ≫= hc i j (d + e)

theorem kerOp_comm (T : Fin k → ∀ e, M e ⟶ M (e + 1))
    (hc : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)) (d : ℕ) (i j : Fin k) (e : ℕ) :
    kerOp T hc d i e ≫ kerOp T hc d j (e + 1) = kerOp T hc d j e ≫ kerOp T hc d i (e + 1) := by
  rw [← cancel_mono (kernel.ι _)]
  simp only [Category.assoc, kerOp_ι, kerOp_ι_assoc]
  rw [diagOp_comm T hc]

def kerSC (T : Fin k → ∀ e, M e ⟶ M (e + 1)) (d e : ℕ) : ShortComplex X.Modules :=
  ShortComplex.mk (kernel.ι (sumMap T d e)) (sumMap T d e) (kernel.condition _)

theorem kerSC_shortExact (T : Fin k → ∀ e, M e ⟶ M (e + 1)) (d e : ℕ) [Epi (sumMap T d e)] :
    (kerSC T d e).ShortExact :=
  ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _))
    (inferInstanceAs (Mono (kernel.ι (sumMap T d e))))
    (inferInstanceAs (Epi (sumMap T d e)))

end GlobalTheory.CompanionTheory.GE.KerSeq
end
end
