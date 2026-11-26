module

public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.PowNorm
theorem UpperTheory.Zero.ConvolutionTheory.EB.powNorm :
    UpperTheory.Zero.ConvolutionTheory.EB.PowNorm := by
  intro H _ _ Q U ρ hQ hU k
  have hρ : 0 ≤ ρ := (norm_nonneg _).trans hU
  have hb : ∀ f ∈ Q, ‖U f‖ ≤ ρ * ‖f‖ := by
    intro f hf
    exact (U ∘L Q.subtypeL).le_of_opNorm_le hU ⟨f, hf⟩
  have key : ∀ k : ℕ, ∀ f ∈ Q, (U ^ k) f ∈ Q ∧ ‖(U ^ k) f‖ ≤ ρ ^ k * ‖f‖ := by
    intro k
    induction k with
    | zero =>
      intro f hf
      simp [hf]
    | succ k ih =>
      intro f hf
      obtain ⟨h1, h2⟩ := ih f hf
      have e : (U ^ (k + 1)) f = U ((U ^ k) f) := by
        rw [pow_succ']
        rfl
      rw [e]
      refine ⟨hQ _ h1, (hb _ h1).trans ?_⟩
      rw [pow_succ', mul_assoc]
      exact mul_le_mul_of_nonneg_left h2 hρ
  refine ⟨fun f hf => (key k f hf).1, ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (pow_nonneg hρ k) fun q => ?_
  exact (key k q q.2).2
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.LvEx
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] borelG borelF borelA borelH

theorem UpperTheory.Zero.ConvolutionTheory.EB.lvEx :
    UpperTheory.Zero.ConvolutionTheory.EB.LvEx := by
  intro E _ _ _ a b Z φ h
  have key : ∀ w : Pl E, ∃ (A : Subgroup (GLw a w)) (B : Subgroup (GLw b w)),
      IsOpen (A : Set (GLw a w)) ∧ IsOpen (B : Set (GLw b w)) ∧ A ≤ KGL w (n := a) ∧ B ≤ KGL w (n := b) ∧
      (w ∉ Z → A = KGL w (n := a) ∧ B = KGL w (n := b)) ∧ (w ∈ Z → IsHecke (A.prod B) (φ w)) := by
    intro w
    by_cases hw : w ∈ Z
    · obtain ⟨K', ho, hle, hH⟩ := h w hw
      refine ⟨K'.comap (MonoidHom.inl _ _), K'.comap (MonoidHom.inr _ _), ?_, ?_, ?_, ?_,
        fun h' => absurd hw h', fun _ => ⟨hH.1, ?_⟩⟩
      · exact ho.preimage (continuous_id.prodMk continuous_const)
      · exact ho.preimage (continuous_const.prodMk continuous_id)
      · intro x hx
        exact (hle hx).1
      · intro y hy
        exact (hle hy).2
      · rintro ⟨x, y⟩ ⟨hx, hy⟩ g
        have hxy : ((x, y) : GLw a w × GLw b w) ∈ K' := by
          have := K'.mul_mem hx hy
          simpa using this
        exact hH.2 _ hxy g
    · exact ⟨KGL w (n := a), KGL w (n := b), (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).1,
        (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).1, le_rfl, le_rfl,
        fun _ => ⟨rfl, rfl⟩, fun h' => absurd h' hw⟩
  choose A B hA hB hA' hB' hoff hfix using key
  exact ⟨⟨A, B, hA, hB, hA', hB', hoff⟩, hfix⟩
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.SatCard
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] borelG borelF borelA borelH

theorem UpperTheory.Zero.ConvolutionTheory.EB.satCard :
    UpperTheory.Zero.ConvolutionTheory.EB.SatCard := by
  intro E _ _ _ n D w B h
  obtain ⟨b, hb, rfl⟩ := h
  rw [Multiset.card_sum]
  exact (Finset.sum_congr rfl fun i _ => (hb i).card).trans D.sum
end
end
