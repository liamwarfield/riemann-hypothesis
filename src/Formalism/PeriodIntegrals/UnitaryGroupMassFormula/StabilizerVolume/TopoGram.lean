module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensVAll

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoGram
noncomputable section

namespace PI.VolStabS.TopoGram

open Matrix

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem hform_eq (σ : A →+* A) (J : Matrix n n A) (x y : n → A) :
    Formalism.UG.hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem hform_mulVec (σ : A →+* A) (J G : Matrix n n A) (x y : n → A) :
    Formalism.UG.hform σ J (G *ᵥ x) (G *ᵥ y) = Formalism.UG.hform σ (Formalism.UG.cT σ G * J * G) x y := by
  rw [hform_eq, hform_eq, ← mulVec_mulVec, ← mulVec_mulVec]
  conv_rhs => rw [dotProduct_mulVec, Formalism.UG.cT, vecMul_transpose]
  congr 1
  funext i
  exact RingHom.map_mulVec σ G x i

end PI.VolStabS.TopoGram

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Matrix
open scoped TensorProduct

theorem gramPres_holds : GramPres := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet g X
  have hg : Formalism.UG.cT (sigR (AF F) σ) ((HA.mat (AF F) σ J g : GL (Fin M) (AF F ⊗[F] E)) :
      Matrix (Fin M) (Fin M) _) * JR (AF F) J *
      ((HA.mat (AF F) σ J g : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) _) =
      JR (AF F) J := g.2
  funext x y
  change hR (AF F) σ J (((HA.mat (AF F) σ J g : GL (Fin M) (AF F ⊗[F] E)) :
      Matrix (Fin M) (Fin M) _) *ᵥ X x) (((HA.mat (AF F) σ J g : GL (Fin M) (AF F ⊗[F] E)) :
      Matrix (Fin M) (Fin M) _) *ᵥ X y) = hR (AF F) σ J (X x) (X y)
  rw [hR, TopoGram.hform_mulVec, hg]
  rfl

end PI.VolStabS
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensPos
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Filter Topology Set
open scoped TensorProduct ENNReal

namespace LocPosW

theorem pos_of_lb {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure V} {ν : Measure X} {f : V → Y} {ι : X → Y} (hι : Function.Injective ι)
    {U : Set V} {fib : X → Measure V} (hfib : IsFibreFamily μ f ι U ν Set.univ fib)
    {f' : V → X} (hf' : Continuous f') (hff : ∀ v, f v = ι (f' v))
    {φ : V → ℝ} (hφc : Continuous φ) (hφs : HasCompactSupport φ) (hφU : tsupport φ ⊆ U)
    (hφ0 : ∀ v, 0 ≤ φ v) {W : Set V} (hWU : W ⊆ U) {δ : ℝ} (hδ : 0 < δ)
    (hWφ : ∀ v ∈ W, δ ≤ φ v) {b0 : X} {c : ℝ≥0∞} (hc : 0 < c) (hc' : c ≠ ⊤) {N : Set X}
    (hN : N ∈ 𝓝 b0) (hlb : ∀ S ⊆ N, MeasurableSet S → c * ν S ≤ μ (f ⁻¹' (ι '' S) ∩ W))
    (hνpos : ∀ O : Set X, IsOpen O → O.Nonempty → ν O ≠ 0) (hνfin : ∃ N' ∈ 𝓝 b0, ν N' < ⊤) :
    0 < ∫ v, φ v ∂(fib b0) := by
  classical
  set g : X → ℝ := fun b => ∫ v, φ v ∂(fib b) with hg
  obtain ⟨hint, hcont⟩ := hfib.2.2 φ hφc hφs hφU
  have hgc : ContinuousAt g b0 := (hcont b0 (mem_univ _)).continuousAt univ_mem
  by_contra hneg
  push Not at hneg
  set η := δ * c.toReal with hηdef
  have hη : 0 < η := mul_pos hδ (ENNReal.toReal_pos hc.ne' hc')
  obtain ⟨N', hN', hN'fin⟩ := hνfin
  have hev : ∀ᶠ b in 𝓝 b0, g b < η := hgc.eventually (Iio_mem_nhds (lt_of_le_of_lt hneg hη))
  obtain ⟨O, hOsub, hOo, hbO⟩ := mem_nhds_iff.1 (inter_mem (inter_mem hN hN') hev)
  have hOm : MeasurableSet O := hOo.measurableSet
  have hOpos : ν O ≠ 0 := hνpos O hOo ⟨b0, hbO⟩
  have hOfin : ν O ≠ ⊤ := ne_top_of_le_ne_top hN'fin.ne (measure_mono fun b hb => (hOsub hb).1.2)
  have hfO : f ⁻¹' (ι '' O) = f' ⁻¹' O := by
    ext v
    simp only [mem_preimage, mem_image, hff, hι.eq_iff, exists_eq_right]
  let ψ : V → ℝ≥0∞ := (f ⁻¹' (ι '' O)).indicator (fun v => ENNReal.ofReal (φ v))
  have hψm : Measurable ψ := by
    refine Measurable.indicator (ENNReal.measurable_ofReal.comp hφc.measurable) ?_
    rw [hfO]
    exact hf'.measurable hOm
  have hdis := hfib.2.1 ψ hψm
  have hin : ∀ b, ∫⁻ v, ψ v ∂(fib b) = O.indicator (fun b => ENNReal.ofReal (g b)) b := by
    intro b
    have hnull := hfib.1 b
    by_cases hb : b ∈ O
    · rw [indicator_of_mem hb]
      have hae : ψ =ᵐ[fib b] fun v => ENNReal.ofReal (φ v) := by
        refine ae_iff.2 (measure_mono_null (fun v hv => ?_) hnull)
        intro hvin
        apply hv
        have h1 : f v = ι b := hvin.1
        have h2 : f' v = b := hι (by rw [← hff]; exact h1)
        have h3 : v ∈ f ⁻¹' (ι '' O) := by rw [hfO]; show f' v ∈ O; rw [h2]; exact hb
        exact indicator_of_mem h3 _
      rw [lintegral_congr_ae hae,
        ← ofReal_integral_eq_lintegral_ofReal (hint b (mem_univ b)) (ae_of_all _ hφ0)]
    · rw [indicator_of_notMem hb]
      have hae : ψ =ᵐ[fib b] 0 := by
        refine ae_iff.2 (measure_mono_null (fun v hv => ?_) hnull)
        intro hvin
        apply hv
        have h1 : f v = ι b := hvin.1
        have h2 : f' v = b := hι (by rw [← hff]; exact h1)
        have h3 : v ∉ f ⁻¹' (ι '' O) := by rw [hfO]; show f' v ∉ O; rw [h2]; exact hb
        exact indicator_of_notMem h3 _
      rw [lintegral_congr_ae hae]
      simp
  simp_rw [hin] at hdis
  rw [lintegral_indicator hOm] at hdis
  have hup : ∫⁻ b in O, ENNReal.ofReal (g b) ∂ν < ∫⁻ b in O, ENNReal.ofReal η ∂ν := by
    have hle : ∫⁻ b in O, ENNReal.ofReal (g b) ∂ν ≤ ∫⁻ b in O, ENNReal.ofReal η ∂ν :=
      setLIntegral_mono measurable_const fun b hb => ENNReal.ofReal_le_ofReal (hOsub hb).2.le
    refine setLIntegral_strict_mono hOm hOpos measurable_const ?_ (ae_of_all _ fun b hb => ?_)
    · refine ne_top_of_le_ne_top ?_ hle
      rw [setLIntegral_const]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hOfin
    · exact (ENNReal.ofReal_lt_ofReal_iff hη).2 (hOsub hb).2
  rw [setLIntegral_const] at hup
  have hlow : ENNReal.ofReal η * ν O ≤ ∫⁻ v in U, ψ v ∂μ := by
    calc ENNReal.ofReal η * ν O = ENNReal.ofReal δ * (c * ν O) := by
          rw [hηdef, ENNReal.ofReal_mul hδ.le, ENNReal.ofReal_toReal hc', mul_assoc]
      _ ≤ ENNReal.ofReal δ * μ (f ⁻¹' (ι '' O) ∩ W) :=
          mul_le_mul_right (hlb O (fun b hb => (hOsub hb).1.1) hOm) _
      _ = ∫⁻ v in f ⁻¹' (ι '' O) ∩ W, ENNReal.ofReal δ ∂μ := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ v in f ⁻¹' (ι '' O) ∩ W, ψ v ∂μ :=
          setLIntegral_mono hψm fun v hv => by
            show ENNReal.ofReal δ ≤ (f ⁻¹' (ι '' O)).indicator (fun v => ENNReal.ofReal (φ v)) v
            rw [indicator_of_mem hv.1]
            exact ENNReal.ofReal_le_ofReal (hWφ v hv.2)
      _ ≤ ∫⁻ v in U, ψ v ∂μ := lintegral_mono_set (inter_subset_right.trans hWU)
  rw [hdis] at hlow
  exact lt_irrefl _ (hlow.trans_lt hup)

theorem gramR_ratTup {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X0 : Fin n → Fin M → E) :
    gramR R σ J (ratTup R X0) = (gramE σ J X0).map (inclR R) := by
  have hs : ∀ e : E, sigR R σ (inclR R e) = inclR R (σ e) := fun e => by
    simp [sigR, inclR, Algebra.TensorProduct.map_tmul]
  ext p q
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gramR, hR, gramE, hE, Formalism.UG.hform, Matrix.map_apply, ratTup, JR, map_sum, map_mul, hs]
  rfl

end LocPosW

open LocPosW

def LBInf : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ (μinf : Measure (Fin a → Fin M → Ainf F ⊗[F] E)) (νinf : Measure (HermR (Ainf F) σ a)),
    μinf.IsAddHaarMeasure → νinf.IsAddHaarMeasure →
    ∀ W : Set (Fin a → Fin M → Ainf F ⊗[F] E), IsOpen W → ratTup (F := F) (Ainf F) X0 ∈ W →
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ⊤ ∧ ∃ N ∈ 𝓝 (hermOf (Ainf F) σ (gramE σ J X0) hT),
      ∀ S ⊆ N, MeasurableSet S →
        c * νinf S ≤ μinf ((gramR (Ainf F) σ J) ⁻¹' (Subtype.val '' S) ∩ W)

theorem archPos_of_lb (hL : LBInf) : ArchPos := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμ νinf hν fibInf hfib
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  have := hμ.1
  have := hν.1
  obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ :=
    (tensAll_holds F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet).1
  have : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (HermR (Ainf F) σ a) := ⟨rfl⟩
  have : LocallyCompactSpace (HermR (Ainf F) σ a) :=
    t4.isClosedEmbedding_subtypeVal.locallyCompactSpace
  set X1 := ratTup (F := F) (Ainf F) X0 with hX1
  have hX1U : X1 ∈ {X : Fin a → Fin M → Ainf F ⊗[F] E | LinearIndependent (Ainf F ⊗[F] E) X} :=
    linIndep_of_isUnit_det (Ainf F) σ J X1
      (by rw [gramR_ratTup]; exact isUnit_det_hermOf (Ainf F) σ _ hT hdet)
  obtain ⟨K, hK, hxK, hKU⟩ := exists_compact_subset t7 hX1U
  obtain ⟨φ, hφ1, hφ0, hφc, hφr⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_singleton (x := X1)) isOpen_interior.isClosed_compl
    (disjoint_singleton_left.2 fun h => h hxK)
  have hsupp : Function.support φ ⊆ interior K := fun X hX => by
    by_contra h
    exact hX (hφ0 h)
  have hts : tsupport φ ⊆ {X : Fin a → Fin M → Ainf F ⊗[F] E | LinearIndependent (Ainf F ⊗[F] E) X} :=
    (closure_mono hsupp).trans ((closure_minimal interior_subset hK.isClosed).trans hKU)
  let W : Set (Fin a → Fin M → Ainf F ⊗[F] E) := {X | (1 / 2 : ℝ) < φ X}
  have hWo : IsOpen W := isOpen_lt continuous_const φ.continuous
  have hX1W : X1 ∈ W := by
    show (1 / 2 : ℝ) < φ X1
    rw [hφ1 (mem_singleton X1)]
    norm_num
  have hWU : W ⊆ {X : Fin a → Fin M → Ainf F ⊗[F] E | LinearIndependent (Ainf F ⊗[F] E) X} :=
    fun X hX => hts (subset_tsupport _ (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hX).ne')
  obtain ⟨c, hc0, hctop, N, hN, hlb⟩ :=
    hL F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet μinf νinf hμ.1 hν.1 W hWo hX1W
  have hpos := pos_of_lb (f' := gramH (Ainf F) σ hσ J hJ.1) Subtype.val_injective hfib
    (continuous_gramH (Ainf F) σ hσ J hJ.1) (fun _ => rfl) φ.continuous hφc hts
    (fun X => (hφr X).1) hWU (by norm_num : (0 : ℝ) < 1 / 2) (fun X hX => hX.le) hc0 hctop hN hlb
    (fun O hO hne => (hO.measure_pos νinf hne).ne') (νinf.finiteAt_nhds _)
  refine ⟨fun X => ((φ X : ℝ) : ℂ), Complex.continuous_ofReal.comp φ.continuous,
    hφc.comp_left Complex.ofReal_zero, ?_⟩
  rw [integral_complex_ofReal]
  exact_mod_cast hpos.ne'

end PI.VolStabS
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.UnifVSpec
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensAAOf
noncomputable section

namespace PI.VolStabS

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW

def ResAA : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J), SWa1 F E σ M J → Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility F E σ M J →
    ∀ (a : ℕ), 1 ≤ a → 2 * a < M → ∀ (X0 : Fin a → Fin M → E)
    (hT : ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j), (gramE σ J X0).det ≠ 0 →
    ∀ ψ, IsCharAF F ψ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E),
    ∀ᶠ v in cofinite,
    ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
    ∀ νv, SdHerm F E σ (Fv F v) (psiV F ψ v) a νv →
    ∃ (L : AddSubgroup (Fin a → Fin M → Fv F v ⊗[F] E))
      (Λ : ℕ → AddSubgroup (Fin a → Fin M → Fv F v ⊗[F] E))
      (H : ℕ → AddSubgroup (HermR (Fv F v) σ a)),
      (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)) = latV b v ∧
      IsOpen (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)) ∧
      IsCompact (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)) ∧ Λ 0 ≤ L ∧
      (∀ n, IsOpen (Λ n : Set (Fin a → Fin M → Fv F v ⊗[F] E))) ∧
      (∀ n, IsCompact (Λ n : Set (Fin a → Fin M → Fv F v ⊗[F] E))) ∧ Antitone Λ ∧
      (∀ n, IsOpen (H n : Set (HermR (Fv F v) σ a))) ∧
      (∀ n, IsCompact (H n : Set (HermR (Fv F v) σ a))) ∧
      (∀ N' ∈ 𝓝 (0 : HermR (Fv F v) σ a), ∃ n, (H n : Set (HermR (Fv F v) σ a)) ⊆ N') ∧
      (∀ y ∈ L, gramH (Fv F v) σ (sigma_invol σ hCM.2.2.2) J hJ.1 y - hermOf (Fv F v) σ (gramE σ J X0) hT ∈ H 0 →
        ∃ D : (Fin a → Fin M → Fv F v ⊗[F] E) →+ HermR (Fv F v) σ a,
          (∀ n, (Λ n).map D = H n) ∧ ∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n,
            gramH (Fv F v) σ (sigma_invol σ hCM.2.2.2) J hJ.1 (y + Z + W) - gramH (Fv F v) σ (sigma_invol σ hCM.2.2.2) J hJ.1 (y + Z) - D W ∈
              H (n + 1)) ∧
      ∃ (k K : Type) (_ : Field k) (_ : Finite k) (_ : CommRing K) (_ : Algebra k K)
        (σ' : K ≃ₐ[k] K) (J' : Matrix (Fin M) (Fin M) K) (T' : Matrix (Fin a) (Fin a) K),
        IsQuadInv k K σ' ∧ (2 : k) ≠ 0 ∧ (∀ i j, σ' (J' j i) = J' i j) ∧ IsUnit J'.det ∧
        (∀ i j, σ' (T' j i) = T' i j) ∧ IsUnit T'.det ∧ (Nat.card k : ℝ) = qV v ∧
        ((μv ((L : Set (Fin a → Fin M → Fv F v ⊗[F] E)) ∩
            gramH (Fv F v) σ (sigma_invol σ hCM.2.2.2) J hJ.1 ⁻¹' {z | z - hermOf (Fv F v) σ (gramE σ J X0) hT ∈ H 0})) /
            νv (H 0)).toReal =
          (Nat.card {X : Fin a → Fin M → K // ffGram (σ' : K →+* K) J' X = T'} : ℝ) /
            (Nat.card k : ℝ) ^ (2 * M * a - a ^ 2)

theorem densAA_of (hFL : FibLat) (hFF : FFCount) (hR : ResAA) : DensAA := by
  intro F E _ _ _ _ _ σ hCM M J hJ hSa hSc a ha1 ha2 X0 hT hdet ψ hψ d b
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  obtain ⟨C, hC⟩ := hFF M
  refine ⟨C, ?_⟩
  filter_upwards [hR F E σ hCM M J hJ hSa hSc a ha1 ha2 X0 hT hdet ψ hψ d b] with v hv
  intro μv hμv νv hνv fibV hfib
  have := secondCountable_Fv F v
  have := locallyCompact_Fv F v
  have := hμv.1
  have := hνv.1
  obtain ⟨L, Λ, H, hL, hLo, hLc, hΛL, hΛo, hΛc, hΛa, hHo, hHc, hHb, hyp, k, K, _, _, _, _, σ', J',
    T', hQ, h2, hJ', hJu, hT', hTu, hq, hcnt⟩ := hv μv hμv νv hνv
  have : SecondCountableTopology (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin a → Fin a → Fv F v ⊗[F] E))
  have : T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))
  have : LocallyCompactSpace (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin a → Fin a → Fv F v ⊗[F] E))
  have : SecondCountableTopology (HermR (Fv F v) σ a) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have hN := isOpen_unitHerm (Fv F v) (isOpen_units_Fv F v) σ a
  have e := hFL _ _ _ μv νv hμv.1 hνv.1 (gramR (Fv F v) σ J) Subtype.val Subtype.val_injective
    (gramH (Fv F v) σ (sigma_invol σ hCM.2.2.2) J hJ.1) (continuous_gramH (Fv F v) σ (sigma_invol σ hCM.2.2.2) J hJ.1) (fun _ => rfl) _ _ fibV hfib
    (hermOf (Fv F v) σ (gramE σ J X0) hT) Filter.univ_mem _
    (hN.mem_nhds (isUnit_det_hermOf (Fv F v) σ _ hT hdet))
    (fun X hX => linIndep_of_isUnit_det (Fv F v) σ J X hX) L hLo hLc Λ H hΛL hΛo hΛc hΛa hHo hHc
    hHb hyp
  rw [hcnt, hL] at e
  rw [e]
  have hb := hC k K σ' hQ h2 J' hJ' hJu a (by omega) T' hT' hTu
  rw [← hq]
  have : ((((Nat.card {X : Fin a → Fin M → K // ffGram (σ' : K →+* K) J' X = T'} : ℝ) /
      (Nat.card k : ℝ) ^ (2 * M * a - a ^ 2) : ℝ) : ℂ) - 1) =
      (((Nat.card {X : Fin a → Fin M → K // ffGram (σ' : K →+* K) J' X = T'} : ℝ) /
      (Nat.card k : ℝ) ^ (2 * M * a - a ^ 2) - 1 : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_real, Real.norm_eq_abs]
  exact hb

end PI.VolStabS
end
end

noncomputable section

namespace PI.VolStabS

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW

def unifV {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) : Fv F v :=
  ((v.valuation_exists_uniformizer F).choose : Fv F v)

theorem unifV_val {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v (unifV v) = WithZero.exp (-1 : ℤ) := by
  rw [unifV, v.valuedAdicCompletion_eq_valuation', (v.valuation_exists_uniformizer F).choose_spec]

theorem unifV_spec {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    unifV v ≠ 0 ∧ Tendsto (fun k : ℕ => unifV v ^ k) atTop (𝓝 0) ∧
      unifV v ∈ v.adicCompletionIntegers F := by
  have hv := unifV_val v
  have h1 : Valued.v (unifV v) < 1 := by
    rw [hv]
    decide
  refine ⟨fun h => ?_, ?_, ?_⟩
  · rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  · have hlt : ‖unifV v‖ < 1 := Valued.toNormedField.norm_lt_one_iff.2 h1
    exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one hlt
  · rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    exact h1.le

def lamF {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (a M : ℕ) (n : ℕ) :
    AddSubgroup (Fin a → Fin M → Fv F v ⊗[F] E) :=
  smulSub (unifV v ^ (n + 1)) (latSub b v a M)

def hF {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (a : ℕ)
    (n : ℕ) : AddSubgroup (HermR (Fv F v) σ a) :=
  smulSub (unifV v ^ (n + 1)) (hermO b v σ a)

def LatFacts : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (σ : E →ₐ[F] E) (d : ℕ) (b : Module.Basis (Fin d) F E) (a M : ℕ)
    (v : HeightOneSpectrum (𝓞 F)),
    (∀ n, IsOpen (lamF b v a M n : Set (Fin a → Fin M → Fv F v ⊗[F] E))) ∧
    (∀ n, IsCompact (lamF b v a M n : Set (Fin a → Fin M → Fv F v ⊗[F] E))) ∧
    Antitone (lamF b v a M) ∧ lamF b v a M 0 ≤ latSub b v a M ∧
    (∀ n, IsOpen (hF b v σ a n : Set (HermR (Fv F v) σ a))) ∧
    (∀ n, IsCompact (hF b v σ a n : Set (HermR (Fv F v) σ a))) ∧
    (∀ N' ∈ 𝓝 (0 : HermR (Fv F v) σ a), ∃ n, (hF b v σ a n : Set (HermR (Fv F v) σ a)) ⊆ N')

def HensAA : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J), SWa1 F E σ M J → Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility F E σ M J →
    ∀ (a : ℕ), 1 ≤ a → 2 * a < M → ∀ (X0 : Fin a → Fin M → E)
    (hT : ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j), (gramE σ J X0).det ≠ 0 →
    ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v in cofinite,
    ∀ y ∈ latSub b v a M, gramH (Fv F v) σ (sigma_invol σ hCM.2.2.2) J hJ.1 y - hermOf (Fv F v) σ (gramE σ J X0) hT ∈ hF b v σ a 0 →
      ∃ D : (Fin a → Fin M → Fv F v ⊗[F] E) →+ HermR (Fv F v) σ a,
        (∀ n, (lamF b v a M n).map D = hF b v σ a n) ∧ ∀ n, ∀ Z ∈ lamF b v a M 0,
          ∀ W ∈ lamF b v a M n, gramH (Fv F v) σ (sigma_invol σ hCM.2.2.2) J hJ.1 (y + Z + W) - gramH (Fv F v) σ (sigma_invol σ hCM.2.2.2) J hJ.1 (y + Z) - D W ∈ hF b v σ a (n + 1)

def IdxAA : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J), SWa1 F E σ M J → Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility F E σ M J →
    ∀ (a : ℕ), 1 ≤ a → 2 * a < M → ∀ (X0 : Fin a → Fin M → E)
    (hT : ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j), (gramE σ J X0).det ≠ 0 →
    ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v in cofinite,
    ∀ (μ : Measure (Fin a → Fin M → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ a)), μ.IsAddHaarMeasure →
      ν.IsAddHaarMeasure →
      μ (latV b v) = (Nat.card (𝓞 F ⧸ v.asIdeal) : ENNReal) ^ (2 * M * a) * μ (lamF b v a M 0) ∧
      ν (hermO b v σ a) = (Nat.card (𝓞 F ⧸ v.asIdeal) : ENNReal) ^ (a ^ 2) * ν (hF b v σ a 0)

def CntAA : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J), SWa1 F E σ M J → Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility F E σ M J →
    ∀ (a : ℕ), 1 ≤ a → 2 * a < M → ∀ (X0 : Fin a → Fin M → E)
    (hT : ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j), (gramE σ J X0).det ≠ 0 →
    ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v in cofinite,
    ∀ (μ : Measure (Fin a → Fin M → Fv F v ⊗[F] E)), μ.IsAddHaarMeasure →
      ∃ (k K : Type) (_ : Field k) (_ : Finite k) (_ : CommRing K) (_ : Algebra k K)
        (σ' : K ≃ₐ[k] K) (J' : Matrix (Fin M) (Fin M) K) (T' : Matrix (Fin a) (Fin a) K),
        IsQuadInv k K σ' ∧ (2 : k) ≠ 0 ∧ (∀ i j, σ' (J' j i) = J' i j) ∧ IsUnit J'.det ∧
        (∀ i j, σ' (T' j i) = T' i j) ∧ IsUnit T'.det ∧
        Nat.card k = Nat.card (𝓞 F ⧸ v.asIdeal) ∧
        μ (latV b v ∩ gramH (Fv F v) σ (sigma_invol σ hCM.2.2.2) J hJ.1 ⁻¹' {z | z - hermOf (Fv F v) σ (gramE σ J X0) hT ∈ hF b v σ a 0}) =
          (Nat.card {X : Fin a → Fin M → K // ffGram (σ' : K →+* K) J' X = T'} : ENNReal) *
            μ (lamF b v a M 0)

theorem resAA_of (hV : VolAA) (hL : LatFacts) (hH : HensAA) (hI : IdxAA) (hC : CntAA) :
    ResAA := by
  intro F E _ _ _ _ _ σ hCM M J hJ hSa hSc a ha1 ha2 X0 hT hdet ψ hψ d b
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  filter_upwards [hV F E σ hCM M J hJ hSa hSc a ha1 ha2 X0 hT hdet ψ hψ d b,
    hH F E σ hCM M J hJ hSa hSc a ha1 ha2 X0 hT hdet d b,
    hI F E σ hCM M J hJ hSa hSc a ha1 ha2 X0 hT hdet d b,
    hC F E σ hCM M J hJ hSa hSc a ha1 ha2 X0 hT hdet d b] with v hv hh hi hc
  intro μv hμ νv hν
  have := hμ.1
  have := hν.1
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := hL F E σ d b a M v
  refine ⟨latSub b v a M, lamF b v a M, hF b v σ a, rfl,
    (PositiveNearLattice.isClopen_latV b v a M).isOpen, PositiveNearLattice.isCompact_latV b v a M, l4, l1, l2, l3,
    l5, l6, l7, hh, ?_⟩
  obtain ⟨k, K, i1, i2, i3, i4, σ', J', T', hQ, h2, hJ', hJu, hT', hTu, hcard, hcnt⟩ :=
    hc μv hμ.1
  refine ⟨k, K, i1, i2, i3, i4, σ', J', T', hQ, h2, hJ', hJu, hT', hTu, ?_, ?_⟩
  · rw [hcard]; rfl
  obtain ⟨e1, e2⟩ := hi μv νv hμ.1 hν.1
  rw [hv.1 μv hμ, ← hcard] at e1
  rw [hv.2 νv hν, ← hcard] at e2
  show (μv (latV b v ∩ _) / νv _).toReal = _
  rw [hcnt, ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have f1 := congrArg ENNReal.toReal e1
  have f2 := congrArg ENNReal.toReal e2
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_one] at f1 f2
  have hq : (0 : ℝ) < Nat.card k := by exact_mod_cast Nat.card_pos
  have hle : a ^ 2 ≤ 2 * M * a := by nlinarith
  have hp : (Nat.card k : ℝ) ^ (2 * M * a) = (Nat.card k : ℝ) ^ (2 * M * a - a ^ 2) *
      (Nat.card k : ℝ) ^ (a ^ 2) := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  have hA : (0 : ℝ) < (Nat.card k : ℝ) ^ (2 * M * a - a ^ 2) := pow_pos hq _
  have hB : (0 : ℝ) < (Nat.card k : ℝ) ^ (a ^ 2) := pow_pos hq _
  rw [hp] at f1
  have hn : (νv (hF b v σ a 0)).toReal = 1 / (Nat.card k : ℝ) ^ (a ^ 2) := by
    field_simp; linarith
  have hm : (μv (lamF b v a M 0)).toReal =
      1 / ((Nat.card k : ℝ) ^ (2 * M * a - a ^ 2) * (Nat.card k : ℝ) ^ (a ^ 2)) := by
    field_simp; linarith
  rw [hm, hn]
  field_simp

end PI.VolStabS
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.PullLocSt
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Matrix
open scoped TensorProduct

def CompG : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ g : HA (AF F) σ J, ∃ (hInf : HA (Ainf F) σ J) (hv : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J),
    (∀ X : Fin a → Fin M → AF F ⊗[F] E, projInf (g • X) = hInf • projInf X) ∧
    (∀ (v : HeightOneSpectrum (𝓞 F)) (X : Fin a → Fin M → AF F ⊗[F] E),
      projV v (projFin (g • X)) = hv v • projV v (projFin X)) ∧
    ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v in Filter.cofinite,
      ∀ Y : Fin a → Fin M → Fv F v ⊗[F] E, hv v • Y ∈ latV b v ↔ Y ∈ latV b v

def FibInvInf : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ μinf, SdW F E σ M J (Ainf F) (psiInf F ψ) a μinf →
    ∀ νinf, SdHerm F E σ (Ainf F) (psiInf F ψ) a νinf →
    ∀ fibInf : HermR (Ainf F) σ a → Measure (Fin a → Fin M → Ainf F ⊗[F] E),
    IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
      {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fibInf →
    ∀ (h : HA (Ainf F) σ J) (Φinf : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ),
      Continuous Φinf → HasCompactSupport Φinf →
      ∫ X, Φinf (h • X) ∂(fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT)) =
        ∫ X, Φinf X ∂(fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT))

def FibInvV : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F),
    ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
    ∀ νv, SdHerm F E σ (Fv F v) (psiV F ψ v) a νv →
    ∀ fibV : HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E),
    IsFibreFamily μv (gramR (Fv F v) σ J) Subtype.val
      {X | LinearIndependent (Fv F v ⊗[F] E) X} νv Set.univ fibV →
    ∀ (h : HA (Fv F v) σ J) (Φv : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ), IsSB Φv →
      ∫ X, Φv (h • X) ∂(fibV (hermOf (Fv F v) σ (gramE σ J X0) hT)) =
        ∫ X, Φv X ∂(fibV (hermOf (Fv F v) σ (gramE σ J X0) hT))

def smulHomeo {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    (σ : E →ₐ[F] E) {M a : ℕ} (J : Matrix (Fin M) (Fin M) E) (h : HA R σ J) :
    (Fin a → Fin M → R ⊗[F] E) ≃ₜ (Fin a → Fin M → R ⊗[F] E) where
  toEquiv := MulAction.toPerm h
  continuous_toFun := by
    refine continuous_pi fun x => ?_
    change Continuous fun y : Fin a → Fin M → R ⊗[F] E =>
      ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) _) *ᵥ (y x)
    exact continuous_const.matrix_mulVec (continuous_apply x)
  continuous_invFun := by
    refine continuous_pi fun x => ?_
    change Continuous fun y : Fin a → Fin M → R ⊗[F] E =>
      ((HA.mat R σ J h⁻¹ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) _) *ᵥ (y x)
    exact continuous_const.matrix_mulVec (continuous_apply x)

theorem pullLoc_of (hC : CompG) (hI : FibInvInf) (hV : FibInvV) : PullLoc := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ g d b Φ Φinf Φf Φv hcΦ hcs
    hpure hprod
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  obtain ⟨hInf, hv, h1, h2, h3⟩ := hC F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet g
  let eI := smulHomeo (Ainf F) σ (a := a) J hInf
  let eV := fun v => smulHomeo (Fv F v) σ (a := a) J (hv v)
  refine ⟨fun Y => Φinf (hInf • Y), fun Y => ∏ᶠ v, Φv v (hv v • projV v Y),
    fun v Y => Φv v (hv v • Y), hcΦ.comp eI.continuous, hcs.comp_homeomorph eI, ⟨?_, ?_, fun _ => rfl⟩,
    ?_, ?_, ?_⟩
  · intro v
    exact ⟨(hpure.1 v).1.comp_continuous (eV v).continuous, (hpure.1 v).2.comp_homeomorph (eV v)⟩
  · filter_upwards [hpure.2.1, h3 d b] with v hv1 hv2
    funext Y
    simp only [hv1, Set.indicator, Pi.one_apply]
    by_cases hY : Y ∈ latV b v
    · rw [if_pos ((hv2 Y).2 hY), if_pos hY]
    · rw [if_neg (fun h => hY ((hv2 Y).1 h)), if_neg hY]
  · intro X
    show Φ (g • X) = Φinf (hInf • projInf X) * ∏ᶠ v, Φv v (hv v • projV v (projFin X))
    rw [hprod (g • X), h1 X, hpure.2.2]
    congr 1
    refine finprod_congr fun v => ?_
    rw [h2 v X]
  · exact fun μinf hμinf νinf hνinf fibInf hfi =>
      hI F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμinf νinf hνinf fibInf hfi hInf Φinf
        hcΦ hcs
  · exact fun v μv hμv νv hνv fibV hfv =>
      hV F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v μv hμv νv hνv fibV hfv (hv v) (Φv v)
        (hpure.1 v)

end PI.VolStabS
end
end
