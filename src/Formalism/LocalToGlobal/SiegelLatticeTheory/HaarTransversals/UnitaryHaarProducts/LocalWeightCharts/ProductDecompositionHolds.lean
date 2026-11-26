module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.StarOfInv

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.ProductDecompositionHolds
noncomputable section

open MeasureTheory Matrix Topology
open scoped ENNReal NNReal Pointwise

namespace WlocSk.HM

open Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

def jinv (g : Mx k r) : Mx k r := Hpk k r * gᴴ * Hpk k r

lemma jinv_mul {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : jinv g * g = 1 := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  unfold jinv
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
    _ = Hpk k r * Hpk k r := by rw [hg']
    _ = 1 := Formalism.QuantumDeterminants.GBasic.Hpk_sq k r

lemma mul_jinv {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g * jinv g = 1 := mul_eq_one_comm.mp (jinv_mul hg)

lemma jinv_eq {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g⁻¹ = jinv g := Matrix.inv_eq_left_inv (jinv_mul hg)

lemma jinv_cont : Continuous (fun g : Mx k r => jinv g) :=
  (continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const

lemma lmul_meas (a : Mx k r) : Measurable (lmulM (k := k) (r := r) a) := by
  have hc : Continuous (lmulM (k := k) (r := r) a) := by
    unfold Formalism.QuantumDeterminants.lmulM
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Matrix.mul_apply, Matrix.of_apply]
    exact continuous_finsetSum _ fun l _ => by fun_prop
  exact hc.measurable

lemma mulP_meas : Measurable (mulP : Mt k r × Mt k r → Mt k r) := by
  have hc : Continuous (mulP : Mt k r × Mt k r → Mt k r) := by
    unfold WlocSk.mulP
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Matrix.mul_apply, Matrix.of_apply]
    exact continuous_finsetSum _ fun l _ => by fun_prop
  exact hc.measurable

theorem s_closed (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hT : 0 < Tz k r z) :
    IsClosed (Sset k r z : Set (Mx k r)) := by
  have hE : IsClosedEmbedding (Grp.val : Grp (UH (Hpk k r) : Set (Mx k r)) uh_clsub → Mx k r) := Grp.emb
  let A : Set (Grp (UH (Hpk k r) : Set (Mx k r)) uh_clsub) := Grp.val ⁻¹' (UWset k r z : Set (Mx k r))
  let B : Set (Grp (UH (Hpk k r) : Set (Mx k r)) uh_clsub) := Grp.val ⁻¹' (Nset k r : Set (Mx k r))
  have hA : IsCompact A := hE.isCompact_preimage (compactW z hz hT)
  have hB : IsClosed B := n_closed.preimage hE.continuous
  have hAB : IsClosed (A * B) := hB.mul_left_of_isCompact hA
  have himg : Grp.val '' (A * B) = (Sset k r z : Set (Mx k r)) := by
    ext s
    constructor
    · rintro ⟨x, ⟨a, ha, b, hb, rfl⟩, rfl⟩
      exact ⟨a.val, ha, b.val, hb, rfl⟩
    · rintro ⟨h, hh, m, hm, rfl⟩
      exact ⟨Grp.mk h hh.1 * Grp.mk m hm.1, ⟨Grp.mk h hh.1, hh, Grp.mk m hm.1, hm, rfl⟩, rfl⟩
  rw [← himg]
  exact hE.isClosedMap _ hAB

theorem s_clsub (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hconj : ∀ h ∈ UWset k r z, ∀ m ∈ Nset k r, h⁻¹ * m * h ∈ Nset k r) :
    ClSub (Sset k r z : Set (Mx k r)) := by
  have hW := uw_clsub (k := k) (r := r) z
  have hN := n_clsub (k := k) (r := r)
  refine ⟨⟨1, hW.one_mem, 1, hN.one_mem, (Matrix.mul_one 1).symm⟩, ?_, ?_, ?_, s_closed z hz hT⟩
  · rintro _ ⟨h, hh, m, hm, rfl⟩ _ ⟨h', hh', m', hm', rfl⟩
    refine ⟨h * h', hW.mul_mem _ hh _ hh', h'⁻¹ * m * h' * m', hN.mul_mem _ (hconj h' hh' m hm) _ hm', ?_⟩
    have e : h' * h'⁻¹ = 1 := Matrix.mul_nonsing_inv h' (hW.unit h' hh')
    calc h * m * (h' * m') = h * (h' * h'⁻¹) * m * h' * m' := by
          rw [e]; simp only [Matrix.mul_assoc, Matrix.mul_one]
      _ = h * h' * (h'⁻¹ * m * h' * m') := by simp only [Matrix.mul_assoc]
  · rintro _ ⟨h, hh, m, hm, rfl⟩
    have hi := hW.inv_mem h hh
    have hu := hW.unit h hh
    refine ⟨h⁻¹, hi, h * m⁻¹ * h⁻¹, ?_, ?_⟩
    · have := hconj h⁻¹ hi m⁻¹ (hN.inv_mem m hm)
      rwa [Matrix.nonsing_inv_nonsing_inv h hu] at this
    · rw [Matrix.mul_inv_rev]
      calc m⁻¹ * h⁻¹ = (h⁻¹ * h) * m⁻¹ * h⁻¹ := by rw [Matrix.nonsing_inv_mul h hu, Matrix.one_mul]
        _ = h⁻¹ * (h * m⁻¹ * h⁻¹) := by simp only [Matrix.mul_assoc]
  · rintro _ ⟨h, hh, m, hm, rfl⟩
    rw [Matrix.det_mul]
    exact (hW.unit h hh).mul (hN.unit m hm)

theorem prod_haar (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hconj : ∀ h ∈ UWset k r z, ∀ m ∈ Nset k r, h⁻¹ * m * h ∈ Nset k r)
    (μW μN : Measure (Mt k r)) (hW : IsHaarOn (UWset k r z) μW) (hN : IsHaarOn (Nset k r) μN)
    [IsFiniteMeasure μW] (hNc : ∀ K : Set (Mt k r), IsCompact K → μN K < ⊤) :
    IsHaarOn (Sset k r z) ((μW.prod μN).map mulP) := by
  obtain ⟨hσW, hW0, hWc, hWl⟩ := hW
  obtain ⟨hσN, hN0, hNcc, hNl⟩ := hN
  have hSc := s_clsub z hz hT hconj
  have hm := mulP_meas (k := k) (r := r)
  have aeW : ∀ᵐ p ∂(μW.prod μN), (Matrix.of p.1 : Mx k r) ∈ UWset k r z := by
    rw [ae_iff]
    have : {p : Mt k r × Mt k r | ¬ (Matrix.of p.1 : Mx k r) ∈ UWset k r z} =
        {x : Mt k r | Matrix.of x ∉ UWset k r z} ×ˢ Set.univ := by
      ext p; exact ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩
    rw [this, Measure.prod_prod, hWc, zero_mul]
  have aeN : ∀ᵐ p ∂(μW.prod μN), (Matrix.of p.2 : Mx k r) ∈ Nset k r := by
    rw [ae_iff]
    have : {p : Mt k r × Mt k r | ¬ (Matrix.of p.2 : Mx k r) ∈ Nset k r} =
        Set.univ ×ˢ {x : Mt k r | Matrix.of x ∉ Nset k r} := by
      ext p; exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
    rw [this, Measure.prod_prod, hNcc, mul_zero]

  have hUWc : @IsCompact (Mt k r) _ (UWset k r z) := compactW z hz hT
  have hfc : ∀ K : Set (Mt k r), IsCompact K → ((μW.prod μN).map mulP) K < ⊤ := by
    intro K hK
    let f : Mt k r × Mt k r → Mt k r := fun q => (jinv (Matrix.of q.1) * Matrix.of q.2 : Mx k r)
    have hf : Continuous f := (jinv_cont.comp continuous_fst).matrix_mul continuous_snd
    have hK' : IsCompact (f '' ((UWset k r z : Set (Mt k r)) ×ˢ K)) := (hUWc.prod hK).image hf
    have hsub : (mulP ⁻¹' K : Set (Mt k r × Mt k r)) ≤ᵐ[μW.prod μN]
        (Set.univ ×ˢ (f '' ((UWset k r z : Set (Mt k r)) ×ˢ K))) := by
      filter_upwards [aeW] with p h1 hp
      refine ⟨trivial, ⟨(p.1, mulP p), ⟨h1, hp⟩, ?_⟩⟩
      show jinv (Matrix.of p.1) * (Matrix.of p.1 * Matrix.of p.2) = Matrix.of p.2
      rw [← Matrix.mul_assoc, jinv_mul h1.1, Matrix.one_mul]
    rw [Measure.map_apply hm hK.isClosed.measurableSet]
    refine lt_of_le_of_lt (measure_mono_ae hsub) ?_
    rw [Measure.prod_prod]
    exact ENNReal.mul_lt_top (measure_lt_top μW _) (hNc _ hK')

  have hρ0 : (μW.prod μN).map mulP ≠ 0 := by
    intro h0
    have h1 := congrArg (fun ν : Measure (Mt k r) => ν Set.univ) h0
    simp only [Measure.map_apply hm MeasurableSet.univ, FunLike.coe_zero, Pi.zero_apply] at h1
    rw [Set.preimage_univ, ← Set.univ_prod_univ, Measure.prod_prod, mul_eq_zero] at h1
    rcases h1 with h | h
    · exact hW0 (Measure.measure_univ_eq_zero.mp h)
    · exact hN0 (Measure.measure_univ_eq_zero.mp h)

  have hSm : MeasurableSet {x : Mt k r | Matrix.of x ∉ Sset k r z} :=
    (show @IsClosed (Mt k r) _ (Sset k r z) from hSc.closed).measurableSet.compl
  have hconc : ((μW.prod μN).map mulP) {x : Mt k r | Matrix.of x ∉ Sset k r z} = 0 := by
    rw [Measure.map_apply hm hSm]
    have hae : ∀ᵐ p ∂(μW.prod μN), ¬ (p ∈ mulP ⁻¹' {x : Mt k r | Matrix.of x ∉ Sset k r z}) := by
      filter_upwards [aeW, aeN] with p h1 h2
      intro hp
      exact hp ⟨Matrix.of p.1, h1, Matrix.of p.2, h2, rfl⟩
    exact measure_mono_null (fun p hp => not_not_intro hp) (ae_iff.mp hae)

  have leftW : ∀ h₀ ∈ UWset k r z, ((μW.prod μN).map mulP).map (lmulM h₀) = (μW.prod μN).map mulP := by
    intro h₀ hh₀
    rw [Measure.map_map (lmul_meas h₀) hm]
    have e : (lmulM h₀ ∘ mulP : Mt k r × Mt k r → Mt k r) = mulP ∘ Prod.map (lmulM h₀) id := by
      funext p
      exact (Matrix.mul_assoc h₀ (Matrix.of p.1) (Matrix.of p.2)).symm
    rw [e, ← Measure.map_map hm ((lmul_meas h₀).prodMap measurable_id),
      ← Measure.map_prod_map _ _ (lmul_meas h₀) measurable_id, hWl h₀ hh₀, Measure.map_id]

  have leftN : ∀ m₀ ∈ Nset k r, ((μW.prod μN).map mulP).map (lmulM m₀) = (μW.prod μN).map mulP := by
    intro m₀ hm₀
    rw [Measure.map_map (lmul_meas m₀) hm]
    let g : Mt k r → Mt k r → Mt k r := fun h m => lmulM (jinv (Matrix.of h) * m₀ * Matrix.of h) m
    have hgm : Measurable (Function.uncurry g) := by
      have : Continuous (Function.uncurry g) := by
        show Continuous fun q : Mt k r × Mt k r =>
          ((jinv (Matrix.of q.1) * m₀ * Matrix.of q.1) * Matrix.of q.2 : Mx k r)
        exact (((jinv_cont.comp continuous_fst).matrix_mul continuous_const).matrix_mul
          continuous_fst).matrix_mul continuous_snd
      exact this.measurable
    have hg : ∀ᵐ h ∂μW, μN.map (g h) = μN := by
      rw [ae_iff]
      refine measure_mono_null (fun h hh => ?_) hWc
      intro hin
      apply hh
      have hc : jinv (Matrix.of h) * m₀ * Matrix.of h ∈ Nset k r := by
        rw [← jinv_eq hin.1]; exact hconj _ hin _ hm₀
      exact hNl _ hc
    have hT := MeasurePreserving.skew_product (MeasurePreserving.id μW) hgm hg
    have hae : (lmulM m₀ ∘ mulP : Mt k r × Mt k r → Mt k r) =ᵐ[μW.prod μN]
        mulP ∘ (fun p : Mt k r × Mt k r => (id p.1, g p.1 p.2)) := by
      filter_upwards [aeW] with p h1
      show m₀ * (Matrix.of p.1 * Matrix.of p.2) =
        Matrix.of p.1 * ((jinv (Matrix.of p.1) * m₀ * Matrix.of p.1) * Matrix.of p.2)
      have e := mul_jinv h1.1
      calc m₀ * (Matrix.of p.1 * Matrix.of p.2)
          = (Matrix.of p.1 * jinv (Matrix.of p.1)) * m₀ * Matrix.of p.1 * Matrix.of p.2 := by
            rw [e, Matrix.one_mul, Matrix.mul_assoc]
        _ = Matrix.of p.1 * ((jinv (Matrix.of p.1) * m₀ * Matrix.of p.1) * Matrix.of p.2) := by
            simp only [Matrix.mul_assoc]
    rw [Measure.map_congr hae, ← Measure.map_map hm hT.measurable, hT.map_eq]
  refine ⟨sigma_of_compact _ hfc, hρ0, hconc, ?_⟩
  rintro _ ⟨h₀, hh₀, m₀, hm₀, rfl⟩
  have e : (lmulM (h₀ * m₀) : Mt k r → Mt k r) = lmulM h₀ ∘ lmulM m₀ := by
    funext x; exact Matrix.mul_assoc h₀ m₀ (Matrix.of x)
  rw [e, ← Measure.map_map (lmul_meas h₀) (lmul_meas m₀), leftN m₀ hm₀, leftW h₀ hh₀]

theorem sprod_main (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hconj : ∀ h ∈ UWset k r z, ∀ m ∈ Nset k r, h⁻¹ * m * h ∈ Nset k r)
    (μW μN μS : Measure (Mt k r)) (hW : IsHaarOn (UWset k r z) μW) (hN : IsHaarOn (Nset k r) μN)
    [IsFiniteMeasure μW] (hNc : ∀ K : Set (Mt k r), IsCompact K → μN K < ⊤) (hS : IsHaarOn (Sset k r z) μS) :
    ∃ cS : ℝ≥0∞, cS ≠ 0 ∧ cS ≠ ⊤ ∧ (μW.prod μN).map mulP = cS • μS := by
  have hSc := s_clsub z hz hT hconj
  obtain ⟨c1, h10, h1t, e1⟩ := haar_unique _ hSc _ (prod_haar z hz hT hconj μW μN hW hN hNc)
  obtain ⟨c2, h20, h2t, e2⟩ := haar_unique _ hSc _ hS
  refine ⟨c1 / c2, (ENNReal.div_pos_iff.mpr ⟨h10, h2t⟩).ne', ENNReal.div_ne_top h1t h20, ?_⟩
  rw [e1, e2, smul_smul, ENNReal.div_mul_cancel h20 h2t]

end WlocSk.HM

namespace WlocSk

theorem sProd_of (hG : SGrp) : SProd := by
  intro k r z c u v b H _ _ _ σ Vp _ _ _ π w μG μS ν μW μN hyp
  obtain ⟨hset, -, -, -, -, hS, -, hW, hN, hWf, hNc⟩ := hyp
  obtain ⟨-, -, hz, hT, -⟩ := hset
  have hconj := (hG k r z c hz hT).2.2.2.2
  exact HM.sprod_main z hz hT (fun h hh m hm => (hconj h hh m hm).1) μW μN μS hW hN hNc hS

theorem product_decomposition_holds : SProd := sProd_of subgroup_hypothesis_holds

end WlocSk
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.AeProductMemUnipotentAndNilradical
noncomputable section

open MeasureTheory Matrix Topology
open scoped InnerProductSpace ENNReal

namespace WlocSk.PtD

open WlocSk Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.L2.SG.WuDecay Formalism.L2.SG.SplitPrimeNormLemmas

variable {k r : ℕ}

def PiCont : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ) (Vp : Type) [NormedAddCommGroup Vp]
    [InnerProductSpace ℂ Vp] (π : Mat k r → (Vp →L[ℂ] Vp)), inWb k r z → 0 < Tz k r z →
    IsHCTypeW k r z u π → ∀ ξ : Vp, ContinuousOn (fun h => π h ξ) (UWset k r z)

theorem ellA_cont (z : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    Continuous (fun g : Mat k r => ellA k r z g a) := by
  unfold ellA
  split_ifs with h
  · exact (continuous_apply _).comp (continuous_apply _)
  · simp only [Matrix.mulVec, dotProduct]
    exact continuous_finsetSum _ fun j _ => (continuous_id.matrix_elem _ j).mul continuous_const

theorem psiGen_cont (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) :
    Continuous (psiGen k r z c) := by
  unfold psiGen
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp (continuous_finsetSum _ fun a _ => continuous_const.mul (ellA_cont z a)))))

theorem inv_contOn : ContinuousOn (fun h : Mat k r => h⁻¹) (Gr k r) := by
  unfold Gr
  have key : ∀ h ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), h⁻¹ = (h.det)⁻¹ • h.adjugate := fun h _ => by
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  refine ContinuousOn.congr ?_ key
  exact ((continuous_id.matrix_det.continuousOn).inv₀
    (fun h hh => (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hh).ne_zero)).smul continuous_id.matrix_adjugate.continuousOn

theorem ae_product_mem_unipotent_and_nilradical {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Mt k r)} [SFinite μW] [SFinite μN]
    (hW : μW {x | Matrix.of x ∉ UWset k r z} = 0) (hN : μN {x | Matrix.of x ∉ Nset k r} = 0)
    (hUWG : UWset k r z ⊆ Gr k r) (hNG : Nset k r ⊆ Gr k r) :
    ∀ᵐ p ∂(μW.prod μN), (Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r) ∧
      (Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.1 * Matrix.of p.2 ∈ Gr k r) := by
  have h1 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z := by
    rw [ae_iff]
    have e : {p : Mt k r × Mt k r | ¬ Matrix.of p.1 ∈ UWset k r z} = {x | Matrix.of x ∉ UWset k r z} ×ˢ Set.univ := by
      ext p
      simp
    rw [e, Measure.prod_prod, hW, zero_mul]
  have h2 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ Nset k r := by
    rw [ae_iff]
    have e : {p : Mt k r × Mt k r | ¬ Matrix.of p.2 ∈ Nset k r} = Set.univ ×ˢ {x | Matrix.of x ∉ Nset k r} := by
      ext p
      simp
    rw [e, Measure.prod_prod, hN, mul_zero]
  filter_upwards [h1, h2] with p hp1 hp2
  exact ⟨⟨hp1, hp2⟩, hp1, Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (hUWG hp1) (hNG hp2)⟩

section Meas

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]
  {σ : Mat k r → (H →L[ℂ] H)} {π : Mat k r → (Vp →L[ℂ] Vp)}

theorem bInt_aesm (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (hσ : IsURepOn (Gr k r) σ)
    {μW μN : Measure (Mt k r)}
    (hUWc : IsClosed (UWset k r z)) (hUWG : UWset k r z ⊆ Gr k r)
    (hUWinv : ∀ h ∈ UWset k r z, h⁻¹ ∈ UWset k r z)
    (hπc : ∀ ξ : Vp, ContinuousOn (fun h => π h ξ) (UWset k r z))
    (hae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.1 * Matrix.of p.2 ∈ Gr k r)
    (w' : H) (ξ : Vp) (v : H) : AEStronglyMeasurable (bInt z c σ π w' ξ v) (μW.prod μN) := by
  set T : Set (Mt k r × Mt k r) :=
    {p | Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.1 * Matrix.of p.2 ∈ Gr k r} with hTdef
  have hfst : Continuous fun p : Mt k r × Mt k r => (Matrix.of p.1 : Mat k r) := continuous_fst
  have hsnd : Continuous fun p : Mt k r × Mt k r => (Matrix.of p.2 : Mat k r) := continuous_snd
  have hmul : Continuous fun p : Mt k r × Mt k r => Matrix.of p.1 * Matrix.of p.2 :=
    hfst.matrix_mul hsnd
  have hTc : IsClosed T := (hUWc.preimage hfst).inter (gr_isClosed.preimage hmul)
  have h1 : ContinuousOn (fun p : Mt k r × Mt k r => σ (Matrix.of p.1 * Matrix.of p.2) v) T :=
    (hσ.2.2 v).comp hmul.continuousOn (fun p hp => hp.2)
  have hi : ContinuousOn (fun p : Mt k r × Mt k r => (Matrix.of p.1)⁻¹) T :=
    inv_contOn.comp hfst.continuousOn (fun p hp => hUWG hp.1)
  have h2 : ContinuousOn (fun p : Mt k r × Mt k r => π (Matrix.of p.1)⁻¹ ξ) T :=
    (hπc ξ).comp hi (fun p hp => hUWinv _ hp.1)
  have h3 : Continuous fun p : Mt k r × Mt k r => star (psiGen k r z c (Matrix.of p.2)) :=
    continuous_star.comp ((psiGen_cont z c).comp hsnd)
  have hcont : ContinuousOn (bInt z c σ π w' ξ v) T :=
    ((continuousOn_const.inner h1).mul h3.continuousOn).smul h2
  have := hcont.aestronglyMeasurable (μ := μW.prod μN) hTc.measurableSet
  have hae' : ∀ᵐ p ∂(μW.prod μN), p ∈ T := hae
  rwa [Measure.restrict_eq_self_of_ae_mem hae'] at this

end Meas

theorem aInt_of (hSG : SigmaG) (hD : Decay) (hRG : ReprodG) (hS : SGrp) (hPi : PiUnit)
    (hNI : NIntDecay) (hU : UWComp) (hPC : PiCont) : AInt := by
  intro k r z c u v b H _ _ _ σ Vp _ _ _ π w μG μS ν μW μN hH hR hC x₀ hx₀ ξ g hg
  obtain ⟨C, _, hCb⟩ := aBound_of hSG hD hRG hS hPi hNI hU k r z c u v b H σ Vp π w μG μS ν μW μN
    hH hR hC x₀ hx₀ ξ
  obtain ⟨hSet, hDS, hHC, _, _, _, _, hμW, hμN, _, _⟩ := hH
  have hz := hSet.2.2.1
  have hT := hSet.2.2.2.1
  have hσ : IsURepOn (Gr k r) σ := hSG k r _ _ H σ hDS
  obtain ⟨hUWG, hNG, hUW, _, _⟩ := hS k r z c hz hT
  have := hμW.1
  have := hμN.1
  have hae := ae_product_mem_unipotent_and_nilradical hμW.2.2.1 hμN.2.2.1 hUWG hNG
  refine ⟨bInt_aesm z c hσ (hU k r z hz hT).isClosed hUWG (fun h hh => (hUW h hh h hh).2.1)
    (hPC k r z u Vp π hz hT hHC) (hae.mono fun p hp => hp.2) _ _ _, ?_⟩
  exact (hCb g hg).trans_lt ENNReal.ofReal_lt_top

theorem aCont_of (hSG : SigmaG) (hD : Decay) (hRG : ReprodG) (hS : SGrp) (hPi : PiUnit)
    (hNI : NIntDecay) (hU : UWComp) (hPC : PiCont) : ACont := by
  intro k r z c u v b H _ _ _ σ Vp _ _ _ π w μG μS ν μW μN hH hR hC x₀ hx₀ ξ g₀ hg₀
  have : FirstCountableTopology (Mat k r) :=
    inferInstanceAs (FirstCountableTopology (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ))
  obtain ⟨Cφ, hCφ0, hCφ⟩ := ptDecay_of hSG hD hRG k r z c u v b H σ Vp π w μG μS ν μW μN hH hR hC x₀ hx₀
  obtain ⟨hSet, hDS, hHC, _, _, _, _, hμW, hμN, hWfin, hNc⟩ := hH
  have hz := hSet.2.2.1
  have hT := hSet.2.2.2.1
  have hσ : IsURepOn (Gr k r) σ := hSG k r _ _ H σ hDS
  obtain ⟨hUWG, hNG, hUW, _, _⟩ := hS k r z c hz hT
  have hPU := (hPi k r z u Vp π hz hT hHC).2
  obtain ⟨Kw, hKw⟩ := (hU k r z hz hT).exists_bound_of_continuousOn
    (opn_continuous (k := k) (r := r)).continuousOn
  have hKw0 : 0 ≤ max Kw 0 := le_max_right _ _
  have hinvb : ∀ h ∈ UWset k r z, opn h⁻¹ ≤ max Kw 0 := fun h hh =>
    le_max_of_le_left ((Real.le_norm_self _).trans (hKw _ (hUW h hh h hh).2.1))
  have := hμW.1
  have := hμN.1
  have hN := nilradical_half_sum_nonneg (k := k) (r := r)
  have hae := ae_product_mem_unipotent_and_nilradical hμW.2.2.1 hμN.2.2.1 hUWG hNG
  have hH2 : 0 ≤ opn (Hpk k r) * opn (Hpk k r) := mul_nonneg (opn_nonneg _) (opn_nonneg _)
  set K0 := Cφ * (max Kw 0 * (opn (Hpk k r) * opn (Hpk k r) * (opn g₀ + 1))) ^ N1H k r * ‖ξ‖
    with hK0d
  have hK0 : 0 ≤ K0 := mul_nonneg (mul_nonneg hCφ0 (Real.rpow_nonneg (mul_nonneg hKw0
    (mul_nonneg hH2 (by linarith [opn_nonneg g₀]))) _)) (norm_nonneg _)
  have hmeas : Measurable fun m : Mt k r => opn (Matrix.of m) ^ (-N1H k r) :=
    (show Continuous fun m : Mt k r => opn (Matrix.of m) from opn_continuous).measurable.pow_const _
  have hgi : Integrable (fun m : Mt k r => opn (Matrix.of m) ^ (-N1H k r)) μN := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun m =>
      Real.rpow_nonneg (opn_nonneg _) _)]
    exact hNI k r μN hμN hNc
  have hbi : Integrable (fun p : Mt k r × Mt k r => K0 * opn (Matrix.of p.2) ^ (-N1H k r))
      (μW.prod μN) := by
    have := (integrable_const (1 : ℝ) (μ := μW)).mul_prod hgi
    simpa using this.const_mul K0
  show ContinuousWithinAt (fun g => ∫ p, bInt z c σ π (σ x₀ w) ξ (σ g w) p ∂(μW.prod μN))
    (Gr k r) g₀
  apply continuousWithinAt_of_dominated
    (bound := fun p : Mt k r × Mt k r => K0 * opn (Matrix.of p.2) ^ (-N1H k r))
  · exact Filter.Eventually.of_forall fun g => bInt_aesm z c hσ (hU k r z hz hT).isClosed hUWG
      (fun h hh => (hUW h hh h hh).2.1) (hPC k r z u Vp π hz hT hHC)
      (hae.mono fun p hp => hp.2) _ _ _
  · have hev1 : ∀ᶠ g in 𝓝[Gr k r] g₀, g ∈ Gr k r := self_mem_nhdsWithin
    have hev2 : ∀ᶠ g in 𝓝[Gr k r] g₀, opn g < opn g₀ + 1 :=
      eventually_nhdsWithin_of_eventually_nhds
        ((opn_continuous (k := k) (r := r)).continuousAt.eventually (gt_mem_nhds (lt_add_one _)))
    filter_upwards [hev1, hev2] with g hg hlt
    filter_upwards [hae] with p hp
    refine (bInt_bound z c hσ (π := π) hCφ hKw0 ξ p (hUWG hp.1.1) (hinvb _ hp.1.1)
      (hPU _ (hUW _ hp.1.1 _ hp.1.1).2.1 ξ) (hNG hp.1.2) hg).trans ?_
    have hle : (max Kw 0 * (opn (Hpk k r) * opn (Hpk k r) * opn g)) ^ N1H k r ≤
        (max Kw 0 * (opn (Hpk k r) * opn (Hpk k r) * (opn g₀ + 1))) ^ N1H k r :=
      Real.rpow_le_rpow (mul_nonneg hKw0 (mul_nonneg hH2 (opn_nonneg _)))
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlt.le hH2) hKw0) hN
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hle hCφ0) (norm_nonneg _)) (Real.rpow_nonneg (opn_nonneg _) _)
  · exact hbi
  · refine Filter.Eventually.of_forall fun p => ?_
    have h1 : ContinuousWithinAt (fun g => σ (Matrix.of p.1 * Matrix.of p.2) (σ g w)) (Gr k r) g₀ :=
      (σ _).continuous.continuousAt.comp_continuousWithinAt (hσ.2.2 w g₀ hg₀)
    exact ((continuousWithinAt_const.inner h1).mul continuousWithinAt_const).smul
      continuousWithinAt_const

end WlocSk.PtD
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.UnipotentRightInvariance
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal

namespace WlocSk.WRI

open Formalism.QuantumDeterminants WlocSk.HM

variable {k r : ℕ}

theorem haar_right_compact {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [T2Space G] [CompactSpace G] (g : G) :
    (Measure.haar : Measure G).map (· * g) = Measure.haar := by
  set μ : Measure G := Measure.haar
  set ν : Measure G := μ.map (· * g)
  have hν : ν = Measure.haarScalarFactor ν μ • μ := Measure.isMulLeftInvariant_eq_smul ν μ
  have hmass : ν Set.univ = μ Set.univ := by
    simp only [ν]
    rw [Measure.map_apply (measurable_mul_const g) MeasurableSet.univ, Set.preimage_univ]
  have h0 : μ Set.univ ≠ 0 := by
    intro h; exact (NeZero.ne μ) (Measure.measure_univ_eq_zero.mp h)
  have htop : μ Set.univ ≠ ∞ := measure_ne_top μ _
  have hc : ((Measure.haarScalarFactor ν μ : ℝ≥0) : ℝ≥0∞) = 1 := by
    have e := hmass
    rw [hν, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at e
    have e2 : ((Measure.haarScalarFactor ν μ : ℝ≥0) : ℝ≥0∞) * μ Set.univ = 1 * μ Set.univ := by
      rw [one_mul]; exact e
    exact (ENNReal.mul_left_inj h0 htop).mp e2
  rw [hν]
  have : Measure.haarScalarFactor ν μ = 1 := by exact_mod_cast hc
  rw [this, one_smul]

theorem hmeas_right (U : Set (Mx k r)) (hU : ClSub U) (hc : IsCompact U) (g : Mx k r) (hg : g ∈ U) :
    (hmeas U hU).map (fun x : Mt k r => fun i j => (Matrix.of x * g) i j) = hmeas U hU := by
  have : CompactSpace (Grp U hU) := isCompact_iff_compactSpace.mp hc
  have hvt : Measurable (Grp.vt : Grp U hU → Mt k r) := (val_cemb U hU).continuous.measurable
  have hR : Measurable (fun x : Mt k r => fun i j => (Matrix.of x * g) i j) := by
    have : Continuous (fun x : Mt k r => fun i j => (Matrix.of x * g) i j) :=
      Continuous.matrix_mul continuous_id continuous_const
    exact this.measurable
  unfold hmeas
  rw [Measure.map_map hR hvt]
  have : (fun x : Mt k r => fun i j => (Matrix.of x * g) i j) ∘ (Grp.vt : Grp U hU → Mt k r) =
      (Grp.vt : Grp U hU → Mt k r) ∘ (fun a => a * Grp.mk g hg) := by
    funext a; rfl
  rw [this, ← Measure.map_map hvt (measurable_mul_const _), haar_right_compact]

end WlocSk.WRI

open WlocSk.HM WlocSk.WRI in
theorem unipotent_right_invariance : WlocSk.WRightInv := by
  intro k r z μW hz hT hH _ h hh
  obtain ⟨c, -, -, hμ⟩ := haar_unique _ (uw_clsub z) μW hH
  have hR : Continuous (fun x : Formalism.QuantumDeterminants.Mt k r =>
      fun i j => (Matrix.of x * h) i j) :=
    Continuous.matrix_mul continuous_id continuous_const
  rw [hμ, Measure.map_smul c hR.measurable.aemeasurable,
    hmeas_right _ _ (compactW z hz hT) h hh]
end
end
