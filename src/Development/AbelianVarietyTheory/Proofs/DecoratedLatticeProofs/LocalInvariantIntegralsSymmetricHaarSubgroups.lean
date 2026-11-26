module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumOfRankOneGram
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMulLeftInvariantMapLevyProductMapToFourierJaco
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricDoubleIntegralFiniteCombination

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevyProductMapHaarIsMulLeftInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevyProductMapHaarIsMulLeftInvariant
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace
open GlobalTheory.HaarR

theorem GlobalTheory.HaarR.map_prodR_isMulLeftInvariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ), 1 ≤ p → p ≤ c → ∀ (ν : Measure k), ν.IsAddHaarMeasure → ∀ m : Measure (GL n k), m.IsHaarMeasure → ((m.prod (volN ν n c p)).map (prodR p)).IsMulLeftInvariant := by
  intro k _ _ _ _ _ _ n _ _ c p h1 hp ν hν m hm
  haveI := hν
  haveI := hm
  haveI : BorelSpace (GL n k) := GlobalTheory.SplitFlip.borel_GL
  haveI : BorelSpace (GL (n ⊕ Fin c) k) := GlobalTheory.SplitFlip.borel_GL
  obtain ⟨hNc, -, hH, -, -⟩ := GlobalTheory.RootEx.VolN.volN_haar_and_modulus k n c p h1 hp ν
  haveI := hH
  haveI : LocallyCompactSpace (N k n c p) := hNc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (N k n c p) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SigmaFinite m := inferInstance
  haveI : SigmaFinite (volN ν n c p) := inferInstance
  have hE : Continuous (embX c : GL n k → GL (n ⊕ Fin c) k) := GlobalTheory.RootEx.QuotStep.continuous_embX
  have hφ : Measurable (prodR (k := k) (n := n) (c := c) p) :=
    (Continuous.subtype_mk ((hE.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)) _).measurable
  have hmulJ : ∀ g : R k n c p, Measurable (fun y : R k n c p => g * y) :=
    fun g => (continuous_const_mul g).measurable
  have hmulH : ∀ g : GL n k, Measurable (fun y : GL n k => g * y) := fun g => (continuous_const_mul g).measurable
  let μR : Measure (R k n c p) := (m.prod (volN ν n c p)).map (prodR p)
  let K : Subgroup (GL (n ⊕ Fin c) k) :=
    { carrier := {x | ∃ hx : x ∈ R k n c p,
        μR.map (fun y => (⟨x, hx⟩ : R k n c p) * y) = μR}
      one_mem' := ⟨one_mem _, by
        simp only [show (⟨1, one_mem _⟩ : R k n c p) = 1 from rfl, one_mul]
        exact Measure.map_id'⟩
      mul_mem' := by
        rintro a b ⟨ha, Ha⟩ ⟨hb, Hb⟩
        refine ⟨mul_mem ha hb, ?_⟩
        have : (fun y : R k n c p => (⟨a * b, mul_mem ha hb⟩ : R k n c p) * y)
            = (fun y => (⟨a, ha⟩ : R k n c p) * y) ∘ (fun y => (⟨b, hb⟩ : R k n c p) * y) :=
          funext fun y => mul_assoc (⟨a, ha⟩ : R k n c p) ⟨b, hb⟩ y
        rw [this, ← Measure.map_map (hmulJ _) (hmulJ _), Hb, Ha]
      inv_mem' := by
        rintro a ⟨ha, Ha⟩
        refine ⟨inv_mem ha, ?_⟩
        conv_lhs => rw [← Ha]
        rw [Measure.map_map (hmulJ _) (hmulJ _)]
        have : (fun y : R k n c p => (⟨a⁻¹, inv_mem ha⟩ : R k n c p) * y) ∘
            (fun y => (⟨a, ha⟩ : R k n c p) * y) = id :=
          funext fun y => inv_mul_cancel_left (⟨a, ha⟩ : R k n c p) y
        rw [this, Measure.map_id] }
  have hXK : (embX c : GL n k →* GL (n ⊕ Fin c) k).range ≤ K := by
    rintro _ ⟨g₀, rfl⟩
    refine ⟨Subgroup.mem_sup_left ⟨g₀, rfl⟩, ?_⟩
    show Measure.map _ (Measure.map _ _) = _
    rw [Measure.map_map (hmulJ _) hφ]
    have : (fun y : R k n c p => (⟨embX c g₀, Subgroup.mem_sup_left ⟨g₀, rfl⟩⟩ : R k n c p) * y) ∘ prodR p
        = prodR p ∘ Prod.map (fun y : GL n k => g₀ * y) id := by
      funext q; apply Subtype.ext; simp [mul_assoc]
    rw [this, ← Measure.map_map hφ ((hmulH _).prodMap measurable_id),
      ← Measure.map_prod_map m (volN ν n c p) (hmulH _) measurable_id, map_mul_left_eq_self, Measure.map_id]
  have hNK : N k n c p ≤ K := by
    intro u₀ hu₀
    refine ⟨Subgroup.mem_sup_right hu₀, ?_⟩
    show Measure.map _ (Measure.map _ _) = _
    rw [Measure.map_map (hmulJ _) hφ]
    let cg : GL n k → N k n c p := fun g => ⟨(embX c g)⁻¹ * u₀ * embX c g, GlobalTheory.RootEx.Model.conj_mem hu₀ g⟩
    have hcg : Continuous cg :=
      Continuous.subtype_mk (((hE.inv).mul continuous_const).mul hE) _
    let F : GL n k → N k n c p → N k n c p := fun g u => cg g * u
    have hF : Measurable (Function.uncurry F) :=
      (((hcg.comp continuous_fst).mul continuous_snd)).measurable
    have hFm : ∀ g, Measure.map (F g) (volN ν n c p) = volN ν n c p := fun g => map_mul_left_eq_self _ _
    have hmp := (MeasurePreserving.id m).skew_product hF (Filter.Eventually.of_forall hFm)
    have : (fun y : R k n c p => (⟨u₀, Subgroup.mem_sup_right hu₀⟩ : R k n c p) * y) ∘ prodR p
        = prodR p ∘ (fun q : GL n k × N k n c p => (id q.1, F q.1 q.2)) := by
      funext q; apply Subtype.ext; simp [F, cg, mul_assoc]
    rw [this, ← Measure.map_map hφ hmp.measurable, hmp.map_eq]
  refine ⟨fun g => ?_⟩
  obtain ⟨hx, H⟩ := (sup_le hXK hNK) g.2
  exact H
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevyProductMapHaarIsMulLeftInvariantStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace
open GlobalTheory.HaarR

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levyProductMap_haar_isMulLeftInvariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ), 1 ≤ p → p ≤ c → ∀ (ν : Measure k), ν.IsAddHaarMeasure → ∀ m : Measure (GL n k), m.IsHaarMeasure → ((m.prod (volN ν n c p)).map (prodR p)).IsMulLeftInvariant := by
  first | exact @GlobalTheory.HaarR.map_prodR_isMulLeftInvariant | exact GlobalTheory.HaarR.map_prodR_isMulLeftInvariant | (intros; apply GlobalTheory.HaarR.map_prodR_isMulLeftInvariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevyProductMapToFourierJacobiPreimageIntegralGL
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevyProductMapToFourierJacobiPreimageIntegralGL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace
open GlobalTheory.HaarR

noncomputable section
namespace GlobalTheory.HaarFJInt

open GlobalTheory.RootEx.Radical

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

def midLev (c ρ : ℕ) : n ⊕ Fin c → ℕ := Sum.elim (fun _ => 2 * ρ + 1) (fun i => 2 * (i.val + 1))

theorem uni_of_mem_N {ρ : ℕ} {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c (ρ + 1)) :
    Uni (midLev c ρ) u.val := by
  rw [mem_N_iff] at hu
  intro r s hrs
  refine hu r s ?_
  rcases r with r | r <;> rcases s with s | s <;> simp only [midLev, lev, Sum.elim_inl, Sum.elim_inr] at hrs ⊢ <;> omega

theorem uni_colE (ρ : ℕ) (β : n → k) : Uni (midLev c ρ) (colE c (ρ + 1) β).val := by
  intro r s hrs
  rcases r with r | r <;> rcases s with s | s
  · simp [colE, upU, Matrix.one_apply]
  · simp only [midLev, Sum.elim_inl, Sum.elim_inr] at hrs
    have : s.val ≠ ρ := by omega
    simp [colE, upU, this]
  · simp [colE, upU]
  · simp [colE, upU, Matrix.one_apply]

theorem uni_inl_inl {ρ : ℕ} {M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k} (h : Uni (midLev c ρ) M) (i j : n) :
    M (Sum.inl i) (Sum.inl j) = (1 : Matrix n n k) i j := by
  rw [h _ _ (by simp [midLev])]
  simp [Matrix.one_apply]

theorem embX_mem_KO {g : GL n k} (hg : g ∈ KO k n) : embX c g ∈ KO k (n ⊕ Fin c) := by
  rw [GlobalTheory.SplitFlip.mem_KO_iff] at hg ⊢
  have one_int : ∀ (i j : Fin c), (1 : Matrix (Fin c) (Fin c) k) i j ∈ 𝒪[k] := fun i j => by
    rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [embX_val]
    rcases i with i | i <;> rcases j with j | j
    · exact hg.1 i j
    · exact zero_mem _
    · exact zero_mem _
    · exact one_int i j
  · rw [← map_inv, embX_val]
    rcases i with i | i <;> rcases j with j | j
    · exact hg.2 i j
    · exact zero_mem _
    · exact zero_mem _
    · exact one_int i j

theorem colE_mem_KO (p : ℕ) {β : n → k} (hβ : ∀ i, β i ∈ 𝒪[k]) : colE c p β ∈ KO k (n ⊕ Fin c) := by
  rw [GlobalTheory.SplitFlip.mem_KO_iff]
  have one_int : ∀ {m : Type} [DecidableEq m] (i j : m), (1 : Matrix m m k) i j ∈ 𝒪[k] := fun i j => by
    rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rcases i with i | i <;> rcases j with j | j
    · exact one_int i j
    · simp only [colE, upU, fromBlocks_apply₁₂, Matrix.of_apply]
      split_ifs
      · exact hβ i
      · exact zero_mem _
    · simp only [colE, upU, fromBlocks_apply₂₁, Matrix.zero_apply]; exact zero_mem _
    · exact one_int i j
  · rcases i with i | i <;> rcases j with j | j
    · exact one_int i j
    · show (fromBlocks 1 (-(Matrix.of fun r (i : Fin c) => if i.val + 1 = p then β r else 0)) 0 1 :
        Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inl i) (Sum.inr j) ∈ 𝒪[k]
      simp only [fromBlocks_apply₁₂, Matrix.neg_apply, Matrix.of_apply]
      split_ifs
      · exact neg_mem (hβ i)
      · rw [neg_zero]; exact zero_mem _
    · show (fromBlocks 1 (-(Matrix.of fun r (i : Fin c) => if i.val + 1 = p then β r else 0)) 0 1 :
        Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inr i) (Sum.inl j) ∈ 𝒪[k]
      simp only [fromBlocks_apply₂₁, Matrix.zero_apply]; exact zero_mem _
    · show (fromBlocks 1 (-(Matrix.of fun r (i : Fin c) => if i.val + 1 = p then β r else 0)) 0 1 :
        Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inr i) (Sum.inr j) ∈ 𝒪[k]
      simp only [fromBlocks_apply₂₂]; exact one_int i j

theorem embX_mul_inl {ρ : ℕ} (g : GL n k) (w : GL (n ⊕ Fin c) k) (hw : Uni (midLev c ρ) w.val) (i j : n) :
    (embX c g * w).val (Sum.inl i) (Sum.inl j) = g.val i j := by
  rw [Units.val_mul, embX_val, Matrix.mul_apply, Fintype.sum_sum_type]
  simp [uni_inl_inl hw, Matrix.one_apply]

theorem mul_embX_inl {ρ : ℕ} (g : GL n k) (w : GL (n ⊕ Fin c) k) (hw : Uni (midLev c ρ) w.val) (i j : n) :
    (w * embX c g).val (Sum.inl i) (Sum.inl j) = g.val i j := by
  rw [Units.val_mul, embX_val, Matrix.mul_apply, Fintype.sum_sum_type]
  simp [uni_inl_inl hw, Matrix.one_apply]

theorem col_eq {ρ : ℕ} (hρ : ρ < c) (u : GL (n ⊕ Fin c) k) (hu : u ∈ N k n c (ρ + 1)) (β : n → k) (t : n) :
    (u * colE c (ρ + 1) β).val (Sum.inl t) (Sum.inr ⟨ρ, hρ⟩) = β t := by
  have h1 := uni_inl_inl (uni_of_mem_N hu)
  have h0 : u.val (Sum.inl t) (Sum.inr ⟨ρ, hρ⟩) = 0 := by
    rw [mem_N_iff] at hu
    rw [hu _ _ (by simp [lev])]
    simp
  rw [Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type]
  simp [colE, upU, h1, Matrix.one_apply, h0]

theorem mem_KO_iff_prod {ρ : ℕ} (hρ : ρ < c) (g : GL n k) (u : GL (n ⊕ Fin c) k) (hu : u ∈ N k n c (ρ + 1))
    (β : n → k) :
    embX c g * u * colE c (ρ + 1) β ∈ KO k (n ⊕ Fin c) ↔
      g ∈ KO k n ∧ u ∈ KO k (n ⊕ Fin c) ∧ ∀ i, β i ∈ 𝒪[k] := by
  constructor
  · intro hr
    have hw : Uni (midLev c ρ) (u * colE c (ρ + 1) β).val :=
      Uni.mul (uni_of_mem_N hu) (uni_colE ρ β)
    have hwi : Uni (midLev c ρ) ((u * colE c (ρ + 1) β)⁻¹).val := Uni.inv hw
    have hr' := (GlobalTheory.SplitFlip.mem_KO_iff _).1 hr
    have hg : g ∈ KO k n := by
      rw [GlobalTheory.SplitFlip.mem_KO_iff]
      refine ⟨fun i j => ?_, fun i j => ?_⟩
      · have := hr'.1 (Sum.inl i) (Sum.inl j)
        rwa [mul_assoc, embX_mul_inl g _ hw] at this
      · have := hr'.2 (Sum.inl i) (Sum.inl j)
        rwa [mul_assoc, _root_.mul_inv_rev, ← map_inv, mul_embX_inl g⁻¹ _ hwi] at this
    have hwK : u * colE c (ρ + 1) β ∈ KO k (n ⊕ Fin c) := by
      have := mul_mem (inv_mem (embX_mem_KO (c := c) hg)) hr
      rwa [mul_assoc, inv_mul_cancel_left] at this
    have hβ : ∀ i, β i ∈ 𝒪[k] := fun i => by
      have := ((GlobalTheory.SplitFlip.mem_KO_iff _).1 hwK).1 (Sum.inl i) (Sum.inr ⟨ρ, hρ⟩)
      rwa [col_eq hρ u hu β i] at this
    refine ⟨hg, ?_, hβ⟩
    have := mul_mem hwK (inv_mem (colE_mem_KO (c := c) (ρ + 1) hβ))
    rwa [mul_inv_cancel_right] at this
  · rintro ⟨hg, huK, hβ⟩
    exact mul_mem (mul_mem (embX_mem_KO hg) huK) (colE_mem_KO _ hβ)

end GlobalTheory.HaarFJInt

open GlobalTheory.HaarFJInt in
theorem GlobalTheory.HaarFJInt.prodRFJ_preimage_KO : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ), ρ < c → prodRFJ (k := k) (n := n) (c := c) ρ ⁻¹' {x | (x : GL (n ⊕ Fin c) k) ∈ KO k (n ⊕ Fin c)} = ((KO k n : Set (GL n k)) ×ˢ {u : N k n c (ρ + 1) | (u : GL (n ⊕ Fin c) k) ∈ KO k (n ⊕ Fin c)}) ×ˢ {β : n → k | ∀ i, β i ∈ 𝒪[k]} := by
  intro k _ _ _ _ n _ _ c ρ hρ
  ext ⟨⟨g, u⟩, β⟩
  simp only [Set.mem_preimage, Set.mem_setOf_eq, prodRFJ_coe, Set.mem_prod, SetLike.mem_coe]
  rw [mem_KO_iff_prod hρ g u u.2 β, and_assoc]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevyProductMapToFourierJacobiPreimageIntegralGLStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace
open GlobalTheory.HaarR

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levyProductMapToFourierJacobi_preimage_integralGL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ), ρ < c → prodRFJ (k := k) (n := n) (c := c) ρ ⁻¹' {x | (x : GL (n ⊕ Fin c) k) ∈ KO k (n ⊕ Fin c)} = ((KO k n : Set (GL n k)) ×ˢ {u : N k n c (ρ + 1) | (u : GL (n ⊕ Fin c) k) ∈ KO k (n ⊕ Fin c)}) ×ˢ {β : n → k | ∀ i, β i ∈ 𝒪[k]} := by
  first | exact @GlobalTheory.HaarFJInt.prodRFJ_preimage_KO | exact GlobalTheory.HaarFJInt.prodRFJ_preimage_KO | (intros; apply GlobalTheory.HaarFJInt.prodRFJ_preimage_KO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevyProductMapHaarFiniteOnCompacts
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevyProductMapHaarFiniteOnCompacts
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace
open GlobalTheory.HaarR

noncomputable section
namespace GlobalTheory.HaarR
namespace RDecomp

section
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}

theorem blocks_of_mem_R {r : GL (n ⊕ Fin c) k} (hr : r ∈ R k n c p) :
    ∃ x : GL n k, r.val.toBlocks₁₁ = x.val ∧ (r⁻¹).val.toBlocks₁₁ = (x⁻¹).val := by
  obtain ⟨x, u, hu, rfl⟩ := GlobalTheory.RootEx.Radical.exists_of_mem_R hr
  refine ⟨x, GlobalTheory.RootEx.Radical.toBlocks₁₁_embX_mul x hu, ?_⟩
  have e : (embX c x * u)⁻¹ = embX c x⁻¹ * (embX c x * u⁻¹ * (embX c x)⁻¹) := by
    rw [map_inv]; group
  rw [e]
  exact GlobalTheory.RootEx.Radical.toBlocks₁₁_embX_mul x⁻¹ (GlobalTheory.RootEx.Radical.conj_mem x (inv_mem hu))

def gpart (r : R k n c p) : GL n k :=
  ⟨(r : GL (n ⊕ Fin c) k).val.toBlocks₁₁, ((r : GL (n ⊕ Fin c) k)⁻¹).val.toBlocks₁₁,
    by obtain ⟨x, h1, h2⟩ := blocks_of_mem_R r.2; rw [h1, h2, Units.mul_inv],
    by obtain ⟨x, h1, h2⟩ := blocks_of_mem_R r.2; rw [h1, h2, Units.inv_mul]⟩

theorem gpart_prodR (q : GL n k × N k n c p) : gpart (prodR p q) = q.1 :=
  Units.ext (GlobalTheory.RootEx.Radical.toBlocks₁₁_embX_mul q.1 q.2.2)

theorem mem_N_of_mem_R (r : R k n c p) : (embX c (gpart r))⁻¹ * (r : GL (n ⊕ Fin c) k) ∈ N k n c p := by
  obtain ⟨x, u, hu, e⟩ := GlobalTheory.RootEx.Radical.exists_of_mem_R r.2
  have : gpart r = x := Units.ext (by
    change (r : GL (n ⊕ Fin c) k).val.toBlocks₁₁ = _
    rw [e]; exact GlobalTheory.RootEx.Radical.toBlocks₁₁_embX_mul x hu)
  rw [this, e, inv_mul_cancel_left]
  exact hu

def upart (r : R k n c p) : N k n c p := ⟨(embX c (gpart r))⁻¹ * (r : GL (n ⊕ Fin c) k), mem_N_of_mem_R r⟩

end

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem continuous_gpart (p : ℕ) : Continuous (gpart (k := k) (n := n) (c := c) (p := p)) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (GlobalTheory.RootEx.VolN.continuous_entry (Sum.inl i) (Sum.inl j)).comp continuous_subtype_val
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (GlobalTheory.RootEx.VolN.continuous_entry (Sum.inl i) (Sum.inl j)).comp (continuous_subtype_val.inv)

def prodRHomeo (p : ℕ) : GL n k × N k n c p ≃ₜ R k n c p where
  toFun := prodR p
  invFun r := (gpart r, upart r)
  left_inv q := by
    have h := gpart_prodR (c := c) q
    refine Prod.ext h (Subtype.ext ?_)
    change (embX c (gpart (prodR p q)))⁻¹ * (embX c q.1 * (q.2 : GL (n ⊕ Fin c) k)) = _
    rw [h, inv_mul_cancel_left]
  right_inv r := Subtype.ext (by
    change embX c (gpart r) * ((embX c (gpart r))⁻¹ * (r : GL (n ⊕ Fin c) k)) = _
    rw [mul_inv_cancel_left])
  continuous_toFun := Continuous.subtype_mk
    ((GlobalTheory.RootEx.QuotStep.continuous_embX.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)) _
  continuous_invFun := (continuous_gpart p).prodMk (Continuous.subtype_mk
    ((GlobalTheory.RootEx.QuotStep.continuous_embX.comp (continuous_gpart p)).inv.mul continuous_subtype_val) _)

end

end RDecomp
open RDecomp

theorem finite_r : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ), 1 ≤ p → p ≤ c → ∀ (ν : Measure k), ν.IsAddHaarMeasure → ∀ m : Measure (GL n k), m.IsHaarMeasure → IsFiniteMeasureOnCompacts ((m.prod (volN ν n c p)).map (prodR p)) := by
  intro k _ _ _ _ _ _ n _ _ c p _ _ ν hν m hm
  haveI := hν
  haveI := hm
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  haveI : BorelSpace (GL n k) := GlobalTheory.SplitFlip.borel_GL
  haveI : BorelSpace (GL (n ⊕ Fin c) k) := GlobalTheory.SplitFlip.borel_GL
  haveI : SecondCountableTopology (GL n k) := GlobalTheory.SplitFlip.secondCountable_GL
  haveI : SecondCountableTopology (GL (n ⊕ Fin c) k) := GlobalTheory.SplitFlip.secondCountable_GL
  haveI : LocallyCompactSpace (GL (n ⊕ Fin c) k) := GlobalTheory.SplitFlip.locallyCompact_GL
  haveI : (volN ν n c p).IsHaarMeasure := GlobalTheory.RootEx.VolN.isHaarMeasure_volN ν p
  haveI : LocallyCompactSpace (N k n c p) := (GlobalTheory.RootEx.VolN.isClosed_N p).locallyCompactSpace
  haveI : SecondCountableTopology (N k n c p) := TopologicalSpace.Subtype.secondCountableTopology _
  have e : ⇑(prodRHomeo (k := k) (n := n) (c := c) p) = prodR p := rfl
  rw [← e]
  exact Measure.IsFiniteMeasureOnCompacts.map _ (prodRHomeo p)

end GlobalTheory.HaarR
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevyProductMapHaarFiniteOnCompactsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace
open GlobalTheory.HaarR

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levyProductMap_haar_finiteOnCompacts : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ), 1 ≤ p → p ≤ c → ∀ (ν : Measure k), ν.IsAddHaarMeasure → ∀ m : Measure (GL n k), m.IsHaarMeasure → IsFiniteMeasureOnCompacts ((m.prod (volN ν n c p)).map (prodR p)) := by
  first | exact @GlobalTheory.HaarR.finite_r | exact GlobalTheory.HaarR.finite_r | (intros; apply GlobalTheory.HaarR.finite_r <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiProductMapHaarFiniteOnCompacts
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiProductMapHaarFiniteOnCompacts
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace
open GlobalTheory.HaarR

noncomputable section
namespace GlobalTheory.HaarR

theorem finite_on_compacts_prodRFJ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ), 1 ≤ ρ → ρ < c → ∀ (ν : Measure k), ν.IsAddHaarMeasure → ∀ m : Measure (GL n k), m.IsHaarMeasure → IsFiniteMeasureOnCompacts (((m.prod (volN ν n c (ρ + 1))).prod (Measure.pi fun _ : n => ν)).map (prodRFJ ρ)) := by
  intro k _ _ _ _ _ _ n _ _ c ρ hp hpc ν hν m hm
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  haveI : BorelSpace (GL (n ⊕ Fin c) k) := GlobalTheory.SplitFlip.borel_GL
  haveI := QuotLinear.finiteOnCompacts_volN (n := n) (c := c) (p := ρ + 1) ν
  haveI : LocallyCompactSpace (N k n c (ρ + 1)) :=
    (QuotLinear.isClosed_N (k := k) (n := n) (c := c) (p := ρ + 1)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (N k n c (ρ + 1)) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : IsLocallyFiniteMeasure (volN ν n c (ρ + 1)) := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  haveI : SigmaFinite (volN ν n c (ρ + 1)) := sigmaFinite_of_locallyFinite
  haveI : IsLocallyFiniteMeasure ν := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  haveI : SigmaFinite ν := sigmaFinite_of_locallyFinite
  set M := (m.prod (volN ν n c (ρ + 1))).prod (Measure.pi fun _ : n => ν) with hM
  haveI : IsFiniteMeasureOnCompacts M := by rw [hM]; infer_instance
  refine ⟨fun K hK => ?_⟩
  obtain ⟨D, hD, hD'⟩ := GlobalTheory.RootEx.ProperTriple.proper_triple k n c ρ hp hpc _ (hK.image continuous_subtype_val)
  have hD2 : IsCompact ((fun w : GL n k × N k n c (ρ + 1) × (n → k) => ((w.1, w.2.1), w.2.2)) '' D) :=
    hD.image (by fun_prop)
  have hsub : prodRFJ ρ ⁻¹' K ⊆ (fun w : GL n k × N k n c (ρ + 1) × (n → k) => ((w.1, w.2.1), w.2.2)) '' D := by
    intro z hz
    exact ⟨(z.1.1, z.1.2, z.2), hD' _ ⟨_, hz, rfl⟩, rfl⟩
  by_cases hf : AEMeasurable (prodRFJ (k := k) (n := n) (c := c) ρ) M
  · rw [Measure.map_apply_of_aemeasurable hf hK.isClosed.measurableSet]
    exact (measure_mono hsub).trans_lt hD2.measure_lt_top
  · by_cases hzero : M = 0
    · simp [hzero]
    · rw [Measure.map_of_not_aemeasurable_of_ne_zero hf hzero]
      exact measure_lt_top _ _

end GlobalTheory.HaarR
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiProductMapHaarFiniteOnCompactsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace
open GlobalTheory.HaarR

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobiProductMap_haar_finiteOnCompacts : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ), 1 ≤ ρ → ρ < c → ∀ (ν : Measure k), ν.IsAddHaarMeasure → ∀ m : Measure (GL n k), m.IsHaarMeasure → IsFiniteMeasureOnCompacts (((m.prod (volN ν n c (ρ + 1))).prod (Measure.pi fun _ : n => ν)).map (prodRFJ ρ)) := by
  first | exact @GlobalTheory.HaarR.finite_on_compacts_prodRFJ | exact GlobalTheory.HaarR.finite_on_compacts_prodRFJ | (intros; apply GlobalTheory.HaarR.finite_on_compacts_prodRFJ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevyProductMapPreimageIntegralGL
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevyProductMapPreimageIntegralGL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace
open GlobalTheory.HaarR

namespace GlobalTheory.HaarR

theorem rootExchangeEmbedGL_mem_integralGL {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] [DecidableEq n] (c : ℕ) {g : GL n k} (hg : g ∈ KO k n) :
    embX c g ∈ KO k (n ⊕ Fin c) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SplitFlip.mem_KO_iff g).1 hg
  have key : ∀ x : GL n k, (∀ i j, x.val i j ∈ 𝒪[k]) → ∀ i j, (embX c x).val i j ∈ 𝒪[k] := by
    intro x hx i j
    rw [GlobalTheory.RootEx.Radical.embX_val]
    rcases i with i | i <;> rcases j with j | j
    · simpa using hx i j
    · simp
    · simp
    · simp only [fromBlocks_apply₂₂, Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
  refine (GlobalTheory.SplitFlip.mem_KO_iff _).2 ⟨key g h1, ?_⟩
  rw [← map_inv]
  exact key _ h2

theorem prodR_preimage_KO : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ), prodR (k := k) (n := n) (c := c) p ⁻¹' {x | (x : GL (n ⊕ Fin c) k) ∈ KO k (n ⊕ Fin c)} = (KO k n : Set (GL n k)) ×ˢ {u : N k n c p | (u : GL (n ⊕ Fin c) k) ∈ KO k (n ⊕ Fin c)} := by
  intro k _ _ _ _ n _ _ c p
  ext ⟨g, u⟩
  simp only [Set.mem_preimage, Set.mem_setOf_eq, prodR_coe, Set.mem_prod, SetLike.mem_coe]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := (GlobalTheory.SplitFlip.mem_KO_iff _).1 h
    have hg : g ∈ KO k n := by
      refine (GlobalTheory.SplitFlip.mem_KO_iff g).2 ⟨fun i j => ?_, fun i j => ?_⟩
      · have e := GlobalTheory.RootEx.Radical.toBlocks₁₁_embX_mul (c := c) g u.2
        have := h1 (Sum.inl i) (Sum.inl j)
        rw [← e]; exact this
      · have hu' : embX c g * ((u : GL (n ⊕ Fin c) k))⁻¹ * (embX c g)⁻¹ ∈ N k n c p :=
          GlobalTheory.RootEx.Radical.conj_mem g (inv_mem u.2)
        have e := GlobalTheory.RootEx.Radical.toBlocks₁₁_embX_mul (c := c) g⁻¹ hu'
        have hinv : (embX c g * (u : GL (n ⊕ Fin c) k))⁻¹
            = embX c g⁻¹ * (embX c g * ((u : GL (n ⊕ Fin c) k))⁻¹ * (embX c g)⁻¹) := by
          rw [map_inv]; group
        have := h2 (Sum.inl i) (Sum.inl j)
        rw [hinv] at this
        rw [← e]
        exact this
    refine ⟨hg, ?_⟩
    have := mul_mem (inv_mem (rootExchangeEmbedGL_mem_integralGL c hg)) h
    rwa [inv_mul_cancel_left] at this
  · rintro ⟨hg, hu⟩
    exact mul_mem (rootExchangeEmbedGL_mem_integralGL c hg) hu

end GlobalTheory.HaarR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevyProductMapPreimageIntegralGLStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace
open GlobalTheory.HaarR

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levyProductMap_preimage_integralGL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ), prodR (k := k) (n := n) (c := c) p ⁻¹' {x | (x : GL (n ⊕ Fin c) k) ∈ KO k (n ⊕ Fin c)} = (KO k n : Set (GL n k)) ×ˢ {u : N k n c p | (u : GL (n ⊕ Fin c) k) ∈ KO k (n ⊕ Fin c)} := by
  first | exact @GlobalTheory.HaarR.prodR_preimage_KO | exact GlobalTheory.HaarR.prodR_preimage_KO | (intros; apply GlobalTheory.HaarR.prodR_preimage_KO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalInvariantIntegralsSymmetricHaarSubgroups
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace

namespace GlobalTheory.HaarR
open scoped ENNReal NNReal

theorem eq_of_mass_one {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G] (κ μ : Measure G) [μ.IsHaarMeasure]
    [IsFiniteMeasureOnCompacts κ] [κ.IsMulLeftInvariant] (S : Set G) (hS : μ S = 1) (hκ : κ S = 1) : κ = μ := by
  have h := Measure.isMulLeftInvariant_eq_smul κ μ
  set a := Measure.haarScalarFactor κ μ
  have h1 : (a : ℝ≥0∞) = 1 := by
    rw [h, Measure.smul_apply, hS, ENNReal.smul_def, smul_eq_mul, mul_one] at hκ
    exact hκ
  have : a = 1 := by exact_mod_cast h1
  rw [h, this, one_smul]

theorem quot_int_haar : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (m : Measure (GL n k)) (G : Measure (GL (n ⊕ Fin c) k)), m.IsHaarMeasure → G.IsHaarMeasure → m (KO k n) = 1 → (c + 1 = 2 * ρ → ∀ μR : Measure (R k n c ρ), μR.IsHaarMeasure → μR {x | x.1 ∈ KO k (n ⊕ Fin c)} = 1 → μR.IsInvInvariant ∧ ∀ f z, IsQuotInt ν m G ρ f z → IsQuotIntL1 μR G f z) ∧ (1 ≤ ρ → c = 2 * ρ → ∀ μR : Measure (RFJ k n c ρ), μR.IsHaarMeasure → μR {x | x.1 ∈ KO k (n ⊕ Fin c)} = 1 → μR.IsInvInvariant ∧ ∀ f z, IsQuotIntFJ ν m G ρ f z → IsQuotIntL1 μR G f z) := by
  intro k _ _ _ _ _ _ ν hν n _ _ c ρ m G hm hG hmK
  haveI := hν.1
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  haveI : BorelSpace (GL n k) := GlobalTheory.SplitFlip.borel_GL
  haveI : BorelSpace (GL (n ⊕ Fin c) k) := GlobalTheory.SplitFlip.borel_GL
  have hKO : ∀ (S : Subgroup (GL (n ⊕ Fin c) k)), MeasurableSet {x : S | (x : GL (n ⊕ Fin c) k) ∈ KO k (n ⊕ Fin c)} :=
    fun S => (GlobalTheory.SplitFlip.isOpen_KO.preimage continuous_subtype_val).measurableSet
  have hFint : ∀ F ∈ SB (GL (n ⊕ Fin c) k), Integrable F G := fun F hF => hF.1.continuous.integrable_of_hasCompactSupport hF.2
  have hFS : ∀ (S : Subgroup (GL (n ⊕ Fin c) k)), IsClosed (S : Set (GL (n ⊕ Fin c) k)) → ∀ (μS : Measure S),
      μS.IsHaarMeasure → ∀ F ∈ SB (GL (n ⊕ Fin c) k), ∀ h, Integrable (fun r : S => F (r * h)) μS := by
    intro S hS μS _ F hF h
    exact (hF.1.continuous.comp (continuous_subtype_val.mul continuous_const)).integrable_of_hasCompactSupport
      ((hF.2.comp_homeomorph (Homeomorph.mulRight h)).comp_isClosedEmbedding hS.isClosedEmbedding_subtypeVal)
  refine ⟨fun hc μR hR hRK => ?_, fun h1 hc μR hR hRK => ?_⟩
  · have h1 : 1 ≤ ρ := by omega
    have h2 : ρ ≤ c := by omega
    obtain ⟨hNc, hcl, hNH, -, -⟩ := GlobalTheory.RootEx.VolN.volN_haar_and_modulus k n c ρ h1 h2 ν
    haveI : LocallyCompactSpace (N k n c ρ) := hNc.locallyCompactSpace
    haveI := hNH
    haveI : LocallyCompactSpace (R k n c ρ) := hcl.locallyCompactSpace
    haveI := hR
    haveI := hm
    haveI := GlobalTheory.T.levyProductMap_haar_isMulLeftInvariant k n c ρ h1 h2 ν hν.1 m hm
    haveI := GlobalTheory.T.levyProductMap_haar_finiteOnCompacts k n c ρ h1 h2 ν hν.1 m hm
    have hmeas : Measurable (prodR (k := k) (n := n) (c := c) ρ) :=
      (Continuous.subtype_mk ((GlobalTheory.RootEx.QuotStep.continuous_embX.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd)) _).measurable
    have hκ : (m.prod (volN ν n c ρ)).map (prodR ρ) = μR := by
      refine eq_of_mass_one _ μR _ hRK ((Measure.map_apply hmeas (hKO (R k n c ρ))).trans ?_)
      rw [GlobalTheory.T.levyProductMap_preimage_integralGL, Measure.prod_prod, hmK, GlobalTheory.T.rootExchangeUnipotentHaar_integralPoints_eq_one k n c ρ h1 h2 ν hν, one_mul]
    haveI : μR.IsMulRightInvariant := GlobalTheory.LevelUnimod.unimodular k n c ρ (fun i => i.val + 1)
      (fun i => by simp [Fin.rev]; omega) (R k n c ρ)
      (GlobalTheory.RootEx.ParabolicEntries.mem_R_iff_and_mem_RFJ_iff k n c ρ).1 μR hR
    refine ⟨GlobalTheory.SemiHaar.invInv_of_rightInv μR, ?_⟩
    rintro f z ⟨F, hF, hf, hz⟩
    have hi := hFS _ hcl μR hR F hF
    refine ⟨F, hFint F hF, hi, fun h => ?_, hz⟩
    have hc' : Continuous fun r : R k n c ρ => F (r * h) :=
      hF.1.continuous.comp (continuous_subtype_val.mul continuous_const)
    have hp : Integrable (fun q => F ((prodR (k := k) (n := n) (c := c) ρ q : GL (n ⊕ Fin c) k) * h)) (m.prod (volN ν n c ρ)) := by
      have := hi h
      rw [← hκ] at this
      exact (integrable_map_measure hc'.aestronglyMeasurable hmeas.aemeasurable).1 this
    rw [hf h, ← hκ, integral_map hmeas.aemeasurable hc'.aestronglyMeasurable, integral_prod _ hp]
    rfl
  · have h2 : ρ < c := by omega
    obtain ⟨hNc, -, hNH, -, -⟩ := GlobalTheory.RootEx.VolN.volN_haar_and_modulus k n c (ρ + 1) (by omega) (by omega) ν
    haveI : LocallyCompactSpace (N k n c (ρ + 1)) := hNc.locallyCompactSpace
    haveI := hNH
    haveI := hm
    haveI := hR
    have hmem := (GlobalTheory.RootEx.ParabolicEntries.mem_R_iff_and_mem_RFJ_iff k n c ρ).2 h1 h2
    have hcl : IsClosed (RFJ k n c ρ : Set (GL (n ⊕ Fin c) k)) := by
      have e : (RFJ k n c ρ : Set (GL (n ⊕ Fin c) k)) = ⋂ r : n ⊕ Fin c, ⋂ s : n ⊕ Fin c,
          {g : GL (n ⊕ Fin c) k | (r.isRight ∨ s.isRight) →
            Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) s ≤
              Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) r →
            g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s} := by
        ext g; simp only [SetLike.mem_coe, hmem, Set.mem_iInter, Set.mem_setOf_eq]
      rw [e]
      refine isClosed_iInter fun r => isClosed_iInter fun s => ?_
      by_cases hrs : (r.isRight ∨ s.isRight) ∧ Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) s ≤
          Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) r
      · have : {g : GL (n ⊕ Fin c) k | (r.isRight ∨ s.isRight) →
            Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) s ≤
              Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) r →
            g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s} =
            {g : GL (n ⊕ Fin c) k | g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s} := by
          ext g; simp only [Set.mem_setOf_eq]; exact ⟨fun h => h hrs.1 hrs.2, fun h _ _ => h⟩
        rw [this]
        exact isClosed_eq (GlobalTheory.RootEx.VolN.continuous_entry r s) continuous_const
      · have : {g : GL (n ⊕ Fin c) k | (r.isRight ∨ s.isRight) →
            Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) s ≤
              Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) r →
            g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s} = Set.univ := by
          ext g; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]; exact fun a b => absurd ⟨a, b⟩ hrs
        rw [this]; exact isClosed_univ
    haveI : LocallyCompactSpace (RFJ k n c ρ) := hcl.locallyCompactSpace
    haveI := GlobalTheory.T.isMulLeftInvariant_map_levyProductMapToFourierJacobi k n c ρ h1 h2 ν hν.1 m hm
    haveI := GlobalTheory.T.fourierJacobiProductMap_haar_finiteOnCompacts k n c ρ h1 h2 ν hν.1 m hm
    have hmeas : Measurable (prodRFJ (k := k) (n := n) (c := c) ρ) :=
      (Continuous.subtype_mk (((GlobalTheory.RootEx.QuotStep.continuous_embX.comp (continuous_fst.comp continuous_fst)).mul
        (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))).mul
        ((GlobalTheory.RootEx.QuotStep.continuous_colE (ρ + 1)).comp continuous_snd)) _).measurable
    have hκ : ((m.prod (volN ν n c (ρ + 1))).prod (Measure.pi fun _ : n => ν)).map (prodRFJ ρ) = μR := by
      refine eq_of_mass_one _ μR _ hRK ((Measure.map_apply hmeas (hKO (RFJ k n c ρ))).trans ?_)
      have hpi : {β : n → k | ∀ i, β i ∈ 𝒪[k]} = Set.univ.pi fun _ : n => (𝒪[k] : Set k) := by
        ext β; simp
      rw [GlobalTheory.T.levyProductMapToFourierJacobi_preimage_integralGL k n c ρ h2, Measure.prod_prod, Measure.prod_prod, hmK, GlobalTheory.T.rootExchangeUnipotentHaar_integralPoints_eq_one k n c (ρ + 1) (by omega) (by omega) ν hν, hpi,
        Measure.pi_pi, hν.2]
      simp
    haveI : μR.IsMulRightInvariant := GlobalTheory.LevelUnimod.unimodular k n c (2 * ρ + 1) (fun i => 2 * (i.val + 1))
      (fun i => by simp [Fin.rev]; omega) (RFJ k n c ρ) hmem μR hR
    refine ⟨GlobalTheory.SemiHaar.invInv_of_rightInv μR, ?_⟩
    rintro f z ⟨F, hF, hf, hz⟩
    have hi := hFS _ hcl μR hR F hF
    refine ⟨F, hFint F hF, hi, fun h => ?_, hz⟩
    have hc' : Continuous fun r : RFJ k n c ρ => F (r * h) :=
      hF.1.continuous.comp (continuous_subtype_val.mul continuous_const)
    have hp : Integrable (fun q => F ((prodRFJ (k := k) (n := n) (c := c) ρ q : GL (n ⊕ Fin c) k) * h))
        ((m.prod (volN ν n c (ρ + 1))).prod (Measure.pi fun _ : n => ν)) := by
      have := hi h
      rw [← hκ] at this
      exact (integrable_map_measure hc'.aestronglyMeasurable hmeas.aemeasurable).1 this
    rw [hf h, ← hκ, integral_map hmeas.aemeasurable hc'.aestronglyMeasurable, integral_prod _ hp,
      integral_prod _ hp.integral_prod_left]
    rfl

end GlobalTheory.HaarR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalInvariantIntegralsSymmetricHaarSubgroupsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localInvariantIntegrals_symmetric_haarSubgroups : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (m : Measure (GL n k)) (G : Measure (GL (n ⊕ Fin c) k)), m.IsHaarMeasure → G.IsHaarMeasure → m (KO k n) = 1 → (c + 1 = 2 * ρ → ∀ μR : Measure (R k n c ρ), μR.IsHaarMeasure → μR {x | x.1 ∈ KO k (n ⊕ Fin c)} = 1 → μR.IsInvInvariant ∧ ∀ f z, IsQuotInt ν m G ρ f z → IsQuotIntL1 μR G f z) ∧ (1 ≤ ρ → c = 2 * ρ → ∀ μR : Measure (RFJ k n c ρ), μR.IsHaarMeasure → μR {x | x.1 ∈ KO k (n ⊕ Fin c)} = 1 → μR.IsInvInvariant ∧ ∀ f z, IsQuotIntFJ ν m G ρ f z → IsQuotIntL1 μR G f z) := by
  first | exact @GlobalTheory.HaarR.quot_int_haar | exact GlobalTheory.HaarR.quot_int_haar | (intros; apply GlobalTheory.HaarR.quot_int_haar <;> assumption)
end
