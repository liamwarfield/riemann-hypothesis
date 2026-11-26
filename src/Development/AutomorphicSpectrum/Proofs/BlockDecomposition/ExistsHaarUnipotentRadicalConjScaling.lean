module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactSupportDcos

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarSkewMatricesConjScaling
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarSkewMatricesConjScaling
noncomputable section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SkewMod

open GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.CgMod

variable {D : D7} {n : ℕ}

def skewPart (D : D7) (n : ℕ) (x : Mx D n n) : Mx D n n := half D • (x - adj x)

theorem skewPart_add (x y : Mx D n n) : skewPart D n (x + y) = skewPart D n x + skewPart D n y := by
  simp only [skewPart, adj_add]
  rw [← smul_add]
  congr 1
  abel

def skewPartHom (D : D7) (n : ℕ) : Mx D n n →+ Mx D n n := AddMonoidHom.mk' (skewPart D n) skewPart_add

theorem skewPart_mem (x : Mx D n n) : skewPart D n x ∈ skewA D n := by
  rw [mem_skewA, skewPart, adj_smul, cA_half, adj_sub, adj_adj, ← smul_neg, neg_sub]

theorem skewPart_of_mem {s : Mx D n n} (hs : s ∈ skewA D n) : skewPart D n s = s := by
  rw [skewPart, mem_skewA.1 hs, sub_neg_eq_add, smul_add]
  exact half_smul_add s

theorem skewPart_anti {c : AE D} (hc : cA D c = -c) {s : Mx D n n} (hs : s ∈ skewA D n) :
    skewPart D n (c • s) = 0 := by
  rw [skewPart, adj_smul, mem_skewA.1 hs, hc, neg_smul, smul_neg, neg_neg, sub_self, smul_zero]

theorem skewPart_split {d e : AE D} (he : cA D e = -e) (hde : d * e = 1) (x : Mx D n n) :
    skewPart D n x + d • skewPart D n (e • x) = x := by
  have h : d * half D * e = half D := by rw [mul_comm d, mul_assoc, hde, mul_one]
  rw [skewPart, skewPart, adj_smul, he, neg_smul, sub_neg_eq_add, ← smul_add, smul_smul, smul_smul, h, smul_add,
    smul_sub]
  have := half_smul_add x
  rw [sub_add_add_cancel]
  exact this

set_option synthInstance.maxHeartbeats 400000 in
theorem continuous_skewPart : Continuous (skewPartHom D n) := by
  haveI : IsTopologicalAddGroup (Mx D n n) := (lattice_Mx D n n).1
  have h : Continuous fun x : Mx D n n => x - adj x := continuous_id.sub (continuous_adj (D := D) (m := n) (n := n))
  change Continuous fun x : Mx D n n => half D • (x - adj x)
  exact h.const_smul (half D)

theorem lr_skew (a : GL (Fin n) (AE D)) : ∀ s ∈ skewA D n, GlobalTheory.ModuLR.lrCE a (ad a)⁻¹ s ∈ skewA D n :=
  fun s hs => (skewConj a.1 ⟨s, hs⟩).2

theorem lr_skew_symm (a : GL (Fin n) (AE D)) :
    ∀ s ∈ skewA D n, (GlobalTheory.ModuLR.lrCE a (ad a)⁻¹).symm s ∈ skewA D n :=
  fun s hs => (skewConj (a⁻¹).1 ⟨s, hs⟩).2


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem map_skewConj : ∀ (D : D7) (r : ℕ) (κ : Measure (skewA D r)), κ.IsAddHaarMeasure → ∀ a : GL (Fin r) (AE D), κ.map (skewConj a.1) = ((absA D (Matrix.GeneralLinearGroup.det a) ^ r)⁻¹ : ℝ≥0) • κ := by
  intro D n κ hκ a
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D n n
  haveI : IsTopologicalAddGroup (Mx D n n) := i1
  haveI : LocallyCompactSpace (Mx D n n) := i2
  haveI : SecondCountableTopology (Mx D n n) := i3
  haveI : T2Space (Mx D n n) := i4
  haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
  haveI : BorelSpace (skewA D n) := Subtype.borelSpace _
  haveI : SecondCountableTopology (skewA D n) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space (skewA D n) := Topology.IsEmbedding.subtypeVal.t2Space
  have hcl : IsClosed (skewA D n : Set (Mx D n n)) := isClosed_eq continuous_adj continuous_neg
  haveI : LocallyCompactSpace (skewA D n) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨d, e, hde, hd, he⟩ := exists_anti_units D
  have hsq := char_sq (skewA D n) (skewPartHom D n) continuous_skewPart skewPart_mem
    (fun s hs => skewPart_of_mem hs) (mulCE d e hde)
    (fun s hs => skewPart_anti hd hs) (fun s hs => skewPart_anti he hs)
    (fun x => skewPart_split he hde x) (GlobalTheory.ModuLR.lrCE a (ad a)⁻¹)
    (lr_smul a d e hde) (lr_skew a) (lr_skew_symm a)
  have hlr : addEquivAddHaarChar (GlobalTheory.ModuLR.lrCE a (ad a)⁻¹) =
      absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n * absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n := by
    have h := GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE _ _ D.sp.cm.sig (isCMExt_host D) n n a (ad a)⁻¹
    rw [h]
    exact congrArg (fun t => absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n * t ^ n) (absA_det_ad_inv a)
  have hT : addEquivAddHaarChar (restr (skewA D n) _ (lr_skew a) (lr_skew_symm a)) =
      absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n :=
    (pow_left_inj₀ zero_le zero_le two_ne_zero).1 ((hsq.trans hlr).trans (sq _).symm)
  have h := addEquivAddHaarChar_smul_map κ (restr (skewA D n) _ (lr_skew a) (lr_skew_symm a))
  have e1 : (⇑(restr (skewA D n) _ (lr_skew a) (lr_skew_symm a)) : skewA D n → skewA D n) = skewConj a.1 := rfl
  rw [hT, e1] at h
  have hne : absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n ≠ 0 := pow_ne_zero _ (absA_pos _).ne'
  conv_rhs => rw [← h]
  rw [smul_smul, inv_mul_cancel₀ hne, one_smul]

end GlobalTheory.CompanionTheory.SkewMod
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarSkewMatricesConjScalingStatement
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_skew_matrices_conj_scaling : ∀ (D : D7) (r : ℕ) (κ : Measure (skewA D r)), κ.IsAddHaarMeasure → ∀ a : GL (Fin r) (AE D), κ.map (skewConj a.1) = ((absA D (Matrix.GeneralLinearGroup.det a) ^ r)⁻¹ : ℝ≥0) • κ := by
  first | exact @GlobalTheory.CompanionTheory.SkewMod.map_skewConj | exact GlobalTheory.CompanionTheory.SkewMod.map_skewConj | (intros; apply GlobalTheory.CompanionTheory.SkewMod.map_skewConj <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalHaarFromProduct
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalHaarFromProduct
noncomputable section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.QKAvg.RadHaar

theorem isMulLeftInvariant_map_of {X G : Type*} [MeasurableSpace X] [MeasurableSpace G] [Mul G] (P : Measure X)
    (e : X ≃ᵐ G) (h : ∀ q, ∃ T : X → X, MeasurePreserving T P P ∧ ∀ p, e (T p) = e q * e p) :
    (P.map e).IsMulLeftInvariant := by
  refine ⟨fun g => ?_⟩
  obtain ⟨T, hT, hTe⟩ := h (e.symm g)
  have h1 : (fun x => g * x) = e ∘ T ∘ e.symm := by
    funext x
    simp [hTe]
  have hm : Measurable (fun x => g * x) := by
    rw [h1]
    exact e.measurable.comp (hT.measurable.comp e.symm.measurable)
  rw [Measure.map_map hm e.measurable]
  have h2 : (fun x => g * x) ∘ e = e ∘ T := by
    funext p
    simp [hTe]
  rw [h2, ← Measure.map_map e.measurable hT.measurable, hT.map_eq]

theorem measurePreserving_shear {A C : Type*} [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd₂ A]
    [AddCommGroup C] [MeasurableSpace C] [MeasurableAdd₂ C] (κ : Measure A) (β : Measure C) [SFinite κ] [SFinite β]
    [κ.IsAddLeftInvariant] [β.IsAddLeftInvariant] {f : C → A} (hf : Measurable f) (b₀ : C) :
    MeasurePreserving (fun p : A × C => (p.1 + f p.2, p.2 + b₀)) (κ.prod β) (κ.prod β) := by
  have h1 : MeasurePreserving (fun p : C × A => (b₀ + p.1, f p.1 + p.2)) (β.prod κ) (β.prod κ) :=
    (measurePreserving_add_left β b₀).skew_product (g := fun c a => f c + a)
      (by exact (hf.comp measurable_fst).add measurable_snd)
      (Filter.Eventually.of_forall fun c => map_add_left_eq_self κ (f c))
  have h2 := (Measure.measurePreserving_swap (μ := β) (ν := κ)).comp
    (h1.comp (Measure.measurePreserving_swap (μ := κ) (ν := β)))
  have hfun : (fun p : A × C => (p.1 + f p.2, p.2 + b₀)) =
      Prod.swap ∘ (fun p : C × A => (b₀ + p.1, f p.1 + p.2)) ∘ Prod.swap := by
    funext p
    exact Prod.ext (add_comm _ _) (add_comm _ _)
  rw [hfun]
  exact h2

private theorem isMulRightInvariant_map_of_exists_measurePreserving {X G : Type*} [MeasurableSpace X] [MeasurableSpace G] [Mul G] (P : Measure X)
    (e : X ≃ᵐ G) (h : ∀ q, ∃ T : X → X, MeasurePreserving T P P ∧ ∀ p, e (T p) = e p * e q) :
    (P.map e).IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  obtain ⟨T, hT, hTe⟩ := h (e.symm g)
  have h1 : (fun x => x * g) = e ∘ T ∘ e.symm := by
    funext x
    simp [hTe]
  have hm : Measurable (fun x => x * g) := by
    rw [h1]
    exact e.measurable.comp (hT.measurable.comp e.symm.measurable)
  rw [Measure.map_map hm e.measurable]
  have h2 : (fun x => x * g) ∘ e = e ∘ T := by
    funext p
    simp [hTe]
  rw [h2, ← Measure.map_map e.measurable hT.measurable, hT.map_eq]

theorem haar_of_shear {A C G : Type*} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A] [LocallyCompactSpace A]
    [AddCommGroup C] [TopologicalSpace C] [IsTopologicalAddGroup C]
    [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C] [LocallyCompactSpace C]
    [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    (e : A × C ≃ₜ G) (f : C → C → A) (hf : Continuous fun x : C × C => f x.1 x.2)
    (hmul : ∀ c b c' b', e (c, b) * e (c', b') = e (c + (c' + f b b'), b + b'))
    (κ : Measure A) (β : Measure C) [κ.IsAddHaarMeasure] [β.IsAddHaarMeasure] :
    ((κ.prod β).map e).IsHaarMeasure ∧ ((κ.prod β).map e).IsMulRightInvariant := by
  have hfc : IsFiniteMeasureOnCompacts ((κ.prod β).map e) := by
    refine ⟨fun K hK => ?_⟩
    change (κ.prod β).map e.toMeasurableEquiv K < ⊤
    rw [MeasurableEquiv.map_apply]
    exact (e.isCompact_preimage.2 hK).measure_lt_top
  have hop : Measure.IsOpenPosMeasure ((κ.prod β).map e) := by
    refine ⟨fun U hU hne => ?_⟩
    change (κ.prod β).map e.toMeasurableEquiv U ≠ 0
    rw [MeasurableEquiv.map_apply]
    exact (hU.preimage e.continuous).measure_ne_zero _ (hne.preimage e.surjective)
  have hl : ((κ.prod β).map e).IsMulLeftInvariant := by
    refine isMulLeftInvariant_map_of (κ.prod β) e.toMeasurableEquiv ?_
    rintro ⟨c, b⟩
    refine ⟨fun p => (p.1 + (c + f b p.2), p.2 + b),
      measurePreserving_shear κ β ((hf.comp (continuous_const.prodMk continuous_id)).measurable.const_add c) b, ?_⟩
    rintro ⟨c', b'⟩
    change e _ = e (c, b) * e (c', b')
    rw [hmul]
    congr 1
    exact Prod.ext (add_left_comm _ _ _) (add_comm _ _)
  have hr : ((κ.prod β).map e).IsMulRightInvariant := by
    refine isMulRightInvariant_map_of_exists_measurePreserving (κ.prod β) e.toMeasurableEquiv ?_
    rintro ⟨c, b⟩
    refine ⟨fun p => (p.1 + (c + f p.2 b), p.2 + b),
      measurePreserving_shear κ β ((hf.comp (continuous_id.prodMk continuous_const)).measurable.const_add c) b, ?_⟩
    rintro ⟨c', b'⟩
    change e _ = e (c', b') * e (c, b)
    rw [hmul]
  exact ⟨{ toIsFiniteMeasureOnCompacts := hfc, toIsMulLeftInvariant := hl, toIsOpenPosMeasure := hop }, hr⟩

variable {D : D7} {B W : HSp D} {t : ℕ} (d : HypDec B W t)

def coordB (q : GA D B) : Mx D t W.rank := d.pX ⬝ mt B q ⬝ d.j0

def coordC (q : GA D B) : Mx D t t :=
  d.pX ⬝ mt B q ⬝ d.jY + half D • (coordB d q ⬝ plus W (coordB d q))

theorem pX_nn (c : skewA D t) (b : Mx D t W.rank) : d.pX ⬝ mt B (d.nC c * d.nB b) =
    d.pX + b ⬝ d.p0 - (half D • (b ⬝ plus W b)) ⬝ d.pY + c.1 ⬝ d.pY := by
  rw [GlobalTheory.MixModel.mt_mul, ← Matrix.mul_assoc, GlobalTheory.MixModel.HypDec.pX_nC, Matrix.add_mul, Matrix.mul_assoc, GlobalTheory.MixModel.HypDec.pY_nB, GlobalTheory.MixModel.HypDec.pX_nB]

theorem coordB_nn (c : skewA D t) (b : Mx D t W.rank) : coordB d (d.nC c * d.nB b) = b := by
  rw [coordB, pX_nn]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, GlobalTheory.MixModel.HypDec.pX_j0, GlobalTheory.MixModel.HypDec.p0_j0, GlobalTheory.MixModel.HypDec.pY_j0, Matrix.mul_one,
    Matrix.mul_zero, zero_add, sub_zero, add_zero]

theorem coordC_nn (c : skewA D t) (b : Mx D t W.rank) : coordC d (d.nC c * d.nB b) = c.1 := by
  rw [coordC, coordB_nn, pX_nn]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, GlobalTheory.MixModel.HypDec.pX_jY, GlobalTheory.MixModel.HypDec.p0_jY, GlobalTheory.MixModel.HypDec.pY_jY, Matrix.mul_one,
    Matrix.mul_zero]
  abel

section Top

local instance topRingAE : IsTopologicalRing (AE D) := (Formalism.IndefR.Eqv.ae_facts D).1

local instance topGrpGA (S : HSp D) : IsTopologicalGroup (GA D S) := (Formalism.IndefR.Eqv.ga_facts D S).1

theorem continuous_coordB : Continuous (coordB d) := by
  show Continuous fun q : GA D B => d.pX * mt B q * d.j0
  exact (continuous_const.matrix_mul (GlobalTheory.MixModel.continuous_mt B)).matrix_mul continuous_const

theorem continuous_coordC : Continuous (coordC d) := by
  have hB := continuous_coordB d
  have hP : Continuous fun q : GA D B => GlobalTheory.MixModel.giA W * GlobalTheory.MixModel.adj (coordB d q) :=
    continuous_const.matrix_mul (GlobalTheory.MixModel.continuous_adj.comp hB)
  have hS : Continuous fun q : GA D B =>
      GlobalTheory.MixModel.half D • (coordB d q * (GlobalTheory.MixModel.giA W * GlobalTheory.MixModel.adj (coordB d q))) :=
    (hB.matrix_mul hP).const_smul (GlobalTheory.MixModel.half D)
  have hA : Continuous fun q : GA D B => d.pX * mt B q * d.jY :=
    (continuous_const.matrix_mul (GlobalTheory.MixModel.continuous_mt B)).matrix_mul continuous_const
  exact hA.add hS

theorem coordC_mem (n : radN d) : coordC d n.1.1 ∈ skewA D t := by
  obtain ⟨c, b, h⟩ := n.2
  rw [h, coordC_nn]
  exact c.2

def coordHomeo : (skewA D t × Mx D t W.rank) ≃ₜ radN d where
  toFun p := ⟨⟨d.nC p.1 * d.nB p.2, mul_mem (GlobalTheory.GodementSectionReduction.nC_mem d _) (GlobalTheory.GodementSectionReduction.nB_mem d _)⟩, p.1, p.2, rfl⟩
  invFun n := (⟨coordC d n.1.1, coordC_mem d n⟩, coordB d n.1.1)
  left_inv p := by
    apply Prod.ext
    · exact Subtype.ext (coordC_nn d p.1 p.2)
    · exact coordB_nn d p.1 p.2
  right_inv n := by
    obtain ⟨c, b, h⟩ := n.2
    apply Subtype.ext
    apply Subtype.ext
    change d.nC ⟨coordC d n.1.1, coordC_mem d n⟩ * d.nB (coordB d n.1.1) = n.1.1
    have e1 : (⟨coordC d n.1.1, coordC_mem d n⟩ : skewA D t) = c :=
      Subtype.ext (by change coordC d n.1.1 = c.1; rw [h, coordC_nn])
    rw [e1, h, coordB_nn]
  continuous_toFun :=
    Continuous.subtype_mk (Continuous.subtype_mk
      ((d.continuous_nC.comp continuous_fst).mul (d.continuous_nB.comp continuous_snd)) _) _
  continuous_invFun :=
    (Continuous.subtype_mk ((continuous_coordC d).comp (continuous_subtype_val.comp continuous_subtype_val)) _).prodMk
      ((continuous_coordB d).comp (continuous_subtype_val.comp continuous_subtype_val))

theorem coordHomeo_coe (p : skewA D t × Mx D t W.rank) :
    (((coordHomeo d p : radN d) : GlobalTheory.RegSW.stab d) : GA D B) = d.nC p.1 * d.nB p.2 := rfl

end Top


set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
theorem exists_coord : ∀ (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t) [LocallyCompactSpace (radN d)] (κ : Measure (skewA D t)) (β : Measure (Mx D t W.rank)), κ.IsAddHaarMeasure → β.IsAddHaarMeasure → ∃ Ψ : (skewA D t × Mx D t W.rank) ≃ₜ radN d, (∀ p, (((Ψ p : GlobalTheory.RegSW.stab d) : GA D B)) = d.nC p.1 * d.nB p.2) ∧ ((κ.prod β).map Ψ).IsHaarMeasure ∧ ((κ.prod β).map Ψ).IsMulRightInvariant := by
  intro D B W t d _ κ β hκ hβ
  have hc := coordHomeo_coe d
  obtain ⟨i1, i2, i3, i4, i5⟩ := Formalism.IndefR.Eqv.ae_facts D
  obtain ⟨j1, j2, j3, j4, j5⟩ := Formalism.IndefR.Eqv.ga_facts D B
  have : T2Space (Mx D t t) := inferInstanceAs (T2Space (Fin t → Fin t → AE D))
  have : BorelSpace (Mx D t t) := ⟨rfl⟩
  have : SecondCountableTopology (Mx D t t) := inferInstanceAs (SecondCountableTopology (Fin t → Fin t → AE D))
  have : LocallyCompactSpace (Mx D t t) := inferInstanceAs (LocallyCompactSpace (Fin t → Fin t → AE D))
  have : T2Space (Mx D t W.rank) := inferInstanceAs (T2Space (Fin t → Fin W.rank → AE D))
  have : BorelSpace (Mx D t W.rank) := ⟨rfl⟩
  have : SecondCountableTopology (Mx D t W.rank) := inferInstanceAs (SecondCountableTopology (Fin t → Fin W.rank → AE D))
  have : LocallyCompactSpace (Mx D t W.rank) := inferInstanceAs (LocallyCompactSpace (Fin t → Fin W.rank → AE D))
  have q3 : SecondCountableTopology (skewA D t) :=
    inferInstanceAs (SecondCountableTopology ((skewA D t : Set (Mx D t t))))
  have hcl : IsClosed ((skewA D t : Set (Mx D t t))) := by
    show IsClosed {c : Mx D t t | GlobalTheory.MixModel.adj c = -c}
    exact isClosed_eq GlobalTheory.MixModel.continuous_adj continuous_neg
  have : LocallyCompactSpace (skewA D t) := hcl.locallyCompactSpace
  refine ⟨coordHomeo d, hc, ?_⟩
  refine haar_of_shear (coordHomeo d) (fun b b' => cComm W b b') (GlobalTheory.Unf.HaarCoord.continuous_cComm W t) ?_ κ β
  intro c b c' b'
  apply Subtype.ext
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hc, hc, hc]
  dsimp only
  rw [GlobalTheory.MixModel.HypDec.nC_add, GlobalTheory.MixModel.HypDec.nC_add]
  simp only [mul_assoc]
  rw [← mul_assoc (d.nB b) (d.nC c'), ← GlobalTheory.MixModel.HypDec.nC_mul_nB d b c', mul_assoc (d.nC c'), GlobalTheory.MixModel.HypDec.nB_mul_nB,
    ← GlobalTheory.MixModel.HypDec.nC_mul_nB d (b + b') (cComm W b b')]

end GlobalTheory.CompanionTheory.QKAvg.RadHaar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalHaarFromProductStatement
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_radical_haar_from_product : ∀ (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t) [LocallyCompactSpace (radN d)] (κ : Measure (skewA D t)) (β : Measure (Mx D t W.rank)), κ.IsAddHaarMeasure → β.IsAddHaarMeasure → ∃ Ψ : (skewA D t × Mx D t W.rank) ≃ₜ radN d, (∀ p, (((Ψ p : GlobalTheory.RegSW.stab d) : GA D B)) = d.nC p.1 * d.nB p.2) ∧ ((κ.prod β).map Ψ).IsHaarMeasure ∧ ((κ.prod β).map Ψ).IsMulRightInvariant := by
  first | exact @GlobalTheory.CompanionTheory.QKAvg.RadHaar.exists_coord | exact GlobalTheory.CompanionTheory.QKAvg.RadHaar.exists_coord | (intros; apply GlobalTheory.CompanionTheory.QKAvg.RadHaar.exists_coord <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHaarUnipotentRadicalConjScaling
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.QKAvg.RadMeas

variable {D : D7} {B W : HSp D} {t : ℕ}

theorem absDet_eq (d : HypDec B W t) (m : GlobalTheory.RegSW.stab d) (g : GA D W) (a : GL (Fin t) (AE D))
    (hm : (m : GA D B) = d.emb0 g * d.levi a) :
    GlobalTheory.RegSW.absDet d m = absA D (Matrix.GeneralLinearGroup.det a) := by
  have h : mt B (m : GA D B) ⬝ d.jX = d.jX ⬝ a.1 := by
    rw [hm, mt_mul, Matrix.mul_assoc, d.levi_jX, ← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX]
  have e : GlobalTheory.RegSW.onX d m = a :=
    Units.ext ((GlobalTheory.RegSW.eq_of_mul_jX d (GlobalTheory.RegSW.mul_jX d m)).trans (GlobalTheory.RegSW.eq_of_mul_jX d h).symm)
  simp only [GlobalTheory.RegSW.absDet, MonoidHom.comp_apply, e]

theorem regular_of_haar {A : Type} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A] [BorelSpace A]
    (μ : Measure A) [μ.IsAddHaarMeasure] : μ.Regular := inferInstance

theorem sFinite_of_haar {A : Type} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]
    (μ : Measure A) [μ.IsAddHaarMeasure] : SFinite μ := inferInstance


set_option maxHeartbeats 1000000 in
theorem map_lr {n : ℕ} (a : GL (Fin t) (AE D)) (h : GL (Fin n) (AE D))
    (hh : absA D (Matrix.GeneralLinearGroup.det h) = 1) (β : Measure (Mx D t n)) (hβ : β.IsAddHaarMeasure) :
    β.map (fun b : Mx D t n => (a.1 ⬝ b ⬝ h.1 : Mx D t n)) =
      ((absA D (Matrix.GeneralLinearGroup.det a) ^ n)⁻¹ : ℝ≥0) • β := by
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D t n
  haveI : IsTopologicalAddGroup (Mx D t n) := i1
  haveI : LocallyCompactSpace (Mx D t n) := i2
  haveI : SecondCountableTopology (Mx D t n) := i3
  haveI : T2Space (Mx D t n) := i4
  haveI : BorelSpace (Mx D t n) := ⟨rfl⟩
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  let φ := GlobalTheory.ModuLR.lrCE a h
  have hc : addEquivAddHaarChar φ = absA D (Matrix.GeneralLinearGroup.det a) ^ n *
      absA D (Matrix.GeneralLinearGroup.det h) ^ t :=
    GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE D.host.F D.host.E D.sp.cm.sig (isCMExt_host D) t n a h
  rw [hh, one_pow, mul_one] at hc
  have e : (fun b : Mx D t n => (a.1 ⬝ b ⬝ h.1 : Mx D t n)) = φ :=
    funext fun y => (GlobalTheory.ModuLR.lrCE_apply a h y).symm
  have hA : absA D (Matrix.GeneralLinearGroup.det a) ^ n ≠ 0 := pow_ne_zero _ ((Group.isUnit _).map (absA D)).ne_zero
  haveI := regular_of_haar β
  have key := addEquivAddHaarChar_smul_map β φ
  rw [e, ← hc]
  rw [← hc] at hA
  conv_rhs => rw [← key]
  rw [smul_smul, inv_mul_cancel₀ hA, one_smul]


set_option maxHeartbeats 1000000 in
theorem exists_radN_measure (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t) [LocallyCompactSpace (radN d)] :
    ∃ νN : Measure (radN d), νN.IsHaarMeasure ∧ νN.IsMulRightInvariant ∧ ∀ m ∈ levM d,
      νN.map (fun n : radN d => MulAut.conjNormal m n) =
        ((GlobalTheory.RegSW.absDet d m ^ (W.rank + t))⁻¹ : ℝ≥0) • νN := by
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D t W.rank
  obtain ⟨j1, j2, j3, j4, -, -⟩ := lattice_Mx D t t
  haveI : IsTopologicalAddGroup (Mx D t W.rank) := i1
  haveI : LocallyCompactSpace (Mx D t W.rank) := i2
  haveI : SecondCountableTopology (Mx D t W.rank) := i3
  haveI : T2Space (Mx D t W.rank) := i4
  haveI : BorelSpace (Mx D t W.rank) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (Mx D t t) := j1
  haveI : LocallyCompactSpace (Mx D t t) := j2
  haveI : SecondCountableTopology (Mx D t t) := j3
  haveI : T2Space (Mx D t t) := j4
  haveI : BorelSpace (Mx D t t) := ⟨rfl⟩
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have hcl : IsClosed (skewA D t : Set (Mx D t t)) := isClosed_eq continuous_adj continuous_neg
  haveI : LocallyCompactSpace (skewA D t) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : BorelSpace (skewA D t) := Subtype.borelSpace _
  haveI : T2Space (skewA D t) := inferInstance
  haveI : SecondCountableTopology (skewA D t) :=
    hcl.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  let κ : Measure (skewA D t) := Measure.addHaar
  let β : Measure (Mx D t W.rank) := Measure.addHaar
  haveI hκ : κ.IsAddHaarMeasure := inferInstance
  haveI hβ : β.IsAddHaarMeasure := inferInstance
  haveI := sFinite_of_haar κ
  haveI := sFinite_of_haar β
  obtain ⟨Ψ, hΨ, hH, hR⟩ := GlobalTheory.T.unipotent_radical_haar_from_product D B W t d κ β hκ hβ
  refine ⟨(κ.prod β).map Ψ, hH, hR, ?_⟩
  rintro m ⟨g, a, hm⟩
  let f₁ : skewA D t → skewA D t := skewConj a.1
  let f₂ : Mx D t W.rank → Mx D t W.rank := fun b => (a.1 ⬝ b ⬝ (matHom W g⁻¹).1 : Mx D t W.rank)
  have hf₁ : Continuous f₁ := Continuous.subtype_mk
    ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const) _
  have hf₂ : Continuous f₂ := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have hL : ∀ n : radN d, (((MulAut.conjNormal m n : radN d) : GlobalTheory.RegSW.stab d) : GA D B) =
      (m : GA D B) * ((n : GlobalTheory.RegSW.stab d) : GA D B) * (m : GA D B)⁻¹ := fun n => by
    rw [MulAut.conjNormal_apply]
    rfl
  have hconj : ∀ p, MulAut.conjNormal m (Ψ p) = Ψ (Prod.map f₁ f₂ p) := by
    rintro ⟨c, b⟩
    apply Subtype.ext
    apply Subtype.ext
    refine (hL _).trans ?_
    rw [hΨ (c, b), hΨ (Prod.map f₁ f₂ (c, b)), hm]
    exact conj_coord d g a c b
  have hcm : Measurable fun n : radN d => MulAut.conjNormal m n := by
    have : (fun n : radN d => MulAut.conjNormal m n) = Ψ ∘ Prod.map f₁ f₂ ∘ Ψ.symm := by
      funext n
      simp only [Function.comp]
      rw [← hconj, Ψ.apply_symm_apply]
    rw [this]
    exact (Ψ.continuous.comp ((hf₁.prodMap hf₂).comp Ψ.symm.continuous)).measurable
  have hk := GlobalTheory.T.haar_skew_matrices_conj_scaling D t κ hκ a
  have hb := map_lr a (matHom W g⁻¹) (GlobalTheory.CompanionTheory.HyperbolicDecompositionLaw.absA_det_matHom g⁻¹) β hβ
  rw [Measure.map_map hcm Ψ.continuous.measurable]
  have hc : (fun n : radN d => MulAut.conjNormal m n) ∘ Ψ = Ψ ∘ Prod.map f₁ f₂ := by
    funext p
    exact hconj p
  rw [hc, ← Measure.map_map Ψ.continuous.measurable (hf₁.prodMap hf₂).measurable,
    ← Measure.map_prod_map κ β hf₁.measurable hf₂.measurable]
  change (((κ.map (skewConj a.1)).prod (β.map _)).map Ψ) = _
  rw [hk, hb, Measure.prod_smul_left, Measure.prod_smul_right, Measure.map_smul, Measure.map_smul, smul_smul,
    absDet_eq d m g a hm, pow_add, mul_inv, mul_comm]
  all_goals exact Ψ.continuous.measurable.aemeasurable

end GlobalTheory.CompanionTheory.QKAvg.RadMeas
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHaarUnipotentRadicalConjScalingStatement
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_haar_unipotent_radical_conj_scaling : ∀ (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t) [LocallyCompactSpace (radN d)], ∃ νN : Measure (radN d), νN.IsHaarMeasure ∧ νN.IsMulRightInvariant ∧ ∀ m ∈ levM d, νN.map (fun n : radN d => MulAut.conjNormal m n) = ((GlobalTheory.RegSW.absDet d m ^ (W.rank + t))⁻¹ : ℝ≥0) • νN := by
  first | exact @GlobalTheory.CompanionTheory.QKAvg.RadMeas.exists_radN_measure | exact GlobalTheory.CompanionTheory.QKAvg.RadMeas.exists_radN_measure | (intros; apply GlobalTheory.CompanionTheory.QKAvg.RadMeas.exists_radN_measure <;> assumption)
end
