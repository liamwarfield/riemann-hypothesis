module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCoverPf

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ProdFormula
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.MeasurePreservingPiProd
noncomputable section

open MeasureTheory Topology
open scoped ENNReal

namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

instance sf2 : SigmaFinite ((2 : ℝ≥0∞) • (volume : Measure ℂ)) := by
  rw [← ENNReal.coe_ofNat, ← ENNReal.smul_def]
  infer_instance

section PiProd

variable {ι : Type} [Fintype ι] {α β : ι → Type} [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSpace (β i)]

def piProdEquiv : ((i : ι) → α i × β i) ≃ᵐ ((i : ι) → α i) × ((i : ι) → β i) where
  toFun x := (fun i => (x i).1, fun i => (x i).2)
  invFun p i := (p.1 i, p.2 i)
  left_inv x := rfl
  right_inv p := rfl
  measurable_toFun := (Measurable.of_eval fun i => measurable_fst.comp (measurable_pi_apply i)).prodMk
    (Measurable.of_eval fun i => measurable_snd.comp (measurable_pi_apply i))
  measurable_invFun := Measurable.of_eval fun i =>
    ((measurable_pi_apply i).comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd)

theorem measurePreserving_piProd (μ : ∀ i, Measure (α i)) (ν : ∀ i, Measure (β i)) [∀ i, SigmaFinite (μ i)]
    [∀ i, SigmaFinite (ν i)] :
    MeasurePreserving (piProdEquiv (α := α) (β := β)) (Measure.pi fun i => (μ i).prod (ν i))
      ((Measure.pi μ).prod (Measure.pi ν)) := by
  have hf := (piProdEquiv (α := α) (β := β)).measurable
  refine ⟨hf, ?_⟩
  refine (Measure.prod_eq_generateFrom generateFrom_pi generateFrom_pi isPiSystem_pi isPiSystem_pi
    (Measure.FiniteSpanningSetsIn.pi fun i => (μ i).toFiniteSpanningSetsIn)
    (Measure.FiniteSpanningSetsIn.pi fun i => (ν i).toFiniteSpanningSetsIn) ?_).symm
  rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩
  have hA' : ∀ i, MeasurableSet (A i) := fun i => hA i (Set.mem_univ i)
  have hB' : ∀ i, MeasurableSet (B i) := fun i => hB i (Set.mem_univ i)

  have hpre : (piProdEquiv (α := α) (β := β)) ⁻¹' (Set.univ.pi A ×ˢ Set.univ.pi B) =
      Set.univ.pi fun i => A i ×ˢ B i := by
    ext x
    simp [piProdEquiv, Set.mem_univ_pi, forall_and]
  rw [Measure.map_apply hf ((MeasurableSet.univ_pi hA').prod (MeasurableSet.univ_pi hB')), hpre,
    Measure.pi_pi, Measure.pi_pi, Measure.pi_pi, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => Measure.prod_prod _ _

end PiProd

section Loc

variable {n r : ℕ}

private theorem continuous_Dl_diagonal (l : ℕ) :
    Continuous (fun c : Fin (r + 1) → ℂ => Formalism.L2.SG.RealObj.Dl (Matrix.diagonal c) l) := by
  unfold Formalism.L2.SG.RealObj.Dl
  split_ifs with hl
  · exact (Continuous.matrix_diagonal continuous_id).matrix_submatrix _ _ |>.matrix_det
  · exact continuous_const

theorem gv_cont (T T' : ℝ) : Continuous (fun c : Fin (r + 1) → ℂ => Gv T T' (Matrix.diagonal c)) := by
  unfold Formalism.L2.SG.RealObj.Gv
  exact ((continuous_Dl_diagonal _).norm.pow 2).sub (continuous_const.mul ((continuous_Dl_diagonal _).norm.pow 2))

theorem wtLoc_cont (k : ℕ) (T T' : ℝ) : Continuous (fun c : Fin (r + 1) → ℂ => wtLoc k T T' c) := by
  unfold wtLoc Formalism.L2.SG.RealObj.JacV
  refine ((gv_cont T T').pow _).mul (continuous_finsetProd _ fun l _ => ?_)
  unfold Formalism.L2.SG.RealObj.modC
  exact (((continuous_Dl_diagonal l).norm).pow 2).pow 2

theorem wtLoc_nonneg (k : ℕ) (T T' : ℝ) {c : Fin (r + 1) → ℂ} (hc : c ∈ GoodLoc (r := r) T T') :
    0 ≤ wtLoc k T T' c := by
  unfold wtLoc Formalism.L2.SG.RealObj.JacV
  exact mul_nonneg (pow_nonneg hc.2.le _) (Finset.prod_nonneg fun _ _ => sq_nonneg _)

theorem measurableSet_goodLoc (T T' : ℝ) : MeasurableSet (GoodLoc (r := r) T T') := by
  have h1 : IsOpen {c : Fin (r + 1) → ℂ | ∀ l, c l ≠ 0} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const
  have h2 : IsOpen {c : Fin (r + 1) → ℂ | 0 < Gv T T' (Matrix.diagonal c)} :=
    isOpen_lt continuous_const (gv_cont T T')
  rw [GoodLoc, Set.setOf_and]
  exact (h1.inter h2).measurableSet

def nuLoc (k : ℕ) (T T' C : ℝ) : Measure (Fin (r + 1) → ℂ) :=
  ((dcLoc (r := r)).restrict (GoodLoc (r := r) T T')).withDensity (fun c => ENNReal.ofReal (C * wtLoc k T T' c))

instance (k : ℕ) (T T' C : ℝ) : SigmaFinite (nuLoc (r := r) k T T' C) := by
  unfold nuLoc dcLoc
  exact SigmaFinite.withDensity_ofReal _

variable (ε : Fin n → Bool)

def phiLoc (h : (Fin (r + 1) → ℂ) → Formalism.REAL.UJ ε) (x : (Fin (r + 1) → ℂ) × (Formalism.REAL.UJ ε × Formalism.REAL.UJ ε)) :
    Formalism.REAL.UJ ε :=
  x.2.1 * h x.1 * x.2.2⁻¹

theorem phiLoc_meas {h : (Fin (r + 1) → ℂ) → Formalism.REAL.UJ ε} (hh : Measurable h) : Measurable (phiLoc ε h) := by
  unfold phiLoc
  exact ((measurable_fst.comp measurable_snd).mul (hh.comp measurable_fst)).mul
    (measurable_snd.comp measurable_snd).inv

theorem muG_eq_map (k : ℕ) (T T' : ℝ) (μS μS' : Measure (Formalism.REAL.UJ ε)) [SFinite μS] [SFinite μS']
    (h : (Fin (r + 1) → ℂ) → Formalism.REAL.UJ ε) (hh : Measurable h) (C : ℝ)
    (hD : DisintLoc ε k T T' μS μS' h C) :
    Formalism.REAL.muG ε = ((nuLoc (r := r) k T T' C).prod (μS.prod μS')).map (phiLoc ε h) := by
  have hp := phiLoc_meas ε hh
  refine Measure.ext fun s hs => ?_
  have hφ : Measurable (s.indicator (1 : Formalism.REAL.UJ ε → ℝ≥0∞)) := measurable_const.indicator hs
  have hm : Measurable fun p => s.indicator (1 : Formalism.REAL.UJ ε → ℝ≥0∞) (phiLoc ε h p) := hφ.comp hp
  have hw : Measurable fun c : Fin (r + 1) → ℂ => ENNReal.ofReal (C * wtLoc k T T' c) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (wtLoc_cont k T T').measurable)
  have hg := hm.lintegral_prod_right' (ν := μS.prod μS')
  rw [← lintegral_indicator_one hs, hD _ hφ, Measure.map_apply hp hs, ← lintegral_indicator_one (hp hs)]
  have hind : ((phiLoc ε h) ⁻¹' s).indicator
      (1 : (Fin (r + 1) → ℂ) × (Formalism.REAL.UJ ε × Formalism.REAL.UJ ε) → ℝ≥0∞) =
      fun p => s.indicator (1 : Formalism.REAL.UJ ε → ℝ≥0∞) (phiLoc ε h p) := by
    funext p
    by_cases hx : phiLoc ε h p ∈ s <;> simp [hx]
  rw [hind, lintegral_prod _ hm.aemeasurable, nuLoc, lintegral_withDensity_eq_lintegral_mul _ hw hg]
  refine lintegral_congr fun c => ?_
  congr 1
  have hc : Measurable fun y : Formalism.REAL.UJ ε × Formalism.REAL.UJ ε =>
      s.indicator (1 : Formalism.REAL.UJ ε → ℝ≥0∞) (phiLoc ε h (c, y)) := hm.comp measurable_prodMk_left
  beta_reduce
  rw [lintegral_prod _ hc.aemeasurable]
  rfl

end Loc

end Formalism.L2.SG.RealObj.InfCut.ProductExactness
end
end

noncomputable section

open MeasureTheory Topology
open scoped ENNReal

namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness

section ProdF

variable {ι : Type} [Fintype ι] {r : ℕ} {G : ι → Type} [∀ v, Group (G v)] [∀ v, MeasurableSpace (G v)]
  [∀ v, MeasurableMul₂ (G v)] [∀ v, MeasurableInv (G v)]

theorem prod_formula (mG : ∀ v, Measure (G v)) [∀ v, SigmaFinite (mG v)]
    (ν : ∀ v, Measure (Fin (r + 1) → ℂ)) [∀ v, SigmaFinite (ν v)]
    (μ μ' : ∀ v, Measure (G v)) [∀ v, SigmaFinite (μ v)] [∀ v, SigmaFinite (μ' v)]
    (h : ∀ v, (Fin (r + 1) → ℂ) → G v) (hh : ∀ v, Measurable (h v))
    (hm : ∀ v, mG v = ((ν v).prod ((μ v).prod (μ' v))).map (fun x => x.2.1 * h v x.1 * x.2.2⁻¹))
    (φ : ((v : ι) → G v) → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ x, φ x ∂Measure.pi mG = ∫⁻ c, ∫⁻ s, ∫⁻ s', φ (s * (fun v => h v (c v)) * s'⁻¹)
      ∂Measure.pi μ' ∂Measure.pi μ ∂Measure.pi ν := by
  have hFm : ∀ v, Measurable
      (fun x : (Fin (r + 1) → ℂ) × (G v × G v) => x.2.1 * h v x.1 * x.2.2⁻¹) :=
    fun v => ((measurable_fst.comp measurable_snd).mul ((hh v).comp measurable_fst)).mul
      (measurable_snd.comp measurable_snd).inv
  have : ∀ v, SigmaFinite (((ν v).prod ((μ v).prod (μ' v))).map
      (fun x : (Fin (r + 1) → ℂ) × (G v × G v) => x.2.1 * h v x.1 * x.2.2⁻¹)) := fun v => by
    rw [← hm v]; infer_instance
  have hpi : Measure.pi mG = (Measure.pi fun v => (ν v).prod ((μ v).prod (μ' v))).map
      (fun y v => (y v).2.1 * h v (y v).1 * (y v).2.2⁻¹) := by
    rw [Measure.pi_map_pi (fun v => (hFm v).aemeasurable)]
    congr 1; funext v; exact hm v
  have hYm : Measurable (fun (y : (v : ι) → (Fin (r + 1) → ℂ) × (G v × G v)) (v : ι) =>
      (y v).2.1 * h v (y v).1 * (y v).2.2⁻¹) :=
    Measurable.of_eval fun v => (hFm v).comp (measurable_pi_apply v)
  have hgm : Measurable (fun z : ((v : ι) → (Fin (r + 1) → ℂ)) × (((v : ι) → G v) × ((v : ι) → G v)) =>
      φ (z.2.1 * (fun v => h v (z.1 v)) * z.2.2⁻¹)) := by
    refine hφ.comp (((measurable_fst.comp measurable_snd).mul ?_).mul
      (measurable_snd.comp measurable_snd).inv)
    exact Measurable.of_eval fun v => (hh v).comp ((measurable_pi_apply v).comp measurable_fst)
  have hE1 := measurePreserving_piProd (α := fun _ => Fin (r + 1) → ℂ) (β := fun v => G v × G v)
    ν (fun v => (μ v).prod (μ' v))
  have hE2 := (MeasurePreserving.id (Measure.pi ν)).prod
    (measurePreserving_piProd (α := G) (β := G) μ μ')
  have hE := hE2.comp hE1
  rw [hpi, lintegral_map hφ hYm]
  refine Eq.trans ?_ ((hE.lintegral_comp hgm).trans ?_)
  · rfl
  rw [lintegral_prod _ hgm.aemeasurable]
  refine lintegral_congr fun c => ?_
  exact lintegral_prod (fun y : ((v : ι) → G v) × ((v : ι) → G v) =>
    φ (y.1 * (fun v => h v (c v)) * y.2⁻¹)) (hgm.comp measurable_prodMk_left).aemeasurable

theorem dc_switch (μ μ' : Measure ((v : ι) → G v)) [SFinite μ'] (φ : ((v : ι) → G v) → ℝ≥0∞) (hφ : Measurable φ)
    (γ t t' : (v : ι) → G v) (ht : μ.map (fun x => x * t) = μ) (ht' : μ'.map (fun x => x * t') = μ') :
    ∫⁻ s, ∫⁻ s', φ (s * (t * γ * t'⁻¹) * s'⁻¹) ∂μ' ∂μ = ∫⁻ s, ∫⁻ s', φ (s * γ * s'⁻¹) ∂μ' ∂μ := by
  have hΦ : Measurable fun a : (v : ι) → G v => ∫⁻ s', φ (a * γ * s'⁻¹) ∂μ' :=
    (hφ.comp ((measurable_fst.mul_const γ).mul measurable_snd.inv)).lintegral_prod_right'
  have inner : ∀ a : (v : ι) → G v,
      ∫⁻ s', φ (a * γ * (s' * t')⁻¹) ∂μ' = ∫⁻ s', φ (a * γ * s'⁻¹) ∂μ' := by
    intro a
    have hf : Measurable fun s' : (v : ι) → G v => φ (a * γ * s'⁻¹) :=
      hφ.comp (measurable_const.mul measurable_inv)
    rw [← lintegral_map hf (measurable_mul_const t'), ht']
  calc ∫⁻ s, ∫⁻ s', φ (s * (t * γ * t'⁻¹) * s'⁻¹) ∂μ' ∂μ
      = ∫⁻ s, ∫⁻ s', φ (s * t * γ * (s' * t')⁻¹) ∂μ' ∂μ := by
        refine lintegral_congr fun s => lintegral_congr fun s' => ?_
        congr 1; group
    _ = ∫⁻ s, ∫⁻ s', φ (s * t * γ * s'⁻¹) ∂μ' ∂μ :=
        lintegral_congr fun s => inner (s * t)
    _ = ∫⁻ s, ∫⁻ s', φ (s * γ * s'⁻¹) ∂μ' ∂μ := by
        rw [← lintegral_map hΦ (measurable_mul_const t), ht]

end ProdF

end Formalism.L2.SG.RealObj.InfCut.ProductExactness
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HaarSubIsHaarS
noncomputable section

open MeasureTheory Topology

namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

variable {n : ℕ} {ε : Fin n → Bool}

def haarSub (G : Subgroup (Formalism.REAL.UJ ε)) (hG : IsClosed (G : Set (Formalism.REAL.UJ ε))) : Measure (Formalism.REAL.UJ ε) :=
  haveI : LocallyCompactSpace G := hG.isClosedEmbedding_subtypeVal.locallyCompactSpace
  (Measure.haar : Measure G).map Subtype.val

theorem haarSub_isHaarS (G : Subgroup (Formalism.REAL.UJ ε)) (hG : IsClosed (G : Set (Formalism.REAL.UJ ε))) :
    IsHaarS (G : Set (Formalism.REAL.UJ ε)) (haarSub G hG) := by
  have : LocallyCompactSpace G := hG.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hemb := hG.isClosedEmbedding_subtypeVal
  have hι : Measurable (Subtype.val : G → Formalism.REAL.UJ ε) := measurable_subtype_coe
  have hfin : IsFiniteMeasureOnCompacts (haarSub G hG) := by
    refine ⟨fun K hK => ?_⟩
    rw [haarSub, Measure.map_apply hι hK.measurableSet]
    exact (hemb.isCompact_preimage hK).measure_lt_top
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hfin⟩
  · have := hfin
    infer_instance
  · rw [haarSub, Ne, Measure.map_eq_zero_iff hι.aemeasurable]
    exact NeZero.ne _
  · rw [haarSub, Measure.map_apply hι hG.measurableSet.compl]
    have hempty : (Subtype.val : G → Formalism.REAL.UJ ε) ⁻¹' (G : Set (Formalism.REAL.UJ ε))ᶜ = ∅ := by
      ext x
      simp
    rw [hempty, measure_empty]
  · intro s hs
    rw [haarSub, Measure.map_map (measurable_const_mul s) hι]
    have hcomp : (fun x => s * x) ∘ (Subtype.val : G → Formalism.REAL.UJ ε) =
        Subtype.val ∘ (fun y : G => (⟨s, hs⟩ : G) * y) := rfl
    rw [hcomp, ← Measure.map_map hι (measurable_const_mul _), map_mul_left_eq_self]

end Formalism.L2.SG.RealObj.InfCut.ProductExactness
end
end

noncomputable section

open MeasureTheory Topology NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal

namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section SetM

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def eV (v : InfinitePlace X.B.I.F) : Fin D.R.rS → Fin X.B.I.n → ℂ := fun a => rv X.B.I v (X.eR a)
def pV (v : InfinitePlace X.B.I.F) : Fin D.R.rS → Fin X.B.I.n → ℂ := fun a => rv X.B.I v (X.fR a)
def zV (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) : Fin X.B.I.n → ℂ := rv X.B.I v (X.zR u)

def NGv (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) : Subgroup (Formalism.REAL.UJ (X.B.I.ε v)) :=
  NilradicalHermitianFrames.NH.NG (X.B.I.ε v) (eV X v) (zV X u v)
def HGv (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) : Subgroup (Formalism.REAL.UJ (X.B.I.ε v)) :=
  NilradicalHermitianFrames.NH.HG (X.B.I.ε v) (eV X v) (pV X v) (zV X u v)
def muNv (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) : Measure (Formalism.REAL.UJ (X.B.I.ε v)) :=
  haarSub (NGv X u v) (NilradicalHermitianFrames.NH.NG_closed _ _ _)
def muHv (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) : Measure (Formalism.REAL.UJ (X.B.I.ε v)) :=
  haarSub (HGv X u v) (NilradicalHermitianFrames.NH.HG_closed _ _ _ _)

def muSv (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) : Measure (Formalism.REAL.UJ (X.B.I.ε v)) :=
  ((muNv X u v).prod (muHv X u v)).map (fun q => q.1 * q.2)

theorem muNv_haar (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    IsHaarS (NLoc (X.B.I.ε v) (eV X v) (zV X u v)) (muNv X u v) :=
  haarSub_isHaarS _ _
theorem muHv_haar (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    IsHaarS (HLoc (X.B.I.ε v) (eV X v) (pV X v) (zV X u v)) (muHv X u v) :=
  haarSub_isHaarS _ _

instance (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) : SigmaFinite (muNv X u v) := (muNv_haar X u v).1.1
instance (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) : SigmaFinite (muHv X u v) := (muHv_haar X u v).1.1

def NinfG (u : D.what₂.Word) : Subgroup X.B.I.Ginf := Subgroup.pi Set.univ (fun v => NGv X u v)
def HinfG (u : D.what₂.Word) : Subgroup X.B.I.Ginf := Subgroup.pi Set.univ (fun v => HGv X u v)

theorem NinfG_coe (u : D.what₂.Word) : (NinfG X u : Set X.B.I.Ginf) =
    Ninf X.B.I (fun a => crdOf X.B.I X.ιE X.bas (X.eX a)) (crdOf X.B.I X.ιE X.bas (X.zu u)) := by
  ext g
  unfold Ninf
  simp only [Set.mem_setOf_eq]
  show (∀ v ∈ (Set.univ : Set (InfinitePlace X.B.I.F)), g v ∈ NGv X u v) ↔ _
  simp only [Set.mem_univ, true_implies]
  exact Iff.rfl

theorem HinfG_coe (u : D.what₂.Word) : (HinfG X u : Set X.B.I.Ginf) =
    Hset X.B.I (Set.range (fun a => crdOf X.B.I X.ιE X.bas (X.eX a)) ∪
      Set.range (fun a => crdOf X.B.I X.ιE X.bas (X.fY a)) ∪ {crdOf X.B.I X.ιE X.bas (X.zu u)}) := by
  ext g
  unfold Hset
  simp only [Set.mem_setOf_eq]
  show (∀ v ∈ (Set.univ : Set (InfinitePlace X.B.I.F)), g v ∈ HGv X u v) ↔ _
  simp only [Set.mem_univ, true_implies]
  refine forall_congr' fun v => ?_
  constructor
  · rintro ⟨he, hp, hz⟩ x hx
    rcases hx with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hx
    · exact he a
    · exact hp a
    · rw [Set.mem_singleton_iff.1 hx]
      exact hz
  · intro h
    exact ⟨fun a => h _ (Or.inl (Or.inl ⟨a, rfl⟩)), fun a => h _ (Or.inl (Or.inr ⟨a, rfl⟩)), h _ (Or.inr rfl)⟩

theorem NinfG_closed (u : D.what₂.Word) : IsClosed (NinfG X u : Set X.B.I.Ginf) := by
  show IsClosed (Set.univ.pi fun v => (NGv X u v : Set (Formalism.REAL.UJ (X.B.I.ε v))))
  exact isClosed_set_pi fun v _ => NilradicalHermitianFrames.NH.NG_closed _ _ _

theorem HinfG_closed (u : D.what₂.Word) : IsClosed (HinfG X u : Set X.B.I.Ginf) := by
  show IsClosed (Set.univ.pi fun v => (HGv X u v : Set (Formalism.REAL.UJ (X.B.I.ε v))))
  exact isClosed_set_pi fun v _ => NilradicalHermitianFrames.NH.HG_closed _ _ _ _

theorem muN_eq (u : D.what₂.Word) : ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ∞ ∧ X.muN u = κ • Measure.pi (muNv X u) := by
  obtain ⟨hσ, h0, hc, hi⟩ := X.muN_haar u
  haveI := hσ
  have hv : ∀ v, IsHaarS (NGv X u v : Set (Formalism.REAL.UJ (X.B.I.ε v))) (muNv X u v) :=
    fun v => haarSub_isHaarS _ _
  have hc' : X.muN u (NinfG X u : Set X.B.I.Ginf)ᶜ = 0 := by rw [NinfG_coe]; exact hc
  have hi' : ∀ h ∈ NinfG X u, (X.muN u).map (fun x => h * x) = X.muN u := by
    intro h hh
    apply hi
    rw [← NinfG_coe]
    exact hh
  refine PiM.uniq_on_closed (NinfG X u) (NinfG_closed X u) (X.muN u) (Measure.pi (muNv X u)) hc' ?_ hi' ?_ h0
    (PiM.pi_ne_zero _ fun v => (hv v).1.2.1)
  · show Measure.pi (muNv X u) (Set.univ.pi fun v => (NGv X u v : Set (Formalism.REAL.UJ (X.B.I.ε v))))ᶜ = 0
    exact PiM.pi_conc _ _ fun v => (hv v).1.2.2.1
  · intro g hg
    exact PiM.pi_map_mul_left _ g fun v => (hv v).1.2.2.2 (g v) ((Subgroup.mem_pi _).mp hg v (Set.mem_univ v))

theorem muH_eq (u : D.what₂.Word) : ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ∞ ∧ X.muH u = κ • Measure.pi (muHv X u) := by
  obtain ⟨hσ, h0, hc, hi⟩ := X.muH_haar u
  haveI := hσ
  have hv : ∀ v, IsHaarS (HGv X u v : Set (Formalism.REAL.UJ (X.B.I.ε v))) (muHv X u v) :=
    fun v => haarSub_isHaarS _ _
  have hc' : X.muH u (HinfG X u : Set X.B.I.Ginf)ᶜ = 0 := by rw [HinfG_coe]; exact hc
  have hi' : ∀ h ∈ HinfG X u, (X.muH u).map (fun x => h * x) = X.muH u := by
    intro h hh
    apply hi
    rw [← HinfG_coe]
    exact hh
  refine PiM.uniq_on_closed (HinfG X u) (HinfG_closed X u) (X.muH u) (Measure.pi (muHv X u)) hc' ?_ hi' ?_ h0
    (PiM.pi_ne_zero _ fun v => (hv v).1.2.1)
  · show Measure.pi (muHv X u) (Set.univ.pi fun v => (HGv X u v : Set (Formalism.REAL.UJ (X.B.I.ε v))))ᶜ = 0
    exact PiM.pi_conc _ _ fun v => (hv v).1.2.2.1
  · intro g hg
    exact PiM.pi_map_mul_left _ g fun v => (hv v).1.2.2.2 (g v) ((Subgroup.mem_pi _).mp hg v (Set.mem_univ v))

theorem muS_eq (u : D.what₂.Word) (hσ : ∀ v, SigmaFinite (muSv X u v)) :
    ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ∞ ∧ muS X u = κ • Measure.pi (muSv X u) := by
  obtain ⟨κ1, h1, h1', hN⟩ := muN_eq X u
  obtain ⟨κ2, h2, h2', hH⟩ := muH_eq X u
  have key : ((Measure.pi (muNv X u)).prod (Measure.pi (muHv X u))).map (fun p => p.1 * p.2) =
      Measure.pi (muSv X u) := by
    rw [← (measurePreserving_piProd (muNv X u) (muHv X u)).map_eq,
      Measure.map_map (g := fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2)
        (show Measurable (fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2) from
          (continuous_fst.mul continuous_snd).measurable) piProdEquiv.measurable]
    exact Measure.pi_map_pi
      (f := fun v (q : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v)) => q.1 * q.2) (hμ := hσ)
      (fun v => (show Measurable (fun q : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v) => q.1 * q.2) from
        (continuous_fst.mul continuous_snd).measurable).aemeasurable)
  refine ⟨κ1 * κ2, mul_ne_zero h1 h2, ENNReal.mul_ne_top h1' h2', ?_⟩
  show ((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2) = _
  rw [hN, hH, Measure.prod_smul_left, Measure.prod_smul_right, Measure.map_smul, Measure.map_smul, key,
    smul_smul]
  all_goals exact (show Measurable (fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2) from
    (continuous_fst.mul continuous_snd).measurable).aemeasurable

end SetM

end Formalism.L2.SG.RealObj.InfCut.ProductExactness
