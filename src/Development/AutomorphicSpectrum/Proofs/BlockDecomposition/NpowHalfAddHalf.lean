module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalWittIsotropicToE0
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientCuspidalPermutation
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicMeasureEulerProductDecomposition
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NpowHalfAddHalf
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsRhoRight
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L GlobalTheory.CompanionTheory.MuC
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace GlobalTheory.CompanionTheory.MuC

theorem isRho_right {D : D7} {p : ℕ} {f : G D p → ℂ} (hf : IsRho f) (x : G D p) :
    IsRho (fun g => f (g * x)) := by
  refine ⟨hf.1.comp (continuous_mul_const x), ?_⟩
  intro q hq a ha g
  have := hf.2 q hq a ha (g * x)
  simpa [mul_assoc] using this

end GlobalTheory.CompanionTheory.MuC
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Cell

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SetCell

variable {D : D7} {p : ℕ}

theorem mem_K_of_mem_KOff {S : Finset (Pl D)} {u : G D p} (hu : u ∈ KOff D p S) : u ∈ K D p := by
  obtain ⟨hf, h1, h2⟩ := mem_levelOff.1 hu
  refine mem_levelAll.2 ⟨fun v => ?_, fun w => ?_⟩
  · by_cases hv : v ∈ S
    · rw [h1 v hv]; exact one_mem _
    · exact h2 v hv
  · rw [mem_finPts_iff_forall.1 hf w]; exact one_mem _

theorem height_mul_K {H : G D p → ℝ≥0} (hH : IsHeight H) {k : G D p} (hk : k ∈ K D p) (g : G D p) :
    H (g * k) = H g := by
  obtain ⟨q, hq, k', hk', rfl⟩ := GlobalTheory.StdUnn.Iwasawa.exists_mul D p g
  rw [mul_assoc, GlobalTheory.CompanionTheory.HtEx.height_eq hH ⟨q, hq⟩ (mul_mem hk' hk), GlobalTheory.CompanionTheory.HtEx.height_eq hH ⟨q, hq⟩ hk']

theorem w_mem_GF {w : G D p} (hw : IsW w) : w ∈ GF D p := by
  have hY : mat w⁻¹ = blk4 0 (-1) 1 0 := by
    have e2 : mat w⁻¹ * mat w = 1 :=
      (show mat (w⁻¹ * w) = mat w⁻¹ * mat w from rfl).symm.trans (by rw [inv_mul_cancel]; rfl)
    have e3 : mat w * blk4 0 (-1) 1 0 = 1 := by
      rw [show mat w = _ from hw, GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul]
      simp [GlobalTheory.StdUnn.Model.block_matrix_one]
    calc mat w⁻¹ = mat w⁻¹ * (mat w * blk4 0 (-1) 1 0) := by rw [e3, mul_one]
      _ = blk4 0 (-1) 1 0 := by rw [← mul_assoc, e2, one_mul]
  refine GlobalTheory.CompanionTheory.PcB.mem_GF w (blk4 0 1 (-1) 0) (blk4 0 (-1) 1 0) ?_ ?_
  · rw [show mat w = _ from hw, GlobalTheory.CompanionTheory.PcB.rational_map_block_matrix, GlobalTheory.CompanionTheory.PcB.rat_zero', GlobalTheory.CompanionTheory.PcB.rat_one', GlobalTheory.CompanionTheory.PcB.rat_neg',
      GlobalTheory.CompanionTheory.PcB.rat_one']
  · rw [hY, GlobalTheory.CompanionTheory.PcB.rational_map_block_matrix, GlobalTheory.CompanionTheory.PcB.rat_zero', GlobalTheory.CompanionTheory.PcB.rat_one', GlobalTheory.CompanionTheory.PcB.rat_neg',
      GlobalTheory.CompanionTheory.PcB.rat_one']

theorem npow_half_add_half (r : ℝ≥0) : npow r ((p : ℂ) / 2 + (p : ℂ) / 2) = (((r : ℝ) ^ p : ℝ) : ℂ) := by
  have e : (p : ℂ) / 2 + (p : ℂ) / 2 = (p : ℂ) := by ring
  rw [e, npow, Complex.cpow_natCast]
  push_cast
  rfl

def hp (H : G D p → ℝ≥0) (g : G D p) : ℝ := (H g : ℝ) ^ p

theorem hp_law {H : G D p → ℝ≥0} (hH : IsHt H) {q : G D p} (hq : q ∈ P D p) {a : GL (Fin p) (AE D)}
    (ha : blkA (mat q) = a.1) (g : G D p) :
    hp H (q * g) = (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) ^ p * hp H g := by
  simp only [hp]
  rw [hH.2.2 q hq a ha g, NNReal.coe_mul, mul_pow]

theorem hp_pos {H : G D p → ℝ≥0} (hH : IsHt H) (g : G D p) : 0 < hp H g :=
  pow_pos (by exact_mod_cast hH.2.1 g) _

theorem exists_block {q : G D p} (hq : q ∈ P D p) : ∃ a : GL (Fin p) (AE D), blkA (mat q) = a.1 :=
  ⟨GlobalTheory.StdUnn.HeightExists.leviBlock (D := D) (n := p) ⟨q, hq⟩, rfl⟩

theorem isRho_iff_sec {H : G D p → ℝ≥0} (hH : IsHt H) (f : G D p → ℂ) : IsRho f ↔ Sec (P D p) (hp H) f := by
  constructor
  · rintro ⟨c, l⟩
    refine ⟨c, fun q hq g => ?_⟩
    obtain ⟨a, ha⟩ := exists_block hq
    rw [l q hq a ha g, hp_law hH hq ha g, npow_half_add_half]
    simp only [MonoidHom.one_apply, Circle.coe_one, one_mul]
    push_cast
    ring
  · rintro ⟨c, l⟩
    refine ⟨c, fun q hq a ha g => ?_⟩
    have h1 := l q hq g
    rw [hp_law hH hq ha g] at h1
    have h0 : ((hp H g : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hp_pos hH g).ne'
    rw [npow_half_add_half]
    simp only [MonoidHom.one_apply, Circle.coe_one, one_mul]
    apply mul_right_cancel₀ h0
    rw [h1]
    push_cast
    ring

theorem setC : HtExist → PositivityTheory.Rg.Rsw.Cell.SetC := by
  intro hEx D p mu hmu
  obtain ⟨H, hH⟩ := GlobalTheory.StdUnn.exists_height D p
  have hI : IsHt H := GlobalTheory.CompanionTheory.HtEx.isHt_of_isHeight hH
  have hS := isRho_iff_sec hI
  refine ⟨hp H, ?_, hS, ?_, ?_⟩
  · refine ⟨GlobalTheory.StdUnn.HeightExists.isClosed_P, (hEx D p).2, ?_, hp_pos hI, ?_, ?_, ?_, ?_⟩
    · exact (NNReal.continuous_coe.comp hI.1).pow p
    · intro q hq g g'
      obtain ⟨a, ha⟩ := exists_block hq
      rw [hp_law hI hq ha g, hp_law hI hq ha g']
      ring
    · exact fun f f' hf hf' => hmu.add f f' ((hS f).2 hf) ((hS f').2 hf')
    · exact fun c f hf => hmu.smul c f ((hS f).2 hf)
    · exact fun f hf h0 => hmu.pos f ((hS f).2 hf) h0
  · intro S u hu g
    simp only [hp]
    rw [height_mul_K hH (mem_K_of_mem_KOff hu) g]
  · intro nb hnb w hw y
    have hN : ∀ f, IsRho f → mu (fun g => f (g * nb y)) = mu f := fun f hf => hmu.inv_n (nb y) y.1 (hnb y) f hf
    have hW := w_mem_GF hw
    refine ⟨fun f hf => hN f ((hS f).2 hf), fun f hf => ?_⟩
    have hf' := (hS f).2 hf
    have r1 := GlobalTheory.CompanionTheory.MuC.isRho_right hf' w⁻¹
    have r2 := GlobalTheory.CompanionTheory.MuC.isRho_right r1 (nb y)
    have e3 := hmu.inv_rat w hW _ r2
    have e2 := hN _ r1
    have e1 := hmu.inv_rat w⁻¹ ((GF D p).inv_mem hW) f hf'
    calc mu (fun g => f (g * (w * nb y * w⁻¹))) = mu (fun g => f (g * w * nb y * w⁻¹)) := by
          simp only [mul_assoc]
      _ = mu f := by rw [e3, e2, e1]

end GlobalTheory.CompanionTheory.SetCell

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CovolumeOneEulerProductMeasureExists
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CovolumeOneEulerProductMeasureExists
noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.CovolA

open NumberField IsDedekindDomain MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB
open GlobalTheory.CompanionTheory.SiegelND.DxN GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler
open scoped TensorProduct ENNReal NNReal

theorem cvN_ratTup {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    {d M n : ℕ} (b : Module.Basis (Fin d) F E) (r : Fin n → Fin M → E) (p : Fin n × (Fin M × Fin d)) :
    cvN R b (ratTup R r : Fin n → Fin M → R ⊗[F] E) p = algebraMap F R (b.repr (r p.1 p.2.1) p.2.2) := by
  simp only [cvN, cv, ratTup, inclR]
  change (Algebra.TensorProduct.basis R b).repr ((1 : R) ⊗ₜ[F] (r p.1 p.2.1)) p.2.2 = _
  rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, one_smul]

section Meas
open GroundTheory.Global
attribute [local instance 100000] GroundTheory.Global.measurableSpace_adeleRing GroundTheory.Global.measurableSpace_infiniteAdeleRing

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_covolOne (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (n : ℕ) {d : ℕ} (b : Module.Basis (Fin d) F E) :
    ∃ (dA : Measure (Fin 1 → Fin n → AF F ⊗[F] E)) (e : (Fin 1 → Fin n → AF F ⊗[F] E) ≃ₜ (Fin 1 × (Fin n × Fin d) → AF F)),
      (∀ X, e X = cvN (AF F) b X) ∧ BorelSpace (Fin 1 → Fin n → AF F ⊗[F] E) ∧
      dA.map e = GroundTheory.Automorphic.GJMatrix.adeleMeasurePi F ∧ IsCovolOne dA := by
  obtain ⟨e, he, hB⟩ := exists_coordHomeoN σ hCM 1 n b
  obtain ⟨t1, -, -, -, -, -, -, -, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)
  haveI : IsTopologicalAddGroup (Fin 1 → Fin n → AF F ⊗[F] E) := inferInstance
  let eA := e.toMeasurableEquiv
  let μ := GroundTheory.Automorphic.GJMatrix.adeleMeasurePi (K := F) (ι := Fin 1 × (Fin n × Fin d))
  have hadd : ∀ x y, e (x + y) = e x + e y := by
    intro x y
    rw [he, he, he]
    funext p
    simp [cvN, cv]
  let φ : (Fin 1 → Fin n → AF F ⊗[F] E) ≃+ (Fin 1 × (Fin n × Fin d) → AF F) :=
    { e.toEquiv with map_add' := hadd }
  have hr : ∀ (r : Fin 1 → Fin n → E) p,
      e (ratTup (AF F) r) p = algebraMap F (AF F) (b.repr (r p.1 p.2.1) p.2.2) := by
    intro r p
    rw [he, cvN_ratTup]
  refine ⟨μ.map eA.symm, e, he, hB, ?_, ?_, e ⁻¹' Set.univ.pi fun _ => fundamentalSet F, ?_, ?_⟩
  · exact MeasurableEquiv.map_map_symm eA
  · exact φ.symm.isAddHaarMeasure_map μ e.symm.continuous e.continuous
  · refine IsAddFundamentalDomain.mk' (eA.measurable (MeasurableSet.univ_pi fun _ =>
      measurableSet_fundamentalSet F)).nullMeasurableSet fun x => ?_
    choose k hk huniq using fun p => existsUnique_sub_mem_fundamentalSet F (e x p)
    let r : Fin 1 → Fin n → E := fun a i => ∑ j, (-k (a, (i, j))) • b j
    have hrk : ∀ p, b.repr (r p.1 p.2.1) p.2.2 = -k p := by
      intro p
      simp only [r]
      rw [Module.Basis.repr_sum_self]
    refine ⟨⟨ratTup (AF F) r, r, rfl⟩, ?_, ?_⟩
    · change e (ratTup (AF F) r + x) ∈ Set.univ.pi fun _ => fundamentalSet F
      rw [hadd]
      intro p _
      have := hk p
      rw [Pi.add_apply, hr, hrk, map_neg, neg_add_eq_sub]
      exact this
    · rintro ⟨_, r', rfl⟩ h
      change e (ratTup (AF F) r' + x) ∈ Set.univ.pi fun _ => fundamentalSet F at h
      rw [hadd] at h
      refine Subtype.ext (e.injective (funext fun p => ?_))
      change e (ratTup (AF F) r') p = e (ratTup (AF F) r) p
      have hp := h p (Set.mem_univ p)
      rw [Pi.add_apply, hr] at hp
      have hk' : -(b.repr (r' p.1 p.2.1) p.2.2) = k p := huniq p _ (by
        change e x p - algebraMap F (AF F) (-(b.repr (r' p.1 p.2.1) p.2.2)) ∈ fundamentalSet F
        rw [map_neg, sub_neg_eq_add, add_comm]
        exact hp)
      rw [hr, hr, hrk, ← hk', neg_neg]
  · rw [MeasurableEquiv.map_apply]
    have : eA.symm ⁻¹' (e ⁻¹' Set.univ.pi fun _ => fundamentalSet F) = Set.univ.pi fun _ => fundamentalSet F := by
      ext u
      simp [eA]
    rw [this]
    change Measure.pi (fun _ => adeleMeasure F) _ = 1
    rw [Measure.pi_pi]
    simp [adeleMeasure_fundamentalSet]

theorem split_coord' (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M n : ℕ) (dx : Measure (Fin n → Fin M → AF F ⊗[F] E))
    {d : ℕ} (b : Module.Basis (Fin d) F E)
    (e : (Fin n → Fin M → AF F ⊗[F] E) ≃ₜ (Fin n × (Fin M × Fin d) → AF F))
    (he : ∀ X, e X = cvN (AF F) b X) (hB : BorelSpace (Fin n → Fin M → AF F ⊗[F] E))
    (hdxc : dx.map e = GroundTheory.Automorphic.GJMatrix.adeleMeasurePi F)
    (l : Measure (InfiniteAdeleRing F)) (hH : l.IsAddHaarMeasure)
    (D : Set (Ainf F)) (hD : IsAddFundamentalDomain (intInf F) D l) (hD1 : l D = 1)
    (lf : Measure (Af F)) (hlf : lf.IsAddHaarMeasure) (h1 : lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1) :
    MeasurePreserving (fun X : Fin n → Fin M → AF F ⊗[F] E => (projInf X, projFin X)) dx
      ((coordW (Ainf F) b l n M).prod (coordW (Af F) b lf n M)) := by
  obtain ⟨-, hAfLC, hAfSC, hAfT2⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  have hEq := adele_eq l hH D hD hD1 lf hlf h1
  obtain ⟨i1, i3⟩ := coordMapN σ hCM (Ainf F) b l hH n M
  obtain ⟨f1, f3⟩ := coordMapN σ hCM (Af F) b lf hlf n M
  haveI hBi := (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Ainf F)).2.2.2.2.2.2.2.1 n M
  haveI hBf := (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Af F)).2.2.2.2.2.2.2.1 n M
  haveI : SigmaFinite l := by
    exact Measure.IsAddHaarMeasure.sigmaFinite l
  haveI : SigmaFinite lf := Measure.IsAddHaarMeasure.sigmaFinite lf
  let eI := (i1.homeomorph).toMeasurableEquiv
  let eF := (f1.homeomorph).toMeasurableEquiv
  let eA := e.toMeasurableEquiv
  have hI : MeasurePreserving eI (coordW (Ainf F) b l n M) (Measure.pi fun _ : Fin n × (Fin M × Fin d) => l) :=
    ⟨eI.measurable, i3⟩
  have hF : MeasurePreserving eF (coordW (Af F) b lf n M) (Measure.pi fun _ : Fin n × (Fin M × Fin d) => lf) :=
    ⟨eF.measurable, f3⟩
  have hΘ := measurePreserving_arrowProdEquivProdArrow (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
    (Fin n × (Fin M × Fin d)) (fun _ => l) (fun _ => lf)
  have hA' : MeasurePreserving eA dx (Measure.pi fun _ : Fin n × (Fin M × Fin d) => l.prod lf) := by
    have e1 : GroundTheory.Automorphic.GJMatrix.adeleMeasurePi (K := F) (ι := Fin n × (Fin M × Fin d)) =
        Measure.pi fun _ : Fin n × (Fin M × Fin d) => l.prod lf := by
      rw [GroundTheory.Automorphic.GJMatrix.adeleMeasurePi, hEq]
    exact ⟨eA.measurable, hdxc.trans e1⟩
  let eP := eI.prodCongr eF
  haveI : SFinite (coordW (Af F) b lf n M) := sfinite_coordW σ hCM b lf hlf n M
  haveI : SFinite (coordW (Ainf F) b l n M) := by
    have hK : IsHomeomorph (GlobalTheory.CompanionTheory.SW.WBox.cK (F := F) (E := E) (Ainf F) b) :=
      (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Ainf F)).2.2.2.2.2.2.1 d b
    haveI := GlobalTheory.CompanionTheory.SW.WBox.sigmaFinite_coordK (Ainf F) hK l
    unfold coordW
    infer_instance
  have hP : MeasurePreserving eP ((coordW (Ainf F) b l n M).prod (coordW (Af F) b lf n M))
      ((Measure.pi fun _ : Fin n × (Fin M × Fin d) => l).prod (Measure.pi fun _ : Fin n × (Fin M × Fin d) => lf)) :=
    hI.prod hF
  refine (hP.comp_left_iff).1 ?_
  have hc := hΘ.comp hA'
  convert hc using 1
  funext X
  have hX : ∀ p, e X p = cvN (AF F) b X p := fun p => by rw [he]
  refine Prod.ext (funext fun p => ?_) (funext fun p => ?_)
  · change cvN (Ainf F) b (projInf X) p = (e X p).1
    rw [hX]
    exact GlobalTheory.CompanionTheory.SW.WBox.cK_map b (fstA F) (X p.1 p.2.1) p.2.2
  · change cvN (Af F) b (projFin X) p = (e X p).2
    rw [hX]
    exact GlobalTheory.CompanionTheory.SW.WBox.cK_map b (sndA F) (X p.1 p.2.1) p.2.2

end Meas

section Euler

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem split_coord (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M n : ℕ) (dx : Measure (Fin n → Fin M → AF F ⊗[F] E))
    {d : ℕ} (b : Module.Basis (Fin d) F E)
    (e : (Fin n → Fin M → AF F ⊗[F] E) ≃ₜ (Fin n × (Fin M × Fin d) → AF F))
    (he : ∀ X, e X = cvN (AF F) b X) (hB : BorelSpace (Fin n → Fin M → AF F ⊗[F] E))
    (hdxc : @Measure.map _ _ _ (@MeasurableSpace.pi _ _ fun _ => GroundTheory.Global.measurableSpace_adeleRing F) e dx =
      @GroundTheory.Automorphic.GJMatrix.adeleMeasurePi F _ _ (Fin n × (Fin M × Fin d)) _)
    (laminf : Measure (Ainf F)) (hinf : IsStdInf laminf)
    (lf : Measure (Af F)) (hlf : lf.IsAddHaarMeasure) (h1 : lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1) :
    MeasurePreserving (fun X : Fin n → Fin M → AF F ⊗[F] E => (projInf X, projFin X)) dx
      ((coordW (Ainf F) b laminf n M).prod (coordW (Af F) b lf n M)) := by
  have hm : GroundTheory.Global.measurableSpace_infiniteAdeleRing F = (measAinf : MeasurableSpace (Ainf F)) :=
    (GroundTheory.Global.borelSpace_infiniteAdeleRing F).measurable_eq
  obtain ⟨l, hl, hH, D, hD, hD1⟩ := @std_transfer F _ _ laminf hinf (GroundTheory.Global.measurableSpace_infiniteAdeleRing F) hm
  have h := split_coord' σ hCM M n dx b e he hB hdxc l hH D hD hD1 lf hlf h1
  rw [coordW_congr hm l laminf hl b n M] at h
  exact h

theorem euler_coord (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M n : ℕ) (dx : Measure (Fin n → Fin M → AF F ⊗[F] E))
    {d : ℕ} (b : Module.Basis (Fin d) F E)
    (e : (Fin n → Fin M → AF F ⊗[F] E) ≃ₜ (Fin n × (Fin M × Fin d) → AF F))
    (he : ∀ X, e X = cvN (AF F) b X) (hB : BorelSpace (Fin n → Fin M → AF F ⊗[F] E))
    (hdxc : @Measure.map _ _ _ (@MeasurableSpace.pi _ _ fun _ => GroundTheory.Global.measurableSpace_adeleRing F) e dx =
      @GroundTheory.Automorphic.GJMatrix.adeleMeasurePi F _ _ (Fin n × (Fin M × Fin d)) _)
    (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v))
    (hinf : IsStdInf laminf) (hlam : ∀ v, IsStdV v (lam v)) :
    IsEulerProd b dx 1 (coordW (Ainf F) b laminf n M) (fun v => coordW (Fv F v) b (lam v) n M) := by
  obtain ⟨lf, hlf, h1⟩ := GlobalTheory.CompanionTheory.AdeleHaar.exists_haar_integral_one F
  have hmass := fun v => coordW_latV σ hCM b lam hlam n M v
  refine ⟨fun v => ?_, ?_, ∅, fun S _ φinf φ hφi hφ => ?_⟩
  · simp only [hmass v]; exact ENNReal.one_lt_top
  · simp only [hmass]; simp [summable_zero]
  · have hT := split_coord σ hCM M n dx b e he hB hdxc laminf hinf lf hlf h1
    obtain ⟨hg, hI⟩ := lint_fin σ hCM b lam hlam lf hlf h1 n M S φ hφ
    haveI := sfinite_coordW σ hCM b lf hlf n M
    set g := ({Y | ∀ v, v ∉ S → projV v Y ∈ latV b v} : Set (Fin n → Fin M → Af F ⊗[F] E)).indicator
      fun Y => ∏ v ∈ S, φ v (projV v Y) with hgdef
    have e' : ∀ X, pureL b S φinf φ X =
        (fun p : _ × _ => φinf p.1 * g p.2) (projInf X, projFin X) := by
      intro X
      by_cases hX : X ∈ intOff b S
      · have hX' : projFin X ∈ ({Y | ∀ v, v ∉ S → projV v Y ∈ latV b v} : Set (Fin n → Fin M → Af F ⊗[F] E)) := hX
        simp only [pureL, Set.indicator_of_mem hX, hgdef, Set.indicator_of_mem hX']
      · have hX' : projFin X ∉ ({Y | ∀ v, v ∉ S → projV v Y ∈ latV b v} : Set (Fin n → Fin M → Af F ⊗[F] E)) := hX
        simp only [pureL, Set.indicator_of_notMem hX, hgdef, Set.indicator_of_notMem hX', mul_zero]
    have hm : Measurable (fun p : (Fin n → Fin M → Ainf F ⊗[F] E) × (Fin n → Fin M → Af F ⊗[F] E) => φinf p.1 * g p.2) :=
      (hφi.comp measurable_fst).mul (hg.comp measurable_snd)
    rw [lintegral_congr e', hT.lintegral_comp hm, lintegral_prod_mul hφi.aemeasurable hg.aemeasurable, hI]
    simp [hmass]

end Euler

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.CovolA

end

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

theorem GlobalTheory.CompanionTheory.WeilSiegel.HypStep.CovolA.exists_dA : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∃ dA : Measure (Fin 1 → Fin n → AF F ⊗[F] E), IsCovolOne dA ∧ IsEulerProd b dA 1 (coordW (Ainf F) b laminf 1 n) (fun v => coordW (Fv F v) b (lam v) 1 n) := by
  intro F E _ _ _ _ _ σ hCM n d b laminf lam hinf hlam
  obtain ⟨dA, e, he, hB, hm, hc⟩ := GlobalTheory.CompanionTheory.WeilSiegel.HypStep.CovolA.exists_covolOne σ hCM n b
  exact ⟨dA, hc, GlobalTheory.CompanionTheory.WeilSiegel.HypStep.CovolA.euler_coord σ hCM n 1 dA b e he hB hm laminf lam hinf hlam⟩
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CovolumeOneEulerProductMeasureExistsStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolume_one_euler_product_measure_exists : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∃ dA : Measure (Fin 1 → Fin n → AF F ⊗[F] E), IsCovolOne dA ∧ IsEulerProd b dA 1 (coordW (Ainf F) b laminf 1 n) (fun v => coordW (Fv F v) b (lam v) 1 n) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.CovolA.exists_dA | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.CovolA.exists_dA | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStep.CovolA.exists_dA <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeStabilizerCompact
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeStabilizerCompact
noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.CompanionTheory.KFin.CompactStab

section Abstract

variable {R : Type} [CommRing R] {O : Subring R} {n : ℕ}

theorem exists_common_denom (hden : ∀ a : R, ∃ s ∈ O, IsUnit s ∧ s * a ∈ O) {ι : Type} (T : Finset ι) (f : ι → R) :
    ∃ w ∈ O, IsUnit w ∧ ∀ i ∈ T, w * f i ∈ O := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, O.one_mem, isUnit_one, by simp⟩
  | insert a T _ ih =>
    obtain ⟨w, hw, hwu, h⟩ := ih
    obtain ⟨s, hs, hsu, h'⟩ := hden (f a)
    refine ⟨w * s, O.mul_mem hw hs, hwu.mul hsu, fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · rw [mul_assoc]; exact O.mul_mem hw h'
    · rw [mul_right_comm]; exact O.mul_mem (h i hi) hs

theorem smul_mem_of_mem {Λ : Submodule O (Fin n → R)} {a : R} {z : Fin n → R} (ha : a ∈ O) (hz : z ∈ Λ) :
    a • z ∈ Λ :=
  Λ.smul_of_tower_mem (⟨a, ha⟩ : O) hz

theorem exists_smul_mem (hden : ∀ a : R, ∃ s ∈ O, IsUnit s ∧ s * a ∈ O) {Λ : Submodule O (Fin n → R)}
    (hs : Submodule.span R (Λ : Set (Fin n → R)) = ⊤) (x : Fin n → R) : ∃ s ∈ O, IsUnit s ∧ s • x ∈ Λ := by
  have hx : x ∈ Submodule.span R (Λ : Set (Fin n → R)) := hs ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, O.one_mem, isUnit_one, by simpa using hx⟩
  | zero => exact ⟨1, O.one_mem, isUnit_one, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs₁, hs₂, hs₃⟩ := hx
    obtain ⟨t, ht₁, ht₂, ht₃⟩ := hy
    refine ⟨s * t, O.mul_mem hs₁ ht₁, hs₂.mul ht₂, ?_⟩
    have : (s * t) • (x + y) = t • (s • x) + s • (t • y) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm t s]
    rw [this]
    exact Λ.add_mem (smul_mem_of_mem ht₁ hs₃) (smul_mem_of_mem hs₁ ht₃)
  | smul a x _ hx =>
    obtain ⟨s, hs₁, hs₂, hs₃⟩ := hx
    obtain ⟨t, ht₁, ht₂, ht₃⟩ := hden a
    refine ⟨t * s, O.mul_mem ht₁ hs₁, ht₂.mul hs₂, ?_⟩
    have : (t * s) • a • x = (t * a) • (s • x) := by
      rw [smul_smul, smul_smul]; congr 1; ring
    rw [this]
    exact smul_mem_of_mem ht₃ hs₃

theorem exists_unit_inner (hden : ∀ a : R, ∃ s ∈ O, IsUnit s ∧ s * a ∈ O) {Λ : Submodule O (Fin n → R)}
    (hs : Submodule.span R (Λ : Set (Fin n → R)) = ⊤) :
    ∃ u ∈ O, IsUnit u ∧ ∀ x : Fin n → R, (∀ i, x i ∈ O) → u • x ∈ Λ := by
  classical
  have h1 : ∀ T : Finset (Fin n), ∃ u ∈ O, IsUnit u ∧ ∀ j ∈ T, u • (Pi.single j 1 : Fin n → R) ∈ Λ := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact ⟨1, O.one_mem, isUnit_one, by simp⟩
    | insert a T _ ih =>
      obtain ⟨w, hw, hwu, h⟩ := ih
      obtain ⟨s, hs₁, hsu, h'⟩ := exists_smul_mem hden hs (Pi.single a 1 : Fin n → R)
      refine ⟨w * s, O.mul_mem hw hs₁, hwu.mul hsu, fun i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · rw [mul_smul]; exact smul_mem_of_mem hw h'
      · rw [mul_comm, mul_smul]; exact smul_mem_of_mem hs₁ (h i hi)
  obtain ⟨u, hu, huu, h⟩ := h1 Finset.univ
  refine ⟨u, hu, huu, fun x hx => ?_⟩
  have e : u • x = ∑ j, x j • (u • (Pi.single j 1 : Fin n → R)) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply, mul_comm]
  rw [e]
  exact sum_mem fun j _ => smul_mem_of_mem (hx j) (h j (Finset.mem_univ _))

theorem exists_unit_outer (hden : ∀ a : R, ∃ s ∈ O, IsUnit s ∧ s * a ∈ O) {Λ : Submodule O (Fin n → R)}
    (hfg : Λ.FG) : ∃ w ∈ O, IsUnit w ∧ ∀ y ∈ Λ, ∀ i, w * y i ∈ O := by
  classical
  obtain ⟨T, rfl⟩ := hfg
  obtain ⟨w, hw, hwu, h⟩ := exists_common_denom hden (T ×ˢ (Finset.univ : Finset (Fin n))) (fun p => p.1 p.2)
  refine ⟨w, hw, hwu, fun y hy i => ?_⟩
  induction hy using Submodule.span_induction with
  | mem y hy => exact h (y, i) (Finset.mem_product.2 ⟨hy, Finset.mem_univ _⟩)
  | zero => simp
  | add y z _ _ hy hz => rw [Pi.add_apply, mul_add]; exact O.add_mem hy hz
  | smul c y _ hy =>
    have : w * (c • y) i = c * (w * y i) := by
      rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul]; ring
    rw [this]
    exact O.mul_mem c.2 hy

variable [TopologicalSpace R] [IsTopologicalRing R]

theorem isOpen_lattice (ho : IsOpen (O : Set R)) (hden : ∀ a : R, ∃ s ∈ O, IsUnit s ∧ s * a ∈ O)
    {Λ : Submodule O (Fin n → R)} (hs : Submodule.span R (Λ : Set (Fin n → R)) = ⊤) :
    IsOpen (Λ : Set (Fin n → R)) := by
  obtain ⟨u, -, huu, h⟩ := exists_unit_inner hden hs
  obtain ⟨c, rfl⟩ := huu
  have hU : IsOpen {x : Fin n → R | ∀ i, ((c⁻¹ : Rˣ) : R) * x i ∈ O} := by
    have : {x : Fin n → R | ∀ i, ((c⁻¹ : Rˣ) : R) * x i ∈ O} =
        ⋂ i, (fun x : Fin n → R => ((c⁻¹ : Rˣ) : R) * x i) ⁻¹' (O : Set R) := by
      ext x; simp
    rw [this]
    exact isOpen_iInter_of_finite fun i => ho.preimage (continuous_const.mul (continuous_apply i))
  have hsub : {x : Fin n → R | ∀ i, ((c⁻¹ : Rˣ) : R) * x i ∈ O} ⊆ (Λ : Set (Fin n → R)) := fun x hx => by
    have := h (fun i => ((c⁻¹ : Rˣ) : R) * x i) hx
    have e : (c : R) • (fun i => ((c⁻¹ : Rˣ) : R) * x i) = x := by
      funext i
      simp
    rwa [e] at this
  have h0 : (Λ : Set (Fin n → R)) ∈ nhds (0 : Fin n → R) :=
    Filter.mem_of_superset (hU.mem_nhds fun i => by simp [O.zero_mem]) hsub
  exact AddSubgroup.isOpen_of_mem_nhds Λ.toAddSubgroup h0

variable [T2Space R]

theorem isCompact_stabGL (hc : IsCompact (O : Set R)) (ho : IsOpen (O : Set R))
    (hden : ∀ a : R, ∃ s ∈ O, IsUnit s ∧ s * a ∈ O) {Λ : Submodule O (Fin n → R)} (hfg : Λ.FG)
    (hs : Submodule.span R (Λ : Set (Fin n → R)) = ⊤) :
    IsCompact {M : GL (Fin n) R | ∀ y, y ∈ Λ ↔ M.1 *ᵥ y ∈ Λ} := by
  classical
  obtain ⟨u, -, huu, hu⟩ := exists_unit_inner hden hs
  obtain ⟨w, -, hwu, hw⟩ := exists_unit_outer hden hfg
  obtain ⟨c, hcdef⟩ := hwu.mul huu
  have hb : ∀ M : GL (Fin n) R, (∀ y, y ∈ Λ → M.1 *ᵥ y ∈ Λ) → ∀ i j, (c : R) * M.1 i j ∈ O := by
    intro M hM i j
    have h1 := hu (Pi.single j 1) (fun i => by
      by_cases e : i = j
      · subst e; simp [O.one_mem]
      · simp [e, O.zero_mem])
    have h2 := hw _ (hM _ h1) i
    have e : w * (M.1 *ᵥ (u • (Pi.single j 1 : Fin n → R))) i = (c : R) * M.1 i j := by
      rw [hcdef, Matrix.mulVec_smul, Pi.smul_apply, Matrix.mulVec_single_one, smul_eq_mul, mul_assoc]
      rfl
    rwa [e] at h2
  let C : Set R := (fun z => ((c⁻¹ : Rˣ) : R) * z) '' (O : Set R)
  have hC : IsCompact C := hc.image (continuous_const.mul continuous_id)
  have hmem : ∀ a : R, (c : R) * a ∈ O → a ∈ C := fun a ha => ⟨_, ha, by simp⟩
  let S : Set (Matrix (Fin n) (Fin n) R) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => C
  have hS : IsCompact S := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hC
  have hK := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) R)).isCompact_preimage
    (hS.prod (hS.image MulOpposite.continuous_op))
  have hop := isOpen_lattice ho hden hs
  have hcl : IsClosed (Λ : Set (Fin n → R)) := AddSubgroup.isClosed_of_isOpen Λ.toAddSubgroup hop
  refine hK.of_isClosed_subset ?_ fun M hM => ?_
  · have e : {M : GL (Fin n) R | ∀ y, y ∈ Λ ↔ M.1 *ᵥ y ∈ Λ} =
        ⋂ y, {M : GL (Fin n) R | y ∈ Λ ↔ M.1 *ᵥ y ∈ Λ} := by
      ext M; simp
    rw [e]
    refine isClosed_iInter fun y => ?_
    have hcont : Continuous fun M : GL (Fin n) R => M.1 *ᵥ y :=
      Continuous.matrix_mulVec Units.continuous_val continuous_const
    by_cases hy : y ∈ Λ
    · have : {M : GL (Fin n) R | y ∈ Λ ↔ M.1 *ᵥ y ∈ Λ} = (fun M : GL (Fin n) R => M.1 *ᵥ y) ⁻¹' (Λ : Set _) := by
        ext M; simp [hy]
      rw [this]
      exact hcl.preimage hcont
    · have : {M : GL (Fin n) R | y ∈ Λ ↔ M.1 *ᵥ y ∈ Λ} = (fun M : GL (Fin n) R => M.1 *ᵥ y) ⁻¹' (Λ : Set _)ᶜ := by
        ext M; simp [hy]
      rw [this]
      exact hop.isClosed_compl.preimage hcont
  · have hM' : ∀ y, y ∈ Λ → M.1 *ᵥ y ∈ Λ := fun y hy => (hM y).1 hy
    have hMi : ∀ y, y ∈ Λ → (M⁻¹).1 *ᵥ y ∈ Λ := fun y hy => by
      refine (hM _).2 ?_
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel]
      simpa using hy
    exact ⟨fun i _ j _ => hmem _ (hb M hM' i j), (M⁻¹).1, fun i _ j _ => hmem _ (hb M⁻¹ hMi i j), rfl⟩

end Abstract

section Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_denom_intLoc (v : HeightOneSpectrum (𝓞 F)) (z : Fv F v ⊗[F] E) :
    ∃ s ∈ intLoc F E v, IsUnit s ∧ s * z ∈ intLoc F E v := by
  have key : ∃ d : (𝓞 E)⁰, ((1 : Fv F v) ⊗ₜ[F] ((d : 𝓞 E) : E)) * z ∈ intLoc F E v := by
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨1, by rw [mul_zero]; exact zero_mem _⟩
    | tmul a x =>
      obtain ⟨c, hc, hca⟩ := HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v a
      obtain ⟨n, m, hm, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
      have hm0 : algebraMap (𝓞 E) E m ≠ 0 := by simpa using nonZeroDivisors.ne_zero hm
      have hc' : algebraMap (𝓞 F) (𝓞 E) c ∈ (𝓞 E)⁰ := mem_nonZeroDivisors_of_ne_zero (by
        simpa using nonZeroDivisors.ne_zero hc)
      refine ⟨⟨_, mul_mem hc' hm⟩, ?_⟩
      convert tmul_mem_intLoc (E := E) hca n using 1
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      have e : (((algebraMap (𝓞 F) (𝓞 E) c * m : 𝓞 E)) : E) * (algebraMap (𝓞 E) E n / algebraMap (𝓞 E) E m) =
          (c : F) • (n : E) := by
        rw [Algebra.smul_def]
        change algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) c * m) * _ = algebraMap F E (algebraMap (𝓞 F) F c) * algebraMap (𝓞 E) E n
        rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
        field_simp
      rw [e, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_comm]
      rfl
    | add y z hy hz =>
      obtain ⟨c, hc⟩ := hy
      obtain ⟨d, hd⟩ := hz
      refine ⟨c * d, ?_⟩
      have e : ((1 : Fv F v) ⊗ₜ[F] (((c * d : (𝓞 E)⁰) : 𝓞 E) : E)) * (y + z) =
          ((1 : Fv F v) ⊗ₜ[F] ((d : 𝓞 E) : E)) * (((1 : Fv F v) ⊗ₜ[F] ((c : 𝓞 E) : E)) * y) +
          ((1 : Fv F v) ⊗ₜ[F] ((c : 𝓞 E) : E)) * (((1 : Fv F v) ⊗ₜ[F] ((d : 𝓞 E) : E)) * z) := by
        rw [← mul_assoc, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_add]
        simp [mul_comm]
      rw [e]
      exact add_mem (mul_mem (tmul_mem_intLoc (one_mem _) _) hc) (mul_mem (tmul_mem_intLoc (one_mem _) _) hd)
  obtain ⟨d, hd⟩ := key
  have hd0 : ((d : 𝓞 E) : E) ≠ 0 := by simpa using nonZeroDivisors.ne_zero d.2
  refine ⟨_, tmul_mem_intLoc (one_mem _) (d : 𝓞 E), IsUnit.of_mul_eq_one ((1 : Fv F v) ⊗ₜ[F] ((d : 𝓞 E) : E)⁻¹) ?_, hd⟩
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_inv_cancel₀ hd0, ← Algebra.TensorProduct.one_def]

end Place

theorem isCompact_stabLat : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}, IsCMExt F E σ → IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (intLoc F E v) (Fin n → Fv F v ⊗[F] E)), IsLat (intLoc F E v) Λ → IsCompact (stabLat σ J Λ : Set (GLoc σ J v)) := by
  intro F E _ _ _ _ _ σ n J _ _ v Λ hΛ
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Fv F v)
  haveI : T2Space (Fv F v ⊗[F] E) := e.isEmbedding.t2Space
  have hcl : IsClosed (HR (Fv F v) σ J : Set (GL (Fin n) (Fv F v ⊗[F] E))) := by
    have hv : Continuous fun g : GL (Fin n) (Fv F v ⊗[F] E) => (g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :=
      Units.continuous_val
    exact isClosed_eq (((hv.matrix_map (GlobalTheory.AdelicUnitaryTop.continuous_sigR (Fv F v) σ)).matrix_transpose.matrix_mul
      continuous_const).matrix_mul hv) continuous_const
  have hemb : Topology.IsClosedEmbedding (matHom (Fv F v) σ J) := hcl.isClosedEmbedding_subtypeVal
  exact hemb.isCompact_preimage (isCompact_stabGL (GlobalTheory.ThK.isCompact_isOpen_intLoc v).1 (GlobalTheory.ThK.isCompact_isOpen_intLoc v).2
    (exists_denom_intLoc v) hΛ.1 hΛ.2)

end GlobalTheory.CompanionTheory.KFin.CompactStab
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeStabilizerCompactStatement
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_stabilizer_compact : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}, IsCMExt F E σ → IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (intLoc F E v) (Fin n → Fv F v ⊗[F] E)), IsLat (intLoc F E v) Λ → IsCompact (stabLat σ J Λ : Set (GLoc σ J v)) := by
  first | exact @GlobalTheory.CompanionTheory.KFin.CompactStab.isCompact_stabLat | exact GlobalTheory.CompanionTheory.KFin.CompactStab.isCompact_stabLat | (intros; apply GlobalTheory.CompanionTheory.KFin.CompactStab.isCompact_stabLat <;> assumption)
end
end
