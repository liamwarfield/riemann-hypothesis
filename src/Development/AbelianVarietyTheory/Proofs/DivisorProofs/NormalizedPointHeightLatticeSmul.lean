module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralEqOfNorms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitOffBadOfSuppSplitOff
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianVarietyTorsionCardEqPowProof
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeSmul
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.ChowHt GlobalTheory.Adelic

namespace GlobalTheory.Adelic.HeightScaling

variable {F K : Type} [Field F] [Field K] [NumberField K] {N n : ℕ}

theorem finite_support_log {c : K} (hc : c ≠ 0) :
    (Function.support fun v : FinitePlace K => Real.log (v c)).Finite := by
  refine Set.Finite.subset (FinitePlace.hasFiniteMulSupport hc) fun v hv h1 => hv ?_
  simp only at h1
  simp [h1]

theorem sum_log_eq_zero {c : K} (hc : c ≠ 0) :
    (∑ᶠ v : FinitePlace K, Real.log (v c)) + ∑ τ : K →+* ℂ, Real.log ‖τ c‖ = 0 := by
  have hmul : (Function.mulSupport fun w : FinitePlace K => w c).Finite :=
    FinitePlace.hasFiniteMulSupport hc
  have h1 : ∑ᶠ w : FinitePlace K, Real.log (w c) = Real.log (∏ᶠ w : FinitePlace K, w c) := by
    rw [finsum_eq_sum_of_support_subset (s := hmul.toFinset),
      finprod_eq_prod_of_mulSupport_subset (s := hmul.toFinset) _ (by simp),
      Real.log_prod (fun w _ => (FinitePlace.pos_iff.2 hc).ne')]
    intro w hw
    simp only [Set.Finite.coe_toFinset, Function.mem_mulSupport]
    intro h1
    apply hw
    simp [h1]
  have h2 : ∑ φ : K →+* ℂ, Real.log ‖φ c‖ = Real.log |Algebra.norm ℚ c| := by
    rw [← Real.log_prod (fun φ _ => norm_ne_zero_iff.2 ((map_ne_zero φ).2 hc))]
    congr 1
    have := congr_arg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ c)
    rw [norm_prod] at this
    rw [Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ => ‖φ c‖) (fun φ => ‖φ c‖)
      (fun _ => by simp [RingHom.equivRatAlgHom_apply]), ← this]
    rw [eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
  rw [h1, h2, FinitePlace.prod_eq_inv_abs_norm hc]
  push_cast
  rw [Real.log_inv, neg_add_cancel]

theorem finite_support_log_finSize {w : Matrix (Fin N) (Fin n) F} (hw : Submodule.span F (Set.range w.col) = ⊤)
    (φ : F →+* K) {y : Fin N → K} (hy : y ≠ 0) :
    (Function.support fun v : FinitePlace K => Real.log (finSize w φ v.1 y)).Finite := by
  have hfin : (⋃ k : {k : Fin n // ∑ j, φ (w j k) * y j ≠ 0},
      Function.mulSupport fun v : FinitePlace K => v (∑ j, φ (w j k.1) * y j)).Finite :=
    Set.finite_iUnion fun k => FinitePlace.hasFiniteMulSupport k.2
  refine hfin.subset fun v hv => ?_
  by_contra hn
  apply hv
  have h1 : ∀ k : Fin n, ∑ j, φ (w j k) * y j ≠ 0 → v.1 (∑ j, φ (w j k) * y j) = 1 := fun k hk => by
    by_contra h
    exact hn (Set.mem_iUnion.2 ⟨⟨k, hk⟩, h⟩)
  have hpos := finSize_pos hw φ v.1 hy
  have hle : finSize w φ v.1 y ≤ 1 := Real.iSup_le (fun k => by
    by_cases hk : ∑ j, φ (w j k) * y j = 0
    · rw [hk, map_zero]; exact zero_le_one
    · exact (h1 k hk).le) zero_le_one
  have hge : 1 ≤ finSize w φ v.1 y := by
    by_contra h
    refine hpos.not_ge (Real.iSup_le (fun k => ?_) le_rfl)
    by_cases hk : ∑ j, φ (w j k) * y j = 0
    · rw [hk, map_zero]
    · exact absurd ((h1 k hk).ge.trans (le_finSize w φ v.1 y k)) h
  simp only [le_antisymm hle hge, Real.log_one]

theorem pointHeight_smul : ∀ (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] (N n : ℕ) (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), Submodule.span F (Set.range w.col) = ⊤ → (∀ σ, (A σ).det ≠ 0) → ∀ (y : Fin N → K) (c : K), y ≠ 0 → c ≠ 0 → pointHeight w A (c • y) = pointHeight w A y := by
  intro F K _ _ _ _ _ N n w A hw hA y c hy hc
  rw [pointHeight_eq, pointHeight_eq]
  congr 1
  have e1 : ∀ v : FinitePlace K, Real.log (finSize w (algebraMap F K) v.1 (c • y)) =
      Real.log (v c) + Real.log (finSize w (algebraMap F K) v.1 y) := fun v => by
    rw [finSize_smul, Real.log_mul (v.1.ne_zero hc) (finSize_pos hw _ v.1 hy).ne']
    rfl
  have e2 : ∀ τ : K →+* ℂ, Real.log (archSize (A (τ.comp (algebraMap F K))) fun j => τ ((c • y) j)) =
      Real.log ‖τ c‖ + Real.log (archSize (A (τ.comp (algebraMap F K))) fun j => τ (y j)) := fun τ => by
    have h0 : (fun j => τ (y j)) ≠ 0 := fun h => hy (funext fun j => (map_eq_zero τ).1 (congrFun h j))
    have h1 : (fun j => τ ((c • y) j)) = τ c • fun j => τ (y j) := funext fun j => by simp
    rw [h1, archSize_smul, Real.log_mul (norm_ne_zero_iff.2 ((map_ne_zero τ).2 hc)) (archSize_pos (hA _) h0).ne']
  rw [finsum_congr e1, Finset.sum_congr rfl fun τ _ => e2 τ, Finset.sum_add_distrib,
    finsum_add_distrib (finite_support_log hc) (finite_support_log_finSize hw _ hy)]
  linarith [sum_log_eq_zero hc]

end GlobalTheory.Adelic.HeightScaling
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeSmulStatement
open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.ChowHt GlobalTheory.Adelic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalizedPointHeightLattice_smul : ∀ (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] (N n : ℕ) (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), Submodule.span F (Set.range w.col) = ⊤ → (∀ σ, (A σ).det ≠ 0) → ∀ (y : Fin N → K) (c : K), y ≠ 0 → c ≠ 0 → pointHeight w A (c • y) = pointHeight w A y := by
  first | exact @GlobalTheory.Adelic.HeightScaling.pointHeight_smul | exact GlobalTheory.Adelic.HeightScaling.pointHeight_smul | (intros; apply GlobalTheory.Adelic.HeightScaling.pointHeight_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist
open IsDedekindDomain NumberField Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep

namespace GlobalTheory.SphGal

open GlobalTheory.LFun GlobalTheory.PRep

theorem satEig_map_mul (q m : ℕ) (B : Multiset ℂˣ) (z : ℂˣ) (j : ℕ) :
    satEig q m (B.map (· * z)) j = (z : ℂ) ^ j * satEig q m B j := by
  have h := Multiset.pow_smul_esymm (z : ℂ) j (B.map fun b : ℂˣ => (b : ℂ))
  simp only [smul_eq_mul, Multiset.map_map, Function.comp_def] at h
  simp only [satEig, Multiset.map_map, Function.comp_def, Units.val_mul]
  rw [mul_left_comm, h]
  simp only [mul_comm]

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {m : ℕ}

theorem isUnitAt_det_of_mem {k : GL (Fin m) (w.adicCompletion E)} (hk : k ∈ KGL w (n := m)) :
    Formalism.L2.Host.IsUnitAt w (Matrix.GeneralLinearGroup.det k) := by
  obtain ⟨k, rfl⟩ := hk
  have e : ((Matrix.GeneralLinearGroup.det (bc (Ov E w).subtype k) : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
      ((Matrix.GeneralLinearGroup.det k : (Ov E w)ˣ) : Ov E w) :=
    ((Ov E w).subtype.map_det k.val).symm
  change Valued.v _ = 1
  rw [e]
  generalize Matrix.GeneralLinearGroup.det k = u
  have h1 : Valued.v ((u : Ov E w) : w.adicCompletion E) ≤ 1 := (u : Ov E w).2
  have h2 : Valued.v (((u⁻¹ : (Ov E w)ˣ) : Ov E w) : w.adicCompletion E) ≤ 1 := ((u⁻¹ : (Ov E w)ˣ) : Ov E w).2
  have h3 : Valued.v ((u : Ov E w) : w.adicCompletion E) *
      Valued.v (((u⁻¹ : (Ov E w)ˣ) : Ov E w) : w.adicCompletion E) = 1 := by
    rw [← map_mul, ← Subring.coe_mul, Units.mul_inv]; simp
  exact le_antisymm h1 (h3 ▸ mul_le_of_le_one_right' h2)

theorem det_diagJ {L : Type} [Field L] (ϖ : L) {j : ℕ} (hj : j ≤ m) : (diagJ m ϖ j).det = ϖ ^ j := by
  rw [diagJ, Matrix.det_diagonal, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one,
    Fin.card_filter_val_lt, min_eq_right hj]

theorem loc_det_of_Tj {χ : Formalism.L2.Host.HChar E} (hχ : χ.UnrAt w) {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ)
    {j : ℕ} (hj : j ≤ m) {g : GL (Fin m) (w.adicCompletion E)} (hg : Tj ℂ m (Ov E w) ϖ j g ≠ 0) :
    χ.loc w (Matrix.GeneralLinearGroup.det g) = χ.val w ^ j := by
  obtain ⟨a, ha, b, hb, e⟩ := Set.mem_of_indicator_ne_zero hg
  have h0 : ϖ ≠ 0 := fun h0 => by simp [IsUnifV, h0] at hϖ
  have e2 : Matrix.GeneralLinearGroup.det g =
      Matrix.GeneralLinearGroup.det a * Units.mk0 ϖ h0 ^ j * Matrix.GeneralLinearGroup.det b := by
    apply Units.ext
    change g.val.det = a.val.det * _ * b.val.det
    rw [e, Matrix.det_mul, Matrix.det_mul, det_diagJ ϖ hj]
    simp
  rw [e2, map_mul, map_mul, hχ _ (isUnitAt_det_of_mem ha), hχ _ (isUnitAt_det_of_mem hb), map_pow,
    χ.val_eq hχ (Units.mk0 ϖ h0) hϖ, one_mul, mul_one]

theorem hasSatGL_of_twist {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin m) (w.adicCompletion E)) V}
    {ρ' : Representation ℂ (GL (Fin m) (w.adicCompletion E)) W} {χ : Formalism.L2.Host.HChar E} (hχ : χ.UnrAt w)
    (T : V ≃ₗ[ℂ] W)
    (hT : ∀ g x, ρ' g (T x) = ((χ.loc w (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) • T (ρ g x))
    {B : Multiset ℂˣ} (h : HasSatGL w ρ B) : HasSatGL w ρ' (B.map (· * χ.val w)) := by
  have hf : ∀ x, T x ∈ fixed ρ' (KGL w (n := m)) ↔ x ∈ fixed ρ (KGL w (n := m)) := fun x => by
    simp only [GlobalTheory.LGrp.mem_fixed]
    refine forall₂_congr fun k hk => ?_
    rw [hT, hχ _ (isUnitAt_det_of_mem hk), Units.val_one, one_smul, T.injective.eq_iff]
  constructor
  · obtain ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1 h.1
    exact (Submodule.ne_bot_iff _).2 ⟨T x, (hf x).2 hx, (map_ne_zero_iff T T.injective).2 h0⟩
  · intro y hy h0
    obtain ⟨x, rfl⟩ := T.surjective y
    have hx := h.2 x ((hf x).1 hy) ((map_ne_zero_iff T T.injective).1 h0)
    refine ⟨h0, hy, by rw [Multiset.card_map, hx.2.2.1], fun ϖ hϖ j hj => ?_⟩
    rw [satEig_map_mul, mul_smul, ← map_smul T, ← hx.2.2.2 ϖ hϖ j hj, heckeVec, heckeVec]
    have e := T.toAddEquiv.map_finsum
      (fun c : _ ⧸ KGL w (n := m) => Tj ℂ m (Ov E w) ϖ j c.out • ρ c.out x)
    rw [show T _ = _ from e, smul_finsum]
    refine finsum_congr fun c => ?_
    by_cases hc : Tj ℂ m (Ov E w) ϖ j c.out = 0
    · simp [hc]
    · rw [hT, loc_det_of_Tj hχ hϖ hj hc, smul_comm]
      simp

theorem hasSatGL_twist (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (π : CuspSub E m)
    (χ : Formalism.L2.Host.HChar E) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) (hχ : χ.UnrAt w)
    (h : GlobalTheory.LFun.HasSatGL w (π.locRep w) B) :
    GlobalTheory.LFun.HasSatGL w ((π.twist χ).locRep w) (B.map (· * χ.val w)) := by
  refine hasSatGL_of_twist hχ (π.toTwist χ) (fun g x => ?_) h
  rw [CuspSub.locRep_eq, CuspSub.op_toTwist, opAdd, zero_smul, add_zero, map_smul, opMul, CuspSub.chiDet_locGL]
  rfl

end GlobalTheory.SphGal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaTildeUnramified
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum

namespace GlobalTheory.WeilParts

theorem exists_isEtaTilde_unramified (D : D7) : ∃ η, IsEtaTilde D η := by
  obtain ⟨χ, h1, h2, h3, h4⟩ := GlobalTheory.Mem.EtaTilde.exists_etaTilde D
  exact ⟨χ, h1, h4, h3, h2⟩

end GlobalTheory.WeilParts
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemIntV
noncomputable section

open IsDedekindDomain GlobalTheory.LKTrip
open scoped TensorProduct

namespace GlobalTheory.OrbFinAf

variable {p : ℕ} [Fact p.Prime]

abbrev Qv (v : AwayP p) : Type := v.1.adicCompletion ℚ

abbrev Gv (G : HTGroup p) (v : AwayP p) : Type := UPts G.star (Qv v)

def piV (G : HTGroup p) (v : AwayP p) : G.GAf →* Gv G v := ubcMap (AfP.eval v)

def basV (G : HTGroup p) (v : AwayP p) : Module.Basis (Fin (Module.finrank ℚ G.C)) (Qv v) (Qv v ⊗[ℚ] G.C) :=
  Algebra.TensorProduct.basis (Qv v) (Module.finBasis ℚ G.C)

def IsIntV (G : HTGroup p) (v : AwayP p) (y : Qv v ⊗[ℚ] G.C) : Prop :=
  ∀ i, (basV G v).repr y i ∈ v.1.adicCompletionIntegers ℚ

def IntV (G : HTGroup p) (v : AwayP p) : Set (Gv G v) :=
  {g | IsIntV G v (((g : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) ∧
    IsIntV G v ((((g : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1)⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) ∧
    ((((g : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2 : (Qv v)ˣ) : Qv v) ∈ v.1.adicCompletionIntegers ℚ) ∧
    (((((g : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2)⁻¹ : (Qv v)ˣ) : Qv v) ∈ v.1.adicCompletionIntegers ℚ)}

theorem inv_mem_IntV (G : HTGroup p) (v : AwayP p) {g : Gv G v} (h : g ∈ IntV G v) : g⁻¹ ∈ IntV G v := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h2
  · simpa using h1
  · exact h4
  · simpa using h3

end GlobalTheory.OrbFinAf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjFsBasisOfUnitary
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Points GlobalTheory.TopForm GlobalTheory.ChartGlue GlobalTheory.CechPic
open scoped ContDiff

namespace GlobalTheory

open CxPts

section Pull

variable {k k' : Type} [CommRing k] [CommRing k'] {Y Y' : Scheme.{0}} {p : Y ⟶ Sp k}
  {p' : Y' ⟶ Sp k'} {σ : k →+* ℂ} {σ' : k' →+* ℂ} {D D' : ℕ} {f : Y' ⟶ Y}
  {m : CxPts p' σ' → CxPts p σ}

namespace CxPts

theorem continuous_of_comp (hm : ∀ z, (m z).1 = z.1 ≫ f) : Continuous m :=
  continuous_induced_rng.2
    (((Points.continuous_comp f).comp continuous_subtype_val).congr fun z => (hm z).symm)

theorem mem_ptsIn_preimage (hm : ∀ z, (m z).1 = z.1 ≫ f) {U : Y.Opens} {z : CxPts p' σ'} :
    z ∈ ptsIn p' σ' (f ⁻¹ᵁ U) ↔ m z ∈ ptsIn p σ U := by
  change _ ↔ ⊤ ≤ (m z).1 ⁻¹ᵁ U
  rw [hm]
  rfl

theorem ev_of_comp (hm : ∀ z, (m z).1 = z.1 ≫ f) (U : Y.Opens) (g : Γ(Y, U)) (z : CxPts p' σ') :
    ev p σ U g (m z) = ev p' σ' (f ⁻¹ᵁ U) (f.app U g) z := by
  rw [ev, ev, hm]
  exact valR_comp _ _ _ _

end CxPts

theorem AlgChart.holo_map (hm : ∀ z, (m z).1 = z.1 ≫ f) (c' : AlgChart p' σ' D')
    (c : AlgChart p σ D) : DifferentiableOn ℂ (c.e ∘ m ∘ c'.e.symm)
      (c'.e.target ∩ c'.e.symm ⁻¹' (m ⁻¹' c.e.source)) :=
  differentiableOn_euclidean.2 fun a => ((c'.holo _ (f.app _ (c.x a))).mono fun x (hv : x ∈ c'.e.target ∩ c'.e.symm ⁻¹' (m ⁻¹' c.e.source)) =>
    ⟨hv.1, (mem_ptsIn_preimage hm).2 (c.source_subset hv.2)⟩).congr fun _ hv =>
      (c.apply_eq _ hv.2 a).trans (ev_of_comp hm _ _ _)

namespace AnRead

variable {R : AnRead p σ D} {S : Set (CxPts p σ)}

theorem exists_eventuallyEq_comp (hm : ∀ z, (m z).1 = z.1 ≫ f) (c : AlgChart p' σ' D') {v : V D'}
    (hv : v ∈ c.e.target) {E : Type*} (g : CxPts p σ → E) :
    ∃ i, m (c.e.symm v) ∈ (R.chart i).e.source ∧
      (g ∘ m) ∘ c.e.symm =ᶠ[𝓝 v] (g ∘ (R.chart i).e.symm) ∘ (R.chart i).e ∘ m ∘ c.e.symm := by
  obtain ⟨i, hi⟩ := R.cover (m (c.e.symm v))
  exact ⟨i, hi, eventually_of_mem ((isOpen_over c.e ((R.chart i).e.open_source.preimage
    (continuous_of_comp hm))).mem_nhds ⟨hv, hi⟩)
    fun w hw => (congrArg g ((R.chart i).e.left_inv hw.2)).symm⟩

theorem HoloOn.comp_map {g : CxPts p σ → ℂ} (h : R.HoloOn S g) (hS : IsOpen S)
    (hm : ∀ z, (m z).1 = z.1 ≫ f) (R' : AnRead p' σ' D') : R'.HoloOn (m ⁻¹' S) (g ∘ m) :=
  fun j v hv => by
  obtain ⟨i, hi, e⟩ := exists_eventuallyEq_comp (R := R) hm (R'.chart j) hv.1 g
  have ho := isOpen_over (R'.chart j).e ((R.chart i).e.open_source.preimage (continuous_of_comp hm))
  exact ((((h i).differentiableAt ((isOpen_over _ hS).mem_nhds (mem_over _ hi hv.2))).comp v
    (((R'.chart j).holo_map hm (R.chart i)).differentiableAt
      (ho.mem_nhds ⟨hv.1, hi⟩))).congr_of_eventuallyEq e).differentiableWithinAt

theorem SmoothOn.comp_map {g : CxPts p σ → ℝ} (h : R.SmoothOn S g) (hS : IsOpen S)
    (hm : ∀ z, (m z).1 = z.1 ≫ f) (R' : AnRead p' σ' D') : R'.SmoothOn (m ⁻¹' S) (g ∘ m) :=
  fun j v hv => by
  obtain ⟨i, hi, e⟩ := exists_eventuallyEq_comp (R := R) hm (R'.chart j) hv.1 g
  have ho := isOpen_over (R'.chart j).e ((R.chart i).e.open_source.preimage (continuous_of_comp hm))
  have ht : ContDiffOn ℝ ∞ ((R.chart i).e ∘ m ∘ (R'.chart j).e.symm) _ :=
    (contDiffOn_piLp 2).2 fun a => contDiffOn_real ho
      (differentiableOn_euclidean.1 ((R'.chart j).holo_map hm (R.chart i)) a)
  exact ((((h i).contDiffAt ((isOpen_over _ hS).mem_nhds (mem_over _ hi hv.2))).comp v
    (ht.contDiffAt (ho.mem_nhds ⟨hv.1, hi⟩))).congr_of_eventuallyEq e).contDiffWithinAt

end AnRead

namespace Weight

variable {R : AnRead p σ D} {B : LB Y} {φ : Weight p σ B}

theorem IsSmooth.linComb (h : φ.IsSmooth R) {κ : Type} [Fintype κ] (f : κ → (Y' ⟶ Y)) (ε : κ → ℤ)
    (m : κ → CxPts p' σ' → CxPts p σ) (hm : ∀ a z, (m a z).1 = z.1 ≫ f a) (R' : AnRead p' σ' D') :
    (φ.linComb f ε m hm).IsSmooth R' := fun j c =>
  ContDiffOn.sum (f := fun a v => (ε a : ℝ) * φ.φ (j a) (m a ((R'.chart c).e.symm v))) fun a _ =>
    contDiffOn_const.mul ((((h (j a)).comp_map (isOpen_ptsIn _) (hm a) R').mono
      fun z hz => mem_of_mem_linComb (hm · z) hz a) c)

theorem IsSmooth.pull (h : φ.IsSmooth R) {q : Y' ⟶ Sp k} (f : Y' ⟶ Y) (hf : f ≫ p = q)
    (R' : AnRead q σ D') : (φ.pull f hf).IsSmooth R' :=
  h.linComb _ _ _ _ R'

end Weight

end Pull

section Conj

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ σ' : k →+* ℂ} {A B : LB Y}

theorem CxPts.ev_conj {y : CxPts p σ} {y' : CxPts p σ'} (h : y'.1 = spMap (starRingEnd ℂ) ≫ y.1)
    {U : Y.Opens} (hy : y ∈ ptsIn p σ U) (g : Γ(Y, U)) :
    ev p σ' U g y' = starRingEnd ℂ (ev p σ U g y) := by
  rw [ev, h]
  exact valR_conjHomeomorph y.1 U hy g

theorem sum_normSq_vecMul_unitary {α : Type*} [Fintype α] [DecidableEq α] {U : Matrix α α ℂ}
    (hU : U ∈ Matrix.unitaryGroup α ℂ) (w : α → ℂ) :
    ∑ a, ‖Matrix.vecMul w U a‖ ^ 2 = ∑ a, ‖w a‖ ^ 2 := by
  have key (x : α → ℂ) : ((∑ a, ‖x a‖ ^ 2 : ℝ) : ℂ) = x ⬝ᵥ star x := by
    simp only [dotProduct, Pi.star_apply, RCLike.star_def, Complex.mul_conj', Complex.ofReal_sum,
      Complex.ofReal_pow]
  apply Complex.ofReal_injective
  rw [key, key, Matrix.star_vecMul, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff.1 hU, Matrix.vecMul_one]

namespace Weight

theorem isConj_fsBasis_of_unitary {α : Type*} [Fintype α] [DecidableEq α] (hB : B.IsLB)
    (b : α → B.Sec) (hb : ⨆ j, nonzeroLocus (b j) = ⊤) {M M' U : Matrix α α ℂ}
    (hM : M.det ≠ 0) (hM' : M'.det ≠ 0) (hU : U ∈ Matrix.unitaryGroup α ℂ)
    (e : M' = M.map (starRingEnd ℂ) * U) :
    (fsBasis p σ hB b hb M hM).IsConj (fsBasis p σ' hB b hb M' hM') := fun i y y' h hy => by
  rw [fsBasis_φ, fsBasis_φ]
  congr 1
  have hv (j : α) : valR y'.1 (B.U i) ((b j).f i) = starRingEnd ℂ (valR y.1 (B.U i) ((b j).f i)) :=
    CxPts.ev_conj h hy _
  have := sum_normSq_vecMul_unitary hU fun a =>
    starRingEnd ℂ (∑ j, M j a * valR y.1 (B.U i) ((b j).f i))
  simp only [RCLike.norm_conj] at this
  refine Eq.trans (Finset.sum_congr rfl fun a _ => ?_) this
  congr 2
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [e, hv, Matrix.mul_apply, Matrix.map_apply, Matrix.vecMul, dotProduct, map_sum, map_mul,
    Finset.sum_mul]
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)

variable {φ : Weight p σ B} {φ' : Weight p σ' B}

end Weight

end Conj

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlacesApart
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepLifts

theorem prime_eq_of_mem {K : Type} [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (h1 : (p : 𝓞 K) ∈ P.asIdeal) (h2 : (q : 𝓞 K) ∈ P.asIdeal) : p = q := by
  by_contra hne
  obtain ⟨a, b, hab⟩ : IsCoprime (p : 𝓞 K) (q : 𝓞 K) := Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)
  exact P.isPrime.ne_top
    ((Ideal.eq_top_iff_one _).2 (hab ▸ add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)))

theorem places_apart {D : D7} {T : Type} (L : LevCh D T) {μ0 : T} (h : L.Is μ0) (t : T) :
    (∀ PP ∈ L.Pg, ∀ PP', PP' ∈ L.Pg ∨ PP' ∈ L.Q t → ¬ Lev.IsConjPl PP PP') ∧ Disjoint L.Pg (L.Q t) := by
  have hQ : ∀ PP ∈ L.Q t, ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := by
    intro PP hP k hk
    obtain ⟨⟨q, hq, hc, -, hne⟩, -⟩ := h.Q_pl t PP hP
    have h1 : (q : 𝓞 D.host.E) ∈ PP.asIdeal := by
      rw [← hc]
      rw [← Ideal.absNorm_eq_natCard]
      exact Ideal.absNorm_mem PP.asIdeal
    exact hne k (prime_eq_of_mem PP hq (D.host.g_prime k) h1 hk)
  refine ⟨fun PP hP PP' hP' hc => ?_, Finset.disjoint_left.2 fun PP hP hP' => ?_⟩
  · rcases hP' with hP' | hP'
    · exact GlobalTheory.TypePlaces.not_isConjPl L.C.P L.Pg h.Pg PP hP PP' hP' hc
    · obtain ⟨k, hk⟩ := (h.Pg PP).1 hP
      obtain ⟨c, hc', e⟩ := hc _ (L.C.P.overP hk)
      have e' : c = ((D.host.g k : ℕ) : 𝓞 D.host.E) := RingOfIntegers.ext (by rw [e]; simp)
      exact hQ PP' hP' k (e' ▸ hc')
  · obtain ⟨k, hk⟩ := (h.Pg PP).1 hP
    exact hQ PP hP' k (L.C.P.overP hk)

theorem lifts_exist : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → ∀ (i : Fin D.R.m), (∀ (t : T) (g0 : G0 R.Pg D.R.r), ∃ κ, IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ) ∧ ∀ g0 : G0 R.Pg D.R.r, ∃ κ', IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ' := by
  intro D G _ _ Pl0 T A Ks _ _ _ R h i
  obtain ⟨c, hc⟩ := h.βV i
  obtain ⟨c', hc'⟩ := h.βW i
  refine ⟨fun t => ?_, ?_⟩
  · exact GlobalTheory.ParahoricLift.liftsExist (Vc D i) (R.βV i) (R.datVt i t) _ _ hc (places_apart _ h t).1 (places_apart _ h t).2
  · refine GlobalTheory.ParahoricLift.liftsExist (Wc D i) (R.βW i) (R.datWp i R.triv) _ _ hc' (fun PP hP PP' hP' => ?_)
      (Finset.disjoint_empty_right _)
    exact (places_apart _ h A.μ0).1 PP hP PP' (hP'.imp id fun h0 => absurd h0 (Finset.notMem_empty _))

end GlobalTheory.StepLifts
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyHomologyEquiv
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.Adelic GlobalTheory.CechPic

namespace GlobalTheory.FieldChangeInter

variable {X X' : Scheme.{0}}

def cechIso {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X) {κ : Type} [LinearOrder κ]
    (D : κ → X.Opens) :
    letI := algebraΓOfHom f
    cechLB f M D ≅ cech R (LB.toMod M) ⊤ D :=
  letI := algebraΓOfHom f
  (cechFunctor κ R).mapIso (Cube.isoMk (fun s => LinearEquiv.ofBijective
    (M := SecOnR f M (⨅ i ∈ s, D i)) (M₂ := sectionsOn (LB.toMod M) (⊤ ⊓ ⨅ i ∈ s, D i))
    (SecOnR.restrict f M (inf_le_right : ⊤ ⊓ (⨅ i ∈ s, D i) ≤ ⨅ i ∈ s, D i))
    (SecOnR.restrict_bijective f _ (le_inf le_top le_rfl)))
    fun {s t} h x => (SecOnR.restrict_restrict f _ inf_le_right x).trans
      (SecOnR.restrict_restrict f inf_le_right (cechOpen_anti ⊤ D h) x).symm)

theorem nonempty_homology_equiv {R : Type} (O : Type) [CommRing R] [CommRing O]
    [Algebra R O] [Module.Flat R O] (C : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    Nonempty ((((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R O)).mapHomologicalComplex _).obj
      C).homology n ≃ₗ[O] O ⊗[R] C.homology n) := by
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.flat_algebraMap_iff.2 (inferInstance : Module.Flat R O))
  have : (ModuleCat.extendScalars.{0, 0, 0} (algebraMap R O)).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj (algebraMap R O)).isLeftAdjoint
  obtain ⟨e⟩ := Semicont.nonempty_extendScalars_obj_equiv O (C.homology n)
  exact ⟨((C.sc n).mapHomologyIso
    (ModuleCat.extendScalars.{0, 0, 0} (algebraMap R O))).toLinearEquiv ≪≫ₗ e⟩

theorem nonempty_coh_equiv {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) {M : LB X} (hM : M.IsLB)
    {κ : Type} [LinearOrder κ] [Finite κ] {D : κ → X.Opens} (hc : ⨆ i, D i = ⊤)
    (hD : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, D i)) (n : ℕ) :
    letI := algebraΓOfHom f
    Nonempty ((cechLB f M D).homology n ≃ₗ[R] coh (twist (structureModule X) M) n) := by
  letI := algebraΓOfHom f
  haveI := LB.isQuasicoherent_toMod hM
  exact ⟨((HomologicalComplex.homologyFunctor _ _ n).mapIso (cechIso f M D)).toLinearEquiv ≪≫ₗ
    cechHEquivCoh R hc hD (LB.toMod M) n ≪≫ₗ (cohOn.mapIso R ⊤ n (Twist.unitTwistIso M)).symm⟩

variable {k E : Type} [Field k] [Field E] [Algebra k E] {f : X ⟶ Spec (CommRingCat.of k)}
  {f' : X' ⟶ Spec (CommRingCat.of E)} {π : X' ⟶ X}

theorem hdim_pull [QuasiCompact f] [IsSeparated f]
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap k E)))) {M : LB X} (hM : M.IsLB) (n : ℕ) :
    letI := algebraΓOfHom f
    letI := algebraΓOfHom f'
    hdim E (twist (structureModule X') (M.pull π)) n = hdim k (twist (structureModule X) M) n := by
  letI := algebraΓOfHom f
  letI := algebraΓOfHom f'
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have := isAffineHom_diagonal_of_isSeparated f
  obtain ⟨m, D, hD, hc⟩ := exists_fin_affine_cover (X := X) (V := ⊤) isCompact_univ
  have hD' := isAffineOpen_finset_biInf hD
  obtain ⟨e₁⟩ := nonempty_coh_equiv f hM hc hD' n
  obtain ⟨e₂⟩ := nonempty_coh_equiv f' (LB.isLB_pull hM π) (D := fun i => π ⁻¹ᵁ D i)
    (by rw [← Scheme.Hom.preimage_iSup, hc]; rfl) (fun s hs => isAffineOpen_biInf_preimage H (hD' s hs)) n
  obtain ⟨e₃⟩ := nonempty_homology_equiv E (cechLB f M D) n
  have e₄ := ((HomologicalComplex.homologyFunctor _ _ n).mapIso (cechLBBaseChangeIso hM H hD')).toLinearEquiv
  rw [hdim_def, hdim_def, ← e₁.finrank_eq, ← e₂.finrank_eq]
  exact e₄.finrank_eq.symm.trans (e₃.finrank_eq.trans Module.finrank_baseChange)

theorem interNum_pull [QuasiCompact f] [IsSeparated f]
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap k E)))) {ι : Type} [Fintype ι] {L : ι → LB X}
    (hL : ∀ i, (L i).IsLB) :
    letI := algebraΓOfHom f
    letI := algebraΓOfHom f'
    interNum E (structureModule X') (fun i => (L i).pull π) = interNum k (structureModule X) L := by
  letI := algebraΓOfHom f
  letI := algebraΓOfHom f'
  have h : chiPic k (structureModule X) = chiPic E (structureModule X') ∘ pull π := by
    funext c
    obtain ⟨M, hM, rfl⟩ := cls_surj c
    exact finsum_congr fun n => congrArg (fun a : ℕ => (-1 : ℤ) ^ n * a) (hdim_pull H hM n).symm
  rw [interNum_eq_multiDiff k _ hL, h, multiDiff_comap, Function.comp_apply, map_zero,
    interNum_eq_multiDiff E _ fun i ↦ pull_isLB (hL i) π]
  rfl

theorem del_baseChange : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (S : LinSys k),
    IsProjOver S.str → (S.baseChange E).del = S.del := by
  intro k E _ _ _ S h
  have : IsProper S.str := by
    obtain ⟨N, i, hi, e⟩ := h
    have := isProper_str k N
    rw [← e]
    infer_instance
  exact interNum_pull (ι := Fin S.D) (L := fun _ => S.L) (S.isPullback_baseChange E) fun _ => S.isLB

end GlobalTheory.FieldChangeInter
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairGramInvCongruent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairGramInvCongruent
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKMid

variable {p : ℕ} [Fact p.Prime]

theorem psiR_tmul (G : HTGroup p) (v : InfinitePlace G.F) (r : ℝ) (c : G.C) :
    G.psiR v (r ⊗ₜ c) = r • G.psi v c := by
  rw [Algebra.smul_def]
  first
    | (unfold HTGroup.psiR; erw [Algebra.TensorProduct.lift_tmul]; rfl)
    | exact Algebra.TensorProduct.lift_tmul _ _ _ r c

theorem psiR_starT (G : HTGroup p) (v : InfinitePlace G.F) (x : ℝ ⊗[ℚ] G.C) :
    G.psiR v (starT G.star ℝ x).unop = (G.gram v)⁻¹ * (G.psiR v x)ᴴ * G.gram v := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r c =>
    rw [starT_tmul, psiR_tmul, psiR_tmul]
    rw [G.psi_star, Matrix.conjTranspose_smul, star_trivial, Matrix.mul_smul, Matrix.smul_mul]
  | add x y hx hy =>
    simp only [map_add (f := _), MulOpposite.unop_add, hx, hy, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]

theorem Pair.gram_psi_inv_congr : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (v : InfinitePlace G.F),
    ∃ Z : GL (Fin G.n) ℂ, (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) =
      (Z : Matrix (Fin G.n) (Fin G.n) ℂ)ᴴ * G.gram v * (Z : Matrix (Fin G.n) (Fin G.n) ℂ) := by
  intro p _ G P v
  obtain ⟨z, hz⟩ := P.trivR
  refine ⟨Units.map (G.psiR v).toMonoidHom z, ?_⟩
  set Zm : Matrix (Fin G.n) (Fin G.n) ℂ := G.psiR v (z : ℝ ⊗[ℚ] G.C) with hZm
  change G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C) = Zmᴴ * G.gram v * Zm
  have hb : G.psiR v (inC G ℝ (P.β : G.C)) = G.psi v (P.β : G.C) := by
    change G.psiR v ((1 : ℝ) ⊗ₜ (P.β : G.C)) = _
    rw [psiR_tmul, one_smul]
  have h1 := congrArg (G.psiR v) hz
  rw [map_mul, map_mul, psiR_starT, hb] at h1
  simp only [Units.val_one, map_one] at h1
  rw [← hZm] at h1
  have hg : IsUnit (G.gram v).det := isUnit_iff_ne_zero.2 (G.gram_det v)
  set M := G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)
  have hMb : M * G.psi v (P.β : G.C) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have h2 : G.psi v (P.β : G.C) * ((G.gram v)⁻¹ * Zmᴴ * G.gram v * Zm) = 1 := by
    have := mul_eq_one_comm.1 (by simpa [Matrix.mul_assoc] using h1 :
      Zm * (G.psi v (P.β : G.C) * ((G.gram v)⁻¹ * Zmᴴ * G.gram v)) = 1)
    simpa [Matrix.mul_assoc] using this
  have h3 : M = (G.gram v)⁻¹ * Zmᴴ * G.gram v * Zm := by
    calc M = M * (G.psi v (P.β : G.C) * ((G.gram v)⁻¹ * Zmᴴ * G.gram v * Zm)) := by rw [h2, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hMb, Matrix.one_mul]
  rw [h3]
  simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hg, Matrix.one_mul]

end GlobalTheory.LKMid
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairGramInvCongruentStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.similitudePair_gram_inv_congruent : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (v : InfinitePlace G.F), ∃ Z : GL (Fin G.n) ℂ, (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) = (Z : Matrix (Fin G.n) (Fin G.n) ℂ)ᴴ * G.gram v * (Z : Matrix (Fin G.n) (Fin G.n) ℂ) := by
  first | exact @GlobalTheory.LKMid.Pair.gram_psi_inv_congr | exact GlobalTheory.LKMid.Pair.gram_psi_inv_congr | (intros; apply GlobalTheory.LKMid.Pair.gram_psi_inv_congr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualCHLat
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.MovedLat

open GlobalTheory.AdelicLatMove GlobalTheory.AdLat Formalism.IndefR

variable {D : D7}

theorem hat_hLat (V : HSp D) (g : Bridge.Gf V) :
    (hat D.host.F (Bridge.hLat V g : Set (Fin V.rank → D.host.E)) : Set (Fin V.rank → RA D.host.F D.host.E)) =
      g.1.1.mulVec '' (hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E))) := by
  obtain ⟨-, -, hfg, hsp, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  obtain ⟨Λ, hΛ, -, -, h⟩ := exists_lattice_latOf D.host.F D.host.E V.rank (GlobalTheory.Member.latC V) g.1 hfg hsp
  rw [GlobalTheory.RepsCompare.coe_hLat, ← hΛ, h]

theorem hLat_one (V : HSp D) : Bridge.hLat V 1 = GlobalTheory.Member.latC V := by
  obtain ⟨-, -, hfg, hsp, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  apply SetLike.coe_injective
  rw [GlobalTheory.RepsCompare.coe_hLat]
  ext x
  rw [SetLike.mem_coe, ← (hat_rational_points_and_approx D.host.F D.host.E _ _ hfg hsp).1]
  simp [GlobalTheory.AdLat.latOf]

theorem isSelfDualC_hLat (V : HSp D) (g : Bridge.Gf V) : IsSelfDualC V (Bridge.hLat V g) := by
  refine ⟨GlobalTheory.RepsCompare.isLattice_hLat V g, fun v => ?_⟩
  obtain ⟨-, -, hfg, hsp, c2, -, -, gh, gd, -, hsd⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have key := latOf_selfDual D.host.F D.host.E V.rank (GlobalTheory.Member.latC V) (GlobalTheory.Member.cF D) V.gramᵀ 1 g.1 hfg hsp c2 gh gd
    one_ne_zero hsd (GlobalTheory.RepsCompare.isUnA_gf V g)
  rw [← SetLike.mem_coe, GlobalTheory.RepsCompare.coe_hLat, ← key, ← GlobalTheory.RepsCompare.coe_hLat]
  refine forall_congr' fun y => imp_congr_right fun _ => ?_
  have e : ∑ i, ∑ j, star (y i) * V.gram i j * v j = ∑ a, ∑ b, v a * V.gramᵀ a b * GlobalTheory.Member.cF D (y b) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    change star (y b) * V.gram b a * v a = v a * V.gram b a * star (y b)
    ring
  rw [e, FractionalIdeal.mem_one_iff]

theorem mulVec_mem_hatL (V : HSp D) (g : GA D V) (Λ Λ' : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (H : ∀ z ∈ hat D.host.F (Λ : Set (Fin V.rank → D.host.E)),
      (finHom V g).1 *ᵥ z ∈ hat D.host.F (Λ' : Set (Fin V.rank → D.host.E)))
    (x : Fin V.rank → EAf D) (hx : x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) :
    (Formalism.L2.Theta.mt V g).map (toEAf D) *ᵥ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ' := by
  have h := GlobalTheory.PrincInLevel.swap_mem_hatL Λ' _ (H _ (GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ x hx))
  convert h using 1
  ext i
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul, toEAf, finPart,
    finHom, Formalism.L2.Theta.mt, Formalism.UG.bc]

theorem actO_mem (S T : HSp D) (g : GA D S) (h : GA D T)
    (ΛS ΛS' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT ΛT' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hS : ∀ z ∈ hat D.host.F (ΛS : Set (Fin S.rank → D.host.E)),
      (finHom S g).1 *ᵥ z ∈ hat D.host.F (ΛS' : Set (Fin S.rank → D.host.E)))
    (hT : ∀ z ∈ hat D.host.F (ΛT : Set (Fin T.rank → D.host.E)),
      (finHom T h).1 *ᵥ z ∈ hat D.host.F (ΛT' : Set (Fin T.rank → D.host.E)))
    (u : WO S T)
    (hu : u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) :
    actO S T g h u ∈
      latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True := by
  induction hu using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hu
    have e := rankOne_pure S T a s t 1 α
    rw [mul_one] at e
    rw [← e, actO_rankOne]
    exact rankOne_mem_latO S T ΛS' ΛT' a ha _
      (mulVec_mem_hatL S g ΛS ΛS' hS _ (pure_mem_hatL ΛS 1 (one_mem _) s hs)) _
      (mulVec_mem_hatL T h ΛT ΛT' hT _ (pure_mem_hatL ΛT α hα t ht))
  | zero => simp only [actO, Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add y z _ _ hy hz => simp only [actO, Matrix.mul_add, Matrix.add_mul] at hy hz ⊢; exact add_mem hy hz
  | neg y _ hy => simp only [actO, Matrix.mul_neg, Matrix.neg_mul] at hy ⊢; exact neg_mem hy

theorem fwd (V : HSp D) (g : GA D V) : ∀ z ∈ hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)),
    (finHom V g).1 *ᵥ z ∈ hat D.host.F (Bridge.hLat V (FWT.fin V g) : Set (Fin V.rank → D.host.E)) := by
  intro z hz
  rw [← SetLike.mem_coe, hat_hLat]
  exact ⟨z, hz, rfl⟩

theorem bwd (V : HSp D) (g : GA D V) :
    ∀ z ∈ hat D.host.F (Bridge.hLat V (FWT.fin V g) : Set (Fin V.rank → D.host.E)),
    (finHom V g⁻¹).1 *ᵥ z ∈ hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := by
  intro z hz
  rw [← SetLike.mem_coe, hat_hLat] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  change (finHom V g⁻¹).1 *ᵥ ((finHom V g).1 *ᵥ y) ∈ _
  rw [Matrix.mulVec_mulVec, map_inv, Units.inv_mul, Matrix.one_mulVec]
  exact hy

theorem latG_eq (W : HSp D) (k : GA D W) : Formalism.L2.Pj.latG W k = Submodule.span (𝓞 D.host.E)
    {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v ∈ Bridge.hLat W (FWT.fin W k), w = a • v} := by
  have key : ∀ v, Formalism.L2.Pj.finVec W v ∈ Formalism.L2.Pj.gLat W k ↔ v ∈ Bridge.hLat W (FWT.fin W k) := by
    intro v
    rw [← SetLike.mem_coe, GlobalTheory.RepsCompare.coe_hLat, Formalism.L2.Pj.gLat, (GlobalTheory.Member.latHat_eq_hat_and_gram D W).1]
    exact Iff.rfl
  unfold Formalism.L2.Pj.latG
  simp only [key]

theorem moved_lattices : ∀ (D : D7) (V W : HSp D) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)), (ΛV : Set (Fin V.rank → D.host.E)) = L0c D V → (ΛW : Set (Fin W.rank → D.host.E)) = L0c D W → IsSelfDualC V ΛV → IsSelfDualC W ΛW → ∀ (h : GA D V) (k : GA D W), IsSelfDualC V (Formalism.IndefR.Bridge.hLat V (Formalism.IndefR.FWT.fin V h)) ∧ IsSelfDualC W (Formalism.IndefR.Bridge.hLat W (Formalism.IndefR.FWT.fin W k)) ∧ (∀ u : WO V W, u ∈ (latO V W (Formalism.IndefR.Bridge.hLat V (Formalism.IndefR.FWT.fin V h) : Set (Fin V.rank → D.host.E)) (Formalism.IndefR.Bridge.hLat W (Formalism.IndefR.FWT.fin W k) : Set (Fin W.rank → D.host.E)) fun _ => True) ↔ ∃ u₀ ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True), u = actO V W h k u₀) ∧ Formalism.L2.Pj.latG W k = Submodule.span (𝓞 D.host.E) {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v ∈ Formalism.IndefR.Bridge.hLat W (Formalism.IndefR.FWT.fin W k), w = a • v} ∧ Formalism.IndefR.Bridge.hLat V 1 = ΛV ∧ Formalism.IndefR.Bridge.hLat W 1 = ΛW := by
  intro D V W ΛV ΛW hV hW _ _ h k
  obtain rfl : ΛV = GlobalTheory.Member.latC V := SetLike.coe_injective (hV.trans (GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq V).symm)
  obtain rfl : ΛW = GlobalTheory.Member.latC W := SetLike.coe_injective (hW.trans (GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq W).symm)
  refine ⟨isSelfDualC_hLat V _, isSelfDualC_hLat W _, fun u => ⟨fun hu => ?_, ?_⟩, latG_eq W k, hLat_one V, hLat_one W⟩
  · exact ⟨_, actO_mem V W h⁻¹ k⁻¹ _ _ _ _ (bwd V h) (bwd W k) u hu, (actO_actO_inv V W h k u).symm⟩
  · rintro ⟨u₀, hu, rfl⟩
    exact actO_mem V W h k _ _ _ _ (fwd V h) (fwd W k) u₀ hu

end GlobalTheory.MovedLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntBTmulBasis
noncomputable section

open IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.AdicSpan

def IsIntB (v : HeightOneSpectrum ℤ) {M : Type} [AddCommGroup M] [Module ℚ M] {κ : Type} (b : Module.Basis κ ℚ M)
    (y : v.adicCompletion ℚ ⊗[ℚ] M) : Prop :=
  ∀ i, (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).repr y i ∈ v.adicCompletionIntegers ℚ

theorem isIntB_zero (v : HeightOneSpectrum ℤ) {M : Type} [AddCommGroup M] [Module ℚ M] {κ : Type}
    (b : Module.Basis κ ℚ M) : IsIntB v b 0 := fun i => by simp [zero_mem]

theorem isIntB_tmul_basis (v : HeightOneSpectrum ℤ) {M : Type} [AddCommGroup M] [Module ℚ M] {κ : Type}
    (b : Module.Basis κ ℚ M) (j : κ) : IsIntB v b ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] b j) := fun i => by
  classical
  rw [Algebra.TensorProduct.basis_repr_tmul, b.repr_self, Finsupp.smul_apply, Finsupp.mapRange_apply,
    Finsupp.single_apply]
  split_ifs <;> simp [zero_mem, one_mem]

end GlobalTheory.AdicSpan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffOfSec
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

noncomputable section

namespace GlobalTheory.EffBound

open GlobalTheory.CechPic

def Eff {X : Scheme.{0}} (c : Pic X) : Prop :=
  ∃ (N : LB X) (hN : N.IsLB), cls N hN = c ∧ ∃ (σ : LB.Sec N) (j : N.ι), σ.f j ≠ 0

theorem eff_of_sec {X : Scheme.{0}} (N : LB X) (hN : N.IsLB) (σ : LB.Sec N) (j : N.ι) (h : σ.f j ≠ 0) :
    Eff (cls N hN) :=
  ⟨N, hN, rfl, σ, j, h⟩

theorem cls_pw {X : Scheme.{0}} {H : LB X} (hH : H.IsLB) (t : ℤ) :
    cls (pw H t) (isLB_pw hH t) = t • cls H hH := by
  have hL := LB.isLB_linComb hH (fun _ : PUnit => 𝟙 X) (fun _ => t)
  have e : LBIso (LB.LinComb H (fun _ : PUnit => 𝟙 X) (fun _ => t)) (pw H t) :=
    iso_of_chart (isLB_pw hH t)
      { idx := fun j => j PUnit.unit
        le := fun j y hy => Set.mem_iInter.1 hy PUnit.unit
        g := fun y j j' hj hj' => by
          refine (gm_linComb H (fun _ : PUnit => 𝟙 X) (fun _ => t) (𝟙 X) y j j' hj hj').trans ?_
          rw [Fintype.prod_unique]
          change _ = gm (𝟙 X) y _ (H.g (j PUnit.unit) (j' PUnit.unit) ^ t)
          rw [map_zpow, Category.comp_id] }
  rw [← (cls_eq_iff hL (isLB_pw hH t)).2 e, cls_linComb hH, Fintype.sum_unique, pull_id]

end GlobalTheory.EffBound
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepMemSm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmoothStable

theorem rep_mem_sm : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau), ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w ∈ M.sm τ, M.rep τ g w ∈ M.sm τ := by
  intro D V S M τ g hg w hw
  have hσ : IsURepOn (UJset (M.ε τ)) (M.σ τ) := (M.ds τ).2.2.1
  have e : M.sm τ = GlobalTheory.SmVec.smSub (gramAt D V τ) (M.rep τ) :=
    Submodule.span_eq (GlobalTheory.SmVec.smSub (gramAt D V τ) (M.rep τ))
  rw [e] at hw ⊢
  exact GlobalTheory.SmVec.rep_mem (GlobalTheory.SmVec.gram_unit (M.fr_unit τ) (M.fr_gram τ))
    (GlobalTheory.SmVec.isURepOn_trRep (M.fr_unit τ) (M.fr_gram τ) hσ) hw hg

end GlobalTheory.SmoothStable
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsAmpleTensorAmplePowProjective
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem IsAmpleLB.eventually_isGenerated_tens_lbPow {X : Scheme.{0}} {A N : LB X} (hA : IsAmpleLB A)
    (hN : N.IsLB) : ∀ᶠ n : ℕ in atTop, IsGenerated (tens N (lbPow A n)) := by
  have := isFiniteQC_twist (F := GlobalTheory.structureModule X) hN
  refine (hA.eventually_isGloballyGenerated_twist (twist (GlobalTheory.structureModule X) N)).mono
    fun n hn => ?_
  have hP := isLB_lbPow hA.isLB n
  have hT := isLB_tens hN hP
  obtain ⟨e⟩ := nonempty_twist_twist_iso_of_cls_eq (GlobalTheory.structureModule X) hN hP hT
    (cls_tens hN hP hT)
  exact (isGloballyGenerated_toMod_iff hT).1 ((hn.of_epi e.hom).of_epi (unitTwistIso _).hom)

theorem IsAmpleLB.eventually_isAmpleLB_tens_lbPow_succ {X : Scheme.{0}} {A N : LB X}
    (hA : IsAmpleLB A) (hN : N.IsLB) : ∀ᶠ n : ℕ in atTop, IsAmpleLB (tens N (lbPow A (n + 1))) := by
  refine (hA.eventually_isGenerated_tens_lbPow hN).mono fun n hn => ?_
  have hP := isLB_lbPow hA.isLB n
  have hP' := isLB_lbPow hA.isLB (n + 1)
  have hT := isLB_tens hN hP'
  have hD := LB.isLB_div hT hA.isLB
  refine hA.tensor_isGenerated hn hT ((cls_eq_zero_iff (LB.isLB_div hD hn.isLB)).1 ?_)
  rw [cls_div hD hn.isLB, cls_div hT hA.isLB, cls_tens hN hP', cls_tens hN hP,
    cls_lbPow hA.isLB, cls_lbPow hA.isLB, succ_nsmul]
  abel

theorem exists_isAmpleLB_tens_lbPow : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ A N : LB X, IsAmpleLB A → N.IsLB → ∃ c : ℕ, 1 ≤ c ∧ IsAmpleLB (tens N (lbPow A c)) := by
  intro k _ _ X _ _ A N hA hN
  obtain ⟨n, hn⟩ := (hA.eventually_isAmpleLB_tens_lbPow_succ hN).exists
  exact ⟨n + 1, Nat.succ_pos n, hn⟩

end GlobalTheory
end
end
