module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePlaceComponentAdeleNormEqLocalNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentCoprimeAtGoodPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormBlockEmbLeftInvariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtZeroHeisenbergCMRealLineTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceSzNonneg
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize

namespace GlobalTheory.ArchTens

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def placeSz {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (w : Pl D.host.E) : ℝ :=
  (cosExp G w : ℝ) * Real.log (Ideal.absNorm (w.under (𝓞 D.host.F)).asIdeal)

theorem placeSz_nonneg {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (w : Pl D.host.E) :
    0 ≤ placeSz G w :=
  mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)

section Claims

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (C : ℝ)

def DatAt : Prop := ∀ (σ : D.what₂.LL →+* ℂ) Φ, ∀ β ∈ ch.S.supp A.μ0 Φ, ∀ (w : locPl ch.G A.μ0) x y,
  AbsLe σ ((ch.S.term A.μ0 Φ β w).datum (ch.S.colAt A.μ0 w x) (ch.S.rowAt A.μ0 w y))
    (C * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * placeSz ch.G w)

def FlipAt : Prop := ∀ (σ : D.what₂.LL →+* ℂ) Φ (w : locPl ch.G A.μ0) z,
  AbsLe σ (Tflip ch.W ch.S.B A.μ0 Φ w z) (C * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * placeSz ch.G w)

def CoefAt : Prop := ∀ Φ, ∀ β ∈ ch.S.supp A.μ0 Φ, ∀ w : locPl ch.G A.μ0,
  |((ch.S.term A.μ0 Φ β w).coef : ℝ)| ≤ Real.exp (C * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * placeSz ch.G w)

end Claims

section Abs

variable {D : D7}

theorem absLe_mono {σ : D.what₂.LL →+* ℂ} {z : ℂ} {B B' : ℝ} (h : AbsLe σ z B) (hB : B ≤ B') : AbsLe σ z B' :=
  let ⟨y, e, h⟩ := h
  ⟨y, e, h.trans (Real.exp_le_exp.2 hB)⟩

theorem absLe_mul {σ : D.what₂.LL →+* ℂ} {z z' : ℂ} {B B' : ℝ} (h : AbsLe σ z B) (h' : AbsLe σ z' B') :
    AbsLe σ (z * z') (B + B') := by
  obtain ⟨y, e, hy⟩ := h
  obtain ⟨y', e', hy'⟩ := h'
  refine ⟨y * y', by rw [map_mul, e, e'], ?_⟩
  rw [map_mul, norm_mul, Real.exp_add]
  exact mul_le_mul hy hy' (norm_nonneg _) (Real.exp_pos _).le

theorem absLe_prod {ι : Type} (s : Finset ι) {σ : D.what₂.LL →+* ℂ} (z : ι → ℂ) (B : ι → ℝ) (h : ∀ i ∈ s, AbsLe σ (z i) (B i)) :
    AbsLe σ (∏ i ∈ s, z i) (∑ i ∈ s, B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, map_one _, by simp⟩
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact absLe_mul (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem absLe_rat (σ : D.what₂.LL →+* ℂ) (q : ℚ) {B : ℝ} (h : |(q : ℝ)| ≤ Real.exp B) : AbsLe σ (q : ℂ) B := by
  refine ⟨(q : D.what₂.LL), map_ratCast _ _, ?_⟩
  rw [map_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
  exact h

end Abs

theorem sum_placeSz_le {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) :
    ∑ w : locPl G t, placeSz G w ≤ sig G := by
  classical
  rw [Finset.sum_coe_sort (locPl G t) (placeSz G)]
  have h1 : ∑ w ∈ locPl G t, placeSz G w = ∑ w ∈ G.pl.W0, placeSz G w := by
    refine (Finset.sum_subset (Finset.subset_union_left) fun w _ hw => ?_).symm
    simp [placeSz, (depthAt_of_notMem G hw).1]
  rw [h1, sig]
  unfold Places.W0
  refine (Finset.sum_image_le_of_nonneg fun w _ => placeSz_nonneg G w).trans (le_of_eq (Finset.sum_congr rfl fun v hv => ?_))
  rw [placeSz, (depthAt_w G hv).1, G.pl.under_w hv]

end GlobalTheory.ArchTens

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParsevalFundamentalDomainTheta
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParsevalFundamentalDomainTheta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaUnfold

open GlobalTheory.WeilM
open scoped Classical

theorem continuous_infToMixed (F : Type) [Field F] [NumberField F] :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  change Continuous fun x : InfiniteAdeleRing F =>
    ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
     (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

theorem adele_nontrivial (F : Type) [Field F] [NumberField F] : Nontrivial (AdeleRing (𝓞 F) F) :=
  inferInstanceAs (Nontrivial (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

theorem schA_continuous (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]
    {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ schA F κ) : Continuous Φ := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    refine (f.continuous.comp ?_).mul (hg.1.continuous.comp ?_)
    · exact continuous_pi fun i =>
        (continuous_infToMixed F).comp (continuous_fst.comp (continuous_apply i))
    · exact continuous_pi fun i => continuous_snd.comp (continuous_apply i)
  | zero => exact continuous_const
  | add Φ Ψ _ _ h1 h2 => exact h1.add h2
  | smul c Φ _ h => exact continuous_const.mul h

def ratEquiv (F : Type) [Field F] [NumberField F] (κ : Type) : (κ → F) ≃ GlobalTheory.ThetaParseval.ratVec F κ :=
  Equiv.ofBijective
    (fun ξ => ⟨fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i), (GlobalTheory.ThetaParseval.mem_ratVec_iff _).2 ⟨ξ, rfl⟩⟩)
    ⟨fun a b h => funext fun i => (haveI := adele_nontrivial F; (algebraMap F (AdeleRing (𝓞 F) F)).injective) (congrFun (congrArg Subtype.val h) i),
     fun y => by
      obtain ⟨ξ, hξ⟩ := (GlobalTheory.ThetaParseval.mem_ratVec_iff y.1).1 y.2
      exact ⟨ξ, Subtype.ext hξ.symm⟩⟩

theorem unfold : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (𝓕₁ : Set (κ → AF F)), @IsAddFundamentalDomain (GlobalTheory.ThetaParseval.ratVec F κ) _ _ _ (borel _) 𝓕₁ μ → ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
      ∫⁻ x in 𝓕₁, ∑' ξ : κ → F, ‖Φ ((fun i => algebraMap F (AF F) (ξ i)) + x)‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  intro F _ _ κ _ μ hμ 𝓕₁ h𝓕 Φ hΦ
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  have hc := schA_continuous F hΦ
  haveI : Countable F := by
    have b := Module.finBasis ℚ F
    exact Countable.of_equiv _ b.equivFun.toEquiv.symm
  haveI : Countable (GlobalTheory.ThetaParseval.ratVec F κ) := Countable.of_equiv _ (ratEquiv F κ)
  have hm : ∀ c : κ → AF F, Measurable fun x : κ → AF F => ‖Φ (c + x)‖ₑ ^ 2 := fun c =>
    ((hc.comp (continuous_const.add continuous_id)).measurable.enorm).pow_const 2
  rw [lintegral_tsum fun ξ => (hm _).aemeasurable, h𝓕.lintegral_eq_tsum' (fun x => ‖Φ x‖ₑ ^ 2)]
  rw [← ((ratEquiv F κ).trans (Equiv.neg _)).tsum_eq]
  refine tsum_congr fun ξ => ?_
  simp only [Equiv.trans_apply, Equiv.neg_apply, neg_neg, AddSubgroup.vadd_def, vadd_eq_add]
  rfl
end GlobalTheory.ThetaUnfold
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParsevalFundamentalDomainThetaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parseval_fundamental_domain_theta : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (𝓕₁ : Set (κ → AF F)), @IsAddFundamentalDomain (GlobalTheory.ThetaParseval.ratVec F κ) _ _ _ (borel _) 𝓕₁ μ → ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
      ∫⁻ x in 𝓕₁, ∑' ξ : κ → F, ‖Φ ((fun i => algebraMap F (AF F) (ξ i)) + x)‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.ThetaUnfold.unfold | exact GlobalTheory.ThetaUnfold.unfold | (intros; apply GlobalTheory.ThetaUnfold.unfold <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeInvariantVector
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeInvariantVector
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

noncomputable section
namespace GlobalTheory.SelfDualFirstProjAny

theorem exists_valuation_eq (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℤ) :
    ∃ a : v.adicCompletion F, Valued.v a = WithZero.exp n := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  refine ⟨(π : v.adicCompletion F) ^ (-n), ?_⟩
  rw [map_zpow₀, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  simp [← WithZero.exp_zsmul]

theorem exists_pair_of_annihilator_any : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ] (ψ : AddChar (Fv F v) ℂ), Continuous ψ → (∀ t, ‖ψ t‖ = 1) → ψ ≠ 1 →
    ∀ (Λ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) (c : Fv F v), c ≠ 0 →
    (∀ w, w ∈ Λ ↔ ∀ l ∈ Λ, ψ (w.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ w.2) = 1) →
    (∀ l ∈ Λ, ∀ i, c * l.1 i ∈ v.adicCompletionIntegers F ∧ c * l.2 i ∈ v.adicCompletionIntegers F) →
    ∀ η : κ → Fv F v, (∀ b : κ → Fv F v, ((0 : κ → Fv F v), b) ∈ Λ → ψ (η ⬝ᵥ b) = 1) → ∃ y, (η, y) ∈ Λ := by
  intro F _ _ v κ _ ψ hcont hnorm hne Λ c hc hself hbd η hη
  classical
  have hne' : ∃ t, ψ t ≠ 1 := by
    by_contra h
    push_neg at h
    exact hne (by ext t; simpa using h t)
  obtain ⟨n, hn⟩ := GlobalTheory.CharConductor.exists_conductor_exponent F v ψ hcont hnorm hne'
  obtain ⟨a, ha⟩ := exists_valuation_eq F v n
  have ha0 : a ≠ 0 := by
    intro h; rw [h, map_zero] at ha; exact WithZero.zero_ne_coe ha
  let O := v.adicCompletionIntegers F
  let ψ₀ : AddChar (Fv F v) ℂ := ψ.mulShift a
  have hψ₀ : ∀ x, ψ₀ x = ψ (a * x) := fun x => rfl

  have hcond : ∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ₀ (x * y) = 1) ↔
      x ∈ v.adicCompletionIntegers F := by
    intro x
    have := hn (a * x)
    simp only [hψ₀, mul_assoc] at this ⊢
    rw [this, map_mul, ha, HeightOneSpectrum.mem_adicCompletionIntegers]
    have e : Valued.v x = WithZero.exp (-n) * (WithZero.exp n * Valued.v x) := by
      rw [← mul_assoc, ← WithZero.exp_add]; simp
    constructor
    · intro h
      rw [e]
      calc WithZero.exp (-n) * (WithZero.exp n * Valued.v x) ≤ WithZero.exp (-n) * WithZero.exp n := by gcongr
        _ = 1 := by rw [← WithZero.exp_add]; simp
    · intro h
      calc WithZero.exp n * Valued.v x ≤ WithZero.exp n * 1 := by gcongr
        _ = WithZero.exp n := mul_one _

  let f : ((κ → Fv F v) × (κ → Fv F v)) →+ ((κ → Fv F v) × (κ → Fv F v)) :=
    { toFun := fun w => (w.1, a • w.2)
      map_zero' := by simp
      map_add' := by intro x y; simp [smul_add] }
  let Λ₀ := Λ.comap f
  have hmem : ∀ w, w ∈ Λ₀ ↔ (w.1, a • w.2) ∈ Λ := fun w => Iff.rfl
  have hback : ∀ l : (κ → Fv F v) × (κ → Fv F v), (l.1, a • (a⁻¹ • l.2)) = l := by
    intro l; rw [smul_smul, mul_inv_cancel₀ ha0, one_smul]
  have hself₀ : ∀ w, w ∈ Λ₀ ↔ ∀ l ∈ Λ₀, ψ₀ (w.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ w.2) = 1 := by
    intro w
    rw [hmem, hself]
    constructor
    · intro h l hl
      have := h (l.1, a • l.2) hl
      rw [hψ₀]
      convert this using 2
      simp only [mul_sub, dotProduct_smul, smul_eq_mul]
    · intro h l hl
      have hl' : (l.1, a⁻¹ • l.2) ∈ Λ₀ := by rw [hmem]; simpa [hback l] using hl
      have := h _ hl'
      rw [hψ₀] at this
      convert this using 2
      simp only [mul_sub, dotProduct_smul, smul_eq_mul, smul_dotProduct]
      rw [← mul_assoc, mul_inv_cancel₀ ha0, one_mul]

  obtain ⟨c', hc', hbd₀⟩ : ∃ c' : Fv F v, c' ≠ 0 ∧ ∀ l ∈ Λ₀, ∀ i,
      c' * l.1 i ∈ v.adicCompletionIntegers F ∧ c' * l.2 i ∈ v.adicCompletionIntegers F := by
    rcases O.mem_or_inv_mem a with haO | haO
    · refine ⟨c * a, mul_ne_zero hc ha0, fun l hl i => ?_⟩
      have h := hbd _ ((hmem l).1 hl) i
      simp only [Pi.smul_apply, smul_eq_mul] at h
      refine ⟨?_, ?_⟩
      · have e : c * a * l.1 i = a * (c * l.1 i) := by ring
        rw [e]; exact O.toSubring.mul_mem haO h.1
      · have e : c * a * l.2 i = c * (a * l.2 i) := by ring
        rw [e]; exact h.2
    · refine ⟨c, hc, fun l hl i => ?_⟩
      have h := hbd _ ((hmem l).1 hl) i
      simp only [Pi.smul_apply, smul_eq_mul] at h
      refine ⟨h.1, ?_⟩
      have e : c * l.2 i = a⁻¹ * (c * (a * l.2 i)) := by
        rw [mul_left_comm, ← mul_assoc a⁻¹ a, inv_mul_cancel₀ ha0, one_mul]
      rw [e]; exact O.toSubring.mul_mem haO h.2
  have hη₀ : ∀ b : κ → Fv F v, ((0 : κ → Fv F v), b) ∈ Λ₀ → ψ₀ (η ⬝ᵥ b) = 1 := by
    intro b hb
    rw [hmem] at hb
    rw [hψ₀, ← smul_eq_mul, ← dotProduct_smul]
    exact hη _ hb
  obtain ⟨y, hy⟩ := GlobalTheory.SelfDualFirstProj.exists_pair_of_annihilator v ψ₀ Λ₀ c' hc' hcond hself₀ hbd₀ η hη₀
  exact ⟨a • y, (hmem _).1 hy⟩

end GlobalTheory.SelfDualFirstProjAny
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeInvariantVectorStatement
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.self_dual_lattice_invariant_vector : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ] (ψ : AddChar (Fv F v) ℂ), Continuous ψ → (∀ t, ‖ψ t‖ = 1) → ψ ≠ 1 →
    ∀ (Λ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) (c : Fv F v), c ≠ 0 →
    (∀ w, w ∈ Λ ↔ ∀ l ∈ Λ, ψ (w.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ w.2) = 1) →
    (∀ l ∈ Λ, ∀ i, c * l.1 i ∈ v.adicCompletionIntegers F ∧ c * l.2 i ∈ v.adicCompletionIntegers F) →
    ∀ η : κ → Fv F v, (∀ b : κ → Fv F v, ((0 : κ → Fv F v), b) ∈ Λ → ψ (η ⬝ᵥ b) = 1) → ∃ y, (η, y) ∈ Λ := by
  first | exact @GlobalTheory.SelfDualFirstProjAny.exists_pair_of_annihilator_any | exact GlobalTheory.SelfDualFirstProjAny.exists_pair_of_annihilator_any | (intros; apply GlobalTheory.SelfDualFirstProjAny.exists_pair_of_annihilator_any <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StdCharHalfSymplecticFormRealCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StdCharHalfSymplecticFormRealCoordinates
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

noncomputable section

namespace GlobalTheory.RealCharF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem infPartF_cAF (σ : E →ₐ[F] E) (z : AEF F E) :
    infPartF F E (cAF σ z) = sigR (Ainf F) σ (infPartF F E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem conj_theta_tmul_one [IsTotallyReal F] {τ : E →+* ℂ} {w : InfinitePlace F}
    (hw : w.embedding = τ.comp (algebraMap F E)) {θ : Ainf F ⊗[F] E →+* ℂ} (h : IsInfEmbF τ θ) (a : Ainf F) :
    starRingEnd ℂ (θ (a ⊗ₜ[F] (1 : E))) = θ (a ⊗ₜ[F] (1 : E)) := by
  have hv : w.IsReal := IsTotallyReal.isReal w
  rw [GlobalTheory.DualPairCompare.gen_inf_val τ w hw θ h a, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hv]
  exact Complex.conj_ofReal _

theorem theta_sigR {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {τ : E →+* ℂ} {w : InfinitePlace F}
    (hw : w.embedding = τ.comp (algebraMap F E)) {θ : Ainf F ⊗[F] E →+* ℂ} (h : IsInfEmbF τ θ)
    (y : Ainf F ⊗[F] E) : θ (sigR (Ainf F) σ y) = starRingEnd ℂ (θ y) := by
  haveI : IsTotallyReal F := hσ.1
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul a e =>
    have e1 : ∀ e' : E, a ⊗ₜ[F] e' = (a ⊗ₜ[F] (1 : E)) * ((1 : Ainf F) ⊗ₜ[F] e') := by
      intro e'; rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    show θ (a ⊗ₜ[F] σ e) = _
    rw [e1 (σ e), e1 e, map_mul, map_mul, map_mul, h.1, h.1, hσ.2.2.2, conj_theta_tmul_one hw h a]
    rfl

theorem theta_infPartF_incAF {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (h : IsInfEmbF τ θ) (e : E) :
    θ (infPartF F E (incAF F E e)) = τ e := by
  have : infPartF F E (incAF F E e) = (1 : Ainf F) ⊗ₜ[F] e := by
    show (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) ((1 : AF F) ⊗ₜ[F] e) = _
    rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  rw [this, h.1]

theorem theta_fstA_symplOHF {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {τ : E →+* ℂ} {w : InfinitePlace F}
    (hw : w.embedding = τ.comp (algebraMap F E)) {θ : Ainf F ⊗[F] E →+* ℂ} (h : IsInfEmbF τ θ)
    {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (x y : WOF F E nS nT) :
    θ (fstA F (symplOHF σ JS JT ξ₀ x y) ⊗ₜ[F] (1 : E)) =
      ((τ ξ₀ * θ (infPartF F E (hOF σ JS JT x y))).re : ℂ) := by
  set z := incAF F E ξ₀ * hOF σ JS JT x y with hz
  have h1 : fstA F (symplOHF σ JS JT ξ₀ x y) =
      algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E) (infPartF F E z) := by
    unfold symplOHF symplOF
    rw [map_mul, AlgHom.commutes, GlobalTheory.HeisLineDiffF.map_trace_tens]
    rfl
  have h2 : ∀ c : Ainf F, c ⊗ₜ[F] (1 : E) = algebraMap (Ainf F) (Ainf F ⊗[F] E) c := by
    intro c
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  have h3 : θ (algebraMap (Ainf F) (Ainf F ⊗[F] E) (algebraMap F (Ainf F) (1 / 2))) = 1 / 2 := by
    rw [← IsScalarTower.algebraMap_apply]
    have : (θ.comp (algebraMap F (Ainf F ⊗[F] E))) (1 / 2) = 1 / 2 := by
      rw [map_div₀, map_one, map_ofNat]
    exact this
  have h4 : θ (infPartF F E z) = τ ξ₀ * θ (infPartF F E (hOF σ JS JT x y)) := by
    rw [hz, map_mul, map_mul, theta_infPartF_incAF h]
  rw [h1, h2, map_mul, map_mul, GlobalTheory.SelfDualLatticeCompare.trace_tensor (Ainf F) hσ, map_add (f := _),
    theta_sigR hσ hw h, h3, h4, Complex.add_conj]
  push_cast
  ring

theorem theta_hOF {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {tau : InfinitePlace F → (E →+* ℂ)}
    (hw : ∀ w, w.embedding = (tau w).comp (algebraMap F E)) {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)}
    (hθ : IsInfFamF tau θ) {ι : (InfinitePlace F → ℂ) →+ AEF F E} (hι : IsChartF θ ι)
    {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} (JT : Matrix (Fin nT) (Fin nT) E) (hJS : JS.det ≠ 0)
    (u v : IxF F nS nT → ℂ) (w : InfinitePlace F) :
    θ w (infPartF F E (hOF σ JS JT (iotaVF ι u) (iotaVF ι v))) =
      ((JS.map (tau w))⁻¹ * (cpt v w)ᴴ * JT.map (tau w) * cpt u w).trace := by
  rw [GlobalTheory.OrientedChar.map_inv_field _ _ hJS, GlobalTheory.OrientedChar.trace_four]
  unfold hOF
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, infPartF_cAF, theta_sigR hσ (hw w) (hθ w), theta_infPartF_incAF (hθ w),
    iotaVF, Matrix.of_apply, hι.comp, cpt, Matrix.map_apply]

theorem trace_HMF {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E)
    (tau : InfinitePlace F → (E →+* ℂ)) (u v : IxF F nS nT → ℂ) :
    star v ⬝ᵥ HMF JS JT ξ₀ tau *ᵥ u = ∑ w, ((2 * (tau w ξ₀).im : ℝ) : ℂ) *
      ((JS.map (tau w))⁻¹ * (cpt v w)ᴴ * JT.map (tau w) * cpt u w).trace := by
  rw [star_dotProduct_eq]
  refine Finset.sum_congr rfl fun w _ => ?_
  unfold HMF
  rw [cpt_blk, ← Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul]
  simp only [Matrix.mul_assoc]

theorem psi_symplOHF_iotaVF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ u v : IxF F nS nT → ℂ, B.ψ (symplOHF σ JS JT ξ₀ (iotaVF ι u) (iotaVF ι v)) =
        Complex.exp (Real.pi * Complex.I * ((star v ⬝ᵥ HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) *ᵥ u).im : ℂ)) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ θ hθ ι hι u v
  have hσ := hB.cm
  haveI : IsTotallyReal F := hσ.1
  have hψ := GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood F E σ B hB
  have hw : ∀ w : InfinitePlace F, w.embedding = (B.emb w).1.comp (algebraMap F E) := fun w => (B.emb w).2.symm
  set s := symplOHF σ JS JT ξ₀ (iotaVF ι u) (iotaVF ι v) with hs
  have hsnd : sndA F s = 0 :=
    GlobalTheory.HeisDerivCM.map_symplOHF_eq_zero (sndA F) σ JS JT ξ₀ _ _ (Or.inr (real_iotaVF hι v))
  have e1 : B.ψ s = psiInf F B.ψ (fstA F s) := by
    have hsplit : s = pairA F (fstA F s) 0 := Prod.ext rfl hsnd
    conv_lhs => rw [hsplit]
    rfl
  have hre : ∀ w : InfinitePlace F, ((B.emb w).1 ξ₀).re = 0 := by
    intro w
    have h1 := hσ.2.2.2 (B.emb w).1 ξ₀
    rw [hσξ, map_neg] at h1
    have h2 := congrArg Complex.re h1
    rw [Complex.neg_re, Complex.star_def, Complex.conj_re] at h2
    linarith
  rw [e1, hψ.2.2 θ hθ, trace_HMF]
  have e2 : ∑ w, θ w (fstA F s ⊗ₜ[F] (1 : E)) = ∑ w, ((((B.emb w).1 ξ₀) *
      ((JS.map (B.emb w).1)⁻¹ * (cpt v w)ᴴ * JT.map (B.emb w).1 * cpt u w).trace).re : ℂ) :=
    Finset.sum_congr rfl fun w _ => by
      rw [hs, theta_fstA_symplOHF hσ (hw w) (hθ w) JS JT ξ₀ (iotaVF ι u) (iotaVF ι v),
        theta_hOF hσ hw hθ hι JT hJS.2 u v]
  rw [e2]
  congr 1
  rw [Complex.im_sum]
  simp only [Complex.mul_re, hre, Complex.im_ofReal_mul, zero_mul, zero_sub]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  ring

end GlobalTheory.RealCharF
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StdCharHalfSymplecticFormRealCoordinatesStatement
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stdChar_half_symplecticForm_real_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ u v : IxF F nS nT → ℂ, B.ψ (symplOHF σ JS JT ξ₀ (iotaVF ι u) (iotaVF ι v)) =
        Complex.exp (Real.pi * Complex.I * ((star v ⬝ᵥ HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) *ᵥ u).im : ℂ)) := by
  first | exact @GlobalTheory.RealCharF.psi_symplOHF_iotaVF | exact GlobalTheory.RealCharF.psi_symplOHF_iotaVF | (intros; apply GlobalTheory.RealCharF.psi_symplOHF_iotaVF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjPlInvolutive
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat

namespace GlobalTheory.SumSize.OppConj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Coef

variable {ι : Type} [Fintype ι] {n : ℕ}

def mapF {K L : Type} [Field K] [Field L] (φ : K →+* L) (lam : ι → DomWeight n) (x : VV K lam) : VV L lam :=
  ⟨MvPolynomial.map φ x.1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV φ lam _ x.2⟩

theorem mapVV_mapF {K L : Type} [Field K] [Field L] (φ : K →+* L) (ψ : L →+* ℂ) (lam : ι → DomWeight n) (x : VV K lam) :
    GlobalTheory.CoefModel.mapVV ψ lam (mapF φ lam x) = GlobalTheory.CoefModel.mapVV (ψ.comp φ) lam x :=
  Subtype.ext (by
    change MvPolynomial.map ψ (MvPolynomial.map φ x.1) = MvPolynomial.map (ψ.comp φ) x.1
    rw [MvPolynomial.map_map])

theorem mapVV_mapVV {K : Type} [Field K] (φ : K →+* ℂ) (ψ : ℂ →+* ℂ) (lam : ι → DomWeight n) (x : VV K lam) :
    GlobalTheory.CoefModel.mapVV ψ lam (GlobalTheory.CoefModel.mapVV φ lam x) = GlobalTheory.CoefModel.mapVV (ψ.comp φ) lam x :=
  Subtype.ext (by
    change MvPolynomial.map ψ (MvPolynomial.map φ x.1) = MvPolynomial.map (ψ.comp φ) x.1
    rw [MvPolynomial.map_map])

theorem mapVV_id (lam : ι → DomWeight n) (v : VV ℂ lam) : GlobalTheory.CoefModel.mapVV (RingHom.id ℂ) lam v = v :=
  Subtype.ext (by
    change MvPolynomial.map (RingHom.id ℂ) v.1 = v.1
    rw [MvPolynomial.map_id])

theorem conj_comp_conj : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ :=
  RingHom.ext fun z => Complex.conj_conj z

theorem mapVV_conj_conj (lam : ι → DomWeight n) (v : VV ℂ lam) :
    GlobalTheory.CoefModel.mapVV (starRingEnd ℂ) lam (GlobalTheory.CoefModel.mapVV (starRingEnd ℂ) lam v) = v := by
  rw [mapVV_mapVV, conj_comp_conj, mapVV_id]

def conjMap {n' : ℕ} {lam : ι → DomWeight n} {lam' : ι → DomWeight n'} (K : VV ℂ lam →ₗ[ℂ] VV ℂ lam') (v : VV ℂ lam) : VV ℂ lam' :=
  GlobalTheory.CoefModel.mapVV (starRingEnd ℂ) lam' (K (GlobalTheory.CoefModel.mapVV (starRingEnd ℂ) lam v))

end Coef

section Places

variable (K : Type) [Field K] [NumberField K] [StarRing K]

def conjPl (q : InfinitePlace K) : InfinitePlace K := InfinitePlace.mk (q.embedding.comp (starRingEnd K))

variable {K}

theorem conjugate_comp (φ : K →+* ℂ) (f : K →+* K) :
    (ComplexEmbedding.conjugate φ).comp f = ComplexEmbedding.conjugate (φ.comp f) :=
  RingHom.ext fun x => by simp [ComplexEmbedding.conjugate_coe_eq]

theorem conjPl_mk (φ : K →+* ℂ) : conjPl K (InfinitePlace.mk φ) = InfinitePlace.mk (φ.comp (starRingEnd K)) := by
  unfold conjPl
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · rw [h]
  · rw [h, conjugate_comp, InfinitePlace.mk_conjugate_eq]

theorem star_comp_star : (starRingEnd K).comp (starRingEnd K) = RingHom.id K :=
  RingHom.ext fun x => by simp

theorem conjPl_conjPl (q : InfinitePlace K) : conjPl K (conjPl K q) = q := by
  change conjPl K (InfinitePlace.mk (q.embedding.comp (starRingEnd K))) = q
  rw [conjPl_mk, RingHom.comp_assoc, star_comp_star, RingHom.comp_id, InfinitePlace.mk_embedding]

theorem conjPl_involutive : Function.Involutive (conjPl K) := conjPl_conjPl

theorem meanInf_conjPl (g : InfinitePlace K → ℝ) : Formalism.PairingDivisionLocalBalance.meanInf K (fun q => g (conjPl K q)) = Formalism.PairingDivisionLocalBalance.meanInf K g := by
  unfold Formalism.PairingDivisionLocalBalance.meanInf
  congr 1
  exact Equiv.sum_comp (conjPl_involutive.toPerm _) g

end Places

section Nrm

variable {D : D7} {n : ℕ} (lam : D.what₂.Tau → DomWeight n)

theorem nrm_conj (v : VV ℂ lam) :
    nrm lam (fun _ => 1) (GlobalTheory.CoefModel.mapVV (starRingEnd ℂ) lam v) = nrm lam (fun _ => 1) v := by
  have h := GlobalTheory.CoefModel.pairK_mapVV (starRingEnd ℂ) lam (fun _ => rfl) (fun _ : D.what₂.Tau => (1 : Matrix (Fin n) (Fin n) ℂ)) v v
  simp only [Matrix.map_one _ (map_zero _) (map_one _)] at h
  simp only [nrm, h, Complex.conj_re]

theorem nrmLe_conj_iff (σ : D.what₂.LL →+* ℂ) (v : VV ℂ lam) (B : ℝ) :
    NrmLe lam ((starRingEnd ℂ).comp σ) v B ↔ NrmLe lam σ v B := by
  constructor
  · rintro ⟨u, hu, hB⟩
    refine ⟨u, hu, ?_⟩
    rwa [← mapVV_mapVV, nrm_conj] at hB
  · rintro ⟨u, hu, hB⟩
    refine ⟨u, hu, ?_⟩
    rwa [← mapVV_mapVV, nrm_conj]

theorem nrmLe_mk_iff (φ : D.what₂.LL →+* ℂ) (v : VV ℂ lam) (B : ℝ) :
    NrmLe lam (InfinitePlace.mk φ).embedding v B ↔ NrmLe lam φ v B := by
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · rw [h]
  · have e : ComplexEmbedding.conjugate φ = (starRingEnd ℂ).comp φ :=
      RingHom.ext fun x => by simp [ComplexEmbedding.conjugate_coe_eq]
    rw [h, e, nrmLe_conj_iff]

end Nrm

section Transfer

variable {D : D7} {n n' : ℕ} {lam : D.what₂.Tau → DomWeight n} {lam' : D.what₂.Tau → DomWeight n'}

theorem embLL_comp_star : D.what₂.embLL.comp (starRingEnd D.what₂.LL) = (starRingEnd ℂ).comp D.what₂.embLL :=
  RingHom.ext fun x => D.starLL_cx x

theorem nrmLe_of_conjMap (σ : D.what₂.LL →+* ℂ) (K : VV ℂ lam →ₗ[ℂ] VV ℂ lam') (c : ℝ)
    (h : ∀ B v, NrmLe lam (σ.comp (starRingEnd D.what₂.LL)) v B →
      NrmLe lam' (σ.comp (starRingEnd D.what₂.LL)) (conjMap K v) (c * B))
    (B : ℝ) (v : VV ℂ lam) (hv : NrmLe lam σ v B) : NrmLe lam' σ (K v) (c * B) := by
  obtain ⟨u, hu, hB⟩ := hv
  have h1 : NrmLe lam (σ.comp (starRingEnd D.what₂.LL)) (GlobalTheory.CoefModel.mapVV (starRingEnd ℂ) lam v) B := by
    refine ⟨mapF (starRingEnd D.what₂.LL) lam u, ?_, ?_⟩
    · rw [mapVV_mapF, embLL_comp_star, ← mapVV_mapVV, hu]
    · rwa [mapVV_mapF, RingHom.comp_assoc, star_comp_star, RingHom.comp_id]
  obtain ⟨u', hu', hB'⟩ := h B _ h1
  refine ⟨mapF (starRingEnd D.what₂.LL) lam' u', ?_, ?_⟩
  · rw [mapVV_mapF, embLL_comp_star, ← mapVV_mapVV, hu', conjMap, mapVV_conj_conj, mapVV_conj_conj]
  · rwa [mapVV_mapF]

end Transfer

section Std

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (C b : ℝ)

def PairStdAt : Prop := ∃ g : InfinitePlace D.what₂.LL → ℝ, Formalism.PairingDivisionLocalBalance.meanInf _ g ≤ aOne ch.G C b ∧
  ∀ (p : InfinitePlace D.what₂.LL) Φ β d, Occurs ch.S.toGridChoice A.μ0 Φ β d → ∀ (c : ch.S.Classes A.μ0 Φ β),
    (∀ (j : Fin D.R.m) B v, NrmLe _ p.embedding v B →
      NrmLe _ p.embedding (ch.S.Z.kkMap 1 (d.1 j) (ch.S.ptTop c j) (ch.S.ptTop c (j + 1)) v) (Real.exp (g p) * B)) ∧
    ∀ (i : Fin D.R.m) B v, NrmLe _ p.embedding v B →
      NrmLe _ p.embedding (conjMap (ch.S.Z.kkMap 1 (d.2 i) (ch.S.ptRow c i) (ch.S.ptRow c (i + 1))) v) (Real.exp (g p) * B)

theorem infRowAt_of (h : PairStdAt ch C b) : InfRowAt ch C b := by
  obtain ⟨g, hg, h⟩ := h
  refine ⟨fun p => g (conjPl _ p), by rwa [meanInf_conjPl], ?_⟩
  intro p Φ β d hO c i B v hv
  have key := (h (conjPl _ p) Φ β d hO c).2 i
  refine nrmLe_of_conjMap p.embedding _ _ (fun B' v' hv' => ?_) B v hv
  exact (nrmLe_mk_iff _ (p.embedding.comp (starRingEnd D.what₂.LL)) _ _).1
    (key B' v' ((nrmLe_mk_iff _ (p.embedding.comp (starRingEnd D.what₂.LL)) _ _).2 hv'))

end Std

def PairStdK : Prop := BigC fun _ ch C b => PairStdAt ch C b

theorem bigC_mono {Q Q' : ChQ} (h : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (F : Face D A) (ch : Choice R) (C b : ℝ),
    Q F ch C b → Q' F ch C b) : BigC Q → BigC Q' := by
  rintro ⟨CF0, h0⟩
  refine ⟨CF0, fun CF hCF => ?_⟩
  obtain ⟨C0, h1⟩ := h0 CF hCF
  refine ⟨C0, fun ε C hC => ?_⟩
  obtain ⟨x0, h2⟩ := h1 ε C hC
  exact ⟨x0, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch h3 h4 h5 =>
    h F ch C large₂.sc.b (h2 D large₂ he hx Γ Pl0 T A Ks R F hS ch h3 h4 h5)⟩

theorem infRowK_of (h : PairStdK) : InfRowK := bigC_mono (fun _ ch C b => infRowAt_of ch C b) h

end GlobalTheory.SumSize.OppConj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongApproximationSplitPlaceSkewHermitianUnitar
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongApproximationSplitPlaceSkewHermitianUnitar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.SplitApprox

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU.Supp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig M r s) :
    M.det ≠ 0 := by
  obtain ⟨hn, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hn)
  have key : (A.submatrix id e.symm)ᵀ * M * (A.submatrix id e.symm).map star =
      (Aᵀ * M * A.map star).submatrix e.symm e.symm := by
    ext i j; rfl
  have hd := congrArg Matrix.det key
  rw [Matrix.det_submatrix_equiv_self, hA, Matrix.det_mul, Matrix.det_mul] at hd
  intro h0
  rw [h0] at hd
  simp [Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg] at hd
  exact pow_ne_zero _ (by norm_num) hd.symm

theorem det_ne_zero_of_map {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (f : E →+* ℂ) (h : (J.map f).det ≠ 0) :
    J.det ≠ 0 := by
  intro h0
  apply h
  rw [show J.map f = f.mapMatrix J from rfl, ← RingHom.map_det, h0, map_zero]


omit [NumberField E] in
theorem cA_apply (y : AF F ⊗[F] E) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ y = sigR (AF F) σ y := by
  induction y using TensorProduct.inductionOn with
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]


omit [NumberField F] in
theorem isHermND_smul_transpose {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hs : ∀ i j, σ (J j i) = -J i j)
    (hd : J.det ≠ 0) {δ : E} (hδ : δ ≠ 0) (hσδ : σ δ = -δ) : IsHermND σ (δ • Jᵀ) := by
  refine ⟨fun i j => ?_, ?_⟩
  · simp only [Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul, map_mul, hσδ, hs j i]
    ring
  · rw [Matrix.det_smul, Matrix.det_transpose]
    exact mul_ne_zero (pow_ne_zero _ hδ) hd

theorem mem_UG_iff_mem_HR {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {δ : E} (hδ : δ ≠ 0)
    (g : GL (Fin n) (AF F ⊗[F] E)) :
    g ∈ GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F J) ↔ g ∈ HR (AF F) σ (δ • Jᵀ) := by
  set G : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := (g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) with hG
  set K := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F J with hK
  have hc : G.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) = G.map (sigR (AF F) σ) := by
    ext i j; exact cA_apply _
  have hJR : JR (AF F) (δ • Jᵀ) = inclR (F := F) (AF F) δ • Kᵀ := by
    ext i j; simp [JR, hK, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, map_mul]
  have hunit : inclR (F := F) (AF F) δ⁻¹ * inclR (F := F) (AF F) δ = 1 := by rw [← map_mul, inv_mul_cancel₀ hδ, map_one]
  show Gᵀ * K * G.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) = K ↔
    Formalism.UG.cT (sigR (AF F) σ) G * JR (AF F) (δ • Jᵀ) * G = JR (AF F) (δ • Jᵀ)
  rw [hc, hJR, Formalism.UG.cT]
  constructor
  · intro h
    have h1 := congrArg Matrix.transpose h
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc] at h1
    rw [Matrix.mul_smul, Matrix.smul_mul, h1]
  · intro h
    have h' : (G.map (sigR (AF F) σ))ᵀ * Kᵀ * G = Kᵀ := by
      have h1 := congrArg (fun M => inclR (F := F) (AF F) δ⁻¹ • M) h
      simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, hunit, one_smul] at h1
      exact h1
    have h1 := congrArg Matrix.transpose h'
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose,
      ← Matrix.mul_assoc] at h1
    exact h1

def toUA {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {δ : E} (hδ : δ ≠ 0) :
    HA (AF F) σ (δ • Jᵀ) →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ J where
  toFun g := ⟨HA.mat (AF F) σ _ g, (mem_UG_iff_mem_HR J hδ _).2 (show HR (AF F) σ (δ • Jᵀ) from g).2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem continuous_toUA {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {δ : E} (hδ : δ ≠ 0) :
    Continuous (toUA (σ := σ) J hδ) :=
  Continuous.subtype_mk (continuous_subtype_val (p := fun g => g ∈ HR (AF F) σ (δ • Jᵀ))) _

theorem isPlacesIdem_placeIdem (v : HeightOneSpectrum (𝓞 F)) : GlobalTheory.Published.IsPlacesIdem ∅ {v} (placeIdem v) :=
  ⟨fun w hw => absurd hw (Finset.notMem_empty w), fun _ _ => rfl,
    fun u hu => by rw [Finset.mem_singleton.1 hu]; exact GlobalTheory.AdelicU.evalV_singleFin_self v 1,
    fun u hu => GlobalTheory.AdelicU.evalV_singleFin_ne (fun h => hu (Finset.mem_singleton.2 h)) 1⟩

theorem mul_placeIdem {v : HeightOneSpectrum (𝓞 F)} {u : AF F} (hu : GlobalTheory.AdelicU.evFin F v u = 0) :
    u * placeIdem v = 0 := by
  have h2 : sndA F u * GlobalTheory.AdelicU.singleFin v 1 = 0 := by
    apply RestrictedProduct.ext
    intro w
    change evalV F w (sndA F u * GlobalTheory.AdelicU.singleFin v 1) = 0
    rw [map_mul]
    by_cases e : w = v
    · subst e; rw [show evalV F w (sndA F u) = 0 from hu, zero_mul]
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne e, mul_zero]
  exact Prod.ext (mul_zero _) h2

omit [NumberField E] in
theorem singleTens_mul_self {v : HeightOneSpectrum (𝓞 F)} (y : Fv F v ⊗[F] E) :
    singleTens E v y * singleTens E v y = singleTens E v (y * y) := (map_mul _ _ _).symm

theorem splitIdemAd_mul_self (h : IsCMExt F E σ) {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v) :
    splitIdemAd h τ * splitIdemAd h τ = splitIdemAd h τ := by
  rw [splitIdemAd, singleTens_mul_self, GlobalTheory.AdelicU.splitIdem_mul_self]

theorem splitIdemAd_mul_sigR (h : IsCMExt F E σ) {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v) :
    splitIdemAd h τ * sigR (AF F) σ (splitIdemAd h τ) = 0 := by
  rw [splitIdemAd, sigR_singleTens, GlobalTheory.AdelicU.sigR_splitIdem, ← map_mul, mul_sub, mul_one,
    GlobalTheory.AdelicU.splitIdem_mul_self, sub_self, map_zero]

theorem splitIdemAd_add_sigR (h : IsCMExt F E σ) {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v) :
    splitIdemAd h τ + sigR (AF F) σ (splitIdemAd h τ) = algebraMap (AF F) (AF F ⊗[F] E) (placeIdem v) := by
  rw [splitIdemAd, sigR_singleTens, GlobalTheory.AdelicU.sigR_splitIdem, ← map_add (f := _), add_sub_cancel, singleTens_one]

theorem strongApprox_split : GlobalTheory.Published.StrongApproxSU → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : Chars F E) (om : Rep σ Γ.V Γ.W) (om' : Rep σ Γ.V' Γ.W), IsTriple Bs Γ X om om' →
    ∀ (v : Bs.P) (s : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.W.J), (mat s).det = 1 →
      s ∈ closure {x | ∃ γ ∈ ratU σ Γ.W.J, ∃ k ∈ UAt σ Γ.W (evFin F v.1), x = γ * k} := by
  intro H F E _ _ _ _ _ σ a a' Bs Γ X om om' hT v s hs
  have hcm := hT.base.cm
  let w0 := (inferInstance : Nonempty (InfinitePlace F)).some
  have hWd : Γ.W.J.det ≠ 0 := by
    have h0 := det_ne_zero_of_hasSig (hT.geo.hW.sig w0)
    rw [Matrix.det_smul] at h0
    exact det_ne_zero_of_map _ _ (right_ne_zero_of_mul h0)
  have h2 : 2 ≤ a + a' := by have := hT.geo.aBig; omega
  obtain ⟨x, hx⟩ := GlobalTheory.AdelicU.exists_cm_conj_ne hcm
  have hδ : x - σ x ≠ 0 := sub_ne_zero.2 (Ne.symm hx)
  have hσδ : σ (x - σ x) = -(x - σ x) := by rw [map_sub, GlobalTheory.AdelicU.cm_conj_conj hcm, neg_sub]
  have hJ' := isHermND_smul_transpose hT.geo.hW.skew hWd hδ hσδ
  have hidem := isPlacesIdem_placeIdem (F := F) v.1
  have hnc := GlobalTheory.Published.StrongApprox.not_isCompact_split σ h2 hJ' v.1 (placeIdem v.1)
    (hidem.2.2.1 v.1 (Finset.mem_singleton_self _)) (splitIdemAd hcm (Bs.τ v)) (splitIdemAd_mul_self hcm _)
    (splitIdemAd_mul_sigR hcm _) (splitIdemAd_add_sigR hcm _)
  let s' : HA (AF F) σ ((x - σ x) • Γ.W.Jᵀ) :=
    (⟨s.1, (mem_UG_iff_mem_HR _ hδ _).1 s.2⟩ : HR (AF F) σ ((x - σ x) • Γ.W.Jᵀ))
  have hs' : s' ∈ GlobalTheory.Published.SUAdelic σ ((x - σ x) • Γ.W.Jᵀ) := GlobalTheory.Published.StrongApprox.mem_SUAdelic.2 hs
  have hcl := H F E σ hcm _ _ h2 hJ' ∅ {v.1} _ hidem hnc s' hs'
  have e : toUA Γ.W.J hδ s' = s := rfl
  rw [← e]
  refine map_mem_closure (continuous_toUA Γ.W.J hδ) hcl ?_
  rintro y ⟨γ, hγ, k, hk, rfl⟩
  refine ⟨toUA Γ.W.J hδ γ, ?_, toUA Γ.W.J hδ k, ?_, map_mul _ _ _⟩
  · obtain ⟨γ0, -, hγ0⟩ := Subgroup.mem_map.1 hγ.2
    exact Subgroup.mem_subgroupOf.2 ⟨γ0, hγ0⟩
  · intro u hu
    ext i j
    have hk2 := hk.2 i j
    change u • ((HA.mat (AF F) σ _ k).1 - 1 : Matrix (Fin (a + a')) (Fin (a + a')) (AF F ⊗[F] E)) i j = 0
    rw [Algebra.smul_def, ← hk2, ← mul_assoc, ← map_mul, mul_placeIdem hu, map_zero, zero_mul]

end GlobalTheory.SplitApprox
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongApproximationSplitPlaceSkewHermitianUnitarStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strongApproximation_splitPlace_skewHermitian_unitary : GlobalTheory.Published.StrongApproxSU → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : Chars F E) (om : Rep σ Γ.V Γ.W) (om' : Rep σ Γ.V' Γ.W), IsTriple Bs Γ X om om' →
    ∀ (v : Bs.P) (s : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.W.J), (mat s).det = 1 →
      s ∈ closure {x | ∃ γ ∈ ratU σ Γ.W.J, ∃ k ∈ UAt σ Γ.W (evFin F v.1), x = γ * k} := by
  first | exact @GlobalTheory.SplitApprox.strongApprox_split | exact GlobalTheory.SplitApprox.strongApprox_split | (intros; apply GlobalTheory.SplitApprox.strongApprox_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.Tri
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.AmpleGen

variable {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A]

def tri (n : ℤ) : ℤ := (n * n + n) / 2

def mix (L : LB A.left) (a b : ℤ) : LB A.left :=
  LB.LinComb L (K := Fin 2) ![𝟙 A.left, (GrpObj.inv : A ⟶ A).left] ![a, b]

def NV (P : LB A.left) (j : ℕ) : Prop :=
  ∃ (κ : Type) (_ : LinearOrder κ) (_ : Fintype κ) (W : κ → A.left.Opens),
    (∀ i, IsAffineOpen (W i)) ∧ ⨆ i, W i = ⊤ ∧ ¬ (GlobalTheory.AbLaw.cechLB A.hom P W).ExactAt j

end GlobalTheory.AmpleGen
end
end
