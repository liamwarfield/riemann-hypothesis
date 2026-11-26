module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDoubleStepKernelLocalModels
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransvectionLemmaOfWittCoreDescent

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingOnlyBaseGramRationalPointsContribute
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OffBaseGramTermSumInvariantRationalFlagUnipotent
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OffBaseGramTermSumInvariantRationalFlagUnipotent
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf.Reindex

variable {D : D7}

theorem exists_rat_block {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) {γ : GA D V} (hq : γ ∈ GQ V)
    (hn : γ ∈ flagN d) : ∃ (u : UX D ρ) (u₀ : Matrix (Fin ρ) (Fin ρ) D.host.E),
      blockX d γ = u.1.1 ∧ rat u₀ = u.1.1 := by
  obtain ⟨u, hu, h⟩ := GlobalTheory.JacClosed.flagN_le d hn
  have hb : blockX d γ = u.1 := by rw [blockX, h, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul]
  have hr : blockX d γ ∈ ratMx D ρ ρ :=
    ratMx_mul (rat_mem _) (ratMx_mul ((mem_GQ_iff V γ).1 hq) (rat_mem _))
  obtain ⟨u₀, hu₀⟩ := mem_ratMx.1 hr
  exact ⟨⟨u, hu⟩, u₀, hb, hu₀.trans hb⟩

theorem det_eq_one {ρ : ℕ} (u : UX D ρ) (u₀ : Matrix (Fin ρ) (Fin ρ) D.host.E) (h : rat u₀ = u.1.1) :
    u₀.det = 1 := by
  have h0 : ∀ i j : Fin ρ, j < i → u₀ i j = 0 := fun i j hij => incA_injective (by
    rw [map_zero]
    have := congrFun (congrFun h i) j
    change incA D (u₀ i j) = _ at this
    rw [this]; exact ((mem_UX.1 u.2) i j).1 hij)
  have h1 : ∀ i : Fin ρ, u₀ i i = 1 := fun i => incA_injective (by
    rw [map_one]
    have := congrFun (congrFun h i) i
    change incA D (u₀ i i) = _ at this
    rw [this]; exact ((mem_UX.1 u.2) i i).2)
  rw [Matrix.det_of_upperTriangular (fun i j (hij : j < i) => h0 i j hij)]
  simp [h1]

theorem gramQ_mul (W : HSp D) {ρ : ℕ} (x : Matrix (Fin W.rank) (Fin ρ) D.host.E) (u₀ : Matrix (Fin ρ) (Fin ρ) D.host.E) :
    gramQ W (x * u₀) = u₀ᴴ * gramQ W x * u₀ := by
  simp only [gramQ, Matrix.conjTranspose_mul, Matrix.mul_assoc]

end GlobalTheory.Unf.Reindex


open GlobalTheory.Unf.Reindex in
theorem GlobalTheory.Unf.tsum_offBase_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E), IsBase W x₀ → ∀ γ ∈ GQ V, γ ∈ flagN d → ∀ Φ : WO V W → ℂ, IsThetaFunO ψ V W Φ → ∑' x : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, term ψ d W vS (om (γ, 1) Φ) x.1 = ∑' x : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, term ψ d W vS Φ x.1 := by
  intro D ψ V V₀ W ρ d χV χW om om' hV hV₀ vS x₀ hx₀ γ hq hn Φ hΦ
  obtain ⟨u, u₀, hb, hu₀⟩ := exists_rat_block d hq hn
  have hdet : IsUnit u₀.det := by rw [det_eq_one u u₀ hu₀]; exact isUnit_one
  have hdet' : IsUnit u₀ᴴ.det := by rw [Matrix.det_conjTranspose, det_eq_one u u₀ hu₀, star_one]; exact isUnit_one
  set G₀ := gramQ W x₀
  have hG : u₀ᴴ * G₀ * u₀ = G₀ := by
    apply rat_injective
    have := hx₀.2 u.1 u.2
    rw [rat_mul, rat_mul, rat_conjTranspose, hu₀]
    rw [Matrix.mul_assoc]; exact this
  have key : ∀ x : Matrix (Fin W.rank) (Fin ρ) D.host.E, gramQ W (x * u₀) = G₀ ↔ gramQ W x = G₀ := by
    intro x
    rw [gramQ_mul]
    constructor
    · intro h
      have h2 : u₀ᴴ * gramQ W x * u₀ = u₀ᴴ * G₀ * u₀ := h.trans hG.symm
      have h3 := congrArg (fun M => (u₀ᴴ)⁻¹ * M * u₀⁻¹) h2
      simp only [Matrix.mul_assoc] at h3
      simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet', Matrix.mul_nonsing_inv _ hdet] using h3
    · intro h; rw [h, hG]
  have hinv : u₀ * u₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hinv' : u₀⁻¹ * u₀ = 1 := Matrix.nonsing_inv_mul _ hdet
  let e : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ G₀} ≃
      {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ G₀} :=
    { toFun := fun x => ⟨x.1 * u₀, fun h => x.2 ((key x.1).1 h)⟩
      invFun := fun x => ⟨x.1 * u₀⁻¹, fun h => x.2 (by
        have := (key (x.1 * u₀⁻¹)).2 h
        rwa [Matrix.mul_assoc, hinv', Matrix.mul_one] at this)⟩
      left_inv := fun x => Subtype.ext (by simp only [Matrix.mul_assoc, hinv, Matrix.mul_one])
      right_inv := fun x => Subtype.ext (by simp only [Matrix.mul_assoc, hinv', Matrix.mul_one]) }
  have hterm : ∀ x : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ G₀},
      term ψ d W vS (om (γ, 1) Φ) x.1 = term ψ d W vS Φ (e x).1 := by
    intro x
    refine (GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hV hV₀ vS Φ hΦ).2.1 γ hq hn x.1 (x.1 * u₀) ?_
    rw [rat_mul, hu₀, hb]
  rw [tsum_congr hterm]
  exact Equiv.tsum_eq e (fun y => term ψ d W vS Φ y.1)

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OffBaseGramTermSumInvariantRationalFlagUnipotentStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.offBaseGram_termSum_invariant_rationalFlagUnipotent : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E), IsBase W x₀ → ∀ γ ∈ GQ V, γ ∈ flagN d → ∀ Φ : WO V W → ℂ, IsThetaFunO ψ V W Φ → ∑' x : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, term ψ d W vS (om (γ, 1) Φ) x.1 = ∑' x : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, term ψ d W vS Φ x.1 := by
  first | exact @GlobalTheory.Unf.tsum_offBase_invariant | exact GlobalTheory.Unf.tsum_offBase_invariant | (intros; apply GlobalTheory.Unf.tsum_offBase_invariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralValueNeOneOfGramNe
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralValueNeOneOfGramNe
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem gramSkew_rat {D : D7} (W : HSp D) {ρ : ℕ} (y : Matrix (Fin W.rank) (Fin ρ) D.host.E) :
    GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew W (rat y) = rat ((-D.host.xi0) • (gramQ W y)ᵀ) := by
  have e : adj (rat y) ⬝ (gA W ⬝ rat y) = rat (gramQ W y) := by
    rw [gramQ, rat_mul, rat_mul, rat_conjTranspose]; rfl
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew, e, rat_smul, map_neg]
  rfl

theorem gramQ_eq_of_gramSkew {D : D7} (W : HSp D) {ρ : ℕ} {x y : Matrix (Fin W.rank) (Fin ρ) D.host.E}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew W (rat x) = GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew W (rat y)) : gramQ W x = gramQ W y := by
  rw [gramSkew_rat, gramSkew_rat] at h
  have h' := rat_injective h
  have hξ : -D.host.xi0 ≠ 0 := neg_ne_zero.2 (GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero (D := D))
  exact Matrix.transpose_injective (smul_right_injective _ hξ h')

theorem exists_central_ne : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (x₀ x : Matrix (Fin W.rank) (Fin ρ) D.host.E), gramQ W x ≠ gramQ W x₀ → ∃ c : skewA D ρ, star (ψ (d.qS W c (rat x₀))) * ψ (d.qS W c (rat x)) ≠ 1 := by
  intro D ψ hψ V V₀ W ρ d x₀ x hne
  by_contra hcon
  push_neg at hcon
  have hall : ∀ c : skewA D ρ, ψ (d.qS W c (rat x)) = ψ (d.qS W c (rat x₀)) := by
    intro c
    have hn : ‖ψ (d.qS W c (rat x₀))‖ = 1 := hψ.1.2.1 _
    have hs : ψ (d.qS W c (rat x₀)) * star (ψ (d.qS W c (rat x₀))) = 1 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; simp
    calc ψ (d.qS W c (rat x)) = ψ (d.qS W c (rat x₀)) * star (ψ (d.qS W c (rat x₀))) * ψ (d.qS W c (rat x)) := by
          rw [hs, one_mul]
      _ = ψ (d.qS W c (rat x₀)) := by rw [mul_assoc, hcon c, mul_one]
  have h := (((GlobalTheory.T.mixedModelCentralTerms_via_gramMatrices D).1 V V₀ W ρ d).2.2 ψ hψ).2.2 (rat x) (rat_mem x) (rat x₀) (rat_mem x₀)
  exact hne (gramQ_eq_of_gramSkew W (h.1 hall))

end GlobalTheory.Unf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralValueNeOneOfGramNeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_centralValue_ne_one_of_gram_ne : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (x₀ x : Matrix (Fin W.rank) (Fin ρ) D.host.E), gramQ W x ≠ gramQ W x₀ → ∃ c : skewA D ρ, star (ψ (d.qS W c (rat x₀))) * ψ (d.qS W c (rat x)) ≠ 1 := by
  first | exact @GlobalTheory.Unf.exists_central_ne | exact GlobalTheory.Unf.exists_central_ne | (intros; apply GlobalTheory.Unf.exists_central_ne <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingOnlyBaseGramRationalPointsContribute
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Unf.cut_gram_base : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (vN : VolN d) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (Th : GA D V → ℂ), IsBase W x₀ → IsTh ψ d W x₀ Th → ∀ Ψ : WO V W → ℂ, IsThetaFunO ψ V W Ψ → ∫ n in vN.𝓝, ∑' x : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1 ∂vN.ν = 0 := by
  intro D ψ V V₀ W ρ d χV χW om om' hW hW' vS vN x₀ Th hB hTh Ψ hΨ
  have lemR : ∀ γ ∈ GQ V, γ ∈ flagN d → ∀ Φ : WO V W → ℂ, IsThetaFunO ψ V W Φ → ∑' x : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, term ψ d W vS (om (γ, 1) Φ) x.1 = ∑' x : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, term ψ d W vS Φ x.1 := GlobalTheory.T.offBaseGram_termSum_invariant_rationalFlagUnipotent D ψ V V₀ W ρ d χV χW om om' hW hW' vS x₀ hB
  have lemQ : ∀ x : Matrix (Fin W.rank) (Fin ρ) D.host.E, gramQ W x ≠ gramQ W x₀ → ∃ c : skewA D ρ, star (ψ (d.qS W c (rat x₀))) * ψ (d.qS W c (rat x)) ≠ 1 := GlobalTheory.T.exists_centralValue_ne_one_of_gram_ne D ψ hW.std V V₀ W ρ d x₀
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨j1, j2, j3, j4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag V (isIsoSub_e d)
  obtain ⟨hH, hFD, h1⟩ := vN.unit

  have hBc : ∀ (c : skewA D ρ) (Φ : WO V W → ℂ), IsThetaFunO ψ V W Φ → ∀ x,
      term ψ d W vS (om (d.nC c, 1) Φ) x = ψ (d.qS W c (rat x)) * term ψ d W vS Φ x := by
    intro c Φ hΦ x
    have h := (GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hW hW' vS Φ hΦ).1 x 0 1 c
    rw [d.nB_zero, Subgroup.coe_one, map_one, mul_one, mul_one] at h
    rw [h]
    simp only [Subgroup.coe_one, Units.val_one, Matrix.mul_one, Matrix.mul_zero]
    rfl
  have hsplit : ∀ g h : GA D V, om (g * h, 1) Ψ = om (g, 1) (om (h, 1) Ψ) := by
    intro g h
    rw [show ((g * h, (1 : GA D W)) : GA D V × GA D W) = (g, 1) * (h, 1) by simp, map_mul, Module.End.mul_apply]
  let F : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀} → flagN d → ℂ :=
    fun i n => Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) i.1
  let a : skewA D ρ → Matrix (Fin W.rank) (Fin ρ) D.host.E → ℂ :=
    fun c x => star (ψ (d.qS W c (rat x₀))) * ψ (d.qS W c (rat x))
  have hE : ∀ i c (n : flagN d), F i (⟨d.nC c, d.nC_mem_NFlag c⟩ * n) = a c i.1 * F i n := by
    intro i c n
    simp only [F, a, Subgroup.coe_mul]
    rw [hTh.cen c n.1 n.2, hsplit, hBc c _ (hW.om_pres _ _ hΨ)]
    ring

  haveI : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin W.rank) (Fin ρ) D.host.E) :=
    inferInstanceAs (Countable (Fin W.rank → Fin ρ → D.host.E))
  have hT := GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hW hW' vS
  obtain ⟨-, hM⟩ := GlobalTheory.T.flag_subgroups_closed_normal_cocompact' D V V₀ ρ d
  obtain ⟨-, hcl, hnorm, K, hK, hKc⟩ := hM (GlobalTheory.MixPer.centre d) (Or.inl rfl)
  have hdisc : DiscreteTopology (NFlagQ V d.e) :=
    DiscreteTopology.of_continuous_injective (f := fun γ : NFlagQ V d.e => (⟨γ.1.1, γ.2⟩ : GQ V))
      (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _)
      (fun a b h => Subtype.ext (Subtype.ext (congrArg (fun x : GQ V => (x : GA D V)) h)))
  have hcl' : IsClosed (((GlobalTheory.MixPer.centre d).subgroupOf (flagN d) : Subgroup (flagN d)) : Set (flagN d)) := by
    rw [Subgroup.coe_subgroupOf]; exact hcl.preimage continuous_subtype_val
  have hcpt : ∃ K' : Set ((GlobalTheory.MixPer.centre d).subgroupOf (flagN d)), IsCompact K' ∧
      ∀ m, ∃ γ ∈ (NFlagQ V d.e).subgroupOf ((GlobalTheory.MixPer.centre d).subgroupOf (flagN d)), ∃ k ∈ K', m = γ * k := by
    let φ : GlobalTheory.MixPer.centre d → (GlobalTheory.MixPer.centre d).subgroupOf (flagN d) := fun c =>
      ⟨⟨c.1, (hM (GlobalTheory.MixPer.centre d) (Or.inl rfl)).1 c.2⟩, Subgroup.mem_subgroupOf.2 c.2⟩
    have hφ : Continuous φ := Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _
    refine ⟨φ '' K, hK.image hφ, fun m => ?_⟩
    obtain ⟨γ, hγ, k, hk, e⟩ := hKc ⟨m.1.1, Subgroup.mem_subgroupOf.1 m.2⟩
    refine ⟨φ γ, ?_, φ k, ⟨k, hk, rfl⟩, ?_⟩
    · exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hγ))
    · refine Subtype.ext (Subtype.ext ?_)
      change m.1.1 = γ.1 * k.1
      exact congrArg Subtype.val e
  have hmeas : ∀ i, Measurable (F i) := fun i =>
    (hTh.cont.mul ((hT Ψ hΨ).2.2.2.1 i.1 |>.comp (continuous_subtype_val.prodMk continuous_const))).measurable
  have hbd : ∃ B : NNReal, ∀ n, ∑' i, ‖F i n‖ₑ ≤ B := by
    obtain ⟨K, hK, hKc⟩ := (GlobalTheory.T.isotropic_unipotentRadicals_rational_cocompact D V ρ d.e (isIsoSub_e d)).1
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hTh.cont.continuousOn
    obtain ⟨C, A, hCA⟩ := GlobalTheory.T.thetaTermSeries_summable_moderateGrowth_uniform D ψ V V₀ W ρ d χV χW om om' hW hW' vS Ψ hΨ
    refine ⟨M.toNNReal * (C * (height V 1 * quotHeight W 1) ^ A).toNNReal, fun n => ?_⟩
    have hTn : ‖Th n.1‖ₑ ≤ ENNReal.ofReal M := by
      obtain ⟨γ, hγ, k, hk, rfl⟩ := hKc n
      rw [Subgroup.coe_mul, hTh.left γ.1 (Subgroup.mem_subgroupOf.1 hγ) γ.2 k.1 k.2, ← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (hM k hk)
    have hS := hCA 1 1 n.1 n.2
    rw [mul_one] at hS
    calc ∑' i, ‖F i n‖ₑ = ‖Th n.1‖ₑ * ∑' i : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀},
          ‖term ψ d W vS (om (n.1, 1) Ψ) i.1‖ₑ := by
          rw [← ENNReal.tsum_mul_left]; exact tsum_congr fun i => enorm_mul _ _
      _ ≤ ENNReal.ofReal M * ENNReal.ofReal (C * (height V 1 * quotHeight W 1) ^ A) :=
          mul_le_mul' hTn ((ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _).trans hS)
      _ = _ := by rw [ENNReal.ofReal, ENNReal.ofReal, ← ENNReal.coe_mul]
  have hinv : ∀ γ ∈ NFlagQ V d.e, ∀ n, ∑' i, F i (γ * n) = ∑' i, F i n := by
    intro γ hγ n
    have hγ' := Subgroup.mem_subgroupOf.1 hγ
    simp only [F, Subgroup.coe_mul]
    rw [hTh.left γ.1 hγ' γ.2 n.1 n.2, hsplit, tsum_mul_left, tsum_mul_left,
      lemR γ.1 hγ' γ.2 _ (hW.om_pres _ _ hΨ)]
  have hcinv : ∀ c : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, ∀ γ ∈ NFlagQ V d.e, γ ∈ (GlobalTheory.MixPer.centre d).subgroupOf (flagN d) → ∀ n,
      ∑' i : {i : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀} // id i = c}, F i.1 (γ * n) =
        ∑' i : {i : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀} // id i = c}, F i.1 n := by
    intro c γ hγ hγM n
    refine tsum_congr fun i => ?_
    have hγ' := Subgroup.mem_subgroupOf.1 hγ
    obtain ⟨c', hc'⟩ := Subgroup.mem_subgroupOf.1 hγM
    simp only [F, Subgroup.coe_mul]
    rw [hTh.left γ.1 hγ' γ.2 n.1 n.2, hsplit]
    congr 1
    refine (hT _ (hW.om_pres _ _ hΨ)).2.1 γ.1 hγ' γ.2 i.1.1 i.1.1 ?_
    rw [blockX_of_fix d (mem_fixer.2 (hc' ▸ d.nC_jX c')), Matrix.mul_one]
  have heig : ∀ c : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, ∃ u ∈ (GlobalTheory.MixPer.centre d).subgroupOf (flagN d), ∃ a : ℂ, a ≠ 1 ∧ ∀ i : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, id i = c →
      ∀ m ∈ (GlobalTheory.MixPer.centre d).subgroupOf (flagN d), ∀ n, F i (m * u * n) = a * F i (m * n) := by
    intro c
    obtain ⟨c', hc'⟩ := lemQ c.1 c.2
    refine ⟨⟨d.nC c', d.nC_mem_NFlag c'⟩, Subgroup.mem_subgroupOf.2 ⟨c', rfl⟩, a c' c.1, hc', ?_⟩
    intro i hi m hm n
    subst hi
    obtain ⟨c'', hc''⟩ := Subgroup.mem_subgroupOf.1 hm
    have : m = ⟨d.nC c'', d.nC_mem_NFlag c''⟩ := Subtype.ext hc''.symm
    subst this
    rw [mul_assoc, hE, hE, hE]
    simp only [id]
    ring
  exact GlobalTheory.T.integral_tsum_normal_eigenfunctions_eq_zero (flagN d) vN.ν (NFlagQ V d.e) ((GlobalTheory.MixPer.centre d).subgroupOf (flagN d)) j4 hdisc hnorm hcl' hcpt
    vN.𝓝 hFD (by rw [h1]; exact ENNReal.one_ne_top) _ _ id F hmeas hbd hinv hcinv heig
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingOnlyBaseGramRationalPointsContributeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfolding_only_baseGram_rational_points_contribute : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (vN : VolN d) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (Th : GA D V → ℂ), IsBase W x₀ → IsTh ψ d W x₀ Th → ∀ Ψ : WO V W → ℂ, IsThetaFunO ψ V W Ψ → ∫ n in vN.𝓝, ∑' x : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1 ∂vN.ν = 0 := by
  first | exact @GlobalTheory.Unf.cut_gram_base | exact GlobalTheory.Unf.cut_gram_base | (intros; apply GlobalTheory.Unf.cut_gram_base <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DependentFramesFirstRelationMeanZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransvectionTrivialAfterFlagUnipotentFixing
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransvectionTrivialAfterFlagUnipotentFixing
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf

open GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction

variable {D : D7}

theorem form_mulVec_mulVec (S : HSp D) {k l : ℕ} (M : Mx D S.rank k) (N : Mx D S.rank l) (x : Fin k → AE D)
    (y : Fin l → AE D) :
    form S (M *ᵥ x) (N *ᵥ y) = (fun i => cA D (y i)) ⬝ᵥ ((adj N ⬝ (gA S ⬝ M)) *ᵥ x) := by
  have h : (fun i => cA D ((N *ᵥ y) i)) = (N.map (cA D)) *ᵥ fun i => cA D (y i) := by
    funext i
    exact RingHom.map_mulVec (cA D) N y i
  rw [form, h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec _ (adj N), adj,
    Matrix.vecMul_transpose]

theorem form_act_act (S : HSp D) (g : GA D S) (x y : VA S) : form S (act S g x) (act S g y) = form S x y := by
  rw [act, act, form_mulVec_mulVec, mt_unitary, form]

theorem act_vecX_of_mem_Nfix {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (j : Fin ρ) (a : Fin ρ → AE D)
    (ha : ∀ i, j < i → a i = 0) {m : GA D V} (hm : m ∈ Nfix d j) : act V m (vecX d a) = vecX d a := by
  have hm' : ∀ i : Fin ρ, i ≤ j → ∀ k, (mt V m ⬝ d.jX : Mx D V.rank ρ) k i = d.jX k i := by
    intro i hi k
    have h1 := (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hm).2) ⟨i, hi⟩
    have h2 := congrFun (congrFun (mem_fixer.1 h1) k) 0
    simpa [Matrix.mul_apply, Matrix.submatrix_apply] using h2
  rw [act, vecX, Matrix.mulVec_mulVec]
  funext k
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i ≤ j
  · rw [hm' i hi k]
  · rw [ha i (not_le.1 hi), mul_zero, mul_zero]

theorem rat_mulVec_ratVec {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E) (a : Fin n → D.host.E) :
    rat x *ᵥ ratVec a = ratVec (x *ᵥ a) := by
  funext i
  exact (RingHom.map_mulVec (incA D) x a i).symm

theorem transv_trivial_after_Nfix : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W), IsWeilDatumO ψ V W χV χW om → ∀ (vS : VolM D W.rank ρ) (Ψ : WO V W → ℂ), IsThetaFunO ψ V W Ψ → ∀ (j : Fin ρ) (a : Fin ρ → D.host.E), (∀ i, j < i → a i = 0) → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.VA V) (u : GA D V), GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v = 0 → GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.IsTransv V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v u → ∀ x : Matrix (Fin W.rank) (Fin ρ) D.host.E, x *ᵥ a = 0 → ∀ m ∈ Nfix d j, ∀ n : GA D V, term ψ d W vS (om (m * u * n, 1) Ψ) x = term ψ d W vS (om (m * n, 1) Ψ) x := by
  intro D hD ψ V V₀ W ρ d χV χW om hW vS Ψ hΨ j a ha v u hv hu x hx m hm n
  obtain ⟨-, hConj, hTriv⟩ := GlobalTheory.T.transvectionLemma_of_wittCoreDescent D hD
  have ha' : ∀ i, j < i → ratVec a i = 0 := fun i hi => by simp [ratVec, ha i hi]
  have hmw : act V m (vecX d (ratVec a)) = vecX d (ratVec a) := act_vecX_of_mem_Nfix d j _ ha' hm
  have hc := hConj V V₀ ρ d (ratVec a) v hv u m hu
  rw [hmw] at hc
  have hv' : form V (vecX d (ratVec a)) (act V m v) = 0 := by
    rw [← hmw, form_act_act, hv]
  have hx' : rat x *ᵥ ratVec a = 0 := by
    rw [rat_mulVec_ratVec, hx]
    funext i
    simp [ratVec]
  have e : ((m * u * n, (1 : GA D W)) : GA D V × GA D W) = (m * u * m⁻¹, 1) * (m * n, 1) := by
    ext
    · simp [mul_assoc]
    · simp
  have key := hTriv V V₀ W ρ d ψ χV χW om hW vS.μ vS.𝓕 vS.covol a (act V m v) hv' (m * u * m⁻¹) hc (rat x) hx'
    (om (m * n, 1) Ψ) (hW.om_pres _ _ hΨ)
  rw [term, term, e, map_mul, Module.End.mul_apply]
  exact congrFun key 0

end GlobalTheory.Unf

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransvectionTrivialAfterFlagUnipotentFixingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transvection_trivial_after_flagUnipotentFixing : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W), IsWeilDatumO ψ V W χV χW om → ∀ (vS : VolM D W.rank ρ) (Ψ : WO V W → ℂ), IsThetaFunO ψ V W Ψ → ∀ (j : Fin ρ) (a : Fin ρ → D.host.E), (∀ i, j < i → a i = 0) → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.VA V) (u : GA D V), GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v = 0 → GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.IsTransv V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v u → ∀ x : Matrix (Fin W.rank) (Fin ρ) D.host.E, x *ᵥ a = 0 → ∀ m ∈ Nfix d j, ∀ n : GA D V, term ψ d W vS (om (m * u * n, 1) Ψ) x = term ψ d W vS (om (m * n, 1) Ψ) x := by
  first | exact @GlobalTheory.Unf.transv_trivial_after_Nfix | exact GlobalTheory.Unf.transv_trivial_after_Nfix | (intros; apply GlobalTheory.Unf.transv_trivial_after_Nfix <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GramMatrixOfColumnsUnitriangularConjEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GramMatrixOfColumnsUnitriangularConjEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf

theorem gramQ_unitri : ∀ (D : D7) (W : HSp D) (ρ : ℕ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E), IsBase W x₀ → ∀ u : Matrix (Fin ρ) (Fin ρ) D.host.E, (∀ i, u i i = 1) → (∀ i k, k < i → u i k = 0) → uᴴ * gramQ W x₀ * u = gramQ W x₀ := by
  intro D W ρ x₀ hb u hd hl
  have htri : (rat u : Mx D ρ ρ).BlockTriangular id := fun i j (h : j < i) => by
    show incA D (u i j) = 0
    rw [hl i j h, map_zero]
  have hdiag : ∀ i, (rat u : Mx D ρ ρ) i i = 1 := fun i => by
    show incA D (u i i) = 1
    rw [hd i, map_one]
  have hu : IsUnit (rat u : Mx D ρ ρ) := (Matrix.isUnit_iff_isUnit_det _).2 (by
    rw [Matrix.det_of_upperTriangular htri]; simp only [hdiag, Finset.prod_const_one]; exact isUnit_one)
  have hmem : hu.unit ∈ UX D ρ := fun i j => ⟨fun h => htri h, hdiag i⟩
  have h := hb.2 _ hmem
  rw [IsUnit.unit_spec] at h
  apply rat_injective
  rw [rat_mul, rat_mul, rat_conjTranspose, Matrix.mul_assoc]
  exact h

end GlobalTheory.Unf

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GramMatrixOfColumnsUnitriangularConjEqStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramMatrixOfColumns_unitriangular_conj_eq : ∀ (D : D7) (W : HSp D) (ρ : ℕ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E), IsBase W x₀ → ∀ u : Matrix (Fin ρ) (Fin ρ) D.host.E, (∀ i, u i i = 1) → (∀ i k, k < i → u i k = 0) → uᴴ * gramQ W x₀ * u = gramQ W x₀ := by
  first | exact @GlobalTheory.Unf.gramQ_unitri | exact GlobalTheory.Unf.gramQ_unitri | (intros; apply GlobalTheory.Unf.gramQ_unitri <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalFlagUnipotentIsotropicBlockUnitriangular
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalFlagUnipotentIsotropicBlockUnitriangular
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf.RatBlock

variable {D : D7}

theorem blockX_mem_UX {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) {n : GA D V} (hn : n ∈ flagN d) :
    ∃ u ∈ UX D ρ, blockX d n = u.1 := by
  obtain ⟨u, hu, b, c, rfl⟩ := ((flag_jacobi_structure D V V₀ ρ d).1 n).1 hn
  have h1 : mt V (d.levi u * (d.nB b * d.nC c)) ⬝ d.jX = d.jX ⬝ u.1 := by
    rw [mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, d.nC_jX, d.nB_jX, d.levi_jX]
  refine ⟨u, hu, ?_⟩
  rw [blockX, h1, ← Matrix.mul_assoc d.pX d.jX, d.pX_jX, Matrix.one_mul]

theorem blockX_col_of_fix {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) {g : GA D V} (k : Fin ρ)
    (h : g ∈ fixer V (d.jX.submatrix id fun _ : Fin 1 => k)) (i : Fin ρ) :
    blockX d g i k = (1 : Mx D ρ ρ) i k := by
  have hcol : ∀ l, (mt V g ⬝ d.jX) l k = d.jX l k := fun l => by
    have := congrFun (congrFun (mem_fixer.1 h) l) 0
    simpa [Matrix.mul_apply, Matrix.submatrix_apply] using this
  rw [← d.pX_jX, blockX, Matrix.mul_apply, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun l _ => by rw [hcol l]

end GlobalTheory.Unf.RatBlock


open GlobalTheory.Unf.RatBlock in
theorem GlobalTheory.Unf.ratBlock_unitri : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (γ : GA D V), γ ∈ GQ V → γ ∈ flagN d → ∃ u u' : Matrix (Fin ρ) (Fin ρ) D.host.E, (rat u : Mx D ρ ρ) = blockX d γ ∧ u * u' = 1 ∧ u' * u = 1 ∧ (∀ i, u i i = 1) ∧ (∀ i k, k < i → u i k = 0) ∧ ∀ j : Fin ρ, γ ∈ Nfix d j → ∀ i k, k ≤ j → u i k = if i = k then 1 else 0 := by
  intro D V V₀ ρ d γ hq hn
  obtain ⟨M, hM⟩ := (mem_GQ_iff V γ).1 hq
  have hM' : rat M = mt V γ := hM
  have hb : (rat (d.qX * (M * d.e)) : Mx D ρ ρ) = blockX d γ := by
    rw [blockX, ← hM', rat_mul, rat_mul]; rfl
  obtain ⟨v, hv, hvb⟩ := blockX_mem_UX d hn
  have hent : ∀ i k, incA D ((d.qX * (M * d.e)) i k) = v.1 i k := fun i k => by
    have := congrFun (congrFun (hb.trans hvb) i) k
    exact this
  have hdiag : ∀ i, (d.qX * (M * d.e)) i i = 1 := fun i =>
    incA_injective (by rw [map_one, hent]; exact ((mem_UX.1 hv) i i).2)
  have hlow : ∀ i k, k < i → (d.qX * (M * d.e)) i k = 0 := fun i k hki =>
    incA_injective (by rw [map_zero, hent]; exact ((mem_UX.1 hv) i k).1 hki)
  have hdet : (d.qX * (M * d.e)).det = 1 := by
    rw [Matrix.det_of_upperTriangular (fun i k (hki : k < i) => hlow i k hki)]
    simp [hdiag]
  have hu : IsUnit (d.qX * (M * d.e)).det := by rw [hdet]; exact isUnit_one
  refine ⟨d.qX * (M * d.e), (d.qX * (M * d.e))⁻¹, hb, Matrix.mul_nonsing_inv _ hu, Matrix.nonsing_inv_mul _ hu,
    hdiag, hlow, fun j hj i k hkj => ?_⟩
  have hfix : γ ∈ fixer V (d.jX.submatrix id fun _ : Fin 1 => k) := by
    have h2 := (Subgroup.mem_inf.1 hj).2
    exact (Subgroup.mem_iInf.1 h2) ⟨k, hkj⟩
  apply incA_injective
  have e1 := blockX_col_of_fix d k hfix i
  rw [← hb] at e1
  change incA D _ = _ at e1
  rw [e1, Matrix.one_apply]
  split_ifs <;> simp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalFlagUnipotentIsotropicBlockUnitriangularStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_flagUnipotent_isotropicBlock_unitriangular : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (γ : GA D V), γ ∈ GQ V → γ ∈ flagN d → ∃ u u' : Matrix (Fin ρ) (Fin ρ) D.host.E, (rat u : Mx D ρ ρ) = blockX d γ ∧ u * u' = 1 ∧ u' * u = 1 ∧ (∀ i, u i i = 1) ∧ (∀ i k, k < i → u i k = 0) ∧ ∀ j : Fin ρ, γ ∈ Nfix d j → ∀ i k, k ≤ j → u i k = if i = k then 1 else 0 := by
  exact GlobalTheory.Unf.ratBlock_unitri
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DependentFramesFirstRelationMeanZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf.DepFrames

theorem gramQ_mul {D : D7} (W : HSp D) {ρ : ℕ} (x : Matrix (Fin W.rank) (Fin ρ) D.host.E) (u : Matrix (Fin ρ) (Fin ρ) D.host.E) :
    gramQ W (x * u) = uᴴ * gramQ W x * u := by
  simp only [gramQ, conjTranspose_mul, Matrix.mul_assoc]

theorem dep_frames_mean_zero : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (vN : VolN d) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (Th : GA D V → ℂ), IsBase W x₀ → IsTh ψ d W x₀ Th → ∀ Ψ : WO V W → ℂ, IsThetaFunO ψ V W Ψ → ∀ j : Fin ρ, ∫ n in vN.𝓝, ∑' x : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x = gramQ W x₀ ∧ (∀ a : Fin ρ → D.host.E, (∀ i, j ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) ∧ ∃ a : Fin ρ → D.host.E, a j = 1 ∧ (∀ i, j < i → a i = 0) ∧ x *ᵥ a = 0}, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1 ∂vN.ν = 0 := by
  intro D hDesc ψ V V₀ W ρ d χV χW om om' hw hw' vS vN x₀ Th hB hTh Ψ hΨ j
  classical
  have : Countable D.host.E := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableE
  have : Countable (Matrix (Fin W.rank) (Fin ρ) D.host.E) :=
    inferInstanceAs (Countable (Fin W.rank → Fin ρ → D.host.E))
  obtain ⟨hLC, hSC, -, -, -, hDisc, hCnt⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have h56 := GlobalTheory.T.flag_subgroups_closed_normal_cocompact' D V V₀ ρ d
  haveI : LocallyCompactSpace (flagN d) := h56.1.locallyCompactSpace
  haveI : SecondCountableTopology (flagN d) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : vN.ν.IsHaarMeasure := vN.unit.1
  obtain ⟨hle, hNcl, hNnorm, K, hK, hcov⟩ := h56.2 (Nfix d j) (Or.inr (Or.inr ⟨j, rfl⟩))
  have hT := GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hw hw' vS
  have hcont : ∀ x, Continuous fun n : flagN d => term ψ d W vS (om (n.1, 1) Ψ) x := fun x =>
    ((hT Ψ hΨ).2.2.2.1 x).comp (continuous_subtype_val.prodMk continuous_const)
  obtain ⟨C, A, hC⟩ := GlobalTheory.T.thetaTermSeries_summable_moderateGrowth_uniform D ψ V V₀ W ρ d χV χW om om' hw hw' vS Ψ hΨ
  obtain ⟨K0, hK0, hcov0⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D V ρ d.e (isIsoSub_e d)).1
  obtain ⟨Mb, hMb⟩ := hK0.exists_bound_of_continuousOn (f := fun n : flagN d => Th n.1) hTh.cont.continuousOn
  have hThb : ∀ n : flagN d, ‖Th n.1‖ ≤ Mb := by
    intro n
    obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov0 n
    have hγ' : (γ : GA D V) ∈ GQ V := Subgroup.mem_subgroupOf.1 hγ
    have : Th ((γ * k : flagN d) : GA D V) = Th k.1 := hTh.left γ.1 hγ' γ.2 k.1 k.2
    rw [this]
    exact hMb k hk
  have hbdS : ∀ (S : Set (Matrix (Fin W.rank) (Fin ρ) D.host.E)) (n : flagN d),
      ∑' x : S, ‖Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1‖ₑ ≤
        ((Mb.toNNReal * (C * (height V 1 * quotHeight W 1) ^ A).toNNReal : NNReal) : ENNReal) := by
    intro S n
    have h1 : ∑' x, ‖term ψ d W vS (om (n.1, 1) Ψ) x‖ₑ ≤ ENNReal.ofReal (C * (height V 1 * quotHeight W 1) ^ A) := by
      have := hC 1 1 n.1 n.2
      rwa [mul_one] at this
    simp_rw [enorm_mul]
    rw [ENNReal.tsum_mul_left, ENNReal.coe_mul]
    refine mul_le_mul' ?_ ((ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _).trans h1)
    rw [← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal (hThb n)
  let Pj : Matrix (Fin W.rank) (Fin ρ) D.host.E → Prop := fun x => gramQ W x = gramQ W x₀ ∧
    (∀ a : Fin ρ → D.host.E, (∀ i, j ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) ∧
    ∃ a : Fin ρ → D.host.E, a j = 1 ∧ (∀ i, j < i → a i = 0) ∧ x *ᵥ a = 0
  have huniq : ∀ x : Matrix (Fin W.rank) (Fin ρ) D.host.E,
      (∀ a : Fin ρ → D.host.E, (∀ i, j ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) →
      ∀ a a' : Fin ρ → D.host.E, a j = 1 → (∀ i, j < i → a i = 0) → x *ᵥ a = 0 →
        a' j = 1 → (∀ i, j < i → a' i = 0) → x *ᵥ a' = 0 → a = a' := by
    intro x hind a a' ha1 ha2 ha3 hb1 hb2 hb3
    refine sub_eq_zero.1 (hind (a - a') (fun i hi => ?_) (by rw [Matrix.mulVec_sub, ha3, hb3, sub_self]))
    rcases hi.lt_or_eq with h | h
    · simp [ha2 i h, hb2 i h]
    · subst h; simp [ha1, hb1]
  have hPu : ∀ u u' : Matrix (Fin ρ) (Fin ρ) D.host.E, u * u' = 1 → u' * u = 1 → (∀ i, u i i = 1) →
      (∀ i k, k < i → u i k = 0) → ∀ x, Pj x ↔ Pj (x * u) := by
    intro u u' huu' hu'u hdiag htri x
    have hG := GlobalTheory.T.gramMatrixOfColumns_unitriangular_conj_eq D W ρ x₀ hB u hdiag htri
    refine and_congr ⟨fun h => by rw [gramQ_mul, h, hG], fun h => ?_⟩ ((GlobalTheory.T.dependent_frame_first_column_relation D.host.E W.rank ρ x).2.2 j u hdiag htri)
    rw [gramQ_mul, ← hG] at h
    have h' := congrArg (fun M => u'ᴴ * M * u') h
    have e1 : ∀ M : Matrix (Fin ρ) (Fin ρ) D.host.E, u'ᴴ * (uᴴ * M * u) * u' = M := by
      intro M
      rw [show u'ᴴ * (uᴴ * M * u) * u' = (u * u')ᴴ * M * (u * u') by
        simp only [conjTranspose_mul, Matrix.mul_assoc]]
      rw [huu', conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
    rwa [e1, e1] at h'

  have key : ∀ γ : flagN d, γ.1 ∈ GQ V → ∀ u : Matrix (Fin ρ) (Fin ρ) D.host.E, (rat u : Mx D ρ ρ) = blockX d γ.1 →
      ∀ (n : flagN d) (x : Matrix (Fin W.rank) (Fin ρ) D.host.E),
        Th (γ * n).1 * term ψ d W vS (om ((γ * n).1, 1) Ψ) x = Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) (x * u) := by
    intro γ hγ u hu n x
    have hom : om ((γ * n).1, 1) Ψ = om (γ.1, 1) (om (n.1, 1) Ψ) := by
      rw [show (((γ * n : flagN d) : GA D V), (1 : GA D W)) = (γ.1, 1) * (n.1, 1) by
        rw [Prod.mk_mul_mk, one_mul]; rfl, map_mul]
      rfl
    rw [hom, (hT _ (hw.om_pres _ _ hΨ)).2.1 γ.1 hγ γ.2 x (x * u) (by rw [rat_mul, hu]),
      show ((γ * n : flagN d) : GA D V) = γ.1 * n.1 from rfl, hTh.left γ.1 hγ γ.2 n.1 n.2]
  have hfixv : ∀ u : Matrix (Fin ρ) (Fin ρ) D.host.E, (∀ i k, k ≤ j → u i k = if i = k then 1 else 0) →
      ∀ c : Fin ρ → D.host.E, (∀ i, j < i → c i = 0) → u *ᵥ c = c := by
    intro u hu c hc
    funext i
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_congr rfl (g := fun k => if i = k then c k else 0) fun k _ => ?_, Finset.sum_ite_eq]
    · simp
    · rcases le_or_gt k j with h | h
      · rw [hu i k h]; split_ifs <;> simp
      · rw [hc k h]; simp
  refine GlobalTheory.T.integral_tsum_normal_eigenfunctions_eq_zero (flagN d) vN.ν ((GQ V).subgroupOf (flagN d)) ((Nfix d j).subgroupOf (flagN d)) ?_ ?_ hNnorm
    (hNcl.preimage continuous_subtype_val) ?_ vN.𝓝 vN.unit.2.1 (by rw [vN.unit.2.2]; exact ENNReal.one_ne_top)
    {x // Pj x} (Fin ρ → D.host.E) (fun x => Classical.choose x.2.2.2)
    (fun x n => Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1) (fun x => (hTh.cont.mul (hcont x.1)).measurable)
    ⟨_, fun n => hbdS {x | Pj x} n⟩ ?_ ?_ ?_
  · exact Function.Injective.countable (f := fun x : ((GQ V).subgroupOf (flagN d)) =>
      (⟨x.1.1, Subgroup.mem_subgroupOf.1 x.2⟩ : GQ V))
      (fun a b h => Subtype.ext (Subtype.ext (congrArg (fun y : GQ V => y.1) h)))
  · exact DiscreteTopology.of_continuous_injective (f := fun x : ((GQ V).subgroupOf (flagN d)) =>
      (⟨x.1.1, Subgroup.mem_subgroupOf.1 x.2⟩ : GQ V))
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
      (fun a b h => Subtype.ext (Subtype.ext (congrArg (fun y : GQ V => y.1) h)))
  · refine ⟨(fun m : Nfix d j => (⟨⟨m.1, hle m.2⟩, m.2⟩ : (Nfix d j).subgroupOf (flagN d))) '' K,
      hK.image ((continuous_subtype_val.subtype_mk _).subtype_mk _), fun m => ?_⟩
    obtain ⟨γ, hγ, k, hk, e⟩ := hcov ⟨m.1.1, Subgroup.mem_subgroupOf.1 m.2⟩
    refine ⟨⟨⟨γ.1, hle γ.2⟩, γ.2⟩, ?_, ⟨⟨k.1, hle k.2⟩, k.2⟩, ⟨k, hk, rfl⟩, ?_⟩
    · rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]; exact Subgroup.mem_subgroupOf.1 hγ
    · have e2 : m.1.1 = γ.1 * k.1 := congrArg Subtype.val e
      exact Subtype.ext (Subtype.ext e2)
  · intro γ hγ n
    have hγ' : γ.1 ∈ GQ V := Subgroup.mem_subgroupOf.1 hγ
    obtain ⟨u, u', hu, huu', hu'u, hdiag, htri, -⟩ := GlobalTheory.T.rational_flagUnipotent_isotropicBlock_unitriangular D V V₀ ρ d γ.1 hγ' γ.2
    let e : {x // Pj x} ≃ {x // Pj x} :=
      { toFun := fun x => ⟨x.1 * u, (hPu u u' huu' hu'u hdiag htri x.1).1 x.2⟩
        invFun := fun x => ⟨x.1 * u', (hPu u u' huu' hu'u hdiag htri (x.1 * u')).2
          (by rw [Matrix.mul_assoc, hu'u, Matrix.mul_one]; exact x.2)⟩
        left_inv := fun x => Subtype.ext (by simp only [Matrix.mul_assoc, huu', Matrix.mul_one])
        right_inv := fun x => Subtype.ext (by simp only [Matrix.mul_assoc, hu'u, Matrix.mul_one]) }
    show ∑' i : {x // Pj x}, Th (γ * n).1 * term ψ d W vS (om ((γ * n).1, 1) Ψ) i.1 =
      ∑' i : {x // Pj x}, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) i.1
    rw [← e.tsum_eq (fun i => Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) i.1)]
    exact tsum_congr fun i => key γ hγ' u hu n i.1
  · intro c γ hγ hγM n
    have hγ' : γ.1 ∈ GQ V := Subgroup.mem_subgroupOf.1 hγ
    obtain ⟨u, u', hu, huu', hu'u, hdiag, htri, hfix⟩ := GlobalTheory.T.rational_flagUnipotent_isotropicBlock_unitriangular D V V₀ ρ d γ.1 hγ' γ.2
    have hfu := hfixv u (hfix j (Subgroup.mem_subgroupOf.1 hγM))
    let e : {x // Pj x} ≃ {x // Pj x} :=
      { toFun := fun x => ⟨x.1 * u, (hPu u u' huu' hu'u hdiag htri x.1).1 x.2⟩
        invFun := fun x => ⟨x.1 * u', (hPu u u' huu' hu'u hdiag htri (x.1 * u')).2
          (by rw [Matrix.mul_assoc, hu'u, Matrix.mul_one]; exact x.2)⟩
        left_inv := fun x => Subtype.ext (by simp only [Matrix.mul_assoc, huu', Matrix.mul_one])
        right_inv := fun x => Subtype.ext (by simp only [Matrix.mul_assoc, hu'u, Matrix.mul_one]) }
    have hκ : ∀ x : {x // Pj x}, Classical.choose (e x).2.2.2 = Classical.choose x.2.2.2 := by
      intro x
      have s1 := Classical.choose_spec (e x).2.2.2
      have s0 := Classical.choose_spec x.2.2.2
      exact huniq _ (e x).2.2.1 _ _ s1.1 s1.2.1 s1.2.2 s0.1 s0.2.1
        (by show (x.1 * u) *ᵥ _ = 0; rw [← Matrix.mulVec_mulVec, hfu _ s0.2.1, s0.2.2])
    let e' := e.subtypeEquiv (p := fun x => Classical.choose x.2.2.2 = c) (q := fun x => Classical.choose x.2.2.2 = c)
      (fun x => by rw [hκ x])
    show ∑' i : {i : {x // Pj x} // Classical.choose i.2.2.2 = c}, Th (γ * n).1 * term ψ d W vS (om ((γ * n).1, 1) Ψ) i.1.1 =
      ∑' i : {i : {x // Pj x} // Classical.choose i.2.2.2 = c}, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) i.1.1
    rw [← e'.tsum_eq (fun i => Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) i.1.1)]
    exact tsum_congr fun i => key γ hγ' u hu n i.1.1
  · intro c
    by_cases hc : ∃ x : {x // Pj x}, Classical.choose x.2.2.2 = c
    · obtain ⟨x, hx⟩ := hc
      have s0 := Classical.choose_spec x.2.2.2
      rw [hx] at s0
      have hg : gramQ W x₀ *ᵥ c = 0 := by
        rw [← x.2.1, gramQ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, s0.2.2, Matrix.mulVec_zero,
          Matrix.mulVec_zero]
      obtain ⟨v, u, a, hform, htr, huN, ha, hTu⟩ := hTh.dep j c s0.1 s0.2.1 hg
      refine ⟨⟨u, hle huN⟩, huN, a, ha, fun y hy m hm n => ?_⟩
      have sy := Classical.choose_spec y.2.2.2
      rw [hy] at sy
      have hm' : m.1 ∈ Nfix d j := Subgroup.mem_subgroupOf.1 hm
      show Th (m.1 * u * n.1) * term ψ d W vS (om (m.1 * u * n.1, 1) Ψ) y.1 =
        a * (Th (m.1 * n.1) * term ψ d W vS (om (m.1 * n.1, 1) Ψ) y.1)
      rw [hTu m.1 m.2 n.1 n.2, GlobalTheory.T.transvection_trivial_after_flagUnipotentFixing D hDesc ψ V V₀ W ρ d χV χW om hw vS Ψ hΨ j c s0.2.1 v u hform htr y.1 sy.2.2
        m.1 hm' n.1, mul_assoc]
    · push_neg at hc
      exact ⟨1, one_mem _, 0, zero_ne_one, fun x hx => absurd hx (hc x)⟩

end GlobalTheory.Unf.DepFrames
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DependentFramesFirstRelationMeanZeroStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dependentFrames_firstRelation_mean_zero : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (vN : VolN d) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (Th : GA D V → ℂ), IsBase W x₀ → IsTh ψ d W x₀ Th → ∀ Ψ : WO V W → ℂ, IsThetaFunO ψ V W Ψ → ∀ j : Fin ρ, ∫ n in vN.𝓝, ∑' x : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x = gramQ W x₀ ∧ (∀ a : Fin ρ → D.host.E, (∀ i, j ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) ∧ ∃ a : Fin ρ → D.host.E, a j = 1 ∧ (∀ i, j < i → a i = 0) ∧ x *ᵥ a = 0}, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1 ∂vN.ν = 0 := by
  first | exact @GlobalTheory.Unf.DepFrames.dep_frames_mean_zero | exact GlobalTheory.Unf.DepFrames.dep_frames_mean_zero | (intros; apply GlobalTheory.Unf.DepFrames.dep_frames_mean_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelMeanEqOrbitSumMean
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem mean_theta_orbit : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (vN : VolN d) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (Th : GA D V → ℂ), IsBase W x₀ → IsTh ψ d W x₀ Th → ∀ Ψ : WO V W → ℂ, IsThetaFunO ψ V W Ψ → ∫ n in vN.𝓝, Th n.1 * om (n.1, 1) Ψ 0 ∂vN.ν = ∫ n in vN.𝓝, ∑' x : Orb W x₀, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1 ∂vN.ν := by
  intro D hDesc ψ V V₀ W ρ d χV χW om om' hw hw' vS vN x₀ Th hB hTh Ψ hΨ
  have : Countable D.host.E := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableE
  have : Countable (Matrix (Fin W.rank) (Fin ρ) D.host.E) :=
    inferInstanceAs (Countable (Fin W.rank → Fin ρ → D.host.E))
  have hT := GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hw hw' vS
  have hsum : ∀ n : flagN d, HasSum (term ψ d W vS (om (n.1, 1) Ψ)) (om (n.1, 1) Ψ 0) :=
    fun n => (hT _ (hw.om_pres _ _ hΨ)).2.2.2.2
  have hcont : ∀ x, Continuous fun n : flagN d => term ψ d W vS (om (n.1, 1) Ψ) x := fun x =>
    ((hT Ψ hΨ).2.2.2.1 x).comp (continuous_subtype_val.prodMk continuous_const)
  obtain ⟨C, A, hC⟩ := GlobalTheory.T.thetaTermSeries_summable_moderateGrowth_uniform D ψ V V₀ W ρ d χV χW om om' hw hw' vS Ψ hΨ
  have hbd : ∀ n : flagN d, ∑' x, ‖term ψ d W vS (om (n.1, 1) Ψ) x‖ₑ ≤
      ENNReal.ofReal (C * (height V 1 * quotHeight W 1) ^ A) := fun n => by
    have := hC 1 1 n.1 n.2
    rwa [mul_one] at this
  obtain ⟨K, hK, hcov⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D V ρ d.e (isIsoSub_e d)).1
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (f := fun n : flagN d => Th n.1) hTh.cont.continuousOn
  have hThb : ∀ n : flagN d, ‖Th n.1‖ ≤ M := by
    intro n
    obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov n
    have hγ' : (γ : GA D V) ∈ GQ V := Subgroup.mem_subgroupOf.1 hγ
    have : Th ((γ * k : flagN d) : GA D V) = Th k.1 := hTh.left γ.1 hγ' γ.2 k.1 k.2
    rw [this]
    exact hM k hk
  have hpart : ∀ (S : Set (Matrix (Fin W.rank) (Fin ρ) D.host.E)) (n : flagN d),
      ‖∑' x : S, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1‖ ≤
        M * max (C * (height V 1 * quotHeight W 1) ^ A) 0 := by
    intro S n
    rw [tsum_mul_left, norm_mul]
    refine mul_le_mul (hThb n) ?_ (norm_nonneg _) ((norm_nonneg _).trans (hThb n))
    have h1 : ‖∑' x : S, term ψ d W vS (om (n.1, 1) Ψ) x.1‖ₑ ≤
        ENNReal.ofReal (C * (height V 1 * quotHeight W 1) ^ A) :=
      enorm_tsum_le_tsum_enorm.trans
        ((ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _).trans (hbd n))
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rwa [toReal_enorm, ENNReal.toReal_ofReal'] at h2
  have hmeas : ∀ S : Set (Matrix (Fin W.rank) (Fin ρ) D.host.E),
      AEStronglyMeasurable (fun n : flagN d => ∑' x : S, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1)
        (vN.ν.restrict vN.𝓝) := by
    intro S
    refine aestronglyMeasurable_of_tendsto_ae (Filter.atTop : Filter (Finset S))
      (f := fun s n => ∑ x ∈ s, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1) (fun s => ?_)
      (Filter.Eventually.of_forall fun n => ?_)
    · exact (continuous_finsetSum _ fun x _ => hTh.cont.mul (hcont x.1)).aestronglyMeasurable
    · exact (((hsum n).summable.mul_left (Th n.1)).subtype (fun x => x ∈ S)).hasSum
  have : IsFiniteMeasure (vN.ν.restrict vN.𝓝) :=
    isFiniteMeasure_restrict.2 (by rw [vN.unit.2.2]; exact ENNReal.one_ne_top)
  have hint : ∀ S : Set (Matrix (Fin W.rank) (Fin ρ) D.host.E),
      Integrable (fun n : flagN d => ∑' x : S, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1)
        (vN.ν.restrict vN.𝓝) :=
    fun S => Integrable.of_bound (hmeas S) _ (Filter.Eventually.of_forall (hpart S))

  have h61 := fun x : Matrix (Fin W.rank) (Fin ρ) D.host.E => GlobalTheory.T.dependent_frame_first_column_relation D.host.E W.rank ρ x
  let Sb : Set (Matrix (Fin W.rank) (Fin ρ) D.host.E) := {x | gramQ W x ≠ gramQ W x₀}
  let Sj : Fin ρ → Set (Matrix (Fin W.rank) (Fin ρ) D.host.E) := fun j => {x | gramQ W x = gramQ W x₀ ∧
    ((∀ a : Fin ρ → D.host.E, (∀ i, j ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) ∧
      ∃ a : Fin ρ → D.host.E, a j = 1 ∧ (∀ i, j < i → a i = 0) ∧ x *ᵥ a = 0)}
  have hpt : ∀ n : flagN d, Th n.1 * om (n.1, 1) Ψ 0 =
      (∑' x : Sb, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1) +
      (∑' x : Orb W x₀, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1) +
      ∑ j, ∑' x : Sj j, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1 := by
    intro n
    have hs : Summable fun x => Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x := (hsum n).summable.mul_left _
    rw [← ((hsum n).mul_left (Th n.1)).tsum_eq]
    have ht : ∀ S : Set (Matrix (Fin W.rank) (Fin ρ) D.host.E),
        ∑' x : S, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1 =
          ∑' x, S.indicator (fun x => Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x) x := fun S => tsum_subtype S (fun x => Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x)
    rw [ht, ht, Finset.sum_congr rfl fun j _ => ht (Sj j)]
    rw [← Summable.tsum_finsetSum (fun j _ => hs.indicator _), ← Summable.tsum_add (hs.indicator _) (hs.indicator _),
      ← Summable.tsum_add ((hs.indicator _).add (hs.indicator _)) (summable_sum fun j _ => hs.indicator _)]
    congr 1
    funext x
    by_cases hg : gramQ W x = gramQ W x₀
    · have h1 : x ∉ Sb := fun h => h hg
      rw [Set.indicator_of_notMem h1, zero_add]
      by_cases hl : LinearIndependent D.host.E x.transpose
      · have h2 : x ∈ Orb W x₀ := ⟨hl, hg⟩
        have h3 : ∀ j, x ∉ Sj j := fun j h => (h61 x).1.2 ⟨j, h.2⟩ hl
        rw [Set.indicator_of_mem h2, Finset.sum_eq_zero fun j _ => Set.indicator_of_notMem (h3 j) _, add_zero]
      · have h2 : x ∉ Orb W x₀ := fun h => hl h.1
        obtain ⟨j, hj⟩ := (h61 x).1.1 hl
        rw [Set.indicator_of_notMem h2, zero_add, Finset.sum_eq_single j
          (fun j' _ hj' => Set.indicator_of_notMem (fun (h : x ∈ Sj j') => hj' ((h61 x).2.1 j' j h.2 hj)) _)
          (fun h => (h (Finset.mem_univ j)).elim), Set.indicator_of_mem (show x ∈ Sj j from ⟨hg, hj⟩)]
    · have h1 : x ∈ Sb := hg
      have h2 : x ∉ Orb W x₀ := fun h => hg h.2
      have h3 : ∀ j, x ∉ Sj j := fun j h => hg h.1
      rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2,
        Finset.sum_eq_zero fun j _ => Set.indicator_of_notMem (h3 j) _, add_zero, add_zero]
  have e1 : ∫ n in vN.𝓝, ∑' x : Sb, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1 ∂vN.ν = 0 :=
    GlobalTheory.T.unfolding_only_baseGram_rational_points_contribute D ψ V V₀ W ρ d χV χW om om' hw hw' vS vN x₀ Th hB hTh Ψ hΨ
  have e2 : ∀ j, ∫ n in vN.𝓝, ∑' x : Sj j, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1 ∂vN.ν = 0 :=
    GlobalTheory.T.dependentFrames_firstRelation_mean_zero D hDesc ψ V V₀ W ρ d χV χW om om' hw hw' vS vN x₀ Th hB hTh Ψ hΨ
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add ?_ ?_, integral_add ?_ ?_,
    integral_finsetSum _ ?_, e1, Finset.sum_eq_zero fun j _ => e2 j, zero_add, add_zero]
  · exact fun j _ => hint _
  · exact hint _
  · exact hint _
  · exact (hint _).add (hint _)
  · exact integrable_finsetSum _ fun j _ => hint _

end GlobalTheory.Unf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelMeanEqOrbitSumMeanStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKernel_mean_eq_orbit_sum_mean : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (vN : VolN d) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (Th : GA D V → ℂ), IsBase W x₀ → IsTh ψ d W x₀ Th → ∀ Ψ : WO V W → ℂ, IsThetaFunO ψ V W Ψ → ∫ n in vN.𝓝, Th n.1 * om (n.1, 1) Ψ 0 ∂vN.ν = ∫ n in vN.𝓝, ∑' x : Orb W x₀, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1 ∂vN.ν := by
  first | exact @GlobalTheory.Unf.mean_theta_orbit | exact GlobalTheory.Unf.mean_theta_orbit | (intros; apply GlobalTheory.Unf.mean_theta_orbit <;> assumption)
end
