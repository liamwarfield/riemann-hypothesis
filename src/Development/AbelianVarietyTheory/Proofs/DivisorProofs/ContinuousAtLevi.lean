module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
public import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiRegularAlongOfEtale
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnramifiedNonsplitExistsConjInvolutionUniformise
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BtOrderIsHopfOrderNoetherian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePartBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterEmbeddingCompat
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTripleTrivialOverRealsOfGramCongruent
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtLevi
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open ReciprocityTheory.L2DbarEstimates (V leviV)
open GlobalTheory GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CxPts

namespace GlobalTheory.SemiPosBir

variable {k : Type} [CommRing k] {X Z : Scheme.{0}} {p : X ⟶ Sp k} {q : Z ⟶ Sp k} {σ : k →+* ℂ}
  {D : ℕ}


open ReciprocityTheory.L2DbarEstimates in
theorem continuousAt_levi {g : V D → ℂ} {x : V D} (hg : ContDiffAt ℝ 2 g x) (ξ : Fin D → ℂ) :
    ContinuousAt (fun v => leviV D g v ξ) x := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ g) x := hg.fderiv_right (by norm_num)
  have h2 : ∀ l, ContDiffAt ℝ 1 (wdb D l g) x := fun l =>
    ((h1.clm_apply contDiffAt_const).add
      (contDiffAt_const.mul (h1.clm_apply contDiffAt_const))).div_const 2
  have h3 : ∀ j l, ContinuousAt (wd D j (wdb D l g)) x := fun j l => by
    have h4 : ContinuousAt (fderiv ℝ (wdb D l g)) x :=
      ((h2 l).fderiv_right (m := 0) (by norm_num)).continuousAt
    exact ((h4.clm_apply continuousAt_const).sub
      (continuousAt_const.mul (h4.clm_apply continuousAt_const))).div_const 2
  unfold leviV
  exact tendsto_finsetSum _ fun j _ => tendsto_finsetSum _ fun l _ =>
    ((h3 j l).mul continuousAt_const).mul continuousAt_const

theorem ae_mem [IsDomain k] [IsIntegral X] (hσ : Function.Injective σ) (c : AlgChart p σ D)
    {U : X.Opens} (hU : (U : Set X).Nonempty) :
    ∀ᵐ v : V D, v ∈ c.e.target → c.e.symm v ∈ ptsIn p σ U := by
  rcases c.e.source.eq_empty_or_nonempty with h | ⟨y, hy⟩
  · exact .of_forall fun v hv => absurd (c.e.map_target hv) (h ▸ notMem_empty _)
  have hy' := mem_ptsIn.1 (c.source_subset hy)
  obtain ⟨x, hx, hx'⟩ := nonempty_preirreducible_inter U.isOpen c.U.isOpen hU ⟨_, hy'⟩
  obtain ⟨a, ha, ha'⟩ := c.affine.exists_basicOpen_le (V := U) ⟨x, hx⟩ hx'
  have h0 : a ≠ 0 := by
    rintro rfl
    rw [Scheme.basicOpen_zero] at ha'
    exact ha'
  have : Nonempty c.U := ⟨⟨_, hy'⟩⟩
  let φ := MvPolynomial.eval₂Hom (algX p c.U) c.x
  let : Algebra (MvPolynomial (Fin D) k) Γ(X, c.U) := φ.toAlgebra
  have : Algebra.Etale (MvPolynomial (Fin D) k) Γ(X, c.U) := c.etale
  have h₁ := isAlgebraic_of_flat_of_formallyUnramified (MvPolynomial (Fin D) k) Γ(X, c.U)
  obtain ⟨r, hr, b, hb⟩ := (h₁.isAlgebraic a).exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero h0)
  have hr' : MvPolynomial.map σ r ≠ 0 :=
    (map_ne_zero_iff _ (MvPolynomial.map_injective σ hσ)).2 hr
  filter_upwards [ReciprocityTheory.MultiplicativeHeights.ae_eval_ne_zero_linear (volume : Measure (V D))
    (WithLp.linearEquiv 2 ℂ (Fin D → ℂ)) _ hr'] with v hv hvt
  have hs := c.e.map_target hvt
  have hz := c.source_subset hs
  refine ptsIn_mono ha ((mem_ptsIn_basicOpen hz a).2 fun e => hv ?_)
  have e₁ : (evHom hz).comp φ = (MvPolynomial.eval (WithLp.linearEquiv 2 ℂ (Fin D → ℂ) v)).comp
      (MvPolynomial.map σ) := by
    refine MvPolynomial.ringHom_ext (fun t => ?_) fun i => ?_
    · simp only [φ, RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.map_C,
        MvPolynomial.eval_C, ← ev_eq, ev_algX hz]
    · simp only [φ, RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.map_X,
        MvPolynomial.eval_X, ← ev_eq, ← c.apply_eq _ hs, c.e.right_inv hvt]
      rfl
  have e₂ : φ r = a * b := hb
  refine (RingHom.congr_fun e₁ r).symm.trans ?_
  rw [RingHom.comp_apply, e₂, ← ev_eq, ev_mul, e, zero_mul]


variable (D) in
def PosOn (f : CxPts p σ → ℝ) (S : Set (CxPts p σ)) : Prop :=
  ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source ∩ S, ∀ ξ : Fin D → ℂ,
    0 ≤ (leviV D (fun v => (f (c.e.symm v) : ℂ)) (c.e y) ξ).re

theorem PosOn.of_inter [IsDomain k] [IsIntegral X] (hσ : Function.Injective σ)
    {f : CxPts p σ → ℝ} {S : Set (CxPts p σ)} (hS : IsOpen S) (hf : ∀ y ∈ S, CInfAt f y)
    {U : X.Opens} (hU : (U : Set X).Nonempty) (h : PosOn D f (S ∩ ptsIn p σ U)) :
    PosOn D f S := fun c y hy ξ => by
  have ho := (isOpen_over c.e hS).mem_nhds (mem_over c.e hy.1 hy.2)
  have hd : ContDiffAt ℝ 2 (fun v => f (c.e.symm v)) (c.e y) :=
    ((contDiffOn_chart hf c).contDiffAt ho).of_le (by norm_cast)
  have hc := Complex.continuous_re.continuousAt.comp
    (continuousAt_levi (Complex.ofRealCLM.contDiff.contDiffAt.comp _ hd) ξ)
  have hfr := (mem_closure_iff_frequently.1 ((Measure.dense_of_ae (ae_mem hσ c hU)) (c.e y)))
  refine isClosed_Ici.mem_of_frequently_of_tendsto ((hfr.and_eventually ho).mono ?_) hc
  rintro v ⟨h₁, h₂, h₃⟩
  have := h c _ ⟨c.e.map_target h₂, h₃, h₁ h₂⟩ ξ
  rwa [c.e.right_inv h₂] at this

theorem levi_pull {j : Z ⟶ X} (hj : j ≫ p = q) (f : CxPts p σ → ℝ) (c : AlgChart p σ D)
    (c' : AlgChart q σ D) (e : c'.U ≤ j ⁻¹ᵁ c.U) (hx : ∀ a, c'.x a = (j.appLE _ _ e).hom (c.x a))
    {z : CxPts q σ} (hz : z ∈ c'.e.source) (hz' : PtsOver.map j hj _ z ∈ c.e.source)
    (ξ : Fin D → ℂ) :
    leviV D (fun v => (f (PtsOver.map j hj _ (c'.e.symm v)) : ℂ)) (c'.e z) ξ =
      leviV D (fun v => (f (c.e.symm v) : ℂ)) (c.e (PtsOver.map j hj _ z)) ξ := by
  have he (w) (hw : w ∈ c'.e.source) (hw' : PtsOver.map j hj (spMap σ) w ∈ c.e.source) :
      c'.e w = c.e (PtsOver.map j hj (spMap σ) w) := by
    ext a
    rw [c'.apply_eq w hw, c.apply_eq _ hw', hx]
    exact valR_appLE w.1 j e (c'.source_subset hw) _
  have hS : IsOpen (c'.e.source ∩ PtsOver.map j hj (spMap σ) ⁻¹' c.e.source) :=
    c'.e.open_source.inter (c.e.open_source.preimage (PtsOver.continuous_map j hj _))
  rw [← he z hz hz']
  refine ReciprocityTheory.L2DbarEstimates.leviV_congr ?_ ξ
  filter_upwards [(isOpen_over c'.e hS).mem_nhds (mem_over c'.e hz (S := _) ⟨hz, hz'⟩)] with v hv
  have e₁ : c.e.symm v = PtsOver.map j hj _ (c'.e.symm v) := by
    have := he _ hv.2.1 hv.2.2
    rw [c'.e.right_inv hv.1] at this
    exact (congrArg c.e.symm this).trans (c.e.left_inv hv.2.2)
  rw [e₁]

theorem appLE_comp_eval {j : Z ⟶ X} (hj : j ≫ p = q) {U : X.Opens} {W : Z.Opens}
    (e : W ≤ j ⁻¹ᵁ U) (x : Fin D → Γ(X, U)) :
    (j.appLE U W e).hom.comp (MvPolynomial.eval₂Hom (algX p U) x) =
      MvPolynomial.eval₂Hom (algX q W) fun a => (j.appLE U W e).hom (x a) := by
  subst hj
  refine MvPolynomial.ringHom_ext (fun t => ?_) fun i => ?_
  · rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
    exact congrArg (fun g : Γ(Sp k, ⊤) ⟶ Γ(Z, W) => g.hom ((Scheme.ΓSpecIso (.of k)).inv.hom t))
      (Scheme.Hom.appLE_comp_appLE j p ⊤ U W le_top e)
  · rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']

theorem exists_map_eq (j : Z ⟶ X) [IsOpenImmersion j] (hj : j ≫ p = q) {y : CxPts p σ}
    (hy : y ∈ ptsIn p σ j.opensRange) : ∃ z : CxPts q σ, PtsOver.map j hj _ z = y := by
  have H : Set.range y.1 ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    exact hy (x := x) trivial
  refine ⟨⟨IsOpenImmersion.lift j y.1 H, ?_⟩, Subtype.ext (IsOpenImmersion.lift_fac _ _ _)⟩
  rw [← hj, ← Category.assoc, IsOpenImmersion.lift_fac]
  exact y.2

theorem PosOn.pull (j : Z ⟶ X) [IsOpenImmersion j] (hj : j ≫ p = q) {f : CxPts p σ → ℝ}
    {S : Set (CxPts p σ)} (h : PosOn D f S) :
    PosOn D (fun w => f (PtsOver.map j hj _ w)) (PtsOver.map j hj (spMap σ) ⁻¹' S) :=
  fun c' z hz ξ => by
  have e : c'.U ≤ j ⁻¹ᵁ j ''ᵁ c'.U := (j.preimage_image_eq _).ge
  have hi : IsIso (j.appLE _ _ e) := by
    rw [← Scheme.Hom.appIso_hom']
    infer_instance
  have hb := ConcreteCategory.bijective_of_isIso (j.appLE _ _ e)
  choose x hx using fun a => hb.2 (c'.x a)
  have h₁ := appLE_comp_eval hj e x
  have h₂ : (MvPolynomial.eval₂Hom (algX p (j ''ᵁ c'.U)) x).Etale := by
    refine (RingHom.Etale.respectsIso.cancel_right_isIso (CommRingCat.ofHom
      (MvPolynomial.eval₂Hom (algX p (j ''ᵁ c'.U)) x)) (j.appLE _ _ e)).1 ?_
    change ((j.appLE _ _ e).hom.comp (MvPolynomial.eval₂Hom (algX p (j ''ᵁ c'.U)) x)).Etale
    rw [h₁, show (fun a => (j.appLE _ _ e).hom (x a)) = c'.x from funext hx]
    exact c'.etale
  obtain ⟨c, hc, hU, hcx⟩ := AlgChart.exists_of_etale (y := PtsOver.map j hj (spMap σ) z)
    (c'.affine.image_of_isOpenImmersion j) x h₂
    (mem_ptsIn.2 ⟨_, mem_ptsIn.1 (c'.source_subset hz.1), rfl⟩)
  have key : ∀ (U : X.Opens) (hU : c.U = U) (e : c'.U ≤ j ⁻¹ᵁ U) (x : Fin D → Γ(X, U)),
      c.x = hU ▸ x → (∀ a, (j.appLE _ _ e).hom (x a) = c'.x a) →
      ∃ e : c'.U ≤ j ⁻¹ᵁ c.U, ∀ a, c'.x a = (j.appLE _ _ e).hom (c.x a) := by
    rintro _ rfl e x h₁ h₂
    exact ⟨e, fun a => by rw [h₁]; exact (h₂ a).symm⟩
  obtain ⟨e', hx'⟩ := key _ hU e x hcx hx
  rw [levi_pull hj f c c' e' hx' hz.1 hc]
  exact h c _ ⟨hc, hz.2⟩ ξ

theorem PosOn.of_pull (j : Z ⟶ X) [IsOpenImmersion j] (hj : j ≫ p = q) {f : CxPts p σ → ℝ}
    {S : Set (CxPts p σ)}
    (h : PosOn D (fun w => f (PtsOver.map j hj _ w)) (PtsOver.map j hj (spMap σ) ⁻¹' S)) :
    PosOn D f (S ∩ ptsIn p σ j.opensRange) := fun c y hy ξ => by
  obtain ⟨z, rfl⟩ := exists_map_eq j hj hy.2.2
  obtain ⟨W, hW, hzW, e⟩ := exists_isAffineOpen_le z.1 (V := j ⁻¹ᵁ c.U) (c.source_subset hy.1)
  have h₂ : (MvPolynomial.eval₂Hom (algX q W) fun a => (j.appLE _ W e).hom (c.x a)).Etale := by
    rw [← appLE_comp_eval hj e]
    exact RingHom.Etale.stableUnderComposition _ _ c.etale
      (HasRingHomProperty.appLE @Etale j inferInstance ⟨c.U, c.affine⟩ ⟨W, hW⟩ e)
  obtain ⟨c', hc, rfl, hcx⟩ := AlgChart.exists_of_etale (y := z) hW _ h₂ hzW
  rw [← levi_pull hj f c c' e (congrFun hcx) hc hy.1]
  exact h c' _ ⟨hc, hy.2.1⟩ ξ

theorem posOn_iff_pull [IsDomain k] [IsIntegral X] (hσ : Function.Injective σ) (j : Z ⟶ X)
    [IsOpenImmersion j] [Nonempty Z] (hj : j ≫ p = q) {f : CxPts p σ → ℝ}
    {S : Set (CxPts p σ)} (hS : IsOpen S) (hf : ∀ y ∈ S, CInfAt f y) : PosOn D f S ↔
    PosOn D (fun w => f (PtsOver.map j hj _ w)) (PtsOver.map j hj (spMap σ) ⁻¹' S) :=
  ⟨fun h => h.pull j hj, fun h => (h.of_pull j hj).of_inter hσ hS hf (range_nonempty _)⟩

theorem semiPos_iff_pull : ∀ (k : Type) [CommRing k] (X X' : Scheme.{0}) (p : X ⟶ Sp k) (q : X' ⟶ Sp k) (D : ℕ), IsArithVar p D → IsArithVar q D → ∀ (π : X' ⟶ X) (hπ : π ≫ p = q) (U : X.Opens), (U : Set X).Nonempty → IsIso (π ∣_ U) → ∀ L : HermLB p, (L.SemiPos D ↔ (L.pull π hπ).SemiPos D) := by
  intro k _ X X' p q D hp hq π hπ U hU hi L
  have := hp.isDomain
  have := hp.finite
  have := hp.isIntegral
  have := hq.isIntegral
  refine forall_congr' fun σ => ?_
  have hσ : Function.Injective σ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    rw [Ideal.under_def, RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    exact RingHom.injective_int _
  have : Nonempty U.toScheme := hU.to_subtype
  have : Nonempty (π ⁻¹ᵁ U).toScheme := (π ∣_ U).surjective.nonempty
  have : IsOpenImmersion ((π ⁻¹ᵁ U).ι ≫ π) := by
    rw [← morphismRestrict_ι]
    infer_instance
  have key (i : L.B.ι) : PosOn D ((L.φ σ).φ i) (ptsIn p σ (L.B.U i)) ↔
      PosOn D (fun w => (L.φ σ).φ i (PtsOver.map π hπ _ w))
        (PtsOver.map π hπ (spMap σ) ⁻¹' ptsIn p σ (L.B.U i)) := by
    rw [posOn_iff_pull hσ ((π ⁻¹ᵁ U).ι ≫ π) rfl (isOpen_ptsIn _) (L.cInf σ i),
      posOn_iff_pull hσ (π ⁻¹ᵁ U).ι (q := ((π ⁻¹ᵁ U).ι ≫ π) ≫ p) (by rw [Category.assoc, hπ])
        ((isOpen_ptsIn _).preimage (PtsOver.continuous_map π hπ _))
        fun y hy => CInfAt.pull π hπ (L.cInf σ i _ hy)]
    have e (w : CxPts (((π ⁻¹ᵁ U).ι ≫ π) ≫ p) σ) : PtsOver.map ((π ⁻¹ᵁ U).ι ≫ π) rfl _ w =
        PtsOver.map π hπ _ (PtsOver.map (π ⁻¹ᵁ U).ι (by rw [Category.assoc, hπ]) _ w) :=
      Subtype.ext (Category.assoc _ _ _).symm
    rw [funext e]
    simp only [e]
    rfl
  have e₁ (J : (L.B.pull π).ι) : ptsIn q σ ((L.B.pull π).U J) =
      PtsOver.map π hπ (spMap σ) ⁻¹' ptsIn p σ (L.B.U (J PUnit.unit)) := Set.ext fun z => by
    rw [mem_preimage, mem_ptsIn, mem_ptsIn]
    exact ⟨fun h => mem_iInter.1 h PUnit.unit, fun h => mem_iInter.2 fun _ => h⟩
  have e₂ (J : (L.B.pull π).ι) : ((L.φ σ).pull π hπ).φ J =
      fun w => (L.φ σ).φ (J PUnit.unit) (PtsOver.map π hπ _ w) :=
    funext ((L.φ σ).pull_φ π hπ J)
  change (∀ i, PosOn D ((L.φ σ).φ i) (ptsIn p σ (L.B.U i))) ↔
    ∀ J, PosOn D (((L.φ σ).pull π hπ).φ J) (ptsIn q σ ((L.B.pull π).U J))
  simp only [e₁, e₂, key]
  exact ⟨fun h J => h _, fun h i => h fun _ => i⟩

end GlobalTheory.SemiPosBir
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishesToPullChartIffOfFlat
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Vanishing

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX isPushout_sections)
open ReciprocityTheory.AnForm.R (ds_stalkId_eq_map)
open ReciprocityTheory.AnForm.R.FinalTheorems (stalkId)
open GlobalTheory.LB GlobalTheory.CechPic GlobalTheory.TangentOrigin
open GlobalTheory.Adelic (cutIdeal)
open H0

variable {k k' : Type} [CommRing k] [CommRing k'] {Y Y' T : Scheme.{0}} {φ : Y' ⟶ Y}

section Ideal

variable {L : LB Y} {L' : LB Y'} {ι : Type}

theorem secGer_chartSec (l : ChartPull L' L φ) (s : ι → L.Sec) (j : L'.ι) (z : Y') (hj : z ∈ L'.U j)
    (i : ι) : secGer (fun i => chartSec l (s i)) j z hj i =
      (φ.stalkMap z).hom (secGer s (l.idx j) (φ z) (l.le j hj) i) :=
  ger_appLE φ (l.le j) z hj _

theorem stalkId_cutIdeal_chartSec (hL : L.IsLB) (hL' : L'.IsLB) (l : ChartPull L' L φ)
    (s : ι → L.Sec) (z : Y') : stalkId (cutIdeal hL' fun i => chartSec l (s i)) z =
      (stalkId (cutIdeal hL s) (φ z)).map (φ.stalkMap z).hom := by
  obtain ⟨j, hj⟩ := exists_chart hL' z
  rw [stalkId_cutIdeal hL' _ j z hj, stalkId_cutIdeal hL s _ _ (l.le j hj), Ideal.map_span,
    ← Set.range_comp]
  exact congrArg (fun f => Ideal.span (Set.range f)) (funext (secGer_chartSec l s j z hj))

theorem stalkId_cutIdeal_secPull (hL : L.IsLB) (s : ι → L.Sec) (z : Y') :
    stalkId (cutIdeal (LB.isLB_pull hL φ) fun i => secPull (s i) φ) z =
      (stalkId (cutIdeal hL s) (φ z)).map (φ.stalkMap z).hom :=
  stalkId_cutIdeal_chartSec hL _ (GlobalTheory.chartPullPull L φ) s z

variable {I : Y.IdealSheafData} {I' : Y'.IdealSheafData}

theorem le_ker_iff_stalk (t : T ⟶ Y) :
    I ≤ t.ker ↔ ∀ z, stalkId I (t z) ≤ RingHom.ker (t.stalkMap z).hom := by
  refine ⟨fun h z => ?_, fun h => Scheme.IdealSheafData.le_ofIdeals_iff.2 fun U a ha => ?_⟩
  · obtain ⟨W, hW, -⟩ := exists_affine (U := ⊤) (y := t z) trivial
    rw [ds_stalkId_eq_map I W _ hW, Ideal.map_le_iff_le_comap]
    intro a ha
    have h₀ : (t.app W.1).hom a = 0 := t.ideal_ker_le W (h W ha)
    exact (Scheme.Hom.germ_stalkMap_apply t _ z hW a).trans ((congrArg _ h₀).trans (map_zero _))
  · refine fun_ext_ger (U := t ⁻¹ᵁ U.1) fun z hz => ?_
    have := h z ((mem_ideal_iff_ger I U a).1 ha _ hz)
    exact (Scheme.Hom.germ_stalkMap_apply t _ z hz a).symm.trans (this.trans (map_zero _).symm)

variable (hI : ∀ z, stalkId I' z = (stalkId I (φ z)).map (φ.stalkMap z).hom)
include hI

theorem le_ker_iff_comp (t : T ⟶ Y') : I' ≤ t.ker ↔ I ≤ (t ≫ φ).ker := by
  rw [le_ker_iff_stalk, le_ker_iff_stalk]
  refine forall_congr' fun z => ?_
  rw [hI, Ideal.map_le_iff_le_comap, RingHom.comap_ker, Scheme.Hom.stalkMap_comp]
  rfl

theorem le_map_of_stalk : I ≤ I'.map φ := (le_ker_iff_comp hI _).1 I'.ker_subschemeι.ge

theorem eq_comap_of_stalk : I' = I.comap φ :=
  le_antisymm ((le_ker_iff_comp hI _).2 (by
      rw [Limits.pullback.condition]
      exact I.ker_subschemeι.ge.trans (Scheme.Hom.le_ker_comp _ _)))
    (Scheme.IdealSheafData.le_map_iff_comap_le.1 (le_map_of_stalk hI))

end Ideal

section Order

variable {p : Y ⟶ Sp k} {p' : Y' ⟶ Sp k'} {σ : k →+* k'} {B : LB Y} {B' : LB Y'} {O : Y.Opens}
  {I : Y.IdealSheafData} {I' : Y'.IdealSheafData} {n : ℕ}
  (hI : ∀ z, stalkId I' z = (stalkId I (φ z)).map (φ.stalkMap z).hom)




end Order

section On

variable {S S' : Scheme.{0}} {u : S ⟶ Y} {u' : S' ⟶ Y'} {ψ : S' ⟶ S}

theorem stalkMap_square (hψ : ψ ≫ u = u' ≫ φ) (z : S') {U : Y.Opens} (h : u (ψ z) ∈ U)
    (h' : φ (u' z) ∈ U) (x : Γ(Y, U)) :
    (ψ.stalkMap z).hom ((u.stalkMap (ψ z)).hom (ger _ h x)) =
      (u'.stalkMap z).hom ((φ.stalkMap (u' z)).hom (ger _ h' x)) := by
  have key {r r' : S' ⟶ Y} (e : r = r') (h : r z ∈ U) (h' : r' z ∈ U) :
      (r.stalkMap z).hom (ger _ h x) = (r'.stalkMap z).hom (ger _ h' x) := by
    subst e
    rfl
  have := key hψ h h'
  rwa [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at this

theorem pt_square (hψ : ψ ≫ u = u' ≫ φ) (z : S') : u (ψ z) = φ (u' z) :=
  congrArg (fun r : S' ⟶ Y => r z) hψ

theorem exists_stalkHom (hψ : ψ ≫ u = u' ≫ φ) (z : S') :
    ∃ θ : Y.presheaf.stalk (u (ψ z)) →+* Y'.presheaf.stalk (u' z),
      (∀ (U : Y.Opens) h h' (x : Γ(Y, U)),
        θ (ger _ h x) = (φ.stalkMap (u' z)).hom (ger _ h' x)) ∧
      ∀ x, (u'.stalkMap z).hom (θ x) = (ψ.stalkMap z).hom ((u.stalkMap (ψ z)).hom x) := by
  have key (y : Y) (e : y = φ (u' z)) : ∃ θ : Y.presheaf.stalk y →+* Y'.presheaf.stalk (u' z),
      ∀ (U : Y.Opens) h h' (x : Γ(Y, U)),
        θ (ger _ h x) = (φ.stalkMap (u' z)).hom (ger _ h' x) := by
    subst e
    exact ⟨_, fun _ _ _ _ => rfl⟩
  obtain ⟨θ, hθ⟩ := key _ (pt_square hψ z)
  refine ⟨θ, hθ, fun x => ?_⟩
  obtain ⟨U, hU, x, rfl⟩ := Y.presheaf.germ_exist x
  exact (congrArg _ (hθ U hU (pt_square hψ z ▸ hU) x)).trans (stalkMap_square hψ z hU _ x).symm

variable {B : LB Y} {B' : LB Y'}

def chartPullOn (a : ChartPull B' B φ) (hψ : ψ ≫ u = u' ≫ φ) :
    ChartPull (B'.pull u') (B.pull u) ψ where
  idx J _ := a.idx (J PUnit.unit)
  le J z hz := mem_pull.2 ((pt_square hψ z).symm ▸ a.le _ (mem_pull.1 hz))
  g z J J' hJ hJ' := by
    have h := memInf (a.le _ (mem_pull.1 hJ)) (a.le _ (mem_pull.1 hJ'))
    have h' : u (ψ z) ∈ B.U (a.idx (J PUnit.unit)) ⊓ B.U (a.idx (J' PUnit.unit)) :=
      (pt_square hψ z).symm ▸ h
    refine ((tr_pull B' u' z hJ hJ').trans ?_).trans (gm_pull_g B u ψ z (fun _ => _) (fun _ => _)
      (mem_pull.2 h'.1) (mem_pull.2 h'.2)).symm
    rw [tr_chartPull a _ (mem_pull.1 hJ) (mem_pull.1 hJ'), hψ]
    refine Units.ext (Eq.trans ?_ (gm_val (u' ≫ φ) z _ h _).symm)
    refine (congrArg (fun x => (u'.stalkMap z).hom ((φ.stalkMap (u' z)).hom x))
      (val_tr B _ h)).trans ?_
    refine Eq.trans ?_ (Scheme.Hom.germ_stalkMap_apply (u' ≫ φ) _ z h _)
    rw [Scheme.Hom.stalkMap_comp]
    rfl

variable {p : Y ⟶ Sp k} {p' : Y' ⟶ Sp k'} {σ : k →+* k'} {O : Y.Opens} {W : Y'.Opens}
  {I : Y.IdealSheafData} {I' : Y'.IdealSheafData} {ψ : I'.subscheme ⟶ I.subscheme}

def pullOn (a : ChartPull B' B φ) (w : φ ≫ p = p' ≫ spMap σ)
    (hψ : ψ ≫ I.subschemeι = I'.subschemeι ≫ φ) : sectionsOnClosedSubscheme p B I →ₛₗ[σ] sectionsOnClosedSubscheme p' B' I' :=
  pullChart (chartPullOn a hψ) (by rw [← Category.assoc, hψ, Category.assoc, w, Category.assoc])
    le_top

theorem germ_pullOn (a : ChartPull B' B φ) (w : φ ≫ p = p' ≫ spMap σ)
    (hψ : ψ ≫ I.subschemeι = I'.subschemeι ≫ φ) (g : sectionsOnClosedSubscheme p B I) (j : (B'.pull I'.subschemeι).ι)
    (z : I'.subscheme) (hj : z ∈ (B'.pull I'.subschemeι).U j) :
    germ j z (Opens.mem_top z) hj (pullOn a w hψ g) = (ψ.stalkMap z).hom
      (germ (fun _ => a.idx (j PUnit.unit)) (ψ z) (Opens.mem_top _)
        ((chartPullOn a hψ).le j hj) g) :=
  germ_pullChart _ _ _ g j z _ hj

end On

theorem LeadAt.map {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    {ι : Type} [Finite ι] {π : R →+* S} {π' : R' →+* S'} {x : ι → R} {a : ℕ} {f : R}
    {γ : MonoDeg ι a → S} (h : LeadAt π x f γ) (θ : R →+* R') (η : S →+* S')
    (e : ∀ r, π' (θ r) = η (π r)) : LeadAt π' (fun i => θ (x i)) (θ f) fun α => η (γ α) := by
  obtain ⟨m, hm, hf⟩ := h
  refine ⟨fun α => θ (m α), fun α => by rw [e, hm], ?_⟩
  have := Ideal.mem_map_of_mem θ hf
  rw [Ideal.map_pow, Ideal.map_span, ← Set.range_comp] at this
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sub, map_sum, map_mul, map_monoVal] at this
  exact this

section Lead

variable {p : Y ⟶ Sp k} {p' : Y' ⟶ Sp k'} {σ : k →+* k'} {L M : LB Y} {L' M' : LB Y'}
  {hL : L.IsLB} {hL' : L'.IsLB} {ι : Type} [Finite ι] {s : ι → L.Sec} {O : Y.Opens} {W : Y'.Opens}

theorem HasLead.pullChart (m : ChartPull M' M φ) (l : ChartPull L' L φ) (w : φ ≫ p = p' ≫ spMap σ)
    {ψ : (cutIdeal hL' fun i => chartSec l (s i)).subscheme ⟶ (cutIdeal hL s).subscheme}
    (hψ : ψ ≫ (cutIdeal hL s).subschemeι = (cutIdeal hL' fun i => chartSec l (s i)).subschemeι ≫ φ)
    (hW : W ≤ φ ⁻¹ᵁ O) {hO : SuppIn O (cutIdeal hL s)}
    (hO' : SuppIn W (cutIdeal hL' fun i => chartSec l (s i))) {n d : ℤ} {a : ℕ} {h : n + a = d}
    {f : H0 p (tw M L d) O} {c : MonoDeg ι a → sectionsOnClosedSubscheme p (tw M L n) (cutIdeal hL s)}
    (e : HasLead hL s hO h f c) :
    HasLead hL' _ hO' h (pullChart (chartPullTwist m l d) w hW f)
      fun α => pullOn (chartPullTwist m l n) w hψ (c α) := fun z i j hi hj => by
  obtain ⟨θ, hθ, hθ'⟩ := exists_stalkHom hψ z
  have := (e (ψ z) (m.idx i) (l.idx j) ((pt_square hψ z).symm ▸ m.le i hi)
    ((pt_square hψ z).symm ▸ l.le j hj)).map θ (ψ.stalkMap z).hom hθ'
  convert this using 1
  · exact funext fun t => (secGer_chartSec l s j _ hj t).trans (hθ _ _ _ _).symm
  · exact (germ_pullChart _ _ _ _ _ _ _ _).trans (hθ _ _ _ _).symm
  · exact funext fun α => germ_pullOn _ _ _ _ _ _ _

end Lead

section Symbol

variable {p : Y ⟶ Sp k} {p' : Y' ⟶ Sp k'} {σ : k →+* k'} (H : IsPullback φ p' p (spMap σ))




variable {D : ℕ} [SmoothOfRelativeDimension D p] [SmoothOfRelativeDimension D p'] (K : CanonLB p D)
  {L A B : LB Y} {L' A' B' : LB Y'} (l : ChartPull L' L φ) (a : ChartPull A' A φ)
  (b : ChartPull B' B φ) (s : Fin D → L.Sec)

abbrev pullQuotSec (e : (LB.div A (tw B L D)).Sec) : (LB.div A' (tw B' L' D)).Sec :=
  chartSec (chartPullQuot a (chartPullTwist b l D)) e

variable (hL : L.IsLB) (hA : A.IsLB) (hB : B.IsLB) (hL' : L'.IsLB) (hA' : A'.IsLB) (hB' : B'.IsLB)
  (e : (LB.div A (tw B L D)).Sec)


variable (hS : Etale ((cutIdeal hL s).subschemeι ≫ p))
  (hS' : Etale ((cutIdeal hL' fun t => chartSec l (s t)).subschemeι ≫ p'))
  (he : SuppIn (nonzeroLocus e) (cutIdeal hL s))
  (he' : SuppIn (nonzeroLocus (pullQuotSec l a b e)) (cutIdeal hL' fun t => chartSec l (s t)))
  {ψ : (cutIdeal hL' fun t => chartSec l (s t)).subscheme ⟶ (cutIdeal hL s).subscheme}
  (hψ : ψ ≫ (cutIdeal hL s).subschemeι = (cutIdeal hL' fun t => chartSec l (s t)).subschemeι ≫ φ)

variable {O : Y.Opens} {W : Y'.Opens} (hW : W ≤ φ ⁻¹ᵁ O) (hO : SuppIn O (cutIdeal hL s))
  (hO' : SuppIn W (cutIdeal hL' fun t => chartSec l (s t)))

end Symbol

section Field

variable {E E' : Type} [Field E] [Field E'] {σ : E →+* E'} {p : Y ⟶ Sp E} {p' : Y' ⟶ Sp E'}
  (H : IsPullback φ p' p (spMap σ)) {L : LB Y} (hL : L.IsLB)




section Order

variable {ι : Type} (s : ι → L.Sec) {B : LB Y} {B' : LB Y'} {O : Y.Opens} {n : ℕ}

end Order

variable {D : ℕ} [SmoothOfRelativeDimension D p] [SmoothOfRelativeDimension D p'] (K : CanonLB p D)
  {A B : LB Y} {A' B' : LB Y'} (hA : A.IsLB) (hB : B.IsLB) (hA' : A'.IsLB) (hB' : B'.IsLB)
  (a : ChartPull A' A φ) (b : ChartPull B' B φ) (s : Fin D → L.Sec)
  (hS : Etale ((cutIdeal hL s).subschemeι ≫ p)) (e : (LB.div A (tw B L D)).Sec)
  (he : SuppIn (nonzeroLocus e) (cutIdeal hL s)) {O : Y.Opens} (hO : SuppIn O (cutIdeal hL s))

end Field

end GlobalTheory.Vanishing
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoefficientMapExtensionRationalValues
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoefficientMapExtensionRationalValues
noncomputable section

namespace GlobalTheory.Div.CoefExtension

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 1600000 in
theorem exists_ext_placeEx : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.grp_chiW → R.IsFam → R.IsModels → ∀ (gramR : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E) (c0R : VV D.what₂.LL (fun τ => Bridge.lamRdef (Ptw D) τ) →ₛₗ[D.what₂.embLL] R.cX.coef.W) (c0L : ∀ i : Fin D.R.m, VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).coef.W), Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L → ∀ (i : Fin D.R.m) (K' : Type) [Field K'] (jL : D.what₂.LL →+* K') (σ' : K' →+* ℂ), σ'.comp jL = D.what₂.embLL → ∃ c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W, CoefficientBaseChange R i jL σ' (c0L i) c0' ∧ ∀ t (Cl : Type) [Fintype Cl] (h : Cl → GA D (Vc D i)), PlaceEx R i t h c0' := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hL hW hF hM gramR c0R c0L hT i K' _ jL σ' hσ
  obtain ⟨c0', hc⟩ := GlobalTheory.Mem.PlaceVal.exists_ext_VV (W := (R.cV i).W) jL σ' hσ (lamV D i) (c0L i)
  exact ⟨c0', hc, fun t Cl _ h =>
    GlobalTheory.RationalValues.placeEx R i jL σ' t h c0' hM.jV hT hc hL hW hF.pl_onto hF.muVal⟩

end GlobalTheory.Div.CoefExtension
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoefficientMapExtensionRationalValuesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coefficientMap_extension_rational_values : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.grp_chiW → R.IsFam → R.IsModels → ∀ (gramR : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E) (c0R : VV D.what₂.LL (fun τ => Bridge.lamRdef (Ptw D) τ) →ₛₗ[D.what₂.embLL] R.cX.coef.W) (c0L : ∀ i : Fin D.R.m, VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).coef.W), Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L → ∀ (i : Fin D.R.m) (K' : Type) [Field K'] (jL : D.what₂.LL →+* K') (σ' : K' →+* ℂ), σ'.comp jL = D.what₂.embLL → ∃ c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W, CoefficientBaseChange R i jL σ' (c0L i) c0' ∧ ∀ t (Cl : Type) [Fintype Cl] (h : Cl → GA D (Vc D i)), PlaceEx R i t h c0' := by
  first | exact @GlobalTheory.Div.CoefExtension.exists_ext_placeEx | exact GlobalTheory.Div.CoefExtension.exists_ext_placeEx | (intros; apply GlobalTheory.Div.CoefExtension.exists_ext_placeEx <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemTensSpan
noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.RealLift

namespace GlobalTheory.KFixIrr

def chiOne (P Q R S : ℕ) (x : ℚ) : Submodule ℂ (Formalism.BasicNotions.TH.Pol P Q R S) :=
  ⨅ X : {X : Mat P Q // IsKC X}, LinearMap.ker (fockAct1 P Q R S X.1 - ((x : ℂ) * X.1.trace) • 1)

theorem mem_chiOne {P Q R S : ℕ} (x : ℚ) (f : Formalism.BasicNotions.TH.Pol P Q R S) :
    f ∈ chiOne P Q R S x ↔ ∀ X : Mat P Q, IsKC X → fockAct1 P Q R S X f = ((x : ℂ) * X.trace) • f := by
  simp only [chiOne, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, sub_eq_zero, Subtype.forall]

def lowOne (P Q R S : ℕ) (x : ℚ) (d : ℕ) : Submodule ℂ (Formalism.BasicNotions.TH.Pol P Q R S) :=
  chiOne P Q R S x ⊓ MvPolynomial.restrictTotalDegree (Ln P Q R S) ℂ d

theorem mem_lowOne {P Q R S : ℕ} (x : ℚ) (d : ℕ) (f : Formalism.BasicNotions.TH.Pol P Q R S) :
    f ∈ lowOne P Q R S x d ↔ f ∈ chiOne P Q R S x ∧ f.totalDegree ≤ d := by
  rw [lowOne, Submodule.mem_inf, MvPolynomial.mem_restrictTotalDegree]

def tensSpan {ι V : Type} [Fintype ι] [AddCommGroup V] [Module ℂ V] (H : ι → Submodule ℂ V) :
    Submodule ℂ (⨂[ℂ] _ : ι, V) :=
  Submodule.span ℂ {T | ∃ f : ι → V, (∀ w, f w ∈ H w) ∧ T = PiTensorProduct.tprod ℂ f}

theorem tprod_mem_tensSpan {ι V : Type} [Fintype ι] [AddCommGroup V] [Module ℂ V] (H : ι → Submodule ℂ V)
    (f : ι → V) (hf : ∀ w, f w ∈ H w) : PiTensorProduct.tprod ℂ f ∈ tensSpan H :=
  Submodule.subset_span ⟨f, hf, rfl⟩

end GlobalTheory.KFixIrr

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelGroupLiftExists
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts GlobalTheory.GeoLevel
open GlobalTheory.Member (FinCong IotaOK)
open GlobalTheory.LevelCusp (IsMatch)
open GlobalTheory.Dict (castFr)
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GeoLevel

theorem isBaseFrame_of_isLatBasis {D : D7} (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (h : IsLatBasis V rfl β) :
    IsBaseFrame V β (GlobalTheory.Member.latC V) 1 := by
  refine ⟨fun x => ?_, Formalism.L2.Herm.coordinate_lattice_self_dual D.sp.cm V, Nat.one_pos, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨z, rfl⟩ := GlobalTheory.LiftLevel.swap_surj x
    refine Iff.trans ?_ (h z)
    rw [(GlobalTheory.Member.latHat_eq_hat_and_gram D V).1]
    exact (GlobalTheory.LevSplit.latHat_iff _ z).symm
  · rw [← GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq] at hx
    simpa using hx
  · rw [← GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq]
    simpa using hx

theorem not_isConjPl_of_le {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (l : Level H)
    {w w' : Formalism.L2.DIV.Pl D.host.E} (hw : l.Mb ≤ w.asIdeal) (hw' : l.Mb ≤ w'.asIdeal) : ¬ IsConjPl w w' := by
  intro h
  apply w'.isPrime.ne_top
  rw [eq_top_iff, ← l.coprime]
  refine sup_le hw' (Ideal.map_le_iff_le_comap.2 fun a ha => ?_)
  obtain ⟨c', hc', e⟩ := h a (hw ha)
  have : H.bar a = c' := by
    apply RingOfIntegers.coe_injective
    exact (H.bar_eq a).trans e.symm
  show H.bar a ∈ w'.asIdeal
  rw [this]; exact hc'

theorem finR_rfl {D : D7} (V : HSp D) (κ : GA D V) : finR V rfl κ = finE V κ := by
  apply Units.ext
  ext i j
  rfl

end GlobalTheory.GeoLevel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroConjNegOfCmExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroConjNegOfCmExtension
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.CMTraceZero

theorem exists_ne_zero_conj_neg : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∃ ξ₀ : E, ξ₀ ≠ 0 ∧ σ ξ₀ = -ξ₀ := by
  intro F E _ _ _ _ _ σ B hB
  obtain ⟨_, hc, _, hτ⟩ := hB.cm
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hinv : ∀ x, σ (σ x) = x := fun x => τ.injective (by rw [hτ, hτ, star_star])
  have hne : ∃ x, σ x ≠ x := by
    by_contra hall
    push_neg at hall
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    have hw := hc.isComplex w
    rw [InfinitePlace.isComplex_iff] at hw
    apply hw
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have := hτ w.embedding x
    rw [hall x] at this
    simpa using this.symm
  obtain ⟨x, hx⟩ := hne
  refine ⟨x - σ x, sub_ne_zero.mpr (Ne.symm hx), ?_⟩
  rw [map_sub, hinv, neg_sub]

end GlobalTheory.CMTraceZero
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroConjNegOfCmExtensionStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_conj_neg_of_cmExtension : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∃ ξ₀ : E, ξ₀ ≠ 0 ∧ σ ξ₀ = -ξ₀ := by
  first | exact @GlobalTheory.CMTraceZero.exists_ne_zero_conj_neg | exact GlobalTheory.CMTraceZero.exists_ne_zero_conj_neg | (intros; apply GlobalTheory.CMTraceZero.exists_ne_zero_conj_neg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurComponentsSpan
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
open GlobalTheory.LiftLower
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PrincipalDecomp

open GlobalTheory.SphericalOps GlobalTheory.HeckeAdjoint GlobalTheory.HeckeOrthSum

theorem mult_le_of_parts {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}
    {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {M : DSModel V S} {J : Subgroup (GA D V)}
    {χ : GA D V → ℂ} {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))} {μ : Measure (GA D V)} {𝓕 : Set (GA D V)}
    (hθ : IsInfFam θ) (hμ : μ.IsHaarMeasure) (hF : IsFundamentalDomain (GQ V) 𝓕 μ)
    (hS : SchurMult θ M (J : Set (GA D V)) χ μ 𝓕) [FiniteDimensional ℂ (Mult θ M (J : Set (GA D V)) χ)]
    (hK : ∀ P d R, Hecke₂ V (J : Set (GA D V)) χ Sb P d R →
      ∀ T ∈ Mult θ M (J : Set (GA D V)) χ, heckeOn M R T ∈ Mult θ M (J : Set (GA D V)) χ)
    (Z : Submodule ℂ (MMap M))
    (hZ : ∀ c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ,
      (∀ P d, (¬ ∃ R, Hecke₂ V (J : Set (GA D V)) χ Sb P d R) → c P d = 0) →
        partFull θ M (J : Set (GA D V)) χ Sb c ≤ Z) :
    Mult θ M (J : Set (GA D V)) χ ≤ Z := by
  classical
  obtain ⟨h1, h2⟩ := GlobalTheory.SchurConst.ipM_posDef D θ V S M _ χ μ 𝓕 hθ hμ hF hS (GlobalTheory.GardingVec.sm_ne_bot D V S M)
  have hpos : IsPosOn (Mult θ M (J : Set (GA D V)) χ) (ipM M μ 𝓕) :=
    ⟨fun x hx y hy z hz c => (h1 x hx y hy z hz c).1, fun x hx y hy => (h1 x hx y hy y hy 0).2, fun x hx => h2 x hx⟩
  refine hpos.le_iSup_eigen
    (I := {x : HeightOneSpectrum (𝓞 D.host.E) × List ℤ × Finset (GA D V) //
      Hecke₂ V (J : Set (GA D V)) χ Sb x.1 x.2.1 x.2.2})
    (fun i => heckeOn M i.1.2.2) (fun i => hK _ _ _ i.2) (fun i k T hT => ?_) ?_ Z ?_
  · rw [GlobalTheory.MultMem.mem_mult_iff] at hT
    exact MultilinearMap.ext fun v => comm_heckeLin (realUnif D _) i.2 k.2 (hT.lev v)
  · rintro ⟨⟨P, d, R⟩, hR⟩
    obtain ⟨R', hR', -⟩ := exists_dual (realUnif D P) hR
    exact ⟨⟨(P, dualLab d, R'), hR'⟩, fun T hT T' hT' =>
      ipM_heckeOn_dualLab D V S θ M J χ Sb μ 𝓕 hθ hμ hF hS P d R R' hR hR' T hT T' hT' (hK _ _ _ hR T hT)
        (hK _ _ _ hR' T' hT')⟩
  · intro x T hT hx
    let c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ := fun P d =>
      if h : ∃ R, Hecke₂ V (J : Set (GA D V)) χ Sb P d R then x ⟨(P, d, h.choose), h.choose_spec⟩ else 0
    refine hZ c (fun P d h => dif_neg h) ((mem_partFull ..).2 ⟨hT, fun P d R hR v => ?_⟩)
    have h : ∃ R, Hecke₂ V (J : Set (GA D V)) χ Sb P d R := ⟨R, hR⟩
    rw [labelUnique (realUnif D) P d R h.choose hR h.choose_spec (T v) (((GlobalTheory.MultMem.mem_mult_iff ..).1 hT).lev v)]
    simp only [c, dif_pos h]
    exact congrArg (fun U : MMap M => U v) (hx ⟨(P, d, h.choose), h.choose_spec⟩)

end GlobalTheory.PrincipalDecomp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchingDeterminantRootOfUnity
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts GlobalTheory.GeoLevel
open GlobalTheory.Member (FinCong IotaOK)
open GlobalTheory.LevelCusp (IsMatch)
open GlobalTheory.Dict (castFr)
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

namespace GlobalTheory.GeoLevel

theorem det_mul_cc_det_of_isMatch {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (δ : GL (Fin r) E) (h : IsMatch X X δ) :
    (δ : Matrix (Fin r) (Fin r) E).det * IsCMField.complexConj E (δ : Matrix (Fin r) (Fin r) E).det = 1 := by
  have hm : (δ : Matrix (Fin r) (Fin r) E)ᵀ * X.Gm *
      ((IsCMField.complexConj E : E →+* E).mapMatrix (δ : Matrix (Fin r) (Fin r) E)) = X.Gm := by
    ext i j
    have := h.iso (Pi.single i 1) (Pi.single j 1)
    simp only [herm, cc, Matrix.mulVec_single_one, Matrix.col_apply] at this
    simp only [Pi.single_apply, apply_ite, map_one, map_zero, mul_ite, ite_mul, mul_one, one_mul, mul_zero,
      zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    rw [← this]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    rfl
  have hd := congrArg Matrix.det hm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.map_det] at hd
  apply mul_left_cancel₀ X.Gm_det
  rw [mul_one]
  refine Eq.trans ?_ hd
  rw [← mul_assoc, mul_comm X.Gm.det]
  rfl

theorem four_dvd_finrank_and_det_eq_pm_one : ∀ (D : D7), 4 ∣ Module.finrank ℚ D.host.E ∧ ∀ (r : ℕ) (X : Data D.host.E r) (δ : GL (Fin r) D.host.E), IsMatch X X δ → (δ : Matrix (Fin r) (Fin r) D.host.E).det = 1 ∨ ∃ m : ℕ, 0 < m ∧ (δ : Matrix (Fin r) (Fin r) D.host.E).det ^ m = 1 := by
  intro D
  refine ⟨?_, fun r X δ h => ?_⟩
  · have hE : Module.finrank ℚ D.host.E = 4 * D.R.n := by
      have h : (Module.finrank ℚ D.host.E : ℝ) = 4 * (D.R.n : ℝ) := by
        rw [D.host.finrank_cmField]
        unfold Ranks.n
        push_cast
        ring
      exact_mod_cast h
    exact ⟨_, hE⟩
  · have h1 := det_mul_cc_det_of_isMatch X δ h
    refine Or.inr (GlobalTheory.Mem.StabDet.eq_pm_one_of_unitary D.host _ ⟨?_, h1⟩
      (GlobalTheory.Mem.StabDet.isIntegral_det X.Λ X.Λ_fg X.Λ_span _ fun v hv => (h.lat v).1 hv))
    rw [mul_comm]
    exact h1

end GlobalTheory.GeoLevel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingActExtendsSemiAbelianDvr
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingActExtendsSemiAbelianDvr
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory

open GlobalTheory.ExtUnique

theorem ringAct_extends_semiAbelian_dvr : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G] (A : Over (Sp L)) [GrpObj A] (φ : A.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback A G (spMap (algebraMap W L)) φ → ∀ (O : Type) [Ring O] (act : O → (A ⟶ A)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 A → (∀ a b, act (a * b) = act a ≫ act b) → (∀ a b, act (a + b) = act a * act b) → ∃ act' : O → (G ⟶ G), ((∀ a, IsMonHom (act' a)) ∧ act' 1 = 𝟙 G ∧ (∀ a b, act' (a * b) = act' a ≫ act' b) ∧ (∀ a b, act' (a + b) = act' a * act' b)) ∧ ∀ a, (act a).left ≫ φ = φ ≫ (act' a).left := by
  intro W L _ _ _ _ _ _ G _ A _ φ hG hφ O _ act hh h1 hmul hadd
  obtain ⟨_, _⟩ := ExtUnique.flat_and_isSeparated_of_isSemiAbelian G hG
  obtain ⟨_, _⟩ := ExtUnique.spec_fractionRing W L
  have hq : QuasiCompact (spMap (algebraMap W L)) := ‹_›
  have hd : IsSchemeTheoreticallyDominant (spMap (algebraMap W L)) := ‹_›
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso (isGrpPullback_pullback G (spMap (algebraMap W L))) hφ
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso hφ (isGrpPullback_pullback G (spMap (algebraMap W L)))
  have ext : ∀ x : O, ∃ F : G ⟶ G, (act x).left ≫ φ = φ ≫ F.left := by
    intro x
    have := hh x
    obtain ⟨F, ⟨-, hF⟩, -⟩ := GlobalTheory.semiAbelian_hom_extends_uniquely_dvr W L G G hG hG
      (a.hom ≫ act x ≫ b.hom) inferInstance
    refine ⟨F, ?_⟩
    have h₁ := pullback_map_left_fst (spMap (algebraMap W L)) F
    rw [hF, Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hb', ← ha', Category.assoc] at h₁
    have : IsIso a.hom.left := inferInstanceAs (IsIso ((Over.forget _).map a.hom))
    exact (cancel_epi a.hom.left).1 h₁
  choose f hf using ext
  refine ⟨f, ⟨fun x => ?_, ?_, fun x y => ?_, fun x y => ?_⟩, hf⟩
  · have := hh x
    exact isMonHom_of_isGrpPullback hφ hφ (act x) (f x) (hf x)
  · refine GlobalTheory.ExtUnique.over_hom_ext_of_isPullback hφ.1 ?_
    rw [← hf, h1, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]
  · refine GlobalTheory.ExtUnique.over_hom_ext_of_isPullback hφ.1 ?_
    rw [← hf, hmul, Over.comp_left, Over.comp_left, Category.assoc, hf, ← Category.assoc, hf, Category.assoc]
  · refine GlobalTheory.ExtUnique.over_hom_ext_of_isPullback hφ.1 ?_
    let φ₀ : Over.mk (A.hom ≫ spMap (algebraMap W L)) ⟶ G := Over.homMk φ hφ.1.w
    have h := hφ.2 A (act x) (act y) (φ₀ ≫ f x) (φ₀ ≫ f y) (hf x).symm (hf y).symm
    rw [← MonObj.comp_mul] at h
    rw [← hf, hadd, ← h]
    rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingActExtendsSemiAbelianDvrStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ring_action_extension_compatible : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G] (A : Over (Sp L)) [GrpObj A] (φ : A.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback A G (spMap (algebraMap W L)) φ → ∀ (O : Type) [Ring O] (act : O → (A ⟶ A)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 A → (∀ a b, act (a * b) = act a ≫ act b) → (∀ a b, act (a + b) = act a * act b) → ∃ act' : O → (G ⟶ G), ((∀ a, IsMonHom (act' a)) ∧ act' 1 = 𝟙 G ∧ (∀ a b, act' (a * b) = act' a ≫ act' b) ∧ (∀ a b, act' (a + b) = act' a * act' b)) ∧ ∀ a, (act a).left ≫ φ = φ ≫ (act' a).left := by
  first | exact @GlobalTheory.ringAct_extends_semiAbelian_dvr | exact GlobalTheory.ringAct_extends_semiAbelian_dvr | (intros; apply GlobalTheory.ringAct_extends_semiAbelian_dvr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionsLieRationalWeightsCommute
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionsLieRationalWeightsCommute
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem fock_lie_wts_comm : ∀ P Q R S : ℕ, IsLieAct (fockAct1 P Q R S) ∧ IsLieAct (fockAct2 P Q R S) ∧
    (∀ v, v ∈ ⨆ μ : Ix P Q → ℚ, wtSub (fockAct1 P Q R S) μ) ∧ (∀ v, v ∈ ⨆ μ : Ix R S → ℚ, wtSub (fockAct2 P Q R S) μ) ∧
    ∀ X Y f, fockAct1 P Q R S X (fockAct2 P Q R S Y f) = fockAct2 P Q R S Y (fockAct1 P Q R S X f) := by
  intro P Q R S
  obtain ⟨h1, h2, hc⟩ := GlobalTheory.FockPair.pair_lie_commute P Q R S
  obtain ⟨w1, w2⟩ := GlobalTheory.FockPolGK.pol_locFin_weights P Q R S
  refine ⟨h1, h2, fun v => (w1 v).2, fun v => (w2 v).2, fun X Y f => ?_⟩
  have := LinearMap.congr_fun (hc X Y) f
  simpa only [Module.End.mul_apply] using this

end GlobalTheory.HoweR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionsLieRationalWeightsCommuteStatement
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockActions_lie_rationalWeights_commute : ∀ P Q R S : ℕ, IsLieAct (fockAct1 P Q R S) ∧ IsLieAct (fockAct2 P Q R S) ∧ (∀ v, v ∈ ⨆ μ : Ix P Q → ℚ, wtSub (fockAct1 P Q R S) μ) ∧ (∀ v, v ∈ ⨆ μ : Ix R S → ℚ, wtSub (fockAct2 P Q R S) μ) ∧ ∀ X Y f, fockAct1 P Q R S X (fockAct2 P Q R S Y f) = fockAct2 P Q R S Y (fockAct1 P Q R S X f) := by
  first | exact @GlobalTheory.HoweR.fock_lie_wts_comm | exact GlobalTheory.HoweR.fock_lie_wts_comm | (intros; apply GlobalTheory.HoweR.fock_lie_wts_comm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorDerivativeIsDifferential
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.LogDR.isExtD_extD : ∀ (K : Type) [Field K], IsExtD ℤ K (extD K) := by
  intro K _
  refine { mul := ?_, sq := ?_, alg := ?_ }
  ·
    intro x y
    rw [extD_apply, extD_apply, extD_apply, CechDR.dDR_mul, add_comm]
    rfl
  · intro x
    rw [extD_apply, extD_apply, CechDR.dDR_dDR]
  · intro a
    rw [extD_apply, CechDR.dDR_algebraMap]
end
