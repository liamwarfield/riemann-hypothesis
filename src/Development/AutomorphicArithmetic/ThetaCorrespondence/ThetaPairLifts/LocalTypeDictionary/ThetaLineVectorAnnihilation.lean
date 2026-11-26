module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaSumDifferentiableAlongLine

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LineDerivativeSplitEqSum
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LineDerivativeAdditiveInLines
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.JointlyContinuousArchimedeanWeilAction
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM Filter Topology
open scoped SchwartzMap GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
noncomputable section
namespace GlobalTheory.ArchJointCont
theorem tendsto_schrodinger_action_along_line : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Y, ∀ (r : (Fin n × Fin d → AF F) → ℂ), r 0 ≠ 0 →
    (∀ f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r) →
    ∀ (h k : ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (h₀ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
    (∀ t : ℝ, om (γ (Multiplicative.ofAdd t), 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (h t) r) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (k t) r) →
    Filter.Tendsto h (nhds 0) (nhds h₀) → Filter.Tendsto k (nhds 0) (nhds h₀) := by
  intro hP F E _ _ _ _ _ σ n d Y Wd M ψ χX χW om hψ _hM hW γ hγ r hr0 hR h k h₀ hk hh
  have hs := IsUWeilPair.isUSplitting hW
  let δ : ℝ → UA σ Y.J × UA σ Wd.J := fun t => (γ (Multiplicative.ofAdd t), 1)
  have hδc : Continuous δ := (hγ.1.comp continuous_ofAdd).prodMk continuous_const
  have hδ0 : δ 0 = 1 := by
    show (γ (Multiplicative.ofAdd 0), 1) = 1
    rw [ofAdd_zero, map_one]; rfl
  have hδm : ∀ s t, δ (s + t) = δ s * δ t := fun s t => by
    show (γ (Multiplicative.ofAdd (s + t)), 1) = (γ (Multiplicative.ofAdd s), 1) * (γ (Multiplicative.ofAdd t), 1)
    rw [ofAdd_add, map_mul, Prod.mk_mul_mk, one_mul]
  have ex := fun f => _root_.GlobalTheory.ArchLinePair.exists_orbit_pair_archimedean_line hP M ψ χX χW om hψ hW δ hδc hδ0 hδm (fun t => hγ.2 _)
    (fun t u _ => by simp [δ, mat]) f
  choose c g hc0 hslope hact using ex
  have hrr : ∀ x z, At (evI F) z → r (x + z) = r x := (hR 0).1
  have hinj := GlobalTheory.ArchCancel.eq_of_tens_eq F r hrr ⟨0, hr0⟩
  have hA : ∀ t (f : SInf F (Fin n × Fin d)), om (δ t) (tens (evI F) ⇑f r) = tens (evI F) ⇑(c f t) r :=
    fun t f => hact f t r (hR f)
  have tadd : ∀ f g : SInf F (Fin n × Fin d),
      tens (evI F) ⇑(f + g) r = tens (evI F) ⇑f r + tens (evI F) ⇑g r := by
    intro f g; funext x; simp [tens, add_mul]
  have tsmul : ∀ (a : ℂ) (f : SInf F (Fin n × Fin d)), tens (evI F) ⇑(a • f) r = a • tens (evI F) ⇑f r := by
    intro a f; funext x; simp [tens, mul_assoc]
  let A : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d) := fun t =>
    { toFun := fun f => c f t
      map_add' := fun f g => hinj _ _ (by rw [← hA, tadd, map_add (f := _), hA, hA, tadd])
      map_smul' := fun a f => hinj _ _ (by rw [← hA, tsmul, map_smul, hA, RingHom.id_apply, tsmul]) }
  have hAf : ∀ t f, A t f = c f t := fun _ _ => rfl
  have hmul : ∀ s t f, c f (s + t) = c (c f t) s := fun s t f => hinj _ _ (by
    rw [← hA (s + t) f, ← hA s (c f t), ← hA t f, hδm, map_mul, Module.End.mul_apply])
  have hcont0 : ∀ f, Tendsto (fun s => c f s) (𝓝 0) (𝓝 f) := by
    intro f
    have h1 : Tendsto (fun s : ℝ => s • (s⁻¹ • (c f s - f))) (𝓝[≠] 0) (𝓝 ((0 : ℝ) • g f)) :=
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).smul (hslope f)
    rw [zero_smul] at h1
    have h2 : Tendsto (fun s => c f s) (𝓝[≠] 0) (𝓝 f) := by
      have h1' := h1.add_const f
      rw [zero_add] at h1'
      refine h1'.congr' (eventually_nhdsWithin_of_forall fun s hs => ?_)
      rw [smul_smul, mul_inv_cancel₀ hs, one_smul, sub_add_cancel]
    have h3 : ContinuousAt (fun s => c f s) 0 := by
      rw [← continuousWithinAt_compl_self, ContinuousWithinAt, hc0]; exact h2
    have h4 := h3.tendsto
    rwa [hc0] at h4
  have hcont : ∀ f, Continuous fun s => c f s := by
    intro f
    refine continuous_iff_continuousAt.2 fun t₀ => ?_
    have ht : Tendsto (fun s : ℝ => s - t₀) (𝓝 t₀) (𝓝 0) := by
      have h5 := (continuous_sub_right t₀).tendsto t₀
      rwa [sub_self] at h5
    refine ((hcont0 (c f t₀)).comp ht).congr fun s => ?_
    show c (c f t₀) (s - t₀) = c f s
    rw [← hmul, sub_add_cancel]
  let g₀ := GlobalTheory.ArchLocality.intInd (F := F) (Fin n × Fin d)
  have hg₀ : g₀ ∈ SB _ := GlobalTheory.ArchLocality.intInd_mem _
  have hg₀0 : g₀ 0 = 1 := by
    simp only [g₀, GlobalTheory.ArchLocality.intInd]
    rw [Set.indicator_of_mem (show (0 : Fin n × Fin d → IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) ∈ Set.pi Set.univ
      fun _ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) from
        fun i _ => zero_mem (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F))]
    rfl
  let r₀ : (Fin n × Fin d → AF F) → ℂ := fun x => g₀ fun i => (x i).2
  have hrr₀ : ∀ x z, At (evI F) z → r₀ (x + z) = r₀ x := by
    intro x z hz
    refine congrArg g₀ (funext fun i => ?_)
    show (x i).2 + (z i).2 = (x i).2
    rw [GlobalTheory.ArchLocality.snd_eq_zero_of_at hz i, add_zero]
  have hR₀ : ∀ f : SInf F (Fin n × Fin d), Rest (evI F) ⇑f r₀ := fun f =>
    ⟨hrr₀, Submodule.subset_span ⟨f, g₀, hg₀, rfl⟩⟩
  have hAcont : ∀ t, Continuous (A t) := by
    intro t
    refine continuous_of_weak (A t) fun T => ?_
    obtain ⟨l, hl, hlf⟩ := exists_adm F T
    obtain ⟨T', hT'⟩ := hs.adm (δ t) l hl g₀ hg₀
    refine T'.continuous.congr fun f => ?_
    have e1 : om (δ t) (pureA F ⇑f g₀) = pureA F ⇑(c f t) g₀ := hact f t r₀ (hR₀ f)
    have e2 := hT' f
    rw [LinearMap.comp_apply, e1, hlf, hg₀0, one_mul] at e2
    exact e2.symm
  let 𝓕 : Set.Icc (-1 : ℝ) 1 → SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d) := fun i => ⟨A i, hAcont i⟩
  haveI : BarrelledSpace ℂ (SInf F (Fin n × Fin d)) := GlobalTheory.schwartzMap_barrelledSpace _
  have hq := schwartz_withSeminorms ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ
  have hUE : UniformEquicontinuous ((↑) ∘ 𝓕) := hq.banach_steinhaus fun q x => by
    have hc : Continuous fun t : ℝ => schwartzSeminormFamily ℂ _ ℂ q (c x t) :=
      (hq.continuous_seminorm q).comp (hcont x)
    have := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).bddAbove_image hc.continuousOn
    rw [Set.image_eq_range] at this
    exact this
  have hk' : ∀ t, k t = c (h t) t := fun t => hinj _ _ ((hk t).symm.trans (hA t (h t)))
  have h1 : Tendsto (fun t => A t (h t - h₀)) (𝓝 0) (𝓝 0) := by
    have hE := hUE.equicontinuous 0
    intro U hU
    have hU' : {p : SInf F (Fin n × Fin d) × SInf F (Fin n × Fin d) | p.2 - p.1 ∈ U} ∈
        uniformity (SInf F (Fin n × Fin d)) := by
      rw [uniformity_eq_comap_nhds_zero]; exact ⟨U, hU, fun p hp => hp⟩
    have ev := hE _ hU'
    have hz : Tendsto (fun t => h t - h₀) (𝓝 0) (𝓝 0) := by simpa using hh.sub_const h₀
    have ev3 : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ Set.Icc (-1 : ℝ) 1 := Icc_mem_nhds (by norm_num) (by norm_num)
    refine Filter.mem_map.2 ?_
    filter_upwards [hz.eventually ev, ev3] with t ht ht'
    have := ht ⟨t, ht'⟩
    simpa [𝓕] using this
  have h2 : Tendsto (fun t => A t (h t - h₀) + c h₀ t) (𝓝 0) (𝓝 (0 + h₀)) := h1.add (hcont0 h₀)
  rw [zero_add] at h2
  refine h2.congr fun t => ?_
  rw [hk' t, map_sub]
  show c (h t) t - c h₀ t + c h₀ t = c (h t) t
  exact sub_add_cancel _ _
end GlobalTheory.ArchJointCont
end
end

section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jointly_continuous_archimedean_weil_action : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Y, ∀ (r : (Fin n × Fin d → AF F) → ℂ), r 0 ≠ 0 →
    (∀ f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r) →
    ∀ (h k : ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (h₀ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
    (∀ t : ℝ, om (γ (Multiplicative.ofAdd t), 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (h t) r) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (k t) r) →
    Filter.Tendsto h (nhds 0) (nhds h₀) → Filter.Tendsto k (nhds 0) (nhds h₀) := by
  first | exact @_root_.GlobalTheory.ArchJointCont.tendsto_schrodinger_action_along_line | exact _root_.GlobalTheory.ArchJointCont.tendsto_schrodinger_action_along_line | (intros; apply _root_.GlobalTheory.ArchJointCont.tendsto_schrodinger_action_along_line <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open Filter Topology
noncomputable section
open scoped Classical
namespace GlobalTheory.LineAdd
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
section
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
end
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
theorem line_sum_curve_eq_prod (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd)
    (hψ : IsStd ψ) (hG : M.IsGood ψ) (hW : M.IsWeil ψ χX χW om)
    {ι : Type} (γs : ι → (Multiplicative ℝ →* UA σ Y.J)) (hγs : ∀ i, γs i ∈ Lines σ Y)
    (r : (Fin n × Fin d → AF F) → ℂ) (hr00 : r 0 ≠ 0) (hr : ∀ f : SInf F (Fin n × Fin d), Rest (evI F) f r)
    (f : SInf F (Fin n × Fin d)) (g : ι → SInf F (Fin n × Fin d))
    (hg : ∀ i, ∃ c : ℝ → SInf F (Fin n × Fin d),
      (∀ t, om (γs i (Multiplicative.ofAdd t), 1) (tens (evI F) ⇑f r) = tens (evI F) ⇑(c t) r) ∧ c 0 = f ∧
      Tendsto (fun t : ℝ => t⁻¹ • (c t - f)) (𝓝[≠] 0) (𝓝 (g i))) :
    ∀ l : List ι, ∃ c : ℝ → SInf F (Fin n × Fin d),
      (∀ t, om ((l.map fun i => γs i (Multiplicative.ofAdd t)).prod, 1) (tens (evI F) ⇑f r) = tens (evI F) ⇑(c t) r) ∧
      c 0 = f ∧ Tendsto (fun t : ℝ => t⁻¹ • (c t - f)) (𝓝[≠] 0) (𝓝 (l.map g).sum) := by
  have hr0 : ∃ x, r x ≠ 0 := ⟨0, hr00⟩
  have canc := GlobalTheory.ArchCancel.eq_of_tens_eq F r (hr f).1 hr0
  have img : ∀ i (h : SInf F (Fin n × Fin d)) (t : ℝ), ∃ k : SInf F (Fin n × Fin d),
      om (γs i (Multiplicative.ofAdd t), 1) (tens (evI F) ⇑h r) = tens (evI F) ⇑k r := by
    intro i h t
    obtain ⟨c, -, hc, -⟩ := _root_.GlobalTheory.T.archimedean_line_pairing_twist hP M ψ χX χW om hψ hG hW (γs i) (hγs i) h r (hr h)
    exact ⟨c t, hc t⟩
  intro l
  induction l with
  | nil =>
    refine ⟨fun _ => f, fun t => ?_, rfl, ?_⟩
    · simp only [List.map_nil, List.prod_nil]
      exact om_one_one om _
    · simp only [sub_self, smul_zero, List.map_nil, List.sum_nil]
      exact tendsto_const_nhds
  | cons i l' ih =>
    obtain ⟨c', hc', hc'0, hlim'⟩ := ih
    obtain ⟨ci, hci, hci0, hlimi⟩ := hg i
    set S' := (l'.map g).sum with hS'
    let s : ℝ → SInf F (Fin n × Fin d) := fun t => if t = 0 then S' else t⁻¹ • (c' t - f)
    choose k hk using fun t => img i (s t) t
    have hs : Tendsto s (𝓝 0) (𝓝 S') := by
      rw [← nhdsNE_sup_pure (0 : ℝ)]
      refine Tendsto.sup ?_ ?_
      · refine hlim'.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with t ht
        simp only [s, if_neg (show t ≠ 0 from ht)]
      · simp only [tendsto_pure_left, s, if_pos rfl]
        exact fun _ => mem_of_mem_nhds
    have hk' : Tendsto k (𝓝 0) (𝓝 S') :=
      _root_.GlobalTheory.T.jointly_continuous_archimedean_weil_action hP M ψ χX χW om hψ hG hW (γs i) (hγs i) r hr00 hr s k S' hk hs
    have hcs : ∀ t, c' t = f + t • s t := by
      intro t
      by_cases ht : t = 0
      · subst ht; simp [hc'0]
      · simp only [s, if_neg ht, smul_smul, mul_inv_cancel₀ ht, one_smul, add_sub_cancel]
    refine ⟨fun t => ci t + t • k t, fun t => ?_, ?_, ?_⟩
    · simp only [List.map_cons, List.prod_cons]
      rw [om_prod_one, hc' t, hcs t, tens_add_smul, map_add (f := _), map_smul, hci t, hk t, tens_add_smul]
    · simp [hci0]
    · simp only [List.map_cons, List.sum_cons]
      refine (hlimi.add (hk'.mono_left nhdsWithin_le_nhds)).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : t ≠ 0 := ht
      rw [add_sub_right_comm, smul_add, smul_smul, inv_mul_cancel₀ ht', one_smul]
end GlobalTheory.LineAdd
open GlobalTheory.LineAdd GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels in
theorem GlobalTheory.LineAdd.deriv_prod_lines_eq_sum : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ {ι : Type} (l : List ι) (γs : ι → (Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J)),
    (∀ i, γs i ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X) → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X, (∀ t, γ t = (l.map fun i => γs i t).prod) →
    ∀ f ∈ M.Pol B.ψ B.emb, ∀ (f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (fs : ι → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ →
    (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (γs i (Multiplicative.ofAdd t), 1)) f (fs i)) →
    f₁ = (l.map fs).sum := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om a b a' b' hpair ι l γs hγs γ _ hprod f _ f₁ fs hD hDs
  obtain ⟨r, hr00, hr⟩ := GlobalTheory.ThK.exists_rest_inf F (Fin n × Fin d)
  have hψ := hpair.base.std
  have hG := hpair.good
  have hW := hpair.weil
  have canc := GlobalTheory.ArchCancel.eq_of_tens_eq F r (hr f).1 ⟨0, hr00⟩
  choose cs gs hcs hlims using fun i => _root_.GlobalTheory.T.archimedean_line_pairing_twist hP M B.ψ χX χW om hψ hG hW (γs i) (hγs i) f r (hr f)
  have hcs0 : ∀ i, cs i 0 = f := by
    intro i
    refine canc _ _ ?_
    rw [← hcs i 0]
    simp only [ofAdd_zero, map_one]
    exact om_one_one om _
  have hlims' : ∀ i, Tendsto (fun t : ℝ => t⁻¹ • (cs i t - f)) (𝓝[≠] 0) (𝓝 (gs i)) := by
    intro i; simpa [hcs0 i] using hlims i
  have hfs : ∀ i, fs i = gs i := by
    intro i
    refine canc _ _ (funext fun x => ?_)
    exact (hDs i r (hr f) x).unique (hasDerivAt_of_curve (hcs i) (hcs0 i) (hlims' i) x)
  obtain ⟨c, hc, hc0, hlim⟩ := _root_.GlobalTheory.LineAdd.line_sum_curve_eq_prod hP M B.ψ χX χW om hψ hG hW γs hγs r hr00 hr f gs
    (fun i => ⟨cs i, hcs i, hcs0 i, hlims' i⟩) l
  have hc' : ∀ t, om (γ (Multiplicative.ofAdd t), 1) (tens (evI F) ⇑f r) = tens (evI F) ⇑(c t) r := by
    intro t; rw [hprod]; exact hc t
  have e1 : f₁ = (l.map gs).sum := by
    refine canc _ _ (funext fun x => ?_)
    exact (hD r (hr f) x).unique (hasDerivAt_of_curve hc' hc0 hlim x)
  rw [e1]
  congr 1
  exact List.map_congr_left fun i _ => (hfs i).symm
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_derivative_additive_in_lines : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ {ι : Type} (l : List ι) (γs : ι → (Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J)),
    (∀ i, γs i ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X) → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X, (∀ t, γ t = (l.map fun i => γs i t).prod) →
    ∀ f ∈ M.Pol B.ψ B.emb, ∀ (f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (fs : ι → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ →
    (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (γs i (Multiplicative.ofAdd t), 1)) f (fs i)) →
    f₁ = (l.map fs).sum := by
  first | exact @_root_.GlobalTheory.LineAdd.deriv_prod_lines_eq_sum | exact _root_.GlobalTheory.LineAdd.deriv_prod_lines_eq_sum | (intros; apply _root_.GlobalTheory.LineAdd.deriv_prod_lines_eq_sum <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.LineDerivSplit
theorem line_derivative_split_eq_sum : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ {ι : Type} (l : List ι) (γs : ι → (Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J)),
    (∀ i, γs i ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X) → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X, (∀ t, γ t = (l.map fun i => γs i t).prod) →
    ∀ ΦD ∈ GlobalTheory.SquareAgree.algD M B.ψ B.emb, ∀ Φ₁D : (Fin n × Fin d → AF F) → ℂ,
    (∀ x, HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) ΦD x) (Φ₁D x) 0) →
    ∃ Ψ : ι → ((Fin n × Fin d → AF F) → ℂ), (∀ i, Ψ i ∈ GlobalTheory.SquareAgree.algD M B.ψ B.emb) ∧
      (∀ i, ∀ u, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (M.co.rho B.ψ u (om (γs i (Multiplicative.ofAdd t), 1) ΦD)))
        (GlobalTheory.WeilM.thetaSum F (M.co.rho B.ψ u (Ψ i))) 0) ∧ Φ₁D = (l.map Ψ).sum := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP ι l γs hγs γ hγ hprod ΦD hΦD Φ₁D hΦ₁
  have hact := _root_.GlobalTheory.T.dualPair_preserves_polarization hPr F E σ B n d X W M χX χW om r s r' s' hP
  choose Ds hDsP hDs using fun i => hact.1 (γs i) (hγs i)
  obtain ⟨Dγ, -, hDγ⟩ := hact.1 γ hγ
  obtain ⟨m, c, g, hg⟩ := (Submodule.mem_span_set').1 hΦD
  choose f φ hf hSB hcof hgf using fun j => (g j).2
  have hstd : ∀ j, ∀ᶠ v in Filter.cofinite,
      φ j v = Set.indicator {x : Fin n × Fin d → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} 1 := by
    intro j
    filter_upwards [hcof j, hP.good.std] with v h1 h2
    rw [h1, h2]
  have hmem : ∀ j, c j • f j ∈ M.Pol B.ψ B.emb := fun j => Submodule.smul_mem _ _ (hf j)
  have hΦ : ΦD = ∑ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c j • f j) (φ j) := by
    rw [← hg]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hgf j, pure_smul₀]
  refine ⟨fun i => ∑ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Ds i (c j • f j)) (φ j), fun i => ?_, fun i u => ?_, ?_⟩
  · refine Submodule.sum_mem _ fun j _ => Submodule.subset_span ?_
    exact ⟨_, φ j, hDsP i _ (hmem j), hSB j, hcof j, rfl⟩
  · rw [hΦ]
    exact _root_.GlobalTheory.ThetaLineDerFirst.hasDerivAt_thetaSum_along_line hPr M B.ψ χX χW om hP.base.std hP.good hP.weil (γs i) (hγs i) m
      (fun j => c j • f j) (fun j => Ds i (c j • f j)) φ (fun j => ⟨hSB j, hcof j⟩)
      (fun j => (hDs i _ (hmem j) _).2 rfl) u
  · have hpt : ∀ x, Φ₁D x = ∑ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Dγ (c j • f j)) (φ j) x := by
      intro x
      have h2 : HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) ΦD x)
          (∑ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Dγ (c j • f j)) (φ j) x) 0 := by
        have e : (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) ΦD x) =
            fun t => ∑ j, om (γ (Multiplicative.ofAdd t), 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c j • f j) (φ j)) x := by
          funext t
          set_option synthInstance.maxHeartbeats 100000 in
            rw [hΦ, map_sum, Finset.sum_apply]
        rw [e]
        have hs := HasDerivAt.sum (u := Finset.univ) fun j _ => GlobalTheory.ThetaFacInf.Fib.hasDerivAt_pure (φ j) (hSB j) (hstd j)
          ((hDγ _ (hmem j) _).2 rfl) x
        simpa [Finset.sum_fn] using hs
      exact (hΦ₁ x).unique h2
    have hadd : ∀ j, Dγ (c j • f j) = (l.map fun i => Ds i (c j • f j)).sum := fun j =>
      _root_.GlobalTheory.T.line_derivative_additive_in_lines hPr F E σ B n d X W M χX χW om r s r' s' hP l γs hγs γ hγ hprod _ (hmem j) _ _
        ((hDγ _ (hmem j) _).2 rfl) (fun i => (hDs i _ (hmem j) _).2 rfl)
    calc Φ₁D = ∑ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Dγ (c j • f j)) (φ j) :=
          funext fun x => (hpt x).trans (Finset.sum_apply x _ _).symm
      _ = ∑ j, (l.map fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Ds i (c j • f j)) (φ j)).sum := by
          simp only [hadd, pure_listSum]
      _ = (l.map fun i => ∑ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Ds i (c j • f j)) (φ j)).sum :=
          sum_listSum l (fun j i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Ds i (c j • f j)) (φ j))
end GlobalTheory.LineDerivSplit
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_derivative_splits : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ {ι : Type} (l : List ι) (γs : ι → (Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J)),
    (∀ i, γs i ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X) → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X, (∀ t, γ t = (l.map fun i => γs i t).prod) →
    ∀ ΦD ∈ GlobalTheory.SquareAgree.algD M B.ψ B.emb, ∀ Φ₁D : (Fin n × Fin d → AF F) → ℂ,
    (∀ x, HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) ΦD x) (Φ₁D x) 0) →
    ∃ Ψ : ι → ((Fin n × Fin d → AF F) → ℂ), (∀ i, Ψ i ∈ GlobalTheory.SquareAgree.algD M B.ψ B.emb) ∧
      (∀ i, ∀ u, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (M.co.rho B.ψ u (om (γs i (Multiplicative.ofAdd t), 1) ΦD)))
        (GlobalTheory.WeilM.thetaSum F (M.co.rho B.ψ u (Ψ i))) 0) ∧ Φ₁D = (l.map Ψ).sum := by
  first | exact @_root_.GlobalTheory.LineDerivSplit.line_derivative_split_eq_sum | exact _root_.GlobalTheory.LineDerivSplit.line_derivative_split_eq_sum | (intros; apply _root_.GlobalTheory.LineDerivSplit.line_derivative_split_eq_sum <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.LineKillV
theorem line_vector_annihilated : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Γ.V, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, ∀ Φ₁D ∈ algD Γ.M Bs.ψ Bs.emb,
    (∀ x, HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) ΦD x) (Φ₁D x) 0) → ∀ Φ₁,
    IsDatum Γ.M ψ cA Φ₁D Φ₁ → p Φ₁ = 0 := by
  intro hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTr Pi rf rl p p' hm γ hγ ΦD hΦD
    Φ₁D hΦ₁D hder Φ₁ hΦ₁
  have hψ : Bs.ψ = ψ := hO.psi
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hψ ▸ hTr.base.std
  obtain ⟨Y, γs, hY, hγs, hγsY, hprod⟩ := GlobalTheory.T.unitaryArchimedeanOneParam_eq_prod_cmType_lines D θ hθ W Γ.V hO.JW γ hγ
  obtain ⟨Ψ, hΨ, hΨd, hsum⟩ := _root_.GlobalTheory.T.line_derivative_splits hP _ _ _ Bs _ _ _ _ Γ.M _ _ om _ _ _ _
    (GlobalTheory.ThK.RealUniq.isPair_V hTr) _ γs hγs γ hγ hprod ΦD hΦD Φ₁D hder
  obtain ⟨Φ, hΦalg, hΦ⟩ := hO.algA' ΦD hΦD
  choose Φ' hΦ'alg hΦ' using fun τ => hO.algA' (Ψ τ) (hΨ τ)
  have hder' : ∀ τ, IsDer θ W (fun g => ωA (g, 1)) τ (Y τ) Φ (Φ' τ) := by
    intro τ z
    obtain ⟨u, rfl⟩ := cA.surjective z
    have h1 := hΨd τ u
    have e1 : (fun t : ℝ => GlobalTheory.WeilM.thetaSum D.host.F (Γ.M.co.rho Bs.ψ u (om (γs τ (Multiplicative.ofAdd t), 1) ΦD))) =
        fun t : ℝ => ωA (oneP θ W τ (Y τ) t, 1) Φ (cA u) := by
      funext t
      have h2 := (hO.weilA ΦD Φ hΦ (oneP θ W τ (Y τ) t) 1).2 u
      rw [GlobalTheory.KapXLine.kapX_one, ← hγsY τ t] at h2
      rw [hψ]; exact h2
    have e2 : GlobalTheory.WeilM.thetaSum D.host.F (Γ.M.co.rho Bs.ψ u (Ψ τ)) = Φ' τ (cA u) := by
      rw [hψ]; exact (hΦ' τ).2 u
    rw [e1, e2] at h1
    exact h1
  have hp : ∀ τ, p (Φ' τ) = 0 := fun τ =>
    hm.mapA.invl τ (Y τ) (hY τ) Φ hΦalg (Φ' τ) (hΦ'alg τ) (hder' τ)
  have hsumD : IsDatum Γ.M ψ cA Φ₁D (((Finset.univ : Finset D.what₂.Tau).toList.map Φ').sum) := by
    rw [hsum]; exact isDatum_list_sum hstd _ Ψ Φ' hΦ'
  rw [IsDatum.fun_eq Γ.M ψ cA cA.surjective hΦ₁ hsumD, map_list_sum, List.map_map]
  exact List.sum_eq_zero fun x hx => by
    obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hx
    exact hp τ
end GlobalTheory.LineKillV
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_line_vector_annihilation : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Γ.V, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, ∀ Φ₁D ∈ algD Γ.M Bs.ψ Bs.emb,
    (∀ x, HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) ΦD x) (Φ₁D x) 0) → ∀ Φ₁,
    IsDatum Γ.M ψ cA Φ₁D Φ₁ → p Φ₁ = 0 := by
  first | exact @_root_.GlobalTheory.LineKillV.line_vector_annihilated | exact _root_.GlobalTheory.LineKillV.line_vector_annihilated | (intros; apply _root_.GlobalTheory.LineKillV.line_vector_annihilated <;> assumption)
end
