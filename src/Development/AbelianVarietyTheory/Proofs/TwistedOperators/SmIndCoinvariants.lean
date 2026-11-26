module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InductionContragredient
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenericLevelOfFrameBlockAndCharacter
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemFourierJacobiSubgroupIffParabolicMulColumn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdaptedExponentSchwartzBruhatLastColumn

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmIndCoinvariants
noncomputable section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.IndDual

namespace GlobalTheory.SmGL.IndCoinv

variable {G X U : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup X] [Module ℂ X]
  [AddCommGroup U] [Module ℂ U] {P : Subgroup G} {σ : Representation ℂ P X} {ρ : Representation ℂ P U}

theorem smIndMap_bump (β : σ.IntertwiningMap ρ) {J : Subgroup G} (hJ : IsOpen (J : Set G))
    (w : fixed σ (J.subgroupOf P)) (v : fixed ρ (J.subgroupOf P)) (hv : β w = v) :
    smIndMap β (bump σ hJ w) = bump ρ hJ v := by
  refine Subtype.ext (Subtype.ext (funext fun g => ?_))
  show β ((bump σ hJ w).1.1 g) = _
  rcases cell_cases (P := P) J g with h | ⟨p, j, hj, rfl⟩
  · rw [bump_zero _ _ _ h, bump_zero _ _ _ h, map_zero]
  · rw [bump_mul _ _ _ _ hj, bump_mul _ _ _ _ hj, β.isIntertwining, hv]

theorem mem_of_bump {K : Subgroup G} (hK : IsCompact (K : Set G))
    (hPK : ∀ g : G, ∃ p ∈ P, ∃ x ∈ K, g = p * x)
    (hb : ∀ U ∈ nhds (1 : G), ∃ J : Subgroup G, IsOpen (J : Set G) ∧ (J : Set G) ⊆ U ∧ J ≤ K ∧
      ∀ x ∈ K, ∀ j ∈ J, x * j * x⁻¹ ∈ J)
    (Z : Submodule ℂ (smoothPart (ind P σ))) (hZ : ∀ g, ∀ f ∈ Z, smInd P σ g f ∈ Z)
    (h : ∀ (J : Subgroup G) (hJ : IsOpen (J : Set G)), J ≤ K → ∀ w, bump σ hJ w ∈ Z)
    (f : smoothPart (ind P σ)) : f ∈ Z := by
  obtain ⟨J, hJ, hJU, hle, hn⟩ := hb _ (IsOpen.mem_nhds (isSmooth_smoothRep _ f) (by
    rw [Set.mem_ofPred_eq, map_one, Module.End.one_apply]))
  refine Submodule.span_le.2 ?_ (mem_span_bump σ hJ hK hle hn hPK f fun j hj => hJU hj)
  rintro _ ⟨z, -, w, rfl⟩
  exact hZ _ _ (h J hJ hle w)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem map_mem_fixed {σ : Representation ℂ G X} {ρ : Representation ℂ G U} (β : σ.IntertwiningMap ρ)
    {H : Subgroup G} {w : X} (hw : w ∈ fixed σ H) : β w ∈ fixed ρ H :=
  mem_fixed_iff.2 fun h hh => by rw [← β.isIntertwining, mem_fixed_iff.1 hw h hh]

theorem mem_of_fixed [T2Space G] {σ : Representation ℂ G X} (hσ : IsSmooth σ) {H : Subgroup G}
    (hH : IsCompact (H : Set G)) {Γ : Type} (T : Γ → σ.IntertwiningMap σ) (M : Submodule ℂ (fixed σ H))
    (hM : ∀ γ (z : fixed σ H), (⟨T γ z, map_mem_fixed (T γ) z.2⟩ : fixed σ H) - z ∈ M) (w : fixed σ H)
    (hw : w.1 ∈ Submodule.span ℂ {y : X | ∃ γ z, y = T γ z - z}) : w ∈ M := by
  by_contra hn
  obtain ⟨l, hl, hl0⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
  obtain ⟨l₀, hl₀⟩ := LinearMap.exists_extend l
  obtain ⟨l₁, h1, h2⟩ := GlobalTheory.SmGL.DualAverage.exists_invariant_form G X σ hσ _ hH l₀
  have h3 : ∀ v : fixed σ H, l₁ v = l v := fun v =>
    (h2 _ (mem_fixed_iff.1 v.2)).trans (LinearMap.congr_fun hl₀ v)
  have h4 : ∀ γ, l₁ ∘ₗ (T γ).toLinearMap = l₁ := fun γ =>
    dual_ext hσ hH (fun h hh v => by
      show l₁ (T γ _) = l₁ (T γ _)
      rw [(T γ).isIntertwining, h1 h hh]) h1 fun v hv => by
      have h5 : l (_ - _) ∈ M.map l := Submodule.mem_map_of_mem (hM γ ⟨v, hv⟩)
      rw [hl0, Submodule.mem_bot, map_sub, ← h3, ← h3, sub_eq_zero] at h5
      exact h5
  apply hl
  rw [← h3]
  refine (Submodule.span_le (p := LinearMap.ker l₁)).2 ?_ hw
  rintro _ ⟨γ, z, rfl⟩
  have h5 : l₁ (T γ z) = l₁ z := LinearMap.congr_fun (h4 γ) z
  simp [h5]

theorem smInd_coinvariants : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (P K : Subgroup G), IsClosed (P : Set G) → IsCompact (K : Set G) → (∀ g : G, ∃ p ∈ P, ∃ x ∈ K, g = p * x) → (∀ U ∈ nhds (1 : G), ∃ J : Subgroup G, IsOpen (J : Set G) ∧ (J : Set G) ⊆ U ∧ J ≤ K ∧ ∀ x ∈ K, ∀ j ∈ J, x * j * x⁻¹ ∈ J) → ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (U : Type) [AddCommGroup U] [Module ℂ U] (σ : Representation ℂ P X) (ρ : Representation ℂ P U), IsSmooth σ → ∀ (α : σ.IntertwiningMap ρ) (Γ : Type) (T : Γ → σ.IntertwiningMap σ), Function.Surjective α → (∀ x, α x = 0 → x ∈ Submodule.span ℂ {y : X | ∃ γ z, y = T γ z - z}) → Function.Surjective (smIndMap α) ∧ ∀ f, smIndMap α f = 0 → f ∈ Submodule.span ℂ {y : smoothPart (ind P σ) | ∃ γ z, y = smIndMap (T γ) z - z} := by
  intro G _ _ _ _ P K hP hK hPK hb X _ _ U _ _ σ ρ hσ α Γ T hα hker
  have hc : ∀ J : Subgroup G, IsOpen (J : Set G) → J ≤ K → IsCompact (J.subgroupOf P : Set P) :=
    fun J hJ hle => hP.isClosedEmbedding_subtypeVal.isCompact_preimage
      (hK.of_isClosed_subset (J.isClosed_of_isOpen hJ) hle)
  constructor
  · intro f
    refine mem_of_bump hK hPK hb (LinearMap.range (smIndMap α).toLinearMap) ?_ ?_ f
    · rintro g _ ⟨φ, rfl⟩
      exact ⟨smInd P σ g φ, rfl⟩
    · intro J hJ hle w
      obtain ⟨x, hx⟩ := hα w
      obtain ⟨v, hv, e⟩ := IwahoriOnto.exists_fixed_map_eq hσ (hc J hJ hle) α.toLinearMap x fun h hh => by
        show α _ = α _
        rw [α.isIntertwining, hx, mem_fixed_iff.1 w.2 h hh]
      exact ⟨bump σ hJ ⟨v, hv⟩, smIndMap_bump α hJ _ _ (e.trans hx)⟩
  · intro f hf
    set Z := Submodule.span ℂ {y : smoothPart (ind P σ) | ∃ γ z, y = smIndMap (T γ) z - z} with hZ
    let N : Submodule ℂ X := LinearMap.ker α.toLinearMap
    have hN : ∀ g, ∀ v ∈ N, σ g v ∈ N := fun g v hv => by
      have hv' : α v = 0 := hv
      show α _ = 0
      rw [α.isIntertwining, hv', map_zero]
    let τ := sub σ N hN
    let j : τ.IntertwiningMap σ := { toLinearMap := N.subtype, isIntertwining' := fun _ => rfl }
    let f' : smoothPart (ind P τ) :=
      ⟨⟨fun g => ⟨f.1.1 g, congrArg (fun φ : smoothPart (ind P ρ) => φ.1.1 g) hf⟩, fun h g => Subtype.ext (f.1.2 h g)⟩,
        mem_smoothPart_of_nhds (Filter.mem_of_superset (IsOpen.mem_nhds f.2 (by simp)) fun g hg => by
          have hg' : ind P σ g f.1 = f.1 := hg
          exact Subtype.ext (funext fun x => Subtype.ext (congrFun (congrArg Subtype.val hg') x)))⟩
    have hst : ∀ g, Z ≤ Z.comap (smInd P σ g) := fun g => Submodule.span_le.2 (by
      rintro _ ⟨γ, z, rfl⟩
      exact Submodule.subset_span ⟨γ, smInd P σ g z, rfl⟩)
    refine mem_of_bump hK hPK hb (Z.comap (smIndMap j).toLinearMap) (fun g φ hφ => hst g hφ) ?_ f'
    intro J hJ hle w
    have hw := map_mem_fixed j w.2
    show smIndMap j _ ∈ Z
    rw [smIndMap_bump j hJ w ⟨_, hw⟩ rfl]
    refine mem_of_fixed hσ (hc J hJ hle) T (Z.comap (bump σ hJ)) (fun γ z => ?_) _ (hker _ w.1.2)
    rw [Submodule.mem_comap, map_sub, ← smIndMap_bump (T γ) hJ z _ rfl]
    exact Submodule.subset_span ⟨γ, _, rfl⟩

end GlobalTheory.SmGL.IndCoinv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOfFlagOfHermFormPreserving
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOfFlagOfHermFormPreserving
namespace GlobalTheory.FlagEq
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem eq_of_flag_of_hermForm : ∀ {α : Type} {m : α → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : α, Fin (m τ)) (Hm : Matrix (Fin g) (Fin g) ℂ), (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re) → ∀ (h h' : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (∀ x y, ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h x) (h y) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h' x) (h' y)) → ∀ (bv : ∀ τ, Fin (m τ) → (Fin g → ℂ)) (s : ℂ), s ≠ 0 → (∀ τ i, h (Pi.single (e.symm ⟨τ, i⟩) 1) - s • bv τ i ∈ Submodule.span ℂ (bv τ '' {j | j < i})) → (∀ τ i, h' (Pi.single (e.symm ⟨τ, i⟩) 1) - s • bv τ i ∈ Submodule.span ℂ (bv τ '' {j | j < i})) → h = h' := by
  intro α m g e Hm hpos h h' hH bv s hs hh hh'
  have key : ∀ τ, ∀ i : Fin (m τ), h (Pi.single (e.symm ⟨τ, i⟩) 1) = h' (Pi.single (e.symm ⟨τ, i⟩) 1) := by
    intro τ
    let ev : Fin (m τ) → (Fin g → ℂ) := fun j => Pi.single (e.symm ⟨τ, j⟩) 1
    let E : Fin (m τ) → Submodule ℂ (Fin g → ℂ) := fun i => Submodule.span ℂ (ev '' {j | j < i})
    have ha : ∀ i, Submodule.span ℂ (bv τ '' {j | j < i}) ≤ (E i).map h'.toLinearMap := by
      intro i
      induction i using WellFoundedLT.induction with
      | _ i ih =>
        rw [Submodule.span_le]
        rintro _ ⟨j, hj, rfl⟩
        have hj : j < i := hj
        have h1 : h' (ev j) ∈ (E i).map h'.toLinearMap :=
          Submodule.mem_map_of_mem (Submodule.subset_span ⟨j, hj, rfl⟩)
        have h2 : h' (ev j) - s • bv τ j ∈ (E i).map h'.toLinearMap := by
          have := ih j hj (hh' τ j)
          have hsub : {k : Fin (m τ) | k < j} ⊆ {k | k < i} := by
            intro k hk
            exact lt_trans hk hj
          exact Submodule.map_mono (Submodule.span_mono (Set.image_mono hsub)) this
        have h3 : s • bv τ j ∈ (E i).map h'.toLinearMap := by
          have := Submodule.sub_mem _ h1 h2
          simpa using this
        have := Submodule.smul_mem _ s⁻¹ h3
        rw [smul_smul, inv_mul_cancel₀ hs, one_smul] at this
        exact this
    intro i
    induction i using WellFoundedLT.induction with
    | _ i ih =>
      have hon : Set.EqOn h.toLinearMap h'.toLinearMap (E i) := by
        apply LinearMap.eqOn_span'
        rintro _ ⟨j, hj, rfl⟩
        exact ih j hj
      set u := h (ev i) - h' (ev i) with hu
      have hu' : u = (h (ev i) - s • bv τ i) - (h' (ev i) - s • bv τ i) := by
        rw [hu]; abel
      have huB : u ∈ Submodule.span ℂ (bv τ '' {j | j < i}) := by
        rw [hu']; exact Submodule.sub_mem _ (hh τ i) (hh' τ i)
      obtain ⟨v, hvE, hv⟩ := ha i huB
      have hv' : h' v = u := hv
      have hhv : h v = u := by
        rw [← hv']; exact hon hvE
      have hx : h (ev i) = h' (ev i) + u := by rw [hu]; abel
      have hE := hH (ev i) v
      rw [hhv, hv', hx] at hE
      have h0 : hermForm Hm u u = 0 := by
        unfold hermForm at hE ⊢
        rw [add_dotProduct] at hE
        simpa using hE
      by_contra hne
      have hne' : u ≠ 0 := by
        intro h0'; apply hne; rw [hu] at h0'; exact sub_eq_zero.mp h0'
      have := hpos u hne'
      rw [h0] at this
      simp at this
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun ℂ (Fin g)).ext
  intro n
  rw [Pi.basisFun_apply]
  have := key (e n).1 (e n).2
  simpa using this

end GlobalTheory.FlagEq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOfFlagOfHermFormPreservingStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_flag_of_hermForm_preserving : ∀ {α : Type} {m : α → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : α, Fin (m τ)) (Hm : Matrix (Fin g) (Fin g) ℂ), (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re) → ∀ (h h' : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (∀ x y, ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h x) (h y) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h' x) (h' y)) → ∀ (bv : ∀ τ, Fin (m τ) → (Fin g → ℂ)) (s : ℂ), s ≠ 0 → (∀ τ i, h (Pi.single (e.symm ⟨τ, i⟩) 1) - s • bv τ i ∈ Submodule.span ℂ (bv τ '' {j | j < i})) → (∀ τ i, h' (Pi.single (e.symm ⟨τ, i⟩) 1) - s • bv τ i ∈ Submodule.span ℂ (bv τ '' {j | j < i})) → h = h' := by
  first | exact @GlobalTheory.FlagEq.eq_of_flag_of_hermForm | exact GlobalTheory.FlagEq.eq_of_flag_of_hermForm | (intros; apply GlobalTheory.FlagEq.eq_of_flag_of_hermForm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContraAdmissibleTrace
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContraAdmissibleTrace
noncomputable section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace

namespace GlobalTheory.SmGL.ContraTrace

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V]

def res (π : Representation ℂ G V) (K : Subgroup G) :
    fixed (contra π) K →ₗ[ℂ] Module.Dual ℂ (fixed π K) :=
  (fixed π K).subtype.dualMap ∘ₗ (smoothPart π.dual).subtype ∘ₗ (fixed (contra π) K).subtype

theorem invariant_of_fixed {π : Representation ℂ G V} {K : Subgroup G} (l : fixed (contra π) K)
    (h : G) (hh : h ∈ K) (w : V) : (l.1 : Module.Dual ℂ V) (π h w) = (l.1 : Module.Dual ℂ V) w := by
  have h1 := mem_fixed.1 l.2 h⁻¹ (inv_mem hh)
  conv_rhs => rw [← h1]
  rw [contra_apply, inv_inv]

theorem res_bijective [T2Space G] {π : Representation ℂ G V} (hπ : IsSmooth π) {K : Subgroup G}
    (ho : IsOpen (K : Set G)) (hK : IsCompact (K : Set G)) : Function.Bijective (res π K) := by
  constructor
  · intro l l' h
    refine Subtype.ext (Subtype.ext ?_)
    exact IndDual.dual_ext hπ hK (invariant_of_fixed l) (invariant_of_fixed l')
      fun w hw => LinearMap.congr_fun h ⟨w, hw⟩
  · intro m
    obtain ⟨l₀, hl₀⟩ := LinearMap.exists_extend m
    obtain ⟨l, h1, h2⟩ := DualAverage.exists_invariant_form G V π hπ K hK l₀
    have h3 : ∀ g ∈ K, π.dual g l = l := fun g hg => LinearMap.ext fun w => h1 g⁻¹ (inv_mem hg) w
    refine ⟨⟨⟨l, mem_smoothPart_of_nhds (Filter.mem_of_superset (ho.mem_nhds (one_mem K)) h3)⟩,
      mem_fixed.2 fun g hg => Subtype.ext (h3 g hg)⟩, LinearMap.ext fun w => ?_⟩
    exact (h2 _ (mem_fixed.1 w.2)).trans (LinearMap.congr_fun hl₀ w)

theorem isAdmissible_contra [T2Space G] {π : Representation ℂ G V} (hπ : IsAdmissible π) :
    IsAdmissible (contra π) :=
  ⟨isSmooth_contra π, fun K ho hK =>
    haveI := hπ.2 K ho hK
    FiniteDimensional.of_injective (res π K) (res_bijective hπ.1 ho hK).1⟩

theorem smoothOp_contra [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] [μ.IsInvInvariant] {π : Representation ℂ G V} (hπ : IsSmooth π)
    {f : G → ℂ} (hf : IsLocallyConstant f) (hc : HasCompactSupport f) (l : smoothPart π.dual) (v : V) :
    (smoothOp (contra π) μ f l : Module.Dual ℂ V) v =
      (l : Module.Dual ℂ V) (smoothOp π μ (fun g => f g⁻¹) v) := by
  have h1 := (isSmooth_contra π).map_smoothOp (μ := μ) hf hc
    (Module.Dual.eval ℂ V v ∘ₗ (smoothPart π.dual).subtype) l
  have h2 := hπ.map_smoothOp (μ := μ) (f := fun g => f g⁻¹) (hf.comp_continuous continuous_inv)
    (hc.comp_homeomorph (Homeomorph.inv G)) (l : Module.Dual ℂ V) v
  refine h1.trans (Eq.trans ?_ h2.symm)
  rw [← integral_inv_eq_self]
  refine integral_congr_ae (.of_forall fun g => ?_)
  show f g⁻¹ • (l : Module.Dual ℂ V) (π g⁻¹⁻¹ v) = f g⁻¹ • (l : Module.Dual ℂ V) (π g v)
  rw [inv_inv]

theorem contra_admissible_trace : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsInvInvariant], (∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsAdmissible π → IsAdmissible (contra π) ∧ ∀ f : G → ℂ, IsLocallyConstant f → HasCompactSupport f → smoothTrace (contra π) μ f = smoothTrace π μ (fun g => f g⁻¹) := by
  intro G _ _ _ _ _ _ μ _ _ hG V _ _ π hπ
  refine ⟨isAdmissible_contra hπ, fun f hf hc => ?_⟩
  have hf' : IsLocallyConstant fun g => f g⁻¹ := hf.comp_continuous continuous_inv
  have hc' : HasCompactSupport fun g => f g⁻¹ := hc.comp_homeomorph (Homeomorph.inv G)
  obtain ⟨K, ho, hK, hle⟩ := hG _ (Filter.inter_mem
    ((isOpen_leftStabilizer hf hc).mem_nhds (one_mem _))
    ((isOpen_leftStabilizer hf' hc').mem_nhds (one_mem _)))
  have := hπ.2 K ho hK
  have := (isAdmissible_contra hπ).2 K ho hK
  have m1 := (isSmooth_contra π).smoothOp_mem_fixed (μ := μ) hf hc (K := K) fun k hk => (hle hk).1
  have m2 := hπ.1.smoothOp_mem_fixed (μ := μ) hf' hc' (K := K) fun k hk => (hle hk).2
  let e := LinearEquiv.ofBijective _ (res_bijective hπ.1 ho hK)
  rw [smoothTrace, smoothTrace, finRankTrace_eq _ _ m1, finRankTrace_eq _ _ m2,
    ← LinearMap.trace_transpose' (M := fixed π K), ← LinearMap.trace_conj' _ e.symm]
  congr 1
  refine LinearMap.ext fun l => e.injective ?_
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.apply_symm_apply, LinearEquiv.symm_symm]
  exact LinearMap.ext fun v => smoothOp_contra μ hπ.1 hf hc l.1 v.1

end GlobalTheory.SmGL.ContraTrace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContraAdmissibleTraceStatement
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAdmissible_contra_and_smoothTrace_inv : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsInvInvariant], (∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsAdmissible π → IsAdmissible (contra π) ∧ ∀ f : G → ℂ, IsLocallyConstant f → HasCompactSupport f → smoothTrace (contra π) μ f = smoothTrace π μ (fun g => f g⁻¹) := by
  first | exact @GlobalTheory.SmGL.ContraTrace.contra_admissible_trace | exact GlobalTheory.SmGL.ContraTrace.contra_admissible_trace | (intros; apply GlobalTheory.SmGL.ContraTrace.contra_admissible_trace <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymmetricPositionLevelShapeOnParabolic
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymmetricPositionLevelShapeOnParabolic
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

namespace GlobalTheory.SymShape

theorem block_mul_embX {F : Type} [Field F] {κ l p : ℕ} {u : GL (Fin κ ⊕ Fin l) F} (hu : u ∈ N F (Fin κ) l p)
    (γ : GL (Fin κ) F) : (u * embX l γ).val.toBlocks₁₁ = γ.val := by
  rw [Units.val_mul, GlobalTheory.RootEx.Radical.embX_val, ← Matrix.fromBlocks_toBlocks u.val,
    Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁, GlobalTheory.RootEx.Radical.toBlocks₁₁_of_mem hu]
  simp

theorem simpleSum_embX {F : Type} [Field F] {κ l : ℕ} (γ : GL (Fin κ) F) : simpleSum (embX l γ) = 0 := by
  apply GlobalTheory.RootEx.Radical.simpleSum_eq_zero
  intro i j
  rw [GlobalTheory.RootEx.Radical.embX_val, Matrix.fromBlocks_apply₂₂]

theorem sym_shape :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle) (ϖ : kˣ) (ρ κ l : ℕ)
      (P : _root_.GlobalTheory.StepData.TypeDatum k (Fin κ ⊕ Fin l)),
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsSymLevel ψ ϖ ρ P →
        (∀ u ∈ N k (Fin κ) l 1, ∀ γ : GL (Fin κ) k, u * embX l γ ∈ P.J →
          ∃ gb, Reduces γ gb ∧ IsUpperUnip Fin.val gb.val) ∧
        (∀ (γ : GL (Fin κ) k) (gb : GL (Fin κ) 𝓀[k]), Reduces γ gb →
          IsUpperUnip Fin.val gb.val → ∃ hm : embX l γ ∈ P.J,
          (P.lam ⟨_, hm⟩ : ℂ) = ψ ((ϖ⁻¹ : kˣ) * superSum Fin.val γ.val)) ∧
        ∀ u ∈ N k (Fin κ) l 1, ∀ hm : u ∈ P.J,
          (P.lam ⟨u, hm⟩ : ℂ) = ψ ((ϖ⁻¹ : kˣ) * simpleSum u) := by
  intro k _ _ _ _ ψ ϖ ρ κ l P hP
  refine ⟨?_, ?_, ?_⟩
  · intro u hu γ hm
    obtain ⟨u', hu', γ', hγ', g₀, hg₀, hr₀⟩ := (hP.1 _).1 hm
    have key : ∀ {F : Type} [Field F] (f : 𝒪[k] →+* F) (x : GL (Fin κ ⊕ Fin l) F) (y : GL (Fin κ) F),
        Matrix.GeneralLinearGroup.map f g₀ = x → x.val.toBlocks₁₁ = y.val →
          (g₀.val.toBlocks₁₁).map f = y.val := by
      intro F _ f x y h1 h2
      rw [← h2, ← h1]
      rfl
    have hBk := key (algebraMap 𝒪[k] k) _ γ hg₀ (block_mul_embX hu γ)
    have hBr := key (IsLocalRing.residue 𝒪[k]) _ γ' hr₀ (block_mul_embX hu' γ')
    have hdet : IsUnit (g₀.val.toBlocks₁₁).det := by
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
      change ((g₀.val.toBlocks₁₁).map (IsLocalRing.residue 𝒪[k])).det ≠ 0
      rw [hBr]
      exact (Matrix.isUnits_det_units γ').ne_zero
    refine ⟨γ', ⟨((Matrix.isUnit_iff_isUnit_det _).mpr hdet).unit, ?_, ?_⟩, hγ'⟩
    · exact Units.ext (by rw [← hBk]; rfl)
    · exact Units.ext (by rw [← hBr]; rfl)
  · intro γ gb hred hgb
    obtain ⟨γ₀, h1, h2⟩ := hred
    let g₀ : GL (Fin κ ⊕ Fin l) 𝒪[k] :=
      ⟨Matrix.fromBlocks γ₀.val 0 0 1, Matrix.fromBlocks (γ₀⁻¹).val 0 0 1,
        by rw [Matrix.fromBlocks_multiply]; simp, by rw [Matrix.fromBlocks_multiply]; simp⟩
    have hemb : ∀ {F : Type} [Field F] (f : 𝒪[k] →+* F),
        Matrix.GeneralLinearGroup.map f g₀ = embX l (Matrix.GeneralLinearGroup.map f γ₀) := by
      intro F _ f
      refine Units.ext ?_
      rw [GlobalTheory.RootEx.Radical.embX_val]
      change (Matrix.fromBlocks γ₀.val 0 0 1).map f = _
      rw [Matrix.fromBlocks_map]
      simp
    have hm : embX l γ ∈ P.J := (hP.1 _).2 ⟨1, one_mem _, gb, hgb, g₀, by rw [hemb, h1], by rw [hemb, h2, one_mul]⟩
    refine ⟨hm, ?_⟩
    have hblk : (embX l γ).val.toBlocks₁₁ = γ.val := by
      rw [GlobalTheory.RootEx.Radical.embX_val, Matrix.toBlocks_fromBlocks₁₁]
    rw [hP.2 ⟨_, hm⟩]
    simp only [simpleSum_embX, hblk, mul_zero, AddChar.map_zero_eq_one, Circle.coe_one, one_mul]
  · intro u hu hm
    rw [hP.2 ⟨u, hm⟩]
    simp only [GlobalTheory.RootEx.Radical.toBlocks₁₁_of_mem hu, GlobalTheory.GenericShape.superSum_one, mul_zero,
      AddChar.map_zero_eq_one, Circle.coe_one, mul_one]

end GlobalTheory.SymShape
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymmetricPositionLevelShapeOnParabolicStatement
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricPositionLevel_shape_on_parabolic :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle) (ϖ : kˣ) (ρ κ l : ℕ)
      (P : _root_.GlobalTheory.StepData.TypeDatum k (Fin κ ⊕ Fin l)),
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsSymLevel ψ ϖ ρ P →
        (∀ u ∈ N k (Fin κ) l 1, ∀ γ : GL (Fin κ) k, u * embX l γ ∈ P.J →
          ∃ gb, Reduces γ gb ∧ IsUpperUnip Fin.val gb.val) ∧
        (∀ (γ : GL (Fin κ) k) (gb : GL (Fin κ) 𝓀[k]), Reduces γ gb →
          IsUpperUnip Fin.val gb.val → ∃ hm : embX l γ ∈ P.J,
          (P.lam ⟨_, hm⟩ : ℂ) = ψ ((ϖ⁻¹ : kˣ) * superSum Fin.val γ.val)) ∧
        ∀ u ∈ N k (Fin κ) l 1, ∀ hm : u ∈ P.J,
          (P.lam ⟨u, hm⟩ : ℂ) = ψ ((ϖ⁻¹ : kˣ) * simpleSum u) := by
  exact @_root_.GlobalTheory.SymShape.sym_shape
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilFormulaRootExchangeParabolicQuotient
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilFormulaRootExchangeParabolicQuotient
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

namespace GlobalTheory.QuotIntFJ

theorem integral_rotate_three {B X U : Type} [MeasurableSpace X] [MeasurableSpace B] [MeasurableSpace U]
    (β : Measure B) (μ : Measure X) (ρ : Measure U) [SFinite μ] [SFinite β] [SFinite ρ]
    (Φ : B → X → U → ℂ) (hΦ : Integrable (fun z : B × (X × U) => Φ z.1 z.2.1 z.2.2) (β.prod (μ.prod ρ))) :
    Integrable (fun b => ∫ x, ∫ u, Φ b x u ∂ρ ∂μ) β ∧
      ∫ b, ∫ x, ∫ u, Φ b x u ∂ρ ∂μ ∂β = ∫ x, ∫ u, ∫ b, Φ b x u ∂β ∂ρ ∂μ := by
  have hsec : ∀ᵐ b ∂β, Integrable (fun y : X × U => Φ b y.1 y.2) (μ.prod ρ) := hΦ.prod_right_ae
  have hin : ∀ᵐ b ∂β, ∫ x, ∫ u, Φ b x u ∂ρ ∂μ = ∫ y : X × U, Φ b y.1 y.2 ∂(μ.prod ρ) := by
    filter_upwards [hsec] with b hb
    exact (integral_prod (fun y : X × U => Φ b y.1 y.2) hb).symm
  have hsw : Integrable (fun w : (X × U) × B => Φ w.2 w.1.1 w.1.2) ((μ.prod ρ).prod β) := hΦ.swap
  refine ⟨hΦ.integral_prod_left.congr (hin.mono fun b hb => hb.symm), ?_⟩
  calc ∫ b, ∫ x, ∫ u, Φ b x u ∂ρ ∂μ ∂β
      = ∫ b, ∫ y : X × U, Φ b y.1 y.2 ∂(μ.prod ρ) ∂β := integral_congr_ae hin
    _ = ∫ w : B × (X × U), Φ w.1 w.2.1 w.2.2 ∂(β.prod (μ.prod ρ)) := (integral_prod _ hΦ).symm
    _ = ∫ w : (X × U) × B, Φ w.2 w.1.1 w.1.2 ∂((μ.prod ρ).prod β) :=
        (integral_prod_swap (fun w : B × (X × U) => Φ w.1 w.2.1 w.2.2)).symm
    _ = ∫ y : X × U, ∫ b, Φ b y.1 y.2 ∂β ∂(μ.prod ρ) := integral_prod _ hsw
    _ = ∫ x, ∫ u, ∫ b, Φ b x u ∂β ∂ρ ∂μ :=
        integral_prod (fun y : X × U => ∫ b, Φ b y.1 y.2 ∂β) hsw.integral_prod_left

theorem weil_formula_FJ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c) (ν : Measure k) [ν.IsAddHaarMeasure] (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) (f : GL (n ⊕ Fin c) k → ℂ) (z : ℂ), IsQuotInt ν μX μG (ρ + 1) f z → (∀ h, Integrable (fun β : n → k => f (colE c (ρ + 1) β * h)) (Measure.pi fun _ => ν)) ∧ IsQuotIntFJ ν μX μG ρ (fun h => ∫ β : n → k, f (colE c (ρ + 1) β * h) ∂(Measure.pi fun _ => ν)) z := by
  intro k _ _ _ _ _ _ n _ _ c ρ hρ hρc ν _ μX _ μG f z hq
  obtain ⟨F, hF, hfF, hz⟩ := hq
  have hF' : IsLocallyConstant F ∧ HasCompactSupport F := hF
  obtain ⟨hsck, ht2k⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have := hsck
  have := ht2k
  obtain ⟨hB1, hL1, hS1, -⟩ := volGL_haar k n ν
  obtain ⟨hB2, hL2, hS2, -⟩ := volGL_haar k (n ⊕ Fin c) ν
  have := hB1
  have := hL1
  have := hS1
  have := hB2
  have := hL2
  have := hS2

  have hV : volN ν n c (ρ + 1) =
      (Measure.pi fun _ => ν).map (GlobalTheory.RootEx.VolN.coEquiv (k := k) (n := n) (c := c) (ρ + 1)) :=
    GlobalTheory.RootEx.VolN.volN_eq (n := n) (c := c) ν (ρ + 1)
  have : SigmaFinite (volN ν n c (ρ + 1)) := by
    rw [hV]
    exact (GlobalTheory.RootEx.VolN.coEquiv (k := k) (n := n) (c := c) (ρ + 1)).sigmaFinite_map
  have : IsFiniteMeasureOnCompacts (volN ν n c (ρ + 1)) := by
    rw [hV]
    refine ⟨fun K hK => ?_⟩
    rw [MeasurableEquiv.map_apply]
    have hpre : (GlobalTheory.RootEx.VolN.coEquiv (k := k) (n := n) (c := c) (ρ + 1)) ⁻¹' K =
        GlobalTheory.RootEx.VolN.co (ρ + 1) '' K := by
      ext e
      constructor
      · intro he
        exact ⟨_, he, GlobalTheory.RootEx.VolN.co_mkNel _ e⟩
      · rintro ⟨g, hg, rfl⟩
        show GlobalTheory.RootEx.Model.mkNel _ (GlobalTheory.RootEx.VolN.co _ g) ∈ K
        rw [GlobalTheory.RootEx.VolN.mkNel_co]
        exact hg
    rw [hpre]
    exact (hK.image (GlobalTheory.RootEx.VolN.continuous_co _)).measure_lt_top

  have hint : ∀ h : GL (n ⊕ Fin c) k, Integrable
      (fun w : (n → k) × (GL n k × N k n c (ρ + 1)) =>
        F (embX c w.2.1 * (w.2.2 : GL (n ⊕ Fin c) k) * colE c (ρ + 1) w.1 * h))
      ((Measure.pi fun _ => ν).prod (μX.prod (volN ν n c (ρ + 1)))) := by
    intro h
    have hcont : Continuous (fun w : (n → k) × (GL n k × N k n c (ρ + 1)) =>
        F (embX c w.2.1 * (w.2.2 : GL (n ⊕ Fin c) k) * colE c (ρ + 1) w.1 * h)) := by
      refine hF'.1.continuous.comp (Continuous.mul (Continuous.mul (Continuous.mul ?_ ?_) ?_) continuous_const)
      · exact GlobalTheory.RootEx.QuotStep.continuous_embX.comp (continuous_fst.comp continuous_snd)
      · exact continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
      · exact (GlobalTheory.RootEx.QuotStep.continuous_colE (ρ + 1)).comp continuous_fst
    obtain ⟨D, hD, hDC⟩ := GlobalTheory.T.exists_compact_preimage_embX_mul_colE k n c ρ hρ hρc ((fun g => g * h⁻¹) '' tsupport F)
      (hF'.2.image (continuous_mul_const h⁻¹))
    have hsupp : HasCompactSupport (fun w : (n → k) × (GL n k × N k n c (ρ + 1)) =>
        F (embX c w.2.1 * (w.2.2 : GL (n ⊕ Fin c) k) * colE c (ρ + 1) w.1 * h)) := by
      refine HasCompactSupport.intro
        (hD.image (f := fun t : GL n k × N k n c (ρ + 1) × (n → k) => (t.2.2, (t.1, t.2.1)))
          (by fun_prop)) ?_
      intro w hw
      by_contra hne
      apply hw
      refine ⟨(w.2.1, w.2.2, w.1), hDC _ ⟨_, subset_tsupport _ hne, ?_⟩, rfl⟩
      simp [mul_assoc]
    exact hcont.integrable_of_hasCompactSupport hsupp
  have hfeq : ∀ (h : GL (n ⊕ Fin c) k) (b : n → k), f (colE c (ρ + 1) b * h) =
      ∫ x, ∫ u : N k n c (ρ + 1), F (embX c x * (u : GL (n ⊕ Fin c) k) * colE c (ρ + 1) b * h)
        ∂(volN ν n c (ρ + 1)) ∂μX := by
    intro h b
    rw [hfF]
    simp only [mul_assoc]
  have key := fun h : GL (n ⊕ Fin c) k => integral_rotate_three (Measure.pi fun _ : n => ν) μX
    (volN ν n c (ρ + 1))
    (fun b x (u : N k n c (ρ + 1)) => F (embX c x * (u : GL (n ⊕ Fin c) k) * colE c (ρ + 1) b * h))
    (hint h)
  refine ⟨fun h => (key h).1.congr (Filter.Eventually.of_forall fun b => (hfeq h b).symm), ?_⟩
  unfold IsQuotIntFJ
  refine ⟨F, hF, fun h => ?_, hz⟩
  calc ∫ b : n → k, f (colE c (ρ + 1) b * h) ∂(Measure.pi fun _ => ν)
      = ∫ b : n → k, ∫ x, ∫ u : N k n c (ρ + 1),
          F (embX c x * (u : GL (n ⊕ Fin c) k) * colE c (ρ + 1) b * h)
            ∂(volN ν n c (ρ + 1)) ∂μX ∂(Measure.pi fun _ => ν) :=
        integral_congr_ae (Filter.Eventually.of_forall (hfeq h))
    _ = _ := (key h).2

end GlobalTheory.QuotIntFJ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilFormulaRootExchangeParabolicQuotientStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_formula_rootExchange_parabolic_quotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c) (ν : Measure k) [ν.IsAddHaarMeasure] (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) (f : GL (n ⊕ Fin c) k → ℂ) (z : ℂ), IsQuotInt ν μX μG (ρ + 1) f z → (∀ h, Integrable (fun β : n → k => f (colE c (ρ + 1) β * h)) (Measure.pi fun _ => ν)) ∧ IsQuotIntFJ ν μX μG ρ (fun h => ∫ β : n → k, f (colE c (ρ + 1) β * h) ∂(Measure.pi fun _ => ν)) z := by
  first | exact @GlobalTheory.QuotIntFJ.weil_formula_FJ | exact GlobalTheory.QuotIntFJ.weil_formula_FJ | (intros; apply GlobalTheory.QuotIntFJ.weil_formula_FJ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotIntFJUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotIntFJUnique
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

noncomputable section
namespace GlobalTheory.QuotIntFJ
open GlobalTheory.QuotInt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.QuotIntFJ.quotIntFJ_unique : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n]
    [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c) (ν : Measure k) [ν.IsAddHaarMeasure]
    (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure]
    (f : GL (n ⊕ Fin c) k → ℂ) (z z' : ℂ), _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.IsQuotIntFJ ν μX μG ρ f z →
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.IsQuotIntFJ ν μX μG ρ f z' → z = z' := by
  intro k _ _ _ _ _ _ n _ _ c ρ hρ hρc ν _ μX _ μG _ f z z' hz hz'
  obtain ⟨F₁, hF₁, hf₁, rfl⟩ := hz
  obtain ⟨F₂, hF₂, hf₂, rfl⟩ := hz'
  haveI := _root_.GlobalTheory.SplitWeil.secondCountable k
  have hA := _root_.GlobalTheory.SplitWeil.volGL_haar k n ν
  have hB := _root_.GlobalTheory.SplitWeil.volGL_haar k (n ⊕ Fin c) ν
  haveI := hA.1; haveI := hA.2.1; haveI := hB.1; haveI := hB.2.1
  set U := _root_.GlobalTheory.RootEx.N k n c (ρ + 1)
  set μU := _root_.GlobalTheory.RootEx.volN ν n c (ρ + 1)
  haveI : μU.IsHaarMeasure := _root_.GlobalTheory.RootEx.VolN.isHaarMeasure_volN ν (ρ + 1)
  haveI : SFinite μU := by
    show SFinite (_root_.GlobalTheory.RootEx.volN ν n c (ρ + 1))
    rw [_root_.GlobalTheory.RootEx.VolN.volN_eq]; infer_instance
  set emb := _root_.GlobalTheory.RootEx.embX (k := k) (n := n) c
  set col := _root_.GlobalTheory.RootEx.colE (k := k) (n := n) c (ρ + 1)
  let m : GL n k × (U × (n → k)) → GL (n ⊕ Fin c) k := fun p => emb p.1 * ↑p.2.1 * col p.2.2
  have hm : Continuous m := by
    refine (_root_.GlobalTheory.RootEx.QuotStep.continuous_embX.comp continuous_fst).mul
      (continuous_subtype_val.comp (continuous_fst.comp continuous_snd)) |>.mul
      ((_root_.GlobalTheory.RootEx.QuotStep.continuous_colE (ρ + 1)).comp
        (continuous_snd.comp continuous_snd))
  have hSB : ∀ φ ∈ _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k), Continuous φ ∧ HasCompactSupport φ :=
    fun φ hφ => ⟨hφ.1.continuous, hφ.2⟩
  have hcs : ∀ φ ∈ _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k), ∃ D : Set (GL n k × (U × (n → k))),
      IsCompact D ∧ ∀ p, φ (m p) ≠ 0 → p ∈ D := by
    intro φ hφ
    obtain ⟨D, hD, hDm⟩ := _root_.GlobalTheory.RootEx.ProperTriple.proper_triple k n c ρ hρ hρc (tsupport φ) (hSB φ hφ).2
    exact ⟨D, hD, fun p hp => hDm p (subset_tsupport _ hp)⟩
  set μP := μX.prod (μU.prod (Measure.pi fun _ : n => ν))
  have hint : ∀ φ ∈ _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k),
      Integrable (fun p => φ (m p)) μP := by
    intro φ hφ
    obtain ⟨D, hD, hDm⟩ := hcs φ hφ
    refine ((hSB φ hφ).1.comp hm).integrable_of_hasCompactSupport ?_
    exact HasCompactSupport.intro hD (fun p hp => by by_contra h; exact hp (hDm p h))
  have hint2 : ∀ φ ∈ _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k), ∀ g : GL n k,
      Integrable (fun y : U × (n → k) => φ (m (g, y))) (μU.prod (Measure.pi fun _ : n => ν)) := by
    intro φ hφ g
    obtain ⟨D, hD, hDm⟩ := hcs φ hφ
    refine ((hSB φ hφ).1.comp (hm.comp (Continuous.prodMk_right g))).integrable_of_hasCompactSupport ?_
    exact HasCompactSupport.intro (hD.image continuous_snd)
      (fun y hy => by by_contra h; exact hy ⟨(g, y), hDm _ h, rfl⟩)
  set Λ : (GL (n ⊕ Fin c) k → ℂ) → ℂ := fun φ => ∫ (g : GL n k), ∫ (u : U),
      ∫ (β : n → k), φ (emb g * ↑u * col β) ∂Measure.pi fun _ ↦ ν ∂μU ∂μX with hΛ
  have hΛP : ∀ φ ∈ _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k), Λ φ = ∫ p, φ (m p) ∂μP := by
    intro φ hφ
    rw [integral_prod _ (hint φ hφ)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    exact (integral_prod _ (hint2 φ hφ g)).symm
  set R := _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.RFJ k n c ρ
  have hmR : ∀ p, m p ∈ R := by
    intro p
    have h1 : emb p.1 ∈ R :=
      (le_sup_right : _root_.GlobalTheory.RootEx.R k n c (ρ + 1) ≤ R)
        ((le_sup_left : emb.range ≤ _) ⟨p.1, rfl⟩)
    have h2 : (p.2.1 : GL (n ⊕ Fin c) k) ∈ R :=
      (le_sup_right : _root_.GlobalTheory.RootEx.R k n c (ρ + 1) ≤ R)
        ((le_sup_right : U ≤ _) p.2.1.2)
    have h3 : col p.2.2 ∈ R := (le_sup_left : _root_.GlobalTheory.RootEx.R k n c ρ ≤ R)
      ((le_sup_right : _root_.GlobalTheory.RootEx.N k n c ρ ≤ _)
        (_root_.GlobalTheory.RootEx.Radical.colE_mem _ (Nat.lt_succ_self ρ)))
    exact R.mul_mem (R.mul_mem h1 h2) h3
  have hadd : ∀ φ ∈ _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k),
      ∀ ψ ∈ _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k), Λ (φ + ψ) = Λ φ + Λ ψ := by
    intro φ hφ ψ hψ
    rw [hΛP _ (add_mem hφ hψ), hΛP _ hφ, hΛP _ hψ, ← integral_add (hint φ hφ) (hint ψ hψ)]
    rfl
  have hsmul : ∀ (a : ℂ) (φ : GL (n ⊕ Fin c) k → ℂ), (Λ fun g ↦ a * φ g) = a * Λ φ := by
    intro a φ
    simp only [hΛ]
    rw [← integral_const_mul]; congr 1; funext g
    rw [← integral_const_mul]; congr 1; funext u
    rw [← integral_const_mul]
  have hloc : ∀ (φ ψ : GL (n ⊕ Fin c) k → ℂ), (∀ r ∈ R, φ r = ψ r) → Λ φ = Λ ψ := by
    intro φ ψ h
    simp only [hΛ]
    congr 1; funext g; congr 1; funext u; congr 1; funext β
    exact h _ (hmR (g, u, β))
  have hpos : ∀ φ ∈ _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k), (∀ g, φ g = 0 ∨ φ g = 1) →
      (∃ r ∈ R, φ r = 1) → Λ φ ≠ 0 := by
    intro φ hφ h01 ⟨r, hr, hr1⟩
    obtain ⟨r', hr', β, rfl⟩ :=
      ((_root_.GlobalTheory.RootEx.FourierJacobiGroup.mem_RFJ_iff k n c ρ hρ hρc).1 r).1 hr
    obtain ⟨x, u, hu, rfl⟩ := _root_.GlobalTheory.RootEx.Radical.exists_of_mem_R hr'
    have hre : ∀ p, φ (m p) = ((φ (m p)).re : ℂ) := by
      intro p
      rcases h01 (m p) with h | h <;> simp [h]
    rw [hΛP φ hφ, integral_congr_ae (Filter.Eventually.of_forall hre), integral_complex_ofReal]
    obtain ⟨D, hD, hDm⟩ := hcs φ hφ
    have hpos := Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := μP)
      (x := (x, ⟨u, hu⟩, β)) (Complex.continuous_re.comp ((hSB φ hφ).1.comp hm))
      (HasCompactSupport.intro hD (fun p hp => by
        by_contra h
        exact hp (hDm p (fun h' => h (by simp [h'])))))
      (fun p => by rcases h01 (m p) with h | h <;> simp [h])
      (by show (φ (emb x * u * col β)).re ≠ 0; rw [hr1]; simp)
    exact_mod_cast hpos.ne'
  let H : Subgroup (GL (n ⊕ Fin c) k) :=
    { carrier := {r | ∀ φ : GL (n ⊕ Fin c) k → ℂ, (Λ fun g ↦ φ (r * g)) = Λ φ}
      mul_mem' := fun {a b} ha hb φ => by
        have e : (fun g ↦ φ (a * b * g)) = fun g ↦ (fun y ↦ φ (a * y)) (b * g) := by
          funext g; simp only [mul_assoc]
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [e, hb (fun y ↦ φ (a * y)), ha φ]
      one_mem' := fun φ => by simp only [one_mul]
      inv_mem' := fun {a} ha φ => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        have := ha (fun y ↦ φ (a⁻¹ * y))
        simp only [inv_mul_cancel_left] at this
        exact this.symm }
  have hembH : ∀ x : GL n k, emb x ∈ H := by
    intro x φ
    simp only [hΛ]
    have e : ∀ (g : GL n k) (u : U) (β : n → k),
        emb x * (emb g * ↑u * col β) = emb (x * g) * ↑u * col β := by
      intro g u β; simp only [map_mul, mul_assoc]
    simp only [e]
    exact integral_mul_left_eq_self (μ := μX)
      (fun g ↦ ∫ (u : U), ∫ (β : n → k), φ (emb g * ↑u * col β) ∂Measure.pi fun _ ↦ ν ∂μU) x
  have hUH : ∀ v ∈ U, v ∈ H := by
    intro v hv φ
    simp only [hΛ]
    congr 1; funext g
    have hw : (emb g)⁻¹ * v * emb g ∈ U :=
      _root_.GlobalTheory.RootEx.Model.conj_mem hv g
    have e : ∀ (u : U) (β : n → k), v * (emb g * ↑u * col β) =
        emb g * ↑((⟨_, hw⟩ : U) * u) * col β := by
      intro u β; simp only [Subgroup.coe_mul]; group
    simp only [e]
    exact integral_mul_left_eq_self (μ := μU)
      (fun u : U ↦ ∫ (β : n → k), φ (emb g * ↑u * col β) ∂Measure.pi fun _ ↦ ν) (⟨_, hw⟩ : U)
  have hcolH : ∀ γ : n → k, col γ ∈ H := by
    intro γ φ
    simp only [hΛ]
    congr 1; funext g
    set δ : n → k := (↑g⁻¹ : Matrix n n k) *ᵥ γ
    have hconj : emb g⁻¹ * col γ * (emb g⁻¹)⁻¹ = col δ :=
      _root_.GlobalTheory.RootEx.QuotStep.conj_colE (ρ + 1) g⁻¹ γ
    have e : ∀ (u : U) (β : n → k), col γ * (emb g * ↑u * col β) =
        emb g * (col δ * ↑u * (col δ)⁻¹) * col (δ + β) := by
      intro u β
      have hc : col (δ + β) = col δ * col β := (_root_.GlobalTheory.RootEx.FourierJacobiGroup.colE_add (ρ + 1) δ β).symm
      rw [hc, ← hconj]
      simp only [map_inv, inv_inv]
      group
    simp only [e]
    have hβ : ∀ y : GL (n ⊕ Fin c) k,
        ∫ (β : n → k), φ (emb g * y * col (δ + β)) ∂(Measure.pi fun _ ↦ ν) =
        ∫ (β : n → k), φ (emb g * y * col β) ∂(Measure.pi fun _ ↦ ν) := fun y =>
      integral_add_left_eq_self (fun β ↦ φ (emb g * y * col β)) δ
    simp only [hβ]
    exact _root_.GlobalTheory.RootEx.ConjVol.integral_conj_colE k n c ρ hρ hρc ν δ
      (fun y ↦ ∫ (β : n → k), φ (emb g * y * col β) ∂Measure.pi fun _ ↦ ν)
  have hinv : ∀ r ∈ R, ∀ (φ : GL (n ⊕ Fin c) k → ℂ), (Λ fun g ↦ φ (r * g)) = Λ φ := by
    intro r hr
    obtain ⟨r', hr', β, rfl⟩ :=
      ((_root_.GlobalTheory.RootEx.FourierJacobiGroup.mem_RFJ_iff k n c ρ hρ hρc).1 r).1 hr
    obtain ⟨x, u, hu, rfl⟩ := _root_.GlobalTheory.RootEx.Radical.exists_of_mem_R hr'
    exact H.mul_mem (H.mul_mem (hembH x) (hUH u hu)) (hcolH β)
  have hF : (F₁ - F₂) ∈ _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k) := sub_mem hF₁ hF₂
  have hG : ∀ φ ∈ _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k), Integrable φ μG :=
    fun φ hφ => (hSB φ hφ).1.integrable_of_hasCompactSupport (hSB φ hφ).2
  have hΛf : ∀ F ∈ _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k),
      (∀ h, f h = ∫ (g : GL n k), ∫ (u : U), ∫ (β : n → k), F (emb g * ↑u * col β * h)
        ∂(Measure.pi fun _ ↦ ν) ∂μU ∂μX) → ∀ h, (Λ fun g ↦ F (g * h)) = f h := by
    intro F _ hf h
    rw [hf h]
  have key := _root_.GlobalTheory.QuotInt.integral_eq_zero_of_avg μG _ hB.2.2.2.2.1 hB.2.2.2.1
    R Λ hadd hsmul hloc hinv hpos hF (fun h => by
      have e : (fun g => (F₁ - F₂) (g * h)) =
          (fun g => F₁ (g * h)) + (fun g => (-1 : ℂ) * F₂ (g * h)) := by
        funext g; simp [sub_eq_add_neg]
      have hneg : (fun g => (-1 : ℂ) * F₂ (g * h)) ∈
          _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k) :=
        (_root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k)).smul_mem (-1 : ℂ)
          (_root_.GlobalTheory.QuotInt.sb_right hF₂ h)
      rw [e, hadd _ (_root_.GlobalTheory.QuotInt.sb_right hF₁ h) _ hneg,
        hsmul (-1) (fun g => F₂ (g * h)), hΛf F₁ hF₁ hf₁ h, hΛf F₂ hF₂ hf₂ h]
      ring)
  have hsub : ∫ g, (F₁ - F₂) g ∂μG = ∫ g, F₁ g ∂μG - ∫ g, F₂ g ∂μG :=
    integral_sub (hG _ hF₁) (hG _ hF₂)
  rw [hsub] at key
  exact sub_eq_zero.1 key

end GlobalTheory.QuotIntFJ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotIntFJUniqueStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_isQuotIntFJ_of_isQuotIntFJ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c) (ν : Measure k) [ν.IsAddHaarMeasure] (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (f : GL (n ⊕ Fin c) k → ℂ) (z z' : ℂ), IsQuotIntFJ ν μX μG ρ f z → IsQuotIntFJ ν μX μG ρ f z' → z = z' := by
  first | exact @GlobalTheory.QuotIntFJ.quotIntFJ_unique | exact GlobalTheory.QuotIntFJ.quotIntFJ_unique | (intros; apply GlobalTheory.QuotIntFJ.quotIntFJ_unique <;> assumption)
end
end
