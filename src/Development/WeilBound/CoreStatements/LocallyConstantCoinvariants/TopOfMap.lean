module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTwistedRankQuotient
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreRepresentationSmooth

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.LocConstChar
noncomputable section

namespace PositivityTheory.KCo

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen GlobalTheory.CompanionTheory.ThetaGLLen.FullRank Matrix Topology
  MeasureTheory

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a : Type} [Fintype a] [DecidableEq a] {κ : ℕ}

theorem common_gen (hκ : κ = Fintype.card a) (w w' : SB (RankIn (k := k) (a := a) (b := a) {κ})) :
    ∃ t, w ∈ Submodule.span ℂ (Set.range fun g : GL a k => rightRep (k := k) a a κ g t) ∧
      w' ∈ Submodule.span ℂ (Set.range fun g : GL a k => rightRep (k := k) a a κ g t) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have : NonarchimedeanAddGroup k := ⟨fun V hV => by
    obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset hV
    exact ⟨⟨⟨⟨⟨GlobalTheory.SplitWeil.cball s, GlobalTheory.SplitWeil.add_mem_cball⟩, by simp [GlobalTheory.SplitWeil.cball]⟩,
      GlobalTheory.SplitWeil.neg_mem_cball⟩, GlobalTheory.SplitWeil.isOpen_cball s⟩, hs⟩⟩
  have : TotallyDisconnectedSpace k := inferInstance
  have : TotallyDisconnectedSpace (Matrix a a k) := inferInstanceAs (TotallyDisconnectedSpace (a → a → k))
  have : LocallyCompactSpace (Matrix a a k) := inferInstanceAs (LocallyCompactSpace (a → a → k))
  have : TotallyDisconnectedSpace (GL a k) :=
    ⟨(isTotallyDisconnected_of_image (f := fun g : GL a k => g.val) GlobalTheory.SplitFlip.isEmbedding_val_GL.continuous.continuousOn
      GlobalTheory.SplitFlip.isEmbedding_val_GL.injective (isTotallyDisconnected_of_totallyDisconnectedSpace _))⟩
  let := rMul (k := k) (a := a) (c := a) κ
  have hsm : ∀ (g : GL a k) (x : RankIn (k := k) (a := a) (b := a) {κ}), g • x = rAct {κ} x g⁻¹ := fun _ _ => rfl
  have : ContinuousSMul (GL a k) (RankIn (k := k) (a := a) (b := a) {κ}) := ⟨continuous_rAct_inv κ⟩
  have : MulAction.IsPretransitive (GL a k) (RankIn (k := k) (a := a) (b := a) {κ}) := ⟨fun x y => by
    obtain ⟨g, hg⟩ := exists_gl_eq_mul_of_rank k a a x.1 y.1 (x.2.trans hκ) (y.2.trans hκ)
    refine ⟨g⁻¹, Subtype.ext ?_⟩
    rw [hsm, inv_inv, rAct_val, hg]⟩
  have hXo : IsOpen {x : Matrix a a k | x.rank ∈ ({κ} : Set ℕ)} := by
    convert isOpen_le_rank (k := k) (a := a) (b := a) κ using 1
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    exact ⟨fun h => h.ge, fun h => le_antisymm ((Matrix.rank_le_card_height x).trans hκ.ge) h⟩
  have : LocallyCompactSpace (RankIn (k := k) (a := a) (b := a) {κ}) := hXo.locallyCompactSpace
  have hop : ∀ x : RankIn (k := k) (a := a) (b := a) {κ}, IsOpenMap fun g : GL a k => g • x :=
    fun x => isOpenMap_smul_of_sigmaCompact x
  have hρ : ∀ (g : GL a k) (f : SB (RankIn (k := k) (a := a) (b := a) {κ})) (x : RankIn (k := k) (a := a) (b := a) {κ}),
      (rightRep (k := k) a a κ g f).1 x = f.1 (g⁻¹ • x) := by
    intro g f x
    show _ = f.1 (rAct {κ} x g⁻¹⁻¹)
    rw [inv_inv]
    rfl
  exact exists_common_generator (rightRep (k := k) a a κ) hρ hop GlobalTheory.SplitFlip.isCompact_KO GlobalTheory.SplitFlip.isOpen_KO w w'

def toRank (hκ : κ = Fintype.card a) (g : GL a k) : RankIn (k := k) (a := a) (b := a) {κ} :=
  ⟨g.val, (Matrix.rank_unit g).trans hκ.symm⟩

theorem toRank_surj (hκ : κ = Fintype.card a) : Function.Surjective (toRank (k := k) hκ) := fun x => by
  obtain ⟨g, hg⟩ := exists_gl_eq_mul_of_rank k a a (1 : Matrix a a k) x.1 (by simp) (x.2.trans hκ)
  exact ⟨g, Subtype.ext (by rw [hg, Matrix.one_mul]; rfl)⟩

def rankHomeo (hκ : κ = Fintype.card a) : GL a k ≃ₜ RankIn (k := k) (a := a) (b := a) {κ} :=
  IsEmbedding.toHomeomorphOfSurjective (f := toRank hκ)
    ((IsEmbedding.subtypeVal.of_comp_iff (f := toRank hκ)).1 (GlobalTheory.SplitFlip.isEmbedding_val_GL (k := k) (n := a))) (toRank_surj hκ)

theorem locConst_char {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {χ : G →* ℂˣ} (h : IsSmoothChar χ) :
    IsLocallyConstant fun g => (χ g : ℂ) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_
  have : IsOpen ((fun x => g⁻¹ * x) ⁻¹' (χ.ker : Set G)) := h.preimage (continuous_const.mul continuous_id)
  filter_upwards [this.mem_nhds (by simp)] with x hx
  have hx' : χ (g⁻¹ * x) = 1 := hx
  rw [map_mul, map_inv, inv_mul_eq_one] at hx'
  rw [hx']

theorem exists_fun (hκ : κ = Fintype.card a) {ξ : GL a k →* ℂˣ} (hξ : IsSmoothChar ξ) :
    ∃ l : SB (RankIn (k := k) (a := a) (b := a) {κ}) →ₗ[ℂ] ℂ, Function.Surjective l ∧
      (∀ (g p : GL a k) φ, l (fibBase a a κ (g, p) φ) = (ξ p : ℂ) * ((ξ g)⁻¹ : ℂˣ) * l φ) ∧
      ∀ φ, l φ = 0 → φ ∈ twRel (rightRep (k := k) a a κ) ξ⁻¹ := by
  borelize k
  let μ : Measure (GL a k) := GlobalTheory.SplitFlip.haarVol (KO k a)
  have hc := (locConst_char hξ).continuous
  have hint : ∀ φ : SB (RankIn (k := k) (a := a) (b := a) {κ}), Integrable (fun g => φ.1 (rankHomeo hκ g) * (ξ g : ℂ)) μ := fun φ =>
    ((φ.2.1.continuous.comp (rankHomeo hκ).continuous).mul hc).integrable_of_hasCompactSupport
      (φ.2.2.comp_homeomorph (rankHomeo hκ)).mul_right
  let l : SB (RankIn (k := k) (a := a) (b := a) {κ}) →ₗ[ℂ] ℂ :=
    { toFun := fun φ => ∫ g, φ.1 (rankHomeo hκ g) * (ξ g : ℂ) ∂μ
      map_add' := fun φ ψ => by
        rw [← integral_add (hint φ) (hint ψ)]
        exact integral_congr_ae (Filter.Eventually.of_forall fun g => add_mul _ _ _)
      map_smul' := fun c φ => by
        rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun g => mul_assoc _ _ _) }
  have hl : ∀ (g p : GL a k) φ, l (fibBase a a κ (g, p) φ) = (ξ p : ℂ) * ((ξ g)⁻¹ : ℂˣ) * l φ := by
    intro g p φ
    have h1 := integral_mul_left_eq_self (μ := μ) (fun y => φ.1 (rankHomeo hκ y) * (ξ y : ℂ)) p⁻¹
    have h2 := integral_mul_right_eq_self (μ := μ) (fun y => φ.1 (rankHomeo hκ (y * 1)) * (ξ y : ℂ)) g
    have h3 := integral_mul_left_eq_self (μ := μ) (fun y => φ.1 (rankHomeo hκ (y * g)) * (ξ (y * g) : ℂ)) p⁻¹
    simp only [mul_one] at h2
    change ∫ y, _ ∂μ = _ * ∫ y, φ.1 (rankHomeo hκ y) * (ξ y : ℂ) ∂μ
    rw [← h2, ← h3, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have e : (fibBase a a κ (g, p) φ).1 (rankHomeo hκ y) = φ.1 (rankHomeo hκ (p⁻¹ * y * g)) := congrArg φ.1 (Subtype.ext rfl)
    simp only [e, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp
  have hK : IsClopen (KO k a : Set (GL a k)) := ⟨Subgroup.isClosed_of_isOpen _ GlobalTheory.SplitFlip.isOpen_KO, GlobalTheory.SplitFlip.isOpen_KO⟩
  let f : GL a k → ℂ := fun g => (KO k a : Set (GL a k)).indicator 1 g * ((ξ⁻¹ g : ℂˣ) : ℂ)
  have hf : f ∈ SB (GL a k) := ⟨(LocallyConstant.charFn ℂ hK).2.mul (locConst_char hξ.inv),
    HasCompactSupport.mul_right (HasCompactSupport.intro GlobalTheory.SplitFlip.isCompact_KO fun x hx => Set.indicator_of_notMem hx _)⟩
  let φ₀ : SB (RankIn (k := k) (a := a) (b := a) {κ}) := ⟨f ∘ (rankHomeo hκ).symm, hf.1.comp_continuous (rankHomeo hκ).symm.continuous,
    hf.2.comp_homeomorph _⟩
  have h0 : l φ₀ ≠ 0 := by
    have e : l φ₀ = ∫ g, (KO k a : Set (GL a k)).indicator (fun _ => (1 : ℂ)) g ∂μ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      simp only [φ₀, f, Function.comp, Homeomorph.symm_apply_apply, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
      rw [mul_assoc, inv_mul_cancel₀ (ξ g).ne_zero, mul_one]
      rfl
    rw [e, integral_indicator hK.isOpen.measurableSet, setIntegral_const]
    have := (ENNReal.toReal_pos (hK.isOpen.measure_pos μ ⟨1, one_mem _⟩).ne' GlobalTheory.SplitFlip.isCompact_KO.measure_lt_top.ne).ne'
    simpa [Measure.real] using this
  have key : ∀ t w, w ∈ Submodule.span ℂ (Set.range fun g : GL a k => rightRep (k := k) a a κ g t) →
      ∃ s : ℂ, w - s • t ∈ twRel (rightRep (k := k) a a κ) ξ⁻¹ ∧ l w = s * l t := by
    intro t w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact ⟨_, Submodule.subset_span ⟨g, t, rfl⟩, (hl g 1 t).trans (by simp)⟩
    | zero => exact ⟨0, by simp, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs, e⟩ := hx
      obtain ⟨u, hu, e'⟩ := hy
      exact ⟨s + u, by convert add_mem hs hu using 1; rw [add_smul]; abel, by rw [map_add (f := _), e, e', add_mul]⟩
    | smul c x _ hx =>
      obtain ⟨s, hs, e⟩ := hx
      exact ⟨c * s, by convert Submodule.smul_mem _ c hs using 1; rw [smul_sub, smul_smul],
        by rw [map_smul, e, smul_eq_mul, mul_assoc]⟩
  refine ⟨l, fun z => ⟨(z / l φ₀) • φ₀, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ h0]⟩, hl, fun φ hφ => ?_⟩
  obtain ⟨t, h1, h2⟩ := common_gen hκ φ φ₀
  obtain ⟨s, hs, e⟩ := key t φ h1
  obtain ⟨s₀, -, e₀⟩ := key t φ₀ h2
  have ht : l t ≠ 0 := fun h => h0 (by rw [e₀, h, mul_zero])
  rw [(mul_eq_zero.1 (e.symm.trans hφ)).resolve_right ht, zero_smul, sub_zero] at hs
  exact hs

end PositivityTheory.KCo
end
end

noncomputable section

namespace PositivityTheory.KCo

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
open scoped TensorProduct

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem top_of_map {V U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U] (Φ : V →ₗ[ℂ] U) {R N : Submodule ℂ V}
    (hK : ∀ f, Φ f = 0 → f ∈ R) (hR : R ≤ N) (h : N.map Φ = ⊤) : N = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have hv : Φ v ∈ N.map Φ := by rw [h]; exact Submodule.mem_top
  obtain ⟨n, hn, hnv⟩ := hv
  have hker : v - n ∈ N := hR (hK _ (by rw [map_sub, hnv, sub_self]))
  have := N.add_mem hker hn
  simpa using this

theorem irr_gen (hB : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) (n t : ℕ) {μ : kˣ →* ℂˣ} (hμ : IsSmoothChar μ)
    (hu : ∀ x, ‖(μ x : ℂ)‖ = 1) {Γ W : Type} [Group Γ] [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (Γ × (GL (Fin n) k × GL (Fin t) k)) W) (hτ : IsSmooth (τ.comp (MonoidHom.inr Γ _)))
    (l : W →ₗ[ℂ] ℂ) (hs : Function.Surjective l)
    (hτl : ∀ g p₁ p₂ φ, l (τ (g, p₁, p₂) φ) = (μ (GeneralLinearGroup.det p₂) : ℂ) * l φ)
    (hk : ∀ x, l x = 0 → x ∈ twRel (τ.comp (MonoidHom.inl Γ _)) 1)
    (N : Submodule ℂ (IndSp (two (stdSum (rfl : n + t = n + t)))
      (MonoidHom.comp (τ.comp (MonoidHom.inr _ _)) (leviTwo k (Fin n) (Fin t)).symm.toMonoidHom)))
    (hR : twRel ((indSnd (stdSum rfl) τ).comp (MonoidHom.inl _ _)) 1 ≤ N)
    (hN : ∀ h, ∀ f ∈ N, indSnd (stdSum rfl) τ (1, h) f ∈ N) :
    N = ⊤ ∨ N ≤ twRel ((indSnd (stdSum rfl) τ).comp (MonoidHom.inl _ _)) 1 := by
  let e := stdSum (rfl : n + t = n + t)
  obtain ⟨-, -, -, -, -, hcont, hP, -, hPK⟩ := GlobalTheory.SmGL.LeviInt.levi_integral_facts k _ (Fin (n + t)) _ (two e)
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  let ρ : Representation ℂ (Levi k (Two (Fin n) (Fin t))) _ :=
    MonoidHom.comp (τ.comp (MonoidHom.inr Γ _)) (leviTwo k (Fin n) (Fin t)).symm.toMonoidHom
  let π₁ := detRep (Fin n) (1 : kˣ →* ℂˣ)
  let π₂ := detRep (Fin t) μ
  let ρD : Representation ℂ (Levi k (Two (Fin n) (Fin t))) (ℂ ⊗[ℂ] ℂ) :=
    (extTensor π₁ π₂).comp (leviTwo k (Fin n) (Fin t)).symm.toMonoidHom
  let q : ρ.IntertwiningMap ρD :=
    { toLinearMap := (TensorProduct.lid ℂ ℂ).symm.toLinearMap ∘ₗ l
      isIntertwining' := fun m => LinearMap.ext fun φ => by
        change (TensorProduct.lid ℂ ℂ).symm (l (τ (1, m false, m true) φ)) =
          extTensor π₁ π₂ (m false, m true) ((TensorProduct.lid ℂ ℂ).symm (l φ))
        rw [hτl]
        simp [π₁, π₂, detRep] }
  have hq : Function.Surjective q := (TensorProduct.lid ℂ ℂ).symm.surjective.comp hs
  have hρ : IsSmooth ρ := isSmooth_comp hτ _ ((continuous_apply false).prodMk (continuous_apply true))
  have hI : (parInd (two e) ρD).IsIrreducible := hB k n t ℂ ℂ π₁ π₂
    ((isSmooth_ofChar_iff _).2 (IsSmoothChar.detChar (by unfold IsSmoothChar; simp))) (isIrreducible_ofChar _)
    ((isUnitarisable_ofChar_iff _).2 fun g => by simp)
    ((isSmooth_ofChar_iff _).2 hμ.detChar) (isIrreducible_ofChar _) ((isUnitarisable_ofChar_iff _).2 fun g => hu _)
  let σ := (twist ρ (deltaHalf k (Two (Fin n) (Fin t)))).comp (leviProj k (two e))
  have hσ : IsSmooth σ := isSmooth_comp (isSmooth_twist hρ (isSmoothChar_deltaHalf k)) _ hcont
  let α : Representation.IntertwiningMap σ ((twist ρD (deltaHalf k (Two (Fin n) (Fin t)))).comp (leviProj k (two e))) :=
    compMap (twistMap q _) _
  let T : Γ → Representation.IntertwiningMap σ σ := fun γ =>
    compMap (twistMap (actFst τ γ) (deltaHalf k (Two (Fin n) (Fin t)))) (leviProj k (two e))
  have hker0 : ∀ x, α x = 0 → x ∈ Submodule.span ℂ {y | ∃ γ z, y = T γ z - z} := by
    intro x hx
    have h0 : l x = 0 := (TensorProduct.lid ℂ ℂ).symm.map_eq_zero_iff.1 hx
    refine (Submodule.span_le (p := Submodule.span ℂ {y | ∃ γ z, y = T γ z - z})).2 ?_ (hk x h0)
    rintro _ ⟨γ, v, rfl⟩
    refine Submodule.subset_span ⟨γ, v, ?_⟩
    rw [MonoidHom.one_apply, Units.val_one, one_smul]
    rfl
  obtain ⟨-, hker⟩ := GlobalTheory.SmGL.IndCoinv.smInd_coinvariants (GL (Fin (n + t)) k) (parab k (two e)) (KO k _) hP
    GlobalTheory.SplitFlip.isCompact_KO hPK (GlobalTheory.SmGL.exists_open_normalised_subgroup_subset k _) _ _ σ _ hσ α _ T (fun y => hq y) hker0
  let Φ : (parInd (two e) ρ).IntertwiningMap (parInd (two e) ρD) := parIndMap (two e) q
  have hK : ∀ f, Φ f = 0 → f ∈ twRel ((indSnd e τ).comp (MonoidHom.inl _ _)) 1 := fun f hf => by
    refine (Submodule.span_le (p := twRel ((indSnd e τ).comp (MonoidHom.inl _ _)) 1)).2 ?_ (hker f hf)
    rintro _ ⟨γ, z, rfl⟩
    refine Submodule.subset_span ⟨γ, z, ?_⟩
    rw [MonoidHom.one_apply, Units.val_one, one_smul]
    congr 1
    refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    show τ (γ, 1) (z.1.1 x) = τ (γ, 1) (z.1.1 (x * 1))
    rw [mul_one]
  let S : Subrepresentation (parInd (two e) ρD) := ⟨N.map Φ.toLinearMap, by
    rintro h _ ⟨f, hf, rfl⟩
    refine ⟨_, hN h f hf, ?_⟩
    rw [indSnd_inr]
    exact Φ.isIntertwining _ _ h f⟩
  rcases hI.eq_bot_or_eq_top S with h | h
  · refine Or.inr fun f hf => hK f ?_
    have : Φ.toLinearMap f ∈ S.toSubmodule := ⟨f, hf, rfl⟩
    rw [h] at this
    exact this
  · exact Or.inl (top_of_map Φ.toLinearMap hK hR (congrArg Subrepresentation.toSubmodule h))

theorem irr_ind (hB : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) (n t : ℕ) {μ : kˣ →* ℂˣ} (hμ : IsSmoothChar μ)
    (hu : ∀ x, ‖(μ x : ℂ)‖ = 1) (N : Submodule ℂ (IndSp (two (stdSum (rfl : n + t = n + t)))
      (MonoidHom.comp ((fibRep (Fin n) (Fin n) (Fin t) μ n).comp (MonoidHom.inr _ _)) (leviTwo k (Fin n) (Fin t)).symm.toMonoidHom)))
    (hR : twRel ((indSnd (stdSum rfl) (fibRep (Fin n) (Fin n) (Fin t) μ n)).comp (MonoidHom.inl _ _)) 1 ≤ N)
    (hN : ∀ h, ∀ f ∈ N, indSnd (stdSum rfl) (fibRep (Fin n) (Fin n) (Fin t) μ n) (1, h) f ∈ N) :
    N = ⊤ ∨ N ≤ twRel ((indSnd (stdSum rfl) (fibRep (Fin n) (Fin n) (Fin t) μ n)).comp (MonoidHom.inl _ _)) 1 := by
  let τ := fibRep (Fin n) (Fin n) (Fin t) μ n
  let ξ : GL (Fin n) k →* ℂˣ := detChar (Fin n) (μ⁻¹ * absPow k (((Fintype.card (Fin n) : ℂ) + Fintype.card (Fin t)) / 2))
  have hξ : IsSmoothChar ξ := (hμ.inv.mul (isSmoothChar_of_isUnram (isUnram_absPow k _))).detChar
  obtain ⟨l, hs, hl, hk⟩ := exists_fun (k := k) (κ := n) (Fintype.card_fin n).symm hξ
  have hτ : IsSmooth (τ.comp (MonoidHom.inr _ _)) := GlobalTheory.T.fibre_representation_smooth k _ _ _ μ hμ n
  have hτl : ∀ g p₁ p₂ φ, l (τ (g, p₁, p₂) φ) = (μ (GeneralLinearGroup.det p₂) : ℂ) * l φ := by
    intro g p₁ p₂ φ
    change l ((fibChar (Fin n) (Fin n) (Fin t) μ (g, p₁, p₂) : ℂ) • fibBase (Fin n) (Fin n) n (g, p₁) φ) = _
    rw [map_smul, hl, smul_eq_mul, ← mul_assoc]
    congr 1
    have a1 : ∀ (x : kˣ) (s s' s'' : ℂ), s + s' + s'' = 0 → absPow k s x * absPow k s' x * absPow k s'' x = 1 := fun x s s' s'' h => by
      rw [← MonoidHom.mul_apply, ← absPow_add, ← MonoidHom.mul_apply, ← absPow_add, h]
      exact Units.ext (by simp [val_absPow])
    have b1 := congrArg Units.val (a1 (GeneralLinearGroup.det p₁) (-(n : ℂ) / 2) (-(t : ℂ) / 2) (((n : ℂ) + t) / 2) (by ring))
    have b2 := congrArg Units.val (a1 (GeneralLinearGroup.det p₂) (-(n : ℂ) / 2) ((n : ℂ) / 2) 0 (by ring))
    simp only [fibChar, ξ, MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.coe_fst, MonoidHom.coe_snd, detChar_apply,
      Units.val_mul, MonoidHom.inv_apply, Fintype.card_fin, Units.val_inv_eq_inv_val, Units.val_one, val_absPow, Complex.cpow_zero,
      mul_one] at b1 b2 ⊢
    have n1 := (μ (GeneralLinearGroup.det g)).ne_zero
    have n2 := (μ (GeneralLinearGroup.det p₁)).ne_zero
    have n3 := (absPow k (((n : ℂ) + t) / 2) (GeneralLinearGroup.det g)).ne_zero
    rw [val_absPow] at n3
    simp only [neg_div] at b1 b2
    field_simp
    linear_combination (exp := 1) ((nabs k (GeneralLinearGroup.det p₂) : ℂ) ^ (-((n : ℂ) / 2)) *
      (nabs k (GeneralLinearGroup.det p₂) : ℂ) ^ ((n : ℂ) / 2)) * b1 + b2
  refine irr_gen hB n t hμ hu τ hτ l hs hτl (fun x h0 => ?_) N hR hN
  refine (Submodule.span_le (p := twRel (τ.comp (MonoidHom.inl _ _)) 1)).2 ?_ (hk x h0)
  rintro _ ⟨γ, v, rfl⟩
  have e1 : τ (γ, 1) v = (ξ γ : ℂ) • rightRep (Fin n) (Fin n) n γ v := by
    change (fibChar (Fin n) (Fin n) (Fin t) μ (γ, 1) : ℂ) • fibBase (Fin n) (Fin n) n (γ, 1) v = _
    congr 1
    simp [fibChar, ξ]
  have h : rightRep (Fin n) (Fin n) n γ v - ((ξ⁻¹ γ : ℂˣ) : ℂ) • v =
      ((ξ⁻¹ γ : ℂˣ) : ℂ) • (τ (γ, 1) v - (((1 : GL (Fin n) k →* ℂˣ) γ : ℂˣ) : ℂ) • v) := by
    rw [e1, MonoidHom.one_apply, Units.val_one, one_smul, smul_sub, smul_smul, MonoidHom.inv_apply, Units.inv_mul, one_smul]
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨γ, v, rfl⟩)

end PositivityTheory.KCo
