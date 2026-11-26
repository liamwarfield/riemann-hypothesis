module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RationalCoordinates.RationalCoordinateCountability.ContinuousFrameUM
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ContinuousCA

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RationalCoordinates.RationalCoordinateCountability.CountableProdSub
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RationalCoordinates.RationalCoordinateCountability.VaddInvBotProd
noncomputable section

open scoped ENNReal Pointwise
open MeasureTheory

namespace PositivityTheory.SiegelWeilFormula.Act.C5.CoordK

theorem fd_bot_univ {X : Type} [AddGroup X] [MeasurableSpace X] (μ : Measure X) :
    IsAddFundamentalDomain (⊥ : AddSubgroup X) Set.univ μ := by
  refine ⟨nullMeasurableSet_univ, Filter.Eventually.of_forall fun x => ⟨0, Set.mem_univ _⟩, ?_⟩
  intro g h hgh
  exact absurd (Subtype.ext ((AddSubgroup.mem_bot.1 g.2).trans (AddSubgroup.mem_bot.1 h.2).symm)) hgh

theorem fd_prod' {X Y : Type} [AddCommGroup X] [AddCommGroup Y] [MeasurableSpace X] [MeasurableSpace Y]
    {Γ : AddSubgroup X} {Δ : AddSubgroup Y}
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν] {s : Set X} {t : Set Y}
    (hs : IsAddFundamentalDomain Γ s μ) (ht : IsAddFundamentalDomain Δ t ν) :
    IsAddFundamentalDomain (Γ.prod Δ) (s ×ˢ t) (μ.prod ν) := by
  refine ⟨hs.nullMeasurableSet.prod ht.nullMeasurableSet, ?_, ?_⟩
  · have h1 := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae hs.ae_covers
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae ht.ae_covers
    filter_upwards [h1, h2] with p hp1 hp2
    obtain ⟨⟨g, hg⟩, hgs⟩ := hp1
    obtain ⟨⟨d, hd⟩, hdt⟩ := hp2
    exact ⟨⟨(g, d), AddSubgroup.mem_prod.2 ⟨hg, hd⟩⟩, hgs, hdt⟩
  · intro g h hgh
    have key : (g : X × Y).1 ≠ (h : X × Y).1 ∨ (g : X × Y).2 ≠ (h : X × Y).2 := by
      by_contra hc
      push_neg at hc
      exact hgh (Subtype.ext (Prod.ext hc.1 hc.2))
    rcases key with h1 | h2
    · have hg : (g : X × Y).1 ∈ Γ := (AddSubgroup.mem_prod.1 g.2).1
      have hh : (h : X × Y).1 ∈ Γ := (AddSubgroup.mem_prod.1 h.2).1
      have hd : AEDisjoint μ ((⟨_, hg⟩ : Γ) +ᵥ s) ((⟨_, hh⟩ : Γ) +ᵥ s) :=
        hs.aedisjoint (fun e => h1 (congrArg Subtype.val e))
      refine (hd.preimage Measure.quasiMeasurePreserving_fst).mono ?_ ?_
      · rintro _ ⟨y, ⟨hy, -⟩, rfl⟩
        exact Set.vadd_mem_vadd_set hy
      · rintro _ ⟨y, ⟨hy, -⟩, rfl⟩
        exact Set.vadd_mem_vadd_set hy
    · have hg : (g : X × Y).2 ∈ Δ := (AddSubgroup.mem_prod.1 g.2).2
      have hh : (h : X × Y).2 ∈ Δ := (AddSubgroup.mem_prod.1 h.2).2
      have hd : AEDisjoint ν ((⟨_, hg⟩ : Δ) +ᵥ t) ((⟨_, hh⟩ : Δ) +ᵥ t) :=
        ht.aedisjoint (fun e => h2 (congrArg Subtype.val e))
      refine (hd.preimage Measure.quasiMeasurePreserving_snd).mono ?_ ?_
      · rintro _ ⟨y, ⟨-, hy⟩, rfl⟩
        exact Set.vadd_mem_vadd_set hy
      · rintro _ ⟨y, ⟨-, hy⟩, rfl⟩
        exact Set.vadd_mem_vadd_set hy

theorem vaddInv_bot_prod {X Y : Type} [AddCommGroup X] [AddCommGroup Y] [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableAdd Y] (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] (Δ : AddSubgroup Y)
    (hν : ∀ y ∈ Δ, MeasurePreserving (fun z => y + z) ν ν) :
    VAddInvariantMeasure ((⊥ : AddSubgroup X).prod Δ) (X × Y) (μ.prod ν) := by
  refine ⟨fun c u hu => ?_⟩
  obtain ⟨⟨a, d⟩, hc⟩ := c
  have ha : a = 0 := AddSubgroup.mem_bot.1 (AddSubgroup.mem_prod.1 hc).1
  have hd : d ∈ Δ := (AddSubgroup.mem_prod.1 hc).2
  subst ha
  have hmp : MeasurePreserving (Prod.map id (fun z => d + z)) (μ.prod ν) (μ.prod ν) :=
    (MeasurePreserving.id μ).prod (hν d hd)
  have hfun : (fun x : X × Y => (⟨(0, d), hc⟩ : ((⊥ : AddSubgroup X).prod Δ)) +ᵥ x) =
      Prod.map id (fun z => d + z) := by
    funext x
    refine Prod.ext ?_ rfl
    show (0 : X) + x.1 = x.1
    exact zero_add _
  rw [hfun]
  exact hmp.measure_preimage hu.nullMeasurableSet

theorem mp_of_vaddInv {Y : Type} [AddCommGroup Y] [MeasurableSpace Y] [MeasurableAdd Y] (ν : Measure Y) (Δ : AddSubgroup Y)
    [VAddInvariantMeasure Δ Y ν] (y : Y) (hy : y ∈ Δ) : MeasurePreserving (fun z => y + z) ν ν := by
  refine ⟨measurable_const_add y, ?_⟩
  ext u hu
  rw [Measure.map_apply (measurable_const_add y) hu]
  exact VAddInvariantMeasure.measure_preimage_vadd (⟨y, hy⟩ : Δ) hu

end PositivityTheory.SiegelWeilFormula.Act.C5.CoordK

end
end

set_option linter.unusedSectionVars false

noncomputable section

open scoped ENNReal Pointwise
open MeasureTheory

namespace PositivityTheory.SiegelWeilFormula.Act.C5.CoordK

instance countable_prodSub {X Y : Type} [AddGroup X] [AddGroup Y] (Γ : AddSubgroup X) (Δ : AddSubgroup Y) [Countable Γ]
    [Countable Δ] : Countable ((Γ.prod Δ : AddSubgroup (X × Y))) := by
  refine Function.Injective.countable (f := fun g : (Γ.prod Δ : AddSubgroup (X × Y)) =>
    ((⟨(g : X × Y).1, (AddSubgroup.mem_prod.1 g.2).1⟩ : Γ), (⟨(g : X × Y).2, (AddSubgroup.mem_prod.1 g.2).2⟩ : Δ))) ?_
  intro g g' h
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
  exact Subtype.ext (Prod.ext h.1 h.2)

instance mcv_sub {X : Type} [AddGroup X] [MeasurableSpace X] [MeasurableAdd X] (Γ : AddSubgroup X) :
    MeasurableConstVAdd Γ X := ⟨fun g => measurable_const_add (g : X)⟩

instance mAdd_prod {X Y : Type} [Add X] [Add Y] [MeasurableSpace X] [MeasurableSpace Y] [MeasurableAdd X] [MeasurableAdd Y] :
    MeasurableAdd (X × Y) where
  measurable_const_add c := ((measurable_const_add c.1).comp measurable_fst).prodMk ((measurable_const_add c.2).comp measurable_snd)
  measurable_add_const c := ((measurable_add_const c.1).comp measurable_fst).prodMk ((measurable_add_const c.2).comp measurable_snd)

instance countable_botSub {X : Type} [AddGroup X] : Countable ((⊥ : AddSubgroup X)) := by
  infer_instance

section Chain

variable {U N Z N' : Type} [AddCommGroup U] [AddCommGroup N] [AddCommGroup Z] [AddCommGroup N']
  [MeasurableSpace U] [MeasurableSpace N] [MeasurableSpace Z] [MeasurableSpace N']
  [MeasurableAdd₂ U] [MeasurableAdd₂ N] [MeasurableAdd₂ Z] [MeasurableAdd₂ N'] [MeasurableNeg Z] [MeasurableSub₂ Z]

def phi (P : N ≃ᵐ (Z × N')) : (U × N) ≃ᵐ (N' × (U × Z)) :=
  ((MeasurableEquiv.refl U).prodCongr P).trans ((MeasurableEquiv.prodAssoc.symm).trans MeasurableEquiv.prodComm)

theorem phi_apply (P : N ≃ᵐ (Z × N')) (p : U × N) : phi P p = ((P p.2).2, (p.1, (P p.2).1)) := rfl

theorem phi_symm_apply (P : N ≃ᵐ (Z × N')) (w : N' × (U × Z)) : (phi P).symm w = (w.2.1, P.symm (w.2.2, w.1)) := rfl

def sh (τ : U × N' → Z) (hτ : Measurable τ) : (N' × (U × Z)) ≃ᵐ (N' × (U × Z)) where
  toFun w := (w.1, (w.2.1, w.2.2 + τ (w.2.1, w.1)))
  invFun w := (w.1, (w.2.1, w.2.2 - τ (w.2.1, w.1)))
  left_inv w := by simp
  right_inv w := by simp
  measurable_toFun := measurable_fst.prodMk (measurable_snd.fst.prodMk
    (measurable_snd.snd.add (hτ.comp (measurable_snd.fst.prodMk measurable_fst))))
  measurable_invFun := measurable_fst.prodMk (measurable_snd.fst.prodMk
    (measurable_snd.snd.sub (hτ.comp (measurable_snd.fst.prodMk measurable_fst))))

theorem sh_apply {τ : U × N' → Z} (hτ : Measurable τ) (w : N' × (U × Z)) :
    sh τ hτ w = (w.1, (w.2.1, w.2.2 + τ (w.2.1, w.1))) := rfl

theorem sh_symm_apply {τ : U × N' → Z} (hτ : Measurable τ) (w : N' × (U × Z)) :
    (sh τ hτ).symm w = (w.1, (w.2.1, w.2.2 - τ (w.2.1, w.1))) := rfl

theorem sh_mp {τ : U × N' → Z} (hτ : Measurable τ) (l : Measure N') (νu : Measure U) (μZ : Measure Z) [SFinite l]
    [SFinite νu] [SFinite μZ] [μZ.IsAddRightInvariant] :
    MeasurePreserving (sh τ hτ) (l.prod (νu.prod μZ)) (l.prod (νu.prod μZ)) := by
  have h1 := (measurePreserving_prodAssoc l νu μZ).symm
  have h2 := shear_mp' (l.prod νu) μZ (fun p : N' × U => τ (p.2, p.1)) (hτ.comp (measurable_snd.prodMk measurable_fst))
  have h3 := measurePreserving_prodAssoc l νu μZ
  have e : (sh τ hτ : N' × (U × Z) → N' × (U × Z)) =
      (MeasurableEquiv.prodAssoc) ∘ (fun p : (N' × U) × Z => (p.1, p.2 + τ (p.1.2, p.1.1))) ∘
        (MeasurableEquiv.prodAssoc (α := N') (β := U) (γ := Z)).symm := by
    funext w; rfl
  rw [e]
  exact h3.comp (h2.comp h1)

end Chain

section Main

variable {U N Z N' : Type} [AddCommGroup U] [AddCommGroup N] [AddCommGroup Z] [AddCommGroup N']
  [MeasurableSpace U] [MeasurableSpace N] [MeasurableSpace Z] [MeasurableSpace N']
  [MeasurableAdd₂ U] [MeasurableAdd₂ N] [MeasurableAdd₂ Z] [MeasurableAdd₂ N'] [MeasurableNeg Z] [MeasurableSub₂ Z]
  {νu : Measure U} [SFinite νu] {lam : Measure N} [SFinite lam] [lam.IsAddLeftInvariant]
  {μZ : Measure Z} [SFinite μZ] [μZ.IsAddLeftInvariant] [μZ.IsAddRightInvariant] {lam' : Measure N'} [SFinite lam']
  {ΓN : AddSubgroup N} {ΓZ : AddSubgroup Z} {ΓN' : AddSubgroup N'} [Countable ΓN] [Countable ΓZ] [Countable ΓN']
  {P : N ≃ᵐ (Z × N')} {c : ℝ≥0∞} {𝓖 : Set N} {𝓩 : Set Z} {𝓖' : Set N'} {τ : U × N' → Z}

theorem phi_add (hPadd : ∀ a b, P (a + b) = P a + P b) (p q : U × N) :
    phi (U := U) P (p + q) = phi P p + phi P q := by
  show ((P (p.2 + q.2)).2, (p.1 + q.1, (P (p.2 + q.2)).1)) = _
  rw [hPadd]
  rfl

theorem phi_map (hPc : lam.map P = c • (μZ.prod lam')) :
    (νu.prod lam).map (phi P) = c • (lam'.prod (νu.prod μZ)) := by
  have hg : MeasurePreserving P lam (c • (μZ.prod lam')) := ⟨P.measurable, hPc⟩
  have h1 := (MeasurePreserving.id νu).prod hg
  rw [Measure.prod_smul_right] at h1
  have h2 := (measurePreserving_prodAssoc νu μZ lam').symm
  have h3 := Measure.measurePreserving_swap (μ := νu.prod μZ) (ν := lam')
  have h23 := h3.comp h2
  calc (νu.prod lam).map (phi P)
      = ((νu.prod lam).map (Prod.map id P)).map (Prod.swap ∘ (MeasurableEquiv.prodAssoc (α := U) (β := Z) (γ := N')).symm) := by
        rw [Measure.map_map h23.measurable h1.measurable]; rfl
    _ = (c • (νu.prod (μZ.prod lam'))).map (Prod.swap ∘ (MeasurableEquiv.prodAssoc (α := U) (β := Z) (γ := N')).symm) := by
        rw [h1.map_eq]
    _ = c • (lam'.prod (νu.prod μZ)) := by rw [Measure.map_smul c h23.measurable.aemeasurable, h23.map_eq]

theorem chainC (hPc : lam.map P = c • (μZ.prod lam')) (hPadd : ∀ a b, P (a + b) = P a + P b)
    (hΓ : ∀ β, β ∈ ΓN ↔ (P β).1 ∈ ΓZ ∧ (P β).2 ∈ ΓN')
    (h𝓖 : IsAddFundamentalDomain ΓN 𝓖 lam) (h𝓩 : IsAddFundamentalDomain ΓZ 𝓩 μZ)
    (h𝓖' : IsAddFundamentalDomain ΓN' 𝓖' lam') (hτ : Measurable τ) (f : U × N → ℂ) (H : N' × (U × Z) → ℂ)
    (hf : ∀ γ ∈ ΓN, ∀ u β, f (u, γ + β) = f (u, β))
    (hH : ∀ g ∈ ΓZ, ∀ w : N' × (U × Z), H (w.1, (w.2.1, g + w.2.2)) = H w)
    (hfH : ∀ u β, f (u, β) = H ((P β).2, (u, (P β).1 + τ (u, (P β).2)))) :
    ∫ p, f p ∂(νu.prod (lam.restrict 𝓖)) =
      c.toReal • ∫ q, H q ∂((lam'.restrict 𝓖').prod (νu.prod (μZ.restrict 𝓩))) := by
  set Φ := phi (U := U) P
  set S := sh τ hτ
  set m := lam'.prod (νu.prod μZ)
  set m' := (lam'.restrict 𝓖').prod (νu.prod μZ)
  set S3 : Set (N' × (U × Z)) := 𝓖' ×ˢ (Set.univ ×ˢ 𝓩)
  set S4 : Set (N' × (U × Z)) := Set.univ ×ˢ (Set.univ ×ˢ 𝓩)

  set Γ₀ : AddSubgroup (U × N) := (⊥ : AddSubgroup U).prod ΓN
  set Γt : AddSubgroup (N' × (U × Z)) := ΓN'.prod ((⊥ : AddSubgroup U).prod ΓZ)
  set Γ₂ : AddSubgroup (N' × (U × Z)) := (⊥ : AddSubgroup N').prod ((⊥ : AddSubgroup U).prod ΓZ)
  have : VAddInvariantMeasure Γ₀ (U × N) (νu.prod lam) :=
    vaddInv_bot_prod νu lam ΓN (fun y _ => measurePreserving_add_left lam y)
  have : VAddInvariantMeasure ((⊥ : AddSubgroup U).prod ΓZ) (U × Z) (νu.prod μZ) :=
    vaddInv_bot_prod νu μZ ΓZ (fun y _ => measurePreserving_add_left μZ y)
  have : VAddInvariantMeasure Γ₂ (N' × (U × Z)) m' :=
    vaddInv_bot_prod (lam'.restrict 𝓖') (νu.prod μZ) _ (fun y hy => mp_of_vaddInv _ _ y hy)

  have hT0 : IsAddFundamentalDomain Γ₀ (Set.univ ×ˢ 𝓖) (νu.prod lam) := fd_prod' (fd_bot_univ νu) h𝓖
  have hS3 : IsAddFundamentalDomain Γt S3 m := fd_prod' h𝓖' (fd_prod' (fd_bot_univ νu) h𝓩)
  have hmemt : ∀ g : Γt, (Φ.symm (g : N' × (U × Z))) ∈ Γ₀ := by
    intro g
    have hg := AddSubgroup.mem_prod.1 g.2
    have hg2 := AddSubgroup.mem_prod.1 hg.2
    rw [phi_symm_apply]
    refine AddSubgroup.mem_prod.2 ⟨hg2.1, (hΓ _).2 ?_⟩
    rw [MeasurableEquiv.apply_symm_apply]
    exact ⟨hg2.2, hg.1⟩
  have hT1 : IsAddFundamentalDomain Γ₀ (Φ ⁻¹' S3) (νu.prod lam) := by
    refine hS3.preimage_of_equiv (f := Φ) ⟨Φ.measurable.aemeasurable, ?_⟩ (e := fun g => ⟨Φ.symm g, hmemt g⟩) ?_ ?_
    · rw [phi_map hPc]; exact Measure.smul_absolutelyContinuous
    · refine ⟨fun g g' h => Subtype.ext (Φ.symm.injective (congrArg Subtype.val h)), fun g => ?_⟩
      refine ⟨⟨Φ g, ?_⟩, Subtype.ext (Φ.symm_apply_apply _)⟩
      have hg := AddSubgroup.mem_prod.1 g.2
      rw [phi_apply]
      have hP := (hΓ _).1 hg.2
      exact AddSubgroup.mem_prod.2 ⟨hP.2, AddSubgroup.mem_prod.2 ⟨hg.1, hP.1⟩⟩
    · intro g p
      show Φ (Φ.symm g + p) = g + Φ p
      rw [phi_add hPadd, MeasurableEquiv.apply_symm_apply]
  have hS4 : IsAddFundamentalDomain Γ₂ S4 m' := fd_prod' (fd_bot_univ _) (fd_prod' (fd_bot_univ νu) h𝓩)
  have hSmp : MeasurePreserving S m' m' := sh_mp hτ _ _ _
  have hS5 : IsAddFundamentalDomain Γ₂ (S.symm ⁻¹' S4) m' := by
    refine hS4.preimage_of_equiv (f := S.symm) hSmp.symm.quasiMeasurePreserving (e := id) Function.bijective_id ?_
    intro g w
    have hg := AddSubgroup.mem_prod.1 g.2
    have hg2 := AddSubgroup.mem_prod.1 hg.2
    show S.symm ((g : N' × (U × Z)) + w) = (g : N' × (U × Z)) + S.symm w
    rw [sh_symm_apply, sh_symm_apply]
    rw [AddSubgroup.mem_bot] at hg2 hg
    ext
    · rfl
    · rfl
    · simp only [Prod.snd_add, Prod.fst_add, hg.1, hg2.1, zero_add]; abel

  have eS3 : m.restrict S3 = (lam'.restrict 𝓖').prod (νu.prod (μZ.restrict 𝓩)) := by
    simp only [m, S3, ← Measure.prod_restrict, Measure.restrict_univ]
  have eS4 : m'.restrict S4 = (lam'.restrict 𝓖').prod (νu.prod (μZ.restrict 𝓩)) := by
    simp only [m', S4, ← Measure.prod_restrict, Measure.restrict_univ]
  have hpt : ∀ p, f p = H (S (Φ p)) := by
    rintro ⟨u, β⟩
    rw [hfH, phi_apply, sh_apply]
  calc ∫ p, f p ∂(νu.prod (lam.restrict 𝓖))
      = ∫ p in Set.univ ×ˢ 𝓖, f p ∂(νu.prod lam) := by rw [← Measure.prod_restrict, Measure.restrict_univ]
    _ = ∫ p in Φ ⁻¹' S3, f p ∂(νu.prod lam) := by
        refine hT0.setIntegral_eq hT1 fun g p => ?_
        have hg := AddSubgroup.mem_prod.1 g.2
        rw [AddSubgroup.mem_bot] at hg
        obtain ⟨u, β⟩ := p
        show f ((g : U × N) + (u, β)) = f (u, β)
        have e : (g : U × N) + (u, β) = (u, (g : U × N).2 + β) := by ext <;> simp [hg.1]
        rw [e, hf _ hg.2]
    _ = ∫ p in Φ ⁻¹' S3, H (S (Φ p)) ∂(νu.prod lam) := by simp only [← hpt]
    _ = ∫ w in S3, H (S w) ∂((νu.prod lam).map Φ) := (Φ.measurableEmbedding.setIntegral_map (μ := νu.prod lam) (fun w => H (S w)) S3).symm
    _ = c.toReal • ∫ w in S3, H (S w) ∂m := by rw [phi_map hPc, Measure.restrict_smul, integral_smul_measure]
    _ = c.toReal • ∫ w in S4, H (S w) ∂m' := by rw [eS3, ← eS4]
    _ = c.toReal • ∫ w in S.symm ⁻¹' S4, H w ∂m' := by
        congr 1
        have e : S ⁻¹' (S.symm ⁻¹' S4) = S4 := by ext w; simp
        have h := hSmp.setIntegral_preimage_emb S.measurableEmbedding H (S.symm ⁻¹' S4)
        rw [e] at h
        exact h
    _ = c.toReal • ∫ w in S4, H w ∂m' := by
        congr 1
        refine hS5.setIntegral_eq hS4 fun g w => ?_
        have hg := AddSubgroup.mem_prod.1 g.2
        have hg2 := AddSubgroup.mem_prod.1 hg.2
        rw [AddSubgroup.mem_bot] at hg hg2
        show H ((g : N' × (U × Z)) + w) = H w
        have e : (g : N' × (U × Z)) + w = (w.1, (w.2.1, (g : N' × (U × Z)).2.2 + w.2.2)) := by
          ext <;> simp [hg.1, hg2.1]
        rw [e, hH _ hg2.2]
    _ = c.toReal • ∫ q, H q ∂((lam'.restrict 𝓖').prod (νu.prod (μZ.restrict 𝓩))) := by rw [eS4]

theorem chainE (hPc : lam.map P = c • (μZ.prod lam')) (hPadd : ∀ a b, P (a + b) = P a + P b)
    (hΓ : ∀ β, β ∈ ΓN ↔ (P β).1 ∈ ΓZ ∧ (P β).2 ∈ ΓN')
    (h𝓖 : IsAddFundamentalDomain ΓN 𝓖 lam) (h𝓩 : IsAddFundamentalDomain ΓZ 𝓩 μZ)
    (h𝓖' : IsAddFundamentalDomain ΓN' 𝓖' lam') (hτ : Measurable τ) (f : U × N → ℝ≥0∞) (H : N' × (U × Z) → ℝ≥0∞)
    (hf : ∀ γ ∈ ΓN, ∀ u β, f (u, γ + β) = f (u, β))
    (hH : ∀ g ∈ ΓZ, ∀ w : N' × (U × Z), H (w.1, (w.2.1, g + w.2.2)) = H w)
    (hfH : ∀ u β, f (u, β) = H ((P β).2, (u, (P β).1 + τ (u, (P β).2)))) :
    ∫⁻ p, f p ∂(νu.prod (lam.restrict 𝓖)) =
      c * ∫⁻ q, H q ∂((lam'.restrict 𝓖').prod (νu.prod (μZ.restrict 𝓩))) := by
  set Φ := phi (U := U) P
  set S := sh τ hτ
  set m := lam'.prod (νu.prod μZ)
  set m' := (lam'.restrict 𝓖').prod (νu.prod μZ)
  set S3 : Set (N' × (U × Z)) := 𝓖' ×ˢ (Set.univ ×ˢ 𝓩)
  set S4 : Set (N' × (U × Z)) := Set.univ ×ˢ (Set.univ ×ˢ 𝓩)

  set Γ₀ : AddSubgroup (U × N) := (⊥ : AddSubgroup U).prod ΓN
  set Γt : AddSubgroup (N' × (U × Z)) := ΓN'.prod ((⊥ : AddSubgroup U).prod ΓZ)
  set Γ₂ : AddSubgroup (N' × (U × Z)) := (⊥ : AddSubgroup N').prod ((⊥ : AddSubgroup U).prod ΓZ)
  have : VAddInvariantMeasure Γ₀ (U × N) (νu.prod lam) :=
    vaddInv_bot_prod νu lam ΓN (fun y _ => measurePreserving_add_left lam y)
  have : VAddInvariantMeasure ((⊥ : AddSubgroup U).prod ΓZ) (U × Z) (νu.prod μZ) :=
    vaddInv_bot_prod νu μZ ΓZ (fun y _ => measurePreserving_add_left μZ y)
  have : VAddInvariantMeasure Γ₂ (N' × (U × Z)) m' :=
    vaddInv_bot_prod (lam'.restrict 𝓖') (νu.prod μZ) _ (fun y hy => mp_of_vaddInv _ _ y hy)

  have hT0 : IsAddFundamentalDomain Γ₀ (Set.univ ×ˢ 𝓖) (νu.prod lam) := fd_prod' (fd_bot_univ νu) h𝓖
  have hS3 : IsAddFundamentalDomain Γt S3 m := fd_prod' h𝓖' (fd_prod' (fd_bot_univ νu) h𝓩)
  have hmemt : ∀ g : Γt, (Φ.symm (g : N' × (U × Z))) ∈ Γ₀ := by
    intro g
    have hg := AddSubgroup.mem_prod.1 g.2
    have hg2 := AddSubgroup.mem_prod.1 hg.2
    rw [phi_symm_apply]
    refine AddSubgroup.mem_prod.2 ⟨hg2.1, (hΓ _).2 ?_⟩
    rw [MeasurableEquiv.apply_symm_apply]
    exact ⟨hg2.2, hg.1⟩
  have hT1 : IsAddFundamentalDomain Γ₀ (Φ ⁻¹' S3) (νu.prod lam) := by
    refine hS3.preimage_of_equiv (f := Φ) ⟨Φ.measurable.aemeasurable, ?_⟩ (e := fun g => ⟨Φ.symm g, hmemt g⟩) ?_ ?_
    · rw [phi_map hPc]; exact Measure.smul_absolutelyContinuous
    · refine ⟨fun g g' h => Subtype.ext (Φ.symm.injective (congrArg Subtype.val h)), fun g => ?_⟩
      refine ⟨⟨Φ g, ?_⟩, Subtype.ext (Φ.symm_apply_apply _)⟩
      have hg := AddSubgroup.mem_prod.1 g.2
      rw [phi_apply]
      have hP := (hΓ _).1 hg.2
      exact AddSubgroup.mem_prod.2 ⟨hP.2, AddSubgroup.mem_prod.2 ⟨hg.1, hP.1⟩⟩
    · intro g p
      show Φ (Φ.symm g + p) = g + Φ p
      rw [phi_add hPadd, MeasurableEquiv.apply_symm_apply]
  have hS4 : IsAddFundamentalDomain Γ₂ S4 m' := fd_prod' (fd_bot_univ _) (fd_prod' (fd_bot_univ νu) h𝓩)
  have hSmp : MeasurePreserving S m' m' := sh_mp hτ _ _ _
  have hS5 : IsAddFundamentalDomain Γ₂ (S.symm ⁻¹' S4) m' := by
    refine hS4.preimage_of_equiv (f := S.symm) hSmp.symm.quasiMeasurePreserving (e := id) Function.bijective_id ?_
    intro g w
    have hg := AddSubgroup.mem_prod.1 g.2
    have hg2 := AddSubgroup.mem_prod.1 hg.2
    show S.symm ((g : N' × (U × Z)) + w) = (g : N' × (U × Z)) + S.symm w
    rw [sh_symm_apply, sh_symm_apply]
    rw [AddSubgroup.mem_bot] at hg2 hg
    ext
    · rfl
    · rfl
    · simp only [Prod.snd_add, Prod.fst_add, hg.1, hg2.1, zero_add]; abel

  have eS3 : m.restrict S3 = (lam'.restrict 𝓖').prod (νu.prod (μZ.restrict 𝓩)) := by
    simp only [m, S3, ← Measure.prod_restrict, Measure.restrict_univ]
  have eS4 : m'.restrict S4 = (lam'.restrict 𝓖').prod (νu.prod (μZ.restrict 𝓩)) := by
    simp only [m', S4, ← Measure.prod_restrict, Measure.restrict_univ]
  have hpt : ∀ p, f p = H (S (Φ p)) := by
    rintro ⟨u, β⟩
    rw [hfH, phi_apply, sh_apply]
  calc ∫⁻ p, f p ∂(νu.prod (lam.restrict 𝓖))
      = ∫⁻ p in Set.univ ×ˢ 𝓖, f p ∂(νu.prod lam) := by rw [← Measure.prod_restrict, Measure.restrict_univ]
    _ = ∫⁻ p in Φ ⁻¹' S3, f p ∂(νu.prod lam) := by
        refine hT0.setLIntegral_eq hT1 f fun g p => ?_
        have hg := AddSubgroup.mem_prod.1 g.2
        rw [AddSubgroup.mem_bot] at hg
        obtain ⟨u, β⟩ := p
        show f ((g : U × N) + (u, β)) = f (u, β)
        have e : (g : U × N) + (u, β) = (u, (g : U × N).2 + β) := by ext <;> simp [hg.1]
        rw [e, hf _ hg.2]
    _ = ∫⁻ p in Φ ⁻¹' S3, H (S (Φ p)) ∂(νu.prod lam) := by simp only [← hpt]
    _ = ∫⁻ w in S3, H (S w) ∂((νu.prod lam).map Φ) := by
        rw [Φ.measurableEmbedding.restrict_map, Φ.measurableEmbedding.lintegral_map]
    _ = c * ∫⁻ w in S3, H (S w) ∂m := by rw [phi_map hPc, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]
    _ = c * ∫⁻ w in S4, H (S w) ∂m' := by rw [eS3, ← eS4]
    _ = c * ∫⁻ w in S.symm ⁻¹' S4, H w ∂m' := by
        congr 1
        have e : S ⁻¹' (S.symm ⁻¹' S4) = S4 := by ext w; simp
        have h := hSmp.setLIntegral_comp_preimage_emb S.measurableEmbedding H (S.symm ⁻¹' S4)
        rw [e] at h
        exact h
    _ = c * ∫⁻ w in S4, H w ∂m' := by
        congr 1
        refine hS5.setLIntegral_eq hS4 H fun g w => ?_
        have hg := AddSubgroup.mem_prod.1 g.2
        have hg2 := AddSubgroup.mem_prod.1 hg.2
        rw [AddSubgroup.mem_bot] at hg hg2
        show H ((g : N' × (U × Z)) + w) = H w
        have e : (g : N' × (U × Z)) + w = (w.1, (w.2.1, (g : N' × (U × Z)).2.2 + w.2.2)) := by
          ext <;> simp [hg.1, hg2.1]
        rw [e, hH _ hg2.2]
    _ = c * ∫⁻ q, H q ∂((lam'.restrict 𝓖').prod (νu.prod (μZ.restrict 𝓩))) := by rw [eS4]

end Main

end PositivityTheory.SiegelWeilFormula.Act.C5.CoordK

end
end

noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Act.C5.CoordK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : SD σ} {R : RD d} {L : LD d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}

theorem fix_mul {x y : d.G}
    (hx : ∀ k, inFrame d.b x k (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀))
    (hy : ∀ k, inFrame d.b y k (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀))
    (k) : inFrame d.b (x * y) k (Sum.inl L.i₀) =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀) := by
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, Matrix.mul_apply]
  simp only [hy]
  rw [← Matrix.mul_apply, Matrix.mul_one, hx]

theorem perF (h : Hyp L nb uM nb' w₁ cM δ) (Ψ : d.G → ℂ) (hΨ : ∀ r ∈ rat2 σ d.Y, (∀ k, inFrame d.b r k (Sum.inl L.i₀) =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀)) → ∀ g, Ψ (r * g) = Ψ g)
    (T : nF σ d.Y d.b) (x : d.G) (γ : nA σ d.Y d.b) (hγ : γ ∈ nF σ d.Y d.b) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    Ψ (nb (γ + β) * (uM u * x)) * th T (γ + β) = Ψ (nb β * (uM u * x)) * th T β := by
  have e2 : ((γ + β : nA σ d.Y d.b) : Matrix (Fin d.n) (Fin d.n) (AE F E)) = γ.1 + β.1 := rfl
  rw [kunf.nb_add h.nb, mul_assoc, hΨ _ (kunf.nb_rat h.nb hγ) (fix_nb h γ)]
  congr 1
  unfold th
  rw [e2, Matrix.mul_add, Matrix.trace_add, map_add (f := _), neg_add, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv,
    kunf.psi_rat d.ok.good.std T ⟨γ, hγ⟩, inv_one, one_mul]

theorem perFE (h : Hyp L nb uM nb' w₁ cM δ) (Ψ : d.G → ℝ≥0∞) (hΨ : ∀ r ∈ rat2 σ d.Y, (∀ k, inFrame d.b r k (Sum.inl L.i₀) =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀)) → ∀ g, Ψ (r * g) = Ψ g)
    (T : nF σ d.Y d.b) (x : d.G) (γ : nA σ d.Y d.b) (hγ : γ ∈ nF σ d.Y d.b) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    Ψ (nb (γ + β) * (uM u * x)) * ‖th T (γ + β)‖ₑ = Ψ (nb β * (uM u * x)) * ‖th T β‖ₑ := by
  have e2 : ((γ + β : nA σ d.Y d.b) : Matrix (Fin d.n) (Fin d.n) (AE F E)) = γ.1 + β.1 := rfl
  rw [kunf.nb_add h.nb, mul_assoc, hΨ _ (kunf.nb_rat h.nb hγ) (fix_nb h γ)]
  congr 2
  unfold th
  rw [e2, Matrix.mul_add, Matrix.trace_add, map_add (f := _), neg_add, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv,
    kunf.psi_rat d.ok.good.std T ⟨γ, hγ⟩, inv_one, one_mul]

theorem shift_eq (h : Hyp L nb uM nb' w₁ cM δ) (r b u : Fin L.n → AE F E) (s a : AF F) :
    sM R L (r + b) * cM (u, s + a) = (sM R L r * cM (0, s)) * (sM R L b * cM (u, a)) := by
  have e1 : cM (u, s + a) = cM (0, s) * cM (u, a) := by
    rw [cM_split h, centre_matrix_add h, cM_split h u a, ← mul_assoc, cM_comm h, mul_assoc]
  rw [sM_add, e1]
  simp only [mul_assoc]
  rw [← mul_assoc (sM R L b) (cM (0, s)), siegel_centre_commute h, mul_assoc]

theorem rr_rat (h : Hyp L nb uM nb' w₁ cM δ) {r : Fin L.n → AE F E} (hr : r ∈ L.ratV) {s : AF F}
    (hs : s ∈ (algebraMap F (AF F)).range) : sM R L r * cM (0, s) ∈ rat2 σ d.Y :=
  mul_mem (sM_rat hr) (cM_rat h (c := (0, s)) (zero_mem _) hs)

theorem rr_fix (h : Hyp L nb uM nb' w₁ cM δ) (r : Fin L.n → AE F E) (s : AF F) (k) :
    inFrame d.b (sM R L r * cM (0, s)) k (Sum.inl L.i₀) =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀) :=
  fix_mul (L := L) (fix_sM r) (fix_cM h (0, s)) k

theorem pt_eq (h : Hyp L nb uM nb' w₁ cM δ) (x : d.G) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    nb β * (uM u * x) = sM R L (pb L β + (tau L uM nb' δ (u, C4.prj L β)).1) *
      (cM (u, pa L δ β + (tau L uM nb' δ (u, C4.prj L β)).2) * (L.j (nb' (C4.prj L β)) * x)) := by
  calc nb β * (uM u * x) = (L.j (nb' (C4.prj L β)) * (sM R L (pb L β) * cM (u, pa L δ β))) * x := by
        rw [nb_split (R := R) h β]
        simp only [mul_assoc]
        rw [← mul_assoc (cM (0, pa L δ β)) (uM u), ← cM_comm h, ← cM_split h]
    _ = _ := by rw [move h]; simp only [mul_assoc]

instance countable_ratV (L : LD d) : Countable L.ratV := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  have h : ((L.ratV : AddSubgroup (Fin L.n → AE F E)) : Set (Fin L.n → AE F E)).Countable := by
    refine (Set.countable_range (GlobalTheory.ThK.incV F : (Fin L.n → E) → _)).mono fun u hu => ?_
    obtain ⟨v, rfl⟩ := C1.ratV_inc hu
    exact ⟨v, rfl⟩
  exact h.to_subtype

theorem coordsC_ck (h : Hyp L nb uM nb' w₁ cM δ) {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {ν : Measure (Fin L.n → AE F E)} {𝓤 : Set (Fin L.n → AE F E)}
    (hU : L.UData uM ν 𝓤) {lam' : Measure (nA σ L.Y L.b)} {𝓖' : Set (nA σ L.Y L.b)}
    (hc' : CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖') {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b} (hT : L.IsSub T T')
    {𝓐 : Set (AF F)} (h𝓐 : IsAddFundamentalDomain (fA F) 𝓐 (lamA F))
    {P : (nA σ d.Y d.b) ≃ₜ+ (((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b)} (hP : ∀ β, P β = ((pb L β, pa L δ β), C4.prj L β))
    {c : ℝ≥0∞} (hPc : lam.map P = c • ((ν.prod (lamA F)).prod lam'))
    (Ψ : d.G → ℂ) (hΨ : ∀ r ∈ rat2 σ d.Y, (∀ k, inFrame d.b r k (Sum.inl L.i₀) =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀)) → ∀ g, Ψ (r * g) = Ψ g) (x : d.G) :
    ∫ p, Ψ (nb p.2 * (uM p.1 * x)) * th T p.2 ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖)) =
      c.toReal • ∫ p, Ψ (sM R L p.2.2.1 * (cM (p.2.1, p.2.2.2) * (L.j (nb' p.1) * x))) * th' T' p.1
        ∂((lam'.restrict 𝓖').prod ((ν.restrict 𝓤).prod ((ν.restrict 𝓤).prod ((lamA F).restrict 𝓐)))) := by
  haveI : Fact (IsFrame2 σ d.Y d.b) := ⟨d.ok.frame⟩
  haveI : Fact (IsFrame2 σ L.Y L.b) := ⟨L.ok.frame⟩
  haveI := hc.2.1
  haveI := hc'.2.1
  haveI := hU.2.1
  obtain ⟨-, -, hiff⟩ := pEquiv h
  let PM : (nA σ d.Y d.b) ≃ᵐ (((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b) := P.toHomeomorph.toMeasurableEquiv
  have hPM : ∀ β, PM β = ((pb L β, pa L δ β), C4.prj L β) := hP
  have hPc' : lam.map PM = c • ((ν.prod (lamA F)).prod lam') := hPc
  have hZ : IsAddFundamentalDomain (L.ratV.prod (fA F)) (𝓤 ×ˢ 𝓐) (ν.prod (lamA F)) := fd_prod' hU.2.2.1 h𝓐
  have key := chainC (νu := ν.restrict 𝓤) (ΓN := nF σ d.Y d.b) (ΓZ := L.ratV.prod (fA F)) (ΓN' := nF σ L.Y L.b)
    hPc' (fun a b => map_add P a b) (fun β => by rw [hPM, hiff, AddSubgroup.mem_prod]) hc.2.2.1 hZ hc'.2.2.1
    (continuous_tau h).measurable
    (fun p => Ψ (nb p.2 * (uM p.1 * x)) * th T p.2)
    (fun q => Ψ (sM R L q.2.2.1 * (cM (q.2.1, q.2.2.2) * (L.j (nb' q.1) * x))) * th' T' q.1)
    (fun γ hγ u β => perF h Ψ hΨ T x γ hγ u β)
    (fun g hg w => by
      obtain ⟨hg1, hg2⟩ := AddSubgroup.mem_prod.1 hg
      obtain ⟨β'', u, b, a⟩ := w
      show Ψ (sM R L (g.1 + b) * (cM (u, g.2 + a) * _)) * _ = Ψ (sM R L b * (cM (u, a) * _)) * _
      rw [← mul_assoc, shift_eq h, mul_assoc (sM R L g.1 * cM (0, g.2)), hΨ _ (rr_rat h hg1 hg2) (rr_fix h g.1 g.2)]
      simp only [mul_assoc])
    (fun u β => by
      rw [hPM]
      show Ψ (nb β * (uM u * x)) * th T β = Ψ (sM R L (pb L β + (tau L uM nb' δ (u, C4.prj L β)).1) *
        (cM (u, pa L δ β + (tau L uM nb' δ (u, C4.prj L β)).2) * (L.j (nb' (C4.prj L β)) * x))) * th' T' (C4.prj L β)
      rw [pt_eq (R := R) h x u β]
      congr 1
      unfold th th'
      rw [C4.tr_sub L hT β])
  rw [key, ← Measure.prod_restrict]

theorem coordsE_ck (h : Hyp L nb uM nb' w₁ cM δ) {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {ν : Measure (Fin L.n → AE F E)} {𝓤 : Set (Fin L.n → AE F E)}
    (hU : L.UData uM ν 𝓤) {lam' : Measure (nA σ L.Y L.b)} {𝓖' : Set (nA σ L.Y L.b)}
    (hc' : CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖') {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b} (hT : L.IsSub T T')
    {𝓐 : Set (AF F)} (h𝓐 : IsAddFundamentalDomain (fA F) 𝓐 (lamA F))
    {P : (nA σ d.Y d.b) ≃ₜ+ (((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b)} (hP : ∀ β, P β = ((pb L β, pa L δ β), C4.prj L β))
    {c : ℝ≥0∞} (hPc : lam.map P = c • ((ν.prod (lamA F)).prod lam'))
    (Ψ : d.G → ℝ≥0∞) (hΨm : Measurable Ψ) (hΨ : ∀ r ∈ rat2 σ d.Y, (∀ k, inFrame d.b r k (Sum.inl L.i₀) =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀)) → ∀ g, Ψ (r * g) = Ψ g) (x : d.G) :
    ∫⁻ p, Ψ (nb p.2 * (uM p.1 * x)) * ‖th T p.2‖ₑ ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖)) =
      c * ∫⁻ p, Ψ (sM R L p.2.2.1 * (cM (p.2.1, p.2.2.2) * (L.j (nb' p.1) * x))) * ‖th' T' p.1‖ₑ
        ∂((lam'.restrict 𝓖').prod ((ν.restrict 𝓤).prod ((ν.restrict 𝓤).prod ((lamA F).restrict 𝓐)))) := by
  haveI : Fact (IsFrame2 σ d.Y d.b) := ⟨d.ok.frame⟩
  haveI : Fact (IsFrame2 σ L.Y L.b) := ⟨L.ok.frame⟩
  haveI := hc.2.1
  haveI := hc'.2.1
  haveI := hU.2.1
  obtain ⟨-, -, hiff⟩ := pEquiv h
  let PM : (nA σ d.Y d.b) ≃ᵐ (((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b) := P.toHomeomorph.toMeasurableEquiv
  have hPM : ∀ β, PM β = ((pb L β, pa L δ β), C4.prj L β) := hP
  have hPc' : lam.map PM = c • ((ν.prod (lamA F)).prod lam') := hPc
  have hZ : IsAddFundamentalDomain (L.ratV.prod (fA F)) (𝓤 ×ˢ 𝓐) (ν.prod (lamA F)) := fd_prod' hU.2.2.1 h𝓐
  have key := chainE (νu := ν.restrict 𝓤) (ΓN := nF σ d.Y d.b) (ΓZ := L.ratV.prod (fA F)) (ΓN' := nF σ L.Y L.b)
    hPc' (fun a b => map_add P a b) (fun β => by rw [hPM, hiff, AddSubgroup.mem_prod]) hc.2.2.1 hZ hc'.2.2.1
    (continuous_tau h).measurable
    (fun p => Ψ (nb p.2 * (uM p.1 * x)) * ‖th T p.2‖ₑ)
    (fun q => Ψ (sM R L q.2.2.1 * (cM (q.2.1, q.2.2.2) * (L.j (nb' q.1) * x))) * ‖th' T' q.1‖ₑ)
    (fun γ hγ u β => perFE h Ψ hΨ T x γ hγ u β)
    (fun g hg w => by
      obtain ⟨hg1, hg2⟩ := AddSubgroup.mem_prod.1 hg
      obtain ⟨β'', u, b, a⟩ := w
      show Ψ (sM R L (g.1 + b) * (cM (u, g.2 + a) * _)) * _ = Ψ (sM R L b * (cM (u, a) * _)) * _
      rw [← mul_assoc, shift_eq h, mul_assoc (sM R L g.1 * cM (0, g.2)), hΨ _ (rr_rat h hg1 hg2) (rr_fix h g.1 g.2)]
      simp only [mul_assoc])
    (fun u β => by
      rw [hPM]
      show Ψ (nb β * (uM u * x)) * ‖th T β‖ₑ = Ψ (sM R L (pb L β + (tau L uM nb' δ (u, C4.prj L β)).1) *
        (cM (u, pa L δ β + (tau L uM nb' δ (u, C4.prj L β)).2) * (L.j (nb' (C4.prj L β)) * x))) * ‖th' T' (C4.prj L β)‖ₑ
      rw [pt_eq (R := R) h x u β]
      congr 2
      unfold th th'
      rw [C4.tr_sub L hT β])
  rw [key, ← Measure.prod_restrict]

end PositivityTheory.SiegelWeilFormula.Act.C5.CoordK

end
