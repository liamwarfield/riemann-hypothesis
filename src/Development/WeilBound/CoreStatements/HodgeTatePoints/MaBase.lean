module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsKrullAkizuki
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import ReciprocityTheory.DualLattices.KilledGen
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CharacterIdealPrincipalEigen

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.MaBase
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Ma

theorem reg_open : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) (a : Ω), a ∈ regAt ξ p → ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q :=
  fun _ _ _ ξ p a ha => exists_open_mem_regAt ξ p a ha

theorem reg_local : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), (∀ p : Cpt ξ, IsLocalRing (regAt ξ p)) ∧ (∀ p q : Cpt ξ, q.1 ⤳ p.1 → regAt ξ p ≤ regAt ξ q) ∧ (IsCptGen ξ → ∀ (p : Cpt ξ) (a : Ω), ∃ u ∈ regAt ξ p, ∃ v ∈ regAt ξ p, v ≠ 0 ∧ a = u / v) := by
  intro X Ω _ ξ
  refine ⟨fun p => ?_, fun p q h => (RegAtMono.regAt_mono X Ω ξ p q h).1, fun hg p a => ?_⟩
  · unfold regAt
    exact IsLocalRing.of_surjective' (genMap ξ p).rangeRestrict (RingHom.rangeRestrict_surjective _)
  · haveI := (regAt_isLocalRing_isFractionRing_stalk X Ω ξ hg p).2.1
    obtain ⟨u, v, hv, rfl⟩ := IsFractionRing.div_surjective (A := regAt ξ p) a
    refine ⟨u, u.2, v, v.2, fun h => ?_, rfl⟩
    exact nonZeroDivisors.ne_zero hv (Subtype.ext h)

theorem regat_loc : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (c : κ) (p : Cpt M.ξ), InChart M.ξ x c p → (∀ a ∈ chRing o x c, a ∈ regAt M.ξ p) ∧ ∀ a : Ω, a ∈ regAt M.ξ p ↔ ∃ u ∈ chRing o x c, ∃ v ∈ chRing o x c, unitAt M.ξ p v ∧ a = u / v := by
  intro o _ Ω _ _ κ _ x M c p hp
  have h1 : ∀ a ∈ chRing o x c, a ∈ regAt M.ξ p := fun a ha => (M.tie.ring c hp.1 a).1 ha p hp
  refine ⟨h1, fun a => ⟨fun ha => ?_, ?_⟩⟩
  · obtain ⟨s, hs, hu, hsa⟩ := (regAt_iff_exists_chart_fraction M.X Ω M.ξ o κ x M.tie c p hp a).1 ha
    exact ⟨s * a, hsa, s, hs, hu, by field_simp [hu.1]⟩
  · rintro ⟨u, hu, v, -, hv, rfl⟩
    rw [div_eq_mul_inv]
    exact mul_mem (h1 u hu) hv.2.2

theorem prime_pt : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (c : κ), x c ≠ 0 → ∀ P : Ideal (chRing o x c), P.IsPrime → ∃! p : Cpt M.ξ, InChart M.ξ x c p ∧ ∀ u : chRing o x c, u ∈ P ↔ ¬ unitAt M.ξ p (u : Ω) := by
  intro o _ Ω _ _ κ _ x M c hc P hP
  obtain ⟨p, ⟨h1, h2⟩, h3⟩ := chart_point_of_prime M.X Ω M.ξ o κ x M.tie c hc P hP
  refine ⟨p, ⟨h1, fun u => ?_⟩, fun q hq => h3 q ⟨hq.1, fun u => ?_⟩⟩
  · rw [← h2 u, not_not]
  · rw [hq.2 u, not_not]

open ChartPrimes in
theorem basic : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (c : κ) (p : Cpt M.ξ) (U : M.X.Opens), InChart M.ξ x c p → p.1 ∈ U → ∃ f ∈ chRing o x c, unitAt M.ξ p f ∧ ∀ q : Cpt M.ξ, InChart M.ξ x c q → unitAt M.ξ q f → q.1 ∈ U := by
  intro o _ Ω _ _ κ _ x M c p U hp hpU
  have T := M.tie
  have hc := hp.1
  obtain ⟨W, hW, hmem⟩ := T.affine c hc
  have hg : genPt M.ξ ∈ W := (hmem _).2 ⟨specializes_rfl, inChart_genPt T.gen x c hc⟩
  have hpW : p.1 ∈ W := (hmem _).2 ⟨p.2, hp⟩
  obtain ⟨f, hf, hpf⟩ := hW.exists_basicOpen_le (V := U) ⟨p.1, hpU⟩ hpW
  have key : ∀ (q : Cpt M.ξ) (hq : q.1 ∈ W), q.1 ∈ M.X.basicOpen f ↔ unitAt M.ξ q (secVal M.ξ W hg f) := by
    intro q hq
    rw [M.X.mem_basicOpen f _ hq, ← genMap_germ_eq W hg q hq f]
    exact isUnit_iff_unitAt q (T.gen.inj _) _
  refine ⟨secVal M.ξ W hg f, ?_, (key p hpW).1 hpf, fun q hq hu => hf ((key q ((hmem _).2 ⟨q.2, hq⟩)).2 hu)⟩
  exact (T.ring c hc _).2 fun q hq => ⟨_, genMap_germ_eq W hg q ((hmem _).2 ⟨q.2, hq⟩) f⟩

theorem reg_le_spec : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (p q : Cpt M.ξ), regAt M.ξ p ≤ regAt M.ξ q ↔ q.1 ⤳ p.1 := by
  intro o _ Ω _ _ κ _ x M p q
  refine ⟨fun h => ?_, (reg_local M.X Ω M.ξ).2.1 p q⟩
  rw [specializes_iff_forall_open]
  intro s hs hp
  obtain ⟨c, hc⟩ := M.tie.cover p
  obtain ⟨f, -, hu, hf⟩ := basic o Ω κ x M c p ⟨s, hs⟩ hc hp
  exact hf q ⟨hc.1, fun j => h (hc.2 j)⟩ ⟨hu.1, h hu.2.1, h hu.2.2⟩

end PositivityTheory.HtPt.Ma
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.InChartOfMemCtrSet
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb

theorem mem_ctrSet_of {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} {x : κ → Ω}
    {X' : Scheme.{0}} {Ω' : Type} [Field Ω'] {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {i : Ω →+* Ω'} {p' : Cpt ξ'}
    (c : κ) (hc : x c ≠ 0) (ho : ∀ r : o, i (algebraMap o Ω r) ∈ regAt ξ' p')
    (hx : ∀ j, i (x j / x c) ∈ regAt ξ' p') : p' ∈ ctrSet o x i ξ' := by
  refine ⟨c, hc, fun a ha => ?_⟩
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    exact hx j
  | algebraMap r => exact ho r
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz

theorem join_charts : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ κ' : Type) (x : κ → Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (i : Ω →+* Ω') (w : κ' → Ω') (M' : PModel o (joinCo i x w)), (∀ a : o, i (algebraMap o Ω a) = algebraMap o Ω' a) → ∀ p' : Cpt M'.ξ, p' ∈ ctrSet o x i M'.ξ ∧ ∃ l, InChart M'.ξ w l p' := by
  intro o _ Ω _ _ κ κ' x Ω' _ _ i w M' hi p'
  obtain ⟨⟨c, l⟩, hc⟩ := M'.tie.cover p'
  have h0 : i (x c) * w l ≠ 0 := hc.1
  have h1 := left_ne_zero_of_mul h0
  have h2 := right_ne_zero_of_mul h0
  refine ⟨mem_ctrSet_of c ((map_ne_zero i).1 h1) (fun r => ?_) fun j => ?_, l, h2, fun j => ?_⟩
  · rw [hi]
    exact (M'.tie.ring (c, l) hc.1 _).1 (Subalgebra.algebraMap_mem _ r) p' hc
  · have := hc.2 (j, l)
    simp only [joinCo] at this
    rwa [mul_div_mul_right _ _ h2, ← map_div₀] at this
  · have := hc.2 (c, j)
    simp only [joinCo] at this
    rwa [mul_div_mul_left _ _ h1] at this

end PositivityTheory.HtPt.Mb
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.GenfibMap
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb

theorem dom_local : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (f : X' ⟶ X), Dominates ξ' ξ f i → ∀ p' : Cpt ξ', ∃ h : genPt ξ ⤳ f p'.1, ((∀ a ∈ regAt ξ ⟨f p'.1, h⟩, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt ξ ⟨f p'.1, h⟩, unitAt ξ' p' (i a) → unitAt ξ ⟨f p'.1, h⟩ a) := by
  intro X Ω _ ξ X' Ω' _ ξ' i f hd p'
  obtain ⟨q, hq⟩ := p'
  have hp : genPt ξ ⤳ f q := RegAtDom.map_genPt hd ▸ hq.map f.continuous
  refine ⟨hp, ?_, ?_⟩
  · rintro _ ⟨s, rfl⟩
    exact ⟨(f.stalkMap q).hom s, RegAtDom.genMap_stalkMap hd q hq hp s⟩
  · rintro _ ⟨s, rfl⟩ ⟨h0, -, t, ht⟩
    have hv := RegAtDom.genMap_stalkMap hd q hq hp s
    have hone : genMap ξ' ⟨q, hq⟩ (1 - (f.stalkMap q).hom s * t) = 0 := by
      rw [map_sub, map_mul, map_one, hv, ht, mul_inv_cancel₀ h0, sub_self]
    have hu : IsUnit ((f.stalkMap q).hom s) := by
      rcases IsLocalRing.isUnit_or_isUnit_one_sub_self ((f.stalkMap q).hom s * t) with h | h
      · exact isUnit_of_mul_isUnit_left h
      · have h' := h.map (genMap ξ' ⟨q, hq⟩)
        rw [hone] at h'
        exact absurd h' not_isUnit_zero
    exact RegAtMono.unitAt_of_isUnit ξ ⟨f q, hp⟩ (isUnit_of_map_unit (f.stalkMap q).hom s hu)

theorem dom_comp {X X₁ X₂ : Scheme.{0}} {Ω Ω₁ Ω₂ : Type} [Field Ω] [Field Ω₁] [Field Ω₂]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ₁ : Spec (CommRingCat.of Ω₁) ⟶ X₁} {ξ₂ : Spec (CommRingCat.of Ω₂) ⟶ X₂}
    {f : X₁ ⟶ X} {g : X₂ ⟶ X₁} {i : Ω →+* Ω₁} {k : Ω₁ →+* Ω₂} (hf : Dominates ξ₁ ξ f i)
    (hg : Dominates ξ₂ ξ₁ g k) : Dominates ξ₂ ξ (g ≫ f) (k.comp i) := by
  unfold Dominates at *
  rw [← Category.assoc, hg, Category.assoc, hf, ← Category.assoc, ← Spec.map_comp]
  rfl

theorem iso_comp : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (X₁ X₂ : Scheme.{0}) (Ω' : Type) [Field Ω'] (i : Ω →+* Ω') (p : Cpt ξ), (∀ (ξ₁ : Spec (CommRingCat.of Ω) ⟶ X₁) (ξ₂ : Spec (CommRingCat.of Ω') ⟶ X₂) (f : X₁ ⟶ X) (g : X₂ ⟶ X₁), Dominates ξ₂ ξ₁ g i → IsoAt ξ₁ f (RingHom.id Ω) p → (∀ p₁ : Cpt ξ₁, f p₁.1 = p.1 → NormAt ξ₂ g i p₁) → NormAt ξ₂ (g ≫ f) i p) ∧ (∀ (ξ₁ : Spec (CommRingCat.of Ω') ⟶ X₁) (ξ₂ : Spec (CommRingCat.of Ω') ⟶ X₂) (f : X₁ ⟶ X) (g : X₂ ⟶ X₁), Dominates ξ₂ ξ₁ g (RingHom.id Ω') → NormAt ξ₁ f i p → (∀ p₁ : Cpt ξ₁, f p₁.1 = p.1 → IsoAt ξ₂ g (RingHom.id Ω') p₁) → NormAt ξ₂ (g ≫ f) i p) ∧ (∀ (ξ₁ : Spec (CommRingCat.of Ω) ⟶ X₁) (ξ₂ : Spec (CommRingCat.of Ω) ⟶ X₂) (f : X₁ ⟶ X) (g : X₂ ⟶ X₁), Dominates ξ₂ ξ₁ g (RingHom.id Ω) → IsoAt ξ₁ f (RingHom.id Ω) p → (∀ p₁ : Cpt ξ₁, f p₁.1 = p.1 → IsoAt ξ₂ g (RingHom.id Ω) p₁) → IsoAt ξ₂ (g ≫ f) (RingHom.id Ω) p) := by
  intro X Ω _ ξ X₁ X₂ Ω' _ i p
  refine ⟨fun ξ₁ ξ₂ f g hg hf hn => ?_, fun ξ₁ ξ₂ f g hg hf hn => ?_, fun ξ₁ ξ₂ f g hg hf hn => ?_⟩
  · have hr : ∀ p₁ : Cpt ξ₁, f p₁.1 = p.1 → regAt ξ p = regAt ξ₁ p₁ := fun p₁ h => by
      rw [hf.regAt_eq p₁ h, Subring.map_id]
    refine ⟨fun q hq => ?_, ?_, by
      have h := dom_comp hf.dom hg
      rwa [RingHom.comp_id] at h⟩
    · obtain ⟨h, -⟩ := dom_local _ _ ξ₁ _ _ ξ₂ i g hg q
      rw [hr ⟨_, h⟩ hq]
      exact (hn ⟨_, h⟩ hq).exists_max q rfl
    · obtain ⟨p₁, h₁, hu⟩ := hf.existsUnique
      rw [hr p₁ h₁]
      intro P hP
      obtain ⟨q, ⟨hq, hq'⟩, hqu⟩ := (hn p₁ h₁).existsUnique P hP
      refine ⟨q, ⟨(congrArg f hq).trans h₁, hq'⟩, fun q' hq'' => hqu q' ⟨?_, hq''.2⟩⟩
      obtain ⟨h, -⟩ := dom_local _ _ ξ₁ _ _ ξ₂ i g hg q'
      exact congrArg Subtype.val (hu ⟨_, h⟩ hq''.1)
  · have hr : ∀ (q : Cpt ξ₂) (p₁ : Cpt ξ₁), g q.1 = p₁.1 → f p₁.1 = p.1 → regAt ξ₂ q = regAt ξ₁ p₁ :=
      fun q p₁ h h' => by rw [(hn p₁ h').regAt_eq q h, Subring.map_id]
    refine ⟨fun q hq => ?_, fun P hP => ?_, by
      have h := dom_comp hf.dom hg
      rwa [RingHom.id_comp] at h⟩
    · obtain ⟨h, -⟩ := dom_local _ _ ξ₁ _ _ ξ₂ _ g hg q
      rw [hr q ⟨_, h⟩ rfl hq]
      exact hf.exists_max ⟨_, h⟩ hq
    · obtain ⟨p₁, ⟨h₁, h₁'⟩, hu⟩ := hf.existsUnique P hP
      obtain ⟨q, hq, hqu⟩ := (hn p₁ h₁).existsUnique
      refine ⟨q, ⟨(congrArg f hq).trans h₁, (hr q p₁ hq h₁).trans h₁'⟩, fun q' hq' => hqu q' ?_⟩
      obtain ⟨h, -⟩ := dom_local _ _ ξ₁ _ _ ξ₂ _ g hg q'
      exact congrArg Subtype.val (hu ⟨_, h⟩ ⟨hq'.1, (hr q' ⟨_, h⟩ rfl hq'.1).symm.trans hq'.2⟩)
  · refine ⟨?_, fun q hq => ?_, by
      have h := dom_comp hf.dom hg
      rwa [RingHom.comp_id] at h⟩
    · obtain ⟨p₁, h₁, hu⟩ := hf.existsUnique
      obtain ⟨q, hq, hqu⟩ := (hn p₁ h₁).existsUnique
      refine ⟨q, (congrArg f hq).trans h₁, fun q' hq' => hqu q' ?_⟩
      obtain ⟨h, -⟩ := dom_local _ _ ξ₁ _ _ ξ₂ _ g hg q'
      exact congrArg Subtype.val (hu ⟨_, h⟩ hq')
    · obtain ⟨h, -⟩ := dom_local _ _ ξ₁ _ _ ξ₂ _ g hg q
      rw [(hn ⟨_, h⟩ hq).regAt_eq q rfl, Subring.map_id, hf.regAt_eq ⟨_, h⟩ hq]

end PositivityTheory.HtPt.Mb
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.NearMemSpan
noncomputable section

namespace PositivityTheory.HtPt.Mc

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

section
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

theorem near_all {ι : Type} [Finite ι] (p : Cpt ξ) (P : ι → Cpt ξ → Prop)
    (h : ∀ i, ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → P i q) :
    ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → ∀ i, P i q := by
  choose U hU hP using h
  refine ⟨⟨⋂ i, (U i : Set X), isOpen_iInter_of_finite fun i => (U i).isOpen⟩, ?_, fun q hq i => hP i q ?_⟩
  · exact Set.mem_iInter.2 hU
  · exact Set.mem_iInter.1 hq i

theorem near_mem_span {n : ℕ} (g : Fin n → E) (p : Cpt ξ) (e : E)
    (h : e ∈ Submodule.span (regAt ξ p) (Set.range g)) :
    ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → e ∈ Submodule.span (regAt ξ q) (Set.range g) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h
  obtain ⟨U, hU, H⟩ := near_all p (fun i q => (c i : Ω) ∈ regAt ξ q)
    fun i => (regAt_unitAt_open X Ω ξ p (c i)).1 (c i).2
  exact ⟨U, hU, fun q hq => (Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun i => ⟨c i, H q hq i⟩, hc⟩⟩

theorem near_span_eq {n m : ℕ} (g : Fin n → E) (b : Fin m → E) (p : Cpt ξ)
    (h : Submodule.span (regAt ξ p) (Set.range g) = Submodule.span (regAt ξ p) (Set.range b)) :
    ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U →
      Submodule.span (regAt ξ q) (Set.range g) = Submodule.span (regAt ξ q) (Set.range b) := by
  obtain ⟨U, hU, H⟩ := near_all p (fun i q => g i ∈ Submodule.span (regAt ξ q) (Set.range b))
    fun i => near_mem_span b p _ (h ▸ Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨U', hU', H'⟩ := near_all p (fun i q => b i ∈ Submodule.span (regAt ξ q) (Set.range g))
    fun i => near_mem_span g p _ (h ▸ Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨U ⊓ U', ⟨hU, hU'⟩, fun q hq => le_antisymm ?_ ?_⟩
  · exact Submodule.span_le.2 (Set.range_subset_iff.2 (H q hq.1))
  · exact Submodule.span_le.2 (Set.range_subset_iff.2 (H' q hq.2))

end

theorem frame_spread : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (T : Set (Cpt ξ)) (r : ℕ) (b : Fin r → E) (p : Cpt ξ), L.IsCohOn T → p ∈ T → L.IsFrameAt b p → ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q ∈ T, q.1 ∈ U → L.IsFrameAt b q := by
  intro X Ω _ ξ E _ _ L T r b p hL hp hb
  obtain ⟨U, hU, n, g, hg⟩ := hL p hp
  obtain ⟨U', hU', H⟩ := near_span_eq g b p ((hg p hp hU).symm.trans hb.2)
  exact ⟨U ⊓ U', ⟨hU, hU'⟩, fun q hq hqU => ⟨hb.1, (hg q hq hqU.1).trans (H q hqU.2)⟩⟩

section
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E E' : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E'] [Module Ω E']

theorem map_of_span {L : Lat ξ E} (φ : E →ₗ[Ω] E') {q : Cpt ξ} {ι : Type} {b : ι → E}
    (h : L q = Submodule.span (regAt ξ q) (Set.range b)) :
    L.map φ q = Submodule.span (regAt ξ q) (Set.range (φ ∘ b)) := by
  unfold Lat.map
  rw [h, Submodule.map_span, Set.range_comp]
  rfl

theorem coh_map {L : Lat ξ E} {T : Set (Cpt ξ)} (φ : E →ₗ[Ω] E') (h : L.IsCohOn T) : (L.map φ).IsCohOn T := by
  intro p hp
  obtain ⟨U, hU, n, g, hg⟩ := h p hp
  exact ⟨U, hU, n, φ ∘ g, fun q hq hqU => map_of_span φ (hg q hq hqU)⟩

theorem vb_of_coh {L : Lat ξ E} {T : Set (Cpt ξ)} {r : ℕ} {V : Submodule Ω E} (h : L.IsCohOn T)
    (hb : ∀ p ∈ T, ∃ b : Fin r → E, Submodule.span Ω (Set.range b) = V ∧ L.IsFrameAt b p) : L.IsVBOn T r V := by
  intro p hp
  obtain ⟨b, hV, hb⟩ := hb p hp
  obtain ⟨U, hU, H⟩ := frame_spread X Ω ξ E L T r b p h hp hb
  exact ⟨U, hU, b, hV, H⟩

theorem span_smul_fam {ι : Type} (b : ι → E) {a : Ω} (ha : a ≠ 0) :
    Submodule.span Ω (Set.range fun i => a • b i) = Submodule.span Ω (Set.range b) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨i, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rintro _ ⟨i, rfl⟩
    have : b i = a⁻¹ • a • b i := by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem li_smul_fam {ι : Type} {b : ι → E} (hb : LinearIndependent Ω b) {a : Ω} (ha : a ≠ 0) :
    LinearIndependent Ω fun i => a • b i :=
  hb.units_smul fun _ => Units.mk0 a ha

end

theorem coh_ops : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (E' : Type) [AddCommGroup E'] [Module Ω E'] (L L' : Lat ξ E) (T : Set (Cpt ξ)), (∀ r V, L.IsVBOn T r V → L.IsCohOn T) ∧ (∀ φ : E →ₗ[Ω] E', L.IsCohOn T → (L.map φ).IsCohOn T) ∧ (L.IsCohOn T → L'.IsCohOn T → Lat.IsCohOn (fun p => L p ⊔ L' p : Lat ξ E) T) ∧ (∀ (r : ℕ) (V : Submodule Ω E) (a : Ω), a ≠ 0 → L.IsVBOn T r V → (L.scale a).IsVBOn T r V) ∧ (∀ (r : ℕ) (V : Submodule Ω E), L.IsCohOn T → (∀ p ∈ T, ∃ b : Fin r → E, Submodule.span Ω (Set.range b) = V ∧ L.IsFrameAt b p) → L.IsVBOn T r V) := by
  intro X Ω _ ξ E _ _ E' _ _ L L' T
  refine ⟨fun r V h => Lat.IsCohOn.of_isVBOn h, fun φ h => coh_map φ h, fun h h' p hp => ?_,
    fun r V a ha h p hp => ?_, fun r V h hb => vb_of_coh h hb⟩
  · obtain ⟨U, hU, n, g, hg⟩ := h p hp
    obtain ⟨U', hU', n', g', hg'⟩ := h' p hp
    refine ⟨U ⊓ U', ⟨hU, hU'⟩, n + n', Fin.append g g', fun q hq hqU => ?_⟩
    have e : Set.range (Fin.append g g') = Set.range g ∪ Set.range g' := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        induction i using Fin.addCases with
        | left i => exact Or.inl ⟨i, by simp⟩
        | right i => exact Or.inr ⟨i, by simp⟩
      · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
        · exact ⟨Fin.castAdd n' i, by simp⟩
        · exact ⟨Fin.natAdd n i, by simp⟩
    rw [e, Submodule.span_union, ← hg q hq hqU.1, ← hg' q hq hqU.2]
  · obtain ⟨U, hU, b, hV, hb⟩ := h p hp
    refine ⟨U, hU, fun i => a • b i, (span_smul_fam b ha).trans hV, fun q hq hqU =>
      ⟨li_smul_fam (hb q hq hqU).1 ha, ?_⟩⟩
    exact map_of_span _ (hb q hq hqU).2

end PositivityTheory.HtPt.Mc
end
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.KftwoDefs
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace PositivityTheory.HtPt.Kftwo

structure PairHost {E E' : Type} [Field E] [NumberField E] [IsCMField E] [Field E'] [NumberField E'] [IsCMField E']
    (H : Host E) (H' : Host E') where

  ψ : 𝓞 E' →+* Matrix (Fin 2) (Fin 2) (𝓞 E)

  σ : 𝓞 E' ≃+* 𝓞 E'
  bar : ∀ a i j, ψ (H'.bar a) i j = H.bar (ψ a j i)
  w0 : ψ H'.w0 = Matrix.scalar (Fin 2) H.w0
  conj : ∀ a, ψ (σ a) * Matrix.diagonal ![1, -1] = Matrix.diagonal ![1, -1] * ψ a
  rt : σ H'.rt = H'.rt
  chars : ∀ (k : Type) [Field k] [CharZero k] (τ τ' : 𝓞 E' →+* k), τ H'.rt = τ' H'.rt →
    τ' = τ ∨ τ' = τ.comp σ.toRingHom

end PositivityTheory.HtPt.Kftwo
end
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.FinClosure
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb

theorem fin_closure : ∀ (A : Type) [CommRing A] [IsDomain A] [Algebra.EssFiniteType ℤ A] (K : Type) [Field K] [Algebra A K] [IsFractionRing A K] (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra A L] [IsScalarTower A K L], Module.Finite A (integralClosure A L) := by
  intro A _ _ _ K _ _ _ L _ _ _ _ _
  let A₀ := Algebra.EssFiniteType.subalgebra ℤ A
  let S := Algebra.EssFiniteType.submonoid ℤ A
  have hS : ∀ a : A, ∃ u s : A₀, IsUnit (s : A) ∧ a * s = u := fun a => by
    obtain ⟨⟨u, s⟩, e⟩ := IsLocalization.surj S a
    exact ⟨u, s, IsLocalization.map_units A s, e⟩
  have : FaithfulSMul A₀ K := (faithfulSMul_iff_algebraMap_injective _ _).2
    ((IsFractionRing.injective A K).comp Subtype.val_injective)
  have : IsFractionRing A₀ K := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) z
    obtain ⟨u, s, hs, e⟩ := hS a
    obtain ⟨v, t, ht, e'⟩ := hS b
    refine ⟨u * t, v * s, ?_⟩
    have h1 : algebraMap A K s ≠ 0 := (hs.map _).ne_zero
    have h2 : algebraMap A K t ≠ 0 := (ht.map _).ne_zero
    show _ = algebraMap A K (u * t) / algebraMap A K (v * s)
    rw [← e, ← e']
    simp only [map_mul]
    rw [mul_assoc, mul_assoc, mul_comm (algebraMap A K t), mul_div_mul_right _ _ (mul_ne_zero h1 h2)]
  have hfin : Module.Finite A₀ (integralClosure A₀ L) :=
    GroundTheory.Heights₂.Heights.Model.FiniteIntegralClosure.proof A₀ K L
  obtain ⟨g, hg⟩ : (Subalgebra.toSubmodule (integralClosure A₀ L)).FG := Module.Finite.iff_fg.1 hfin
  refine (Module.Finite.iff_fg (N := Subalgebra.toSubmodule (integralClosure A L))).2 ⟨g, le_antisymm ?_ ?_⟩
  · refine Submodule.span_le.2 fun y hy => ?_
    have h : y ∈ Subalgebra.toSubmodule (integralClosure A₀ L) := hg ▸ Submodule.subset_span hy
    exact IsIntegral.tower_top (R := A₀) h
  · intro y hy
    obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization S y (hy : IsIntegral A y)
    have h : m • y ∈ Submodule.span A₀ (g : Set L) := by
      rw [hg]
      exact hm
    have h' : (m.1 : A) • y ∈ Submodule.span A (g : Set L) := Submodule.span_le_restrictScalars A₀ A _ h
    obtain ⟨w, hw⟩ := (IsLocalization.map_units A m).exists_left_inv
    have := Submodule.smul_mem _ w h'
    have hw' : w * (m.1 : A) = 1 := hw
    rwa [smul_smul, hw', one_smul] at this

end PositivityTheory.HtPt.Mb
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.OfMem
set_option backward.isDefEq.respectTransparency false

noncomputable section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.HtPt.Ci.Val

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {R : Type} [CommRing R]
  [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X}

theorem one (h : genPt ξ ⤳ centre z) : ValAt ξ z 1 1 := ⟨h, 1, map_one _, map_one _⟩

theorem mul {a b : Ω} {r s : R} (ha : ValAt ξ z a r) (hb : ValAt ξ z b s) : ValAt ξ z (a * b) (r * s) := by
  obtain ⟨h, u, rfl, rfl⟩ := ha
  obtain ⟨_, v, rfl, rfl⟩ := hb
  exact ⟨h, u * v, map_mul _ _ _, map_mul _ _ _⟩

theorem pow {a : Ω} {r : R} (ha : ValAt ξ z a r) (n : ℕ) : ValAt ξ z (a ^ n) (r ^ n) := by
  obtain ⟨h, u, rfl, rfl⟩ := ha
  exact ⟨h, u ^ n, map_pow _ _ _, map_pow _ _ _⟩

theorem prod (h : genPt ξ ⤳ centre z) {ι : Type} (T : Finset ι) {a : ι → Ω} {r : ι → R}
    (ha : ∀ k, ValAt ξ z (a k) (r k)) : ValAt ξ z (∏ k ∈ T, a k) (∏ k ∈ T, r k) := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty]; exact one h
  | insert k T hk ih => rw [Finset.prod_insert hk, Finset.prod_insert hk]; exact mul (ha k) ih

theorem mem {a : Ω} {r : R} (ha : ValAt ξ z a r) (h : genPt ξ ⤳ centre z) : a ∈ regAt ξ ⟨centre z, h⟩ := by
  obtain ⟨_, u, rfl, -⟩ := ha
  exact ⟨u, rfl⟩

theorem of_mem {a : Ω} {h : genPt ξ ⤳ centre z} (ha : a ∈ regAt ξ ⟨centre z, h⟩) : ∃ r, ValAt ξ z a r := by
  obtain ⟨u, rfl⟩ := ha
  exact ⟨_, h, u, rfl, rfl⟩

theorem zpow {K : Type} [Field K] {z : Spec (CommRingCat.of K) ⟶ X} {a : Ω} {r : K} (ha : ValAt ξ z a r)
    (ha' : ValAt ξ z a⁻¹ r⁻¹) (n : ℤ) : ValAt ξ z (a ^ n) (r ^ n) := by
  cases n with
  | ofNat n => simpa using pow ha n
  | negSucc n => simpa only [zpow_negSucc, inv_pow] using pow ha' (n + 1)

end PositivityTheory.HtPt.Ci.Val
end
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.DetUpdateRowDiagonal
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rh

theorem det_updateRow_diagonal {R : Type} [CommRing R] {m : ℕ} (c r : Fin m → R) (i : Fin m) :
    ((Matrix.diagonal c).updateRow i r).det = (∏ j ∈ Finset.univ.erase i, c j) * r i := by
  rw [← Matrix.cramer_transpose_apply, Matrix.diagonal_transpose, Matrix.cramer_eq_adjugate_mulVec,
    Matrix.adjugate_diagonal, Matrix.mulVec_diagonal]

theorem len_eq : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → ∀ (ι : Type) [Fintype ι] (L L' : Submodule R (ι → R)), L ≤ L' → ∀ x y : NNReal, x ≠ 0 → HasLen v R ((ι → R) ⧸ L) x → HasLen v R ((ι → R) ⧸ L') y → x ≤ y ∧ (x = y → L = L') := by
  intro C _ v R _ _ hv ι _ L L' hL x y hx0 hx hy
  obtain ⟨m, c, ⟨e⟩, rfl⟩ := hx
  obtain ⟨n, d, ⟨e'⟩, rfl⟩ := hy
  haveI := isLocal_of_integers hv
  let π : ((i : Fin m) → R ⧸ Ideal.span {c i}) →ₗ[R] ((i : Fin n) → R ⧸ Ideal.span {d i}) :=
    e'.toLinearMap ∘ₗ (Submodule.factor hL) ∘ₗ e.symm.toLinearMap
  have hπ : Function.Surjective π :=
    e'.surjective.comp ((Submodule.factor_surjective hL).comp e.symm.surjective)
  let s : Fin m → ((i : Fin m) → R ⧸ Ideal.span {c i}) :=
    fun i => Pi.single i (1 : R ⧸ Ideal.span {c i})
  have hsp : Submodule.span R (Set.range fun i => π (s i)) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨w, rfl⟩ := hπ z
    set_option synthInstance.maxHeartbeats 100000 in
      rw [eq_sum_single c w, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hdiag : ∀ k, ∑ i, Matrix.diagonal c k i • π (s i) = 0 := by
    intro k
    rw [Finset.sum_eq_single k]
    · rw [Matrix.diagonal_apply_eq, ← map_smul, single_smul_self c k, map_zero]
    · intro i _ hi
      rw [Matrix.diagonal_apply_ne' _ hi, zero_smul]
    · simp
  have key : ∀ T : Matrix (Fin m) (Fin m) R, (∀ k, ∑ i, T k i • π (s i) = 0) →
      v (algebraMap R C T.det) ≤ ∏ i, v (algebraMap R C (d i)) := by
    intro T hT
    have h := det_mem_span_prod n d m _ hsp T hT
    rw [Ideal.mem_span_singleton] at h
    have h2 := hv.le_of_dvd h
    rwa [map_prod, map_prod] at h2
  refine ⟨?_, fun hxy => le_antisymm hL fun l hl => ?_⟩
  · have := key _ hdiag
    rwa [Matrix.det_diagonal, map_prod, map_prod] at this
  · set w := e (Submodule.Quotient.mk l) with hw
    have hπw : π w = 0 := by
      have : (Submodule.Quotient.mk l : (ι → R) ⧸ L') = 0 := (Submodule.Quotient.mk_eq_zero _).2 hl
      simp [π, hw, this]
    have hw0 : w = 0 := by
      funext i
      have hrel : ∑ k, (Quotient.out (w k) : R) • π (s k) = 0 := by
        rw [← hπw]
        set_option synthInstance.maxHeartbeats 100000 in
          conv_rhs => rw [eq_sum_single c w, map_sum]
        simp only [map_smul, s]
      have h := key ((Matrix.diagonal c).updateRow i fun k => (Quotient.out (w k) : R)) (by
        intro k
        by_cases hk : k = i
        · subst hk
          simpa only [Matrix.updateRow_self] using hrel
        · simpa only [Matrix.updateRow_ne hk] using hdiag k)
      rw [det_updateRow_diagonal, ← hxy, map_mul, map_mul, map_prod, map_prod,
        ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)] at h
      have hne : ∏ j ∈ Finset.univ.erase i, v (algebraMap R C (c j)) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun j _ =>
          Finset.prod_ne_zero_iff.1 hx0 j (Finset.mem_univ j)
      have h2 := le_of_mul_le_mul_left h (pos_iff_ne_zero.2 hne)
      have h3 := hv.dvd_of_le h2
      rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.mk_out] at h3
      exact h3
    have : (Submodule.Quotient.mk l : (ι → R) ⧸ L) = 0 := e.injective (by rw [← hw, hw0, map_zero])
    exact (Submodule.Quotient.mk_eq_zero _).1 this

end PositivityTheory.HtPt.Rh
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.DegLeOfEquiv
open GlobalTheory.CompanionTheory.Ar.Crv

namespace PositivityTheory.HtPt.Ch

section SlopeTestRemainingChoices

variable {K : Type} [Field K] {C : ACurve K} {V : Type} [AddCommGroup V] [Module K V]

theorem basis_mem {i : C.I} {n : ℕ} {b : Module.Basis (Fin n) K V} {L : AddSubgroup V}
    (h : IsLatOf C i b L) (q : Fin n) : b q ∈ L := by
  refine (h _).2 fun r => ?_
  by_cases e : q = r <;> simp [e, Finsupp.single_apply]

theorem smul_mem_lat {i : C.I} {n : ℕ} {b : Module.Basis (Fin n) K V} {L : AddSubgroup V}
    (h : IsLatOf C i b L) {a : K} (ha : C.v i a ≤ 1) {x : V} (hx : x ∈ L) : a • x ∈ L := by
  refine (h _).2 fun r => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul]
  exact mul_le_one' ha ((h _).1 hx r)

theorem v_det_le {i : C.I} {n : ℕ} {b b' : Module.Basis (Fin n) K V} {L L' : AddSubgroup V}
    (h : IsLatOf C i b L) (h' : IsLatOf C i b' L') (hle : L ≤ L') : C.v i (b'.det b) ≤ 1 := by
  rw [Module.Basis.det_apply, Matrix.det_apply']
  refine (C.v i).map_sum_le fun σ _ => ?_
  rw [map_mul, map_prod]
  refine mul_le_one' ?_ (Finset.prod_le_one' fun q _ => (h' _).1 (hle (basis_mem h q)) _)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e | e <;> simp [e]

theorem deg_triv [FiniteDimensional K V] {n : ℕ} (b : Module.Basis (Fin n) K V)
    {L : C.I → AddSubgroup V} (h : ∀ i, IsLatOf C i b (L i)) : IsBun C L ∧ deg C L = 0 := by
  have hb : IsBun C L := Inhab.isBun_of_basis C b L h
  refine ⟨hb, ?_⟩
  rw [(GlobalTheory.T.bundle_degree_eq_sum_valuations K C V L n b (fun _ => b) hb h).2]
  simp [Module.Basis.det_self]

end SlopeTestRemainingChoices

theorem deg_mono : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L L' : C.I → AddSubgroup V), IsBun C L → IsBun C L' → (∀ i, L i ≤ L' i) → deg C L ≤ deg C L' := by
  intro K _ C V _ _ _ L L' hL hL' hle
  choose b hb using hL.1
  choose b' hb' using hL'.1
  obtain ⟨hf, e⟩ := GlobalTheory.T.bundle_degree_eq_sum_valuations K C V L _ (Module.finBasis K V) b hL hb
  obtain ⟨hf', e'⟩ := GlobalTheory.T.bundle_degree_eq_sum_valuations K C V L' _ (Module.finBasis K V) b' hL' hb'
  rw [e, e']
  refine finsum_le_finsum' (hf.subset fun i hi h1 => hi (by simp [h1]))
    (hf'.subset fun i hi h1 => hi (by simp [h1])) fun i => ?_
  refine mul_le_mul_of_nonneg_left ?_ (Int.natCast_nonneg _)
  have n1 : C.v i ((Module.finBasis K V).det (b i)) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 ((Module.finBasis K V).isUnit_det (b i)).ne_zero
  have n2 : C.v i ((Module.finBasis K V).det (b' i)) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 ((Module.finBasis K V).isUnit_det (b' i)).ne_zero
  rw [WithZero.log_le_log n1 n2, ← Module.Basis.det_mul_det _ (b' i) (b i), map_mul]
  exact mul_le_of_le_one_right' (v_det_le (hb i) (hb' i) (hle i))

theorem deg_le_of_equiv {K : Type} [Field K] {C : ACurve K} {V V' : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
    {L : C.I → AddSubgroup V} {L' : C.I → AddSubgroup V'} (e : V ≃ₗ[K] V') (hL : IsBun C L)
    (hL' : IsBun C L') (h : ∀ i, ∀ x ∈ L i, e x ∈ L' i) : deg C L ≤ deg C L' := by
  obtain ⟨hM, hd⟩ := GlobalTheory.T.degree_invariant_linear_equiv K C V V' L
    (fun i => (L i).comap e.symm.toLinearMap.toAddMonoidHom) e hL (fun i x => by simp)
  rw [← hd]
  refine deg_mono K C V' _ _ hM hL' fun i y hy => ?_
  simpa using h i (e.symm y) hy

theorem deg_inj : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (f : V →ₗ[K] V') (W : Submodule K V), IsBun C L → IsBun C L' → Function.Injective f → IsHom C L L' f → subDeg C L W ≤ subDeg C L' (W.map f) := by
  intro K _ C V _ _ _ V' _ _ _ L L' f W hL hL' hf hh
  exact deg_le_of_equiv (Submodule.equivMapOfInjective f hf W) (GlobalTheory.T.sub_and_quotient_bundles K C V L W hL).1
    (GlobalTheory.T.sub_and_quotient_bundles K C V' L' _ hL').1 fun i x hx => hh i x hx

theorem subdeg_trivial : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (n : ℕ) (b : Module.Basis (Fin n) K V) (L : C.I → AddSubgroup V) (W : Submodule K V), (∀ i, IsLatOf C i b (L i)) → subDeg C L W ≤ 0 := by
  intro K _ C V _ _ _ n b L W h
  obtain ⟨hL, h0⟩ := deg_triv b h
  have hs := GlobalTheory.T.degree_additive_sub_quotient K C V L W hL
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K (fun q => W.mkQ (b q))
  have : Finite κ := Finite.of_injective a ha
  have : Fintype κ := Fintype.ofFinite κ
  have htop : ⊤ ≤ Submodule.span K (Set.range ((fun q => W.mkQ (b q)) ∘ a)) := by
    rw [hsp, show (Set.range fun q => W.mkQ (b q)) = W.mkQ '' Set.range b from
      Set.range_comp _ _, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_mkQ]
  let c := (Module.Basis.mk hli htop).reindex (Fintype.equivFin κ)
  have hc : ∀ q, c q = W.mkQ (b (a ((Fintype.equivFin κ).symm q))) := fun q => by simp [c]
  obtain ⟨hM, hM0⟩ := deg_triv (C := C) c (fun i => Inhab.isLatOf_latOf C i c)
  have := deg_mono K C _ _ _ hM (GlobalTheory.T.sub_and_quotient_bundles K C V L W hL).2 fun i y hy => by
    rw [← c.sum_repr y]
    refine sum_mem fun q _ => ⟨c.repr y q • b (a ((Fintype.equivFin κ).symm q)),
      smul_mem_lat (h i) (hy q) (basis_mem (h i) _), ?_⟩
    rw [hc]; simp
  omega

theorem ses_restrict {K : Type} [Field K] {C : ACurve K} {V V' V'' : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
    [AddCommGroup V''] [Module K V''] [FiniteDimensional K V'']
    {L : C.I → AddSubgroup V} {L' : C.I → AddSubgroup V'} {L'' : C.I → AddSubgroup V''}
    {f : V →ₗ[K] V'} {g : V' →ₗ[K] V''} (hL' : IsBun C L') (h : ShortExact C L L' L'' f g)
    (A : Submodule K V) (X : Submodule K V') (B : Submodule K V'')
    (hA : ∀ x, x ∈ A ↔ f x ∈ X) (hB : ∀ z, z ∈ B ↔ ∃ y ∈ X, g y = z) :
    ∃ I : C.I → AddSubgroup B, IsBun C I ∧ subDeg C L' X = subDeg C L A + deg C I ∧
      ∀ i z, z ∈ I i ↔ ∃ y ∈ L' i, y ∈ X ∧ g y = z := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  let f' : A →ₗ[K] X := f.restrict fun x hx => (hA x).1 hx
  let g' : X →ₗ[K] B := g.restrict fun y hy => (hB _).2 ⟨y, hy, rfl⟩
  have hse : ShortExact C (sub C L A) (sub C L' X)
      (fun i => (sub C L' X i).map g'.toAddMonoidHom) f' g' := by
    refine ⟨fun x y e => Subtype.ext (h1 (congrArg Subtype.val e)), fun y => ⟨fun hy => ?_, ?_⟩,
      fun z => ?_, fun i x => h4 i x, fun i z => Iff.rfl⟩
    · obtain ⟨x, hx⟩ := (h2 y).1 (congrArg Subtype.val hy)
      exact ⟨⟨x, (hA x).2 (hx ▸ y.2)⟩, Subtype.ext hx⟩
    · rintro ⟨x, rfl⟩
      exact Subtype.ext (h2.apply_apply_eq_zero x)
    · obtain ⟨y, hy, e⟩ := (hB z).1 z.2
      exact ⟨⟨y, hy⟩, Subtype.ext e⟩
  obtain ⟨-, hI, hd⟩ := GlobalTheory.T.short_exact_first_term_bundle K C _ _ _ _ _ _ f' g' (GlobalTheory.T.sub_and_quotient_bundles K C V' L' X hL').1 hse
  refine ⟨_, hI, hd, fun i z => ⟨?_, ?_⟩⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, y.2, rfl⟩
  · rintro ⟨y, hy, hX, e⟩
    exact ⟨⟨y, hX⟩, hy, Subtype.ext e⟩

theorem subdeg_ses : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (V'' : Type) [AddCommGroup V''] [Module K V''] [FiniteDimensional K V''] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (L'' : C.I → AddSubgroup V'') (f : V →ₗ[K] V') (g : V' →ₗ[K] V'') (X : Submodule K V'), IsBun C L' → ShortExact C L L' L'' f g → subDeg C L' X ≤ subDeg C L (X.comap f) + subDeg C L'' (X.map g) := by
  intro K _ C V _ _ _ V' _ _ _ V'' _ _ _ L L' L'' f g X hL' h
  obtain ⟨I, hI, hd, hm⟩ := ses_restrict hL' h (X.comap f) X (X.map g) (fun _ => Iff.rfl)
    (fun _ => Iff.rfl)
  have hL'' := (GlobalTheory.T.short_exact_first_term_bundle K C _ _ _ _ _ _ f g hL' h).2.1
  have : deg C I ≤ subDeg C L'' (X.map g) :=
    deg_mono K C _ _ _ hI (GlobalTheory.T.sub_and_quotient_bundles K C V'' L'' _ hL'').1 fun i z hz => by
      obtain ⟨y, hy, -, e⟩ := (hm i z).1 hz
      exact (h.2.2.2.2 i z).2 ⟨y, hy, e⟩
  omega

theorem exists_dot {K : Type} [Field K] {d : ℕ} (ψ : Module.Dual K (Fin d → K)) :
    ∃ u : Fin d → K, ∀ x, u ⬝ᵥ x = ψ x := by
  refine ⟨fun j => ψ (Pi.single j 1), fun x => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    conv_rhs => rw [pi_eq_sum_univ' x, map_sum]
  simp [dotProduct, mul_comm]

theorem subdeg_orth : ∀ (K : Type) [Field K] (C : ACurve K) (d : ℕ) (L : C.I → AddSubgroup (Fin d → K)) (W X : Submodule K (Fin d → K)), IsBun C L → (∀ u, u ∈ W ↔ ∀ φ ∈ X, u ⬝ᵥ φ = 0) → subDeg C (dotDual C L) X = deg C (dotDual C L) + subDeg C L W := by
  intro K _ C d L W X hL hW
  have hbij : Function.Bijective (dotProductBilin K K : (Fin d → K) →ₗ[K] (Fin d → K) →ₗ[K] K) := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun u hu => funext fun j => ?_, fun ψ => ?_⟩
    · simpa using LinearMap.congr_fun hu (Pi.single j 1)
    · obtain ⟨u, hu⟩ := exists_dot ψ
      exact ⟨u, LinearMap.ext hu⟩
  obtain ⟨hD, -, hbi⟩ := GlobalTheory.T.dual_lattice_degree_neg K C _ _ L _ hL hbij
  let B₀ : (Fin d → K) →ₗ[K] W →ₗ[K] K := ((dotProductBilin K K).comp W.subtype).flip
  have hB₀ : ∀ φ (w : W), B₀ φ w = (w : Fin d → K) ⬝ᵥ φ := fun _ _ => rfl
  let B : ((Fin d → K) ⧸ X) →ₗ[K] W →ₗ[K] K :=
    X.liftQ B₀ fun φ hφ => LinearMap.ext fun w => (hW w).1 w.2 φ hφ
  have hB : ∀ φ (w : W), B (X.mkQ φ) w = (w : Fin d → K) ⬝ᵥ φ := fun _ _ => rfl
  have hBb : Function.Bijective B := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun y hy => ?_, fun ψ => ?_⟩
    · obtain ⟨φ, rfl⟩ := X.mkQ_surjective y
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
        ← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
      intro ψ hψ
      obtain ⟨u, hu⟩ := exists_dot ψ
      have hu' : u ∈ W := (hW u).2 fun x hx => by
        rw [hu]; exact (Submodule.mem_dualAnnihilator ψ).1 hψ x hx
      rw [← hu, ← hB φ ⟨u, hu'⟩, hy]; rfl
    · obtain ⟨ψ', rfl⟩ := LinearMap.dualMap_surjective_of_injective W.injective_subtype ψ
      obtain ⟨u, hu⟩ := exists_dot ψ'
      refine ⟨X.mkQ u, LinearMap.ext fun w => ?_⟩
      rw [hB, dotProduct_comm, hu]; rfl
  obtain ⟨-, hq, -⟩ := GlobalTheory.T.dual_lattice_degree_neg K C _ _ _ B (GlobalTheory.T.sub_and_quotient_bundles K C _ _ X hD).2 hBb
  have he : dualLat C (quot C (dualLat C L (dotProductBilin K K)) X) B = sub C L W := by
    funext i; ext w
    have : (w : Fin d → K) ∈ L i ↔ (w : Fin d → K) ∈
        dualLat C (dualLat C L (dotProductBilin K K)) (dotProductBilin K K).flip i := by rw [hbi]
    refine Iff.trans ?_ this.symm
    constructor
    · intro H φ hφ
      exact H _ ⟨φ, hφ, rfl⟩
    · rintro H _ ⟨φ, hφ, rfl⟩
      exact H φ hφ
  have hs := GlobalTheory.T.degree_additive_sub_quotient K C _ _ X hD
  rw [he] at hq
  unfold dotDual
  unfold subDeg at hs ⊢
  omega

end PositivityTheory.HtPt.Ch
end
