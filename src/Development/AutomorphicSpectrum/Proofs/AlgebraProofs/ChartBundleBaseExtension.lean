module

public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamiliesGlueToBundle
public import Development.WeilBound.CoreStatements.HodgeTatePoints.ReBase
public import Development.WeilBound.CoreStatements.HodgeTatePoints.RcFlag
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.LineFibre
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.JPull
public import Development.WeilBound.CoreStatements.HodgeTatePoints.RfTors
public import Development.WeilBound.CoreStatements.HodgeTatePoints.ProdIccFin
public import Development.WeilBound.CoreStatements.HodgeTatePoints.ExistsDenOfOpen

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleBaseExtension
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleBaseExtension
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing div_mem_chartRing exists_pow_mul_mem_chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg restrictChart)

namespace GlobalTheory.CompanionTheory.Ar.Num.PullExists

section Charts

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

def mixChart (c : ∀ k, ι k) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) : ∀ k : K ⊕ K', Sum.elim ι ι' k
  | .inl k => c k
  | .inr k => s (.inr k)

def secondChart (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) : ∀ k, ι' k := fun k => s (.inr k)

theorem restrictChart_mixChart (c : ∀ k, ι k) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) :
    restrictChart (mixChart c s) = c := rfl

theorem secondChart_mixChart (c : ∀ k, ι k) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) :
    secondChart (mixChart c s) = secondChart s := rfl

theorem mseg_joinCoord {F : Type*} [CommMonoid F] (x : (Σ k, ι k) → F) (z : (Σ k, ι' k) → F)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) :
    mseg (joinCoord x z) s = mseg x (restrictChart s) * mseg z (secondChart s) := by
  simp only [mseg, Fintype.prod_sum_type]
  rfl

end Charts

section Pull

variable {O : Type} [CommRing O] {Ω Ω₁ : Type} [Field Ω] [Field Ω₁] [Algebra O Ω] [Algebra O Ω₁]
  [Algebra Ω Ω₁] [IsScalarTower O Ω Ω₁]
  {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {x : (Σ k, ι k) → Ω} {z : (Σ k, ι' k) → Ω₁}

theorem mseg_bcCoord (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω₁)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) :
    mseg (bcCoord x z) s =
      algebraMap Ω Ω₁ (mseg x (restrictChart s)) * mseg z (secondChart s) := by
  rw [bcCoord, mseg_joinCoord]
  simp [mseg, map_prod]

theorem first_ne_zero {s : ∀ k : K ⊕ K', Sum.elim ι ι' k} (hs : mseg (bcCoord x z) s ≠ 0) :
    mseg x (restrictChart s) ≠ 0 := by
  intro h
  exact hs (by rw [mseg_bcCoord, h]; simp)

theorem second_ne_zero {s : ∀ k : K ⊕ K', Sum.elim ι ι' k} (hs : mseg (bcCoord x z) s ≠ 0) :
    mseg z (secondChart s) ≠ 0 := by
  intro h
  exact hs (by rw [mseg_bcCoord, h]; simp)

theorem ratio_first {s : ∀ k : K ⊕ K', Sum.elim ι ι' k} (hs : mseg (bcCoord x z) s ≠ 0)
    (c : ∀ k, ι k) :
    algebraMap Ω Ω₁ (mseg x c / mseg x (restrictChart s)) ∈
      chartRing O (mseg (bcCoord x z)) s := by
  have h := div_mem_chartRing (o := O) (mseg (bcCoord x z)) s (mixChart c s)
  rw [mseg_bcCoord x z (mixChart c s), mseg_bcCoord x z s, restrictChart_mixChart,
    secondChart_mixChart, mul_div_mul_right _ _ (second_ne_zero hs), ← map_div₀] at h
  exact h

theorem ratio_second {s t : ∀ k : K ⊕ K', Sum.elim ι ι' k} (ht : mseg (bcCoord x z) t ≠ 0) :
    mseg z (secondChart s) / mseg z (secondChart t) ∈ chartRing O (mseg (bcCoord x z)) t := by
  have h := div_mem_chartRing (o := O) (mseg (bcCoord x z)) t (mixChart (restrictChart t) s)
  rw [mseg_bcCoord x z (mixChart (restrictChart t) s), mseg_bcCoord x z t, restrictChart_mixChart,
    secondChart_mixChart, mul_div_mul_left _ _
      ((map_ne_zero (algebraMap Ω Ω₁)).2 (first_ne_zero ht))] at h
  exact h

theorem map_mem_chartRing {s : ∀ k : K ⊕ K', Sum.elim ι ι' k} (hs : mseg (bcCoord x z) s ≠ 0)
    {a : Ω} (ha : a ∈ chartRing O (mseg x) (restrictChart s)) :
    algebraMap Ω Ω₁ a ∈ chartRing O (mseg (bcCoord x z)) s := by
  have hle : chartRing O (mseg x) (restrictChart s) ≤
      (chartRing O (mseg (bcCoord x z)) s).comap (IsScalarTower.toAlgHom O Ω Ω₁) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨c, rfl⟩
    exact ratio_first hs c
  exact hle ha

variable {N : ℕ} {V V₁ : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V₁] [Module Ω₁ V₁]
  [Module Ω V₁] [IsScalarTower Ω Ω₁ V₁]

def pullFam (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω₁) (E : ChartBundle O (mseg x) N V)
    (bc : V →ₗ[Ω] V₁) : (∀ k : K ⊕ K', Sum.elim ι ι' k) → AddSubgroup V₁ := fun s =>
  spanOver (chartRing O (mseg (bcCoord x z)) s) (bc '' (E.lat (restrictChart s) : Set V))

theorem isLatFamily_pullFam (E : ChartBundle O (mseg x) N V) (bc : V →ₗ[Ω] V₁) :
    IsLatFamily O (bcCoord x z) (pullFam x z E bc) := by
  refine ⟨fun s _ a ha v hv => LocFreeBC.smul_mem_spanOver _ _ ha hv,
    fun s t hs ht v hv => ?_⟩
  have hf : mseg (bcCoord x z) s / mseg (bcCoord x z) t ∈ chartRing O (mseg (bcCoord x z)) t :=
    div_mem_chartRing _ t s
  have hst : ∀ a ∈ chartRing O (mseg (bcCoord x z)) t, ∀ e ∈ pullFam x z E bc t,
      a • e ∈ pullFam x z E bc t := fun a ha e he => LocFreeBC.smul_mem_spanOver _ _ ha he
  have hfac : mseg (bcCoord x z) s / mseg (bcCoord x z) t =
      algebraMap Ω Ω₁ (mseg x (restrictChart s) / mseg x (restrictChart t)) *
        (mseg z (secondChart s) / mseg z (secondChart t)) := by
    rw [mseg_bcCoord x z s, mseg_bcCoord x z t, map_div₀, mul_div_mul_comm]
  change v ∈ AddSubgroup.closure _ at hv
  induction hv using AddSubgroup.closure_induction with
  | mem v hv =>
    obtain ⟨a, ha, _, ⟨e, he, rfl⟩, rfl⟩ := hv
    obtain ⟨m₁, hm₁⟩ := exists_pow_mul_mem_chartRing (mseg (bcCoord x z)) s t hs ha
    obtain ⟨m₂, hm₂⟩ := E.overlap _ _ (first_ne_zero hs) (first_ne_zero ht) e he
    refine ⟨m₁ + m₂, AddSubgroup.subset_closure ⟨_, mul_mem hm₁ (pow_mem
      (ratio_second (s := s) ht) m₂), _, ⟨_, hm₂, rfl⟩, ?_⟩⟩
    rw [map_smul, ← algebraMap_smul Ω₁ (_ ^ m₂) (bc e), smul_smul, smul_smul]
    congr 1
    rw [pow_add, map_pow]
    nth_rw 2 [hfac]
    rw [mul_pow]
    ring
  | zero => exact ⟨0, by simp⟩
  | add v w _ _ hv hw => exact LocFreeBC.loc_add _ _ hst hf hv hw
  | neg v _ hv =>
    obtain ⟨n, hn⟩ := hv
    exact ⟨n, by simpa using neg_mem hn⟩

theorem locFree_pullFam (E : ChartBundle O (mseg x) N V) (bc : V →ₗ[Ω] V₁)
    (hbc : IsBaseChange Ω₁ bc) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k)
    (hs : mseg (bcCoord x z) s ≠ 0) :
    LocFree (chartRing O (mseg (bcCoord x z)) s) N (pullFam x z E bc s) := by
  classical
  exact LocFreeBC.locFree_baseChange _ _ (fun _ ha => map_mem_chartRing hs ha) bc hbc N _
    (((BundleOfFamily.main O Ω K ι x N V).2 E).2 _ (first_ne_zero hs))

theorem exists_pullBC [IsDomain O] [IsDiscreteValuationRing O] (E : ChartBundle O (mseg x) N V)
    (bc : V →ₗ[Ω] V₁) (hbc : IsBaseChange Ω₁ bc) :
    ∃ EB : ChartBundle O (mseg (bcCoord x z)) N V₁, IsPullBC O x z bc E EB := by
  classical
  obtain ⟨EB, hEB⟩ := (BundleOfFamily.main O Ω₁ (K ⊕ K') (Sum.elim ι ι') (bcCoord x z) N V₁).1
    (pullFam x z E bc) (isLatFamily_pullFam E bc) (locFree_pullFam E bc hbc)
  refine ⟨EB, fun s hs => ?_⟩
  rw [hEB s hs]
  refine congrArg AddSubgroup.closure (Set.ext fun v => ?_)
  constructor
  · rintro ⟨a, ha, _, ⟨e, he, rfl⟩, rfl⟩
    exact ⟨a, ha, e, he, rfl⟩
  · rintro ⟨a, ha, e, he, rfl⟩
    exact ⟨a, ha, _, ⟨e, he, rfl⟩, rfl⟩

end Pull

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E : ChartBundle O (mseg x) N V), (∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω), ∃ EB : ChartBundle O (mseg (joinCoord x z)) N V, IsPull O x z E EB) ∧ ∀ (Ω₁ : Type) [Field Ω₁] [Algebra O Ω₁] [Algebra Ω Ω₁] [IsScalarTower O Ω Ω₁] (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω₁) (V₁ : Type) [AddCommGroup V₁] [Module Ω₁ V₁] [Module Ω V₁] [IsScalarTower Ω Ω₁ V₁] (bc : V →ₗ[Ω] V₁), IsBaseChange Ω₁ bc → ∃ EB : ChartBundle O (mseg (bcCoord x z)) N V₁, IsPullBC O x z bc E EB := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x N V _ _ E
  refine ⟨fun K' _ _ ι' _ z => ?_,
    fun Ω₁ _ _ _ _ K' _ _ ι' _ z V₁ _ _ _ _ bc hbc => exists_pullBC E bc hbc⟩
  exact exists_pullBC (Ω₁ := Ω) (V₁ := V) (z := z) E LinearMap.id
    (IsBaseChange.ofEquiv (LinearEquiv.refl Ω V))

end GlobalTheory.CompanionTheory.Ar.Num.PullExists
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleBaseExtensionStatement
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_bundle_base_extension : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E : ChartBundle O (mseg x) N V), (∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω), ∃ EB : ChartBundle O (mseg (joinCoord x z)) N V, IsPull O x z E EB) ∧ ∀ (Ω₁ : Type) [Field Ω₁] [Algebra O Ω₁] [Algebra Ω Ω₁] [IsScalarTower O Ω Ω₁] (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω₁) (V₁ : Type) [AddCommGroup V₁] [Module Ω₁ V₁] [Module Ω V₁] [IsScalarTower Ω Ω₁ V₁] (bc : V →ₗ[Ω] V₁), IsBaseChange Ω₁ bc → ∃ EB : ChartBundle O (mseg (bcCoord x z)) N V₁, IsPullBC O x z bc E EB := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.PullExists.main | exact GlobalTheory.CompanionTheory.Ar.Num.PullExists.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.PullExists.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderRetractRestriction
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderRetractRestriction
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem ret_hopf_factor : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ AA : HopfOrder (C := C) R N, ∀ (N' : Type) [AddCommGroup N'] [Fintype N'] [DecidableEq N'], ∀ (ι : N' →+ N) (π : N →+ N'), (∀ y, π (ι y) = y) → (∀ g ∈ AA.carrier, (fun x => g (ι (π x))) ∈ AA.carrier) → (∃ A' : HopfOrder (C := C) R N', A'.carrier = AA.carrier.map (LinearMap.funLeft R C (ι : N' → N))) ∧ (∀ h ∈ AA.carrier.map (LinearMap.funLeft R C (ι : N' → N)), (fun x => h (π x)) ∈ AA.carrier) ∧ ∀ K' : AddSubgroup N', GenAF p AA.carrier (K'.map ι) → GenAF p (AA.carrier.map (LinearMap.funLeft R C (ι : N' → N))) K' :=
  @PositivityTheory.HtPt.Re.ret_hopf

end GlobalTheory.CompanionTheory.Ar.GR
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderRetractRestrictionStatement
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hopf_order_retract_restriction : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ AA : HopfOrder (C := C) R N, ∀ (N' : Type) [AddCommGroup N'] [Fintype N'] [DecidableEq N'], ∀ (ι : N' →+ N) (π : N →+ N'), (∀ y, π (ι y) = y) → (∀ g ∈ AA.carrier, (fun x => g (ι (π x))) ∈ AA.carrier) → (∃ A' : HopfOrder (C := C) R N', A'.carrier = AA.carrier.map (LinearMap.funLeft R C (ι : N' → N))) ∧ (∀ h ∈ AA.carrier.map (LinearMap.funLeft R C (ι : N' → N)), (fun x => h (π x)) ∈ AA.carrier) ∧ ∀ K' : AddSubgroup N', GenAF p AA.carrier (K'.map ι) → GenAF p (AA.carrier.map (LinearMap.funLeft R C (ι : N' → N))) K' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.ret_hopf_factor | exact GlobalTheory.CompanionTheory.Ar.GR.ret_hopf_factor | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.ret_hopf_factor <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderSubgroupTranslationStatement
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stable_hopf_order_subgroup_translation : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable (F := F) AA.carrier → ∀ (K : Submodule F N) (t : N), t ∉ K → (∃ S : HopfOrder (C := C) R F, S.carrier = stepOrder AA.carrier K t ∧ FStable (F := F) S.carrier) ∧ stepOrder AA.carrier K t = stepOrderRes AA.carrier K t := by
  intro p _ C _ _ _ v R _ _ hv hp F _ _ _ _ f hf N _ _ _ _ AA hst K t ht
  classical
  have : Fintype (N ⧸ K) := Fintype.ofFinite _
  have hsurj : Function.Surjective K.mkQ := K.mkQ_surjective
  have hne : K.mkQ t ≠ 0 := by
    simpa [Submodule.Quotient.mk_eq_zero] using ht
  have heq := PositivityTheory.HtPt.Rc.stepOrder_eq AA.carrier K.mkQ hsurj t
  rw [K.ker_mkQ] at heq
  obtain ⟨AQ, hAQ⟩ := PositivityTheory.HtPt.Rc.exists_quo hv AA K.mkQ.toAddMonoidHom hsurj
  obtain ⟨S, hS⟩ := PositivityTheory.HtPt.Rc.exists_res hv AQ
    (LinearMap.toSpanSingleton F (N ⧸ K) (K.mkQ t)).toAddMonoidHom (PositivityTheory.HtPt.Rc.span_inj hne)
  refine ⟨⟨S, ?_, ?_⟩, ?_⟩
  · rw [hS, hAQ, heq]
    rfl
  · rw [hS, hAQ]
    intro a h hh
    obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hh
    refine Submodule.mem_map.mpr ⟨fun x => g (a • x), ?_, ?_⟩
    · have hg' : (fun x => g (K.mkQ x)) ∈ AA.carrier := hg
      change (fun x => g (a • K.mkQ x)) ∈ AA.carrier
      simpa only [map_smul] using hst a _ hg'
    · funext x
      change g (a • LinearMap.toSpanSingleton F (N ⧸ K) (K.mkQ t) x) =
        g (LinearMap.toSpanSingleton F (N ⧸ K) (K.mkQ t) (a • x))
      rw [map_smul]
  · unfold stepOrder stepOrderRes
    ext h
    constructor
    · intro hh
      obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hh
      exact ⟨g, hg.1, fun a k hk => hg.2 _ _ hk⟩
    · rintro ⟨g, hg, hgh⟩
      obtain ⟨g', hg', hg'e⟩ := PositivityTheory.HtPt.Rc.invres p C v R hv hp N AA K.toAddSubgroup
        (Submodule.span F {t} ⊔ K).toAddSubgroup
        (by
          intro x hx
          exact Submodule.mem_sup_right hx) g hg
        (by
          intro x hx k hk
          obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
          obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
          rw [add_assoc, hgh a _ (K.add_mem hz hk), hgh a z hz])
      refine Submodule.mem_map.mpr ⟨g', hg', ?_⟩
      funext a
      show g' (a • t) = h a
      rw [hg'e (a • t) (Submodule.mem_sup_left (Submodule.mem_span_singleton.mpr ⟨a, rfl⟩))]
      simpa using hgh a 0 K.zero_mem
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LineFibreHolds
namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem lineFibre_holds : ReciprocityTheory.ChartRestriction.G.AI.I4.LineFibreStatement :=
  GroundTheory.Heights₂.Heights.ForSecondHalf.LineFibre.full

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LineIsomorphismGroupoidLaws
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LineIsomorphismGroupoidLaws
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem lineIso_algebra : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)), IsMultiProjPrime P → (∀ a, IsLineIso P a a 1 1) ∧ (∀ a b f g, IsLineIso P a b f g → IsLineIso P b a g f) ∧ (∀ a b c f g f' g', IsLineIso P a b f g → IsLineIso P b c f' g' → IsLineIso P a c (f * f') (g * g')) ∧ (∀ a b a' b' f g f' g', IsLineIso P a b f g → IsLineIso P a' b' f' g' → IsLineIso P (a + a') (b + b') (f * f') (g * g')) ∧ ∀ (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) (P' : Ideal (MRing ι')), IsBlockMap κ v → imageZ v P' = P → ∀ a b f g, IsLineIso P a b f g → IsLineIso P' (pullDeg κ a) (pullDeg κ b) (rename v f) (rename v g) :=
  @PositivityTheory.UnitarySelfGeneration.i_algebra

end GlobalTheory.CompanionTheory.Ar.Cmp
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LineIsomorphismGroupoidLawsStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_isomorphism_groupoid_laws : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)), IsMultiProjPrime P → (∀ a, IsLineIso P a a 1 1) ∧ (∀ a b f g, IsLineIso P a b f g → IsLineIso P b a g f) ∧ (∀ a b c f g f' g', IsLineIso P a b f g → IsLineIso P b c f' g' → IsLineIso P a c (f * f') (g * g')) ∧ (∀ a b a' b' f g f' g', IsLineIso P a b f g → IsLineIso P a' b' f' g' → IsLineIso P (a + a') (b + b') (f * f') (g * g')) ∧ ∀ (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) (P' : Ideal (MRing ι')), IsBlockMap κ v → imageZ v P' = P → ∀ a b f g, IsLineIso P a b f g → IsLineIso P' (pullDeg κ a) (pullDeg κ b) (rename v f) (rename v g) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.lineIso_algebra | exact GlobalTheory.CompanionTheory.Ar.Cmp.lineIso_algebra | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.lineIso_algebra <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TorsionPointsHopfOrder
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TorsionPointsHopfOrder
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.torsion_points_hopf_order : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], ∀ (T : TorsRep G p) (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (pt : N → (sp (R₀ := R) R ⟶ G)), IsTorsPts G p pt → (∃ AA : HopfOrder (C := C) R N, AA.carrier = torsFun C T pt) ∧ (∀ a : T.A, (∀ φ : T.A →ₐ[R] R, φ a = 0) → a = 0) ∧ (∀ x, ∃! φ : T.A →ₐ[R] R, spMap φ ≫ T.y = pt x) ∧ (∀ φ : T.A →ₐ[R] R, ∃ x, spMap φ ≫ T.y = pt x) ∧ ∀ x : N, p • x = 0 := by
  first | exact @PositivityTheory.HtPt.Rf.tors_hopf | exact PositivityTheory.HtPt.Rf.tors_hopf
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TorsionPointsHopfOrderStatement
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_points_hopf_order : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], ∀ (T : TorsRep G p) (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (pt : N → (sp (R₀ := R) R ⟶ G)), IsTorsPts G p pt → (∃ AA : HopfOrder (C := C) R N, AA.carrier = torsFun C T pt) ∧ (∀ a : T.A, (∀ φ : T.A →ₐ[R] R, φ a = 0) → a = 0) ∧ (∀ x, ∃! φ : T.A →ₐ[R] R, spMap φ ≫ T.y = pt x) ∧ (∀ φ : T.A →ₐ[R] R, ∃ x, spMap φ ≫ T.y = pt x) ∧ ∀ x : N, p • x = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Relay.torsion_points_hopf_order | exact GlobalTheory.CompanionTheory.Relay.torsion_points_hopf_order | (intros; apply GlobalTheory.CompanionTheory.Relay.torsion_points_hopf_order <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderFundamentalIdeal
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderFundamentalIdeal
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
open PositivityTheory.HtPt.Rc ReciprocityTheory.PGsh.L2.SecondCohomologyLattice in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.stable_hopf_order_fundamental_ideal : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable (F := F) AA.carrier → ∀ σ : MulChar F R, IsFund p σ → (∀ χ : MulChar F R, ∃ r : NNReal, r ≠ 0 ∧ HasLen v R (OmType AA.carrier χ) r) ∧ ∀ r : ℕ → NNReal, (∀ m ∈ Finset.Icc 1 (p ^ f - 1), HasLen v R (OmType AA.carrier (σ ^ m)) (r m)) → HasLen v R (OmAA AA.carrier) (∏ m ∈ Finset.Icc 1 (p ^ f - 1), r m) := by
  intro p _ C _ _ _ v R _ _ hv hvp F _ _ _ _ f hf N _ _ _ _ AA hAA σ hσ
  have := hv.hom_inj.isDomain
  have hfg := fg_of_isLat AA.lat
  constructor
  · intro χ
    obtain ⟨-, -, cO, -, -, hcO0, -, -, hcO⟩ := lens p C v R hv hvp N (fun x => by
      rw [← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero, zero_smul]) AA
    obtain ⟨r, hr⟩ := exists_hasLen hv _ _ (eig_fg hv _ hfg χ) (sq_aug_fg hv _ hfg)
    refine ⟨r, ?_, hr⟩
    obtain ⟨s, hs0, hs⟩ := (len_ne_zero_iff hv hcO).1 hcO0
    refine (len_ne_zero_iff hv hr).2 ⟨s, hs0, fun m => ?_⟩
    obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    have h := hs (Submodule.Quotient.mk ⟨g, eig_le_aug _ χ g.2⟩)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h ⊢
    exact h
  · intro r hr
    obtain ⟨u, hu⟩ := exists_inv_card (F := F) hv p hvp
    have proj_mem (χ : MulChar F R) (S : Submodule R (N → C))
        (hS : FStable (F := F) S) {g : N → C} (hg : g ∈ S) : projL χ g ∈ S := by
      have heq : projL χ g = u • ∑ a : Fˣ, χ⁻¹ (a : F) • (fun x => g ((a : F) • x)) := by
        funext x
        rw [projL_apply, Pi.smul_apply, Finset.sum_apply, Algebra.smul_def, hu]
        exact congrArg _ (Finset.sum_congr rfl fun a _ => (Algebra.smul_def _ _).symm)
      rw [heq]
      exact S.smul_mem _ (S.sum_mem fun a _ => S.smul_mem _ (hS _ g hg))
    have proj_eig (χ : MulChar F R) {g : N → C} (hg : g ∈ augIdeal AA.carrier) :
        projL χ g ∈ eig AA.carrier χ := by
      rw [mem_aug] at hg
      refine ⟨proj_mem χ _ hAA hg.1, fun a x => ?_⟩
      by_cases ha : a = 0
      · rw [ha, zero_smul, MulChar.map_zero, map_zero, zero_mul, projL_apply]
        simp only [smul_zero, hg.2, mul_zero, Finset.sum_const_zero]
      · obtain ⟨a, rfl⟩ := isUnit_iff_ne_zero.2 ha
        rw [projL_apply, projL_apply, mul_left_comm, Finset.mul_sum Finset.univ _ (algebraMap R C _),
          ← Equiv.sum_comp (Equiv.mulRight a) (fun b : Fˣ => algebraMap R C (χ (a : F)) *
            (algebraMap R C (χ⁻¹ (b : F)) * g ((b : F) • x)))]
        congr 1
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Equiv.coe_mulRight, Units.val_mul, mul_smul, ← mul_assoc, ← map_mul, map_mul χ⁻¹,
          mul_left_comm, mul_inv_unit, mul_one]
    obtain ⟨hord, -, -, -, hsep⟩ := GlobalTheory.CompanionTheory.Ar.GR.FundGen.main p C v R hv hvp F f hf σ hσ
    have hn : p ^ f - 1 = Fintype.card Fˣ := by rw [Fintype.card_units, hf]
    rw [hn] at hr hord ⊢
    have hsum := sum_projL (C := C) (N := N) σ (fun a ha => by
      by_contra hne
      have := hsep a 1 (fun h => hne (Units.ext h))
      rw [ha, map_one, sub_self, map_zero, map_zero] at this
      exact zero_ne_one this)
    let Ψ : augIdeal AA.carrier →ₗ[R]
        ((i : Fin (Fintype.card Fˣ)) → OmType AA.carrier (σ ^ ((i : ℕ) + 1))) :=
      LinearMap.pi fun i => Submodule.mkQ _ ∘ₗ
        (projL (σ ^ ((i : ℕ) + 1))).restrict fun _ hg => proj_eig _ hg
    have hsurj : Function.Surjective Ψ := by
      intro y
      choose g hg using fun i => Submodule.Quotient.mk_surjective _ (y i)
      refine ⟨⟨∑ i, (g i : N → C), Submodule.sum_mem _ fun i _ => eig_le_aug _ _ (g i).2⟩, ?_⟩
      funext i
      rw [← hg i]
      refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
      show projL (σ ^ ((i : ℕ) + 1)) (∑ i, (g i : N → C)) = g i
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_eq_single i, projL_self _ (g i).2]
      · intro j _ hj
        refine projL_ne (fun h => hj ?_) (g j).2
        rw [pow_succ, pow_succ] at h
        exact Fin.ext (pow_injOn_Iio_orderOf (by rw [hord]; exact j.2) (by rw [hord]; exact i.2)
          (mul_right_cancel h).symm)
      · simp
    have hker : (sqIdeal (augIdeal AA.carrier)).comap (augIdeal AA.carrier).subtype =
        LinearMap.ker Ψ := by
      ext g
      rw [LinearMap.mem_ker, funext_iff]
      constructor
      · intro hg i
        have hstable : FStable (F := F) (sqIdeal (augIdeal AA.carrier)) :=
          fun a _ ha => sq_pull (LinearMap.lsmul F N a).toAddMonoidHom
            AA.carrier AA.carrier (hAA a) ha
        exact (Submodule.Quotient.mk_eq_zero _).2 (proj_mem _ _ hstable hg)
      · intro hg
        show (g : N → C) ∈ sqIdeal (augIdeal AA.carrier)
        rw [← hsum g]
        refine Submodule.sum_mem _ fun i _ => ?_
        have h1 : (Submodule.Quotient.mk
            (⟨projL (σ ^ ((i : ℕ) + 1)) (g : N → C), proj_eig _ g.2⟩ :
              eig AA.carrier (σ ^ ((i : ℕ) + 1))) :
            OmType AA.carrier (σ ^ ((i : ℕ) + 1))) = 0 := hg i
        rw [Submodule.Quotient.mk_eq_zero] at h1
        exact h1
    rw [prod_Icc_fin]
    exact ReciprocityTheory.PGsh.Up.hasLen_of_equiv ((Submodule.quotEquivOfEq _ _ hker).trans
      (Ψ.quotKerEquivOfSurjective hsurj)) (Tot.hasLen_pi _ _ fun i =>
        hr _ (Finset.mem_Icc.2 ⟨by omega, i.2⟩))
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderFundamentalIdealStatement
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stable_hopf_order_fundamental_ideal : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ σ : MulChar F R, IsFund p σ → (∀ χ : MulChar F R, ∃ r : NNReal, r ≠ 0 ∧ HasLen v R (OmType AA.carrier χ) r) ∧ ∀ r : ℕ → NNReal, (∀ m ∈ Finset.Icc 1 (p ^ f - 1), HasLen v R (OmType AA.carrier (σ ^ m)) (r m)) → HasLen v R (OmAA AA.carrier) (∏ m ∈ Finset.Icc 1 (p ^ f - 1), r m) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.stable_hopf_order_fundamental_ideal | exact GlobalTheory.CompanionTheory.Relay.stable_hopf_order_fundamental_ideal | (intros; apply GlobalTheory.CompanionTheory.Relay.stable_hopf_order_fundamental_ideal <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DivisibleGroupTowerCompatibilityStatement
section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.LevMapLev
noncomputable section

namespace PositivityTheory.HtPt.Gi

open TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup WithConv GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT Coalgebra Bialgebra
  PositivityTheory.HtPt.Twpdiv

def levMap {La : Type} [AddCommGroup La] (p n : ℕ) (φ : La →+ La) : LevGrp La p n →* LevGrp La p n :=
  AddMonoidHom.toMultiplicative (Submodule.mapQ _ _ φ.toIntLinearMap (by
    rintro _ ⟨b, rfl⟩
    exact ⟨φ b, (map_nsmul φ _ b).symm⟩)).toAddMonoidHom

theorem levMap_lev {La : Type} [AddCommGroup La] (p n : ℕ) (φ : La →+ La) (a : La) :
    levMap p n φ (lev p n a) = lev p n (φ a) := rfl

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {La : Type} [AddCommGroup La] [Module.Free ℤ La]
  [Module.Finite ℤ La] {L : Type} [AddCommGroup L] [Module O L] {X : OrdTower p O La L} {G : PDivGroup p O}
  (e : ∀ n, G.A n ≃ₐ[O] X.A n) {τ : La →+ G.Tate}

def evG (n : ℕ) (t : LevGrp La p n) : G.A n →ₐ[O] O := (evalAt (X.A n) t).comp (e n).toAlgHom

omit [Fact p.Prime] [Module.Free ℤ La] [Module.Finite ℤ La] in
theorem evG_apply (n : ℕ) (t : LevGrp La p n) (g : G.A n) : evG e n t g = (e n g).1 t := rfl

omit [Fact p.Prime] [Module.Free ℤ La] [Module.Finite ℤ La] in
theorem sepG (n : ℕ) : Sep (evG e n) := fun _ _ h => (e n).injective (Subtype.ext (funext h))

variable {e}

omit [Module.Free ℤ La] [Module.Finite ℤ La] in
theorem evG_lev (hre : X.Realises G e τ) (n : ℕ) (a : La) : evG e n (lev p n a) = (τ a).pt n :=
  AlgHom.ext fun g => (hre.pt a n g).symm

omit [Module.Free ℤ La] [Module.Finite ℤ La] in
theorem evG_one (hre : X.Realises G e τ) (n : ℕ) (g : G.A n) : evG e n 1 g = counit (R := O) g := by
  rw [← lev_zero, evG_lev hre, map_zero]
  rfl

omit [Module.Free ℤ La] [Module.Finite ℤ La] in
theorem evG_mul (hre : X.Realises G e τ) (n : ℕ) (s t : LevGrp La p n) (g : G.A n) :
    pair (evG e n s) (evG e n t) (comul (R := O) g) = evG e n (s * t) g := by
  obtain ⟨a, rfl⟩ := lev_surjective p n s
  obtain ⟨b, rfl⟩ := lev_surjective p n t
  rw [← lev_add, evG_lev hre, evG_lev hre, evG_lev hre, map_add (f := _)]
  exact (AlgHom.convMul_apply ((τ a).conv n) ((τ b).conv n) g).symm

def pullA {φ : La →+ La} {dφ : L →ₗ[O] L} (h : X.Acts φ dφ) (n : ℕ) : G.A n →ₐ[O] G.A n :=
  Ord.liftTo (evG e n) (sepG e n) (fun t => evG e n (levMap p n φ t)) fun g =>
    ⟨(e n).symm ⟨fun t => (e n g).1 (levMap p n φ t), (h n (e n g).1 _ fun _ => rfl).1 (e n g).2⟩, fun t => by
      rw [evG_apply, AlgEquiv.apply_symm_apply]; rfl⟩

omit [Fact p.Prime] [Module.Free ℤ La] [Module.Finite ℤ La] in
theorem evG_pullA {φ : La →+ La} {dφ : L →ₗ[O] L} (h : X.Acts φ dφ) (n : ℕ) (t : LevGrp La p n) :
    (evG e n t).comp (pullA (e := e) h n) = evG e n (levMap p n φ t) := Ord.ev_liftTo _ _ _ _ t

omit [Fact p.Prime] [Module.Free ℤ La] [Module.Finite ℤ La] in
theorem evG_pullA' {φ : La →+ La} {dφ : L →ₗ[O] L} (h : X.Acts φ dφ) (n : ℕ) (t : LevGrp La p n) (g : G.A n) :
    evG e n t (pullA (e := e) h n g) = evG e n (levMap p n φ t) g := DFunLike.congr_fun (evG_pullA h n t) g

def pullB (hre : X.Realises G e τ) {φ : La →+ La} {dφ : L →ₗ[O] L} (h : X.Acts φ dφ) (n : ℕ) :
    G.A n →ₐc[O] G.A n :=
  BialgHom.ofAlgHom (pullA (e := e) h n)
    (AlgHom.ext fun g => by
      change counit (R := O) (pullA (e := e) h n g) = counit (R := O) g
      rw [← evG_one hre, ← evG_one hre, evG_pullA', map_one])
    (AlgHom.ext fun g => (sepG e n).pair (sepG e n) _ _ fun z => by
      change pair _ _ (Algebra.TensorProduct.map _ _ (comul (R := O) g)) =
        pair _ _ (comul (R := O) (pullA (e := e) h n g))
      rw [pair_map, evG_pullA, evG_pullA, evG_mul hre, evG_mul hre, evG_pullA', map_mul])

def endG (hre : X.Realises G e τ) {φ : La →+ La} {dφ : L →ₗ[O] L} (h : X.Acts φ dφ) : G ⟶ G where
  app := pullB hre h
  comm n := BialgHom.ext fun g => sepG e n _ _ fun t => by
    obtain ⟨a, rfl⟩ := lev_surjective p n t
    change (e n (G.res n (pullA (e := e) h (n + 1) g))).1 _ = evG e n _ (pullA (e := e) h n (G.res n g))
    rw [hre.res, evG_pullA', levMap_lev, evG_apply, hre.res, ← evG_apply, evG_pullA', levMap_lev, map_nsmul,
      evG_apply]

end PositivityTheory.HtPt.Gi

end

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

theorem PositivityTheory.HtPt.Gi.tower_end : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (L : Type) [AddCommGroup L] [Module O L] (X : OrdTower p O La L) (G : PDivGroup p O) (e : ∀ n, G.A n ≃ₐ[O] X.A n) (τ : La →+ G.Tate) (hre : X.Realises G e τ), (∀ (φ : La →+ La) (dφ : L →ₗ[O] L), X.Acts φ dφ → ∃ f : G ⟶ G, (∀ a, tateMap G G O f (τ a) = τ (φ a)) ∧ ∀ n (g : G.A n) (a : La), (e n (f.app n g)).1 (lev p n a) = (e n g).1 (lev p n (φ a))) ∧ ∀ (H : PDivGroup p O) (f f' : G ⟶ H), (∀ a, tateMap G H O f (τ a) = tateMap G H O f' (τ a)) → f = f' := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ La _ _ _ L _ _ X G e τ hre
  refine ⟨fun φ dφ h => ⟨PositivityTheory.HtPt.Gi.endG hre h, fun a => TateOver.ext (funext fun n => AlgHom.ext fun g => ?_),
    fun n g a => PositivityTheory.HtPt.Gi.evG_pullA' h n _ g⟩, fun H f f' hf =>
      PDivGroup.Hom.ext (funext fun n => BialgHom.ext fun g =>
        PositivityTheory.HtPt.Gi.sepG e n _ _ fun t => ?_)⟩
  · rw [tateMap_pt, ← PositivityTheory.HtPt.Gi.evG_lev hre, ← PositivityTheory.HtPt.Gi.evG_lev hre]
    exact PositivityTheory.HtPt.Gi.evG_pullA' h n _ g
  · obtain ⟨a, rfl⟩ := PositivityTheory.HtPt.Twpdiv.lev_surjective p n t
    rw [PositivityTheory.HtPt.Gi.evG_lev hre, ← tateMap_pt, ← tateMap_pt, hf]
end

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi
open Coalgebra Bialgebra PositivityTheory.HtPt.Twpdiv in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisible_group_tower_compatibility :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
      (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C]
      (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O)
      (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La]
      (L : Type) [AddCommGroup L] [Module O L] (X : OrdTower p O La L)
      (G : PDivGroup p O) (e : ∀ n, G.A n ≃ₐ[O] X.A n) (τ : La →+ G.Tate)
      (hre : X.Realises G e τ),
      (∀ (φ : La →+ La) (dφ : L →ₗ[O] L), X.Acts φ dφ → ∃ f : G ⟶ G,
        (∀ a, tateMap G G O f (τ a) = τ (φ a)) ∧ ∀ n (g : G.A n) (a : La),
          (e n (f.app n g)).1 (lev p n a) = (e n g).1 (lev p n (φ a))) ∧
      ∀ (H : PDivGroup p O) (f f' : G ⟶ H),
        (∀ a, tateMap G H O f (τ a) = tateMap G H O f' (τ a)) → f = f' := by
  intro p _ C _ _ _ v O _ _ _ hv hp hO La _ _ _ L _ _ X G e τ hre
  let ev (n : ℕ) (t : LevGrp La p n) : G.A n →ₐ[O] O := (evalAt (X.A n) t).comp (e n).toAlgHom
  have ev_apply (n : ℕ) (t : LevGrp La p n) (g : G.A n) : ev n t g = (e n g).1 t := rfl
  have ev_sep (n : ℕ) : PositivityTheory.HtPt.Twpdiv.Sep (ev n) :=
    fun _ _ h => (e n).injective (Subtype.ext (funext h))
  have ev_lev (n : ℕ) (a : La) : ev n (lev p n a) = (τ a).pt n :=
    AlgHom.ext fun g => (hre.pt a n g).symm
  have tate_pt {H : PDivGroup p O} (f : G ⟶ H) (a : La) (n : ℕ) (g : H.A n) :
      (tateMap G H O f (τ a)).pt n g = (τ a).pt n (f.app n g) := rfl
  constructor
  · intro φ dφ h
    let levMap (n : ℕ) : LevGrp La p n →* LevGrp La p n :=
      AddMonoidHom.toMultiplicative (Submodule.mapQ _ _ φ.toIntLinearMap (by
        rintro _ ⟨b, rfl⟩
        exact ⟨φ b, (map_nsmul φ _ b).symm⟩)).toAddMonoidHom
    have levMap_lev (n : ℕ) (a : La) : levMap n (lev p n a) = lev p n (φ a) := rfl
    have liftable (n : ℕ) (g : G.A n) : ∃ u : G.A n, ∀ t, ev n t u = ev n (levMap n t) g := by
      let pulled (t : LevGrp La p n) : O := (e n g).1 (levMap n t)
      have hpulled : pulled ∈ X.A n :=
        (h n (e n g).1 pulled fun a => congrArg (e n g).1 (levMap_lev n a)).1 (e n g).2
      let u : X.A n := ⟨pulled, hpulled⟩
      refine ⟨(e n).symm u, fun t => ?_⟩
      rw [ev_apply, AlgEquiv.apply_symm_apply, ev_apply]
    let pull (n : ℕ) : G.A n →ₐ[O] G.A n :=
      Ord.liftTo (ev n) (ev_sep n) (fun t => ev n (levMap n t)) (liftable n)
    have ev_pull (n : ℕ) (t : LevGrp La p n) : (ev n t).comp (pull n) = ev n (levMap n t) :=
      Ord.ev_liftTo _ _ _ _ t
    have pull_apply (n : ℕ) (t : LevGrp La p n) (g : G.A n) :
        ev n t (pull n g) = ev n (levMap n t) g := DFunLike.congr_fun (ev_pull n t) g
    have pull_lev (n : ℕ) (a : La) (g : G.A n) :
        ev n (lev p n a) (pull n g) = ev n (lev p n (φ a)) g := by
      rw [pull_apply, levMap_lev]
    have ev_one (n : ℕ) (g : G.A n) : ev n 1 g = counit (R := O) g := by
      rw [← lev_zero p n, ev_lev, map_zero]
      rfl
    have ev_mul (n : ℕ) (s t : LevGrp La p n) (g : G.A n) :
        pair (ev n s) (ev n t) (comul (R := O) g) = ev n (s * t) g := by
      obtain ⟨a, rfl⟩ := lev_surjective p n s
      obtain ⟨b, rfl⟩ := lev_surjective p n t
      rw [← lev_add, ev_lev, ev_lev, ev_lev, map_add]
      exact (AlgHom.convMul_apply ((τ a).conv n) ((τ b).conv n) g).symm
    let app (n : ℕ) : G.A n →ₐc[O] G.A n :=
      BialgHom.ofAlgHom (pull n)
        (AlgHom.ext fun g => by
          change counit (R := O) (pull n g) = counit (R := O) g
          rw [← ev_one, ← ev_one, pull_apply, map_one])
        (AlgHom.ext fun g => (ev_sep n).pair (ev_sep n) _ _ fun z => by
          change pair (ev n z.1) (ev n z.2) (Algebra.TensorProduct.map _ _ (comul (R := O) g)) =
            pair (ev n z.1) (ev n z.2) (comul (R := O) (pull n g))
          rw [pair_map, ev_pull, ev_pull, ev_mul, ev_mul, pull_apply, map_mul])
    let f : G ⟶ G :=
      { app := app
        comm n := BialgHom.ext fun g => ev_sep n _ _ fun t => by
          obtain ⟨a, rfl⟩ := lev_surjective p n t
          calc
            ev n (lev p n a) (G.res n (pull (n + 1) g)) =
                ev (n + 1) (lev p (n + 1) (p • a)) (pull (n + 1) g) := hre.res n _ a
            _ = ev (n + 1) (lev p (n + 1) (φ (p • a))) g := pull_lev (n + 1) (p • a) g
            _ = ev (n + 1) (lev p (n + 1) (p • φ a)) g := by rw [map_nsmul]
            _ = ev n (lev p n (φ a)) (G.res n g) := (hre.res n g (φ a)).symm
            _ = ev n (lev p n a) (pull n (G.res n g)) := (pull_lev n a (G.res n g)).symm }
    refine ⟨f, fun a => TateOver.ext (funext fun n => AlgHom.ext fun g => ?_), fun n g a => pull_lev n a g⟩
    rw [tate_pt, ← ev_lev, ← ev_lev]
    exact pull_lev n a g
  · intro H f f' hf
    refine GlobalTheory.PDivGroup.Hom.ext (funext fun n => BialgHom.ext fun g => ev_sep n _ _ fun t => ?_)
    obtain ⟨a, rfl⟩ := lev_surjective p n t
    rw [ev_lev, ← tate_pt, ← tate_pt, hf]
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CmTypePolynomialVanishingCriterion
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CmTypePolynomialVanishingCriterion
open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExG.Block

theorem sum_eq_sum_subtype {α β : Type} [Fintype α] [AddCommMonoid β] (D : α → Prop)
    [Fintype {s // D s}] (G : α → β) (h : ∀ s, ¬ D s → G s = 0) :
    ∑ s, G s = ∑ s : {s // D s}, G s.1 := by
  classical
  rw [← Finset.sum_filter_of_ne (p := D) (fun x _ hx => by_contra fun hD => hx (h x hD))]
  exact Finset.sum_subtype _ (fun x => by simp) G

section

variable {E : Type} [Field E] [NumberField E] {C : Type} [Field C] {w : Valuation C ℝ≥0}

theorem mem_freeLattice {S : Type} {a : S → w.valuationSubring} {r : ℕ} {x : S → Fin r → C} :
    x ∈ freeLattice a r ↔ ∀ i, ∃ f : Polynomial w.valuationSubring, ∀ s,
      x s i = ((f.eval (a s) : w.valuationSubring) : C) := Iff.rfl

def valSpan (emb : (E →+* C) → (𝓞 E →+* w.valuationSubring)) :
    Submodule w.valuationSubring ((E →+* C) → w.valuationSubring) :=
  Submodule.span w.valuationSubring (Set.range fun a : 𝓞 E => fun s => emb s a)

theorem mul_mem_valSpan (emb : (E →+* C) → (𝓞 E →+* w.valuationSubring))
    {f g : (E →+* C) → w.valuationSubring} (hf : f ∈ valSpan emb) (hg : g ∈ valSpan emb) :
    f * g ∈ valSpan emb := by
  unfold valSpan at hf hg ⊢
  induction hf using Submodule.span_induction with
  | mem x h =>
    obtain ⟨a, rfl⟩ := h
    induction hg using Submodule.span_induction with
    | mem y h =>
      obtain ⟨b, rfl⟩ := h
      exact Submodule.subset_span ⟨a * b, by funext s; simp⟩
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hy
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

variable {M : Type} [AddCommGroup M] [Module C M] [Module w.valuationSubring M]
  [IsScalarTower w.valuationSubring C M] {ρ : 𝓞 E →+* Module.End C M}
  {X : Submodule w.valuationSubring M} {N : ℕ} {t : Fin N → M}

theorem rho_mem (h : HT.IsFreeOn ρ X t) (a : 𝓞 E) (j : Fin N) : ρ a (t j) ∈ X := by
  have e := congrArg (fun u => ρ u (t j)) ((RingOfIntegers.basis E).sum_repr a)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply] at e
  rw [← e]
  refine sum_mem fun k _ => zsmul_mem ?_ _
  rw [h.2.2]
  exact Submodule.subset_span ⟨(j, k), rfl⟩

theorem eigCoord_mem (s : E →+* C) (v : Fin N → C) : eigCoord ρ t s v ∈ HT.eigSp ρ s := by
  rw [eigCoord_apply]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (HT.LatBasic.eigProj_mem ρ s _)

theorem exists_coord (emb : (E →+* C) → (𝓞 E →+* w.valuationSubring))
    (hemb : ∀ s (a : 𝓞 E), ((emb s a : w.valuationSubring) : C) = s (a : E))
    (h : HT.IsFreeOn ρ X t) {y : M} (hy : y ∈ X) :
    ∃ F : Fin N → (E →+* C) → w.valuationSubring, (∀ j, F j ∈ valSpan emb) ∧
      ∀ s, HT.eigProj ρ s y = ∑ j, ((F j s : w.valuationSubring) : C) • HT.eigProj ρ s (t j) := by
  classical
  rw [h.2.2] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨j, k⟩, rfl⟩ := hx
    refine ⟨fun i s => if i = j then emb s (RingOfIntegers.basis E k) else 0, fun i => ?_,
      fun s => ?_⟩
    · by_cases hij : i = j
      · simp only [hij, if_true]
        exact Submodule.subset_span ⟨_, rfl⟩
      · simp only [hij, if_false]
        exact zero_mem (valSpan emb)
    · rw [HodgeDeterminantLattice.eigProj_act, Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (by simp)]
      simp [hemb]
  | zero => exact ⟨0, fun _ => zero_mem _, fun s => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨F, hF, e⟩ := hx
    obtain ⟨G, hG, e'⟩ := hy
    refine ⟨F + G, fun j => add_mem (hF j) (hG j), fun s => ?_⟩
    simp [e s, e' s, add_smul, Finset.sum_add_distrib]
  | smul c x _ hx =>
    obtain ⟨F, hF, e⟩ := hx
    refine ⟨c • F, fun j => Submodule.smul_mem _ c (hF j), fun s => ?_⟩
    rw [← algebraMap_smul C c x, map_smul, e s, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul]
    rfl

theorem sum_smul_mem [CharZero C] [Fintype (E →+* C)]
    (emb : (E →+* C) → (𝓞 E →+* w.valuationSubring))
    (hemb : ∀ s (a : 𝓞 E), ((emb s a : w.valuationSubring) : C) = s (a : E))
    (hcard : Fintype.card (E →+* C) = Module.finrank ℚ E)
    (h : HT.IsFreeOn ρ X t) (j : Fin N) {F : (E →+* C) → w.valuationSubring}
    (hF : F ∈ valSpan emb) :
    ∑ s, ((F s : w.valuationSubring) : C) • HT.eigProj ρ s (t j) ∈ X := by
  unfold valSpan at hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    have e : ∑ s : E →+* C, ((emb s a : w.valuationSubring) : C) • HT.eigProj ρ s (t j) =
        ρ a (t j) := by
      have h1 := congrArg (fun T : Module.End C M => T (ρ a (t j)))
        (HT.sum_eigProj_eq_one C M E ρ hcard)
      simp only [LinearMap.sum_apply, HodgeDeterminantLattice.eigProj_act, Module.End.one_apply] at h1
      simpa only [hemb] using h1
    simpa only [e] using rho_mem h a j
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [Pi.add_apply, AddMemClass.coe_add, add_smul, Finset.sum_add_distrib]
    exact add_mem hx hy
  | smul c x _ hx =>
    have e : ∑ s : E →+* C, (((c • x) s : w.valuationSubring) : C) • HT.eigProj ρ s (t j) =
        c • ∑ s : E →+* C, ((x s : w.valuationSubring) : C) • HT.eigProj ρ s (t j) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [← algebraMap_smul C c (((x s : w.valuationSubring) : C) • HT.eigProj ρ s (t j)), smul_smul]
      rfl
    rw [e]
    exact Submodule.smul_mem _ c hx

end

theorem block_freeLattice : ∀ (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [CharZero C] (w : Valuation C ℝ≥0) [Fintype (E →+* C)] (emb : (E →+* C) → (𝓞 E →+* w.valuationSubring)), (∀ s (a : 𝓞 E), ((emb s a : w.valuationSubring) : C) = s (a : E)) → Fintype.card (E →+* C) = Module.finrank ℚ E → ∀ (D : (E →+* C) → Prop) (π : 𝓞 E), (∀ f : (E →+* C) → w.valuationSubring, (∀ s, ¬ D s → f s = 0) → ((∃ g : Polynomial w.valuationSubring, ∀ s, D s → f s = g.eval (emb s π)) ↔ f ∈ Submodule.span w.valuationSubring (Set.range fun a : 𝓞 E => fun s => emb s a))) → ∀ (M : Type) [AddCommGroup M] [Module C M] [Module w.valuationSubring M] [IsScalarTower w.valuationSubring C M] (ρ : 𝓞 E →+* Module.End C M) (X : Submodule w.valuationSubring M) (N : ℕ) (t : Fin N → M), HT.IsFreeOn ρ X t → ∀ [Fintype {s // D s}], (∀ f : {s // D s} → Fin N → C, (∑ s, eigCoord ρ t s.1 (f s)) ∈ X ↔ f ∈ freeLattice (fun s : {s // D s} => emb s.1 π) N) ∧ (∀ y ∈ X, ∃ f ∈ freeLattice (fun s : {s // D s} => emb s.1 π) N, ∀ s, HT.eigProj ρ s.1 y = eigCoord ρ t s.1 (f s)) := by
  intro E _ _ C _ _ w _ emb hemb hcard D π H M _ _ _ _ ρ X N t hfree _
  classical
  have hind : (fun s => if D s then (1 : w.valuationSubring) else 0) ∈ valSpan emb :=
    (H _ (fun s hs => if_neg hs)).1 ⟨1, fun s hs => by simp [hs]⟩
  have hpoly : ∀ F ∈ valSpan emb, ∃ g : Polynomial w.valuationSubring,
      ∀ s, D s → F s = g.eval (emb s π) := by
    intro F hF
    have hm := mul_mem_valSpan emb hind hF
    obtain ⟨g, hg⟩ := (H _ (fun s hs => by simp [hs])).2 hm
    exact ⟨g, fun s hs => by simpa [hs] using hg s hs⟩
  refine ⟨fun f => ⟨fun hx => ?_, fun hf => ?_⟩, fun y hy => ?_⟩
  · obtain ⟨F, hF, e⟩ := exists_coord emb hemb hfree hx
    have hD : ∀ s : {s // D s}, HT.eigProj ρ s.1 (∑ s, eigCoord ρ t s.1 (f s)) =
        eigCoord ρ t s.1 (f s) := by
      intro s
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_eq_single s]
      · exact HT.LatBasic.eigProj_of_mem (eigCoord_mem _ _)
      · intro s' _ hne
        exact HT.LatBasic.eigProj_of_ne (fun e => hne (Subtype.ext e.symm)) (eigCoord_mem _ _)
      · simp
    have hnD : ∀ s, ¬ D s → HT.eigProj ρ s (∑ s, eigCoord ρ t s.1 (f s)) = 0 := by
      intro s hs
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_eq_zero fun s' _ =>
        HT.LatBasic.eigProj_of_ne (fun e : s = s'.1 => hs (by rw [e]; exact s'.2)) (eigCoord_mem _ _)
    have hF0 : ∀ j s, ¬ D s → F j s = 0 := by
      intro j s hs
      have h1 := Fintype.linearIndependent_iff.1 (HodgeDeterminantLattice.linearIndependent_eigProj s hfree)
        (fun j => ((F j s : w.valuationSubring) : C)) (by rw [← e s, hnD s hs]) j
      exact Subtype.ext h1
    have hcoord : ∀ (s : {s // D s}) j, f s j = ((F j s.1 : w.valuationSubring) : C) := by
      intro s j
      have h0 := (hD s).symm.trans (e s.1)
      rw [eigCoord_apply] at h0
      have h1 := Fintype.linearIndependent_iff.1 (HodgeDeterminantLattice.linearIndependent_eigProj s.1 hfree)
        (fun j => f s j - ((F j s.1 : w.valuationSubring) : C))
        (by simp only [sub_smul, Finset.sum_sub_distrib, h0, sub_self]) j
      exact sub_eq_zero.1 h1
    refine mem_freeLattice.2 fun j => ?_
    obtain ⟨g, hg⟩ := (H (F j) (hF0 j)).2 (hF j)
    exact ⟨g, fun s => by rw [hcoord s j, hg s.1 s.2]⟩
  · choose g hg using mem_freeLattice.1 hf
    let F : Fin N → (E →+* C) → w.valuationSubring :=
      fun j s => if D s then (g j).eval (emb s π) else 0
    have hFm : ∀ j, F j ∈ valSpan emb := fun j =>
      (H (F j) (fun s hs => if_neg hs)).1 ⟨g j, fun s hs => if_pos hs⟩
    have key : ∑ j, ∑ s, ((F j s : w.valuationSubring) : C) • HT.eigProj ρ s (t j) ∈ X :=
      sum_mem fun j _ => sum_smul_mem emb hemb hcard hfree j (hFm j)
    have e : ∑ s, eigCoord ρ t s.1 (f s) =
        ∑ j, ∑ s, ((F j s : w.valuationSubring) : C) • HT.eigProj ρ s (t j) := by
      simp only [eigCoord_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [sum_eq_sum_subtype D _ (fun s hs => by simp [F, hs])]
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [F, if_pos s.2, hg j s]
    rw [e]
    exact key
  · obtain ⟨F, hF, e⟩ := exists_coord emb hemb hfree hy
    refine ⟨fun s j => ((F j s.1 : w.valuationSubring) : C), mem_freeLattice.2 fun j => ?_,
      fun s => ?_⟩
    · obtain ⟨g, hg⟩ := hpoly _ (hF j)
      exact ⟨g, fun s => by rw [hg s.1 s.2]⟩
    · rw [e, eigCoord_apply]

end GlobalTheory.CompanionTheory.Ar.Flat.ExG.Block
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CmTypePolynomialVanishingCriterionStatement
open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_type_polynomial_vanishing_criterion : ∀ (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [CharZero C] (w : Valuation C ℝ≥0) [Fintype (E →+* C)] (emb : (E →+* C) → (𝓞 E →+* w.valuationSubring)), (∀ s (a : 𝓞 E), ((emb s a : w.valuationSubring) : C) = s (a : E)) → Fintype.card (E →+* C) = Module.finrank ℚ E → ∀ (D : (E →+* C) → Prop) (π : 𝓞 E), (∀ f : (E →+* C) → w.valuationSubring, (∀ s, ¬ D s → f s = 0) → ((∃ g : Polynomial w.valuationSubring, ∀ s, D s → f s = g.eval (emb s π)) ↔ f ∈ Submodule.span w.valuationSubring (Set.range fun a : 𝓞 E => fun s => emb s a))) → ∀ (M : Type) [AddCommGroup M] [Module C M] [Module w.valuationSubring M] [IsScalarTower w.valuationSubring C M] (ρ : 𝓞 E →+* Module.End C M) (X : Submodule w.valuationSubring M) (N : ℕ) (t : Fin N → M), HT.IsFreeOn ρ X t → ∀ [Fintype {s // D s}], (∀ f : {s // D s} → Fin N → C, (∑ s, eigCoord ρ t s.1 (f s)) ∈ X ↔ f ∈ freeLattice (fun s : {s // D s} => emb s.1 π) N) ∧ (∀ y ∈ X, ∃ f ∈ freeLattice (fun s : {s // D s} => emb s.1 π) N, ∀ s, HT.eigProj ρ s.1 y = eigCoord ρ t s.1 (f s)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.ExG.Block.block_freeLattice | exact GlobalTheory.CompanionTheory.Ar.Flat.ExG.Block.block_freeLattice | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.ExG.Block.block_freeLattice <;> assumption)
end
end
