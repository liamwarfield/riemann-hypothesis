module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LeadMinor
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueSemilinear

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XChartNoethFrac
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace PositivityTheory.Xgn.A_chart_noeth_frac

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type}

theorem ratio_eq [DecidableEq K] (x : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : mseg x c ≠ 0) (k : K) (i : ι k) :
    mseg x (Function.update c k i) / mseg x c = x ⟨k, i⟩ / x ⟨k, c k⟩ := by
  have h1 : mseg x (Function.update c k i) = x ⟨k, i⟩ * ∏ l ∈ Finset.univ.erase k, x ⟨l, c l⟩ := by
    unfold mseg
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k), Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun l hl => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
  have h2 : mseg x c = x ⟨k, c k⟩ * ∏ l ∈ Finset.univ.erase k, x ⟨l, c l⟩ := by
    unfold mseg
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
  rw [h2] at hc
  rw [h1, h2, mul_div_mul_right _ _ (right_ne_zero_of_mul hc)]

theorem mseg_join {K' : Type} [Fintype K'] {ι' : K' → Type} (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω)
    (c : ∀ k : K ⊕ K', Sum.elim ι ι' k) :
    mseg (joinCoord x z) c = mseg x (restrictChart c) * mseg z (fun k => c (.inr k)) := by
  simp only [mseg, Fintype.prod_sum_type]
  rfl

def comb {K' : Type} {ι' : K' → Type} (t : ∀ k, ι k) (c : ∀ k : K ⊕ K', Sum.elim ι ι' k) :
    ∀ k : K ⊕ K', Sum.elim ι ι' k
  | .inl k => t k
  | .inr k => c (.inr k)

variable [∀ k, Fintype (ι k)]

theorem fnField_le [DecidableEq K] (x : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : mseg x c ≠ 0) :
    fnField O x ≤ Subfield.closure (chartRing O (mseg x) c : Set Ω) := by
  have hk : ∀ k, x ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc k (Finset.mem_univ k)
  have hm : ∀ k (i : ι k), x ⟨k, i⟩ / x ⟨k, c k⟩ ∈ Subfield.closure (chartRing O (mseg x) c : Set Ω) := by
    intro k i
    rw [← ratio_eq x c hc k i]
    exact Subfield.subset_closure (ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing (o := O) _ _ _)
  unfold fnField
  rw [Subfield.closure_le]
  rintro _ (⟨a, rfl⟩ | ⟨⟨k, i, j⟩, rfl⟩)
  · exact Subfield.subset_closure (Subalgebra.algebraMap_mem _ a)
  · have h : x ⟨k, i⟩ / x ⟨k, j⟩ = (x ⟨k, i⟩ / x ⟨k, c k⟩) / (x ⟨k, j⟩ / x ⟨k, c k⟩) := by
      rw [div_div_div_cancel_right₀ (hk k)]
    show x ⟨k, i⟩ / x ⟨k, j⟩ ∈ Subfield.closure (chartRing O (mseg x) c : Set Ω)
    rw [h]
    exact div_mem (hm k i) (hm k j)

theorem isFractionRing_of_closure (R : Subalgebra O Ω) (h : Subfield.closure (R : Set Ω) = ⊤) :
    IsFractionRing R Ω := by
  refine IsFractionRing.of_field R Ω fun z => ?_
  have hz : z ∈ Subfield.closure (R : Set Ω) := h ▸ Subfield.mem_top z
  obtain ⟨a, ha, b, hb, rfl⟩ := Subfield.mem_closure_iff.1 hz
  have e : Subring.closure (R : Set Ω) = R.toSubring := Subring.closure_eq R.toSubring
  rw [e] at ha hb
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, rfl⟩

end PositivityTheory.Xgn.A_chart_noeth_frac

open PositivityTheory.Xgn.A_chart_noeth_frac in
theorem PositivityTheory.Xgn.t_chart_noeth_frac : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω), (∀ c, IsNoetherianRing (chartRing O (mseg x) c)) ∧ (fnField O x = ⊤ → ∀ c, mseg x c ≠ 0 → IsFractionRing (chartRing O (mseg x) c) Ω) ∧ ∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω), (fnField O x = ⊤ → fnField O (joinCoord x z) = ⊤) ∧ ∀ c, mseg (joinCoord x z) c ≠ 0 → mseg x (restrictChart c) ≠ 0 ∧ (chartRing O (mseg x) (restrictChart c)) ≤ (chartRing O (mseg (joinCoord x z)) c) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x
  refine ⟨fun c => isNoetherianRing_of_fg (Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩), fun h c hc => ?_,
    fun K' _ _ ι' _ z => ⟨fun h => ?_, fun c hc => ?_⟩⟩
  · exact isFractionRing_of_closure _ (top_le_iff.1 (h ▸ fnField_le x c hc))
  · rw [eq_top_iff, ← h]
    unfold fnField
    refine Subfield.closure_mono (Set.union_subset_union_right _ ?_)
    rintro _ ⟨⟨k, i, j⟩, rfl⟩
    exact ⟨⟨.inl k, i, j⟩, rfl⟩
  · have hc' := hc
    rw [mseg_join] at hc'
    refine ⟨left_ne_zero_of_mul hc', ?_⟩
    unfold chartRing
    apply Algebra.adjoin_le
    rintro _ ⟨t, rfl⟩
    have h : mseg x t / mseg x (restrictChart c) =
        mseg (joinCoord x z) (comb t c) / mseg (joinCoord x z) c := by
      rw [mseg_join x z (comb t c), mseg_join x z c]
      exact (mul_div_mul_right _ _ (right_ne_zero_of_mul hc')).symm
    simp only
    rw [h]
    exact ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing (o := O) _ _ _
end

section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XBundleOfFamily
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

theorem PositivityTheory.Xgn.t_bundle_of_family : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V], (∀ Γ : (∀ k, ι k) → AddSubgroup V, IsLatFamily O x Γ → (∀ s, mseg x s ≠ 0 → LocFree (chartRing O (mseg x) s) N (Γ s)) → ∃ E : ChartBundle O (mseg x) N V, ∀ s, mseg x s ≠ 0 → E.lat s = Γ s) ∧ ∀ E : ChartBundle O (mseg x) N V, IsLatFamily O x E.lat ∧ ∀ s, mseg x s ≠ 0 → LocFree (chartRing O (mseg x) s) N (E.lat s) := by
  classical
  intro O _ Ω _ _ K _ _ ι _ x N V _ _
  refine ⟨fun Γ hfam hloc => ?_, fun E => ⟨⟨fun s _ => E.stable s, fun s t hs ht => E.overlap s t hs ht⟩, fun s hs => ⟨E.stable s, E.frame s hs⟩⟩⟩
  refine ⟨{ lat := fun s => if mseg x s = 0 then ⊥ else Γ s
            stable := ?_
            frame := ?_
            overlap := ?_ }, ?_⟩
  · intro s a ha e he
    by_cases h : mseg x s = 0
    · simp only [h, if_true, AddSubgroup.mem_bot] at he ⊢
      rw [he, smul_zero]
    · simp only [h, if_false] at he ⊢
      exact hfam.1 s h a ha e he
  · intro s hs
    simp only [hs, if_false]
    exact (hloc s hs).2
  · intro s t hs ht e he
    simp only [hs, ht, if_false] at he ⊢
    exact hfam.2 s t hs ht e he
  · intro s hs
    simp only [hs, if_false]
end

section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XPullLine
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace PositivityTheory.Xgn.A_pull_line
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (restrictChart)
open ReciprocityTheory.ChartRestriction.G.Geo (div_mem_chartRing)

variable {O : Type} [CommRing O] {Ω Ω₁ : Type} [Field Ω] [Field Ω₁] [Algebra O Ω] [Algebra O Ω₁]
  {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}

def comb (t : ∀ k, ι k) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) : ∀ k : K ⊕ K', Sum.elim ι ι' k
  | .inl k => t k
  | .inr k => s (.inr k)

theorem mseg_join (φ : Ω →ₐ[O] Ω₁) (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω₁)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) :
    mseg (joinCoord (fun p => φ (x p)) z) s =
      φ (mseg x (restrictChart s)) * mseg z (fun k => s (.inr k)) := by
  simp only [mseg, Fintype.prod_sum_type, map_prod]
  rfl

theorem chartMon_join (φ : Ω →ₐ[O] Ω₁) (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω₁)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) (a : K → ℤ) :
    chartMon (joinCoord (fun p => φ (x p)) z) s (pullDeg (K' := K') a) =
      φ (chartMon x (restrictChart s) a) := by
  simp only [chartMon, Fintype.prod_sum_type, pullDeg, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
    zpow_zero, Finset.prod_const_one, mul_one, map_prod, map_zpow₀]
  rfl

theorem map_mem (φ : Ω →ₐ[O] Ω₁) (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω₁)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) (hs : mseg (joinCoord (fun p => φ (x p)) z) s ≠ 0)
    (r : Ω) (hr : r ∈ chartRing O (mseg x) (restrictChart s)) :
    φ r ∈ chartRing O (mseg (joinCoord (fun p => φ (x p)) z)) s := by
  have hw : mseg z (fun k => s (.inr k)) ≠ 0 := by
    rw [mseg_join] at hs
    exact right_ne_zero_of_mul hs
  have hle : chartRing O (mseg x) (restrictChart s) ≤
      (chartRing O (mseg (joinCoord (fun p => φ (x p)) z)) s).comap φ := by
    unfold chartRing
    apply Algebra.adjoin_le
    rintro _ ⟨t, rfl⟩
    have h : φ (mseg x t / mseg x (restrictChart s)) =
        mseg (joinCoord (fun p => φ (x p)) z) (comb t s) / mseg (joinCoord (fun p => φ (x p)) z) s := by
      rw [mseg_join φ x z (comb t s), mseg_join φ x z s, map_div₀]
      exact (mul_div_mul_right _ _ hw).symm
    have h2 := div_mem_chartRing (o := O) (mseg (joinCoord (fun p => φ (x p)) z)) s (comb t s)
    rw [← h] at h2
    exact h2
  exact hle hr

theorem main [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
    (φ : Ω →ₐ[O] Ω₁) (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω₁) (u : Ω) (a : K → ℤ)
    (A : (∀ k, ι k) → AddSubgroup Ω) (hA : IsLine O x u a A)
    (B : (∀ k : K ⊕ K', Sum.elim ι ι' k) → AddSubgroup Ω₁)
    (hB : ∀ s, mseg (joinCoord (fun p => φ (x p)) z) s ≠ 0 → B s = AddSubgroup.closure
      {v | ∃ c ∈ chartRing O (mseg (joinCoord (fun p => φ (x p)) z)) s, ∃ e ∈ A (restrictChart s),
        v = c • φ e}) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k)
    (hs : mseg (joinCoord (fun p => φ (x p)) z) s ≠ 0) (v : Ω₁) :
    v ∈ B s ↔ ∃ r ∈ chartRing O (mseg (joinCoord (fun p => φ (x p)) z)) s,
      v = r * (φ u * chartMon (joinCoord (fun p => φ (x p)) z) s (pullDeg (K' := K') a)) := by
  have hx : mseg x (restrictChart s) ≠ 0 := by
    rw [mseg_join] at hs
    intro h
    exact left_ne_zero_of_mul hs (by rw [h, map_zero])
  rw [hB s hs, chartMon_join, ← map_mul]
  constructor
  · intro hv
    induction hv using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨c, hc, e, he, rfl⟩ := hw
      obtain ⟨r, hr, rfl⟩ := (hA _ hx e).1 he
      refine ⟨c * φ r, mul_mem hc (map_mem φ x z s hs r hr), ?_⟩
      rw [smul_eq_mul, map_mul, mul_assoc]
    | zero => exact ⟨0, zero_mem _, by rw [zero_mul]⟩
    | add w₁ w₂ _ _ h₁ h₂ =>
      obtain ⟨r₁, hr₁, rfl⟩ := h₁
      obtain ⟨r₂, hr₂, rfl⟩ := h₂
      exact ⟨r₁ + r₂, add_mem hr₁ hr₂, by rw [add_mul]⟩
    | neg w _ h =>
      obtain ⟨r, hr, rfl⟩ := h
      exact ⟨-r, neg_mem hr, by rw [neg_mul]⟩
  · rintro ⟨r, hr, rfl⟩
    exact AddSubgroup.subset_closure ⟨r, hr, _, (hA _ hx _).2 ⟨1, one_mem _, (one_mul _).symm⟩, rfl⟩

end PositivityTheory.Xgn.A_pull_line
end

section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XPullPreserve
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace PositivityTheory.Xgn.A_pull_preserve

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (restrictChart)

theorem below_ne {Ω : Type} [Field Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    (z : (Σ k, ι' k) → Ω) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k)
    (h : mseg (joinCoord x z) s ≠ 0) : mseg x (restrictChart s) ≠ 0 := by
  unfold mseg at h ⊢
  rw [Finset.prod_ne_zero_iff] at h ⊢
  intro k _
  exact h (Sum.inl k) (Finset.mem_univ _)

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω] {V : Type} [AddCommGroup V]
  [Module Ω V]

theorem smul_mem (R : Subalgebra O Ω) (L : AddSubgroup V) (b : Ω) (hb : b ∈ R) (v : V)
    (hv : v ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ L, v = a • e}) :
    b • v ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ L, v = a • e} := by
  induction hv using AddSubgroup.closure_induction with
  | mem v hv =>
    obtain ⟨a, ha, e, he, rfl⟩ := hv
    exact AddSubgroup.subset_closure ⟨b * a, R.mul_mem hb ha, e, he, by rw [mul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add v w _ _ hv hw => rw [smul_add]; exact add_mem hv hw
  | neg v _ hv => rw [smul_neg]; exact neg_mem hv

theorem le_closure (R : Subalgebra O Ω) (L L' : AddSubgroup V) (h : L ≤ L') :
    AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ L, v = a • e} ≤
      AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ L', v = a • e} := by
  apply AddSubgroup.closure_mono
  rintro v ⟨a, ha, e, he, rfl⟩
  exact ⟨a, ha, e, h he, rfl⟩

theorem gen_closure [IsDomain O] (R : Subalgebra O Ω) (L L' : AddSubgroup V)
    (h : ∀ v ∈ L, ∃ c : O, c ≠ 0 ∧ algebraMap O Ω c • v ∈ L') (v : V)
    (hv : v ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ L, v = a • e}) :
    ∃ c : O, c ≠ 0 ∧
      algebraMap O Ω c • v ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ L', v = a • e} := by
  induction hv using AddSubgroup.closure_induction with
  | mem v hv =>
    obtain ⟨a, ha, e, he, rfl⟩ := hv
    obtain ⟨c, hc, hce⟩ := h e he
    exact ⟨c, hc, AddSubgroup.subset_closure ⟨a, ha, _, hce, smul_comm _ _ _⟩⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact zero_mem _⟩
  | add v w _ _ hv hw =>
    obtain ⟨c, hc, hv⟩ := hv
    obtain ⟨d, hd, hw⟩ := hw
    refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
    rw [smul_add, map_mul]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact smul_mem R L' _ (R.algebraMap_mem d) _ hv
    · rw [mul_smul]
      exact smul_mem R L' _ (R.algebraMap_mem c) _ hw
  | neg v _ hv =>
    obtain ⟨c, hc, hv⟩ := hv
    exact ⟨c, hc, by rw [smul_neg]; exact neg_mem hv⟩

theorem scaled_closure (R : Subalgebra O Ω) (L L' : AddSubgroup V) (c : Ω)
    (h : ∀ v, v ∈ L' ↔ ∃ e ∈ L, v = c • e) (v : V) :
    v ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ L', v = a • e} ↔
      ∃ e ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ L, v = a • e}, v = c • e := by
  constructor
  · intro hv
    induction hv using AddSubgroup.closure_induction with
    | mem v hv =>
      obtain ⟨a, ha, e, he, rfl⟩ := hv
      obtain ⟨e', he', rfl⟩ := (h e).1 he
      exact ⟨a • e', AddSubgroup.subset_closure ⟨a, ha, e', he', rfl⟩, smul_comm _ _ _⟩
    | zero => exact ⟨0, zero_mem _, (smul_zero _).symm⟩
    | add v w _ _ hv hw =>
      obtain ⟨e, he, rfl⟩ := hv
      obtain ⟨f, hf, rfl⟩ := hw
      exact ⟨e + f, add_mem he hf, (smul_add _ _ _).symm⟩
    | neg v _ hv =>
      obtain ⟨e, he, rfl⟩ := hv
      exact ⟨-e, neg_mem he, (smul_neg _ _).symm⟩
  · rintro ⟨e, he, rfl⟩
    induction he using AddSubgroup.closure_induction with
    | mem v hv =>
      obtain ⟨a, ha, e, he, rfl⟩ := hv
      exact AddSubgroup.subset_closure ⟨a, ha, c • e, (h _).2 ⟨e, he, rfl⟩, smul_comm _ _ _⟩
    | zero => rw [smul_zero]; exact zero_mem _
    | add v w _ _ hv hw => rw [smul_add]; exact add_mem hv hw
    | neg v _ hv => rw [smul_neg]; exact neg_mem hv

end PositivityTheory.Xgn.A_pull_preserve

theorem PositivityTheory.Xgn.t_pull_preserve : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E E' : ChartBundle O (mseg x) N V) (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω) (EB E'B : ChartBundle O (mseg (joinCoord x z)) N V), IsPull O x z E EB → IsPull O x z E' E'B → (LatLE O x E E' → LatLE O (joinCoord x z) EB E'B) ∧ (SameGeneric O x E E' → SameGeneric O (joinCoord x z) EB E'B) ∧ (∀ c : Ω, IsScaled x c E.lat E'.lat → IsScaled (joinCoord x z) c EB.lat E'B.lat) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x N V _ _ E E' K' _ _ ι' _ z EB E'B hP hP'
  refine ⟨fun h s hs => ?_, fun h s hs => ?_, fun c h s hs v => ?_⟩
  · rw [hP s hs, hP' s hs]
    exact PositivityTheory.Xgn.A_pull_preserve.le_closure _ _ _ (h _ (PositivityTheory.Xgn.A_pull_preserve.below_ne x z s hs))
  · rw [hP s hs, hP' s hs]
    have h0 := h _ (PositivityTheory.Xgn.A_pull_preserve.below_ne x z s hs)
    exact ⟨PositivityTheory.Xgn.A_pull_preserve.gen_closure _ _ _ h0.1,
      PositivityTheory.Xgn.A_pull_preserve.gen_closure _ _ _ h0.2⟩
  · rw [hP s hs, hP' s hs]
    exact PositivityTheory.Xgn.A_pull_preserve.scaled_closure _ _ _ c
      (h _ (PositivityTheory.Xgn.A_pull_preserve.below_ne x z s hs)) v
end

section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.LineLatticeSpread
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.LineLatticeSpread

theorem exists_common {α : Type*} [TopologicalSpace α] [TopologicalSpace.NoetherianSpace α] [QuasiSober α]
    {O : Type*} [CommRing O] [IsDomain O] (f : α → PrimeSpectrum O) (hf : Continuous f) (C : Set α)
    (hC : IsClosed C) (h : ∀ x ∈ C, ∃ o : O, o ≠ 0 ∧ o ∈ (f x).asIdeal) :
    ∃ n : O, n ≠ 0 ∧ ∀ x ∈ C, n ∈ (f x).asIdeal := by
  classical
  obtain ⟨S, hS, hcl, hirr, hU⟩ := TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hC
  have key : ∀ Z ∈ S, ∃ o : O, o ≠ 0 ∧ ∀ x ∈ Z, o ∈ (f x).asIdeal := by
    intro Z hZ
    obtain ⟨η, hη⟩ := QuasiSober.sober (hirr Z hZ) (hcl Z hZ)
    obtain ⟨o, ho, hm⟩ := h η (by rw [hU]; exact ⟨Z, hZ, hη.mem⟩)
    refine ⟨o, ho, fun x hx => ?_⟩
    exact (PrimeSpectrum.le_iff_specializes _ _).2 ((hη.specializes hx).map hf) hm
  choose! o ho hm using key
  refine ⟨∏ Z ∈ hS.toFinset, o Z, Finset.prod_ne_zero_iff.2 fun Z hZ => ho Z (hS.mem_toFinset.1 hZ), ?_⟩
  intro x hx
  rw [hU] at hx
  obtain ⟨Z, hZ, hxZ⟩ := hx
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem o (hS.mem_toFinset.2 hZ)
  rw [hc]
  exact Ideal.mul_mem_right _ _ (hm Z hZ x hxZ)

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem isGenAt_iff (L : Lat ξ Ω) (b : Fin 1 → Ω) (q : Cpt ξ) (hb : L.IsFrameAt b q) (t : Ω) :
    L.IsGenAt q t ↔ unitAt ξ q (t / b 0) := by
  have h0 : b 0 ≠ 0 := hb.1.ne_zero 0
  have hr : Set.range b = {b 0} := Set.range_unique
  have hL : L q = Submodule.span (regAt ξ q) {b 0} := by rw [hb.2, hr]
  constructor
  · rintro ⟨ht, e⟩
    have e' := hL.symm.trans e
    refine ⟨div_ne_zero ht h0, ?_, ?_⟩
    · have : t ∈ Submodule.span (regAt ξ q) {b 0} := e' ▸ Submodule.mem_span_singleton_self t
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 this
      have hr' : (r : Ω) * b 0 = t := hr
      rw [← hr', mul_div_cancel_right₀ _ h0]
      exact r.2
    · have : b 0 ∈ Submodule.span (regAt ξ q) {t} := e' ▸ Submodule.mem_span_singleton_self (b 0)
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 this
      have hr' : (r : Ω) * t = b 0 := hr
      rw [inv_div, ← hr', mul_div_cancel_right₀ _ ht]
      exact r.2
  · rintro ⟨h1, h2, h3⟩
    have ht : t ≠ 0 := fun h => h1 (by rw [h, zero_div])
    refine ⟨ht, hL.trans (le_antisymm ?_ ?_)⟩
    · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
      refine ⟨⟨_, h3⟩, ?_⟩
      show (t / b 0)⁻¹ * t = b 0
      field_simp
    · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
      refine ⟨⟨_, h2⟩, ?_⟩
      show (t / b 0) * b 0 = t
      field_simp

end PositivityTheory.Xgn.LineLatticeSpread

open PositivityTheory.Xgn.LineLatticeSpread in
theorem PositivityTheory.Xgn.line_lattice_spread : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsNoetherianRing O] [LocallyOfFiniteType s] [QuasiCompact s], ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → Function.Injective (algebraMap O Ω) → IsCptGen ξ → ∀ (L : Lat ξ Ω) (T : Set (Cpt ξ)) (n₀ : O) (t : Ω), n₀ ≠ 0 → (∀ p, unitAt ξ p (algebraMap O Ω n₀) → p ∈ T) → L.IsVBOn T 1 ⊤ → (∀ p ∈ genFibre O ξ, L.IsGenAt p t) → ∃ n : O, n ≠ 0 ∧ ∀ p, unitAt ξ p (algebraMap O Ω n) → L.IsGenAt p t := by
  intro X Ω _ ξ O _ _ _ s _ _ _ hs _ hc L T n₀ t hn₀ hT hL hgen
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  haveI : IsNoetherian X := {}
  have hu : ∀ (p : Cpt ξ) (o : O), unitAt ξ p (algebraMap O Ω o) ↔ o ∉ (s p.1).asIdeal := fun p o =>
    (ConstReg.regular_const X Ω ξ O s hs p o).2 hc
  let W : Set X := ⋃ (U : X.Opens) (_ : ∀ q : Cpt ξ, q.1 ∈ U → L.IsGenAt q t), (U : Set X)
  have hW : IsOpen W := isOpen_iUnion fun U => isOpen_iUnion fun _ => U.isOpen
  obtain ⟨n, hn, H⟩ := exists_common (O := O) (fun x : X => s x) s.continuous (closure {genPt ξ} ∩ Wᶜ)
    (isClosed_closure.inter hW.isClosed_compl) (by
      rintro x ⟨hx, hxW⟩
      by_contra hcon
      let p : Cpt ξ := ⟨x, specializes_iff_mem_closure.2 hx⟩
      have hp : p ∈ genFibre O ξ := fun o ho => (hu p o).2 fun hm => hcon ⟨o, ho, hm⟩
      obtain ⟨U, hpU, b, -, hb⟩ := hL p (hT p (hp n₀ hn₀))
      have h1 := (isGenAt_iff L b p (hb p (hT p (hp n₀ hn₀)) hpU) t).1 (hgen p hp)
      obtain ⟨U₁, hp₁, H₁⟩ := (regAt_unitAt_open X Ω ξ p _).2 h1
      obtain ⟨U₂, hp₂, H₂⟩ := (regAt_unitAt_open X Ω ξ p _).2 (hp n₀ hn₀)
      refine hxW (Set.mem_iUnion₂.2 ⟨U ⊓ U₁ ⊓ U₂, ?_, ⟨⟨hpU, hp₁⟩, hp₂⟩⟩)
      rintro q ⟨⟨hq, hq₁⟩, hq₂⟩
      exact (isGenAt_iff L b q (hb q (hT q (H₂ q hq₂)) hq) t).2 (H₁ q hq₁))
  refine ⟨n, hn, fun p hp => ?_⟩
  have hpW : p.1 ∈ W := by
    by_contra hW'
    exact (hu p n).1 hp (H p.1 ⟨specializes_iff_mem_closure.1 p.2, hW'⟩)
  obtain ⟨U, hU, hpU⟩ := Set.mem_iUnion₂.1 hpW
  exact hU p hpU
end
