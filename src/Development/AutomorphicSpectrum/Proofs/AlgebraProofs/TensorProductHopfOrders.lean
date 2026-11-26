module

public import Development.WeilBound.CoreStatements.HodgeTatePoints.HcptgenRing
public import Development.WeilBound.CoreStatements.HodgeTatePoints.RbProj
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FundamentalIdealFrobeniusPowers

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TensorProductHopfOrders
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TensorProductHopfOrders
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.tensor_product_hopf_orders : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N₁ : Type) [AddCommGroup N₁] [Fintype N₁] [DecidableEq N₁], ∀ (N₂ : Type) [AddCommGroup N₂] [Fintype N₂] [DecidableEq N₂], ∀ (A₁ : HopfOrder (C := C) R N₁) (A₂ : HopfOrder (C := C) R N₂), ∃ AA : HopfOrder (C := C) R (N₁ × N₂), AA.carrier = tens A₁.carrier A₂.carrier ∧ AA.carrier.map (LinearMap.funLeft R C (AddMonoidHom.inl N₁ N₂ : N₁ → N₁ × N₂)) = A₁.carrier ∧ AA.carrier.map (LinearMap.funLeft R C (AddMonoidHom.inr N₁ N₂ : N₂ → N₁ × N₂)) = A₂.carrier ∧ (∀ g ∈ AA.carrier, (fun z : N₁ × N₂ => g (z.1, 0)) ∈ AA.carrier) ∧ (∀ g ∈ AA.carrier, (fun z : N₁ × N₂ => g (0, z.2)) ∈ AA.carrier) ∧ ∀ c₁ c₂, HasColen R v A₁.carrier c₁ → HasColen R v A₂.carrier c₂ → HasColen R v AA.carrier (c₁ ^ Fintype.card N₂ * c₂ ^ Fintype.card N₁) := by
  first | exact @PositivityTheory.HtPt.Re.tens_hopf | exact PositivityTheory.HtPt.Re.tens_hopf
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TensorProductHopfOrdersStatement
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_product_hopf_orders : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N₁ : Type) [AddCommGroup N₁] [Fintype N₁] [DecidableEq N₁], ∀ (N₂ : Type) [AddCommGroup N₂] [Fintype N₂] [DecidableEq N₂], ∀ (A₁ : HopfOrder (C := C) R N₁) (A₂ : HopfOrder (C := C) R N₂), ∃ AA : HopfOrder (C := C) R (N₁ × N₂), AA.carrier = tens A₁.carrier A₂.carrier ∧ AA.carrier.map (LinearMap.funLeft R C (AddMonoidHom.inl N₁ N₂ : N₁ → N₁ × N₂)) = A₁.carrier ∧ AA.carrier.map (LinearMap.funLeft R C (AddMonoidHom.inr N₁ N₂ : N₂ → N₁ × N₂)) = A₂.carrier ∧ (∀ g ∈ AA.carrier, (fun z : N₁ × N₂ => g (z.1, 0)) ∈ AA.carrier) ∧ (∀ g ∈ AA.carrier, (fun z : N₁ × N₂ => g (0, z.2)) ∈ AA.carrier) ∧ ∀ c₁ c₂, HasColen R v A₁.carrier c₁ → HasColen R v A₂.carrier c₂ → HasColen R v AA.carrier (c₁ ^ Fintype.card N₂ * c₂ ^ Fintype.card N₁) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.tensor_product_hopf_orders | exact GlobalTheory.CompanionTheory.Relay.tensor_product_hopf_orders | (intros; apply GlobalTheory.CompanionTheory.Relay.tensor_product_hopf_orders <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartRingsNoetherianFraction
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartRingsNoetherianFraction
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.ChartNoethFrac

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing div_mem_chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

theorem isNoetherianRing_chartRing {O Ω σ : Type} [CommRing O] [IsNoetherianRing O] [Field Ω] [Algebra O Ω]
    [Finite σ] (y : σ → Ω) (c : σ) : IsNoetherianRing (chartRing O y c) := by
  have hfg : (chartRing O y c).FG := ⟨(Set.finite_range _).toFinset, by rw [Set.Finite.coe_toFinset]; rfl⟩
  have : Algebra.FiniteType O (chartRing O y c) := (Subalgebra.fg_iff_finiteType _).1 hfg
  exact Algebra.FiniteType.isNoetherianRing O _

variable {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type}

theorem fnField_le_closure [DecidableEq K] [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (c : ∀ k, ι k)
    (hc : mseg x c ≠ 0) :
    fnField O x ≤ Subfield.closure (chartRing O (mseg x) c : Set Ω) := by
  have hr : ∀ (k : K) (i : ι k), x ⟨k, i⟩ / x ⟨k, c k⟩ ∈ chartRing O (mseg x) c := fun k i => by
    rw [PositivityTheory.HtPt.Hcptgen.ratio_eq x c hc k i]
    exact div_mem_chartRing _ _ _
  refine (Subfield.closure_le).2 ?_
  rintro _ (⟨r, rfl⟩ | ⟨⟨k, i, j⟩, rfl⟩)
  · exact Subfield.subset_closure ((chartRing O (mseg x) c).algebraMap_mem r)
  · have hk : x ⟨k, c k⟩ ≠ 0 := Finset.prod_ne_zero_iff.1 hc k (Finset.mem_univ k)
    have e : x ⟨k, i⟩ / x ⟨k, j⟩ = (x ⟨k, i⟩ / x ⟨k, c k⟩) / (x ⟨k, j⟩ / x ⟨k, c k⟩) :=
      (div_div_div_cancel_right₀ hk _ _).symm
    show x ⟨k, i⟩ / x ⟨k, j⟩ ∈ Subfield.closure (chartRing O (mseg x) c : Set Ω)
    rw [e]
    exact div_mem (Subfield.subset_closure (hr k i)) (Subfield.subset_closure (hr k j))

theorem isFractionRing_of_closure_eq_top (A : Subalgebra O Ω)
    (h : Subfield.closure (A : Set Ω) = ⊤) : IsFractionRing A Ω := by
  refine IsFractionRing.of_field A Ω fun z => ?_
  have hz : z ∈ Subfield.closure (A : Set Ω) := h ▸ Subfield.mem_top z
  obtain ⟨a, ha, b, hb, rfl⟩ := Subfield.mem_closure_iff.1 hz
  have hs : Subring.closure (A : Set Ω) = A.toSubring := by
    have := Subring.closure_eq A.toSubring
    simpa using this
  rw [hs] at ha hb
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, rfl⟩

variable {K' : Type} [Fintype K'] {ι' : K' → Type}

theorem mseg_joinCoord [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) :
    mseg (joinCoord x z) s = mseg x (restrictChart s) * mseg z (fun k => s (.inr k)) := by
  unfold mseg
  rw [Fintype.prod_sum_type]
  rfl

def comb (t : ∀ k, ι k) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) : ∀ k : K ⊕ K', Sum.elim ι ι' k
  | .inl k => t k
  | .inr k => s (.inr k)


omit [Fintype K] [Fintype K'] in
theorem fnField_le_join (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) :
    fnField O x ≤ fnField O (joinCoord x z) := by
  refine Subfield.closure_mono (Set.union_subset_union_right _ ?_)
  rintro _ ⟨⟨k, i, j⟩, rfl⟩
  exact ⟨⟨.inl k, i, j⟩, rfl⟩

theorem chartRing_le_join [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) (hs : mseg (joinCoord x z) s ≠ 0) :
    chartRing O (mseg x) (restrictChart s) ≤ chartRing O (mseg (joinCoord x z)) s := by
  have hw : mseg z (fun k => s (.inr k)) ≠ 0 := by
    rw [mseg_joinCoord] at hs
    exact right_ne_zero_of_mul hs
  refine Algebra.adjoin_le ?_
  rintro _ ⟨t, rfl⟩
  have h : mseg x t / mseg x (restrictChart s) =
      mseg (joinCoord x z) (comb t s) / mseg (joinCoord x z) s := by
    rw [mseg_joinCoord x z (comb t s), mseg_joinCoord x z s]
    exact (mul_div_mul_right _ _ hw).symm
  show mseg x t / mseg x (restrictChart s) ∈ chartRing O (mseg (joinCoord x z)) s
  rw [h]
  exact div_mem_chartRing _ _ _

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω), (∀ c, IsNoetherianRing (chartRing O (mseg x) c)) ∧ (fnField O x = ⊤ → ∀ c, mseg x c ≠ 0 → IsFractionRing (chartRing O (mseg x) c) Ω) ∧ ∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω), (fnField O x = ⊤ → fnField O (joinCoord x z) = ⊤) ∧ ∀ c, mseg (joinCoord x z) c ≠ 0 → mseg x (restrictChart c) ≠ 0 ∧ (chartRing O (mseg x) (restrictChart c)) ≤ (chartRing O (mseg (joinCoord x z)) c) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x
  refine ⟨fun c => isNoetherianRing_chartRing _ c, fun htop c hc => ?_, fun K' _ _ ι' _ z =>
    ⟨fun htop => top_le_iff.1 (htop ▸ fnField_le_join x z), fun c hc => ⟨?_, chartRing_le_join x z c hc⟩⟩⟩
  · exact isFractionRing_of_closure_eq_top _ (top_le_iff.1 (htop ▸ fnField_le_closure x c hc))
  · rw [mseg_joinCoord] at hc
    exact left_ne_zero_of_mul hc

end GlobalTheory.CompanionTheory.Ar.Num.ChartNoethFrac
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartRingsNoetherianFractionStatement
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_rings_noetherian_fraction : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω), (∀ c, IsNoetherianRing (chartRing O (mseg x) c)) ∧ (fnField O x = ⊤ → ∀ c, mseg x c ≠ 0 → IsFractionRing (chartRing O (mseg x) c) Ω) ∧ ∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω), (fnField O x = ⊤ → fnField O (joinCoord x z) = ⊤) ∧ ∀ c, mseg (joinCoord x z) c ≠ 0 → mseg x (restrictChart c) ≠ 0 ∧ (chartRing O (mseg x) (restrictChart c)) ≤ (chartRing O (mseg (joinCoord x z)) c) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.ChartNoethFrac.main | exact GlobalTheory.CompanionTheory.Ar.Num.ChartNoethFrac.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.ChartNoethFrac.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FundamentalIdealFrobeniusProduct
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FundamentalIdealFrobeniusProduct
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR.ROm

section
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
  {F : Type} [Field F]

theorem mem_x_ideal_iff (M : Submodule R (F → C)) (χ : MulChar F R) (r : R) :
    r ∈ xIdeal M χ ↔ (fun a => algebraMap R C (r * χ a)) ∈ M := by
  have : LinearMap.toSpanSingleton R (F → C) (fun a => algebraMap R C (χ a)) r =
      fun a => algebraMap R C (r * χ a) := by
    funext a; simp [Algebra.smul_def]
  rw [xIdeal, Submodule.mem_comap, this]

theorem mem_aug (M : Submodule R (F → C)) (g : F → C) :
    g ∈ augIdeal M ↔ g ∈ M ∧ g 0 = 0 := Iff.rfl

theorem v_le_of_mem (hv : v.Integers R) {a b : R} (h : a ∈ Ideal.span {b}) :
    v (algebraMap R C a) ≤ v (algebraMap R C b) := by
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 h
  rw [map_mul, map_mul]
  exact mul_le_of_le_one_left' (hv.map_le_one s)

theorem v_eq_of_span (hv : v.Integers R) {a b : R} (h : Ideal.span {a} = Ideal.span {b}) :
    v (algebraMap R C a) = v (algebraMap R C b) :=
  le_antisymm (v_le_of_mem hv (h ▸ Ideal.mem_span_singleton_self a))
    (v_le_of_mem hv (h ▸ Ideal.mem_span_singleton_self b))

theorem sq_bound (hv : v.Integers R) {X : Type} (s : Set (X → C)) (l : (X → C) →ₗ[R] C)
    (b : NNReal) (h : ∀ g ∈ s, ∀ g' ∈ s, v (l (g * g')) ≤ b) :
    ∀ g ∈ sqIdeal (Submodule.span R s), v (l g) ≤ b := by
  let T : Submodule R C :=
    { carrier := {x | v x ≤ b}
      add_mem' := fun hx hy => v.map_add_le hx hy
      zero_mem' := by simp
      smul_mem' := fun r x hx => by
        change v (r • x) ≤ b
        rw [Algebra.smul_def, map_mul]
        exact (mul_le_of_le_one_left' (hv.map_le_one r)).trans hx }
  have : sqIdeal (Submodule.span R s) ≤ T.comap l := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, hg, g', hg', rfl⟩
    have h1 : Submodule.span R s * Submodule.span R s ≤ T.comap l := by
      rw [Submodule.span_mul_span]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨a, ha, a', ha', rfl⟩
      exact h a ha a' ha'
    exact h1 (Submodule.mul_mem_mul hg hg')
  exact fun g hg => this hg

variable [Fintype F] [DecidableEq F]

theorem pow_mem_aug (AA : HopfOrder (C := C) R F) {g : F → C} (hg : g ∈ augIdeal AA.carrier)
    (k : ℕ) : g ^ (k + 1) ∈ augIdeal AA.carrier := by
  induction k with
  | zero => simpa using hg
  | succ k ih =>
    rw [pow_succ]
    refine (mem_aug _ _).2 ⟨AA.mul_mem _ _ ih.1 hg.1, ?_⟩
    rw [Pi.mul_apply, ((mem_aug _ _).1 hg).2, mul_zero]

theorem pow_mem_sq (AA : HopfOrder (C := C) R F) (χ : MulChar F R) {c : R}
    (hc : c ∈ xIdeal AA.carrier χ) {k : ℕ} (hk : 2 ≤ k) :
    (fun a => algebraMap R C (c ^ k * (χ ^ k) a)) ∈ sqIdeal (augIdeal AA.carrier) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 + 1 := ⟨k - 2, by omega⟩
  have hg : (fun a => algebraMap R C (c * χ a)) ∈ augIdeal AA.carrier :=
    (mem_aug _ _).2 ⟨(mem_x_ideal_iff _ _ _).1 hc, by simp [MulChar.map_zero]⟩
  refine Submodule.subset_span ⟨_, pow_mem_aug AA hg j, _, hg, ?_⟩
  funext a
  rw [← pow_succ, Pi.pow_apply, MulChar.pow_apply' _ (by omega), ← mul_pow, map_pow]

theorem sq_le (AA : HopfOrder (C := C) R F) : sqIdeal (augIdeal AA.carrier) ≤ AA.carrier := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, hg, g', hg', rfl⟩
  exact AA.mul_mem _ _ hg.1 hg'.1

omit [Fintype F] [DecidableEq F] in
theorem eig_fun (χ : MulChar F R) (r : R) (a x : F) :
    algebraMap R C (r * χ (a • x)) = algebraMap R C (χ a) * algebraMap R C (r * χ x) := by
  simp only [smul_eq_mul, map_mul]; ring

end

theorem digits {p f m : ℕ} (h1 : 1 ≤ m) (h2 : m < p ^ f) :
    ∃ d : Fin f → Fin p, (∃ n, (d n : ℕ) ≠ 0) ∧ ∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ) = m := by
  refine ⟨finFunctionFinEquiv.symm ⟨m, h2⟩, ?_, ?_⟩
  · by_contra h
    push Not at h
    have := finFunctionFinEquiv_apply (finFunctionFinEquiv.symm ⟨m, h2⟩)
    rw [Equiv.apply_symm_apply] at this
    simp [h] at this
    omega
  · rw [← finFunctionFinEquiv_apply, Equiv.apply_symm_apply]

theorem hasLen_quot {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
    (v : Valuation C NNReal) {M : Type} [AddCommGroup M] [Module R M] (φ : R →ₗ[R] M)
    (hφ : Function.Surjective φ) (δ : R) (hk : LinearMap.ker φ = Ideal.span {δ}) :
    HasLen v R M (v (algebraMap R C δ)) := by
  refine ⟨1, fun _ => δ, ⟨?_⟩, by simp⟩
  exact ((φ.quotKerEquivOfSurjective hφ).symm.trans (Submodule.quotEquivOfEq _ _ hk)).trans
    (LinearEquiv.funUnique (Fin 1) R (R ⧸ Ideal.span {δ})).symm

end GlobalTheory.CompanionTheory.Ar.GR.ROm

open GlobalTheory.CompanionTheory.Ar.GR.ROm PositivityTheory.HtPt.Rb in
theorem _root_.GlobalTheory.CompanionTheory.Relay.fundamental_ideal_frobenius_product : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable (F := F) AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ c : ℕ → R, (∀ n, xIdeal AA.carrier (σ ^ p ^ n) = Ideal.span {c n}) → ∀ n, (∀ r : R, (fun a => algebraMap R C (r * (σ ^ p ^ (n + 1)) a)) ∈ sqIdeal (augIdeal AA.carrier) ↔ r ∈ Ideal.span {c n ^ p}) ∧ (∃ δ : R, c n ^ p = δ * c (n + 1)) ∧ ∀ δ : R, c n ^ p = δ * c (n + 1) → HasLen v R (OmType AA.carrier (σ ^ p ^ (n + 1))) (v (algebraMap R C δ)) := by
  intro p hpp C _ _ _ v R _ _ hv hp F _ _ _ _ f hf AA hst σ hσ c hc n
  haveI : IsDomain R := hv.hom_inj.isDomain
  have hp2 : 2 ≤ p := hpp.out.two_le
  have hf0 : 0 < f := Nat.pos_of_ne_zero (f_ne_zero hf)
  have hord : orderOf σ = p ^ f - 1 := (FundGen.main p C v R hv hp F f hf σ hσ).1
  obtain ⟨h0, -⟩ := exists_inv_card hv hp hf
  have hprin := eig_rank_one p C v R hv hp F f hf AA hst
  have hmono := (GlobalTheory.T.fundamental_ideal_frobenius_powers p C v R hv hp F f hf AA hst σ hσ c hc).2
  have hq : 1 ≤ p ^ f := Nat.one_le_pow _ _ (by omega)
  have hsq : ∀ n, (fun a => algebraMap R C (c n ^ p * (σ ^ p ^ (n + 1)) a)) ∈
      sqIdeal (augIdeal AA.carrier) := fun n => by
    have := pow_mem_sq AA (σ ^ p ^ n) (hc n ▸ Ideal.mem_span_singleton_self (c n)) hp2
    rwa [← pow_mul, ← pow_succ] at this
  have hdvd : ∀ n, c n ^ p ∈ Ideal.span {c (n + 1)} := fun n => by
    rw [← hc, mem_x_ideal_iff]
    exact sq_le AA (hsq n)
  have hper : ∀ n, σ ^ p ^ (n + f) = σ ^ p ^ n := fun n => by
    rw [pow_eq_pow_iff_modEq, hord, pow_add]
    have : p ^ f ≡ 1 [MOD (p ^ f - 1)] := ((Nat.modEq_iff_dvd' hq).2 dvd_rfl).symm
    simpa using this.mul_left (p ^ n)
  have hcarry := frobeniusChain_carry p f hp2 hf0 (fun n => v (algebraMap R C (c n)))
    (fun n => v_eq_of_span hv (by rw [← hc, ← hc, hper])) (fun n => hv.map_le_one _)
    (fun n => by simpa only [map_pow] using v_le_of_mem hv (hdvd n))
  choose c' hc'0 hc' using fun m : ℕ => (hprin (σ ^ m)).1
  have hdec := (r_decomp_relay p C v R hv hp F f hf AA hst σ hσ c' hc').1
  have hiff : ∀ r : R, (fun a => algebraMap R C (r * (σ ^ p ^ (n + 1)) a)) ∈
      sqIdeal (augIdeal AA.carrier) ↔ r ∈ Ideal.span {c n ^ p} := by
    intro r
    constructor
    · intro hr
      rw [hdec] at hr
      have := sq_bound hv _ ((LinearMap.proj (R := R) (φ := fun _ : F => C) 1).comp
        (projL (σ ^ p ^ (n + 1)))) (v (algebraMap R C (c n)) ^ p) ?_ _ hr
      · rw [LinearMap.comp_apply, projL_apply, proj_eigen_self h0 _ _ (eig_fun _ r)] at this
        simp only [LinearMap.proj_apply, map_one, mul_one] at this
        rw [Ideal.mem_span_singleton]
        refine hv.dvd_of_le ?_
        simpa only [map_pow] using this
      · rintro _ ⟨m, hm, rfl⟩ _ ⟨m', hm', rfl⟩
        simp only [Finset.coe_Icc, Set.mem_Icc] at hm hm'
        have e : ((fun a : F => algebraMap R C (c' m * (σ ^ m) a)) *
            fun a : F => algebraMap R C (c' m' * (σ ^ m') a)) =
            fun a : F => algebraMap R C ((c' m * c' m') * (σ ^ (m + m')) a) := by
          funext a
          simp only [Pi.mul_apply, pow_add, MulChar.mul_apply, map_mul]; ring
        rw [LinearMap.comp_apply, projL_apply]
        simp only []
        rw [e]
        by_cases hχ : σ ^ p ^ (n + 1) = σ ^ (m + m')
        · rw [hχ, proj_eigen_self h0 _ _ (eig_fun _ _)]
          simp only [LinearMap.proj_apply, map_one, mul_one]
          obtain ⟨d, ⟨i, hi⟩, hd⟩ := digits (p := p) (f := f) hm.1 (by omega)
          obtain ⟨d', ⟨i', hi'⟩, hd'⟩ := digits (p := p) (f := f) hm'.1 (by omega)
          have e1 := hmono d ⟨i, hi⟩
          have e2 := hmono d' ⟨i', hi'⟩
          rw [hd, hc'] at e1
          rw [hd', hc'] at e2
          rw [map_mul, map_mul, v_eq_of_span hv e1, v_eq_of_span hv e2]
          have := hcarry (fun k => (d k : ℕ) + d' k) n ?_ ?_
          · simpa only [pow_add, Finset.prod_mul_distrib, map_prod, map_pow] using this
          · rw [Finset.sum_add_distrib]
            have a1 := Finset.single_le_sum (f := fun k => (d k : ℕ)) (fun _ _ => Nat.zero_le _)
              (Finset.mem_univ i)
            have a2 := Finset.single_le_sum (f := fun k => (d' k : ℕ)) (fun _ _ => Nat.zero_le _)
              (Finset.mem_univ i')
            omega
          · simp only [add_mul, Finset.sum_add_distrib, hd, hd']
            rw [← hord, ← pow_eq_pow_iff_modEq, hχ]
        · rw [proj_eigen_ne hχ _ (eig_fun _ _)]
          simp
    · intro hr
      obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 hr
      convert Submodule.smul_mem _ s (hsq n) using 1
      funext a
      simp [Algebra.smul_def, map_mul, mul_assoc]
  refine ⟨hiff, ?_, fun δ hδ => ?_⟩
  · obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 (hdvd n)
    exact ⟨s, hs.symm⟩
  · have hne : c (n + 1) ≠ 0 := by
      intro h
      have := hc (n + 1)
      rw [hc', h, Ideal.span_singleton_zero, Ideal.span_singleton_eq_bot] at this
      exact hc'0 _ this
    have hg : (fun a => algebraMap R C (c (n + 1) * (σ ^ p ^ (n + 1)) a)) ∈
        eig AA.carrier (σ ^ p ^ (n + 1)) :=
      ((hprin _).2 _).2 ⟨_, hc (n + 1) ▸ Ideal.mem_span_singleton_self _, rfl⟩
    have hsm : ∀ r : R, r • (fun a => algebraMap R C (c (n + 1) * (σ ^ p ^ (n + 1)) a)) =
        fun a => algebraMap R C (r * c (n + 1) * (σ ^ p ^ (n + 1)) a) := fun r => by
      funext a
      simp only [Pi.smul_apply, Algebra.smul_def, map_mul, mul_assoc]
    refine hasLen_quot v ((Submodule.mkQ _).comp (LinearMap.toSpanSingleton R _ ⟨_, hg⟩)) ?_ δ ?_
    · refine (Submodule.mkQ_surjective _).comp ?_
      rintro ⟨g, hg'⟩
      obtain ⟨r, hr, rfl⟩ := ((hprin _).2 _).1 hg'
      rw [hc] at hr
      obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 hr
      exact ⟨s, Subtype.ext (hsm s)⟩
    · ext r
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      change r • (fun a => algebraMap R C (c (n + 1) * (σ ^ p ^ (n + 1)) a)) ∈ _ ↔ _
      rw [hsm, hiff, hδ, Ideal.mem_span_singleton, Ideal.mem_span_singleton,
        mul_dvd_mul_iff_right hne]
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FundamentalIdealFrobeniusProductStatement
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_ideal_frobenius_product : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable F AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ c : ℕ → R, (∀ n, xIdeal AA.carrier (σ ^ p ^ n) = Ideal.span {c n}) → ∀ n, (∀ r : R, (fun a => algebraMap R C (r * (σ ^ p ^ (n + 1)) a)) ∈ sqIdeal (augIdeal AA.carrier) ↔ r ∈ Ideal.span {c n ^ p}) ∧ (∃ δ : R, c n ^ p = δ * c (n + 1)) ∧ ∀ δ : R, c n ^ p = δ * c (n + 1) → HasLen v R (OmType AA.carrier (σ ^ p ^ (n + 1))) (v (algebraMap R C δ)) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.fundamental_ideal_frobenius_product | exact GlobalTheory.CompanionTheory.Relay.fundamental_ideal_frobenius_product | (intros; apply GlobalTheory.CompanionTheory.Relay.fundamental_ideal_frobenius_product <;> assumption)
end
end
