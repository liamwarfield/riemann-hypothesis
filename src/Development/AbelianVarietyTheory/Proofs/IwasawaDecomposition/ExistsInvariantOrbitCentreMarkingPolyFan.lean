module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefImPartOnPolydiscOfPuncturedCover

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkedOrbitFormPrimitive
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkedOrbitFormPrimitive
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

namespace OrbMark

theorem eq_one_of_smul_eq_of_orbFun_evalZ_eq_one :
    ∀ {O : Type} [CommRing O] (bar : O → O) (w0 : O) {X₀ : Type} [AddCommGroup X₀] [Module O X₀]
      (v : LinearMap.BilinForm ℤ X₀) (hv : v ∈ balForms bar X₀), IsPrim bar (⟨v, hv⟩ : balForms bar X₀) →
      ∀ {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (β : LinearMap.BilinForm ℤ X),
        (OrbMark.orbFun O w0 v).evalZ β = 1 →
        ∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = β → k = 1 := by
  intro O _ bar w0 X₀ _ _ v hv hp X _ _ _ β hβ k β' hk
  obtain ⟨τ, f, -, hf, -, H⟩ := GlobalTheory.T.exists_semilinear_pullback_of_markedOrbitIndicator w0 v β hβ
  have hval : ∀ (x₀ y₀ : X₀), ∃ x y, v x₀ y₀ = β x y := by
    intro x₀ y₀
    obtain ⟨x, hx⟩ := hf (Submodule.Quotient.mk x₀)
    obtain ⟨y, hy⟩ := hf (Submodule.Quotient.mk y₀)
    exact ⟨x, y, (H x y x₀ y₀ hx.symm hy.symm).symm⟩
  have hβ' : ∀ x y, (k : ℤ) * β' x y = β x y := fun x y => by rw [← hk]; simp
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · exfalso
    have hv0 : v = 0 := LinearMap.ext₂ fun x₀ y₀ => by
      obtain ⟨x, y, e⟩ := hval x₀ y₀
      rw [e, ← hβ']
      simp
    exact zero_ne_one (hp 0 0 (Subtype.ext (by simp [hv0])))
  · have hkz : (k : ℤ) ≠ 0 := by exact_mod_cast hk0.ne'
    have hcan : ∀ {a b : ℤ}, (k : ℤ) * a = k * b → a = b := fun h => mul_left_cancel₀ hkz h
    have hl : ∀ x, f x = 0 → ∀ y, β' x y = 0 := by
      intro x hx y
      obtain ⟨y₀, hy₀⟩ := Submodule.Quotient.mk_surjective _ (f y)
      have e := H x y 0 y₀ (by rw [hx]; rfl) hy₀
      apply hcan
      rw [hβ', e]
      simp
    have hr : ∀ x, f x = 0 → ∀ y, β' y x = 0 := by
      intro x hx y
      obtain ⟨y₀, hy₀⟩ := Submodule.Quotient.mk_surjective _ (f y)
      have e := H y x y₀ 0 hy₀ (by rw [hx]; rfl)
      apply hcan
      rw [hβ', e]
      simp
    obtain ⟨ζ₁, hζ₁⟩ := GlobalTheory.T.exists_intBilinForm_descend_along_surjective f hf β' hl hr
    let m : X₀ →ₗ[ℤ] X₀ ⧸ (CarDim.orad v : Submodule O X₀) :=
      (CarDim.orad v : Submodule O X₀).mkQ.toAddMonoidHom.toIntLinearMap
    let ζ : LinearMap.BilinForm ℤ X₀ := ζ₁.compl₁₂ m m
    have hζ : ∀ x₀ y₀, (k : ℤ) * ζ x₀ y₀ = v x₀ y₀ := by
      intro x₀ y₀
      obtain ⟨x, hx⟩ := hf (Submodule.Quotient.mk x₀)
      obtain ⟨y, hy⟩ := hf (Submodule.Quotient.mk y₀)
      have e1 : ζ x₀ y₀ = β' x y := by
        show ζ₁ (Submodule.Quotient.mk x₀) (Submodule.Quotient.mk y₀) = _
        rw [← hx, ← hy, hζ₁]
      rw [e1, hβ', H x y x₀ y₀ hx.symm hy.symm]
    have hmem : ζ ∈ balForms bar X₀ := by
      refine ⟨fun y z => hcan ?_, fun a y z => hcan ?_⟩
      · rw [hζ, hζ, hv.1]
      · rw [hζ, hζ, hv.2]
    refine hp k ⟨ζ, hmem⟩ (Subtype.ext (LinearMap.ext₂ fun x₀ y₀ => ?_))
    change v x₀ y₀ = ((k • ζ : LinearMap.BilinForm ℤ X₀)) x₀ y₀
    rw [LinearMap.smul_apply, LinearMap.smul_apply, nsmul_eq_mul, hζ]

end OrbMark

end GlobalTheory.PolFan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkedOrbitFormPrimitiveStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.markedOrbit_form_primitive : ∀ {O : Type} [CommRing O] (bar : O → O) (w0 : O) {X₀ : Type} [AddCommGroup X₀] [Module O X₀] (v : LinearMap.BilinForm ℤ X₀) (hv : v ∈ balForms bar X₀), IsPrim bar (⟨v, hv⟩ : balForms bar X₀) →
  ∀ {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (β : LinearMap.BilinForm ℤ X), (OrbMark.orbFun O w0 v).evalZ β = 1 →
    ∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = β → k = 1 := by
  first | exact @GlobalTheory.PolFan.OrbMark.eq_one_of_smul_eq_of_orbFun_evalZ_eq_one | exact GlobalTheory.PolFan.OrbMark.eq_one_of_smul_eq_of_orbFun_evalZ_eq_one | (intros; apply GlobalTheory.PolFan.OrbMark.eq_one_of_smul_eq_of_orbFun_evalZ_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimitiveBalancedFormFracCoordsOfCellMult
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimitiveBalancedFormFracCoordsOfCellMult
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.PolFan

namespace CentreChoice

variable {O : Type} [CommRing O] {bar : O → O} {X : Type} [AddCommGroup X] [Module O X]

theorem exists_isPrim_smul {x : balForms bar X} (hx : x ≠ 0) :
    ∃ (g : ℕ) (v : balForms bar X), 0 < g ∧ x = g • v ∧ IsPrim bar v := by
  classical
  obtain ⟨a, b, hab⟩ : ∃ a b, (x : LinearMap.BilinForm ℤ X) a b ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (Subtype.ext (LinearMap.ext₂ h))
  let S : Set ℕ := {g | 0 < g ∧ ∃ v : balForms bar X, x = g • v}
  have hS1 : 1 ∈ S := ⟨one_pos, x, (one_smul _ _).symm⟩
  have hbd : ∀ g ∈ S, g ≤ ((x : LinearMap.BilinForm ℤ X) a b).natAbs := by
    rintro g ⟨hg, v, hv⟩
    have e : (x : LinearMap.BilinForm ℤ X) a b = (g : ℤ) * (v : LinearMap.BilinForm ℤ X) a b := by
      rw [hv]
      simp
    rw [e] at hab ⊢
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    exact Nat.le_mul_of_pos_right _ (Int.natAbs_pos.2 (right_ne_zero_of_mul hab))
  have hB : BddAbove S := ⟨_, hbd⟩
  obtain ⟨hg, v, hv⟩ := Nat.sSup_mem ⟨1, hS1⟩ hB
  refine ⟨sSup S, v, hg, hv, fun j v' hj => ?_⟩
  have hj0 : j ≠ 0 := by
    rintro rfl
    apply hx
    rw [hv, hj, zero_smul, smul_zero]
  have hmem : sSup S * j ∈ S := ⟨Nat.mul_pos hg (Nat.pos_of_ne_zero hj0), v', by rw [hv, hj, mul_smul]⟩
  have h1 : sSup S * j ≤ sSup S * 1 := by simpa using le_csSup hB hmem
  have h2 := Nat.le_of_mul_le_mul_left h1 hg
  omega

theorem exists_isPrim_frac : ∀ {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) (M : ℕ) {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] {m : ℕ} (δ : Fin m → LinearMap.BilinForm ℤ X), IsMultCell bar φ M δ → 2 ≤ M →
  ∃ (v : LinearMap.BilinForm ℤ X) (hv : v ∈ balForms bar X), IsPrim bar (⟨v, hv⟩ : balForms bar X) ∧ (∀ y, 0 ≤ v y y) ∧
    ∃ t : Fin m → ℝ, (∀ i, 0 ≤ t i ∧ t i < 1) ∧ toReal v = ∑ i, t i • toReal (δ i) := by
  intro O _ bar φ M X _ _ _ m δ hδ h2
  classical
  obtain ⟨hc, -, -, hM⟩ := hδ
  let δ' : Fin m → balForms bar X := fun i => ⟨δ i, hc.mem i⟩
  let P := Submodule.span ℤ (Set.range δ')
  have hcard : 1 < Nat.card (Submodule.torsion ℤ (balForms bar X ⧸ P)) := by
    have : Nat.card (Submodule.torsion ℤ (balForms bar X ⧸ P)) = M := hM
    omega
  have hfin : Finite (Submodule.torsion ℤ (balForms bar X ⧸ P)) := Nat.finite_of_card_ne_zero (by omega)
  haveI := Finite.one_lt_card_iff_nontrivial.1 hcard
  obtain ⟨t, ht⟩ := exists_ne (0 : Submodule.torsion ℤ (balForms bar X ⧸ P))
  obtain ⟨⟨a, ha⟩, hat⟩ := (Submodule.mem_torsion_iff _).1 t.2
  obtain ⟨x, hx⟩ := Submodule.mkQ_surjective P t.1
  have hxP : x ∉ P := fun h => ht (Subtype.ext (by rw [← hx]; exact (Submodule.Quotient.mk_eq_zero P).2 h))
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have h1 : a • x ∈ P := (Submodule.Quotient.mk_eq_zero P).1 (by
    rw [Submodule.Quotient.mk_smul, ← Submodule.mkQ_apply, hx]; exact hat)
  have hk : 0 < a.natAbs := Int.natAbs_pos.2 ha0
  have hkx : (a.natAbs : ℤ) • x ∈ P := by
    rcases Int.natAbs_eq a with h | h
    · rwa [h] at h1
    · rw [h, neg_smul] at h1
      exact P.neg_mem_iff.1 h1
  obtain ⟨c, hc'⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hkx
  set k : ℕ := a.natAbs with hkdef
  have hkZ : (0 : ℤ) < k := by exact_mod_cast hk
  let x' : balForms bar X := x - ∑ i, (c i / k) • δ' i
  have hsP : ∑ i, (c i / k) • δ' i ∈ P :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hx'0 : x' ≠ 0 := fun h => hxP (by
    have : x = x' + ∑ i, (c i / k) • δ' i := by simp [x']
    rw [this, h, zero_add]; exact hsP)
  have hkx' : (k : ℤ) • x' = ∑ i, (c i % k) • δ' i := by
    simp only [x', smul_sub, Finset.smul_sum, smul_smul, ← hc']
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← sub_smul]
    congr 1
    have := Int.mul_ediv_add_emod (c i) k
    linarith
  obtain ⟨g, v, hg, hxv, hprim⟩ := exists_isPrim_smul hx'0
  have hr0 : ∀ i, 0 ≤ c i % k := fun i => Int.emod_nonneg _ hkZ.ne'
  have hr1 : ∀ i, c i % k < k := fun i => Int.emod_lt_of_pos _ hkZ
  have key : ∀ a b, ((k : ℤ) * g) * (v : LinearMap.BilinForm ℤ X) a b = ∑ i, (c i % k) * δ i a b := by
    intro a b
    have e := congrArg (fun z : balForms bar X => (z : LinearMap.BilinForm ℤ X) a b) hkx'
    simp only [hxv] at e
    simpa [Submodule.coe_sum, LinearMap.sum_apply, δ', mul_assoc] using e
  have hkg : (0 : ℤ) < (k : ℤ) * g := mul_pos hkZ (by exact_mod_cast hg)
  refine ⟨v, v.2, hprim, fun y => ?_, fun i => ((c i % k : ℤ) : ℝ) / ((k : ℝ) * g), fun i => ⟨?_, ?_⟩, ?_⟩
  · have hs : 0 ≤ ∑ i, (c i % k) * δ i y y :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hr0 i) (hc.nonneg i y)
    rw [← key] at hs
    exact nonneg_of_mul_nonneg_right hs hkg
  · have : (0 : ℝ) < (k : ℝ) * g := by exact_mod_cast hkg
    exact div_nonneg (by exact_mod_cast hr0 i) this.le
  · have : (0 : ℝ) < (k : ℝ) * g := by exact_mod_cast hkg
    rw [div_lt_one this]
    have : c i % k < (k : ℤ) * g := lt_of_lt_of_le (hr1 i) (le_mul_of_one_le_right hkZ.le (by exact_mod_cast hg))
    exact_mod_cast this
  · have hpos : (0 : ℝ) < (k : ℝ) * g := by exact_mod_cast hkg
    refine LinearMap.ext₂ fun a b => ?_
    have e : ((k : ℝ) * g) * ((v : LinearMap.BilinForm ℤ X) a b : ℝ) = ∑ i, ((c i % k : ℤ) : ℝ) * (δ i a b : ℝ) := by
      exact_mod_cast key a b
    simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [← mul_right_inj' hpos.ne', e, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp

end CentreChoice

end GlobalTheory.PolFan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimitiveBalancedFormFracCoordsOfCellMultStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primitiveBalancedForm_fracCoords_of_cellMult : ∀ {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) (M : ℕ) {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] {m : ℕ} (δ : Fin m → LinearMap.BilinForm ℤ X), IsMultCell bar φ M δ → 2 ≤ M →
  ∃ (v : LinearMap.BilinForm ℤ X) (hv : v ∈ balForms bar X), IsPrim bar (⟨v, hv⟩ : balForms bar X) ∧ (∀ y, 0 ≤ v y y) ∧
    ∃ t : Fin m → ℝ, (∀ i, 0 ≤ t i ∧ t i < 1) ∧ toReal v = ∑ i, t i • toReal (δ i) := by
  first | exact @GlobalTheory.PolFan.CentreChoice.exists_isPrim_frac | exact GlobalTheory.PolFan.CentreChoice.exists_isPrim_frac | (intros; apply GlobalTheory.PolFan.CentreChoice.exists_isPrim_frac <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriesExistsMarkedFormInCone
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriesExistsMarkedFormInCone
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem carries_exists_marked : ∀ {O : Type} [CommRing O] (bar : O → O) (w0 : O) (c : FormFamily O) {X₀ : Type} [AddCommGroup X₀] [Module O X₀] [Module.Finite O X₀] {m : ℕ} (δ₀ : Fin m → LinearMap.BilinForm ℤ X₀) (v : LinearMap.BilinForm ℤ X₀) (t : Fin m → ℝ),
  v ∈ balForms bar X₀ → v ≠ 0 → (∀ y, 0 ≤ v y y) → c.Carries δ₀ → (∀ i, 0 ≤ t i) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m' : ℕ) (δ : Fin m' → LinearMap.BilinForm ℤ X), c.Carries δ →
    ∃ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) ∧ (OrbMark.orbFun O w0 v).evalZ β = 1 ∧ InRCone δ β := by
  intro O _ bar w0 c X₀ _ _ _ m δ₀ v t hbal hv hpos hc₀ ht hsum X _ _ _ m' δ hc
  obtain ⟨e₀, s₀, hδ₀⟩ := hc₀
  obtain ⟨e, s, hδ⟩ := hc
  set g : X ≃ₗ[O] X₀ := e.trans e₀.symm with hg
  refine ⟨pull g.toLinearMap v, pull_mem _ hbal, fun y => by simpa using hpos (g y), ?_, ?_⟩
  · rw [evalZ_pull _ g.surjective]
    exact OrbMark.orbFun_evalZ_self w0 hv hbal.1
  · refine ⟨fun j => t (s₀.symm (s j)), fun j => ht _, LinearMap.ext₂ fun a b => ?_⟩
    have h1 := LinearMap.congr_fun₂ hsum (g a) (g b)
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul] at h1 ⊢
    show ((v (g a) (g b) : ℤ) : ℝ) = _
    rw [h1]
    have key : ∀ i, (δ₀ i (g a) (g b) : ℝ) = (c.δ (s₀ i) (e a) (e b) : ℝ) := fun i => by
      rw [hδ₀ i, pull_apply]; simp [hg]
    have key' : ∀ j, (δ j a b : ℝ) = (c.δ (s j) (e a) (e b) : ℝ) := fun j => by
      rw [hδ j, pull_apply]; rfl
    simp only [key, key']
    rw [← (s.trans s₀.symm).sum_comp]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp

end GlobalTheory.PolFan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriesExistsMarkedFormInConeStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carries_exists_marked_form_in_cone : ∀ {O : Type} [CommRing O] (bar : O → O) (w0 : O) (c : FormFamily O) {X₀ : Type} [AddCommGroup X₀] [Module O X₀] [Module.Finite O X₀] {m : ℕ} (δ₀ : Fin m → LinearMap.BilinForm ℤ X₀) (v : LinearMap.BilinForm ℤ X₀) (t : Fin m → ℝ),
  v ∈ balForms bar X₀ → v ≠ 0 → (∀ y, 0 ≤ v y y) → c.Carries δ₀ → (∀ i, 0 ≤ t i) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m' : ℕ) (δ : Fin m' → LinearMap.BilinForm ℤ X), c.Carries δ →
    ∃ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) ∧ (OrbMark.orbFun O w0 v).evalZ β = 1 ∧ InRCone δ β := by
  first | exact @GlobalTheory.PolFan.carries_exists_marked | exact GlobalTheory.PolFan.carries_exists_marked | (intros; apply GlobalTheory.PolFan.carries_exists_marked <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInvariantOrbitCentreMarkingPolyFan
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan.OrbMark

theorem centres_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ lab : InvFun (𝓞 E)),
    (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) →
    IsPolyFan H.bar q φ → IsTwInv H φ → IsTwInv H lab → SimpLab H.bar q φ lab → ∀ M : ℕ, 2 ≤ M →
    maxMult H.bar q φ ≤ M → ∀ c : FormFamily (𝓞 E),
    ∃ w : InvFun (𝓞 E), IsTwInv H w ∧ IsCentreSet H.bar q φ w ∧
      (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
        Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsMultCell H.bar φ M δ → c.Carries δ →
          ∃ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) ∧ w.evalZ β = 1 ∧ InRCone δ β) ∧
      (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
        Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell H.bar φ δ),
          LinearIndependent ℤ δ → (∀ i, IsPrim H.bar (⟨δ i, h.mem i⟩ : balForms H.bar X)) →
          ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 →
          ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal β = ∑ i, c i • toReal (δ i) → ∀ i, c i < 1) := by
  intro E _ _ _ H q φ lab _hdom _hfan hφ hlab hsl M hM _hmax c
  classical
  by_cases hex : ∃ (X : Type) (_ : AddCommGroup X) (_ : Module (𝓞 E) X) (_ : Module.Finite (𝓞 E) X)
      (_ : Module.Projective (𝓞 E) X), Module.finrank (𝓞 E) X ≤ q ∧
      ∃ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsMultCell H.bar φ M δ ∧ c.Carries δ
  · obtain ⟨X₀, _, _, _, _, -, m₀, δ₀, hM₀, hc₀⟩ := hex
    obtain ⟨v, hv, hvp, hvn, t, ht, htv⟩ := GlobalTheory.T.exists_primitiveBalancedForm_fracCoords_of_cellMult H.bar φ M δ₀ hM₀ hM
    obtain ⟨h₀, hli, hpr, -⟩ := hM₀
    have hv0 : v ≠ 0 := fun h => by
      have e : (⟨v, hv⟩ : balForms H.bar X₀) = 0 := Subtype.ext h
      rw [e] at hvp
      exact not_isPrim_zero hvp
    refine ⟨OrbMark.orbFun (𝓞 E) H.w0 v, OrbMark.isTwInv_orbFun H v,
      fun X _ _ _ _ hX => ⟨fun β _ _ => OrbMark.orbFun_eval_eq_zero_or_one _ _ _,
        fun β _ _ h1 => GlobalTheory.T.markedOrbit_form_primitive H.bar H.w0 v hv hvp β h1,
        fun m γ hγ β hβ hβp β' hβ' hβp' h1 h1' hc hc' =>
          GlobalTheory.T.eq_of_markedForms_in_same_cell_simplicialFan E H q φ lab hφ hlab hsl δ₀ h₀ hli hpr v t hv0 (fun i => (ht i).1) htv X hX m γ hγ β hβ hβp β' hβ' hβp'
            h1 h1' hc hc'⟩,
      fun X _ _ _ _ _ m δ _ hδ => ?_,
      fun X _ _ _ _ _ m δ h hδ hδp β hβ hβp h1 c' hc' hβc =>
        GlobalTheory.T.markedForm_coordinate_lt_one_in_primitiveCell E H φ hφ δ₀ h₀ hli hpr v t hv0 ht htv X m δ h hδ hδp β hβ hβp h1 c' hc' hβc⟩
    obtain ⟨β, hβ, hβp, h1, hin⟩ := GlobalTheory.T.carries_exists_marked_form_in_cone H.bar H.w0 c δ₀ v t hv hv0 hvn hc₀ (fun i => (ht i).1) htv X m δ hδ
    exact ⟨β, hβ, hβp, h1, hin⟩
  · refine ⟨zeroFun (𝓞 E), fun _ _ _ _ => rfl, fun X _ _ _ _ _ =>
      ⟨fun β _ _ => Or.inl (zeroFun_evalZ β), fun β _ _ h => by simp at h,
        fun _ _ _ β _ _ _ _ _ h => by simp at h⟩,
      fun X _ _ _ _ hX m δ hδ hc => (hex ⟨X, inferInstance, inferInstance, inferInstance, inferInstance, hX, m, δ, hδ, hc⟩).elim,
      fun X _ _ _ _ _ m δ _ _ _ β _ _ h => by simp at h⟩

end GlobalTheory.PolFan.OrbMark
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInvariantOrbitCentreMarkingPolyFanStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_orbitCentre_marking_polyFan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ lab : InvFun (𝓞 E)),
    (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) →
    IsPolyFan H.bar q φ → IsTwInv H φ → IsTwInv H lab → SimpLab H.bar q φ lab → ∀ M : ℕ, 2 ≤ M →
    maxMult H.bar q φ ≤ M → ∀ c : FormFamily (𝓞 E),
    ∃ w : InvFun (𝓞 E), IsTwInv H w ∧ IsCentreSet H.bar q φ w ∧
      (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
        Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsMultCell H.bar φ M δ → c.Carries δ →
          ∃ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) ∧ w.evalZ β = 1 ∧ InRCone δ β) ∧
      (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
        Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell H.bar φ δ),
          LinearIndependent ℤ δ → (∀ i, IsPrim H.bar (⟨δ i, h.mem i⟩ : balForms H.bar X)) →
          ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 →
          ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal β = ∑ i, c i • toReal (δ i) → ∀ i, c i < 1) := by
  first | exact @GlobalTheory.PolFan.OrbMark.centres_exists | exact GlobalTheory.PolFan.OrbMark.centres_exists | (intros; apply GlobalTheory.PolFan.OrbMark.centres_exists <;> assumption)
end
