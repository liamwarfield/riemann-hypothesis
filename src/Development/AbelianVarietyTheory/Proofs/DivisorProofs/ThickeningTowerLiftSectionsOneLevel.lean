module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealEqSpanMonomialOfOrdersAlongCompleteDVR

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftSectionsNextThickeningStandardCharts
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftSectionsNextThickeningStandardCharts
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlg.LiftCech

variable {R : Type} [CommRing R]

theorem map_cst_rs {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (J : Ideal R) {U V : X.Opens}
    (h : V ≤ U) {x : Γ(X, U)} (hx : x ∈ J.map (cst f U)) : rs X h x ∈ J.map (cst f V) := by
  have h' := Ideal.mem_map_of_mem (rs X h) hx
  rw [Ideal.map_map] at h'
  have e : (rs X h).comp (cst f U) = cst f V := RingHom.ext fun r => rs_cst f h r
  rwa [e] at h'

theorem gs_sub' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a b : Γ(X, U)) :
    gs f y U (a - b) = gs f y U a - gs f y U b := by
  simp only [gs_eq f y U h, map_sub]

theorem gs_zero' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs
  split <;> simp

end GlobalTheory.FormalAlg.LiftCech


open GlobalTheory.FormalAlg.LiftCech in
theorem GlobalTheory.FormalAlg.lift_cech : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∀ (e k : ℕ), (∀ c : ∀ i j, Γ((Y (e + 1)).left, C.D (e + 1) i ⊓ C.D (e + 1) j), (∀ i j, c i j ∈ towerIdeal Y (e + 1) (I ^ (e + 1)) _) → (∀ i j l, rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) j) (c i j) + rs (Y (e + 1)).left (inf_le_left.trans inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k * rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) j ⊓ C.D (e + 1) l) (c j l) = rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) l) (c i l)) → ∃ a : ∀ i, Γ((Y (e + 1)).left, C.D (e + 1) i), (∀ i, a i ∈ towerIdeal Y (e + 1) (I ^ (e + 1)) _) ∧ ∀ i j, c i j = rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (a i) - rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k * rs (Y (e + 1)).left (inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) j) (a j)) → ∀ g : ∀ i j, Γ((Y (e + 1)).left, C.D (e + 1) i ⊓ C.D (e + 1) j)ˣ, (⟨Fin (n + 1), C.D (e + 1), g⟩ : LB (Y (e + 1)).left).IsLB → (∀ i j, (g i j).val - rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k ∈ towerIdeal Y (e + 1) I _) → ∀ σ : ∀ i, Γ((Y e).left, β e ⁻¹ᵁ C.D (e + 1) i), (∀ z i j, β e z ∈ C.D (e + 1) i → β e z ∈ C.D (e + 1) j → gs (𝟙 _) z _ (σ i) = gs (β e) z _ (g i j).val * gs (𝟙 _) z _ (σ j)) → ∃ σ' : LB.Sec (⟨Fin (n + 1), C.D (e + 1), g⟩ : LB (Y (e + 1)).left), ∀ i, ((β e).app (C.D (e + 1) i)).hom (σ'.f i) = σ i := by
  intro R _ I Y β hβ n C e k hH g hg hgρ σ hσ
  have hbp := (GlobalTheory.T.isPullback_thick_tower_squares R I Y β hβ).1 e
  have hk := GlobalTheory.T.baseChange_quotient_closedImmersion_idealSheaf R (I ^ (e + 1)) _ _ _ (β e) (Y e).hom hbp
  have hbas := (GlobalTheory.T.thickeningTower_liftedRatios_projective_relations R I Y β hβ n C).1 (e + 1)
  have hz := (GlobalTheory.T.thickeningTower_liftedRatios_generate_surjective R I Y β hβ n C).1 (e + 1)
  have hA : ∀ i j, IsAffineOpen (C.D (e + 1) i ⊓ C.D (e + 1) j) := fun i j =>
    hbas i j ▸ (C.aff (e + 1) i).basicOpen _
  have hker : ∀ (V : (Y (e + 1)).left.Opens), IsAffineOpen V → ∀ x,
      ((β e).app V).hom x = 0 ↔ x ∈ towerIdeal Y (e + 1) (I ^ (e + 1)) V := fun V hV x => by
    rw [← RingHom.mem_ker, (hk.2.2 V hV).2]; rfl
  have hmem : ∀ (J : Ideal R) {U V : (Y (e + 1)).left.Opens} (h : V ≤ U) {x : Γ((Y (e + 1)).left, U)},
      x ∈ towerIdeal Y (e + 1) J U → rs (Y (e + 1)).left h x ∈ towerIdeal Y (e + 1) J V :=
    fun J _ _ h _ hx => map_cst_rs _ J h hx
  have hmul : ∀ (V : (Y (e + 1)).left.Opens) (x y : Γ((Y (e + 1)).left, V)), x ∈ towerIdeal Y (e + 1) I V →
      y ∈ towerIdeal Y (e + 1) (I ^ (e + 1)) V → x * y = 0 := by
    intro V x y hx hy
    have h := Ideal.mul_mem_mul hx hy
    unfold towerIdeal at h
    rw [← Ideal.map_mul, ← pow_succ'] at h
    have h0 := hz V
    unfold towerIdeal at h0
    rw [h0] at h
    exact (Submodule.mem_bot _).1 h
  choose τ hτ using fun i => (hk.2.2 _ (C.aff (e + 1) i)).1 (σ i)
  have key : ∀ (x : (Y e).left) i, β e x ∈ C.D (e + 1) i →
      gs (β e) x (C.D (e + 1) i) (τ i) = gs (𝟙 _) x _ (σ i) := fun x i hxi => by
    rw [← hτ i, gs_pull (𝟙 _) (β e) x _ hxi, Category.id_comp]
  let c : ∀ i j, Γ((Y (e + 1)).left, C.D (e + 1) i ⊓ C.D (e + 1) j) := fun i j =>
    rs _ (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (τ i) -
      (g i j).val * rs _ (inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) j) (τ j)
  have hcdef : ∀ i j, c i j = rs _ (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (τ i) -
      (g i j).val * rs _ (inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) j) (τ j) := fun _ _ => rfl
  have hc : ∀ i j, c i j ∈ towerIdeal Y (e + 1) (I ^ (e + 1)) _ := by
    intro i j
    rw [← hker _ (hA i j)]
    apply fn_ext
    intro x hx
    have hxi : β e x ∈ C.D (e + 1) i := hx.1
    have hxj : β e x ∈ C.D (e + 1) j := hx.2
    rw [gs_pull (𝟙 _) (β e) x _ hx, Category.id_comp, gs_zero',
      hcdef, gs_sub' _ _ _ hx, gs_mul _ _ _ hx, gs_res _ _ _ hx, gs_res _ _ _ hx, key x i hxi, key x j hxj,
      hσ x i j hxi hxj, sub_self]
  have hcoc : ∀ i j l, rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) j) (c i j) + rs (Y (e + 1)).left (inf_le_left.trans inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k * rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) j ⊓ C.D (e + 1) l) (c j l) = rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) l) (c i l) := by
    intro i j l
    have h1 : rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) j) (g i j).val * rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) j ⊓ C.D (e + 1) l) (c j l) = rs (Y (e + 1)).left (inf_le_left.trans inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k * rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) j ⊓ C.D (e + 1) l) (c j l) := by
      rw [← sub_eq_zero, ← sub_mul]
      refine hmul _ _ _ ?_ (hmem _ _ (hc j l))
      have h := hmem I (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) j) (hgρ i j)
      rwa [map_sub, map_pow, rs_rs] at h
    have hco := congrArg Units.val (hg.cocycle i j l)
    simp only [res, Units.val_mul, Units.coe_map, MonoidHom.coe_coe] at hco
    rw [← h1, hcdef, hcdef, hcdef]
    simp only [map_sub, map_mul, rs_rs]
    linear_combination (-(rs (Y (e + 1)).left (inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) l) (τ l))) * hco
  obtain ⟨a, ha, hca⟩ := hH c hc hcoc
  refine ⟨⟨fun i => τ i - a i, fun i j => ?_⟩, fun i => ?_⟩
  · have h2 : (g i j).val * rs (Y (e + 1)).left (inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) j) (a j) = rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k * rs (Y (e + 1)).left (inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) j) (a j) := by
      rw [← sub_eq_zero, ← sub_mul]
      exact hmul _ _ _ (hgρ i j) (hmem _ _ (ha j))
    have h3 := hca i j
    rw [hcdef] at h3
    change rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (τ i - a i) = (g i j).val * rs (Y (e + 1)).left (inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) j) (τ j - a j)
    rw [map_sub, map_sub]
    linear_combination h3 + h2
  · change ((β e).app (C.D (e + 1) i)).hom (τ i - a i) = σ i
    rw [map_sub, hτ i, (hker _ (C.aff (e + 1) i) (a i)).2 (ha i), sub_zero]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftSectionsNextThickeningStandardChartsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_sections_next_thickening_standardCharts : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∀ (e k : ℕ), (∀ c : ∀ i j, Γ((Y (e + 1)).left, C.D (e + 1) i ⊓ C.D (e + 1) j), (∀ i j, c i j ∈ towerIdeal Y (e + 1) (I ^ (e + 1)) _) → (∀ i j l, rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) j) (c i j) + rs (Y (e + 1)).left (inf_le_left.trans inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k * rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) j ⊓ C.D (e + 1) l) (c j l) = rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) l) (c i l)) → ∃ a : ∀ i, Γ((Y (e + 1)).left, C.D (e + 1) i), (∀ i, a i ∈ towerIdeal Y (e + 1) (I ^ (e + 1)) _) ∧ ∀ i j, c i j = rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (a i) - rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k * rs (Y (e + 1)).left (inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) j) (a j)) → ∀ g : ∀ i j, Γ((Y (e + 1)).left, C.D (e + 1) i ⊓ C.D (e + 1) j)ˣ, (⟨Fin (n + 1), C.D (e + 1), g⟩ : LB (Y (e + 1)).left).IsLB → (∀ i j, (g i j).val - rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k ∈ towerIdeal Y (e + 1) I _) → ∀ σ : ∀ i, Γ((Y e).left, β e ⁻¹ᵁ C.D (e + 1) i), (∀ z i j, β e z ∈ C.D (e + 1) i → β e z ∈ C.D (e + 1) j → gs (𝟙 _) z _ (σ i) = gs (β e) z _ (g i j).val * gs (𝟙 _) z _ (σ j)) → ∃ σ' : LB.Sec (⟨Fin (n + 1), C.D (e + 1), g⟩ : LB (Y (e + 1)).left), ∀ i, ((β e).app (C.D (e + 1) i)).hom (σ'.f i) = σ i := by
  first | exact @GlobalTheory.FormalAlg.lift_cech | exact GlobalTheory.FormalAlg.lift_cech | (intros; apply GlobalTheory.FormalAlg.lift_cech <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartCocycleOfPullbackPowerStandard
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLineBundleOfCompatibleLocalFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLineBundleOfCompatibleLocalFrames
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

namespace GlobalTheory.FramesBundle

theorem cg_cancel {G : Type} [CommGroup G] (a b c : G) : (a * b) * (a * c)⁻¹ = b * c⁻¹ := by
  apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel

theorem cg_cocycle {G : Type} [CommGroup G] (a b c : G) : (b * a⁻¹) * (c * b⁻¹) = c * a⁻¹ := by
  apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel

theorem cg_gen {G : Type} [CommGroup G] (a g c : G) : a⁻¹ = ((g * c) * a⁻¹ * g⁻¹) * c⁻¹ := by
  apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel

theorem frames_bundle : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (n : ℕ) (D : Fin (n + 1) → X.Opens), ⨆ i, D i = ⊤ → ∀ (τ : ∀ (i : Fin (n + 1)) (m : L.ι), Γ(X, D i ⊓ L.U m)ˣ), (∀ i x m m', x ∈ D i ⊓ L.U m → x ∈ D i ⊓ L.U m' → gm (𝟙 X) x _ (τ i m) = gm (𝟙 X) x _ (L.g m m') * gm (𝟙 X) x _ (τ i m')) → ∃ g : ∀ i j, Γ(X, D i ⊓ D j)ˣ, (⟨Fin (n + 1), D, g⟩ : LB X).IsLB ∧ LBIso L ⟨Fin (n + 1), D, g⟩ ∧ ∀ i j m, res (inf_le_left : D i ⊓ D j ⊓ L.U m ≤ D i ⊓ D j) (g i j) = res (le_inf (inf_le_left.trans inf_le_right) inf_le_right : D i ⊓ D j ⊓ L.U m ≤ D j ⊓ L.U m) (τ j m) * (res (le_inf (inf_le_left.trans inf_le_left) inf_le_right : D i ⊓ D j ⊓ L.U m ≤ D i ⊓ L.U m) (τ i m))⁻¹ := by
  intro X L hL n D hD τ hτ
  have hg : ∀ i j, ∃ s : Γ(X, D i ⊓ D j)ˣ, ∀ m,
      res (inf_le_left : D i ⊓ D j ⊓ L.U m ≤ D i ⊓ D j) s =
        res (le_inf (inf_le_left.trans inf_le_right) inf_le_right : D i ⊓ D j ⊓ L.U m ≤ D j ⊓ L.U m) (τ j m) *
          (res (le_inf (inf_le_left.trans inf_le_left) inf_le_right : D i ⊓ D j ⊓ L.U m ≤ D i ⊓ L.U m) (τ i m))⁻¹ := by
    intro i j
    refine glue_unit (D i ⊓ D j) (fun m => D i ⊓ D j ⊓ L.U m) (fun m => inf_le_left) ?_ _ ?_
    · intro x hx
      obtain ⟨m, hm⟩ := exists_chart hL x
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨m, ⟨hx, hm⟩⟩
    · intro m m' x hx
      rw [map_mul, map_mul, map_inv, map_inv, gm_res _ x _ hx.1, gm_res _ x _ hx.1, gm_res _ x _ hx.2,
        gm_res _ x _ hx.2, hτ j x m m' ⟨hx.1.1.2, hx.1.2⟩ ⟨hx.2.1.2, hx.2.2⟩,
        hτ i x m m' ⟨hx.1.1.1, hx.1.2⟩ ⟨hx.2.1.1, hx.2.2⟩, cg_cancel]
  choose g hg' using hg
  have key : ∀ i j m x, x ∈ D i ⊓ D j ⊓ L.U m →
      gm (𝟙 X) x (D i ⊓ D j) (g i j) = gm (𝟙 X) x (D j ⊓ L.U m) (τ j m) * (gm (𝟙 X) x (D i ⊓ L.U m) (τ i m))⁻¹ := by
    intro i j m x hx
    rw [← gm_res _ x (inf_le_left : D i ⊓ D j ⊓ L.U m ≤ D i ⊓ D j) hx, hg' i j m, map_mul, map_inv,
      gm_res _ x _ hx, gm_res _ x _ hx]
  refine ⟨g, ⟨hD, ?_, ?_⟩, ⟨⟨fun p => (τ p.1 p.2)⁻¹⟩, ?_⟩, hg'⟩
  · intro i
    apply unit_ext
    intro x hx
    rw [gm_res _ x _ hx, map_one]
    obtain ⟨m, hm⟩ := exists_chart hL x
    exact (key i i m x ⟨⟨hx, hx⟩, hm⟩).trans (mul_inv_cancel _)
  · intro i j k
    apply unit_ext
    intro x hx
    rw [map_mul, gm_res _ x _ hx, gm_res _ x _ hx, gm_res _ x _ hx]
    obtain ⟨m, hm⟩ := exists_chart hL x
    have h1 := key i j m x ⟨⟨hx.1.1, hx.1.2⟩, hm⟩
    have h2 := key j k m x ⟨⟨hx.1.2, hx.2⟩, hm⟩
    have h3 := key i k m x ⟨⟨hx.1.1, hx.2⟩, hm⟩
    exact (congrArg₂ (· * ·) h1 h2).trans ((cg_cocycle _ _ _).trans h3.symm)
  · rintro ⟨i, m⟩ ⟨j, m'⟩
    apply unit_ext
    intro x hx
    have hx' : x ∈ D i ⊓ L.U m ⊓ (D j ⊓ L.U m') := hx
    have eL : ∀ h : D i ⊓ L.U m ⊓ (D j ⊓ L.U m') ≤ D i ⊓ L.U m,
        gm (𝟙 X) x (D i ⊓ L.U m ⊓ (D j ⊓ L.U m')) (res h (τ i m)⁻¹) = (gm (𝟙 X) x _ (τ i m))⁻¹ := by
      intro h
      rw [map_inv, map_inv, gm_res _ x _ hx']
    have eR : ∀ (h1 : D i ⊓ L.U m ⊓ (D j ⊓ L.U m') ≤ D i ⊓ D j) (h2 : D i ⊓ L.U m ⊓ (D j ⊓ L.U m') ≤ L.U m ⊓ L.U m')
        (h3 : D i ⊓ L.U m ⊓ (D j ⊓ L.U m') ≤ D j ⊓ L.U m'),
        gm (𝟙 X) x (D i ⊓ L.U m ⊓ (D j ⊓ L.U m')) (res h1 (g i j) * (res h2 (L.g m m'))⁻¹ * res h3 (τ j m')⁻¹) =
          gm (𝟙 X) x _ (g i j) * (gm (𝟙 X) x _ (L.g m m'))⁻¹ * (gm (𝟙 X) x _ (τ j m'))⁻¹ := by
      intro h1 h2 h3
      rw [map_mul, map_mul, map_inv, map_inv, map_inv, gm_res _ x _ hx', gm_res _ x _ hx', gm_res _ x _ hx']
    have h1 := key i j m x ⟨⟨hx'.1.1, hx'.2.1⟩, hx'.1.2⟩
    have h2 := hτ j x m m' ⟨hx'.2.1, hx'.1.2⟩ ⟨hx'.2.1, hx'.2.2⟩
    refine (eL _).trans (Eq.trans ?_ (eR _ _ _).symm)
    rw [h1, h2]
    exact cg_gen _ _ _

end GlobalTheory.FramesBundle
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLineBundleOfCompatibleLocalFramesStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_lineBundle_of_compatible_local_frames : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (n : ℕ) (D : Fin (n + 1) → X.Opens), ⨆ i, D i = ⊤ → ∀ (τ : ∀ (i : Fin (n + 1)) (m : L.ι), Γ(X, D i ⊓ L.U m)ˣ), (∀ i x m m', x ∈ D i ⊓ L.U m → x ∈ D i ⊓ L.U m' → gm (𝟙 X) x _ (τ i m) = gm (𝟙 X) x _ (L.g m m') * gm (𝟙 X) x _ (τ i m')) → ∃ g : ∀ i j, Γ(X, D i ⊓ D j)ˣ, (⟨Fin (n + 1), D, g⟩ : LB X).IsLB ∧ LBIso L ⟨Fin (n + 1), D, g⟩ ∧ ∀ i j m, res (inf_le_left : D i ⊓ D j ⊓ L.U m ≤ D i ⊓ D j) (g i j) = res (le_inf (inf_le_left.trans inf_le_right) inf_le_right : D i ⊓ D j ⊓ L.U m ≤ D j ⊓ L.U m) (τ j m) * (res (le_inf (inf_le_left.trans inf_le_left) inf_le_right : D i ⊓ D j ⊓ L.U m ≤ D i ⊓ L.U m) (τ i m))⁻¹ := by
  first | exact @GlobalTheory.FramesBundle.frames_bundle | exact GlobalTheory.FramesBundle.frames_bundle | (intros; apply GlobalTheory.FramesBundle.frames_bundle <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningTowerChartsPreimageAndGermPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningTowerChartsPreimageAndGermPullback
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false

namespace GlobalTheory.FormalAlg

theorem Charts.tower_preimage_germ : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (n : ℕ) (C : Charts I Y β n) (γ : ∀ e, (Y 0).left ⟶ (Y e).left), γ 0 = 𝟙 _ → (∀ e, γ e ≫ β e = γ (e + 1)) → ∀ (e : ℕ) (i : Fin (n + 1)), γ e ⁻¹ᵁ C.D e i = C.D 0 i ∧ ∀ (j : Fin (n + 1)) (z : (Y 0).left), z ∈ C.D 0 i → gs (γ e) z (C.D e i) (C.ρ e i j) = gs (𝟙 _) z (C.D 0 i) (C.ρ 0 i j) := by
  intro R _ I Y β n C γ h0 hγ e
  induction e with
  | zero =>
    intro i
    subst_vars
    refine ⟨?_, fun j z _ => ?_⟩
    · rw [h0]; rfl
    · rw [h0]
  | succ e ih =>
    intro i
    obtain ⟨hpre, hgerm⟩ := ih i
    have hp : γ (e + 1) ⁻¹ᵁ C.D (e + 1) i = C.D 0 i := by
      rw [← hγ e, Scheme.Hom.comp_preimage, C.pre, hpre]
    refine ⟨hp, fun j z hz => ?_⟩
    have hz' : γ e z ∈ C.D e i := by rw [← hpre] at hz; exact hz
    have hz'' : β e (γ e z) ∈ C.D (e + 1) i := by
      have : γ e z ∈ β e ⁻¹ᵁ C.D (e + 1) i := by rw [C.pre]; exact hz'
      exact this
    rw [← hgerm j z hz, ← C.ρ_pull e i j, ← hγ e, ← gs_pull (γ e) (β e) z _ hz'',
      ← gs_res (γ e) z (C.pre e i).ge hz']
    rfl

end GlobalTheory.FormalAlg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningTowerChartsPreimageAndGermPullbackStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickeningTowerCharts_preimage_and_germ_pullback : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (n : ℕ) (C : Charts I Y β n) (γ : ∀ e, (Y 0).left ⟶ (Y e).left), γ 0 = 𝟙 _ → (∀ e, γ e ≫ β e = γ (e + 1)) → ∀ (e : ℕ) (i : Fin (n + 1)), γ e ⁻¹ᵁ C.D e i = C.D 0 i ∧ ∀ (j : Fin (n + 1)) (z : (Y 0).left), z ∈ C.D 0 i → gs (γ e) z (C.D e i) (C.ρ e i j) = gs (𝟙 _) z (C.D 0 i) (C.ρ 0 i j) := by
  first | exact @GlobalTheory.FormalAlg.Charts.tower_preimage_germ | exact GlobalTheory.FormalAlg.Charts.tower_preimage_germ | (intros; apply GlobalTheory.FormalAlg.Charts.tower_preimage_germ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLocalUnitsAlongNilpotentThickening
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLocalUnitsAlongNilpotentThickening
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

namespace GlobalTheory.FormalAlg

theorem lift_localUnits_of_thickening :
    ∀ (R : Type) [CommRing R] (J : Ideal R) (X X₀ : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (γ : X₀ ⟶ X) (q : X₀ ⟶ Spec (CommRingCat.of (R ⧸ J))), IsPullback γ q f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) → Surjective γ → ∀ (L : LB X), L.IsLB → ∀ D : X.Opens, IsAffineOpen D → ∀ u : ∀ m : L.ι, Γ(X₀, γ ⁻¹ᵁ (D ⊓ L.U m))ˣ, (∀ z m m', γ z ∈ D ⊓ L.U m → γ z ∈ D ⊓ L.U m' → gm (𝟙 X₀) z _ (u m) = gm γ z _ (L.g m m') * gm (𝟙 X₀) z _ (u m')) → ∃ τ : ∀ m : L.ι, Γ(X, D ⊓ L.U m)ˣ, (∀ m, (γ.app (D ⊓ L.U m)).hom (τ m).val = (u m).val) ∧ ∀ x m m', x ∈ D ⊓ L.U m → x ∈ D ⊓ L.U m' → gm (𝟙 X) x _ (τ m) = gm (𝟙 X) x _ (L.g m m') * gm (𝟙 X) x _ (τ m') := by
  intro R _ J X X₀ f γ q hpb hsurj L hL D hD u hu
  have hLp := LB.isLB_pull hL γ
  let O : L.ι → X₀.Opens := fun m => γ ⁻¹ᵁ (D ⊓ L.U m)
  have hO : ∀ m, O m ≤ γ ⁻¹ᵁ D := fun m => γ.preimage_mono inf_le_left
  have hc : γ ⁻¹ᵁ D ≤ ⨆ m, O m := by
    intro z hz
    obtain ⟨m, hm⟩ := exists_chart hL (γ z)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨m, show γ z ∈ D ⊓ L.U m from ⟨hz, hm⟩⟩
  have hU : ∀ m, O m ≤ (L.pull γ).U (fun _ => m) := fun m z hz => mem_pull.2 hz.2

  have hg : ∀ z a b, γ z ∈ L.U a → γ z ∈ L.U b →
      gm (𝟙 X₀) z ((L.pull γ).U (fun _ => a) ⊓ (L.pull γ).U (fun _ => b))
        ((L.pull γ).g (fun _ => a) (fun _ => b)) = gm γ z _ (L.g a b) := by
    intro z a b ha hb
    have hp : (𝟙 X₀) z ∈ (L.pull γ).U (fun _ => a) ⊓ (L.pull γ).U (fun _ => b) :=
      ⟨mem_pull.2 ha, mem_pull.2 hb⟩
    show gm (𝟙 X₀) z _ (∏ _k : PUnit, (res _ (pullU γ _ (L.g a b))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    refine (gm_res (𝟙 X₀) z _ hp _).trans ((gm_pull (𝟙 X₀) γ z (L.U a ⊓ L.U b) ⟨ha, hb⟩ _).trans ?_)
    rw [Category.id_comp]
  have hcomp : ∀ a b, rs X₀ (inf_le_left : O a ⊓ O b ≤ O a) (u a).val =
      rs X₀ (inf_le_inf (hU a) (hU b)) ((L.pull γ).g (fun _ => a) (fun _ => b)).val *
        rs X₀ (inf_le_right : O a ⊓ O b ≤ O b) (u b).val := by
    intro a b
    have e : res (inf_le_left : O a ⊓ O b ≤ O a) (u a) =
        res (inf_le_inf (hU a) (hU b)) ((L.pull γ).g (fun _ => a) (fun _ => b)) *
          res (inf_le_right : O a ⊓ O b ≤ O b) (u b) := by
      apply unit_ext
      intro z hz
      have hz' : (𝟙 X₀) z ∈ O a ⊓ O b := hz
      rw [map_mul, gm_res _ z _ hz', gm_res _ z _ hz', gm_res _ z _ hz',
        hg z a b hz.1.2 hz.2.2]
      exact hu z a b hz.1 hz.2
    have e' := congrArg Units.val e
    simp only [Units.val_mul, GlobalTheory.LB.val_res] at e'
    exact e'
  obtain ⟨t, ht, -⟩ := SecOn.existsUnique_of_local hLp O hO hc (fun m _ => m) hU
    (fun m => (u m).val) hcomp
  obtain ⟨s, hs⟩ := secOn_pull_surjective_of_surjective R (R ⧸ J) (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective X X₀ f q γ hpb L hL D hD t
  have hcoord : ∀ m, (γ.app (D ⊓ L.U m)).hom (GlobalTheory.LB.coord s m) = (u m).val := by
    intro m
    have e := ht m
    rw [← hs] at e
    erw [SecOn.coord_pull γ s (fun _ => m), GlobalTheory.LB.resG_appLE] at e
    rw [Scheme.Hom.app_eq_appLE]
    exact e
  have hunit : ∀ m, IsUnit (GlobalTheory.LB.coord s m) := by
    intro m
    apply X.toRingedSpace.isUnit_of_isUnit_germ
    intro x hx
    obtain ⟨z, rfl⟩ := γ.surjective x
    apply isUnit_of_map_unit (γ.stalkMap z).hom
    erw [Scheme.Hom.germ_stalkMap_apply γ (D ⊓ L.U m) z hx, hcoord m]
    exact (u m).isUnit.map _
  refine ⟨fun m => (hunit m).unit, fun m => hcoord m, ?_⟩
  intro x m m' hx hx'
  have hi : D ⊓ L.U m ⊓ L.U m' ≤ D ⊓ L.U m := inf_le_left
  have hj : D ⊓ L.U m ⊓ L.U m' ≤ D ⊓ L.U m' := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hij : D ⊓ L.U m ⊓ L.U m' ≤ L.U m ⊓ L.U m' :=
    le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have e : res hi (hunit m).unit = res hij (L.g m m') * res hj (hunit m').unit := by
    apply Units.ext
    simp only [Units.val_mul, GlobalTheory.LB.val_res, IsUnit.unit_spec]
    exact SecOn.compat s m m' hi hj hij
  have hxx : (𝟙 X) x ∈ D ⊓ L.U m ⊓ L.U m' := ⟨hx, hx'.2⟩
  have e' := congrArg (gm (𝟙 X) x _) e
  rw [map_mul, gm_res _ x _ hxx, gm_res _ x _ hxx, gm_res _ x _ hxx] at e'
  exact e'

end GlobalTheory.FormalAlg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLocalUnitsAlongNilpotentThickeningStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_local_units_along_nilpotent_thickening : ∀ (R : Type) [CommRing R] (J : Ideal R) (X X₀ : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (γ : X₀ ⟶ X) (q : X₀ ⟶ Spec (CommRingCat.of (R ⧸ J))), IsPullback γ q f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) → Surjective γ → ∀ (L : LB X), L.IsLB → ∀ D : X.Opens, IsAffineOpen D → ∀ u : ∀ m : L.ι, Γ(X₀, γ ⁻¹ᵁ (D ⊓ L.U m))ˣ, (∀ z m m', γ z ∈ D ⊓ L.U m → γ z ∈ D ⊓ L.U m' → gm (𝟙 X₀) z _ (u m) = gm γ z _ (L.g m m') * gm (𝟙 X₀) z _ (u m')) → ∃ τ : ∀ m : L.ι, Γ(X, D ⊓ L.U m)ˣ, (∀ m, (γ.app (D ⊓ L.U m)).hom (τ m).val = (u m).val) ∧ ∀ x m m', x ∈ D ⊓ L.U m → x ∈ D ⊓ L.U m' → gm (𝟙 X) x _ (τ m) = gm (𝟙 X) x _ (L.g m m') * gm (𝟙 X) x _ (τ m') := by
  first | exact @GlobalTheory.FormalAlg.lift_localUnits_of_thickening | exact GlobalTheory.FormalAlg.lift_localUnits_of_thickening | (intros; apply GlobalTheory.FormalAlg.lift_localUnits_of_thickening <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalFramesOfPullbackPowerOnNonzeroLocus
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalFramesOfPullbackPowerOnNonzeroLocus
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section

namespace GlobalTheory.Div.FramePull

variable {X X₀ : Scheme.{0}}

theorem isUnit_res_of_le {V U : X₀.Opens} (f : Γ(X₀, U)) (h : V ≤ X₀.basicOpen f) :
    IsUnit ((X₀.presheaf.map (homOfLE (h.trans (X₀.basicOpen_le f))).op).hom f) := by
  have e : (X₀.presheaf.map (homOfLE (h.trans (X₀.basicOpen_le f))).op).hom f =
      (X₀.presheaf.map (homOfLE h).op).hom ((X₀.presheaf.map (homOfLE (X₀.basicOpen_le f)).op).hom f) := by
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl
  rw [e]
  exact (X₀.toRingedSpace.isUnit_res_basicOpen f).map _

theorem le_basicOpen {H : LB X₀} (s : LB.Sec H) (a : H.ι) :
    nonzeroLocus s ⊓ H.U a ≤ X₀.basicOpen (s.f a) := by
  rintro z ⟨hz, ha⟩
  obtain ⟨a', ha'⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
  have e := congrArg X₀.basicOpen (s.compat a a')
  rw [Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ (H.g a a').isUnit, Scheme.basicOpen_res,
    Scheme.basicOpen_res] at e
  have hm : z ∈ H.U a ⊓ H.U a' ⊓ X₀.basicOpen (s.f a) := by
    rw [e]; exact ⟨⟨ha, X₀.basicOpen_le _ ha'⟩, ⟨ha, X₀.basicOpen_le _ ha'⟩, ha'⟩
  exact hm.2

theorem gm_gen_div {M L' : LB X₀} {w : LB.Iso L' M} (hw : w.IsGen) (z : X₀) (p q : M.ι × L'.ι)
    (hp : z ∈ M.U p.1 ⊓ L'.U p.2) (hq : z ∈ M.U q.1 ⊓ L'.U q.2) :
    gm (𝟙 X₀) z _ (w.s p) = gm (𝟙 X₀) z (M.U p.1 ⊓ M.U q.1) (M.g p.1 q.1) *
      (gm (𝟙 X₀) z (L'.U p.2 ⊓ L'.U q.2) (L'.g p.2 q.2))⁻¹ * gm (𝟙 X₀) z _ (w.s q) := by
  have hm : z ∈ (LB.div M L').U p ⊓ (LB.div M L').U q := ⟨hp, hq⟩
  have := congrArg (gm (𝟙 X₀) z _) (hw p q)
  rw [gm_res _ z _ hm, map_mul, gm_res _ z _ hm] at this
  rw [this]
  refine congrArg (· * _) ?_
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ z _ hm _)
    ((map_inv _ _).trans (congrArg _ (gm_res _ z _ hm _))))

theorem gm_pull_g (L : LB X) (γ : X₀ ⟶ X) (z : X₀) (m m' : L.ι) (hm : γ z ∈ L.U m) (hm' : γ z ∈ L.U m') :
    gm (𝟙 X₀) z ((L.pull γ).U (fun _ => m) ⊓ (L.pull γ).U (fun _ => m'))
      ((L.pull γ).g (fun _ => m) (fun _ => m')) = gm γ z _ (L.g m m') := by
  have hp : z ∈ (L.pull γ).U (fun _ => m) ⊓ (L.pull γ).U (fun _ => m') := ⟨mem_pull.2 hm, mem_pull.2 hm'⟩
  show gm (𝟙 X₀) z _ (∏ _k : PUnit, (res _ (pullU γ _ (L.g m m'))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  refine (gm_res _ z _ hp _).trans ((gm_pull (𝟙 X₀) γ z (L.U m ⊓ L.U m') ⟨hm, hm'⟩ _).trans ?_)
  rw [Category.id_comp]

theorem grp₁ {M : Type} [CommGroup M] (G S W : M) (k : ℕ) :
    (G * S) ^ k * (G ^ (k : ℤ) * 1⁻¹ * W)⁻¹ = S ^ k * W⁻¹ := by
  rw [zpow_natCast, inv_one, mul_one, mul_pow, mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul]

theorem grp₂ {M : Type} [CommGroup M] (S Γ W : M) (k : ℕ) :
    S ^ k * ((1 : M) ^ (k : ℤ) * Γ⁻¹ * W)⁻¹ = Γ * (S ^ k * W⁻¹) := by
  rw [one_zpow, one_mul, mul_inv, inv_inv, mul_left_comm]

theorem frame_pull : ∀ (X X₀ : Scheme.{0}) (γ : X₀ ⟶ X) (H₀ : LB X₀) (s : LB.Sec H₀) (k : ℕ) (L : LB X), L.IsLB →
    H₀.IsLB → ∀ (w : LB.Iso (L.pull γ) (pw H₀ k)), w.IsGen → ∀ (D : X.Opens), γ ⁻¹ᵁ D = nonzeroLocus s →
    ∃ u : ∀ m : L.ι, Γ(X₀, γ ⁻¹ᵁ (D ⊓ L.U m))ˣ, (∀ z m m', γ z ∈ D ⊓ L.U m → γ z ∈ D ⊓ L.U m' →
      gm (𝟙 X₀) z _ (u m) = gm γ z _ (L.g m m') * gm (𝟙 X₀) z _ (u m')) ∧
      ∀ z m a, γ z ∈ D ⊓ L.U m → z ∈ H₀.U a →
        gs (𝟙 X₀) z _ (s.f a) ^ k = (gm (𝟙 X₀) z _ (u m)).val * (gm (𝟙 X₀) z _ (w.s (a, fun _ => m))).val := by
  intro X X₀ γ H₀ s k L hL hH w hw D hD
  let W : L.ι → H₀.ι → X₀.Opens := fun m a => γ ⁻¹ᵁ (D ⊓ L.U m) ⊓ H₀.U a
  have hWb : ∀ m a, W m a ≤ X₀.basicOpen (s.f a) := fun m a z hz =>
    le_basicOpen s a ⟨hD ▸ (show z ∈ γ ⁻¹ᵁ D from hz.1.1), hz.2⟩
  have hWw : ∀ m a, W m a ≤ (LB.div (pw H₀ k) (L.pull γ)).U (a, fun _ => m) := fun m a z hz =>
    ⟨hz.2, mem_pull.2 hz.1.2⟩
  let S : ∀ m a, Γ(X₀, W m a)ˣ := fun m a => (isUnit_res_of_le (s.f a) (hWb m a)).unit
  let v : ∀ m a, Γ(X₀, W m a)ˣ := fun m a => S m a ^ k * (res (hWw m a) (w.s (a, fun _ => m)))⁻¹
  have hS : ∀ m a z (hz : z ∈ W m a), (gm (𝟙 X₀) z _ (S m a)).val = gs (𝟙 X₀) z _ (s.f a) := by
    intro m a z hz
    rw [← gs_unit _ z _ hz, IsUnit.unit_spec]
    exact gs_res _ z _ hz _
  have hv : ∀ m a z (hz : z ∈ W m a), gm (𝟙 X₀) z _ (v m a) =
      gm (𝟙 X₀) z _ (S m a) ^ k * (gm (𝟙 X₀) z _ (w.s (a, fun _ => m)))⁻¹ := by
    intro m a z hz
    simp only [v, map_mul, map_pow, map_inv]
    rw [gm_res _ z _ hz]

  have hwg : ∀ z a a' m m', z ∈ H₀.U a → z ∈ H₀.U a' → γ z ∈ L.U m → γ z ∈ L.U m' →
      gm (𝟙 X₀) z _ (w.s (a, fun _ => m)) = gm (𝟙 X₀) z (H₀.U a ⊓ H₀.U a') (H₀.g a a') ^ (k : ℤ) *
        (gm γ z _ (L.g m m'))⁻¹ * gm (𝟙 X₀) z _ (w.s (a', fun _ => m')) := by
    intro z a a' m m' ha ha' hm hm'
    rw [gm_gen_div hw z (a, fun _ => m) (a', fun _ => m') ⟨ha, mem_pull.2 hm⟩ ⟨ha', mem_pull.2 hm'⟩,
      gm_pull_g L γ z m m' hm hm']
    exact congrArg (fun t => t * _ * _) (map_zpow _ _ _)
  have hSg : ∀ m m' a a' z (hz : z ∈ W m a) (hz' : z ∈ W m' a'),
      gm (𝟙 X₀) z _ (S m a) = gm (𝟙 X₀) z (H₀.U a ⊓ H₀.U a') (H₀.g a a') * gm (𝟙 X₀) z _ (S m' a') := by
    intro m m' a a' z hz hz'
    apply Units.ext
    rw [Units.val_mul, hS m a z hz, hS m' a' z hz']
    exact gs_sec_chart s (𝟙 X₀) z hz.2 hz'.2
  have glue : ∀ m, ∃ t : Γ(X₀, γ ⁻¹ᵁ (D ⊓ L.U m))ˣ, ∀ a, res (inf_le_left : W m a ≤ _) t = v m a := by
    intro m
    refine glue_unit (γ ⁻¹ᵁ (D ⊓ L.U m)) (W m) (fun a => inf_le_left) (fun z hz => ?_) (v m) ?_
    · obtain ⟨a, ha⟩ := exists_chart hH z
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨a, hz, ha⟩
    · intro a a' z hz
      rw [hv m a z hz.1, hv m a' z hz.2, hSg m m a a' z hz.1 hz.2,
        hwg z a a' m m hz.1.2 hz.2.2 hz.1.1.2 hz.1.1.2, gm_self hL γ z hz.1.1.2]
      exact grp₁ _ _ _ k
  choose u hu using glue
  have hug : ∀ m a z (hz : z ∈ W m a), gm (𝟙 X₀) z _ (u m) = gm (𝟙 X₀) z _ (v m a) := by
    intro m a z hz
    rw [← hu m a, gm_res _ z _ hz]
  refine ⟨u, fun z m m' hm hm' => ?_, fun z m a hm ha => ?_⟩
  · obtain ⟨a, ha⟩ := exists_chart hH z
    have hz : z ∈ W m a := ⟨hm, ha⟩
    have hz' : z ∈ W m' a := ⟨hm', ha⟩
    rw [hug m a z hz, hug m' a z hz', hv m a z hz, hv m' a z hz', hSg m m' a a z hz hz',
      gm_self hH (𝟙 X₀) z ha, one_mul, hwg z a a m m' ha ha hm.2 hm'.2, gm_self hH (𝟙 X₀) z ha]
    exact grp₂ _ _ _ k
  · have hz : z ∈ W m a := ⟨hm, ha⟩
    rw [hug m a z hz, hv m a z hz, ← hS m a z hz, ← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_mul_cancel_right]

end GlobalTheory.Div.FramePull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalFramesOfPullbackPowerOnNonzeroLocusStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_frames_of_pullback_power_on_nonzeroLocus : ∀ (X X₀ : Scheme.{0}) (γ : X₀ ⟶ X) (H₀ : LB X₀) (s : LB.Sec H₀) (k : ℕ) (L : LB X), L.IsLB → H₀.IsLB → ∀ (w : LB.Iso (L.pull γ) (pw H₀ k)), w.IsGen → ∀ (D : X.Opens), γ ⁻¹ᵁ D = nonzeroLocus s → ∃ u : ∀ m : L.ι, Γ(X₀, γ ⁻¹ᵁ (D ⊓ L.U m))ˣ, (∀ z m m', γ z ∈ D ⊓ L.U m → γ z ∈ D ⊓ L.U m' → gm (𝟙 X₀) z _ (u m) = gm γ z _ (L.g m m') * gm (𝟙 X₀) z _ (u m')) ∧ ∀ z m a, γ z ∈ D ⊓ L.U m → z ∈ H₀.U a → gs (𝟙 X₀) z _ (s.f a) ^ k = (gm (𝟙 X₀) z _ (u m)).val * (gm (𝟙 X₀) z _ (w.s (a, fun _ => m))).val := by
  first | exact @GlobalTheory.Div.FramePull.frame_pull | exact GlobalTheory.Div.FramePull.frame_pull | (intros; apply GlobalTheory.Div.FramePull.frame_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartCocycleOfPullbackPowerStandard
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem GlobalTheory.FormalAlg.exists_chart_cocycle_of_pull : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∀ (H₀ : LB (Y 0).left) (s₀ : Fin (n + 1) → LB.Sec H₀), H₀.IsLB → ((∀ i, C.D 0 i = nonzeroLocus (s₀ i)) ∧ ∀ i j (m : H₀.ι), rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ j).f m) = rs (Y 0).left (inf_le_left : C.D 0 i ⊓ H₀.U m ≤ C.D 0 i) (C.ρ 0 i j) * rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ i).f m)) → ∀ γ : ∀ e, (Y 0).left ⟶ (Y e).left, γ 0 = 𝟙 _ → (∀ e, γ e ≫ β e = γ (e + 1)) → ∀ (e k : ℕ) (L : LB (Y e).left), L.IsLB → LBIso (L.pull (γ e)) (GlobalTheory.AbLaw.pw H₀ k) → ∃ g : ∀ i j, Γ((Y e).left, C.D e i ⊓ C.D e j)ˣ, (⟨Fin (n + 1), C.D e, g⟩ : LB (Y e).left).IsLB ∧ LBIso L ⟨Fin (n + 1), C.D e, g⟩ ∧ ∀ i j, (g i j).val - rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ k ∈ towerIdeal Y e I (C.D e i ⊓ C.D e j) := by
  rintro R _ I Y β hβ n C H₀ s₀ hH₀ ⟨hD, hρs⟩ γ hγ0 hγs e k L hL ⟨w, hw⟩
  have hpb : IsPullback (γ e) (Y 0).hom ((Y e).hom ≫ thick R I e) (thick R I 0) :=
    (GlobalTheory.T.isPullback_thick_tower_squares R I Y β hβ).2 γ hγ0 hγs e
  have hsurj : ∀ e, Surjective (γ e) := by
    intro e
    induction e with
    | zero => rw [hγ0]; infer_instance
    | succ e ih =>
      rw [← hγs e]
      have := MorphismProperty.of_isPullback (P := @Surjective) (hβ e).flip (GlobalTheory.GenSystem.surjective_thickTrans R I e)
      infer_instance
  have hpre := fun i => GlobalTheory.T.thickeningTowerCharts_preimage_and_germ_pullback R I Y β n C γ hγ0 hγs e i
  have hu := fun i => GlobalTheory.T.exists_local_frames_of_pullback_power_on_nonzeroLocus _ _ (γ e) H₀ (s₀ i) k L hL hH₀ w hw (C.D e i) ((hpre i).1.trans (hD i))
  choose u hu1 hu2 using hu
  have ht := fun i => GlobalTheory.T.lift_local_units_along_nilpotent_thickening R (I ^ (0 + 1)) (Y e).left (Y 0).left ((Y e).hom ≫ thick R I e) (γ e) (Y 0).hom
    hpb (hsurj e) L hL (C.D e i) (C.aff e i) (u i) (hu1 i)
  choose τ hτ1 hτ2 using ht
  obtain ⟨g, hgLB, hgIso, hg⟩ := GlobalTheory.T.cech_lineBundle_of_compatible_local_frames (Y e).left L hL n (C.D e) (C.cover e) τ hτ2
  refine ⟨g, hgLB, hgIso, fun i j => ?_⟩
  have hVaff : IsAffineOpen (C.D e i ⊓ C.D e j) := by
    have := (C.aff e i).basicOpen (C.ρ e i j)
    rwa [(GlobalTheory.T.thickeningTower_liftedRatios_projective_relations R I Y β hβ n C).1 e i j] at this
  obtain ⟨-, -, hker⟩ := GlobalTheory.T.baseChange_quotient_closedImmersion_idealSheaf R (I ^ (0 + 1)) (Y e).left (Y 0).left ((Y e).hom ≫ thick R I e) (γ e) (Y 0).hom hpb
  have hk := (hker _ hVaff).2

  have hτu : ∀ i m z (hz : γ e z ∈ C.D e i ⊓ L.U m), gm (γ e) z _ (τ i m) = gm (𝟙 _) z _ (u i m) := by
    intro i m z hz
    have h1 := gm_pull (𝟙 _) (γ e) z _ hz (τ i m)
    rw [Category.id_comp] at h1
    rw [← h1]
    congr 1
    exact Units.ext (hτ1 i m)
  have hmem : (g i j).val - rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ k ∈
      RingHom.ker ((γ e).app (C.D e i ⊓ C.D e j)).hom := by
    rw [RingHom.mem_ker]
    apply fn_ext
    intro z hz
    have hz' : γ e z ∈ C.D e i ⊓ C.D e j := hz
    obtain ⟨m, hm⟩ := exists_chart hL (γ e z)
    obtain ⟨a, ha⟩ := exists_chart hH₀ z
    have hzi : z ∈ C.D 0 i := (hpre i).1 ▸ hz'.1
    have hzj : z ∈ C.D 0 j := (hpre j).1 ▸ hz'.2
    have hm3 : γ e z ∈ C.D e i ⊓ C.D e j ⊓ L.U m := ⟨hz', hm⟩

    have hgz : gs (γ e) z _ (g i j).val = (gm (𝟙 _) z _ (u j m)).val * ((gm (𝟙 _) z _ (u i m))⁻¹).val := by
      rw [gs_unit _ z _ hz', ← gm_res (γ e) z (inf_le_left : C.D e i ⊓ C.D e j ⊓ L.U m ≤ C.D e i ⊓ C.D e j) hm3,
        hg i j m, map_mul, map_inv, gm_res _ z _ hm3, gm_res _ z _ hm3, hτu j m z ⟨hz'.2, hm⟩,
        hτu i m z ⟨hz'.1, hm⟩, Units.val_mul]

    have hsj := hu2 j z m a ⟨hz'.2, hm⟩ ha
    have hsi := hu2 i z m a ⟨hz'.1, hm⟩ ha
    have hrel : gs (𝟙 _) z _ ((s₀ j).f a) = gs (𝟙 _) z _ (C.ρ 0 i j) * gs (𝟙 _) z _ ((s₀ i).f a) := by
      have h := congrArg (gs (𝟙 _) z (C.D 0 i ⊓ H₀.U a)) (hρs i j a)
      have hmz : (𝟙 (Y 0).left) z ∈ C.D 0 i ⊓ H₀.U a := ⟨hzi, ha⟩
      rwa [gs_mul _ z _ hmz, gs_res _ z _ hmz, gs_res _ z _ hmz, gs_res _ z _ hmz] at h
    have hρz : gs (γ e) z _ (rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ k) =
        gs (𝟙 _) z _ (C.ρ 0 i j) ^ k := by
      rw [gs_eq _ z _ hz', map_pow, map_pow, ← gs_eq _ z _ hz', gs_res _ z _ hz', (hpre i).2 j z hzi]
    have hu' : (gm (𝟙 _) z _ (u j m)).val = gs (𝟙 _) z _ (C.ρ 0 i j) ^ k * (gm (𝟙 _) z _ (u i m)).val := by
      have hW := (gm (𝟙 (Y 0).left) z _ (w.s (a, fun _ => m))).isUnit
      apply hW.mul_left_cancel
      rw [mul_comm _ (gm (𝟙 _) z _ (u j m)).val, ← hsj, hrel, mul_pow, hsi]
      ring
    have hsub := gs_pull (𝟙 _) (γ e) z (C.D e i ⊓ C.D e j) hz' ((g i j).val - rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ k)
    rw [Category.id_comp] at hsub
    have h0 : gs (𝟙 _) z (γ e ⁻¹ᵁ (C.D e i ⊓ C.D e j)) 0 = 0 := by rw [gs_eq _ z _ hz, map_zero, map_zero]
    rw [h0, hsub, gs_eq _ z _ hz', map_sub, map_sub, ← gs_eq _ z _ hz', ← gs_eq _ z _ hz', hgz, hρz, hu']
    rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one, sub_self]
  rw [hk] at hmem
  simpa only [towerIdeal, zero_add, pow_one] using hmem
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartCocycleOfPullbackPowerStandardStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_chart_cocycle_of_pullback_power_standard : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∀ (H₀ : LB (Y 0).left) (s₀ : Fin (n + 1) → LB.Sec H₀), H₀.IsLB → ((∀ i, C.D 0 i = nonzeroLocus (s₀ i)) ∧ ∀ i j (m : H₀.ι), rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ j).f m) = rs (Y 0).left (inf_le_left : C.D 0 i ⊓ H₀.U m ≤ C.D 0 i) (C.ρ 0 i j) * rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ i).f m)) → ∀ γ : ∀ e, (Y 0).left ⟶ (Y e).left, γ 0 = 𝟙 _ → (∀ e, γ e ≫ β e = γ (e + 1)) → ∀ (e k : ℕ) (L : LB (Y e).left), L.IsLB → LBIso (L.pull (γ e)) (GlobalTheory.AbLaw.pw H₀ k) → ∃ g : ∀ i j, Γ((Y e).left, C.D e i ⊓ C.D e j)ˣ, (⟨Fin (n + 1), C.D e, g⟩ : LB (Y e).left).IsLB ∧ LBIso L ⟨Fin (n + 1), C.D e, g⟩ ∧ ∀ i j, (g i j).val - rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ k ∈ towerIdeal Y e I (C.D e i ⊓ C.D e j) := by
  first | exact @GlobalTheory.FormalAlg.exists_chart_cocycle_of_pull | exact GlobalTheory.FormalAlg.exists_chart_cocycle_of_pull | (intros; apply GlobalTheory.FormalAlg.exists_chart_cocycle_of_pull <;> assumption)
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section
namespace GlobalTheory.FormalAlg

theorem glue_chart {X X' : Scheme.{0}} (φ : X' ⟶ X) {M L' : LB X} {L : LB X'} (ω : LB.Iso L' M)
    (hω : ω.IsGen) (u : LB.Iso L (L'.pull φ)) (hu : PGen u) (hM : M.IsLB) (hL' : L'.IsLB) (hL : L.IsLB)
    (σ : LB.Sec L) (i : M.ι) :
    ∃ a : Γ(X', φ ⁻¹ᵁ M.U i), ∀ z b c, φ z ∈ M.U i → φ z ∈ L'.U b → z ∈ L.U c →
      gs (𝟙 _) z _ a = (gv ω φ z i b).val * ((gw u (𝟙 _) z b c).val * gs (𝟙 _) z _ (σ.f c)) := by
  let W : L'.ι × L.ι → X'.Opens := fun p => φ ⁻¹ᵁ (M.U i ⊓ L'.U p.1) ⊓ L.U p.2
  have l₀ : ∀ p, W p ≤ φ ⁻¹ᵁ M.U i := fun p x hx => hx.1.1
  have l₁ : ∀ p, W p ≤ φ ⁻¹ᵁ (M.U i ⊓ L'.U p.1) := fun p x hx => hx.1
  have l₂ : ∀ p, W p ≤ (L'.pull φ).U (fun _ => p.1) ⊓ L.U p.2 := fun p x hx => ⟨mem_pull.2 hx.1.2, hx.2⟩
  have l₃ : ∀ p, W p ≤ L.U p.2 := fun p x hx => hx.2
  have key : ∀ (y : X') (b b' : L'.ι) (c c' : L.ι), φ y ∈ M.U i → φ y ∈ L'.U b → φ y ∈ L'.U b' →
      y ∈ L.U c → y ∈ L.U c' →
      (gv ω φ y i b).val * ((gw u (𝟙 _) y b c).val * gs (𝟙 _) y _ (σ.f c)) =
        (gv ω φ y i b').val * ((gw u (𝟙 _) y b' c').val * gs (𝟙 _) y _ (σ.f c')) := by
    intro y b b' c c' hi hb hb' hc hc'
    have h1 := gm_isGen hω φ y i i b b' hi hi hb hb'
    have h2 := hu X' (𝟙 _) y b b' c c' hb hb' hc hc'
    have h3 := GlobalTheory.SecPullIso.gs_sec_trans σ (𝟙 _) y hc hc'
    rw [gm_self hM φ y hi, one_mul] at h1
    rw [Category.id_comp] at h2
    rw [h1, h2, h3]
    generalize gm φ y _ (L'.g b b') = B
    generalize gm (𝟙 X') y _ (L.g c c') = C
    generalize gv ω φ y i b' = D
    generalize gw u (𝟙 _) y b' c' = E
    generalize gs (𝟙 X') y _ (σ.f c') = s
    simp only [Units.val_mul]
    have hB := B.inv_mul
    have hC := C.inv_mul
    linear_combination ((D : _) * E * s * (C⁻¹ : _ˣ) * C) * hB + ((D : _) * E * s) * hC
  obtain ⟨v, hv⟩ : ∃ v : ∀ p, Γ(X', W p), ∀ z p, z ∈ W p →
      gs (𝟙 _) z (W p) (v p) = (gv ω φ z i p.1).val * ((gw u (𝟙 _) z p.1 p.2).val * gs (𝟙 _) z _ (σ.f p.2)) :=
    ⟨fun p => (res (l₁ p) (pullU φ _ (ω.s (i, p.1)))).val * ((res (l₂ p) (u.s (fun _ => p.1, p.2))).val *
        (X'.presheaf.map (homOfLE (l₃ p)).op).hom (σ.f p.2)), fun z p hz => by
      rw [gs_mul _ z _ hz, gs_mul _ z _ hz, gs_unit _ z _ hz, gs_unit _ z _ hz, gm_res (𝟙 X') z (l₁ p) hz,
        show gm (𝟙 X') z (W p) (res (l₂ p) (u.s (fun _ => p.1, p.2))) = gw u (𝟙 _) z p.1 p.2 from gm_res (𝟙 X') z (l₂ p) hz _, gs_res (𝟙 X') z (l₃ p) hz, show gm (𝟙 X') z (φ ⁻¹ᵁ (M.U i ⊓ L'.U p.1)) (pullU φ _ (ω.s (i, p.1))) = gv ω φ z i p.1 from
          (gm_pull (𝟙 _) φ z _ (l₁ p hz) _).trans (by rw [Category.id_comp]; rfl)]⟩
  obtain ⟨a, ha, -⟩ := X'.sheaf.existsUnique_gluing' W (φ ⁻¹ᵁ M.U i) (fun p => homOfLE (l₀ p)) (fun y hy => by
      obtain ⟨b, hb⟩ := exists_chart hL' (φ y)
      obtain ⟨c, hc⟩ := exists_chart hL y
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(b, c), ⟨hy, hb⟩, hc⟩) v
    (fun p q => fn_ext (V := W p ⊓ W q) fun y hy => by
      refine (gs_res (𝟙 _) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 _) y inf_le_right hy _).symm)
      rw [hv y p hy.1, hv y q hy.2]
      exact key y p.1 q.1 p.2 q.2 hy.1.1.1 hy.1.1.2 hy.2.1.2 hy.1.2 hy.2.2)
  refine ⟨a, fun z b c h₁ h₂ h₃ => ?_⟩
  have hz : z ∈ W (b, c) := ⟨⟨h₁, h₂⟩, h₃⟩
  exact (gs_res (𝟙 _) z (l₀ (b, c)) hz a).symm.trans ((congrArg (gs (𝟙 _) z (W (b, c))) (ha (b, c))).trans
    (hv z (b, c) hz))

theorem lift_step : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∀ (H₀ : LB (Y 0).left) (s₀ : Fin (n + 1) → LB.Sec H₀), H₀.IsLB → ((∀ i, C.D 0 i = nonzeroLocus (s₀ i)) ∧ ∀ i j (m : H₀.ι), rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ j).f m) = rs (Y 0).left (inf_le_left : C.D 0 i ⊓ H₀.U m ≤ C.D 0 i) (C.ρ 0 i j) * rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ i).f m)) → ∀ γ : ∀ e, (Y 0).left ⟶ (Y e).left, γ 0 = 𝟙 _ → (∀ e, γ e ≫ β e = γ (e + 1)) → ∀ (e k : ℕ), (∀ c : ∀ i j, Γ((Y (e + 1)).left, C.D (e + 1) i ⊓ C.D (e + 1) j), (∀ i j, c i j ∈ towerIdeal Y (e + 1) (I ^ (e + 1)) _) → (∀ i j l, rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) j) (c i j) + rs (Y (e + 1)).left (inf_le_left.trans inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k * rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) j ⊓ C.D (e + 1) l) (c j l) = rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) l) (c i l)) → ∃ a : ∀ i, Γ((Y (e + 1)).left, C.D (e + 1) i), (∀ i, a i ∈ towerIdeal Y (e + 1) (I ^ (e + 1)) _) ∧ ∀ i j, c i j = rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (a i) - rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k * rs (Y (e + 1)).left (inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) j) (a j)) → ∀ (L : LB (Y e).left) (L' : LB (Y (e + 1)).left) (u : LB.Iso L (L'.pull (β e))), L.IsLB → L'.IsLB → u.IsGen → LBIso (L'.pull (γ (e + 1))) (GlobalTheory.AbLaw.pw H₀ k) → ∀ σ : LB.Sec L, ∃ σ' : LB.Sec L', Rel (β e) u σ' σ := by
  intro R _ I Y β hβ n C H₀ s₀ hH₀ hs₀ γ hγ0 hγ e k hc L L' u hL hL' hu hpw σ
  obtain ⟨g, hMLB, ⟨ω, hω⟩, hcong⟩ := GlobalTheory.T.exists_chart_cocycle_of_pullback_power_standard R I Y β hβ n C H₀ s₀ hH₀ hs₀ γ hγ0 hγ (e + 1) k L' hL' hpw
  have hup : PGen u := (isGen_iff u).1 hu
  choose σi hσi using fun i => glue_chart (M := (⟨Fin (n + 1), C.D (e + 1), g⟩ : LB (Y (e + 1)).left)) (β e) ω hω u
    hup hMLB hL' hL σ i
  have hcoc : ∀ z i j, β e z ∈ C.D (e + 1) i → β e z ∈ C.D (e + 1) j →
      gs (𝟙 _) z _ (σi i) = gs (β e) z _ (g i j).val * gs (𝟙 _) z _ (σi j) := by
    intro z i j hi hj
    obtain ⟨b, hb⟩ := exists_chart hL' (β e z)
    obtain ⟨c, hc'⟩ := exists_chart hL z
    rw [hσi i z b c hi hb hc', hσi j z b c hj hb hc']
    have h1 := gm_isGen hω (β e) z i j b b hi hj hb hb
    rw [gm_self hL' (β e) z hb, inv_one, mul_one] at h1
    rw [h1, gs_unit (β e) z (C.D (e + 1) i ⊓ C.D (e + 1) j) ⟨hi, hj⟩, Units.val_mul, mul_assoc]
  obtain ⟨σ'', hσ''⟩ := GlobalTheory.T.lift_sections_next_thickening_standardCharts R I Y β hβ n C e k hc g hMLB hcong σi hcoc
  let w := isoPullId ω (F := 𝟙 _) rfl
  have hw : w.IsGen := (isGen_iff w).2 (isoPullId_pgen hω rfl)
  obtain ⟨σ', hσ'⟩ := GlobalTheory.SecPullIso.exists_pull (𝟙 _) _ L' w hMLB hL' hw σ''
  refine ⟨σ', fun z b c hb hc' => ?_⟩
  obtain ⟨i, hi⟩ := exists_chart hMLB (β e z)
  have hR : Rel (𝟙 _) w σ'' σ' := hσ'
  have e1 := hR.pull (β e) z i b hi hb
  rw [Category.comp_id, gw_isoPullId ω rfl (β e) z i b hi hb] at e1
  have e2 : gs (β e) z _ (σ''.f i) = gs (𝟙 _) z _ (σi i) := by
    rw [← hσ'' i, gs_pull (𝟙 _) (β e) z _ hi, Category.id_comp]
  rw [e2, hσi i z b c hi hb hc'] at e1
  exact ((Units.mul_right_inj (gv ω (β e) z i b)).1 e1).symm

end GlobalTheory.FormalAlg
