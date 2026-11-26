module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionDescendsEtaleCover
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsDescentSymmetricLinearisedBundle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspProdCharTransport

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpSchemeMonHomSquareLiftOneRight
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section
namespace GlobalTheory.UPel.HT.Hecke.PullInj

variable {X Y Z : Scheme.{0}}

theorem gen_germ {L : LB X} {w : LB.Gen L} (hw : w.IsGen) (r : Z ⟶ X) (z : Z) {k l : L.ι}
    (hk : r z ∈ L.U k) (hl : r z ∈ L.U l) :
    gm r z _ (w.s k) = gm r z (L.U k ⊓ L.U l) (L.g k l) * gm r z _ (w.s l) := by
  have hm : r z ∈ L.U k ⊓ L.U l := ⟨hk, hl⟩
  exact (gm_res r z inf_le_left hm _).symm.trans ((congrArg (gm r z _) (hw k l)).trans
    ((map_mul _ _ _).trans (congrArg _ (gm_res r z inf_le_right hm _))))

theorem gm_pull_g (Q : LB Y) (F : X ⟶ Y) (r : Z ⟶ X) (z : Z) {j j' : PUnit → Q.ι}
    (hj : F (r z) ∈ Q.U (j PUnit.unit)) (hj' : F (r z) ∈ Q.U (j' PUnit.unit)) :
    gm r z ((Q.pull F).U j ⊓ (Q.pull F).U j') ((Q.pull F).g j j') =
      gm (r ≫ F) z (Q.U (j PUnit.unit) ⊓ Q.U (j' PUnit.unit)) (Q.g (j PUnit.unit) (j' PUnit.unit)) := by
  have hp : r z ∈ (Q.pull F).U j ⊓ (Q.pull F).U j' := ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
  show gm r z _ (∏ _k : PUnit, (res _ (pullU F _ (Q.g _ _))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res r z _ hp _).trans (gm_pull r F z (Q.U (j PUnit.unit) ⊓ Q.U (j' PUnit.unit)) ⟨hj, hj'⟩ _)

theorem germ_div_g (M L : LB X) (r : Z ⟶ X) (z : Z) {p q : M.ι × L.ι}
    (hp : r z ∈ (LB.div M L).U p) (hq : r z ∈ (LB.div M L).U q) :
    gm r z _ ((LB.div M L).g p q) =
      gm r z (M.U p.1 ⊓ M.U q.1) (M.g p.1 q.1) * (gm r z (L.U p.2 ⊓ L.U q.2) (L.g p.2 q.2))⁻¹ := by
  have hm : r z ∈ (LB.div M L).U p ⊓ (LB.div M L).U q := ⟨hp, hq⟩
  show gm r z _ (res _ (M.g _ _) * (res _ (L.g _ _))⁻¹) = _
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hm _) ((map_inv _ _).trans (congrArg _ (gm_res r z _ hm _))))

theorem mem_divPull {Q₁ Q₂ : LB Y} {F : X ⟶ Y} {x : X} {k : (PUnit → Q₂.ι) × (PUnit → Q₁.ι)} :
    x ∈ (LB.div (Q₂.pull F) (Q₁.pull F)).U k ↔ F x ∈ Q₂.U (k.1 PUnit.unit) ∧ F x ∈ Q₁.U (k.2 PUnit.unit) :=
  ⟨fun h => ⟨mem_pull.1 h.1, mem_pull.1 h.2⟩, fun h => ⟨mem_pull.2 h.1, mem_pull.2 h.2⟩⟩

theorem gm_top_eq {S : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) (g : Γ(A.left, ⊤)ˣ)
    (r r' : Z ⟶ A.left) (e : r ≫ A.hom = r' ≫ A.hom) (z : Z) : gm r z ⊤ g = gm r' z ⊤ g := by
  obtain ⟨c, hc⟩ := (GlobalTheory.globalFns_holds S A hA).2 g.val
  have h1 : ∀ r₀ : Z ⟶ A.left, gs r₀ z ⊤ g.val = gs (r₀ ≫ A.hom) z ⊤ c := fun r₀ => by
    rw [← hc]; exact gs_pull r₀ A.hom z ⊤ trivial c
  apply Units.ext
  rw [← gs_unit r z ⊤ trivial, ← gs_unit r' z ⊤ trivial, h1, h1, e]

end GlobalTheory.UPel.HT.Hecke.PullInj

namespace GlobalTheory.UPel.HT.Hecke.PullInj

variable {S : Scheme.{0}}

theorem transl_axis₁ (A : Over S) [GrpObj A] [IsCommMonObj A] (h : 𝟙_ (Over S) ⟶ A) :
    lift (1 : A ⟶ A) (𝟙 A) ≫ transl (lift (1 : 𝟙_ (Over S) ⟶ A) h : 𝟙_ (Over S) ⟶ G2 A) =
      transl h ≫ lift (1 : A ⟶ A) (𝟙 A) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [transl, MonObj.mul_comp, MonObj.comp_mul]
  · simp [transl, MonObj.mul_comp, MonObj.comp_mul]

theorem transl_axis₂ (A : Over S) [GrpObj A] [IsCommMonObj A] (h : 𝟙_ (Over S) ⟶ A) :
    lift (𝟙 A) (1 : A ⟶ A) ≫ transl (lift h (1 : 𝟙_ (Over S) ⟶ A) : 𝟙_ (Over S) ⟶ G2 A) =
      transl h ≫ lift (𝟙 A) (1 : A ⟶ A) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [transl, MonObj.mul_comp, MonObj.comp_mul]
  · simp [transl, MonObj.mul_comp, MonObj.comp_mul]

theorem grpScheme_monHom_square_lift_one_left {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (ψ : A ⟶ A')
    [IsMonHom ψ] : lift (1 : A ⟶ A) (𝟙 A) ≫ lift (fst A A ≫ ψ) (snd A A ≫ ψ) = ψ ≫ lift (1 : A' ⟶ A') (𝟙 A') := by
  apply CartesianMonoidalCategory.hom_ext
  · simp
  · simp

theorem grpScheme_monHom_square_lift_one_right {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (ψ : A ⟶ A')
    [IsMonHom ψ] : lift (𝟙 A) (1 : A ⟶ A) ≫ lift (fst A A ≫ ψ) (snd A A ≫ ψ) = ψ ≫ lift (𝟙 A') (1 : A' ⟶ A') := by
  apply CartesianMonoidalCategory.hom_ext
  · simp
  · simp

end GlobalTheory.UPel.HT.Hecke.PullInj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorTranslateRatioGlobalUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorTranslateRatioGlobalUnit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT.Hecke.PullInj

noncomputable section
namespace GlobalTheory.UPel.HT.Hecke.PullInj

theorem gen_transl_ratio : ∀ (X X' : Scheme.{0}) (π : X ⟶ X') (Q₁ Q₂ : LB X'), Q₁.IsLB → Q₂.IsLB →
    ∀ (w : LB.Iso (Q₁.pull π) (Q₂.pull π)), w.IsGen → ∀ τ : X ⟶ X, τ ≫ π = π → ∃ f : Γ(X, ⊤)ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (k : (PUnit → Q₂.ι) × (PUnit → Q₁.ι)),
        r z ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k →
        gm (r ≫ τ) z _ (w.s k) = gm r z ⊤ f * gm r z _ (w.s k) := by
  intro X X' π Q₁ Q₂ hQ₁ hQ₂ w hw τ hτ
  have hπτ : ∀ x : X, π (τ x) = π x := fun x => by
    rw [← Scheme.Hom.comp_apply, hτ]
  have hmem : ∀ {x : X} {k : (PUnit → Q₂.ι) × (PUnit → Q₁.ι)},
      x ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k → τ x ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k := by
    intro x k hx
    rw [mem_divPull] at hx ⊢
    rw [hπτ]; exact hx
  have hle : ∀ k, (LB.div (Q₂.pull π) (Q₁.pull π)).U k ≤ τ ⁻¹ᵁ (LB.div (Q₂.pull π) (Q₁.pull π)).U k :=
    fun k x hx => hmem hx
  let u : ∀ k, Γ(X, (LB.div (Q₂.pull π) (Q₁.pull π)).U k)ˣ := fun k =>
    res (hle k) (pullU τ _ (w.s k)) * (w.s k)⁻¹
  have hu : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) k, r z ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k →
      gm r z _ (u k) = gm (r ≫ τ) z _ (w.s k) * (gm r z _ (w.s k))⁻¹ := by
    intro Z r z k hz
    show gm r z _ (res (hle k) (pullU τ _ (w.s k)) * (w.s k)⁻¹) = _
    rw [map_mul, map_inv, gm_res r z (hle k) hz, gm_pull r τ z _ (hmem hz)]
  have hg : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) k l, r z ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k →
      r z ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U l →
      gm (r ≫ τ) z _ ((LB.div (Q₂.pull π) (Q₁.pull π)).g k l) = gm r z _ ((LB.div (Q₂.pull π) (Q₁.pull π)).g k l) := by
    intro Z r z k l hk hl
    have hk' := hmem hk
    have hl' := hmem hl
    rw [germ_div_g _ _ (r ≫ τ) z hk' hl', germ_div_g _ _ r z hk hl]
    have hk₀ := mem_divPull.1 hk
    have hl₀ := mem_divPull.1 hl
    have hk₁ := mem_divPull.1 hk'
    have hl₁ := mem_divPull.1 hl'
    rw [gm_pull_g Q₂ π (r ≫ τ) z hk₁.1 hl₁.1, gm_pull_g Q₁ π (r ≫ τ) z hk₁.2 hl₁.2,
      gm_pull_g Q₂ π r z hk₀.1 hl₀.1, gm_pull_g Q₁ π r z hk₀.2 hl₀.2, Category.assoc, hτ]
  have hc : (⊤ : X.Opens) ≤ iSup (LB.div (Q₂.pull π) (Q₁.pull π)).U := by
    intro x _
    obtain ⟨i, hi⟩ := exists_chart hQ₂ (π x)
    obtain ⟨j, hj⟩ := exists_chart hQ₁ (π x)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(fun _ => i, fun _ => j), mem_divPull.2 ⟨hi, hj⟩⟩
  obtain ⟨f, hf⟩ := glue_unit (⊤ : X.Opens) (LB.div (Q₂.pull π) (Q₁.pull π)).U (fun _ => le_top) hc u (by
    intro k l x hx
    rw [hu _ _ _ k hx.1, hu _ _ _ l hx.2, gen_germ hw (𝟙 X ≫ τ) x (hmem hx.1) (hmem hx.2),
      gen_germ hw (𝟙 X) x hx.1 hx.2, hg _ _ _ k l hx.1 hx.2]
    simp only [← div_eq_mul_inv]
    exact mul_div_mul_left_eq_div _ _ _)
  refine ⟨f, fun Z r z k hz => ?_⟩
  rw [← gm_res r z (le_top : (LB.div (Q₂.pull π) (Q₁.pull π)).U k ≤ ⊤) hz f, hf k, hu Z r z k hz,
    inv_mul_cancel_right]

end GlobalTheory.UPel.HT.Hecke.PullInj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorTranslateRatioGlobalUnitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT.Hecke.PullInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generator_translate_ratio_global_unit : ∀ (X X' : Scheme.{0}) (π : X ⟶ X') (Q₁ Q₂ : LB X'), Q₁.IsLB → Q₂.IsLB → ∀ (w : LB.Iso (Q₁.pull π) (Q₂.pull π)), w.IsGen → ∀ τ : X ⟶ X, τ ≫ π = π → ∃ f : Γ(X, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (k : (PUnit → Q₂.ι) × (PUnit → Q₁.ι)), r z ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k → gm (r ≫ τ) z _ (w.s k) = gm r z ⊤ f * gm r z _ (w.s k) := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.PullInj.gen_transl_ratio) | (exact GlobalTheory.UPel.HT.Hecke.PullInj.gen_transl_ratio) | (intros; apply GlobalTheory.UPel.HT.Hecke.PullInj.gen_transl_ratio  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAxisUnitGeneratorsPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAxisUnitGeneratorsPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT.Hecke.PullInj

noncomputable section
namespace GlobalTheory.UPel.HT.Hecke.PullInj

theorem mul_inv_axis_comm_identity {G : Type*} [CommGroup G] (a b W R₁ R₂ : G) :
    a * b⁻¹ * W * (b * R₁) * (a * R₂)⁻¹ = W * R₁ * R₂⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem axis_unit : ∀ (A₀ A₀' X X' : Scheme.{0}) (ψ : A₀ ⟶ A₀') (e : A₀ ⟶ X) (e' : A₀' ⟶ X') (π : X ⟶ X'),
    e ≫ π = ψ ≫ e' → ∀ (Q₁ Q₂ : LB X'), Q₁.IsLB → Q₂.IsLB → ∀ (w : LB.Iso (Q₁.pull π) (Q₂.pull π)), w.IsGen →
    ∀ (ρ₁ : LB.Gen (Q₁.pull e')) (ρ₂ : LB.Gen (Q₂.pull e')), ρ₁.IsGen → ρ₂.IsGen →
    ∃ g : Γ(A₀, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ A₀) (z : Z) (k : (PUnit → Q₂.ι) × (PUnit → Q₁.ι)),
      e (r z) ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k →
      gm (r ≫ e) z _ (w.s k) * gm (r ≫ ψ) z _ (ρ₁.s k.2) = gm r z ⊤ g * gm (r ≫ ψ) z _ (ρ₂.s k.1) := by
  intro A₀ A₀' X X' ψ e e' π h Q₁ Q₂ hQ₁ hQ₂ w hw ρ₁ ρ₂ hρ₁ hρ₂
  have hpt : ∀ x : A₀, π (e x) = e' (ψ x) := fun x => by
    have := congrArg (fun f : A₀ ⟶ X' => f x) h
    simpa using this
  set D := LB.div (Q₂.pull π) (Q₁.pull π)
  let W : D.ι → A₀.Opens := fun k => e ⁻¹ᵁ D.U k
  have h₁ : ∀ k : D.ι, W k ≤ ψ ⁻¹ᵁ (Q₁.pull e').U k.2 := fun k x hx => by
    have hb := (mem_divPull.1 (show e x ∈ D.U k from hx)).2
    rw [hpt] at hb
    exact mem_pull.2 hb
  have h₂ : ∀ k : D.ι, W k ≤ ψ ⁻¹ᵁ (Q₂.pull e').U k.1 := fun k x hx => by
    have hb := (mem_divPull.1 (show e x ∈ D.U k from hx)).1
    rw [hpt] at hb
    exact mem_pull.2 hb
  let u : ∀ k, Γ(A₀, W k)ˣ := fun k =>
    pullU e _ (w.s k) * res (h₁ k) (pullU ψ _ (ρ₁.s k.2)) * (res (h₂ k) (pullU ψ _ (ρ₂.s k.1)))⁻¹
  have hu : ∀ (Z : Scheme.{0}) (r : Z ⟶ A₀) (z : Z) (k : D.ι) (hz : r z ∈ W k),
      gm r z (W k) (u k) = gm (r ≫ e) z _ (w.s k) * gm (r ≫ ψ) z _ (ρ₁.s k.2) * (gm (r ≫ ψ) z _ (ρ₂.s k.1))⁻¹ := by
    intro Z r z k hz
    simp only [u, map_mul, map_inv]
    rw [gm_res r z (h₁ k) hz, gm_res r z (h₂ k) hz, gm_pull r e z _ hz, gm_pull r ψ z _ (h₁ k hz),
      gm_pull r ψ z _ (h₂ k hz)]
  have hcov : (⊤ : A₀.Opens) ≤ iSup W := fun x _ => by
    obtain ⟨i, hi⟩ := exists_chart hQ₂ (π (e x))
    obtain ⟨j, hj⟩ := exists_chart hQ₁ (π (e x))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨((fun _ => i), (fun _ => j)), mem_divPull.2 ⟨hi, hj⟩⟩
  have hcomp : ∀ k l, ∀ x ∈ W k ⊓ W l, gm (𝟙 A₀) x (W k) (u k) = gm (𝟙 A₀) x (W l) (u l) := by
    intro k l x hx
    rw [hu _ _ x k hx.1, hu _ _ x l hx.2]
    simp only [Category.id_comp]
    have hk : e x ∈ D.U k := hx.1
    have hl : e x ∈ D.U l := hx.2
    have hk' := mem_divPull.1 hk
    have hl' := mem_divPull.1 hl
    have hk₁ : ψ x ∈ (Q₁.pull e').U k.2 := h₁ k hx.1
    have hl₁ : ψ x ∈ (Q₁.pull e').U l.2 := h₁ l hx.2
    have hk₂ : ψ x ∈ (Q₂.pull e').U k.1 := h₂ k hx.1
    have hl₂ : ψ x ∈ (Q₂.pull e').U l.1 := h₂ l hx.2
    have E := gen_germ hw e x hk hl
    rw [germ_div_g _ _ e x hk hl] at E
    rw [show e = 𝟙 A₀ ≫ e from (Category.id_comp e).symm] at E
    rw [gm_pull_g Q₂ π (𝟙 A₀ ≫ e) x hk'.1 hl'.1, gm_pull_g Q₁ π (𝟙 A₀ ≫ e) x hk'.2 hl'.2] at E
    simp only [Category.id_comp] at E
    have R₁ := gen_germ hρ₁ ψ x hk₁ hl₁
    have R₂ := gen_germ hρ₂ ψ x hk₂ hl₂
    rw [show ψ = 𝟙 A₀ ≫ ψ from (Category.id_comp ψ).symm] at R₁ R₂
    rw [gm_pull_g Q₁ e' (𝟙 A₀ ≫ ψ) x (mem_pull.1 hk₁) (mem_pull.1 hl₁)] at R₁
    rw [gm_pull_g Q₂ e' (𝟙 A₀ ≫ ψ) x (mem_pull.1 hk₂) (mem_pull.1 hl₂)] at R₂
    simp only [Category.id_comp, ← h] at E R₁ R₂
    rw [E, R₁, R₂]
    exact mul_inv_axis_comm_identity _ _ _ _ _
  obtain ⟨g, hg⟩ := glue_unit (⊤ : A₀.Opens) W (fun _ => le_top) hcov u hcomp
  refine ⟨g, fun Z r z k hk => ?_⟩
  have hz : r z ∈ W k := hk
  have e₁ : gm r z ⊤ g = gm r z (W k) (u k) := by rw [← hg k, gm_res r z le_top hz]
  rw [e₁, hu Z r z k hz, inv_mul_cancel_right]

end GlobalTheory.UPel.HT.Hecke.PullInj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAxisUnitGeneratorsPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT.Hecke.PullInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_axis_unit_generators_pullback : ∀ (A₀ A₀' X X' : Scheme.{0}) (ψ : A₀ ⟶ A₀') (e : A₀ ⟶ X) (e' : A₀' ⟶ X') (π : X ⟶ X'), e ≫ π = ψ ≫ e' → ∀ (Q₁ Q₂ : LB X'), Q₁.IsLB → Q₂.IsLB → ∀ (w : LB.Iso (Q₁.pull π) (Q₂.pull π)), w.IsGen → ∀ (ρ₁ : LB.Gen (Q₁.pull e')) (ρ₂ : LB.Gen (Q₂.pull e')), ρ₁.IsGen → ρ₂.IsGen → ∃ g : Γ(A₀, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ A₀) (z : Z) (k : (PUnit → Q₂.ι) × (PUnit → Q₁.ι)), e (r z) ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k → gm (r ≫ e) z _ (w.s k) * gm (r ≫ ψ) z _ (ρ₁.s k.2) = gm r z ⊤ g * gm (r ≫ ψ) z _ (ρ₂.s k.1) := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.PullInj.axis_unit) | (exact GlobalTheory.UPel.HT.Hecke.PullInj.axis_unit) | (intros; apply GlobalTheory.UPel.HT.Hecke.PullInj.axis_unit  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackProdInjectiveBirigidifiedGaloisIsogeny
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section


open GlobalTheory.UPel.HT.Hecke.PullInj in
theorem GlobalTheory.UPel.HT.Hecke.pullback_prod_injective_birigidified_galois_isogeny_alt : ∀ (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (G : Subgroup (𝟙_ (Over S) ⟶ A)) (ψ : A ⟶ A'), IsAbelianScheme A → IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover G (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → ∀ Q₁ Q₂ : LB (G2 A').left, Q₁.IsLB → Q₂.IsLB → (∃ t : (Q₁.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) → (∃ t : (Q₁.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) → (∃ t : (Q₂.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) → (∃ t : (Q₂.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) → LBIso (Q₁.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) (Q₂.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) → LBIso Q₁ Q₂ := by
  intro S A A' _ _ _ _ G ψ hA hA' hψ hG Q₁ Q₂ hQ₁ hQ₂ ⟨ρ₁, hρ₁⟩ ⟨σ₁, hσ₁⟩ ⟨ρ₂, hρ₂⟩ ⟨σ₂, hσ₂⟩ ⟨w, hw⟩
  have hP := GlobalTheory.T.isGaloisCover_prod_sq2_of_isGaloisCover S A A' G ψ hψ hG
  have := hP.finite
  have := hP.fin
  have := hP.etale
  have := hP.onto
  have hT := GlobalTheory.LinDescent.locTransitive_of_isGaloisCover hP
  have hA2 : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  let π := Hecke.sq2 ψ
  let τ : ↥G × ↥G → ((G2 A).left ⟶ (G2 A).left) :=
    fun h => (Hecke.transl (lift h.1.1 h.2.1 : 𝟙_ (Over S) ⟶ G2 A)).left
  have hτπ : ∀ c, τ c ≫ π = π := hP.inv
  have hτx : ∀ c x, π (τ c x) = π x := fun c x => congrArg (fun q : (G2 A).left ⟶ (G2 A').left => q x) (hτπ c)

  have hchart : ∀ x : (G2 A).left, ∃ k, x ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k := fun x => by
    obtain ⟨j₂, h₂⟩ := exists_chart hQ₂ (π x)
    obtain ⟨j₁, h₁⟩ := exists_chart hQ₁ (π x)
    exact ⟨(fun _ => j₂, fun _ => j₁), mem_divPull.2 ⟨h₂, h₁⟩⟩

  let Inv : ↥G × ↥G → Prop := fun c => ∀ (Z : Scheme.{0}) (r : Z ⟶ (G2 A).left) (z : Z) k,
    r z ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k → gm (r ≫ τ c) z _ (w.s k) = gm r z _ (w.s k)
  have hmul : ∀ a b, Inv a → Inv b → Inv (a * b) := fun a b ha hb Z r z k hk => by
    have e : r ≫ τ (a * b) = (r ≫ τ a) ≫ τ b := by rw [Category.assoc]; exact congrArg (r ≫ ·) (hP.mul a b)
    have hk' : (r ≫ τ a) z ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k := by
      have h0 := (mem_divPull (F := π)).1 hk
      refine (mem_divPull (F := π)).2 ?_
      change π (τ a (r z)) ∈ _ ∧ π (τ a (r z)) ∈ _
      rw [hτx]; exact h0
    rw [e, hb Z _ z k hk', ha Z r z k hk]

  let s₀ : (G2 A).left ⟶ A.left := (toUnit (G2 A) ≫ η[A]).left
  have hs₀ : s₀ ≫ A.hom = (G2 A).hom := by
    exact Over.w (toUnit (G2 A) ≫ η[A])

  have axis : ∀ (c : ↥G × ↥G) (e : A.left ⟶ (G2 A).left) (e' : A'.left ⟶ (G2 A').left) (T : A.left ⟶ A.left),
      e ≫ π = ψ.left ≫ e' → e ≫ (G2 A).hom = A.hom → e ≫ τ c = T ≫ e → T ≫ ψ.left = ψ.left → T ≫ A.hom = A.hom →
      (∃ ρ : LB.Gen (Q₁.pull e'), ρ.IsGen) → (∃ ρ : LB.Gen (Q₂.pull e'), ρ.IsGen) → Inv c := by
    rintro c e e' T he heS heT hTψ hTS ⟨r₁, hr₁⟩ ⟨r₂, hr₂⟩
    obtain ⟨f, hf⟩ := GlobalTheory.T.generator_translate_ratio_global_unit _ _ π Q₁ Q₂ hQ₁ hQ₂ w hw (τ c) (hτπ c)
    obtain ⟨g, hg⟩ := GlobalTheory.T.exists_axis_unit_generators_pullback _ _ _ _ ψ.left e e' π he Q₁ Q₂ hQ₁ hQ₂ w hw r₁ r₂ hr₁ hr₂
    have hTx : ∀ a, ψ.left (T a) = ψ.left a := fun a => congrArg (fun q : A.left ⟶ A'.left => q a) hTψ
    have hex : ∀ a, π (e a) = e' (ψ.left a) := fun a => congrArg (fun q : A.left ⟶ (G2 A').left => q a) he
    have hf1 : ∀ (Z : Scheme.{0}) (r : Z ⟶ A.left) (z : Z), gm (r ≫ e) z ⊤ f = 1 := fun Z r z => by
      obtain ⟨k, hk⟩ := hchart (e (r z))
      have hk' : e ((r ≫ T) z) ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k := by
        have h0 := (mem_divPull (F := π)).1 hk
        refine (mem_divPull (F := π)).2 ?_
        change π (e (T (r z))) ∈ _ ∧ π (e (T (r z))) ∈ _
        rw [hex, hTx, ← hex]; exact h0
      have h1 := hf Z (r ≫ e) z k hk
      have h2 := hg Z r z k hk
      have h3 := hg Z (r ≫ T) z k hk'
      rw [Category.assoc, heT, ← Category.assoc] at h1
      rw [Category.assoc r T ψ.left, hTψ, gm_top_eq A hA g (r ≫ T) r (by rw [Category.assoc, hTS])] at h3
      rw [← h2, mul_left_inj] at h3
      rw [h3] at h1
      exact (mul_eq_right.1 h1.symm)
    intro Z r z k hk
    have hf' : gm r z ⊤ f = 1 := by
      rw [gm_top_eq (G2 A) hA2 f r (r ≫ s₀ ≫ e) (by rw [Category.assoc, Category.assoc, heS, hs₀]), ← Category.assoc]
      exact hf1 Z (r ≫ s₀) z
    rw [hf Z r z k hk, hf', _root_.one_mul]
  have inv₁ : ∀ h : ↥G, Inv (1, h) := fun h =>
    axis (1, h) (lift (1 : A ⟶ A) (𝟙 A)).left (lift (1 : A' ⟶ A') (𝟙 A')).left (Hecke.transl h.1).left
      (congrArg (·.left) (grpScheme_monHom_square_lift_one_left ψ))
      (Over.w _)
      (by
        show (lift (1 : A ⟶ A) (𝟙 A)).left ≫ (Hecke.transl (lift ((1 : ↥G) : 𝟙_ (Over S) ⟶ A) h.1)).left = _
        rw [OneMemClass.coe_one, ← Over.comp_left, ← Over.comp_left]
        exact congrArg (·.left) (transl_axis₁ A h.1))
      (hG.inv h) (Over.w _) ⟨ρ₁, hρ₁⟩ ⟨ρ₂, hρ₂⟩
  have inv₂ : ∀ h : ↥G, Inv (h, 1) := fun h =>
    axis (h, 1) (lift (𝟙 A) (1 : A ⟶ A)).left (lift (𝟙 A') (1 : A' ⟶ A')).left (Hecke.transl h.1).left
      (congrArg (·.left) (grpScheme_monHom_square_lift_one_right ψ))
      (Over.w _)
      (by
        show (lift (𝟙 A) (1 : A ⟶ A)).left ≫ (Hecke.transl (lift h.1 ((1 : ↥G) : 𝟙_ (Over S) ⟶ A))).left = _
        rw [OneMemClass.coe_one, ← Over.comp_left, ← Over.comp_left]
        exact congrArg (·.left) (transl_axis₂ A h.1))
      (hG.inv h) (Over.w _) ⟨σ₁, hσ₁⟩ ⟨σ₂, hσ₂⟩
  have inv : ∀ c, Inv c := fun c => by
    have e : c = (c.1, 1) * (1, c.2) := Prod.ext (_root_.mul_one c.1).symm (_root_.one_mul c.2).symm
    rw [e]
    exact hmul _ _ (inv₂ c.1) (inv₁ c.2)

  have hdesc : ∀ p : Q₂.ι × Q₁.ι, ∃ g : Γ((G2 A').left, Q₂.U p.1 ⊓ Q₁.U p.2)ˣ, ∀ (Z : Scheme.{0})
      (r : Z ⟶ (G2 A).left) (z : Z), r z ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U (fun _ => p.1, fun _ => p.2) →
      gm (r ≫ π) z _ g = gm r z _ (w.s (fun _ => p.1, fun _ => p.2)) := fun p => by
    obtain ⟨g, hg⟩ := GlobalTheory.LinDescent.LocTransitive.exists_descend_unit hT (Q₂.U p.1 ⊓ Q₁.U p.2)
      (κ := Unit) (fun _ => (LB.div (Q₂.pull π) (Q₁.pull π)).U (fun _ => p.1, fun _ => p.2))
      (fun _ x hx => (mem_divPull (F := π)).1 hx)
      (fun x hx => ⟨(), (mem_divPull (F := π)).2 hx⟩)
      (fun _ => w.s (fun _ => p.1, fun _ => p.2)) (fun _ _ _ _ _ => rfl)
      (fun c Z r z hz => by
        have hz' : r z ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U (fun _ => p.1, fun _ => p.2) :=
          (mem_divPull (F := π)).2 hz
        refine ⟨(), (), hz', ?_, inv c Z r z _ hz'⟩
        refine (mem_divPull (F := π)).2 ?_
        change π (τ c (r z)) ∈ _ ∧ π (τ c (r z)) ∈ _
        rw [hτx]; exact hz)
    exact ⟨g, fun Z r z hz => hg Z r z () hz⟩
  choose g hg using hdesc
  refine ⟨⟨g⟩, fun p q => ?_⟩
  apply GlobalTheory.LinDescent.unit_ext_of_flat (π := π)
  intro x hx
  have hp : x ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U (fun _ => p.1, fun _ => p.2) :=
    (mem_divPull (F := π)).2 hx.1
  have hq : x ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U (fun _ => q.1, fun _ => q.2) :=
    (mem_divPull (F := π)).2 hx.2
  have e1 := gen_germ hw (𝟙 _) x hp hq
  rw [germ_div_g _ _ (𝟙 _) x hp hq, gm_pull_g Q₂ π (𝟙 _) x hx.1.1 hx.2.1,
    gm_pull_g Q₁ π (𝟙 _) x hx.1.2 hx.2.2] at e1
  refine ((gm_res (𝟙 _ ≫ π) x inf_le_left hx (g p)).trans (hg p _ (𝟙 _) x hp)).trans ?_
  rw [e1, map_mul, gm_res (𝟙 _ ≫ π) x inf_le_right hx (g q), germ_div_g Q₂ Q₁ (𝟙 _ ≫ π) x hx.1 hx.2]
  exact congrArg (_ * ·) (hg q _ (𝟙 _) x hq).symm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackProdInjectiveBirigidifiedGaloisIsogenyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_prod_injective_birigidified_galois_isogeny : ∀ (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (G : Subgroup (𝟙_ (Over S) ⟶ A)) (ψ : A ⟶ A'), IsAbelianScheme A → IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover G (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → ∀ Q₁ Q₂ : LB (G2 A').left, Q₁.IsLB → Q₂.IsLB → (∃ t : (Q₁.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) → (∃ t : (Q₁.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) → (∃ t : (Q₂.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) → (∃ t : (Q₂.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) → LBIso (Q₁.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) (Q₂.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) → LBIso Q₁ Q₂ := by
  first | exact @GlobalTheory.UPel.HT.Hecke.pullback_prod_injective_birigidified_galois_isogeny_alt | exact GlobalTheory.UPel.HT.Hecke.pullback_prod_injective_birigidified_galois_isogeny_alt | (intros; apply GlobalTheory.UPel.HT.Hecke.pullback_prod_injective_birigidified_galois_isogeny_alt <;> assumption)
end
