module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitModuliOfStalkCompleteDVR

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummandDualAnnihilatorReductionProjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummandDualAnnihilatorReductionProjective
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualSummand

open Module _root_.Submodule

variable {R : Type} [CommRing R] {C : Type*} [AddCommGroup C] [Module R C]

theorem isCompl_dualAnnihilator {K N : Submodule R C} (h : IsCompl K N) :
    IsCompl K.dualAnnihilator N.dualAnnihilator := by
  constructor
  · rw [disjoint_iff, eq_bot_iff]
    intro f hf
    rw [mem_inf, mem_dualAnnihilator, mem_dualAnnihilator] at hf
    rw [mem_bot]
    ext c
    rw [← projection_add_projection_eq_self h c, map_add (f := _), hf.1 _ (projection_apply_mem h c),
      hf.2 _ (projection_apply_mem h.symm c)]
    simp
  · rw [codisjoint_iff, eq_top_iff]
    intro f _
    have e : f = f ∘ₗ N.projection K h.symm + f ∘ₗ K.projection N h := by
      ext c
      simp only [LinearMap.add_apply, LinearMap.comp_apply]
      rw [← map_add (f := _), add_comm, projection_add_projection_eq_self h c]
    rw [e]
    refine add_mem_sup ?_ ?_
    · rw [mem_dualAnnihilator]
      intro k hk
      simp [projection_apply_of_mem_right h.symm hk]
    · rw [mem_dualAnnihilator]
      intro n hn
      simp [projection_apply_of_mem_right h hn]

theorem dualAnnihilator_dualCoannihilator_eq [Projective R C] {K N : Submodule R C}
    (h : IsCompl K N) : K.dualAnnihilator.dualCoannihilator = K := by
  refine le_antisymm (fun c hc => ?_) (le_dualAnnihilator_dualCoannihilator _)
  rw [mem_dualCoannihilator] at hc
  have hn : N.projection K h.symm c = 0 := by
    rw [← forall_dual_apply_eq_zero_iff R]
    intro φ
    have := hc (φ ∘ₗ N.projection K h.symm) (by
      rw [mem_dualAnnihilator]
      intro k hk
      simp [projection_apply_of_mem_right h.symm hk])
    simpa using this
  rw [← projection_add_projection_eq_self h c, hn, add_zero]
  exact projection_apply_mem h c

theorem mem_smul_top_of_forall_dual [Projective R C] (I : Ideal R) (c : C)
    (h : ∀ x : Dual R C, x c ∈ I) : c ∈ I • (⊤ : Submodule R C) := by
  obtain ⟨s, hs⟩ := projective_def.mp (inferInstance : Projective R C)
  rw [← hs c, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Submodule.sum_mem _ fun m _ => ?_
  exact smul_mem_smul (by simpa using h (Finsupp.lapply m ∘ₗ s)) mem_top

variable {R₀ : Type} [CommRing R₀] {π : R →+* R₀} {C₀ : Type*} [AddCommGroup C₀] [Module R₀ C₀]

theorem exists_dual_lift [Projective R C] (hπ : Function.Surjective π) (ρ : C →ₛₗ[π] C₀)
    (y : Dual R₀ C₀) : ∃ x : Dual R C, ∀ c, π (x c) = y (ρ c) := by
  obtain ⟨s, hs⟩ := projective_def.mp (inferInstance : Projective R C)
  refine ⟨Finsupp.linearCombination R (fun m => Function.surjInv hπ (y (ρ m))) ∘ₗ s, fun c => ?_⟩
  conv_rhs => rw [← hs c]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.comp_apply, Finsupp.linearCombination_apply, Finsupp.sum, map_sum,
    smul_eq_mul, map_mul, Function.surjInv_eq, LinearMap.map_smulₛₗ, id, RingHom.id_apply]

theorem exists_dual_descent {ρ : C →ₛₗ[π] C₀} (hπ : Function.Surjective π)
    (hρ : Function.Surjective ρ) (hker : ∀ c, ρ c = 0 ↔ c ∈ RingHom.ker π • (⊤ : Submodule R C))
    (x : Dual R C) : ∃ y : Dual R₀ C₀, ∀ c, y (ρ c) = π (x c) := by
  have hI : RingHom.ker π • (⊤ : Submodule R C) ≤ Submodule.comap x (RingHom.ker π) := by
    rw [Submodule.smul_le]
    intro r hr n _
    rw [Submodule.mem_comap, map_smul, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ hr
  have hx : ∀ a b, ρ a = ρ b → π (x a) = π (x b) := by
    intro a b hab
    have h1 : a - b ∈ RingHom.ker π • (⊤ : Submodule R C) := (hker _).mp (by rw [map_sub, hab, sub_self])
    have h2 := hI h1
    rw [Submodule.mem_comap, map_sub] at h2
    rw [← sub_eq_zero, ← map_sub]
    exact (RingHom.mem_ker).mp h2
  let g := Function.surjInv hρ
  have hg : ∀ v, ρ (g v) = v := Function.surjInv_eq hρ
  refine ⟨{ toFun := fun v => π (x (g v)), map_add' := ?_, map_smul' := ?_ }, fun c => hx _ _ (hg _)⟩
  · intro a b
    rw [show π (x (g a)) + π (x (g b)) = π (x (g a + g b)) by simp]
    exact hx _ _ (by rw [map_add (f := _), hg, hg, hg])
  · intro r v
    obtain ⟨r', rfl⟩ := hπ r
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [← map_mul, ← smul_eq_mul, ← map_smul]
    exact hx _ _ (by rw [LinearMap.map_smulₛₗ, hg, hg])

end GlobalTheory.DualSummand

namespace GlobalTheory.DualSummand

open Module _root_.Submodule

variable {R : Type} [CommRing R] {C : Type*} [AddCommGroup C] [Module R C]
variable {R₀ : Type} [CommRing R₀] {π : R →+* R₀} {C₀ : Type*} [AddCommGroup C₀] [Module R₀ C₀]

theorem eq_zero_of_forall_dual_reduction [Projective R C] {ρ : C →ₛₗ[π] C₀}
    (hπ : Function.Surjective π) (hρ : Function.Surjective ρ)
    (hker : ∀ c, ρ c = 0 ↔ c ∈ RingHom.ker π • (⊤ : Submodule R C))
    (v : C₀) (hv : ∀ φ : Dual R₀ C₀, φ v = 0) : v = 0 := by
  obtain ⟨c, rfl⟩ := hρ v
  rw [hker]
  refine mem_smul_top_of_forall_dual _ c fun x => ?_
  obtain ⟨y, hy⟩ := exists_dual_descent hπ hρ hker x
  rw [RingHom.mem_ker, ← hy]
  exact hv y

theorem exists_eq_dualAnnihilator [Projective R C] [Module.Finite R C]
    {G H : Submodule R (Dual R C)} (hGH : IsCompl G H) :
    ∃ K : Submodule R C, (∃ N, IsCompl K N) ∧ G = K.dualAnnihilator := by
  have hsurj : ∀ ψ : Dual R (Dual R C), ∃ k : C, ∀ φ : Dual R C, φ k = ψ φ := by
    intro ψ
    obtain ⟨k, hk⟩ := (Module.bijective_dual_eval R C).2 ψ
    exact ⟨k, fun φ => by rw [← hk, Dual.eval_apply]⟩
  have hsplit : ∀ φ : Dual R C, G.projection H hGH φ + H.projection G hGH.symm φ = φ :=
    projection_add_projection_eq_self hGH
  have hKL : IsCompl G.dualCoannihilator H.dualCoannihilator := by
    constructor
    · rw [disjoint_iff, eq_bot_iff]
      intro c hc
      rw [mem_inf, mem_dualCoannihilator, mem_dualCoannihilator] at hc
      rw [mem_bot, ← forall_dual_apply_eq_zero_iff R]
      intro φ
      rw [← hsplit φ, LinearMap.add_apply, hc.1 _ (projection_apply_mem hGH φ),
        hc.2 _ (projection_apply_mem hGH.symm φ), add_zero]
    · rw [codisjoint_iff, eq_top_iff]
      intro c _
      obtain ⟨k, hk⟩ := hsurj (Dual.eval R C c ∘ₗ H.projection G hGH.symm)
      obtain ⟨l, hl⟩ := hsurj (Dual.eval R C c ∘ₗ G.projection H hGH)
      refine Submodule.mem_sup.mpr ⟨k, ?_, l, ?_, ?_⟩
      · rw [mem_dualCoannihilator]
        intro g hg
        rw [hk g]
        simp [projection_apply_of_mem_right hGH.symm hg]
      · rw [mem_dualCoannihilator]
        intro h hh
        rw [hl h]
        simp [projection_apply_of_mem_right hGH hh]
      · rw [← sub_eq_zero, ← forall_dual_apply_eq_zero_iff R]
        intro φ
        rw [map_sub, map_add (f := _), hk φ, hl φ]
        simp only [LinearMap.comp_apply, Dual.eval_apply]
        rw [← LinearMap.add_apply, add_comm, hsplit φ, sub_self]
  refine ⟨G.dualCoannihilator, ⟨_, hKL⟩, le_antisymm ?_ ?_⟩
  · intro g hg
    rw [mem_dualAnnihilator]
    intro k hk
    exact (mem_dualCoannihilator _).mp hk g hg
  · intro φ hφ
    rw [mem_dualAnnihilator] at hφ
    have h0 : H.projection G hGH.symm φ = 0 := by
      ext c
      obtain ⟨k, hk, l, hl, rfl⟩ := Submodule.mem_sup.mp (hKL.sup_eq_top ▸ mem_top : c ∈ _)
      have e : H.projection G hGH.symm φ = φ - G.projection H hGH φ := by
        rw [eq_sub_iff_add_eq, add_comm, hsplit φ]
      rw [map_add (f := _), (mem_dualCoannihilator _).mp hl _ (projection_apply_mem hGH.symm φ), e,
        LinearMap.sub_apply, hφ k hk, (mem_dualCoannihilator _).mp hk _ (projection_apply_mem hGH φ)]
      simp
    rw [← hsplit φ, h0, add_zero]
    exact projection_apply_mem hGH φ

end GlobalTheory.DualSummand

namespace GlobalTheory.LiftSys

open Module _root_.Submodule GlobalTheory.DualSummand

theorem summand_dual_reduction :
    ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → ∀ (C C₀ : Type 1) [AddCommGroup C] [Module R C] [AddCommGroup C₀] [Module R₀ C₀], Module.Finite R C → Module.Projective R C → ∀ ρ : C →ₛₗ[π] C₀, Function.Surjective ρ → (∀ c, ρ c = 0 ↔ c ∈ RingHom.ker π • (⊤ : Submodule R C)) → ∀ F₀ : Submodule R₀ C₀, (∃ N₀, IsCompl F₀ N₀) → (∀ K : Submodule R C, (∃ N, IsCompl K N) → (∃ N, IsCompl K.dualAnnihilator N) ∧ K.dualAnnihilator.dualCoannihilator = K ∧ ((∀ c, c ∈ K ⊔ RingHom.ker π • ⊤ ↔ ρ c ∈ F₀) ↔ ∀ y : Module.Dual R₀ C₀, y ∈ F₀.dualAnnihilator ↔ ∃ x ∈ K.dualAnnihilator, ∀ c, y (ρ c) = π (x c))) ∧ ∀ G : Submodule R (Module.Dual R C), (∃ N, IsCompl G N) → ∃ K : Submodule R C, (∃ N, IsCompl K N) ∧ G = K.dualAnnihilator := by
  intro R R₀ _ _ π hπ C C₀ _ _ _ _ _ _ ρ hρ hker F₀ ⟨N₀, hF⟩
  refine ⟨fun K ⟨N, hKN⟩ => ⟨⟨_, isCompl_dualAnnihilator hKN⟩,
    dualAnnihilator_dualCoannihilator_eq hKN, ?_⟩, fun G ⟨H, hGH⟩ => exists_eq_dualAnnihilator hGH⟩
  have hsplit : ∀ c, K.projection N hKN c + N.projection K hKN.symm c = c :=
    projection_add_projection_eq_self hKN
  have hNK : ∀ k ∈ K, N.projection K hKN.symm k = 0 := fun k hk =>
    projection_apply_of_mem_right hKN.symm hk
  constructor
  · intro hL y
    constructor
    · intro hy
      rw [mem_dualAnnihilator] at hy
      obtain ⟨x₀, hx₀⟩ := exists_dual_lift hπ ρ y
      refine ⟨x₀ ∘ₗ N.projection K hKN.symm, ?_, fun c => ?_⟩
      · rw [mem_dualAnnihilator]
        intro k hk
        simp [hNK k hk]
      · rw [LinearMap.comp_apply, hx₀]
        conv_lhs => rw [← hsplit c]
        rw [map_add (f := _), map_add (f := _),
          hy _ ((hL _).mp (mem_sup_left (projection_apply_mem hKN c))), zero_add]
    · rintro ⟨x, hx, hxy⟩
      rw [mem_dualAnnihilator] at hx ⊢
      intro f hf
      obtain ⟨c, rfl⟩ := hρ f
      obtain ⟨k, hk, m, hm, rfl⟩ := Submodule.mem_sup.mp ((hL c).mpr hf)
      rw [map_add (f := _), (hker m).mpr hm, add_zero, hxy, hx k hk, map_zero]
  · intro hR c
    constructor
    · intro hc
      obtain ⟨k, hk, m, hm, rfl⟩ := Submodule.mem_sup.mp hc
      rw [map_add (f := _), (hker m).mpr hm, add_zero]
      have hv : N₀.projection F₀ hF.symm (ρ k) = 0 := by
        refine eq_zero_of_forall_dual_reduction hπ hρ hker _ fun φ => ?_
        obtain ⟨x, hx, hxy⟩ := (hR (φ ∘ₗ N₀.projection F₀ hF.symm)).mp (by
          rw [mem_dualAnnihilator]
          intro f hf
          simp [projection_apply_of_mem_right hF.symm hf])
        have := hxy k
        rw [LinearMap.comp_apply] at this
        rw [this, (mem_dualAnnihilator _).mp hx k hk, map_zero]
      rw [← projection_add_projection_eq_self hF (ρ k), hv, add_zero]
      exact projection_apply_mem hF _
    · intro hc
      rw [← hsplit c]
      refine add_mem_sup (projection_apply_mem hKN c) ?_
      refine mem_smul_top_of_forall_dual _ _ fun x₀ => ?_
      obtain ⟨y, hy⟩ := exists_dual_descent hπ hρ hker (x₀ ∘ₗ N.projection K hKN.symm)
      have hyF : y ∈ F₀.dualAnnihilator := (hR y).mpr ⟨x₀ ∘ₗ N.projection K hKN.symm, by
        rw [mem_dualAnnihilator]
        intro k hk
        simp [hNK k hk], hy⟩
      rw [RingHom.mem_ker, ← LinearMap.comp_apply, ← hy]
      exact (mem_dualAnnihilator _).mp hyF _ hc

end GlobalTheory.LiftSys
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummandDualAnnihilatorReductionProjectiveStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summand_dualAnnihilator_reduction_projective : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → ∀ (C C₀ : Type 1) [AddCommGroup C] [Module R C] [AddCommGroup C₀] [Module R₀ C₀], Module.Finite R C → Module.Projective R C → ∀ ρ : C →ₛₗ[π] C₀, Function.Surjective ρ → (∀ c, ρ c = 0 ↔ c ∈ RingHom.ker π • (⊤ : Submodule R C)) → ∀ F₀ : Submodule R₀ C₀, (∃ N₀, IsCompl F₀ N₀) → (∀ K : Submodule R C, (∃ N, IsCompl K N) → (∃ N, IsCompl K.dualAnnihilator N) ∧ K.dualAnnihilator.dualCoannihilator = K ∧ ((∀ c, c ∈ K ⊔ RingHom.ker π • ⊤ ↔ ρ c ∈ F₀) ↔ ∀ y : Module.Dual R₀ C₀, y ∈ F₀.dualAnnihilator ↔ ∃ x ∈ K.dualAnnihilator, ∀ c, y (ρ c) = π (x c))) ∧ ∀ G : Submodule R (Module.Dual R C), (∃ N, IsCompl G N) → ∃ K : Submodule R C, (∃ N, IsCompl K N) ∧ G = K.dualAnnihilator := by
  first | exact @GlobalTheory.LiftSys.summand_dual_reduction | exact GlobalTheory.LiftSys.summand_dual_reduction | (intros; apply GlobalTheory.LiftSys.summand_dual_reduction <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleDeRhamHomologySummandsCrystal
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys

section Lin

variable {S : Type*} [CommRing S] {M N : Type*} [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]

theorem smul_top_le_comap (f : M →ₗ[S] N) (J : Ideal S) :
    J • (⊤ : Submodule S M) ≤ (J • (⊤ : Submodule S N)).comap f :=
  Submodule.smul_le.2 fun r hr n _ ↦ by
    rw [Submodule.mem_comap, map_smul]; exact Submodule.smul_mem_smul hr trivial

theorem mem_smul_top_equiv (e : M ≃ₗ[S] N) (J : Ideal S) (x : M) :
    e x ∈ J • (⊤ : Submodule S N) ↔ x ∈ J • (⊤ : Submodule S M) :=
  ⟨fun h ↦ by simpa using smul_top_le_comap (e.symm : N →ₗ[S] M) J h,
   fun h ↦ smul_top_le_comap (e : M →ₗ[S] N) J h⟩

theorem mem_sup_smul_top_equiv (e : M ≃ₗ[S] N) (J : Ideal S) (K : Submodule S N) (x : M) :
    x ∈ K.comap (e : M →ₗ[S] N) ⊔ J • ⊤ ↔ e x ∈ K ⊔ J • ⊤ := by
  constructor
  · intro h
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 h
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup ha ((mem_smul_top_equiv e J b).2 hb)
  · intro h
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h
    have hx : x = e.symm a + e.symm b := by rw [← map_add (f := _), hab, LinearEquiv.symm_apply_apply]
    rw [hx]
    refine Submodule.add_mem_sup ?_ ((mem_smul_top_equiv e J _).1 (by simpa using hb))
    simpa using ha

theorem exists_isCompl_comap_iff (e : M ≃ₗ[S] N) (K : Submodule S N) :
    (∃ L, IsCompl K L) ↔ ∃ L, IsCompl (K.comap (e : M →ₗ[S] N)) L := by
  constructor
  · rintro ⟨L, h⟩
    exact ⟨L.comap (e : M →ₗ[S] N), (Submodule.orderIsoMapComap e).symm.isCompl h⟩
  · rintro ⟨L, h⟩
    refine ⟨L.map (e : M →ₗ[S] N), ?_⟩
    have := (Submodule.orderIsoMapComap e).isCompl h
    simpa [Submodule.orderIsoMapComap, Submodule.map_comap_eq_of_surjective e.surjective] using this

end Lin

theorem admissible_classification : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A' : Over (Sp R)) [GrpObj A'] (i' : A₀.left ⟶ A'.left) (h' : IsGrpPullback A₀ A' (spMap π) i'), IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → (∀ K : Submodule R (Cr hI π A₀.hom), (∃ N, IsCompl K N) → (∀ c, c ∈ K ⊔ I • ⊤ ↔ rho hI hk A₀.hom c ∈ F1 A₀.hom) → ∃ F : Submodule R (HdR A'), GrothendieckMessing.IsAdmissible h' F ∧ (K.comap (prim (divided₂ hI) (spMap π) A₀).subtype).dualAnnihilator = F.comap (crysToDR (divided₂ hI) h')) ∧ (∀ F : Submodule R (HdR A'), GrothendieckMessing.IsAdmissible h' F → ∃ K : Submodule R (Cr hI π A₀.hom), (∃ N, IsCompl K N) ∧ (∀ c, c ∈ K ⊔ I • ⊤ ↔ rho hI hk A₀.hom c ∈ F1 A₀.hom) ∧ (K.comap (prim (divided₂ hI) (spMap π) A₀).subtype).dualAnnihilator = F.comap (crysToDR (divided₂ hI) h')) ∧ ∀ K K' : Submodule R (Cr hI π A₀.hom), (∃ N, IsCompl K N) → (∃ N, IsCompl K' N) → (K.comap (prim (divided₂ hI) (spMap π) A₀).subtype).dualAnnihilator = (K'.comap (prim (divided₂ hI) (spMap π) A₀).subtype).dualAnnihilator → K = K' := by
  intro H1 H2 R R₀ _ _ I hI π hπ hk g A₀ _ A' _ i' h' hA hg
  obtain ⟨-, -, pc, bij, fin, proj, hA₀, hg₀⟩ :=
    abelianLift_facts H1 H2 R R₀ I hI π hπ hk g A₀ A' i' h' hA hg
  obtain ⟨rs, rk⟩ := GlobalTheory.T.abelianScheme_crystal_reduces_to_deRham_sqZero H1 H2 R R₀ I hI π hπ hk g A₀ A' i' h' hA hg
  obtain ⟨-, ⟨N₀, hN₀⟩, -⟩ := GlobalTheory.AbelianHodge.abelianDeRham_hodge H1 H2 R₀ A₀ g hA₀ hg₀
  let P := prim (divided₂ hI) (spMap π) A₀
  let Ψ : primDR A' ≃ₗ[R] P := LinearEquiv.ofBijective (liftMor (divided₂ hI) h').pull bij
  let Φ : primDR A' ≃ₗ[R] Cr hI π A₀.hom := Ψ.trans (LinearEquiv.ofTop _ pc)
  have hΦ : ∀ c, Φ c = ((Ψ c : P) : Cr hI π A₀.hom) := fun _ ↦ rfl
  let ρ := (GrothendieckMessing.redMor h').pull
  have mT : IsMor (dp0 R₀) (A₀.hom ≫ 𝟙 _) (dp0 R₀) A₀.hom (RingHom.id R₀) (𝟙 _) :=
    IsMor.of_over _ (by simp)
  have mT' : IsMor (dp0 R₀) A₀.hom (dp0 R₀) (A₀.hom ≫ 𝟙 _) (RingHom.id R₀) (𝟙 _) :=
    IsMor.of_over _ (by simp)
  have back : ∀ x, mT'.pull1 (mT.pull1 x) = x := fun x ↦
    (IsMor.pullback1_comp mT mT' (IsMor.id _ _) (fun _ ↦ rfl) (Category.id_comp _) x).trans
      (IsMor.pullCohomologyOne_id _ x)
  have inj : Function.Injective mT.pull1 := Function.LeftInverse.injective back
  have mD : IsMor (dp0 R) (A'.hom ≫ 𝟙 _) (dp0 R₀) A₀.hom π i' :=
    IsMor.of_dividedPowersZeroIdeal _ (by rw [Category.comp_id]; exact h'.1.w)
  have key : ∀ c : primDR A',
      mT.pull1 ((ρ c : primDR A₀) : FirstDeRham (A₀.hom ≫ 𝟙 _)) = rho hI hk A₀.hom (Φ c) := by
    intro c
    rw [hΦ]
    exact (IsMor.pullback1_comp _ mT mD (fun _ ↦ rfl) (Category.id_comp _) c.1).trans
      (IsMor.pullback1_comp _ (redMor hI hk A₀.hom) mD (fun _ ↦ rfl) (Category.id_comp _) c.1).symm
  have F1iff : ∀ c : primDR A', ρ c ∈ PrimitiveSubmodule A₀ ↔ rho hI hk A₀.hom (Φ c) ∈ F1 A₀.hom := by
    intro c
    rw [← key]
    constructor
    · intro h
      exact mT.pullback1_mem_hodgeFiltration h
    · intro h
      have := mT'.pullback1_mem_hodgeFiltration h
      rw [back] at this
      exact this
  have ρker : ∀ c, ρ c = 0 ↔ c ∈ RingHom.ker π • (⊤ : Submodule R (primDR A')) := by
    intro c
    rw [hk, ← mem_smul_top_equiv Φ, ← rk, ← key, map_eq_zero_iff _ inj, Submodule.coe_eq_zero]
  have ρsurj : Function.Surjective ρ := by
    intro y
    obtain ⟨d, hd⟩ := rs (mT.pull1 y.1)
    refine ⟨Φ.symm d, Subtype.ext (inj ?_)⟩
    rw [key, LinearEquiv.apply_symm_apply, hd]
  obtain ⟨D1, D2⟩ := GlobalTheory.T.summand_dualAnnihilator_reduction_projective R R₀ π hπ (primDR A') (primDR A₀) (Module.Finite.equiv Φ.symm)
    (Module.Projective.of_equiv Φ.symm) ρ ρsurj ρker (PrimitiveSubmodule A₀) ⟨N₀, hN₀⟩
  have cond : ∀ K : Submodule R (Cr hI π A₀.hom),
      (∀ c, c ∈ K ⊔ I • ⊤ ↔ rho hI hk A₀.hom c ∈ F1 A₀.hom) ↔
        ∀ c, c ∈ K.comap (Φ : primDR A' →ₗ[R] Cr hI π A₀.hom) ⊔ RingHom.ker π • ⊤ ↔
          ρ c ∈ PrimitiveSubmodule A₀ := by
    intro K
    rw [hk]
    constructor
    · intro H c
      rw [mem_sup_smul_top_equiv, F1iff]
      exact H (Φ c)
    · intro H c
      have := H (Φ.symm c)
      rwa [mem_sup_smul_top_equiv, F1iff, LinearEquiv.apply_symm_apply] at this
  have crysSurj : Function.Surjective (crysToDR (divided₂ hI) h') := fun y ↦
    ⟨y.comp (Ψ.symm : P →ₗ[R] primDR A'), LinearMap.ext fun c ↦ by
      rw [crysToDR_apply]
      exact congrArg y (Ψ.symm_apply_apply c)⟩
  have ann : ∀ K : Submodule R (Cr hI π A₀.hom),
      (K.comap P.subtype).dualAnnihilator =
        (K.comap (Φ : primDR A' →ₗ[R] Cr hI π A₀.hom)).dualAnnihilator.comap
          (crysToDR (divided₂ hI) h') := by
    intro K
    ext d
    simp only [Submodule.mem_comap, Submodule.mem_dualAnnihilator, crysToDR_apply]
    constructor
    · intro H c hc
      exact H _ hc
    · intro H p hp
      have e : (liftMor (divided₂ hI) h').pull (Ψ.symm p) = p := Ψ.apply_symm_apply p
      have hm : Φ (Ψ.symm p) ∈ K := by
        rw [hΦ, Ψ.apply_symm_apply]
        exact hp
      have := H (Ψ.symm p) hm
      rwa [crysToDR_apply, e] at this
  have eqiff : ∀ (K : Submodule R (Cr hI π A₀.hom)) (F : Submodule R (HdR A')),
      (K.comap P.subtype).dualAnnihilator = F.comap (crysToDR (divided₂ hI) h') ↔
        (K.comap (Φ : primDR A' →ₗ[R] Cr hI π A₀.hom)).dualAnnihilator = F := by
    intro K F
    rw [ann]
    exact (Submodule.comap_injective_of_surjective crysSurj).eq_iff
  refine ⟨fun K hK hc ↦ ?_, fun F hF ↦ ?_, fun K K' hK hK' he ↦ ?_⟩
  · obtain ⟨c1, -, c3⟩ := D1 _ ((exists_isCompl_comap_iff Φ K).1 hK)
    exact ⟨_, ⟨c1, c3.1 ((cond K).1 hc)⟩, (eqiff K _).2 rfl⟩
  · obtain ⟨K', hK', rfl⟩ := D2 F hF.1
    have hKK : (K'.map (Φ : primDR A' →ₗ[R] Cr hI π A₀.hom)).comap
        (Φ : primDR A' →ₗ[R] Cr hI π A₀.hom) = K' :=
      Submodule.comap_map_eq_of_injective Φ.injective K'
    obtain ⟨-, -, c3⟩ := D1 K' hK'
    refine ⟨K'.map (Φ : primDR A' →ₗ[R] Cr hI π A₀.hom), (exists_isCompl_comap_iff Φ _).2 (by rw [hKK]; exact hK'),
      (cond _).2 (by rw [hKK]; exact c3.2 hF.2), (eqiff _ _).2 (by rw [hKK])⟩
  · rw [ann, ann] at he
    have e := Submodule.comap_injective_of_surjective crysSurj he
    obtain ⟨-, c2, -⟩ := D1 _ ((exists_isCompl_comap_iff Φ K).1 hK)
    obtain ⟨-, c2', -⟩ := D1 _ ((exists_isCompl_comap_iff Φ K').1 hK')
    refine Submodule.comap_injective_of_surjective Φ.surjective ?_
    rw [← c2, ← c2', e]

end GlobalTheory.LiftSys
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleDeRhamHomologySummandsCrystalStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_deRhamHomology_summands_crystal : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A' : Over (Sp R)) [GrpObj A'] (i' : A₀.left ⟶ A'.left) (h' : IsGrpPullback A₀ A' (spMap π) i'), IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → (∀ K : Submodule R (Cr hI π A₀.hom), (∃ N, IsCompl K N) → (∀ c, c ∈ K ⊔ I • ⊤ ↔ rho hI hk A₀.hom c ∈ F1 A₀.hom) → ∃ F : Submodule R (HdR A'), GrothendieckMessing.IsAdmissible h' F ∧ (K.comap (prim (divided₂ hI) (spMap π) A₀).subtype).dualAnnihilator = F.comap (crysToDR (divided₂ hI) h')) ∧ (∀ F : Submodule R (HdR A'), GrothendieckMessing.IsAdmissible h' F → ∃ K : Submodule R (Cr hI π A₀.hom), (∃ N, IsCompl K N) ∧ (∀ c, c ∈ K ⊔ I • ⊤ ↔ rho hI hk A₀.hom c ∈ F1 A₀.hom) ∧ (K.comap (prim (divided₂ hI) (spMap π) A₀).subtype).dualAnnihilator = F.comap (crysToDR (divided₂ hI) h')) ∧ ∀ K K' : Submodule R (Cr hI π A₀.hom), (∃ N, IsCompl K N) → (∃ N, IsCompl K' N) → (K.comap (prim (divided₂ hI) (spMap π) A₀).subtype).dualAnnihilator = (K'.comap (prim (divided₂ hI) (spMap π) A₀).subtype).dualAnnihilator → K = K' := by
  first | exact @GlobalTheory.LiftSys.admissible_classification | exact GlobalTheory.LiftSys.admissible_classification | (intros; apply GlobalTheory.LiftSys.admissible_classification <;> assumption)
end
