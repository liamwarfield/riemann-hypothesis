module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactUnitaryIntegralPoints
public import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfSubsetCpt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct Pointwise

namespace GlobalTheory.LocFinU

theorem relIndex_ne_zero_of_subset_cpt {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U P : Subgroup G) (hU : IsOpen (U : Set G)) (Ω : Set G) (hΩ : IsCompact Ω) (hP : (P : Set G) ⊆ Ω) :
    U.relIndex P ≠ 0 := by
  obtain ⟨s, hs⟩ := hΩ.elim_finite_subcover (fun g : Ω => (g : G) • (U : Set G)) (fun g => hU.smul _)
    (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, ⟨1, U.one_mem, mul_one x⟩⟩)
  have hmem : ∀ q : P ⧸ U.subgroupOf P, ∃ i : s, ((Quotient.out q : P) : G) ∈ ((i : Ω) : G) • (U : Set G) := by
    intro q
    have := hs (hP (Quotient.out q).2)
    simp only [Set.mem_iUnion] at this
    obtain ⟨i, hi, h⟩ := this
    exact ⟨⟨i, hi⟩, h⟩
  choose f hf using hmem
  have hinj : Function.Injective f := by
    intro q q' h
    have h1 := hf q
    have h2 := hf q'
    rw [h] at h1
    obtain ⟨u, hu, hu'⟩ := h1
    obtain ⟨u', hu2, hu2'⟩ := h2
    rw [← Quotient.out_eq q, ← Quotient.out_eq q']
    change QuotientGroup.mk _ = QuotientGroup.mk _
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hu', ← hu2']
    simp only [smul_eq_mul, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left]
    exact U.mul_mem (U.inv_mem hu) hu2
  haveI : Finite (P ⧸ U.subgroupOf P) := Finite.of_injective f hinj
  exact Subgroup.index_ne_zero_of_finite

end GlobalTheory.LocFinU

namespace GlobalTheory.LocFinU

theorem continuous_cj {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) : Continuous (cj w) := by
  unfold cj
  split_ifs with h
  · exact h.choose_spec.1
  · exact continuous_id

theorem isClosed_UL {E : Type} [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) :
    IsClosed (UL n w : Set (GLw n w)) := by
  unfold UL
  split_ifs
  · exact isClosed_univ
  · have hc : Continuous fun g : GLw n w => cT (cj w) (g : Matrix (Fin n) (Fin n) _) * 1 * (g : Matrix (Fin n) (Fin n) _) :=
      ((Units.continuous_val.matrix_map (continuous_cj w)).matrix_transpose.matrix_mul continuous_const).matrix_mul
        Units.continuous_val
    exact isClosed_eq hc continuous_const

theorem isCompact_KL {E : Type} [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) :
    IsCompact (KL n w : Set (UL n w)) := by
  rw [Subtype.isCompact_iff]
  have hK : IsCompact (GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w)) :=
    GlobalTheory.LFun.IntPtsUnitary.isCompact_GLint _ (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers E w)
  have : (Subtype.val '' (KL n w : Set (UL n w))) = (GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w)) ∩ (UL n w : Set (GLw n w)) := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx, x.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨g, h2⟩, h1, rfl⟩
  rw [this]
  exact hK.inter_right (isClosed_UL n w)

end GlobalTheory.LocFinU

namespace GlobalTheory.LocFinU

theorem cptPart_subset_of_comm {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (T : Subgroup G) (hc : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) :
    (cptPart T : Set G) ⊆ {t | t ∈ T ∧ IsCompact (closure (Subgroup.zpowers t : Set G))} := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one =>
    refine ⟨T.one_mem, ?_⟩
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.coe_bot, closure_singleton]
    exact isCompact_singleton
  | mul x y _ _ hx hy =>
    refine ⟨T.mul_mem hx.1 hy.1, ?_⟩
    have hxy : Commute x y := hc x hx.1 y hy.1
    have hcp : IsCompact (closure (Subgroup.zpowers x : Set G) * closure (Subgroup.zpowers y : Set G)) :=
      hx.2.mul hy.2
    refine hcp.of_isClosed_subset isClosed_closure (closure_minimal ?_ hcp.isClosed)
    rintro _ ⟨k, rfl⟩
    exact ⟨x ^ k, subset_closure ⟨k, rfl⟩, y ^ k, subset_closure ⟨k, rfl⟩, (hxy.mul_zpow k).symm⟩
  | inv x _ hx =>
    refine ⟨T.inv_mem hx.1, ?_⟩
    rw [Subgroup.zpowers_inv]
    exact hx.2

end GlobalTheory.LocFinU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackDescentAlongGaloisCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackDescentAlongGaloisCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.GaloisCartDesc

theorem epi_of_isGaloisCover {X Y : Scheme.{0}} {Ga : Type} [Group Ga] {ρ : Ga → (X ⟶ X)} {π : X ⟶ Y}
    (h : GlobalTheory.ZM.IsGaloisCover Ga ρ π) : Epi π := by
  refine ⟨fun {Z} g₁ g₂ e ↦ ?_⟩
  obtain ⟨f', -, hu⟩ := h.existsUnique_desc (π ≫ g₁) (fun a ↦ by rw [← Category.assoc, h.inv])
  exact (hu g₁ rfl).trans (hu g₂ e.symm).symm

theorem epi_pullback_fst {X Y : Scheme.{0}} {Ga : Type} [Group Ga] {ρ : Ga → (X ⟶ X)} {π : X ⟶ Y}
    (h : GlobalTheory.ZM.IsGaloisCover Ga ρ π) {T : Scheme.{0}} (t : T ⟶ Y) : Epi (pullback.fst t π) := by
  let ρ' : Ga → (pullback t π ⟶ pullback t π) := fun a ↦
    pullback.map t π t π (𝟙 _) (ρ a) (𝟙 _) (by simp) (by simp [h.inv])
  have hg : GlobalTheory.ZM.IsGaloisCover Ga ρ' (pullback.fst t π) :=
    by
      let hp := (IsPullback.of_hasPullback t π).flip
      have hu : ∀ a, ρ' a ≫ pullback.snd t π = pullback.snd t π ≫ ρ a :=
        fun a ↦ by simp only [ρ', pullback.map, pullback.lift_snd]
      exact ((GlobalTheory.ZM.galoisCover_descent _ _ _ _ _ h).2.2 _ _ _ _ _ _ hu hp.w).2 hp
        (fun a ↦ by simp only [ρ', pullback.map, pullback.lift_fst, Category.comp_id])
  exact epi_of_isGaloisCover hg

theorem isGrpPullback_of_galoisCover : ∀ (S S₁ Y : Scheme.{0}) (π₁ : S₁ ⟶ S) (Ga : Type) [Group Ga] (ρ₁ : Ga → (S₁ ⟶ S₁)) (f : S ⟶ Y)
    (A' : Over S₁) (A : Over S) (B : Over Y) [GrpObj A'] [GrpObj A] [GrpObj B] (φ₁ : A'.left ⟶ A.left)
    (ψ : A'.left ⟶ B.left) (φ : A.left ⟶ B.left), GlobalTheory.ZM.IsGaloisCover Ga ρ₁ π₁ → IsGrpPullback A' A π₁ φ₁ →
    IsGrpPullback A' B (π₁ ≫ f) ψ → φ₁ ≫ φ = ψ → IsGrpPullback A B f φ := by
  intro S S₁ Y π₁ Ga _ ρ₁ f A' A B _ _ _ φ₁ ψ φ hG hφ₁ hψ hφ

  let τ : Ga → (A'.left ⟶ A'.left) := fun a ↦
    hφ₁.1.lift φ₁ (A'.hom ≫ ρ₁ a) (by rw [hφ₁.1.w, Category.assoc, hG.inv])
  have hτ₁ : ∀ a, τ a ≫ φ₁ = φ₁ := fun a ↦ hφ₁.1.lift_fst _ _ _
  have hτ₂ : ∀ a, τ a ≫ A'.hom = A'.hom ≫ ρ₁ a := fun a ↦ hφ₁.1.lift_snd _ _ _
  have gφ₁ : GlobalTheory.ZM.IsGaloisCover Ga τ φ₁ := ((GlobalTheory.ZM.galoisCover_descent _ _ _ _ _ hG).2.2 _ _ _ _ _ _ hτ₂ hφ₁.1.flip.w).2 hφ₁.1.flip hτ₁
  have eφ₁ : Epi φ₁ := epi_of_isGaloisCover gφ₁

  have w : φ ≫ B.hom = A.hom ≫ f := by
    rw [← cancel_epi φ₁, reassoc_of% hφ, hψ.1.w, ← reassoc_of% hφ₁.1.w]

  let q : A'.left ⟶ pullback B.hom f := pullback.lift ψ (A'.hom ≫ π₁) (by rw [hψ.1.w, Category.assoc])
  have hq₁ : q ≫ pullback.fst B.hom f = ψ := pullback.lift_fst _ _ _
  have hq₂ : q ≫ pullback.snd B.hom f = A'.hom ≫ π₁ := pullback.lift_snd _ _ _
  have hsq : IsPullback q A'.hom (pullback.snd B.hom f) π₁ := by
    refine IsPullback.of_right ?_ hq₂ (IsPullback.of_hasPullback B.hom f)
    rw [hq₁]
    exact hψ.1
  have hτq : ∀ a, τ a ≫ q = q := fun a ↦ by
    apply pullback.hom_ext
    · rw [Category.assoc, hq₁, ← hφ, reassoc_of% hτ₁ a]
    · rw [Category.assoc, hq₂, reassoc_of% hτ₂ a, hG.inv]
  have gq : GlobalTheory.ZM.IsGaloisCover Ga τ q := ((GlobalTheory.ZM.galoisCover_descent _ _ _ _ _ hG).2.2 _ _ _ _ _ _ hτ₂ hsq.flip.w).2 hsq.flip hτq
  have eq : Epi q := epi_of_isGaloisCover gq
  obtain ⟨d, hd, -⟩ := gq.existsUnique_desc φ₁ hτ₁
  let c : A.left ⟶ pullback B.hom f := pullback.lift φ A.hom w
  have hc : φ₁ ≫ c = q := by
    apply pullback.hom_ext
    · simp only [c, Category.assoc, hq₁]
      rw [pullback.lift_fst, hφ]
    · simp only [c, Category.assoc, hq₂]
      rw [pullback.lift_snd, hφ₁.1.w]
  have hcd : c ≫ d = 𝟙 _ := by rw [← cancel_epi φ₁, reassoc_of% hc, hd, Category.comp_id]
  have hdc : d ≫ c = 𝟙 _ := by rw [← cancel_epi q, reassoc_of% hd, hc, Category.comp_id]
  let i : A.left ≅ pullback B.hom f := ⟨c, d, hcd, hdc⟩
  refine ⟨IsPullback.of_iso_pullback ⟨w⟩ i (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _), ?_⟩

  intro T x y x₀ y₀ hx hy
  let e : pullback T.hom π₁ ⟶ T.left := pullback.fst T.hom π₁
  have ee : Epi e := epi_pullback_fst hG T.hom
  let T₁ : Over S₁ := Over.mk (pullback.snd T.hom π₁)
  let j : Over.mk (T₁.hom ≫ π₁) ⟶ T := Over.homMk e (by simp [T₁, e, pullback.condition])
  let j' : Over.mk (T₁.hom ≫ π₁ ≫ f) ⟶ Over.mk (T.hom ≫ f) :=
    Over.homMk e (by simp [T₁, e, pullback.condition_assoc])
  have lift : ∀ z : T ⟶ A, ∃ z₁ : T₁ ⟶ A', z₁.left ≫ φ₁ = e ≫ z.left := fun z ↦
    ⟨Over.homMk (hφ₁.1.lift (e ≫ z.left) (pullback.snd T.hom π₁)
      (by simp [e, pullback.condition])) (hφ₁.1.lift_snd _ _ _), hφ₁.1.lift_fst _ _ _⟩
  obtain ⟨x₁, hx₁⟩ := lift x
  obtain ⟨y₁, hy₁⟩ := lift y
  have a₁ : ((j ≫ x) * (j ≫ y)).left = (x₁ * y₁).left ≫ φ₁ :=
    hφ₁.2 T₁ x₁ y₁ (j ≫ x) (j ≫ y) (by simp [j, hx₁]) (by simp [j, hy₁])
  have a₂ : ((j' ≫ x₀) * (j' ≫ y₀)).left = (x₁ * y₁).left ≫ ψ :=
    hψ.2 T₁ x₁ y₁ (j' ≫ x₀) (j' ≫ y₀) (by simp [j', hx, ← hφ, reassoc_of% hx₁])
      (by simp [j', hy, ← hφ, reassoc_of% hy₁])
  rw [← MonObj.comp_mul] at a₁ a₂
  rw [← cancel_epi e]
  have b₁ : e ≫ (x * y).left = (x₁ * y₁).left ≫ φ₁ := by simpa [j] using a₁
  have b₂ : e ≫ (x₀ * y₀).left = (x₁ * y₁).left ≫ ψ := by simpa [j'] using a₂
  rw [b₂, reassoc_of% b₁, hφ]

end GlobalTheory.GaloisCartDesc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackDescentAlongGaloisCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGrpPullback_descent_along_galoisCover : ∀ (S S₁ Y : Scheme.{0}) (π₁ : S₁ ⟶ S) (Ga : Type) [Group Ga] (ρ₁ : Ga → (S₁ ⟶ S₁)) (f : S ⟶ Y) (A' : Over S₁) (A : Over S) (B : Over Y) [GrpObj A'] [GrpObj A] [GrpObj B] (φ₁ : A'.left ⟶ A.left) (ψ : A'.left ⟶ B.left) (φ : A.left ⟶ B.left), GlobalTheory.ZM.IsGaloisCover Ga ρ₁ π₁ → IsGrpPullback A' A π₁ φ₁ → IsGrpPullback A' B (π₁ ≫ f) ψ → φ₁ ≫ φ = ψ → IsGrpPullback A B f φ := by
  first | exact @GlobalTheory.GaloisCartDesc.isGrpPullback_of_galoisCover | exact GlobalTheory.GaloisCartDesc.isGrpPullback_of_galoisCover | (intros; apply GlobalTheory.GaloisCartDesc.isGrpPullback_of_galoisCover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualPullback
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB

set_option autoImplicit false

noncomputable section

open GlobalTheory.LB (resG_resG resG_self homOfLinear)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.QCoh (pullbackSections)

namespace GlobalTheory.DualPull

variable {X Y : Scheme.{0}}

abbrev cutO (T W : Y.Opens) : Y.Opens := T.ι ''ᵁ T.ι ⁻¹ᵁ W

theorem cutO_le (T W : Y.Opens) : cutO T W ≤ W := T.ι.image_preimage_le W

theorem cutO_le' (T W : Y.Opens) : cutO T W ≤ T := T.ι_image_le _

theorem le_cutO {T W S : Y.Opens} (h : S ≤ T) (h' : S ≤ W) : S ≤ cutO T W := by
  rw [cutO, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact le_inf h h'

theorem cutO_mono (T : Y.Opens) {W W' : Y.Opens} (h : W' ≤ W) : cutO T W' ≤ cutO T W :=
  le_cutO (cutO_le' _ _) ((cutO_le _ _).trans h)

def cut (T : Y.Opens) : Y.Modules :=
  (Scheme.Modules.pushforward T.ι).obj ((structureModule Y).restrict T.ι)

def cutEquiv (T W : Y.Opens) : Γ(cut T, W) ≃+ Γ(Y, cutO T W) := AddEquiv.refl _

theorem cutEquiv_smul (T W : Y.Opens) (a : Γ(Y, W)) (s : Γ(cut T, W)) :
    cutEquiv T W (a • s) = resG Y (cutO_le T W) a * cutEquiv T W s :=
  congrArg (· * cutEquiv T W s) congr($(T.ι.app_appIso_inv W) a)

theorem cutEquiv_res (T : Y.Opens) {W W' : Y.Opens} (h : W' ≤ W) (s : Γ(cut T, W)) :
    cutEquiv T W' (resM (cut T) h s) = resG Y (cutO_mono T h) (cutEquiv T W s) := rfl

variable {P : Y.Modules} {T : Y.Opens}

def toCut (l : Γ(dual P, T)) : P ⟶ cut T :=
  homOfLinear (fun W =>
    { toFun s := (cutEquiv T W).symm (dualApp l (cutO_le' T W) (resM P (cutO_le T W) s))
      map_add' s t := by simp only [map_add (f := _)]
      map_smul' a s := (cutEquiv T W).injective (by
        rw [RingHom.id_apply, cutEquiv_smul, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
          resM_smul, map_smul, smul_eq_mul]) })
    fun {W W'} h s => (cutEquiv T W').injective (by
      change dualApp l _ (resM P _ (resM P h s)) = resG Y (cutO_mono T h) (dualApp l _ (resM P _ s))
      rw [← dualApp_resM, resM_resM, resM_resM])

theorem toCut_app (l : Γ(dual P, T)) (W : Y.Opens) (s : Γ(P, W)) :
    cutEquiv T W ((toCut l).app W s) = dualApp l (cutO_le' T W) (resM P (cutO_le T W) s) := rfl

theorem toCut_injective {l l' : Γ(dual P, T)} (h : toCut l = toCut l') : l = l' :=
  dual_ext fun W hW s => by
    have := congrArg (resG Y (le_cutO hW le_rfl)) ((toCut_app l W s).symm.trans (h ▸ toCut_app l' W s))
    rwa [← dualApp_resM, ← dualApp_resM, resM_resM, resM_self] at this

def ofCut (φ : P ⟶ cut T) : Γ(dual P, T) :=
  dualMk (fun W h =>
    { toFun s := resG Y (le_cutO h le_rfl) (cutEquiv T W (φ.app W s))
      map_add' s t := by simp only [map_add (f := _)]
      map_smul' a s := by
        rw [Scheme.Modules.Hom.app_smul, cutEquiv_smul, map_mul, resG_resG, resG_self]; rfl })
    fun W W' h h' s => by
      change resG Y _ (cutEquiv T W' (φ.app W' (resM P h' s))) = resG Y h' (resG Y _ _)
      rw [app_resM, cutEquiv_res, resG_resG, resG_resG]

theorem dualApp_ofCut (φ : P ⟶ cut T) {W : Y.Opens} (h : W ≤ T) (s : Γ(P, W)) :
    dualApp (ofCut φ) h s = resG Y (le_cutO h le_rfl) (cutEquiv T W (φ.app W s)) := rfl

variable (f : Y ⟶ X)

def adj {F : X.Modules} {G : Y.Modules} (ψ : F ⟶ (Scheme.Modules.pushforward f).obj G) :
    (Scheme.Modules.pullback f).obj F ⟶ G :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv F G).symm ψ

theorem adj_app {F : X.Modules} {G : Y.Modules} (ψ : F ⟶ (Scheme.Modules.pushforward f).obj G)
    {V : X.Opens} (e : T ≤ f ⁻¹ᵁ V) (s : Γ(F, V)) :
    (adj f ψ).app T (pullbackSections f F e s) = resM G e (ψ.app V s) := by
  refine (QCoh.hom_app_res (adj f ψ) e _).trans (congrArg (resM G e) ?_)
  have := ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv F G).apply_symm_apply ψ
  rw [Adjunction.homEquiv_unit] at this
  exact congr(($this).app V s)

theorem pull_ext {F : X.Modules} {G : Y.Modules} {φ φ' : (Scheme.Modules.pullback f).obj F ⟶ G}
    (h : ∀ (V : X.Opens) (s : Γ(F, V)), φ.app _ (pullbackSections f F (le_refl (f ⁻¹ᵁ V)) s) =
      φ'.app _ (pullbackSections f F (le_refl (f ⁻¹ᵁ V)) s)) : φ = φ' := by
  refine ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv F G).injective ?_
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext s
  have e : pullbackSections f F (le_refl (f ⁻¹ᵁ V)) s = _ := QCoh.res_self _ _ _
  exact (congrArg (φ.app _) e).symm.trans ((h V s).trans (congrArg (φ'.app _) e))

variable {F G : X.Modules} {V : X.Opens}

theorem dual_pull_ext (e : T ≤ f ⁻¹ᵁ V) {l l' : Γ(dual ((Scheme.Modules.pullback f).obj F), T)}
    (h : ∀ (W : X.Opens) (_ : W ≤ V) (S : Y.Opens) (hS : S ≤ T) (e' : S ≤ f ⁻¹ᵁ W) (s : Γ(F, W)),
      dualApp l hS (pullbackSections f F e' s) = dualApp l' hS (pullbackSections f F e' s)) :
    l = l' := by
  refine toCut_injective (pull_ext f fun W s => (cutEquiv T _).injective ?_)
  have e' : cutO T (f ⁻¹ᵁ W) ≤ f ⁻¹ᵁ (W ⊓ V) :=
    le_inf (cutO_le T (f ⁻¹ᵁ W)) ((cutO_le' T (f ⁻¹ᵁ W)).trans e)
  have : resM _ (cutO_le T (f ⁻¹ᵁ W)) (pullbackSections f F (le_refl (f ⁻¹ᵁ W)) s) =
      pullbackSections f F e' (resM F inf_le_left s) :=
    (QCoh.res_pullbackSections f F _ _ _).trans (QCoh.pullbackSections_res f F e' _ _).symm
  rw [toCut_app, toCut_app, this]
  exact h _ inf_le_right _ _ _ _

theorem cutO_le_inf (V W : X.Opens) : cutO (f ⁻¹ᵁ V) (f ⁻¹ᵁ W) ≤ f ⁻¹ᵁ (W ⊓ V) :=
  le_inf (cutO_le (f ⁻¹ᵁ V) (f ⁻¹ᵁ W)) (cutO_le' (f ⁻¹ᵁ V) (f ⁻¹ᵁ W))

theorem appLE_resG {W : X.Opens} (h : W ≤ V) (e : T ≤ f ⁻¹ᵁ W) (a : Γ(X, V)) :
    f.appLE W T e (resG X h a) = f.appLE V T (e.trans (f.preimage_mono h)) a :=
  congr($(f.map_appLE e (homOfLE h).op) a)

theorem resG_appLE {S : Y.Opens} (h : S ≤ T) (e : T ≤ f ⁻¹ᵁ V) (a : Γ(X, V)) :
    resG Y h (f.appLE V T e a) = f.appLE V S (h.trans e) a :=
  congr($(f.appLE_map e (homOfLE h).op) a)

def formPush (l : Γ(dual F, V)) : F ⟶ (Scheme.Modules.pushforward f).obj (cut (f ⁻¹ᵁ V)) :=
  homOfLinear (fun W =>
    { toFun s := (cutEquiv (f ⁻¹ᵁ V) (f ⁻¹ᵁ W)).symm (f.appLE (W ⊓ V) _ (cutO_le_inf f V W)
        (dualApp l inf_le_right (resM F inf_le_left s)))
      map_add' s t := by simp only [map_add (f := _)]; rfl
      map_smul' a s := (cutEquiv (f ⁻¹ᵁ V) (f ⁻¹ᵁ W)).injective (by
        refine Eq.trans ?_ (cutEquiv_smul _ _ (f.app W a) _).symm
        rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
          resM_smul, map_smul, smul_eq_mul, map_mul, appLE_resG]
        rfl) })
    fun {W W'} h s => (cutEquiv (f ⁻¹ᵁ V) (f ⁻¹ᵁ W')).injective (by
      change f.appLE (W' ⊓ V) _ _ (dualApp l _ (resM F _ (resM F h s))) =
        resG Y (cutO_mono _ (f.preimage_mono h)) (f.appLE (W ⊓ V) _ _ (dualApp l _ (resM F _ s)))
      rw [resG_appLE, ← appLE_resG f (inf_le_inf_right V h) (cutO_le_inf f V W'), ← dualApp_resM,
        resM_resM, resM_resM])

def pullForm (l : Γ(dual F, V)) : Γ(dual ((Scheme.Modules.pullback f).obj F), f ⁻¹ᵁ V) :=
  ofCut (adj f (formPush f l))

theorem dualApp_pullForm (l : Γ(dual F, V)) {W : X.Opens} (h : W ≤ V) (hT : T ≤ f ⁻¹ᵁ V)
    (e : T ≤ f ⁻¹ᵁ W) (s : Γ(F, W)) :
    dualApp (pullForm f l) hT (pullbackSections f F e s) = f.appLE W T e (dualApp l h s) := by
  rw [pullForm, dualApp_ofCut, adj_app]
  change resG Y _ (resG Y (cutO_mono _ e) (f.appLE (W ⊓ V) _ (cutO_le_inf f V W)
    (dualApp l inf_le_right (resM F inf_le_left s)))) = _
  rw [resG_appLE, resG_appLE, dualApp_resM l h, appLE_resG]


variable (F) in
def pullFormHom :
    dual F ⟶ (Scheme.Modules.pushforward f).obj (dual ((Scheme.Modules.pullback f).obj F)) :=
  homOfLinear (fun V =>
    { toFun l := pullForm f l
      map_add' l l' := dual_pull_ext f le_rfl fun W h S hS e s => by
        change _ = dualApp (pullForm f l) hS _ + dualApp (pullForm f l') hS _
        rw [dualApp_pullForm f _ h, dualApp_pullForm f _ h, dualApp_pullForm f _ h, dualApp_add,
          LinearMap.add_apply, map_add]
      map_smul' a l := dual_pull_ext f le_rfl fun W h S hS e s => by
        change _ = resG Y hS (f.app V a) * dualApp (pullForm f l) hS _
        rw [dualApp_pullForm f _ h, dualApp_pullForm f _ h, dualApp_smul,
          LinearMap.smul_apply, smul_eq_mul, map_mul, appLE_resG]
        rfl })
    fun {V V'} hV l => dual_pull_ext f le_rfl fun W h S hS e s => by
      change dualApp (pullForm f (resM _ hV l)) hS _ =
        dualApp (pullForm f l) (hS.trans (f.preimage_mono hV)) _
      rw [dualApp_pullForm f _ h, dualApp_pullForm f _ (h.trans hV), dualApp_res]


variable (F) in
def theta : (Scheme.Modules.pullback f).obj (dual F) ⟶ dual ((Scheme.Modules.pullback f).obj F) :=
  adj f (pullFormHom f F)

theorem dualApp_theta (l : Γ(dual F, V)) {W : X.Opens} (h : W ≤ V) (e : T ≤ f ⁻¹ᵁ V)
    {S : Y.Opens} (hS : S ≤ T) (e' : S ≤ f ⁻¹ᵁ W) (s : Γ(F, W)) :
    dualApp ((theta f F).app T (pullbackSections f (dual F) e l)) hS (pullbackSections f F e' s) =
      f.appLE W S e' (dualApp l h s) := by
  rw [theta, adj_app]
  exact dualApp_pullForm f l h (hS.trans e) e' s

theorem isIso_theta {r : ℕ} (h : IsVB F r) : IsIso (theta f F) := by
  have := h.isQuasicoherent
  have := h.dual.isQuasicoherent
  refine isIso_of_frames (ι := Fin r) _ fun y => ?_
  obtain ⟨U, e, hx, he⟩ := h (f y)
  refine ⟨f ⁻¹ᵁ U, _, hx, he.dual.pullback f, ?_⟩
  have H (i : Fin r) : (theta f F).app _ (pullbackSections f (dual F) (le_refl (f ⁻¹ᵁ U))
      (he.coord i)) = (he.pullback f).coord i :=
    dual_pull_ext f le_rfl fun W hW S hS e' s => by
      rw [dualApp_theta f _ hW, IsFrame.dualApp_coord, IsFrame.dualApp_coord]
      exact (he.pullback_basis_repr f hW e' s i).symm
  rw [funext H]
  exact (he.pullback f).dual

end GlobalTheory.DualPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatGLOfInvT
open NumberField IsDedekindDomain Matrix Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.UG Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.BCWords GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ThetaSatake

open GlobalTheory.ThetaPull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

abbrev cw (w : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 E) :=
  conjSrc (IsCMField.complexConj E).toRingEquiv w

theorem theta_locGL (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin n) ((cw w).adicCompletion E)) :
    thetaGL n (cFin E) (locGL E n (cw w) g) =
      locGL E n w (thetaGL n (RingHom.id _) (Matrix.GeneralLinearGroup.map (conjLoc _ w) g)) := by
  have key : ∀ v, Matrix.GeneralLinearGroup.map (pLoc E v) (thetaGL n (cFin E) (locGL E n (cw w) g)) =
      thetaGL n (RingHom.id _) (Matrix.GeneralLinearGroup.map (conjLoc _ v)
        (Matrix.GeneralLinearGroup.map (pLoc E (cw v)) (locGL E n (cw w) g))) := fun v =>
    map_thetaGL (pLoc E v) (RingHom.id _) (RingHom.id _) (fun _ => rfl)
      (Matrix.GeneralLinearGroup.map (cFin E) (locGL E n (cw w) g))
  have key2 : ∀ v, Matrix.GeneralLinearGroup.map (pLoc E v) (thetaGL n (cFin E) (locGL E n (cw w) g)) =
      Matrix.GeneralLinearGroup.map (pLoc E v)
        (locGL E n w (thetaGL n (RingHom.id _) (Matrix.GeneralLinearGroup.map (conjLoc _ w) g))) := fun v => by
    rw [key]
    by_cases h : v = w
    · subst h
      rw [pLoc_locGL, pLoc_locGL]
    · rw [pLoc_locGL_of_ne h, pLoc_locGL_of_ne (fun e => h (conjSrc_injective _ e)), map_one, map_one]
  refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext _ fun v => ?_)
  exact congrArg (fun u : GL (Fin n) (v.adicCompletion E) => u.val i j) (key2 v)

theorem conjLoc_surj (w : HeightOneSpectrum (𝓞 E)) :
    Function.Surjective (conjLoc (IsCMField.complexConj E).toRingEquiv w) := fun y => by
  classical
  refine ⟨pLoc E _ (cFin E (sLoc E w y)), ?_⟩
  rw [← pLoc_conjFin]
  exact (congrArg (pLoc E w) (cFin_cFin _)).trans
    (Pi.single_eq_same (M := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) w y)

theorem absNorm_cw (w : HeightOneSpectrum (𝓞 E)) : Ideal.absNorm (cw w).asIdeal = Ideal.absNorm w.asIdeal := by
  rw [(GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc (IsCMField.complexConj E).toRingEquiv w)]
  simp only [Ideal.absNorm_eq_natCard]
  exact Nat.card_congr (Ideal.quotientEquiv (w.asIdeal.comap (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv)) w.asIdeal (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv)
    (Ideal.map_comap_of_surjective _ (RingEquiv.surjective _) _).symm).toEquiv

def cloc (w : HeightOneSpectrum (𝓞 E)) : (cw w).adicCompletion E ≃+* w.adicCompletion E :=
  RingEquiv.ofBijective (conjLoc _ w) ⟨(conjLoc _ w).injective, conjLoc_surj w⟩

theorem thetaGL_conj (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin n) ((cw w).adicCompletion E)) :
    thetaGL n (RingHom.id _) (Matrix.GeneralLinearGroup.map (conjLoc _ w) g) =
      PhiU n _ * GlobalTheory.LFun.ConjPlace.invT (cloc w) n g * (PhiU n _)⁻¹ := by
  have e1 : GlobalTheory.LFun.ConjPlace.invT (cloc w) n g =
      GlobalTheory.CuspRep.invT n _ (Matrix.GeneralLinearGroup.map (conjLoc _ w) g) :=
    Units.ext (Matrix.ext fun i j => GlobalTheory.LFun.ConjPlace.invT_val _ g i j)
  rw [e1]
  rfl

theorem phiU_mem {K : Type} [Field K] (O : Subring K) (n : ℕ) : PhiU n K ∈ Formalism.UG.GLint (Fin n) O := by
  have h : ∀ i j : Fin n, GlobalTheory.Tw.Phi n K i j ∈ O := fun i j => by
    simp only [GlobalTheory.Tw.Phi, Matrix.of_apply]
    split_ifs
    · exact pow_mem (neg_mem (one_mem O)) _
    · exact zero_mem O
  exact GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨h, fun i j => h j i⟩

theorem hasSatGL_of_invT {w w' : HeightOneSpectrum (𝓞 E)} {a : ℕ}
    (c : w.adicCompletion E ≃+* w'.adicCompletion E) (hc : ∀ x, Valued.v (c x) = Valued.v x)
    (hq : Formalism.UG.qV E w' = Formalism.UG.qV E w)
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V} {ρ' : Representation ℂ (GL (Fin a) (w'.adicCompletion E)) W}
    (T : V ≃ₗ[ℂ] W) (hT : ∀ g x, ρ' (GlobalTheory.LFun.ConjPlace.invT c a g) (T x) = T (ρ g x)) {B : Multiset ℂˣ}
    (h : GlobalTheory.LFun.HasSatGL w ρ B) : GlobalTheory.LFun.HasSatGL w' ρ' (B.map (·⁻¹)) := by
  have hK := GlobalTheory.LFun.ConjPlace.mem_iff_invT (n := a) c (GlobalTheory.LFun.ConjPlace.map_mem_Ov_iff c hc)
  have hf : ∀ g y, T.toLinearMap ((ρ.comp (GlobalTheory.LFun.ConjPlace.invT c a).symm.toMonoidHom) g y) =
      ρ' g (T.toLinearMap y) := fun g y => by
    change T (ρ ((GlobalTheory.LFun.ConjPlace.invT c a).symm g) y) = ρ' g (T y)
    rw [← hT, MulEquiv.apply_symm_apply]
  have key : ∀ x, GlobalTheory.LFun.IsSatVecGL w ρ x B → GlobalTheory.LFun.IsSatVecGL w' ρ' (T x) (B.map (·⁻¹)) := fun x hx =>
    (GlobalTheory.LFun.ConjPlace.isSatVecGL_invT c hc hq hx).map T.toLinearMap hf
      ((map_ne_zero_iff T T.injective).2 hx.1)
  constructor
  · obtain ⟨x, hx⟩ := h.exists_vec
    exact (Submodule.ne_bot_iff _).2 ⟨_, (key x hx).2.1, (key x hx).1⟩
  · intro y hy h0
    obtain ⟨x, rfl⟩ := T.surjective y
    refine key x (h.2 x (GlobalTheory.LGrp.mem_fixed.2 fun k hk => T.injective ?_) ((map_ne_zero_iff T T.injective).1 h0))
    have := GlobalTheory.LGrp.mem_fixed.1 hy _ ((hK k).1 hk)
    rwa [hT] at this

theorem hasSat_thetaSub {a : ℕ} (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (C : Multiset ℂˣ)
    (h : (CG.mk π).HasSat (cw w) C) : (CG.mk (thetaSub π)).HasSat w (C.map (·⁻¹)) := by
  rw [CG.hasSat_mk] at h ⊢
  let ρ' := (thetaSub π).locRep w
  let T₀ : π.V ≃ₗ[ℂ] (thetaSub π).V := (pull E a).submoduleMap π.V
  have h0 : ∀ g x, ρ' (thetaGL a (RingHom.id _) (Matrix.GeneralLinearGroup.map (conjLoc _ w) g)) (T₀ x) =
      T₀ (π.locRep (cw w) g x) := fun g x => by
    rw [CuspSub.locRep_eq, CuspSub.locRep_eq, ← theta_locGL]
    exact Subtype.ext (pull_act (.fin (locGL E a (cw w) g)) x.1).symm
  let k := PhiU a (w.adicCompletion E)
  let S : (thetaSub π).V ≃ₗ[ℂ] (thetaSub π).V :=
    LinearEquiv.ofLinear (ρ' k⁻¹) (ρ' k) (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)
      (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
  refine hasSatGL_of_invT (cloc w) (conjLoc_spec _ w).2.2 (absNorm_cw w).symm (T₀.trans S) (fun g x => ?_) h
  change ρ' _ (ρ' k⁻¹ (T₀ x)) = ρ' k⁻¹ (T₀ _)
  rw [← h0, thetaGL_conj, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  congr 2
  dsimp only [k]
  group

end GlobalTheory.ThetaSatake
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfIsOpen
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.TwTrLin

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem mem_fixed_iff (ρ : Representation ℂ G V) (H : Subgroup G) (v : V) :
    v ∈ fixed ρ H ↔ ∀ h ∈ H, ρ h v = v := by
  show (∀ h : H, ρ (h : G) v = ((1 : H →* ℂˣ) h : ℂ) • v) ↔ _
  simp only [MonoidHom.one_apply, Units.val_one, one_smul]
  exact ⟨fun H h hh => H ⟨h, hh⟩, fun H h => H h h.2⟩

theorem finite_out_support [TopologicalSpace G] [IsTopologicalGroup G] {K' : Subgroup G}
    (hK' : IsOpen (K' : Set G)) {f : G → ℂ} (hf : HasCompactSupport f) :
    {q : G ⧸ K' | f q.out ≠ 0}.Finite := by
  haveI : DiscreteTopology (G ⧸ K') := QuotientGroup.discreteTopology hK'
  have hc : IsCompact ((QuotientGroup.mk : G → G ⧸ K') '' tsupport f) :=
    hf.image QuotientGroup.continuous_mk
  refine hc.finite_of_discrete.subset ?_
  intro q hq
  exact ⟨q.out, subset_tsupport _ hq, QuotientGroup.out_eq' q⟩

theorem term_fin (ρ : Representation ℂ G V) (K' : Subgroup G) (f : G → ℂ) (A : V →ₗ[ℂ] V)
    (h : {q : G ⧸ K' | f q.out ≠ 0}.Finite) :
    Function.HasFiniteSupport fun q : G ⧸ K' => f q.out • (ρ q.out ∘ₗ A) :=
  h.subset (Function.support_smul_subset_left (fun q : G ⧸ K' => f q.out) fun q => ρ q.out ∘ₗ A)

theorem levOp_add (ρ : Representation ℂ G V) (K K' : Subgroup G) (f f' : G → ℂ) (A : V →ₗ[ℂ] V)
    (h : {q : G ⧸ K' | f q.out ≠ 0}.Finite) (h' : {q : G ⧸ K' | f' q.out ≠ 0}.Finite) :
    levOp ρ K K' (f + f') A = levOp ρ K K' f A + levOp ρ K K' f' A := by
  unfold levOp
  rw [← smul_add, ← finsum_add_distrib (term_fin ρ K' f A h) (term_fin ρ K' f' A h')]
  congr 1
  exact finsum_congr fun q => by simp [add_smul]

theorem levOp_smul_fun (ρ : Representation ℂ G V) (K K' : Subgroup G) (f : G → ℂ) (A : V →ₗ[ℂ] V) (c : ℂ) :
    levOp ρ K K' (c • f) A = c • levOp ρ K K' f A := by
  unfold levOp
  rw [smul_comm c, smul_finsum c]
  congr 1
  exact finsum_congr fun q => by simp [mul_smul]

theorem levOp_smul_op (ρ : Representation ℂ G V) (K K' : Subgroup G) (f : G → ℂ) (A : V →ₗ[ℂ] V) (c : ℂ) :
    levOp ρ K K' f (c • A) = c • levOp ρ K K' f A := by
  unfold levOp
  rw [smul_comm c, smul_finsum c]
  congr 1
  exact finsum_congr fun q => by rw [LinearMap.comp_smul, smul_comm]

end GlobalTheory.TwTrLin

namespace GlobalTheory.TwTrLin

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem A_fixed (ρ : Representation ℂ G V) (θ : G →* G) (hθ : ∀ g, θ (θ g) = g) (K' : Subgroup G)
    (hK'θ : ∀ k ∈ K', θ k ∈ K') (A : V →ₗ[ℂ] V) (hA : ∀ g, A ∘ₗ ρ g = ρ (θ g) ∘ₗ A) {v : V}
    (hv : v ∈ fixed ρ K') : A v ∈ fixed ρ K' := by
  rw [mem_fixed_iff] at hv ⊢
  intro k hk
  have := LinearMap.congr_fun (hA (θ k)) v
  simp only [LinearMap.comp_apply, hθ] at this
  rw [← this, hv _ (hK'θ k hk)]

theorem levOp_mapsTo (ρ : Representation ℂ G V) (K K' : Subgroup G) (A : V →ₗ[ℂ] V) (f : G → ℂ)
    (hfin : {q : G ⧸ K' | f q.out ≠ 0}.Finite)
    (hl : ∀ k ∈ K', ∀ x, f (k * x) = f x) (hr : ∀ k ∈ K', ∀ x, f (x * k) = f x)
    (hA : ∀ v ∈ fixed ρ K', A v ∈ fixed ρ K') :
    ∀ v ∈ fixed ρ K', levOp ρ K K' f A v ∈ fixed ρ K' := by
  intro v hv
  have hw := hA v hv
  have hw' := (mem_fixed_iff ρ K' (A v)).1 hw
  let F : G ⧸ K' → V := fun q => f q.out • ρ q.out (A v)
  have hF : ∀ x : G, F (QuotientGroup.mk x) = f x • ρ x (A v) := by
    intro x
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K' x
    simp only [F, hh, hr _ h.2, map_mul, Module.End.mul_apply, hw' _ h.2]
  have hFfin : Function.HasFiniteSupport F :=
    hfin.subset (Function.support_smul_subset_left (fun q : G ⧸ K' => f q.out) fun q => ρ q.out (A v))
  have hL : levOp ρ K K' f A v = ((K'.relIndex K : ℕ) : ℂ)⁻¹ • ∑ᶠ q, F q := by
    unfold levOp
    rw [LinearMap.smul_apply, ← LinearMap.applyₗ_apply_apply (R := ℂ) v,
      map_finsum _ (term_fin ρ K' f A hfin)]
    rfl
  rw [hL, mem_fixed_iff]
  intro k hk
  rw [map_smul, map_finsum _ hFfin]
  congr 1
  have hk' : ∀ q, ρ k (F q) = F (k • q) := by
    intro q
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rw [MulAction.Quotient.smul_mk, hF, smul_eq_mul, hl _ hk]
    simp only [F, map_smul, map_mul, Module.End.mul_apply]
  simp_rw [hk']
  exact finsum_comp_equiv (MulAction.toPerm k : Equiv.Perm (G ⧸ K'))

end GlobalTheory.TwTrLin

namespace GlobalTheory.TwTrLin

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem twTr_eq (ρ : Representation ℂ G V) (K K' : Subgroup G) (f : G → ℂ) (A : V →ₗ[ℂ] V)
    (h : ∀ v ∈ fixed ρ K', levOp ρ K K' f A v ∈ fixed ρ K') :
    twTr ρ K K' f A = LinearMap.trace ℂ (fixed ρ K') ((levOp ρ K K' f A).restrict h) := dif_pos h

theorem trace_restrict_congr {W : Submodule ℂ V} {L L' : V →ₗ[ℂ] V} (e : L = L') (h : ∀ v ∈ W, L v ∈ W)
    (h' : ∀ v ∈ W, L' v ∈ W) : LinearMap.trace ℂ W (L.restrict h) = LinearMap.trace ℂ W (L'.restrict h') := by
  subst e; rfl

theorem restrict_add' {W : Submodule ℂ V} (L₁ L₂ : V →ₗ[ℂ] V) (h₁ : ∀ v ∈ W, L₁ v ∈ W) (h₂ : ∀ v ∈ W, L₂ v ∈ W)
    (h : ∀ v ∈ W, (L₁ + L₂) v ∈ W) : (L₁ + L₂).restrict h = L₁.restrict h₁ + L₂.restrict h₂ := by
  ext x; simp [LinearMap.restrict_apply]

theorem restrict_smul' {W : Submodule ℂ V} (L : V →ₗ[ℂ] V) (c : ℂ) (h₁ : ∀ v ∈ W, L v ∈ W)
    (h : ∀ v ∈ W, (c • L) v ∈ W) : (c • L).restrict h = c • L.restrict h₁ := by
  ext x; simp [LinearMap.restrict_apply]

theorem trace_id_eq_finrank (W : Type) [AddCommGroup W] [Module ℂ W] :
    LinearMap.trace ℂ W LinearMap.id = (Module.finrank ℂ W : ℂ) := by
  by_cases hW : Module.Finite ℂ W
  · exact LinearMap.trace_id ℂ W
  · rw [Module.finrank_of_not_finite hW]
    unfold LinearMap.trace
    rw [dite_eq_right]
    · simp
    · rintro ⟨s, ⟨b⟩⟩
      exact hW (Module.Finite.of_basis b)

theorem relIndex_ne_zero_of_isOpen [TopologicalSpace G] [IsTopologicalGroup G] {K K' : Subgroup G}
    (hKc : IsCompact (K : Set G)) (hK'o : IsOpen (K' : Set G)) : K'.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  haveI : Finite (K ⧸ K'.subgroupOf K) :=
    Subgroup.quotient_finite_of_isOpen _ (hK'o.preimage continuous_subtype_val)
  exact Subgroup.index_ne_zero_of_finite

theorem levOp_unit (ρ : Representation ℂ G V) (K K' : Subgroup G) :
    ∃ x₀ ∈ K', levOp ρ K K' ((K' : Set G).indicator 1) LinearMap.id = ((K'.relIndex K : ℕ) : ℂ)⁻¹ • ρ x₀ := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K' (1 : G)
  refine ⟨h, h.2, ?_⟩
  unfold levOp
  have hout : ∀ q : G ⧸ K', q ≠ (QuotientGroup.mk 1 : G ⧸ K') → q.out ∉ K' := by
    intro q hq hm
    apply hq
    rw [← QuotientGroup.out_eq' q]
    exact QuotientGroup.eq.2 (by simpa using K'.inv_mem hm)
  rw [finsum_eq_single _ (QuotientGroup.mk 1 : G ⧸ K')
    (fun q hq => by rw [Set.indicator_of_notMem (hout q hq), zero_smul])]
  rw [hh, one_mul, Set.indicator_of_mem h.2]
  simp

end GlobalTheory.TwTrLin

namespace GlobalTheory.TwTrLin

theorem twTr_linear : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), ∀ (θ : G →* G), (∀ g, θ (θ g) = g) → ∀ A : V →ₗ[ℂ] V, (∀ g, A ∘ₗ ρ g = ρ (θ g) ∘ₗ A) → ∀ K' : Subgroup G, IsLevel θ K K' → (∀ f f' (c : ℂ), IsHecke K' f → IsHecke K' f' → twTr ρ K K' (f + f') A = twTr ρ K K' f A + twTr ρ K K' f' A ∧ twTr ρ K K' (c • f) A = c * twTr ρ K K' f A ∧ twTr ρ K K' f (c • A) = c * twTr ρ K K' f A) ∧ (fixed ρ K' = ⊥ → ∀ f, twTr ρ K K' f A = 0) ∧ twTr ρ K K' ((K' : Set G).indicator 1) LinearMap.id = ((K'.relIndex K : ℕ) : ℂ)⁻¹ * (Module.finrank ℂ (fixed ρ K') : ℂ) ∧ K'.relIndex K ≠ 0 := by
  intro G _ _ _ K _ hKc V _ _ ρ θ hθ A hA K' hlev
  obtain ⟨hK'o, _, hK'θ⟩ := hlev
  have hAf : ∀ v ∈ fixed ρ K', A v ∈ fixed ρ K' := fun v hv => A_fixed ρ θ hθ K' hK'θ A hA hv
  have hmaps : ∀ f, IsHecke K' f → ∀ v ∈ fixed ρ K', levOp ρ K K' f A v ∈ fixed ρ K' := fun f hf =>
    levOp_mapsTo ρ K K' A f (finite_out_support hK'o hf.1) (fun k hk x => (hf.2 k hk x).1)
      (fun k hk x => (hf.2 k hk x).2) hAf
  refine ⟨?_, ?_, ?_, relIndex_ne_zero_of_isOpen hKc hK'o⟩
  · intro f f' c hf hf'
    have h1 := hmaps f hf
    have h2 := hmaps f' hf'
    have e1 := levOp_add ρ K K' f f' A (finite_out_support hK'o hf.1) (finite_out_support hK'o hf'.1)
    have e2 := levOp_smul_fun ρ K K' f A c
    have e3 := levOp_smul_op ρ K K' f A c
    have h12 : ∀ v ∈ fixed ρ K', levOp ρ K K' (f + f') A v ∈ fixed ρ K' := by
      intro v hv; rw [e1]; exact add_mem (h1 v hv) (h2 v hv)
    have hs : ∀ v ∈ fixed ρ K', (c • levOp ρ K K' f A) v ∈ fixed ρ K' := fun v hv =>
      Submodule.smul_mem _ c (h1 v hv)
    have hc : ∀ v ∈ fixed ρ K', levOp ρ K K' (c • f) A v ∈ fixed ρ K' := by
      intro v hv; rw [e2]; exact hs v hv
    have hc' : ∀ v ∈ fixed ρ K', levOp ρ K K' f (c • A) v ∈ fixed ρ K' := by
      intro v hv; rw [e3]; exact hs v hv
    refine ⟨?_, ?_, ?_⟩
    · rw [twTr_eq _ _ _ _ _ h12, twTr_eq _ _ _ _ _ h1, twTr_eq _ _ _ _ _ h2,
        trace_restrict_congr e1 h12 (fun v hv => add_mem (h1 v hv) (h2 v hv)), restrict_add' _ _ h1 h2, map_add]
    · rw [twTr_eq _ _ _ _ _ hc, twTr_eq _ _ _ _ _ h1, trace_restrict_congr e2 hc hs, restrict_smul' _ c h1,
        map_smul, smul_eq_mul]
    · rw [twTr_eq _ _ _ _ _ hc', twTr_eq _ _ _ _ _ h1, trace_restrict_congr e3 hc' hs, restrict_smul' _ c h1,
        map_smul, smul_eq_mul]
  · intro h0 f
    unfold twTr
    split_ifs with h
    · haveI : Subsingleton (fixed ρ K') := by
        have key : ∀ v : V, v ∈ fixed ρ K' → v = 0 := fun v hv => by
          rw [h0] at hv
          exact (Submodule.mem_bot ℂ).1 hv
        exact ⟨fun a b => Subtype.ext ((key _ a.2).trans (key _ b.2).symm)⟩
      rw [show (levOp ρ K K' f A).restrict h = 0 from LinearMap.ext fun x => Subsingleton.elim _ _, map_zero]
    · rfl
  · obtain ⟨x₀, hx₀, hL⟩ := levOp_unit ρ K K'
    have hfx : ∀ v ∈ fixed ρ K', ρ x₀ v = v := fun v hv => (mem_fixed_iff ρ K' v).1 hv x₀ hx₀
    have hm : ∀ v ∈ fixed ρ K', levOp ρ K K' ((K' : Set G).indicator 1) LinearMap.id v ∈ fixed ρ K' := by
      intro v hv
      rw [hL, LinearMap.smul_apply, hfx v hv]
      exact Submodule.smul_mem _ _ hv
    rw [twTr_eq _ _ _ _ _ hm]
    have hr : (levOp ρ K K' ((K' : Set G).indicator 1) LinearMap.id).restrict hm =
        ((K'.relIndex K : ℕ) : ℂ)⁻¹ • LinearMap.id := by
      ext x
      simp [LinearMap.restrict_apply, hL, hfx x.1 x.2]
    rw [hr, map_smul, trace_id_eq_finrank, smul_eq_mul]

end GlobalTheory.TwTrLin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdelicAbsValueCpowCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdelicAbsValueCpowCharacter
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ResW

theorem dchi_absC_one_finrank (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (s : ℂ) :
    dchi (GlobalTheory.CuspRep.Model.absC E s) 1 = s * (Module.finrank ℚ E : ℂ) := by
  let A : Cinf E →L[ℝ] ℂ :=
    s • ∑ w, (2 : ℝ) • (Complex.ofRealCLM.comp (Complex.reCLM.comp (ContinuousLinearMap.proj w)))
  have h : dchi (GlobalTheory.CuspRep.Model.absC E s) = A := fderiv_extZero (continuous_chiInf _) fun z => by
    change Complex.exp (s * GlobalTheory.Mem.Chr.CharModel.logNorm E (infId E (expU z))) = _
    rw [GlobalTheory.CuspRep.Model.logNorm_infId]
    congr 1
    simp [A, expU, Complex.norm_exp]
  have h2 : Module.finrank ℚ E = 2 * Fintype.card (InfinitePlace E) := by
    rw [IsTotallyComplex.finrank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
  rw [h, h2]
  simp [A, mul_comm]

theorem exists_abs_cpow : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (z : ℂ), ∃ χ : HChar E, (∀ (a : ℕ) (φ : Sm E a), zc E a (mulChi a χ φ) = mulChi a χ (zc E a φ + (a * (Module.finrank ℚ E : ℂ) * z) • φ)) ∧ (∀ v, χ.UnrAt v ∧ ((χ.val v : ℂˣ) : ℂ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-z)) ∧ (∀ x, ‖((χ.1 x : ℂˣ) : ℂ)‖ = ‖(((nu E z.re).1 x : ℂˣ) : ℂ)‖) ∧ (z.im = 0 → χ = nu E z.re) := by
  intro E _ _ _ z
  refine ⟨GlobalTheory.CuspRep.Model.absC E z, fun a φ => ?_, fun v => ⟨fun x hx => Units.ext ?_, ?_⟩, fun x => ?_, fun hz => ?_⟩
  · unfold zc
    rw [lie_mulChi]
    have e : (Matrix.of (fun i j : Fin a => if i = j then (1 : Cinf E) else 0)).trace = (a : ℝ) • (1 : Cinf E) := by
      simp [Matrix.trace, Nat.cast_smul_eq_nsmul]
    rw [e, map_smul, dchi_absC_one_finrank]
    congr 3
    simp only [Complex.real_smul, Complex.ofReal_natCast]; ring
  · change Complex.exp (z * GlobalTheory.Mem.Chr.CharModel.logNorm E (GlobalTheory.Mem.Chr.localIdele E v x)) = 1
    rw [GlobalTheory.Mem.Chr.CharModel.logNorm_local v x 0 (by simpa [IsUnitAt] using hx)]; simp
  · change Complex.exp (z * GlobalTheory.Mem.Chr.CharModel.logNorm E (GlobalTheory.Mem.Chr.localIdele E v (atFin v (unif v)))) = _
    have h0 : (Ideal.absNorm v.asIdeal : ℕ) ≠ 0 := by simpa [Ideal.absNorm_eq_zero_iff] using v.ne_bot
    rw [GlobalTheory.Mem.Chr.CharModel.logNorm_local v _ 1 (unif_spec v), Complex.cpow_def_of_ne_zero (by exact_mod_cast h0),
      ← Complex.natCast_log]
    congr 1; push_cast; ring
  · change ‖Complex.exp (z * GlobalTheory.Mem.Chr.CharModel.logNorm E x)‖ =
      ‖Complex.exp ((z.re : ℂ) * GlobalTheory.Mem.Chr.CharModel.logNorm E x)‖
    rw [Complex.norm_exp, Complex.norm_exp]; simp
  · have e : z = (z.re : ℂ) := Complex.ext rfl (by simpa using hz)
    conv_lhs => rw [e]
    rfl

end GlobalTheory.ResW

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdelicAbsValueCpowCharacterStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idelic_absValue_cpow_character : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (z : ℂ), ∃ χ : HChar E, (∀ (a : ℕ) (φ : Sm E a), zc E a (mulChi a χ φ) = mulChi a χ (zc E a φ + (a * (Module.finrank ℚ E : ℂ) * z) • φ)) ∧ (∀ v, χ.UnrAt v ∧ ((χ.val v : ℂˣ) : ℂ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-z)) ∧ (∀ x, ‖((χ.1 x : ℂˣ) : ℂ)‖ = ‖(((nu E z.re).1 x : ℂˣ) : ℂ)‖) ∧ (z.im = 0 → χ = nu E z.re) := by
  first | exact @GlobalTheory.ResW.exists_abs_cpow | exact GlobalTheory.ResW.exists_abs_cpow | (intros; apply GlobalTheory.ResW.exists_abs_cpow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralCharacterSubquotientProductIrreducibles
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralCharacterSubquotientProductIrreducibles
open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv

namespace GlobalTheory.GamMul

theorem centralChar_subquotient_prodIrr : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], (∀ x : IrrGL (k := k), ∃ ω : kˣ →* ℂˣ, HasCentralChar x.rep ω) ∧ ∀ (t m : ℕ) (x : Fin t → IrrGL (k := k)) (hd : ∑ a, (x a).1 = m) (ω : Fin t → kˣ →* ℂˣ), (∀ a, HasCentralChar (x a).rep (ω a)) → ∀ (τ : IrrRep (GL (Fin m) k)) (ω' : kˣ →* ℂˣ), IsSubquotient τ.ρ (prodIrr x hd) → HasCentralChar τ.ρ ω' → ω' = ∏ a, ω a := by
  intro k _ _ _ _
  refine ⟨fun y => ?_, fun t m x hd ω hω τ ω' hsub hω' => ?_⟩
  · obtain ⟨f, _, hf⟩ := LocGL.exists_smooth_hasCentralChar y.2.rep.smooth y.2.rep.irr
    exact ⟨f, hf⟩
  · have hcen : HasCentralChar (prodIrr x hd) (∏ a, ω a) :=
      CentralSupport.hasCentralChar_multiProd_prod _ (fun a => (x a).rep) ω hω
    have := Model.nontrivial_of_isIrreducible τ.irr
    obtain ⟨v, hv⟩ := exists_ne (0 : τ.V)
    ext z
    have h1 := Model.scalar_of_isSubquotient hsub (hcen z) v
    rw [hω'] at h1
    exact smul_left_injective ℂ hv h1

end GlobalTheory.GamMul
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralCharacterSubquotientProductIrreduciblesStatement
open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralCharacter_subquotient_productIrreducibles : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], (∀ x : IrrGL (k := k), ∃ ω : kˣ →* ℂˣ, HasCentralChar x.rep ω) ∧ ∀ (t m : ℕ) (x : Fin t → IrrGL (k := k)) (hd : ∑ a, (x a).1 = m) (ω : Fin t → kˣ →* ℂˣ), (∀ a, HasCentralChar (x a).rep (ω a)) → ∀ (τ : IrrRep (GL (Fin m) k)) (ω' : kˣ →* ℂˣ), IsSubquotient τ.ρ (prodIrr x hd) → HasCentralChar τ.ρ ω' → ω' = ∏ a, ω a := by
  first | exact @GlobalTheory.GamMul.centralChar_subquotient_prodIrr | exact GlobalTheory.GamMul.centralChar_subquotient_prodIrr | (intros; apply GlobalTheory.GamMul.centralChar_subquotient_prodIrr <;> assumption)
end
end
