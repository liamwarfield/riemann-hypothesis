module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GmMulEqOfResMulEq
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFamFieldPull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PhiRelTransport
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsGTransport
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PowEqOneOfPush
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFiniteCubeInduction
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ESecCompOfIsGrpPullback
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU

variable {S S' : Scheme.{0}} {f : S' ⟶ S}

private theorem comp_mul_of_isGrpPullback_lift {G H : Over S} {G' H' : Over S'} [GrpObj G] [GrpObj H]
    [GrpObj G'] [GrpObj H'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (hφ : IsGrpPullback G' G f φ)
    (hψ : IsGrpPullback H' H f ψ) (a : G ⟶ H) [IsMonHom a] (a' : G' ⟶ H') (h : a'.left ≫ ψ = φ ≫ a.left)
    {T : Over S'} (x y : T ⟶ G') : (x * y) ≫ a' = (x ≫ a') * (y ≫ a') := by
  apply Over.OverMorphism.ext
  apply hψ.1.hom_ext
  · let x₀ : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk (x.left ≫ φ) (by
      show (x.left ≫ φ) ≫ G.hom = T.hom ≫ f
      rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w])
    let y₀ : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk (y.left ≫ φ) (by
      show (y.left ≫ φ) ≫ G.hom = T.hom ≫ f
      rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w])
    let x₁ : Over.mk (T.hom ≫ f) ⟶ H := Over.homMk ((x ≫ a').left ≫ ψ) (by
      show ((x ≫ a').left ≫ ψ) ≫ H.hom = T.hom ≫ f
      rw [Category.assoc, hψ.1.w, ← Category.assoc, Over.w])
    let y₁ : Over.mk (T.hom ≫ f) ⟶ H := Over.homMk ((y ≫ a').left ≫ ψ) (by
      show ((y ≫ a').left ≫ ψ) ≫ H.hom = T.hom ≫ f
      rw [Category.assoc, hψ.1.w, ← Category.assoc, Over.w])
    have e1 := hφ.2 T x y x₀ y₀ rfl rfl
    have e2 := hψ.2 T (x ≫ a') (y ≫ a') x₁ y₁ rfl rfl
    have e3 : x₁ = x₀ ≫ a := by
      apply Over.OverMorphism.ext
      simp only [x₁, x₀, Over.comp_left, Over.homMk_left, Category.assoc, h]
    have e4 : y₁ = y₀ ≫ a := by
      apply Over.OverMorphism.ext
      simp only [y₁, y₀, Over.comp_left, Over.homMk_left, Category.assoc, h]
    calc ((x * y) ≫ a').left ≫ ψ = (x * y).left ≫ φ ≫ a.left := by
          rw [Over.comp_left, Category.assoc, h]
      _ = ((x₀ * y₀) ≫ a).left := by rw [← Category.assoc, ← e1, Over.comp_left]
      _ = (x₁ * y₁).left := by rw [MonObj.mul_comp, e3, e4]
      _ = ((x ≫ a') * (y ≫ a')).left ≫ ψ := e2
  · rw [Over.w, Over.w]

theorem isMonHom_of_over_isMonHom {G H : Over S} {G' H' : Over S'} [GrpObj G] [GrpObj H] [GrpObj G'] [GrpObj H']
    {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (hφ : IsGrpPullback G' G f φ) (hψ : IsGrpPullback H' H f ψ)
    (a : G ⟶ H) [IsMonHom a] (a' : G' ⟶ H') (h : a'.left ≫ ψ = φ ≫ a.left) : IsMonHom a' := by
  have key := fun (T : Over S') (x y : T ⟶ G') => comp_mul_of_isGrpPullback_lift hφ hψ a a' h x y
  have hmul : μ ≫ a' = (a' ⊗ₘ a') ≫ μ := by
    have := key (G' ⊗ G') (fst G' G') (snd G' G')
    simpa [Hom.mul_def] using this
  have h1 : (1 : 𝟙_ (Over S') ⟶ G') = η := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have h1' : (1 : 𝟙_ (Over S') ⟶ H') = η := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have hone : η ≫ a' = η := by
    have e := key _ (1 : 𝟙_ (Over S') ⟶ G') 1
    rw [_root_.mul_one] at e
    have e' : ((1 : 𝟙_ (Over S') ⟶ G') ≫ a') * 1 = ((1 : 𝟙_ (Over S') ⟶ G') ≫ a') * ((1 : 𝟙_ (Over S') ⟶ G') ≫ a') := by
      rw [_root_.mul_one]; exact e
    have e'' := (mul_left_cancel e').symm
    rw [h1, h1'] at e''
    exact e''
  exact { one_hom := hone, mul_hom := hmul }

theorem eSec_comp_of_isGrpPullback {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left}
    (hφ : IsGrpPullback G' G f φ) : (η[G']).left ≫ φ = f ≫ (η[G]).left := by
  have h1 : (1 : 𝟙_ (Over S') ⟶ G') = η[G'] := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  let P : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G := Over.homMk ((η[G']).left ≫ φ) (by
    show ((η[G']).left ≫ φ) ≫ G.hom = (𝟙_ (Over S')).hom ≫ f
    rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w])
  have e := hφ.2 (𝟙_ (Over S')) η[G'] η[G'] P P rfl rfl
  have hP : P * P = P := by
    apply Over.OverMorphism.ext
    rw [e, ← h1, _root_.mul_one, h1]
    rfl
  have hP1 : P = 1 := mul_eq_left.mp hP
  have hl := congrArg Over.Hom.left hP1
  rw [Hom.one_def, Over.comp_left] at hl
  change (η[G']).left ≫ φ = _ at hl
  rw [hl]
  congr 1

theorem IsWt.pull {X : Type} [AddCommGroup X] {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G f F) {i : splitTorus S X ⟶ G} {i' : splitTorus S' X ⟶ G'}
    (hi : TorusCompat f F i' i) {V : G.left.Opens} {V' : G'.left.Opens} (hV : V' ≤ F ⁻¹ᵁ V) {u : Γ(G.left, V)}
    {χ : X} (hu : IsWt i V u χ) : IsWt i' V' ((F.appLE V V' hV).hom u) χ := by
  obtain ⟨τ, hτ, hχ, hτi⟩ := hi
  intro Z' t' g' h₁ h₂
  let Z : Over S := Over.mk (Z'.hom ≫ f)
  let t : Z ⟶ splitTorus S X := Over.homMk (t'.left ≫ τ) (by
    show (t'.left ≫ τ) ≫ (splitTorus S X).hom = Z'.hom ≫ f
    rw [Category.assoc, hτ, ← Category.assoc, Over.w])
  let g : Z ⟶ G := Over.homMk (g'.left ≫ F) (by
    show (g'.left ≫ F) ≫ G.hom = Z'.hom ≫ f
    rw [Category.assoc, hF.1.w, ← Category.assoc, Over.w])
  let x₀ : Z ⟶ G := Over.homMk ((t' ≫ i').left ≫ F) (by
    show ((t' ≫ i').left ≫ F) ≫ G.hom = Z'.hom ≫ f
    rw [Category.assoc, hF.1.w, ← Category.assoc, Over.w])
  have hx₀ : t ≫ i = x₀ := by
    apply Over.OverMorphism.ext
    simp only [t, x₀, Over.comp_left, Over.homMk_left, Category.assoc, hτi]
  have hmul : (t ≫ i * g).left = (t' ≫ i' * g').left ≫ F := by
    rw [hx₀]
    exact hF.2 Z' (t' ≫ i') g' x₀ g rfl rfl
  have h₁' : ⊤ ≤ (t ≫ i * g).left ⁻¹ᵁ V := by
    rw [hmul]
    intro x _
    exact hV (h₁ trivial)
  have h₂' : ⊤ ≤ g.left ⁻¹ᵁ V := by
    intro x _
    exact hV (h₂ trivial)
  have key := hu Z t g h₁' h₂'
  have hcong : ∀ (a b : Z'.left ⟶ G.left) (hab : a = b) (ha : ⊤ ≤ a ⁻¹ᵁ V) (hb : ⊤ ≤ b ⁻¹ᵁ V),
      (a.appLE V ⊤ ha).hom u = (b.appLE V ⊤ hb).hom u := by
    intro a b hab ha hb
    subst hab
    rfl
  have e1 : ((t' ≫ i' * g').left.appLE V' ⊤ h₁).hom ((F.appLE V V' hV).hom u) =
      (((t' ≫ i' * g').left ≫ F).appLE V ⊤ (by intro x _; exact hV (h₁ trivial))).hom u := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  have e2 : (g'.left.appLE V' ⊤ h₂).hom ((F.appLE V V' hV).hom u) =
      ((g'.left ≫ F).appLE V ⊤ (by intro x _; exact hV (h₂ trivial))).hom u := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  have hc : (t.left.appTop).hom (charUnit S X χ).val = (t'.left.appTop).hom (charUnit S' X χ).val := by
    show ((t'.left ≫ τ).appTop).hom _ = _
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hχ]
  rw [e1, e2]
  exact (hcong _ _ hmul.symm _ h₁').trans (key.trans (congrArg₂ (· * ·) hc (hcong _ _ rfl h₂' _)))

theorem exists_tq_baseChange : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (X : Type) [AddCommGroup X] (G : Over S) [GrpObj G]
    (G' : Over S') [GrpObj G'] (F : G'.left ⟶ G.left), IsGrpPullback G' G f F →
    ∀ Q : TQ G X, ∃ Q' : TQ G' X, TorusCompat f F Q'.i Q.i := by
  intro S S' f X _ G _ G' _ F hF Q
  letI := Q.grp
  letI := Q.comm
  haveI := Q.q_hom
  haveI := Q.i_hom
  obtain ⟨i', hi', -⟩ := existsUnique_torusCompat hF.1 Q.i
  haveI : IsMonHom i' := TorusCompat.isMonHom hF hi'
  have hB := isGrpPullback_pullback Q.B f
  let q' : G' ⟶ (Over.pullback f).obj Q.B :=
    Over.homMk (pullback.lift (F ≫ Q.q.left) G'.hom (by rw [Category.assoc, Over.w Q.q, hF.1.w]))
      (by exact pullback.lift_snd _ _ _)
  have hq'fst : q'.left ≫ pullback.fst Q.B.hom f = F ≫ Q.q.left := pullback.lift_fst _ _ _
  haveI : IsMonHom q' := isMonHom_of_over_isMonHom hF hB Q.q q' hq'fst
  have hBsq : IsPullback F q'.left Q.q.left (pullback.fst Q.B.hom f) := by
    refine IsPullback.of_bot ?_ hq'fst.symm (IsPullback.of_hasPullback Q.B.hom f)
    have e1 : q'.left ≫ pullback.snd Q.B.hom f = G'.hom := pullback.lift_snd _ _ _
    rw [e1, Over.w Q.q]
    exact hF.1
  have hAb : IsAbelianScheme ((Over.pullback f).obj Q.B) := by
    haveI := Q.isAb.smooth
    haveI := Q.isAb.proper
    haveI := Q.isAb.geomConnected
    exact ⟨inferInstance, by simp only [Over.pullback_obj_hom]; infer_instance,
      by simp only [Over.pullback_obj_hom]; infer_instance, by simp only [Over.pullback_obj_hom]; infer_instance⟩
  have hη : (η[(Over.pullback f).obj Q.B]).left ≫ pullback.fst Q.B.hom f = f ≫ (η[Q.B]).left :=
    eSec_comp_of_isGrpPullback hB
  have hT' : (toUnit (splitTorus S' X)).left = (splitTorus S' X).hom := by
    have := Over.w (toUnit (splitTorus S' X))
    simpa using this
  have hT : (toUnit (splitTorus S X)).left = (splitTorus S X).hom := by
    have := Over.w (toUnit (splitTorus S X))
    simpa using this
  have hker0 : IsPullback Q.i.left (splitTorus S X).hom Q.q.left (η[Q.B]).left := by
    have h0 : IsPullback Q.i.left (toUnit (splitTorus S X)).left Q.q.left (η[Q.B]).left :=
      Q.isKernel.map (Over.forget S)
    rw [hT] at h0
    exact h0
  have hcomp : IsPullback (i'.left ≫ F) (splitTorus S' X).hom Q.q.left
      ((η[(Over.pullback f).obj Q.B]).left ≫ pullback.fst Q.B.hom f) := by
    rw [← torusCompat_iff.mp hi', hη]
    exact (SplitTorus.isGrpPullback_bcMap f X).1.paste_horiz hker0
  have hcommA : i'.left ≫ q'.left = (splitTorus S' X).hom ≫ (η[(Over.pullback f).obj Q.B]).left := by
    apply hB.1.hom_ext
    · simpa only [Category.assoc, hq'fst] using hcomp.w
    · rw [Category.assoc, Over.w q', Over.w i', Category.assoc, Over.w η[(Over.pullback f).obj Q.B]]
      simp
  have hA : IsPullback i'.left (splitTorus S' X).hom q'.left (η[(Over.pullback f).obj Q.B]).left :=
    IsPullback.of_right hcomp hcommA hBsq
  have hker : IsPullback i' (toUnit (splitTorus S' X)) q' η := by
    apply IsPullback.of_map (Over.forget S')
    · apply Over.OverMorphism.ext
      show i'.left ≫ q'.left = (toUnit (splitTorus S' X)).left ≫ (η[(Over.pullback f).obj Q.B]).left
      rw [hT']
      exact hcommA
    · show IsPullback i'.left (toUnit (splitTorus S' X)).left q'.left (η[(Over.pullback f).obj Q.B]).left
      rw [hT']
      exact hA
  have hloc : ∀ (b : ((Over.pullback f).obj Q.B).left) (χ : X),
      ∃ V, b ∈ V ∧ ∃ u : (Γ(G'.left, q'.left ⁻¹ᵁ V))ˣ, IsWt i' (q'.left ⁻¹ᵁ V) (↑u) χ := by
    intro b χ
    obtain ⟨V, hbV, u, hu⟩ := Q.loc ((pullback.fst Q.B.hom f).base b) χ
    have hle : q'.left ⁻¹ᵁ (pullback.fst Q.B.hom f ⁻¹ᵁ V) ≤ F ⁻¹ᵁ (Q.q.left ⁻¹ᵁ V) := by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hq'fst]
    refine ⟨pullback.fst Q.B.hom f ⁻¹ᵁ V, hbV, Units.map (F.appLE _ _ hle).hom.toMonoidHom u, ?_⟩
    exact IsWt.pull hF hi' hle hu
  exact ⟨TQ.mk _ hAb q' i' inferInstance inferInstance
    (MorphismProperty.of_isPullback (P := @Flat) hBsq Q.q_flat)
    (MorphismProperty.of_isPullback (P := @Surjective) hBsq Q.q_surj)
    (MorphismProperty.of_isPullback (P := @IsAffineHom) hBsq Q.q_affine) hker hloc, hi'⟩

end GlobalTheory.UU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubWeilOneLeft
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU

private theorem isCub_mul_swap_middle {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ)
    (a b c d y : A) :
    θ a b y * θ (a * b) (c * d) y * θ c d y = θ (a * c) (b * d) y * θ a c y * θ b d y := by
  have e1 : θ a b y * θ (a * b) (c * d) y = θ a (b * (c * d)) y * θ b (c * d) y := by
    rw [_root_.mul_comm]; exact h.coc a b (c * d) y
  have e2 : θ b (c * d) y * θ c d y = θ (b * c) d y * θ b c y := (h.coc b c d y).symm
  have e3 : θ (a * c) (b * d) y * θ a c y = θ a (c * (b * d)) y * θ c (b * d) y := h.coc a c (b * d) y
  have e4 : θ c (b * d) y * θ b d y = θ (c * b) d y * θ c b y := (h.coc c b d y).symm
  rw [e1, _root_.mul_assoc, e2, e3, _root_.mul_assoc, e4, _root_.mul_comm c b, h.s01 c b, mul_left_comm c b d]

private theorem v_sub_one_add_le_v_pow_l_sub_one {U : Type} [CommGroup U] {P B C D Px Px' D' E F : U} {k : ℕ}
    (ih : P * C ^ k = D * Px * Px') (e : D * B * C = D' * E * F) :
    P * B * C ^ (k + 1) = D' * (Px * E) * (Px' * F) := by
  calc P * B * C ^ (k + 1) = (P * C ^ k) * (B * C) := by rw [pow_succ]; ac_rfl
    _ = Px * Px' * (D * B * C) := by rw [ih]; ac_rfl
    _ = D' * (Px * E) * (Px' * F) := by rw [e]; ac_rfl

theorem cubN_mul_left {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ) (k : ℕ)
    (x x' y : A) :
    cubN θ k 1 (x * x') y * θ x x' y ^ k = θ (x ^ k) (x' ^ k) y * cubN θ k 1 x y * cubN θ k 1 x' y := by
  induction k with
  | zero => simp [cubN, h.face]
  | succ k ih =>
    simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
    rw [pow_succ x, pow_succ x', mul_pow x x' k]
    exact v_sub_one_add_le_v_pow_l_sub_one ih (isCub_mul_swap_middle h (x ^ k) (x' ^ k) x x' y)

private theorem gm_id_global_mul {X : Scheme.{0}} (z : X) (a b : Γ(X, ⊤)ˣ) :
    gm (𝟙 X) z ⊤ (a * b) = gm (𝟙 X) z ⊤ a * gm (𝟙 X) z ⊤ b :=
  map_mul _ a b

section
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} {c : CubicalStr G L} {N : ℕ}
  {T : Over S} {x x' y : T ⟶ G}

theorem CubWeil.mul_left {ζ ζ' : Γ(T.left, ⊤)ˣ} (h : CubWeil c N x y ζ) (h' : CubWeil c N x' y ζ') :
    CubWeil c N (x * x') y (ζ * ζ') := by
  obtain ⟨hx, hy, hv⟩ := h
  obtain ⟨hx', -, hv'⟩ := h'
  refine ⟨by rw [mul_pow, hx, hx', _root_.one_mul], hy, fun z J hJ => ?_⟩
  have hc := isCub_cubV c hJ
  have e1 := cubN_mul_left hc N x x' y
  rw [hx, hx', hc.face, _root_.one_mul, hc.s12 x x' y, hc.s01 x y x'] at e1
  have e2 := hc.N_add N 1 y x x'
  simp only [hc.face, _root_.one_mul, _root_.mul_one, hy] at e2
  apply mul_right_cancel (b := cubV c z J y x x' ^ N)
  rw [gm_id_global_mul, _root_.mul_assoc, e1, e2, ← hv z J hJ, ← hv' z J hJ]
  exact mul_mul_mul_comm _ _ _ _

theorem cubWeil_one_left (c : CubicalStr G L) (hy : y ^ N = 1) : CubWeil c N 1 y 1 := by
  obtain ⟨ζ, hζ, -⟩ := existsUnique_cubWeil (x := (1 : T ⟶ G)) c (one_pow N) hy
  have h2 := hζ.mul_left hζ
  rw [_root_.one_mul] at h2
  have e : ζ * ζ = ζ * 1 := by rw [_root_.mul_one]; exact h2.unique hζ
  rw [mul_left_cancel e] at hζ
  exact hζ

theorem CubWeil.pow_left {ζ : Γ(T.left, ⊤)ˣ} (h : CubWeil c N x y ζ) (n : ℕ) : CubWeil c N (x ^ n) y (ζ ^ n) := by
  induction n with
  | zero => simpa using cubWeil_one_left c h.2.1
  | succ n ih => simpa [pow_succ] using ih.mul_left h

theorem CubWeil.pow_eq_one {ζ : Γ(T.left, ⊤)ˣ} (h : CubWeil c N x y ζ) : ζ ^ N = 1 := by
  have hp := h.pow_left N
  rw [h.1] at hp
  exact hp.unique (cubWeil_one_left c h.2.1)

end

theorem cubWeil_basic : (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (c : CubicalStr G L) (N : ℕ) (T : Over S), (∀ x y : T ⟶ G, x ^ N = 1 → y ^ N = 1 → ∃! ζ, CubWeil c N x y ζ) ∧ (∀ (x x' y : T ⟶ G) ζ ζ', CubWeil c N x y ζ → CubWeil c N x' y ζ' → CubWeil c N (x * x') y (ζ * ζ')) ∧ (∀ (x y : T ⟶ G) ζ, CubWeil c N x y ζ → CubWeil c N y x ζ⁻¹ ∧ ζ ^ N = 1) ∧ (∀ (T' : Over S) (ρ : T' ⟶ T) (x y : T ⟶ G) ζ, CubWeil c N x y ζ → CubWeil c N (ρ ≫ x) (ρ ≫ y) (Units.map ρ.left.appTop.hom.toMonoidHom ζ)) ∧ ∀ (H : Over S) [GrpObj H] (i : H ⟶ G), IsMonHom i → Nonempty (BiTriv c i) → ∀ (t : T ⟶ H) (y : T ⟶ G), t ^ N = 1 → y ^ N = 1 → CubWeil c N (t ≫ i) y 1) := by
  intro S G _ _ L c N T
  refine ⟨fun x y hx hy => existsUnique_cubWeil c hx hy, fun x x' y ζ ζ' h h' => h.mul_left h',
    fun x y ζ h => ⟨h.symm, h.pow_eq_one⟩, fun T' ρ x y ζ h => h.comp ρ, ?_⟩
  intro H _ i hi hne t y ht hy
  obtain ⟨σ⟩ := hne
  exact σ.cubWeil ht hy

end GlobalTheory.UU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMemCommonChart
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU
variable {S : Scheme.{0}}

theorem isWt_of_gm {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] {i : splitTorus S X ⟶ G} {V : G.left.Opens}
    (u : Γ(G.left, V)ˣ) (χ : X)
    (h : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left), g.left z ∈ V →
      gm ((t ≫ i) * g).left z V u = gm t.left z ⊤ (charUnit S X χ) * gm g.left z V u) :
    IsWt i V u.val χ := by
  intro Z t g h₁ h₂
  apply TopCat.Presheaf.section_ext Z.left.sheaf ⊤
  intro z hz
  have hg : g.left z ∈ V := h₂ trivial
  have hf : ((t ≫ i) * g).left z ∈ V := h₁ trivial
  have ht : t.left z ∈ (⊤ : (splitTorus S X).left.Opens) := trivial
  have key := congrArg Units.val (h Z t g z hg)
  simp only [gm, dif_pos hg, dif_pos hf, dif_pos ht, pullU, MonoidHom.comp_apply, Units.coe_map,
    Units.val_mul] at key
  change Z.left.presheaf.germ ⊤ z hz _ = Z.left.presheaf.germ ⊤ z hz _
  simp only [Scheme.Hom.appLE, CommRingCat.comp_apply, map_mul, TopCat.Presheaf.germ_res_apply]
  exact key

attribute [local instance] SplitExt.free SplitExt.finite

variable {E : SplitExt S} {G : Over S} [GrpObj G]

theorem exists_mem_commonChart (E : SplitExt S) (x : E.B.left) : ∃ j, x ∈ E.chart j := by
  have hk : ∀ k, ∃ a, x ∈ (E.O (E.basis k)).L.U a := by
    intro k
    have hx : x ∈ (⊤ : E.B.left.Opens) := trivial
    rw [← (E.O (E.basis k)).isLB.cover] at hx
    simpa [TopologicalSpace.Opens.mem_iSup] using hx
  choose c hc using hk
  refine ⟨c, ?_⟩
  unfold SplitExt.chart
  rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf]
  exact Set.mem_iInter.2 hc

private theorem gm_res_pullU_eq_gm_comp {Z P Y : Scheme.{0}} (p : Z ⟶ P) (a : P ⟶ Y) {U : Y.Opens} {W : P.Opens}
    (h : W ≤ a ⁻¹ᵁ U) {z : Z} (hz : p z ∈ W) (w : Γ(Y, U)ˣ) :
    gm p z W (res h (pullU a U w)) = gm (p ≫ a) z U w := by
  have hz' : (p ≫ a) z ∈ U := h hz
  ext
  simp only [gm, dif_pos hz, dif_pos hz', pullU, res, MonoidHom.comp_apply, Units.coe_map]
  erw [← Scheme.Hom.germ_stalkMap_apply p W z hz, TopCat.Presheaf.germ_res_apply,
    Scheme.Hom.germ_stalkMap_apply]
  rfl

private theorem gm_id_pullU_eq_gm {Z P Y : Scheme.{0}} (p : Z ⟶ P) (a : P ⟶ Y) {U : Y.Opens} {z : Z}
    (hz : p z ∈ a ⁻¹ᵁ U) (w : Γ(Y, U)ˣ) :
    gm p z (a ⁻¹ᵁ U) (pullU a U w) = gm (p ≫ a) z U w := by
  have hz' : (p ≫ a) z ∈ U := hz
  ext
  simp only [gm, dif_pos hz, dif_pos hz', pullU, MonoidHom.comp_apply, Units.coe_map]
  rfl

theorem isWt_coordinate (d : E.GtDatum G) (j : E.ChartIdx) (k : Module.Free.ChooseBasisIndex ℤ E.X) :
    IsWt d.i _ (d.u j k).val (E.basis k) := by
  refine isWt_of_gm (d.u j k) (E.basis k) ?_
  intro Z t g z hz
  have hf : (t ≫ d.i) * g = lift t g ≫ (lift (fst (splitTorus S E.X) G ≫ d.i) (snd (splitTorus S E.X) G) ≫ μ) := by
    show lift (t ≫ d.i) g ≫ μ = _
    rw [← Category.assoc, comp_lift, lift_fst_assoc, lift_snd]
  have hp : (lift t g).left z ∈ (snd (splitTorus S E.X) G).left ⁻¹ᵁ (d.q.left ⁻¹ᵁ E.chart j) := by
    have e : ((lift t g).left ≫ (snd (splitTorus S E.X) G).left) = g.left := by
      rw [← Over.comp_left, lift_snd]
    show ((lift t g).left ≫ (snd (splitTorus S E.X) G).left) z ∈ d.q.left ⁻¹ᵁ E.chart j
    rw [e]
    exact hz
  have key := congrArg (gm (lift t g).left z _) (d.equiv j k)
  rw [map_mul] at key
  rw [gm_res_pullU_eq_gm_comp (a := (lift (fst (splitTorus S E.X) G ≫ d.i) (snd (splitTorus S E.X) G) ≫ μ).left) _ _ hp,
    gm_id_pullU_eq_gm (a := (snd (splitTorus S E.X) G).left) _ hp] at key
  rw [← Over.comp_left, ← Over.comp_left, lift_snd, ← hf] at key
  rw [key]
  congr 1
  erw [gm_res_pullU_eq_gm_comp (a := (fst (splitTorus S E.X) G).left) _ _ hp]
  rw [← Over.comp_left, lift_fst]

theorem exists_unit_isWt (d : E.GtDatum G) (j : E.ChartIdx) (χ : E.X) :
    ∃ u : Γ(G.left, d.q.left ⁻¹ᵁ E.chart j)ˣ, IsWt d.i _ u.val χ := by
  have hχ : χ ∈ AddSubgroup.closure (Set.range E.basis) := by
    rw [← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup, E.basis.span_eq]
    exact Submodule.mem_top
  induction hχ using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    exact ⟨d.u j k, isWt_coordinate d j k⟩
  | zero => exact ⟨1, by simpa using (isWt_one : IsWt d.i (d.q.left ⁻¹ᵁ E.chart j) 1 0)⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a * b, by simpa using ha.mul hb⟩
  | neg x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨a⁻¹, ha.inv⟩

def TQ.ofGtDatum (d : E.GtDatum G) : TQ G E.X where
  B := E.B
  comm := E.isAbelian.comm
  isAb := E.isAbelian
  q := d.q
  i := d.i
  q_hom := d.q_hom
  i_hom := d.i_hom
  q_flat := d.q_flat
  q_surj := d.q_surjective
  q_affine := d.q_affine
  isKernel := d.isKernel
  loc b χ := by
    obtain ⟨j, hj⟩ := exists_mem_commonChart E b
    exact ⟨E.chart j, hj, exists_unit_isWt d j χ⟩

theorem exists_tq_of_gtDatum :
    ∀ (S : Scheme.{0}) (E : SplitExt S) (G : Over S) [GrpObj G] (Dat : E.GtDatum G), ∃ Q : TQ G E.X, Q.i = Dat.i := by
  intro S E G _ Dat
  exact ⟨TQ.ofGtDatum Dat, rfl⟩

end GlobalTheory.UU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkBaseChange
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaBaseChange

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange

theorem exists_fraction_map {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R')
    (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F]
    (hF : ∀ r : R, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) =
      algebraMap (FractionRing R') F (algebraMap R' (FractionRing R') (φ r))) :
    ∃ g : Spec (CommRingCat.of (FractionRing R')) ⟶ Spec (CommRingCat.of (FractionRing R)),
      g ≫ jK R = jK R' ≫ specOf φ ∧ jFK (R := R') F ≫ g = jFK (R := R) F := by
  have inj : Function.Injective ((algebraMap R' (FractionRing R')).comp φ) :=
    (injective_iff_map_eq_zero _).2 fun r hr => by
      have e := hF r
      rw [show algebraMap R' (FractionRing R') (φ r) = 0 from hr, map_zero] at e
      exact (IsFractionRing.injective R (FractionRing R))
        (((algebraMap (FractionRing R) F).injective (e.trans (map_zero _).symm)).trans (map_zero _).symm)
  obtain ⟨ψ, h₁⟩ : ∃ ψ : FractionRing R →+* FractionRing R',
      ψ.comp (algebraMap R (FractionRing R)) = (algebraMap R' (FractionRing R')).comp φ :=
    ⟨IsFractionRing.lift (K := FractionRing R) inj, RingHom.ext fun r => by
      rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap]⟩
  have h₂ : (algebraMap (FractionRing R') F).comp ψ = algebraMap (FractionRing R) F :=
    IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r =>
      (congrArg (algebraMap (FractionRing R') F) (RingHom.congr_fun h₁ r)).trans (hF r).symm)
  refine ⟨Spec.map (CommRingCat.ofHom ψ), ?_, ?_⟩
  · exact (Spec.map_comp _ _).symm.trans ((congrArg (fun q => Spec.map (CommRingCat.ofHom q)) h₁).trans
      (Spec.map_comp (CommRingCat.ofHom φ) (CommRingCat.ofHom (algebraMap R' (FractionRing R')))))
  · exact (Spec.map_comp _ _).symm.trans (congrArg (fun q => Spec.map (CommRingCat.ofHom q)) h₂)

theorem grp_generic {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) :
    IsGrpPullback A.A G (jK R) (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) := by
  have := U.gen_hom
  have : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  exact ((isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback G (jK R))).congr (Category.id_comp _) rfl

end GlobalTheory.ThetaBaseChange

namespace GlobalTheory


open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange GlobalTheory.ThetaBaseChange in
set_option maxHeartbeats 1600000 in
theorem qkToAk_baseChange : GlobalFnsSt → SecBaseChangeSt → QkBaseChangeSt := by
  intro hG _ R R' _ _ _ _ I I' _ _ φ D A G _ _ U G' _ _ bc hbc A' D' hD U' hU F _ _ _ hF k hk p x p' x' hy hg hx H w' hw'
  obtain ⟨wL, hwL, -, -, hlev⟩ := (isPullUnif_iff_stalks R R' I I' φ D D' hD A A' G G' bc U U').1 hU
  obtain ⟨w, hw⟩ := U.ext
  obtain ⟨hx1, H⟩ := H w hw
  obtain ⟨g, hg₁, hg₂⟩ := exists_fraction_map φ F hF
  have gA := grp_generic U.toUnifPre
  have gΨ : IsGrpPullback G' G (specOf φ) (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) :=
    ((isGrpPullback_of_iso bc).comp (isGrpPullback_pullback G (specOf φ))).congr (Category.id_comp _) rfl
  have hΘF : (jFK (R := R') F ≫ jK R') ≫ specOf φ = jFK (R := R) F ≫ jK R := by
    rw [Category.assoc, ← hg₁, ← Category.assoc, hg₂]
  obtain ⟨Θ, hΘ₁, hΘ₂⟩ := exists_cmp hΘF (pull_grp hD).1.w
  have gA' := (grp_generic U'.toUnifPre).comp gΨ
  obtain ⟨Φ, hΦ₁, hΦ₂⟩ : ∃ Φ : A'.A.left ⟶ A.A.left, Φ ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) =
      (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R')) ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) ∧
      Φ ≫ A.A.hom = A'.A.hom ≫ g :=
    ⟨gA.1.lift _ (A'.A.hom ≫ g) (by rw [gA'.1.w, Category.assoc, hg₁]), gA.1.lift_fst _ _ _, gA.1.lift_snd _ _ _⟩
  have gΦ : IsGrpPullback A'.A A.A g Φ := gA.cancel (gA'.congr hg₁.symm hΦ₁.symm) hΦ₂
  have hxΦ : x'.left ≫ Φ = x.left := gA.1.hom_ext (by
    rw [Category.assoc, hΦ₁, ← hx]; simp only [Category.assoc]) (by
    rw [Category.assoc, hΦ₂, ← Category.assoc, Over.w x', Over.w x]; exact hg₂)
  refine ⟨pow_eq_one_of_push hg₂ gΦ hxΦ hx1, fun θ' hθ' => ?_⟩
  have n₁ : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.inv_hom_id, Over.id_left]
  have n₂ : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, U'.gen.inv_hom_id, Over.id_left]
  have n₃ : U'.gen.hom.left ≫ U'.gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, U'.gen.hom_inv_id, Over.id_left]
  have hΦ₃ : (U'.gen.hom.left ≫ Φ) ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) =
      pullback.fst G'.hom (jK R') ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) := by
    rw [Category.assoc, hΦ₁, ← Category.assoc, ← Category.assoc U'.gen.hom.left, n₃]
    exact congrArg (· ≫ _) (Category.id_comp _)
  obtain ⟨v₂, hv₂, hsq⟩ := exists_side A.isLB A'.isLB U.LG.isLB U'.LG.isLB hw _ n₁ hw' hwL _ hΦ₃
  obtain ⟨v, hv, hvv⟩ := exists_unpull hv₂ _ n₂ (P := Φ) (by rw [← Category.assoc, n₂, Category.id_comp])
  obtain ⟨Ω, hΩ₁, hΩ₂⟩ := exists_cmp hg₂ hΦ₂
  obtain ⟨ω, hω₁, hω₂⟩ := exists_cmp_inv hg₂ gΦ.1
  have hΩω : Ω ≫ ω = 𝟙 _ := cmp_ext gΦ.1 (by rw [Category.assoc, hω₁, hΩ₁, Category.id_comp])
    (by rw [Category.assoc, hω₂, hΩ₂, Category.id_comp])
  let n : TFK (R := R) F ⊗ A.A ⟶ UnifPre.GF (G := G) F := lift (fst _ _) (snd _ _ ≫ U.gen.inv)
  have hn : n.left ≫ (U.toUnifPre.genF F).left = 𝟙 _ := congrArg (fun q => q.left) (show n ≫ U.toUnifPre.genF F = 𝟙 _ by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n])
  have hn₁ : n.left ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left = (fst (TFK (R := R) F) A.A).left :=
    congrArg (fun q => q.left) (lift_fst _ _ : n ≫ fst _ _ = _)
  have hn₂ : n.left ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left =
      (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left :=
    congrArg (fun q => q.left) (lift_snd _ _ : n ≫ snd _ _ = _)
  have hh₁ : (U'.toUnifPre.genF F).left ≫ (fst (TFK (R := R') F) A'.A).left =
      (fst (TFK (R := R') F) ((Over.pullback (jK R')).obj G')).left :=
    congrArg (fun q => q.left) (lift_fst _ _ : U'.toUnifPre.genF F ≫ fst _ _ = _)
  have hh₂ : (U'.toUnifPre.genF F).left ≫ (snd (TFK (R := R') F) A'.A).left =
      (snd (TFK (R := R') F) ((Over.pullback (jK R')).obj G')).left ≫ U'.gen.hom.left :=
    congrArg (fun q => q.left) (lift_snd _ _ : U'.toUnifPre.genF F ≫ snd _ _ = _)
  obtain ⟨Ξ, hΞ⟩ : ∃ Ξ : (UnifPre.GF (G := G') F).left ⟶ (UnifPre.GF (G := G) F).left,
      Ξ = (U'.toUnifPre.genF F).left ≫ Ω ≫ n.left := ⟨_, rfl⟩
  have x₁ : (Ξ ≫ (U.toUnifPre.genF F).left) ≫ ω = (U'.toUnifPre.genF F).left := by
    rw [hΞ, Category.assoc _ (Ω ≫ n.left), Category.assoc Ω, hn, Category.comp_id, Category.assoc, hΩω,
      Category.comp_id]
  have x₂ : Ξ ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left =
      (snd (TFK (R := R') F) ((Over.pullback (jK R')).obj G')).left ≫ (U'.gen.hom.left ≫ Φ) ≫ U.gen.inv.left := by
    rw [hΞ, Category.assoc, Category.assoc, hn₂, ← Category.assoc Ω]
    refine (congrArg (fun a => _ ≫ a ≫ _) hΩ₂).trans ?_
    rw [← Category.assoc, ← Category.assoc, hh₂]
    simp only [Category.assoc]
  have hΞ₁ : Ξ ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left =
      (fst (TFK (R := R') F) ((Over.pullback (jK R')).obj G')).left := by
    rw [hΞ, Category.assoc, Category.assoc, hn₁]
    exact (congrArg (_ ≫ ·) hΩ₁).trans hh₁
  have hΞ₂ : Ξ ≫ UnifPre.gFK (G := G) F = UnifPre.gFK (G := G') F ≫ (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) := by
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) x₂).trans ?_)
    refine Eq.trans ?_ ((congrArg (_ ≫ ·) hΦ₃).trans (Category.assoc _ _ _).symm)
    simp only [Category.assoc]
  obtain ⟨θ, hθ, hact⟩ := exists_theta_moved A.isLB A'.isLB hg₂ gΦ hv hω₁ hω₂ θ' (x := x) (by rw [hθ']; exact hxΦ)
  obtain ⟨ν, hν, Hν⟩ := H θ hθ
  obtain ⟨ν', hν', Hν'⟩ := GlobalTheory.phiRel_transport hG R R' φ D.toPre D'.toPre hD F hF Θ hΘ₁ hΘ₂ k p p' hy hg ν hν
  refine ⟨ν', hν', fun t' t₂' s' s₂' E E₂ hA => ?_⟩
  have bij := (expandsF_bijective U.toUnifPre F hG hk (U.expand k hk) hw).1
  have bij' := (expandsF_bijective U'.toUnifPre F hG hk (U'.expand k hk) hw').1
  choose pl hpl using exists_fam_field_pull hG R R' φ D.toPre D'.toPre hD F hF Θ hΘ₁ hΘ₂ k
  have key : ∀ a' b', U'.toUnifPre.ExpandsF F k w' a' b' → ∃ a b, Moved v ω a' a ∧
      U.toUnifPre.ExpandsF F k w a b ∧ pl b = b' := fun a' b' E => by
    obtain ⟨a, ha⟩ := exists_moved A.isLB A'.isLB hω₂ n₂ hv₂ hvv a'
    obtain ⟨b, σ, h₁, h₂⟩ := (bij a).exists
    refine ⟨a, b, ha, ⟨σ, h₁, h₂⟩, (bij' a').unique ?_ E⟩
    obtain ⟨σ', h₁', -⟩ := E
    exact ⟨σ', h₁', expandsG_transport R R' I I' φ D D' hD A A' G G' bc hbc U.toUnifPre U'.toUnifPre wL hwL hlev F hF
      Θ hΘ₁ hΘ₂ Ξ hΞ₁ hΞ₂ k σ σ' b (pl b)
      (moved_sec A.isLB A'.isLB n₃ n₁ hΦ₃ hsq hvv x₁ x₂ ha h₁ h₁') (hpl b) h₂⟩
  obtain ⟨t, s, m, e, rfl⟩ := key t' s' E
  obtain ⟨t₂, s₂, m₂, e₂, rfl⟩ := key t₂' s₂' E₂
  exact Hν' s s₂ _ _ (hpl s) (hpl s₂) (Hν t t₂ s s₂ e e₂ (hact t' t₂' t t₂ m m₂ hA))

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace CharAgree

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem comp_q_eq_one_iff (g : GtCoord I D e G)
    {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (a : Z ⟶ thickObj R I e G) :
    a ≫ g.q = toUnit _ ≫ η[thickObj R I e D.P.A] ↔
      a.left ≫ g.pG.left = a.left ≫ (fstG I e G).left ≫ G.hom ≫ eSec D.P.A := by
  have h1 : (a ≫ g.q).left ≫ pullback.fst D.P.A.hom (thick R I e) = a.left ≫ g.pG.left :=
    Category.assoc _ _ _
  have h2 : (toUnit Z ≫ η[thickObj R I e D.P.A]).left ≫ pullback.fst D.P.A.hom (thick R I e) =
      a.left ≫ (fstG I e G).left ≫ G.hom ≫ eSec D.P.A := by
    have k1 := UnitValue.eSec_pullback_fst (thick R I e) D.P.A
    have k2 : (toUnit Z).left = a.left ≫ pullback.snd G.hom (thick R I e) :=
      ((Category.comp_id _).symm.trans (Over.w (toUnit Z))).trans (Over.w a).symm
    have k3 : pullback.fst G.hom (thick R I e) ≫ G.hom =
        pullback.snd G.hom (thick R I e) ≫ thick R I e := pullback.condition
    refine (Category.assoc _ _ _).trans ((congrArg ((toUnit Z).left ≫ ·) k1).trans ?_)
    refine (congrArg (· ≫ thick R I e ≫ eSec D.P.A) k2).trans ((Category.assoc _ _ _).trans ?_)
    refine congrArg (a.left ≫ ·) ((Category.assoc _ _ _).symm.trans ?_)
    exact (congrArg (· ≫ eSec D.P.A) k3.symm).trans (Category.assoc _ _ _)
  refine ⟨fun h => h1.symm.trans ((congrArg (fun φ => φ.left ≫ _) h).trans h2), fun h => ?_⟩
  refine Over.OverMorphism.ext (pullback.hom_ext (h1.trans (h.trans h2.symm)) ?_)
  exact (Over.w _).trans (Over.w _).symm

def Match (g : GtCoord I D e G) (g' : GtCoord I D' e G) (xe : D'.X → D.X) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι)
    (J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι), Good D.P.L z J → Good D'.P.L z J' →
    r ≫ g.pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D.P.A →
    r ≫ g'.pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D'.P.A →
    ∀ x, val (g.t (xe x)) r z J = val (g'.t x) r z J'

omit [IsDomain R] in
theorem connected_thick [IsLocalRing R] (hI : I ≠ ⊤) (e : ℕ) :
    ConnectedSpace (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := by
  have hJ : I ^ (e + 1) ≠ ⊤ := fun h =>
    hI (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero e)))
  have : Nontrivial (R ⧸ I ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2 hJ
  have : IsLocalRing (R ⧸ I ^ (e + 1)) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have : PreconnectedSpace (PrimeSpectrum (R ⧸ I ^ (e + 1))) := by
    refine ⟨isPreconnected_of_forall (IsLocalRing.closedPoint _) fun y _ => ?_⟩
    exact ⟨closure {y}, Set.subset_univ _,
      (IsLocalRing.specializes_closedPoint y).mem_closure, subset_closure rfl,
      isPreconnected_singleton.closure⟩
  exact ({ toNonempty := inferInstance } : ConnectedSpace (PrimeSpectrum (R ⧸ I ^ (e + 1))))

variable [IsLocalRing R] [IsNoetherianRing R] (hI : I ≠ ⊤)
include hI

theorem exists_torus_iso (g : GtCoord I D e G) (g' : GtCoord I D' e G) :
    ∃ θ : splitTorus _ D'.X ≅ splitTorus _ D.X, IsMonHom θ.hom ∧ θ.hom ≫ g.i = g'.i := by
  have m : Mono g.i := ⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩
  have m' : Mono g'.i := ⟨fun a b h => g'.isKernel.hom_ext h (toUnit_unique _ _)⟩
  have := g.i_hom
  have := g'.i_hom
  let u := g.isKernel.lift g'.i (toUnit _) (gtCoord_i_comp_q hI g g')
  let v := g'.isKernel.lift g.i (toUnit _) (gtCoord_i_comp_q hI g' g)
  have hu : u ≫ g.i = g'.i := g.isKernel.lift_fst _ _ _
  have hv : v ≫ g'.i = g.i := g'.isKernel.lift_fst _ _ _
  refine ⟨⟨u, v, ?_, ?_⟩, ⟨?_, ?_⟩, hu⟩
  · rw [← cancel_mono g'.i, Category.assoc, hv, hu, Category.id_comp]
  · rw [← cancel_mono g.i, Category.assoc, hu, hv, Category.id_comp]
  · change η ≫ u = η
    rw [← cancel_mono g.i, Category.assoc, hu, IsMonHom.one_hom, IsMonHom.one_hom]
  · change μ ≫ u = (u ⊗ₘ u) ≫ μ
    rw [← cancel_mono g.i, Category.assoc, hu, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom,
      tensorHom_comp_tensorHom_assoc, hu]

theorem exists_match (g : GtCoord I D e G) (g' : GtCoord I D' e G) :
    ∃ xe : D'.X ≃+ D.X, Match g g' xe := by
  obtain ⟨θ, hθ, hi⟩ := exists_torus_iso hI g g'
  have := connected_thick hI e
  obtain ⟨xe, hx⟩ := exists_addEquiv_of_splitTorus_iso _ D.X D'.X θ hθ
  refine ⟨xe, fun Z r z J J' hJ hJ' _ h' x => ?_⟩
  let FinalForm : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) :=
    Over.mk (r ≫ (thickObj R I e G).hom)
  let a : FinalForm ⟶ thickObj R I e G := Over.homMk r rfl
  let τ := g'.isKernel.lift a (toUnit _) ((comp_q_eq_one_iff g' a).2 h')
  have hτ : τ ≫ g'.i = a := g'.isKernel.lift_fst _ _ _
  have hτ' : (τ ≫ θ.hom) ≫ g.i = a := by rw [Category.assoc, hi, hτ]
  have k := (TorusCoord.val_torus_point_and_translate R I D e G g FinalForm (τ ≫ θ.hom) 1 z J hJ (xe x)).1
  have k' := (TorusCoord.val_torus_point_and_translate R I D' e G g' FinalForm τ 1 z J' hJ' x).1
  rw [hτ'] at k
  rw [hτ] at k'
  refine k.trans (Eq.trans (Units.ext ?_) k'.symm)
  rw [gm_val _ _ ⊤ trivial, gm_val _ _ ⊤ trivial]
  refine congrArg (FinalForm.left.presheaf.germ ⊤ z trivial).hom ?_
  exact (SplitTorusHom.appTop_comp τ θ.hom _).trans (congrArg τ.left.appTop.hom (hx x))

theorem match_unique (g : GtCoord I D e G) (g' : GtCoord I D' e G) {f f' : D'.X → D.X}
    (h : Match g g' f) (h' : Match g g' f') : f = f' := by
  funext x
  have := connected_thick hI e
  refine SplitTorusHom.charUnit_injective (S := Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))
    (congrArg Units.val (unit_ext fun z _ => ?_))
  choose J hJ using fun ψ : (splitTorus _ D.X).left ⟶ D.P.A.left => exists_chart D.P.isLB (ψ z)
  choose J' hJ' using fun ψ : (splitTorus _ D.X).left ⟶ D'.P.A.left => exists_chart D'.P.isLB (ψ z)
  have c := (comp_q_eq_one_iff g g.i).1 g.isKernel.w
  have c' := (comp_q_eq_one_iff g' g.i).1 (gtCoord_i_comp_q hI g' g)
  have k := fun χ =>
    (TorusCoord.val_torus_point_and_translate R I D e G g _ (𝟙 _) 1 z J hJ χ).1
  simp only [Category.id_comp] at k
  exact (k _).symm.trans (((h _ _ z J J' hJ hJ' c c' x).trans
    (h' _ _ z J J' hJ hJ' c c' x).symm).trans (k _))


omit hI [IsLocalRing R] [IsNoetherianRing R] in
theorem match_down {D D' : DegData R I} {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    (U : UnifPre I D A G) (U' : UnifPre I D' A' G) {f : D'.toPre.X → D.toPre.X}
    (h : Match (U.gt (e + 1)) (U'.gt (e + 1)) f) : Match (U.gt e) (U'.gt e) f := by
  intro Z r z J J' hJ hJ' c c' x
  have t : thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have up : ∀ {Y : Scheme.{0}} (p : (thickObj R I (e + 1) G).left ⟶ Y)
      (p₀ : (thickObj R I e G).left ⟶ Y) (s : G.left ⟶ Y), thickMap R I e G ≫ p = p₀ →
      r ≫ p₀ = r ≫ (fstG I e G).left ≫ s →
      (r ≫ thickMap R I e G) ≫ p = (r ≫ thickMap R I e G) ≫ (fstG I (e + 1) G).left ≫ s := by
    intro Y p p₀ s h₁ h₂
    refine (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) h₁).trans (h₂.trans ?_))
    refine Eq.trans (congrArg (r ≫ ·) ?_) (Category.assoc _ _ _).symm
    exact (congrArg (· ≫ s) t.symm).trans (Category.assoc _ _ _)
  have k := h Z (r ≫ thickMap R I e G) z J J' hJ hJ' (up _ _ _ (U.gt_q e) c)
    (up _ _ _ (U'.gt_q e) c') x
  exact (val_corr hJ (U.gt_t e (f x)) r).symm.trans ((val_pull hJ _ _ _).trans (k.trans
    ((val_pull hJ' _ _ _).symm.trans (val_corr hJ' (U'.gt_t e x) r))))

end CharAgree


open CharAgree in
theorem unifPre_characterGroup_iso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G), ∃ xe : D'.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U'.gt e).pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D'.toPre.P.A → ∀ x, Geo.Tor.val ((U.gt e).t (xe x)) r z J = Geo.Tor.val ((U'.gt e).t x) r z J') := by
  intro R _ _ _ I hR D D' A A' G _ _ _ U U'
  obtain ⟨hN, -, -, hC⟩ := hR
  have hI : I ≠ ⊤ := by
    rintro rfl
    have : Subsingleton R := IsHausdorff.subsingleton hC.toIsHausdorff
    exact false_of_nontrivial_of_subsingleton R
  choose xe hxe using fun e => exists_match hI (U.gt e) (U'.gt e)
  have down : ∀ (e : ℕ) (f : D'.toPre.X → D.toPre.X), Match (U.gt e) (U'.gt e) f →
      Match (U.gt 0) (U'.gt 0) f := by
    intro e f
    induction e with
    | zero => exact id
    | succ e ih => exact fun h => ih (match_down U U' h)
  refine ⟨xe 0, fun e => ?_⟩
  have h := hxe e
  rw [match_unique hI _ _ (down e _ h) (hxe 0)] at h
  exact h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcWitMemRangeJKOfMemRangeJ
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory
namespace ArcNotAbelian

theorem isProper_fibre {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G) (K : Type) [Field K]
    (t : Spec (CommRingCat.of K) ⟶ S) (p : Spec (CommRingCat.of K)) (hp : t p ∈ abLocus G) :
    IsProper (pullback.snd G.hom t) := by
  let K' := AlgebraicClosure K
  let u : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of K) := Spec.map (CommRingCat.ofHom (algebraMap K K'))
  have : Subsingleton (Spec (CommRingCat.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have q : Spec (CommRingCat.of K') := (default : PrimeSpectrum K')
  have : Nonempty (Spec (CommRingCat.of K')) := ⟨q⟩
  have h₁ : IsProper (pullback.snd G.hom (u ≫ t)) :=
    hp K' (u ≫ t) ⟨q, congrArg (fun z => t z) (Subsingleton.elim (u q) p)⟩
  have P := (IsPullback.of_hasPullback (pullback.snd G.hom t) u).paste_horiz (IsPullback.of_hasPullback G.hom t)
  have h₂ : UniversallyClosed (pullback.snd (pullback.snd G.hom t) u) := by
    rw [← P.isoPullback_hom_snd]; infer_instance
  have hu : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) u :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have : UniversallyClosed (pullback.snd G.hom t) :=
    MorphismProperty.of_pullback_snd_of_descendsAlong (P := @UniversallyClosed) hu h₂
  have := hG.separated
  have := hG.smooth
  exact ⟨⟩


open TorusToProper in
theorem subsingleton_of_mono (K : Type) [Field K] (X : Type) [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over (Spec (CommRingCat.of K))) [GrpObj B]
    [IsProper B.hom] (f : splitTorus (Spec (CommRingCat.of K)) X ⟶ B) (hf : IsMonHom f) [Mono f] :
    Subsingleton X := by
  have h := splitTorus_hom_proper_trivial_field K X B f hf
  have e : ptFun K X (AddMonoidAlgebra K X) (univ K X) = ptFun K X (AddMonoidAlgebra K X) 1 := by
    rw [← cancel_mono f, h, ← Category.assoc, ← Category.assoc]
    congr 1
    exact toUnit_unique _ _
  have e₂ := (ptFun_fst K X _ (univ K X)).symm.trans
    ((congrArg (fun z => z.left ≫ Rosenlicht.torusFst _ X) e).trans (ptFun_fst K X _ 1))
  have e₃ : charRing X _ (univ K X) = charRing X (AddMonoidAlgebra K X) 1 :=
    congrArg CommRingCat.Hom.hom (Spec.map_injective e₂)
  have key : ∀ a : X, (AddMonoidAlgebra.single a 1 : AddMonoidAlgebra K X) = 1 := by
    intro a
    have := congrArg (fun φ => φ (AddMonoidAlgebra.single a 1)) e₃
    simp only [charRing_single] at this
    simpa [univ] using this
  exact ⟨fun a b => AddMonoidAlgebra.single_left_injective (one_ne_zero (α := K)) ((key a).trans (key b).symm)⟩

theorem subsingleton_of_mem_abLocus {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G)
    (A : Type) [CommRing A] (hA : IsField A) (t : Spec (CommRingCat.of A) ⟶ S) (p : Spec (CommRingCat.of A))
    (hp : t p ∈ abLocus G) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (f : splitTorus (Spec (CommRingCat.of A)) X ⟶ (Over.pullback t).obj G) (hf : IsMonHom f) [Mono f] :
    Subsingleton X := by
  letI := hA.toField
  have : IsProper ((Over.pullback t).obj G).hom := isProper_fibre G hG A t p hp
  exact subsingleton_of_mono A X _ f hf

end ArcNotAbelian


open ArcNotAbelian in
theorem arcWit_mem_range_jK_of_mem_range_j : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (χ : Sp (PowerSeries k) ⟶ Y.X) (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ) (x : Sp (PowerSeries k)), χ x ∈ Set.range Y.j → x ∈ Set.range (jK (PowerSeries k)) := by
  intro E _ _ _ H D l Xo c k _ bF a O _ β Y χ W x hx
  refine mem_range_jK x fun hX => ?_
  have h₁ : χ x ∈ abLocus Y.t.G := by
    obtain ⟨p, hp⟩ := hx
    have hz : Y.jQ p ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by
      rw [Y.ab_gen]; exact ⟨_, rfl⟩
    rw [← hp]
    exact hz
  have h₂ : x ∈ abLocus W.t.G := (abLocus_pullback abLocusOne Y.t.semi W.m.cart.1 x).1 h₁
  have hmax : (Ideal.span {(PowerSeries.X : PowerSeries k)} ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one, ← PowerSeries.maximalIdeal_eq_span_X]; infer_instance
  have hF : IsField (PowerSeries k ⧸ Ideal.span {(PowerSeries.X : PowerSeries k)} ^ (0 + 1)) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax
  have hle : Ideal.span {(PowerSeries.X : PowerSeries k)} ^ (0 + 1) ≤ x.asIdeal := by
    rw [zero_add, pow_one, Ideal.span_le, Set.singleton_subset_iff]; exact hX
  obtain ⟨p, hp⟩ : x ∈ Set.range (PrimeSpectrum.comap
      (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries k)} ^ (0 + 1)))) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    exact hle
  let g := W.P.U.gt 0
  have m : Mono g.i := ⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩
  have hp' : thick (PowerSeries k) (Ideal.span {PowerSeries.X}) 0 p ∈ abLocus W.t.G := by
    rw [← hp] at h₂; exact h₂
  have hs := subsingleton_of_mem_abLocus W.t.G W.t.semi _ hF _ p hp' W.P.D.toPre.X g.i g.i_hom
  have hn : Nontrivial (a.restrict β).D₀.X := (a.restrict β).nontriv
  exact not_subsingleton _ (W.e.toEquiv.subsingleton)

end GlobalTheory
end
