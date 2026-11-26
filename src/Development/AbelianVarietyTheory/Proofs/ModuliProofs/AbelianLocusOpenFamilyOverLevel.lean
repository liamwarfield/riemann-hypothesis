module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsToricTorsionCubWeilOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullObjectOfGenericFibreDvr
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsStableBasOfPullback

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteOfAmpleDeterminantFramesPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteOfAmpleDeterminantFramesPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FrameFinite

open GlobalTheory.SecAff GlobalTheory.LN GlobalTheory.ThetaAct GlobalTheory.GeomPointSections GlobalTheory.FrameBasis

theorem top_le {X : Scheme.{0}} {W V : X.Opens} (h : W ≤ V) : (⊤ : W.toScheme.Opens) ≤ W.ι ⁻¹ᵁ V := fun t _ => h t.2

theorem pa_ι_bijective {X : Scheme.{0}} (V : X.Opens) : Function.Bijective (pa V.ι (top_le le_rfl)) :=
  pa_bijective V.ι _ le_top (by rw [Scheme.Opens.opensRange_ι])

theorem gm_eq_of_pa {X Z : Scheme.{0}} (q : X ⟶ Z) {W V V' : X.Opens} {U : Z.Opens} (l₁ : W ≤ V) (l₂ : W ≤ V')
    (l₃ : W ≤ q ⁻¹ᵁ U) (u : Γ(X, V)ˣ) (u' : Γ(X, V')ˣ) (g : Γ(Z, U)ˣ) (l₄ : ⊤ ≤ (W.ι ≫ q) ⁻¹ᵁ U)
    (h : pa W.ι (top_le l₁) u.val = pa (W.ι ≫ q) l₄ g.val * pa W.ι (top_le l₂) u'.val) (x : X) (hx : x ∈ W) :
    gm (𝟙 X) x V u = gm (𝟙 X ≫ q) x U g * gm (𝟙 X) x V' u' := by
  have e : rs l₁ u.val = pa q l₃ g.val * rs l₂ u'.val := (pa_ι_bijective W).1 (by
    rw [map_mul, pa_rs, pa_rs, pa_pa q W.ι l₃ _ _ rfl l₄]
    exact h)
  apply Units.ext
  rw [Units.val_mul, ← gs_unit (𝟙 X) x _ (l₁ hx), ← gs_unit (𝟙 X) x _ (l₂ hx), ← gs_unit (𝟙 X ≫ q) x _ (l₃ hx),
    ← gs_res (𝟙 X) x l₁ hx, ← gs_res (𝟙 X) x l₂ hx, ← Geo.Tor.gs_appLE q _ W l₃ (𝟙 X) x hx,
    ← gs_mul (𝟙 X) x W hx]
  exact congrArg (gs (𝟙 X) x W) e

theorem exists_gen_of_affine {X Z : Scheme.{0}} {A : LB Z} (hA : A.IsLB) (q : X ⟶ Z)
    (R : ∀ (T : Scheme.{0}) (_ : T ⟶ X) (_ : A.ι), Γ(T, ⊤) → Prop)
    (ex : ∀ (T : Scheme.{0}) [IsAffine T] (r : T ⟶ X) (i : A.ι), (∀ t, q (r t) ∈ A.U i) → ∃ d, IsUnit d ∧ R T r i d)
    (re : ∀ (T T' : Scheme.{0}) (s : T' ⟶ T) (r : T ⟶ X) i d, R T r i d → R T' (s ≫ r) i (pa s (le_pre_top _) d))
    (cmp : ∀ (T : Scheme.{0}) [IsAffine T] (r : T ⟶ X) i j d d' (h : ⊤ ≤ (r ≫ q) ⁻¹ᵁ (A.U i ⊓ A.U j)),
      R T r i d → R T r j d' → d = pa (r ≫ q) h (A.g i j).val * d') :
    ∃ t : (A.pull q).Gen, t.IsGen := by
  have ex' : ∀ (i : A.ι) (V : {V : X.Opens // IsAffineOpen V ∧ V ≤ (A.pull q).U fun _ => i}),
      ∃ u : Γ(X, V.1)ˣ, R V.1 V.1.ι i (pa V.1.ι (top_le le_rfl) u.val) := fun i V => by
    have : IsAffine V.1 := V.2.1
    obtain ⟨d, hd, hR⟩ := ex V.1 V.1.ι i fun t => mem_pull.1 (V.2.2 t.2)
    obtain ⟨u, rfl⟩ := (pa_ι_bijective V.1).2 d
    obtain ⟨u, rfl⟩ := (MulEquiv.isUnit_map (f := RingEquiv.ofBijective _ (pa_ι_bijective V.1))).1 hd
    exact ⟨u, hR⟩
  choose u hu using ex'
  have key : ∀ i V j V' x, x ∈ V.1 → x ∈ V'.1 →
      gm (𝟙 X) x _ (u i V) = gm (𝟙 X ≫ q) x _ (A.g i j) * gm (𝟙 X) x _ (u j V') := by
    intro i V j V' x hx hx'
    obtain ⟨W, hW, hxW, hle⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := V.1 ⊓ V'.1) ⟨hx, hx'⟩
    have : IsAffine W := hW
    have l₁ : W ≤ V.1 := fun y hy => (hle hy).1
    have l₂ : W ≤ V'.1 := fun y hy => (hle hy).2
    have l₃ : W ≤ q ⁻¹ᵁ (A.U i ⊓ A.U j) := fun y hy => ⟨mem_pull.1 (V.2.2 (l₁ hy)), mem_pull.1 (V'.2.2 (l₂ hy))⟩
    have r₁ := re _ _ (X.homOfLE l₁) _ _ _ (hu i V)
    have r₂ := re _ _ (X.homOfLE l₂) _ _ _ (hu j V')
    rw [pa_pa _ _ _ _ _ (X.homOfLE_ι l₁) (top_le l₁), X.homOfLE_ι] at r₁
    rw [pa_pa _ _ _ _ _ (X.homOfLE_ι l₂) (top_le l₂), X.homOfLE_ι] at r₂
    exact gm_eq_of_pa q l₁ l₂ l₃ _ _ _ (top_le l₃) (cmp _ _ _ _ _ _ _ r₁ r₂) x hxW
  have cov : ∀ i x, x ∈ (A.pull q).U (fun _ => i) →
      ∃ V : {V : X.Opens // IsAffineOpen V ∧ V ≤ (A.pull q).U fun _ => i}, x ∈ V.1 := fun i x hx => by
    obtain ⟨W, hW, hxW, hle⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := x) hx
    exact ⟨⟨W, hW, hle⟩, hxW⟩
  have gl : ∀ i, ∃ s : Γ(X, (A.pull q).U fun _ => i)ˣ, ∀ V, res V.2.2 s = u i V := fun i =>
    glue_unit _ (fun V : {V : X.Opens // IsAffineOpen V ∧ V ≤ (A.pull q).U fun _ => i} => V.1) (fun V => V.2.2)
      (fun x hx => TopologicalSpace.Opens.mem_iSup.2 (cov i x hx)) (u i) (fun V V' x hx => by
        rw [key i V i V' x hx.1 hx.2, gm_self hA (𝟙 X ≫ q) x (mem_pull.1 (V.2.2 hx.1)), _root_.one_mul])
  choose s hs using gl
  refine ⟨⟨fun J => s (J PUnit.unit)⟩, fun J J' => unit_ext fun x hx => ?_⟩
  obtain ⟨V, hV⟩ := cov (J PUnit.unit) x hx.1
  obtain ⟨V', hV'⟩ := cov (J' PUnit.unit) x hx.2
  have := key _ V _ V' x hV hV'
  rw [← hs, ← hs, gm_res (𝟙 X) x _ hV, gm_res (𝟙 X) x _ hV', ← gm_pull_g A q (𝟙 X) x J J' hx.1 hx.2] at this
  exact (gm_res (𝟙 X) x _ hx _).trans (this.trans
    ((map_mul _ _ _).trans (congrArg _ (gm_res (𝟙 X) x _ hx _))).symm)

section Det

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {a : ℤ} {T T' T₀ T₁ T₂ : Over S} {n : ℕ}

def Det (e : Fin n → SecM A L a T₁) (e₀ : Fin n → SecM A L a T₀) (χ : T ⟶ T₁) (ρ : T ⟶ T₀) (d : Γ(T.left, ⊤)) : Prop :=
  ∃ P : Matrix (Fin n) (Fin n) Γ(T.left, ⊤),
    (∀ k, pull A L a χ (e k) = ∑ l, P k l • pull A L a ρ (e₀ l)) ∧ P.det = d

variable {e : Fin n → SecM A L a T₁} {e₀ : Fin n → SecM A L a T₀} {e' : Fin n → SecM A L a T₂}

theorem exists_det [IsAffine T.left] (he : StableBas e) (he₀ : StableBas e₀) (χ : T ⟶ T₁) (ρ : T ⟶ T₀) :
    ∃ d : Γ(T.left, ⊤)ˣ, Det e e₀ χ ρ d.val := by
  choose P hP using fun k => (((isBas_iff_existsUnique _).1 (he₀ _ ρ)) (pull A L a χ (e k))).exists
  obtain ⟨d, hd⟩ := ((he₀ _ ρ).iff_det (Matrix.of P) hP).1 (he _ χ)
  exact ⟨d, Matrix.of P, hP, hd.symm⟩

theorem Det.comp {χ : T ⟶ T₁} {ρ : T ⟶ T₀} {d} (h : Det e e₀ χ ρ d) (s : T' ⟶ T) {χ' : T' ⟶ T₁} {ρ' : T' ⟶ T₀}
    (h₁ : s ≫ χ = χ') (h₂ : s ≫ ρ = ρ') : Det e e₀ χ' ρ' (pa s.left (le_pre_top _) d) := by
  obtain ⟨P, hP, rfl⟩ := h
  subst h₁ h₂
  refine ⟨(pa s.left (V := ⊤) (le_pre_top _)).mapMatrix P, fun k => ?_, (RingHom.map_det _ _).symm⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← pull_pull, hP, map_sum]
  simp only [map_smulₛₗ, pull_pull]
  rfl

theorem Det.mul [IsAffine T.left] (he₀ : StableBas e₀) {χ : T ⟶ T₁} {ρ : T ⟶ T₀} {χ' : T ⟶ T₂} {d d' m}
    (h : Det e e₀ χ ρ d) (h' : Det e' e₀ χ' ρ d') (hm : Det e e' χ χ' m) : d = m * d' := by
  obtain ⟨P, hP, rfl⟩ := h
  obtain ⟨P', hP', rfl⟩ := h'
  obtain ⟨M, hM, rfl⟩ := hm
  rw [← Matrix.det_mul]
  congr 1
  ext1 k l
  refine congrFun ((((isBas_iff_existsUnique _).1 (he₀ _ ρ)) (pull A L a χ (e k))).unique (hP k) ?_) l
  rw [hM]
  simp only [hP', Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, mul_smul]
  exact Finset.sum_comm

end Det

section Transport

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} {g : A'.left ⟶ A.left}
  [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {w : LB.Iso L' (L.pull g)}

theorem exists_natEquiv (hg : IsPullback g A'.hom A.hom f) (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) (a : ℤ) :
    ∃ Φ : ∀ T : Over S', SecM A' L' a T ≃+ SecM A L a ((Over.map f).obj T),
      (∀ (T : Over S') (c : Γ(T.left, ⊤)) x, Φ T (c • x) = (show Γ(((Over.map f).obj T).left, ⊤) from c) • Φ T x) ∧
      ∀ (T T₀ : Over S') (u : T ⟶ T₀) x, Φ T (pull A' L' a u x) = pull A L a ((Over.map f).map u) (Φ T₀ x) := by
  choose h hi f₁ s₁ using fun T : Over S' =>
    exists_total hg ((Over.map f).obj T) T (𝟙 _) (Category.id_comp _).symm
  choose E hE R using fun T : Over S' =>
    exists_secEquiv hw hL hL' (IsIso.inv_hom_id (h T)) (IsIso.hom_inv_id (h T)) (s₁ T).symm (fun c => c)
      (fun c => congrArg (fun q => q.appTop.hom c) ((f₁ T).trans (Category.comp_id _))) a
  refine ⟨E, hE, fun T T₀ u x => ?_⟩
  have nat : h T ≫ ((Over.map f).map u ▷ A).left = (u ▷ A').left ≫ h T₀ := by
    apply pullback.hom_ext
    · change (h T ≫ ((Over.map f).map u ▷ A).left) ≫ (fst _ A).left =
        ((u ▷ A').left ≫ h T₀) ≫ (fst ((Over.map f).obj T₀) A).left
      rw [Category.assoc, whisker_fst_left, ← Category.assoc, f₁, Category.assoc, Category.assoc, f₁,
        ← Category.assoc (u ▷ A').left, whisker_fst_left]
      simp
    · change (h T ≫ ((Over.map f).map u ▷ A).left) ≫ (snd _ A).left =
        ((u ▷ A').left ≫ h T₀) ≫ (snd ((Over.map f).obj T₀) A).left
      rw [Category.assoc, whisker_snd_left, s₁, Category.assoc, s₁, ← Category.assoc, whisker_snd_left]
  refine Subtype.ext ((R T _).unique_left hL' (IsIso.inv_hom_id (h T)) fun Z r z p q hp hq => ?_)
  rw [gs_pull_apply ((Over.map f).map u) _ (r ≫ h T) z p hp, gs_pull_apply u _ r z q hq, Category.assoc, nat,
    ← Category.assoc, R T₀ x Z (r ≫ (u ▷ A').left) z p q ?_ (chart_le A' L' a u q hq), ← pw_comp]
  · simp only [whisker_snd_left]
  · exact (congrArg (fun φ => φ (r z) ∈ LB.wchart L (fun _ : Fin 1 => (snd ((Over.map f).obj T₀) A).left) p)
      nat).mp (chart_le A L a ((Over.map f).map u) p hp)

theorem exists_frames (hg : IsPullback g A'.hom A.hom f) (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {a : ℤ}
    {κ : Type} {T : κ → Over S'} {n : ℕ} (e : ∀ i, Fin n → SecM A' L' a (T i)) (he : ∀ i, StableBas (e i)) :
    ∃ e' : ∀ i, Fin n → SecM A L a ((Over.map f).obj (T i)), (∀ i, StableBas (e' i)) ∧
      ∀ i j (T' : Over S') (χ : T' ⟶ T i) (ρ : T' ⟶ T j) d, Det (e i) (e j) χ ρ d →
        Det (e' i) (e' j) ((Over.map f).map χ) ((Over.map f).map ρ) d := by
  obtain ⟨Φ, h₁, h₂⟩ := exists_natEquiv hg hw hL hL' a
  refine ⟨fun i k => Φ _ (e i k), fun i T₁ _ u => ?_, ?_⟩
  · let T' : Over S' := Over.mk (Y := T₁.left) (u.left ≫ (T i).hom)
    let u' : T' ⟶ T i := Over.homMk u.left rfl
    have : IsAffine T'.left := ‹IsAffine T₁.left›
    have key : IsBas Γ(T₁.left, ⊤) fun k => pull A L a ((Over.map f).map u') (Φ _ (e i k)) := by
      let E' : SecM A' L' a T' ≃ₗ[Γ(T₁.left, ⊤)] SecM A L a ((Over.map f).obj T') := { Φ T' with map_smul' := h₁ T' }
      obtain ⟨b₁, b₂⟩ := he i T' u'
      have e₁ : (fun k => pull A L a ((Over.map f).map u') (Φ _ (e i k))) =
          E'.toLinearMap ∘ fun k => pull A' L' a u' (e i k) := funext fun k => (h₂ _ _ _ _).symm
      rw [e₁]
      refine ⟨b₁.map' _ E'.ker, ?_⟩
      rw [Set.range_comp, ← Submodule.map_span]
      exact (congrArg (Submodule.map E'.toLinearMap) b₂).trans ((Submodule.map_top _).trans E'.range)
    have gen : ∀ (X : Scheme.{0}) (x x' : X ⟶ S) (_ : x = x') (T₀ : Over S) (v : Over.mk x ⟶ T₀)
        (v' : Over.mk x' ⟶ T₀) (_ : v.left = v'.left) (b : Fin n → SecM A L a T₀),
        IsBas Γ(X, ⊤) (fun k => pull A L a v (b k)) → IsBas Γ(X, ⊤) (fun k => pull A L a v' (b k)) := by
      rintro X x _ rfl T₀ v v' hv b H
      obtain rfl : v = v' := Over.OverMorphism.ext hv
      exact H
    exact gen T₁.left ((u.left ≫ (T i).hom) ≫ f) T₁.hom ((Category.assoc _ _ _).trans (Over.w u)) _
      ((Over.map f).map u') u rfl _ key
  · rintro i j T' χ ρ d ⟨P, hP, rfl⟩
    refine ⟨P, fun k => ?_, rfl⟩
    rw [← h₂, hP]
    exact (map_sum (Φ T').toAddMonoidHom _ _).trans
      (Finset.sum_congr rfl fun l _ => (h₁ _ _ _).trans (congrArg _ (h₂ _ _ _ _)))

end Transport

section Main

variable {Z Y C : Scheme.{0}} {f : Z ⟶ Y} {G : Over Z} {G' : Over Y} {g : G.left ⟶ G'.left}
  [GrpObj G] [GrpObj G'] {L : LB G.left} {L' : LB G'.left} {w : LB.Iso L (L'.pull g)} {N : ℕ}

theorem exists_det_trans (hL : L.IsLB) (A : AmpFrames G L N) (i j : A.A.ι) :
    ∃ c m : Γ((A.A.U i ⊓ A.A.U j).toScheme, ⊤)ˣ,
      Det (fun _ : Fin 1 => SecM.ofSec G (A.th i)) (fun _ : Fin 1 => SecM.ofSec G (A.th j))
        (Over.homMk (Z.homOfLE inf_le_left) (by simp) : Over.mk (A.A.U i ⊓ A.A.U j).ι ⟶ Over.mk (A.A.U i).ι)
        (Over.homMk (Z.homOfLE inf_le_right) (by simp) : Over.mk (A.A.U i ⊓ A.A.U j).ι ⟶ Over.mk (A.A.U j).ι) c.val ∧
      Det (fun k => SecM.ofSec G (A.b i k)) (fun k => SecM.ofSec G (A.b j k))
        (Over.homMk (Z.homOfLE inf_le_left) (by simp) : Over.mk (A.A.U i ⊓ A.A.U j).ι ⟶ Over.mk (A.A.U i).ι)
        (Over.homMk (Z.homOfLE inf_le_right) (by simp) : Over.mk (A.A.U i ⊓ A.A.U j).ι ⟶ Over.mk (A.A.U j).ι) m.val ∧
      pa (A.A.U i ⊓ A.A.U j).ι (top_le le_rfl) (A.A.g i j).val = (c ^ A.r * m ^ A.s).val := by
  obtain ⟨c, M, ⟨t, h₁, h₂⟩, h₃, h₄⟩ := A.trans i j
  refine ⟨c, Matrix.GeneralLinearGroup.det M, ⟨Matrix.of fun _ _ => c.val, fun k => ?_, Matrix.det_fin_one _⟩,
    ⟨M.val, fun k => ?_, rfl⟩, ?_⟩
  · rw [lin_iff hL] at h₁ h₂
    rw [Fin.sum_univ_one, one_smul] at h₁
    exact h₁.symm.trans h₂
  · obtain ⟨t, h₁, h₂⟩ := h₃ k
    rw [lin_iff hL] at h₁ h₂
    rw [Fin.sum_univ_one, one_smul] at h₁
    exact h₁.symm.trans h₂
  · refine Eq.trans ?_ h₄
    have e : (A.A.U i ⊓ A.A.U j).topIso.inv = (A.A.U i ⊓ A.A.U j).ι.appLE (A.A.U i ⊓ A.A.U j) ⊤ (top_le le_rfl) :=
      (Scheme.Opens.ι_appLE (A.A.U i ⊓ A.A.U j) (A.A.U i ⊓ A.A.U j) ⊤ (top_le le_rfl)).symm
    rw [e]; rfl

theorem exists_gen_pull (hg : IsPullback g G.hom G'.hom f) (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB)
    (A : AmpFrames G L N) (s₁ : ∀ i, StableBas fun _ : Fin 1 => SecM.ofSec G (A.th i))
    (s₂ : ∀ i, StableBas fun k => SecM.ofSec G (A.b i k)) (q : C ⟶ Z) (i₀ : A.A.ι) (q₀ : C ⟶ (A.A.U i₀).toScheme)
    (hq : q₀ ≫ (A.A.U i₀).ι ≫ f = q ≫ f) : ∃ t : (A.A.pull q).Gen, t.IsGen := by
  obtain ⟨th, t₁, d₁⟩ := exists_frames hg hw hL' hL _ s₁
  obtain ⟨b, t₂, d₂⟩ := exists_frames hg hw hL' hL _ s₂
  let ρ : ∀ {T : Scheme.{0}} (r : T ⟶ C), Over.mk (r ≫ q ≫ f) ⟶ (Over.map f).obj (Over.mk (A.A.U i₀).ι) :=
    fun r => Over.homMk (r ≫ q₀) ((Category.assoc _ _ _).trans (congrArg (r ≫ ·) hq))
  let χ : ∀ {T : Scheme.{0}} (r : T ⟶ C) {i} (x : T ⟶ (A.A.U i).toScheme), x ≫ (A.A.U i).ι = r ≫ q →
      (Over.mk (r ≫ q ≫ f) ⟶ (Over.map f).obj (Over.mk (A.A.U i).ι)) :=
    fun r _ x hx => Over.homMk x ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ f) hx).trans (Category.assoc _ _ _)))
  refine exists_gen_of_affine A.isLB q
    (fun T r i d => ∃ (x : T ⟶ (A.A.U i).toScheme) (hx : x ≫ (A.A.U i).ι = r ≫ q) (c m : Γ(T, ⊤)ˣ),
      Det (th i) (th i₀) (χ r x hx) (ρ r) c.val ∧ Det (b i) (b i₀) (χ r x hx) (ρ r) m.val ∧
        d = (c ^ A.r * m ^ A.s).val) (fun T _ r i hi => ?_) ?_ ?_
  · have hr : Set.range (r ≫ q) ⊆ Set.range (A.A.U i).ι := by
      rintro _ ⟨y, rfl⟩
      exact ⟨⟨_, hi y⟩, rfl⟩
    have : IsAffine (Over.mk (r ≫ q ≫ f)).left := ‹IsAffine T›
    have hx := IsOpenImmersion.lift_fac _ _ hr
    obtain ⟨c, hc⟩ := exists_det (t₁ i) (t₁ i₀) (χ r _ hx) (ρ r)
    obtain ⟨m, hm⟩ := exists_det (t₂ i) (t₂ i₀) (χ r _ hx) (ρ r)
    exact ⟨_, Units.isUnit _, _, hx, c, m, hc, hm, rfl⟩
  · rintro T T' s r i _ ⟨x, hx, c, m, hc, hm, rfl⟩
    let s' : Over.mk ((s ≫ r) ≫ q ≫ f) ⟶ Over.mk (r ≫ q ≫ f) := Over.homMk s (Category.assoc _ _ _).symm
    let φ : Γ(T, ⊤)ˣ →* Γ(T', ⊤)ˣ := Units.map (pa s (V := ⊤) (le_pre_top _)).toMonoidHom
    have hx' : (s ≫ x) ≫ (A.A.U i).ι = (s ≫ r) ≫ q := by rw [Category.assoc, hx, Category.assoc]
    have e₁ : s' ≫ χ r x hx = χ (s ≫ r) (s ≫ x) hx' := Over.OverMorphism.ext rfl
    have e₂ : s' ≫ ρ r = ρ (s ≫ r) := Over.OverMorphism.ext (Category.assoc _ _ _).symm
    refine ⟨s ≫ x, hx', φ c, φ m, hc.comp s' e₁ e₂, hm.comp s' e₁ e₂, ?_⟩
    rw [← map_zpow, ← map_zpow, ← map_mul]
    rfl
  · rintro T _ r i j _ _ h ⟨x, hx, c, m, hc, hm, rfl⟩ ⟨x', hx', c', m', hc', hm', rfl⟩
    have hr : Set.range (r ≫ q) ⊆ Set.range (A.A.U i ⊓ A.A.U j).ι := by
      rintro _ ⟨y, rfl⟩
      exact ⟨⟨_, h (show y ∈ (⊤ : T.Opens) from trivial)⟩, rfl⟩
    obtain ⟨s, hs⟩ : ∃ s : T ⟶ (A.A.U i ⊓ A.A.U j).toScheme, s ≫ (A.A.U i ⊓ A.A.U j).ι = r ≫ q :=
      ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
    have : IsAffine (Over.mk (r ≫ q ≫ f)).left := ‹IsAffine T›
    obtain ⟨c₀, m₀, k₁, k₂, k₃⟩ := exists_det_trans hL A i j
    let s' : Over.mk (r ≫ q ≫ f) ⟶ (Over.map f).obj (Over.mk (A.A.U i ⊓ A.A.U j).ι) :=
      Over.homMk s ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ f) hs).trans (Category.assoc _ _ _)))
    let φ : Γ((A.A.U i ⊓ A.A.U j).toScheme, ⊤)ˣ →* Γ(T, ⊤)ˣ :=
      Units.map (pa s (V := ⊤) (le_pre_top _)).toMonoidHom
    have e₁ : s ≫ Z.homOfLE inf_le_left = x := by
      rw [← cancel_mono (A.A.U i).ι, Category.assoc, Scheme.homOfLE_ι, hs, hx]
    have e₂ : s ≫ Z.homOfLE inf_le_right = x' := by
      rw [← cancel_mono (A.A.U j).ι, Category.assoc, Scheme.homOfLE_ι, hs, hx']
    have a₁ : c = φ c₀ * c' := Units.ext (hc.mul (t₁ i₀) hc' ((d₁ _ _ _ _ _ _ k₁).comp s'
      (Over.OverMorphism.ext e₁) (Over.OverMorphism.ext e₂)))
    have a₂ : m = φ m₀ * m' := Units.ext (hm.mul (t₂ i₀) hm' ((d₂ _ _ _ _ _ _ k₂).comp s'
      (Over.OverMorphism.ext e₁) (Over.OverMorphism.ext e₂)))
    rw [← pa_pa _ s (top_le le_rfl) (le_pre_top _) _ hs h, k₃, a₁, a₂, mul_zpow, mul_zpow, _root_.mul_mul_mul_comm,
      ← map_zpow, ← map_zpow, ← map_mul]
    rfl

end Main

theorem exists_sec_fin {X : Scheme.{0}} {A : LB X} (hA : A.IsLB) (d : ℕ) (s : H0 A d) :
    ∃ s' : LB.Sec (LB.LinComb A (K := Fin d) (fun _ => 𝟙 X) (fun _ => 1)), nonzeroLocus s' = nonzeroLocus s := by
  obtain ⟨s', hs⟩ := exists_sec hA (φ' := fun _ : Fin d => 𝟙 X) (ε' := fun _ => 1) (fun U _ h => by simp) s
  refine ⟨s', TopologicalSpace.Opens.ext (Set.ext fun y => ?_)⟩
  choose J hJ using fun χ : X ⟶ X => exists_chart hA (χ y)
  have hJ' : Geo.Tor.Good A y J := hJ
  exact (mem_nonzeroLocus_iff_isUnit s' (hJ'.mem (fun _ : Fin d => 𝟙 X) (𝟙 X))).trans
    ((congrArg IsUnit (hs X (𝟙 X) y J hJ')).to_iff.trans
      (mem_nonzeroLocus_iff_isUnit s (hJ'.mem (fun _ : Fin 1 => 𝟙 X) (𝟙 X))).symm)

theorem isFinite_of_ampFrames : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z Y : Scheme.{0}) [IsLocallyNoetherian Z] (z : Z ⟶ Sp ℤ) (t : SAB H Z) (t' : SAB H Y) (f : Z ⟶ Y) (_ : SABMap t t' f) (N : ℕ) (_ : GlobalTheory.LN.AmpFrames t.G t.PP.L N), 0 < N → Geo.Tor.IsNormalScheme Z → Flat z → IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → IsProper f → IsFinite f := by
  intro h₁ h₂ E _ _ _ H Z Y _ z t t' f ν N A hN hZ hz hp hA hK hf
  have hL := t.PP.isLB
  have hb := basisAlong_of_ampFrames h₁ h₂ E H Z z t N A hN hZ hz hp hA hK
  have s₁ : ∀ i, StableBas fun _ : Fin 1 => SecM.ofSec t.G (A.th i) := fun i =>
    stableBas_of_traits hL _ (exists_stableBas_local h₂.secBaseChangeAny t hp hA hK 1 le_rfl) fun p =>
      ⟨(A.A.U i).toScheme.presheaf.stalk p, inferInstance, inferInstance, (A.A.U i).toScheme.fromSpecStalk p,
        Scheme.fromSpecStalk_closedPoint, (basisAlong_iff hL _ _ _).1 (hb i _ _).1⟩
  have s₂ : ∀ i, StableBas fun k => SecM.ofSec t.G (A.b i k) := fun i =>
    stableBas_of_traits hL _ (exists_stableBas_local h₂.secBaseChangeAny t hp hA hK N hN) fun p =>
      ⟨(A.A.U i).toScheme.presheaf.stalk p, inferInstance, inferInstance, (A.A.U i).toScheme.fromSpecStalk p,
        Scheme.fromSpecStalk_closedPoint, (basisAlong_iff hL _ _ _).1 (hb i _ _).2⟩
  obtain ⟨w, hw, -⟩ := ν.lin
  have : LocallyQuasiFinite f := by
    refine GlobalTheory.AmpleFibre.locallyQuasiFinite_of_trivial_on_fibres Z Y f A.A hf A.isLB (fun x => ?_) fun k _ _ y C _ i hi => ?_
    · obtain ⟨d, s, -, hs⟩ := A.ample x
      obtain ⟨s', e⟩ := exists_sec_fin A.isLB d s
      exact ⟨d, s', by rw [e]; exact hs⟩
    · have : JacobsonSpace C := LocallyOfFiniteType.jacobsonSpace (i ≫ pullback.snd f y)
      obtain ⟨c, -, hc⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set C)) Set.univ_nonempty
        isClosed_univ.isLocallyClosed
      replace hc : IsClosed {c} := hc
      obtain ⟨x, hx⟩ : ∃ x : Sp k ⟶ C, x ≫ i ≫ pullback.snd f y = 𝟙 _ :=
        ⟨pointOfClosedPoint _ c hc, pointOfClosedPoint_comp _ c hc⟩
      obtain ⟨i₀, hi₀⟩ := exists_chart A.isLB ((x ≫ i ≫ pullback.fst f y) (IsLocalRing.closedPoint k))
      have hr : Set.range (x ≫ i ≫ pullback.fst f y) ⊆ Set.range (A.A.U i₀).ι := by
        rintro _ ⟨u, rfl⟩
        obtain rfl : u = IsLocalRing.closedPoint k := Subsingleton.elim (α := PrimeSpectrum k) _ _
        exact ⟨⟨_, hi₀⟩, rfl⟩
      refine exists_gen_pull ν.cart.1 ((isGen_iff w).1 hw) hL t'.PP.isLB A s₁ s₂ _ i₀
        ((i ≫ pullback.snd f y) ≫ IsOpenImmersion.lift _ _ hr) ?_
      rw [Category.assoc, IsOpenImmersion.lift_fac_assoc]
      simp only [Category.assoc, pullback.condition, reassoc_of% hx]
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

end GlobalTheory.FrameFinite
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteOfAmpleDeterminantFramesPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFinite_of_ampleDeterminantFrames_pullback : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z Y : Scheme.{0}) [IsLocallyNoetherian Z] (z : Z ⟶ Sp ℤ) (t : SAB H Z) (t' : SAB H Y) (f : Z ⟶ Y) (_ : SABMap t t' f) (N : ℕ) (_ : GlobalTheory.LN.AmpFrames t.G t.PP.L N), 0 < N → IsNormalScheme Z → Flat z → IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → IsProper f → IsFinite f := by
  first | exact @GlobalTheory.FrameFinite.isFinite_of_ampFrames | exact GlobalTheory.FrameFinite.isFinite_of_ampFrames | (intros; apply GlobalTheory.FrameFinite.isFinite_of_ampFrames <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoNearNormalPointOfFiniteBirationalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIso_near_normal_point_of_finite_birational : ∀ (U M : Scheme.{0}) [IsLocallyNoetherian M] (u : U ⟶ M) (W : M.Opens), IsFinite u → IsReduced U → IsIso (u ∣_ W) → Dense (W : Set M) → Dense ((u ⁻¹ᵁ W : U.Opens) : Set U) → ∀ x : M, IsDomain (M.presheaf.stalk x) → IsIntegrallyClosed (M.presheaf.stalk x) → ∃ V : M.Opens, x ∈ V ∧ IsIso (u ∣_ V) := by
  first | exact @GlobalTheory.FiniteBirationalNear.main | exact GlobalTheory.FiniteBirationalNear.main | (intros; apply GlobalTheory.FiniteBirationalNear.main <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionLevelExtendsFromDenseOpenNormal
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionLevelExtendsFromDenseOpenNormal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

theorem GlobalTheory.exists_torsion_level_extend : ∀ (Λ : Type) [AddCommGroup Λ] (N : ℕ) (S W : Scheme.{0}) [IsLocallyNoetherian S] (j : W ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (G' : Over W) [GrpObj G'] (φ : G'.left ⟶ G.left) (lv' : Λ → (𝟙_ (Over W) ⟶ G')), Geo.Tor.IsNormalScheme S → IsOpenImmersion j → IsDominant j → IsProper G.hom → IsUnit (N : Γ(S, ⊤)) → IsGrpPullback G' G j φ → (∀ a c, lv' (a + c) = lv' a * lv' c) → (∀ a, lv' (N • a) = 1) → ∃ lv : Λ → (𝟙_ (Over S) ⟶ G), (∀ a c, lv (a + c) = lv a * lv c) ∧ (∀ a, lv (N • a) = 1) ∧ ∀ a, (lv' a).left ≫ φ = j ≫ (lv a).left := by
  intro Λ _ N S W _ j G _ _ G' _ φ lv' hS _ _ _ hN gp hadd hker
  have hred : IsReduced S := by
    have : ∀ x : S, _root_.IsReduced (S.presheaf.stalk x) := fun x => by
      obtain ⟨_, _⟩ := hS x
      infer_instance
    exact isReduced_of_isReduced_stalk _
  have hqc : QuasiCompact j := inferInstance
  let P : Over S := Over.mk ((𝟙_ (Over W)).hom ≫ j)
  let ρ : (𝟙_ (Over W) ⟶ G') →* (P ⟶ G) := pushHom gp _
  have hρ : ∀ x, (ρ x).left = x.left ≫ φ := fun _ => rfl
  have h0 : lv' 0 = 1 := by simpa using hker 0
  have hpow : ∀ (n : ℕ) a, lv' (n • a) = lv' a ^ n := fun n a => by
    induction n with
    | zero => simpa using h0
    | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]
  have hex : ∀ a, ∃ σ : S ⟶ G.left, σ ≫ G.hom = 𝟙 S ∧ j ≫ σ = (lv' a).left ≫ φ := fun a => by
    obtain ⟨s, h₁, h₂⟩ := GlobalTheory.exists_section_of_pow_eq_one hS j G N hN P (ρ (lv' a))
      (by rw [← map_pow, ← hpow, hker, map_one]) (𝟙 _) ((Category.id_comp _).trans (Category.id_comp _))
    exact ⟨s, h₁, h₂.trans (Category.id_comp _)⟩
  choose σ hσ₁ hσ₂ using hex
  let lv : Λ → (𝟙_ (Over S) ⟶ G) := fun a => Over.homMk (σ a) (hσ₁ a)
  let u : P ⟶ 𝟙_ (Over S) := Over.homMk j ((Category.comp_id _).trans (Category.id_comp _).symm)
  have hu : ∀ a, u ≫ lv a = ρ (lv' a) := fun a => Over.OverMorphism.ext (hσ₂ a)
  have inj : ∀ s t : 𝟙_ (Over S) ⟶ G, u ≫ s = u ≫ t → s = t := fun s t h =>
    Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := S) G.hom ((Over.w s).trans (Over.w t).symm) j
      (congrArg (fun z => z.left) h))
  refine ⟨lv, fun a c => inj _ _ ?_, fun a => inj _ _ ?_, fun a => (hσ₂ a).symm⟩
  · rw [MonObj.comp_mul, hu, hu, hu, hadd, map_mul]
  · rw [hu, hker, map_one, MonObj.comp_one]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionLevelExtendsFromDenseOpenNormalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionLevel_extends_from_dense_open_normal : ∀ (Λ : Type) [AddCommGroup Λ] (N : ℕ) (S W : Scheme.{0}) [IsLocallyNoetherian S] (j : W ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (G' : Over W) [GrpObj G'] (φ : G'.left ⟶ G.left) (lv' : Λ → (𝟙_ (Over W) ⟶ G')), IsNormalScheme S → IsOpenImmersion j → IsDominant j → IsProper G.hom → IsUnit (N : Γ(S, ⊤)) → IsGrpPullback G' G j φ → (∀ a c, lv' (a + c) = lv' a * lv' c) → (∀ a, lv' (N • a) = 1) → ∃ lv : Λ → (𝟙_ (Over S) ⟶ G), (∀ a c, lv (a + c) = lv a * lv c) ∧ (∀ a, lv (N • a) = 1) ∧ ∀ a, (lv' a).left ≫ φ = j ≫ (lv a).left := by
  first | exact @GlobalTheory.exists_torsion_level_extend | exact GlobalTheory.exists_torsion_level_extend | (intros; apply GlobalTheory.exists_torsion_level_extend <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullLevelObjectOfCoveringPullbacks
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullLevelObjectOfCoveringPullbacks
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.FullDescent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {n N : ℕ}

theorem exists_lift {S S' : Scheme.{0}} (f : S' ⟶ S) {k : Type} [Field k] (x : Sp k ⟶ S) (p : Sp k)
    (hp : x p ∈ Set.range f) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (i : k →+* Ω) (y : Sp Ω ⟶ S'), spMap i ≫ x = y ≫ f := by
  obtain ⟨q, hq⟩ := hp
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := x) (g := f) p q hq.symm
  let Ω : Type := AlgebraicClosure ((pullback x f).residueField z)
  let u : Sp Ω ⟶ pullback x f :=
    Spec.map (CommRingCat.ofHom (algebraMap ((pullback x f).residueField z) Ω)) ≫ (pullback x f).fromSpecResidueField z
  refine ⟨Ω, inferInstance, inferInstance, (Spec.preimage (u ≫ pullback.fst x f)).hom, u ≫ pullback.snd x f, ?_⟩
  have e : spMap (Spec.preimage (u ≫ pullback.fst x f)).hom = u ≫ pullback.fst x f := Spec.map_preimage _
  rw [e]
  exact (Category.assoc _ _ _).trans ((congrArg (u ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm)

theorem tate_push {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (ν : SABMap t' t f)
    {k : Type} [Field k] {y : Sp k ⟶ S'} {x : Sp k ⟶ S} (hx : x = y ≫ f)
    (I : TateIso D k (Over.mk y ⟶ t'.G) (fun a g => g ≫ t'.act.act a)
        (fun m g g' c => Out.WeilIs t'.G t'.PP.L m g g' (unitOn c))) :
    ∃ J : TateIso D k (Over.mk x ⟶ t.G) (fun a g => g ≫ t.act.act a)
        (fun m g g' c => Out.WeilIs t.G t.PP.L m g g' (unitOn c)),
      J.ζ = I.ζ ∧ ∀ m a, (J.ev m a).left = (I.ev m a).left ≫ ν.φ := by
  subst hx
  have hL : LBIso t'.PP.L (t.PP.L.pull ν.cm.F) := by
    obtain ⟨w, hw, -⟩ := ν.lin
    exact ⟨w, hw⟩
  refine ⟨ObjPull.tateMove (ObjPull.pushEquiv ν.cart (Over.mk y)).symm (fun c g => ?_) (fun m g g' c hc => ?_) I,
    rfl, fun _ _ => rfl⟩
  · obtain ⟨g, rfl⟩ := (ObjPull.pushEquiv ν.cart (Over.mk y)).surjective g
    rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_eq]
    apply Over.OverMorphism.ext
    show (g.left ≫ _) ≫ _ = (g.left ≫ _) ≫ _
    rw [Category.assoc, ← ν.act, Category.assoc]
  · exact (weilIs_iff_of_isGrpPullback_comm S S' t.G t'.G f ν.cm.F t.PP.L t'.PP.L t.PP.isLB t'.PP.isLB ν.cart hL
      (Over.mk y) m _ _ g g' _ (ObjPull.pushEquiv_symm_left ν.cart (Over.mk y) g).symm
      (ObjPull.pushEquiv_symm_left ν.cart (Over.mk y) g').symm).1 hc

theorem torsion_ext (hL : Out.Laws) {S : Scheme.{0}} (t : SAB H S) (hp : IsProper t.G.hom)
    (ha : Out.RelAmple t.G t.PP.L) (hk : Out.KTriv t.G t.PP.L) {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed K]
    [CharZero K] (i : K →+* Ω) (x : Sp K ⟶ S) :
    Function.Injective (TateIsoFieldExt.precomp
        (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) t.G) ∧
      ∀ m, 0 < m → ∀ z : Over.mk (spMap i ≫ x) ⟶ t.G, z ^ m = 1 → ∃ y : Over.mk x ⟶ t.G, y ^ m = 1 ∧
        TateIsoFieldExt.precomp (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) t.G y = z := by
  obtain ⟨P, φ, -, hφ, -⟩ := exists_polAV_pullback_of_isLocalRing E H S t hp ha hk K x
  obtain ⟨hinj, honto⟩ := torsion_points_field_extension hL (Sp K) P K Ω i (𝟙 _)
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback hφ (𝟙 _) x (Category.id_comp _).symm
  obtain ⟨e', he'⟩ := exists_mulEquiv_of_isGrpPullback hφ (spMap i ≫ 𝟙 _) (spMap i ≫ x) (by simp)
  have key : ∀ y, TateIsoFieldExt.precomp (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) t.G (e y) =
      e' ((Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ 𝟙 (Sp K)) ⟶ Over.mk (𝟙 (Sp K))) ≫ y) := fun y => by
    apply Over.OverMorphism.ext
    rw [he']
    show spMap i ≫ (e y).left = (spMap i ≫ y.left) ≫ φ
    rw [he]
    exact (Category.assoc _ _ _).symm
  refine ⟨fun y y' h => ?_, fun m hm z hz => ?_⟩
  · obtain ⟨y, rfl⟩ := e.surjective y
    obtain ⟨y', rfl⟩ := e.surjective y'
    rw [key, key] at h
    exact congrArg e (hinj (e'.injective h))
  · obtain ⟨z, rfl⟩ := e'.surjective z
    rw [← map_pow, map_eq_one_iff _ e'.injective] at hz
    obtain ⟨y, hy, rfl⟩ := honto m z (Nat.cast_ne_zero.2 hm.ne') hz
    exact ⟨e y, by rw [← map_pow, hy, map_one], key y⟩

theorem fullObj_of_cover : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp (RZ H n N)) (t : SAB H S) (lv : D.La → (𝟙_ (Over S) ⟶ t.G)), 0 < N → IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (∀ a c, lv (a + c) = lv a * lv c) → (∀ a, lv (N • a) = 1) → (∀ p : S, ∃ (S' : Scheme.{0}) (f : S' ⟶ S) (t' : SAB H S') (ν : SABMap t' t f) (lv' : D.La → (𝟙_ (Over S') ⟶ t'.G)), p ∈ Set.range f ∧ (∀ a, (lv' a).left ≫ ν.φ = f ≫ (lv a).left) ∧ FullObj D (f ≫ s) t' lv') → FullObj D s t lv := by
  intro hL E _ _ _ H D n N S s t lv hN hp ha hk hadd hker hcov
  refine ⟨hp, ha, hk, hadd, hker, fun k _ _ _ x β hx => ?_⟩
  obtain ⟨S', f, t', ν, lv', hq, hl, o⟩ := hcov (x (default : PrimeSpectrum k))
  obtain ⟨Ω, _, _, i, y, hy⟩ := exists_lift f x _ hq
  have : CharZero Ω := (i.charZero_iff i.injective).1 inferInstance
  have hy' : y ≫ f ≫ s = spMap (i.comp β) := by
    rw [← Category.assoc, ← hy, Category.assoc, hx]
    exact (Spec.map_comp _ _).symm
  obtain ⟨hdet, I', hI', hA'⟩ := o.geom Ω y (i.comp β) hy'
  refine ⟨?_, ?_⟩
  · refine (detCond_iff_of_field_extension E H D S t.G k Ω i x t.act _ t.semi.smooth).1 ?_
    rw [hy]
    exact (detCond_iff_of_sabMap E H D S S' t t' f ⟨ν⟩ Ω y _).1 hdet
  obtain ⟨J, hJ, hJ'⟩ := tate_push ν hy I'
  obtain ⟨hinj, honto⟩ := torsion_ext hL t hp ha hk i x
  let g : Over.mk (spMap i ≫ x) ⟶ Over.mk x := Over.homMk (spMap i) rfl
  obtain ⟨I, hI⟩ := TateIsoFieldExt.down D i (TateIsoFieldExt.precomp g t.G)
    (act := fun a z => z ≫ t.act.act a) (act' := fun a z => z ≫ t.act.act a)
    (e' := fun m z z' c => Out.WeilIs t.G t.PP.L m z z' (unitOn c))
    (e := fun m z z' c => Out.WeilIs t.G t.PP.L m z z' (unitOn c)) hinj honto
    (fun c z => (Category.assoc g z (t.act.act c)).symm)
    (fun c => by
      haveI := t.act.hom c
      exact MonObj.one_comp (t.act.act c))
    (fun m z z' c => weilIs_fieldExt_iff S t.G k Ω i x t.PP.L m z z' c
      ⟨inferInstance, t.semi.smooth, hp, t.semi.geomConnected⟩ t.PP.isLB) J
  obtain ⟨h₁, h₂⟩ := hI N hN
  refine ⟨I, i.injective ?_, fun a => hinj ?_⟩
  · rw [← h₁, hJ, hI']
    rfl
  · rw [← h₂]
    apply Over.OverMorphism.ext
    rw [hJ', ← hA', Over.comp_left, ObjPull.toUnit_left', Category.assoc, hl]
    show spMap i ≫ (toUnit (Over.mk x) ≫ lv a).left = y ≫ f ≫ (lv a).left
    rw [Over.comp_left, ObjPull.toUnit_left', ← Category.assoc y, ← hy]
    exact (Category.assoc _ _ _).symm

end GlobalTheory.FullDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullLevelObjectOfCoveringPullbacksStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fullLevelObject_of_covering_pullbacks : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp (RZ H n N)) (t : SAB H S) (lv : D.La → (𝟙_ (Over S) ⟶ t.G)), 0 < N → IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (∀ a c, lv (a + c) = lv a * lv c) → (∀ a, lv (N • a) = 1) → (∀ p : S, ∃ (S' : Scheme.{0}) (f : S' ⟶ S) (t' : SAB H S') (ν : SABMap t' t f) (lv' : D.La → (𝟙_ (Over S') ⟶ t'.G)), p ∈ Set.range f ∧ (∀ a, (lv' a).left ≫ ν.φ = f ≫ (lv a).left) ∧ FullObj D (f ≫ s) t' lv') → FullObj D s t lv := by
  first | exact @GlobalTheory.FullDescent.fullObj_of_cover | exact GlobalTheory.FullDescent.fullObj_of_cover | (intros; apply GlobalTheory.FullDescent.fullObj_of_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianLocusOpenFamilyOverLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.AbelianLocusNormalisation

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_pull {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) : ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull f t
  exact ⟨_, ⟨m⟩⟩


theorem exists_comp {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S}
    {g : S'' ⟶ S'} (m' : SABMap t'' t' g) (m : SABMap t' t f) {h : S'' ⟶ S} (e : g ≫ f = h) :
    ∃ n : SABMap t'' t h, n.φ = m'.φ ≫ m.φ := by
  subst e
  exact ObjMaps.exists_sab_comp m m'

theorem exists_cancel {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S}
    {h : S'' ⟶ S} (m : SABMap t' t f) (n : SABMap t'' t h) {g : S'' ⟶ S'} (e : g ≫ f = h) :
    ∃ m' : SABMap t'' t' g, n.φ = m'.φ ≫ m.φ := by
  subst e
  exact ObjMaps.exists_sab_cancel m n

theorem isProper_pull {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    (h : IsProper t.G.hom) : IsProper t'.G.hom :=
  MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 h

theorem isAbelianScheme_of_isProper {S : Scheme.{0}} (t : SAB H S) (h : IsProper t.G.hom) : IsAbelianScheme t.G :=
  ⟨inferInstance, t.semi.smooth, h, t.semi.geomConnected⟩

theorem pol_of_map {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    (h : IsProper t.G.hom) : (Out.RelAmple t.G t.PP.L → Out.RelAmple t'.G t'.PP.L) ∧
      (Out.KTriv t.G t.PP.L → Out.KTriv t'.G t'.PP.L) := by
  obtain ⟨w, hw, -⟩ := m.lin
  exact (pol_pull S S' t.G t'.G f m.φ t.PP.L t'.PP.L t.PP.isLB t'.PP.isLB (isAbelianScheme_of_isProper t h) m.cart
    ⟨w, hw⟩).2

theorem isNormalScheme_of_open {X Y : Scheme.{0}} (f : Y ⟶ X) [IsOpenImmersion f] (h : Geo.Tor.IsNormalScheme X) :
    Geo.Tor.IsNormalScheme Y := fun x => by
  obtain ⟨_, _⟩ := h (f x)
  let e := (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
  exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩

theorem isReduced_of_normal {X : Scheme.{0}} (h : Geo.Tor.IsNormalScheme X) : IsReduced X := by
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    obtain ⟨_, _⟩ := h x
    infer_instance
  exact isReduced_of_isReduced_stalk X

theorem exists_full_through (hE : GlobalTheory.LN.HomExtSt) (h1 : Out.Laws) (h2 : Out.Laws2) {D : Datum H} {n N : ℕ}
    (hN : 0 < N) {S W : Scheme.{0}} [IsLocallyNoetherian S] (s : S ⟶ Sp (RZ H n N)) (t : SAB H S)
    (lv : D.La → (𝟙_ (Over S) ⟶ t.G)) (hp : IsProper t.G.hom) (add : ∀ a c, lv (a + c) = lv a * lv c)
    (ker : ∀ a, lv (N • a) = 1) (j : W ⟶ S) [IsOpenImmersion j] [IsDominant j] (tW : SAB H W) (ν : SABMap tW t j)
    (lW : D.La → (𝟙_ (Over W) ⟶ tW.G)) (hl : ∀ a, (lW a).left ≫ ν.φ = j ≫ (lv a).left)
    (o : FullObj D (j ≫ s) tW lW) (p : S) :
    ∃ (S' : Scheme.{0}) (f : S' ⟶ S) (t' : SAB H S') (ν : SABMap t' t f) (lv' : D.La → (𝟙_ (Over S') ⟶ t'.G)),
      p ∈ Set.range f ∧ (∀ a, (lv' a).left ≫ ν.φ = f ≫ (lv a).left) ∧ FullObj D (f ≫ s) t' lv' := by
  obtain ⟨ξ, hξ, hs⟩ := exists_mem_genericPoints_specializes p
  have hξj := genericPoints_subset_range_of_isDominant j hξ
  by_cases hne : ξ = p
  · exact ⟨W, j, tW, ν, lW, hne ▸ hξj, hl, o⟩
  obtain ⟨V, _, _, -, f, hf₀, hf₁⟩ := exists_complete_discreteValuationRing_of_specializes hs hne
  let K := FractionRing V
  let g : Sp K ⟶ Sp V := spMap (algebraMap V K)
  have hr : Set.range (g ≫ f) ⊆ Set.range j := by
    rintro _ ⟨q, rfl⟩
    have : g q = (⊥ : PrimeSpectrum V) := by
      apply PrimeSpectrum.ext
      show Ideal.comap (algebraMap V K) q.asIdeal = ⊥
      rw [Subsingleton.elim (α := PrimeSpectrum K) q ⊥]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective V K)
    rw [Scheme.Hom.comp_apply, this, hf₀]
    exact hξj
  let x : Sp K ⟶ W := IsOpenImmersion.lift j (g ≫ f) hr
  have hx : x ≫ j = g ≫ f := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨tV, ⟨νV⟩⟩ := exists_pull (S' := Sp V) f t
  obtain ⟨tK, ⟨νK⟩⟩ := exists_pull g tV
  obtain ⟨κ, hκ⟩ := exists_comp νK νV rfl
  obtain ⟨κ', hκ'⟩ := exists_cancel ν κ hx
  let lV := fun a => ObjPull.secPull νV.cart (lv a)
  let lK := fun a => ObjPull.secPull κ'.cart (lW a)
  have oK : FullObj D (x ≫ j ≫ s) tK lK :=
    (GlobalTheory.T.fullLevelObject_pullback_exists_and_full E H D n N W _ (j ≫ s) tW lW x).2 tK κ' lK (fun a => ObjPull.secPull_left _ _) o
  have hpV := isProper_pull νV hp
  obtain ⟨am, kt⟩ := GlobalTheory.T.relAmple_principal_of_genericFibre_dvr hE h1 h2 E H V K tV tK νK hpV oK.ample oK.ktriv
  refine ⟨Sp V, f, tV, νV, lV, ⟨_, hf₁⟩, fun a => ObjPull.secPull_left _ _, ?_⟩
  refine GlobalTheory.T.fullObject_of_genericFibre_dvr h1 h2 E H D n N V K (f ≫ s) tV lV tK νK lK hN hpV am kt (fun a c => ?_) (fun a => ?_)
    (fun a => ?_) ?_
  · simp only [lV, add, map_mul]
  · simp only [lV, ker, map_one]
  · apply νV.cart.1.hom_ext
    · have e₁ : (lK a).left ≫ κ'.φ = x ≫ (lW a).left := ObjPull.secPull_left _ _
      have e₂ : (lV a).left ≫ νV.φ = f ≫ (lv a).left := ObjPull.secPull_left _ _
      change ((lK a).left ≫ νK.φ) ≫ νV.φ = (g ≫ (lV a).left) ≫ νV.φ
      rw [Category.assoc, ← hκ, hκ', ← Category.assoc, e₁, Category.assoc, hl, ← Category.assoc, hx, Category.assoc,
        Category.assoc, e₂]
    · rw [Category.assoc, νK.cart.1.w, ← Category.assoc, Over.w (lK a), Category.assoc, Over.w (lV a)]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  · rwa [← Category.assoc, hx, Category.assoc] at oK

theorem exists_full (hE : GlobalTheory.LN.HomExtSt) (h1 : Out.Laws) (h2 : Out.Laws2) {D : Datum H} {n N : ℕ}
    (hN : 0 < N) (hu : IsUnit (N : RZ H n N)) {S W : Scheme.{0}} [IsLocallyNoetherian S]
    (hS : Geo.Tor.IsNormalScheme S) (s : S ⟶ Sp (RZ H n N)) (t : SAB H S) (hp : IsProper t.G.hom)
    (hq : IsQProjOver (t.G.hom ≫ s)) (j : W ⟶ S) [IsOpenImmersion j] [IsDominant j] (tW : SAB H W)
    (ν : SABMap tW t j) (lW : D.La → (𝟙_ (Over W) ⟶ tW.G)) (o : FullObj D (j ≫ s) tW lW) :
    ∃ lv : D.La → (𝟙_ (Over S) ⟶ t.G), FullObj D s t lv ∧ ∀ a, (lW a).left ≫ ν.φ = j ≫ (lv a).left := by
  have hu' : IsUnit (N : Γ(S, ⊤)) := by
    simpa using hu.map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (RZ H n N))).inv.hom)
  obtain ⟨lv, add, ker, hl⟩ := GlobalTheory.T.torsionLevel_extends_from_dense_open_normal D.La N S W j t.G tW.G ν.φ lW hS ‹_› ‹_› hp hu' ν.cart o.add o.ker
  have th := exists_full_through hE h1 h2 hN s t lv hp add ker j tW ν lW hl o
  have am : Out.RelAmple t.G t.PP.L := GlobalTheory.T.relAmple_of_polarised_at_every_point E H S t hp
    (fun A _ y B φ h => GlobalTheory.T.isProjOver_baseChange_of_proper_quasiProjective _ A S s t.G y B φ hp hq h) fun p => by
      obtain ⟨S', f, t', ν', _, a, -, b⟩ := th p
      exact ⟨S', f, t', ν', a, b.ample, b.ktriv⟩
  have kt : Out.KTriv t.G t.PP.L := GlobalTheory.T.kernelTrivial_of_every_point_covered h1 E H S t hp am fun p => by
    obtain ⟨S', f, t', ν', _, a, -, b⟩ := th p
    exact ⟨S', f, t', ν', a, b.ktriv⟩
  exact ⟨lv, GlobalTheory.T.fullLevelObject_of_covering_pullbacks h1 E H D n N S s t lv hN hp am kt add ker th, hl⟩

theorem isProper_of_isProjOver {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} (h : IsProjOver s) :
    IsProper s := by
  obtain ⟨N, i, hi, rfl⟩ := h
  have := isProper_str R N
  infer_instance

theorem separated_finiteType_of_isQProjOver {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R}
    (h : IsQProjOver s) : IsSeparated s ∧ LocallyOfFiniteType s := by
  obtain ⟨N, i, hi, -, rfl⟩ := h
  have := isProper_str R N
  exact ⟨inferInstance, inferInstance⟩

theorem isProper_of_abLocus (hE : GlobalTheory.LN.HomExtSt) {R : Type} [CommRing R] [IsNoetherianRing R] {Z M : Scheme.{0}}
    {sZ : Z ⟶ Sp R} {sM : M ⟶ Sp R} (hZ : IsProjOver sZ) (hM : IsQProjOver sM) {t : SAB H Z} {tM : SAB H M}
    (hp : IsProper tM.G.hom) {U : Z.Opens} (hU : abLocus t.G ⊆ U) {u : U.toScheme ⟶ M} (hu : u ≫ sM = U.ι ≫ sZ)
    {tU : SAB H U.toScheme} (mU : SABMap tU t U.ι) (mM : SABMap tU tM u) : IsProper u := by
  have := isProper_of_isProjOver hZ
  obtain ⟨_, _⟩ := separated_finiteType_of_isQProjOver hM
  have : IsLocallyNoetherian M := LocallyOfFiniteType.isLocallyNoetherian sM
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  refine GlobalTheory.T.isProper_of_completeDVR_lift_generic R _ M u sM ‹_› ?_ fun V K _ _ _ _ _ _ _ x y _ hxy => ?_
  · obtain ⟨N, i, hi, e⟩ := hZ
    exact ⟨N, U.ι ≫ i, inferInstance, inferInstance, by rw [hu, Category.assoc, e]⟩
  obtain ⟨z, hz, -⟩ := valuative_lift_of_isProper sZ (x ≫ U.ι) (y ≫ sM)
    (by rw [Category.assoc, ← hu, reassoc_of% hxy])
  obtain ⟨tz, ⟨mz⟩⟩ := exists_pull z t
  obtain ⟨ty, ⟨my⟩⟩ := exists_pull y tM
  obtain ⟨tx, ⟨mx⟩⟩ := exists_pull x tU
  obtain ⟨a, -⟩ := exists_comp mx mU rfl
  obtain ⟨b, -⟩ := exists_comp mx mM rfl
  obtain ⟨a', -⟩ := exists_cancel mz a hz
  obtain ⟨b', -⟩ := exists_cancel my b hxy.symm
  have hA : IsAbelianScheme tz.G := isAbelianScheme_of_common_generic_fibre ty.G tz.G
    (isAbelianScheme_of_isProper ty (isProper_pull my hp)) tz.semi (fun f hf => by
      obtain ⟨F, hF, -⟩ := hE V K ty.G tz.G ty.semi tz.semi f hf
      exact ⟨F, hF.2⟩) tx.G b'.cart a'.cart
  have := hA.proper
  have hr : Set.range z ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    exact (range_subset_abLocus_of_isProper t.semi mz.cart.1).trans hU
  exact ⟨IsOpenImmersion.lift U.ι z hr, by rw [← cancel_mono U.ι, Category.assoc, IsOpenImmersion.lift_fac, hz]⟩

theorem isAffineHom_of_isProper {R : Type} [CommRing R] {X Z V : Scheme.{0}} [IsAffine V] (g : X ⟶ Z) [IsImmersion g]
    (u : X ⟶ V) [IsProper u] (sZ : Z ⟶ Sp R) [IsSeparated sZ] (sV : V ⟶ Sp R) (h : u ≫ sV = g ≫ sZ) :
    IsAffineHom g := by
  let l : X ⟶ pullback sV sZ := pullback.lift u g h
  have e₁ : l ≫ pullback.fst sV sZ = u := pullback.lift_fst _ _ _
  have e₂ : l ≫ pullback.snd sV sZ = g := pullback.lift_snd _ _ _
  have : IsProper (l ≫ pullback.fst sV sZ) := by rwa [e₁]
  have : IsProper l := IsProper.of_comp l (pullback.fst sV sZ)
  have : IsImmersion (l ≫ pullback.snd sV sZ) := by rwa [e₂]
  have : IsImmersion l := IsImmersion.of_comp l (pullback.snd sV sZ)
  have : IsClosedImmersion l := IsClosedImmersion.of_isPreimmersion l l.isClosedMap.isClosed_range
  have : IsAffineHom sV := inferInstance
  have : IsAffineHom (pullback.snd sV sZ) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback sV sZ) ‹_›
  rw [← e₂]
  infer_instance

theorem isFinite_of_isProper (h1 : Out.Laws) (h2 : Out.Laws2) {R : Type} [CommRing R] {Z M : Scheme.{0}}
    [IsLocallyNoetherian Z] (sZ : Z ⟶ Sp R) [IsSeparated sZ] (sM : M ⟶ Sp R) (z : Z ⟶ Sp ℤ) [Flat z]
    (hn : Geo.Tor.IsNormalScheme Z) {t : SAB H Z} {tM : SAB H M} (hp : IsProper tM.G.hom)
    (am : Out.RelAmple tM.G tM.PP.L) (kt : Out.KTriv tM.G tM.PP.L) {N : ℕ} (hN : 0 < N)
    (A : GlobalTheory.LN.AmpFrames t.G t.PP.L N) {U : Z.Opens} {u : U.toScheme ⟶ M} [IsProper u] (hu : u ≫ sM = U.ι ≫ sZ)
    {tU : SAB H U.toScheme} (mU : SABMap tU t U.ι) (mM : SABMap tU tM u) : IsFinite u := by
  suffices h : ∀ V : M.affineOpens, IsFinite (u ∣_ V.1) by
    refine IsFinite.iff_isProper_and_isAffineHom.2 ⟨‹_›, ⟨fun V hV => ?_⟩⟩
    have := h ⟨V, hV⟩
    have : IsAffine V.toScheme := hV
    exact isAffine_of_isAffineHom (u ∣_ V)
  intro V
  have : IsAffine V.1.toScheme := V.2
  have ha := isAffineHom_of_isProper ((u ⁻¹ᵁ V.1).ι ≫ U.ι) (u ∣_ V.1) sZ (V.1.ι ≫ sM)
    (by rw [morphismRestrict_ι_assoc, hu, Category.assoc])
  obtain ⟨t', ⟨m'⟩⟩ := exists_pull (u ⁻¹ᵁ V.1).ι tU
  obtain ⟨tV, ⟨mV⟩⟩ := exists_pull V.1.ι tM
  obtain ⟨a, -⟩ := exists_comp m' mU rfl
  obtain ⟨b, -⟩ := exists_comp m' mM rfl
  obtain ⟨b', -⟩ := exists_cancel mV b (morphismRestrict_ι u V.1)
  obtain ⟨A', -⟩ := GlobalTheory.T.ampleDeterminantFrames_pullback_of_isAffineHom E H Z _ t t' _ a N A ha
  exact GlobalTheory.T.isFinite_of_ampleDeterminantFrames_pullback h1 h2 E H _ _ (((u ⁻¹ᵁ V.1).ι ≫ U.ι) ≫ z) t' tV (u ∣_ V.1) b' N A' hN
    (isNormalScheme_of_open ((u ⁻¹ᵁ V.1).ι ≫ U.ι) hn) inferInstance (isProper_pull b hp) ((pol_of_map b hp).1 am)
    ((pol_of_map b hp).2 kt) inferInstance

theorem isIso_restrict_of_section {U M : Scheme.{0}} [IsReduced U] (u : U ⟶ M) [IsSeparated u] (W : M.Opens)
    (j : W.toScheme ⟶ U) [IsDominant j] (h : j ≫ u = W.ι) :
    IsIso (u ∣_ W) ∧ Dense ((u ⁻¹ᵁ W : U.Opens) : Set U) := by
  have hr : Set.range j ⊆ Set.range (u ⁻¹ᵁ W).ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    show u (j w) ∈ W
    rw [← Scheme.Hom.comp_apply, h]
    exact w.2
  refine ⟨?_, j.denseRange.mono (hr.trans (Scheme.Opens.range_ι _).le)⟩
  let σ := IsOpenImmersion.lift (u ⁻¹ᵁ W).ι j hr
  have hσ : σ ≫ (u ⁻¹ᵁ W).ι = j := IsOpenImmersion.lift_fac _ _ _
  have h₁ : σ ≫ u ∣_ W = 𝟙 _ := by
    rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, reassoc_of% hσ, h, Category.id_comp]
  have : IsDominant σ := by
    constructor
    have hd := Dense.preimage j.denseRange (u ⁻¹ᵁ W).ι.isOpenEmbedding.isOpenMap
    refine hd.mono ?_
    rintro y ⟨x, hx⟩
    refine ⟨x, (u ⁻¹ᵁ W).ι.isOpenEmbedding.injective ?_⟩
    rw [← hx, ← hσ]; rfl
  refine ⟨σ, ?_, h₁⟩
  refine ext_of_isDominant_of_isSeparated (u ∣_ W) ?_ σ ?_
  · rw [Category.assoc, h₁, Category.comp_id, Category.id_comp]
  · rw [reassoc_of% h₁, Category.comp_id]

theorem normal_stalk_of_generic {O : Type} [CommRing O] [IsDomain O] {M : Scheme.{0}} (s : M ⟶ Sp O)
    (h : Smooth (pullback.snd s (spMap (algebraMap O (FractionRing O))))) (x : M) (hx : (s x).asIdeal = ⊥) :
    IsDomain (M.presheaf.stalk x) ∧ IsIntegrallyClosed (M.presheaf.stalk x) := by
  have hb : IsPreimmersion (spMap (algebraMap O (FractionRing O))) :=
    IsPreimmersion.of_isLocalization (R := CommRingCat.of O) (S := FractionRing O) (nonZeroDivisors O)
  have hbf : Flat (spMap (algebraMap O (FractionRing O))) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ (nonZeroDivisors O))
  have h1 : IsPreimmersion (pullback.fst s (spMap (algebraMap O (FractionRing O)))) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip hb
  have hx' : x ∈ Set.range (pullback.fst s (spMap (algebraMap O (FractionRing O)))) := by
    rw [Scheme.Pullback.range_fst]
    refine ⟨(⊥ : PrimeSpectrum (FractionRing O)), PrimeSpectrum.ext ?_⟩
    rw [hx]
    exact Ideal.comap_bot_of_injective (algebraMap O (FractionRing O)) (IsFractionRing.injective O _)
  obtain ⟨y, rfl⟩ := hx'
  obtain ⟨_, _⟩ := (GlobalTheory.isNormalScheme_iff _).mp (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ _ h).2.1 y
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks (pullback.fst s (spMap (algebraMap O (FractionRing O)))) y
  let e := (asIso ((pullback.fst s (spMap (algebraMap O (FractionRing O)))).stalkMap y)).commRingCatIsoToRingEquiv
  exact ⟨e.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e.symm⟩

theorem exists_isIso_restrict {U M : Scheme.{0}} (u : U ⟶ M) (T : M → Prop)
    (h : ∀ x, T x → ∃ V : M.Opens, x ∈ V ∧ IsIso (u ∣_ V)) : ∃ W : M.Opens, (∀ x, T x → x ∈ W) ∧ IsIso (u ∣_ W) := by
  let W : M.Opens := ⨆ V : {V : M.Opens // IsIso (u ∣_ V)}, V.1
  refine ⟨W, fun x hx => ?_, ?_⟩
  · obtain ⟨V, a, b⟩ := h x hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨V, b⟩, a⟩
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    (fun V : {V : M.Opens // IsIso (u ∣_ V)} => W.ι ⁻¹ᵁ V.1) ?_ fun V => ?_
  · rw [← Scheme.Hom.preimage_iSup]
    exact W.ι_preimage_self
  · have e : W.ι ''ᵁ (W.ι ⁻¹ᵁ V.1) = V.1 := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact inf_eq_right.2 (le_iSup (fun V : {V : M.Opens // IsIso (u ∣_ V)} => V.1) V)
    refine ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictRestrict u W (W.ι ⁻¹ᵁ V.1))).2 ?_
    rw [e]
    exact V.2

theorem exists_finite_map : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (MM : Scheme.{0}) (sM : MM ⟶ Sp (RZ H n N)) (tM : SAB H MM) (lev : D.La → (𝟙_ (Over MM) ⟶ tM.G)) (m : ℕ) (C : ZOn sM tM m) (U : C.Z.Opens), n.Prime → (∃ j, N = n ^ j) → 0 < m → FamCore D sM tM lev → (U : Set C.Z) = abLocus C.t.G → ∃ (u : U.toScheme ⟶ MM) (tU : SAB H U.toScheme) (mU : SABMap tU C.t U.ι) (mM : SABMap tU tM u), u ≫ sM = U.ι ≫ C.s ∧ IsFinite u ∧ Surjective u ∧ (∃ W : MM.Opens, (∀ x : MM, (sM x).asIdeal = ⊥ → x ∈ W) ∧ IsIso (u ∣_ W)) ∧ ∀ j' : C.W.toScheme ⟶ U.toScheme, j' ≫ U.ι = C.j → j' ≫ u = C.W.ι := by
  intro hE h1 h2 E _ _ _ H D n N MM sM tM lev m C U hn ⟨e, he⟩ hm F hU
  have := BaseRing.finiteType_RZ H n N
  have : IsNoetherianRing (RZ H n N) := Algebra.FiniteType.isNoetherianRing ℤ _
  have hn₀ : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne_zero
  have hun : IsUnit (n : RZ H n N) := IsUnit.of_mul_eq_one
    ⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr (Or.inl rfl))⟩ (Subtype.ext (by simp [hn₀]))
  have huN : IsUnit (N : RZ H n N) := by simpa only [he, Nat.cast_pow] using hun.pow e
  have hN : 0 < N := he ▸ pow_pos hn.pos e
  have := isProper_of_isProjOver C.proj
  obtain ⟨_, _⟩ := separated_finiteType_of_isQProjOver F.qproj
  have : IsLocallyNoetherian MM := LocallyOfFiniteType.isLocallyNoetherian sM
  have : IsLocallyNoetherian C.Z := LocallyOfFiniteType.isLocallyNoetherian C.s
  have := C.flat
  have := F.flat
  have := F.red
  have := C.j_open
  have := C.j_dom
  have hnU := isNormalScheme_of_open U.ι ((GlobalTheory.isNormalScheme_iff_pred _).mp C.normal)
  have := isReduced_of_normal hnU
  obtain ⟨tU, ⟨mU⟩⟩ := exists_pull U.ι C.t
  have hpU : IsProper tU.G.hom := by
    obtain ⟨U', hU', hP⟩ := C.good.1
    obtain rfl : U' = U := TopologicalSpace.Opens.ext (hU'.trans hU.symm)
    have i := mU.cart.1.isoIsPullback_hom_snd _ _ (isPullback_morphismRestrict C.t.G.hom U').flip
    rw [← i]
    infer_instance
  have hqU : IsQProjOver (tU.G.hom ≫ U.ι ≫ C.s) := by
    obtain ⟨k, i, _, _, hi⟩ := C.qproj
    have : IsOpenImmersion mU.φ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) mU.cart.1.flip inferInstance
    have : QuasiCompact mU.φ := MorphismProperty.of_isPullback (P := @QuasiCompact) mU.cart.1.flip inferInstance
    exact ⟨k, mU.φ ≫ i, inferInstance, inferInstance, by rw [Category.assoc, hi, mU.cart.1.w_assoc]⟩
  have hpW := isProper_pull C.m₁ F.obj.proper
  have hr : Set.range C.j ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι, hU]
    exact range_subset_abLocus_of_isProper C.t.semi C.m₂.cart.1
  let j : C.W.toScheme ⟶ U.toScheme := IsOpenImmersion.lift U.ι C.j hr
  have hj : j ≫ U.ι = C.j := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (j ≫ U.ι) := by rwa [hj]
  have : IsOpenImmersion j := IsOpenImmersion.of_comp j U.ι
  have : IsDominant j := by
    constructor
    have hd := Dense.preimage C.j.denseRange U.ι.isOpenEmbedding.isOpenMap
    refine hd.mono ?_
    rintro y ⟨x, hx⟩
    refine ⟨x, U.ι.isOpenEmbedding.injective ?_⟩
    rw [← hx, ← hj]; rfl
  obtain ⟨ν, -⟩ := exists_cancel mU C.m₂ hj
  let lW := fun a => ObjPull.secPull C.m₁.cart (lev a)
  have hlW : ∀ a, (lW a).left ≫ C.m₁.φ = C.W.ι ≫ (lev a).left := fun a => ObjPull.secPull_left _ _
  have oW : FullObj D (C.W.ι ≫ sM) C.tW lW := (GlobalTheory.T.fullLevelObject_pullback_exists_and_full E H D n N MM _ sM tM lev C.W.ι).2 C.tW C.m₁ lW hlW F.obj
  have hjs : j ≫ U.ι ≫ C.s = C.W.ι ≫ sM := by rw [reassoc_of% hj, C.j_over]
  obtain ⟨lv, o, hl⟩ := exists_full hE h1 h2 hN huN hnU (U.ι ≫ C.s) tU hpU hqU j C.tW ν lW (by rwa [hjs])
  obtain ⟨u, ⟨hu, mM, hM⟩, -⟩ := F.rep _ (U.ι ≫ C.s) tU lv inferInstance inferInstance inferInstance o
  have hju : j ≫ u = C.W.ι := by
    obtain ⟨k, hk⟩ := exists_comp ν mM rfl
    refine (F.rep _ (C.W.ι ≫ sM) C.tW lW inferInstance inferInstance inferInstance oW).unique
      ⟨by rw [Category.assoc, hu, hjs], k, fun a => ?_⟩ ⟨rfl, C.m₁, hlW⟩
    rw [hk, ← Category.assoc, hl, Category.assoc, hM, Category.assoc]
  have := isProper_of_abLocus hE C.proj F.qproj F.obj.proper hU.ge hu mU mM
  have : Flat (spMap (algebraMap ℤ (RZ H n N))) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have hf : IsFinite u := isFinite_of_isProper h1 h2 C.s sM (C.s ≫ spMap (algebraMap ℤ (RZ H n N))) ((GlobalTheory.isNormalScheme_iff_pred _).mp C.normal)
    F.obj.proper F.obj.ample F.obj.ktriv (pow_pos hm 2) C.amp hu mU mM
  obtain ⟨hi, hd⟩ := isIso_restrict_of_section u C.W j hju
  refine ⟨u, tU, mU, mM, hu, hf, ⟨?_⟩, exists_isIso_restrict u _ fun x hx => ?_, fun j' hj' => ?_⟩
  · have hd' : Dense (Set.range u) := C.dense.mono fun w hw =>
      ⟨j ⟨w, hw⟩, congrArg (fun f => f (⟨w, hw⟩ : C.W.toScheme)) hju⟩
    rw [← Set.range_eq_univ, ← u.isClosedMap.isClosed_range.closure_eq]
    exact hd'.closure_eq
  · obtain ⟨a, b⟩ := normal_stalk_of_generic sM F.gen x hx
    exact GlobalTheory.T.isIso_near_normal_point_of_finite_birational _ MM u C.W hf inferInstance hi C.dense hd x a b
  · obtain rfl : j' = j := by rw [← cancel_mono U.ι, hj, hj']
    exact hju

end GlobalTheory.AbelianLocusNormalisation
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianLocusOpenFamilyOverLevelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_locus_open_family_over_level : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (MM : Scheme.{0}) (sM : MM ⟶ Sp (RZ H n N)) (tM : SAB H MM) (lev : D.La → (𝟙_ (Over MM) ⟶ tM.G)) (m : ℕ) (C : ZOn sM tM m) (U : C.Z.Opens), n.Prime → (∃ j, N = n ^ j) → 0 < m → FamCore D sM tM lev → (U : Set C.Z) = abLocus C.t.G → ∃ (u : U.toScheme ⟶ MM) (tU : SAB H U.toScheme) (mU : SABMap tU C.t U.ι) (mM : SABMap tU tM u), u ≫ sM = U.ι ≫ C.s ∧ IsFinite u ∧ Surjective u ∧ (∃ W : MM.Opens, (∀ x : MM, (sM x).asIdeal = ⊥ → x ∈ W) ∧ IsIso (u ∣_ W)) ∧ ∀ j' : C.W.toScheme ⟶ U.toScheme, j' ≫ U.ι = C.j → j' ≫ u = C.W.ι := by
  first | exact @GlobalTheory.AbelianLocusNormalisation.exists_finite_map | exact GlobalTheory.AbelianLocusNormalisation.exists_finite_map | (intros; apply GlobalTheory.AbelianLocusNormalisation.exists_finite_map <;> assumption)
end
