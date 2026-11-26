module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompLinearEquivIntertwining
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKernelOfCubWeilOrthogonal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePrincMulUnit

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLineBundleIsoOnOpenOfRestrictionIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLineBundleIsoOnOpenOfRestrictionIso
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem gm_eq_map_stalk {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)ˣ) :
    gm f y U a = Units.map (f.stalkMap y).hom.toMonoidHom (gm (𝟙 X) (f y) U a) := by
  apply Units.ext
  rw [gm_val f y U h, Units.coe_map, gm_val _ (f y) U h, ← Scheme.Hom.germ_stalkMap_apply]
  rfl

theorem isoOn_of_lbIso (X : Scheme.{0}) (W : X.Opens) (L M : LB X) (h : LBIso (L.pull W.ι) (M.pull W.ι)) :
    ∃ w : Cmp W L M, IsoOn W L M w := by
  obtain ⟨s, hs⟩ := h
  have hle : ∀ (a : L.ι) (b : M.ι), W ⊓ (L.U a ⊓ M.U b) ≤
      W.ι ''ᵁ ((M.pull W.ι).U (fun _ => b) ⊓ (L.pull W.ι).U (fun _ => a)) := by
    intro a b x hx
    obtain ⟨y, rfl⟩ : ∃ y : W.toScheme, W.ι y = x := ⟨⟨x, hx.1⟩, rfl⟩
    exact W.ι.apply_mem_image_iff.2 ⟨mem_pull.2 hx.2.2, mem_pull.2 hx.2.1⟩
  refine ⟨fun a b => (res (hle a b) (GlobalTheory.GlueLineBundle.imU W.ι _ (s.s (fun _ => b, fun _ => a))))⁻¹, ?_⟩
  intro x hx a a' b b' ha ha' hb hb'
  obtain ⟨y, rfl⟩ : ∃ y : W.toScheme, W.ι y = x := ⟨⟨x, hx⟩, rfl⟩
  have E : ∀ (a : L.ι) (b : M.ι), W.ι y ∈ L.U a → W.ι y ∈ M.U b →
      gm W.ι y (W ⊓ (L.U a ⊓ M.U b))
        ((res (hle a b) (GlobalTheory.GlueLineBundle.imU W.ι _ (s.s (fun _ => b, fun _ => a))))⁻¹) =
      (gm (𝟙 _) y _ (s.s (fun _ => b, fun _ => a)))⁻¹ := by
    intro a b ha hb
    have hm : W.ι y ∈ W ⊓ (L.U a ⊓ M.U b) := ⟨hx, ha, hb⟩
    have hv : (𝟙 W.toScheme) y ∈ (M.pull W.ι).U (fun _ => b) ⊓ (L.pull W.ι).U (fun _ => a) :=
      ⟨mem_pull.2 hb, mem_pull.2 ha⟩
    have e := GlobalTheory.GlueLineBundle.gm_imU W.ι (𝟙 _) y _ hv (s.s (fun _ => b, fun _ => a))
    rw [Category.id_comp] at e
    rw [map_inv, gm_res W.ι y (hle a b) hm, e]
    rfl
  have EL : ∀ (a a' : L.ι), W.ι y ∈ L.U a → W.ι y ∈ L.U a' →
      gm W.ι y (L.U a ⊓ L.U a') (L.g a a') = gm (𝟙 _) y _ ((L.pull W.ι).g (fun _ => a) (fun _ => a')) := by
    intro a a' ha ha'
    have e := gm_pull_g L W.ι (𝟙 _) y (fun _ => a) (fun _ => a') (mem_pull.2 ha) (mem_pull.2 ha')
    rw [Category.id_comp] at e
    exact e.symm
  have EM : ∀ (b b' : M.ι), W.ι y ∈ M.U b → W.ι y ∈ M.U b' →
      gm W.ι y (M.U b ⊓ M.U b') (M.g b b') = gm (𝟙 _) y _ ((M.pull W.ι).g (fun _ => b) (fun _ => b')) := by
    intro b b' hb hb'
    have e := gm_pull_g M W.ι (𝟙 _) y (fun _ => b) (fun _ => b') (mem_pull.2 hb) (mem_pull.2 hb')
    rw [Category.id_comp] at e
    exact e.symm
  have hp : y ∈ (LB.div (M.pull W.ι) (L.pull W.ι)).U (fun _ => b, fun _ => a) := ⟨mem_pull.2 hb, mem_pull.2 ha⟩
  have hq : y ∈ (LB.div (M.pull W.ι) (L.pull W.ι)).U (fun _ => b', fun _ => a') := ⟨mem_pull.2 hb', mem_pull.2 ha'⟩
  have G := (isGen_iff_germ s).1 hs y _ _ hp hq
  rw [gm_div' (M.pull W.ι) (L.pull W.ι) (𝟙 _) y _ _ hp hq] at G
  have alg : ∀ {Gp : Type} [CommGroup Gp] (S Mg large₂ S' : Gp), S = Mg * large₂⁻¹ * S' → S⁻¹ * Mg = large₂ * S'⁻¹ := by
    intro Gp _ S Mg large₂ S' e
    rw [e, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, _root_.mul_assoc, _root_.mul_assoc, inv_mul_cancel, _root_.mul_one]
    exact _root_.mul_comm _ _
  have key : gm W.ι y (W ⊓ (L.U a ⊓ M.U b))
        ((res (hle a b) (GlobalTheory.GlueLineBundle.imU W.ι _ (s.s (fun _ => b, fun _ => a))))⁻¹) *
        gm W.ι y (M.U b ⊓ M.U b') (M.g b b') =
      gm W.ι y (L.U a ⊓ L.U a') (L.g a a') * gm W.ι y (W ⊓ (L.U a' ⊓ M.U b'))
        ((res (hle a' b') (GlobalTheory.GlueLineBundle.imU W.ι _ (s.s (fun _ => b', fun _ => a'))))⁻¹) := by
    rw [E a b ha hb, E a' b' ha' hb', EL a a' ha ha', EM b b' hb hb']
    exact alg _ _ _ _ G
  have hinj : Function.Injective (Units.map (W.ι.stalkMap y).hom.toMonoidHom) := fun u v e =>
    Units.ext ((ConcreteCategory.bijective_of_isIso (W.ι.stalkMap y)).1 (congrArg Units.val e))
  apply hinj
  rw [map_mul, map_mul, ← gm_eq_map_stalk W.ι y _ (show W.ι y ∈ W ⊓ (L.U a ⊓ M.U b) from ⟨hx, ha, hb⟩),
    ← gm_eq_map_stalk W.ι y _ (show W.ι y ∈ M.U b ⊓ M.U b' from ⟨hb, hb'⟩),
    ← gm_eq_map_stalk W.ι y _ (show W.ι y ∈ L.U a ⊓ L.U a' from ⟨ha, ha'⟩),
    ← gm_eq_map_stalk W.ι y _ (show W.ι y ∈ W ⊓ (L.U a' ⊓ M.U b') from ⟨hx, ha', hb'⟩)]
  exact key

end GlobalTheory.PicGlue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLineBundleIsoOnOpenOfRestrictionIsoStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isLineBundleIsoOnOpen_of_restriction_iso : ∀ (X : Scheme.{0}) (W : X.Opens) (L M : LB X), LBIso (L.pull W.ι) (M.pull W.ι) → ∃ w : Cmp W L M, IsoOn W L M w := by
  first | exact @GlobalTheory.PicGlue.isoOn_of_lbIso | exact GlobalTheory.PicGlue.isoOn_of_lbIso | (intros; apply GlobalTheory.PicGlue.isoOn_of_lbIso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCompactCharacterVanishing
open MeasureTheory Matrix

namespace GlobalTheory

theorem typeFunction_unip_add {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    {a b : ℕ} (e : ι ≃ Fin a ⊕ Fin b) (u : (Fin a → Fin b → K) → GL ι K)
    (hu : ∀ X, (u X : Matrix ι ι K) =
      Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1))
    (X Y : Fin a → Fin b → K) : u (Y + X) = u X * u Y := by
  apply Units.ext
  rw [Units.val_mul, hu, hu, hu]
  simp only [Matrix.reindex_apply, Equiv.symm_symm]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp [Matrix.of_add_of]

theorem typeFunction_constantTerm_eq_zero :
  ∀ (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (ι : Type) [Fintype ι] [DecidableEq ι] (J : Subgroup (GL ι K)), IsOpen (J : Set (GL ι K)) → IsCompact (J : Set (GL ι K)) →
  ∀ χ : J →* ℂˣ, IsOpen (χ.ker : Set J) →
  (∀ (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b), 0 < a → 0 < b → ∀ u : (Fin a → Fin b → K) → GL ι K,
      (∀ X, (u X : Matrix ι ι K) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) →
      ∀ h : GL ι K, ∃ X, ∃ hX : h⁻¹ * u X * h ∈ J, χ ⟨_, hX⟩ ≠ 1) →
  ∀ f : GL ι K → ℂ, (∀ g (hg : g ∈ J), f g = (((χ ⟨g, hg⟩)⁻¹ : ℂˣ) : ℂ)) → (∀ g, g ∉ J → f g = 0) →
  IsLocallyConstant f ∧ HasCompactSupport f ∧
  (∀ x ∈ (χ.ker.map J.subtype), ∀ y ∈ (χ.ker.map J.subtype), ∀ g, f (x * g * y) = f g) ∧
  (∀ (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b), 0 < a → 0 < b → ∀ (μ : Measure (Fin a → Fin b → K)), μ.IsAddHaarMeasure →
    ∀ u : (Fin a → Fin b → K) → GL ι K,
      (∀ X, (u X : Matrix ι ι K) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) →
      ∀ g h : GL ι K, ∫ X, f (g * (h⁻¹ * u X * h)) ∂μ = 0) := by
  intro K _ _ _ _ _ _ ι _ _ J hJo hJc χ hχ hnt f hf1 hf0
  have hR : ∀ g j (hj : j ∈ J), f (g * j) = f g * (((χ ⟨j, hj⟩)⁻¹ : ℂˣ) : ℂ) := by
    intro g j hj
    by_cases hg : g ∈ J
    · rw [hf1 _ (J.mul_mem hg hj), hf1 g hg]
      have : (⟨g * j, J.mul_mem hg hj⟩ : J) = ⟨g, hg⟩ * ⟨j, hj⟩ := rfl
      rw [this, map_mul, mul_inv, Units.val_mul]
    · rw [hf0 g hg, hf0 _ (fun h => hg ((J.mul_mem_cancel_right hj).1 h)), zero_mul]
  have hL : ∀ g j (hj : j ∈ J), f (j * g) = (((χ ⟨j, hj⟩)⁻¹ : ℂˣ) : ℂ) * f g := by
    intro g j hj
    by_cases hg : g ∈ J
    · rw [hf1 _ (J.mul_mem hj hg), hf1 g hg]
      have : (⟨j * g, J.mul_mem hj hg⟩ : J) = ⟨j, hj⟩ * ⟨g, hg⟩ := rfl
      rw [this, map_mul, mul_inv, Units.val_mul]
    · rw [hf0 g hg, hf0 _ (fun h => hg ((J.mul_mem_cancel_left hj).1 h)), mul_zero]
  have hRk : ∀ y ∈ (χ.ker.map J.subtype), ∀ g, f (g * y) = f g := by
    rintro _ ⟨y, hy, rfl⟩ g
    have h1 : χ y = 1 := hy
    have := hR g y y.2
    simp only [Subtype.coe_eta, h1, inv_one, Units.val_one, mul_one] at this
    exact this
  have hLk : ∀ y ∈ (χ.ker.map J.subtype), ∀ g, f (y * g) = f g := by
    rintro _ ⟨y, hy, rfl⟩ g
    have h1 : χ y = 1 := hy
    have := hL g y y.2
    simp only [Subtype.coe_eta, h1, inv_one, Units.val_one, one_mul] at this
    exact this
  have hNo : IsOpen ((χ.ker.map J.subtype : Subgroup (GL ι K)) : Set (GL ι K)) := by
    rw [Subgroup.coe_map]
    exact hJo.isOpenMap_subtype_val _ hχ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro g
    refine ⟨(fun x => g⁻¹ * x) ⁻¹' ((χ.ker.map J.subtype : Subgroup (GL ι K)) : Set (GL ι K)),
      hNo.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
    · simp only [Set.mem_preimage, inv_mul_cancel, SetLike.mem_coe]
      exact Subgroup.one_mem _
    · intro x hx
      have := hRk _ hx g
      rwa [mul_inv_cancel_left] at this
  · exact HasCompactSupport.intro' hJc (J.isClosed_of_isOpen hJo) (fun g hg => hf0 g hg)
  · intro x hx y hy g
    rw [hRk y hy, hLk x hx]
  · intro a b e ha hb μ hμ u hu g h
    obtain ⟨Y, hY, hne⟩ := hnt a b e ha hb u hu h
    have key : ∀ X, f (g * (h⁻¹ * u (Y + X) * h)) =
        f (g * (h⁻¹ * u X * h)) * (((χ ⟨_, hY⟩)⁻¹ : ℂˣ) : ℂ) := by
      intro X
      rw [← hR _ _ hY, typeFunction_unip_add e u hu]
      congr 1
      group
    have h1 := integral_add_left_eq_self (μ := μ) (fun X => f (g * (h⁻¹ * u X * h))) Y
    simp only [key] at h1
    rw [integral_mul_const] at h1
    have hc : (((χ ⟨_, hY⟩)⁻¹ : ℂˣ) : ℂ) ≠ 1 := by
      intro hc
      exact hne (inv_eq_one.1 (Units.val_eq_one.1 hc))
    by_contra hI
    exact hc (mul_left_cancel₀ hI (h1.trans (mul_one _).symm))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoNormalisedAlongSectionRetract
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoNormalisedAlongSectionRetract
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PicGlue

theorem germ_pull_eq_stalkMap {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)ˣ) :
    gm f y U a = Units.map (f.stalkMap y).hom.toMonoidHom (gm (𝟙 X) (f y) U a) := by
  apply Units.ext
  rw [Units.coe_map, gm_val f y U h, gm_val (𝟙 X) (f y) U h]
  exact (Scheme.Hom.germ_stalkMap_apply f U y h _).symm

theorem retract_section_apply {X Y : Scheme.{0}} (p : X ⟶ Y) (e : Y ⟶ X) (hep : e ≫ p = 𝟙 Y) (y : Y) : p (e y) = y := by
  have := congrArg (fun f : Y ⟶ Y ↦ f y) hep
  simpa using this

theorem norm_glue_comm {G : Type} [CommGroup G] (A B F G' R R' : G) (k : A * G' = F * B) :
    A * (G' * R') * (F * R)⁻¹ = B * R' * R⁻¹ := by
  rw [← _root_.mul_assoc, k, mul_inv]
  simp only [_root_.mul_assoc]
  rw [mul_left_comm F, mul_left_comm F, mul_inv_cancel_left]

theorem norm_match_comm {G : Type} [CommGroup G] (A S R R' : G) (h : S = A * R' * R⁻¹) :
    A * S⁻¹ * R' = R := by
  rw [h]; simp only [mul_inv]; simp [mul_comm, mul_left_comm, _root_.mul_assoc]

theorem exists_norm (X Y : Scheme.{0}) (p : X ⟶ Y) (e : Y ⟶ X) (hep : e ≫ p = 𝟙 Y) (V : Y.Opens)
    (W₁ W₂ : X.Opens) (L M : LB X) (w : Cmp (p ⁻¹ᵁ V) L M) (r : RigD e L) (r' : RigD e M)
    (hL : IsOn W₁ L) (hM : IsOn W₂ M) (h₁ : p ⁻¹ᵁ V ≤ W₁) (h₂ : p ⁻¹ᵁ V ≤ W₂)
    (hw : IsoOn (p ⁻¹ᵁ V) L M w) (hr : RigOn e L r) (hr' : RigOn e M r') :
    ∃ w' : Cmp (p ⁻¹ᵁ V) L M, IsoOn (p ⁻¹ᵁ V) L M w' ∧ Norm e (p ⁻¹ᵁ V) L M w' r r' := by
  have hpt := retract_section_apply p e hep
  let O : L.ι × M.ι → Y.Opens := fun i ↦ e ⁻¹ᵁ (p ⁻¹ᵁ V ⊓ (L.U i.1 ⊓ M.U i.2))
  have hOV : ∀ i, O i ≤ V := fun i y hy ↦ by
    have : p (e y) ∈ V := hy.1
    rwa [hpt] at this
  have hOa : ∀ i, O i ≤ e ⁻¹ᵁ L.U i.1 := fun i y hy ↦ hy.2.1
  have hOb : ∀ i, O i ≤ e ⁻¹ᵁ M.U i.2 := fun i y hy ↦ hy.2.2
  have hcov : V ≤ iSup O := fun y hy ↦ by
    have hx : e y ∈ p ⁻¹ᵁ V := show p (e y) ∈ V by rwa [hpt]
    obtain ⟨a, ha⟩ := hL.cov _ (h₁ hx)
    obtain ⟨b, hb⟩ := hM.cov _ (h₂ hx)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(a, b), ⟨hx, ha, hb⟩⟩
  let u : ∀ i, Γ(Y, O i)ˣ := fun i ↦
    pullU e _ (w i.1 i.2) * res (hOb i) (r' i.2) * (res (hOa i) (r i.1))⁻¹
  have hu : ∀ i, ∀ y ∈ O i, gm (𝟙 Y) y (O i) (u i) =
      gm e y _ (w i.1 i.2) * gm (𝟙 Y) y _ (r' i.2) * (gm (𝟙 Y) y _ (r i.1))⁻¹ := by
    intro i y hy
    simp only [u, map_mul, map_inv]
    rw [gm_res (𝟙 Y) y (hOb i) hy, gm_res (𝟙 Y) y (hOa i) hy, gm_pull (𝟙 Y) e y _ hy, Category.id_comp]
  obtain ⟨s, hs⟩ := glue_unit V O hOV hcov u (by
    intro i j y hy
    rw [hu i y hy.1, hu j y hy.2]
    obtain ⟨⟨hV, ha, hb⟩, -, ha', hb'⟩ := hy
    have k := congrArg (Units.map (e.stalkMap y).hom.toMonoidHom) (hw (e y) hV i.1 j.1 i.2 j.2 ha ha' hb hb')
    simp only [map_mul, ← germ_pull_eq_stalkMap] at k
    rw [← germ_pull_eq_stalkMap e y (p ⁻¹ᵁ V ⊓ (L.U i.1 ⊓ M.U i.2)) ⟨hV, ha, hb⟩,
      ← germ_pull_eq_stalkMap e y (M.U i.2 ⊓ M.U j.2) ⟨hb, hb'⟩,
      ← germ_pull_eq_stalkMap e y (L.U i.1 ⊓ L.U j.1) ⟨ha, ha'⟩,
      ← germ_pull_eq_stalkMap e y (p ⁻¹ᵁ V ⊓ (L.U j.1 ⊓ M.U j.2)) ⟨hV, ha', hb'⟩] at k
    rw [hr y i.1 j.1 ha ha', hr' y i.2 j.2 hb hb']
    exact norm_glue_comm _ _ _ _ _ _ k)
  have hle : ∀ (a : L.ι) (b : M.ι), p ⁻¹ᵁ V ⊓ (L.U a ⊓ M.U b) ≤ p ⁻¹ᵁ V := fun _ _ ↦ inf_le_left
  refine ⟨fun a b ↦ w a b * (res (hle a b) (pullU p V s))⁻¹, ?_, ?_⟩
  · intro x hx a a' b b' ha ha' hb hb'
    simp only [map_mul, map_inv]
    rw [gm_res (𝟙 X) x (hle a b) ⟨hx, ha, hb⟩, gm_res (𝟙 X) x (hle a' b') ⟨hx, ha', hb'⟩]
    have k := hw x hx a a' b b' ha ha' hb hb'
    rw [mul_right_comm, k, _root_.mul_assoc]
  · intro y a b hV ha hb
    simp only [map_mul, map_inv]
    have hy : y ∈ O (a, b) := ⟨hV, ha, hb⟩
    rw [gm_res e y (hle a b) ⟨hV, ha, hb⟩, gm_pull e p y V hV, hep, ← gm_res (𝟙 Y) y (hOV (a, b)) hy, hs,
      hu (a, b) y hy]
    exact norm_match_comm _ _ _ _ rfl

end GlobalTheory.PicGlue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoNormalisedAlongSectionRetractStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundleIso_normalisedAlongSection_retraction : ∀ (X Y : Scheme.{0}) (p : X ⟶ Y) (e : Y ⟶ X), e ≫ p = 𝟙 Y → ∀ (V : Y.Opens) (W₁ W₂ : X.Opens) (L M : LB X) (w : Cmp (p ⁻¹ᵁ V) L M) (r : RigD e L) (r' : RigD e M), IsOn W₁ L → IsOn W₂ M → p ⁻¹ᵁ V ≤ W₁ → p ⁻¹ᵁ V ≤ W₂ → IsoOn (p ⁻¹ᵁ V) L M w → RigOn e L r → RigOn e M r' → ∃ w' : Cmp (p ⁻¹ᵁ V) L M, IsoOn (p ⁻¹ᵁ V) L M w' ∧ Norm e (p ⁻¹ᵁ V) L M w' r r' := by
  first | exact @GlobalTheory.PicGlue.exists_norm | exact GlobalTheory.PicGlue.exists_norm | (intros; apply GlobalTheory.PicGlue.exists_norm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAutomorphicFormFixedOfLocallyIntegralFixed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAutomorphicFormFixedOfLocallyIntegralFixed
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix Filter Topology

noncomputable section

namespace GlobalTheory.CuspRep.TailFix

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem entry_int {w : HeightOneSpectrum (𝓞 E)} {g : GL (Fin a) (w.adicCompletion E)} (hg : g ∈ KGL w (n := a))
    (i j : Fin a) : g i j ∈ w.adicCompletionIntegers E := by
  obtain ⟨h, rfl⟩ := hg
  exact (h i j).2

theorem tendsto_of_loc {α : Type} {l : Filter α} {f : α → Af E} {x : Af E}
    (hx : ∀ v, pLoc E v x ∈ v.adicCompletionIntegers E) (hf : ∀ b v, pLoc E v (f b) ∈ v.adicCompletionIntegers E)
    (h : ∀ v, ∀ᶠ b in l, pLoc E v (f b) = pLoc E v x) : Tendsto f l (𝓝 x) := by
  let s := RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
    (fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) cofinite
  have hs : Continuous s := RestrictedProduct.isEmbedding_structureMap.continuous
  let lift : ∀ y : Af E, (∀ v, pLoc E v y ∈ v.adicCompletionIntegers E) →
      ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletionIntegers E : Set (v.adicCompletion E)) :=
    fun y hy v => ⟨pLoc E v y, hy v⟩
  have hl : ∀ y hy, s (lift y hy) = y := fun y hy => FiniteAdeleRing.ext _ fun v => rfl
  have h1 : Tendsto (fun b => lift (f b) (hf b)) l (𝓝 (lift x hx)) := tendsto_pi_nhds.2 fun v =>
    tendsto_const_nhds.congr' <| (h v).mono fun b hb => Subtype.ext hb.symm
  have h2 := (hs.tendsto _).comp h1
  rw [hl] at h2
  exact h2.congr fun b => hl _ _

theorem exists_tail {U : Set (GL (Fin a) (Af E))} (hU : U ∈ 𝓝 (1 : GL (Fin a) (Af E))) :
    ∃ F : Finset (HeightOneSpectrum (𝓞 E)), ∀ r : GL (Fin a) (Af E),
      (∀ v, GeneralLinearGroup.map (pLoc E v) r ∈ KGL v (n := a)) →
      (∀ v ∈ F, GeneralLinearGroup.map (pLoc E v) r = 1) → r ∈ U := by
  classical
  by_contra hn
  push_neg at hn
  choose r hr1 hr2 hrU using hn
  have ent : ∀ q : Finset (HeightOneSpectrum (𝓞 E)) → GL (Fin a) (Af E),
      (∀ F v, GeneralLinearGroup.map (pLoc E v) (q F) ∈ KGL v (n := a)) →
      (∀ F, ∀ v ∈ F, GeneralLinearGroup.map (pLoc E v) (q F) = 1) →
      Tendsto (fun F => (q F).val) atTop (𝓝 1) := fun q hq1 hq2 =>
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j =>
      tendsto_of_loc (fun v => by rw [Matrix.one_apply]; split_ifs <;> simp)
        (fun F v => entry_int (hq1 F v) i j) fun v => by
        filter_upwards [eventually_ge_atTop {v}] with F hF
        have e := hq2 F v (hF (Finset.mem_singleton_self v))
        rw [← map_one (GeneralLinearGroup.map (pLoc E v))] at e
        exact congrArg (fun x : GL (Fin a) (v.adicCompletion E) => x i j) e
  have ht : Tendsto r atTop (𝓝 1) := by
    rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    exact (ent r hr1 hr2).prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp
      (ent (fun F => (r F)⁻¹) (fun F v => by rw [map_inv]; exact inv_mem (hr1 F v))
        (fun F v hv => by rw [map_inv, hr2 F v hv, inv_one])))
  obtain ⟨F, hF⟩ := (ht.eventually hU).exists
  exact hrU F hF

end GlobalTheory.CuspRep.TailFix


open GlobalTheory.CuspRep.TailFix in
theorem GlobalTheory.CuspRep.fixed_of_locFixed : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (φ : Sm E a), IsAutForm φ → ∀ S : Finset (HeightOneSpectrum (𝓞 E)),
    (∀ w ∉ S, ∀ k ∈ KGL w (n := a), act (.fin (locGL E a w k)) φ = φ) → ∀ k : GL (Fin a) (Af E),
    (∀ w ∉ S, GeneralLinearGroup.map (pLoc E w) k ∈ KGL w (n := a)) →
    (∀ w ∈ S, GeneralLinearGroup.map (pLoc E w) k = 1) → act (.fin k) φ = φ := by
  classical
  intro E _ _ _ a φ hφ S hS k hk1 hk2
  have hU : {x : GL (Fin a) (Af E) | finRep E a x φ = φ} ∈ 𝓝 (1 : GL (Fin a) (Af E)) :=
    hφ.level.mem_nhds (by simp)
  obtain ⟨F, hF⟩ := exists_tail hU
  have key : ∀ T : Finset (HeightOneSpectrum (𝓞 E)), ∀ k : GL (Fin a) (Af E),
      (∀ w ∉ S, GeneralLinearGroup.map (pLoc E w) k ∈ KGL w (n := a)) →
      (∀ w ∈ S, GeneralLinearGroup.map (pLoc E w) k = 1) →
      (∀ w ∈ F, w ∉ T → GeneralLinearGroup.map (pLoc E w) k = 1) → finRep E a k φ = φ := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro k h1 h2 h3
      refine hF k (fun v => ?_) (fun v hv => h3 v hv (by simp))
      by_cases hv : v ∈ S
      · rw [h2 v hv]; exact one_mem _
      · exact h1 v hv
    | insert w T hw ih =>
      intro k h1 h2 h3
      obtain ⟨g, hg⟩ : ∃ g, g = locGL E a w (GeneralLinearGroup.map (pLoc E w) k) := ⟨_, rfl⟩
      have hgH : finRep E a g φ = φ := by
        by_cases hwS : w ∈ S
        · rw [hg, h2 w hwS, map_one, map_one]; rfl
        · rw [hg]; exact hS w hwS _ (h1 w hwS)
      have e : ∀ v, GeneralLinearGroup.map (pLoc E v) (g⁻¹ * k) =
          if v = w then 1 else GeneralLinearGroup.map (pLoc E v) k := fun v => by
        rw [map_mul, map_inv]
        split_ifs with hv
        · subst hv; rw [hg, pLoc_locGL, inv_mul_cancel]
        · rw [hg, pLoc_locGL_of_ne hv, inv_one, one_mul]
      have hk' : finRep E a (g⁻¹ * k) φ = φ := by
        refine ih _ (fun v hv => ?_) (fun v hv => ?_) (fun v hv hvT => ?_)
        · rw [e]; split_ifs
          · exact one_mem _
          · exact h1 v hv
        · rw [e]; split_ifs
          · rfl
          · exact h2 v hv
        · rw [e]; split_ifs with h
          · rfl
          · exact h3 v hv (by simp [h, hvT])
      calc finRep E a k φ = finRep E a (g * (g⁻¹ * k)) φ := by rw [mul_inv_cancel_left]
        _ = φ := by rw [map_mul, Module.End.mul_apply, hk', hgH]
  exact key F k hk1 hk2 (fun w hw hwF => absurd hw hwF)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAutomorphicFormFixedOfLocallyIntegralFixedStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothAutomorphicForm_fixed_of_locally_integral_fixed : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsAutForm φ → ∀ S : Finset (HeightOneSpectrum (𝓞 E)), (∀ w ∉ S, ∀ k ∈ KGL w (n := a), act (.fin (locGL E a w k)) φ = φ) → ∀ k : GL (Fin a) (Af E), (∀ w ∉ S, GeneralLinearGroup.map (pLoc E w) k ∈ KGL w (n := a)) → (∀ w ∈ S, GeneralLinearGroup.map (pLoc E w) k = 1) → act (.fin k) φ = φ := by
  first | exact @GlobalTheory.CuspRep.fixed_of_locFixed | exact GlobalTheory.CuspRep.fixed_of_locFixed | (intros; apply GlobalTheory.CuspRep.fixed_of_locFixed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomCharacterEndOfTorusExtensionAction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsBisAltTail
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusEndChar

theorem main : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G] (E : TorusExtension G) (f : G ⟶ G), IsMonHom f → letI := E.addCommGroup; ∃! ρ : E.X →+ E.X, ∃ τ : splitTorus (Sp k) E.X ⟶ splitTorus (Sp k) E.X, τ ≫ E.i = E.i ≫ f ∧ ∀ χ, chV τ χ = charUnit (Sp k) E.X (ρ χ) := by
  intro k _ G _ _ E f hf
  letI := E.addCommGroup
  haveI := E.free
  haveI := E.finite
  letI := E.grpB
  haveI : IsMonHom E.q := E.q_hom
  haveI : IsMonHom E.i := E.i_hom
  haveI : IsProper E.B.hom := E.isAbelian.proper
  haveI : ConnectedSpace (Sp k) := by
    have : PreconnectedSpace (PrimeSpectrum k) := by
      refine ⟨isPreconnected_of_forall (IsLocalRing.closedPoint k) fun y _ =>
        ⟨closure {y}, Set.subset_univ _, ?_, subset_closure rfl, isPreconnected_singleton.closure⟩⟩
      exact (IsLocalRing.specializes_closedPoint y).mem_closure
    exact (⟨inferInstance⟩ : ConnectedSpace (PrimeSpectrum k))
  have hk : E.i ≫ f ≫ E.q = toUnit _ ≫ η[E.B] :=
    splitTorus_hom_proper_trivial_local k E.X E.B (E.i ≫ f ≫ E.q) inferInstance
  let τ : splitTorus (Sp k) E.X ⟶ splitTorus (Sp k) E.X :=
    E.isKernel.lift (E.i ≫ f) (toUnit _) (by rw [Category.assoc, hk])
  have hτ : τ ≫ E.i = E.i ≫ f := E.isKernel.lift_fst _ _ _
  have hmono : Mono E.i := E.isKernel.mono_fst_of_mono
  have hτm : IsMonHom τ := by
    constructor
    · rw [← cancel_mono E.i, Category.assoc, hτ, IsMonHom.one_hom_assoc, IsMonHom.one_hom, IsMonHom.one_hom]
    · rw [← cancel_mono E.i, Category.assoc, Category.assoc, hτ, IsMonHom.mul_hom_assoc (f := E.i),
        IsMonHom.mul_hom (f := f), IsMonHom.mul_hom (f := E.i), tensorHom_comp_tensorHom_assoc,
        tensorHom_comp_tensorHom_assoc, hτ]
  obtain ⟨ρ, hρ⟩ := SplitTorusHom.exists_addMonoidHom (S := Sp k) τ
  refine ⟨ρ, ⟨τ, hτ, fun χ => Units.ext ?_⟩, ?_⟩
  · rw [chV_val, hρ]
  · rintro ρ' ⟨τ', hτ', hρ'⟩
    have hττ : τ' = τ := by rw [← cancel_mono E.i, hτ', hτ]
    subst hττ
    ext χ
    apply SplitTorusHom.charUnit_injective (S := Sp k)
    rw [← hρ', chV_val, hρ]

end GlobalTheory.TorusEndChar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomCharacterEndOfTorusExtensionAction
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory
namespace TorusActRing

theorem chV_id_eq {k : Type} [Field k] (X : Type) [AddCommGroup X] (χ : X) :
    chV (𝟙 (splitTorus (Sp k) X)) χ = charUnit (Sp k) X χ := by
  ext1
  rw [chV_val]
  simp

theorem charUnit_add' {k : Type} [Field k] (X : Type) [AddCommGroup X] (χ ψ : X) :
    charUnit (Sp k) X (χ + ψ) = charUnit (Sp k) X χ * charUnit (Sp k) X ψ := by
  rw [← chV_id_eq, ← chV_id_eq, ← chV_id_eq, chV_add]

end TorusActRing

theorem ringHom_charEnd_of_torusExtension : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G] (E : TorusExtension G) (O : Type) [Ring O] (act : O → (G ⟶ G)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 G → (∀ a b, act (a * b) = act a ≫ act b) → (∀ a b, act (a + b) = act a * act b) → letI := E.addCommGroup; ∃ ρ : O →+* Module.End ℤ E.X, ∀ a, ∃ τ : splitTorus (Sp k) E.X ⟶ splitTorus (Sp k) E.X, τ ≫ E.i = E.i ≫ act a ∧ ∀ χ, chV τ χ = charUnit (Sp k) E.X (ρ a χ) := by
  intro k _ G _ _ E O _ act hmon h1 hmul hadd
  letI := E.addCommGroup
  have hex := fun a => GlobalTheory.TorusEndChar.main k G E (act a) (hmon a)
  choose ρ₀ hρ₀ using fun a => (hex a).exists
  have uniq : ∀ a (σ : E.X →+ E.X) (τ : splitTorus (Sp k) E.X ⟶ splitTorus (Sp k) E.X),
      τ ≫ E.i = E.i ≫ act a → (∀ χ, chV τ χ = charUnit (Sp k) E.X (σ χ)) → σ = ρ₀ a :=
    fun a σ τ e₁ e₂ => (hex a).unique ⟨τ, e₁, e₂⟩ (hρ₀ a)
  have compχ : ∀ (σ : E.X →+ E.X) (τ : splitTorus (Sp k) E.X ⟶ splitTorus (Sp k) E.X),
      (∀ χ, chV τ χ = charUnit (Sp k) E.X (σ χ)) → ∀ (Z : Over (Sp k)) (s : Z ⟶ splitTorus (Sp k) E.X) χ,
      chV (s ≫ τ) χ = chV s (σ χ) :=
    fun σ τ hτ Z s χ => ((splitTorus_map_of_charHom (Sp k) E.X E.X σ).2 τ hτ).2.2 Z s χ
  have one : ρ₀ 1 = AddMonoidHom.id _ := by
    refine (uniq 1 (AddMonoidHom.id _) (𝟙 _) ?_ (fun χ => ?_)).symm
    swap
    · rw [AddMonoidHom.id_apply]; exact TorusActRing.chV_id_eq E.X χ
    rw [h1, Category.id_comp, Category.comp_id]
  have mul : ∀ a b, ρ₀ (a * b) = (ρ₀ a).comp (ρ₀ b) := by
    intro a b
    obtain ⟨τa, ha1, ha2⟩ := hρ₀ a
    obtain ⟨τb, hb1, hb2⟩ := hρ₀ b
    refine (uniq (a * b) _ (τa ≫ τb) ?_ ?_).symm
    · rw [Category.assoc, hb1, ← Category.assoc, ha1, Category.assoc, hmul]
    · intro χ
      rw [compχ _ τb hb2, ha2]
      rfl
  have add : ∀ a b, ρ₀ (a + b) = ρ₀ a + ρ₀ b := by
    intro a b
    obtain ⟨τa, ha1, ha2⟩ := hρ₀ a
    obtain ⟨τb, hb1, hb2⟩ := hρ₀ b
    haveI := E.i_hom
    refine (uniq (a + b) _ (τa * τb) ?_ ?_).symm
    · rw [MonObj.mul_comp, ha1, hb1, hadd, Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift]
    · intro χ
      rw [chV_mul, ha2, hb2, AddMonoidHom.add_apply, TorusActRing.charUnit_add']
  have zero : ρ₀ 0 = 0 := by
    have := add 0 0
    rw [add_zero] at this
    simpa using this
  refine ⟨{ toFun := fun a => (ρ₀ a).toIntLinearMap
            map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, fun a => ?_⟩
  · ext x; simp [one]
  · intro a b; ext x; simp [mul]
  · ext x; simp [zero]
  · intro a b; ext x; simp [add]
  · obtain ⟨τ, e₁, e₂⟩ := hρ₀ a
    exact ⟨τ, e₁, fun χ => e₂ χ⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomCharacterEndOfTorusExtensionActionStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringHom_characterEnd_of_torusExtension_action : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G] (E : TorusExtension G) (O : Type) [Ring O] (act : O → (G ⟶ G)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 G → (∀ a b, act (a * b) = act a ≫ act b) → (∀ a b, act (a + b) = act a * act b) → letI := E.addCommGroup; ∃ ρ : O →+* Module.End ℤ E.X, ∀ a, ∃ τ : splitTorus (Sp k) E.X ⟶ splitTorus (Sp k) E.X, τ ≫ E.i = E.i ≫ act a ∧ ∀ χ, chV τ χ = charUnit (Sp k) E.X (ρ a χ) := by
  first | exact @GlobalTheory.ringHom_charEnd_of_torusExtension | exact GlobalTheory.ringHom_charEnd_of_torusExtension | (intros; apply GlobalTheory.ringHom_charEnd_of_torusExtension <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PerCoordExists
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PerCoordExists
open Matrix
open scoped ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)
open GlobalTheory.PELU
open GlobalTheory.PeriodCoord (realMap realMap_apply realMap_inj det_ne_zero_of_pos colMat exists_finset_of_mem_nhds)

namespace GlobalTheory.PerCoordU

noncomputable section

variable {g : ℕ}

theorem coords_sum {d : ℕ} (π : Matrix (Fin g) (Fin g) ℂ →ₗ[ℂ] (Fin d → ℂ)) (S : Matrix (Fin g) (Fin g) ℂ) (k : Fin d) :
    π S k = ∑ i, ∑ j, S i j * π (Matrix.single i j 1) k := by
  conv_lhs => rw [matrix_eq_sum_single S]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show Matrix.single i j (S i j) = S i j • Matrix.single i j (1 : ℂ) by rw [smul_single, smul_eq_mul, mul_one],
    map_smul, Pi.smul_apply, smul_eq_mul]

theorem perCoord_exists : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ)
    (D : PLat O bar), ∃ d, PerCoord D ρ d := by
  intro O _ bar g ρ D
  classical
  refine ⟨Module.finrank ℂ (Tsp bar ρ), fun P₀ hP₀ => ?_⟩
  set d := Module.finrank ℂ (Tsp bar ρ)
  let bV := Module.finBasis ℂ (Tsp bar ρ)
  obtain ⟨p, hp⟩ := (Tsp bar ρ).subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)
  let ι : (Fin d → ℂ) →ₗ[ℂ] Matrix (Fin g) (Fin g) ℂ := (Tsp bar ρ).subtype ∘ₗ bV.equivFun.symm.toLinearMap
  let π : Matrix (Fin g) (Fin g) ℂ →ₗ[ℂ] (Fin d → ℂ) := bV.equivFun.toLinearMap ∘ₗ p
  have hιeq : ∀ b, ι b = ((bV.equivFun.symm b : Tsp bar ρ) : Matrix (Fin g) (Fin g) ℂ) := fun b => rfl
  have hιT : ∀ b, ι b ∈ Tsp bar ρ := fun b => by rw [hιeq]; exact Submodule.coe_mem _
  have hpv : ∀ v : Tsp bar ρ, p ((Tsp bar ρ).subtype v) = v := fun v => LinearMap.congr_fun hp v
  have hπι : ∀ b, π (ι b) = b := fun b => by
    rw [hιeq]; simp only [π, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [show ((bV.equivFun.symm b : Tsp bar ρ) : Matrix (Fin g) (Fin g) ℂ) = (Tsp bar ρ).subtype (bV.equivFun.symm b) from rfl, hpv, LinearEquiv.apply_symm_apply]
  have hιπ : ∀ S ∈ Tsp bar ρ, ι (π S) = S := fun S hS => by
    rw [hιeq]; simp only [π, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [show S = (Tsp bar ρ).subtype ⟨S, hS⟩ from rfl, hpv, LinearEquiv.symm_apply_apply]
    rfl
  obtain ⟨α, β, hαβ⟩ := exists_colMat_per hP₀
  obtain ⟨M₀, hM₀h, hpos₀, hM₀⟩ := hP₀.2.2.2.2
  have hdet₀ : M₀.det ≠ 0 := det_ne_zero_of_pos hpos₀
  have hu₀ : IsUnit M₀.det := isUnit_iff_ne_zero.2 hdet₀
  have hA₀ : colMat α P₀ = 1 ∧ colMat β P₀ = 0 :=
    realMap_inj (ext_per hP₀ fun x => by rw [← hαβ P₀ hP₀]; simp [realMap_apply])
  let Cf : (D.La → Fin g → ℂ) → Matrix (Fin g) (Fin g) ℂ := fun f => (colMat α f)⁻¹ * colMat β f
  let Z : (D.La →+ (Fin g → ℂ)) → (Fin d → ℂ) := fun P => π ((Cf P)ᵀ * M₀)
  let Cof : (Fin d → ℂ) → Matrix (Fin g) (Fin g) ℂ := fun b => (ι b * M₀⁻¹)ᵀ
  let Q : (Fin d → ℂ) → (D.La →+ (Fin g → ℂ)) := fun b => (realMap 1 (Cof b)).toAddMonoidHom.comp P₀
  have hQ : ∀ b x, Q b x = realMap 1 (Cof b) (P₀ x) := fun b x => rfl
  have hCofT : ∀ b, (Cof b)ᵀ * M₀ = ι b := fun b => by
    simp only [Cof, transpose_transpose, nonsing_inv_mul_cancel_right _ _ hu₀]
  obtain ⟨U, hUg, hUo, hU0⟩ := mem_nhds_iff.1 (GlobalTheory.T.eventually_posDef_hermForm_near_zero_matrix M₀ hpos₀)
  have hQper : ∀ b, Cof b ∈ U → IsPeriod D ρ (Q b) := fun b hb => by
    obtain ⟨hY, hX, hpos⟩ := hUg hb
    have hT : (Cof b)ᵀ * M₀ ∈ Tsp bar ρ := by rw [hCofT]; exact hιT b
    obtain ⟨hMh, hMim⟩ := GlobalTheory.T.riemann_relation_converse_conjAffine M₀ (Cof b) hM₀h hdet₀ hT.1 hY
    refine GlobalTheory.T.isPeriodMap_comp_injective_realLinear D ρ P₀ (realMap 1 (Cof b)) _ hP₀ (realMap_one_injective hX) (fun a x => ?_) hMh hpos (fun x y => ?_)
    · rw [realMap_apply, realMap_apply, one_mulVec, one_mulVec, star_mulVec_map, mulVec_mulVec,
        ← comm_of_mem_Tsp hP₀ hM₀ hdet₀ hT a, ← mulVec_mulVec, mulVec_add]
    · rw [realMap_apply, realMap_apply, one_mulVec, one_mulVec, hMim, hM₀]
  have hCofc : Continuous Cof := by
    exact (Continuous.matrix_mul ι.continuous_of_finiteDimensional continuous_const).matrix_transpose
  have hCof0 : Cof 0 = 0 := by simp [Cof, ι]
  have hZ0 : Z P₀ = 0 := by simp [Z, Cf, hA₀]
  have hcol : ∀ γ : Fin g → (D.La →₀ ℂ), Continuous fun f : D.La → Fin g → ℂ => colMat γ f := fun γ =>
    continuous_matrix fun i j => by simp only [colMat, of_apply]; fun_prop
  have hCfc : ContinuousAt Cf ⇑P₀ := by
    refine ContinuousAt.mul ?_ (hcol β).continuousAt
    refine ContinuousAt.comp (f := fun f => colMat α f) ?_ (hcol α).continuousAt
    refine continuousAt_matrix_inv _ ?_
    rw [hA₀.1, det_one]
    exact (Ring.inverse_eq_inv' (G₀ := ℂ)) ▸ continuousAt_inv₀ one_ne_zero
  have hCf0 : Cf P₀ = 0 := by simp [Cf, hA₀]
  have hdetc : Continuous fun f : D.La → Fin g → ℂ => (colMat α f).det := (hcol α).matrix_det
  obtain ⟨s, ε, hε, hs⟩ := exists_finset_of_mem_nhds
    ((hdetc.continuousAt (x := ⇑P₀)).eventually_ne (show (colMat α P₀).det ≠ 0 by simp [hA₀.1]) |>.and
      (hCfc.preimage_mem_nhds (hUo.mem_nhds (by rw [hCf0]; exact hU0))))
  refine ⟨Cof ⁻¹' U, Q, Z, s, ε, hUo.preimage hCofc, hε, ⟨fun b hb => hQper b hb, fun x => ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · let F : (Fin d → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
      { toFun := fun b => Cof b *ᵥ star (P₀ x)
        map_add' := fun b b' => by simp only [Cof, map_add (f := _), Matrix.add_mul, transpose_add, add_mulVec]
        map_smul' := fun c b => by
          simp only [Cof, map_smul, Matrix.smul_mul, transpose_smul, smul_mulVec, RingHom.id_apply] }
    have hF : Differentiable ℂ (fun b => F b) := (LinearMap.toContinuousLinearMap F).differentiable
    refine ((differentiableOn_const (P₀ x)).add hF.differentiableOn).congr fun b _ => ?_
    rw [hQ, realMap_apply, one_mulVec]; rfl
  · show Cof (Z P₀) ∈ U
    rw [hZ0, hCof0]; exact hU0
  · ext x
    rw [hZ0, hQ, hCof0, realMap_apply, one_mulVec, zero_mulVec, add_zero]
  · intro b hb _
    have h1 := hαβ (Q b) (hQper b hb)
    have key : colMat α (Q b) = 1 ∧ colMat β (Q b) = Cof b :=
      realMap_inj (ext_per hP₀ fun x => by rw [← h1 x, hQ])
    show π (((colMat α (Q b))⁻¹ * colMat β (Q b))ᵀ * M₀) = b
    rw [key.1, key.2, inv_one, Matrix.one_mul, hCofT, hπι]
  · intro P hP hn
    obtain ⟨hdetA, hCU⟩ := hs _ hn
    have hu : IsUnit (colMat α P).det := isUnit_iff_ne_zero.2 hdetA
    have hT := mem_Tsp_of_period hP₀ hP hM₀ (hαβ P hP) hdetA
    have hCofZ : Cof (Z P) = Cf P := by
      show (ι (π ((Cf P)ᵀ * M₀)) * M₀⁻¹)ᵀ = Cf P
      rw [hιπ _ hT, mul_nonsing_inv_cancel_right _ _ hu₀, transpose_transpose]
    refine ⟨show Cof (Z P) ∈ U by rw [hCofZ]; exact hCU, Matrix.toLinearEquiv' _ (invertibleOfIsUnitDet _ hu),
      fun x => ?_⟩
    rw [hQ, hCofZ]
    change P x = colMat α P *ᵥ realMap 1 ((colMat α P)⁻¹ * colMat β P) (P₀ x)
    rw [hαβ P hP x, realMap_apply, realMap_apply, one_mulVec, mulVec_add, mulVec_mulVec,
      mul_nonsing_inv_cancel_left _ _ hu]
  · intro P P' hP hP' _ _ h hh
    let H := LinearMap.toMatrix' h.toLinearMap
    have hHv : ∀ v, h v = H *ᵥ v := fun v => (LinearMap.toMatrix'_mulVec _ v).symm
    have hHinv : LinearMap.toMatrix' h.symm.toLinearMap * H = 1 := by
      rw [← LinearMap.toMatrix'_comp, show h.symm.toLinearMap ∘ₗ h.toLinearMap = LinearMap.id from
        LinearMap.ext fun v => h.symm_apply_apply v, LinearMap.toMatrix'_id]
    have hHu : IsUnit H.det := isUnit_det_of_left_inverse hHinv
    have key : colMat α P' = H * colMat α P ∧ colMat β P' = H * colMat β P :=
      realMap_inj (ext_per hP₀ fun x => by
        rw [← hαβ P' hP' x, hh x, hαβ P hP x, hHv]
        simp only [realMap_apply, mulVec_add, mulVec_mulVec])
    show π (((colMat α P')⁻¹ * colMat β P')ᵀ * M₀) = π (((colMat α P)⁻¹ * colMat β P)ᵀ * M₀)
    rw [key.1, key.2, Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc H⁻¹ H, nonsing_inv_mul _ hHu,
      Matrix.one_mul]
  · intro m B' P _ hP hnear
    have hc : ∀ (γ : Fin g → (D.La →₀ ℂ)) i j, DifferentiableOn ℂ (fun b => colMat γ (P b) i j) B' :=
      fun γ i j => by
        simp only [colMat, of_apply]
        exact DifferentiableOn.fun_sum fun x _ => (differentiableOn_pi.1 (hP.2 x) i).const_mul _
    have hinv := RiemannRel.differentiableOn_left_inverse (fun b => colMat α (P b)) (fun b => (colMat α (P b))⁻¹)
      (hc α) (fun b hb => nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (hs _ (hnear b hb)).1))
    refine differentiableOn_pi.2 fun k => ?_
    show DifferentiableOn ℂ (fun b => π (((colMat α (P b))⁻¹ * colMat β (P b))ᵀ * M₀) k) B'
    have hd : DifferentiableOn ℂ (fun b => ∑ i : Fin g, ∑ j : Fin g,
        (∑ l : Fin g, (∑ n : Fin g, (colMat α (P b))⁻¹ l n * colMat β (P b) n i) * M₀ l j) *
          π (Matrix.single i j 1) k) B' :=
      DifferentiableOn.fun_sum fun i _ => DifferentiableOn.fun_sum fun j _ =>
        (DifferentiableOn.fun_sum fun l _ => (DifferentiableOn.fun_sum fun n _ =>
          (hinv _ _).mul (hc β _ _)).mul_const _).mul_const _
    apply hd.congr
    intro b _
    simpa only [Matrix.mul_apply, Matrix.transpose_apply] using
      (coords_sum π (((colMat α (P b))⁻¹ * colMat β (P b))ᵀ * M₀) k)

end

end GlobalTheory.PerCoordU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PerCoordExistsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_perCoord : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (D : PLat O bar), ∃ d, PerCoord D ρ d := by
  first | exact @GlobalTheory.PerCoordU.perCoord_exists | exact GlobalTheory.PerCoordU.perCoord_exists | (intros; apply GlobalTheory.PerCoordU.perCoord_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompositeCutOperatorsProductLocalCellsMirabolic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompositeCutOperatorsProductLocalCellsMirabolic
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

namespace GlobalTheory.JSW.CutProd

open GlobalTheory.JSW.Cut

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {m : ℕ}

theorem lr_loc_of_mem_mirS {S : Finset (HeightOneSpectrum (𝓞 E))} {p : GA E (m + 1)} (hp : p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m))
    (w : HeightOneSpectrum (𝓞 E)) :
    GlobalTheory.JSW.KirFin.lr (GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p) = GlobalTheory.JSW.KirFin.lr 1 := by
  funext j
  have h := hp.2 j
  simp only [GlobalTheory.JSW.KirFin.lr]
  show ((pLoc E w).comp (pFin E)) ((p : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j) = _
  rw [h]
  split_ifs with hj <;> simp [hj, Matrix.one_apply, eq_comm]

theorem exists_cut_prod (ψ : ∀ w : HeightOneSpectrum (𝓞 E), AddChar (w.adicCompletion E) ℂ)
    (hψ : ∀ w x, ψ w x = (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w x)) : ℂ)) (K : Subgroup (GL (Fin (m + 1)) (Af E)))
    (U : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin (m + 1)) (w.adicCompletion E)))
    (z : ∀ w : HeightOneSpectrum (𝓞 E), GL (Fin (m + 1)) (w.adicCompletion E)) (S : Finset (HeightOneSpectrum (𝓞 E))) :
    (∀ w ∈ S, ∀ u ∈ U w, locGL E (m + 1) w u ∈ K) →
    (∀ w ∈ S, Cuts (ψ w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))
      (cell (z w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) {p | GlobalTheory.JSW.KirFin.lr p = GlobalTheory.JSW.KirFin.lr 1}) →
    ∃ T : GA E (m + 1) →₀ ℂ, (∀ h ∈ T.support, h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S ∧ GeneralLinearGroup.map (pInf E) h = 1) ∧
      ∀ W : GA E (m + 1) → ℂ, (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) →
        (∀ u ∈ K, ∀ g, W (g * finGL E (m + 1) u) = W g) →
        ∀ y : GA E (m + 1), (∀ w ∈ S, GlobalTheory.JSW.KirFin.lr (GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) y) =
          GlobalTheory.JSW.KirFin.lr 1) →
        GlobalTheory.JSW.Cut.act T W y = {x : GA E (m + 1) | ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) x ∈
          cell (z w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))}.indicator W y := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro _ _
    refine ⟨Finsupp.single 1 1, fun h hh => ?_, fun W _ _ y _ => ?_⟩
    · have h1 : h = 1 := Finset.mem_singleton.1 (Finsupp.support_single_subset hh)
      subst h1
      exact ⟨fun v _ => map_one _, map_one _⟩
    · simp
  | insert w S hw ih =>
    intro hK hC
    obtain ⟨T₁, hT₁s, hT₁⟩ := ih (fun v hv => hK v (Finset.mem_insert_of_mem hv))
      (fun v hv => hC v (Finset.mem_insert_of_mem hv))
    obtain ⟨T₂, hT₂s, hT₂⟩ := GlobalTheory.T.localCutOperator_transfer_adelicWhittaker E m w (ψ w) (hψ w) K (U w) (hK w (Finset.mem_insert_self _ _))
      (cell (z w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) {p | GlobalTheory.JSW.KirFin.lr p = GlobalTheory.JSW.KirFin.lr 1}
      (hC w (Finset.mem_insert_self _ _))
    refine ⟨comp T₁ T₂, fun k hk => ?_, fun W hN hKW y hy => ?_⟩
    · obtain ⟨a, ha, b, hb, rfl⟩ := mem_support_comp hk
      obtain ⟨g, rfl⟩ := hT₂s b hb
      have hb' := (GlobalTheory.JSW.WhitModel.loc_mem_supS (insert w S) w g).2 (Or.inl (Finset.mem_insert_self _ _))
      refine ⟨fun v hv => ?_, ?_⟩
      · rw [map_mul, (hT₁s a ha).1 v (fun h => hv (Finset.mem_insert_of_mem h)), hb' v hv, one_mul]
      · rw [map_mul, (hT₁s a ha).2, pInf_finGL, one_mul]
    · have hyh : ∀ h ∈ T₁.support, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (y * h) =
          GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) y := fun h hh => by
        rw [map_mul, (hT₁s h hh).1 w hw, mul_one]
      have hyS := hT₁ W hN hKW y (fun v hv => hy v (Finset.mem_insert_of_mem hv))
      have hyw := hy w (Finset.mem_insert_self _ _)
      rw [act_comp]
      by_cases hyc : GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) y ∈
          cell (z w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))
      · rw [act_congr T₁ (f' := W) fun k hk => ?_, hyS]
        · simp only [Set.indicator, Set.mem_setOf_eq, Finset.forall_mem_insert, hyc, true_and]
        · rw [hT₂ W hN hKW (y * k) (by rw [hyh k hk]; exact hyw), Set.indicator_of_mem]
          rw [Set.mem_setOf_eq, hyh k hk]; exact hyc
      · rw [act_congr T₁ (f' := 0) fun k hk => ?_]
        · simp only [Set.indicator, Set.mem_setOf_eq, Finset.forall_mem_insert, hyc, false_and, if_false]
          unfold GlobalTheory.JSW.Cut.act; simp
        · rw [hT₂ W hN hKW (y * k) (by rw [hyh k hk]; exact hyw), Set.indicator_of_notMem]
          · rfl
          · rw [Set.mem_setOf_eq, hyh k hk]; exact hyc

end GlobalTheory.JSW.CutProd

theorem _root_.GlobalTheory.JSW.CutProd.cut_prod_mirS : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (ψ : ∀ w : HeightOneSpectrum (𝓞 E), AddChar (w.adicCompletion E) ℂ), (∀ w x, ψ w x = (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w x)) : ℂ)) → ∀ (K : Subgroup (GL (Fin (m + 1)) (Af E))) (U : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin (m + 1)) (w.adicCompletion E))) (z : ∀ w : HeightOneSpectrum (𝓞 E), GL (Fin (m + 1)) (w.adicCompletion E)), (∀ w ∈ S, ∀ u ∈ U w, locGL E (m + 1) w u ∈ K) → (∀ w ∈ S, GlobalTheory.JSW.Cut.Cuts (ψ w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E))) (GlobalTheory.JSW.Cut.cell (z w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) {p | GlobalTheory.JSW.KirFin.lr p = GlobalTheory.JSW.KirFin.lr 1}) → ∃ T : GA E (m + 1) →₀ ℂ, (∀ h ∈ T.support, h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S ∧ GeneralLinearGroup.map (pInf E) h = 1) ∧ ∀ W : GA E (m + 1) → ℂ, (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ u ∈ K, ∀ g, W (g * finGL E (m + 1) u) = W g) → ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GlobalTheory.JSW.Cut.act T W p = {x : GA E (m + 1) | ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) x ∈ GlobalTheory.JSW.Cut.cell (z w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))}.indicator W p := by
  intro E _ _ _ m S ψ hψ K U z hK hC
  obtain ⟨T, hTs, hT⟩ := GlobalTheory.JSW.CutProd.exists_cut_prod ψ hψ K U z S hK hC
  exact ⟨T, hTs, fun W hN hKW p hp => hT W hN hKW p fun w _ => GlobalTheory.JSW.CutProd.lr_loc_of_mem_mirS hp w⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompositeCutOperatorsProductLocalCellsMirabolicStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.composite_cut_operators_product_local_cells_mirabolic : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (ψ : ∀ w : HeightOneSpectrum (𝓞 E), AddChar (w.adicCompletion E) ℂ), (∀ w x, ψ w x = (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w x)) : ℂ)) → ∀ (K : Subgroup (GL (Fin (m + 1)) (Af E))) (U : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin (m + 1)) (w.adicCompletion E))) (z : ∀ w : HeightOneSpectrum (𝓞 E), GL (Fin (m + 1)) (w.adicCompletion E)), (∀ w ∈ S, ∀ u ∈ U w, locGL E (m + 1) w u ∈ K) → (∀ w ∈ S, GlobalTheory.JSW.Cut.Cuts (ψ w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E))) (GlobalTheory.JSW.Cut.cell (z w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) {p | GlobalTheory.JSW.KirFin.lr p = GlobalTheory.JSW.KirFin.lr 1}) → ∃ T : GA E (m + 1) →₀ ℂ, (∀ h ∈ T.support, h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S ∧ GeneralLinearGroup.map (pInf E) h = 1) ∧ ∀ W : GA E (m + 1) → ℂ, (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ u ∈ K, ∀ g, W (g * finGL E (m + 1) u) = W g) → ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GlobalTheory.JSW.Cut.act T W p = {x : GA E (m + 1) | ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) x ∈ GlobalTheory.JSW.Cut.cell (z w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))}.indicator W p := by
  first | exact @GlobalTheory.JSW.CutProd.cut_prod_mirS | exact GlobalTheory.JSW.CutProd.cut_prod_mirS | (intros; apply GlobalTheory.JSW.CutProd.cut_prod_mirS <;> assumption)
end
end
