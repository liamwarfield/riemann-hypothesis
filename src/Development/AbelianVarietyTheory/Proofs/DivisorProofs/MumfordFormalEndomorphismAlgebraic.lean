module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordThickeningEndomorphismMapsSections
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleFourthPowerUniformisedGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningEqOfGenericSectionRatios

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericFibreHomOfFormalSectionRatios
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonHomExtensionOpenPartField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonHomExtensionOpenPartField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.GenericHomField

abbrev bc (K : Type) [Field K] : Sp (AlgebraicClosure K) ⟶ Sp K := spMap (algebraMap K (AlgebraicClosure K))

instance flat_bc (K : Type) [Field K] : Flat (bc K) := by
  rw [bc, spMap, Flat.SpecMap_iff]
  exact RingHom.Flat.of_isField (Field.toIsField K) _

instance surjective_bc (K : Type) [Field K] : Surjective (bc K) :=
  ⟨Function.surjective_to_subsingleton _⟩

theorem isPullback_map_left {S T : Scheme.{0}} (φ : T ⟶ S) {X Y : Over S} (u : X ⟶ Y) :
    IsPullback ((Over.pullback φ).map u).left (pullback.fst X.hom φ) (pullback.fst Y.hom φ) u.left := by
  refine IsPullback.of_right (h₁₂ := pullback.snd Y.hom φ) (v₁₃ := φ) (h₂₂ := Y.hom) ?_ ?_
    (IsPullback.of_hasPullback Y.hom φ).flip
  · have e1 : ((Over.pullback φ).map u).left ≫ pullback.snd Y.hom φ = pullback.snd X.hom φ :=
      Over.w ((Over.pullback φ).map u)
    have e2 : u.left ≫ Y.hom = X.hom := Over.w u
    rw [e1, e2]
    exact (IsPullback.of_hasPullback X.hom φ).flip
  · simp only [Over.pullback_map_left]
    exact pullback.lift_fst _ _ _

variable {K : Type} [Field K]

theorem map_injective {X Y : Over (Sp K)} {u v : X ⟶ Y}
    (h : (Over.pullback (bc K)).map u = (Over.pullback (bc K)).map v) : u = v := by
  have : Epi (pullback.fst X.hom (bc K)) := Flat.epi_of_flat_of_surjective _
  ext1
  apply (cancel_epi (pullback.fst X.hom (bc K))).1
  rw [← (isPullback_map_left (bc K) u).w, ← (isPullback_map_left (bc K) v).w, h]

theorem map_mul' {X M : Over (Sp K)} [MonObj M] (a b : X ⟶ M) :
    (Over.pullback (bc K)).map (a * b) = (Over.pullback (bc K)).map a * (Over.pullback (bc K)).map b :=
  map_mul (Over.pullback (bc K)).homMonoidHom a b

theorem flat_mul {S : Scheme.{0}} (H V : Over S) [GrpObj H] [Flat H.hom] (j : V ⟶ H)
    [IsOpenImmersion j.left] : Flat ((fst V V ≫ j) * (snd V V ≫ j)).left := by
  let sh : H ⊗ H ⟶ H ⊗ H := lift (fst H H) (fst H H * snd H H)
  let sh' : H ⊗ H ⟶ H ⊗ H := lift (fst H H) ((fst H H)⁻¹ * snd H H)
  have e1 : sh ≫ sh' = 𝟙 _ := by
    ext <;> simp [sh, sh', MonObj.comp_mul, GrpObj.comp_inv]
  have e2 : sh' ≫ sh = 𝟙 _ := by
    ext <;> simp [sh, sh', MonObj.comp_mul, GrpObj.comp_inv]
  have : IsIso sh.left := ⟨sh'.left, by rw [← Over.comp_left, e1]; rfl, by rw [← Over.comp_left, e2]; rfl⟩
  have hm : (fst V V ≫ j) * (snd V V ≫ j) = (j ⊗ₘ j) ≫ sh ≫ snd H H := by
    simp [sh, Hom.mul_def]
  have : Flat (snd H H).left := by
    show Flat (pullback.snd H.hom H.hom); infer_instance
  have : IsOpenImmersion (j ⊗ₘ j).left := by
    rw [Over.tensorHom_left]; infer_instance
  rw [hm, Over.comp_left, Over.comp_left]
  infer_instance

theorem quasiCompact_mul {S : Scheme.{0}} (H V : Over S) [GrpObj H] [IsLocallyNoetherian H.left]
    [QuasiCompact H.hom] [QuasiSeparated H.hom] (j : V ⟶ H) [IsOpenImmersion j.left] :
    QuasiCompact ((fst V V ≫ j) * (snd V V ≫ j)).left := by
  have : QuasiCompact V.hom := by rw [← Over.w j]; infer_instance
  have : QuasiCompact (V ⊗ V).hom := by
    show QuasiCompact (pullback.fst V.hom V.hom ≫ V.hom); infer_instance
  have h2 : QuasiCompact (((fst V V ≫ j) * (snd V V ≫ j)).left ≫ H.hom) := by
    rw [Over.w]; infer_instance
  have h3 : QuasiSeparated H.hom := inferInstance
  exact MorphismProperty.of_postcomp (W := @QuasiCompact) (W' := @QuasiSeparated) _ H.hom h3 h2

theorem surjective_mul {K : Type} [Field K] (H V : Over (Sp K)) [GrpObj H] (hH : GlobalTheory.SS.SmConn H)
    (j : V ⟶ H) [IsOpenImmersion j.left] [Nonempty V.left] :
    Surjective ((fst V V ≫ j) * (snd V V ≫ j)).left := by
  have hH' := GlobalTheory.IsogRed.smConn_baseChange (bc K) H hH
  obtain ⟨_, hs, _, _, _⟩ := hH
  obtain ⟨_, hs', _, _, _⟩ := hH'
  have : IsIntegral ((Over.pullback (bc K)).obj H).left :=
    isIntegral_of_smooth_of_geometricallyConnected ((Over.pullback (bc K)).obj H).hom
  have hj' : IsOpenImmersion ((Over.pullback (bc K)).map j).left :=
    MorphismProperty.of_isPullback (isPullback_map_left (bc K) j).flip inferInstance
  have hV' : Nonempty ((Over.pullback (bc K)).obj V).left := by
    obtain ⟨v⟩ := ‹Nonempty V.left›
    obtain ⟨w, -⟩ := (pullback.fst V.hom (bc K)).surjective v
    exact ⟨w⟩
  have hflat : Flat ((Over.pullback (bc K)).map ((fst V V ≫ j) * (snd V V ≫ j))).left :=
    MorphismProperty.of_isPullback (isPullback_map_left (bc K) _).flip (flat_mul H V j)
  have htr : ∀ (a x : 𝟙_ (Over (Sp (AlgebraicClosure K))) ⟶ (Over.pullback (bc K)).obj H),
      x ≫ (GlobalTheory.SS.transl a).hom = a * x := fun a x =>
    (GlobalTheory.GenericHom.point_comp_mul x a (𝟙 _)).trans (by rw [Category.comp_id])
  have hdec : ∀ h : 𝟙_ (Over (Sp (AlgebraicClosure K))) ⟶ (Over.pullback (bc K)).obj H,
      ∃ a x : 𝟙_ (Over (Sp (AlgebraicClosure K))) ⟶ (Over.pullback (bc K)).obj V,
      (a ≫ (Over.pullback (bc K)).map j) * (x ≫ (Over.pullback (bc K)).map j) = h := by
    intro h
    obtain ⟨u, hu⟩ := GlobalTheory.GenericHom.exists_generic ((Over.pullback (bc K)).map j)
      [Iso.refl _, asIso (ι[(Over.pullback (bc K)).obj H]) ≪≫ GlobalTheory.SS.transl h]
    obtain ⟨x, hx⟩ := hu (Iso.refl _) (by simp)
    obtain ⟨a, ha⟩ := hu (asIso (ι[(Over.pullback (bc K)).obj H]) ≪≫ GlobalTheory.SS.transl h) (by simp)
    refine ⟨a, x, ?_⟩
    rw [ha, hx, Iso.trans_hom, ← Category.assoc, htr, asIso_hom, Iso.refl_hom, Category.comp_id,
      ← Hom.inv_def, inv_mul_cancel_right]
  have hrange : ∀ y, y ∈ Set.range ((Over.pullback (bc K)).map ((fst V V ≫ j) * (snd V V ≫ j))).left := by
    intro y
    obtain ⟨h, hh⟩ := GlobalTheory.GenericHom.exists_point_mem ((Over.pullback (bc K)).obj H) (closure {y})
      isClosed_closure.isLocallyClosed ⟨y, subset_closure rfl⟩
    obtain ⟨a, x, hax⟩ := hdec h
    let t := lift a x ≫ Functor.LaxMonoidal.μ (Over.pullback (bc K)) V V
    have ht : t ≫ (Over.pullback (bc K)).map ((fst V V ≫ j) * (snd V V ≫ j)) = h := by
      rw [map_mul', Functor.map_comp, Functor.map_comp, MonObj.comp_mul, ← hax]
      simp only [t, Category.assoc]
      rw [← Category.assoc (Functor.LaxMonoidal.μ _ V V), Functor.Monoidal.μ_fst,
        ← Category.assoc (Functor.LaxMonoidal.μ _ V V), Functor.Monoidal.μ_snd, lift_fst_assoc, lift_snd_assoc]
    have hpt : ((Over.pullback (bc K)).map ((fst V V ≫ j) * (snd V V ≫ j))).left
        (t.left (IsLocalRing.closedPoint (AlgebraicClosure K))) =
        h.left (IsLocalRing.closedPoint (AlgebraicClosure K)) := by
      have := congrArg (fun φ => φ.left (IsLocalRing.closedPoint (AlgebraicClosure K))) ht
      exact this
    exact (hflat.generalizingMap).stableUnderGeneralization_range
      (specializes_iff_mem_closure.2 (hh _)) ⟨_, hpt⟩
  refine ⟨fun y => ?_⟩
  obtain ⟨yb, rfl⟩ := (pullback.fst H.hom (bc K)).surjective y
  obtain ⟨w, rfl⟩ := hrange yb
  exact ⟨pullback.fst _ (bc K) w, by
    rw [← Scheme.Hom.comp_apply, ← (isPullback_map_left (bc K) _).w, Scheme.Hom.comp_apply]⟩

theorem exists_monHom_extension_of_field : ∀ (K : Type) [Field K] (H G V : Over (Sp K)) [GrpObj H] [GrpObj G], GlobalTheory.SS.SmConn H → GlobalTheory.SS.SmConn G → ∀ (j : V ⟶ H) (f : V ⟶ G), IsOpenImmersion j.left → Nonempty V.left → (∀ (Z : Over (Sp K)) (u₁ u₂ u₃ : Z ⟶ V), (u₁ ≫ j) * (u₂ ≫ j) = u₃ ≫ j → (u₁ ≫ f) * (u₂ ≫ f) = u₃ ≫ f) → ∃ F : H ⟶ G, IsMonHom F ∧ j ≫ F = f := by
  intro K _ H G V _ _ hH hG j f hj hV hm
  have hj' : IsOpenImmersion ((Over.pullback (bc K)).map j).left :=
    MorphismProperty.of_isPullback (isPullback_map_left (bc K) j).flip hj
  have hV' : Nonempty ((Over.pullback (bc K)).obj V).left := by
    obtain ⟨v⟩ := hV
    obtain ⟨w, -⟩ := (pullback.fst V.hom (bc K)).surjective v
    exact ⟨w⟩
  have hpts : ∀ x y z : 𝟙_ (Over (Sp (AlgebraicClosure K))) ⟶ (Over.pullback (bc K)).obj V,
      (x ≫ (Over.pullback (bc K)).map j) * (y ≫ (Over.pullback (bc K)).map j) = z ≫ (Over.pullback (bc K)).map j →
      (x ≫ (Over.pullback (bc K)).map f) * (y ≫ (Over.pullback (bc K)).map f) = z ≫ (Over.pullback (bc K)).map f := by
    intro x y z hxyz
    obtain ⟨x', rfl⟩ := ((Over.mapPullbackAdj (bc K)).homEquiv _ V).surjective x
    obtain ⟨y', rfl⟩ := ((Over.mapPullbackAdj (bc K)).homEquiv _ V).surjective y
    obtain ⟨z', rfl⟩ := ((Over.mapPullbackAdj (bc K)).homEquiv _ V).surjective z
    simp only [← Adjunction.homEquiv_naturality_right, ← ReciprocityTheory.ChartRestriction.G.Out.UBC.homEquiv_mul] at hxyz ⊢
    exact congrArg _ (hm _ x' y' z' (Equiv.injective _ hxyz))
  obtain ⟨Fb, hFb, hjF⟩ := GlobalTheory.GenericHom.exists_monHom_extension (AlgebraicClosure K)
    ((Over.pullback (bc K)).obj H) ((Over.pullback (bc K)).obj G) ((Over.pullback (bc K)).obj V)
    (GlobalTheory.IsogRed.smConn_baseChange _ H hH) (GlobalTheory.IsogRed.smConn_baseChange _ G hG)
    ((Over.pullback (bc K)).map j) ((Over.pullback (bc K)).map f) hj' hV' hpts
  let m : V ⊗ V ⟶ H := (fst V V ≫ j) * (snd V V ≫ j)
  let g : V ⊗ V ⟶ G := (fst V V ≫ f) * (snd V V ≫ f)
  have hPg : (Over.pullback (bc K)).map g = (Over.pullback (bc K)).map m ≫ Fb := by
    simp only [m, g, map_mul', Functor.map_comp, MonObj.mul_comp, Category.assoc, hjF]
  haveI := hj
  haveI := hV
  obtain ⟨_, hs, _, _, _⟩ := id hH
  have : IsLocallyNoetherian H.left := LocallyOfFiniteType.isLocallyNoetherian H.hom
  have hflat : Flat m.left := flat_mul H V j
  have hqc : QuasiCompact m.left := quasiCompact_mul H V j
  have hsurj : Surjective m.left := surjective_mul H V hH j
  have hcond : ∀ {Z : Scheme.{0}} (a b : Z ⟶ (V ⊗ V).left), a ≫ m.left = b ≫ m.left →
      a ≫ g.left = b ≫ g.left := by
    intro Z a b hab
    have hb : b ≫ (V ⊗ V).hom = a ≫ (V ⊗ V).hom := by
      rw [← Over.w m, ← Category.assoc, ← Category.assoc, hab]
    let a' : Over.mk (a ≫ (V ⊗ V).hom) ⟶ V ⊗ V := Over.homMk a rfl
    let b' : Over.mk (a ≫ (V ⊗ V).hom) ⟶ V ⊗ V := Over.homMk b hb
    have h1 : a' ≫ m = b' ≫ m := Over.OverMorphism.ext hab
    have h2 : a' ≫ g = b' ≫ g := map_injective (by
      rw [Functor.map_comp, Functor.map_comp, hPg, ← Category.assoc, ← Category.assoc,
        ← Functor.map_comp, ← Functor.map_comp, h1])
    exact congrArg CommaMorphism.left h2
  let F₀ : H.left ⟶ G.left := EffectiveEpi.desc m.left g.left hcond
  have hF₀ : m.left ≫ F₀ = g.left := EffectiveEpi.fac m.left g.left hcond
  have hw : F₀ ≫ G.hom = H.hom := by
    apply (cancel_epi m.left).1
    rw [← Category.assoc, hF₀, Over.w g, Over.w m]
  let F : H ⟶ G := Over.homMk F₀ hw
  have hmF : m ≫ F = g := Over.OverMorphism.ext hF₀
  have hmb : Epi ((Over.pullback (bc K)).map m).left := by
    have : Flat ((Over.pullback (bc K)).map m).left :=
      MorphismProperty.of_isPullback (isPullback_map_left (bc K) m).flip hflat
    have : Surjective ((Over.pullback (bc K)).map m).left :=
      MorphismProperty.of_isPullback (isPullback_map_left (bc K) m).flip hsurj
    exact Flat.epi_of_flat_of_surjective _
  have hPF : (Over.pullback (bc K)).map F = Fb := by
    ext1
    apply (cancel_epi ((Over.pullback (bc K)).map m).left).1
    rw [← Over.comp_left, ← Over.comp_left, ← Functor.map_comp, hmF, hPg]
  have hmul : ∀ (Z : Over (Sp K)) (x y : Z ⟶ H), (x * y) ≫ F = (x ≫ F) * (y ≫ F) := by
    intro Z x y
    apply map_injective
    rw [Functor.map_comp, map_mul', map_mul', Functor.map_comp, Functor.map_comp, hPF, MonObj.mul_comp]
  refine ⟨F, ?_, map_injective (by rw [Functor.map_comp, hPF, hjF])⟩
  have hone : (1 : 𝟙_ (Over (Sp K)) ⟶ H) ≫ F = 1 := by
    have h := hmul (𝟙_ (Over (Sp K))) 1 1
    rw [_root_.mul_one] at h
    exact _root_.mul_eq_left.1 h.symm
  have e1 : ∀ (A : Over (Sp K)) [GrpObj A], (η[A] : 𝟙_ _ ⟶ A) = 1 := fun A _ => by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  refine ⟨?_, ?_⟩
  · rw [e1 H, e1 G, hone]
  · have h := hmul _ (fst H H) (snd H H)
    simpa [Hom.mul_def] using h

end GlobalTheory.GenericHomField
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonHomExtensionOpenPartFieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_monHom_extension_openPart_field : ∀ (K : Type) [Field K] (H G V : Over (Sp K)) [GrpObj H] [GrpObj G], GlobalTheory.SS.SmConn H → GlobalTheory.SS.SmConn G → ∀ (j : V ⟶ H) (f : V ⟶ G), IsOpenImmersion j.left → Nonempty V.left → (∀ (Z : Over (Sp K)) (u₁ u₂ u₃ : Z ⟶ V), (u₁ ≫ j) * (u₂ ≫ j) = u₃ ≫ j → (u₁ ≫ f) * (u₂ ≫ f) = u₃ ≫ f) → ∃ F : H ⟶ G, IsMonHom F ∧ j ≫ F = f := by
  first | exact @GlobalTheory.GenericHomField.exists_monHom_extension_of_field | exact GlobalTheory.GenericHomField.exists_monHom_extension_of_field | (intros; apply GlobalTheory.GenericHomField.exists_monHom_extension_of_field <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMorphismOfSectionRatiosVeryAmple
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMorphismOfSectionRatiosVeryAmple
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

open GlobalTheory.LBGerm

theorem ratMap_gs_appLE {Z S : Scheme.{0}} (r : Z ⟶ S) (U : S.Opens) (h : ⊤ ≤ r ⁻¹ᵁ U) (w : Z) (a : Γ(S, U)) :
    gs r w U a = gs (𝟙 Z) w ⊤ ((r.appLE U ⊤ h).hom a) := by
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply, gs_res (𝟙 Z) w h trivial, gs_pull (𝟙 Z) r w U (h trivial) a,
    Category.id_comp]

theorem ratMap_eq_of_gs_eq {T S : Scheme.{0}} (g₁ g₂ : T ⟶ S) {U : S.Opens} (hU : IsAffineOpen U)
    (h₁ : ∀ w, g₁ w ∈ U) (h₂ : ∀ w, g₂ w ∈ U) (h : ∀ (a : Γ(S, U)) (w : T), gs g₁ w U a = gs g₂ w U a) :
    g₁ = g₂ := by
  have hf : ⊤ ≤ g₁ ⁻¹ᵁ U := fun w _ => h₁ w
  have hg : ⊤ ≤ g₂ ⁻¹ᵁ U := fun w _ => h₂ w
  have key : ∀ (r : T ⟶ S) (hr : ⊤ ≤ r ⁻¹ᵁ U),
      (⊤ : T.Opens).ι ≫ r = (⊤ : T.Opens).toSpecΓ ≫ Spec.map (r.appLE U ⊤ hr) ≫ hU.fromSpec := by
    intro r hr
    rw [Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, hU.toSpecΓ_fromSpec, Scheme.Hom.resLE_comp_ι]
  have e : g₁.appLE U ⊤ hf = g₂.appLE U ⊤ hg := by
    ext a
    exact fn_ext fun w _ => (ratMap_gs_appLE g₁ U hf w a).symm.trans ((h a w).trans (ratMap_gs_appLE g₂ U hg w a))
  exact Scheme.hom_ext_of_forall g₁ g₂ fun w => ⟨⊤, trivial, by rw [key g₁ hf, key g₂ hg, e]⟩

theorem ratMap_gs_ofRingHom {X Y : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (V : Y.Opens)
    (θ : Γ(X, U) →+* Γ(Y, V)) {Z : Scheme.{0}} (u : Z ⟶ V.toScheme) (w : Z) :
    (u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ) ≫ hU.fromSpec) w ∈ U ∧ ∀ b : Γ(X, U),
      gs (u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ) ≫ hU.fromSpec) w U b = gs (u ≫ V.ι) w V (θ b) := by
  have h0 : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
  have h' : ⊤ ≤ (u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ) ≫ hU.fromSpec) ⁻¹ᵁ U :=
    fun z _ => h0 (Set.mem_univ ((u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)) z))
  have h : ⊤ ≤ (u ≫ V.ι) ⁻¹ᵁ V := fun z _ => (u z).2
  refine ⟨h' trivial, fun b => ?_⟩
  have h1 : hU.fromSpec.appLE U ⊤ h0 = (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact Category.comp_id _
  have h2 : (u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ) ≫ hU.fromSpec).appLE U ⊤ h' =
      hU.fromSpec.appLE U ⊤ h0 ≫ (u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)).appTop := by
    have e := Scheme.Hom.appLE_comp_appLE (u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)) hU.fromSpec U ⊤ ⊤ h0 le_rfl
    rw [show (u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)).appLE ⊤ ⊤ le_rfl =
      (u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)).appTop from Scheme.Hom.appLE_eq_app (f := u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)) (U := ⊤)] at e
    simpa only [Category.assoc] using e.symm
  have h3 : (u ≫ V.ι).appLE V ⊤ h = V.topIso.inv ≫ u.appTop := by
    rw [← Scheme.Hom.appLE_comp_appLE u V.ι V ⊤ ⊤ (fun x _ => x.2) le_rfl]
    erw [Scheme.Opens.ι_appLE]
    simp only [Scheme.Opens.topIso_inv]
    congr 1
    exact Scheme.Hom.appLE_eq_app (f := u) (U := ⊤)
  have h4 : (u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ) ≫ hU.fromSpec).appLE U ⊤ h' =
      CommRingCat.ofHom θ ≫ (u ≫ V.ι).appLE V ⊤ h := by
    rw [h2, h1, h3, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.Opens.toSpecΓ_appTop]
    simp only [Category.assoc]
    rw [Scheme.ΓSpecIso_naturality_assoc]
    exact Iso.inv_hom_id_assoc _ _
  rw [ratMap_gs_appLE _ U h' w b, ratMap_gs_appLE _ V h w (θ b), h4]
  rfl

theorem ratMap_gs_eval₂ {K : Type} [CommRing K] {Z S S' : Scheme.{0}} {Idx : Type} (g₁ : Z ⟶ S) (g₂ : Z ⟶ S')
    {U₁ : S.Opens} {U₂ : S'.Opens} (w : Z) (hw₁ : g₁ w ∈ U₁) (hw₂ : g₂ w ∈ U₂) (f₁ : K →+* Γ(S, U₁))
    (f₂ : K →+* Γ(S', U₂)) (r₁ : Idx → Γ(S, U₁)) (r₂ : Idx → Γ(S', U₂))
    (hc : ∀ a, gs g₁ w U₁ (f₁ a) = gs g₂ w U₂ (f₂ a)) (hr : ∀ l, gs g₁ w U₁ (r₁ l) = gs g₂ w U₂ (r₂ l))
    (P : MvPolynomial Idx K) :
    gs g₁ w U₁ (MvPolynomial.eval₂Hom f₁ r₁ P) = gs g₂ w U₂ (MvPolynomial.eval₂Hom f₂ r₂ P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp only [MvPolynomial.eval₂Hom_C]; exact hc a
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), gs_add _ _ _ hw₁, gs_add _ _ _ hw₂, hp, hq]
  | mul_X p n hp => rw [map_mul, map_mul, gs_mul _ _ _ hw₁, gs_mul _ _ _ hw₂, hp, MvPolynomial.eval₂Hom_X',
      MvPolynomial.eval₂Hom_X', hr n]

theorem ratMap_gs_cst {K : Type} [CommRing K] {Z S : Scheme.{0}} (p : S ⟶ Spec (CommRingCat.of K)) (g : Z ⟶ S)
    (U : S.Opens) (w : Z) (hw : g w ∈ U) (a : K) :
    gs g w U (AbLaw.cst p U a) = gs (g ≫ p) w ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a) := by
  rw [AbLaw.cst, RingHom.comp_apply, RingHom.comp_apply, AbLaw.rs, gs_res g w le_top hw]
  exact gs_pull g p w ⊤ trivial _

theorem ratMap_key {A X Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (π : A ⟶ X) {k k' m : ℕ}
    (σ : Fin (m + 1) → H0 L k) (hcov : ⨆ i, π ⁻¹ᵁ nonzeroLocus (σ i) = ⊤) (s₀ : H0 L k) (t₀ : H0 L k')
    (t : Fin (m + 1) → H0 L k') (i₀ : Fin (m + 1)) (r : Fin (m + 1) → Γ(A, π ⁻¹ᵁ nonzeroLocus (σ i₀)))
    (hr : ∀ (j : Fin (m + 1)) (c : Fin 1 → L.ι) (a : A), π a ∈ nonzeroLocus (σ i₀) → π a ∈ secChart L c →
      secGerm π a (σ j) c = gs (𝟙 A) a (π ⁻¹ᵁ nonzeroLocus (σ i₀)) (r j) * secGerm π a (σ i₀) c)
    (c : Fin 1 → L.ι) (g z : Z ⟶ A) (w : Z) (hc : (g ≫ π) w ∈ secChart L c)
    (ht₀ : IsUnit (secGerm (g ≫ π) w t₀ c)) (hti : IsUnit (secGerm (g ≫ π) w (t i₀) c))
    (hrat : ∀ i, SecRatioEq L (z ≫ π) (g ≫ π) (σ i) s₀ (t i) t₀) :
    z w ∈ π ⁻¹ᵁ nonzeroLocus (σ i₀) ∧ ∀ (l : Fin (m + 1)) (ρ : Z.presheaf.stalk w),
      ρ * secGerm (g ≫ π) w (t i₀) c = secGerm (g ≫ π) w (t l) c →
        gs z w (π ⁻¹ᵁ nonzeroLocus (σ i₀)) (r l) = ρ := by
  obtain ⟨l₀, hl₀⟩ := TopologicalSpace.Opens.mem_iSup.1
    (show z w ∈ ⨆ i, π ⁻¹ᵁ nonzeroLocus (σ i) by rw [hcov]; trivial)
  obtain ⟨j, hj⟩ := exists_chart hL (π (z w))
  let c' : Fin 1 → L.ι := fun _ => j
  have hc' : (z ≫ π) w ∈ secChart L c' := Set.mem_iInter.2 fun _ => hj
  have germ := fun i => secRatioEq_iff_germ.1 (hrat i) w c' c hc' hc
  have uσ : IsUnit (secGerm (z ≫ π) w (σ l₀) c') := (GlobalTheory.mem_nonzeroLocus_iff_pull (σ l₀) (z ≫ π) w hc').1 hl₀
  have us₀ : IsUnit (secGerm (z ≫ π) w s₀ c') := by
    have h := uσ.mul ht₀
    rw [germ l₀] at h
    exact isUnit_of_mul_isUnit_left h
  have uσi : IsUnit (secGerm (z ≫ π) w (σ i₀) c') := by
    have h := us₀.mul hti
    rw [← germ i₀] at h
    exact isUnit_of_mul_isUnit_left h
  have hD : z w ∈ π ⁻¹ᵁ nonzeroLocus (σ i₀) := (GlobalTheory.mem_nonzeroLocus_iff_pull (σ i₀) (z ≫ π) w hc').2 uσi
  refine ⟨hD, fun l ρ hρ => ?_⟩
  have hrl := congrArg (z.stalkMap w).hom (hr l c' (z w) hD hc')
  rw [map_mul, ← secGerm_comp z π w _ hc', ← secGerm_comp z π w _ hc', ← gs_stalkMap z w _ hD] at hrl
  refine (us₀.mul hti).mul_right_cancel ?_
  linear_combination (-(gs z w (π ⁻¹ᵁ nonzeroLocus (σ i₀)) (r l))) * germ i₀ + (-(secGerm (g ≫ π) w t₀ c)) * hrl +
    germ l + (-(secGerm (z ≫ π) w s₀ c')) * hρ

theorem exists_morphism_of_secRatio : ∀ (K : Type) [Field K] (A : Over (Sp K)) [IsIntegral A.left] (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (π : A.left ⟶ X) (k k' m : ℕ) (σ : Fin (m + 1) → H0 L k), VeryAmpleAlong A.hom π L σ → ∀ (s₀ : H0 L k) (t₀ : H0 L k') (t : Fin (m + 1) → H0 L k'), (∃ a : A.left, π a ∈ nonzeroLocus t₀) → ∀ (Y : Over (Sp K)) (x y : Y ⟶ A), IsDominant x.left → (∀ i, SecRatioEq L (y.left ≫ π) (x.left ≫ π) (σ i) s₀ (t i) t₀) → ∃ (V : Over (Sp K)) (j f : V ⟶ A), IsOpenImmersion j.left ∧ Nonempty V.left ∧ ∀ (Z : Over (Sp K)) (u : Z ⟶ V) (z : Z ⟶ A), (∀ i, SecRatioEq L (z.left ≫ π) ((u ≫ j).left ≫ π) (σ i) s₀ (t i) t₀) → u ≫ f = z := by
  intro K _ A _ X L hL π k k' m σ hva s₀ t₀ t ⟨a, ha⟩ Y x y hdom hrat
  haveI := hdom
  obtain ⟨hcov, hloc⟩ := hva
  obtain ⟨q, hq⟩ := x.left.denseRange.exists_mem_open (π ⁻¹ᵁ nonzeroLocus t₀).isOpen ⟨a, ha⟩
  obtain ⟨i₀, hi₀⟩ := TopologicalSpace.Opens.mem_iSup.1
    (show y.left q ∈ ⨆ i, π ⁻¹ᵁ nonzeroLocus (σ i) by rw [hcov]; trivial)
  obtain ⟨hD, r, hr, hsurj⟩ := hloc i₀
  obtain ⟨jx, hjx⟩ := exists_chart hL (π (x.left q))
  obtain ⟨jy, hjy⟩ := exists_chart hL (π (y.left q))
  let c : Fin 1 → L.ι := fun _ => jx
  let c' : Fin 1 → L.ι := fun _ => jy
  have hcx : (x.left ≫ π) q ∈ secChart L c := Set.mem_iInter.2 fun _ => hjx
  have hcy : (y.left ≫ π) q ∈ secChart L c' := Set.mem_iInter.2 fun _ => hjy
  have e := secRatioEq_iff_germ.1 (hrat i₀) q c' c hcy hcx
  have u1 : IsUnit (secGerm (y.left ≫ π) q (σ i₀) c') := (GlobalTheory.mem_nonzeroLocus_iff_pull (σ i₀) (y.left ≫ π) q hcy).1 hi₀
  have u2 : IsUnit (secGerm (x.left ≫ π) q t₀ c) := (GlobalTheory.mem_nonzeroLocus_iff_pull t₀ (x.left ≫ π) q hcx).1 hq
  have u3 : IsUnit (secGerm (x.left ≫ π) q (t i₀) c) := by
    have h := u1.mul u2
    rw [e] at h
    exact isUnit_of_mul_isUnit_right h
  let W₀ : A.left.Opens := π ⁻¹ᵁ secChart L c
  let b : H0 L k' → Γ(A.left, W₀) := fun s => (π.app (secChart L c)).hom (s.f c)
  let V : A.left.Opens := A.left.basicOpen (b t₀ * b (t i₀))
  have hVW : V ≤ W₀ := A.left.basicOpen_le _
  have hb : ∀ {Z : Scheme.{0}} (g : Z ⟶ A.left) (w : Z) (_ : g w ∈ W₀) (s : H0 L k'),
      gs g w W₀ (b s) = secGerm (g ≫ π) w s c := fun g w hw s => gs_pull g π w _ hw _
  have memV : ∀ {Z : Scheme.{0}} (g : Z ⟶ A.left) (w : Z), g w ∈ V → (g ≫ π) w ∈ secChart L c ∧
      IsUnit (secGerm (g ≫ π) w t₀ c) ∧ IsUnit (secGerm (g ≫ π) w (t i₀) c) := by
    intro Z g w hw
    have hW : g w ∈ W₀ := hVW hw
    have h := (GlobalTheory.LBGerm.isUnit_gs_iff g w W₀ hW _).2 hw
    rw [gs_mul g w W₀ hW, hb g w hW, hb g w hW] at h
    exact ⟨hW, isUnit_of_mul_isUnit_left h, isUnit_of_mul_isUnit_right h⟩
  have hxq : x.left q ∈ V :=
    (GlobalTheory.LBGerm.isUnit_gs_iff x.left q W₀ hcx (b t₀ * b (t i₀))).1
      (by rw [gs_mul _ q W₀ hcx, hb _ q hcx, hb _ q hcx]; exact u2.mul u3)
  have hu : IsUnit ((A.left.presheaf.map (homOfLE hVW).op).hom (b (t i₀))) := by
    have h := A.left.toRingedSpace.isUnit_res_basicOpen (b t₀ * b (t i₀))
    rw [map_mul] at h
    exact isUnit_of_mul_isUnit_right h
  let ρ : Fin (m + 1) → Γ(A.left, V) := fun l =>
    (A.left.presheaf.map (homOfLE hVW).op).hom (b (t l)) * ↑hu.unit⁻¹
  have hρ : ∀ {Z : Scheme.{0}} (g : Z ⟶ A.left) (w : Z) (_ : g w ∈ V) (l : Fin (m + 1)),
      gs g w V (ρ l) * secGerm (g ≫ π) w (t i₀) c = secGerm (g ≫ π) w (t l) c := by
    intro Z g w hw l
    have hW : g w ∈ W₀ := hVW hw
    have one : gs g w V 1 = 1 := by rw [gs_eq g w V hw, map_one, map_one]
    rw [← hb g w hW, ← hb g w hW, ← gs_res g w hVW hw (b (t i₀)), ← gs_res g w hVW hw (b (t l)),
      gs_mul g w V hw, _root_.mul_assoc, ← gs_mul g w V hw, hu.val_inv_mul, one, _root_.mul_one]
  let ev := MvPolynomial.eval₂Hom (AbLaw.cst A.hom (π ⁻¹ᵁ nonzeroLocus (σ i₀))) r
  let ev' := MvPolynomial.eval₂Hom (AbLaw.cst A.hom V) ρ
  have transfer : ∀ {Z : Scheme.{0}} (g z : Z ⟶ A.left) (w : Z), g w ∈ V → g ≫ A.hom = z ≫ A.hom →
      (∀ i, SecRatioEq L (z ≫ π) (g ≫ π) (σ i) s₀ (t i) t₀) →
      z w ∈ π ⁻¹ᵁ nonzeroLocus (σ i₀) ∧ ∀ P, gs g w V (ev' P) = gs z w _ (ev P) := by
    intro Z g z w hw hp hrt
    obtain ⟨hc, h0, hi⟩ := memV g w hw
    obtain ⟨hzD, hR⟩ := ratMap_key hL π σ hcov s₀ t₀ t i₀ r hr c g z w hc h0 hi hrt
    refine ⟨hzD, ratMap_gs_eval₂ g z w hw hzD _ _ ρ r (fun a => ?_) (fun l => (hR l _ (hρ g w hw l)).symm)⟩
    rw [ratMap_gs_cst A.hom g V w hw, ratMap_gs_cst A.hom z _ w hzD, hp]
  have hker : RingHom.ker ev ≤ RingHom.ker ev' := by
    intro P hP
    rw [RingHom.mem_ker] at hP ⊢
    apply app_injective_of_isDominant x.left V
    rw [map_zero]
    refine fn_ext fun w hw => ?_
    have tr := transfer x.left y.left w hw ((Over.w x).trans (Over.w y).symm) hrat
    rw [gs_pull (𝟙 _) x.left w V hw, Category.id_comp, tr.2 P, hP, GlobalTheory.LBGerm.gs_zero _ _ _ tr.1,
      GlobalTheory.LBGerm.gs_zero _ _ _ hw]
  let θ := (RingHom.liftOfSurjective ev hsurj) ⟨ev', hker⟩
  have hθ : ∀ P, θ (ev P) = ev' P := RingHom.liftOfSurjective_comp_apply ev hsurj ⟨ev', hker⟩
  let f₀ : V.toScheme ⟶ A.left := V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ) ≫ hD.fromSpec
  have hf₀ : ∀ {Z : Scheme.{0}} (u : Z ⟶ V.toScheme) (w : Z), (u ≫ f₀) w ∈ π ⁻¹ᵁ nonzeroLocus (σ i₀) ∧
      ∀ P, gs (u ≫ f₀) w _ (ev P) = gs (u ≫ V.ι) w V (ev' P) := fun u w => by
    obtain ⟨h1, h2⟩ := ratMap_gs_ofRingHom hD V θ u w
    exact ⟨h1, fun P => (h2 (ev P)).trans (by rw [hθ])⟩
  have hmem : ∀ {Z : Scheme.{0}} (u : Z ⟶ V.toScheme) (w : Z), (u ≫ V.ι) w ∈ V := fun u w => (u w).2
  have hover : f₀ ≫ A.hom = V.ι ≫ A.hom := by
    refine ratMap_eq_of_gs_eq _ _ (isAffineOpen_top (Sp K)) (fun _ => trivial) (fun _ => trivial) fun a w => ?_
    obtain ⟨a', rfl⟩ : ∃ a' : K, (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a' = a :=
      ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom a, by simp⟩
    have h := hf₀ (𝟙 V.toScheme) w
    have hc := h.2 (MvPolynomial.C a')
    rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, ratMap_gs_cst _ _ _ w h.1,
      ratMap_gs_cst _ _ _ w (hmem (𝟙 _) w)] at hc
    simpa only [Category.id_comp] using hc
  refine ⟨Over.mk (V.ι ≫ A.hom), Over.homMk V.ι rfl, Over.homMk f₀ hover, ?_, ⟨⟨x.left q, hxq⟩⟩, ?_⟩
  · exact (inferInstance : IsOpenImmersion V.ι)
  · intro Z u z hz
    apply Over.OverMorphism.ext
    change u.left ≫ f₀ = z.left
    have hz' : ∀ i, SecRatioEq L (z.left ≫ π) ((u.left ≫ V.ι) ≫ π) (σ i) s₀ (t i) t₀ := hz
    have hp : (u.left ≫ V.ι) ≫ A.hom = z.left ≫ A.hom := by
      rw [Category.assoc]
      exact (Over.w u).trans (Over.w z).symm
    refine ratMap_eq_of_gs_eq _ _ hD (fun w => (hf₀ u.left w).1)
      (fun w => (transfer _ _ w (hmem u.left w) hp hz').1) fun b' w => ?_
    obtain ⟨P, rfl⟩ := hsurj b'
    exact ((hf₀ u.left w).2 P).trans ((transfer _ _ w (hmem u.left w) hp hz').2 P)

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMorphismOfSectionRatiosVeryAmpleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_morphism_of_sectionRatios_veryAmple : ∀ (K : Type) [Field K] (A : Over (Sp K)) [IsIntegral A.left] (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (π : A.left ⟶ X) (k k' m : ℕ) (σ : Fin (m + 1) → H0 L k), VeryAmpleAlong A.hom π L σ → ∀ (s₀ : H0 L k) (t₀ : H0 L k') (t : Fin (m + 1) → H0 L k'), (∃ a : A.left, π a ∈ nonzeroLocus t₀) → ∀ (Y : Over (Sp K)) (x y : Y ⟶ A), IsDominant x.left → (∀ i, SecRatioEq L (y.left ≫ π) (x.left ≫ π) (σ i) s₀ (t i) t₀) → ∃ (V : Over (Sp K)) (j f : V ⟶ A), IsOpenImmersion j.left ∧ Nonempty V.left ∧ ∀ (Z : Over (Sp K)) (u : Z ⟶ V) (z : Z ⟶ A), (∀ i, SecRatioEq L (z.left ≫ π) ((u ≫ j).left ≫ π) (σ i) s₀ (t i) t₀) → u ≫ f = z := by
  first | exact @GlobalTheory.Mum.exists_morphism_of_secRatio | exact GlobalTheory.Mum.exists_morphism_of_secRatio | (intros; apply GlobalTheory.Mum.exists_morphism_of_secRatio <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulOfMulAtDominantPairCommGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulOfMulAtDominantPairCommGroup
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem mul_of_isDominant_pair : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], GlobalTheory.SS.SmConn A → ∀ (V : Over (Sp K)) (j f : V ⟶ A), IsOpenImmersion j.left → ∀ (Y : Over (Sp K)) (x₁ x₂ y₁ y₂ : Y ⟶ A), IsDominant (lift x₁ x₂).left → (∀ (Z : Over (Sp K)) (w : Z ⟶ Y) (u : Z ⟶ V), u ≫ j = w ≫ x₁ → u ≫ f = w ≫ y₁) → (∀ (Z : Over (Sp K)) (w : Z ⟶ Y) (u : Z ⟶ V), u ≫ j = w ≫ x₂ → u ≫ f = w ≫ y₂) → (∀ (Z : Over (Sp K)) (w : Z ⟶ Y) (u : Z ⟶ V), u ≫ j = w ≫ (x₁ * x₂) → u ≫ f = w ≫ (y₁ * y₂)) → ∀ (Z : Over (Sp K)) (u₁ u₂ u₃ : Z ⟶ V), (u₁ ≫ j) * (u₂ ≫ j) = u₃ ≫ j → (u₁ ≫ f) * (u₂ ≫ f) = u₃ ≫ f := by
  intro K _ A _ hA V j f hj Y x₁ x₂ y₁ y₂ hdom h₁ h₂ h₃ Z u₁ u₂ u₃ hu
  obtain ⟨_, hsm, hsep, _, _⟩ := hA
  let R : A.left.Opens := j.left.opensRange
  let U : (A ⊗ A).left.Opens :=
    (fst A A).left ⁻¹ᵁ R ⊓ (snd A A).left ⁻¹ᵁ R ⊓ (fst A A * snd A A).left ⁻¹ᵁ R
  let W : Over (Sp K) := Over.mk (U.ι ≫ (A ⊗ A).hom)
  let ιW : W ⟶ A ⊗ A := Over.homMk U.ι rfl
  have : IsOpenImmersion ιW.left := inferInstanceAs (IsOpenImmersion U.ι)
  have hWU : ∀ q : W.left, ιW.left q ∈ U := fun q => (Scheme.Opens.range_ι U).subset ⟨q, rfl⟩
  have hR : ∀ (g : A ⊗ A ⟶ A) (q : W.left), ιW.left q ∈ g.left ⁻¹ᵁ R →
      (ιW ≫ g).left q ∈ Set.range j.left := fun g q h => by
    rw [Over.comp_left, Scheme.Hom.comp_apply]; exact h
  obtain ⟨v₁, hv₁⟩ := GlobalTheory.GenericHom.exists_lift j (ιW ≫ fst A A) fun q => hR _ q (hWU q).1.1
  obtain ⟨v₂, hv₂⟩ := GlobalTheory.GenericHom.exists_lift j (ιW ≫ snd A A) fun q => hR _ q (hWU q).1.2
  obtain ⟨v₃, hv₃⟩ := GlobalTheory.GenericHom.exists_lift j (ιW ≫ (fst A A * snd A A)) fun q => hR _ q (hWU q).2
  have : Smooth (A ⊗ A).hom := inferInstanceAs (Smooth (pullback.fst A.hom A.hom ≫ A.hom))
  have : Smooth W.hom := inferInstanceAs (Smooth (U.ι ≫ (A ⊗ A).hom))
  have := GlobalTheory.isNormalScheme_of_smooth (S := Spec (.of K)) W.hom
  have : IsReduced W.left := GlobalTheory.IsNormalScheme.isReduced
  let Y' : Y.left.Opens := (lift x₁ x₂).left ⁻¹ᵁ U
  let Z' : Over (Sp K) := Over.mk (Y'.ι ≫ Y.hom)
  let w : Z' ⟶ Y := Over.homMk Y'.ι rfl
  let p : Z' ⟶ W := Over.homMk ((lift x₁ x₂).left ∣_ U) (by
    show (lift x₁ x₂).left ∣_ U ≫ U.ι ≫ (A ⊗ A).hom = Y'.ι ≫ Y.hom
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w])
  have hpw : p ≫ ιW = w ≫ lift x₁ x₂ := Over.OverMorphism.ext (morphismRestrict_ι _ _)
  have : IsDominant p.left := IsZariskiLocalAtTarget.restrict hdom U
  have e₁ : p ≫ v₁ ≫ f = w ≫ y₁ :=
    h₁ Z' w (p ≫ v₁) (by rw [Category.assoc, hv₁, ← Category.assoc, hpw, Category.assoc, lift_fst])
  have e₂ : p ≫ v₂ ≫ f = w ≫ y₂ :=
    h₂ Z' w (p ≫ v₂) (by rw [Category.assoc, hv₂, ← Category.assoc, hpw, Category.assoc, lift_snd])
  have e₃ : p ≫ v₃ ≫ f = w ≫ (y₁ * y₂) :=
    h₃ Z' w (p ≫ v₃) (by
      rw [Category.assoc, hv₃, ← Category.assoc, hpw, Category.assoc, MonObj.comp_mul, lift_fst, lift_snd])
  have key : (v₁ ≫ f) * (v₂ ≫ f) = v₃ ≫ f := by
    refine Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated A.hom ?_ p.left ?_)
    · rw [Over.w, Over.w]
    · have : p ≫ ((v₁ ≫ f) * (v₂ ≫ f)) = p ≫ (v₃ ≫ f) := by
        rw [MonObj.comp_mul, e₁, e₂, e₃, MonObj.comp_mul]
      exact congrArg CommaMorphism.left this
  have hU : ∀ q : Z.left, (lift (u₁ ≫ j) (u₂ ≫ j)).left q ∈ Set.range ιW.left := by
    intro q
    show _ ∈ Set.range U.ι
    rw [Scheme.Opens.range_ι]
    have hq : ∀ (g : A ⊗ A ⟶ A) (u : Z ⟶ V), lift (u₁ ≫ j) (u₂ ≫ j) ≫ g = u ≫ j →
        (lift (u₁ ≫ j) (u₂ ≫ j)).left q ∈ g.left ⁻¹ᵁ R := fun g u e => by
      show g.left ((lift (u₁ ≫ j) (u₂ ≫ j)).left q) ∈ Set.range j.left
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, e]
      exact ⟨u.left q, by rw [Over.comp_left, Scheme.Hom.comp_apply]⟩
    exact ⟨⟨hq _ u₁ (lift_fst _ _), hq _ u₂ (lift_snd _ _)⟩,
      hq _ u₃ (by rw [MonObj.comp_mul, lift_fst, lift_snd, hu])⟩
  obtain ⟨g, hg⟩ := GlobalTheory.GenericHom.exists_lift ιW (lift (u₁ ≫ j) (u₂ ≫ j)) hU
  have canc : ∀ a b : Z ⟶ V, a ≫ j = b ≫ j → a = b := fun a b e =>
    Over.OverMorphism.ext ((cancel_mono j.left).1 (congrArg CommaMorphism.left e))
  have c₁ : g ≫ v₁ = u₁ := canc _ _ (by rw [Category.assoc, hv₁, ← Category.assoc, hg, lift_fst])
  have c₂ : g ≫ v₂ = u₂ := canc _ _ (by rw [Category.assoc, hv₂, ← Category.assoc, hg, lift_snd])
  have c₃ : g ≫ v₃ = u₃ := canc _ _ (by
    rw [Category.assoc, hv₃, ← Category.assoc, hg, MonObj.comp_mul, lift_fst, lift_snd, hu])
  rw [← c₁, ← c₂, ← c₃, Category.assoc, Category.assoc, Category.assoc, ← MonObj.comp_mul, key]

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulOfMulAtDominantPairCommGroupStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mul_of_mul_at_dominant_pair_commGroup : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], GlobalTheory.SS.SmConn A → ∀ (V : Over (Sp K)) (j f : V ⟶ A), IsOpenImmersion j.left → ∀ (Y : Over (Sp K)) (x₁ x₂ y₁ y₂ : Y ⟶ A), IsDominant (lift x₁ x₂).left → (∀ (Z : Over (Sp K)) (w : Z ⟶ Y) (u : Z ⟶ V), u ≫ j = w ≫ x₁ → u ≫ f = w ≫ y₁) → (∀ (Z : Over (Sp K)) (w : Z ⟶ Y) (u : Z ⟶ V), u ≫ j = w ≫ x₂ → u ≫ f = w ≫ y₂) → (∀ (Z : Over (Sp K)) (w : Z ⟶ Y) (u : Z ⟶ V), u ≫ j = w ≫ (x₁ * x₂) → u ≫ f = w ≫ (y₁ * y₂)) → ∀ (Z : Over (Sp K)) (u₁ u₂ u₃ : Z ⟶ V), (u₁ ≫ j) * (u₂ ≫ j) = u₃ ≫ j → (u₁ ≫ f) * (u₂ ≫ f) = u₃ ≫ f := by
  first | exact @GlobalTheory.Mum.mul_of_isDominant_pair | exact GlobalTheory.Mum.mul_of_isDominant_pair | (intros; apply GlobalTheory.Mum.mul_of_isDominant_pair <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericFibreHomOfFormalSectionRatios
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.GenericRatio

theorem exists_complete_point (T : Scheme.{0}) [IsLocallyNoetherian T] (t : T) :
    ∃ (B : Type) (_ : CommRing B) (_ : IsLocalRing B), IsAdicComplete (maximalIdeal B) B ∧
      ∃ q : Sp B ⟶ T, Flat q ∧ q (closedPoint B) = t := by
  let O : Type := T.presheaf.stalk t
  have : IsNoetherianRing O := inferInstanceAs (IsNoetherianRing (T.presheaf.stalk t))
  refine ⟨AdicCompletion (maximalIdeal O) O, inferInstance, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap O (AdicCompletion (maximalIdeal O) O))) ≫ T.fromSpecStalk t, ?_, ?_⟩
  · have h1 : Flat (T.fromSpecStalk t) := GenericExt.flat_fromSpecStalk T t
    have h2 : Flat (Spec.map (CommRingCat.ofHom (algebraMap O (AdicCompletion (maximalIdeal O) O)))) := by
      rw [HasRingHomProperty.Spec_iff (P := @Flat)]
      exact RingHom.flat_algebraMap_iff.2 inferInstance
    exact Flat.comp _ _
  · have : IsLocalHom (CommRingCat.ofHom (algebraMap O (AdicCompletion (maximalIdeal O) O))).hom :=
      inferInstanceAs (IsLocalHom (algebraMap O (AdicCompletion (maximalIdeal O) O)))
    exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg (T.fromSpecStalk t) Spec_closedPoint).trans
      Scheme.fromSpecStalk_closedPoint)

theorem secRatioEq_of_levels {B : Type} [CommRing B] [IsLocalRing B] [IsHausdorff (maximalIdeal B) B]
    {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {k k' : ℕ} {u v : Sp B ⟶ X} {s₁ s₂ : H0 L k} {t₁ t₂ : H0 L k'}
    (h : ∀ e, SecRatioEq L (thick B (maximalIdeal B) e ≫ u) (thick B (maximalIdeal B) e ≫ v) s₁ s₂ t₁ t₂) :
    SecRatioEq L u v s₁ s₂ t₁ t₂ := by
  have top : ∀ w : Sp B ⟶ X, ∃ i : Fin 1 → L.ι, ⊤ ≤ w ⁻¹ᵁ secChart L i := fun w => by
    obtain ⟨i, hi⟩ := exists_chart hL (w (closedPoint B))
    have : closedPoint B ∈ w ⁻¹ᵁ secChart L (fun _ => i) := Set.mem_iInter.2 fun _ => hi
    exact ⟨fun _ => i, ((IsLocalRing.closedPoint_mem_iff _).1 this).ge⟩
  obtain ⟨i, hi⟩ := top u
  obtain ⟨i', hi'⟩ := top v
  have key : ∀ (s : H0 L k) (t : H0 L k') (Z : Scheme.{0}) (r : Z ⟶ Sp B) (z : Z),
      gs r z ⊤ ((u.appLE _ ⊤ hi).hom (s.f i) * (v.appLE _ ⊤ hi').hom (t.f i')) =
        secGerm (r ≫ u) z s i * secGerm (r ≫ v) z t i' := fun s t Z r z =>
    (gs_mul r z ⊤ trivial _ _).trans (congrArg₂ (· * ·) (gs_appLE u _ ⊤ hi r z trivial _)
      (gs_appLE v _ ⊤ hi' r z trivial _))
  have E := GlobalTheory.FormalGeneric.fn_ext_germs (maximalIdeal B) (a := (u.appLE _ ⊤ hi).hom (s₁.f i) *
      (v.appLE _ ⊤ hi').hom (t₂.f i')) (b := (u.appLE _ ⊤ hi).hom (s₂.f i) * (v.appLE _ ⊤ hi').hom (t₁.f i'))
    fun e z => (key _ _ _ _ z).trans ((secRatioEq_iff_germ.1 (h e) z i i' (hi trivial) (hi' trivial)).trans
      (key _ _ _ _ z).symm)
  refine secRatioEq_of_exists_germ fun y => ⟨i, i', hi trivial, hi' trivial, ?_⟩
  exact (key s₁ t₂ _ (𝟙 _) y).symm.trans ((congrArg _ E).trans (key s₂ t₁ _ (𝟙 _) y))

theorem exists_generic_mem {R : Type} [CommRing R] [IsDomain R] {Y : Scheme.{0}} (f : Y ⟶ Sp R) [Flat f]
    (W : Y.Opens) {y : Y} (hy : y ∈ W) : ∃ a : (pullback f (jK R) :), pullback.fst f (jK R) a ∈ W := by
  let ξ : Sp R := jK R (closedPoint (FractionRing R))
  have hξ : ξ ⤳ f y := by
    refine (PrimeSpectrum.le_iff_specializes _ _).1 fun r hr => ?_
    have h1 : algebraMap R (FractionRing R) r ∈ maximalIdeal (FractionRing R) := hr
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot,
      map_eq_zero_iff _ (IsFractionRing.injective R (FractionRing R))] at h1
    rw [h1]
    exact Ideal.zero_mem _
  obtain ⟨y', h1, h2⟩ := Flat.generalizingMap f hξ
  have : y' ∈ Set.range (pullback.fst f (jK R)) := by
    rw [Scheme.Pullback.range_fst]
    exact ⟨_, h2.symm⟩
  obtain ⟨a, ha⟩ := this
  exact ⟨a, ha ▸ h1.mem_open W.isOpen hy⟩

theorem isDominant_of_flat {X Y : Scheme.{0}} [IrreducibleSpace X] (f : Y ⟶ X) [Flat f] (y : Y) : IsDominant f := by
  obtain ⟨y', -, h2⟩ := Flat.generalizingMap f (genericPoint_specializes (f y))
  refine ⟨Dense.mono (Set.singleton_subset_iff.2 ⟨y', h2⟩) ?_⟩
  exact dense_iff_closure_eq.2 (genericPoint_spec X)

theorem exists_formal_pair {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (G : Over (Sp R)) [GrpObj G] [LocallyOfFiniteType G.hom]
    (b : ∀ e : ℕ, thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G) (hb : ∀ e, IsMonHom (b e))
    (hc : ∀ e, thickMap R (maximalIdeal R) e G ≫ (b (e + 1)).left = (b e).left ≫ thickMap R (maximalIdeal R) e G)
    {L : LB G.left} (hL : L.IsLB) :
    ∃ (Y : Over (Sp R)) (x₁ x₂ : Y ⟶ G) (Φ : (Y ⟶ G) → (Y ⟶ G)), Nonempty Y.left ∧ Flat (lift x₁ x₂).left ∧
      (∀ x y, Φ (x * y) = Φ x * Φ y) ∧ ∀ (x : Y ⟶ G) (k k' : ℕ) (s₁ s₂ : H0 L k) (t₁ t₂ : H0 L k'),
        (∀ e, SecRatioEq L ((b e).left ≫ (fstG (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left
          s₁ s₂ t₁ t₂) → SecRatioEq L (Φ x).left x.left s₁ s₂ t₁ t₂ := by
  have : LocallyOfFiniteType (G ⊗ G).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst G.hom G.hom ≫ G.hom))
  have : IsLocallyNoetherian (G ⊗ G).left := LocallyOfFiniteType.isLocallyNoetherian (G ⊗ G).hom
  let o : 𝟙_ (Over (Sp R)) ⟶ G ⊗ G := lift 1 1
  obtain ⟨B, _, _, hB, q, hq, hqt⟩ := exists_complete_point (G ⊗ G).left (o.left (closedPoint R))
  have hs : (q ≫ (G ⊗ G).hom) (closedPoint B) ∈ Set.range (thick R (maximalIdeal R) 0) := by
    have h1 : (q ≫ (G ⊗ G).hom) (closedPoint B) = closedPoint R :=
      (Scheme.Hom.comp_apply _ _ _).trans ((congrArg (G ⊗ G).hom hqt).trans
        ((Scheme.Hom.comp_apply _ _ _).symm.trans (congrArg (fun g => g (closedPoint R)) (Over.w o))))
    exact ⟨_, (GlobalTheory.adicLevelι_closedPoint (maximalIdeal.isMaximal R).ne_top 0).trans h1.symm⟩
  obtain ⟨Φ, hΦ, hr⟩ := GlobalTheory.T.exists_additive_action_thickeningEndos_completePoints R (maximalIdeal R) G b hb hc B (q ≫ (G ⊗ G).hom) hs
  let q' : Over.mk (q ≫ (G ⊗ G).hom) ⟶ G ⊗ G := Over.homMk q rfl
  refine ⟨Over.mk (q ≫ (G ⊗ G).hom), q' ≫ fst G G, q' ≫ snd G G, Φ, ⟨closedPoint B⟩, ?_, hΦ,
    fun x k k' s₁ s₂ t₁ t₂ h => secRatioEq_of_levels hL fun e => ?_⟩
  · rw [lift_comp_fst_snd]
    exact hq
  · obtain ⟨r, h1, h2⟩ := hr x e
    have h3 := (h e).comp r
    exact h1 ▸ h2 ▸ h3

theorem exists_generic_hom : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (N : ℕ) (S : ∀ k : ℕ, H0 U.LG.L k → H0 U.LG.L (N * k)), 1 ≤ N → (∀ (k e : ℕ) (s₁ s₂ : H0 U.LG.L k), SecRatioEq U.LG.L ((b e).left ≫ (fstG (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left s₁ s₂ (S k s₁) (S k s₂)) → (∀ k : ℕ, 3 ≤ k → ∃ s₀ : H0 U.LG.L k, SecCoNonzero U.LG.L ((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left s₀ (S k s₀)) → ∃ φ : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G, IsMonHom φ ∧ (∀ (k : ℕ) (s₁ s₂ : H0 U.LG.L k), SecRatioEq U.LG.L (φ.left ≫ pullback.fst G.hom (jK R)) (pullback.fst G.hom (jK R)) s₁ s₂ (S k s₁) (S k s₂)) := by
  intro R _ _ _ hR D A G _ _ hG U a a' h h' _ b hb N S _ hS hnd
  have := hR.1.1
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  let F := Over.pullback (jK R)
  let π : (F.obj G).left ⟶ G.left := pullback.fst G.hom (jK R)
  have hA : GlobalTheory.SS.SmConn (F.obj G) := ⟨inferInstance, inferInstanceAs (Smooth (pullback.snd G.hom (jK R))),
    inferInstanceAs (IsSeparated (pullback.snd G.hom (jK R))),
    inferInstanceAs (QuasiCompact (pullback.snd G.hom (jK R))),
    inferInstanceAs (GeometricallyConnected (pullback.snd G.hom (jK R)))⟩
  have := hA.2.1
  have := hA.2.2.2.2
  have hint : IsIntegral (F.obj G).left := GlobalTheory.isIntegral_of_smooth_of_geometricallyConnected (F.obj G).hom
  obtain ⟨m, σ, hσ⟩ := GlobalTheory.T.exists_veryAmple_fourth_power_uniformised_group R (maximalIdeal R) D A G U
  obtain ⟨s₀, y₀, i₀, i₀', -, hy₀⟩ := hnd 4 (by norm_num)
  have ht₀ : ∃ p : (F.obj G).left, π p ∈ nonzeroLocus (S 4 s₀) := by
    refine exists_generic_mem G.hom _ (y := (fstG (maximalIdeal R) 0 G).left y₀) ?_
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i₀', (Scheme.preimage_basicOpen _ _).ge hy₀⟩
  obtain ⟨Y, x₁, x₂, Φ, ⟨y⟩, hfl, hΦ, hrat⟩ := exists_formal_pair G b hb.1 hb.2.1 U.LG.isLB
  have hπ : ∀ x : Y ⟶ G, (F.map x).left ≫ π = pullback.fst Y.hom (jK R) ≫ x.left := fun x =>
    pullback.lift_fst _ _ _
  have hratK : ∀ (x : Y ⟶ G) (k : ℕ) (s₁ s₂ : H0 U.LG.L k), SecRatioEq U.LG.L ((F.map (Φ x)).left ≫ π)
      ((F.map x).left ≫ π) s₁ s₂ (S k s₁) (S k s₂) := fun x k s₁ s₂ => by
    rw [hπ, hπ]
    exact (hrat x k _ s₁ s₂ _ _ fun e => hS k e s₁ s₂).comp _
  have hflK : Flat (lift (F.map x₁) (F.map x₂)).left := by
    rw [← Functor.OplaxMonoidal.lift_δ, Over.comp_left]
    have h1 : Flat (F.map (lift x₁ x₂)).left := MorphismProperty.overPullbackMap (P := @Flat) (jK R) _ hfl
    have h2 : IsIso (Functor.OplaxMonoidal.δ F G G).left :=
      inferInstanceAs (IsIso ((Over.forget _).map (Functor.OplaxMonoidal.δ F G G)))
    infer_instance
  have hYfl : Flat Y.hom := by
    have : Flat (G ⊗ G).hom := inferInstanceAs (Flat (pullback.fst G.hom G.hom ≫ G.hom))
    rw [← Over.w (lift x₁ x₂)]
    infer_instance
  obtain ⟨yK, -⟩ := exists_generic_mem Y.hom ⊤ (y := y) trivial
  have : Smooth (fst (F.obj G) (F.obj G)).left :=
    inferInstanceAs (Smooth (pullback.fst (F.obj G).hom (F.obj G).hom))
  have : GeometricallyConnected (fst (F.obj G) (F.obj G)).left :=
    inferInstanceAs (GeometricallyConnected (pullback.fst (F.obj G).hom (F.obj G).hom))
  have : IsIntegral (F.obj G ⊗ F.obj G).left := by
    have := GlobalTheory.isNormalScheme_of_smooth (S := Sp (FractionRing R)) (F.obj G).hom
    have : IsLocallyNoetherian (F.obj G).left := LocallyOfFiniteType.isLocallyNoetherian (F.obj G).hom
    exact GlobalTheory.isIntegral_of_smooth_of_geometricallyConnected (fst (F.obj G) (F.obj G)).left
  have hdom : IsDominant (lift (F.map x₁) (F.map x₂)).left := isDominant_of_flat _ yK
  have hfl₁ : Flat (F.map x₁).left := by
    rw [← lift_fst (F.map x₁) (F.map x₂), Over.comp_left]
    infer_instance
  have hdom₁ : IsDominant (F.map x₁).left := isDominant_of_flat _ yK
  obtain ⟨V, j, f, hj, hV, hf⟩ := GlobalTheory.T.exists_morphism_of_sectionRatios_veryAmple (FractionRing R) (F.obj G) G.left U.LG.L U.LG.isLB π 4 _ m σ hσ s₀
    (S 4 s₀) (fun i => S 4 (σ i)) ht₀ (F.obj Y) (F.map x₁) (F.map (Φ x₁)) hdom₁ fun i => hratK x₁ 4 _ _
  have hpt : ∀ (x : Y ⟶ G) (Z : Over (Sp (FractionRing R))) (w : Z ⟶ F.obj Y) (u : Z ⟶ V),
      u ≫ j = w ≫ F.map x → u ≫ f = w ≫ F.map (Φ x) := fun x Z w u e => hf Z u _ fun i => by
    rw [e, Over.comp_left, Over.comp_left, Category.assoc, Category.assoc]
    exact (hratK x 4 _ _).comp _
  have hadd := GlobalTheory.T.mul_of_mul_at_dominant_pair_commGroup (FractionRing R) (F.obj G) hA V j f hj (F.obj Y) _ _ _ _ hdom (hpt x₁) (hpt x₂)
    (by rw [← Functor.map_mul, ← Functor.map_mul, ← hΦ]; exact hpt (x₁ * x₂))
  obtain ⟨φ, hφ, hjφ⟩ := GlobalTheory.T.exists_monHom_extension_openPart_field (FractionRing R) (F.obj G) (F.obj G) V hA hA j f hj hV hadd
  refine ⟨φ, hφ, fun k s₁ s₂ => ?_⟩
  let Z : Over (Sp (FractionRing R)) := Over.mk (pullback.fst (F.map x₁).left j.left ≫ (F.obj Y).hom)
  let w : Z ⟶ F.obj Y := Over.homMk (pullback.fst (F.map x₁).left j.left) rfl
  let u : Z ⟶ V := Over.homMk (pullback.snd (F.map x₁).left j.left) (by
    have e := congrArg (· ≫ (F.obj G).hom) (pullback.condition (f := (F.map x₁).left) (g := j.left))
    simp only [Category.assoc, Over.w] at e
    exact e.symm)
  have huw : u ≫ j = w ≫ F.map x₁ := Over.OverMorphism.ext pullback.condition.symm
  have e : (w ≫ F.map x₁) ≫ φ = w ≫ F.map (Φ x₁) := by rw [← huw, Category.assoc, hjφ, hpt x₁ Z w u huw]
  obtain ⟨z⟩ : Nonempty Z.left := by
    obtain ⟨v⟩ := hV
    obtain ⟨p, v', hp⟩ := (F.map x₁).left.denseRange.exists_mem_open (IsOpenImmersion.isOpen_range j.left)
      ⟨_, v, rfl⟩
    obtain ⟨z, -⟩ := Scheme.Pullback.exists_preimage_pullback p v' hp.symm
    exact ⟨z⟩
  have : Flat (w ≫ F.map x₁).left :=
    inferInstanceAs (Flat (pullback.fst (F.map x₁).left j.left ≫ (F.map x₁).left))
  have := isDominant_of_flat (w ≫ F.map x₁).left z
  refine SecRatioEq.of_isDominant (Y := (F.obj G).left) (w ≫ F.map x₁).left ?_
  have e' : (w ≫ F.map x₁).left ≫ φ.left ≫ π = w.left ≫ (F.map (Φ x₁)).left ≫ π := by
    rw [← Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc]
  have h3 := (hratK x₁ k s₁ s₂).comp w.left
  rw [← e', ← Category.assoc w.left] at h3
  exact h3

end GlobalTheory.Mum.GenericRatio
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericFibreHomOfFormalSectionRatiosStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_genericFibreHom_of_formalSectionRatios : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (N : ℕ) (S : ∀ k : ℕ, H0 U.LG.L k → H0 U.LG.L (N * k)), 1 ≤ N → (∀ (k e : ℕ) (s₁ s₂ : H0 U.LG.L k), SecRatioEq U.LG.L ((b e).left ≫ (fstG (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left s₁ s₂ (S k s₁) (S k s₂)) → (∀ k : ℕ, 3 ≤ k → ∃ s₀ : H0 U.LG.L k, SecCoNonzero U.LG.L ((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left s₀ (S k s₀)) → ∃ φ : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G, IsMonHom φ ∧ (∀ (k : ℕ) (s₁ s₂ : H0 U.LG.L k), SecRatioEq U.LG.L (φ.left ≫ pullback.fst G.hom (jK R)) (pullback.fst G.hom (jK R)) s₁ s₂ (S k s₁) (S k s₂)) := by
  first | exact @GlobalTheory.Mum.GenericRatio.exists_generic_hom | exact GlobalTheory.Mum.GenericRatio.exists_generic_hom | (intros; apply GlobalTheory.Mum.GenericRatio.exists_generic_hom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianGenericFibreHomExtendsNormalNoetheria
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianGenericFibreHomExtendsNormalNoetheria
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.semiAbelian_end_generic_extends : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ φ : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G, IsMonHom φ → ∃ g : G ⟶ G, IsMonHom g ∧ (Over.pullback (jK R)).map g = φ := by
  intro R _ _ _ _ G _ hG φ hφ
  obtain ⟨F, ⟨hF, hF'⟩, -⟩ := GlobalTheory.semiAbelianHomExtension_holds.of_isGenericPointHom
    (GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec R)
    (GlobalTheory.IsGenericPointHom.fractionField R (FractionRing R)) hG hG φ
  exact ⟨F, hF, hF'⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianGenericFibreHomExtendsNormalNoetheriaStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelian_genericFibre_hom_extends_normal_noetherian : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ φ : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G, IsMonHom φ → ∃ g : G ⟶ G, IsMonHom g ∧ (Over.pullback (jK R)).map g = φ := by
  first | exact @GlobalTheory.Mum.semiAbelian_end_generic_extends | exact GlobalTheory.Mum.semiAbelian_end_generic_extends | (intros; apply GlobalTheory.Mum.semiAbelian_end_generic_extends <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordFormalEndomorphismAlgebraic
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem formalEnd_algebraic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ b, FormalEnd U.toUnifPre a h' b → ∃ g : G ⟶ G, IsMonHom g ∧ ∀ e, (Over.pullback (thick R (maximalIdeal R) e)).map g = b e := by
  intro R _ _ _ hR D A G _ _ hG U a a' h h' hE b hb
  obtain ⟨N, hN, S, hS, hnd⟩ := GlobalTheory.T.mumford_thickening_endomorphism_maps_sections R hR D A G hG U a a' h h' hE b hb
  obtain ⟨φ, hφ, hgen⟩ := GlobalTheory.T.exists_genericFibreHom_of_formalSectionRatios R hR D A G hG U a a' h h' hE b hb N S hN hS hnd
  have := hR.1.1
  have := hR.1.2.2.1
  obtain ⟨g, hg, hgφ⟩ := GlobalTheory.T.semiAbelian_genericFibre_hom_extends_normal_noetherian R G hG φ hφ
  exact ⟨g, hg, GlobalTheory.T.thickening_eq_of_generic_section_ratios R hR D A G hG U a a' h h' hE b hb N S hS hnd φ hgen g hg hgφ⟩

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordFormalEndomorphismAlgebraicStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumford_formalEndomorphism_algebraic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ b, FormalEnd U.toUnifPre a h' b → ∃ g : G ⟶ G, IsMonHom g ∧ ∀ e, (Over.pullback (thick R (maximalIdeal R) e)).map g = b e := by
  first | exact @GlobalTheory.Mum.formalEnd_algebraic | exact GlobalTheory.Mum.formalEnd_algebraic | (intros; apply GlobalTheory.Mum.formalEnd_algebraic <;> assumption)
end
