module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueGlueSectionsPrincipalCover
public import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHolomorphicLieFrame

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FibreSectionNowhereZeroOfGenerates
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFibreSectionPowMulBaseChangeAway
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFibreSectionPowMulBaseChangeAway
noncomputable section

namespace GlobalTheory.Frames.SecLoc

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem appLE_bijective {Y Z : Scheme.{0}} (π : Z ⟶ Y) [IsOpenImmersion π] {V : Y.Opens} (hV : V ≤ π.opensRange)
    {V' : Z.Opens} (h : V' ≤ π ⁻¹ᵁ V) (h' : π ⁻¹ᵁ V ≤ V') : Function.Bijective (π.appLE V V' h).hom := by
  obtain rfl : V' = π ⁻¹ᵁ V := le_antisymm h h'
  rw [← Scheme.Hom.app_eq_appLE]
  haveI := π.isIso_app V hV
  exact ConcreteCategory.bijective_of_isIso (π.app V)

theorem exists_pow_mul_eq {Y Z : Scheme.{0}} [CompactSpace Y] [QuasiSeparatedSpace Y] (π : Z ⟶ Y)
    [IsOpenImmersion π] (a : Γ(Y, ⊤)) (ha : π.opensRange = Y.basicOpen a) {M : LB Y} (hM : M.IsLB)
    (U' : M.ι → Z.Opens) (h : ∀ i, U' i ≤ π ⁻¹ᵁ M.U i) (h' : ∀ i, π ⁻¹ᵁ M.U i ≤ U' i) (f : ∀ i, Γ(Z, U' i))
    (hf : ∀ i j, resG Z (inf_le_left : U' i ⊓ U' j ≤ U' i) (f i) =
      (π.appLE (M.U i ⊓ M.U j) (U' i ⊓ U' j) (inf_le_inf (h i) (h j))).hom (M.g i j).val *
        resG Z (inf_le_right : U' i ⊓ U' j ≤ U' j) (f j)) :
    ∃ (N : ℕ) (s : LB.Sec M), ∀ i, (π.appLE _ _ (h i)).hom (s.f i) =
      (π.appLE ⊤ (U' i) le_top).hom a ^ N * f i := by
  have k : ∀ i, U' i ≤ π ⁻¹ᵁ (π.opensRange ⊓ M.U i) := fun i z hz => ⟨⟨z, rfl⟩, h i hz⟩
  have hb : ∀ i, Function.Bijective (π.appLE _ _ (k i)).hom := fun i =>
    appLE_bijective π inf_le_left (k i) (fun z hz => h' i hz.2)
  choose t ht using fun i => (hb i).2 (f i)
  have hmem : t ∈ secOn M π.opensRange := fun i j => by
    have k₂ : U' i ⊓ U' j ≤ π ⁻¹ᵁ (π.opensRange ⊓ M.U i ⊓ M.U j) := fun z hz => ⟨k i hz.1, h j hz.2⟩
    apply (appLE_bijective π (inf_le_left.trans inf_le_left) k₂
      (fun z hz => ⟨h' i hz.1.2, h' j hz.2⟩)).1
    rw [map_mul, GlobalTheory.LB.appLE_resG, GlobalTheory.LB.appLE_resG, GlobalTheory.LB.appLE_resG]
    have := hf i j
    rw [← ht i, ← ht j, GlobalTheory.LB.resG_appLE, GlobalTheory.LB.resG_appLE] at this
    exact this
  haveI := GlobalTheory.LB.isQuasicoherent_toMod hM
  obtain ⟨N, u, hu⟩ := GlobalTheory.QCoh.Qcqs.exists_pow_smul_eq_res_of_qcqs (GlobalTheory.LB.toMod M)
    (U := ⊤) isCompact_univ isQuasiSeparated_univ a le_top ha (GlobalTheory.LB.mkSec t hmem)
  let s : LB.Sec M := ⟨fun i => resG Y (le_inf le_top le_rfl) (GlobalTheory.LB.coord u i), fun i j => by
    change resG Y _ (resG Y _ _) = _ * resG Y _ (resG Y _ _)
    rw [GlobalTheory.LB.resG_resG, GlobalTheory.LB.resG_resG, GlobalTheory.LB.coord_rel u i j _ _ le_rfl, GlobalTheory.LB.resG_self]⟩
  refine ⟨N, s, fun i => ?_⟩
  have e : resG Y inf_le_left (resG Y le_top a ^ N) * t i =
      resG Y (inf_le_inf_right _ le_top) (GlobalTheory.LB.coord u i) := congrArg (fun w => GlobalTheory.LB.coord w i) hu
  have e₂ := congrArg (π.appLE _ _ (k i)).hom e
  rw [map_mul, ht, map_pow, map_pow, GlobalTheory.LB.resG_resG, GlobalTheory.LB.appLE_resG, GlobalTheory.LB.appLE_resG] at e₂
  exact (GlobalTheory.LB.appLE_resG _ _ _ _).trans e₂.symm

theorem exists_pow_mul_eq_linComb {X Y Z : Scheme.{0}} [CompactSpace Y] [QuasiSeparatedSpace Y] (π : Z ⟶ Y)
    [IsOpenImmersion π] (a : Γ(Y, ⊤)) (ha : π.opensRange = Y.basicOpen a) {L : LB X} (hL : L.IsLB)
    {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (φ' : K → (Z ⟶ X)) (ε : K → ℤ) (e : (fun k => π ≫ φ k) = φ')
    (s' : LB.Sec (LB.LinComb L φ' ε)) :
    ∃ (N : ℕ) (s : LB.Sec (LB.LinComb L φ ε)), ∀ (j : K → L.ι)
      (hle : (LB.LinComb L φ' ε).U j ≤ π ⁻¹ᵁ (LB.LinComb L φ ε).U j), (π.appLE _ _ hle).hom (s.f j) =
        (π.appLE ⊤ _ le_top).hom a ^ N * s'.f j := by
  subst e
  obtain ⟨N, s, hs⟩ := exists_pow_mul_eq π a ha (M := LB.LinComb L φ ε) (LB.isLB_linComb hL φ ε)
    (LB.LinComb L (fun k => π ≫ φ k) ε).U
    (fun _ _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k)
    (fun _ _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k) s'.f (fun i j => by
      refine (s'.compat i j).trans (congrArg (· * _) ?_)
      exact congrArg Units.val (DVR.linComb_g_comp φ ε π i j))
  exact ⟨N, s, fun j _ => hs j⟩

theorem opensRange_of_isPullback {S : Type} [CommRing S] (g : S) {Y Z : Scheme.{0}} {π : Z ⟶ Y} {p : Y ⟶ Sp S}
    {p' : Z ⟶ Sp (Localization.Away g)} (h : IsPullback π p' p (spMap (algebraMap S (Localization.Away g))))
    [IsOpenImmersion π] : π.opensRange = Y.basicOpen (p.appTop.hom (toΓ S g)) := by
  have e : Y.basicOpen (p.appTop.hom (toΓ S g)) = p ⁻¹ᵁ PrimeSpectrum.basicOpen g :=
    (Scheme.preimage_basicOpen_top p _).symm.trans (congrArg (p ⁻¹ᵁ ·) (basicOpen_eq_of_affine (R := .of S) g))
  rw [e]
  ext y
  have r : Set.range (spMap (algebraMap S (Localization.Away g))) = (PrimeSpectrum.basicOpen g).1 :=
    PrimeSpectrum.localization_away_comap_range (Localization.Away g) g
  have r' := Scheme.Pullback.range_fst p (spMap (algebraMap S (Localization.Away g)))
  rw [r] at r'
  constructor
  · rintro ⟨z, rfl⟩
    have : π z ∈ Set.range (pullback.fst p (spMap (algebraMap S (Localization.Away g)))) :=
      ⟨h.isoPullback.hom z, by rw [← Scheme.Hom.comp_apply, h.isoPullback_hom_fst]⟩
    rw [r'] at this
    exact this
  · intro hy
    have : y ∈ Set.range (pullback.fst p (spMap (algebraMap S (Localization.Away g)))) := by
      rw [r']; exact hy
    obtain ⟨w, rfl⟩ := this
    exact ⟨h.isoPullback.inv w, by rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst]⟩

theorem appLE_const {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) {Y Z : Scheme.{0}} {π : Z ⟶ Y}
    {p : Y ⟶ Sp S} {p' : Z ⟶ Sp T} (w : π ≫ p = p' ≫ spMap φ) (U : Z.Opens) (a : S) :
    (π.appLE ⊤ U le_top).hom (p.appTop.hom (toΓ S a)) = resG Z le_top (p'.appTop.hom (toΓ T (φ a))) := by
  have e₁ : π.appTop.hom (p.appTop.hom (toΓ S a)) = p'.appTop.hom ((spMap φ).appTop.hom (toΓ S a)) := by
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, w]
  have e₂ : (spMap φ).appTop.hom (toΓ S a) = toΓ T (φ a) :=
    (congrArg (fun f => f.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))).symm
  rw [← e₂, ← e₁]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

theorem isPullback_gx {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) :
    IsPullback (snd (Over.mk x) Xo.univ.t.G).left (fst (Over.mk x) Xo.univ.t.G).left Xo.univ.t.G.hom x :=
  (IsPullback.of_hasPullback x Xo.univ.t.G.hom).flip

theorem isPullback_gxMap {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (x : Sp S ⟶ Xo.X) :
    IsPullback (SecPull.gxMap φ x _ rfl) (fst (Over.mk (spMap φ ≫ x)) Xo.univ.t.G).left
      (fst (Over.mk x) Xo.univ.t.G).left (spMap φ) :=
  IsPullback.of_right (by
    convert isPullback_gx (spMap φ ≫ x) using 1
    exact SecPull.gxMap_snd φ x _ rfl) (SecPull.gxMap_fst φ x _ rfl)
    (isPullback_gx x)

theorem exists_secBC_pow_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (g : S) (s' : LB.Sec (PPx (spMap (algebraMap S (Localization.Away g)) ≫ x))), ∃ (N : ℕ) (s : LB.Sec (PPx x)) (s₁ : LB.Sec (PPx (spMap (algebraMap S (Localization.Away g)) ≫ x))), SecBC (algebraMap S (Localization.Away g)) 1 x _ s s₁ ∧ ∀ i, s₁.f i = scal _ ((algebraMap S (Localization.Away g)) g ^ N) i * s'.f i := by
  intro E _ _ _ H Dw l Xo S _ x g s'
  have hP := isPullback_gxMap (algebraMap S (Localization.Away g)) x
  have hpr : IsProper (fst (Over.mk x) Xo.univ.t.G).left :=
    MorphismProperty.of_isPullback (P := @IsProper) (isPullback_gx x) Xo.univ.proper
  have : CompactSpace (Over.mk x).left := inferInstanceAs (CompactSpace (Sp S))
  have : QuasiSeparatedSpace (Over.mk x).left := inferInstanceAs (QuasiSeparatedSpace (Sp S))
  have : CompactSpace (Gx x) :=
    QuasiCompact.compactSpace_of_compactSpace (fst (Over.mk x) Xo.univ.t.G).left
  have : QuasiSeparatedSpace (Gx x) :=
    quasiSeparatedSpace_of_quasiSeparated (fst (Over.mk x) Xo.univ.t.G).left
  have hoi : IsOpenImmersion (spMap (algebraMap S (Localization.Away g))) :=
    IsOpenImmersion.of_isLocalization g
  have : IsOpenImmersion (SecPull.gxMap (algebraMap S (Localization.Away g)) x _ rfl) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hP.flip hoi
  obtain ⟨N, s, hs⟩ := exists_pow_mul_eq_linComb _ _ (opensRange_of_isPullback g hP) Xo.univ.t.PP.isLB
    (K := Fin 1) (fun _ => (snd (Over.mk x) Xo.univ.t.G).left)
    (fun _ => (snd (Over.mk (spMap (algebraMap S (Localization.Away g)) ≫ x)) Xo.univ.t.G).left) (fun _ => 1)
    (funext fun _ => SecPull.gxMap_snd _ x _ rfl) s'
  refine ⟨N, s, SecPull.scalSec _ (algebraMap S (Localization.Away g) g ^ N) s',
    ⟨_, SecPull.gxMap_snd _ x _ rfl, SecPull.gxMap_fst _ x _ rfl, fun i h => ?_⟩, fun _ => rfl⟩
  have e₁ : scal x 1 i = 1 := by simp only [scal, Out.liftFun, map_one]
  rw [e₁, _root_.one_mul]
  refine (hs i h).trans (congrArg (· * s'.f i) ?_)
  rw [appLE_const _ hP.w]
  simp only [scal, Out.liftFun, map_pow]
  rfl

end GlobalTheory.Frames.SecLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFibreSectionPowMulBaseChangeAwayStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fibreSection_pow_mul_baseChange_away : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (g : S) (s' : LB.Sec (PPx (spMap (algebraMap S (Localization.Away g)) ≫ x))), ∃ (N : ℕ) (s : LB.Sec (PPx x)) (s₁ : LB.Sec (PPx (spMap (algebraMap S (Localization.Away g)) ≫ x))), SecBC (algebraMap S (Localization.Away g)) 1 x _ s s₁ ∧ ∀ i, s₁.f i = scal _ ((algebraMap S (Localization.Away g)) g ^ N) i * s'.f i := by
  first | exact @GlobalTheory.Frames.SecLoc.exists_secBC_pow_mul | exact GlobalTheory.Frames.SecLoc.exists_secBC_pow_mul | (intros; apply GlobalTheory.Frames.SecLoc.exists_secBC_pow_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FibreSectionNowhereZeroOfGenerates
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem secNZ_of_secGen : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (s : LB.Sec (PPx x)), SecGen x s → SecNZ x s := by
  intro hbc E _ _ _ H Dw l Xo S _ x s hs p
  obtain ⟨g, hg, θ, hθ⟩ := GlobalTheory.T.exists_local_generator_stable_baseChange hbc E H Dw l Xo S x p
  have hid : ∀ (R : Type) [CommRing R] (z : Sp R ⟶ Xo.X), z = spMap (RingHom.id R) ≫ z := by
    intro R _ z
    have : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _
    rw [this, Category.id_comp]
  obtain ⟨-, hc2, -, hc4⟩ := GlobalTheory.T.scaledBaseChange_fibreSection_calculus E H Dw l Xo (Localization.Away g) (Localization.Away g)
    (Localization.Away g) (RingHom.id _) (RingHom.id _) (spMap (algebraMap S (Localization.Away g)) ≫ x)
    _ _ (hid _ _) (hid _ _)
  have hθθ : SecBC (RingHom.id (Localization.Away g)) 1 _ _ θ θ :=
    (hc2 1 θ θ).2 fun i => by rw [(hc4 1 1 i).2.2, _root_.one_mul]
  have hnz := (hθ _ (RingHom.id _) _ θ (hid _ _) hθθ).2
  obtain ⟨p', hp'⟩ : ∃ p' : PrimeSpectrum (Localization.Away g),
      PrimeSpectrum.comap (algebraMap S (Localization.Away g)) p' = p := by
    have h := PrimeSpectrum.localization_away_comap_range (Localization.Away g) g
    have : (p : PrimeSpectrum S) ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away g))) := by
      rw [h]; exact hg
    exact this
  obtain ⟨q, i, hq, hqi⟩ := hnz p'
  obtain ⟨N, s₀, s₁, h01, h1⟩ := GlobalTheory.T.exists_fibreSection_pow_mul_baseChange_away E H Dw l Xo S x g θ
  have hu : IsUnit (scal (spMap (algebraMap S (Localization.Away g)) ≫ x)
      ((algebraMap S (Localization.Away g)) g ^ N) i) := by
    obtain ⟨v, hv⟩ := ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away g) g).pow N).exists_right_inv
    refine IsUnit.of_mul_eq_one (scal _ v i) ?_
    rw [← (hc4 _ v i).1, hv, (hc4 1 1 i).2.2]
  have hq1 : q ∈ (Gx _).basicOpen (s₁.f i) := by
    rw [h1 i, Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ hu]
    exact ⟨Scheme.basicOpen_le _ _ hqi, hqi⟩
  obtain ⟨q₀, i₀, hq₀, hqi₀⟩ := (GlobalTheory.Frames.secBC_nonvanishing_iff E H Dw l Xo S (Localization.Away g) _ x _ rfl s₀ s₁ h01 p').1
    ⟨q, i, hq, hq1⟩
  obtain ⟨b, hb, -⟩ := hs s₀
  rw [hb i₀, Scheme.basicOpen_mul] at hqi₀
  exact ⟨q₀, i₀, hq₀.trans hp', hqi₀.2⟩

end GlobalTheory.Frames
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FibreSectionNowhereZeroOfGeneratesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibreSectionNowhereZero_of_generates : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (s : LB.Sec (PPx x)), SecGen x s → SecNZ x s := by
  first | exact @GlobalTheory.Frames.secNZ_of_secGen | exact GlobalTheory.Frames.secNZ_of_secGen | (intros; apply GlobalTheory.Frames.secNZ_of_secGen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FibreSectionGeneratesOfNowhereZero
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FibreSectionGeneratesOfNowhereZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

noncomputable section

namespace GlobalTheory.Frames.NonzeroGenerates

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl

theorem spMap_id' {A : Type} [CommRing A] : spMap (RingHom.id A) = 𝟙 (Sp A) :=
  Spec.map_id (CommRingCat.of A)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {S T U : Type} [CommRing S] [CommRing T] [CommRing U]

theorem eq_id_comp (x : Sp S ⟶ Xo.X) : x = spMap (RingHom.id S) ≫ x := by
  rw [spMap_id', Category.id_comp]

theorem scal_mul (x : Sp S ⟶ Xo.X) (a b : S) (i : (PPx x).ι) : scal x (a * b) i = scal x a i * scal x b i :=
  ((GlobalTheory.T.scaledBaseChange_fibreSection_calculus E H Dw l Xo S S S _ _ x x x (eq_id_comp x) (eq_id_comp x)).2.2.2 a b i).1

theorem scal_one (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) : scal x 1 i = 1 :=
  ((GlobalTheory.T.scaledBaseChange_fibreSection_calculus E H Dw l Xo S S S _ _ x x x (eq_id_comp x) (eq_id_comp x)).2.2.2 1 1 i).2.2

theorem secBC_id_iff (x : Sp S ⟶ Xo.X) (a : S) (s t : LB.Sec (PPx x)) :
    SecBC (RingHom.id S) a x x s t ↔ ∀ i, t.f i = scal x a i * s.f i :=
  (GlobalTheory.T.scaledBaseChange_fibreSection_calculus E H Dw l Xo S S S _ _ x x x (eq_id_comp x) (eq_id_comp x)).2.1 a s t

theorem exists_mul (x : Sp S ⟶ Xo.X) (a : S) (s : LB.Sec (PPx x)) :
    ∃ t : LB.Sec (PPx x), ∀ i, t.f i = scal x a i * s.f i := by
  obtain ⟨t, ht, -⟩ := GlobalTheory.T.existsUnique_scaledBaseChange_fibreSection E H Dw l Xo S S (RingHom.id S) a x x (eq_id_comp x) s
  exact ⟨t, (secBC_id_iff x a s t).1 ht⟩

theorem exists_pull (φ : S →+* T) (x : Sp S ⟶ Xo.X) (x' : Sp T ⟶ Xo.X) (hx : x' = spMap φ ≫ x)
    (s : LB.Sec (PPx x)) : ∃ s' : LB.Sec (PPx x'), SecBC φ 1 x x' s s' :=
  (GlobalTheory.T.existsUnique_scaledBaseChange_fibreSection E H Dw l Xo S T φ 1 x x' hx s).exists

theorem pull_trans_iff {φ : S →+* T} {ψ : T →+* U} {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X} {x'' : Sp U ⟶ Xo.X}
    (hx : x' = spMap φ ≫ x) (hx' : x'' = spMap ψ ≫ x') {a : S} {s s' s''} (h : SecBC φ a x x' s s') :
    SecBC ψ 1 x' x'' s' s'' ↔ SecBC (ψ.comp φ) a x x'' s s'' :=
  (GlobalTheory.T.scaledBaseChange_fibreSection_calculus E H Dw l Xo S T U φ ψ x x' x'' hx hx').1 a s s' s'' h

theorem pull_mul_iff {φ : S →+* T} {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X} (hx : x' = spMap φ ≫ x) {a : S}
    {s : LB.Sec (PPx x)} {s' t' : LB.Sec (PPx x')} (h : SecBC φ 1 x x' s s') :
    SecBC φ a x x' s t' ↔ ∀ i, t'.f i = scal x' (φ a) i * s'.f i :=
  (GlobalTheory.T.scaledBaseChange_fibreSection_calculus E H Dw l Xo S T T φ _ x x' x' hx (eq_id_comp x')).2.2.1 a s s' t' h

theorem pull_iff_of_mul {φ : S →+* T} {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X} (hx : x' = spMap φ ≫ x) {a : S}
    {s t : LB.Sec (PPx x)} {s' t' : LB.Sec (PPx x')} (hst : ∀ i, t.f i = scal x a i * s.f i)
    (h : SecBC φ 1 x x' s s') : SecBC φ 1 x x' t t' ↔ ∀ i, t'.f i = scal x' (φ a) i * s'.f i := by
  rw [pull_trans_iff (eq_id_comp x) hx ((secBC_id_iff x a s t).2 hst), RingHom.comp_id, pull_mul_iff hx h]

theorem not_mem_of_mem_basicOpen_scal (x : Sp S ⟶ Xo.X) (a : S) (i : (PPx x).ι) (q : Gx x)
    (hq : q ∈ (Gx x).basicOpen (scal x a i)) : a ∉ (Formalism.L2.PjFree.gxSnd x q).asIdeal := by
  have e : scal x a i = ((Formalism.L2.PjFree.gxSnd x).appLE ⊤ ((PPx x).U i) le_top).hom (toΓ S a) := rfl
  rw [e] at hq
  erw [Scheme.basicOpen_appLE] at hq
  have h2 := hq.2
  have e2 : (Sp S).basicOpen (toΓ S a) = PrimeSpectrum.basicOpen a :=
    basicOpen_eq_of_affine (R := CommRingCat.of S) a
  erw [e2] at h2
  exact h2

theorem secGen_of_secGen {x : Sp S ⟶ Xo.X} {θ s : LB.Sec (PPx x)} (hθ : SecGen x θ) (hs : SecNZ x s) :
    SecGen x s := by
  obtain ⟨a, ha, -⟩ := hθ s
  have hu : IsUnit a := by
    by_contra hn
    obtain ⟨m, hm, ham⟩ := exists_max_ideal_of_mem_nonunits hn
    obtain ⟨q, i, hq, hqi⟩ := hs ⟨m, hm.isPrime⟩
    rw [ha i, Scheme.basicOpen_mul] at hqi
    have := not_mem_of_mem_basicOpen_scal x a i q hqi.1
    rw [hq] at this
    exact this ham
  obtain ⟨u, rfl⟩ := hu
  intro t
  obtain ⟨b, hb, hbu⟩ := hθ t
  refine ⟨b * ↑u⁻¹, fun i => ?_, fun c hc => ?_⟩
  · rw [hb i, ha i, ← _root_.mul_assoc, ← scal_mul, Units.inv_mul_cancel_right]
  · have : c * u = b := hbu _ fun i => by rw [hc i, ha i, ← _root_.mul_assoc, ← scal_mul]
    rw [← this, Units.mul_inv_cancel_right]

theorem secNZ_pull {φ : S →+* T} {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X} (hx : x' = spMap φ ≫ x)
    {s : LB.Sec (PPx x)} {s' : LB.Sec (PPx x')} (h : SecBC φ 1 x x' s s') (hs : SecNZ x s) : SecNZ x' s' :=
  fun p' => (GlobalTheory.T.scaledBaseChange_fibreSection_nonvanishing_iff E H Dw l Xo S T φ x x' hx s s' h p').2 (hs _)

end GlobalTheory.Frames.NonzeroGenerates


open GlobalTheory.Frames.NonzeroGenerates in
theorem GlobalTheory.Frames.secGen_of_secNZ : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (s : LB.Sec (PPx x)), SecNZ x s → SecGen x s := by
  intro hBC E _ _ _ H Dw l Xo S _ x s hs t
  classical

  let G : Set S := {g | ∀ (T : Type) [CommRing T] (ψ : Localization.Away g →+* T) (φ : S →+* T),
    ψ.comp (algebraMap S (Localization.Away g)) = φ → ∀ s' : LB.Sec (PPx (spMap φ ≫ x)),
      SecBC φ 1 x _ s s' → SecGen _ s'}
  have hG : Ideal.span G = ⊤ := by
    by_contra hn
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hn
    obtain ⟨g, hg, θ, hθ⟩ := GlobalTheory.T.exists_local_generator_stable_baseChange hBC E H Dw l Xo S x ⟨m, hm.isPrime⟩
    refine hg (hle (Ideal.subset_span ?_))
    intro T _ ψ φ hφ s' hs'
    have e : spMap φ ≫ x = spMap ψ ≫ spMap (algebraMap S (Localization.Away g)) ≫ x := by
      rw [← hφ, GlobalTheory.Frames.NonzeroGenerates.spMap_comp', Category.assoc]
    obtain ⟨θ', hθ'⟩ := GlobalTheory.Frames.NonzeroGenerates.exists_pull ψ _ _ e θ
    exact GlobalTheory.Frames.NonzeroGenerates.secGen_of_secGen (hθ T ψ _ θ' e hθ').1 (GlobalTheory.Frames.NonzeroGenerates.secNZ_pull rfl hs' hs)
  choose sl hsl using fun g : S => GlobalTheory.Frames.NonzeroGenerates.exists_pull (algebraMap S (Localization.Away g)) x _ rfl s
  choose tl htl using fun g : S => GlobalTheory.Frames.NonzeroGenerates.exists_pull (algebraMap S (Localization.Away g)) x _ rfl t
  have hgen : ∀ g : G, SecGen _ (sl g) := fun g => g.2 _ (RingHom.id _) _ (RingHom.id_comp _) _ (hsl g)
  choose c hc hcu using fun g : G => hgen g (tl g)
  have key : ∀ (g : G) (h : S) (α : Localization.Away g.1 →+* Localization.Away h),
      α.comp (algebraMap S _) = algebraMap S _ →
      ∀ i, (tl h).f i = scal _ (α (c g)) i * (sl h).f i := by
    intro g h α hα
    have e : spMap (algebraMap S (Localization.Away h)) ≫ x =
        spMap α ≫ spMap (algebraMap S (Localization.Away g.1)) ≫ x := by
      rw [← hα, GlobalTheory.Frames.NonzeroGenerates.spMap_comp', Category.assoc]
    have h1 : SecBC α 1 _ _ (sl g) (sl h) := (GlobalTheory.Frames.NonzeroGenerates.pull_trans_iff rfl e (hsl g)).2 (by rw [hα]; exact hsl h)
    have h2 : SecBC α 1 _ _ (tl g) (tl h) := (GlobalTheory.Frames.NonzeroGenerates.pull_trans_iff rfl e (htl g)).2 (by rw [hα]; exact htl h)
    exact (GlobalTheory.Frames.NonzeroGenerates.pull_iff_of_mul e (hc g) h1).1 h2
  obtain ⟨a, ha, hau⟩ := Localization.existsUnique_algebraMap_eq_of_span_eq_top G hG c (fun g h => by
    have hα : (IsLocalization.Away.awayToAwayRight (S := Localization.Away g.1)
        (P := Localization.Away (g.1 * h.1)) g.1 h.1).comp (algebraMap S _) = algebraMap S _ :=
      RingHom.ext fun r => IsLocalization.Away.awayToAwayRight_eq g.1 h.1 r
    have hβ : (IsLocalization.Away.awayToAwayLeft (S := Localization.Away h.1)
        (P := Localization.Away (g.1 * h.1)) h.1 g.1).comp (algebraMap S _) = algebraMap S _ :=
      RingHom.ext fun r => IsLocalization.Away.awayToAwayLeft_eq h.1 g.1 r
    exact (g.2 _ _ _ hα _ (hsl _) (tl _)).unique (key g _ _ hα) (key h _ _ hβ))
  refine ⟨a, ?_, fun b hb => hau b fun g => hcu g _ ((GlobalTheory.Frames.NonzeroGenerates.pull_iff_of_mul rfl hb (hsl g)).1 (htl g))⟩
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.Frames.NonzeroGenerates.exists_mul x a s
  have hloc : ∀ g : G, SecBC (algebraMap S (Localization.Away g.1)) 1 x _ t₀ (tl g) := fun g =>
    (GlobalTheory.Frames.NonzeroGenerates.pull_iff_of_mul rfl ht₀ (hsl g)).2 (by rw [ha g]; exact hc g)
  obtain ⟨F, hF, h1⟩ := Submodule.mem_span_finite_of_mem_span ((Ideal.eq_top_iff_one _).1 hG)
  let h : Fin F.card → S := fun i => (F.equivFin.symm i).1
  have hr : Set.range h = F := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact (F.equivFin.symm i).2
    · intro hy
      exact ⟨F.equivFin ⟨y, hy⟩, by simp [h]⟩
  have hh : Ideal.span (Set.range h) = ⊤ := by
    rw [hr]; exact (Ideal.eq_top_iff_one _).2 h1
  have hmem : ∀ i, h i ∈ G := fun i => hF (F.equivFin.symm i).2
  have glue := GlobalTheory.T.existsUnique_glue_sections_principal_cover E H Dw l Xo S x F.card h hh (fun i => tl (h i)) (fun i j α β hα hβ u hu => by
    have e1 : spMap (algebraMap S (Localization.Away (h i * h j))) ≫ x =
        spMap α ≫ spMap (algebraMap S (Localization.Away (h i))) ≫ x := by
      rw [← hα, GlobalTheory.Frames.NonzeroGenerates.spMap_comp', Category.assoc]
    have e2 : spMap (algebraMap S (Localization.Away (h i * h j))) ≫ x =
        spMap β ≫ spMap (algebraMap S (Localization.Away (h j))) ≫ x := by
      rw [← hβ, GlobalTheory.Frames.NonzeroGenerates.spMap_comp', Category.assoc]
    have h3 := (GlobalTheory.Frames.NonzeroGenerates.pull_trans_iff rfl e1 (htl (h i))).1 hu
    rw [hα] at h3
    exact (GlobalTheory.Frames.NonzeroGenerates.pull_trans_iff rfl e2 (htl (h j))).2 (by rw [hβ]; exact h3))
  have : t = t₀ := glue.unique (fun i => htl (h i)) (fun i => hloc ⟨h i, hmem i⟩)
  rw [this]
  exact ht₀
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FibreSectionGeneratesOfNowhereZeroStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibreSectionGenerates_of_nowhereZero : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (s : LB.Sec (PPx x)), SecNZ x s → SecGen x s := by
  first | exact @GlobalTheory.Frames.secGen_of_secNZ | exact GlobalTheory.Frames.secGen_of_secNZ | (intros; apply GlobalTheory.Frames.secGen_of_secNZ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFramesDifferByUnit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.IntLie

section Pull

variable {S' S₀ : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S₀} [GrpObj G] {f : S' ⟶ S₀}
  {φ : G'.left ⟶ G.left}

theorem one_push₀ (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : Over.mk (T.hom ≫ f) ⟶ G).left = (1 : T ⟶ G').left ≫ φ := by
  let e0 : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ) (by
    show ((1 : T ⟶ G').left ≫ φ) ≫ G.hom = T.hom ≫ f
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w])
  have h1 : (e0 * e0).left = ((1 : T ⟶ G') * 1).left ≫ φ := h.2 T 1 1 e0 e0 rfl rfl
  rw [_root_.mul_one] at h1
  have h2 : e0 * e0 = e0 := Over.OverMorphism.ext h1
  have h3 : e0 = 1 := mul_eq_left.1 h2
  rw [← h3]
  rfl

theorem one_push (h : IsGrpPullback G' G f φ) (T' : Over S') (T : Over S₀) (g : T'.left ⟶ T.left)
    (hg : g ≫ T.hom = T'.hom ≫ f) : (1 : T' ⟶ G').left ≫ φ = g ≫ (1 : T ⟶ G).left := by
  let δ : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk g hg
  rw [← one_push₀ h T', ← MonObj.comp_one δ]
  rfl

theorem mul_push (h : IsGrpPullback G' G f φ) (T' : Over S') (T : Over S₀) (g : T'.left ⟶ T.left)
    (hg : g ≫ T.hom = T'.hom ≫ f) (a b : T' ⟶ G') (a₀ b₀ : T ⟶ G) (ha : a.left ≫ φ = g ≫ a₀.left)
    (hb : b.left ≫ φ = g ≫ b₀.left) : (a * b).left ≫ φ = g ≫ (a₀ * b₀).left := by
  let δ : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk g hg
  rw [← h.2 T' a b (δ ≫ a₀) (δ ≫ b₀) ha.symm hb.symm, ← MonObj.comp_mul]
  rfl

theorem prod_push (h : IsGrpPullback G' G f φ) (T' : Over S') (T : Over S₀) (g : T'.left ⟶ T.left)
    (hg : g ≫ T.hom = T'.hom ≫ f) {m : ℕ} (a : Fin m → (T' ⟶ G')) (a₀ : Fin m → (T ⟶ G))
    (ha : ∀ j, (a j).left ≫ φ = g ≫ (a₀ j).left) :
    ((List.ofFn a).prod).left ≫ φ = g ≫ ((List.ofFn a₀).prod).left := by
  induction m with
  | zero => simpa using one_push h T' T g hg
  | succ m ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    exact mul_push h T' T g hg _ _ _ _ (ha 0) (ih _ _ fun j => ha j.succ)

theorem isIso_of_pull {G₁ G₂ : Over S₀} [GrpObj G₁] [GrpObj G₂] {ψ : G₁.left ⟶ G₂.left}
    (h : IsGrpPullback G₁ G₂ (𝟙 _) ψ) : IsIso ψ :=
  h.1.isIso_fst_of_isIso

end Pull

theorem spMap_comp₂ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem spMap_frac_cancel {V K A : Type} [CommRing V] [CommRing K] [Algebra V K] [IsFractionRing V K] [CommRing A]
    (g h : Sp A ⟶ Sp K) (e : g ≫ spMap (algebraMap V K) = h ≫ spMap (algebraMap V K)) : g = h := by
  rw [← Spec.map_preimage g, ← Spec.map_preimage h] at e ⊢
  simp only [spMap, ← Spec.map_comp] at e
  have e1 := Spec.map_injective e
  congr 1
  apply CommRingCat.hom_ext
  apply IsLocalization.ringHom_ext (nonZeroDivisors V)
  exact congrArg CommRingCat.Hom.hom e1

theorem dualMap_alg {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    (dualMap f).comp (algebraMap A (DualNumber A)) = (algebraMap B (DualNumber B)).comp f := by
  apply RingHom.ext
  intro r
  ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_epsMul {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (a : A) :
    (dualMap f).comp (epsMul a) = (epsMul (f a)).comp (dualMap f) := by
  apply RingHom.ext
  intro r
  ext <;> simp [dualMap, epsMul, _root_.mul_comm]

theorem epsMul_alg {A : Type} [CommRing A] (a : A) :
    (epsMul a).comp (algebraMap A (DualNumber A)) = algebraMap A (DualNumber A) := by
  ext s <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem comb_generic {V K : Type} [CommRing V] [CommRing K] [Algebra V K] [IsFractionRing V K]
    {x : Sp K ⟶ Xo.X} {G : SAB H (Sp V)} {t : SAB H (Sp K)} (m₁ : SABMap t Xo.univ.t x)
    (m₂ : SABMap t G (spMap (algebraMap V K))) {m : ℕ} (ub : Fin m → (epsOver V V ⟶ G.G))
    (u' : Fin m → (Sp (DualNumber K) ⟶ t.G.left))
    (hu : ∀ j, u' j ≫ m₂.φ = spMap (dualMap (algebraMap V K)) ≫ (ub j).left)
    (w : epsOver V V ⟶ G.G) (w' : Sp (DualNumber K) ⟶ t.G.left)
    (hw : w' ≫ m₂.φ = spMap (dualMap (algebraMap V K)) ≫ w.left) (a : Fin m → V) (ha : IsComb ub a w) :
    IsCombAt x (fun j => u' j ≫ m₁.φ) (fun j => algebraMap V K (a j)) (w' ≫ m₁.φ) := by
  obtain ⟨U, hU, hwU⟩ := ha
  have hδ : spMap (dualMap (algebraMap V K)) ≫
      spMap ((algebraMap V (DualNumber V)).comp (algebraMap V V)) =
      spMap (algebraMap K (DualNumber K)) ≫ spMap (algebraMap V K) := by
    rw [spMap_comp₂, spMap_comp₂]
    show spMap ((dualMap (algebraMap V K)).comp (algebraMap V (DualNumber V))) = _
    rw [dualMap_alg]
  have hov : ∀ (z : epsOver V V ⟶ G.G) (z' : Sp (DualNumber K) ⟶ t.G.left),
      z' ≫ m₂.φ = spMap (dualMap (algebraMap V K)) ≫ z.left →
      z' ≫ t.G.hom = spMap (algebraMap K (DualNumber K)) := by
    intro z z' hz
    apply spMap_frac_cancel (V := V)
    rw [Category.assoc, ← m₂.cart.1.w, ← Category.assoc, hz, Category.assoc, Over.w z]
    exact hδ
  let T' : Over (Sp K) := Over.mk (spMap (algebraMap K (DualNumber K)))
  let Y : Fin m → (T' ⟶ t.G) := fun j => Over.homMk (spMap (epsMul (algebraMap V K (a j))) ≫ u' j) (by
    show (spMap (epsMul (algebraMap V K (a j))) ≫ u' j) ≫ t.G.hom = spMap (algebraMap K (DualNumber K))
    rw [Category.assoc, hov _ _ (hu j), spMap_comp₂, epsMul_alg])
  have hB := prod_push m₂.cart T' (epsOver V V) (spMap (dualMap (algebraMap V K))) hδ Y U (fun j => by
    show (spMap (epsMul (algebraMap V K (a j))) ≫ u' j) ≫ m₂.φ = _
    rw [Category.assoc, hu j, hU j, ← Category.assoc, ← Category.assoc, spMap_comp₂, spMap_comp₂,
      dualMap_epsMul])
  have hY : ((List.ofFn Y).prod).left = w' := by
    apply m₂.cart.1.hom_ext
    · rw [hB, ← hwU]
      exact hw.symm
    · rw [hov _ _ hw]
      exact Over.w _
  let Z : Fin m → (tEps x ⟶ Xo.univ.t.G) := fun j => Over.homMk ((Y j).left ≫ m₁.φ) (by
    show ((Y j).left ≫ m₁.φ) ≫ Xo.univ.t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ x
    rw [Category.assoc, m₁.cart.1.w, ← Category.assoc, Over.w (Y j)]
    rfl)
  have hA := prod_push m₁.cart T' (tEps x) (𝟙 _) (Category.id_comp _) Y Z (fun j => (Category.id_comp _).symm)
  refine ⟨Z, fun j => Category.assoc _ _ _, ?_⟩
  rw [← hY]
  exact ((Category.id_comp _).symm.trans hA.symm)

theorem tan_eig_iff {V K : Type} [CommRing V] [Field K] [Algebra V K] (io : c.F →+* K) {G G₂ : SAB H (Sp V)}
    (n : SABMap G G₂ (𝟙 _)) (τ : E →+* ℂ) (w : epsOver V V ⟶ G.G) (w₂ : epsOver V V ⟶ G₂.G)
    (h : w.left ≫ n.φ = w₂.left) :
    (IsTan w ↔ IsTan w₂) ∧ (IsEigV c io G τ w ↔ IsEigV c io G₂ τ w₂) := by
  have := isIso_of_pull n.cart
  constructor
  · have h1 := one_push n.cart (ptOver V V) (ptOver V V) (𝟙 _) (by simp)
    rw [Category.id_comp] at h1
    unfold IsTan
    rw [← h, ← h1, ← Category.assoc]
    exact (cancel_mono n.cm.F).symm
  · unfold IsEigV
    refine forall_congr' fun a => forall_congr' fun z => forall_congr' fun _ => ?_
    rw [Over.comp_left, Over.comp_left, ← h, Category.assoc, ← n.act a, ← Category.assoc, ← Category.assoc]
    exact (cancel_mono n.cm.F).symm

theorem mul_eq_one_of_comb {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) {m : ℕ}
    (u u₂ : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (hu : ∀ i, IsTanAt x (u i))
    (huniq : ∀ i, ∃! a : Fin m → S, IsCombAt x u a (u i)) (A B : Matrix (Fin m) (Fin m) S)
    (hA : ∀ i, IsCombAt x u (A i) (u₂ i)) (hB : ∀ i, IsCombAt x u₂ (B i) (u i)) : B * A = 1 := by
  obtain ⟨N, _, _, v, ρ, hinj, htan, hcomb, -, -⟩ := GlobalTheory.TanMod.exists_tangent_module E H Dw l Xo S x
  choose b hb using fun i => (htan _).1 (hu i)
  obtain rfl : u = fun i => v (b i) := funext fun i => (hb i).symm
  obtain rfl : u₂ = fun i => v (∑ j, A i j • b j) := funext fun i => (hcomb _ b _ _).1 (hA i)
  ext i k
  have h1 := (hcomb _ (fun i => ∑ j, A i j • b j) _ _).1 (hB i)
  have h2 : IsCombAt x (fun i => v (b i)) ((B * A) i) (v (b i)) := by
    refine (hcomb _ b _ _).2 (h1.trans (congrArg v ?_))
    simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
    exact Finset.sum_comm
  have h3 : IsCombAt x (fun i => v (b i)) ((1 : Matrix (Fin m) (Fin m) S) i) (v (b i)) := by
    refine (hcomb _ b _ _).2 (congrArg v ?_)
    simp [Matrix.one_apply]
  exact congrFun ((huniq i).unique h2 h3) k

theorem integral_frames_differ_by_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (y y' : FrPt Xo c T.Fr) (G G₂ : SAB H (Sp T.V)) (t t₂ : SAB H (Sp T.Fr)) (m₁ : SABMap t Xo.univ.t y.x) (m₂ : SABMap t G (spMap (algebraMap T.V T.Fr))) (n₁ : SABMap t₂ Xo.univ.t y'.x) (n₂ : SABMap t₂ G₂ (spMap (algebraMap T.V T.Fr))) (k : SABMap t t₂ (𝟙 _)) (n : SABMap G G₂ (𝟙 _)), y'.x = y.x → k.φ ≫ n₁.φ = m₁.φ → m₂.φ ≫ n.φ = k.φ ≫ n₂.φ → ∀ (ub : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G.G)) (ub₂ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G₂.G)), ((∀ τ i, IsTan (ub τ i)) ∧ (∀ τ i, IsEigV c io G τ (ub τ i)) ∧ (∀ τ (w : epsOver T.V T.V ⟶ G.G), IsTan w → IsEigV c io G τ w → ∃! a : Fin (Dw.mult τ) → T.V, IsComb (ub τ) a w) ∧ ∀ τ i, ∃ u' : Sp (DualNumber T.Fr) ⟶ t.G.left, u' ≫ m₁.φ = y.u τ i ∧ u' ≫ m₂.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ (ub τ i).left) → ((∀ τ i, IsTan (ub₂ τ i)) ∧ (∀ τ i, IsEigV c io G₂ τ (ub₂ τ i)) ∧ (∀ τ (w : epsOver T.V T.V ⟶ G₂.G), IsTan w → IsEigV c io G₂ τ w → ∃! a : Fin (Dw.mult τ) → T.V, IsComb (ub₂ τ) a w) ∧ ∀ τ i, ∃ u' : Sp (DualNumber T.Fr) ⟶ t₂.G.left, u' ≫ n₁.φ = y'.u τ i ∧ u' ≫ n₂.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ (ub₂ τ i).left) → ∀ τ : E →+* ℂ, ∃ A : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.V, IsUnit A.det ∧ ∀ i, IsCombAt y.x (y.u τ) (fun j => algebraMap T.V T.Fr (A i j)) (y'.u τ i) := by
  intro E _ _ _ H Dw l Xo c T io
  let _ := io.toAlgebra
  intro y y' G G₂ t t₂ m₁ m₂ n₁ n₂ k n hx hk hn ub ub₂ ⟨ht, he, hb, hl⟩ ⟨ht₂, he₂, hb₂, hl₂⟩ τ
  have := isIso_of_pull n.cart
  have := isIso_of_pull k.cart
  have hnw : n.φ ≫ G₂.G.hom = G.G.hom := n.cart.1.w.trans (Category.comp_id _)
  choose u' hu1 hu2 using hl τ
  choose u₂ hv1 hv2 using hl₂ τ
  let w : Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G.G) := fun i => Over.homMk ((ub₂ τ i).left ≫ inv n.φ) (by
    rw [← hnw, Category.assoc, IsIso.inv_hom_id_assoc]
    exact Over.w _)
  have hw : ∀ i, (w i).left ≫ n.φ = (ub₂ τ i).left := fun i => by
    show ((ub₂ τ i).left ≫ inv n.φ) ≫ n.φ = _
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  let w₂ : Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G₂.G) := fun i => Over.homMk ((ub τ i).left ≫ n.φ) (by
    rw [Category.assoc, hnw]
    exact Over.w _)
  have hw₂ : ∀ i, (ub τ i).left ≫ n.φ = (w₂ i).left := fun i => rfl
  choose A hA using fun i => (hb τ (w i) ((tan_eig_iff io n τ _ _ (hw i)).1.2 (ht₂ τ i))
    ((tan_eig_iff io n τ _ _ (hw i)).2.2 (he₂ τ i))).exists
  choose B hB using fun i => (hb₂ τ (w₂ i) ((tan_eig_iff io n τ _ _ (hw₂ i)).1.1 (ht τ i))
    ((tan_eig_iff io n τ _ _ (hw₂ i)).2.1 (he τ i))).exists
  have hA' : ∀ i, IsCombAt y.x (y.u τ) (fun j => algebraMap T.V T.Fr (A i j)) (y'.u τ i) := by
    intro i
    have h := comb_generic m₁ m₂ (ub τ) u' hu2 (w i) (u₂ i ≫ inv k.φ) (by
      rw [← cancel_mono n.φ, Category.assoc, Category.assoc, hn, IsIso.inv_hom_id_assoc, hv2, Category.assoc,
        hw]) (A i) (hA i)
    rw [funext hu1, ← hk, Category.assoc, IsIso.inv_hom_id_assoc, hv1] at h
    exact h
  have hB' : ∀ i, IsCombAt y.x (y'.u τ) (fun j => algebraMap T.V T.Fr (B i j)) (y.u τ i) := by
    intro i
    have h := comb_generic n₁ n₂ (ub₂ τ) u₂ hv2 (w₂ i) (u' i ≫ k.φ) (by
      rw [Category.assoc, ← hn, ← Category.assoc, hu2, Category.assoc, hw₂]) (B i) (hB i)
    rw [funext hv1, Category.assoc, hk, hu1, hx] at h
    exact h
  refine ⟨Matrix.of A, ?_, hA'⟩
  have h1 := mul_eq_one_of_comb y.x (y.u τ) (y'.u τ) (y.tan τ)
    (fun i => y.basis τ _ (y.tan τ i) (y.eig τ i))
    ((Matrix.of A).map (algebraMap T.V T.Fr)) ((Matrix.of B).map (algebraMap T.V T.Fr)) hA' hB'
  have h2 : Matrix.of B * Matrix.of A = 1 := by
    apply Matrix.map_injective (IsFractionRing.injective T.V T.Fr)
    show (Matrix.of B * Matrix.of A).map (algebraMap T.V T.Fr) = (1 : Matrix _ _ T.V).map (algebraMap T.V T.Fr)
    rw [Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  exact Matrix.isUnit_det_of_left_inverse h2

end GlobalTheory.IntLie
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ModuliExistsNumberFieldPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ModuliExistsAlgebraicPoint
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_finite_point_mem_opens {k : Type} [Field k] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] (W : X.Opens) (hW : (W : Set X).Nonempty) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra k L), FiniteDimensional k L ∧
      ∃ y : Spec (CommRingCat.of L) ⟶ X,
        y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k L)) ∧ Set.range y ⊆ W := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨x, hxW, hx⟩ := nonempty_inter_closedPoints hW W.isOpen.isLocallyClosed
  have hc : IsClosedImmersion (X.fromSpecResidueField x) := isClosed_singleton_iff_isClosedImmersion.mp hx
  have hfin : IsFinite (X.fromSpecResidueField x ≫ f) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.fromSpecResidueField x ≫ f)
  rw [← hφ, IsFinite.SpecMap_iff] at hfin
  let : Algebra k (X.residueField x) := φ.hom.toAlgebra
  refine ⟨X.residueField x, inferInstance, inferInstance, hfin, X.fromSpecResidueField x, hφ.symm, ?_⟩
  rw [Scheme.range_fromSpecResidueField]
  simpa using hxW

theorem moduli_exists_algebraic_point :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W : (Xo.XF c).Opens), (W : Set (Xo.XF c)).Nonempty → ∃ (L : Type) (_ : Field L) (_ : Algebra c.F L), FiniteDimensional c.F L ∧ ∃ y : Sp L ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F L) ∧ Set.range y ⊆ W := by
  intro E _ _ _ H D l Xo c W hW
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  exact exists_finite_point_mem_opens (pullback.snd _ _) W hW

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ModuliExistsNumberFieldPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory

theorem moduli_exists_numberField_point :
    N1c → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → Formalism.L2.PjFree.XoNumPt Xo c := by
  intro hN E _ _ _ H Dw l Xo c hr
  obtain ⟨x⟩ := (PeriodExists.typeFn_period_exist E H Dw).2.2 hN hr l Xo c
  obtain ⟨L, _, _, hfin, y, hy, -⟩ := moduli_exists_algebraic_point E H Dw l Xo c ⊤ ⟨x, trivial⟩
  have : NumberField L := NumberField.of_module_finite c.F L
  refine ⟨L, inferInstance, this, algebraMap c.F L, y ≫ pullback.fst _ _, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hy]
  simp only [sOf, spMap, ← Spec.map_comp]
  rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ModuliExistsNumberFieldPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.xoNumPt_of_p_add_q_pos : N1c → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → Formalism.L2.PjFree.XoNumPt Xo c := by
  first | exact @GlobalTheory.moduli_exists_numberField_point | exact GlobalTheory.moduli_exists_numberField_point | (intros; apply GlobalTheory.moduli_exists_numberField_point <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsThetaPt
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open Formalism.L2.PjFree hiding gxFst gxSnd relab toC
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameUnif.ThetaPtEx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l}

theorem exists_chart_top {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (p : Sp ℂ ⟶ X) :
    ∃ j, ⊤ ≤ p ⁻¹ᵁ L.U j := by
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1
    (hL.cover.ge (Set.mem_univ (p (default : PrimeSpectrum ℂ))))
  refine ⟨j, fun q _ => ?_⟩
  obtain rfl : q = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  exact hj

theorem exists_gen (hT : Out.SecTwistSt) (y : Sp ℂ ⟶ Xo.X) {Z : Type} (ex : Z → (Over.mk y ⟶ Xo.univ.t.G))
    (θ : Z → ℂ) (fr : Xo.univ.t.PP.L.ι → Z → ℂ) (κ : ℂ) (hκ : κ ≠ 0) (hθ : ∃ z, θ z ≠ 0)
    (hfr : ∀ j z, ⊤ ≤ (ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0)
    (s : (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom y)).Sec)
    (hs : ∀ j z (x : Sp ℂ ⟶ pullback Xo.univ.t.G.hom y),
        x ≫ pullback.fst _ _ = (ex z).left → x ≫ pullback.snd _ _ = 𝟙 _ →
        ⊤ ≤ (ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
        valAt' x ((Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom y)).U (fun _ => j))
          (s.f (fun _ => j)) = θ z * fr j z) :
    ∃ t : LB.Sec (PPx y), SecGen y t ∧
      ∀ j z (pt : Sp ℂ ⟶ Gx y), pt ≫ gxFst y = (ex z).left → pt ≫ gxSnd y = 𝟙 (Sp ℂ) →
        ⊤ ≤ (ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
        valAt' pt ((PPx y).U (fun _ => j)) (t.f (fun _ => j)) = κ * θ z * fr j z := by
  obtain ⟨s', hs'⟩ := GlobalTheory.T.exists_fibreSection_other_model_same_values E H Dw l Xo y s
  have hw : ∀ z, (ex z).left ≫ Xo.univ.t.G.hom = 𝟙 (Sp ℂ) ≫ y := fun z =>
    (Over.w (ex z)).trans (Category.id_comp y).symm
  have key : ∀ j z (pt : Sp ℂ ⟶ Gx y), pt ≫ gxFst y = (ex z).left → pt ≫ gxSnd y = 𝟙 (Sp ℂ) →
      ⊤ ≤ (ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx y).U (fun _ => j)) ((SecPull.scalSec y κ s').f (fun _ => j)) = κ * θ z * fr j z := by
    intro j z pt h1 h2 h3
    have e1 := (GlobalTheory.T.sec_values_complex_fibre_abelianScheme hT E H Dw l Xo y s').1 κ (fun _ => j) pt h2
    have e2 := hs' j pt (pullback.lift (ex z).left (𝟙 _) (hw z)) ((pullback.lift_fst _ _ _).trans h1.symm)
      (pullback.lift_snd _ _ _) h2
    have e3 := hs j z (pullback.lift (ex z).left (𝟙 _) (hw z)) (pullback.lift_fst _ _ _)
      (pullback.lift_snd _ _ _) h3
    refine e1.trans ?_
    rw [e2, e3, mul_assoc]
  refine ⟨SecPull.scalSec y κ s', ?_, key⟩
  obtain ⟨z, hz⟩ := hθ
  obtain ⟨j, hj⟩ := exists_chart_top Xo.univ.t.PP.isLB (ex z).left
  let pt : Sp ℂ ⟶ Gx y := pullback.lift (f := (Over.mk y).hom) (g := Xo.univ.t.G.hom) (𝟙 _) (ex z).left (hw z).symm
  have h1 : pt ≫ gxFst y = (ex z).left := pullback.lift_snd _ _ _
  have h2 : pt ≫ gxSnd y = 𝟙 (Sp ℂ) := pullback.lift_fst _ _ _
  refine (GlobalTheory.T.sec_values_complex_fibre_abelianScheme hT E H Dw l Xo y _).2.1.2 ⟨fun _ => j, pt, h2, ?_⟩
  rw [key j z pt h1 h2 hj]
  exact mul_ne_zero (mul_ne_zero hκ hz) (hfr j z hj)

theorem exists_thetaPt : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∀ b ∈ T.co ⁻¹' (M.X k).dom, ∀ κ : ℂ, κ ≠ 0 → ∃ y : FrPt Xo c (CAt σ), IsThetaPt T b κ y := by
  intro hT E _ _ _ H Dw l Xo c σ g e F r M k T b hb κ hκ
  have hP := T.isPer _ hb
  obtain ⟨u, hu, htan, heig, hbas⟩ := GlobalTheory.T.exists_tangent_eigenbasis_exponential E H Dw l Xo c σ g e F k _ hP
  obtain ⟨s, hs⟩ := T.fr_sec b hb
  obtain ⟨hdet, hsym, hpos, -⟩ := T.norm b hb
  obtain ⟨w, hw⟩ := ((GlobalTheory.T.thetaChar_half_differentiable_ne_zero_families g T.c₁ T.c₂ T.half₁ T.half₂).1 _ hsym hpos).2
  have hθ : ∃ z, thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ z) ≠ 0 :=
    ⟨(T.h b)⁻¹ *ᵥ w, by rwa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]⟩
  obtain ⟨t, ht, hval⟩ := exists_gen hT (F.u k (T.Pf (T.co b))) (F.ex k (T.Pf (T.co b)))
    (fun z => thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ z)) (fun j z => T.fr j (b, z)) κ hκ hθ
    (fun j z hz => T.fr_ne j b z hb hz) s hs
  exact ⟨⟨F.u k (T.Pf (T.co b)), F.over_σ k _ hP, u, htan, heig, hbas, t, ht⟩, rfl, hu, hval⟩

end GlobalTheory.FrameUnif.ThetaPtEx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaPointsFrameRatio
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaPointsFrameRatio
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open Formalism.L2.PjFree hiding gxFst gxSnd relab toC
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory

theorem sec_eq_scal_of_values (hT : Out.SecTwistSt) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {V : Type}
    (x : Sp ℂ ⟶ Xo.X) (ex : V → (Over.mk x ⟶ Xo.univ.t.G)) (hex : Function.Surjective ex)
    (s s' : LB.Sec (PPx x)) (hs : SecGen x s) (t : ℂ)
    (hv : ∀ j z (pt : Sp ℂ ⟶ Gx x), pt ≫ gxFst x = (ex z).left → pt ≫ gxSnd x = 𝟙 (Sp ℂ) →
      ⊤ ≤ (ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx x).U (fun _ => j)) (s'.f (fun _ => j)) =
        t * valAt' pt ((PPx x).U (fun _ => j)) (s.f (fun _ => j))) :
    ∀ i, s'.f i = scal x t i * s.f i := by
  obtain ⟨h1, h2, -⟩ := sec_values_complex_fibre hT E H Dw l Xo x s
  obtain ⟨a, ha, -⟩ := hs s'
  obtain ⟨i, pt, hp, hne⟩ := h2.1 hs
  have hi : i = fun _ => i (0 : Fin 1) := funext fun k => congrArg i (Subsingleton.elim _ _)
  obtain ⟨j, rfl⟩ : ∃ j, i = fun _ => j := ⟨_, hi⟩
  have cond : gxFst x ≫ Xo.univ.t.G.hom = gxSnd x ≫ x := pullback.condition.symm
  obtain ⟨z, hz⟩ := hex (Over.homMk (pt ≫ gxFst x) (by
    show (pt ≫ gxFst x) ≫ Xo.univ.t.G.hom = x
    rw [Category.assoc, cond, ← Category.assoc, hp, Category.id_comp]))
  have hz' : pt ≫ gxFst x = (ex z).left := by rw [hz]; rfl
  have hU : ⊤ ≤ pt ⁻¹ᵁ (PPx x).U (fun _ => j) := by
    by_contra h
    exact hne (by unfold valAt'; rw [dite_eq_right h])
  have hU' : ⊤ ≤ (ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := by
    rw [← hz']
    intro p hp'
    exact Set.mem_iInter.1 (hU hp') (0 : Fin 1)
  have e := hv j z pt hz' hp hU'
  have e' := (congrArg (valAt' pt ((PPx x).U (fun _ => j))) (ha (fun _ => j))).trans (h1 a _ pt hp)
  have hat : a = t := mul_right_cancel₀ hne (e'.symm.trans e)
  rw [← hat]
  exact ha

theorem isCombAt_single_of_isTanAt {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {S : Type} [CommRing S]
    (x : Sp S ⟶ Xo.X) {m : ℕ} (u : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (tan : ∀ j, IsTanAt x (u j))
    (i : Fin m) : IsCombAt x u (Pi.single i 1) (u i) := by
  obtain ⟨N, _, _, v, ρ, -, h2, h3, -⟩ := TanMod.exists_tangent_module E H Dw l Xo S x
  choose n hn using fun j => (h2 _).1 (tan j)
  obtain rfl : u = fun j => v (n j) := funext fun j => (hn j).symm
  rw [h3]
  show v (n i) = _
  congr 1
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul]) (by simp)]
  simp

theorem appLE_id_apply_self {X : Scheme.{0}} (U : X.Opens) (h : U ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ U) (f : Γ(X, U)) :
    (Scheme.Hom.appLE (𝟙 X) U U h).hom f = f := by
  have : Scheme.Hom.appLE (𝟙 X) U U h = 𝟙 _ := by
    rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
    exact (Category.id_comp _).trans (X.presheaf.map_id _)
  rw [this]
  rfl

theorem frBor_of_isThetaPt : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∀ b ∈ T.co ⁻¹' (M.X k).dom, ∀ (κ : ℂ) (t₀ : (CAt σ)ˣ) (y y' : FrPt Xo c (CAt σ)), IsThetaPt T b κ y → IsThetaPt T b (toC (t₀ : CAt σ) * κ) y' → FrBor (fun i => Option.elim i t₀ (fun _ => 1)) y y' := by
  intro hT E _ _ _ H Dw l Xo c σ g e F r M k T b hb κ t₀ y y' hy hy'
  have hP := T.isPer _ hb
  obtain ⟨x, xo, u, tan, eig, basis, s, gen⟩ := y
  obtain ⟨x', xo', u', tan', eig', basis', s', gen'⟩ := y'
  obtain ⟨hx, hu, hs⟩ := hy
  obtain ⟨hx', hu', hs'⟩ := hy'
  dsimp only at hx hu hs hx' hu' hs'
  subst hx hx'
  obtain ⟨-, hd, -⟩ := isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F k _ hP
  have huu : ∀ τ i, u' τ i = u τ i := fun τ i => (hd _).unique (hu' τ i) (hu τ i)
  refine ⟨rfl, fun τ i => ⟨Pi.single i 1, by simp, fun j hj => Pi.single_eq_of_ne hj.ne' _, ?_⟩, 𝟙 _,
    Category.id_comp _, Category.id_comp _, fun i h => ?_⟩
  · show IsCombAt _ (u τ) _ (u' τ i)
    rw [huu]
    exact isCombAt_single_of_isTanAt (S := CAt σ) _ _ (tan τ) i
  · have key := sec_eq_scal_of_values hT (F.u k (T.Pf (T.co b))) (F.ex k (T.Pf (T.co b))) (F.ex_onto k _ hP)
      s s' gen (toC (t₀ : CAt σ)) (fun j z pt h1 h2 h3 => by
        refine (hs' j z pt h1 h2 h3).trans ?_
        refine Eq.trans ?_ (congrArg (toC (t₀ : CAt σ) * ·) (hs j z pt h1 h2 h3).symm)
        ring)
    refine Eq.trans ?_ (key i).symm
    exact appLE_id_apply_self _ h _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaPointsFrameRatioStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open Formalism.L2.PjFree hiding gxFst gxSnd relab toC
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaPoints_frame_ratio : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∀ b ∈ T.co ⁻¹' (M.X k).dom, ∀ (κ : ℂ) (t₀ : (CAt σ)ˣ) (y y' : FrPt Xo c (CAt σ)), IsThetaPt T b κ y → IsThetaPt T b (toC (t₀ : CAt σ) * κ) y' → FrBor (fun i => Option.elim i t₀ (fun _ => 1)) y y' := by
  first | exact @GlobalTheory.frBor_of_isThetaPt | exact GlobalTheory.frBor_of_isThetaPt | (intros; apply GlobalTheory.frBor_of_isThetaPt <;> assumption)
end
end
