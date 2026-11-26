module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtensionSemiAbelianDiscreteValuationRing
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLetterIntegralInIntegralEigenbasis
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrincipallyPolarizedCMExtensionDvr
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsRetractTensorTriple
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionSectionCoordsThetaTimesRoots
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaIdealFamilyUniversalProperty

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsToricTorsionCubWeilOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
open GlobalTheory.UU

namespace GlobalTheory

theorem exists_toric_torsion_cubWeil_one : Out.Laws3 → ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (L : RigLB G) (c : CubicalStr G L) (g N : ℕ) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X), SmoothOfRelativeDimension g G.hom → (N : k) ≠ 0 → ∃ T : Set (Over.mk x ⟶ G), (∀ τ ∈ T, τ ^ N = 1) ∧ (∀ τ ∈ T, ∀ y : Over.mk x ⟶ G, y ^ N = 1 → CubWeil c N τ y 1) ∧ Nat.card {p : Over.mk x ⟶ G // p ^ N = 1} * Nat.card T = N ^ (2 * g) := by
  intro h3 X G _ _ hG L c g N k _ _ x dG hN
  let G' : Over (Sp k) := (Over.pullback x).obj G
  have hp : IsGrpPullback G' G x (pullback.fst G.hom x) := isGrpPullback_pullback G x
  have hG' : IsSemiAbelian G' := IsSemiAbelian.pullback x G hG
  have := hG'.comm
  have := hG'.smooth
  have := hG'.geomConnected
  have dG' : SmoothOfRelativeDimension g G'.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hp.1 dG
  obtain ⟨E⟩ := hG.fibres k x
  let := E.addCommGroup
  let := E.grpB
  have := E.free
  have := E.finite
  have := E.i_hom
  obtain ⟨hL, hr, ⟨c', hc'⟩, -⟩ := h3.cubePull _ _ G G' (cubeMapOf hp) L c
  obtain ⟨σ⟩ := GlobalTheory.BiextTriv.main k E.X G' _ c' E.i E.i_hom
  have hw : pullback.fst G.hom x ≫ G.hom = G'.hom ≫ x := pullback.condition
  let U : Over (Sp k) := 𝟙_ (Over (Sp k))
  let ρ : Over.mk x ⟶ Over.mk (U.hom ≫ x) := Over.homMk (𝟙 _) rfl
  let φ : (U ⟶ G') →* (Over.mk x ⟶ G) := (preHom ρ).comp (toBaseHom (toBase_mul_pullback G x) U)
  have hφ : ∀ a : U ⟶ G', (φ a).left = a.left ≫ pullback.fst G.hom x := fun a => Category.id_comp _
  have hb : Function.Bijective φ := by
    refine ⟨fun a b h => Over.OverMorphism.ext (pullback.hom_ext ?_ ?_), fun p => ?_⟩
    · rw [← hφ, ← hφ, h]
    · exact (Over.w a).trans (Over.w b).symm
    · refine ⟨Over.homMk (pullback.lift p.left (𝟙 _) ((Over.w p).trans (Category.id_comp _).symm))
        (pullback.lift_snd _ _ _), Over.OverMorphism.ext ((hφ _).trans (pullback.lift_fst _ _ _))⟩
  let e := MulEquiv.ofBijective φ hb
  have he : ∀ a : U ⟶ G', e a ^ N = 1 ↔ a ^ N = 1 := fun a => by rw [← map_pow, e.map_eq_one_iff]
  have hcount := GlobalTheory.card_torsion_mul_card_toric_torsion k G' E g N hG' dG' hN
  refine ⟨e '' {y | y ^ N = 1 ∧ ∃ t, y = t ≫ E.i}, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ⟨ha, -⟩, rfl⟩
    exact (he a).2 ha
  · rintro _ ⟨_, ⟨ha, t, rfl⟩, rfl⟩ y hy
    obtain ⟨b, rfl⟩ := e.surjective y
    have ht : t ^ N = 1 := E.isKernel.hom_ext
      (by rw [MonObj.pow_comp, ha, MonObj.one_comp]) (toUnit_unique _ _)
    have h1 := σ.cubWeil ht ((he b).1 hy)
    have h2 := (GlobalTheory.UU.cubWeil_of_isPullCubical _ _ x G G' (cubeMapOf hp) hw (toBase_mul_pullback G x) L _ c c' hc' N U _ _ _ h1).comp ρ
    rw [map_one] at h2
    exact h2
  · rw [← hcount]
    congr 1
    · exact (Nat.card_congr (e.toEquiv.subtypeEquiv fun a => (he a).symm)).symm
    · exact Nat.card_image_of_injective e.injective _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmplePrincipalOfGenericFibreDvr
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmplePrincipalOfGenericFibreDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.PolDvr

theorem exists_polAV {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R]
    [IsLocalRing R] (t : SAB H (Sp R)) (hp : IsProper t.G.hom) (hA : Out.RelAmple t.G t.PP.L)
    (hK : Out.KTriv t.G t.PP.L) :
    ∃ (P : Out.PolAV (Sp R)) (e : P.A ≅ t.G), (∀ {S : Scheme.{0}} (B : Over S) [GrpObj B] (f : Sp R ⟶ S)
      (φ : t.G.left ⟶ B.left) (M : LB B.left), IsGrpPullback t.G B f φ → LBIso t.PP.L (M.pull φ) →
        IsGrpPullback P.A B f (e.hom.left ≫ φ) ∧ LBIso P.L (M.pull (e.hom.left ≫ φ))) := by
  have hab : IsAbelianScheme t.G := ⟨t.comm, t.semi.smooth, hp, t.semi.geomConnected⟩
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim R t.G hab
  let P : Out.PolAV (Sp R) :=
    { A := t.G
      isAb := hab
      g := g
      smoothDim := hg
      L := t.PP.L
      isLB := t.PP.isLB
      rigid := ⟨t.PP.rig, t.PP.rigGen⟩
      sym := GlobalTheory.CechPic.sym_of_isSymmetric t.PP t.sym
      ample := hA
      ktriv := hK }
  refine ⟨P, Iso.refl _, ?_⟩
  intro S B _ f φ M h₁ h₂
  simp only [Iso.refl_hom, Over.id_left, Category.id_comp]
  exact ⟨h₁, h₂⟩

theorem relAmple_kTriv_of_generic_fibre : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (t : SAB H (Sp V)) (tK : SAB H (Sp K)) (_ : SABMap tK t (spMap (algebraMap V K))), IsProper t.G.hom → Out.RelAmple tK.G tK.PP.L → Out.KTriv tK.G tK.PP.L → Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L := by
  intro hH hL hL2 E _ _ _ H V K _ _ _ _ _ _ t tK m hp hA hK
  have hab : IsAbelianScheme t.G := ⟨t.comm, t.semi.smooth, hp, t.semi.geomConnected⟩
  have hiso : LBIso tK.PP.L (t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  obtain ⟨t', -, e, -, -, hA', hK'⟩ := GlobalTheory.T.exists_principallyPolarizedCM_extension_dvr hH hL hL2 E H V K t.G tK m.cm.F hab m.cart hA hK
  have hp' : IsProper t'.G.hom := by
    have := hp
    have : IsIso e.hom.left := ((Over.forget _).mapIso e).isIso_hom
    rw [← Over.w e.hom]
    infer_instance
  obtain ⟨P, e', -⟩ := exists_polAV t' hp' hA' hK'
  have : IsIso (e'.hom ≫ e.hom).left := ((Over.forget _).mapIso (e' ≪≫ e)).isIso_hom
  have hAmp : Out.RelAmple t.G t.PP.L :=
    GlobalTheory.T.relAmple_of_generic_isogenous_dedekind hL hL2 V K P t.G (e'.hom ≫ e.hom) t.PP.L tK.G m.cm.F tK.PP.L hab t.PP.isLB tK.PP.isLB
      inferInstance inferInstance inferInstance m.cart hiso hA
  refine ⟨hAmp, ?_⟩
  have hpK : IsProper tK.G.hom := MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 hp
  obtain ⟨P₀, e₀, hu⟩ := exists_polAV tK hpK hA hK
  obtain ⟨hpb, hlb⟩ := hu t.G (spMap (algebraMap V K)) m.cm.F t.PP.L m.cart hiso
  have hsym : ∃ s : LB.Gen (LB.LinComb t.PP.L (K := Fin 2) ![(ι[t.G]).left, 𝟙 t.G.left] ![1, -1]), s.IsGen := by
    obtain ⟨s, hs, -⟩ := GlobalTheory.SymmetricBundle.gen_of_isSymmetric t.PP t.sym
    exact ⟨s, hs⟩
  obtain ⟨M, hM⟩ := (GlobalTheory.T.abelianScheme_cubical_bundle_exists_and_maps hL.globalFns (Sp V) t.G hab).1 t.PP ⟨t.cub.t, t.cub.isGen⟩ hsym
  have key := GlobalTheory.T.thetaGroupK_trivial_of_principal_genericFibre_dvr hL V K P₀ t.G M (e₀.hom.left ≫ m.cm.F) hab hpb (by rw [hM]; exact hlb)
    (by rw [hM]; exact hAmp)
  rw [hM] at key
  exact key

end GlobalTheory.PolDvr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmplePrincipalOfGenericFibreDvrStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_principal_of_genericFibre_dvr : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (t : SAB H (Sp V)) (tK : SAB H (Sp K)) (_ : SABMap tK t (spMap (algebraMap V K))), IsProper t.G.hom → Out.RelAmple tK.G tK.PP.L → Out.KTriv tK.G tK.PP.L → Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L := by
  first | exact @GlobalTheory.PolDvr.relAmple_kTriv_of_generic_fibre | exact GlobalTheory.PolDvr.relAmple_kTriv_of_generic_fibre | (intros; apply GlobalTheory.PolDvr.relAmple_kTriv_of_generic_fibre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTopBaseModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.Models.RankZero

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {n N : ℕ}

section Point

variable {U : Scheme.{0}} {F O : Type} [Field F] [CommRing O] {c : U ⟶ Sp F} {t₀ : SAB H U}

def pointCpt (hc : IsIso c) (ht : IsIso t₀.G.hom) (β : O →+* F) (hn : Geo.Tor.IsNormalScheme (Sp O)) :
    Cpt c t₀ β where
  X := Sp O
  s := 𝟙 _
  normal := hn
  proj := Inhab.isProjOver_id O
  flat := inferInstance
  jQ := c ≫ inv (pullback.snd _ _)
  jQ_over := by simp
  jQ_open := inferInstance
  jQ_dense := by
    rw [Set.range_eq_univ.2 (c ≫ inv (pullback.snd (𝟙 _) (spMap β))).surjective]
    exact dense_univ
  t := Inhab.zeroTriple H _
  m := (nonempty_sabMap ht (isIso_zeroTriple _) _).some
  ab_gen := by
    rw [Set.range_eq_univ.2 (c ≫ inv (pullback.snd (𝟙 _) (spMap β))).surjective,
      Inhab.abLocus_eq_univ _ (Inhab.isProper_zeroTriple _), Set.preimage_univ]

end Point

theorem zeta_one : zeta 1 = 1 := (pow_one _).symm.trans (BaseRing.zeta_pow_self one_pos)

theorem KA_le_of_eq_one {l₀ : Level H} (h : l₀.A = 1) (l : Level H) : KA l₀ ≤ KA l := by
  refine IntermediateField.adjoin_le_iff.2 ?_
  rintro x (rfl | rfl)
  · exact IntermediateField.subset_adjoin _ _ (by simp)
  · rw [h, zeta_one]; exact one_mem _

end GlobalTheory.Models.RankZero

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGoodThetaObjectEmbeddingData
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEmbeddingSectionsOverField
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEmbeddingSectionsOverField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.EmbField

theorem exists_section_spMap {K R' : Type} [Field K] [CommRing R'] (φ : K →+* R') (hφ : IsOpenImmersion (spMap φ))
    (p : Sp K) (hp : p ∈ Set.range (spMap φ)) : ∃ ψ : R' →+* K, spMap ψ ≫ spMap φ = 𝟙 _ := by
  obtain ⟨a, -⟩ := hp
  have hsurj : Surjective (spMap φ) := ⟨fun q => ⟨a, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  have : IsIso (spMap φ) := (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨hφ, hsurj⟩
  refine ⟨(Spec.preimage (inv (spMap φ))).hom, ?_⟩
  have hinv : spMap (Spec.preimage (inv (spMap φ))).hom = inv (spMap φ) := by
    simp [spMap]
  rw [hinv, IsIso.inv_hom_id]

private theorem projRep_map_of_secCoord_iff {A B σ : Type} [CommRing A] [CommRing B]
    (ψ : A →+* B) (φ : B →+* A) (hψ : spMap ψ ≫ spMap φ = 𝟙 (Sp B))
    {Z Z' : Scheme.{0}} {s : Z ⟶ Sp A} {s' : Z' ⟶ Sp B} (jz : Z' ⟶ Z) [IsIso jz]
    (hjz : jz ≫ s = s' ≫ spMap ψ) {M : LB Z} {M' : LB Z'} {th : σ → M.Sec} {th' : σ → M'.Sec}
    (hM' : M'.IsLB)
    (e : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Z') (w : σ → T),
      SecCoord M' th' y w ↔ SecCoord M th (y ≫ jz) w)
    {I : Ideal (MvPolynomial σ A)} (h : ProjRep I s M th) :
    ProjRep (I.map (MvPolynomial.map ψ)) s' M' th' := by
  obtain ⟨-, hpt, hex⟩ := h
  have hs' : s' = jz ≫ s ≫ spMap φ := by
    rw [reassoc_of% hjz, hψ, Category.comp_id]
  have hcomp : ∀ (T : Type) [CommRing T] (β : B →+* T), spMap β ≫ spMap ψ = spMap (β.comp ψ) := by
    intro T _ β
    exact (spMap_comp β ψ).symm
  have hker : ∀ (T : Type) [CommRing T] (β : B →+* T) (v : σ → T),
      (∀ F ∈ I, MvPolynomial.eval₂ (β.comp ψ) v F = 0) →
        ∀ F ∈ I.map (MvPolynomial.map ψ), MvPolynomial.eval₂ β v F = 0 := by
    intro T _ β v hv F hF
    have hle : I.map (MvPolynomial.map ψ) ≤ RingHom.ker (MvPolynomial.eval₂Hom β v) := by
      refine Ideal.map_le_iff_le_comap.2 fun G hG => ?_
      simp only [Ideal.mem_comap, RingHom.mem_ker, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_map]
      exact hv G hG
    simpa [RingHom.mem_ker] using hle hF
  refine ⟨hM', fun T _ β x v hx hc => ?_, fun T _ β v hv hI => ?_⟩
  · have hx' : (x ≫ jz) ≫ s = spMap (β.comp ψ) := by
      rw [Category.assoc, hjz, ← Category.assoc, hx, hcomp]
    obtain ⟨hspan, hzero⟩ := hpt T (β.comp ψ) (x ≫ jz) v hx' ((e T x v).1 hc)
    exact ⟨hspan, hker T β v hzero⟩
  · have hI' : ∀ F ∈ I, MvPolynomial.eval₂ (β.comp ψ) v F = 0 := by
      intro F hF
      rw [← MvPolynomial.eval₂_map]
      exact hI _ (Ideal.mem_map_of_mem _ hF)
    obtain ⟨x₀, ⟨hx₀, hc₀⟩, hu⟩ := hex T (β.comp ψ) v hv hI'
    refine ⟨x₀ ≫ inv jz, ⟨?_, ?_⟩, fun y hy => ?_⟩
    · simp only [hs', Category.assoc, IsIso.inv_hom_id_assoc]
      rw [← Category.assoc, hx₀, ← hcomp, Category.assoc, hψ, Category.comp_id]
    · exact (e T _ v).2 (by rwa [Category.assoc, IsIso.inv_hom_id, Category.comp_id])
    · have hyx : y ≫ jz = x₀ :=
        hu _ ⟨by rw [Category.assoc, hjz, ← Category.assoc, hy.1, hcomp], (e T y v).1 hy.2⟩
      rw [← hyx, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

theorem exists_emb_field : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (K : Type) [Field K] (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (m : ℕ) (w : Ix g (N' ^ 2) → K), m ^ 2 ∣ N' → 2 ≤ m → t.HasTh (𝟙 _) w → ∃ (σ : Ix g (N' ^ 2) → LB.Sec (Out.LPow t.A t.L ((m : ℤ) ^ 2) (Over.mk (𝟙 _)))), t.Emb m (Over.mk (𝟙 _)) σ ∧ ProjRep (idealOf (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ (𝟙 _)) (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ := by
  intro hL hL2 o _ g N' J b K _ s t m w hm h2 hth
  have hLB : (Out.LPow t.A t.L ((m : ℤ) ^ 2) (Over.mk (𝟙 (Sp K)))).IsLB := by
    exact ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ t.isLB _ _
  obtain ⟨R', _, φ, σ, hφ, hp, hE, hP⟩ :=
    GlobalTheory.T.exists_local_multiplicationPullback_theta_embedding hL hL2 o g N' J b (Sp K) s t m K (𝟙 _) w hm h2 hth (default : PrimeSpectrum K)
  obtain ⟨ψ, hψ⟩ := exists_section_spMap φ hφ _ hp
  let h : Over.mk (𝟙 (Sp K)) ⟶ Over.mk (spMap φ ≫ 𝟙 (Sp K)) := Over.homMk (spMap ψ) (by simpa using hψ)
  have hA1 : IsAffine (Over.mk (spMap φ ≫ 𝟙 (Sp K))).left :=
    show IsAffine (Spec (CommRingCat.of R')) from inferInstance
  have hA2 : IsAffine (Over.mk (𝟙 (Sp K))).left :=
    show IsAffine (Spec (CommRingCat.of K)) from inferInstance
  obtain ⟨σ', hE', hc⟩ := GlobalTheory.emb_baseChange hL2 o g N' J b (Sp K) s t m _ _ h σ hA1 hA2 hE
  refine ⟨σ', hE', ?_⟩
  have : IsIso (spMap φ) := by
    obtain ⟨a, -⟩ := hp
    exact (isIso_iff_isOpenImmersion_and_surjective _).2
      ⟨hφ, ⟨fun q => ⟨a, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩⟩
  have : IsIso (spMap ψ ≫ spMap φ) := by rw [hψ]; infer_instance
  have : IsIso (spMap ψ) := IsIso.of_isIso_comp_right (spMap ψ) (spMap φ)
  have : IsIso ((Over.forget (Sp K)).map h) := show IsIso (spMap ψ) from inferInstance
  have : IsIso h := isIso_of_reflects_iso h (Over.forget (Sp K))
  have : IsIso (h ▷ t.A).left := show IsIso ((Over.forget (Sp K)).map (h ▷ t.A)) from inferInstance
  have hsq := (GlobalTheory.EmbPull.isPullback_whisker t.A h).w
  have hP' := projRep_map_of_secCoord_iff ψ φ hψ (h ▷ t.A).left hsq hLB hc hP
  exact ideals_homogeneous.2.2 K _ _ _ _ _ _ hP'

end GlobalTheory.ZM.EmbField
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEmbeddingSectionsOverFieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_embeddingSections_over_field : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (K : Type) [Field K] (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (m : ℕ) (w : Ix g (N' ^ 2) → K), m ^ 2 ∣ N' → 2 ≤ m → t.HasTh (𝟙 _) w → ∃ (σ : Ix g (N' ^ 2) → LB.Sec (Out.LPow t.A t.L ((m : ℤ) ^ 2) (Over.mk (𝟙 _)))), t.Emb m (Over.mk (𝟙 _)) σ ∧ ProjRep (idealOf (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ (𝟙 _)) (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ := by
  first | exact @GlobalTheory.ZM.EmbField.exists_emb_field | exact GlobalTheory.ZM.EmbField.exists_emb_field | (intros; apply GlobalTheory.ZM.EmbField.exists_emb_field <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGoodThetaObjectEmbeddingData
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.GoodFibre

theorem spMap_id (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 (Sp R) := by
  simp [spMap, Sp]

theorem exists_retraction {K R' : Type} [Field K] [CommRing R'] (φ : K →+* R') (hφ : IsOpenImmersion (spMap φ))
    (p : Sp K) (hp : p ∈ Set.range (spMap φ)) : ∃ ψ : R' →+* K, ψ.comp φ = RingHom.id K := by
  have hsurj : Function.Surjective (spMap φ) := by
    intro q
    obtain ⟨r, hr⟩ := hp
    exact ⟨r, Subsingleton.elim _ _⟩
  haveI : Surjective (spMap φ) := ⟨hsurj⟩
  haveI : IsIso (spMap φ) := (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨hφ, inferInstance⟩
  obtain ⟨ψ', hψ'⟩ := Spec.map_surjective (inv (spMap φ))
  refine ⟨ψ'.hom, ?_⟩
  have key : Spec.map (CommRingCat.ofHom φ ≫ ψ') = Spec.map (𝟙 _) := by
    rw [Spec.map_comp, hψ', Spec.map_id]
    exact IsIso.inv_hom_id (spMap φ)
  have := Spec.map_injective key
  ext a
  exact congrArg (fun f => f.hom a) this

theorem secCoord_of_local {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) {I : Type} {th : I → M.Sec} {K R' : Type} [Field K]
    [CommRing R'] {y : Sp K ⟶ X} {v : I → K} (φ : K →+* R') (hφ : IsOpenImmersion (spMap φ)) (p : Sp K)
    (hp : p ∈ Set.range (spMap φ)) (h : SecCoord M th (spMap φ ≫ y) (fun i => φ (v i))) : SecCoord M th y v := by
  obtain ⟨ψ, hψ⟩ := exists_retraction φ hφ p hp
  have h' := GlobalTheory.ZM.Coord.baseChange h ψ
  have e1 : spMap ψ ≫ spMap φ ≫ y = y := by
    rw [← Category.assoc, GlobalTheory.ZM.spMap_comp_ringHom_comp, hψ, spMap_id, Category.id_comp]
  have e2 : (fun i => ψ (φ (v i))) = v :=
    funext fun i => congrArg (fun f : K →+* K => f (v i)) hψ
  rw [e1, e2] at h'
  exact h'

theorem span_theta (l1 : Out.Laws) (l2 : Out.Laws2) {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)}
    {K : Type} [Field K] {s : Sp K ⟶ Sp o} (t : TObj g (N' ^ 2) J b s) (n : ℕ) (v : Ix g (N' ^ 2) → K)
    (h2 : 2 ≤ n) (hn : n ∣ N') (hth : t.HasTh (𝟙 _) v) : Ideal.span (Set.range v) = ⊤ := by
  by_contra hne
  obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal _ hne
  have hc := GlobalTheory.coset_of_hasTh l1 l2 o g N' J b (Sp K) s t n K (𝟙 _) v q h2 hn hth hq.isPrime
  unfold Coset at hc
  obtain ⟨c, hc⟩ := hc 0
  exact hc (hle (Ideal.subset_span ⟨_, rfl⟩))

theorem exists_fibData : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R), ∃ (p : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → R) (Hh : Type) (_ : Finite Hh) (hh : Hh → Ix g ((n ^ j) ^ 2)) (Q : Polynomial ℚ) (d : ℕ), FibData b Mat κ β v (n ^ 2) p hh Q d := by
  intro l1 l2 g J _ Mat κ n hn hodd
  obtain ⟨j₁, hj₁⟩ := GlobalTheory.cutBy_embedded_abelian l1 l2 g J Mat κ n hn hodd
  refine ⟨max j₁ 4, fun j hj o _ b R _ β v => ?_⟩
  have hjc : j₁ ≤ j := le_of_max_le_left hj
  have hj4 : 4 ≤ j := le_of_max_le_right hj
  have hoddN : Odd (n ^ j) := hodd.pow
  have hdvd : n ^ 2 ∣ n ^ j := pow_dvd_pow n (by omega)
  have hdvd2 : (n ^ 2) ^ 2 ∣ n ^ j := by
    rw [← pow_mul]
    exact pow_dvd_pow n (by omega)
  have htwo : 2 ≤ n ^ 2 := le_trans hn.two_le (Nat.le_self_pow (by norm_num) n)
  obtain ⟨e, idx, hto⟩ := GlobalTheory.torsion_secCoord l1 l2 g (n ^ 2) (n ^ j) hoddN hdvd2
  obtain ⟨Hh, hfin, hh, Q, d, hcut⟩ := hj₁ j hjc o b
  refine ⟨fun h a => β (b.ζ ^ e a h : oˣ) * v (idx a h), Hh, hfin, hh, Q, d, ?_⟩
  intro K _ _ x s t hgood
  obtain ⟨hs, -, hth⟩ := hgood
  rw [GlobalTheory.ZM.spMap_comp_ringHom_comp] at hs
  subst hs
  obtain ⟨σ, hemb, hproj⟩ := GlobalTheory.T.exists_embeddingSections_over_field l1 l2 o g (n ^ j) J b K _ t (n ^ 2) (fun a => x (v a)) hdvd2 htwo hth
  have hLB := (GlobalTheory.T.thetaSections_veryAmple_periodic l1 l2 o g (n ^ j) J b K (x.comp β) t (n ^ 2) σ hoddN hdvd htwo hemb).2.1
  have hspan : Ideal.span (Set.range fun a => x (v a)) = ⊤ :=
    span_theta l1 l2 t n (fun a => x (v a)) hn.two_le (dvd_pow_self n (by omega)) hth
  have hsec : ∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ n ^ j)).left
      (fun a => x (β (b.ζ ^ e a h : oˣ) * v (idx a h))) := by
    intro h
    have hy : ((Over.homMk (𝟙 (Sp K)) (by simp) : Over.mk (𝟙 (Sp K)) ⟶ Out.baseOver (Sp K)) ≫ t.lab h)
        = t.lab h := by
      ext
      simp
    obtain ⟨R', _, φ, hφ, hp, hc⟩ := hto o J b (Sp K) _ t K (x.comp β) (𝟙 _) (fun a => x (v a)) σ
      (Category.id_comp _) hth hspan hemb h _ (by rw [hy]) (IsLocalRing.closedPoint K)
    have key := secCoord_of_local hLB φ hφ _ hp hc
    have hv : (fun a => x (β (b.ζ ^ e a h : oˣ) * v (idx a h)))
        = (fun a => (x.comp β) (b.ζ ^ e a h : oˣ) * x (v (idx a h))) := by
      funext a
      simp
    rw [hv]
    exact key
  refine ⟨σ, _, hemb, hproj, ideals_homogeneous.1 _ _ _ _ _ _ σ _ hLB, ?_, hsec⟩
  exact hcut K (x.comp β) t σ _ hemb fun h => hsec (hh h)

end GlobalTheory.ZM.GoodFibre
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGoodThetaObjectEmbeddingDataStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_goodThetaObjectEmbeddingData : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R), ∃ (p : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → R) (Hh : Type) (_ : Finite Hh) (hh : Hh → Ix g ((n ^ j) ^ 2)) (Q : Polynomial ℚ) (d : ℕ), FibData b Mat κ β v (n ^ 2) p hh Q d := by
  first | exact @GlobalTheory.ZM.GoodFibre.exists_fibData | exact GlobalTheory.ZM.GoodFibre.exists_fibData | (intros; apply GlobalTheory.ZM.GoodFibre.exists_fibData <;> assumption)
end
end
