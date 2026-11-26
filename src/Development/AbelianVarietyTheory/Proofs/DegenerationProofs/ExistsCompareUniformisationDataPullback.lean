module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsMonHomOfPG

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCmpOfIsPullDeg
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPsiGeneratingOnWholeSpectrum
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPsiGeneratingOnWholeSpectrum
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.PsiTop

theorem exists_setPsi_psiOn_top : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R), ∃ ψ h, Nonempty (PsiOn (setPsi D ψ h) ⊤) := by
  intro R _ _ _ D
  have H : ∀ χ : D.X, ∃ t : LB.Gen (LB.LinComb D.P.L (K := PUnit) (Y := Spec (CommRingCat.of R))
      (fun _ => (D.c χ).left) (fun _ => -1)), t.IsGen := fun χ =>
    DVR.exists_gen_of_local D.P.L D.P.isLB _ _
  choose t ht using H
  refine ⟨fun χ => LB.pullGen D.P.L _ _ (t χ) (jK R), fun χ => DVR.pullGen_isGen _ _ _ _ (ht χ) _,
    ⟨⟨fun χ => LB.pullGen D.P.L _ _ (t χ) (⊤ : (Spec (CommRingCat.of R)).Opens).ι,
      fun χ => DVR.pullGen_isGen _ _ _ _ (ht χ) _, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩⟩⟩
  refine (val_pull hJ _ _ _).trans ((val_pull hJ (t χ) _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm))
  refine Eq.trans ?_ (val_pull hJ (t χ) _ _).symm
  rw [Category.assoc, Category.assoc, morphismRestrict_ι]

end GlobalTheory.PsiTop
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPsiGeneratingOnWholeSpectrumStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_psi_generating_on_whole_spectrum : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R), ∃ ψ h, Nonempty (PsiOn (setPsi D ψ h) ⊤) := by
  first | exact @GlobalTheory.PsiTop.exists_setPsi_psiOn_top | exact GlobalTheory.PsiTop.exists_setPsi_psiOn_top | (intros; apply GlobalTheory.PsiTop.exists_setPsi_psiOn_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsCubicalBundleMapOfPulledBackDegeneration
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsCubicalBundleMapOfPulledBackDegeneration
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

namespace GlobalTheory.DegPullPackage

theorem isCPMap_of_rig (hG : GlobalFnsSt) {S S' : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B]
    {f : S' ⟶ S} {B' : Over S'} [GrpObj B'] [IsCommMonObj B'] (hB' : IsAbelianScheme B') (M : CP B) (M' : CP B')
    {β : B'.left ⟶ B.left} {hw : β ≫ B.hom = B'.hom ≫ f}
    (mul : ∀ (T : Over S') (x y : T ⟶ B'), toBase hw (x * y) = toBase hw x * toBase hw y)
    (w : LB.Iso M'.L.L (M.L.L.pull β)) (hg : w.IsGen)
    (he : eSec B' ≫ β = f ≫ eSec B)
    (hr' : PMaps w (fun _ : PUnit => eSec B') (fun _ => eSec B) (fun _ => 1) M'.L.rig M.L.rig f) :
    IsCPMap M' M f β hw w := by
  obtain ⟨rig, hr, c, s, hs, h₂, h₃, H⟩ := exists_isCPMap M mul M'.L.L M'.L.isLB w hg
  let N : CP B' := ⟨⟨M'.L.L, rig, M'.L.isLB, hr⟩, c, s, hs, h₂, h₃⟩
  have es : ∀ (Z : Scheme.{0}) (r : Z ⟶ B'.left) (z : Z) (J), Good M'.L.L z J → val s r z J = val M'.sym r z J :=
    gen_unique M'.L.isLB B'.hom (1 : 𝟙_ (Over S') ⟶ B').left (Over.w _) (hG _ _ hB').2 hs M'.sym_gen
      fun y J hJ => (N.val_sym_one hJ).trans (M'.val_sym_one hJ).symm
  have ec : ∀ (T : Over S') (z : T.left) (J), Good M'.L.L z J → ∀ x y u : T ⟶ B',
      cubV c z J x y u = cubV M'.c z J x y u := fun T z J hJ x y u =>
    gen_unique M'.L.isLB (φ := thφ B' (x3 B')) (ε := thε) (G3 B').hom
      (lift (1 : 𝟙_ (Over S') ⟶ B') (lift 1 1)).left (Over.w _) (surjective_cube hG hB') c.isGen M'.c.isGen
      (fun y J hJ => ((isCub_cubV c hJ).face 1 1).trans ((isCub_cubV M'.c hJ).face 1 1).symm) _ _ z J hJ
  refine ⟨mul, hg, fun T z J' J hJ' hJ W hW => ?_⟩
  obtain ⟨-, a₂, a₃⟩ := H.vals T z J' J hJ' hJ W hW
  refine ⟨?_, fun x => ?_, fun x y u => ?_⟩
  · have e := CubTransport.val_pmaps (fun _ => he) hr' T.hom hJ hJ'
    rw [Fintype.prod_unique, zpow_one] at e
    rw [hW, one_left]
    exact e
  · exact (a₂ x).trans (congrArg (W x⁻¹ * ·) (es _ x.left z J' hJ'))
  · exact (a₃ x y u).trans (congrArg (W (x * y * u) * W x * W y * W u * ·) (ec T z J' hJ' x y u))

theorem isCPMap_of_isPullDeg : ∀ (hG : GlobalFnsSt) (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (hD : IsPullDeg φ D D'), IsCPMap (CP.ofDegPre hG D') (CP.ofDegPre hG D) (spMap φ) (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) (pull_grp hD).1.w hD.w := by
  intro hG R V _ _ _ _ φ D D' hD
  exact isCPMap_of_rig hG D'.P.isAb (CP.ofDegPre hG D) (CP.ofDegPre hG D')
    (fun T x y => Over.OverMorphism.ext ((pull_grp hD).2 T x y _ _ rfl rfl).symm) hD.w hD.w_gen hD.he
    ((maps_iff hD.w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf φ) _
      (rigPull_le (G' := D'.P.A) (G := D.P.A) _ (specOf φ) hD.he D.P.L) (fun _ => rfl)).1 hD.w_rig)

end GlobalTheory.DegPullPackage
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsCubicalBundleMapOfPulledBackDegenerationStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCubicalBundleMap_of_pulled_back_degeneration : ∀ (hG : GlobalFnsSt) (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (hD : IsPullDeg φ D D'), IsCPMap (CP.ofDegPre hG D') (CP.ofDegPre hG D) (spMap φ) (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) (pull_grp hD).1.w hD.w := by
  first | exact @GlobalTheory.DegPullPackage.isCPMap_of_isPullDeg | exact GlobalTheory.DegPullPackage.isCPMap_of_isPullDeg | (intros; apply GlobalTheory.DegPullPackage.isCPMap_of_isPullDeg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FourthSideRespectsRigSymmetryCube
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FourthSideRespectsRigSymmetryCube
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.LN.FourthSide

section General
variable {S Z : Scheme.{0}} {G : Over S} [GrpObj G] {s s' : Z ⟶ S}

theorem mul_left_congr {x y : Over.mk s ⟶ G} {x' y' : Over.mk s' ⟶ G} (hx : x.left = x'.left)
    (hy : y.left = y'.left) : (x * y).left = (x' * y').left := by
  obtain rfl : s = s' := (Over.w x).symm.trans ((congrArg (· ≫ G.hom) hx).trans (Over.w x'))
  rw [Over.OverMorphism.ext hx, Over.OverMorphism.ext hy]

theorem cubV_congr [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L) (z : Z) (J) {x y u : Over.mk s ⟶ G}
    {x' y' u' : Over.mk s' ⟶ G} (hx : x.left = x'.left) (hy : y.left = y'.left) (hu : u.left = u'.left) :
    @id (Z.presheaf.stalk z)ˣ (cubV c (T := Over.mk s) z J x y u) =
      @id (Z.presheaf.stalk z)ˣ (cubV c (T := Over.mk s') z J x' y' u') := by
  obtain rfl : s = s' := (Over.w x).symm.trans ((congrArg (· ≫ G.hom) hx).trans (Over.w x'))
  rw [Over.OverMorphism.ext hx, Over.OverMorphism.ext hy, Over.OverMorphism.ext hu]

end General

theorem cube_alg {A A₀ A₁ A₂ M : Type} [CommGroup A] [CommGroup A₀] [CommGroup A₁] [CommGroup A₂] [CommGroup M]
    (n : A →* A₀) (a : A →* A₁) (b : A →* A₂) {W : A → M} {W₀ : A₀ → M} {W₁ : A₁ → M} {W₂ : A₂ → M}
    (sq : ∀ x, W₂ (b x) * W x = W₀ (n x) * W₁ (a x)) (x y u : A) {C C' E E' : M}
    (h₀ : C * W₀ (n x * n y) * W₀ (n x * n u) * W₀ (n y * n u) * W₀ 1 =
      W₀ (n x * n y * n u) * W₀ (n x) * W₀ (n y) * W₀ (n u) * E)
    (h₁ : E * W₁ (a x * a y) * W₁ (a x * a u) * W₁ (a y * a u) * W₁ 1 =
      W₁ (a x * a y * a u) * W₁ (a x) * W₁ (a y) * W₁ (a u) * E')
    (h₂ : C * W₂ (b x * b y) * W₂ (b x * b u) * W₂ (b y * b u) * W₂ 1 =
      W₂ (b x * b y * b u) * W₂ (b x) * W₂ (b y) * W₂ (b u) * C') :
    C' * W (x * y) * W (x * u) * W (y * u) * W 1 = W (x * y * u) * W x * W y * W u * E' := by
  have e : ∀ x, W x = (W₂ (b x))⁻¹ * (W₀ (n x) * W₁ (a x)) := fun x => eq_inv_mul_of_mul_eq (sq x)
  simp only [e, map_mul, map_one]
  apply Additive.ofMul.injective
  have k₀ := congrArg Additive.ofMul h₀
  have k₁ := congrArg Additive.ofMul h₁
  have k₂ := congrArg Additive.ofMul h₂
  simp only [ofMul_mul, ofMul_inv] at k₀ k₁ k₂ ⊢
  linear_combination (norm := abel) k₀ + k₁ - k₂

theorem sym_alg {A A₀ A₁ A₂ M : Type} [CommGroup A] [CommGroup A₀] [CommGroup A₁] [CommGroup A₂] [CommGroup M]
    (n : A →* A₀) (a : A →* A₁) (b : A →* A₂) {W : A → M} {W₀ : A₀ → M} {W₁ : A₁ → M} {W₂ : A₂ → M}
    (sq : ∀ x, W₂ (b x) * W x = W₀ (n x) * W₁ (a x)) (x : A) {C C' E E' : M}
    (h₀ : C * W₀ (n x) = W₀ (n x)⁻¹ * E) (h₁ : E * W₁ (a x) = W₁ (a x)⁻¹ * E')
    (h₂ : C * W₂ (b x) = W₂ (b x)⁻¹ * C') : C' * W x = W x⁻¹ * E' := by
  have e : ∀ x, W x = (W₂ (b x))⁻¹ * (W₀ (n x) * W₁ (a x)) := fun x => eq_inv_mul_of_mul_eq (sq x)
  simp only [e, map_inv]
  apply Additive.ofMul.injective
  have k₀ := congrArg Additive.ofMul h₀
  have k₁ := congrArg Additive.ofMul h₁
  have k₂ := congrArg Additive.ofMul h₂
  simp only [ofMul_mul, ofMul_inv] at k₀ k₁ k₂ ⊢
  linear_combination (norm := abel) k₀ + k₁ - k₂

theorem rig_alg {M : Type} [CommGroup M] {W W₀ W₁ W₂ C C' E E' : M} (sq : W₂ * W = W₀ * W₁) (h₀ : C = W₀ * E)
    (h₁ : E = W₁ * E') (h₂ : C = W₂ * C') : C' = W * E' :=
  mul_left_cancel (a := W₂) (by rw [← h₂, h₀, h₁, ← _root_.mul_assoc, ← _root_.mul_assoc, sq])

theorem pG_mul {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {e : ℕ} (g : GtCoord I D e G)
    (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (x y : T ⟶ thickObj R I e G) :
    toBase (A' := thickObj R I e G) (f := thick R I e) (g := g.pG.left) (Over.w g.pG) (x * y) =
      toBase (Over.w g.pG) x * toBase (Over.w g.pG) y := by
  have := g.q_hom
  have := toBase_mul_pullback D.P.A (thick R I e) T (x ≫ g.q) (y ≫ g.q)
  rw [← MonObj.mul_comp] at this
  have a : ∀ x : T ⟶ thickObj R I e G, toBase (Over.w g.pG) x =
      toBase (A := D.P.A) (g := pullback.fst D.P.A.hom (thick R I e)) pullback.condition (x ≫ g.q) :=
    fun x => Over.OverMorphism.ext (Category.assoc _ _ _).symm
  exact (a _).trans (this.trans (congrArg₂ (· * ·) (a x) (a y)).symm)


set_option maxHeartbeats 1000000 in
theorem fourth_side_vals : ∀ (hG : GlobalFnsSt) (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (I : Ideal R) (I' : Ideal V) (φ : R →+* V), I.map φ ≤ I' → ∀ (D : DegPre R) (D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (P' : CP G') (F : G'.left ⟶ G.left) (hF : F ≫ G.hom = G'.hom ≫ spMap φ) (wL : LB.Iso P'.L.L (U.P.L.L.pull F)), IsCPMap P' U.P (spMap φ) F hF wL → ∀ (β : D'.P.A.left ⟶ D.P.A.left) (hβ : β ≫ D.P.A.hom = D'.P.A.hom ≫ spMap φ) (v : LB.Iso D'.P.L (D.P.L.pull β)), IsCPMap (CP.ofDegPre hG D') (CP.ofDegPre hG D) (spMap φ) β hβ v → ∀ (e : ℕ) (g' : GtCoord I' D' e G') (h : (thickObj V I' e G').left ⟶ (thickObj R I e G).left), h ≫ (fstG I e G).left = (fstG I' e G').left ≫ F → g'.pG.left ≫ β = h ≫ (U.gt e).pG.left → ∀ w' : LB.Iso (P'.L.L.pull (fstG I' e G').left) (D'.P.L.pull g'.pG.left), (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj V I' e G').left) (z : Z) (jM : D.P.L.ι) (jM' : D'.P.L.ι) (jL : U.P.L.L.ι) (jL' : P'.L.L.ι), β (g'.pG.left (r z)) ∈ D.P.L.U jM → g'.pG.left (r z) ∈ D'.P.L.U jM' → F ((fstG I' e G').left (r z)) ∈ U.P.L.L.U jL → (fstG I' e G').left (r z) ∈ P'.L.L.U jL' → gw v (r ≫ g'.pG.left) z jM jM' * gw w' r z jM' (fun _ => jL') = gw (U.w e) (r ≫ h) z jM (fun _ => jL) * gw wL (r ≫ (fstG I' e G').left) z jL jL') → ∀ (T : Over (Spec (CommRingCat.of (V ⧸ I' ^ (e + 1))))) (z : T.left) (JG : (T.left ⟶ G'.left) → P'.L.L.ι) (J : (T.left ⟶ D'.P.A.left) → D'.P.L.ι), Good P'.L.L z JG → Good D'.P.L z J → ∀ W : (T ⟶ thickObj V I' e G') → (T.left.presheaf.stalk z)ˣ, (∀ x, W x = gw w' x.left z (J (x.left ≫ g'.pG.left)) (fun _ => JG (x.left ≫ (fstG I' e G').left))) → (val (L := D'.P.L) (φ := fun _ : PUnit => eSec D'.P.A) (ε := fun _ => 1) D'.rig (T.hom ≫ thick V I' e) z J = W 1 * val (L := P'.L.L) (φ := fun _ : PUnit => eSec G') (ε := fun _ => 1) P'.L.rig (T.hom ≫ thick V I' e) z JG) ∧ (∀ x : T ⟶ thickObj V I' e G', val D'.sym (x.left ≫ g'.pG.left) z J * W x = W x⁻¹ * val P'.sym (x.left ≫ (fstG I' e G').left) z JG) ∧ ∀ x y u : T ⟶ thickObj V I' e G', @id (T.left.presheaf.stalk z)ˣ (cubV D'.cub (T := (Over.map (thick V I' e)).obj T) z J ((Over.map (thick V I' e)).map x ≫ g'.pG) ((Over.map (thick V I' e)).map y ≫ g'.pG) ((Over.map (thick V I' e)).map u ≫ g'.pG)) * W (x * y) * W (x * u) * W (y * u) * W 1 = W (x * y * u) * W x * W y * W u * @id (T.left.presheaf.stalk z)ˣ (cubV P'.c (T := (Over.map (thick V I' e)).obj T) z JG ((Over.map (thick V I' e)).map x ≫ fstG I' e G') ((Over.map (thick V I' e)).map y ≫ fstG I' e G') ((Over.map (thick V I' e)).map u ≫ fstG I' e G')) := by
  intro hG R V _ _ _ _ I I' φ hle D D' A G _ _ G' _ _ U P' F hF wL hwL β hβ v hv e g' h hh hp w' hsq T z JG J hJG hJ W hW
  have hpow : I ^ (e + 1) ≤ (I' ^ (e + 1)).comap φ := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono hle _
  obtain ⟨σ, hσ⟩ : ∃ σ : Spec (CommRingCat.of (V ⧸ I' ^ (e + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))),
      σ ≫ thick R I e = thick V I' e ≫ spMap φ :=
    ⟨spMap (Ideal.quotientMap (I' ^ (e + 1)) φ hpow), by rw [← Spec.map_comp, ← Spec.map_comp]; rfl⟩
  have : IsClosedImmersion (thick R I e) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have := Cmp.mono_fstG I e G
  have hb : (T.hom ≫ σ) ≫ thick R I e = (T.hom ≫ thick V I' e) ≫ spMap φ := by
    rw [Category.assoc, hσ, Category.assoc]
  let a := toBaseHom (toBase_mul_pullback G' (thick V I' e)) T
  let b := toBaseHom (pG_mul g') T
  have ha : ∀ x : T ⟶ thickObj V I' e G', (x.left ≫ h) ≫ (fstG I e G).left = (a x).left ≫ F := fun x =>
    (Category.assoc _ _ _).trans ((congrArg (x.left ≫ ·) hh).trans (Category.assoc _ _ _).symm)
  have hq : ∀ x : T ⟶ thickObj V I' e G', (x.left ≫ h) ≫ (U.gt e).pG.left = (b x).left ≫ β := fun x =>
    (Category.assoc _ _ _).trans ((congrArg (x.left ≫ ·) hp.symm).trans (Category.assoc _ _ _).symm)
  have hs : ∀ x : T ⟶ thickObj V I' e G', (x.left ≫ h) ≫ (thickObj R I e G).hom = T.hom ≫ σ := fun x => by
    rw [← cancel_mono (thick R I e), hb, Category.assoc]
    refine (congrArg ((x.left ≫ h) ≫ ·) (Over.w (fstG I e G)).symm).trans ?_
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ G.hom) (ha x)).trans ?_)
    exact Over.w (toBase (T := Over.mk (T.hom ≫ thick V I' e)) hF (a x))
  let n₀ : (T ⟶ thickObj V I' e G') → (Over.mk (T.hom ≫ σ) ⟶ thickObj R I e G) :=
    fun x => Over.homMk (x.left ≫ h) (hs x)
  let n : (T ⟶ thickObj V I' e G') →* (Over.mk (T.hom ≫ σ) ⟶ thickObj R I e G) := MonoidHom.mk' n₀ fun x y => by
    refine Over.OverMorphism.ext ((cancel_mono (fstG I e G).left).1 ((ha (x * y)).trans ?_))
    rw [map_mul]
    refine (congrArg (fun q => q.left) (hwL.mul _ (a x) (a y))).trans (Eq.trans ?_
      (congrArg (fun q => q.left) (toBase_mul_pullback G (thick R I e) _ (n₀ x) (n₀ y))).symm)
    exact mul_left_congr (ha x).symm (ha y).symm
  obtain ⟨K, hK⟩ := exists_good_pt U.P.L.isLB z
  obtain ⟨J₀, hJ₀⟩ := exists_good_pt D.P.isLB z
  obtain ⟨W₀, hW₀⟩ : ∃ W₀ : (Over.mk (T.hom ≫ σ) ⟶ thickObj R I e G) → (T.left.presheaf.stalk z)ˣ, ∀ x, W₀ x =
    gw (U.w e) x.left z (J₀ (x.left ≫ (U.gt e).pG.left)) (fun _ => K (x.left ≫ (fstG I e G).left)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨W₁, hW₁⟩ : ∃ W₁ : (Over.mk (T.hom ≫ thick V I' e) ⟶ G') → (T.left.presheaf.stalk z)ˣ, ∀ x, W₁ x =
    gw wL x.left z (K (x.left ≫ F)) (JG x.left) := ⟨_, fun _ => rfl⟩
  obtain ⟨W₂, hW₂⟩ : ∃ W₂ : (Over.mk (T.hom ≫ thick V I' e) ⟶ D'.P.A) → (T.left.presheaf.stalk z)ˣ, ∀ x, W₂ x =
    gw v x.left z (J₀ (x.left ≫ β)) (J x.left) := ⟨_, fun _ => rfl⟩
  obtain ⟨p₁, p₂, p₃⟩ := U.w_vals e (Over.mk (T.hom ≫ σ)) z K J₀ hK hJ₀ W₀ hW₀
  obtain ⟨q₁, q₂, q₃⟩ := hwL.vals (Over.mk (T.hom ≫ thick V I' e)) z JG K hJG hK W₁ hW₁
  obtain ⟨r₁, r₂, r₃⟩ := hv.vals (Over.mk (T.hom ≫ thick V I' e)) z J J₀ hJ hJ₀ W₂ hW₂
  have sq : ∀ x, W₂ (b x) * W x = W₀ (n x) * W₁ (a x) := fun x => by
    have k := hsq _ x.left z _ _ _ _ (hJ₀ ((b x).left ≫ β)) (hJ (b x).left) (hK ((a x).left ≫ F)) (hJG (a x).left)
    have k₀ : W₀ (n x) = gw (U.w e) (x.left ≫ h) z (J₀ ((b x).left ≫ β)) (fun _ => K ((a x).left ≫ F)) := by
      rw [← ha, ← hq]
      exact hW₀ (n x)
    rw [k₀, hW, hW₁, hW₂]
    exact k
  refine ⟨?_, fun x => ?_, fun x y u => ?_⟩
  · have k := sq 1
    rw [map_one, map_one, map_one] at k
    have p : val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig
        ((T.hom ≫ σ) ≫ thick R I e) z J₀ = W₀ 1 * val (L := U.P.L.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1)
          U.P.L.rig ((T.hom ≫ σ) ≫ thick R I e) z K := p₁
    rw [hb] at p
    exact rig_alg k p q₁ r₁
  · have p : val D.sym ((x.left ≫ h) ≫ (U.gt e).pG.left) z J₀ * W₀ (n x) =
        W₀ (n x)⁻¹ * val U.P.sym ((x.left ≫ h) ≫ (fstG I e G).left) z K := p₂ (n x)
    rw [ha, hq] at p
    have q : val U.P.sym ((x.left ≫ (fstG I' e G').left) ≫ F) z K * W₁ (a x) =
        W₁ (a x)⁻¹ * val P'.sym (x.left ≫ (fstG I' e G').left) z JG := q₂ (a x)
    have r : val D.sym ((x.left ≫ g'.pG.left) ≫ β) z J₀ * W₂ (b x) =
        W₂ (b x)⁻¹ * val D'.sym (x.left ≫ g'.pG.left) z J := r₂ (b x)
    exact sym_alg n a b sq x p q r
  · let C : (T.left.presheaf.stalk z)ˣ := cubV D.cub (T := Over.mk ((T.hom ≫ thick V I' e) ≫ spMap φ)) z J₀
      (toBase (T := Over.mk (T.hom ≫ thick V I' e)) hβ (b x))
      (toBase (T := Over.mk (T.hom ≫ thick V I' e)) hβ (b y))
      (toBase (T := Over.mk (T.hom ≫ thick V I' e)) hβ (b u))
    let E : (T.left.presheaf.stalk z)ˣ := cubV U.P.c (T := Over.mk ((T.hom ≫ thick V I' e) ≫ spMap φ)) z K
      (toBase (T := Over.mk (T.hom ≫ thick V I' e)) hF (a x))
      (toBase (T := Over.mk (T.hom ≫ thick V I' e)) hF (a y))
      (toBase (T := Over.mk (T.hom ≫ thick V I' e)) hF (a u))
    let C' : (T.left.presheaf.stalk z)ˣ := cubV D'.cub (T := Over.mk (T.hom ≫ thick V I' e)) z J (b x) (b y) (b u)
    let E' : (T.left.presheaf.stalk z)ˣ := cubV P'.c (T := Over.mk (T.hom ≫ thick V I' e)) z JG (a x) (a y) (a u)
    let C₀ : (T.left.presheaf.stalk z)ˣ := cubV D.cub (T := (Over.map (thick R I e)).obj (Over.mk (T.hom ≫ σ))) z J₀
      ((Over.map (thick R I e)).map (n x) ≫ (U.gt e).pG) ((Over.map (thick R I e)).map (n y) ≫ (U.gt e).pG)
      ((Over.map (thick R I e)).map (n u) ≫ (U.gt e).pG)
    let E₀ : (T.left.presheaf.stalk z)ˣ := cubV U.P.c (T := (Over.map (thick R I e)).obj (Over.mk (T.hom ≫ σ))) z K
      ((Over.map (thick R I e)).map (n x) ≫ fstG I e G) ((Over.map (thick R I e)).map (n y) ≫ fstG I e G)
      ((Over.map (thick R I e)).map (n u) ≫ fstG I e G)
    have hC : C₀ = C := cubV_congr (s := (T.hom ≫ σ) ≫ thick R I e) (s' := (T.hom ≫ thick V I' e) ≫ spMap φ)
      D.cub z J₀ (hq x) (hq y) (hq u)
    have hE : E₀ = E := cubV_congr (s := (T.hom ≫ σ) ≫ thick R I e) (s' := (T.hom ≫ thick V I' e) ≫ spMap φ)
      U.P.c z K (ha x) (ha y) (ha u)
    have p : C₀ * W₀ (n x * n y) * W₀ (n x * n u) * W₀ (n y * n u) * W₀ 1 =
      W₀ (n x * n y * n u) * W₀ (n x) * W₀ (n y) * W₀ (n u) * E₀ := p₃ (n x) (n y) (n u)
    have q : E * W₁ (a x * a y) * W₁ (a x * a u) * W₁ (a y * a u) * W₁ 1 =
      W₁ (a x * a y * a u) * W₁ (a x) * W₁ (a y) * W₁ (a u) * E' := q₃ (a x) (a y) (a u)
    have r : C * W₂ (b x * b y) * W₂ (b x * b u) * W₂ (b y * b u) * W₂ 1 =
      W₂ (b x * b y * b u) * W₂ (b x) * W₂ (b y) * W₂ (b u) * C' := r₃ (b x) (b y) (b u)
    rw [hC, hE] at p
    have k := cube_alg n a b sq x y u p q r
    have hC' : C' = cubV D'.cub (T := (Over.map (thick V I' e)).obj T) z J
        ((Over.map (thick V I' e)).map x ≫ g'.pG) ((Over.map (thick V I' e)).map y ≫ g'.pG)
        ((Over.map (thick V I' e)).map u ≫ g'.pG) :=
      cubV_congr (s := T.hom ≫ thick V I' e) (s' := T.hom ≫ thick V I' e) D'.cub z J rfl rfl rfl
    have hE' : E' = cubV P'.c (T := (Over.map (thick V I' e)).obj T) z JG
        ((Over.map (thick V I' e)).map x ≫ fstG I' e G') ((Over.map (thick V I' e)).map y ≫ fstG I' e G')
        ((Over.map (thick V I' e)).map u ≫ fstG I' e G') :=
      cubV_congr (s := T.hom ≫ thick V I' e) (s' := T.hom ≫ thick V I' e) P'.c z JG rfl rfl rfl
    rw [hC', hE'] at k
    exact k

end GlobalTheory.LN.FourthSide
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FourthSideRespectsRigSymmetryCubeStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourthSide_respects_rig_symmetry_cube : ∀ (hG : GlobalFnsSt) (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (I : Ideal R) (I' : Ideal V) (φ : R →+* V), I.map φ ≤ I' → ∀ (D : DegPre R) (D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (P' : CP G') (F : G'.left ⟶ G.left) (hF : F ≫ G.hom = G'.hom ≫ spMap φ) (wL : LB.Iso P'.L.L (U.P.L.L.pull F)), IsCPMap P' U.P (spMap φ) F hF wL → ∀ (β : D'.P.A.left ⟶ D.P.A.left) (hβ : β ≫ D.P.A.hom = D'.P.A.hom ≫ spMap φ) (v : LB.Iso D'.P.L (D.P.L.pull β)), IsCPMap (CP.ofDegPre hG D') (CP.ofDegPre hG D) (spMap φ) β hβ v → ∀ (e : ℕ) (g' : GtCoord I' D' e G') (h : (thickObj V I' e G').left ⟶ (thickObj R I e G).left), h ≫ (fstG I e G).left = (fstG I' e G').left ≫ F → g'.pG.left ≫ β = h ≫ (U.gt e).pG.left → ∀ w' : LB.Iso (P'.L.L.pull (fstG I' e G').left) (D'.P.L.pull g'.pG.left), (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj V I' e G').left) (z : Z) (jM : D.P.L.ι) (jM' : D'.P.L.ι) (jL : U.P.L.L.ι) (jL' : P'.L.L.ι), β (g'.pG.left (r z)) ∈ D.P.L.U jM → g'.pG.left (r z) ∈ D'.P.L.U jM' → F ((fstG I' e G').left (r z)) ∈ U.P.L.L.U jL → (fstG I' e G').left (r z) ∈ P'.L.L.U jL' → gw v (r ≫ g'.pG.left) z jM jM' * gw w' r z jM' (fun _ => jL') = gw (U.w e) (r ≫ h) z jM (fun _ => jL) * gw wL (r ≫ (fstG I' e G').left) z jL jL') → ∀ (T : Over (Spec (CommRingCat.of (V ⧸ I' ^ (e + 1))))) (z : T.left) (JG : (T.left ⟶ G'.left) → P'.L.L.ι) (J : (T.left ⟶ D'.P.A.left) → D'.P.L.ι), Good P'.L.L z JG → Good D'.P.L z J → ∀ W : (T ⟶ thickObj V I' e G') → (T.left.presheaf.stalk z)ˣ, (∀ x, W x = gw w' x.left z (J (x.left ≫ g'.pG.left)) (fun _ => JG (x.left ≫ (fstG I' e G').left))) → (val (L := D'.P.L) (φ := fun _ : PUnit => eSec D'.P.A) (ε := fun _ => 1) D'.rig (T.hom ≫ thick V I' e) z J = W 1 * val (L := P'.L.L) (φ := fun _ : PUnit => eSec G') (ε := fun _ => 1) P'.L.rig (T.hom ≫ thick V I' e) z JG) ∧ (∀ x : T ⟶ thickObj V I' e G', val D'.sym (x.left ≫ g'.pG.left) z J * W x = W x⁻¹ * val P'.sym (x.left ≫ (fstG I' e G').left) z JG) ∧ ∀ x y u : T ⟶ thickObj V I' e G', @id (T.left.presheaf.stalk z)ˣ (cubV D'.cub (T := (Over.map (thick V I' e)).obj T) z J ((Over.map (thick V I' e)).map x ≫ g'.pG) ((Over.map (thick V I' e)).map y ≫ g'.pG) ((Over.map (thick V I' e)).map u ≫ g'.pG)) * W (x * y) * W (x * u) * W (y * u) * W 1 = W (x * y * u) * W x * W y * W u * @id (T.left.presheaf.stalk z)ˣ (cubV P'.c (T := (Over.map (thick V I' e)).obj T) z JG ((Over.map (thick V I' e)).map x ≫ fstG I' e G') ((Over.map (thick V I' e)).map y ≫ fstG I' e G') ((Over.map (thick V I' e)).map u ≫ fstG I' e G')) := by
  first | exact @GlobalTheory.LN.FourthSide.fourth_side_vals | exact GlobalTheory.LN.FourthSide.fourth_side_vals | (intros; apply GlobalTheory.LN.FourthSide.fourth_side_vals <;> assumption)
end
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.LN.PreBaseChange

theorem exists_cmp_of_isPullDeg (hG : GlobalFnsSt) {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V]
    {I : Ideal R} {I' : Ideal V} {φ : R →+* V} (hI : I.map φ ≤ I') {D : DegPre R} {D₁ D' : DegPre V}
    (hD : IsPullDeg φ D D₁) {A : PolAV (Sp (FractionRing R))} {A' : PolAV (Sp (FractionRing V))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {G' : Over (Spec (CommRingCat.of V))} [GrpObj G']
    [IsCommMonObj G'] (U : PreU I D A G) (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left)
    (pb : IsGrpPullback G' G (spMap φ) F) (wL : LB.Iso U'.P.L.L (U.P.L.L.pull F))
    (hw : IsCPMap U'.P U.P (spMap φ) F pb.1.w wL) :
    ∃ (U₁ : PreU I' D₁ A' G') (C : Cmp φ U U₁ F), U₁.P = U'.P ∧ HEq C.wL wL := by
  obtain ⟨bc, hbc, rfl⟩ := grpPullback_iso pb (isGrpPullback_pullback G (specOf φ))
  choose h q' i' hh hq' using fun e => gtCoord_baseChange_maps R V φ D D₁ hD I I' hI G G' bc hbc e (U.gt e)
  choose g _ hg using fun e => exists_gtCoord_pull hG R V φ D D₁ hD I I' hI G G' bc hbc e (U.gt e) (h e) (q' e)
    (i' e) (hh e) (hq' e)
  have hc := fun e => gtCoord_compat_of_pull R V φ D D₁ hD I I' G G' _ e (U.gt e) (U.gt (e + 1)) (g e) (g (e + 1))
    (h e) (h (e + 1)) (hh e) (hh (e + 1)) (hg e) (hg (e + 1)) (U.gt_q e) (U.gt_t e)
  choose w w_gen sq using fun e => FourthSide.exists_fourth_side _ _ _ _ _ _ D.P.L D₁.P.L U.P.L.L U'.P.L.L D.P.isLB
    D₁.P.isLB U.P.L.isLB U'.P.L.isLB _ _ (U.gt e).pG.left (g e).pG.left (fstG I e G).left (fstG I' e G').left (h e)
    (hg e).1 (hh e) hD.w wL (U.w e) hD.w_gen hw.gen (U.w_gen e)
  have pt : ∀ {Z X Y : Scheme.{0}} {a b : X ⟶ Y} (_ : a = b) (x : Z ⟶ X) (z : Z) {W : Y.Opens},
      a (x z) ∈ W → b (x z) ∈ W := fun e _ _ _ k => e ▸ k
  have compat : ∀ (e : ℕ) (Z : Scheme.{0}) (x : Z ⟶ (thickObj V I' e G').left) (z : Z) (j : D₁.P.L.ι)
      (k : U'.P.L.L.ι), (g e).pG.left (x z) ∈ D₁.P.L.U j → (fstG I' e G').left (x z) ∈ U'.P.L.L.U k →
      gw (w (e + 1)) (x ≫ thickMap V I' e G') z j (fun _ => k) = gw (w e) x z j (fun _ => k) := by
    intro e Z x z j k hj hk
    have := Cmp.mono_fstG I (e + 1) G
    have t := LevelCompat.thickMap_fstG I e G
    have t' := LevelCompat.thickMap_fstG I' e G'
    have hm : thickMap V I' e G' ≫ h (e + 1) = h e ≫ thickMap R I e G := by
      rw [← cancel_mono (fstG I (e + 1) G).left, Category.assoc, hh (e + 1), ← Category.assoc, t', Category.assoc, t,
        hh e]
    obtain ⟨jM, hM⟩ := exists_chart D.P.isLB
      ((hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ((g e).pG.left (x z)))
    obtain ⟨jL, hL⟩ := exists_chart U.P.L.isLB
      ((bc.hom.left ≫ pullback.fst G.hom (specOf φ)) ((fstG I' e G').left (x z)))
    have a₀ := sq e Z x z jM j jL k hM hj hL hk
    have a₁ := sq (e + 1) Z (x ≫ thickMap V I' e G') z jM j jL k
      (pt (congrArg (· ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) (hc e).1).symm x z hM)
      (pt (hc e).1.symm x z hj)
      (pt (congrArg (· ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ)) t').symm x z hL) (pt t'.symm x z hk)
    have b := U.w_compat e Z (x ≫ h e) z jM jL (pt (hg e).1 x z hM) (pt (hh e).symm x z hL)
    rw [Category.assoc x, Category.assoc x, Category.assoc x, (hc e).1, t', hm, ← Category.assoc x (h e), b] at a₁
    exact mul_left_cancel (a₁.trans a₀.symm)
  refine ⟨⟨U'.semi, U'.gen, U'.gen_hom, U'.P, U'.wA, U'.wA_gen, g, fun e => (hc e).1, fun e => (hc e).2, w, w_gen,
      fun e => GlobalTheory.T.fourthSide_respects_rig_symmetry_cube hG R V I I' φ hI D D₁ A G G' U U'.P _ _ wL hw _ _ hD.w (GlobalTheory.T.isCubicalBundleMap_of_pulled_back_degeneration hG R V φ D D₁ hD) e
        (g e) (h e) (hh e) (hg e).1 (w e) (sq e), compat⟩,
    ⟨pb, wL, hw, _, pull_grp hD, hD.w, hD.w_gen, hD.xe, hD.c_pr, fun e Z x' x hx => ?_, hI⟩, rfl, HEq.rfl⟩
  have := Cmp.mono_fstG I e G
  obtain rfl : x = x' ≫ h e := (cancel_mono (fstG I e G).left).1 (hx.trans (by rw [Category.assoc, hh e]))
  refine ⟨(congrArg (x' ≫ ·) (hg e).1).trans (Category.assoc _ _ _).symm,
    fun z J J' hJ hJ' => ⟨fun χ => ?_, fun k k' hk hk' => ?_⟩⟩
  · refine (CubTransport.val_pmaps ((hg e).2 χ).1 ((hg e).2 χ).2 x' hJ hJ').trans
      ((mul_comm _ _).trans (congrArg _ (Finset.prod_congr rfl fun k _ => ?_)))
    rw [Category.assoc]
  · exact sq e Z x' z _ _ k k' (pt (hg e).1.symm x' z (hJ ((x' ≫ h e) ≫ (U.gt e).pG.left)))
      (hJ' (x' ≫ (g e).pG.left)) (pt (hh e) x' z hk) hk'

theorem exists_cmp_pull : Laws → ∀ (R V : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V] (I : Ideal R) (I' : Ideal V) (φ : R →+* V), I.map φ ≤ I' → ∀ (D : DegPre R) (D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (A' : PolAV (Sp (FractionRing V))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left) (pb : IsGrpPullback G' G (spMap φ) F) (wL : LB.Iso U'.P.L.L (U.P.L.L.pull F)), IsCPMap U'.P U.P (spMap φ) F pb.1.w wL → ∃ (D₁ : DegPre V) (U₁ : PreU I' D₁ A' G') (C : Cmp φ U U₁ F), U₁.P = U'.P ∧ HEq C.wL wL := by
  intro hL R V _ _ _ _ _ I I' φ hI D D' A A' G _ _ G' _ _ U U' F pb wL hw
  obtain ⟨ψ, h, hW⟩ := GlobalTheory.T.exists_psi_generating_on_whole_spectrum R D
  obtain ⟨D₁, hD, -⟩ := DegPull.exists_isPullDeg hL.polBaseChange R V φ (setPsi D ψ h) ⊤ hW trivial
  obtain ⟨U₁, C, h₁, h₂⟩ := exists_cmp_of_isPullDeg hL.globalFns hI hD (U.setPsi ψ h) U' F pb wL hw
  exact ⟨D₁, U₁, ⟨C.pb, C.wL, C.wL_map, C.β, C.pbB, C.v, C.v_gen, C.xe, C.c_pr, C.lev, C.map_le⟩, h₁, h₂⟩

end GlobalTheory.LN.PreBaseChange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsComparisonCompAlongIdentity
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsComparisonCompAlongIdentity
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.LN.Cmp

theorem Oφ_baseChange {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {φ : R →+* V} {D : DegPre R}
    {D' : DegPre V} {β : D'.P.A.left ⟶ D.P.A.left} (pb : IsGrpPullback D'.P.A D.P.A (spMap φ) β) {x' : D'.X} {x : D.X}
    (hc : (D'.c x').left ≫ β = spMap φ ≫ (D.c x).left)
    {T : Over (Spec (CommRingCat.of R))} {T' : Over (Spec (CommRingCat.of V))}
    (p : T ⟶ D.P.A) (p' : T' ⟶ D'.P.A) (h : T'.left ⟶ T.left) (hp : p'.left ≫ β = h ≫ p.left) (κ : Fin 4) :
    D'.Oφ p' x' κ ≫ β = h ≫ D.Oφ p x κ := by
  have hb : h ≫ T.hom = T'.hom ≫ spMap φ := by
    rw [← Over.w p, ← Category.assoc, ← hp, Category.assoc, pb.1.w, ← Category.assoc, Over.w]
  let U : Over.mk (T'.hom ≫ spMap φ) ⟶ T := Over.homMk h hb
  have e : pushPt pb.1.w p' = U ≫ p := Over.OverMorphism.ext hp
  have c : pushPt pb.1.w (toUnit T' ≫ D'.c x') = toUnit _ ≫ D.c x := Over.OverMorphism.ext (by
    show (T'.hom ≫ (D'.c x').left) ≫ β = (T'.hom ≫ spMap φ) ≫ (D.c x).left
    rw [Category.assoc, hc, ← Category.assoc])
  refine Eq.trans ?_ (WeightPf.Oφ_comp U p x κ).symm
  rw [← e]
  fin_cases κ
  · exact congrArg (fun q => q.left) ((map_mul (pushHom pb T') p' (toUnit T' ≫ D'.c x')).trans
      (congrArg (pushPt pb.1.w p' * ·) c))
  · exact congrArg (fun q => q.left) c
  · rfl
  · exact congrArg (fun q => q.left) (map_one (pushHom pb T'))

theorem exists_comp_id : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (I : Ideal R) (I' : Ideal V) (φ : R →+* V) (D : DegPre R) (D₁ D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (A₁ A' : PolAV (Sp (FractionRing V))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (U₁ : PreU I' D₁ A₁ G') (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left) (C₁ : Cmp φ U U₁ F) (C₂ : Cmp (RingHom.id V) U₁ U' (𝟙 G'.left)) (wL : LB.Iso U'.P.L.L (U.P.L.L.pull F)), IsCPMap U'.P U.P (spMap φ) F C₁.pb.1.w wL → (∀ (Z : Scheme.{0}) (r : Z ⟶ G'.left) (z : Z) (j : U.P.L.L.ι) (i : U₁.P.L.L.ι) (k : U'.P.L.L.ι), F (r z) ∈ U.P.L.L.U j → r z ∈ U₁.P.L.L.U i → r z ∈ U'.P.L.L.U k → gw wL r z j k = gw C₁.wL r z j i * gw C₂.wL r z i k) → ∃ C : Cmp φ U U' F, C.wL = wL := by
  intro R V _ _ _ _ I I' φ D D₁ D' A A₁ A' G _ _ G' _ _ U U₁ U' F C₁ C₂ wL hmap hw
  have g₁ := (isGen_iff _).1 C₁.v_gen
  have g₂ := (isGen_iff _).1 C₂.v_gen
  obtain ⟨v, T⟩ := exists_comp D₁.P.isLB C₁.v C₂.v g₁ g₂ D.P.isLB D'.P.isLB
  have pbB : IsGrpPullback D'.P.A D.P.A (spMap φ) (C₂.β ≫ C₁.β) := by
    have h := C₂.pbB.comp C₁.pbB
    rwa [spMap_ringHom_id, Category.id_comp] at h
  refine ⟨{
    pb := C₁.pb
    wL := wL
    wL_map := hmap
    β := C₂.β ≫ C₁.β
    pbB := pbB
    v := v
    v_gen := (isGen_iff _).2 (T.pgen_comp D₁.P.isLB g₁ g₂)
    xe := C₂.xe.trans C₁.xe
    c_pr := fun x => by
      rw [← Category.assoc, C₂.c_pr, spMap_ringHom_id, Category.id_comp, C₁.c_pr]
      rfl
    lev := fun e Z x' x hx => ?_
    map_le := C₁.map_le }, rfl⟩
  obtain ⟨a₁, b₁⟩ := C₁.lev e Z x' x hx
  obtain ⟨a₂, b₂⟩ := C₂.lev e Z x' x' (by rw [Category.comp_id])
  refine ⟨by rw [← a₁, reassoc_of% a₂], fun z J J' hJ hJ' => ?_⟩
  obtain ⟨J₁, hJ₁⟩ := exists_good_pt D₁.P.isLB z
  obtain ⟨c₁, d₁⟩ := b₁ z J J₁ hJ hJ₁
  obtain ⟨c₂, d₂⟩ := b₂ z J₁ J' hJ₁ hJ'
  have tri : ∀ f : Z ⟶ D'.P.A.left, gw v f z (J (f ≫ C₂.β ≫ C₁.β)) (J' f) =
      gw C₁.v (f ≫ C₂.β) z (J (f ≫ C₂.β ≫ C₁.β)) (J₁ (f ≫ C₂.β)) * gw C₂.v f z (J₁ (f ≫ C₂.β)) (J' f) :=
    fun f => T Z f z _ _ _ (hJ (f ≫ C₂.β ≫ C₁.β)) (hJ₁ (f ≫ C₂.β)) (hJ' f)
  refine ⟨fun χ => ?_, fun k k' hk hk' => ?_⟩
  · have hp : (U'.gt e).pG.left ≫ C₂.β = 𝟙 _ ≫ (U₁.gt e).pG.left := by
      have := (C₂.lev e _ (𝟙 _) (𝟙 _) (by rw [Category.comp_id])).1
      rwa [Category.id_comp] at this
    have o : ∀ κ, D'.Oφ (U'.gt e).pG χ κ ≫ C₂.β = D₁.Oφ (U₁.gt e).pG (C₂.xe χ) κ := fun κ =>
      (Oφ_baseChange C₂.pbB (C₂.c_pr χ) _ _ _ hp κ).trans (Category.id_comp _)
    refine (c₁ (C₂.xe χ)).trans ?_
    rw [c₂ χ, _root_.mul_assoc, ← Finset.prod_mul_distrib]
    refine congrArg _ (Finset.prod_congr rfl fun κ _ => ?_)
    have t := tri (x' ≫ D'.Oφ (U'.gt e).pG χ κ)
    simp only [Category.assoc] at t
    rw [t, mul_zpow, mul_comm, ← o κ]
    simp only [Category.assoc]
  · obtain ⟨i, hi⟩ := exists_chart U₁.P.L.isLB ((fstG I' e G').left (x' z))
    have t := tri (x' ≫ (U'.gt e).pG.left)
    simp only [Category.assoc] at t
    have a : x' ≫ (U'.gt e).pG.left ≫ C₂.β ≫ C₁.β = x ≫ (U.gt e).pG.left := by rw [← a₁, reassoc_of% a₂]
    rw [a, a₂] at t
    have hk₂ : F ((x' ≫ (fstG I' e G').left) z) ∈ U.P.L.L.U k := by
      have : F ((x' ≫ (fstG I' e G').left) z) = (fstG I e G).left (x z) :=
        (congrArg (fun q : Z ⟶ G.left => q z) hx).symm
      rw [this]; exact hk
    rw [t, hw Z (x' ≫ (fstG I' e G').left) z k i k' hk₂ hi hk', _root_.mul_assoc, d₂ i k' hi hk',
      ← _root_.mul_assoc, d₁ k i hk hi, _root_.mul_assoc]

end GlobalTheory.LN.Cmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsComparisonCompAlongIdentityStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_comparison_comp_along_identity : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (I : Ideal R) (I' : Ideal V) (φ : R →+* V) (D : DegPre R) (D₁ D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (A₁ A' : PolAV (Sp (FractionRing V))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (U₁ : PreU I' D₁ A₁ G') (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left) (C₁ : Cmp φ U U₁ F) (C₂ : Cmp (RingHom.id V) U₁ U' (𝟙 G'.left)) (wL : LB.Iso U'.P.L.L (U.P.L.L.pull F)), IsCPMap U'.P U.P (spMap φ) F C₁.pb.1.w wL → (∀ (Z : Scheme.{0}) (r : Z ⟶ G'.left) (z : Z) (j : U.P.L.L.ι) (i : U₁.P.L.L.ι) (k : U'.P.L.L.ι), F (r z) ∈ U.P.L.L.U j → r z ∈ U₁.P.L.L.U i → r z ∈ U'.P.L.L.U k → gw wL r z j k = gw C₁.wL r z j i * gw C₂.wL r z i k) → ∃ C : Cmp φ U U' F, C.wL = wL := by
  first | exact @GlobalTheory.LN.Cmp.exists_comp_id | exact GlobalTheory.LN.Cmp.exists_comp_id | (intros; apply GlobalTheory.LN.Cmp.exists_comp_id <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompareUniformisationDataPullback
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

namespace GlobalTheory.LN.PreCompare

theorem exists_cmp : Laws → Laws2 → Ega → ∀ (R V : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V] [IsLocalRing V] (I : Ideal R) (I' : Ideal V), AdmBase R I → AdmBase V I' → I' ≠ ⊤ → ∀ φ : R →+* V, I.map φ ≤ I' → ∀ (D : DegPre R) (D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (A' : PolAV (Sp (FractionRing V))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left) (pb : IsGrpPullback G' G (spMap φ) F) (wL : LB.Iso U'.P.L.L (U.P.L.L.pull F)), IsCPMap U'.P U.P (spMap φ) F pb.1.w wL → ∃ C : Cmp φ U U' F, C.wL = wL := by
  intro hL _ _ R V _ _ _ _ _ _ I I' _ hV _ φ hI D D' A A' G _ _ G' _ _ U U' F pb wL hw
  obtain ⟨D₁, U₁, C₁, hP, hC⟩ := PreBaseChange.exists_cmp_pull hL R V I I' φ hI D D' A A' G G' U U' F pb wL hw
  obtain ⟨semi, gen, gen_hom, P, wA, wA_gen, gt, gt_q, gt_t, w, w_gen, w_vals, w_compat⟩ := U'
  obtain rfl : U₁.P = P := hP
  obtain rfl : C₁.wL = wL := eq_of_heq hC
  obtain ⟨C₂, h₂⟩ := PreUnique.exists_cmp_id hL V I' hV D₁ D' A' A' G' U₁
    ⟨semi, gen, gen_hom, U₁.P, wA, wA_gen, gt, gt_q, gt_t, w, w_gen, w_vals, w_compat⟩ (idIso U₁.P.L.L) (by simp)
    (IsCPMap.id U₁.P)
  refine GlobalTheory.T.exists_comparison_comp_along_identity R V I I' φ D D₁ D' A A' A' G G' U U₁ _ F C₁ C₂ C₁.wL hw fun Z r z j i k hj hi hk => ?_
  rw [h₂]
  have a := (isGen_iff _).1 C₁.wL_map.gen Z r z j j i k hj hj hi hk
  rw [gm_self U.P.L.isLB (r ≫ F) z hj, _root_.one_mul] at a
  exact ((congrArg₂ (· * ·) a (gw_idIso U₁.P.L.L r z hi hk)).trans (by rw [mul_comm, mul_inv_cancel_left])).symm

end GlobalTheory.LN.PreCompare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompareUniformisationDataPullbackStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compare_uniformisationData_pullback : Laws → Laws2 → Ega → ∀ (R V : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V] [IsLocalRing V] (I : Ideal R) (I' : Ideal V), AdmBase R I → AdmBase V I' → I' ≠ ⊤ → ∀ φ : R →+* V, I.map φ ≤ I' → ∀ (D : DegPre R) (D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (A' : PolAV (Sp (FractionRing V))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left) (pb : IsGrpPullback G' G (spMap φ) F) (wL : LB.Iso U'.P.L.L (U.P.L.L.pull F)), IsCPMap U'.P U.P (spMap φ) F pb.1.w wL → ∃ C : Cmp φ U U' F, C.wL = wL := by
  first | exact @GlobalTheory.LN.PreCompare.exists_cmp | exact GlobalTheory.LN.PreCompare.exists_cmp | (intros; apply GlobalTheory.LN.PreCompare.exists_cmp <;> assumption)
end
