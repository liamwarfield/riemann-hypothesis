module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LieFreeNearTwoPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicRapidDecayOfMemAdelicSchwartzSpace
public import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwo
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackProdInjectiveBirigidifiedGaloisIsogeny
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsTwistCharacterUnitsModSpecialIdeal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentCoordsBaseChangeSmoothCommGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentCoordsBaseChangeSmoothCommGroup
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieCoordR

open ReciprocityTheory.ChartRestriction.G.Chart (sp fB sp_hom_fB)

section Iso

variable {W : Type} [CommRing W] {R' : Type} [CommRing R'] [Algebra W R']

theorem epsHom_w : 𝟙 (Spec (CommRingCat.of (DualNumber R'))) ≫ (sp (R₀ := W) (DualNumber R')).hom =
    (epsPtR (spMap (algebraMap W R'))).hom := by
  rw [Category.id_comp]
  exact (sp_hom_fB (R := W) (R' := R') (P := DualNumber R')).symm

theorem epsInv_w : 𝟙 (Spec (CommRingCat.of (DualNumber R'))) ≫ (epsPtR (spMap (algebraMap W R'))).hom =
    (sp (R₀ := W) (DualNumber R')).hom := by
  rw [Category.id_comp]
  exact sp_hom_fB (R := W) (R' := R') (P := DualNumber R')

def epsHom : epsPtR (spMap (algebraMap W R')) ⟶ sp (R₀ := W) (DualNumber R') :=
  Over.homMk (𝟙 (Spec (CommRingCat.of (DualNumber R')))) epsHom_w

def epsInv : sp (R₀ := W) (DualNumber R') ⟶ epsPtR (spMap (algebraMap W R')) :=
  Over.homMk (𝟙 (Spec (CommRingCat.of (DualNumber R')))) epsInv_w

end Iso

section Main
open GlobalTheory.SqZero
variable {W : Type} [CommRing W] {G : Over (Sp W)} [GrpObj G] [IsCommMonObj G]
  {n : ℕ} {v : Fin n → (epsR W ⟶ G)} {R' : Type} [CommRing R'] [Algebra W R']

theorem epsHom_epsInv : epsHom (W := W) (R' := R') ≫ epsInv = 𝟙 _ :=
  Over.OverMorphism.ext (Category.id_comp (𝟙 (Spec (CommRingCat.of (DualNumber R')))))

theorem epsInv_epsHom : epsInv (W := W) (R' := R') ≫ epsHom = 𝟙 _ :=
  Over.OverMorphism.ext (Category.id_comp (𝟙 (Spec (CommRingCat.of (DualNumber R')))))

theorem fst_left : (ReciprocityTheory.ChartRestriction.G.Chart.spMap (fstS W R')).left =
    spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom := rfl

theorem isTanOver_epsInv (w : epsPtR (spMap (algebraMap W R')) ⟶ G)
    (hw : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ w.left =
        (1 : Over.mk (spMap (algebraMap W R')) ⟶ G).left) : IsTanOver (epsInv ≫ w) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left, fst_left]
  exact (congrArg (spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ ·)
    (Category.id_comp (X := Spec (CommRingCat.of (DualNumber R'))) w.left)).trans hw


variable (v) in
def coordPt (c : Fin n → R') : epsPtR (spMap (algebraMap W R')) ⟶ G :=
  epsHom ≫ tanExp v c

theorem coordPt_injective [Smooth G.hom] (hv : IsLieBasis v) :
    Function.Injective (coordPt (R' := R') v) := by
  intro c c' h
  have h' := congrArg (epsInv ≫ ·) h
  simp only [coordPt] at h'
  rw [← Category.assoc, ← Category.assoc, epsInv_epsHom, Category.id_comp, Category.id_comp] at h'
  exact (LieTwo.isLieBasisOver_of_expBij (expBij (DualNumber R') hv)).1 c c' h'

theorem coordPt_range [Smooth G.hom] (hv : IsLieBasis v) (w : epsPtR (spMap (algebraMap W R')) ⟶ G) :
    spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ w.left =
        (1 : Over.mk (spMap (algebraMap W R')) ⟶ G).left ↔ w ∈ Set.range (coordPt v) := by
  constructor
  · intro hw
    obtain ⟨s, hs⟩ := (LieTwo.isLieBasisOver_of_expBij (expBij (DualNumber R') hv)).2 _
      (isTanOver_epsInv w hw)
    exact ⟨s, by rw [coordPt, ← hs, ← Category.assoc, epsHom_epsInv, Category.id_comp]⟩
  · rintro ⟨s, rfl⟩
    have := congrArg (fun f => Over.Hom.left f) (isTanOver_tanExp (S := R') hv.1 s)
    rw [Over.comp_left, fst_left] at this
    rw [coordPt, Over.comp_left]
    exact (congrArg (spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ ·)
      (Category.id_comp (X := Spec (CommRingCat.of (DualNumber R'))) (tanExp v s).left)).trans this

theorem coordPt_add (hv : IsLieBasis v) (c c' : Fin n → R') :
    coordPt v (c + c') = coordPt v c * coordPt v c' := by
  rw [coordPt, coordPt, coordPt, LieTwo.tanExp_add hv.1, MonObj.comp_mul]

theorem dualScale_eq (s : R') : (dualScale W s).toRingHom = ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR s :=
  RingHom.ext fun a => TrivSqZeroExt.ext (by simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR])
    (by simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR, mul_comm])

theorem coordPt_smul (s : R') (c : Fin n → R') :
    (coordPt v (s • c)).left = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR s) ≫ (coordPt v c).left := by
  have h1 : s • c = fun i => c i * s := funext fun i => by simp [mul_comm]
  rw [coordPt, coordPt, Over.comp_left, Over.comp_left, h1, ← scl_tanExp, scl, Over.comp_left,
    ReciprocityTheory.ChartRestriction.G.Chart.spMap_left, dualScale_eq]
  exact (Category.id_comp (X := Spec (CommRingCat.of (DualNumber R'))) _).trans
    (congrArg (spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR s) ≫ ·)
      (Category.id_comp (X := Spec (CommRingCat.of (DualNumber R'))) (tanExp v c).left)).symm


variable (v) in
def lieMat (hv : IsLieBasis v) (u : G ⟶ G) : Matrix (Fin n) (Fin n) W := by
  classical
  exact if h : ∀ i, IsTangent (v i ≫ u) then
    Matrix.transpose (Matrix.of fun i => (hv.2 _ (h i)).exists.choose) else 0

theorem isTangent_comp (hv : ∀ i, IsTangent (v i)) (u : G ⟶ G) [IsMonHom u] (i : Fin n) :
    IsTangent (v i ≫ u) := by
  unfold IsTangent at *
  rw [Over.comp_left, ← Category.assoc, hv i, ← Over.comp_left, IsMonHom.one_hom]

theorem comp_eq_tanExp (hv : IsLieBasis v) (u : G ⟶ G) [IsMonHom u] (i : Fin n) :
    v i ≫ u = tanExp v (fun j => lieMat v hv u j i) := by
  have h := isTangent_comp hv.1 u
  have hc := (hv.2 _ (h i)).exists.choose_spec
  rw [isLieComb_iff_lieExp] at hc
  rw [hc]
  simp only [lieMat, dif_pos h, Matrix.transpose_apply, Matrix.of_apply]

theorem coordPt_comp (hv : IsLieBasis v) (u : G ⟶ G) [IsMonHom u] (c : Fin n → R') :
    coordPt v c ≫ u = coordPt v (((lieMat v hv u).map (algebraMap W R')).mulVec c) := by
  have h1 : tanExp v c ≫ u = tanExp (fun i => v i ≫ u) c := by
    simp only [tanExp, lieExp]
    exact (map_prod (IsMonHom.monoidHom u (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := W) (DualNumber R'))) _ _).trans
      (Finset.prod_congr rfl fun i _ => by
        show (_ ≫ v i) ≫ u = _
        exact Category.assoc _ _ _)
  have hM : ∀ i, res (Algebra.ofId W R') (v i ≫ u) =
      tanExp v (Matrix.of (fun i j => algebraMap W R' (lieMat v hv u j i)) i) := by
    intro i
    rw [comp_eq_tanExp hv u i, res_tanExp]
    rfl
  have key : Matrix.vecMul c (Matrix.of (fun i j => algebraMap W R' (lieMat v hv u j i))) =
      ((lieMat v hv u).map (algebraMap W R')).mulVec c := by
    funext j
    simp [Matrix.vecMul, Matrix.mulVec, dotProduct, mul_comm]
  rw [coordPt, coordPt, Category.assoc, h1, LieTwo.tanExp_eq_vecMul hv.1 hM, key]

end Main

theorem exists_coords_baseChange : ∀ (W : Type) [CommRing W] [IsLocalRing W] (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∃ (n : ℕ) (M : (G ⟶ G) → Matrix (Fin n) (Fin n) W), ∀ (R' : Type) [CommRing R'] (β : W →+* R'), ∃ T : (Fin n → R') → (epsPtR (spMap β) ⟶ G), Function.Injective T ∧ (∀ v : epsPtR (spMap β) ⟶ G, spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ v.left = (1 : Over.mk (spMap β) ⟶ G).left ↔ v ∈ Set.range T) ∧ (∀ c c', T (c + c') = T c * T c') ∧ (∀ (s : R') c, (T (s • c)).left = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR s) ≫ (T c).left) ∧ ∀ u : G ⟶ G, IsMonHom u → ∀ c, T c ≫ u = T (((M u).map β).mulVec c) := by
  intro W _ _ G _ _ hsm
  haveI := hsm
  obtain ⟨n, v, hv⟩ := ReciprocityTheory.ChartRestriction.G.Chart.exists_isLieBasis G hsm
  refine ⟨n, lieMat v hv, fun R' _ β => ?_⟩
  letI := β.toAlgebra
  exact ⟨coordPt v, coordPt_injective hv, coordPt_range hv, coordPt_add hv, coordPt_smul,
    fun u hu c => by haveI := hu; exact coordPt_comp hv u c⟩

end GlobalTheory.LieCoordR
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentCoordsBaseChangeSmoothCommGroupStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tangent_coords_base_change_smooth_comm_group : ∀ (W : Type) [CommRing W] [IsLocalRing W] (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∃ (n : ℕ) (M : (G ⟶ G) → Matrix (Fin n) (Fin n) W), ∀ (R' : Type) [CommRing R'] (β : W →+* R'), ∃ T : (Fin n → R') → (epsPtR (spMap β) ⟶ G), Function.Injective T ∧ (∀ v : epsPtR (spMap β) ⟶ G, spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ v.left = (1 : Over.mk (spMap β) ⟶ G).left ↔ v ∈ Set.range T) ∧ (∀ c c', T (c + c') = T c * T c') ∧ (∀ (s : R') c, (T (s • c)).left = spMap (epsScaleR s) ≫ (T c).left) ∧ ∀ u : G ⟶ G, IsMonHom u → ∀ c, T c ≫ u = T (((M u).map β).mulVec c) := by
  first | (exact @GlobalTheory.LieCoordR.exists_coords_baseChange) | (exact GlobalTheory.LieCoordR.exists_coords_baseChange) | (intros; apply GlobalTheory.LieCoordR.exists_coords_baseChange  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedLatticeStabilizerIffBasisIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedLatticeStabilizerIffBasisIntegral
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.GeoActCompare
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LatStab

section Core

variable {B : Type} [CommRing B] {n : ℕ}

theorem mulVec_mem_iff (S : Subring B) (y : Matrix (Fin n) (Fin n) B) :
    (∀ v : Fin n → B, (∀ i, v i ∈ S) → ∀ i, y.mulVec v i ∈ S) ↔ ∀ i j, y i j ∈ S := by
  constructor
  · intro h i j
    have := h (Pi.single j 1) (fun k => by
      rcases eq_or_ne k j with rfl | hk
      · simp
      · simp [hk]) i
    simpa using this
  · intro h v hv i
    show ∑ j, y i j * v j ∈ S
    exact S.sum_mem fun j _ => S.mul_mem (h i j) (hv j)

theorem exists_int_iff (S : Subring B) (y : GL (Fin n) B) :
    (∃ u : GL (Fin n) S, u.val.map S.subtype = y.val) ↔
      (∀ i j, y.val i j ∈ S) ∧ ∀ i j, (y⁻¹).val i j ∈ S := by
  constructor
  · rintro ⟨u, hu⟩
    have h1 : Units.map (S.subtype.mapMatrix (m := Fin n)).toMonoidHom u = y := Units.ext hu
    subst h1
    refine ⟨fun i j => (u.val i j).2, fun i j => ?_⟩
    rw [← map_inv]
    exact ((u⁻¹).val i j).2
  · rintro ⟨h1, h2⟩
    have inj : Function.Injective (S.subtype.mapMatrix (m := Fin n)) :=
      Matrix.map_injective S.subtype_injective
    let a : Matrix (Fin n) (Fin n) S := Matrix.of fun i j => ⟨_, h1 i j⟩
    let b : Matrix (Fin n) (Fin n) S := Matrix.of fun i j => ⟨_, h2 i j⟩
    have ha : S.subtype.mapMatrix a = y.val := rfl
    have hb : S.subtype.mapMatrix b = (y⁻¹).val := rfl
    refine ⟨⟨a, b, inj ?_, inj ?_⟩, rfl⟩
    · rw [map_mul, ha, hb, map_one, Units.mul_inv]
    · rw [map_mul, ha, hb, map_one, Units.inv_mul]

theorem image_eq_iff {A : Type} [CommRing A] (e : A →+* B) (he : Function.Bijective e) (S : Subring B)
    (β x : GL (Fin n) B) (k : GL (Fin n) A) (hx : x.val = k.val.map e) (L : Set (Fin n → A))
    (hL : ∀ z, z ∈ L ↔ ∀ i, (β⁻¹).val.mulVec (fun a => e (z a)) i ∈ S) :
    k.val.mulVec '' L = L ↔ ∃ u : GL (Fin n) S, u.val.map S.subtype = (β⁻¹ * x * β).val := by
  have key : ∀ (x : GL (Fin n) B) (k : GL (Fin n) A), x.val = k.val.map e →
      ((∀ z ∈ L, k.val.mulVec z ∈ L) ↔ ∀ i j, (β⁻¹ * x * β).val i j ∈ S) := by
    intro x k hx
    have hm : ∀ z : Fin n → A, (β⁻¹).val.mulVec (fun a => e (k.val.mulVec z a)) =
        (β⁻¹ * x * β).val.mulVec ((β⁻¹).val.mulVec (fun a => e (z a))) := by
      intro z
      have : (fun a => e (k.val.mulVec z a)) = x.val.mulVec (fun a => e (z a)) := by
        funext a
        rw [hx, RingHom.map_mulVec]; rfl
      rw [this, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul,
        mul_inv_cancel_right]
    rw [← mulVec_mem_iff]
    constructor
    · intro h v hv
      choose z hz using fun a => he.2 (β.val.mulVec v a)
      have hz' : (β⁻¹).val.mulVec (fun a => e (z a)) = v := by
        rw [show (fun a => e (z a)) = β.val.mulVec v from funext hz, Matrix.mulVec_mulVec, Units.inv_mul,
          Matrix.one_mulVec]
      have := (hL _).1 (h z ((hL z).2 (by rw [hz']; exact hv)))
      rwa [hm, hz'] at this
    · intro h z hz
      rw [hL, hm]
      exact h _ ((hL z).1 hz)
  have hx' : (x⁻¹).val = (k⁻¹).val.map e := by
    have h1 : Units.map (e.mapMatrix (m := Fin n)).toMonoidHom k = x := Units.ext hx.symm
    rw [← h1, ← map_inv]; rfl
  have hi : (β⁻¹ * x * β)⁻¹ = β⁻¹ * x⁻¹ * β := by group
  rw [exists_int_iff, hi, ← key x k hx, ← key x⁻¹ k⁻¹ hx']
  constructor
  · intro h
    refine ⟨fun z hz => h ▸ ⟨z, hz, rfl⟩, fun z hz => ?_⟩
    rw [← h] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  · rintro ⟨h1, h2⟩
    apply Set.Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact h1 z hz
    · intro z hz
      exact ⟨_, h2 z hz, by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]⟩

end Core

theorem mem_St_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    x ∈ Formalism.L2.DIV.St β ↔ ∃ u : GL (Fin n) (Formalism.L2.Herm.intAf F E),
      u.val.map (Formalism.L2.Herm.intAf F E).subtype = (β⁻¹ * x * β).val := by
  refine exists_congr fun u => ?_
  show β * Formalism.L2.DIV.intGL F E n u * β⁻¹ = x ↔ (Formalism.L2.DIV.intGL F E n u).val = _
  rw [← Units.ext_iff]
  constructor
  · rintro rfl; group
  · intro h; rw [h]; group

theorem gLat_eq_latHat_iff : ∀ (D : D7) (V : HSp D) (r : ℕ) (hr : V.rank = r) (β : GL (Fin r) (EAf D)), LatticeBasisLifts.IsLatBasis V hr β → ∀ κ : GA D V, gLat V κ = (latHat V : Set (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)) ↔ LatticeBasisLifts.finR V hr κ ∈ Formalism.L2.DIV.St β := by
  intro D V r hr β hβ κ
  subst hr
  rw [mem_St_iff]
  exact image_eq_iff (swapAE D) (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).bijective
    (LatticeBasisLifts.OAf D) β _ (finHom V κ) rfl _ hβ

end GlobalTheory.LatStab
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedLatticeStabilizerIffBasisIntegralStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.GeoActCompare
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completedLattice_stabilizer_iff_basis_integral : ∀ (D : D7) (V : HSp D) (r : ℕ) (hr : V.rank = r) (β : GL (Fin r) (EAf D)), LatticeBasisLifts.IsLatBasis V hr β → ∀ κ : GA D V, gLat V κ = (latHat V : Set (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)) ↔ LatticeBasisLifts.finR V hr κ ∈ Formalism.L2.DIV.St β := by
  first | exact @GlobalTheory.LatStab.gLat_eq_latHat_iff | exact GlobalTheory.LatStab.gLat_eq_latHat_iff | (intros; apply GlobalTheory.LatStab.gLat_eq_latHat_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationAtCorrespondOfCartesian
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationAtCorrespondOfCartesian
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

noncomputable section

namespace GlobalTheory.UnifPull

variable {X X' : Scheme.{0}} {G : Over X} {G' : Over X'} [GrpObj G] [GrpObj G'] {f : X' ⟶ X}
  {φ : G'.left ⟶ G.left}

def push (hw : φ ≫ G.hom = G'.hom ≫ f) {T : Scheme.{0}} {t' : T ⟶ X'} {t : T ⟶ X} (ht : t' ≫ f = t)
    (x : Over.mk t' ⟶ G') : Over.mk t ⟶ G :=
  Over.homMk (x.left ≫ φ) (by
    show (x.left ≫ φ) ≫ G.hom = t
    rw [Category.assoc, hw, ← Category.assoc, Over.w x, ← ht]
    rfl)

theorem push_left (hw : φ ≫ G.hom = G'.hom ≫ f) {T : Scheme.{0}} {t' : T ⟶ X'} {t : T ⟶ X} (ht : t' ≫ f = t)
    (x : Over.mk t' ⟶ G') : (push hw ht x).left = x.left ≫ φ := rfl

def pull (H : IsPullback φ G'.hom G.hom f) {T : Scheme.{0}} {t' : T ⟶ X'} {t : T ⟶ X} (ht : t' ≫ f = t)
    (x : Over.mk t ⟶ G) : Over.mk t' ⟶ G' :=
  Over.homMk (H.lift x.left t' ((Over.w x).trans ht.symm)) (H.lift_snd _ _ _)

theorem push_pull (H : IsPullback φ G'.hom G.hom f) {T : Scheme.{0}} {t' : T ⟶ X'} {t : T ⟶ X} (ht : t' ≫ f = t)
    (x : Over.mk t ⟶ G) : push H.w ht (pull H ht x) = x :=
  Over.OverMorphism.ext (H.lift_fst _ _ _)

theorem push_injective (H : IsPullback φ G'.hom G.hom f) {T : Scheme.{0}} {t' : T ⟶ X'} {t : T ⟶ X}
    (ht : t' ≫ f = t) : Function.Injective (push H.w ht) := fun x y h =>
  Over.OverMorphism.ext (H.hom_ext (congrArg (fun u => u.left) h) (by rw [Over.w x, Over.w y]))

theorem push_surjective (H : IsPullback φ G'.hom G.hom f) {T : Scheme.{0}} {t' : T ⟶ X'} {t : T ⟶ X}
    (ht : t' ≫ f = t) : Function.Surjective (push H.w ht) := fun x => ⟨_, push_pull H ht x⟩

theorem push_mul (hφ : IsGrpPullback G' G f φ) {T : Scheme.{0}} (t' : T ⟶ X') (x y : Over.mk t' ⟶ G') :
    push hφ.1.w (t := t' ≫ f) rfl (x * y) = push hφ.1.w rfl x * push hφ.1.w rfl y :=
  Over.OverMorphism.ext (hφ.2 (Over.mk t') x y (push hφ.1.w rfl x) (push hφ.1.w rfl y) rfl rfl).symm

theorem push_one (hφ : IsGrpPullback G' G f φ) {T : Scheme.{0}} (t' : T ⟶ X') :
    push hφ.1.w (t := t' ≫ f) rfl (1 : Over.mk t' ⟶ G') = 1 := by
  have h := push_mul hφ t' 1 1
  rw [_root_.mul_one] at h
  exact mul_eq_left.1 h.symm

theorem push_comp (hw : φ ≫ G.hom = G'.hom ≫ f) {T : Scheme.{0}} {t' : T ⟶ X'} {t : T ⟶ X} (ht : t' ≫ f = t)
    {a' : G' ⟶ G'} {a : G ⟶ G} (ha : a'.left ≫ φ = φ ≫ a.left) (x : Over.mk t' ⟶ G') :
    push hw ht (x ≫ a') = push hw ht x ≫ a :=
  Over.OverMorphism.ext (by
    show (x ≫ a').left ≫ φ = (push hw ht x ≫ a).left
    rw [Over.comp_left, Over.comp_left, push_left, Category.assoc, ha, Category.assoc])

theorem isDerivAt0_iff_comp (H : IsPullback φ G'.hom G.hom f) {g : ℕ} {y' : Sp ℂ ⟶ X'}
    {e : (Fin g → ℂ) → (Sp ℂ ⟶ G'.left)} (he : ∀ z, e z ≫ G'.hom = y')
    (hol : IsHolTo Set.univ (fun z => e z ≫ φ)) (w : Fin g → ℂ) {v : Sp (DualNumber ℂ) ⟶ G'.left}
    (hv : v ≫ G'.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y') :
    IsDerivAt0 e w v ↔ IsDerivAt0 (fun z => e z ≫ φ) w (v ≫ φ) := by
  refine ⟨fun h => FibreDeriv.isDerivAt0_comp h φ, fun h => ?_⟩
  have H₁ := (IsPullback.of_hasPullback G'.hom y').paste_horiz H
  let e₁ : (Fin g → ℂ) → (Sp ℂ ⟶ pullback G'.hom y') :=
    fun z => pullback.lift (e z) (𝟙 _) (by rw [he, Category.id_comp])
  let v₁ : Sp (DualNumber ℂ) ⟶ pullback G'.hom y' := pullback.lift v (spMap (algebraMap ℂ (DualNumber ℂ))) hv
  have h1 : ∀ z, e₁ z ≫ pullback.fst _ _ = e z := fun z => pullback.lift_fst _ _ _
  have hv1 : v₁ ≫ pullback.fst _ _ = v := pullback.lift_fst _ _ _
  have hf1 : (fun z => e₁ z ≫ pullback.fst G'.hom y' ≫ φ) = fun z => e z ≫ φ :=
    funext fun z => by rw [← Category.assoc, h1]
  have key := FibreDeriv.isDerivAt0_of_isPullback H₁ (e := e₁) (fun z => pullback.lift_snd _ _ _)
    (by rw [hf1]; exact hol) (pullback.lift_snd _ _ _) (by rw [hf1, ← Category.assoc, hv1]; exact h)
  have := FibreDeriv.isDerivAt0_comp key (pullback.fst _ _)
  rw [hv1] at this
  simpa only [h1] using this

theorem spMap_fst_alg : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap (algebraMap ℂ (DualNumber ℂ)) = 𝟙 _ := by
  show Spec.map _ ≫ Spec.map _ = 𝟙 _
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1

theorem isExp_iff (hφ : IsGrpPullback G' G f φ) {g : ℕ} (y' : Sp ℂ ⟶ X') (e : (Fin g → ℂ) → (Over.mk y' ⟶ G')) :
    IsExp y' e ↔ IsExp (y' ≫ f) (fun z => push hφ.1.w rfl (e z)) := by
  have H := hφ.1
  have hpe : ∀ z, (push H.w (t := y' ≫ f) rfl (e z)).left = (e z).left ≫ φ := fun z => rfl
  have hes : ∀ z, (e z).left ≫ G'.hom = y' := fun z => Over.w (e z)
  have hol : IsHolTo Set.univ (fun z => (e z).left) ↔ IsHolTo Set.univ (fun z => (e z).left ≫ φ) :=
    ⟨fun h => HolFibre.isHolTo_comp h φ, fun h => HolFibre.isHolTo_of_isPullback H h
      (by simp only [hes]; exact HolFibre.isHolTo_const isOpen_univ y')⟩
  have ht : (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y') ≫ f = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ (y' ≫ f) :=
    Category.assoc _ _ _
  let pE : (epsPt y' ⟶ G') → (epsPt (y' ≫ f) ⟶ G) := push H.w ht
  have pEi : Function.Injective pE := push_injective H ht
  have pEs : Function.Surjective pE := push_surjective H ht
  have hd : IsHolTo Set.univ (fun z => (e z).left ≫ φ) → ∀ w (v : epsPt y' ⟶ G'),
      IsDerivAt0 (fun z => (e z).left) w v.left ↔ IsDerivAt0 (fun z => (push H.w (t := y' ≫ f) rfl (e z)).left) w (pE v).left :=
    fun h w v => isDerivAt0_iff_comp H hes h w (Over.w v)
  have hbase : ∀ v : epsPt y' ⟶ G', spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (pE v).left =
      (push H.w (t := y' ≫ f) rfl (e 0)).left ↔ spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left := by
    intro v
    refine ⟨fun h => H.hom_ext (by rw [Category.assoc]; exact h) ?_, fun h => ?_⟩
    · rw [Category.assoc, Over.w v, hes]
      show spMap _ ≫ spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y' = y'
      rw [← Category.assoc, spMap_fst_alg, Category.id_comp]
    · show spMap _ ≫ v.left ≫ φ = (e 0).left ≫ φ
      rw [← Category.assoc, h]
  have hinj : Function.Injective (push H.w (t := y' ≫ f) rfl (t' := y')) := push_injective H rfl
  constructor
  · rintro ⟨hadd, hsurj, hh, hd1, hd2⟩
    have hh' := hol.1 hh
    refine ⟨fun z w => by dsimp only; rw [hadd, push_mul hφ], (push_surjective H rfl).comp hsurj, hh', fun w => ?_,
      fun v hv => ?_⟩
    · obtain ⟨v, hv, hu⟩ := hd1 w
      refine ⟨pE v, (hd hh' w v).1 hv, fun v' hv' => ?_⟩
      obtain ⟨v', rfl⟩ := pEs v'
      rw [hu v' ((hd hh' w v').2 hv')]
    · obtain ⟨v, rfl⟩ := pEs v
      obtain ⟨w, hw, hu⟩ := hd2 v ((hbase v).1 hv)
      exact ⟨w, (hd hh' w v).1 hw, fun w' hw' => hu w' ((hd hh' w' v).2 hw')⟩
  · rintro ⟨hadd, hsurj, hh, hd1, hd2⟩
    have hh' : IsHolTo Set.univ (fun z => (e z).left ≫ φ) := hh
    refine ⟨fun z w => hinj (by have h := hadd z w; dsimp only at h; rw [h, push_mul hφ]), fun x => ?_, hol.2 hh', fun w => ?_, fun v hv => ?_⟩
    · obtain ⟨z, hz⟩ := hsurj (push H.w rfl x)
      exact ⟨z, hinj hz⟩
    · obtain ⟨v, hv, hu⟩ := hd1 w
      obtain ⟨v, rfl⟩ := pEs v
      exact ⟨v, (hd hh' w v).2 hv, fun v' hv' => pEi (hu _ ((hd hh' w v').1 hv'))⟩
    · obtain ⟨w, hw, hu⟩ := hd2 (pE v) ((hbase v).2 hv)
      exact ⟨w, (hd hh' w v).2 hw, fun w' hw' => hu w' ((hd hh' w' v).1 hw')⟩

end GlobalTheory.UnifPull

namespace GlobalTheory.UnifPull

variable {O : Type} [Ring O] {bar : O → O} {g : ℕ} {ρ : O →+* Matrix (Fin g) (Fin g) ℂ} {R R' : Type} [CommRing R]
  [CommRing R'] {σ : R →+* ℂ} {σ' : R' →+* ℂ} {Λ : Type} {F : Fam R O Λ g} {F' : Fam R' O Λ g} {N : ℕ}
  {f : F'.X ⟶ F.X} {φ : F'.A.left ⟶ F.A.left}

theorem unifAt_iff (hφ : IsGrpPullback F'.A F.A f φ) (hact : ∀ a, (F'.act a).left ≫ φ = φ ≫ (F.act a).left)
    (hL : LBIso F'.L (F.L.pull φ)) (heta : ∀ a, (F'.eta a).left ≫ φ = f ≫ (F.eta a).left) (D' : PLat O bar)
    (t : Λ → D'.La) (P : D'.La →+ (Fin g → ℂ)) (y' : Sp ℂ ⟶ F'.X) (hy' : y' ≫ F'.s = spMap σ')
    (hy : (y' ≫ f) ≫ F.s = spMap σ) (e' : (Fin g → ℂ) → (Over.mk y' ⟶ F'.A)) :
    UnifAt F' σ' ρ N D' t P y' e' ↔ UnifAt F σ ρ N D' t P (y' ≫ f) (fun z => push hφ.1.w rfl (e' z)) := by
  have hinj : Function.Injective (push hφ.1.w (t := y' ≫ f) rfl (t' := y')) := push_injective hφ.1 rfl
  have hker : ∀ z, push hφ.1.w (t := y' ≫ f) rfl (e' z) = 1 ↔ e' z = 1 := fun z => by
    rw [← push_one hφ y']
    exact hinj.eq_iff
  have hlin : ∀ a z, e' (ρ a *ᵥ z) = e' z ≫ F'.act a ↔
      push hφ.1.w (t := y' ≫ f) rfl (e' (ρ a *ᵥ z)) = push hφ.1.w rfl (e' z) ≫ F.act a := fun a z => by
    rw [← push_comp hφ.1.w rfl (hact a)]
    exact hinj.eq_iff.symm
  have hweil : ∀ (k : ℤ) (x x' : Over.mk y' ⟶ F'.A) (c : Γ(Sp ℂ, ⊤)ˣ), Out.WeilIs F'.A F'.L k x x' c ↔
      Out.WeilIs F.A F.L k (push hφ.1.w (t := y' ≫ f) rfl x) (push hφ.1.w rfl x') c := fun k x x' c =>
    GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ F.A F'.A f φ F.L F'.L F.isLB F'.isLB hφ hL (Over.mk y') k x x' _ _ c
      rfl rfl
  have hunit : ∀ a, push hφ.1.w (t := y' ≫ f) rfl (toUnit (Over.mk y') ≫ F'.eta a) =
      toUnit (Over.mk (y' ≫ f)) ≫ F.eta a := fun a => Over.OverMorphism.ext (by
    rw [push_left, Over.comp_left, Over.comp_left, Category.assoc, heta]
    simp)
  have heta' : ∀ a x, toUnit _ ≫ F'.eta a = x ↔ toUnit _ ≫ F.eta a = push hφ.1.w (t := y' ≫ f) rfl x :=
    fun a x => by
      rw [← hunit]
      exact hinj.eq_iff.symm
  constructor
  · rintro ⟨-, hP, hE, hK, hA, hW, hT⟩
    exact ⟨hy, hP, (isExp_iff hφ y' e').1 hE, fun z => (hker z).trans (hK z), fun a z => (hlin a z).1 (hA a z),
      fun k a b c hk hc => (hweil k _ _ _).1 (hW k a b c hk hc), fun a => (heta' a _).1 (hT a)⟩
  · rintro ⟨-, hP, hE, hK, hA, hW, hT⟩
    exact ⟨hy', hP, (isExp_iff hφ y' e').2 hE, fun z => (hker z).symm.trans (hK z), fun a z => (hlin a z).2 (hA a z),
      fun k a b c hk hc => (hweil k _ _ _).2 (hW k a b c hk hc), fun a => (heta' a _).2 (hT a)⟩

end GlobalTheory.UnifPull


open GlobalTheory.UnifPull in
theorem GlobalTheory.unifAt_correspond_of_cartesian : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* ℂ) (σ' : R' →+* ℂ) (Λ : Type) (F : Fam R O Λ g) (F' : Fam R' O Λ g) (N : ℕ) (f : F'.X ⟶ F.X) (φ : F'.A.left ⟶ F.A.left), IsGrpPullback F'.A F.A f φ → (∀ a, (F'.act a).left ≫ φ = φ ≫ (F.act a).left) → LBIso F'.L (F.L.pull φ) → (∀ a, (F'.eta a).left ≫ φ = f ≫ (F.eta a).left) → ∀ (D' : PLat O bar) (t : Λ → D'.La) P (y' : Sp ℂ ⟶ F'.X), y' ≫ F'.s = spMap σ' → (y' ≫ f) ≫ F.s = spMap σ → (∀ e', UnifAt F' σ' ρ N D' t P y' e' → ∃ e, UnifAt F σ ρ N D' t P (y' ≫ f) e ∧ ∀ z, (e z).left = (e' z).left ≫ φ) ∧ ∀ e, UnifAt F σ ρ N D' t P (y' ≫ f) e → ∃ e', UnifAt F' σ' ρ N D' t P y' e' ∧ ∀ z, (e z).left = (e' z).left ≫ φ := by
  intro O _ bar g ρ R R' _ _ σ σ' Λ F F' N f φ hφ hact hL heta D' t P y' hy' hy
  refine ⟨fun e' he' => ⟨_, (unifAt_iff hφ hact hL heta D' t P y' hy' hy e').1 he', fun z => rfl⟩,
    fun e he => ⟨fun z => pull hφ.1 rfl (e z), ?_, fun z => (hφ.1.lift_fst _ _ _).symm⟩⟩
  have h : (fun z => push hφ.1.w (t := y' ≫ f) rfl (pull hφ.1 rfl (e z))) = e := funext fun z => push_pull hφ.1 rfl (e z)
  exact (unifAt_iff hφ hact hL heta D' t P y' hy' hy _).2 (by rw [h]; exact he)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationAtCorrespondOfCartesianStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisationAt_correspond_of_cartesian : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* ℂ) (σ' : R' →+* ℂ) (Λ : Type) (F : Fam R O Λ g) (F' : Fam R' O Λ g) (N : ℕ) (f : F'.X ⟶ F.X) (φ : F'.A.left ⟶ F.A.left), IsGrpPullback F'.A F.A f φ → (∀ a, (F'.act a).left ≫ φ = φ ≫ (F.act a).left) → LBIso F'.L (F.L.pull φ) → (∀ a, (F'.eta a).left ≫ φ = f ≫ (F.eta a).left) → ∀ (D' : PLat O bar) (t : Λ → D'.La) P (y' : Sp ℂ ⟶ F'.X), y' ≫ F'.s = spMap σ' → (y' ≫ f) ≫ F.s = spMap σ → (∀ e', UnifAt F' σ' ρ N D' t P y' e' → ∃ e, UnifAt F σ ρ N D' t P (y' ≫ f) e ∧ ∀ z, (e z).left = (e' z).left ≫ φ) ∧ ∀ e, UnifAt F σ ρ N D' t P (y' ≫ f) e → ∃ e', UnifAt F' σ' ρ N D' t P y' e' ∧ ∀ z, (e z).left = (e' z).left ≫ φ := by
  first | exact @GlobalTheory.unifAt_correspond_of_cartesian | exact GlobalTheory.unifAt_correspond_of_cartesian | (intros; apply GlobalTheory.unifAt_correspond_of_cartesian <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResPullURes
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LBObs

private lemma res_res_eq_res_trans {X : Scheme.{0}} {U W Z : X.Opens} (h : W ≤ U) (h' : Z ≤ W) (x : Γ(X, U)ˣ) :
    res h' (res h x) = res (h'.trans h) x := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

private lemma pullU_res_eq_res_pullU {X Y : Scheme.{0}} (f : Y ⟶ X) {U W : X.Opens} (h : W ≤ U) (x : Γ(X, U)ˣ) :
    pullU f W (res h x) = res ((TopologicalSpace.Opens.map f.base).monotone h) (pullU f U x) := by
  ext
  simp only [pullU, res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply]
  rfl

private lemma res_pullU_res_eq_res_pullU' {X Y : Scheme.{0}} (f : Y ⟶ X) {U W : X.Opens} (h : W ≤ U) {Z : Y.Opens}
    (k : Z ≤ f ⁻¹ᵁ W) (x : Γ(X, U)ˣ) :
    res k (pullU f W (res h x)) = res (k.trans fun _ hy ↦ h hy) (pullU f U x) := by
  rw [pullU_res_eq_res_pullU, res_res_eq_res_trans]

theorem isFrame_pull (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens)
    (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) (L : LB X) (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ)
    (Z : Scheme.{0}) (φ : Z ⟶ X) (C' : Type) [Category.{0} C'] (V' : C' → Z.Opens)
    (hV' : ∀ ⦃T T' : C'⦄, (T ⟶ T') → V' T' ≤ V' T) (H : C' ⥤ C) (hH : ∀ T, V' T ≤ φ ⁻¹ᵁ V (H.obj T)) :
    IsFrame L V hV u → IsFrame (L.pull φ) V' hV' fun T T' a ↦ res (hH T') (pullU φ _ (u _ _ (H.map a))) := by
  rintro ⟨τ, hgen, hcomp⟩
  have hle : ∀ (T : C') (j : PUnit → L.ι), V' T ⊓ (L.pull φ).U j ≤ φ ⁻¹ᵁ (V (H.obj T) ⊓ L.U (j PUnit.unit)) :=
    fun T j x hx ↦ ⟨hH T hx.1, LB.wchart_le L (fun _ ↦ φ) j PUnit.unit hx.2⟩
  refine ⟨fun T j ↦ res (hle T j) (pullU φ _ (τ (H.obj T) (j PUnit.unit))), fun T j j' ↦ ?_, fun T T' a j ↦ ?_⟩
  · have e := congrArg (fun x ↦ res (fun y hy ↦ ⟨⟨hH T hy.1.1, LB.wchart_le L (fun _ ↦ φ) j PUnit.unit hy.1.2⟩,
        LB.wchart_le L (fun _ ↦ φ) j' PUnit.unit hy.2⟩ : V' T ⊓ (L.pull φ).U j ⊓ (L.pull φ).U j' ≤
          φ ⁻¹ᵁ (V (H.obj T) ⊓ L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit))) (pullU φ _ x))
      (hgen (H.obj T) (j PUnit.unit) (j' PUnit.unit))
    simp only [map_mul] at e
    erw [res_pullU_res_eq_res_pullU', res_pullU_res_eq_res_pullU', res_pullU_res_eq_res_pullU'] at e
    simp only [LB.pull, LB.LinComb, Fintype.prod_unique, zpow_one]
    erw [res_res_eq_res_trans, res_res_eq_res_trans, res_res_eq_res_trans]
    exact e
  · have e := congrArg (fun x ↦ res (hle T' j) (pullU φ _ x)) (hcomp (H.obj T) (H.obj T') (H.map a) (j PUnit.unit))
    simp only [map_mul, res_pullU_res_eq_res_pullU', res_res_eq_res_trans] at e
    simp only [res_res_eq_res_trans]
    exact e
end GlobalTheory.LBObs
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitCharacter
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitDetChar

open GlobalTheory.IdemModTwo GlobalTheory.SplitIdem

section Alg

variable {R : Type} [CommRing R]

def cut (a : R) (ha : a * a = a) : Rˣ →* Rˣ where
  toFun u := ⟨a * u + (1 - a), a * (u⁻¹ : Rˣ) + (1 - a),
    by linear_combination ((u : R) * (u⁻¹ : Rˣ) - u - (u⁻¹ : Rˣ) + 1) * ha + a * u.mul_inv,
    by linear_combination ((u : R) * (u⁻¹ : Rˣ) - u - (u⁻¹ : Rˣ) + 1) * ha + a * u.mul_inv⟩
  map_one' := Units.ext (by simp)
  map_mul' u w := Units.ext (by
    show a * ((u : R) * w) + (1 - a) = (a * u + (1 - a)) * (a * w + (1 - a))
    linear_combination (-((u : R) * w) + u + w - 1) * ha)

theorem cut_val (a : R) (ha : a * a = a) (u : Rˣ) : (cut a ha u : R) = a * u + (1 - a) := rfl

theorem continuous_cut [TopologicalSpace R] [IsTopologicalRing R] (a : R) (ha : a * a = a) :
    Continuous (cut a ha) :=
  Units.continuous_iff.2 ⟨(continuous_const.mul Units.continuous_val).add continuous_const,
    (continuous_const.mul Units.continuous_coe_inv).add continuous_const⟩

theorem mul_det {n : ℕ} (a : R) (M : Matrix (Fin n) (Fin n) R) (h : ∀ i j, a * (M - 1) i j = 0) :
    a * M.det = a := by
  let I : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R R a)
  have hI : ∀ x, x ∈ I ↔ x * a = 0 := fun x => Iff.rfl
  have h1 : (Ideal.Quotient.mk I).mapMatrix M = (Ideal.Quotient.mk I).mapMatrix 1 := by
    ext i j
    exact Ideal.Quotient.eq.2 ((hI _).2 ((mul_comm _ _).trans (h i j)))
  have h2 : Ideal.Quotient.mk I M.det = Ideal.Quotient.mk I 1 := by
    rw [RingHom.map_det, h1, map_one, det_one, map_one]
  have h3 := (hI _).1 (Ideal.Quotient.eq.1 h2)
  linear_combination h3

end Alg


theorem char_norm {D : D7} {χ : (Formalism.L2.Theta.AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D χ n)
    (x y : (Formalism.L2.Theta.AE D)ˣ) (hy : (y : Formalism.L2.Theta.AE D) = x * cA D x) : χ y = 1 := by
  obtain ⟨⟨η, hη⟩, h⟩ := h
  have := D.host.isCMField_hostE
  have e : y = idF D (Units.map (Algebra.norm (AF D.host.F) : Formalism.L2.Theta.AE D →* AF D.host.F) x) :=
    Units.ext (hy.trans (GlobalTheory.Published.algebraMap_norm_tensor (E := D.host.E) (AF D.host.F)
      (x : Formalism.L2.Theta.AE D)).symm)
  rw [e, h η hη, hη.2.2.1, one_pow]


end GlobalTheory.SplitDetChar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelicCharacterEqProdUnramifiedValueZpow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelicCharacterEqProdUnramifiedValueZpow
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CharUnramVal

theorem locK_eq_val_zpow {L : Type} [Field L] [NumberField L] (χ : HChar L) (Q : HeightOneSpectrum (𝓞 L))
    (hu : χ.UnrAt Q) (k : Lˣ) (m : ℤ) (hk : Q.valuation L (k : L) = WithZero.exp (-m)) :
    χ.locK Q k = χ.val Q ^ m := by
  have h1 : Valued.v ((atFin Q k : (Q.adicCompletion L)ˣ) : Q.adicCompletion L) = WithZero.exp (-m) :=
    (GlobalTheory.CharLocProd.val_algebraMap Q (k : L)).trans hk
  have h2 : Valued.v ((atFin Q (unif Q) : (Q.adicCompletion L)ˣ) : Q.adicCompletion L) = WithZero.exp (-1 : ℤ) :=
    unif_spec Q
  have h3 : IsUnitAt Q (atFin Q k * atFin Q (unif Q) ^ (-m)) := by
    show Valued.v _ = _
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, h1, h2, ← WithZero.exp_zsmul,
      ← WithZero.exp_add]
    simp
  have h4 := hu _ h3
  rw [map_mul, map_zpow, zpow_neg, mul_inv_eq_one] at h4
  exact h4

theorem char_eq_prod_val_zpow : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x) → (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) → (∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ e : AE D, IsPlIdem D e P ∧ infPart D e = 0 ∧ ι (finPart D e) P = 1 ∧ ∀ P' : HeightOneSpectrum (𝓞 D.host.E), P' ≠ P → ι (finPart D e) P' = 0) → ∀ (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E), ChrEq c χ → ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ∀ (S : Finset (HeightOneSpectrum (𝓞 D.host.E))) (m : HeightOneSpectrum (𝓞 D.host.E) → ℤ), (∀ Q ∈ S, χ.UnrAt Q ∧ Valued.v (ι (finPart D (x : AE D)) Q) = WithZero.exp (-m Q)) → (∀ Q, Q ∉ S → ι (finPart D (x : AE D)) Q = 1) → ((c x : Circle) : ℂ) = ((∏ Q ∈ S, χ.val Q ^ m Q : ℂˣ) : ℂ) := by
  classical
  intro D ι h1 h2 h3 c χ hc x hx S m hS hoff
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2 h3 c χ hc
  obtain ⟨S', k₀, -, hS'⟩ := GlobalTheory.finiteIdele_exists_local_approx D.host.E N hN
    (Units.map ((ι : _ →+* _).comp (finPart D)).toMonoidHom x)
  have hx0 : ∀ P : HeightOneSpectrum (𝓞 D.host.E), ι (finPart D (x : AE D)) P ≠ 0 := by
    intro P h
    by_cases hP : P ∈ S
    · have := (hS P hP).2
      rw [h, map_zero] at this
      exact WithZero.exp_ne_zero this.symm
    · exact zero_ne_one (h.symm.trans (hoff P hP))
  choose k hk using fun P => GlobalTheory.adicCompletion_exists_unit_approx D.host.E N hN P _ (hx0 P)
  have key := hprod x hx (S ∪ S') (fun P => if P ∈ S then k P else 1) (fun P _ => by
    by_cases hP : P ∈ S
    · simp only [if_pos hP]
      exact ⟨(hk P).1, (hk P).2.1⟩
    · simp only [if_neg hP, hoff P hP, Units.val_one, map_one, sub_self, map_zero, zero_le, and_self])
    (fun P hP => hS' P fun h => hP (Finset.mem_union_right _ h))
  rw [key, Units.coe_prod, ← Finset.prod_subset (Finset.subset_union_left (s₁ := S) (s₂ := S'))]
  · refine Finset.prod_congr rfl fun P hP => ?_
    simp only [if_pos hP]
    rw [locK_eq_val_zpow χ P (hS P hP).1 (k P) (m P) ((hk P).1.symm.trans (hS P hP).2)]
  · intro P _ hP
    simp only [if_neg hP, map_one, Units.val_one]

end GlobalTheory.CharUnramVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelicCharacterEqProdUnramifiedValueZpowStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idelicCharacter_eq_prod_unramifiedValue_zpow : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x) → (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) → (∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ e : AE D, IsPlIdem D e P ∧ infPart D e = 0 ∧ ι (finPart D e) P = 1 ∧ ∀ P' : HeightOneSpectrum (𝓞 D.host.E), P' ≠ P → ι (finPart D e) P' = 0) → ∀ (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E), ChrEq c χ → ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ∀ (S : Finset (HeightOneSpectrum (𝓞 D.host.E))) (m : HeightOneSpectrum (𝓞 D.host.E) → ℤ), (∀ Q ∈ S, χ.UnrAt Q ∧ Valued.v (ι (finPart D (x : AE D)) Q) = WithZero.exp (-m Q)) → (∀ Q, Q ∉ S → ι (finPart D (x : AE D)) Q = 1) → ((c x : Circle) : ℂ) = ((∏ Q ∈ S, χ.val Q ^ m Q : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.CharUnramVal.char_eq_prod_val_zpow | exact GlobalTheory.CharUnramVal.char_eq_prod_val_zpow | (intros; apply GlobalTheory.CharUnramVal.char_eq_prod_val_zpow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiInvolutionOfGaloisIsogenyDescent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiInvolutionOfGaloisIsogenyDescent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.UPel.HT.Hecke

theorem rosati_of_descent : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (M : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b M s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (act' : OActN D.O A') (ψ : o.A ⟶ A') (G : Subgroup (𝟙_ (Over S) ⟶ o.A)), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover G (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → (∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ act'.act c') → ∀ (m : ℕ) (P' : LB (G2 A').left), P'.IsLB → LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) → (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) → ∀ c' : D.O, LBIso (P'.pull (lift (fst A' A' ≫ act'.act c') (snd A' A')).left) (P'.pull (lift (fst A' A') (snd A' A' ≫ act'.act (D.star c').unop)).left) := by
  intro p _ D R _ b M S s o A' _ _ act' ψ G hA' hψ hG hact m P' hP' hIso r₁ r₂ c
  haveI := act'.hom c
  haveI := act'.hom (D.star c).unop
  have e₁ : sq2 ψ ≫ (lift (fst A' A' ≫ act'.act c) (snd A' A')).left =
      (lift (fst o.A o.A ≫ o.act.act c) (snd o.A o.A)).left ≫ sq2 ψ := by
    simp only [sq2, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp [hact]
  have e₂ : sq2 ψ ≫ (lift (fst A' A') (snd A' A' ≫ act'.act (D.star c).unop)).left =
      (lift (fst o.A o.A) (snd o.A o.A ≫ o.act.act (D.star c).unop)).left ≫ sq2 ψ := by
    simp only [sq2, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp [hact]
  have u₁ : (lift (1 : A' ⟶ A') (𝟙 A')).left ≫ (lift (fst A' A' ≫ act'.act c) (snd A' A')).left =
      𝟙 _ ≫ (lift (1 : A' ⟶ A') (𝟙 A')).left := by
    rw [← Over.comp_left, Category.id_comp]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have u₂ : (lift (𝟙 A') (1 : A' ⟶ A')).left ≫ (lift (fst A' A' ≫ act'.act c) (snd A' A')).left =
      (act'.act c).left ≫ (lift (𝟙 A') (1 : A' ⟶ A')).left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have v₁ : (lift (1 : A' ⟶ A') (𝟙 A')).left ≫ (lift (fst A' A') (snd A' A' ≫ act'.act (D.star c).unop)).left =
      (act'.act (D.star c).unop).left ≫ (lift (1 : A' ⟶ A') (𝟙 A')).left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have v₂ : (lift (𝟙 A') (1 : A' ⟶ A')).left ≫ (lift (fst A' A') (snd A' A' ≫ act'.act (D.star c).unop)).left =
      𝟙 _ ≫ (lift (𝟙 A') (1 : A' ⟶ A')).left := by
    rw [← Over.comp_left, Category.id_comp]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp

  have hL := o.isLB
  have hX₁ : ((P'.pull (lift (fst A' A' ≫ act'.act c) (snd A' A')).left).pull (sq2 ψ)).IsLB :=
    pull_isLB (pull_isLB hP' _) _
  have hX₂ : ((P'.pull (lift (fst A' A') (snd A' A' ≫ act'.act (D.star c).unop)).left).pull (sq2 ψ)).IsLB :=
    pull_isLB (pull_isLB hP' _) _
  have hL₁ : (lbPow (o.P.pull (lift (fst o.A o.A ≫ o.act.act c) (snd o.A o.A)).left) m).IsLB :=
    ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ (pull_isLB hL _) _ _
  have hL₂ : (lbPow (o.P.pull (lift (fst o.A o.A) (snd o.A o.A ≫ o.act.act (D.star c).unop)).left) m).IsLB :=
    ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ (pull_isLB hL _) _ _
  have I₁ : LBIso (lbPow (o.P.pull (lift (fst o.A o.A ≫ o.act.act c) (snd o.A o.A)).left) m)
      ((P'.pull (lift (fst A' A' ≫ act'.act c) (snd A' A')).left).pull (sq2 ψ)) :=
    LBIso.chartPull (chartPullLinComb o.P _ (K := Fin m) (fun _ => 𝟙 _) (fun _ => 𝟙 _) (fun _ => 1) _
        (fun _ => by rw [Category.id_comp, Category.comp_id]))
      (chartPullLinComb P' _ (K := PUnit) (fun _ => sq2 ψ) (fun _ => sq2 ψ) (fun _ => 1) _ (fun _ => e₁)) hIso
  have I₂ : LBIso (lbPow (o.P.pull (lift (fst o.A o.A) (snd o.A o.A ≫ o.act.act (D.star c).unop)).left) m)
      ((P'.pull (lift (fst A' A') (snd A' A' ≫ act'.act (D.star c).unop)).left).pull (sq2 ψ)) :=
    LBIso.chartPull (chartPullLinComb o.P _ (K := Fin m) (fun _ => 𝟙 _) (fun _ => 𝟙 _) (fun _ => 1) _
        (fun _ => by rw [Category.id_comp, Category.comp_id]))
      (chartPullLinComb P' _ (K := PUnit) (fun _ => sq2 ψ) (fun _ => sq2 ψ) (fun _ => 1) _ (fun _ => e₂)) hIso
  have Rm : LBIso (lbPow (o.P.pull (lift (fst o.A o.A ≫ o.act.act c) (snd o.A o.A)).left) m)
      (lbPow (o.P.pull (lift (fst o.A o.A) (snd o.A o.A ≫ o.act.act (D.star c).unop)).left) m) :=
    GlobalTheory.PowPrimitive.lbIso_linComb (o.rosati c) _ _
  have hsq := LBIso.trans hX₁ hL₁ hX₂ I₁.symm (LBIso.trans hL₁ hL₂ hX₂ Rm I₂)
  obtain ⟨t₁, ht₁⟩ := r₁
  obtain ⟨t₂, ht₂⟩ := r₂
  exact GlobalTheory.T.pullback_prod_injective_birigidified_galois_isogeny S o.A A' G ψ o.ab hA' hψ hG _ _ (pull_isLB hP' _) (pull_isLB hP' _)
    (gen_chartPull (chartPullLinComb P' _ (K := PUnit) (fun _ => _) (fun _ => _) (fun _ => 1) _ (fun _ => u₁)) t₁ ht₁)
    (gen_chartPull (chartPullLinComb P' _ (K := PUnit) (fun _ => _) (fun _ => _) (fun _ => 1) _ (fun _ => u₂)) t₂ ht₂)
    (gen_chartPull (chartPullLinComb P' _ (K := PUnit) (fun _ => _) (fun _ => _) (fun _ => 1) _ (fun _ => v₁)) t₁ ht₁)
    (gen_chartPull (chartPullLinComb P' _ (K := PUnit) (fun _ => _) (fun _ => _) (fun _ => 1) _ (fun _ => v₂)) t₂ ht₂)
    hsq

end GlobalTheory.UPel.HT.Hecke
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiInvolutionOfGaloisIsogenyDescentStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rosati_involution_of_galois_isogeny_descent : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (M : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b M s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (act' : OActN D.O A') (ψ : o.A ⟶ A') (G : Subgroup (𝟙_ (Over S) ⟶ o.A)), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover G (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → (∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ act'.act c') → ∀ (m : ℕ) (P' : LB (G2 A').left), P'.IsLB → LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) → (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) → ∀ c' : D.O, LBIso (P'.pull (lift (fst A' A' ≫ act'.act c') (snd A' A')).left) (P'.pull (lift (fst A' A') (snd A' A' ≫ act'.act (D.star c').unop)).left) := by
  first | exact @GlobalTheory.UPel.HT.Hecke.rosati_of_descent | exact GlobalTheory.UPel.HT.Hecke.rosati_of_descent | (intros; apply GlobalTheory.UPel.HT.Hecke.rosati_of_descent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackOfGroupSchemeModelBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackOfGroupSchemeModelBaseChange
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory.SS

theorem exists_isGrpPullback_of_isModel : ∀ (K W L : Type) [Field K] [CommRing W] [Field L] [Algebra K L] [Algebra W L] (A : Over (Sp K)) [GrpObj A] (G : Over (Sp W)) [GrpObj G], GlobalTheory.SS.IsModel (L := L) A G → ∀ (A' : Over (Sp L)) [GrpObj A'] (ψ : A'.left ⟶ A.left), IsGrpPullback A' A (spMap (algebraMap K L)) ψ → ∃ φ : A'.left ⟶ G.left, IsGrpPullback A' G (spMap (algebraMap W L)) φ := by
  intro K W L _ _ _ _ _ A _ G _ hM A' _ ψ hψ
  obtain ⟨e, he⟩ := hM
  obtain ⟨e₁, he₁, -⟩ := grpPullback_iso hψ (isGrpPullback_pullback A (spMap (algebraMap K L)))
  have : IsMonHom (e₁ ≪≫ e.symm).hom := inferInstanceAs (IsMonHom (e₁.hom ≫ e.inv))
  have h := (isGrpPullback_of_iso (e₁ ≪≫ e.symm)).comp (isGrpPullback_pullback G (spMap (algebraMap W L)))
  exact ⟨_, h.congr (Category.id_comp _) rfl⟩

end GlobalTheory.SS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackOfGroupSchemeModelBaseChangeStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGrpPullback_of_group_scheme_model_base_change : ∀ (K W L : Type) [Field K] [CommRing W] [Field L] [Algebra K L] [Algebra W L] (A : Over (Sp K)) [GrpObj A] (G : Over (Sp W)) [GrpObj G], GlobalTheory.SS.IsModel (L := L) A G → ∀ (A' : Over (Sp L)) [GrpObj A'] (ψ : A'.left ⟶ A.left), IsGrpPullback A' A (spMap (algebraMap K L)) ψ → ∃ φ : A'.left ⟶ G.left, IsGrpPullback A' G (spMap (algebraMap W L)) φ := by
  first | exact @GlobalTheory.SS.exists_isGrpPullback_of_isModel | exact GlobalTheory.SS.exists_isGrpPullback_of_isModel | (intros; apply GlobalTheory.SS.exists_isGrpPullback_of_isModel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameCharacterFromProduct
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeoActCompare.TameConj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.GeoActCompare
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IndefiniteRowSideFullHecke.LevelLiftConditions (idealHat CongMod)
open GlobalTheory.IdemSupport (mem_intAE_iff parts_cA finPart_cA_mem)

variable {D : D7}

theorem mul_mem_intAE {y z : Af D.host.F ⊗[D.host.F] D.host.E} (hy : y ∈ intAE D) (hz : z ∈ intAE D) :
    y * z ∈ intAE D := by
  rw [mem_intAE_iff] at hy hz ⊢
  rw [RingHom.map_mul]
  exact mul_mem hy hz

theorem FinUnit_mul {x y : (AE D)ˣ} (hx : FinUnit x) (hy : FinUnit y) : FinUnit (x * y) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Units.val_mul, RingHom.map_mul, hx.1, hy.1, one_mul]
  · rw [Units.val_mul, RingHom.map_mul]
    exact mul_mem_intAE hx.2.1 hy.2.1
  · rw [mul_inv, Units.val_mul, RingHom.map_mul]
    exact mul_mem_intAE hx.2.2 hy.2.2

theorem FinUnit_inv {x : (AE D)ˣ} (hx : FinUnit x) : FinUnit x⁻¹ := by
  refine ⟨?_, hx.2.2, hx.2.1⟩
  have e : infPart D (x : AE D) * infPart D ((x⁻¹ : (AE D)ˣ) : AE D) = 1 := by
    rw [← RingHom.map_mul, Units.mul_inv, RingHom.map_one]
  rwa [hx.1, one_mul] at e

theorem FinUnit_conj {x : (AE D)ˣ} (hx : FinUnit x) : FinUnit (Units.map (cA D).toMonoidHom x) := by
  refine ⟨?_, finPart_cA_mem hx.2.1, finPart_cA_mem hx.2.2⟩
  exact (parts_cA (x : AE D)).1.trans (by rw [hx.1, RingHom.map_one])


end GlobalTheory.GeoActCompare.TameConj
end
end
