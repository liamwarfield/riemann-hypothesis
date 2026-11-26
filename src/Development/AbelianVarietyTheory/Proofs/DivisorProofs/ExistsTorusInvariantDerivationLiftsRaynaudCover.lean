module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTanAtGTv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueWeightDecompositionRaynaudAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartConst

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageProjectionAbelianPart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageProjectionAbelianPart
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RayEv

theorem Ray.isAffineHom_q {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {O : Type} [CommRing O] [StarRing O]
    [Module O D.X] {oa : D.OAct O} (Y : Ray oa) : IsAffineHom Y.q.left := by
  obtain ⟨c⟩ := GlobalTheory.TorusModel.nonempty_gtCoord GlobalTheory.allSixLaws.1.globalFns Y.isGt ⊥ 0
  have := c.q_affine
  let F := fstG (⊥ : Ideal R) 0 Y.H
  let j := inv F.left
  have hF : F.left ≫ Y.H.hom = (thickObj R ⊥ 0 Y.H).hom ≫ thick R ⊥ 0 := Over.w F
  let ξ := Y.Φ Y.H (𝟙 _)
  obtain ⟨x, hx⟩ := GlobalTheory.TorusCoord.exists_point c (T := Y.H) (Y.H.hom ≫ inv (thick R ⊥ 0)) (by simp) ξ
  obtain ⟨ξ', hξ'⟩ := GlobalTheory.TorusCoord.exists_isPointOf c (T := Y.H) j (by
    rw [← hF]; exact IsIso.inv_hom_id_assoc _ _)
  let b : Y.H ⟶ Y.H := (Y.Φ Y.H).symm ξ'
  have hb : Y.Φ Y.H b = ξ' := Equiv.apply_symm_apply _ _
  let a := x ≫ F.left
  have ha : a ≫ Y.H.hom = Y.H.hom := by
    rw [Category.assoc, hF]
    exact GlobalTheory.TorusCoord.IsPointOf.comp_hom c hx
  let a' : Y.H ⟶ Y.H := Over.homMk a ha
  have haj : a ≫ j = x := by simp [a, j]
  have e1 : b.left ≫ x = j := by
    have h1 : GtPt.IsPull b.left ξ (Y.Φ Y.H (b ≫ 𝟙 _)) := Y.rep.1 Y.H Y.H b (𝟙 _)
    rw [Category.comp_id, hb] at h1
    exact (GlobalTheory.TorusCoord.IsPointOf.pull c hx h1).unique_left c hξ'
  have e1' : b.left ≫ a = 𝟙 _ := by
    rw [← Category.assoc, e1]; simp [j]
  have e2 : a' ≫ b = 𝟙 _ := by
    have h2 : GtPt.IsPull a (Y.Φ Y.H b) (Y.Φ Y.H (a' ≫ b)) := Y.rep.1 Y.H Y.H a' b
    rw [hb] at h2
    have h3 := GlobalTheory.TorusCoord.IsPointOf.pull c hξ' h2
    rw [haj] at h3
    exact (Y.Φ Y.H).injective (h3.unique_right c hx)
  have e2' : a ≫ b.left = 𝟙 _ := congrArg (·.left) e2
  have : IsIso a := ⟨⟨b.left, e2', e1'⟩⟩
  have hq : Y.q.left = a ≫ j ≫ c.q.left ≫ pullback.fst D.P.A.hom (thick R ⊥ 0) := by
    rw [← Category.assoc a j, haj, ← GlobalTheory.TorusCoord.pG_left]
    exact hx.1
  rw [hq]
  infer_instance

end GlobalTheory.RayEv

theorem GlobalTheory.RayEv.Ray.isAffineOpen_preimage_q : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type)
    [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.affineOpens),
    IsAffineOpen (Y.q.left ⁻¹ᵁ V.1) := by
  intro R _ _ Q O _ _ _ oa Y V
  haveI := Y.isAffineHom_q
  exact V.2.preimage Y.q.left
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageProjectionAbelianPartStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAffineOpen_preimage_projection_abelianPart : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.affineOpens), IsAffineOpen (Y.q.left ⁻¹ᵁ V.1) := by
  first | exact @GlobalTheory.RayEv.Ray.isAffineOpen_preimage_q | exact GlobalTheory.RayEv.Ray.isAffineOpen_preimage_q | (intros; apply GlobalTheory.RayEv.Ray.isAffineOpen_preimage_q <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantLiftDerivationRaynaud
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPreservingVectorFieldOnSmallerPreimages
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudTorusWeightFunctionOfBasicOpens
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudTorusWeightFunctionOfBasicOpens
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.WtLocal

open GlobalTheory.ZH.CrdCalc (valR_res valR_spMap)
open GlobalTheory.TorusModel (isPull_iff)

theorem gm_comp' {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (q : Y ⟶ X) (z : Z) (U : X.Opens) (h : q (r z) ∈ U) (a : Γ(X, U)ˣ) :
    gm (r ≫ q) z U a = Units.map (r.stalkMap z).hom.toMonoidHom (gm q (r z) U a) := by
  refine Units.ext ?_
  rw [← gs_unit (r ≫ q) z U h, ← gs_pull r q z U h, gs_stalkMap r z (q ⁻¹ᵁ U) h, gs_pull (𝟙 Y) q (r z) U h,
    Category.id_comp, gs_unit q (r z) U h]
  rfl

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} (Y : Ray oa)

theorem isWt_of_local (α : Q.X) (V : Y.H.left.Opens) (f : Γ(Y.H.left, V))
    (h : ∀ (S : Type) [CommRing S] [IsLocalRing S] (φ : R →+* S) (x x' : Over.mk (spMap φ) ⟶ Y.H) (c : Q.X → Sˣ),
      ⊤ ≤ x.left ⁻¹ᵁ V → ⊤ ≤ x'.left ⁻¹ᵁ V → x' ≫ Y.q = x ≫ Y.q →
      (∀ χ y J, Good Q.P.L y J → val ((Y.Φ _ x').s χ) (𝟙 _) y J =
        gm (𝟙 (Over.mk (spMap φ)).left) y ⊤ (unitOn (c χ)) * val ((Y.Φ _ x).s χ) (𝟙 _) y J) →
      valR (A := S) x'.left V f = c α * valR (A := S) x.left V f) : IsWt Y α V f := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  subst ha ha'
  refine sub_eq_zero.1 (eq_zero_of_localization _ fun P hP => (map_sub _ _ _).trans (sub_eq_zero.2 ?_))
  let l := algebraMap S (Localization.AtPrime P)
  let k : Over.mk (spMap (l.comp φ)) ⟶ Over.mk (spMap φ) := Over.homMk (spMap l)
    (Spec.map_comp (CommRingCat.ofHom φ) (CommRingCat.ofHom l)).symm
  obtain ⟨a₁, a₂⟩ := valR_spMap l x.left V hV
  obtain ⟨b₁, b₂⟩ := valR_spMap l x'.left V hV'
  have := h _ (l.comp φ) (k ≫ x) (k ≫ x') (fun χ => Units.map l.toMonoidHom (c χ)) a₁ b₁
    (by rw [Category.assoc, Category.assoc, hq]) fun χ y J hJ => by
      have hJ' : Good Q.P.L (k.left y) fun ψ => J (k.left ≫ ψ) := fun ψ => hJ (k.left ≫ ψ)
      have key : ∀ u : Over.mk (spMap φ) ⟶ Y.H, val ((Y.Φ _ (k ≫ u)).s χ) (𝟙 _) y J =
          Units.map (k.left.stalkMap y).hom.toMonoidHom
            (val ((Y.Φ _ u).s χ) (𝟙 _) (k.left y) fun ψ => J (k.left ≫ ψ)) := fun u => by
        refine (((isPull_iff _ _ _).1 (Y.rep.1 _ _ k u)).2 χ y J hJ).trans ?_
        rw [val_of _ (𝟙 _) _ _ (fun i => J (k.left ≫ DegPre.gtφT Q _ (Y.Φ _ u).b χ i)) (fun i => by rw [Category.id_comp])]
        refine Eq.trans ?_ (gm_comp' k.left (𝟙 _) y _ (hJ.mem _ k.left) _)
        rw [Category.comp_id]
        rfl
      rw [key, key, hc χ _ _ hJ', map_mul, ← gm_comp' k.left (𝟙 _) y ⊤ trivial]
      congr 1
      refine Units.ext ?_
      rw [gm_val _ _ ⊤ trivial, gm_val _ _ ⊤ trivial]
      refine congrArg ((Sp (Localization.AtPrime P)).presheaf.germ ⊤ y trivial).hom ?_
      exact (congrArg (fun q => q.hom (c χ : S)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom l))).symm
  rw [map_mul]
  exact (b₂ f).symm.trans (this.trans (congrArg (_ * ·) (a₂ f)))

end GlobalTheory.Heat.WtLocal

namespace GlobalTheory.Heat.WtLocal

open GlobalTheory.ZH.CrdCalc (valR_res)

theorem isWt_of_basicOpen : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.affineOpens) (V' : Q.P.A.left.Opens), V' ≤ V.1 → ∀ (α : Q.X) (f : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V')), (∀ (g : Γ(Q.P.A.left, V.1)) (h : Q.P.A.left.basicOpen g ≤ V'), IsWt Y α (Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g) (resG Y.H.left (Y.q.left.preimage_mono h) f)) → IsWt Y α (Y.q.left ⁻¹ᵁ V') f := by
  intro R _ _ Q O _ _ _ oa Y V V' hV α f hf
  refine isWt_of_local Y α _ _ fun S _ _ φ x x' c hx hx' hq hc => ?_
  have e : x'.left ≫ Y.q.left = x.left ≫ Y.q.left := congrArg (fun q => q.left) hq
  have hp : Y.q.left (x'.left (closedPoint S)) ∈ V' := hx' trivial
  obtain ⟨g, hg, hpg⟩ := V.2.exists_basicOpen_le ⟨_, hp⟩ (hV hp)
  have m' : ⊤ ≤ x'.left ⁻¹ᵁ (Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g) :=
    (Scheme.preimage_eq_top_of_closedPoint_mem (R := .of S) x'.left hpg).ge
  have m : ⊤ ≤ x.left ⁻¹ᵁ (Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g) := by
    rw [← Scheme.Hom.comp_preimage, ← e]; exact m'
  have t := hf g hg S φ x x' c _ _ rfl rfl m m' hq hc
  exact (valR_res (R := S) x'.left _ m' f).symm.trans (t.trans (congrArg (_ * ·) (valR_res (R := S) x.left _ m f)))

end GlobalTheory.Heat.WtLocal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudTorusWeightFunctionOfBasicOpensStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRaynaudTorusWeightFunction_of_basicOpens : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.affineOpens) (V' : Q.P.A.left.Opens), V' ≤ V.1 → ∀ (α : Q.X) (f : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V')), (∀ (g : Γ(Q.P.A.left, V.1)) (h : Q.P.A.left.basicOpen g ≤ V'), IsWt Y α (Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g) (resG Y.H.left (Y.q.left.preimage_mono h) f)) → IsWt Y α (Y.q.left ⁻¹ᵁ V') f := by
  first | exact @GlobalTheory.Heat.WtLocal.isWt_of_basicOpen | exact GlobalTheory.Heat.WtLocal.isWt_of_basicOpen | (intros; apply GlobalTheory.Heat.WtLocal.isWt_of_basicOpen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPreservingVectorFieldOnSmallerPreimages
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.WtSub

theorem valR_resG' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) {U V : X.Opens} (e : V ≤ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)) : valR x V (resG X e f) = valR x U f := by
  have h' : ⊤ ≤ x ⁻¹ᵁ U := h.trans (x.preimage_mono e)
  simp only [valR, dif_pos h, dif_pos h']
  congr 1
  change (X.presheaf.map (homOfLE e).op ≫ x.appLE V ⊤ h).hom f = _
  rw [Scheme.Hom.map_appLE]

theorem valR_one' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    valR x U (1 : Γ(X, U)) = 1 := by
  simp only [valR, dif_pos h, map_one]

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} {Y : Ray oa}

theorem isWt_res {α : Q.X} {U V : Y.H.left.Opens} (e : V ≤ U) {f : Γ(Y.H.left, U)} (hf : IsWt Y α U f) :
    IsWt Y α V (resG Y.H.left e f) := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  have hU : ⊤ ≤ a ⁻¹ᵁ U := hV.trans (a.preimage_mono e)
  have hU' : ⊤ ≤ a' ⁻¹ᵁ U := hV'.trans (a'.preimage_mono e)
  rw [valR_resG' a' e hV', valR_resG' a e hV]
  exact hf S φ x x' c a a' ha ha' hU hU' hq hc

theorem isWt_inv {V : Y.H.left.Opens} (u : Γ(Y.H.left, V)ˣ) (hu : IsWt Y 0 V u.val) :
    IsWt Y 0 V (u⁻¹ : Γ(Y.H.left, V)ˣ).val := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  have hc0 : c 0 = 1 := WtAlg.c_zero x x' c hc
  have e1 := hu S φ x x' c a a' ha ha' hV hV' hq hc
  rw [hc0, Units.val_one, _root_.one_mul] at e1
  rw [hc0, Units.val_one, _root_.one_mul]
  have m : ∀ b : Sp S ⟶ Y.H.left, ⊤ ≤ b ⁻¹ᵁ V →
      valR b V (u⁻¹ : Γ(Y.H.left, V)ˣ).val * valR b V u.val = 1 := by
    intro b hb
    rw [← WtAlg.valR_mul'' b V hb, Units.inv_mul, valR_one' b V hb]
  have m' : ∀ b : Sp S ⟶ Y.H.left, ⊤ ≤ b ⁻¹ᵁ V →
      valR b V u.val * valR b V (u⁻¹ : Γ(Y.H.left, V)ˣ).val = 1 := by
    intro b hb
    rw [← WtAlg.valR_mul'' b V hb, Units.mul_inv, valR_one' b V hb]
  calc valR a' V (u⁻¹ : Γ(Y.H.left, V)ˣ).val
        = valR a' V (u⁻¹ : Γ(Y.H.left, V)ˣ).val *
            (valR a V u.val * valR a V (u⁻¹ : Γ(Y.H.left, V)ˣ).val) := by rw [m' a hV, _root_.mul_one]
    _ = (valR a' V (u⁻¹ : Γ(Y.H.left, V)ˣ).val * valR a' V u.val) *
            valR a V (u⁻¹ : Γ(Y.H.left, V)ˣ).val := by rw [e1, _root_.mul_assoc]
    _ = valR a V (u⁻¹ : Γ(Y.H.left, V)ˣ).val := by rw [m a' hV', _root_.one_mul]

theorem isRaynaudTorusWeightFunction_zero_pow {V : Y.H.left.Opens} {g : Γ(Y.H.left, V)} (hg : IsWt Y 0 V g) (n : ℕ) : IsWt Y 0 V (g ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    have h1 := WtAlg.isWt_natCast (Y := Y) V 1
    rwa [Nat.cast_one] at h1
  | succ n ih =>
    rw [pow_succ']
    exact WtAlg.isRaynaudTorusWeightFunction_weightZero_mul hg ih

end GlobalTheory.Heat.WtSub

namespace GlobalTheory.Heat.WtSub

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O}

theorem isWt_basicOpen (Y : Ray oa) (V : Q.P.A.left.affineOpens) (d : Fld Y.H.left)
    (hd : IsField (Y.q.left ⁻¹ᵁ V.1) d)
    (hpres : ∀ (α : Q.X) f, IsWt Y α (Y.q.left ⁻¹ᵁ V.1) f → IsWt Y α _ (d _ f))
    (hdec : ∀ (W : Q.P.A.left.Opens), IsAffineOpen W → ∀ f : Γ(Y.H.left, Y.q.left ⁻¹ᵁ W),
      ∃! F : Q.X →₀ Γ(Y.H.left, Y.q.left ⁻¹ᵁ W), (∀ χ, IsWt Y χ _ (F χ)) ∧ f = F.sum (fun _ t => t))
    (hP : IsAffineOpen (Y.q.left ⁻¹ᵁ V.1))
    (g : Γ(Q.P.A.left, V.1)) (α : Q.X) (f : Γ(Y.H.left, Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g))
    (hf : IsWt Y α _ f) : IsWt Y α _ (d _ f) := by
  have hle : Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g ≤ Y.q.left ⁻¹ᵁ V.1 :=
    Y.q.left.preimage_mono (Q.P.A.left.basicOpen_le g)
  set G : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1) := (Y.q.left.app V.1).hom g with hGdef
  have hG0 : IsWt Y 0 _ G := AbConst.isWt_app Y V.1 g
  have heq : Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g = Y.H.left.basicOpen G :=
    Scheme.preimage_basicOpen Y.q.left g
  let _ : Algebra Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1) Γ(Y.H.left, Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g) :=
    (Y.H.left.presheaf.map (homOfLE hle).op).hom.toAlgebra
  have : IsLocalization.Away G Γ(Y.H.left, Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g) :=
    hP.isLocalization_of_eq_basicOpen G (homOfLE hle) heq
  have halg : ∀ t, algebraMap Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1)
      Γ(Y.H.left, Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g) t = resG Y.H.left hle t := fun _ => rfl
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj G f
  rw [← map_pow, halg, halg] at ha
  have hunit : IsUnit (resG Y.H.left hle (G ^ n)) := by
    rw [← halg, map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit G).pow n
  have hGn0 : IsWt Y 0 _ (resG Y.H.left hle (G ^ n)) := isWt_res hle (isRaynaudTorusWeightFunction_zero_pow hG0 n)
  obtain ⟨F, ⟨hFw, hFa⟩, -⟩ := hdec V.1 V.2 a
  obtain ⟨F0, -, huniq⟩ := hdec (Q.P.A.left.basicOpen g) (V.2.basicOpen g) (f * resG Y.H.left hle (G ^ n))
  have hA : Finsupp.mapRange (resG Y.H.left hle) (map_zero _) F = F0 := by
    refine huniq _ ⟨fun χ => ?_, ?_⟩
    · rw [Finsupp.mapRange_apply]
      exact isWt_res hle (hFw χ)
    · rw [Finsupp.sum_mapRange_index (fun _ => rfl), ha, hFa, map_finsuppSum]
  have hB : Finsupp.single α (f * resG Y.H.left hle (G ^ n)) = F0 := by
    refine huniq _ ⟨fun χ => ?_, ?_⟩
    · by_cases hχ : α = χ
      · subst hχ
        rw [Finsupp.single_eq_same, _root_.mul_comm]
        exact WtAlg.isRaynaudTorusWeightFunction_weightZero_mul hGn0 hf
      · rw [Finsupp.single_eq_of_ne' hχ]
        exact WtAlg.isWt_zero _ _
    · rw [Finsupp.sum_single_index rfl]
  have hα : resG Y.H.left hle (F α) = f * resG Y.H.left hle (G ^ n) := by
    have h1 := DFunLike.congr_fun (hA.trans hB.symm) α
    rwa [Finsupp.mapRange_apply, Finsupp.single_eq_same] at h1
  obtain ⟨-, hmul, hres⟩ := hd
  have hdfG : IsWt Y α _ (d _ (f * resG Y.H.left hle (G ^ n))) := by
    rw [← hα, hres _ _ hle le_rfl]
    exact isWt_res hle (hpres α (F α) (hFw α))
  have hdG : IsWt Y 0 _ (d _ (resG Y.H.left hle (G ^ n))) := by
    rw [hres _ _ hle le_rfl]
    exact isWt_res hle (hpres 0 (G ^ n) (isRaynaudTorusWeightFunction_zero_pow hG0 n))
  have hGdf : IsWt Y α _ (resG Y.H.left hle (G ^ n) * d _ f) := by
    have e2 : resG Y.H.left hle (G ^ n) * d _ f =
        d _ (f * resG Y.H.left hle (G ^ n)) - f * d _ (resG Y.H.left hle (G ^ n)) := by
      rw [hmul _ hle]
      ring
    rw [e2, _root_.mul_comm f (d _ (resG Y.H.left hle (G ^ n)))]
    exact WtAlg.isWt_sub hdfG (WtAlg.isRaynaudTorusWeightFunction_weightZero_mul hdG hf)
  obtain ⟨u, hu⟩ := hunit
  have hu0 : IsWt Y 0 _ (u⁻¹ : Γ(Y.H.left, Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g)ˣ).val := by
    refine isWt_inv u ?_
    rw [hu]
    exact hGn0
  have h2 := WtAlg.isRaynaudTorusWeightFunction_weightZero_mul hu0 hGdf
  rwa [← hu, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul] at h2

end GlobalTheory.Heat.WtSub

namespace GlobalTheory.Heat.WtSub

theorem isWt_field_of_le : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.affineOpens) (d : Fld Y.H.left), IsField (Y.q.left ⁻¹ᵁ V.1) d → (∀ (α : Q.X) f, IsWt Y α (Y.q.left ⁻¹ᵁ V.1) f → IsWt Y α _ (d _ f)) → ∀ (α : Q.X) (V' : Q.P.A.left.Opens), V' ≤ V.1 → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d _ f) := by
  intro R _ _ Q O _ _ _ oa Y V d hd hpres α V' hV' f hf
  apply GlobalTheory.T.isRaynaudTorusWeightFunction_of_basicOpens R Q O oa Y V V' hV' α (d _ f)
  intro g hg
  have hle : Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V.1 := Y.q.left.preimage_mono hV'
  obtain ⟨hadd, hmul, hres⟩ := hd
  rw [← hres _ _ (Y.q.left.preimage_mono hg) hle f]
  exact isWt_basicOpen Y V d ⟨hadd, hmul, hres⟩ hpres (fun W hW => GlobalTheory.T.existsUnique_weightDecomposition_raynaud_affine R Q O oa Y W hW)
    (GlobalTheory.T.isAffineOpen_preimage_projection_abelianPart R Q O oa Y V) g α _ (isWt_res _ hf)

end GlobalTheory.Heat.WtSub
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPreservingVectorFieldOnSmallerPreimagesStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_preserving_vectorField_on_smaller_preimages : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.affineOpens) (d : Fld Y.H.left), IsField (Y.q.left ⁻¹ᵁ V.1) d → (∀ (α : Q.X) f, IsWt Y α (Y.q.left ⁻¹ᵁ V.1) f → IsWt Y α _ (d _ f)) → ∀ (α : Q.X) (V' : Q.P.A.left.Opens), V' ≤ V.1 → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d _ f) := by
  first | exact @GlobalTheory.Heat.WtSub.isWt_field_of_le | exact GlobalTheory.Heat.WtSub.isWt_field_of_le | (intros; apply GlobalTheory.Heat.WtSub.isWt_field_of_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightPreservingLiftOfBaseDerivation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudTorusWeightFunctionMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudTorusWeightFunctionMul
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.WtMul

open GlobalTheory.Heat.WtAlg

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} {Y : Ray oa}

theorem c_add {S : Type} [CommRing S] {φ : R →+* S} (x x' : Over.mk (spMap φ) ⟶ Y.H) (c : Q.X → Sˣ)
    (hq : x' ≫ Y.q = x ≫ Y.q)
    (hc : ∀ χ y J, Good Q.P.L y J →
      val ((Y.Φ _ x').s χ) (𝟙 _) y J = gm (𝟙 (Over.mk (spMap φ)).left) y ⊤ (unitOn (c χ)) * val ((Y.Φ _ x).s χ) (𝟙 _) y J)
    (χ χ' : Q.X) : c (χ + χ') = c χ * c χ' := by
  have hu : unitOn (c (χ + χ')) = unitOn (c χ) * unitOn (c χ') := unit_ext fun y _ => by
    obtain ⟨J, hJ, -⟩ := exists_good Q.P.L Q.P.isLB y (K := PEmpty.{1}) PEmpty.elim PEmpty.elim
      (fun a => a.elim) (fun a => a.elim)
    have e₁ := GlobalTheory.TorusModel.cv_add (Y.Φ _ x) hJ χ χ'
    have e₂ := GlobalTheory.TorusModel.cv_add (Y.Φ _ x') hJ χ χ'
    rw [Ray.Φ_b] at e₁ e₂
    rw [hq] at e₂
    dsimp only [GlobalTheory.TorusModel.cv] at e₁ e₂
    rw [hc _ y J hJ, hc _ y J hJ, hc _ y J hJ, _root_.mul_assoc, e₁, _root_.mul_mul_mul_comm] at e₂
    rw [map_mul]
    exact mul_right_cancel e₂
  have := congrArg (fun u : (Γ(Sp S, ⊤))ˣ => (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom u.val) hu
  simp only [unitOn, Units.coe_map, Units.val_mul, map_mul] at this
  refine Units.ext ((Iso.inv_hom_id_apply _ _).symm.trans (this.trans ?_))
  exact congrArg₂ (· * ·) (Iso.inv_hom_id_apply _ _) (Iso.inv_hom_id_apply _ _)

theorem isWt_mul : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Y.H.left.Opens) (χ χ' : Q.X) (f g : Γ(Y.H.left, V)), IsWt Y χ V f → IsWt Y χ' V g → IsWt Y (χ + χ') V (f * g) := by
  intro R _ _ Q O _ _ _ oa Y V χ χ' f g hf hg S _ φ x x' c a a' ha ha' hV hV' hq hc
  rw [valR_mul'' _ _ hV', valR_mul'' _ _ hV, hg S φ x x' c a a' ha ha' hV hV' hq hc,
    hf S φ x x' c a a' ha ha' hV hV' hq hc, c_add x x' c hq hc, Units.val_mul]
  ring

end GlobalTheory.Heat.WtMul
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudTorusWeightFunctionMulStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRaynaudTorusWeightFunction_mul : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Y.H.left.Opens) (χ χ' : Q.X) (f g : Γ(Y.H.left, V)), IsWt Y χ V f → IsWt Y χ' V g → IsWt Y (χ + χ') V (f * g) := by
  first | exact @GlobalTheory.Heat.WtMul.isWt_mul | exact GlobalTheory.Heat.WtMul.isWt_mul | (intros; apply GlobalTheory.Heat.WtMul.isWt_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightPreservingLiftOfBaseDerivation
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WtLift

variable {X A : Type} [AddCommGroup X] [CommRing A] (P : X → A → Prop)
  (hadd : ∀ χ a b, P χ a → P χ b → P χ (a + b)) (hzero : ∀ χ, P χ 0)
  (hmul : ∀ χ ψ a b, P χ a → P ψ b → P (χ + ψ) (a * b))
  (hdec : ∀ f : A, ∃! F : X →₀ A, (∀ χ, P χ (F χ)) ∧ f = F.sum (fun _ t => t))


include hdec in
def dec (f : A) : X →₀ A := (hdec f).exists.choose

include hdec in
theorem dec_spec (f : A) : (∀ χ, P χ (dec P hdec f χ)) ∧ f = (dec P hdec f).sum (fun _ t => t) :=
  (hdec f).exists.choose_spec

include hdec in
theorem dec_eq {f : A} {F : X →₀ A} (hF : ∀ χ, P χ (F χ)) (hs : f = F.sum (fun _ t => t)) : dec P hdec f = F :=
  (hdec f).unique (dec_spec P hdec f) ⟨hF, hs⟩

include hadd hdec in
theorem dec_add (a b : A) : dec P hdec (a + b) = dec P hdec a + dec P hdec b := by
  refine dec_eq P hdec (fun χ => ?_) ?_
  · rw [Finsupp.add_apply]; exact hadd _ _ _ ((dec_spec P hdec a).1 χ) ((dec_spec P hdec b).1 χ)
  · rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), ← (dec_spec P hdec a).2, ← (dec_spec P hdec b).2]

include hzero hdec in
theorem dec_single {α : X} {f : A} (hf : P α f) : dec P hdec f = Finsupp.single α f := by
  classical
  refine dec_eq P hdec (fun χ => ?_) ?_
  · rw [Finsupp.single_apply]; split_ifs with h
    · exact h ▸ hf
    · exact hzero χ
  · rw [Finsupp.sum_single_index rfl]

include hzero hdec in
theorem dec_zero : dec P hdec (0 : A) = 0 := by
  rw [dec_single P hzero hdec (hzero 0), Finsupp.single_zero]

include hzero hmul hdec in
theorem dec_mul {χ : X} {f : A} (hf : P χ f) (h : A) (ψ : X) :
    dec P hdec (f * h) (χ + ψ) = f * dec P hdec h ψ := by
  set G : X →₀ A := Finsupp.mapDomain (fun ψ => χ + ψ) ((dec P hdec h).mapRange (f * ·) (mul_zero f)) with hG
  have hinj : Function.Injective (fun ψ : X => χ + ψ) := add_right_injective χ
  have hGv : ∀ ψ, G (χ + ψ) = f * dec P hdec h ψ := fun ψ => by
    rw [hG, Finsupp.mapDomain_apply_of_injective hinj, Finsupp.mapRange_apply]
  have key : dec P hdec (f * h) = G := by
    refine dec_eq P hdec (fun ω => ?_) ?_
    · have e : ω = χ + (ω - χ) := by abel
      rw [e, hGv]; exact hmul _ _ _ _ hf ((dec_spec P hdec h).1 _)
    · rw [hG, Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl),
        Finsupp.sum_mapRange_index (fun _ => rfl), ← Finsupp.mul_sum, ← (dec_spec P hdec h).2]
  rw [key, hGv]

variable (δ₀ : A → A)

def proj (f : A) : A := (dec P hdec f).sum (fun χ t => dec P hdec (δ₀ t) χ)

include hadd hzero hdec in
theorem proj_add (h0 : ∀ a b, δ₀ (a + b) = δ₀ a + δ₀ b) (a b : A) :
    proj P hdec δ₀ (a + b) = proj P hdec δ₀ a + proj P hdec δ₀ b := by
  have hz : δ₀ 0 = 0 := by
    have := h0 0 0; simp only [add_zero] at this; exact left_eq_add.mp this
  unfold proj
  rw [dec_add P hadd hdec, Finsupp.sum_add_index']
  · intro χ; rw [hz, dec_zero P hzero hdec, Finsupp.zero_apply]
  · intro χ s t; rw [h0, dec_add P hadd hdec, Finsupp.add_apply]

include hzero hdec in
theorem proj_of_wt (hz : δ₀ 0 = 0) {α : X} {f : A} (hf : P α f) : proj P hdec δ₀ f = dec P hdec (δ₀ f) α := by
  unfold proj; rw [dec_single P hzero hdec hf, Finsupp.sum_single_index]
  rw [hz, dec_zero P hzero hdec]; rfl


include hzero hdec in
theorem induction_wt (Qp : A → Prop) (q0 : Qp 0) (qadd : ∀ a b, Qp a → Qp b → Qp (a + b))
    (qw : ∀ χ a, P χ a → Qp a) (f : A) : Qp f := by
  rw [(dec_spec P hdec f).2, Finsupp.sum]
  exact Finset.sum_induction _ Qp qadd q0 (fun χ _ => qw χ _ ((dec_spec P hdec f).1 χ))

include hadd hzero hmul hdec in
theorem proj_mul (h0 : ∀ a b, δ₀ (a + b) = δ₀ a + δ₀ b) (h1 : ∀ a b, δ₀ (a * b) = a * δ₀ b + b * δ₀ a) (a b : A) :
    proj P hdec δ₀ (a * b) = a * proj P hdec δ₀ b + b * proj P hdec δ₀ a := by
  have hz : δ₀ 0 = 0 := by
    have := h0 0 0; simp only [add_zero] at this; exact left_eq_add.mp this
  have pz : proj P hdec δ₀ 0 = 0 := by
    unfold proj; rw [dec_zero P hzero hdec, Finsupp.sum_zero_index]
  have hom : ∀ χ ψ x y, P χ x → P ψ y →
      proj P hdec δ₀ (x * y) = x * proj P hdec δ₀ y + y * proj P hdec δ₀ x := by
    intro χ ψ x y hx hy
    rw [proj_of_wt P hzero hdec δ₀ hz (hmul _ _ _ _ hx hy), proj_of_wt P hzero hdec δ₀ hz hy,
      proj_of_wt P hzero hdec δ₀ hz hx, h1, dec_add P hadd hdec, Finsupp.add_apply, dec_mul P hzero hmul hdec hx,
      add_comm χ ψ, dec_mul P hzero hmul hdec hy]
  have padd := proj_add P hadd hzero hdec δ₀ h0

  have step : ∀ ψ y, P ψ y → ∀ x, proj P hdec δ₀ (x * y) = x * proj P hdec δ₀ y + y * proj P hdec δ₀ x := by
    intro ψ y hy
    refine induction_wt P hzero hdec _ ?_ ?_ (fun χ x hx => hom χ ψ x y hx hy)
    · rw [zero_mul, pz, zero_mul, mul_zero, add_zero]
    · intro x x' ex ex'; rw [add_mul, padd, padd, ex, ex']; ring
  revert b
  intro b
  refine induction_wt P hzero hdec (fun y => proj P hdec δ₀ (a * y) = a * proj P hdec δ₀ y + y * proj P hdec δ₀ a)
    ?_ ?_ (fun ψ y hy => step ψ y hy a) b
  · simp only [mul_zero, pz, zero_mul, add_zero]
  · intro y y' ey ey'; rw [mul_add, padd, ey, ey', padd]; ring

include hzero hdec in
theorem proj_wt (hz : δ₀ 0 = 0) {α : X} {f : A} (hf : P α f) : P α (proj P hdec δ₀ f) := by
  rw [proj_of_wt P hzero hdec δ₀ hz hf]; exact (dec_spec P hdec _).1 α

end GlobalTheory.WtLift

namespace GlobalTheory.WtLift

theorem exists_isWt_lift : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.affineOpens) (D : Derivation ℤ R R) (δ₀ : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1) → Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1)), (∀ a b, δ₀ (a + b) = δ₀ a + δ₀ b) → (∀ a b, δ₀ (a * b) = a * δ₀ b + b * δ₀ a) → (∀ r, δ₀ (constFn Y.H.hom _ r) = constFn Y.H.hom _ (D r)) → ∃ δ : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1) → Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1), (∀ a b, δ (a + b) = δ a + δ b) ∧ (∀ a b, δ (a * b) = a * δ b + b * δ a) ∧ (∀ r, δ (constFn Y.H.hom _ r) = constFn Y.H.hom _ (D r)) ∧ ∀ (α : Q.X) f, IsWt Y α _ f → IsWt Y α _ (δ f) := by
  intro R _ _ Q O _ _ _ oa Y V D δ₀ h0 h1 hc
  have hadd : ∀ (χ : Q.X) (a b : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1)), IsWt Y χ _ a → IsWt Y χ _ b → IsWt Y χ _ (a + b) :=
    fun χ a b ha hb => WtAlg.isWt_add ha hb
  have hzero : ∀ χ : Q.X, IsWt Y χ (Y.q.left ⁻¹ᵁ V.1) 0 := fun χ => WtAlg.isWt_zero (Y := Y) χ _
  have hmul : ∀ (χ ψ : Q.X) (a b : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1)), IsWt Y χ _ a → IsWt Y ψ _ b →
      IsWt Y (χ + ψ) _ (a * b) :=
    fun χ ψ a b ha hb => GlobalTheory.T.isRaynaudTorusWeightFunction_mul R Q O oa Y _ χ ψ a b ha hb
  have hdec := GlobalTheory.T.existsUnique_weightDecomposition_raynaud_affine R Q O oa Y V.1 V.2
  have hz : δ₀ 0 = 0 := by
    have := h0 0 0; simp only [add_zero] at this; exact left_eq_add.mp this
  refine ⟨proj (fun χ f => IsWt Y χ _ f) hdec δ₀, proj_add _ hadd hzero hdec δ₀ h0,
    proj_mul _ hadd hzero hmul hdec δ₀ h0 h1, fun r => ?_, fun α f hf => proj_wt _ hzero hdec δ₀ hz hf⟩
  rw [proj_of_wt _ hzero hdec δ₀ hz (WtAlg.isWt_constFn (Y := Y) _ r), hc,
    dec_single _ hzero hdec (WtAlg.isWt_constFn (Y := Y) _ (D r)), Finsupp.single_eq_same]

end GlobalTheory.WtLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightPreservingLiftOfBaseDerivationStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weight_preserving_lift_of_base_derivation : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.affineOpens) (D : Derivation ℤ R R) (δ₀ : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1) → Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1)), (∀ a b, δ₀ (a + b) = δ₀ a + δ₀ b) → (∀ a b, δ₀ (a * b) = a * δ₀ b + b * δ₀ a) → (∀ r, δ₀ (constFn Y.H.hom _ r) = constFn Y.H.hom _ (D r)) → ∃ δ : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1) → Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1), (∀ a b, δ (a + b) = δ a + δ b) ∧ (∀ a b, δ (a * b) = a * δ b + b * δ a) ∧ (∀ r, δ (constFn Y.H.hom _ r) = constFn Y.H.hom _ (D r)) ∧ ∀ (α : Q.X) f, IsWt Y α _ f → IsWt Y α _ (δ f) := by
  first | exact @GlobalTheory.WtLift.exists_isWt_lift | exact GlobalTheory.WtLift.exists_isWt_lift | (intros; apply GlobalTheory.WtLift.exists_isWt_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationLiftRaynaudPreimageAffine
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationLiftRaynaudPreimageAffine
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LiftDer

theorem exists_lift_of_smooth (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) [Smooth f]
    (U : X.Opens) (hU : IsAffineOpen U) (D : Derivation ℤ R R) :
    ∃ δ : Γ(X, U) → Γ(X, U), (∀ a b, δ (a + b) = δ a + δ b) ∧ (∀ a b, δ (a * b) = a * δ b + b * δ a) ∧
      ∀ r, δ (constFn f U r) = constFn f U (D r) := by
  let g : R →+* Γ(X, U) :=
    (f.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  have hg : g.Smooth := by
    refine RingHom.Smooth.comp (RingHom.Smooth.of_bijective ?_) ?_
    · exact ((Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm).bijective
    · exact HasRingHomProperty.appLE @Smooth f inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _
  letI : Algebra R Γ(X, U) := g.toAlgebra
  haveI : Algebra.FormallySmooth R Γ(X, U) := hg.formallySmooth
  obtain ⟨d, hadd, hmul, hc⟩ := GlobalTheory.KS.exists_derivation_extend_of_formallySmooth R Γ(X, U) Γ(X, U)
    (RingHom.id _) (fun r => g (D r)) (fun a b => by simp) (fun a b => by
      simp only [Derivation.leibniz, smul_eq_mul, map_add (f := _), map_mul, RingHom.id_apply]
      rw [RingHom.algebraMap_toAlgebra])
  exact ⟨d, hadd, hmul, fun r => hc r⟩

theorem isAffineHom_q {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O]
    [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) : IsAffineHom Y.q.left := by
  obtain ⟨c⟩ := GlobalTheory.TorusModel.nonempty_gtCoord GlobalTheory.allSixLaws.1.globalFns Y.isGt ⊥ 0
  have hc : IsAffineHom c.q.left := c.q_affine
  let F := fstG (⊥ : Ideal R) 0 Y.H
  let j := inv F.left
  have hF : F.left ≫ Y.H.hom = (thickObj R ⊥ 0 Y.H).hom ≫ thick R ⊥ 0 := Over.w F
  let ξ := Y.Φ Y.H (𝟙 _)
  obtain ⟨x, hx⟩ := GlobalTheory.TorusCoord.exists_point c (T := Y.H) (Y.H.hom ≫ inv (thick R ⊥ 0)) (by simp) ξ
  obtain ⟨ξ', hξ'⟩ := GlobalTheory.TorusCoord.exists_isPointOf c (T := Y.H) j (by
    rw [← hF]; exact IsIso.inv_hom_id_assoc _ _)
  let b : Y.H ⟶ Y.H := (Y.Φ Y.H).symm ξ'
  have hb : Y.Φ Y.H b = ξ' := Equiv.apply_symm_apply _ _
  let a := x ≫ F.left
  have ha : a ≫ Y.H.hom = Y.H.hom := by
    rw [Category.assoc, hF]
    exact GlobalTheory.TorusCoord.IsPointOf.comp_hom c hx
  let a' : Y.H ⟶ Y.H := Over.homMk a ha
  have haj : a ≫ j = x := by simp [a, j]
  have e1 : b.left ≫ x = j := by
    have h1 : GtPt.IsPull b.left ξ (Y.Φ Y.H (b ≫ 𝟙 _)) := Y.rep.1 Y.H Y.H b (𝟙 _)
    rw [Category.comp_id, hb] at h1
    exact (GlobalTheory.TorusCoord.IsPointOf.pull c hx h1).unique_left c hξ'
  have e1' : b.left ≫ a = 𝟙 _ := by
    rw [← Category.assoc, e1]; simp [j]
  have e2 : a' ≫ b = 𝟙 _ := by
    have h2 : GtPt.IsPull a (Y.Φ Y.H b) (Y.Φ Y.H (a' ≫ b)) := Y.rep.1 Y.H Y.H a' b
    rw [hb] at h2
    have h3 := GlobalTheory.TorusCoord.IsPointOf.pull c hξ' h2
    rw [haj] at h3
    exact (Y.Φ Y.H).injective (h3.unique_right c hx)
  have e2' : a ≫ b.left = 𝟙 _ := congrArg (·.left) e2
  have : IsIso a := ⟨⟨b.left, e2', e1'⟩⟩
  have hq : Y.q.left = a ≫ j ≫ c.q.left ≫ pullback.fst Q.P.A.hom (thick R ⊥ 0) := by
    rw [← Category.assoc a j, haj, ← GlobalTheory.TorusCoord.pG_left]
    exact hx.1
  rw [hq]
  infer_instance

theorem smooth_H {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O]
    [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) : Smooth Y.H.hom := by
  have h1 : Smooth Y.q.left := Y.smooth_q
  have := Q.P.smoothDim
  have h2 : Smooth Q.P.A.hom := SmoothOfRelativeDimension.smooth Q.P.g _
  rw [← Over.w Y.q]
  infer_instance

theorem exists_lift_preimage : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.affineOpens) (D : Derivation ℤ R R), ∃ δ : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1) → Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1), (∀ a b, δ (a + b) = δ a + δ b) ∧ (∀ a b, δ (a * b) = a * δ b + b * δ a) ∧ ∀ r, δ (constFn Y.H.hom _ r) = constFn Y.H.hom _ (D r) := by
  intro R _ _ Q O _ _ _ oa Y V D
  have := isAffineHom_q Y
  have := smooth_H Y
  exact exists_lift_of_smooth R Y.H.left Y.H.hom _ (V.2.preimage Y.q.left) D

end GlobalTheory.LiftDer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationLiftRaynaudPreimageAffineStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_derivation_lift_raynaud_preimage_affine : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.affineOpens) (D : Derivation ℤ R R), ∃ δ : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1) → Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1), (∀ a b, δ (a + b) = δ a + δ b) ∧ (∀ a b, δ (a * b) = a * δ b + b * δ a) ∧ ∀ r, δ (constFn Y.H.hom _ r) = constFn Y.H.hom _ (D r) := by
  first | exact @GlobalTheory.LiftDer.exists_lift_preimage | exact GlobalTheory.LiftDer.exists_lift_preimage | (intros; apply GlobalTheory.LiftDer.exists_lift_preimage <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantLiftDerivationRaynaud
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.Heat.HxLift

theorem exists_invLift : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.affineOpens) (D : Derivation ℤ R R), ∃ d : Fld Y.H.left, IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V.1) d ∧ ∀ (α : Q.X) (V' : Q.P.A.left.Opens), V' ≤ V.1 → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d _ f) := by
  intro R _ _ Q O _ _ _ oa Y V D
  obtain ⟨δ₀, h0a, h0m, h0c⟩ := GlobalTheory.T.exists_derivation_lift_raynaud_preimage_affine R Q O oa Y V D
  obtain ⟨δ, ha, hm, hc, hw⟩ := GlobalTheory.T.exists_weight_preserving_lift_of_base_derivation R Q O oa Y V D δ₀ h0a h0m h0c
  obtain ⟨d, hd, hdU⟩ := GlobalTheory.T.exists_vectorField_extending_affineDerivation Y.H.left _ (GlobalTheory.T.isAffineOpen_preimage_projection_abelianPart R Q O oa Y V) δ ha hm
  refine ⟨d, ⟨hd, fun O' hO' r => ?_⟩, ?_⟩
  · rw [← GlobalTheory.ZH.FormSec.res_constFn Y.H.hom hO' r, ← GlobalTheory.ZH.FormSec.res_constFn Y.H.hom hO' (D r),
      hd.2.2 _ _ hO' le_rfl, hdU, hc]
  · refine GlobalTheory.T.weight_preserving_vectorField_on_smaller_preimages R Q O oa Y V d hd (fun α f hf => ?_)
    rw [hdU]
    exact hw α f hf

end GlobalTheory.Heat.HxLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantLiftDerivationRaynaudStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torusInvariant_lift_derivation_raynaud : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.affineOpens) (D : Derivation ℤ R R), ∃ d : Fld Y.H.left, IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V.1) d ∧ ∀ (α : Q.X) (V' : Q.P.A.left.Opens), V' ≤ V.1 → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d _ f) := by
  first | exact @GlobalTheory.Heat.HxLift.exists_invLift | exact GlobalTheory.Heat.HxLift.exists_invLift | (intros; apply GlobalTheory.Heat.HxLift.exists_invLift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantDerivationLiftsRaynaudCover
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

theorem GlobalTheory.HeatInvLift.exists_invLift_cover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (D : Derivation ℤ R R), ∃ (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (j : J → Dd.toPre.P.L.ι) (d : J → Fld Y.H.left), ⨆ i, V i = ⊤ ∧ (∀ i, V i ≤ Dd.toPre.P.L.U (j i)) ∧ (∀ i, IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V i) (d i)) ∧ ∀ i, (∀ (α : Dd.toPre.X) (V' : Dd.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V i → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d i _ f)) := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y D
  let J := {p : Dd.toPre.P.A.left.affineOpens × Dd.toPre.P.L.ι // p.1.1 ≤ Dd.toPre.P.L.U p.2}
  have H := fun i : J => GlobalTheory.T.exists_torusInvariant_lift_derivation_raynaud R Dd.toPre O oa Y i.1.1 D
  choose d hd using H
  refine ⟨J, fun i => i.1.1.1, fun i => i.1.2, d, ?_, fun i => i.2, fun i => (hd i).1, fun i α V' hV' f hf => ?_⟩
  · rw [eq_top_iff]
    intro x _
    have hx : x ∈ (⨆ k, Dd.toPre.P.L.U k) := by rw [Dd.toPre.P.isLB.cover]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVk⟩ :=
      Dd.toPre.P.A.left.isBasis_affineOpens.exists_subset_of_mem_open hk (Dd.toPre.P.L.U k).isOpen
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(⟨V, hV⟩, k), hVk⟩, hxV⟩
  · have e : Y.q.left ⁻¹ᵁ (V' ⊓ i.1.1.1) = Y.q.left ⁻¹ᵁ V' := by
      rw [Scheme.Hom.preimage_inf]; exact inf_eq_left.2 hV'
    have key := (hd i).2 α (V' ⊓ i.1.1.1) inf_le_right
    rw [e] at key
    exact key f hf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantDerivationLiftsRaynaudCoverStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torusInvariant_derivationLifts_raynaudCover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (D : Derivation ℤ R R), ∃ (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (j : J → Dd.toPre.P.L.ι) (d : J → Fld Y.H.left), ⨆ i, V i = ⊤ ∧ (∀ i, V i ≤ Dd.toPre.P.L.U (j i)) ∧ (∀ i, IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V i) (d i)) ∧ ∀ i, (∀ (α : Dd.toPre.X) (V' : Dd.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V i → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d i _ f)) := by
  first | exact @GlobalTheory.HeatInvLift.exists_invLift_cover | exact GlobalTheory.HeatInvLift.exists_invLift_cover | (intros; apply GlobalTheory.HeatInvLift.exists_invLift_cover <;> assumption)
end
