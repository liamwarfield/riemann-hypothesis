module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTanAtGTv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionValueInFrameLocalRingPoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointValueSectionInChartOfFrameValue
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointValueSectionInChartOfFrameValue
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatV

theorem valR_of_isValue : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (Ω : Type) [CommRing Ω] [IsLocalRing Ω] (x : Sp Ω ⟶ X) (g : GlobalTheory.RayEv.Transport.Frame L (x ≫ 𝟙 X)) (k : ℕ) (σ : SecM (𝟙 X) L k) (ω : Ω), IsValue (𝟙 X) L x g k σ ω → ∀ i, ⊤ ≤ x ⁻¹ᵁ L.U i → valR x _ (σ.f fun _ => i) = ω * (valR (𝟙 (Sp Ω)) _ (g.s fun _ => i).val) ^ k := by
  intro X L hL Ω _ _ x g k σ ω hv i hi
  set z := IsLocalRing.closedPoint Ω
  have hxz : x z ∈ L.U i := hi (show z ∈ (⊤ : (Sp Ω).Opens) from trivial)
  obtain ⟨J, hJ, hJi⟩ := exists_good L hL z (K := PUnit) (fun _ => x ≫ 𝟙 X) (fun _ => i) (fun _ _ _ => rfl)
    (fun _ => hxz)
  have h := hv (Sp Ω) (𝟙 _) z J hJ
  have e1 : J ((𝟙 (Sp Ω) ≫ x) ≫ 𝟙 X) = i := by simpa using hJi PUnit.unit
  have e2 : J (𝟙 (Sp Ω) ≫ x ≫ 𝟙 X) = i := by simpa using hJi PUnit.unit
  rw [sval_of σ (𝟙 _ ≫ x) z J (fun _ => i) (fun _ => e1), val_of g (𝟙 _) z J (fun _ => i) (fun _ => e2),
    Category.id_comp] at h
  have m1 : (𝟙 (Sp Ω)) z ∈ (⊤ : (Sp Ω).Opens) := trivial
  have a1 : valR x _ (σ.f fun _ => i) =
      (stalkClosedPointIso (CommRingCat.of Ω)).hom.hom (gs x z _ (σ.f fun _ => i)) :=
    GlobalTheory.ZH.ThetaData.valR_eq_gs x _ (Set.mem_iInter.2 fun _ => hxz) _
  have mG : (𝟙 (Sp Ω)) z ∈ LB.wchart L (fun _ : PUnit => x ≫ 𝟙 X) (fun _ => i) := Set.mem_iInter.2 fun _ => hxz
  have a2 : valR (𝟙 (Sp Ω)) _ (g.s fun _ => i).val =
      (stalkClosedPointIso (CommRingCat.of Ω)).hom.hom (gs (𝟙 (Sp Ω)) z _ (g.s fun _ => i).val) :=
    GlobalTheory.ZH.ThetaData.valR_eq_gs (𝟙 _) _ mG _
  have a3 : gs (𝟙 (Sp Ω)) z _ (g.s fun _ => i).val = (gm (𝟙 (Sp Ω)) z _ (g.s fun _ => i)).val :=
    gs_unit _ _ _ mG _
  have hω : (stalkClosedPointIso (CommRingCat.of Ω)).hom.hom (gs (𝟙 (Sp Ω)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom ω)) = ω := by
    rw [← GlobalTheory.ZH.ThetaData.valR_eq_gs (𝟙 _) ⊤ m1, GlobalTheory.ZH.CrdCalc.valR_eq _ _ le_rfl]
    simp [GlobalTheory.ZH.CrdCalc.valHom, Scheme.Hom.appLE]
  rw [a1, a2, a3]
  have h' := congrArg (stalkClosedPointIso (CommRingCat.of Ω)).hom.hom h
  rw [map_mul, hω, Units.val_pow_eq_pow_val, map_pow] at h'
  exact h'

end GlobalTheory.HeatV
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointValueSectionInChartOfFrameValueStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointValue_section_in_chart_of_frame_value : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (Ω : Type) [CommRing Ω] [IsLocalRing Ω] (x : Sp Ω ⟶ X) (g : GlobalTheory.RayEv.Transport.Frame L (x ≫ 𝟙 X)) (k : ℕ) (σ : SecM (𝟙 X) L k) (ω : Ω), IsValue (𝟙 X) L x g k σ ω → ∀ i, ⊤ ≤ x ⁻¹ᵁ L.U i → valR x _ (σ.f fun _ => i) = ω * (valR (𝟙 (Sp Ω)) _ (g.s fun _ => i).val) ^ k := by
  first | exact @GlobalTheory.HeatV.valR_of_isValue | exact GlobalTheory.HeatV.valR_of_isValue | (intros; apply GlobalTheory.HeatV.valR_of_isValue <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointValueRelationSectionsThroughGeneratingIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointValueRelationSectionsThroughGeneratingIso
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.GermVal

theorem valR_linComb_germ : ∀ (Y X₁ X₂ : Scheme.{0}) (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (k : ℕ) (σ' : SecM (𝟙 X₁) L₁ k) (s : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ)))), (∀ (y : Y) (i : L₂.ι) (j : L₁.ι), f₂ y ∈ L₂.U i → f₁ y ∈ L₁.U j → gs (𝟙 Y) y _ (s.f fun _ => i) = (gs (𝟙 Y) y _ (w.s (fun _ => i, fun _ => j)).val) ^ k * gs f₁ y _ (σ'.f fun _ => j)) → ∀ (F : Type) [CommRing F] [IsLocalRing F] (ξ : Sp F ⟶ Y) (i : L₂.ι) (j : L₁.ι), ⊤ ≤ (ξ ≫ f₂) ⁻¹ᵁ L₂.U i → ⊤ ≤ (ξ ≫ f₁) ⁻¹ᵁ L₁.U j → valR ξ _ (s.f fun _ => i) = (valR ξ _ (w.s (fun _ => i, fun _ => j)).val) ^ k * valR (ξ ≫ f₁) _ (σ'.f fun _ => j) := by
  intro Y X₁ X₂ L₁ L₂ f₁ f₂ w k σ' s H F _ _ ξ i j h2 h1
  have m2 : f₂ (ξ (IsLocalRing.closedPoint F)) ∈ L₂.U i := (GlobalTheory.ZH.CrdCalc.top_le_iff (ξ ≫ f₂) _).1 h2
  have m1 : f₁ (ξ (IsLocalRing.closedPoint F)) ∈ L₁.U j := (GlobalTheory.ZH.CrdCalc.top_le_iff (ξ ≫ f₁) _).1 h1
  have hy := H (ξ (IsLocalRing.closedPoint F)) i j m2 m1
  have a2 : ξ (IsLocalRing.closedPoint F) ∈ (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ))).U (fun _ => i) :=
    Set.mem_iInter.2 fun _ => m2
  have aw : ξ (IsLocalRing.closedPoint F) ∈
      ((L₂.pull f₂).div (L₁.pull f₁)).U (fun _ => i, fun _ => j) :=
    ⟨Set.mem_iInter.2 fun _ => m2, Set.mem_iInter.2 fun _ => m1⟩
  have a1 : f₁ (ξ (IsLocalRing.closedPoint F)) ∈ (LB.LinComb L₁ (K := Fin 1) (fun _ => 𝟙 X₁) (fun _ => (k : ℤ))).U (fun _ => j) :=
    Set.mem_iInter.2 fun _ => m1
  rw [GlobalTheory.ZH.ThetaData.valR_eq_gs ξ _ a2, GlobalTheory.ZH.ThetaData.valR_eq_gs ξ _ aw,
    GlobalTheory.ZH.ThetaData.valR_eq_gs (ξ ≫ f₁) _ a1, gs_stalkMap ξ _ _ a2, gs_stalkMap ξ _ _ aw,
    gs_comp ξ f₁ _ _ a1, hy]
  simp only [map_mul, map_pow]

end GlobalTheory.GermVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointValueRelationSectionsThroughGeneratingIsoStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointValue_relation_sections_through_generating_iso : ∀ (Y X₁ X₂ : Scheme.{0}) (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (k : ℕ) (σ' : SecM (𝟙 X₁) L₁ k) (s : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ)))), (∀ (y : Y) (i : L₂.ι) (j : L₁.ι), f₂ y ∈ L₂.U i → f₁ y ∈ L₁.U j → gs (𝟙 Y) y _ (s.f fun _ => i) = (gs (𝟙 Y) y _ (w.s (fun _ => i, fun _ => j)).val) ^ k * gs f₁ y _ (σ'.f fun _ => j)) → ∀ (F : Type) [CommRing F] [IsLocalRing F] (ξ : Sp F ⟶ Y) (i : L₂.ι) (j : L₁.ι), ⊤ ≤ (ξ ≫ f₂) ⁻¹ᵁ L₂.U i → ⊤ ≤ (ξ ≫ f₁) ⁻¹ᵁ L₁.U j → valR ξ _ (s.f fun _ => i) = (valR ξ _ (w.s (fun _ => i, fun _ => j)).val) ^ k * valR (ξ ≫ f₁) _ (σ'.f fun _ => j) := by
  first | exact @GlobalTheory.GermVal.valR_linComb_germ | exact GlobalTheory.GermVal.valR_linComb_germ | (intros; apply GlobalTheory.GermVal.valR_linComb_germ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPowerThroughGenIsoAndSchemeIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPowerThroughGenIsoAndSchemeIso
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SecThroughIso


open ReciprocityTheory.ChartRestriction.G.DVR in
theorem gs_appLE {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) {U : X.Opens} {V : Y.Opens}
    (h : V ≤ g ⁻¹ᵁ U) (hz : f z ∈ V) (x : Γ(X, U)) :
    gs f z V ((g.appLE U V h).hom x) = gs (f ≫ g) z U x := by
  have e : (g.appLE U V h).hom x = (Y.presheaf.map (homOfLE h).op).hom ((g.app U).hom x) := rfl
  rw [e, gs_res f z h hz, gs_pull f g z U (h hz)]

theorem exists_sec_of_genIso : ∀ (Y X₁ X₂ : Scheme.{0}) (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)), w.IsGen → L₁.IsLB → L₂.IsLB → ∀ (π : X₁ ⟶ Y), π ≫ f₁ = 𝟙 X₁ → f₁ ≫ π = 𝟙 Y → ∀ (k : ℕ) (s : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ)))), ∃ σ' : SecM (𝟙 X₁) L₁ k, (∀ (y : Y) (i : L₂.ι) (j : L₁.ι), f₂ y ∈ L₂.U i → f₁ y ∈ L₁.U j → gs (𝟙 Y) y _ (s.f fun _ => i) = (gs (𝟙 Y) y _ (w.s (fun _ => i, fun _ => j)).val) ^ k * gs f₁ y _ (σ'.f fun _ => j)) := by
  intro Y X₁ X₂ L₁ L₂ f₁ f₂ w hw h1 h2 π hπ hπ' k s
  let ε : Fin 1 → ℤ := fun _ => (k : ℤ)
  let u := isoInv (ReciprocityTheory.ChartRestriction.G.DVR.flatIso L₁ L₂ f₁ f₂ w ε)
  have hu : u.IsGen := isoInv_isGen (ReciprocityTheory.ChartRestriction.G.DVR.flatIso_isGen L₁ L₂ f₁ f₂ w hw ε)
  let t := ReciprocityTheory.ChartRestriction.G.DVR.secOfIso s hu (LB.isLB_linComb h1 (fun _ : Fin 1 => f₁) ε) (LB.isLB_linComb h2 (fun _ : Fin 1 => f₂) ε)
  refine ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.pullSecLC L₁ (fun _ => f₁) (fun _ => 𝟙 X₁) ε π (fun _ => hπ) t, ?_⟩
  intro y i j hy2 hy1

  have hyA : y ∈ (LB.LinComb L₁ (fun _ : Fin 1 => f₁) ε).U (fun _ => j) := Set.mem_iInter.2 fun _ => hy1
  have hyB : y ∈ (LB.LinComb L₂ (fun _ : Fin 1 => f₂) ε).U (fun _ => i) := Set.mem_iInter.2 fun _ => hy2
  have hyAB : y ∈ (LB.LinComb L₁ (fun _ : Fin 1 => f₁) ε).U (fun _ => j) ⊓ (LB.LinComb L₂ (fun _ : Fin 1 => f₂) ε).U (fun _ => i) := ⟨hyA, hyB⟩
  have hyw : y ∈ (LB.div (L₂.pull f₂) (L₁.pull f₁)).U (fun _ => i, fun _ => j) :=
    ⟨Set.mem_iInter.2 fun _ => hy2, Set.mem_iInter.2 fun _ => hy1⟩

  have s1 : gs f₁ y _ ((ReciprocityTheory.ChartRestriction.G.PullbackSections.pullSecLC L₁ (fun _ => f₁) (fun _ => 𝟙 X₁) ε π (fun _ => hπ) t).f fun _ => j) =
      gs (𝟙 Y) y _ (t.f fun _ => j) := by
    show gs f₁ y _ ((π.appLE _ _ _).hom _) = _
    rw [gs_appLE f₁ π y _ (show f₁ y ∈ _ from Set.mem_iInter.2 fun _ => by simpa using hy1), hπ']

  have s2 : gs (𝟙 Y) y _ (t.f fun _ => j) = gs (𝟙 Y) y _ (ReciprocityTheory.ChartRestriction.G.DVR.isoCand u s (fun _ => j) (fun _ => i)) := by
    rw [← ReciprocityTheory.ChartRestriction.G.DVR.secOfIso_spec s hu _ _ (fun _ => j) (fun _ => i)]
    exact (gs_res (𝟙 Y) y inf_le_left hyAB _).symm

  have s3 : gs (𝟙 Y) y _ (ReciprocityTheory.ChartRestriction.G.DVR.isoCand u s (fun _ => j) (fun _ => i)) =
      ((gm (𝟙 Y) y _ (w.s (fun _ => i, fun _ => j))) ^ (-(k : ℤ))).val * gs (𝟙 Y) y _ (s.f fun _ => i) := by
    unfold ReciprocityTheory.ChartRestriction.G.DVR.isoCand
    rw [gs_mul (𝟙 Y) y _ hyAB, gs_unit (𝟙 Y) y _ hyAB, gs_res (𝟙 Y) y inf_le_right hyAB]
    congr 2
    rw [map_inv, gm_res (𝟙 Y) y _ hyAB]
    show (gm (𝟙 Y) y _ (res _ ((ReciprocityTheory.ChartRestriction.G.DVR.flatIso L₁ L₂ f₁ f₂ w ε).s ((fun _ => j), (fun _ => i))))⁻¹)⁻¹ = _
    have hyBA : y ∈ ((LB.LinComb L₂ (fun _ : Fin 1 => f₂) ε).div (LB.LinComb L₁ (fun _ : Fin 1 => f₁) ε)).U ((fun _ => i), (fun _ => j)) := ⟨hyB, hyA⟩
    have hyAB' : y ∈ ((LB.LinComb L₁ (fun _ : Fin 1 => f₁) ε).div (LB.LinComb L₂ (fun _ : Fin 1 => f₂) ε)).U ((fun _ => j), (fun _ => i)) := hyAB
    rw [map_inv, inv_inv]
    erw [gm_res (𝟙 Y) y _ hyBA]
    show gm (𝟙 Y) y _ (∏ q : Fin 1, res (ReciprocityTheory.ChartRestriction.G.DVR.flat_le L₁ L₂ f₁ f₂ ((fun _ => j), (fun _ => i)) q) (w.s (fun _ => i, fun _ => j)) ^ (-ε q)) = _
    rw [Fin.prod_univ_one]
    erw [map_zpow, gm_res (𝟙 Y) y _ hyAB']
    rfl
  rw [s1, s2, s3, gs_unit (𝟙 Y) y _ hyw, ← _root_.mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one, _root_.one_mul]

end GlobalTheory.SecThroughIso
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPowerThroughGenIsoAndSchemeIsoStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_power_through_genIso_and_schemeIso : ∀ (Y X₁ X₂ : Scheme.{0}) (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)), w.IsGen → L₁.IsLB → L₂.IsLB → ∀ (π : X₁ ⟶ Y), π ≫ f₁ = 𝟙 X₁ → f₁ ≫ π = 𝟙 Y → ∀ (k : ℕ) (s : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ)))), ∃ σ' : SecM (𝟙 X₁) L₁ k, (∀ (y : Y) (i : L₂.ι) (j : L₁.ι), f₂ y ∈ L₂.U i → f₁ y ∈ L₁.U j → gs (𝟙 Y) y _ (s.f fun _ => i) = (gs (𝟙 Y) y _ (w.s (fun _ => i, fun _ => j)).val) ^ k * gs f₁ y _ (σ'.f fun _ => j)) := by
  first | exact @GlobalTheory.SecThroughIso.exists_sec_of_genIso | exact GlobalTheory.SecThroughIso.exists_sec_of_genIso | (intros; apply GlobalTheory.SecThroughIso.exists_sec_of_genIso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointValueOfSectionPullbackScalarMultiple
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointValueOfSectionPullbackScalarMultiple
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SecScalVal

theorem val_of_secScal : ∀ (X₂ Y : Scheme.{0}) (L₂ : LB X₂) (f₂ : Y ⟶ X₂) (k : ℕ) (σ : SecM (𝟙 X₂) L₂ k) (s : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ)))) (c : Γ(Y, ⊤)), GeneratorPullback.SecScal L₂ (fun _ : Fin 1 => f₂) (fun _ => (k : ℤ)) s (fun _ : Fin 1 => 𝟙 X₂) (fun _ => (k : ℤ)) σ f₂ c → ∀ (F : Type) [CommRing F] (ξ : Sp F ⟶ Y) (i : L₂.ι), ⊤ ≤ (ξ ≫ f₂) ⁻¹ᵁ L₂.U i → valR (ξ ≫ f₂) _ (σ.f fun _ => i) = valR ξ ⊤ c * valR ξ _ (s.f fun _ => i) := by
  intro X₂ Y L₂ f₂ k σ s c hs F _ ξ i hi
  have hc := hs (fun _ => i) (fun _ => i) (fun a b _ => by rcases a <;> rcases b <;> rfl)
  have hW : ⊤ ≤ ξ ⁻¹ᵁ (LB.wchart L₂ (fun _ : Fin 1 => f₂) (fun _ => i) ⊓
      LB.wchart L₂ (fun _ : Fin 1 => f₂ ≫ 𝟙 X₂) (fun _ => i)) := by
    intro y _
    have hy := hi (Set.mem_univ y)
    refine ⟨Set.mem_iInter.2 fun _ => ?_, Set.mem_iInter.2 fun _ => ?_⟩
    · simpa using hy
    · simpa using hy
  have hv := congrArg (valR ξ _) hc
  rw [GlobalTheory.ZH.CrdCalc.valR_mul ξ _ hW] at hv
  erw [GlobalTheory.ZH.CrdCalc.valR_res ξ _ hW, GlobalTheory.ZH.CrdCalc.valR_res ξ _ hW,
    GlobalTheory.ZH.CrdCalc.valR_res ξ _ hW] at hv
  have hσ : ⊤ ≤ ξ ⁻¹ᵁ f₂ ⁻¹ᵁ LB.wchart L₂ (fun _ : Fin 1 => 𝟙 X₂) (fun _ => i) :=
    hW.trans (ξ.preimage_mono (inf_le_right.trans
      (fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k)))
  have hσ' : ⊤ ≤ (ξ ≫ f₂) ⁻¹ᵁ LB.wchart L₂ (fun _ : Fin 1 => 𝟙 X₂) (fun _ => i) := hσ
  rw [GlobalTheory.ZH.CrdCalc.valR_eq ξ _ hσ] at hv
  exact (GlobalTheory.ZH.CrdCalc.valR_eq (ξ ≫ f₂) _ hσ' _).trans hv

end GlobalTheory.SecScalVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointValueOfSectionPullbackScalarMultipleStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointValue_of_section_pullback_scalar_multiple : ∀ (X₂ Y : Scheme.{0}) (L₂ : LB X₂) (f₂ : Y ⟶ X₂) (k : ℕ) (σ : SecM (𝟙 X₂) L₂ k) (s : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ)))) (c : Γ(Y, ⊤)), GeneratorPullback.SecScal L₂ (fun _ : Fin 1 => f₂) (fun _ => (k : ℤ)) s (fun _ : Fin 1 => 𝟙 X₂) (fun _ => (k : ℤ)) σ f₂ c → ∀ (F : Type) [CommRing F] (ξ : Sp F ⟶ Y) (i : L₂.ι), ⊤ ≤ (ξ ≫ f₂) ⁻¹ᵁ L₂.U i → valR (ξ ≫ f₂) _ (σ.f fun _ => i) = valR ξ ⊤ c * valR ξ _ (s.f fun _ => i) := by
  first | exact @GlobalTheory.SecScalVal.val_of_secScal | exact GlobalTheory.SecScalVal.val_of_secScal | (intros; apply GlobalTheory.SecScalVal.val_of_secScal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPullbackPowerBundleScalarOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPullbackPowerBundleScalarOne
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SecRestr

theorem exists_restr : ∀ (X₂ Y : Scheme.{0}) (L₂ : LB X₂) (f₂ : Y ⟶ X₂) (k : ℕ) (σ : SecM (𝟙 X₂) L₂ k), ∃ s : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ))), GeneratorPullback.SecScal L₂ (fun _ : Fin 1 => f₂) (fun _ => (k : ℤ)) s (fun _ : Fin 1 => 𝟙 X₂) (fun _ => (k : ℤ)) σ f₂ 1 := by
  intro X₂ Y L₂ f₂ k σ
  refine ⟨ReciprocityTheory.ChartRestriction.G.DVR.TG.pullSec' L₂ _ _ σ f₂ (fun _ => f₂) (fun _ => (Category.comp_id _).symm), ?_⟩
  intro j₁ j₂ hc
  have hj : j₁ = j₂ := funext fun i => by
    rw [Subsingleton.elim i 0]
    exact hc (Sum.inl 0) (Sum.inr 0) (Category.comp_id _).symm
  subst hj
  rw [ReciprocityTheory.ChartRestriction.G.DVR.TG.pullSec'_f]
  have h1 : ReciprocityTheory.ChartRestriction.G.Out.resTop (LB.wchart L₂ (fun _ : Fin 1 => f₂) j₁ ⊓
      LB.wchart L₂ (fun _ : Fin 1 => f₂ ≫ 𝟙 X₂) j₁) (1 : Γ(Y, ⊤)) = 1 := map_one _
  rw [h1, _root_.one_mul, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

end GlobalTheory.SecRestr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPullbackPowerBundleScalarOneStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_pullback_power_bundle_scalar_one : ∀ (X₂ Y : Scheme.{0}) (L₂ : LB X₂) (f₂ : Y ⟶ X₂) (k : ℕ) (σ : SecM (𝟙 X₂) L₂ k), ∃ s : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ))), GeneratorPullback.SecScal L₂ (fun _ : Fin 1 => f₂) (fun _ => (k : ℤ)) s (fun _ : Fin 1 => 𝟙 X₂) (fun _ => (k : ℤ)) σ f₂ 1 := by
  first | exact @GlobalTheory.SecRestr.exists_restr | exact GlobalTheory.SecRestr.exists_restr | (intros; apply GlobalTheory.SecRestr.exists_restr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPowerMulGlobalFunction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPowerMulGlobalFunction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SecSmul

theorem map_resTop {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (c : Γ(X, ⊤)) :
    (X.presheaf.map (homOfLE h).op).hom (resTop U c) = resTop V c := by
  simp only [resTop]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem exists_smul : ∀ (X : Scheme.{0}) (L : LB X) (k : ℕ) (σ : SecM (𝟙 X) L k) (c : Γ(X, ⊤)),
    ∃ σ'' : SecM (𝟙 X) L k, ∀ j, σ''.f j = resTop _ c * σ.f j := by
  intro X L k σ c
  refine ⟨⟨fun j => resTop _ c * σ.f j, fun i j => ?_⟩, fun j => rfl⟩
  rw [map_mul, map_mul, σ.compat i j, map_resTop, map_resTop]
  ring

end GlobalTheory.SecSmul
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPowerMulGlobalFunctionStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_power_mul_global_function : ∀ (X : Scheme.{0}) (L : LB X) (k : ℕ) (σ : SecM (𝟙 X) L k) (c : Γ(X, ⊤)), ∃ σ'' : SecM (𝟙 X) L k, ∀ j, σ''.f j = resTop _ c * σ.f j := by
  first | exact @GlobalTheory.SecSmul.exists_smul | exact GlobalTheory.SecSmul.exists_smul | (intros; apply GlobalTheory.SecSmul.exists_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPowerThroughGeneratingLineBundleIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPowerThroughGeneratingLineBundleIso
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SecThroughIso

open ReciprocityTheory.ChartRestriction.G.DVR

theorem exists_sec_of_iso : ∀ (Y X₁ X₂ : Scheme.{0}) (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂)
    (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)), w.IsGen → L₁.IsLB → L₂.IsLB → ∀ (k : ℕ) (σ' : SecM (𝟙 X₁) L₁ k),
    ∃ s : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ))),
      (∀ (y : Y) (i : L₂.ι) (j : L₁.ι), f₂ y ∈ L₂.U i → f₁ y ∈ L₁.U j →
        gs (𝟙 Y) y _ (s.f fun _ => i) = (gs (𝟙 Y) y _ (w.s (fun _ => i, fun _ => j)).val) ^ k *
          gs f₁ y _ (σ'.f fun _ => j)) := by
  intro Y X₁ X₂ L₁ L₂ f₁ f₂ w hw h₁ h₂ k σ'
  let t : LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => f₁) (fun _ => (k : ℤ))) :=
    TG.pullSec' L₁ (fun _ => 𝟙 X₁) (fun _ => (k : ℤ)) σ' f₁ (fun _ => f₁) (fun _ => (Category.comp_id _).symm)
  refine ⟨secOfIso (u := flatIso L₁ L₂ f₁ f₂ w (fun _ : Fin 1 => (k : ℤ))) t
    (flatIso_isGen L₁ L₂ f₁ f₂ w hw _) (linComb_isLB _ h₂ _ _) (linComb_isLB _ h₁ _ _), ?_⟩
  intro y i j hi hj
  have hz : (𝟙 Y) y ∈ (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ))).U (fun _ => i) ⊓
      (LB.LinComb L₁ (K := Fin 1) (fun _ => f₁) (fun _ => (k : ℤ))).U (fun _ => j) :=
    ⟨Set.mem_iInter.2 fun _ => hi, Set.mem_iInter.2 fun _ => hj⟩
  have e := ps_gs_secOfIso (flatIso L₁ L₂ f₁ f₂ w (fun _ : Fin 1 => (k : ℤ))) t
    (flatIso_isGen L₁ L₂ f₁ f₂ w hw _) (linComb_isLB _ h₂ _ _) (linComb_isLB _ h₁ _ _)
    (fun _ => i) (fun _ => j) (𝟙 Y) y hz
  have hw' : (𝟙 Y) y ∈ ((L₂.pull f₂).div (L₁.pull f₁)).U (fun _ => i, fun _ => j) :=
    ⟨Set.mem_iInter.2 fun _ => hi, Set.mem_iInter.2 fun _ => hj⟩
  have e1 : gm (𝟙 Y) y _ ((flatIso L₁ L₂ f₁ f₂ w (fun _ : Fin 1 => (k : ℤ))).s (fun _ => j, fun _ => i)) =
      gm (𝟙 Y) y _ (w.s (fun _ => i, fun _ => j)) ^ (-(k : ℤ)) := by
    show gm (𝟙 Y) y _ (∏ k' : Fin 1, res (flat_le L₁ L₂ f₁ f₂ (fun _ => j, fun _ => i) k')
      (w.s (fun _ => i, fun _ => j)) ^ (-(k : ℤ))) = _
    rw [map_prod, Fin.prod_univ_one, map_zpow]
    congr 1
    exact gm_res _ y _ (show (𝟙 Y) y ∈ LB.wchart L₁ (fun _ : Fin 1 => f₁) (fun _ => j) ⊓
      LB.wchart L₂ (fun _ : Fin 1 => f₂) (fun _ => i) from ⟨hz.2, hz.1⟩) _
  have e2 : gs (𝟙 Y) y _ (t.f fun _ => j) = gs f₁ y _ (σ'.f fun _ => j) := by
    simp only [t]
    rw [TG.pullSec'_f]
    refine (gs_res _ y _ hz.2 _).trans ?_
    refine (gs_pull (𝟙 Y) f₁ y _ (Set.mem_iInter.2 fun _ => hj) _).trans ?_
    rw [Category.id_comp]
    rfl
  rw [e, e1, e2, gs_unit _ y _ hw', zpow_neg, inv_inv, zpow_natCast, Units.val_pow_eq_pow_val]

end GlobalTheory.SecThroughIso
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPowerThroughGeneratingLineBundleIsoStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_power_through_generating_lineBundleIso : ∀ (Y X₁ X₂ : Scheme.{0}) (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)), w.IsGen → L₁.IsLB → L₂.IsLB → ∀ (k : ℕ) (σ' : SecM (𝟙 X₁) L₁ k), ∃ s : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ))), (∀ (y : Y) (i : L₂.ι) (j : L₁.ι), f₂ y ∈ L₂.U i → f₁ y ∈ L₁.U j → gs (𝟙 Y) y _ (s.f fun _ => i) = (gs (𝟙 Y) y _ (w.s (fun _ => i, fun _ => j)).val) ^ k * gs f₁ y _ (σ'.f fun _ => j)) := by
  first | exact @GlobalTheory.SecThroughIso.exists_sec_of_iso | exact GlobalTheory.SecThroughIso.exists_sec_of_iso | (intros; apply GlobalTheory.SecThroughIso.exists_sec_of_iso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationValueSpacesGenericPointDictionary
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatSym

theorem vs_iff_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R), ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dd' : Fin n → Fld t.G.left), IsAdicComplete ((maximalIdeal R).map φ) Ω → x' ≫ t.G.hom = spMap φ → (∀ a, IsInv t.G (v' a) (dd' a)) → (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) → (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∀ (ψ : FractionRing R →+* FractionRing Ω) (ξ : Sp (FractionRing Ω) ⟶ P.A.A.left), (∀ r, ψ (algebraMap R (FractionRing R) r) = algebraMap Ω (FractionRing Ω) (φ r)) → ξ ≫ P.A.A.hom = spMap ψ → ξ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) = spMap (algebraMap Ω (FractionRing Ω)) ≫ x' → (∀ O (f : Γ(P.A.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∃ (j₀ : P.A.L.ι) (q : FractionRing Ω), ⊤ ≤ ξ ⁻¹ᵁ P.A.L.U j₀ ∧ q ≠ 0 ∧ ∀ (k : ℕ) (s : FractionRing Ω), 1 ≤ k → (GlobalTheory.HeatSym.VS φ t.PP.L x' g k s ↔ ∃ σ : SecM (𝟙 P.A.A.left) P.A.L k, s = q ^ k * valR ξ _ (σ.f fun _ => j₀)) := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt gam _ _ _ n v' D Ω _ _ _ φ x' δ dd' _ hx' _ _ _ _
  rw [← P.bundle]
  intro g hg δL _ ψ ξ hψ hξA hξx _
  obtain ⟨w, hw⟩ := P.U.ext
  have hgi : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, P.U.gen.inv_hom_id]; rfl
  have hig : P.U.gen.hom.left ≫ P.U.gen.inv.left = 𝟙 _ := by
    rw [← Over.comp_left, P.U.gen.hom_inv_id]; rfl
  have hξ1 : (ξ ≫ P.U.gen.inv.left) ≫ P.U.gen.hom.left = ξ := by
    rw [Category.assoc, hgi, Category.comp_id]
  have hξ2 : (ξ ≫ P.U.gen.inv.left) ≫ pullback.fst t.G.hom (jK R) =
      spMap (algebraMap Ω (FractionRing Ω)) ≫ x' := by
    rw [Category.assoc]; exact hξx
  have chart : ∀ {A : Type} [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (L : LB Z), L.IsLB →
      ∀ (x : Sp A ⟶ Z), ∃ j, ⊤ ≤ x ⁻¹ᵁ L.U j := by
    intro A _ _ Z L hL x
    have hc : x (IsLocalRing.closedPoint A) ∈ (⨆ i, L.U i : Z.Opens) := by rw [hL.cover]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hc
    exact ⟨j, (GlobalTheory.ZH.CrdCalc.top_le_iff x _).2 hj⟩
  obtain ⟨j₀, hj₀⟩ := chart P.A.L P.A.isLB ξ
  obtain ⟨i, hi⟩ := chart P.U.LG.L P.U.LG.isLB x'
  have hiK : ⊤ ≤ ((ξ ≫ P.U.gen.inv.left) ≫ pullback.fst t.G.hom (jK R)) ⁻¹ᵁ P.U.LG.L.U i := by
    rw [hξ2]; exact fun p _ => hi (Set.mem_univ _)
  have hjK : ⊤ ≤ ((ξ ≫ P.U.gen.inv.left) ≫ P.U.gen.hom.left) ⁻¹ᵁ P.A.L.U j₀ := by
    rw [hξ1]; exact hj₀
  have hW : ⊤ ≤ (ξ ≫ P.U.gen.inv.left) ⁻¹ᵁ
      (LB.div (P.U.LG.L.pull (pullback.fst t.G.hom (jK R))) (P.A.L.pull P.U.gen.hom.left)).U
        (fun _ => i, fun _ => j₀) :=
    fun p hp => ⟨Set.mem_iInter.2 fun _ => hiK hp, Set.mem_iInter.2 fun _ => hjK hp⟩
  have hG : ⊤ ≤ (𝟙 (Sp Ω)) ⁻¹ᵁ (LB.LinComb P.U.LG.L (fun _ : PUnit => x' ≫ 𝟙 t.G.left) (fun _ => 1)).U (fun _ => i) :=
    fun p hp => Set.mem_iInter.2 fun _ => hi hp
  set e₀ : Ω := valR (𝟙 (Sp Ω)) _ (g.s fun _ => i).val with he₀
  set W : FractionRing Ω := valR (ξ ≫ P.U.gen.inv.left) _ (w.s (fun _ => i, fun _ => j₀)).val with hWdef
  have he₀u : IsUnit e₀ := by
    rw [he₀, GlobalTheory.ZH.CrdCalc.valR_eq _ _ hG]
    exact (Units.map (GlobalTheory.ZH.CrdCalc.valHom _ _ hG).toMonoidHom (g.s fun _ => i)).isUnit
  have hWu : IsUnit W := by
    rw [hWdef, GlobalTheory.ZH.CrdCalc.valR_eq _ _ hW]
    exact (Units.map (GlobalTheory.ZH.CrdCalc.valHom _ _ hW).toMonoidHom (w.s (fun _ => i, fun _ => j₀))).isUnit
  have hι0 : algebraMap Ω (FractionRing Ω) e₀ ≠ 0 := (he₀u.map _).ne_zero
  have hφne : ∀ r : R, r ≠ 0 → algebraMap Ω (FractionRing Ω) (φ r) ≠ 0 := by
    intro r hr
    rw [← hψ]
    exact (map_ne_zero ψ).2 ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr)
  refine ⟨j₀, W * (algebraMap Ω (FractionRing Ω) e₀)⁻¹, hj₀, mul_ne_zero hWu.ne_zero (inv_ne_zero hι0), ?_⟩
  intro k s hk

  have htop : ∀ {Y : Scheme.{0}} (a : Γ(Y, ⊤)), resTop (⊤ : Y.Opens) a = a := by
    intro Y a
    have e : (homOfLE le_top : (⊤ : Y.Opens) ⟶ ⊤) = 𝟙 _ := Subsingleton.elim _ _
    simp only [resTop, e, op_id, CategoryTheory.Functor.map_id]
    rfl
  have v1 := fun σ ω hv => GlobalTheory.T.pointValue_section_in_chart_of_frame_value t.G.left P.U.LG.L P.U.LG.isLB Ω x' g k σ ω hv i hi
  have v5 : ∀ σ : SecM (𝟙 t.G.left) P.U.LG.L k,
      valR ((ξ ≫ P.U.gen.inv.left) ≫ pullback.fst t.G.hom (jK R)) _ (σ.f fun _ => i) =
        algebraMap Ω (FractionRing Ω) (valR x' _ (σ.f fun _ => i)) := by
    intro σ
    rw [hξ2]
    exact (GlobalTheory.ZH.CrdCalc.valR_spMap _ x' ((LB.LinComb P.U.LG.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => (k : ℤ))).U fun _ => i) (fun p hp => Set.mem_iInter.2 fun _ => hi hp)).2 _
  have hj₀' : ⊤ ≤ ξ ⁻¹ᵁ (LB.LinComb P.A.L (K := Fin 1) (fun _ => 𝟙 P.A.A.left) (fun _ => (k : ℤ))).U (fun _ => j₀) :=
    fun p hp => Set.mem_iInter.2 fun _ => hj₀ hp
  constructor
  · rintro ⟨r, σ, ω, hr, hv, hs⟩
    obtain ⟨s₁, hs₁⟩ := GlobalTheory.T.exists_section_pullback_power_bundle_scalar_one _ _ P.U.LG.L (pullback.fst t.G.hom (jK R)) k σ
    obtain ⟨σ₀, hσ₀⟩ := GlobalTheory.T.exists_section_power_through_genIso_and_schemeIso _ _ _ P.A.L P.U.LG.L P.U.gen.hom.left (pullback.fst t.G.hom (jK R)) w hw P.A.isLB
      P.U.LG.isLB P.U.gen.inv.left hgi hig k s₁
    obtain ⟨σ', hσ'⟩ := GlobalTheory.T.exists_section_power_mul_global_function _ P.A.L k σ₀ (scal P.A.A.hom (algebraMap R (FractionRing R) r)⁻¹)
    refine ⟨σ', ?_⟩
    have e1 := v1 σ ω hv
    have e2 := GlobalTheory.T.pointValue_of_section_pullback_scalar_multiple _ _ P.U.LG.L (pullback.fst t.G.hom (jK R)) k σ s₁ 1 hs₁ (FractionRing Ω) _ i hiK
    have e3 := GlobalTheory.T.pointValue_relation_sections_through_generating_iso _ _ _ P.A.L P.U.LG.L P.U.gen.hom.left (pullback.fst t.G.hom (jK R)) w k σ₀ s₁ hσ₀
      (FractionRing Ω) (ξ ≫ P.U.gen.inv.left) i j₀ hiK hjK
    rw [hξ1] at e3
    have e4 : valR ξ _ (σ'.f fun _ => j₀) = (algebraMap Ω (FractionRing Ω) (φ r))⁻¹ * valR ξ _ (σ₀.f fun _ => j₀) := by
      erw [hσ' (fun _ => j₀)]
      rw [GlobalTheory.ZH.CrdCalc.valR_mul _ _ hj₀', GlobalTheory.ZH.FormCount.valR_scal ψ ξ _ hξA _ hj₀', map_inv₀, hψ]
    have e1' : valR (ξ ≫ P.U.gen.inv.left) ⊤ 1 = 1 := by
      rw [GlobalTheory.ZH.CrdCalc.valR_eq _ _ le_top, map_one]
    rw [v5, e1, e1', _root_.one_mul, e3] at e2
    rw [e4]
    have hr' := hφne r hr
    rw [map_mul, map_pow] at e2
    rw [_root_.mul_pow, inv_pow]
    have hk0 : algebraMap Ω (FractionRing Ω) e₀ ^ k ≠ 0 := pow_ne_zero _ hι0
    field_simp
    linear_combination (-(algebraMap Ω (FractionRing Ω) e₀ ^ k)) * hs + e2
  · rintro ⟨σ', rfl⟩
    obtain ⟨s₁, hs₁⟩ := GlobalTheory.T.exists_section_power_through_generating_lineBundleIso _ _ _ P.A.L P.U.LG.L P.U.gen.hom.left (pullback.fst t.G.hom (jK R)) w hw P.A.isLB
      P.U.LG.isLB k σ'
    obtain ⟨F, hF, -⟩ := (P.U.expand k hk).1 s₁
    obtain ⟨r, hr, σ, f, hsc, -⟩ := hF
    obtain ⟨ω, hv⟩ := GlobalTheory.HeatV.exists_isValue t.G.left P.U.LG.L P.U.LG.isLB Ω x' g hg k σ
    refine ⟨r, σ, ω, hr, hv, ?_⟩
    have e1 := v1 σ ω hv
    have e2 := GlobalTheory.T.pointValue_of_section_pullback_scalar_multiple _ _ P.U.LG.L (pullback.fst t.G.hom (jK R)) k σ s₁ _ hsc (FractionRing Ω) _ i hiK
    have e3 := GlobalTheory.T.pointValue_relation_sections_through_generating_iso _ _ _ P.A.L P.U.LG.L P.U.gen.hom.left (pullback.fst t.G.hom (jK R)) w k σ' s₁ hs₁
      (FractionRing Ω) (ξ ≫ P.U.gen.inv.left) i j₀ hiK hjK
    rw [hξ1] at e3
    have hq : (ξ ≫ P.U.gen.inv.left) ≫ pullback.snd t.G.hom (jK R) ≫ jK R =
        spMap ((algebraMap Ω (FractionRing Ω)).comp φ) := by
      rw [← pullback.condition, ← Category.assoc, hξ2, Category.assoc, hx', spMap, spMap, spMap, ← Spec.map_comp]
      rfl
    have e5 : valR (ξ ≫ P.U.gen.inv.left) ⊤ (scal (pullback.snd t.G.hom (jK R) ≫ jK R) r) =
        algebraMap Ω (FractionRing Ω) (φ r) := by
      have := GlobalTheory.ZH.FormCount.valR_scal ((algebraMap Ω (FractionRing Ω)).comp φ) (ξ ≫ P.U.gen.inv.left) _ hq ⊤ le_top r
      rw [htop] at this
      exact this
    rw [v5, e1, e5, e3] at e2
    rw [map_mul, map_pow] at e2
    rw [_root_.mul_pow, inv_pow]
    field_simp
    linear_combination e2

end GlobalTheory.HeatSym
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationValueSpacesGenericPointDictionaryStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisation_value_spaces_generic_point_dictionary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R), ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dd' : Fin n → Fld t.G.left), IsAdicComplete ((maximalIdeal R).map φ) Ω → x' ≫ t.G.hom = spMap φ → (∀ a, IsInv t.G (v' a) (dd' a)) → (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) → (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∀ (ψ : FractionRing R →+* FractionRing Ω) (ξ : Sp (FractionRing Ω) ⟶ P.A.A.left), (∀ r, ψ (algebraMap R (FractionRing R) r) = algebraMap Ω (FractionRing Ω) (φ r)) → ξ ≫ P.A.A.hom = spMap ψ → ξ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) = spMap (algebraMap Ω (FractionRing Ω)) ≫ x' → (∀ O (f : Γ(P.A.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∃ (j₀ : P.A.L.ι) (q : FractionRing Ω), ⊤ ≤ ξ ⁻¹ᵁ P.A.L.U j₀ ∧ q ≠ 0 ∧ ∀ (k : ℕ) (s : FractionRing Ω), 1 ≤ k → (GlobalTheory.HeatSym.VS φ t.PP.L x' g k s ↔ ∃ σ : SecM (𝟙 P.A.A.left) P.A.L k, s = q ^ k * valR ξ _ (σ.f fun _ => j₀)) := by
  first | exact @GlobalTheory.HeatSym.vs_iff_generic | exact GlobalTheory.HeatSym.vs_iff_generic | (intros; apply GlobalTheory.HeatSym.vs_iff_generic <;> assumption)
end
