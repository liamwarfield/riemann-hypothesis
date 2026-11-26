module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormAvgTypeOtherPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowSizesNR

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexHalfActionSplitPlaceFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexHalfActionSplitPlaceFrames
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SplitHecke GlobalTheory.LFun.ConjPlace GlobalTheory.AdelicU GlobalTheory.LFun.SplitTie

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SplitIdx


open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting in
theorem relIndex_half_act : ∀ (D : D7) (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.SplitProj D v) (ε : AE D), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsIdemOf φ ε → ∀ (BS : GL (Fin S.rank) (Fv D.host.F v)) (BT : GL (Fin T.rank) (Fv D.host.F v)), GlobalTheory.SplitHecke.Frame S ε (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) BS → GlobalTheory.SplitHecke.Frame T ε (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) BT → ∀ g : GA D T, (GlobalTheory.SplitIdx.halfLat S T ε).relIndex ((GlobalTheory.SplitIdx.halfLat S T ε).map (GlobalTheory.SplitIdx.actL S T g)) = (GlobalTheory.SplitIdx.intMat D.host.F v T.rank S.rank).relIndex ((GlobalTheory.SplitIdx.intMat D.host.F v T.rank S.rank).map (GlobalTheory.SplitIdx.mulL (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.grpCo φ T BT g).1)) := by
  intro D S T v φ ε hε BS BT hS hT g
  have hch := (GlobalTheory.SplitProjChart.chart_rdA D v φ ε hε).1
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.SplitHomLattice.mem_latO_iff_intM ε v (rdA φ) hε.1 hch S T BS BT hS hT
  have hL : ∀ V : HSp D, ((frameLat V : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E)) = L0c D V := by
    intro V
    ext x
    show V.frame.equivFun.symm x ∈ V.L0 ↔ _
    rw [Module.Basis.equivFun_symm_apply]
    rfl
  set Hf := GlobalTheory.PlaceModel.half S T ε with hHf
  set P := (grpCo φ T BT g).1 with hP
  let Ψ : WO S T →+ Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v) :=
    AddMonoidHom.mk' (fun u => c • ((BT⁻¹).1 * u.map (rdA φ) * BS.1)) (fun x y => by
      simp only [Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul, smul_add])
  have hΨ : ∀ u, Ψ u = c • ((BT⁻¹).1 * u.map (rdA φ) * BS.1) := fun _ => rfl
  have hmemH : ∀ u ∈ Hf, (u ∈ halfLat S T ε ↔ Ψ u ∈ intMat D.host.F v T.rank S.rank) := by
    intro u hu
    have hu' : IsHalf ε u := (GlobalTheory.PlaceModel.isHalf_iff S T).2 hu
    rw [halfLat, AddSubgroup.mem_inf, hL S, hL T, hΨ]
    constructor
    · rintro ⟨h, -⟩ i j
      exact GlobalTheory.SplitHecke.isInt_Ov.1 ((hc u hu').1 h i j)
    · intro h
      exact ⟨(hc u hu').2 fun i j => GlobalTheory.SplitHecke.isInt_Ov.2 (h i j), hu⟩
  have hmt1 : Formalism.L2.Theta.mt S (1 : GA D S)⁻¹ = 1 := by
    rw [inv_one]; unfold Formalism.L2.Theta.mt; rw [map_one]; rfl
  have hA : ∀ u, Ψ (actL S T g u) = P * Ψ u := by
    intro u
    change Ψ (actO S T 1 g u) = _
    rw [actO, hmt1, Matrix.mul_one, hΨ, hΨ, hP, grpCo, Matrix.mul_smul]
    congr 1
    rw [Matrix.map_mul]
    simp only [Units.val_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc BT.1, Units.mul_inv, Matrix.one_mul]
    rfl
  have hAHf : ∀ u ∈ Hf, actL S T g u ∈ Hf := by
    intro u hu
    have hu' := (GlobalTheory.PlaceModel.isHalf_iff S T).2 hu
    refine (GlobalTheory.PlaceModel.isHalf_iff S T).1 fun i j => ?_
    show ε * actO S T 1 g u i j = actO S T 1 g u i j
    rw [actO, hmt1, Matrix.mul_one, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact (mul_left_comm ε _ _).trans (congrArg (Formalism.L2.Theta.mt T g i k * ·) (hu' k j))
  let f : Hf →+ Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v) := Ψ.comp Hf.subtype
  have hbij := GlobalTheory.PlaceCoord.bijOn_map (S := S) (T := T) hch hε.1.1 hε.2.2
  have hf_inj : Function.Injective f := by
    intro x y hxy
    have hxy' : Ψ x = Ψ y := hxy
    rw [hΨ, hΨ] at hxy'
    have h1 : (BT⁻¹).1 * (x : WO S T).map (rdA φ) * BS.1 = (BT⁻¹).1 * (y : WO S T).map (rdA φ) * BS.1 :=
      smul_right_injective (Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v)) hc0 hxy'
    have h2 := congrArg (fun M => BT.1 * M * (BS⁻¹).1) h1
    simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul] at h2
    simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at h2
    exact Subtype.ext (hbij.injOn ((GlobalTheory.PlaceModel.isHalf_iff S T).2 x.2) ((GlobalTheory.PlaceModel.isHalf_iff S T).2 y.2) h2)
  have hf_surj : Function.Surjective f := by
    intro y
    obtain ⟨t, ht, ht'⟩ := GlobalTheory.PlaceCoord.exists_half hch hε.1.1 hε.2.2 (c⁻¹ • (BT.1 * y * (BS⁻¹).1))
    refine ⟨⟨t, (GlobalTheory.PlaceModel.isHalf_iff S T).1 ht⟩, ?_⟩
    change Ψ t = y
    rw [hΨ, ht', Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hc0, one_smul]
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  have hH : halfLat S T ε ≤ Hf := inf_le_right
  have hK : (halfLat S T ε).map (actL S T g) ≤ Hf := by
    rintro _ ⟨u, hu, rfl⟩
    exact hAHf u (hH hu)
  have e1 : ((halfLat S T ε).addSubgroupOf Hf).map f = intMat D.host.F v T.rank S.rank := by
    ext y
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (hmemH w w.2).1 (AddSubgroup.mem_addSubgroupOf.1 hw)
    · intro hy
      obtain ⟨w, hw⟩ := hf_surj y
      refine ⟨w, AddSubgroup.mem_addSubgroupOf.2 ((hmemH w w.2).2 ?_), hw⟩
      exact hw ▸ hy
  have e2 : (((halfLat S T ε).map (actL S T g)).addSubgroupOf Hf).map f =
      (intMat D.host.F v T.rank S.rank).map (mulL P) := by
    ext y
    rw [AddSubgroup.mem_map, AddSubgroup.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨u, hu, hw⟩ := AddSubgroup.mem_map.1 (AddSubgroup.mem_addSubgroupOf.1 hw)
      refine ⟨Ψ u, (hmemH u (hH hu)).1 hu, ?_⟩
      change P * Ψ u = Ψ (w : WO S T)
      rw [← hw, hA]
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨w, hw⟩ := hf_surj z
      have hz' : Ψ w ∈ intMat D.host.F v T.rank S.rank := hw ▸ hz
      refine ⟨⟨actL S T g w, hAHf w w.2⟩, AddSubgroup.mem_addSubgroupOf.2 ⟨w, (hmemH w w.2).2 hz', rfl⟩, ?_⟩
      change Ψ (actL S T g w) = mulL P z
      rw [hA w, ← hw]
      rfl
  rw [← AddSubgroup.relIndex_addSubgroupOf hK, ← AddSubgroup.relIndex_map_map_of_injective _ _ hf_inj, e1, e2]

end GlobalTheory.SplitIdx

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexHalfActionSplitPlaceFramesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SplitHecke GlobalTheory.LFun.ConjPlace GlobalTheory.AdelicU GlobalTheory.LFun.SplitTie

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_half_action_splitPlace_frames : ∀ (D : D7) (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.SplitProj D v) (ε : AE D), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsIdemOf φ ε → ∀ (BS : GL (Fin S.rank) (Fv D.host.F v)) (BT : GL (Fin T.rank) (Fv D.host.F v)), GlobalTheory.SplitHecke.Frame S ε (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) BS → GlobalTheory.SplitHecke.Frame T ε (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) BT → ∀ g : GA D T, (GlobalTheory.SplitIdx.halfLat S T ε).relIndex ((GlobalTheory.SplitIdx.halfLat S T ε).map (GlobalTheory.SplitIdx.actL S T g)) = (GlobalTheory.SplitIdx.intMat D.host.F v T.rank S.rank).relIndex ((GlobalTheory.SplitIdx.intMat D.host.F v T.rank S.rank).map (GlobalTheory.SplitIdx.mulL (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.grpCo φ T BT g).1)) := by
  first | exact @GlobalTheory.SplitIdx.relIndex_half_act | exact GlobalTheory.SplitIdx.relIndex_half_act | (intros; apply GlobalTheory.SplitIdx.relIndex_half_act <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SuppAtUnitaryGroupLocalToAdelicEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SuppAtUnitaryGroupLocalToAdelicEmbedding
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SplitHecke GlobalTheory.LFun.ConjPlace GlobalTheory.AdelicU GlobalTheory.LFun.SplitTie

noncomputable section

namespace GlobalTheory.SuppAtPlace

theorem suppAt_embV : ∀ (D : D7) (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → ∀ ε : AE D, Formalism.L2.NTheta.IsIdemAt ε w → ∀ g : Gv V v, SuppAt ε V (embV V v g) := by
  intro D V v w h ε he g
  have hP : IsPrimeIdem w ε (ε + cA D ε) := Or.inl ⟨he, rfl⟩
  exact (Supp.suppF_iff_of_isPrimeIdem V hP h _).2 ⟨g, rfl⟩

end GlobalTheory.SuppAtPlace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SuppAtUnitaryGroupLocalToAdelicEmbeddingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SplitHecke GlobalTheory.LFun.ConjPlace GlobalTheory.AdelicU GlobalTheory.LFun.SplitTie

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.suppAt_unitaryGroupLocalToAdelicEmbedding : ∀ (D : D7) (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → ∀ ε : AE D, Formalism.L2.NTheta.IsIdemAt ε w → ∀ g : Gv V v, SuppAt ε V (embV V v g) := by
  first | exact @GlobalTheory.SuppAtPlace.suppAt_embV | exact GlobalTheory.SuppAtPlace.suppAt_embV | (intros; apply GlobalTheory.SuppAtPlace.suppAt_embV <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexMovedHomLatticeEqProdHalvesSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexMovedHomLatticeEqProdHalvesSplitPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SplitHecke GlobalTheory.LFun.ConjPlace GlobalTheory.AdelicU GlobalTheory.LFun.SplitTie

noncomputable section

namespace GlobalTheory.SplitIdxDec

open GlobalTheory.PlaceModel GlobalTheory.FinWeilO

variable {D : D7} {S T : HSp D}

theorem smul_mem_half {e : AE D} (he : e * e = e) (x : WO S T) : e • x ∈ half S T e := by
  rw [mem_half, smul_smul, he]

theorem smul_eq_zero_of_mem_half {e f : AE D} (hef : e * f = 0) {x : WO S T} (hx : x ∈ half S T f) :
    e • x = 0 := by
  rw [← (mem_half S T).1 hx, smul_smul, hef, zero_smul]

theorem smul_add_add_WO (e : AE D) (x y z : WO S T) : e • (x + y + z) = e • x + e • y + e • z := by
  rw [smul_add, smul_add]

def proj3 (B : AddSubgroup (WO S T)) {e₁ e₂ e₃ : AE D} (h1 : e₁ * e₁ = e₁) (h2 : e₂ * e₂ = e₂)
    (h3 : e₃ * e₃ = e₃) (hB : ∀ b ∈ B, e₁ • b ∈ B ∧ e₂ • b ∈ B ∧ e₃ • b ∈ B) :
    B →+ (B ⊓ half S T e₁ : AddSubgroup (WO S T)) × (B ⊓ half S T e₂ : AddSubgroup (WO S T)) ×
      (B ⊓ half S T e₃ : AddSubgroup (WO S T)) where
  toFun b := (⟨e₁ • (b : WO S T), (hB b b.2).1, smul_mem_half h1 _⟩,
    ⟨e₂ • (b : WO S T), (hB b b.2).2.1, smul_mem_half h2 _⟩,
    ⟨e₃ • (b : WO S T), (hB b b.2).2.2, smul_mem_half h3 _⟩)
  map_zero' := Prod.ext (Subtype.ext (smul_zero _)) (Prod.ext (Subtype.ext (smul_zero _)) (Subtype.ext (smul_zero _)))
  map_add' x y := Prod.ext (Subtype.ext (smul_add _ _ _))
    (Prod.ext (Subtype.ext (smul_add _ _ _)) (Subtype.ext (smul_add _ _ _)))

theorem part_eq {e f g : AE D} {x y z : WO S T} (hx : x ∈ half S T e) (hy : y ∈ half S T f) (hz : z ∈ half S T g)
    (hef : e * f = 0) (heg : e * g = 0) : e • (x + y + z) = x := by
  rw [smul_add_add_WO, (mem_half S T).1 hx, smul_eq_zero_of_mem_half hef hy, smul_eq_zero_of_mem_half heg hz,
    add_zero, add_zero]

theorem projThreeIdempotentHalves_surjective (B : AddSubgroup (WO S T)) {e₁ e₂ e₃ : AE D} (h1 : e₁ * e₁ = e₁) (h2 : e₂ * e₂ = e₂)
    (h3 : e₃ * e₃ = e₃) (h12 : e₁ * e₂ = 0) (h13 : e₁ * e₃ = 0) (h23 : e₂ * e₃ = 0)
    (hB : ∀ b ∈ B, e₁ • b ∈ B ∧ e₂ • b ∈ B ∧ e₃ • b ∈ B) :
    Function.Surjective (proj3 B h1 h2 h3 hB) := by
  rintro ⟨⟨b₁, hb₁⟩, ⟨b₂, hb₂⟩, ⟨b₃, hb₃⟩⟩
  have h21 : e₂ * e₁ = 0 := by rw [mul_comm, h12]
  have h31 : e₃ * e₁ = 0 := by rw [mul_comm, h13]
  have h32 : e₃ * e₂ = 0 := by rw [mul_comm, h23]
  have c2 : e₂ • (b₂ + b₁ + b₃) = b₂ := part_eq hb₂.2 hb₁.2 hb₃.2 h21 h23
  have c3 : e₃ • (b₃ + b₁ + b₂) = b₃ := part_eq hb₃.2 hb₁.2 hb₂.2 h31 h32
  rw [show b₂ + b₁ + b₃ = b₁ + b₂ + b₃ by abel] at c2
  rw [show b₃ + b₁ + b₂ = b₁ + b₂ + b₃ by abel] at c3
  exact ⟨⟨b₁ + b₂ + b₃, add_mem (add_mem hb₁.1 hb₂.1) hb₃.1⟩, Prod.ext (Subtype.ext (part_eq hb₁.2 hb₂.2 hb₃.2 h12 h13))
    (Prod.ext (Subtype.ext c2) (Subtype.ext c3))⟩

theorem projThreeIdempotentHalves_apply (B : AddSubgroup (WO S T)) {e₁ e₂ e₃ : AE D} (h1 : e₁ * e₁ = e₁) (h2 : e₂ * e₂ = e₂)
    (h3 : e₃ * e₃ = e₃) (hB : ∀ b ∈ B, e₁ • b ∈ B ∧ e₂ • b ∈ B ∧ e₃ • b ∈ B) (b : B) :
    ((proj3 B h1 h2 h3 hB b).1 : WO S T) = e₁ • (b : WO S T) ∧
      ((proj3 B h1 h2 h3 hB b).2.1 : WO S T) = e₂ • (b : WO S T) ∧
      ((proj3 B h1 h2 h3 hB b).2.2 : WO S T) = e₃ • (b : WO S T) := ⟨rfl, rfl, rfl⟩

theorem relIndex_three {A B : AddSubgroup (WO S T)} {e₁ e₂ e₃ : AE D}
    (h1 : e₁ * e₁ = e₁) (h2 : e₂ * e₂ = e₂) (h3 : e₃ * e₃ = e₃)
    (h12 : e₁ * e₂ = 0) (h13 : e₁ * e₃ = 0) (h23 : e₂ * e₃ = 0) (hs : e₁ + e₂ + e₃ = 1)
    (hA : ∀ a ∈ A, e₁ • a ∈ A ∧ e₂ • a ∈ A ∧ e₃ • a ∈ A)
    (hB : ∀ b ∈ B, e₁ • b ∈ B ∧ e₂ • b ∈ B ∧ e₃ • b ∈ B) :
    A.relIndex B = (A ⊓ half S T e₁).relIndex (B ⊓ half S T e₁) *
      ((A ⊓ half S T e₂).relIndex (B ⊓ half S T e₂) * (A ⊓ half S T e₃).relIndex (B ⊓ half S T e₃)) := by
  have hcomap : A.addSubgroupOf B = (((A ⊓ half S T e₁).addSubgroupOf (B ⊓ half S T e₁)).prod
      (((A ⊓ half S T e₂).addSubgroupOf (B ⊓ half S T e₂)).prod
        ((A ⊓ half S T e₃).addSubgroupOf (B ⊓ half S T e₃)))).comap (proj3 B h1 h2 h3 hB) := by
    refine AddSubgroup.ext fun b => ?_
    obtain ⟨k₁, k₂, k₃⟩ := projThreeIdempotentHalves_apply B h1 h2 h3 hB b
    constructor
    · intro hb
      have hb' : (b : WO S T) ∈ A := AddSubgroup.mem_addSubgroupOf.1 hb
      refine AddSubgroup.mem_comap.2 (AddSubgroup.mem_prod.2 ⟨?_, AddSubgroup.mem_prod.2 ⟨?_, ?_⟩⟩)
      · refine AddSubgroup.mem_addSubgroupOf.2 (AddSubgroup.mem_inf.2 ⟨?_, ?_⟩)
        · rw [k₁]; exact (hA _ hb').1
        · rw [k₁]; exact smul_mem_half h1 _
      · refine AddSubgroup.mem_addSubgroupOf.2 (AddSubgroup.mem_inf.2 ⟨?_, ?_⟩)
        · rw [k₂]; exact (hA _ hb').2.1
        · rw [k₂]; exact smul_mem_half h2 _
      · refine AddSubgroup.mem_addSubgroupOf.2 (AddSubgroup.mem_inf.2 ⟨?_, ?_⟩)
        · rw [k₃]; exact (hA _ hb').2.2
        · rw [k₃]; exact smul_mem_half h3 _
    · intro hb
      obtain ⟨p₁, p₂⟩ := AddSubgroup.mem_prod.1 (AddSubgroup.mem_comap.1 hb)
      obtain ⟨p₂, p₃⟩ := AddSubgroup.mem_prod.1 p₂
      have a₁ := (AddSubgroup.mem_inf.1 (AddSubgroup.mem_addSubgroupOf.1 p₁)).1
      have a₂ := (AddSubgroup.mem_inf.1 (AddSubgroup.mem_addSubgroupOf.1 p₂)).1
      have a₃ := (AddSubgroup.mem_inf.1 (AddSubgroup.mem_addSubgroupOf.1 p₃)).1
      rw [k₁] at a₁
      rw [k₂] at a₂
      rw [k₃] at a₃
      refine AddSubgroup.mem_addSubgroupOf.2 ?_
      have e : (b : WO S T) = e₁ • (b : WO S T) + e₂ • (b : WO S T) + e₃ • (b : WO S T) := by
        rw [← add_smul, ← add_smul, hs, one_smul]
      rw [e]
      exact add_mem (add_mem a₁ a₂) a₃
  rw [AddSubgroup.relIndex, hcomap,
    AddSubgroup.index_comap_of_surjective _ (projThreeIdempotentHalves_surjective B h1 h2 h3 h12 h13 h23 hB), AddSubgroup.index_prod,
    AddSubgroup.index_prod]
  rfl

theorem map_inf_half {Λ : AddSubgroup (WO S T)} {φ : WO S T →+ WO S T} {e : AE D} (he : e * e = e)
    (hΛ : ∀ a ∈ Λ, e • a ∈ Λ) (hφ : ∀ x, φ (e • x) = e • φ x) :
    Λ.map φ ⊓ half S T e = (Λ ⊓ half S T e).map φ := by
  refine AddSubgroup.ext fun y => ⟨fun hy => ?_, fun hy => ?_⟩
  · obtain ⟨⟨x, hx, rfl⟩, h2⟩ := AddSubgroup.mem_inf.1 hy
    refine ⟨e • x, AddSubgroup.mem_inf.2 ⟨hΛ x hx, smul_mem_half he x⟩, ?_⟩
    rw [hφ]
    exact (mem_half S T).1 h2
  · obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨hx1, hx2⟩ := AddSubgroup.mem_inf.1 hx
    refine AddSubgroup.mem_inf.2 ⟨⟨x, hx1, rfl⟩, ?_⟩
    rw [mem_half, ← hφ, (mem_half S T).1 hx2]

theorem actL_apply (g : GA D T) (x : WO S T) : GlobalTheory.SplitIdx.actL S T g x = actO S T 1 g x := rfl

theorem actL_smul (g : GA D T) (a : AE D) (x : WO S T) :
    GlobalTheory.SplitIdx.actL S T g (a • x) = a • GlobalTheory.SplitIdx.actL S T g x := by
  rw [actL_apply, actL_apply, actO_smul]

theorem actL_of_killed {g : GA D T} {r : AE D}
    (hr : r • (Formalism.L2.Theta.mt T g - 1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) = 0) {x : WO S T}
    (hx : x ∈ half S T r) : GlobalTheory.SplitIdx.actL S T g x = x := by
  rw [actL_apply, actO, inv_one, mt_one, Matrix.mul_one]
  have h : @HMul.hMul (Matrix (Fin T.rank) (Fin T.rank) (AE D)) (Matrix (Fin T.rank) (Fin S.rank) (AE D))
      (Matrix (Fin T.rank) (Fin S.rank) (AE D)) _ (Formalism.L2.Theta.mt T g - 1) x = 0 := by
    rw [← (mem_half S T).1 hx, Matrix.mul_smul, ← Matrix.smul_mul, hr, Matrix.zero_mul]
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h
  exact h

theorem rest_idem {R : Type} [CommRing R] {e f r : R} (he : e * e = e) (hf : f * f = f) (hef : e * f = 0)
    (hr : r = 1 - e - f) :
    r * r = r ∧ e * r = 0 ∧ f * r = 0 ∧ e + f + r = 1 ∧ r * (e + f) = 0 := by
  subst hr
  refine ⟨by linear_combination he + hf + 2 * hef, by linear_combination -he - hef,
    by linear_combination -hf - hef, by ring, by linear_combination -he - hf - 2 * hef⟩

theorem kill_of_supp {g : GA D T} {r ε : AE D} (hr0 : r * (ε + cA D ε) = 0)
    (hg' : ∀ i j, (ε + cA D ε) * (Formalism.L2.Theta.mt T g - 1) i j = (Formalism.L2.Theta.mt T g - 1) i j) :
    r • (Formalism.L2.Theta.mt T g - 1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) = 0 := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, ← hg' i j, ← mul_assoc, hr0, zero_mul]

theorem split_index {Λ : AddSubgroup (WO S T)} {g : GA D T} {ε c r : AE D}
    (he : ε * ε = ε) (h2 : c * c = c) (h3 : r * r = r) (hec : ε * c = 0) (h13 : ε * r = 0) (h23 : c * r = 0)
    (hsum : ε + c + r = 1) (hkill : r • (Formalism.L2.Theta.mt T g - 1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) = 0)
    (stε : ∀ a ∈ Λ, ε • a ∈ Λ) (stc : ∀ a ∈ Λ, c • a ∈ Λ) (str : ∀ a ∈ Λ, r • a ∈ Λ) :
    Λ.relIndex (Λ.map (GlobalTheory.SplitIdx.actL S T g)) =
      (Λ ⊓ half S T ε).relIndex ((Λ ⊓ half S T ε).map (GlobalTheory.SplitIdx.actL S T g)) *
      (Λ ⊓ half S T c).relIndex ((Λ ⊓ half S T c).map (GlobalTheory.SplitIdx.actL S T g)) := by
  have stφ : ∀ (e : AE D), (∀ a ∈ Λ, e • a ∈ Λ) → ∀ b ∈ Λ.map (GlobalTheory.SplitIdx.actL S T g),
      e • b ∈ Λ.map (GlobalTheory.SplitIdx.actL S T g) := by
    rintro e hst _ ⟨a, ha, rfl⟩
    exact ⟨e • a, hst a ha, actL_smul g e a⟩
  have key := relIndex_three he h2 h3 hec h13 h23 hsum (fun a ha => ⟨stε a ha, stc a ha, str a ha⟩)
    (fun b hb => ⟨stφ ε stε b hb, stφ c stc b hb, stφ r str b hb⟩)
  rw [map_inf_half he stε (actL_smul g ε), map_inf_half h2 stc (actL_smul g c),
    map_inf_half h3 str (actL_smul g r)] at key
  have hid : (Λ ⊓ half S T r).map (GlobalTheory.SplitIdx.actL S T g) = Λ ⊓ half S T r := by
    refine AddSubgroup.ext fun y => ⟨?_, fun hy => ⟨y, hy, actL_of_killed hkill (AddSubgroup.mem_inf.1 hy).2⟩⟩
    rintro ⟨x, hx, rfl⟩
    rwa [actL_of_killed hkill (AddSubgroup.mem_inf.1 hx).2]
  rw [hid, AddSubgroup.relIndex_self, mul_one] at key
  exact key


open GlobalTheory.SplitScalar GlobalTheory.FinWeil GlobalTheory.WeilParts in
theorem idx_dec : ∀ (D : D7) (S T : HSp D) (ε : AE D), IsSplitIdem D ε → ∀ g : GA D T, SuppAt ε T g →
    GlobalTheory.FinWeil.idx (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T))
      ((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).map (GlobalTheory.FinWeilO.rhoF S T (1, g))) =
    (GlobalTheory.SplitIdx.halfLat S T ε).relIndex ((GlobalTheory.SplitIdx.halfLat S T ε).map (GlobalTheory.SplitIdx.actL S T g)) *
    (GlobalTheory.SplitIdx.halfLat S T (cA D ε)).relIndex ((GlobalTheory.SplitIdx.halfLat S T (cA D ε)).map (GlobalTheory.SplitIdx.actL S T g)) := by
  intro D S T ε hε g hg
  have hg' : ∀ i j, (ε + cA D ε) * (Formalism.L2.Theta.mt T g - 1) i j = (Formalism.L2.Theta.mt T g - 1) i j := hg
  obtain ⟨he, hec, v, ε', hv, heq⟩ := hε
  have h2 : cA D ε * cA D ε = cA D ε := by rw [← map_mul, he]
  have hs' : IsSplitIdem D (cA D ε) :=
    ⟨h2, by rw [cA_cA, mul_comm, hec], v, ε', hv, by rw [cA_cA, add_comm, heq]⟩
  have hε2 : IsSplitIdem D ε := ⟨he, hec, v, ε', hv, heq⟩
  obtain ⟨r, hr⟩ : ∃ r : AE D, r = 1 - ε - cA D ε := ⟨_, rfl⟩
  obtain ⟨h3, h13, h23, hsum, hr0⟩ := rest_idem he h2 hec hr
  have hkill : r • (Formalism.L2.Theta.mt T g - 1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) = 0 :=
    kill_of_supp hr0 hg'
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : AddSubgroup (WO S T), Λ = latO S T (frameLat S : Set (Fin S.rank → D.host.E))
    (frameLat T : Set (Fin T.rank → D.host.E)) fun _ => True := ⟨_, rfl⟩
  have hh : ∀ e, GlobalTheory.SplitIdx.halfLat S T e = Λ ⊓ half S T e := fun e => by rw [hΛ]; rfl
  have stε : ∀ a ∈ Λ, ε • a ∈ Λ := by
    rw [hΛ]
    exact fun a ha => GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ ε (GlobalTheory.SplitHomLattice.idem_int hε2) a ha
  have stc : ∀ a ∈ Λ, cA D ε • a ∈ Λ := by
    rw [hΛ]
    exact fun a ha => GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ (cA D ε) (GlobalTheory.SplitHomLattice.idem_int hs') a ha
  have str : ∀ a ∈ Λ, r • a ∈ Λ := fun a ha => by
    rw [hr, sub_smul, sub_smul, one_smul]
    exact sub_mem (sub_mem ha (stε a ha)) (stc a ha)

  have hL : GlobalTheory.FinWeil.idx (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T))
      ((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).map (GlobalTheory.FinWeilO.rhoF S T (1, g))) =
      Λ.relIndex (Λ.map (GlobalTheory.SplitIdx.actL S T g)) := by
    have e1 : (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).toAddSubgroup = Λ.comap (XF.incl S T) :=
      AddSubgroup.ext fun _ => by rw [hΛ]; exact Iff.rfl
    have e2 : ((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).map (GlobalTheory.FinWeilO.rhoF S T (1, g))).toAddSubgroup.map
        (XF.incl S T) = Λ.map (GlobalTheory.SplitIdx.actL S T g) := by
      refine AddSubgroup.ext fun u => ⟨?_, ?_⟩
      · rintro ⟨x, ⟨y, hy, rfl⟩, rfl⟩
        refine ⟨(y : WO S T), ?_, rfl⟩
        rw [hΛ]
        exact hy
      · rintro ⟨w, hw, rfl⟩
        rw [hΛ] at hw
        exact ⟨GlobalTheory.FinWeilO.rhoF S T (1, g) (XF.mk w (latO_fin hw)), ⟨XF.mk w (latO_fin hw), hw, rfl⟩, rfl⟩
    rw [GlobalTheory.FinWeil.idx, e1, AddSubgroup.relIndex_comap, e2]
  rw [hh, hh, hL]
  exact split_index he h2 h3 hec h13 h23 hsum hkill stε stc str

end GlobalTheory.SplitIdxDec

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexMovedHomLatticeEqProdHalvesSplitPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SplitHecke GlobalTheory.LFun.ConjPlace GlobalTheory.AdelicU GlobalTheory.LFun.SplitTie

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_movedHomLattice_eq_prod_halves_splitPlace : ∀ (D : D7) (S T : HSp D) (ε : AE D), IsSplitIdem D ε → ∀ g : GA D T, SuppAt ε T g → GlobalTheory.FinWeil.idx (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)) ((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).map (GlobalTheory.FinWeilO.rhoF S T (1, g))) = (GlobalTheory.SplitIdx.halfLat S T ε).relIndex ((GlobalTheory.SplitIdx.halfLat S T ε).map (GlobalTheory.SplitIdx.actL S T g)) * (GlobalTheory.SplitIdx.halfLat S T (cA D ε)).relIndex ((GlobalTheory.SplitIdx.halfLat S T (cA D ε)).map (GlobalTheory.SplitIdx.actL S T g)) := by
  first | exact @GlobalTheory.SplitIdxDec.idx_dec | exact GlobalTheory.SplitIdxDec.idx_dec | (intros; apply GlobalTheory.SplitIdxDec.idx_dec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IndexMovedHomLatticeSplitPlaceChart
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open GlobalTheory.SplitHecke GlobalTheory.LFun.ConjPlace GlobalTheory.AdelicU GlobalTheory.LFun.SplitTie

namespace GlobalTheory.SplitIdx

theorem half_index : ∀ (D : D7) (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsSplit (E := D.host.E) v → ∀ e, IsSplitChart D.sp.cm.sig T.gram (frameLat T) h e → ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ (d : Fin T.rank → ℤ) (t : GL (Fin T.rank) (w.adicCompletion D.host.E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL w (n := T.rank), ∀ k₂ ∈ KGL w (n := T.rank), ∀ ε : AE D, Formalism.L2.NTheta.IsIdemAt ε w → (halfLat S T ε).relIndex ((halfLat S T ε).map (actL S T (embV T v (e.symm (k₁ * t * k₂))))) = qV D.host.E w ^ (S.rank * (∑ i, max (-d i) 0).toNat) := by
  intro D S T v w h hs e he ϖ hϖ d t ht k₁ hk₁ k₂ hk₂ ε hε
  obtain ⟨φ, hφ, ⟨BS, hBS⟩, BT, hBT, ψ, hψ, hq, κ, hκ, hco⟩ := GlobalTheory.T.splitPlace_chart_frames_conj_maximalCompact D S T v w h hs e he ε hε
  rw [GlobalTheory.T.relIndex_half_action_splitPlace_frames D S T v φ ε hφ BS BT hBS hBT, hco, ← hq]
  have hback : ∀ x : GL (Fin T.rank) (w.adicCompletion D.host.E),
      GlobalTheory.LFun.SplitTie.glEquiv T.rank ψ
        (Matrix.GeneralLinearGroup.map (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v) x) = x := by
    intro x
    ext i j
    simp [GlobalTheory.LFun.SplitTie.glEquiv]
  have hK : ∀ x ∈ KGL w (n := T.rank),
      Matrix.GeneralLinearGroup.map (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v) x ∈ KGL v (n := T.rank) := by
    intro x hx
    rw [GlobalTheory.LFun.SplitTie.mem_KGL_iff hψ, hback]
    exact hx
  have hunif : IsUnifV D.host.F v (ψ.symm ϖ) := by
    have h1 := hψ (ψ.symm ϖ)
    rw [RingEquiv.apply_symm_apply] at h1
    show Valued.v _ = _
    rw [← h1]
    exact hϖ
  have hdiag : (Matrix.GeneralLinearGroup.map (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v) t).1 =
      Matrix.diagonal (fun i => ψ.symm ϖ ^ d i) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [ht, map_zpow₀]
    · simp [ht, Matrix.diagonal_apply, hij]
  have hsplit : ∀ a b c : GL (Fin T.rank) (w.adicCompletion D.host.E),
      κ⁻¹ * Matrix.GeneralLinearGroup.map (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v) (a * b * c) * κ =
        (κ⁻¹ * Matrix.GeneralLinearGroup.map (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v) a) *
          Matrix.GeneralLinearGroup.map (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v) b *
          (Matrix.GeneralLinearGroup.map (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v) c * κ) := by
    intro a b c
    simp only [map_mul, mul_assoc]
  rw [hsplit]
  exact GlobalTheory.T.relIndex_integralMatrices_cartanDouble_coset v T.rank S.rank (ψ.symm ϖ) hunif d _ hdiag _ (mul_mem (inv_mem hκ) (hK k₁ hk₁)) _
    (mul_mem (hK k₂ hk₂) hκ)

theorem index_moved_split : ∀ (D : D7) (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsSplit (E := D.host.E) v → ∀ e, IsSplitChart D.sp.cm.sig T.gram (frameLat T) h e → ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ (d : Fin T.rank → ℤ) (t : GL (Fin T.rank) (w.adicCompletion D.host.E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL w (n := T.rank), ∀ k₂ ∈ KGL w (n := T.rank), GlobalTheory.FinWeil.idx (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)) ((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).map (GlobalTheory.FinWeilO.rhoF S T (1, embV T v (e.symm (k₁ * t * k₂))))) = qV D.host.E w ^ (S.rank * (∑ i, |d i|).toNat) := by
  intro D S T v w h hs e he ϖ hϖ d t ht k₁ hk₁ k₂ hk₂
  obtain ⟨τ, hτ⟩ := GlobalTheory.LFun.SplitChart.exists_splitPrime_eq (GlobalTheory.AdelicU.isCMExt_host D) hs h
  obtain ⟨ε, hε, -⟩ := GlobalTheory.EmbChart.exists_isIdemAt_chart (D := D) τ
  rw [hτ] at hε
  obtain ⟨w', hne, hunder, -⟩ := GlobalTheory.LFun.SplitChart.exists_conj_place (GlobalTheory.AdelicU.isCMExt_host D) h hs
  have h' : w'.under (𝓞 D.host.F) = v := (hunder w').2 (Or.inr rfl)
  obtain ⟨c, hc, hq', -, he'⟩ := GlobalTheory.LFun.ConjPlace.exists_conj_chart (GlobalTheory.AdelicU.isCMExt_host D)
    (GlobalTheory.Mem.VolExists.isHermND D.sp.cm T) (GlobalTheory.AdelicU.SelfDual.isSelfDualAt_frameLat D T v) hne h h' he
  have hε' := GlobalTheory.T.isIdemAt_conj_of_other_prime_over_split D v w w' hne h h' ε hε
  rw [GlobalTheory.T.relIndex_movedHomLattice_eq_prod_halves_splitPlace D S T ε hε.1 _ (GlobalTheory.T.suppAt_unitaryGroupLocalToAdelicEmbedding D T v w h ε hε (e.symm (k₁ * t * k₂))),
    half_index D S T v w h hs e he ϖ hϖ d t ht k₁ hk₁ k₂ hk₂ ε hε]
  have hO := GlobalTheory.LFun.ConjPlace.map_mem_Ov_iff c hc
  have hk : ∀ k ∈ KGL w (n := T.rank), GlobalTheory.LFun.ConjPlace.invT c T.rank k ∈ KGL w' (n := T.rank) := fun k hk =>
    (GlobalTheory.LFun.ConjPlace.mem_iff_invT c hO k).1 hk
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    simp [IsUnifV] at hϖ
  have hmul : t.1 * Matrix.diagonal (fun i => ϖ ^ (-d i)) = 1 := by
    rw [ht, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← zpow_add₀ hϖ0, add_neg_cancel, zpow_zero]
  have hinv : (t⁻¹).1 = Matrix.diagonal (fun i => ϖ ^ (-d i)) := Units.inv_eq_of_mul_eq_one_right hmul
  have hdiag : (GlobalTheory.LFun.ConjPlace.invT c T.rank t).1 = Matrix.diagonal (fun i => c ϖ ^ (-d i)) := by
    ext i j
    rw [GlobalTheory.LFun.ConjPlace.invT_val, hinv]
    by_cases hij : i = j
    · subst hij
      simp [map_zpow₀]
    · simp [Matrix.diagonal_apply, hij, Ne.symm hij]
  have hunif : IsUnifV D.host.E w' (c ϖ) := by
    show Valued.v (c ϖ) = _
    rw [hc]
    exact hϖ
  have hsym : e.symm (k₁ * t * k₂) = (e.trans (GlobalTheory.LFun.ConjPlace.invT c T.rank)).symm
      (GlobalTheory.LFun.ConjPlace.invT c T.rank k₁ * GlobalTheory.LFun.ConjPlace.invT c T.rank t *
        GlobalTheory.LFun.ConjPlace.invT c T.rank k₂) := by
    rw [MulEquiv.symm_trans_apply, ← map_mul, ← map_mul, MulEquiv.symm_apply_apply]
  have hconj := half_index D S T v w' h' hs _ he' (c ϖ) hunif (fun i => -d i) _ hdiag _ (hk k₁ hk₁) _ (hk k₂ hk₂)
    (cA D ε) hε'
  rw [← hsym] at hconj
  rw [hconj, hq']
  simp only [neg_neg]
  rw [← pow_add, ← mul_add]
  have hA : 0 ≤ ∑ i, max (-d i) 0 := Finset.sum_nonneg fun i _ => le_max_right _ _
  have hB : 0 ≤ ∑ i, max (d i) 0 := Finset.sum_nonneg fun i _ => le_max_right _ _
  rw [← Int.toNat_add hA hB, ← Finset.sum_add_distrib]
  congr 3
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [add_comm]
  exact max_zero_add_max_neg_zero_eq_abs_self (d i)

end GlobalTheory.SplitIdx

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IndexMovedHomLatticeSplitPlaceChartStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.index_movedHomLattice_splitPlaceChart : ∀ (D : D7) (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsSplit (E := D.host.E) v → ∀ e, IsSplitChart D.sp.cm.sig T.gram (frameLat T) h e → ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ (d : Fin T.rank → ℤ) (t : GL (Fin T.rank) (w.adicCompletion D.host.E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL w (n := T.rank), ∀ k₂ ∈ KGL w (n := T.rank), GlobalTheory.FinWeil.idx (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)) ((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).map (GlobalTheory.FinWeilO.rhoF S T (1, embV T v (e.symm (k₁ * t * k₂))))) = qV D.host.E w ^ (S.rank * (∑ i, |d i|).toNat) := by
  first | exact @GlobalTheory.SplitIdx.index_moved_split | exact GlobalTheory.SplitIdx.index_moved_split | (intros; apply GlobalTheory.SplitIdx.index_moved_split <;> assumption)
end
