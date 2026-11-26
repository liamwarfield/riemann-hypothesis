module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchPowAlt
public import Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.IsLocCompTwistFills

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.CmpIso
noncomputable section

open NumberField IsDedekindDomain
open GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

namespace UpperTheory.Gal.InertialTypesAlt.G

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private def evalEquiv {v : Pl F} (w : PlacesOver E v) (hw : ∀ u : PlacesOver E v, u = w) :
    CompletionsOver E v ≃+* w.1.adicCompletion E :=
  letI : Unique (PlacesOver E v) := ⟨⟨w⟩, hw⟩
  RingEquiv.piUnique fun u : PlacesOver E v => u.1.adicCompletion E

private theorem evalEquiv_symm_cont {v : Pl F} (w : PlacesOver E v) (hw : ∀ u : PlacesOver E v, u = w) :
    Continuous (evalEquiv w hw).symm :=
  letI : Unique (PlacesOver E v) := ⟨⟨w⟩, hw⟩
  (Homeomorph.piUnique fun u : PlacesOver E v => u.1.adicCompletion E).symm.continuous

private def cmpEquiv (n : ℕ) {v : Pl F} (w : PlacesOver E v) (hw : ∀ u : PlacesOver E v, u = w) :
    GL (Fin n) (CompletionsOver E v) ≃ₜ* Gw n w.1 where
  toFun := GM.cmp w
  invFun := mapGL n ((evalEquiv w hw).symm : w.1.adicCompletion E →+* CompletionsOver E v)
  left_inv g := Units.ext (Matrix.ext fun _ _ => (evalEquiv w hw).symm_apply_apply _)
  right_inv g := Units.ext (Matrix.ext fun _ _ => (evalEquiv w hw).apply_symm_apply _)
  map_mul' := map_mul _
  continuous_toFun := Continuous.units_map _ (continuous_id.matrix_map (continuous_apply w))
  continuous_invFun := Continuous.units_map _ (continuous_id.matrix_map (evalEquiv_symm_cont w hw))

end

theorem cmpIso : CmpIso := by
  intro F E _ _ _ _ _ n v w hw
  refine ⟨⟨cmpEquiv n w hw, fun _ => rfl⟩, fun g => ⟨fun h => h w, fun h u => ?_⟩, fun h => funext fun g => ?_⟩
  · obtain rfl := hw u
    exact h
  · letI : Unique (PlacesOver E v) := ⟨⟨w⟩, hw⟩
    exact finprod_unique _

end UpperTheory.Gal.InertialTypesAlt.G
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.LocTw
open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open UpperTheory.Gal.InertialTypesAlt.G

theorem UpperTheory.Gal.InertialTypesAlt.G.locTw :
    UpperTheory.Gal.InertialTypesAlt.G.LocTw := by
  intro K _ _ _ n _ π χ v τ hτ
  have h' : (π.twist χ).IsLocComp v (τ.twist (CuspSub.locDet n χ v) (CuspSub.isOpen_ker_locDet χ v)) :=
    PositivityTheory.RSHS.LocalComponentTwist.isLocComp_twist π χ hτ
  refine ⟨⟨_, h'⟩, fun τ₁ h₁ => ?_⟩
  obtain ⟨e⟩ := GlobalTheory.CuspRep.LocUniq.isLocComp_unique (π.twist χ) v _ τ₁ h' h₁
  refine ⟨e.toLinearEquiv, fun g x => ?_⟩
  exact LinearMap.congr_fun (e.isIntertwining' g) x
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.NormTriv
open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC Formalism.ConjugateSelfDual UpperTheory.ConvolutionTheory.T
open scoped Classical
open UpperTheory.Gal.InertialTypesAlt.G

private theorem loc_one_of' {L : Type} [Field L] [NumberField L] (ψ : HChar L) (w : HeightOneSpectrum (𝓞 L))
    (hu : ψ.UnrAt w) (hv : ψ.val w = 1) (x : (w.adicCompletion L)ˣ) : ψ.loc w x = 1 := by
  refine GlobalTheory.FrobDense.eq_one_of_unif (ψ.loc w) (fun y hy => ?_) x
  have h2 := unif_spec w
  have h3 := hu (y * (atFin w (unif w))⁻¹) (by
    unfold IsUnitAt
    unfold IsUnifAt at hy h2
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hy, h2]
    exact mul_inv_cancel₀ WithZero.exp_ne_zero)
  rw [map_mul, map_inv, mul_inv_eq_one] at h3
  exact h3.trans hv

theorem UpperTheory.Gal.InertialTypesAlt.G.normTriv :
    UpperTheory.Gal.InertialTypesAlt.G.NormTriv := by
  intro F E _ _ _ _ _ η hη x
  let ψ : HChar E := ⟨η.1.comp (GroundTheory.Global.ideleNorm F E), η.2.1.comp GroundTheory.Global.continuous_ideleNorm, fun k =>
    (congrArg η.1 (GroundTheory.Global.ideleNorm_diagonal (K := F) k)).trans (η.2.2 _)⟩
  have hψ : ∀ x, ψ.1 x = η.1 (GroundTheory.Global.ideleNorm F E x) := fun _ => rfl
  have hev : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ψ.UnrAt w ∧ ψ.val w = 1 := by
    filter_upwards [hη.2.2, (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under F E).eventually
      (Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified η))] with w h1 h2
    have hf := GlobalTheory.ArtinTransport.normV_eq_pow (E := F) (E' := E) (v := w.under (𝓞 F)) (w := w) rfl
    obtain ⟨a, b⟩ := GlobalTheory.NormValGen.unrAt_val_of_comp_norm F E η ψ hψ w _ hf h2
    exact ⟨a, b.trans (h1 _ hf)⟩
  have h1 : ψ.1 = 1 := GlobalTheory.FrobDense.eq_one_of_away ψ.1 ψ.2.1 ψ.2.2 (Filter.eventually_cofinite.1 hev).toFinset
    fun w hw y => by
      have := not_not.1 (fun h => hw ((Set.Finite.mem_toFinset _).2 h))
      exact loc_one_of' ψ w this.1 this.2 y
  rw [← hψ, h1]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.ChiBasic
noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.G

private theorem isOpen_ker_chiAt {K : Type} [Field K] [NumberField K] (n : ℕ) (χ : HChar K) (v : Pl K) :
    IsOpen {g : Gw n v | χ.loc v (Matrix.GeneralLinearGroup.det g) = 1} := by
  have h := (isOpen_ker_finIdele K (χ.1.comp (finId K)) (χ.2.1.comp (continuous_finId K))).preimage
    ((Matrix.GeneralLinearGroup.continuous_det (n := Fin n)).comp (CuspSub.continuous_locGL (a := n) v))
  convert h using 1
  ext g
  exact Iff.of_eq (congrArg (fun u => χ.1 u = 1) (finId_det_locGL v g).symm)

private theorem isLocallyConstant_chiAt {K : Type} [Field K] [NumberField K] (n : ℕ) (χ : HChar K) (v : Pl K) :
    IsLocallyConstant (chiAt n χ v) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hc : Continuous fun y : Gw n v => x⁻¹ * y := continuous_const.mul continuous_id
  have hm : (fun y : Gw n v => x⁻¹ * y) ⁻¹' {g : Gw n v | χ.loc v (Matrix.GeneralLinearGroup.det g) = 1} ∈ nhds x :=
    ((isOpen_ker_chiAt n χ v).preimage hc).mem_nhds (by simp)
  filter_upwards [hm] with y hy
  have hy' : χ.loc v (Matrix.GeneralLinearGroup.det (x⁻¹ * y)) = 1 := hy
  rw [map_mul, map_mul, map_inv, map_inv] at hy'
  have e : χ.loc v (Matrix.GeneralLinearGroup.det y) = χ.loc v (Matrix.GeneralLinearGroup.det x) :=
    (inv_mul_eq_one.1 hy').symm
  simp only [chiAt, e]

theorem chiBasic : ChiBasic := by
  intro K _ _ n χ v
  refine ⟨isLocallyConstant_chiAt n χ v, fun g => ?_, fun f hf => ?_⟩
  · simp [chiAt, HChar.loc, ← Units.val_mul]
  · exact ⟨hf.1.mul (isLocallyConstant_chiAt n χ v), hf.2.mul_right⟩

end UpperTheory.Gal.InertialTypesAlt.G
end
end
