module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothGramSchmidtIndefiniteHermitianFrames
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnOfRapidDec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalFockIntertwinerRealPlaceOfCoverContra
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFinWeil
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEigenSysOfHeckeLin
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersRamificationLevelPlaces

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarHypothesesOfTopRows
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarHypothesesOfTopRows
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

namespace GlobalTheory.GivenOfTop

theorem given_of_top : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → HostHyp D → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → D.host.ccK = ⊤ → FWT.QGuard R.toRealDat → GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes R.toRealDat → Given R.toRealDat F.lv2 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hC hEx hH hP hc hQ hG
  exact ⟨(GlobalTheory.CoreOfWeak.core_of_weak R F hC hEx).1, hP, hOk.ok2.irr, hG, hQ, hH.gapR⟩

end GlobalTheory.GivenOfTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarHypothesesOfTopRowsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalarHypotheses_of_topRows : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → HostHyp D → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → D.host.ccK = ⊤ → FWT.QGuard R.toRealDat → GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes R.toRealDat → Given R.toRealDat F.lv2 := by
  first | exact @GlobalTheory.GivenOfTop.given_of_top | exact GlobalTheory.GivenOfTop.given_of_top | (intros; apply GlobalTheory.GivenOfTop.given_of_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSatakeLeOfUnitarySphericalGL
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSatakeLeOfUnitarySphericalGL
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.LFun.SatBoundGL

private theorem mem_adicCompletionIntegers_iff {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (x : w.adicCompletion E) :
    letI := GlobalTheory.LocalData.complRel w
    x ∈ Valuation.integer (ValuativeRel.valuation (w.adicCompletion E)) ↔ x ∈ w.adicCompletionIntegers E := by
  letI := GlobalTheory.LocalData.complRel w
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have h := ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  rw [Valuation.mem_integer_iff, HeightOneSpectrum.mem_adicCompletionIntegers]
  simpa using h x 1


open ValuativeRel in
theorem resCard_completion {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    letI := GlobalTheory.LocalData.complRel w
    haveI := GlobalTheory.LocalData.isLocalField w
    GlobalTheory.SplitWeil.resCard (w.adicCompletion E) = Ideal.absNorm w.asIdeal := by
  letI := GlobalTheory.LocalData.complRel w
  haveI := GlobalTheory.LocalData.isLocalField w

  let e : Valuation.integer (ValuativeRel.valuation (w.adicCompletion E)) ≃+* w.adicCompletionIntegers E :=
    { toFun := fun x => ⟨x.1, (mem_adicCompletionIntegers_iff w x.1).1 x.2⟩
      invFun := fun y => ⟨y.1, (mem_adicCompletionIntegers_iff w y.1).2 y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  unfold GlobalTheory.SplitWeil.resCard
  rw [Nat.card_congr (IsLocalRing.ResidueField.mapEquiv e).toEquiv, Formalism.UG.P.tjcosets_card_residue w]
  rfl

theorem norm_le_of_hasSatGL : GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound.SatakeTrivialBound → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (B : Multiset ℂˣ), GlobalTheory.LGrp.IsIrrSmooth ρ → GlobalTheory.LGrp.IsUnitarisable ρ → HasSatGL w ρ B → ∀ b ∈ B, ‖(b : ℂ)‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) := by
  intro hT E _ _ w n V _ _ ρ B hirr hun hsat b hb
  letI := GlobalTheory.LocalData.complRel w
  haveI := GlobalTheory.LocalData.isLocalField w
  obtain ⟨hsph, hvec⟩ := hsat

  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hsph
  have hG : LGrp.HasSatakeGL ρ B := GlobalTheory.LFun.SatCompare.hasSatakeGL_of_isSatVecGL hirr (hvec x hx hx0)
  obtain ⟨α, hαB, hα⟩ := (GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ ρ B).mp hG
  have hR := hT (w.adicCompletion E) n V ρ α hirr.1 hirr.2 ((GlobalTheory.LGrp.isUnitarisable_iff ρ).mp hun) ?_ hα
  · rw [← hαB] at hb
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hb
    have hi := (hR i).2
    rwa [resCard_completion] at hi
  · unfold GlobalTheory.SmGL.IsSpherical
    exact (GlobalTheory.LGrp.isSpherical_iff ρ _).mp hG.2

end GlobalTheory.LFun.SatBoundGL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSatakeLeOfUnitarySphericalGLStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_satake_le_of_unitary_spherical_GL : GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound.SatakeTrivialBound → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (B : Multiset ℂˣ), GlobalTheory.LGrp.IsIrrSmooth ρ → GlobalTheory.LGrp.IsUnitarisable ρ → HasSatGL w ρ B → ∀ b ∈ B, ‖(b : ℂ)‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) := by
  first | exact @GlobalTheory.LFun.SatBoundGL.norm_le_of_hasSatGL | exact GlobalTheory.LFun.SatBoundGL.norm_le_of_hasSatGL | (intros; apply GlobalTheory.LFun.SatBoundGL.norm_le_of_hasSatGL <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SurjectiveReductionOntoFiniteLevelGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SurjectiveReductionOntoFiniteLevelGroup
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeMatchOnto

open scoped TensorProduct
open Formalism.L2.SG.AdBridge


open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
theorem map_thetaV_eq_one (I : AutInst) (v : InfinitePlace I.F) (M : Matrix (Fin I.n) (Fin I.n) (AF I.F ⊗[I.F] I.E))
    (hM : M.map (Algebra.TensorProduct.map (fstA I.F) (AlgHom.id I.F I.E)) = 1) : M.map (thetaV I v) = 1 := by
  letI : Algebra I.F ℂ := v.embedding.toAlgebra
  let evI : Ainf I.F →ₐ[I.F] ℂ :=
    { toRingHom := (InfinitePlace.Completion.extensionEmbedding v).comp
        (Pi.evalRingHom (fun w : InfinitePlace I.F => w.Completion) v)
      commutes' := fun c => evV_algebraMap I v c }
  let φA : I.E →ₐ[I.F] ℂ := { I.φ v with commutes' := I.φ_over v }
  let θ' := Algebra.TensorProduct.lift evI φA (fun _ _ => Commute.all _ _)
  have key : ∀ z : AF I.F ⊗[I.F] I.E, thetaV I v z =
      θ' (Algebra.TensorProduct.map (fstA I.F) (AlgHom.id I.F I.E) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul a x =>
      rw [thetaV_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul]
      rfl
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
  have e : M.map (thetaV I v) = (M.map (Algebra.TensorProduct.map (fstA I.F) (AlgHom.id I.F I.E))).map θ' := by
    ext i j; simp only [Matrix.map_apply]; exact key _
  rw [e, hM]
  exact Matrix.map_one _ (map_zero θ') (map_one θ')

theorem fst_eq_one_of_bridge (I : AutInst) (e : I.GA ≃ₜ* HAd I) (hB : IsBridge I e) (x : I.GA) (z : HAd I)
    (hz : e x = z) (hx : (hmat I z).map (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA I.F) (AlgHom.id I.F I.E)) = 1) :
    x.1 = 1 := by
  funext v
  apply Subtype.ext
  apply Units.ext
  have h1 := (hB x).1 v
  have hP : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  show uMat (x.1 v) = 1
  rw [h1]
  unfold ofHAInf
  rw [hz]
  rw [map_thetaV_eq_one I v _ hx, Matrix.mul_one, Matrix.nonsing_inv_mul _ hP]

theorem iota_fst_eq_one {D : D7} (y : GA D (D.sp.Y 0)) (hy : y ∈ GfC (D.sp.Y 0)) :
    (Formalism.IndefR.RationalEmbedding.iota D y).1 = 1 := by
  refine fst_eq_one_of_bridge _ _ (Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D) _ y
    ((Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply y) ?_
  have h := congrArg (fun g : GL (Fin (D.sp.Y 0).rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E) =>
    g.val) (MonoidHom.mem_ker.1 hy)
  exact h

theorem castGA_fst {I I' : AutInst} (h : I = I') (x : I.GA) (hx : x.1 = 1) : (castGA h x).1 = 1 := by
  subst h; exact hx

theorem real_one {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (y : GA D (D.sp.Y 0)) (hy : y ∈ GfC (D.sp.Y 0)) : (iotaX X h y).1 = 1 :=
  castGA_fst h.symm _ (iota_fst_eq_one y hy)

end GlobalTheory.SeeMatchOnto

namespace GlobalTheory.SeeMatchOnto

open scoped TensorProduct
open Matrix

section Frame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem mulVec_mem_intAf (U : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (hU : ∀ i j, U i j ∈ Formalism.L2.Herm.intAf F E) (w : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)
    (hw : ∀ i, w i ∈ Formalism.L2.Herm.intAf F E) (i : Fin n) : (U *ᵥ w) i ∈ Formalism.L2.Herm.intAf F E := by
  rw [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hU i j) (hw j)

theorem mem_hatL_iff_of_St {β M : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hF : Formalism.L2.DIV.IsFrame β Λ) (hM : M ∈ Formalism.L2.DIV.St β) (x : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) :
    x ∈ Formalism.L2.Herm.hatL (F := F) Λ ↔ M.val *ᵥ x ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
  obtain ⟨u, rfl⟩ := hM
  have hint : ∀ v : GL (Fin n) (Formalism.L2.Herm.intAf F E), ∀ i j,
      (Formalism.L2.DIV.intGL F E n v).val i j ∈ Formalism.L2.Herm.intAf F E :=
    fun v i j => (v.val i j).2
  have e : (β⁻¹).val *ᵥ ((Formalism.L2.DIV.frGL β u).val *ᵥ x) =
      (Formalism.L2.DIV.intGL F E n u).val *ᵥ ((β⁻¹).val *ᵥ x) := by
    have : Formalism.L2.DIV.frGL β u = β * Formalism.L2.DIV.intGL F E n u * β⁻¹ := rfl
    rw [this, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
    congr 2
    group
  rw [hF, hF, e]
  constructor
  · intro hw i
    exact mulVec_mem_intAf _ (hint u) _ hw i
  · intro hw i
    have e2 : (β⁻¹).val *ᵥ x = (Formalism.L2.DIV.intGL F E n u⁻¹).val *ᵥ
          ((Formalism.L2.DIV.intGL F E n u).val *ᵥ ((β⁻¹).val *ᵥ x)) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
        Matrix.one_mulVec]
    rw [e2]
    exact mulVec_mem_intAf _ (hint u⁻¹) _ hw i

end Frame

end GlobalTheory.SeeMatchOnto

namespace GlobalTheory.SeeMatchOnto

open scoped TensorProduct
open Matrix Formalism.L2.SG.AdBridge

theorem ofHAFin_eq (I : AutInst) (z : HAd I) :
    ofHAFin I z = ((hmat I z).map (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA I.F) (AlgHom.id I.F I.E))).map
      (Algebra.TensorProduct.comm I.F (Formalism.MainNotions.S.Af I.F) I.E) := by
  unfold ofHAFin
  ext i j
  simp only [Matrix.map_apply]
  induction (hmat I z i j) using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [tauF_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.comm_tmul]
    rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]

theorem fmat_eq_of_bridge (I : AutInst) (e : I.GA ≃ₜ* HAd I) (hB : IsBridge I e) (x : I.GA) (z : HAd I)
    (hz : e x = z) : I.fmat x.2 =
      ((hmat I z).map (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA I.F) (AlgHom.id I.F I.E))).map
        (Algebra.TensorProduct.comm I.F (Formalism.MainNotions.S.Af I.F) I.E) := by
  rw [(hB x).2, hz, ofHAFin_eq]

theorem Lv_iff {D : D7} (z : Fin (D.sp.Y 0).rank → D.host.E) :
    z ∈ Formalism.L2.SG.InstExistsPf.Lv D ↔ z ∈ Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0 := by
  constructor
  · intro hz
    exact ⟨_, hz, (D.sp.Y 0).frame.equivFun.apply_symm_apply z⟩
  · rintro ⟨w, hw, rfl⟩
    show (D.sp.Y 0).frame.equivFun.symm ((D.sp.Y 0).frame.equivFun w) ∈ (D.sp.Y 0).L0
    simpa using hw

theorem Lf_eq {D : D7} :
    @Eq (Submodule (Formalism.MainNotions.S.IntAf (Formalism.L2.SG.InstExistsPf.instOf D).F (Formalism.L2.SG.InstExistsPf.instOf D).E)
      (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n → (Formalism.L2.SG.InstExistsPf.instOf D).E ⊗[(Formalism.L2.SG.InstExistsPf.instOf D).F]
        Formalism.MainNotions.S.Af (Formalism.L2.SG.InstExistsPf.instOf D).F))
      (Formalism.L2.SG.InstExistsPf.instOf D).Lf
      (Formalism.L2.Herm.hatL (F := D.host.F) (E := D.host.E) (Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0)) := by
  show Submodule.span _ _ = Submodule.span _ _
  congr 1
  ext w
  constructor
  · rintro ⟨⟨z, hz⟩, rfl⟩
    exact ⟨z, (Lv_iff z).1 hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, (Lv_iff z).2 hz⟩, rfl⟩

end GlobalTheory.SeeMatchOnto

namespace GlobalTheory.SeeMatchOnto

open scoped TensorProduct
open Matrix Formalism.L2.SG.AdBridge

theorem conj_mem_St {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {β a M : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hM : M ∈ Formalism.L2.DIV.St β) :
    a * M * a⁻¹ ∈ Formalism.L2.DIV.St (a * β) := by
  obtain ⟨u, rfl⟩ := hM
  refine ⟨u, ?_⟩
  show a * β * Formalism.L2.DIV.intGL F E n u * (a * β)⁻¹ = a * (β * Formalism.L2.DIV.intGL F E n u * β⁻¹) * a⁻¹
  group

theorem iota_snd_mem_Kset {D : D7} (β : GL (Fin (D.sp.Y 0).rank) (EAf D))
    (hF : Formalism.L2.DIV.IsFrame β (Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0)) (y : GA D (D.sp.Y 0))
    (hy : finE (D.sp.Y 0) y ∈ Formalism.L2.DIV.St β) :
    (Formalism.IndefR.RationalEmbedding.iota D y).2 ∈ (Formalism.IndefR.RationalEmbedding.inst D).Kset := by
  have hfm := fmat_eq_of_bridge _ _ (Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D) (Formalism.IndefR.RationalEmbedding.iota D y) y
    ((Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply y)
  intro x
  show x ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf ↔
    ((Formalism.L2.SG.InstExistsPf.instOf D).fmat (Formalism.IndefR.RationalEmbedding.iota D y).2) *ᵥ x ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf
  rw [hfm, Lf_eq]
  exact mem_hatL_iff_of_St hF hy x

theorem castGA_snd_Kset {I I' : AutInst} (h : I = I') (x : I.GA) (hx : x.2 ∈ I.Kset) : (castGA h x).2 ∈ I'.Kset := by
  subst h; exact hx

end GlobalTheory.SeeMatchOnto

namespace GlobalTheory.SeeMatchOnto

theorem onto : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (t : GA D (Yc D 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧ (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)) → IdempotentRealFixed D → t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ γ : G0g D.nd, ∃ k ∈ X.B.I.Kset, cG (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k))) = γ := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hLev hGrp hMod cG t hιE hpin hE0 ht hConj hFrame γ
  obtain ⟨κ, hκf, hκp, hκr⟩ := GlobalTheory.LevelRowsObj.liftsExist hLev (cG.symm γ)
  set y : GA D (Yc D 0) := t * κ * t⁻¹ with hydef
  have hy : y ∈ GfC (Yc D 0) := (GfC _).mul_mem ((GfC _).mul_mem ht hκf) ((GfC _).inv_mem ht)
  have h1 := real_one X h y hy
  have hy' : (iotaX X h).symm (1, (iotaX X h y).2) = y := by
    rw [← h1]; exact (iotaX X h).symm_apply_apply y
  refine ⟨(iotaX X h y).2, ?_, ?_⟩
  · have hS : finE (Yc D 0) y ∈ Formalism.L2.DIV.St (finE (Yc D 0) t * R.βY 0) := by
      rw [hydef, map_mul, map_mul, map_inv]
      exact conj_mem_St (Formalism.L2.DIV.parLev_St hκp)
    exact castGA_snd_Kset h.symm _ (iota_snd_mem_Kset _ hFrame y hS)
  · have hk : kap X h t (iotaX X h y).2 = κ := by
      unfold kap
      rw [hy']
      show (t⁻¹ * (t * κ * t⁻¹) * t : GA D (Yc D 0)) = κ
      group
    rw [hk, hκr, MulEquiv.apply_symm_apply]

end GlobalTheory.SeeMatchOnto
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SurjectiveReductionOntoFiniteLevelGroupStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_reduction_onto_finiteLevelGroup : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (t : GA D (Yc D 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧ (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)) → IdempotentRealFixed D → t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ γ : G0g D.nd, ∃ k ∈ X.B.I.Kset, cG (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k))) = γ := by
  first | exact @GlobalTheory.SeeMatchOnto.onto | exact GlobalTheory.SeeMatchOnto.onto | (intros; apply GlobalTheory.SeeMatchOnto.onto <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftIntegOfCuspRapidDecay
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.Chain.LiftConv

theorem liftInteg_of_cuspRapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, GlobalTheory.Chain.LiftInteg D :=
  fun hP D => liftInteg_of_growth hP D (GlobalTheory.T.thetaKernel_moderateGrowth_with_seminorms D)

end GlobalTheory.Chain.LiftConv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelPlacesNotIsConjPlaceRealDat
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelPlacesNotIsConjPlaceRealDat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeConjPlaces

theorem pg_not_isConjPl : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.IsGrp F → ∀ PP ∈ R.Pg, ∀ PP' ∈ R.Pg, ¬ IsConjPl (D := D) PP PP' := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL _ PP hP PP' hP'
  exact GlobalTheory.TypePlaces.not_isConjPl R.C.P R.Pg hL.Pg PP hP PP' hP'

end GlobalTheory.SeeConjPlaces
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelPlacesNotIsConjPlaceRealDatStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelPlaces_not_isConjPlace_realDat : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.IsGrp F → ∀ PP ∈ R.Pg, ∀ PP' ∈ R.Pg, ¬ IsConjPl (D := D) PP PP' := by
  first | exact @GlobalTheory.SeeConjPlaces.pg_not_isConjPl | exact GlobalTheory.SeeConjPlaces.pg_not_isConjPl | (intros; apply GlobalTheory.SeeConjPlaces.pg_not_isConjPl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelSubgroupConjFiniteMovesFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelSubgroupConjFiniteMovesFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.FrameConj

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem conj_mem_iff {G : Type} [Group G] (H : Subgroup G) {T : G} (hT : T ∈ H) (x : G) :
    T * x * T⁻¹ ∈ H ↔ x ∈ H := by
  rw [Subgroup.mul_mem_cancel_right H (H.inv_mem hT), Subgroup.mul_mem_cancel_left H hT]

theorem frGL_mul_left (T β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (y) :
    frGL (T * β) y = T * frGL β y * T⁻¹ := by
  simp only [frGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

theorem conj_mem_St_iff (T β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    T * x * T⁻¹ ∈ St (T * β) ↔ x ∈ St β := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    rw [frGL_mul_left] at hy
    exact mul_left_cancel (mul_right_cancel hy)
  · rintro ⟨y, rfl⟩
    exact ⟨y, frGL_mul_left T β y⟩

theorem redFn_conj (T β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (PP : Pl E) :
    redFn (T * β) PP (T * x * T⁻¹) = redFn β PP x := by
  by_cases hx : x ∈ St β
  · obtain ⟨y, rfl⟩ := hx
    rw [← frGL_mul_left, redFn_frGL, redFn_frGL]
  · have h' : T * x * T⁻¹ ∉ St (T * β) := fun h => hx ((conj_mem_St_iff T β x).1 h)
    unfold redFn ext1
    rw [dite_eq_right hx, dite_eq_right h']

variable {LL : Type} [CommRing LL]

theorem rTup_conj (T β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (L : LevDat E LL n) :
    rTup (T * β) L (T * x * T⁻¹) = rTup β L x := by
  funext PP
  show upperLeftBlock L.hr (redFn (T * β) PP.1 (T * x * T⁻¹)) = upperLeftBlock L.hr (redFn β PP.1 x)
  rw [redFn_conj]

theorem levFn_conj (T β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (L : LevDat E LL n) :
    levFn (T * β) L (T * x * T⁻¹) = levFn β L x := by
  unfold levFn
  simp only [rTup_conj, redFn_conj]

theorem conj_mem_lev_iff [StarRing E] {hc : CMData F E} {J : Matrix (Fin n) (Fin n) E}
    {T : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hT : T ∈ UA hc J) (β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (L : LevDat E LL n) : T * x * T⁻¹ ∈ lev hc J (T * β) L ↔ x ∈ lev hc J β L := by
  rw [mem_lev, mem_lev, mem_parLev, mem_parLev, conj_mem_iff _ hT, conj_mem_St_iff, rTup_conj]
  simp only [redFn_conj]

end Gen

theorem levS_conj_frame : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : LevDat D.host.E ℂ V.rank) (t : GA D V),
    t ∈ GfC V → ∀ k : GA D V, (k ∈ levS V β L ↔ t * k * t⁻¹ ∈ levS V (finE V t * β) L) ∧
      levChi V (finE V t * β) L (t * k * t⁻¹) = levChi V β L k := by
  intro D V β L t ht k
  have hfin : finE V (t * k * t⁻¹) = finE V t * finE V k * (finE V t)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
  refine ⟨?_, ?_⟩
  · show k ∈ levG V β L ↔ t * k * t⁻¹ ∈ levG V (finE V t * β) L
    simp only [levG, levA, Subgroup.mem_inf, Subgroup.mem_comap]
    rw [conj_mem_iff _ ht, hfin, conj_mem_lev_iff (GlobalTheory.LevSplit.finE_mem_UA V t)]
  · unfold levChi
    rw [hfin, levFn_conj]

end GlobalTheory.FrameConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelSubgroupConjFiniteMovesFrameStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelSubgroup_conj_finite_moves_frame : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : LevDat D.host.E ℂ V.rank) (t : GA D V), t ∈ GfC V → ∀ k : GA D V, (k ∈ levS V β L ↔ t * k * t⁻¹ ∈ levS V (finE V t * β) L) ∧ levChi V (finE V t * β) L (t * k * t⁻¹) = levChi V β L k := by
  first | exact @GlobalTheory.FrameConj.levS_conj_frame | exact GlobalTheory.FrameConj.levS_conj_frame | (intros; apply GlobalTheory.FrameConj.levS_conj_frame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThPDatumEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftLevel

variable {D : D7}

def thPDatum (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (e : AE D) : WO S T → ℂ :=
  fun x => if IsHalf (cA D e) x ∧ IsIntM (frMapAdj S T βS βT x) then
    omegaK Pg (fun PP => redM PP (frMapAdj S T βS βT x)) *
      omegaQ Q T.rank ξ (-1) (fun PP => redM PP (frMapAdj S T βS βT x))
    else 0

def indL {S T : HSp D} (L : AddSubgroup (WO S T)) : WO S T → ℂ := fun x => if x ∈ L then 1 else 0

def partAt {S T : HSp D} (a : AE D) (w : WO S T) : WO S T := w.map fun z => a * z

abbrev LvCls {S T : HSp D} (C : Ctx S T) (Lv : GlobalTheory.SW.Level C.X) : Type :=
  tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI Lv.𝔪) • C.X.Λ) ⧸
    (tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI Lv.𝔪 * Lv.𝔪) • C.X.Λ)).addSubgroupOf _

end GlobalTheory.LiftLevel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicIdentificationRespectsRealFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicIdentificationRespectsRealFinite
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.IotaReal

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
theorem thetaV_eq_gen (I : Formalism.MainNotions.S.AutInst) (v : InfinitePlace I.F) (θ' : Ainf I.F ⊗[I.F] I.E →+* ℂ)
    (hθ' : Formalism.MainNotions.StandardLattice.IsInfEmb (I.φ v) θ') (y : AF I.F ⊗[I.F] I.E) :
    Formalism.L2.SG.AdBridge.thetaV I v y = θ' (Algebra.TensorProduct.map (fstA I.F) (AlgHom.id I.F I.E) y) := by
  have hb : ∀ b : Ainf I.F,
      InfinitePlace.Completion.extensionEmbedding v (b v) = θ' (b ⊗ₜ[I.F] (1 : I.E)) := by
    intro b
    have hc : Continuous fun b : Ainf I.F => InfinitePlace.Completion.extensionEmbedding v (b v) :=
      (InfinitePlace.Completion.isometry_extensionEmbedding v).continuous.comp (continuous_apply v)
    refine congrFun ((InfiniteAdeleRing.denseRange_algebraMap I.F).equalizer hc hθ'.2 (funext fun x => ?_)) b
    show InfinitePlace.Completion.extensionEmbedding v (algebraMap I.F (Ainf I.F) x v) =
      θ' ((algebraMap I.F (Ainf I.F) x) ⊗ₜ[I.F] (1 : I.E))
    rw [Algebra.TensorProduct.tmul_one_eq_one_tmul x, hθ'.1, I.φ_over]
    exact Formalism.L2.SG.AdBridge.evV_algebraMap I v x
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [Formalism.L2.SG.AdBridge.thetaV_tmul, Algebra.TensorProduct.map_tmul]
    have e : (fstA I.F a) ⊗ₜ[I.F] ((AlgHom.id I.F I.E) x) =
        ((fstA I.F a) ⊗ₜ[I.F] (1 : I.E)) * ((1 : Ainf I.F) ⊗ₜ[I.F] x) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]; rfl
    rw [e, map_mul, hθ'.1, ← hb]
    rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
theorem map_thetaV_gen (I : Formalism.MainNotions.S.AutInst) (v : InfinitePlace I.F) (θ' : Ainf I.F ⊗[I.F] I.E →+* ℂ)
    (hθ' : Formalism.MainNotions.StandardLattice.IsInfEmb (I.φ v) θ') (k : Formalism.L2.SG.AdBridge.HAd I) :
    (Formalism.L2.SG.AdBridge.hmat I k).map (Formalism.L2.SG.AdBridge.thetaV I v) = Formalism.MainNotions.StandardLattice.infMat I.cm.sig I.J θ' k := by
  ext i j
  exact thetaV_eq_gen I v θ' hθ' _

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
theorem tauF_eq_comm (I : Formalism.MainNotions.S.AutInst) (y : AF I.F ⊗[I.F] I.E) :
    Formalism.L2.SG.AdBridge.tauF I y = Algebra.TensorProduct.comm I.F (Formalism.MainNotions.S.Af I.F) I.E
      (Algebra.TensorProduct.map (sndA I.F) (AlgHom.id I.F I.E) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [Formalism.L2.SG.AdBridge.tauF_tmul]
    rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
theorem ofHAFin_eq_one (I : Formalism.MainNotions.S.AutInst) (k : Formalism.L2.SG.AdBridge.HAd I)
    (h : (Formalism.L2.SG.AdBridge.hmat I k).map (Algebra.TensorProduct.map (sndA I.F) (AlgHom.id I.F I.E)) = 1) :
    Formalism.L2.SG.AdBridge.ofHAFin I k = 1 := by
  ext i j
  have e := congrFun (congrFun h i) j
  simp only [Matrix.map_apply] at e
  simp only [Formalism.L2.SG.AdBridge.ofHAFin, Matrix.map_apply, tauF_eq_comm, e, Matrix.one_apply]
  split_ifs <;> simp

theorem infMat_of_mem_GfC {D : D7} (k : GA D (D.sp.Y 0)) (hk : k ∈ GfC (D.sp.Y 0))
    (θ' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) :
    Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig (D.sp.Y 0).gram θ' k = 1 := by
  have e : (infHom (D.sp.Y 0) k).val = 1 := by
    rw [show infHom (D.sp.Y 0) k = 1 from hk]; rfl
  ext i j
  have e2 := congrFun (congrFun e i) j
  unfold Formalism.MainNotions.StandardLattice.infMat
  rw [Matrix.map_apply, Matrix.map_apply]
  refine (congrArg θ' e2).trans ?_
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem mem_GfC_of_infMat {D : D7} (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (hθ : IsInfFam θ) (k : GA D (D.sp.Y 0))
    (hk : ∀ τ, Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig (D.sp.Y 0).gram (θ τ) k = 1) : k ∈ GfC (D.sp.Y 0) := by
  classical
  let Ψ : Finset (D.host.E →+* ℂ) := Finset.univ.filter fun σ => ∃ ρ, tauE D ρ = σ
  have hmem : ∀ σ, σ ∈ Ψ ↔ ∃ ρ, tauE D ρ = σ := fun σ => by simp [Ψ]
  choose r hr using fun σ : Ψ => (hmem σ.1).1 σ.2
  obtain ⟨h1, -⟩ := (GlobalTheory.UnitaryGlue.adelic_glue D (D.sp.Y 0)).2 Ψ (fun σ => θ (r σ))
    (fun σ => by rw [hmem, hmem]; exact GlobalTheory.PointAtPlace.tauE_cm σ) (fun σ => by rw [← hr σ]; exact hθ _)
  exact h1 k fun σ => hk (r σ)

theorem conj_eq_iff {n : ℕ} (P M N : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P) :
    P⁻¹ * M * P = N ↔ M = P * N * P⁻¹ := by
  have hd := (Matrix.isUnit_iff_isUnit_det P).1 hP
  constructor
  · rintro rfl
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hd]
  · rintro rfl
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.mul_one, Matrix.nonsing_inv_mul_cancel_left _ _ hd]

theorem isAtTau_atTau {D : D7} (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (hθ : IsInfFam θ) (τ : D.what₂.Tau) (g : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ)
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ)) : IsAtTau θ (D.sp.Y 0) τ g (atTau θ (D.sp.Y 0) τ g) := by
  have hu := GlobalTheory.PointAtPlace.existsUnique_isAtTau (D.sp.Y 0) τ θ hθ g hg
  unfold atTau
  rw [dite_eq_left hu.exists]
  exact hu.exists.choose_spec

theorem iota_real_finite_of_eq {D : D7} (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ)
    (I : Formalism.MainNotions.S.AutInst) (h : I = Formalism.L2.SG.InstExistsPf.instOf D)
    (ιE : I.E ≃+* D.host.E) (pl : InfinitePlace I.F ≃ D.what₂.Tau)
    (hφ : ∀ v (x : I.E), I.φ v x = embS D (pl v) (ιE x)) (hι : ∀ x : I.E, HEq (ιE x) x) :
    let ι := (Formalism.IndefR.RationalEmbedding.iota D).trans (Formalism.L2.SG.RowsJoinPinned.castGA h.symm)
    (∀ k : GA D (D.sp.Y 0), k ∈ GfC (D.sp.Y 0) ↔ (ι k).1 = 1) ∧ (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), (ι (atTau θ (D.sp.Y 0) τ g)).2 = 1 ∧ (∀ v, v ≠ pl.symm τ → (ι (atTau θ (D.sp.Y 0) τ g)).1 v = 1) ∧ HEq (uMat ((ι (atTau θ (D.sp.Y 0) τ g)).1 (pl.symm τ))) ((fun Pm : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ => Pm⁻¹ * g * Pm) ((Formalism.L2.SG.InstExistsPf.instOf D).P (Formalism.L2.Host.tauPl D τ)))) ∧ ∀ τ (y : Formalism.REAL.UJ (I.ε (pl.symm τ))), ∃ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), (ι (atTau θ (D.sp.Y 0) τ g)).1 (pl.symm τ) = y := by
  intro ι
  subst h
  have hι' : ∀ x, ιE x = x := fun x => eq_of_heq (hι x)
  have hpl : pl = (Formalism.L2.Host.tauPl D).symm := by
    ext v
    have e1 : embS D (pl v) = embS D ((Formalism.L2.Host.tauPl D).symm v) := by
      ext x
      exact (congrArg (embS D (pl v)) (hι' x).symm).trans (hφ v x).symm
    exact GlobalTheory.PointAtPlace.tauE_injective e1
  subst hpl
  have key : ∀ k, (∀ v, Formalism.MainNotions.S.uMat ((ι k).1 v) = Formalism.L2.SG.AdBridge.ofHAInf (Formalism.L2.SG.InstExistsPf.instOf D) k v) ∧ (Formalism.L2.SG.InstExistsPf.instOf D).fmat (ι k).2 = Formalism.L2.SG.AdBridge.ofHAFin _ k := by
    intro k
    have := Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D (Formalism.IndefR.RationalEmbedding.iota D k)
    have e := (Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply k
    exact ⟨fun v => (this.1 v).trans (congrArg (fun z => Formalism.L2.SG.AdBridge.ofHAInf (Formalism.IndefR.RationalEmbedding.inst D) z v) e),
      this.2.trans (congrArg (Formalism.L2.SG.AdBridge.ofHAFin (Formalism.IndefR.RationalEmbedding.inst D)) e)⟩
  have hinf : ∀ k v, Formalism.MainNotions.S.uMat ((ι k).1 v) = ((Formalism.L2.SG.InstExistsPf.instOf D).P v)⁻¹ *
      Formalism.MainNotions.StandardLattice.infMat (Formalism.L2.SG.InstExistsPf.instOf D).cm.sig (Formalism.L2.SG.InstExistsPf.instOf D).J (θ ((Formalism.L2.Host.tauPl D).symm v)) k *
      (Formalism.L2.SG.InstExistsPf.instOf D).P v := fun k v =>
    ((key k).1 v).trans (congrArg (fun M => ((Formalism.L2.SG.InstExistsPf.instOf D).P v)⁻¹ * M * (Formalism.L2.SG.InstExistsPf.instOf D).P v)
      (map_thetaV_gen (Formalism.L2.SG.InstExistsPf.instOf D) v (θ ((Formalism.L2.Host.tauPl D).symm v)) (hθ _) k))
  have hPu := (Formalism.L2.SG.InstExistsPf.instOf D).P_unit

  have hd : ∀ v, IsUnit ((Formalism.L2.SG.InstExistsPf.instOf D).P v).det := fun v =>
    (Matrix.isUnit_iff_isUnit_det _).1 (hPu v)
  refine ⟨fun k => ⟨fun hk => ?_, fun hk => ?_⟩, ?_, ?_⟩
  · funext v
    apply Subtype.ext
    apply Units.ext
    show Formalism.MainNotions.S.uMat ((ι k).1 v) = 1
    rw [hinf k v]
    have e : Formalism.MainNotions.StandardLattice.infMat (Formalism.L2.SG.InstExistsPf.instOf D).cm.sig (Formalism.L2.SG.InstExistsPf.instOf D).J
        (θ ((Formalism.L2.Host.tauPl D).symm v)) k = 1 := infMat_of_mem_GfC k hk _
    rw [e, Matrix.mul_one, Matrix.nonsing_inv_mul _ (hd v)]
  · apply mem_GfC_of_infMat θ hθ k
    intro τ
    have e := hinf k (Formalism.L2.Host.tauPl D τ)
    rw [congrFun hk (Formalism.L2.Host.tauPl D τ), Equiv.symm_apply_apply] at e
    have e2 := (conj_eq_iff _ _ _ (hPu _)).1 e.symm
    refine e2.trans ?_
    rw [show Formalism.MainNotions.S.uMat ((1 : (Formalism.L2.SG.InstExistsPf.instOf D).Ginf) (Formalism.L2.Host.tauPl D τ)) = 1 from rfl,
      Matrix.mul_one]
    exact Matrix.mul_nonsing_inv _ (hd _)
  · intro τ g hg
    have hat := isAtTau_atTau θ hθ τ g hg
    refine ⟨?_, fun v hv => ?_, ?_⟩
    · apply Subtype.ext
      apply Units.ext
      have e := (key (atTau θ (D.sp.Y 0) τ g)).2
      refine e.trans (ofHAFin_eq_one _ _ ?_)
      · have e3 : (finHom (D.sp.Y 0) (atTau θ (D.sp.Y 0) τ g)).val = 1 := by
          rw [show finHom (D.sp.Y 0) (atTau θ (D.sp.Y 0) τ g) = 1 from hat.1]; rfl
        ext i j
        exact congrFun (congrFun e3 i) j
    · apply Subtype.ext
      apply Units.ext
      show Formalism.MainNotions.S.uMat ((ι (atTau θ (D.sp.Y 0) τ g)).1 v) = 1
      rw [hinf _ v]
      have hne : (Formalism.L2.Host.tauPl D).symm v ≠ τ := fun e => hv ((Equiv.symm_apply_eq _).1 e)
      have e : Formalism.MainNotions.StandardLattice.infMat (Formalism.L2.SG.InstExistsPf.instOf D).cm.sig (Formalism.L2.SG.InstExistsPf.instOf D).J
          (θ ((Formalism.L2.Host.tauPl D).symm v)) (atTau θ (D.sp.Y 0) τ g) = 1 := hat.2.2 _ hne
      rw [e, Matrix.mul_one, Matrix.nonsing_inv_mul _ (hd v)]
    · apply heq_of_eq
      show Formalism.MainNotions.S.uMat ((ι (atTau θ (D.sp.Y 0) τ g)).1 (Formalism.L2.Host.tauPl D τ)) = _
      rw [hinf _ (Formalism.L2.Host.tauPl D τ), Equiv.symm_apply_apply]
      have e : Formalism.MainNotions.StandardLattice.infMat (Formalism.L2.SG.InstExistsPf.instOf D).cm.sig (Formalism.L2.SG.InstExistsPf.instOf D).J
          (θ τ) (atTau θ (D.sp.Y 0) τ g) = g := hat.2.1
      rw [e]
      rfl
  · intro τ y
    set P := (Formalism.L2.SG.InstExistsPf.instOf D).P (Formalism.L2.Host.tauPl D τ) with hP
    have hdP : IsUnit P.det := hd _
    set H : Matrix (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) ℂ :=
      gramAt D (D.sp.Y 0) τ with hH
    set Y : Matrix (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) ℂ :=
      Formalism.MainNotions.S.uMat y with hY
    have hs : Pᴴ * H * P = Formalism.REAL.Jm ((Formalism.L2.SG.InstExistsPf.instOf D).ε (Formalism.L2.Host.tauPl D τ)) := by
      have := (Formalism.L2.SG.InstExistsPf.instOf D).P_spec (Formalism.L2.Host.tauPl D τ)
      have eφ : (Formalism.L2.SG.InstExistsPf.instOf D).φ (Formalism.L2.Host.tauPl D τ) = tauE D τ := by
        show embS D ((Formalism.L2.Host.tauPl D).symm (Formalism.L2.Host.tauPl D τ)) = _
        rw [Equiv.symm_apply_apply]
        rfl
      rw [eφ] at this
      exact this
    have hy : Yᴴ * Formalism.REAL.Jm ((Formalism.L2.SG.InstExistsPf.instOf D).ε (Formalism.L2.Host.tauPl D τ)) * Y =
        Formalism.REAL.Jm ((Formalism.L2.SG.InstExistsPf.instOf D).ε (Formalism.L2.Host.tauPl D τ)) := y.2
    have hPi : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdP
    have hPiH : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hPi, Matrix.conjTranspose_one]
    have hg : (P * Y * P⁻¹)ᴴ * H * (P * Y * P⁻¹) = H := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
      calc (P⁻¹)ᴴ * (Yᴴ * Pᴴ) * H * (P * Y * P⁻¹) = (P⁻¹)ᴴ * (Yᴴ * (Pᴴ * H * P) * Y) * P⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = (P⁻¹)ᴴ * (Pᴴ * H * P) * P⁻¹ := by rw [hs, hy]
        _ = H := by
            simp only [Matrix.mul_assoc]
            rw [hPi, Matrix.mul_one, ← Matrix.mul_assoc, hPiH, Matrix.one_mul]
    refine ⟨P * Y * P⁻¹, hg, ?_⟩
    have hat := isAtTau_atTau θ hθ τ (P * Y * P⁻¹) hg
    apply Subtype.ext
    apply Units.ext
    show Formalism.MainNotions.S.uMat ((ι (atTau θ (D.sp.Y 0) τ (P * Y * P⁻¹))).1 (Formalism.L2.Host.tauPl D τ)) = Y
    rw [hinf _ (Formalism.L2.Host.tauPl D τ), Equiv.symm_apply_apply]
    have e : Formalism.MainNotions.StandardLattice.infMat (Formalism.L2.SG.InstExistsPf.instOf D).cm.sig (Formalism.L2.SG.InstExistsPf.instOf D).J
        (θ τ) (atTau θ (D.sp.Y 0) τ (P * Y * P⁻¹)) = P * Y * P⁻¹ := hat.2.1
    rw [e]
    exact (conj_eq_iff _ _ _ (hPu _)).2 rfl

theorem iotaX_real_finite : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ k : GA D (D.sp.Y 0), k ∈ GfC (D.sp.Y 0) ↔ (iotaX X h k).1 = 1) ∧ (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), (iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).2 = 1 ∧ (∀ v, v ≠ X.pl.symm τ → (iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 v = 1) ∧ HEq (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) ((fun Pm : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ => Pm⁻¹ * g * Pm) ((Formalism.L2.SG.InstExistsPf.instOf D).P (Formalism.L2.Host.tauPl D τ)))) ∧ ∀ τ (y : Formalism.REAL.UJ (X.B.I.ε (X.pl.symm τ))), ∃ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), (iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ) = y := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h _ _ hMod hιE
  exact iota_real_finite_of_eq R.θ hMod.inf X.B.I h X.ιE X.pl X.φ_eq hιE

end GlobalTheory.IotaReal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicIdentificationRespectsRealFiniteStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicIdentification_respects_real_finite : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ k : GA D (D.sp.Y 0), k ∈ GfC (D.sp.Y 0) ↔ (iotaX X h k).1 = 1) ∧ (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), (iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).2 = 1 ∧ (∀ v, v ≠ X.pl.symm τ → (iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 v = 1) ∧ HEq (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) ((fun Pm : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ => Pm⁻¹ * g * Pm) ((Formalism.L2.SG.InstExistsPf.instOf D).P (Formalism.L2.Host.tauPl D τ)))) ∧ ∀ τ (y : Formalism.REAL.UJ (X.B.I.ε (X.pl.symm τ))), ∃ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), (iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ) = y := by
  first | exact @GlobalTheory.IotaReal.iotaX_real_finite | exact GlobalTheory.IotaReal.iotaX_real_finite | (intros; apply GlobalTheory.IotaReal.iotaX_real_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemIntMat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.InertHomIdx

variable {D : D7}

def compW (D : D7) (w : HeightOneSpectrum (𝓞 D.host.E)) : AE D →+* w.adicCompletion D.host.E :=
  (GlobalTheory.LFun.compAt D.host.F w).comp (finPart D)

def matW (S T : HSp D) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    GlobalTheory.FinWeilO.XF S T →+ Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E) where
  toFun x := (x : WO S T).map (compW D w)
  map_zero' := by ext i j; simp [GlobalTheory.FinWeilO.XF.coe_zero]
  map_add' x y := by ext i j; simp [GlobalTheory.FinWeilO.XF.coe_add]

theorem matW_apply (S T : HSp D) (w : HeightOneSpectrum (𝓞 D.host.E)) (x : GlobalTheory.FinWeilO.XF S T) :
    matW S T w x = (x : WO S T).map (compW D w) := rfl

def intMat (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (m n : ℕ) :
    AddSubgroup (Matrix (Fin m) (Fin n) L) where
  carrier := {X | ∀ i j, X i j ∈ Formalism.UG.intL L}
  add_mem' hX hY i j := add_mem (hX i j) (hY i j)
  zero_mem' _ _ := zero_mem _
  neg_mem' hX i j := neg_mem (hX i j)

theorem mem_intMat {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {m n : ℕ}
    {X : Matrix (Fin m) (Fin n) L} : X ∈ intMat L m n ↔ ∀ i j, X i j ∈ Formalism.UG.intL L := Iff.rfl

def lmul {L : Type} [Ring L] {m n : ℕ} (g : Matrix (Fin m) (Fin m) L) :
    Matrix (Fin m) (Fin n) L →+ Matrix (Fin m) (Fin n) L where
  toFun X := g * X
  map_zero' := Matrix.mul_zero g
  map_add' := Matrix.mul_add g

theorem lmul_apply {L : Type} [Ring L] {m n : ℕ} (g : Matrix (Fin m) (Fin m) L) (X : Matrix (Fin m) (Fin n) L) :
    lmul g X = g * X := rfl

end GlobalTheory.InertHomIdx

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteEmbeddingIdempotentPatchInFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteEmbeddingIdempotentPatchInFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FineCut

theorem conj_cut {R : Type} [CommRing R] {n : ℕ} (β F : GL (Fin n) R) (c : R) :
    β.1 * (c • (β⁻¹ * F * β).1 + (1 - c) • (1 : Matrix (Fin n) (Fin n) R)) * (β⁻¹).1
      = c • F.1 + (1 - c) • (1 : Matrix (Fin n) (Fin n) R) := by
  have h1 : β.1 * (β⁻¹ * F * β).1 * (β⁻¹).1 = F.1 := by
    rw [← Units.val_mul, ← Units.val_mul]; congr 1; group
  have h2 : β.1 * (β⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, h1, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, h2]

theorem finE_cut : ∀ {D : D7} (T : HSp D) (βT : GL (Fin T.rank) (EAf D)) (g k : GA D T) (ε : AE D), Formalism.L2.Theta.mt T k = ε • Formalism.L2.Theta.mt T g + (1 - ε) • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) → (Formalism.IndefR.Lev.finE T k : GL (Fin T.rank) (EAf D)).1 = βT.1 * (toEAf D ε • (βT⁻¹ * Formalism.IndefR.Lev.finE T g * βT : GL (Fin T.rank) (EAf D)).1 + (1 - toEAf D ε) • (1 : Matrix (Fin T.rank) (Fin T.rank) (EAf D))) * (βT⁻¹ : GL (Fin T.rank) (EAf D)).1 := by
  intro D T βT g k ε h
  have hk : (Formalism.IndefR.Lev.finE T k : GL (Fin T.rank) (EAf D)).1
      = toEAf D ε • (Formalism.IndefR.Lev.finE T g : GL (Fin T.rank) (EAf D)).1 + (1 - toEAf D ε) • (1 : Matrix (Fin T.rank) (Fin T.rank) (EAf D)) := by
    show (Formalism.L2.Theta.mt T k).map (toEAf D) = toEAf D ε • (Formalism.L2.Theta.mt T g).map (toEAf D) + (1 - toEAf D ε) • 1
    rw [h, GlobalTheory.CompStab.map_idem]
  rw [hk]
  exact (conj_cut βT (Formalism.IndefR.Lev.finE T g) (toEAf D ε)).symm

end GlobalTheory.FineCut

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteEmbeddingIdempotentPatchInFrameStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteEmbedding_idempotent_patch_in_frame : ∀ {D : D7} (T : HSp D) (βT : GL (Fin T.rank) (EAf D)) (g k : GA D T) (ε : AE D), Formalism.L2.Theta.mt T k = ε • Formalism.L2.Theta.mt T g + (1 - ε) • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) → (Formalism.IndefR.Lev.finE T k : GL (Fin T.rank) (EAf D)).1 = βT.1 * (toEAf D ε • (βT⁻¹ * Formalism.IndefR.Lev.finE T g * βT : GL (Fin T.rank) (EAf D)).1 + (1 - toEAf D ε) • (1 : Matrix (Fin T.rank) (Fin T.rank) (EAf D))) * (βT⁻¹ : GL (Fin T.rank) (EAf D)).1 := by
  first | exact @GlobalTheory.FineCut.finE_cut | exact GlobalTheory.FineCut.finE_cut | (intros; apply GlobalTheory.FineCut.finE_cut <;> assumption)
end
end
