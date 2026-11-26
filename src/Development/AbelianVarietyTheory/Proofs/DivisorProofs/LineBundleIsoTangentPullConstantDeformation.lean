module

public import Development.AbelianVarietyTheory.Definitions.Divisors.P22
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveStrongApproximationAvoidingFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StoneVonNeumannSchwartzBruhatTransverseLagrangia
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsPtOfOfRat
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutLat

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoTangentPullConstantDeformation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoTangentPullConstantDeformation
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj MonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.TangentConstLB

theorem symIso_of_comm {S₀ S₁ : Scheme.{0}} {X : Over S₀} {A' : Over S₁} [GrpObj X] [GrpObj A']
    {L : LB X.left} (hL : L.IsLB)
    (hS : LBIso L (L.pull (GrpObj.inv : X ⟶ X).left)) (f : A'.left ⟶ X.left)
    (hf : (GrpObj.inv : A' ⟶ A').left ≫ f = f ≫ (GrpObj.inv : X ⟶ X).left) :
    LBIso ((L.pull f).pull (GrpObj.inv : A' ⟶ A').left) (L.pull f) := by
  have pull_isLB : ∀ {X Y : Scheme.{0}} {L : LB X}, L.IsLB → (F : Y ⟶ X) → (L.pull F).IsLB := by
    intro X Y L hL F
    refine ⟨top_le_iff.1 ?_, ?_, ?_⟩
    · intro y _
      obtain ⟨i, hi⟩ := exists_chart hL (F y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
    · intro J
      refine unit_ext fun y hy => ?_
      rw [gm_res (𝟙 Y) y _ hy, map_one, gm_pull_g L F (𝟙 Y) y J J hy hy]
      exact gm_self hL _ y (mem_pull.1 hy)
    · intro I J K
      refine unit_ext fun y hy => ?_
      rw [map_mul, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy,
        gm_pull_g L F (𝟙 Y) y I J hy.1.1 hy.1.2,
        gm_pull_g L F (𝟙 Y) y J K hy.1.2 hy.2, gm_pull_g L F (𝟙 Y) y I K hy.1.1 hy.2]
      exact gm_cocycle hL _ y (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2)
  have h1 := GlobalTheory.FamRep.lbIso_pull_pull hL f (GrpObj.inv : A' ⟶ A').left
  rw [hf] at h1
  have h2 := (GlobalTheory.FamRep.lbIso_pull_pull hL (GrpObj.inv : X ⟶ X).left f).symm
  have h3 := GlobalTheory.FamRep.lbIso_pull hS.symm f
  have hinv := pull_isLB hL (GrpObj.inv : X ⟶ X).left
  exact LBIso.trans (pull_isLB (pull_isLB hL f) _) (pull_isLB hL _) (pull_isLB hL f) h1
    (LBIso.trans (pull_isLB hL _) (pull_isLB hinv f) (pull_isLB hL f) h2 h3)

theorem lbIso_tangent_const :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (x₀ : Sp K ⟶ Xo.X) (x' : Sp (DualNumber K) ⟶ Xo.X) (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (q : A'.left ⟶ A.left), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G x₀ π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π → i ≫ q = 𝟙 _ → IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q → LBIso (Xo.univ.t.PP.L.pull π') (Xo.univ.t.PP.L.pull (q ≫ π)) := by
  intro E _ _ _ H Dw l Xo c K _ _ x₀ x' A _ A' _ π π' i q hi hπ hπ' hiπ hiq hq
  have pull_isLB : ∀ {X Y : Scheme.{0}} {L : LB X}, L.IsLB → (F : Y ⟶ X) → (L.pull F).IsLB := by
    intro X Y L hL F
    refine ⟨top_le_iff.1 ?_, ?_, ?_⟩
    · intro y _
      obtain ⟨i, hi⟩ := exists_chart hL (F y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
    · intro J
      refine unit_ext fun y hy => ?_
      rw [gm_res (𝟙 Y) y _ hy, map_one, gm_pull_g L F (𝟙 Y) y J J hy hy]
      exact gm_self hL _ y (mem_pull.1 hy)
    · intro I J K
      refine unit_ext fun y hy => ?_
      rw [map_mul, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy,
        gm_pull_g L F (𝟙 Y) y I J hy.1.1 hy.1.2,
        gm_pull_g L F (𝟙 Y) y J K hy.1.2 hy.2, gm_pull_g L F (𝟙 Y) y I K hy.1.1 hy.2]
      exact gm_cocycle hL _ y (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2)
  haveI : CharZero K := (RingHom.charZero_iff (algebraMap c.F K).injective).1 inferInstance
  have hAbG : IsAbelianScheme Xo.univ.t.G := by
    haveI := Xo.univ.proper
    exact AbelianSchemeGerms.isAbelianScheme_of_proper _ Xo.univ.t.semi
  have hA : IsAbelianScheme A := by
    refine { comm := ?_, smooth := ?_, proper := ?_, geomConnected := ?_ }
    · have := hAbG.comm
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (hπ.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← hπ.2 T x y (pushPt hπ.1.w x) (pushPt hπ.1.w y) rfl rfl,
        ← hπ.2 T y x (pushPt hπ.1.w y) (pushPt hπ.1.w x) rfl rfl, _root_.mul_comm]
    · exact MorphismProperty.of_isPullback (P := @Smooth) hπ.1 hAbG.smooth
    · exact MorphismProperty.of_isPullback (P := @IsProper) hπ.1 hAbG.proper
    · exact MorphismProperty.of_isPullback (P := @GeometricallyConnected) hπ.1 hAbG.geomConnected
  have hL := Xo.univ.t.PP.isLB
  obtain ⟨-, w, hw, -⟩ := Xo.univ.t.sym
  have hS : LBIso Xo.univ.t.PP.L (Xo.univ.t.PP.L.pull (GrpObj.inv : Xo.univ.t.G ⟶ Xo.univ.t.G).left) := ⟨w, hw⟩
  have c1 : (GrpObj.inv : A' ⟶ A').left ≫ π' = π' ≫ (GrpObj.inv : Xo.univ.t.G ⟶ Xo.univ.t.G).left :=
    GlobalTheory.PolBaseChange.inv_comm hπ'
  have c2 : (GrpObj.inv : A' ⟶ A').left ≫ (q ≫ π) = (q ≫ π) ≫ (GrpObj.inv : Xo.univ.t.G ⟶ Xo.univ.t.G).left := by
    rw [← Category.assoc, GlobalTheory.PolBaseChange.inv_comm hq, Category.assoc, GlobalTheory.PolBaseChange.inv_comm hπ,
      Category.assoc]
  have f1 := GlobalTheory.FamRep.lbIso_pull_pull hL π' i
  rw [hiπ] at f1
  have f2 := GlobalTheory.FamRep.lbIso_pull_pull hL (q ≫ π) i
  rw [← Category.assoc, hiq, Category.id_comp] at f2
  exact GlobalTheory.SymFirstOrder.lbIso_of_symmetric K A A' i q hA hi hq hiq _ _ (pull_isLB hL π') (pull_isLB hL (q ≫ π))
    (symIso_of_comm hL hS π' c1) (symIso_of_comm hL hS (q ≫ π) c2)
    (LBIso.trans (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) f1 f2.symm)

end GlobalTheory.TangentConstLB
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoTangentPullConstantDeformationStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj MonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundle_iso_tangent_pull_constant_deformation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (x₀ : Sp K ⟶ Xo.X) (x' : Sp (DualNumber K) ⟶ Xo.X) (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (q : A'.left ⟶ A.left), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G x₀ π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π → i ≫ q = 𝟙 _ → IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q → LBIso (Xo.univ.t.PP.L.pull π') (Xo.univ.t.PP.L.pull (q ≫ π)) := by
  first | exact @GlobalTheory.TangentConstLB.lbIso_tangent_const | exact GlobalTheory.TangentConstLB.lbIso_tangent_const | (intros; apply GlobalTheory.TangentConstLB.lbIso_tangent_const <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StoneVonNeumannSchwartzBruhatAnyCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StoneVonNeumannSchwartzBruhatAnyCharacter
open Matrix

noncomputable section
namespace GlobalTheory.SvNAnyChar

def scaleSnd {k : Type} [Field k] {κ : Type} (c : k) :
    (κ → k) × (κ → k) →+ (κ → k) × (κ → k) where
  toFun w := (w.1, c • w.2)
  map_zero' := by simp
  map_add' a b := by simp

@[simp] theorem scaleSnd_fst {k : Type} [Field k] {κ : Type} (c : k) (w : (κ → k) × (κ → k)) :
    (scaleSnd c w).1 = w.1 := rfl

@[simp] theorem scaleSnd_snd {k : Type} [Field k] {κ : Type} (c : k) (w : (κ → k) × (κ → k)) :
    (scaleSnd c w).2 = c • w.2 := rfl

theorem schr_mulShift_scaleSnd {k : Type} [Field k] [Invertible (2 : k)] {κ : Type} [Fintype κ]
    (ψ : AddChar k ℂ) {c : k} (hc : c ≠ 0) (w : (κ → k) × (κ → k)) (φ : (κ → k) → ℂ) :
    GlobalTheory.WeilM.schr (ψ.mulShift c) (scaleSnd c⁻¹ w) φ = GlobalTheory.WeilM.schr ψ w φ := by
  funext x
  simp only [GlobalTheory.WeilM.schr, scaleSnd_fst, scaleSnd_snd, AddChar.mulShift_apply, dotProduct_smul,
    smul_eq_mul]
  congr 2
  rw [mul_add, mul_left_comm c (⅟2), mul_inv_cancel_left₀ hc, mul_inv_cancel_left₀ hc]

theorem stoneVonNeumann_any_char :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    [Invertible (2 : k)] {κ : Type} [Fintype κ] {n d : ℕ} (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 →
    ∀ (wT wM : Matrix (Fin n) (Fin d) k →+ (κ → k) × (κ → k)),
    (∀ Y Y', (wT Y).1 ⬝ᵥ (wT Y').2 - (wT Y').1 ⬝ᵥ (wT Y).2 = 0) →
    (∀ z z', (wM z).1 ⬝ᵥ (wM z').2 - (wM z').1 ⬝ᵥ (wM z).2 = 0) →
    (∀ Y z, (wT Y).1 ⬝ᵥ (wM z).2 - (wM z).1 ⬝ᵥ (wT Y).2 = ∑ i, ∑ j, Y i j * z i j) →
    (∀ w, ∃ Y z, wT Y + wM z = w) →
    ∃ ι : ((κ → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ),
      Set.BijOn ι (GlobalTheory.WeilM.SB (κ → k) : Set _) (GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) : Set _) ∧
      (∀ Y, ∀ φ ∈ GlobalTheory.WeilM.SB (κ → k), ι (GlobalTheory.WeilM.schr ψ0 (wT Y) φ) = fun Y' => ι φ (Y' + Y)) ∧
      (∀ z, ∀ φ ∈ GlobalTheory.WeilM.SB (κ → k), ι (GlobalTheory.WeilM.schr ψ0 (wM z) φ) = fun Y' => ψ0 (∑ i, ∑ j, Y' i j * z i j) * ι φ Y') := by
  intro k _ _ _ _ _ _ κ _ n d ψ0 hψ hne wT wM hT hM hTM hsurj
  obtain ⟨c, hc, hcond⟩ := GlobalTheory.CondRescale.exists_rescale_conductor_integers ψ0 hψ hne
  have hψ1 : Continuous (ψ0.mulShift c) := by
    have : (ψ0.mulShift c : k → ℂ) = fun x => ψ0 (c * x) := by
      funext x
      exact AddChar.mulShift_apply
    rw [this]
    exact hψ.comp (continuous_const.mul continuous_id)
  let S : Matrix (Fin n) (Fin d) k →+ Matrix (Fin n) (Fin d) k :=
    { toFun := fun z => c • z
      map_zero' := smul_zero c
      map_add' := smul_add c }
  have hS : ∀ z, S z = c • z := fun _ => rfl
  have hsum : ∀ (a : k) (Y z : Matrix (Fin n) (Fin d) k),
      ∑ i, ∑ j, Y i j * (a • z) i j = a * ∑ i, ∑ j, Y i j * z i j := by
    intro a Y z
    simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  obtain ⟨ι, hbij, h1, h2⟩ := GlobalTheory.T.stoneVonNeumann_schwartzBruhat_transverseLagrangians (κ := κ) (n := n) (d := d) (ψ0.mulShift c) hψ1
    (fun x => by simpa only [AddChar.mulShift_apply] using hcond x)
    ((scaleSnd c⁻¹).comp wT) ((scaleSnd c⁻¹).comp (wM.comp S))
    (fun Y Y' => by
      simp only [AddMonoidHom.comp_apply, scaleSnd_fst, scaleSnd_snd, dotProduct_smul, smul_eq_mul]
      rw [← mul_sub, hT, mul_zero])
    (fun z z' => by
      simp only [AddMonoidHom.comp_apply, scaleSnd_fst, scaleSnd_snd, dotProduct_smul, smul_eq_mul]
      rw [← mul_sub, hM, mul_zero])
    (fun Y z => by
      simp only [AddMonoidHom.comp_apply, scaleSnd_fst, scaleSnd_snd, dotProduct_smul, smul_eq_mul]
      rw [← mul_sub, hTM, hS, hsum, inv_mul_cancel_left₀ hc])
    (fun w => by
      obtain ⟨Y, z, h⟩ := hsurj (scaleSnd c w)
      refine ⟨Y, c⁻¹ • z, ?_⟩
      simp only [AddMonoidHom.comp_apply]
      rw [hS, smul_inv_smul₀ hc, ← map_add (f := _), h]
      exact Prod.ext rfl (inv_smul_smul₀ hc _))
  refine ⟨ι, hbij, fun Y φ hφ => ?_, fun z φ hφ => ?_⟩
  · have := h1 Y φ hφ
    rwa [AddMonoidHom.comp_apply, schr_mulShift_scaleSnd ψ0 hc] at this
  · have := h2 (c⁻¹ • z) φ hφ
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, schr_mulShift_scaleSnd ψ0 hc, hS,
      smul_inv_smul₀ hc] at this
    rw [this]
    funext Y'
    rw [AddChar.mulShift_apply, hsum, mul_inv_cancel_left₀ hc]

end GlobalTheory.SvNAnyChar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StoneVonNeumannSchwartzBruhatAnyCharacterStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stoneVonNeumann_schwartzBruhat_anyCharacter : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    [Invertible (2 : k)] {κ : Type} [Fintype κ] {n d : ℕ} (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 →
    ∀ (wT wM : Matrix (Fin n) (Fin d) k →+ (κ → k) × (κ → k)),
    (∀ Y Y', (wT Y).1 ⬝ᵥ (wT Y').2 - (wT Y').1 ⬝ᵥ (wT Y).2 = 0) →
    (∀ z z', (wM z).1 ⬝ᵥ (wM z').2 - (wM z').1 ⬝ᵥ (wM z).2 = 0) →
    (∀ Y z, (wT Y).1 ⬝ᵥ (wM z).2 - (wM z).1 ⬝ᵥ (wT Y).2 = ∑ i, ∑ j, Y i j * z i j) →
    (∀ w, ∃ Y z, wT Y + wM z = w) →
    ∃ ι : ((κ → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ),
      Set.BijOn ι (GlobalTheory.WeilM.SB (κ → k) : Set _) (GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) : Set _) ∧
      (∀ Y, ∀ φ ∈ GlobalTheory.WeilM.SB (κ → k), ι (GlobalTheory.WeilM.schr ψ0 (wT Y) φ) = fun Y' => ι φ (Y' + Y)) ∧
      (∀ z, ∀ φ ∈ GlobalTheory.WeilM.SB (κ → k), ι (GlobalTheory.WeilM.schr ψ0 (wM z) φ) = fun Y' => ψ0 (∑ i, ∑ j, Y' i j * z i j) * ι φ Y') := by
  first | exact @GlobalTheory.SvNAnyChar.stoneVonNeumann_any_char | exact GlobalTheory.SvNAnyChar.stoneVonNeumann_any_char | (intros; apply GlobalTheory.SvNAnyChar.stoneVonNeumann_any_char <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterFiniteIdeleValueEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterFiniteIdeleValueEq
open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.FinIdlRead

open GlobalTheory.Mem.Col2.SplitChar

theorem toFinE_eq_adEquiv (D : D7) (y : Formalism.MainNotions.StandardLatticesGL3.AE D) : GlobalTheory.BotFormula.toFinE D y = adEquiv D y := by
  let f : Formalism.MainNotions.StandardLatticesGL3.AE D →+* Formalism.MainNotions.StandardLatticesGL3.AE D := (adEquiv D).symm.toRingHom.comp (GlobalTheory.BotFormula.toFinE D).toRingHom
  have hf : ∀ z, adEquiv D (f z) = GlobalTheory.BotFormula.toFinE D z := fun z => (adEquiv D).apply_symm_apply _
  have hι : ∀ (x : D.host.E) (a : FiniteAdeleRing (𝓞 ℚ) ℚ), (GlobalTheory.BotFormula.toFinE D).toRingHom (x ⊗ₜ[ℚ] a) =
      algebraMap D.host.E _ x * GlobalTheory.AdeleBaseChange.adMap ℚ D.host.E a := GlobalTheory.BotClassDict.toFinE_tmul
  have hinc : ∀ a : D.host.E, f (inc D a) = inc D a := fun a => by
    apply (adEquiv D).injective
    rw [hf, adEquiv_inc]
    have h1 : GlobalTheory.BotFormula.toFinE D (inc D a) = algebraMap D.host.E _ a * GlobalTheory.AdeleBaseChange.adMap ℚ D.host.E 1 :=
      GlobalTheory.BotClassDict.toFinE_tmul a 1
    rw [h1, map_one, mul_one]
  have hint : ∀ r ∈ OhE D, f r ∈ OhE D := fun r hr => by
    rw [mem_OhE_iff, hf]
    exact GlobalTheory.AdeleBaseChange.map_mem_int (F := ℚ) (E := D.host.E) hι hr
  have h0 : f y - y = 0 := by
    refine GlobalTheory.AdeleBaseChange.eq_zero_of_divisible (F := ℚ) (E := D.host.E) (f y - y) fun N hN => ?_
    obtain ⟨a, r, hr, e⟩ := exists_approx y hN
    refine ⟨f r - r, sub_mem (hint r hr) hr, ?_⟩
    rw [nsmul_eq_mul]
    change f y - y = (N : Formalism.MainNotions.StandardLatticesGL3.AE D) * (f r - r)
    rw [e, map_add (f := _), map_mul, map_natCast, hinc]
    ring
  rw [← hf, sub_eq_zero.1 h0]

theorem finAdEquiv_one_tmul (D : D7) (x : D.host.E) :
    GlobalTheory.LFun.finAdEquiv D.host.F D.host.E ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) =
      algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x := by
  show GlobalTheory.LFun.toFinAd D.host.F D.host.E ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = _
  rw [GlobalTheory.LFun.toFinAd_tmul, map_one, one_mul]

theorem mem_intAE_iff_finAdEquiv (D : D7) (y : Af D.host.F ⊗[D.host.F] D.host.E) :
    y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E y P) ≤ 1 := by
  let c := (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toRingEquiv
  let ι : Formalism.L2.DIV.AfE D.host.F D.host.E →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E :=
    (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).toRingHom.comp c.symm.toRingHom
  have hι : ∀ x a, ι (x ⊗ₜ[D.host.F] a) = algebraMap D.host.E _ x * GlobalTheory.AdeleBaseChange.adMap D.host.F D.host.E a :=
    fun x a => (GlobalTheory.LFun.toFinAd_tmul a x).trans (mul_comm _ _)
  have e : ι (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E y) = GlobalTheory.LFun.finAdEquiv D.host.F D.host.E y := by
    change GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (c.symm (c y)) = _
    rw [c.symm_apply_apply]
  rw [GlobalTheory.HostAdeleIso.mem_intAE_iff_comm]
  constructor
  · intro hy
    have := GlobalTheory.AdeleBaseChange.map_mem_int hι hy
    rw [e] at this
    exact this
  · intro hy
    refine GlobalTheory.AdeleBaseChange.mem_int_of_map hι ?_
    rw [e]
    exact hy

theorem chr_finIdl : ∀ {D : D7} (ν : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq ν χ → ∀ x y, IsFinIdl x y →
    ((ν x : Circle) : ℂ) = ((χ.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D y) : ℂˣ) : ℂ) := by
  intro D ν χ h x y hxy
  obtain ⟨Φ, -, hΦ', h1, h2, h3⟩ := GlobalTheory.DetRootRead.exists_adele_equiv_fin D (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E)
    (finAdEquiv_one_tmul D) (mem_intAE_iff_finAdEquiv D)
  rw [GlobalTheory.DetRootRead.read_of_equiv D ν χ h Φ hΦ' h1 h2 x]
  obtain ⟨s, hs, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have split : ∀ z w : AE D, infPart D z = infPart D w → finPart D z = finPart D w → z = w := fun z w hi hf =>
    s.injective (Prod.ext ((hs z).1.trans (hi.trans (hs w).1.symm)) ((hs z).2.trans (hf.trans (hs w).2.symm)))
  have hfst : (Φ (x : AE D)).1 = 1 := by
    let w : AE D := Φ.symm (1, (Φ (x : AE D)).2)
    have hw : Φ w = (1, (Φ (x : AE D)).2) := Φ.apply_symm_apply _
    have hwi : infPart D w = 1 := (h3 w).1 (by rw [hw])
    have hwf : finPart D w = finPart D (x : AE D) := by
      apply (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).injective
      rw [← (h3 w).2, ← (h3 (x : AE D)).2, hw]
    have : w = (x : AE D) := split _ _ (hwi.trans hxy.1.symm) hwf
    rw [← this, hw]
  have he : Units.map Φ.toRingHom.toMonoidHom x = GlobalTheory.Mem.Col2.SplitChar.finIdl D y := by
    refine Units.ext (Prod.ext ?_ ?_)
    · exact hfst
    · change (Φ (x : AE D)).2 = adEquiv D (y : Formalism.MainNotions.StandardLatticesGL3.AE D)
      rw [(h3 _).2, hxy.2, toFinE_eq_adEquiv]
  rw [he]

end GlobalTheory.FinIdlRead
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterFiniteIdeleValueEqStatement
open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeCharacter_finiteIdele_value_eq : ∀ {D : D7} (ν : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq ν χ → ∀ x y, IsFinIdl x y →
  ((ν x : Circle) : ℂ) = ((χ.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D y) : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.FinIdlRead.chr_finIdl | exact GlobalTheory.FinIdlRead.chr_finIdl | (intros; apply GlobalTheory.FinIdlRead.chr_finIdl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefLineBundleBaseChangeFieldExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefLineBundleBaseChangeFieldExtension
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefFieldExt

variable {k E : Type} [Field k] [Field E] {X Y : Scheme.{0}} [Algebra k Γ(X, ⊤)] [Algebra E Γ(Y, ⊤)]

theorem isNef_pull (hN : Published.NefNumerics) [IsProper (strHom k (X := X))] {L H : LB X} (h : IsNef k L)
    (hH : IsAmpleLB H) {H' : LB Y} (hH' : IsAmpleLB H') (g : Y ⟶ X) : IsNef E (L.pull g) := by
  have hL := LB.isLB_pull h.isLB g
  have hA := LB.isLB_pull hH.isLB g
  refine ⟨hL, fun C hC => ?_⟩
  let Z : Closeds X := Closeds.closure (g '' C)
  have hi : IsIrreducible (Z : Set X) := (hC.1.image g g.continuous.continuousOn).closure
  obtain ⟨φ, hφ⟩ : ∃ φ, φ ≫ redι Z = redι C ≫ g := ⟨IsClosedImmersion.lift (redι Z) (redι C ≫ g) (by
    rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι,
      Scheme.IdealSheafData.map_vanishingIdeal]), IsClosedImmersion.lift_fac _ _ _⟩

  letI := algebraΓAlong k (redι Z)
  have := isIntegral_red hi
  have hZp : IsProper (strHom k (X := (Scheme.IdealSheafData.vanishingIdeal Z).subscheme)) := by
    rw [← comp_strHom (appTop_algebraMap_along k (redι Z))]
    infer_instance
  have hHZ := hH.pull_of_isClosedImmersion (redι Z)
  have hproj := hHZ.isProjOver (strHom k _)
  have hLZ : IsNef k (L.pull (redι Z)) := h.pull_of_isClosedImmersion (redι Z) (appTop_algebraMap_along k (redι Z))

  letI := algebraΓAlong E (redι C)
  have := hC.isProper_strHom
  have := isIntegral_red hC.1

  have hdense : ∀ U : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme.Opens,
      genericPoint _ ∈ U → ∃ y, φ y ∈ U := fun U hU => by
    obtain ⟨V, hV, hUV⟩ := (redι Z).isClosedEmbedding.isInducing.isOpen_iff.1 U.isOpen
    have h1 : redι Z (genericPoint _) ∈ V := by
      rw [← Set.mem_preimage, hUV]; exact hU
    have h2 : redι Z (genericPoint _) ∈ closure (g '' C) := by
      have := (range_redι Z).le ⟨genericPoint (Scheme.IdealSheafData.vanishingIdeal Z).subscheme, rfl⟩
      exact this
    obtain ⟨_, hv, ⟨c, hc, rfl⟩⟩ := mem_closure_iff.1 h2 V hV h1
    obtain ⟨y, rfl⟩ := (range_redι C).ge hc
    refine ⟨y, ?_⟩
    rw [← SetLike.mem_coe, ← hUV, Set.mem_preimage]
    have e : redι Z (φ y) = g (redι C y) := congrArg (fun q => q y) hφ
    rw [e]; exact hv
  have key : ∀ m : ℕ, 0 ≤ m * interNumRed E C ![L.pull g] + interNumRed E C ![H.pull g] := fun m => by
    have hbig := (hLZ.pow hHZ m).isBig_tens_ample hN hproj hHZ
    obtain ⟨r, ⟨s, hs0⟩, hr⟩ :=
      (hbig.frequently_hasNonzeroSec.and_eventually (Filter.eventually_ge_atTop 1)).exists
    obtain ⟨x, hx⟩ := hdense (nonzeroLocus s) ((sec_ne_zero_iff s).1 hs0)
    have hx' : x ∈ nonzeroLocus (secPull s φ) := (nonzeroLocus_secPull s φ).ge hx
    have hLZ' := LB.isLB_pull h.isLB (redι Z)
    have hHZ' := LB.isLB_pull hH.isLB (redι Z)
    have hr' := isLB_lbPow (isLB_tens (isLB_lbPow hLZ' m) hHZ') r
    have h0 := (interNum_one_nonneg_of_sec (k := E) (hH'.pull_of_isClosedImmersion (redι C))
      ((topologicalKrullDim_red C).trans hC.2) (LB.isLB_pull hr' φ) (secPull s φ)
      ((sec_ne_zero_iff _).1 (sec_ne_zero_of_mem hx'))).1
    have hT' := isLB_tens (isLB_lbPow hL m) hA
    have h1 : interNumRed E C ![lbPow (tens (lbPow (L.pull g) m) (H.pull g)) r] =
        interNum E (structureModule _) ![(lbPow (tens (lbPow (L.pull (redι Z)) m) (H.pull (redι Z))) r).pull φ] := by
      rw [interNumRed_one_eq (isLB_lbPow hT' r)]
      refine interNum_congr_cls E _ (isLB_vecOne (LB.isLB_pull (isLB_lbPow hT' r) _))
        (isLB_vecOne (LB.isLB_pull hr' φ)) fun i => ?_
      fin_cases i
      change pull (redι C) (cls _ (isLB_lbPow hT' r)) = pull φ (cls _ hr')
      rw [cls_lbPow_tens_lbPow hL hA, cls_lbPow_tens_lbPow hLZ' hHZ', cls_pull h.isLB, cls_pull hH.isLB,
        cls_pull h.isLB, cls_pull hH.isLB]
      simp only [map_nsmul, map_add (f := _), ← pull_comp, hφ]
    rw [← h1, hC.interNumRed_lbPow hH' hT', hC.interNumRed_of_cls_eq_add hH' hT' (isLB_lbPow hL m) hA rfl,
      hC.interNumRed_lbPow hH' hL] at h0
    exact nonneg_of_mul_nonneg_right h0 (Nat.cast_pos.2 hr)
  by_contra! hneg
  have := key ((interNumRed E C ![H.pull g]).natAbs + 1)
  have h2 := le_abs_self (interNumRed E C ![H.pull g])
  have h3 := abs_nonneg (interNumRed E C ![H.pull g])
  push_cast at this
  nlinarith

end GlobalTheory.NefFieldExt

namespace GlobalTheory.NefFieldExt

theorem isNef_baseChange : GlobalTheory.Published.NefNumerics → ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0})
    (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → IsProjOver p →
    letI := algebraΓOfHom p; letI := algebraΓOfHom q; ∀ L : LB Y, IsNef k L → IsNef E (L.pull π) := by
  intro hN k E _ _ _ Y X p q π H hp
  letI := algebraΓOfHom p
  letI := algebraΓOfHom q
  intro L hL
  obtain ⟨hpp, A, hA⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp
  have : IsProper (strHom k (X := Y)) := by rw [strHom_eq (f := p) fun _ => rfl]; exact hpp
  have : IsAffineHom π := MorphismProperty.of_isPullback H.flip inferInstance
  exact isNef_pull hN hL hA (hA.pull_of_isAffineHom π) π

end GlobalTheory.NefFieldExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefLineBundleBaseChangeFieldExtensionStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNefLineBundle_baseChange_field_extension : GlobalTheory.Published.NefNumerics → ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → IsProjOver p → letI := algebraΓOfHom p; letI := algebraΓOfHom q; ∀ L : LB Y, IsNef k L → IsNef E (L.pull π) := by
  first | exact @GlobalTheory.NefFieldExt.isNef_baseChange | exact GlobalTheory.NefFieldExt.isNef_baseChange | (intros; apply GlobalTheory.NefFieldExt.isNef_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianMulNatSurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianMulNatSurjective
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SemiAbSurj

theorem surjective_of_rationalPoints {k : Type} [Field k] [IsAlgClosed k] {X Y : Over (Sp k)}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] (f : X ⟶ Y) [Flat f.left]
    [LocallyOfFinitePresentation f.left]
    (h : ∀ y : 𝟙_ (Over (Sp k)) ⟶ Y, ∃ x : 𝟙_ (Over (Sp k)) ⟶ X, x ≫ f = y) : Surjective f.left := by
  refine ⟨Set.range_eq_univ.1 ?_⟩
  by_contra hne
  obtain ⟨y, hy⟩ := RationalPoint.exists_pt_mem (f.left.isOpenMap.isOpen_range).isClosed_compl
    (Set.nonempty_compl.2 hne)
  obtain ⟨x, rfl⟩ := h y
  exact hy ⟨RationalPoint.pt x, rfl⟩

end GlobalTheory.SemiAbSurj

namespace GlobalTheory.SemiAbSurj

theorem exists_root_unit {k : Type} [Field k] [IsAlgClosed k] (m : ℕ) (hm : m ≠ 0)
    (u : Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ) : ∃ v : Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ, v ^ m = u := by
  let e : Γ((𝟙_ (Over (Sp k))).left, ⊤) ≃+* k := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e u.val) (Nat.pos_of_ne_zero hm)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hm] at hz
    exact (u.isUnit.map e).ne_zero hz.symm
  refine ⟨Units.map e.symm.toRingHom.toMonoidHom (Units.mk0 z hz0), Units.ext ?_⟩
  rw [← map_pow, Units.coe_map, Units.val_pow_eq_pow_val, Units.val_mk0, hz]
  exact e.symm_apply_apply u.val

theorem exists_pow_eq_of_torusExtension {k : Type} [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G]
    [IsCommMonObj G] [LocallyOfFiniteType G.hom] (E : TorusExtension G) (m : ℕ) (hm : m ≠ 0)
    (x : 𝟙_ (Over (Sp k)) ⟶ G) : ∃ y : 𝟙_ (Over (Sp k)) ⟶ G, y ^ m = x := by
  classical
  letI := E.addCommGroup
  letI := E.free
  letI := E.grpB
  haveI := E.q_hom
  haveI := E.i_hom
  have hB := E.isAbelian
  haveI := hB.smooth
  haveI := hB.comm

  have hsB := GlobalTheory.AbelianLimit.surjective_pow E.B hB m (Nat.one_le_iff_ne_zero.2 hm)
  haveI : LocallyOfFiniteType (((𝟙 E.B) ^ m : E.B ⟶ E.B).left ≫ E.B.hom) := by rw [Over.w]; infer_instance
  haveI : LocallyOfFiniteType ((𝟙 E.B) ^ m : E.B ⟶ E.B).left := locallyOfFiniteType_of_comp _ E.B.hom
  obtain ⟨p, hp⟩ := GlobalTheory.GeomSurj.exists_lift_of_surjective ((𝟙 E.B) ^ m : E.B ⟶ E.B).left (x ≫ E.q).left
  let b' : 𝟙_ (Over (Sp k)) ⟶ E.B := Over.homMk p (by
    have := Over.w (x ≫ E.q)
    rw [hp, Category.assoc, Over.w] at this
    exact this)
  have hb' : b' ^ m = x ≫ E.q := by
    rw [← Category.comp_id b', ← MonObj.comp_pow]
    exact Over.OverMorphism.ext hp.symm

  haveI : LocallyOfFiniteType (E.q.left ≫ E.B.hom) := by rw [Over.w]; infer_instance
  haveI : LocallyOfFiniteType E.q.left := locallyOfFiniteType_of_comp _ E.B.hom
  haveI := E.q_surjective
  obtain ⟨p', hp'⟩ := GlobalTheory.GeomSurj.exists_lift_of_surjective E.q.left b'.left
  let g' : 𝟙_ (Over (Sp k)) ⟶ G := Over.homMk p' (by
    have := Over.w b'
    rw [hp', Category.assoc, Over.w] at this
    exact this)
  have hg' : g' ≫ E.q = b' := Over.OverMorphism.ext hp'.symm

  let qh := IsMonHom.monoidHom E.q (𝟙_ (Over (Sp k)))
  let ih := IsMonHom.monoidHom E.i (𝟙_ (Over (Sp k)))
  have hq : ∀ z, qh z = z ≫ E.q := fun _ => rfl
  have hi : ∀ z, ih z = z ≫ E.i := fun _ => rfl
  let h := x * (g' ^ m)⁻¹
  have hh : h ≫ E.q = 1 := by
    rw [← hq, map_mul, map_inv, map_pow, hq, hq, hg', hb', mul_inv_cancel]
  let s := E.isKernel.lift h (toUnit _) (by rw [hh, Hom.one_def])
  have hs : s ≫ E.i = h := E.isKernel.lift_fst _ _ _
  let e := splitTorusPointsEquiv (Sp k) E.X (𝟙_ (Over (Sp k)))
  obtain ⟨d, hd⟩ := GlobalTheory.TorsionLift.exists_char_root (Module.Free.chooseBasis ℤ E.X) m (e s)
    fun i => exists_root_unit m hm _
  refine ⟨e.symm d ≫ E.i * g', ?_⟩
  rw [mul_pow, ← hi, ← map_pow, ← map_pow, hd, MulEquiv.symm_apply_apply, hi, hs]
  exact inv_mul_cancel_right x (g' ^ m)

end GlobalTheory.SemiAbSurj

namespace GlobalTheory.SemiAbSurj

theorem surjective_pow : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ m : ℕ, m ≠ 0 → Surjective ((𝟙 G) ^ m : G ⟶ G).left := by
  intro S G _ _ hG m hm
  have hfl := (GlobalTheory.SemiAbMulFlat.flat_and_locallyQuasiFinite_pow S G hG m hm).1
  haveI := hG.smooth
  refine ⟨fun x => ?_⟩
  let K := AlgebraicClosure (S.residueField (G.hom x))
  let t : Sp K ⟶ S := spMap (algebraMap (S.residueField (G.hom x)) K) ≫ S.fromSpecResidueField (G.hom x)
  have ht : G.hom x = t (IsLocalRing.closedPoint K) := (Scheme.fromSpecResidueField_apply _ _).symm
  let B := (Over.pullback t).obj G
  have hP := GlobalTheory.AbelianLimit.isPullback_pow (isGrpPullback_pullback G t) m
  haveI : LocallyOfFiniteType B.hom := inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom t))
  haveI : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
  haveI : Flat ((𝟙 B) ^ m : B ⟶ B).left := MorphismProperty.of_isPullback hP hfl
  haveI : LocallyOfFiniteType (((𝟙 B) ^ m : B ⟶ B).left ≫ B.hom) := by rw [Over.w]; infer_instance
  haveI : LocallyOfFiniteType ((𝟙 B) ^ m : B ⟶ B).left := locallyOfFiniteType_of_comp _ B.hom
  haveI : LocallyOfFinitePresentation ((𝟙 B) ^ m : B ⟶ B).left := inferInstance
  obtain ⟨E⟩ := hG.fibres K t
  have hs : Surjective ((𝟙 B) ^ m : B ⟶ B).left := by
    refine surjective_of_rationalPoints _ fun y => ?_
    obtain ⟨z, hz⟩ := exists_pow_eq_of_torusExtension B E m hm y
    exact ⟨z, by rw [MonObj.comp_pow, Category.comp_id, hz]⟩
  obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback (.of_hasPullback G.hom t) x _ ht
  obtain ⟨z, rfl⟩ := ((𝟙 B) ^ m : B ⟶ B).left.surjective y
  exact ⟨pullback.fst G.hom t z,
    (congrArg (fun g => g z) (GlobalTheory.AbelianLimit.pow_comm (isGrpPullback_pullback G t) m)).symm.trans hy⟩

end GlobalTheory.SemiAbSurj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianMulNatSurjectiveStatement
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelian_mul_nat_surjective : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ m : ℕ, m ≠ 0 → Surjective ((𝟙 G) ^ m : G ⟶ G).left := by
  first | exact @GlobalTheory.SemiAbSurj.surjective_pow | exact GlobalTheory.SemiAbSurj.surjective_pow | (intros; apply GlobalTheory.SemiAbSurj.surjective_pow <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearBarGoodPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearBarGoodPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.LinBarAt

theorem locCo_form' {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : Darboux B κ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (x u : W) :
    (GlobalTheory.LatVac.locCo co v x).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v u).2 -
      (GlobalTheory.LatVac.locCo co v u).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v x).2 = evFin F v (B x u) := by
  rw [co.form]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [GlobalTheory.LatVac.locCo, dotProduct, map_sum, map_mul, map_sub]

theorem locCo_surj' {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : Darboux B κ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (w : (κ → Fv F v) × (κ → Fv F v)) : ∃ u : W, At (evFin F v) u ∧ GlobalTheory.LatVac.locCo co v u = w := by
  refine ⟨co.e.symm (fun k => GlobalTheory.LatVac.liftV v (w.1 k), fun k => GlobalTheory.LatVac.liftV v (w.2 k)), ?_, ?_⟩
  · intro a ha
    rw [← LinearEquiv.map_smul, ← co.e.symm.map_zero]
    congr 1
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · exact GlobalTheory.LatVac.at_liftV v _ a ha
    · exact GlobalTheory.LatVac.at_liftV v _ a ha
  · refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;>
      simp [GlobalTheory.LatVac.locCo, GlobalTheory.LatVac.evFin_liftV]

theorem at_symp' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n d : ℕ} (JA : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)}
    (x u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (hx : At (evFin F v) x) :
    At (evFin F v) (symp (R := AF F) (cA σ) (-1) JA JB x u) := by
  intro a ha
  have h := GlobalTheory.LatVac.symp_smul_smul σ JA JB (-1) a 1 x u
  rw [hx a ha, one_smul, mul_one, GlobalTheory.VacIndic.symp_zero_left] at h
  rw [smul_eq_mul]
  exact h.symm

end GlobalTheory.LinBarAt

namespace GlobalTheory.LinBarAt

theorem exists_isLinBar_at : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v →
    ∀ t : E →ₐ[F] Fv F v, ∃ ι, G.M'.IsLinBar B.ψ t 1 1 ι := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hTr v hv t
  obtain ⟨uT, uM, hT, hM, hspan, hsymp⟩ := (GlobalTheory.T.exists_local_unipotent_additive) F E σ B a a' G X om om' hTr v t
  have hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ v) := GlobalTheory.VacAny.continuous_psiV hTr.base.std.1 v
  have hunr : PsiUnr B.ψ v := (GlobalTheory.T.psi_unramified_away_different) F B.ψ hTr.base.std v (GlobalTheory.SplitFullyUnr.not_le_differentIdeal v hv.2)
  have hunr' : ∀ x : Fv F v, (∀ y ∈ 𝒪[Fv F v], GlobalTheory.LatVac.psiAt B.ψ v (x * y) = 1) ↔
      x ∈ 𝒪[Fv F v] := by
    intro x
    simp only [GlobalTheory.FinPl.SplitPoint.mem_integer_iff]
    exact hunr x
  have hcoM : ∀ z, coAt G t (uM z) = 0 := fun z => coAt_eq_zero G t _ (hM z).2.1
  haveI : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F _).injective
  obtain ⟨ι, hbij, htr, hmu⟩ := GlobalTheory.T.stoneVonNeumann_schwartzBruhat_transverseLagrangians (GlobalTheory.LatVac.psiAt B.ψ v) hψc hunr'
    ((GlobalTheory.LatVac.locCo G.M'.co v).comp uT) ((GlobalTheory.LatVac.locCo G.M'.co v).comp uM)
    (fun Y Y' => by
      simp only [AddMonoidHom.comp_apply]
      rw [locCo_form']
      unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA incM
      rw [hsymp _ _ (hT Y).1 (hT Y').1, (hT Y).2.1, (hT Y').2.1]
      simp)
    (fun z z' => by
      simp only [AddMonoidHom.comp_apply]
      rw [locCo_form']
      unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA incM
      rw [hsymp _ _ (hM z).1 (hM z').1, hcoM, hcoM]
      simp)
    (fun Y z => by
      simp only [AddMonoidHom.comp_apply]
      rw [locCo_form']
      unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA incM
      rw [hsymp _ _ (hT Y).1 (hM z).1, (hT Y).2.1, (hT Y).2.2, (hM z).2.2, hcoM]
      simp)
    (fun w => by
      obtain ⟨u, hu, rfl⟩ := locCo_surj' G.M'.co v w
      obtain ⟨Y, z, rfl⟩ := hspan u hu
      exact ⟨Y, z, by simp only [AddMonoidHom.comp_apply, map_add (f := _)]⟩)
  have hφ₁ : ∀ (u : Matrix (Fin a') (Fin (a + a')) (AE F E)), At (evFin F v) u →
      ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ₁, Acts (evFin F v) (G.M'.co.rho B.ψ u) φ φ₁ →
        φ₁ = GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v u) φ :=
    fun u hu φ hφ φ₁ hact => GlobalTheory.TensUniq.eq_of_tens_eq v φ φ₁ _ hφ fun r hr =>
      (hact r hr).symm.trans (GlobalTheory.VacBridge.rho_acts_locCo G.M'.co B.ψ v u hu φ r hr)
  refine ⟨ι, hbij, ?_, ?_⟩
  · intro u hu hu0 φ hφ φ₁ _ hact Y
    have e1 := hφ₁ u hu φ hφ φ₁ hact
    obtain ⟨Y₀, z, rfl⟩ := hspan u hu
    have hz : z = 0 := by
      have h := hu0
      rw [Matrix.map_add _ (map_add _), (hT Y₀).2.1, (hM z).2.2, zero_add, neg_eq_zero] at h
      exact h
    subst hz
    rw [map_zero, add_zero] at e1 ⊢
    show ι φ₁ Y = ι φ (Y + coAt G t (uT Y₀))
    rw [(hT Y₀).2.2, e1]
    exact congrFun (htr Y₀ φ hφ) Y
  · intro u hu hu1 φ hφ φ₁ _ hact x hx hx0
    have e1 := hφ₁ u hu φ hφ φ₁ hact
    obtain ⟨Y₀, z, rfl⟩ := hspan u hu
    have hY : Y₀ = 0 := by
      have h := hu1
      rw [Matrix.map_add _ (map_add _), (hM z).2.1, add_zero] at h
      rw [← (hT Y₀).2.2]
      exact coAt_eq_zero G t _ h
    subst hY
    rw [map_zero, zero_add] at e1 ⊢
    show ι φ₁ (coAt G t x) = _ * ι φ (coAt G t x)
    rw [e1, GlobalTheory.VacIndic.psi_of_at B.ψ (at_symp' _ _ _ x (uM z) hx)]
    conv_rhs => unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA incM
    rw [hsymp x (uM z) hx (hM z).1, hx0, hcoM,
      (hM z).2.2]
    have h2 := congrFun (hmu z φ hφ) (coAt G t x)
    simp only [AddMonoidHom.comp_apply] at h2
    rw [h2, ← GlobalTheory.LatVac.psiAt_apply]
    congr 2
    simp [Finset.sum_neg_distrib]

end GlobalTheory.LinBarAt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearBarGoodPlaceStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_bar_good_place : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v →
    ∀ t : E →ₐ[F] Fv F v, ∃ ι, G.M'.IsLinBar B.ψ t 1 1 ι := by
  first | exact @GlobalTheory.LinBarAt.exists_isLinBar_at | exact GlobalTheory.LinBarAt.exists_isLinBar_at | (intros; apply GlobalTheory.LinBarAt.exists_isLinBar_at <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfIntersectionVanishes
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Discrepancy GlobalTheory.Cartier GlobalTheory.QCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ZeroDimSystem

def comb {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)] {M : LB X} {m : ℕ}
    (t : Fin m → M.Sec) : (Fin m → k) →ₛₗ[algebraMap k Γ(X, ⊤)] M.Sec :=
  ⟨⟨fun c => ∑ i, algebraMap k Γ(X, ⊤) (c i) • t i, fun a b => by
      simp [add_smul, Finset.sum_add_distrib]⟩, fun c a => by
      simp [mul_smul, Finset.smul_sum]⟩

theorem comb_apply {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)] {M : LB X} {m : ℕ}
    (t : Fin m → M.Sec) (c : Fin m → k) :
    comb t c = ∑ i, algebraMap k Γ(X, ⊤) (c i) • t i := rfl

def vanishAt {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)] {M : LB X} {m : ℕ}
    (t : Fin m → M.Sec) (x : X) : Submodule k (Fin m → k) where
  carrier := {c | x ∉ nonzeroLocus (comb t c)}
  add_mem' := fun {a b} ha hb hx => by
    rw [map_add (f := _)] at hx
    exact (nonzeroLocus_add_le _ _ hx).elim ha hb
  zero_mem' := fun hx => by
    rw [map_zero] at hx
    exact nonzeroLocus_secZero.le hx
  smul_mem' := fun c a ha hx => by
    rw [(comb t).map_smulₛₗ] at hx
    exact ha ((nonzeroLocus_secScale _ _).le hx).2

theorem mem_vanishAt {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)] {M : LB X}
    {m : ℕ} (t : Fin m → M.Sec) (x : X) (c : Fin m → k) :
    c ∈ vanishAt t x ↔ x ∉ nonzeroLocus (comb t c) := Iff.rfl

theorem single_notMem_vanishAt {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)]
    {M : LB X} {m : ℕ} (t : Fin m → M.Sec) {x : X} {i : Fin m} (hx : x ∈ nonzeroLocus (t i)) :
    (Pi.single i 1 : Fin m → k) ∉ vanishAt t x := by
  classical
  rw [mem_vanishAt, not_not, comb_apply,
    Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp), Pi.single_eq_same, map_one,
    one_smul]
  exact hx

section Main

variable {k : Type} [Field k] [Infinite k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)]
  [AlgebraicGeometry.IsNoetherian X] {M : LB X} (hM : M.IsLB) {m : ℕ} (t : Fin m → M.Sec)
  (ht : ⨆ i, nonzeroLocus (t i) = ⊤)
  (hf : ∀ r, algebraMap k Γ(X, ⊤) r = (strHom k X).appTop ((Scheme.ΓSpecIso (.of k)).inv r))
  (hp : IsProjOver (strHom k (X := X)))
include hM ht hf hp

end Main

end GlobalTheory.ZeroDimSystem

namespace GlobalTheory

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceSiegelLawDiagonalLagrangianCharacter
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
theorem _root_.GlobalTheory.T.splitPlace_siegelLaw_diagonalLagrangian_character : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle) (ωd : GAF σ JS × GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
            Module.End ℂ (WOF F E nS (nT + nT) → ℂ)),
        IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
            (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ α : GL (Fin nT) (AF F ⊗[F] E) →* Circle,
        (∀ (h : GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)) (t : GL (Fin nT) (AF F ⊗[F] E)),
          mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) h * ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) = ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * t.1 →
          ∀ f, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
            GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (ωd (1, h) f) = (α t : ℂ) * ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (Matrix.GeneralLinearGroup.det t)) : ℝ) ^ ((Fintype.card (Fin nS) : ℝ) / 2) : ℝ) : ℂ) * GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) f) →
      ∀ f₀, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f₀ →
        GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) f₀ ≠ 0 →
      ∀ e, IsSplitIdemF σ e → ∀ t : GL (Fin nT) (AF F ⊗[F] E),
        (∀ i j, (e + cAF σ e) * (t.1 - 1) i j = (t.1 - 1) i j) → α t = χS (Matrix.GeneralLinearGroup.det t) := by
  first | exact @PositivityTheory.ThKW.lagrangian_integral_parseval | exact PositivityTheory.ThKW.lagrangian_integral_parseval | (intros; apply PositivityTheory.ThKW.lagrangian_integral_parseval <;> assumption)
end
