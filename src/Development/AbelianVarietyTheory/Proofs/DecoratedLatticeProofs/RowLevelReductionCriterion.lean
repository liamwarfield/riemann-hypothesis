module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaConstMul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisOFinsetSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteLevelDatumVectorTransformsByLevelCharacter
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunOConstMul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentMulEntryEqZeroOfCutInverse

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowLevelReductionCriterion
noncomputable section

namespace GlobalTheory.PrinFrame

section Alg

open Matrix

variable {A : Type} [CommRing A] {n : ℕ}

theorem conj_single_mem (S : Subring A) (p : S) (hp : p * p = p) (γ : GL (Fin n) A)
    (h : ∀ i j, i ≠ j → ∀ a b, (p : A) * ((γ⁻¹).1 a i * γ.1 j b) ∈ S) (i j a b : Fin n) :
    (p : A) * ((γ⁻¹).1 a i * γ.1 j b) ∈ S := by
  by_cases hij : i = j
  · subst hij
    by_cases hl : ∃ l, l ≠ i
    · obtain ⟨l, hl⟩ := hl
      have hp' : (p : A) * p = p := congrArg Subtype.val hp
      have e1 : ∑ c, γ.1 l c * (γ⁻¹).1 c l = 1 := by
        have := congrFun (congrFun γ.mul_inv l) l
        rwa [Matrix.mul_apply, Matrix.one_apply_eq] at this
      have e2 : (p : A) * ((γ⁻¹).1 a i * γ.1 i b) =
          ∑ c, ((p : A) * ((γ⁻¹).1 a i * γ.1 l c)) * ((p : A) * ((γ⁻¹).1 c l * γ.1 i b)) := by
        rw [← mul_one ((p : A) * _), ← e1, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        linear_combination (-((γ⁻¹).1 a i * γ.1 i b * γ.1 l c * (γ⁻¹).1 c l)) * hp'
      rw [e2]
      exact S.sum_mem fun c _ => S.mul_mem (h i l hl.symm a c) (h l i hl c b)
    · push Not at hl
      have e1 : (γ⁻¹).1 i i * γ.1 i i = 1 := by
        have := congrFun (congrFun γ.inv_mul i) i
        rwa [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single i (fun c _ hc => absurd (hl c) hc)
          (fun hc => absurd (Finset.mem_univ i) hc)] at this
      rw [hl a, hl b, e1, mul_one]
      exact p.2
  · exact h i j hij a b

theorem red_conj_eq_one (S : Subring A) {k : Type} [CommRing k] (ρ : S →+* k) (p : S) (hρ : ρ p = 1) (γ : GL (Fin n) A)
    (h : ∀ i j a b, (p : A) * ((γ⁻¹).1 a i * γ.1 j b) ∈ S) (y y₀ : Matrix (Fin n) (Fin n) S)
    (hy : y₀.map S.subtype = γ.1 * y.map S.subtype * (γ⁻¹).1) (h1 : y.map ρ = 1) : y₀.map ρ = 1 := by
  have e0 : ∀ {B : Type} [CommRing B] (f : S →+* B) (z : Matrix (Fin n) (Fin n) S), (z - 1).map f = z.map f - 1 := by
    intro B _ f z
    rw [Matrix.map_sub _ (map_sub f), Matrix.map_one _ (map_zero f) (map_one f)]
  have e1 : (y₀ - 1).map S.subtype = γ.1 * (y - 1).map S.subtype * (γ⁻¹).1 := by
    rw [e0, e0, hy, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.mul_inv]
  have e2 : ∀ b a, ρ ((y - 1) b a) = 0 := fun b a => by
    have := congrFun (congrFun (e0 ρ y) b) a
    rwa [h1, sub_self] at this
  rw [← sub_eq_zero, ← e0]
  ext j i
  have e3 : p * (y₀ - 1) j i = ∑ a, ∑ b, (⟨_, h i j a b⟩ : S) * (y - 1) b a := by
    apply Subtype.ext
    have := congrFun (congrFun e1 j) i
    rw [Matrix.map_apply, Matrix.mul_apply] at this
    simp only [Matrix.mul_apply, Matrix.map_apply, Subring.subtype_apply] at this
    rw [Subring.coe_mul, this]
    simp only [AddSubmonoidClass.coe_finsetSum, Subring.coe_mul, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have e4 := congrArg ρ e3
  rw [map_mul, hρ, one_mul] at e4
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, e2, mul_zero, Finset.sum_const_zero] at e4
  exact e4

theorem transv_entry (S : Subring A) (p : S) (β β₀ : GL (Fin n) A) (i j : Fin n) (z : Matrix (Fin n) (Fin n) S)
    (h : (p : A) • (β.1 * z.map S.subtype * (β⁻¹).1) =
      (p : A) • (β₀.1 * (Matrix.transvection i j (1 : S)).map S.subtype * (β₀⁻¹).1)) (a b : Fin n) :
    (p : A) * (((β₀⁻¹ * β)⁻¹).1 a i * (β₀⁻¹ * β).1 j b) ∈ S := by
  have h2 := congrArg (fun M => (β⁻¹).1 * M * β.1) h
  have e0 : (Matrix.transvection i j (1 : S)).map S.subtype = 1 + Matrix.single i j (1 : A) := by
    rw [Matrix.transvection, Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_single,
      map_one]
  have e1 : (β⁻¹).1 * (β.1 * z.map S.subtype * (β⁻¹).1) * β.1 = z.map S.subtype := by
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  have e2 : (β⁻¹).1 * (β₀.1 * (1 + Matrix.single i j (1 : A)) * (β₀⁻¹).1) * β.1 =
      1 + ((β₀⁻¹ * β)⁻¹).1 * Matrix.single i j (1 : A) * (β₀⁻¹ * β).1 := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Units.mul_inv, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      Units.inv_mul, _root_.mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul]
    simp only [Matrix.mul_assoc]
  simp only [Matrix.mul_smul, Matrix.smul_mul] at h2
  rw [e0, e1, e2] at h2
  have h3 := congrFun (congrFun h2 a) b
  have e3 : (((β₀⁻¹ * β)⁻¹).1 * Matrix.single i j (1 : A) * (β₀⁻¹ * β).1) a b =
      ((β₀⁻¹ * β)⁻¹).1 a i * (β₀⁻¹ * β).1 j b := by
    generalize ((β₀⁻¹ * β)⁻¹).1 = M
    generalize (β₀⁻¹ * β).1 = N
    simp [Matrix.mul_apply, Matrix.single, ite_and]
  simp only [Matrix.smul_apply, Matrix.add_apply, e3, smul_eq_mul, Matrix.map_apply, Subring.subtype_apply, mul_add] at h3
  rw [← sub_eq_iff_eq_add'] at h3
  rw [← h3]
  refine S.sub_mem (S.mul_mem p.2 (z a b).2) (S.mul_mem p.2 ?_)
  rw [Matrix.one_apply]
  split_ifs
  · exact S.one_mem
  · exact S.zero_mem

end Alg

end GlobalTheory.PrinFrame

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PrinFrame

variable {D : D7}


set_option maxHeartbeats 1000000 in
theorem redFn_eq_one_of_le (V : HSp D) (β β₀ : GL (Fin V.rank) (Lev.EAf D))
    (h₀ : Formalism.L2.DIV.IsFrame β₀ (Formalism.L2.Herm.crdLat V V.L0))
    (hle : ∀ κ ∈ GfC V, finE V κ ∈ Formalism.L2.DIV.St β₀ → finE V κ ∈ Formalism.L2.DIV.St β)
    (P : Formalism.L2.DIV.Pl D.host.E) (hP : ¬ Formalism.IndefR.Lev.IsConjPl P P) (x : GL (Fin V.rank) (Lev.EAf D))
    (hx : x ∈ Formalism.L2.DIV.St β) (hx₀ : x ∈ Formalism.L2.DIV.St β₀) (h1 : redFn β P x = 1) : redFn β₀ P x = 1 := by
  have hB : IsBaseFrame V β₀ (Formalism.L2.Herm.crdLat V V.L0) (1 ^ 0) := by
    refine ⟨h₀, GlobalTheory.LevelChoices.dualL_crdLat V, one_pos, fun x hx => ?_, fun x hx => ?_⟩
    · rw [pow_zero, Nat.cast_one, one_smul]
      rwa [← GlobalTheory.LevelChoices.coe_crdLat] at hx
    · rw [pow_zero, Nat.cast_one, one_smul, ← GlobalTheory.LevelChoices.coe_crdLat]
      exact hx
  obtain ⟨e, he⟩ := GlobalTheory.ParahoricLift.exists_isIdemAt hP
  obtain ⟨p, hp, hpp, hres⟩ := GlobalTheory.ParahoricLift.exists_idem_int he
  have hoff : ∀ i j, i ≠ j → ∀ a b, (p : Lev.EAf D) * (((β₀⁻¹ * β)⁻¹).1 a i * (β₀⁻¹ * β).1 j b) ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro i j hij
    have hu' : p * (Matrix.transvection i j (1 : Formalism.L2.Herm.intAf D.host.F D.host.E)).det = p := by
      rw [Matrix.det_transvection_of_ne i j hij, mul_one]
    have hmm := GlobalTheory.ParahoricLift.conj_inv_part β₀ p p _ hu' hpp
    rw [hp] at hmm
    obtain ⟨κ, hs, hκ⟩ := GlobalTheory.ParahoricLift.split_lift_fin V he.1 _ _ hmm
    have hPI : IsPrimeIdem P e (e + cA D e) := Or.inl ⟨he, rfl⟩
    obtain ⟨-, -, T3, -⟩ := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V
    have hsf := GlobalTheory.LevSplit.supp_fin V (f := e + cA D e) hs
    rw [← hp] at hκ
    have hf : GlobalTheory.LevSplit.finSw D (e + cA D e) = p + Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) p := by
      rw [RingHom.map_add (f := _), GlobalTheory.LevSplit.finSw_cA, hp]
    have hSt : finE V κ ∈ Formalism.L2.DIV.St β₀ :=
      GlobalTheory.ParahoricLift.mem_St_of_part D.sp.cm.sig V.gram _ β₀ hB.1 (GlobalTheory.ParahoricLift.hatL_selfDual hB) p p hpp
        (GlobalTheory.LevSplit.sigR_int p.2) _ hu' (finE V κ) (GlobalTheory.LevSplit.finE_mem_UA V κ) _ hf hsf hκ
    obtain ⟨z, hz⟩ := hle κ ((T3 P e _ hPI).2.2.1 κ hs) hSt
    rw [← hz] at hκ
    exact transv_entry _ p β β₀ i j z.1 hκ
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨y₀, hy₀⟩ := hx₀
  rw [redFn_frGL] at h1
  rw [← hy₀, redFn_frGL]
  have e1 : intGL D.host.F D.host.E V.rank y₀ = (β₀⁻¹ * β) * intGL D.host.F D.host.E V.rank y * (β₀⁻¹ * β)⁻¹ := by
    have e2 : β₀ * intGL D.host.F D.host.E V.rank y₀ * β₀⁻¹ = β * intGL D.host.F D.host.E V.rank y * β⁻¹ := hy₀
    rw [mul_inv_eq_iff_eq_mul, ← eq_inv_mul_iff_mul_eq] at e2
    rw [e2]
    group
  exact Units.ext (red_conj_eq_one _ (resS D.host.F P) p hres (β₀⁻¹ * β) (conj_single_mem _ p hpp _ hoff) y.1 y₀.1
    (congrArg Units.val e1) (congrArg Units.val h1))

theorem kset_iff_finE (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (β : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) (hβ : Formalism.L2.DIV.IsFrame β (Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0))
    (κ : GA D (D.sp.Y 0)) : (iotaX X h κ).2 ∈ X.B.I.Kset ↔ finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St β := by
  have key : ∀ (I : AutInst) (hI : I = Formalism.L2.SG.InstExistsPf.instOf D),
      (castGA hI.symm (Formalism.IndefR.RationalEmbedding.iota D κ)).2 ∈ I.Kset ↔ finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St β := by
    intro I hI
    subst hI
    have hL : (Formalism.L2.SG.InstExistsPf.instOf D).L = Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0 :=
      Formalism.L2.SG.InstExistsPf.Lv_eq_map D
    have e := Formalism.L2.SG.EvalTIota.finE_brg_i (Formalism.IndefR.RationalEmbedding.iota D κ)
    have e2 : Lev.finE (D.sp.Y 0) κ = ((Formalism.IndefR.RationalEmbedding.iota D κ).2.1 : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) :=
      (congrArg (Lev.finE (D.sp.Y 0)) ((Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply κ)).symm.trans e
    have hx := GlobalTheory.FlagBasis.kset_iff (Formalism.L2.SG.InstExistsPf.instOf D) (β := β) (hL ▸ hβ) (Formalism.IndefR.RationalEmbedding.iota D κ).2
    generalize Lev.finE (D.sp.Y 0) κ = y at e2 ⊢
    subst e2
    exact hx
  exact key X.B.I h

theorem edgeSum_symEdge_one {k : Type} [CommRing k] {n : ℕ} (ρ l : ℕ) : edgeSum (symEdge ρ l) (1 : GL (Fin n) k) = 0 := by
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  split_ifs with h
  · refine Matrix.one_apply_ne ?_
    rintro rfl
    unfold symEdge at h
    omega
  · rfl

theorem rowChi_eq_one : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), GlobalTheory.Core.Mi.IdE X → ∀ (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)), IsTypePlaces Pg → (∃ e, IsIdemSum e Pg) → ∀ β : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D), (∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧ finE (D.sp.Y 0) κ ∈ St β) ↔ ((iotaX X h κ).1 = 1 ∧ (iotaX X h κ).2 ∈ X.B.I.Kset)) → ∀ κ ∈ rowJ X h, (∀ PP ∈ Pg, redFn β PP (finE (D.sp.Y 0) κ) = 1) → rowChi X h κ = 1 := by
  intro D X h _ Pg hPg hIdem β hβ κ hκ hred
  have hnc := GlobalTheory.T.genusTypePlaceSet_not_conjugatePlaces Pg hPg hIdem
  have hψ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, ∃ ψ : AddChar (kP PP) ℂ, ψ ≠ 1 := fun PP => by
    haveI := PP.isPrime
    obtain ⟨ψ, hψ⟩ := (AddChar.exists_apply_ne_zero (α := kP PP) (a := 1)).2 one_ne_zero
    exact ⟨ψ, fun e => hψ (by rw [e]; rfl)⟩
  choose ψ0 hψ0 using hψ
  obtain ⟨β₀, h₀, hK⟩ := GlobalTheory.SeeConjRead.read_fin X h Pg hPg hnc ψ0 fun PP _ => hψ0 PP
  have hle : ∀ κ ∈ GfC (D.sp.Y 0), finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St β₀ → finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St β :=
    fun κ h1 h2 => ((hβ κ).2 ⟨(GlobalTheory.SeeConjRead.iotaX_fst_eq_one_iff X h κ).2 h1, (kset_iff_finE X h β₀ h₀ κ).2 h2⟩).2
  have hS₀ := ((hK κ).1.1 hκ.2).1
  have hS := hle κ ((GlobalTheory.SeeConjRead.iotaX_fst_eq_one_iff X h κ).1 hκ.1) hS₀
  refine ((hK κ).2 hκ.2).trans (Finset.prod_eq_one fun PP hPP => ?_)
  rw [redFn_eq_one_of_le (D.sp.Y 0) β β₀ h₀ hle PP (hnc PP hPP PP hPP) _ hS hS₀ (hred PP hPP), edgeSum_symEdge_one,
    AddChar.map_zero_eq_one]

end GlobalTheory.PrinFrame

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunSplitPlaceSchroedingerModel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.LinTheta

theorem infPart_of_isSplitIdem {D : D7} {e : AE D} (he : IsSplitIdem D e) : infPart D e = 0 := by
  obtain ⟨h1, h2, v, ε, ⟨α, hε, -, -⟩, h3⟩ := he
  have h4 : e = e * algebraMap (AF D.host.F) (AE D) ε := by
    rw [← h3, mul_add, h1, h2, add_zero]
  have h5 : infPart D (algebraMap (AF D.host.F) (AE D) ε) = 0 := by
    have h6 : fstA D.host.F ε = 0 := by rw [hε]; rfl
    simp [infPart, Algebra.TensorProduct.algebraMap_apply, h6]
  rw [h4, map_mul, h5, mul_zero]

theorem isThetaFunO_placeModel (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)
    (ΛS : Lat S) (ΛT : Lat T)
    (e : AE D) (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ))
    (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (he : IsSplitIdem D e) (hf : IsThetaFunO ψ S T f₀)
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e
      (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Tm)
    (Φ : WO S T → ℂ)
    (hΦ : IsSBHalf e (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      fun _ => True) Φ) : IsThetaFunO ψ S T (Tm Φ) := by
  letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hS
  letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hT
  exact GlobalTheory.DiagLiftFix.isTheta_placeModel hψ inferInstance inferInstance he.1 he.2.1 (infPart_of_isSplitIdem he) hf Tm hTm Φ hΦ

end GlobalTheory.LocMod.LinTheta
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLocalComponentsOneMulInv
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLocalComponentsOneMulInv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm

noncomputable section
namespace GlobalTheory.LocOm

theorem isLoc_one_mul_inv : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (V : HSp D) (Z : Type) [Fintype Z] [DecidableEq Z] (F : Frame k V.rank Z), p.IsLoc F 1 1 ∧ (∀ (g g' : GA D V) (gk gk' : GL Z k), p.IsLoc F g gk → p.IsLoc F g' gk' → p.IsLoc F (g * g') (gk * gk')) ∧ ∀ (g : GA D V) (gk : GL Z k), p.IsLoc F g gk → p.IsLoc F g⁻¹ gk⁻¹ := by
  intro D k _ _ _ _ p V Z _ _ F
  have hmul : ∀ g g' : GA D V, (mt V (g * g')).map p.π = (mt V g).map p.π * (mt V g').map p.π := fun g g' => by
    rw [GlobalTheory.AdelicLatMove.mt_mul, Matrix.map_mul]
  refine ⟨⟨GlobalTheory.SplitLinear.suppAt_one _ _, ?_⟩, fun g g' gk gk' h h' => ⟨GlobalTheory.SplitLinear.suppAt_mul h.1 h'.1, ?_⟩,
    fun g gk h => ⟨GlobalTheory.SplitLinear.suppAt_inv h.1, ?_⟩⟩
  · rw [GlobalTheory.AdelicLatMove.mt_one, Matrix.map_one _ (map_zero p.π) (map_one p.π), Units.val_one, Matrix.mul_one, F.βγ]
  · rw [hmul, h.2, h'.2, Units.val_mul]
    rw [Matrix.mul_assoc (F.β * gk.val), ← Matrix.mul_assoc F.γ, ← Matrix.mul_assoc F.γ, F.γβ, Matrix.one_mul]
    simp only [Matrix.mul_assoc]
  · have e1 : (mt V g⁻¹).map p.π * (F.β * gk.val * F.γ) = 1 := by
      rw [← h.2, ← hmul, inv_mul_cancel, GlobalTheory.AdelicLatMove.mt_one, Matrix.map_one _ (map_zero p.π) (map_one p.π)]
    have e2 : (F.β * gk.val * F.γ) * (F.β * (gk⁻¹).val * F.γ) = 1 := by
      rw [Matrix.mul_assoc (F.β * gk.val), ← Matrix.mul_assoc F.γ, ← Matrix.mul_assoc F.γ, F.γβ, Matrix.one_mul,
        Matrix.mul_assoc F.β, ← Matrix.mul_assoc gk.val, Units.mul_inv, Matrix.one_mul, F.βγ]
    calc (mt V g⁻¹).map p.π = (mt V g⁻¹).map p.π * ((F.β * gk.val * F.γ) * (F.β * (gk⁻¹).val * F.γ)) := by
          rw [e2, Matrix.mul_one]
      _ = F.β * (gk⁻¹).val * F.γ := by rw [← Matrix.mul_assoc, e1, Matrix.one_mul]

end GlobalTheory.LocOm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLocalComponentsOneMulInvStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitLocalComponents_one_mul_inv : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (V : HSp D) (Z : Type) [Fintype Z] [DecidableEq Z] (F : Frame k V.rank Z), p.IsLoc F 1 1 ∧ (∀ (g g' : GA D V) (gk gk' : GL Z k), p.IsLoc F g gk → p.IsLoc F g' gk' → p.IsLoc F (g * g') (gk * gk')) ∧ ∀ (g : GA D V) (gk : GL Z k), p.IsLoc F g gk → p.IsLoc F g⁻¹ gk⁻¹ := by
  first | exact @GlobalTheory.LocOm.isLoc_one_mul_inv | exact GlobalTheory.LocOm.isLoc_one_mul_inv | (intros; apply GlobalTheory.LocOm.isLoc_one_mul_inv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsModelCombL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.BiCombStable

variable {D : D7}

theorem comb_apply (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) (w : WO S T) :
    comb ψ S T c f w = ∑ x ∈ c.support, c x * (ψ (symplOH S T w x) * f (w + x)) := by
  simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

def combL (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun := comb ψ S T c
  map_add' f g := by
    funext w
    simp only [comb_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a f := by
    funext w
    simp only [comb_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring

def biCombL (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (c : WO A S →₀ ℂ) (c' : WO S A' →₀ ℂ) :
    (WO A S → WO S A' → ℂ) →ₗ[ℂ] (WO A S → WO S A' → ℂ) where
  toFun := biComb ψ A S A' c c'
  map_add' f g := by
    funext u v
    simp only [biComb, comb_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a f := by
    funext u v
    simp only [biComb, comb_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

section Loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Loc

end GlobalTheory.BiCombStable
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ToEAfMulIncAMemOfIsIdemSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IdemIntegral

theorem toEAf_mem_of_finPart_mem {D : D7} {w : AE D} (hw : finPart D w ∈ intAE D) :
    toEAf D w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  show (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E) (finPart D w) ∈ _
  generalize finPart D w = z at hw
  induction hw using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, rfl⟩ := hy
    rw [Algebra.TensorProduct.comm_tmul]
    exact GlobalTheory.PlaceDatum.tmul_mem_int ⟨x, rfl⟩ ha
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem finPart_incA_mem {D : D7} (r : 𝓞 D.host.E) : finPart D (incA D (r : D.host.E)) ∈ intAE D := by
  have : finPart D (incA D (r : D.host.E)) = (1 : Af D.host.F) ⊗ₜ[D.host.F] (r : D.host.E) := rfl
  rw [this]
  exact AddSubgroup.subset_closure ⟨1, fun v => by simp, r, rfl⟩

theorem mem_of_idemAt {D : D7} {e : AE D} {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt e PP)
    {a : D.host.E} (ha : Formalism.L2.Col.IntAt PP a) :
    toEAf D (e * incA D a) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨r, s, hs, hsa⟩ := ha
  have hs0 : s ≠ 0 := fun h => hs (h ▸ zero_mem _)
  have hsE : (s : D.host.E) ≠ 0 := by exact_mod_cast hs0
  have ha : a = ((s : D.host.E))⁻¹ * (r : D.host.E) := by
    change (s : D.host.E) * a = (r : D.host.E) at hsa
    rw [← hsa, ← mul_assoc, inv_mul_cancel₀ hsE, one_mul]
  have h1 : finPart D (e * incA D ((s : D.host.E))⁻¹) ∈ intAE D := by
    by_contra h
    exact hs ((he.2 s hs0).2 h)
  rw [ha, (incA D).map_mul, ← mul_assoc, (toEAf D).map_mul]
  exact mul_mem (toEAf_mem_of_finPart_mem h1) (toEAf_mem_of_finPart_mem (finPart_incA_mem r))

end GlobalTheory.IdemIntegral

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrincipalLevelFixesFockVectorsFiniteDatum
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrincipalLevelFixesFockVectorsFiniteDatum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PrincipalLevelFock

theorem levW_fix_ptAt : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ Q, ∀ k ∈ levW R i, ω (1, k) (ptAt R i σ BW f Q) = ptAt R i σ BW f Q := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F i t σ s P cμ cη m ω BW f₀ f c io h Q k hk
  have hr : Formalism.L2.DIV.rTup (R.βW i) (R.datWp i P) (finE (Wc D i) k) = 1 := by
    have h2 := hk.2.2
    have e : (R.datWp i R.triv).P.H = ⊥ := rfl
    rw [e] at h2
    exact Subgroup.mem_bot.1 h2
  have hk' : k ∈ levG (Wc D i) (R.βW i) (R.datWp i P) := by
    refine ⟨hk.1, hk.2.1, ?_⟩
    show Formalism.L2.DIV.rTup (R.βW i) (R.datWp i P) (finE (Wc D i) k) ∈ (R.datWp i P).P.H
    rw [hr]; exact Subgroup.one_mem _
  have hchi : levChi (Wc D i) (R.βW i) (R.datWp i P) k = 1 := by
    unfold levChi Formalism.L2.DIV.levFn
    rw [hr, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one]
    have hs : (R.datWp i P).s = 0 := rfl
    have hq : (R.datWp i P).Q = ∅ := rfl
    rw [hs, hq]
    simp
  have hz := GlobalTheory.ZetaLaw.zeta_law R F i t σ s P cμ cη m ω BW f₀ f c io h k hk'
  rw [hchi] at hz
  have hθ : IsInfFam R.θ := h.1.models.inf
  exact (GlobalTheory.FiniteFock.om_pureTensorO_of_finite R.ψ R.θ (Vc D i) (Wc D i) _ _ ω hθ h.2.2.2.2.2.1 _ _ _ _ f
    h.2.2.2.2.2.2.2.2.1 1 (Subgroup.one_mem _) k hk.1 1 hz Q).trans (one_smul ℂ _)

end GlobalTheory.PrincipalLevelFock
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrincipalLevelFixesFockVectorsFiniteDatumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalLevel_fixes_fockVectors_finiteDatum : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ Q, ∀ k ∈ levW R i, ω (1, k) (ptAt R i σ BW f Q) = ptAt R i σ BW f Q := by
  first | exact @GlobalTheory.PrincipalLevelFock.levW_fix_ptAt | exact GlobalTheory.PrincipalLevelFock.levW_fix_ptAt | (intros; apply GlobalTheory.PrincipalLevelFock.levW_fix_ptAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceSectionAddComplementMul
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitLinAt

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sec_self (p : SplitPt D k) (a : k) : p.e * p.sec a = p.sec a := by
  rw [← p.sec_pr, p.pr_sec]

theorem sec_mul (p : SplitPt D k) (a b : k) : p.sec (a * b) = p.sec a * p.sec b := by
  have h := p.sec_pr (p.sec a * p.sec b)
  rw [map_mul, p.pr_sec, p.pr_sec] at h
  rw [h, ← mul_assoc, sec_self]

theorem sec_one (p : SplitPt D k) : p.sec 1 = p.e := by
  have h := p.sec_pr 1
  rwa [map_one, mul_one] at h

theorem splitPlaceSection_add_complement_mul (p : SplitPt D k) (a b : k) :
    (p.sec a + (1 - p.e)) * (p.sec b + (1 - p.e)) = p.sec (a * b) + (1 - p.e) := by
  have he : p.e * p.e = p.e := p.split.1
  have ha := sec_self p a
  have hb := sec_self p b
  rw [sec_mul]
  linear_combination (-1 : AE D) * ha + (-1 : AE D) * hb + he

def idl (p : SplitPt D k) : kˣ →* (AE D)ˣ where
  toFun a := ⟨p.sec a + (1 - p.e), p.sec ((a⁻¹ : kˣ) : k) + (1 - p.e),
    by rw [splitPlaceSection_add_complement_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, sec_one]; ring,
    by rw [splitPlaceSection_add_complement_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, sec_one]; ring⟩
  map_one' := Units.ext (by simp only [Units.val_one, sec_one]; ring)
  map_mul' a b := Units.ext (by simp only [Units.val_mul, splitPlaceSection_add_complement_mul])

theorem idl_val (p : SplitPt D k) (a : kˣ) : ((idl p a : (AE D)ˣ) : AE D) = p.sec (a : k) + (1 - p.e) := rfl

def lam (p : SplitPt D k) (χ : (AE D)ˣ →* Circle) (r : ℝ) : kˣ →* ℂˣ where
  toFun a := Units.mk0 ((χ (idl p a) : ℂ) * ((GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D (idl p a) ^ r : ℝ) : ℂ))
    (mul_ne_zero (Circle.coe_ne_zero _)
      (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin_pos D _) r).ne'))
  map_one' := Units.ext (by simp [GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV])
  map_mul' a b := Units.ext (by
    simp only [map_mul, Units.val_mk0, Units.val_mul, Circle.coe_mul, GlobalTheory.SplitLinear.absFin_mul,
      Real.mul_rpow (GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin_pos D _).le (GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin_pos D _).le, Complex.ofReal_mul]
    ring)

theorem lam_val (p : SplitPt D k) (χ : (AE D)ˣ →* Circle) (r : ℝ) (a : kˣ) :
    ((lam p χ r a : ℂˣ) : ℂ) = (χ (idl p a) : ℂ) * ((GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D (idl p a) ^ r : ℝ) : ℂ) := rfl

end GlobalTheory.SplitLinAt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WithMuEq
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel Matrix

noncomputable section

namespace GlobalTheory.SeeSaw.MuUnits

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem Phi_eq {a t : Type} [Fintype a] [DecidableEq a] [Fintype t] [DecidableEq t] (Q Q' : TypeDatum k a)
    (hJ : Q.J = Q'.J) (hl : ∀ x (hx : x ∈ Q.J) (hx' : x ∈ Q'.J), Q.lam ⟨x, hx⟩ = Q'.lam ⟨x, hx'⟩)
    (μ μ' : kˣ →* ℂˣ) (hμ : ∀ x : kˣ, valuation k (x : k) = 1 → μ x = μ' x) (x : Matrix (a ⊕ t) a k) :
    Q.Phi t μ x = Q'.Phi t μ' x := by
  by_cases h : (∃ g ∈ Q.J, g.val = x.toRows₁) ∧ MaxM x.toRows₂
  · obtain ⟨⟨g, hg, e⟩, h2⟩ := h
    have hg' : g ∈ Q'.J := hJ ▸ hg
    rw [Q.Phi_of_mem μ ⟨g, hg⟩ e h2, Q'.Phi_of_mem μ' ⟨g, hg'⟩ e h2, hl g hg hg',
      hμ _ (valuation_det_of_mem_KO (Q.le_KO hg))]
  · have h' : ¬ ((∃ g ∈ Q'.J, g.val = x.toRows₁) ∧ MaxM x.toRows₂) := by rwa [← hJ]
    rw [not_not.1 (mt (Q.Phi_ne_zero_iff μ).1 h), not_not.1 (mt (Q'.Phi_ne_zero_iff μ').1 h')]

theorem iter_eq {r t : Type} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] (P : TypeDatum k r)
    (μ μ' : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (hμ' : ∀ j, IsTame (μ' j))
    (h : ∀ j (x : kˣ), valuation k (x : k) = 1 → μ j x = μ' j x) (j : ℕ) :
    (P.iter t μ hμ j).J = (P.iter t μ' hμ' j).J ∧ ∀ x (hx : x ∈ (P.iter t μ hμ j).J) (hx' : x ∈ (P.iter t μ' hμ' j).J),
      (P.iter t μ hμ j).lam ⟨x, hx⟩ = (P.iter t μ' hμ' j).lam ⟨x, hx'⟩ := by
  induction j with
  | zero => exact ⟨rfl, fun _ _ _ => rfl⟩
  | succ j ih =>
    obtain ⟨hJ, hl⟩ := ih
    set Q := P.iter t μ hμ j
    set Q' := P.iter t μ' hμ' j
    have hS : Q.stepJ t = Q'.stepJ t := by
      ext g; rw [TypeDatum.mem_stepJ, TypeDatum.mem_stepJ, hJ]
    refine ⟨?_, fun x hx hx' => ?_⟩
    · rw [TypeDatum.iter_succ, TypeDatum.iter_succ]
      change (Q.stepJ t).comap _ = (Q'.stepJ t).comap _
      rw [hS]
    · have hx1 : (reGL (ixSucc r t j)).symm x ∈ Q.stepJ t := hx
      have hx1' : (reGL (ixSucc r t j)).symm x ∈ Q'.stepJ t := hx'
      change (Q.step t (μ (j + 1)) (hμ _)).lam ⟨_, hx1⟩ = (Q'.step t (μ' (j + 1)) (hμ' _)).lam ⟨_, hx1'⟩
      have hg' : ((Q.corner ⟨_, hx1⟩ : Q.J) : GL _ k) ∈ Q'.J := hJ ▸ (Q.corner ⟨_, hx1⟩).2
      refine (Q.step_lam _ _ ⟨_, hx1⟩ (Q.corner ⟨_, hx1⟩) (Q.corner_val _)).trans
        (Eq.trans ?_ (Q'.step_lam _ _ ⟨_, hx1'⟩ ⟨_, hg'⟩ (Q.corner_val _)).symm)
      rw [hl _ (Q.corner ⟨_, hx1⟩).2 hg',
        h _ _ (valuation_det_of_mem_KO (Q.le_KO (Q.corner ⟨_, hx1⟩).2)), h _ _ (valuation_det_of_mem_KO hx1.1)]

theorem withMu_eq (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ)
    (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) :
    (∀ j (x : kˣ), valuation k (x : k) = 1 → μ j x = S.μ j x) →
      (∀ j a H, ((withMu S μ hμ).T t).Phi j a H = (S.T t).Phi j a H) ∧
      ∀ j a H, (((withMu S μ hμ).T t).lev j a H).J = ((S.T t).lev j a H).J ∧
        ∀ x hx hx', (((withMu S μ hμ).T t).lev j a H).lam ⟨x, hx⟩ = ((S.T t).lev j a H).lam ⟨x, hx'⟩ := by
  intro h
  have E := iter_eq (t := t) S.P μ S.μ hμ S.tame h
  refine ⟨fun j a H => funext fun x => ?_, fun j a H => ⟨?_, fun x hx hx' => ?_⟩⟩
  · change (S.P.iter t μ hμ j).Phi t (μ (j + 1)) _ = (S.P.iter t S.μ S.tame j).Phi t (S.μ (j + 1)) _
    exact Phi_eq _ _ (E j).1 (E j).2 _ _ (h (j + 1)) _
  · change (S.P.iter t μ hμ j).J.comap _ = (S.P.iter t S.μ S.tame j).J.comap _
    rw [(E j).1]; rfl
  · exact (E j).2 _ hx hx'

end GlobalTheory.SeeSaw.MuUnits
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SkewAdjointSimilitudeExchangesHalves
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SkewAdjointSimilitudeExchangesHalves
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KappaHalf

variable {D : D7}

theorem isHalf_iff_smul {m n : ℕ} (e : AE D) (u : Mx D m n) : IsHalf e u ↔ e • u = u := by
  constructor
  · intro h; ext i j; rw [Matrix.smul_apply, smul_eq_mul, h i j]
  · intro h i j; have := congrFun (congrFun h i) j; rwa [Matrix.smul_apply, smul_eq_mul] at this

theorem isHalf_mul_left {k m n : ℕ} {e : AE D} (A : Mx D k m) {u : Mx D m n} (hu : IsHalf e u) :
    IsHalf e (A * u) := by
  rw [isHalf_iff_smul] at hu ⊢
  rw [← Matrix.mul_smul, hu]

theorem isHalf_mul_right {k m n : ℕ} {e : AE D} {u : Mx D k m} (B : Mx D m n) (hu : IsHalf e u) :
    IsHalf e (u * B) := by
  rw [isHalf_iff_smul] at hu ⊢
  rw [← Matrix.smul_mul, hu]

theorem isHalf_smul {m n : ℕ} {e : AE D} (c : AE D) {u : Mx D m n} (hu : IsHalf e u) :
    IsHalf e (c • u) := by
  rw [isHalf_iff_smul] at hu ⊢
  rw [smul_comm, hu]

theorem isHalf_adj_of_cA {m n : ℕ} {e : AE D} {z : Mx D m n} (hz : IsHalf (cA D e) z) :
    IsHalf e (adj z) := by
  intro i j
  simp only [adj, Matrix.transpose_apply, Matrix.map_apply]
  conv_lhs => rw [← GlobalTheory.DualPairCheck.cA_cA e]
  rw [← map_mul, hz j i]

theorem isHalf_cA_adj {m n : ℕ} {e : AE D} {z : Mx D m n} (hz : IsHalf e z) :
    IsHalf (cA D e) (adj z) := by
  intro i j
  simp only [adj, Matrix.transpose_apply, Matrix.map_apply]
  rw [← map_mul, hz j i]

theorem isHalf_ofAdj {L S : HSp D} {e : AE D} {z : Mx D L.rank S.rank} (hz : IsHalf e (adj z)) :
    IsHalf e (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S z) := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj
  exact isHalf_smul _ (isHalf_mul_left _ (isHalf_mul_right _ hz))

theorem ofAdj_rat_mul_half : ∀ (D : D7) (L S L'' : HSp D) (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (e : AE D) (y : WO S L''), (IsHalf (cA D e) y → IsHalf e (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L''.rank) * y))) ∧ (IsHalf e y → IsHalf (cA D e) (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L''.rank) * y))) := by
  intro D L S L'' τ e y
  exact ⟨fun h => isHalf_ofAdj (isHalf_adj_of_cA (isHalf_mul_left _ h)),
    fun h => isHalf_ofAdj (isHalf_cA_adj (isHalf_mul_left _ h))⟩

end GlobalTheory.KappaHalf

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SkewAdjointSimilitudeExchangesHalvesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skewAdjointSimilitude_exchanges_halves : ∀ (D : D7) (L S L'' : HSp D) (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (e : AE D) (y : WO S L''), (IsHalf (cA D e) y → IsHalf e (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L''.rank) * y))) ∧ (IsHalf e y → IsHalf (cA D e) (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L''.rank) * y))) := by
  first | exact @GlobalTheory.KappaHalf.ofAdj_rat_mul_half | exact GlobalTheory.KappaHalf.ofAdj_rat_mul_half | (intros; apply GlobalTheory.KappaHalf.ofAdj_rat_mul_half <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LambdaValueEdgeSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open ValuativeRel

namespace GlobalTheory.ChainChar

theorem char_of_red {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {O : Type} [CommRing O] (I : Ideal O) (π : O →+ k) {s κ r : ℕ} (hr : r = κ + (s + 1))
    (S : GlobalTheory.SymChain.SymData k s κ) (x : S.P.J) (g : GL (Fin r) (O ⧸ I))
    (hx : ∀ (a b : Fin κ ⊕ Fin (s + 1)) (a' b' : Fin r), a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a →
      b'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ b → ∀ z : O, Ideal.Quotient.mk I z = g.val a' b' →
      valuation k ((x : GL (Fin κ ⊕ Fin (s + 1)) k).val a b - π z) < 1)
    (z : O) (hz : Ideal.Quotient.mk I z = edgeSum (GlobalTheory.chainEdge κ) g) :
    ((S.P.lam x : ℂˣ) : ℂ) = (S.ψ (((S.ϖ⁻¹ : kˣ) : k) * π z) : ℂ) := by
  subst hr
  set X := (x : GL (Fin κ ⊕ Fin (s + 1)) k).val with hX
  let e : Fin κ ⊕ Fin (s + 1) ≃ Fin (κ + (s + 1)) := finSumFinEquiv
  have he : ∀ a, (e a).val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a := by
    rintro (a | a) <;> simp [e, GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos]
  choose l hl using fun a b => Ideal.Quotient.mk_surjective (I := I) (g.val (e a) (e b))
  have h1 : ∀ a b, valuation k (X a b - π (l a b)) < 1 := fun a b => hx a b _ _ (he a) (he b) _ (hl a b)
  have hI : ∀ p ∈ I, valuation k (π p) < 1 := by
    intro p hp
    have h2 := hx (.inr 0) (.inr 0) _ _ (he _) (he _) (l (.inr 0) (.inr 0) + p)
      (by rw [map_add (f := _), hl, Ideal.Quotient.eq_zero_iff_mem.2 hp, add_zero])
    have h3 := (valuation k).map_sub_lt (h1 (.inr 0) (.inr 0)) h2
    rwa [map_add, sub_sub_sub_cancel_left, add_sub_cancel_left] at h3
  let w : O := ∑ a, ∑ b, if GlobalTheory.chainEdge κ (e a) (e b) then l a b else 0
  let t : k := ∑ a, ∑ b, if GlobalTheory.chainEdge κ (e a) (e b) then X a b else 0
  have hw : w - z ∈ I := by
    rw [← Ideal.Quotient.eq, hz, edgeSum, ← e.sum_comp]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [w, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs
    · exact hl a b
    · exact map_zero _
  have htw : valuation k (t - π w) < 1 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [t, w, map_sum, ← Finset.sum_sub_distrib]
    refine (valuation k).map_sum_lt one_ne_zero fun a _ => (valuation k).map_sum_lt one_ne_zero fun b _ => ?_
    split_ifs
    · exact h1 a b
    · simp
  have htz : valuation k (t - π z) < 1 := by
    have h4 := (valuation k).map_add_lt htw (hI _ hw)
    rwa [map_sub, sub_add_sub_cancel] at h4
  have ht : t = GlobalTheory.RootEx.simpleSum (x : GL (Fin κ ⊕ Fin (s + 1)) k) + GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.superSum Fin.val X.toBlocks₁₁ := by
    simp only [t, Fintype.sum_sum_type, Finset.sum_add_distrib, GlobalTheory.RootEx.simpleSum, GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.superSum,
      GlobalTheory.chainEdge, he, GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos, Sum.elim_inl, Sum.elim_inr]
    have e1 : ∀ (a : Fin κ) (b : Fin (s + 1)), ¬ (κ + b.val = a.val + 1 ∧ a.val + 1 ≠ κ) := fun a b => by
      have := a.2; omega
    have e2 : ∀ (a : Fin (s + 1)) (b : Fin κ), ¬ (b.val = κ + a.val + 1 ∧ κ + a.val + 1 ≠ κ) := fun a b => by
      have := b.2; omega
    have e3 : ∀ (a b : Fin κ), (b.val = a.val + 1 ∧ a.val + 1 ≠ κ) ↔ b.val = a.val + 1 := fun a b => by
      have := b.2; omega
    have e4 : ∀ (a b : Fin (s + 1)), (κ + b.val = κ + a.val + 1 ∧ κ + a.val + 1 ≠ κ) ↔ b.val = a.val + 1 := fun a b => by
      omega
    simp only [e1, e2, e3, e4, if_false, Finset.sum_const_zero, add_zero, zero_add]
    rw [add_comm]
    rfl
  have hone : S.ψ (((S.ϖ⁻¹ : kˣ) : k) * (t - π z)) = 1 := by
    refine (S.cond _).2 ?_ _ le_rfl
    have h5 := (S.unif _).1 htz
    have h6 : valuation k (((S.ϖ⁻¹ : kˣ) : k) * (S.ϖ : k)) = valuation k ((1 : kˣ) : k) := by
      rw [Units.inv_mul, Units.val_one]
    rw [← h6, map_mul, map_mul]
    exact mul_le_mul_right h5 _
  rw [S.sym.2 x, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, ← mul_add, ← ht]
  congr 1
  rw [← mul_one (S.ψ (_ * π z)), ← hone, ← AddChar.map_add_eq_mul, ← mul_add, add_sub_cancel]

end GlobalTheory.ChainChar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitarySupportedSplitPlacesEqProdLocalParts
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitarySupportedSplitPlacesEqProdLocalParts
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitDecomp

open GlobalTheory.SplitCut GlobalTheory.FinPl

variable {D : D7}

theorem real_idem_mul (y : AE D) (hy : infPart D y = 0) :
    algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0) * y = 0 := by
  refine key_gen (Module.finBasis D.host.F D.host.E) _ y fun k => ?_
  have h1 : fstA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).repr y k) = 0 := by
    rw [← GlobalTheory.InfZeroFinSum.repr_map_id (Module.finBasis D.host.F D.host.E) (fstA D.host.F) y k]
    have : Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) y = 0 := hy
    rw [this, map_zero, Finsupp.zero_apply]
  refine baseAdele_ext_infinite_finite ?_ ?_
  · rw [map_mul, h1, mul_zero, map_zero]
  · rw [map_mul, map_zero]
    exact zero_mul _

theorem entry_memAt (V : HSp D) (P : Pl D → Prop) (g : GA D V) (hg : g ∈ grpAt V P) (i j : Fin V.rank) :
    (mt V g - 1) i j ∈ idAt D P := by
  have h := congrArg (fun x : GL (Fin V.rank) (AE D ⧸ idAt D P) => x.1 i j) (show _ = (1 : GL _ _) from hg)
  change Ideal.Quotient.mk (idAt D P) (mt V g i j) = _ at h
  have h2 : Ideal.Quotient.mk (idAt D P) (mt V g i j) =
      Ideal.Quotient.mk (idAt D P) ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) := by
    rw [h, Units.val_one]; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  rw [Matrix.sub_apply]; exact Ideal.Quotient.eq.mp h2


set_option maxHeartbeats 800000 in
open GlobalTheory.LocWeil.PlaceIdem in
theorem prod_of_grpAt : ∀ (D : D7) (V : HSp D) (n : ℕ) (k : Fin n → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, GlobalTheory.FinPl.SplitPt D (k i)), Function.Injective (fun i => (q i).v) → ∀ g ∈ GlobalTheory.FinPl.grpAt V (fun p => ∃ i, p = (q i).v), ∃ h : Fin n → GA D V, (∀ i, SuppAt (q i).e V (h i)) ∧ g = ((List.finRange n).map h).prod := by
  intro D V n k _ _ _ _ q hv g hg
  set E : Fin n → AE D := fun i => algebraMap (AF D.host.F) (AE D) (eFin D.host.F (q i).v) with hEdef
  have hE : ∀ i, (q i).e + cA D (q i).e = E i := fun i => by
    obtain ⟨ε, hε, h⟩ := (q i).above
    rw [h, eFin_of_placeIdem hε]
  have hEE : ∀ i, E i * E i = E i := fun i => by
    simp only [hEdef, ← map_mul, eFin_idem]
  have hEc : ∀ i, cA D (E i) = E i := fun i => cA_algebraMap _
  have hEo : ∀ i i', i ≠ i' → E i * E i' = 0 := fun i i' hii => by
    simp only [hEdef, ← map_mul]
    rw [eFin_mul_eFin _ (fun h => hii (hv h)), map_zero]
  choose h hh using fun i => cut_exists V g (E i) (hEE i) (hEc i)
  set M := mt V g with hM
  refine ⟨h, fun i a b => ?_, ?_⟩
  · rw [hE i, hh i]
    exact idempotent_mul_cut_sub_one_entry _ (hEE i) M a b
  · apply mt_injective
    rw [mt_list_prod V h E M hh hEo _ (List.nodup_finRange n)]
    have hsum : ((List.finRange n).map E).sum = ∑ i, E i := (Fin.sum_univ_def E).symm
    rw [hsum]
    refine exists_widePullback_of_iteratedLine _ M fun a b => ?_
    have hm := entry_memAt V _ g hg a b
    unfold idAt at hm
    obtain ⟨hinf, hoff⟩ := Ideal.mem_inf.mp hm
    rw [Ideal.mem_iInf] at hoff
    have h1 := key (fun i => (q i).v) hv ((M - 1) a b) (fun u hu =>
      (RingHom.mem_ker).mp (hoff ⟨u, fun ⟨i, hi⟩ => hu ⟨i, hi.symm⟩⟩))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sub, map_one, map_sum] at h1
    have h2 := real_idem_mul ((M - 1) a b) ((RingHom.mem_ker).mp hinf)
    have h3 : (1 - ∑ i, E i) = (1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0) - ∑ i, E i) +
        algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0) := by ring
    rw [h3, add_mul, h1, h2, add_zero]

end GlobalTheory.SplitDecomp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitarySupportedSplitPlacesEqProdLocalPartsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitarySupported_splitPlaces_eq_prod_local_parts : ∀ (D : D7) (V : HSp D) (n : ℕ) (k : Fin n → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, GlobalTheory.FinPl.SplitPt D (k i)), Function.Injective (fun i => (q i).v) → ∀ g ∈ GlobalTheory.FinPl.grpAt V (fun p => ∃ i, p = (q i).v), ∃ h : Fin n → GA D V, (∀ i, SuppAt (q i).e V (h i)) ∧ g = ((List.finRange n).map h).prod := by
  first | exact @GlobalTheory.SplitDecomp.prod_of_grpAt | exact GlobalTheory.SplitDecomp.prod_of_grpAt | (intros; apply GlobalTheory.SplitDecomp.prod_of_grpAt <;> assumption)
end
end
