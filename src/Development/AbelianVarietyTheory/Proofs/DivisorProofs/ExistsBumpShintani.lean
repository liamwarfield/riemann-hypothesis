module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSphericalCuspFormWhittakerNeZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KirillovSemilocalSmoothBump
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitaryOnWeilDatumTransportAdelicSchwartz
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryCommutingHeisenbergActsFibrewise
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEisensteinLevelSubgroup

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBumpShintani
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBumpShintani
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
open scoped ContDiff

namespace GlobalTheory.JSW.BumpShintani

theorem map_comp_eq {E : Type} [Field E] [NumberField E] {a : ℕ} (w : HeightOneSpectrum (𝓞 E)) (g : GA E a) :
    GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g =
      GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) g) := by
  ext i j; rfl

theorem pInf_tl {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (l : HeightOneSpectrum (𝓞 E) →₀ (Fin a → ℕ)) :
    GeneralLinearGroup.map (pInf E) (GlobalTheory.JSW.tl ϖ l) = 1 := by
  unfold GlobalTheory.JSW.tl
  rw [map_list_prod]
  apply List.prod_eq_one
  intro x hx
  simp only [List.map_map, List.mem_map] at hx
  obtain ⟨w, _, rfl⟩ := hx
  simp

theorem loc_tl {E : Type} [Field E] [NumberField E] {a : ℕ} (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ)
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin a → ℕ)) (v : HeightOneSpectrum (𝓞 E)) (hv : v ∉ l.support) :
    GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (GlobalTheory.JSW.tl ϖ l) = 1 := by
  unfold GlobalTheory.JSW.tl
  rw [map_list_prod]
  apply List.prod_eq_one
  intro x hx
  simp only [List.map_map, List.mem_map] at hx
  obtain ⟨w, hw, rfl⟩ := hx
  have hne : v ≠ w := fun h => hv (h ▸ (Finset.mem_toList.1 hw))
  simp only [Function.comp_apply, map_comp_eq, pFin_finGL]
  exact pLoc_locGL_of_ne hne _

theorem exists_bump_shintani : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) → ∃ b : GA E (m + 1) → ℂ, b 1 = 1 ∧ (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) ∧ (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * p ∈ C) ∧ ∀ (π : CuspSub E (m + 1)) (α : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ), (∀ w ∉ S, HasSatGL w (π.locRep w) (Finset.univ.val.map (α w))) → ∃ F ∈ GlobalTheory.JSW.mspanR π, (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, F (g * finGL E (m + 1) u) = F g) ∧ (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + 1)), ∀ g, F (g * finGL E (m + 1) (locGL E (m + 1) w k)) = F g) ∧ ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) → ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) → ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GlobalTheory.JSW.whit F (p * GlobalTheory.JSW.tl ϖ l) = b p * ∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (l w) := by
  intro E _ _ _ m S hcond
  obtain ⟨b, hb1, hbN, hbC, hbU, hbS⟩ := GlobalTheory.T.exists_adelic_whittaker_equivariant_bump_mirabolic E m S
  refine ⟨b, hb1, hbN, hbC, ?_⟩
  intro π α hSat
  obtain ⟨φ, hφV, hφK, hφx⟩ := GlobalTheory.T.exists_spherical_cuspForm_whittaker_ne_zero E m S hcond π α hSat
  obtain ⟨F, hFV, hFb, hFU, hFinv, hFeig⟩ := GlobalTheory.T.kirillov_semilocal_smooth_bump E m S b hbN hbC hbU hbS π φ hφV hφx
  refine ⟨F, hFV, hFU, ?_, ?_⟩
  · intro w hw k hk g
    refine hFinv _ (pInf_finGL _) ?_ ?_ g
    · intro w' hw'
      have hne : w' ≠ w := fun h => hw (h ▸ hw')
      rw [map_comp_eq, pFin_finGL]
      exact pLoc_locGL_of_ne hne _
    · intro g'
      exact congrArg (fun ψ : Sm E (m + 1) => ψ.1 g') (hφK w hw k hk)
  · intro ϖ hϖ l hl p hp
    have hC := GlobalTheory.T.whittaker_mul_torus_iterated_factorisation E (m + 1) S hcond π α hSat φ hφV hφK ϖ hϖ l hl
    have hS : ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (GlobalTheory.JSW.tl ϖ l) = 1 :=
      fun w hw => loc_tl ϖ l w (fun h => hl w h hw)
    rw [hFeig _ _ (pInf_tl ϖ l) hS hC p hp.1, hFb p hp, mul_comm]

end GlobalTheory.JSW.BumpShintani
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBumpShintaniStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bump_shintani_alt : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) → ∃ b : GA E (m + 1) → ℂ, b 1 = 1 ∧ (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) ∧ (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * p ∈ C) ∧ ∀ (π : CuspSub E (m + 1)) (α : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ), (∀ w ∉ S, HasSatGL w (π.locRep w) (Finset.univ.val.map (α w))) → ∃ F ∈ GlobalTheory.JSW.mspanR π, (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, F (g * finGL E (m + 1) u) = F g) ∧ (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + 1)), ∀ g, F (g * finGL E (m + 1) (locGL E (m + 1) w k)) = F g) ∧ ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) → ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) → ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GlobalTheory.JSW.whit F (p * GlobalTheory.JSW.tl ϖ l) = b p * ∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (l w) := by
  first
  | exact @GlobalTheory.JSW.BumpShintani.exists_bump_shintani
  | exact GlobalTheory.JSW.BumpShintani.exists_bump_shintani
  | (intros; apply GlobalTheory.JSW.BumpShintani.exists_bump_shintani <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactArchOperatorPreservesFockVacua
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactArchOperatorPreservesFockVacua
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.KInfVac

open GlobalTheory.RealLift GlobalTheory.KInfPol

theorem gaussD_of_kInf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ k ∈ KInf σ W B.emb,
    ∀ A : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d), (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) ⇑f ⇑(A f)) →
    ∀ g : SInf F (Fin n × Fin d), GlobalTheory.ThK.EvAt0.PolD.GaussD M B.emb g → GlobalTheory.ThK.EvAt0.PolD.GaussD M B.emb (A g) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP k hk A hA f₀ hf₀
  have hB := hP.base
  have hw := hP.weil
  rw [← GlobalTheory.ThK.EvAt0.PolEv.isGauss_iff hB.std] at hf₀ ⊢
  obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ _ _ _ B.ψ _ _ M.co hB.std
  have hL := actsLaws F (Fin n × Fin d)
  have hSD : ∀ u, At (evI F) u → ∀ φ, SD (M.heisLine B.ψ u) φ (D u φ) := fun u hu φ => (hD u hu φ).1
  have hAD : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine B.ψ u) φ (D u φ) :=
    fun u hu φ => (hL φ _ φ).1 _ (heisLine_zero M B.ψ u) (hSD u hu φ)
  have hint : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin n × Fin d),
      ActsD (evI F) (M.heisLine B.ψ (u * (mat k)ᵀ)) (A φ) (A (D u φ)) :=
    fun u hu φ => (hL _ _ φ).1 _ (heisLine_zero M B.ψ _) (sd_intertwine hw k (hA φ) (hA _) (hSD u hu φ))
  have hkk : (mat k⁻¹)ᵀ * (mat k)ᵀ = 1 := by
    rw [← Matrix.transpose_mul]
    change (mat (k * k⁻¹))ᵀ = 1
    rw [mul_inv_cancel]
    exact Matrix.transpose_one
  have hcan : ∀ u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), u * (mat k⁻¹)ᵀ * (mat k)ᵀ = u := fun u => by
    rw [Matrix.mul_assoc, hkk, Matrix.mul_one]
  obtain ⟨ε, hε⟩ := hf₀
  refine ⟨ε, fun u u' hu hu' huu g g' hg hg' => ?_⟩
  have hv := at_mul_right hu (mat k⁻¹)ᵀ
  have hv' := at_mul_right hu' (mat k⁻¹)ᵀ
  have h1 := hint _ hv f₀
  have h2 := hint _ hv' f₀
  rw [hcan] at h1 h2
  have e1 := (hL _ _ _).2.2.1 _ hg h1
  have e2 := (hL _ _ _).2.2.1 _ hg' h2
  have key := hε _ _ hv hv' (fun w => ?_) _ _ (hAD _ hv f₀) (hAD _ hv' f₀)
  · rw [e1, e2, key, map_smul]
  · have hm : (mat k⁻¹).map (piInf (B.emb w)) * (mat k).map (piInf (B.emb w)) = 1 := by
      rw [← Matrix.map_mul]
      change (mat (k⁻¹ * k)).map _ = 1
      rw [inv_mul_cancel]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    have hm' : (mat k).map (piInf (B.emb w)) * (mat k⁻¹).map (piInf (B.emb w)) = 1 := mul_eq_one_comm.1 hm
    have hc : (mat k⁻¹).map (piInf (B.emb w)) * W.θ w = W.θ w * (mat k⁻¹).map (piInf (B.emb w)) := by
      calc _ = (mat k⁻¹).map (piInf (B.emb w)) * W.θ w *
            ((mat k).map (piInf (B.emb w)) * (mat k⁻¹).map (piInf (B.emb w))) := by rw [hm', Matrix.mul_one]
        _ = (mat k⁻¹).map (piInf (B.emb w)) * (W.θ w * (mat k).map (piInf (B.emb w))) *
            (mat k⁻¹).map (piInf (B.emb w)) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [← (hk.2 w).eq, ← Matrix.mul_assoc, hm, Matrix.one_mul]
    rw [Matrix.map_mul, Matrix.map_mul, huu w, Matrix.transpose_map, Matrix.smul_mul]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, hc]

end GlobalTheory.KInfVac

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactArchOperatorPreservesFockVacuaStatement
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximalCompact_archOperator_preserves_fockVacua : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ k ∈ KInf σ W B.emb,
    ∀ A : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d), (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) ⇑f ⇑(A f)) →
    ∀ g : SInf F (Fin n × Fin d), GlobalTheory.ThK.EvAt0.PolD.GaussD M B.emb g → GlobalTheory.ThK.EvAt0.PolD.GaussD M B.emb (A g) := by
  first | exact @GlobalTheory.KInfVac.gaussD_of_kInf | exact GlobalTheory.KInfVac.gaussD_of_kInf | (intros; apply GlobalTheory.KInfVac.gaussD_of_kInf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTieCoordBase
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOnBase

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section ClassSum

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem j_thetaMat_base (hB : BaseLinks R F) (j : Fin D.R.m) (t : T0)
    (y : Fin ((A.fam.L j t).dZ (liftLvl F) (liftSub R F j t)) → D.what₂.LL) :
    (R.FW j).j (sg0 D A) (coordMap R F j ((thetaMat R F j t).mulVec y)) =
      R.thG j t (R.jV j t ((A.fam.L j t).toF (liftLvl F) (liftSub R F j t) y)) := by
  have k0 := j_coordMap (R := R) (F := F) j ((thetaMat R F j t).mulVec y)
  have k1 := (R.toCx F).key_lift F.cr false hB.1 hB.2.1 j t y
  have k2 := tC_cpt (R.toCx F) F.cr false j t y
  have k3 : (R.toCx F).θ' j t ((R.toCx F).jL j t (F.cr.toL (R.toCx F).zs false j t y)) =
      Tw.mk (twAt D.what₂.embLL A.v0) (R.thG j t (R.jV j t ((A.fam.L j t).toF (liftLvl F) (liftSub R F j t) y))) := rfl
  exact k0.trans ((k1.trans k2).trans k3)

theorem eq_thetaOp_base {s : ℕ} (hOk : A.fam.Ok s) (hHV : R.models_HV) (hjV : R.models_jV) (hU : R.LUnif) (hB : BaseLinks R F)
    (i : Fin D.R.m) (t : T0) (x : Fin (OntoChain.srcDim F i t) → D.what₂.LL) {u : Fin (R.nW i) → D.what₂.LL}
    (hu : u ∈ R.WL F false i) (ha : (R.FW i).j (sg0 D A) u = R.thG i t (R.jV i t (srcF F i t x))) :
    u = thetaOp R F i t x := by
  rw [← range_coordMap] at hu
  obtain ⟨z, rfl⟩ := hu
  obtain ⟨y, rfl⟩ : ∃ y, (thetaMat R F i t).mulVec y = z := ((R.toCx F).liftMat_bij F.cr false (RealDat.kForm hU false)
    (RealDat.ewNorm false) (RealDat.nP_pos false) hB.1 hB.2.1 i t).2 z
  have hb : _ = R.thG i t (R.jV i t (srcF F i t (((A.fam.L i t).lE (liftLvl F) (liftSub R F i t)).mulVec y))) :=
    (j_thetaMat_base hB i t y).trans (congrArg (fun f => R.thG i t (R.jV i t f)) (toF_eq_srcF hOk i t y))
  have h0 := lPr_eq_zero_of_ker hOk hHV hjV i t (x - ((A.fam.L i t).lE (liftLvl F) (liftSub R F i t)).mulVec y)
    ((lift_sub i t _ _).trans (sub_eq_zero.2 (ha.symm.trans hb)))
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, BlockDat.lf_lPr_lE (blockHyp (F := F) hOk i t), Matrix.one_mulVec,
    sub_eq_zero] at h0
  rw [← h0, Matrix.mulVec_mulVec]
  rfl

theorem goodOp_classSum_base {s : ℕ} (hOk : A.fam.Ok s) {ph : Fin D.R.m → ℂ} (hG : PhasedLift R ph) (hHV : R.models_HV)
    (hjV : R.models_jV) (hHW : R.models_HW) (hU : R.LUnif) (hB : BaseLinks R F) (i : Fin D.R.m) (t : T0)
    {θ : (Fin (OnTies.srcDim A i t F.P0 F.ψ0⁻¹) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL)}
    (hθ : OnTies.IsClassSum R i t F.P0 F.ψ0⁻¹ (ph i) θ) (x : Fin (OnTies.srcDim A i t F.P0 F.ψ0⁻¹) → D.what₂.LL)
    (hx : goodOp R i (θ x) ∈ R.WL F false i) : goodOp R i (θ x) = thetaOp R F i t x := by
  refine eq_thetaOp_base hOk hHV hjV hU hB i t x hx ((hHW i _).1 ?_)
  refine (adForm_goodOp hU i _).trans ?_
  refine (congrArg (Mult.postOn _ (R.eWf i (sg0 D A))) (hθ x)).trans ?_
  exact (LinearMap.map_smul _ _ _).trans (hG i t _).symm

end ClassSum

section Tied

variable {J : CoreJ D} [inst : Algebra J.Q.c.F D.what₂.LL] {R : RealDat D A J.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

local instance runAlg (r : RunData J) : Algebra r.full.J.Q.c.F D.what₂.LL := inst

variable {fw : FWTie J R κ v₀} {hc : LawsCore J.toCore} {run : HeightOneSpectrum (𝓞 D.what₂.LL) → RunData J}
  {h : ∀ v, LawsP (run v).full.toTop} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D}
  {p : HeightOneSpectrum (𝓞 D.what₂.LL) → ℕ}
  {wL wF : HeightOneSpectrum (𝓞 D.what₂.LL) → ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {nT : ℕ}
  {ℓ : ∀ i : Fin D.R.m, G → (LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l ≃ₗ[𝓞 D.host.E] LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l)}
  {ph : Fin D.R.m → ℂ} {c : OnConst} {s : ℕ}

theorem exists_tieCoord_base {P : Type} [Group P] [Finite P] {inc : P →* G} {O : OnObj ((R.toCx F).data F.cr false) P c}
    (ht : OnObjLevelCompatibility F fw hc run h hinj EX p wL wF nT ℓ ph inc O) (hinc : F.P0 ≤ inc.range)
    (hOk : A.fam.Ok s) (h1 : R.grp_levels F) (h2 : R.grp_chiW) (hHV : R.models_HV) (hjV : R.models_jV) (hHW : R.models_HW)
    (hμ : R.tup_mu_conj) (hG : PhasedLift R ph) (hU : R.LUnif) (hB : BaseLinks R F)
    (hrat : TwistedRational R F ph) (hI : LeafIdentity O) (hT : LeafTW2 O) : ∃ w, TieCoord (withCoord O w) := by
  obtain ⟨z, act, y, ht⟩ := ht
  obtain ⟨v₁, -⟩ := exists_place3 D.what₂.LL
  let w : ∀ j, (Fin (O.nZ j) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (R.nW j) → D.what₂.LL) := fun j =>
    LinearEquiv.ofBijective (toForms (T := (run v₁).full) (R := R) (h v₁) fw j (z j))
      (toForms_bijective (T := (run v₁).full) (R := R) (h v₁) fw j (z j))
  have he : ∀ j x, w j (O.e j x) = goodOp R j (w j x) := fun j x => (ht v₁ j).1.e_eOp x
  have hZ : ∀ j x, x ∈ O.Zg j ↔ w j x ∈ R.WL F false j := fun j =>
    mem_Zg_iff h1 h2 hinc j ((ht v₁ j).1.rho_eq_of_actionPin (ht v₁ j).2) (ht v₁ j).1.U_eq (ht v₁ j).1.ψ_eq (he j)
      (ht v₁ j).1.V₀_eq
  have hM : ∀ j x, x ∈ O.Ms j ↔ w j x ∈ supLat (R.FW j) := fun j x => mem_Ms_iff (ht v₁ j).1 x
  have key : ∀ v j, ClassSumRational R j (R.mu v) F.P0 F.ψ0⁻¹ (ph j) →
      (O.θ' v j ∘ₗ O.eX v j = O.e j ∘ₗ O.θ' v j ∧
        ∀ x ∈ LinearMap.range (O.eX v j), x - O.pr v j x ∈ LinearMap.ker (O.θ' v j)) →
      IsLatIn (O.Zg j) (O.Im v j) → (withCoord O w).TjId j v (R.mu v) := fun v j hra hI hT => by
    refine coord_tuple j v (y v j) (fun x => by rw [(ht v j).1.Mt_eq]; rfl) (fun x hx => ?_) hI
    have hθ : OnTies.IsClassSum R j (R.mu v) F.P0 F.ψ0⁻¹ (ph j)
        ((w j).toLinearMap ∘ₗ O.θ' v j ∘ₗ (y v j).symm.toLinearMap) := (ht v j).1.θ'_eq hra
    have e : ((w j).toLinearMap ∘ₗ O.θ' v j ∘ₗ (y v j).symm.toLinearMap) (y v j x) = w j (O.θ' v j x) :=
      congrArg (fun u => w j (O.θ' v j u)) ((y v j).symm_apply_apply x)
    have hm : w j (O.e j (O.θ' v j x)) ∈ R.WL F false j :=
      (hZ j _).1 (hT.2.le (Submodule.subset_span ⟨_, ⟨x, hx, rfl⟩, rfl⟩))
    have := goodOp_classSum_base hOk hG hHV hjV hHW hU hB j (R.mu v) hθ (y v j x) (by rw [e, ← he]; exact hm)
    rw [e, ← he] at this
    exact this
  refine ⟨w, fun j => coord_lattice j (hZ j) (hM j), fun v hv j =>
    ⟨key v j (hrat v hv j) ((hI v hv).1 j) ((hT v hv).1 j).2.1, ?_⟩⟩
  have := key (Formalism.DivisionValues.conjPl v) j (by rw [hμ v]; exact hrat v hv j) ((hI v hv).2 j) ((hT v hv).2 j).2.1
  rwa [hμ v] at this

end Tied

section Free

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type}
  [Group P] [Finite P] {c : OnConst}

end Free

end GlobalTheory.BigOnBase

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityTensorModelVW
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityTensorModelVW
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.LFun
open ValuativeRel

noncomputable section
namespace GlobalTheory.WeilLocalityVW

theorem comm_off {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : Chars F E) (om : Rep σ Γ.V Γ.W) (om' : Rep σ Γ.V' Γ.W)
    (hTr : IsTriple Bs Γ X om om') (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.W.J)
    (hk : k ∈ UAt σ Γ.W (evFin F v)) (u : AF F) (hu : evFin F v u = 0) (p q : Fin a × Fin (a + a') → AF F)
    (Φ : (Fin a × Fin (a + a') → AF F) → ℂ) (hΦ : Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a'))) :
    om (1, k) (GlobalTheory.WeilM.schr Bs.ψ (u • p, u • q) Φ) = GlobalTheory.WeilM.schr Bs.ψ (u • p, u • q) (om (1, k) Φ) := by
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil
  set w := Γ.M.co.e.symm (p, q) with hw
  have he : Γ.M.co.e (u • w) = (u • p, u • q) := by
    rw [LinearEquiv.map_smul, hw, LinearEquiv.apply_symm_apply, Prod.smul_mk]
  have h0 : u • (mat k - 1) = 0 := hk u hu
  have hact : GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ)
      ((1, k) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.V.J × GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.W.J) (u • w) = u • w := by
    have h1 : (u • w) * (mat k)ᵀ - u • w = w * (u • (mat k - 1))ᵀ := by
      rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub,
        Matrix.mul_one, Matrix.smul_mul, smul_sub]
    rw [h0, Matrix.transpose_zero, Matrix.mul_zero, sub_eq_zero] at h1
    simp only [GlobalTheory.WeilM.actAB]
    simpa [mat] using h1
  have h2 := hW.impl (1, k) (u • w) Φ hΦ
  simp only [GlobalTheory.WeilM.Darboux.rho, he, hact] at h2
  exact h2

theorem liftV_one_mul {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (b : AF F) :
    GlobalTheory.LatVac.liftV v 1 * b = GlobalTheory.LatVac.liftV v (evFin F v b) := by
  refine Prod.ext ?_ ?_
  · exact zero_mul _
  · change GlobalTheory.AdelicU.singleFin v 1 * b.2 = GlobalTheory.AdelicU.singleFin v (evFin F v b)
    apply GlobalTheory.AdelicU.af_ext
    intro w
    rw [map_mul]
    by_cases hw : w = v
    · subst hw
      rw [GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self, one_mul]
      rfl
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne hw, GlobalTheory.AdelicU.evalV_singleFin_ne hw, zero_mul]

theorem schr_trans {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ]
    (w : κ → AF F) (Φ : (κ → AF F) → ℂ) : GlobalTheory.WeilM.schr ψ (w, 0) Φ = fun y => Φ (y + w) := by
  funext y
  simp [GlobalTheory.WeilM.schr]

theorem locality : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : Chars F E) (om : Rep σ Γ.V Γ.W) (om' : Rep σ Γ.V' Γ.W), IsTriple Bs Γ X om om' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ k ∈ UAt σ Γ.W (evFin F v), ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v),
      ∃ φ₁ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, k)) φ φ₁ := by
  intro F E _ _ _ _ _ σ a a' Bs Γ X om om' hTr v k hk φ hφ
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil
  set T := om (1, k) with hTdef
  have hkeep : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), T Φ ∈ GlobalTheory.WeilM.schA F _ :=
    fun Φ hΦ => hW.pres (1, k) Φ hΦ
  have hcomm : ∀ u : AF F, evFin F v u = 0 → ∀ p q : Fin a × Fin (a + a') → AF F,
      ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')),
        T (GlobalTheory.WeilM.schr Bs.ψ (u • p, u • q) Φ) = GlobalTheory.WeilM.schr Bs.ψ (u • p, u • q) (T Φ) :=
    fun u hu p q Φ hΦ => comm_off Bs Γ X om om' hTr v k hk u hu p q Φ hΦ
  have hfib := GlobalTheory.T.isometry_commuting_heisenberg_acts_fibrewise v Bs.ψ T hTr.base.std (GlobalTheory.PsiNontrivAt.exists_psiAt_ne_one Bs.ψ hTr.base.std) hkeep
    (fun μ hμ Φ hΦ => hW.unit μ hμ (1, k) Φ hΦ) hcomm
  have htr : ∀ u : AF F, evFin F v u = 0 → ∀ p : Fin a × Fin (a + a') → AF F,
      ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), T (fun y => Φ (y + u • p)) = fun y => T Φ (y + u • p) := by
    intro u hu p Φ hΦ
    have h := hcomm u hu p 0 Φ hΦ
    rw [smul_zero, schr_trans, schr_trans] at h
    exact h
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (Fin a × Fin (a + a')) v
  refine ⟨fun t => (R 0)⁻¹ * T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ R) (fun i => GlobalTheory.LatVac.liftV v (t i)), ?_, ?_⟩
  · have h4 := GlobalTheory.LatVac.restrict_liftV_mem_SB v _ (hkeep _ (hR φ hφ).2)
    exact (GlobalTheory.WeilM.SB _).smul_mem (R 0)⁻¹ h4
  · intro r hr
    funext y
    set u : AF F := 1 - GlobalTheory.LatVac.liftV v 1 with hudef
    have hu : evFin F v u = 0 := by simp [hudef, GlobalTheory.LatVac.evFin_liftV]
    set p : Fin a × Fin (a + a') → AF F := fun i => GlobalTheory.LatVac.liftV v (evFin F v (y i)) with hpdef
    have hyp : y + u • (-y) = p := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hudef, hpdef]
      rw [← liftV_one_mul]
      ring
    have hpat : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) p := by
      intro u' hu'
      funext i
      exact GlobalTheory.LatVac.at_liftV v _ u' hu'
    set Φ₀ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ R with hΦ₀
    set Φ₁ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ r with hΦ₁
    set Φ₂ : (Fin a × Fin (a + a') → AF F) → ℂ := (r y / R 0) • (fun w => Φ₀ (w + u • (-y))) with hΦ₂
    have hm₀ : Φ₀ ∈ GlobalTheory.WeilM.schA F _ := (hR φ hφ).2
    have hm₂ : Φ₂ ∈ GlobalTheory.WeilM.schA F _ := Submodule.smul_mem _ _ (GlobalTheory.SchwartzTranslation.schA_add_const _ _ hm₀)
    have hfz : ∀ z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → (Φ₁ - Φ₂) (y + z) = 0 := by
      intro z hz
      have e1 : r (y + z) = r y := hr.1 y z hz
      have e2 : y + z + u • (-y) = p + z := by rw [← hyp]; abel
      have hpz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) (p + z) := fun u' hu' => by
        rw [smul_add, hpat u' hu', hz u' hu', add_zero]
      have e3 : R (p + z) = R 0 := by simpa using (hR φ hφ).1 0 (p + z) hpz
      have e4 : (fun i => evFin F v ((y + z + u • (-y)) i)) = fun i => evFin F v ((y + z) i) := by
        funext i
        simp [hu]
      simp only [Pi.sub_apply, hΦ₂, hΦ₁, hΦ₀, Pi.smul_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens]
      rw [e4, e2, e3, e1]
      field_simp
      ring
    have h0 := hfib (Φ₁ - Φ₂) (sub_mem hr.2 hm₂) y hfz
    rw [map_sub, Pi.sub_apply, sub_eq_zero] at h0
    have h2 : T Φ₂ y = (r y / R 0) * T Φ₀ p := by
      rw [hΦ₂, map_smul, htr u hu (-y) Φ₀ hm₀, Pi.smul_apply, smul_eq_mul, hyp]
    rw [h0, h2]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, hpdef]
    field_simp

end GlobalTheory.WeilLocalityVW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityTensorModelVWStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRepresentationLocality_tensorModelVW : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : Chars F E) (om : Rep σ Γ.V Γ.W) (om' : Rep σ Γ.V' Γ.W), IsTriple Bs Γ X om om' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ k ∈ UAt σ Γ.W (evFin F v), ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v),
      ∃ φ₁ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, k)) φ φ₁ := by
  first | exact @GlobalTheory.WeilLocalityVW.locality | exact GlobalTheory.WeilLocalityVW.locality | (intros; apply GlobalTheory.WeilLocalityVW.locality <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairMembersMemSchwartzBruhat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairMembersMemSchwartzBruhat
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StdPairCone
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.StdPairSB

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem det_sub_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) k) (hA : ∀ i j, A i j ∈ 𝒪[k])
    (hB : ∀ i j, B i j ∈ 𝒪[k]) (p : 𝒪[k])
    (hAB : ∀ i j, valuation k (B i j - A i j) ≤ valuation k (p : k)) :
    valuation k (B.det - A.det) ≤ valuation k (p : k) := by
  let A' : Matrix (Fin n) (Fin n) 𝒪[k] := Matrix.of fun i j => ⟨A i j, hA i j⟩
  let B' : Matrix (Fin n) (Fin n) 𝒪[k] := Matrix.of fun i j => ⟨B i j, hB i j⟩
  have hA' : A = (algebraMap 𝒪[k] k).mapMatrix A' := by ext i j; rfl
  have hB' : B = (algebraMap 𝒪[k] k).mapMatrix B' := by ext i j; rfl
  have hdvd : ∀ x y : 𝒪[k], valuation k (x : k) ≤ valuation k (y : k) ↔ y ∣ x :=
    fun x y => Valuation.Integers.le_iff_dvd (Valuation.integer.integers (valuation k))
  have key : (Ideal.Quotient.mk (Ideal.span {p})).mapMatrix B' =
      (Ideal.Quotient.mk (Ideal.span {p})).mapMatrix A' := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, ← hdvd]
    simpa [A', B'] using hAB i j
  have h2 : B'.det - A'.det ∈ Ideal.span {p} := by
    rw [← Ideal.Quotient.eq, RingHom.map_det, RingHom.map_det, key]
  rw [Ideal.mem_span_singleton, ← hdvd] at h2
  rw [hA', hB', ← RingHom.map_det, ← RingHom.map_det]
  exact h2


open Classical in
def gfun (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c : ℕ) {m r : ℕ} (A : Matrix (Fin m) (Fin m) k)
    (B : Matrix (Fin m) (Fin r) k) : ℂ :=
  if h : A.det ≠ 0 ∧ IsGLO A ∧ ∀ i j, B i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) then
    (((ν (Units.mk0 _ h.1))⁻¹ : ℂˣ) : ℂ) else 0

theorem prop_of_ne {ν : kˣ →* ℂˣ} {ϖ : kˣ} {c m r : ℕ} {A : Matrix (Fin m) (Fin m) k}
    {B : Matrix (Fin m) (Fin r) k} (h : gfun ν ϖ c A B ≠ 0) :
    A.det ≠ 0 ∧ IsGLO A ∧ ∀ i j, B i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) := by
  by_contra hP
  exact h (by unfold gfun; rw [dite_eq_right hP])

theorem stable {ν : kˣ →* ℂˣ} {ϖ : kˣ} {c : ℕ} (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ)
    (hν : GlobalTheory.SplitFlip.CondLE ϖ c ν) {m r : ℕ} {A A' : Matrix (Fin m) (Fin m) k}
    {B B' : Matrix (Fin m) (Fin r) k}
    (hP : A.det ≠ 0 ∧ IsGLO A ∧ ∀ i j, B i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c))
    (hA : ∀ i j, valuation k (A' i j - A i j) ≤ valuation k ((ϖ ^ max c 1 : kˣ) : k))
    (hB : ∀ i j, valuation k (B' i j - B i j) ≤ valuation k ((ϖ ^ max c 1 : kˣ) : k)) :
    (A'.det ≠ 0 ∧ IsGLO A' ∧ ∀ i j, B' i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)) ∧
      gfun ν ϖ c A' B' = gfun ν ϖ c A B := by
  obtain ⟨hd0, ⟨hAint, hAdet⟩, hBc⟩ := hP
  have hu : valuation k (ϖ : k) < 1 := by rw [hϖ]; exact uniformizer_lt_one
  have hγc : valuation k ((ϖ ^ max c 1 : kˣ) : k) ≤ valuation k ((ϖ ^ c : kˣ) : k) := by
    simp only [Units.val_pow_eq_pow_val, map_pow]
    exact pow_le_pow_right_of_le_one' hu.le (le_max_left _ _)
  have hγ1 : valuation k ((ϖ ^ max c 1 : kˣ) : k) < 1 := by
    simp only [Units.val_pow_eq_pow_val, map_pow]
    exact pow_lt_one₀ zero_le' hu (by omega)
  have hA'int : ∀ i j, A' i j ∈ 𝒪[k] := by
    intro i j
    have h1 : valuation k (A i j) ≤ 1 := hAint i j
    rw [Valuation.mem_integer_iff, ← sub_add_cancel (A' i j) (A i j)]
    exact Valuation.map_add_le _ ((hA i j).trans hγ1.le) h1
  have hB'c : ∀ i j, B' i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) := by
    intro i j
    rw [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq, ← sub_add_cancel (B' i j) (B i j)]
    exact Valuation.map_add_le _ ((hB i j).trans hγc) (hBc i j)
  have hdiff := det_sub_le A A' hAint hA'int ⟨((ϖ ^ max c 1 : kˣ) : k), hγ1.le⟩ hA
  have hdiff1 : valuation k (A'.det - A.det) < valuation k A.det := by
    rw [hAdet]; exact lt_of_le_of_lt hdiff hγ1
  have hdet' : valuation k A'.det = 1 := by
    rw [← sub_add_cancel A'.det A.det, Valuation.map_add_eq_of_lt_right _ hdiff1, hAdet]
  have hd0' : A'.det ≠ 0 := by
    intro h; rw [h, map_zero] at hdet'; exact zero_ne_one hdet'
  refine ⟨⟨hd0', ⟨hA'int, hdet'⟩, hB'c⟩, ?_⟩
  unfold gfun
  rw [dite_eq_left ⟨hd0', ⟨hA'int, hdet'⟩, hB'c⟩, dite_eq_left ⟨hd0, ⟨hAint, hAdet⟩, hBc⟩]
  set u := Units.mk0 A.det hd0
  set u' := Units.mk0 A'.det hd0'
  have hr : ν (u⁻¹ * u') = 1 := by
    apply hν
    refine ⟨?_, ?_⟩
    · simp [u, u', hAdet, hdet']
    · have : ((u⁻¹ * u' : kˣ) : k) - 1 = A.det⁻¹ * (A'.det - A.det) := by
        simp only [u, u', Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
        rw [mul_sub, inv_mul_cancel₀ hd0]
      rw [this, map_mul, map_inv₀, hAdet, inv_one, one_mul]
      exact hdiff.trans hγc
  have hu' : u' = u * (u⁻¹ * u') := by group
  rw [hu', map_mul, hr, mul_one]

theorem isLocallyConstant_gfun {ν : kˣ →* ℂˣ} {ϖ : kˣ} {c : ℕ} (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ)
    (hν : GlobalTheory.SplitFlip.CondLE ϖ c ν) (m r : ℕ) :
    IsLocallyConstant
      (fun q : Matrix (Fin m) (Fin m) k × Matrix (Fin m) (Fin r) k => gfun ν ϖ c q.1 q.2) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  rintro ⟨A, B⟩
  have hnh : ∀ x : k, ∀ᶠ y in 𝓝 x, valuation k (y - x) ≤ valuation k ((ϖ ^ max c 1 : kˣ) : k) := by
    intro x
    have ht : Tendsto (fun y : k => y - x) (𝓝 x) (𝓝 0) := by
      simpa using (tendsto_id.sub_const x : Tendsto (fun y : k => y - x) (𝓝 x) (𝓝 (x - x)))
    exact ht (GlobalTheory.SplitWeil.cball_mem_nhds (ϖ ^ max c 1))
  have hev : ∀ᶠ q in 𝓝 (A, B),
      (∀ i j, valuation k ((q : Matrix (Fin m) (Fin m) k × Matrix (Fin m) (Fin r) k).1 i j - A i j) ≤
        valuation k ((ϖ ^ max c 1 : kˣ) : k)) ∧
      ∀ i j, valuation k (q.2 i j - B i j) ≤ valuation k ((ϖ ^ max c 1 : kˣ) : k) := by
    refine Filter.Eventually.and ?_ ?_
    · refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
      exact ((continuous_fst.matrix_elem i j).tendsto (A, B)).eventually (hnh (A i j))
    · refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
      exact ((continuous_snd.matrix_elem i j).tendsto (A, B)).eventually (hnh (B i j))
  filter_upwards [hev] with q hq
  by_cases hP : A.det ≠ 0 ∧ IsGLO A ∧ ∀ i j, B i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)
  · exact (stable hϖ hν hP hq.1 hq.2).2
  · have h0 : gfun ν ϖ c A B = 0 := by unfold gfun; rw [dite_eq_right hP]
    show gfun ν ϖ c q.1 q.2 = gfun ν ϖ c A B
    rw [h0]
    by_contra hne
    refine hP (stable hϖ hν (prop_of_ne hne) (fun i j => ?_) (fun i j => ?_)).1
    · rw [Valuation.map_sub_swap]; exact hq.1 i j
    · rw [Valuation.map_sub_swap]; exact hq.2 i j

theorem integral_of_ne {ν : kˣ →* ℂˣ} {ϖ : kˣ} {c : ℕ} (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ) {m r : ℕ}
    {A : Matrix (Fin m) (Fin m) k} {B : Matrix (Fin m) (Fin r) k} (h : gfun ν ϖ c A B ≠ 0) :
    (∀ i j, A i j ∈ 𝒪[k]) ∧ ∀ i j, B i j ∈ 𝒪[k] := by
  obtain ⟨-, ⟨hA, -⟩, hB⟩ := prop_of_ne h
  have hu : valuation k (ϖ : k) < 1 := by rw [hϖ]; exact uniformizer_lt_one
  refine ⟨hA, fun i j => ?_⟩
  rw [Valuation.mem_integer_iff]
  refine (show valuation k (B i j) ≤ valuation k ((ϖ ^ c : kˣ) : k) from hB i j).trans ?_
  simp only [Units.val_pow_eq_pow_val, map_pow]
  exact pow_le_one₀ zero_le' hu.le

end Local

end GlobalTheory.StdPairSB

theorem GlobalTheory.StdPairSB.stdPair_mem_SB : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ν : kˣ →* ℂˣ) (ϖ : kˣ)
    (c a a' : ℕ), GlobalTheory.SplitFlip.IsUnif ϖ → GlobalTheory.SplitFlip.CondLE ϖ c ν →
      stdA ν ϖ c a a' ∈ SB (Matrix (Fin a) (Fin (a + a')) k) ∧ stdB ν ϖ c a a' ∈ SB (Matrix (Fin a') (Fin (a + a')) k) := by
  intro k _ _ _ _ ν ϖ c a a' hϖ hν
  haveI := GlobalTheory.SplitWeil.t2Space k
  have hc1 : ∀ m : ℕ, Continuous fun X : Matrix (Fin m) (Fin (a + a')) k => blk₁ X := by
    intro m; exact continuous_pi fun i => continuous_pi fun j => continuous_id.matrix_elem i (Fin.castAdd a' j)
  have hc2 : ∀ m : ℕ, Continuous fun X : Matrix (Fin m) (Fin (a + a')) k => blk₂ X := by
    intro m; exact continuous_pi fun i => continuous_pi fun j => continuous_id.matrix_elem i (Fin.natAdd a j)
  have hK : ∀ m : ℕ, IsCompact (Set.univ.pi fun _ : Fin m => Set.univ.pi fun _ : Fin (a + a') => (𝒪[k] : Set k) :
      Set (Matrix (Fin m) (Fin (a + a')) k)) :=
    fun m => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => GlobalTheory.SplitWeil.isCompact_int k
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have : stdA ν ϖ c a a' = (fun q => GlobalTheory.StdPairSB.gfun ν ϖ c q.1 q.2) ∘ fun X => (blk₁ X, blk₂ X) := rfl
    rw [this]
    exact (GlobalTheory.StdPairSB.isLocallyConstant_gfun hϖ hν a a').comp_continuous ((hc1 a).prodMk (hc2 a))
  · refine HasCompactSupport.intro (hK a) fun X hX => ?_
    by_contra hne
    obtain ⟨h1, h2⟩ := GlobalTheory.StdPairSB.integral_of_ne (A := blk₁ X) (B := blk₂ X) hϖ hne
    exact hX fun i _ j _ => Fin.addCases (motive := fun j => X i j ∈ 𝒪[k]) (fun j => h1 i j) (fun j => h2 i j) j
  · have : stdB ν ϖ c a a' = (fun q => GlobalTheory.StdPairSB.gfun ν ϖ c q.1 q.2) ∘ fun Y => (blk₂ Y, blk₁ Y) := rfl
    rw [this]
    exact (GlobalTheory.StdPairSB.isLocallyConstant_gfun hϖ hν a' a).comp_continuous ((hc2 a').prodMk (hc1 a'))
  · refine HasCompactSupport.intro (hK a') fun Y hY => ?_
    by_contra hne
    obtain ⟨h2, h1⟩ := GlobalTheory.StdPairSB.integral_of_ne (A := blk₂ Y) (B := blk₁ Y) hϖ hne
    exact hY fun i _ j _ => Fin.addCases (motive := fun j => Y i j ∈ 𝒪[k]) (fun j => h1 i j) (fun j => h2 i j) j
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairMembersMemSchwartzBruhatStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StdPairCone
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardPair_members_mem_schwartzBruhat : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ν : kˣ →* ℂˣ) (ϖ : kˣ)
    (c a a' : ℕ), GlobalTheory.SplitFlip.IsUnif ϖ → GlobalTheory.SplitFlip.CondLE ϖ c ν →
      stdA ν ϖ c a a' ∈ SB (Matrix (Fin a) (Fin (a + a')) k) ∧ stdB ν ϖ c a a' ∈ SB (Matrix (Fin a') (Fin (a + a')) k) := by
  first | exact @GlobalTheory.StdPairSB.stdPair_mem_SB | exact GlobalTheory.StdPairSB.stdPair_mem_SB | (intros; apply GlobalTheory.StdPairSB.stdPair_mem_SB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactSubgroupUnitaryPointsSupportedAtPla
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactSubgroupUnitaryPointsSupportedAtPla
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix Filter Topology
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.SmallAtPlace

open IsDedekindDomain NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


omit [NumberField E] in
theorem smul_tens_single (v : HeightOneSpectrum (𝓞 F)) {u : AF F} (hu : evFin F v u = 0)
    (h1 : ∀ a b : Af F, (LinearMap.inr F (Ainf F) (Af F) (a * b) : AF F) =
      LinearMap.inr F (Ainf F) (Af F) a * LinearMap.inr F (Ainf F) (Af F) b)
    (z : Fv F v ⊗[F] E) :
    u • GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (E := E) (R' := AF F) (LinearMap.inr F (Ainf F) (Af F)) h1
      (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (singleFin v) (singleFin_mul v) z) = 0 := by
  have key : ∀ b : AF F, u * b = 0 → ∀ e : E, u • (b ⊗ₜ[F] e : AF F ⊗[F] E) = 0 := fun b hb e => by
    rw [TensorProduct.smul_tmul', smul_eq_mul, hb, TensorProduct.zero_tmul]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), smul_add, hx, hy, add_zero]
  | tmul a e =>
    let b : AF F := LinearMap.inr F (Ainf F) (Af F) (singleFin v a)
    have hb : u * b = 0 := by
      refine Prod.ext (mul_zero _) ?_
      show u.2 * singleFin v a = 0
      refine af_ext fun t => ?_
      rw [map_mul, map_zero]
      by_cases ht : t = v
      · subst ht
        have : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F t u.2 = 0 := hu
        rw [this, zero_mul]
      · rw [evalV_singleFin_ne ht, mul_zero]
    exact key b hb e


omit [NumberField E] in
theorem smul_mat_emb_sub_one (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    (x : GLoc σ J v) {u : AF F} (hu : evFin F v u = 0) :
    u • ((HA.mat (AF F) σ J (emb σ J v x)).1 - 1) = 0 := by
  ext r s
  rw [Matrix.smul_apply, Matrix.sub_apply, Matrix.zero_apply]
  have h1 : ∀ a b : Af F, (LinearMap.inr F (Ainf F) (Af F) (a * b) : AF F) =
      LinearMap.inr F (Ainf F) (Af F) a * LinearMap.inr F (Ainf F) (Af F) b :=
    fun _ _ => Prod.ext (mul_zero _).symm rfl
  have hm := GlobalTheory.AutFunCompare.mat_extH σ J (R' := AF F) (LinearMap.inr F (Ainf F) (Af F)) h1
    (embLocFin σ J v x) r s
  have hm2 := GlobalTheory.AutFunCompare.mat_extH σ J (singleFin v) (singleFin_mul v) x r s
  have e1 : (HA.mat (AF F) σ J (emb σ J v x)).1 r s = _ := hm
  have e2 : (HA.mat (Af F) σ J (embLocFin σ J v x)).1 r s = _ := hm2
  rw [e1, e2]
  set T1 := GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (E := E) (R' := AF F) (LinearMap.inr F (Ainf F) (Af F)) h1
  set T2 := GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (E := E) (singleFin v) (singleFin_mul v)
  have key : ∀ z, u • T1 (T2 z) = 0 := smul_tens_single v hu h1
  have : (1 - T1 1) * (1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) r s +
      T1 ((1 - T2 1) * (1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) r s + T2 ((HA.mat _ σ J x).1 r s)) -
      (1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) r s =
      T1 (T2 ((HA.mat _ σ J x).1 r s - (1 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) r s)) := by
    by_cases h : r = s
    · subst h
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq, Matrix.one_apply_eq, mul_one, mul_one, map_add (f := _), map_sub, map_sub, map_sub]
      abel
    · simp only [Matrix.one_apply_ne h, mul_zero, zero_add, sub_zero, map_zero]
  rw [this]
  exact key _

omit [NumberField E] in
theorem map_smul_of_eq_one {R : Type} [CommRing R] [Algebra F R] (ψ : AF F →ₐ[F] R) {a : AF F} (ha : ψ a = 1)
    (y : AF F ⊗[F] E) :
    Algebra.TensorProduct.map ψ (AlgHom.id F E) (a • y) = Algebra.TensorProduct.map ψ (AlgHom.id F E) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy]
  | tmul b e =>
    rw [TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, smul_eq_mul,
      map_mul, ha, one_mul]

omit [NumberField E] in
theorem mapH_eq_one_of_smul (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {R : Type} [CommRing R]
    [Algebra F R] (ψ : AF F →ₐ[F] R) {a : AF F} (ha : ψ a = 1) {g : GAd σ J}
    (hg : a • ((HA.mat (AF F) σ J g).1 - 1) = 0) : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.mapH σ J ψ g = 1 := by
  refine GlobalTheory.AutFunCompare.HA_ext σ J fun r s => ?_
  rw [GlobalTheory.AutFunCompare.mat_mapH]
  have h := congrArg (Algebra.TensorProduct.map ψ (AlgHom.id F E)) (congrFun (congrFun hg r) s)
  rw [Matrix.smul_apply, Matrix.sub_apply, map_smul_of_eq_one ψ ha, map_sub, Matrix.zero_apply, map_zero, sub_eq_zero] at h
  rw [h]
  show _ = (1 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) r s
  by_cases e : r = s
  · subst e; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
  · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne e, map_zero]


omit [NumberField E] in
theorem eq_emb_proj_of_smul (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    {g : GAd σ J} (hg : ∀ u : AF F, evFin F v u = 0 → u • ((HA.mat (AF F) σ J g).1 - 1) = 0) :
    g = emb σ J v (proj σ J v g) := by
  refine GAd_ext σ J (fun w => ?_) (fun u => ?_)
  · rw [projArch_emb]
    let a : AF F := ((1 : Ainf F), (0 : Af F))
    have h1 : evInf F w a = 1 := by
      show (GlobalTheory.AutFunCompare.evW w) (1 : Ainf F) = 1
      exact map_one _
    have h0 : evFin F v a = 0 := by
      show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (0 : Af F) = 0
      exact map_zero _
    exact mapH_eq_one_of_smul σ J (evInf F w) h1 (hg a h0)
  · by_cases h : u = v
    · subst h; rw [proj_emb_self]
    · rw [proj_emb_ne σ J h]
      let a : AF F := ((0 : Ainf F), singleFin u 1)
      have h1 : evFin F u a = 1 := evalV_singleFin_self u 1
      have h0 : evFin F v a = 0 := evalV_singleFin_ne (Ne.symm h) 1
      exact mapH_eq_one_of_smul σ J (evFin F u) h1 (hg a h0)

theorem exists_compact_subgroup_at_place : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E},
    (∀ x, σ (σ x) = x) → ∀ {n : ℕ} (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (U : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J)), U ∈ 𝓝 (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J) →
    ∃ K : Subgroup (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J), (∀ g ∈ K, g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ X (GlobalTheory.AdelicU.evFin F v)) ∧
      IsCompact (K : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J)) ∧
      (∃ O : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J), IsOpen O ∧ (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J) ∈ O ∧
        ∀ g ∈ O, g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ X (GlobalTheory.AdelicU.evFin F v) → g ∈ K) ∧ (K : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J)) ⊆ U := by
  intro F E _ _ _ _ _ σ hσ n X v U hU
  have heq : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) = HR (AF F) σ (X.J.map σ) := by
    have h := GlobalTheory.SiegelSet.ug_eq_hr (F := F) (J := X.J) hσ one_ne_zero
    rw [one_smul] at h
    exact h
  let e : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J ≃* GAd σ (X.J.map σ) := MulEquiv.subgroupCongr heq
  have he : Continuous e := continuous_subtype_val.subtype_mk _
  have he' : Continuous e.symm := continuous_subtype_val.subtype_mk _
  let f : GLoc σ (X.J.map σ) v →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J := e.symm.toMonoidHom.comp (emb σ (X.J.map σ) v)
  have hf : Continuous f := he'.comp (continuous_emb σ (X.J.map σ) v)
  have hW : f ⁻¹' U ∈ 𝓝 (1 : GLoc σ (X.J.map σ) v) :=
    hf.continuousAt.preimage_mem_nhds (by rw [map_one]; exact hU)
  haveI := GlobalTheory.Doubling.nonarchimedeanGroup_GLoc σ (X.J.map σ) v
  obtain ⟨V₀, hV₀⟩ := NonarchimedeanGroup.is_nonarchimedean _ hW
  haveI := isLattice_stdLattice (E := E) (n := n)
  let V₁ : Subgroup (GLoc σ (X.J.map σ) v) := (V₀ : Subgroup _) ⊓ stabLoc σ (X.J.map σ) (stdLattice E n) v
  have hV₁o : IsOpen (V₁ : Set (GLoc σ (X.J.map σ) v)) :=
    V₀.isOpen.inter (isOpen_stabLoc σ (X.J.map σ) (stdLattice E n) v)
  have hV₁c : IsCompact (V₁ : Set (GLoc σ (X.J.map σ) v)) :=
    (isCompact_stabLoc σ (X.J.map σ) (stdLattice E n) v).inter_left V₀.isClosed
  have hmat : ∀ g, (HA.mat (AF F) σ (X.J.map σ) (e g)).1 = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g := fun g => rfl
  refine ⟨V₁.map f, ?_, ?_, ⟨(proj σ (X.J.map σ) v ∘ e) ⁻¹' (V₁ : Set _),
    hV₁o.preimage ((continuous_proj σ (X.J.map σ) v).comp he), ?_, ?_⟩, ?_⟩
  · rintro _ ⟨x, -, rfl⟩ u hu
    have h := smul_mat_emb_sub_one σ (X.J.map σ) v x hu
    have h2 : (HA.mat (AF F) σ (X.J.map σ) (e (f x))).1 = (HA.mat (AF F) σ (X.J.map σ) (emb σ (X.J.map σ) v x)).1 := by
      simp [f]
    rw [← hmat, h2]
    exact h
  · rw [Subgroup.coe_map]
    exact hV₁c.image hf
  · show proj σ (X.J.map σ) v (e 1) ∈ V₁
    rw [map_one, map_one]
    exact one_mem _
  · intro g hg hgv
    refine ⟨proj σ (X.J.map σ) v (e g), hg, ?_⟩
    have h : e g = emb σ (X.J.map σ) v (proj σ (X.J.map σ) v (e g)) :=
      eq_emb_proj_of_smul σ (X.J.map σ) v fun u hu => by rw [hmat]; exact hgv u hu
    show e.symm (emb σ (X.J.map σ) v (proj σ (X.J.map σ) v (e g))) = g
    rw [← h, MulEquiv.symm_apply_apply]
  · rintro _ ⟨x, hx, rfl⟩
    exact hV₀ hx.1

end GlobalTheory.SmallAtPlace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactSubgroupUnitaryPointsSupportedAtPlaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix Filter Topology
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compactSubgroup_unitaryPoints_supportedAtPlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E},
    (∀ x, σ (σ x) = x) → ∀ {n : ℕ} (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (U : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J)), U ∈ 𝓝 (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J) →
    ∃ K : Subgroup (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J), (∀ g ∈ K, g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ X (GlobalTheory.AdelicU.evFin F v)) ∧
      IsCompact (K : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J)) ∧
      (∃ O : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J), IsOpen O ∧ (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J) ∈ O ∧
        ∀ g ∈ O, g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ X (GlobalTheory.AdelicU.evFin F v) → g ∈ K) ∧ (K : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J)) ⊆ U := by
  first | exact @GlobalTheory.SmallAtPlace.exists_compact_subgroup_at_place | exact GlobalTheory.SmallAtPlace.exists_compact_subgroup_at_place | (intros; apply GlobalTheory.SmallAtPlace.exists_compact_subgroup_at_place <;> assumption)
end
end
