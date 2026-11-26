module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepSplittingCharactersTameLevelResidue
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTransformDarbouxModelLinearInjective
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateTsumLeOfThetaLevelMultiple

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchOperatorUnitaryWSeesaw
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchOperatorUnitaryWSeesaw
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

noncomputable section

namespace GlobalTheory.ArchFactor

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def liftI (t : κ → mixedEmbedding.mixedSpace F) : κ → AF F :=
  fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t i), (0 : FiniteAdeleRing (𝓞 F) F)) : AF F)

end GlobalTheory.ArchFactor

end

namespace GlobalTheory.ArchFactor

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem evI_add' (a b : AF F) : evI F (a + b) = evI F a + evI F b :=
  map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evI_mul' (a b : AF F) : evI F (a * b) = evI F a * evI F b :=
  map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem comm_offI {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ}
    {χX χW : Chr F E} {om : Rep σ X W} (hw : M.IsWeil ψ χX χW om) (x : UA σ X.J × UA σ W.J)
    (hx1 : x.1 ∈ UAt σ X (evI F)) (hx2 : x.2 ∈ UAt σ W (evI F))
    (u : AF F) (hu : evI F u = 0) (p q : Fin n × Fin d → AF F) (Φ : (Fin n × Fin d → AF F) → ℂ)
    (hΦ : Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d)) :
    om x (GlobalTheory.WeilM.schr ψ (u • p, u • q) Φ) = GlobalTheory.WeilM.schr ψ (u • p, u • q) (om x Φ) := by
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hw
  set w := M.co.e.symm (p, q) with hw'
  have he : M.co.e (u • w) = (u • p, u • q) := by
    rw [LinearEquiv.map_smul, hw', LinearEquiv.apply_symm_apply, Prod.smul_mk]
  have h1 : u • (mat x.1 - 1) = 0 := hx1 u hu
  have h2 : u • (mat x.2 - 1) = 0 := hx2 u hu
  have e1 : mat x.1 * (u • w) = u • w := by
    have : mat x.1 * (u • w) - u • w = (u • (mat x.1 - 1)) * w := by
      rw [Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_smul, smul_sub]
    rw [h1, Matrix.zero_mul, sub_eq_zero] at this
    exact this
  have e2 : (u • w) * (mat x.2)ᵀ = u • w := by
    have : (u • w) * (mat x.2)ᵀ - u • w = w * (u • (mat x.2 - 1))ᵀ := by
      rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_sub, Matrix.transpose_one,
        Matrix.mul_sub, Matrix.mul_one, smul_sub]
    rw [h2, Matrix.transpose_zero, Matrix.mul_zero, sub_eq_zero] at this
    exact this
  have hact : GlobalTheory.WeilM.actAB (cA σ) x (u • w) = u • w := by
    simp only [GlobalTheory.WeilM.actAB]
    have := e1
    simp only [mat] at this e2
    rw [this, e2]
  have h3 := hW.impl x (u • w) Φ hΦ
  simp only [GlobalTheory.WeilM.Darboux.rho, he, hact] at h3
  exact h3

theorem schr_trans' (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ] (w : κ → AF F) (Φ : (κ → AF F) → ℂ) :
    GlobalTheory.WeilM.schr ψ (w, 0) Φ = fun y => Φ (y + w) := by
  funext y
  simp [GlobalTheory.WeilM.schr]

end GlobalTheory.ArchFactor


open GlobalTheory.ArchFactor in
theorem GlobalTheory.ArchFactor.exists_archOperator : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ h ∈ UAt σ G.W (evI F),
    ∃ T : SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')), ∀ f : SInf F (Fin a × Fin (a + a')), Acts (evI F) (om (1, h)) f (T f) := by
  intro F E _ _ _ _ _ σ a a' B G X om om' hT h hh
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hT.weil
  have hkeep : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), om (1, h) Φ ∈ GlobalTheory.WeilM.schA F _ :=
    fun Φ hΦ => hW.pres (1, h) Φ hΦ
  have h1 : (1 : UA σ G.V.J) ∈ UAt σ G.V (evI F) := by
    intro u _
    simp [mat]
  have hcomm := comm_offI hT.weil (1, h) h1 hh
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_finiteWeight_complementary_archimedeanSchwartz (F := F) (Fin a × Fin (a + a'))
  have hB : ∀ f : SInf F (Fin a × Fin (a + a')), ∃ g : SInf F (Fin a × Fin (a + a')),
      ∀ t, g t = (R 0)⁻¹ * om (1, h) (tens (evI F) (⇑f) R) (liftI t) := by
    intro f
    obtain ⟨g, hg⟩ := GlobalTheory.T.exists_schwartz_archimedeanSlice_adelicSchwartz _ (Submodule.smul_mem _ (R 0)⁻¹ (hkeep _ (hR f).2))
    exact ⟨g, fun t => by rw [hg]; rfl⟩
  choose Tf hTf using hB
  have htens_add : ∀ f g : SInf F (Fin a × Fin (a + a')),
      tens (evI F) (⇑(f + g)) R = tens (evI F) (⇑f) R + tens (evI F) (⇑g) R := by
    intro f g; funext x; simp only [tens, SchwartzMap.add_apply, Pi.add_apply]; ring
  have htens_smul : ∀ (c : ℂ) (f : SInf F (Fin a × Fin (a + a'))),
      tens (evI F) (⇑(c • f)) R = c • tens (evI F) (⇑f) R := by
    intro c f; funext x; simp only [tens, SchwartzMap.smul_apply, Pi.smul_apply, smul_eq_mul]; ring
  let T : SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')) :=
    { toFun := Tf
      map_add' := fun f g => by
        ext t
        rw [SchwartzMap.add_apply, hTf, hTf, hTf, htens_add, map_add (f := _), Pi.add_apply]; ring
      map_smul' := fun c f => by
        ext t
        rw [SchwartzMap.smul_apply, hTf, hTf, htens_smul, map_smul, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
          RingHom.id_apply]; ring }
  refine ⟨T, fun f r hr => ?_⟩
  funext y
  set T0 := om (1, h) with hT0
  set u : AF F := ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) with hudef
  have hu : evI F u = 0 := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : InfiniteAdeleRing F) = 0
    exact map_zero _
  set p : Fin a × Fin (a + a') → AF F := liftI (fun i => evI F (y i)) with hpdef
  have hyp : y + u • (-y) = p := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hudef, hpdef, liftI, evI,
      RingEquiv.symm_apply_apply]
    refine Prod.ext ?_ ?_
    · show (y i).1 + 0 * (-(y i)).1 = (y i).1
      simp
    · show (y i).2 + 1 * (-(y i)).2 = 0
      rw [one_mul]
      exact add_neg_cancel ((y i).2)
  have hpat : At (evI F) p := by
    intro u' hu'
    have h0 : u'.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu')
    funext i
    refine Prod.ext ?_ ?_
    · show u'.1 * (p i).1 = 0
      rw [h0, zero_mul]
    · show u'.2 * (p i).2 = 0
      simp [hpdef, liftI]
  set Φ₀ := tens (evI F) (⇑f) R with hΦ₀
  set Φ₁ := tens (evI F) (⇑f) r with hΦ₁
  set Φ₂ : (Fin a × Fin (a + a') → AF F) → ℂ := (r y / R 0) • (fun w => Φ₀ (w + u • (-y))) with hΦ₂
  have hm₀ : Φ₀ ∈ GlobalTheory.WeilM.schA F _ := (hR f).2
  have hm₂ : Φ₂ ∈ GlobalTheory.WeilM.schA F _ := Submodule.smul_mem _ _ (GlobalTheory.SchwartzTranslation.schA_add_const _ _ hm₀)
  have hfz : ∀ z, At (evI F) z → (Φ₁ - Φ₂) (y + z) = 0 := by
    intro z hz
    have e1 : r (y + z) = r y := hr.1 y z hz
    have e2 : y + z + u • (-y) = p + z := by rw [← hyp]; abel
    have hpz : At (evI F) (p + z) := fun u' hu' => by
      rw [smul_add, hpat u' hu', hz u' hu', add_zero]
    have e3 : R (p + z) = R 0 := by simpa using (hR f).1 0 (p + z) hpz
    have e4 : (fun i => evI F ((y + z + u • (-y)) i)) = fun i => evI F ((y + z) i) := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, evI_add', evI_mul', hu, zero_mul, add_zero]
    simp only [Pi.sub_apply, hΦ₂, hΦ₁, hΦ₀, Pi.smul_apply, smul_eq_mul, tens]
    rw [e4, e2, e3, e1]
    field_simp
    ring
  have h0 := GlobalTheory.T.heisenbergCommuting_operator_independent_of_archimedeanFibres B.ψ T0 hT.base.std hkeep (fun u hu p q Φ hΦ => hcomm u hu p q Φ hΦ) (Φ₁ - Φ₂)
    (sub_mem hr.2 hm₂) y hfz
  rw [map_sub, Pi.sub_apply, sub_eq_zero] at h0
  have htr : T0 (fun w => Φ₀ (w + u • (-y))) = fun w => T0 Φ₀ (w + u • (-y)) := by
    have h := hcomm u hu (-y) 0 Φ₀ hm₀
    rw [smul_zero, schr_trans', schr_trans'] at h
    exact h
  have h2 : T0 Φ₂ y = (r y / R 0) * T0 Φ₀ p := by
    rw [hΦ₂, map_smul, htr, Pi.smul_apply, smul_eq_mul, hyp]
  show T0 Φ₁ y = tens (evI F) (⇑(Tf f)) r y
  rw [h0, h2]
  show r y / R 0 * T0 Φ₀ p = (Tf f) (fun i => evI F (y i)) * r y
  rw [hTf]
  show r y / R 0 * T0 Φ₀ p = (R 0)⁻¹ * T0 Φ₀ p * r y
  rw [div_eq_mul_inv]
  ring
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchOperatorUnitaryWSeesawStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_archOperator_unitaryW_seesaw : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ h ∈ UAt σ G.W (evI F),
    ∃ T : SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')), ∀ f : SInf F (Fin a × Fin (a + a')), Acts (evI F) (om (1, h)) f (T f) := by
  first | exact @GlobalTheory.ArchFactor.exists_archOperator | exact GlobalTheory.ArchFactor.exists_archOperator | (intros; apply GlobalTheory.ArchFactor.exists_archOperator <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealIntertwinerLargerSourceMirrorCase
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealIntertwinerLargerSourceMirrorCase
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.RealItLarge

open GlobalTheory.Chain GlobalTheory.Chain.RealIt

theorem exists_isCoverIt_swap (p q r s : ℕ) (T₀ : GrpData (p * r + q * s) (p * s + q * r)) (T₁ : GrpData p q)
    (T₂ : GrpData r s) (F : FockData T₀ T₁ T₂) (R₁ : DSRep T₁) (R₂ : DSRep T₂) (Tm : R₁.U.H →L[ℂ] R₂.U.H →L[ℂ] F.H)
    (hI : ∀ x x' y y', inner ℂ (Tm x y) (Tm x' y') = inner ℂ x x' * inner ℂ y y')
    (hE : ∀ g h x y, F.π (g, h) (Tm x y) = Tm (R₁.U.π g x) (R₂.U.π h y)) :
    ∃ B : Pol r s p q →ₗ[ℂ] R₁.U.H →ₛₗ[starRingEnd ℂ] R₂.U.H, IsCoverIt R₂ R₁ B := by
  let A : R₁.U.H → F.H →L[ℂ] R₂.U.H := fun x => ContinuousLinearMap.adjoint (Tm x)
  have hC : ∀ x φ y, inner ℂ y (A x φ) = inner ℂ (Tm x y) φ := fun x φ y => by
    simp only [A]
    rw [ContinuousLinearMap.adjoint_inner_right]
  have hn : ∀ x y, ‖Tm x y‖ = ‖x‖ * ‖y‖ := by
    intro x y
    have h := hI x x y y
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, ← mul_pow] at h
    have h2 : ‖Tm x y‖ ^ 2 = (‖x‖ * ‖y‖) ^ 2 := by exact_mod_cast h
    exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2
  have hall : ∀ g h φ x, A (R₁.U.π g x) (F.π (g, h) φ) = R₂.U.π h (A x φ) := by
    intro g h φ x
    apply ext_inner_left ℂ
    intro y
    obtain ⟨y, rfl⟩ : ∃ y', R₂.U.π h y' = y := ⟨R₂.U.π h⁻¹ y, by
      change (R₂.U.π h * R₂.U.π h⁻¹) y = y
      rw [← map_mul]; simp⟩
    rw [hC, ← hE, GlobalTheory.Chain.CoverContr.inner_map_of_norm _ (R₂.U.isom h), hC]
    exact GlobalTheory.Chain.CoverContr.inner_map_of_norm _ (F.isom _) _ _
  have he : ∀ h φ x, A x (F.π (1, h) φ) = R₂.U.π h (A x φ) := fun h φ x => by
    simpa using hall 1 h φ x
  have hi : ∀ g φ x, A (R₁.U.π g x) (F.π (g, 1) φ) = A x φ := fun g φ x => by
    simpa using hall g 1 φ x
  let sw : Pol r s p q →ₗ[ℂ] Pol p q r s := (MvPolynomial.rename Prod.swap).toLinearMap
  have hsw : ∀ P, sw P = MvPolynomial.rename Prod.swap P := fun _ => rfl
  let B : Pol r s p q →ₗ[ℂ] R₁.U.H →ₛₗ[starRingEnd ℂ] R₂.U.H :=
    LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun P x => A x (F.ι (sw P)))
      (fun P Q x => by simp only [map_add (f := _)])
      (fun c P x => by simp only [map_smul, RingHom.id_apply])
      (fun P x x' => by simp only [A, map_add (f := _), ContinuousLinearMap.add_apply])
      (fun c P x => by simp only [A, map_smul, map_smulₛₗ, ContinuousLinearMap.smul_apply])
  have hB : ∀ P x, B P x = A x (F.ι (sw P)) := fun _ _ => rfl
  obtain ⟨-, hd1, hd2⟩ := GlobalTheory.T.fock_derived_actions_tensor_members p q r s T₀ T₁ T₂ F
  have hsym := GlobalTheory.FockSwap.swap_symmetry r s p q
  refine ⟨B, ?_, ?_, ?_, ?_, ?_⟩
  · intro P
    refine ⟨‖F.ι (sw P)‖, fun x => ?_⟩
    rw [hB]
    set φ := F.ι (sw P)
    have h := hC x φ (A x φ)
    have h1 : ‖A x φ‖ * ‖A x φ‖ ≤ ‖A x φ‖ * (‖φ‖ * ‖x‖) := by
      have := norm_inner_le_norm (𝕜 := ℂ) (Tm x (A x φ)) φ
      rw [← h, hn, inner_self_eq_norm_sq_to_K] at this
      simp at this
      nlinarith
    rcases (norm_nonneg (A x φ)).eq_or_lt with h0 | h0
    · rw [← h0]; positivity
    · exact le_of_mul_le_mul_left h1 h0
  · intro P x
    rw [R₂.ι_range, hB]
    have hf := (GlobalTheory.FockKFin.kfin_fock p q r s T₀ T₁ T₂ F
      (GlobalTheory.FockDegree.Om_Kset_homog p q r s T₀ T₁ T₂ F) (sw P)).2
    unfold KFin at *
    have : (Set.range fun k : T₂.Kset => R₂.U.π k (A x (F.ι (sw P)))) =
        (A x).toLinearMap '' Set.range fun k : T₂.Kset => F.π (1, k) (F.ι (sw P)) := by
      rw [← Set.range_comp]; congr 1; funext k; simp [he]
    rw [this, ← Submodule.map_span]
    infer_instance
  · intro x hx
    by_contra hcon
    push_neg at hcon
    have hcon' : ∀ P : Pol p q r s, A x (F.ι P) = 0 := fun P => by
      have := hcon (MvPolynomial.rename Prod.swap P)
      rwa [hB, hsw, MvPolynomial.rename_rename, Prod.swap_swap_eq, MvPolynomial.rename_id_apply] at this
    have h0 : ∀ φ, A x φ = 0 := fun φ =>
      congrFun (Continuous.ext_on F.dense (A x).continuous (continuous_const (y := (0 : R₂.U.H)))
        (by rintro _ ⟨P, rfl⟩; exact hcon' P)) φ
    have := R₂.nontriv
    obtain ⟨y, hy⟩ := exists_ne (0 : R₂.U.H)
    have h := hC x (Tm x y) y
    rw [h0, inner_zero_right, eq_comm, inner_self_eq_zero, ← norm_eq_zero, hn, mul_eq_zero,
      norm_eq_zero, norm_eq_zero] at h
    tauto
  · intro Z hZ P x
    have := (((A x).restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt (0 : ℝ) (hd2 Z hZ (sw P))
    have e1 : sw (fockAct1 r s p q Z P) = fockAct2 p q r s Z (sw P) := hsym.1 Z P
    simpa [hB, Function.comp_def, he, e1] using this
  · intro Z hZ P x
    have h1 := (((A x).restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt (0 : ℝ) (hd1 Z hZ (sw P))
    have h2 := h1.scomp_of_eq (0 : ℝ) (hasDerivAt_neg (0 : ℝ)) (by simp)
    have e2 : sw (fockAct2 r s p q Z P) = fockAct1 p q r s Z (sw P) := hsym.2.1 Z P
    have h3 : (fun t : ℝ => B P (R₁.U.π (T₁.expt (t • Z)) x)) =
        fun t : ℝ => A x (F.π (T₁.expt ((-t) • Z), 1) (F.ι (sw P))) := by
      funext t
      rw [hB, ← hi (T₁.expt (t • Z)) (F.π (T₁.expt ((-t) • Z), 1) (F.ι (sw P))) x]
      congr 1
      change _ = (F.π (T₁.expt (t • Z), 1) * F.π (T₁.expt ((-t) • Z), 1)) _
      rw [← map_mul, Prod.mk_mul_mk, ← T₁.expt_add Z hZ, add_neg_cancel, zero_smul, T₁.expt_zero,
        mul_one, Prod.mk_one_one, map_one, ContinuousLinearMap.one_apply]
    rw [h3, hB, e2]
    simpa [Function.comp_def] using h2

end GlobalTheory.Chain.RealItLarge

namespace GlobalTheory.Chain.RealItLarge

open GlobalTheory.Chain GlobalTheory.Chain.RealIt Formalism.MainNotions.SchurIrreducible

variable {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar}

theorem isParam_lamM' {t : ℕ} {al be ga de : List ℚ} (h : HypA t al be ga de) : IsParam (lamM' t al be ga de) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  have mem : ∀ e, e ∈ ga ++ de ++ al ++ be → e ∈ al ++ be ++ ga ++ de := fun e he => by
    simp only [List.mem_append] at he ⊢
    tauto
  have h' : HypA t ga de al be := by
    refine ⟨h1, by omega, h5, h6, h3, h4, ?_, fun e he => h8 e ?_, fun e he => h9 e ?_, fun e he => h10 e (mem e he),
      fun e he => h11 e (mem e he)⟩
    · refine (List.Perm.nodup_iff ?_).1 h7
      rw [List.append_assoc (al ++ be), List.append_assoc (ga ++ de)]
      exact List.perm_append_comm
    · simp only [List.mem_append] at he ⊢
      tauto
    · simp only [List.mem_append] at he ⊢
      tauto
  obtain ⟨-, -, ⟨p1, p2, p3, p4⟩, -⟩ := GlobalTheory.T.lowest_kTypes_jointShape_block_unitary t ga de al be h'
  let σ : Ix (al.length + de.length) (ga.length + be.length + t) → Ix (ga.length + be.length + t) (al.length + de.length) :=
    Sum.swap
  have e : ∀ a, lamM' t al be ga de a = lamA' t ga de al be (σ a) := fun a => by rcases a with a | a <;> rfl
  refine ⟨fun a b hab => ?_, fun a b hab => ?_, fun a => ?_, fun a b => ?_⟩
  · rw [e, e] at hab
    exact Sum.swap_leftInverse.injective (p1 hab)
  · rw [e, e]
    refine p2 _ _ ?_
    rcases a with a | a <;> rcases b with b | b <;> exact hab
  · rw [e]; exact p3 _
  · rw [e, e]; exact p4 _ _

theorem exists_locIt_large {X : ProvA} (hX : ChosenSeries X) (h1 : ArchimedeanRallisFirst X) (h2 : ArchimedeanRallisSecond X)
    (hB : GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D) (M : DSModel V S) (M' : DSModel W S') (τ : D.what₂.Tau) {t : ℕ}
    {al be ga de : List ℚ} (hd : DataARm t al be ga de) {aS aT : ℚ}
    (hS : S τ = dualPar (signed (al ++ de) (ga ++ block t ++ be) aT))
    (hS' : S' τ = dualPar (signed (al ++ be) (ga ++ de) aS)) :
    (0 < V.rank ∧ 0 < W.rank) ∧ ∃ A, LocIt M M' τ aS aT A := by
  obtain ⟨-, p1, -⟩ := GlobalTheory.T.lowest_kTypes_jointShape_block_unitary t al be ga de hd.1
  have p2 := isParam_lamM' hd.1
  have ht := hd.1.1
  have hn := hd.1.2.1
  obtain ⟨⟨e, he⟩, m, hm, hU⟩ := hB.1 X V S M τ (al.length + de.length) (ga.length + be.length + t) _ _ aT
    ⟨by omega, by simp, by simp [block]; omega, p2, hX _ _ _ p2, hS⟩
  obtain ⟨⟨e', he'⟩, m', hm', hU'⟩ := hB.2 X W S' M' τ (al.length + be.length) (ga.length + de.length) _ _ aS
    ⟨by omega, by simp, by simp, p1, hX _ _ _ p1, hS'⟩
  obtain ⟨U, hU⟩ := hU e he
  obtain ⟨U', hU'⟩ := hU' e' he'
  obtain ⟨Φ, hΦ⟩ := (h1.2 t al be ga de hd).1
  obtain ⟨Tm, hi, hq, -⟩ := h2.2 t al be ga de hd Φ hΦ
  obtain ⟨B, hB⟩ := exists_isCoverIt_swap _ _ _ _ _ _ _ _ _ _ Tm hi hq
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_fockPolynomialIso_unitaryPair _ _ _ _ _ _ _ _ e e' he he'
  obtain ⟨v, hv, -⟩ := (hX _ _ _ p1).1
  have c1 := Fintype.card_congr e
  have c2 := Fintype.card_congr e'
  simp only [Fintype.card_sum, Fintype.card_fin] at c1 c2
  exact ⟨⟨by omega, by omega⟩,
    GlobalTheory.T.exists_localFockIntertwiner_realPlace_of_coverContraction D V W S S' M M' τ _ _ _ _ _ _ _ _ e e' m m' aS aT U U' κ B hm hm' hU hU' ⟨v, 0, hv⟩ hκ hB⟩

end GlobalTheory.Chain.RealItLarge

theorem GlobalTheory.Chain.RealItLarge.itLarge : ∀ {D : D7} (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (t : ℕ) (aS aT : D.what₂.Tau → ℚ), GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → IsInfFam θ → (∀ τ, ∃ be de : List ℚ, Formalism.MainNotions.SchurIrreducible.DataARm t [] be [] de ∧ S τ = dualPar (GlobalTheory.Chain.signed de (Formalism.BasicNotions.TH.block t ++ be) (aT τ)) ∧ S' τ = dualPar (GlobalTheory.Chain.signed be de (aS τ))) → ∀ (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → (∀ τ, HasInfExp D χS τ (aS τ) ∧ HasInfExp D χT τ (aT τ)) → ∀ f, GlobalTheory.Chain.IsVacVec ψ θ M M' f → ∃ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M, IsItW θ M M' ω (GlobalTheory.Chain.ptOf ψ θ M M' f) It := by
  intro D V W S S' M M' θ ψ t aS aT hD hH hθ hP χS χT ω hω hexp f hf
  obtain ⟨X, hX, h1, h2⟩ := GlobalTheory.Chain.ItPairObj.exists_record hD hH
  have hB := GlobalTheory.T.thetaModels_eq_coverDiscreteSeries hD hH D
  have key : ∀ τ, (0 < V.rank ∧ 0 < W.rank) ∧ ∃ A, GlobalTheory.Chain.RealIt.LocIt M M' τ (aS τ) (aT τ) A := fun τ => by
    obtain ⟨be, de, hd, e1, e2⟩ := hP τ
    exact GlobalTheory.Chain.RealItLarge.exists_locIt_large hX h1 h2 hB M M' τ (al := []) (ga := []) hd e1 e2
  choose hr A hA using key
  obtain ⟨It, I, hI⟩ := GlobalTheory.T.exists_globalFockIntertwiner_tensor_realPlaces D V W _ _ M M' aS aT A GlobalTheory.Contr.contraction.2 (GlobalTheory.T.gluing_law_holds D _ _) hA
  have hc := fun τ => GlobalTheory.T.thetaVacuumCharacters_atRealPlaces D V W _ _ M M' θ ψ χS χT ω f τ _ _ hθ hω (hexp τ).1 (hexp τ).2 hf
  exact ⟨It, GlobalTheory.Chain.RealIt.isItW_of_globIt hθ hI hr (GlobalTheory.T.fockVectorsOverVacuumIsometry_of_skeletonDatum D V W _ _ M M' ψ θ hω.std hθ f hf).2.2.2.2
    (fun τ => (hc τ).2.1) fun τ => (hc τ).2.2⟩

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealIntertwinerLargerSourceMirrorCaseStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realIntertwiner_largerSource_mirrorCase : ∀ {D : D7} (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (t : ℕ) (aS aT : D.what₂.Tau → ℚ), GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → IsInfFam θ → (∀ τ, ∃ be de : List ℚ, Formalism.MainNotions.SchurIrreducible.DataARm t [] be [] de ∧ S τ = dualPar (GlobalTheory.Chain.signed de (Formalism.BasicNotions.TH.block t ++ be) (aT τ)) ∧ S' τ = dualPar (GlobalTheory.Chain.signed be de (aS τ))) → ∀ (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → (∀ τ, HasInfExp D χS τ (aS τ) ∧ HasInfExp D χT τ (aT τ)) → ∀ f, GlobalTheory.Chain.IsVacVec ψ θ M M' f → ∃ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M, IsItW θ M M' ω (GlobalTheory.Chain.ptOf ψ θ M M' f) It := by
  first | exact @GlobalTheory.Chain.RealItLarge.itLarge | exact GlobalTheory.Chain.RealItLarge.itLarge | (intros; apply GlobalTheory.Chain.RealItLarge.itLarge <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSumHalfWittHeisenbergLevelOfZeroCore
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSumHalfWittHeisenbergLevelOfZeroCore
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.BumpMix

open scoped Topology

namespace GlobalTheory.BumpMixLevel

variable {D : D7}

theorem symplOH_ext_fin {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (x a : Mx D T.rank ρ)
    (ha : a.map (infPart D) = 0) :
    symplOH S T (d.extX T x) (d.extY T a) = pairA D.host.F 0 (symplOH S T (d.extX T x) (d.extY T a)).2 := by
  have hfin : (d.extY T a).map (infPart D) = 0 := by
    rw [HypDec.extY_apply, Matrix.map_mul, ha, Matrix.zero_mul]
  have h3 : GlobalTheory.FinTranslate.eInf D * symplOH S T (d.extX T x) (d.extY T a) = 0 := by
    rw [← GlobalTheory.FinTranslate.symplOH_smul_right, GlobalTheory.FinTranslate.smul_fin hfin, GlobalTheory.FinTranslate.symplOH_zero_right]
  exact Prod.ext ((one_mul _).symm.trans (congrArg Prod.fst h3)) rfl

theorem exists_level_pair (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) {S S₀ T : HSp D} {ρ : ℕ}
    (d : HypDec S S₀ ρ) (K : Set (Mx D T.rank ρ)) (hK : IsCompact K) :
    ∃ U : AddSubgroup (Mx D T.rank ρ), IsOpen (U : Set (Mx D T.rank ρ)) ∧
      ∀ a ∈ U, a.map (infPart D) = 0 → ∀ k ∈ K, ψ (symplOH S T (d.extX T k) (d.extY T a)) = 1 := by
  have hX : Continuous (d.extX T) := continuous_id.matrix_mul continuous_const
  have hY : Continuous (d.extY T) := continuous_id.matrix_mul continuous_const
  have hs : Continuous fun p : Mx D T.rank ρ × Mx D T.rank ρ => (symplOH S T (d.extX T p.1) (d.extY T p.2)).2 :=
    continuous_snd.comp (GlobalTheory.OrientedHeis.continuous_symplOH (hX.comp continuous_fst) (hY.comp continuous_snd))
  have hZ := GlobalTheory.FinTranslate.ker_mem_nhds hψ.1.1 hψ.1.2.1
  have hO := (isOpen_interior (s := {b : Af D.host.F | ψ (pairA D.host.F 0 b) = 1})).preimage hs
  have hsub : K ×ˢ ({0} : Set (Mx D T.rank ρ)) ⊆
      (fun p : Mx D T.rank ρ × Mx D T.rank ρ => (symplOH S T (d.extX T p.1) (d.extY T p.2)).2) ⁻¹'
        interior {b : Af D.host.F | ψ (pairA D.host.F 0 b) = 1} := by
    rintro ⟨k, a⟩ ⟨-, ha⟩
    rw [Set.mem_singleton_iff] at ha
    subst ha
    simp only [Set.mem_preimage, map_zero, GlobalTheory.FinTranslate.symplOH_zero_right, Prod.snd_zero]
    exact mem_interior_iff_mem_nhds.2 hZ
  obtain ⟨u, v, -, hv, hKu, h0v, huv⟩ := generalized_tube_lemma hK isCompact_singleton hO hsub
  obtain ⟨U, hUo, hU⟩ := GlobalTheory.MixSumBound.finite_points_in_nhds D T.rank ρ v (hv.mem_nhds (h0v rfl))
  refine ⟨U, hUo, fun a ha hfin k hk => ?_⟩
  have h1 := huv (Set.mk_mem_prod (hKu hk) (hU a ha hfin))
  have h2 : (symplOH S T (d.extX T k) (d.extY T a)).2 ∈ {b : Af D.host.F | ψ (pairA D.host.F 0 b) = 1} :=
    interior_subset h1
  rw [symplOH_ext_fin d k a hfin]
  exact h2

theorem poinX_heis_level : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), S₀.rank = 0 → ∀ (β : Mx D T.rank ρ → ℂ), IsBump β → ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧ ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u (poinX ψ d T β) = poinX ψ d T β := by
  intro D ψ hψ S S₀ T ρ d h0 β hβ
  haveI : LocallyCompactSpace (Mx D T.rank ρ) := (GlobalTheory.MixModel.lattice_Mx D T.rank ρ).2.1
  obtain ⟨Uβ, hUβo, hUβ⟩ := hβ.level
  obtain ⟨C, hC, hC0⟩ := exists_compact_mem_nhds (0 : Mx D T.rank ρ)
  obtain ⟨UC, hUCo, hUC⟩ := GlobalTheory.MixSumBound.finite_points_in_nhds D T.rank ρ C hC0
  obtain ⟨UY, hUYo, hUY⟩ := GlobalTheory.BumpMixLevel.exists_level_pair ψ hψ d (tsupport β ∪ C) (hβ.supp.isCompact.union hC)
  let pX : WO S T →+ Mx D T.rank ρ :=
    { toFun := fun u => u ⬝ d.jX, map_zero' := Matrix.zero_mul _, map_add' := fun _ _ => Matrix.add_mul _ _ _ }
  let pY : WO S T →+ Mx D T.rank ρ :=
    { toFun := fun u => u ⬝ d.jY, map_zero' := Matrix.zero_mul _, map_add' := fun _ _ => Matrix.add_mul _ _ _ }
  have hpX : Continuous pX := continuous_id.matrix_mul continuous_const
  have hpY : Continuous pY := continuous_id.matrix_mul continuous_const
  refine ⟨(Uβ ⊓ UC).comap pX ⊓ UY.comap pY, ((hUβo.inter hUCo).preimage hpX).inter (hUYo.preimage hpY), ?_⟩
  intro u hu hfin
  have hsub0 : ∀ z : WO S₀ T, z = 0 := fun z => Matrix.ext fun i j => absurd j.isLt (by omega)
  have hw : ∀ w : WO S T, w = d.extX T (w ⬝ d.jX) + d.extY T (w ⬝ d.jY) := fun w => by
    conv_lhs => rw [eq_coords d w]
    rw [hsub0 (w ⬝ d.j0), map_zero, add_zero]
  have hx₀ : u ⬝ d.jX ∈ Uβ ∧ u ⬝ d.jX ∈ UC := hu.1
  have ha₀ : u ⬝ d.jY ∈ UY := hu.2
  have hfx : (u ⬝ d.jX).map (infPart D) = 0 := by rw [Matrix.map_mul, hfin, Matrix.zero_mul]
  have hfa : (u ⬝ d.jY).map (infPart D) = 0 := by rw [Matrix.map_mul, hfin, Matrix.zero_mul]
  have h00 : ψ (symplOH S T (d.extX T (u ⬝ d.jX)) (d.extY T (u ⬝ d.jY))) = 1 :=
    hUY _ ha₀ hfa _ (Or.inr (hUC _ hx₀.2 hfx))
  funext w
  have hs : symplOH S T w u = symplOH S T (d.extX T (w ⬝ d.jX)) (d.extY T (u ⬝ d.jY)) -
      symplOH S T (d.extX T (u ⬝ d.jX)) (d.extY T (w ⬝ d.jY)) := by
    conv_lhs => rw [hw w, hw u]
    simp only [GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right, d.symplOH_extX_extX,
      d.symplOH_extY_extY, zero_add, add_zero]
    rw [GlobalTheory.MixModel.symplOH_skew S T (d.extX T (u ⬝ d.jX)) (d.extY T (w ⬝ d.jY))]
    abel
  simp only [heisO, poinX]
  rw [← tsum_mul_left]
  refine tsum_congr fun γ => ?_
  rw [Matrix.add_mul, Matrix.add_mul]
  have hb : β (w ⬝ d.jX + u ⬝ d.jX + rat γ) = β (w ⬝ d.jX + rat γ) := by
    rw [add_right_comm]; exact hUβ _ hx₀.1 hfx _
  rw [hb]
  by_cases hk : β (w ⬝ d.jX + rat γ) = 0
  · rw [hk, mul_zero, mul_zero, mul_zero]
  have hkK : ψ (symplOH S T (d.extX T (w ⬝ d.jX + rat γ)) (d.extY T (u ⬝ d.jY))) = 1 :=
    hUY _ ha₀ hfa _ (Or.inl (subset_tsupport β hk))
  rw [← mul_assoc, ← d.symplOH_extX_extY T, ← d.symplOH_extX_extY T, ← AddChar.map_add_eq_mul, hs]
  have he : symplOH S T (d.extX T (w ⬝ d.jX)) (d.extY T (u ⬝ d.jY)) -
      symplOH S T (d.extX T (u ⬝ d.jX)) (d.extY T (w ⬝ d.jY)) +
      symplOH S T (d.extX T (w ⬝ d.jX + u ⬝ d.jX + 2 • rat γ)) (d.extY T (w ⬝ d.jY + u ⬝ d.jY)) =
      symplOH S T (d.extX T (w ⬝ d.jX + 2 • rat γ)) (d.extY T (w ⬝ d.jY)) +
        (symplOH S T (d.extX T (w ⬝ d.jX + rat γ)) (d.extY T (u ⬝ d.jY)) +
          symplOH S T (d.extX T (w ⬝ d.jX + rat γ)) (d.extY T (u ⬝ d.jY))) +
        symplOH S T (d.extX T (u ⬝ d.jX)) (d.extY T (u ⬝ d.jY)) := by
    simp only [map_add (f := _), two_nsmul, GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right]
    abel
  rw [he]
  simp only [AddChar.map_add_eq_mul, hkK, h00, mul_one]

end GlobalTheory.BumpMixLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSumHalfWittHeisenbergLevelOfZeroCoreStatement
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.BumpMix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincareSumHalfWitt_heisenberg_level_of_zero_core : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), S₀.rank = 0 → ∀ (β : Mx D T.rank ρ → ℂ), IsBump β → ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧ ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u (poinX ψ d T β) = poinX ψ d T β := by
  first | exact @GlobalTheory.BumpMixLevel.poinX_heis_level | exact GlobalTheory.BumpMixLevel.poinX_heis_level | (intros; apply GlobalTheory.BumpMixLevel.poinX_heis_level <;> assumption)
end
end
end
