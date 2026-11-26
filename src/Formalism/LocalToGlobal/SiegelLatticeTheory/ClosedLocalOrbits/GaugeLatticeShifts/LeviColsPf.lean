module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ParCols
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ActFrame

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LeviColsPf
noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence

namespace Formalism.L2.SG.NormCut

section LeviHom

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X)

theorem leviM_mul_inv {x : X.B.I.Gf} (hx : Good X x) (v : TR.Pl) : leviM TR x v * leviM TR x⁻¹ v = 1 := by
  rw [← leviM_mul_par TR hx.1 hx.2 v, mul_inv_cancel, leviM_one]

theorem isUnit_det_leviM {x : X.B.I.Gf} (hx : Good X x) (v : TR.Pl) : IsUnit (leviM TR x v).det := by
  exact Matrix.isUnit_det_of_right_inverse (leviM_mul_inv TR hx v)

theorem levi_coe {x : X.B.I.Gf} (hx : Good X x) (v : TR.Pl) :
    ((levi TR x v : GL (Fin D.R.k) (TR.Fq v)) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) = leviM TR x v := by
  unfold levi
  rw [dite_eq_left (isUnit_det_leviM TR hx v)]
  rfl

theorem levi_mul {x y : X.B.I.Gf} (hx : Good X x) (hy : Good X y) : levi TR (x * y) = levi TR x * levi TR y := by
  funext v
  apply Units.ext
  rw [Pi.mul_apply, Units.val_mul, levi_coe TR (good_mul _ hx hy), levi_coe TR hx, levi_coe TR hy]
  exact leviM_mul_par TR hx.1 hy.1 v

theorem levi_one : levi TR (1 : X.B.I.Gf) = 1 := by
  funext v
  apply Units.ext
  rw [levi_coe TR (good_one _) v, leviM_one]
  rfl

theorem levi_inv {x : X.B.I.Gf} (hx : Good X x) : levi TR x⁻¹ = (levi TR x)⁻¹ := by
  have h1 := levi_mul TR (good_inv _ hx) hx
  rw [inv_mul_cancel, levi_one] at h1
  exact eq_inv_of_mul_eq_one_left h1.symm

end LeviHom

section ColGood

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem Z_hA_mL {d w : VA X.B.I} (hd : d ∈ mL X.B.I X.B.g) (hw : w ∈ X.B.I.Lf) :
    ZMod' X.B.I X.B.g (hA X.B.I d w) := by
  rw [hA_symm]
  exact Z_sig X.B.I X.B.g (mL_Qs X.B.I X.B.g hw hd)

theorem colStab (u : D.what₂.Word) (h h' : Formalism.L2.SG.PoincareInHH.PoincareSetting.Hfin X u)
    (hk : ((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u) ∈ X.B.I.Kset) :
    (∀ a, X.B.I.fmat (((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u)) *ᵥ X.e0 a - X.e0 a ∈
      mL X.B.I X.B.g) ∧
    X.B.I.fmat (((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u)) *ᵥ X.z0 - X.z0 ∈ mL X.B.I X.B.g := by
  set k := ((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u) with hkdef
  obtain ⟨hE0, hF0, hZ0, -, -⟩ := frame_Lf X
  have hk' : k = (X.xu u)⁻¹ * ((h : X.B.I.Gf)⁻¹ * ((h' : X.B.I.Gf) * X.xu u)) := by rw [hkdef]; group
  have hfix : ∀ y ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.fixSet X u,
      X.B.I.fmat (X.xu u) *ᵥ incl X.B.I y = incl X.B.I y → X.B.I.fmat k *ᵥ incl X.B.I y = incl X.B.I y := by
    intro y hy hxu
    rw [hk']
    have h1 : X.B.I.fmat (h' : X.B.I.Gf) *ᵥ incl X.B.I y = incl X.B.I y := h'.2 y hy
    have h2 : X.B.I.fmat (h : X.B.I.Gf)⁻¹ *ᵥ incl X.B.I y = incl X.B.I y := fixes_inv X (h.2 y hy)
    exact fixes_mul X (fixes_inv X hxu) (fixes_mul X h2 (fixes_mul X h1 hxu))
  have hE : ∀ a, X.B.I.fmat k *ᵥ incl X.B.I (X.crd (X.eX a)) = incl X.B.I (X.crd (X.eX a)) := fun a =>
    hfix _ (Or.inl (Or.inl ⟨a, rfl⟩)) ((X.xu_fix u a).1)
  have hZ : X.B.I.fmat k *ᵥ (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.crd (X.zu u))) =
      X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.crd (X.zu u)) := by
    rw [Matrix.mulVec_mulVec, ← fmat_mul]
    have e : k * (X.xu u)⁻¹ = (X.xu u)⁻¹ * ((h : X.B.I.Gf)⁻¹ * (h' : X.B.I.Gf)) := by rw [hkdef]; group
    rw [e, fmat_mul, ← Matrix.mulVec_mulVec]
    congr 1
    have hy : X.crd (X.zu u) ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.fixSet X u := Or.inr rfl
    exact fixes_mul X (fixes_inv X (h.2 _ hy)) (h'.2 _ hy)
  have key : ∀ (w v : VA X.B.I), v ∈ X.B.I.Lf → X.B.I.fmat k *ᵥ w = w → InAt X.B.I X.B.g X.B.g (v - w) →
      X.B.I.fmat k *ᵥ v - v ∈ mL X.B.I X.B.g := by
    intro w v hv hw hvw
    refine mem_mL_of_InAt X (sub_mem (K_mv X.B.I hk hv) hv) ?_
    have := congG_of_Kset X hk hvw
    have e : X.B.I.fmat k *ᵥ v - v = X.B.I.fmat k *ᵥ (v - w) - (v - w) := by
      rw [Matrix.mulVec_sub, hw]; abel
    rw [e]; exact this
  refine ⟨fun a => key _ _ (hE0 a) (hE a) (X.basisApprox a).1, key _ _ hZ0 hZ ?_⟩
  obtain ⟨c, hc, hcm⟩ := X.xu_z u
  refine ⟨c, hc, ?_⟩
  rw [show X.z0 - X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.crd (X.zu u)) =
    -(X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.crd (X.zu u)) - X.z0) by abel, smul_neg]
  exact Submodule.neg_mem _ hcm

theorem par_of_stab {k : X.B.I.Gf} (hk : k ∈ X.B.I.Kset)
    (he : ∀ a, X.B.I.fmat k *ᵥ X.e0 a - X.e0 a ∈ mL X.B.I X.B.g)
    (hie : ∀ a, X.B.I.fmat k⁻¹ *ᵥ X.e0 a - X.e0 a ∈ mL X.B.I X.B.g)
    (hiz : X.B.I.fmat k⁻¹ *ᵥ X.z0 - X.z0 ∈ mL X.B.I X.B.g) : Par X k := by
  obtain ⟨hE0, hF0, hZ0, hB, hBd⟩ := frame_Lf X
  refine ⟨hk, fun a => ?_, fun j => ?_⟩
  · rw [show X.B.I.fmat k *ᵥ X.e0 a = X.e0 a + (X.B.I.fmat k *ᵥ X.e0 a - X.e0 a) by abel]
    exact add_mem (sub_Mo X.B.I ⟨a, rfl⟩) (mL_Mo X.B.I (he a))
  · refine mem_Mo_eb X (K_mv X.B.I hk (hB j)) (fun a => ?_) ?_ (fun l => ?_)
    · rw [hA_adj, show X.B.I.fmat k⁻¹ *ᵥ X.e0 a = X.e0 a + (X.B.I.fmat k⁻¹ *ᵥ X.e0 a - X.e0 a) by abel,
        hA_add_left]
      exact Z_add X.B.I X.B.g ((X.weightVectorsIntegral j).2.2 a).1 (Z_hA_mL X (hie a) (hB j))
    · rw [hA_adj, show X.B.I.fmat k⁻¹ *ᵥ X.z0 = X.z0 + (X.B.I.fmat k⁻¹ *ᵥ X.z0 - X.z0) by abel, hA_add_left]
      exact Z_add X.B.I X.B.g (X.weightVectorsIntegral j).1 (Z_hA_mL X hiz (hB j))
    · have e : hA X.B.I (X.bw l) (X.B.I.fmat k *ᵥ X.bw j) = 0 := by
        rw [X.bw_w l, X.bw_w j, Matrix.mulVec_smul, hA_smul_left, hA_smul_right]
        have := X.ew_orth
        linear_combination (hA X.B.I (X.bw l) (X.B.I.fmat k *ᵥ X.bw j)) * this
      rw [e]; exact Z_zero X.B.I X.B.g

theorem colGood (u : D.what₂.Word) (h h' : Formalism.L2.SG.PoincareInHH.PoincareSetting.Hfin X u)
    (hk : ((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u) ∈ X.B.I.Kset)
    (hki : ((h' : X.B.I.Gf) * X.xu u)⁻¹ * ((h : X.B.I.Gf) * X.xu u) ∈ X.B.I.Kset) :
    Good X (((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u)) := by
  have e1 : (((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u))⁻¹ =
      ((h' : X.B.I.Gf) * X.xu u)⁻¹ * ((h : X.B.I.Gf) * X.xu u) := by
    rw [_root_.mul_inv_rev, inv_inv]
  have e2 : (((h' : X.B.I.Gf) * X.xu u)⁻¹ * ((h : X.B.I.Gf) * X.xu u))⁻¹ =
      ((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h' : X.B.I.Gf) * X.xu u) := by
    rw [_root_.mul_inv_rev, inv_inv]
  obtain ⟨he, hz⟩ := colStab X u h h' hk
  obtain ⟨he', hz'⟩ := colStab X u h' h hki
  refine ⟨par_of_stab X hk he (by rw [e1]; exact he') (by rw [e1]; exact hz'), ?_⟩
  rw [e1]
  exact par_of_stab X hki he' (by rw [e2]; exact he) (by rw [e2]; exact hz)

end ColGood

section LeviColsPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X) {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂) (cs' : ColSys X u' rows')


variable (F0 F0') in
def AdmPar : Prop :=
  ∀ t : GTerm X u u' F0 F0' what₂ rows',
    Good X (kOf X u u' (cs.h (cs.base t.lam) : X.B.I.Gf) (cs'.h (cs'.base t.lam') : X.B.I.Gf) t.pt)

theorem leviCols_of (hL : ColLatK cs) (hL' : ColLatK cs') (hA : AdmPar F0 F0' cs cs') :
    LeviCols TR F0 F0' cs cs' := by
  unfold LeviCols
  intro t ρ ρ' h1 h2
  have hK : Good X (kOf X u u' (cs.h (cs.base t.lam) : X.B.I.Gf) (cs'.h (cs'.base t.lam') : X.B.I.Gf) t.pt) := hA t
  unfold iotaOf scOf
  rw [h1, h2]
  unfold kOf at hK ⊢
  have lb : cs.lamOf (cs.base t.lam) = cs.lamOf ρ := by
    rw [h1]
    exact cs.base_lam _ (h1 ▸ cs.lam_mem ρ)
  have lb' : cs'.lamOf (cs'.base t.lam') = cs'.lamOf ρ' := by
    rw [h2]
    exact cs'.base_lam _ (h2 ▸ cs'.lam_mem ρ')
  have gA := colGood X u _ _ (hL _ _ lb) (hL _ _ lb.symm)
  have gB := colGood X u' _ _ (hL' _ _ lb') (hL' _ _ lb'.symm)
  have e : ((cs.h ρ : X.B.I.Gf) * X.xu u)⁻¹ * t.pt.2 * ((cs'.h ρ' : X.B.I.Gf) * X.xu u') =
      (((cs.h (cs.base t.lam) : X.B.I.Gf) * X.xu u)⁻¹ * ((cs.h ρ : X.B.I.Gf) * X.xu u))⁻¹ *
        (((cs.h (cs.base t.lam) : X.B.I.Gf) * X.xu u)⁻¹ * t.pt.2 *
          ((cs'.h (cs'.base t.lam') : X.B.I.Gf) * X.xu u')) *
        (((cs'.h (cs'.base t.lam') : X.B.I.Gf) * X.xu u')⁻¹ * ((cs'.h ρ' : X.B.I.Gf) * X.xu u')) := by
    group
  rw [e, levi_mul TR (good_mul _ (good_inv _ gA) hK) gB, levi_mul TR (good_inv _ gA) hK, levi_inv TR gA]

end LeviColsPf

end Formalism.L2.SG.NormCut
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHModel
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Formalism.L2.SG.Pf.BH.Model

def sqs {n : ℕ} (w : Fin n → ℝ) : ℝ := ∑ i, (w i) ^ 2

theorem norm_sq_euclid {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : ‖x‖ ^ 2 = ∑ i, (WithLp.ofLp x i) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.norm_eq_abs, sq_abs]

theorem euclid_prod (a b : ℕ) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x : EuclideanSpace ℝ (Fin a), ∫⁻ y : EuclideanSpace ℝ (Fin b), F (‖x‖ ^ 2 + ‖y‖ ^ 2) =
      ∫⁻ z : EuclideanSpace ℝ (Fin (a + b)), F (‖z‖ ^ 2) := by

  have hA := PiLp.volume_preserving_ofLp (Fin a)
  have hB := PiLp.volume_preserving_ofLp (Fin b)
  have hC := PiLp.volume_preserving_ofLp (Fin (a + b))
  have hEa : MeasurableEmbedding (@WithLp.ofLp 2 (Fin a → ℝ)) := (MeasurableEquiv.toLp 2 (Fin a → ℝ)).symm.measurableEmbedding
  have hEb : MeasurableEmbedding (@WithLp.ofLp 2 (Fin b → ℝ)) := (MeasurableEquiv.toLp 2 (Fin b → ℝ)).symm.measurableEmbedding
  have hEc : MeasurableEmbedding (@WithLp.ofLp 2 (Fin (a + b) → ℝ)) :=
    (MeasurableEquiv.toLp 2 (Fin (a + b) → ℝ)).symm.measurableEmbedding
  have e1 : ∀ x : EuclideanSpace ℝ (Fin a), ‖x‖ ^ 2 = sqs (WithLp.ofLp x) := norm_sq_euclid
  have e2 : ∀ y : EuclideanSpace ℝ (Fin b), ‖y‖ ^ 2 = sqs (WithLp.ofLp y) := norm_sq_euclid
  have e3 : ∀ z : EuclideanSpace ℝ (Fin (a + b)), ‖z‖ ^ 2 = sqs (WithLp.ofLp z) := norm_sq_euclid
  simp_rw [e1, e2, e3]
  rw [hC.lintegral_comp_emb hEc (fun w => F (sqs w))]
  have inner : ∀ x : EuclideanSpace ℝ (Fin a), ∫⁻ y : EuclideanSpace ℝ (Fin b), F (sqs (WithLp.ofLp x) + sqs (WithLp.ofLp y)) =
      ∫⁻ q : Fin b → ℝ, F (sqs (WithLp.ofLp x) + sqs q) :=
    fun x => hB.lintegral_comp_emb hEb (fun q => F (sqs (WithLp.ofLp x) + sqs q))
  simp_rw [inner]
  rw [hA.lintegral_comp_emb hEa (fun p => ∫⁻ q : Fin b → ℝ, F (sqs p + sqs q))]

  have hS : Measurable fun w : Fin (a + b) → ℝ => sqs w := by unfold sqs; fun_prop
  have hsum := volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin a ⊕ Fin b => ℝ)
  have hcong := volume_measurePreserving_piCongrLeft (fun _ : Fin (a + b) => ℝ) finSumFinEquiv
  rw [← hcong.lintegral_comp_emb (MeasurableEquiv.piCongrLeft _ finSumFinEquiv).measurableEmbedding]
  rw [← hsum.symm.lintegral_comp_emb (MeasurableEquiv.sumPiEquivProdPi _).symm.measurableEmbedding]
  rw [Measure.volume_eq_prod, lintegral_prod _ ?meas]
  · refine lintegral_congr fun p => lintegral_congr fun q => ?_
    congr 1
    symm
    unfold sqs
    rw [← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]
    have h1 : ∀ (g : Fin a ⊕ Fin b → ℝ) (i : Fin a),
        (Equiv.piCongrLeft (fun _ => ℝ) finSumFinEquiv) g (Fin.castAdd b i) = g (Sum.inl i) := fun g i => by
      rw [← finSumFinEquiv_apply_left, Equiv.piCongrLeft_apply_apply]
    have h2 : ∀ (g : Fin a ⊕ Fin b → ℝ) (i : Fin b),
        (Equiv.piCongrLeft (fun _ => ℝ) finSumFinEquiv) g (Fin.natAdd a i) = g (Sum.inr i) := fun g i => by
      rw [← finSumFinEquiv_apply_right, Equiv.piCongrLeft_apply_apply]
    simp [MeasurableEquiv.piCongrLeft, MeasurableEquiv.sumPiEquivProdPi, h1, h2, Equiv.sumPiEquivProdPi]
  · exact ((hF.comp hS).comp (MeasurableEquiv.piCongrLeft _ finSumFinEquiv).measurable).comp
      (MeasurableEquiv.sumPiEquivProdPi _).symm.measurable |>.aemeasurable

end Formalism.L2.SG.Pf.BH.Model

namespace Formalism.L2.SG.Pf.BH.Model

theorem euclid_cast (a b : ℕ) (h : a = b) (F : ℝ → ℝ≥0∞) :
    ∫⁻ z : EuclideanSpace ℝ (Fin a), F (‖z‖ ^ 2) = ∫⁻ z : EuclideanSpace ℝ (Fin b), F (‖z‖ ^ 2) := by
  subst h; rfl

theorem ip_to_euclid (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (F : ℝ → ℝ≥0∞) :
    ∫⁻ y : E, F (‖y‖ ^ 2) = ∫⁻ x : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), F (‖x‖ ^ 2) := by
  let φ := (stdOrthonormalBasis ℝ E).repr
  have hφ : MeasurePreserving φ := φ.measurePreserving
  have he : MeasurableEmbedding φ := φ.toHomeomorph.measurableEmbedding
  rw [← hφ.lintegral_comp_emb he (fun x => F (‖x‖ ^ 2))]
  refine lintegral_congr fun y => ?_
  rw [LinearIsometryEquiv.norm_map]

theorem cplx_step (m : ℕ) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ w : ℂ, ∫⁻ x : EuclideanSpace ℝ (Fin m), F (2 * ‖w‖ ^ 2 + ‖x‖ ^ 2) =
      2⁻¹ * ∫⁻ z : EuclideanSpace ℝ (Fin (2 + m)), F (‖z‖ ^ 2) := by
  set G : ℝ → ℝ≥0∞ := fun t => ∫⁻ x : EuclideanSpace ℝ (Fin m), F (t + ‖x‖ ^ 2) with hG
  have hGm : Measurable G := by
    have : Measurable fun p : ℝ × EuclideanSpace ℝ (Fin m) => F (p.1 + ‖p.2‖ ^ 2) := hF.comp (by fun_prop)
    exact this.lintegral_prod_right'

  have hs : (Real.sqrt 2) ≠ 0 := by positivity
  have hmap := Measure.map_addHaar_smul (volume : Measure ℂ) hs
  have e1 : ∀ w : ℂ, 2 * ‖w‖ ^ 2 = ‖(Real.sqrt 2) • w‖ ^ 2 := by
    intro w; rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by norm_num)]
  have step1 : ∫⁻ w : ℂ, G (2 * ‖w‖ ^ 2) = 2⁻¹ * ∫⁻ w : ℂ, G (‖w‖ ^ 2) := by
    simp_rw [e1]
    have hmeas : Measurable fun w : ℂ => G (‖w‖ ^ 2) := hGm.comp (by fun_prop)
    rw [← lintegral_map hmeas (by fun_prop : Measurable fun w : ℂ => (Real.sqrt 2) • w), hmap,
      lintegral_smul_measure, Complex.finrank_real_complex]
    congr 1
    rw [show Real.sqrt 2 ^ 2 = 2 by rw [Real.sq_sqrt (by norm_num)]]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹), ENNReal.ofReal_inv_of_pos (by norm_num)]
    simp

  have step2 : ∫⁻ w : ℂ, G (‖w‖ ^ 2) = ∫⁻ y : EuclideanSpace ℝ (Fin 2), G (‖y‖ ^ 2) := by
    have h1 := Complex.volume_preserving_equiv_pi
    have h2 := PiLp.volume_preserving_ofLp (Fin 2)
    have he2 : MeasurableEmbedding (@WithLp.ofLp 2 (Fin 2 → ℝ)) :=
      (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.measurableEmbedding
    calc ∫⁻ w : ℂ, G (‖w‖ ^ 2) = ∫⁻ w : ℂ, G (sqs (Complex.measurableEquivPi w)) := by
          refine lintegral_congr fun w => ?_
          congr 1
          rw [Complex.measurableEquivPi_apply, sqs, Fin.sum_univ_two, Complex.sq_norm, Complex.normSq_apply]
          simp; ring
      _ = ∫⁻ p : Fin 2 → ℝ, G (sqs p) :=
          h1.lintegral_comp_emb Complex.measurableEquivPi.measurableEmbedding (fun p => G (sqs p))
      _ = ∫⁻ y : EuclideanSpace ℝ (Fin 2), G (sqs (WithLp.ofLp y)) :=
          (h2.lintegral_comp_emb he2 (fun p => G (sqs p))).symm
      _ = ∫⁻ y : EuclideanSpace ℝ (Fin 2), G (‖y‖ ^ 2) := by
          refine lintegral_congr fun y => ?_
          rw [norm_sq_euclid]; rfl
  have hmain : ∫⁻ w : ℂ, ∫⁻ x : EuclideanSpace ℝ (Fin m), F (2 * ‖w‖ ^ 2 + ‖x‖ ^ 2) = ∫⁻ w : ℂ, G (2 * ‖w‖ ^ 2) := rfl
  rw [hmain, step1, step2]
  congr 1
  exact euclid_prod 2 m F hF

end Formalism.L2.SG.Pf.BH.Model

namespace Formalism.L2.SG.Pf.BH.Model

theorem cpow_step (r : ℕ) : ∀ (m : ℕ) (F : ℝ → ℝ≥0∞), Measurable F →
    ∫⁻ u : Fin r → ℂ, ∫⁻ x : EuclideanSpace ℝ (Fin m), F (2 * ∑ a, ‖u a‖ ^ 2 + ‖x‖ ^ 2) =
      (2 ^ r)⁻¹ * ∫⁻ z : EuclideanSpace ℝ (Fin (2 * r + m)), F (‖z‖ ^ 2) := by
  induction r with
  | zero =>
    intro m F hF
    rw [MeasureTheory.volume_pi, Measure.pi_of_empty, lintegral_dirac]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, mul_zero, zero_add, pow_zero, inv_one, one_mul]
    exact euclid_cast m (2 * 0 + m) (by ring) F
  | succ r ih =>
    intro m F hF
    have hp := measurePreserving_piFinSuccAbove (fun _ : Fin (r + 1) => (volume : Measure ℂ)) 0
    have hmeasH : Measurable fun u : Fin (r + 1) → ℂ =>
        ∫⁻ x : EuclideanSpace ℝ (Fin m), F (2 * ∑ a, ‖u a‖ ^ 2 + ‖x‖ ^ 2) := by
      have : Measurable fun p : (Fin (r + 1) → ℂ) × EuclideanSpace ℝ (Fin m) =>
          F (2 * ∑ a, ‖p.1 a‖ ^ 2 + ‖p.2‖ ^ 2) := hF.comp (by fun_prop)
      exact this.lintegral_prod_right'
    rw [MeasureTheory.volume_pi, ← hp.symm.lintegral_comp_emb
      (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) 0).symm.measurableEmbedding]
    have hsplit : ∀ p : ℂ × (Fin r → ℂ), ∑ a, ‖(MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) 0).symm p a‖ ^ 2 =
        ‖p.1‖ ^ 2 + ∑ a, ‖p.2 a‖ ^ 2 := by
      intro p
      rw [Fin.sum_univ_succ]
      simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNth_zero']
    simp_rw [hsplit]
    rw [lintegral_prod _ ?meas]
    · have inner : ∀ w : ℂ, ∫⁻ u' : Fin r → ℂ, ∫⁻ x : EuclideanSpace ℝ (Fin m),
          F (2 * (‖w‖ ^ 2 + ∑ a, ‖u' a‖ ^ 2) + ‖x‖ ^ 2) ∂volume ∂(Measure.pi fun _ => volume) =
          (2 ^ r)⁻¹ * ∫⁻ z : EuclideanSpace ℝ (Fin (2 * r + m)), F (2 * ‖w‖ ^ 2 + ‖z‖ ^ 2) := by
        intro w
        have := ih m (fun t => F (2 * ‖w‖ ^ 2 + t)) (hF.comp (by fun_prop))
        rw [← MeasureTheory.volume_pi]
        rw [← this]
        refine lintegral_congr fun u' => lintegral_congr fun x => ?_
        congr 1; ring
      simp_rw [inner]
      rw [lintegral_const_mul' _ _ (by simp), cplx_step (2 * r + m) F hF,
        euclid_cast (2 + (2 * r + m)) (2 * (r + 1) + m) (by ring) F, ← mul_assoc, pow_succ,
        ENNReal.mul_inv (by simp) (by simp)]
    · have : Measurable fun q : (ℂ × (Fin r → ℂ)) × EuclideanSpace ℝ (Fin m) =>
          F (2 * (‖q.1.1‖ ^ 2 + ∑ a, ‖q.1.2 a‖ ^ 2) + ‖q.2‖ ^ 2) := hF.comp (by fun_prop)
      exact this.lintegral_prod_right'.aemeasurable

end Formalism.L2.SG.Pf.BH.Model

namespace Formalism.L2.SG.Pf.BH.Model

theorem enn_sq {E : Type*} [NormedAddCommGroup E] (y : E) : ((‖y‖₊ : ℝ≥0∞)) ^ 2 = ENNReal.ofReal (‖y‖ ^ 2) := by
  rw [ENNReal.ofReal_pow (norm_nonneg y), ENNReal.ofReal, norm_toNNReal]

theorem modelVol : Formalism.L2.SG.Pf.BH.ModelVol := by
  intro E1 E2 _ _ _ _ _ _ _ _ _ _ r s hs
  set G : ℝ → ℝ≥0∞ := fun t => if t < s ^ 2 then 1 else 0 with hG
  have hGm : Measurable G := Measurable.ite measurableSet_Iio measurable_const measurable_const
  have hs2 : 0 < s ^ 2 := by positivity

  have hint : ∀ (c : Fin r → ℂ) (y1 : E1) (y2 : E2) (y3 : E1),
      (if (‖y1‖₊ : ℝ≥0∞) ^ 2 + ENNReal.ofReal (2 * ∑ a, ‖c a - 1‖ ^ 2) + (‖y2‖₊ : ℝ≥0∞) ^ 2 + (‖y3‖₊ : ℝ≥0∞) ^ 2 <
          ENNReal.ofReal (s ^ 2) then (1 : ℝ≥0∞) else 0) =
        G (2 * ∑ a, ‖c a - 1‖ ^ 2 + (‖y1‖ ^ 2 + (‖y2‖ ^ 2 + ‖y3‖ ^ 2))) := by
    intro c y1 y2 y3
    have hB : 0 ≤ 2 * ∑ a, ‖c a - 1‖ ^ 2 := by positivity
    rw [enn_sq, enn_sq, enn_sq, ← ENNReal.ofReal_add (by positivity) hB, ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    simp only [ENNReal.ofReal_lt_ofReal_iff hs2, hG]
    split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; linarith)
  simp_rw [hint]

  have step : ∀ B : ℝ, ∫⁻ y1 : E1, ∫⁻ y2 : E2, ∫⁻ y3 : E1, G (B + (‖y1‖ ^ 2 + (‖y2‖ ^ 2 + ‖y3‖ ^ 2))) =
      ∫⁻ w : EuclideanSpace ℝ (Fin (Module.finrank ℝ E1 + (Module.finrank ℝ E2 + Module.finrank ℝ E1))),
        G (B + ‖w‖ ^ 2) := by
    intro B
    have s3 : ∀ t : ℝ, ∫⁻ y2 : E2, ∫⁻ y3 : E1, G (B + (t + (‖y2‖ ^ 2 + ‖y3‖ ^ 2))) =
        ∫⁻ z : EuclideanSpace ℝ (Fin (Module.finrank ℝ E2 + Module.finrank ℝ E1)), G (B + (t + ‖z‖ ^ 2)) := by
      intro t
      have a1 : ∀ y2 : E2, ∫⁻ y3 : E1, G (B + (t + (‖y2‖ ^ 2 + ‖y3‖ ^ 2))) =
          ∫⁻ x3 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E1)), G (B + (t + (‖y2‖ ^ 2 + ‖x3‖ ^ 2))) :=
        fun y2 => ip_to_euclid E1 (fun u => G (B + (t + (‖y2‖ ^ 2 + u))))
      simp_rw [a1]
      rw [ip_to_euclid E2 (fun u => ∫⁻ x3 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E1)), G (B + (t + (u + ‖x3‖ ^ 2))))]
      exact euclid_prod _ _ (fun u => G (B + (t + u))) (hGm.comp (by fun_prop))
    simp_rw [s3]
    rw [ip_to_euclid E1 (fun u => ∫⁻ z : EuclideanSpace ℝ (Fin (Module.finrank ℝ E2 + Module.finrank ℝ E1)),
      G (B + (u + ‖z‖ ^ 2)))]
    exact euclid_prod _ _ (fun u => G (B + u)) (hGm.comp (by fun_prop))
  simp_rw [step]

  have htr := lintegral_add_left_eq_self (μ := (volume : Measure (Fin r → ℂ)))
    (fun c : Fin r → ℂ => ∫⁻ w : EuclideanSpace ℝ (Fin (Module.finrank ℝ E1 + (Module.finrank ℝ E2 + Module.finrank ℝ E1))),
      G (2 * ∑ a, ‖c a - 1‖ ^ 2 + ‖w‖ ^ 2)) 1
  rw [← htr]
  simp only [Pi.add_apply, Pi.one_apply, add_sub_cancel_left]
  rw [cpow_step r _ G hGm]

  have hball : ∀ (n : ℕ), ∫⁻ z : EuclideanSpace ℝ (Fin n), G (‖z‖ ^ 2) = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s) := by
    intro n
    rw [← lintegral_indicator_one measurableSet_ball]
    refine lintegral_congr fun z => ?_
    simp only [hG, Set.indicator, Metric.mem_ball, dist_zero_right, Pi.one_apply]
    congr 1
    apply propext
    constructor
    · intro h; exact lt_of_pow_lt_pow_left₀ 2 hs.le h
    · intro h; exact pow_lt_pow_left₀ h (norm_nonneg _) two_ne_zero
  rw [euclid_cast _ (2 * Module.finrank ℝ E1 + 2 * r + Module.finrank ℝ E2) (by ring) G, hball,
    ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num)]
  simp

end Formalism.L2.SG.Pf.BH.Model
end
end
