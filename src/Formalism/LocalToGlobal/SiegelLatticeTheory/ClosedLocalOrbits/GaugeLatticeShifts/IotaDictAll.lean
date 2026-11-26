module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RatIota

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.BridgeAR
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.BridgeRat
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.BridgeAd
noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.NormCut

namespace Formalism.L2.SG.Pf.BridgeAd

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem hermitian_module_dual_beta_congruence {m : VA X.B.I} (hm : m ∈ Mo X.B.I X.B.g (Set.range X.e0)) (j : Fin D.R.k) :
    ZMod' X.B.I X.B.g (hA X.B.I m (X.bwd j)) := by
  rw [hA_symm]
  refine Z_sig X.B.I X.B.g (Z_pair_Mo X (X.vectorsInLattice.2.2 j).2 ?_ _ hm)
  rintro _ ⟨a, rfl⟩
  exact dual_beta_reference_congruence j a

theorem mem_module_of_congruences {v : VA X.B.I} (hv : v ∈ X.B.I.Lf) (he : ∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.e0 a) v))
    (hz : ZMod' X.B.I X.B.g (hA X.B.I X.z0 v)) (hbd : ∀ l, ZMod' X.B.I X.B.g (hA X.B.I (X.bwd l) v))
    (hb : ∀ l, ZMod' X.B.I X.B.g (hA X.B.I (X.bw l) v)) : v ∈ Mo X.B.I X.B.g (Set.range X.e0) := by
  obtain ⟨hE, hF, hZ, hB, hBd⟩ := frame_Lf X
  have hd := dual_coords X hv
  rw [show v = (v - repr0 X v) + repr0 X v by abel]
  refine add_mem (mL_Mo X.B.I hd) ?_
  unfold repr0
  refine add_mem (add_mem (sub_mem (add_mem ?_ ?_) ?_) ?_) ?_
  · refine sum_mem fun a _ => ?_
    have : hA X.B.I (X.f0 a) v • X.e0 a = (⟨_, hA_int X.B.I (hF a) hv⟩ : IntAf X.B.I.F X.B.I.E) • X.e0 a := rfl
    rw [this]; exact Submodule.smul_mem _ _ (sub_Mo X.B.I ⟨a, rfl⟩)
  · exact sum_mem fun a _ => mL_Mo X.B.I (Z_smul_mL X (he a) (hF a))
  · exact mL_Mo X.B.I (Z_smul_mL X hz hZ)
  · exact sum_mem fun l _ => mL_Mo X.B.I (Z_smul_mL X (hbd l) (hB l))
  · exact sum_mem fun l _ => mL_Mo X.B.I (Z_smul_mL X (hb l) (hBd l))

theorem hA_bwd_K (δ : X.B.I.Gf) (k j : Fin D.R.k) : hA X.B.I (X.bwd k) (X.B.I.fmat δ *ᵥ X.bwd j) = 0 := by
  rw [X.bwd_w k, X.bwd_w j, Matrix.mulVec_smul, hA_smul_left, hA_smul_right, sigA_sigA]
  have := X.ew_orth
  linear_combination (hA X.B.I (X.bwd k) (X.B.I.fmat δ *ᵥ X.bwd j)) * this

variable {X} (TR : TypedRed X)
include TR

theorem adTriv_inv {δ : X.B.I.Gf} (hK : δ ∈ X.B.I.Kset) (hN : NCong X δ) (hT : Formalism.L2.SG.Pf.AdTriv X δ) :
    Formalism.L2.SG.Pf.AdTriv X δ⁻¹ := by
  have gδ := good_of_ncong X hK hN
  have h1 : levi TR δ = 1 := (Formalism.L2.SG.Pf.IotaDictPf.levi_one_iff TR gδ).2 hT
  refine (Formalism.L2.SG.Pf.IotaDictPf.levi_one_iff TR (good_inv X gδ)).1 ?_
  rw [levi_inv TR gδ, h1, inv_one]

theorem adTriv_bwd {δ : X.B.I.Gf} (hK : δ ∈ X.B.I.Kset) (hN : NCong X δ) (hT : Formalism.L2.SG.Pf.AdTriv X δ) (j : Fin D.R.k) :
    (X.B.I.fmat δ - 1) *ᵥ X.bwd j ∈ Mo X.B.I X.B.g (Set.range X.e0) := by
  obtain ⟨hE, hF, hZ, hB, hBd⟩ := frame_Lf X
  have hNi := ncong_inv X hK hN
  have hTi := adTriv_inv TR hK hN hT
  have hadj : ∀ y : VA X.B.I, hA X.B.I y ((X.B.I.fmat δ - 1) *ᵥ X.bwd j) =
      hA X.B.I ((X.B.I.fmat δ⁻¹ - 1) *ᵥ y) (X.bwd j) := by
    intro y
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hA_sub_right, hA_adj, Matrix.sub_mulVec, Matrix.one_mulVec,
      hA_sub_left]
  refine mem_module_of_congruences X (K_sub_mv X.B.I hK (hBd j)) (fun a => ?_) ?_ (fun l => ?_) (fun l => ?_)
  · rw [hadj]
    exact hermitian_module_dual_beta_congruence X (Mo_mono X.B.I (Set.image_subset_range _ _) (hNi.1 a)) j
  · rw [hadj]; exact hermitian_module_dual_beta_congruence X hNi.2 j
  · rw [Matrix.sub_mulVec, Matrix.one_mulVec, hA_sub_right, hA_bwd_K, hA_bwd_bwd, sub_zero]
    exact Z_zero X.B.I X.B.g
  · rw [hadj]; exact hermitian_module_dual_beta_congruence X (hTi l) j

theorem adFull_of_adTriv {δ : X.B.I.Gf} (hK : δ ∈ X.B.I.Kset) (hN : NCong X δ) (hT : Formalism.L2.SG.Pf.AdTriv X δ)
    {w : VA X.B.I} (hw : w ∈ X.B.I.Lf) (he : ∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.e0 a) w)) :
    (X.B.I.fmat δ - 1) *ᵥ w ∈ Mo X.B.I X.B.g (Set.range X.e0) := by
  obtain ⟨hE, hF, hZ, hB, hBd⟩ := frame_Lf X
  have hd := dual_coords X hw
  have hsm : ∀ (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (m : VA X.B.I), c ∈ IntAf X.B.I.F X.B.I.E →
      m ∈ Mo X.B.I X.B.g (Set.range X.e0) → c • m ∈ Mo X.B.I X.B.g (Set.range X.e0) := fun c m hc hm => by
    have : c • m = (⟨c, hc⟩ : IntAf X.B.I.F X.B.I.E) • m := rfl
    rw [this]; exact Submodule.smul_mem _ _ hm
  rw [show w = (w - repr0 X w) + repr0 X w by abel, Matrix.mulVec_add]
  refine add_mem (mL_Mo X.B.I ?_) ?_
  · rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact sub_mem (mem_mL_of_Kset X hK _ hd) hd
  unfold repr0
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub, mulVec_fsum X, Matrix.mulVec_smul]
  refine add_mem (add_mem (sub_mem (add_mem ?_ ?_) ?_) ?_) ?_
  · exact sum_mem fun a _ => hsm _ _ (hA_int X.B.I (hF a) hw)
      (Mo_mono X.B.I (Set.image_subset_range _ _) (hN.1 a))
  · exact sum_mem fun a _ => mL_Mo X.B.I (Z_smul_mL X (he a) (K_sub_mv X.B.I hK (hF a)))
  · exact hsm _ _ (hA_int X.B.I hZ hw) hN.2
  · exact sum_mem fun l _ => hsm _ _ (hA_int X.B.I (hBd l) hw) (hT l)
  · exact sum_mem fun l _ => hsm _ _ (hA_int X.B.I (hB l) hw) (adTriv_bwd TR hK hN hT l)

end Formalism.L2.SG.Pf.BridgeAd
end
end

noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.NormCut

namespace Formalism.L2.SG.Pf.BridgeRat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def hat (A : X.B.I.Gf) (y : (VS D).V) : VA X.B.I := X.B.I.fmat A⁻¹ *ᵥ incl X.B.I (X.crd y)

theorem hat_add (A : X.B.I.Gf) (y z : (VS D).V) : hat X A (y + z) = hat X A y + hat X A z := by
  simp only [hat]
  rw [← Matrix.mulVec_add]
  congr 1
  funext i
  simp [incl, Formalism.L2.SG.HidaSetting.HidaSetting.crd, crdOf, map_add (f := _)]

theorem hat_sub (A : X.B.I.Gf) (y z : (VS D).V) : hat X A (y - z) = hat X A y - hat X A z := by
  simp only [hat]
  rw [← Matrix.mulVec_sub]
  congr 1
  funext i
  simp [incl, Formalism.L2.SG.HidaSetting.HidaSetting.crd, crdOf, map_sub]

theorem hat_smul (A : X.B.I.Gf) (c : D.host.E) (y : (VS D).V) :
    hat X A (c • y) = Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm c) • hat X A y := by
  simp only [hat]
  rw [← Matrix.mulVec_smul]
  congr 1
  funext i
  simp [incl, Formalism.L2.SG.HidaSetting.HidaSetting.crd, crdOf, map_mul, smul_eq_mul]

theorem hat_sum (A : X.B.I.Gf) {ι : Type} (s : Finset ι) (f : ι → (VS D).V) :
    hat X A (∑ i ∈ s, f i) = ∑ i ∈ s, hat X A (f i) := by
  exact map_sum (AddMonoidHom.mk' (hat X A) (hat_add X A)) f s

theorem hat_ratLink (A : X.B.I.Gf) {b : X.B.I.GA} {β : (VS D).V ≃ₗ[D.host.E] (VS D).V} (h : RatLink X b β)
    (y : (VS D).V) : hat X A (β y) = X.B.I.fmat (A⁻¹ * b.2 * A) *ᵥ hat X A y := by
  obtain ⟨M, -, -, hfm, hcrd⟩ := h
  have hone : X.B.I.fmat 1 = 1 := by simp [AutInst.fmat]
  have hincl : incl X.B.I ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd y) =
      (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) *ᵥ
        incl X.B.I (X.crd y) := by
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp [incl, Matrix.mulVec, dotProduct, map_sum, map_mul]
  simp only [hat]
  rw [hcrd y, Formalism.L2.SG.PoincareInHH.Cut.fmat_mul X, Formalism.L2.SG.PoincareInHH.Cut.fmat_mul X, hfm,
    Matrix.mulVec_mulVec, mul_assoc _ (X.B.I.fmat A), ← Formalism.L2.SG.PoincareInHH.Cut.fmat_mul X,
    mul_inv_cancel, hone, mul_one, ← Matrix.mulVec_mulVec, hincl]

theorem hA_hat (A : X.B.I.Gf) (y z : (VS D).V) :
    hA X.B.I (hat X A y) (hat X A z) = Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm ((VS D).hT y z)) := by
  simp only [hat]
  rw [Formalism.L2.SG.PoincareInHH.Cut.hA_fmat X, Formalism.L2.SG.PoincareInHH.Cut.hA_crd X]

theorem mL_div {m : VA X.B.I} (hm : m ∈ mL X.B.I X.B.g) : ∃ x ∈ X.B.I.Lf, m = (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • x := by
  unfold mL at hm
  induction hm using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, hx, rfl⟩
  | zero => exact ⟨0, zero_mem _, (smul_zero _).symm⟩
  | add a b _ _ ha hb =>
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨x', hx', rfl⟩ := hb
    exact ⟨x + x', add_mem hx hx', (smul_add _ _ _).symm⟩
  | smul c a _ ha =>
    obtain ⟨x, hx, rfl⟩ := ha
    exact ⟨c • x, Submodule.smul_mem _ c hx, smul_comm c _ x⟩

theorem locP_of_InAt (A : X.B.I.Gf) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hlat : ∀ y, y ∈ Λ ↔ hat X A y ∈ X.B.I.Lf) {y : (VS D).V} (hy : InAt X.B.I X.B.g X.B.g (hat X A y))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) :
    y ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ)) := by
  obtain ⟨c, hcop, hc⟩ := hy
  obtain ⟨x, hx, hcx⟩ := mL_div X hc
  have hgB : X.B.g = gS D := X.g_eq
  have hgE : ((gS D : ℕ) : D.host.E) ≠ 0 :=
    Nat.cast_ne_zero.2 (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
  set t : D.host.E := (c : D.host.E) / ((gS D : ℕ) : D.host.E) with ht_def
  have ht : hat X A (t • y) = x := by
    rw [hat_smul]
    have hg0 : ((X.B.g : ℕ) : X.B.I.E) ≠ 0 := by
      rw [hgB]
      exact Nat.cast_ne_zero.2 (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
    have hcast : ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) =
        Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) ((X.B.g : ℕ) : X.B.I.E) := (map_natCast _ _).symm
    have hunit : IsUnit ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := by
      rw [hcast]
      exact (isUnit_iff_ne_zero.2 hg0).map _
    rw [← hunit.smul_left_cancel, ← hcx, smul_smul]
    congr 1
    rw [hcast, ← map_mul, show ((c : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) =
      Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) ((c : ℕ) : X.B.I.E) from (map_natCast _ _).symm]
    congr 1
    apply X.ιE.injective
    rw [map_mul, RingEquiv.apply_symm_apply, map_natCast, map_natCast, hgB, ht_def]
    field_simp
  have hty : t • y ∈ Λ := (hlat _).2 (ht ▸ hx)
  simp only [Formalism.HermitianLatticesTheory.localization₂]
  refine ⟨((c : ℕ) : 𝓞 D.host.E), ?_, ?_⟩
  · show ((c : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal
    intro hcP
    have hcopZ : IsCoprime (c : ℤ) (X.B.g : ℤ) := Nat.isCoprime_iff_coprime.2 hcop
    obtain ⟨a, b, hab⟩ := hcopZ.map (Int.castRingHom (𝓞 D.host.E))
    apply P.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hab]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ ?_)
    · simpa using hcP
    · rw [hgB]
      simpa using hP
  · have hsm : ∀ (o : 𝓞 D.host.E) (v : (VS D).V), o • v = (o : D.host.E) • v :=
      fun o v => (algebraMap_smul D.host.E o v).symm
    have hcy : ((c : ℕ) : 𝓞 D.host.E) • y = ((gS D : ℕ) : 𝓞 D.host.E) • (t • y) := by
      rw [hsm, hsm, smul_smul]
      congr 1
      push_cast
      rw [ht_def]
      field_simp
    rw [hcy]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hty

theorem Mo_le_Lf : Mo X.B.I X.B.g (Set.range X.e0) ≤ X.B.I.Lf := by
  refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨a, rfl⟩
    exact (X.vectorsInLattice.1 a).1
  · rintro y ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Nat.cast_smul_eq_nsmul]
    exact nsmul_mem hx _

theorem ratFromAd (A : X.B.I.Gf) {u : D.what₂.Word} {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hlat : ∀ y, y ∈ Λ ↔ hat X A y ∈ X.B.I.Lf)
    (hfixE : ∀ a, hat X A (X.eX a) = incl X.B.I (X.crd (X.eX a)))
    (hFC : IsFixedConv Λ (gS D) (lf D (X.Fu u))) (hTF : ∀ a, (X.Fu u).e a = X.eX a)
    {y : (VS D).V} (hy : hat X A y ∈ Mo X.B.I X.B.g (Set.range X.e0)) :
    y ∈ NgX Λ (gS D) (lf D (X.Fu u)) (lf D (X.Fu u)) := by
  have hyΛ : y ∈ Λ := (hlat y).2 (Mo_le_Lf X hy)

  obtain ⟨s, hs, m, hm, hsm⟩ := Submodule.mem_sup.1 hy
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (IntAf X.B.I.F X.B.I.E)).1 hs
  choose t c' hc' ht using fun a => PIW.AdelClassFin.dual_dense X.B.I.F X.B.I.E X.B.g
    (Nat.pos_of_ne_zero (Formalism.L2.SG.Pf.ChiNMul.gB_ne_zero X)) (c a : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (c a).2
  set r : (VS D).V := ∑ a, X.ιE ((t a : 𝓞 X.B.I.E) : X.B.I.E) • X.eX a with hr

  have hdiff : InAt X.B.I X.B.g X.B.g (hat X A (y - r)) := by
    have e1 : hat X A (y - r) = (∑ a, Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) ((t a : 𝓞 X.B.I.E) : X.B.I.E) •
        (X.e0 a - incl X.B.I (X.crd (X.eX a)))) +
        ((∑ a, ((X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * c' a) • X.e0 a) + m) := by
      rw [hat_sub, ← hsm, ← hc, hr]
      simp only [hat_sum X A, hat_smul, RingEquiv.symm_apply_apply, hfixE]
      have e2 : ∀ a, (c a : IntAf X.B.I.F X.B.I.E) • X.e0 a =
          (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) ((t a : 𝓞 X.B.I.E) : X.B.I.E) +
            (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * c' a) • X.e0 a := by
        intro a; rw [Subring.smul_def, ht a]
      simp only [e2, add_smul, Finset.sum_add_distrib, smul_sub, Finset.sum_sub_distrib]
      abel
    rw [e1]
    refine InAt_add X (InAt_sum X _ _ fun a _ => InAt_smul X (inclE_mem X.B.I ⟨t a, rfl⟩) (X.basisApprox a).1)
      (InAt_add X ⟨1, Nat.coprime_one_left _, ?_⟩ ⟨1, Nat.coprime_one_left _, by rw [Nat.cast_one, one_smul]; exact hm⟩)
    rw [Nat.cast_one, one_smul]
    refine sum_mem fun a _ => ?_
    rw [mul_smul]
    have : c' a • X.e0 a = (⟨_, hc' a⟩ : IntAf X.B.I.F X.B.I.E) • X.e0 a := rfl
    rw [this]
    exact smul_mem_mL X.B.I (Submodule.smul_mem _ _ (X.vectorsInLattice.1 a).1)
  refine Formalism.L2.SG.Pf.mem_of_forall_locP fun P => ?_
  haveI := P.isPrime
  by_cases hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
  ·
    have h1 := locP_of_InAt X A hlat hdiff P hP
    have h2 : r ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ (lf D (X.Fu u))) := by
      obtain ⟨cc, -, hc1, hloc⟩ := hFC.1 P
      have hc1' := hc1 hP
      rw [hloc]
      rw [hr]
      refine sum_mem fun a _ => ?_
      have hmem : X.eX a ∈ Submodule.span (𝓞 D.host.E) (Set.range fun b => cc b • (lf D (X.Fu u)).fl.e b) :=
        Submodule.subset_span ⟨a, by simp [hc1' a, hTF a, lf]⟩
      have hint : X.ιE ((t a : 𝓞 X.B.I.E) : X.B.I.E) ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
        have := ((t a).2 : IsIntegral ℤ ((t a : 𝓞 X.B.I.E) : X.B.I.E)).map X.ιE.toRingHom.toIntAlgHom
        exact ⟨⟨_, this⟩, rfl⟩
      obtain ⟨o, ho⟩ := hint
      rw [← ho, algebraMap_smul]
      exact Submodule.smul_mem _ _ (Formalism.L2.SG.Pf.mem_localization_of_mem' hmem)
    rw [show y = (y - r) + r by abel]
    exact add_mem (Formalism.L2.SG.Pf.localization_mono (le_sup_left.trans le_sup_left) h1)
      (Formalism.L2.SG.Pf.localization_mono (le_sup_right.trans le_sup_left) h2)
  ·
    refine ⟨((gS D : ℕ) : 𝓞 D.host.E), hP, ?_⟩
    exact (le_sup_left.trans le_sup_left : Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ≤ _)
      (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hyΛ)

end Formalism.L2.SG.Pf.BridgeRat
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IotaBridgeHalves
noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.NormCut

namespace Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def IotaBridgeARC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u : D.what₂.Word)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V), Λ ∈ Y.what₂ u →
    ∀ (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (b : X.B.I.GA), RatLink X b β →
      (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)⁻¹ * b.2 * (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)
        ∈ X.B.I.Kset →
      NCong X ((((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)⁻¹ * b.2 *
        (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)) →
      AdTriv X ((((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)⁻¹ * b.2 *
        (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)) → RatTriv u X Λ β

def IotaBridgeRAC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u : D.what₂.Word)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V), Λ ∈ Y.what₂ u →
    ∀ (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (b : X.B.I.GA), RatLink X b β →
      (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)⁻¹ * b.2 * (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)
        ∈ X.B.I.Kset →
      NCong X ((((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)⁻¹ * b.2 *
        (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)) →
      RatTriv u X Λ β → AdTriv X ((((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)⁻¹ * b.2 *
        (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u))

end Formalism.L2.SG.Pf
end
end

noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.NormCut Formalism.L2.SG.Pf.BridgeRat

namespace Formalism.L2.SG.Pf.BridgeAR

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem Z_of_coprime {t : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (ht : t ∈ IntAf X.B.I.F X.B.I.E) {c : ℕ}
    (hc : Nat.Coprime c X.B.g) (hZ : ZMod' X.B.I X.B.g ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t)) :
    ZMod' X.B.I X.B.g t := by
  obtain ⟨s, hs, hcs⟩ := hZ
  have hb := Nat.gcd_eq_gcd_ab c X.B.g
  rw [hc.gcd_eq_one, Nat.cast_one] at hb
  have hb' : (1 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) =
      (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (Nat.gcdA c X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) +
        (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (Nat.gcdB c X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := by
    have h1 := congrArg (Int.cast : ℤ → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) hb
    push_cast at h1
    exact h1
  refine ⟨(Nat.gcdA c X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s +
    (Nat.gcdB c X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t, ?_, ?_⟩
  · exact (IntAf X.B.I.F X.B.I.E).add_mem
      ((IntAf X.B.I.F X.B.I.E).mul_mem (intCast_mem _ _) hs)
      ((IntAf X.B.I.F X.B.I.E).mul_mem (intCast_mem _ _) ht)
  · calc t = 1 * t := (one_mul t).symm
      _ = ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t) * (Nat.gcdA c X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) +
          (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) *
            ((Nat.gcdB c X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t) := by
        rw [hb']
        ring
      _ = _ := by
        rw [hcs]
        ring

end Formalism.L2.SG.Pf.BridgeAR

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.BridgeAR

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem iotaBridgeARC_holds : IotaBridgeARC := by
  intro D X Y u Λ hΛ β b hb hK hN hT x hx
  set A : X.B.I.Gf := ((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u with hAdef
  have hbl : (Y.cs u).lamOf ((Y.cs u).base Λ) = Λ := (Y.cs u).base_lam Λ hΛ
  have hlat : ∀ y, y ∈ Λ ↔ hat X A y ∈ X.B.I.Lf := fun y => by
    have := (Y.cs u).lat_eq ((Y.cs u).base Λ) y
    rw [hbl] at this
    exact this
  have hfixE : ∀ a, hat X A (X.eX a) = incl X.B.I (X.crd (X.eX a)) := fun a => by
    unfold hat
    exact fixes_inv X (fixes_mul X (((Y.cs u).h ((Y.cs u).base Λ)).2 _ (Or.inl (Or.inl ⟨a, rfl⟩)))
      ((X.xu_fix u a).1))
  have hTF : ∀ a, (X.Fu u).e a = X.eX a := (Formalism.L2.SG.Full.Full.frameTie (X := X) u u).1
  have hFC : IsFixedConv Λ (gS D) (lf D (X.Fu u)) := ((Y.rowsOK u).1 Λ hΛ).2.1.2.2.2
  refine ratFromAd X A hlat hfixE hFC hTF ?_
  rw [hat_sub, hat_ratLink X A hb, show X.B.I.fmat (A⁻¹ * b.2 * A) *ᵥ hat X A x - hat X A x =
    (X.B.I.fmat (A⁻¹ * b.2 * A) - 1) *ᵥ hat X A x by rw [Matrix.sub_mulVec, Matrix.one_mulVec]]
  have hxΛ : x ∈ Λ := hx.1
  have hw : hat X A x ∈ X.B.I.Lf := (hlat x).1 hxΛ
  refine Formalism.L2.SG.Pf.BridgeAd.adFull_of_adTriv Y.TR hK hN hT hw (fun a => ?_)

  have hxo : x ∈ orth (VS D) (Xsp (lf D (X.Fu u))) := hx.2
  have h0 : (VS D).hT (X.eX a) x = 0 := by
    have hmem : X.eX a ∈ Xsp (lf D (X.Fu u)) := by
      rw [← hTF a]
      exact Submodule.subset_span ⟨a, rfl⟩
    have := (Submodule.mem_iInf _).1 hxo (X.eX a)
    exact (Submodule.mem_iInf _).1 this hmem
  have hE0 : hA X.B.I (incl X.B.I (X.crd (X.eX a))) (hat X A x) = 0 := by
    rw [← hfixE a, hA_hat, h0, map_zero, map_zero]
  obtain ⟨c, hc, hcd⟩ := (X.basisApprox a).1
  have hint : hA X.B.I (X.e0 a) (hat X A x) ∈ IntAf X.B.I.F X.B.I.E := hA_int X.B.I (X.vectorsInLattice.1 a).1 hw
  refine Z_of_coprime X hint hc ?_
  have e : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I (X.e0 a) (hat X A x) =
      hA X.B.I ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.e0 a - incl X.B.I (X.crd (X.eX a)))) (hat X A x) := by
    rw [hA_smul_left, hA_sub_left, hE0, sub_zero, map_natCast]
  rw [e]
  exact Z_hA_mL X hcd hw

end Formalism.L2.SG.Pf
end
end

noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.NormCut

namespace Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def IotaDictAllC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
    (s₁ s₂ : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')), s₁.lam = s₂.lam → s₁.lam' = s₂.lam' →
      (iotaOf Y.TR (Y.cs u) (Y.cs u') s₁ = iotaOf Y.TR (Y.cs u) (Y.cs u') s₂ ↔
        IotaCompat s₁.lam (lf D (X.Fu u)) s₁.frame s₂.frame (s₂.lin * s₁.lin⁻¹) (gS D))

theorem levi_split_iff {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (Y : Formalism.L2.SG.Full.Full X) {u u' : D.what₂.Word}
    (s₁ s₂ : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) (hl : s₁.lam = s₂.lam) (hl' : s₁.lam' = s₂.lam') :
    (iotaOf Y.TR (Y.cs u) (Y.cs u') s₁ = iotaOf Y.TR (Y.cs u) (Y.cs u') s₂ ↔
      AdTriv X ((((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) * X.xu u)⁻¹ * (s₂.pt * s₁.pt⁻¹).2 *
        (((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) * X.xu u))) := by
  obtain ⟨gδ, -, hs⟩ := IotaDictPf.iotaOf_split Y s₁ s₂ hl hl'
  have hb2 : (s₂.pt * s₁.pt⁻¹).2 = s₂.pt.2 * s₁.pt.2⁻¹ := by rw [Prod.snd_mul, Prod.snd_inv]
  rw [hb2, AdTriv, ← IotaDictPf.levi_one_iff Y.TR gδ, hs]
  constructor
  · intro h
    exact mul_right_cancel (h.symm.trans (one_mul _).symm)
  · intro h
    rw [h, one_mul]

theorem iotaDict_fwd {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (Y : Formalism.L2.SG.Full.Full X) {u u' : D.what₂.Word}
    (s₁ s₂ : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) (hl : s₁.lam = s₂.lam) (hl' : s₁.lam' = s₂.lam')
    (h : iotaOf Y.TR (Y.cs u) (Y.cs u') s₁ = iotaOf Y.TR (Y.cs u) (Y.cs u') s₂) :
    IotaCompat s₁.lam (lf D (X.Fu u)) s₁.frame s₂.frame (s₂.lin * s₁.lin⁻¹) (gS D) := by
  obtain ⟨gδ, nδ, -⟩ := IotaDictPf.iotaOf_split Y s₁ s₂ hl hl'
  have hb2 : (s₂.pt * s₁.pt⁻¹).2 = s₂.pt.2 * s₁.pt.2⁻¹ := by rw [Prod.snd_mul, Prod.snd_inv]
  have hRL : RatLink X (s₂.pt * s₁.pt⁻¹) (s₂.lin * s₁.lin⁻¹) :=
    Formalism.L2.SG.TermOp.Vanish.ratLink_mul X s₂.rep.2.1 (Formalism.L2.SG.TermOp.Vanish.ratLink_inv X s₁.rep.2.1)
  rw [Formalism.L2.SG.Pf.Act.ratIotaC' Y u u' s₁ s₂ hl hl']
  refine iotaBridgeARC_holds _ X Y u s₁.lam s₁.mem _ _ hRL (by rw [hb2]; exact gδ.1.1) (by rw [hb2]; exact nδ) ?_
  exact (levi_split_iff Y s₁ s₂ hl hl').1 h

theorem iotaDictAllC_of (h2 : IotaBridgeRAC) : IotaDictAllC := by
  intro D X Y u u' s₁ s₂ hl hl'
  refine ⟨iotaDict_fwd Y s₁ s₂ hl hl', fun h => ?_⟩
  obtain ⟨gδ, nδ, -⟩ := IotaDictPf.iotaOf_split Y s₁ s₂ hl hl'
  have hb2 : (s₂.pt * s₁.pt⁻¹).2 = s₂.pt.2 * s₁.pt.2⁻¹ := by rw [Prod.snd_mul, Prod.snd_inv]
  have hRL : RatLink X (s₂.pt * s₁.pt⁻¹) (s₂.lin * s₁.lin⁻¹) :=
    Formalism.L2.SG.TermOp.Vanish.ratLink_mul X s₂.rep.2.1 (Formalism.L2.SG.TermOp.Vanish.ratLink_inv X s₁.rep.2.1)
  rw [Formalism.L2.SG.Pf.Act.ratIotaC' Y u u' s₁ s₂ hl hl'] at h
  exact (levi_split_iff Y s₁ s₂ hl hl').2
    (h2 D X Y u s₁.lam s₁.mem _ _ hRL (by rw [hb2]; exact gδ.1.1) (by rw [hb2]; exact nδ) h)

theorem iotaDictC_holds_of (h2 : IotaBridgeRAC) : IotaDictC :=
  fun D X Y u u' s₁ s₂ _ _ _ _ hl hl' => iotaDictAllC_of h2 D X Y u u' s₁ s₂ hl hl'

end Formalism.L2.SG.Pf
