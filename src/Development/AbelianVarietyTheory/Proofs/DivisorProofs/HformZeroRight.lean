module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
public import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.PNeatB
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelRowsOrthogonalSumOfParts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockEmb
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntAFSmulMemLatOF

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HformZeroRight
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

noncomputable section

namespace GlobalTheory.GramFrame

theorem hform_add_right {A : Type} [CommRing A] {n : Type} [Fintype n] (τ : A →+* A)
    (J : Matrix n n A) (x u v : n → A) : Formalism.UG.hform τ J x (u + v) = Formalism.UG.hform τ J x u + Formalism.UG.hform τ J x v := by
  simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hform_smul_right {A : Type} [CommRing A] {n : Type} [Fintype n] (τ : A →+* A)
    (J : Matrix n n A) (a : A) (x y : n → A) : Formalism.UG.hform τ J x (a • y) = a * Formalism.UG.hform τ J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_zero_right {A : Type} [CommRing A] {n : Type} [Fintype n] (τ : A →+* A)
    (J : Matrix n n A) (x : n → A) : Formalism.UG.hform τ J x 0 = 0 := by
  simp [Formalism.UG.hform]

variable {D : D7}

theorem sigR_inclE (x : D.host.E) :
    Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) x) =
      Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (D.sp.cm.sig x) := by
  simp [Formalism.UG.sigR, Formalism.UG.inclE]

theorem inclE_int (b : 𝓞 D.host.E) :
    Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (algebraMap (𝓞 D.host.E) D.host.E b) ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E :=
  Subring.subset_closure (Or.inl ⟨⟨_, b, rfl⟩, rfl⟩)

theorem hform_inclE {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E) (x y : Fin n → D.host.E) :
    Formalism.UG.hform (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
      (J.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)))
      (fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (x i))
      (fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (y i)) =
    Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (Formalism.UG.hform (D.sp.cm.sig : D.host.E →+* D.host.E) J x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.UG.hform, map_sum, map_mul, sigR_inclE, Matrix.map_apply]
  rfl

theorem pair_hatL {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (h : ∀ x ∈ Λ, ∀ y ∈ Λ, Formalism.UG.hform (D.sp.cm.sig : D.host.E →+* D.host.E) J x y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range)
    (x y : Fin n → Formalism.IndefR.Lev.EAf D) (hx : x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ)
    (hy : y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) :
    Formalism.UG.hform (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
      (J.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))) x y ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨x0, hx0, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨y0, hy0, rfl⟩ := hy
      rw [hform_inclE]
      obtain ⟨b, hb⟩ := h x0 hx0 y0 hy0
      rw [← hb]
      exact inclE_int b
    | zero => rw [hform_zero_right]; exact zero_mem _
    | add a b _ _ ha hb => rw [hform_add_right]; exact add_mem ha hb
    | smul s a _ ha => rw [Subring.smul_def, hform_smul_right]; exact mul_mem s.2 ha
  | zero => rw [Formalism.UG.P.csDual_hform_zero_left]; exact zero_mem _
  | add a b _ _ ha hb => rw [Formalism.UG.P.csDual_hform_add_left]; exact add_mem ha hb
  | smul s a _ ha =>
    rw [Subring.smul_def, Formalism.UG.P.csDual_hform_smul_left]
    exact mul_mem (GlobalTheory.LevSplit.sigR_int s.2) ha

end GlobalTheory.GramFrame

namespace GlobalTheory.GramFrame

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem prV_hform' {n : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    (x y : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) :
    Formalism.UG.prV (E := E) v (Formalism.UG.hform (Formalism.UG.sigR σ (Formalism.L2.Herm.Af F))
      (J.map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F))) x y) =
    Formalism.UG.hform (Formalism.UG.sigR σ (v.adicCompletion F))
      (J.map (Formalism.UG.inclE (F := F) (v.adicCompletion F)))
      (fun i => Formalism.UG.prV (E := E) v (x i)) (fun i => Formalism.UG.prV (E := E) v (y i)) := by
  have hs : ∀ z, Formalism.UG.prV (E := E) v (Formalism.UG.sigR σ (Formalism.L2.Herm.Af F) z) =
      Formalism.UG.sigR σ (v.adicCompletion F) (Formalism.UG.prV (E := E) v z) :=
    fun z => RingHom.congr_fun (Formalism.UG.P.afsplit_prV_comp_sigR σ v) z
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.UG.hform, map_sum, map_mul, hs, Matrix.map_apply]
  rfl

theorem inv_int {n : ℕ} (σ : E →ₐ[F] E)
    (hσ : ∀ s ∈ Formalism.L2.Herm.intAf F E, Formalism.UG.sigR σ (Formalism.L2.Herm.Af F) s ∈ Formalism.L2.Herm.intAf F E)
    (J : Matrix (Fin n) (Fin n) E) (hJ : IsUnit J.det)
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E))
    (hlat : Submodule.IsFullLattice E Λ) (hfr : Formalism.L2.DIV.IsFrame β Λ)
    (hd : Formalism.L2.Forms.dualL (σ : E →+* E) J Λ ≤ Λ)
    (G' : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (hG' : Formalism.UG.cT (Formalism.UG.sigR σ (Formalism.L2.Herm.Af F)) β.val *
      J.map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F)) * β.val * G' = 1) :
    ∀ i j, G' i j ∈ Formalism.L2.Herm.intAf F E := by
  intro i j
  have key : ∀ x ∈ Formalism.L2.Herm.hatL (F := F) Λ,
      Formalism.UG.hform (Formalism.UG.sigR σ (Formalism.L2.Herm.Af F))
        (J.map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F))) x
        (β.val *ᵥ (G' *ᵥ Pi.single j 1)) ∈ Formalism.L2.Herm.intAf F E := by
    intro x hx
    have ha := (hfr x).1 hx
    have e : x = β.val *ᵥ ((β⁻¹).val *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [e, GlobalTheory.DualCompletion.hform_mulVec_left]
    have e2 : (Formalism.UG.cT (Formalism.UG.sigR σ (Formalism.L2.Herm.Af F)) β.val *
        J.map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F))) *ᵥ (β.val *ᵥ (G' *ᵥ Pi.single j 1)) =
        Pi.single j 1 := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hG', Matrix.one_mulVec]
    rw [e2]
    refine Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hσ _ (ha k)) ?_
    rw [Pi.single_apply]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F),
      (fun k => Formalism.UG.prV (E := E) v ((β.val *ᵥ (G' *ᵥ Pi.single j 1)) k)) ∈
        Formalism.UG.latS (F := F) (v.adicCompletion F)
          (Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E)
            (v.adicCompletionIntegers F).toSubring) Λ := by
    intro v
    have hm := (GlobalTheory.DualCompletion.mem_latS_dualL σ J hJ v Λ hlat
      (fun k => Formalism.UG.prV (E := E) v ((β.val *ᵥ (G' *ᵥ Pi.single j 1)) k))).2
    refine Submodule.span_mono (Set.image_mono hd) (hm fun u hu => ?_)
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨x0, hx0, rfl⟩ := hu
      have h3 := key _ (Submodule.subset_span ⟨x0, hx0, rfl⟩)
      have h4 := Formalism.UG.P.afsplit_prV_int (E := E) v _ h3
      rw [prV_hform'] at h4
      exact h4
    | zero => rw [Formalism.UG.P.csDual_hform_zero_left]; exact zero_mem _
    | add a b _ _ ha hb => rw [Formalism.UG.P.csDual_hform_add_left]; exact add_mem ha hb
    | smul s a _ ha =>
      rw [Subring.smul_def, Formalism.UG.P.csDual_hform_smul_left]
      exact mul_mem (Formalism.L2.G.RelativeIndexFlags.sigR_mem v σ s.2) ha
  have hc : β.val *ᵥ (G' *ᵥ Pi.single j 1) ∈ Formalism.L2.Herm.hatL (F := F) Λ :=
    Formalism.L2.Geo.Def.PN.latS_of_loc Λ hlat.span_eq_top _ hloc
  have h5 := (hfr _).1 hc i
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec,
    Matrix.mulVec_single_one] at h5
  exact h5

end General

end GlobalTheory.GramFrame

namespace GlobalTheory.GramFrame

theorem gram_entry {A : Type} [CommRing A] {n : ℕ} (τ : A →+* A) (J B : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    (Formalism.UG.cT τ B * J * B) i j = Formalism.UG.hform τ J (B *ᵥ Pi.single i 1) (B *ᵥ Pi.single j 1) := by
  rw [GlobalTheory.DualCompletion.hform_col, map_one, one_mul, Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
  rfl

end GlobalTheory.GramFrame

namespace GlobalTheory.GramFrame

end GlobalTheory.GramFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryAdelicPointPrescribedFrameImages
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryAdelicPointPrescribedFrameImages
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SphEis.ColImg

open Formalism.UG (cT_mul cT_one)

section Ring

variable {S : Type} [CommRing S] (s : S →+* S)

theorem cT_add' {a b : Type} (M N : Matrix a b S) : cT s (M + N) = cT s M + cT s N := by
  ext i k; simp [cT]

theorem cT_zero' {a b : Type} : cT s (0 : Matrix a b S) = 0 := by
  ext i k; simp [cT]

theorem cT_cT' (hs : ∀ x, s (s x) = x) {a b : Type} (M : Matrix a b S) : cT s (cT s M) = M := by
  ext i k; simp [cT, hs]

theorem cT_gram {n a b : ℕ} (hs : ∀ x, s (s x) = x) (J : Matrix (Fin n) (Fin n) S) (hJ : cT s J = J)
    (M : Matrix (Fin n) (Fin a) S) (N : Matrix (Fin n) (Fin b) S) :
    cT s (cT s M * J * N) = cT s N * J * M := by
  rw [cT_mul, cT_mul, cT_cT' s hs, hJ, Matrix.mul_assoc]

theorem gram_comb {n j m : ℕ} (J : Matrix (Fin n) (Fin n) S) (J0 : Matrix (Fin m) (Fin m) S)
    (A B : Matrix (Fin n) (Fin j) S) (Z : Matrix (Fin n) (Fin m) S)
    (pX pY : Matrix (Fin j) (Fin n) S) (p0 : Matrix (Fin m) (Fin n) S)
    (aa : cT s A * J * A = 0) (bb : cT s B * J * B = 0) (ab : cT s A * J * B = 1) (ba : cT s B * J * A = 1)
    (az : cT s A * J * Z = 0) (bz : cT s B * J * Z = 0) (za : cT s Z * J * A = 0) (zb : cT s Z * J * B = 0)
    (zz : cT s Z * J * Z = J0) :
    cT s (A * pX + Z * p0 + B * pY) * J * (A * pX + Z * p0 + B * pY) =
      cT s pX * pY + cT s p0 * J0 * p0 + cT s pY * pX := by
  have h1 : cT s A * (J * (A * pX + Z * p0 + B * pY)) = pY := by
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, aa, az, ab, Matrix.zero_mul, Matrix.one_mul, zero_add]
  have h2 : cT s Z * (J * (A * pX + Z * p0 + B * pY)) = J0 * p0 := by
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, za, zz, zb, Matrix.zero_mul, zero_add, add_zero]
  have h3 : cT s B * (J * (A * pX + Z * p0 + B * pY)) = pX := by
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, ba, bz, bb, Matrix.zero_mul, Matrix.one_mul, zero_add, add_zero]
  rw [cT_add', cT_add', cT_mul, cT_mul, cT_mul]
  simp only [Matrix.add_mul, Matrix.mul_assoc, h1, h2, h3]

end Ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sig_invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem sigR_invol (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (e : AF F ⊗[F] E) :
    sigR (AF F) σ (sigR (AF F) σ e) = e := by
  induction e using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  | tmul a x => simp [sigR, hσ]

theorem cT_adMat (σ : E →ₐ[F] E) {a b : Type} (X : Matrix a b E) :
    cT (sigR (AF F) σ) (adMat F X) = adMat F (cT (σ : E →+* E) X) := by
  ext i k; simp [cT, adMat, sigR, inclR]

end GlobalTheory.SphEis.ColImg

namespace GlobalTheory.SphEis.ColImg

open Formalism.UG (cT_mul cT_one)

section Ring

variable {S : Type} [CommRing S] (s : S →+* S)

theorem images_ring {n j m : ℕ} (Ja Jai : Matrix (Fin n) (Fin n) S) (j0 k0 : Matrix (Fin m) (Fin m) S)
    (hJi : Jai * Ja = 1) (hk0 : k0 * j0 = 1)
    (c d C' D' : Matrix (Fin n) (Fin j) S) (z Z' : Matrix (Fin n) (Fin m) S)
    (cc : cT s c * Ja * c = 0) (dd : cT s d * Ja * d = 0) (cd : cT s c * Ja * d = 1) (dc : cT s d * Ja * c = 1)
    (cz : cT s c * Ja * z = 0) (dz : cT s d * Ja * z = 0) (zc : cT s z * Ja * c = 0) (zd : cT s z * Ja * d = 0)
    (zz : cT s z * Ja * z = j0)
    (sum : c * (cT s d * Ja) + z * (k0 * (cT s z * Ja)) + d * (cT s c * Ja) = 1)
    (cc' : cT s C' * Ja * C' = 0) (dd' : cT s D' * Ja * D' = 0) (cd' : cT s C' * Ja * D' = 1) (dc' : cT s D' * Ja * C' = 1)
    (cz' : cT s C' * Ja * Z' = 0) (dz' : cT s D' * Ja * Z' = 0) (zc' : cT s Z' * Ja * C' = 0) (zd' : cT s Z' * Ja * D' = 0)
    (zz' : cT s Z' * Ja * Z' = j0) :
    ∃ u : GL (Fin n) S, cT s u.1 * Ja * u.1 = Ja ∧ u.1 * c = C' ∧ u.1 * z = Z' ∧ u.1 * d = D' := by
  obtain ⟨pX, hpX⟩ : ∃ p, p = cT s d * Ja := ⟨_, rfl⟩
  obtain ⟨p0, hp0⟩ : ∃ p, p = k0 * (cT s z * Ja) := ⟨_, rfl⟩
  obtain ⟨pY, hpY⟩ : ∃ p, p = cT s c * Ja := ⟨_, rfl⟩
  rw [← hpX, ← hp0, ← hpY] at sum
  have Xc : pX * c = 1 := by rw [hpX, dc]
  have Xz : pX * z = 0 := by rw [hpX, dz]
  have Xd : pX * d = 0 := by rw [hpX, dd]
  have Yc : pY * c = 0 := by rw [hpY, cc]
  have Yz : pY * z = 0 := by rw [hpY, cz]
  have Yd : pY * d = 1 := by rw [hpY, cd]
  have Oc : p0 * c = 0 := by rw [hp0, Matrix.mul_assoc, zc, Matrix.mul_zero]
  have Oz : p0 * z = 1 := by rw [hp0, Matrix.mul_assoc, zz, hk0]
  have Od : p0 * d = 0 := by rw [hp0, Matrix.mul_assoc, zd, Matrix.mul_zero]
  obtain ⟨g, hg⟩ : ∃ g, g = C' * pX + Z' * p0 + D' * pY := ⟨_, rfl⟩
  have gram : cT s g * Ja * g = Ja := by
    rw [hg, gram_comb s Ja j0 C' D' Z' pX pY p0 cc' dd' cd' dc' cz' dz' zc' zd' zz',
      ← gram_comb s Ja j0 c d z pX pY p0 cc dd cd dc cz dz zc zd zz, sum, cT_one, Matrix.one_mul, Matrix.mul_one]
  have hl : (Jai * cT s g * Ja) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT s g), gram, hJi]
  have hr : g * (Jai * cT s g * Ja) = 1 := mul_eq_one_comm.1 hl
  refine ⟨⟨g, Jai * cT s g * Ja, hr, hl⟩, gram, ?_, ?_, ?_⟩
  · change g * c = C'
    simp only [hg, Matrix.add_mul, Matrix.mul_assoc, Xc, Oc, Yc, Matrix.mul_zero, Matrix.mul_one, add_zero]
  · change g * z = Z'
    simp only [hg, Matrix.add_mul, Matrix.mul_assoc, Xz, Oz, Yz, Matrix.mul_zero, Matrix.mul_one, add_zero, zero_add]
  · change g * d = D'
    simp only [hg, Matrix.add_mul, Matrix.mul_assoc, Xd, Od, Yd, Matrix.mul_zero, Matrix.mul_one, add_zero, zero_add]

end Ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem adMat_gram (σ : E →ₐ[F] E) {n a b : ℕ} (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin a) E)
    (Y : Matrix (Fin n) (Fin b) E) (R : Matrix (Fin a) (Fin b) E) (h : cT (σ : E →+* E) X * J * Y = R) :
    cT (sigR (AF F) σ) (adMat F X) * adMat F J * adMat F Y = adMat F R := by
  rw [cT_adMat, adMat, adMat, adMat, adMat, ← Matrix.map_mul, ← Matrix.map_mul, h]

theorem adMat_zero' {a b : Type} : adMat F (0 : Matrix a b E) = 0 := Matrix.map_zero _ (map_zero _)

theorem adMat_one' {a : Type} [DecidableEq a] : adMat F (1 : Matrix a a E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

theorem adMat_mul' {a b c : Type} [Fintype b] (X : Matrix a b E) (Y : Matrix b c E) :
    adMat F (X * Y) = adMat F X * adMat F Y := Matrix.map_mul

end GlobalTheory.SphEis.ColImg

namespace GlobalTheory.SphEis.ColImg

open Formalism.UG (cT_mul cT_one)

theorem exists_point_images :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ (C' D' : Matrix (Fin n) (Fin j) (AF F ⊗[F] E)) (Z' : Matrix (Fin n) (Fin m) (AF F ⊗[F] E)), cT (sigR (AF F) σ) C' * adMat F J * C' = 0 → cT (sigR (AF F) σ) D' * adMat F J * D' = 0 → cT (sigR (AF F) σ) C' * adMat F J * D' = 1 → cT (sigR (AF F) σ) C' * adMat F J * Z' = 0 → cT (sigR (AF F) σ) D' * adMat F J * Z' = 0 → cT (sigR (AF F) σ) Z' * adMat F J * Z' = adMat F J₀ → ∃ g : GAd σ J, (matHom _ σ J g).1 * adMat F C = C' ∧ (matHom _ σ J g).1 * adMat F Z = Z' ∧ (matHom _ σ J g).1 * adMat F D = D' := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ fr C' D' Z' cc dd cd cz dz zz
  have hσ : ∀ x, σ (σ x) = x := sig_invol fr.cm
  have hs : ∀ x, sigR (AF F) σ (sigR (AF F) σ x) = x := sigR_invol σ hσ
  have hJ : cT (sigR (AF F) σ) (adMat F J) = adMat F J := by rw [cT_adMat, cT_form fr.herm]
  have dc : cT (sigR (AF F) σ) D' * adMat F J * C' = 1 := by
    rw [← cT_gram _ hs _ hJ, cd, cT_one]
  have zc : cT (sigR (AF F) σ) Z' * adMat F J * C' = 0 := by rw [← cT_gram _ hs _ hJ, cz, cT_zero']
  have zd : cT (sigR (AF F) σ) Z' * adMat F J * D' = 0 := by rw [← cT_gram _ hs _ hJ, dz, cT_zero']
  have acc := adMat_gram (F := F) σ J C C 0 fr.cc
  have add := adMat_gram (F := F) σ J D D 0 fr.dd
  have acd := adMat_gram (F := F) σ J C D 1 fr.cd
  have adc := adMat_gram (F := F) σ J D C 1 fr.dc
  have acz := adMat_gram (F := F) σ J C Z 0 fr.cz
  have adz := adMat_gram (F := F) σ J D Z 0 fr.dz
  have azc := adMat_gram (F := F) σ J Z C 0 fr.zc
  have azd := adMat_gram (F := F) σ J Z D 0 fr.zd
  have azz := adMat_gram (F := F) σ J Z Z J₀ fr.zz
  rw [adMat_zero'] at acc add acz adz azc azd
  rw [adMat_one'] at acd adc
  have hJ0 : adMat F J₀⁻¹ * adMat F J₀ = 1 := by
    rw [← adMat_mul', Matrix.nonsing_inv_mul _ (det_isUnit fr.herm₀), adMat_one']
  have hJi : adMat F J⁻¹ * adMat F J = 1 := by
    rw [← adMat_mul', Matrix.nonsing_inv_mul _ (det_isUnit fr.herm), adMat_one']
  have hsum : adMat F C * (cT (sigR (AF F) σ) (adMat F D) * adMat F J) +
      adMat F Z * (adMat F J₀⁻¹ * (cT (sigR (AF F) σ) (adMat F Z) * adMat F J)) +
      adMat F D * (cT (sigR (AF F) σ) (adMat F C) * adMat F J) = 1 := by
    have := congrArg (adMat F) fr.sum
    rw [adMat_one'] at this
    rw [← this, cT_adMat, cT_adMat, cT_adMat]
    simp only [adMat_mul', adMat, Matrix.map_add _ (map_add _)]
  obtain ⟨u, hu, h1, h2, h3⟩ := images_ring (sigR (AF F) σ) (adMat F J) (adMat F J⁻¹) (adMat F J₀) (adMat F J₀⁻¹) hJi hJ0
    (adMat F C) (adMat F D) C' D' (adMat F Z) Z' acc add acd adc acz adz azc azd azz hsum cc dd cd dc cz dz zc zd zz
  exact ⟨(show HA (AF F) σ J from (⟨u, hu⟩ : HR (AF F) σ J)), h1, h2, h3⟩

end GlobalTheory.SphEis.ColImg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryAdelicPointPrescribedFrameImagesStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryAdelicPoint_prescribed_frameImages : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ (C' D' : Matrix (Fin n) (Fin j) (AF F ⊗[F] E)) (Z' : Matrix (Fin n) (Fin m) (AF F ⊗[F] E)), cT (sigR (AF F) σ) C' * adMat F J * C' = 0 → cT (sigR (AF F) σ) D' * adMat F J * D' = 0 → cT (sigR (AF F) σ) C' * adMat F J * D' = 1 → cT (sigR (AF F) σ) C' * adMat F J * Z' = 0 → cT (sigR (AF F) σ) D' * adMat F J * Z' = 0 → cT (sigR (AF F) σ) Z' * adMat F J * Z' = adMat F J₀ → ∃ g : GAd σ J, (matHom _ σ J g).1 * adMat F C = C' ∧ (matHom _ σ J g).1 * adMat F Z = Z' ∧ (matHom _ σ J g).1 * adMat F D = D' := by
  first | exact @GlobalTheory.SphEis.ColImg.exists_point_images | exact GlobalTheory.SphEis.ColImg.exists_point_images | (intros; apply GlobalTheory.SphEis.ColImg.exists_point_images <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalSquaringPathUniqueOfAgreeLowDegrees
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomPowerSeriesEqOfRescale
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem coeff_mul_of_coeff_lt_eq_zero {R : Type} [CommRing R] (φ δ : PowerSeries R) (j : ℕ)
    (h : ∀ i < j, PowerSeries.coeff i δ = 0) :
    PowerSeries.coeff j (φ * δ) = PowerSeries.constantCoeff φ * PowerSeries.coeff j δ := by
  rw [PowerSeries.coeff_mul, Finset.sum_eq_single (0, j)]
  · simp
  · rintro ⟨a, b⟩ hp hne
    have hp : a + b = j := by simpa using hp
    have hb : b < j := by
      by_contra hb
      have ha : a = 0 := by omega
      have hb' : b = j := by omega
      subst ha hb'
      exact hne rfl
    rw [h _ hb, mul_zero]
  · intro hn
    exact absurd (by simp) hn

theorem ringHom_powerSeries_eq_of_rescale :
    ∀ (A B R : Type) [CommRing A] [CommRing B] [CommRing R] (π : B →+* A) (ε : A →+* B) (m : A →+* A) (β : B →+* R) (c : R) (n : ℕ), ε.comp π = RingHom.id B → m.comp π = π → ε.comp m = ε → (∀ f ∈ RingHom.ker ε, m f - 2 * f ∈ RingHom.ker ε ^ 2) → 0 < n → (∀ j, n ≤ j → IsUnit (c ^ j - 2)) → ∀ γ γ' : A →+* PowerSeries R, γ.comp π = PowerSeries.C.comp β → γ'.comp π = PowerSeries.C.comp β → PowerSeries.constantCoeff.comp γ = β.comp ε → PowerSeries.constantCoeff.comp γ' = β.comp ε → (PowerSeries.rescale c).comp γ = γ.comp m → (PowerSeries.rescale c).comp γ' = γ'.comp m → (∀ j < n, ∀ f, PowerSeries.coeff j (γ f) = PowerSeries.coeff j (γ' f)) → γ = γ' := by
  intro A B R _ _ _ π ε m β c n hεπ hmπ _hεm hm hn hc γ γ' hγπ hγ'π hγ0 hγ'0 hγm hγ'm hlow
  have hεπ' : ∀ b, ε (π b) = b := fun b => by simpa using RingHom.congr_fun hεπ b
  have hmπ' : ∀ b, m (π b) = π b := fun b => by simpa using RingHom.congr_fun hmπ b
  have hγπ' : ∀ b, γ (π b) = PowerSeries.C (β b) := fun b => by simpa using RingHom.congr_fun hγπ b
  have hγ'π' : ∀ b, γ' (π b) = PowerSeries.C (β b) := fun b => by simpa using RingHom.congr_fun hγ'π b
  have hc0 : ∀ f, PowerSeries.constantCoeff (γ f) = β (ε f) := fun f => by
    simpa using RingHom.congr_fun hγ0 f
  have hc0' : ∀ f, PowerSeries.constantCoeff (γ' f) = β (ε f) := fun f => by
    simpa using RingHom.congr_fun hγ'0 f
  have hγm' : ∀ f, γ (m f) = PowerSeries.rescale c (γ f) := fun f => by
    simpa using (RingHom.congr_fun hγm f).symm
  have hγ'm' : ∀ f, γ' (m f) = PowerSeries.rescale c (γ' f) := fun f => by
    simpa using (RingHom.congr_fun hγ'm f).symm
  have hcoeff : ∀ j, ∀ f, PowerSeries.coeff j (γ f) = PowerSeries.coeff j (γ' f) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
    rcases lt_or_ge j n with hj | hj
    · exact hlow j hj
    have hj0 : j ≠ 0 := by omega
    obtain ⟨D, hD⟩ : ∃ D : A → R, ∀ f, D f = PowerSeries.coeff j (γ f) - PowerSeries.coeff j (γ' f) :=
      ⟨_, fun _ => rfl⟩
    have hlowδ : ∀ f, ∀ i < j, PowerSeries.coeff i (γ f - γ' f) = 0 := by
      intro f i hi; rw [map_sub, ih i hi f, sub_self]
    have Dadd : ∀ f g, D (f + g) = D f + D g := by
      intro f g; simp only [hD, map_add (f := _)]; ring
    have Dsub : ∀ f g, D (f - g) = D f - D g := by
      intro f g; simp only [hD, map_sub]; ring
    have Dmul : ∀ f g, D (f * g) = β (ε f) * D g + β (ε g) * D f := by
      intro f g
      have e : γ (f * g) - γ' (f * g) = γ f * (γ g - γ' g) + γ' g * (γ f - γ' f) := by
        rw [map_mul, map_mul]; ring
      have h1 := coeff_mul_of_coeff_lt_eq_zero (γ f) _ j (hlowδ g)
      have h2 := coeff_mul_of_coeff_lt_eq_zero (γ' g) _ j (hlowδ f)
      have h3 : D (f * g) = PowerSeries.coeff j (γ (f * g) - γ' (f * g)) := by
        rw [hD, map_sub]
      rw [h3, e, map_add (f := _), h1, h2, hc0, hc0', map_sub, map_sub, hD, hD]
    have Dπ : ∀ b, D (π b) = 0 := by
      intro b; rw [hD, hγπ', hγ'π', PowerSeries.coeff_C, if_neg hj0, sub_self]
    have Dsq : ∀ x ∈ RingHom.ker ε ^ 2, D x = 0 := by
      intro x hx
      rw [pow_two] at hx
      refine Submodule.mul_induction_on hx ?_ ?_
      · intro a ha b hb
        rw [RingHom.mem_ker] at ha hb
        rw [Dmul, ha, hb, map_zero, zero_mul, zero_mul, add_zero]
      · intro x y hx hy
        rw [Dadd, hx, hy, add_zero]
    have Dm2 : ∀ f, D (m f) = 2 * D f := by
      intro f
      set f0 := f - π (ε f) with hf0
      have hf0k : f0 ∈ RingHom.ker ε := by
        rw [RingHom.mem_ker, hf0, map_sub, hεπ', sub_self]
      have hmf : m f = π (ε f) + m f0 := by
        rw [hf0, map_sub, hmπ']; ring
      have hff : f = π (ε f) + f0 := by rw [hf0]; ring
      have hDf : D f = D f0 := by
        conv_lhs => rw [hff]
        rw [Dadd, Dπ, zero_add]
      have hsplit : m f0 = (m f0 - 2 * f0) + (f0 + f0) := by ring
      rw [hmf, Dadd, Dπ, zero_add, hsplit, Dadd, Dsq _ (hm f0 hf0k), Dadd, hDf]
      ring
    have Dmc : ∀ f, D (m f) = c ^ j * D f := by
      intro f
      rw [hD, hD, hγm', hγ'm', PowerSeries.coeff_rescale, PowerSeries.coeff_rescale]
      ring
    intro f
    have h0 : (c ^ j - 2) * D f = 0 := by
      have := (Dmc f).symm.trans (Dm2 f)
      rw [sub_mul, this, sub_self]
    have hDf0 : D f = 0 := (hc j hj).mul_right_eq_zero.mp h0
    rw [hD] at hDf0
    exact sub_eq_zero.mp hDf0
  exact RingHom.ext fun f => PowerSeries.ext fun j => hcoeff j f

end GlobalTheory.Nef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalSquaringPathUniqueOfAgreeLowDegrees
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem exists_spMap_fromSpecStalk {A : Type} [CommRing A] [IsLocalRing A] {X : Scheme.{0}} (f : Sp A ⟶ X) (x : X)
    (hx : f (IsLocalRing.closedPoint (CommRingCat.of A)) = x) :
    ∃ g0 : X.presheaf.stalk x →+* A, spMap g0 ≫ X.fromSpecStalk x = f := by
  subst hx
  exact ⟨(Scheme.stalkClosedPointTo f).hom, Scheme.Spec_stalkClosedPointTo_fromSpecStalk f⟩

theorem ringHom_eq_of_fromSpecStalk {X : Scheme.{0}} (x : X) {B : Type} [CommRing B]
    (f f' : X.presheaf.stalk x →+* B) (h : spMap f ≫ X.fromSpecStalk x = spMap f' ≫ X.fromSpecStalk x) : f = f' := by
  have h' : spMap f = spMap f' := (cancel_mono (X.fromSpecStalk x)).mp h
  have := Spec.map_injective h'
  exact congrArg CommRingCat.Hom.hom this

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_constantCoeff_closedPoint (R : Type) [CommRing R] [IsLocalRing R] : (spMap (PowerSeries.constantCoeff (R := R))) (IsLocalRing.closedPoint (CommRingCat.of R)) = IsLocalRing.closedPoint (CommRingCat.of (PowerSeries R)) := by
  haveI : IsLocalHom (CommRingCat.Hom.hom (CommRingCat.ofHom (PowerSeries.constantCoeff (R := R)))) :=
    ⟨fun _ h => PowerSeries.isUnit_iff_constantCoeff.mpr h⟩
  exact Spec_closedPoint

end GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem path_unique : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R], ∀ [IsLocalRing R], QuasiSeparated G.hom → ∀ (c : R) (n : ℕ), 0 < n → (∀ j, n ≤ j → IsUnit (c ^ j - 2)) → ∀ (b : Sp R ⟶ S) (ξ ξ' : Sp (PowerSeries R) ⟶ G.left), IsPath G c b ξ → IsPath G c b ξ' → (∀ (U : G.left.Opens) (h : ⊤ ≤ ξ ⁻¹ᵁ U) (h' : ⊤ ≤ ξ' ⁻¹ᵁ U) (f : Γ(G.left, U)) (j : ℕ), 0 < j → j < n → PowerSeries.coeff j (evAt ξ h f) = PowerSeries.coeff j (evAt ξ' h' f)) → ξ = ξ' := by
  intro S G _ R _ _ hqs c n hn hc b ξ ξ' hξ hξ' hlow
  set s : S := b (IsLocalRing.closedPoint (CommRingCat.of R)) with hs
  set x : G.left := unitSec G s with hx
  have hpt : ∀ q0 : Sp (PowerSeries R) ⟶ G.left, IsPath G c b q0 →
      q0 (IsLocalRing.closedPoint (CommRingCat.of (PowerSeries R))) = x := by
    intro q0 hq0
    have e := congrArg (fun q : Sp R ⟶ G.left => q (IsLocalRing.closedPoint (CommRingCat.of R))) hq0.zero
    change q0 (spMap PowerSeries.constantCoeff (IsLocalRing.closedPoint (CommRingCat.of R))) = unitSec G s at e
    rw [spMap_constantCoeff_closedPoint] at e
    exact e
  obtain ⟨π, ε, m, hSD, h1, h2, h3⟩ := GlobalTheory.T.exists_groupSchemeUnitStalkData S G s
  have hm := GlobalTheory.T.groupSchemeSquaring_cotangent_eq_two S G hqs s π ε m hSD
  obtain ⟨β, hβ⟩ := exists_spMap_fromSpecStalk b s rfl
  obtain ⟨g, hg⟩ := exists_spMap_fromSpecStalk ξ x (hpt ξ hξ)
  obtain ⟨g', hg'⟩ := exists_spMap_fromSpecStalk ξ' x (hpt ξ' hξ')
  have E1 : ∀ (k : G.left.presheaf.stalk x →+* PowerSeries R), IsPath G c b (spMap k ≫ G.left.fromSpecStalk x) →
      k.comp π = PowerSeries.C.comp β := by
    intro k hk
    apply ringHom_eq_of_fromSpecStalk s
    rw [spMap_comp' π k, spMap_comp' β PowerSeries.C, Category.assoc, Category.assoc, hβ, hSD.str, ← Category.assoc, hk.base]
  have E2 : ∀ (k : G.left.presheaf.stalk x →+* PowerSeries R), IsPath G c b (spMap k ≫ G.left.fromSpecStalk x) →
      PowerSeries.constantCoeff.comp k = β.comp ε := by
    intro k hk
    apply ringHom_eq_of_fromSpecStalk x
    rw [spMap_comp' k PowerSeries.constantCoeff, spMap_comp' ε β, Category.assoc, Category.assoc, hSD.unit, ← Category.assoc (spMap β), hβ, hk.zero]
  have E3 : ∀ (k : G.left.presheaf.stalk x →+* PowerSeries R), IsPath G c b (spMap k ≫ G.left.fromSpecStalk x) →
      (PowerSeries.rescale c).comp k = k.comp m := by
    intro k hk
    apply ringHom_eq_of_fromSpecStalk x
    rw [spMap_comp' k (PowerSeries.rescale c), spMap_comp' m k, Category.assoc, Category.assoc, hSD.sq, hk.scale, Category.assoc]
  subst hg hg'
  have hlow' : ∀ j < n, ∀ f, PowerSeries.coeff j (g f) = PowerSeries.coeff j (g' f) := by
    intro j hj f
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · have a := RingHom.congr_fun (E2 g hξ) f
      have a' := RingHom.congr_fun (E2 g' hξ') f
      simp only [RingHom.comp_apply] at a a'
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_zero_eq_constantCoeff_apply, a, a']
    · obtain ⟨U, hxU, f0, rfl⟩ := TopCat.Presheaf.germ_exist _ f
      obtain ⟨hh, hev⟩ := (GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk).2.2.2.2.2.2 (PowerSeries R) G.left x g U hxU
      obtain ⟨hh', hev'⟩ := (GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk).2.2.2.2.2.2 (PowerSeries R) G.left x g' U hxU
      have := hlow U hh hh' f0 j hj0 hj
      rw [hev, hev'] at this
      exact this
  have := ringHom_powerSeries_eq_of_rescale _ _ R π ε m β c n h1 h2 h3 hm hn hc g g' (E1 g hξ) (E1 g' hξ')
    (E2 g hξ) (E2 g' hξ') (E3 g hξ) (E3 g' hξ') hlow'
  rw [this]

end GlobalTheory.Nef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalSquaringPathUniqueOfAgreeLowDegreesStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalSquaringPath_unique_of_agree_low_degrees : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R], ∀ [IsLocalRing R], QuasiSeparated G.hom → ∀ (c : R) (n : ℕ), 0 < n → (∀ j, n ≤ j → IsUnit (c ^ j - 2)) → ∀ (b : Sp R ⟶ S) (ξ ξ' : Sp (PowerSeries R) ⟶ G.left), IsPath G c b ξ → IsPath G c b ξ' → (∀ (U : G.left.Opens) (h : ⊤ ≤ ξ ⁻¹ᵁ U) (h' : ⊤ ≤ ξ' ⁻¹ᵁ U) (f : Γ(G.left, U)) (j : ℕ), 0 < j → j < n → PowerSeries.coeff j (evAt ξ h f) = PowerSeries.coeff j (evAt ξ' h' f)) → ξ = ξ' := by
  first | exact @GlobalTheory.Nef.path_unique | exact GlobalTheory.Nef.path_unique | (intros; apply GlobalTheory.Nef.path_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerRepNormalizesHeisenbergFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerRepNormalizesHeisenbergFinite
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil

noncomputable section

namespace GlobalTheory.FinLatHeis

open GlobalTheory.FinLatF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}

theorem unitary_mtF {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : GAF σ J) :
    ((mtF σ J g).map (cAF σ))ᵀ * J.map (incAF F E) * mtF σ J g = J.map (incAF F E) :=
  g.2

theorem hOF_actOF (hS : IsHermND σ JS) (g : GAF σ JS) (h : GAF σ JT) (x y : WOF F E nS nT) :
    hOF σ JS JT (actOF σ JS JT g h x) (actOF σ JS JT g h y) = hOF σ JS JT x y := by
  have hu : IsUnit JS.det := isUnit_iff_ne_zero.mpr hS.2
  have h1 : JS⁻¹.map (incAF F E) * JS.map (incAF F E) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu]
    exact Matrix.map_one _ (incAF F E).map_zero (incAF F E).map_one
  exact GlobalTheory.SymplOInv.sum_unitary (cAF σ) (JT.map (incAF F E)) (mtF σ JT h) (JS⁻¹.map (incAF F E))
    (JS.map (incAF F E)) (mtF σ JS g⁻¹) h1 (unitary_mtF h) (unitary_mtF g⁻¹) x y

theorem symplOHF_actOF (hS : IsHermND σ JS) (ξ₀ : E) (g : GAF σ JS) (h : GAF σ JT) (x y : WOF F E nS nT) :
    symplOHF σ JS JT ξ₀ (actOF σ JS JT g h x) (actOF σ JS JT g h y) = symplOHF σ JS JT ξ₀ x y := by
  unfold symplOHF symplOF
  rw [hOF_actOF hS]


variable (F E) in
def realIdF : AEF F E := algebraMap (AF F) (AEF F E) (pairA F 1 0)

theorem infPartF_realIdF : infPartF F E (realIdF F E) = 1 := by
  show Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (pairA F 1 0 ⊗ₜ[F] (1 : E)) = 1
  rw [Algebra.TensorProduct.map_tmul, show fstA F (pairA F 1 0) = 1 from rfl]
  rfl

theorem realIdF_mul_of_inf {z : AEF F E} (hz : infPartF F E z = 0) : realIdF F E * z = 0 := by
  rw [realIdF, ← Algebra.smul_def]
  exact GlobalTheory.HeisThetaF.smul_eq_zero_of_infPartF hz

theorem realIdF_smul_of_fin {x : WOF F E nS nT} (hx : x.map (infPartF F E) = 0) : realIdF F E • x = 0 := by
  ext i j
  exact realIdF_mul_of_inf (congrFun (congrFun hx i) j)

theorem fin_part (w₀ : WOF F E nS nT) : ((1 - realIdF F E) • w₀).map (infPartF F E) = 0 := by
  funext i j
  show infPartF F E ((1 - realIdF F E) * w₀ i j) = 0
  rw [map_mul, map_sub, infPartF_realIdF, map_one, sub_self, zero_mul]

theorem decomp (w₀ : WOF F E nS nT) : w₀ = realIdF F E • w₀ + (1 - realIdF F E) • w₀ := by
  rw [← add_smul, add_sub_cancel, one_smul]

theorem symplOF_real_fin (hσ : ∀ x, σ (σ x) = x) (ξ₀ : E) (u : WOF F E nS nT) {x : WOF F E nS nT}
    (hx : x.map (infPartF F E) = 0) : symplOF σ JS JT ξ₀ (realIdF F E • u) x = 0 := by
  rw [symplOF_smul σ JS JT hσ, realIdF, GlobalTheory.HeisThetaF.cAF_algebraMap, ← realIdF, realIdF_smul_of_fin hx,
    GlobalTheory.HeisLineF.symplOF_zero_right]

theorem symplOHF_real_fin (hσ : ∀ x, σ (σ x) = x) (ξ₀ : E) (u : WOF F E nS nT) {x : WOF F E nS nT}
    (hx : x.map (infPartF F E) = 0) : symplOHF σ JS JT ξ₀ (realIdF F E • u) x = 0 := by
  unfold symplOHF; rw [symplOF_real_fin hσ ξ₀ u hx, mul_zero]

theorem symplOHF_fin_real (hσ : ∀ x, σ (σ x) = x) (hS : IsHermND σ JS) (hT : IsHermND σ JT) {ξ₀ : E}
    (hξ : σ ξ₀ = -ξ₀) (u : WOF F E nS nT) {x : WOF F E nS nT}
    (hx : x.map (infPartF F E) = 0) : symplOHF σ JS JT ξ₀ x (realIdF F E • u) = 0 := by
  unfold symplOHF
  rw [GlobalTheory.HeisLineF.symplOF_skew σ JS JT hσ hS hT ξ₀ hξ, symplOF_real_fin hσ ξ₀ u hx, neg_zero, mul_zero]

theorem realIdF_smul_mtF {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {g : GAF σ J} (hg : g ∈ GlobalTheory.WeilPartsF.GfCF σ J) :
    realIdF F E • mtF σ J g = realIdF F E • (1 : Matrix (Fin n) (Fin n) (AEF F E)) := by
  have h : (mtF σ J g).map (infPartF F E) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hg)
  rw [← sub_eq_zero, ← smul_sub]
  refine Matrix.ext fun i j => ?_
  show realIdF F E * (mtF σ J g - 1) i j = 0
  refine realIdF_mul_of_inf ?_
  rw [Matrix.sub_apply, map_sub, sub_eq_zero]
  refine (congrFun (congrFun h i) j).trans ?_
  rw [← Matrix.map_one (infPartF F E) (infPartF F E).map_zero (infPartF F E).map_one]
  rfl

theorem actOF_real {g : GAF σ JS} {h : GAF σ JT} (hg : g ∈ GlobalTheory.WeilPartsF.GfCF σ JS)
    (hh : h ∈ GlobalTheory.WeilPartsF.GfCF σ JT) (u : WOF F E nS nT) :
    actOF σ JS JT g h (realIdF F E • u) = realIdF F E • u := by
  have h1 := realIdF_smul_mtF hh
  have h2 := realIdF_smul_mtF ((GlobalTheory.WeilPartsF.GfCF σ JS).inv_mem hg)
  unfold actOF
  have hI : realIdF F E * realIdF F E = realIdF F E := by
    rw [realIdF, ← map_mul]
    congr 1
    show ((1 : Ainf F) * 1, (0 : Af F) * 0) = ((1 : Ainf F), (0 : Af F))
    rw [one_mul, mul_zero]
  calc mtF σ JT h * (realIdF F E • u) * mtF σ JS g⁻¹
      = (realIdF F E • mtF σ JT h) * u * (realIdF F E • mtF σ JS g⁻¹) := by
        rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, hI]
    _ = realIdF F E • u := by
        rw [h1, h2, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, hI]

end GlobalTheory.FinLatHeis

namespace GlobalTheory.FinLatHeis

open GlobalTheory.FinLatF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {ψ : AddChar (AF F) ℂ}

theorem phaseF_rhoFF (hS : IsHermND σ JS) (w : 𝓞 E) (p : GAF σ JS × GAF σ JT) (x : XFF F E nS nT) :
    phaseF σ JS JT ξ₀ ψ w (rhoFF σ JS JT p x) = phaseF σ JS JT ξ₀ ψ w x := by
  rw [phaseF, phaseF, coe_rhoFF, ← actOF_smul, symplOHF_actOF hS]

theorem phaseF_ne_zero (w : 𝓞 E) (x : XFF F E nS nT) : phaseF σ JS JT ξ₀ ψ w x ≠ 0 := by
  intro h0
  have h := AddChar.map_add_eq_mul ψ (-symplOHF σ JS JT ξ₀ (intAF F w • (x : WOF F E nS nT)) x)
    (symplOHF σ JS JT ξ₀ (intAF F w • (x : WOF F E nS nT)) x)
  rw [neg_add_cancel, AddChar.map_zero_eq_one] at h
  rw [phaseF] at h0
  rw [h0, zero_mul] at h
  exact one_ne_zero h

variable {hc : HeisClosedF σ JS JT ξ₀ ψ} {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {w : 𝓞 E}
  {lam : ℕ →* ℂ} {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ)}

theorem comm (hσ : ∀ x, σ (σ x) = x) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (hξ : σ ξ₀ = -ξ₀)
    (hR : IsLatRepF σ JS JT ξ₀ ψ hc Λ w lam Om)
    (L : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ →ₗ[ℂ] GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ)
    (hL : ∀ x v, L (opFF hc w x v) = opFF hc w x (L v))
    (p : GAF σ JS × GAF σ JT) (f : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ) : Om p (L f) = L (Om p f) := by
  have H := isHeis_opFF hσ hS hT hξ hc hR.hw
  have : Om p ∘ₗ L = L ∘ₗ Om p := by
    refine LinearMap.ext_on hR.span ?_
    rintro _ ⟨x, e, he, rfl⟩
    have he' : Fixes (opFF hc w) (latF F E nS nT Λ) (L e) := fun a ha => by rw [← hL, he a ha]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hL, hR.op, hR.op, hL, hR.vac p e he, hR.vac p _ he',
      GlobalTheory.FinWeilO.normOp_comm H lam (hR.sd' p) (hR.fin p) L hL he]
  exact LinearMap.congr_fun this f

theorem heis_fin (hS : IsHermND σ JS) (hR : IsLatRepF σ JS JT ξ₀ ψ hc Λ w lam Om)
    (p : GAF σ JS × GAF σ JT) (x : XFF F E nS nT) (f f' : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ)
    (hf : (f' : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ ψ x f) :
    (Om p f' : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ ψ (actOF σ JS JT p.1 p.2 x) (Om p f) := by
  have h1 : opFF hc w x f = phaseF σ JS JT ξ₀ ψ w x • f' := Subtype.ext (by rw [coe_opFF, Submodule.coe_smul, hf])
  have h2 := congrArg Subtype.val (hR.op p x f)
  rw [h1, map_smul, Submodule.coe_smul, coe_opFF, phaseF_rhoFF hS, coe_rhoFF] at h2
  exact smul_right_injective _ (phaseF_ne_zero w x) h2

end GlobalTheory.FinLatHeis


open GlobalTheory.FinLatF GlobalTheory.FinLatHeis in
theorem GlobalTheory.FinLatHeis.isLatRepF_heis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
        (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        GlobalTheory.FinLatF.IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om →
        ∀ g ∈ GlobalTheory.WeilPartsF.GfCF σ JS, ∀ h ∈ GlobalTheory.WeilPartsF.GfCF σ JT, ∀ (w₀ : WOF F E nS nT)
          (f f' : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ),
          (f' : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ B.ψ w₀ f →
          (Om (g, h) f' : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ B.ψ (actOF σ JS JT g h w₀) (Om (g, h) f) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ _ hξ hc Λ w lam Om hR g hg h hh w₀ f f' hf
  have hσ : ∀ x, σ (σ x) = x := by
    intro x
    let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
    apply τ.injective
    rw [hB.cm.2.2.2 τ, hB.cm.2.2.2 τ, star_star]
  set r := realIdF F E
  let L : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ →ₗ[ℂ] GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ :=
    (heisLF σ JS JT ξ₀ B.ψ (r • w₀)).restrict fun f hf => hc _ f hf
  have hL : ∀ m, (L m : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ B.ψ (r • w₀) m := fun _ => rfl
  have hLop : ∀ x v, L (opFF hc w x v) = opFF hc w x (L v) := fun x v => Subtype.ext (by
    rw [hL, coe_opFF, coe_opFF, hL, GlobalTheory.WeilPartsF.heisOF_smul, heisOF_heisOF', heisOF_heisOF',
      symplOHF_real_fin hσ ξ₀ w₀ x.fin, symplOHF_fin_real hσ hS hT hξ w₀ x.fin, add_comm])
  let f₁ : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ := ⟨_, hc ((1 - r) • w₀) f f.2⟩
  have hf' : f' = L f₁ := Subtype.ext (by
    rw [hf, hL]
    show heisOF σ JS JT ξ₀ B.ψ w₀ f = heisOF σ JS JT ξ₀ B.ψ (r • w₀) (heisOF σ JS JT ξ₀ B.ψ ((1 - r) • w₀) f)
    rw [heisOF_heisOF', symplOHF_real_fin hσ ξ₀ w₀ (fin_part w₀), AddChar.map_zero_eq_one, one_smul, ← decomp])
  have h1 := heis_fin hS hR (g, h) (XFF.mk _ (fin_part w₀)) f f₁ rfl
  rw [XFF.coe_mk] at h1
  rw [hf', comm hσ hS hT hξ hR L hLop, hL, h1, heisOF_heisOF',
    symplOHF_real_fin hσ ξ₀ w₀ (actOF_mem_finSubF g h (fin_part w₀)), AddChar.map_zero_eq_one, one_smul]
  congr 1
  conv_rhs => rw [decomp w₀, actOF_add, actOF_real hg hh]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerRepNormalizesHeisenbergFiniteStatement
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeIntertwinerRep_normalizes_heisenberg_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
        (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        GlobalTheory.FinLatF.IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om →
        ∀ g ∈ GlobalTheory.WeilPartsF.GfCF σ JS, ∀ h ∈ GlobalTheory.WeilPartsF.GfCF σ JT, ∀ (w₀ : WOF F E nS nT)
          (f f' : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ),
          (f' : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ B.ψ w₀ f →
          (Om (g, h) f' : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ B.ψ (actOF σ JS JT g h w₀) (Om (g, h) f) := by
  first | exact @GlobalTheory.FinLatHeis.isLatRepF_heis | exact GlobalTheory.FinLatHeis.isLatRepF_heis | (intros; apply GlobalTheory.FinLatHeis.isLatRepF_heis <;> assumption)
end
end
