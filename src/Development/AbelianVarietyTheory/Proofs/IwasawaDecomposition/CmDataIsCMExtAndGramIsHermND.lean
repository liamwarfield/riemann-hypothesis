module

public import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.SchurOrthogonalityIndefiniteUnitaryGroup
public import Formalism.SharpRestriction.Divisibility.WeightFamilies
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.TotallyPositiveExponents
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IotaOQContinuousInjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfCharInfCharOfCommute

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmDataIsCMExtAndGramIsHermND
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

theorem hspace_gram_det_ne_zero {E : Type} [Field E] [NumberField E] [StarRing E] (W : HSpace E) :
    W.gram.det ≠ 0 := by
  classical
  intro h0
  obtain ⟨v, hv, hmul⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have hb : ∀ i, W.hT (W.frame i) (∑ j, v j • W.frame j) = 0 := by
    intro i
    have := congrFun hmul i
    simp only [Matrix.mulVec, dotProduct, HSpace.gram, Pi.zero_apply] at this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  have hz : (∑ j, v j • W.frame j) = 0 := by
    refine W.nondeg.2 _ fun x => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← W.frame.sum_repr x, map_sum W.hT, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hb, smul_zero]
  apply hv
  funext j
  exact Fintype.linearIndependent_iff.mp W.frame.linearIndependent v hz j

theorem cmData_isCMExt_and_gram_isHermND : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E), IsCMExt F E cm.sig ∧ ∀ W : HSpace E, IsHermND cm.sig W.gram := by
  intro F E _ _ _ _ _ _ cm
  refine ⟨⟨cm.totReal, cm.cmUnram.1, cm.deg2, fun τ x => cm.cmUnram.2.1 τ x⟩, fun W => ⟨fun i j => ?_, hspace_gram_det_ne_zero W⟩⟩
  exact W.herm.eq (W.frame j) (W.frame i)

end GlobalTheory.Mem.Vol
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicSplit
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open Formalism.MainNotions.S hiding Af
open scoped TensorProduct

namespace GlobalTheory.Mem.VolSplit

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {r : ℕ}

theorem map_sigR {A B : Type} [CommRing A] [Algebra F A] [CommRing B] [Algebra F B] (p : A →ₐ[F] B) (z : A ⊗[F] E) :
    (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom (sigR A σ z) =
      sigR B σ ((Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [sigR]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem map_JR {A B : Type} [CommRing A] [Algebra F A] [CommRing B] [Algebra F B] (p : A →ₐ[F] B)
    (J : Matrix (Fin r) (Fin r) E) :
    (JR A J).map (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom = JR B J := by
  ext i j; simp [JR, inclR]

theorem map_unit {A B : Type} [CommRing A] [Algebra F A] [CommRing B] [Algebra F B] (p : A →ₐ[F] B)
    (J : Matrix (Fin r) (Fin r) E) (g : Matrix (Fin r) (Fin r) (A ⊗[F] E)) :
    (Formalism.UG.cT (sigR A σ) g * JR A J * g).map (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom =
      Formalism.UG.cT (sigR B σ) (g.map (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom) * JR B J *
        g.map (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom := by
  rw [Matrix.map_mul, Matrix.map_mul, map_JR]
  congr 2
  ext i j
  exact map_sigR σ p _

end Gen

theorem exists_adelic_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E), ∃ e : HA (AF F) σ J ≃ₜ* HA (Ainf F) σ J × HA (Af F) σ J, ∀ h, ((HA.mat (Af F) σ J (e h).2 : GL (Fin M) (Af F ⊗[F] E)) : Matrix (Fin M) (Fin M) (Af F ⊗[F] E)) = finMat σ J h ∧ ((HA.mat (Ainf F) σ J (e h).1 : GL (Fin M) (Ainf F ⊗[F] E)) : Matrix (Fin M) (Fin M) (Ainf F ⊗[F] E)) = ((HA.mat (AF F) σ J h : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) := by
  intro F E _ _ _ _ _ σ r J
  let pInf : AF F ⊗[F] E →+* Ainf F ⊗[F] E := (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom
  let pFin : AF F ⊗[F] E →+* Af F ⊗[F] E := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom
  obtain ⟨e, he, hc, hc'⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  have ext : ∀ {M N : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)}, M.map pInf = N.map pInf → M.map pFin = N.map pFin →
      M = N := fun {M N} h1 h2 => by
    ext i j
    refine e.injective (Prod.ext ?_ ?_)
    · rw [(he _).1, (he _).1]; exact congrFun (congrFun h1 i) j
    · rw [(he _).2, (he _).2]; exact congrFun (congrFun h2 i) j
  let gl : Matrix (Fin r) (Fin r) (Ainf F ⊗[F] E) → Matrix (Fin r) (Fin r) (Af F ⊗[F] E) →
      Matrix (Fin r) (Fin r) (AF F ⊗[F] E) := fun M N => Matrix.of fun i j => e.symm (M i j, N i j)
  have g1 : ∀ M N, (gl M N).map pInf = M := fun M N => by
    ext i j
    exact ((he _).1.symm.trans (congrArg Prod.fst (e.apply_symm_apply _)))
  have g2 : ∀ M N, (gl M N).map pFin = N := fun M N => by
    ext i j
    exact ((he _).2.symm.trans (congrArg Prod.snd (e.apply_symm_apply _)))
  let χ : HA (AF F) σ J →* HA (Ainf F) σ J × HA (Af F) σ J :=
    { toFun := fun h => ((⟨Formalism.UG.bc pInf (HA.mat _ _ _ h), (by
          have := congrArg (fun M => M.map pInf) (show Formalism.UG.cT _ _ * _ * _ = _ from h.2)
          rw [map_unit σ (fstA F), map_JR (fstA F)] at this
          exact this)⟩ : HR (Ainf F) σ J),
        (⟨Formalism.UG.bc pFin (HA.mat _ _ _ h), (by
          have := congrArg (fun M => M.map pFin) (show Formalism.UG.cT _ _ * _ * _ = _ from h.2)
          rw [map_unit σ (sndA F), map_JR (sndA F)] at this
          exact this)⟩ : HR (Af F) σ J))
      map_one' := Prod.ext (Subtype.ext (map_one (Formalism.UG.bc pInf))) (Subtype.ext (map_one (Formalism.UG.bc pFin)))
      map_mul' := fun a b => Prod.ext (Subtype.ext (map_mul (Formalism.UG.bc pInf) _ _))
        (Subtype.ext (map_mul (Formalism.UG.bc pFin) _ _)) }
  let ω : HA (Ainf F) σ J × HA (Af F) σ J → HA (AF F) σ J := fun g =>
    (⟨⟨gl g.1.1.val g.2.1.val, gl g.1.1.inv g.2.1.inv,
      ext (by rw [Matrix.map_mul, g1, g1, g.1.1.val_inv]; simp) (by rw [Matrix.map_mul, g2, g2, g.2.1.val_inv]; simp),
      ext (by rw [Matrix.map_mul, g1, g1, g.1.1.inv_val]; simp) (by rw [Matrix.map_mul, g2, g2, g.2.1.inv_val]; simp)⟩,
      ext ((map_unit σ (fstA F) J _).trans (Eq.trans (by
        rw [g1]
        exact g.1.2) (map_JR (fstA F) J).symm)) ((map_unit σ (sndA F) J _).trans (Eq.trans (by
        rw [g2]
        exact g.2.2) (map_JR (sndA F) J).symm))⟩ : HR (AF F) σ J)
  have l1 : Function.LeftInverse ω χ := fun h => Subtype.ext (Units.ext (ext (g1 _ _) (g2 _ _)))
  have l2 : Function.RightInverse ω χ := fun g =>
    Prod.ext (Subtype.ext (Units.ext (g1 _ _))) (Subtype.ext (Units.ext (g2 _ _)))
  let ψ : HA (AF F) σ J ≃* HA (Ainf F) σ J × HA (Af F) σ J :=
    { χ with invFun := ω, left_inv := l1, right_inv := l2 }
  have hp1 : Continuous pInf := (continuous_fst.comp hc).congr fun z => (he z).1
  have hp2 : Continuous pFin := (continuous_snd.comp hc).congr fun z => (he z).2
  have hv : Continuous fun h : HA (AF F) σ J => HA.mat _ _ _ h := continuous_subtype_val
  have c1 : Continuous ψ := by
    refine Continuous.prodMk (Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _)
      (Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _)
    · exact (Units.continuous_val.comp hv).matrix_map hp1
    · exact (Units.continuous_coe_inv.comp hv).matrix_map hp1
    · exact (Units.continuous_val.comp hv).matrix_map hp2
    · exact (Units.continuous_coe_inv.comp hv).matrix_map hp2
  have c2 : Continuous ψ.symm := by
    refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
    · refine continuous_matrix fun i j => hc'.comp (Continuous.prodMk ?_ ?_)
      · exact (Units.continuous_val.comp (continuous_subtype_val.comp continuous_fst)).matrix_elem i j
      · exact (Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd)).matrix_elem i j
    · refine continuous_matrix fun i j => hc'.comp (Continuous.prodMk ?_ ?_)
      · exact (Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_fst)).matrix_elem i j
      · exact (Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_snd)).matrix_elem i j
  exact ⟨{ ψ with continuous_toFun := c1, continuous_invFun := c2 }, fun h => ⟨rfl, rfl⟩⟩

end GlobalTheory.Mem.VolSplit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFdegSmulOfIsDS
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

theorem exists_isFdeg_smul_of_isDS : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ → ∀ c : NNReal, 0 < c → ∃ d : ℝ, IsFdeg ((c : ENNReal) • Formalism.REAL.muG ε) σ d := by
  intro n ε lam H _ _ σ h c hc
  obtain ⟨h1, h2, hU, hirr, hsq, -⟩ := h
  obtain ⟨d, hd, hI⟩ := GlobalTheory.schur_orthogonality_unitary n ε H σ hU hirr hsq
  have hc' : (0 : ℝ) < (c : ℝ) := hc
  refine ⟨d / c, div_pos hd hc', fun v w v' w' => ⟨(hI v w v' w').1.smul_measure ENNReal.coe_ne_top, ?_⟩⟩
  rw [integral_smul_measure, (hI v w v' w').2, ENNReal.coe_toReal, Complex.real_smul,
    Complex.ofReal_div, div_div_eq_mul_div]
  ring

end GlobalTheory.Mem.Vol
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueInfEmb
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.VolEmb

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem infEmb_exists (τ : E →+* ℂ) (w : InfinitePlace F) (hw : w.embedding = τ.comp (algebraMap F E)) :
    ∃ θ : Ainf F ⊗[F] E →+* ℂ, IsInfEmb τ θ := by
  let _ : Algebra F ℂ := (τ.comp (algebraMap F E)).toAlgebra
  let f : Ainf F →ₐ[F] ℂ :=
    { toRingHom := (InfinitePlace.Completion.extensionEmbedding w).comp (Pi.evalRingHom _ w)
      commutes' := fun x => by
        change InfinitePlace.Completion.extensionEmbedding w ((algebraMap F (Ainf F) x) w) = _
        rw [InfiniteAdeleRing.algebraMap_apply, InfinitePlace.Completion.extensionEmbedding_coe]
        exact DFunLike.congr_fun hw x }
  let g : E →ₐ[F] ℂ := { toRingHom := τ, commutes' := fun _ => rfl }
  refine ⟨(Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom, fun x => ?_, ?_⟩
  · show f 1 * g x = τ x
    rw [map_one, one_mul]
    rfl
  · have : (fun a : Ainf F => (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom
        (a ⊗ₜ[F] (1 : E))) = fun a => InfinitePlace.Completion.extensionEmbedding w (a w) := by
      funext a
      show f a * g 1 = _
      rw [map_one, mul_one]
      rfl
    rw [this]
    exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)

theorem infEmb_unique (τ : E →+* ℂ) (θ θ' : Ainf F ⊗[F] E →+* ℂ) (h : IsInfEmb τ θ)
    (h' : IsInfEmb τ θ') : θ = θ' :=
  by apply _root_.UpperTheory.Reformulated.B.Qh26.isInfEmb_unique <;> assumption

theorem existsUnique_infEmb : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ τ : E →+* ℂ, ∃! θ : Ainf F ⊗[F] E →+* ℂ, IsInfEmb τ θ := by
  intro F E _ _ _ _ _ σ h τ
  have := h.1
  have hr : (InfinitePlace.mk (τ.comp (algebraMap F E))).IsReal := IsTotallyReal.isReal _
  have hw : (InfinitePlace.mk (τ.comp (algebraMap F E))).embedding = τ.comp (algebraMap F E) :=
    InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 hr)
  obtain ⟨θ, hθ⟩ := infEmb_exists τ _ hw
  exact ⟨θ, hθ, fun θ' h' => infEmb_unique τ θ' θ h' hθ⟩

end GlobalTheory.Mem.VolEmb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCMFamHost
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.HermPartIsHermitian
noncomputable section

namespace GlobalTheory.CuspAlgComparison

open Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions NumberField GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.TotallyPositiveExponents
open Matrix hiding vec
open scoped ComplexOrder

section Host

variable {R : Ranks} (H : Host R)

theorem tau_injective : Function.Injective (tau H) := fun _ _ h =>
  Subtype.ext ((factEmb R H).1.1 h)

theorem tau_sqrt (τ : Pl R) : tau H τ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) :=
  ((factEmb R H).2 _).2 τ.2

theorem sqrt_d_pos : 0 < Real.sqrt H.d := Real.sqrt_pos.2 (by exact_mod_cast H.hyp.2.1.pos)

theorem emb_cases (σ : H.E →+* ℂ) :
    ∃ τ : Pl R, σ = tau H τ ∨ σ = (starRingEnd ℂ).comp (tau H τ) := by
  obtain ⟨g, rfl⟩ := (factEmb R H).1.2 σ
  by_cases hg : g ∈ R.Psi
  · exact ⟨⟨g, hg⟩, Or.inl rfl⟩
  · rw [Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem, not_not] at hg
    refine ⟨⟨_, hg⟩, Or.inr (RingHom.ext fun x => ?_)⟩
    change H.emb g x = starRingEnd ℂ (H.emb (g * R.cc) x)
    rw [Formalism.L2.Geo.emb_mul_cc_comp]
    change _ = starRingEnd ℂ (H.emb g (H.conj x))
    rw [show H.emb g (H.conj x) = _ from H.conjE_apply _ x]
    simp

theorem tau_ne_conj (τ τ' : Pl R) : tau H τ ≠ (starRingEnd ℂ).comp (tau H τ') := by
  intro h
  have h1 := congrArg Complex.im (DFunLike.congr_fun h H.sqrtMinusD)
  rw [RingHom.comp_apply, tau_sqrt, tau_sqrt] at h1
  have := sqrt_d_pos H
  simp at h1
  linarith

end Host

section Forms

variable {R : Ranks} {H : Host R} {n : ℕ}


end Forms

end GlobalTheory.CuspAlgComparison

end
end

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

theorem isCMFam_host (R : Ranks) (H : Host R) (I : Type) (e : I ≃ R.Psi) :
    IsCMFam (fun i => H.emb (e i).1) := by
  refine ⟨fun i j h => ?_, fun w => ?_⟩
  · rcases NumberField.InfinitePlace.mk_eq_iff.1 h with h1 | h1
    · exact e.injective (GlobalTheory.CuspAlgComparison.tau_injective H h1)
    · exact absurd h1.symm (GlobalTheory.CuspAlgComparison.tau_ne_conj H (e j) (e i))
  · obtain ⟨τ, h | h⟩ := GlobalTheory.CuspAlgComparison.emb_cases H w.embedding
    · refine ⟨e.symm τ, ?_⟩
      rw [← NumberField.InfinitePlace.mk_embedding w, h]
      simp only [Equiv.apply_symm_apply]
      rfl
    · refine ⟨e.symm τ, ?_⟩
      rw [← NumberField.InfinitePlace.mk_embedding w, h]
      simp only [Equiv.apply_symm_apply]
      exact (NumberField.InfinitePlace.mk_conjugate_eq _).symm

end GlobalTheory.Mem.Vol
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowHCParameterIsHCParamAndFormalDegreePos
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowHCParameterIsHCParamAndFormalDegreePos
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

theorem lamS_succ_lt (R : Ranks) (P : HCParam R) (i j : Fin R.r) (hij : j.val = i.val + 1) :
    lamS R P j < lamS R P i := by
  have hk : R.m + 3 ≤ R.k := R.m_add_three_le_k
  have hm : 2 ≤ R.m := R.two_le_m
  have hjr : j.val < R.k + R.m - 1 := j.isLt
  have hu : ∀ a b : Fin R.k, a.val = b.val → P.u a = P.u b := fun a b h => by rw [Fin.ext h]
  have hb : ∀ a b : Fin R.m, a.val = b.val → P.b a = P.b b := fun a b h => by rw [Fin.ext h]
  unfold Formalism.MainNotions.S.lamS
  by_cases hj : j.val < R.k - 1
  · have hi : i.val < R.k - 1 := by omega
    rw [dite_eq_left hj, dite_eq_left hi]
    have key : P.v ⟨j.val, hj⟩ < P.v ⟨i.val, hi⟩ :=
      calc P.v ⟨j.val, hj⟩ < P.u ⟨j.val, by omega⟩ := P.u_gt_v ⟨j.val, hj⟩
        _ = P.u ⟨i.val + 1, by omega⟩ := hu _ _ (by simp [hij])
        _ < P.v ⟨i.val, hi⟩ := P.v_gt_u ⟨i.val, hi⟩
    exact_mod_cast key
  · by_cases hi : i.val < R.k - 1
    · have hj0 : j.val - (R.k - 1) < R.m := by omega
      rw [dite_eq_right hj, dite_eq_left hj0, dite_eq_left hi]
      have key : -P.b ⟨j.val - (R.k - 1), hj0⟩ < P.v ⟨i.val, hi⟩ :=
        calc -P.b ⟨j.val - (R.k - 1), hj0⟩ = -P.b ⟨0, by omega⟩ :=
            congrArg (fun x => -x) (hb _ _ (show j.val - (R.k - 1) = 0 by omega))
          _ < P.u ⟨R.k - 1, by omega⟩ := P.u_last_gt (by omega) (by omega)
          _ = P.u ⟨i.val + 1, by omega⟩ := hu _ _ (by simp; omega)
          _ < P.v ⟨i.val, hi⟩ := P.v_gt_u ⟨i.val, hi⟩
      have := (Rat.cast_lt (K := ℝ)).mpr key
      push_cast at this
      exact this
    · have hj0 : j.val - (R.k - 1) < R.m := by omega
      have hi0 : i.val - (R.k - 1) < R.m := by omega
      have hi1 : i.val - (R.k - 1) + 1 < R.m := by omega
      rw [dite_eq_right hj, dite_eq_left hj0, dite_eq_right hi, dite_eq_left hi0]
      have h1 := P.gap_be ⟨i.val - (R.k - 1), hi0⟩
      have h2 := P.gap_eb ⟨i.val - (R.k - 1), hi0⟩ hi1
      have h3 : P.b ⟨i.val - (R.k - 1) + 1, hi1⟩ = P.b ⟨j.val - (R.k - 1), hj0⟩ := hb _ _ (by simp; omega)
      have ht : (0 : ℚ) ≤ R.t := Nat.cast_nonneg _
      have key : P.b ⟨i.val - (R.k - 1), hi0⟩ < P.b ⟨j.val - (R.k - 1), hj0⟩ := by
        rw [← h3]; linarith
      have := (Rat.cast_lt (K := ℝ)).mpr key
      linarith

theorem lamS_int (R : Ranks) (P : HCParam R) (i : Fin R.r) : ∃ z : ℤ, lamS R P i = (z : ℝ) := by
  unfold Formalism.MainNotions.S.lamS
  split_ifs with h h'
  · obtain ⟨z, hz⟩ := P.v_int ⟨i.val, h⟩
    exact ⟨z, by rw [hz, Rat.cast_intCast]⟩
  · obtain ⟨z, hz⟩ := P.b_int ⟨i.val - (R.k - 1), h'⟩
    exact ⟨-z, by rw [hz, Rat.cast_intCast]; push_cast; ring⟩
  · exact ⟨0, by simp⟩

theorem lamSH_isHCParam (R : Ranks) (P : HCParam R) : Formalism.QuantumDeterminants.IsHCParam (lamSH R P) := by
  refine ⟨?_, ?_⟩
  · rw [Fin.strictAnti_iff_succ_lt]
    intro i
    exact lamS_succ_lt R P (Fin.cast (Formalism.MainNotions.S.dimS_eq R) (Fin.castSucc i))
      (Fin.cast (Formalism.MainNotions.S.dimS_eq R) i.succ) (by simp)
  · intro a
    obtain ⟨z, hz⟩ := lamS_int R P (Fin.cast (Formalism.MainNotions.S.dimS_eq R) a)
    obtain ⟨w, hw⟩ := R.k_even
    have hk : (R.k : ℝ) = 2 * w := by rw [hw]; push_cast; ring
    refine ⟨z - R.rS - w, ?_⟩
    show lamS R P (Fin.cast (Formalism.MainNotions.S.dimS_eq R) a) - _ = _
    rw [hz]
    push_cast
    rw [hk]
    ring

theorem fdegHC_pos_of_injective {n : ℕ} (lam : Fin n → ℝ) (hlam : Function.Injective lam) :
    0 < Formalism.QuantumDeterminants.fdegHC lam := by
  unfold Formalism.QuantumDeterminants.fdegHC
  apply div_pos
  · apply Finset.prod_pos
    intro a _
    apply Finset.prod_pos
    intro b hb
    rw [Finset.mem_filter] at hb
    exact abs_pos.mpr (sub_ne_zero.mpr fun h => hb.2.ne (hlam h))
  · apply Finset.prod_pos
    intro a _
    apply Finset.prod_pos
    intro b hb
    rw [Finset.mem_filter] at hb
    have h1 : (a : ℕ) < b := hb.2
    have h2 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast h1
    linarith

theorem lamSH_isHCParam_and_trueDsig_pos :
    ∀ (R : Ranks) (P : HCParam R), Formalism.QuantumDeterminants.IsHCParam (lamSH R P) ∧ 0 < trueDsig R P := by
  intro R P
  refine ⟨lamSH_isHCParam R P, ?_⟩
  exact fdegHC_pos_of_injective _ (lamSH_isHCParam R P).1.injective

end GlobalTheory.Mem.Vol
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowHCParameterIsHCParamAndFormalDegreePosStatement
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowHCParameter_isHCParam_and_formalDegree_pos : ∀ (R : Ranks) (P : HCParam R), Formalism.QuantumDeterminants.IsHCParam (lamSH R P) ∧ 0 < trueDsig R P := by
  first | exact @GlobalTheory.Mem.Vol.lamSH_isHCParam_and_trueDsig_pos | exact GlobalTheory.Mem.Vol.lamSH_isHCParam_and_trueDsig_pos | (intros; apply GlobalTheory.Mem.Vol.lamSH_isHCParam_and_trueDsig_pos <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ImportsRest
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.SignatureFactor

theorem Jpq_mul_self (p q : ℕ) : Formalism.UG.Jpq p q * Formalism.UG.Jpq p q = 1 := by
  simp [Formalism.UG.Jpq, Matrix.fromBlocks_multiply]

theorem exists_factor : ∀ (M p q : ℕ) (G : Matrix (Fin M) (Fin M) ℂ), Formalism.UG.HasSignature G p q → p + q = M ∧ (∃ A : Matrix (Fin p ⊕ Fin q) (Fin M) ℂ, Aᴴ * Formalism.UG.Jpq p q * A = G) ∧ ∀ A : Matrix (Fin p ⊕ Fin q) (Fin M) ℂ, Aᴴ * Formalism.UG.Jpq p q * A = G → ∃ B : Matrix (Fin M) (Fin p ⊕ Fin q) ℂ, A * B = 1 ∧ B * A = 1 := by
  intro M p q G h
  obtain ⟨e, P, hP⟩ := h
  have hP' : P.valᴴ * (reindex e e G) * P.val = Formalism.UG.Jpq p q := hP
  set Q : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := Units.val (P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) with hQ
  have hPQ : P.val * Q = 1 := by
    rw [hQ, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hG' : Qᴴ * Formalism.UG.Jpq p q * Q = reindex e e G := by
    rw [← hP']
    calc Qᴴ * (P.valᴴ * (reindex e e G) * P.val) * Q
        = (P.val * Q)ᴴ * (reindex e e G) * (P.val * Q) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hPQ]; simp
  have hdet : G.det ≠ 0 := by
    intro h0
    have h1 : (Formalism.UG.Jpq p q).det = 0 := by
      rw [← hP', Matrix.det_mul, Matrix.det_mul, Matrix.det_reindex_self, h0]; simp
    have h2 := congrArg Matrix.det (Jpq_mul_self p q)
    rw [Matrix.det_mul, h1] at h2
    simp at h2
  refine ⟨?_, ⟨Q.submatrix id e, ?_⟩, ?_⟩
  · simpa using (Fintype.card_congr e).symm
  · ext i j
    have := congrFun (congrFun hG' (e i)) (e j)
    simpa [Matrix.mul_apply] using this
  · intro A hA
    have hBA : (G⁻¹ * (Aᴴ * Formalism.UG.Jpq p q)) * A = 1 := by
      rw [Matrix.mul_assoc, hA]
      exact Matrix.nonsing_inv_mul G (isUnit_iff_ne_zero.mpr hdet)
    exact ⟨_, (Matrix.mul_eq_one_comm_of_equiv e).mp hBA, hBA⟩

end GlobalTheory.Mem.SignatureFactor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAlgOfFinite
noncomputable section

namespace GlobalTheory.Mem.Col2.JetEx

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker

def FinAlg (T : Set ℂ) : Prop :=
  ∃ Z : Finset ℂ, (∀ z ∈ Z, IsAlgebraic ℚ z) ∧ T ⊆ (Subfield.closure (Z : Set ℂ) : Set ℂ)

theorem FinAlg.mono {T T' : Set ℂ} (h : FinAlg T') (hT : T ⊆ T') : FinAlg T := by
  obtain ⟨Z, hZ, hsub⟩ := h
  exact ⟨Z, hZ, hT.trans hsub⟩

theorem finAlg_of_finite {T : Set ℂ} (h : T.Finite) (ha : ∀ z ∈ T, IsAlgebraic ℚ z) : FinAlg T := by
  refine ⟨h.toFinset, fun z hz => ha z (h.mem_toFinset.mp hz), ?_⟩
  rw [h.coe_toFinset]
  exact Subfield.subset_closure

theorem finAlg_biUnion {κ : Type} {s : Set κ} (hs : s.Finite) {T : κ → Set ℂ} (h : ∀ k ∈ s, FinAlg (T k)) :
    FinAlg (⋃ k ∈ s, T k) := by
  classical
  choose! Z hZ hsub using h
  refine ⟨hs.toFinset.biUnion Z, ?_, ?_⟩
  · intro z hz
    obtain ⟨k, hk, hzk⟩ := Finset.mem_biUnion.mp hz
    exact hZ k (hs.mem_toFinset.mp hk) z hzk
  · refine Set.iUnion₂_subset fun k hk => (hsub k hk).trans (Subfield.closure_mono ?_)
    intro z hz
    exact Finset.mem_biUnion.mpr ⟨k, hs.mem_toFinset.mpr hk, hz⟩

theorem FinAlg.union {T T' : Set ℂ} (h : FinAlg T) (h' : FinAlg T') : FinAlg (T ∪ T') := by
  classical
  obtain ⟨Z, hZ, hsub⟩ := h
  obtain ⟨Z', hZ', hsub'⟩ := h'
  refine ⟨Z ∪ Z', fun z hz => ?_, Set.union_subset ?_ ?_⟩
  · rcases Finset.mem_union.mp hz with hz | hz
    · exact hZ z hz
    · exact hZ' z hz
  · exact hsub.trans (Subfield.closure_mono (by simp))
  · exact hsub'.trans (Subfield.closure_mono (by simp))

theorem FinAlg.closure {T : Set ℂ} (h : FinAlg T) : FinAlg (Subfield.closure T : Set ℂ) := by
  obtain ⟨Z, hZ, hsub⟩ := h
  exact ⟨Z, hZ, SetLike.coe_subset_coe.mpr (Subfield.closure_le.mpr hsub)⟩

variable {X : Fields} (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (M : ℕ)

def jetSet (n : ℕ) : Set ℂ :=
  {z | ∃ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x : HomE X.E a b)
    (e : DVar X.Tau a b →₀ ℕ), InRange S M c N N' x ∧ e.degree = n ∧
      z = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd S N N' c x) e}

def JetAlg : Prop :=
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x : HomE X.E a b),
    InRange S M c N N' x → ∀ e : DVar X.Tau a b →₀ ℕ,
      IsAlgebraic ℚ ((A.chiF a b N N')⁻¹ * derivAt0 (A.thInd S N N' c x) e)

def VacEq : Prop :=
  ∀ (γ : UF X.E a) (γ' : UF X.E b) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)),
    IsSdLat N → IsSdLat N' → ∀ z, A.e a b (gmap γ.1 N) (gmap γ'.1 N') z = A.e a b N N' (A.pullV a b γ.1 γ'.1 z)

end GlobalTheory.Mem.Col2.JetEx

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrredOfCharpolyEq
open Formalism.MainNotions.N

noncomputable section

namespace GlobalTheory.BrauerNesbittIrr

open Matrix

variable {k Γ : Type} [Field k] [Group Γ] {a : ℕ}

abbrev matHom (ρ : Γ →* GL (Fin a) k) : Γ →* Matrix (Fin a) (Fin a) k := (Units.coeHom _).comp ρ

abbrev liftRep (ρ : Γ →* GL (Fin a) k) : MonoidAlgebra k Γ →ₐ[k] Matrix (Fin a) (Fin a) k :=
  MonoidAlgebra.lift k (Matrix (Fin a) (Fin a) k) Γ (matHom ρ)

theorem liftRep_mem (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k))
    (hW : ∀ g, ∀ x ∈ W, (ρ g : Matrix (Fin a) (Fin a) k) *ᵥ x ∈ W) (α : MonoidAlgebra k Γ) :
    ∀ x ∈ W, liftRep ρ α *ᵥ x ∈ W := by
  induction α using MonoidAlgebra.induction_linear with
  | zero => intro x _; simp [W.zero_mem]
  | add p q hp hq => intro x hx; rw [map_add (f := _), add_mulVec]; exact W.add_mem (hp x hx) (hq x hx)
  | single g c =>
    intro x hx
    rw [MonoidAlgebra.lift_single, Matrix.smul_mulVec]
    exact W.smul_mem c (hW g x hx)

theorem liftRep_surjective [IsAlgClosed k] (ρ : Γ →* GL (Fin a) k) (ha : 0 < a)
    (h : ∀ W : Submodule k (Fin a → k), (∀ g, ∀ x ∈ W, (ρ g : Matrix (Fin a) (Fin a) k) *ᵥ x ∈ W) →
      W = ⊥ ∨ W = ⊤) :
    Function.Surjective (liftRep ρ) := by
  haveI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
  have hirr : IsIrrSub ρ ⊤ := ⟨top_ne_bot, fun g v _ => Submodule.mem_top,
    fun W' _ hinv => h W' hinv⟩
  have hs := GlobalTheory.BurnsideField.span_mat_eq_top_of_isIrrSub ρ hirr
  intro X
  have hle : Submodule.span k (Set.range (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat ρ)) ≤
      LinearMap.range (liftRep ρ).toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact ⟨MonoidAlgebra.single g 1, by simp⟩
  obtain ⟨α, hα⟩ := hle (hs ▸ Submodule.mem_top : X ∈ _)
  exact ⟨α, hα⟩

theorem irred_of_charpoly_eq [IsAlgClosed k] (ρ ρ' : Γ →* GL (Fin a) k)
    (hc : ∀ g, (ρ g : Matrix (Fin a) (Fin a) k).charpoly = (ρ' g : Matrix (Fin a) (Fin a) k).charpoly)
    (h' : ∀ W : Submodule k (Fin a → k), (∀ g, ∀ x ∈ W, (ρ' g : Matrix (Fin a) (Fin a) k) *ᵥ x ∈ W) →
      W = ⊥ ∨ W = ⊤)
    (W : Submodule k (Fin a → k)) (hW : ∀ g, ∀ x ∈ W, (ρ g : Matrix (Fin a) (Fin a) k) *ᵥ x ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  classical
  by_contra hne
  push_neg at hne
  obtain ⟨hb, ht⟩ := hne
  have hcp : ∀ α, (liftRep ρ α).charpoly = (liftRep ρ' α).charpoly :=
    GlobalTheory.charpoly_lift_eq_of_charpoly_eq a (matHom ρ) (matHom ρ') hc
  have hdet : ∀ α, (liftRep ρ α).det = (liftRep ρ' α).det := fun α => by
    rw [det_eq_sign_charpoly_coeff, det_eq_sign_charpoly_coeff, hcp]
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
  have ha : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · subst h; exact absurd (Subsingleton.elim w 0) hw0
    · exact h
  haveI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
  have hsurj := liftRep_surjective ρ' ha h'
  let S : Set (Matrix (Fin a) (Fin a) k) :=
    {X | ∃ α, (∀ x ∈ W, liftRep ρ α *ᵥ x = 0) ∧ liftRep ρ' α = X}
  let I : TwoSidedIdeal (Matrix (Fin a) (Fin a) k) := TwoSidedIdeal.mk' S
    ⟨0, fun x _ => by simp, by simp⟩
    (by
      rintro _ _ ⟨α, hα, rfl⟩ ⟨β, hβ, rfl⟩
      exact ⟨α + β, fun x hx => by rw [map_add (f := _), add_mulVec, hα x hx, hβ x hx, add_zero],
        map_add _ _ _⟩)
    (by
      rintro _ ⟨α, hα, rfl⟩
      exact ⟨-α, fun x hx => by rw [map_neg, neg_mulVec, hα x hx, neg_zero], map_neg _ _⟩)
    (by
      rintro X _ ⟨α, hα, rfl⟩
      obtain ⟨β, rfl⟩ := hsurj X
      exact ⟨β * α, fun x hx => by rw [map_mul, ← mulVec_mulVec, hα x hx, mulVec_zero],
        map_mul _ _ _⟩)
    (by
      rintro _ Y ⟨α, hα, rfl⟩
      obtain ⟨β, rfl⟩ := hsurj Y
      exact ⟨α * β, fun x hx => by
        rw [map_mul, ← mulVec_mulVec, hα _ (liftRep_mem ρ W hW β x hx)], map_mul _ _ _⟩)
  have hmem : ∀ X, X ∈ I ↔ X ∈ S := fun X => TwoSidedIdeal.mem_mk' _ _ _ _ _ _ X
  rcases IsSimpleOrder.eq_bot_or_eq_top I with hI | hI
  · have h0 : ∀ α, (∀ x ∈ W, liftRep ρ α *ᵥ x = 0) → liftRep ρ' α = 0 := fun α hα => by
      have : liftRep ρ' α ∈ I := (hmem _).2 ⟨α, hα, rfl⟩
      rw [hI] at this
      exact (TwoSidedIdeal.mem_bot _).1 this
    let ψ : MonoidAlgebra k Γ →ₗ[k] (Fin (Module.finrank k W) → Fin a → k) :=
      { toFun := fun α i => liftRep ρ α *ᵥ ((Module.finBasis k W i : W) : Fin a → k)
        map_add' := fun α β => by funext i; simp [add_mulVec]
        map_smul' := fun c α => by funext i; simp [Matrix.smul_mulVec] }
    have hker : LinearMap.ker ψ ≤ LinearMap.ker (liftRep ρ').toLinearMap := by
      intro α hα
      rw [LinearMap.mem_ker] at hα ⊢
      apply h0 α
      intro x hx
      have hf : (Matrix.toLin' (liftRep ρ α)).comp W.subtype = 0 :=
        (Module.finBasis k W).ext fun i => by
          have := congrFun hα i
          simpa [ψ] using this
      have := LinearMap.congr_fun hf ⟨x, hx⟩
      simpa using this
    have hrange : LinearMap.range (liftRep ρ').toLinearMap = ⊤ := LinearMap.range_eq_top.2 hsurj
    let q := (LinearMap.ker ψ).liftQ (liftRep ρ').toLinearMap hker
    have hq : LinearMap.range q = ⊤ := by rw [Submodule.range_liftQ, hrange]
    haveI : FiniteDimensional k (MonoidAlgebra k Γ ⧸ LinearMap.ker ψ) :=
      LinearEquiv.finiteDimensional (ψ.quotKerEquivRange).symm
    have h1 : Module.finrank k (Matrix (Fin a) (Fin a) k) ≤
        Module.finrank k (MonoidAlgebra k Γ ⧸ LinearMap.ker ψ) := by
      have := LinearMap.finrank_range_le q
      rwa [hq, finrank_top] at this
    have h2 : Module.finrank k (MonoidAlgebra k Γ ⧸ LinearMap.ker ψ) ≤
        Module.finrank k W * a := by
      rw [ψ.quotKerEquivRange.finrank_eq]
      refine (Submodule.finrank_le _).trans (le_of_eq ?_)
      first
        | simp [Module.finrank_pi_fintype, Module.finrank_fintype_fun_eq_card]
        | rw [Module.finrank_pi_fintype]; simp
        | simp [Module.finrank_pi]
    have h3 : Module.finrank k W < a := by
      have := Submodule.finrank_lt ht
      simpa using this
    rw [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one] at h1
    nlinarith
  · have h1 : (1 : Matrix (Fin a) (Fin a) k) ∈ I := by rw [hI]; exact TwoSidedIdeal.mem_top _
    obtain ⟨κ, hκ, hκ1⟩ := (hmem _).1 h1
    have h0 : (liftRep ρ κ).det = 0 := Matrix.exists_mulVec_eq_zero_iff.1 ⟨w, hw0, hκ w hw⟩
    rw [hdet, hκ1, det_one] at h0
    exact one_ne_zero h0

theorem litBNIrr (Γ : Type) [Group Γ] : LitBNIrr Γ := by
  intro ℓ _ a ρ ρ' hc h' W hW
  exact irred_of_charpoly_eq ρ ρ' hc (fun W hW => h' W fun g _ x hx => hW g x hx) W
    (fun g x hx => hW g (Subgroup.mem_top g) x hx)

end GlobalTheory.BrauerNesbittIrr

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumIndicatorLeZsumR
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An

theorem zsumR_eq_sum_toFinset {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t T : ℝ) (f : ℂ → ℝ)
    (h : (zerosIn χ t T).Finite) :
    zsumR χ t T f = ∑ ρ ∈ h.toFinset, (zmult χ ρ : ℝ) * f ρ := by
  unfold zsumR
  exact finsum_mem_eq_finite_toFinset_sum _ h


open Classical in
theorem sum_indicator_le_zsumR {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t T : ℝ) (S : Finset ℂ)
    (h : (zerosIn χ t T).Finite) :
    ∑ ρ ∈ S, (zmult χ ρ : ℝ) * (if ρ ∈ zerosIn χ t T then 1 else 0) ≤ zsumR χ t T (fun _ => 1) := by
  rw [zsumR_eq_sum_toFinset χ t T _ h]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    rw [Finset.mem_filter] at hx
    exact h.mem_toFinset.mpr hx.2
  · intro x _ _
    exact Nat.cast_nonneg _


open Classical in
theorem recip_le_sum_windows {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) (ρ : ℂ)
    (hρ : ρ ∈ zerosIn χ 0 T) :
    (if 1 < |ρ.im| then 1 / ‖ρ‖ else 0 : ℝ) ≤
      ∑ k ∈ Icc 1 ⌊T⌋₊, (k : ℝ)⁻¹ * ((if ρ ∈ zerosIn χ (k : ℝ) 1 then 1 else 0) +
        (if ρ ∈ zerosIn χ (-(k : ℝ)) 1 then 1 else 0)) := by
  have hnn : ∀ j : ℕ, (0 : ℝ) ≤ (j : ℝ)⁻¹ * ((if ρ ∈ zerosIn χ (j : ℝ) 1 then 1 else 0) +
      (if ρ ∈ zerosIn χ (-(j : ℝ)) 1 then 1 else 0)) := by
    intro j
    apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg j))
    apply add_nonneg <;> split_ifs <;> norm_num
  by_cases h1 : 1 < |ρ.im|
  · rw [if_pos h1]
    obtain ⟨hre0, hre1, hT, hL⟩ := hρ
    rw [sub_zero] at hT
    have hk1 : 1 ≤ ⌊|ρ.im|⌋₊ := Nat.le_floor (by rw [Nat.cast_one]; exact h1.le)
    have hkT : ⌊|ρ.im|⌋₊ ≤ ⌊T⌋₊ := Nat.floor_mono hT
    have hkle : (⌊|ρ.im|⌋₊ : ℝ) ≤ |ρ.im| := Nat.floor_le (abs_nonneg _)
    have hklt : |ρ.im| < ⌊|ρ.im|⌋₊ + 1 := Nat.lt_floor_add_one _
    have hkpos : (0 : ℝ) < ⌊|ρ.im|⌋₊ := by exact_mod_cast hk1
    have hind : (1 : ℝ) ≤ (if ρ ∈ zerosIn χ (⌊|ρ.im|⌋₊ : ℝ) 1 then 1 else 0) +
        (if ρ ∈ zerosIn χ (-(⌊|ρ.im|⌋₊ : ℝ)) 1 then 1 else 0) := by
      rcases le_or_gt 0 ρ.im with him | him
      · have hmem : ρ ∈ zerosIn χ (⌊|ρ.im|⌋₊ : ℝ) 1 := by
          refine ⟨hre0, hre1, ?_, hL⟩
          have hab : |ρ.im| = ρ.im := abs_of_nonneg him
          rw [abs_le]
          constructor <;> linarith
        rw [if_pos hmem]
        split_ifs <;> norm_num
      · have hmem : ρ ∈ zerosIn χ (-(⌊|ρ.im|⌋₊ : ℝ)) 1 := by
          refine ⟨hre0, hre1, ?_, hL⟩
          have hab : |ρ.im| = -ρ.im := abs_of_neg him
          rw [abs_le]
          constructor <;> linarith
        rw [if_pos hmem]
        split_ifs <;> norm_num
    calc 1 / ‖ρ‖ ≤ ((⌊|ρ.im|⌋₊ : ℕ) : ℝ)⁻¹ := by
          rw [one_div]
          exact inv_anti₀ hkpos (hkle.trans (Complex.abs_im_le_norm ρ))
      _ ≤ ((⌊|ρ.im|⌋₊ : ℕ) : ℝ)⁻¹ * ((if ρ ∈ zerosIn χ (⌊|ρ.im|⌋₊ : ℝ) 1 then 1 else 0) +
          (if ρ ∈ zerosIn χ (-(⌊|ρ.im|⌋₊ : ℝ)) 1 then 1 else 0)) :=
          le_mul_of_one_le_right (inv_nonneg.mpr hkpos.le) hind
      _ ≤ _ := Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_Icc.mpr ⟨hk1, hkT⟩)
  · rw [if_neg h1]
    exact Finset.sum_nonneg (fun j _ => hnn j)

theorem zsumR_recip_le : GlobalTheory.Mem.An.ZeroCount → ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ T : ℝ, 2 ≤ T → zsumR χ 0 T (fun ρ => if 1 < |ρ.im| then 1 / ‖ρ‖ else 0) ≤ C * Real.log (q * T) ^ 2 ∧ zsumR χ 0 1 (fun _ => 1) ≤ C * Real.log (3 * q) := by
  classical
  rintro ⟨C0, hC0⟩
  set D := max C0 0 with hD
  have hD0 : 0 ≤ D := le_max_right _ _
  have hZ : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ t : ℝ,
      zsumR χ t 1 (fun _ => 1) ≤ D * Real.log (q * (|t| + 2)) := by
    intro q _ χ hχ t
    refine (hC0 q χ hχ t).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.log_nonneg ?_))
    have : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    nlinarith [abs_nonneg t]
  refine ⟨12 * D, ?_⟩
  intro q _ χ hχ T hT
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  refine ⟨?_, ?_⟩
  · obtain ⟨hfin, _⟩ := GlobalTheory.T.dirichletLZerosInWindow_finite_and_pos_order q χ 0 T
    have hfin' : ∀ t : ℝ, (zerosIn χ t 1).Finite := fun t => (GlobalTheory.T.dirichletLZerosInWindow_finite_and_pos_order q χ t 1).1
    have hN1 : 1 ≤ ⌊T⌋₊ := Nat.le_floor (by rw [Nat.cast_one]; linarith)
    have hNT : (⌊T⌋₊ : ℝ) ≤ T := Nat.floor_le (by linarith)
    have hNpos : (0 : ℝ) < ⌊T⌋₊ := by exact_mod_cast hN1
    rw [zsumR_eq_sum_toFinset χ 0 T _ hfin]
    have hsplit : ∀ k : ℕ, ∑ ρ ∈ hfin.toFinset, (zmult χ ρ : ℝ) * ((k : ℝ)⁻¹ *
        ((if ρ ∈ zerosIn χ (k : ℝ) 1 then 1 else 0) + (if ρ ∈ zerosIn χ (-(k : ℝ)) 1 then 1 else 0))) =
        (k : ℝ)⁻¹ * (∑ ρ ∈ hfin.toFinset, (zmult χ ρ : ℝ) * (if ρ ∈ zerosIn χ (k : ℝ) 1 then 1 else 0) +
          ∑ ρ ∈ hfin.toFinset, (zmult χ ρ : ℝ) * (if ρ ∈ zerosIn χ (-(k : ℝ)) 1 then 1 else 0)) := by
      intro k
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ρ _
      ring
    have hLA : 0 ≤ Real.log (q * (T + 2)) := Real.log_nonneg (by nlinarith)
    calc ∑ ρ ∈ hfin.toFinset, (zmult χ ρ : ℝ) * (if 1 < |ρ.im| then 1 / ‖ρ‖ else 0)
        ≤ ∑ ρ ∈ hfin.toFinset, (zmult χ ρ : ℝ) * ∑ k ∈ Icc 1 ⌊T⌋₊, (k : ℝ)⁻¹ *
            ((if ρ ∈ zerosIn χ (k : ℝ) 1 then 1 else 0) + (if ρ ∈ zerosIn χ (-(k : ℝ)) 1 then 1 else 0)) := by
          apply Finset.sum_le_sum
          intro ρ hρ
          exact mul_le_mul_of_nonneg_left (recip_le_sum_windows χ T ρ (hfin.mem_toFinset.mp hρ))
            (Nat.cast_nonneg _)
      _ = ∑ k ∈ Icc 1 ⌊T⌋₊, ∑ ρ ∈ hfin.toFinset, (zmult χ ρ : ℝ) * ((k : ℝ)⁻¹ *
            ((if ρ ∈ zerosIn χ (k : ℝ) 1 then 1 else 0) + (if ρ ∈ zerosIn χ (-(k : ℝ)) 1 then 1 else 0))) := by
          simp_rw [Finset.mul_sum]
          exact Finset.sum_comm
      _ ≤ ∑ k ∈ Icc 1 ⌊T⌋₊, (k : ℝ)⁻¹ * (2 * D * Real.log (q * (T + 2))) := by
          apply Finset.sum_le_sum
          intro k hk
          have hk' := Finset.mem_Icc.mp hk
          have hkT : (k : ℝ) ≤ T := (Nat.cast_le.mpr hk'.2).trans hNT
          rw [hsplit k]
          apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg k))
          have e1 := (sum_indicator_le_zsumR χ (k : ℝ) 1 hfin.toFinset (hfin' _)).trans (hZ q χ hχ k)
          have e2 := (sum_indicator_le_zsumR χ (-(k : ℝ)) 1 hfin.toFinset (hfin' _)).trans
            (hZ q χ hχ (-(k : ℝ)))
          rw [abs_neg] at e2
          have hlog : Real.log (q * (|(k : ℝ)| + 2)) ≤ Real.log (q * (T + 2)) := by
            apply Real.log_le_log (by nlinarith [abs_nonneg (k : ℝ)])
            rw [abs_of_nonneg (Nat.cast_nonneg k)]
            nlinarith
          have := mul_le_mul_of_nonneg_left hlog hD0
          linarith
      _ = 2 * D * Real.log (q * (T + 2)) * ∑ k ∈ Icc 1 ⌊T⌋₊, (k : ℝ)⁻¹ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring
      _ ≤ 2 * D * Real.log (q * (T + 2)) * (1 + Real.log T) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by linarith) hLA)
          have h := harmonic_le_one_add_log ⌊T⌋₊
          simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
          have := Real.log_le_log hNpos hNT
          linarith
      _ ≤ 12 * D * Real.log (q * T) ^ 2 := by
          have hqT : 2 ≤ (q : ℝ) * T := by nlinarith
          have hu : Real.log 2 ≤ Real.log (q * T) := Real.log_le_log (by norm_num) hqT
          have hl2 := Real.log_two_gt_d9
          have hA : Real.log (q * (T + 2)) ≤ 2 * Real.log (q * T) := by
            have h := Real.log_le_log (by nlinarith : (0 : ℝ) < q * (T + 2))
              (by nlinarith : (q : ℝ) * (T + 2) ≤ 2 * (q * T))
            rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt (by nlinarith : (0 : ℝ) < q * T))] at h
            linarith
          have hB : 1 + Real.log T ≤ 3 * Real.log (q * T) := by
            have := Real.log_le_log (by linarith : (0 : ℝ) < T) (by nlinarith : T ≤ (q : ℝ) * T)
            linarith
          have hB0 : 0 ≤ 1 + Real.log T := by
            have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T)
            linarith
          have h := mul_le_mul hA hB hB0 (by linarith)
          have h' := mul_le_mul_of_nonneg_left h (by linarith : (0 : ℝ) ≤ 2 * D)
          calc 2 * D * Real.log (q * (T + 2)) * (1 + Real.log T)
              = 2 * D * (Real.log (q * (T + 2)) * (1 + Real.log T)) := by ring
            _ ≤ 2 * D * (2 * Real.log (q * T) * (3 * Real.log (q * T))) := h'
            _ = 12 * D * Real.log (q * T) ^ 2 := by ring
  · have h := hZ q χ hχ 0
    rw [abs_zero, zero_add] at h
    refine h.trans ?_
    have h1 : Real.log (q * 2) ≤ Real.log (3 * q) := Real.log_le_log (by linarith) (by linarith)
    have h2 : 0 ≤ Real.log (3 * q) := Real.log_nonneg (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left h1 hD0, mul_nonneg hD0 h2]

end GlobalTheory.Mem.An
end
