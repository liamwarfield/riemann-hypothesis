module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.WeilRepresentation.WeilTheta
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilFinFinal
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkTowModel
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.WpSTop
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGSplitFree
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGTop

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGHolds
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseBoxSec
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl.Box
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl.Dense
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {κ β : Type} [Fintype κ] [Fintype β] {m n : ℕ}
variable {A : Spc F E m} {Y : Spc F E n} {B : Base F E}
theorem _root_.GlobalTheory.ThK.Dbl.boxSecX_of_k (hL : _root_.GlobalTheory.ThK.Dbl.FinLevel_k) (hC : _root_.GlobalTheory.ThK.Dbl.Stab2Cpt_k) : _root_.GlobalTheory.ThK.Dbl.BoxSecX_k := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB _ _ hX _ _ hM χ _ _ dd om S l ⟨d', ht, hd⟩ h K a hK _ Φ₁ h1 Φ₂ h2
  have tr : ∀ {p q : ℕ} {u : Matrix (Fin p) (Fin q) (AE F E)}, At (evI F) u → At (evI F) uᵀ := fun hu c hc => by
    rw [← Matrix.transpose_smul, hu c hc, Matrix.transpose_zero]
  refine isSec_of h (polData_kfin hM (fun g₁ s1 g₂ s2 f₁ p1 f₂ p2 => _root_.GlobalTheory.ThK.Dbl.Box.box_kfin_k hL hB hK (hC F E σ B n X r s hB (.inl hX) K hK)
    h.weil.2.1.toIsSplitting hd (fun N n1 n2 => (sInf_le (a := N) ⟨fun f ⟨ε, hε⟩ => n1 ε f fun u u' hu hu' e => ?_,
      fun u hu f hf f₁ e => ?_⟩ : M.Pol B.ψ B.emb ≤ N)) s1 s2 p1 p2) h1 h2)
  · rw [← u.transpose_transpose, ← u'.transpose_transpose, ht, ht]
    refine hε uᵀ u'ᵀ (tr hu) (tr hu') (fun w => ?_) _ _ (actsD_dop M hB.std (tr hu) f) (actsD_dop M hB.std (tr hu') f)
    rw [Matrix.transpose_map, Matrix.transpose_map, e w, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.mul_assoc]
  · rw [actsD_unique' M hB.std hu e]
    have hmem := n2 uᵀ (tr hu) f hf
    rwa [ht] at hmem
end GlobalTheory.ThK.Dbl.Box
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseSWStd
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl.Box
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl.Dense
open GlobalTheory.Doubling (absE)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {κ : Type} [Fintype κ] {m n : ℕ} {A : Spc F E m} {Y : Spc F E n} {B : Base F E} {ψ : AddChar (AF F) ℂ}
variable {dd} {χ : Chr F E} {om S l}
theorem sw_transl_k (h1 : _root_.GlobalTheory.ThK.Dbl.SiegelWeilStd_k) (h2 : _root_.GlobalTheory.ThK.Dbl.FrameConj_k) {r s r' s'} (hB : _root_.UpperTheory.TP.W.GoodK σ B) (hm : 1 ≤ m) (hn : 1 ≤ n) (h0 : min r s = 0)
    (hA : A.IsHerm σ B r s ∧ Y.IsSkew σ B r' s' ∨ A.IsSkew σ B r s ∧ Y.IsHerm σ B r' s') (hχ : IsHecke F E χ)
    (hc : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m) {dd om S l}
    (h : IsDbl (σ := σ) (A := A) (Y := Y) (κ := κ ⊕ κ) B.ψ dd χ om S l) {K a} (hK : IsStab2 B K) (ha : IsHgt K a)
    {μ : Measure (UA σ A.J)} {D : Set (UA σ A.J)} (hμ : μ.IsHaarMeasure) (hD : IsFundamentalDomain (ratU σ A.J) D μ)
    {Φ} (hΦ : Φ ∈ kfin om K) : EisValueAt (flat a (fun x => l (om x Φ)) (((m : ℂ) - n) / 2)) (((m : ℂ) - n) / 2)
      fun x => (if n < m then 1 else 2) * ⨍ g in D, thetaSum F (om x (S g Φ)) ∂μ := by
  obtain ⟨N, _, n0, n1, n2⟩ := hΦ
  obtain ⟨b, K₀, p, t, hb, hK₀, hp, hk⟩ := h2 F E σ B n Y r' s' hB (hA.symm.imp And.right And.right) K hK
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = absE F E (Matrix.GeneralLinearGroup.det t) := ⟨_, rfl⟩
  have d0 : 0 < d := hd ▸ absE_pos _
  have a0 : ∀ x, 0 < a x := fun x => by
    obtain ⟨q, u, hq, k, hk, rfl⟩ := ha.iwa x
    exact ha.val q u hq k hk ▸ absE_pos _
  have hk' : ∀ k ∈ K₀, p * k * p⁻¹ ∈ K := fun k h => (hk _).2 (by simpa [mul_assoc] using h)
  have ha₀ : IsHgt K₀ fun x => d * a (x * p⁻¹) := by
    refine ⟨fun x => ?_, fun q u hq k h => ?_⟩
    · obtain ⟨q, u, hq, k, h, e⟩ := ha.iwa (x * p⁻¹)
      exact ⟨q * p, _, hq.mul hp, _, (hk k).1 h, by rw [mul_inv_eq_iff_eq_mul.1 e]; group⟩
    · rw [show q * k * p⁻¹ = q * p⁻¹ * (p * k * p⁻¹) by group, ha.val _ _ (hq.mul hp.inv) _ (hk' k h), map_mul, map_mul, map_inv,
        map_inv, NNReal.coe_mul, NNReal.coe_inv, ← hd]
      field_simp
  have mul : ∀ x y Ψ, om x (om y Ψ) = om (x * y) Ψ := fun x y Ψ => by rw [map_mul, Module.End.mul_apply]
  intro x
  obtain ⟨e, e1, ⟨t₁, e2⟩, e3, e4⟩ := h1 F E σ B m n A Y r s r' s' hB hm hn h0 hA χ hχ hc _ dd om S l h b K₀ _ hb hK₀ ha₀ μ D hμ hD
    (om p⁻¹ Φ) (h.weil.2.1.pres _ _ (n0 n1)) (Submodule.finiteDimensional_of_le (S₂ := N.map (om p⁻¹)) (Submodule.span_le.2 (by
      rintro _ ⟨k, rfl⟩
      exact ⟨_, n2 _ (hk' k k.2) Φ n1, by simp only [mul]; congr 2; group⟩))) (x * p)
  have dc : Differentiable ℂ fun z : ℂ => (d : ℂ) ^ (((m : ℂ) - n) / 2 - z) :=
    (differentiable_id.const_sub _).const_cpow (.inl (Complex.ofReal_ne_zero.2 d0.ne'))
  refine ⟨fun z => (d : ℂ) ^ (((m : ℂ) - n) / 2 - z) * e z, fun z hz => (dc.analyticAt z).meromorphicAt.mul (e1 z hz),
    ⟨t₁, fun z hz => ?_⟩, (dc.analyticAt _).mul e3, ?_⟩
  · refine (congrArg (HasSum · _) (funext fun q => ?_)).mpr ((e2 z hz).mul_left ((d : ℂ) ^ (((m : ℂ) - n) / 2 - z)))
    simp only [eisTerm, flat, mul, ← mul_assoc, mul_inv_cancel_right]
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg d0.le (a0 _).le, ← mul_assoc,
      ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 d0.ne')]
    simp
  · simp only [e4, sub_self, Complex.cpow_zero, one_mul, ← dbl_comm hB.std h hp.inv _ (n0 n1), mul, mul_inv_cancel_right]
theorem _root_.GlobalTheory.ThK.Dbl.siegelWeilAniso_of_k (h1 : _root_.GlobalTheory.ThK.Dbl.SiegelWeilStd_k) (h2 : _root_.GlobalTheory.ThK.Dbl.FrameConj_k) (hL : _root_.GlobalTheory.ThK.Dbl.FinLevel_k) (hC : _root_.GlobalTheory.ThK.Dbl.Stab2Cpt_k) :
    _root_.GlobalTheory.ThK.Dbl.SiegelWeilAniso_k := by
  refine ⟨?_, ?_⟩
  · intro F E _ _ _ _ _ σ B m n A Y M r s r' s' hB hm hn hA h0 hY hM χ hχ hc dd om S l hd h K a hK ha Φ₁ p1 Φ₂ p2
    refine _root_.GlobalTheory.ThK.Dbl.Box.sw_transl_k h1 h2 hB hm hn h0 (.inl ⟨hA, hY⟩) hχ hc h hK ha hM.haar hM.dom
      (polData_kfin hM (fun g₁ s1 g₂ s2 f₁ p1 f₂ p2 => _root_.GlobalTheory.ThK.Dbl.Box.box_kfin_k hL hB hK (hC F E σ B n Y r' s' hB (.inr hY) K hK)
      h.weil.2.1.toIsSplitting hd (fun N n1 n2 => (sInf_le (a := N) ⟨fun f ⟨ε, hε⟩ => n1 ε f fun u u' hu hu' e => ?_,
        fun u hu f hf f₁ e => ?_⟩ : M.Pol B.ψ B.emb ≤ N)) s1 s2 p1 p2) p1 p2)
    · exact hε u u' hu hu' e _ _ (actsD_dop M hB.std hu f) (actsD_dop M hB.std hu' f)
    · rw [actsD_unique' M hB.std hu e]; exact n2 u hu f hf
  · intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB hn hd' hX hW h0 hM χ hχ hc dd om S l ⟨d', ht, hd⟩ h K a hK ha μ D hμ hD Φ₁ p1 Φ₂ p2
    have tr : ∀ {p q : ℕ} {u : Matrix (Fin p) (Fin q) (AE F E)}, At (evI F) u → At (evI F) uᵀ := fun hu c hc => by
      rw [← Matrix.transpose_smul, hu c hc, Matrix.transpose_zero]
    refine _root_.GlobalTheory.ThK.Dbl.Box.sw_transl_k h1 h2 hB hd' hn h0 (.inr ⟨hW, hX⟩) hχ hc h hK ha hμ hD
      (polData_kfin hM (fun g₁ s1 g₂ s2 f₁ p1 f₂ p2 => _root_.GlobalTheory.ThK.Dbl.Box.box_kfin_k hL hB hK (hC F E σ B n X r s hB (.inl hX) K hK)
      h.weil.2.1.toIsSplitting hd (fun N n1 n2 => (sInf_le (a := N) ⟨fun f ⟨ε, hε⟩ => n1 ε f fun u u' hu hu' e => ?_,
        fun u hu f hf f₁ e => ?_⟩ : M.Pol B.ψ B.emb ≤ N)) s1 s2 p1 p2) p1 p2)
    · have er : Rel B.emb ε X.θ W.θ uᵀ u'ᵀ := fun w => by
        simpa [Matrix.transpose_map, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.mul_assoc] using congrArg Matrix.transpose (e w)
      have he := hε uᵀ u'ᵀ (tr hu) (tr hu') er _ _ (actsD_dop M hB.std (tr hu) f) (actsD_dop M hB.std (tr hu') f)
      have ht1 : d'.e u = M.co.e uᵀ := by simpa using ht uᵀ
      have ht2 : d'.e u' = M.co.e u'ᵀ := by simpa using ht u'ᵀ
      rw [ht1, ht2]
      change dop (aOf M u'ᵀ) (lOf M u'ᵀ) f = Complex.I • dop (aOf M uᵀ) (lOf M uᵀ) f
      exact he
    · rw [actsD_unique' M hB.std hu e]
      have := n2 uᵀ (tr hu) f hf
      rwa [ht] at this
end GlobalTheory.ThK.Dbl.Box
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.VacFix2K
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsBetaK
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl.Vf2
open scoped Matrix TensorProduct
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.InertChart GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open PositivityTheory.ThK PositivityTheory.ThK.Vac PositivityTheory.ThKH.Iwas GlobalTheory.Doubling PositivityTheory.ThKG.Loc.Cone.Vf
open Formalism.UG (bc)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {v : Pl F}
theorem exists_res_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) (v : Pl F) : ∃ (K : Type) (_ : Field K) (r : intLoc F E v →+* K),
    Function.Surjective r ∧ (((∀ z, r z = 0 → r (cInt σ v z) = 0) ∧ ∃ κ, r (κ - cInt σ v κ) ≠ 0) ∨
      ∃ η, r η = 1 ∧ r (cInt σ v η) = 0) ∧ ∀ z, r z ≠ 0 → r (cInt σ v z) ≠ 0 → IsUnit z := by
  have hσ := hB.cm
  rcases _root_.GlobalTheory.KFinLoc.split_or_inert_k F E σ B hB v with ⟨⟨τ⟩⟩ | ⟨w, hw⟩
  · let ρ : intLoc F E v →+* v.adicCompletionIntegers F := ((splitProj τ : Fv F v ⊗[F] E →+* Fv F v).comp
      (intLoc F E v).subtype).codRestrict (v.adicCompletionIntegers F).toSubring fun z => splitProj_mem τ z.2
    have mk : ∀ a b : v.adicCompletionIntegers F, (splitAlgEquiv hσ τ).symm (a.1, b.1) ∈ intLoc F E v := fun a b =>
      (mem_intLoc_iff_split hσ τ).2 ⟨by rw [splitProj_symm]; exact a.2, by rw [splitProj_comp_symm]; exact b.2⟩
    refine ⟨_, inferInstance, (IsLocalRing.residue _).comp ρ,
      IsLocalRing.residue_surjective.comp fun a => ⟨⟨_, mk a 0⟩, Subtype.ext (splitProj_symm hσ τ _)⟩,
      .inr ⟨⟨_, splitIdem_mem hσ τ⟩, ?_, ?_⟩, fun z h1 h2 => ?_⟩
    · exact (congrArg (IsLocalRing.residue _) (Subtype.ext (splitProj_splitIdem hσ τ) : ρ ⟨_, splitIdem_mem hσ τ⟩ = 1)).trans (map_one _)
    · exact (congrArg (IsLocalRing.residue _) (Subtype.ext ((splitProj_comp τ σ _).symm.trans (splitProj_comp_splitIdem hσ τ)) :
        ρ (cInt σ v ⟨_, splitIdem_mem hσ τ⟩) = 0)).trans (map_zero _)
    · obtain ⟨a, ha⟩ := ((IsLocalRing.residue_ne_zero_iff_isUnit _).1 h1).exists_right_inv
      obtain ⟨b, hb⟩ := ((IsLocalRing.residue_ne_zero_iff_isUnit _).1 h2).exists_right_inv
      refine IsUnit.of_mul_eq_one ⟨_, mk a b⟩ (Subtype.ext (split_ext hσ τ ?_ ?_))
      · rw [Subring.coe_mul, map_mul, splitProj_symm, Subring.coe_one, map_one]; exact congrArg Subtype.val ha
      · rw [Subring.coe_mul, map_mul, splitProj_comp_symm, Subring.coe_one, map_one, splitProj_comp]; exact congrArg Subtype.val hb
  · have hu : w.under (𝓞 F) = v := (under_eq_iff hw w).2 rfl
    obtain ⟨c, hc, -⟩ := existsUnique_isConjAt σ hw hu
    obtain ⟨ϖ, -, hv, -, -, ⟨x, hx, hx1⟩, -⟩ := exists_isUnramInv hσ hw hc
    let ρ : intLoc F E v →+* w.adicCompletionIntegers E :=
      ((toCompl hu).comp (intLoc F E v).subtype).codRestrict (w.adicCompletionIntegers E).toSubring fun z => toCompl_mem hu z.2
    have sj : Function.Surjective ρ := fun a => by
      obtain ⟨z, hz⟩ := (toCompl_bijective hw hu).2 a.1
      exact ⟨⟨z, (mem_intLoc_iff hw hu _).2 (hz ▸ a.2)⟩, Subtype.ext hz⟩
    have un : ∀ z, ((IsLocalRing.residue _).comp ρ) z ≠ 0 ↔ Valued.v (toCompl hu z.1) = 1 := fun z =>
      (IsLocalRing.residue_ne_zero_iff_isUnit _).trans HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
    refine ⟨_, inferInstance, (IsLocalRing.residue _).comp ρ, IsLocalRing.residue_surjective.comp sj,
      .inl ⟨fun z hz => by_contra fun h => (un z).2 ?_ hz, ?_⟩, fun z h1 _ => ?_⟩
    · rw [← hv, hc]
      exact (un (cInt σ v z)).1 h
    · obtain ⟨κ, hκ⟩ := sj ⟨x, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hx⟩
      refine ⟨κ, (un _).2 ?_⟩
      change Valued.v (toCompl hu (κ.1 - sigR _ σ κ.1)) = 1
      rw [map_sub, ← hc, show toCompl hu κ.1 = x from congrArg Subtype.val hκ, Valuation.map_sub_swap, hx1]
    · obtain ⟨a, ha⟩ := ((IsLocalRing.residue_ne_zero_iff_isUnit _).1 h1).exists_right_inv
      obtain ⟨z', rfl⟩ := sj a
      refine IsUnit.of_mul_eq_one z' (Subtype.ext ((toCompl_bijective hw hu).1 ?_))
      rw [Subring.coe_mul, map_mul, Subring.coe_one, map_one]; exact congrArg Subtype.val ha
theorem exists_beta_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {X : Spc F E n} {r s : ℕ} (hX : X.IsHerm σ B r s)
    (g : UG (cA σ) (dbl (incM F X.J))) {x y a₁ a₂ : Matrix (Fin n) (Fin n) (AE F E)}
    (hg : g.1.1 * (diagCols (Fin n) : Matrix _ _ (AE F E)) = Matrix.fromRows x y) (hx : x ∈ Pres v X) (hy : y ∈ Pres v X)
    (h1 : a₁ ∈ Pres v X) (h2 : a₂ ∈ Pres v X) (h : a₁ * x + a₂ * y = 1) (ax : At (evFin F v) (x - 1)) (ay : At (evFin F v) (y - 1)) :
    ∃ b b' t', Adj (cA σ) (incM F X.J) b b' ∧ b + b' = -1 ∧ b ∈ Pres v X ∧ t' ∈ Pres v X ∧ (y + b * (y - x)) * t' = 1 := by
  have hσ := cm_conj_conj hB.cm
  have cc := _root_.PositivityTheory.SiegelWeilFormula.kfour.cA_cA' σ hσ
  have hL := hX.lat
  obtain ⟨K, _, ρ, r1, r2, r3⟩ := _root_.GlobalTheory.ThK.Dbl.Vf2.exists_res_k hB v
  obtain ⟨P, p1, p2⟩ := Frames.exists_rational_frame X.L v
  obtain ⟨G', hG', g1, g2⟩ := Hgt.gram_loc (v := v) (herm_det hX) hL.fg (I := IsIntegral ℤ) (fun z hz b => hz.mul b.2) hX.dual
    isIntegral_one (fun z hz => ⟨1, (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top, ⟨z, hz⟩, by simp; rfl⟩) P p1 p2
  simp only [inv_one, one_mul] at g1 g2
  have ha := fr_iff (Frames.frame_of_rational P p1 p2)
  set G₀ := P.1ᵀ * X.J * P.1.map σ with hG₀
  let ι := inclR (F := F) (E := E) (Fv F v)
  set a : GL (Fin n) (Fv F v ⊗[F] E) := bc ι P
  let j := (intLoc F E v).subtype.mapMatrix (m := Fin n)
  have inj : Function.Injective j := fun A B e => Matrix.ext fun i k => Subtype.ext (congrFun₂ e i k)
  let G : Matrix (Fin n) (Fin n) (intLoc F E v) := fun i k => ⟨_, (g1 i k).mem⟩
  let H : Matrix (Fin n) (Fin n) (intLoc F E v) := fun i k => ⟨_, (g2 i k).mem⟩
  have eG : a.1ᵀ * (incM F X.J).map (compFin F E v) * a.1.map (sigR _ σ) = j G := by
    change _ = G₀.map ι
    rw [hG₀, Matrix.map_mul, Matrix.map_mul, show (incM F X.J).map (compFin F E v) = X.J.map ι from
      Matrix.ext fun i k => congrArg (· ⊗ₜ[F] X.J i k) (map_one (evFin F v))]
    rfl
  have jj : ∀ N N' : Matrix (Fin n) (Fin n) (intLoc F E v), j (Nᵀ * G * N'.map (cInt σ v)) = (j N)ᵀ * j G * (j N').map (sigR _ σ) :=
    fun N N' => by rw [map_mul, map_mul]; rfl
  obtain ⟨θ₀, hθ⟩ := _root_.GlobalTheory.exists_int_add_conj_eq_one_of_base_good_k B hB
  let θ : AE F E := inclR (F := F) (AF F) (θ₀ : E)
  have iθ : compFin F E v (-θ) ∈ intLoc F E v := by
    rw [map_neg]; exact neg_mem (tmul_mem_intLoc (show evFin F v 1 ∈ _ by rw [map_one]; exact one_mem _) θ₀)
  have b0 : Adj (cA σ) (incM F X.J) ((-θ) • 1) ((-cA σ θ) • 1) := Adj.one.smul (by rw [map_neg, cc])
  have hb0 : (-θ) • (1 : Matrix (Fin n) (Fin n) (AE F E)) + (-cA σ θ) • 1 = -1 := by
    rw [← add_smul, ← neg_add, show θ + cA σ θ = inclR (F := F) (AF F) (θ₀ + σ θ₀ : E) from (map_add _ _ _).symm, hθ, map_one,
      neg_smul, one_smul]
  have pb0 := smul_mem_Pres hL iθ (one_mem (Pres v X))
  have lag := lag_of b0 hb0 g hg
  set b₀ := (-θ) • (1 : Matrix (Fin n) (Fin n) (AE F E))
  have pm := sub_mem hy hx
  obtain ⟨Nm, hNm⟩ := (ha _).1 pm
  obtain ⟨NM, hNM⟩ := (ha _).1 (add_mem hy (mul_mem pb0 pm))
  obtain ⟨NP, hNP⟩ := (ha _).1 (add_mem h1 h2)
  obtain ⟨NQ, hNQ⟩ := (ha _).1 (sub_mem (neg_mem h1) (mul_mem (add_mem h1 h2) pb0))
  obtain ⟨S, s1, s2⟩ := exists_skew (c := cInt σ v) (r := ρ) (G := G) (G' := H) (M := NM) (m := Nm) (P := NP) (Q := NQ)
    (fun z => Subtype.ext (by
      change sigR _ σ (sigR _ σ z.1) = z.1
      induction z.1 using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (hσ x)
      | add x y hx hy => simp only [map_add (f := _), hx, hy])) r1
    (fun i k => Subtype.ext (congrArg ι (by
      change σ (G₀ k i) = G₀ i k
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hG₀, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hσ, hX.herm, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)))
    (inj (by
      rw [map_mul, map_one]
      change G₀.map ι * G'.map ι = 1
      rw [← Matrix.map_mul, mul_eq_one_comm.1 hG', Matrix.map_one _ (map_zero _) (map_one _)])) r2 r3
    (inj (by
      rw [map_add (f := _), jj, jj, hNm, hNM, ← eG, ← gram_fr, ← gram_fr, ← Matrix.add_mul, ← Matrix.mul_add,
        ← Matrix.map_add _ (map_add _), lag, Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul, map_zero]))
    (inj (by
      rw [map_add (f := _), map_mul, map_mul, hNm, hNM, hNP, hNQ, ← map_mul, ← map_mul, ← map_add (f := _), map_one, ← map_one (fr v a), ← h]
      congr 1
      noncomm_ring))
  let SA : Matrix (Fin n) (Fin n) (AE F E) := (a.1 * j S * (a⁻¹).1).map (sgE E v)
  have aS : At (evFin F v) SA := fun u hu => Matrix.ext fun i k => at_sgE _ u hu
  have fS : fr v a SA = j S := by
    rw [fr_apply, show SA.map (compFin F E v) = a.1 * j S * (a⁻¹).1 from Matrix.ext fun _ _ => comp_sgE _]
    simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, Units.inv_mul_cancel_left]
  have sk : SAᵀ * incM F X.J + incM F X.J * SA.map (cA σ) = 0 := by
    have k1 := gram_fr (σ := σ) a (incM F X.J) SA 1
    have k2 := gram_fr (σ := σ) a (incM F X.J) 1 SA
    have k3 := congrArg j s1
    have k4 := jj S 1
    have k5 := jj 1 S
    simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, map_one, mapc_one, fS, eG,
      Matrix.map_one _ (map_zero (sigR (Fv F v) σ)) (map_one _), Matrix.map_one _ (map_zero (cInt σ v)) (map_one _)] at k1 k2 k4 k5
    rw [map_add (f := _), k4, k5, ← k1, ← k2, ← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.map_add _ (map_add _), map_zero] at k3
    have u1 : IsUnit a.1ᵀ := (Matrix.isUnit_transpose _).2 a.isUnit
    have u2 : IsUnit (a.1.map (sigR (Fv F v) σ)) := a.isUnit.map (sigR (Fv F v) σ).mapMatrix
    rw [u2.mul_left_eq_zero, u1.mul_right_eq_zero] at k3
    refine Matrix.ext fun i k => eq_zero_of_at (v := v) (fun u hu => congrFun₂ (at_add (at_mul_left (M := SAᵀ)
      (fun u hu => congrArg Matrix.transpose (aS u hu)) _) (at_mul_right _ (N := SA.map (cA σ)) fun u hu => Matrix.ext fun i k => by
        change u • cA σ (SA i k) = 0
        rw [← map_smul, show u • SA i k = 0 from congrFun₂ (aS u hu) i k, map_zero]) u hu) i k) (congrFun₂ k3 i k)
  have am : At (evFin F v) (y - x) := by simpa using at_sub ay ax
  obtain ⟨t', pt, ht⟩ := exists_inv ha (f := y + (b₀ + SA) * (y - x)) (N := NM + S * Nm)
    (by rw [add_sub_right_comm]; exact at_add ay (at_mul_right _ am))
    (by rw [map_add (f := _), map_mul, hNm, hNM, ← fS, ← map_mul, ← map_add (f := _), add_mul, add_assoc]) s2
  exact ⟨b₀ + SA, _ + -SA, t', b0.add (by rw [Adj, mapc_neg, Matrix.mul_neg]; exact eq_neg_of_add_eq_zero_left sk),
    by rw [add_add_add_comm, add_neg_cancel, add_zero, hb0], add_mem pb0 ((ha _).2 ⟨S, fS.symm⟩), pt, ht⟩
end GlobalTheory.ThK.Dbl.Vf2
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LocConeVfEig
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.MemLatAtVK
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace PositivityTheory.ThK.Vac
open scoped Matrix TensorProduct nonZeroDivisors
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.LatVac
open GlobalTheory.StdDual (codiff codiff_ne_zero)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
theorem mem_latW_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {W : Spc F E d} {r s : ℕ} (hW : W.IsSkew σ B r s) (v : Pl F)
    {w : Fin d → AE F E} (hw : At (evFin F v) w)
    (h : ∀ y ∈ W.L, ∀ a ∈ v.adicCompletionIntegers F, B.ψ (liftV v a * trF σ W.J y w) = 1) : w ∈ latW W v := by
  have hσ := sigma_sigma hB.cm
  have hfull : Submodule.span E (W.L : Set (Fin d → E)) = ⊤ := by
    let T := Submodule.span E (W.L : Set (Fin d → E))
    change T = ⊤
    by_contra hT
    let g : (Fin d → E) →ₗ[E] Module.Dual E T :=
      ((dotProductBilin E E).compl₂ (Matrix.mulVecLin W.Jᵀ)).domRestrict₂ T
    have hdim : Module.finrank E (Module.Dual E T) < Module.finrank E (Fin d → E) := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt hT
    obtain ⟨z, hz, hz₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    let y : Fin d → E := fun i => σ (z i)
    have hy₀ : y ≠ 0 := by
      intro hy
      apply hz₀
      exact funext fun i => σ.injective ((congrFun hy i).trans (map_zero σ).symm)
    have horth (x : Fin d → E) (hx : x ∈ W.L) : form σ W.J y x = 0 := by
      have hz' : z ⬝ᵥ W.Jᵀ *ᵥ x = 0 :=
        congrArg (fun f : Module.Dual E T => f ⟨x, Submodule.subset_span hx⟩)
          (LinearMap.mem_ker.mp hz)
      rw [Matrix.dotProduct_transpose_mulVec] at hz'
      have hz'' : form σ W.J x y = 0 := by
        simpa only [form, y, sigma_sigma hB.cm] using hz'
      have hs : σ (form σ W.J y x) = (-1 : E) * form σ W.J x y := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hW.skew, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      rw [hz'', mul_zero] at hs
      exact (map_eq_zero σ).1 hs
    have hline (a : E) : a • y ∈ W.L := (hW.dual _).2 fun x hx => by
      have he : form σ W.J (a • y) x = 0 := by
        change (a • y) ⬝ᵥ W.J *ᵥ (fun i => σ (x i)) = 0
        rw [smul_dotProduct, smul_eq_mul, show y ⬝ᵥ W.J *ᵥ (fun i => σ (x i)) = 0 from horth x hx, mul_zero]
      simp only [he, mul_zero, map_zero]
      exact fun _ => isIntegral_zero
    let i : E →ₗ[𝓞 E] W.L :=
      ((LinearMap.toSpanSingleton E _ y).restrictScalars (𝓞 E)).codRestrict W.L hline
    let : Module.Finite (𝓞 E) W.L := Module.Finite.iff_fg.mpr hW.lat.fg
    let : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun a b hab =>
      smul_left_injective E hy₀ (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
  have : Module.Finite (𝓞 F) (𝓞 E) := Module.Finite.of_restrictScalars_finite ℤ _ _
  obtain ⟨m, g, f, hg, hf, hid⟩ := dual_family (𝓞 F) F (W.L.restrictScalars (𝓞 F)) (hW.lat.fg.restrictScalars) (by
    rw [eq_top_iff]
    intro x _
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) E
      (W.L : Set (Fin d → E)) x (hfull ▸ Submodule.mem_top)
    obtain ⟨_, k, hk, rfl⟩ := t
    rw [Submodule.span_eq] at ht
    have hk0 : (k : F) ≠ 0 := Int.cast_ne_zero.2 (nonZeroDivisors.ne_zero hk)
    have ht' : (k : F) • x ∈ W.L := by
      rw [Int.cast_smul_eq_zsmul, ← algebraMap_smul (𝓞 E) k x]; exact ht
    rw [← inv_smul_smul₀ hk0 x]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ht'))
  choose u hu using fun i => exists_tr_rep hσ (skew_det hW) (f i)
  have hdec : ∀ z : Fin d → AE F E, z = ∑ i, trF σ W.J (u i) z • incV (g i) := fun z => by
    have hz := span_incV z
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, rfl⟩ := hz
      simp only [trF_incV, ← hu]
      ext j
      conv_lhs => rw [hid x]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [incV, Finset.sum_apply, Pi.smul_apply, map_sum, algebraMap_smul]
      exact Finset.sum_congr rfl fun i _ =>
        map_smul (Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E) _ _
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add (f := _), add_smul, Finset.sum_add_distrib, ← hx, ← hy]
    | smul a x _ hx => simp only [map_smul, smul_eq_mul, mul_smul, ← Finset.smul_sum, ← hx]
  rw [hdec w]
  refine sum_mem fun i _ => AddSubgroup.subset_closure ⟨_, fun a ha => ?_, ?_, g i, hg i, rfl⟩
  · rw [← map_smul, hw a ha, map_zero]
  · refine mem_int_of_psi hB.std v _ fun t ht a ha => ?_
    have hm : algebraMap F E t • u i ∈ W.L := (hW.dual _).2 fun x hx o => by
      let o' : 𝓞 E := ⟨σ o, (RingOfIntegers.isIntegral_coe o).map (σ.restrictScalars ℤ)⟩
      obtain ⟨c, hc⟩ := hf i _ (W.L.smul_mem o' hx)
      have e : (o : E) * form σ W.J (algebraMap F E t • u i) x = t • form σ W.J (u i) (o' • x) := by
        rw [form_eq, form_eq, Algebra.smul_def t, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        have : (o' • x) l = σ o * x l := rfl
        rw [this, map_mul, hσ, Matrix.smul_vecMul, Pi.smul_apply, smul_eq_mul]
        ring
      rw [e, ← Algebra.trace_trace (S := F), map_smul, ← hu, ← hc, smul_eq_mul]
      obtain ⟨k, hk⟩ := (FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F))).1 ht _
        ((FractionalIdeal.mem_one_iff _).2 ⟨c, rfl⟩)
      rw [Algebra.traceForm_apply] at hk
      rw [← hk]
      exact isIntegral_algebraMap
    have := h _ hm a ha
    rwa [trF_smul, liftV_mul, map_mul (evFin F v), AlgHom.commutes] at this
theorem mem_latAtV_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {X : Spc F E n} {W : Spc F E d} {r s r' s' : ℕ} (hX : X.IsHerm σ B r s)
    (hW : W.IsSkew σ B r' s') (v : Pl F) {z : Matrix (Fin n) (Fin d) (AE F E)} (hz : At (evFin F v) z)
    (h : ∀ γ ∈ latAtV X W v, B.ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) γ z) = 1) : z ∈ latAtV X W v := by
  have hσ := sigma_sigma hB.cm
  have hfull : Submodule.span E (X.L : Set (Fin n → E)) = ⊤ := by
    let T := Submodule.span E (X.L : Set (Fin n → E))
    change T = ⊤
    by_contra hT
    let g : (Fin n → E) →ₗ[E] Module.Dual E T :=
      ((dotProductBilin E E).compl₂ (Matrix.mulVecLin X.Jᵀ)).domRestrict₂ T
    have hdim : Module.finrank E (Module.Dual E T) < Module.finrank E (Fin n → E) := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt hT
    obtain ⟨z, hz, hz₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    let y : Fin n → E := fun i => σ (z i)
    have hy₀ : y ≠ 0 := by
      intro hy
      apply hz₀
      exact funext fun i => σ.injective ((congrFun hy i).trans (map_zero σ).symm)
    have horth (x : Fin n → E) (hx : x ∈ X.L) : form σ X.J y x = 0 := by
      have hz' : z ⬝ᵥ X.Jᵀ *ᵥ x = 0 :=
        congrArg (fun f : Module.Dual E T => f ⟨x, Submodule.subset_span hx⟩)
          (LinearMap.mem_ker.mp hz)
      rw [Matrix.dotProduct_transpose_mulVec] at hz'
      have hz'' : form σ X.J x y = 0 := by
        simpa only [form, y, sigma_sigma hB.cm] using hz'
      have hs : σ (form σ X.J y x) = (1 : E) * form σ X.J x y := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hX.herm, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      rw [hz'', mul_zero] at hs
      exact (map_eq_zero σ).1 hs
    have hline (a : E) : a • y ∈ X.L := (hX.dual _).2 fun x hx => by
      have he : form σ X.J (a • y) x = 0 := by
        change (a • y) ⬝ᵥ X.J *ᵥ (fun i => σ (x i)) = 0
        rw [smul_dotProduct, smul_eq_mul, show y ⬝ᵥ X.J *ᵥ (fun i => σ (x i)) = 0 from horth x hx, mul_zero]
      rw [he]
      exact isIntegral_zero
    let i : E →ₗ[𝓞 E] X.L :=
      ((LinearMap.toSpanSingleton E _ y).restrictScalars (𝓞 E)).codRestrict X.L hline
    let : Module.Finite (𝓞 E) X.L := Module.Finite.iff_fg.mpr hX.lat.fg
    let : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun a b hab =>
      smul_left_injective E hy₀ (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
  obtain ⟨m, g, f, hg, hf, hid⟩ := dual_family (𝓞 E) E X.L hX.lat.fg hfull
  let a : Fin m → Fin n → E := fun i k => f i (Pi.single k 1)
  let u : Fin m → Fin n → E := fun i => (fun k => σ (a i k)) ᵥ* X.J⁻¹
  have hu : ∀ i, u i ᵥ* X.J = fun k => σ (a i k) := fun i => by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (herm_det hX), Matrix.vecMul_one]
  have huL : ∀ i, u i ∈ X.L := fun i => (hX.dual _).2 fun x hx => by
    obtain ⟨c, hc⟩ := hf i x hx
    have e : form σ X.J (u i) x = σ (f i x) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [form_eq, hu, LinearMap.pi_apply_eq_sum_univ (f i) x, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_eq_mul, map_mul, mul_comm]
      have : (fun j => if k = j then (1 : E) else 0) = Pi.single k 1 := funext fun j => by
        rw [Pi.single_apply]; exact if_congr eq_comm rfl rfl
      rw [this]
    rw [e, ← hc]
    exact (RingOfIntegers.isIntegral_coe c).map (σ.restrictScalars ℤ)
  have hdec : z = ∑ i, Matrix.vecMulVec (incV (g i)) (incV (a i) ᵥ* z) := by
    ext p l
    have e : ∀ k, ∑ i, incV (F := F) (g i) p * incV (a i) k = (1 : Matrix (Fin n) (Fin n) (AE F E)) p k := fun k => by
      have := congrFun (hid (Pi.single k 1)) p
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [incV, ← map_mul, ← map_sum, mul_comm (g _ p), a, ← this, Pi.single_apply, Matrix.one_apply]
      split_ifs <;> simp
    simp only [Matrix.sum_apply, Matrix.vecMulVec_apply, Matrix.vecMul, dotProduct, Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, e]
    exact (congrFun (congrFun (Matrix.one_mul z) p) l).symm
  rw [hdec]
  refine sum_mem fun i _ => vecMulVec_mem (hg i) (_root_.PositivityTheory.ThK.Vac.mem_latW_k hB hW v (fun c hc => ?_) fun y hy c hc => ?_)
  · rw [← Matrix.vecMul_smul, hz c hc, Matrix.vecMul_zero]
  · have := h _ (neg_mem (AddSubgroup.subset_closure ⟨liftV v c, at_liftV v c, by rwa [evFin_liftV], u i, huL i, y, hy, rfl⟩))
    rw [GlobalTheory.LatVacArith.symp_neg_left, ← one_smul (AF F) z, symp_smul_smul, symp_vecMulVec hσ, hu] at this
    simpa only [hσ, mul_one, mul_neg, neg_neg] using this
end PositivityTheory.ThK.Vac
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace PositivityTheory.ThKG.Loc.Cone.Vf
open scoped Matrix TensorProduct GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.LatVac
open PositivityTheory.ThK PositivityTheory.ThK.Vac PositivityTheory.ThKH.Iwas PositivityTheory.ThKH.Locrep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {v : Pl F}
section Alg
variable {R A α β : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) [Fintype α] [Fintype β]
end Alg
theorem dbl_eigen_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {X : Spc F E n} {W : Spc F E d} {r s r' s' : ℕ} (hX : X.IsHerm σ B r s)
    (hW : W.IsSkew σ B r' s') {M : Model σ X W} {φ} (hφ : M.IsVac B.ψ v φ)
    {d' : Darboux (symp (R := AF F) (cA σ) (-1) (incM F W.J) (incM F X.J)) (Fin n × Fin d)} (hd' : ∀ x, d'.e xᵀ = M.co.e x)
    {dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F W.J) (dbl (incM F X.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d))}
    (hdd : IsDblCoord (cA σ) (-1) (incM F W.J) (incM F X.J) d' dd) {omd}
    (hsp : IsSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd) (g : UG (cA σ) (dbl (incM F X.J)))
    (hg : At (evFin F v) (g.1.1 - 1)) (hg' : PresD v X (g⁻¹).1.1) :
    ∃ c : ℂ, Acts (evFin F v) (omd g) (boxFun φ (star φ)) (c • boxFun φ (star φ)) := by
  obtain ⟨hs, h0, θ, -, hθ⟩ := hφ
  have hAt := (latAtV_at_stable X W v).1
  obtain ⟨r₀, x₀, h₀, h₁⟩ := exists_base (Fin n × Fin d) v
  have hv : ∀ γ ∈ latAtV X W v, schr (psiAt B.ψ v) (locCo M.co v γ) φ = _ := fun γ hγ =>
    (eq_of_acts v h₁ (h₀ φ hs) (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v γ (hAt γ hγ) φ)).trans
      (eq_of_acts v h₁ (h₀ φ hs) (hθ γ hγ)).symm
  set θ' := inclR (F := F) (AF F) (θ : E)
  refine eigen dd hB.std {z | ∃ γ₁ ∈ latAtV X W v, ∃ γ₂ ∈ latAtV X W v, z = Matrix.fromCols γ₁ᵀ γ₂ᵀ} ?_ ?_
    (fun z => B.ψ (⅟(2 : AF F) * symp (cA σ) θ' (incM F W.J) (dbl (incM F X.J)) z z)) (sb_box_loc hs (sb_star hs)) ?_ ?_
    (omd g) (hsp.pres g) (hsp.adm g) (actB (cA σ) g) (hsp.impl g) ?_ ?_
  · rintro _ ⟨γ₁, h1, γ₂, h2, rfl⟩ u hu
    ext i (j | j)
    exacts [congrFun (congrFun (hAt _ h1 u hu) j) i, congrFun (congrFun (hAt _ h2 u hu) j) i]
  · intro z hz h
    have ez : z = Matrix.fromCols (z.toCols₁ᵀ)ᵀ (z.toCols₂ᵀ)ᵀ := (Matrix.fromCols_toCols z).symm
    refine ⟨_, _root_.PositivityTheory.ThK.Vac.mem_latAtV_k hB hX hW v (fun u hu => ?_) fun γ hγ => ?_, _, _root_.PositivityTheory.ThK.Vac.mem_latAtV_k hB hX hW v (fun u hu => ?_) fun γ hγ => ?_, ez⟩
    · ext i j; exact congrFun (congrFun (hz u hu) j) (Sum.inl i)
    · have := h _ ⟨γ, hγ, 0, zero_mem _, rfl⟩
      rwa [ez, symp_dbl, symp_zero, sub_zero] at this
    · ext i j; exact congrFun (congrFun (hz u hu) j) (Sum.inr i)
    · have := h _ ⟨0, zero_mem _, -γ, neg_mem hγ, rfl⟩
      rwa [ez, symp_dbl, symp_zero, zero_sub, ← neg_one_smul (AF F) γ, symp_smul, neg_one_mul, neg_neg] at this
  · obtain ⟨x, hx⟩ := Function.ne_iff.1 h0
    exact fun e => mul_ne_zero hx (star_ne_zero.2 hx) (congrFun e (Sum.elim x x))
  · rintro _ ⟨γ₁, h1, γ₂, h2, rfl⟩
    have e : locCo dd v (Matrix.fromCols γ₁ᵀ γ₂ᵀ) = (Sum.elim (locCo M.co v γ₁).1 (locCo M.co v γ₂).1,
        Sum.elim (locCo M.co v γ₁).2 (-(locCo M.co v γ₂).2)) := by
      have := hdd γ₁ᵀ γ₂ᵀ
      rw [hd', hd'] at this
      ext (i | i) <;> simp [locCo, this]
    have a2 : At (evFin F v) (⅟(2 : AF F) * symp (cA σ) θ' (incM F X.J) (incM F W.J) γ₂ γ₂) := fun u hu => by
      rw [smul_eq_mul, mul_left_comm, ← symp_smul, hAt _ h2 u hu, symp_zero, mul_zero]
    rw [e, schr_box hB.std, hv _ h1, hv _ h2, symp_dbl, mul_sub, sub_eq_add_neg, AddChar.map_add_eq_mul, ← star_psi hB.std a2]
    funext x
    simp only [boxFun, Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul']
    ring
  · intro u hu
    have : u * (g.1.1 - 1)ᵀ = 0 := by
      rw [← idem_smul hg, Matrix.transpose_smul, Matrix.mul_smul, ← Matrix.smul_mul]
      change (sg v 1 • u) * _ = 0
      rw [hu, Matrix.zero_mul]
    rwa [Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this
  · rintro _ ⟨γ₁, h1, γ₂, h2, rfl⟩
    obtain ⟨a, ha, b, hb, c, hc, e, he, eg⟩ := hg'
    refine ⟨Matrix.fromCols γ₁ᵀ γ₂ᵀ * ((g⁻¹).1.1)ᵀ, ⟨a * γ₁ + b * γ₂, add_mem (mul_latAtV ha h1) (mul_latAtV hb h2),
      c * γ₁ + e * γ₂, add_mem (mul_latAtV hc h1) (mul_latAtV he h2), ?_⟩, ?_, ?_⟩
    · rw [eg, Matrix.fromBlocks_transpose, Matrix.fromCols_mul_fromBlocks]
      simp only [Matrix.transpose_add, Matrix.transpose_mul]
    · have : g.1.1 * (g⁻¹).1.1 = 1 := g.1.mul_inv
      rw [actB, Matrix.mul_assoc, ← Matrix.transpose_mul, this, Matrix.transpose_one, Matrix.mul_one]
    · rw [symp, symp, hTens_mul (cA σ) _ (g⁻¹).2]
end PositivityTheory.ThKG.Loc.Cone.Vf
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl.Vf2
open scoped Matrix TensorProduct GlobalTheory.VacAny
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.LatVac
open PositivityTheory.ThK PositivityTheory.ThK.Vac PositivityTheory.ThKH.Iwas PositivityTheory.ThKH.Locrep PositivityTheory.ThKG.Loc.Cone.Vf
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {v : Pl F}
theorem _root_.GlobalTheory.ThK.Dbl.vacFix2_k : _root_.GlobalTheory.ThK.Dbl.VacFix2_k := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB hX hW hM χ _ dd omd ⟨d', hd', hdd⟩ ⟨_, hsp, hrule⟩ K hK v hv g hk hg
  have hL := hX.lat
  have vd := hM.vac v
  obtain ⟨hsb, h0, -⟩ := hM.vac v
  obtain ⟨r₀, x₀, h₀, h₁⟩ := exists_base (Fin n × Fin d) v
  set Φ := tens (evFin F v) (M.vac v) r₀ with hΦ
  have hΦs : Φ ∈ schA F _ := (h₀ _ hsb).2
  obtain ⟨y₀, hy⟩ := Function.ne_iff.1 h0
  have hΦy : Φ (putA v x₀ y₀) = M.vac v y₀ := by
    change M.vac v (evA _ v (putA v x₀ y₀)) * r₀ (putA v x₀ y₀) = _
    rw [ev_put (evA_inA v), inv_putA v (h₀ _ hsb).1, h₁, mul_one]
  have hΦ0 : Φ ≠ 0 := fun e => hy (by rw [← hΦy, e]; rfl)
  have q1 : PresD v X g.1.1 := presD_of fun z z' a b => ((hK g).1 hk).2 z z' a b g (.inl rfl)
  have q2 : PresD v X (g⁻¹).1.1 := presD_of fun z z' a b => ((hK g).1 hk).2 z z' a b g⁻¹ (.inr rfl)
  obtain ⟨c, hc⟩ := _root_.PositivityTheory.ThKG.Loc.Cone.Vf.dbl_eigen_k hB hX hW vd hd' hdd hsp.toIsSplitting g hg q2
  suffices h : c = 1 by rwa [h, one_smul] at hc
  obtain ⟨g₁, m₁, g₂, m₂, g₃, m₃, g₄, m₄, eg⟩ := q1
  obtain ⟨a₁, n₁, a₂, n₂, a₃, -, a₄, -, ea⟩ := q2
  have hD : g.1.1 * (diagCols (Fin n) : Matrix _ _ (AE F E)) = Matrix.fromRows (g₁ + g₂) (g₃ + g₄) := by
    rw [eg, diagCols, Matrix.fromBlocks_mul_fromRows]; simp
  have hI : a₁ * (g₁ + g₂) + a₂ * (g₃ + g₄) = 1 := by
    have : (g⁻¹).1.1 * (g.1.1 * (diagCols (Fin n) : Matrix _ _ (AE F E))) = diagCols (Fin n) := by
      rw [← Matrix.mul_assoc, show (g⁻¹).1.1 * g.1.1 = 1 from g.1.inv_mul, Matrix.one_mul]
    rw [hD, ea, Matrix.fromBlocks_mul_fromRows, diagCols] at this
    exact (Matrix.fromRows_inj this).1
  have aD := at_mul_left (M := g.1.1 - 1) hg (diagCols (Fin n) : Matrix _ _ (AE F E))
  rw [Matrix.sub_mul, Matrix.one_mul, hD] at aD
  have ax : At (evFin F v) (g₁ + g₂ - 1) := fun u hu => congrArg Matrix.toRows₁ (aD u hu)
  have ay : At (evFin F v) (g₃ + g₄ - 1) := fun u hu => congrArg Matrix.toRows₂ (aD u hu)
  have px := add_mem m₁ m₂
  have py := add_mem m₃ m₄
  generalize g₁ + g₂ = x at *
  generalize g₃ + g₄ = y at *
  obtain ⟨b, b', t', b1, hb, pb, pt, ht⟩ := _root_.GlobalTheory.ThK.Dbl.Vf2.exists_beta_k hB hX g hD px py n₁ n₂ hI ax ay
  have hm : At (evFin F v) (y - x) := by simpa using at_sub ay ax
  have pm := sub_mem py px
  obtain ⟨s₀, n₀, p, t, ss, eg', es, en, en', hn, hp, et, et'⟩ :=
    Vf2.exists_decomp b1 hb g hD ht (ε := PositivityTheory.ThKG.Loc.Cone.Vf.eps v) eps_mul ((cA σ).commutes _) (eps_smul hm)
  have o1 := one_mem (Pres v X)
  have z0 := zero_mem (Pres v X)
  have pC : PresD v X (CC b) := ⟨_, o1, _, add_mem o1 pb, _, o1, _, pb, rfl⟩
  have pCi : PresD v X (Ci b) := ⟨_, neg_mem pb, _, add_mem o1 pb, _, o1, _, neg_mem o1, rfl⟩
  have c1 : compFin F E v (PositivityTheory.ThKG.Loc.Cone.Vf.eps v : AE F E) = 1 := by rw [PositivityTheory.ThKG.Loc.Cone.Vf.eps, comp_alg, ev_sg]; rfl
  have pe : (PositivityTheory.ThKG.Loc.Cone.Vf.eps v : AE F E) • (1 : Matrix _ _ _) ∈ Pres v X := smul_mem_Pres hL (by rw [c1]; exact one_mem _) o1
  have pe' : (1 - PositivityTheory.ThKG.Loc.Cone.Vf.eps v : AE F E) • (1 : Matrix _ _ _) ∈ Pres v X :=
    smul_mem_Pres hL (by rw [map_sub, map_one, c1, sub_self]; exact zero_mem _) o1
  have bt : boxFun Φ (star Φ) = tens (evFin F v) (boxFun (M.vac v) (star (M.vac v))) (boxFun r₀ (star r₀)) := by
    funext x
    simp only [hΦ, boxFun, tens, Pi.star_apply, star_mul']
    exact mul_mul_mul_comm _ _ _ _
  have hΦd := GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ Φ hΦs _ (star_mem_schA hΦs)
  have hd0 : boxFun Φ (star Φ) ≠ 0 := fun e => lDiag_ne hΦs hΦ0 (by rw [e, map_zero])
  have rd : Rest (evFin F v) (boxFun (M.vac v) (star (M.vac v))) (boxFun r₀ (star r₀)) := by
    refine ⟨fun x z hz => ?_, bt ▸ hΦd⟩
    have i1 := (h₀ _ hsb).1 (x ∘ Sum.inl) (z ∘ Sum.inl) fun u hu => funext fun i => congrFun (hz u hu) _
    have i2 := (h₀ _ hsb).1 (x ∘ Sum.inr) (z ∘ Sum.inr) fun u hu => funext fun i => congrFun (hz u hu) _
    change r₀ (x ∘ Sum.inl + z ∘ Sum.inl) * star (r₀ (x ∘ Sum.inr + z ∘ Sum.inr)) = _
    rw [i1, i2]; rfl
  have ev : ∀ g : UG (cA σ) (dbl (incM F X.J)), At (evFin F v) (g.1.1 - 1) → PresD v X (g⁻¹).1.1 →
      ∃ a : ℂ, omd g (boxFun Φ (star Φ)) = a • boxFun Φ (star Φ) := fun g h1 h2 => by
    obtain ⟨a, ha⟩ := _root_.PositivityTheory.ThKG.Loc.Cone.Vf.dbl_eigen_k hB hX hW vd hd' hdd hsp.toIsSplitting g h1 h2
    exact ⟨a, by rw [bt, ha _ rd, tens_smul]⟩
  obtain ⟨a, ha⟩ := ev s₀ (by
      rw [es]
      refine at_conj (CC_Ci b) fun u hu => ?_
      have : u • (PositivityTheory.ThKG.Loc.Cone.Vf.eps v : AE F E) = 0 := at_eps u hu
      rw [SS, ← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add, Matrix.fromBlocks_smul]
      simp only [sub_smul, one_smul, neg_zero, add_zero, ← sub_eq_add_neg, sub_sub_cancel_left, smul_neg, ← smul_assoc, this,
        zero_smul, Matrix.fromBlocks_zero])
    (by rw [inv_eq_of_mul_eq_one_right ss, es]; exact (pC.mul ⟨_, pe', _, pe, _, pe, _, pe', rfl⟩).mul pCi)
  obtain ⟨a', ha'⟩ := ev n₀ (by
      rw [en]
      refine at_conj (CC_Ci b) fun u hu => ?_
      rw [← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add, Matrix.fromBlocks_smul]
      simp only [add_neg_cancel, neg_zero, add_zero, smul_zero, smul_neg]
      rw [at_mul_left hm t' u hu, neg_zero, Matrix.fromBlocks_zero])
    (by rw [en']; exact (pC.mul ⟨_, o1, _, mul_mem pm pt, _, z0, _, o1, rfl⟩).mul pCi)
  have a1 : a' = 1 := by
    rw [rule_diag hdd hrule n₀ 1 hn (by rw [map_one, map_one]) hΦs hΦ0 ha']
    simp
  have aa : a * a = 1 := by
    have e : omd (s₀ * s₀) (boxFun Φ (star Φ)) = (a * a) • boxFun Φ (star Φ) := by
      rw [map_mul, Module.End.mul_apply, ha, map_smul, ha, smul_smul]
    rw [ss, map_one, Module.End.one_apply] at e
    exact smul_left_injective ℂ hd0 (e.symm.trans (one_smul _ _).symm)
  have e1 : omd g (boxFun Φ (star Φ)) = c • boxFun Φ (star Φ) := by rw [bt, hc _ rd, tens_smul]
  have e2 : omd p (boxFun Φ (star Φ)) = c • boxFun Φ (star Φ) := by
    have e3 : omd (s₀ * n₀ * s₀) (boxFun Φ (star Φ)) = boxFun Φ (star Φ) := by
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ha, map_smul, ha', a1, one_smul, map_smul, ha, smul_smul,
        aa, one_smul]
    have : p = (s₀ * n₀ * s₀)⁻¹ * g := by rw [eg']; group
    rw [this, map_mul, Module.End.mul_apply, e1, map_smul]
    conv_lhs => rw [← e3, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  have hpos := rule_diag hdd hrule p t hp (chi_det hL χ hv t (by rw [et]; exact add_mem py (mul_mem pb pm)) (by rw [et']; exact pt)
    (by rw [et, add_sub_right_comm]; exact at_add ay (at_mul_right _ hm))) hΦs hΦ0 e2
  have n4 := Bad.norm_eig hsp.unit hsp.pres hΦd hd0 e1
  rw [hpos] at n4 ⊢
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)] at n4
  rw [n4, Complex.ofReal_one]
end GlobalTheory.ThK.Dbl.Vf2
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseEisCont
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
theorem eisContinues_of_k (h1 : _root_.GlobalTheory.ThK.Dbl.EisBL_k) (h2 : _root_.GlobalTheory.ThK.Dbl.FrameConj_k) : _root_.GlobalTheory.ThK.Dbl.EisContinues_k := by
  intro F E _ _ _ _ _ σ B n Y r s hB hn hY χ hχ c hc K a hK ha s₁ f hf
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  obtain ⟨b, K₀, p, t, hb, hK₀, hp, hk⟩ := h2 F E σ B n Y r s hB hY K hK
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = absE F E (Matrix.GeneralLinearGroup.det t) := ⟨_, rfl⟩
  have d0 : 0 < d := hd ▸ absE_pos _
  have a0 : ∀ x, 0 < a x := fun x => by
    obtain ⟨q, u, hq, k, hk, rfl⟩ := ha.iwa x
    exact ha.val q u hq k hk ▸ absE_pos _
  have hk' : ∀ k ∈ K₀, p * k * p⁻¹ ∈ K := fun k h => (hk _).2 (by simpa [mul_assoc] using h)
  have ha₀ : IsHgt K₀ fun x => d * a (x * p⁻¹) := by
    refine ⟨fun x => ?_, fun q u hq k h => ?_⟩
    · obtain ⟨q, u, hq, k, h, e⟩ := ha.iwa (x * p⁻¹)
      exact ⟨q * p, _, hq.mul hp, _, (hk k).1 h, by rw [mul_inv_eq_iff_eq_mul.1 e]; group⟩
    · rw [show q * k * p⁻¹ = q * p⁻¹ * (p * k * p⁻¹) by group, ha.val _ _ (hq.mul hp.inv) _ (hk' k h), map_mul, map_mul, map_inv,
        map_inv, NNReal.coe_mul, NNReal.coe_inv, ← hd]
      field_simp
  have hf₀ : IsSec K₀ χ s₁ fun x => f (x * p⁻¹) := by
    refine ⟨hf.cont.comp (continuous_mul_const _), fun q u x hq => by rw [mul_assoc, hf.law q u _ hq], ?_⟩
    haveI := hf.fin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k : K => fun x => f (x * k.1))).map
      (LinearMap.funLeft ℂ ℂ fun x => x * p⁻¹)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨⟨_, hk' k k.2⟩, rfl⟩, funext fun x => by simp [LinearMap.funLeft, mul_assoc]⟩
  obtain ⟨Ê, ⟨t₁, e1, e2⟩, e3⟩ := h1 F E σ B n Y r s hB hn hY χ hχ c hc b K₀ _ hb hK₀ ha₀ s₁ _ hf₀
  have dc : Differentiable ℂ fun z : ℂ => (d : ℂ) ^ (s₁ - z) :=
    (differentiable_id.const_sub s₁).const_cpow (.inl (Complex.ofReal_ne_zero.2 d0.ne'))
  refine (eisCont_of_reg (f := flat a f s₁) (Ê := fun z x => (d : ℂ) ^ (s₁ - z) * Ê z (x * p)) (t := t₁) (fun z hz x => ?_)
    (fun x => dc.differentiableOn.mul (e2 _)) fun s₀ => ?_).imp fun U hU => ⟨_, hU⟩
  · refine (congrArg (HasSum · _) (funext fun q => ?_)).mp ((e1 z hz (x * p)).mul_left ((d : ℂ) ^ (s₁ - z)))
    simp only [eisTerm, flat, ← mul_assoc, mul_inv_cancel_right]
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg d0.le (a0 _).le, ← mul_assoc,
      ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 d0.ne')]
    simp
  · obtain ⟨k, U, H, hU, e4, e5⟩ := e3 s₀
    refine ⟨k, _, (reg_of_weak hU e5).mul one_le_height_GL2 (dc.analyticAt s₀) (continuous_mul_const p) (b := ht2 p) fun x => ?_, ?_⟩
    · rw [mul_comm]; exact_mod_cast heightGL_mul_le F x.1 p.1
    · filter_upwards [mem_nhdsWithin_of_mem_nhds hU, self_mem_nhdsWithin] with z hz hz' x
      rw [e4 z hz hz', mul_left_comm]
end GlobalTheory.ThK.Dbl
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseDblW
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
section Emb
variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {β : Type} [Fintype β] [DecidableEq β]
end Emb
section Member
variable {a b : ℕ} {JA : Matrix (Fin a) (Fin a) E} {JB : Matrix (Fin b) (Fin b) E} {κ : Type} [Fintype κ]
  {d : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (incM F JB)) κ}
  {dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (dbl (incM F JB))) (κ ⊕ κ)} {ψ : AddChar (AF F) ℂ}
  {χ : Chr F E} {om : UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ)}
  {omd : UG (cA σ) (dbl (incM F JB)) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ)}
end Member
theorem dblX_k : _root_.GlobalTheory.ThK.Dbl.DblX_k := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' h
  obtain ⟨hw, ⟨d', ht, hw'⟩, -⟩ := h.weil
  have ht' : ∀ x, M.co.e xᵀ = d'.e x := fun x => (ht xᵀ).symm
  obtain ⟨dd, om₂, S, h1, h2, h3⟩ := dbl_main h.base.std h.base.cm.2.2.1 (by simp [mul_comm]) (skew_det h.skew) (herm_det h.herm)
    h.hX.1 (fun x => by rw [← ht']; exact h.good.rat xᵀ) ht' hw' hw
  refine ⟨dd, om₂, S, _, h1, fun φ hφ φ' hφ' => ⟨box_mem hφ hφ', fun k g g' x hx =>
    ⟨?_, (h3 φ hφ φ' hφ').2 g g' x hx⟩⟩, ⟨d', ht, h2⟩, lD_haar⟩
  have p := h.weil.isUSplitting.pres
  have e : ∀ (g : UA σ X.J) ϕ, om.comp (MonoidHom.inl _ _) g (om.comp (MonoidHom.inr _ _) k ϕ) = om (g, k) ϕ := fun g ϕ => by
    rw [← Module.End.mul_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_mul]; simp
  rw [(h3 φ hφ φ' hφ').1, ← thetaSum_smul, (h3 _ (hw.1.pres k φ hφ) _ (hw.1.pres k φ' hφ')).2 g g' x hx, e, e,
    theta_box (p _ φ hφ) (p _ φ' hφ')]
  rfl
end GlobalTheory.ThK.Dbl
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseNormZeta
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
theorem swFullX_of_k (h1 : _root_.GlobalTheory.ThK.Dbl.SWAnisoX_k) (h2 : _root_.GlobalTheory.ThK.Dbl.EisContinues_k) (h3 : _root_.GlobalTheory.ThK.Dbl.BoxSecX_k) : _root_.GlobalTheory.ThK.Dbl.SWFullX_k := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB hn hd hX hW h0 hM χ hχ hr dd om S l c1 c2 K a hK ha μ D hμ hD Φ₁ p1 Φ₂ p2
  obtain ⟨U, Ê, hE, hR⟩ := h2 F E σ B n X r s hB hn (.inl hX) χ hχ d hr K a hK ha _ _
    (h3 F E σ B n d X W M r s r' s' hB hn hd hX hW h0 hM χ hχ hr dd om S l c1 c2 K a hK ha Φ₁ p1 Φ₂ p2)
  obtain ⟨k, hk⟩ := hR (((d : ℂ) - n) / 2)
  exact ⟨_, _, hE.update hk (h1 F E σ B n d X W M r s r' s' hB hn hd hX hW h0 hM χ hχ hr dd om S l c1 c2 K a hK ha μ D hμ hD Φ₁ p1 Φ₂ p2),
    Set.mem_insert _ _, fun x => by rw [Function.update_self]⟩
end GlobalTheory.ThK.Dbl
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseDense
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace Dense
open GlobalTheory.CompanionTheory.CMAdele
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}
end Dense
theorem polSch_k : _root_.GlobalTheory.ThK.Dbl.PolSch_k := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, -, φ, h1, h2, rfl⟩
  exact Dense.pure_mem f ⟨h1, (h2.and hp.good.std).mono fun v hv => hv.1.trans hv.2⟩
end GlobalTheory.ThK.Dbl
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
namespace UpperTheory.TP
open GlobalTheory.ThK.Dbl
theorem tools_holds_k : _root_.UpperTheory.TP.Tools_k :=
  have p1 := _root_.GlobalTheory.ThK.Dbl.siegelWeilAniso_of_k _root_.PositivityTheory.SiegelWeilFormula.Fin.siegelWeilStd_k _root_.GlobalTheory.ThK.Dbl.frameConj_k _root_.GlobalTheory.ThK.Dbl.finLevel_k _root_.GlobalTheory.ThK.Dbl.stab2Cpt_k
  have l1 := _root_.GlobalTheory.ThK.Dbl.boxSecX_of_k _root_.GlobalTheory.ThK.Dbl.finLevel_k _root_.GlobalTheory.ThK.Dbl.stab2Cpt_k
  have l2 : GlobalTheory.RealLift.LieSecond := PositivityTheory.ThKR.lieSecond2 PositivityTheory.ThKR.localLift_holds PositivityTheory.RL.derEx
  { swFull := _root_.GlobalTheory.ThK.Dbl.swFullX_of_k p1.2 (_root_.GlobalTheory.ThK.Dbl.eisContinues_of_k _root_.PositivityTheory.RgEis.Hd.eisBL_k _root_.GlobalTheory.ThK.Dbl.frameConj_k) l1
    boxSec := l1
    dbl := _root_.GlobalTheory.ThK.Dbl.dblX_k
    stab2 := _root_.GlobalTheory.ThK.Dbl.stab2Cpt_k
    cpt := _root_.GlobalTheory.ThK.Dbl.cptAll_of_k PositivityTheory.ThKEst.grpTop_of _root_.PositivityTheory.ThKEst.epsOf_of_k
      (PositivityTheory.ThKEst.siegelAll_of UpperTheory.Lit.siegelSetUnitary_of_core) PositivityTheory.ThKEst.finVolU PositivityTheory.ThKF.unimodularity_holds
    basic := _root_.PositivityTheory.ThKF0.thetaBasic_k
    polSch := _root_.GlobalTheory.ThK.Dbl.polSch_k
    unfold0 := _root_.GlobalTheory.ThK.Dbl.unfold0_k
    pairEx := _root_.PositivityTheory.ThKG.Tow.pairEx_of_k _root_.PositivityTheory.ThKG.Tow.modelEx_k _root_.PositivityTheory.ThKW.S.weilEx_k
    split := _root_.UpperTheory.TP.splitFree_k
    vacFix := _root_.GlobalTheory.ThK.Dbl.vacFix2_k
    acts := _root_.PositivityTheory.ThKF0.actsEx_k
    lie1 := PositivityTheory.RL.lieFirst l2
    lie2 := l2 }
theorem tLift_holds_k : _root_.UpperTheory.TP.TLift_k := _root_.UpperTheory.TP.tLift_of_tools_k _root_.UpperTheory.TP.tools_holds_k (_root_.GlobalTheory.ThK.Dbl.hgtEx_of_k _root_.GlobalTheory.ThK.Dbl.stab2Cpt_k)
end UpperTheory.TP
end
end

theorem UpperTheory.TP.K.tLiftK : UpperTheory.TP.TLiftK :=
  UpperTheory.TP.tLift_holds_k
