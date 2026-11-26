module

public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.SectionMonomialGenerators

@[expose] public section

section -- merged from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.InnerEuclideanEmbeddingEqAverage
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module ComplexConjugate

namespace Formalism.MainNotions.Gaps.NetNorms

variable {D : D7} {B : WeightFamilies.Prov D} {j : ℕ} {ka : WeightFamilies.Wt D j}

namespace NetData

variable (Nt : NetData B j ka)

theorem inner_euclideanEmbedding_eq_average (σ : B.KO →+* ℂ) (F G : B.Cusp j ka) :
    inner ℂ (Nt.e0 σ F) (Nt.e0 σ G) =
      (((Fintype.card (Nt.NN σ) : ℝ)⁻¹ : ℝ) : ℂ) * ∑ y, conj (Nt.ev σ y F) * Nt.ev σ y G := by
  classical
  rw [PiLp.inner_apply, Fintype.sum_sigma, Finset.sum_eq_single σ]
  · have hc : (((Fintype.card (Nt.NN σ) : ℝ)⁻¹ : ℝ) : ℂ) = ((Nt.cf σ : ℝ) : ℂ) * ((Nt.cf σ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Nt.cf_sq]
    rw [hc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [Nt.goodRowsProjector_apply_eq_sum, if_true, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
    ring
  · intro τ _ h
    simp [Nt.goodRowsProjector_apply_eq_sum, h]
  · simp

def herm : Formalism.MainNotions.Gaps.SizeBoundsAlt.Herm (fun σ => Nt.netN σ) (Fintype.card (Σ τ : B.KO →+* ℂ, Nt.NN τ)) where
  e σ := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Fintype.equivFin (Σ τ : B.KO →+* ℂ, Nt.NN τ))).toLinearEquiv.toLinearMap.comp
    (Nt.e0 σ)
  norm_e σ F := by
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
      LinearIsometryEquiv.norm_map, Nt.norm_euclideanEmbedding_eq_netNorm]

theorem herm_inner (σ : B.KO →+* ℂ) (F G : B.Cusp j ka) :
    inner ℂ (Nt.herm.e σ F) (Nt.herm.e σ G) = inner ℂ (Nt.e0 σ F) (Nt.e0 σ G) := by
  simp only [herm, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
    LinearIsometryEquiv.inner_map_map]

theorem herm_conj : Nt.herm.Conj := by
  intro σ f g
  rw [Nt.herm_inner, Nt.herm_inner, Nt.inner_euclideanEmbedding_eq_average, Nt.inner_euclideanEmbedding_eq_average]
  rw [← Fintype.card_congr (Nt.cj σ), ← (Nt.cj σ).sum_comp]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Nt.ev_conj, Complex.conj_conj, star_mul', Complex.star_def, Complex.conj_ofReal, map_sum, map_mul]

end NetData

theorem sup_L2_bound_of_net : SupL2BoundFromNet (D := D) (B := B) (j := j) (ka := ka) := by
  intro Nt hM hL large₂ CG AG hP F σ
  rw [Nt.Bp_L2N_run hM hL]
  change B.supN j ka σ F ^ 2 ≤ _ * Nt.netN σ F ^ 2
  obtain ⟨y, hy⟩ := hM σ F
  have hS := B.supN_nonneg j ka σ F
  have hn : (1 : ℝ) ≤ (Fintype.card (Nt.NN σ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Fintype.card_pos_iff.mpr ⟨y⟩).ne'
  have hsum0 : (0 : ℝ) ≤ ∑ y, ‖Nt.ev σ y F‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsq : Nt.netN σ F ^ 2 = (Fintype.card (Nt.NN σ) : ℝ)⁻¹ * ∑ y, ‖Nt.ev σ y F‖ ^ 2 :=
    Real.sq_sqrt (mul_nonneg (inv_nonneg.mpr (by linarith)) hsum0)
  have h1 : ‖Nt.ev σ y F‖ ^ 2 ≤ ∑ y, ‖Nt.ev σ y F‖ ^ 2 :=
    Finset.single_le_sum (f := fun y => ‖Nt.ev σ y F‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ y)
  have h2 : (B.supN j ka σ F / 4) ^ 2 ≤ ‖Nt.ev σ y F‖ ^ 2 := pow_le_pow_left₀ (by positivity) hy 2
  have h3 : B.supN j ka σ F ^ 2 ≤ 16 * (Fintype.card (Nt.NN σ) : ℝ) * Nt.netN σ F ^ 2 := by
    rw [hsq]
    have : 16 * (Fintype.card (Nt.NN σ) : ℝ) * ((Fintype.card (Nt.NN σ) : ℝ)⁻¹ * ∑ y, ‖Nt.ev σ y F‖ ^ 2) =
        16 * ∑ y, ‖Nt.ev σ y F‖ ^ 2 := by
      field_simp
    rw [this]
    have h4 : (B.supN j ka σ F / 4) ^ 2 = B.supN j ka σ F ^ 2 / 16 := by ring
    linarith
  have h4 : 16 * (Fintype.card (Nt.NN σ) : ℝ) ≤ Real.exp (WeightFamilies.PPv D large₂ CG AG * (1 + Real.log ka.size)) := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < 16 * (Fintype.card (Nt.NN σ) : ℝ))]
    exact Real.exp_le_exp.mpr (hP σ)
  calc B.supN j ka σ F ^ 2 ≤ 16 * (Fintype.card (Nt.NN σ) : ℝ) * Nt.netN σ F ^ 2 := h3
    _ ≤ Real.exp (WeightFamilies.PPv D large₂ CG AG * (1 + Real.log ka.size)) * Nt.netN σ F ^ 2 :=
      mul_le_mul_of_nonneg_right h4 (sq_nonneg _)

theorem deepHermNet : DeepHermNetSt (D := D) (B := B) (j := j) (ka := ka) := by
  intro P Nt hM hL X
  exact ⟨_, { e := Nt.herm.e, norm_e := fun σ F => (Nt.herm.norm_e σ F).trans (by rw [Nt.Bp_L2N_run hM hL]) },
    Nt.herm_conj⟩

theorem deepLogDNet : DeepLogDNetSt (D := D) (B := B) (j := j) (ka := ka) := by
  intro P Nt hM hL X σ Pd hI hP
  change Real.log (finrank B.KO (B.Cusp j ka) : ℝ) ≤ Pd
  have hd : finrank B.KO (B.Cusp j ka) ≤ Fintype.card (Nt.NN σ) := by
    have hb := hI _ _ (Module.finBasis B.KO (B.Cusp j ka)).linearIndependent
    have := hb.fintype_card_le_finrank
    simpa [Module.finrank_fintype_fun_eq_card] using this
  have hlog0 : 0 ≤ Real.log (Fintype.card (Nt.NN σ) : ℝ) := Real.log_natCast_nonneg _
  rcases Nat.eq_zero_or_pos (finrank B.KO (B.Cusp j ka)) with h0 | h0
  · rw [h0]
    simp only [Nat.cast_zero, Real.log_zero]
    linarith
  · calc Real.log (finrank B.KO (B.Cusp j ka) : ℝ) ≤ Real.log (Fintype.card (Nt.NN σ) : ℝ) :=
          Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hd)
      _ ≤ Pd := hP

end Formalism.MainNotions.Gaps.NetNorms
end
end

section -- merged from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroSplitOfLocalAndSum
section -- merged from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfLocalAndSum
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D}

theorem concl_of_nat {j : ℕ} (X : PJ D B P j) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ)
    (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (β : ℝ) (r : HeightOneSpectrum (𝓞 B.KO) → ℝ)
    (hnu : ∀ la, 0 ≤ nus la) (hr0 : ∀ la, 0 ≤ r la) (hrs : Summable (fun la => r la * X.lN la))
    (hrb : (∑' la, r la * X.lN la) ≤ β)
    (hloc : ∀ la (e : ℕ), (T : ℝ) * nus la ≤ (e : ℝ) →
      ∀ V' : Submodule (X.Kl la) (X.Vl la), V' ≤ X.locK la (X.Msup ka) →
        X.qlen la (X.loc la (X.Msup ka) ⊓ X.ofK la V') (X.loc la (X.Theta S ka wL wF T) ⊓ X.ofK la V') ≠ ⊤ ∧
        ((X.qlen la (X.loc la (X.Msup ka) ⊓ X.ofK la V')
            (X.loc la (X.Theta S ka wL wF T) ⊓ X.ofK la V')).toNat : ℝ) ≤
          (e : ℝ) * (Module.finrank (X.Kl la) V' : ℝ) + r la) :
    Concl X S ka wL wF T nus β := by
  unfold Concl
  refine ⟨r, hr0, hrs, hrb, ?_⟩
  intro la e he V' hV'
  have hT : (0 : ℝ) ≤ (T : ℝ) * nus la := mul_nonneg (Nat.cast_nonneg _) (hnu la)
  have he0 : (0 : ℤ) ≤ e := by
    have h := hT.trans he
    exact_mod_cast h
  lift e to ℕ using he0 with n
  have h := hloc la n (by exact_mod_cast he) V' hV'
  simpa only [Int.cast_natCast] using h

end Formalism.MainNotions.Gaps.EtaleWeightGaps
end
end

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D}

section J

variable {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

variable {G : GlobalFamilyData X ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)}

theorem vEt_nonneg_comb {S : Scal B} {c : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ} (hB : CombBound G S c nus)
    (Q : LocalPointData G la) (ζ : PtsG G la) : 0 ≤ vEt Q ζ := by
  unfold vEt
  split_ifs with hj
  · exact div_nonneg (EReal.toReal_nonneg ((hB la (Q.y ζ)).1 hj).1) (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
  · exact le_rfl

theorem nu_le_comb {S : Scal B} {c : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ} (hB : CombBound G S c nus)
    (Q : LocalPointData G la) (hTie : Q.InTie S) (ζ : PtsG G la) : Q.nu S ζ ≤ nus la + max 0 c * vEt Q ζ := by
  have hv := vEt_nonneg_comb hB Q ζ
  have hm : c * vEt Q ζ ≤ max 0 c * vEt Q ζ := mul_le_mul_of_nonneg_right (le_max_right _ _) hv
  by_cases hj : j < D.R.m
  · have h1 := ((hB la (Q.y ζ)).1 hj).2 ((hTie ζ).2.2.1 hj)
    rw [← EReal.coe_toReal (hTie ζ).1 (hTie ζ).2.1, EReal.coe_le_coe_iff] at h1
    have h2 : c / (2 * (G.iet : ℝ)) * (X.vAt la (Q.y ζ) (X.inc _ G.et)).toReal = c * vEt Q ζ := by
      unfold vEt
      rw [if_pos hj]
      ring
    rw [h2] at h1
    unfold LocalPointData.nu
    linarith
  · have h1 := (hB la (Q.y ζ)).2 (not_lt.1 hj)
    rw [← EReal.coe_toReal (hTie ζ).1 (hTie ζ).2.1, EReal.coe_le_coe_iff] at h1
    have h2 : 0 ≤ max 0 c * vEt Q ζ := mul_nonneg (le_max_left _ _) hv
    unfold LocalPointData.nu
    linarith

theorem Net_nonneg_comb {S : Scal B} {c : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ} (hB : CombBound G S c nus)
    (hj : j < D.R.m) (Q : LocalPointData G la) : 0 ≤ Q.Net := by
  unfold LocalPointData.Net
  exact finsum_nonneg fun ζ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (EReal.toReal_nonneg ((hB la (Q.y ζ)).1 hj).1)

theorem rLa_nonneg_comb {S : Scal B} {c' : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ} (hB : CombBound G S c' nus)
    (Q : LocalPointData G la) (CRm : ℝ) (T : ℕ) (c : ℝ) : 0 ≤ rLa Q CRm T c := by
  unfold rLa
  have h1 : (0 : ℝ) ≤ (if j < D.R.m then (T : ℝ) * (max 0 c / (2 * (G.iet : ℝ))) * Q.Net else 0) := by
    split_ifs with hj
    · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (div_nonneg (le_max_left _ _)
        (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))) (Net_nonneg_comb hB hj Q)
    · exact le_rfl
  have h2 : (0 : ℝ) ≤ (Q.Ila.toNat : ℝ) := Nat.cast_nonneg _
  exact add_nonneg (add_nonneg (mul_nonneg (Nat.cast_nonneg _) (add_nonneg h2 h1)) (Nat.cast_nonneg _))
    (Nat.cast_nonneg _)

theorem theta_le_msup_of_hypC {large₂ : SizeData₂ D} (X : PJ D B P j) {H : KHyp} {C2 A2 CR Bx CT : ℝ} (S : Scal B)
    {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ} {h0 : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ}
    (h : HypC large₂ X H C2 A2 CR Bx CT S ka wL wF T nP nW h0 nus) : X.Theta S ka wL wF T ≤ X.Msup ka :=
  Formalism.MainNotions.Gaps.T0.theta_le_msup_of_setC X S h.2.2.2.2.1 h.2.1

theorem span_Thc_of_hypC {large₂ : SizeData₂ D} {X : PJ D B P j} {H : KHyp} {C2 A2 CR Bx CT : ℝ} {S : Scal B}
    {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ} {h0 : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ}
    (hH : HypC large₂ X H C2 A2 CR Bx CT S ka wL wF T nP nW h0 nus) :
    Submodule.span B.KO (X.Thc S.sF wF : Set (B.Cusp j wF)) = ⊤ ∧
    Submodule.span B.KO (X.Thc S.s0 (X.wF0 wL wF) : Set (B.Cusp j (X.wF0 wL wF))) = ⊤ ∧
    Submodule.span B.KO (X.Thc S.sK ka : Set (B.Cusp j ka)) = ⊤ := by
  obtain ⟨-, -, ⟨-, -, -, -, -, po, -, -, PLam, -, -, hF, h0', hK⟩, -⟩ := hH
  exact ⟨span_eq_top_of_shortG hF, span_eq_top_of_shortG h0', span_eq_top_of_shortG hK⟩

end J

def LocalC (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) : Prop :=
  ∀ (large₂ : SizeData₂ D) (X : Prov D B P) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ),
    ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ)
      (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ),
    HypC large₂ (X j h1 h2) H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus →
    LatAt B j ka → SupBoundByL2AtWeight large₂ B j ka K.CG K.AG → LAMwAt large₂ B j ka K.CL K.AL →
    (j < D.R.m → QAt large₂ B j ka K.CRm H.CK Ch Ah Cq Aq T (cc D large₂ C2 A2 CR wL)) →
    ∀ (G : GlobalFamilyData (X j h1 h2) ka wL wF) (Gc PH Prw Pet Pd : ℝ),
    G.TiedW S Gc Prw → G.TiedTh S Gc → G.TiedZ S T Gc →
    G.TiedQ large₂ S K.CRm T (cc D large₂ C2 A2 CR wL) Ch Ah → G.TiedEt large₂ K.Cf K.Af →
    DeepHerm (X j h1 h2) ka → DeepSubMul (X j h1 h2) → DeepLogD (X j h1 h2) ka Pd →
    PageGd (X j h1 h2) ka large₂ K.CG K.AG Pd →
    ShareRd (D := D) (j := j) T G.del ((X j h1 h2).rk ka (B.Mlat j ka)) →
    ShareRho (D := D) (j := j) T G.rz ((X j h1 h2).rk ka (B.Mlat j ka)) →
    ShareRhoP (D := D) (j := j) T G.rq ((X j h1 h2).rk ka (B.Mlat j ka)) →
    PolyDom (j := j) D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka →
    CombBound G S (cc D large₂ C2 A2 CR wL) nus →
    ∀ (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la),
    InBasis G la → Q.InCurve → Q.InTie S → Q.InLift T → InContainZ G la S T → InContainM G la K.CRm T (cc D large₂ C2 A2 CR wL) →
    Q.Ila ≠ ⊤ →
    ∀ e : ℕ, (T : ℝ) * nus la ≤ (e : ℝ) →
    ∀ V' : Submodule ((X j h1 h2).Kl la) ((X j h1 h2).Vl la), V' ≤ (X j h1 h2).locK la ((X j h1 h2).Msup ka) →
      (X j h1 h2).qlen la ((X j h1 h2).loc la ((X j h1 h2).Msup ka) ⊓ (X j h1 h2).ofK la V')
        ((X j h1 h2).loc la ((X j h1 h2).Theta S ka wL wF T) ⊓ (X j h1 h2).ofK la V') ≠ ⊤ ∧
      (((X j h1 h2).qlen la ((X j h1 h2).loc la ((X j h1 h2).Msup ka) ⊓ (X j h1 h2).ofK la V')
          ((X j h1 h2).loc la ((X j h1 h2).Theta S ka wL wF T) ⊓ (X j h1 h2).ofK la V')).toNat : ℝ) ≤
        (e : ℝ) * (Module.finrank ((X j h1 h2).Kl la) V' : ℝ) + rLa Q K.CRm T (cc D large₂ C2 A2 CR wL)

def SumC (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) : Prop :=
  ∀ (large₂ : SizeData₂ D) (X : Prov D B P) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ),
    ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ)
      (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ),
    HypC large₂ (X j h1 h2) H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus →
    LatAt B j ka → SupBoundByL2AtWeight large₂ B j ka K.CG K.AG → LAMwAt large₂ B j ka K.CL K.AL →
    (j < D.R.m → QAt large₂ B j ka K.CRm H.CK Ch Ah Cq Aq T (cc D large₂ C2 A2 CR wL)) →
    ∀ (G : GlobalFamilyData (X j h1 h2) ka wL wF) (Gc PH Prw Pet Pd : ℝ),
    G.TiedW S Gc Prw → G.TiedTh S Gc → G.TiedZ S T Gc →
    G.TiedQ large₂ S K.CRm T (cc D large₂ C2 A2 CR wL) Ch Ah → G.TiedEt large₂ K.Cf K.Af →
    DeepHerm (X j h1 h2) ka → DeepSubMul (X j h1 h2) → DeepLogD (X j h1 h2) ka Pd →
    PageGd (X j h1 h2) ka large₂ K.CG K.AG Pd →
    ShareRd (D := D) (j := j) T G.del ((X j h1 h2).rk ka (B.Mlat j ka)) →
    ShareRho (D := D) (j := j) T G.rz ((X j h1 h2).rk ka (B.Mlat j ka)) →
    ShareRhoP (D := D) (j := j) T G.rq ((X j h1 h2).rk ka (B.Mlat j ka)) →
    PolyDom (j := j) D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka →
    CombBound G S (cc D large₂ C2 A2 CR wL) nus →
    ∀ Qf : ∀ la, LocalPointData G la, Heights Qf Gc PH Prw Pet →
    Summable (fun la => rLa (Qf la) K.CRm T (cc D large₂ C2 A2 CR wL) * (X j h1 h2).lN la) ∧
    (∑' la, rLa (Qf la) K.CRm T (cc D large₂ C2 A2 CR wL) * (X j h1 h2).lN la) ≤
      (X j h1 h2).rk ka (B.Mlat j ka) * D.R.f * D.R.m * large₂.sc.b * large₂.de2

theorem theorem_zero_split_of_local_and_sum (hL : LocalC D B P) (hS : SumC D B P) : Conclusion1OfComb (D := D) (B := B) (P := P) := by
  intro large₂ X K H Ch Ah Cq Aq C2 A2 CR CT j h1 h2 S ka wL wF T nP nW h0 nus hH lA sA mA qA G Gc PH Prw Pet Pd Qf
    tW tTh tZ tQ tEt dH dS dL pG sRd sRho sRhoP hP iB iC iT iLf iZ iM hB hHt
  obtain ⟨hrs, hrb⟩ := hS large₂ X K H Ch Ah Cq Aq C2 A2 CR CT j h1 h2 S ka wL wF T nP nW h0 nus hH lA sA mA qA
    G Gc PH Prw Pet Pd tW tTh tZ tQ tEt dH dS dL pG sRd sRho sRhoP hP hB Qf hHt
  exact concl_of_nat (X j h1 h2) S ka wL wF T nus _ (fun la => rLa (Qf la) K.CRm T (cc D large₂ C2 A2 CR wL))
    hH.2.2.2.1.1 (fun la => rLa_nonneg_comb hB (Qf la) _ _ _) hrs hrb
    (fun la e he V' hV => hL large₂ X K H Ch Ah Cq Aq C2 A2 CR CT j h1 h2 S ka wL wF T nP nW h0 nus hH lA sA mA qA
      G Gc PH Prw Pet Pd tW tTh tZ tQ tEt dH dS dL pG sRd sRho sRhoP hP hB la (Qf la) (iB la) (iC la) (iT la)
      (iLf la tW (iC la) (iT la)) (iZ la) (iM la) (hHt.1 la) e he V' hV)

end Formalism.MainNotions.Gaps.EtaleWeightGaps
end
end

section -- merged from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.IntegralFormsEqSpan
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module TensorProduct

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

theorem comap_span_of_subset {R S M : Type*} [CommRing R] [CommRing S] [AddCommGroup M] [Module S M] [Module R M] [SMul R S]
    [IsScalarTower R S M] (p : Submodule S M) (s : Set M) (hs : s ⊆ p) :
    (Submodule.span R s).comap (p.subtype.restrictScalars R) = Submodule.span R ((↑) ⁻¹' s : Set ↥p) := by
  apply Submodule.map_injective_of_injective (f := p.subtype.restrictScalars R) Subtype.val_injective
  rw [Submodule.map_comap_eq, Submodule.map_span]
  have h : (p.subtype.restrictScalars R) '' ((↑) ⁻¹' s : Set ↥p) = s := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hx; exact ⟨⟨x, hs hx⟩, hx, rfl⟩
  rw [h, inf_eq_right, Submodule.span_le]
  intro x hx
  exact ⟨⟨x, hs hx⟩, rfl⟩

theorem mem_span_subtype_iff {R S M : Type*} [CommRing R] [CommRing S] [AddCommGroup M] [Module S M] [Module R M] [SMul R S]
    [IsScalarTower R S M] (p : Submodule S M) (s : Set ↥p) (x : ↥p) :
    x ∈ Submodule.span R s ↔ (x : M) ∈ Submodule.span R ((↑) '' s : Set M) := by
  have h : Submodule.span R ((↑) '' s : Set M) = (Submodule.span R s).map (p.subtype.restrictScalars R) := by
    rw [Submodule.map_span]; rfl
  rw [h]
  constructor
  · intro hx; exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    exact this ▸ hy

theorem isBaseChange_span {K K' V : Type*} [Field K] [Field K'] [Algebra K K'] [AddCommGroup V] [Module K V]
    (W : Submodule K V) (p : Submodule K' (K' ⊗[K] V))
    (hp : p = Submodule.span K' ((fun v => (1 : K') ⊗ₜ[K] v) '' (W : Set V)))
    (f : ↥W →ₗ[K] ↥p) (hf : ∀ w, (f w : K' ⊗[K] V) = (1 : K') ⊗ₜ[K] (w : V)) : IsBaseChange K' f := by
  have hg : ∀ x : K' ⊗[K] ↥W, ((f.liftBaseChange K' x : ↥p) : K' ⊗[K] V) = W.subtype.baseChange K' x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s w =>
      rw [LinearMap.liftBaseChange_tmul, LinearMap.baseChange_tmul, Submodule.coe_smul, hf, TensorProduct.smul_tmul',
        smul_eq_mul, mul_one]
      rfl
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), Submodule.coe_add, hx, hy]
  have hbij : Function.Bijective (f.liftBaseChange K') := by
    constructor
    · intro x y hxy
      have h1 : W.subtype.baseChange K' x = W.subtype.baseChange K' y := by rw [← hg, ← hg, hxy]
      exact Module.Flat.lTensor_preserves_injective_linearMap (M := K') W.subtype Subtype.val_injective h1
    · rw [← LinearMap.range_eq_top, eq_top_iff]
      rintro ⟨y, hy⟩ -
      have hy' := hy
      rw [hp] at hy'
      induction hy' using Submodule.span_induction with
      | mem y h =>
        obtain ⟨w, hw, rfl⟩ := h
        refine ⟨(1 : K') ⊗ₜ[K] (⟨w, hw⟩ : ↥W), Subtype.ext ?_⟩
        rw [LinearMap.liftBaseChange_tmul, one_smul, hf]
      | zero => exact (LinearMap.range (f.liftBaseChange K')).zero_mem
      | add a b ha hb iha ihb =>
        exact (LinearMap.range (f.liftBaseChange K')).add_mem (iha (hp ▸ ha)) (ihb (hp ▸ hb))
      | smul r a ha ih => exact (LinearMap.range (f.liftBaseChange K')).smul_mem r (ih (hp ▸ ha))
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective (f.liftBaseChange K') hbij) (fun x => by simp)

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

variable (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (ka : WeightFamilies.Wt D j)

def embV (F : B.Cusp j ka) : ↥(Vw X la N ka) := ⟨emb X la N (X.inc ka F), emb_mem_Vw X la N ka F⟩

theorem inW_loc_eq_span (M : Submodule (𝓞 B.KO) X.Forms) (hM : M ≤ X.Msup ka) :
    T0.inW X ka la (X.loc la M) =
      Submodule.span (X.Ol la) {x : ↥(T0.WL X ka la) | ∃ F ∈ M, (x : X.Vl la) = X.bc la F} := by
  unfold T0.inW PJ.loc
  rw [comap_span_of_subset (R := X.Ol la) (T0.WL X ka la) (X.bc la '' (M : Set X.Forms))]
  · congr 1
    ext x
    constructor
    · rintro ⟨F, hF, h⟩; exact ⟨F, hF, h.symm⟩
    · rintro ⟨F, hF, h⟩; exact ⟨F, hF, h.symm⟩
  · rintro _ ⟨F, hF, rfl⟩
    exact Submodule.subset_span ⟨F, hM hF, rfl⟩

theorem span_jW_inW (M : Submodule (𝓞 B.KO) X.Forms) (hM : M ≤ X.Msup ka) :
    Submodule.span (Op X la N) (jW X la N ka '' (T0.inW X ka la (X.loc la M) : Set ↥(T0.WL X ka la))) =
      Submodule.span (Op X la N) {f : ↥(Vw X la N ka) | ∃ F ∈ M, (f : Rp X la N) = emb X la N F} := by
  rw [inW_loc_eq_span X la ka M hM]
  have h1 : jW X la N ka '' (Submodule.span (X.Ol la) {x : ↥(T0.WL X ka la) | ∃ F ∈ M, (x : X.Vl la) = X.bc la F} :
      Set ↥(T0.WL X ka la)) =
      ((Submodule.span (X.Ol la) {x : ↥(T0.WL X ka la) | ∃ F ∈ M, (x : X.Vl la) = X.bc la F}).map
        ((jW X la N ka).restrictScalars (X.Ol la)) : Set ↥(Vw X la N ka)) := rfl
  rw [h1, Submodule.map_span, Submodule.span_span_of_tower]
  congr 1
  ext f
  constructor
  · rintro ⟨x, ⟨F, hF, hx⟩, rfl⟩
    refine ⟨F, hF, ?_⟩
    show bcV X la N (x : X.Vl la) = _
    rw [hx, emb_eq_bcV]
  · rintro ⟨F, hF, hf⟩
    refine ⟨⟨X.bc la F, Submodule.subset_span ⟨F, hM hF, rfl⟩⟩, ⟨F, hF, rfl⟩, Subtype.ext ?_⟩
    rw [hf, emb_eq_bcV]
    rfl

theorem integralForms_eq_span : M1 X la N ka = Submodule.span (Op X la N) (Set.range fun F : B.Mlat j ka => embV X la N ka F) := by
  unfold M1 T0.MW
  rw [span_jW_inW X la N ka _ le_rfl]
  congr 1
  ext f
  constructor
  · rintro ⟨_, ⟨F, hF, rfl⟩, hf⟩
    exact ⟨⟨F, hF⟩, Subtype.ext hf.symm⟩
  · rintro ⟨F, rfl⟩
    exact ⟨_, ⟨F, F.2, rfl⟩, rfl⟩

theorem Th1_eq (S : Scal B) (wL wF : WeightFamilies.Wt D j) (T : ℕ) (h : X.Theta S ka wL wF T ≤ X.Msup ka) :
    Th1 X la N ka S wL wF T = Submodule.span (Op X la N)
      {f : ↥(Vw X la N ka) | ∃ F ∈ X.Theta S ka wL wF T, (f : Rp X la N) = emb X la N F} :=
  span_jW_inW X la N ka _ h

theorem jW_isBaseChange (hM : Submodule.span B.KO (B.Mlat j ka : Set (B.Cusp j ka)) = ⊤) :
    IsBaseChange (Kp X la N) (jW X la N ka) := by
  have hp : Vw X la N ka = Submodule.span (Kp X la N) ((fun v => bcV X la N v) '' (T0.WL X ka la : Set (X.Vl la))) := by
    refine le_antisymm ?_ ?_
    · rw [Vw_eq_span_image X la N ka hM]
      refine Submodule.span_mono ?_
      rintro _ ⟨F, hF, rfl⟩
      exact ⟨X.bc la (X.inc ka F), Submodule.subset_span ⟨X.inc ka F, ⟨F, hF, rfl⟩, rfl⟩, rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      exact bcV_mem_Vw X la N ka hx
  exact isBaseChange_span (K := X.Kl la) (K' := Kp X la N) (V := X.Vl la) (T0.WL X ka la) (Vw X la N ka) hp
    (jW X la N ka) (fun w => rfl)

end Formalism.MainNotions.Gaps.EtaleWeightGaps
end
end
