module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.Descend
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.VecClose
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentInFibreIffOfIsPullback
public import GroundTheory.LocalFields.Uniqueness

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinScalingLaw
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinScalingLaw
noncomputable section

open Filter Topology PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgEisScale

variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

lemma ht_rep {Γ K P : Subgroup G} {l : G → ℝ} (hl : IsHt Γ K ⊤ l) (q : Cos P Γ) (g : G) :
    l (rep q * g) = l g := by
  have hq : rep q ∈ Γ := (Quotient.out q).2
  rw [hl.left _ (Subgroup.mem_top _), hl.rat _ hq (Subgroup.mem_top _), zero_add]

lemma eis_twist {Γ K P : Subgroup G} {l : G → ℝ} (hl : IsHt Γ K ⊤ l) (c : G → ℂ)
    (ρ : K →* (W →L[ℂ] W)) (Λ Λ' : G → ℂ) (t : ℂ) (h : ∀ x, Λ' x = Λ x + t * l x) (g : G) (w : W) :
    eis Γ K P c ρ Λ' g w = Complex.exp (t * l g) • eis Γ K P c ρ Λ g w := by
  unfold eis
  rw [← tsum_const_smul'']
  refine tsum_congr fun q => ?_
  rw [h, ht_rep hl, Complex.exp_add, smul_smul, mul_comm]

lemma conv_twist {Γ K P : Subgroup G} {l : G → ℝ} (hl : IsHt Γ K ⊤ l) {f f' : G → ℝ} (t : ℝ)
    (h : ∀ x, f' x = f x + t * l x) (hc : Conv Γ P f) : Conv Γ P f' := by
  intro g
  refine ((hc g).mul_right (Real.exp (t * l g))).congr fun q => ?_
  rw [h, ht_rep hl, Real.exp_add]

theorem wall_scale [IsTopologicalGroup G] {K Γ P P' : Subgroup G} {ρ : K →* (W →L[ℂ] W)} {c : G → ℂ}
    {η η' β l : G → ℝ} {s : ℝ} (hs : 0 < s) (hl : IsHt Γ K ⊤ l) {R : ℝ} {D : ℂ → ℂ}
    {Op : ℂ → (secSp K P c ρ →L[ℂ] secSp K P' c ρ)} {H : ℂ → G → (secSp K P c ρ →L[ℂ] W)}
    (hw : Wall Γ K P P' c η η' β ρ (secSp K P c ρ) R D Op H) :
    Wall Γ K P P' c (fun g => s * (η g + l g)) (fun g => s * (η' g - l g)) β ρ (secSp K P c ρ) (R / s)
      (fun z => D (s * z)) (fun z => Op (s * z))
      (fun z g => Complex.exp (s * z * l g) • H (s * z) g) := by
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hre : ∀ z : ℂ, ((s : ℂ) * z).re = s * z.re := fun z => by simp
  have hσ : Differentiable ℂ (fun z : ℂ => (s : ℂ) * z) := by fun_prop
  have hgtx : ∀ x : ℝ, R / s < x → R < s * x := fun x hx => by
    rwa [div_lt_iff₀' hs] at hx
  have hltx : ∀ x : ℝ, x < -(R / s) → s * x < -R := fun x hx => by
    have h1 := mul_lt_mul_of_pos_left hx hs
    have h2 : s * -(R / s) = -R := by field_simp
    linarith
  have hlec : ∀ {x : ℝ} {z : ℂ}, x ≤ z.re → s * x ≤ ((s : ℂ) * z).re := fun h => by
    rw [hre]; exact mul_le_mul_of_nonneg_left h hs.le
  have hlec' : ∀ {y : ℝ} {z : ℂ}, z.re ≤ y → ((s : ℂ) * z).re ≤ s * y := fun h => by
    rw [hre]; exact mul_le_mul_of_nonneg_left h hs.le
  have hlc : Continuous fun g => (l g : ℂ) := Complex.continuous_ofReal.comp hl.cont
  refine
    { le := hw.le
      pos := div_nonneg hw.pos hs.le
      convR := fun x hx => ?_
      convL := fun x hx => ?_
      dEnt := ⟨hw.dEnt.1.comp hσ, fun b a => ?_⟩
      dNe := ?_
      op := ⟨?_, fun b a ha => ?_⟩
      hol := fun g => ?_
      cont := ?_
      bdd := fun b a g => ?_
      eqR := fun z hz g w => ?_
      eqL := fun z hz g w => ?_ }
  · exact conv_twist hl (s * x) (fun y => by ring) (hw.convR (s * x) (hgtx x hx))
  · exact conv_twist hl (s * x) (fun y => by ring) (hw.convL (s * x) (hltx x hx))
  · obtain ⟨M, hM⟩ := hw.dEnt.2 (s * b) (s * a)
    exact ⟨M, fun z h1 h2 => hM _ (hlec h1) (hlec' h2)⟩
  · obtain ⟨z, hz⟩ := hw.dNe
    refine ⟨z / s, ?_⟩
    have : (s : ℂ) * (z / s) = z := by field_simp
    simpa [this] using hz
  · refine hw.op.1.comp hσ.differentiableOn fun z hz => ?_
    have hz' : z.re < -(R / s) := hz
    show ((s : ℂ) * z).re < -R
    rw [hre]; exact hltx _ hz'
  · obtain ⟨M, hM⟩ := hw.op.2 (s * b) (s * a) (hltx a ha)
    exact ⟨M, fun z h1 h2 => hM _ (hlec h1) (hlec' h2)⟩
  · have h1 : Differentiable ℂ fun z : ℂ => Complex.exp (s * z * l g) := by fun_prop
    exact h1.smul ((hw.hol g).comp hσ)
  · have h1 : Continuous fun y : ℂ × G => Complex.exp (s * y.1 * l y.2) :=
      ((continuous_const.mul continuous_fst).mul (hlc.comp continuous_snd)).cexp
    have h2 : Continuous fun y : ℂ × G => H (s * y.1) y.2 :=
      hw.cont.comp (f := fun y : ℂ × G => ((s : ℂ) * y.1, y.2)) (by fun_prop)
    exact h1.smul h2
  · obtain ⟨U, hU, M, hM⟩ := hw.bdd (s * b) (s * a) g
    have hV : {g' | |l g'| < |l g| + 1} ∈ 𝓝 g :=
      (isOpen_lt (continuous_abs.comp hl.cont) continuous_const).mem_nhds (by simp)
    refine ⟨U ∩ {g' | |l g'| < |l g| + 1}, inter_mem hU hV,
      Real.exp (s * max |b| |a| * (|l g| + 1)) * M, fun z h1 h2 g' hg' => ?_⟩
    have hH := hM _ (hlec h1) (hlec' h2) g' hg'.1
    have hg2 : |l g'| < |l g| + 1 := hg'.2
    have hz : |z.re| ≤ max |b| |a| := abs_le_max_abs_abs h1 h2
    have hE : ‖Complex.exp (s * z * l g')‖ ≤ Real.exp (s * max |b| |a| * (|l g| + 1)) := by
      rw [Complex.norm_exp, Complex.re_mul_ofReal, hre]
      apply Real.exp_le_exp.mpr
      calc s * z.re * l g' ≤ |s * z.re * l g'| := le_abs_self _
        _ = s * |z.re| * |l g'| := by rw [abs_mul, abs_mul, abs_of_pos hs]
        _ ≤ s * max |b| |a| * (|l g| + 1) := by gcongr
    rw [norm_smul]
    exact mul_le_mul hE hH (norm_nonneg _) (Real.exp_pos _).le
  · rw [eis_twist hl c ρ (fun x => s * z * η x) _ (s * z) (fun x => by push_cast; ring),
      ContinuousLinearMap.smul_apply, hw.eqR _ (by rw [hre]; exact hgtx _ hz) g w, smul_comm]
  · rw [eis_twist hl c ρ (fun x => β x - s * z * η' x) _ (s * z) (fun x => by push_cast; ring),
      ContinuousLinearMap.smul_apply, hw.eqL _ (by rw [hre]; exact hltx _ hz) g w]

theorem scale : PositivityTheory.RgEis.Scale := by
  intro G _ _ _ _ _ W _ _ _ K ρ _ _ Γ P P' c η η' β l s hs hl hW
  obtain ⟨R, D, Op, H, hw⟩ := hW
  exact ⟨_, _, _, _, wall_scale hs hl hw⟩

end GlobalTheory.CompanionTheory.RgEisScale
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinScalingLawStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_scaling_law : PositivityTheory.RgEis.Scale := by
  first | exact @GlobalTheory.CompanionTheory.RgEisScale.scale | exact GlobalTheory.CompanionTheory.RgEisScale.scale | (intros; apply GlobalTheory.CompanionTheory.RgEisScale.scale <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfLeSmall
noncomputable section

open MeasureTheory PositivityTheory.Rg.BcB.E1
open scoped ENNReal Pointwise

namespace GlobalTheory.CompanionTheory.KerPoint

theorem support_cv_adj_cv (hKB : KerBasic) (hCv : CvTest) (X : Ctx) (φ ψ : X.G → ℂ) (hφ : Tst φ) (hψ : Tst ψ)
    (N : Set X.G) (hNc : IsCompact N) (hN : tsupport ψ ⊆ N) :
    Function.support (cv X.μ (adj ψ) (cv X.μ φ ψ)) ⊆ N⁻¹ * (tsupport φ * N) := by
  have hadj : Tst (adj ψ) := (hKB X ψ hψ).2.2.2.1
  have hc := hCv X φ ψ hφ hψ
  have hcc := hCv X (adj ψ) (cv X.μ φ ψ) hadj hc.1
  refine hcc.2.1.trans ?_
  have hs1 : tsupport (adj ψ) ⊆ N⁻¹ := by
    refine closure_minimal ?_ hNc.inv.isClosed
    intro z hz
    have hz' : ψ z⁻¹ ≠ 0 := by
      intro h0
      apply hz
      simp [adj, h0]
    exact Set.mem_inv.2 (hN (subset_tsupport _ hz'))
  have hs2 : tsupport (cv X.μ φ ψ) ⊆ tsupport φ * N :=
    closure_minimal (hc.2.1.trans (Set.mul_subset_mul_left hN)) (hφ.2.isCompact.mul hNc).isClosed
  exact Set.mul_subset_mul hs1 hs2

theorem inner_map_sub_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (U : H →L[ℂ] H)
    (a b k₁ k₂ : H) (δ : ℝ) (ha : ‖a - k₁‖ ≤ δ) (hb : ‖b - k₂‖ ≤ δ) :
    ‖inner ℂ a (U b) - inner ℂ k₁ (U k₂)‖ ≤ ‖U‖ * δ * (‖k₂‖ + δ) + ‖k₁‖ * ‖U‖ * δ := by
  have e : inner ℂ a (U b) - inner ℂ k₁ (U k₂) = inner ℂ (a - k₁) (U b) + inner ℂ k₁ (U (b - k₂)) := by
    simp only [inner_sub_left, inner_sub_right, map_sub]
    ring
  have hbn : ‖b‖ ≤ ‖k₂‖ + δ := by
    have := norm_add_le (b - k₂) k₂
    rw [sub_add_cancel] at this
    linarith
  have hU : 0 ≤ ‖U‖ := norm_nonneg _
  have t1 : ‖(inner ℂ (a - k₁) (U b) : ℂ)‖ ≤ ‖U‖ * δ * (‖k₂‖ + δ) := by
    calc ‖(inner ℂ (a - k₁) (U b) : ℂ)‖ ≤ ‖a - k₁‖ * ‖U b‖ := norm_inner_le_norm _ _
      _ ≤ δ * (‖U‖ * (‖k₂‖ + δ)) := by
          have h2 : ‖U b‖ ≤ ‖U‖ * (‖k₂‖ + δ) :=
            (U.le_opNorm b).trans (mul_le_mul_of_nonneg_left hbn hU)
          exact mul_le_mul ha h2 (norm_nonneg _) ((norm_nonneg _).trans ha)
      _ = ‖U‖ * δ * (‖k₂‖ + δ) := by ring
  have t2 : ‖(inner ℂ k₁ (U (b - k₂)) : ℂ)‖ ≤ ‖k₁‖ * ‖U‖ * δ := by
    calc ‖(inner ℂ k₁ (U (b - k₂)) : ℂ)‖ ≤ ‖k₁‖ * ‖U (b - k₂)‖ := norm_inner_le_norm _ _
      _ ≤ ‖k₁‖ * (‖U‖ * δ) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          exact (U.le_opNorm _).trans (mul_le_mul_of_nonneg_left hb hU)
      _ = ‖k₁‖ * ‖U‖ * δ := by ring
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add t1 t2)

theorem eq_zero_of_le_small {D C : ℝ} (hC : 0 ≤ C) (h : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → D ≤ δ * C) : D ≤ 0 := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hC1 : 0 < C + 1 := by linarith
  have hδ : 0 < min 1 (ε / (C + 1)) := lt_min one_pos (div_pos hε hC1)
  have h1 := h _ hδ (min_le_left _ _)
  have h2 : min 1 (ε / (C + 1)) * C ≤ ε := by
    calc min 1 (ε / (C + 1)) * C ≤ ε / (C + 1) * (C + 1) :=
          mul_le_mul (min_le_right _ _) (by linarith) hC (div_pos hε hC1).le
      _ = ε := by field_simp
  linarith

theorem ptEq_of : KerBasic → CvTest → OpAdj → ColOp → BumpEx → ApproxU → KerClose → VecLim → PtEq := by
  intro hKB hCv hAdj hCol hBump hAU hKC hVL X ι _ Φ₁ Φ₂ Φ T₁ T₂ U h1 h2 h hT1 hT2 hT x y i j k₁ k₂ hk1 hk2
  obtain ⟨N, hNc, hN1⟩ := exists_compact_mem_nhds (1 : X.G)
  have h1N : (1 : X.G) ∈ N := mem_of_mem_nhds hN1
  have hΩ : IsCompact (N⁻¹ * (tsupport (Φ i j) * N)) := hNc.inv.mul ((h i j).2.isCompact.mul hNc)
  obtain ⟨M, hM0, hM⟩ := hKC X _ x y hΩ
  have hadj1 : ∀ a b, Tst ((fun i j => adj (Φ₁ j i)) a b : X.G → ℂ) :=
    fun a b => (hKB X _ (h1 b a)).2.2.2.1
  have hTadj := hAdj X ι Φ₁ T₁ h1 hT1
  have key : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ‖ker X.Γ (Φ i j) x y - inner ℂ k₁ (U k₂)‖ ≤
      δ * (M + ‖U‖ * (‖k₂‖ + 1) + ‖k₁‖ * ‖U‖) := by
    intro δ hδ hδ1
    obtain ⟨W₁, hW₁, hL₁⟩ := hVL X ι (fun i j => adj (Φ₁ j i)) (ContinuousLinearMap.adjoint T₁) x i k₁ δ hadj1 hTadj hk1 hδ
    obtain ⟨W₂, hW₂, hL₂⟩ := hVL X ι Φ₂ T₂ y j k₂ δ h2 hT2 hk2 hδ
    obtain ⟨W₃, hW₃, hL₃⟩ := hAU X (Φ i j) δ (h i j) hδ
    obtain ⟨ψ, hψ, hsub⟩ := hBump X (N ∩ W₁ ∩ W₂ ∩ W₃)
      (Filter.inter_mem (Filter.inter_mem (Filter.inter_mem hN1 hW₁) hW₂) hW₃)
    have sN : tsupport ψ ⊆ N := fun z hz => (hsub hz).1.1.1
    have s1 : tsupport ψ ⊆ W₁ := fun z hz => (hsub hz).1.1.2
    have s2 : tsupport ψ ⊆ W₂ := fun z hz => (hsub hz).1.2
    have s3 : tsupport ψ ⊆ W₃ := fun z hz => (hsub hz).2
    have hc := hCol X ι ψ hψ.1
    obtain ⟨v, hv⟩ := hc.1 x i
    obtain ⟨u, hu⟩ := hc.1 y j
    have e1 : inner ℂ v ((T₁ * U * T₂) u) = ker X.Γ (cv X.μ (adj ψ) (cv X.μ (Φ i j) ψ)) x y :=
      (hc.2 Φ (T₁ * U * T₂) h hT y j u hu).2 x i v hv
    have e2 : inner ℂ v ((T₁ * U * T₂) u) = inner ℂ (ContinuousLinearMap.adjoint T₁ v) (U (T₂ u)) := by
      rw [ContinuousLinearMap.adjoint_inner_left]
      rfl
    have b1 := hL₁ ψ hψ s1 v hv
    have b2 := hL₂ ψ hψ s2 u hu
    have b3 := inner_map_sub_le U _ _ k₁ k₂ δ b1 b2
    have b4 := hM (cv X.μ (adj ψ) (cv X.μ (Φ i j) ψ)) (Φ i j) δ
      (support_cv_adj_cv hKB hCv X _ ψ (h i j) hψ.1 N hNc sN)
      (by
        intro z hz
        refine ⟨1⁻¹, Set.inv_mem_inv.2 h1N, z * 1, ⟨z, subset_tsupport _ hz, 1, h1N, rfl⟩, by simp⟩)
      (fun z => (hL₃ ψ hψ s3 z).2)
    have hsplit : ker X.Γ (Φ i j) x y - inner ℂ k₁ (U k₂) =
        (inner ℂ (ContinuousLinearMap.adjoint T₁ v) (U (T₂ u)) - inner ℂ k₁ (U k₂)) -
          (ker X.Γ (cv X.μ (adj ψ) (cv X.μ (Φ i j) ψ)) x y - ker X.Γ (Φ i j) x y) := by
      rw [← e2, e1]
      ring
    have hU : 0 ≤ ‖U‖ := norm_nonneg _
    have hk : 0 ≤ ‖k₂‖ := norm_nonneg _
    have hle : ‖U‖ * δ * (‖k₂‖ + δ) ≤ ‖U‖ * δ * (‖k₂‖ + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hU hδ.le)
    rw [hsplit]
    refine (norm_sub_le _ _).trans ?_
    nlinarith [b3, b4, hle]
  have hC : 0 ≤ M + ‖U‖ * (‖k₂‖ + 1) + ‖k₁‖ * ‖U‖ := by positivity
  have := eq_zero_of_le_small hC key
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

end GlobalTheory.CompanionTheory.KerPoint

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeparableNormCommuting
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeparableNormCommuting
open Polynomial

namespace GlobalTheory.CompanionTheory.Centraliser

variable {K : Type} [Field K] {n : ℕ}

theorem act_mul (γ : Matrix (Fin n) (Fin n) K) (a b : K[X]) (v : Fin n → K) :
    (aeval γ (a * b)).mulVec v = (aeval γ a).mulVec ((aeval γ b).mulVec v) := by
  rw [map_mul, Matrix.mulVec_mulVec]

theorem charpoly_dvd_of_aeval_eq_zero (γ : Matrix (Fin n) (Fin n) K)
    (hs : γ.charpoly.Separable) {p : K[X]} (hp : aeval γ p = 0) : γ.charpoly ∣ p := by
  have h := GlobalTheory.CharpolyPowIrred.charpoly_dvd_pow_of_aeval γ p hp
  rcases Nat.eq_zero_or_pos (Fintype.card (Fin n)) with h0 | h0
  · rw [h0, pow_zero] at h
    exact h.trans (one_dvd p)
  · exact (hs.squarefree.dvd_pow_iff_dvd h0.ne').1 h

theorem exists_vec_ann (γ : Matrix (Fin n) (Fin n) K) (hs : γ.charpoly.Separable) (q : K[X]) :
    q ∣ γ.charpoly → ∃ v : Fin n → K, (aeval γ q).mulVec v = 0 ∧
      ∀ h : K[X], (aeval γ h).mulVec v = 0 → q ∣ h := by
  have hf0 : γ.charpoly ≠ 0 := γ.charpoly_monic.ne_zero
  refine UniqueFactorizationMonoid.induction_on_prime q ?_ ?_ ?_
  · intro h
    exact absurd (zero_dvd_iff.1 h) hf0
  · intro x hx _
    exact ⟨0, by simp, fun h _ => hx.dvd⟩
  · intro a p ha hp ih hd
    obtain ⟨v', hv1, hv2⟩ := ih ((dvd_mul_left a p).trans hd)
    obtain ⟨g, hg⟩ : p ∣ γ.charpoly := (dvd_mul_right p a).trans hd
    have hgne : g ≠ 0 := by
      rintro rfl
      exact hf0 (by simpa using hg)
    have hg0 : aeval γ g ≠ 0 := fun h => by
      obtain ⟨c, hc⟩ := charpoly_dvd_of_aeval_eq_zero γ hs h
      rw [hg] at hc
      have h1 : g * (p * c) = g * 1 := by
        rw [mul_one]
        calc g * (p * c) = p * g * c := by ring
          _ = g := hc.symm
      exact hp.not_unit (IsUnit.of_mul_eq_one _ (mul_left_cancel₀ hgne h1))
    obtain ⟨u, hu⟩ : ∃ u, (aeval γ g).mulVec u ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hg0 (Matrix.mulVec_injective (funext fun u => by simpa using hcon u))
    set w := (aeval γ g).mulVec u with hw
    have hpw : (aeval γ p).mulVec w = 0 := by
      rw [hw, ← act_mul, ← hg, Matrix.aeval_self_charpoly, Matrix.zero_mulVec]
    have hkey : ∀ h : K[X], (aeval γ h).mulVec w = 0 → p ∣ h := by
      intro h hh
      by_contra hnd
      obtain ⟨s, t, hst⟩ := (Prime.coprime_iff_not_dvd hp).2 hnd
      apply hu
      have h1 : (aeval γ (s * p + t * h)).mulVec w = w := by
        rw [hst]; simp
      rw [map_add (f := _), Matrix.add_mulVec, act_mul, act_mul, hpw, hh] at h1
      simpa using h1.symm
    have hpa : ¬ p ∣ a := by
      rintro ⟨c, rfl⟩
      exact hp.not_unit (hs.squarefree p
        ((mul_dvd_mul_left p (dvd_mul_right p c)).trans hd))
    have hcop : IsCoprime p a := (Prime.coprime_iff_not_dvd hp).2 hpa
    refine ⟨v' + w, ?_, ?_⟩
    · rw [Matrix.mulVec_add, act_mul, hv1, mul_comm, act_mul, hpw]
      simp
    · intro h hh
      have h1 : (aeval γ (h * p)).mulVec v' = 0 := by
        have h2 : (aeval γ (h * p)).mulVec (v' + w) = 0 := by
          rw [mul_comm, act_mul, hh, Matrix.mulVec_zero]
        rw [Matrix.mulVec_add, act_mul γ h p w, hpw, Matrix.mulVec_zero, add_zero] at h2
        exact h2
      have hah : a ∣ h := hcop.symm.dvd_of_dvd_mul_right (hv2 _ h1)
      obtain ⟨c, rfl⟩ := hah
      have h3 : (aeval γ (a * c)).mulVec v' = 0 := by
        rw [mul_comm, act_mul, hv1]; simp
      rw [Matrix.mulVec_add, h3, zero_add] at hh
      exact hcop.mul_dvd (hkey _ hh) (dvd_mul_right a c)

theorem exists_cyclic_vec (γ : Matrix (Fin n) (Fin n) K) (hs : γ.charpoly.Separable) :
    ∃ v : Fin n → K, ∀ w : Fin n → K, ∃ q : K[X], (aeval γ q).mulVec v = w := by
  obtain ⟨v, -, hv⟩ := exists_vec_ann γ hs γ.charpoly dvd_rfl
  refine ⟨v, ?_⟩
  let L : K[X] →ₗ[K] (Fin n → K) :=
    { toFun := fun p => (aeval γ p).mulVec v
      map_add' := fun a b => by rw [map_add (f := _), Matrix.add_mulVec]
      map_smul' := fun c a => by rw [map_smul, Matrix.smul_mulVec]; rfl }
  let φ : degreeLT K n →ₗ[K] (Fin n → K) := L.domRestrict (degreeLT K n)
  have hinj : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    rintro ⟨p, hp⟩ h0
    have hd : γ.charpoly ∣ p := hv p h0
    have hlt : p.degree < γ.charpoly.degree := by
      rw [Matrix.charpoly_degree_eq_dim, Fintype.card_fin]
      exact Polynomial.mem_degreeLT.1 hp
    exact Subtype.ext (Polynomial.eq_zero_of_dvd_of_degree_lt hd hlt)
  have hfr : Module.finrank K (degreeLT K n) = Module.finrank K (Fin n → K) :=
    (degreeLTEquiv K n).finrank_eq
  have hsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).1 hinj
  intro w
  obtain ⟨⟨q, _⟩, hq⟩ := hsurj w
  exact ⟨q, hq⟩

theorem a1 : PositivityTheory.Rg.Tf.Loc.A1 := by
  intro K _ n γ hs M hM
  obtain ⟨v, hv⟩ := exists_cyclic_vec γ hs
  obtain ⟨p, hp⟩ := hv (M.mulVec v)
  refine ⟨p, Matrix.mulVec_injective (funext fun w => ?_)⟩
  obtain ⟨q, rfl⟩ := hv w
  have hc : Commute M (aeval γ q) := by
    rw [aeval_eq_sum_range]
    exact Commute.sum_right _ _ _ fun i _ => (hM.pow_right i).smul_right _
  rw [Matrix.mulVec_mulVec, hc.eq, ← Matrix.mulVec_mulVec, ← hp, ← act_mul, mul_comm, act_mul]

end GlobalTheory.CompanionTheory.Centraliser
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeparableNormCommutingStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.separable_norm_commuting : PositivityTheory.Rg.Tf.Loc.A1 := by
  first | exact @GlobalTheory.CompanionTheory.Centraliser.a1 | exact GlobalTheory.CompanionTheory.Centraliser.a1 | (intros; apply GlobalTheory.CompanionTheory.Centraliser.a1 <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistOfSectionLaw
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistOfSectionLaw
noncomputable section

namespace GlobalTheory.CompanionTheory.RgEisTwist

open PositivityTheory.RgEis

variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {Γ K : Subgroup G} {c₀ : G → ℂ}

lemma ch_mul (h : IsCh Γ ⊤ c₀) (a b : G) : c₀ (a * b) = c₀ a * c₀ b :=
  h.mul a (Subgroup.mem_top a) b (Subgroup.mem_top b)

lemma ch_one (h : IsCh Γ ⊤ c₀) : c₀ 1 = 1 :=
  h.rat 1 (one_mem _) (Subgroup.mem_top 1)

lemma ch_rat_mul (h : IsCh Γ ⊤ c₀) {γ : G} (hγ : γ ∈ Γ) (g : G) : c₀ (γ * g) = c₀ g := by
  rw [ch_mul h, h.rat γ hγ (Subgroup.mem_top γ), one_mul]

lemma ch_norm (h : IsCh Γ ⊤ c₀) (g : G) : ‖c₀ g‖ = 1 :=
  h.norm g (Subgroup.mem_top g)

lemma ch_cont (h : IsCh Γ ⊤ c₀) : Continuous c₀ := by
  have h' := h.cont
  rw [Subgroup.coe_top] at h'
  exact continuousOn_univ.mp h'

def twRep (h : IsCh Γ ⊤ c₀) (K : Subgroup G) (ρ : K →* (W →L[ℂ] W)) : K →* (W →L[ℂ] W) where
  toFun r := c₀ r • ρ r
  map_one' := by simp [ch_one h]
  map_mul' a b := by
    ext w
    simp [ch_mul h, smul_smul, mul_comm]

lemma twRep_apply (h : IsCh Γ ⊤ c₀) (ρ : K →* (W →L[ℂ] W)) (r : K) :
    twRep h K ρ r = c₀ r • ρ r := rfl

lemma twRep_cont (h : IsCh Γ ⊤ c₀) {ρ : K →* (W →L[ℂ] W)} (hρ : Continuous ρ) :
    Continuous (twRep h K ρ) :=
  ((ch_cont h).comp continuous_subtype_val).smul hρ

lemma secSp_twist (h : IsCh Γ ⊤ c₀) (ρ : K →* (W →L[ℂ] W)) (P : Subgroup G) (c : G → ℂ) :
    secSp K P (c * c₀) ρ = secSp K P c (twRep h K ρ) := by
  ext w
  have key : ∀ r : K, (c * c₀) (r : G) • ρ r w = c (r : G) • twRep h K ρ r w := fun r => by
    rw [twRep_apply, smul_apply, smul_smul, Pi.mul_apply]
  change (∀ r : K, (r : G) ∈ P → (c * c₀) (r : G) • ρ r w = w) ↔
    ∀ r : K, (r : G) ∈ P → c (r : G) • twRep h K ρ r w = w
  simp only [key]

lemma sec_twist (h : IsCh Γ ⊤ c₀) (ρ : K →* (W →L[ℂ] W)) (P : Subgroup G) (c : G → ℂ) (g : G) :
    sec K P (c * c₀) ρ g = c₀ g • sec K P c (twRep h K ρ) g := by
  unfold sec
  by_cases hk : ∃ k : K, g * (k : G)⁻¹ ∈ P
  · rw [dite_eq_left hk, dite_eq_left hk, twRep_apply, Pi.mul_apply, Subgroup.coe_inv, ch_mul h g, smul_smul, smul_smul]
    congr 1
    ring
  · rw [dite_eq_right hk, dite_eq_right hk, smul_zero]

lemma eis_twist (h : IsCh Γ ⊤ c₀) (ρ : K →* (W →L[ℂ] W)) (P : Subgroup G) (c : G → ℂ) (Λ : G → ℂ)
    (g : G) (w : W) :
    eis Γ K P (c * c₀) ρ Λ g w = c₀ g • eis Γ K P c (twRep h K ρ) Λ g w := by
  unfold eis
  rw [← tsum_const_smul'']
  refine tsum_congr fun q => ?_
  have hq : rep q ∈ Γ := (Quotient.out q).2
  rw [sec_twist h, smul_apply, ch_rat_mul h hq, smul_comm]

def castL {A B : Submodule ℂ W} (e : A = B) : A →L[ℂ] B :=
  (ContinuousLinearEquiv.ofEq A B e).toContinuousLinearMap

lemma leftGood_cast {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {A B : Submodule ℂ W} (e : A = B)
    {Op : ℂ → (X →L[ℂ] A)} {a : ℝ} (hO : LeftGood Op a) :
    LeftGood (fun z => (castL e).comp (Op z)) a := by
  subst e
  have hid : (fun z => (castL (rfl : A = A)).comp (Op z)) = Op := by
    funext z
    ext x
    rfl
  rwa [hid]

lemma wall_twist (h : IsCh Γ ⊤ c₀) {P P' : Subgroup G} {c : G → ℂ} {η η' β : G → ℝ}
    {ρ : K →* (W →L[ℂ] W)} {L : Submodule ℂ W} {R : ℝ} {D : ℂ → ℂ}
    {Op : ℂ → (L →L[ℂ] secSp K P' c (twRep h K ρ))} {H : ℂ → G → (L →L[ℂ] W)}
    (hw : Wall Γ K P P' c η η' β (twRep h K ρ) L R D Op H) :
    Wall Γ K P P' (c * c₀) η η' β ρ L R D
      (fun z => (castL (secSp_twist h ρ P' c).symm).comp (Op z)) (fun z g => c₀ g • H z g) := by
  refine
    { le := ?_
      pos := hw.pos
      convR := hw.convR
      convL := hw.convL
      dEnt := hw.dEnt
      dNe := hw.dNe
      op := leftGood_cast _ hw.op
      hol := fun g => (hw.hol g).const_smul (c₀ g)
      cont := ((ch_cont h).comp continuous_snd).smul hw.cont
      bdd := ?_
      eqR := ?_
      eqL := ?_ }
  · rw [secSp_twist h ρ P c]
    exact hw.le
  · intro b a g
    obtain ⟨U, hU, M, hM⟩ := hw.bdd b a g
    refine ⟨U, hU, M, fun z h1 h2 g' hg' => ?_⟩
    rw [norm_smul, ch_norm h, one_mul]
    exact hM z h1 h2 g' hg'
  · intro z hz g w
    rw [smul_apply, hw.eqR z hz g w, eis_twist h, smul_comm]
  · intro z hz g w
    rw [smul_apply, hw.eqL z hz g w, eis_twist h]
    rfl

theorem twist : SecLaw → Twist := by
  intro _ G _ _ _ _ _ Γ K S P P' c c₀ η η' β ξ N _ h _ _ _
  refine ⟨fun hA W _ _ _ ρ hρ => ?_, fun hA W _ _ _ ρ hρ => ?_, fun hA W _ _ _ ρ hρ => ?_⟩
  · obtain ⟨R, D, Op, H, hw⟩ := hA W (twRep h K ρ) (twRep_cont h hρ)
    unfold HasWall
    rw [secSp_twist h ρ P c]
    exact ⟨R, D, _, _, wall_twist h hw⟩
  · obtain ⟨R, D, Op, H, hw, ⟨a, ha0, ha⟩, O, hO, hOp⟩ := hA W (twRep h K ρ) (twRep_cont h hρ)
    unfold HasFirst
    rw [secSp_twist h ρ S c]
    refine ⟨R, D, _, _, wall_twist h hw, ⟨a, ha0, fun g w => ?_⟩,
      fun z => (castL (secSp_twist h ρ P' c).symm).comp (O z), leftGood_cast _ hO, fun z hz => ?_⟩
    · rw [smul_apply, ha g w, sec_twist h, smul_apply, smul_comm]
    · rw [hOp z hz, ContinuousLinearMap.comp_smul]
  · obtain ⟨R, D, Op, H, hw, hd, T, hT⟩ := hA W (twRep h K ρ) (twRep_cont h hρ)
    unfold HasLast
    rw [secSp_twist h ρ P c]
    refine ⟨R, D, _, _, wall_twist h hw, hd,
      (castL (secSp_twist h ρ S c).symm).comp T, fun g w => ?_⟩
    rw [smul_apply, hT g w, sec_twist h, smul_apply, smul_comm]
    rfl

end GlobalTheory.CompanionTheory.RgEisTwist
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistOfSectionLawStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_of_section_law : PositivityTheory.RgEis.SecLaw → PositivityTheory.RgEis.Twist := by
  first | exact @GlobalTheory.CompanionTheory.RgEisTwist.twist | exact GlobalTheory.CompanionTheory.RgEisTwist.twist | (intros; apply GlobalTheory.CompanionTheory.RgEisTwist.twist <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMapTorusSurjective
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMapTorusSurjective
open PositivityTheory.Rg.Tf.Loc GroundTheory.LocalField Topology
open Matrix

namespace GlobalTheory.CompanionTheory.LocTop

section Field

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem secondCountable_field : SecondCountableTopology F := by
  letI N : NontriviallyNormedField F := nontriviallyNormedField F
  have hw : @WeaklyLocallyCompactSpace F N.toUniformSpace.toTopologicalSpace :=
    (inferInstance : WeaklyLocallyCompactSpace F)
  haveI : ProperSpace F := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  have h : @SecondCountableTopology F N.toUniformSpace.toTopologicalSpace := inferInstance
  exact h

variable (n : ℕ)

def intMat : Set (Matrix (Fin n) (Fin n) F) := {X | ∀ i j, X i j ∈ intO F}

theorem isCompact_intMat : IsCompact (intMat F n) := by
  have hO : IsCompact ((intO F : Subring F) : Set F) :=
    IsNonarchimedeanLocalField.isCompact_closedBall F 1
  have hrow : IsCompact (Set.pi Set.univ fun _ : Fin n => ((intO F : Subring F) : Set F)) :=
    isCompact_univ_pi fun _ => hO
  have hmat : IsCompact (Set.pi Set.univ fun _ : Fin n =>
      Set.pi Set.univ fun _ : Fin n => ((intO F : Subring F) : Set F)) :=
    isCompact_univ_pi fun _ => hrow
  have hset : intMat F n = Set.pi Set.univ fun _ : Fin n =>
      Set.pi Set.univ fun _ : Fin n => ((intO F : Subring F) : Set F) := by
    ext X
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
  rw [hset]
  exact hmat

theorem isOpen_intMat : IsOpen (intMat F n) := by
  have hO : IsOpen ((intO F : Subring F) : Set F) :=
    Valuation.isOpen_integer (v := ValuativeRel.valuation F)
  have hset : intMat F n =
      ⋂ i : Fin n, ⋂ j : Fin n, (fun X : Matrix (Fin n) (Fin n) F => X i j) ⁻¹'
        ((intO F : Subring F) : Set F) := by
    ext X
    simp [intMat]
  rw [hset]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hO.preimage ?_
  exact (continuous_apply j).comp (continuous_apply i)

theorem mem_unitGL_iff (g : GL (Fin n) F) :
    g ∈ unitGL (n := Fin n) F ↔
      (g : Matrix (Fin n) (Fin n) F) ∈ intMat F n ∧
        ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) ∈ intMat F n := by
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · exact ((h : Matrix (Fin n) (Fin n) (intO F)) i j).2
    · rw [← map_inv]
      exact (((h⁻¹ : GL (Fin n) (intO F)) : Matrix (Fin n) (Fin n) (intO F)) i j).2
  · rintro ⟨h1, h2⟩
    let A : Matrix (Fin n) (Fin n) (intO F) := fun i j => ⟨(g : Matrix (Fin n) (Fin n) F) i j, h1 i j⟩
    let B : Matrix (Fin n) (Fin n) (intO F) :=
      fun i j => ⟨((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j, h2 i j⟩
    have hA : A.map (intO F).subtype = (g : Matrix (Fin n) (Fin n) F) := by ext i j; rfl
    have hB : B.map (intO F).subtype = ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
      ext i j; rfl
    have hinj : Function.Injective
        (fun X : Matrix (Fin n) (Fin n) (intO F) => X.map (intO F).subtype) :=
      Matrix.map_injective Subtype.val_injective
    have hAB : A * B = 1 := hinj (by
      simp only
      rw [Matrix.map_mul, hA, hB, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)])
    have hBA : B * A = 1 := hinj (by
      simp only
      rw [Matrix.map_mul, hA, hB, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)])
    refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
    ext i j
    rfl

variable [T2Space F]

theorem unitGL_eq_preimage :
    (unitGL (n := Fin n) F : Set (GL (Fin n) F)) =
      Units.embedProduct (Matrix (Fin n) (Fin n) F) ⁻¹'
        (intMat F n ×ˢ (MulOpposite.unop ⁻¹' intMat F n)) := by
  ext g
  exact mem_unitGL_iff F n g

theorem isOpen_unitGL : IsOpen (unitGL (n := Fin n) F : Set (GL (Fin n) F)) := by
  rw [unitGL_eq_preimage]
  exact ((isOpen_intMat F n).prod ((isOpen_intMat F n).preimage MulOpposite.continuous_unop)).preimage
    Units.continuous_embedProduct

theorem isCompact_unitGL : IsCompact (unitGL (n := Fin n) F : Set (GL (Fin n) F)) := by
  rw [unitGL_eq_preimage]
  refine (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) F)).isCompact_preimage
    ((isCompact_intMat F n).prod ?_)
  exact (MulOpposite.opHomeomorph.symm.isCompact_preimage).2 (isCompact_intMat F n)

theorem locallyCompact_GL : LocallyCompactSpace (GL (Fin n) F) := by
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) F) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → F))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.isClosedEmbedding.locallyCompactSpace
  exact (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) F)).locallyCompactSpace

theorem secondCountable_GL : SecondCountableTopology (GL (Fin n) F) := by
  haveI := secondCountable_field F
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) F) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → F))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact (Units.isEmbedding_embedProduct (M := Matrix (Fin n) (Fin n) F)).secondCountableTopology

end Field

section Twisted

variable {k E : Type} [Field k] [Field E] [TopologicalSpace E] [IsTopologicalRing E] [T2Space E]
  [Algebra k E]

theorem continuous_sigmaGL (σ : E ≃ₐ[k] E) (hσ : Continuous σ) (n : ℕ) :
    Continuous (sigmaGL σ : Monoid.End (GL (Fin n) E)) := by
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · exact Units.continuous_val.matrix_map hσ
  · have : (fun g : GL (Fin n) E => (((sigmaGL σ g : GL (Fin n) E)⁻¹ : GL (Fin n) E) :
        Matrix (Fin n) (Fin n) E)) =
        fun g : GL (Fin n) E => ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map σ := by
      funext g
      rw [← map_inv]
      rfl
    show Continuous (fun g : GL (Fin n) E => (((sigmaGL σ g : GL (Fin n) E)⁻¹ : GL (Fin n) E) :
        Matrix (Fin n) (Fin n) E))
    rw [this]
    exact (Units.continuous_val.comp continuous_inv).matrix_map hσ

theorem isClosed_twCent (σ : E ≃ₐ[k] E) (hσ : Continuous σ) (n : ℕ) (δ : GL (Fin n) E) :
    IsClosed (twCent (sigmaGL σ) δ : Set (GL (Fin n) E)) := by
  haveI : T2Space (GL (Fin n) E) :=
    (Units.isEmbedding_embedProduct (M := Matrix (Fin n) (Fin n) E)).t2Space
  have hθ := continuous_sigmaGL σ hσ n
  have : (twCent (sigmaGL σ) δ : Set (GL (Fin n) E)) = {g | g⁻¹ * δ * sigmaGL σ g = δ} := rfl
  rw [this]
  exact isClosed_eq ((continuous_inv.mul continuous_const).mul hθ) continuous_const

end Twisted

theorem t0 : T0 := by
  refine ⟨fun F _ _ _ _ n => ?_, ?_⟩
  · haveI : T2Space F := t2Space_of_isNonarchimedeanLocalField F
    exact ⟨locallyCompact_GL F n, secondCountable_GL F n, isOpen_unitGL F n, isCompact_unitGL F n⟩
  · intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ _ n δ
    haveI : T2Space E := t2Space_of_isNonarchimedeanLocalField E
    exact isClosed_twCent σ (continuous_algHom σ.toAlgHom) n δ

end GlobalTheory.CompanionTheory.LocTop
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMapTorusSurjectiveStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_map_torus_surjective : PositivityTheory.Rg.Tf.Loc.T0 := by
  first | exact @GlobalTheory.CompanionTheory.LocTop.t0 | exact GlobalTheory.CompanionTheory.LocTop.t0 | (intros; apply GlobalTheory.CompanionTheory.LocTop.t0 <;> assumption)
end
end
