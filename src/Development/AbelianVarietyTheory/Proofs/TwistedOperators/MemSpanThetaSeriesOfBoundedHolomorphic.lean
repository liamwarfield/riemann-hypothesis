module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReadOffFormsAutomorphicInverseMultiplier
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsContinuousRealScalarCharacterWeakWeil

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOfRationalLevelInvariantAgreeChosen
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOfRationalLevelInvariantAgreeChosen
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.ExtInv

theorem eq_of_invariant : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Lv : SW.Level C.X) (M : ℕ), 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ gL : Lt D.host.E T.rank → GA D T, (∀ L ∈ Lv.lats, gL L ∈ GfC T ∧ TrivAt T (C.under Lv) (gL L) ∧ IsMov (fmt T (gL L)) C.X.Λ L) → ∀ φ ψ : GA D T → ℂ, (∀ γ ∈ GQ T, ∀ g, φ (γ * g) = φ g) → (∀ γ ∈ GQ T, ∀ g, ψ (γ * g) = ψ g) → (∀ k, C.LevK Lv k 1 → ∀ g, φ (g * k) = φ g) → (∀ k, C.LevK Lv k 1 → ∀ g, ψ (g * k) = ψ g) → (∀ L ∈ Lv.lats, ∀ a ∈ GinfC T, φ (gL L * a) = ψ (gL L * a)) → φ = ψ := by
  intro D S T C Lv M hM hM𝔪 gL hgL φ ψ hφ hψ hφk hψk hag
  have hΛ : C.X.Λ.FG ∧ Submodule.span D.host.E (C.X.Λ : Set (Fin T.rank → D.host.E)) = ⊤ :=
    ⟨C.X.Λ_fg, C.X.Λ_span⟩
  have hm1 : IsMov (fmt T 1) C.X.Λ C.X.Λ := by rw [Red.fmt_one]; exact Red.isMov_one _
  obtain ⟨-, hL⟩ := GlobalTheory.T.self_dual_lattices_at_level D S T C
  have hI : C.under Lv ≠ ⊥ := (hL Lv 1 _ hΛ.1 hm1).2.2.1
  have hgrp := ((GlobalTheory.T.rational_unitary_group_structure D S T C).2.2.2 T).2.1
  have hcomm := ((GlobalTheory.T.rational_unitary_group_structure D S T C).2.2.2 T).2.2.2.1
  funext g
  obtain ⟨γ, hγ, a, ha, g', hg', k, hk, hg, ht, -, hck, hcJ⟩ := GlobalTheory.T.exists_rational_real_trivialAt_congruent_factor D T C.X.Λ (C.under Lv) M hΛ hI hM g
  have hinv : fmt T g' * fmt T g'⁻¹ = 1 := by rw [← (hgrp g' g'⁻¹).2.1, mul_inv_cancel, Red.fmt_one]
  obtain ⟨L, hLf, hLm⟩ := ((GlobalTheory.T.finiteAdelicLatticeTransport_laws D _ C.X.Λ hΛ).2.2.2 _ _ hinv).1
  have hLl : L ∈ Lv.lats := (hL Lv g' L hLf.1 hLm).2.1 ht
  obtain ⟨h1, h2, h3⟩ := hgL L hLl
  have hk1 : C.LevK Lv k 1 := Red.levK_one C Lv k hk hck.1 (hcJ _ hM𝔪)
  have hk2 : C.LevK Lv ((gL L)⁻¹ * g') 1 := GlobalTheory.T.level_group_congruent_of_two_lattice_moves D S T C Lv (gL L) g' L h1 hg' h2 ht hLf.1 h3 hLm
  have e : g = γ * (gL L * a * ((gL L)⁻¹ * g') * k) := by
    rw [hg, ← (hcomm a ha).2.2 _ h1]
    group
  rw [e, hφ γ hγ, hψ γ hγ, hφk k hk1, hψk k hk1, hφk _ hk2, hψk _ hk2]
  exact hag L hLl a ha

end GlobalTheory.Ker.ExtInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOfRationalLevelInvariantAgreeChosenStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_rational_level_invariant_agree_chosen : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Lv : SW.Level C.X) (M : ℕ), 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ gL : Lt D.host.E T.rank → GA D T, (∀ L ∈ Lv.lats, gL L ∈ GfC T ∧ TrivAt T (C.under Lv) (gL L) ∧ IsMov (fmt T (gL L)) C.X.Λ L) → ∀ φ ψ : GA D T → ℂ, (∀ γ ∈ GQ T, ∀ g, φ (γ * g) = φ g) → (∀ γ ∈ GQ T, ∀ g, ψ (γ * g) = ψ g) → (∀ k, C.LevK Lv k 1 → ∀ g, φ (g * k) = φ g) → (∀ k, C.LevK Lv k 1 → ∀ g, ψ (g * k) = ψ g) → (∀ L ∈ Lv.lats, ∀ a ∈ GinfC T, φ (gL L * a) = ψ (gL L * a)) → φ = ψ := by
  first | exact @GlobalTheory.Ker.ExtInv.eq_of_invariant | exact GlobalTheory.Ker.ExtInv.eq_of_invariant | (intros; apply GlobalTheory.Ker.ExtInv.eq_of_invariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FormsOfBoundedAdelicFunctionNormBounded
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FormsOfBoundedAdelicFunctionNormBounded
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdSpan.BddForms

theorem fg_of_mem_lats {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
    (Lv : SW.Level X) {L : Lt E r} (hL : L ∈ Lv.lats) : L.FG := by
  obtain ⟨-, s, hcop, hs, -⟩ := hL
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.mpr rfl, Ideal.isCoprime_iff_sup_eq, bot_sup_eq] at hcop
    have hle := Ideal.mul_le_left (I := Lv.𝔪) (J := conjI Lv.𝔪)
    rw [hcop] at hle
    exact Lv.proper (top_le_iff.1 hle)
  let f : (Fin r → E) →ₗ[𝓞 E] (Fin r → E) := s • LinearMap.id
  have hinj : Function.Injective f := fun v w h => smul_right_injective _ hs0 h
  have hle : L.map f ≤ X.Λ := by
    rintro _ ⟨v, hv, rfl⟩
    exact hs v hv
  have : IsNoetherian (𝓞 E) X.Λ := isNoetherian_of_fg_of_noetherian X.Λ X.Λ_fg
  exact Submodule.fg_of_fg_map_injective f hinj (isNoetherian_submodule.1 this _ hle)

theorem zpow_mul_rpow_sq (t : ℝ) (ht : 0 < t) (l : ℤ) : t ^ l * (t ^ 2) ^ (-(l : ℝ) / 2) = 1 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
  rw [show ((2 : ℕ) : ℝ) * (-(l : ℝ) / 2) = -(l : ℝ) by push_cast; ring, Real.rpow_neg ht.le,
    Real.rpow_intCast]
  exact mul_inv_cancel₀ (zpow_ne_zero _ ht.ne')

theorem diag_ne_zero {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} {b : Frame Ψ r}
    (hb : b ∈ Bor Ψ r) (τ : Ψ) (i : Fin r) : b τ i i ≠ 0 := by
  obtain ⟨hdet, hlow⟩ := hb τ
  have htri : (mat b τ).BlockTriangular id := fun a c hca => hlow a c hca
  rw [Matrix.det_of_isUpperTriangular htri, Finset.prod_ne_zero_iff] at hdet
  exact hdet i (Finset.mem_univ _)

theorem exists_isSB_ne (n g : ℕ) : ∃ φ : TF n g, SW.IsSB φ ∧ φ ≠ 0 := by
  have key : ∀ x y : Matrix (Fin n) (Fin g) ℚ, SW.IntM y → (SW.IntM (x + y) ↔ SW.IntM x) := by
    intro x y hy
    constructor
    · intro h k i
      simpa using (h k i).sub (hy k i)
    · intro h k i
      simpa using (h k i).add (hy k i)
  have h0 : SW.IntM (0 : Matrix (Fin n) (Fin g) ℚ) := fun k i => by
    simpa using (isIntegral_zero : IsIntegral ℤ (0 : ℚ))
  refine ⟨fun x => if SW.IntM x then 1 else 0, ⟨1, one_pos, ?_, ?_⟩, ?_⟩
  · intro x hx
    by_cases h : SW.IntM x
    · simpa using h
    · simp [h] at hx
  · intro x y hy
    simp only [Nat.cast_one, one_smul, key x y hy]
  · intro h
    have := congrFun h 0
    simp [h0] at this

end GlobalTheory.AdSpan.BddForms

namespace GlobalTheory.AdSpan.BddForms

theorem pnorm_le_of_bdd : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ B, C.IsB B → ∀ f', C.IsBase Lv B f' → ∀ (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ) (z φ : GA D T → ℂ), (∀ a ∈ GinfC T, RealScal C om B a (z a)) → (∀ γ ∈ GQ T, ∀ g, φ (γ * g) = φ g) → (∀ (k : GA D T) (κ : Lv.J), C.LevK Lv k κ → om (1, k) (C.uVec Lv hn f') = C.uVec Lv hn f' ∧ ∀ g, φ (g * k) = φ g) → ∀ (v₀ : Lt D.host.E T.rank → TF S.rank C.g) (μ : GL (Fin T.rank) D.host.E → Lt D.host.E T.rank → ℂ), (∀ L ∈ Lv.lats, IsVac C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh L)) (v₀ L)) → (∀ γ ∈ Lv.grp, ∀ L ∈ Lv.lats, ∀ k : Lv.J, Lv.Red (fun i => (γ : Matrix (Fin T.rank) (Fin T.rank) D.host.E) *ᵥ Lv.β i) k → wG C.X C.bas C.idx γ (v₀ L) = (μ γ L * (Lv.lam k : ℂˣ)) • v₀ (mapL γ L)) → ∀ (ep : GA D S → ℂ) (cf : GA D T → ℂ), (∀ (h : GA D S) (Λ : Lt D.host.E S.rank) (g : GA D T) (L : Lt D.host.E T.rank), h ∈ GfC S → TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ → g ∈ GfC T → TrivAt T (C.under Lv) g → L.FG → IsMov (fmt T g) C.X.Λ L → ‖ep h‖ = 1 ∧ ‖cf g‖ = 1 ∧ om (h, g) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) = (ep h * cf g) • (C.Th (C.xB B) (Lv.phi C.bas hn v₀ L Λ))) → ∀ gL : Lt D.host.E T.rank → GA D T, (∀ L ∈ Lv.lats, gL L ∈ GfC T ∧ TrivAt T (C.under Lv) (gL L) ∧ IsMov (fmt T (gL L)) C.X.Λ L) → ∀ F : Lt D.host.E T.rank → Frame C.X.Ψ T.rank → ℂ, (∀ L ∈ Lv.lats, DifferentiableOn ℂ (F L) C.X.dom) → (∀ L ∈ Lv.lats, ∀ x ∈ C.X.dom, ∀ b ∈ Bor C.X.Ψ T.rank, F L (rmul x b) = bchar (wtOf C.X C.hr c c' S.rank) b * F L x) → (∀ L ∈ Lv.lats, ∀ a ∈ GinfC T, φ (gL L * a) = z a * (ep 1 * cf (gL L)) * F L (C.xB (C.mvB a B))) → (∃ K : ℝ, ∀ g, ‖φ g‖ ≤ K) → ∃ K : ℝ, ∀ L ∈ Lv.lats, ∀ x ∈ C.X.dom, C.X.pnorm (wtOf C.X C.hr c c' S.rank) (F L) x ≤ K := by
  intro D S T C om hW Lv hn M hw hM hMm B hB f' _hbase c c' z φ hz _hγ _hk v₀ μ _hvac _hμ ep cf hepcf gL hgL F
    _hFd hFb hFφ hφb
  obtain ⟨K, hKφ⟩ := hφb
  obtain ⟨o, b, -, -, hob, -⟩ := GlobalTheory.Ker.exists_orthonormalisation D.host.E T.rank C.X
  have hJ := (GlobalTheory.Ker.onBasis_frame_period D S T C).2
  have hmv : ∀ a, C.IsB (C.mvB a B) := fun a => ((hJ B hB).2.2.2.2.2 a).1
  have hdom : ∀ a, C.xB (C.mvB a B) ∈ C.X.dom := fun a => (hJ _ (hmv a)).2.1
  obtain ⟨φ₀, hφ₀, hφ₀ne⟩ := exists_isSB_ne S.rank C.g

  have hz1 : ∀ a ∈ GinfC T, ‖z a‖ = 1 := by
    intro a ha
    obtain ⟨c0, hc0, hc0'⟩ := GlobalTheory.Ker.RealScalar.om_real_Th D S T C om hW 1 (one_mem _) a ha B hB
    have e1 : om (1, a) (C.Th (C.xB B) φ₀) = z a • C.Th (C.xB (C.mvB a B)) φ₀ := hz a ha φ₀ hφ₀
    have e2 := hc0' φ₀ hφ₀
    have : z a = c0 := RealChar.smul_cancel (RealChar.th_ne C (hdom a) hφ₀ hφ₀ne) (e1.symm.trans e2)
    rw [this, hc0]

  have hstdFG : (stdL D.host.E S.rank).FG := Submodule.fg_span (Set.finite_range _)
  have hec : ∀ L ∈ Lv.lats, ‖ep 1 * cf (gL L)‖ = 1 := by
    intro L hL
    obtain ⟨h1, h2, h3⟩ := hgL L hL
    obtain ⟨e1, e2, -⟩ := hepcf 1 (stdL _ _) (gL L) L (one_mem _) (Red.trivAt_one _ _) hstdFG
      (by rw [Red.fmtC_one]; exact Red.isMov_one _) h1 h2 (fg_of_mem_lats Lv hL) h3
    rw [norm_mul, e1, e2, one_mul]

  have hFa : ∀ L ∈ Lv.lats, ∀ a ∈ GinfC T, ‖F L (C.xB (C.mvB a B))‖ ≤ K := by
    intro L hL a ha
    have h := hKφ (gL L * a)
    rw [hFφ L hL a ha, norm_mul, norm_mul, hz1 a ha, hec L hL, one_mul, one_mul] at h
    exact h
  refine ⟨K, fun L hL x hx => ?_⟩
  obtain ⟨hON, hbB, hxe, hdm, -⟩ := hob x hx
  obtain ⟨a, ha, hax⟩ := (GlobalTheory.AdSpan.ConjHol.unitFr_conj_moved D S T C B hB).2.1 (o x) hON
  have hox : o x ∈ C.X.dom := hax ▸ hdom a
  have hFo : ‖F L (o x)‖ ≤ K := hax ▸ hFa L hL a ha
  set la := wtOf C.X C.hr c c' S.rank with hla
  have hval : F L x = bchar la (b x) * F L (o x) := by
    have := hFb L hL (o x) hox (b x) hbB
    rw [← hxe] at this
    exact this
  have hprod : ‖bchar la (b x)‖ * ∏ τ, ∏ i, (‖b x τ i i‖ ^ 2) ^ (-(la τ i : ℝ) / 2) = 1 := by
    unfold bchar
    simp_rw [norm_prod, norm_zpow]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun τ _ => ?_
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun i _ => ?_
    exact zpow_mul_rpow_sq _ (norm_pos_iff.2 (diag_ne_zero hbB τ i)) _
  simp only [Data.pnorm]
  simp only [← hdm]
  rw [hval, norm_mul]
  calc ‖bchar la (b x)‖ * ‖F L (o x)‖ * ∏ τ, ∏ i, (‖b x τ i i‖ ^ 2) ^ (-(la τ i : ℝ) / 2)
      = ‖F L (o x)‖ * (‖bchar la (b x)‖ * ∏ τ, ∏ i, (‖b x τ i i‖ ^ 2) ^ (-(la τ i : ℝ) / 2)) := by ring
    _ = ‖F L (o x)‖ := by rw [hprod, mul_one]
    _ ≤ K := hFo

end GlobalTheory.AdSpan.BddForms
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FormsOfBoundedAdelicFunctionNormBoundedStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.forms_of_bounded_adelic_function_norm_bounded : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ B, C.IsB B → ∀ f', C.IsBase Lv B f' → ∀ (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ) (z φ : GA D T → ℂ), (∀ a ∈ GinfC T, RealScal C om B a (z a)) → (∀ γ ∈ GQ T, ∀ g, φ (γ * g) = φ g) → (∀ (k : GA D T) (κ : Lv.J), C.LevK Lv k κ → om (1, k) (C.uVec Lv hn f') = C.uVec Lv hn f' ∧ ∀ g, φ (g * k) = φ g) → ∀ (v₀ : Lt D.host.E T.rank → TF S.rank C.g) (μ : GL (Fin T.rank) D.host.E → Lt D.host.E T.rank → ℂ), (∀ L ∈ Lv.lats, IsVac C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh L)) (v₀ L)) → (∀ γ ∈ Lv.grp, ∀ L ∈ Lv.lats, ∀ k : Lv.J, Lv.Red (fun i => (γ : Matrix (Fin T.rank) (Fin T.rank) D.host.E) *ᵥ Lv.β i) k → wG C.X C.bas C.idx γ (v₀ L) = (μ γ L * (Lv.lam k : ℂˣ)) • v₀ (mapL γ L)) → ∀ (ep : GA D S → ℂ) (cf : GA D T → ℂ), (∀ (h : GA D S) (Λ : Lt D.host.E S.rank) (g : GA D T) (L : Lt D.host.E T.rank), h ∈ GfC S → TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ → g ∈ GfC T → TrivAt T (C.under Lv) g → L.FG → IsMov (fmt T g) C.X.Λ L → ‖ep h‖ = 1 ∧ ‖cf g‖ = 1 ∧ om (h, g) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) = (ep h * cf g) • (C.Th (C.xB B) (Lv.phi C.bas hn v₀ L Λ))) → ∀ gL : Lt D.host.E T.rank → GA D T, (∀ L ∈ Lv.lats, gL L ∈ GfC T ∧ TrivAt T (C.under Lv) (gL L) ∧ IsMov (fmt T (gL L)) C.X.Λ L) → ∀ F : Lt D.host.E T.rank → Frame C.X.Ψ T.rank → ℂ, (∀ L ∈ Lv.lats, DifferentiableOn ℂ (F L) C.X.dom) → (∀ L ∈ Lv.lats, ∀ x ∈ C.X.dom, ∀ b ∈ Bor C.X.Ψ T.rank, F L (rmul x b) = bchar (wtOf C.X C.hr c c' S.rank) b * F L x) → (∀ L ∈ Lv.lats, ∀ a ∈ GinfC T, φ (gL L * a) = z a * (ep 1 * cf (gL L)) * F L (C.xB (C.mvB a B))) → (∃ K : ℝ, ∀ g, ‖φ g‖ ≤ K) → ∃ K : ℝ, ∀ L ∈ Lv.lats, ∀ x ∈ C.X.dom, C.X.pnorm (wtOf C.X C.hr c c' S.rank) (F L) x ≤ K := by
  first | exact @GlobalTheory.AdSpan.BddForms.pnorm_le_of_bdd | exact GlobalTheory.AdSpan.BddForms.pnorm_le_of_bdd | (intros; apply GlobalTheory.AdSpan.BddForms.pnorm_le_of_bdd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSeriesFockVectorInvariance
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSeriesFockVectorInvariance
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.ThInv

theorem fvec_val_inv : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ∀ (Lv : SW.Level C.X) (h : GA D S) (B : C.Bas), C.IsB B → ∀ u : WO S T → ℂ, C.IsTh u → ∀ Q : MvPolynomial (FVar D T.rank S.rank) ℂ, (∀ γ ∈ GQ T, ∀ g, om (h, γ * g) (C.fvec B u Q) 0 = om (h, g) (C.fvec B u Q) 0) ∧ ((∀ k, C.LevK Lv k 1 → om (1, k) u = u) → ∀ k, C.LevK Lv k 1 → ∀ g, om (h, g * k) (C.fvec B u Q) 0 = om (h, g) (C.fvec B u Q) 0) := by
  intro D S T C om hW Lv h B hB u hu Q
  have hth : C.IsTh (C.fvec B u Q) := (GlobalTheory.T.fockPolynomialVector_laws D S T C B hB (fun _ => 1) u hu Q).1
  refine ⟨fun γ hγ g => ?_, fun hk k hkL g => ?_⟩
  · have p : ((h, γ * g) : GA D S × GA D T) = (1, γ) * (h, g) := by
      rw [Prod.mk_mul_mk, one_mul]
    rw [p, map_mul, Module.End.mul_apply]
    exact hW.om_aut 1 (one_mem _) γ hγ _ (hW.om_pres _ _ hth)
  · have p : ((h, g * k) : GA D S × GA D T) = (h, g) * (1, k) := by
      rw [Prod.mk_mul_mk, mul_one]
    have hmv := ((GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 B hB).2.2.2.2.2 k
    rw [p, map_mul, Module.End.mul_apply, GlobalTheory.Ker.Red.om_fvec C om hW 1 (one_mem _) k u hu B hB Q,
      hmv.2.2.1 hkL.1, hk k hkL]

end GlobalTheory.Ker.ThInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSeriesFockVectorInvarianceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_series_fock_vector_invariance : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ∀ (Lv : SW.Level C.X) (h : GA D S) (B : C.Bas), C.IsB B → ∀ u : WO S T → ℂ, C.IsTh u → ∀ Q : MvPolynomial (FVar D T.rank S.rank) ℂ, (∀ γ ∈ GQ T, ∀ g, om (h, γ * g) (C.fvec B u Q) 0 = om (h, g) (C.fvec B u Q) 0) ∧ ((∀ k, C.LevK Lv k 1 → om (1, k) u = u) → ∀ k, C.LevK Lv k 1 → ∀ g, om (h, g * k) (C.fvec B u Q) 0 = om (h, g) (C.fvec B u Q) 0) := by
  first | exact @GlobalTheory.Ker.ThInv.fvec_val_inv | exact GlobalTheory.Ker.ThInv.fvec_val_inv | (intros; apply GlobalTheory.Ker.ThInv.fvec_val_inv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSeriesEvalLevelTrivialMulReal
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSeriesEvalLevelTrivialMulReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdSpan.EvalAt

theorem theta_eval : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ (v₀ : Lt D.host.E T.rank → TF S.rank C.g), (∀ L ∈ Lv.lats, IsVac C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh L)) (v₀ L)) → ∀ B, C.IsB B → ∀ (ep : GA D S → ℂ) (cf : GA D T → ℂ), (∀ (h : GA D S) (Λ : Lt D.host.E S.rank) (g : GA D T) (L : Lt D.host.E T.rank), h ∈ GfC S → TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ → g ∈ GfC T → TrivAt T (C.under Lv) g → L.FG → IsMov (fmt T g) C.X.Λ L → ‖ep h‖ = 1 ∧ ‖cf g‖ = 1 ∧ om (h, g) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) = (ep h * cf g) • (C.Th (C.xB B) (Lv.phi C.bas hn v₀ L Λ))) → ∀ z : GA D T → ℂ, (∀ a ∈ GinfC T, RealScal C om B a (z a)) → ∀ (t : ℂ) (h : GA D S) (Λ : Lt D.host.E S.rank), h ∈ GfC S → TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ → ∀ (g : GA D T) (L : Lt D.host.E T.rank), g ∈ GfC T → TrivAt T (C.under Lv) g → L.FG → IsMov (fmt T g) C.X.Λ L → ∀ a ∈ GinfC T, ∀ Q : MvPolynomial (FVar D T.rank S.rank) ℂ, om (h, g * a) (C.fvec B (t • C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) Q) 0 = t * ep h * cf g * z a * thP C.X C.hr C.bas C.idx (Lv.phi C.bas hn v₀ L Λ) (C.toH Q) (C.xB (C.mvB a B)) := by
  intro D S T C om hW Lv hn M hw hM hM𝔪 v₀ hv B hB ep cf hep z hz t h Λ hh hht hΛf hhm g L hg hgt hLf hgm a ha Q
  have hΛ0 : C.X.Λ.FG := C.X.Λ_fg
  have hm1 : IsMov (fmt T 1) C.X.Λ C.X.Λ := by rw [GlobalTheory.Ker.Red.fmt_one]; exact GlobalTheory.Ker.Red.isMov_one _
  have hs1 : IsMov (fmtC S 1) (stdL D.host.E S.rank) (stdL D.host.E S.rank) := by
    rw [GlobalTheory.Ker.Red.fmtC_one]; exact GlobalTheory.Ker.Red.isMov_one _
  obtain ⟨hV, hL⟩ := GlobalTheory.T.self_dual_lattices_at_level D S T C
  have hΛl : C.X.Λ ∈ Lv.lats := (hL Lv 1 _ hΛ0 hm1).2.1 (GlobalTheory.Ker.Red.trivAt_one _ _)
  have hLl : L ∈ Lv.lats := (hL Lv g L hLf hgm).2.1 hgt
  have hsb : ∀ L ∈ Lv.lats, ∀ Λ ∈ Vset D.host.E S.rank M, SW.IsSB (Lv.phi C.bas hn v₀ L Λ) :=
    fun L hL Λ hΛ => (GlobalTheory.T.levelTestFunction_finite_sum_equivariant D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even Lv hn M hM hM𝔪 v₀ hv
      L hL Λ hΛ).1
  have hstd : stdL D.host.E S.rank ∈ Vset D.host.E S.rank M :=
    hV M 1 _ hM (GlobalTheory.Ker.Red.trivAt_one _ _) (GlobalTheory.Ker.Red.stdL_fg _) hs1
  have hφ0 := hsb _ hΛl _ hstd
  have hφ := hsb L hLl Λ (hV M h Λ hM hht hΛf hhm)
  have hJ := (GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2
  have hth : ∀ B', C.IsB B' → ∀ φ : TF S.rank C.g, SW.IsSB φ → C.IsTh (C.Th (C.xB B') φ) :=
    fun B' hB' φ hφ => (GlobalTheory.T.adelicZakTheta_exists_unique D S T C _ (hJ B' hB').2.1 φ hφ).1.1
  have hmv := (hJ B hB).2.2.2.2.2
  have hBa : C.IsB (C.mvB a B) := (hmv a).1
  have hgB : C.mvB g B = B := (hmv g).2.2.1 hg
  have hcomm : a * g = g * a := (((GlobalTheory.T.rational_unitary_group_structure D S T C).2.2.2 T).2.2.2.1 a ha).2.2 g hg
  have p1 : ((h, g * a) : GA D S × GA D T) = (1, a) * (h, g) := by
    rw [Prod.mk_mul_mk, one_mul, hcomm]
  obtain ⟨-, -, e3⟩ := hep h Λ g L hh hht hΛf hhm hg hgt hLf hgm
  rw [(GlobalTheory.T.fockPolynomialVector_laws D S T C B hB (fun _ => 1) _ (hth B hB _ hφ0) Q).2.2.2.2.1, p1, map_mul, Module.End.mul_apply,
    map_smul, GlobalTheory.Ker.Red.om_fvec C om hW h hh g _ (hth B hB _ hφ0) B hB Q, hgB, e3,
    (GlobalTheory.T.fockPolynomialVector_laws D S T C B hB (fun _ => 1) _ (hth B hB _ hφ) Q).2.2.2.2.1, map_smul, map_smul,
    GlobalTheory.Ker.Red.om_fvec C om hW 1 (one_mem _) a _ (hth B hB _ hφ) B hB Q, hz a ha _ hφ,
    (GlobalTheory.T.fockPolynomialVector_laws D S T C _ hBa (fun _ => 1) _ (hth _ hBa _ hφ) Q).2.2.2.2.1]
  simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  rw [((GlobalTheory.T.fockPolynomialVector_testTheta_zero_eq_thetaSeries D S T C).2 _ hBa _ hφ).2 Q]
  ring

end GlobalTheory.AdSpan.EvalAt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSeriesEvalLevelTrivialMulRealStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeries_eval_levelTrivial_mul_real : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ (v₀ : Lt D.host.E T.rank → TF S.rank C.g), (∀ L ∈ Lv.lats, IsVac C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh L)) (v₀ L)) → ∀ B, C.IsB B → ∀ (ep : GA D S → ℂ) (cf : GA D T → ℂ), (∀ (h : GA D S) (Λ : Lt D.host.E S.rank) (g : GA D T) (L : Lt D.host.E T.rank), h ∈ GfC S → TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ → g ∈ GfC T → TrivAt T (C.under Lv) g → L.FG → IsMov (fmt T g) C.X.Λ L → ‖ep h‖ = 1 ∧ ‖cf g‖ = 1 ∧ om (h, g) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) = (ep h * cf g) • (C.Th (C.xB B) (Lv.phi C.bas hn v₀ L Λ))) → ∀ z : GA D T → ℂ, (∀ a ∈ GinfC T, RealScal C om B a (z a)) → ∀ (t : ℂ) (h : GA D S) (Λ : Lt D.host.E S.rank), h ∈ GfC S → TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ → ∀ (g : GA D T) (L : Lt D.host.E T.rank), g ∈ GfC T → TrivAt T (C.under Lv) g → L.FG → IsMov (fmt T g) C.X.Λ L → ∀ a ∈ GinfC T, ∀ Q : MvPolynomial (FVar D T.rank S.rank) ℂ, om (h, g * a) (C.fvec B (t • C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) Q) 0 = t * ep h * cf g * z a * thP C.X C.hr C.bas C.idx (Lv.phi C.bas hn v₀ L Λ) (C.toH Q) (C.xB (C.mvB a B)) := by
  first | exact @GlobalTheory.AdSpan.EvalAt.theta_eval | exact GlobalTheory.AdSpan.EvalAt.theta_eval | (intros; apply GlobalTheory.AdSpan.EvalAt.theta_eval <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSpanThetaSeriesOfBoundedHolomorphic
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.AdSpan.mem_span_thetaSet_of_holUpTo : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → 4 * (Module.finrank ℚ D.host.E * T.rank) + 4 ≤ S.rank → ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ B, C.IsB B → ∀ f', C.IsBase Lv B f' → ∀ (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ) (z φ : GA D T → ℂ), (∀ a ∈ GinfC T, RealScal C om B a (z a)) → HolUpTo C B (ThFr.wtOf C.X C.hr c c' S.rank) z φ → (∀ γ ∈ GQ T, ∀ g, φ (γ * g) = φ g) → (∀ (k : GA D T) (κ : Lv.J), C.LevK Lv k κ → om (1, k) (C.uVec Lv hn f') = C.uVec Lv hn f' ∧ ∀ g, φ (g * k) = φ g) → (∃ K : ℝ, ∀ g, ‖φ g‖ ≤ K) → φ ∈ Submodule.span ℂ (thetaSet C om B (C.uVec Lv hn f') c c') := by
  intro D S T C om hW hsz Lv hn M hw hM hM𝔪 B hB f' hbase c c' z φ hz hhol hγ hk hbdd
  obtain ⟨v₀, μ, hv, hμ⟩ := GlobalTheory.SW.exists_vacua_and_multipliers D.host.E T.rank C.X C.g C.bas C.idx S.rank
    C.sympl C.even Lv
  obtain ⟨ep, cf, hep⟩ := GlobalTheory.T.weilPair_levelTrivial_maps_levelVector D S T C om hW Lv hn M hw hM hM𝔪 v₀ hv B hB
  have hm1 : IsMov (fmt T 1) C.X.Λ C.X.Λ := by rw [GlobalTheory.Ker.Red.fmt_one]; exact GlobalTheory.Ker.Red.isMov_one _
  have hs1 : IsMov (fmtC S 1) (stdL D.host.E S.rank) (stdL D.host.E S.rank) := by
    rw [GlobalTheory.Ker.Red.fmtC_one]; exact GlobalTheory.Ker.Red.isMov_one _
  obtain ⟨hV, hL⟩ := GlobalTheory.T.self_dual_lattices_at_level D S T C
  have hΛl : C.X.Λ ∈ Lv.lats := (hL Lv 1 _ C.X.Λ_fg hm1).2.1 (GlobalTheory.Ker.Red.trivAt_one _ _)
  obtain ⟨t, ht0, hft⟩ := (GlobalTheory.T.levelDatumVector_eq_theta_of_testFunction D S T C Lv hn M hw hM hM𝔪 B hB).1 f' hbase (v₀ C.X.Λ) (hv _ hΛl)
  have hu : C.uVec Lv hn f' = t • C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank)) := by
    rw [hft]; exact ((GlobalTheory.T.levelDatumVector_eq_theta_of_testFunction D S T C Lv hn M hw hM hM𝔪 B hB).2 v₀ hv).2 t
  have hex : ∀ L : Lt D.host.E T.rank, ∃ g : GA D T, L ∈ Lv.lats →
      g ∈ GfC T ∧ TrivAt T (C.under Lv) g ∧ IsMov (fmt T g) C.X.Λ L := by
    intro L
    by_cases hL' : L ∈ Lv.lats
    · obtain ⟨g, hg, h1, h2⟩ := GlobalTheory.Ker.OntoLat.exists_trivAt_mov D S T C Lv L hL'
      exact ⟨g, fun _ => ⟨hg, h1, h2⟩⟩
    · exact ⟨1, fun h => absurd h hL'⟩
  choose gL hgL using hex
  choose Qf hQd hQb hQv using fun L => hhol (gL L)
  have hne : ∀ L ∈ Lv.lats, ep 1 * cf (gL L) ≠ 0 := by
    intro L hL'
    obtain ⟨g1, g2, -⟩ := hep 1 _ (gL L) L (one_mem _) (GlobalTheory.Ker.Red.trivAt_one _ _) (GlobalTheory.Ker.Red.stdL_fg _) hs1
      (hgL L hL').1 (hgL L hL').2.1 hL'.1.1 (hgL L hL').2.2
    refine mul_ne_zero ?_ ?_ <;> intro h0
    · rw [h0, norm_zero] at g1; exact zero_ne_one g1
    · rw [h0, norm_zero] at g2; exact zero_ne_one g2
  let F : Lt D.host.E T.rank → Frame C.X.Ψ T.rank → ℂ := fun L x => Qf L x / (ep 1 * cf (gL L))
  have hFhol : ∀ L ∈ Lv.lats, DifferentiableOn ℂ (F L) C.X.dom := fun L _ => by
    show DifferentiableOn ℂ (fun x => Qf L x / (ep 1 * cf (gL L))) C.X.dom
    simpa only [div_eq_mul_inv] using (hQd L).mul_const (ep 1 * cf (gL L))⁻¹
  have hFbor : ∀ L ∈ Lv.lats, ∀ x ∈ C.X.dom, ∀ b ∈ Bor C.X.Ψ T.rank,
      F L (rmul x b) = bchar (wtOf C.X C.hr c c' S.rank) b * F L x := by
    intro L _ x hx b hb
    show Qf L (rmul x b) / _ = _ * (Qf L x / _)
    rw [hQb L x hx b hb, mul_div_assoc]
  have hFv : ∀ L ∈ Lv.lats, ∀ a ∈ GinfC T,
      φ (gL L * a) = z a * (ep 1 * cf (gL L)) * F L (C.xB (C.mvB a B)) := by
    intro L hL' a ha
    show _ = _ * (Qf L _ / _)
    rw [hQv L a ha, mul_assoc, mul_div_assoc', mul_div_cancel_left₀ _ (hne L hL')]
  have hForm : IsForm C.X Lv.grp Lv.lats μ (wtOf C.X C.hr c c' S.rank) F :=
    ⟨hFhol, hFbor, GlobalTheory.T.readOffForms_automorphic_inverse_multiplier D S T C om hW Lv hn M hw hM hM𝔪 B hB f' hbase c c' z φ hz hγ hk v₀ μ hv hμ ep cf hep
      gL hgL F hFhol hFbor hFv,
     GlobalTheory.T.forms_of_bounded_adelic_function_norm_bounded D S T C om hW Lv hn M hw hM hM𝔪 B hB f' hbase c c' z φ hz hγ hk v₀ μ hv hμ ep cf hep
      gL hgL F hFhol hFbor hFv hbdd⟩
  obtain ⟨m, Λs, P, a, hΛP, hsp⟩ := GlobalTheory.SW.level_theta_span D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx
    S.rank C.sympl C.even hsz Lv hn M hM hM𝔪 v₀ hv μ hμ c c' F hForm
  choose hs hsf hst hsm using fun i => GlobalTheory.T.exists_trivialAtLevel_unitary_transport_selfDual D S T C M hM (Λs i) (hΛP i).1
  have hbij := (GlobalTheory.T.fockPolynomialVector_testTheta_zero_eq_thetaSeries D S T C).1
  let Qs : Fin m → MvPolynomial (FVar D T.rank S.rank) ℂ := fun i => Function.surjInv hbij.2 (P i)
  have hQs : ∀ i, C.toH (Qs i) = P i := fun i => Function.surjInv_eq hbij.2 (P i)
  have hepn : ∀ i, ep (hs i) ≠ 0 := by
    intro i h0
    obtain ⟨g1, -⟩ := hep (hs i) (Λs i) 1 C.X.Λ (hsf i) (hst i) (hΛP i).1.1 (hsm i) (one_mem _)
      (GlobalTheory.Ker.Red.trivAt_one _ _) C.X.Λ_fg hm1
    rw [h0, norm_zero] at g1; exact zero_ne_one g1
  let Θ : Fin m → GA D T → ℂ := fun i g => om (hs i, g) (C.fvec B (C.uVec Lv hn f') (Qs i)) 0
  let ψ : GA D T → ℂ := ∑ i, (a i * ep 1 / (t * ep (hs i))) • Θ i
  have hψ : ∀ g, ψ g = ∑ i, (a i * ep 1 / (t * ep (hs i))) * Θ i g := by
    intro g; simp only [ψ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hψmem : ψ ∈ Submodule.span ℂ (thetaSet C om B (C.uVec Lv hn f') c c') :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨hs i, Qs i, by rw [hQs i]; exact (hΛP i).2, rfl⟩)
  suffices hφψ : φ = ψ by rw [hφψ]; exact hψmem
  set u0 := C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank)) with hu0
  have hJ := (GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2
  have hstd : stdL D.host.E S.rank ∈ Vset D.host.E S.rank M :=
    hV M 1 _ hM (GlobalTheory.Ker.Red.trivAt_one _ _) (GlobalTheory.Ker.Red.stdL_fg _) hs1
  have hth0 : C.IsTh u0 := (GlobalTheory.T.adelicZakTheta_exists_unique D S T C _ (hJ B hB).2.1 _
    (GlobalTheory.T.levelTestFunction_finite_sum_equivariant D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even Lv hn M hM hM𝔪 v₀ hv
      C.X.Λ hΛl _ hstd).1).1.1
  have hΘ : ∀ i g, Θ i g = t * om (hs i, g) (C.fvec B u0 (Qs i)) 0 := by
    intro i g
    show om (hs i, g) (C.fvec B (C.uVec Lv hn f') (Qs i)) 0 = _
    rw [hu, (GlobalTheory.T.fockPolynomialVector_laws D S T C B hB (fun _ => 1) u0 hth0 (Qs i)).2.2.2.2.1 t, map_smul, Pi.smul_apply,
      smul_eq_mul]
  have hk0 : ∀ k, C.LevK Lv k 1 → om (1, k) u0 = u0 := by
    intro k hk'
    have e := (hk k 1 hk').1
    rw [hu, map_smul] at e
    exact smul_right_injective _ ht0 e
  have hinv := fun i => GlobalTheory.T.theta_series_fock_vector_invariance D S T C om hW Lv (hs i) B hB u0 hth0 (Qs i)
  have hψγ : ∀ γ ∈ GQ T, ∀ g, ψ (γ * g) = ψ g := by
    intro γ hγ' g
    rw [hψ, hψ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hΘ, hΘ, (hinv i).1 γ hγ' g]
  have hψk : ∀ k, C.LevK Lv k 1 → ∀ g, ψ (g * k) = ψ g := by
    intro k hk' g
    rw [hψ, hψ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hΘ, hΘ, (hinv i).2 hk0 k hk' g]
  have hag : ∀ L ∈ Lv.lats, ∀ a ∈ GinfC T, φ (gL L * a) = ψ (gL L * a) := by
    intro L hL' a ha
    have hx : C.xB (C.mvB a B) ∈ C.X.dom := (hJ _ ((hJ B hB).2.2.2.2.2 a).1).2.1
    have hev : ∀ i, Θ i (gL L * a) = t * ep (hs i) * cf (gL L) * z a *
        thP C.X C.hr C.bas C.idx (Lv.phi C.bas hn v₀ L (Λs i)) (P i) (C.xB (C.mvB a B)) := by
      intro i
      show om _ (C.fvec B (C.uVec Lv hn f') _) 0 = _
      rw [hu, GlobalTheory.T.thetaSeries_eval_levelTrivial_mul_real D S T C om hW Lv hn M hw hM hM𝔪 v₀ hv B hB ep cf hep z hz t (hs i) (Λs i) (hsf i) (hst i)
        (hΛP i).1.1 (hsm i) (gL L) L (hgL L hL').1 (hgL L hL').2.1 hL'.1.1 (hgL L hL').2.2 a ha (Qs i), hQs i]
    rw [hFv L hL' a ha, hψ, hsp L hL' _ hx, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hev i]
    have h1 := hepn i
    field_simp
  exact GlobalTheory.T.eq_of_rational_level_invariant_agree_chosen D S T C Lv M hM hM𝔪 gL hgL φ ψ hγ hψγ (fun k hk' => (hk k 1 hk').2) hψk hag
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSpanThetaSeriesOfBoundedHolomorphicStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_thetaSeries_of_boundedHolomorphic : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → 4 * (Module.finrank ℚ D.host.E * T.rank) + 4 ≤ S.rank → ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ B, C.IsB B → ∀ f', C.IsBase Lv B f' → ∀ (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ) (z φ : GA D T → ℂ), (∀ a ∈ GinfC T, RealScal C om B a (z a)) → HolUpTo C B (ThFr.wtOf C.X C.hr c c' S.rank) z φ → (∀ γ ∈ GQ T, ∀ g, φ (γ * g) = φ g) → (∀ (k : GA D T) (κ : Lv.J), C.LevK Lv k κ → om (1, k) (C.uVec Lv hn f') = C.uVec Lv hn f' ∧ ∀ g, φ (g * k) = φ g) → (∃ K : ℝ, ∀ g, ‖φ g‖ ≤ K) → φ ∈ Submodule.span ℂ (thetaSet C om B (C.uVec Lv hn f') c c') := by
  first | exact @GlobalTheory.AdSpan.mem_span_thetaSet_of_holUpTo | exact GlobalTheory.AdSpan.mem_span_thetaSet_of_holUpTo | (intros; apply GlobalTheory.AdSpan.mem_span_thetaSet_of_holUpTo <;> assumption)
end
