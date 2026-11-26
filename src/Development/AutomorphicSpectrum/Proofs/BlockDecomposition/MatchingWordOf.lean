module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingUnitOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HintConstMul
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermMultiplicative
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SiegelSetUnitary
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteUnitaryMultiplication
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleCosetMultiplication
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingTransferOf

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingWordOf
noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F
open PositivityTheory.Rg.BcB.F.U (lpow lone)
open PositivityTheory.Rg.BcB.F.MLM (wordL wordU)
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.MatchWord

section Generic

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

omit [TopologicalSpace H] [IsTopologicalGroup H] in
theorem hint_mul_right (K : Subgroup H) (u : H → ℂ) (c : ℂ) : hint K (fun x => u x * c) = hint K u * c := by
  rw [mul_comm, ← GlobalTheory.CompanionTheory.ActTr.hint_const_mul]
  simp only [mul_comm]

theorem conv_assoc {K : Subgroup H} (hK : IsCompact (K : Set H)) (hO : IsOpen (K : Set H)) {f g k : H → ℂ}
    (hf : IsHecke K f) (hg : IsHecke K g) (hk : IsHecke K k) (y : H) :
    hint K (fun z => hint K (fun x => f x * g (x⁻¹ * z)) * k (z⁻¹ * y)) =
      hint K (fun x => f x * hint K (fun z => g z * k (z⁻¹ * (x⁻¹ * y)))) := by
  have hC₁ : IsCompact ((fun t => y * t⁻¹) '' tsupport k) :=
    IsCompact.image hk.1 (continuous_const.mul continuous_inv)
  have h₁ : ∀ l ∈ K, ∀ z x, f x * g (x⁻¹ * (z * l)) * k ((z * l)⁻¹ * y) = f x * g (x⁻¹ * z) * k (z⁻¹ * y) := by
    intro l hl z x
    have e : (z * l)⁻¹ * y = l⁻¹ * (z⁻¹ * y) := by group
    have e2 : x⁻¹ * (z * l) = x⁻¹ * z * l := by group
    rw [e, e2, (hg.2 l hl _).2, (hk.2 l⁻¹ (inv_mem hl) _).1]
  have h₂ : ∀ l ∈ K, ∀ z x, f (x * l) * g ((x * l)⁻¹ * z) * k (z⁻¹ * y) = f x * g (x⁻¹ * z) * k (z⁻¹ * y) := by
    intro l hl z x
    have e : (x * l)⁻¹ * z = l⁻¹ * (x⁻¹ * z) := by group
    rw [e, (hf.2 l hl x).2, (hg.2 l⁻¹ (inv_mem hl) _).1]
  have h₃ : ∀ z x, f x * g (x⁻¹ * z) * k (z⁻¹ * y) ≠ 0 →
      z ∈ (fun t => y * t⁻¹) '' tsupport k ∧ x ∈ tsupport f := by
    intro z x h
    refine ⟨⟨z⁻¹ * y, subset_tsupport _ (right_ne_zero_of_mul h), by group⟩,
      subset_tsupport _ (left_ne_zero_of_mul (left_ne_zero_of_mul h))⟩
  have e := GlobalTheory.CompanionTheory.ActTr.hint_comm hK hO le_rfl hC₁ hK hO le_rfl hf.1
    (fun z x => f x * g (x⁻¹ * z) * k (z⁻¹ * y)) h₁ h₂ h₃
  calc hint K (fun z => hint K (fun x => f x * g (x⁻¹ * z)) * k (z⁻¹ * y))
      = hint K (fun z => hint K (fun x => f x * g (x⁻¹ * z) * k (z⁻¹ * y))) := by
        congr 1
        funext z
        rw [hint_mul_right]
    _ = hint K (fun x => hint K (fun z => f x * g (x⁻¹ * z) * k (z⁻¹ * y))) := e
    _ = _ := by
        congr 1
        funext x
        have e' : (fun z => f x * g (x⁻¹ * z) * k (z⁻¹ * y)) =
            fun z => f x * (fun t => g t * k (t⁻¹ * (x⁻¹ * y))) (x⁻¹ * z) := by
          funext z
          have e2 : (x⁻¹ * z)⁻¹ * (x⁻¹ * y) = z⁻¹ * y := by group
          simp only [e2, mul_assoc]
        rw [e', GlobalTheory.CompanionTheory.ActTr.hint_const_mul, GlobalTheory.CompanionTheory.CtMulSplit.hint_left K x⁻¹ (fun t => g t * k (t⁻¹ * (x⁻¹ * y)))]

end Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem lconv_assoc (hE : Unr E) {w : Pl E} {f g k : UL n w → ℂ} (hf : IsHecke (KL n w) f) (hg : IsHecke (KL n w) g)
    (hk : IsHecke (KL n w) k) : lconv (lconv f g) k = lconv f (lconv g k) := by
  funext y
  exact conv_assoc (GlobalTheory.CompanionTheory.SphLine.isCompact_KL hE n w) (GlobalTheory.CompanionTheory.SphLine.isOpen_KL n w) hf hg hk y

theorem lconv_lone_left {w : Pl E} {f : UL n w → ℂ} (hf : IsHecke (KL n w) f) : lconv (lone (KL n w)) f = f := by
  funext m
  exact GlobalTheory.CompanionTheory.FmPowP.hint_ind_left _ _ le_rfl (by simp [Subgroup.relIndex_self]) f (fun u hu g => (hf.2 u hu g).1) m

theorem lconv_lone_right {w : Pl E} {f : UL n w → ℂ} (hf : IsHecke (KL n w) f) : lconv f (lone (KL n w)) = f := by
  funext m
  exact GlobalTheory.CompanionTheory.FmPowP.hint_ind_right _ _ le_rfl (by simp [Subgroup.relIndex_self]) f (fun u hu g => (hf.2 u hu g).2) m

theorem isHecke_ctMu {a b : ℕ} (h : a + b = n) {w : Pl E} (hU : UL n w = ⊤) (μ : (w.adicCompletion E)ˣ →* ℂˣ)
    (hμ : ∀ u : (w.adicCompletion E)ˣ, ordL (u : w.adicCompletion E) = 0 → μ u = 1) {f : UL n w → ℂ}
    (hf : IsHecke (KL n w) f) : IsHecke (K2 a b w) (ctMu h w μ f) := by
  have hH := GlobalTheory.CompanionTheory.CtMulSplit.isHk_of_isHecke hU hf
  set F : GLw n w → ℂ := fun y => f (toSub (UL n w) y) with hF
  have hb : ∀ u ∈ GlobalTheory.LFun.KGL w (n := n), ∀ g, F (u * g) = F g ∧ F (g * u) = F g := fun u hu g =>
    ⟨by simpa using hH.2.2.2 u hu 1 (Subgroup.one_mem _) g, by simpa using hH.2.2.2 1 (Subgroup.one_mem _) u hu g⟩
  have hbi := GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.constant_term_bi_invariant (a := a) (b := b) h w (GlobalTheory.LFun.KGL w (n := n)) le_rfl
    (fun k hk k' hk' => mul_mem (mul_mem hk hk') (inv_mem hk)) F hH.2.2.2 1 1 (one_mem _) (one_mem _)
  have hone : (1 : GLw a w × GLw b w) ∈ leviOf h w (GlobalTheory.LFun.KGL w (n := n)) := GlobalTheory.CompanionTheory.CtHecke.blk_zero_mem h w (one_mem _)
  have e : ctMu h w μ f = fun m => GlobalTheory.CompanionTheory.CtHecke.cMu μ m * phi3 h w F 1 1 m := by
    funext m
    show GlobalTheory.CompanionTheory.CtHecke.cMu μ m * ct h w F m = _
    rw [GlobalTheory.CompanionTheory.CtMulSplit.constant_term_eq_mackey_entry h w hb]
  rw [e]
  refine ⟨?_, fun κ hκ x => ⟨?_, ?_⟩⟩
  · exact (GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.constant_term_compact_support h w _ hH.2.2.1 1 1).mul_left
  · have := hbi κ 1 (GlobalTheory.CompanionTheory.CtHecke.blk_zero_mem h w hκ) hone x
    rw [mul_one] at this
    simp only [GlobalTheory.CompanionTheory.CtHecke.cMu_mul_left hμ hκ, this]
  · have := hbi 1 κ hone (GlobalTheory.CompanionTheory.CtHecke.blk_zero_mem h w hκ) x
    rw [one_mul] at this
    simp only [GlobalTheory.CompanionTheory.CtHecke.cMu_mul_right hμ hκ, this]

theorem isHecke_hU (d : LocData E n) (hd : d.Ok) {w : Pl E} (hU : UL n w = ⊤) (k : ℕ) : IsHecke (KL n w) (d.hU w k) := by
  have h0 : (d.ϖ w : w.adicCompletion E) ≠ 0 := (d.ϖ w).ne_zero
  have hϖ : IsUnifV E w (d.ϖ w : w.adicCompletion E) := GlobalTheory.CompanionTheory.CtHecke.isUnifV_of_ordL h0 (hd.unif w)
  have hT := Tj_mem_hecke (n := n) hϖ k
  have hcl : IsClosed ((UL n w : Subgroup (GLw n w)) : Set (GLw n w)) := by
    rw [hU]
    exact isClosed_univ
  refine ⟨(GlobalTheory.CompanionTheory.CtHecke.hasCompactSupport_Tj h0 k).comp_isClosedEmbedding hcl.isClosedEmbedding_subtypeVal,
    fun κ hκ x => ⟨?_, ?_⟩⟩
  · have := hT.1 ⟨κ.1, hκ⟩ 1 x.1
    simpa [LocData.hU] using this
  · have := hT.1 1 ⟨κ.1, hκ⟩ x.1
    simpa [LocData.hU] using this

theorem hc_eq (d : LocData E n) (a : ℕ) (ha : a ≤ n) {w : Pl E}
    (hμ : ∀ u : (w.adicCompletion E)ˣ, ordL (u : w.adicCompletion E) = 0 → d.μ w u = 1) (k : ℕ) :
    d.hc a ha w k = ctMu (Nat.add_sub_cancel' ha) w (d.μ w) (d.hU w k) := by
  have h1 : d.sgn a w = 1 := by
    unfold LocData.sgn
    rw [map_pow, hμ _ (GlobalTheory.CompanionTheory.CtMulSplit.ordL_neg_one w)]
    simp
  unfold LocData.hc
  rw [h1, inv_one, one_smul]
  rfl

theorem word_ct (d : LocData E n) (a : ℕ) (ha : a ≤ n) {w : Pl E} (hCt : MT.CtMul) (hSp : SphComm) (hE : Unr E)
    (hd : d.Ok) (hG : d.Good w) (l : List (ℕ × Bool)) :
    IsHecke (KL n w) (wordU d w l) ∧ ∃ A B : UL n w → ℂ, IsHecke (KL n w) A ∧ IsHecke (KL n w) B ∧
      (wordL d a ha w l).s w = ctMu (Nat.add_sub_cancel' ha) w (d.μ w) A ∧
      (wordL d a ha w l).t w = ctMu (Nat.add_sub_cancel' ha) w (d.μ w) B ∧
      mconv (ctMu (Nat.add_sub_cancel' ha) w (d.μ w) A) (ctMu (Nat.add_sub_cancel' ha) w (d.μ w) B) =
        ctMu (Nat.add_sub_cancel' ha) w (d.μ w) (wordU d w l) := by
  obtain ⟨hw, hT, hS₀, hBad, hμ⟩ := hG
  have hU : UL n w = ⊤ := if_pos hw
  set C := ctMu (Nat.add_sub_cancel' ha) w (d.μ w) with hC
  have conv : ∀ {f g : UL n w → ℂ}, IsHecke (KL n w) f → IsHecke (KL n w) g → IsHecke (KL n w) (lconv f g) :=
    fun hf hg => GlobalTheory.CompanionTheory.UnitaryWord.isHecke_lconv GlobalTheory.CompanionTheory.LocHecke.locAlg (GlobalTheory.CompanionTheory.MatchPowers.isLevel_KL n w) hf hg
  have mul : ∀ {f g : UL n w → ℂ}, IsHecke (KL n w) f → IsHecke (KL n w) g → C (lconv f g) = mconv (C f) (C g) :=
    fun hf hg => hCt E n a ha w hw (d.μ w) hμ _ _ hf hg
  have hone : IsHecke (KL n w) (lone (KL n w)) := GlobalTheory.CompanionTheory.MatchUnit.isHecke_lone_KL hE
  have hunit : C (lone (KL n w)) = PositivityTheory.Rg.BcB.F.idem (K2 a (n - a) w) := GlobalTheory.CompanionTheory.MatchUnit.ctMu_lone _ hU _ hμ
  have hlev : d.lev a w = K2 a (n - a) w := by
    unfold LocData.lev
    rw [if_neg hT, if_neg (by simp [hS₀, hBad])]
  have hlev₂ : d.lev₂ a w = K2 a (n - a) w := by
    unfold LocData.lev₂
    rw [if_neg (by simp [hS₀, hBad])]
  have hes : (d.eL a).s w = C (lone (KL n w)) := by
    rw [hunit]
    show PositivityTheory.Rg.BcB.F.idem (d.lev a w) = _
    rw [hlev]
  have het : (d.eL a).t w = C (lone (KL n w)) := by
    rw [hunit]
    show PositivityTheory.Rg.BcB.F.idem (d.lev₂ a w) = _
    rw [hlev₂]
  induction l with
  | nil =>
    refine ⟨?_, lone (KL n w), lone (KL n w), hone, hone, hes, het, ?_⟩
    · show IsHecke (KL n w) ((KL n w : Set (UL n w)).indicator 1)
      rw [GlobalTheory.CompanionTheory.UnitaryWord.lone_KL] at hone
      exact hone
    · rw [← mul hone hone, lconv_lone_left hone, GlobalTheory.CompanionTheory.UnitaryWord.lone_KL]
      rfl
  | cons x l ih =>
    obtain ⟨hW, A, B, hA, hB, hs, ht, hm⟩ := ih
    obtain ⟨k, intersection_update_fsHerm_neg_one⟩ := x
    have hTk := isHecke_hU d hd hU k
    have hck : d.hc a ha w k = C (d.hU w k) := hc_eq d a ha hμ k
    have hWc : wordU d w ((k, intersection_update_fsHerm_neg_one) :: l) = lconv (d.hU w k) (wordU d w l) := rfl
    have key : mconv (C (lconv (d.hU w k) A)) (C B) = C (lconv (d.hU w k) (wordU d w l)) := by
      rw [← mul (conv hTk hA) hB, lconv_assoc hE hTk hA hB, mul hTk (conv hA hB), mul hA hB, hm, ← mul hTk hW]
    refine ⟨hWc ▸ conv hTk hW, ?_⟩
    rw [hWc]
    cases intersection_update_fsHerm_neg_one with
    | false =>
      refine ⟨lconv (d.hU w k) A, B, conv hTk hA, hB, ?_, ?_, key⟩
      · show mconv ((d.hL a ha w k false).s w) ((wordL d a ha w l).s w) = _
        have e : (d.hL a ha w k false).s w = d.hc a ha w k := by simp [LocData.hL]
        rw [e, hs, hck, ← mul hTk hA]
      · show mconv ((d.eL a).t w) ((wordL d a ha w l).t w) = _
        rw [het, ht, ← mul hone hB, lconv_lone_left hB]
    | true =>
      refine ⟨A, lconv (d.hU w k) B, hA, conv hTk hB, ?_, ?_, ?_⟩
      · show mconv ((d.eL a).s w) ((wordL d a ha w l).s w) = _
        rw [hes, hs, ← mul hone hA, lconv_lone_left hA]
      · show mconv ((d.hL a ha w k true).t w) ((wordL d a ha w l).t w) = _
        have e : (d.hL a ha w k true).t w = d.hc a ha w k := by simp [LocData.hL]
        rw [e, ht, hck, ← mul hTk hB]
      · rw [← mul hA (conv hTk hB), ← lconv_assoc hE hA hTk hB, mul (conv hA hTk) hB, mul hA hTk,
          hSp E a (n - a) w (C A) (C (d.hU w k)) (isHecke_ctMu _ hU _ hμ hA) (isHecke_ctMu _ hU _ hμ hTk),
          ← mul hTk hA]
        exact key

end GlobalTheory.CompanionTheory.MatchWord

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cocompactness
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cocompactness
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU PositivityTheory.Rg.Mass

namespace GlobalTheory.CompanionTheory.MassCocompact

theorem coCpt : CoCpt := by
  intro F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hCM hJ hA _ _ hμ h𝓕 _ _
  have hW : GlobalTheory.SiegelSet.IsWittFrame σ J (0 : Matrix (Fin 2) (Fin 0) E) 0 :=
    ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _, fun z _ _ hz => hA z hz⟩
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.SiegelSet.Model.compact_quotient GlobalTheory.CompanionTheory.SiegelRed.siegelSetUnitary hCM hJ hW
  refine ⟨⟨C, hC, fun h => ?_⟩, ?_, ?_⟩
  · obtain ⟨γ, hγ, c, hc, e⟩ := hcov h
    exact ⟨⟨γ, hγ⟩, c, hc, e⟩
  · exact (GlobalTheory.SiegelWeilConvCompare.measure_fundamentalDomain_pos F E σ 2 J μ hμ 𝓕 h𝓕).ne'
  · exact (((GlobalTheory.CompanionTheory.SW.finVol_unitaryGroup F E σ hCM 2 J hJ).2 μ hμ).2 𝓕 h𝓕).ne

end GlobalTheory.CompanionTheory.MassCocompact

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CocompactnessStatement
open PositivityTheory.Rg.Mass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocompactness : CoCpt := by
  first | exact @GlobalTheory.CompanionTheory.MassCocompact.coCpt | exact GlobalTheory.CompanionTheory.MassCocompact.coCpt | (intros; apply GlobalTheory.CompanionTheory.MassCocompact.coCpt <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingSecondBlockOf
noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.Bc.ArchbcB.B
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.MatchLMPlaces

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.MLM PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcN.F2 (mconv phi3 gconv leviOf IsHk)
open PositivityTheory.Rg.BcB.F.Eig (lconv)
open PositivityTheory.Rg.BcB.F.U (lpow lone)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem mconv_mul_mul {a b : ℕ} {w : Pl E} (r s : ℂ) (u v : GLw a w × GLw b w → ℂ) :
    mconv (fun y => r * u y) (fun y => s * v y) = fun y => (r * s) * mconv u v y := by
  funext y
  unfold mconv
  rw [← GlobalTheory.CompanionTheory.TailLocPow.hint_smul]
  congr 1
  funext z
  ring

theorem lconv_mul_mul {w : Pl E} (r s : ℂ) (u v : UL n w → ℂ) :
    lconv (fun y => r * u y) (fun y => s * v y) = fun y => (r * s) * lconv u v y := by
  funext y
  unfold lconv
  rw [← GlobalTheory.CompanionTheory.TailLocPow.hint_smul]
  congr 1
  funext z
  ring

section S0

variable (d : LocData E n) {a : ℕ} (ha : a ≤ n) {w : Pl E}

end S0

section T

variable (d : LocData E n) {a : ℕ} (ha : a ≤ n) {w : Pl E}

abbrev cc (d : LocData E n) (w : Pl E) : ↥(d.c w).support → ℂ := fun j => d.c w j.1

abbrev xx (d : LocData E n) (w : Pl E) : ↥(d.c w).support → Fin n → ℤ := fun j => j.1

theorem qT_eq (s : Finset (Fin (n / 2))) :
    d.qT a w s = fun y => (((Tail.I2 a (n - a) w).relIndex (K2 a (n - a) w) : ℕ) : ℂ) *
      MT.entT n w (d.ϖ w) a (cc d w) (xx d w) s y := by
  funext y
  unfold LocData.qT MT.entT
  by_cases h : LocData.admitted n a s
  · have h' : MT.admitted n a s := ⟨h.1.1, h.1.2.1, h.1.2.2, h.2.1, h.2.2⟩
    rw [dite_eq_left h, dite_eq_left h', Finsupp.sum, Finset.mul_sum, ← Finset.sum_coe_sort (d.c w).support]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold Tail.dc2
    ring
  · have h' : ¬ MT.admitted n a s := fun h' => h ⟨⟨h'.1, h'.2.1, h'.2.2.1⟩, h'.2.2.2.1, h'.2.2.2.2⟩
    rw [dite_eq_right h, dite_eq_right h', mul_zero]

theorem mpow_scale {b : ℕ} (r : ℂ) (u : GLw a w × GLw b w → ℂ) (k : ℕ) :
    MT.mpow w (fun y => r * u y) k = fun y => r ^ k * MT.mpow w u k y := by
  induction k with
  | zero =>
    funext y
    simp [MT.mpow]
  | succ k ih =>
    show mconv _ (MT.mpow w _ k) = _
    rw [ih, mconv_mul_mul]
    funext y
    show _ = r ^ (k + 1) * mconv u (MT.mpow w u k) y
    ring

theorem lpow_scale (K : Subgroup (UL n w)) (r : ℂ) (g : UL n w → ℂ) (k : ℕ) :
    lpow K (fun y => r * g y) k = fun y => r ^ k * lpow K g k y := by
  induction k with
  | zero =>
    funext y
    simp [U.lpow]
  | succ k ih =>
    show lconv _ (lpow K _ k) = _
    rw [ih, lconv_mul_mul]
    funext y
    show _ = r ^ (k + 1) * lconv g (lpow K g k) y
    ring

theorem unitary_function_at_T (hT : w ∈ d.T) : d.g₀ w = fun y => (((iwU n w (d.b w)).relIndex (KL n w) : ℕ) : ℂ) *
    ∑ j, cc d w j * fU n w (d.b w) (d.ϖ w) (lOf (xx d w j)) y := by
  have h : d.g₀ w = fun y => (d.c w).sum fun x t =>
      t * (((iwU n w (d.b w)).relIndex (KL n w) : ℕ) : ℂ) * fU n w (d.b w) (d.ϖ w) (lOf x) y := by
    unfold LocData.g₀
    rw [if_pos hT]
  rw [h]
  funext y
  rw [Finsupp.sum, Finset.mul_sum, ← Finset.sum_coe_sort (d.c w).support]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end T

end GlobalTheory.CompanionTheory.MatchLMPlaces

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriHeckeSumAdditive
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriHeckeSumAdditive
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open GlobalTheory.CompanionTheory.DcosProduct (dc mem_dc_mul inv_mul_mem_of_dc tdiag_add conj_entry)
open PositivityTheory.Rg.BcN.F2 (hconv hk IsHk)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.IwHeckeMul

section Abstract

variable {G : Type} [Group G]

theorem fibre_coset {I : Subgroup G} {t t' : G}
    (hf : ∀ g ∈ I, ∃ a ∈ I, ∃ b ∈ I, g = a * b ∧ t * a * t⁻¹ ∈ I ∧ t'⁻¹ * b * t' ∈ I)
    (hc : ∀ g ∈ I, (t * t')⁻¹ * g * (t * t') ∈ I → t⁻¹ * g * t ∈ I)
    {i i' z : G} (hi : i ∈ I) (hi' : i' ∈ I) (h1 : z ∈ dc I t)
    (h2 : z⁻¹ * (i * (t * t') * i') ∈ dc I t') : (i * t)⁻¹ * z ∈ I := by
  have h1' : i⁻¹ * z ∈ dc I t := by
    obtain ⟨x, hx, y, hy, rfl⟩ := h1
    exact ⟨i⁻¹ * x, mul_mem (inv_mem hi) hx, y, hy, by group⟩
  have h2' : (i⁻¹ * z)⁻¹ * (t * t') ∈ dc I t' := by
    obtain ⟨x, hx, y, hy, e⟩ := h2
    refine ⟨x, hx, y * i'⁻¹, mul_mem hy (inv_mem hi'), ?_⟩
    have : (i⁻¹ * z)⁻¹ * (t * t') = z⁻¹ * (i * (t * t') * i') * i'⁻¹ := by group
    rw [this, e]; group
  have := inv_mul_mem_of_dc hf hc h1' h2'
  have e : (i * t)⁻¹ * z = t⁻¹ * (i⁻¹ * z) := by group
  rwa [e]

theorem conv_dc {I : Subgroup G} {t t' : G}
    (hf : ∀ g ∈ I, ∃ a ∈ I, ∃ b ∈ I, g = a * b ∧ t * a * t⁻¹ ∈ I ∧ t'⁻¹ * b * t' ∈ I)
    (hc : ∀ g ∈ I, (t * t')⁻¹ * g * (t * t') ∈ I → t⁻¹ * g * t ∈ I)
    {e e' e'' : G → ℂ} (he : ∀ y, (y ∈ dc I t → e y = 1) ∧ (y ∉ dc I t → e y = 0))
    (he' : ∀ y, (y ∈ dc I t' → e' y = 1) ∧ (y ∉ dc I t' → e' y = 0))
    (he'' : ∀ y, (y ∈ dc I (t * t') → e'' y = 1) ∧ (y ∉ dc I (t * t') → e'' y = 0)) (m : G) :
    ∑ᶠ q : G ⧸ I, e q.out * e' (q.out⁻¹ * m) = e'' m := by
  by_cases hm : m ∈ dc I (t * t')
  · rw [(he'' m).1 hm]
    obtain ⟨i, hi, i', hi', rfl⟩ := hm
    rw [finsum_eq_single _ (((i * t : G)) : G ⧸ I)]
    · have hz : (i * t)⁻¹ * (((i * t : G)) : G ⧸ I).out ∈ I :=
        QuotientGroup.eq.1 (QuotientGroup.out_eq' _).symm
      obtain ⟨z, hzd⟩ : ∃ z, z = (((i * t : G)) : G ⧸ I).out := ⟨_, rfl⟩
      rw [← hzd] at hz ⊢
      have h1 : z ∈ dc I t := ⟨i, hi, _, hz, by group⟩
      have h2 : z⁻¹ * (i * (t * t') * i') ∈ dc I t' :=
        ⟨((i * t)⁻¹ * z)⁻¹, inv_mem hz, i', hi', by group⟩
      rw [(he _).1 h1, (he' _).1 h2, one_mul]
    · intro q hq
      by_cases h1 : q.out ∈ dc I t
      · by_cases h2 : q.out⁻¹ * (i * (t * t') * i') ∈ dc I t'
        · exfalso
          apply hq
          rw [← QuotientGroup.out_eq' q]
          exact (QuotientGroup.eq.2 (fibre_coset hf hc hi hi' h1 h2)).symm
        · rw [(he' _).2 h2, mul_zero]
      · rw [(he _).2 h1, zero_mul]
  · rw [(he'' m).2 hm]
    refine finsum_eq_zero_of_forall_eq_zero fun q => ?_
    by_cases h1 : q.out ∈ dc I t
    · by_cases h2 : q.out⁻¹ * m ∈ dc I t'
      · exact absurd (mem_dc_mul hf h1 h2) hm
      · rw [(he' _).2 h2, mul_zero]
    · rw [(he _).2 h1, zero_mul]

end Abstract

section Local

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem val_unif {w : Pl E} {ϖ : (w.adicCompletion E)ˣ} (hϖ : ordL (ϖ : w.adicCompletion E) = 1) :
    ValuativeRel.valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) =
      ValuativeRel.uniformizer (w.adicCompletion E) := by
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have e := ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  have h1 : Valued.v (ϖ : w.adicCompletion E) < 1 :=
    GlobalTheory.CompanionTheory.IwahoriContraction.v_lt_one_of_ordL_eq_one w ϖ.ne_zero hϖ
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (ValuativeRel.uniformizer (w.adicCompletion E))
  apply le_antisymm
  · rw [ValuativeRel.le_uniformizer_iff]
    exact e.lt_one_iff_lt_one.2 h1
  · rw [← hy]
    have h2 : Valued.v y < 1 := e.lt_one_iff_lt_one.1 (hy ▸ ValuativeRel.uniformizer_lt_one)
    exact (e _ _).2 (GlobalTheory.CompanionTheory.IwahoriContraction.v_le_of_ordL_eq_one w ϖ.ne_zero hϖ h2)

theorem iw_fact {w : Pl E} {ϖ : (w.adicCompletion E)ˣ} (hϖ : ordL (ϖ : w.adicCompletion E) = 1) {n : ℕ}
    {x x' : Fin n → ℤ} (hx : Antitone x) (hx' : Antitone x') :
    ∀ g ∈ iwGL n w, ∃ a ∈ iwGL n w, ∃ b ∈ iwGL n w, g = a * b ∧
      tdiag ϖ x * a * (tdiag ϖ x)⁻¹ ∈ iwGL n w ∧ (tdiag ϖ x')⁻¹ * b * tdiag ϖ x' ∈ iwGL n w := by
  intro g hg
  have c1 := GlobalTheory.IwahoriTraceProof.dominantContracts (k := w.adicCompletion E) (n := Fin n) ϖ (val_unif hϖ) x hx
  have c2 := GlobalTheory.IwahoriTraceProof.dominantContracts (k := w.adicCompletion E) (n := Fin n) ϖ (val_unif hϖ) x' hx'
  obtain ⟨u, hu, d, hd, c, hc, rfl⟩ := GlobalTheory.IwahoriTraceProof.iwahori_factorisation hg
  have hdI := GlobalTheory.SmGL.diagT_mem_iwahori hd
  have huI := (GlobalTheory.IwahoriTraceProof.mem_unipO_iff hu.1).2 hu
  have hcI := GlobalTheory.SmGL.KOne_le_iwahori _ _ hc.2
  refine ⟨_, mul_mem huI hdI, c, hcI, rfl, ?_, GlobalTheory.SmGL.KOne_le_iwahori _ _ (c2.2 c hc).2⟩
  have hcomm : tdiag ϖ x * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) d * (tdiag ϖ x)⁻¹ =
      GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) d := by
    unfold tdiag
    rw [← map_mul, mul_comm, map_mul]
    group
  have h1 := c1.1 u hu
  have h1I := (GlobalTheory.IwahoriTraceProof.mem_unipO_iff h1.1).2 h1
  have e : tdiag ϖ x * (u * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) d) * (tdiag ϖ x)⁻¹ =
      (tdiag ϖ x * u * (tdiag ϖ x)⁻¹) *
        (tdiag ϖ x * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) d * (tdiag ϖ x)⁻¹) := by group
  rw [e, hcomm]
  exact mul_mem h1I hdI

theorem v_zpow_le_one {w : Pl E} {ϖ : (w.adicCompletion E)ˣ} (hϖ : ordL (ϖ : w.adicCompletion E) = 1) {k : ℤ}
    (hk : 0 ≤ k) : Valued.v ((ϖ ^ k : (w.adicCompletion E)ˣ) : w.adicCompletion E) ≤ 1 := by
  have h1 : Valued.v (ϖ : w.adicCompletion E) < 1 :=
    GlobalTheory.CompanionTheory.IwahoriContraction.v_lt_one_of_ordL_eq_one w ϖ.ne_zero hϖ
  have h0 : 0 < Valued.v (ϖ : w.adicCompletion E) :=
    zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ϖ.ne_zero)
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀]
  exact zpow_le_one₀ h0 h1.le hk

theorem int_entries {w : Pl E} {ϖ : (w.adicCompletion E)ˣ} (hϖ : ordL (ϖ : w.adicCompletion E) = 1) {n : ℕ}
    {x x' : Fin n → ℤ} (hx : Antitone x) (hx' : Antitone x') {g : GLw n w}
    (h1 : ∀ i j, Valued.v (g.val i j) ≤ 1)
    (h2 : ∀ i j, Valued.v (((tdiag ϖ (x + x'))⁻¹ * g * tdiag ϖ (x + x')).val i j) ≤ 1) (i j : Fin n) :
    Valued.v (((tdiag ϖ x)⁻¹ * g * tdiag ϖ x).val i j) ≤ 1 := by
  rw [conj_entry]
  rcases le_total i j with h | h
  · have a1 := hx' h
    have e : ((ϖ ^ (x j - x i) : (w.adicCompletion E)ˣ) : w.adicCompletion E) * g.val i j =
        ((ϖ ^ (x' i - x' j) : (w.adicCompletion E)ˣ) : w.adicCompletion E) *
          (((tdiag ϖ (x + x'))⁻¹ * g * tdiag ϖ (x + x')).val i j) := by
      rw [conj_entry, ← mul_assoc, ← Units.val_mul, ← _root_.zpow_add]
      congr 3
      simp only [Pi.add_apply]
      ring
    rw [e, map_mul]
    exact mul_le_one' (v_zpow_le_one hϖ (by omega)) (h2 i j)
  · have a1 := hx h
    rw [map_mul]
    exact mul_le_one' (v_zpow_le_one hϖ (by omega)) (h1 i j)

theorem iw_chain {w : Pl E} {ϖ : (w.adicCompletion E)ˣ} (hϖ : ordL (ϖ : w.adicCompletion E) = 1) {n : ℕ}
    {x x' : Fin n → ℤ} (hx : Antitone x) (hx' : Antitone x') :
    ∀ g ∈ iwGL n w, (tdiag ϖ x * tdiag ϖ x')⁻¹ * g * (tdiag ϖ x * tdiag ϖ x') ∈ iwGL n w →
      (tdiag ϖ x)⁻¹ * g * tdiag ϖ x ∈ iwGL n w := by
  intro g hg hg'
  rw [← tdiag_add] at hg'
  obtain ⟨h1, h2, h3⟩ := (GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n g).1.1 hg
  obtain ⟨p1, p2, -⟩ := (GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n _).1.1 hg'
  have e : ∀ t : GLw n w, (t⁻¹ * g * t)⁻¹ = t⁻¹ * g⁻¹ * t := fun t => by group
  refine (GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n _).1.2
    ⟨int_entries hϖ hx hx' h1 p1, ?_, fun i j hij => ?_⟩
  · rw [e]
    exact int_entries hϖ hx hx' h2 (by rw [← e]; exact p2)
  · rw [conj_entry, map_mul]
    have a1 := hx hij.le
    exact (mul_le_of_le_one_left' (v_zpow_le_one hϖ (by omega))).trans_lt (h3 i j hij)

theorem dcos_mem (n : ℕ) (w : Pl E) (t y : GLw n w) :
    (y ∈ dc (iwGL n w) t → dcos n w t y = 1) ∧ (y ∉ dc (iwGL n w) t → dcos n w t y = 0) :=
  ⟨fun h => if_pos h, fun h => if_neg h⟩

theorem isHk_dcos (n : ℕ) (w : Pl E) (t : GLw n w) : IsHk (iwGL n w) (dcos n w t) := by
  refine ⟨GlobalTheory.SmGL.IwahoriOnto.isOpen_iwahori (w.adicCompletion E) (Fin n),
    GlobalTheory.SmGL.IwahoriOnto.isCompact_iwahori (w.adicCompletion E) (Fin n),
    HasCompactSupport.of_support_subset_isCompact (GlobalTheory.CompanionTheory.IwFacts.isCompact_support_dcos w n t) fun g hg => hg,
    fun k₁ h₁ k₂ h₂ g => ?_⟩
  by_cases h : g ∈ dc (iwGL n w) t
  · have h' : k₁ * g * k₂ ∈ dc (iwGL n w) t := by
      obtain ⟨x, hx, z, hz, rfl⟩ := h
      exact ⟨k₁ * x, mul_mem h₁ hx, z * k₂, mul_mem hz h₂, by group⟩
    rw [(dcos_mem n w t _).1 h, (dcos_mem n w t _).1 h']
  · have h' : k₁ * g * k₂ ∉ dc (iwGL n w) t := by
      rintro ⟨x, hx, z, hz, e⟩
      refine h ⟨k₁⁻¹ * x, mul_mem (inv_mem h₁) hx, z * k₂⁻¹, mul_mem hz (inv_mem h₂), ?_⟩
      have : g = k₁⁻¹ * (k₁ * g * k₂) * k₂⁻¹ := by group
      rw [this, e]; group
    rw [(dcos_mem n w t _).2 h, (dcos_mem n w t _).2 h']

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (a : ℕ) (ϖ : (w.adicCompletion E)ˣ), ordL (ϖ : w.adicCompletion E) = 1 → ∀ (x x' : Fin a → ℤ), Antitone x → Antitone x' → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GLw a w) V) (v : V), (∀ k ∈ iwGL a w, π k v = v) → ∑ᶠ q : GLw a w ⧸ iwGL a w, dcos a w (tdiag ϖ (x + x')) q.out • π q.out v = ∑ᶠ q : GLw a w ⧸ iwGL a w, dcos a w (tdiag ϖ x) q.out • π q.out (∑ᶠ q' : GLw a w ⧸ iwGL a w, dcos a w (tdiag ϖ x') q'.out • π q'.out v) := by
  intro E _ _ _ w a ϖ hϖ x x' hx hx' V _ _ π v hv
  obtain ⟨-, -, h⟩ := GlobalTheory.CompanionTheory.HeckeAlg.hk_alg (w.adicCompletion E) (Fin a) (iwGL a w) (dcos a w (tdiag ϖ x))
    (dcos a w (tdiag ϖ x')) (isHk_dcos a w _) (isHk_dcos a w _)
  obtain ⟨-, hm, -⟩ := h V π v (by
    show ∀ k : iwGL a w, π (k : GLw a w) v = (((1 : iwGL a w →* ℂˣ) k : ℂˣ) : ℂ) • v
    intro k
    simpa using hv k k.2)
  have hc : hconv (iwGL a w) (dcos a w (tdiag ϖ x)) (dcos a w (tdiag ϖ x')) = dcos a w (tdiag ϖ (x + x')) := by
    funext g
    rw [tdiag_add]
    exact conv_dc (iw_fact hϖ hx hx') (iw_chain hϖ hx hx') (dcos_mem a w _) (dcos_mem a w _) (dcos_mem a w _) g
  rw [hc] at hm
  exact hm

end Local

end GlobalTheory.CompanionTheory.IwHeckeMul
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriHeckeSumAdditiveStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwahori_hecke_sum_additive : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (a : ℕ) (ϖ : (w.adicCompletion E)ˣ), ordL (ϖ : w.adicCompletion E) = 1 → ∀ (x x' : Fin a → ℤ), Antitone x → Antitone x' → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GLw a w) V) (v : V), (∀ k ∈ iwGL a w, π k v = v) → ∑ᶠ q : GLw a w ⧸ iwGL a w, dcos a w (tdiag ϖ (x + x')) q.out • π q.out v = ∑ᶠ q : GLw a w ⧸ iwGL a w, dcos a w (tdiag ϖ x) q.out • π q.out (∑ᶠ q' : GLw a w ⧸ iwGL a w, dcos a w (tdiag ϖ x') q'.out • π q'.out v) := by
  first | exact @GlobalTheory.CompanionTheory.IwHeckeMul.main | exact GlobalTheory.CompanionTheory.IwHeckeMul.main | (intros; apply GlobalTheory.CompanionTheory.IwHeckeMul.main <;> assumption)
end
end
