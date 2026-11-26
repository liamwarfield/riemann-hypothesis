module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsLocEqOfIsLocComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateFreeOfCard
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralNormalizedIntegralMatricesTwoSidedMu
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiDiagonalEpsilonGramMulVec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilQDivisorAvoidsPointCartierIffNotMemSupp
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilQDivisorAvoidsPointCartierIffNotMemSupp
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

namespace GlobalTheory.PairStep

open CategoryTheory AlgebraicGeometry TopologicalSpace in
set_option autoImplicit false in
private lemma exists_coheight_one_generalization_not_unitAt {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] {z : X} {f : X.functionField} (hf : f ≠ 0)
    (hreg : _root_.GlobalTheory.Cartier.RegAt z f) (hnu : ¬ _root_.GlobalTheory.Cartier.UnitAt z f) :
    ∃ w : X, w ⤳ z ∧ Order.coheight w = 1 ∧ ¬ _root_.GlobalTheory.Cartier.UnitAt w f := by
  obtain ⟨U, hzU, a, rfl⟩ := hreg.exists_fnOf
  obtain ⟨V, hV, hzV, hVU⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hzU
  have hV' : IsAffineOpen V := hV
  have hgV : genericPoint X ∈ V :=
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr ⟨z, trivial, hzV⟩
  rw [← _root_.GlobalTheory.Cartier.fnOf_resG hVU hgV a] at hf hnu ⊢
  generalize _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG X hVU a = b at hf hnu ⊢
  haveI : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  haveI : Nonempty V := ⟨⟨z, hzV⟩⟩
  have hmem : ∀ q : PrimeSpectrum Γ(X, V), hV'.fromSpec q ∈ V := fun q => by
    have : hV'.fromSpec q ∈ Set.range hV'.fromSpec := Set.mem_range_self q
    rwa [hV'.range_fromSpec] at this
  have key : ∀ q : PrimeSpectrum Γ(X, V),
      _root_.GlobalTheory.Cartier.UnitAt (hV'.fromSpec q) (_root_.GlobalTheory.Cartier.fnOf V hgV b) ↔
        b ∉ q.asIdeal := by
    intro q
    rw [_root_.GlobalTheory.Cartier.unitAt_fnOf_iff (hmem q) hgV b]
    have : hV'.fromSpec q ∈ X.basicOpen b ↔ q ∈ PrimeSpectrum.basicOpen b := by
      rw [← hV'.fromSpec_preimage_basicOpen]; rfl
    rw [this, PrimeSpectrum.mem_basicOpen]
  set p := hV'.primeIdealOf ⟨z, hzV⟩
  have hpz : hV'.fromSpec p = z := hV'.fromSpec_primeIdealOf ⟨z, hzV⟩
  have hbp : b ∈ p.asIdeal := by
    by_contra h
    exact hnu (hpz ▸ (key p).mpr h)
  obtain ⟨P, hPmin, hPp⟩ := Ideal.exists_minimalPrimes_le
    ((Ideal.span_singleton_le_iff_mem _).mpr hbp)
  haveI hPprime : P.IsPrime := hPmin.1.1
  set q : PrimeSpectrum Γ(X, V) := ⟨P, hPprime⟩
  have hbP : b ∈ P := (Ideal.span_singleton_le_iff_mem _).mp hPmin.1.2
  refine ⟨hV'.fromSpec q, ?_, ?_, fun h => (key q).mp h hbP⟩
  · rw [← hpz]
    exact ((PrimeSpectrum.le_iff_specializes q p).mp hPp).map hV'.fromSpec.continuous
  · letI := X.presheaf.algebra_section_stalk ⟨hV'.fromSpec q, hmem q⟩
    haveI hloc := hV'.isLocalization_stalk' q (hmem q)
    have hdim : ringKrullDim (X.presheaf.stalk (hV'.fromSpec q)) = (P.height : WithBot ℕ∞) :=
      @IsLocalization.AtPrime.ringKrullDim_eq_height _ _ q.asIdeal q.2 _ _ _ hloc
    rw [ringKrullDim_stalk_eq_coheight] at hdim
    haveI : (Ideal.span {b}).IsPrincipal := ⟨⟨b, rfl⟩⟩
    have hle : P.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hPmin
    have hne : P.height ≠ 0 := by
      rw [Ne, Ideal.height_eq_zero_iff]
      intro hmin
      have hbot : P ≤ ⊥ := hmin.2 ⟨Ideal.isPrime_bot, bot_le⟩ bot_le
      have hb0 : b = 0 := (Submodule.eq_bot_iff _).mp (le_bot_iff.mp hbot) b hbP
      exact hf (by rw [hb0, map_zero])
    have h1 : P.height = 1 := le_antisymm hle (ENat.one_le_iff_ne_zero.mpr hne)
    rw [h1] at hdim
    exact_mod_cast hdim


open CategoryTheory AlgebraicGeometry TopologicalSpace in
set_option autoImplicit false in
theorem _root_.GlobalTheory.PairStep.off_qWeil_iff_notMem_supp : ∀ (X : Scheme.{0}) [IsIntegral X]
    [IsLocallyNoetherian X] (D₀ : _root_.GlobalTheory.Cartier.CartierDiv X) (m : ℕ) (z : X),
    D₀.Eff → 0 < m →
      (_root_.GlobalTheory.PairStep.Off (_root_.GlobalTheory.Discrepancy.qWeil D₀ m) z ↔
        z ∉ D₀.supp) := by
  intro X _ _ D m z hD hm
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  obtain ⟨g, hg⟩ := D.exists_isEqn z
  obtain ⟨U, hzU, hU⟩ := hg.exists_nhds
  have hgen : ∀ w : X, w ⤳ z → D.IsEqn w g := fun w hwz =>
    hU w (hwz.mem_open U.isOpen hzU)
  unfold _root_.GlobalTheory.PairStep.Off _root_.GlobalTheory.Discrepancy.qWeil
  simp only [div_eq_zero_iff, hm', or_false, Int.cast_eq_zero]
  rw [hg.mem_supp_iff, not_not]
  constructor
  · intro h
    by_contra hnu
    have hreg := (_root_.GlobalTheory.Cartier.CartierDiv.eff_iff.mp hD) z g hg
    obtain ⟨w, hwz, hw1, hwnu⟩ := exists_coheight_one_generalization_not_unitAt (Units.ne_zero g) hreg hnu
    have hmult := h w hwz
    rw [(hgen w hwz).mult_eq] at hmult
    obtain ⟨a, ha⟩ := _root_.GlobalTheory.Discrepancy.regAt_of_specializes hwz hreg
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact Units.ne_zero g (by rw [← ha, map_zero])
    rw [← ha, _root_.GlobalTheory.Cartier.ord_algebraMap hw1 ha0] at hmult
    have hdim : ringKrullDim (X.presheaf.stalk w) = 1 := by
      rw [ringKrullDim_stalk_eq_coheight, hw1]; rfl
    haveI : Ring.KrullDimLE 1 (X.presheaf.stalk w) := by
      rw [Ring.krullDimLE_iff, hdim]
      exact_mod_cast le_rfl
    have hfin := isFiniteLength_quotient_span_singleton (X.presheaf.stalk w)
      (mem_nonZeroDivisors_of_ne_zero ha0)
    have htop := Module.length_ne_top_iff.mpr hfin
    have hzero : Module.length (X.presheaf.stalk w) (X.presheaf.stalk w ⧸ Ideal.span {a}) ≠ 0 := by
      rw [Ne, Module.length_eq_zero_iff, Ideal.Quotient.subsingleton_iff,
        Ideal.span_singleton_eq_top]
      exact fun hunit => hwnu ⟨a, hunit, ha⟩
    have : (Module.length (X.presheaf.stalk w) (X.presheaf.stalk w ⧸ Ideal.span {a})).toNat ≠ 0 := by
      rw [Ne, ENat.toNat_eq_zero]
      tauto
    exact this (by exact_mod_cast hmult)
  · intro hunit w hwz
    rw [(hgen w hwz).mult_eq]
    obtain ⟨V, hzV, hV⟩ := hunit.exists_nhds
    exact (hV w (hwz.mem_open V.isOpen hzV)).ord_eq_zero

end GlobalTheory.PairStep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilQDivisorAvoidsPointCartierIffNotMemSuppStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilQDivisorAvoidsPoint_cartier_iff_notMem_supp : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (D₀ : CartierDiv X) (m : ℕ) (z : X), D₀.Eff → 0 < m → (Off (qWeil D₀ m) z ↔ z ∉ D₀.supp) := by
  first | exact @GlobalTheory.PairStep.off_qWeil_iff_notMem_supp | exact GlobalTheory.PairStep.off_qWeil_iff_notMem_supp | (intros; apply GlobalTheory.PairStep.off_qWeil_iff_notMem_supp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockLevelsTwistedConstantTermSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockLevelsTwistedConstantTermSplitPlace
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
  GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.SplitLevels

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mem_UL_split {n : ℕ} {w : Pl E} (hw : IsSplitAt w) (x : GLw n w) : x ∈ UL n w := by
  rw [UL, if_pos hw]; exact Subgroup.mem_top x

theorem toSub_of_mem {G : Type} [Group G] (H : Subgroup G) (g : G) (hg : g ∈ H) : toSub H g = ⟨g, hg⟩ := by
  simp [toSub, hg]

theorem blk_zero {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w) : blk h w m 0 = dgM h w m := by
  ext1
  rw [CtLevel.blk_val, dgM_val, dgMat, Matrix.mul_zero]

theorem ct_inv_blocks {a b n : ℕ} (h : a + b = n) (w : Pl E) (N : Subgroup (GLw n w)) (F : GLw n w → ℂ)
    (hNn : ∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∀ x ∈ N, k⁻¹ * x * k ∈ N)
    (hF : ∀ y ∈ N, ∀ x, F (y * x) = F x ∧ F (x * y) = F x)
    (k : GLw a w × GLw b w) (hk1 : k.1 ∈ GlobalTheory.LFun.KGL w (n := a)) (hk2 : k.2 ∈ GlobalTheory.LFun.KGL w (n := b)) (hkN : dgM h w k ∈ N)
    (m : GLw a w × GLw b w) : ct h w F (k * m) = ct h w F m ∧ ct h w F (m * k) = ct h w F m := by
  have hab := GlobalTheory.T.absHalf_blockDet_integralGL_invariant E a b w m k hk1 hk2
  constructor
  · unfold ct
    rw [hab.1]
    congr 2
    funext X
    congr 1
    funext κ
    rw [(GlobalTheory.T.blockUpperTimesUnipotent_mul_blockDiagonal E a b n h w m k _).1]
    have e : (κ : GLw n w)⁻¹ * (dgM h w k * blk h w m (Multiplicative.toAdd X)) * κ =
        ((κ : GLw n w)⁻¹ * dgM h w k * κ) * ((κ : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * κ) := by group
    rw [e, (hF _ (hNn _ κ.2 _ hkN) _).1]
  · unfold ct
    have e : (fun X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
        avg fun κ : GlobalTheory.LFun.KGL w (n := n) => F ((κ : GLw n w)⁻¹ * blk h w (m * k) (Multiplicative.toAdd X) * κ)) =
        fun X => avg fun κ : GlobalTheory.LFun.KGL w (n := n) => F ((κ : GLw n w)⁻¹ *
          blk h w m (Multiplicative.toAdd (Multiplicative.ofAdd (k.1.val * Multiplicative.toAdd X * (k.2⁻¹).val))) * κ) := by
      funext X
      congr 1
      funext κ
      rw [(GlobalTheory.T.blockUpperTimesUnipotent_mul_blockDiagonal E a b n h w m k _).2]
      have e : (κ : GLw n w)⁻¹ * (blk h w m (k.1.val * Multiplicative.toAdd X * (k.2⁻¹).val) * dgM h w k) * κ =
          ((κ : GLw n w)⁻¹ * blk h w m (k.1.val * Multiplicative.toAdd X * (k.2⁻¹).val) * κ) *
            ((κ : GLw n w)⁻¹ * dgM h w k * κ) := by group
      rw [e, (hF _ (hNn _ κ.2 _ hkN) _).2]
      rfl
    have hh := GlobalTheory.T.haarIntegralNormalized_integralMatrices_twoSidedMul E a b w (fun Y => avg fun κ : GlobalTheory.LFun.KGL w (n := n) =>
      F ((κ : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd Y) * κ)) k.1 k.2⁻¹ hk1 (inv_mem hk2)
    rw [hab.2, e, hh]

theorem ctMu_inv_blocks {a b n : ℕ} (h : a + b = n) (w : Pl E) (hw : IsSplitAt w) (N : Subgroup (GLw n w))
    (K' : Subgroup (UL n w)) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (f : UL n w → ℂ) (hf : IsHecke K' f)
    (hNK : N ≤ K'.map (UL n w).subtype) (hNn : ∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∀ x ∈ N, k⁻¹ * x * k ∈ N)
    (k : GLw a w × GLw b w) (hk : k ∈ (lev₁ h w N μ).prod (lev₂ h w N μ)) (m : GLw a w × GLw b w) :
    ctMu h w μ f (k * m) = ctMu h w μ f m ∧ ctMu h w μ f (m * k) = ctMu h w μ f m := by
  obtain ⟨⟨⟨hk1, hkN1⟩, hkμ1⟩, ⟨⟨hk2, hkN2⟩, hkμ2⟩⟩ := hk
  have hkN : dgM h w k ∈ N := by
    have e : k = (k.1, 1) * (1, k.2) := by ext <;> simp
    rw [e, map_mul]
    exact N.mul_mem hkN1 hkN2
  have hF : ∀ y ∈ N, ∀ x, (fun y => f (toSub (UL n w) y)) (y * x) = (fun y => f (toSub (UL n w) y)) x ∧
      (fun y => f (toSub (UL n w) y)) (x * y) = (fun y => f (toSub (UL n w) y)) x := by
    intro y hy x
    obtain ⟨y', hy', rfl⟩ := hNK hy
    have e1 : toSub (UL n w) ((UL n w).subtype y' * x) = y' * toSub (UL n w) x := by
      rw [toSub_of_mem _ _ (mem_UL_split hw _), toSub_of_mem _ _ (mem_UL_split hw x)]; rfl
    have e2 : toSub (UL n w) (x * (UL n w).subtype y') = toSub (UL n w) x * y' := by
      rw [toSub_of_mem _ _ (mem_UL_split hw _), toSub_of_mem _ _ (mem_UL_split hw x)]; rfl
    exact ⟨by simp only; rw [e1]; exact (hf.2 y' hy' _).1, by simp only; rw [e2]; exact (hf.2 y' hy' _).2⟩
  have hc := ct_inv_blocks h w N (fun y => f (toSub (UL n w) y)) hNn hF k hk1 hk2 hkN m
  have hμ1 : μ (GeneralLinearGroup.det k.1) = 1 := hkμ1
  have hμ2 : μ (GeneralLinearGroup.det k.2) = 1 := hkμ2
  unfold ctMu
  rw [hc.1, hc.2]
  simp only [Prod.fst_mul, Prod.snd_mul, map_mul, mul_pow, map_pow, hμ1, hμ2, one_pow, mul_one, one_mul]
  constructor <;> trivial

theorem levels_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∀ (n a : ℕ) (ha : a ≤ n) (w : Pl E),
    IsSplitAt w → ∀ (μ : (w.adicCompletion E)ˣ →* ℂˣ), IsOpen {x | μ x = 1} → ∀ K' : Subgroup (UL n w),
    IsLevel (MonoidHom.id _) (KL n w) K' → ∃ (K₁ : Subgroup (GLw a w)) (K₂ : Subgroup (GLw (n - a) w))
      (K'' : Subgroup (GLw n w)), IsLevel (thL a w) (GlobalTheory.LFun.KGL w (n := a)) K₁ ∧
      IsLevel (thL (n - a) w) (GlobalTheory.LFun.KGL w (n := (n - a))) K₂ ∧
      ((K' = KL n w ∧ ∀ u ∈ (GlobalTheory.LFun.KGL w (n := 1)), μ (GeneralLinearGroup.det u) = 1) →
        K₁ = GlobalTheory.LFun.KGL w (n := a) ∧ K₂ = GlobalTheory.LFun.KGL w (n := (n - a))) ∧
      IsOpen (K'' : Set (GLw n w)) ∧ K'' ≤ K'.map (UL n w).subtype ∧
      (K''.subgroupOf (GlobalTheory.LFun.KGL w (n := n))).Normal ∧
      (∀ m₁ ∈ K₁, ∀ m₂ ∈ K₂, blk (Nat.add_sub_cancel' ha) w (m₁, m₂) 0 ∈ K'') ∧
      (∀ m₁ ∈ K₁, ∀ m₂ ∈ K₂, μ (GeneralLinearGroup.det m₁ ^ (n - a) * GeneralLinearGroup.det m₂ ^ a) = 1) ∧
      ∀ f, IsHecke K' f → IsHecke (K₁.prod K₂) (ctMu (Nat.add_sub_cancel' ha) w μ f) := by
  intro E _ _ _ n a ha w hw μ hμ K' hK'
  obtain ⟨N, hNo, hNK, hNn, hNf⟩ := GlobalTheory.T.exists_open_conjStable_subgroup_of_splitLevel E n w K' hw hK'
  have hlev := GlobalTheory.T.isLevel_blockLevels_splitPlace E a (n - a) n (Nat.add_sub_cancel' ha) w N μ hw hNo hμ
  refine ⟨lev₁ (Nat.add_sub_cancel' ha) w N μ, lev₂ (Nat.add_sub_cancel' ha) w N μ, N, hlev.1, hlev.2, ?_, hNo, hNK,
    ?_, ?_, ?_, fun f hf => ⟨GlobalTheory.T.hasCompactSupport_twistedConstantTermSplitPlace E a (n - a) n _ w μ f hw hf.1, fun k hk m =>
      ctMu_inv_blocks _ w hw N K' μ f hf hNK hNn k hk m⟩⟩
  · rintro ⟨hK'e, hμ1⟩
    rw [hNf hK'e]
    exact GlobalTheory.T.blockLevels_eq_integralGL_of_unramified E a (n - a) n _ w μ hμ1
  · refine ⟨fun x hx k => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have := hNn _ (inv_mem k.2) _ hx
    simpa [mul_assoc] using this
  · intro m₁ hm₁ m₂ hm₂
    rw [blk_zero]
    have e : ((m₁, m₂) : GLw a w × GLw (n - a) w) = (m₁, 1) * (1, m₂) := by ext <;> simp
    rw [e, map_mul]
    exact N.mul_mem hm₁.1.2 hm₂.1.2
  · intro m₁ hm₁ m₂ hm₂
    have h1 : μ (GeneralLinearGroup.det m₁) = 1 := hm₁.2
    have h2 : μ (GeneralLinearGroup.det m₂) = 1 := hm₂.2
    rw [map_mul, map_pow, map_pow, h1, h2, one_pow, one_pow, mul_one]

end GlobalTheory.BCT.SplitLevels
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockLevelsTwistedConstantTermSplitPlaceStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_block_levels_twistedConstantTerm_split_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∀ (n a : ℕ) (ha : a ≤ n) (w : Pl E), IsSplitAt w → ∀ (μ : (w.adicCompletion E)ˣ →* ℂˣ), IsOpen {x | μ x = 1} → ∀ K' : Subgroup (UL n w), IsLevel (MonoidHom.id _) (KL n w) K' → ∃ (K₁ : Subgroup (GLw a w)) (K₂ : Subgroup (GLw (n - a) w)) (K'' : Subgroup (GLw n w)), IsLevel (thL a w) (GlobalTheory.LFun.KGL w (n := a)) K₁ ∧ IsLevel (thL (n - a) w) (GlobalTheory.LFun.KGL w (n := (n - a))) K₂ ∧ ((K' = KL n w ∧ ∀ u ∈ (GlobalTheory.LFun.KGL w (n := 1)), μ (GeneralLinearGroup.det u) = 1) → K₁ = GlobalTheory.LFun.KGL w (n := a) ∧ K₂ = GlobalTheory.LFun.KGL w (n := (n - a))) ∧ IsOpen (K'' : Set (GLw n w)) ∧ K'' ≤ K'.map (UL n w).subtype ∧ (K''.subgroupOf (GlobalTheory.LFun.KGL w (n := n))).Normal ∧ (∀ m₁ ∈ K₁, ∀ m₂ ∈ K₂, blk (Nat.add_sub_cancel' ha) w (m₁, m₂) 0 ∈ K'') ∧ (∀ m₁ ∈ K₁, ∀ m₂ ∈ K₂, μ (GeneralLinearGroup.det m₁ ^ (n - a) * GeneralLinearGroup.det m₂ ^ a) = 1) ∧ ∀ f, IsHecke K' f → IsHecke (K₁.prod K₂) (ctMu (Nat.add_sub_cancel' ha) w μ f) := by
  first | exact @GlobalTheory.BCT.SplitLevels.levels_split | exact GlobalTheory.BCT.SplitLevels.levels_split | (intros; apply GlobalTheory.BCT.SplitLevels.levels_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionSubgroupSchemes
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HTTorsRep

theorem absNorm_coprime {K : Type} [Field K] [NumberField K] (p : ℕ) [hp : Fact p.Prime] (𝔟 : Ideal (𝓞 K))
    (h : 𝔟 ⊔ Ideal.span {(p : 𝓞 K)} = ⊤) : (Ideal.absNorm 𝔟).Coprime p := by
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp.out]
  intro hdvd
  have h1 : (1 : 𝓞 K) ∈ 𝔟 ⊔ Ideal.span {(p : 𝓞 K)} := h ▸ Submodule.mem_top
  obtain ⟨β, hβ, z, hz, hβz⟩ := Submodule.mem_sup.1 h1
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  by_cases h0 : 𝔟 = ⊥
  · subst h0
    have hβ0 : β = 0 := (Submodule.mem_bot _).1 hβ
    subst hβ0
    rw [zero_add] at hβz
    have hu : IsUnit (p : 𝓞 K) := ⟨⟨(p : 𝓞 K), y, by rw [mul_comm]; exact hβz, hβz⟩, rfl⟩
    have hu' := hu.map (Algebra.norm ℤ : 𝓞 K →* ℤ)
    rw [show (p : 𝓞 K) = algebraMap ℤ (𝓞 K) (p : ℤ) by simp, Algebra.norm_algebraMap] at hu'
    have hd : Module.finrank ℤ (𝓞 K) ≠ 0 := (Module.finrank_pos).ne'
    rw [isUnit_pow_iff hd, Int.isUnit_iff] at hu'
    rcases hu' with h' | h'
    · exact hp.out.one_lt.ne' (by exact_mod_cast h')
    · have : (0 : ℤ) ≤ p := by positivity
      omega
  · have hne : Ideal.absNorm 𝔟 ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hne hdvd
    have : Finite (𝓞 K ⧸ 𝔟) := Nat.finite_of_card_ne_zero hne
    obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' p hdvd
    have hpx : (p : 𝓞 K ⧸ 𝔟) * x = 0 := by
      rw [← nsmul_eq_mul, ← hx, addOrderOf_nsmul_eq_zero]
    have h1' : (Ideal.Quotient.mk 𝔟 y) * (p : 𝓞 K ⧸ 𝔟) = 1 := by
      have := congrArg (Ideal.Quotient.mk 𝔟) hβz
      rwa [map_add, Ideal.Quotient.eq_zero_iff_mem.2 hβ, zero_add, map_mul, map_natCast, map_one] at this
    have hx0 : x = 0 := by
      rw [← _root_.one_mul x, ← h1', _root_.mul_assoc, hpx, MulZeroClass.mul_zero]
    rw [hx0, addOrderOf_zero] at hx
    exact hp.out.one_lt.ne hx

section Tors

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] (n : ℕ)

theorem mono_of_unit {X : Over S} (e : 𝟙_ (Over S) ⟶ X) : Mono e := ⟨fun g h _ => toUnit_unique g h⟩

theorem ι_mulN : torsion.ι A n ≫ mulN A n = toUnit _ ≫ η[A] := by
  exact (pullback.condition (f := mulN A n) (g := (η : 𝟙_ (Over S) ⟶ A))).trans
    (congrArg (· ≫ η[A]) (toUnit_unique _ _))

def torsEta : 𝟙_ (Over S) ⟶ torsion A n :=
  pullback.lift η[A] (𝟙 _) (by rw [IsMonHom.one_hom, Category.id_comp])

theorem mono_ι : Mono (torsion.ι A n) := by
  have := mono_of_unit η[A]
  exact pullback.fst_of_mono

def torsAct (f : A ⟶ A) [IsMonHom f] (hf : f ≫ mulN A n = mulN A n ≫ f) : torsion A n ⟶ torsion A n :=
  pullback.lift (torsion.ι A n ≫ f) (toUnit _) (by
    rw [Category.assoc, hf, ← Category.assoc, ι_mulN, Category.assoc, IsMonHom.one_hom])

@[simp]
theorem torsAct_ι (f : A ⟶ A) [IsMonHom f] (hf : f ≫ mulN A n = mulN A n ≫ f) :
    torsAct n f hf ≫ torsion.ι A n = torsion.ι A n ≫ f := pullback.lift_fst _ _ _

theorem exists_openClosed {Ix : Type} [DecidableEq Ix] (act : Ix → (A ⟶ A)) [∀ a, IsMonHom (act a)]
    (hc : ∀ a, act a ≫ mulN A n = mulN A n ≫ act a) [Etale (torsion A n).hom] [IsSeparated (torsion A n).hom]
    (t : Finset Ix) :
    ∃ (Z : Over S) (j : Z ⟶ torsion A n), Mono j ∧ IsOpenImmersion j.left ∧ IsClosedImmersion j.left ∧
      ∀ (W : Over S) (y : W ⟶ torsion A n), (∃ z, z ≫ j = y) ↔ ∀ a ∈ t, y ≫ torsion.ι A n ≫ act a = 1 := by
  have hEta : torsEta n ≫ torsion.ι A n = η[A] := pullback.lift_fst _ _ _
  have hsec : IsOpenImmersion (torsEta (A := A) n).left ∧ IsClosedImmersion (torsEta (A := A) n).left :=
    GlobalTheory.isOpenImmersion_and_isClosedImmersion_of_section_of_etale (torsion A n).hom _ (Over.w (torsEta n))
  have := hsec.1; have := hsec.2
  have := mono_of_unit (torsEta (A := A) n)
  have := mono_ι (A := A) n
  induction t using Finset.induction_on with
  | empty =>
    exact ⟨_, 𝟙 _, inferInstance, by rw [Over.id_left]; infer_instance, by rw [Over.id_left]; infer_instance, fun W y =>
      ⟨fun _ a ha => absurd ha (Finset.notMem_empty a), fun _ => ⟨y, Category.comp_id y⟩⟩⟩
  | insert a t hat ih =>
    obtain ⟨Z, j, hj, hjo, hjc, hpts⟩ := ih
    let g := j ≫ torsAct n (act a) (hc a)
    have hP := (IsPullback.of_hasPullback g (torsEta n)).map (Over.forget S)
    have ho : IsOpenImmersion (pullback.fst g (torsEta n)).left :=
      MorphismProperty.of_isPullback (P := @IsOpenImmersion) hP.flip hsec.1
    have hcl : IsClosedImmersion (pullback.fst g (torsEta n)).left :=
      MorphismProperty.of_isPullback (P := @IsClosedImmersion) hP.flip hsec.2
    refine ⟨pullback g (torsEta n), pullback.fst g (torsEta n) ≫ j, inferInstance, ?_, ?_, fun W y => ?_⟩
    · rw [Over.comp_left]; infer_instance
    · rw [Over.comp_left]; infer_instance
    constructor
    · rintro ⟨z, rfl⟩ b hb
      rcases Finset.mem_insert.1 hb with rfl | hb
      · have e : j ≫ torsion.ι A n ≫ act b = g ≫ torsion.ι A n := by simp [g]
        simp only [Category.assoc]
        rw [e, ← Category.assoc (pullback.fst g _), pullback.condition]
        simp only [Category.assoc, hEta]
        rw [← Category.assoc, toUnit_unique (z ≫ pullback.snd g (torsEta n)) (toUnit W)]; rfl
      · exact (hpts W _).1 ⟨z ≫ pullback.fst _ _, Category.assoc _ _ _⟩ b hb
    · intro h
      obtain ⟨w, hw⟩ := (hpts W y).2 (fun b hb => h b (Finset.mem_insert_of_mem hb))
      have hwg : w ≫ g = toUnit W ≫ torsEta n := by
        rw [← cancel_mono (torsion.ι A n)]
        simp only [g, Category.assoc, torsAct_ι, hEta]
        rw [← Category.assoc w j, hw, h a (Finset.mem_insert_self a t)]; rfl
      exact ⟨pullback.lift w (toUnit W) hwg, by rw [← Category.assoc, pullback.lift_fst, hw]⟩

end Tors


open GlobalTheory.IwLevel in
theorem exists_finiteEtale_killedBy : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : GlobalTheory.UPel.HT.Obj b N s) (𝔟 : Ideal (𝓞 D.F)), 𝔟 ⊔ Ideal.span {(p : 𝓞 D.F)} = ⊤ → ∃ (K : Over S) (i : K ⟶ o.A), Mono i ∧ IsFinite K.hom ∧ Etale K.hom ∧ ∀ (T : Over S) (x : T ⟶ o.A), GlobalTheory.IwLevel.InSub i x ↔ GlobalTheory.IwLevel.KilledBy (GlobalTheory.IwLevel.htAct o) (𝔟.map (algebraMap (𝓞 D.F) D.O)) x := by
  intro p _ D R _ b N S s o 𝔟 h𝔟
  classical
  set n := Ideal.absNorm 𝔟 with hn_def
  have hcop := absNorm_coprime p 𝔟 h𝔟
  have hnR : IsUnit ((n : ℕ) : R) := b.unit n hcop
  have hnS : IsUnit ((n : ℕ) : Γ(S, ⊤)) := by
    have := hnR.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ s.appTop).hom
    simpa using this
  haveI := o.ab
  obtain ⟨-, hTf, hTe⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion o.A hnS
  have hactN : ∀ k : ℕ, o.act.act (k : D.O) = mulN o.A k := by
    intro k
    induction k with
    | zero =>
      have h := o.act.add 0 0
      rw [add_zero] at h
      rw [Nat.cast_zero]
      exact left_eq_mul.1 h
    | succ k ih => rw [Nat.cast_succ, o.act.add, ih, o.act.one]; rfl
  have hc : ∀ a : D.O, o.act.act a ≫ mulN o.A n = mulN o.A n ≫ o.act.act a := by
    intro a
    rw [← hactN, ← o.act.mul, ← o.act.mul, Nat.cast_comm]
  haveI : ∀ a, IsMonHom (o.act.act a) := o.act.hom
  haveI : IsSeparated (torsion o.A n).hom := inferInstance
  have : Module.Finite ℤ D.O := D.finO
  have : IsNoetherian D.O D.O := isNoetherian_of_tower ℤ inferInstance
  obtain ⟨t, ht⟩ := IsNoetherian.noetherian (𝔟.map (algebraMap (𝓞 D.F) D.O))
  obtain ⟨Z, j, hj, hjo, hjc, hpts⟩ := exists_openClosed n o.act.act hc t
  have := mono_ι (A := o.A) n
  refine ⟨Z, j ≫ torsion.ι o.A n, inferInstance, ?_, ?_, fun T x => ?_⟩
  · rw [← Over.w j]; infer_instance
  · rw [← Over.w j]; infer_instance
  rw [← ht]
  refine Iff.trans ?_ (killedBy_span (htAct o) (t : Set D.O) x).symm
  simp only [htAct_act]
  constructor
  · rintro ⟨z, rfl⟩ a ha
    simpa only [Category.assoc] using (hpts T (z ≫ j)).1 ⟨z, rfl⟩ a ha
  · intro hx
    have hn𝔟 : ((n : ℕ) : 𝓞 D.F) ∈ 𝔟 := Ideal.absNorm_mem 𝔟
    have hnO : ((n : ℕ) : D.O) ∈ Submodule.span D.O (t : Set D.O) := by
      rw [ht]; simpa using Ideal.mem_map_of_mem (algebraMap (𝓞 D.F) D.O) hn𝔟
    have hxn : x ≫ mulN o.A n = toUnit T ≫ η[o.A] := by
      rw [← hactN]
      have := (killedBy_span (htAct o) (t : Set D.O) x).2 (by simpa only [htAct_act] using hx) _ hnO
      exact this
    let y : T ⟶ torsion o.A n := pullback.lift x (toUnit T) hxn
    have hy : y ≫ torsion.ι o.A n = x := pullback.lift_fst _ _ _
    obtain ⟨z, hz⟩ := (hpts T y).2 (fun a ha => by rw [← Category.assoc, hy]; exact hx a ha)
    exact ⟨z, by rw [← Category.assoc, hz, hy]⟩

end GlobalTheory.HTTorsRep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVeryAmpleBySectionsOfInvertibleLinearChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVeryAmpleBySectionsOfInvertibleLinearChange
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LinChange

open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi (LB)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp PSpace resG)
open GlobalTheory.QCoh.Qcqs (baseRingHom baseRingHom_res baseRingHom_top)

variable {R : Type} [CommRing R] {X : Scheme.{0}} {H : LB X} {n : ℕ}

def lin (f : X ⟶ Sp R) (a : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (s : Fin (n + 1) → H.Sec) :
    Fin (n + 1) → H.Sec :=
  fun i => ∑ j, GlobalTheory.AbLaw.cst f ⊤ (a i j) • s j

theorem cst_eq (f : X ⟶ Sp R) (W : X.Opens) (r : R) :
    GlobalTheory.AbLaw.cst f W r = (baseRingHom f W).hom r := by
  rw [← baseRingHom_res f (le_top : W ≤ ⊤), baseRingHom_top]
  rfl

theorem resG_cst (f : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U) (r : R) :
    resG X h (GlobalTheory.AbLaw.cst f U r) = GlobalTheory.AbLaw.cst f V r :=
  GlobalTheory.AbLaw.rs_cst f h r

theorem sum_f {m : ℕ} (s : Fin m → H.Sec) (k : H.ι) : (∑ j, s j).f k = ∑ j, (s j).f k :=
  map_sum ({ toFun := fun s : H.Sec => s.f k, map_zero' := rfl, map_add' := fun _ _ => rfl } :
    H.Sec →+ Γ(X, H.U k)) s Finset.univ

theorem lin_f (f : X ⟶ Sp R) (a : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (s : Fin (n + 1) → H.Sec)
    (i : Fin (n + 1)) (k : H.ι) :
    (lin f a s i).f k = ∑ j, GlobalTheory.AbLaw.cst f (H.U k) (a i j) * (s j).f k := by
  rw [lin, sum_f]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [GlobalTheory.LB.smul_f, resG_cst]

theorem lin_lin (f : X ⟶ Sp R) (a b : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (s : Fin (n + 1) → H.Sec) :
    lin f b (lin f a s) = lin f (b * a) s := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [lin, Finset.smul_sum, smul_smul, ← map_mul, Matrix.mul_apply, map_sum, Finset.sum_smul]
  exact Finset.sum_comm

theorem lin_one (f : X ⟶ Sp R) (s : Fin (n + 1) → H.Sec) : lin f 1 s = s := by
  funext i
  simp [lin, Matrix.one_apply, apply_ite]

end GlobalTheory.LinChange

namespace GlobalTheory.LinChange
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi (LB)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp PSpace resG)
open GlobalTheory.QCoh.Qcqs (baseRingHom baseRingHom_res baseRingHom_top)
open GlobalTheory.ProjSpace (toProj toProj_str toProj_preimage_chart O1 coord coord_f chart pullRatio secRatio_on
  pullRatio_toProj_on iSup_nonzeroLocus_coord toProj_coord)

variable {R : Type} [CommRing R] {X : Scheme.{0}} {H : LB X} {n : ℕ}

theorem iSup_nonzeroLocus_lin (f : X ⟶ Sp R) {s : Fin (n + 1) → H.Sec} (hs : ⨆ i, nonzeroLocus (s i) = ⊤)
    {a : Matrix (Fin (n + 1)) (Fin (n + 1)) R} (ha : IsUnit a.det) :
    ⨆ i, nonzeroLocus (lin f a s i) = ⊤ := by
  have hb : lin f a⁻¹ (lin f a s) = s := by rw [lin_lin, Matrix.nonsing_inv_mul a ha, lin_one]
  refine top_unique fun y _ => ?_
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hs.ge (Set.mem_univ y))
  obtain ⟨k, hk⟩ := GlobalTheory.exists_chart_of_mem_nonzeroLocus hi
  by_contra hne
  have hnu : ∀ j, ¬ IsUnit (X.presheaf.germ (H.U k) y hk ((lin f a s j).f k)) := fun j hu =>
    hne (Opens.mem_iSup.2 ⟨j, (GlobalTheory.mem_nonzeroLocus_iff_basicOpen _ hk).2 ((X.mem_basicOpen _ y hk).2 hu)⟩)
  have hu := (X.mem_basicOpen _ y hk).1 ((GlobalTheory.mem_nonzeroLocus_iff_basicOpen _ hk).1 hi)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hb, lin_f, map_sum] at hu
  refine (IsLocalRing.mem_maximalIdeal _).1 (Ideal.sum_mem _ fun j _ => ?_) hu
  rw [map_mul]
  exact Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hnu j))

theorem appLE_cst {Y : Scheme.{0}} (p : Y ⟶ Sp R) (g : X ⟶ Y) {U : Y.Opens} {W : X.Opens} (h : W ≤ g ⁻¹ᵁ U) (r : R) :
    (g.appLE U W h).hom (GlobalTheory.AbLaw.cst p U r) = GlobalTheory.AbLaw.cst (g ≫ p) W r := by
  rw [cst_eq, cst_eq, ← GlobalTheory.ProjSpace.baseRingHom_appLE p g U W h]
  rfl

theorem toProj_lin (f : X ⟶ Sp R) {s : Fin (n + 1) → H.Sec} (hs : ⨆ i, nonzeroLocus (s i) = ⊤)
    (a : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (ht : ⨆ i, nonzeroLocus (lin f a s i) = ⊤)
    (hc : ⨆ i, nonzeroLocus (lin (PSpace.str R n) a (coord R n) i) = ⊤) :
    toProj f (lin f a s) ht =
      toProj f s hs ≫ toProj (PSpace.str R n) (lin (PSpace.str R n) a (coord R n)) hc := by
  have e := GlobalTheory.ProjSpace.toProj_eq_comp_of_locally (f := PSpace.str R n) hc (toProj f s hs)
    (t := lin f a s) ht ?_
  · rwa [toProj_str] at e
  intro z
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hs.ge (Set.mem_univ z))
  obtain ⟨l, hl⟩ := GlobalTheory.exists_chart_of_mem_nonzeroLocus hi
  have hW : nonzeroLocus (s i) ⊓ H.U l ≤ toProj f s hs ⁻¹ᵁ chart R n i :=
    inf_le_left.trans (toProj_preimage_chart f s hs i).ge
  refine ⟨nonzeroLocus (s i) ⊓ H.U l, ⟨hi, hl⟩, i, hW, l, inf_le_right, resG X inf_le_right ((s i).f l),
    fun j => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [lin_f, lin_f (H := O1 R n) (PSpace.str R n) a (coord R n) j i, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, map_mul, resG_cst, coord_f]
  erw [appLE_cst (PSpace.str R n) (toProj f s hs) hW (a j m)]
  rw [toProj_str]
  change _ = _ * (_ * pullRatio (toProj f s hs) _ i hW m)
  generalize (GlobalTheory.AbLaw.cst f (nonzeroLocus (s i) ⊓ H.U l)) (a j m) = c
  rw [pullRatio_toProj_on, secRatio_on (s i) (s m) l inf_le_left inf_le_right]
  ring

end GlobalTheory.LinChange

namespace GlobalTheory.LinChange
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi (LB)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp PSpace resG)
open GlobalTheory.ProjSpace (toProj coord iSup_nonzeroLocus_coord toProj_coord)

variable {R : Type} [CommRing R] {X : Scheme.{0}} {H : LB X} {n : ℕ}

theorem toProj_congr (f : X ⟶ Sp R) {s t : Fin (n + 1) → H.Sec} (h : s = t) (hs : ⨆ i, nonzeroLocus (s i) = ⊤)
    (ht : ⨆ i, nonzeroLocus (t i) = ⊤) : toProj f s hs = toProj f t ht := by
  subst h
  rfl

def linAut (a : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (ha : IsUnit a.det) : PSpace R n ⟶ PSpace R n :=
  toProj (PSpace.str R n) (lin (PSpace.str R n) a (coord R n))
    (iSup_nonzeroLocus_lin _ (iSup_nonzeroLocus_coord R n) ha)

theorem linAut_comp (a b : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (ha : IsUnit a.det) (hb : IsUnit b.det)
    (hba : IsUnit (b * a).det) : linAut a ha ≫ linAut b hb = linAut (b * a) hba :=
  (toProj_lin (PSpace.str R n) _ b
    (iSup_nonzeroLocus_lin _ (iSup_nonzeroLocus_lin _ (iSup_nonzeroLocus_coord R n) ha) hb) _).symm.trans (toProj_congr _ (lin_lin _ a b _) _ _)

theorem linAut_one (h : IsUnit (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R).det) : linAut 1 h = 𝟙 (PSpace R n) :=
  (toProj_congr _ (lin_one _ _) _ _).trans (toProj_coord R n)

instance isIso_linAut (a : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (ha : IsUnit a.det) : IsIso (linAut a ha) := by
  have hb : IsUnit a⁻¹.det := Matrix.isUnit_nonsing_inv_det a ha
  refine ⟨⟨linAut a⁻¹ hb, ?_, ?_⟩⟩
  · rw [linAut_comp a a⁻¹ ha hb (by rw [Matrix.nonsing_inv_mul a ha, Matrix.det_one]; exact isUnit_one)]
    simp only [Matrix.nonsing_inv_mul a ha]
    exact linAut_one _
  · rw [linAut_comp a⁻¹ a hb ha (by rw [Matrix.mul_nonsing_inv a ha, Matrix.det_one]; exact isUnit_one)]
    simp only [Matrix.mul_nonsing_inv a ha]
    exact linAut_one _

end GlobalTheory.LinChange

theorem GlobalTheory.veryAmpleBy_linChange : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (H : LB X) (n : ℕ)
    (s : Fin (n + 1) → H.Sec) (a : Matrix (Fin (n + 1)) (Fin (n + 1)) R), IsUnit a.det → H.IsLB →
    GlobalTheory.AbLaw.VeryAmpleBy f H s → GlobalTheory.AbLaw.VeryAmpleBy f H (fun i => ∑ j, GlobalTheory.AbLaw.cst f ⊤ (a i j) • s j) := by
  intro R _ X f H n s a ha _ hv
  obtain ⟨hs, hci⟩ := (GlobalTheory.ProjSpace.veryAmpleBy_iff f s).1 hv
  refine (GlobalTheory.ProjSpace.veryAmpleBy_iff f (GlobalTheory.LinChange.lin f a s)).2
    ⟨GlobalTheory.LinChange.iSup_nonzeroLocus_lin f hs ha, ?_⟩
  rw [GlobalTheory.LinChange.toProj_lin f hs a _ (GlobalTheory.LinChange.iSup_nonzeroLocus_lin _
    (GlobalTheory.ProjSpace.iSup_nonzeroLocus_coord R n) ha)]
  exact (inferInstance : IsClosedImmersion (GlobalTheory.ProjSpace.toProj f s hs ≫ GlobalTheory.LinChange.linAut a ha))
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVeryAmpleBySectionsOfInvertibleLinearChangeStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isVeryAmpleBySections_of_invertible_linear_change : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (H : LB X) (n : ℕ) (s : Fin (n + 1) → H.Sec) (a : Matrix (Fin (n + 1)) (Fin (n + 1)) R), IsUnit a.det → H.IsLB → GlobalTheory.AbLaw.VeryAmpleBy f H s → GlobalTheory.AbLaw.VeryAmpleBy f H (fun i => ∑ j, GlobalTheory.AbLaw.cst f ⊤ (a i j) • s j) := by
  first | exact @GlobalTheory.veryAmpleBy_linChange | exact GlobalTheory.veryAmpleBy_linChange | (intros; apply GlobalTheory.veryAmpleBy_linChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFiberEqCardSectionsMulLength
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsoSpecHomSpecMapAppTop
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped NumberField
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IwLevel.FiberCard

theorem isoSpec_hom_specMap_appTop' {P : Scheme.{0}} [IsAffine P] {R : CommRingCat.{0}} (s : P ⟶ Spec R) :
    P.isoSpec.hom ≫ Spec.map ((Scheme.ΓSpecIso R).inv ≫ s.appTop) = s := by
  rw [Scheme.isoSpec_hom, Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
    Category.comp_id]

end GlobalTheory.IwLevel.FiberCard
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFiberEqCardSectionsMulLength
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FinSchemeRank

theorem length_self_eq_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Module.length R R = Module.length S S := by
  letI : Algebra R S := e.toRingHom.toAlgebra
  let f : R ≃ₗ[R] S :=
    { e with map_smul' := fun r x => by simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra] }
  rw [f.length_eq]
  exact Module.length_eq_of_surjective (S := R) (R := S) (M := S) e.surjective

theorem finrank_eq_length_of_isLocalRing (k : Type*) [Field k] [IsAlgClosed k] (A : Type*) [CommRing A]
    [IsLocalRing A] [Algebra k A] [Module.Finite k A] :
    (Module.finrank k A : ℕ∞) = Module.length A A := by
  haveI : IsLocalHom (algebraMap k A) :=
    ⟨fun a ha => isUnit_iff_ne_zero.mpr fun h => by simp [h] at ha⟩
  haveI : Module.Finite k (IsLocalRing.ResidueField A) :=
    Module.Finite.of_surjective (IsScalarTower.toAlgHom k A (IsLocalRing.ResidueField A)).toLinearMap
      IsLocalRing.residue_surjective
  have hb : Function.Bijective (algebraMap k (IsLocalRing.ResidueField A)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  have h1 : Module.length k (IsLocalRing.ResidueField A) = 1 := by
    rw [Module.length_eq_finrank,
      ← (AlgEquiv.ofBijective (Algebra.ofId k _) hb).toLinearEquiv.finrank_eq, Module.finrank_self]
    rfl
  rw [← Module.length_eq_finrank, IsLocalRing.length_restrictScalars k A A,
    ← Module.length_eq_of_surjective (S := k) (R := IsLocalRing.ResidueField k)
      (M := IsLocalRing.ResidueField A) IsLocalRing.residue_surjective, h1, _root_.mul_one]

theorem finrank_eq_card_mul (k : Type) [Field k] [IsAlgClosed k] (B : Type) [CommRing B] [Algebra k B]
    [Module.Finite k B] (m : ℕ∞)
    (hm : ∀ p : PrimeSpectrum B,
      Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) = m) :
    (Module.finrank k B : ℕ∞) = Nat.card (PrimeSpectrum B) * m := by
  haveI : IsArtinianRing B := IsArtinianRing.of_finite k B
  letI := Fintype.ofFinite (PrimeSpectrum B)
  have h : ∀ p : PrimeSpectrum B, (Module.finrank k (Localization.AtPrime p.asIdeal) : ℕ∞) = m := by
    intro p
    haveI : Module.Finite k (Localization.AtPrime p.asIdeal) :=
      Module.Finite.of_surjective (Algebra.algHom k B (Localization.AtPrime p.asIdeal)).toLinearMap
        (IsArtinianRing.localization_surjective p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal))
    rw [← hm p, finrank_eq_length_of_isLocalRing k]
  rw [IsArtinianRing.finrank_eq_sum_primeSpectrum B k, Nat.cast_sum]
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]

theorem card_algHom_eq_card_primeSpectrum (k : Type) [Field k] [IsAlgClosed k] (B : Type) [CommRing B]
    [Algebra k B] [Module.Finite k B] :
    Nat.card (B →ₐ[k] k) = Nat.card (PrimeSpectrum B) := by
  haveI : IsArtinianRing B := IsArtinianRing.of_finite k B
  let F : (B →ₐ[k] k) → PrimeSpectrum B := fun φ => ⟨RingHom.ker φ, RingHom.ker_isPrime _⟩
  refine Nat.card_congr (Equiv.ofBijective F ⟨?_, ?_⟩)
  · intro φ ψ h
    have h' : RingHom.ker φ = RingHom.ker ψ := congrArg PrimeSpectrum.asIdeal h
    ext b
    have : b - algebraMap k B (φ b) ∈ RingHom.ker φ := by simp [RingHom.mem_ker]
    rw [h', RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero] at this
    exact this.symm
  · intro p
    haveI : p.asIdeal.IsMaximal := Ideal.isMaximal_of_isPrime p.asIdeal
    letI : Field (B ⧸ p.asIdeal) := Ideal.Quotient.field _
    have hb : Function.Bijective (algebraMap k (B ⧸ p.asIdeal)) :=
      IsAlgClosed.algebraMap_bijective_of_isIntegral
    let e := AlgEquiv.ofBijective (Algebra.ofId k (B ⧸ p.asIdeal)) hb
    refine ⟨(e.symm : (B ⧸ p.asIdeal) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k p.asIdeal), ?_⟩
    ext x
    change x ∈ RingHom.ker _ ↔ x ∈ p.asIdeal
    simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]

theorem finrank_eq_card_sections_mul : ∀ (k : Type) [Field k] [IsAlgClosed k] (P : Scheme.{0}) (q : P ⟶ Sp k),
    IsFinite q → ∀ (m : ℕ∞), (∀ x : P, Module.length (P.presheaf.stalk x) (P.presheaf.stalk x) = m) →
    ∀ z : Sp k, (q.finrank z : ℕ∞) = (Nat.card {s : Sp k ⟶ P // s ≫ q = 𝟙 _} : ℕ∞) * m := by
  intro k _ _ P q hq m hm z
  haveI := hq
  haveI : IsAffine P := isAffine_of_isAffineHom q
  let B : Type := Γ(P, ⊤)
  letI : Algebra k B := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ q.appTop).hom.toAlgebra
  let q' : Spec (CommRingCat.of B) ⟶ Sp k := Spec.map (CommRingCat.ofHom (algebraMap k B))
  have hq1 : P.isoSpec.hom ≫ q' = q := GlobalTheory.IwLevel.FiberCard.isoSpec_hom_specMap_appTop' q
  have hq2 : q' = P.isoSpec.inv ≫ q := by rw [← hq1, Iso.inv_hom_id_assoc]
  haveI : IsFinite q' := by rw [hq2]; infer_instance
  haveI : Module.Finite k B :=
    RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff _).mp (inferInstanceAs (IsFinite q')))
  haveI : Flat q' := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  haveI : Flat q := by rw [← hq1]; infer_instance
  have hrk : q.finrank z = Module.finrank k B := by
    rw [← hq1, Scheme.Hom.finrank_comp_left_of_isIso]
    refine (Scheme.Hom.finrank_SpecMap_algebraMap k B z).trans ?_
    rw [Module.rankAtStalk_eq_finrank_of_free]
    rfl
  have hsec : Nat.card {s : Sp k ⟶ P // s ≫ q = 𝟙 _} = Nat.card (B →ₐ[k] k) := by
    let F : {s : Sp k ⟶ P // s ≫ q = 𝟙 _} → (B →ₐ[k] k) := fun s =>
      { (Spec.preimage (s.1 ≫ P.isoSpec.hom)).hom with
        commutes' := fun c => by
          have h : CommRingCat.ofHom (algebraMap k B) ≫ Spec.preimage (s.1 ≫ P.isoSpec.hom) = 𝟙 _ := by
            apply Spec.map_injective
            rw [Spec.map_comp, Spec.map_preimage, Spec.map_id, Category.assoc]
            exact (congrArg (s.1 ≫ ·) hq1).trans s.2
          exact congrArg (fun u => u.hom c) h }
    refine Nat.card_congr (Equiv.ofBijective F ⟨?_, ?_⟩)
    · intro s₁ s₂ h
      apply Subtype.ext
      have h1 : Spec.preimage (s₁.1 ≫ P.isoSpec.hom) = Spec.preimage (s₂.1 ≫ P.isoSpec.hom) := by
        ext c
        exact congrArg (fun u : B →ₐ[k] k => u c) h
      have h2 := congrArg Spec.map h1
      rw [Spec.map_preimage, Spec.map_preimage] at h2
      simpa using congrArg (· ≫ P.isoSpec.inv) h2
    · intro φ
      let s : Sp k ⟶ P := Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ P.isoSpec.inv
      have hs' : s ≫ P.isoSpec.hom = Spec.map (CommRingCat.ofHom φ.toRingHom) := by simp [s]
      have hs : s ≫ q = 𝟙 _ := by
        rw [← hq1, ← Category.assoc, hs', ← Spec.map_comp, ← Spec.map_id]
        congr 1
        ext c
        exact φ.commutes c
      refine ⟨⟨s, hs⟩, ?_⟩
      ext b
      change (Spec.preimage (s ≫ P.isoSpec.hom)).hom b = φ b
      rw [hs', Spec.preimage_map]
      rfl
  have hstalk : ∀ p : PrimeSpectrum B,
      Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) = m := by
    intro p
    have hU := isAffineOpen_top P
    have hp : hU.fromSpec p ∈ (⊤ : P.Opens) := by simp
    letI : Algebra B (P.presheaf.stalk (hU.fromSpec p)) :=
      TopCat.Presheaf.algebra_section_stalk P.presheaf ⟨hU.fromSpec p, hp⟩
    haveI : IsLocalization p.asIdeal.primeCompl (P.presheaf.stalk (hU.fromSpec p)) :=
      hU.isLocalization_stalk' p hp
    rw [← hm (hU.fromSpec p)]
    exact length_self_eq_of_ringEquiv (IsLocalization.algEquiv p.asIdeal.primeCompl
      (Localization.AtPrime p.asIdeal) (P.presheaf.stalk (hU.fromSpec p))).toRingEquiv
  rw [hrk, hsec, card_algHom_eq_card_primeSpectrum k B]
  exact finrank_eq_card_mul k B m hstalk

end GlobalTheory.FinSchemeRank
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFiberEqCardSectionsMulLengthStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_fiber_eq_card_sections_mul_length : ∀ (k : Type) [Field k] [IsAlgClosed k] (P : Scheme.{0}) (q : P ⟶ Sp k), IsFinite q → ∀ (m : ℕ∞), (∀ x : P, Module.length (P.presheaf.stalk x) (P.presheaf.stalk x) = m) → ∀ z : Sp k, (q.finrank z : ℕ∞) = (Nat.card {s : Sp k ⟶ P // s ≫ q = 𝟙 _} : ℕ∞) * m := by
  first | (exact @GlobalTheory.FinSchemeRank.finrank_eq_card_sections_mul) | (exact GlobalTheory.FinSchemeRank.finrank_eq_card_sections_mul) | (intros; apply GlobalTheory.FinSchemeRank.finrank_eq_card_sections_mul  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEffQDivAddOfIsQCart
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem isEffQDiv_add {X : Scheme.{0}} {Δ D : X → ℚ} (hΔ : IsEffQDiv Δ) (hD : IsEffQDiv D) :
    IsEffQDiv (Δ + D) := by
  refine ⟨(hΔ.finite.union hD.finite).subset (Function.support_add _ _), ?_, ?_⟩
  · intro z hz
    by_cases h : Δ z = 0
    · exact hD.coheight z fun h' => hz (by simp [h, h'])
    · exact hΔ.coheight z h
  · intro z
    exact add_nonneg (hΔ.nonneg z) (hD.nonneg z)

theorem isEffQDiv_add_of_isQCart : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (Δ D : X → ℚ), IsEffQDiv Δ → IsQCart D → IsEffQDiv (Δ + D) := by
  intro X _ _ p hp Δ D hΔ hD
  have : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hp
  obtain ⟨m, D₀, -, hD₀, rfl⟩ := hD
  exact isEffQDiv_add hΔ (isEffQDiv_qWeil hD₀ m)

end GlobalTheory.PairStep
end
