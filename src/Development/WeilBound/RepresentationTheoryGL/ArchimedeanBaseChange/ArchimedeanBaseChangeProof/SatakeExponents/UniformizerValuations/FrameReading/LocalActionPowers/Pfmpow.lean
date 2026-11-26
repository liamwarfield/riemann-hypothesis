module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PFinConv
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.LocalMatchingOfAssemblyHypotheses

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousCj
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open PositivityTheory.Rg.Bc.ArchbcB.B.M4 PositivityTheory.Rg.Bc.ArchbcB.B.M4.Tw
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.IwUFacts

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem continuous_cj (w : Pl E) : Continuous (cj w) := by
  unfold cj
  split_ifs with h
  · exact h.choose_spec.1
  · exact continuous_id

end GlobalTheory.CompanionTheory.IwUFacts
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalOperatorSums.FinsumQuotLe
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.QuotientOutRightInvariant
namespace UpperTheory.Reformulated.B.P6.r20a

theorem finsum_const_eq_card_mul {α : Type} [Finite α] (c : ℂ) : ∑ᶠ _ : α, c = (Nat.card α : ℂ) * c := by
  haveI : Fintype α := Fintype.ofFinite α
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]

theorem quotient_out_right_invariant {H : Type} [Group H] (K : Subgroup H) (u : H → ℂ)
    (hu : ∀ (x k : H), k ∈ K → u (x * k) = u x) (x : H) :
    u (Quotient.out (x : H ⧸ K)) = u x := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K x
  rw [hk]
  exact hu x k k.2

theorem PositivityTheory.Rg.BcN.F2.LocOpPf.finsum_quot_le :
    ∀ {H : Type} [inst : Group H] {S T : Subgroup H}, S ≤ T → ∀ (u : H → ℂ), (∀ (x t : H), t ∈ T → u (x * t) = u x) → S.relIndex T ≠ OfNat.ofNat (nat_lit 0) → (Function.support fun (q : H ⧸ S) ↦ u (Quotient.out q)).Finite → ∑ᶠ (q : H ⧸ S), u (Quotient.out q) = (S.relIndex T).cast * ∑ᶠ (q : H ⧸ T), u (Quotient.out q) := by
  intro H _ S T hST u hu hidx hfin
  have huS : ∀ (x s : H), s ∈ S → u (x * s) = u x := fun x s hs => hu x s (hST hs)
  set e := Subgroup.quotientEquivProdOfLE hST with he
  have hfst : ∀ x : H, (e (x : H ⧸ S)).1 = (x : H ⧸ T) := fun x => rfl
  have key : ∀ q : H ⧸ S, u (Quotient.out q) = u (Quotient.out (e q).1) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [hfst x, quotient_out_right_invariant S u huS x, quotient_out_right_invariant T u hu x]
  have hcard : S.relIndex T = Nat.card (T ⧸ S.subgroupOf T) := rfl
  haveI : Finite (T ⧸ S.subgroupOf T) := Nat.finite_of_card_ne_zero (by rw [← hcard]; exact hidx)
  set F : (H ⧸ T) × (T ⧸ S.subgroupOf T) → ℂ := fun pr => u (Quotient.out pr.1) with hF
  have h1 : ∑ᶠ (q : H ⧸ S), u (Quotient.out q) = ∑ᶠ (q : H ⧸ S), F (e q) :=
    finsum_congr key
  have h2 : ∑ᶠ (q : H ⧸ S), F (e q) = ∑ᶠ pr, F pr := finsum_comp_equiv e
  have hFfin : (Function.support F).Finite := by
    apply (hfin.image e).subset
    intro pr hpr
    refine ⟨e.symm pr, ?_, by simp⟩
    have : u (Quotient.out (e.symm pr)) = F pr := by
      rw [key]; simp [hF]
    simpa [Function.mem_support, this] using hpr
  have h3 : ∑ᶠ pr, F pr = ∑ᶠ (p : H ⧸ T) (r : T ⧸ S.subgroupOf T), F (p, r) := finsum_curry F hFfin
  have h4 : ∀ p : H ⧸ T, ∑ᶠ (r : T ⧸ S.subgroupOf T), F (p, r)
      = (Nat.card (T ⧸ S.subgroupOf T) : ℂ) * u (Quotient.out p) := fun p =>
    finsum_const_eq_card_mul (u (Quotient.out p))
  have hffin : (Function.support fun (p : H ⧸ T) => u (Quotient.out p)).Finite := by
    apply (hfin.image fun q => (e q).1).subset
    intro p hp
    refine ⟨((Quotient.out p : H) : H ⧸ S), ?_, ?_⟩
    · have h5 : u (Quotient.out ((Quotient.out p : H) : H ⧸ S)) = u (Quotient.out p) :=
        quotient_out_right_invariant S u huS _
      simpa [Function.mem_support, h5] using hp
    · show (e ((Quotient.out p : H) : H ⧸ S)).1 = p
      rw [hfst]
      exact QuotientGroup.out_eq' p
  rw [h1, h2, h3, finsum_congr h4, hcard]
  have hsub : (Function.support fun p : H ⧸ T =>
      (Nat.card (T ⧸ S.subgroupOf T) : ℂ) * u (Quotient.out p)) ⊆ ↑hffin.toFinset := by
    intro p hp
    rw [Set.Finite.coe_toFinset, Function.mem_support]
    rw [Function.mem_support] at hp
    intro h0
    apply hp
    simp only [h0, mul_zero]
  rw [finsum_eq_sum_of_support_subset _ hsub, finsum_eq_sum _ hffin, Finset.mul_sum]

end UpperTheory.Reformulated.B.P6.r20a
end

noncomputable section

open GlobalTheory.BCT

namespace PositivityTheory.Rg.BcN.F2.LocOpPf

theorem finsum_quot_le {H : Type} [Group H] {S T : Subgroup H} (hST : S ≤ T) (u : H → ℂ)
    (hu : ∀ x, ∀ t ∈ T, u (x * t) = u x) (hrel : S.relIndex T ≠ 0)
    (hfin : (Function.support fun q : H ⧸ S => u q.out).Finite) :
    ∑ᶠ q : H ⧸ S, u q.out = (S.relIndex T : ℂ) * ∑ᶠ q : H ⧸ T, u q.out :=
  _root_.UpperTheory.Reformulated.B.P6.r20a.PositivityTheory.Rg.BcN.F2.LocOpPf.finsum_quot_le hST u hu hrel hfin

theorem hinteq {H : Type} [Group H] (K S : Subgroup H) (u : H → ℂ) (hSK : S ≤ K) (hSu : S ≤ rStab u)
    (hrel : S.relIndex K ≠ 0) (hfin : (Function.support fun q : H ⧸ S => u q.out).Finite) :
    hint K u = ((S.relIndex K : ℂ))⁻¹ * ∑ᶠ q : H ⧸ S, u q.out := by
  have hS0 : S ≤ rStab u ⊓ K := le_inf hSu hSK
  have hmul := Subgroup.relIndex_mul_relIndex S (rStab u ⊓ K) K hS0 inf_le_right
  have h1 : S.relIndex (rStab u ⊓ K) ≠ 0 := by
    intro h; rw [h, zero_mul] at hmul; exact hrel hmul.symm
  have h2 : (rStab u ⊓ K).relIndex K ≠ 0 := by
    intro h; rw [h, mul_zero] at hmul; exact hrel hmul.symm
  have hu : ∀ x, ∀ t ∈ rStab u ⊓ K, u (x * t) = u x := fun x t ht => ht.1 x
  rw [finsum_quot_le hS0 u hu h1 hfin, hint, ← hmul]
  push_cast
  field_simp

end PositivityTheory.Rg.BcN.F2.LocOpPf
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LocalActionPowers.PfmpowAlg
section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LocalActionPowers.PfmpowLev
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.FA.MatrixConvolutionPowers

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem thL_cont_invol (n : ℕ) (w : Pl E) : Continuous (thL n w) ∧ ∀ g : GLw n w, thL n w (thL n w g) = g := by
  unfold thL
  split_ifs
  · exact ⟨continuous_id, fun g => rfl⟩
  · exact ⟨GlobalTheory.LocTwist.continuous_thetaGL n (cj w) (GlobalTheory.CompanionTheory.IwUFacts.continuous_cj w),
      GlobalTheory.LocTwist.thetaGL_thetaGL n (cj w) (GlobalTheory.PrincCong.cj_cj w)⟩

theorem level_of_comap {G₁ G₂ : Type} [Group G₁] [Group G₂] [TopologicalSpace G₁] [TopologicalSpace G₂]
    [IsTopologicalGroup G₁] [IsTopologicalGroup G₂]
    (θ : G₁ →* G₁) (hθ : Continuous θ) (hθθ : ∀ g, θ (θ g) = g) (ι : G₁ →* G₂) (hι : Continuous ι)
    (U : Subgroup G₂) (hU : IsOpen (U : Set G₂)) (K : Subgroup G₁) (hK : ∀ g, ι g ∈ U → g ∈ K) :
    IsLevel θ K (U.comap ι ⊓ U.comap (ι.comp θ)) ∧ ∀ g ∈ U.comap ι ⊓ U.comap (ι.comp θ), ι g ∈ U := by
  refine ⟨⟨?_, fun g hg => hK g (Subgroup.mem_inf.1 hg).1, fun k hk => ?_⟩, fun g hg => (Subgroup.mem_inf.1 hg).1⟩
  · rw [Subgroup.coe_inf, Subgroup.coe_comap, Subgroup.coe_comap]
    exact (hU.preimage hι).inter (hU.preimage (hι.comp hθ))
  · obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hk
    refine Subgroup.mem_inf.2 ⟨h2, ?_⟩
    change ι (θ (θ k)) ∈ U
    rw [hθθ]; exact h1

theorem exists_level_prod (w : Pl E) (U : Subgroup (GLw a w × GLw b w)) (hU : IsOpen (U : Set (GLw a w × GLw b w)))
    (hle : U ≤ K2 a b w) :
    ∃ (V₁ : Subgroup (GLw a w)) (V₂ : Subgroup (GLw b w)), IsLevel (thL a w) (GlobalTheory.LFun.KGL w (n := a)) V₁ ∧
      IsLevel (thL b w) (GlobalTheory.LFun.KGL w (n := b)) V₂ ∧ V₁.prod V₂ ≤ U := by
  obtain ⟨c₁, i₁⟩ := thL_cont_invol (E := E) a w
  obtain ⟨c₂, i₂⟩ := thL_cont_invol (E := E) b w
  have hl := level_of_comap (thL a w) c₁ i₁ (MonoidHom.inl (GLw a w) (GLw b w))
    (continuous_id.prodMk continuous_const) U hU (GlobalTheory.LFun.KGL w (n := a))
    (fun g hg => (Subgroup.mem_prod.1 (hle hg)).1)
  have hr := level_of_comap (thL b w) c₂ i₂ (MonoidHom.inr (GLw a w) (GLw b w))
    (continuous_const.prodMk continuous_id) U hU (GlobalTheory.LFun.KGL w (n := b))
    (fun g hg => (Subgroup.mem_prod.1 (hle hg)).2)
  refine ⟨_, _, hl.1, hr.1, fun x hx => ?_⟩
  obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_prod.1 hx
  have e : x = MonoidHom.inl (GLw a w) (GLw b w) x.1 * MonoidHom.inr (GLw a w) (GLw b w) x.2 := by
    ext <;> simp
  rw [e]
  exact U.mul_mem (hl.2 _ hx₁) (hr.2 _ hx₂)

theorem isHecke_idem {w : Pl E} (V₁ : Subgroup (GLw a w)) (V₂ : Subgroup (GLw b w))
    (hV₁ : IsLevel (thL a w) (GlobalTheory.LFun.KGL w (n := a)) V₁) (hV₂ : IsLevel (thL b w) (GlobalTheory.LFun.KGL w (n := b)) V₂) :
    IsHecke (V₁.prod V₂) (idem (V₁.prod V₂)) := by
  have hVo : IsOpen ((V₁.prod V₂ : Subgroup (GLw a w × GLw b w)) : Set (GLw a w × GLw b w)) := by
    rw [Subgroup.coe_prod]; exact hV₁.1.prod hV₂.1
  have hVc : IsClosed ((V₁.prod V₂ : Subgroup (GLw a w × GLw b w)) : Set (GLw a w × GLw b w)) :=
    Subgroup.isClosed_of_isOpen _ hVo
  have hK : IsCompact ((K2 a b w : Subgroup (GLw a w × GLw b w)) : Set (GLw a w × GLw b w)) := by
    rw [K2, Subgroup.coe_prod]
    exact (GlobalTheory.CompanionTheory.IwLevels.isCompact_KGL w a).prod (GlobalTheory.CompanionTheory.IwLevels.isCompact_KGL w b)
  have hsub : ((V₁.prod V₂ : Subgroup (GLw a w × GLw b w)) : Set (GLw a w × GLw b w)) ⊆ (K2 a b w : Set _) := by
    intro x hx
    obtain ⟨h1, h2⟩ := Subgroup.mem_prod.1 hx
    exact Subgroup.mem_prod.2 ⟨hV₁.2.1 h1, hV₂.2.1 h2⟩
  refine ⟨HasCompactSupport.intro' (hK.of_isClosed_subset hVc hsub) hVc fun x hx => ?_, fun k hk x => ⟨?_, ?_⟩⟩
  · unfold idem; exact Set.indicator_of_notMem hx _
  · unfold idem
    by_cases hx : x ∈ V₁.prod V₂
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((V₁.prod V₂).mul_mem hk hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (by simpa using (V₁.prod V₂).mul_mem ((V₁.prod V₂).inv_mem hk) h))]
  · unfold idem
    by_cases hx : x ∈ V₁.prod V₂
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((V₁.prod V₂).mul_mem hx hk)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (by simpa using (V₁.prod V₂).mul_mem h ((V₁.prod V₂).inv_mem hk)))]

end PositivityTheory.Rg.BcB.F.FA.MatrixConvolutionPowers

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LocalActionPowers.PfmpowLoc
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail
open PositivityTheory.Rg.BcN.F2 (mconv)
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.FA.MatrixConvolutionPowers

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem relIndex_ne {w : Pl E} {V : Subgroup (GLw a w × GLw b w)} (hV : IsOpen (V : Set (GLw a w × GLw b w)))
    (hle : V ≤ K2 a b w) : V.relIndex (K2 a b w) ≠ 0 := by
  have hK : IsCompact ((K2 a b w : Subgroup (GLw a w × GLw b w)) : Set (GLw a w × GLw b w)) := by
    have := (GlobalTheory.CompanionTheory.IwLevels.isCompact_KGL w a).prod (GlobalTheory.CompanionTheory.IwLevels.isCompact_KGL w b)
    simpa [K2, Subgroup.coe_prod] using this
  exact GlobalTheory.CompanionTheory.IwLevels.relIndex_ne_zero hV hK

theorem idem_left {w : Pl E} {V : Subgroup (GLw a w × GLw b w)} {v : GLw a w × GLw b w} (hv : v ∈ V)
    (g0 : GLw a w × GLw b w) : idem V (v * g0) = idem V g0 := by
  unfold idem
  by_cases hg : g0 ∈ V
  · rw [Set.indicator_of_mem (V.mul_mem hv hg), Set.indicator_of_mem hg]
  · have : v * g0 ∉ V := fun h => hg (by simpa using V.mul_mem (V.inv_mem hv) h)
    rw [Set.indicator_of_notMem this, Set.indicator_of_notMem hg]

theorem idem_right {w : Pl E} {V : Subgroup (GLw a w × GLw b w)} {v : GLw a w × GLw b w} (hv : v ∈ V)
    (g0 : GLw a w × GLw b w) : idem V (g0 * v) = idem V g0 := by
  unfold idem
  by_cases hg : g0 ∈ V
  · rw [Set.indicator_of_mem (V.mul_mem hg hv), Set.indicator_of_mem hg]
  · have : g0 * v ∉ V := fun h => hg (by simpa using V.mul_mem h (V.inv_mem hv))
    rw [Set.indicator_of_notMem this, Set.indicator_of_notMem hg]

theorem mconv_zero_left {w : Pl E} (f : GLw a w × GLw b w → ℂ) :
    mconv (fun _ => (0 : ℂ)) f = fun _ => 0 := by
  funext m
  unfold mconv
  simpa using FinConv.hint_zero ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b)))

theorem mconv_zero_right {w : Pl E} (f : GLw a w × GLw b w → ℂ) :
    mconv f (fun _ => (0 : ℂ)) = fun _ => 0 := by
  funext m
  unfold mconv
  simpa using FinConv.hint_zero ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b)))

theorem mconv_left {w : Pl E} {f g : GLw a w × GLw b w → ℂ} {v : GLw a w × GLw b w} (hf : ∀ x, f (v * x) = f x)
    (m : GLw a w × GLw b w) : mconv f g (v * m) = mconv f g m := by
  unfold mconv
  calc hint ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))) (fun m' => f m' * g (m'⁻¹ * (v * m)))
      = hint ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b)))
          (fun z => (fun z => f (v * z) * g (z⁻¹ * m)) (v⁻¹ * z)) := by
        congr 1; funext z; simp [mul_assoc]
    _ = hint ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))) (fun z => f (v * z) * g (z⁻¹ * m)) :=
        FinConv.hint_left _ (fun z => f (v * z) * g (z⁻¹ * m)) v⁻¹
    _ = _ := by congr 1; funext z; rw [hf]

theorem mconv_right {w : Pl E} {f g : GLw a w × GLw b w → ℂ} {v : GLw a w × GLw b w} (hg : ∀ x, g (x * v) = g x)
    (m : GLw a w × GLw b w) : mconv f g (m * v) = mconv f g m := by
  unfold mconv
  congr 1; funext z; rw [← mul_assoc, hg]

theorem mconv_idem_left {w : Pl E} {V : Subgroup (GLw a w × GLw b w)} (hV : IsOpen (V : Set (GLw a w × GLw b w)))
    (hle : V ≤ K2 a b w) {f : GLw a w × GLw b w → ℂ} (hf : ∀ v ∈ V, ∀ x, f (v * x) = f x) :
    mconv (idem V) f = f := by
  funext m
  have hr := relIndex_ne hV hle
  set u : GLw a w × GLw b w → ℂ := fun m' => idem V m' * f (m'⁻¹ * m) with hu
  have hSu : V ≤ rStab u := by
    intro k hk x
    simp only [hu]
    rw [idem_right hk, _root_.mul_inv_rev, mul_assoc, hf _ (V.inv_mem hk)]
  have hsupp : ∀ q : (GLw a w × GLw b w) ⧸ V, q ≠ QuotientGroup.mk 1 → u q.out = 0 := by
    intro q hq
    simp only [hu]
    have : q.out ∉ V := by
      intro hm
      apply hq
      rw [← QuotientGroup.out_eq' q]
      exact QuotientGroup.eq.2 (by simpa using V.inv_mem hm)
    unfold idem
    rw [Set.indicator_of_notMem this, zero_mul]
  have hfin : (Function.support fun q : (GLw a w × GLw b w) ⧸ V => u q.out).Finite := by
    refine (Set.finite_singleton (QuotientGroup.mk 1 : (GLw a w × GLw b w) ⧸ V)).subset fun q hq => ?_
    by_contra hne
    exact hq (hsupp q hne)
  have h := PositivityTheory.Rg.BcN.F2.LocOpPf.hinteq (K2 a b w) V u hle hSu hr hfin
  change hint ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))) u = f m
  rw [show ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))) = K2 a b w from rfl, h,
    finsum_eq_single _ (QuotientGroup.mk 1) hsupp]
  obtain ⟨hh, e⟩ := QuotientGroup.mk_out_eq_mul V (1 : GLw a w × GLw b w)
  simp only [hu]
  rw [e, one_mul]
  unfold idem
  rw [Set.indicator_of_mem hh.2, hf _ (V.inv_mem hh.2)]
  have : ((V.relIndex (K2 a b w) : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hr
  field_simp

theorem mconv_idem_right {w : Pl E} {V : Subgroup (GLw a w × GLw b w)} (hV : IsOpen (V : Set (GLw a w × GLw b w)))
    (hle : V ≤ K2 a b w) {f : GLw a w × GLw b w → ℂ} (hf : ∀ v ∈ V, ∀ x, f (x * v) = f x) :
    mconv f (idem V) = f := by
  funext m
  have hr := relIndex_ne hV hle
  set u : GLw a w × GLw b w → ℂ := fun m' => f m' * idem V (m'⁻¹ * m) with hu
  have hSu : V ≤ rStab u := by
    intro k hk x
    simp only [hu]
    rw [hf _ hk, _root_.mul_inv_rev, mul_assoc, idem_left (V.inv_mem hk)]
  have hsupp : ∀ q : (GLw a w × GLw b w) ⧸ V, q ≠ QuotientGroup.mk m → u q.out = 0 := by
    intro q hq
    simp only [hu]
    have : q.out⁻¹ * m ∉ V := by
      intro hm
      apply hq
      rw [← QuotientGroup.out_eq' q]
      exact QuotientGroup.eq.2 hm
    unfold idem
    rw [Set.indicator_of_notMem this, mul_zero]
  have hfin : (Function.support fun q : (GLw a w × GLw b w) ⧸ V => u q.out).Finite := by
    refine (Set.finite_singleton (QuotientGroup.mk m : (GLw a w × GLw b w) ⧸ V)).subset fun q hq => ?_
    by_contra hne
    exact hq (hsupp q hne)
  have h := PositivityTheory.Rg.BcN.F2.LocOpPf.hinteq (K2 a b w) V u hle hSu hr hfin
  change hint ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))) u = f m
  rw [show ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))) = K2 a b w from rfl, h,
    finsum_eq_single _ (QuotientGroup.mk m) hsupp]
  obtain ⟨hh, e⟩ := QuotientGroup.mk_out_eq_mul V m
  simp only [hu]
  rw [e, hf _ hh.2]
  unfold idem
  rw [Set.indicator_of_mem (by simpa using V.inv_mem hh.2)]
  have : ((V.relIndex (K2 a b w) : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hr
  field_simp

end PositivityTheory.Rg.BcB.F.FA.MatrixConvolutionPowers

end
end

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail
open PositivityTheory.Rg.BcN.F2 (mconv)
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.FA.MatrixConvolutionPowers

set_option linter.unusedSectionVars false

attribute [local instance] borelG borelF borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem fixed_mono {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V] (ρ : Representation k G V)
    {K K' : Subgroup G} (hle : K' ≤ K) {v : V} (hv : v ∈ fixed ρ K) : v ∈ fixed ρ K' := by
  simp only [GlobalTheory.PRep.fixed, GlobalTheory.PRep.eig, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_ofPred_eq] at hv ⊢
  intro h
  exact hv ⟨h.1, hle h.2⟩

theorem isHecke_zero {G : Type} [Group G] [TopologicalSpace G] (K : Subgroup G) : IsHecke K (fun _ : G => (0 : ℂ)) :=
  ⟨HasCompactSupport.zero, fun _ _ _ => ⟨rfl, rfl⟩⟩

theorem isTestFunction_modify {φ ψ : ∀ w : Pl E, GLw a w × GLw b w → ℂ} (hφ : IsTestP φ) (T : Finset (Pl E))
    (V₁ : ∀ w : Pl E, Subgroup (GLw a w)) (V₂ : ∀ w : Pl E, Subgroup (GLw b w))
    (hV₁ : ∀ w, IsLevel (thL a w) (GlobalTheory.LFun.KGL w (n := a)) (V₁ w)) (hV₂ : ∀ w, IsLevel (thL b w) (GlobalTheory.LFun.KGL w (n := b)) (V₂ w))
    (hout : ∀ w, w ∉ T → ψ w = φ w) (hin : ∀ w ∈ T, IsHecke ((V₁ w).prod (V₂ w)) (ψ w)) : IsTestP ψ := by
  obtain ⟨K₁, K₂, hK₁, hK₂, hT⟩ := hφ
  refine ⟨fun w => if w ∈ T then V₁ w else K₁ w, fun w => if w ∈ T then V₂ w else K₂ w, ⟨fun w => ?_, ?_⟩,
    ⟨fun w => ?_, ?_⟩, fun w => ?_, ?_⟩
  · by_cases h : w ∈ T
    · simp only [h, if_true]; exact hV₁ w
    · simp only [h, if_false]; exact hK₁.1 w
  · filter_upwards [hK₁.2, T.finite_toSet.compl_mem_cofinite] with w hw hwT
    simp only [Set.mem_compl_iff, Finset.mem_coe] at hwT
    simp only [hwT, if_false, hw]
  · by_cases h : w ∈ T
    · simp only [h, if_true]; exact hV₂ w
    · simp only [h, if_false]; exact hK₂.1 w
  · filter_upwards [hK₂.2, T.finite_toSet.compl_mem_cofinite] with w hw hwT
    simp only [Set.mem_compl_iff, Finset.mem_coe] at hwT
    simp only [hwT, if_false, hw]
  · by_cases h : w ∈ T
    · simp only [h, if_true]; exact hin w h
    · simp only [h, if_false]; rw [hout w h]; exact hT.1 w
  · filter_upwards [hT.2, T.finite_toSet.compl_mem_cofinite] with w hw hwT
    simp only [Set.mem_compl_iff, Finset.mem_coe] at hwT
    rw [hout w hwT, hw]

theorem hasLev_zero : HasLev (0 : H E a b → ℂ) :=
  ⟨⊤, by rw [Subgroup.coe_top]; exact isOpen_univ, fun _ _ _ => rfl⟩

theorem hasLev_add {G G' : H E a b → ℂ} (h : HasLev G) (h' : HasLev G') : HasLev (G + G') := by
  obtain ⟨U, hU, hG⟩ := h
  obtain ⟨U', hU', hG'⟩ := h'
  refine ⟨U ⊓ U', by rw [Subgroup.coe_inf]; exact hU.inter hU', fun u hu x => ?_⟩
  have hu' := Subgroup.mem_inf.1 hu
  simp only [Pi.add_apply, hG u hu'.1 x, hG' u hu'.2 x]

theorem hasLev_sum {ι : Type} (s : Finset ι) (g : ι → H E a b → ℂ) (h : ∀ i ∈ s, HasLev (g i)) :
    HasLev (∑ i ∈ s, g i) := by
  induction s using Finset.induction_on with
  | empty => simpa using (hasLev_zero (E := E) (a := a) (b := b))
  | insert x s hx ih =>
    rw [Finset.sum_insert hx]
    exact hasLev_add (h x (Finset.mem_insert_self x s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem uniform_lev {ι : Type} [Finite ι] (G : ι → H E a b → ℂ) (h : ∀ i, HasLev (G i)) :
    ∃ U : Subgroup (Hf E a b), IsOpen (U : Set (Hf E a b)) ∧ ∀ i, ∀ u ∈ U, ∀ x, G i (x * finH u) = G i x := by
  choose U hU hG using h
  refine ⟨⨅ i, U i, ?_, fun i u hu x => hG i u (Subgroup.mem_iInf.1 hu i) x⟩
  rw [Subgroup.coe_iInf]
  exact isOpen_iInter_of_finite hU

theorem convF_congr {A A' κ : Type} [Fintype κ] [MeasurableSpace (Hf E a b)] (ν : Measure (Hf E a b))
    (ψ : Matrix κ κ (Hf E a b → ℂ)) (G : A × κ → H E a b → ℂ) (G' : A' × κ → H E a b → ℂ) (p : A) (q : A')
    (h : ∀ z, G (p, z) = G' (q, z)) (x : κ) : convF ν ψ G (p, x) = convF ν ψ G' (q, x) := by
  funext y
  simp only [convF, h]

theorem convF_zero {A κ : Type} [Fintype κ] [MeasurableSpace (Hf E a b)] (ν : Measure (Hf E a b))
    (ψ : Matrix κ κ (Hf E a b → ℂ)) : convF ν ψ (0 : A × κ → H E a b → ℂ) = 0 := by
  funext i y
  simp [convF]

theorem iter_restrict {A κ : Type} [Fintype κ] [MeasurableSpace (Hf E a b)] (ν : Measure (Hf E a b))
    (ψ : Matrix κ κ (Hf E a b → ℂ)) (F : A × κ → H E a b → ℂ) (p : A) (k : ℕ) (x : κ) :
    (convF ν ψ)^[k] F (p, x) = (convF ν ψ)^[k] (fun i : Unit × κ => F (p, i.2)) ((), x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact convF_congr ν ψ _ _ p () (fun z => ih z) x

section
variable {κ : Pl E → Type} [∀ w, Fintype (κ w)]

def pw (M : LM κ a b) : ℕ → LM κ a b
  | 0 => M
  | k + 1 => M.mul (pw M k)

theorem mul_m (M M' : LM κ a b) (w : Pl E) (x y : κ w) :
    (M.mul M').m w x y = ∑ z, mconv (M.m w x z) (M'.m w z y) := rfl

theorem mul_s (M M' : LM κ a b) (w : Pl E) : (M.mul M').s w = mconv (M.s w) (M'.s w) := rfl

theorem product_torus_component (M M' : LM κ a b) (w : Pl E) : (M.mul M').t w = mconv (M.t w) (M'.t w) := rfl

def dg (V : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)) (w : Pl E) (x y : κ w) : GLw a w × GLw b w → ℂ :=
  if x = y then idem (V w) else fun _ => 0

def only0 (L : LM κ a b) (V : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)) (w₀ : Pl E) : LM κ a b :=
  ⟨fun w x y => if w = w₀ then L.m w x y else dg V w x y, L.s, L.t⟩

def rest1 (L : LM κ a b) (V : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)) (w₀ : Pl E) : LM κ a b :=
  ⟨fun w x y => if w = w₀ then dg V w x y else L.m w x y, L.s, L.t⟩

theorem dg_mul_left (V : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)) (w : Pl E) (x : κ w)
    (f : κ w → GLw a w × GLw b w → ℂ) : ∑ z, mconv (dg V w x z) (f z) = mconv (idem (V w)) (f x) := by
  rw [Finset.sum_eq_single x]
  · simp [dg]
  · intro z _ hz
    simp only [dg, if_neg (Ne.symm hz)]
    exact mconv_zero_left _
  · simp

theorem dg_mul_right (V : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)) (w : Pl E) (y : κ w)
    (f : κ w → GLw a w × GLw b w → ℂ) : ∑ z, mconv (f z) (dg V w z y) = mconv (f y) (idem (V w)) := by
  rw [Finset.sum_eq_single y]
  · simp [dg]
  · intro z _ hz
    simp only [dg, if_neg hz]
    exact mconv_zero_right _
  · simp

theorem mconv_idem_dg {V : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)} {w : Pl E}
    (hV : IsOpen (V w : Set (GLw a w × GLw b w))) (hle : V w ≤ K2 a b w) (x y : κ w) :
    mconv (idem (V w)) (dg V w x y) = dg V w x y := by
  unfold dg
  split_ifs
  · exact mconv_idem_left hV hle fun v hv g => idem_left hv g
  · exact mconv_zero_right _

theorem stabilizerDilationWeights_dualIsotropicVector (M : LM κ a b) (W : ∀ w : Pl E, Subgroup (GLw a w × GLw b w))
    (hW : ∀ w, IsOpen (W w : Set (GLw a w × GLw b w)) ∧ W w ≤ K2 a b w) (hs : ∀ w, M.s w = idem (W w)) :
    ∀ k w, (pw M k).s w = idem (W w) := by
  intro k
  induction k with
  | zero => exact hs
  | succ k ih =>
    intro w
    show mconv (M.s w) ((pw M k).s w) = _
    rw [hs, ih]
    exact mconv_idem_left (hW w).1 (hW w).2 fun v hv g => idem_left hv g

theorem power_torus_component_idempotent (M : LM κ a b) (W : ∀ w : Pl E, Subgroup (GLw a w × GLw b w))
    (hW : ∀ w, IsOpen (W w : Set (GLw a w × GLw b w)) ∧ W w ≤ K2 a b w) (ht : ∀ w, M.t w = idem (W w)) :
    ∀ k w, (pw M k).t w = idem (W w) := by
  intro k
  induction k with
  | zero => exact ht
  | succ k ih =>
    intro w
    show mconv (M.t w) ((pw M k).t w) = _
    rw [ht, ih]
    exact mconv_idem_left (hW w).1 (hW w).2 fun v hv g => idem_left hv g

theorem pw_m_congr (M M' : LM κ a b) (w : Pl E) (h : M.m w = M'.m w) : ∀ k, (pw M k).m w = (pw M' k).m w := by
  intro k
  induction k with
  | zero => exact h
  | succ k ih =>
    show (fun x y => ∑ z, mconv (M.m w x z) ((pw M k).m w z y)) =
      fun x y => ∑ z, mconv (M'.m w x z) ((pw M' k).m w z y)
    rw [h, ih]

theorem pw_dg (M : LM κ a b) (V : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)) (w : Pl E)
    (hV : IsOpen (V w : Set (GLw a w × GLw b w))) (hle : V w ≤ K2 a b w) (h : M.m w = dg V w) :
    ∀ k, (pw M k).m w = dg V w := by
  intro k
  induction k with
  | zero => exact h
  | succ k ih =>
    funext x y
    show ∑ z, mconv (M.m w x z) ((pw M k).m w z y) = _
    rw [h, ih, dg_mul_left V w x (fun z => dg V w z y)]
    exact mconv_idem_dg hV hle x y

theorem pw_left (M : LM κ a b) (w : Pl E) (W : Subgroup (GLw a w × GLw b w))
    (h : ∀ x y, ∀ v ∈ W, ∀ g, M.m w x y (v * g) = M.m w x y g) :
    ∀ k x y, ∀ v ∈ W, ∀ g, (pw M k).m w x y (v * g) = (pw M k).m w x y g := by
  intro k
  induction k with
  | zero => exact h
  | succ k ih =>
    intro x y v hv g
    show (∑ z, mconv (M.m w x z) ((pw M k).m w z y)) (v * g) = (∑ z, mconv (M.m w x z) ((pw M k).m w z y)) g
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl fun z _ => mconv_left (fun g' => h x z v hv g') g

theorem pw_right (M : LM κ a b) (w : Pl E) (W : Subgroup (GLw a w × GLw b w))
    (h : ∀ x y, ∀ v ∈ W, ∀ g, M.m w x y (g * v) = M.m w x y g) :
    ∀ k x y, ∀ v ∈ W, ∀ g, (pw M k).m w x y (g * v) = (pw M k).m w x y g := by
  intro k
  induction k with
  | zero => exact h
  | succ k ih =>
    intro x y v hv g
    show (∑ z, mconv (M.m w x z) ((pw M k).m w z y)) (g * v) = (∑ z, mconv (M.m w x z) ((pw M k).m w z y)) g
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl fun z _ => mconv_right (fun g' => ih z y v hv g') g

end

section
variable {κ : Pl E → Type} [∀ w, Fintype (κ w)]

theorem pw_ok (hA : FmAlg) (S : Set (Pl E)) (P : Finset (Pl E)) (B : Block E) (e : B.κ ≃ ∀ w : P, κ w)
    (hS : IsSection S) (hP : (↑P : Set (Pl E)) ⊆ S) (M : LM κ B.a B.b) (hM : M.Ok P) : ∀ k, (pw M k).Ok P := by
  intro k
  induction k with
  | zero => exact hM
  | succ k ih => exact (hA E κ S P B e hS hP M (pw M k) hM ih).2.1

theorem iter_pw (hA : FmAlg) (hC : ConvMul) (S : Set (Pl E)) (P : Finset (Pl E)) (B : Block E)
    (e : B.κ ≃ ∀ w : P, κ w) (hS : IsSection S) (hP : (↑P : Set (Pl E)) ⊆ S) (M : LM κ B.a B.b) (hM : M.Ok P)
    {A : Type} (G : A × B.κ → H E B.a B.b → ℂ) (U : Subgroup (Hf E B.a B.b)) (hU : IsOpen (U : Set (Hf E B.a B.b)))
    (hG : ∀ i, ∀ u ∈ U, ∀ x, G i (x * finH u) = G i x) :
    ∀ k, (convF B.ν (fm S P B e M))^[k + 1] G = convF B.ν (fm S P B e (pw M k)) G := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    have hk := pw_ok hA S P B e hS hP M hM k
    obtain ⟨h1, -, h3, -⟩ := hA E κ S P B e hS hP M (pw M k) hM hk
    have h2 := (hA E κ S P B e hS hP (pw M k) M hk hM).1
    rw [← (hC E B A _ _ U G h1 h2 hU hG).1, h3]
    rfl

end

end PositivityTheory.Rg.BcB.F.FA.MatrixConvolutionPowers

end
end

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail
open PositivityTheory.Rg.BcN.F2 (mconv)
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.FA

attribute [local instance] borelG borelF borelH

open MatrixConvolutionPowers

theorem fmPowOf_holds : FmPowOf := by
  intro hA hAtP hC hAct hIdem
  intro E _ _ _ κ _ S P B e hS hP U₁ U₂ L A F m hU₁ hU₂ hL hs ht hbi hF hne w₀
  by_contra hcon
  push Not at hcon
  apply hne
  funext i
  obtain ⟨p, k⟩ := i

  choose V₁ V₂ hV₁ hV₂ hVU using fun w => exists_level_prod w (U₁ w) (hU₁.1 w).1 (hU₁.1 w).2
  set V : ∀ w : Pl E, Subgroup (GLw B.a w × GLw B.b w) := fun w => (V₁ w).prod (V₂ w) with hVdef
  have hVo : ∀ w, IsOpen (V w : Set (GLw B.a w × GLw B.b w)) := fun w => by
    rw [hVdef, Subgroup.coe_prod]; exact (hV₁ w).1.prod (hV₂ w).1
  have hVK : ∀ w, V w ≤ K2 B.a B.b w := fun w => Subgroup.prod_mono (hV₁ w).2.1 (hV₂ w).2.1
  have hVH : ∀ w, IsHecke (V w) (idem (V w)) := fun w => isHecke_idem (V₁ w) (V₂ w) (hV₁ w) (hV₂ w)
  have hdgH : ∀ w (x y : κ w), IsHecke (V w) (dg V w x y) := fun w x y => by
    unfold dg; split_ifs
    · exact hVH w
    · exact isHecke_zero _
  have hw₀P : w₀.1 ∈ P := w₀.2
  set L0 := only0 L V w₀.1 with hL0
  set L1 := rest1 L V w₀.1 with hL1
  have hL0s : L0.s = L.s := by rw [hL0]; rfl
  have hL0t : L0.t = L.t := by rw [hL0]; rfl
  have hL1s : L1.s = L.s := by rw [hL1]; rfl
  have hL1t : L1.t = L.t := by rw [hL1]; rfl
  clear_value L0 L1

  have hL0ok : L0.Ok P := by
    refine ⟨fun x y => isTestFunction_modify (hL.1 x y) (P.erase w₀.1) V₁ V₂ hV₁ hV₂ (fun w hw => ?_) (fun w hw => ?_), by rw [hL0t]; exact hL.2⟩
    · unfold LM.ent
      split_ifs with hwP
      · have : w = w₀.1 := by
          by_contra hne'; exact hw (Finset.mem_erase.2 ⟨hne', hwP⟩)
        subst this
        simp [hL0, only0]
      · rw [hL0s]
    · obtain ⟨hne', hwP⟩ := Finset.mem_erase.1 hw
      unfold LM.ent
      rw [dif_pos hwP]
      simp only [hL0, only0, if_neg hne']
      exact hdgH w _ _
  have hL1ok : L1.Ok P := by
    refine ⟨fun x y => isTestFunction_modify (hL.1 x y) {w₀.1} V₁ V₂ hV₁ hV₂ (fun w hw => ?_) (fun w hw => ?_), by rw [hL1t]; exact hL.2⟩
    · have hne' : w ≠ w₀.1 := fun h => hw (Finset.mem_singleton.2 h)
      unfold LM.ent
      split_ifs with hwP
      · simp [hL1, rest1, hne']
      · rw [hL1s]
    · rw [Finset.mem_singleton.1 hw]
      unfold LM.ent
      rw [dif_pos hw₀P]
      simp only [hL1, rest1, if_true]
      exact hdgH _ _ _

  set Φ : ∀ w : Pl E, GLw B.a w × GLw B.b w → ℂ := fun w => if w ∈ P then idem (V w) else L.s w with hΦ
  have hΦt : IsTestP Φ := by
    refine isTestFunction_modify (hL.1 (e k) (e k)) P V₁ V₂ hV₁ hV₂ (fun w hw => ?_) (fun w hw => ?_)
    · simp only [hΦ, if_neg hw, LM.ent, dif_neg hw]
    · simp only [hΦ, if_pos hw]; exact hVH w
  have hΨt : IsTestP L.t := hL.2
  let Good : (Unit × B.κ → H E B.a B.b → ℂ) → Prop := fun G =>
    ∀ i, HasLev (G i) ∧ ∀ j : Slot S, actS Φ L.t j (G i) = G i
  set i₀ : Slot S := Sum.inl ⟨w₀.1, hP w₀.2⟩ with hi₀

  have hform : ∀ G, Good G → ∀ x, convF B.ν (fm S P B e L0) G ((), x) =
      ∑ y : κ w₀, actP w₀.1 (L.m w₀.1 (e x w₀) y) (G ((), e.symm (Function.update (e x) w₀ y))) := by
    intro G hG x
    have hQ : Quiet S P B e L0 i₀ G := by
      refine ⟨fun w hwP hw x' y' hxy => ?_, fun j hj q x' y' hag => ?_⟩
      · have hne' : w ≠ w₀.1 := fun h => hw (hP hwP) (by subst h; rfl)
        simp only [hL0, only0, if_neg hne', dg, if_neg hxy]
        rfl
      · obtain ⟨⟩ := q
        cases j with
        | inl w' =>
          have hent : LM.ent P L0 (e x') (e y') w'.1 = Φ w'.1 := by
            unfold LM.ent
            by_cases hwP : w'.1 ∈ P
            · rw [dif_pos hwP]
              have hne' : w'.1 ≠ w₀.1 := fun h => hj (by rw [hi₀]; congr 1; exact Subtype.ext h)
              have hxy : e x' ⟨w'.1, hwP⟩ = e y' ⟨w'.1, hwP⟩ := hag ⟨w'.1, hwP⟩ fun h he =>
                hne' (congrArg Subtype.val (Sum.inl_injective he)).symm
              simp only [hL0, only0, if_neg hne', dg, hxy, if_true, hΦ, if_pos hwP]
            · rw [dif_neg hwP]
              simp only [hL0, only0, hΦ, if_neg hwP]
          show actP w'.1 (LM.ent P L0 (e x') (e y') w'.1) (G ((), y')) = G ((), y')
          rw [hent]
          exact (hG ((), y')).2 (Sum.inl w')
        | inr w' =>
          show actT w'.1 (L0.t w'.1) (G ((), y')) = G ((), y')
          rw [hL0t]
          exact (hG ((), y')).2 (Sum.inr w')
    have h := hAtP E κ S P B e hS hP Unit L0 w₀ G hL0ok (fun i => (hG i).1) hQ () x
    rw [h]
    simp only [hL0, only0, if_true]

  have hterm : ∀ (x : B.κ) (y : κ w₀) (g : H E B.a B.b → ℂ), HasLev g → (∀ j : Slot S, actS Φ L.t j g = g) →
      HasLev (actP w₀.1 (L.m w₀.1 (e x w₀) y) g) ∧
        ∀ j : Slot S, actS Φ L.t j (actP w₀.1 (L.m w₀.1 (e x w₀) y) g) = actP w₀.1 (L.m w₀.1 (e x w₀) y) g := by
    intro x y g hg hfix
    set ψ₁ := LM.ent P L (e x) (Function.update (e x) w₀ y) with hψ₁
    have hψt : IsTestP ψ₁ := hL.1 _ _
    have hψw : ψ₁ w₀.1 = L.m w₀.1 (e x w₀) y := by
      simp only [hψ₁, LM.ent, dif_pos hw₀P, Function.update_self]
    have hT : actP w₀.1 (L.m w₀.1 (e x w₀) y) g = actS ψ₁ L.t i₀ g := by
      show _ = actP w₀.1 (ψ₁ w₀.1) g
      rw [hψw]
    rw [hT]
    refine ⟨(hAct E B.a B.b S hS ψ₁ L.t ψ₁ L.t hψt hΨt hψt hΨt g g hg hg i₀ i₀).1, fun j => ?_⟩
    by_cases hj : j = i₀
    · subst hj
      have key := (hAct E B.a B.b S hS Φ L.t ψ₁ L.t hΦt hΨt hψt hΨt g g hg hg i₀ i₀).2.2.2
      rw [← key]
      show actP w₀.1 (mconv (Φ w₀.1) (ψ₁ w₀.1)) g = actP w₀.1 (ψ₁ w₀.1) g
      have hΦw : Φ w₀.1 = idem (V w₀.1) := by simp only [hΦ, if_pos hw₀P]
      rw [hΦw, mconv_idem_left (hVo _) (hVK _) fun v hv g' => ?_]
      rw [hψw]
      exact ((hbi w₀.1 hw₀P (e x w₀) y v (hVU w₀.1 hv) g').1)
    · rw [(hAct E B.a B.b S hS Φ L.t ψ₁ L.t hΦt hΨt hψt hΨt g g hg hg j i₀).2.2.1 hj, hfix j]

  have hact_sum : ∀ (j : Slot S) (s : Finset (κ w₀)) (T : κ w₀ → H E B.a B.b → ℂ), (∀ y, HasLev (T y)) →
      actS Φ L.t j (∑ y ∈ s, T y) = ∑ y ∈ s, actS Φ L.t j (T y) := by
    intro j s T hT
    induction s using Finset.induction_on with
    | empty =>
      have h0 := (hAct E B.a B.b S hS Φ L.t Φ L.t hΦt hΨt hΦt hΨt 0 0 hasLev_zero hasLev_zero j j).2.1 1
      simp only [add_zero, one_smul] at h0
      simpa using h0
    | insert z s hz ih =>
      rw [Finset.sum_insert hz, Finset.sum_insert hz]
      have h1 := (hAct E B.a B.b S hS Φ L.t Φ L.t hΦt hΨt hΦt hΨt (T z) (∑ y ∈ s, T y) (hT z)
        (hasLev_sum s T fun y _ => hT y) j j).2.1 1
      simp only [one_smul] at h1
      rw [h1, ih]

  have hgood : ∀ G, Good G → Good (convF B.ν (fm S P B e L0) G) := by
    intro G hG i
    obtain ⟨⟨⟩, x⟩ := i
    rw [hform G hG x]
    have hts := fun y => hterm x y _ (hG ((), e.symm (Function.update (e x) w₀ y))).1
      (hG ((), e.symm (Function.update (e x) w₀ y))).2
    refine ⟨hasLev_sum _ _ fun y _ => (hts y).1, fun j => ?_⟩
    rw [hact_sum j _ _ fun y => (hts y).1]
    exact Finset.sum_congr rfl fun y _ => (hts y).2 j
  have hgoodn : ∀ G, Good G → ∀ n, Good ((convF B.ν (fm S P B e L0))^[n] G) := by
    intro G hG n
    induction n with
    | zero => exact hG
    | succ n ih => rw [Function.iterate_succ_apply']; exact hgood _ ih

  have hslice : ∀ G, Good G → ∀ n (x' : ∀ w : P, κ w) (y : κ w₀),
      (convF B.ν (fm S P B e L0))^[n] G ((), e.symm (Function.update x' w₀ y)) =
        (locM w₀.1 (L.m w₀.1))^[n] (fun y => G ((), e.symm (Function.update x' w₀ y))) y := by
    intro G hG n
    induction n with
    | zero => intro x' y; rfl
    | succ n ih =>
      intro x' y
      rw [Function.iterate_succ_apply', hform _ (hgoodn G hG n), Function.iterate_succ_apply']
      simp only [Equiv.apply_symm_apply, Function.update_self, Function.update_idem, ih]
      rfl

  set Fp : Unit × B.κ → H E B.a B.b → ℂ := fun i => F (p, i.2) with hFp
  have hFgood : Good Fp := by
    intro i
    refine ⟨(hF (p, i.2)).1, fun j => ?_⟩
    cases j with
    | inl w' =>
      show actP w'.1 (Φ w'.1) (F (p, i.2)) = F (p, i.2)
      have hfix := ((hF (p, i.2)).2 w'.1 w'.2).1
      by_cases hwP : w'.1 ∈ P
      · simp only [hΦ, if_pos hwP]
        exact ((hIdem E B.a B.b w'.1 (V w'.1) (F (p, i.2)) (hVo _) (hVK _) (hF (p, i.2)).1).1).2
          (fixed_mono _ (hVU w'.1) hfix)
      · simp only [hΦ, if_neg hwP, hs]
        exact ((hIdem E B.a B.b w'.1 (U₁ w'.1) (F (p, i.2)) (hU₁.1 _).1 (hU₁.1 _).2 (hF (p, i.2)).1).1).2 hfix
    | inr w' =>
      show actT w'.1 (L.t w'.1) (F (p, i.2)) = F (p, i.2)
      rw [ht]
      exact ((hIdem E B.a B.b w'.1 (U₂ w'.1) (F (p, i.2)) (hU₂.1 _).1 (hU₂.1 _).2 (hF (p, i.2)).1).2).2
        (((hF (p, i.2)).2 w'.1 w'.2.1).2 w'.2.2)
  have hz : (convF B.ν (fm S P B e L0))^[m] Fp = 0 := by
    funext i
    obtain ⟨⟨⟩, k'⟩ := i
    have hk' : k' = e.symm (Function.update (e k') w₀ (e k' w₀)) := by simp
    rw [hk', hslice Fp hFgood m (e k') (e k' w₀)]
    have := congrFun (hcon p (e k')) (e k' w₀)
    simpa [hFp] using this
  rw [iter_restrict]
  show (convF B.ν (fm S P B e L))^[m] Fp ((), k) = 0
  obtain ⟨U, hU, hUF⟩ := uniform_lev Fp fun i => (hFgood i).1
  cases m with
  | zero => simpa using congrFun hz ((), k)
  | succ n =>

    have hok1 := pw_ok hA S P B e hS hP L1 hL1ok n
    have hok0 := pw_ok hA S P B e hS hP L0 hL0ok n
    have hWs : ∀ w, IsOpen (U₁ w : Set (GLw B.a w × GLw B.b w)) ∧ U₁ w ≤ K2 B.a B.b w := hU₁.1
    have hWt : ∀ w, IsOpen (U₂ w : Set (GLw B.a w × GLw B.b w)) ∧ U₂ w ≤ K2 B.a B.b w := hU₂.1
    have hent : ∀ x y, LM.ent P (pw L n) x y = LM.ent P ((pw L1 n).mul (pw L0 n)) x y := by
      intro x y
      funext w
      unfold LM.ent
      split_ifs with hwP
      · by_cases hw0 : w = w₀.1
        · subst hw0
          have e1 : (pw L1 n).m w₀.1 = dg V w₀.1 :=
            pw_dg L1 V w₀.1 (hVo _) (hVK _) (by funext x' y'; simp [hL1, rest1]) n
          have e0 : (pw L0 n).m w₀.1 = (pw L n).m w₀.1 :=
            pw_m_congr L0 L w₀.1 (by funext x' y'; simp [hL0, only0]) n
          rw [mul_m]
          rw [e1, e0, dg_mul_left V w₀.1 _ (fun z => (pw L n).m w₀.1 z (y ⟨w₀.1, hwP⟩))]
          refine (mconv_idem_left (hVo _) (hVK _) fun v hv g => ?_).symm
          exact pw_left L w₀.1 (V w₀.1) (fun x' y' v' hv' g' => (hbi w₀.1 hwP x' y' v' (hVU w₀.1 hv') g').1) n _ _ v hv g
        · have e1 : (pw L1 n).m w = (pw L n).m w :=
            pw_m_congr L1 L w (by funext x' y'; simp [hL1, rest1, hw0]) n
          have e0 : (pw L0 n).m w = dg V w :=
            pw_dg L0 V w (hVo _) (hVK _) (by funext x' y'; simp [hL0, only0, hw0]) n
          rw [mul_m]
          rw [e1, e0, dg_mul_right V w _ (fun z => (pw L n).m w (x ⟨w, hwP⟩) z)]
          refine (mconv_idem_right (hVo _) (hVK _) fun v hv g => ?_).symm
          exact pw_right L w (V w) (fun x' y' v' hv' g' => (hbi w hwP x' y' v' (hVU w hv') g').2) n _ _ v hv g
      · rw [mul_s]
        rw [stabilizerDilationWeights_dualIsotropicVector L U₁ hWs hs n, stabilizerDilationWeights_dualIsotropicVector L1 U₁ hWs (by rw [hL1s]; exact hs) n, stabilizerDilationWeights_dualIsotropicVector L0 U₁ hWs (by rw [hL0s]; exact hs) n]
        exact (mconv_idem_left (hWs w).1 (hWs w).2 fun v hv g => idem_left hv g).symm
    have htt : (pw L n).t = ((pw L1 n).mul (pw L0 n)).t := by
      funext w
      rw [product_torus_component]
      rw [power_torus_component_idempotent L U₂ hWt ht n, power_torus_component_idempotent L1 U₂ hWt (by rw [hL1t]; exact ht) n, power_torus_component_idempotent L0 U₂ hWt (by rw [hL0t]; exact ht) n]
      exact (mconv_idem_left (hWt w).1 (hWt w).2 fun v hv g => idem_left hv g).symm
    have hfm : fm S P B e (pw L n) = fm S P B e ((pw L1 n).mul (pw L0 n)) := by
      funext x y h
      simp only [fm, hent, htt]
    obtain ⟨hf1, -, hmul, -⟩ := hA E κ S P B e hS hP (pw L1 n) (pw L0 n) hok1 hok0
    have hf0 := (hA E κ S P B e hS hP (pw L0 n) (pw L1 n) hok0 hok1).1
    rw [iter_pw hA hC S P B e hS hP L hL Fp U hU hUF n, hfm, ← hmul, (hC E B Unit _ _ U Fp hf1 hf0 hU hUF).1,
      ← iter_pw hA hC S P B e hS hP L0 hL0ok Fp U hU hUF n, hz, convF_zero]
    rfl

end PositivityTheory.Rg.BcB.F.FA

end
