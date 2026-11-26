module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondEmbeddingEqStar
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.FrameStd

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.FirstEmbeddingAlgebraMap
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.DenomHolds
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LatBasisAllOfParts
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondEmbeddingAlgebraMap
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LatBasisAllOfBack
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets NumberField IsDedekindDomain Formalism.BasicNotions
  Formalism.L2.SG.HidaSetting
open scoped TensorProduct Matrix

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)

theorem dual_fwd (hθ : IsSplitEquiv X p θ) (z : Fin X.B.I.n → FpX X p) (hz : z ∈ Mlat2 X p θ) :
    ∀ y ∈ Mlat1 X p θ, z ⬝ᵥ (J1 X p θ *ᵥ y) ∈ OpX X p := by
  intro y hy
  induction hz using Submodule.span_induction with
  | mem z hz' =>
    obtain ⟨l', hl', rfl⟩ := hz'
    induction hy using Submodule.span_induction with
    | mem y hy' =>
      obtain ⟨l, hl, rfl⟩ := hy'
      exact dual_gen X p θ hθ l l' hl hl'
    | zero => simp
    | add a b _ _ ha hb =>
      rw [Matrix.mulVec_add]
      first
      | (rw [dotProduct_add]; exact add_mem ha hb)
      | (rw [Matrix.dotProduct_add]; exact add_mem ha hb)
    | smul c a _ ha =>
      show _ ⬝ᵥ (J1 X p θ *ᵥ ((c : FpX X p) • a)) ∈ OpX X p
      rw [Matrix.mulVec_smul]
      first
      | (rw [dotProduct_smul, smul_eq_mul]; exact mul_mem c.2 ha)
      | (rw [Matrix.dotProduct_smul, smul_eq_mul]; exact mul_mem c.2 ha)
  | zero => simp
  | add a b _ _ ha hb =>
    first
    | (rw [add_dotProduct]; exact add_mem ha hb)
    | (rw [Matrix.add_dotProduct]; exact add_mem ha hb)
  | smul c a _ ha =>
    show ((c : FpX X p) • a) ⬝ᵥ _ ∈ OpX X p
    first
    | (rw [smul_dotProduct, smul_eq_mul]; exact mul_mem c.2 ha)
    | (rw [Matrix.smul_dotProduct, smul_eq_mul]; exact mul_mem c.2 ha)

def DualBack : Prop :=
  ∀ z, (∀ y ∈ Mlat1 X p θ, z ⬝ᵥ (J1 X p θ *ᵥ y) ∈ OpX X p) → z ∈ Mlat2 X p θ

theorem latDual_of (hθ : IsSplitEquiv X p θ) (hB : DualBack X p θ) : LatDualP X p θ := by
  first
  | exact fun z => ⟨fun hz => dual_fwd X p θ hθ z hz, hB z⟩
  | exact ⟨fun z hz => dual_fwd X p θ hθ z hz, hB⟩
  | (unfold LatDualP; done)

theorem latBasisAll_of_back
    (hB : ∀ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ → DualBack X p θ) :
    LatBasisAll X p :=
  latBasisAll_of X p (fun θ hθ => latSplit_of X p θ (unitElt_holds X p θ hθ)) (fun θ _ => latFree_holds X p θ)
    (fun θ hθ => latDual_of X p θ hθ (hB θ hθ))

end Loc

end MassDataIdxSteps
end
end

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets NumberField IsDedekindDomain Formalism.BasicNotions
  Formalism.L2.SG.HidaSetting
open scoped TensorProduct Matrix

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)

def LocInt (x : Fin X.B.I.n → X.B.I.E) : Prop :=
  ∀ l ∈ X.B.I.L, iota1 X p θ (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J l x) ∈ OpX X p ∧
    iota2 X p θ (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J l x) ∈ OpX X p

def LocGlob : Prop :=
  ∀ x : Fin X.B.I.n → X.B.I.E, LocInt X p θ x → (fun j => iota2 X p θ (x j)) ∈ Mlat2 X p θ

def ApproxP : Prop :=
  ∀ z : Fin X.B.I.n → FpX X p, (∀ y ∈ Mlat1 X p θ, z ⬝ᵥ (J1 X p θ *ᵥ y) ∈ OpX X p) →
    ∃ x : Fin X.B.I.n → X.B.I.E, LocInt X p θ x ∧ z - (fun j => iota2 X p θ (x j)) ∈ Mlat2 X p θ

theorem dualBack_of (h1 : LocGlob X p θ) (h2 : ApproxP X p θ) : DualBack X p θ := by
  intro z hz
  obtain ⟨x, hx, hzx⟩ := h2 z hz
  have h := Submodule.add_mem _ hzx (h1 x hx)
  rwa [sub_add_cancel] at h

def DenomP : Prop :=
  ∀ e : X.B.I.E, iota1 X p θ e ∈ OpX X p → iota2 X p θ e ∈ OpX X p →
    ∃ s : 𝓞 X.B.I.F, s ∉ p.1.asIdeal ∧ ∃ c : 𝓞 X.B.I.E, (c : X.B.I.E) = algebraMap X.B.I.F X.B.I.E s * e

theorem secondEmbedding_algebraMap (f : X.B.I.F) : iota2 X p θ (algebraMap X.B.I.F X.B.I.E f) = algebraMap X.B.I.F (FpX X p) f := by
  have h1 : inclR (FpX X p) (algebraMap X.B.I.F X.B.I.E f) =
      algebraMap (FpX X p) (TpX X p) (algebraMap X.B.I.F (FpX X p) f) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : X.B.I.E →ₐ[X.B.I.F] TpX X p).commutes f
  have h2 := congrArg Prod.snd (th_incl (X := X) (p := p) (θ := θ) (algebraMap X.B.I.F X.B.I.E f))
  simp only at h2
  rw [← h2, h1, AlgEquiv.commutes]
  rfl

theorem unit_of_notMem (t : 𝓞 X.B.I.F) (ht : t ∉ p.1.asIdeal) :
    (algebraMap X.B.I.F (FpX X p) (t : X.B.I.F))⁻¹ ∈ OpX X p ∧ algebraMap X.B.I.F (FpX X p) (t : X.B.I.F) ≠ 0 := by
  have hle : p.1.intValuation t ≤ 1 := p.1.intValuation_le_one t
  have hnlt : ¬ p.1.intValuation t < 1 := fun h => ht ((p.1.intValuation_lt_one_iff_mem t).mp h)
  have hval : Valued.v (algebraMap X.B.I.F (FpX X p) (t : X.B.I.F)) = 1 := by
    have e1 : Valued.v (algebraMap X.B.I.F (FpX X p) (t : X.B.I.F)) = p.1.intValuation t := by
      first
      | exact (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := X.B.I.F) p.1
          (t : X.B.I.F)).trans
          (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := X.B.I.F) p.1 t)
      | exact (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := X.B.I.F) p.1 t).trans
          (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := X.B.I.F) p.1 t)
    rw [e1]
    exact le_antisymm hle (not_lt.mp hnlt)
  have hne : algebraMap X.B.I.F (FpX X p) (t : X.B.I.F) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hval
    exact zero_ne_one hval
  refine ⟨?_, hne⟩
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hval, inv_one]

theorem hform_smul_right (y x : Fin X.B.I.n → X.B.I.E) (c : X.B.I.E) :
    Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J y (c • x) = c * Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J y x := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Loc

end MassDataIdxSteps
end
end

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets NumberField IsDedekindDomain Formalism.BasicNotions
  Formalism.L2.SG.HidaSetting
open scoped TensorProduct Matrix

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)

def liftE (r : 𝓞 X.B.I.F) : 𝓞 X.B.I.E :=
  ⟨algebraMap X.B.I.F X.B.I.E (r : X.B.I.F),
    (RingOfIntegers.isIntegral_coe r).map (IsScalarTower.toAlgHom ℤ X.B.I.F X.B.I.E)⟩

theorem liftE_coe (r : 𝓞 X.B.I.F) : ((liftE X r : 𝓞 X.B.I.E) : X.B.I.E) = algebraMap X.B.I.F X.B.I.E (r : X.B.I.F) := rfl

def starE (a : 𝓞 X.B.I.E) : 𝓞 X.B.I.E :=
  ⟨star (a : X.B.I.E), (RingOfIntegers.isIntegral_coe a).map (starRingEnd X.B.I.E).toIntAlgHom⟩

theorem hform_zero_left (x : Fin X.B.I.n → X.B.I.E) :
    Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J 0 x = 0 := by
  simp [Formalism.UG.hform]

theorem hform_add_left (y y' x : Fin X.B.I.n → X.B.I.E) :
    Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (y + y') x =
      Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J y x + Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J y' x := by
  simp only [Formalism.UG.hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hform_smul_left (a : 𝓞 X.B.I.E) (y x : Fin X.B.I.n → X.B.I.E) :
    Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (a • y) x =
      star (a : X.B.I.E) * Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J y x := by
  simp only [Formalism.UG.hform, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  show star ((a • y) i) * X.B.I.J i j * x j = star (a : X.B.I.E) * (star (y i) * X.B.I.J i j * x j)
  rw [Pi.smul_apply, Algebra.smul_def]
  show star ((a : X.B.I.E) * y i) * _ * _ = _
  rw [star_mul']
  ring

theorem locGlob_of (hN : DenomP X p θ) : LocGlob X p θ := by
  classical
  intro x hx
  obtain ⟨S, hS⟩ := X.B.I.L_fg
  have hSL : ∀ g ∈ S, g ∈ X.B.I.L := fun g hg => hS ▸ Submodule.subset_span hg
  have hg : ∀ g ∈ S, ∃ s : 𝓞 X.B.I.F, s ∉ p.1.asIdeal ∧ ∃ c : 𝓞 X.B.I.E,
      (c : X.B.I.E) = algebraMap X.B.I.F X.B.I.E s * Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J g x :=
    fun g hgS => hN _ (hx g (hSL g hgS)).1 (hx g (hSL g hgS)).2
  choose! s hs c hc using hg
  set t : 𝓞 X.B.I.F := ∏ g ∈ S, s g with ht_def
  have ht : t ∉ p.1.asIdeal := by
    intro h
    have := p.1.isPrime
    obtain ⟨g, hgS, hg⟩ := Ideal.IsPrime.prod_mem_iff.1 h
    exact hs g hgS hg
  set T : X.B.I.E := algebraMap X.B.I.F X.B.I.E (t : X.B.I.F) with hT
  have hkey : ∀ g ∈ S, Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J g (T • x) ∈
      (algebraMap (𝓞 X.B.I.E) X.B.I.E).range := by
    intro g hgS
    rw [hform_smul_right]
    refine ⟨liftE X (∏ h ∈ S.erase g, s h) * c g, ?_⟩
    rw [map_mul]
    show ((liftE X (∏ h ∈ S.erase g, s h) : 𝓞 X.B.I.E) : X.B.I.E) * ((c g : 𝓞 X.B.I.E) : X.B.I.E) = _
    rw [hc g hgS, liftE_coe, hT, ht_def, ← Finset.mul_prod_erase S s hgS]
    have hm : ((s g * ∏ x ∈ S.erase g, s x : 𝓞 X.B.I.F) : X.B.I.F) =
        (s g : X.B.I.F) * ((∏ x ∈ S.erase g, s x : 𝓞 X.B.I.F) : X.B.I.F) := map_mul (algebraMap _ _) _ _
    rw [hm, map_mul]
    ring
  have hTx : T • x ∈ X.B.I.L := by
    refine (X.B.I.L_dual _).2 fun y hy => ?_
    rw [← hS] at hy
    induction hy using Submodule.span_induction with
    | mem g hg => exact hkey g hg
    | zero => rw [hform_zero_left]; exact ⟨0, map_zero _⟩
    | add y y' _ _ h1 h2 =>
        obtain ⟨c1, e1⟩ := h1
        obtain ⟨c2, e2⟩ := h2
        exact ⟨c1 + c2, by rw [map_add (f := _), e1, e2, hform_add_left]⟩
    | smul a y _ h1 =>
        obtain ⟨c1, e1⟩ := h1
        exact ⟨starE X a * c1, by rw [map_mul, e1, hform_smul_left]; rfl⟩
  obtain ⟨hinv, hne⟩ := unit_of_notMem X p t ht
  have hM : (fun j => iota2 X p θ ((T • x) j)) ∈ Mlat2 X p θ := Submodule.subset_span ⟨T • x, hTx, rfl⟩
  have heq : (fun j => iota2 X p θ (x j)) =
      (⟨(algebraMap X.B.I.F (FpX X p) (t : X.B.I.F))⁻¹, hinv⟩ : OpX X p) • (fun j => iota2 X p θ ((T • x) j)) := by
    funext j
    show iota2 X p θ (x j) = (algebraMap X.B.I.F (FpX X p) (t : X.B.I.F))⁻¹ * iota2 X p θ (T * x j)
    rw [map_mul, hT, secondEmbedding_algebraMap, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  rw [heq]
  exact Submodule.smul_mem _ _ hM

theorem latBasisAll_of_parts
    (hN : ∀ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ → DenomP X p θ)
    (hA : ∀ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ → ApproxP X p θ) :
    LatBasisAll X p := latBasisAll_of_back X p (fun θ hθ => dualBack_of X p θ (locGlob_of X p θ (hN θ hθ)) (hA θ hθ))

end Loc

end MassDataIdxSteps
end
end

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets NumberField IsDedekindDomain Formalism.BasicNotions
  Formalism.L2.SG.HidaSetting Polynomial
open scoped TensorProduct

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)

theorem fixed_ex (a : X.B.I.E) (ha : star a = a) : ∃ f : X.B.I.F, algebraMap X.B.I.F X.B.I.E f = a := by
  obtain ⟨f, hf⟩ := (X.B.I.cm.fixed a).1 ha
  exact ⟨f, hf⟩

theorem val_le (f : X.B.I.F) (hf : iota2 X p θ (algebraMap X.B.I.F X.B.I.E f) ∈ OpX X p) :
    p.1.valuation X.B.I.F f ≤ 1 := by
  rw [secondEmbedding_algebraMap, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at hf
  rwa [← IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

theorem denom_holds (hθ : IsSplitEquiv X p θ) : DenomP X p θ := by
  classical
  have key : ∀ f : X.B.I.F, p.1.valuation X.B.I.F f ≤ 1 →
      ∃ s : 𝓞 X.B.I.F, s ∉ p.1.asIdeal ∧ ∃ t : 𝓞 X.B.I.F, (t : X.B.I.F) = (s : X.B.I.F) * f := by
    intro f hf
    have hS := IsDedekindDomain.HeightOneSpectrum.Support.finite (𝓞 X.B.I.F) f
    have hex : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 X.B.I.F), ∃ n : ℕ, w.valuation X.B.I.F f ≤ WithZero.exp (n : ℤ) := by
      intro w
      by_cases h0 : w.valuation X.B.I.F f = 0
      · exact ⟨0, by rw [h0]; exact zero_le'⟩
      · refine ⟨(WithZero.log (w.valuation X.B.I.F f)).toNat, ?_⟩
        conv_lhs => rw [← WithZero.exp_log h0]
        exact WithZero.exp_le_exp.2 (Int.self_le_toNat _)
    choose N hN using hex
    obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := insert p.1 hS.toFinset)
      (fun w : IsDedekindDomain.HeightOneSpectrum (𝓞 X.B.I.F) => w.asIdeal)
      (fun w => if w = p.1 then 1 else N w) (fun w _ => w.prime)
      (fun w _ w' _ hne h => hne (IsDedekindDomain.HeightOneSpectrum.ext h))
      (fun w => if w.1 = p.1 then 1 else 0)
    have hyp : y ∉ p.1.asIdeal := by
      intro hmem
      have h1 := hy p.1 (Finset.mem_insert_self _ _)
      simp only [if_true, pow_one] at h1
      have h2 : (1 : 𝓞 X.B.I.F) ∈ p.1.asIdeal := by
        have h3 : y - (y - 1) ∈ p.1.asIdeal := p.1.asIdeal.sub_mem hmem h1
        simpa using h3
      exact p.1.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h2)
    have hval : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 X.B.I.F), w.valuation X.B.I.F ((y : X.B.I.F) * f) ≤ 1 := by
      intro w
      rw [Valuation.map_mul]
      by_cases hw : w ∈ hS.toFinset
      · have hwp : w ≠ p.1 := by
          intro h
          rw [Set.Finite.mem_toFinset, h] at hw
          exact absurd hf (not_le.2 hw)
        have h1 := hy w (Finset.mem_insert_of_mem hw)
        simp only [hwp, if_false, sub_zero] at h1
        have h2 : w.valuation X.B.I.F (y : X.B.I.F) ≤ WithZero.exp (-(N w : ℤ)) := by
          rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
          exact (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem w y (N w)).2 h1
        calc w.valuation X.B.I.F (y : X.B.I.F) * w.valuation X.B.I.F f
            ≤ WithZero.exp (-(N w : ℤ)) * WithZero.exp (N w : ℤ) := mul_le_mul' h2 (hN w)
          _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
      · have hfw : w.valuation X.B.I.F f ≤ 1 := by
          rw [Set.Finite.mem_toFinset] at hw
          exact not_lt.1 hw
        exact mul_le_one' (IsDedekindDomain.HeightOneSpectrum.valuation_le_one w y) hfw
    obtain ⟨t, ht⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one X.B.I.F ((y : X.B.I.F) * f) hval
    exact ⟨y, hyp, t, ht⟩
  intro e h1 h2
  obtain ⟨tf, htf⟩ := fixed_ex X (e + star e) (by rw [star_add, star_star, add_comm])
  obtain ⟨nf, hnf⟩ := fixed_ex X (e * star e) (by rw [star_mul, star_star])
  have hi : ∀ x : X.B.I.E, iota2 X p θ (star x) = iota1 X p θ x := fun x => by
    rw [secondEmbedding_eq_star X p θ hθ, star_star]
  have hvt : p.1.valuation X.B.I.F tf ≤ 1 :=
    val_le X p θ tf (by rw [htf, map_add (f := _), hi]; exact add_mem h2 h1)
  have hvn : p.1.valuation X.B.I.F nf ≤ 1 :=
    val_le X p θ nf (by rw [hnf, map_mul, hi]; exact mul_mem h2 h1)
  obtain ⟨s1, hs1, t1, ht1⟩ := key tf hvt
  obtain ⟨s2, hs2, t2, ht2⟩ := key nf hvn
  refine ⟨s1 * s2, fun h => (p.1.isPrime.mem_or_mem h).elim hs1 hs2, ?_⟩
  have f1 : algebraMap X.B.I.F X.B.I.E (t1 : X.B.I.F) = algebraMap X.B.I.F X.B.I.E (s1 : X.B.I.F) * (e + star e) := by
    rw [ht1, map_mul, htf]
  have f2 : algebraMap X.B.I.F X.B.I.E (t2 : X.B.I.F) = algebraMap X.B.I.F X.B.I.E (s2 : X.B.I.F) * (e * star e) := by
    rw [ht2, map_mul, hnf]
  have hrel : (algebraMap X.B.I.F X.B.I.E ((s1 * s2 : 𝓞 X.B.I.F) : X.B.I.F) * e) ^ 2 -
      ((liftE X (s2 * t1) : 𝓞 X.B.I.E) : X.B.I.E) * (algebraMap X.B.I.F X.B.I.E ((s1 * s2 : 𝓞 X.B.I.F) : X.B.I.F) * e) +
      ((liftE X (s1 * s1 * s2 * t2) : 𝓞 X.B.I.E) : X.B.I.E) = 0 := by
    rw [liftE_coe, liftE_coe]
    push_cast
    try simp only [map_mul]
    linear_combination (-(algebraMap X.B.I.F X.B.I.E (s1 : X.B.I.F) * algebraMap X.B.I.F X.B.I.E (s2 : X.B.I.F) ^ 2 * e)) * f1 +
      (algebraMap X.B.I.F X.B.I.E (s1 : X.B.I.F) ^ 2 * algebraMap X.B.I.F X.B.I.E (s2 : X.B.I.F)) * f2
  have hint : IsIntegral (𝓞 X.B.I.E) (algebraMap X.B.I.F X.B.I.E ((s1 * s2 : 𝓞 X.B.I.F) : X.B.I.F) * e) := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C (liftE X (s2 * t1)) * Polynomial.X +
      Polynomial.C (liftE X (s1 * s1 * s2 * t2)), by monicity!, ?_⟩
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow,
      Polynomial.eval₂_C, Polynomial.eval₂_X]
    exact hrel
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  exact ⟨c, hc⟩

end Loc

end MassDataIdxSteps
end
end

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets NumberField IsDedekindDomain Formalism.BasicNotions
  Formalism.L2.SG.HidaSetting
open scoped TensorProduct Matrix

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)

theorem hform_iota2 (hθ : IsSplitEquiv X p θ) (l l' : Fin X.B.I.n → X.B.I.E) :
    iota2 X p θ (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J l l') =
      (fun j => iota2 X p θ (l' j)) ⬝ᵥ (J1 X p θ *ᵥ fun j => iota1 X p θ (l j)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [secondEmbedding_eq_star X p θ hθ, Formalism.UG.hform, star_sum, star_mul', starRingEnd_apply, star_star,
    herm_entry, map_sum, map_mul, dotProduct, Matrix.mulVec, firstForm_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

theorem hform_iota1 (hθ : IsSplitEquiv X p θ) (l x : Fin X.B.I.n → X.B.I.E) :
    iota1 X p θ (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J l x) =
      (fun j => iota2 X p θ (l j)) ⬝ᵥ (J1 X p θ *ᵥ fun j => iota1 X p θ (x j)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.UG.hform, map_sum, map_mul, dotProduct, Matrix.mulVec, firstForm_apply, starRingEnd_apply,
    ← secondEmbedding_eq_star X p θ hθ, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

theorem firstEmbedding_algebraMap (f : X.B.I.F) : iota1 X p θ (algebraMap X.B.I.F X.B.I.E f) = algebraMap X.B.I.F (FpX X p) f := by
  show ((θ (Algebra.TensorProduct.includeRight (algebraMap X.B.I.F X.B.I.E f))).1) = _
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply X.B.I.F (FpX X p) (TpX X p), AlgEquiv.commutes]
  simp

def DenseF : Prop :=
  ∀ c ε : FpX X p, ε ≠ 0 → ∃ b : X.B.I.F, ∃ o ∈ OpX X p, algebraMap X.B.I.F (FpX X p) b - c = ε * o

def EpsLat : Prop :=
  ∃ ε : FpX X p, ε ≠ 0 ∧ ∀ u : Fin X.B.I.n → FpX X p, (∀ i, u i ∈ OpX X p) →
    ε • u ∈ Mlat1 X p θ ∧ ε • u ∈ Mlat2 X p θ

theorem approx_of (hθ : IsSplitEquiv X p θ) (hD : DenseF X p) (hE : EpsLat X p θ) : ApproxP X p θ := by
  intro z hz
  obtain ⟨ε, hε0, hε⟩ := hE
  obtain ⟨a, w, hw, hwa⟩ := unitElt_holds X p θ hθ
  set α1 := iota1 X p θ (a : X.B.I.E) with hα1
  set α2 := iota2 X p θ (a : X.B.I.E) with hα2
  have val : ∀ β : FpX X p, ∃ d : FpX X p, d ≠ 0 ∧ d ∈ OpX X p ∧ d * β ∈ OpX X p := by
    intro β
    by_cases hβ : β ∈ OpX X p
    · exact ⟨1, one_ne_zero, one_mem _, by simpa using hβ⟩
    · have hβ0 : β ≠ 0 := fun h => hβ (h ▸ zero_mem _)
      refine ⟨β⁻¹, inv_ne_zero hβ0, ?_, by rw [inv_mul_cancel₀ hβ0]; exact one_mem _⟩
      exact ((OpX X p).mem_or_inv_mem β).resolve_left hβ
  obtain ⟨d1, hd10, hd1, hd1α⟩ := val α1
  obtain ⟨d2, hd20, hd2, hd2α⟩ := val α2
  have hδ0 : d1 * d2 ≠ 0 := mul_ne_zero hd10 hd20
  have hδ1 : d1 * d2 * α1 ∈ OpX X p := by
    rw [mul_right_comm]
    exact mul_mem hd1α hd2
  have hδ2 : d1 * d2 * α2 ∈ OpX X p := by
    rw [mul_assoc]
    exact mul_mem hd1 hd2α
  have hεδ : ε * (d1 * d2) ≠ 0 := mul_ne_zero hε0 hδ0
  choose b o ho hb using fun j => hD (w * z j * α1) (ε * (d1 * d2)) hεδ
  choose b' o' ho' hb' using fun j => hD (-(w * z j)) (ε * (d1 * d2)) hεδ
  set x : Fin X.B.I.n → X.B.I.E := fun j =>
    algebraMap X.B.I.F X.B.I.E (b j) + algebraMap X.B.I.F X.B.I.E (b' j) * (a : X.B.I.E) with hx
  set u1 : Fin X.B.I.n → FpX X p := fun j => d1 * d2 * o j + o' j * (d1 * d2 * α1) with hu1
  set u2 : Fin X.B.I.n → FpX X p := fun j => d1 * d2 * o j + o' j * (d1 * d2 * α2) with hu2
  have hu1m : ∀ j, u1 j ∈ OpX X p := fun j =>
    add_mem (mul_mem (mul_mem hd1 hd2) (ho j)) (mul_mem (ho' j) hδ1)
  have hu2m : ∀ j, u2 j ∈ OpX X p := fun j =>
    add_mem (mul_mem (mul_mem hd1 hd2) (ho j)) (mul_mem (ho' j) hδ2)
  have e1 : (fun j => iota1 X p θ (x j)) = ε • u1 := by
    funext j
    simp only [hx, hu1, map_add (f := _), map_mul, firstEmbedding_algebraMap, Pi.smul_apply, smul_eq_mul]
    rw [← hα1]
    linear_combination hb j + α1 * hb' j
  have e2 : (fun j => iota2 X p θ (x j)) = z + ε • u2 := by
    funext j
    simp only [hx, hu2, map_add (f := _), map_mul, secondEmbedding_algebraMap, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    rw [← hα2]
    linear_combination hb j + α2 * hb' j + z j * hwa
  have M1mem : ε • u1 ∈ Mlat1 X p θ := (hε u1 hu1m).1
  have M2mem : ε • u2 ∈ Mlat2 X p θ := (hε u2 hu2m).2
  have mem1 : ∀ l ∈ X.B.I.L, (fun j => iota1 X p θ (l j)) ∈ Mlat1 X p θ := fun l hl =>
    Submodule.subset_span ⟨l, hl, rfl⟩
  have mem2 : ∀ l ∈ X.B.I.L, (fun j => iota2 X p θ (l j)) ∈ Mlat2 X p θ := fun l hl =>
    Submodule.subset_span ⟨l, hl, rfl⟩
  refine ⟨x, fun l hl => ⟨?_, ?_⟩, ?_⟩
  · rw [hform_iota1 X p θ hθ, e1]
    exact dual_fwd X p θ hθ _ (mem2 l hl) _ M1mem
  · rw [hform_iota2 X p θ hθ, e2, add_dotProduct]
    exact add_mem (hz _ (mem1 l hl)) (dual_fwd X p θ hθ _ M2mem _ (mem1 l hl))
  · rw [e2, sub_add_cancel_left]
    exact neg_mem M2mem

end Loc

end MassDataIdxSteps
end
end

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets NumberField IsDedekindDomain Formalism.BasicNotions
  Formalism.L2.SG.HidaSetting
open scoped TensorProduct Matrix

instance charZero_adicCompletion {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    CharZero (v.adicCompletion F) :=
  charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)

theorem denseF_holds : DenseF X p := by
  intro c ε hε
  have hO : IsOpen ((OpX X p : Set (FpX X p))) := Valued.isOpen_integer _
  have hU : IsOpen {k : FpX X p | (k - c) * ε⁻¹ ∈ OpX X p} :=
    hO.preimage ((continuous_id.sub continuous_const).mul continuous_const)
  obtain ⟨b, hb⟩ := (HeightOneSpectrum.denseRange_algebraMap (v := p.1) (K := X.B.I.F)).exists_mem_open hU
    ⟨c, by simp [zero_mem]⟩
  refine ⟨b, _, hb, ?_⟩
  field_simp

theorem cube_mem (ι : X.B.I.E →+* FpX X p) (Msub : Submodule (OpX X p) (Fin X.B.I.n → FpX X p)) (M : ℤ)
    (hgen : ∀ j : Fin X.B.I.n, (fun i => ι ((M • (Pi.single j (1 : X.B.I.E) : Fin X.B.I.n → X.B.I.E)) i)) ∈ Msub)
    (u : Fin X.B.I.n → FpX X p) (hu : ∀ i, u i ∈ OpX X p) : (M : FpX X p) • u ∈ Msub := by
  classical
  have heq : (M : FpX X p) • u =
      ∑ j, (⟨u j, hu j⟩ : OpX X p) • (fun i => ι ((M • (Pi.single j (1 : X.B.I.E) : Fin X.B.I.n → X.B.I.E)) i)) := by
    funext i
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, map_zsmul, Pi.single_apply]
    rw [Finset.sum_eq_single i]
    · simp only [if_true, map_one]
      show (M : FpX X p) * u i = u i * (M • (1 : FpX X p))
      rw [zsmul_eq_mul, mul_one, mul_comm]
    · intro j _ hji
      simp only [if_neg (Ne.symm hji), map_zero, smul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [heq]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hgen j)

theorem epsLat_holds : EpsLat X p θ := by
  classical
  have h : ∀ j : Fin X.B.I.n, ∃ N : ℤ, N ≠ 0 ∧ N • (Pi.single j (1 : X.B.I.E) : Fin X.B.I.n → X.B.I.E) ∈ X.B.I.L :=
    fun j => MassDataLevelSSteps.LatTop.exists_int_smul_mem X.B.I.L X.B.I.L_span _
  choose N hN0 hNL using h
  set M : ℤ := ∏ j, N j with hM
  have hM0 : M ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hN0 j
  have hML : ∀ j, M • (Pi.single j (1 : X.B.I.E) : Fin X.B.I.n → X.B.I.E) ∈ X.B.I.L := by
    intro j
    rw [hM, ← Finset.mul_prod_erase Finset.univ N (Finset.mem_univ j), mul_comm, mul_smul]
    exact zsmul_mem (hNL j) _
  refine ⟨(M : FpX X p), ?_, fun u hu => ⟨?_, ?_⟩⟩
  · exact Int.cast_ne_zero.2 hM0
  · exact cube_mem X p (iota1 X p θ) (Mlat1 X p θ) M
      (fun j => by unfold Mlat1; exact Submodule.subset_span ⟨_, hML j, rfl⟩) u hu
  · exact cube_mem X p (iota2 X p θ) (Mlat2 X p θ) M
      (fun j => by unfold Mlat2; exact Submodule.subset_span ⟨_, hML j, rfl⟩) u hu

theorem latBasisAll_holds' : LatBasisAll X p :=
  latBasisAll_of_parts X p (fun θ hθ => denom_holds X p θ hθ)
    (fun θ hθ => approx_of X p θ hθ (denseF_holds X p) (epsLat_holds X p θ))

end Loc

end MassDataIdxSteps
