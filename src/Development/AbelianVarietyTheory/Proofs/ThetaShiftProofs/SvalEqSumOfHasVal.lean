module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SectionsEquivAnArcTheta
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HasSumLocallyUniformlyOnTerm
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.AnalyticTorusPointBaseEqHolUnifEx
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesCoeffNormBoundedRingLaws
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSumsAtHalfCurveFraction
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SecScalOfIsPullSec
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FramedPointEvalNaturalWeightScaling
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FormalThetaSumShiftPeriodDiv

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SvalEqSumOfHasVal
noncomputable section
namespace GlobalTheory.ArcPts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace SecValue

variable {K R : Type} [CommRing K] [CommRing R] {X Z : Scheme.{0}}

theorem res_constFn (p : X ⟶ Sp K) {U V : X.Opens} (h : V ≤ U) (a : K) :
    (X.presheaf.map (homOfLE h).op).hom (constFn p U a) = constFn p V a := by
  exact congrArg (fun q : Γ(Sp K, ⊤) ⟶ Γ(X, V) => q.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a))
    (p.appLE_map (U := ⊤) (V := U) le_top (homOfLE h).op)

theorem valR_constFn (p : X ⟶ Sp K) (f : K →+* R) (q : Sp R ⟶ X) (hq : q ≫ p = spMap f) (U : X.Opens)
    (h : ⊤ ≤ q ⁻¹ᵁ U) (a : K) : valR q U (constFn p U a) = f a := by
  refine (HolHom.valR_appLE q p ⊤ U le_top _ h).trans ?_
  rw [hq, ← Category.comp_id (spMap f),
    HolHom.valR_spMap f (𝟙 _) ⊤ le_rfl, HolHom.valR_eq _ _ le_rfl]
  congr 1
  exact congrArg (fun g : CommRingCat.of K ⟶ CommRingCat.of K => g.hom a)
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv_hom_id

def subComb (p : X ⟶ Sp K) {M : LB X} (s : M.Sec) {n : ℕ} (r : Fin n → K) (σ : Fin n → M.Sec) : M.Sec where
  f j := s.f j - ∑ i, constFn p _ (r i) * (σ i).f j
  compat j k := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sub, map_sum, map_sum, mul_sub, s.compat j k, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, res_constFn, res_constFn, (σ i).compat j k]
    ring

theorem valR_subComb (p : X ⟶ Sp K) {M : LB X} (s : M.Sec) {n : ℕ} (r : Fin n → K) (σ : Fin n → M.Sec)
    (f : K →+* R) (q : Sp R ⟶ X) (hq : q ≫ p = spMap f) (j : M.ι) (h : ⊤ ≤ q ⁻¹ᵁ M.U j) :
    valR q _ ((subComb p s r σ).f j) = valR q _ (s.f j) - ∑ i, f (r i) * valR q _ ((σ i).f j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← valR_constFn p f q hq _ h, HolHom.valR_eq _ _ h, subComb, map_sub, map_sum, map_mul]

theorem sval_subComb {L : LB Z} {π : X ⟶ Z} {m : ℕ} (p : X ⟶ Sp K) (s : SecP L π m) {n : ℕ} (r : Fin n → K)
    (σ : Fin n → SecP L π m) (f : K →+* R) (q : Sp R ⟶ X) (hq : q ≫ p = spMap f) (j : L.ι)
    (h : ⊤ ≤ (q ≫ π) ⁻¹ᵁ L.U j) :
    ArcPts.sval (subComb p s r σ : SecP L π m) q j = ArcPts.sval s q j - ∑ i, f (r i) * ArcPts.sval (σ i) q j := by
  have hw : ⊤ ≤ q ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => π) (fun _ => j) :=
    fun z hz => Set.mem_iInter.2 fun _ => h hz
  exact valR_subComb p s r σ f q hq (fun _ => j) hw

theorem sval_eq_zero {L : LB Z} {π : X ⟶ Z} {m : ℕ} (s : SecP L π m) (hs : ∀ i, s.f i = 0) (q : Sp R ⟶ X) (j : L.ι) :
    ArcPts.sval s q j = 0 := by
  refine (congrArg (valR q _) (hs fun _ => j)).trans ?_
  by_cases h : ⊤ ≤ q ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => π) (fun _ => j)
  · exact (HolHom.valR_eq q _ h 0).trans (map_zero _)
  · exact dif_neg h

end SecValue

theorem sval_eq_sum_of_hasVal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (S : Scheme.{0}) (A : AnArc (𝓞 E)) (t : SAB H S) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A t y) (j : ℕ) [NeZero j] (s : SecP t.PP.L (pullback.fst t.G.hom y) j) (n : ℕ) (r : Fin n → ℂ⸨X⸩) (α : Fin n → A.X) (th : Fin n → (Fin A.gB → ℂ) → ℂ), (∀ i, th i ∈ A.Theta j (α i)) → (∀ v, HasVal s (fib (Φ.x v)) (Φ.τ v) (∑ i, r i * A.FSum j (α i) (th i) v)) → ∀ (R : Type) [CommRing R] (f : ℂ⸨X⸩ →+* R) (q : Sp R ⟶ pullback t.G.hom y), q ≫ pullback.snd _ _ = spMap f → ∀ jj, ⊤ ≤ (q ≫ pullback.fst _ _) ⁻¹ᵁ t.PP.L.U jj → sval s q jj = ∑ i, f (r i) * sval (Φ.sig j (α i) (th i)) q jj := by
  intro E _ _ _ H _ S A t y Φ j _ s n r α th hth hs R _ f q hq jj hjj
  have h0 := Φ.sep j (SecValue.subComb (pullback.snd t.G.hom y) s r fun i => Φ.sig j (α i) (th i)) fun v k hk => by
    have hv : fib (Φ.x v) ≫ pullback.snd t.G.hom y = spMap (RingHom.id _) := by
      rw [fib, pullback.lift_snd]
      exact (Spec.map_id _).symm
    rw [SecValue.sval_subComb _ s r _ _ _ hv k hk, hs v k hk, Finset.sum_mul, zero_mul, sub_eq_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Φ.val j (α i) (th i) (hth i) v k hk, RingHom.id_apply, _root_.mul_assoc]
  have h1 := SecValue.sval_eq_zero _ h0 q jj
  rwa [SecValue.sval_subComb _ s r _ f q hq jj hjj, sub_eq_zero] at h1

end GlobalTheory.ArcPts
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MemThetaShiftZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

noncomputable section

namespace GlobalTheory.ArcThetaSpaces

open TwistedTheta

section

variable {P : Out.PolAV (Sp ℂ)} {g : ℕ} {u : HolUnif P.A P.L g} {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}

theorem eq_zero_of_val (u : HolUnif P.A P.L g) (U : P.A.left.Opens) (f : Γ(P.A.left, U))
    (h : ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ U → valAt' (u.ex z).left U f = 0) : f = 0 := by
  have := P.isAb.smooth
  have := isReduced_of_smooth_complex _ P.A.hom inferInstance
  refine ComplexPoints.eq_of_valAt'_eq P.A.hom _ _ _ fun x hx hi => ?_
  obtain ⟨z, hz⟩ := u.ex_onto (Over.homMk x hx)
  obtain rfl : (u.ex z).left = x := by rw [hz]; rfl
  rw [h z hi, valAt'_zero]

theorem finite_thetaShift (hT : Out.GlobalSectionsRankAlgClosed) {j : ℕ} (hj : 1 ≤ j)
    (h₁ : ∀ s, ∃ θ, u.IsFnPow j s θ) (h₂ : ∀ θ, u.IsThetaFn Hm χ j θ → ∃ s, u.IsFnPow j s θ) (c : Fin g → ℂ) :
    Module.Finite ℂ (TwistedTheta.thetaShift u Hm χ j c) := by
  obtain ⟨b, rfl⟩ : ∃ b : Fin g → ℂ, c = j • b := ⟨(j : ℂ)⁻¹ • c, by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ (Nat.cast_ne_zero.2 (by omega))]⟩
  obtain ⟨β, hβ⟩ := PowSec.exists_basis_sections hT ℂ P j hj
  choose φ hφ using h₁
  have hle : TwistedTheta.thetaShift u Hm χ j (j • b) ≤ Submodule.span ℂ (Set.range fun i z => φ (β i) (z + b)) := by
    intro θ hθ
    obtain ⟨s, hs⟩ := h₂ _ (isThetaFn_sub hθ)
    obtain ⟨a, ha, -⟩ := hβ s
    refine (Submodule.mem_span_range_iff_exists_fun ℂ).2 ⟨a, funext fun z => ?_⟩
    have hi := FrameValue.le_chartAt P.isLB (u.ex (z + b)).left
    set i := FrameValue.chartAt P.isLB (u.ex (z + b)).left
    have hi' : ⊤ ≤ (u.ex (z + b)).left ⁻¹ᵁ (lbPow P.L j).U (fun _ => i) := fun p hp => mem_powChart.2 (hi hp)
    have e := (valAt'_sum _ _ _ _).symm.trans
      ((congrArg (valAt' _ _) (ha fun _ => i)).symm.trans (hs (fun _ => i) (z + b) hi'))
    simp only [add_sub_cancel_right] at e
    refine mul_right_cancel₀ (pow_ne_zero j (u.fr_ne i _ hi)) (Eq.trans ?_ e)
    rw [Finset.sum_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    refine Eq.trans ?_ ((valAt'_mul _ _ _ _).trans (congrArg₂ (· * ·)
      (valAt'_constFn _ _ (Over.w (u.ex (z + b))) _ _ hi') (hφ _ _ _ hi'))).symm
    simp [_root_.mul_assoc]
  have := Module.Finite.span_of_finite ℂ (Set.finite_range fun i z => φ (β i) (z + b))
  exact Submodule.finiteDimensional_of_le hle

theorem mem_thetaShift_zero {j : ℕ} {θ : (Fin g → ℂ) → ℂ} (h : u.IsThetaFn Hm χ j θ) : θ ∈ TwistedTheta.thetaShift u Hm χ j 0 :=
  ⟨h.1, fun l z => by rw [h.2 l z, FrameValue.hermForm_zero_left]; simp⟩

theorem exists_ne_zero (hT : Out.GlobalSectionsRankAlgClosed) (h₁ : ∀ s, ∃ θ, u.IsThetaFn Hm χ 1 θ ∧ u.IsFnPow 1 s θ) :
    ∃ θ, u.IsThetaFn Hm χ 1 θ ∧ θ ≠ 0 := by
  obtain ⟨β, hβ⟩ := PowSec.exists_indep_sections hT P 1 le_rfl
  have i₀ : Fin (1 ^ P.g) := ⟨0, by simp⟩
  by_contra hne
  push_neg at hne
  have h0 : ∀ i j, (β i).f j = 0 := fun i j => eq_zero_of_val u _ _ fun z hz => by
    obtain ⟨θ, h, h'⟩ := h₁ (β i)
    rw [h' j z hz, hne θ h, Pi.zero_apply, zero_mul]
  exact one_ne_zero (congrFun (hβ 1 fun j => by simp [h0]) i₀)

theorem exists_isFn (h₁ : ∀ s, ∃ θ, u.IsThetaFn Hm χ 1 θ ∧ u.IsFnPow 1 s θ) (th : P.L.Sec) (h : ∃ j, th.f j ≠ 0) :
    ∃ θ, u.IsThetaFn Hm χ 1 θ ∧ θ ≠ 0 ∧ u.IsFn th θ := by
  obtain ⟨θ, h₂, h₃⟩ := h₁ (secToPow th 1)
  have hf : u.IsFn th θ := fun i z hi => by
    have hi' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow P.L 1).U (fun _ => i) := fun p hp => mem_powChart.2 (hi hp)
    have e := h₃ (fun _ => i) z hi'
    rw [pow_one] at e
    refine Eq.trans ?_ e
    exact ((valAt'_res _ _ (th.f i ^ 1) hi').trans (by rw [pow_one])).symm
  refine ⟨θ, h₂, ?_, hf⟩
  rintro rfl
  obtain ⟨j, hj⟩ := h
  exact hj (eq_zero_of_val u _ _ fun z hz => by rw [hf j z hz, Pi.zero_apply, zero_mul])

end

theorem sections_theta : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (Λ : GtAn a), (∀ (j : ℕ) (α : Λ.A.X), 1 ≤ j → (∀ s, Λ.fn j α s ∈ Λ.A.Theta j α) ∧ ∀ th ∈ Λ.A.Theta j α, ∃! s, Λ.fn j α s = th) ∧ AnFin Λ.A ∧ ∀ th : a.D₀.P.L.Sec, (∃ j, th.f j ≠ 0) → ∃ θ ∈ Λ.A.Theta 1 0, θ ≠ 0 ∧ Λ.u.IsFn th θ := by
  intro hL _ E _ _ _ H _ D l c O _ β _ _ b a Λ
  have hT := theta_eq_thetaShift Λ.A Λ.u (fun m => Λ.A.chi ⟨m.1, Λ.lam ▸ m.2⟩) Λ.lam
    (fun l l' e => congrArg Λ.A.chi (Subtype.ext e))
  have h0 : Λ.A.ct 0 = 0 := map_zero _
  have hθ : ∀ n θ, Λ.u.IsThetaFn Λ.A.Hm (fun m => Λ.A.chi ⟨m.1, Λ.lam ▸ m.2⟩) n θ → ∃ s, Λ.u.IsFnPow n s θ :=
    fun n θ h => ((Λ.pow n).2 θ h).exists
  refine ⟨fun j α hj => ?_, ⟨fun j α hj => ?_, ?_⟩, fun th h => ?_⟩
  · rw [hT]
    refine ⟨fun s => secFn_mem Λ.ah (Λ.ct α) s, fun th hth => ?_⟩
    obtain ⟨s, hs⟩ := exists_secFn_eq Λ.ah (by omega) (hθ j) (Λ.ct α) hth
    exact ⟨s, hs, fun t ht => secFn_injective (Λ.ct α) (ht.trans hs.symm)⟩
  · rw [hT]
    exact finite_thetaShift hL.globalSectionsRank hj (fun s => ((Λ.pow j).1 s).exists.imp fun _ h => h.2) (hθ j) _
  · rw [hT, h0]
    obtain ⟨θ, h₁, h₂⟩ := exists_ne_zero hL.globalSectionsRank fun s => ((Λ.pow 1).1 s).exists
    exact ⟨θ, mem_thetaShift_zero h₁, h₂⟩
  · rw [hT, h0]
    obtain ⟨θ, h₁, h₂⟩ := exists_isFn (fun s => ((Λ.pow 1).1 s).exists) th h
    exact ⟨θ, mem_thetaShift_zero h₁, h₂⟩

end GlobalTheory.ArcThetaSpaces
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFormalConvergence
noncomputable section

namespace GlobalTheory.ArcPts

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

section
variable {O : Type} [CommRing O] [StarRing O] {A : AnArc O} {T : ℝ} (hT : A.IsConvLine T) {j : ℕ} [NeZero j]
include hT

theorem fsum_mem_halfRing {α : A.X} {th : (Fin A.gB → ℂ) → ℂ} (h : th ∈ A.Theta j α) (v : A.V) :
    ∃ hm : A.FSum j α th v ∈ Conv.halfRing T, ∀ w hw, Conv.ev T w hw ⟨_, hm⟩ = A.Sum j α th w v :=
  ⟨fun _ hw => (AnArc.hasSum_coeff_FSum hT h hw v).summable,
    fun _ hw => Conv.ev_eq_of_hasSum hw _ (AnArc.hasSum_coeff_FSum hT h hw v)⟩

theorem exists_dfsum_halfRing {α : A.X} {th : (Fin A.gB → ℂ) → ℂ} (h : th ∈ A.Theta j α) (z₀ : A.V) :
    ∃ F : Conv.halfRing T, IsDFSum A j α th z₀ F ∧
      ∀ w hw, Conv.ev T w hw F = fderiv ℂ (A.Sum j α th w) 0 z₀ := by
  let S : ℂ⸨X⸩ := HahnSeries.ofSuppBddBelow (fun n => fderiv ℂ (fun v => (A.FSum j α th v).coeff n) 0 z₀)
    ⟨-A.be α α, fun n hn => by
      by_contra hlt
      exact hn (by simp only [AnArc.fderiv_coeff_FSum_eq_zero (not_le.1 hlt), zero_apply])⟩
  exact ⟨⟨S, fun _ hw => (AnArc.hasSum_fderiv_coeff_FSum hT h hw 0 z₀).summable⟩, fun _ => rfl,
    fun _ hw => Conv.ev_eq_of_hasSum hw _ (AnArc.hasSum_fderiv_coeff_FSum hT h hw 0 z₀)⟩

theorem differentiable_ev_comb (f : A.V → Conv.halfRing T) (hf : IsComb A j (Conv.halfRing T) (fun v => f v))
    (w : ℂ) (hw : T < w.im) : Differentiable ℂ (fun v => Conv.ev T w hw (f v)) := by
  obtain ⟨n, r, α, th, h1, h2⟩ := hf
  have key : (fun v => Conv.ev T w hw (f v)) =
      fun v => ∑ i, Conv.ev T w hw ⟨r i, (h1 i).1⟩ * A.Sum j (α i) (th i) w v := by
    funext v
    choose hm hv using fun i => fsum_mem_halfRing hT (h1 i).2 v
    have e : f v = ∑ i, (⟨r i, (h1 i).1⟩ : Conv.halfRing T) * ⟨_, hm i⟩ := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum]
      exact h2 v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hv i w hw]
  rw [key]
  exact Differentiable.fun_sum fun i _ =>
    (AnArc.differentiable_Sum hT (NeZero.ne j) (h1 i).2 hw).const_mul _

end

theorem exists_formal_convergence : ∀ (O : Type) [CommRing O] [StarRing O] (A : AnArc O), ∃ T₀ : ℝ, ∀ T ≥ T₀, ∀ (j : ℕ) [NeZero j], (∀ α, ∀ th ∈ A.Theta j α, (∀ v, ∃ h : A.FSum j α th v ∈ Conv.halfRing T, ∀ w hw, Conv.ev T w hw ⟨_, h⟩ = A.Sum j α th w v) ∧ ∀ z₀, ∃ F : Conv.halfRing T, IsDFSum A j α th z₀ F ∧ ∀ w hw, Conv.ev T w hw F = fderiv ℂ (A.Sum j α th w) 0 z₀) ∧ ∀ f : A.V → Conv.halfRing T, IsComb A j (Conv.halfRing T) (fun v => f v) → ∀ w hw, Differentiable ℂ (fun v => Conv.ev T w hw (f v)) := by
  intro O _ _ A
  obtain ⟨T₀, h₀⟩ := A.exists_isConvLine
  refine ⟨T₀, fun T hT j _ => ?_⟩
  have h := h₀.mono hT
  exact ⟨fun α th hth => ⟨fsum_mem_halfRing h hth, exists_dfsum_halfRing h hth⟩, differentiable_ev_comb h⟩

end GlobalTheory.ArcPts
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AnalyticDictionaryExpAdditiveSurjectiveLinear
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AnalyticDictionaryExpAdditiveSurjectiveLinear
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcPts

theorem ex0_additive_surjective_equivariant : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F)
    [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b)
    (Λ : GtAn a), (∀ z z', (Λ.ex0 z).IsAdd (Λ.ex0 z') (Λ.ex0 (z + z'))) ∧ Function.Surjective Λ.ex0 ∧
      ∀ (x : 𝓞 E) z, @GtAct ℂ _ _ (𝓞 E) _ H.starRing a.D₀ ℂ _ _ _ a.oa x (Λ.ex0 z) (Λ.ex0 (Λ.A.actV x z)) := by
  intro _ _ E _ _ _ H inst D l c O _ β _ _ b a Λ
  refine ⟨GtAnModel.isAdd Λ, GtAnModel.analyticTorusPoint_surjective Λ, ?_⟩
  obtain rfl : inst = H.starRing := Λ.star_eq
  exact GtAnModel.gtAct Λ

end GlobalTheory.ArcPts
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AnalyticDictionaryExpAdditiveSurjectiveLinearStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analyticDictionaryExp_additive_surjective_linear : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (Λ : GtAn a), (∀ z z', (Λ.ex0 z).IsAdd (Λ.ex0 z') (Λ.ex0 (z + z'))) ∧ Function.Surjective Λ.ex0 ∧ ∀ (x : 𝓞 E) z, @GtAct ℂ _ _ (𝓞 E) _ H.starRing a.D₀ ℂ _ _ _ a.oa x (Λ.ex0 z) (Λ.ex0 (Λ.A.actV x z)) := by
  first | exact @GlobalTheory.ArcPts.ex0_additive_surjective_equivariant | exact GlobalTheory.ArcPts.ex0_additive_surjective_equivariant | (intros; apply GlobalTheory.ArcPts.ex0_additive_surjective_equivariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcPointTangentPart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames GlobalTheory.Frames.ChgBC

noncomputable section

namespace GlobalTheory.ArcQ.TanPart

section Mul

variable {B B' Z Z' : Scheme.{0}} {G : Over B} [GrpObj G] {G' : Over B'} [GrpObj G'] {f : B' ⟶ B}
  {φ : G'.left ⟶ G.left}

end Mul

section Eps

variable {S : Type} [CommRing S]

theorem fst_alg : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S :=
  RingHom.ext fun x => by simp [TrivSqZeroExt.algebraMap_eq_inl]

end Eps

section Comb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {S : Type} [CommRing S]

end Comb

section Gt

open GlobalTheory.TorusModel

variable {A : Type} [CommRing A] [IsDomain A] {D₀ : Out.DegPre A}

theorem isZero_of_isAdd {T : Over (Spec (CommRingCat.of A))} {g : Out.GtPt D₀ T} (h : g.IsAdd g g) : g.IsZero := by
  obtain ⟨hb, hv⟩ := (GlobalTheory.TorusModel.isAdd_iff _ _ _).1 h
  have hb1 : g.b = 1 := by
    exact (mul_eq_left.1 hb.symm)
  refine ⟨hb1, fun χ => corr_of_val D₀.P.isLB fun y J hJ => ?_⟩
  have e := hv χ y J hJ
  have face (x x' : T ⟶ D₀.P.A) : cubV D₀.cub y J 1 x x' = 1 := by
    have q := val_corr hJ (D₀.cub.face 0) (lift x x').left
    rw [val_one] at q
    refine (Eq.trans ?_ (val_cub D₀.cub (lift x x') hJ (pzero D₀.P.A _) (x2 D₀.P.A 0) (x2 D₀.P.A 1)).symm).trans q
    congr 1 <;> simp [x2, pzero, Hom.one_def]
  have swap01 (x x' w : T ⟶ D₀.P.A) : cubV D₀.cub y J x x' w = cubV D₀.cub y J x' x w := by
    have q := (val_corr hJ D₀.cub.cubeSymmetric_swap_first (lift x (lift x' w)).left).trans (val_cub D₀.cub (lift x (lift x' w)) hJ _ _ _)
    refine q.trans ?_
    congr 1 <;> simp [x3]
  have swap12 (x x' w : T ⟶ D₀.P.A) : cubV D₀.cub y J x x' w = cubV D₀.cub y J x w x' := by
    have q := (val_corr hJ D₀.cub.cubeSymmetric_swap_last (lift x (lift x' w)).left).trans (val_cub D₀.cub (lift x (lift x' w)) hJ _ _ _)
    refine q.trans ?_
    congr 1 <;> simp [x3]
  have face3 (x x' : T ⟶ D₀.P.A) : cubV D₀.cub y J x x' 1 = 1 :=
    (swap12 _ _ _).trans ((swap01 _ _ _).trans (face _ _))
  rw [hb1] at e
  change cv g χ y J * cubV D₀.cub y J (DVR.cP D₀ T χ) 1 1 = _ at e
  rw [face3, _root_.mul_one] at e
  exact (mul_eq_left.1 e.symm).trans (val_one _).symm

end Gt

section ThetaShiftProofs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {K₁ : Type} [Field K₁] [Algebra c.F K₁] {b : O →+* K₁} {a : ArcIn Dw l β K₁ b} {χ : Sp (PowerSeries K₁) ⟶ Y.X}

end ThetaShiftProofs

end GlobalTheory.ArcQ.TanPart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RepTransport
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj

namespace GlobalTheory.FibreFrame

variable {K R R' : Type} [CommRing K] [CommRing R] [CommRing R'] {X Y Z : Scheme.{0}} {L : LB Z} {m : ℕ}

theorem le_wchart {π : X ⟶ Z} {q : Sp R ⟶ X} {j : L.ι} (h : ⊤ ≤ (q ≫ π) ⁻¹ᵁ L.U j) :
    ⊤ ≤ q ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => π) (fun _ => j) :=
  fun _ hz => Set.mem_iInter.2 fun _ => h hz

theorem sval_spMap {π : X ⟶ Z} (s : SecP L π m) (ρ : R →+* R') (q : Sp R ⟶ X) {j : L.ι}
    (h : ⊤ ≤ (q ≫ π) ⁻¹ᵁ L.U j) : ArcPts.sval s (spMap ρ ≫ q) j = ρ (ArcPts.sval s q j) :=
  HolHom.valR_spMap ρ q _ (le_wchart h) _

theorem exists_pull {π : X ⟶ Z} (s : SecP L π m) (h : Y ⟶ X) {π' : Y ⟶ Z} (e : h ≫ π = π') :
    ∃ s' : SecP L π' m, (∀ j (le : LB.wchart L (fun _ : Fin 1 => π') j ≤ h ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => π) j),
        s'.f j = (Y.presheaf.map (homOfLE le).op).hom ((h.app _).hom (s.f j))) ∧
      ∀ (R : Type) [CommRing R] (q : Sp R ⟶ Y) (j : L.ι), ⊤ ≤ (q ≫ π') ⁻¹ᵁ L.U j →
        ArcPts.sval s' q j = ArcPts.sval s (q ≫ h) j := by
  subst e
  refine ⟨DVR.pullSec L (fun _ : Fin 1 => π) (fun _ => (m : ℤ)) s h, fun _ _ => rfl, fun R _ q j hj => ?_⟩
  exact (HolHom.valR_res q _ _ (le_wchart hj)).trans (HolHom.valR_comp q h _ _).symm

theorem res_constFn (p : X ⟶ Sp K) {U V : X.Opens} (h : V ≤ U) (a : K) :
    (X.presheaf.map (homOfLE h).op).hom (constFn p U a) = constFn p V a :=
  congrArg (fun q : Γ(Sp K, ⊤) ⟶ Γ(X, V) => q.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a))
    (p.appLE_map (U := ⊤) (V := U) le_top (homOfLE h).op)

theorem valR_constFn (p : X ⟶ Sp K) (f : K →+* R) (q : Sp R ⟶ X) (hq : q ≫ p = spMap f) (U : X.Opens)
    (h : ⊤ ≤ q ⁻¹ᵁ U) (a : K) : valR q U (constFn p U a) = f a := by
  refine (HolHom.valR_appLE q p ⊤ U le_top _ h).trans ?_
  rw [hq, Conv.valR_spMap_top]

def comb (p : X ⟶ Sp K) {M : LB X} {n : ℕ} (r : Fin n → K) (σ : Fin n → M.Sec) : M.Sec where
  f j := ∑ i, constFn p _ (r i) * (σ i).f j
  compat j k := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, res_constFn, res_constFn, (σ i).compat j k]
    ring

theorem valR_comb (p : X ⟶ Sp K) {M : LB X} {n : ℕ} (r : Fin n → K) (σ : Fin n → M.Sec) (f : K →+* R)
    (q : Sp R ⟶ X) (hq : q ≫ p = spMap f) (j : M.ι) (h : ⊤ ≤ q ⁻¹ᵁ M.U j) :
    valR q _ ((comb p r σ).f j) = ∑ i, f (r i) * valR q _ ((σ i).f j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← valR_constFn p f q hq _ h, HolHom.valR_eq _ _ h, comb, map_sum, map_mul]

theorem sval_comb {π : X ⟶ Z} (p : X ⟶ Sp K) {n : ℕ} (r : Fin n → K) (σ : Fin n → SecP L π m) (f : K →+* R)
    (q : Sp R ⟶ X) (hq : q ≫ p = spMap f) {j : L.ι} (h : ⊤ ≤ (q ≫ π) ⁻¹ᵁ L.U j) :
    ArcPts.sval (comb p r σ : SecP L π m) q j = ∑ i, f (r i) * ArcPts.sval (σ i) q j := by
  exact valR_comb p r σ f q hq (fun _ => j) (le_wchart h)

theorem ext_sval {π : X ⟶ Z} {s s' : SecP L π m}
    (h : ∀ (R : Type) [CommRing R] (q : Sp R ⟶ X) (j : L.ι), ⊤ ≤ (q ≫ π) ⁻¹ᵁ L.U j →
      ArcPts.sval s q j = ArcPts.sval s' q j) (j : Fin 1 → L.ι) : s.f j = s'.f j := by
  obtain ⟨j, rfl⟩ : ∃ k, j = fun _ => k := ⟨j 0, funext fun i => congrArg j (Subsingleton.elim _ _)⟩
  refine TopCat.Presheaf.section_ext X.sheaf _ _ _ fun x hx => ?_
  obtain ⟨V, hV, hxV, hle⟩ := exists_isAffineOpen_mem_and_subset (X := X) hx
  obtain ⟨q, hq, hv⟩ := Conv.exists_point_of_ringHom hV (RingHom.id _)
  have hle' : V ≤ LB.wchart L (fun _ : Fin 1 => π) (fun _ => j) := hle
  have e := h _ q j fun z hz => LB.wchart_le L (fun _ : Fin 1 => π) (fun _ => j) 0 (hle' (hq hz))
  have e1 := (hv _).symm.trans (HolHom.valR_res q hle' (s.f fun _ => j) hq)
  have e2 := (hv _).symm.trans (HolHom.valR_res q hle' (s'.f fun _ => j) hq)
  exact X.presheaf.germ_ext V hxV (homOfLE hle') (homOfLE hle') (e1.trans (e.trans e2.symm))

def Rep {π : X ⟶ Z} (p : X ⟶ Sp K) {n : ℕ} (σ : Fin n → SecP L π m) (s : SecP L π m) (c : Fin n → K) : Prop :=
  ∀ (R : Type) [CommRing R] (f : K →+* R) (q : Sp R ⟶ X) (j : L.ι), q ≫ p = spMap f → ⊤ ≤ (q ≫ π) ⁻¹ᵁ L.U j →
    ArcPts.sval s q j = ∑ i, f (c i) * ArcPts.sval (σ i) q j

theorem rep_comb {π : X ⟶ Z} (p : X ⟶ Sp K) {n : ℕ} (σ : Fin n → SecP L π m) (c : Fin n → K) :
    Rep p σ (comb p c σ) c := fun _ _ f q _ hq h => sval_comb p c σ f q hq h

theorem rep_iff {π : X ⟶ Z} (p : X ⟶ Sp K) {n : ℕ} (σ : Fin n → SecP L π m) (s : SecP L π m) (c : Fin n → K) :
    Rep p σ s c ↔ ∀ j, s.f j = (comb p c σ).f j := by
  refine ⟨fun H => ext_sval fun R _ q j hj => ?_, fun H R _ f q j hq hj => ?_⟩
  · have hq : q ≫ p = spMap (Spec.preimage (q ≫ p)).hom := (Spec.map_preimage _).symm
    exact (H R _ q j hq hj).trans (sval_comb p c σ _ q hq hj).symm
  · exact (congrArg (valR q _) (H _)).trans (sval_comb p c σ f q hq hj)

theorem rep_transport {π : X ⟶ Z} {p : X ⟶ Sp K} {n : ℕ} {σ : Fin n → SecP L π m} (e : Y ≅ X) {π' : Y ⟶ Z}
    {p' : Y ⟶ Sp K} (hπ : e.hom ≫ π = π') (hp : e.hom ≫ p = p') {σ' : Fin n → SecP L π' m}
    (hσ : ∀ i (R : Type) [CommRing R] (q : Sp R ⟶ Y) (j : L.ι), ⊤ ≤ (q ≫ π') ⁻¹ᵁ L.U j →
      ArcPts.sval (σ' i) q j = ArcPts.sval (σ i) (q ≫ e.hom) j)
    (H : ∀ s, ∃! c, Rep p σ s c) (s' : SecP L π' m) : ∃! c, Rep p' σ' s' c := by
  subst hπ hp
  obtain ⟨s, -, hs⟩ := exists_pull s' e.inv (π' := π) (e.inv_hom_id_assoc π)
  have key : ∀ c, Rep (e.hom ≫ p) σ' s' c ↔ Rep p σ s c := fun c => by
    constructor
    · intro h R _ f q j hq hj
      have hj' : ⊤ ≤ ((q ≫ e.inv) ≫ e.hom ≫ π) ⁻¹ᵁ L.U j := by simpa using hj
      rw [hs R q j hj, h R f _ j (by simpa using hq) hj']
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hσ i R _ j hj', Category.assoc, e.inv_hom_id, Category.comp_id]
    · intro h R _ f q j hq hj
      have hj' : ⊤ ≤ ((q ≫ e.hom) ≫ π) ⁻¹ᵁ L.U j := by simpa using hj
      have := h R f (q ≫ e.hom) j (by simpa using hq) hj'
      rw [hs R _ j hj', Category.assoc, e.hom_inv_id, Category.comp_id] at this
      rw [this]
      exact Finset.sum_congr rfl fun i _ => by rw [hσ i R _ j hj]
  simp only [key]
  exact H s


open Out in
theorem exists_frame (hS : SecBaseChangeSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ)
    (hn : 1 ≤ n) (x : S) : ∃ V : S.Opens, x ∈ V ∧ ∃ (N : ℕ) (β : ∀ (R : Type) [CommRing R] (y : Sp R ⟶ S),
      ⊤ ≤ y ⁻¹ᵁ V → Fin N → SecP P.L (pullback.fst P.A.hom y) n),
      (∀ (R : Type) [CommRing R] (y : Sp R ⟶ S) (hy : ⊤ ≤ y ⁻¹ᵁ V) (R' : Type) [CommRing R'] (y' : Sp R' ⟶ S)
        (hy' : ⊤ ≤ y' ⁻¹ᵁ V) (C : Type) [CommRing C] (q : Sp C ⟶ pullback P.A.hom y) (q' : Sp C ⟶ pullback P.A.hom y')
        (i : Fin N) (j : P.L.ι), q ≫ pullback.fst _ _ = q' ≫ pullback.fst _ _ →
        ⊤ ≤ (q ≫ pullback.fst _ _) ⁻¹ᵁ P.L.U j → ArcPts.sval (β R y hy i) q j = ArcPts.sval (β R' y' hy' i) q' j) ∧
      ∀ (R : Type) [CommRing R] (y : Sp R ⟶ S) (hy : ⊤ ≤ y ⁻¹ᵁ V) (s : SecP P.L (pullback.fst P.A.hom y) n),
        ∃! c, Rep (pullback.snd P.A.hom y) (β R y hy) s c := by
  obtain ⟨V, hV, b, hb⟩ := hS S P n hn x
  let W := overRes (T := baseOver S) V
  have key : ∀ (R : Type) [CommRing R] (y : Sp R ⟶ S), ⊤ ≤ y ⁻¹ᵁ V →
      ∃ (k : pullback P.A.hom y ⟶ (W ⊗ P.A).left) (β : Fin (n ^ P.g) → SecP P.L (pullback.fst P.A.hom y) n),
        k ≫ (snd W P.A).left = pullback.fst _ _ ∧
        (∀ i (C : Type) [CommRing C] (q : Sp C ⟶ pullback P.A.hom y) (j : P.L.ι),
          ⊤ ≤ (q ≫ pullback.fst _ _) ⁻¹ᵁ P.L.U j →
          ArcPts.sval (β i) q j = ArcPts.sval (m := n) (p := (snd W P.A).left) (b i) (q ≫ k) j) ∧
        ∀ s, ∃! c, Rep (pullback.snd P.A.hom y) β s c := by
    intro R _ y hy
    let t : Sp R ⟶ W.left := IsOpenImmersion.lift V.ι y (by
      rintro _ ⟨z, rfl⟩
      exact V.range_ι.ge (hy (x := z) trivial))
    have ht : (baseAt t).hom = y := by
      show t ≫ V.ι ≫ 𝟙 _ = y
      rw [Category.comp_id]
      exact IsOpenImmersion.lift_fac _ _ _
    have hp : IsPullback (pullback.snd P.A.hom y) (pullback.fst P.A.hom y) (baseAt t).hom P.A.hom :=
      ht ▸ (IsPullback.of_hasPullback P.A.hom y).flip
    let e : pullback P.A.hom y ≅ (baseAt t ⊗ P.A).left := hp.isoPullback
    have e₁ : e.hom ≫ (snd (baseAt t) P.A).left = pullback.fst _ _ := hp.isoPullback_hom_snd
    have e₂ : e.hom ≫ (fst (baseAt t) P.A).left = pullback.snd _ _ := hp.isoPullback_hom_fst
    have e₃ : (homAt t ▷ P.A).left ≫ (snd W P.A).left = (snd (baseAt t) P.A).left :=
      congrArg CommaMorphism.left (whiskerRight_snd (homAt t) P.A)
    choose b' hb0 hb' using fun i => exists_pull (π := (snd W P.A).left) (m := n) (b i) (homAt t ▷ P.A).left e₃
    choose β _ hβ using fun i => exists_pull (b' i) e.hom e₁
    obtain ⟨hli, hsp⟩ := hb R t b' (fun i j => hb0 i j _)
    refine ⟨e.hom ≫ (homAt t ▷ P.A).left, β, (Category.assoc _ _ _).trans ((congrArg _ e₃).trans e₁), fun i C _ q j hj => ?_,
      rep_transport (p := (fst (baseAt t) P.A).left) e e₁ e₂ hβ fun s => ?_⟩
    · rw [hβ i C q j hj, hb' i C _ j (by rw [Category.assoc, e₁]; exact hj), Category.assoc]
    have bij := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv
    have key : ∀ c : Fin (n ^ P.g) → R, Rep (fst (baseAt t) P.A).left b' s c ↔
        ∑ i, (show Γ((baseAt t).left, ⊤) from (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (c i)) •
          (SecM.ofSec P.A (b' i) : SecM P.A P.L n (baseAt t)) = SecM.ofSec P.A s := fun c => by
      have ev : ∀ j, (∑ i, (show Γ((baseAt t).left, ⊤) from (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (c i)) •
          (SecM.ofSec P.A (b' i) : SecM P.A P.L n (baseAt t))).1 j =
          (comb (K := R) (fst (baseAt t) P.A).left c b').f j := fun j => by
        rw [Submodule.coe_sum, Finset.sum_apply]
        rfl
      rw [rep_iff]
      exact ⟨fun h => Subtype.ext (funext fun j => (ev j).trans (h j).symm),
        fun h j => (congrFun (congrArg Subtype.val h) j).symm.trans (ev j)⟩
    obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun _).1
      (hsp.ge (Submodule.mem_top : SecM.ofSec P.A s ∈ ⊤))
    choose a ha using fun i => bij.2 (r i)
    obtain rfl : (fun i => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (a i)) = r := funext ha
    refine ⟨a, (key a).2 hr, fun a' ha' => funext fun i => bij.1 ?_⟩
    exact Fintype.linearIndependent_iffₛ.1 hli _ _ (((key a').1 ha').trans hr.symm) i
  choose k β hk hβ hr using key
  refine ⟨V, hV, _, β, fun R _ y hy R' _ y' hy' C _ q q' i j hq hj => ?_, hr⟩
  have hm : Mono (snd W P.A).left := by
    have : Mono W.hom := inferInstanceAs (Mono (V.ι ≫ 𝟙 S))
    exact inferInstanceAs (Mono (pullback.snd W.hom P.A.hom))
  rw [hβ R y hy i C q j hj, hβ R' y' hy' i C q' j (hq ▸ hj)]
  congr 1
  rw [← cancel_mono (snd W P.A).left, Category.assoc, Category.assoc, hk, hk, hq]

end GlobalTheory.FibreFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFinSiteNormEqZpowSiteAlg
noncomputable section

namespace GlobalTheory.ArcQ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem exists_finSite_norm_eq_zpow_siteAlg :
    ∀ (K₁ : Type) [Field K₁] [NumberField K₁] (w : HeightOneSpectrum (𝓞 K₁)),
      (∃ (Tv : CDVR) (io : K₁ →+* Tv.Fr), Tv.FinRes ∧ OverLa w Tv.V io 1) ∧
      ∀ (Tv : CDVR) (io : K₁ →+* Tv.Fr), Tv.FinRes → OverLa w Tv.V io 1 →
        ∃ (Z : FinSite K₁ w) (ιT : Tv.Fr →+* Z.K), ιT.comp io = Z.ι ∧
          (∀ x : Tv.Fr, x ≠ 0 → ‖ιT x‖ = Z.r ^ vV Tv.V x) ∧ SiteAlg Z Tv ιT := by
  intro K₁ _ _ w
  obtain ⟨h1, h2⟩ := exists_finSite_siteAlg K₁ w
  refine ⟨h1, fun Tv io hfin ho => ?_⟩
  obtain ⟨Z, ιT, hc, hn, hs⟩ := h2 Tv io 1 hfin ho
  refine ⟨Z, ιT, hc, fun x hx => ?_, hs⟩
  have hf : ∀ v, ‖ιT (algebraMap Tv.V Tv.Fr v)‖ ≤ 1 := fun v => (hn _).2 ⟨v, rfl⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible Tv.V
  obtain ⟨y, hy⟩ := w.valuation_exists_uniformizer K₁
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy
    exact WithZero.exp_ne_zero hy.symm
  have hv : vLa w y = 1 := by
    rw [vLa, hy, WithZero.log_exp, neg_neg]
  have e1 : ‖Z.ι y‖ = Z.r := by
    have := Z.norm_ι y hy0
    rw [this]
    change Z.r ^ vLa w y = Z.r
    rw [hv, zpow_one]
  have e2 : ‖ιT (algebraMap Tv.V Tv.Fr π)‖ = Z.r := by
    rw [← e1, ← hc, RingHom.comp_apply,
      norm_map_eq_zpow_vV ιT hf hπ ((map_ne_zero io).2 hy0), ho.2 y, hv]
    simp
  rw [norm_map_eq_zpow_vV ιT hf hπ hx, e2]

end GlobalTheory.ArcQ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCoeffMemSubfield
noncomputable section

namespace GlobalTheory.ArcPts

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory Filter
open scoped LaurentSeries PowerSeries

theorem exists_coeff_mem_subfield {k L V ι : Type*} [Field k] [Field L] [Algebra k L] [Fintype ι]
    (K : IntermediateField k L) (r : ι → L) (g : ι → V → L) (f : V → L) (hg : ∀ i v, g i v ∈ K)
    (hf : ∀ v, f v ∈ K) (h : ∀ v, f v = ∑ i, r i * g i v) :
    ∃ s : ι → L, (∀ i, s i ∈ K) ∧ ∀ v, f v = ∑ i, s i * g i v := by
  obtain ⟨π, hπ⟩ := (Algebra.linearMap K L).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 (algebraMap K L).injective)
  refine ⟨fun i => π (r i), fun i => (π (r i)).2, fun v => ?_⟩
  have h1 : π (f v) = ⟨f v, hf v⟩ := LinearMap.congr_fun hπ ⟨f v, hf v⟩
  have h2 : π (f v) = ∑ i, π (r i) * ⟨g i v, hg i v⟩ := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h v, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : r i * g i v = (⟨g i v, hg i v⟩ : K) • r i := by
      rw [mul_comm]; rfl
    rw [this, map_smul, smul_eq_mul, mul_comm]
  have h3 := congrArg (fun x : K => (x : L)) (h1.symm.trans h2)
  simpa using h3

theorem exists_isComb_halfRing : ∀ (O : Type) [CommRing O] [StarRing O] (A : AnArc O), AnFin A →
    ∀ (j : ℕ) [NeZero j] (f : A.V → ℂ⸨X⸩), IsComb A j Set.univ f → (∀ v, f v ∈ Conv.convLaurent) →
    ∃ T : ℝ, IsComb A j (Conv.halfRing T) f ∧ ∀ v, f v ∈ Conv.halfRing T := by
  rintro O _ _ A - j _ f ⟨n, r, α, th, h1, h2⟩ hf
  obtain ⟨T₀, h₀⟩ := A.exists_isConvLine
  have hm : ∀ i v, A.FSum j (α i) (th i) v ∈ Conv.halfRing T₀ := fun i v _ hw =>
    (AnArc.hasSum_coeff_FSum h₀ (h1 i).2 hw v).summable
  obtain ⟨s, hs, hfs⟩ := exists_coeff_mem_subfield Conv.convLaurent r (fun i v => A.FSum j (α i) (th i) v) f
    (fun i v => Conv.halfRing_le_convLaurent T₀ (hm i v)) hf h2
  obtain ⟨T, hT, hT₀⟩ := ((eventually_all.2 fun i => Conv.eventually_mem_halfRing (hs i)).and
    (eventually_ge_atTop T₀)).exists
  refine ⟨T, ⟨n, s, α, th, fun i => ⟨hT i, (h1 i).2⟩, hfs⟩, fun v => ?_⟩
  rw [hfs v]
  exact Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (hT i) (Conv.halfRing_mono hT₀ (hm i v))

end GlobalTheory.ArcPts
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AnalyticDictionaryExpKernelIotaTorusPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AnalyticDictionaryExpKernelIotaTorusPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcPts.GtKer

theorem ker_iota_torus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (Λ : GtAn a), (∀ z, (Λ.ex0 z).IsZero ↔ ∃ la : Λ.A.La, la.y = 0 ∧ z = Λ.A.P0 la) ∧ (∀ la : Λ.A.La, Out.GtPtF.IsIota (Λ.ε la.y) (Λ.ex0 (Λ.A.P0 la))) ∧ (∀ lam : Λ.A.X →+ ℂ, IsTorusPt (Λ.ex0 (lam, 0)) (fun x => eTwoPi (lam (Λ.ε.symm x)))) ∧ ∀ z x, IsTorusPt (Λ.ex0 z) x → z.2 ∈ Λ.A.abelian₂ := by
  intro E _ _ _ H _ D l c O _ β _ _ b a Λ
  refine ⟨GtAnModel.isZero_iff Λ, GtAnModel.isIota Λ, fun lam => ⟨?_, fun x j hc hj => ?_⟩, fun z x h => ?_⟩
  · rw [GtAnModel.analyticTorusPoint_base_eq_holUnif_ex, GtAnModel.ex_zero]
  · obtain ⟨x, rfl⟩ := Λ.ε.surjective x
    have hz := GtAnModel.isLift_gt Λ (lam, 0) x
    have h := FrameValue.valAt'_gen a.D₀.P.isLB ((Λ.ex0 (lam, 0)).isGen _) hz (j := j) hj
    have h1 := Λ.arcDict_expZero_section (lam, 0) x
    have e : ∀ k k', ![Λ.A.ct x + (0 : Fin Λ.A.gB → ℂ), Λ.A.ct x, 0, 0] k = ![Λ.A.ct x + 0, Λ.A.ct x, 0, 0] k' →
        j k = j k' := fun k k' hk =>
      hc k k' (((Category.id_comp _).symm.trans (hz k)).trans
        ((congrArg (fun w => (Λ.u.ex w).left) hk).trans ((Category.id_comp _).symm.trans (hz k')).symm))
    have e₁ : j 0 = j 1 := e 0 1 (by simp)
    have e₂ : j 2 = j 3 := e 2 3 (by simp)
    have n₁ := Λ.u.fr_ne _ _ ((hz.le_iff j).1 hj 1)
    have n₃ := Λ.u.fr_ne _ _ ((hz.le_iff j).1 hj 3)
    have hf : FrameValue.frameProd Λ.u Out.DegPre.gtε ![Λ.A.ct x + (0 : Fin Λ.A.gB → ℂ), Λ.A.ct x, 0, 0] j = 1 := by
      simp only [Matrix.cons_val] at n₁ n₃
      simp only [FrameValue.frameProd, Fin.prod_univ_four, Out.DegPre.gtε, Matrix.cons_val, e₁, e₂, add_zero,
        zpow_neg, zpow_one]
      field_simp
    refine h.trans ((congrArg₂ (· * ·) h1 hf).trans ?_)
    simp
  · have h0 : Λ.u.ex z.2 = 1 := Over.OverMorphism.ext ((Λ.ex0_b z).symm.trans ((congrArg (·.left) h.1).trans
      ((toUnit_TF_comp_left _).trans (by rw [Hom.one_def, toUnit_unit, Category.id_comp]))))
    exact Λ.lam.le ((Λ.u.ker _).1 h0)

end GlobalTheory.ArcPts.GtKer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AnalyticDictionaryExpKernelIotaTorusPointsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analyticDictionaryExp_kernel_iota_torusPoints : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (Λ : GtAn a), (∀ z, (Λ.ex0 z).IsZero ↔ ∃ la : Λ.A.La, la.y = 0 ∧ z = Λ.A.P0 la) ∧ (∀ la : Λ.A.La, Out.GtPtF.IsIota (Λ.ε la.y) (Λ.ex0 (Λ.A.P0 la))) ∧ (∀ lam : Λ.A.X →+ ℂ, IsTorusPt (Λ.ex0 (lam, 0)) (fun x => eTwoPi (lam (Λ.ε.symm x)))) ∧ ∀ z x, IsTorusPt (Λ.ex0 z) x → z.2 ∈ Λ.A.abelian₂ := by
  first | exact @GlobalTheory.ArcPts.GtKer.ker_iota_torus | exact GlobalTheory.ArcPts.GtKer.ker_iota_torus | (intros; apply GlobalTheory.ArcPts.GtKer.ker_iota_torus <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusCoordinateRatioDifferentiableAtOrigin
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusCoordinateRatioDifferentiableAtOrigin
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries
open Filter Topology

namespace GlobalTheory.AbelianLetters

theorem exists_top_le_wchart {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Sp ℂ ⟶ X)) : ∃ j, ⊤ ≤ LB.wchart L φ j := by
  choose j hj using fun k => exists_chart hL (φ k (default : PrimeSpectrum ℂ))
  refine ⟨j, fun p _ => Set.mem_iInter.2 fun k => ?_⟩
  obtain rfl : p = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  exact hj k

theorem valAt'_unit_ne_zero {X : Scheme.{0}} (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)ˣ) :
    valAt' x U f.val ≠ 0 := by
  rw [HolHom.valAt'_eq_valR, HolHom.valR_eq _ _ h]
  exact (f.isUnit.map _).ne_zero

theorem IsRatio.differentiableAt_zero : ∀ [Algebra (FractionRing ℂ) ℂ] (D : Out.DegPre ℂ) (g n : ℕ) (ex : (Fin g → ℂ) → Out.GtPtF D ℂ) (s₀ : Out.GtPt D D.P.A), s₀.b = 𝟙 D.P.A ^ n → (∀ z z', (ex z).IsAdd (ex z') (ex (z + z'))) → IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ _ from (ex z).b.left)) → (∀ x j, DifferentiableOn ℂ (fun z => chiVal (ex z) x j) {z | ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφ D ℂ (ex z).b x) j}) → ∀ u : D.X → (Fin g → ℂ) → ℂ, IsRatio ex n s₀ u → ∀ x, DifferentiableAt ℂ (u x) 0 := by
  intro _ D g n ex s₀ hb hadd hol hchi u hu x
  obtain ⟨j, hj⟩ := exists_top_le_wchart D.P.isLB (Out.DegPre.gtφ D ℂ (ex ((n : ℂ) • 0)).b x)
  have h1 : ∀ z, ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφ D ℂ (ex z).b x) j ↔
      ⊤ ≤ (show Sp ℂ ⟶ _ from (ex z).b.left) ⁻¹ᵁ LB.wchart D.P.L (Out.DegPre.gtφT D D.P.A (𝟙 D.P.A ^ 1) x) j := by
    intro z
    have := top_le_wchart_nsmul hadd (n := 1) rfl z x j
    rwa [Nat.cast_one, one_smul] at this
  have hS : {z | ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφ D ℂ (ex z).b x) j} ∈ 𝓝 ((n : ℂ) • (0 : Fin g → ℂ)) := by
    filter_upwards [(HolHom.holAt_of_isHolTo hol (Set.mem_univ ((n : ℂ) • (0 : Fin g → ℂ))) _ ((h1 _).1 hj)).1]
      with t ht using (h1 t).2 ht
  have hn : DifferentiableAt ℂ (fun z : Fin g → ℂ => (n : ℂ) • z) 0 := by fun_prop
  have hc : DifferentiableAt ℂ (fun z => chiVal (ex ((n : ℂ) • z)) x j) 0 :=
    ((hchi x j).differentiableAt hS).comp 0 hn
  have h0 := (top_le_wchart_nsmul hadd hb 0 x j).1 hj
  obtain ⟨hev, hd⟩ := HolHom.holAt_of_isHolTo hol (Set.mem_univ 0) _ h0
  refine (hc.fun_mul ((hd ((s₀.s x).s j).val).fun_inv (valAt'_unit_ne_zero _ h0 _))).congr_of_eventuallyEq ?_
  filter_upwards [hev] with t ht
  exact (eq_mul_inv_iff_mul_eq₀ (valAt'_unit_ne_zero _ ht _)).2
    (hu x t j ((top_le_wchart_nsmul hadd hb t x j).2 ht)).symm

end GlobalTheory.AbelianLetters
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusCoordinateRatioDifferentiableAtOriginStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusCoordinateRatio_differentiableAt_origin : ∀ [Algebra (FractionRing ℂ) ℂ] (D : Out.DegPre ℂ) (g n : ℕ) (ex : (Fin g → ℂ) → Out.GtPtF D ℂ) (s₀ : Out.GtPt D D.P.A), s₀.b = 𝟙 D.P.A ^ n → (∀ z z', (ex z).IsAdd (ex z') (ex (z + z'))) → IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ _ from (ex z).b.left)) → (∀ x j, DifferentiableOn ℂ (fun z => chiVal (ex z) x j) {z | ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφ D ℂ (ex z).b x) j}) → ∀ u : D.X → (Fin g → ℂ) → ℂ, IsRatio ex n s₀ u → ∀ x, DifferentiableAt ℂ (u x) 0 := by
  first | exact @GlobalTheory.AbelianLetters.IsRatio.differentiableAt_zero | exact GlobalTheory.AbelianLetters.IsRatio.differentiableAt_zero | (intros; apply GlobalTheory.AbelianLetters.IsRatio.differentiableAt_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsBasisFSum
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory

theorem AnArc.FSum_sum_smul {O : Type} [CommRing O] [StarRing O] (A : AnArc O) (j : ℕ) [NeZero j] (α : A.X)
    {K : Type} (s : Finset K) (c : K → ℂ) (th : K → (Fin A.gB → ℂ) → ℂ) (v : A.V) :
    A.FSum j α (∑ i ∈ s, c i • th i) v = ∑ i ∈ s, HahnSeries.single 0 (c i) * A.FSum j α (th i) v := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := A.FSum_smul j α 0 0 v
    rw [zero_smul, zero_smul] at h
    simpa using h
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, A.FSum_add, ih, A.FSum_smul,
      HahnSeries.single_zero_mul_eq_smul]

theorem AnArc.exists_basis_FSum : ∀ (O : Type) [CommRing O] [StarRing O] (A : AnArc O), AnFin A → ∀ (j : ℕ) [NeZero j], ∃ (n : ℕ) (α : Fin n → A.X) (th : Fin n → (Fin A.gB → ℂ) → ℂ) (T₀ : ℝ), (∀ i, th i ∈ A.Theta j (α i)) ∧ LinearIndependent ℂ⸨X⸩ (fun i v => A.FSum j (α i) (th i) v) ∧ (∀ w : ℂ, T₀ < w.im → LinearIndependent ℂ (fun i v => A.Sum j (α i) (th i) w v)) ∧ ∀ α', ∀ th' ∈ A.Theta j α', ∃ r : Fin n → ℂ⸨X⸩, (∀ i T, r i ∈ Conv.halfRing T) ∧ ∀ v, A.FSum j α' th' v = ∑ i, r i * A.FSum j (α i) (th i) v := by
  intro O _ _ A hA j _
  classical
  have hj : 1 ≤ j := Nat.one_le_iff_ne_zero.2 (NeZero.ne j)
  obtain ⟨-, e, he⟩ := exists_representatives_mod_nsmul A.X j hj
  obtain ⟨T₀, hT⟩ := A.exists_isConvLine
  have : ∀ c, Module.Finite ℂ (A.Theta j (e c)) := fun c => hA.1 j (e c) hj
  let b := fun c => Module.finBasis ℂ (A.Theta j (e c))
  let I := fun c => Fin (Module.finrank ℂ (A.Theta j (e c)))
  let t : ∀ c, I c → (Fin A.gB → ℂ) → ℂ := fun c i => b c i
  have ht : ∀ c, LinearIndependent ℂ (t c) := fun c =>
    (b c).linearIndependent.map' (A.Theta j (e c)).subtype (Submodule.ker_subtype _)
  have htm : ∀ c i, t c i ∈ A.Theta j (e c) := fun c i => (b c i).2
  have hrep : ∀ c c' y, e c = e c' + j • y → c = c' := fun c c' y h =>
    (he (e c)).unique ⟨0, by simp⟩ ⟨y, h⟩
  let s := (Fintype.equivFin (Σ c, I c)).symm
  refine ⟨_, fun i => e (s i).1, fun i => t (s i).1 (s i).2, T₀, fun i => htm _ _,
    (A.linearIndependent_FSum_sigma hrep ht).comp s s.injective, fun w hw =>
    (A.linearIndependent_Sum_sigma (NeZero.ne j) hrep ht w fun c i z =>
      AnArc.summable_term hT (NeZero.ne j) (htm c i) hw (0, z)).comp s s.injective, fun α' th' hth' => ?_⟩
  obtain ⟨c, ⟨m, hm⟩, -⟩ := he α'
  have hα : α' + j • (-m) = e c := by rw [hm]; simp
  have hmem := A.translate_mem_Theta hth' (-m)
  rw [hα] at hmem
  let x := (b c).repr ⟨_, hmem⟩
  have hx : (fun z => th' (z + A.ct (-m))) = ∑ i, x i • t c i := by
    have := congrArg Subtype.val ((b c).sum_repr ⟨_, hmem⟩)
    rw [Submodule.coe_sum] at this
    exact this.symm
  let u : ℂ⸨X⸩ := HahnSeries.single (A.exponent j α' (-m)) ((A.psi (-m) : ℂ) ^ j * eTwoPi (A.T (-m) α'))
  obtain ⟨r, hr1, hr0⟩ : ∃ r : ∀ c', I c' → ℂ⸨X⸩, (∀ i, r c i = u * HahnSeries.single 0 (x i)) ∧
      ∀ c', c' ≠ c → ∀ i, r c' i = 0 :=
    ⟨Pi.single (M := fun c' => I c' → ℂ⸨X⸩) c fun i => u * HahnSeries.single 0 (x i),
      fun i => by rw [Pi.single_eq_same], fun c' h i => by rw [Pi.single_eq_of_ne h]; rfl⟩
  refine ⟨fun i => r (s i).1 (s i).2, fun i T => ?_, fun v => ?_⟩
  · beta_reduce
    generalize s i = p
    obtain ⟨c', i'⟩ := p
    by_cases h : c' = c
    · subst h
      rw [hr1]
      exact mul_mem (Conv.single_mem_halfRing _ _ _) (Conv.single_mem_halfRing _ _ _)
    · rw [hr0 c' h]
      exact zero_mem _
  · rw [s.sum_comp (fun p : Σ c, I c => r p.1 p.2 * A.FSum j (e p.1) (t p.1 p.2) v), Fintype.sum_sigma,
      Finset.sum_eq_single c (fun c' _ h => by simp [hr0 c' h]) (by simp),
      A.FSum_eq_translate j α' th' (-m) v, hα, hx, A.FSum_sum_smul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hr1, _root_.mul_assoc]

end GlobalTheory
end
