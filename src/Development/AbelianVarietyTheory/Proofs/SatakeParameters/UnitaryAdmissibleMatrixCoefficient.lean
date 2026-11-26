module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LeviRep
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryAdmissibleMatrixCoefficient
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRepresent
namespace GlobalTheory.ExistsRepresentation

theorem exists_represent {V : Type} [AddCommGroup V] [Module ℂ V]
    (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hpos : ∀ v : V, v ≠ 0 → (0 : ℝ) < (Bf v v).re)
    (L : V →ₗ⋆[ℂ] ℂ) (W : Submodule ℂ V) [FiniteDimensional ℂ W] :
    ∃ u ∈ W, ∀ w ∈ W, L w = Bf u w := by
  classical
  let b := Module.finBasis ℂ W
  let Φ : W →ₗ[ℂ] (Fin (Module.finrank ℂ W) → ℂ) :=
    { toFun := fun u i => Bf (u : V) (b i : V)
      map_add' := by
        intro u u'
        funext i
        simp
      map_smul' := by
        intro c u
        funext i
        simp }
  have hinj : Function.Injective Φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro u hu
    have hall : ∀ w : W, Bf (u : V) (w : V) = 0 := by
      intro w
      rw [← b.sum_repr w]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smulₛₗ]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      have h0 := congrFun hu i
      simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h0
      simp [h0]
    by_contra hne
    have hne' : (u : V) ≠ 0 := by simpa using hne
    have h1 := hpos _ hne'
    rw [hall u] at h1
    simp at h1
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp hinj
  obtain ⟨u, hu⟩ := hsurj (fun i => L (b i : V))
  refine ⟨u, u.2, fun w hw => ?_⟩
  have hwsum : w = ∑ i, (b.repr ⟨w, hw⟩ i) • (b i : V) := by
    have h2 := congrArg Subtype.val (b.sum_repr ⟨w, hw⟩)
    rw [Submodule.coe_sum] at h2
    simp only [Submodule.coe_smul] at h2
    exact h2.symm
  rw [hwsum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smulₛₗ]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h3 := congrFun hu i
  simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk] at h3
  rw [h3]

end GlobalTheory.ExistsRepresentation
end

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GodementJacquet MeasureTheory
open scoped Pointwise

namespace GlobalTheory.SmoothRiesz

theorem exists_mem_eq_on_of_finiteDimensional {V : Type} [AddCommGroup V] [Module ℂ V]
    (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hpos : ∀ v, v ≠ 0 → 0 < (Bf v v).re)
    (L : V →ₗ⋆[ℂ] ℂ) (W : Submodule ℂ V) [FiniteDimensional ℂ W] :
    ∃ u ∈ W, ∀ w ∈ W, L w = Bf u w := by
  first
  | exact @_root_.GlobalTheory.ExistsRepresentation.exists_represent
  | exact _root_.GlobalTheory.ExistsRepresentation.exists_represent
  | (apply _root_.GlobalTheory.ExistsRepresentation.exists_represent <;> assumption)
  | (intros; apply _root_.GlobalTheory.ExistsRepresentation.exists_represent <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ExistsRepresentation.exists_represent <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ExistsRepresentation.exists_represent ..)

theorem finite_orbit {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ G V) (hsm : IsSmooth σ)
    (K : Subgroup G) (hKc : IsCompact (K : Set G)) (y : V) :
    ((fun k : G => σ k y) '' (K : Set G)).Finite := by
  let S : Set G := {g | σ g y = y}
  have hSo : IsOpen S := hsm y
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover (fun g : K => (g : G) • S) (fun g => hSo.smul _)
    (fun k hk => Set.mem_iUnion.2 ⟨⟨k, hk⟩, Set.mem_smul_set.2 ⟨1, by simp [S], by simp⟩⟩)
  refine ((t.finite_toSet.image (fun i : K => σ (i : G) y))).subset ?_
  rintro _ ⟨k, hk, rfl⟩
  obtain ⟨i, hi, hki⟩ := Set.mem_iUnion₂.1 (ht hk)
  obtain ⟨s, hs, rfl⟩ := Set.mem_smul_set.1 hki
  refine ⟨i, hi, ?_⟩
  have hs' : σ s y = y := hs
  simp only [smul_eq_mul, map_mul, Module.End.mul_apply, hs']

theorem exists_eq_of_invariant {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ G V) (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hadm : IsAdmissible σ) (hpos : ∀ v, v ≠ 0 → 0 < (Bf v v).re)
    (hinv : ∀ g v w, Bf (σ g v) (σ g w) = Bf v w) (L : V →ₗ⋆[ℂ] ℂ)
    (K : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (hL : ∀ s ∈ K, ∀ w, L (σ s w) = L w) : ∃ u : V, ∀ w, L w = Bf u w := by
  haveI : FiniteDimensional ℂ (fixed σ K) := hadm.2 K hKo hKc
  obtain ⟨u, huK, hu⟩ := exists_mem_eq_on_of_finiteDimensional Bf hpos L (fixed σ K)
  have hfix : ∀ k ∈ K, σ k u = u := fun k hk => by
    simpa using huK ⟨k, hk⟩
  refine ⟨u, fun w => ?_⟩
  have hcomp : ∀ (a b : G) (x : V), σ a (σ b x) = σ (a * b) x := fun a b x => by
    rw [map_mul, Module.End.mul_apply]
  let O : Finset V := (finite_orbit σ hadm.1 K hKc w).toFinset
  have hO : ∀ x, x ∈ O ↔ ∃ k ∈ K, σ k w = x := fun x => by simp [O]
  have hwO : w ∈ O := (hO w).2 ⟨1, K.one_mem, by simp⟩
  have hcard : ((O.card : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨w, hwO⟩)
  have heK : (∑ x ∈ O, x) ∈ fixed σ K := by
    intro k
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sum]
    refine Finset.sum_nbij' (fun x => σ k x) (fun x => σ (k : G)⁻¹ x) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      obtain ⟨c, hc, rfl⟩ := (hO x).1 hx
      exact (hO _).2 ⟨k * c, K.mul_mem k.2 hc, (hcomp _ _ _).symm⟩
    · intro x hx
      obtain ⟨c, hc, rfl⟩ := (hO x).1 hx
      exact (hO _).2 ⟨(k : G)⁻¹ * c, K.mul_mem (K.inv_mem k.2) hc, (hcomp _ _ _).symm⟩
    · intro x _
      rw [hcomp]; simp
    · intro x _
      rw [hcomp]; simp
    · intro x _
      rfl
  have hLO : ∀ x ∈ O, L x = L w := fun x hx => by
    obtain ⟨c, hc, rfl⟩ := (hO x).1 hx
    exact hL c hc w
  have hBO : ∀ x ∈ O, Bf u x = Bf u w := fun x hx => by
    obtain ⟨c, hc, rfl⟩ := (hO x).1 hx
    conv_lhs => rw [← hfix c hc]
    exact hinv c u w
  have key := hu _ heK
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.sum_congr rfl hLO, Finset.sum_congr rfl hBO, Finset.sum_const,
    Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul] at key
  exact mul_left_cancel₀ hcard key

end GlobalTheory.SmoothRiesz

namespace GlobalTheory

theorem exists_vector_of_smooth_antilinear : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin r) k) V)
    (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), IsAdmissible σ → (∀ v w, Bf w v = starRingEnd ℂ (Bf v w)) →
    (∀ v, v ≠ 0 → 0 < (Bf v v).re) → (∀ g v w, Bf (σ g v) (σ g w) = Bf v w) →
    ∀ (L : V →ₗ⋆[ℂ] ℂ) (S : Subgroup (GL (Fin r) k)), IsOpen (S : Set (GL (Fin r) k)) →
      (∀ s ∈ S, ∀ w, L (σ s w) = L w) → ∃ u : V, ∀ w, L w = Bf u w := by
  intro k _ _ _ _ r V _ _ σ Bf hadm _ hpos hinv L S hSo hL
  have hKo : IsOpen ((S ⊓ KO k (Fin r) : Subgroup _) : Set (GL (Fin r) k)) :=
    hSo.inter SplitFlip.isOpen_KO
  have hKc : IsCompact ((S ⊓ KO k (Fin r) : Subgroup _) : Set (GL (Fin r) k)) :=
    SplitFlip.isCompact_KO.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hKo) inf_le_right
  exact SmoothRiesz.exists_eq_of_invariant σ Bf hadm hpos hinv L _ hKo hKc
    fun s hs => hL s hs.1

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParameterTensorOneDimInjective
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParameterTensorOneDimInjective
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne TensorProduct

namespace GlobalTheory.WeilDeligne.TwistInj

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem apply_eq_det_smul (f : Module.End ℂ (Fin 1 → ℂ)) (v : Fin 1 → ℂ) :
    f v = LinearMap.det f • v := by
  have hd : LinearMap.det f = f (Pi.single 0 1) 0 := by
    conv_lhs => rw [← Matrix.toLin'_toMatrix' f]
    rw [LinearMap.det_toLin', Matrix.det_fin_one, LinearMap.toMatrix'_apply]
  have hv : v = v 0 • (Pi.single 0 1 : Fin 1 → ℂ) := by
    funext i; fin_cases i; simp
  funext i; fin_cases i
  rw [hv, map_smul, hd]
  simp [mul_comm]

def chr (c : WDRep h (Fin 1 → ℂ)) : Weil h →* ℂˣ :=
  (Units.map (LinearMap.det : Module.End ℂ (Fin 1 → ℂ) →* ℂ)).comp c.ρ.asGroupHom

theorem coe_chr (c : WDRep h (Fin 1 → ℂ)) (σ : Weil h) :
    (chr c σ : ℂ) = LinearMap.det (c.ρ σ) := by
  simp [chr, Representation.asGroupHom_apply]

theorem isSmooth_chr (c : WDRep h (Fin 1 → ℂ)) : IsSmooth (chr c) :=
  c.smooth.of_le fun σ hσ => Units.ext (by rw [coe_chr, hσ, map_one]; rfl)

theorem N_eq_zero (c : WDRep h (Fin 1 → ℂ)) : c.N = 0 := by
  have hz : LinearMap.det (0 : Module.End ℂ (Fin 1 → ℂ)) = 0 := by
    have := congrFun (apply_eq_det_smul 0 (fun _ => 1)) 0
    simpa using this.symm
  obtain ⟨k, hk⟩ := c.nilpotent
  have h0 : LinearMap.det c.N = 0 := by
    have : LinearMap.det c.N ^ k = 0 := by rw [← map_pow, hk, hz]
    exact pow_eq_zero_iff'.mp this |>.1
  refine LinearMap.ext fun v => ?_
  rw [apply_eq_det_smul, h0, zero_smul]
  rfl

theorem tensor_iso_twist {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (a : WDRep h V) (c : WDRep h (Fin 1 → ℂ)) :
    (a.tensor c).Iso (a.twist (chr c) (isSmooth_chr c)) := by
  refine ⟨(TensorProduct.congr (LinearEquiv.refl ℂ V) (LinearEquiv.funUnique (Fin 1) ℂ ℂ)).trans
    (TensorProduct.rid ℂ V), fun σ v => ?_, fun v => ?_⟩
  · induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      simp only [WDRep.tensor_ρ, TensorProduct.map_tmul, LinearEquiv.trans_apply,
        TensorProduct.congr_tmul, LinearEquiv.refl_apply, LinearEquiv.funUnique_apply,
        TensorProduct.rid_tmul, WDRep.twist_ρ, LinearMap.smul_apply, map_smul, coe_chr]
      rw [apply_eq_det_smul (c.ρ σ) y, smul_smul]
      simp [Function.eval, mul_comm]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      simp [N_eq_zero c, Function.eval, WDRep.twist]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem iso_of_twist {V V' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
    {a : WDRep h V} {b : WDRep h V'} (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ)
    (hab : (a.twist χ hχ).Iso (b.twist χ hχ)) : a.Iso b := by
  obtain ⟨e, h1, h2⟩ := hab
  refine ⟨e, fun σ v => ?_, h2⟩
  have := h1 σ v
  simp only [WDRep.twist_ρ, LinearMap.smul_apply, map_smul] at this
  exact smul_right_injective V' (Units.ne_zero (χ σ)) this

end GlobalTheory.WeilDeligne.TwistInj


open GlobalTheory.WeilDeligne.TwistInj in
theorem GlobalTheory.WeilDeligne.lpChar_left_injective_of_lpDim_one : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a b c : WD h), c.lpDim = 1 → a.lpChar c = b.lpChar c → a = b := by
  intro E Ω _ _ _ _ _ A w h a b c hc hab
  induction a using WD.ind with
  | hP n a =>
  induction b using WD.ind with
  | hP m b =>
  induction c using WD.ind with
  | hP k c =>
  rw [WD.lpDim_mk, Module.finrank_fin_fun] at hc
  subst hc
  rw [WD.lpChar_mk, WD.lpChar_mk, WD.mk_eq_mk] at hab
  exact WD.sound (TwistInj.iso_of_twist (TwistInj.chr c) (TwistInj.isSmooth_chr c)
    (((TwistInj.tensor_iso_twist a c).symm.trans hab).trans (TwistInj.tensor_iso_twist b c)))
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParameterTensorOneDimInjectiveStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDeligneParameter_tensor_oneDim_injective : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a b c : WD h), c.lpDim = 1 → a.lpChar c = b.lpChar c → a = b := by
  first | exact @GlobalTheory.WeilDeligne.lpChar_left_injective_of_lpDim_one | exact GlobalTheory.WeilDeligne.lpChar_left_injective_of_lpDim_one | (intros; apply GlobalTheory.WeilDeligne.lpChar_left_injective_of_lpDim_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LpCharCompatibilities
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LpCharCompatibilities
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial TensorProduct Module

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {V V' V'' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
  [AddCommGroup V''] [Module ℂ V''] [FiniteDimensional ℂ V'']

namespace WDRep

theorem iso_sum_tensor (a : WDRep h V) (b : WDRep h V') (c : WDRep h V'') :
    ((a.sum b).tensor c).Iso ((a.tensor c).sum (b.tensor c)) := by
  refine ⟨TensorProduct.prodLeft ℂ ℂ V V' V'', fun σ v => ?_, fun v => ?_⟩
  · induction v using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y =>
      obtain ⟨x₁, x₂⟩ := x
      simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · induction v using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y =>
      obtain ⟨x₁, x₂⟩ := x
      simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem iso_tw_tensor (a : WDRep h V) (c : WDRep h V') (s : ℝ) :
    ((a.tw s).tensor c).Iso ((a.tensor c).tw s) :=
  ⟨.refl _ _, fun σ v => by simp [TensorProduct.map_smul_left], fun _ => rfl⟩

theorem iso_tensor_tw (a : WDRep h V) (c : WDRep h V') (s : ℝ) :
    (a.tensor (c.tw s)).Iso ((a.tensor c).tw s) :=
  ⟨.refl _ _, fun σ v => by simp [TensorProduct.map_smul_right], fun _ => rfl⟩

theorem iso_tensor_assoc (a : WDRep h V) (b : WDRep h V') (c : WDRep h V'') :
    ((a.tensor b).tensor c).Iso (a.tensor (b.tensor c)) := by
  refine ⟨TensorProduct.assoc ℂ V V' V'', fun σ v => ?_, fun v => ?_⟩
  · induction v using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul x z =>
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => simp
      | add x y hx hy => simp only [map_add (f := _), add_tmul, hx, hy]
  · induction v using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul x z =>
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => simp [tmul_add, add_tmul, add_assoc]
      | add x y hx hy => simp only [map_add (f := _), add_tmul, hx, hy]

theorem iso_zero_tensor (a : WDRep h V) (c : WDRep h V') [Subsingleton V] (b : WDRep h V'') [Subsingleton V''] :
    (a.tensor c).Iso b := by
  haveI : Subsingleton (V ⊗[ℂ] V') := by
    refine ⟨fun x y => ?_⟩
    have key : ∀ z : V ⊗[ℂ] V', z = 0 := fun z => by
      induction z using TensorProduct.induction_on with
      | zero => rfl
      | tmul x y => rw [Subsingleton.elim x 0, zero_tmul]
      | add x y hx hy => rw [hx, hy, add_zero]
    rw [key x, key y]
  exact ⟨0, fun _ _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩

theorem ρ_eq_one_of_line (c : WDRep h V') (hu : c.Unr) (hd : finrank ℂ V' = 1)
    (hroot : (c.ρ (frob h)).charpoly.IsRoot 1) (σ : Weil h) : c.ρ σ = 1 := by
  obtain ⟨v, hv⟩ := ((Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr hroot).exists_hasEigenvector
  have hv1 : c.ρ (frob h) v = v := by simpa using hv.apply_eq_smul
  have hspan := (finrank_eq_one_iff_of_nonzero' v hv.2).mp hd
  have hF : c.ρ (frob h) = 1 := LinearMap.ext fun u => by
    obtain ⟨t, rfl⟩ := hspan u
    simp [hv1]
  obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (deg_frob (h := h)) σ
  have hz : ∀ n : ℤ, c.ρ (frob h ^ n) = 1 := fun n => by
    have h1 : c.ρ.toHomUnits (frob h) = 1 := Units.ext hF
    have h2 : c.ρ.toHomUnits (frob h ^ n) = 1 := by rw [map_zpow, h1, one_zpow]
    exact congrArg Units.val h2
  rw [hτ, map_mul, hz, hu.2 τ, one_mul]

theorem iso_tensor_line (a : WDRep h V) (c : WDRep h V') (hN : c.N = 0) (hd : finrank ℂ V' = 1)
    (hρ : ∀ σ, c.ρ σ = 1) : (a.tensor c).Iso a := by
  let f : V' ≃ₗ[ℂ] ℂ := LinearEquiv.ofFinrankEq V' ℂ (by simpa using hd)
  refine ⟨(TensorProduct.congr (.refl ℂ V) f).trans (TensorProduct.rid ℂ V), fun σ v => ?_, fun v => ?_⟩
  · induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [hρ]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [hN]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]

end WDRep

namespace WD

theorem lpChar_laws (a b c : WD h) (s : ℝ) :
    (a.lpSum b).lpChar c = (a.lpChar c).lpSum (b.lpChar c) ∧
    (a.lpTw s).lpChar c = (a.lpChar c).lpTw s ∧
    a.lpChar (c.lpTw s) = (a.lpChar c).lpTw s ∧
    (a.lpChar b).lpChar c = a.lpChar (b.lpChar c) ∧
    (WD.lpZero (h := h)).lpChar c = WD.lpZero (h := h) ∧
    (c.unr → c.lpDim = 1 → c.frobEig = {1} → a.lpChar c = a) := by
  induction a using ind with
  | hP n a =>
  induction b using ind with
  | hP m b =>
  induction c using ind with
  | hP k c =>
  refine ⟨?_, ?_, ?_, ?_, ?_, fun hu hd he => ?_⟩
  · simp only [lpSum_mk, lpChar_mk]
    exact sound (a.iso_sum_tensor b c)
  · simp only [lpTw_mk, lpChar_mk]
    exact sound (a.iso_tw_tensor c s)
  · simp only [lpTw_mk, lpChar_mk]
    exact sound (a.iso_tensor_tw c s)
  · simp only [lpChar_mk]
    exact sound (a.iso_tensor_assoc b c)
  · simp only [lpZero, lpChar_mk]
    exact sound (WDRep.iso_zero_tensor _ c _)
  · rw [unr_mk] at hu
    rw [lpDim_mk] at hd
    rw [frobEig_mk] at he
    have hroot : (c.ρ (frob h)).charpoly.IsRoot 1 := by
      have h1 : (1 : ℂ) ∈ (c.ρ (frob h)).charpoly.roots := by rw [he]; simp
      exact (Polynomial.mem_roots'.mp h1).2
    rw [lpChar_mk]
    exact sound (a.iso_tensor_line c hu.1 hd (c.ρ_eq_one_of_line hu hd hroot))

end WD

theorem lpChar_laws_closed : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E))
    (h : IsPlaceOver A w) (a b c : WD h) (s : ℝ),
    (a.lpSum b).lpChar c = (a.lpChar c).lpSum (b.lpChar c) ∧
    (a.lpTw s).lpChar c = (a.lpChar c).lpTw s ∧
    a.lpChar (c.lpTw s) = (a.lpChar c).lpTw s ∧
    (a.lpChar b).lpChar c = a.lpChar (b.lpChar c) ∧
    (WD.lpZero (h := h)).lpChar c = WD.lpZero (h := h) ∧
    (c.unr → c.lpDim = 1 → c.frobEig = {1} → a.lpChar c = a) :=
  fun _ _ _ _ _ _ _ _ _ _ a b c s => WD.lpChar_laws a b c s

end GlobalTheory.WeilDeligne
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LpCharCompatibilitiesStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lp_char_compatibilities : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a b c : WD h) (s : ℝ), (a.lpSum b).lpChar c = (a.lpChar c).lpSum (b.lpChar c) ∧ (a.lpTw s).lpChar c = (a.lpChar c).lpTw s ∧ a.lpChar (c.lpTw s) = (a.lpChar c).lpTw s ∧ (a.lpChar b).lpChar c = a.lpChar (b.lpChar c) ∧ (WD.lpZero (h := h)).lpChar c = WD.lpZero (h := h) ∧ (c.unr → c.lpDim = 1 → c.frobEig = {1} → a.lpChar c = a) := by
  exact @GlobalTheory.WeilDeligne.lpChar_laws_closed
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedOfLpDimLeOneOfUnitEigenvalues
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedOfLpDimLeOneOfUnitEigenvalues
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne

theorem absSpace_eq_bot_of_norm_charpoly_roots {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {f : Module.End ℂ V} (hf : ∀ α ∈ f.charpoly.roots, ‖α‖ = 1) {r : ℝ} (hr : r ≠ 1) :
    absSpace f r = ⊥ := by
  refine eq_bot_iff.mpr (iSup₂_le fun α hα => ?_)
  by_contra hne
  have hev : f.HasEigenvalue α := Module.End.hasEigenvalue_iff.mpr fun h => hne (h ▸ le_refl _)
  have hroot : (minpoly ℂ f).IsRoot α := Module.End.hasEigenvalue_iff_isRoot.mp hev
  have hc : α ∈ f.charpoly.roots := by
    rw [mem_roots (LinearMap.charpoly_monic f).ne_zero, ← Polynomial.dvd_iff_isRoot]
    exact (Polynomial.dvd_iff_isRoot.mpr hroot).trans (LinearMap.minpoly_dvd_charpoly f)
  exact hr (hα ▸ hf α hc)

theorem absSpace_one_eq_top_of_norm_charpoly_roots {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {f : Module.End ℂ V} (hs : f.IsSemisimple) (hf : ∀ α ∈ f.charpoly.roots, ‖α‖ = 1) :
    absSpace f 1 = ⊤ := by
  rw [eq_top_iff, ← hs.iSup_eigenspace_eq_top]
  refine iSup_le fun α => ?_
  by_cases hα : ‖α‖ = 1
  · exact le_iSup₂_of_le (f := fun (β : ℂ) (_ : ‖β‖ = 1) => f.eigenspace β) α hα le_rfl
  · have := absSpace_eq_bot_of_norm_charpoly_roots hf hα
    rw [eq_bot_iff] at this
    refine le_trans ?_ (bot_le : (⊥ : Submodule ℂ V) ≤ absSpace f 1)
    exact le_trans (le_iSup₂_of_le (f := fun (β : ℂ) (_ : ‖β‖ = ‖α‖) => f.eigenspace β) α rfl le_rfl) this

end GlobalTheory.WeilDeligne

theorem GlobalTheory.WeilDeligne.WD.tempered_of_lpDim_le_one_of_norm_eig : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : WD h), a.lpDim ≤ 1 → (∀ φ : Weil h, deg φ = 1 → ∀ α ∈ a.eig φ, ‖α‖ = 1) → a.tempered := by
  intro E Ω _ _ _ _ _ A w h a _ heig
  induction a using WD.ind with
  | hP n a =>
  rw [WD.tempered_mk]
  intro φ hφ
  have hroots : ∀ α ∈ (a.ρ φ).charpoly.roots, ‖α‖ = 1 := by
    intro α hα; exact heig φ hφ α (by rw [WD.eig_mk]; exact hα)
  have hq : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast one_lt_normV w
  have hne : ∀ s : ℝ, s ≠ 0 → ((normV w : ℕ) : ℝ) ^ s ≠ 1 := by
    intro s hs h1
    rw [← Real.rpow_zero ((normV w : ℕ) : ℝ), Real.rpow_right_inj (zero_lt_one.trans hq) hq.ne'] at h1
    exact hs h1
  refine ⟨eq_top_iff.mpr ?_, fun i => ?_⟩
  · rw [← absSpace_one_eq_top_of_norm_charpoly_roots (a.semisimple φ) hroots]
    refine le_iSup_of_le (0 : ℤ) ?_
    simp
  · rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp only [pow_zero, Nat.cast_zero, neg_zero]
      exact Set.bijOn_id _
    · have hi' : (0 : ℝ) < i := by exact_mod_cast hi
      rw [absSpace_eq_bot_of_norm_charpoly_roots hroots (hne _ (by linarith)),
        absSpace_eq_bot_of_norm_charpoly_roots hroots (hne _ (by linarith))]
      simp only [Submodule.bot_coe]
      exact ⟨fun v hv => by rw [Set.mem_singleton_iff.mp hv, map_zero]; rfl,
        fun v hv v' hv' _ => by rw [Set.mem_singleton_iff.mp hv, Set.mem_singleton_iff.mp hv'],
        fun v hv => ⟨0, rfl, by rw [Set.mem_singleton_iff.mp hv, map_zero]⟩⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedOfLpDimLeOneOfUnitEigenvaluesStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tempered_of_lpDim_le_one_of_unit_eigenvalues : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : WD h), a.lpDim ≤ 1 → (∀ φ : Weil h, deg φ = 1 → ∀ α ∈ a.eig φ, ‖α‖ = 1) → a.tempered := by
  first | exact @GlobalTheory.WeilDeligne.WD.tempered_of_lpDim_le_one_of_norm_eig | exact GlobalTheory.WeilDeligne.WD.tempered_of_lpDim_le_one_of_norm_eig | (intros; apply GlobalTheory.WeilDeligne.WD.tempered_of_lpDim_le_one_of_norm_eig <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAlgClosedResidueFieldOfAic
noncomputable section

namespace GlobalTheory.GenusTwoPureComparison.Cmp

open CategoryTheory Limits AlgebraicGeometry Polynomial GlobalTheory.EtC

theorem monic_eq_prod_of_aic {T : Type} [CommRing T] (hT : AIC T) :
    ∀ (n : ℕ) (f : T[X]), f.Monic → f.natDegree = n → ∃ s : Multiset T, f = (s.map fun a => X - C a).prod := by
  intro n
  induction n with
  | zero =>
    intro f hf hn
    exact ⟨0, by simpa using Polynomial.eq_one_of_monic_natDegree_zero hf hn⟩
  | succ n ih =>
    intro f hf hn
    rcases subsingleton_or_nontrivial T with hT0 | hT0
    · have h0 : f = 0 := Subsingleton.elim _ _
      rw [h0, natDegree_zero] at hn; omega
    obtain ⟨a, ha⟩ := hT f hf (by omega)
    have hmul : (X - C a) * (f /ₘ (X - C a)) = f := mul_divByMonic_eq_iff_isRoot.2 ha
    have hq : (f /ₘ (X - C a)).Monic := (monic_X_sub_C a).of_mul_monic_left (by rw [hmul]; exact hf)
    have hd : (f /ₘ (X - C a)).natDegree = n := by
      rw [natDegree_divByMonic _ (monic_X_sub_C a), natDegree_X_sub_C]; omega
    obtain ⟨s, hs⟩ := ih _ hq hd
    refine ⟨a ::ₘ s, ?_⟩
    rw [Multiset.map_cons, Multiset.prod_cons, ← hs, hmul]

theorem henselianLocalRing_of_aic {T : Type} [CommRing T] [IsLocalRing T] (hT : AIC T) : HenselianLocalRing T where
  is_henselian f hf a₀ h₁ _ := by
    classical
    obtain ⟨s, hs⟩ := monic_eq_prod_of_aic hT _ f hf rfl
    have hev : f.eval a₀ = (s.map fun a => a₀ - a).prod := by
      conv_lhs => rw [hs]
      rw [Polynomial.eval_multiset_prod, Multiset.map_map]
      exact congrArg _ (Multiset.map_congr rfl fun a _ => by simp)
    rw [hev] at h₁
    obtain ⟨c, hc, hcm⟩ := ((IsLocalRing.maximalIdeal.isMaximal T).isPrime.multiset_prod_mem_iff_exists_mem _).1 h₁
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hc
    refine ⟨a, ?_, ?_⟩
    · show f.eval a = 0
      rw [hs, Polynomial.eval_multiset_prod, Multiset.map_map]
      exact Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨a, ha, by simp⟩)
    · rw [← neg_sub]; exact (Ideal.neg_mem_iff _).2 hcm

theorem isAlgClosed_residueField_of_aic {T : Type} [CommRing T] [IsLocalRing T] (hT : AIC T) :
    IsAlgClosed (IsLocalRing.ResidueField T) := by
  refine IsAlgClosed.of_exists_root _ fun p hp hirr => ?_
  obtain ⟨q, hqp, hqd, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.lifts_iff_coeff_lifts p |>.2 fun n => IsLocalRing.residue_surjective (p.coeff n)) hp
  have hdeg : 0 < q.natDegree := by
    rw [hqd]; exact Polynomial.natDegree_pos_iff_degree_pos.2 (Polynomial.degree_pos_of_irreducible hirr)
  obtain ⟨a, ha⟩ := hT q hqm hdeg
  refine ⟨IsLocalRing.residue T a, ?_⟩
  rw [← hqp, Polynomial.eval_map, Polynomial.eval₂_at_apply, ha, map_zero]

theorem sh_of_aic {T : Type} [CommRing T] [IsLocalRing T] (hT : AIC T) : SH T := by
  haveI := isAlgClosed_residueField_of_aic hT
  exact ⟨henselianLocalRing_of_aic hT, inferInstance⟩

end GlobalTheory.GenusTwoPureComparison.Cmp

namespace GlobalTheory.GenusTwoPureComparison.Cmp

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

section Fibres
variable {T : Type} [CommRing T] [IsDomain T] [IsLocalRing T] {X : Scheme.{0}}

abbrev spFib (p : X ⟶ Spec (CommRingCat.of T)) : Scheme.{0} :=
  pullback p (Spec.map (CommRingCat.ofHom (IsLocalRing.residue T)))

abbrev spInc (p : X ⟶ Spec (CommRingCat.of T)) : spFib p ⟶ X := pullback.fst _ _

abbrev genFib (p : X ⟶ Spec (CommRingCat.of T)) : Scheme.{0} :=
  pullback p (Spec.map (CommRingCat.ofHom (algebraMap T (FractionRing T))))

abbrev genInc (p : X ⟶ Spec (CommRingCat.of T)) : genFib p ⟶ X := pullback.fst _ _

end Fibres

end GlobalTheory.GenusTwoPureComparison.Cmp

namespace GlobalTheory.GenusTwoPureComparison.Cmp

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

section Torsion
variable {T : Type} [CommRing T] [IsDomain T] [IsLocalRing T]

theorem eqv_spInc (hE2 : E2) (hT : AIC T) (q : ℕ) (hq : IsUnit (q : T)) {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of T)) [IsProper p] (i : ℤ) : Eqv (ZMod q) (sch.map (spInc p)) (tw q i) :=
  hE2 q T (sh_of_aic hT) hq p i

theorem eqv_genInc (hE3 : E3) (hT : AIC T) (q : ℕ) [NeZero q] (hq : IsUnit (q : T)) {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of T)) [Smooth p] (i : ℤ) : Eqv (ZMod q) (sch.map (genInc p)) (tw q i) :=
  hE3 q T hT hq p i

end Torsion

end GlobalTheory.GenusTwoPureComparison.Cmp

namespace GlobalTheory.GenusTwoPureComparison.Cmp

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

section Adic
variable (l : ℕ) [Fact l.Prime]

theorem pullHl_bijective {E E' : Spc} (f : E ⟶ E') (n i : ℤ)
    (hf : ∀ k : ℕ, Function.Bijective (pull (ZMod (l ^ k)) f (tw (l ^ k) i) n)) :
    Function.Bijective (pullHl l f n i) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    funext k
    exact (hf k).1 (congrArg (fun z => z.1 k) hxy)
  · intro y
    choose x hx using fun k => (hf k).2 (y.1 k)
    refine ⟨⟨x, fun k => (hf k).1 ?_⟩, Subtype.ext (funext hx)⟩
    change pull _ f _ n (red (l ^ (k + 1)) (l ^ k) E' n i (x (k + 1))) = pull _ f _ n (x k)
    rw [pull_red, hx, hx]
    exact y.2 k

theorem pullHQ_bijective {E E' : Spc} (f : E ⟶ E') (n i : ℤ)
    (hf : ∀ k : ℕ, Function.Bijective (pull (ZMod (l ^ k)) f (tw (l ^ k) i) n)) :
    Function.Bijective (pullHQ l f n i) := by
  let e := LinearEquiv.ofBijective (pullHl l f n i) (pullHl_bijective l f n i hf)
  have h : pullHQ l f n i = (e.baseChange ℤ_[l] ℚ_[l] _ _).toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a m
    rfl
  rw [h]
  exact (e.baseChange ℤ_[l] ℚ_[l] _ _).bijective

end Adic

end GlobalTheory.GenusTwoPureComparison.Cmp

namespace GlobalTheory.GenusTwoPureComparison.Cmp

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

section Main
variable {T : Type} [CommRing T] [IsDomain T] [IsLocalRing T] (l : ℕ) [Fact l.Prime]

end Main

end GlobalTheory.GenusTwoPureComparison.Cmp

namespace GlobalTheory.GenusTwoPureComparison.Cmp

theorem aic_of_isAlgClosed' (K : Type) [Field K] [IsAlgClosed K] : GlobalTheory.EtC.AIC K := fun p hp hd =>
  IsAlgClosed.exists_root p (by rw [Polynomial.degree_eq_natDegree hp.ne_zero]; exact_mod_cast hd.ne')

end GlobalTheory.GenusTwoPureComparison.Cmp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HermitianFormNormSqLeReMulRe
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HermitianFormNormSqLeReMulRe
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GodementJacquet MeasureTheory

namespace GlobalTheory

theorem hermitianForm_norm_sq_le_re_mul_re :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ),
    (∀ v w, Bf w v = starRingEnd ℂ (Bf v w)) → (∀ v, v ≠ 0 → 0 < (Bf v v).re) →
    ∀ v w, ‖Bf v w‖ ^ 2 ≤ (Bf v v).re * (Bf w w).re := by
  intro V _ _ Bf hsymm hpos v w
  let c : PreInnerProductSpace.Core ℂ V :=
    { inner := fun x y => Bf y x
      conj_inner_symm := fun x y => by
        show starRingEnd ℂ (Bf x y) = Bf y x
        rw [hsymm x y]
      re_inner_nonneg := fun x => by
        show 0 ≤ RCLike.re (Bf x x)
        by_cases hx : x = 0
        · subst hx; simp
        · exact (hpos x hx).le
      add_left := fun x y z => by
        show Bf z (x + y) = Bf z x + Bf z y
        exact map_add _ _ _
      smul_left := fun x y r => by
        show Bf y (r • x) = starRingEnd ℂ r * Bf y x
        rw [LinearMap.map_smulₛₗ, smul_eq_mul] }
  have h := @InnerProductSpace.Core.inner_mul_inner_self_le ℂ V _ _ _ c v w
  change ‖Bf w v‖ * ‖Bf v w‖ ≤ RCLike.re (Bf v v) * RCLike.re (Bf w w) at h
  rw [hsymm v w, RCLike.norm_conj] at h
  rw [sq]
  exact h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HermitianFormNormSqLeReMulReStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GodementJacquet MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_norm_sq_le_re_mul_re_of_posDef : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ),
    (∀ v w, Bf w v = starRingEnd ℂ (Bf v w)) → (∀ v, v ≠ 0 → 0 < (Bf v v).re) →
    ∀ v w, ‖Bf v w‖ ^ 2 ≤ (Bf v v).re * (Bf w w).re := by
  first | exact @GlobalTheory.hermitianForm_norm_sq_le_re_mul_re | exact GlobalTheory.hermitianForm_norm_sq_le_re_mul_re | (intros; apply GlobalTheory.hermitianForm_norm_sq_le_re_mul_re <;> assumption)
end
end
