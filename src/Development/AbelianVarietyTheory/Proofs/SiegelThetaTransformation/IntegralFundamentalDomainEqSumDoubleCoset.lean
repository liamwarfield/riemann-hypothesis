module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockHxDifferentiable
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.KernInvariantSymmPos
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MeasurePreservingMulLeft
public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ThetaSpanAdjoint
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsWeilOfSymplectic

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IntegralFundamentalDomainEqSumDoubleCoset
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.Ker

section DoubleCoset
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem _root_.GlobalTheory.Ker.isOpen_doubleCoset_of_isOpen (Γ K : Subgroup G) (hK : IsOpen (K : Set G)) (a : G) :
    IsOpen {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k} := by
  have hunion : {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k} =
      ⋃ γ ∈ Γ, (fun k => γ * a * k) '' (K : Set G) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_image, SetLike.mem_coe, exists_prop]
    constructor
    · rintro ⟨γ, hγ, k, hk, rfl⟩
      exact ⟨γ, hγ, k, hk, rfl⟩
    · rintro ⟨γ, hγ, k, hk, rfl⟩
      exact ⟨γ, hγ, k, hk, rfl⟩
  rw [hunion]
  exact isOpen_biUnion fun γ _ => isOpenMap_mul_left (γ * a) _ hK

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem _root_.GlobalTheory.Ker.tsum_indicator_coset (Γ K : Subgroup G) (a : G)
    (hfin : {γ : G | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K}.Finite) (x : G) :
    ∑' γ : Γ, ((fun y => a⁻¹ * y) ⁻¹' (K : Set G)).indicator (1 : G → ENNReal) (γ • x)
      = ({γ : G | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K}.ncard : ENNReal) *
        {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k}.indicator 1 x := by
  by_cases hx : x ∈ {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k}
  · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one]
    obtain ⟨γ₀, hγ₀, k₀, hk₀, rfl⟩ := hx
    set T : Set Γ := {γ | a⁻¹ * ((γ : G) * (γ₀ * a * k₀)) ∈ K} with hT
    have hterm : ∀ γ : Γ, ((fun y => a⁻¹ * y) ⁻¹' (K : Set G)).indicator (1 : G → ENNReal)
        (γ • (γ₀ * a * k₀)) = T.indicator (1 : Γ → ENNReal) γ := by
      intro γ
      by_cases hγ : γ ∈ T
      · rw [Set.indicator_of_mem hγ, Set.indicator_of_mem]
        · rfl
        · exact hγ
      · rw [Set.indicator_of_notMem hγ, Set.indicator_of_notMem]
        exact hγ
    simp_rw [hterm]
    rw [← tsum_subtype T (1 : Γ → ENNReal)]
    simp only [Pi.one_apply]
    rw [ENNReal.tsum_set_one]
    have hinj : Function.Injective (fun γ : Γ => (γ : G) * γ₀) :=
      fun γ δ hγδ => Subtype.ext (mul_right_cancel hγδ)
    have himg : {γ : G | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K} = (fun γ : Γ => (γ : G) * γ₀) '' T := by
      ext δ
      constructor
      · rintro ⟨hδ, hδK⟩
        refine ⟨⟨δ * γ₀⁻¹, Γ.mul_mem hδ (Γ.inv_mem hγ₀)⟩, ?_, by simp⟩
        show a⁻¹ * (δ * γ₀⁻¹ * (γ₀ * a * k₀)) ∈ K
        have heq : a⁻¹ * (δ * γ₀⁻¹ * (γ₀ * a * k₀)) = a⁻¹ * δ * a * k₀ := by group
        rw [heq]
        exact K.mul_mem hδK hk₀
      · rintro ⟨γ, hγ, rfl⟩
        refine ⟨Γ.mul_mem γ.2 hγ₀, ?_⟩
        have hγ' : a⁻¹ * ((γ : G) * (γ₀ * a * k₀)) ∈ K := hγ
        have heq : a⁻¹ * ((γ : G) * γ₀) * a = a⁻¹ * ((γ : G) * (γ₀ * a * k₀)) * k₀⁻¹ := by group
        rw [heq]
        exact K.mul_mem hγ' (K.inv_mem hk₀)
    rw [← hinj.encard_image, ← himg, ← hfin.cast_ncard_eq, ENat.toENNReal_coe]
  · rw [Set.indicator_of_notMem hx, mul_zero]
    refine tsum_eq_zero_iff.2 fun γ => Set.indicator_of_notMem ?_ _
    intro hmem
    have hk : a⁻¹ * ((γ : G) * x) ∈ K := hmem
    exact hx ⟨(γ : G)⁻¹, Γ.inv_mem γ.2, _, hk, by group⟩

variable [MeasurableSpace G] [BorelSpace G]

end DoubleCoset

private theorem measure_fd_inter_doubleCoset_mul_ncard_eq {G : Type} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (ν : Measure G) [ν.IsMulLeftInvariant] (Γ K : Subgroup G) [Countable Γ] (D : Set G)
    (hD : IsFundamentalDomain Γ D ν) (hK : IsOpen (K : Set G)) (a : G)
    (hfin : {γ : G | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K}.Finite) :
    ν ({x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k} ∩ D) *
      ({γ : G | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K}.ncard : ENNReal) = ν K := by
  have hC : MeasurableSet {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k} :=
    (_root_.GlobalTheory.Ker.isOpen_doubleCoset_of_isOpen Γ K hK a).measurableSet
  have hmeasK : MeasurableSet ((fun y => a⁻¹ * y) ⁻¹' (K : Set G)) :=
    hK.measurableSet.preimage (measurable_const_mul _)
  have hwhole : ∫⁻ x, ((fun y => a⁻¹ * y) ⁻¹' (K : Set G)).indicator 1 x ∂ν = ν K := by
    rw [lintegral_indicator_one hmeasK, measure_preimage_mul]
  have hinv := (Equiv.inv Γ).tsum_eq (fun γ : Γ =>
    ∫⁻ x in D, ((fun y => a⁻¹ * y) ⁻¹' (K : Set G)).indicator (1 : G → ENNReal) (γ⁻¹ • x) ∂ν)
  simp only [Equiv.inv_apply, inv_inv] at hinv
  rw [← hwhole, hD.lintegral_eq_tsum', ← hinv, ← lintegral_tsum]
  · simp_rw [_root_.GlobalTheory.Ker.tsum_indicator_coset Γ K a hfin]
    rw [lintegral_const_mul _ (measurable_one.indicator hC), lintegral_indicator_one hC,
      Measure.restrict_apply hC, mul_comm]
  · intro γ
    exact ((measurable_one.indicator hmeasK).comp (measurable_const_smul γ)).aemeasurable

theorem _root_.GlobalTheory.Ker.integral_fundamentalDomain_eq_sum_doubleCoset : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsMulLeftInvariant] (Γ K : Subgroup G) [Countable Γ] (𝓖 : Set G), IsFundamentalDomain Γ 𝓖 ν → IsOpen (K : Set G) → ν K ≠ ⊤ → ∀ (ι : Type) [Fintype ι] (h : ι → G), (∀ x : G, ∃! i, ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k) → (∀ i, {γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ K}.Finite) → ∀ F : G → ℂ, (∀ γ ∈ Γ, ∀ x, F (γ * x) = F x) → (∀ k ∈ K, ∀ x, F (x * k) = F x) → ν 𝓖 ≠ ⊤ ∧ IntegrableOn F 𝓖 ν ∧ ∫ x in 𝓖, F x ∂ν = ((ν K).toReal : ℂ) * ∑ i, (({γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ K}.ncard : ℕ) : ℂ)⁻¹ * F (h i) := by
  intro G _ _ _ _ _ ν _ Γ K _ 𝓖 h𝓖 hK hKtop ι _ h huniq hfin F hFΓ hFK
  have hCmeas : ∀ i, MeasurableSet {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k} := fun i =>
    (_root_.GlobalTheory.Ker.isOpen_doubleCoset_of_isOpen Γ K hK (h i)).measurableSet
  have hpos : ∀ i, {γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ K}.ncard ≠ 0 := fun i =>
    ((Set.ncard_pos (hfin i)).2 ⟨1, Γ.one_mem, by simpa using K.one_mem⟩).ne'
  have hCG : ∀ i, ν ({x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k} ∩ 𝓖) =
      ν K / ({γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ K}.ncard : ENNReal) := by
    intro i
    rw [ENNReal.eq_div_iff (by exact_mod_cast hpos i) (ENNReal.natCast_ne_top _), mul_comm]
    exact measure_fd_inter_doubleCoset_mul_ncard_eq ν Γ K 𝓖 h𝓖 hK (h i) (hfin i)
  have hCGtop : ∀ i, ν ({x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k} ∩ 𝓖) ≠ ⊤ := by
    intro i
    rw [hCG i]
    exact (ENNReal.div_lt_top hKtop (by exact_mod_cast hpos i)).ne
  have h𝓖top : ν 𝓖 ≠ ⊤ := by
    have hsub : 𝓖 ⊆ ⋃ i, ({x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k} ∩ 𝓖) := fun x hx =>
      Set.mem_iUnion.2 ⟨(huniq x).exists.choose, (huniq x).exists.choose_spec, hx⟩
    refine ne_top_of_le_ne_top ?_ ((measure_mono hsub).trans (measure_iUnion_fintype_le _ _))
    exact ENNReal.sum_ne_top.2 fun i _ => hCGtop i
  have hdecomp : ∀ x, F x =
      ∑ i, {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k}.indicator (fun _ => F (h i)) x := by
    intro x
    obtain ⟨i, hi, hiuniq⟩ := huniq x
    rw [Finset.sum_eq_single i]
    · rw [Set.indicator_of_mem (show x ∈ {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k} from hi)]
      obtain ⟨γ, hγ, k, hk, rfl⟩ := hi
      rw [hFK k hk, hFΓ γ hγ]
    · intro j _ hj
      exact Set.indicator_of_notMem
        (show x ∉ {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h j * k} from fun hx => hj (hiuniq j hx)) _
    · intro hi'
      exact absurd (Finset.mem_univ i) hi'
  have hint : ∀ i, IntegrableOn
      ({x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k}.indicator (fun _ => F (h i))) 𝓖 ν := by
    intro i
    refine (integrable_indicator_iff (hCmeas i)).2 ?_
    refine integrableOn_const ?_
    rw [Measure.restrict_apply (hCmeas i)]
    exact hCGtop i
  refine ⟨h𝓖top, ?_, ?_⟩
  · exact (integrable_finsetSum _ fun i _ => hint i).congr
      (ae_of_all _ fun x => (hdecomp x).symm)
  · refine (congrArg (fun f : G → ℂ => ∫ x in 𝓖, f x ∂ν) (funext hdecomp)).trans ?_
    rw [integral_finsetSum _ fun i _ => hint i, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_indicator_const _ (hCmeas i), measureReal_def, Measure.restrict_apply (hCmeas i),
      hCG i, ENNReal.toReal_div, ENNReal.toReal_natCast, Complex.real_smul]
    push_cast
    ring

end GlobalTheory.Ker
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsStabiliserInvariantPullBoundedSection
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsStabiliserInvariantPullBoundedSection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.Pull

open GlobalTheory.Dict.Extend

variable {E : Type} [Field E] {r : ℕ}

section Cast

variable {Ψ Ψ' : Finset (E →+* ℂ)}

theorem cast_symm (h : Ψ = Ψ') (x : Frame Ψ r) : castFr h.symm (castFr h x) = x := rfl

theorem cast_lact (h : Ψ = Ψ') (a : GL (Fin r) E) (x : Frame Ψ r) :
    castFr h (lact a x) = lact a (castFr h x) := rfl

theorem cast_rmul (h : Ψ = Ψ') (x b : Frame Ψ r) :
    castFr h (rmul x b) = rmul (castFr h x) (castFr h b) := rfl

theorem cast_bor (h : Ψ = Ψ') {b : Frame Ψ r} (hb : b ∈ Bor Ψ r) : castFr h b ∈ Bor Ψ' r := by
  subst h; exact hb

theorem cast_GG (h : Ψ = Ψ') {G G' : Matrix (Fin r) (Fin r) E} (hG : G = G') {p p' : ℕ} (hp : p = p')
    {x : Frame Ψ r} (hx : x ∈ GG Ψ G p) : castFr h x ∈ GG Ψ' G' p' := by
  subst h hG hp; exact hx

theorem cast_diff (h : Ψ = Ψ') : Differentiable ℂ (castFr (r := r) h) := by
  subst h; exact differentiable_id

theorem cast_bchar (h : Ψ = Ψ') {la : Wt Ψ r} {la' : Wt Ψ' r}
    (hl : ∀ (τ : Ψ') i, la' τ i = la ⟨τ.1, h ▸ τ.2⟩ i) (b : Frame Ψ r) :
    bchar la' (castFr h b) = bchar la b := by
  subst h
  obtain rfl : la' = la := funext fun τ => funext fun i => hl τ i
  rfl

theorem cast_wt (h : Ψ = Ψ') {G G' : Matrix (Fin r) (Fin r) E} (hG : G = G') {la : Wt Ψ r} {la' : Wt Ψ' r}
    (hl : ∀ (τ : Ψ') i, la' τ i = la ⟨τ.1, h ▸ τ.2⟩ i) (x : Frame Ψ' r) :
    (∏ τ, ∏ i, ‖dmin G (castFr h.symm x) τ (Fin.succ i) / dmin G (castFr h.symm x) τ i.castSucc‖ ^
        (-(la τ i : ℝ) / 2)) =
      ∏ τ, ∏ i, ‖dmin G' x τ (Fin.succ i) / dmin G' x τ i.castSucc‖ ^ (-(la' τ i : ℝ) / 2) := by
  subst h hG
  obtain rfl : la' = la := funext fun τ => funext fun i => hl τ i
  rfl

end Cast

theorem inv_mulVec (a : GL (Fin r) E) (v : Fin r → E) :
    ((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem mulVec_inv (a : GL (Fin r) E) (v : Fin r → E) :
    (a : Matrix (Fin r) (Fin r) E) *ᵥ (((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

variable [NumberField E]

theorem mem_mapL {a : GL (Fin r) E} {L : Lt E r} {v : Fin r → E} :
    (a : Matrix (Fin r) (Fin r) E) *ᵥ v ∈ mapL a L ↔ v ∈ L := by
  constructor
  · rintro ⟨w, hw, e⟩
    have e' : (a : Matrix (Fin r) (Fin r) E) *ᵥ w = (a : Matrix (Fin r) (Fin r) E) *ᵥ v := e
    have : w = v := by rw [← inv_mulVec a w, e', inv_mulVec]
    exact this ▸ hw
  · intro hv
    exact ⟨v, hv, rfl⟩

variable [IsCMField E] {X : Data E r}

theorem isUn_inv {a : GL (Fin r) E} (ha : IsUn X a) : IsUn X a⁻¹ := fun x y => by
  rw [← ha, mulVec_inv, mulVec_inv]

theorem isUn_mul {a b : GL (Fin r) E} (ha : IsUn X a) (hb : IsUn X b) : IsUn X (a * b) := fun x y => by
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha, hb]

theorem conj_mem {X' : Data E r} (hG : X'.Gm = X.Gm) {a g : GL (Fin r) E} {M : ℕ} (ha : IsUn X a) (hg : IsUn X g)
    (hfix : mapL g (mapL a X'.Λ) = mapL a X'.Λ)
    (hM : ∀ u ∈ mapL a X'.Λ, ∃ u' ∈ mapL a X'.Λ, (g : Matrix (Fin r) (Fin r) E) *ᵥ u = u + M • u')
    (hP : HasPrinc X' M) : a⁻¹ * g * a ∈ X'.Γ := by
  have hc : mapL (a⁻¹ * g * a) X'.Λ = X'.Λ := by
    rw [mapL_mul, mapL_mul, hfix, ← mapL_mul, inv_mul_cancel, mapL_one]
  refine hP _ ⟨?_, fun x => ?_⟩ fun v hv => ?_
  · rw [hG]
    exact isUn_mul (isUn_mul (isUn_inv ha) hg) ha
  · rw [← mem_mapL (a := a⁻¹ * g * a), hc]
  · obtain ⟨u', ⟨w, hw, e⟩, hu⟩ := hM _ (mem_mapL.2 hv)
    have e' : (a : Matrix (Fin r) (Fin r) E) *ᵥ w = u' := e
    refine ⟨w, hw, ?_⟩
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hu, ← e',
      Matrix.mulVec_add, Matrix.mulVec_smul, inv_mulVec, inv_mulVec]

end GlobalTheory.Dict.Pull

open GlobalTheory.Dict.Extend GlobalTheory.Dict.Pull in
theorem GlobalTheory.Dict.isStabForm_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X' X : Data E r) (h : SameSp X' X) (ga : GL (Fin r) E) (la' : Wt X'.Ψ r) (la : Wt X.Ψ r) (Δ : Subgroup (GL (Fin r) E)) (M : ℕ) (P : Frame X'.Ψ r → ℂ), IsUn X ga → (∀ (τ : X.Ψ) i, la τ i = la' ⟨τ.1, by rw [h.psi]; exact τ.2⟩ i) → (∀ g' ∈ Δ, IsUn X g' ∧ (mapL g' (mapL ga X'.Λ) = mapL ga X'.Λ → ∀ u ∈ mapL ga X'.Λ, ∃ u' ∈ mapL ga X'.Λ, (g' : Matrix (Fin r) (Fin r) E) *ᵥ u = u + M • u')) → HasPrinc X' M → ChiOne X' la' → X'.IsBddSec la' P → IsStabForm X Δ (mapL ga X'.Λ) la (fun x => P (castFr h.psi.symm (lact ga⁻¹ x))) ∧ ∀ Q : Frame X.Ψ r → ℂ, DifferentiableOn ℂ Q X.dom → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Q (rmul x b) = bchar la b * Q x) → DifferentiableOn ℂ (fun x => Q (lact ga (castFr h.psi x))) X'.dom ∧ ∀ x ∈ X'.dom, lact ga (castFr h.psi x) ∈ X.dom ∧ castFr h.psi.symm (lact ga⁻¹ (lact ga (castFr h.psi x))) = x ∧ ∀ b ∈ Bor X'.Ψ r, Q (lact ga (castFr h.psi (rmul x b))) = bchar la' b * Q (lact ga (castFr h.psi x)) := by
  intro E _ _ _ r X' X h ga la' la Δ M P hga hl hΔ hP hχ hb
  obtain ⟨⟨hd, hbor, hinv⟩, C, hC⟩ := hb
  have m1 : ∀ x ∈ X.dom, castFr h.psi.symm (lact ga⁻¹ x) ∈ X'.dom := fun x hx =>
    cast_GG h.psi.symm h.gm.symm h.p0.symm (lact_mem (isUn_inv hga) hx)
  have m2 : ∀ x ∈ X'.dom, lact ga (castFr h.psi x) ∈ X.dom := fun x hx =>
    lact_mem hga (cast_GG h.psi h.gm h.p0 hx)
  refine ⟨⟨?_, ?_, ?_, C, ?_⟩, fun Q hQ hQb => ⟨?_, fun x hx => ⟨m2 x hx, ?_, fun b hb => ?_⟩⟩⟩
  · exact hd.comp ((cast_diff h.psi.symm).comp (differentiable_lact ga⁻¹)).differentiableOn m1
  · intro x hx b hb
    rw [lact_rmul, cast_rmul, hbor _ (m1 x hx) _ (cast_bor h.psi.symm hb), ← cast_bchar h.psi hl]
    rfl
  · intro g hg hfix x hx
    have hm := conj_mem h.gm hga (hΔ g hg).1 hfix ((hΔ g hg).2 hfix) hP
    have e : lact ga⁻¹ (lact g x) = lact (ga⁻¹ * g * ga) (lact ga⁻¹ x) := by
      rw [lact_lact, lact_lact, mul_inv_cancel_right]
    show P (castFr h.psi.symm (lact ga⁻¹ (lact g x))) = _
    rw [e, cast_lact, hinv _ hm _ (m1 x hx), hχ _ hm, _root_.one_mul]
  · intro x hx
    refine le_of_eq_of_le ?_ (hC _ (m1 x hx))
    unfold Data.pnorm
    rw [cast_wt h.psi h.gm hl]
    simp only [dmin_lact (isUn_inv hga)]
  · exact hQ.comp ((differentiable_lact ga).comp (cast_diff h.psi)).differentiableOn m2
  · rw [lact_lact, inv_mul_cancel, lact_one, cast_symm]
  · rw [cast_rmul, lact_rmul, hQb _ (m2 x hx) _ (cast_bor h.psi hb), cast_bchar h.psi hl]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsStabiliserInvariantPullBoundedSectionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isStabiliserInvariant_pull_bounded_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X' X : Data E r) (h : SameSp X' X) (ga : GL (Fin r) E) (la' : Wt X'.Ψ r) (la : Wt X.Ψ r) (Δ : Subgroup (GL (Fin r) E)) (M : ℕ) (P : Frame X'.Ψ r → ℂ), IsUn X ga → (∀ (τ : X.Ψ) i, la τ i = la' ⟨τ.1, by rw [h.psi]; exact τ.2⟩ i) → (∀ g' ∈ Δ, IsUn X g' ∧ (mapL g' (mapL ga X'.Λ) = mapL ga X'.Λ → ∀ u ∈ mapL ga X'.Λ, ∃ u' ∈ mapL ga X'.Λ, (g' : Matrix (Fin r) (Fin r) E) *ᵥ u = u + M • u')) → HasPrinc X' M → ChiOne X' la' → X'.IsBddSec la' P → IsStabForm X Δ (mapL ga X'.Λ) la (fun x => P (castFr h.psi.symm (lact ga⁻¹ x))) ∧ ∀ Q : Frame X.Ψ r → ℂ, DifferentiableOn ℂ Q X.dom → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Q (rmul x b) = bchar la b * Q x) → DifferentiableOn ℂ (fun x => Q (lact ga (castFr h.psi x))) X'.dom ∧ ∀ x ∈ X'.dom, lact ga (castFr h.psi x) ∈ X.dom ∧ castFr h.psi.symm (lact ga⁻¹ (lact ga (castFr h.psi x))) = x ∧ ∀ b ∈ Bor X'.Ψ r, Q (lact ga (castFr h.psi (rmul x b))) = bchar la' b * Q (lact ga (castFr h.psi x)) := by
  first | exact @GlobalTheory.Dict.isStabForm_pull | exact GlobalTheory.Dict.isStabForm_pull | (intros; apply GlobalTheory.Dict.isStabForm_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsEvenRepsTensorLatticeAndSum
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsEvenRepsTensorLatticeAndSum
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ZLat

open GlobalTheory.SW.TensLat GlobalTheory.SW.TensVac

theorem exists_even_reps {G : Type} [AddCommGroup G] (A C : AddSubgroup G) {M : ℕ} (hM : Odd M)
    (hA : ∀ a ∈ A, M • a ∈ C) {c : ℕ} (hc : C.relIndex A = c) (h0 : c ≠ 0) :
    ∃ a : Fin c → G, (∀ i, a i ∈ A) ∧ (∀ i i', 2 • a i - 2 • a i' ∈ C → i = i') ∧
      ∀ y ∈ A, ∃ i, y - 2 • a i ∈ C := by
  obtain ⟨k, rfl⟩ := hM
  have hcard : Nat.card (A ⧸ C.addSubgroupOf A) = c := hc
  haveI : Finite (A ⧸ C.addSubgroupOf A) := Nat.finite_of_card_ne_zero (hcard ▸ h0)
  let e := (Finite.equivFinOfCardEq hcard).symm
  have key (x : A) : 2 • ((k + 1) • (x : G)) = x + (2 * k + 1) • (x : G) := by
    rw [smul_smul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, succ_nsmul, add_comm]
  refine ⟨fun i => (k + 1) • ((e i).out : A), fun i => A.nsmul_mem (e i).out.2 _, ?_, ?_⟩
  · intro i i' h
    apply e.injective
    rw [← QuotientAddGroup.out_eq' (e i), ← QuotientAddGroup.out_eq' (e i'), eq_comm,
      QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    rw [key, key] at h
    have := C.add_mem (C.sub_mem h (hA _ (e i).out.2)) (hA _ (e i').out.2)
    convert this using 1
    push_cast
    abel
  · intro y hy
    refine ⟨e.symm (⟨y, hy⟩ : A), ?_⟩
    rw [key, Equiv.apply_symm_apply]
    have h := QuotientAddGroup.out_eq' ((⟨y, hy⟩ : A) : A ⧸ C.addSubgroupOf A)
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h
    have := C.sub_mem h (hA _ ((⟨y, hy⟩ : A) : A ⧸ C.addSubgroupOf A).out.2)
    convert this using 1
    push_cast
    abel

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ}

omit [IsCMField E] in
theorem stdLat_eq : stdLat E n = stdL E n := by
  ext x
  rw [Base.mem_stdL, stdLat, Submodule.mem_pi]
  refine forall_congr' fun k => ?_
  simp only [Set.mem_univ, true_imp_iff, Submodule.mem_one]
  exact ⟨fun ⟨a, ha⟩ => ha ▸ a.2, fun h => ⟨⟨_, h⟩, rfl⟩⟩

omit [IsCMField E] in
theorem mem_span_smul {N : ℕ} {S : Lt E n} {v : Fin n → E} :
    v ∈ Ideal.span {(N : 𝓞 E)} • S ↔ ∃ v' ∈ S, N • v' = v := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  simp only [Nat.cast_smul_eq_nsmul]

omit [IsCMField E] in
theorem vecMulVec_nsmul (N : ℕ) (v : Fin n → E) (u : Fin r → E) :
    vecMulVec (N • v) u = N • vecMulVec v u := by
  ext i j
  simp [vecMulVec_apply, _root_.mul_assoc]

omit [IsCMField E] in
theorem mem_tens_span_smul {N : ℕ} {S : Lt E n} {L : Lt E r} {y : Matrix (Fin n) (Fin r) E} :
    y ∈ tens (Ideal.span {(N : 𝓞 E)} • S) L ↔ ∃ z ∈ tens S L, N • z = y := by
  have : tens (Ideal.span {(N : 𝓞 E)} • S) L = (tens S L).map (nsmulAddMonoidHom N) := by
    apply le_antisymm
    · refine tens_le fun v hv u hu => ?_
      obtain ⟨v', hv', rfl⟩ := mem_span_smul.1 hv
      exact ⟨_, pure_mem hv' hu, (vecMulVec_nsmul N v' u).symm⟩
    · rw [AddSubgroup.map_le_iff_le_comap]
      refine tens_le fun v hv u hu => ?_
      rw [AddSubgroup.mem_comap, nsmulAddMonoidHom_apply, ← vecMulVec_nsmul]
      exact pure_mem (mem_span_smul.2 ⟨v, hv, rfl⟩) hu
  rw [this]
  rfl

theorem nsmul_mem_std {N : ℕ} {Λ : Lt E n} (hΛ : Λ ∈ Vset E n 1)
    (h : Ideal.span {(N : 𝓞 E)} • stdL E n ≤ Λ) {v : Fin n → E} (hv : v ∈ Λ) :
    N • v ∈ stdL E n := by
  rw [(Base.stdL_mem_Vset (E := E) n 1).2.1]
  intro y hy
  have := (hΛ.2.1 v).1 hv _ (h (mem_span_smul.2 ⟨y, hy, rfl⟩))
  convert this using 1
  simp only [Base.herm_one]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [cc]
  ring

variable {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {w : E}
  {A B C : AddSubgroup (Matrix (Fin n) (Fin r) E)}

theorem sum_reps (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n)
    (hA : Good X w A) (hCA : C ≤ A) (hCB : C ≤ B) {c : ℕ} (u : Fin c → Matrix (Fin n) (Fin r) E)
    (h1 : ∀ i, u i ∈ A) (h2 : ∀ i i', u i - u i' ∈ C → i = i') (h3 : ∀ y ∈ A, ∃ i, y - u i ∈ C)
    {v : TF n g} (hv : IsVac X bas w B v) :
    ∑ i, epsW X w (u i) • heisG X bas (u i) v = (c : ℂ) • projA X bas w A v := by
  obtain ⟨v', hv', -⟩ := hA.vac (bas := bas) hs
  have hsb (i) := rho_sb (w := w) idx hs hn (u i) hv.1
  have hsum (s : Finset (Fin c)) : IsSB (∑ i ∈ s, epsW X w (u i) • heisG X bas (u i) v) ∧
      SW.ip (∑ i ∈ s, epsW X w (u i) • heisG X bas (u i) v) v' = s.card * SW.ip v v' := by
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨isSB_zero, ?_⟩
      have := ip_smul_left 0 hv'.1 hv'.1
      simpa using this
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, ip_add_left (hsb a) ih.1 hv'.1, ih.2, Finset.card_insert_of_notMem ha]
      refine ⟨(GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ _ _ _ _ (hsb a) ih.1).1, ?_⟩
      have := rho_ip (w := w) idx hs hn (u a) hv.1 hv'.1
      rw [hv'.2.2 _ (h1 a)] at this
      rw [this]
      push_cast
      ring
  obtain ⟨k1, k2⟩ := hsum Finset.univ
  rw [hA.uniq hs hv' k1, k2, (hA.proj idx hs hn hv.1 hv').2, smul_smul, Finset.card_univ,
    Fintype.card_fin]
  intro y hy
  choose σ hσ using fun i => h3 (y + u i) (A.add_mem hy (h1 i))
  have hinj : Function.Injective σ := by
    intro i i' h
    apply h2
    have := C.sub_mem (hσ i) (hσ i')
    rw [h] at this
    convert this using 1
    abel
  have hlin (f : Fin c → SW.TF n g) : heisG X bas y (∑ i, f i) = ∑ i, heisG X bas y (f i) := by
    funext x; simp [heisG, heisS, Finset.sum_mul]
  rw [hlin, Finset.smul_sum]
  refine Fintype.sum_bijective σ (Finite.injective_iff_bijective.1 hinj) _ _ fun i => ?_
  rw [hA.rho_rho idx hs hn hy (h1 i) hv.1]
  conv_rhs => rw [← hv.2.2 _ (hCB (hσ i))]
  rw [hA.rho_rho idx hs hn (h1 _) (hCA (hσ i)) hv.1, add_sub_cancel]

end

theorem exists_reps_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L : Lt E r, SelfD X L → ∀ Λ ∈ Vset E n 1, ∀ N : ℕ, Odd N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ → ∃ u : Fin ((⟨Λ⟩ : GenLat E n).zCard N r) → Matrix (Fin n) (Fin r) E, (∀ i, u i ∈ tens Λ L ∧ ∀ b, ∃ u' ∈ L, N • u i b = (2 : ℕ) • u') ∧ (∀ i i', (∀ b, ∃ u' ∈ L, u i b - u i' b = N • u') → i = i') ∧ 0 < (⟨Λ⟩ : GenLat E n).zCard N r ∧ 0 < (⟨Λ⟩ : GenLat E n).mIdx N r ∧ ∀ v : TF n g, IsVac X bas w (tens (stdL E n) L) v → ∑ i, heisG X bas (u i) v = (((⟨Λ⟩ : GenLat E n).zCard N r : ℕ) : ℂ) • projA X bas w (tens Λ L) v := by
  intro E _ _ _ r X g bas idx n hs hn w hw hw' L hL Λ hΛ N hN hle
  have hN0 : N ≠ 0 := hN.pos.ne'
  have hstd := Base.stdL_mem_Vset (E := E) n 1
  have hA : Good X w (tens Λ L) := by
    obtain ⟨h1, h2, h3, -⟩ :=
      tens_selfDual_semichar_index E r X g bas idx n hs hn w hw hw' L hL 1 Λ hΛ
    exact ⟨h1, h2, h3⟩
  have hle' := hle
  rw [stdLat_eq] at hle'
  have hsp : Submodule.span E ((Ideal.span {(N : 𝓞 E)} • stdL E n : Lt E n) : Set (Fin n → E)) = ⊤ := by
    rw [eq_top_iff, ← DualFamily.span_eq_top _ hstd.1 fun x => (hstd.2.1 x).2, Submodule.span_le]
    intro x hx
    have : x = (N : E)⁻¹ • (N • x) := by
      rw [← Nat.cast_smul_eq_nsmul E, inv_smul_smul₀ (Nat.cast_ne_zero.2 hN0)]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (mem_span_smul.2 ⟨x, hx, rfl⟩))
  have hidx : (tens (Ideal.span {(N : 𝓞 E)} • stdL E n) L).relIndex (tens Λ L) =
      (⟨Λ⟩ : GenLat E n).zCard N r := by
    rw [relIndex_tens_left hL.1 (span_of_selfD X hL) hΛ.1 hsp, GenLat.zCard, stdLat_eq]
    rfl
  have hfin : (Ideal.span {(N : 𝓞 E)} • stdLat E n).toAddSubgroup.relIndex Λ.toAddSubgroup ≠ 0 := by
    have hfg : Λ.toAddSubgroup.FG := by
      haveI : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 hΛ.1
      haveI : Module.Finite ℤ Λ := Module.Finite.trans (𝓞 E) Λ
      exact (AddGroup.fg_iff_addSubgroup_fg _).1 (Module.Finite.iff_addGroup_fg.1 this)
    haveI : AddGroup.FG Λ.toAddSubgroup := (AddGroup.fg_iff_addSubgroup_fg _).2 hfg
    haveI := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg Λ.toAddSubgroup
      (mul_ne_zero hN0 hN0)
    have : (nsmulAddMonoidHom (α := Λ.toAddSubgroup) (N * N)).range ≤
        (Ideal.span {(N : 𝓞 E)} • stdLat E n).toAddSubgroup.addSubgroupOf Λ.toAddSubgroup := by
      rintro _ ⟨x, rfl⟩
      rw [AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup, stdLat_eq, mem_span_smul]
      exact ⟨N • (x : Fin n → E), nsmul_mem_std hΛ hle' x.2, by simp [mul_smul]⟩
    exact (AddSubgroup.finiteIndex_of_le this).index_ne_zero
  have hz : 0 < (⟨Λ⟩ : GenLat E n).zCard N r := pow_pos (Nat.pos_of_ne_zero hfin) r
  have hm : 0 < (⟨Λ⟩ : GenLat E n).mIdx N r := by
    refine pow_pos (Nat.pos_of_ne_zero fun h => hfin ?_) r
    exact AddSubgroup.relIndex_eq_zero_of_le_right (K := (⟨Λ⟩ : GenLat E n).Ln.toAddSubgroup)
      (fun x hx => hx.1) h
  have hNA : ∀ y ∈ tens Λ L, N • y ∈ tens (stdL E n) L := by
    have : tens Λ L ≤ (tens (stdL E n) L).comap (nsmulAddMonoidHom N) :=
      tens_le fun v hv u hu => by
        rw [AddSubgroup.mem_comap, nsmulAddMonoidHom_apply, ← vecMulVec_nsmul]
        exact pure_mem (nsmul_mem_std hΛ hle' hv) hu
    exact fun y hy => this hy
  obtain ⟨a, ha1, ha2, ha3⟩ := exists_even_reps (tens Λ L)
    (tens (Ideal.span {(N : 𝓞 E)} • stdL E n) L) (hN.mul hN)
    (fun y hy => mem_tens_span_smul.2 ⟨_, hNA y hy, by rw [mul_smul]⟩) hidx hz.ne'
  refine ⟨fun i => 2 • a i, fun i => ⟨AddSubgroup.nsmul_mem _ (ha1 i) 2, fun b =>
    ⟨_, (mem_tens_stdL L _).1 (hNA _ (ha1 i)) b, ?_⟩⟩, fun i i' h => ha2 i i' ?_, hz, hm,
    fun v hv => ?_⟩
  · exact smul_comm N 2 (a i b)
  · choose z hz hz' using h
    refine mem_tens_span_smul.2 ⟨z, (mem_tens_stdL L _).2 hz, ?_⟩
    funext b
    exact (hz' b).symm
  · rw [← sum_reps idx hs hn hA (C := tens (Ideal.span {(N : 𝓞 E)} • stdL E n) L)
      (tens_le fun v hv u hu => pure_mem (hle' hv) hu)
      (tens_le fun v hv u hu => pure_mem (Submodule.smul_le_right hv) hu)
      (fun i => 2 • a i) (fun i => AddSubgroup.nsmul_mem _ (ha1 i) 2) ha2 ha3 hv]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hA.eps_two hs (ha1 i), one_smul]

end GlobalTheory.Dict.ZLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsEvenRepsTensorLatticeAndSumStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_even_reps_tensorLattice_and_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L : Lt E r, SelfD X L → ∀ Λ ∈ Vset E n 1, ∀ N : ℕ, Odd N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ → ∃ u : Fin ((⟨Λ⟩ : GenLat E n).zCard N r) → Matrix (Fin n) (Fin r) E, (∀ i, u i ∈ tens Λ L ∧ ∀ b, ∃ u' ∈ L, N • u i b = (2 : ℕ) • u') ∧ (∀ i i', (∀ b, ∃ u' ∈ L, u i b - u i' b = N • u') → i = i') ∧ 0 < (⟨Λ⟩ : GenLat E n).zCard N r ∧ 0 < (⟨Λ⟩ : GenLat E n).mIdx N r ∧ ∀ v : TF n g, IsVac X bas w (tens (stdL E n) L) v → ∑ i, heisG X bas (u i) v = (((⟨Λ⟩ : GenLat E n).zCard N r : ℕ) : ℂ) • projA X bas w (tens Λ L) v := by
  first | exact @GlobalTheory.Dict.ZLat.exists_reps_sum | exact GlobalTheory.Dict.ZLat.exists_reps_sum | (intros; apply GlobalTheory.Dict.ZLat.exists_reps_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.KZeroOnFrConstEntire
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.Ker

private theorem det_sgnM_eq_prod_sgn {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : Data E r) : (sgnM X).det = ∏ a : Fin r, ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) := by
  simp [sgnM, Matrix.det_diagonal]

theorem normSq_det_of_isONFr {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    {X : Data E r} {x : Frame X.Ψ r} (hx : IsONFr X x) (τ : X.Ψ) :
    normSq (mat x τ).det = ‖(X.Gm.map τ.1).det‖⁻¹ := by

  have hdet := congrArg Matrix.det (hx τ)
  rw [GlobalTheory.SW.Slab.det_gram, det_sgnM_eq_prod_sgn X] at hdet
  have hG : (X.Gm.map τ.1).det = τ.1 X.Gm.det := (RingHom.map_det τ.1 X.Gm).symm
  have hn := congrArg norm hdet
  rw [norm_mul, norm_mul, Complex.norm_conj, norm_prod] at hn
  simp only [GlobalTheory.SW.Slab.norm_sgn, Finset.prod_const_one] at hn
  rw [hG, Complex.normSq_eq_norm_sq]
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← hn]
  ring

theorem kZero_onFr_const_entire : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → (∃ κ : ℝ, 0 < κ ∧ ∀ x : Frame X.Ψ r, IsONFr X x → x ∈ X.dom ∧ kZero X idx x x (0 : Fin n → Fin g → ℂ) 0 = κ) ∧ ∀ x₁ ∈ X.dom, ∀ x₂ ∈ X.dom, Differentiable ℂ (fun p : (Fin n → Fin g → ℂ) × (Fin n → Fin g → ℂ) => kZero X idx x₁ x₂ p.1 p.2) := by
  intro E _ _ _ r X g q0 hr bas idx n _ _
  refine ⟨⟨∏ τ : X.Ψ, ‖(X.Gm.map τ.1).det‖⁻¹ ^ (n / 2), ?_, fun x hx => ⟨?_, ?_⟩⟩, ?_⟩
  ·
    refine Finset.prod_pos fun τ _ => pow_pos (inv_pos.mpr (norm_pos_iff.mpr ?_)) _
    exact GlobalTheory.SW.KernSym.det_map_Gm X τ
  ·
    obtain ⟨δ₀, hδ₀, hs⟩ := GlobalTheory.SW.thin_slab E r X
    obtain ⟨-, hsub, hon, -⟩ := hs δ₀ hδ₀ le_rfl
    exact hsub (hon x hx)
  ·

    rw [GlobalTheory.SW.KernSym.kZero_ortho idx hx]
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, Complex.exp_zero, mul_one]
    congr 1
    exact Finset.prod_congr rfl fun τ _ => by rw [normSq_det_of_isONFr hx τ]
  ·
    intro x₁ _ x₂ _ p
    exact (GlobalTheory.SW.KernSym.analyticAt_kZero X idx x₁ x₂ p).differentiableAt

end GlobalTheory.Ker
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HeisenbergVacuumProjectionRootOfUnityPhases
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.VacuumTensorLatticeFixedRationalHeisenberg
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.VacuumTensorLatticeFixedRationalHeisenberg
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

namespace GlobalTheory.Phase

theorem vacS_of_isVac : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L : Lt E r, SelfD X L → ∀ Λ ∈ Vset E n 1, ∀ v : TF n g, IsVac X bas w (tens Λ L) v → ∃ A ε, VacS A ε v := by
  intro E _ _ _ r X g bas idx n hs hn w hw hw' L hL Λ hΛ v hv
  have hA : TensVac.Good X w (tens Λ L) := by
    obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.T.tensorLattice_selfDual_semicharacter_index E r X g bas idx n hs hn w hw hw' L hL 1 Λ hΛ
    exact ⟨h1, h2, h3⟩
  let e := AddEquiv.ofBijective _ (TensVac.crdHom_bijective (n := n) hs)
  have he (y) : e.symm (TensVac.crdHom hs y) = y := e.symm_apply_apply y
  have ho (y y' : Matrix (Fin n) (Fin r) E) :
      Phase.om (TensVac.crdHom hs y) (TensVac.crdHom hs y') = -∑ k, EF X (y k) (y' k) :=
    TensVac.om_crdHom hs y y'
  refine ⟨(tens Λ L).map (TensVac.crdHom hs), fun p => epsW X w (e.symm p),
    Vac.fg_map hA.1 _, ?_, ?_, ?_, ⟨2, two_pos, ?_⟩, hv.1, ?_⟩
  · intro p
    obtain ⟨y, rfl⟩ := (TensVac.crdHom_bijective hs).2 p
    rw [AddSubgroup.mem_map_iff_mem (TensVac.crdHom_bijective hs).1, hA.2.1]
    constructor
    · rintro h _ ⟨y', hy', rfl⟩
      obtain ⟨k, hk⟩ := h y' hy'
      exact ⟨-k, by rw [ho, hk, Int.cast_neg]⟩
    · intro h y' hy'
      obtain ⟨k, hk⟩ := h _ ⟨y', hy', rfl⟩
      rw [ho] at hk
      exact ⟨-k, by rw [Int.cast_neg, ← hk, neg_neg]⟩
  · rintro _ ⟨y, hy, rfl⟩
    have := congrArg norm (TensVac.epsW_mul_conj (X := X) w (e.symm (TensVac.crdHom hs y)))
    rw [norm_mul, Complex.norm_conj, norm_one] at this
    exact (mul_self_eq_one_iff.1 this).resolve_right fun h => by
      linarith [norm_nonneg (epsW X w (e.symm (TensVac.crdHom hs y)))]
  · rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩
    rw [← map_add (f := _), he, he, he, ho, (hA.2.2 y hy).2 y' hy', Rat.cast_neg, mul_neg]
  · rintro _ ⟨y, hy, rfl⟩
    rw [← map_nsmul, he, hA.eps_two hs hy]
  · rintro _ ⟨y, hy, rfl⟩
    rw [he]
    exact hv.2.2 y hy

end GlobalTheory.Phase
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.VacuumTensorLatticeFixedRationalHeisenbergStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_tensorLattice_fixed_rational_heisenberg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L : Lt E r, SelfD X L → ∀ Λ ∈ Vset E n 1, ∀ v : TF n g, IsVac X bas w (tens Λ L) v → ∃ A ε, VacS A ε v := by
  first | exact @GlobalTheory.Phase.vacS_of_isVac | exact GlobalTheory.Phase.vacS_of_isVac | (intros; apply GlobalTheory.Phase.vacS_of_isVac <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HeisenbergVacuumProjectionRootOfUnityPhases
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

namespace GlobalTheory.Phase.Proj

section General

variable {α β : Type} [Fintype α] [Fintype β]

theorem ip_smul_smul {φ ψ : Matrix α β ℚ → ℂ} (hφ : IsSB φ) (hψ : IsSB ψ) (a b : ℂ) :
    ip (a • φ) (b • ψ) = a * conj b * ip φ ψ := by
  have hψc : IsSB (fun x => conj (ψ x)) := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ α β ψ ψ hψ hψ).2.2.2.1
  have hpr : IsSB (φ * fun x => conj (ψ x)) := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ α β φ _ hφ hψc).2.2.1
  have hlin := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ α β _ _ hpr hpr).2.2.2.2.2.1 (a * conj b)
  have hfun : (fun x => (a • φ) x * conj ((b • ψ) x)) = (a * conj b) • (φ * fun x => conj (ψ x)) := by
    funext x
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, map_mul]
    ring
  show haar (fun x => (a • φ) x * conj ((b • ψ) x)) = a * conj b * haar (φ * fun x => conj (ψ x))
  rw [hfun, hlin]

theorem ip_conj {φ ψ : Matrix α β ℚ → ℂ} (hφ : IsSB φ) (hψ : IsSB ψ) :
    ip ψ φ = conj (ip φ ψ) := by
  have hψc : IsSB (fun x => conj (ψ x)) := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ α β ψ ψ hψ hψ).2.2.2.1
  have hpr : IsSB (φ * fun x => conj (ψ x)) := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ α β φ _ hφ hψc).2.2.1
  have hc := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ α β _ _ hpr hpr).2.2.2.2.2.2.1
  have hfun : (fun x => ψ x * conj (φ x)) = fun x => conj ((φ * fun x => conj (ψ x)) x) := by
    funext x
    simp only [Pi.mul_apply, map_mul, Complex.conj_conj]
    ring
  show haar (fun x => ψ x * conj (φ x)) = conj (haar (φ * fun x => conj (ψ x)))
  rw [hfun, hc]

theorem ph_ip [DecidableEq β] {φ ψ : Matrix α β ℚ → ℂ} (hφ : PV φ) (hψ : PV ψ) : Ph (ip φ ψ) := by
  have sφ : Shape φ := (GlobalTheory.T.selfDualVacuum_gaussian_shape_rootOfUnity_phases α β φ).2.1 hφ
  have sψ : Shape ψ := (GlobalTheory.T.selfDualVacuum_gaussian_shape_rootOfUnity_phases α β ψ).2.1 hψ
  have sψc : Shape (fun x => conj (ψ x)) := (GlobalTheory.T.isCosetQuadraticPhaseTestFunction_conj_character_mul α β ψ sψ).1
  have spr : Shape (fun x => φ x * conj (ψ x)) := (GlobalTheory.T.isCosetQuadraticPhaseTestFunction_conj_character_mul α β φ sφ).2.2 _ sψc
  exact GlobalTheory.T.schwartzBruhatIntegral_gaussianShape_rootOfUnityPhase α β _ spr

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}

theorem isVac_smul {w : E} {A : AddSubgroup (Matrix (Fin n) (Fin r) E)} {v : TF n g}
    (hv : IsVac X bas w A v) {u : ℂ} (hu : ‖u‖ = 1) : IsVac X bas w A (u • v) := by
  have hv' := hv
  unfold IsVac at hv'
  obtain ⟨hsb, hip, hfix⟩ := hv'
  unfold IsVac
  refine ⟨(GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ (Fin n) (Fin g) v v hsb hsb).2.1 u, ?_, ?_⟩
  · rw [ip_smul_smul hsb hsb, hip, _root_.mul_one, Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]
    simp
  · intro y hy
    have hlin : heisG X bas y (u • v) = u • heisG X bas y v := by
      funext x
      simp only [heisG, heisS, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hlin, smul_comm, hfix y hy]

theorem unitv_smul {v : TF n g} (hv : IsSB v) (h1 : ip v v = 1) (c : ℂ) :
    unitv (c • v) = (((‖c‖ : ℝ) : ℂ)⁻¹ * c) • v := by
  have hc : ip (c • v) (c • v) = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    rw [ip_smul_smul hv hv, h1, _root_.mul_one, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  unfold unitv
  rw [hc, Complex.ofReal_re, Real.sqrt_sq (norm_nonneg c), smul_smul]

theorem proj_phases : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L : Lt E r, SelfD X L → ∀ v : TF n g, IsVac X bas w (tens (stdL E n) L) v → ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ Λ ∈ Vset E n 1, IsVac X bas w (tens Λ L) (unitv (projA X bas w (tens Λ L) v)) ∧ PV (u • unitv (projA X bas w (tens Λ L) v)) ∧ projA X bas w (tens Λ L) v = ((Real.sqrt (((stdL E n).toAddSubgroup.relIndex Λ.toAddSubgroup ^ r : ℕ) : ℝ) : ℝ) : ℂ)⁻¹ • unitv (projA X bas w (tens Λ L) v) := by
  intro E _ _ _ r X g bas idx n hs hn w hw hw1 L hL v hv
  have hstd : stdL E n ∈ Vset E n 1 := GlobalTheory.SW.Base.stdL_mem_Vset n 1
  have hv' := hv
  unfold IsVac at hv'
  obtain ⟨A, ε, hA⟩ := GlobalTheory.T.vacuum_tensorLattice_fixed_rational_heisenberg E r X g bas idx n hs hn w hw hw1 L hL (stdL E n) hstd v hv
  obtain ⟨u, hu1, hupv⟩ := (GlobalTheory.T.selfDualVacuum_gaussian_shape_rootOfUnity_phases (Fin n) (Fin g) v).2.2.1 A ε hA
  refine ⟨u, hu1, fun Λ hΛ => ?_⟩
  have H := GlobalTheory.T.tensorLattice_vacua_exist_unique E r X g bas idx n hs hn w hw hw1 L hL 1 Λ hΛ
  obtain ⟨vΛ, hvΛ⟩ := H.1
  have hvΛ' := hvΛ
  unfold IsVac at hvΛ'
  have hproj : projA X bas w (tens Λ L) v = ip v vΛ • vΛ := H.2.2.1 v hv'.1 vΛ hvΛ
  have hnorm := H.2.2.2 L hL (stdL E n) hstd vΛ v hvΛ hv
  rw [(GlobalTheory.T.tensorLattice_selfDual_semicharacter_index E r X g bas idx n hs hn w hw hw1 L hL 1 Λ hΛ).2.2.2.2.2 (stdL E n) hstd,
    ip_conj hv'.1 hvΛ'.1, Complex.norm_conj] at hnorm
  have hsq := congrArg Real.sqrt hnorm
  rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _), Real.sqrt_one] at hsq
  have hc0 : ‖ip v vΛ‖ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hsq
    exact zero_ne_one hsq
  have hunit : unitv (projA X bas w (tens Λ L) v) = (((‖ip v vΛ‖ : ℝ) : ℂ)⁻¹ * ip v vΛ) • vΛ := by
    rw [hproj]
    exact unitv_smul hvΛ'.1 hvΛ'.2.1 _
  have he : ‖((‖ip v vΛ‖ : ℝ) : ℂ)⁻¹ * ip v vΛ‖ = 1 := by
    rw [norm_mul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hc0]
  refine ⟨?_, ?_, ?_⟩
  · rw [hunit]
    exact isVac_smul hvΛ he
  · obtain ⟨A', ε', hA'⟩ := GlobalTheory.T.vacuum_tensorLattice_fixed_rational_heisenberg E r X g bas idx n hs hn w hw hw1 L hL Λ hΛ vΛ hvΛ
    obtain ⟨u', hu'1, hu'pv⟩ := (GlobalTheory.T.selfDualVacuum_gaussian_shape_rootOfUnity_phases (Fin n) (Fin g) vΛ).2.2.1 A' ε' hA'
    have hph : Ph (ip (u • v) (u' • vΛ)) := ph_ip hupv hu'pv
    have hu'u : conj u' * u' = 1 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hu'1]
      simp
    have heq : u • unitv (projA X bas w (tens Λ L) v) =
        (ip (u • v) (u' • vΛ) * ((‖ip v vΛ‖ : ℝ) : ℂ)⁻¹) • (u' • vΛ) := by
      rw [hunit, ip_smul_smul hv'.1 hvΛ'.1, smul_smul, smul_smul]
      congr 1
      linear_combination (-(u * ip v vΛ * ((‖ip v vΛ‖ : ℝ) : ℂ)⁻¹)) * hu'u
    rw [heq]
    exact (GlobalTheory.T.selfDualVacuum_gaussian_shape_rootOfUnity_phases (Fin n) (Fin g) (u' • vΛ)).2.2.2.1 hu'pv _
      (Ph.mul hph (Ph.inv ((GlobalTheory.T.complex_phase_calculus_rootOfUnity).2.2.1 ‖ip v vΛ‖)))
  · have hC : ((Real.sqrt (((stdL E n).toAddSubgroup.relIndex Λ.toAddSubgroup ^ r : ℕ) : ℝ) : ℝ) : ℂ) *
        ((‖ip v vΛ‖ : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, hsq, Complex.ofReal_one]
    rw [hunit, hproj, smul_smul, ← _root_.mul_assoc, ← _root_.mul_inv, hC, inv_one, _root_.one_mul]

end GlobalTheory.Phase.Proj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HeisenbergVacuumProjectionRootOfUnityPhasesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergVacuum_projection_rootOfUnity_phases : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L : Lt E r, SelfD X L → ∀ v : TF n g, IsVac X bas w (tens (stdL E n) L) v → ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ Λ ∈ Vset E n 1, IsVac X bas w (tens Λ L) (unitv (projA X bas w (tens Λ L) v)) ∧ PV (u • unitv (projA X bas w (tens Λ L) v)) ∧ projA X bas w (tens Λ L) v = ((Real.sqrt (((stdL E n).toAddSubgroup.relIndex Λ.toAddSubgroup ^ r : ℕ) : ℝ) : ℝ) : ℂ)⁻¹ • unitv (projA X bas w (tens Λ L) v) := by
  first | exact @GlobalTheory.Phase.Proj.proj_phases | exact GlobalTheory.Phase.Proj.proj_phases | (intros; apply GlobalTheory.Phase.Proj.proj_phases <;> assumption)
end
end
