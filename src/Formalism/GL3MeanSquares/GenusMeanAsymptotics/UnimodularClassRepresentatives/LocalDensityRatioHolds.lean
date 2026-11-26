module

public import Lemmata.GeneralBFactLeftRest.Imports
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FactorIdentity
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.RelIndexEqMapMulKer

@[expose] public section

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.RelIndexSSubInfEq
section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SurjectiveOfNondegenerate
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.D2.IA

variable {K : Type} [Field K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem surjective_of_nondegenerate {h : V →ₗ⋆[K] V →ₗ[K] K} (hn : h.Nondegenerate) :
    Function.Surjective h := by
  have hinj : Function.Injective h := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    exact hn.1 x (fun y => by rw [hx]; rfl)
  have hbij : Function.Bijective (h.rangeRestrict) :=
    ⟨fun a b hab => hinj (congrArg Subtype.val hab), h.surjective_rangeRestrict⟩
  let j : V ≃+ LinearMap.range h := AddEquiv.ofBijective (h.rangeRestrict).toAddMonoidHom hbij
  have hr : Module.rank K V = Module.rank K (LinearMap.range h) :=
    rank_eq_of_equiv_equiv (starRingEnd K) j star_involutive.bijective (fun r m => by
      apply Subtype.ext
      show h (r • m) = (starRingEnd K) r • h m
      rw [map_smulₛₗ])
  have hf : finrank K (LinearMap.range h) = finrank K (Dual K V) := by
    rw [Subspace.dual_finrank_eq]
    unfold finrank
    rw [hr]
  have htop := Submodule.eq_top_of_finrank_eq hf
  exact LinearMap.range_eq_top.1 htop

theorem exists_adj {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hn : h.Nondegenerate)
    (s : V →ₗ⋆[K] V →ₗ[K] K) : ∃ Y : V →ₗ[K] V, ∀ x y, h x (Y y) = s x y := by
  have hex : ∀ y, ∃ w, ∀ x, h x w = s x y := by
    intro y
    let l : V →ₗ[K] K :=
      { toFun := fun x => star (s x y)
        map_add' := fun a b => by simp
        map_smul' := fun a b => by simp [starRingEnd_apply] }
    obtain ⟨w, hw⟩ := surjective_of_nondegenerate hn l
    refine ⟨w, fun x => ?_⟩
    have h1 : h w x = star (s x y) := by rw [hw]; rfl
    have h2 := hs.eq w x
    rw [← h2, h1, starRingEnd_apply, star_star]
  choose Y hY using hex
  refine ⟨{ toFun := Y, map_add' := fun a b => ?_, map_smul' := fun a b => ?_ }, fun x y => hY y x⟩
  · rw [← sub_eq_zero]
    refine hn.2 _ (fun x => ?_)
    rw [map_sub, map_add (f := _), hY, hY, hY, map_add (f := _), sub_self]
  · rw [← sub_eq_zero]
    refine hn.2 _ (fun x => ?_)
    rw [RingHom.id_apply, map_sub, map_smul, hY, hY, map_smul, sub_self]

section Lat

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

def phi (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V ≃ₗ[K] V) : V →ₗ⋆[K] V →ₗ[K] K :=
  (h.comp (X : V →ₗ[K] V)).compl₂ (X : V →ₗ[K] V) - h

theorem phi_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V ≃ₗ[K] V) (x y : V) :
    phi h X x y = h (X x) (X y) - h x y := rfl

theorem star_phi {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (X : V ≃ₗ[K] V) (x y : V) :
    star (phi h X x y) = phi h X y x := by
  have e : ∀ a b, star (h a b) = h b a := fun a b => hs.eq a b
  rw [phi_apply, phi_apply, star_sub, e, e]

theorem unif_ne_zero {𝔭 : Ideal (𝓞 F)} {π : 𝓞 F} (hπ' : π ∉ 𝔭 ^ 2) : algebraMap F K (π : F) ≠ 0 := by
  intro h0
  have h1 : (π : F) = 0 := (map_eq_zero (algebraMap F K)).1 h0
  have h2 : π = 0 := by exact_mod_cast h1
  exact hπ' (h2 ▸ zero_mem _)

theorem sesq_scale (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {A₀ B₀ : Submodule (𝓞 K) V} {r : ℕ}
    (hr : extP K 𝔭 ^ r • locF 𝔭 A₀ ≤ locF 𝔭 B₀) (s : V →ₗ⋆[K] V →ₗ[K] K) {n m : ℕ} (hnm : n + 2 * r ≤ m)
    (hs : ∀ x ∈ locF 𝔭 B₀, ∀ y ∈ locF 𝔭 B₀, s x y ∈ pK K 𝔭 m) :
    ∀ x ∈ locF 𝔭 A₀, ∀ y ∈ locF 𝔭 A₀, s x y ∈ pK K 𝔭 n := by
  obtain ⟨π, hπ, hπ'⟩ := exists_unif h𝔭
  have h0 : algebraMap F K (π : F) ≠ 0 := unif_ne_zero hπ'
  have hst : star (algebraMap F K (π : F)) = algebraMap F K (π : F) := (hF _).2 ⟨_, rfl⟩
  intro x hx y hy
  have hx' : algebraMap F K (π : F) ^ r • x ∈ locF 𝔭 B₀ :=
    hr ((mem_smul_iff_unif h𝔭 hπ hπ' A₀).2 ⟨x, hx, rfl⟩)
  have hy' : algebraMap F K (π : F) ^ r • y ∈ locF 𝔭 B₀ :=
    hr ((mem_smul_iff_unif h𝔭 hπ hπ' A₀).2 ⟨y, hy, rfl⟩)
  have h1 := pK_anti (K := K) 𝔭 hnm (hs _ hx' _ hy')
  rw [map_smul, map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_pow, hst, smul_eq_mul, smul_eq_mul] at h1
  obtain ⟨b, hb, e⟩ := (mem_pK_iff_unif h𝔭 hπ hπ').1 h1
  refine (mem_pK_iff_unif h𝔭 hπ hπ').2 ⟨b, hb, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero (2 * r) h0)
  calc algebraMap F K (π : F) ^ (2 * r) * s x y
      = algebraMap F K (π : F) ^ r * (algebraMap F K (π : F) ^ r * s x y) := by ring
    _ = algebraMap F K (π : F) ^ (n + 2 * r) * b := e
    _ = _ := by ring

theorem end_scale {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {A₀ B₀ : Submodule (𝓞 K) V} {r r' : ℕ}
    (hr : extP K 𝔭 ^ r • locF 𝔭 A₀ ≤ locF 𝔭 B₀) (hr' : extP K 𝔭 ^ r' • locF 𝔭 B₀ ≤ locF 𝔭 A₀)
    (Y : V →ₗ[K] V) {n m : ℕ} (hnm : n + r + r' ≤ m)
    (hY : ∀ x ∈ locF 𝔭 A₀, Y x ∈ extP K 𝔭 ^ m • locF 𝔭 A₀) :
    ∀ x ∈ locF 𝔭 B₀, Y x ∈ extP K 𝔭 ^ n • locF 𝔭 B₀ := by
  obtain ⟨π, hπ, hπ'⟩ := exists_unif h𝔭
  have h0 : algebraMap F K (π : F) ≠ 0 := unif_ne_zero hπ'
  intro x hx
  have hx' : algebraMap F K (π : F) ^ r' • x ∈ locF 𝔭 A₀ :=
    hr' ((mem_smul_iff_unif h𝔭 hπ hπ' B₀).2 ⟨x, hx, rfl⟩)
  have h1 := smul_anti 𝔭 (locF 𝔭 A₀) hnm (hY _ hx')
  obtain ⟨a, ha, e⟩ := (mem_smul_iff_unif h𝔭 hπ hπ' A₀).1 h1
  have ha' : algebraMap F K (π : F) ^ r • a ∈ locF 𝔭 B₀ :=
    hr ((mem_smul_iff_unif h𝔭 hπ hπ' A₀).2 ⟨a, ha, rfl⟩)
  refine (mem_smul_iff_unif h𝔭 hπ hπ' B₀).2 ⟨_, ha', ?_⟩
  rw [map_smul] at e
  apply smul_right_injective V (pow_ne_zero r' h0)
  show algebraMap F K (π : F) ^ r' • Y x = algebraMap F K (π : F) ^ r' • _
  rw [e, smul_smul, smul_smul]
  congr 1
  ring

end Lat

end Formalism.HermitianLattices.Ext.L3.D2.IA
end
end

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.D2

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

private theorem exists_int_add_star_eq_one_of_isCMUnram (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) :
    ∃ θ : 𝓞 K, algebraMap (𝓞 K) K θ + star (algebraMap (𝓞 K) K θ) = 1 := by
  classical
  have hstarF : ∀ f : F, star (algebraMap F K f) = algebraMap F K f := fun f => (hF _).mpr ⟨f, rfl⟩
  have hint : ∀ c : 𝓞 F, IsIntegral ℤ (algebraMap F K (algebraMap (𝓞 F) F c)) := fun c =>
    (isIntegral_algebraMap_iff ).mpr
      (NumberField.RingOfIntegers.isIntegral_coe c)
  have hcompat : ∀ x : 𝓞 F, algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) x) =
      algebraMap F K (algebraMap (𝓞 F) F x) := fun x => rfl
  let tr : 𝓞 K → K := fun θ => algebraMap (𝓞 K) K θ + star (algebraMap (𝓞 K) K θ)
  show ∃ θ : 𝓞 K, tr θ = 1
  by_contra hne
  push_neg at hne
  let I : Ideal (𝓞 F) :=
    { carrier := {a | ∃ θ : 𝓞 K, tr θ = algebraMap F K (algebraMap (𝓞 F) F a)}
      add_mem' := by
        rintro a b ⟨θ, hθ⟩ ⟨θ', hθ'⟩
        refine ⟨θ + θ', ?_⟩
        simp only [tr, map_add (f := _), star_add] at hθ hθ' ⊢
        linear_combination hθ + hθ'
      zero_mem' := ⟨0, by simp [tr]⟩
      smul_mem' := by
        rintro c a ⟨θ, hθ⟩
        refine ⟨algebraMap (𝓞 F) (𝓞 K) c * θ, ?_⟩
        simp only [tr, smul_eq_mul, map_mul, star_mul', hcompat, hstarF] at hθ ⊢
        linear_combination (algebraMap F K (algebraMap (𝓞 F) F c)) * hθ }
  have hI : (1 : 𝓞 F) ∉ I := by
    rintro ⟨θ, hθ⟩
    exact hne θ (by simpa using hθ)
  obtain ⟨𝔮, h𝔮, hI𝔮⟩ := Ideal.exists_le_maximal I ((Ideal.ne_top_iff_one I).mpr hI)
  have hker : RingHom.ker (algebraMap (𝓞 F) (𝓞 K)) ≤ 𝔮 := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    have h1 : algebraMap F K (algebraMap (𝓞 F) F x) = algebraMap F K (algebraMap (𝓞 F) F 0) := by
      rw [← hcompat, hx, map_zero, map_zero, map_zero]
    have h2 := IsFractionRing.injective (𝓞 F) F ((algebraMap F K).injective h1)
    rw [h2]
    exact 𝔮.zero_mem
  obtain ⟨P, hP, hP𝔮⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K) 𝔮 hker
  obtain ⟨a, t, ht, hat⟩ := hK.2.2 P hP
  have hta : star (algebraMap (𝓞 K) K t) = algebraMap (𝓞 K) K a := by rw [ht, star_star]
  have hdfix : star ((algebraMap (𝓞 K) K a - algebraMap (𝓞 K) K t) ^ 2) =
      (algebraMap (𝓞 K) K a - algebraMap (𝓞 K) K t) ^ 2 := by
    rw [star_pow, star_sub, ← ht, hta]
    ring
  obtain ⟨f, hf⟩ := (hF _).mp hdfix
  have hfi : IsIntegral ℤ f := by
    rw [← isIntegral_algebraMap_iff (A := F) (B := K) , hf]
    have := NumberField.RingOfIntegers.isIntegral_coe ((a - t) ^ 2)
    simpa using this
  let fO : 𝓞 F := ⟨f, hfi⟩
  have hfI : fO ∈ I := by
    refine ⟨a * (a - t), ?_⟩
    show algebraMap (𝓞 K) K (a * (a - t)) + star (algebraMap (𝓞 K) K (a * (a - t))) =
      algebraMap F K f
    rw [hf]
    simp only [map_mul, map_sub, star_mul', star_sub, ← ht, hta]
    ring
  have hmem : algebraMap (𝓞 F) (𝓞 K) fO ∈ P := by
    rw [← Ideal.mem_under (𝓞 F) P, hP𝔮]
    exact hI𝔮 hfI
  have heq : algebraMap (𝓞 F) (𝓞 K) fO = (a - t) ^ 2 := by
    apply IsFractionRing.injective (𝓞 K) K
    rw [hcompat]
    show algebraMap F K f = _
    rw [hf]
    simp
  rw [heq] at hmem
  exact hat (hP.isPrime.mem_of_pow_mem 2 hmem)

theorem mul_inv_mem_iff {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {A B : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {n : ℕ}
    {U W : V ≃ₗ[K] V} (hUA : U ∈ glSub A) (hUB : U ∈ glSub B) (hWA : W ∈ glSub A) (hWB : W ∈ glSub B) :
    U * W⁻¹ ∈ sSub h B 𝔭 n ⊓ glSub A ↔ IA.phi h U - IA.phi h W ∈ hermL B 𝔭 n := by
  have eW : ∀ z : V, W (W⁻¹ z) = z := fun z => by
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]
    rfl
  have eW' : ∀ z : V, W⁻¹ (W z) = z := fun z => by
    rw [← LinearEquiv.mul_apply, inv_mul_cancel]
    rfl
  constructor
  · intro hX
    have hX' := (Subgroup.mem_inf.mp hX).1.2
    refine ⟨fun x y => ?_, fun x hx y hy => ?_⟩
    · simp only [AddSubgroupClass.coe_sub, LinearMap.sub_apply, star_sub, IA.star_phi hs]
    · have := hX' (W x) (apply_mem hWB hx) (W y) (apply_mem hWB hy)
      simp only [LinearEquiv.mul_apply, eW'] at this
      simpa only [LinearMap.sub_apply, IA.phi_apply, sub_sub_sub_cancel_right] using this
  · intro hZ
    refine Subgroup.mem_inf.mpr ⟨⟨mul_mem hUB (inv_mem hWB), fun x hx y hy => ?_⟩,
      mul_mem hUA (inv_mem hWA)⟩
    have := hZ.2 (W⁻¹ x) (apply_mem (inv_mem hWB) hx) (W⁻¹ y) (apply_mem (inv_mem hWB) hy)
    simp only [LinearMap.sub_apply, IA.phi_apply, sub_sub_sub_cancel_right, eW] at this
    simpa only [LinearEquiv.mul_apply] using this

theorem exists_newton (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsFullLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {B₀ : Submodule (𝓞 K) V}
    (hB₀ : Submodule.IsFullLattice K B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {r r' e : ℕ}
    (hr : extP K 𝔭 ^ r • locF 𝔭 A₀ ≤ locF 𝔭 B₀) (hr' : extP K 𝔭 ^ r' • locF 𝔭 B₀ ≤ locF 𝔭 A₀)
    (he : ∀ (k : ℕ) (x : V), (∀ y ∈ locF 𝔭 A₀, h y x ∈ pK K 𝔭 (k + e)) → x ∈ extP K 𝔭 ^ k • locF 𝔭 A₀)
    {k c : ℕ} (hk : c + 2 * e + 2 * r' + r + r' + 1 ≤ k) {Z : V →ₗ⋆[K] V →ₗ[K] K}
    (hZ : Z ∈ hermL (locF 𝔭 A₀) 𝔭 k) :
    ∃ X ∈ sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀), IA.phi h X - Z ∈ hermL (locF 𝔭 B₀) 𝔭 (k + c) := by
  have hsym : ∀ a b : V, star (h a b) = h b a := by
    intro a b
    exact hs.eq a b
  obtain ⟨θ₀, hθ1⟩ := exists_int_add_star_eq_one_of_isCMUnram hK hF
  set θ : K := algebraMap (𝓞 K) K θ₀ with hθdef
  obtain ⟨Y0, hY0⟩ := IA.exists_adj hs (nondegenerate hd) Z
  set Y : V →ₗ[K] V := θ • Y0 with hYdef
  have hhY : ∀ x y, h x (Y y) = θ * Z x y := by
    intro x y
    rw [hYdef, LinearMap.smul_apply, map_smul, hY0, smul_eq_mul]
  have hYh : ∀ x y, h (Y x) y = star θ * Z x y := by
    intro x y
    rw [← hsym y (Y x), hhY, star_mul', hZ.1 y x]

  have hYA : ∀ x ∈ locF 𝔭 A₀, Y x ∈ extP K 𝔭 ^ (k - e) • locF 𝔭 A₀ := by
    intro x hx
    refine he (k - e) (Y x) fun y hy => ?_
    rw [hhY, show k - e + e = k by omega, hθdef, ← Algebra.smul_def]
    exact (pK K 𝔭 k).smul_mem θ₀ (hZ.2 y hy x hx)
  have hDA : Y ∈ endL (locF 𝔭 A₀) (extP K 𝔭 • locF 𝔭 A₀) := fun x hx =>
    Submodule.smul_mono_left (Ideal.pow_le_self (by omega)) (hYA x hx)
  obtain ⟨X, hXeq, hXA⟩ := exists_equiv_of_mem_endL hA₀ h𝔭 hDA
  have hYB := IA.end_scale h𝔭 hr hr' Y (n := 1) (m := k - e) (by omega) hYA
  have hDB : Y ∈ endL (locF 𝔭 B₀) (extP K 𝔭 • locF 𝔭 B₀) := fun x hx => by
    simpa only [pow_one] using hYB x hx
  obtain ⟨X', hX'eq, hX'B⟩ := exists_equiv_of_mem_endL hB₀ h𝔭 hDB
  have hXX : X = X' := LinearEquiv.ext fun x => by rw [hXeq, hX'eq]
  have hphi : ∀ x y, IA.phi h X x y - Z x y = h (Y x) (Y y) := by
    intro x y
    rw [IA.phi_apply, hXeq, hXeq]
    simp only [map_add (f := _), LinearMap.add_apply]
    rw [hhY, hYh]
    linear_combination (Z x y) * hθ1
  have hYY : ∀ x ∈ locF 𝔭 A₀, ∀ y ∈ locF 𝔭 A₀, h (Y x) (Y y) ∈ pK K 𝔭 ((k - e) + (k - e)) :=
    fun x hx y hy => form_mem_pK hF hA₀i h𝔭 (hYA x hx) (hYA y hy)
  refine ⟨X, Subgroup.mem_inf.mpr ⟨mem_sSub.mpr ⟨hXA, fun x hx y hy => ?_⟩, hXX ▸ hX'B⟩, ?_, ?_⟩
  · have e1 : h (X x) (X y) - h x y = Z x y + h (Y x) (Y y) := by
      rw [← IA.phi_apply]
      linear_combination hphi x y
    rw [e1]
    exact add_mem (hZ.2 x hx y hy) (pK_anti 𝔭 (by omega) (hYY x hx y hy))
  · intro x y
    simp only [LinearMap.sub_apply, star_sub, IA.star_phi hs, hZ.1]
  · refine IA.sesq_scale hF h𝔭 hr' (IA.phi h X - Z) (n := k + c) (m := (k - e) + (k - e))
      (by omega) ?_
    intro x hx y hy
    rw [LinearMap.sub_apply, LinearMap.sub_apply, hphi]
    exact hYY x hx y hy

theorem relIndex_sSub_inf_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsFullLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {B₀ : Submodule (𝓞 K) V}
    (hB₀ : Submodule.IsFullLattice K B₀) (hB₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ c₀ : ℕ, ∀ c ≥ c₀, ∃ k₀ : ℕ, ∀ k ≥ k₀,
      sSub h (locF 𝔭 B₀) 𝔭 (k + c) ⊓ glSub (locF 𝔭 A₀) ≤ sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀) ∧
      sesqL (locF 𝔭 B₀) 𝔭 (k + c) ≤ sesqL (locF 𝔭 A₀) 𝔭 k ∧
      (sSub h (locF 𝔭 B₀) 𝔭 (k + c) ⊓ glSub (locF 𝔭 A₀)).relIndex
          (sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀)) =
        (hermL (locF 𝔭 B₀) 𝔭 (k + c)).relIndex (hermL (locF 𝔭 A₀) 𝔭 k) := by
  obtain ⟨r, hr⟩ := exists_smul_le hA₀.toIsLattice hB₀ h𝔭
  obtain ⟨r', hr'⟩ := exists_smul_le hB₀.toIsLattice hA₀ h𝔭
  obtain ⟨e, he⟩ := exists_dual_bound hK hF hs hd hA₀ h𝔭
  refine ⟨2 * r, fun c hc => ⟨c + 2 * e + 2 * r' + r + r' + 1, fun k hk => ?_⟩⟩

  have hGA : ∀ {X : V ≃ₗ[K] V}, X ∈ sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀) →
      X ∈ glSub (locF 𝔭 A₀) ∧ X ∈ glSub (locF 𝔭 B₀) := fun hX =>
    ⟨(mem_sSub.mp (Subgroup.mem_inf.mp hX).1).1, (Subgroup.mem_inf.mp hX).2⟩
  have hphiA : ∀ {X : V ≃ₗ[K] V}, X ∈ sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀) →
      IA.phi h X ∈ hermL (locF 𝔭 A₀) 𝔭 k := by
    intro X hX
    refine ⟨fun x y => IA.star_phi hs X x y, fun x hx y hy => ?_⟩
    rw [IA.phi_apply]
    exact (mem_sSub.mp (Subgroup.mem_inf.mp hX).1).2 x hx y hy
  have hsesq : sesqL (locF 𝔭 B₀) 𝔭 (k + c) ≤ sesqL (locF 𝔭 A₀) 𝔭 k := fun s hs' =>
    IA.sesq_scale hF h𝔭 hr s (n := k) (m := k + c) (by omega) hs'
  have hHG : sSub h (locF 𝔭 B₀) 𝔭 (k + c) ⊓ glSub (locF 𝔭 A₀) ≤
      sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀) := by
    intro X hX
    obtain ⟨hXB, hXA⟩ := Subgroup.mem_inf.mp hX
    obtain ⟨hXBgl, hXBv⟩ := mem_sSub.mp hXB
    refine Subgroup.mem_inf.mpr ⟨mem_sSub.mpr ⟨hXA, fun x hx y hy => ?_⟩, hXBgl⟩
    have := IA.sesq_scale hF h𝔭 hr (IA.phi h X) (n := k) (m := k + c) (by omega)
      (fun x hx y hy => by rw [IA.phi_apply]; exact hXBv x hx y hy) x hx y hy
    rwa [IA.phi_apply] at this
  refine ⟨hHG, hsesq, ?_⟩
  set G := sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀) with hGdef
  set H := sSub h (locF 𝔭 B₀) 𝔭 (k + c) ⊓ glSub (locF 𝔭 A₀) with hHdef
  set HA := hermL (locF 𝔭 A₀) 𝔭 k with hHAdef
  set HB := hermL (locF 𝔭 B₀) 𝔭 (k + c) with hHBdef

  have key : ∀ X Y : G, (QuotientGroup.mk X : G ⧸ H.subgroupOf G) = QuotientGroup.mk Y ↔
      IA.phi h (X : V ≃ₗ[K] V)⁻¹ - IA.phi h (Y : V ≃ₗ[K] V)⁻¹ ∈ HB := by
    intro X Y
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hX := hGA (inv_mem X.2)
    have hY := hGA (inv_mem Y.2)
    have := mul_inv_mem_iff hs (𝔭 := 𝔭) (n := k + c) hX.1 hX.2 hY.1 hY.2
    rw [inv_inv] at this
    rw [← this]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    try exact Iff.rfl
  have hmk : ∀ X : G, IA.phi h (X : V ≃ₗ[K] V)⁻¹ ∈ HA := fun X => hphiA (inv_mem X.2)
  have keyA : ∀ a b : HA, (QuotientAddGroup.mk a : HA ⧸ HB.addSubgroupOf HA) = QuotientAddGroup.mk b ↔
      (a : V →ₗ⋆[K] V →ₗ[K] K) - b ∈ HB := by
    intro a b
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add,
      AddSubgroup.coe_neg]
    constructor
    · intro hab
      have := HB.neg_mem hab
      rwa [neg_add_eq_sub, neg_sub] at this
    · intro hab
      have := HB.neg_mem hab
      rwa [neg_sub, sub_eq_neg_add] at this
  let f : G ⧸ H.subgroupOf G → HA ⧸ HB.addSubgroupOf HA :=
    Quotient.lift (fun X : G => (QuotientAddGroup.mk ⟨_, hmk X⟩ : HA ⧸ HB.addSubgroupOf HA))
      (fun X Y hXY => (keyA _ _).mpr ((key X Y).mp (Quotient.sound hXY)))
  have hinj : Function.Injective f := by
    intro q₁ q₂
    induction q₁ using QuotientGroup.induction_on with
    | H X =>
    induction q₂ using QuotientGroup.induction_on with
    | H Y =>
    intro hXY
    exact (key X Y).mpr ((keyA _ _).mp hXY)
  have hsurj : Function.Surjective f := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H Z =>
    obtain ⟨X, hXG, hXZ⟩ := exists_newton hK hF hs hd hA₀ hA₀i hB₀ h𝔭 hr hr' he (c := c) (k := k)
      (by omega) Z.2
    refine ⟨QuotientGroup.mk ⟨X⁻¹, inv_mem hXG⟩, ?_⟩
    show (QuotientAddGroup.mk ⟨_, hmk ⟨X⁻¹, inv_mem hXG⟩⟩ : HA ⧸ HB.addSubgroupOf HA) =
      QuotientAddGroup.mk Z
    rw [keyA]
    simpa only [inv_inv] using hXZ
  show Nat.card (G ⧸ H.subgroupOf G) = Nat.card (HA ⧸ HB.addSubgroupOf HA)
  exact Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)

end Formalism.HermitianLattices.Ext.L3.D2
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CoeMemOfMemSmulTop
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.D2

theorem relIndex_eq_card_image {G α : Type*} [Group G] (H S : Subgroup G) (f : G → α)
    (hf : ∀ a ∈ S, ∀ b ∈ S, f a = f b ↔ a⁻¹ * b ∈ H) :
    H.relIndex S = Nat.card {c : α // ∃ a ∈ S, f a = c} := by
  classical
  show Nat.card (S ⧸ H.subgroupOf S) = _
  apply Nat.card_congr
  refine Equiv.ofBijective (fun q => Quotient.liftOn' q
    (fun a : S => (⟨f a, a, a.2, rfl⟩ : {c : α // ∃ a ∈ S, f a = c})) ?_) ⟨?_, ?_⟩
  · intro a b hab
    apply Subtype.ext
    show f a = f b
    have hab' : a⁻¹ * b ∈ H.subgroupOf S := QuotientGroup.leftRel_apply.mp hab
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at hab'
    exact (hf a a.2 b b.2).mpr hab'
  · intro q₁ q₂ e
    induction q₁ using QuotientGroup.induction_on with
    | H a =>
    induction q₂ using QuotientGroup.induction_on with
    | H b =>
    have e' : f a = f b := congrArg Subtype.val e
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact (hf a a.2 b b.2).mp e'
  · rintro ⟨c, a, ha, rfl⟩
    exact ⟨QuotientGroup.mk ⟨a, ha⟩, rfl⟩

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem gmap_eq_iff (a b : V ≃ₗ[K] V) (B : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap a B = Formalism.HermitianLatticesTheory.gmap b B ↔ a⁻¹ * b ∈ glSub B := by
  rw [mem_glSub]
  constructor
  · intro e
    rw [autSub_gmap_mul, ← e, ← autSub_gmap_mul, inv_mul_cancel, autSub_gmap_one]
  · intro e
    rw [show b = a * (a⁻¹ * b) from (mul_inv_cancel_left a b).symm, autSub_gmap_mul a, e]

theorem autSub_le_sSub (h : V →ₗ⋆[K] V →ₗ[K] K) (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    autSub h A ≤ sSub h A 𝔭 k := fun X hX => ⟨hX.2, fun x _ y _ => by
  rw [hX.1 x y, sub_self]
  exact Submodule.zero_mem _⟩

theorem coe_mem_of_mem_smul_top (I : Ideal (𝓞 K)) (A : Submodule (𝓞 K) V) {u : ↥A}
    (hu : u ∈ (I • ⊤ : Submodule (𝓞 K) ↥A)) : (u : V) ∈ I • A := by
  have h2 := Submodule.mem_map_of_mem (f := A.subtype) hu
  rwa [Submodule.map_smul'', Submodule.map_subtype_top] at h2

theorem exists_autSub_mul_nSub (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsFullLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {k : ℕ} (hk : eA h (locF 𝔭 A₀) 𝔭 + 1 ≤ k) {X : V ≃ₗ[K] V}
    (hX : X ∈ sSub h (locF 𝔭 A₀) 𝔭 k) :
    ∃ g ∈ autSub h (locF 𝔭 A₀), g⁻¹ * X ∈ nSub (locF 𝔭 A₀) 𝔭 (k - eA h (locF 𝔭 A₀) 𝔭) := by
  obtain ⟨hXg, hXh⟩ := hX
  set A := locF 𝔭 A₀ with hA
  let f : ↥A →ₗ[𝓞 K] ↥A :=
    (((X : V →ₗ[K] V).restrictScalars (𝓞 K)).domRestrict A).codRestrict A
      (fun x => apply_mem hXg x.2)
  have hf : ∀ x : ↥A, ((f x : ↥A) : V) = X x := fun x => rfl
  let Xb : Module.End (𝓞 K) (↥A ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A)) :=
    Submodule.mapQ _ _ f (Submodule.smul_top_le_comap_smul_top _ f)
  have key : ∀ x x' : ↥A, Submodule.Quotient.mk x' = Xb (Submodule.Quotient.mk x) →
      (x' : V) - X x ∈ extP K 𝔭 ^ k • A := by
    intro x x' hx
    have h1 : x' - f x ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A) := by
      rw [← Submodule.Quotient.eq]
      exact hx
    exact coe_mem_of_mem_smul_top _ _ h1
  have h0 : ∀ {z : V}, z ∈ A → z ∈ extP K 𝔭 ^ 0 • A := fun hz => by rwa [pow_zero_smul]
  let := hA₀
  obtain ⟨g, hg, hgX⟩ := exists_isom_lift hK hF hs hd (A₀ := A₀) inferInstance hA₀i h𝔭 hk Xb (by
    intro x y x' y' hx hy
    rw [congrP_algebraMap_iff_sub_mem h𝔭]
    have hu := key x x' hx
    have hv := key y y' hy
    have e1 : h (x' : V) (y' : V) - h (x : V) (y : V) =
        (h (X x) (X y) - h (x : V) (y : V)) + h ((x' : V) - X x) (y' : V)
          + h (X x) ((y' : V) - X y) := by
      simp only [map_sub, LinearMap.sub_apply]
      ring
    rw [e1]
    refine add_mem (add_mem (hXh x x.2 y y.2) ?_) ?_
    · simpa using form_mem_pK hF hA₀i h𝔭 hu (h0 y'.2)
    · simpa using form_mem_pK hF hA₀i h𝔭 (h0 (apply_mem hXg x.2)) hv)
  refine ⟨g, hg, mul_mem (inv_mem hg.2) hXg, fun x hx => ?_⟩
  have h1 := hgX ⟨x, hx⟩ (f ⟨x, hx⟩) rfl
  have h2 := apply_mem_smul (inv_mem (show g ∈ glSub A from hg.2)) _ ((Submodule.neg_mem _ h1))
  have e : ∀ z : V, g⁻¹ (g z) = z := fun z => by
    rw [← mul_apply_eq_comp, inv_mul_cancel]
    rfl
  simpa [e, hf] using h2

theorem relIndex_inf_glSub (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsFullLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {B₀ : Submodule (𝓞 K) V}
    (hB₀ : Submodule.IsFullLattice K B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, (sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀)).relIndex (sSub h (locF 𝔭 A₀) 𝔭 k) =
      orbCount h (locF 𝔭 A₀) (locF 𝔭 B₀) := by
  let := hA₀
  let := hB₀
  obtain ⟨k₁, hk₁⟩ := nSub_le_glSub (A₀ := A₀) (B₀ := B₀) inferInstance inferInstance h𝔭
  refine ⟨eA h (locF 𝔭 A₀) 𝔭 + 1 + k₁, fun k hk => ?_⟩
  rw [Subgroup.inf_relIndex_left,
    relIndex_eq_card_image _ _ (fun X => Formalism.HermitianLatticesTheory.gmap X (locF 𝔭 B₀))
      (fun a _ b _ => gmap_eq_iff a b _)]
  unfold orbCount
  refine Nat.card_congr (Equiv.subtypeEquivRight fun C => ⟨?_, ?_⟩)
  · rintro ⟨X, hX, rfl⟩
    obtain ⟨g, hg, hY⟩ := exists_autSub_mul_nSub hK hF hs hd hA₀ hA₀i h𝔭 (by omega) hX
    exact ⟨g, hg.1, hg.2, (gmap_eq_iff g X _).2 (hk₁ _ (by omega) hY)⟩
  · rintro ⟨g, hg, hgA, rfl⟩
    exact ⟨g, autSub_le_sSub h _ 𝔭 k ⟨hg, hgA⟩, rfl⟩

end Formalism.HermitianLattices.Ext.L3.D2
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MemLocFOfSmulMem
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.D2

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

namespace RedC

theorem index_eq_card {G T : Type*} [Group G] (N : Subgroup G) (f : G → T) (hs : Function.Surjective f)
    (hf : ∀ a b, f a = f b ↔ a⁻¹ * b ∈ N) : N.index = Nat.card T := by
  first | exact Bl.general_b_fact_left_rest.goal1 .. | (apply Bl.general_b_fact_left_rest.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left_rest.goal1 <;> assumption)

def redEnd (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (k : ℕ) (X : V ≃ₗ[K] V) (hX : X ∈ glSub A) :
    Module.End (𝓞 K) (↥A ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A)) :=
  Submodule.mapQ _ _ (((X : V →ₗ[K] V).restrictScalars (𝓞 K)).restrict fun _ hx => apply_mem hX hx)
    (fun x hx => by
      rw [Submodule.mem_comap, Submodule.mem_smul_top_iff]
      rw [Submodule.mem_smul_top_iff] at hx
      exact apply_mem_smul hX _ hx)

theorem redEnd_mk (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (k : ℕ) (X : V ≃ₗ[K] V) (hX : X ∈ glSub A)
    (x : ↥A) : redEnd A 𝔭 k X hX (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨X x, apply_mem hX x.2⟩ := rfl

theorem mk_eq_redEnd_iff {A : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {k : ℕ} {X : V ≃ₗ[K] V}
    (hX : X ∈ glSub A) (x x' : ↥A) :
    Submodule.Quotient.mk x' = redEnd A 𝔭 k X hX (Submodule.Quotient.mk x) ↔
      (x' : V) - X x ∈ extP K 𝔭 ^ k • A := by
  rw [redEnd_mk, Submodule.Quotient.eq, Submodule.mem_smul_top_iff]
  rfl

theorem redEnd_eq_iff {A : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {k : ℕ} {a b : V ≃ₗ[K] V}
    (ha : a ∈ glSub A) (hb : b ∈ glSub A) :
    redEnd A 𝔭 k a ha = redEnd A 𝔭 k b hb ↔ a⁻¹ * b ∈ nSub A 𝔭 k := by
  have e : ∀ z : V, a⁻¹ (a z) = z := fun z => by
    rw [← LinearEquiv.mul_apply, inv_mul_cancel]
    rfl
  have e' : ∀ z : V, a (a⁻¹ z) = z := fun z => by
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]
    rfl
  constructor
  · intro hab
    refine ⟨mul_mem (inv_mem ha) hb, fun x hx => ?_⟩
    have h1 : Submodule.Quotient.mk (⟨b x, apply_mem hb hx⟩ : ↥A) =
        redEnd A 𝔭 k a ha (Submodule.Quotient.mk ⟨x, hx⟩) := by
      rw [hab, redEnd_mk]
    have h2 := apply_mem_smul (inv_mem ha) _ ((mk_eq_redEnd_iff ha _ _).1 h1)
    simpa [e] using h2
  · rintro ⟨-, hab⟩
    refine LinearMap.ext fun q => ?_
    induction q using Submodule.Quotient.induction_on with | _ x => ?_
    symm
    rw [redEnd_mk, mk_eq_redEnd_iff]
    have h2 := apply_mem_smul ha _ (hab x x.2)
    simpa [e'] using h2

theorem redEnd_cond (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {A₀ : Submodule (𝓞 K) V}
    (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {k : ℕ} {X : V ≃ₗ[K] V}
    (hX : X ∈ sSub h (locF 𝔭 A₀) 𝔭 k) (x y x' y' : ↥(locF 𝔭 A₀))
    (hx : Submodule.Quotient.mk x' = redEnd (locF 𝔭 A₀) 𝔭 k X hX.1 (Submodule.Quotient.mk x))
    (hy : Submodule.Quotient.mk y' = redEnd (locF 𝔭 A₀) 𝔭 k X hX.1 (Submodule.Quotient.mk y)) :
    CongrP 𝔭 k (h (x' : V) (y' : V)) (h (x : V) (y : V)) := by
  rw [congrP_algebraMap_iff_sub_mem h𝔭]
  rw [mk_eq_redEnd_iff] at hx hy
  have z : ∀ w ∈ locF 𝔭 A₀, w ∈ extP K 𝔭 ^ 0 • locF 𝔭 A₀ := fun w hw => by rwa [pow_zero_smul]
  have h1 := hX.2 x x.2 y y.2
  have h2 := form_mem_pK hF hA₀i h𝔭 hx (z _ y'.2)
  have h3 := form_mem_pK hF hA₀i h𝔭 (z _ (apply_mem hX.1 x.2)) hy
  rw [add_zero] at h2
  rw [zero_add] at h3
  have h4 := add_mem (add_mem h1 h2) h3
  have e : h (x' : V) (y' : V) - h (x : V) (y : V) =
      h (X x) (X y) - h (x : V) (y : V) + h ((x' : V) - X x) (y' : V) + h (X x) ((y' : V) - X y) := by
    simp only [map_sub, LinearMap.sub_apply]
    abel
  rw [e]
  exact h4

theorem mem_smul_of_smul_mem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (A : Submodule (𝓞 K) V) (k : ℕ)
    {t : 𝓞 F} (ht : t ∉ 𝔭) {v : V} (hv : v ∈ A)
    (h : algebraMap (𝓞 F) (𝓞 K) t • v ∈ extP K 𝔭 ^ k • A) : v ∈ extP K 𝔭 ^ k • A := by
  obtain ⟨u, hu⟩ := MeanA.exists_mul_sub_one_mem_pow h𝔭 ht k
  have : v = algebraMap (𝓞 F) (𝓞 K) u • (algebraMap (𝓞 F) (𝓞 K) t • v) -
      algebraMap (𝓞 F) (𝓞 K) (u * t - 1) • v := by
    rw [map_sub, map_mul, map_one, sub_smul, mul_smul, one_smul]; abel
  rw [this]
  exact sub_mem (Submodule.smul_mem _ _ h) (Submodule.smul_mem_smul (localizedQuotients.ι_mem_pow hu) hv)

theorem mem_locF_of_smul_mem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (A₀ : Submodule (𝓞 K) V)
    {t : 𝓞 F} (ht : t ∉ 𝔭) {v : V} (h : algebraMap (𝓞 F) (𝓞 K) t • v ∈ locF 𝔭 A₀) : v ∈ locF 𝔭 A₀ := by
  have := h𝔭.isPrime
  obtain ⟨s, hs, h1⟩ := (LocalSpans.mem_locF 𝔭 A₀ _).1 h
  refine (LocalSpans.mem_locF 𝔭 A₀ _).2 ⟨s * t, fun h => (h𝔭.isPrime.mem_or_mem h).elim hs ht, ?_⟩
  rwa [map_mul, mul_smul]

theorem exists_lift {A₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsFullLattice K A₀) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (k : ℕ)
    (Y : Module.End (𝓞 K) (↥(locF 𝔭 A₀) ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 A₀)))) :
    ∃ D : V →ₗ[K] V, ∀ x : ↥(locF 𝔭 A₀), ∃ hD : D x ∈ locF 𝔭 A₀,
      Submodule.Quotient.mk (⟨D x, hD⟩ : ↥(locF 𝔭 A₀)) = Y (Submodule.Quotient.mk x) := by
  have := h𝔭.isPrime
  obtain ⟨b, -, hb⟩ := LocalSpans.exists_basis_locF hA₀ h𝔭
  have hsp : Submodule.span (𝓞 K) (Set.range b) ≤ locF 𝔭 A₀ := hb ▸ localizedQuotients.le_locF 𝔭 _
  have hbA : ∀ i, b i ∈ locF 𝔭 A₀ := fun i => hsp (Submodule.subset_span ⟨i, rfl⟩)
  choose c hc using fun i => Submodule.Quotient.mk_surjective _ (Y (Submodule.Quotient.mk ⟨b i, hbA i⟩))
  let D : V →ₗ[K] V := b.constr K fun i => (c i : V)
  have hDb : ∀ i, D (b i) = c i := fun i => b.constr_basis K _ i
  have key : ∀ y ∈ Submodule.span (𝓞 K) (Set.range b), ∃ (hy : y ∈ locF 𝔭 A₀) (hD : D y ∈ locF 𝔭 A₀),
      Submodule.Quotient.mk (⟨D y, hD⟩ : ↥(locF 𝔭 A₀)) = Y (Submodule.Quotient.mk ⟨y, hy⟩) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      refine ⟨hbA i, by rw [hDb]; exact (c i).2, ?_⟩
      rw [← hc i]
      congr 1
      exact Subtype.ext (hDb i)
    | zero =>
      refine ⟨zero_mem _, by rw [map_zero]; exact zero_mem _, ?_⟩
      have e1 : (⟨D 0, by rw [map_zero]; exact zero_mem _⟩ : ↥(locF 𝔭 A₀)) = 0 := Subtype.ext (map_zero D)
      have e2 : (⟨0, zero_mem _⟩ : ↥(locF 𝔭 A₀)) = 0 := rfl
      rw [e1, e2, Submodule.Quotient.mk_zero, map_zero]
    | add y z _ _ h1 h2 =>
      obtain ⟨hy, hDy, e1⟩ := h1
      obtain ⟨hz, hDz, e2⟩ := h2
      refine ⟨add_mem hy hz, by rw [map_add]; exact add_mem hDy hDz, ?_⟩
      have e3 : (⟨D (y + z), by rw [map_add]; exact add_mem hDy hDz⟩ : ↥(locF 𝔭 A₀)) =
          ⟨D y, hDy⟩ + ⟨D z, hDz⟩ := Subtype.ext (map_add D y z)
      have e4 : (⟨y + z, add_mem hy hz⟩ : ↥(locF 𝔭 A₀)) = ⟨y, hy⟩ + ⟨z, hz⟩ := rfl
      rw [e3, e4, Submodule.Quotient.mk_add, Submodule.Quotient.mk_add, map_add (f := _), e1, e2]
    | smul a y _ h1 =>
      obtain ⟨hy, hDy, e1⟩ := h1
      have hs : D (a • y) = a • D y := LinearMap.map_smul_of_tower D a y
      refine ⟨Submodule.smul_mem _ a hy, by rw [hs]; exact Submodule.smul_mem _ a hDy, ?_⟩
      have e3 : (⟨D (a • y), by rw [hs]; exact Submodule.smul_mem _ a hDy⟩ : ↥(locF 𝔭 A₀)) =
          a • ⟨D y, hDy⟩ := Subtype.ext hs
      have e4 : (⟨a • y, Submodule.smul_mem _ a hy⟩ : ↥(locF 𝔭 A₀)) = a • ⟨y, hy⟩ := rfl
      rw [e3, e4, Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul, map_smul, e1]
  refine ⟨D, fun x => ?_⟩
  have hx : (x : V) ∈ locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) := by rw [hb]; exact x.2
  obtain ⟨t, ht, hxt⟩ := (LocalSpans.mem_locF 𝔭 _ _).1 hx
  obtain ⟨hy, hDy, e1⟩ := key _ hxt
  have hs : D (algebraMap (𝓞 F) (𝓞 K) t • (x : V)) = algebraMap (𝓞 F) (𝓞 K) t • D x :=
    LinearMap.map_smul_of_tower D _ _
  have hDx : D x ∈ locF 𝔭 A₀ := mem_locF_of_smul_mem h𝔭 A₀ ht (hs ▸ hDy)
  refine ⟨hDx, ?_⟩
  obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ (Y (Submodule.Quotient.mk x))
  rw [← hw, Submodule.Quotient.eq, Submodule.mem_smul_top_iff]
  have e4 : (⟨algebraMap (𝓞 F) (𝓞 K) t • (x : V), hy⟩ : ↥(locF 𝔭 A₀)) = algebraMap (𝓞 F) (𝓞 K) t • x := rfl
  rw [e4, Submodule.Quotient.mk_smul, Y.map_smul, ← hw, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq,
    Submodule.mem_smul_top_iff] at e1
  refine mem_smul_of_smul_mem h𝔭 _ k ht (sub_mem hDx w.2) ?_
  have e5 : algebraMap (𝓞 F) (𝓞 K) t • (D x - (w : V)) =
      D (algebraMap (𝓞 F) (𝓞 K) t • (x : V)) - algebraMap (𝓞 F) (𝓞 K) t • (w : V) := by
    rw [hs, smul_sub]
  show algebraMap (𝓞 F) (𝓞 K) t • (D x - (w : V)) ∈ _
  rw [e5]
  exact e1

theorem exists_redEnd_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsFullLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {k : ℕ} (hk : eA h (locF 𝔭 A₀) 𝔭 + 1 ≤ k)
    (Y : Module.End (𝓞 K) (↥(locF 𝔭 A₀) ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 A₀))))
    (hY : ∀ x y x' y' : ↥(locF 𝔭 A₀), Submodule.Quotient.mk x' = Y (Submodule.Quotient.mk x) →
      Submodule.Quotient.mk y' = Y (Submodule.Quotient.mk y) →
      CongrP 𝔭 k (h (x' : V) (y' : V)) (h (x : V) (y : V))) :
    ∃ (X : V ≃ₗ[K] V) (hX : X ∈ sSub h (locF 𝔭 A₀) 𝔭 k), redEnd (locF 𝔭 A₀) 𝔭 k X hX.1 = Y := by
  obtain ⟨g, hg, hgY⟩ := exists_isom_lift hK hF hs hd (by first | exact hA₀ | exact hA₀.toIsLattice) hA₀i h𝔭 hk Y hY
  have hgA : g ∈ glSub (locF 𝔭 A₀) := hg.2
  obtain ⟨D, hD⟩ := exists_lift hA₀ h𝔭 k Y
  have hle : extP K 𝔭 ^ (k - eA h (locF 𝔭 A₀) 𝔭) • locF 𝔭 A₀ ≤ extP K 𝔭 • locF 𝔭 A₀ :=
    Submodule.smul_mono_left (Ideal.pow_le_self (by omega))
  let E : V →ₗ[K] V := (g⁻¹ : V ≃ₗ[K] V).toLinearMap ∘ₗ D - LinearMap.id
  have hE : E ∈ endL (locF 𝔭 A₀) (extP K 𝔭 • locF 𝔭 A₀) := by
    intro x hx
    obtain ⟨hDx, h1⟩ := hD ⟨x, hx⟩
    have h2 := apply_mem_smul (inv_mem hgA) _ (hle (hgY ⟨x, hx⟩ ⟨D x, hDx⟩ h1))
    have h3 := neg_mem h2
    have e3 : E x = -(g⁻¹ (g x - D x)) := by
      simp [E]
    rw [e3]
    exact h3
  obtain ⟨Z, hZ, hZA⟩ := exists_equiv_of_mem_endL hA₀ h𝔭 hE
  have hXD : ∀ x, (g * Z) x = D x := fun x => by
    rw [LinearEquiv.mul_apply, hZ]
    simp [E]
  have hXA : g * Z ∈ glSub (locF 𝔭 A₀) := mul_mem hgA hZA
  have hmk : ∀ x : ↥(locF 𝔭 A₀), Submodule.Quotient.mk (⟨(g * Z) x, apply_mem hXA x.2⟩ : ↥(locF 𝔭 A₀)) =
      Y (Submodule.Quotient.mk x) := fun x => by
    obtain ⟨hDx, h1⟩ := hD x
    rw [← h1]
    congr 1
    exact Subtype.ext (hXD x)
  refine ⟨g * Z, ⟨hXA, fun x hx y hy => ?_⟩, ?_⟩
  · exact (congrP_algebraMap_iff_sub_mem h𝔭).1 (hY ⟨x, hx⟩ ⟨y, hy⟩ _ _ (hmk ⟨x, hx⟩) (hmk ⟨y, hy⟩))
  · refine LinearMap.ext fun q => ?_
    induction q using Submodule.Quotient.induction_on with | _ x => ?_
    rw [redEnd_mk]
    exact hmk x

end RedC

theorem alphaL_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsFullLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, alphaL h (locF 𝔭 A₀) 𝔭 =
      (akCount h (locF 𝔭 A₀) 𝔭 k : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ (k * finrank K V ^ 2) := by
  refine ⟨2 * vd h A₀ 𝔭 + 1, fun k hk => ?_⟩
  have h1 : alphaL h (locF 𝔭 A₀) 𝔭 = alphaL h A₀ 𝔭 := by
    unfold alphaL
    simp_rw [akCount_locF hF h A₀ 𝔭 h𝔭]
  rw [h1, akCount_locF hF h A₀ 𝔭 h𝔭]
  exact firstFamilyOperatorEnd.alphaL_eq hK hF hs hd hA₀ hA₀i h𝔭 hk

theorem akCount_eq_relIndex (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsFullLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, akCount h (locF 𝔭 A₀) 𝔭 k =
      (nSub (locF 𝔭 A₀) 𝔭 k).relIndex (sSub h (locF 𝔭 A₀) 𝔭 k) := by
  refine ⟨eA h (locF 𝔭 A₀) 𝔭 + 1, fun k hk => ?_⟩
  symm
  unfold akCount Subgroup.relIndex
  refine RedC.index_eq_card _
    (fun X : ↥(sSub h (locF 𝔭 A₀) 𝔭 k) => ⟨RedC.redEnd (locF 𝔭 A₀) 𝔭 k X.1 X.2.1,
      RedC.redEnd_cond hF hA₀i h𝔭 X.2⟩) ?_ ?_
  · rintro ⟨Y, hY⟩
    obtain ⟨X, hX, e⟩ := RedC.exists_redEnd_eq hK hF hs hd hA₀ hA₀i h𝔭 hk Y hY
    exact ⟨⟨X, hX⟩, Subtype.ext e⟩
  · intro a b
    rw [Subtype.mk.injEq, RedC.redEnd_eq_iff, Subgroup.mem_subgroupOf]
    rfl

end Formalism.HermitianLattices.Ext.L3.D2
end
end

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.D2

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem relIndex_sSub_inf (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsFullLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {B₀ : Submodule (𝓞 K) V}
    (hB₀ : Submodule.IsFullLattice K B₀) (hB₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ c₀ : ℕ, ∀ c ≥ c₀, ∃ k₀ : ℕ, ∀ k ≥ k₀,
      sSub h (locF 𝔭 B₀) 𝔭 (k + c) ⊓ glSub (locF 𝔭 A₀) ≤ sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀) ∧
      (sSub h (locF 𝔭 B₀) 𝔭 (k + c) ⊓ glSub (locF 𝔭 A₀)).relIndex
          (sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀)) *
          Ideal.absNorm 𝔭 ^ (finrank K V * vd h (locF 𝔭 B₀) 𝔭) =
        Ideal.absNorm 𝔭 ^ (finrank K V ^ 2 * c + finrank K V * vd h (locF 𝔭 A₀) 𝔭) := by
  obtain ⟨c₀, hc₀⟩ := relIndex_sSub_inf_eq hK hF hs hd hA₀ hA₀i hB₀ hB₀i h𝔭
  refine ⟨c₀, fun c hc => ?_⟩
  obtain ⟨k₀, hk₀⟩ := hc₀ c hc
  refine ⟨k₀, fun k hk => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hk₀ k hk
  refine ⟨h1, ?_⟩
  rw [h3]
  exact relIndex_hermL hK hF hs hd (by first | exact hA₀ | exact hA₀.toIsLattice) hA₀i
    (by first | exact hB₀ | exact hB₀.toIsLattice) hB₀i h𝔭 h2

end Formalism.HermitianLattices.Ext.L3.D2

namespace Formalism.HermitianLattices.Ext.L3

open D2

theorem local_density_ratio_holds :
    ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K],
      Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F →
      ∀ (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
        [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (A₀ B₀ : Submodule (𝓞 K) V)
        (𝔭 : Ideal (𝓞 F)),
        h.IsSymm → IsTotPosDef h → 𝔭.IsMaximal → Submodule.IsFullLattice K A₀ →
        Submodule.IsFullLattice K B₀ → Formalism.HermitianLatticesTheory.IsIntegralLat h A₀ →
        Formalism.HermitianLatticesTheory.IsIntegralLat h B₀ →
        alphaL h (locF 𝔭 A₀) 𝔭 * (Ideal.absNorm 𝔭 : ℝ) ^ (finrank K V * vd h (locF 𝔭 B₀) 𝔭) *
            orbCount h (locF 𝔭 B₀) (locF 𝔭 A₀) =
          alphaL h (locF 𝔭 B₀) 𝔭 * (Ideal.absNorm 𝔭 : ℝ) ^ (finrank K V * vd h (locF 𝔭 A₀) 𝔭) *
            orbCount h (locF 𝔭 A₀) (locF 𝔭 B₀) := by
  intro K F _ _ _ _ _ _ hK hF V _ _ _ _ _ h A₀ B₀ 𝔭 hs hd h𝔭 hA₀ hB₀ hA₀i hB₀i
  obtain ⟨c₁, hc₁⟩ := D2.relIndex_sSub_inf hK hF hs hd hA₀ hA₀i hB₀ hB₀i h𝔭
  obtain ⟨c₂, hc₂⟩ := D2.relIndex_nSub hK hF hA₀ hB₀ h𝔭
  set c := c₁ + c₂ with hc
  obtain ⟨k₁, hk₁⟩ := hc₁ c (by omega)
  obtain ⟨k₂, hk₂⟩ := hc₂ c (by omega)
  obtain ⟨k₃, hk₃⟩ := D2.akCount_eq_relIndex hK hF hs hd (by first | exact hA₀ | exact hA₀.toIsLattice) hA₀i h𝔭
  obtain ⟨k₄, hk₄⟩ := D2.akCount_eq_relIndex hK hF hs hd (by first | exact hB₀ | exact hB₀.toIsLattice) hB₀i h𝔭
  obtain ⟨k₅, hk₅⟩ := D2.relIndex_inf_glSub hK hF hs hd hA₀ hA₀i hB₀ h𝔭
  obtain ⟨k₆, hk₆⟩ := D2.relIndex_inf_glSub hK hF hs hd hB₀ hB₀i hA₀ h𝔭
  obtain ⟨k₇, hk₇⟩ := D2.nSub_le_glSub hB₀ hA₀ h𝔭
  obtain ⟨k₈, hk₈⟩ := D2.alphaL_eq hK hF hs hd
    (by first | exact hA₀ | exact hA₀.toIsLattice) hA₀i h𝔭
  obtain ⟨k₉, hk₉⟩ := D2.alphaL_eq hK hF hs hd
    (by first | exact hB₀ | exact hB₀.toIsLattice) hB₀i h𝔭
  set k := k₁ + k₂ + k₃ + k₄ + k₅ + k₆ + k₇ + k₈ + k₉ with hk
  obtain ⟨hJI, hIJ⟩ := hk₁ k (by omega)
  obtain ⟨hNN, hNNi⟩ := hk₂ k (by omega)
  have hakA := hk₃ k (by omega)
  have hakB := hk₄ (k + c) (by omega)
  have horbAB := hk₅ k (by omega)
  have horbBA := hk₆ (k + c) (by omega)
  have hNBA := hk₇ (k + c) (by omega)
  have hαA := hk₈ k (by omega)
  have hαB := hk₉ (k + c) (by omega)
  have f1 := D2.nSub_le_sSub hF hA₀i h𝔭 k
  have f2 := D2.nSub_le_sSub hF hB₀i h𝔭 (k + c)
  have hNJ : nSub (locF 𝔭 B₀) 𝔭 (k + c) ≤ sSub h (locF 𝔭 B₀) 𝔭 (k + c) ⊓ glSub (locF 𝔭 A₀) :=
    le_inf f2 hNBA
  have hIS : sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀) ≤ sSub h (locF 𝔭 A₀) 𝔭 k := inf_le_left
  have hJS : sSub h (locF 𝔭 B₀) 𝔭 (k + c) ⊓ glSub (locF 𝔭 A₀) ≤ sSub h (locF 𝔭 B₀) 𝔭 (k + c) :=
    inf_le_left
  have e1 := Subgroup.relIndex_mul_relIndex (hHK := hNN) (hKL := f1)
  have e2 := Subgroup.relIndex_mul_relIndex (hHK := hNJ) (hKL := hJI)
  have e3 := Subgroup.relIndex_mul_relIndex (hHK := hNJ.trans hJI) (hKL := hIS)
  have e4 := Subgroup.relIndex_mul_relIndex (hHK := hNJ) (hKL := hJS)
  have e5 : (nSub (locF 𝔭 A₀) 𝔭 k).relIndex (sSub h (locF 𝔭 A₀) 𝔭 k) *
      (nSub (locF 𝔭 B₀) 𝔭 (k + c)).relIndex (nSub (locF 𝔭 A₀) 𝔭 k) =
      (nSub (locF 𝔭 B₀) 𝔭 (k + c)).relIndex (sSub h (locF 𝔭 B₀) 𝔭 (k + c) ⊓ glSub (locF 𝔭 A₀)) *
        ((sSub h (locF 𝔭 B₀) 𝔭 (k + c) ⊓ glSub (locF 𝔭 A₀)).relIndex
            (sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀)) *
          (sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀)).relIndex (sSub h (locF 𝔭 A₀) 𝔭 k)) := by
    rw [mul_comm, e1, ← e3, ← e2, mul_assoc]
  have E : akCount h (locF 𝔭 A₀) 𝔭 k * Ideal.absNorm 𝔭 ^ (2 * finrank K V ^ 2 * c) *
      Ideal.absNorm 𝔭 ^ (finrank K V * vd h (locF 𝔭 B₀) 𝔭) * orbCount h (locF 𝔭 B₀) (locF 𝔭 A₀) =
      akCount h (locF 𝔭 B₀) 𝔭 (k + c) * orbCount h (locF 𝔭 A₀) (locF 𝔭 B₀) *
        Ideal.absNorm 𝔭 ^ (finrank K V ^ 2 * c + finrank K V * vd h (locF 𝔭 A₀) 𝔭) := by
    rw [hakA, hakB, ← horbAB, ← horbBA, ← hNNi, ← hIJ, ← e4, e5]
    ring
  have hQ : (Ideal.absNorm 𝔭 : ℝ) ≠ 0 := by
    have hb : 𝔭 ≠ ⊥ :=
      Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)
    exact_mod_cast fun h0 => hb (Ideal.absNorm_eq_zero_iff.mp h0)
  have Er : (akCount h (locF 𝔭 A₀) 𝔭 k : ℝ) * (Ideal.absNorm 𝔭 : ℝ) ^ (2 * finrank K V ^ 2 * c) *
      (Ideal.absNorm 𝔭 : ℝ) ^ (finrank K V * vd h (locF 𝔭 B₀) 𝔭) *
        (orbCount h (locF 𝔭 B₀) (locF 𝔭 A₀) : ℝ) =
      (akCount h (locF 𝔭 B₀) 𝔭 (k + c) : ℝ) * (orbCount h (locF 𝔭 A₀) (locF 𝔭 B₀) : ℝ) *
        (Ideal.absNorm 𝔭 : ℝ) ^ (finrank K V ^ 2 * c + finrank K V * vd h (locF 𝔭 A₀) 𝔭) := by
    exact_mod_cast E
  rw [hαA, hαB, div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div,
    div_eq_div_iff (pow_ne_zero _ hQ) (pow_ne_zero _ hQ)]
  apply mul_right_cancel₀ (pow_ne_zero (finrank K V ^ 2 * c) hQ)
  linear_combination ((Ideal.absNorm 𝔭 : ℝ) ^ (k * finrank K V ^ 2)) * Er

end Formalism.HermitianLattices.Ext.L3
