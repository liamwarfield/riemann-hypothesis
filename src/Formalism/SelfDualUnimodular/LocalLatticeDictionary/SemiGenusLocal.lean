module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictZAbs

@[expose] public section

section -- merged from Formalism.SelfDualUnimodular.LocalLatticeDictionary.SelfDualRestr
section -- merged from Formalism.SelfDualUnimodular.LocalLatticeDictionary.ExistsUnitNorm
noncomputable section

open NumberField

namespace Formalism.L2.SG.Pf.LatDictZ.Z0.SGA

open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def InJ (p : Ideal (𝓞 K)) (a : K) : Prop :=
  ∃ r s : 𝓞 K, s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p ∧ r ∈ p ∧ r ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := K) p ∧
    a = algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s

theorem inJ_of_fixed {p : Ideal (𝓞 K)} (hp : p.IsPrime) {a : K} (ha : a ∈ locRing p) (hfix : star a = a)
    (hnu : ¬ IsUnitIn (locRing p) a) : InJ p a := by
  obtain ⟨r, s, hs, rfl⟩ := (mem_locR_iff hp a).1 ((mem_locRing p a).1 ha)
  have hr : r ∉ Formalism.HermitianLatticesTheory.hcompl (K := K) p := fun h => hnu ((isUnitIn_div_iff hp r hs).2 h)
  rw [mem_hcompl_iff hp] at hr
  have hs' := (mem_hcompl_iff hp s).1 hs
  have hcs := (mem_hcompl_iff hp _).1 (conjO_mem_hcompl hs)
  have hs0 := algebraMap_ne_zero_of_mem_hcompl hp hs
  have hcs0 := algebraMap_ne_zero_of_mem_hcompl hp (conjO_mem_hcompl hs)
  have key : conjO K r * s = r * conjO K s := by
    apply RingOfIntegers.ext
    have e1 := hfix
    rw [star_div₀, ← algebraMap_conjO, ← algebraMap_conjO] at e1
    have e2 : algebraMap (𝓞 K) K (conjO K r) * algebraMap (𝓞 K) K s =
        algebraMap (𝓞 K) K r * algebraMap (𝓞 K) K (conjO K s) := by
      rw [div_eq_div_iff hcs0 hs0] at e1
      exact e1
    simpa [map_mul] using e2
  refine ⟨r, s, hs, ?_, ?_, rfl⟩
  · by_contra hrp
    have hrc : r ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := K) p := by
      by_contra h'; exact hr ⟨hrp, h'⟩
    rw [mem_conjIdeal_iff] at hrc
    have h1 : conjO K r * s ∈ p := p.mul_mem_right _ hrc
    rw [key] at h1
    rcases hp.mem_or_mem h1 with h | h
    · exact hrp h
    · exact hcs.1 h
  · by_contra hrc
    have hrp : r ∈ p := by
      by_contra h'; exact hr ⟨h', hrc⟩
    have h1 : r * conjO K s ∈ p := p.mul_mem_right _ hrp
    rw [← key] at h1
    rcases hp.mem_or_mem h1 with h | h
    · exact hrc ((mem_conjIdeal_iff p r).2 h)
    · exact hs'.1 h

theorem InJ.add {p : Ideal (𝓞 K)} (hp : p.IsPrime) {a b : K} (ha : InJ p a) (hb : InJ p b) :
    InJ p (a + b) := by
  have hnz : ∀ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p, s ≠ 0 := by
    intro s hs
    induction hs using Submonoid.closure_induction with
    | mem x hx => exact fun h => hx.1 (h ▸ p.zero_mem)
    | one => exact one_ne_zero
    | mul x y _ _ hx hy => exact mul_ne_zero hx hy
  obtain ⟨r, s, hs, hr1, hr2, rfl⟩ := ha
  obtain ⟨r', s', hs', hr1', hr2', rfl⟩ := hb
  refine ⟨r * s' + r' * s, s * s', mul_mem hs hs', p.add_mem (p.mul_mem_right _ hr1) (p.mul_mem_right _ hr1'),
    (Formalism.HermitianLatticesTheory.conjIdeal (K := K) p).add_mem (Ideal.mul_mem_right _ _ hr2) (Ideal.mul_mem_right _ _ hr2'), ?_⟩
  have h1 : algebraMap (𝓞 K) K s ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).2 (hnz s hs)
  have h2 : algebraMap (𝓞 K) K s' ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).2 (hnz s' hs')
  rw [div_add_div _ _ h1 h2, map_add (f := _), map_mul, map_mul, map_mul]
  ring

theorem InJ.mul {p : Ideal (𝓞 K)} (hp : p.IsPrime) {κ a : K} (hκ : κ ∈ locRing p) (ha : InJ p a) :
    InJ p (κ * a) := by
  have hnz : ∀ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p, s ≠ 0 := by
    intro s hs
    induction hs using Submonoid.closure_induction with
    | mem x hx => exact fun h => hx.1 (h ▸ p.zero_mem)
    | one => exact one_ne_zero
    | mul x y _ _ hx hy => exact mul_ne_zero hx hy
  rw [mem_locRing, Formalism.HermitianLatticesTheory.locDual_mem_locR] at hκ
  obtain ⟨v, hv, hvk⟩ := hκ
  obtain ⟨u, hu⟩ := Submodule.mem_one.1 hvk
  obtain ⟨r, s, hs, hr1, hr2, rfl⟩ := ha
  refine ⟨u * r, v * s, mul_mem hv hs, p.mul_mem_left _ hr1, Ideal.mul_mem_left _ _ hr2, ?_⟩
  have h1 : algebraMap (𝓞 K) K v ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).2 (hnz v hv)
  have hκ' : κ = algebraMap (𝓞 K) K u / algebraMap (𝓞 K) K v := by
    rw [hu]
    field_simp
  rw [hκ', map_mul, map_mul, div_mul_div_comm]

theorem InJ.one_add {p : Ideal (𝓞 K)} (hp : p.IsPrime) {a : K} (ha : InJ p a) :
    IsUnitIn (locRing p) (1 + a) := by
  obtain ⟨r, s, hs, h1, h1', rfl⟩ := ha
  have e1 := algebraMap_ne_zero_of_mem_hcompl hp hs
  have hs' := (mem_hcompl_iff hp s).1 hs
  have e : (1 : K) + algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s =
      algebraMap (𝓞 K) K (s + r) / algebraMap (𝓞 K) K s := by
    rw [map_add (f := _)]; field_simp
  rw [e, isUnitIn_div_iff hp _ hs, mem_hcompl_iff hp]
  exact ⟨fun h => hs'.1 (by simpa using p.sub_mem h h1),
    fun h => hs'.2 (by simpa using Ideal.sub_mem _ h h1')⟩

variable {V : Type} [AddCommGroup V] [Module K V]

theorem norm_add_smul (h : V →ₗ⋆[K] V →ₗ[K] K) (x y : V) (κ : K) :
    h (x + κ • y) (x + κ • y) = h x x + κ * h x y + star κ * h y x + star κ * κ * h y y := by
  simp only [map_add (f := _), LinearMap.add_apply, LinearMap.map_smulₛₗ₂, LinearMap.map_smul, smul_eq_mul,
    starRingEnd_apply]
  ring

theorem exists_unit_norm {p : Ideal (𝓞 K)} (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hp : p.IsMaximal)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hnd : ∀ x, (∀ y, h x y = 0) → x = 0)
    {M : AddSubgroup V} (hM : IsSelfDualMod (locRing p) h M) (x₀ : V) (hx₀ : x₀ ≠ 0) :
    ∃ e ∈ M, IsUnitIn (locRing p) (h e e) := by
  have hS : IsHermSemilocal (locRing p) :=
    { star_mem := fun _ ha => star_mem_locRing hp.isPrime ha
      frac := frac_locRing p
      unram := unram_locRing hK hp
      principal := principal_locRing hK hp
      unit_or := unit_or_locRing hp.isPrime }
  set S := locRing p with hSdef
  have hsym : ∀ u v, star (h u v) = h v u := fun u v => hs.eq u v
  obtain ⟨m, htM, hm0⟩ : ∃ m ∈ M, m ≠ 0 := by
    obtain ⟨t, ht0, htM⟩ := hM.span x₀
    exact ⟨t • x₀, htM, smul_ne_zero ht0 hx₀⟩
  obtain ⟨y, hy⟩ : ∃ y, h m y ≠ 0 := by
    by_contra hc; push Not at hc; exact hm0 (hnd m hc)
  obtain ⟨t', ht'0, ht'M⟩ := hM.span y
  let f : V →+ K :=
    { toFun := fun u => h u m
      map_zero' := by simp
      map_add' := by intro a b; simp }
  have hf : ∀ u, f u = h u m := fun _ => rfl
  have hAS : ∀ c ∈ S, ∀ a ∈ M.map f, c * a ∈ M.map f := by
    rintro c hc _ ⟨u, hu, rfl⟩
    refine ⟨star c • u, hM.smul_mem _ (hS.star_mem _ hc) _ hu, ?_⟩
    rw [hf, hf, map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul]
  have h0 : ∃ a ∈ M.map f, a ≠ 0 := by
    refine ⟨_, ⟨t' • y, ht'M, rfl⟩, ?_⟩
    rw [hf, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, ← hsym m y]
    exact mul_ne_zero (star_ne_zero.mpr ht'0) (star_ne_zero.mpr hy)
  have hb : ∀ a ∈ M.map f, (1 : K) * a ∈ S := by
    rintro _ ⟨u, hu, rfl⟩
    rw [one_mul]; exact hM.int u hu m htM
  obtain ⟨α, ⟨w₀, hw₀, hα⟩, hα0, hdiv⟩ := hS.principal (M.map f) hAS h0 ⟨1, one_ne_zero, hb⟩
  rw [hf] at hα
  have hyM : α⁻¹ • m ∈ M := by
    apply hM.dual
    intro u hu
    have := hdiv _ ⟨u, hu, rfl⟩
    rw [map_smul, smul_eq_mul, mul_comm]
    exact this
  have hxy : h w₀ (α⁻¹ • m) = 1 := by
    rw [map_smul, smul_eq_mul, hα, inv_mul_cancel₀ hα0]
  have hyx : h (α⁻¹ • m) w₀ = 1 := by rw [← hsym, hxy, star_one]
  generalize α⁻¹ • m = y' at hyM hxy hyx
  by_cases hux : IsUnitIn S (h w₀ w₀)
  · exact ⟨w₀, hw₀, hux⟩
  by_cases huy : IsUnitIn S (h y' y')
  · exact ⟨y', hyM, huy⟩
  obtain ⟨κ, hκ, hκt⟩ := exists_trace_eq hS S.one_mem (star_one K)
  refine ⟨w₀ + κ • y', M.add_mem hw₀ (hM.smul_mem _ hκ _ hyM), ?_⟩
  have hJx := inJ_of_fixed hp.isPrime (hM.int _ hw₀ _ hw₀) (hsym w₀ w₀) hux
  have hJy := inJ_of_fixed hp.isPrime (hM.int _ hyM _ hyM) (hsym _ _) huy
  have e : h (w₀ + κ • y') (w₀ + κ • y') = 1 + (h w₀ w₀ + (star κ * κ) * h y' y') := by
    rw [norm_add_smul, hxy, hyx]
    linear_combination hκt
  rw [e]
  exact (hJx.add hp.isPrime (hJy.mul hp.isPrime (S.mul_mem (hS.star_mem _ hκ) hκ))).one_add hp.isPrime

theorem exists_norm_eq {p : Ideal (𝓞 K)} (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hp : p.IsMaximal)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hnd : ∀ x, (∀ y, h x y = 0) → x = 0)
    {M : AddSubgroup V} (hM : IsSelfDualMod (locRing p) h M) (e : V)
    (he : IsUnitIn (locRing p) (h e e)) :
    ∃ X ∈ M, h X X = h e e := by
  have hS : IsHermSemilocal (locRing p) :=
    { star_mem := fun _ ha => star_mem_locRing hp.isPrime ha
      frac := frac_locRing p
      unram := unram_locRing hK hp
      principal := principal_locRing hK hp
      unit_or := unit_or_locRing hp.isPrime }
  set S := locRing p with hSdef
  have hsym : ∀ u v, star (h u v) = h v u := fun u v => hs.eq u v
  set a := h e e with ha
  have hafix : star a = a := hsym e e
  obtain ⟨ha0, haS, hainv⟩ := he
  have he0 : e ≠ 0 := by rintro rfl; simp [a] at ha0
  obtain ⟨y, hy⟩ : ∃ y, h e y ≠ 0 := by
    by_contra hc; push Not at hc; exact he0 (hnd e hc)
  obtain ⟨t', ht'0, ht'M⟩ := hM.span y
  obtain ⟨t, ht0, htM⟩ := hM.span e
  let f : V →+ K :=
    { toFun := fun u => h u e
      map_zero' := by simp
      map_add' := by intro a b; simp }
  have hf : ∀ u, f u = h u e := fun _ => rfl
  have hAS : ∀ c ∈ S, ∀ a ∈ M.map f, c * a ∈ M.map f := by
    rintro c hc _ ⟨u, hu, rfl⟩
    refine ⟨star c • u, hM.smul_mem _ (hS.star_mem _ hc) _ hu, ?_⟩
    rw [hf, hf, map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul]
  have h0 : ∃ a ∈ M.map f, a ≠ 0 := by
    refine ⟨_, ⟨t' • y, ht'M, rfl⟩, ?_⟩
    rw [hf, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, ← hsym e y]
    exact mul_ne_zero (star_ne_zero.mpr ht'0) (star_ne_zero.mpr hy)
  have hb : ∀ a ∈ M.map f, t * a ∈ S := by
    rintro _ ⟨u, hu, rfl⟩
    have := hM.int u hu _ htM
    rwa [map_smul, smul_eq_mul] at this
  obtain ⟨α, ⟨w₀, hw₀, hα⟩, hα0, hdiv⟩ := hS.principal (M.map f) hAS h0 ⟨t, ht0, hb⟩
  rw [hf] at hα
  have hyM : α⁻¹ • e ∈ M := by
    apply hM.dual
    intro u hu
    have := hdiv _ ⟨u, hu, rfl⟩
    rw [map_smul, smul_eq_mul, mul_comm]
    exact this
  have hyw : h (α⁻¹ • e) w₀ = 1 := by
    rw [map_smulₛₗ, LinearMap.smul_apply, ← hsym w₀ e, hα, starRingEnd_apply, smul_eq_mul,
      ← star_mul', inv_mul_cancel₀ hα0, star_one]
  have hyy : h (α⁻¹ • e) (α⁻¹ • e) = star α⁻¹ * α⁻¹ * a := by
    rw [map_smul, map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, smul_eq_mul, smul_eq_mul]
    ring
  let h' : V →ₗ⋆[K] V →ₗ[K] K := a⁻¹ • h
  have h'app : ∀ u v, h' u v = a⁻¹ * h u v := fun u v => by
    show (a⁻¹ • h) u v = _
    rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul]
  have hs' : h'.IsSymm := by
    refine ⟨fun u v => ?_⟩
    rw [h'app, h'app, map_mul, starRingEnd_apply, starRingEnd_apply, star_inv₀, hafix, hsym u v]
  have hnorm : star α⁻¹ * α⁻¹ ∈ S := by
    have : star α⁻¹ * α⁻¹ = h (α⁻¹ • e) (α⁻¹ • e) * a⁻¹ := by rw [hyy]; field_simp
    rw [this]; exact S.mul_mem (hM.int _ hyM _ hyM) hainv
  obtain ⟨bb, hbb1, hbbS⟩ := exists_norm_one_mul_mem hS (a := α⁻¹) hnorm
  have hbb0 : bb ≠ 0 := by rintro rfl; simp at hbb1
  have hyy' : h' (α⁻¹ • e) (α⁻¹ • e) = star (α⁻¹ * bb) * (α⁻¹ * bb) := by
    rw [h'app, hyy, star_mul']
    calc a⁻¹ * (star α⁻¹ * α⁻¹ * a) = star α⁻¹ * α⁻¹ * (star bb * bb) := by
          rw [hbb1]; field_simp
      _ = _ := by ring
  have hwM : a • w₀ ∈ M := hM.smul_mem _ haS _ hw₀
  have hyw' : h' (α⁻¹ • e) (a • w₀) = 1 := by
    rw [h'app, map_smul, smul_eq_mul, hyw]; field_simp
  have hww : h' (a • w₀) (a • w₀) ∈ S := by
    rw [h'app, map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, starRingEnd_apply,
      hafix]
    have : a⁻¹ * (a * (a * h w₀ w₀)) = a * h w₀ w₀ := by field_simp
    rw [this]; exact S.mul_mem haS (hM.int _ hw₀ _ hw₀)
  obtain ⟨c, hc, d, hd, hcd⟩ := exists_norm_one_of_pair hS hs' hbbS
    (mul_ne_zero (inv_ne_zero hα0) hbb0) hyy' hyw' hww
  refine ⟨c • (a • w₀) + d • (α⁻¹ • e), M.add_mem (hM.smul_mem _ hc _ hwM) (hM.smul_mem _ hd _ hyM), ?_⟩
  rw [h'app] at hcd
  have := congrArg (fun u => a * u) hcd
  rw [← mul_assoc, mul_inv_cancel₀ ha0, one_mul, mul_one] at this
  exact this

end Formalism.L2.SG.Pf.LatDictZ.Z0.SGA
end
end

noncomputable section

open NumberField

namespace Formalism.L2.SG.Pf.LatDictZ.Z0.SGB

open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA Formalism.L2.SG.Pf.LatDictZ.Z0.SGA

variable {K : Type} [Field K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V]

def restr (h : V →ₗ⋆[K] V →ₗ[K] K) (W : Submodule K V) : W →ₗ⋆[K] W →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (fun x y => h x y)
    (by intro x y z; simp) (by intro c x y; simp) (by intro x y z; simp) (by intro c x y; simp)

def coef (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) : V →ₗ[K] K := (h X X)⁻¹ • h X

theorem coef_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (X x : V) : coef h X x = (h X X)⁻¹ * h X x := rfl

def proj (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0) : V →ₗ[K] LinearMap.ker (h X) :=
  LinearMap.codRestrict (LinearMap.ker (h X)) (LinearMap.id - (coef h X).smulRight X) (by
    intro x
    rw [LinearMap.mem_ker]
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply, map_sub, map_smul,
      smul_eq_mul, coef_apply]
    field_simp
    ring)

theorem proj_val (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0) (x : V) :
    (proj h X hX x : V) = x - coef h X x • X := rfl

theorem coef_self (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0) : coef h X X = 1 := by
  rw [coef_apply, inv_mul_cancel₀ hX]

theorem coef_ker (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (w : LinearMap.ker (h X)) : coef h X w = 0 := by
  rw [coef_apply, LinearMap.mem_ker.mp w.2, mul_zero]

theorem decomp (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0) (x : V) :
    x = coef h X x • X + (proj h X hX x : V) := by
  rw [proj_val]
  abel

def ext (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0) (g : LinearMap.ker (h X) ≃ₗ[K] LinearMap.ker (h X)) :
    V →ₗ[K] V :=
  (coef h X).smulRight X + (LinearMap.ker (h X)).subtype ∘ₗ (g : _ →ₗ[K] _) ∘ₗ proj h X hX

theorem ext_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0)
    (g : LinearMap.ker (h X) ≃ₗ[K] LinearMap.ker (h X)) (x : V) :
    ext h X hX g x = coef h X x • X + (g (proj h X hX x) : V) := rfl

theorem coef_ext (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0)
    (g : LinearMap.ker (h X) ≃ₗ[K] LinearMap.ker (h X)) (x : V) :
    coef h X (ext h X hX g x) = coef h X x := by
  rw [ext_apply, map_add (f := _), map_smul, coef_self h X hX, coef_ker h X (g (proj h X hX x)), smul_eq_mul,
    mul_one, add_zero]

theorem proj_ext (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0)
    (g : LinearMap.ker (h X) ≃ₗ[K] LinearMap.ker (h X)) (x : V) :
    proj h X hX (ext h X hX g x) = g (proj h X hX x) := by
  apply Subtype.ext
  rw [proj_val, coef_ext, ext_apply]
  abel

theorem ext_comp (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0)
    (g : LinearMap.ker (h X) ≃ₗ[K] LinearMap.ker (h X)) (x : V) :
    ext h X hX g.symm (ext h X hX g x) = x := by
  rw [ext_apply, coef_ext, proj_ext, LinearEquiv.symm_apply_apply]
  exact (decomp h X hX x).symm

def extE (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0)
    (g : LinearMap.ker (h X) ≃ₗ[K] LinearMap.ker (h X)) : V ≃ₗ[K] V :=
  LinearEquiv.ofLinearMap (ext h X hX g) (ext h X hX g.symm)
    (by
      ext x
      have := ext_comp h X hX g.symm x
      rwa [LinearEquiv.symm_symm] at this)
    (by ext x; exact ext_comp h X hX g x)

theorem extE_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0)
    (g : LinearMap.ker (h X) ≃ₗ[K] LinearMap.ker (h X)) (x : V) :
    extE h X hX g x = ext h X hX g x := rfl

theorem h_ker_X (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hs : ∀ u v, star (h u v) = h v u)
    (w : LinearMap.ker (h X)) : h w X = 0 := by
  rw [← hs X w, LinearMap.mem_ker.mp w.2, star_zero]

theorem h_decomp (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0) (hs : ∀ u v, star (h u v) = h v u)
    (x y : V) :
    h x y = star (coef h X x) * coef h X y * h X X + h (proj h X hX x) (proj h X hX y) := by
  conv_lhs => rw [decomp h X hX x, decomp h X hX y]
  simp only [LinearMap.map_add₂, map_add (f := _), LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul, starRingEnd_apply,
    LinearMap.add_apply, LinearMap.smul_apply]
  rw [LinearMap.mem_ker.mp (proj h X hX y).2, h_ker_X h X hs (proj h X hX x)]
  ring

theorem extE_isom (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0) (hs : ∀ u v, star (h u v) = h v u)
    (g : LinearMap.ker (h X) ≃ₗ[K] LinearMap.ker (h X))
    (hg : ∀ u v, h (g u : V) (g v : V) = h (u : V) (v : V)) (x y : V) :
    h (extE h X hX g x) (extE h X hX g y) = h x y := by
  rw [h_decomp h X hX hs, h_decomp h X hX hs x y, extE_apply, extE_apply, coef_ext, coef_ext, proj_ext,
    proj_ext, hg]

variable {S : Subring K}

theorem mem_iff_split {h : V →ₗ⋆[K] V →ₗ[K] K} {M : AddSubgroup V} (hM : IsSelfDualMod S h M) {X : V}
    (hXM : X ∈ M) (hXu : IsUnitIn S (h X X)) (x : V) :
    x ∈ M ↔ coef h X x ∈ S ∧ (proj h X hXu.1 x : V) ∈ M := by
  constructor
  · intro hx
    have hc : coef h X x ∈ S := by
      rw [coef_apply]
      exact S.mul_mem hXu.2.2 (hM.int X hXM x hx)
    refine ⟨hc, ?_⟩
    rw [proj_val]
    exact M.sub_mem hx (hM.smul_mem _ hc X hXM)
  · rintro ⟨hc, hp⟩
    rw [decomp h X hXu.1 x]
    exact M.add_mem (hM.smul_mem _ hc X hXM) hp

theorem selfDual_restr {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : ∀ u v, star (h u v) = h v u) {M : AddSubgroup V}
    (hM : IsSelfDualMod S h M) {X : V} (hXM : X ∈ M) (hXu : IsUnitIn S (h X X)) :
    IsSelfDualMod S (restr h (LinearMap.ker (h X)))
      (M.comap ((LinearMap.ker (h X)).subtype : LinearMap.ker (h X) →ₗ[K] V).toAddMonoidHom) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha m hm
    change ((a • m : LinearMap.ker (h X)) : V) ∈ M
    rw [Submodule.coe_smul]
    exact hM.smul_mem a ha _ hm
  · exact fun x hx y hy => hM.int _ hx _ hy
  · intro x hx
    change (x : V) ∈ M
    apply hM.dual
    intro m hm
    have hpm : ((proj h X hXu.1 m : LinearMap.ker (h X)) : V) ∈ M := ((mem_iff_split hM hXM hXu m).1 hm).2
    have e : h m x = h (proj h X hXu.1 m) x := by
      conv_lhs => rw [decomp h X hXu.1 m]
      rw [map_add (f := _), LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, LinearMap.mem_ker.1 x.2,
        smul_zero, zero_add]
    rw [e]
    exact hx (proj h X hXu.1 m) hpm
  · intro x
    obtain ⟨t, ht, htx⟩ := hM.span (x : V)
    exact ⟨t, ht, by change ((t • x : LinearMap.ker (h X)) : V) ∈ M; rw [Submodule.coe_smul]; exact htx⟩

theorem nondeg_restr {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : ∀ u v, star (h u v) = h v u)
    (hnd : ∀ x, (∀ y, h x y = 0) → x = 0) {X : V} (hX : h X X ≠ 0) (w : LinearMap.ker (h X))
    (hw : ∀ y, restr h (LinearMap.ker (h X)) w y = 0) : w = 0 := by
  refine Subtype.ext (hnd _ (fun z => ?_))
  rw [decomp h X hX z, map_add (f := _), map_smul, smul_eq_mul, h_ker_X h X hs w, mul_zero, zero_add]
  exact hw (proj h X hX z)

theorem symm_restr {h : V →ₗ⋆[K] V →ₗ[K] K} (hsy : h.IsSymm) (W : Submodule K V) :
    (restr h W).IsSymm := by
  first
    | exact fun x y => hsy x y
    | exact ⟨fun x y => hsy.eq x y⟩

theorem selfDual_map {h : V →ₗ⋆[K] V →ₗ[K] K} {M : AddSubgroup V} (hM : IsSelfDualMod S h M)
    (g : V ≃ₗ[K] V) (hg : ∀ x y, h (g x) (g y) = h x y) :
    IsSelfDualMod S h (M.comap (g.symm : V →ₗ[K] V).toAddMonoidHom) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha m hm
    change g.symm (a • m) ∈ M
    rw [map_smul]; exact hM.smul_mem a ha _ hm
  · intro x hx y hy
    have := hM.int _ hx _ hy
    change h (g.symm x) (g.symm y) ∈ S at this
    rwa [← hg, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at this
  · intro x hx
    change g.symm x ∈ M
    apply hM.dual
    intro m hm
    have := hx (g m) (by change g.symm (g m) ∈ M; rwa [LinearEquiv.symm_apply_apply])
    rw [← hg m (g.symm x), LinearEquiv.apply_symm_apply]
    exact this
  · intro x
    obtain ⟨t, ht, htx⟩ := hM.span (g.symm x)
    exact ⟨t, ht, by change g.symm (t • x) ∈ M; rwa [map_smul]⟩

end Formalism.L2.SG.Pf.LatDictZ.Z0.SGB
end
end

noncomputable section

open NumberField Module

namespace Formalism.L2.SG.Pf.LatDictZ.Z0.SGC

open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA Formalism.L2.SG.Pf.LatDictZ.Z0.SGA Formalism.L2.SG.Pf.LatDictZ.Z0.SGB

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem exists_isom_vec {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hsy : h.IsSymm) (hnd : ∀ x, (∀ y, h x y = 0) → x = 0) {e X : V}
    (he : h e e ≠ 0) (hXe : h X X = h e e) :
    ∃ τ : V ≃ₗ[K] V, (∀ x y, h (τ x) (τ y) = h x y) ∧ τ e = X := by
  have he0 : e ≠ 0 := by rintro rfl; simp at he
  have hX0 : X ≠ 0 := by rintro rfl; simp at hXe; exact he hXe.symm
  let f : (K ∙ e) →ₗ[K] V := (LinearMap.toSpanSingleton K V X) ∘ₗ
    ((LinearEquiv.coord K V e he0 : (K ∙ e) ≃ₗ[K] K) : (K ∙ e) →ₗ[K] K)
  have hf : ∀ u, f u = LinearEquiv.coord K V e he0 u • X := fun u => rfl
  have hu : ∀ u : (K ∙ e), (u : V) = LinearEquiv.coord K V e he0 u • e := fun u =>
    (LinearEquiv.coord_apply_smul K V e he0 u).symm
  have hinj : Function.Injective f := by
    intro u v huv
    rw [hf, hf] at huv
    have := smul_left_injective K hX0 huv
    exact (LinearEquiv.coord K V e he0).injective this
  have hiso : ∀ u v : (K ∙ e), h (f u) (f v) = h u v := by
    intro u v
    rw [hf, hf, hu u, hu v]
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hXe]
  obtain ⟨g, hg, hgf⟩ := witt_extension_theorem K V h (fun x y => hsy.eq x y) hnd (K ∙ e) f hinj hiso
  refine ⟨g, hg, ?_⟩
  have := hgf ⟨e, Submodule.mem_span_singleton_self e⟩
  rw [this, hf, LinearEquiv.coord_self, one_smul]

theorem core {p : Ideal (𝓞 K)} (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hp : p.IsMaximal) (n : ℕ) :
    ∀ (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V], finrank K V = n →
    ∀ (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm → (∀ x, (∀ y, h x y = 0) → x = 0) →
    ∀ M₁ M₂ : AddSubgroup V, IsSelfDualMod (locRing p) h M₁ → IsSelfDualMod (locRing p) h M₂ →
      ∃ g : V ≃ₗ[K] V, (∀ x y, h (g x) (g y) = h x y) ∧ ∀ x, x ∈ M₁ ↔ g x ∈ M₂ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ hn h hsy hnd M₁ M₂ h1 h2
  have hs : ∀ u v, star (h u v) = h v u := fun u v => hsy.eq u v
  by_cases hV : ∃ x₀ : V, x₀ ≠ 0
  swap
  · push Not at hV
    refine ⟨LinearEquiv.refl K V, fun _ _ => rfl, fun x => ?_⟩
    rw [hV x]
    exact ⟨fun _ => M₂.zero_mem, fun _ => M₁.zero_mem⟩
  obtain ⟨x₀, hx₀⟩ := hV
  obtain ⟨e, heM, heu⟩ := exists_unit_norm hK hp hsy hnd h1 x₀ hx₀
  obtain ⟨X, hXM, hXe⟩ := exists_norm_eq hK hp hsy hnd h2 e heu
  have hXu : IsUnitIn (locRing p) (h X X) := hXe ▸ heu
  have hX0 : h X X ≠ 0 := hXu.1
  obtain ⟨τ, hτ, hτe⟩ := exists_isom_vec hsy hnd heu.1 hXe
  have hN1 : IsSelfDualMod (locRing p) h (M₁.comap (τ.symm : V →ₗ[K] V).toAddMonoidHom) := by
    refine { smul_mem := ?_, int := ?_, dual := ?_, span := ?_ }
    · intro a ha m hm
      change τ.symm (a • m) ∈ M₁
      rw [map_smul]
      exact h1.smul_mem a ha _ hm
    · intro x hx y hy
      have hxy : h (τ.symm x) (τ.symm y) ∈ locRing p := h1.int _ hx _ hy
      rwa [← hτ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at hxy
    · intro x hx
      change τ.symm x ∈ M₁
      apply h1.dual
      intro m hm
      have hτm : τ m ∈ M₁.comap (τ.symm : V →ₗ[K] V).toAddMonoidHom := by
        change τ.symm (τ m) ∈ M₁
        rwa [LinearEquiv.symm_apply_apply]
      rw [← hτ m (τ.symm x), LinearEquiv.apply_symm_apply]
      exact hx (τ m) hτm
    · intro x
      obtain ⟨t, ht, htx⟩ := h1.span (τ.symm x)
      refine ⟨t, ht, ?_⟩
      change τ.symm (t • x) ∈ M₁
      rwa [map_smul]
  have hXN : X ∈ M₁.comap (τ.symm : V →ₗ[K] V).toAddMonoidHom := by
    change τ.symm X ∈ M₁
    rw [← hτe, LinearEquiv.symm_apply_apply]
    exact heM
  have hdim : finrank K (LinearMap.ker (h X)) < n := by
    have h1' := LinearMap.finrank_range_add_finrank_ker (h X)
    have hpos : 0 < finrank K (LinearMap.range (h X)) := by
      rw [Module.finrank_pos_iff_exists_ne_zero]
      exact ⟨⟨h X X, X, rfl⟩, fun h0 => hX0 (congrArg Subtype.val h0)⟩
    omega
  have hSelfDualRestr {M : AddSubgroup V} (hM : IsSelfDualMod (locRing p) h M) (hXM : X ∈ M) :
      IsSelfDualMod (locRing p) (restr h (LinearMap.ker (h X)))
        (M.comap (LinearMap.ker (h X)).subtype.toAddMonoidHom) := by
    refine { smul_mem := ?_, int := ?_, dual := ?_, span := ?_ }
    · intro a ha m hm
      change ((a • m : LinearMap.ker (h X)) : V) ∈ M
      rw [Submodule.coe_smul]
      exact hM.smul_mem a ha _ hm
    · intro x hx y hy
      exact hM.int x hx y hy
    · intro x hx
      change (x : V) ∈ M
      apply hM.dual
      intro m hm
      have hpm : (proj h X hX0 m : V) ∈ M := ((mem_iff_split hM hXM hXu m).1 hm).2
      have heq : h m x = h (proj h X hX0 m) x := by
        conv_lhs => rw [decomp h X hX0 m]
        rw [map_add (f := _), LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply,
          LinearMap.mem_ker.mp x.2, smul_zero, zero_add]
      rw [heq]
      exact hx (proj h X hX0 m) hpm
    · intro x
      obtain ⟨t, ht, htx⟩ := hM.span (x : V)
      refine ⟨t, ht, ?_⟩
      change ((t • x : LinearMap.ker (h X)) : V) ∈ M
      rwa [Submodule.coe_smul]
  obtain ⟨g', hg', hmem'⟩ := ih _ hdim (LinearMap.ker (h X)) rfl (restr h (LinearMap.ker (h X)))
    (symm_restr hsy _) (nondeg_restr hs hnd hX0) _ _ (hSelfDualRestr hN1 hXN) (hSelfDualRestr h2 hXM)
  refine ⟨τ.trans (extE h X hX0 g'), ?_, ?_⟩
  · intro x y
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, extE_isom h X hX0 hs g' (fun u v => hg' u v), hτ]
  · intro x
    rw [LinearEquiv.trans_apply]
    have e1 : x ∈ M₁ ↔ τ x ∈ M₁.comap (τ.symm : V →ₗ[K] V).toAddMonoidHom := by
      change _ ↔ τ.symm (τ x) ∈ M₁
      rw [LinearEquiv.symm_apply_apply]
    rw [e1, mem_iff_split hN1 hXN hXu, mem_iff_split h2 hXM hXu, extE_apply, coef_ext, proj_ext]
    exact and_congr Iff.rfl (hmem' (proj h X hX0 (τ x)))

theorem semi_genus_local : SemiGenusLoc := by
  intro K _ _ _ V _ _ _ h hK hsy hnd p hp M₁ M₂ h1 h2
  obtain ⟨g, hg, hm⟩ := core hK hp _ V rfl h hsy hnd M₁ M₂ h1 h2
  exact ⟨g, hg, hm⟩

end Formalism.L2.SG.Pf.LatDictZ.Z0.SGC
