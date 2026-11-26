module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsPrimitiveNorm

@[expose] public section

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsIsomScale
noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.U0

open WA

variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

def cutW (h : V →ₗ⋆[K] V →ₗ[K] K) (W : Submodule K V) (X : V) : Submodule K V :=
  W ⊓ LinearMap.ker (h X)

def cutM (h : V →ₗ⋆[K] V →ₗ[K] K) (M : AddSubgroup V) (X : V) : AddSubgroup V :=
  M ⊓ (LinearMap.ker (h X)).toAddSubgroup

variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K} {W : Submodule K V} {M : AddSubgroup V}

theorem mem_cutW {X v : V} : v ∈ cutW h W X ↔ v ∈ W ∧ h X v = 0 := by
  simp [cutW]

theorem mem_cutM {X v : V} : v ∈ cutM h M X ↔ v ∈ M ∧ h X v = 0 := by
  simp [cutM]

theorem symm_zero (hs : h.IsSymm) {x y : V} (hxy : h x y = 0) : h y x = 0 := by
  have e := hs.eq x y
  rw [hxy, map_zero] at e
  exact e.symm

theorem proj_mem (hM : IsLatIn S h W M) {X : V} (hX : X ∈ M) (hu : IsUnitIn S (h X X)) {m : V}
    (hm : m ∈ M) : m - (h X m * (h X X)⁻¹) • X ∈ cutM h M X := by
  have hc : h X m * (h X X)⁻¹ ∈ S := S.mul_mem (hM.int X hX m hm) hu.2.2
  rw [mem_cutM]
  refine ⟨M.sub_mem hm (hM.smul_mem _ hc _ hX), ?_⟩
  rw [map_sub, map_smul, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hu.1, mul_one, sub_self]

theorem IsLatIn.cut (hM : IsLatIn S h W M) (X : V) : IsLatIn S h (cutW h W X) (cutM h M X) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m hm
    obtain ⟨hmM, hm0⟩ := mem_cutM.mp hm
    exact mem_cutW.mpr ⟨hM.le m hmM, hm0⟩
  · intro a ha m hm
    obtain ⟨hmM, hm0⟩ := mem_cutM.mp hm
    refine mem_cutM.mpr ⟨hM.smul_mem a ha m hmM, ?_⟩
    rw [map_smul, hm0, smul_zero]
  · intro x hx y hy
    exact hM.int x (mem_cutM.mp hx).1 y (mem_cutM.mp hy).1
  · intro x hx
    obtain ⟨hxW, hx0⟩ := mem_cutW.mp hx
    obtain ⟨t, ht0, ht⟩ := hM.span x hxW
    refine ⟨t, ht0, mem_cutM.mpr ⟨ht, ?_⟩⟩
    rw [map_smul, hx0, smul_zero]

theorem int_of_cut (hM : IsLatIn S h W M) {X : V} (hX : X ∈ M)
    (hu : IsUnitIn S (h X X)) {x : V} (hXx : h X x = 0) (hx : ∀ m ∈ cutM h M X, h m x ∈ S) :
    ∀ m ∈ M, h m x ∈ S := by
  intro m hm
  have hp := hx _ (proj_mem hM hX hu hm)
  rw [LinearMap.map_sub₂, LinearMap.map_smulₛₗ₂, hXx, smul_zero, sub_zero] at hp
  exact hp

theorem IsSD.cut (hM : IsSD S h W M) {X : V} (hX : X ∈ M) (hu : IsUnitIn S (h X X)) :
    IsSD S h (cutW h W X) (cutM h M X) := by
  refine ⟨hM.toIsLatIn.cut X, fun x hx hxS => ?_⟩
  obtain ⟨hxW, hx0⟩ := mem_cutW.1 hx
  exact mem_cutM.2 ⟨hM.dual x hxW (int_of_cut hM.toIsLatIn hX hu hx0 hxS), hx0⟩

theorem IsASD.cut (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm) {z : V}
    (hM : IsASD S π h W M z) {X : V} (hX : X ∈ M) (hu : IsUnitIn S (h X X)) :
    IsASD S π h (cutW h W X) (cutM h M X) (z - (h X z * (h X X)⁻¹) • X) := by
  have hL := hM.toIsLatIn
  have hXz' := (mem_cutM.1 (proj_mem hL hX hu hM.z_mem)).2
  have hsh : ∀ v, h X v = 0 → h (z - (h X z * (h X X)⁻¹) • X) v = h z v := by
    intro v hv
    rw [LinearMap.map_sub₂, LinearMap.map_smulₛₗ₂, hv, smul_zero, sub_zero]
  refine ⟨hL.cut X, proj_mem hL hX hu hM.z_mem, ?_, fun m hm => ?_, fun x hx hzx hxS => ?_⟩
  · obtain ⟨hN0, -, hNi⟩ := hu
    obtain ⟨hu0, hu1, hui⟩ := hM.z_norm
    have hπ0 := hπ.ne
    obtain ⟨s, hsS, hzX⟩ : ∃ s ∈ S, h z X = s * π :=
      ⟨_, hM.z_rad X hX, by rw [inv_mul_cancel_right₀ hπ0]⟩
    have hXz : h X z = star s * π := by
      rw [← hs.eq z X, hzX, map_mul, starRingEnd_apply, starRingEnd_apply, hπ.fix]
    have hNN : starRingEnd K (h X X) = h X X := hs.eq X X
    have e1 : h (z - (h X z * (h X X)⁻¹) • X) X = 0 := symm_zero hs hXz'
    have key : h (z - (h X z * (h X X)⁻¹) • X) (z - (h X z * (h X X)⁻¹) • X)
        = h z z - s * π * (h X X)⁻¹ * (star s * π) := by
      rw [LinearMap.map_sub, LinearMap.map_smul, e1, smul_zero, sub_zero, LinearMap.map_sub₂,
        LinearMap.map_smulₛₗ₂, smul_eq_mul, map_mul, map_inv₀, hNN, hs.eq X z, hzX, hXz]
    have hzz0 : h z z ≠ 0 := fun e => hu0 (by rw [e, zero_mul])
    have hmul : ∀ a b : K, IsUnitIn S a → IsUnitIn S b → IsUnitIn S (a * b) := fun a b ha hb =>
      ⟨mul_ne_zero ha.1 hb.1, S.mul_mem ha.2.1 hb.2.1, by rw [mul_inv]; exact S.mul_mem ha.2.2 hb.2.2⟩
    have e2 : (h z z - s * π * (h X X)⁻¹ * (star s * π)) * π⁻¹
        = (h z z * π⁻¹) * (1 + π * (-(s * star s * (h X X)⁻¹) * (h z z * π⁻¹)⁻¹)) := by
      field_simp
      ring
    rw [key, e2]
    exact hmul _ _ ⟨hu0, hu1, hui⟩ (hπ.rad _ (S.mul_mem (S.neg_mem
      (S.mul_mem (S.mul_mem hsS (hS.star_mem s hsS)) hNi)) hui))
  · rw [mem_cutM] at hm
    show h _ m * π⁻¹ ∈ S
    rw [hsh m hm.2]
    exact hM.z_rad m hm.1
  · obtain ⟨hxW, hx0⟩ := mem_cutW.1 hx
    rw [hsh x hx0] at hzx
    exact mem_cutM.2 ⟨hM.dual x hxW hzx (int_of_cut hL hX hu hx0 hxS), hx0⟩

theorem exists_isom_move (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) {x y : V}
    (hxy : h x x = h y y) :
    ∃ τ ∈ Formalism.HermitianLatticesTheory.isom h, τ x = y ∧ (∀ v, h x v = 0 → h y v = 0 → τ v = v) ∧
      ∀ W : Submodule K V, x ∈ W → y ∈ W → ∀ v, v ∈ W ↔ τ v ∈ W := by
  by_cases hxy' : x = y
  · subst hxy'
    exact ⟨1, one_mem _, rfl, fun v _ _ => rfl, fun W _ _ v => Iff.rfl⟩
  generalize hu_def : x - y = u
  have hD : h u u = h u x + starRingEnd K (h u x) := by
    rw [hs.eq u x, ← hu_def]
    simp only [map_sub, LinearMap.sub_apply]
    rw [hxy]
    ring
  have hu0 : u ≠ 0 := by rw [← hu_def]; exact sub_ne_zero.2 hxy'
  have hD0 : h u x ≠ 0 := by
    intro e
    apply hu0
    apply hd
    rw [hD, e, map_zero, add_zero]
  have hD0' : starRingEnd K (h u x) ≠ 0 := by rwa [map_ne_zero]
  let f : V →ₗ[K] V := LinearMap.id - (LinearMap.toSpanSingleton K V u) ∘ₗ ((h u x)⁻¹ • h u)
  let f' : V →ₗ[K] V :=
    LinearMap.id - (LinearMap.toSpanSingleton K V u) ∘ₗ ((starRingEnd K (h u x))⁻¹ • h u)
  have hf : ∀ v, f v = v - ((h u x)⁻¹ * h u v) • u := fun v => by simp [f]
  have hf' : ∀ v, f' v = v - ((starRingEnd K (h u x))⁻¹ * h u v) • u := fun v => by simp [f']
  have c1 : f ∘ₗ f' = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.comp_apply, LinearMap.id_apply, hf, hf', map_sub, map_smul, smul_eq_mul, sub_sub,
      ← add_smul, sub_eq_self]
    apply smul_eq_zero_of_left
    rw [hD]
    field_simp
    ring
  have c2 : f' ∘ₗ f = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.comp_apply, LinearMap.id_apply, hf, hf', map_sub, map_smul, smul_eq_mul, sub_sub,
      ← add_smul, sub_eq_self]
    apply smul_eq_zero_of_left
    rw [hD]
    field_simp
    ring
  refine ⟨LinearEquiv.ofLinear f f' c1 c2, fun a b => ?_, ?_, fun v hxv hyv => ?_, fun W hxW hyW v => ?_⟩
  · change h (f a) (f b) = h a b
    rw [hf a, hf b]
    simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.map_smulₛₗ₂, LinearMap.smul_apply,
      smul_eq_mul, map_mul, map_inv₀]
    rw [← hs.eq u a, hD]
    field_simp
    ring
  · change f x = y
    rw [hf, inv_mul_cancel₀ hD0, one_smul, ← hu_def, sub_sub_cancel]
  · change f v = v
    have huv : h u v = 0 := by rw [← hu_def, LinearMap.map_sub₂, hxv, hyv, sub_zero]
    rw [hf, huv, mul_zero, zero_smul, sub_zero]
  · have huW : u ∈ W := by rw [← hu_def]; exact W.sub_mem hxW hyW
    change v ∈ W ↔ f v ∈ W
    rw [hf]
    exact (Submodule.sub_mem_iff_left W (W.smul_mem _ huW)).symm

theorem exists_isom_scale (hs : h.IsSymm) {z : V} (hz : h z z ≠ 0) {b : K} (hb : star b * b = 1) :
    ∃ ψ ∈ Formalism.HermitianLatticesTheory.isom h, ψ z = b • z ∧ ∀ v, h z v = 0 → ψ v = v := by
  have hN : starRingEnd K (h z z) = h z z := hs.eq z z
  have hNi : h z z * (h z z)⁻¹ = 1 := mul_inv_cancel₀ hz
  have hz0 : ∀ (v : V) (c : K), c = 0 → v + c • z = v := fun v c hc => by
    rw [hc, zero_smul, add_zero]
  let f : V →ₗ[K] V :=
    LinearMap.id + (LinearMap.toSpanSingleton K V z) ∘ₗ (((b - 1) * (h z z)⁻¹) • h z)
  let f' : V →ₗ[K] V :=
    LinearMap.id + (LinearMap.toSpanSingleton K V z) ∘ₗ (((star b - 1) * (h z z)⁻¹) • h z)
  have hf : ∀ v, f v = v + ((b - 1) * (h z z)⁻¹ * h z v) • z := fun v => by simp [f]
  have hf' : ∀ v, f' v = v + ((star b - 1) * (h z z)⁻¹ * h z v) • z := fun v => by simp [f']
  have c1 : f ∘ₗ f' = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.comp_apply, LinearMap.id_apply, hf, hf', map_add (f := _), map_smul, smul_eq_mul, add_assoc,
      ← add_smul]
    apply hz0
    linear_combination ((h z z)⁻¹ * h z v) * hb +
      ((h z z)⁻¹ * h z v * (b - 1) * (star b - 1)) * hNi
  have c2 : f' ∘ₗ f = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.comp_apply, LinearMap.id_apply, hf, hf', map_add (f := _), map_smul, smul_eq_mul, add_assoc,
      ← add_smul]
    apply hz0
    linear_combination ((h z z)⁻¹ * h z v) * hb +
      ((h z z)⁻¹ * h z v * (b - 1) * (star b - 1)) * hNi
  refine ⟨LinearEquiv.ofLinear f f' c1 c2, fun a c => ?_, ?_, fun v hv => ?_⟩
  · change h (f a) (f c) = h a c
    rw [hf a, hf c]
    simp only [map_add (f := _), LinearMap.add_apply, map_smul, LinearMap.map_smulₛₗ₂, LinearMap.smul_apply,
      smul_eq_mul, map_mul, map_inv₀, map_sub, map_one, hN]
    rw [← hs.eq z a]
    simp only [starRingEnd_apply]
    linear_combination ((h z z)⁻¹ * star (h z a) * h z c) * hb +
      ((h z z)⁻¹ * star (h z a) * h z c * (b - 1) * (star b - 1)) * hNi
  · change f z = b • z
    rw [hf, mul_assoc, inv_mul_cancel₀ hz, mul_one, sub_smul, one_smul]
    abel
  · change f v = v
    rw [hf, hv, mul_zero, zero_smul, add_zero]

theorem exists_prep (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) {W₁ W₂ : Submodule K V}
    {φ : V ≃ₗ[K] V} (hφ : φ ∈ Formalism.HermitianLatticesTheory.isom h) (hW : ∀ v, v ∈ W₁ ↔ φ v ∈ W₂) {x X : V}
    (hx : x ∈ W₁) (hX : X ∈ W₂) (hxX : h x x = h X X) :
    ∃ φ' ∈ Formalism.HermitianLatticesTheory.isom h, φ' x = X ∧ (∀ v, v ∈ cutW h W₁ x ↔ φ' v ∈ cutW h W₂ X) ∧
      ∀ v, (∀ w ∈ W₁, h w v = 0) → φ' v = φ v := by
  have hφh : ∀ a b, h (φ a) (φ b) = h a b := fun a b => hφ a b
  have hx' : φ x ∈ W₂ := (hW x).1 hx
  obtain ⟨τ, hτ, hτx, hτfix, hτW⟩ := exists_isom_move hs hd (x := φ x) (y := X) (by rw [hφh, hxX])
  have hτh : ∀ a b, h (τ a) (τ b) = h a b := fun a b => hτ a b
  refine ⟨τ * φ, mul_mem hτ hφ, hτx, fun v => ?_, fun v hv => ?_⟩
  · change v ∈ cutW h W₁ x ↔ τ (φ v) ∈ cutW h W₂ X
    rw [mem_cutW, mem_cutW, ← hτW W₂ hx' hX (φ v), ← hW v, ← hτx, hτh, hφh]
  · change τ (φ v) = φ v
    apply hτfix
    · rw [hφh]; exact hv x hx
    · have hX' : φ.symm X ∈ W₁ := (hW _).2 (by rwa [LinearEquiv.apply_symm_apply])
      rw [← LinearEquiv.apply_symm_apply φ X, hφh]
      exact hv _ hX'

theorem mem_iff_of_cut {W₁ W₂ : Submodule K V} {N : AddSubgroup V} (hM : IsLatIn S h W₁ M)
    (hN : IsLatIn S h W₂ N) {x X : V} (hx : x ∈ M) (hX : X ∈ N) (hu : IsUnitIn S (h x x))
    {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (hgx : g x = X)
    (hcut : ∀ v, v ∈ cutM h M x ↔ g v ∈ cutM h N X) : ∀ v, v ∈ M ↔ g v ∈ N := by
  have hgh : ∀ a b, h (g a) (g b) = h a b := fun a b => hg a b
  have hu' : IsUnitIn S (h X X) := by rw [← hgx, hgh]; exact hu
  intro v
  constructor
  · intro hv
    have hp := (hcut _).1 (proj_mem hM hx hu hv)
    have hc : h x v * (h x x)⁻¹ ∈ S := S.mul_mem (hM.int x hx v hv) hu.2.2
    have hgN := (mem_cutM.1 hp).1
    rw [map_sub, map_smul, hgx] at hgN
    have e := N.add_mem hgN (hN.smul_mem _ hc X hX)
    rwa [sub_add_cancel] at e
  · intro hv
    have hp := proj_mem hN hX hu' hv
    have hc : h X (g v) * (h X X)⁻¹ ∈ S := S.mul_mem (hN.int X hX _ hv) hu'.2.2
    have e : g v - (h X (g v) * (h X X)⁻¹) • X = g (v - (h x v * (h x x)⁻¹) • x) := by
      rw [map_sub, map_smul, ← hgx, hgh, hgh]
    rw [e] at hp
    have hm := (mem_cutM.1 ((hcut _).2 hp)).1
    have hc' : h x v * (h x x)⁻¹ ∈ S := by rwa [← hgx, hgh, hgh] at hc
    have e2 := M.add_mem hm (hM.smul_mem _ hc' x hx)
    rwa [sub_add_cancel] at e2

end Formalism.HermitianLattices.Ext.L3.U0
end
end

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.U0

open WA Module

variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem finrank_cutW_lt {W : Submodule K V} {x : V} (hx : x ∈ W) (hxx : h x x ≠ 0) :
    finrank K (cutW h W x) < finrank K W := by
  unfold cutW
  apply Submodule.finrank_lt_finrank_of_lt
  refine lt_of_le_of_ne inf_le_left fun heq => hxx ?_
  have hmem : x ∈ W ⊓ LinearMap.ker (h x) := by
    rw [heq]
    exact hx
  exact LinearMap.mem_ker.mp (Submodule.mem_inf.mp hmem).2

theorem sd_main (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm)
    (hd : ∀ x, h x x = 0 → x = 0) (n : ℕ) :
    ∀ (W₁ W₂ : Submodule K V) (M N : AddSubgroup V) (φ : V ≃ₗ[K] V), finrank K W₁ ≤ n →
      IsSD S h W₁ M → IsSD S h W₂ N → φ ∈ Formalism.HermitianLatticesTheory.isom h → (∀ v, v ∈ W₁ ↔ φ v ∈ W₂) →
      ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, (∀ v, (∀ w ∈ W₁, h w v = 0) → g v = φ v) ∧ ∀ v, v ∈ M ↔ g v ∈ N := by
  induction n with
  | zero =>
    intro W₁ W₂ M N φ hn hM hN hφ hW
    have hbot : W₁ = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hn)
    refine ⟨φ, hφ, fun _ _ => rfl, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
    · have : v = 0 := by
        have := hM.le v hv
        rwa [hbot, Submodule.mem_bot] at this
      rw [this, map_zero]
      exact N.zero_mem
    · have : v = 0 := by
        have := (hW v).mpr (hN.le _ hv)
        rwa [hbot, Submodule.mem_bot] at this
      rw [this]
      exact M.zero_mem
  | succ n ih =>
    intro W₁ W₂ M N φ hn hM hN hφ hW
    by_cases hbot : W₁ = ⊥
    · exact ih W₁ W₂ M N φ (by rw [hbot]; simp) hM hN hφ hW
    obtain ⟨ξ, hξ, hξ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    have hφ' : ∀ a b, h (φ a) (φ b) = h a b := hφ
    obtain ⟨x, hx, hu⟩ := hM.exists_unit_norm hS hπ hs hd hξ hξ0
    obtain ⟨X, hX, hXu⟩ := hN.exists_norm hS hπ hs hd ((hW x).mp (hM.le x hx)) hu (hφ' x x)
    obtain ⟨φ', hφ'i, hφ'x, hφ'W, hφ'fix⟩ := exists_prep hs hd hφ hW (hM.le x hx) (hN.le X hX)
      hXu.symm
    obtain ⟨g, hg, hgfix, hgM⟩ := ih _ _ _ _ φ'
      (by have := finrank_cutW_lt (h := h) (hM.le x hx) hu.1; omega)
      (hM.cut hx hu) (hN.cut hX (by rw [hXu]; exact hu)) hφ'i hφ'W
    have hgx : g x = X := by
      rw [hgfix x fun w hw => symm_zero hs (mem_cutW.mp hw).2, hφ'x]
    refine ⟨g, hg, fun v hv => ?_, mem_iff_of_cut hM.toIsLatIn hN.toIsLatIn hx hX hu hg hgx hgM⟩
    rw [hgfix v fun w hw => hv w (mem_cutW.mp hw).1, hφ'fix v hv]

theorem exists_orth_transfer (hd : ∀ x, h x x = 0 → x = 0) {W₁ W₂ : Submodule K V}
    {ψ : V ≃ₗ[K] V} (hψ : ∀ a b, h (ψ a) (ψ b) = h a b) (hW : ∀ v ∈ W₁, ψ v ∈ W₂) {z₁ z₂ ξ : V}
    (hz₁ : z₁ ∈ W₁) (hz₁0 : z₁ ≠ 0) (hz₂ : z₂ ∈ W₂) (hz₂0 : z₂ ≠ 0) (hξ : ξ ∈ W₁) (hξ0 : ξ ≠ 0)
    (hzξ : h z₁ ξ = 0) : ∃ η ∈ W₂, η ≠ 0 ∧ h z₂ η = 0 := by
  have ha : ψ z₁ ∈ W₂ := hW z₁ hz₁
  have hb : ψ ξ ∈ W₂ := hW ξ hξ
  have haa : h (ψ z₁) (ψ z₁) ≠ 0 := by
    rw [hψ]
    exact fun h0 => hz₁0 (hd z₁ h0)
  have hb0 : ψ ξ ≠ 0 := fun h0 => hξ0 (ψ.injective (h0.trans (map_zero ψ).symm))
  have hab : h (ψ z₁) (ψ ξ) = 0 := by
    rw [hψ]
    exact hzξ
  by_cases h0 : h z₂ (ψ z₁) = 0
  · exact ⟨ψ z₁, ha, fun ha0 => haa (by simp [ha0]), h0⟩
  · refine ⟨(h z₂ (ψ ξ)) • ψ z₁ - (h z₂ (ψ z₁)) • ψ ξ,
      W₂.sub_mem (W₂.smul_mem _ ha) (W₂.smul_mem _ hb), ?_, ?_⟩
    · intro heq
      have hc := congrArg (h (ψ z₁)) heq
      simp only [map_sub, map_smul, smul_eq_mul, hab, mul_zero, sub_zero, map_zero] at hc
      rcases mul_eq_zero.mp hc with hb' | hb'
      · rw [hb', zero_smul, zero_sub, neg_eq_zero, smul_eq_zero] at heq
        exact heq.elim h0 hb0
      · exact haa hb'
    · simp only [map_sub, map_smul, smul_eq_mul]
      ring

theorem IsASD.z_ne {W : Submodule K V} {M : AddSubgroup V} {z : V} (hM : IsASD S π h W M z) :
    z ≠ 0 := by
  intro hz
  exact hM.z_norm_ne (by simp [hz])

theorem IsASD.mem_iff_of_line (hπ : IsUnif S π) {W : Submodule K V} {M : AddSubgroup V} {z : V}
    (hM : IsASD S π h W M z) (hline : ¬ ∃ ξ ∈ W, ξ ≠ 0 ∧ h z ξ = 0) :
    (∀ v ∈ W, v = (h z v * (h z z)⁻¹) • z) ∧ ∀ v, v ∈ M ↔ ∃ c ∈ S, v = c • z := by
  have hζ := hM.z_norm_ne
  have h1 : ∀ v ∈ W, v = (h z v * (h z z)⁻¹) • z := by
    intro v hv
    by_contra hne
    apply hline
    refine ⟨v - (h z v * (h z z)⁻¹) • z, W.sub_mem hv (W.smul_mem _ (hM.le z hM.z_mem)),
      sub_ne_zero.mpr hne, ?_⟩
    simp only [map_sub, map_smul, smul_eq_mul]
    field_simp
    ring
  refine ⟨h1, fun v => ⟨fun hv => ?_, ?_⟩⟩
  · exact ⟨_, mul_inv_mem_of_dv hπ (hM.z_rad v hv) hM.z_norm, h1 v (hM.le v hv)⟩
  · rintro ⟨c, hc, rfl⟩
    exact hM.smul_mem c hc z hM.z_mem

theorem asd_base (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm)
    {W₁ W₂ : Submodule K V} {M N : AddSubgroup V} {z₁ z₂ : V} {φ : V ≃ₗ[K] V}
    (hM : IsASD S π h W₁ M z₁) (hN : IsASD S π h W₂ N z₂) (hφ : φ ∈ Formalism.HermitianLatticesTheory.isom h)
    (hW : ∀ v, v ∈ W₁ ↔ φ v ∈ W₂) (h1 : ¬ ∃ ξ ∈ W₁, ξ ≠ 0 ∧ h z₁ ξ = 0)
    (h2 : ¬ ∃ ξ ∈ W₂, ξ ≠ 0 ∧ h z₂ ξ = 0) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, (∀ v, (∀ w ∈ W₁, h w v = 0) → g v = φ v) ∧ ∀ v, v ∈ M ↔ g v ∈ N := by
  have hφ' : ∀ a b, h (φ a) (φ b) = h a b := hφ
  obtain ⟨-, hMl⟩ := hM.mem_iff_of_line hπ h1
  obtain ⟨hW₂l, hNl⟩ := hN.mem_iff_of_line hπ h2
  have hζ₂ := hN.z_norm_ne
  obtain ⟨l, hl⟩ : ∃ l : K, φ z₁ = l • z₂ := ⟨_, hW₂l _ ((hW z₁).mp (hM.le _ hM.z_mem))⟩
  have hnorm : h z₁ z₁ = star l * l * h z₂ z₂ := by
    rw [← hφ', hl]
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, RingHom.id_apply]
    ring
  have hNl' : IsUnitIn S (star l * l) := by
    have e : star l * l = h z₁ z₁ * π⁻¹ * (h z₂ z₂ * π⁻¹)⁻¹ := by
      rw [hnorm]
      have := hπ.ne
      field_simp
    rw [e]
    exact unit_mul hM.z_norm (unit_inv hN.z_norm)
  obtain ⟨b, hb, hlb⟩ := exists_norm_one_mul_mem hS hNl'.2.1
  have hlbu : IsUnitIn S (l * b) := by
    apply isUnitIn_of_mul (hS.star_mem _ hlb) hlb
    have e : star (l * b) * (l * b) = star l * l := by
      rw [star_mul']
      linear_combination (star l * l) * hb
    rw [e]
    exact hNl'
  obtain ⟨ψ, hψ, hψz, hψfix⟩ := exists_isom_scale hs hζ₂ hb
  have hgz : ψ (φ z₁) = (l * b) • z₂ := by rw [hl, map_smul, hψz, smul_smul]
  refine ⟨ψ * φ, mul_mem hψ hφ, fun v hv => ?_, fun v => ?_⟩
  · change ψ (φ v) = φ v
    apply hψfix
    have h3 : φ.symm z₂ ∈ W₁ := by rw [hW, φ.apply_symm_apply]; exact hN.le _ hN.z_mem
    have := hv _ h3
    rwa [← hφ', φ.apply_symm_apply] at this
  · change v ∈ M ↔ ψ (φ v) ∈ N
    rw [hMl, hNl]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c * (l * b), S.mul_mem hc hlb, by rw [map_smul, map_smul, hgz, smul_smul]⟩
    · rintro ⟨c, hc, hv⟩
      refine ⟨c * (l * b)⁻¹, S.mul_mem hc hlbu.2.2, ?_⟩
      apply φ.injective
      apply ψ.injective
      rw [hv, map_smul, map_smul, hgz, smul_smul, mul_assoc, inv_mul_cancel₀ hlbu.1, mul_one]

theorem asd_main (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm)
    (hd : ∀ x, h x x = 0 → x = 0) (n : ℕ) :
    ∀ (W₁ W₂ : Submodule K V) (M N : AddSubgroup V) (z₁ z₂ : V) (φ : V ≃ₗ[K] V),
      finrank K W₁ ≤ n → IsASD S π h W₁ M z₁ → IsASD S π h W₂ N z₂ → φ ∈ Formalism.HermitianLatticesTheory.isom h →
      (∀ v, v ∈ W₁ ↔ φ v ∈ W₂) →
      ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, (∀ v, (∀ w ∈ W₁, h w v = 0) → g v = φ v) ∧ ∀ v, v ∈ M ↔ g v ∈ N := by
  induction n with
  | zero =>
    intro W₁ W₂ M N z₁ z₂ φ hn hM hN hφ hW
    exfalso
    have hbot : W₁ = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hn)
    have := hM.le _ hM.z_mem
    rw [hbot, Submodule.mem_bot] at this
    exact hM.z_ne this
  | succ n ih =>
    intro W₁ W₂ M N z₁ z₂ φ hn hM hN hφ hW
    have hφ' : ∀ a b, h (φ a) (φ b) = h a b := hφ
    by_cases h1 : ∃ ξ ∈ W₁, ξ ≠ 0 ∧ h z₁ ξ = 0
    · obtain ⟨ξ, hξ, hξ0, hzξ⟩ := h1
      obtain ⟨η, hη, hη0, hzη⟩ := exists_orth_transfer hd hφ' (fun v hv => (hW v).mp hv)
        (hM.le _ hM.z_mem) hM.z_ne (hN.le _ hN.z_mem) hN.z_ne hξ hξ0 hzξ
      obtain ⟨x, hx, hu⟩ := hM.exists_unit_norm hS hπ hs hd hξ hξ0 hzξ
      obtain ⟨w₀, hw₀, hw₀u⟩ := hN.exists_unit_norm hS hπ hs hd hη hη0 hzη
      obtain ⟨X, hX, hXu⟩ := hN.exists_norm hS hπ hs hd ((hW x).mp (hM.le x hx)) hu (hφ' x x)
        hw₀ hw₀u
      obtain ⟨φ', hφ'i, hφ'x, hφ'W, hφ'fix⟩ := exists_prep hs hd hφ hW (hM.le x hx) (hN.le X hX)
        hXu.symm
      obtain ⟨g, hg, hgfix, hgM⟩ := ih _ _ _ _ _ _ φ'
        (by have := finrank_cutW_lt (h := h) (hM.le x hx) hu.1; omega)
        (hM.cut hS hπ hs hx hu) (hN.cut hS hπ hs hX (by rw [hXu]; exact hu)) hφ'i hφ'W
      have hgx : g x = X := by
        rw [hgfix x fun w hw => symm_zero hs (mem_cutW.mp hw).2, hφ'x]
      refine ⟨g, hg, fun v hv => ?_, mem_iff_of_cut hM.toIsLatIn hN.toIsLatIn hx hX hu hg hgx hgM⟩
      rw [hgfix v fun w hw => hv w (mem_cutW.mp hw).1, hφ'fix v hv]
    · refine asd_base hS hπ hs hM hN hφ hW h1 ?_
      rintro ⟨η, hη, hη0, hzη⟩
      apply h1
      have hsym : ∀ a b, h (φ.symm a) (φ.symm b) = h a b := by
        intro a b
        rw [← hφ', φ.apply_symm_apply, φ.apply_symm_apply]
      exact exists_orth_transfer hd hsym
        (fun v hv => by rw [hW, φ.apply_symm_apply]; exact hv)
        (hN.le _ hN.z_mem) hN.z_ne (hM.le _ hM.z_mem) hM.z_ne hη hη0 hzη

end Formalism.HermitianLattices.Ext.L3.U0
