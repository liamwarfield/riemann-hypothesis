module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IsFixMapIff

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LatticeFrames.ExistsPsi
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LatticeFrames.ExistsFrame
namespace UpperTheory.V.Z.Sym.Loc.CP

open IsLocalRing

variable {O K V : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {Δ : K}
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] {B : V →ₗ[K] V →ₗ[K] K} {S : Submodule O V}

theorem exists_smul_mem (L : IsLoc O Δ) (hf : S.FG) (hd : ∀ y, y ∈ S ↔ ∀ x ∈ S, B x y ∈ (algebraMap O K).range) (y : V) :
    ∃ k : K, k ≠ 0 ∧ k • y ∈ S := by
  haveI := L.frac
  classical
  obtain ⟨s, rfl⟩ := hf
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors O) (s.image fun x => B x y)
  refine ⟨algebraMap O K b, (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 (nonZeroDivisors.ne_zero b.2), (hd _).2 fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha⟩ := hb _ (Finset.mem_image_of_mem _ hx)
    exact ⟨a, by rw [ha, map_smul, Algebra.smul_def, smul_eq_mul]⟩
  | zero => simp
  | add a b _ _ ha hb => rw [map_add (f := _), LinearMap.add_apply]; exact add_mem ha hb
  | smul a x _ hx =>
    rw [← algebraMap_smul K a x, LinearMap.map_smul₂, smul_eq_mul]
    exact mul_mem ⟨a, rfl⟩ hx

theorem exists_unit (L : IsLoc O Δ) (hB : ∀ x y, B x y = B y x) (hf : S.FG) (hd : ∀ y, y ∈ S ↔ ∀ x ∈ S, B x y ∈ (algebraMap O K).range)
    (P : V →ₗ[K] V) (hP : ∀ x ∈ S, P x ∈ S) (hPP : ∀ x, P (P x) = P x) (hadj : ∀ x y, B x (P y) = B (P x) (P y)) (h0 : P ≠ 0) :
    ∃ v ∈ S, P v = v ∧ ∃ u : Oˣ, B v v = algebraMap O K u := by
  haveI := L.frac
  by_contra hn
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hp' : algebraMap O K p ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hp.ne_zero
  have h1 : ∀ v ∈ S, ∃ a : O, B (P v) (P v) = algebraMap O K (p * a) := fun v hv => by
    obtain ⟨a, ha⟩ := (hd _).1 (hP v hv) _ (hP v hv)
    have : a ∈ maximalIdeal O := fun hu => hn ⟨P v, hP v hv, hPP v, hu.unit, ha.symm⟩
    rw [hp.maximalIdeal_eq, Ideal.mem_span_singleton] at this
    obtain ⟨b, rfl⟩ := this
    exact ⟨b, ha.symm⟩
  obtain ⟨i, hi⟩ := L.two.exists_right_inv
  have hi' : (2 : K) * algebraMap O K i = 1 := by rw [← map_ofNat (algebraMap O K) 2, ← map_mul, hi, map_one]
  have h2 : ∀ v ∈ S, (algebraMap O K p)⁻¹ • P v ∈ S := fun v hv => (hd _).2 fun w hw => by
    obtain ⟨a, ha⟩ := h1 v hv
    obtain ⟨b, hb⟩ := h1 w hw
    obtain ⟨c, hc⟩ := h1 (v + w) (add_mem hv hw)
    simp only [map_add (f := _), LinearMap.add_apply, map_mul] at ha hb hc
    refine ⟨i * (c - a - b), ?_⟩
    rw [map_smul, hadj, smul_eq_mul, map_mul, map_sub, map_sub]
    rw [hB (P v) (P w)] at hc
    field_simp
    linear_combination (-algebraMap O K i) * hc + algebraMap O K i * ha + algebraMap O K i * hb + B (P w) (P v) * hi'
  have h3 : S.map (P.restrictScalars O) = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal O) _ (hf.map _) ?_ (maximalIdeal_le_jacobson _)
    rintro _ ⟨v, hv, rfl⟩
    have : (P.restrictScalars O) v = p • (P.restrictScalars O) ((algebraMap O K p)⁻¹ • P v) := by
      simp only [LinearMap.restrictScalars_apply, map_smul, hPP]
      rw [← algebraMap_smul K p, smul_smul, mul_inv_cancel₀ hp', one_smul]
    rw [this]
    exact Submodule.smul_mem_smul hp.not_isUnit ⟨_, h2 v hv, rfl⟩
  refine h0 (LinearMap.ext fun y => ?_)
  obtain ⟨k, hk, hy⟩ := exists_smul_mem L hf hd y
  have : P (k • y) = 0 := (Submodule.eq_bot_iff _).1 h3 _ ⟨_, hy, rfl⟩
  rw [map_smul] at this
  exact (smul_eq_zero.1 this).resolve_left hk

theorem not_span_two (h3 : Module.finrank K V = 3) (a b : V) (h : ∀ x, ∃ s t : K, x = s • a + t • b) : False := by
  have := finrank_le_of_span_eq_top (R := K) (v := ![a, b]) (by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨s, t, rfl⟩ := h x
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)) (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)))
  simp [h3] at this

theorem exists_frame (L : IsLoc O Δ) (h3 : Module.finrank K V = 3) (hB : ∀ x y, B x y = B y x) (hf : S.FG)
    (hd : ∀ y, y ∈ S ↔ ∀ x ∈ S, B x y ∈ (algebraMap O K).range) :
    ∃ e ∈ S, ∃ f ∈ S, ∃ h ∈ S, ∃ η : Oˣ, B e e = 0 ∧ B f f = 0 ∧ B e f = 1 ∧ B e h = 0 ∧ B f h = 0 ∧ B h h = algebraMap O K η ∧
      ∀ v ∈ S, ∃ a b c : O, v = a • e + b • f + c • h := by
  haveI := L.frac
  have sm : ∀ (a : O) (x : V), algebraMap O K a • x = a • x := fun a x => algebraMap_smul K a x
  have un : ∀ u : Oˣ, algebraMap O K u ≠ 0 := fun u => (u.isUnit.map _).ne_zero
  have iv : ∀ u : Oˣ, (algebraMap O K u)⁻¹ = algebraMap O K (u⁻¹ : Oˣ) := fun u =>
    inv_eq_of_mul_eq_one_right (by rw [← map_mul, Units.mul_inv, map_one])
  have pm : ∀ (e : V) (u : Oˣ), e ∈ S → ∀ x ∈ S, ∀ g ∈ S, ((algebraMap O K u)⁻¹ * B e x) • g ∈ S := fun e u he x hx g hg => by
    obtain ⟨a, ha⟩ := (hd x).1 hx e he
    rw [iv, ← ha, ← map_mul, sm]; exact S.smul_mem _ hg
  obtain ⟨e₁, m₁, -, u₁, q₁⟩ := exists_unit L hB hf hd LinearMap.id (fun _ h => h) (fun _ => rfl) (fun _ _ => rfl) fun h =>
    not_span_two h3 0 0 fun x => ⟨0, 0, by simpa using LinearMap.congr_fun h x⟩
  let P₂ : V →ₗ[K] V := LinearMap.id - ((algebraMap O K u₁)⁻¹ • B e₁).smulRight e₁
  have a₂ : ∀ x, P₂ x = x - ((algebraMap O K u₁)⁻¹ * B e₁ x) • e₁ := fun x => rfl
  have o₂ : ∀ x, B e₁ (P₂ x) = 0 := fun x => by rw [a₂, map_sub, map_smul, q₁, smul_eq_mul]; field_simp [un u₁]; ring
  obtain ⟨e₂, m₂, p₂, u₂, q₂⟩ := exists_unit L hB hf hd P₂ (fun x hx => sub_mem hx (pm e₁ u₁ m₁ x hx _ m₁))
    (fun x => by rw [a₂ (P₂ x), o₂]; simp) (fun x y => by rw [a₂ x, LinearMap.map_sub₂, LinearMap.map_smul₂, o₂]; simp) fun h =>
    not_span_two h3 e₁ 0 fun x => ⟨_, 0, by simpa [a₂, sub_eq_zero] using LinearMap.congr_fun h x⟩
  have b12 : B e₁ e₂ = 0 := p₂ ▸ o₂ e₂
  have b21 : B e₂ e₁ = 0 := hB _ _ ▸ b12
  let P₃ : V →ₗ[K] V := P₂ - ((algebraMap O K u₂)⁻¹ • B e₂).smulRight e₂
  have a₃ : ∀ x, P₃ x = x - ((algebraMap O K u₁)⁻¹ * B e₁ x) • e₁ - ((algebraMap O K u₂)⁻¹ * B e₂ x) • e₂ := fun x => rfl
  have o₃ : ∀ x, B e₁ (P₃ x) = 0 := fun x => by simp only [a₃, map_sub, map_smul, q₁, b12, smul_eq_mul]; field_simp [un u₁]; ring
  have o₃' : ∀ x, B e₂ (P₃ x) = 0 := fun x => by simp only [a₃, map_sub, map_smul, q₂, b21, smul_eq_mul]; field_simp [un u₂]; ring
  obtain ⟨e₃, m₃, p₃, u₃, q₃⟩ := exists_unit L hB hf hd P₃ (fun x hx => sub_mem (sub_mem hx (pm e₁ u₁ m₁ x hx _ m₁)) (pm e₂ u₂ m₂ x hx _ m₂))
    (fun x => by rw [a₃ (P₃ x), o₃, o₃']; simp)
    (fun x y => by rw [a₃ x, LinearMap.map_sub₂, LinearMap.map_sub₂, LinearMap.map_smul₂, LinearMap.map_smul₂, o₃, o₃']; simp) fun h =>
    not_span_two h3 e₁ e₂ fun x => ⟨_, _, by
      have := LinearMap.congr_fun h x
      rw [a₃, sub_sub, LinearMap.zero_apply, sub_eq_zero] at this
      exact this⟩
  have b13 : B e₁ e₃ = 0 := p₃ ▸ o₃ e₃
  have b23 : B e₂ e₃ = 0 := p₃ ▸ o₃' e₃
  have b31 : B e₃ e₁ = 0 := hB _ _ ▸ b13
  have b32 : B e₃ e₂ = 0 := hB _ _ ▸ b23
  obtain ⟨a, b, hab⟩ := L.nm_unit (-(u₂ * u₁⁻¹)) (-(u₃ * u₁⁻¹))
  have hab' : algebraMap O K u₁ * algebraMap O K a ^ 2 + algebraMap O K u₂ * algebraMap O K b ^ 2 + algebraMap O K u₃ = 0 := by
    have := congrArg (algebraMap O K) hab
    simp only [Units.val_neg, Units.val_mul, map_sub, map_mul, map_neg, map_pow, ← iv] at this
    have h1 := un u₁
    field_simp at this
    linear_combination this
  let t : Oˣ := L.two.unit * u₃
  have ht : algebraMap O K t = 2 * algebraMap O K u₃ := by simp [t, map_ofNat]
  have h2 : (2 : K) ≠ 0 := fun h => un t (by rw [ht, h, zero_mul])
  set A := algebraMap O K a with hA
  set C := algebraMap O K b with hC
  let e := A • e₁ + C • e₂ + e₃
  let f := (algebraMap O K t)⁻¹ • (e₃ - A • e₁ - C • e₂)
  let h := (algebraMap O K u₂ * C) • e₁ - (algebraMap O K u₁ * A) • e₂
  have me : e ∈ S := add_mem (add_mem (by rw [hA, sm]; exact S.smul_mem _ m₁) (by rw [hC, sm]; exact S.smul_mem _ m₂)) m₃
  have mf : f ∈ S := by
    simp only [f]
    rw [iv, sm]
    exact S.smul_mem _ (sub_mem (sub_mem m₃ (by rw [hA, sm]; exact S.smul_mem _ m₁)) (by rw [hC, sm]; exact S.smul_mem _ m₂))
  have mh : h ∈ S := sub_mem (by rw [hC, ← map_mul, sm]; exact S.smul_mem _ m₁) (by rw [hA, ← map_mul, sm]; exact S.smul_mem _ m₂)
  have n₃ := un u₃
  have g1 : B e e = 0 := by simp [e, q₁, q₂, q₃, b12, b21, b13, b31, b23, b32]; linear_combination hab'
  have g2 : B f f = 0 := by
    simp [f, q₁, q₂, q₃, b12, b21, b13, b31, b23, b32, ht]
    field_simp
    first | linear_combination hab' | (right; right; linear_combination hab') | (simp [h2, n₃]; linear_combination hab')
  have g3 : B e f = 1 := by simp [e, f, q₁, q₂, q₃, b12, b21, b13, b31, b23, b32, ht]; field_simp; linear_combination -hab'
  have g4 : B e h = 0 := by simp [e, h, q₁, q₂, q₃, b12, b21, b13, b31, b23, b32]; ring
  have g5 : B f h = 0 := by
    simp only [f, h, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, q₁, q₂, b12, b21, b31, b32]; ring
  have g6 : B h h = algebraMap O K (-(u₁ * u₂ * u₃) : Oˣ) := by
    simp [h, q₁, q₂, q₃, b12, b21]; linear_combination (algebraMap O K u₁ * algebraMap O K u₂) * hab'
  refine ⟨e, me, f, mf, h, mh, _, g1, g2, g3, g4, g5, g6, fun v hv => ?_⟩
  set η : Oˣ := -(u₁ * u₂ * u₃)
  have g3' : B f e = 1 := hB _ _ ▸ g3
  have g4' : B h e = 0 := hB _ _ ▸ g4
  have g5' : B h f = 0 := hB _ _ ▸ g5
  have li : LinearIndependent K ![e, f, h] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_three] at hg
    have k1 := congrArg (B f) hg
    have k2 := congrArg (B e) hg
    have k3 := congrArg (B h) hg
    simp [g1, g2, g3, g4, g5, g6, g3', g4', g5', un η] at k1 k2 k3
    intro i; fin_cases i <;> assumption
  have sp := li.span_eq_top_of_card_eq_finrank (by simp [h3])
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 (sp ▸ Submodule.mem_top : v ∈ Submodule.span K (Set.range ![e, f, h]))
  rw [Fin.sum_univ_three] at hg
  obtain ⟨x, hx⟩ := (hd v).1 hv f mf
  obtain ⟨y, hy⟩ := (hd v).1 hv e me
  obtain ⟨z, hz⟩ := (hd v).1 hv h mh
  rw [← hg] at hx hy hz
  simp [g1, g2, g3, g4, g5, g6, g3', g4', g5'] at hx hy hz
  refine ⟨x, y, z * (η⁻¹ : Oˣ), ?_⟩
  rw [← sm, ← sm, ← sm, map_mul, hx, hy, hz, ← iv, mul_inv_cancel_right₀ (un η)]
  exact hg.symm

end UpperTheory.V.Z.Sym.Loc.CP
end

noncomputable section

namespace UpperTheory.V.Z.Sym.Loc.CP

open QuadraticAlgebra

variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {Δ τ : K}


variable (τ) in
def Bf (τ c t : K) : K × Etau K τ →ₗ[K] K × Etau K τ →ₗ[K] K :=
  LinearMap.mk₂ K (fun v w => c * v.1 * w.1 + t * QuadraticAlgebra.trace (v.2 * star w.2))
    (fun a b w => by simp [QuadraticAlgebra.trace_def]; ring) (fun a b w => by simp [QuadraticAlgebra.trace_def]; ring)
    (fun a b w => by simp [QuadraticAlgebra.trace_def]; ring) (fun a b w => by simp [QuadraticAlgebra.trace_def]; ring)

theorem Bf_apply (c t : K) (v w : K × Etau K τ) : Bf τ c t v w = c * v.1 * w.1 + t * QuadraticAlgebra.trace (v.2 * star w.2) := rfl

theorem Bf_symm (c t : K) (v w : K × Etau K τ) : Bf τ c t v w = Bf τ c t w v := by
  simp [Bf_apply, QuadraticAlgebra.trace_def]; ring

def psi (s : K) (β : Etau K τ) : K × Etau K τ →ₗ[K] Etau K τ →ₗ[K] Etau K τ :=
  LinearMap.mk₂ K (fun v y => s • (v.1 • ((ω - star ω) * y) + v.2 * β * star y))
    (fun a b w => by ext <;> simp <;> ring) (fun a b w => by ext <;> simp <;> ring)
    (fun a b w => by ext <;> simp <;> ring) (fun a b w => by ext <;> simp <;> ring)

theorem psi_apply (s : K) (β : Etau K τ) (v : K × Etau K τ) (y : Etau K τ) :
    psi s β v y = s • (v.1 • ((ω - star ω) * y) + v.2 * β * star y) := rfl

theorem psi_anti {c t s ε : K} {β : Etau K τ} (hc : c = (τ ^ 2 - 4) * ε * s ^ 2) (hβ : QuadraticAlgebra.norm β * ε * s ^ 2 = 2 * t)
    (v w : K × Etau K τ) (y : Etau K τ) : ε • (psi s β v (psi s β w y) + psi s β w (psi s β v y)) = (2 * Bf τ c t v w) • y := by
  subst hc
  rw [QuadraticAlgebra.norm_def] at hβ
  ext <;> simp [psi_apply, Bf_apply, QuadraticAlgebra.trace_def]
  · linear_combination (2 * v.2.re * w.2.re + τ * v.2.re * w.2.im + 2 * v.2.im * w.2.im + τ * v.2.im * w.2.re) * y.re * hβ
  · linear_combination (2 * v.2.re * w.2.re + τ * v.2.re * w.2.im + 2 * v.2.im * w.2.im + τ * v.2.im * w.2.re) * y.im * hβ

theorem psi_quo (s : K) (β : Etau K τ) (z : (Etau K τ)ˣ) (v : K × Etau K τ) (y : Etau K τ) :
    psi s β (v.1, quo z * v.2) ((z : Etau K τ) * y) = (z : Etau K τ) * psi s β v y := by
  have h1 : star ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) * star (z : Etau K τ) = 1 := by
    rw [← star_mul, Units.mul_inv, star_one]
  simp only [psi_apply, quo, star_mul, Algebra.smul_def]
  linear_combination (algebraMap K (Etau K τ) s * (z : Etau K τ) * v.2 * β * star y) * h1

theorem psi_inj {s : K} {β : Etau K τ} (hD : τ ^ 2 - 4 ≠ 0) (hs : s ≠ 0) (hβ : IsUnit β) {v : K × Etau K τ} (h : ∀ y, psi s β v y = 0) : v = 0 := by
  have h1 := h 1
  have h2 := h ω
  simp only [psi_apply, Algebra.smul_def] at h1 h2
  have hs' : IsUnit (algebraMap K (Etau K τ) s) := (isUnit_iff_ne_zero.mpr hs).map _
  rw [hs'.mul_right_eq_zero] at h1 h2
  simp only [star_one, mul_one] at h1
  have hΩ2 : (ω - star ω : Etau K τ) * (ω - star ω) = algebraMap K (Etau K τ) (τ ^ 2 - 4) := by
    ext <;> simp [pow_two] <;> ring
  have key : algebraMap K (Etau K τ) (v.1 * (τ ^ 2 - 4)) = 0 := by
    rw [map_mul, ← hΩ2]; linear_combination h2 - star ω * h1
  have hv1 : v.1 = 0 :=
    (mul_eq_zero.mp ((algebraMap K (Etau K τ)).injective (key.trans (map_zero _).symm))).resolve_right hD
  have hv2 : v.2 = 0 := by
    rw [hv1, map_zero, zero_mul, zero_add] at h1
    exact hβ.mul_left_eq_zero.mp h1
  exact Prod.ext hv1 hv2

theorem exists_psi {s : K} {β : Etau K τ} (hD : τ ^ 2 - 4 ≠ 0) (hs : s ≠ 0) (hβ : IsUnit β) (y y' : Etau K τ) :
    ∃ v, ∀ b, psi s β v b = (b * star y).im • y' + (b * star y').im • y := by
  have hDu : IsUnit (algebraMap K (Etau K τ) (τ ^ 2 - 4)) := (isUnit_iff_ne_zero.mpr hD).map _
  have hΩ2 : (ω - star ω : Etau K τ) * (ω - star ω) = algebraMap K (Etau K τ) (τ ^ 2 - 4) := by
    ext <;> simp [pow_two] <;> ring
  have hΩu : IsUnit (ω - star ω : Etau K τ) := isUnit_of_mul_isUnit_left (hΩ2 ▸ hDu)
  have htr : algebraMap K (Etau K τ) (QuadraticAlgebra.trace (star y * y')) = star y * y' + y * star y' := by
    ext <;> simp [QuadraticAlgebra.trace_def] <;> ring
  have hk : algebraMap K (Etau K τ) s * algebraMap K (Etau K τ) (s * (τ ^ 2 - 4))⁻¹ *
      algebraMap K (Etau K τ) (τ ^ 2 - 4) = 1 := by
    rw [← map_mul, ← map_mul, ← map_one (algebraMap K (Etau K τ))]; congr 1; field_simp
  have hsub : ∀ z : Etau K τ, algebraMap K (Etau K τ) z.im * (ω - star ω) = z - star z := by
    intro z; rw [QuadraticAlgebra.sub_star z, Algebra.smul_def]
  have hinv : ((hβ.unit⁻¹ : (Etau K τ)ˣ) : Etau K τ) * β = 1 := by
    have := hβ.unit.inv_mul; rwa [hβ.unit_spec] at this
  refine ⟨((s * (τ ^ 2 - 4))⁻¹ * QuadraticAlgebra.trace (star y * y'),
    -(2 * (algebraMap K (Etau K τ) (s * (τ ^ 2 - 4))⁻¹ *
      (y * y' * (ω - star ω) * ((hβ.unit⁻¹ : (Etau K τ)ˣ) : Etau K τ))))), fun b => ?_⟩
  have hs1 := hsub (b * star y)
  have hs2 := hsub (b * star y')
  rw [star_mul, star_star] at hs1 hs2
  apply hΩu.mul_left_cancel
  simp only [psi_apply, Algebra.smul_def, map_mul]
  linear_combination
    (algebraMap K (Etau K τ) s * algebraMap K (Etau K τ) (s * (τ ^ 2 - 4))⁻¹ *
        algebraMap K (Etau K τ) (QuadraticAlgebra.trace (star y * y')) * b -
      2 * algebraMap K (Etau K τ) s * algebraMap K (Etau K τ) (s * (τ ^ 2 - 4))⁻¹ * y * y' *
        ((hβ.unit⁻¹ : (Etau K τ)ˣ) : Etau K τ) * β * star b) * hΩ2 +
    (algebraMap K (Etau K τ) (QuadraticAlgebra.trace (star y * y')) * b -
      2 * y * y' * ((hβ.unit⁻¹ : (Etau K τ)ˣ) : Etau K τ) * β * star b) * hk +
    (-2 * y * y' * star b) * hinv + b * htr - y' * hs1 - y * hs2


variable (O) in
def S0 (s : K) (β : Etau K τ) (Λ : Set (Etau K τ)) : Set (K × Etau K τ) := {v | ∀ y ∈ Λ, psi s β v y ∈ Λ}


variable (O) in
structure Uni (c t : K) (S : Set (K × Etau K τ)) : Prop where
  fg : ∃ s : Finset (K × Etau K τ), S = Submodule.span O (s : Set (K × Etau K τ))
  dual : ∀ y, y ∈ S ↔ ∀ x ∈ S, Bf τ c t x y ∈ (algebraMap O K).range

theorem coord {y₁ y₂ : Etau K τ} (hg : (y₂ * star y₁).im ≠ 0) (b : Etau K τ) :
    b = (-(b * star y₂).im / (y₂ * star y₁).im) • y₁ + ((b * star y₁).im / (y₂ * star y₁).im) • y₂ := by
  have key : (y₂ * star y₁).im • b = (-(b * star y₂).im) • y₁ + (b * star y₁).im • y₂ := by
    ext <;> simp <;> ring
  calc b = ((y₂ * star y₁).im)⁻¹ • ((y₂ * star y₁).im • b) := by
        rw [smul_smul, inv_mul_cancel₀ hg, one_smul]
    _ = _ := by rw [key, smul_add, smul_smul, smul_smul, div_eq_inv_mul, div_eq_inv_mul]

theorem coord_uniq {y₁ y₂ : Etau K τ} (hg : (y₂ * star y₁).im ≠ 0) {a b a' b' : K} (h : a • y₁ + b • y₂ = a' • y₁ + b' • y₂) : a = a' ∧ b = b' := by
  have e1 := congrArg (fun z => (z * star y₁).im) h
  have e2 := congrArg (fun z => (z * star y₂).im) h
  simp only [add_mul, smul_mul_assoc, im_add, im_smul, smul_eq_mul] at e1 e2
  have n1 : (y₁ * star y₁).im = 0 := by
    rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star, QuadraticAlgebra.algebraMap_im]
  have n2 : (y₂ * star y₂).im = 0 := by
    rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star, QuadraticAlgebra.algebraMap_im]
  have h12 : (y₁ * star y₂).im = -(y₂ * star y₁).im := by
    rw [← im_star, star_mul, star_star]
  rw [n1] at e1
  rw [n2, h12] at e2
  constructor
  · have : (a - a') * (y₂ * star y₁).im = 0 := by linear_combination -e2
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hg)
  · have : (b - b') * (y₂ * star y₁).im = 0 := by linear_combination e1
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hg)

theorem exists_efh {s : K} {β : Etau K τ} (hD : τ ^ 2 - 4 ≠ 0) (h2 : (2 : K) ≠ 0) (hs : s ≠ 0) (hβ : IsUnit β) {y₁ y₂ : Etau K τ}
    (hg : (y₂ * star y₁).im ≠ 0) : ∃ e f h, psi s β e y₁ = 0 ∧ psi s β e y₂ = y₁ ∧ psi s β f y₁ = y₂ ∧ psi s β f y₂ = 0 ∧
      psi s β h y₁ = -y₁ ∧ psi s β h y₂ = y₂ := by
  have n1 : (y₁ * star y₁).im = 0 := by
    rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star, QuadraticAlgebra.algebraMap_im]
  have n2 : (y₂ * star y₂).im = 0 := by
    rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star, QuadraticAlgebra.algebraMap_im]
  have h12 : (y₁ * star y₂).im = -(y₂ * star y₁).im := by
    rw [← im_star, star_mul, star_star]
  have hstar : ∀ (k : K) (x : Etau K τ), star (k • x) = k • star x := by
    intro k x; ext <;> simp <;> ring
  set G := (y₂ * star y₁).im with hG
  obtain ⟨e, he⟩ := exists_psi hD hs hβ y₁ ((2 * G)⁻¹ • y₁)
  obtain ⟨f, hf⟩ := exists_psi hD hs hβ y₂ ((-(2 * G))⁻¹ • y₂)
  obtain ⟨h, hh⟩ := exists_psi hD hs hβ y₁ (G⁻¹ • y₂)
  refine ⟨e, f, h, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [he, hf, hh, hstar, mul_smul_comm, im_smul, smul_eq_mul, n1, n2, h12, ← hG, zero_smul,
      mul_zero, zero_add, add_zero, smul_smul, ← add_smul]
  all_goals (ext <;> simp <;> field_simp <;> ring)

end UpperTheory.V.Z.Sym.Loc.CP
end
end

noncomputable section

namespace UpperTheory.V.Z.Sym.Loc.CP

open QuadraticAlgebra

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {Δ τ : K}

theorem lat_basis (L : IsLoc O Δ) (hD : τ ^ 2 - 4 ≠ 0) {Λ : Set (Etau K τ)} (h : IsLat O τ Λ) :
    ∃ y₁ y₂ : Etau K τ, (y₂ * star y₁).im ≠ 0 ∧ ∀ b, b ∈ Λ ↔ ∃ p q : O, b = algebraMap O K p • y₁ + algebraMap O K q • y₂ := by
  obtain ⟨y, x, hx, -, -, rfl⟩ := latCls O K Δ τ L hD Λ h
  have hs : ∀ (p : O) (z : Etau K τ), p • z = algebraMap O K p • z := fun p z => (algebraMap_smul K p z).symm
  have hn : QuadraticAlgebra.norm (y : Etau K τ) ≠ 0 :=
    (QuadraticAlgebra.isUnit_iff_norm_isUnit.mp y.isUnit).ne_zero
  refine ⟨y, y * x, ?_, ?_⟩
  · have e : (y : Etau K τ) * x * star (y : Etau K τ) = x * algebraMap K _ (QuadraticAlgebra.norm (y : Etau K τ)) := by
      rw [QuadraticAlgebra.algebraMap_norm_eq_mul_star]
      ring
    rw [e, QuadraticAlgebra.im_mul]
    simp
    exact ⟨hx, hn⟩
  · intro b
    simp only [Set.mem_image, SetLike.mem_coe, Submodule.mem_span_pair]
    constructor
    · rintro ⟨z, ⟨p, q, rfl⟩, rfl⟩
      refine ⟨p, q, ?_⟩
      rw [hs, hs, mul_add, mul_smul_comm, mul_smul_comm, mul_one]
    · rintro ⟨p, q, rfl⟩
      refine ⟨p • 1 + q • x, ⟨p, q, rfl⟩, ?_⟩
      rw [hs, hs, mul_add, mul_smul_comm, mul_smul_comm, mul_one]

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem mem_S0_of_sum_eq {s : K} {β y₁ y₂ : Etau K τ} {Λ : Set (Etau K τ)} (h : ∀ b, b ∈ Λ ↔ ∃ p q : O, b = algebraMap O K p • y₁ + algebraMap O K q • y₂)
    {v : K × Etau K τ} : v ∈ S0 s β Λ ↔ psi s β v y₁ ∈ Λ ∧ psi s β v y₂ ∈ Λ := by
  simp only [S0, Set.mem_setOf_eq]
  constructor
  · intro hv
    exact ⟨hv _ ((h _).2 ⟨1, 0, by simp⟩), hv _ ((h _).2 ⟨0, 1, by simp⟩)⟩
  · rintro ⟨h1, h2⟩ y hy
    obtain ⟨p, q, rfl⟩ := (h _).1 hy
    obtain ⟨p1, q1, e1⟩ := (h _).1 h1
    obtain ⟨p2, q2, e2⟩ := (h _).1 h2
    refine (h _).2 ⟨p * p1 + q * p2, p * q1 + q * q2, ?_⟩
    rw [map_add (f := _), map_smul, map_smul, e1, e2]
    simp only [map_add (f := _), map_mul, smul_add, smul_smul, add_smul]
    abel

variable {c t s : K} {ε : Oˣ} {β : Etau K τ}

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem Bf_int (L2 : IsUnit (2 : O)) (hc : c = (τ ^ 2 - 4) * algebraMap O K ε * s ^ 2) (hβ : QuadraticAlgebra.norm β * algebraMap O K ε * s ^ 2 = 2 * t)
    {y₁ y₂ : Etau K τ} (hg : (y₂ * star y₁).im ≠ 0) {Λ : Set (Etau K τ)}
    (h : ∀ b, b ∈ Λ ↔ ∃ p q : O, b = algebraMap O K p • y₁ + algebraMap O K q • y₂) {v w : K × Etau K τ} (hv : v ∈ S0 s β Λ) (hw : w ∈ S0 s β Λ) :
    Bf τ c t v w ∈ (algebraMap O K).range := by
  have hadd : ∀ a b, a ∈ Λ → b ∈ Λ → a + b ∈ Λ := by
    intro a b ha hb
    obtain ⟨p, q, rfl⟩ := (h _).1 ha
    obtain ⟨p', q', rfl⟩ := (h _).1 hb
    refine (h _).2 ⟨p + p', q + q', ?_⟩
    simp only [map_add (f := _), add_smul]
    abel
  have hsm : ∀ (r : O) a, a ∈ Λ → algebraMap O K r • a ∈ Λ := by
    intro r a ha
    obtain ⟨p, q, rfl⟩ := (h _).1 ha
    refine (h _).2 ⟨r * p, r * q, ?_⟩
    simp only [map_mul, smul_add, smul_smul]
  have h1 : y₁ ∈ Λ := (h _).2 ⟨1, 0, by simp⟩
  have key : (2 * Bf τ c t v w) • y₁ ∈ Λ := by
    rw [← psi_anti hc hβ v w y₁]
    exact hsm ε _ (hadd _ _ (hv _ (hw _ h1)) (hw _ (hv _ h1)))
  obtain ⟨p, q, e⟩ := (h _).1 key
  have e' : (2 * Bf τ c t v w) • y₁ + (0 : K) • y₂ = algebraMap O K p • y₁ + algebraMap O K q • y₂ := by
    rw [zero_smul, add_zero]
    exact e
  obtain ⟨e1, -⟩ := coord_uniq hg e'
  refine ⟨((L2.unit⁻¹ : Oˣ) : O) * p, ?_⟩
  have h2 : algebraMap O K ((L2.unit⁻¹ : Oˣ) : O) * 2 = 1 := by
    rw [← map_ofNat (algebraMap O K) 2, ← map_mul, IsUnit.val_inv_mul, map_one]
  rw [map_mul, ← e1, ← mul_assoc, h2, one_mul]

theorem isUnimodular_cliffordLatticeStabilizer (L : IsLoc O Δ) (hD : τ ^ 2 - 4 ≠ 0) (hs : s ≠ 0) (hu : IsUnit β) (hc : c = (τ ^ 2 - 4) * algebraMap O K ε * s ^ 2)
    (hβ : QuadraticAlgebra.norm β * algebraMap O K ε * s ^ 2 = 2 * t) {Λ : Set (Etau K τ)} (hΛ : IsLat O τ Λ) : Uni O c t (S0 s β Λ) := by
  obtain ⟨y₁, y₂, hg, hΛ'⟩ := lat_basis L hD hΛ
  have h2K : (2 : K) ≠ 0 := by
    have := (L.two.map (algebraMap O K)).ne_zero
    rwa [map_ofNat] at this
  have hεK : algebraMap O K ε ≠ 0 := ((ε.isUnit).map (algebraMap O K)).ne_zero
  obtain ⟨e, f, k, he1, he2, hf1, hf2, hk1, hk2⟩ := exists_efh hD h2K hs hu hg
  have ev1 : ∀ a b d : K, psi s β (a • e + b • f + d • k) y₁ = (-d) • y₁ + b • y₂ := by
    intro a b d
    simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, he1, hf1, hk1]
    module
  have ev2 : ∀ a b d : K, psi s β (a • e + b • f + d • k) y₂ = a • y₁ + d • y₂ := by
    intro a b d
    simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, he2, hf2, hk2]
    module
  have dec : ∀ v : K × Etau K τ, ∃ a b d : K, v = a • e + b • f + d • k := by
    intro v
    obtain ⟨α, b, h1⟩ : ∃ α b : K, psi s β v y₁ = α • y₁ + b • y₂ := ⟨_, _, coord hg _⟩
    obtain ⟨a, δ, h2⟩ : ∃ a δ : K, psi s β v y₂ = a • y₁ + δ • y₂ := ⟨_, _, coord hg _⟩
    have A1 := psi_anti hc hβ v k y₁
    have A2 := psi_anti hc hβ v k y₂
    simp only [hk1, hk2, map_neg, h1, h2, map_add (f := _), map_smul] at A1 A2
    have E1 : (algebraMap O K ε * (-2 * α)) • y₁ + (0 : K) • y₂ = (2 * Bf τ c t v k) • y₁ + (0 : K) • y₂ := by
      rw [← A1]
      module
    have E2 : (0 : K) • y₁ + (algebraMap O K ε * (2 * δ)) • y₂ = (0 : K) • y₁ + (2 * Bf τ c t v k) • y₂ := by
      rw [← A2]
      module
    obtain ⟨r1, -⟩ := coord_uniq hg E1
    obtain ⟨-, r2⟩ := coord_uniq hg E2
    have hδ : δ = -α := by
      have := mul_left_cancel₀ hεK (r2.trans r1.symm)
      exact mul_left_cancel₀ h2K (by linear_combination this)
    refine ⟨a, b, -α, ?_⟩
    rw [← sub_eq_zero]
    refine psi_inj hD hs hu (fun y => ?_)
    rw [coord hg y]
    simp only [map_sub, LinearMap.sub_apply, map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      h1, h2, he1, he2, hf1, hf2, hk1, hk2, hδ]
    module
  have pair : ∀ x z : K, (∃ p q : O, x • y₁ + z • y₂ = algebraMap O K p • y₁ + algebraMap O K q • y₂) ↔
      x ∈ (algebraMap O K).range ∧ z ∈ (algebraMap O K).range := by
    intro x z
    constructor
    · rintro ⟨p, q, hpq⟩
      obtain ⟨r1, r2⟩ := coord_uniq hg hpq
      exact ⟨RingHom.mem_range.mpr ⟨p, r1.symm⟩, RingHom.mem_range.mpr ⟨q, r2.symm⟩⟩
    · rintro ⟨hx, hz⟩
      obtain ⟨p, rfl⟩ := RingHom.mem_range.mp hx
      obtain ⟨q, rfl⟩ := RingHom.mem_range.mp hz
      exact ⟨p, q, rfl⟩
  have memc : ∀ a b d : K, a • e + b • f + d • k ∈ S0 s β Λ ↔
      a ∈ (algebraMap O K).range ∧ b ∈ (algebraMap O K).range ∧ d ∈ (algebraMap O K).range := by
    intro a b d
    rw [mem_S0_of_sum_eq hΛ', ev1, ev2, hΛ', hΛ', pair, pair, neg_mem_iff]
    tauto
  have ind : ∀ a b d a' b' d' : K, a • e + b • f + d • k = a' • e + b' • f + d' • k → a = a' ∧ b = b' ∧ d = d' := by
    intro a b d a' b' d' hv
    have q1 := congrArg (fun v => psi s β v y₁) hv
    have q2 := congrArg (fun v => psi s β v y₂) hv
    simp only [ev1, ev2] at q1 q2
    obtain ⟨u1, u2⟩ := coord_uniq hg q1
    obtain ⟨u3, -⟩ := coord_uniq hg q2
    exact ⟨u3, u2, neg_inj.mp u1⟩
  have gram : ∀ a b d : K, 2 * Bf τ c t e (a • e + b • f + d • k) = algebraMap O K ε * b ∧
      2 * Bf τ c t f (a • e + b • f + d • k) = algebraMap O K ε * a ∧
      Bf τ c t k (a • e + b • f + d • k) = algebraMap O K ε * d := by
    intro a b d
    have Ae := psi_anti hc hβ e (a • e + b • f + d • k) y₂
    have Af := psi_anti hc hβ f (a • e + b • f + d • k) y₁
    have Ak := psi_anti hc hβ k (a • e + b • f + d • k) y₁
    rw [ev2, he2, ev1, map_add (f := _), map_smul, map_smul, he1, he2] at Ae
    rw [ev1, hf1, ev2, map_add (f := _), map_smul, map_smul, hf1, hf2] at Af
    rw [ev1, hk1, map_neg, ev1, map_add (f := _), map_smul, map_smul, hk1, hk2] at Ak
    have Ee : (0 : K) • y₁ + (algebraMap O K ε * b) • y₂ = (0 : K) • y₁ + (2 * Bf τ c t e (a • e + b • f + d • k)) • y₂ := by
      rw [← Ae]
      module
    have Ef : (algebraMap O K ε * a) • y₁ + (0 : K) • y₂ = (2 * Bf τ c t f (a • e + b • f + d • k)) • y₁ + (0 : K) • y₂ := by
      rw [← Af]
      module
    have Ek : (2 * (algebraMap O K ε * d)) • y₁ + (0 : K) • y₂ = (2 * Bf τ c t k (a • e + b • f + d • k)) • y₁ + (0 : K) • y₂ := by
      rw [← Ak]
      module
    exact ⟨(coord_uniq hg Ee).2.symm, (coord_uniq hg Ef).1.symm, (mul_left_cancel₀ h2K (coord_uniq hg Ek).1).symm⟩
  refine ⟨?_, ?_⟩
  · classical
    refine ⟨{e, f, k}, ?_⟩
    ext v
    obtain ⟨a, b, d, rfl⟩ := dec v
    rw [memc]
    simp only [Finset.coe_insert, Finset.coe_singleton, SetLike.mem_coe, Submodule.mem_span_insert,
      Submodule.mem_span_singleton]
    constructor
    · rintro ⟨hp, hq, hr⟩
      obtain ⟨p, rfl⟩ := RingHom.mem_range.mp hp
      obtain ⟨q, rfl⟩ := RingHom.mem_range.mp hq
      obtain ⟨r, rfl⟩ := RingHom.mem_range.mp hr
      refine ⟨p, q • f + r • k, ⟨q, r • k, ⟨r, rfl⟩, rfl⟩, ?_⟩
      all_goals rw [algebraMap_smul, algebraMap_smul, algebraMap_smul, add_assoc]
    · rintro ⟨p, _, ⟨q, _, ⟨r, rfl⟩, rfl⟩, hv⟩
      rw [← algebraMap_smul K p e, ← algebraMap_smul K q f, ← algebraMap_smul K r k, ← add_assoc] at hv
      obtain ⟨u1, u2, u3⟩ := ind _ _ _ _ _ _ hv
      exact ⟨RingHom.mem_range.mpr ⟨p, u1.symm⟩, RingHom.mem_range.mpr ⟨q, u2.symm⟩, RingHom.mem_range.mpr ⟨r, u3.symm⟩⟩
  · intro y
    constructor
    · intro hy x hx
      exact Bf_int L.two hc hβ hg hΛ' hx hy
    · intro H
      obtain ⟨a, b, d, rfl⟩ := dec y
      have meme : e ∈ S0 s β Λ := by
        have := (memc 1 0 0).2 ⟨one_mem _, zero_mem _, zero_mem _⟩
        simpa using this
      have memf : f ∈ S0 s β Λ := by
        have := (memc 0 1 0).2 ⟨zero_mem _, one_mem _, zero_mem _⟩
        simpa using this
      have memk : k ∈ S0 s β Λ := by
        have := (memc 0 0 1).2 ⟨zero_mem _, zero_mem _, one_mem _⟩
        simpa using this
      obtain ⟨g1, g2, g3⟩ := gram a b d
      have hinv : algebraMap O K ↑ε⁻¹ * algebraMap O K ↑ε = 1 := by
        rw [← map_mul, Units.inv_mul, map_one]
      rw [memc]
      refine ⟨?_, ?_, ?_⟩
      · have ha : a = algebraMap O K (↑ε⁻¹ * 2) * Bf τ c t f (a • e + b • f + d • k) := by
          rw [map_mul, map_ofNat]
          linear_combination (-(algebraMap O K ↑ε⁻¹)) * g2 - a * hinv
        rw [ha]
        exact mul_mem (RingHom.mem_range_self _ _) (H f memf)
      · have hb : b = algebraMap O K (↑ε⁻¹ * 2) * Bf τ c t e (a • e + b • f + d • k) := by
          rw [map_mul, map_ofNat]
          linear_combination (-(algebraMap O K ↑ε⁻¹)) * g1 - b * hinv
        rw [hb]
        exact mul_mem (RingHom.mem_range_self _ _) (H e meme)
      · have hd : d = algebraMap O K ↑ε⁻¹ * Bf τ c t k (a • e + b • f + d • k) := by
          linear_combination (-(algebraMap O K ↑ε⁻¹)) * g3 - d * hinv
        rw [hd]
        exact mul_mem (RingHom.mem_range_self _ _) (H k memk)

end UpperTheory.V.Z.Sym.Loc.CP
