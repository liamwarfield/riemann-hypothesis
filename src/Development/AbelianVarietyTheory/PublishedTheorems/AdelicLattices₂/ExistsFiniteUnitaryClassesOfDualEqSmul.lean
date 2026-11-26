module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.ExistsIntMulIsIntegralOfTrace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.ExistsFiniteRepresentatives
section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.ExistsFiniteOrthogonalLengths
namespace GlobalTheory.HermClass

open Module Submodule NumberField

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_finite_lengths (n : ℕ) (hn : n ≠ 0) {N : ℤ} (hN : N ≠ 0) :
    ∃ S : Set E, S.Finite ∧ (0 : E) ∉ S ∧
      ∀ (V : Type) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
      (h : V →ₗ[E] V →ₗ⋆[E] E) (Λ : Submodule ℤ V), finrank E V = n →
      (∀ x y, h y x = star (h x y)) → (∀ y, (∀ x, h y x = 0) → y = 0) →
      Λ.FG → span E (Λ : Set V) = ⊤ →
      (∀ a : E, IsIntegral ℤ a → ∀ x ∈ Λ, a • x ∈ Λ) →
      (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (h x y)) →
      (∀ y, (∀ x ∈ Λ, IsIntegral ℤ (h y x)) → (N : E) • y ∈ Λ) →
      ∃ v ∈ Λ, h v v ∈ S := by
  classical
  obtain ⟨C, hC⟩ := exists_bound_short (E := E) n hn hN
  obtain ⟨M, hM, hMJ⟩ := exists_int_mul_mem_span E
  let L : Submodule ℤ E := Subalgebra.toSubmodule (integralClosure ℤ E) ⊓
    LinearMap.ker ((starRingEnd E).toIntAlgHom.toLinearMap - LinearMap.id)
  have hL : ∀ x, x ∈ L ↔ IsIntegral ℤ x ∧ star x = x := fun x => by
    simp [L, sub_eq_zero, mem_integralClosure_iff, starRingEnd_apply]
  have hLfg : L.FG := (fg_integers E).of_le inf_le_left
  have hK : 2 * (N * M) ≠ 0 := by positivity
  obtain ⟨R, hR, -, hRL⟩ := exists_finite_residues L hLfg hK
  refine ⟨({x : E | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ C} ∪ R ∪
    {((2 * (N * M) : ℤ) : E)}) \ {0},
    (((Embeddings.finite_of_norm_le E ℂ C).union hR).union (Set.finite_singleton _)).subset
      Set.diff_subset, by simp, ?_⟩
  intro V _ _ _ h Λ hV hs hnd hfg hsp hO hint hdual
  obtain ⟨v, hv, hv0, hvC⟩ := hC V h Λ hV hs hfg hsp hO hdual
  by_cases hvv : h v v = 0
  swap
  · exact ⟨v, hv, Or.inl (Or.inl ⟨hint v hv v hv, hvC⟩), hvv⟩
  let J : Ideal (𝓞 E) :=
    { carrier := {a | ∃ x ∈ Λ, h x v = algebraMap (𝓞 E) E a}
      add_mem' := by
        rintro a b ⟨x, hx, ha⟩ ⟨y, hy, hb⟩
        exact ⟨x + y, add_mem hx hy, by simp [ha, hb]⟩
      zero_mem' := ⟨0, zero_mem _, by simp⟩
      smul_mem' := by
        rintro c a ⟨x, hx, ha⟩
        exact ⟨algebraMap (𝓞 E) E c • x, hO _ c.isIntegral_coe x hx, by
          rw [map_smul, LinearMap.smul_apply, ha, smul_eq_mul, smul_eq_mul, map_mul]⟩ }
  have hJ : ∀ x ∈ Λ, ∃ a ∈ J, algebraMap (𝓞 E) E a = h x v := fun x hx =>
    ⟨⟨h x v, hint x hx v hv⟩, ⟨x, hx, rfl⟩, rfl⟩
  have hJ0 : J ≠ ⊥ := by
    intro h0
    refine hv0 (hnd v fun x => ?_)
    have h1 : span E (Λ : Set V) ≤ LinearMap.ker (h.flip v) := span_le.2 fun y hy => by
      obtain ⟨a, ha, hay⟩ := hJ y hy
      rw [h0, Ideal.mem_bot] at ha
      rw [ha, map_zero] at hay
      exact hay.symm
    have h2 : h x v = 0 := h1 (hsp ▸ mem_top)
    rw [hs, h2, star_zero]
  obtain ⟨j, ⟨w, hw, hwj⟩, hj0, hj⟩ := hMJ J hJ0
  have hj0' : algebraMap (𝓞 E) E j ≠ 0 := fun h0 => hj0 (RingOfIntegers.ext h0)
  set v' : V := (N : E) • star ((M : E) / algebraMap (𝓞 E) E j) • v with hv'
  have hv'Λ : v' ∈ Λ := hdual _ fun x hx => by
    obtain ⟨a, ha, hax⟩ := hJ x hx
    obtain ⟨c, hc⟩ := hj _ ha
    have hc' := congrArg (algebraMap (𝓞 E) E) hc
    rw [map_mul, map_mul, map_intCast, hax] at hc'
    have : (M : E) / algebraMap (𝓞 E) E j * h x v = algebraMap (𝓞 E) E c := by
      field_simp; exact hc'
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, hs x v, ← star_mul', this]
    exact isIntegral_star c.isIntegral_coe
  have h1 : h w v' = N * M := by
    simp only [hv', map_smulₛₗ, starRingEnd_apply, star_star, smul_eq_mul, hwj, star_intCast]
    field_simp
  have h2 : h v' w = N * M := by rw [hs, h1]; simp
  have h3 : h v' v' = 0 := by simp [hv', hvv]
  have h4 : ∀ s : E, star s = s → h (w - s • v') (w - s • v') = h w w - 2 * (N * M) * s := by
    intro s hs'
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, map_smulₛₗ,
      starRingEnd_apply, hs', smul_eq_mul, h1, h2, h3, RingHom.id_apply]
    ring
  obtain ⟨ρ, hρ, y, hy, hwρ⟩ := hRL (h w w) ((hL _).2 ⟨hint w hw w hw, (hs w w).symm⟩)
  obtain ⟨hyi, hys⟩ := (hL y).1 hy
  by_cases hρ0 : ρ = 0
  · refine ⟨w - (y - 1) • v', sub_mem hw (hO _ (hyi.sub isIntegral_one) _ hv'Λ), ?_⟩
    have : h (w - (y - 1) • v') (w - (y - 1) • v') = ((2 * (N * M) : ℤ) : E) := by
      rw [h4 _ (by rw [star_sub, hys, star_one]), hwρ, hρ0, zsmul_eq_mul]; push_cast; ring
    rw [this]
    exact ⟨Or.inr rfl, by simpa using hK⟩
  · refine ⟨w - y • v', sub_mem hw (hO _ hyi _ hv'Λ), ?_⟩
    have : h (w - y • v') (w - y • v') = ρ := by
      rw [h4 _ hys, hwρ, zsmul_eq_mul]; push_cast; ring
    rw [this]
    exact ⟨Or.inl (Or.inr hρ), hρ0⟩

theorem exists_finite_orthogonal_lengths (n : ℕ) : ∀ {N : ℤ}, N ≠ 0 →
    ∃ S : Set E, S.Finite ∧ (0 : E) ∉ S ∧
      ∀ (V : Type) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
      (h : V →ₗ[E] V →ₗ⋆[E] E) (Λ : Submodule ℤ V), finrank E V = n →
      (∀ x y, h y x = star (h x y)) → (∀ y, (∀ x, h y x = 0) → y = 0) →
      Λ.FG → span E (Λ : Set V) = ⊤ →
      (∀ a : E, IsIntegral ℤ a → ∀ x ∈ Λ, a • x ∈ Λ) →
      (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (h x y)) →
      (∀ y, (∀ x ∈ Λ, IsIntegral ℤ (h y x)) → (N : E) • y ∈ Λ) →
      ∃ v : Fin n → V, (∀ i, v i ∈ Λ) ∧ (∀ i j, i ≠ j → h (v i) (v j) = 0) ∧
        ∀ i, h (v i) (v i) ∈ S := by
  induction n with
  | zero =>
    intro N _
    exact ⟨∅, Set.finite_empty, by simp, fun V _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩⟩
  | succ n ih =>
    intro N hN
    obtain ⟨S₁, hS₁, h0₁, H₁⟩ := exists_finite_lengths (E := E) (n + 1) n.succ_ne_zero hN
    obtain ⟨M, hM, hMS⟩ := exists_int_mul_isIntegral E (hS₁.image fun a => a⁻¹)
    obtain ⟨S₂, hS₂, h0₂, H₂⟩ := ih (mul_ne_zero hM hN)
    refine ⟨S₁ ∪ S₂, hS₁.union hS₂, by simp [h0₁, h0₂], ?_⟩
    intro V _ _ _ h Λ hV hs hnd hfg hsp hO hint hdual
    obtain ⟨v, hv, hvS⟩ := H₁ V h Λ hV hs hnd hfg hsp hO hint hdual
    set a := h v v with ha
    have ha0 : a ≠ 0 := fun h0 => h0₁ (h0 ▸ hvS)
    have hai : IsIntegral ℤ a := hint v hv v hv
    have has : star a = a := (hs v v).symm
    let W : Submodule E V := LinearMap.ker (h.flip v)
    have hW : ∀ x, x ∈ W ↔ h x v = 0 := fun x => Iff.rfl
    have hWr : finrank E W = n := by
      have h1 := LinearMap.finrank_range_add_finrank_ker (h.flip v)
      have h2 : LinearMap.range (h.flip v) = ⊤ := by
        rw [eq_top_iff]
        intro c _
        exact ⟨(c / a) • v, by simp [← ha, ha0]⟩
      rw [h2, finrank_top, finrank_self, hV] at h1
      change 1 + finrank E W = _ at h1
      omega
    let p : V →ₗ[E] W := LinearMap.codRestrict W
      (a • LinearMap.id - (h.flip v).smulRight v) fun x => by
        rw [hW]; simp [← ha, mul_comm]
    have hp : ∀ x, (p x : V) = a • x - h x v • v := fun x => rfl
    let Λ' : Submodule ℤ W := Λ.comap (W.subtype.restrictScalars ℤ)
    have hΛ' : ∀ x : W, x ∈ Λ' ↔ (x : V) ∈ Λ := fun x => Iff.rfl
    have hpΛ : ∀ x ∈ Λ, p x ∈ Λ' := fun x hx => by
      rw [hΛ', hp]; exact sub_mem (hO _ hai _ hx) (hO _ (hint x hx v hv) _ hv)
    have hyp : ∀ (y : W) (x : V), h y (p x) = a * h y x := fun y x => by
      have : h y v = 0 := y.2
      simp [hp, starRingEnd_apply, has, this]
    obtain ⟨u, huΛ, huo, huS⟩ := H₂ W (h.domRestrict₁₂ W W) Λ' hWr (fun x y => hs x y)
      (fun y hy => Subtype.ext (hnd y fun x => by
        have h1 : h y (p x) = 0 := hy (p x)
        rw [hyp] at h1
        exact (mul_eq_zero.1 h1).resolve_left ha0))
      (by
        apply Submodule.fg_of_fg_map_injective (W.subtype.restrictScalars ℤ) W.subtype_injective
        exact hfg.of_le (map_comap_le _ _))
      (by
        rw [eq_top_iff]
        intro w _
        have h1 : span E (Λ : Set V) ≤ (span E (Λ' : Set W)).comap p :=
          span_le.2 fun x hx => subset_span (hpΛ x hx)
        have h2 : p w ∈ span E (Λ' : Set W) := h1 (hsp ▸ mem_top)
        have h3 : w = a⁻¹ • p w := Subtype.ext (by
          have : h w v = 0 := w.2
          simp [hp, this, ha0])
        rw [h3]; exact smul_mem _ _ h2)
      (fun c hc x hx => hO c hc x hx) (fun x hx y hy => hint x hx y hy)
      (fun y hy => by
        have h1 : (N : E) • a • (y : V) ∈ Λ := hdual _ fun x hx => by
          rw [map_smul, LinearMap.smul_apply, smul_eq_mul, ← hyp]
          exact hy _ (hpΛ x hx)
        have h2 := hO _ (hMS _ ⟨a, hvS, rfl⟩) _ h1
        rw [smul_smul, smul_smul] at h2
        rw [hΛ', Submodule.coe_smul]
        convert h2 using 2
        push_cast; field_simp)
    refine ⟨Fin.cons v fun i => u i, fun i => ?_, fun i j hij => ?_, fun i => ?_⟩
    · cases i using Fin.cases with
      | zero => exact hv
      | succ i => exact huΛ i
    · cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact (hij rfl).elim
        | succ j =>
          have : h (u j) v = 0 := (u j).2
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [hs, this, star_zero]
      | succ i =>
        cases j using Fin.cases with
        | zero => exact (u i).2
        | succ j => exact huo i j fun h0 => hij (congrArg _ h0)
    · cases i using Fin.cases with
      | zero => exact Or.inl hvS
      | succ i => exact Or.inr (huS i)

end GlobalTheory.HermClass
end

namespace GlobalTheory.HermClass

open Module Submodule NumberField

theorem finite_between {E V : Type} [Field E] [CharZero E] [AddCommGroup V] [Module E V]
    (L₀ : Submodule ℤ V) (h₀ : L₀.FG) {M : ℤ} (hM : M ≠ 0) :
    {L : Submodule ℤ V | L₀ ≤ L ∧ ∀ x ∈ L, (M : E) • x ∈ L₀}.Finite := by
  classical
  have hcast : ∀ x : V, (M : E) • x = M • x := fun x => Int.cast_smul_eq_zsmul E M x
  let μ : V →ₗ[ℤ] V := M • LinearMap.id
  have hμ : ∀ x, μ x = M • x := fun x => rfl
  have hinj : Function.Injective μ := by
    intro x y hxy
    rw [hμ, hμ, ← hcast, ← hcast] at hxy
    exact smul_right_injective V (Int.cast_ne_zero.mpr hM) hxy
  let L' := L₀.comap μ
  have hL'fg : L'.FG :=
    Submodule.fg_of_fg_map_injective μ hinj (h₀.of_le (Submodule.map_comap_le μ L₀))
  let K : Submodule ℤ L' := L₀.comap L'.subtype
  have : Module.Finite ℤ L' := Module.Finite.iff_fg.mpr hL'fg
  have : Finite (L' ⧸ K) := by
    apply Module.finite_of_fg_torsion
    intro q
    obtain ⟨x, rfl⟩ := K.mkQ_surjective q
    refine ⟨⟨M, mem_nonZeroDivisors_of_ne_zero hM⟩, ?_⟩
    rw [Submonoid.smul_def, ← LinearMap.map_smul, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact x.2
  have : Finite (Submodule ℤ (L' ⧸ K)) :=
    Finite.of_injective (fun P : Submodule ℤ (L' ⧸ K) => (P : Set (L' ⧸ K))) SetLike.coe_injective
  let g : Submodule ℤ V → Submodule ℤ (L' ⧸ K) := fun L => (L.comap L'.subtype).map K.mkQ
  have key : ∀ L : Submodule ℤ V, L ∈ {L : Submodule ℤ V | L₀ ≤ L ∧ ∀ x ∈ L, (M : E) • x ∈ L₀} →
      ((g L).comap K.mkQ).map L'.subtype = L := by
    rintro L ⟨hle, hM'⟩
    have hK : K ≤ L.comap L'.subtype := fun x hx => hle hx
    have hL' : L ≤ L' := fun x hx => show μ x ∈ L₀ by rw [hμ, ← hcast]; exact hM' x hx
    simp only [g, Submodule.comap_map_mkQ, sup_eq_right.mpr hK, Submodule.map_comap_subtype,
      inf_eq_right.mpr hL']
  refine Set.Finite.of_finite_image (Set.toFinite _) (f := g) ?_
  intro L₁ h₁ L₂ h₂ h12
  exact (key L₁ h₁).symm.trans
    ((congrArg (fun P => (P.comap K.mkQ).map L'.subtype) h12).trans (key L₂ h₂))

theorem exists_finite_representatives {α : Type*} {β : Type*} (f : α → β)
    (hf : (Set.range f).Finite) : ∃ S : Set α, S.Finite ∧ ∀ a, ∃ s ∈ S, f s = f a := by
  classical
  have : Finite (Set.range f) := hf.to_subtype
  refine ⟨Set.range (fun b : Set.range f => b.2.choose), Set.finite_range _, fun a => ?_⟩
  exact ⟨(⟨f a, a, rfl⟩ : Set.range f).2.choose, ⟨⟨f a, a, rfl⟩, rfl⟩,
    (⟨f a, a, rfl⟩ : Set.range f).2.choose_spec⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_finite_classes {V : Type} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (hs : ∀ x y, h y x = star (h x y))
    (hnd : ∀ y, (∀ x, h y x = 0) → y = 0) {N m : ℤ} (hN : N ≠ 0) (hm : m ≠ 0)
    {α : Type*} {ι : Type*} [Finite ι] (Λ : α → Submodule ℤ V) (t : α → ι → V)
    (hfg : ∀ a, (Λ a).FG) (hsp : ∀ a, span E (Λ a : Set V) = ⊤)
    (hO : ∀ a, ∀ c : E, IsIntegral ℤ c → ∀ x ∈ Λ a, c • x ∈ Λ a)
    (hint : ∀ a, ∀ x ∈ Λ a, ∀ y ∈ Λ a, IsIntegral ℤ (h x y))
    (hdual : ∀ a y, (∀ x ∈ Λ a, IsIntegral ℤ (h y x)) → (N : E) • y ∈ Λ a)
    (ht : ∀ a i, t a i ∈ Λ a) :
    ∃ S : Set α, S.Finite ∧ ∀ a, ∃ s ∈ S, ∃ γ : V ≃ₗ[E] V, (∀ x y, h (γ x) (γ y) = h x y) ∧
      (∀ x, x ∈ Λ a ↔ γ x ∈ Λ s) ∧ ∀ i, ∃ y ∈ Λ s, γ (t a i) - t s i = m • y := by
  classical
  set n := finrank E V with hn
  obtain ⟨S₀, hS₀f, hS₀0, hS₀⟩ := exists_finite_orthogonal_lengths (E := E) n hN
  have hv : ∀ a, ∃ v : Fin n → V, (∀ i, v i ∈ Λ a) ∧
      (∀ i j, i ≠ j → h (v i) (v j) = 0) ∧ ∀ i, h (v i) (v i) ∈ S₀ := fun a =>
    hS₀ V h (Λ a) hn.symm hs hnd (hfg a) (hsp a) (hO a) (hint a) (hdual a)
  choose v hvΛ hvo hvS using hv
  have hexp : ∀ a (c : Fin n → E) (y : V), h (∑ i, c i • v a i) y = ∑ i, c i * h (v a i) y := by
    intro a c y
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, LinearMap.sum_apply, smul_eq_mul]
  have hexp2 : ∀ a (x : V) (c : Fin n → E),
      h x (∑ j, c j • v a j) = ∑ j, star (c j) * h x (v a j) := by
    intro a x c
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, smul_eq_mul, starRingEnd_apply]
  have hcoef : ∀ a (c : Fin n → E) j, h (∑ i, c i • v a i) (v a j) = c j * h (v a j) (v a j) := by
    intro a c j
    rw [hexp, Finset.sum_eq_single j]
    · intro i _ hij
      rw [hvo a i j hij, mul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hd0 : ∀ a j, h (v a j) (v a j) ≠ 0 := fun a j h0 => hS₀0 (h0 ▸ hvS a j)
  have hli : ∀ a, LinearIndependent E (v a) := by
    intro a
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have h1 := hcoef a c j
    rw [hc, map_zero, LinearMap.zero_apply] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_right (hd0 a j)
  let b : α → Basis (Fin n) E V := fun a =>
    basisOfLinearIndependentOfCardEqFinrank' (v a) (hli a) ((Fintype.card_fin n).trans hn)
  let Φ : α → V ≃ₗ[E] (Fin n → E) := fun a => (b a).equivFun
  have hΦsymm : ∀ a c, (Φ a).symm c = ∑ i, c i • v a i := by
    intro a c
    simp [Φ, b, Basis.equivFun_symm_apply]
  have hgram : ∀ a (c c' : Fin n → E), h (∑ i, c i • v a i) (∑ j, c' j • v a j) =
      ∑ i, c i * (star (c' i) * h (v a i) (v a i)) := by
    intro a c c'
    rw [hexp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hexp2, Finset.sum_eq_single i]
    · intro j _ hji
      rw [hvo a i j (Ne.symm hji), mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  obtain ⟨M, hM0, hMT⟩ := exists_int_mul_isIntegral E (hS₀f.image fun d => d⁻¹)
  let L₀ : Submodule ℤ (Fin n → E) :=
    Submodule.pi Set.univ fun _ => Subalgebra.toSubmodule (integralClosure ℤ E)
  have hL₀ : ∀ c, c ∈ L₀ ↔ ∀ i, IsIntegral ℤ (c i) := by
    intro c
    simp [L₀, Submodule.mem_pi, mem_integralClosure_iff]
  have hL₀fg : L₀.FG := Submodule.fg_pi fun _ => fg_integers E
  let P : α → Submodule ℤ (Fin n → E) := fun a => (Λ a).map ((Φ a : V →ₗ[E] (Fin n → E)).restrictScalars ℤ)
  have hmemP : ∀ a c, c ∈ P a ↔ (Φ a).symm c ∈ Λ a := by
    intro a c
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hc
      exact ⟨_, hc, by simp⟩
  have hPfg : ∀ a, (P a).FG := fun a => (hfg a).map _
  have hPB : ∀ a, P a ∈ {L : Submodule ℤ (Fin n → E) | L₀ ≤ L ∧ ∀ x ∈ L, (M : E) • x ∈ L₀} := by
    intro a
    refine ⟨fun c hc => ?_, fun c hc => ?_⟩
    · rw [hmemP, hΦsymm]
      exact Submodule.sum_mem _ fun i _ => hO a (c i) ((hL₀ c).1 hc i) _ (hvΛ a i)
    · rw [hL₀]
      intro i
      have hx := (hmemP a c).1 hc
      have hci := hcoef a c i
      rw [← hΦsymm] at hci
      have : (M : E) * c i = ((M : E) * (h (v a i) (v a i))⁻¹) * h ((Φ a).symm c) (v a i) := by
        rw [hci]
        field_simp [hd0 a i]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [this]
      exact (hMT _ ⟨_, hvS a i, rfl⟩).mul (hint a _ hx _ (hvΛ a i))
  have hB := finite_between (E := E) L₀ hL₀fg hM0
  have hres : ∀ Q : Submodule ℤ (Fin n → E), ∃ R : Set (Fin n → E), R.Finite ∧
      (Q.FG → ∀ x ∈ Q, ∃ ρ ∈ R, ∃ y ∈ Q, x = ρ + m • y) := by
    intro Q
    by_cases hQ : Q.FG
    · obtain ⟨R, hRf, -, hR⟩ := exists_finite_residues Q hQ hm
      exact ⟨R, hRf, fun _ => hR⟩
    · exact ⟨∅, Set.finite_empty, fun h' => absurd h' hQ⟩
  choose R hRf hR using hres
  have hρ : ∀ a i, ∃ ρ ∈ R (P a), ∃ y ∈ P a, Φ a (t a i) = ρ + m • y := fun a i =>
    hR (P a) (hPfg a) _ ((hmemP a _).2 (by simpa using ht a i))
  choose ρ hρR y hyP hρeq using hρ
  let f : α → (Fin n → E) × Submodule ℤ (Fin n → E) × (ι → Fin n → E) := fun a =>
    (fun i => h (v a i) (v a i), P a, ρ a)
  have hfin : (Set.range f).Finite := by
    refine ((Set.Finite.pi fun _ => hS₀f).prod (hB.prod
      (Set.Finite.pi fun _ => hB.biUnion fun Q _ => hRf Q))).subset ?_
    rintro _ ⟨a, rfl⟩
    exact ⟨fun i _ => hvS a i, hPB a, fun i _ => Set.mem_biUnion (hPB a) (hρR a i)⟩
  obtain ⟨S, hSf, hS⟩ := exists_finite_representatives f hfin
  refine ⟨S, hSf, fun a => ?_⟩
  obtain ⟨s, hsS, hfs⟩ := hS a
  simp only [f, Prod.mk.injEq] at hfs
  obtain ⟨hd, hP, hρ'⟩ := hfs
  refine ⟨s, hsS, (Φ a).trans (Φ s).symm, ?_, ?_, ?_⟩
  · intro x z
    obtain ⟨cx, rfl⟩ := (Φ a).symm.surjective x
    obtain ⟨cz, rfl⟩ := (Φ a).symm.surjective z
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    simp only [hΦsymm, hgram]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [congrFun hd i]
  · intro x
    have e1 := hmemP a (Φ a x)
    have e2 := hmemP s (Φ a x)
    rw [LinearEquiv.symm_apply_apply] at e1
    rw [hP] at e2
    simp only [LinearEquiv.trans_apply]
    exact e1.symm.trans e2
  · intro i
    refine ⟨(Φ s).symm (y a i - y s i), (hmemP s _).1 (sub_mem (by rw [hP]; exact hyP a i) (hyP s i)), ?_⟩
    apply (Φ s).injective
    simp only [LinearEquiv.trans_apply, map_sub, map_zsmul, LinearEquiv.apply_symm_apply]
    rw [hρeq a i, hρeq s i, congrFun hρ' i, smul_sub]
    abel

end GlobalTheory.HermClass
end

namespace GlobalTheory

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.MultiplicativeHeights
open scoped nonZeroDivisors

namespace Published

def FinitenessOfHermitianClasses : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E),
    (∀ a b, cc (G a b) = G b a) → G.det ≠ 0 →
    ∀ (c : FractionalIdeal (𝓞 E)⁰ E), c ≠ 0 → ∀ (𝔪 : Ideal (𝓞 E)), 𝔪 ≠ ⊥ →
    ∀ (ι : Type) [Finite ι] (𝓛 : Set (Submodule (𝓞 E) (Fin r → E) × (ι → Fin r → E))),
    (∀ p ∈ 𝓛, IsLattice p.1 ∧
      (∀ x, (∀ y ∈ p.1, IsIntegral ℤ (herm G x y)) ↔ x ∈ (c : Submodule (𝓞 E) E) • p.1) ∧
      ∀ i, p.2 i ∈ p.1) →
    ∃ S ⊆ 𝓛, S.Finite ∧ ∀ p ∈ 𝓛, ∃ q ∈ S, ∃ γ : GL (Fin r) E,
      (∀ x y, herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) =
        herm G x y) ∧
      (∀ x, x ∈ p.1 ↔ (γ : Matrix (Fin r) (Fin r) E) *ᵥ x ∈ q.1) ∧
      ∀ i, (γ : Matrix (Fin r) (Fin r) E) *ᵥ p.2 i - q.2 i ∈ 𝔪 • q.1

end Published

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem exists_sesquilinear_eq_herm (G : Matrix (Fin r) (Fin r) E) :
    ∃ h : (Fin r → E) →ₗ[E] (Fin r → E) →ₗ⋆[E] E, ∀ x y, h x y = herm G x y := by
  have hc : ∀ x : E, cc x = star x := fun _ => rfl
  refine ⟨LinearMap.mk₂'ₛₗ _ _ (herm G) ?_ ?_ ?_ ?_, fun _ _ => rfl⟩
  · intro x x' y; simp [herm, add_mul, Finset.sum_add_distrib]
  · intro c x y; simp [herm, Finset.mul_sum, mul_assoc]
  · intro x y y'; simp [herm, hc, mul_add, Finset.sum_add_distrib]
  · intro c x y
    simp only [herm, hc, Pi.smul_apply, smul_eq_mul, star_mul', starRingEnd_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem exists_finite_unitary_classes (G : Matrix (Fin r) (Fin r) E)
    (hG : ∀ a b, cc (G a b) = G b a) (hdet : G.det ≠ 0) {N : ℤ} (hN : N ≠ 0)
    {𝔪 : Ideal (𝓞 E)} (h𝔪 : 𝔪 ≠ ⊥) {α : Type*} {ι : Type*} [Finite ι]
    (Λ : α → Submodule (𝓞 E) (Fin r → E)) (t : α → ι → Fin r → E)
    (hΛ : ∀ a, IsLattice (Λ a))
    (hint : ∀ a, ∀ x ∈ Λ a, ∀ y ∈ Λ a, IsIntegral ℤ ((N : E) * herm G x y))
    (hdual : ∀ a x, (∀ y ∈ Λ a, IsIntegral ℤ (herm G x y)) → (N : E) • x ∈ Λ a)
    (ht : ∀ a i, t a i ∈ Λ a) :
    ∃ S : Set α, S.Finite ∧ ∀ a, ∃ s ∈ S, ∃ γ : GL (Fin r) E,
      (∀ x y, herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) =
        herm G x y) ∧
      (∀ x, x ∈ Λ a ↔ (γ : Matrix (Fin r) (Fin r) E) *ᵥ x ∈ Λ s) ∧
      ∀ i, (γ : Matrix (Fin r) (Fin r) E) *ᵥ t a i - t s i ∈ 𝔪 • Λ s := by
  classical
  have hc : ∀ x : E, cc x = star x := fun _ => rfl
  have hN' : (N : E) ≠ 0 := by exact_mod_cast hN
  obtain ⟨h, hh⟩ := exists_sesquilinear_eq_herm G
  have hs : ∀ x y, h y x = star (h x y) := fun x y => by
    simp only [hh, herm, star_sum, star_mul', ← hc (G _ _), hG, hc, star_star]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hnd : ∀ y, (∀ x, h y x = 0) → y = 0 := fun y hy => by
    refine Matrix.eq_zero_of_vecMul_eq_zero hdet (funext fun b => ?_)
    have := hy (Pi.single b 1)
    rw [hh, herm, Finset.sum_comm, Finset.sum_eq_single b] at this
    · simpa [hc, Matrix.vecMul, dotProduct] using this
    · intro b' _ hb; simp [hc, hb]
    · simp
  have hm : (Ideal.absNorm 𝔪 : ℤ) ≠ 0 := by
    exact_mod_cast fun h0 => h𝔪 (Ideal.absNorm_eq_zero_iff.1 h0)
  obtain ⟨S, hS, H⟩ := HermClass.exists_finite_classes ((N : E) • h)
    (fun x y => by simp [hs x y]) (fun y hy => hnd y fun x => by simpa [hN'] using hy x)
    (mul_ne_zero hN hN) hm (fun a => (Λ a).restrictScalars ℤ) t
    (fun a => by
      have : Module.Finite (𝓞 E) (Λ a) := Module.Finite.iff_fg.2 (hΛ a).1
      exact Module.Finite.iff_fg.1 (Module.Finite.trans (R := ℤ) (𝓞 E) (Λ a)))
    (fun a => (hΛ a).2) (fun a c hc x hx => (Λ a).smul_mem (⟨c, hc⟩ : 𝓞 E) hx)
    (fun a x hx y hy => by simpa [hh] using hint a x hx y hy)
    (fun a x hx => by
      rw [Int.cast_mul, mul_smul]
      exact hdual a _ fun y hy => by simpa [← hh] using hx y hy) ht
  refine ⟨S, hS, fun a => ?_⟩
  obtain ⟨s, hsS, γ, h1, h2, h3⟩ := H a
  let g : GL (Fin r) E := ⟨LinearMap.toMatrix' γ.toLinearMap, LinearMap.toMatrix' γ.symm.toLinearMap,
    by rw [← LinearMap.toMatrix'_comp]; simp, by rw [← LinearMap.toMatrix'_comp]; simp⟩
  have hg : ∀ x, (g : Matrix (Fin r) (Fin r) E) *ᵥ x = γ x := fun x =>
    LinearMap.toMatrix'_mulVec γ.toLinearMap x
  refine ⟨s, hsS, g, fun x y => ?_, fun x => ?_, fun i => ?_⟩
  · simpa [hg, hh, hN'] using h1 x y
  · rw [hg]; exact h2 x
  · obtain ⟨y, hy, he⟩ := h3 i
    rw [hg, he, natCast_zsmul, ← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact Submodule.smul_mem_smul (Ideal.absNorm_mem 𝔪) hy

theorem exists_int_bound_of_dual_eq_smul (G : Matrix (Fin r) (Fin r) E)
    {c : FractionalIdeal (𝓞 E)⁰ E} (hc : c ≠ 0) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ Λ : Submodule (𝓞 E) (Fin r → E),
      (∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm G x y)) ↔ x ∈ (c : Submodule (𝓞 E) E) • Λ) →
      (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ ((N : E) * herm G x y)) ∧
      ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm G x y)) → (N : E) • x ∈ Λ := by
  obtain ⟨h, hh⟩ := exists_sesquilinear_eq_herm G
  obtain ⟨e, he0, he⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger hc
  obtain ⟨d, hd0, hd⟩ := c.isFractional
  have he0' : algebraMap (𝓞 E) E e ≠ 0 := fun h0 => he0 (RingOfIntegers.ext h0)
  have hd0' : algebraMap (𝓞 E) E d ≠ 0 := fun h0 =>
    nonZeroDivisors.ne_zero hd0 (RingOfIntegers.ext h0)
  obtain ⟨N, hN, hNi⟩ := HermClass.exists_int_mul_isIntegral E
    (Set.toFinite {(algebraMap (𝓞 E) E e)⁻¹, (algebraMap (𝓞 E) E d)⁻¹})
  refine ⟨N, hN, fun Λ hΛ => ⟨fun x hx y hy => ?_, fun x hx => ?_⟩⟩
  · have h1 := (hNi _ (Or.inl rfl)).mul ((hΛ _).2 (Submodule.smul_mem_smul he hx) y hy)
    rwa [← hh, map_smul, LinearMap.smul_apply, smul_eq_mul, hh, mul_assoc,
      inv_mul_cancel_left₀ he0'] at h1
  · refine Submodule.smul_induction_on (p := fun x => (N : E) • x ∈ Λ) ((hΛ x).1 hx)
      (fun a ha z hz => ?_) (fun x y hx hy => by rw [smul_add]; exact add_mem hx hy)
    obtain ⟨b, hb⟩ := hd a ha
    have h0 : IsIntegral ℤ (algebraMap (𝓞 E) E b) := b.isIntegral_coe
    have h1 := (hNi _ (Or.inr rfl)).mul h0
    rw [hb, Algebra.smul_def, mul_assoc, inv_mul_cancel_left₀ hd0'] at h1
    rw [smul_smul]
    exact Λ.smul_mem (⟨_, h1⟩ : 𝓞 E) hz

theorem Published.finitenessOfHermitianClasses_holds : Published.FinitenessOfHermitianClasses := by
  intro E _ _ _ r G hG hdet c hc 𝔪 h𝔪 ι _ 𝓛 h𝓛
  obtain ⟨N, hN, H⟩ := exists_int_bound_of_dual_eq_smul G hc
  obtain ⟨S, hS, HS⟩ := exists_finite_unitary_classes G hG hdet hN h𝔪 (fun p : 𝓛 => p.1.1)
    (fun p => p.1.2) (fun p => (h𝓛 p p.2).1) (fun p => (H _ (h𝓛 p p.2).2.1).1)
    (fun p => (H _ (h𝓛 p p.2).2.1).2) (fun p => (h𝓛 p p.2).2.2)
  refine ⟨Subtype.val '' S, by rintro _ ⟨p, -, rfl⟩; exact p.2, hS.image _, fun p hp => ?_⟩
  obtain ⟨s, hs, h⟩ := HS ⟨p, hp⟩
  exact ⟨s, ⟨s, hs, rfl⟩, h⟩

end GlobalTheory
